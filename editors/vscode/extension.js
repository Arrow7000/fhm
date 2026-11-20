//@ts-check
"use strict";

const vscode = require("vscode");
const { spawn } = require("child_process");
const fs = require("fs");
const path = require("path");
const {
  normalizePayload,
  resolveHover,
  resolveDefinition,
  hoverMarkdown,
  diagnosticsToMarkers,
  IDENT_RE,
} = require("../shared/fhmEditorCore.cjs");

/** @type {vscode.DiagnosticCollection} */
let diagnostics;
/** @type {Map<string, NodeJS.Timeout>} */
const pending = new Map();
/** @type {Map<string, import("child_process").ChildProcess>} */
const running = new Map();
/** @type {Map<string, number>} */
const requestGeneration = new Map();
let nextRequestGeneration = 0;
/**
 * Cached v3 ranged symbols (def span + lexical scope for use-site) and lexer
 * tokens. `documentVersion` prevents stale ranges from serving hovers during
 * debounce.
 * @type {Map<string, { version: number, documentVersion: number, ranged: any[], tokens: any[], diagnostics: any[] }>}
 */
const symbolCache = new Map();

/**
 * The languages this extension checks, by VS Code language id: each has its
 * own settings section and binary (`lake build fhm` / `lake build epl`), and
 * both binaries print the same `diagnose` JSON. EPL has no hover symbols yet.
 * @type {Record<string, { section: string, bin: string, pathSetting: string }>}
 */
const LANGUAGES = {
  fhm: { section: "fhm", bin: "fhm", pathSetting: "diagnosePath" },
  epl: { section: "epl", bin: "epl", pathSetting: "path" },
};

/**
 * @param {vscode.WorkspaceFolder | undefined} folder
 * @param {string} [languageId]
 * @returns {string | undefined}
 */
function resolveDiagnoseBin(folder, languageId = "fhm") {
  const lang = LANGUAGES[languageId];
  if (!lang) return undefined;
  const configured = vscode.workspace
    .getConfiguration(lang.section)
    .get(lang.pathSetting, "");
  if (configured && typeof configured === "string" && configured.length > 0) {
    return configured;
  }
  if (!folder) return undefined;
  const candidate = path.join(
    folder.uri.fsPath,
    ".lake",
    "build",
    "bin",
    lang.bin
  );
  return fs.existsSync(candidate) ? candidate : undefined;
}

/**
 * @param {vscode.TextDocument} doc
 */
async function refreshDiagnostics(doc) {
  const lang = LANGUAGES[doc.languageId];
  if (!lang || doc.uri.scheme !== "file") return;

  const cfg = vscode.workspace.getConfiguration(lang.section);
  const diagnosticsEnabled = cfg.get("diagnostics.enable", true);
  if (!diagnosticsEnabled) {
    diagnostics.set(doc.uri, []);
  }

  const folder = vscode.workspace.getWorkspaceFolder(doc.uri);
  const bin = resolveDiagnoseBin(folder, doc.languageId);
  if (!bin) {
    // Highlighting still works; diagnostics need `lake build fhm` / `lake build epl`.
    return;
  }

  const key = doc.uri.toString();
  const documentVersion = doc.version;
  const generation = ++nextRequestGeneration;
  requestGeneration.set(key, generation);
  const prev = running.get(key);
  if (prev) {
    prev.kill();
  }

  try {
    const raw = await new Promise((resolve, reject) => {
      const child = spawn(bin, ["diagnose"], {
        stdio: ["pipe", "pipe", "pipe"],
      });
      running.set(key, child);
      let stdout = "";
      let stderr = "";
      child.stdout.on("data", (c) => {
        stdout += c.toString("utf8");
      });
      child.stderr.on("data", (c) => {
        stderr += c.toString("utf8");
      });
      child.on("error", reject);
      child.on("close", (code) => {
        // A killed obsolete child can close after its replacement starts.
        if (running.get(key) === child) running.delete(key);
        try {
          resolve(JSON.parse(stdout.trim() || "[]"));
        } catch (err) {
          reject(
            new Error(
              `${lang.bin} diagnose parse failed (exit ${code}): ${stderr || String(err)}`
            )
          );
        }
      });
      child.stdin.write(doc.getText(), "utf8");
      child.stdin.end();
    });

    // Only the newest request for the unchanged document snapshot may publish.
    if (
      requestGeneration.get(key) !== generation ||
      doc.version !== documentVersion
    ) {
      return;
    }

    const { diagnostics: diagArr, version, ranged, tokens } = normalizePayload(raw);
    symbolCache.set(key, { version, documentVersion, ranged, tokens, diagnostics: diagArr });

    if (!diagnosticsEnabled) return;

    /** @type {vscode.Diagnostic[]} */
    const diags = diagnosticsToMarkers(diagArr).map((m) => {
      const range = new vscode.Range(
        m.line0,
        m.col0,
        m.endLine0,
        m.endCol0
      );
      const severity =
        m.severity === "warning"
          ? vscode.DiagnosticSeverity.Warning
          : vscode.DiagnosticSeverity.Error;
      return new vscode.Diagnostic(range, m.message, severity);
    });
    diagnostics.set(doc.uri, diags);
  } catch (err) {
    // Keep last good diagnostics/symbols; surface once via console for debugging.
    console.error(`[${lang.bin}]`, err);
  }
}

/**
 * @param {vscode.TextDocument} doc
 */
function scheduleRefresh(doc) {
  const lang = LANGUAGES[doc.languageId];
  if (!lang) return;
  const key = doc.uri.toString();
  // A range is tied to a specific buffer snapshot.  Never answer hovers with
  // offsets from the previous snapshot while this edit is debounced.
  symbolCache.delete(key);
  const prev = pending.get(key);
  if (prev) clearTimeout(prev);
  const ms = vscode.workspace
    .getConfiguration(lang.section)
    .get("diagnostics.debounceMs", 300);
  pending.set(
    key,
    setTimeout(() => {
      pending.delete(key);
      void refreshDiagnostics(doc);
    }, typeof ms === "number" ? ms : 300)
  );
}

/**
 * The document's cached symbols, if they are for its current version.
 * @param {vscode.TextDocument} doc
 */
function currentSymbols(doc) {
  const cache = symbolCache.get(doc.uri.toString());
  if (
    !cache ||
    cache.documentVersion !== doc.version ||
    !cache.ranged ||
    cache.ranged.length === 0
  ) {
    return undefined;
  }
  return cache;
}

/** @type {vscode.OutputChannel | undefined} */
let eplOutput;

/**
 * `EPL: Run File`: run the active `.epl` buffer with `epl run` and show the
 * result (or the first error) in the EPL output channel.
 */
function runEplFile() {
  const editor = vscode.window.activeTextEditor;
  if (!editor || editor.document.languageId !== "epl") {
    void vscode.window.showInformationMessage("Open an .epl file to run it.");
    return;
  }
  const doc = editor.document;
  const folder = vscode.workspace.getWorkspaceFolder(doc.uri);
  const bin = resolveDiagnoseBin(folder, "epl");
  if (!eplOutput) eplOutput = vscode.window.createOutputChannel("EPL");
  const output = eplOutput;
  output.show(true);
  if (!bin) {
    output.appendLine("No epl binary: run `lake build epl`, or set `epl.path`.");
    return;
  }
  const fuel = vscode.workspace.getConfiguration("epl").get("run.fuel", 1000000);
  const name = path.basename(doc.uri.fsPath || "program.epl");
  output.appendLine(`> epl run ${name}`);
  // The output channel shows no colours.
  const env = { ...process.env, NO_COLOR: "1" };
  delete env.FORCE_COLOR;
  const child = spawn(bin, ["run", "--fuel", String(fuel)], {
    stdio: ["pipe", "pipe", "pipe"], env,
  });
  let text = "";
  child.stdout.on("data", (c) => { text += c.toString("utf8"); });
  // Errors print as `[stage] <stdin>:line:col: message`; show the file's name instead.
  child.stderr.on("data", (c) => { text += c.toString("utf8").replace(/<stdin>:/g, `${name}:`); });
  child.on("error", (err) => output.appendLine(String(err)));
  child.on("close", () => {
    output.appendLine(text.trimEnd());
    output.appendLine("");
  });
  child.stdin.write(doc.getText(), "utf8");
  child.stdin.end();
}

/** @param {vscode.ExtensionContext} context */
function activate(context) {
  diagnostics = vscode.languages.createDiagnosticCollection("fhm");
  context.subscriptions.push(diagnostics);

  context.subscriptions.push(
    vscode.commands.registerCommand("epl.run", runEplFile)
  );

  context.subscriptions.push(
    vscode.languages.registerHoverProvider(["fhm", "epl"], {
      provideHover(doc, position) {
        const cache = currentSymbols(doc);
        if (!cache) return undefined;

        const lineText = doc.lineAt(position.line).text;
        const hit = resolveHover(
          cache.ranged,
          position.line,
          position.character,
          lineText,
          cache.tokens
        );
        if (!hit) return undefined;

        const markdown = hoverMarkdown(hit, { sourceUri: doc.uri.toString(), diagnostics: cache.diagnostics });
        if (!markdown) return undefined;

        // The range is on one line and contains the cursor (see resolveHover).
        const hoverRange = new vscode.Range(
          hit.startLine0,
          hit.startCol0,
          hit.endLine0,
          hit.endCol0
        );
        return new vscode.Hover(
          new vscode.MarkdownString(markdown),
          hoverRange
        );
      },
    })
  );

  context.subscriptions.push(
    vscode.languages.registerDefinitionProvider(["fhm", "epl"], {
      provideDefinition(doc, position) {
        const cache = currentSymbols(doc);
        if (!cache) return undefined;
        const def = resolveDefinition(
          cache.ranged,
          position.line,
          position.character,
          doc.lineAt(position.line).text,
          cache.tokens
        );
        if (!def) return undefined;
        return new vscode.Location(
          doc.uri,
          new vscode.Range(def.startLine0, def.startCol0, def.endLine0, def.endCol0)
        );
      },
    })
  );

  context.subscriptions.push(
    vscode.workspace.onDidChangeTextDocument((e) => {
      scheduleRefresh(e.document);
    }),
    vscode.workspace.onDidOpenTextDocument((doc) => {
      scheduleRefresh(doc);
    }),
    vscode.workspace.onDidCloseTextDocument((doc) => {
      diagnostics.delete(doc.uri);
      const key = doc.uri.toString();
      symbolCache.delete(key);
      const t = pending.get(key);
      if (t) clearTimeout(t);
      pending.delete(key);
      const child = running.get(key);
      if (child) child.kill();
      running.delete(key);
      requestGeneration.delete(key);
    }),
    vscode.workspace.onDidSaveTextDocument((doc) => {
      // Immediate refresh on save (still didChange-primary).
      void refreshDiagnostics(doc);
    })
  );

  for (const doc of vscode.workspace.textDocuments) {
    scheduleRefresh(doc);
  }
}

function deactivate() {
  for (const t of pending.values()) clearTimeout(t);
  pending.clear();
  for (const c of running.values()) c.kill();
  running.clear();
  requestGeneration.clear();
  symbolCache.clear();
}

module.exports = {
  activate,
  deactivate,
  IDENT_RE,
  // Explicitly exposed only to the mocked lifecycle regression harness.
  __test: { refreshDiagnostics, scheduleRefresh, symbolCache, running },
};
