//@ts-check
"use strict";

const vscode = require("vscode");
const { spawn } = require("child_process");
const fs = require("fs");
const path = require("path");
const {
  normalizePayload,
  resolveHover,
  diagnosticsToMarkers,
  IDENT_RE,
} = require("../shared/fhmEditorCore.cjs");

/** @type {vscode.DiagnosticCollection} */
let diagnostics;
/** @type {Map<string, NodeJS.Timeout>} */
const pending = new Map();
/** @type {Map<string, import("child_process").ChildProcess>} */
const running = new Map();
/**
 * Cached v3 ranged symbols (def span + lexical scope for use-site).
 * @type {Map<string, { version: number, ranged: any[] }>}
 */
const symbolCache = new Map();

/**
 * @param {vscode.WorkspaceFolder | undefined} folder
 * @returns {string | undefined}
 */
function resolveDiagnoseBin(folder) {
  const configured = vscode.workspace
    .getConfiguration("fhm")
    .get("diagnosePath", "");
  if (configured && typeof configured === "string" && configured.length > 0) {
    return configured;
  }
  if (!folder) return undefined;
  const candidate = path.join(
    folder.uri.fsPath,
    ".lake",
    "build",
    "bin",
    "fhm"
  );
  return fs.existsSync(candidate) ? candidate : undefined;
}

/**
 * @param {vscode.TextDocument} doc
 */
async function refreshDiagnostics(doc) {
  if (doc.languageId !== "fhm" || doc.uri.scheme !== "file") return;

  const cfg = vscode.workspace.getConfiguration("fhm");
  if (!cfg.get("diagnostics.enable", true)) {
    diagnostics.set(doc.uri, []);
    return;
  }

  const folder = vscode.workspace.getWorkspaceFolder(doc.uri);
  const bin = resolveDiagnoseBin(folder);
  if (!bin) {
    // Highlighting still works; diagnostics need `lake build fhm`.
    return;
  }

  const key = doc.uri.toString();
  const prev = running.get(key);
  if (prev) {
    prev.kill();
    running.delete(key);
  }

  try {
    const raw = await new Promise((resolve, reject) => {
      const child = spawn(bin, ["diagnose"], { stdio: ["pipe", "pipe", "pipe"] });
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
        running.delete(key);
        try {
          resolve(JSON.parse(stdout.trim() || "[]"));
        } catch (err) {
          reject(
            new Error(
              `fhm diagnose parse failed (exit ${code}): ${stderr || String(err)}`
            )
          );
        }
      });
      child.stdin.write(doc.getText(), "utf8");
      child.stdin.end();
    });

    const { diagnostics: diagArr, version, ranged } = normalizePayload(raw);
    symbolCache.set(key, { version, ranged });

    /** @type {vscode.Diagnostic[]} */
    const diags = diagnosticsToMarkers(diagArr).map((m) => {
      const range = new vscode.Range(m.line0, m.col0, m.line0, m.col0 + 1);
      const severity =
        m.severity === "warning"
          ? vscode.DiagnosticSeverity.Warning
          : vscode.DiagnosticSeverity.Error;
      return new vscode.Diagnostic(range, m.message, severity);
    });
    diagnostics.set(doc.uri, diags);
  } catch (err) {
    // Keep last good diagnostics/symbols; surface once via console for debugging.
    console.error("[fhm]", err);
  }
}

/**
 * @param {vscode.TextDocument} doc
 */
function scheduleRefresh(doc) {
  if (doc.languageId !== "fhm") return;
  const key = doc.uri.toString();
  const prev = pending.get(key);
  if (prev) clearTimeout(prev);
  const ms = vscode.workspace
    .getConfiguration("fhm")
    .get("diagnostics.debounceMs", 300);
  pending.set(
    key,
    setTimeout(() => {
      pending.delete(key);
      void refreshDiagnostics(doc);
    }, typeof ms === "number" ? ms : 300)
  );
}

/** @param {vscode.ExtensionContext} context */
function activate(context) {
  diagnostics = vscode.languages.createDiagnosticCollection("fhm");
  context.subscriptions.push(diagnostics);

  context.subscriptions.push(
    vscode.languages.registerHoverProvider("fhm", {
      provideHover(doc, position) {
        const cache = symbolCache.get(doc.uri.toString());
        if (!cache || !cache.ranged || cache.ranged.length === 0) {
          return undefined;
        }

        const lineText = doc.lineAt(position.line).text;
        const hit = resolveHover(
          cache.ranged,
          position.line,
          position.character,
          lineText
        );
        if (!hit) return undefined;

        let endLine = hit.endLine0;
        let endCol = hit.endCol0;
        if (
          endLine < hit.startLine0 ||
          (endLine === hit.startLine0 && endCol <= hit.startCol0)
        ) {
          endLine = hit.startLine0;
          endCol = hit.startCol0 + Math.max(1, hit.name?.length ?? 1);
        }
        if (endLine !== hit.startLine0 || endCol - hit.startCol0 > 128) {
          endLine = hit.startLine0;
          endCol = hit.startCol0 + Math.max(1, hit.name?.length ?? 1);
        }

        const hoverRange = new vscode.Range(
          hit.startLine0,
          hit.startCol0,
          endLine,
          endCol
        );
        const md = new vscode.MarkdownString();
        const kind = String(hit.kind || "val").replace(/[`*]/g, "");
        const name = String(hit.name || "?").replace(/[`*]/g, "");
        const ty = String(hit.type || "?").replace(/`/g, "'");
        md.appendMarkdown(`\`${kind}\` **${name}** : \`${ty}\``);
        return new vscode.Hover(md, hoverRange);
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
  symbolCache.clear();
}

module.exports = { activate, deactivate, IDENT_RE };
