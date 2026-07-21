//@ts-check
"use strict";

const vscode = require("vscode");
const { spawn } = require("child_process");
const fs = require("fs");
const path = require("path");

/** @type {vscode.DiagnosticCollection} */
let diagnostics;
/** @type {Map<string, NodeJS.Timeout>} */
const pending = new Map();
/** @type {Map<string, import("child_process").ChildProcess>} */
const running = new Map();
/** @type {Map<string, Record<string, { type: string, kind: string }>>} */
const symbolCache = new Map();

const IDENT_RE = /[A-Za-z_🎉-💫][A-Za-z0-9_🎉-💫]*/u;

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
    "fhm_diagnose"
  );
  return fs.existsSync(candidate) ? candidate : undefined;
}

/**
 * Normalize diagnose stdout: new `{diagnostics,symbols}` object, or legacy array.
 * @param {unknown} raw
 * @returns {{ diagnostics: any[], symbols: Record<string, { type: string, kind: string }> }}
 */
function normalizePayload(raw) {
  if (Array.isArray(raw)) {
    return { diagnostics: raw, symbols: {} };
  }
  if (raw && typeof raw === "object") {
    const obj = /** @type {Record<string, unknown>} */ (raw);
    const diags = Array.isArray(obj.diagnostics) ? obj.diagnostics : [];
    const symbols =
      obj.symbols && typeof obj.symbols === "object" && !Array.isArray(obj.symbols)
        ? /** @type {Record<string, { type: string, kind: string }>} */ (obj.symbols)
        : {};
    return { diagnostics: diags, symbols };
  }
  return { diagnostics: [], symbols: {} };
}

/**
 * @param {vscode.TextDocument} doc
 * @param {vscode.Position} pos
 * @returns {{ word: string, range: vscode.Range } | undefined}
 */
function identAtPosition(doc, pos) {
  const range = doc.getWordRangeAtPosition(pos, IDENT_RE);
  if (!range) return undefined;
  const word = doc.getText(range);
  if (!word) return undefined;
  return { word, range };
}

/**
 * @param {string} kind
 * @returns {string}
 */
function kindBadge(kind) {
  if (kind === "type") return "type";
  if (kind === "ctor") return "ctor";
  return "val";
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
    // Highlighting still works; diagnostics need `lake build fhm_diagnose`.
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
      const child = spawn(bin, [], { stdio: ["pipe", "pipe", "pipe"] });
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
              `fhm_diagnose parse failed (exit ${code}): ${stderr || String(err)}`
            )
          );
        }
      });
      child.stdin.write(doc.getText(), "utf8");
      child.stdin.end();
    });

    const { diagnostics: diagArr, symbols } = normalizePayload(raw);
    symbolCache.set(key, symbols);

    /** @type {vscode.Diagnostic[]} */
    const diags = diagArr.map((d) => {
      const line = Math.max(0, (d.line || 1) - 1);
      const col = Math.max(0, (d.col || 1) - 1);
      const range = new vscode.Range(line, col, line, col + 1);
      const severity =
        d.severity === "warning"
          ? vscode.DiagnosticSeverity.Warning
          : vscode.DiagnosticSeverity.Error;
      return new vscode.Diagnostic(range, d.message || "error", severity);
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
        const hit = identAtPosition(doc, position);
        if (!hit) return undefined;
        const symbols = symbolCache.get(doc.uri.toString());
        if (!symbols) return undefined;
        const sym = symbols[hit.word];
        if (!sym || typeof sym.type !== "string") return undefined;
        const badge = kindBadge(sym.kind);
        const md = new vscode.MarkdownString();
        md.appendMarkdown(`\`${badge}\` **${hit.word}** : \`${sym.type}\``);
        return new vscode.Hover(md, hit.range);
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

module.exports = { activate, deactivate };
