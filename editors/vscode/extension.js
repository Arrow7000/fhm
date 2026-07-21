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
/**
 * Cached v2 ranged symbols (span containment only; no name fallback).
 * @type {Map<string, { version: number, ranged: any[] }>}
 */
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
 * @param {any} sym
 * @returns {boolean}
 */
function isRangedSymbol(sym) {
  return (
    sym &&
    typeof sym === "object" &&
    typeof sym.name === "string" &&
    typeof sym.startLine === "number" &&
    typeof sym.startCol === "number" &&
    typeof sym.endLine === "number" &&
    typeof sym.endCol === "number"
  );
}

/**
 * Half-open span containment (1-based), matching lexer / Span.contains.
 * @param {any} s
 * @param {number} line
 * @param {number} col
 */
function spanContains(s, line, col) {
  const afterStart =
    line > s.startLine || (line === s.startLine && col >= s.startCol);
  const beforeEnd =
    line < s.endLine || (line === s.endLine && col < s.endCol);
  return afterStart && beforeEnd;
}

/**
 * @param {any} s
 * @returns {number}
 */
function spanArea(s) {
  if (s.startLine === s.endLine) return s.endCol - s.startCol;
  return (
    (s.endLine - s.startLine) * 10000 + (s.endCol + (10000 - s.startCol))
  );
}

/**
 * @param {any[]} ranged
 * @param {number} line 1-based
 * @param {number} col 1-based
 * @returns {any | undefined}
 */
function symbolAtRanged(ranged, line, col) {
  const hits = ranged.filter((s) => spanContains(s, line, col));
  if (hits.length === 0) return undefined;
  let best = hits[0];
  for (let i = 1; i < hits.length; i++) {
    const s = hits[i];
    const aBest = spanArea(best);
    const aS = spanArea(s);
    if (aS < aBest || aS === aBest) best = s;
  }
  return best;
}

/**
 * Normalize diagnose stdout: v2 ranged symbols (legacy v1 name-map ignored for hover).
 * @param {unknown} raw
 * @returns {{ diagnostics: any[], version: number, ranged: any[] }}
 */
function normalizePayload(raw) {
  if (Array.isArray(raw)) {
    return { diagnostics: raw, version: 0, ranged: [] };
  }
  if (raw && typeof raw === "object") {
    const obj = /** @type {Record<string, unknown>} */ (raw);
    const diags = Array.isArray(obj.diagnostics) ? obj.diagnostics : [];
    const version = typeof obj.version === "number" ? obj.version : 1;
    if (Array.isArray(obj.symbols)) {
      const ranged = obj.symbols.filter(isRangedSymbol);
      return { diagnostics: diags, version, ranged };
    }
    return { diagnostics: diags, version, ranged: [] };
  }
  return { diagnostics: [], version: 0, ranged: [] };
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
  if (kind === "param") return "param";
  if (kind === "pat") return "pat";
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

    const { diagnostics: diagArr, version, ranged } = normalizePayload(raw);
    symbolCache.set(key, { version, ranged });

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
        const cache = symbolCache.get(doc.uri.toString());
        if (!cache) return undefined;

        // VS Code position is 0-based; diagnose spans are 1-based.
        const line = position.line + 1;
        const col = position.character + 1;

        if (!cache.ranged || cache.ranged.length === 0) return undefined;
        const sym = symbolAtRanged(cache.ranged, line, col);
        // Span hit only; never fill empty types from a name map.
        if (!sym || typeof sym.type !== "string" || sym.type.length === 0) {
          return undefined;
        }
        const badge = kindBadge(sym.kind || "val");
        const name = typeof sym.name === "string" ? sym.name : hit.word;
        const md = new vscode.MarkdownString();
        md.appendMarkdown(`\`${badge}\` **${name}** : \`${sym.type}\``);
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
