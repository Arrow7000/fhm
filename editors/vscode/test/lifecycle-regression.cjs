"use strict";

// Minimal VS Code/child-process harness for extension cache lifecycle races.
// Run: node editors/vscode/test/lifecycle-regression.cjs
const assert = require("assert");
const { EventEmitter } = require("events");
const Module = require("module");

const children = [];
const settings = {
  "diagnosePath": "/mock/fhm",
  "diagnostics.enable": false,
  "diagnostics.debounceMs": 0,
};
const markerSets = [];
let hoverProvider;

function child() {
  const c = new EventEmitter();
  c.stdout = new EventEmitter();
  c.stderr = new EventEmitter();
  c.stdin = { write() {}, end() {} };
  c.kill = () => { c.killed = true; };
  c.finish = (payload) => {
    c.stdout.emit("data", Buffer.from(JSON.stringify(payload)));
    c.emit("close", 0);
  };
  return c;
}

const vscode = {
  workspace: {
    getConfiguration: () => ({ get: (key, fallback) => settings[key] ?? fallback }),
    getWorkspaceFolder: () => undefined,
    textDocuments: [],
    onDidChangeTextDocument: () => ({ dispose() {} }),
    onDidOpenTextDocument: () => ({ dispose() {} }),
    onDidCloseTextDocument: () => ({ dispose() {} }),
    onDidSaveTextDocument: () => ({ dispose() {} }),
  },
  languages: {
    createDiagnosticCollection: () => ({
      set(_uri, markers) { markerSets.push(markers); },
      delete() {},
      dispose() {},
    }),
    registerHoverProvider: (_language, provider) => {
      hoverProvider = provider;
      return { dispose() {} };
    },
  },
  Range: class Range { constructor(...args) { this.args = args; } },
  Diagnostic: class Diagnostic {},
  DiagnosticSeverity: { Warning: 1, Error: 0 },
  MarkdownString: class MarkdownString { appendMarkdown() {} },
  Hover: class Hover { constructor(...args) { this.args = args; } },
};

const originalLoad = Module._load;
Module._load = function (request, parent, isMain) {
  if (request === "vscode") return vscode;
  if (request === "child_process") {
    return { spawn: () => { const c = child(); children.push(c); return c; } };
  }
  return originalLoad.call(this, request, parent, isMain);
};
const extension = require("../extension.js");
Module._load = originalLoad;

extension.activate({ subscriptions: { push() {} } });
const uri = { scheme: "file", toString: () => "file:///audit.fhm" };
const doc = {
  languageId: "fhm", uri, version: 1,
  getText: () => "let x = 1", lineAt: () => ({ text: "let x = 1" }),
};
const payload = (name) => ({
  version: 3, diagnostics: [], symbols: [{
    name, kind: "val", type: "Int", startLine: 1, startCol: 5,
    endLine: 1, endCol: 6, scopeStartLine: 1, scopeStartCol: 1,
    scopeEndLine: 1, scopeEndCol: 10,
  }],
});
const flush = () => new Promise((resolve) => setImmediate(resolve));

(async () => {
  // Disabling markers must not disable diagnose/symbol-cache updates for hover.
  const disabled = extension.__test.refreshDiagnostics(doc);
  assert.equal(children.length, 1, "disabled diagnostics still starts diagnose");
  children[0].finish(payload("x"));
  await disabled;
  assert.equal(extension.__test.symbolCache.get(uri.toString()).ranged[0].name, "x");
  assert.deepEqual(markerSets.at(-1), [], "disabled diagnostics stays clear");
  assert(hoverProvider.provideHover(doc, { line: 0, character: 4 }));

  // An obsolete close may arrive after its replacement begins, but cannot
  // unregister or publish over that replacement.
  settings["diagnostics.enable"] = true;
  const old = extension.__test.refreshDiagnostics(doc);
  const oldChild = children.at(-1);
  doc.version = 2;
  const current = extension.__test.refreshDiagnostics(doc);
  const currentChild = children.at(-1);
  assert.notEqual(oldChild, currentChild);
  assert.equal(oldChild.killed, true);
  oldChild.finish(payload("old"));
  await old;
  assert.equal(extension.__test.running.get(uri.toString()), currentChild);
  currentChild.finish(payload("new"));
  await current;
  await flush();
  const cache = extension.__test.symbolCache.get(uri.toString());
  assert.equal(cache.documentVersion, 2);
  assert.equal(cache.ranged[0].name, "new");
  console.log("VS Code lifecycle regressions: PASS");
})().catch((err) => { console.error(err); process.exitCode = 1; });
