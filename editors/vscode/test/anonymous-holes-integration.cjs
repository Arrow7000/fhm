"use strict";
// Run: lake build fhm && node editors/vscode/test/anonymous-holes-integration.cjs
// Only the VS Code host API is simulated. The unchanged extension spawns the real
// workspace fhm binary; this tests provider integration, not an LSP protocol or UI.
const assert = require("node:assert/strict");
const Module = require("node:module");
const path = require("node:path");
const root = path.resolve(__dirname, "../../..");
assert(require("node:fs").existsSync(path.join(root, ".lake/build/bin/fhm")), "Run lake build fhm before this integration test");
const settings = { "diagnostics.debounceMs": 0, "diagnostics.enable": true };
const listeners = {};
const markerSets = [];
let hoverProvider, definitionProvider;
const disposable = () => ({ dispose() {} });
const vscode = {
  workspace: {
    getConfiguration: () => ({ get: (key, fallback) => settings[key] ?? fallback }),
    getWorkspaceFolder: () => ({ uri: { fsPath: root } }),
    textDocuments: [],
    ...Object.fromEntries(["Change", "Open", "Close", "Save"].map(kind => [
      `onDid${kind}TextDocument`, callback => { listeners[kind] = callback; return disposable(); }
    ])),
  },
  languages: {
    createDiagnosticCollection: () => ({
      set(uri, markers) { markerSets.push({ uri: uri.toString(), markers }); },
      delete() {}, dispose() {},
    }),
    registerHoverProvider: (language, provider) => {
      assert.equal(language, "fhm"); hoverProvider = provider; return disposable();
    },
    registerDefinitionProvider: (language, provider) => {
      assert.equal(language, "fhm"); definitionProvider = provider; return disposable();
    },
  },
  Range: class Range { constructor(...args) { this.args = args; } },
  MarkdownString: class MarkdownString { constructor(value) { this.value = value; } },
  Hover: class Hover { constructor(contents, range) { this.contents = contents; this.range = range; } },
  Location: class Location { constructor(uri, range) { this.uri = uri; this.range = range; } },
  Diagnostic: class Diagnostic { constructor(range, message, severity) { Object.assign(this, { range, message, severity }); } },
  DiagnosticSeverity: { Error: 0, Warning: 1 },
};
const originalLoad = Module._load;
Module._load = function(request, parent, isMain) {
  if (request === "vscode") return vscode;
  return originalLoad.call(this, request, parent, isMain);
};
let extension;
try { extension = require("../extension.js"); }
finally { Module._load = originalLoad; }
const subscriptions = [];
extension.activate({ subscriptions });
let text = "";
const uri = { scheme: "file", fsPath: "/tmp/fhm-editor-anonymous.fhm", toString: () => "file:///tmp/fhm-editor-anonymous.fhm" };
const doc = {
  languageId: "fhm", uri, version: 0,
  getText: () => text,
  lineAt: line => ({ text: text.split("\n")[line] }),
};
async function update(source, open = false) {
  const before = markerSets.length;
  text = source; doc.version++;
  if (open) listeners.Open(doc); else listeners.Change({ document: doc });
  assert.equal(hoverProvider.provideHover(doc, { line: 0, character: source.indexOf("_") }), undefined,
    "didOpen/didChange invalidates stale hover synchronously");
  const until = Date.now() + 15000;
  while (markerSets.length === before) {
    if (Date.now() > until) throw new Error("diagnose publication timed out");
    await new Promise(resolve => setTimeout(resolve, 10));
  }
  return markerSets.at(-1).markers;
}
function hole(expected, occurrence = 0, line = 0) {
  const lineText = doc.lineAt(line).text;
  let column = -1;
  for (let i = 0; i <= occurrence; i++) column = lineText.indexOf("_", column + 1);
  assert(column >= 0);
  const result = hoverProvider.provideHover(doc, { line, character: column });
  assert(result, "actual extension returns hover at underscore");
  assert.equal(result.contents.value, `\`\`\`fhm\n_ : ${expected}\n\`\`\``);
  assert.deepEqual(result.range.args, [line, column, line, column + 1]);
  assert.equal(definitionProvider.provideDefinition(doc, { line, character: column }), undefined,
    "anonymous hole has no declaration target");
  return { markdown: result.contents.value, range: result.range.args };
}
const results = [];
(async () => {
  assert.deepEqual(await update("let id = \\(x : _) -> x\n(id 1, id True)\n", true), []);
  const generic = hole("a");
  const definition = definitionProvider.provideDefinition(doc, { line: 1, character: 1 });
  assert.deepEqual(definition.range.args, [0, 4, 0, 6]);
  results.push({ case: "didOpen generic lambda hole + id definition", hover: generic, definition: definition.range.args });

  assert.deepEqual(await update("(\\(x : _) -> x) 1\n"), []);
  results.push({ case: "didChange hole solved Int", hover: hole("Int") });
  assert.deepEqual(await update("(\\(x : _) -> x) True\n"), []);
  results.push({ case: "didChange same hole solved Bool", hover: hole("Bool") });

  const bad = await update("let f : Int -> _ = \\x -> x\nf True\n");
  assert(bad.some(d => d.severity === 0 && /expected Int, got Bool/.test(d.message)),
    "fixed Int constraint produces actual type mismatch diagnostic");
  assert.deepEqual(bad[0].range.args, [1, 2, 1, 6]);
  results.push({ case: "fixed Int input rejects Bool", diagnostics: bad.map(d => ({ message: d.message, range: d.range.args })) });

  assert.deepEqual(await update("let keep : {element} element -> _ -> element = \\x y -> x\nkeep 1 True\n"), []);
  results.push({ case: "recovery + partial forall", hover: hole("a") });

  assert.deepEqual(await update("let sum = \\(n : _) -> if n < 1 then 0 else n + sum (n - 1)\nsum 3\n"), []);
  results.push({ case: "recursive hole", hover: hole("Int") });

  assert.deepEqual(await update("let f = \\p -> match p with | (True,True)->1 | _ -> let id = \\(x:_) -> x in id 2\nf (False,False)\n"), []);
  results.push({ case: "copied match fallback hole", hover: hole("a", 1) });

  const patternSource = "let first = \\(x : _) -> x\n" +
    "let second : _ -> _ = \\x -> 1\n" +
    "let (id, n) : (_, _) = (\\(x : _) -> x, 7)\n(id True, n)\n";
  assert.deepEqual(await update(patternSource), []);
  results.push({ case: "top-level pattern after two definitions", hovers: [
    hole("a → a", 0, 2), hole("Int", 1, 2), hole("a", 2, 2)
  ] });

  listeners.Close(doc);
  assert.equal(hoverProvider.provideHover(doc, { line: 2, character: 15 }), undefined);
  extension.deactivate();
  console.log(`VS Code anonymous-hole integration: PASS (${results.length} real-backend scenarios)`);
})().catch(error => { extension.deactivate(); console.error(error); process.exitCode = 1; });
