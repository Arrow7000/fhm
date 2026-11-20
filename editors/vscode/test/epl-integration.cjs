"use strict";
// Run: lake build epl && node editors/vscode/test/epl-integration.cjs
// Only the VS Code host API is simulated. The extension spawns the real
// workspace `epl` binary for an `.epl` document and publishes its diagnostics.
const assert = require("node:assert/strict");
const Module = require("node:module");
const path = require("node:path");
const root = path.resolve(__dirname, "../../..");
assert(require("node:fs").existsSync(path.join(root, ".lake/build/bin/epl")), "Run lake build epl before this integration test");

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
      assert(language.includes("epl")); hoverProvider = provider; return disposable();
    },
    registerDefinitionProvider: (language, provider) => {
      assert(language.includes("epl")); definitionProvider = provider; return disposable();
    },
  },
  commands: { registerCommand: disposable },
  Hover: class Hover { constructor(contents, range) { Object.assign(this, { contents, range }); } },
  MarkdownString: class MarkdownString { constructor(value) { this.value = value; } },
  Location: class Location { constructor(uri, range) { Object.assign(this, { uri, range }); } },
  Range: class Range { constructor(...args) { this.args = args; } },
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
extension.activate({ subscriptions: [] });

let text = "";
const uri = { scheme: "file", fsPath: "/tmp/editor-test.epl", toString: () => "file:///tmp/editor-test.epl" };
const doc = { languageId: "epl", uri, version: 0, getText: () => text, lineAt: line => ({ text: text.split("\n")[line] }) };
async function update(source, open = false) {
  const before = markerSets.length;
  text = source; doc.version++;
  if (open) listeners.Open(doc); else listeners.Change({ document: doc });
  const until = Date.now() + 15000;
  while (markerSets.length === before) {
    if (Date.now() > until) throw new Error("diagnose publication timed out");
    await new Promise(resolve => setTimeout(resolve, 10));
  }
  return markerSets.at(-1).markers.map(d => ({ message: d.message, range: d.range.args }));
}

function hover(line, character) {
  return hoverProvider.provideHover(doc, { line, character })?.contents.value;
}
function definition(line, character) {
  return definitionProvider.provideDefinition(doc, { line, character })?.range.args;
}

(async () => {
  assert.deepEqual(await update("let id {a} (x : a) : a = x\n(id 1, id True)\n", true), []);
  assert.deepEqual(await update("let id x = x\n(id 1, id True)\n"), [
    { message: "Type mismatch: expected `Int`, found `Bool`.", range: [1, 10, 1, 14] },
  ]);
  // Positions are UTF-16: the emoji takes two columns.
  assert.deepEqual(await update("let 🌀 = 1\n🌀 'a'\n"), [
    { message: "This is applied to an argument, but its type `Int` is not a function type.", range: [1, 0, 1, 2] },
  ]);
  assert.deepEqual(await update("type Maybe a = Just a | Nothing\nmatch Just 1 with\n| Just x -> x\n"), [
    { message: "This match does not cover the case `Nothing`.", range: [1, 6, 1, 12] },
  ]);

  // Hover shows the types inference found; go-to-definition finds the binder.
  assert.deepEqual(await update("type Maybe a = Just a | Nothing\nlet id {a} (x : a) : a = x\n" +
    "let n = id 1 -- one\nmatch Just n with\n| Just y -> y\n| Nothing -> 0\n"), []);
  assert.equal(hover(1, 4), "```epl\nid : {a} a -> a\n```");
  assert.equal(hover(1, 12), "```epl\nx : a\n```");
  assert.equal(hover(2, 8), "```epl\nid : Int -> Int\n```");
  assert.equal(hover(3, 6), "```epl\nJust : Int -> Maybe Int\n```\n\n---\n\n" +
    "```epl\ntype Maybe a =\n  | Just a\n  | Nothing\n```");
  assert.equal(hover(4, 12), "```epl\ny : Int\n```");
  assert.equal(hover(2, 15), undefined, "no hover in a comment");
  assert.deepEqual(definition(3, 11), [2, 4, 2, 5]);
  assert.deepEqual(definition(4, 12), [4, 7, 4, 8]);
  assert.deepEqual(definition(2, 8), [1, 4, 1, 6]);

  // Types, type variables, constructors and doc comments.
  assert.deepEqual(await update("--- Maybe a value.\ntype Maybe a = Just a | Nothing\n" +
    "/-- Wrap it. -/\nlet wrap {a} (x : a) : Maybe a = Just x\nmatch wrap 1 with\n| Just y -> y\n| Nothing -> 0\n"), []);
  const maybe = "```epl\ntype Maybe a =\n  | Just a\n  | Nothing\n```";
  assert.equal(hover(3, 23), maybe + "\n\n---\n\nMaybe a value.");
  assert.deepEqual(definition(3, 23), [1, 5, 1, 10]);
  assert.equal(hover(3, 29), "```epl\na\n```\n\n_type variable (of wrap)_");
  assert.deepEqual(definition(3, 29), [3, 10, 3, 11]);
  assert.equal(hover(1, 20), "```epl\na\n```\n\n_type variable (of Maybe)_");
  assert.equal(hover(4, 7), "```epl\nwrap : Int -> Maybe Int\n```\n\n---\n\nWrap it.");
  assert.equal(hover(5, 3), "```epl\nJust : {a} a -> Maybe a\n```\n\n---\n\n" + maybe);
  assert.deepEqual(definition(5, 3), [1, 15, 1, 19]);
  assert.deepEqual(await update("let f x y = x + y\nmatch f 1 2 :: [] with\n| n :: _ -> n < 3\n| [] -> False\n"), []);
  assert.equal(hover(0, 14), "```epl\n(+) : Int -> Int -> Int\n```");
  assert.equal(hover(1, 12), "```epl\n(::) : Int -> List Int -> List Int\n```");
  assert.equal(hover(2, 4), "```epl\n(::) : {a} a -> List a -> List a\n```");
  assert.equal(hover(2, 14), "```epl\n(<) : Int -> Int -> Bool\n```");
  assert.deepEqual(await update("let x = 1\n--- Nothing here.\nx\n"), [
    { message: "A doc comment must come before a `let`, a `type` or a constructor.", range: [1, 0, 1, 17] },
  ]);
  console.log("VS Code EPL integration: PASS (8 real-backend scenarios)");
})().catch(err => { console.error(err); process.exit(1); });
