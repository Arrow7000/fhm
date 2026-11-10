import test from "node:test";
import assert from "node:assert/strict";
import { createRequire } from "node:module";
import { fileURLToPath } from "node:url";
import { spawnSync } from "node:child_process";
const core = createRequire(import.meta.url)("../../shared/fhmEditorCore.cjs");
const binary = fileURLToPath(new URL("../../../.lake/build/bin/fhm", import.meta.url));
function check(source) {
  const result = spawnSync(binary, ["diagnose"], {input: source, encoding: "utf8"});
  assert.ifError(result.error);
  const raw = JSON.parse(result.stdout);
  const {ranged, tokens} = core.normalizePayload(raw);
  const at = (line, column) => core.resolveHover(ranged, line - 1, column - 1, source.split("\n")[line - 1], tokens);
  const render = hit => core.hoverMarkdown(hit, {sourceUri: "file:///test.fhm", diagnostics: raw.diagnostics});
  const definition = name => {
    const symbol = ranged.find(s => s.def && s.kind === "val" && s.name === name);
    assert.ok(symbol, name);
    return at(symbol.startLine, symbol.startCol);
  };
  return {raw, ranged, at, render, definition};
}

test("blocked bindings link to the original failure through dependency chains", () => {
  const c = check("let bad = 1 True\nlet middle = bad\nlet use = middle\nuse\n");
  assert.equal(c.render(c.definition("bad")), "");
  for (const name of ["middle", "use"]) {
    assert.equal(c.definition(name).typeStatus, "unavailable");
    assert.equal(c.render(c.definition(name)), "Type unavailable because [`bad`](<file:///test.fhm#L1,5>) has an error.");
  }
  assert.equal(c.raw.diagnostics.length, 1);
});

test("multiple native causes are preserved rather than selecting one", () => {
  const c = check("let a = 1 True\nlet b = 2 False\nlet use = (a, b)\nuse\n");
  const message = c.render(c.definition("use"));
  assert.equal(message, "Type unavailable because [`a`](<file:///test.fhm#L1,5>) and [`b`](<file:///test.fhm#L2,5>) have errors.");
});

test("local causes link to the local binder despite same-named outer definitions", () => {
  const c = check("let bad = 42\nlet f x = let bad = 1 True in let use = bad in use\n0\n");
  assert.equal(c.render(c.definition("use")), "Type unavailable because [`bad`](<file:///test.fhm#L2,15>) has an error.");
  assert.equal(c.render(c.at(1, 5)), "```fhm\nbad : Int\n```");
});

test("invalid declarations and syntax get appropriate source links", () => {
  const declaration = check("type Bad = MkBad _\nlet use : Bad = MkBad 1\nuse\n");
  assert.equal(declaration.render(declaration.definition("use")), "Type unavailable because [`Bad`](<file:///test.fhm#L1,6>) has an error.");
  const syntax = check("let bad = if True then\nlet use = bad\nuse\n");
  assert.match(syntax.render(syntax.definition("use")), /^Type unavailable because \[a syntax error\].*blocked type checking\.$/);
});

test("local errors retain established facts and do not get redundant failure hovers", () => {
  const c = check("let f x = (1 True, x + 1)\n0\n");
  assert.equal(c.render(c.definition("f")), "");
  assert.match(c.render(c.at(1, 7)), /x : Int/);
  assert.match(c.render(c.at(1, 14)), /True : Bool/);
  for (const s of c.ranged.filter(s => s.typeStatus === "unavailable")) {
    const message = c.render(c.at(s.startLine, s.startCol));
    assert.ok(!message.includes("type unknown"), message);
  }
});

test("declared and conditional signatures stay distinct from inference failures", () => {
  const c = check("let broken : Int -> Int = \\x -> True\nlet use = broken 1\nuse\n");
  assert.match(c.render(c.definition("broken")), /broken : Int → Int/);
  assert.match(c.render(c.definition("broken")), /Declared type/);
  assert.match(c.render(c.definition("use")), /use : Int/);
  assert.match(c.render(c.definition("use")), /unvalidated declared interfaces/);
  assert.match(c.render(c.at(1, "let broken : Int -> Int = \\x -> True".indexOf("True") + 1)), /True : Bool/);
});

test("links use host document URIs; missing targets do not invent a location", () => {
  const hit = {typeStatus: "unavailable", failureCauses: [{label:"missing", kind:"binding"}], unavailableCauseCount:1};
  assert.equal(core.hoverMarkdown(hit, {sourceUri:"file:///test.fhm"}), "Type unavailable because `missing` has an error.");
  hit.failureCauses[0].line = 1;
  hit.failureCauses[0].col = 5;
  assert.equal(core.hoverMarkdown(hit, {sourceUri:"command:evil"}), "Type unavailable because `missing` has an error.");
});


test("whole expressions can show an expected annotation without claiming an inferred type", () => {
  const source = "let broken : Int -> Int = \\x -> if True then True else member x\nlet member x = broken x\nmember 1\n";
  const c = check(source);
  const lambda = c.at(1, source.indexOf("\\x") + 1);
  assert.equal(lambda.typeStatus, "unavailable");
  assert.equal(lambda.typeExpected, "Int → Int");
  assert.equal(c.render(lambda), "Expected type from annotation:\n\n```fhm\nInt → Int\n```");
  assert.match(c.render(c.at(1, source.indexOf("then True") + 6)), /True : Bool/);
  const unsigned = check("let broken = \\x -> if x then True else 1\n0\n");
  assert.ok(!unsigned.ranged.some(s => s.typeExpected));
  const parameters = check("let broken (x : Int) : Int = if True then True else x\n0\n");
  assert.ok(!parameters.ranged.some(s => s.typeExpected), "a function signature is not the expected type of its parameterised RHS");
});


test("ambiguous duplicate definitions never produce an arbitrary source link", () => {
  const definition = (name, line, extra = {}) => ({name, kind: "val", type: "type unknown (error)", def: true,
    startLine: line, startCol: 5, endLine: line, endCol: 5 + name.length,
    scopeStartLine: 1, scopeStartCol: 1, scopeEndLine: 4, scopeEndCol: 1, ...extra});
  const {ranged} = core.normalizePayload({version:3, symbols:[definition("bad",1), definition("bad",2),
    definition("use",3,{typeStatus:"unavailable",typeUnavailableCauses:[{kind:"binding",name:"bad"}]})]});
  const hit = core.resolveHover(ranged, 2, 4, "let use = bad");
  assert.equal(core.hoverMarkdown(hit, {sourceUri:"file:///test.fhm"}), "Type unavailable because `bad` has an error.");
});
