#!/usr/bin/env node
// Complete interfaces are editor assumptions; strict run still checks bodies.
import assert from "node:assert/strict";
import { spawnSync } from "node:child_process";
import { readFileSync } from "node:fs";
import { createRequire } from "node:module";
import { fileURLToPath } from "node:url";
const core = createRequire(import.meta.url)("../editors/shared/fhmEditorCore.cjs");
const binary = process.env.FHM || fileURLToPath(new URL("../.lake/build/bin/fhm", import.meta.url));
let tests = 0, failures = 0;
function cli(source, args = ["diagnose"]) {
  const result = spawnSync(binary, args, { input: source, encoding: "utf8", timeout: 15000 });
  assert.ifError(result.error);
  assert.equal(result.signal, null);
  return { status: result.status, payload: JSON.parse(result.stdout) };
}
function test(name, body) {
  tests++;
  try { body(); console.log(`PASS ${name}`); }
  catch (error) { failures++; console.error(`FAIL ${name}: ${error.stack}`); }
}
function definition(payload, name, line) {
  const found = payload.symbols.find(s => s.def && s.kind === "val" && s.name === name && (!line || s.startLine === line));
  assert.ok(found, `Missing definition ${name}`);
  return found;
}
function at(payload, source, line0, word, occurrence = 0) {
  const { ranged, tokens } = core.normalizePayload(payload);
  const line = source.split("\n")[line0];
  const col = [...line.matchAll(new RegExp(`\\b${word}\\b`, "g"))][occurrence]?.index;
  assert.notEqual(col, undefined);
  return { hover: core.resolveHover(ranged, line0, col, line, tokens),
    definition: core.resolveDefinition(ranged, line0, col, line, tokens) };
}
const simple = "--- A declared interface survives its implementation error.\n" +
  "let broken : Int -> Int = \\x -> True\nlet number = broken 3\nlet wrong = broken False\nnumber\n";

test("complete function contracts type callers and diagnose incompatible arguments", () => {
  const { status, payload } = cli(simple);
  assert.equal(status, 1);
  assert.deepEqual(payload.diagnostics.map(d => d.code), ["type.annotationMismatch", "type.argumentMismatch"]);
  assert.equal(definition(payload, "broken").type, "Int → Int");
  assert.equal(definition(payload, "broken").typeStatus, "declared");
  assert.equal(definition(payload, "number").type, "Int");
  assert.equal(definition(payload, "number").typeStatus, "conditional");
  assert.deepEqual(definition(payload, "number").typeAssumptions.map(a => a.name), ["broken"]);
  assert.equal(payload.programTy, "Int");
  assert.deepEqual(payload.programTypeAssumptions.map(a => a.name), ["broken"]);
  assert.equal(cli(simple, ["run", "--json"]).payload.ok, false);
});

test("both editor clients receive provenance notes, documentation and original navigation", () => {
  const { payload } = cli(simple);
  const declared = at(payload, simple, 1, "broken");
  const use = at(payload, simple, 2, "broken");
  assert.equal(declared.hover.typeStatus, "declared");
  assert.equal(use.hover.typeStatus, "conditional");
  assert.match(core.hoverMarkdown(declared.hover), /Declared type; implementation is not fully validated/);
  assert.match(core.hoverMarkdown(use.hover), /unvalidated declared interfaces: `broken`/);
  assert.match(use.hover.doc, /declared interface survives/);
  assert.deepEqual([use.definition.startLine0, use.definition.startCol0], [1, 4]);
});

test("closed scalar contracts carry their assumptions through transitive bindings", () => {
  const source = "let bad : Int = True\nlet one = bad + 1\nlet two = one + 1\ntwo\n";
  const { payload } = cli(source);
  assert.equal(payload.diagnostics.length, 1);
  for (const name of ["one", "two"]) {
    assert.equal(definition(payload, name).type, "Int");
    assert.deepEqual(definition(payload, name).typeAssumptions.map(a => a.name), ["bad"]);
  }
});

test("complete polymorphic contracts instantiate independently and preserve authored names", () => {
  const source = "let bad : {item} item -> item = \\x -> 1 True\nlet number = bad 7\nlet truth = bad False\n(number, truth)\n";
  const { payload } = cli(source);
  assert.equal(payload.diagnostics.length, 1);
  assert.equal(definition(payload, "bad").type, "∀ item. item → item");
  assert.equal(at(payload, source, 1, "bad").hover.type, "Int → Int");
  assert.equal(at(payload, source, 2, "bad").hover.type, "Bool → Bool");
  assert.equal(payload.programTy, "(Int, Bool)");
});

test("complete signatures cut a failed recursive SCC and permit native unsigned inference", () => {
  const source = "let f : Int -> Int = \\x -> if True then True else g x\nlet g x = f x\nlet good = g 7\nlet wrong = g False\ngood\n";
  const { payload } = cli(source);
  assert.deepEqual(payload.diagnostics.map(d => d.code), ["type.annotationMismatch", "type.argumentMismatch"]);
  assert.equal(definition(payload, "f").typeStatus, "declared");
  assert.equal(definition(payload, "g").type, "Int → Int");
  assert.equal(definition(payload, "g").typeStatus, "conditional");
  assert.deepEqual(definition(payload, "g").typeAssumptions.map(a => a.name), ["f"]);
});

test("unsigned residual recursion still checks as a native recursive component", () => {
  const source = "let f : Int -> Int = \\x -> if True then True else g x\n" +
    "let g x = if True then f x else h x\nlet h x = g x\nlet good = h 7\ngood\n";
  const { payload } = cli(source);
  assert.equal(payload.diagnostics.length, 1);
  for (const name of ["g", "h"]) {
    assert.equal(definition(payload, name).type, "Int → Int");
    assert.equal(definition(payload, name).typeStatus, "conditional");
  }
  assert.equal(definition(payload, "good").type, "Int");
});

test("partial recursive signatures require real successful implementation inference", () => {
  const source = "let f : Int -> Int = \\x -> if True then True else g x\nlet g : _ -> _ = \\x -> f x\nlet good = g 7\ngood\n";
  const { payload } = cli(source);
  assert.equal(payload.diagnostics.length, 1);
  assert.equal(definition(payload, "g").type, "Int → Int");
  assert.equal(definition(payload, "g").typeStatus, "conditional");
});

test("anonymous holes, named holes and missing head domains are not interfaces", () => {
  for (const binding of ["let bad : _ -> Int = \\x -> True", "let bad : ?a -> Int = \\x -> True", "let bad x : Int = True"]) {
    const source = binding + "\nlet use = bad False\nuse\n";
    const { payload } = cli(source);
    assert.equal(payload.diagnostics.length, 1);
    for (const name of ["bad", "use"]) {
      assert.match(definition(payload, name).type, /^type unknown/);
      assert.equal(definition(payload, name).typeStatus, undefined);
    }
    assert.equal(payload.programTy, "");
  }
});

test("complete typed heads use the canonical result-annotation normalisation", () => {
  const source = "let bad (x : Int) : Int = True\nlet good = bad 7\nlet wrong = bad False\ngood\n";
  const { payload } = cli(source);
  assert.deepEqual(payload.diagnostics.map(d => d.code), ["type.annotationMismatch", "type.argumentMismatch"]);
  assert.equal(definition(payload, "bad").type, "Int → Int");
  assert.equal(definition(payload, "bad").typeStatus, "declared");
});

test("invalid annotations and unavailable datatype dependencies never provide interfaces", () => {
  for (const binding of ["let bad : List = 1", "let bad : Absent = 1", "type Bad = MkBad _\nlet bad : Bad = MkBad 1"]) {
    const { payload } = cli(binding + "\nlet use = bad\n0\n");
    assert.equal(payload.diagnostics.length, 1);
    assert.match(definition(payload, "bad").type, /^type unknown/);
    assert.match(definition(payload, "use").type, /^type unknown/);
  }
});

test("malformed and duplicate parser headers stay quarantined despite complete annotations", () => {
  for (const source of [
    "let bad : Int = (\nlet bad : Int = 1\nlet use = bad\n0\n",
    "let bad : Int = 1\nlet bad : Int = 2\nlet use = bad\n0\n",
    "let bad : Int = 1 @\nlet use = bad\n0\n",
  ]) {
    const { payload } = cli(source);
    assert.equal(payload.diagnostics.length, 1);
    assert.ok(payload.symbols.filter(s => s.def && s.name === "bad").every(s => s.type.startsWith("type unknown")));
    assert.match(definition(payload, "use").type, /^type unknown/);
  }
});

test("healthy shadows and unrelated closed definitions have no assumed interface status", () => {
  const source = "let bad : Int = True\nlet good bad = bad\nlet value = good False\nlet untouched = 7\nvalue\n";
  const { payload } = cli(source);
  assert.equal(payload.diagnostics.length, 1);
  for (const name of ["good", "value", "untouched"]) assert.equal(definition(payload, name).typeStatus, undefined);
  assert.equal(at(payload, source, 1, "bad", 1).definition.startLine0, 1);
  assert.equal(payload.programTypeAssumptions, undefined);
});

test("local contracts expose argument errors and retain lexical definition targets", () => {
  const source = "let outer x = let bad : Int -> Int = \\y -> True in (bad x, bad False)\n0\n";
  const { payload } = cli(source);
  assert.deepEqual(payload.diagnostics.map(d => d.code), ["type.annotationMismatch", "type.argumentMismatch"]);
  assert.equal(definition(payload, "bad").typeStatus, "declared");
  assert.equal(at(payload, source, 0, "bad", 1).hover.type, "Int → Int");
  assert.equal(at(payload, source, 0, "bad", 1).definition.startCol0, source.indexOf("bad"));
  assert.equal(at(payload, source, 0, "x").hover.type, "Int");
});

test("local contracts open only real enclosing authored type variables", () => {
  const source = "let outer : {item} item -> item = \\x -> let bad : item -> item = \\y -> 1 True in bad x\n0\n";
  const { payload } = cli(source);
  assert.equal(payload.diagnostics.length, 1);
  assert.equal(definition(payload, "bad").type, "item → item");
  assert.equal(at(payload, source, 0, "bad", 1).hover.type, "item → item");
});

test("a complete contract does not license rigid-variable escape from its implementation", () => {
  const source = "let f x = let bad : {a} a -> a = \\y -> if True then x else y in (1 True, x + 1)\n0\n";
  const { payload } = cli(source);
  assert.deepEqual(payload.diagnostics.map(d => d.code), ["type.escapingVariable", "type.notFunction"]);
  assert.equal(definition(payload, "bad").typeStatus, "declared");
  assert.equal(at(payload, source, 0, "x").hover.type, "Int");
});

test("an unbound implementation retains its diagnostic while complete callers can check", () => {
  const source = "let bad : Int -> Int = absent\nlet good = bad 7\nlet wrong = bad False\ngood\n";
  const { payload } = cli(source);
  assert.deepEqual(payload.diagnostics.map(d => d.code), ["lower.unboundName", "type.argumentMismatch"]);
  assert.equal(definition(payload, "good").type, "Int");
});

test("interface showcase remains rejected and repair restores strict metadata and execution", () => {
  const source = readFileSync(new URL("../scratch/error-recovery-interfaces.fhm", import.meta.url), "utf8");
  const broken = cli(source);
  assert.equal(broken.status, 1);
  assert.equal(broken.payload.diagnostics.length, 3);
  assert.equal(cli(source, ["run", "--json"]).payload.ok, false);
  const fixed = source.replace("then True else", "then x else").replace("member False", "member 2").replace("\\x -> 1 True", "\\x -> x");
  const checked = cli(fixed);
  assert.equal(checked.status, 0);
  assert.equal(checked.payload.diagnostics.length, 0);
  assert.ok(checked.payload.symbols.every(s => s.typeStatus === undefined && s.typeAssumptions === undefined));
  assert.equal(checked.payload.programTypeAssumptions, undefined);
  assert.equal(cli(fixed, ["run", "--json"]).status, 0);
});

console.log(`${tests - failures}/${tests} declared-interface recovery checks passed.`);
process.exitCode = failures ? 1 : 0;
