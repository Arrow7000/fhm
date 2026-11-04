#!/usr/bin/env node
// Build first: lake build fhm
// Operational recovery and editor-resolution checks; no placeholder checker.
import assert from "node:assert/strict";
import { spawnSync } from "node:child_process";
import { readFileSync } from "node:fs";
import { createRequire } from "node:module";
import { fileURLToPath } from "node:url";

const { normalizePayload, resolveHover, resolveDefinition } = createRequire(import.meta.url)("../editors/shared/fhmEditorCore.cjs");
const binary = process.env.FHM || fileURLToPath(new URL("../.lake/build/bin/fhm", import.meta.url));
let tests = 0, failures = 0;
function cli(args, source) {
  const result = spawnSync(binary, args, { input: source, encoding: "utf8", timeout: 15000 });
  assert.ifError(result.error);
  assert.equal(result.signal, null);
  return { status: result.status, payload: JSON.parse(result.stdout) };
}
function test(name, action) {
  tests++;
  try { action(); console.log(`PASS ${name}`); }
  catch (error) { failures++; console.error(`FAIL ${name}: ${error.stack}`); }
}
function at(payload, source, line0, token, occurrence = 0) {
  const { ranged, tokens } = normalizePayload(payload);
  const line = source.split("\n")[line0];
  const col0 = [...line.matchAll(new RegExp(`\\b${token}\\b`, "g"))][occurrence]?.index;
  assert.notEqual(col0, undefined, `Missing ${token} on line ${line0 + 1}`);
  return { hover: resolveHover(ranged, line0, col0, line, tokens),
    definition: resolveDefinition(ranged, line0, col0, line, tokens) };
}

test("showcase reports five exact failures and keeps healthy polymorphic hovers", () => {
  const source = readFileSync(new URL("../scratch/error-recovery.fhm", import.meta.url), "utf8");
  const { status, payload } = cli(["diagnose"], source);
  assert.equal(status, 1);
  assert.deepEqual(payload.diagnostics.map(d => d.code), ["type.argumentMismatch", "type.annotationMismatch",
    "lower.unboundName", "lower.typeArity", "type.infiniteType"]);
  const lines = source.split("\n");
  const starts = ["let badArgument", "let badAnnotation", "let badName", "let badArity", "let badInfinite"];
  const tokens = ["True", "True", "noSuchValue", "List", "f f"];
  for (const [index, diagnostic] of payload.diagnostics.entries()) {
    const line0 = lines.findIndex(line => line.startsWith(starts[index]));
    const col0 = lines[line0].lastIndexOf(tokens[index]);
    assert.deepEqual([diagnostic.line, diagnostic.col, diagnostic.endLine, diagnostic.endCol],
      [line0 + 1, col0 + 1, line0 + 1, col0 + tokens[index].length + 1]);
  }
  const numberLine = lines.findIndex(line => line.startsWith("let number"));
  const truthLine = lines.findIndex(line => line.startsWith("let truth"));
  assert.equal(at(payload, source, numberLine, "id").hover.type, "Int → Int");
  assert.equal(at(payload, source, truthLine, "id").hover.type, "Bool → Bool");
  assert.equal(at(payload, source, numberLine, "id").definition.startLine0,
    lines.findIndex(line => line.startsWith("let id")));
  assert.equal(payload.programTy, "(Int, Bool)");
  for (const name of ["blocked", "alsoBlocked"]) {
    const line0 = lines.findIndex(line => line.startsWith(`let ${name} `));
    assert.equal(at(payload, source, line0, name).hover.type, "type unknown (error in `badArgument`)");
  }
  const runner = cli(["run", "--json"], source);
  assert.equal(runner.status, 1);
  assert.equal(runner.payload.ok, false);
  assert.ok(["lower", "typecheck"].includes(runner.payload.stage));
  assert.equal(runner.payload.result, undefined, "Recovered artifacts must never run");
});

test("failed local parameters shadow known outer definitions without borrowing their type", () => {
  const source = "let id x = x\nlet broken id = id 1 + True\nlet good = id 7\ngood\n";
  const { payload } = cli(["diagnose"], source);
  assert.equal(payload.diagnostics.length, 1);
  const local = at(payload, source, 1, "id", 1);
  assert.equal(local.hover.type, "type unknown (error in `broken`)");
  assert.deepEqual([local.definition.startLine0, local.definition.startCol0], [1, 11]);
  assert.equal(at(payload, source, 2, "id").hover.type, "Int → Int");
  assert.deepEqual([at(payload, source, 2, "id").definition.startLine0,
    at(payload, source, 2, "id").definition.startCol0], [0, 4]);
});

test("healthy recovered use hovers retain definition documentation", () => {
  const source = "--- Identity documentation.\nlet id x = x\nlet broken = absent\nlet result = id 1\nresult\n";
  const { payload } = cli(["diagnose"], source);
  const use = at(payload, source, 3, "id");
  assert.equal(use.hover.type, "Int → Int");
  assert.equal(use.hover.doc, "Identity documentation.");
  assert.equal(use.definition.startLine0, 1);
});

test("failed mutual group exports neither signed nor inferred members", () => {
  const source = "let f : Int -> Int = \\x -> if True then True else g x\n" +
    "let g x = f x\nlet blocked = g 1\nlet healthy = 9\nhealthy\n";
  const { payload } = cli(["diagnose"], source);
  assert.equal(payload.diagnostics.length, 1);
  for (const [line, name] of [[0, "f"], [1, "g"], [2, "blocked"]]) {
    assert.match(at(payload, source, line, name).hover.type, /^type unknown \(error in /);
  }
  assert.equal(at(payload, source, 3, "healthy").hover.type, "Int");
  assert.equal(payload.programTy, "Int");
});

test("final-expression failure remains independent and unavailable dependencies suppress cascades", () => {
  const independent = cli(["diagnose"], "let failed : Int = True\n1 True\n");
  assert.deepEqual(independent.payload.diagnostics.map(d => d.code), ["type.annotationMismatch", "type.notFunction"]);
  const source = "let failed : Int = True\nlet next = failed + 1\nnext + 1\n";
  const { payload } = cli(["diagnose"], source);
  assert.equal(payload.diagnostics.length, 1);
  assert.equal(payload.programTy, "");
  assert.equal(at(payload, source, 2, "next").hover.type, "type unknown (error in `failed`)");
});

test("recovered signatures, named holes and pattern projections preserve checked types", () => {
  const source = "let failed = absent\nlet id : {item} ?a -> ?a = \\(x : item) -> x\n" +
    "let (number, truth) = (id 1, id True)\n(number, truth)\n";
  const { payload } = cli(["diagnose"], source);
  assert.equal(payload.diagnostics.length, 1);
  assert.deepEqual(payload.symbols.filter(s => s.kind === "typeHole").map(s => s.type), ["item", "item"]);
  assert.equal(at(payload, source, 2, "id", 0).hover.type, "Int → Int");
  assert.equal(at(payload, source, 2, "id", 1).hover.type, "Bool → Bool");
  assert.equal(at(payload, source, 3, "number").hover.type, "Int");
  assert.equal(at(payload, source, 3, "truth").hover.type, "Bool");
  assert.deepEqual([at(payload, source, 3, "number").definition.startLine0,
    at(payload, source, 3, "number").definition.startCol0], [2, 5]);
});

test("healthy programs use identical strict artifacts after fixing a rejected group", () => {
  const source = "let id x = x\nlet bad : Int = True\nlet good = id 7\ngood\n";
  assert.equal(cli(["diagnose"], source).status, 1);
  const fixed = source.replace("Int = True", "Int = 1");
  const diagnosed = cli(["diagnose"], fixed);
  assert.equal(diagnosed.status, 0);
  assert.deepEqual(diagnosed.payload.diagnostics, []);
  assert.ok(!diagnosed.payload.symbols.some(symbol => symbol.type.startsWith("type unknown")));
  assert.equal(at(diagnosed.payload, fixed, 2, "id").hover.type, "Int → Int");
  const runner = cli(["run", "--json"], fixed);
  assert.equal(runner.status, 0);
  assert.equal(runner.payload.result, "7");
});

console.log(`${tests - failures}/${tests} editor recovery checks passed.`);
process.exitCode = failures ? 1 : 0;
