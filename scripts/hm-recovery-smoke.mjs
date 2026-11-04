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

test("recovered local parameters retain lexical identity and actual contextual types", () => {
  const source = "let id x = x\nlet broken id = id 1 + True\nlet good = id 7\ngood\n";
  const { payload } = cli(["diagnose"], source);
  assert.equal(payload.diagnostics.length, 1);
  const local = at(payload, source, 1, "id", 1);
  assert.equal(local.hover.type, "Int → Int");
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

test("declaration showcase recovers independent errors and validated forward references", () => {
  const source = readFileSync(new URL("../scratch/error-recovery-declarations.fhm", import.meta.url), "utf8");
  const { payload, status } = cli(["diagnose"], source);
  assert.equal(status, 1);
  assert.deepEqual(payload.diagnostics.map(d => d.code), ["lower.holeNotAllowed", "lower.unknownType",
    "decl.duplicateType", "decl.duplicateConstructor", "type.notFunction"]);
  const lines = source.split("\n");
  const healthy = lines.findIndex(line => line.startsWith("let healthy"));
  assert.equal(at(payload, source, healthy, "healthy").hover.type, "Forward");
  assert.equal(payload.programTy, "Forward");
  const blocked = lines.findIndex(line => line.startsWith("let blocked ="));
  assert.equal(at(payload, source, blocked, "blocked").hover.type, "type unknown (error in type `Bad`)");
  assert.ok(!payload.symbols.some(symbol => symbol.type === "Int → Left" || symbol.type === "Bool → Right"));
  const runner = cli(["run", "--json"], source);
  assert.equal(runner.status, 1);
  assert.equal(runner.payload.ok, false);
});

test("unavailable type and constructor references preserve their separate namespaces", () => {
  const source = "type Bad = Bad _\nlet asType (x : Bad) = x\nlet asCtor = Bad 1\nlet healthy = 7\nhealthy\n";
  const { payload } = cli(["diagnose"], source);
  assert.equal(payload.diagnostics.length, 1);
  const type = at(payload, source, 1, "Bad");
  const ctor = at(payload, source, 2, "Bad");
  assert.equal(type.hover.kind, "type");
  assert.equal(ctor.hover.kind, "ctor");
  assert.deepEqual([type.definition.startLine0, type.definition.startCol0], [0, 5]);
  assert.deepEqual([ctor.definition.startLine0, ctor.definition.startCol0], [0, 11]);
  assert.equal(at(payload, source, 3, "healthy").hover.type, "Int");
});

test("fixing declaration failures restores strict typing and clears dependency statuses", () => {
  const source = "type Bad = MkBad _\nlet value = MkBad 1\nvalue\n";
  assert.equal(cli(["diagnose"], source).payload.diagnostics.length, 1);
  const fixed = source.replace("MkBad _", "MkBad Int");
  const { payload, status } = cli(["diagnose"], fixed);
  assert.equal(status, 0);
  assert.deepEqual(payload.diagnostics, []);
  assert.equal(at(payload, fixed, 1, "value").hover.type, "Bad");
  assert.ok(!payload.symbols.some(symbol => symbol.type.startsWith("type unknown")));
  assert.equal(cli(["run", "--json"], fixed).status, 0);
});

test("parser showcase retains later diagnostics, healthy hovers and documentation", () => {
  const source = readFileSync(new URL("../scratch/error-recovery-parser.fhm", import.meta.url), "utf8");
  const { payload, status } = cli(["diagnose"], source);
  assert.equal(status, 1);
  assert.equal(payload.diagnostics.length, 5);
  assert.deepEqual(payload.diagnostics.map(d => d.code), [undefined, undefined,
    "lower.holeNotAllowed", "lower.unboundName", "type.annotationMismatch"]);
  const lines = source.split("\n");
  const numberLine = lines.findIndex(line => line.startsWith("let number"));
  const truthLine = lines.findIndex(line => line.startsWith("let truth"));
  const number = at(payload, source, numberLine, "id");
  assert.equal(number.hover.type, "Int → Int");
  assert.equal(number.hover.doc, "Healthy documentation survives resynchronisation.");
  assert.equal(at(payload, source, truthLine, "id").hover.type, "Bool → Bool");
  assert.equal(payload.programTy, "(Int, Bool)");
  assert.ok(payload.tokens.length > 0, "Recovered source positions retain the original tokens");
  const runner = cli(["run", "--json"], source);
  assert.equal(runner.status, 1);
  assert.equal(runner.payload.stage, "parse");
});

test("parser resynchronisation ignores keyword text inside strings and comments", () => {
  for (const hidden of ['  "text\nlet ghost = 99\nend"\n', '  /-\nlet ghost = 99\n  -/\n']) {
    const source = "let broken = (\n" + hidden + "let good=7\ngood\n";
    const { payload } = cli(["diagnose"], source);
    assert.equal(payload.diagnostics.length, 1);
    assert.equal(payload.programTy, "Int");
    assert.ok(!payload.symbols.some(symbol => symbol.def && symbol.name === "ghost"));
  }
});

test("unparsed local names cannot borrow a healthy outer binder's hover or navigation", () => {
  const source = "let id x=x\nlet broken =\n  \\id ->\n    (id 1,\nlet good=id 7\ngood\n";
  const { payload } = cli(["diagnose"], source);
  assert.equal(payload.diagnostics.length, 1);
  const unparsed = at(payload, source, 3, "id");
  assert.match(unparsed.hover.type, /^type unknown \(syntax at /);
  assert.equal(unparsed.definition, undefined);
  const good = at(payload, source, 4, "id");
  assert.equal(good.hover.type, "Int → Int");
  assert.deepEqual([good.definition.startLine0, good.definition.startCol0], [0, 4]);
});

test("malformed datatype headers preserve separate type and constructor identity", () => {
  const source = "type Bad = Bad (\nlet asType (x : Bad) = x\nlet asCtor = Bad 1\nlet good=7\ngood\n";
  const { payload } = cli(["diagnose"], source);
  assert.equal(payload.diagnostics.length, 1);
  const type = at(payload, source, 1, "Bad"), ctor = at(payload, source, 2, "Bad");
  assert.deepEqual([type.definition.startLine0, type.definition.startCol0], [0, 5]);
  assert.deepEqual([ctor.definition.startLine0, ctor.definition.startCol0], [0, 11]);
  assert.equal(payload.programTy, "Int");
});

test("parser duplicates quarantine every definition and keep a precise original cause", () => {
  for (const prefix of ["let f=1\nlet f=True\n", "let f=(\nlet f=1\n"]) {
    const source = prefix + "let use=f\nlet healthy=7\nhealthy\n";
    const { payload } = cli(["diagnose"], source);
    assert.equal(payload.diagnostics.length, 1);
    assert.ok(payload.symbols.filter(symbol => symbol.def && symbol.name === "f").every(
      symbol => symbol.type.startsWith("type unknown")));
    assert.match(at(payload, source, 2, "use").hover.type, /^type unknown/);
    assert.equal(payload.programTy, "Int");
    if (prefix.includes("True")) {
      const [d] = payload.diagnostics;
      assert.deepEqual([d.line, d.col, d.endLine, d.endCol], [2, 5, 2, 6]);
    }
  }
});

test("a rejected final expression has no invented Unit type and repair restores execution", () => {
  const brokenBody = "let good=7\n(good,\n";
  const response = cli(["diagnose"], brokenBody);
  assert.equal(response.payload.diagnostics.length, 1);
  assert.equal(response.payload.programTy, "");
  assert.equal(at(response.payload, brokenBody, 0, "good").hover.type, "Int");
  const repaired = brokenBody.replace("(good,", "(good, True)");
  const fixed = cli(["diagnose"], repaired);
  assert.equal(fixed.status, 0);
  assert.equal(fixed.payload.programTy, "(Int, Bool)");
  assert.equal(cli(["run", "--json"], repaired).payload.result, "(7, True)");
});

test("lexical showcase preserves prefix/suffix code without accepting repaired bindings", () => {
  const source = readFileSync(new URL("../scratch/error-recovery-lexical.fhm", import.meta.url), "utf8");
  const { payload, status } = cli(["diagnose"], source);
  assert.equal(status, 1);
  assert.equal(payload.diagnostics.length, 5);
  assert.deepEqual(payload.diagnostics.map(d => d.message.includes("escape") ? "escape" : d.code || d.message),
    ["escape", "unexpected character '@'", "escape", "type.notFunction", "unfinished block comment"]);
  const lines = source.split("\n");
  const number = lines.findIndex(line => line.startsWith("let number"));
  const truth = lines.findIndex(line => line.startsWith("let truth"));
  const bad = lines.findIndex(line => line.startsWith("let wouldTypeAfterDeletion"));
  assert.equal(at(payload, source, number, "id").hover.type, "Int → Int");
  assert.equal(at(payload, source, truth, "id").hover.type, "Bool → Bool");
  assert.match(at(payload, source, bad, "wouldTypeAfterDeletion").hover.type, /^type unknown/);
  assert.ok(!payload.symbols.some(symbol => symbol.def && symbol.name === "thisIsCommentText"));
  assert.equal(payload.programTy, "(Int, Bool)");
  assert.equal(cli(["run", "--json"], source).payload.stage, "parse");
});

test("a later lexical gap stays quarantined even behind an earlier grammar failure", () => {
  const source = "let syntaxBroken=(\nlet lexicalBroken=1 @ + 2\nlet use=lexicalBroken\nlet healthy=7\nhealthy\n";
  const { payload } = cli(["diagnose"], source);
  assert.equal(payload.diagnostics.length, 2);
  assert.deepEqual(payload.diagnostics.map(d => d.line), [1, 2]);
  assert.match(at(payload, source, 2, "use").hover.type, /^type unknown/);
  assert.equal(at(payload, source, 3, "healthy").hover.type, "Int");
});

test("unfinished literals preserve the prefix and never promote keyword text into declarations", () => {
  const source = "let before=7\nlet broken=\"unterminated\nlet ghost=99\nbefore\n";
  const { payload } = cli(["diagnose"], source);
  assert.equal(payload.diagnostics.length, 1);
  assert.equal(at(payload, source, 0, "before").hover.type, "Int");
  assert.equal(payload.programTy, "");
  assert.ok(!payload.symbols.some(symbol => symbol.def && symbol.name === "ghost"));
  const text = at(payload, source, 3, "before");
  assert.equal(text.hover, undefined);
  assert.equal(text.definition, undefined);
});

test("malformed multiline strings and comments retain opaque editor token boundaries", () => {
  const source = "let id x=x\nlet broken=\"bad\\q\nlet ghost=id 99\nend\"\n" +
    "--\t id\nlet healthy=id 7\nhealthy\n";
  const { payload } = cli(["diagnose"], source);
  assert.equal(payload.diagnostics.length, 2);
  assert.equal(at(payload, source, 2, "id").hover, undefined, "literal text has no identifier hover");
  assert.equal(at(payload, source, 4, "id").hover, undefined, "comment text has no identifier hover");
  assert.equal(at(payload, source, 5, "id").hover.type, "Int → Int");
  assert.ok(!payload.symbols.some(symbol => symbol.def && symbol.name === "ghost"));
});

test("lexical error positions remain UTF-16 after a non-BMP character", () => {
  const source = "let broken = ('😀', \"bad\\q\")\nlet healthy=7\nhealthy\n";
  const { payload } = cli(["diagnose"], source);
  assert.equal(payload.diagnostics.length, 1);
  const [error] = payload.diagnostics;
  const col = source.split("\n")[0].indexOf("q") + 1;
  assert.deepEqual([error.line, error.col, error.endLine, error.endCol], [1, col, 1, col + 1]);
  assert.equal(payload.programTy, "Int");
});

test("multiple lexical causes on one binding remain visible without dependency cascades", () => {
  const source = "let bad=1 @ +2 #\nlet use=bad\nlet healthy=7\nhealthy\n";
  const { payload } = cli(["diagnose"], source);
  assert.equal(payload.diagnostics.length, 2);
  const use = at(payload, source, 1, "use").hover.type;
  assert.ok(use.includes("1:11") && use.includes("1:16"), "Both original lexical causes survive");
  assert.equal(at(payload, source, 2, "healthy").hover.type, "Int");
});

test("fixing lexical errors restores the original strict path and execution", () => {
  const source = "let bad=1 @ + 2\nlet result=bad + 1\nresult\n";
  assert.equal(cli(["diagnose"], source).status, 1);
  const fixed = source.replace(" @", "");
  const { payload, status } = cli(["diagnose"], fixed);
  assert.equal(status, 0);
  assert.deepEqual(payload.diagnostics, []);
  assert.equal(payload.programTy, "Int");
  assert.equal(cli(["run", "--json"], fixed).payload.result, "4");
});

console.log(`${tests - failures}/${tests} editor recovery checks passed.`);
process.exitCode = failures ? 1 : 0;
