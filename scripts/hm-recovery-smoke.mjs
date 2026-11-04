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

test("a complete signature cuts failed recursion and permits conditional unsigned exports", () => {
  const source = "let f : Int -> Int = \\x -> if True then True else g x\n" +
    "let g x = f x\nlet blocked = g 1\nlet healthy = 9\nhealthy\n";
  const { payload } = cli(["diagnose"], source);
  assert.equal(payload.diagnostics.length, 1);
  assert.equal(at(payload, source, 0, "f").hover.type, "Int → Int");
  assert.equal(at(payload, source, 1, "g").hover.type, "Int → Int");
  assert.equal(at(payload, source, 2, "blocked").hover.type, "Int");
  assert.equal(at(payload, source, 3, "healthy").hover.type, "Int");
  assert.equal(payload.programTy, "Int");
});

test("final-expression failure remains independent and unavailable dependencies suppress cascades", () => {
  const independent = cli(["diagnose"], "let failed : Int = True\n1 True\n");
  assert.deepEqual(independent.payload.diagnostics.map(d => d.code), ["type.annotationMismatch", "type.notFunction"]);
  const source = "let failed : List _ = True\nlet next = failed + 1\nnext + 1\n";
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

test("nested showcase reports seven errors with healthy local and polymorphic navigation", () => {
  const source = readFileSync(new URL("../scratch/error-recovery-nested.fhm", import.meta.url), "utf8");
  const { payload, status } = cli(["diagnose"], source);
  assert.equal(status, 1);
  assert.deepEqual(payload.diagnostics.map(d => d.code), ["type.notFunction", "type.notFunction",
    "type.notFunction", "type.notFunction", "type.annotationMismatch", "type.annotationMismatch", "type.notFunction"]);
  const lines = source.split("\n");
  const local = lines.findIndex(line => line.startsWith("  (2 False"));
  const healthy = at(payload, source, local, "healthy");
  assert.equal(healthy.hover.type, "Int");
  assert.equal(healthy.definition.startLine0, lines.findIndex(line => line.startsWith("  let healthy")));
  const arm = lines.findIndex(line => line.includes("head :: tail"));
  assert.equal(at(payload, source, arm, "head", 1).hover.type, "Int");
  assert.equal(at(payload, source, arm, "tail").hover.type, "List Int");
  assert.equal(at(payload, source, arm, "head", 1).definition.startCol0, lines[arm].indexOf("head"));
  const forall = lines.findIndex(line => line.includes("if True then x else x"));
  assert.equal(at(payload, source, forall, "x").hover.type, "item");
  assert.equal(at(payload, source, lines.length - 2, "after", 0).hover.type, "Int → Int");
  assert.equal(at(payload, source, lines.length - 2, "after", 1).hover.type, "Bool → Bool");
  assert.match(at(payload, source, lines.length - 2, "after").hover.doc, /Healthy polymorphism/);
  assert.equal(payload.programTy, "(Int, Bool)");
  for (const name of ["nested", "arms"]) {
    const line = lines.findIndex(line => line.startsWith(`let ${name} `));
    assert.match(at(payload, source, line, name).hover.type, /^type unknown/);
  }
  for (const name of ["left", "right", "preserve"]) {
    const line = lines.findIndex(line => line.startsWith(`let ${name} `));
    assert.equal(at(payload, source, line, name).hover.typeStatus, "declared");
  }
  assert.equal(cli(["run", "--json"], source).payload.ok, false);
});

test("healthy local RHS uses keep contextual types and their exact parameter target", () => {
  const source = "let f x = let bad = 1 True in let good = x + 1 in (2 False, (good, bad))\n0\n";
  const { payload } = cli(["diagnose"], source);
  assert.equal(payload.diagnostics.length, 2);
  const use = at(payload, source, 0, "x", 1);
  assert.equal(use.hover.type, "Int");
  assert.deepEqual([use.definition.startLine0, use.definition.startCol0], [0, 6]);
  assert.equal(at(payload, source, 0, "good", 1).hover.type, "Int");
  assert.equal(at(payload, source, 0, "bad", 1).hover.type, "type unknown (error in `bad`)");
  assert.equal(at(payload, source, 0, "bad", 1).definition.startCol0, source.indexOf("bad"));
});

test("multiple head parameters keep distinct types and navigation inside a failed function", () => {
  const source = "let f x y = (1 True, (x + 1, if y then 2 False else 0))\n0\n";
  const { payload } = cli(["diagnose"], source);
  assert.equal(payload.diagnostics.length, 2);
  for (const [name, type, column] of [["x", "Int", 6], ["y", "Bool", 8]]) {
    assert.equal(at(payload, source, 0, name).hover.type, type);
    assert.equal(at(payload, source, 0, name, 1).hover.type, type);
    assert.equal(at(payload, source, 0, name, 1).definition.startCol0, column);
  }
  assert.ok(!payload.symbols.some(s => s.name === "x" && s.type === "type variable (scheme binder)"));
});

test("shared outer monotypes are constrained across successfully checked siblings", () => {
  const source = "let f x = (1 True, (x + 1, if x then 0 else 1))\n0\n";
  const { payload } = cli(["diagnose"], source);
  assert.deepEqual(payload.diagnostics.map(d => d.code), ["type.notFunction", "type.mismatch"]);
  assert.equal(payload.diagnostics[1].col, source.indexOf("x then") + 1);
  assert.equal(at(payload, source, 0, "x").hover.type, "Int");
  assert.match(at(payload, source, 0, "f").hover.type, /^type unknown/);
});

test("successful local bindings generalise without generalising captured parameters", () => {
  const source = "let f x = let bad = 1 True in let id y = y in (id 1, (id False, x))\n0\n";
  const { payload } = cli(["diagnose"], source);
  assert.equal(payload.diagnostics.length, 1);
  assert.equal(at(payload, source, 0, "id").hover.type, "∀ a. a → a");
  assert.equal(at(payload, source, 0, "id", 1).hover.type, "Int → Int");
  assert.equal(at(payload, source, 0, "id", 2).hover.type, "Bool → Bool");
  const captured = "let f x = let bad = 1 True in let y = x in (y + 1, if y then 0 else 1)\n0\n";
  const second = cli(["diagnose"], captured).payload;
  assert.equal(second.diagnostics.length, 2);
  assert.equal(at(second, captured, 0, "y").hover.type, "Int");
});

test("a healthy local binder shadows an unavailable outer definition", () => {
  const source = "let bad : Int = True\nlet f = let bad x = x in (1 True, bad 7)\n0\n";
  const { payload } = cli(["diagnose"], source);
  assert.equal(payload.diagnostics.length, 2);
  const use = at(payload, source, 1, "bad", 1);
  assert.equal(use.hover.type, "Int → Int");
  assert.deepEqual([use.definition.startLine0, use.definition.startCol0], [1, source.split("\n")[1].indexOf("bad")]);
});

test("pattern lambdas retain independently constrained captures", () => {
  const source = "let f = \\(x, y) -> (1 True, (x + 1, if y then 2 False else 0))\n0\n";
  const { payload } = cli(["diagnose"], source);
  assert.equal(payload.diagnostics.length, 2);
  assert.equal(at(payload, source, 0, "x").hover.type, "Int");
  assert.equal(at(payload, source, 0, "y").hover.type, "Bool");
  for (const name of ["x", "y"]) {
    assert.equal(at(payload, source, 0, name, 1).definition.startCol0, source.indexOf(name));
  }
});

test("unavailable match scrutinees withhold capture types while independent arms recover", () => {
  const source = "let failed : List _ = True\nlet f = match failed with | x :: xs -> (1 True, x) | [] -> 2 False\n0\n";
  const { payload } = cli(["diagnose"], source);
  assert.deepEqual(payload.diagnostics.map(d => d.code), ["type.annotationMismatch", "type.notFunction", "type.notFunction"]);
  for (const name of ["x", "xs"]) assert.equal(at(payload, source, 1, name).hover.type, "type unknown (error in `failed`)");
  assert.equal(at(payload, source, 1, "x", 1).definition.startCol0, source.split("\n")[1].indexOf("x ::"));
});

test("known list elements still disagree across an unavailable element", () => {
  const source = "let failed : List _ = True\nlet f = [1, failed, False, 2 True]\n0\n";
  const { payload } = cli(["diagnose"], source);
  assert.deepEqual(payload.diagnostics.map(d => d.code), ["type.annotationMismatch", "type.mismatch", "type.notFunction"]);
  assert.equal(payload.diagnostics[1].col, source.split("\n")[1].indexOf("False") + 1);
  assert.match(at(payload, source, 1, "f").hover.type, /^type unknown/);
});

test("a bad local annotation stays independent of an unavailable RHS", () => {
  const source = "let failed : Int = True\nlet f = let x : Absent = failed in (1 True, x)\n0\n";
  const { payload } = cli(["diagnose"], source);
  assert.deepEqual(payload.diagnostics.map(d => d.code), ["type.annotationMismatch", "lower.unknownType", "type.notFunction"]);
});

test("failed local forall checks cannot leak rigid variables to the outer continuation", () => {
  const source = "let f x = let bad : {a} a -> a = \\y -> if True then x else y in (1 True, x + 1)\n0\n";
  const { payload } = cli(["diagnose"], source);
  assert.deepEqual(payload.diagnostics.map(d => d.code), ["type.escapingVariable", "type.notFunction"]);
  assert.equal(at(payload, source, 0, "x").hover.type, "Int");
  assert.equal(at(payload, source, 0, "x", 2).hover.type, "Int");
  assert.equal(at(payload, source, 0, "bad").hover.typeStatus, "declared");
});

test("local mutually recursive failures retain complete declared interfaces", () => {
  const source = "let outer x =\n  let f : Int -> Int = \\n -> if True then True else g n\n" +
    "      g : Int -> Int = \\n -> if True then False else f 1\n  in (1 True, x + 1)\n0\n";
  const { payload } = cli(["diagnose"], source);
  assert.deepEqual(payload.diagnostics.map(d => d.code), ["type.annotationMismatch", "type.annotationMismatch", "type.notFunction"]);
  for (const [line, name] of [[1, "f"], [2, "g"]]) assert.equal(at(payload, source, line, name).hover.typeStatus, "declared");
  assert.equal(at(payload, source, 1, "n").hover.type, "Int");
  assert.equal(at(payload, source, 2, "n").hover.type, "Int");
  assert.equal(at(payload, source, 3, "x").hover.type, "Int");
});

test("a native monomorphic-recursion failure survives unrelated fragment errors", () => {
  const source = "let f x = (f True + f 1, 1 True)\n0\n";
  const { payload } = cli(["diagnose"], source);
  assert.deepEqual(payload.diagnostics.map(d => d.code), ["type.argumentMismatch", "type.notFunction"]);
  assert.match(at(payload, source, 0, "f").hover.type, /^type unknown/);
});

test("final-expression recovery reports concrete non-functions with unavailable arguments", () => {
  const source = "let failed : List _ = True\n(1 failed, (2 False, 3 True))\n";
  const { payload } = cli(["diagnose"], source);
  assert.deepEqual(payload.diagnostics.map(d => d.code), ["type.annotationMismatch", "type.notFunction", "type.notFunction", "type.notFunction"]);
  assert.equal(payload.programTy, "");
});

test("fixing nested showcase errors restores strict artifacts and execution", () => {
  const broken = readFileSync(new URL("../scratch/error-recovery-nested.fhm", import.meta.url), "utf8");
  const fixed = broken.replaceAll(/\b[1-5] (?:True|False)\b/g, "1").replaceAll("then True else", "then 1 else").replaceAll("then False else", "then 1 else").replace("| [] -> 1\n", "| [] -> (1, 1)\n");
  const { payload, status } = cli(["diagnose"], fixed);
  assert.equal(status, 0);
  assert.deepEqual(payload.diagnostics, []);
  assert.ok(!payload.symbols.some(s => s.type.startsWith("type unknown")));
  assert.equal(payload.programTy, "(Int, Bool)");
  assert.equal(cli(["run", "--json"], fixed).payload.result, "(7, True)");
});

test("safe captured constraints survive a rejected local forall", () => {
  const source = "let f x = let bad : {a} a -> a = \\y -> let ok = x + 1 in let fail = 1 True in y in if x then 0 else 1\n0\n";
  const { payload } = cli(["diagnose"], source);
  assert.deepEqual(payload.diagnostics.map(d => d.code), ["type.notFunction", "type.mismatch"]);
  assert.equal(at(payload, source, 0, "x").hover.type, "Int");
  assert.equal(at(payload, source, 0, "bad").hover.typeStatus, "declared");
});

test("authored type parameters stay scoped and navigable in failed head-parameter bindings", () => {
  const source = "let f {item} (x : item) y = (1 True, (x, if y then 2 False else 0))\n0\n";
  const { payload } = cli(["diagnose"], source);
  assert.equal(payload.diagnostics.length, 2);
  assert.equal(at(payload, source, 0, "x").hover.type, "item");
  assert.equal(at(payload, source, 0, "y").hover.type, "Bool");
  assert.equal(at(payload, source, 0, "item", 1).definition.startCol0, source.indexOf("item"));
});

test("shadowing restores outer aliases with constraints learned inside the inner scope", () => {
  const source = "let f x = let alias = x in (1 True, ((\\x -> (2 False, (x + 1, if alias then 0 else 1))) 0, x))\n0\n";
  const { payload } = cli(["diagnose"], source);
  assert.deepEqual(payload.diagnostics.map(d => d.code), ["type.notFunction", "type.notFunction"]);
  for (const occurrence of [0, 1, 4]) assert.equal(at(payload, source, 0, "x", occurrence).hover.type, "Bool");
  for (const occurrence of [2, 3]) assert.equal(at(payload, source, 0, "x", occurrence).hover.type, "Int");
  assert.equal(at(payload, source, 0, "x", 3).definition.startCol0, source.indexOf("\\x") + 1);
  assert.equal(at(payload, source, 0, "x", 4).definition.startCol0, source.indexOf("x"));
});

test("identical concrete mismatches in different conditionals remain separate diagnostics", () => {
  const source = "let rejected : Int = True\nlet f = (if 1 then 0 else 1, if 2 then 0 else 1)\n0\n";
  const { payload } = cli(["diagnose"], source);
  assert.deepEqual(payload.diagnostics.map(d => d.code), ["type.annotationMismatch", "type.mismatch", "type.mismatch"]);
  const line = source.split("\n")[1];
  assert.deepEqual(payload.diagnostics.slice(1).map(d => [d.col, d.endCol]),
    [line.indexOf("1 then"), line.indexOf("2 then")].map(col => [col + 1, col + 2]));
});

console.log(`${tests - failures}/${tests} editor recovery checks passed.`);
process.exitCode = failures ? 1 : 0;
