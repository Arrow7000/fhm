#!/usr/bin/env node
// Build first: lake build fhm
// Run: node scripts/hm-editor-smoke.mjs
// Operational CLI/editor canaries, not metatheory proofs. No Z3 dependency.
import assert from "node:assert/strict";
import { spawnSync } from "node:child_process";
import { createRequire } from "node:module";
import { fileURLToPath } from "node:url";

const require = createRequire(import.meta.url);
const { normalizePayload, resolveHover, resolveDefinition } = require("../editors/shared/fhmEditorCore.cjs");
const binary = process.env.FHM || fileURLToPath(new URL("../.lake/build/bin/fhm", import.meta.url));
let failures = 0;
let tests = 0;

function cli(args, source) {
  const child = spawnSync(binary, args, {
    input: source, encoding: "utf8", timeout: 15_000, maxBuffer: 4 * 1024 * 1024,
  });
  assert.ifError(child.error);
  assert.equal(child.signal, null, `CLI terminated by ${child.signal}`);
  let payload;
  try { payload = JSON.parse(child.stdout); }
  catch { throw new Error(`Invalid CLI JSON (exit ${child.status}): ${child.stdout}\n${child.stderr}`); }
  return { status: child.status, payload };
}

function diagnose(source) {
  const result = cli(["diagnose"], source);
  assert.equal(result.status, 0, JSON.stringify(result.payload.diagnostics));
  assert.deepEqual(result.payload.diagnostics, [], "Unexpected editor diagnostics");
  return result.payload;
}

function hover(payload, source, line0, word, expected, occurrence = 0) {
  const line = source.split("\n")[line0];
  const matches = [...line.matchAll(new RegExp(`\\b${word}\\b`, "g"))];
  const column = matches[occurrence]?.index;
  assert.ok(column !== undefined, `Missing ${word} on line ${line0 + 1}`);
  const { ranged, tokens } = normalizePayload(payload);
  for (let offset = 0; offset < word.length; offset++) {
    const hit = resolveHover(ranged, line0, column + offset, line, tokens);
    assert.ok(hit, `Missing hover for ${word} at ${line0 + 1}:${column + offset + 1}`);
    assert.equal(hit.name, word);
    assert.equal(hit.type, expected);
    assert.deepEqual(
      [hit.startLine0, hit.startCol0, hit.endLine0, hit.endCol0],
      [line0, column, line0, column + word.length],
      "Hover range must use half-open UTF-16 editor coordinates",
    );
  }
}

function run(source, result, flags = []) {
  const response = cli(["run", "--json", ...flags], source);
  assert.equal(response.status, 0, JSON.stringify(response.payload));
  assert.equal(response.payload.ok, true);
  assert.equal(response.payload.result, result);
  return response.payload;
}

function test(name, action) {
  tests++;
  try { action(); console.log(`PASS ${name}`); }
  catch (error) { failures++; console.error(`FAIL ${name}: ${error.message}`); }
}

test("polymorphic id has independently instantiated Int/Bool use hovers", () => {
  const source = "let id = \\x -> x\nlet number = id 1\nlet truth = id True\n(number, truth)\n";
  const payload = diagnose(source);
  hover(payload, source, 1, "id", "Int → Int");
  hover(payload, source, 2, "id", "Bool → Bool");
  const response = run(source, "(1, True)");
  const id = response.bindings.find(binding => binding.name === "id");
  assert.match(id?.type || "", /^∀ .+\. .+ → .+$/, "Binding report must retain id's polymorphic scheme");
});

test("shadowed occurrences resolve to their own binder types", () => {
  const source = "let value = 1\nlet answer = let value = True in value\n(value, answer)\n";
  const payload = diagnose(source);
  hover(payload, source, 1, "value", "Bool", 1);
  hover(payload, source, 2, "value", "Int");
  hover(payload, source, 2, "answer", "Bool");
  run(source, "(1, True)");
});

test("dependency SCC reordering retains source occurrence types", () => {
  const source = "let answer = identity 7\nlet identity = \\x -> x\nanswer\n";
  const payload = diagnose(source);
  hover(payload, source, 0, "identity", "Int → Int");
  hover(payload, source, 2, "answer", "Int");
  run(source, "7");
});

test("mutual recursion retains both member occurrence types", () => {
  const source = "let f = \\n -> if n < 1 then 0 else g (n - 1)\nlet g = \\n -> if n < 1 then 0 else f (n - 1)\nf 3\n";
  const payload = diagnose(source);
  hover(payload, source, 0, "g", "Int → Int");
  hover(payload, source, 1, "f", "Int → Int");
  hover(payload, source, 2, "f", "Int → Int");
  run(source, "0");
});

test("editor reports ordinary List annotations directly", () => {
  const source = "let xs : List Int = [1, 2]\nxs\n";
  const payload = diagnose(source);
  hover(payload, source, 1, "xs", "List Int");
  assert.equal(payload.programTy, "List Int");
});

test("overpromised recursive annotation is rejected by editor and runner", () => {
  // Surface top-level bindings are recursive; `rec` is not a surface keyword.
  const source = "let f : {a} a = 1\nf\n";
  const editor = cli(["diagnose"], source);
  assert.equal(editor.status, 1);
  assert.ok(editor.payload.diagnostics.length > 0);
  const runner = cli(["run", "--json"], source);
  assert.equal(runner.status, 1);
  assert.equal(runner.payload.ok, false);
  assert.equal(runner.payload.stage, "typecheck");
});

test("non-BMP character before ASCII occurrence preserves UTF-16 range", () => {
  const source = "let value = 1\n('😀', value)\n";
  const payload = diagnose(source);
  hover(payload, source, 1, "value", "Int");
});

test("whitespace resolves whole application/list types, not identifier fallback", () => {
  const source = "let id = \\x -> x\nid 1\n";
  const { ranged, tokens } = normalizePayload(diagnose(source));
  const hit = resolveHover(ranged, 1, 2, "id 1", tokens);
  assert.equal(hit?.kind, "expr");
  assert.equal(hit?.type, "Int");
  assert.deepEqual([hit.startCol0, hit.endCol0], [0, 4]);
  const list = normalizePayload(diagnose("[1, 2]\n"));
  assert.equal(resolveHover(list.ranged, 0, 3, "[1, 2]", list.tokens)?.type, "List Int");
});

test("signature names survive RHS hovers and nested-let skolems", () => {
  const source = "let keep : {element} element -> element = \\x -> x\nkeep\n";
  const payload = diagnose(source);
  hover(payload, source, 0, "x", "element", 0);
  hover(payload, source, 0, "x", "element", 1);
  const response = run("let keep : {element} element -> element = \\x -> x\nkeep 1\n", "1");
  assert.equal(response.bindings.find(b => b.name === "keep")?.type, "∀ element. element → element");
  const nested = "let demo = let keep : {item} item -> item = \\x -> x in keep 1\ndemo\n";
  const scoped = diagnose(nested);
  hover(scoped, nested, 0, "x", "item", 0);
  hover(scoped, nested, 0, "x", "item", 1);
  for (const symbol of [...payload.symbols, ...scoped.symbols]) {
    assert.ok(!/\?[a-zA-Z]\w*/.test(symbol.type), symbol.type);
  }
});

test("annotated mutual SCC exports polymorphism but forbids polymorphic recursive calls", () => {
  const source = "let f : {item} item -> item = \\x -> if True then x else g x\nlet g = \\y -> f y\n(f 1, f True)\n";
  const payload = diagnose(source);
  hover(payload, source, 2, "f", "Int → Int", 0);
  hover(payload, source, 2, "f", "Bool → Bool", 1);
  run(source, "(1, True)");
  const bad = "let f : {item} item -> item = \\x -> if True then x else g x\nlet g = \\y -> (f y, f [y])\nf\n";
  const rejected = cli(["diagnose"], bad);
  assert.equal(rejected.status, 1);
  assert.ok(rejected.payload.diagnostics.length > 0);
});

test("type and constructor references with the same name resolve separately", () => {
  const source = "type Box a = Box a\ntype Wrap a = Wrap (Box a)\nlet unbox : {a} Box a -> a = \\b -> match b with | Box x -> x\nlet ignore = \\(_ : Box Int) -> 0\nunbox (Box 3)\n";
  const { ranged, tokens } = normalizePayload(diagnose(source));
  for (const [line0, kind, occurrence, defCol0] of [
    [0, "type", 0, 5], [0, "ctor", 1, 13],
    [1, "type", 0, 5], [2, "type", 0, 5],
    [2, "ctor", 1, 13], [3, "type", 0, 5], [4, "ctor", 0, 13],
  ]) {
    const line = source.split("\n")[line0];
    const col0 = [...line.matchAll(/\bBox\b/g)][occurrence].index;
    for (let offset = 0; offset < 3; offset++) {
      assert.equal(resolveHover(ranged, line0, col0 + offset, line, tokens)?.kind, kind);
      const target = resolveDefinition(ranged, line0, col0 + offset, line, tokens);
      assert.deepEqual([target?.startLine0, target?.startCol0], [0, defCol0]);
    }
  }
});

test("complete nested patterns check and run; nested gaps remain rejected", () => {
  const cases = [
    ["let f = \\p -> match p with | ((a, b), c) -> a\nf ((1, 2), 3)\n", "1"],
    ["let f = \\p -> match p with | (a, (b, c)) -> c\nf (1, (2, 3))\n", "3"],
    ["type Maybe a = Just a | Nothing\nlet g = \\m -> match m with | Nothing -> 0 | Just Nothing -> 0 | Just (Just x) -> x\ng (Just (Just 3))\n", "3"],
    ["let h = \\xs -> match xs with | [] -> 0 | [] :: _ -> 1 | (y :: _) :: _ -> y\nh [[5]]\n", "5"],
  ];
  for (const [source, result] of cases) {
    diagnose(source);
    run(source, result);
  }
  for (const source of [
    "type Maybe a = Just a | Nothing\nlet g = \\m -> match m with | Nothing -> 0 | Just (Just x) -> x\ng (Just Nothing)\n",
    "let h = \\xs -> match xs with | [] -> 0 | [] :: _ -> 1\nh [[5]]\n",
  ]) {
    for (const args of [["diagnose"], ["run", "--json"]]) {
      const response = cli(args, source);
      assert.equal(response.status, 1);
      assert.match(JSON.stringify(response.payload), /match not exhaustive/);
    }
  }
});

test("application errors expose stable codes and precise matching CLI/editor spans", () => {
  const cases = [
    ["let bad = \\n -> n + True\nbad 1\n", "type.argumentMismatch", "type mismatch: expected Int, got Bool", "True", 0],
    ["let f = \\n -> n + 1\nf True\n", "type.argumentMismatch", "type mismatch: expected Int, got Bool", "True", 1],
    ["let f : Int -> Int = \\n -> n + True\nf 1\n", "type.argumentMismatch", "type mismatch: expected Int, got Bool", "True", 0],
    ["let f = \\n -> let id = \\x -> x in id True + n\nf 1\n", "type.argumentMismatch", "type mismatch: expected Int, got Bool", "id True", 0],
    ["1 True\n", "type.notFunction", "cannot apply a value of type Int as a function", "1", 0],
    ["\\x -> x x\n", "type.infiniteType", "infinite type: a would have to equal a → b", "x x", 0],
  ];
  for (const [source, code, message, highlighted, line0] of cases) {
    const editor = cli(["diagnose"], source);
    const runner = cli(["run", "--json"], source);
    assert.equal(editor.status, 1);
    assert.equal(runner.status, 1);
    const [diag] = editor.payload.diagnostics;
    assert.equal(diag.code, code);
    assert.equal(diag.message, message);
    const col = source.split("\n")[line0].indexOf(highlighted) + 1;
    assert.deepEqual([diag.line, diag.col, diag.endLine, diag.endCol],
      [line0 + 1, col, line0 + 1, col + highlighted.length]);
    for (const key of ["code", "message", "line", "col", "endLine", "endCol"]) {
      assert.equal(runner.payload[key], diag[key], key);
    }
  }
});

test("run --json reports errors where diagnose does", () => {
  const sources = {
    typecheck: "let f = \\x -> x + 1\nf True\n",
    lower: "let f = \\x -> y\nf 1\n",
    exhaustiveness: "let f = \\xs ->\n  match xs with\n  | [] -> 0\nf [1]\n",
  };
  for (const [stage, source] of Object.entries(sources)) {
    const editor = cli(["diagnose"], source);
    assert.equal(editor.status, 1, `${stage}: diagnose reports an error`);
    const [first] = editor.payload.diagnostics;
    const runner = cli(["run", "--json"], source);
    assert.equal(runner.payload.stage, stage);
    assert.deepEqual(
      [runner.payload.message, runner.payload.line, runner.payload.col, runner.payload.endLine, runner.payload.endCol],
      [first.message, first.line, first.col, first.endLine, first.endCol],
      `${stage}: run and diagnose agree`,
    );
    assert.ok(runner.payload.line > 1 || runner.payload.col > 1, `${stage}: not the 1:1 default`);
  }
});

console.log(`${tests - failures}/${tests} HM CLI/editor semantic smoke checks passed.`);
process.exitCode = failures ? 1 : 0;
