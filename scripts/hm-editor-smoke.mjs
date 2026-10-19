#!/usr/bin/env node
// Build first: lake build fhm
// Run: node scripts/hm-editor-smoke.mjs
// Operational CLI/editor canaries, not metatheory proofs. No Z3 dependency.
import assert from "node:assert/strict";
import { spawnSync } from "node:child_process";
import { createRequire } from "node:module";
import { fileURLToPath } from "node:url";

const require = createRequire(import.meta.url);
const { normalizePayload, resolveHover, resolveDefinition, hoverMarkdown } = require("../editors/shared/fhmEditorCore.cjs");
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

test("constructor hovers keep instantiated signatures and docs beside their declaration", () => {
  const source = "type Maybe element =\n  --- Wraps a value.\n  | Just element\n  | Nothing\nlet unwrap = \\m -> match m with | Just x -> x | Nothing -> 0\nunwrap (Just 3)\n";
  const { ranged, tokens } = normalizePayload(diagnose(source));
  const declaration = "type Maybe element =\n  | Just element\n  | Nothing";
  for (const line0 of [2, 4, 5]) {
    const line = source.split("\n")[line0];
    const col0 = line.indexOf("Just");
    const hit = resolveHover(ranged, line0, col0, line, tokens);
    assert.equal(hit?.kind, "ctor");
    assert.equal(hit.declaration, declaration);
    assert.equal(hit.doc, "Wraps a value.");
    const markdown = hoverMarkdown(hit);
    assert.ok(markdown.startsWith(`\`\`\`fhm\nJust : ${hit.type}\n\`\`\``));
    assert.ok(markdown.includes(declaration));
    assert.equal(markdown.split("Wraps a value.").length, 2, "constructor docs appear once");
    const target = resolveDefinition(ranged, line0, col0, line, tokens);
    assert.deepEqual([target?.startLine0, target?.startCol0], [2, 4]);
    if (line0 === 5) assert.equal(hit.type, "Int → Maybe Int");
  }
  const prelude = normalizePayload(diagnose("Cons 1 Nil\n"));
  const cons = resolveHover(prelude.ranged, 0, 0, "Cons 1 Nil", prelude.tokens);
  assert.match(cons.declaration, /^type List a =/);
  assert.match(cons.declaration, /Cons a \(List a\)/);
  assert.equal(cons.type, "Int → List Int → List Int");
  assert.equal(resolveDefinition(prelude.ranged, 0, 0, "Cons 1 Nil", prelude.tokens), undefined);
  const plain = normalizePayload(diagnose("let x = 1\nx\n"));
  const x = resolveHover(plain.ranged, 1, 0, "x", plain.tokens);
  assert.equal(x.declaration, undefined);
  assert.equal(hoverMarkdown(x), "```fhm\nx : Int\n```");
});

test("missing cases are actionable nested patterns, shared by CLI and editor", () => {
  const cases = [
    ["type Maybe a = Just a | Nothing\n",
      "let f = \\m -> match m with | Nothing -> 0 | Just (Just x) -> x",
      "f (Just Nothing)", ["Just Nothing"], "9"],
    ["", "let f = \\xs -> match xs with | [] -> 0 | [] :: _ -> 1",
      "f [[1]]", ["(_ :: _) :: _"], "9"],
    ["", "let f = \\p -> match p with | (True, True) -> 1 | (False, False) -> 0",
      "(f (True, False), f (False, True))", ["(True, False)", "(False, True)"], "(9, 9)"],
    ["type Color = Red | Green | Blue\n", "let f = \\c -> match c with | Red -> 0",
      "(f Green, f Blue)", ["Green", "Blue"], "(9, 9)"],
  ];
  for (const [prefix, definition, body, expected, result] of cases) {
    const source = `${prefix}${definition}\n${body}\n`;
    const editor = cli(["diagnose"], source);
    const runner = cli(["run", "--json"], source);
    assert.equal(editor.status, 1);
    assert.equal(runner.status, 1);
    const [diag] = editor.payload.diagnostics;
    assert.equal(diag.code, "match.notExhaustive");
    assert.deepEqual(diag.missingPatterns, expected);
    assert.equal(diag.moreMissing, false);
    for (const key of ["code", "message", "line", "col", "endLine", "endCol", "missingPatterns", "moreMissing"]) {
      assert.deepEqual(runner.payload[key], diag[key], key);
    }
    // The suggested patterns must parse, fill the holes and catch the input
    // that was previously uncovered, rather than merely matching a snapshot.
    const arms = expected.map(pattern => ` | ${pattern} -> 9`).join("");
    const repaired = `${prefix}${definition}${arms}\n${body}\n`;
    diagnose(repaired);
    run(repaired, result);
  }
  diagnose("type Maybe a = Just a | Nothing\nlet f = \\m -> match m with | Just (Just x) -> x | _ -> 0\nf (Just Nothing)\n");
});

test("missing-case examples are capped and say when more remain", () => {
  const prefix = "type Color = A | B | C | D | E | F | G\n";
  const definition = "let f = \\c -> match c with | A -> 0";
  const { payload, status } = cli(["diagnose"], `${prefix}${definition}\nf G\n`);
  assert.equal(status, 1);
  const [diag] = payload.diagnostics;
  assert.deepEqual(diag.missingPatterns, ["B", "C", "D", "E"]);
  assert.equal(diag.moreMissing, true);
  assert.match(diag.message, /and more/);
  const partialFix = definition + diag.missingPatterns.map(p => ` | ${p} -> 9`).join("");
  const next = cli(["diagnose"], `${prefix}${partialFix}\nf G\n`);
  assert.deepEqual(next.payload.diagnostics[0].missingPatterns, ["F", "G"]);
  run(`${prefix}${partialFix} | F -> 9 | G -> 9\nf G\n`, "9");
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

test("pattern lambdas retain capture order, closures, shadowing and multiple parameters", () => {
  const source = "let outer = 10\nlet select = \\(((a, b), (c, d)) : ((Int, Bool), (Bool, Int))) x _ -> ((a + outer) + x, (b, (c, d)))\nselect ((1, True), (False, 4)) 2 0\n";
  const payload = diagnose(source);
  hover(payload, source, 1, "a", "Int");
  hover(payload, source, 1, "b", "Bool");
  hover(payload, source, 1, "c", "Bool");
  hover(payload, source, 1, "d", "Int");
  hover(payload, source, 1, "a", "Int", 1);
  const { ranged, tokens } = normalizePayload(payload);
  const line = source.split("\n")[1];
  const def = resolveDefinition(ranged, 1, line.lastIndexOf("a +"), line, tokens);
  assert.deepEqual([def?.startLine0, def?.startCol0], [1, line.indexOf("a,")],
    "Capture use resolves to its pattern binder");
  run(source, "(13, (True, (False, 4)))");
  run("let f = \\x -> \\(x, y) -> x\nf False (3, True)\n", "3");
  run("let f = \\(a, _) (_, b) -> (a, b)\nf (3, False) (0, True)\n", "(3, True)");
});

test("single-constructor and annotated pattern lambdas infer polymorphic functions", () => {
  run("type Box a = Box a\nlet unbox = \\(Box x) -> x\n(unbox (Box 3), unbox (Box True))\n", "(3, True)");
  run("let fst : {a} (a, Bool) -> a = \\((x, _) : (a, Bool)) -> x\n(fst (3, False), fst (True, True))\n", "(3, True)");
  run("let swap = \\((a, b) : (Int, Bool)) -> (b, a)\nswap (3, True)\n", "(True, 3)");
  run("let sum = \\(n, total) -> if n < 1 then total else sum (n - 1, total + n)\nsum (5, 0)\n", "15");
});

test("refutable lambda parameters reuse missing-case diagnostics and preserve hovers", () => {
  const cases = [
    ["type Maybe a = Just a | Nothing\nlet get = \\(Just x) -> x\nget (Just 3)\n", "Nothing"],
    ["let head = \\(x :: _) -> x\nhead [3]\n", "[]"],
    ["let empty = \\[] -> 0\nempty []\n", "_ :: _"],
    ["let choose = \\(True, x) -> x\nchoose (True, 3)\n", "(False, _)"],
  ];
  for (const [source, missing] of cases) {
    const editor = cli(["diagnose"], source);
    const d = editor.payload.diagnostics[0];
    assert.equal(d?.code, "match.notExhaustive");
    assert.ok(d.missingPatterns.includes(missing), JSON.stringify(d));
    assert.ok(editor.payload.symbols.length > 0, "Rejected parameter keeps inferred hovers");
    const runner = cli(["run", "--json"], source);
    assert.notEqual(runner.status, 0);
    assert.equal(runner.payload.code, d.code);
    assert.deepEqual(runner.payload.missingPatterns, d.missingPatterns);
  }
});

test("top-level pattern lets generalise each name and preserve binder/use hovers", () => {
  const source = "let (identity, number) = (\\x -> x, 7)\nlet integer = identity number\nlet truth = identity True\n(integer, truth)\n";
  const payload = diagnose(source);
  hover(payload, source, 0, "number", "Int");
  hover(payload, source, 1, "identity", "Int → Int");
  hover(payload, source, 2, "identity", "Bool → Bool");
  const { ranged, tokens } = normalizePayload(payload);
  const line = source.split("\n")[2];
  const def = resolveDefinition(ranged, 2, line.indexOf("identity"), line, tokens);
  assert.deepEqual([def?.startLine0, def?.startCol0], [0, 5]);
  assert.ok(!payload.symbols.some(s => s.name.startsWith("$pattern/")));
  const response = run(source, "(7, True)");
  assert.deepEqual(response.bindings.map(b => b.name).sort(), ["identity", "integer", "number", "truth"]);
  assert.match(response.bindings.find(b => b.name === "identity")?.type || "", /^∀ /);
});

test("local pattern lets generalise independently while retaining outer type constraints", () => {
  run("let answer = let (f, n) = (\\x -> x, 3) in (f n, f True)\nanswer\n", "(3, True)");
  run("let make = \\captured -> let (f, n) = (\\x -> captured, 0) in (f True, f n)\nmake 7\n", "(7, 7)");
  run("let x = False\nlet answer = let (x, y) = (3, True) in (x, y)\n(x, answer)\n", "(False, (3, True))");
  run("let answer = let (x, y) = (1, 2)\n                 x = True\n             in (x, y)\nanswer\n", "(True, 2)");
  const bad = cli(["run", "--json"], "let bad = \\f -> let (g, n) = (f, 0) in (g 1, g True)\nbad (\\x -> x)\n");
  assert.notEqual(bad.status, 0, "A projection cannot generalise an outer lambda's type variables");
  assert.equal(bad.payload.stage, "typecheck");
});

test("nested, constructor, annotated and forward-referenced pattern lets work", () => {
  run("type Box a = Box a\nlet Box ((a, b), c) = Box ((3, True), 4)\n(a, (b, c))\n", "(3, (True, 4))");
  run("let (a, b) : (Int, Bool) = (3, True)\n(b, a)\n", "(True, 3)");
  run("let (identity, n) : {a} (a -> a, Int) = (\\(x : a) -> x, 7)\n(identity n, identity True)\n", "(7, True)");
  run("let answer = f True\nlet (f, n) = (\\x -> x, 7)\n(answer, n)\n", "(True, 7)");
  run("let answer = let result = f True\n                 (f, n) = (\\x -> x, 7)\n             in (result, n)\nanswer\n", "(True, 7)");
});

test("unused/refutable pattern lets are still checked and explain missing cases", () => {
  const sources = [
    ["type Maybe a = Just a | Nothing\nlet Just x = Just 3\nx\n", "Nothing"],
    ["let (True, _) = (True, 3)\n0\n", "(False, _)"],
    ["let [] = []\n0\n", "_ :: _"],
    ["let (head :: tail) = [3]\nhead\n", "[]"],
  ];
  for (const [source, missing] of sources) {
    const editor = cli(["diagnose"], source);
    const diagnostic = editor.payload.diagnostics[0];
    assert.equal(diagnostic?.code, "match.notExhaustive");
    assert.ok(diagnostic.missingPatterns.includes(missing), JSON.stringify(diagnostic));
    const runner = cli(["run", "--json"], source);
    assert.notEqual(runner.status, 0);
    assert.deepEqual(runner.payload.missingPatterns, diagnostic.missingPatterns);
  }
  run("let _ = (3, True)\n0\n", "0");
  const mismatch = cli(["run", "--json"], "let (_, _) = 3\n0\n");
  assert.notEqual(mismatch.status, 0, "A capture-free pattern must still constrain the RHS type");
  assert.equal(mismatch.payload.stage, "typecheck");
  assert.ok(!mismatch.payload.message.includes("$pattern/"));
});

test("call-by-name pattern lets skip undemanded RHSs and respect fuel when demanded", () => {
  const loop = "let loop = \\n -> loop (n + 1)\n";
  run(loop + "let _ = loop 0\n42\n", "42", ["--fuel", "200"]);
  run(loop + "let (x, y) = loop 0\n42\n", "42", ["--fuel", "200"]);
  run(loop + "let (x, y) = loop 0\nif True then 42 else x\n", "42", ["--fuel", "200"]);
  const demanded = cli(["run", "--json", "--fuel", "200"],
    loop + "let (x, y) = loop 0\nx\n");
  assert.equal(demanded.payload.stage, "eval");
  assert.equal(demanded.payload.steps, 200);
});

test("deep evaluation returns located resource errors with and without fuel", () => {
  const sum = "let sum = \\n -> if n < 1 then 0 else n + sum (n - 1)\n\nsum 100000\n";
  const growing = "let x = x + 1\n\nx\n";
  const local = "\n(let x = x + 1 in x)\n";
  for (const [source, line, col] of [[sum, 3, 1], [growing, 3, 1], [local, 2, 1]]) {
    for (const flags of [[], ["--fuel", "1000000"]]) {
      const response = cli(["run", "--json", ...flags], source);
      assert.notEqual(response.status, 0);
      assert.equal(response.payload.ok, false);
      assert.equal(response.payload.stage, "eval");
      assert.equal(response.payload.code, "eval.depthLimit");
      assert.match(response.payload.message, /evaluation depth limit exceeded/);
      assert.ok(response.payload.steps > 0 && response.payload.steps < 1000000);
      assert.equal(response.payload.line, line);
      assert.equal(response.payload.col, col);
    }
  }
  const human = spawnSync(binary, ["run", "/dev/stdin"], {
    input: growing, encoding: "utf8", timeout: 15_000,
  });
  assert.ifError(human.error);
  assert.equal(human.signal, null);
  assert.notEqual(human.status, 0);
  assert.match(human.stdout + human.stderr, /evaluation depth limit exceeded/);
  run(sum.replace("sum 100000", "sum 40"), "820");
  const tail = cli(["run", "--json", "--fuel", "2000"],
    "let loop = \\n -> loop (n + 1)\nloop 0\n");
  assert.equal(tail.payload.stage, "eval");
  assert.equal(tail.payload.steps, 2000);
  assert.equal(tail.payload.code, undefined);
  assert.equal(tail.payload.message, "stopped after 2000 steps");
  const early = cli(["run", "--json", "--fuel", "10"], sum);
  assert.equal(early.payload.steps, 10);
  assert.equal(early.payload.code, undefined);
  run("42\n", "42", ["--fuel", "0"]);
});

test("pattern-let docs attach to captures and cycle diagnostics select the affected head", () => {
  const source = "/-- Components of a pair. -/\nlet (identity, number) = (\\x -> x, 7)\n(identity True, number)\n";
  const payload = diagnose(source);
  for (const name of ["identity", "number"]) {
    const definition = payload.symbols.find(s => s.name === name && s.def);
    assert.equal(definition?.doc, "Components of a pair.");
  }
  const bad = cli(["diagnose"], "let (a, b) = (1, 2)\nlet (x, y) = (x, 0)\nx\n");
  assert.match(bad.payload.diagnostics[0]?.message || "", /recursive pattern binding.*x/);
  assert.equal(bad.payload.diagnostics[0].line, 2);
  assert.equal(bad.payload.diagnostics[0].col, 5);
});

test("pattern lets reject duplicate captures and self/mutual cycles by name", () => {
  for (const source of [
    "let (x, y) = (x, 0)\nx\n",
    "let (x, y) = (f 1, 0)\nlet f = \\n -> x\nx\n",
    "let (x, y) = (f 1, 0)\nlet f : Int -> Int = \\n -> x\nx\n",
    "let answer = let (x, y) = (x, 0) in x\nanswer\n",
  ]) {
    const editor = cli(["diagnose"], source);
    assert.match(editor.payload.diagnostics[0]?.message || "", /recursive pattern binding.*x/);
    assert.ok(!editor.payload.diagnostics[0].message.includes("$pattern/"));
    const runner = cli(["run", "--json"], source);
    assert.notEqual(runner.status, 0);
    assert.equal(runner.payload.stage, "parse");
  }
  const duplicate = cli(["diagnose"], "let (x, x) = (1, 2)\nx\n");
  assert.match(duplicate.payload.diagnostics[0]?.message || "", /duplicate names in let pattern/);
});

test("anonymous lambda holes generalize and expose precise token hovers", () => {
  const source = "let id = \\(x : _) -> x\n(id 1, id True)\n";
  const payload = diagnose(source);
  hover(payload, source, 0, "_", "a");
  const response = run(source, "(1, True)");
  assert.match(response.bindings.find(b => b.name === "id")?.type || "", /^∀ .+\. .+ → .+$/);
});

test("structured anonymous holes are independent and retain fixed type constraints", () => {
  const source = "let f : _ -> _ = \\x -> 1\n(f True, f 2)\n";
  const payload = diagnose(source);
  hover(payload, source, 0, "_", "a", 0);
  hover(payload, source, 0, "_", "Int", 1);
  run(source, "(1, 1)");
  const bad = cli(["run", "--json"], "let f : Int -> _ = \\x -> x\nf True\n");
  assert.equal(bad.payload.stage, "typecheck");
  const occurs = cli(["diagnose"], "let f = \\(x : _) -> x x\nf\n");
  assert.equal(occurs.payload.diagnostics[0]?.code, "type.infiniteType");
});

test("datatype holes and adjacent lambda holes show their actual inferred types", () => {
  for (const [source, expected, value] of [
    ["(\\(x : _) (y : _) -> (x,y)) 1 True\n", ["Int", "Bool"], "(1, True)"],
    ["(\\(x : List _) -> x) [1,2]\n", ["Int"], "[1, 2]"],
    ["(\\(x : (_, _)) -> x) (1, True)\n", ["Int", "Bool"], "(1, True)"],
  ]) {
    const payload = diagnose(source);
    expected.forEach((type, i) => hover(payload, source, 0, "_", type, i));
    run(source, value);
  }
  const wildcard = diagnose("let f = \\_ -> 1\nf True\n");
  assert.ok(!wildcard.symbols.some(s => s.kind === "typeHole"));
});

test("pattern-let hole owners and Unicode token spans survive production lowering", () => {
  const pair = "let (x,y) : (_,_) = (1,True)\n(x,y)\n";
  const pairPayload = diagnose(pair);
  hover(pairPayload, pair, 0, "_", "Int", 0);
  hover(pairPayload, pair, 0, "_", "Bool", 1);
  run(pair, "(1, True)");
  const nested = "let (id,n) : (_,_) = (\\(x : _) -> x,1)\n(id True,n)\n";
  const nestedPayload = diagnose(nested);
  hover(nestedPayload, nested, 0, "_", "a → a", 0);
  hover(nestedPayload, nested, 0, "_", "Int", 1);
  hover(nestedPayload, nested, 0, "_", "a", 2);
  run(nested, "(True, 1)");
  const unicode = "('😀', (\\(x : _) -> x) True)\n";
  hover(diagnose(unicode), unicode, 0, "_", "Bool");
  run(unicode, "('😀', True)");
});

test("actual pattern compilation preserves holes in copied fallback arms", () => {
  const source = "let f = \\p -> match p with | (True, True) -> 1 | _ -> let id = \\(x : _) -> x in id 2\n" +
    "(f (True, False), f (False, True))\n";
  const payload = diagnose(source);
  assert.equal(payload.symbols.filter(s => s.kind === "typeHole").length, 1);
  run(source, "(2, 2)");
  run("match (\\(x : _) -> x) True with | True -> 1 | False -> 2\n", "1");
  run("let f = \\((a,b) : (_, _)) -> (b,a)\nf (1, True)\n", "(True, 1)");
});

test("partial forall signatures preserve independent named rigidity", () => {
  run("let id : {a} a -> _ = \\(x : a) -> x\n(id 1, id True)\n", "(1, True)");
  const bad = cli(["run", "--json"], "let f : {a b} a -> b -> _ = \\x y -> x + y\nf\n");
  assert.equal(bad.payload.stage, "typecheck");
});

test("complete signatures permit partial RHSs and preserve their scoped names", () => {
  const source = "let id : {element} element -> element = \\(x : _) -> x\n(id 1, id True)\n";
  hover(diagnose(source), source, 0, "_", "element");
  run(source, "(1, True)");
  run("let id : {a} a -> a = \\x -> x\n(\\(x : _) -> id x) 1\n", "1");
});

test("partial signature displays preserve authored names alongside inferred hole binders", () => {
  const source = "let keep : {element} element -> _ -> element = \\(x : element) (y : _) -> x\n" +
    "(keep 1 True, keep False 2)\n";
  const payload = diagnose(source);
  hover(payload, source, 0, "_", "a", 0);
  hover(payload, source, 0, "_", "a", 1);
  hover(payload, source, 0, "x", "element", 0);
  hover(payload, source, 0, "y", "a");
  const response = run(source, "(1, False)");
  assert.equal(response.bindings.find(b => b.name === "keep")?.type,
    "∀ element a. element → a → element");
});

test("partial signature completion retains unused explicit binders", () => {
  const unused = "let id : {unused} _ -> _ = \\x -> x\n(id 1, id True)\n";
  const unusedPayload = diagnose(unused);
  hover(unusedPayload, unused, 0, "_", "a", 0);
  hover(unusedPayload, unused, 0, "_", "a", 1);
  assert.equal(run(unused, "(1, True)").bindings.find(b => b.name === "id")?.type,
    "∀ unused a. a → a");
});

test("copied signature holes keep every generated scope name", () => {
  const copied = "let f = \\p -> match p with | (True, True) -> 1 | _ -> " +
    "let id : {item} item -> item = \\(x : _) -> x in id 2\n" +
    "(f (True, False), f (False, True))\n";
  const payload = diagnose(copied);
  assert.equal(payload.symbols.filter(s => s.kind === "typeHole").length, 1);
  hover(payload, copied, 0, "_", "item", 1);
  run(copied, "(2, 2)");
});

test("nested signature holes keep outer and inner authored names", () => {
  const nested = "let outer : {element} element -> _ = \\(x : element) -> " +
    "let inner : {item} item -> _ = \\(y : item) -> (x, y) in inner True\nouter 1\n";
  const nestedPayload = diagnose(nested);
  hover(nestedPayload, nested, 0, "_", "(element, Bool)", 0);
  hover(nestedPayload, nested, 0, "_", "(element, item)", 1);
  run(nested, "(1, True)");
});

test("completed signature holes count synthetic binders in every enclosing scope", () => {
  const deep = "let outer : {outer} outer -> _ = \\(x : outer) -> " +
    "let middle : {middle} middle -> _ -> _ = \\(y : middle) z -> " +
    "let inner : {inner} inner -> _ = \\(w : inner) -> x in (inner y, z) " +
    "in middle True\nouter 1 False\n";
  const deepPayload = diagnose(deep);
  hover(deepPayload, deep, 0, "_", "outer", 3);
  run(deep, "(1, False)");
});

test("recursive partial signature structure constrains the entire SCC", () => {
  const shape = "let f : {a} (Int,a) -> _ = \\x -> g x\n" +
    "let g = \\x -> if True then x else f x\n";
  run(shape + "g (1, True)\n", "(1, True)");
  const badShape = cli(["run", "--json"], shape + "g True\n");
  assert.equal(badShape.payload.stage, "typecheck");
});

test("mutual partial signatures may share their separately named forall variables", () => {
  diagnose("let f : {a} a -> _ = \\x -> g x\nlet g : {b} b -> _ = \\x -> f x\nf\n");
});

test("mutual partial signatures may permute their forall variables", () => {
  diagnose("let f : {a b} a -> b -> _ = \\x y -> if True then 1 else g y x\n" +
    "let g : {c d} c -> d -> _ = \\u v -> f v u\nf\n");
});

test("complete recursive signatures permit polymorphic calls while partial signatures forbid them", () => {
  run("let f : {a} a -> Int = \\(x : _) -> if True then 0 else f [x]\nf True\n", "0");
  const badRec = cli(["run", "--json"],
    "let f : {a} a -> _ = \\(x : _) -> if True then 0 else f [x]\nf True\n");
  assert.equal(badRec.payload.stage, "typecheck");
});

// The outer `a` is deliberately absent from both its partial signature type
// and the term environment at the inner signature. It still belongs to the
// provisional forall roots and must not be captured by the inner `b`.
test("a nested signature cannot capture an outer provisional forall root", () => {
  const source = "let f : {a} _ = \\x -> let id : {b} b -> b = \\(y : a) -> y " +
    "in if True then x else f x\nf 1\n";
  const rejected = cli(["run", "--json"], source);
  assert.equal(rejected.status, 1);
  assert.equal(rejected.payload.stage, "typecheck");
});

test("an unrelated nested signature preserves a vacuous outer provisional forall", () => {
  const source = "let f : {a} _ = \\x -> let id : {b} b -> b = \\y -> y " +
    "in if True then x else f x\nf 1\n";
  run(source, "1");
});

console.log(`${tests - failures}/${tests} HM CLI/editor semantic smoke checks passed.`);
process.exitCode = failures ? 1 : 0;
