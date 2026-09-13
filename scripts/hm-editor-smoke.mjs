#!/usr/bin/env node
// Build first: lake build fhm
// Run: node scripts/hm-editor-smoke.mjs
// Operational CLI/editor canaries, not metatheory proofs. No Z3 dependency.
import assert from "node:assert/strict";
import { spawnSync } from "node:child_process";
import { createRequire } from "node:module";
import { fileURLToPath } from "node:url";

const require = createRequire(import.meta.url);
const { normalizePayload, resolveHover } = require("../editors/shared/fhmEditorCore.cjs");
const binary = process.env.FHM || fileURLToPath(new URL("../.lake/build/bin/fhm", import.meta.url));
let failures = 0;

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
  const { ranged } = normalizePayload(payload);
  for (let offset = 0; offset < word.length; offset++) {
    const hit = resolveHover(ranged, line0, column + offset, line);
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

test("Path R editor erases BL to List without bounds diagnostics", () => {
  // Deliberately impossible bounds: diagnose is HM-only, not the BL checker.
  const source = "let xs : BL 5 5 Int = [1, 2]\nxs\n";
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

console.log(`${7 - failures}/7 HM CLI/editor semantic smoke checks passed.`);
process.exitCode = failures ? 1 : 0;
