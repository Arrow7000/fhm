import test from "node:test";
import assert from "node:assert/strict";
import { createRequire } from "node:module";
import { fileURLToPath } from "node:url";
import { spawnSync } from "node:child_process";
const core = createRequire(import.meta.url)("../../shared/fhmEditorCore.cjs");

function diagnose(source) {
  const result = spawnSync(fileURLToPath(new URL("../../../.lake/build/bin/fhm", import.meta.url)), ["diagnose"], { input: source, encoding: "utf8" });
  assert.ifError(result.error);
  return JSON.parse(result.stdout).diagnostics;
}

test("editors use a single concise diagnostic and preserve its source range", () => {
  const [d] = diagnose("let f = \\(x : Int) -> x\nf True");
  assert.equal(d.presentation, undefined, "extended compiler explanations are deferred");
  const [marker] = core.diagnosticsToMarkers([d]);
  assert.equal(marker.message, "Expected Int, found Bool.");
  assert.equal(marker.code, d.code);
  assert.deepEqual([marker.line0, marker.col0, marker.endLine0, marker.endCol0],
    [d.line - 1, d.col - 1, d.endLine - 1, d.endCol - 1]);
});

test("compact editor wording works with older binaries without parsing type syntax", () => {
  for (const [code, message, expected] of [
    ["type.annotationMismatch", "type mismatch: expected Int, got Bool", "Expected Int, found Bool."],
    ["type.argumentMismatch", "type mismatch: expected List (Int → Bool), got Int → List Bool", "Expected List (Int → Bool), found Int → List Bool."],
    ["type.annotationMismatch", "type mismatch in `answer`: expected Int, got Bool", "Type mismatch in `answer`: expected Int, found Bool."],
    ["lower.unboundName", "unbound name `hello`", "Unbound name `hello`."],
    ["future.code", "something unfamiliar", "Something unfamiliar."],
  ]) assert.equal(core.diagnosticMessage({code, message}), expected);
});

test("source text renders as text with only inline code styling", () => {
  const html = core.diagnosticInlineHtml('<img src=x onerror=alert(1)> `[x](command:evil)`');
  assert.ok(!html.includes("<img"));
  assert.match(html, /<code>\[x\]\(command:evil\)<\/code>/);
});


test("legacy unknown labels use a quiet fallback while actual types stay highlighted", () => {
  for (const reason of ["error in expression at 2:27", "error in type `Bad`", "syntax at 1:22"]) {
    const type = `type unknown (${reason})`;
    for (const kind of ["expr", "val", "op", "type"]) {
      const markdown = core.hoverMarkdown({name: "broken", kind, type});
      assert.equal(markdown, "Type unavailable.");
    }
  }
  assert.equal(core.hoverMarkdown({name: "True", kind: "lit", type: "Bool"}),
    "```fhm\nTrue : Bool\n```");
  assert.equal(core.hoverMarkdown({name: "id", kind: "val", type: "a → a"}),
    "```fhm\nid : a → a\n```");
});
