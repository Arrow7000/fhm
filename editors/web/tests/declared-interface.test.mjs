import test from "node:test";
import assert from "node:assert/strict";
import { createRequire } from "node:module";
const core = createRequire(import.meta.url)("../../shared/fhmEditorCore.cjs");

test("declared-interface status survives normalization and hover resolution", () => {
  const source = "let bad = 1";
  const { ranged, tokens } = core.normalizePayload({ version: 3, diagnostics: [],
    symbols: [{ name: "bad", kind: "val", type: "Int", typeStatus: "declared",
      typeAssumptions: [{ name: "bad", line: 1, col: 5 }], def: true,
      startLine: 1, startCol: 5, endLine: 1, endCol: 8,
      scopeStartLine: 1, scopeStartCol: 5, scopeEndLine: 1, scopeEndCol: 12 }],
    tokens: [[1, 5, 1, 8, "ident"]] });
  const hover = core.resolveHover(ranged, 0, 5, source, tokens);
  assert.equal(hover.type, "Int");
  assert.equal(hover.typeStatus, "declared");
  assert.match(core.hoverMarkdown(hover), /Declared type; implementation is not fully validated/);
  assert.equal(core.resolveDefinition(ranged, 0, 5, source, tokens).startCol0, 4);
});

test("conditional hover notes retain distinct contract names and ordinary type syntax", () => {
  const markdown = core.hoverMarkdown({ name: "result", kind: "val", type: "Int", typeStatus: "conditional",
    typeAssumptions: [{ name: "one" }, { name: "two" }, { name: "one" }] });
  assert.match(markdown, /```fhm\nresult : Int\n```/);
  assert.match(markdown, /unvalidated declared interfaces: `one`, `two`\./);
});
