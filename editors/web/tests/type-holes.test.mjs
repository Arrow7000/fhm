import test from "node:test";
import assert from "node:assert/strict";
import { createRequire } from "node:module";

const require = createRequire(import.meta.url);
const core = require("../../shared/fhmEditorCore.cjs");

test("a type-hole token hovers precisely and has no declaration target", () => {
  const source = "\\(x : _) -> x";
  const raw = {
    version: 3,
    symbols: [{ name: "_", kind: "typeHole", type: "Int", def: false,
      startLine: 1, startCol: 7, endLine: 1, endCol: 8,
      scopeStartLine: 1, scopeStartCol: 7, scopeEndLine: 1, scopeEndCol: 8 }],
    tokens: [[1, 7, 1, 8, "punct"]],
    diagnostics: [],
  };
  const { ranged, tokens } = core.normalizePayload(raw);
  const hit = core.resolveHover(ranged, 0, 6, source, tokens);
  assert.equal(hit?.kind, "typeHole");
  assert.equal(hit?.type, "Int");
  assert.equal(hit?.startCol0, 6);
  assert.equal(hit?.endCol0, 7);
  assert.equal(core.hoverMarkdown(hit), "```fhm\n_ : Int\n```");
  assert.equal(core.resolveDefinition(ranged, 0, 6, source, tokens), undefined);
});
