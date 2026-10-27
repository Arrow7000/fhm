import test from "node:test";
import assert from "node:assert/strict";
import fs from "node:fs";
import { spawnSync } from "node:child_process";
import { fileURLToPath } from "node:url";

const grammarUrl = new URL("../../vscode/syntaxes/fhm.tmLanguage.json", import.meta.url);
const grammar = JSON.parse(fs.readFileSync(grammarUrl, "utf8"));

test("named holes have a dedicated grammar rule before ordinary identifiers", () => {
  const names = grammar.patterns.map(p => p.include);
  assert.ok(names.indexOf("#namedHoles") >= 0);
  assert.ok(names.indexOf("#namedHoles") < names.indexOf("#identifiers"));
  assert.equal(grammar.repository.namedHoles.name, "variable.other.type-hole.fhm");
  const pattern = new RegExp(grammar.repository.namedHoles.match, "u");
  for (const name of ["?item", "?a", "?élément", "?😀"]) {
    assert.equal(pattern.exec(name)?.[0], name);
  }
  for (const malformed of ["?", "?1", "? item"]) assert.equal(pattern.test(malformed), false);
});

test("checked-in grammar and token tables agree with the Lean exporter", () => {
  const binary = fileURLToPath(new URL("../../../.lake/build/bin/fhm_grammar", import.meta.url));
  assert.ok(fs.existsSync(binary), "Build fhm_grammar before grammar tests");
  const result = spawnSync(binary, [], { encoding: "utf8" });
  assert.ifError(result.error);
  assert.equal(result.status, 0);
  assert.equal(result.stdout, fs.readFileSync(grammarUrl, "utf8"));
  const tables = spawnSync(binary, ["--tables"], { encoding: "utf8" });
  assert.ifError(tables.error);
  assert.equal(tables.status, 0);
  assert.equal(JSON.parse(tables.stdout).namedHolePrefix, "?");
});
