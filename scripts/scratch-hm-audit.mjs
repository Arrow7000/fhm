#!/usr/bin/env node
// Reproducible HM-only editor audit. No evaluation, Bounds checks, or Z3 calls.
import assert from "node:assert/strict";
import fs from "node:fs";
import path from "node:path";
import { fileURLToPath } from "node:url";
import { spawnSync } from "node:child_process";

const root = fileURLToPath(new URL("../", import.meta.url));
const binary = process.env.FHM || path.join(root, ".lake/build/bin/fhm");
const expectedRejects = new Set([
  "polyrec-groups-nested.fhm",
  "polyrec-head-binder-scoped-must-fail.fhm",
  "polyrec-inner-poly-calls.fhm",
  "polyrec-inner-poly-unannotated-must-fail.fhm",
  "polyrec-mixed-conflict-must-fail.fhm",
  "polyrec-mixed-group.fhm",
  "polyrec-nested.fhm",
  "polyrec-unannotated-must-fail.fhm",
]);
let failures = 0;
let accepted = 0;
let rejected = 0;
const files = fs.readdirSync(path.join(root, "scratch"))
  .filter(name => name.endsWith(".fhm")).sort();
for (const file of files) {
  try {
    const response = spawnSync(binary, ["diagnose", path.join(root, "scratch", file)], {
      encoding: "utf8", timeout: 15_000, maxBuffer: 8 * 1024 * 1024,
    });
    assert.ifError(response.error);
    assert.equal(response.signal, null);
    const payload = JSON.parse(response.stdout);
    assert.equal(payload.version, 3);
    if (expectedRejects.has(file)) {
      assert.equal(response.status, 1, "Expected D2/scoped-sugar rejection");
      assert.ok(payload.diagnostics.length > 0);
      for (const d of payload.diagnostics) {
        assert.ok(d.endLine > d.line || d.endCol > d.col, "Empty diagnostic range");
      }
      rejected++;
      console.log(`PASS reject ${file}: ${payload.diagnostics[0].message}`);
    } else {
      assert.equal(response.status, 0, JSON.stringify(payload.diagnostics));
      assert.deepEqual(payload.diagnostics, []);
      assert.ok(payload.programTy.length > 0);
      for (const symbol of payload.symbols) {
        assert.ok(!/\?[a-zA-Z]\w*/.test(symbol.type), `Debug metavariable in ${symbol.name}: ${symbol.type}`);
      }
      accepted++;
      console.log(`PASS accept ${file}: ${payload.programTy} (${payload.symbols.length} symbols)`);
    }
  } catch (error) {
    failures++;
    console.error(`FAIL ${file}: ${error.message}`);
  }
}
for (const file of expectedRejects) {
  if (!files.includes(file)) {
    failures++;
    console.error(`FAIL missing negative canary ${file}`);
  }
}
console.log(`${files.length} files: ${accepted} accepted, ${rejected} expected rejections, ${failures} audit failures.`);
process.exitCode = failures ? 1 : 0;
