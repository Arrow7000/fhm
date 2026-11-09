import test from "node:test";
import assert from "node:assert/strict";
import { mkdtempSync, writeFileSync, rmSync } from "node:fs";
import { tmpdir } from "node:os";
import path from "node:path";
import { fileURLToPath } from "node:url";
import { createWorkerRunner } from "../worker-runner.mjs";
import { createRunner } from "../child-runner.mjs";

const bin = fileURLToPath(new URL("../../../.lake/build/bin/fhm", import.meta.url));
test("native worker matches one-shot diagnostics and evaluation across successive edits", async () => {
  const timings = [];
  const run = createWorkerRunner({ onTiming: t => timings.push(t) });
  const once = createRunner();
  try {
    for (const source of ['1', 'let id = \\x -> x\n(id 1, id True)', '1 True', 'let x =', '"☃"']) {
      for (const args of [["diagnose"], ["run", "--json", "--fuel", "200000"]]) {
        const actual = JSON.parse((await run(bin, args, source, 15000)).stdout);
        const expected = JSON.parse((await once(bin, args, source, 15000)).stdout);
        delete actual.timings; delete expected.timings;
        assert.deepEqual(actual, expected);
      }
    }
    assert.equal(timings.filter(t => t.phase === "startup").length, 1);
    assert.equal(new Set(timings.map(t => t.pid)).size, 1);
  } finally { run.close(); }
});

const dir = mkdtempSync(path.join(tmpdir(), "fhm-worker-test-"));
const fake = path.join(dir, "worker");
writeFileSync(fake, `#!${process.execPath}
const rl = require('node:readline').createInterface({input: process.stdin});
console.log('{"ready":true}');
rl.on('line', line => {
 const {source} = JSON.parse(line);
 if(source === 'hang') return;
 if(source === 'crash') process.exit(1);
 if(source === 'big') return console.log(JSON.stringify('x'.repeat(2048)));
 if(source === 'invalid') return console.log('oops');
 console.log(JSON.stringify({source, pid:process.pid}));
});
`, { mode: 0o755 });
test.after(() => rmSync(dir, { recursive: true }));

for (const [source, status] of [["hang",504],["crash",502],["big",422],["invalid",502]]) {
  test(`replaces worker after ${source}`, async () => {
    const run = createWorkerRunner({ maxProcesses: 1, maxOutputBytes: 1024 });
    try {
      await assert.rejects(run(fake, [], source, 100), { status });
      const result = JSON.parse((await run(fake, [], "healthy", 1000)).stdout);
      assert.equal(result.source, "healthy");
    } finally { run.close(); }
  });
}
test("bounds concurrency and replaces aborted workers", async () => {
  const run = createWorkerRunner({ maxProcesses: 1 });
  const controller = new AbortController();
  try {
    const pending = run(fake, [], "hang", 5000, controller.signal);
    await assert.rejects(run(fake, [], "healthy", 1000), {status:503});
    controller.abort();
    await assert.rejects(pending, {status:499});
    assert.equal(JSON.parse((await run(fake, [], "healthy", 1000)).stdout).source, "healthy");
  } finally { run.close(); }
});
test("missing executable releases capacity", async () => {
  const run = createWorkerRunner({ maxProcesses: 1, startupTimeoutMs: 100 });
  try {
    await assert.rejects(run('/nonexistent/fhm', [], '', 1000), {code:'ENOENT'});
    assert.equal(JSON.parse((await run(fake, [], "healthy", 1000)).stdout).source, "healthy");
  } finally { run.close(); }
});

test("startup timeout kills a worker that never becomes ready", async () => {
  const silent = path.join(dir, "silent");
  writeFileSync(silent, `#!${process.execPath}\nsetInterval(() => {}, 1000);\n`, {mode:0o755});
  const run = createWorkerRunner({maxProcesses:1, startupTimeoutMs:100});
  try {
    await assert.rejects(run(silent, [], "", 1000), {status:504});
    assert.equal(JSON.parse((await run(fake, [], "healthy", 1000)).stdout).source, "healthy");
  } finally { run.close(); }
});
