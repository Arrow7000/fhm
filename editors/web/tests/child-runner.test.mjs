import test from "node:test";
import assert from "node:assert/strict";
import { createRunner } from "../child-runner.mjs";

test("passes stdin and captures both output streams", async () => {
  const run = createRunner();
  const result = await run(process.execPath, ["-e", "process.stdin.pipe(process.stdout); console.error('err')"], "hello", 5000);
  assert.equal(result.stdout, "hello");
  assert.equal(result.stderr.trim(), "err");
  assert.equal(result.code, 0);
});

test("bounds concurrency, kills timed-out children, and frees their slots", async () => {
  const run = createRunner({ maxProcesses: 1 });
  const pending = run(process.execPath, ["-e", "setInterval(() => {}, 1000)"], "", 100);
  await assert.rejects(run(process.execPath, ["-e", ""], "", 5000), { status: 503 });
  await assert.rejects(pending, { status: 504 });
  assert.equal((await run(process.execPath, ["-e", ""], "", 5000)).code, 0);
});

test("bounds combined output and frees the slot after termination", async () => {
  const run = createRunner({ maxProcesses: 1, maxOutputBytes: 1024 });
  await assert.rejects(run(process.execPath, ["-e", "console.log('x'.repeat(2048))"], "", 5000), { status: 422 });
  assert.equal((await run(process.execPath, ["-e", ""], "", 5000)).code, 0);
});

test("a missing executable releases its slot", async () => {
  const run = createRunner({ maxProcesses: 1 });
  await assert.rejects(run("/nonexistent/fhm", [], "", 5000), { code: "ENOENT" });
  assert.equal((await run(process.execPath, ["-e", ""], "", 5000)).code, 0);
});

test("aborting kills the child and frees its slot", async () => {
  const run = createRunner({ maxProcesses: 1 });
  const controller = new AbortController();
  const pending = run(process.execPath, ["-e", "setInterval(() => {}, 1000)"], "", 5000, controller.signal);
  controller.abort();
  await assert.rejects(pending, { status: 499 });
  assert.equal((await run(process.execPath, ["-e", ""], "", 5000)).code, 0);
});
