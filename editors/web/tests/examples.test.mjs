import test from "node:test";
import assert from "node:assert/strict";
import { spawnSync } from "node:child_process";
import { existsSync } from "node:fs";
import { fileURLToPath } from "node:url";
import { examples } from "../src/examples.mjs";
const bin = fileURLToPath(
  new URL("../../../.lake/build/bin/fhm", import.meta.url),
);
for (const example of examples) {
  test(`example: ${example.id}`, { skip: !existsSync(bin) }, () => {
    const result = spawnSync(bin, ["--json"], {
      input: example.source,
      encoding: "utf8",
      timeout: 10000,
    });
    assert.ifError(result.error);
    const payload = JSON.parse(result.stdout);
    assert.equal(payload.ok, !example.fails, result.stdout);
    if (!example.fails) assert.equal(payload.result, example.result);
    const diagnostics = spawnSync(bin, ["diagnose"], {
      input: example.source,
      encoding: "utf8",
      timeout: 10000,
    });
    assert.ifError(diagnostics.error);
    assert.equal(
      JSON.parse(diagnostics.stdout).diagnostics.length > 0,
      !!example.fails,
    );
  });
}

// The advanced examples' comments make claims about which signatures matter.
const variants = [
  ["cut", ["let eval : Expr -> Value ="], false],
  ["mutual-polyrec", ["let pingLength : {a} Ping a -> Int ="], true],
  ["mutual-polyrec", ["let pongLength : {b} Pong b -> Int ="], true],
  [
    "mutual-polyrec",
    [
      "let pingLength : {a} Ping a -> Int =",
      "let pongLength : {b} Pong b -> Int =",
    ],
    false,
  ],
];
for (const [id, signatures, accepted] of variants) {
  test(
    `example ${id} without ${signatures.length} signature(s) is ${accepted ? "accepted" : "rejected"}`,
    { skip: !existsSync(bin) },
    () => {
      let source = examples.find((example) => example.id === id).source;
      for (const signature of signatures) {
        assert.ok(source.includes(signature));
        source = source.replace(signature, `${signature.split(" :")[0]} =`);
      }
      const result = spawnSync(bin, ["--json"], {
        input: source,
        encoding: "utf8",
      });
      assert.equal(JSON.parse(result.stdout).ok, accepted, result.stdout);
    },
  );
}
