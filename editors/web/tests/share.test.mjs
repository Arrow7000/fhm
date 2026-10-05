import test from "node:test";
import assert from "node:assert/strict";
import {
  encodeSource,
  decodeSource,
  sourceFromHash,
  shareUrl,
  MAX_SOURCE_BYTES,
} from "../src/share.mjs";

test("snapshots round-trip empty, Unicode, and punctuation-rich programs", async () => {
  for (const source of [
    "",
    "-- λ → ∀ 🥨\nlet id = \\x -> x\nid 42",
    '<&"#?%>\n'.repeat(1000),
  ]) {
    const encoded = await encodeSource(source);
    assert.equal(await decodeSource(encoded), source);
    assert.equal(await sourceFromHash(`#code=${encoded}`), source);
  }
});
test("share URLs contain a stable snapshot and drop unrelated query parameters", async () => {
  const url = new URL(
    await shareUrl("42", "https://fhm.example/?utm_source=test#old"),
  );
  assert.equal(url.search, "");
  assert.equal(await sourceFromHash(url.hash), "42");
  assert.equal(await sourceFromHash("#example=lists"), null);
});
test("invalid links and unknown versions fail clearly", async () => {
  for (const encoded of ["2.abc", "1.%%%", "1.YWJj", "0._w", "1.a.b"])
    await assert.rejects(decodeSource(encoded));
});
test("source limits apply before encoding and while decompressing", async () => {
  await assert.rejects(
    encodeSource("x".repeat(MAX_SOURCE_BYTES + 1)),
    /128 KiB/,
  );
  const stream = new Blob(["x".repeat(MAX_SOURCE_BYTES + 1)])
    .stream()
    .pipeThrough(new CompressionStream("gzip"));
  const compressed = Buffer.from(
    await new Response(stream).arrayBuffer(),
  ).toString("base64url");
  await assert.rejects(decodeSource(`1.${compressed}`), /128 KiB/);
});
