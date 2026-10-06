import test from "node:test";
import assert from "node:assert/strict";
import { createHash } from "node:crypto";
import { deflateRawSync } from "node:zlib";
import { DICTIONARY } from "../src/share-dictionary.mjs";
import {
  encodeSource,
  decodeSource,
  sourceFromHash,
  hashFor,
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
test("program hashes round-trip and other hashes are ignored", async () => {
  assert.equal(await sourceFromHash(await hashFor("42")), "42");
  assert.equal(await sourceFromHash("#other"), null);
  assert.equal(await sourceFromHash(""), null);
});
test("invalid links and unknown versions fail clearly", async () => {
  for (const encoded of ["2.w5gugEwQAAA", "1.%%%", "1.YWJj", "1.", "1.a.b"])
    await assert.rejects(decodeSource(encoded));
});
test("source limits apply before encoding and while decompressing", async () => {
  await assert.rejects(
    encodeSource("x".repeat(MAX_SOURCE_BYTES + 1)),
    /128 KiB/,
  );
  const bomb = deflateRawSync(Buffer.alloc(64 * 1024 * 1024, 120), {
    dictionary: Buffer.from(DICTIONARY),
  });
  await assert.rejects(
    decodeSource(`1.${bomb.toString("base64url")}`),
    /128 KiB/,
  );
});
test("links are stable and short", async () => {
  // Every published link depends on these exact dictionary bytes.
  assert.equal(
    createHash("sha256").update(DICTIONARY).digest("hex"),
    "882b10cb99748bcdb5be0b72d172186879444c398384e0655cbc193e21df0989",
  );
  assert.equal(
    await decodeSource("1.w5gugEwQAAA"),
    "let id = \\x -> x\nid 42\n",
  );
  // Interoperates with zlib, i.e. it is plain raw DEFLATE.
  const source = "type Maybe a = Just a | Nothing\n(Just 1, Nothing)\n";
  const zlibLink = deflateRawSync(Buffer.from(source), {
    dictionary: Buffer.from(DICTIONARY),
  }).toString("base64url");
  assert.equal(await decodeSource(`1.${zlibLink}`), source);
  assert.ok((await encodeSource(source)).length < 40);
});
