import { deflateSync, Inflate } from "fflate";
import { DICTIONARY } from "./share-dictionary.mjs";

export const MAX_SOURCE_BYTES = 128 * 1024;
const MAX_ENCODED_CHARS = 256 * 1024;
const encoder = new TextEncoder();
const dictionary = encoder.encode(DICTIONARY);
const tooLarge = () =>
  new Error("This program exceeds the 128 KiB playground limit.");

function toBase64(bytes) {
  let text = "";
  for (let i = 0; i < bytes.length; i += 8192)
    text += String.fromCharCode(...bytes.subarray(i, i + 8192));
  return btoa(text).replace(/\+/g, "-").replace(/\//g, "_").replace(/=+$/, "");
}

function fromBase64(text) {
  if (
    !text ||
    !/^[A-Za-z0-9_-]+$/.test(text) ||
    text.length > MAX_ENCODED_CHARS
  )
    throw new Error("This share link is incomplete or invalid.");
  const binary = atob(text.replace(/-/g, "+").replace(/_/g, "/"));
  return Uint8Array.from(binary, (char) => char.charCodeAt(0));
}

function concat(chunks, size) {
  const bytes = new Uint8Array(size);
  let offset = 0;
  for (const chunk of chunks) {
    bytes.set(chunk, offset);
    offset += chunk.byteLength;
  }
  return bytes;
}

// Feed the input in small pieces so a hostile link can't inflate to more
// than about a megabyte past the limit before we notice.
function inflateBounded(bytes, limit) {
  const chunks = [];
  let size = 0;
  const inflate = new Inflate({ dictionary }, (chunk) => {
    size += chunk.byteLength;
    if (size > limit) throw tooLarge();
    chunks.push(chunk);
  });
  if (!bytes.length) inflate.push(bytes, true);
  for (let i = 0; i < bytes.length; i += 1024)
    inflate.push(bytes.subarray(i, i + 1024), i + 1024 >= bytes.length);
  return concat(chunks, size);
}

// Links are `1.<base64url>`: raw DEFLATE with the preset dictionary in
// share-dictionary.mjs. The version leaves room for a new dictionary later.
export async function encodeSource(source) {
  const bytes = encoder.encode(source);
  if (bytes.length > MAX_SOURCE_BYTES) throw tooLarge();
  return `1.${toBase64(deflateSync(bytes, { level: 9, dictionary }))}`;
}

export async function decodeSource(encoded) {
  const [version, ...parts] = encoded.split(".");
  if (version !== "1" || parts.length !== 1)
    throw new Error("This share link uses an unknown format.");
  try {
    const decoded = inflateBounded(fromBase64(parts[0]), MAX_SOURCE_BYTES);
    return new TextDecoder("utf-8", { fatal: true }).decode(decoded);
  } catch (err) {
    if (err.message?.includes("128 KiB")) throw err;
    throw new Error("This share link is incomplete or invalid.");
  }
}

export async function sourceFromHash(hash) {
  if (!hash.startsWith("#code=")) return null;
  return decodeSource(hash.slice(6));
}

export async function hashFor(source) {
  return `#code=${await encodeSource(source)}`;
}
