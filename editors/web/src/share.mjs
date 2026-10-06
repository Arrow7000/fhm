export const MAX_SOURCE_BYTES = 128 * 1024;
const MAX_ENCODED_CHARS = 256 * 1024;
const encoder = new TextEncoder();

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

async function readBounded(stream, limit) {
  const reader = stream.getReader();
  const chunks = [];
  let size = 0;
  try {
    while (true) {
      const { done, value } = await reader.read();
      if (done) break;
      size += value.byteLength;
      if (size > limit) {
        await reader.cancel();
        throw new Error("This program exceeds the 128 KiB playground limit.");
      }
      chunks.push(value);
    }
  } finally {
    reader.releaseLock();
  }
  const bytes = new Uint8Array(size);
  let offset = 0;
  for (const chunk of chunks) {
    bytes.set(chunk, offset);
    offset += chunk.byteLength;
  }
  return bytes;
}

export async function encodeSource(source) {
  const bytes = encoder.encode(source);
  if (bytes.length > MAX_SOURCE_BYTES)
    throw new Error("This program exceeds the 128 KiB playground limit.");
  // Version zero is the uncompressed fallback, including an empty program.
  if (typeof CompressionStream === "undefined") return `0.${toBase64(bytes)}`;
  const stream = new Blob([bytes])
    .stream()
    .pipeThrough(new CompressionStream("gzip"));
  return `1.${toBase64(await readBounded(stream, MAX_ENCODED_CHARS))}`;
}

export async function decodeSource(encoded) {
  const [version, ...parts] = encoded.split(".");
  if (!["0", "1"].includes(version) || parts.length !== 1)
    throw new Error("This share link uses an unknown format.");
  if (version === "0" && parts[0] === "") return "";
  try {
    const bytes = fromBase64(parts[0]);
    const stream =
      version === "1"
        ? new Blob([bytes])
            .stream()
            .pipeThrough(new DecompressionStream("gzip"))
        : new Blob([bytes]).stream();
    return new TextDecoder("utf-8", { fatal: true }).decode(
      await readBounded(stream, MAX_SOURCE_BYTES),
    );
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
