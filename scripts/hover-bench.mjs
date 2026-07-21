#!/usr/bin/env node
/**
 * Time resolveHover at every column on a line (find hang columns).
 * Usage: node scripts/hover-bench.mjs [path-to.fhm] [line0]
 */
import fs from "node:fs";
import { spawnSync } from "node:child_process";
import path from "node:path";
import { fileURLToPath } from "node:url";
import { createRequire } from "node:module";

const __dirname = path.dirname(fileURLToPath(import.meta.url));
const REPO = path.resolve(__dirname, "..");
const require = createRequire(import.meta.url);
const {
  normalizePayload,
  resolveHover,
  symbolAtRanged,
  identAtColumn,
  symbolAtUseSite,
} = require(path.join(REPO, "editors/shared/fhmEditorCore.cjs"));

const fhmPath = process.argv[2] || path.join(REPO, "scratch/live.fhm");
const line0 = Number(process.argv[3] ?? 2); // default: `type Maybe a =`
const bin = path.join(REPO, ".lake/build/bin/fhm");

const src = fs.readFileSync(fhmPath, "utf8");
const lines = src.split("\n");
const lineText = lines[line0] ?? "";
console.log(`Line ${line0 + 1}: ${JSON.stringify(lineText)}`);

const { stdout, status, error } = spawnSync(bin, ["diagnose"], {
  input: src,
  encoding: "utf8",
  maxBuffer: 10 * 1024 * 1024,
});
if (error || status !== 0) {
  console.error("fhm diagnose failed", error || stdout);
  process.exit(1);
}

const { ranged } = normalizePayload(JSON.parse(stdout.trim()));
console.log(`Ranged symbols: ${ranged.length}\n`);

const SLOW_MS = 50;
for (let col0 = 0; col0 <= lineText.length; col0++) {
  const line = line0 + 1;
  const col = col0 + 1;
  const t0 = performance.now();

  const symR = symbolAtRanged(ranged, line, col);
  const hit = identAtColumn(lineText, col0);
  let symU;
  if (hit) symU = symbolAtUseSite(ranged, line, col, hit.word);
  const result = resolveHover(ranged, line0, col0, lineText);

  const ms = performance.now() - t0;
  const ch = lineText[col0] ?? "(eol)";
  const branch =
    symR && symR.type?.length > 0
      ? "symbolAtRanged+type"
      : hit
        ? symU
          ? "ident+symbolAtUseSite"
          : "ident+noUseSite"
        : "none";
  const flag = ms >= SLOW_MS ? " *** SLOW ***" : "";
  console.log(
    `col0=${col0} '${ch}' ${ms.toFixed(2)}ms branch=${branch} hit=${result?.name ?? "-"}${flag}`
  );
  if (ms >= SLOW_MS) {
    console.log("  symR:", symR?.name, symR?.type?.slice(0, 30));
    console.log("  ident:", hit?.word);
    console.log("  symU count test...");
  }
}
