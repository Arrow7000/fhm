// Golden hover / go-to-definition snapshots.
//
// For each `fixtures/*.fhm` with a `*.hover.txt` next to it, run `fhm diagnose`,
// resolve hover and definition at every column, and compare against the
// snapshot. Regenerate after an intended change with
//
//   UPDATE_HOVER_SNAPSHOTS=1 npm test
//
// and review the diff. Needs the CLI (`lake build fhm`); skipped without it.
import test from "node:test";
import assert from "node:assert/strict";
import { spawnSync } from "node:child_process";
import fs from "node:fs";
import path from "node:path";
import { createRequire } from "node:module";
import { fileURLToPath } from "node:url";

const require = createRequire(import.meta.url);
const core = require("../../shared/fhmEditorCore.cjs");

const here = path.dirname(fileURLToPath(import.meta.url));
const fixtures = path.join(here, "../fixtures");
const binary = process.env.FHM || path.join(here, "../../../.lake/build/bin/fhm");
const update = process.env.UPDATE_HOVER_SNAPSHOTS === "1";

/**
 * One line per maximal run of columns with the same hover and definition:
 *
 *   `cols  text  kind  shown  [⟦highlight⟧]  [→ def line:col]  [doc "…"]`
 *
 * Runs with neither are left out. The highlight `⟦…⟧` is shown when it differs
 * from the run's own columns.
 * @param {string} source
 * @param {unknown} raw
 */
export function renderSnapshot(source, raw) {
  const { ranged, tokens, diagnostics } = core.normalizePayload(raw);
  const out = diagnostics.map((d) => `! ${d.line}:${d.col} ${d.message}`);
  source.split("\n").forEach((lineText, line0) => {
    if (lineText.trim() === "") return;
    out.push(`${line0 + 1} │ ${lineText}`);
    /** @type {{ key: string, from: number, to: number, hit?: any, def?: any } | undefined} */
    let run;
    const flush = () => {
      if (!run || (!run.hit && !run.def)) return;
      const text = lineText.slice(run.from, run.to);
      const cols = run.to - run.from > 1 ? `${run.from + 1}-${run.to}` : `${run.from + 1}`;
      let entry = `    ${cols.padEnd(7)} ${JSON.stringify(text).padEnd(14)}`;
      if (run.hit) {
        const { kind, name, type, startCol0, endCol0 } = run.hit;
        const shown = kind === "expr" ? type : `${name} : ${type}`;
        entry += ` ${kind.padEnd(5)} ${shown.replaceAll("\n", "⏎ ")}`;
        if (startCol0 !== run.from || endCol0 !== run.to) {
          entry += `  ⟦${lineText.slice(startCol0, endCol0)}⟧`;
        }
      }
      if (run.def) entry += `  → def ${run.def.startLine0 + 1}:${run.def.startCol0 + 1}`;
      if (run.hit?.doc) entry += `  doc ${JSON.stringify(run.hit.doc)}`;
      out.push(entry);
    };
    for (let col0 = 0; col0 < lineText.length; col0++) {
      const hit = core.resolveHover(ranged, line0, col0, lineText, tokens);
      const def = core.resolveDefinition(ranged, line0, col0, lineText, tokens);
      const key = JSON.stringify([hit, def]);
      if (run && run.key === key) {
        run.to = col0 + 1;
      } else {
        flush();
        run = { key, from: col0, to: col0 + 1, hit, def };
      }
    }
    flush();
  });
  return out.join("\n") + "\n";
}

const cases = fs
  .readdirSync(fixtures)
  .filter((f) => f.endsWith(".fhm") && fs.existsSync(path.join(fixtures, f.replace(/\.fhm$/, ".hover.txt"))));

for (const file of cases) {
  test(`hover snapshot: ${file}`, { skip: !fs.existsSync(binary) && `no fhm binary at ${binary}` }, () => {
    const source = fs.readFileSync(path.join(fixtures, file), "utf8");
    const child = spawnSync(binary, ["diagnose"], { input: source, encoding: "utf8", maxBuffer: 16 << 20 });
    assert.ifError(child.error);
    const actual = renderSnapshot(source, JSON.parse(child.stdout));
    const snapshot = path.join(fixtures, file.replace(/\.fhm$/, ".hover.txt"));
    if (update) fs.writeFileSync(snapshot, actual);
    assert.equal(actual, fs.readFileSync(snapshot, "utf8"));
  });
}
