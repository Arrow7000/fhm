"use strict";
/**
 * Long-lived worker: sweep every position, heartbeat after each column.
 * Parent kills the worker if heartbeats stop (hang detection).
 */
const { parentPort, workerData } = require("node:worker_threads");
const path = require("node:path");
const core = require(path.join(__dirname, "../../shared/fhmEditorCore.cjs"));

const { ranged, source, budgetMs } = workerData;
const lines = source.split("\n");

let positions = 0;
let hovers = 0;
let maxMs = 0;
let maxAt = null;
const byKind = {};
const namesHit = new Set();

try {
  for (let line0 = 0; line0 < lines.length; line0++) {
    const lineText = lines[line0];
    for (let col0 = 0; col0 <= lineText.length; col0++) {
      positions++;
      const t0 = process.hrtime.bigint();
      const hit = core.resolveHover(ranged, line0, col0, lineText);
      const ms = Number(process.hrtime.bigint() - t0) / 1e6;

      // Heartbeat so parent can detect stalls.
      parentPort.postMessage({
        type: "tick",
        line: line0 + 1,
        col: col0 + 1,
        ms,
      });

      if (ms > budgetMs) {
        parentPort.postMessage({
          type: "fail",
          reason: `budget at ${line0 + 1}:${col0 + 1} (${ms.toFixed(2)}ms > ${budgetMs}ms)`,
        });
        return;
      }
      if (ms > maxMs) {
        maxMs = ms;
        maxAt = { line: line0 + 1, col: col0 + 1, ms };
      }
      if (hit) {
        hovers++;
        byKind[hit.kind] = (byKind[hit.kind] || 0) + 1;
        namesHit.add(hit.name);
      }
    }
  }
  parentPort.postMessage({
    type: "done",
    summary: {
      positions,
      hovers,
      maxMs: Number(maxMs.toFixed(3)),
      maxAt,
      byKind,
      namesSample: [...namesHit].slice(0, 40),
    },
  });
} catch (err) {
  parentPort.postMessage({
    type: "fail",
    reason: err instanceof Error ? err.message : String(err),
  });
}
