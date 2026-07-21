#!/usr/bin/env node
/**
 * Exhaustive hover sweep — emulates Monaco/VS Code hover at every source position.
 * Spawns fhm_diagnose on a fixture unless --json is given.
 *
 * Fails (exit 1) on: throw, per-position budget overrun, or hard hang (worker timeout).
 *
 * Usage:
 *   node editors/web/scripts/hover-sweep.mjs
 *   node editors/web/scripts/hover-sweep.mjs --all
 *   node editors/web/scripts/hover-sweep.mjs --all --safe
 *   node editors/web/scripts/hover-sweep.mjs path/to/file.fhm
 *   HOVER_BUDGET_MS=50 HOVER_HANG_MS=2000 node editors/web/scripts/hover-sweep.mjs --verbose
 */
import { spawn } from "node:child_process";
import fs from "node:fs";
import path from "node:path";
import { fileURLToPath } from "node:url";
import { Worker } from "node:worker_threads";
import { createRequire } from "node:module";

const require = createRequire(import.meta.url);
const core = require("../../shared/fhmEditorCore.cjs");

const __dirname = path.dirname(fileURLToPath(import.meta.url));
const REPO_ROOT = path.resolve(__dirname, "../../..");
const DEFAULT_FIXTURE = path.join(REPO_ROOT, "scratch/live.fhm");
const RICH_FIXTURE = path.join(
  REPO_ROOT,
  "editors/web/fixtures/hover-rich.fhm"
);
const DIAGNOSE_BIN = path.join(REPO_ROOT, ".lake/build/bin/fhm_diagnose");
const BUDGET_MS = Number(process.env.HOVER_BUDGET_MS || 50);
const HANG_MS = Number(process.env.HOVER_HANG_MS || 2000);
const args = process.argv.slice(2);
const verbose = args.includes("--verbose");
const allFixtures = args.includes("--all");
const positional = args.filter((a) => !a.startsWith("-"));

/** Kinds we expect to see at least once on the rich/live fixtures. */
const REQUIRED_KINDS = ["type", "ctor", "param", "val"];

/**
 * @param {string} source
 * @returns {Promise<unknown>}
 */
function runDiagnose(source) {
  return new Promise((resolve, reject) => {
    if (!fs.existsSync(DIAGNOSE_BIN)) {
      reject(
        new Error(
          `fhm_diagnose not found at ${DIAGNOSE_BIN} — run lake build fhm_diagnose`
        )
      );
      return;
    }
    const child = spawn(DIAGNOSE_BIN, [], { stdio: ["pipe", "pipe", "pipe"] });
    let stdout = "";
    let stderr = "";
    const timer = setTimeout(() => {
      child.kill("SIGKILL");
      reject(new Error(`fhm_diagnose timed out after ${HANG_MS * 5}ms`));
    }, Math.max(15_000, HANG_MS * 5));
    child.stdout.on("data", (c) => {
      stdout += c.toString("utf8");
    });
    child.stderr.on("data", (c) => {
      stderr += c.toString("utf8");
    });
    child.on("error", (err) => {
      clearTimeout(timer);
      reject(err);
    });
    child.on("close", (code) => {
      clearTimeout(timer);
      try {
        resolve(JSON.parse(stdout.trim() || "{}"));
      } catch (err) {
        reject(
          new Error(
            `fhm_diagnose parse failed (exit ${code}): ${stderr || String(err)}`
          )
        );
      }
    });
    child.stdin.write(source, "utf8");
    child.stdin.end();
  });
}

/**
 * Fast in-process sweep; still budget-checked.
 * @param {string} fixturePath
 * @param {unknown} raw
 * @param {string} source
 */
function sweepFast(fixturePath, raw, source) {
  const { ranged } = core.normalizePayload(raw);
  const lines = source.split("\n");

  let positions = 0;
  let hovers = 0;
  let maxMs = 0;
  /** @type {{ line: number, col: number, ms: number } | null} */
  let maxAt = null;
  /** @type {Record<string, number>} */
  const byKind = {};
  /** @type {Set<string>} */
  const namesHit = new Set();

  for (let line0 = 0; line0 < lines.length; line0++) {
    const lineText = lines[line0];
    for (let col0 = 0; col0 <= lineText.length; col0++) {
      positions++;
      const t0 = process.hrtime.bigint();
      let hit;
      try {
        hit = core.resolveHover(ranged, line0, col0, lineText);
      } catch (err) {
        console.error(
          `FAIL throw at ${line0 + 1}:${col0 + 1} (${JSON.stringify(lineText[col0] ?? "eol")})`,
          err
        );
        process.exit(1);
      }
      const ms = Number(process.hrtime.bigint() - t0) / 1e6;
      if (ms > maxMs) {
        maxMs = ms;
        maxAt = { line: line0 + 1, col: col0 + 1, ms };
      }
      if (ms > BUDGET_MS) {
        console.error(
          `FAIL budget at ${line0 + 1}:${col0 + 1} (${ms.toFixed(2)}ms > ${BUDGET_MS}ms)`
        );
        process.exit(1);
      }
      if (hit) {
        hovers++;
        byKind[hit.kind] = (byKind[hit.kind] || 0) + 1;
        namesHit.add(hit.name);
        if (verbose) {
          console.log(
            `${line0 + 1}:${col0 + 1} ${hit.kind} ${hit.name} : ${hit.type}`
          );
        }
      }
    }
  }

  return {
    ok: true,
    fixture: fixturePath,
    symbolCount: ranged.length,
    positions,
    hovers,
    maxMs: Number(maxMs.toFixed(3)),
    maxAt,
    byKind,
    namesSample: [...namesHit].slice(0, 40),
    budgetMs: BUDGET_MS,
  };
}

/**
 * Full sweep in one worker; fail if heartbeats stall (hang) or budget exceeded.
 * @param {string} fixturePath
 * @param {unknown} raw
 * @param {string} source
 */
function sweepSafe(fixturePath, raw, source) {
  const { ranged } = core.normalizePayload(raw);
  return new Promise((resolve, reject) => {
    const workerPath = path.join(__dirname, "hover-sweep-worker.cjs");
    const worker = new Worker(workerPath, {
      workerData: { ranged, source, budgetMs: BUDGET_MS },
    });
    let lastTick = Date.now();
    let lastPos = "0:0";
    let settled = false;
    const finish = (fn, arg) => {
      if (settled) return;
      settled = true;
      clearInterval(watchdog);
      worker.terminate();
      fn(arg);
    };
    const watchdog = setInterval(() => {
      if (Date.now() - lastTick > HANG_MS) {
        finish(
          reject,
          new Error(`HANG near ${lastPos} (no heartbeat in ${HANG_MS}ms)`)
        );
      }
    }, Math.min(250, Math.max(50, HANG_MS / 4)));

    worker.on("message", (msg) => {
      if (msg.type === "tick") {
        lastTick = Date.now();
        lastPos = `${msg.line}:${msg.col}`;
        return;
      }
      if (msg.type === "fail") {
        finish(reject, new Error(msg.reason || "sweep failed"));
        return;
      }
      if (msg.type === "done") {
        finish(resolve, {
          ok: true,
          fixture: fixturePath,
          symbolCount: ranged.length,
          ...msg.summary,
          budgetMs: BUDGET_MS,
          hangMs: HANG_MS,
        });
      }
    });
    worker.on("error", (err) => finish(reject, err));
  });
}

/**
 * @param {Record<string, number>} byKind
 * @param {string} fixturePath
 */
function assertCoverage(byKind, fixturePath) {
  const missing = REQUIRED_KINDS.filter((k) => !byKind[k]);
  if (missing.length > 0) {
    console.error(
      `FAIL coverage on ${fixturePath}: missing kinds ${missing.join(", ")}`
    );
    process.exit(1);
  }
}

/**
 * Spot-check: type-param `a` on `type Maybe a` must resolve quickly as param.
 * @param {any[]} ranged
 * @param {string} source
 */
function spotCheckMaybeA(ranged, source) {
  const lines = source.split("\n");
  const line0 = lines.findIndex((l) => /^type Maybe a\b/.test(l));
  if (line0 < 0) return;
  const lineText = lines[line0];
  const col0 = lineText.indexOf(" a");
  if (col0 < 0) return;
  const aCol = col0 + 1; // the `a`
  const t0 = process.hrtime.bigint();
  const hit = core.resolveHover(ranged, line0, aCol, lineText);
  const ms = Number(process.hrtime.bigint() - t0) / 1e6;
  if (ms > BUDGET_MS) {
    console.error(`FAIL Maybe a hover budget: ${ms.toFixed(2)}ms`);
    process.exit(1);
  }
  if (!hit || hit.name !== "a" || hit.kind !== "param") {
    console.error(`FAIL Maybe a hover: expected param a, got`, hit);
    process.exit(1);
  }
  // Range must contain the cursor (Monaco thrash guard).
  if (
    hit.startLine0 !== line0 ||
    aCol < hit.startCol0 ||
    aCol >= hit.endCol0
  ) {
    console.error(`FAIL Maybe a hover range misses cursor`, hit);
    process.exit(1);
  }
  if (verbose) {
    console.log(`spot-check Maybe a: ok (${ms.toFixed(3)}ms) → ${hit.type}`);
  }
}

/**
 * @param {string} fixturePath
 */
async function runOne(fixturePath) {
  const source = fs.readFileSync(fixturePath, "utf8");
  const raw = await runDiagnose(source);
  const useSafe = args.includes("--safe");
  const summary = useSafe
    ? await sweepSafe(fixturePath, raw, source)
    : sweepFast(fixturePath, raw, source);
  const { ranged } = core.normalizePayload(raw);
  spotCheckMaybeA(ranged, source);
  assertCoverage(summary.byKind, fixturePath);
  console.log(JSON.stringify(summary, null, 2));
  return summary;
}

async function main() {
  const jsonArgIdx = args.indexOf("--json");
  if (jsonArgIdx !== -1) {
    const jsonPath = args[jsonArgIdx + 1];
    if (!jsonPath) {
      console.error("--json requires a path");
      process.exit(2);
    }
    const raw = JSON.parse(fs.readFileSync(jsonPath, "utf8"));
    const source =
      typeof raw.source === "string"
        ? raw.source
        : fs.readFileSync(DEFAULT_FIXTURE, "utf8");
    const summary = args.includes("--safe")
      ? await sweepSafe(jsonPath, raw, source)
      : sweepFast(jsonPath, raw, source);
    console.log(JSON.stringify(summary, null, 2));
    return;
  }

  /** @type {string[]} */
  let fixtures;
  if (allFixtures) {
    fixtures = [DEFAULT_FIXTURE, RICH_FIXTURE].filter((p) => fs.existsSync(p));
  } else if (positional[0]) {
    fixtures = [path.resolve(positional[0])];
  } else {
    fixtures = [DEFAULT_FIXTURE];
  }

  for (const f of fixtures) {
    await runOne(f);
  }
}

main().catch((err) => {
  console.error(err);
  process.exit(1);
});
