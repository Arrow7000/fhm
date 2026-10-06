import express from "express";
import fs from "node:fs";
import path from "node:path";
import { fileURLToPath } from "node:url";
import { createRunner } from "./child-runner.mjs";

const __dirname = path.dirname(fileURLToPath(import.meta.url));
const REPO_ROOT = path.resolve(__dirname, "../..");
const BIN_DIR = path.join(REPO_ROOT, ".lake", "build", "bin");
const MAX_SOURCE_BYTES = 128 * 1024;
const DIAGNOSE_TIMEOUT_MS = 15_000;
const RUN_TIMEOUT_MS = 20_000;
const LIVE_FUEL = 200_000;
const LIVE_TIMEOUT_MS = 3_000;

const PORT = Number(process.env.PORT || 5173);
const STATIC_ONLY = process.env.FHM_WEB_STATIC === "1" || process.env.NODE_ENV === "production";
const runBin = createRunner();

function resolveFhmBin() {
  for (const fromEnv of [
    process.env.FHM_PATH,
    process.env.FHM_DIAGNOSE_PATH,
    process.env.FHM_LIVE_PATH,
  ]) {
    if (fromEnv && fs.existsSync(fromEnv)) return fromEnv;
  }
  const candidate = path.join(BIN_DIR, "fhm");
  return fs.existsSync(candidate) ? candidate : null;
}

/**
 * @param {express.Request} req
 * @param {express.Response} res
 */
function readSource(req, res) {
  const source =
    typeof req.body?.source === "string"
      ? req.body.source
      : typeof req.body === "string"
        ? req.body
        : null;
  if (source === null) {
    res.status(400).json({ error: "expected JSON body { source: string }" });
    return null;
  }
  if (Buffer.byteLength(source, "utf8") > MAX_SOURCE_BYTES) {
    res.status(413).json({ error: `source exceeds ${MAX_SOURCE_BYTES} bytes` });
    return null;
  }
  return source;
}

async function createApp() {
  const app = express();
  app.use(express.json({ limit: "256kb" }));

  app.get("/api/health", (_req, res) => {
    const bin = resolveFhmBin();
    res.status(bin ? 200 : 503).json({
      ok: Boolean(bin),
      diagnose: Boolean(bin),
      live: Boolean(bin),
    });
  });

  app.get("/api/example", (_req, res) => {
    const examplePath = path.join(REPO_ROOT, "scratch", "live.fhm");
    if (!fs.existsSync(examplePath)) {
      res.status(404).type("text/plain").send("scratch/live.fhm not found");
      return;
    }
    res.type("text/plain").send(fs.readFileSync(examplePath, "utf8"));
  });

  // Run `fhm` with the given arguments and parse its JSON output. The child is
  // killed if the browser gives up on the request first.
  async function fhmJson(res, args, source, timeoutMs, signal) {
    const bin = resolveFhmBin();
    if (!bin) {
      res.status(503).json({
        error: "fhm not found — run `lake build fhm` in the repo root",
      });
      return null;
    }
    try {
      const { stdout, stderr, code } = await runBin(bin, args, source, timeoutMs, signal);
      try {
        return JSON.parse(stdout.trim() || "{}");
      } catch (err) {
        res.status(502).json({
          error: `fhm ${args.join(" ")} returned non-JSON (exit ${code})`,
          stderr: stderr.slice(0, 2000),
          detail: String(err),
        });
        return null;
      }
    } catch (err) {
      // A live run that hits its time budget is a result, not a failure.
      if (err.status === 504 && args.includes("--fuel")) {
        return { ok: false, stage: "eval", message: `stopped after ${timeoutMs / 1000} s`, limit: "time" };
      }
      if (!res.headersSent) res.status(err.status || 502).json({ error: String(err) });
      return null;
    }
  }

  function cancellation(res) {
    const controller = new AbortController();
    res.on("close", () => {
      if (!res.writableFinished) controller.abort();
    });
    return controller.signal;
  }

  app.post("/api/diagnose", async (req, res) => {
    const source = readSource(req, res);
    if (source === null) return;
    const payload = await fhmJson(res, ["diagnose"], source, DIAGNOSE_TIMEOUT_MS, cancellation(res));
    if (payload) res.json(payload);
  });

  // Unbounded evaluation, for programs that exceed the live check's budget.
  app.post("/api/run", async (req, res) => {
    const source = readSource(req, res);
    if (source === null) return;
    const payload = await fhmJson(res, ["--json"], source, RUN_TIMEOUT_MS, cancellation(res));
    if (payload) res.json(payload);
  });

  // What the playground calls on every edit: diagnostics and hover data, then,
  // if the program type-checks, a run within a small step and time budget.
  app.post("/api/check", async (req, res) => {
    const source = readSource(req, res);
    if (source === null) return;
    const signal = cancellation(res);
    const diagnose = await fhmJson(res, ["diagnose"], source, DIAGNOSE_TIMEOUT_MS, signal);
    if (!diagnose) return;
    const failed = (diagnose.diagnostics || []).some((d) => d.severity !== "warning");
    if (failed) return res.json({ diagnose, run: null });
    const args = ["run", "--json", "--fuel", String(LIVE_FUEL)];
    const run = await fhmJson(res, args, source, LIVE_TIMEOUT_MS, signal);
    if (run) res.json({ diagnose, run });
  });

  if (STATIC_ONLY) {
    const dist = path.join(__dirname, "dist");
    app.use(express.static(dist));
    app.get("*", (_req, res) => {
      res.sendFile(path.join(dist, "index.html"));
    });
  } else {
    const { createServer: createViteServer } = await import("vite");
    const vite = await createViteServer({
      root: __dirname,
      configFile: path.join(__dirname, "vite.config.js"),
      server: { middlewareMode: true },
      appType: "spa",
    });
    app.use(vite.middlewares);
  }

  return app;
}

const app = await createApp();
app.listen(PORT, "0.0.0.0", () => {
  const bin = resolveFhmBin();
  console.log(`FHM playground  http://localhost:${PORT}`);
  console.log(`  fhm: ${bin || "(missing)"}`);
  if (!bin) {
    console.log("  build: lake build fhm  (from repo root)");
  }
});
