import express from "express";
import { spawn } from "node:child_process";
import fs from "node:fs";
import path from "node:path";
import { fileURLToPath } from "node:url";
import { createServer as createViteServer } from "vite";

const __dirname = path.dirname(fileURLToPath(import.meta.url));
const REPO_ROOT = path.resolve(__dirname, "../..");
const BIN_DIR = path.join(REPO_ROOT, ".lake", "build", "bin");
const MAX_SOURCE_BYTES = 128 * 1024;
const DIAGNOSE_TIMEOUT_MS = 15_000;
const RUN_TIMEOUT_MS = 20_000;

const PORT = Number(process.env.PORT || 5173);
const STATIC_ONLY = process.env.FHM_WEB_STATIC === "1";

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
 * @param {string} bin
 * @param {string[]} args
 * @param {string} source
 * @param {number} timeoutMs
 * @returns {Promise<{ stdout: string, stderr: string, code: number | null }>}
 */
function runBin(bin, args, source, timeoutMs) {
  return new Promise((resolve, reject) => {
    const child = spawn(bin, args, {
      stdio: ["pipe", "pipe", "pipe"],
      env: { ...process.env, NO_COLOR: "1" },
    });
    let stdout = "";
    let stderr = "";
    let settled = false;

    const timer = setTimeout(() => {
      child.kill("SIGKILL");
      if (!settled) {
        settled = true;
        reject(new Error(`timeout after ${timeoutMs}ms`));
      }
    }, timeoutMs);

    child.stdout.on("data", (c) => {
      stdout += c.toString("utf8");
    });
    child.stderr.on("data", (c) => {
      stderr += c.toString("utf8");
    });
    child.on("error", (err) => {
      clearTimeout(timer);
      if (!settled) {
        settled = true;
        reject(err);
      }
    });
    child.on("close", (code) => {
      clearTimeout(timer);
      if (!settled) {
        settled = true;
        resolve({ stdout, stderr, code });
      }
    });

    child.stdin.write(source, "utf8");
    child.stdin.end();
  });
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
    res.json({
      ok: true,
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

  app.post("/api/diagnose", async (req, res) => {
    const source = readSource(req, res);
    if (source === null) return;
    const bin = resolveFhmBin();
    if (!bin) {
      res.status(503).json({
        error: "fhm not found — run `lake build fhm` in the repo root",
      });
      return;
    }
    try {
      const { stdout, stderr, code } = await runBin(
        bin,
        ["diagnose"],
        source,
        DIAGNOSE_TIMEOUT_MS
      );
      try {
        const payload = JSON.parse(stdout.trim() || "{}");
        res.json(payload);
      } catch (err) {
        res.status(502).json({
          error: `fhm diagnose returned non-JSON (exit ${code})`,
          stderr: stderr.slice(0, 2000),
          detail: String(err),
        });
      }
    } catch (err) {
      res.status(504).json({ error: String(err) });
    }
  });

  app.post("/api/run", async (req, res) => {
    const source = readSource(req, res);
    if (source === null) return;
    const bin = resolveFhmBin();
    if (!bin) {
      res.status(503).json({
        error: "fhm not found — run `lake build fhm` in the repo root",
      });
      return;
    }
    try {
      const { stdout, stderr, code } = await runBin(
        bin,
        ["--json"],
        source,
        RUN_TIMEOUT_MS
      );
      try {
        const payload = JSON.parse(stdout.trim() || "{}");
        res.json(payload);
      } catch (err) {
        res.status(502).json({
          error: `fhm --json returned non-JSON (exit ${code})`,
          stderr: stderr.slice(0, 2000),
          detail: String(err),
        });
      }
    } catch (err) {
      res.status(504).json({ error: String(err) });
    }
  });

  if (STATIC_ONLY) {
    const dist = path.join(__dirname, "dist");
    app.use(express.static(dist));
    app.get("*", (_req, res) => {
      res.sendFile(path.join(dist, "index.html"));
    });
  } else {
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
app.listen(PORT, () => {
  const bin = resolveFhmBin();
  console.log(`FHM playground  http://localhost:${PORT}`);
  console.log(`  fhm: ${bin || "(missing)"}`);
  if (!bin) {
    console.log("  build: lake build fhm  (from repo root)");
  }
});
