import { spawn } from "node:child_process";
import { performance } from "node:perf_hooks";

const failure = (message, status = 502) => Object.assign(new Error(message), { status });

// One request per worker. Idle processes retain Lean's initialized modules, but
// cancelled/timed-out processes are killed so stale work never keeps running.
// `check` emits an intermediate {phase:"eval", diagnose} frame followed by
// {run}. Keep the slot and diagnostics across those frames; only evaluation's
// timeout becomes a successful response containing an evaluation limit.
export function createWorkerRunner({ maxProcesses = 2, maxOutputBytes = 4 * 1024 * 1024,
  startupTimeoutMs = 15000, evalTimeoutMs = 3000, onTiming = () => {} } = {}) {
  const workers = new Set();
  function start(bin) {
    const child = spawn(bin, ["--worker"], {
      stdio: ["pipe", "pipe", "pipe"], env: { ...process.env, NO_COLOR: "1" },
    });
    const worker = { child, bin, busy: false, ready: false, pending: null };
    workers.add(worker);
    let buffer = Buffer.alloc(0);
    let stderr = "";
    const started = performance.now();
    const dead = (err) => {
      workers.delete(worker);
      clearTimeout(worker.startupTimer);
      worker.pending?.reject(err);
      worker.pending = null;
      child.kill("SIGKILL");
    };
    worker.dead = dead;
    worker.startupTimer = setTimeout(() => dead(failure("worker startup timeout", 504)), startupTimeoutMs);
    child.stdout.on("data", (chunk) => {
      buffer = Buffer.concat([buffer, chunk]);
      if (buffer.length > maxOutputBytes) return dead(failure("program output exceeds playground limit", 422));
      let end;
      while ((end = buffer.indexOf(10)) !== -1) {
        const line = buffer.subarray(0, end).toString("utf8");
        buffer = buffer.subarray(end + 1);
        let payload;
        try { payload = JSON.parse(line); }
        catch { return dead(failure("worker returned invalid JSON")); }
        if (!worker.ready) {
          if (payload.ready !== true) return dead(failure("worker did not send ready"));
          worker.ready = true;
          clearTimeout(worker.startupTimer);
          onTiming({ phase: "startup", ms: performance.now() - started, pid: child.pid });
          worker.pending?.send();
        } else if (worker.pending) {
          if (worker.pending.frame(payload)) continue;
          worker.pending.resolve({ stdout: line, stderr, code: 0 });
          worker.pending = null;
          stderr = "";
        } else return dead(failure("unsolicited worker output"));
      }
    });
    child.stderr.on("data", chunk => { stderr = (stderr + chunk.toString("utf8")).slice(-2000); });
    child.on("error", dead);
    child.stdin.on("error", dead);
    child.on("close", code => dead(failure(`worker exited (${code}): ${stderr}`)));
    return worker;
  }
  async function run(bin, args, source, timeoutMs, signal) {
    if (signal?.aborted) throw failure("request cancelled", 499);
    let worker = [...workers].find(w => w.bin === bin && !w.busy);
    if (!worker) {
      if (workers.size >= maxProcesses) throw failure("playground busy; please retry shortly", 503);
      worker = start(bin);
    }
    worker.busy = true;
    const command = ["diagnose", "check"].includes(args[0]) ? args[0] : "run";
    const fuelIndex = args.indexOf("--fuel");
    const request = { command, source, ...(fuelIndex < 0 ? {} : { fuel: Number(args[fuelIndex + 1]) }) };
    let timer;
    let diagnosis;
    const began = performance.now();
    const abort = () => worker.dead(failure("request cancelled", 499));
    try {
      return await new Promise((resolve, reject) => {
        worker.pending = { resolve: result => {
          if (diagnosis !== undefined) {
            result.stdout = JSON.stringify({ diagnose: diagnosis, ...JSON.parse(result.stdout) });
          }
          resolve(result);
        }, reject, frame(payload) {
          if (command !== "check" || payload.phase !== "eval") return false;
          if (diagnosis !== undefined || !payload.diagnose) {
            worker.dead(failure("invalid worker evaluation phase"));
            return true;
          }
          diagnosis = payload.diagnose;
          onTiming({ phase: "check-diagnose", ms: performance.now() - began, pid: worker.child.pid });
          clearTimeout(timer);
          timer = setTimeout(() => worker.dead(failure(`timeout after ${evalTimeoutMs}ms`, 504)), evalTimeoutMs);
          return true;
        }, send() {
          timer = setTimeout(() => worker.dead(failure(`timeout after ${timeoutMs}ms`, 504)), timeoutMs);
          worker.child.stdin.write(JSON.stringify(request) + "\n");
        } };
        signal?.addEventListener("abort", abort, { once: true });
        if (worker.ready) worker.pending.send();
      });
    } catch (err) {
      if (err.status === 504 && diagnosis !== undefined) {
        return { stdout: JSON.stringify({ diagnose: diagnosis, run: {
          ok: false, stage: "eval", message: `stopped after ${evalTimeoutMs / 1000} s`, limit: "time",
        } }), stderr: "", code: 0 };
      }
      throw err;
    } finally {
      clearTimeout(timer);
      signal?.removeEventListener("abort", abort);
      worker.busy = false;
      onTiming({ phase: command, ms: performance.now() - began, pid: worker.child.pid });
    }
  }
  run.close = () => { for (const w of workers) w.dead(failure("worker pool closed")); };
  return run;
}
