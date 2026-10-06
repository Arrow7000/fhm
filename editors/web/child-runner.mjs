import { spawn } from "node:child_process";

function failure(message, status) {
  return Object.assign(new Error(message), { status });
}

// Hold each slot until the child exits, including after a timeout or output limit.
export function createRunner({ maxProcesses = 2, maxOutputBytes = 4 * 1024 * 1024 } = {}) {
  let active = 0;
  // `signal` aborts the child, e.g. when the browser cancels a stale request.
  return function runBin(bin, args, source, timeoutMs, signal) {
    if (active >= maxProcesses) {
      return Promise.reject(failure("playground busy; please retry shortly", 503));
    }
    active++;
    return new Promise((resolve, reject) => {
      let child;
      try {
        child = spawn(bin, args, { stdio: ["pipe", "pipe", "pipe"], env: { ...process.env, NO_COLOR: "1" } });
      } catch (err) {
        active--;
        reject(err);
        return;
      }
      let stdout = "";
      let stderr = "";
      let bytes = 0;
      let error;
      const stop = (err) => {
        error ??= err;
        child.kill("SIGKILL");
      };
      const timer = setTimeout(() => stop(failure(`timeout after ${timeoutMs}ms`, 504)), timeoutMs);
      const abort = () => stop(failure("request cancelled", 499));
      if (signal?.aborted) abort();
      else signal?.addEventListener("abort", abort, { once: true });
      const collect = (stream) => (chunk) => {
        bytes += chunk.length;
        if (bytes > maxOutputBytes) {
          stop(failure("program output exceeds playground limit", 422));
          return;
        }
        if (stream === "stdout") stdout += chunk.toString("utf8");
        else stderr += chunk.toString("utf8");
      };
      child.stdout.on("data", collect("stdout"));
      child.stderr.on("data", collect("stderr"));
      child.on("error", (err) => { error ??= err; });
      child.stdin.on("error", (err) => {
        if (err.code !== "EPIPE") stop(err);
      });
      child.on("close", (code) => {
        clearTimeout(timer);
        signal?.removeEventListener("abort", abort);
        active--;
        if (error) reject(error);
        else resolve({ stdout, stderr, code });
      });
      child.stdin.end(source, "utf8");
    });
  };
}
