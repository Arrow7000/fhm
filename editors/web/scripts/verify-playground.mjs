/**
 * Smoke-test the FHM web playground: console errors + Monaco mount.
 * Usage: node scripts/verify-playground.mjs [url]
 */
import { chromium } from "playwright";

const URL = process.argv[2] || "http://localhost:5173";
const TIMEOUT_MS = 30_000;

const consoleLines = [];
const pageErrors = [];

const browser = await chromium.launch({ headless: true });
const page = await browser.newPage();

page.on("console", (msg) => {
  consoleLines.push({ type: msg.type(), text: msg.text() });
});
page.on("pageerror", (err) => {
  pageErrors.push(String(err));
});

try {
  await page.goto(URL, { waitUntil: "networkidle", timeout: TIMEOUT_MS });

  await page.waitForSelector(".monaco-editor", { timeout: TIMEOUT_MS });

  const editorText = await page.evaluate(() => {
    const textarea = document.querySelector(".monaco-editor textarea");
    if (textarea?.value) return textarea.value;
    const lines = document.querySelectorAll(".monaco-editor .view-lines");
    return lines.length ? lines[0].textContent || "" : "";
  });

  const fatalConsole = consoleLines.filter(
    (l) =>
      l.type === "error" &&
      !l.text.includes("[fhm] TextMate setup failed")
  );
  const identReError = [...pageErrors, ...consoleLines.map((l) => l.text)].some(
    (t) => t.includes("IDENT_RE") || t.includes("does not provide an export named")
  );

  const ok =
    !identReError &&
    pageErrors.length === 0 &&
    fatalConsole.length === 0 &&
    editorText.length > 0;

  console.log(JSON.stringify({ ok, url: URL, editorTextLen: editorText.length, pageErrors, fatalConsole, allConsole: consoleLines }, null, 2));
  process.exit(ok ? 0 : 1);
} catch (err) {
  console.error(JSON.stringify({ ok: false, error: String(err), pageErrors, console: consoleLines }, null, 2));
  process.exit(1);
} finally {
  await browser.close();
}
