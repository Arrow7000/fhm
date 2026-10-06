/** End-to-end checks against a running production build, local or hosted. */
import assert from "node:assert/strict";
import { chromium } from "playwright";
import { examples } from "../src/examples.mjs";
import { sourceFromHash } from "../src/share.mjs";
const url = (process.argv[2] || "http://localhost:5173").replace(/\/$/, "");
const mod = process.platform === "darwin" ? "Meta" : "Control";
const browser = await chromium.launch({ headless: true });
const errors = [];
const context = await browser.newContext({
  viewport: { width: 1440, height: 900 },
  permissions: ["clipboard-read", "clipboard-write"],
});
const page = await context.newPage();
page.on("pageerror", (error) => errors.push(String(error)));
page.on("console", (message) => {
  if (message.type() === "error") errors.push(message.text());
});
page.setDefaultTimeout(60000);
const ready = (p = page) => p.locator("#status.ok").waitFor();
const hash = (p = page) => p.evaluate(() => location.hash);
const draft = (p = page) =>
  p.evaluate(() => JSON.parse(localStorage.getItem("fhm.draft")).source);
async function program(p, text) {
  await p.locator(".monaco-editor textarea").focus();
  await p.keyboard.press(`${mod}+A`);
  await p.keyboard.insertText(text);
}
async function example(p, title) {
  await p.locator("#examples").click();
  await p.locator("#examples-menu button").filter({ hasText: title }).click();
}
try {
  await page.goto(url);
  await ready();
  // A fresh visitor sees the first example, named in the URL.
  assert.equal(await hash(), `#example=${examples[0].id}`);
  // The program is evaluated without pressing anything.
  await page.locator(".result-value").waitFor();
  assert.equal(
    await page.locator(".result-value").innerText(),
    examples[0].result,
  );
  assert.equal(await page.locator("#types .bindings button.name").count(), 3);

  const downloadEvent = page.waitForEvent("download");
  await page.locator("#download").click();
  assert.match((await downloadEvent).suggestedFilename(), /^program-[0-9a-f]{7}\.fhm$/);

  await page.locator("#divider").focus();
  await page.keyboard.press("ArrowLeft");
  assert.equal(
    await page.locator("#divider").getAttribute("aria-valuenow"),
    "58",
  );

  // Editing re-evaluates and keeps the address bar in sync.
  const edited = "-- a saved draft\nlet answer = 42\nanswer\n";
  await program(page, edited);
  await page.locator(".result-value", { hasText: /^42$/ }).waitFor();
  await page.waitForFunction(() => location.hash.startsWith("#code="));
  assert.equal(await sourceFromHash(await hash()), edited);
  // A program that no longer type-checks keeps the last result, dimmed.
  await program(page, "let answer = 42\nanswer True\n");
  await page.locator("#status.err").waitFor();
  assert.ok(await page.locator("#result.stale .result-value").count());
  // A program that doesn't finish within the live budget can run without it.
  await program(page, "let loop = \\n -> loop (n + 1)\nloop 0\n");
  await page.locator("#result button", { hasText: "Run without a limit" }).waitFor();
  await program(page, edited);
  await page.locator(".result-value", { hasText: /^42$/ }).waitFor();

  // Share copies the live URL rather than opening a dialog.
  await page.locator(".monaco-editor textarea").focus();
  await page.keyboard.press(`${mod}+s`);
  await page.locator("#share-label", { hasText: "Link copied" }).waitFor();
  const sharedUrl = await page.evaluate(() => navigator.clipboard.readText());
  assert.equal(sharedUrl, await page.evaluate(() => location.href));
  assert.equal(await page.locator("dialog[open]").count(), 0);

  // The draft survives a visit without a hash.
  await page.goto(url);
  await ready();
  assert.equal(await draft(), edited);
  assert.ok((await hash()).startsWith("#code="));

  // Opening someone else's link replaces the draft but keeps it restorable.
  await page.goto(`${url}/#example=lists`);
  await ready();
  assert.equal(await draft(), examples[1].source);
  await example(page, "Restore previous program");
  await ready();
  assert.equal(await draft(), edited);

  await example(page, "A type error");
  await page.locator("#status.err").waitFor();
  assert.ok(await page.locator(".problem").count());
  await page.locator(".problem").first().click();

  await page.locator("#theme").click();
  assert.equal(await page.locator("html").getAttribute("data-theme"), "dark");
  if (process.env.FHM_SCREENSHOTS)
    await page.screenshot({ path: `${process.env.FHM_SCREENSHOTS}-dark.png` });
  await page.locator("#theme").click();
  await example(page, examples[0].title);
  await page.locator(".result-value").waitFor();
  if (process.env.FHM_SCREENSHOTS)
    await page.screenshot({ path: `${process.env.FHM_SCREENSHOTS}-light.png` });

  await page.locator("#help").click();
  await page.locator("#help-dialog[open]").waitFor();
  await page.keyboard.press("Escape");

  await page.setViewportSize({ width: 390, height: 844 });
  await page.waitForTimeout(300);
  assert.equal(
    await page.locator("#divider").getAttribute("aria-orientation"),
    "horizontal",
  );
  assert.ok(
    await page.evaluate(
      () => document.documentElement.scrollWidth <= innerWidth,
    ),
  );
  assert.ok(await page.locator("#share").isVisible());
  if (process.env.FHM_SCREENSHOTS)
    await page.screenshot({
      path: `${process.env.FHM_SCREENSHOTS}-mobile.png`,
    });

  const fresh = await browser.newContext();
  const other = await fresh.newPage();
  await other.goto(sharedUrl);
  await ready(other);
  await other.locator(".result-value").waitFor();
  assert.equal(await other.locator(".result-value").innerText(), "42");
  await fresh.close();

  const unavailable = await browser.newContext();
  await unavailable.addInitScript(() => {
    Object.defineProperty(window, "localStorage", {
      get() {
        throw new Error("Storage blocked");
      },
    });
    Object.defineProperty(navigator, "clipboard", {
      value: {
        writeText: async () => {
          throw new Error("Clipboard blocked");
        },
      },
    });
  });
  const blocked = await unavailable.newPage();
  await blocked.goto(url);
  await ready(blocked);
  await blocked.locator("#share").click();
  await blocked.locator("#share-label", { hasText: "address bar" }).waitFor();
  await unavailable.close();

  assert.deepEqual(errors, []);
  console.log(
    JSON.stringify({
      ok: true,
      url,
      checks: [
        "evaluation",
        "inferred types",
        "download",
        "keyboard resize",
        "live URL",
        "live evaluation",
        "stale result",
        "step limit",
        "share copies URL",
        "draft restore",
        "link precedence & restore previous",
        "problem navigation",
        "theme",
        "help",
        "mobile layout",
        "fresh-browser share",
        "blocked storage & clipboard fallback",
      ],
    }),
  );
} finally {
  await browser.close();
}
