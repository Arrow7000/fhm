/** End-to-end checks against a running production build, local or hosted. */
import assert from "node:assert/strict";
import { chromium } from "playwright";
import { examples } from "../src/examples.mjs";
import { sourceFromHash } from "../src/share.mjs";
const url = process.argv[2] || "http://localhost:5173";
const browser = await chromium.launch({ headless: true });
const errors = [];
const context = await browser.newContext({
  viewport: { width: 1440, height: 900 },
});
const page = await context.newPage();
page.on("pageerror", (error) => errors.push(String(error)));
page.on("console", (message) => {
  if (message.type() === "error") errors.push(message.text());
});
page.setDefaultTimeout(60000);
async function ready(p = page) {
  await p.locator("#status.ok").waitFor();
}
async function program(p, text) {
  await p.locator(".monaco-editor textarea").focus();
  await p.keyboard.press(
    process.platform === "darwin" ? "Meta+A" : "Control+A",
  );
  await p.keyboard.insertText(text);
}
try {
  await page.goto(url);
  await ready();
  await page.locator("#run").click();
  await page.locator(".result-value").waitFor();
  assert.equal(
    await page.locator(".result-value").innerText(),
    examples[0].result,
  );
  await page.locator("#tab-types").click();
  assert.equal(await page.locator("#types .binding-row").count(), 3);
  await page.locator("#share").click();
  await page.locator("#share-dialog[open]").waitFor();
  const sharedUrl = await page.locator("#share-link").inputValue();
  assert.equal(
    await sourceFromHash(new URL(sharedUrl).hash),
    examples[0].source,
  );
  await page.locator("#share-dialog .dialog-close").click();
  const downloadEvent = page.waitForEvent("download");
  await page.locator("#download").click();
  assert.equal((await downloadEvent).suggestedFilename(), "polymorphism.fhm");
  await page.locator("#divider").focus();
  await page.keyboard.press("ArrowLeft");
  assert.equal(
    await page.locator("#divider").getAttribute("aria-valuenow"),
    "58",
  );
  await page.locator("#tab-types").focus();
  await page.keyboard.press("ArrowRight");
  assert.equal(
    await page.locator("#tab-problems").getAttribute("aria-selected"),
    "true",
  );
  const edited = "-- a saved draft\nlet answer = 42\nanswer\n";
  await program(page, edited);
  await ready();
  await page.waitForFunction(() =>
    document.getElementById("draft-status").textContent.includes("Saved"),
  );
  await page.reload();
  await ready();
  assert.equal(
    await page.evaluate(
      () => JSON.parse(localStorage.getItem("fhm.draft")).source,
    ),
    edited,
  );
  await page.goto(sharedUrl);
  await ready();
  assert.equal(
    await page.evaluate(
      () => JSON.parse(localStorage.getItem("fhm.draft")).source,
    ),
    examples[0].source,
  );
  await page.locator("#examples").click();
  await page
    .locator(".example-option")
    .filter({ hasText: "When types don't fit" })
    .click();
  await page.locator("#status.err").waitFor();
  await page.locator("#tab-problems").click();
  assert.ok(await page.locator(".problem-item").count());
  await page.locator(".problem-item").first().click();
  await page.locator("#examples").click();
  await page
    .locator(".example-option")
    .filter({ hasText: "Your previous program" })
    .click();
  await ready();
  await page.locator("#theme").click();
  assert.equal(await page.locator("html").getAttribute("data-theme"), "dark");
  if (process.env.FHM_SCREENSHOTS)
    await page.screenshot({ path: `${process.env.FHM_SCREENSHOTS}-dark.png` });
  await page.locator("#theme").click();
  await page.locator("#run").click();
  await page.locator(".result-value").waitFor();
  if (process.env.FHM_SCREENSHOTS)
    await page.screenshot({ path: `${process.env.FHM_SCREENSHOTS}-light.png` });
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
  assert.ok(await page.locator("#run").isVisible());
  if (process.env.FHM_SCREENSHOTS)
    await page.screenshot({
      path: `${process.env.FHM_SCREENSHOTS}-mobile.png`,
    });
  const fresh = await browser.newContext();
  const other = await fresh.newPage();
  await other.goto(sharedUrl);
  await ready(other);
  await other.locator("#run").click();
  await other.locator(".result-value").waitFor();
  assert.equal(
    await other.locator(".result-value").innerText(),
    examples[0].result,
  );
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
  assert.match(
    await blocked.locator("#draft-status").innerText(),
    /Session only/,
  );
  await blocked.locator("#share").click();
  await blocked.locator("#share-dialog[open]").waitFor();
  await blocked.locator("#copy-link").click();
  assert.match(await blocked.locator("#toast").innerText(), /manually/);
  await unavailable.close();
  assert.deepEqual(errors, []);
  console.log(
    JSON.stringify({
      ok: true,
      url,
      checks: [
        "evaluation",
        "inferred types",
        "snapshot sharing",
        "download",
        "keyboard resize & tabs",
        "draft restore",
        "shared link precedence",
        "problem navigation",
        "previous program",
        "theme",
        "mobile layout",
        "fresh-browser share",
        "blocked storage & clipboard fallback",
      ],
    }),
  );
} finally {
  await browser.close();
}
