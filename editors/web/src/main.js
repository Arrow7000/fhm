import * as monaco from "monaco-editor/esm/vs/editor/edcore.main.js";
import "monaco-editor/min/vs/editor/editor.main.css";
import editorWorker from "monaco-editor/esm/vs/editor/editor.worker?worker";
import {
  normalizePayload,
  resolveHover,
  hoverMarkdown,
  diagnosticsToMarkers,
  formatNs,
} from "@fhm/editor-core";
import langConfig from "../../vscode/language-configuration.json";
import { examples, exampleFromId } from "./examples.mjs";
import { hashFor, sourceFromHash } from "./share.mjs";

self.MonacoEnvironment = { getWorker: () => new editorWorker() };
const $ = (id) => document.getElementById(id);
const mac = /Mac|iPhone|iPad/.test(navigator.platform);
const storage = {
  get(key) {
    try {
      return JSON.parse(localStorage.getItem(`fhm.${key}`));
    } catch {
      return null;
    }
  },
  set(key, value) {
    try {
      localStorage.setItem(`fhm.${key}`, JSON.stringify(value));
    } catch {}
  },
};
function node(tag, className, text) {
  const element = document.createElement(tag);
  if (className) element.className = className;
  if (text !== undefined) element.textContent = text;
  return element;
}

let editor;
let ranged = [];
// The example the program was loaded from, if any. While the program is
// unmodified the URL names the example instead of embedding its source.
let currentId = "";
// The latest evaluation, kept (dimmed) while newer edits are being checked.
let lastRun = null;
let lastDiagnosis = null;
let checkTimer, checkAbort, saveTimer, urlTimer, shareTimer;

function status(text, kind = "") {
  $("status").textContent = text;
  $("status").className = `status ${kind}`;
}

function jump(line, column = 1) {
  editor.setPosition({ lineNumber: line, column });
  editor.revealLineInCenterIfOutsideViewport(line);
  editor.focus();
}

// Types are shown with the editor's own highlighting.
async function colorized(text) {
  const span = node("span", "type");
  span.textContent = text;
  try {
    span.innerHTML = (await monaco.editor.colorize(text, "fhm", {})).replace(
      /<br\/?>$/,
      "",
    );
  } catch {}
  return span;
}

/* URL and local draft */

function save() {
  storage.set("draft", { source: editor.getValue(), id: currentId });
}

// The address bar always holds the current program, so it is the share link.
async function syncUrl() {
  clearTimeout(urlTimer);
  const source = editor.getValue();
  const example = exampleFromId(currentId);
  let hash = "";
  try {
    hash =
      example?.source === source
        ? `#example=${example.id}`
        : await hashFor(source);
  } catch {
    // Too large for a link; leave a bare URL rather than a stale program.
  }
  if (source !== editor.getValue()) return false;
  if (location.hash !== hash)
    history.replaceState(null, "", location.pathname + hash);
  return hash !== "";
}

async function share() {
  const label = $("share-label");
  clearTimeout(shareTimer);
  if (!(await syncUrl())) {
    label.textContent = "Too large to link";
    status(
      "This program is over the 128 KiB link limit. Use Download instead.",
      "err",
    );
  } else {
    try {
      await navigator.clipboard.writeText(location.href);
      label.textContent = "Link copied";
    } catch {
      label.textContent = "Link in address bar";
    }
  }
  shareTimer = setTimeout(() => (label.textContent = "Share"), 2000);
}

// Name downloads after the program's contents, so different programs don't
// overwrite each other and the same program always gets the same name.
async function download() {
  const source = editor.getValue();
  let name = "program";
  try {
    const digest = await crypto.subtle.digest(
      "SHA-256",
      new TextEncoder().encode(source),
    );
    const hex = [...new Uint8Array(digest)].map((b) =>
      b.toString(16).padStart(2, "0"),
    );
    name = `program-${hex.join("").slice(0, 7)}`;
  } catch {}
  const url = URL.createObjectURL(
    new Blob([source], { type: "text/plain;charset=utf-8" }),
  );
  const link = node("a");
  link.href = url;
  link.download = `${name}.fhm`;
  link.click();
  setTimeout(() => URL.revokeObjectURL(url), 1000);
}

function replaceProgram(program) {
  const current = editor.getValue();
  if (current !== program.source)
    storage.set("previous", { source: current, id: currentId });
  currentId = program.id || "";
  editor.pushUndoStop();
  editor.executeEdits("load-program", [
    { range: editor.getModel().getFullModelRange(), text: program.source },
  ]);
  editor.pushUndoStop();
  editor.setPosition({ lineNumber: 1, column: 1 });
  editor.setScrollTop(0);
  lastRun = null;
  renderResult();
  save();
  void syncUrl();
  editor.focus();
}

/* Talking to the compiler */

// An idle Render free instance can need a minute to wake. Execution itself is
// still bounded separately by the server's much shorter compiler timeouts.
async function post(url, source, controller, timeout = 90000) {
  const timer = setTimeout(
    () => controller.abort(new Error("The compiler took too long to respond.")),
    timeout,
  );
  try {
    const response = await fetch(url, {
      method: "POST",
      headers: { "Content-Type": "application/json" },
      body: JSON.stringify({ source }),
      signal: controller.signal,
    });
    const payload = await response.json();
    if (!response.ok)
      throw Object.assign(
        new Error(
          response.status === 503
            ? "The compiler is busy."
            : payload.error || `Compiler request failed (${response.status}).`,
        ),
        { status: response.status },
      );
    return payload;
  } finally {
    clearTimeout(timer);
  }
}

const WAKING =
  "Waiting for the compiler (the free server can take up to a minute to start)…";

// Top-level definition sites: a name directly after `let`/`and` whose scope
// runs to the end of the program. Local `let … in` bindings end sooner.
function topLevelBindings(symbols, source) {
  const lines = source.split("\n");
  const end = (s) => [s.scopeEndLine, s.scopeEndCol];
  let last = [0, 0];
  for (const s of symbols) {
    const [l, c] = end(s);
    if (l > last[0] || (l === last[0] && c > last[1])) last = [l, c];
  }
  const seen = new Set();
  return symbols
    .filter((s) => {
      if (s.kind !== "val" || s.endCol <= s.startCol) return false;
      if (s.scopeEndLine !== last[0] || s.scopeEndCol !== last[1]) return false;
      const before = (lines[s.startLine - 1] || "").slice(0, s.startCol - 1);
      if (!/\b(?:let|and)\s+(?:\(\s*)?$/.test(before)) return false;
      const key = `${s.startLine}:${s.startCol}`;
      if (seen.has(key)) return false;
      seen.add(key);
      return true;
    })
    .sort((a, b) => a.startLine - b.startLine || a.startCol - b.startCol);
}

async function renderTypes(raw, source) {
  const bindings = topLevelBindings(raw.symbols || [], source);
  const block = $("types");
  if (!bindings.length && !raw.programTy) return block.replaceChildren();
  const grid = node("div", "bindings");
  for (const b of bindings) {
    const name = node("button", "name", b.name);
    name.title = `Line ${b.startLine}`;
    name.onclick = () => jump(b.startLine, b.startCol);
    grid.append(name, node("span", "colon", ":"), await colorized(b.type));
  }
  if (raw.programTy) {
    const name = node("span", "name", "<program>");
    grid.append(
      name,
      node("span", "colon", ":"),
      await colorized(raw.programTy),
    );
  }
  block.replaceChildren(node("h2", "heading", "Types"), grid);
}

function renderProblems(markers) {
  const block = $("problems");
  block.hidden = !markers.length;
  block.replaceChildren();
  if (!markers.length) return;
  block.append(
    node(
      "h2",
      "heading",
      markers.length === 1 ? "1 problem" : `${markers.length} problems`,
    ),
  );
  for (const m of markers) {
    const item = node("button", "problem");
    item.append(
      node("span", "loc", `${m.startLineNumber}:${m.startColumn}`),
      node("span", "msg", m.message),
    );
    item.onclick = () => jump(m.startLineNumber, m.startColumn);
    block.append(item);
  }
}

// Check, and if that succeeds evaluate, the current program. Runs after every
// edit; evaluation is cut off by a step and time budget on the server.
async function check() {
  clearTimeout(checkTimer);
  checkAbort?.abort();
  const controller = new AbortController();
  checkAbort = controller;
  const model = editor.getModel();
  const version = model.getVersionId();
  const source = model.getValue();
  status("Checking…");
  const wake = setTimeout(() => {
    if (!controller.signal.aborted) status(WAKING);
  }, 4000);
  try {
    let response;
    try {
      response = await post("/api/check", source, controller);
    } catch (error) {
      // Another visitor's request may hold the compiler for a moment.
      if (error.status !== 503) throw error;
      await new Promise((resolve) => setTimeout(resolve, 750));
      if (controller.signal.aborted) return;
      response = await post("/api/check", source, controller);
    }
    if (version !== model.getVersionId() || controller.signal.aborted) return;
    const { diagnose: raw, run } = response;
    const normalized = normalizePayload(raw);
    ranged = normalized.ranged;
    lastDiagnosis = { raw, source };
    const markers = diagnosticsToMarkers(normalized.diagnostics).map((m) => ({
      severity:
        m.severity === "warning"
          ? monaco.MarkerSeverity.Warning
          : monaco.MarkerSeverity.Error,
      message: m.message,
      startLineNumber: m.line0 + 1,
      startColumn: m.col0 + 1,
      endLineNumber: m.endLine0 + 1,
      endColumn: m.endCol0 + 1,
    }));
    monaco.editor.setModelMarkers(model, "fhm", markers);
    renderProblems(markers);
    await renderTypes(raw, source);
    if (run) lastRun = { source, payload: run };
    renderResult();
    status(
      markers.length
        ? `${markers.length} problem${markers.length === 1 ? "" : "s"}`
        : "No problems",
      markers.length ? "err" : "ok",
    );
  } catch (error) {
    if (version !== model.getVersionId()) return;
    if (
      controller.signal.aborted &&
      !/too long/.test(controller.signal.reason?.message)
    )
      return;
    status(
      `${error.message || "Couldn't reach the compiler."} Edit to retry.`,
      "err",
    );
  } finally {
    clearTimeout(wake);
  }
}

// Evaluation that ran out of its live budget can be retried without it.
async function runUnlimited(button) {
  const source = editor.getValue();
  button.disabled = true;
  button.textContent = "Running…";
  try {
    const payload = await post("/api/run", source, new AbortController());
    lastRun = { source, payload };
  } catch (error) {
    lastRun = {
      source,
      payload: {
        ok: false,
        stage: "eval",
        message:
          error.status === 504
            ? "still running after 20 s, so it was stopped"
            : error.message,
      },
    };
  }
  if (source === editor.getValue()) renderResult();
}

const steps = (n) => `${n.toLocaleString("en")} step${n === 1 ? "" : "s"}`;

function renderResult() {
  const block = $("result");
  block.replaceChildren();
  block.classList.remove("stale");
  if (!lastRun) return;
  const { payload, source } = lastRun;
  const heading = node("h2", "heading", "Result");
  block.append(heading);
  if (source !== editor.getValue()) {
    block.classList.add("stale");
    heading.textContent = "Result (of an earlier version)";
  }
  if (payload.ok === false) {
    const limited = payload.limit === "time" || payload.steps !== undefined;
    if (limited) {
      const stop =
        payload.steps !== undefined
          ? `Stopped after ${steps(payload.steps)}.`
          : `Stopped after ${payload.message.replace("stopped after ", "")}.`;
      const note = node("p", "note", `${stop} The program may not terminate. `);
      const button = node(
        "button",
        "link-button inline",
        "Run without a limit",
      );
      button.onclick = () => runUnlimited(button);
      note.append(button);
      block.append(note);
      return;
    }
    // Positions are listed under problems, from the more precise diagnose pass.
    const box = node("div", "run-error");
    box.append(
      node(
        "pre",
        "",
        `Not run: ${payload.message || payload.error || "failed"}`,
      ),
    );
    block.append(box);
    return;
  }
  block.append(node("pre", "result-value", String(payload.result ?? "")));
  const t = payload.timings || {};
  if (typeof t.checkNs === "number" && typeof t.evalNs === "number")
    block.append(
      node(
        "p",
        "note",
        `Checked in ${formatNs(t.checkNs)}, evaluated in ${formatNs(t.evalNs)}` +
          (typeof payload.steps === "number"
            ? ` (${steps(payload.steps)})`
            : ""),
      ),
    );
}

/* Editor setup */

async function syntax() {
  const [onig, tm, wasm, grammar] = await Promise.all([
    import("vscode-oniguruma"),
    import("vscode-textmate"),
    import("vscode-oniguruma/release/onig.wasm?url"),
    import("../../vscode/syntaxes/fhm.tmLanguage.json"),
  ]);
  await onig.loadWASM(await fetch(wasm.default));
  const registry = new tm.Registry({
    onigLib: Promise.resolve({
      createOnigScanner: (p) => onig.createOnigScanner(p),
      createOnigString: (s) => onig.createOnigString(s),
    }),
    loadGrammar: async (scope) =>
      scope === "source.fhm"
        ? tm.parseRawGrammar(
            JSON.stringify(grammar.default),
            "fhm.tmLanguage.json",
          )
        : null,
  });
  const tokenizer = await registry.loadGrammar("source.fhm");
  class State {
    constructor(stack) {
      this.stack = stack;
    }
    clone() {
      return new State(this.stack);
    }
    equals(other) {
      return other instanceof State && this.stack.equals(other.stack);
    }
  }
  monaco.languages.setTokensProvider("fhm", {
    getInitialState: () => new State(tm.INITIAL),
    tokenize(line, state) {
      const result = tokenizer.tokenizeLine(line, state.stack);
      return {
        tokens: result.tokens.map((t) => ({
          startIndex: t.startIndex,
          scopes: t.scopes.at(-1) || "",
        })),
        endState: new State(result.ruleStack),
      };
    },
  });
}

function defineThemes() {
  const palettes = {
    light: {
      base: "vs",
      bg: "#ffffff",
      fg: "#1f2328",
      muted: "#59636e",
      line: "#f6f8fa",
      numbers: "#8c959f",
      select: "#cfe3ff",
      cursor: "#1f2328",
      keyword: "cf222e",
      type: "953800",
      constant: "0550ae",
      string: "0a3069",
    },
    dark: {
      base: "vs-dark",
      bg: "#0d1117",
      fg: "#e6edf3",
      muted: "#9198a1",
      line: "#151b23",
      numbers: "#6e7681",
      select: "#264f78",
      cursor: "#e6edf3",
      keyword: "ff7b72",
      type: "ffa657",
      constant: "79c0ff",
      string: "a5d6ff",
    },
  };
  for (const [name, p] of Object.entries(palettes))
    monaco.editor.defineTheme(`fhm-${name}`, {
      base: p.base,
      inherit: true,
      rules: [
        { token: "comment", foreground: p.muted.slice(1) },
        { token: "keyword", foreground: p.keyword },
        { token: "storage", foreground: p.keyword },
        { token: "entity.name.type", foreground: p.type },
        { token: "constant", foreground: p.constant },
        { token: "string", foreground: p.string },
        { token: "variable", foreground: p.fg.slice(1) },
        { token: "punctuation", foreground: p.fg.slice(1) },
      ],
      colors: {
        "editor.background": p.bg,
        "editor.foreground": p.fg,
        "editorLineNumber.foreground": p.numbers,
        "editorLineNumber.activeForeground": p.fg,
        "editor.lineHighlightBackground": p.line,
        "editor.lineHighlightBorder": p.line,
        "editor.selectionBackground": p.select,
        "editorCursor.foreground": p.cursor,
        "editorIndentGuide.background1": p.line,
        "editorWidget.background": p.line,
        "editorHoverWidget.background": p.bg,
      },
    });
}

const darkQuery = matchMedia("(prefers-color-scheme: dark)");
function effectiveTheme() {
  return (
    document.documentElement.dataset.theme ||
    (darkQuery.matches ? "dark" : "light")
  );
}
function applyTheme() {
  monaco.editor.setTheme(`fhm-${effectiveTheme()}`);
}

/* Examples menu */

function examplesMenu() {
  const button = $("examples");
  const menu = $("examples-menu");
  const items = () => [...menu.querySelectorAll("button")];
  function close(focus = false) {
    menu.hidden = true;
    button.setAttribute("aria-expanded", "false");
    if (focus) button.focus();
  }
  function item(label, onSelect, checked) {
    const entry = node("button");
    entry.setAttribute(
      "role",
      checked === undefined ? "menuitem" : "menuitemradio",
    );
    if (checked !== undefined)
      entry.setAttribute("aria-checked", String(checked));
    entry.tabIndex = -1;
    entry.textContent = label;
    entry.onclick = () => {
      close();
      onSelect();
    };
    return entry;
  }
  function open() {
    const source = editor.getValue();
    menu.replaceChildren();
    let section;
    for (const example of examples) {
      if (example.section !== section) {
        section = example.section;
        const label = node("div", "menu-section", section);
        label.setAttribute("role", "presentation");
        menu.append(label);
      }
      menu.append(
        item(
          example.title,
          () => replaceProgram(example),
          currentId === example.id && example.source === source,
        ),
      );
    }
    menu.append(
      node("hr"),
      item("Blank program", () => replaceProgram({ source: "" })),
    );
    const previous = storage.get("previous");
    if (typeof previous?.source === "string" && previous.source !== source)
      menu.append(
        item("Restore previous program", () => replaceProgram(previous)),
      );
    menu.hidden = false;
    button.setAttribute("aria-expanded", "true");
    (menu.querySelector('[aria-checked="true"]') || items()[0]).focus();
  }
  button.onclick = () => (menu.hidden ? open() : close());
  menu.onkeydown = (event) => {
    const list = items();
    const i = list.indexOf(document.activeElement);
    const next = {
      ArrowDown: (i + 1) % list.length,
      ArrowUp: (i - 1 + list.length) % list.length,
      Home: 0,
      End: list.length - 1,
    }[event.key];
    if (next !== undefined) {
      event.preventDefault();
      list[next].focus();
    } else if (event.key === "Escape" || event.key === "Tab") {
      event.preventDefault();
      close(true);
    }
  };
  document.addEventListener("pointerdown", (event) => {
    if (!menu.hidden && !event.target.closest(".menu-wrap")) close();
  });
}

/* Resizable split */

function splitter() {
  const divider = $("divider");
  const workspace = $("workspace");
  const narrow = matchMedia("(max-width: 760px)");
  let size = storage.get("split") || 60;
  function set(value) {
    size = Math.max(25, Math.min(80, value));
    workspace.style.setProperty("--editor-size", `${size}%`);
    divider.setAttribute("aria-valuenow", String(Math.round(size)));
  }
  function orientation() {
    divider.setAttribute(
      "aria-orientation",
      narrow.matches ? "horizontal" : "vertical",
    );
    set(size);
  }
  orientation();
  narrow.addEventListener("change", orientation);
  divider.onpointerdown = (event) => {
    divider.setPointerCapture(event.pointerId);
    divider.classList.add("dragging");
  };
  divider.onpointermove = (event) => {
    if (!divider.hasPointerCapture(event.pointerId)) return;
    const rect = workspace.getBoundingClientRect();
    set(
      narrow.matches
        ? ((event.clientY - rect.top) / rect.height) * 100
        : ((event.clientX - rect.left) / rect.width) * 100,
    );
  };
  divider.onpointerup = (event) => {
    divider.releasePointerCapture(event.pointerId);
    storage.set("split", size);
  };
  divider.onlostpointercapture = () => divider.classList.remove("dragging");
  divider.ondblclick = () => {
    set(60);
    storage.set("split", size);
  };
  divider.onkeydown = (event) => {
    const less = narrow.matches ? "ArrowUp" : "ArrowLeft";
    const more = narrow.matches ? "ArrowDown" : "ArrowRight";
    if (![less, more, "Home", "End"].includes(event.key)) return;
    event.preventDefault();
    set(
      event.key === "Home"
        ? 25
        : event.key === "End"
          ? 80
          : size + (event.key === less ? -2 : 2),
    );
    storage.set("split", size);
  };
}

/* Startup */

// What to open: a program in the URL, else this browser's draft, else the
// first example. Opening a link keeps the draft restorable from Examples.
async function initialProgram() {
  const draft = storage.get("draft");
  const hasDraft = typeof draft?.source === "string";
  try {
    const shared = await sourceFromHash(location.hash);
    if (shared !== null) {
      if (hasDraft && draft.source !== shared) storage.set("previous", draft);
      return { source: shared };
    }
  } catch (error) {
    return { ...(hasDraft ? draft : examples[0]), notice: error.message };
  }
  const example = location.hash.startsWith("#example=")
    ? exampleFromId(location.hash.slice(9))
    : null;
  if (example) {
    if (hasDraft && draft.source !== example.source)
      storage.set("previous", draft);
    return example;
  }
  return hasDraft ? draft : examples[0];
}

async function main() {
  const program = await initialProgram();
  currentId = program.id || "";
  monaco.languages.register({ id: "fhm", extensions: [".fhm"] });
  monaco.languages.setLanguageConfiguration("fhm", langConfig);
  defineThemes();
  editor = monaco.editor.create($("editor"), {
    value: program.source,
    language: "fhm",
    theme: `fhm-${effectiveTheme()}`,
    automaticLayout: true,
    minimap: { enabled: false },
    fontFamily: getComputedStyle(document.documentElement).getPropertyValue(
      "--mono",
    ),
    fontSize: 14,
    lineHeight: 21,
    tabSize: 2,
    scrollBeyondLastLine: false,
    padding: { top: 12, bottom: 12 },
    overviewRulerBorder: false,
    hideCursorInOverviewRuler: true,
    renderLineHighlightOnlyWhenFocus: true,
    lineNumbersMinChars: 3,
    glyphMargin: false,
    fixedOverflowWidgets: true,
    occurrencesHighlight: "off",
    "bracketPairColorization.enabled": false,
  });
  const narrow = matchMedia("(max-width: 760px)");
  const wrap = () =>
    editor.updateOptions({ wordWrap: narrow.matches ? "on" : "off" });
  wrap();
  narrow.addEventListener("change", wrap);
  darkQuery.addEventListener("change", applyTheme);
  // Register these inside Monaco too: its insert-line command otherwise eats
  // Cmd/Ctrl+Enter before the page-level shortcut can see the event.
  editor.addAction({
    id: "fhm.check",
    label: "Check and run now",
    keybindings: [monaco.KeyMod.CtrlCmd | monaco.KeyCode.Enter],
    run: check,
  });
  editor.addAction({
    id: "fhm.share",
    label: "Copy link to program",
    keybindings: [monaco.KeyMod.CtrlCmd | monaco.KeyCode.KeyS],
    run: share,
  });
  void syntax()
    .then(() => {
      // Re-render so the output panel picks up highlighting too.
      if (lastDiagnosis?.source === editor.getValue())
        void renderTypes(lastDiagnosis.raw, lastDiagnosis.source);
    })
    .catch((error) => console.warn("Syntax highlighting unavailable", error));
  monaco.languages.registerHoverProvider("fhm", {
    provideHover(model, position) {
      const hit = resolveHover(
        ranged,
        position.lineNumber - 1,
        position.column - 1,
        model.getLineContent(position.lineNumber),
      );
      if (!hit) return null;
      const line = hit.startLine0 + 1;
      const col = hit.startCol0 + 1;
      const endCol =
        hit.endLine0 === hit.startLine0
          ? hit.endCol0 + 1
          : col + hit.name.length;
      return {
        range: new monaco.Range(
          line,
          col,
          line,
          Math.max(col + 1, Math.min(col + 128, endCol)),
        ),
        contents: [{ value: hoverMarkdown(hit) }],
      };
    },
  });

  editor.onDidChangeModelContent(() => {
    checkAbort?.abort();
    ranged = [];
    if (lastRun) renderResult();
    clearTimeout(saveTimer);
    saveTimer = setTimeout(save, 250);
    clearTimeout(urlTimer);
    urlTimer = setTimeout(syncUrl, 400);
    clearTimeout(checkTimer);
    checkTimer = setTimeout(check, 300);
  });
  editor.onDidChangeCursorPosition(({ position }) => {
    $("cursor").textContent =
      `Ln ${position.lineNumber}, Col ${position.column}`;
  });
  window.addEventListener("pagehide", save);
  // Fired when someone pastes a different link into the address bar; our own
  // URL updates use replaceState and don't trigger it.
  window.addEventListener("hashchange", async () => {
    try {
      const shared = await sourceFromHash(location.hash);
      const example = location.hash.startsWith("#example=")
        ? exampleFromId(location.hash.slice(9))
        : null;
      if (shared !== null) replaceProgram({ source: shared });
      else if (example) replaceProgram(example);
    } catch (error) {
      status(error.message, "err");
    }
  });

  $("share").onclick = share;
  $("help").onclick = () => $("help-dialog").showModal();
  $("theme").onclick = () => {
    const next = effectiveTheme() === "dark" ? "light" : "dark";
    document.documentElement.dataset.theme = next;
    storage.set("theme", next);
    applyTheme();
  };
  $("download").onclick = download;
  const dialog = $("help-dialog");
  dialog.querySelector(".dialog-close").onclick = () => dialog.close();
  dialog.addEventListener("click", (event) => {
    if (event.target === dialog) dialog.close();
  });
  for (const kbd of document.querySelectorAll("kbd.shortcut")) {
    const key = kbd.dataset.shortcut;
    kbd.textContent = mac ? `⌘${key === "Enter" ? "↵" : key}` : `Ctrl+${key}`;
  }
  window.addEventListener("keydown", (event) => {
    if (!(event.metaKey || event.ctrlKey) || dialog.open) return;
    if (event.key === "Enter") {
      event.preventDefault();
      void check();
    } else if (event.key.toLowerCase() === "s") {
      event.preventDefault();
      void share();
    }
  });
  examplesMenu();
  splitter();
  renderResult();
  save();
  await syncUrl();
  await check();
  if (program.notice)
    status(`Couldn't open the link: ${program.notice}`, "err");
}

main().catch((error) => {
  console.error(error);
  status("Couldn't start the editor. Please reload.", "err");
});
