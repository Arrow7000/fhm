import * as monaco from "monaco-editor/esm/vs/editor/edcore.main.js";
import "monaco-editor/min/vs/editor/editor.main.css";
import "@fontsource/ibm-plex-mono/latin-400.css";
import "@fontsource/ibm-plex-mono/latin-500.css";
import "./style.css";
import editorWorker from "monaco-editor/esm/vs/editor/editor.worker?worker";
import {
  normalizePayload,
  resolveHover,
  hoverMarkdown,
  diagnosticsToMarkers,
} from "@fhm/editor-core";
import langConfig from "../../vscode/language-configuration.json";
import { examples, exampleFromId } from "./examples.mjs";
import { shareUrl, sourceFromHash } from "./share.mjs";

self.MonacoEnvironment = { getWorker: () => new editorWorker() };
const $ = (id) => document.getElementById(id);
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
      return true;
    } catch {
      return false;
    }
  },
};
function node(tag, className, text) {
  const element = document.createElement(tag);
  if (className) element.className = className;
  if (text !== undefined) element.textContent = text;
  return element;
}
let editor,
  ranged = [],
  currentId = "polymorphism",
  title = examples[0].title;
let diagnoseTimer,
  diagnoseAbort,
  saveTimer,
  toastTimer,
  runSource,
  copyValue = "";
let running = false;
function toast(message) {
  $("toast").textContent = message;
  $("toast").hidden = false;
  clearTimeout(toastTimer);
  toastTimer = setTimeout(() => {
    $("toast").hidden = true;
  }, 4000);
}
function status(text, kind = "") {
  $("status").textContent = text;
  $("status").className = `status ${kind}`;
}
function empty(target, heading, message, symbol = "") {
  const box = node("div", "empty-state");
  if (symbol) box.append(node("span", "empty-symbol", symbol));
  box.append(node("h2", "", heading), node("p", "", message));
  target.replaceChildren(box);
  return box;
}
function tab(name) {
  for (const button of document.querySelectorAll("[data-tab]")) {
    const selected = button.dataset.tab === name;
    button.setAttribute("aria-selected", String(selected));
    button.tabIndex = selected ? 0 : -1;
    $(`panel-${button.dataset.tab}`).hidden = !selected;
  }
}
function metadata() {
  $("program-title").textContent = title;
  $("filename").textContent = `${currentId || "program"}.fhm`;
}
function save() {
  const saved = storage.set("draft", {
    source: editor.getValue(),
    id: currentId,
    title,
  });
  $("draft-status").textContent = saved
    ? "Saved in this browser"
    : "Session only · storage unavailable";
}
function remember() {
  storage.set("previous", { source: editor.getValue(), id: currentId, title });
}
function replaceProgram(program) {
  remember();
  currentId = program.id || "";
  title = program.title || "Untitled program";
  editor.pushUndoStop();
  editor.executeEdits("load-program", [
    { range: editor.getModel().getFullModelRange(), text: program.source },
  ]);
  editor.pushUndoStop();
  editor.setPosition({ lineNumber: 1, column: 1 });
  metadata();
  save();
  editor.focus();
  runSource = undefined;
  $("copy-result").hidden = true;
  initialOutput();
  $("result-status").textContent = "Ready when you are.";
}
function initialOutput() {
  const box = empty(
    $("output"),
    "A small experiment?",
    "Edit the program on the left, then run it. Types are checked as you write; hover over a name to take a closer look.",
    "λ",
  );
  const action = node("button", "inline-run", "Run this program →");
  action.onclick = runProgram;
  box.append(action);
}
function jump(line, column = 1) {
  editor.setPosition({ lineNumber: line, column });
  editor.revealLineInCenter(line);
  editor.focus();
}
async function post(url, source, controller, timeout = 45000) {
  const timer = setTimeout(
    () =>
      controller.abort(
        new Error("The compiler took too long. Please try again."),
      ),
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
      throw new Error(
        response.status === 503
          ? "The compiler is busy. Try again in a moment."
          : payload.error || "Couldn't reach the compiler.",
      );
    return payload;
  } finally {
    clearTimeout(timer);
  }
}
function showTypes(raw, source) {
  const lines = source.split("\n");
  const symbols = (raw.symbols || []).filter(
    (s) =>
      s.endCol > s.startCol &&
      ((s.kind === "val" &&
        /\b(?:let|and)\s+(?:\(\s*)?$/.test(
          (lines[s.startLine - 1] || "").slice(0, s.startCol - 1),
        )) ||
        s.kind === "type"),
  );
  const seen = new Set();
  const bindings = symbols.filter((s) => {
    const key = `${s.startLine}:${s.startCol}`;
    if (seen.has(key)) return false;
    seen.add(key);
    return true;
  });
  $("type-count").textContent = bindings.length || "";
  $("types").replaceChildren(node("p", "section-caption", "INFERRED TYPES"));
  for (const binding of bindings) {
    const row = node("div", "binding-row");
    const name = node("button", "binding-location", binding.name);
    name.title = `Go to line ${binding.startLine}`;
    name.onclick = () => jump(binding.startLine, binding.startCol);
    row.append(name, node("span", "binding-type", binding.type));
    $("types").append(row);
  }
  if (raw.programTy) {
    const expression = node("div", "expression-type");
    expression.append(
      node("p", "section-caption", "FINAL EXPRESSION"),
      node("code", "", raw.programTy),
    );
    $("types").append(expression);
  } else if (!bindings.length)
    empty(
      $("types"),
      "Types appear here.",
      "Finish a valid definition to see its inferred type.",
    );
}
async function diagnose() {
  diagnoseAbort?.abort();
  const controller = new AbortController();
  diagnoseAbort = controller;
  const model = editor.getModel(),
    version = model.getVersionId(),
    source = model.getValue();
  status("Checking types…", "busy");
  const wake = setTimeout(() => {
    if (!controller.signal.aborted)
      status("Waiting for compiler · free hosting can take a moment…", "busy");
  }, 4000);
  try {
    const raw = await post("/api/diagnose", source, controller);
    if (version !== model.getVersionId() || controller.signal.aborted) return;
    const normalized = normalizePayload(raw);
    ranged = normalized.ranged;
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
    $("problem-count").textContent = markers.length || "";
    $("problem-count").classList.toggle("error-count", !!markers.length);
    $("problems").replaceChildren();
    if (!markers.length)
      empty(
        $("problems"),
        "Nothing to fix.",
        "Your program passes the type checker.",
        "✓",
      );
    for (const marker of markers) {
      const button = node("button", "problem-item");
      button.append(
        node(
          "span",
          "problem-location",
          `Line ${marker.startLineNumber}, column ${marker.startColumn}`,
        ),
        node("span", "problem-message", marker.message),
      );
      button.onclick = () => jump(marker.startLineNumber, marker.startColumn);
      $("problems").append(button);
    }
    showTypes(raw, source);
    status(
      markers.length
        ? `${markers.length} problem${markers.length === 1 ? "" : "s"}`
        : "Types checked",
      markers.length ? "err" : "ok",
    );
  } catch (error) {
    if (
      version !== model.getVersionId() ||
      (controller.signal.aborted &&
        !controller.signal.reason?.message?.includes("too long"))
    )
      return;
    status("Compiler unavailable · edit or run to retry", "err");
    empty(
      $("problems"),
      "Couldn't check this yet.",
      error.message || "Check your connection, then try again.",
    );
  } finally {
    clearTimeout(wake);
  }
}
async function runProgram() {
  if (running) return;
  running = true;
  $("run").disabled = true;
  $("run-label").textContent = "Running…";
  tab("result");
  const source = editor.getValue();
  runSource = source;
  $("copy-result").hidden = true;
  $("result-status").textContent = "Running…";
  const waiting = setTimeout(() => {
    $("result-status").textContent =
      "Waiting for compiler · the free server may be waking up…";
  }, 4000);
  empty(
    $("output"),
    "Evaluating…",
    "Checking the program, then evaluating its final expression.",
  );
  try {
    const payload = await post("/api/run", source, new AbortController());
    $("output").replaceChildren();
    if (payload.ok === false) {
      $("output").append(
        node("h2", "error-heading", "This program couldn't run."),
        node(
          "pre",
          "error-message",
          payload.message || payload.error || JSON.stringify(payload),
        ),
      );
      const action = node(
        "button",
        "outlined-button error-actions",
        "Show problems →",
      );
      action.onclick = () => tab("problems");
      $("output").append(action);
    } else {
      copyValue = String(payload.result ?? "");
      const block = node("div", "result-block");
      block.append(
        node("p", "result-eyebrow", "RESULT"),
        node(
          "pre",
          `result-value${copyValue.length > 70 ? " long" : ""}`,
          copyValue,
        ),
        node("div", "result-type", payload.programTy || ""),
      );
      $("output").append(block);
      const timings = payload.timings || {};
      $("output").append(
        node(
          "div",
          "result-meta",
          `Checked & evaluated in ${((Number(timings.checkNs || 0) + Number(timings.evalNs || 0)) / 1e6).toFixed(2)} ms`,
        ),
      );
      if (payload.bindings?.length) {
        const bindings = node("div", "result-bindings");
        bindings.append(node("p", "section-caption", "DEFINITIONS"));
        for (const binding of payload.bindings) {
          const row = node("div", "binding-row");
          row.append(
            node("span", "binding-name", binding.name),
            node("span", "binding-type", binding.type),
          );
          bindings.append(row);
        }
        $("output").append(bindings);
      }
      $("copy-result").hidden = false;
    }
    $("result-status").textContent =
      source === editor.getValue()
        ? payload.ok === false
          ? "Not evaluated · see the error above"
          : "Evaluation complete"
        : "Previous run · program has changed";
  } catch (error) {
    empty(
      $("output"),
      "Couldn't run this yet.",
      error.message || "Check your connection, then try again.",
    );
    $("result-status").textContent = "Run again to retry";
  } finally {
    clearTimeout(waiting);
    running = false;
    $("run").disabled = false;
    $("run-label").textContent = "Run";
  }
}
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
function themes() {
  for (const dark of [false, true]) {
    const colors = dark
      ? ["a49f92", "e48b65", "d9b87b", "a6bc8f", "93b7bd"]
      : ["8d887a", "ad482b", "8b682a", "526744", "346c79"];
    monaco.editor.defineTheme(`fhm-${dark ? "dark" : "light"}`, {
      base: dark ? "vs-dark" : "vs",
      inherit: true,
      rules: [
        ...[
          ["comment", 0],
          ["keyword", 1],
          ["storage", 1],
          ["entity.name.type", 2],
          ["entity.name.function", 4],
          ["constant", 2],
          ["string", 3],
        ].map(([token, i]) => ({ token, foreground: colors[i] })),
        { token: "variable", foreground: dark ? "e7e2d5" : "302e29" },
        { token: "punctuation", foreground: dark ? "a49f92" : "78756c" },
      ],
      colors: {
        "editor.background": dark ? "#24231f" : "#faf8f3",
        "editor.foreground": dark ? "#e7e2d5" : "#302e29",
        "editorLineNumber.foreground": dark ? "#797568" : "#b2ad9f",
        "editorLineNumber.activeForeground": dark ? "#d2caba" : "#78756c",
        "editor.selectionBackground": dark ? "#554939" : "#e8dcc6",
        "editor.lineHighlightBackground": dark ? "#2b2923" : "#f3efe5",
        "editorCursor.foreground": dark ? "#e48b65" : "#ad482b",
      },
    });
  }
}
function theme(value) {
  document.documentElement.dataset.theme = value;
  monaco.editor.setTheme(`fhm-${value}`);
  storage.set("theme", value);
  const label = `Switch to ${value === "dark" ? "light" : "dark"} theme`;
  $("theme").setAttribute("aria-label", label);
  $("theme").title = label;
  document.querySelector('meta[name="theme-color"]').content =
    value === "dark" ? "#24231f" : "#f4f1e9";
}
function showExamples() {
  $("example-list").replaceChildren();
  const previous = storage.get("previous");
  const options = [
    ...examples,
    ...(previous?.source !== undefined
      ? [
          {
            ...previous,
            title: "Your previous program",
            description:
              "Go back to the program you had before loading an example.",
            previous: true,
          },
        ]
      : []),
  ];
  options.forEach((example, i) => {
    const button = node("button", "example-option");
    const text = node("span");
    text.append(
      node("strong", "", example.title),
      node("span", "example-description", example.description),
    );
    button.append(
      node(
        "span",
        "example-number",
        example.previous ? "↶" : String(i + 1).padStart(2, "0"),
      ),
      text,
      node(
        "span",
        "example-current",
        !example.previous && currentId === example.id ? "✓" : "",
      ),
    );
    button.onclick = () => {
      $("examples-dialog").close();
      replaceProgram(example.previous ? previous : example);
    };
    $("example-list").append(button);
  });
  $("examples-dialog").showModal();
}
async function share() {
  try {
    const url = await shareUrl(editor.getValue(), location.href);
    $("share-link").value = url;
    $("share-note").textContent =
      url.length > 8000
        ? "This is a long link; some messaging apps may truncate it. Download the file if sharing fails."
        : "Code lives in the link, not a sharing database. Anyone with the link can open their own copy.";
    if (!$("share-dialog").open) $("share-dialog").showModal();
    $("share-link").select();
  } catch (error) {
    toast(error.message);
  }
}
async function copy(text, input) {
  try {
    await navigator.clipboard.writeText(text);
    toast("Copied.");
  } catch {
    if (input) {
      input.focus();
      input.select();
      toast("Select and copy the link manually.");
    } else toast("Clipboard unavailable. Select the result to copy it.");
  }
}
function splitter() {
  const divider = $("divider"),
    workspace = $("workspace"),
    mobile = matchMedia("(max-width: 760px)");
  let size = storage.get("split") || 60;
  function set(value) {
    size = Math.max(30, Math.min(75, value));
    workspace.style.setProperty("--editor-size", `${size}%`);
    divider.setAttribute("aria-valuenow", String(Math.round(size)));
  }
  function orientation() {
    divider.setAttribute(
      "aria-orientation",
      mobile.matches ? "horizontal" : "vertical",
    );
    set(size);
  }
  orientation();
  mobile.addEventListener("change", orientation);
  divider.onpointerdown = (event) => {
    divider.setPointerCapture(event.pointerId);
    divider.classList.add("dragging");
  };
  divider.onpointermove = (event) => {
    if (!divider.hasPointerCapture(event.pointerId)) return;
    const rect = workspace.getBoundingClientRect();
    set(
      mobile.matches
        ? ((event.clientY - rect.top) / rect.height) * 100
        : ((event.clientX - rect.left) / rect.width) * 100,
    );
  };
  divider.onpointerup = (event) => {
    divider.releasePointerCapture(event.pointerId);
    divider.classList.remove("dragging");
    storage.set("split", size);
  };
  divider.onlostpointercapture = () => divider.classList.remove("dragging");
  divider.onkeydown = (event) => {
    const negative = mobile.matches ? "ArrowUp" : "ArrowLeft",
      positive = mobile.matches ? "ArrowDown" : "ArrowRight";
    if (![negative, positive, "Home", "End"].includes(event.key)) return;
    event.preventDefault();
    set(
      event.key === "Home"
        ? 30
        : event.key === "End"
          ? 75
          : size + (event.key === negative ? -2 : 2),
    );
    storage.set("split", size);
  };
}
async function main() {
  let source = examples[0].source,
    notice;
  const draft = storage.get("draft");
  if (typeof draft?.source === "string") {
    source = draft.source;
    currentId = draft.id || "";
    title = draft.title || "Your program";
  }
  try {
    const shared = await sourceFromHash(location.hash);
    if (shared !== null) {
      if (draft) storage.set("previous", draft);
      source = shared;
      currentId = "";
      title = "Shared program";
    } else if (location.hash.startsWith("#example=")) {
      const example = exampleFromId(location.hash.slice(9));
      if (example) {
        source = example.source;
        currentId = example.id;
        title = example.title;
      }
    }
  } catch (error) {
    notice = `Couldn't open shared program: ${error.message}`;
  }
  monaco.languages.register({ id: "fhm", extensions: [".fhm"] });
  monaco.languages.setLanguageConfiguration("fhm", langConfig);
  themes();
  editor = monaco.editor.create($("editor"), {
    value: source,
    language: "fhm",
    theme: "fhm-light",
    automaticLayout: true,
    minimap: { enabled: false },
    fontSize: 14,
    lineHeight: 25,
    fontFamily: '"IBM Plex Mono", monospace',
    tabSize: 2,
    scrollBeyondLastLine: false,
    renderLineHighlight: "line",
    padding: { top: 22, bottom: 22 },
    overviewRulerBorder: false,
    hideCursorInOverviewRuler: true,
    wordWrap: "on",
    folding: true,
    lineNumbersMinChars: 3,
    glyphMargin: false,
  });
  theme(storage.get("theme") === "dark" ? "dark" : "light");
  metadata();
  initialOutput();
  save();
  void syntax().catch((error) =>
    console.warn("Syntax highlighting unavailable", error),
  );
  monaco.languages.registerHoverProvider("fhm", {
    provideHover(model, position) {
      const hit = resolveHover(
        ranged,
        position.lineNumber - 1,
        position.column - 1,
        model.getLineContent(position.lineNumber),
      );
      if (!hit) return null;
      const line = hit.startLine0 + 1,
        col = hit.startCol0 + 1;
      return {
        range: new monaco.Range(
          line,
          col,
          line,
          Math.max(
            col + 1,
            Math.min(
              col + 128,
              hit.endLine0 === hit.startLine0
                ? hit.endCol0 + 1
                : col + hit.name.length,
            ),
          ),
        ),
        contents: [{ value: hoverMarkdown(hit) }],
      };
    },
  });
  editor.onDidChangeModelContent(() => {
    diagnoseAbort?.abort();
    ranged = [];
    monaco.editor.setModelMarkers(editor.getModel(), "fhm", []);
    $("type-count").textContent = "";
    $("problem-count").textContent = "";
    empty(
      $("types"),
      "Checking types…",
      "Feedback will update when you pause typing.",
    );
    empty(
      $("problems"),
      "Checking…",
      "Feedback will update when you pause typing.",
    );
    if (runSource !== undefined)
      $("result-status").textContent = "Previous run · program has changed";
    if (location.hash)
      history.replaceState(null, "", location.pathname + location.search);
    $("draft-status").textContent = "Saving…";
    clearTimeout(saveTimer);
    saveTimer = setTimeout(save, 250);
    clearTimeout(diagnoseTimer);
    diagnoseTimer = setTimeout(diagnose, 450);
    status("Waiting for edits…");
  });
  editor.onDidChangeCursorPosition(({ position }) => {
    $("cursor").textContent =
      `Ln ${position.lineNumber}, Col ${position.column}`;
  });
  window.addEventListener("pagehide", save);
  let navigation = 0;
  window.addEventListener("hashchange", async () => {
    const generation = ++navigation;
    status("Opening program…", "busy");
    try {
      const shared = await sourceFromHash(location.hash);
      if (generation !== navigation) return;
      const example = location.hash.startsWith("#example=")
        ? exampleFromId(location.hash.slice(9))
        : null;
      if (shared !== null)
        replaceProgram({ source: shared, title: "Shared program" });
      else if (example) replaceProgram(example);
      else void diagnose();
    } catch (error) {
      toast(error.message);
      void diagnose();
    }
  });
  $("run").onclick = runProgram;
  $("examples").onclick = showExamples;
  $("guide").onclick = () => $("guide-dialog").showModal();
  $("share").onclick = share;
  $("theme").onclick = () =>
    theme(document.documentElement.dataset.theme === "dark" ? "light" : "dark");
  $("copy-link").onclick = () => copy($("share-link").value, $("share-link"));
  $("copy-result").onclick = () => copy(copyValue);
  $("new-program").onclick = () =>
    replaceProgram({ source: "", title: "Untitled program" });
  $("download").onclick = () => {
    const url = URL.createObjectURL(
      new Blob([editor.getValue()], { type: "text/plain;charset=utf-8" }),
    );
    const link = node("a");
    link.href = url;
    link.download = `${currentId || "program"}.fhm`;
    link.click();
    setTimeout(() => URL.revokeObjectURL(url), 1000);
  };
  for (const dialog of document.querySelectorAll("dialog")) {
    dialog.querySelector(".dialog-close").onclick = () => dialog.close();
    dialog.addEventListener("click", (event) => {
      const rect = dialog.getBoundingClientRect();
      if (
        event.target === dialog &&
        (event.clientX < rect.left ||
          event.clientX > rect.right ||
          event.clientY < rect.top ||
          event.clientY > rect.bottom)
      )
        dialog.close();
    });
  }
  const tabs = [...document.querySelectorAll("[data-tab]")];
  tabs.forEach((button, i) => {
    button.onclick = () => tab(button.dataset.tab);
    button.onkeydown = (event) => {
      const index =
        event.key === "ArrowRight"
          ? (i + 1) % tabs.length
          : event.key === "ArrowLeft"
            ? (i + tabs.length - 1) % tabs.length
            : event.key === "Home"
              ? 0
              : event.key === "End"
                ? tabs.length - 1
                : -1;
      if (index < 0) return;
      event.preventDefault();
      tab(tabs[index].dataset.tab);
      tabs[index].focus();
    };
  });
  const mac = /Mac|iPhone|iPad/.test(navigator.platform);
  document.querySelectorAll(".shortcut-label").forEach((label) => {
    label.textContent = mac ? "⌘" : "Ctrl";
  });
  document.querySelector(".run-shortcut").textContent = mac ? "⌘ ↵" : "Ctrl ↵";
  window.addEventListener("keydown", (event) => {
    if (
      !(event.metaKey || event.ctrlKey) ||
      document.querySelector("dialog[open]")
    )
      return;
    if (event.key === "Enter") {
      event.preventDefault();
      void runProgram();
    } else if (event.key.toLowerCase() === "s") {
      event.preventDefault();
      void share();
    }
  });
  document.querySelector(".skip-link").onclick = (event) => {
    event.preventDefault();
    editor.focus();
  };
  splitter();
  void diagnose();
  if (notice) toast(notice);
}
main().catch((error) => {
  console.error(error);
  status("Couldn't start the editor. Please reload.", "err");
});
