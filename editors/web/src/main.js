import * as monaco from "monaco-editor";
import "monaco-editor/min/vs/editor/editor.main.css";
import editorWorker from "monaco-editor/esm/vs/editor/editor.worker?worker";
import {
  normalizePayload,
  resolveHover,
  diagnosticsToMarkers,
  formatRunOutputHtml,
} from "@fhm/editor-core";
import langConfig from "../../vscode/language-configuration.json";

// Monaco workers (Vite)
self.MonacoEnvironment = {
  getWorker() {
    return new editorWorker();
  },
};

/** Monaco token state wrapping a TextMate rule stack. */
class FhmTokenState {
  /**
   * @param {import("vscode-textmate").StateStack} ruleStack
   */
  constructor(ruleStack) {
    this.ruleStack = ruleStack;
  }
  clone() {
    return new FhmTokenState(this.ruleStack);
  }
  /**
   * @param {FhmTokenState} other
   */
  equals(other) {
    if (!other || !(other instanceof FhmTokenState)) return false;
    if (this.ruleStack === other.ruleStack) return true;
    return (
      typeof this.ruleStack?.equals === "function" &&
      this.ruleStack.equals(other.ruleStack)
    );
  }
}

const DEBOUNCE_MS = 300;
const statusEl = document.getElementById("status");
const outputEl = document.getElementById("output");
const runBtn = document.getElementById("run");

/** @type {monaco.editor.IStandaloneCodeEditor} */
let editor;
/** @type {any[]} */
let rangedSymbols = [];
/** @type {ReturnType<typeof setTimeout> | undefined} */
let diagnoseTimer;
/** @type {AbortController | undefined} */
let diagnoseAbort;

function setStatus(text, kind = "") {
  statusEl.textContent = text;
  statusEl.className = `status${kind ? ` ${kind}` : ""}`;
}

/**
 * @param {string} source
 */
async function postJson(url, source, signal) {
  const res = await fetch(url, {
    method: "POST",
    headers: { "Content-Type": "application/json" },
    body: JSON.stringify({ source }),
    signal,
  });
  const data = await res.json().catch(() => ({}));
  if (!res.ok) {
    const msg = data.error || res.statusText || "request failed";
    throw new Error(msg);
  }
  return data;
}

async function loadExample() {
  try {
    const res = await fetch("/api/example");
    if (res.ok) return await res.text();
  } catch {
    /* fall through */
  }
  return `let add : Int -> Int -> Int = \\a b -> a + b\n\nadd 2 40\n`;
}

/**
 * Wire TextMate grammar → Monaco tokens.
 * @param {string} languageId
 */
async function registerFhmTextMate(languageId) {
  const [{ default: onigWasm }, oniguruma, textmate, { default: grammarJson }] =
    await Promise.all([
      import("vscode-oniguruma/release/onig.wasm?url"),
      import("vscode-oniguruma"),
      import("vscode-textmate"),
      import("../../vscode/syntaxes/fhm.tmLanguage.json"),
    ]);
  const { Registry, INITIAL, parseRawGrammar } = textmate;

  await oniguruma.loadWASM(await fetch(onigWasm));

  const registry = new Registry({
    onigLib: Promise.resolve({
      createOnigScanner: (patterns) => oniguruma.createOnigScanner(patterns),
      createOnigString: (s) => oniguruma.createOnigString(s),
    }),
    loadGrammar: async (scopeName) => {
      if (scopeName !== "source.fhm") return null;
      return parseRawGrammar(JSON.stringify(grammarJson), "fhm.tmLanguage.json");
    },
  });

  const grammar = await registry.loadGrammar("source.fhm");
  if (!grammar) throw new Error("failed to load FHM TextMate grammar");

  monaco.languages.setTokensProvider(languageId, {
    getInitialState: () => new FhmTokenState(INITIAL),
    tokenize: (line, state) => {
      const stack =
        state instanceof FhmTokenState ? state.ruleStack : INITIAL;
      const result = grammar.tokenizeLine(line, stack);
      const tokens = result.tokens.map((t) => ({
        startIndex: t.startIndex,
        // Monaco theme rules match against this string (prefix / last scope).
        scopes: t.scopes[t.scopes.length - 1] || "",
      }));
      return {
        tokens,
        endState: new FhmTokenState(result.ruleStack),
      };
    },
  });
}

function applyLanguageConfiguration(languageId) {
  monaco.languages.setLanguageConfiguration(languageId, {
    comments: langConfig.comments,
    brackets: langConfig.brackets,
    autoClosingPairs: langConfig.autoClosingPairs,
    surroundingPairs: langConfig.surroundingPairs,
  });
}

/**
 * Minimal theme rules so TextMate scopes aren't all plain.
 */
function defineTheme() {
  monaco.editor.defineTheme("fhm-dark", {
    base: "vs-dark",
    inherit: true,
    rules: [
      { token: "comment.line.double-dash.fhm", foreground: "6A737D" },
      { token: "comment.block.fhm", foreground: "6A737D" },
      { token: "keyword.control.fhm", foreground: "C678DD" },
      { token: "keyword.other.fhm", foreground: "C678DD" },
      { token: "storage.type.fhm", foreground: "C678DD" },
      { token: "entity.name.type.fhm", foreground: "E5C07B" },
      { token: "entity.name.function.fhm", foreground: "61AFEF" },
      { token: "variable.other.fhm", foreground: "E06C75" },
      { token: "constant.numeric.fhm", foreground: "D19A66" },
      { token: "constant.language.boolean.fhm", foreground: "D19A66" },
      { token: "string.quoted.double.fhm", foreground: "98C379" },
      { token: "string.quoted.single.fhm", foreground: "98C379" },
      { token: "keyword.operator.fhm", foreground: "56B6C2" },
      { token: "punctuation.fhm", foreground: "ABB2BF" },
    ],
    colors: {
      "editor.background": "#0f1115",
      "editor.foreground": "#e7ecf3",
      "editorLineNumber.foreground": "#5c6778",
      "editorCursor.foreground": "#6cb6ff",
      "editor.selectionBackground": "#243044",
    },
  });
}

async function refreshDiagnostics() {
  const model = editor.getModel();
  if (!model) return;

  diagnoseAbort?.abort();
  diagnoseAbort = new AbortController();
  const { signal } = diagnoseAbort;

  setStatus("checking…");
  try {
    const raw = await postJson("/api/diagnose", model.getValue(), signal);
    const { diagnostics, ranged } = normalizePayload(raw);
    rangedSymbols = ranged;

    const markers = diagnosticsToMarkers(diagnostics).map((m) => ({
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
    setStatus(markers.length ? `${markers.length} issue(s)` : "ok", markers.length ? "err" : "ok");
  } catch (err) {
    if (signal.aborted) return;
    setStatus(String(err.message || err), "err");
  }
}

function scheduleDiagnose() {
  clearTimeout(diagnoseTimer);
  diagnoseTimer = setTimeout(() => {
    void refreshDiagnostics();
  }, DEBOUNCE_MS);
}

async function runProgram() {
  const model = editor.getModel();
  if (!model) return;
  runBtn.disabled = true;
  setStatus("running…");
  outputEl.textContent = "";
  try {
    const payload = await postJson("/api/run", model.getValue());
    outputEl.innerHTML = formatRunOutputHtml(payload);
    if (payload && payload.ok === false) {
      outputEl.classList.add("err");
      setStatus("failed", "err");
    } else {
      outputEl.classList.remove("err");
      setStatus("ok", "ok");
    }
  } catch (err) {
    outputEl.classList.add("err");
    outputEl.textContent = String(err.message || err);
    setStatus("error", "err");
  } finally {
    runBtn.disabled = false;
  }
}

async function main() {
  setStatus("loading…");
  monaco.languages.register({ id: "fhm", extensions: [".fhm"] });
  applyLanguageConfiguration("fhm");
  defineTheme();

  editor = monaco.editor.create(document.getElementById("editor"), {
    value: "",
    language: "fhm",
    theme: "fhm-dark",
    automaticLayout: true,
    minimap: { enabled: false },
    fontSize: 14,
    fontFamily: "IBM Plex Mono, SF Mono, ui-monospace, Menlo, monospace",
    tabSize: 2,
    scrollBeyondLastLine: false,
    renderLineHighlight: "line",
  });

  void registerFhmTextMate("fhm").catch((err) => {
    console.warn("[fhm] TextMate setup failed; editor still works", err);
  });

  const example = await loadExample();
  editor.setValue(example);

  monaco.languages.registerHoverProvider("fhm", {
    provideHover(model, position) {
      try {
        const lineText = model.getLineContent(position.lineNumber);
        const hit = resolveHover(
          rangedSymbols,
          position.lineNumber - 1,
          position.column - 1,
          lineText
        );
        if (!hit) return null;

        const startLine = hit.startLine0 + 1;
        const startCol = hit.startCol0 + 1;
        let endLine = hit.endLine0 + 1;
        let endCol = hit.endCol0 + 1;
        // Guard inverted / empty ranges (Monaco thrash).
        if (
          endLine < startLine ||
          (endLine === startLine && endCol <= startCol)
        ) {
          endLine = startLine;
          endCol = startCol + Math.max(1, hit.name?.length ?? 1);
        }
        // Never return a multi-line or huge highlight from hover.
        if (endLine !== startLine || endCol - startCol > 128) {
          endLine = startLine;
          endCol = startCol + Math.max(1, hit.name?.length ?? 1);
        }

        const kind = String(hit.kind || "val").replace(/[`*]/g, "");
        const name = String(hit.name || "?").replace(/[`*]/g, "");
        const ty = String(hit.type || "?").replace(/`/g, "'");

        return {
          range: new monaco.Range(startLine, startCol, endLine, endCol),
          contents: [
            {
              value: `\`${kind}\` **${name}** : \`${ty}\``,
            },
          ],
        };
      } catch (err) {
        console.warn("[fhm] hover failed", err);
        return null;
      }
    },
  });

  editor.onDidChangeModelContent(() => scheduleDiagnose());
  runBtn.addEventListener("click", () => void runProgram());
  window.addEventListener("keydown", (e) => {
    if ((e.metaKey || e.ctrlKey) && e.key === "Enter") {
      e.preventDefault();
      void runProgram();
    }
  });

  setStatus("ready");
  scheduleDiagnose();
}

main().catch((err) => {
  console.error("[fhm] failed to start playground", err);
  setStatus(String(err.message || err), "err");
});
