//@ts-check
"use strict";

/**
 * Shared FHM editor core — diagnose payload + hover/span helpers.
 * Used by the VS Code extension and the web playground.
 *
 * Diagnose spans are 1-based half-open (lexer / Span.contains).
 * Editor positions passed in are 0-based (VS Code / Monaco).
 */

// Kept for tests / exporters. Prefer `identAtColumn` (manual scan) — never
// `RegExp.exec` with `/gu` in a loop (lastIndex does not advance → hangs).
const IDENT_RE = /[A-Za-z_🎉-💫][A-Za-z0-9_🎉-💫]*/gu;

/** Max half-open columns for a hover highlight (guards pathological spans). */
const MAX_HOVER_SPAN_COLS = 128;

/** @type {WeakMap<any[], Map<string, any[]>>} */
const rangedByNameCache = new WeakMap();

/**
 * Lazily index ranged symbols by name (WeakMap — invalidated when array is replaced).
 * @param {any[]} ranged
 * @returns {Map<string, any[]>}
 */
function rangedByName(ranged) {
  let idx = rangedByNameCache.get(ranged);
  if (!idx) {
    idx = new Map();
    for (const s of ranged) {
      if (typeof s.name !== "string") continue;
      const bucket = idx.get(s.name);
      if (bucket) bucket.push(s);
      else idx.set(s.name, [s]);
    }
    rangedByNameCache.set(ranged, idx);
  }
  return idx;
}

/**
 * Normalize optional scope fields; missing scope falls back to def span (v2).
 * @param {any} sym
 */
function withScope(sym) {
  const hasScope =
    typeof sym.scopeStartLine === "number" &&
    typeof sym.scopeStartCol === "number" &&
    typeof sym.scopeEndLine === "number" &&
    typeof sym.scopeEndCol === "number";
  if (hasScope) return sym;
  return {
    ...sym,
    scopeStartLine: sym.startLine,
    scopeStartCol: sym.startCol,
    scopeEndLine: sym.endLine,
    scopeEndCol: sym.endCol,
  };
}

/**
 * @param {any} sym
 * @returns {boolean}
 */
function isRangedSymbol(sym) {
  return (
    sym &&
    typeof sym === "object" &&
    typeof sym.name === "string" &&
    typeof sym.startLine === "number" &&
    typeof sym.startCol === "number" &&
    typeof sym.endLine === "number" &&
    typeof sym.endCol === "number"
  );
}

/**
 * Non-empty half-open span (1-based).
 * @param {{ startLine: number, startCol: number, endLine: number, endCol: number }} s
 */
function isValidHalfOpenSpan(s) {
  if (typeof s.startLine !== "number" || typeof s.startCol !== "number") {
    return false;
  }
  if (typeof s.endLine !== "number" || typeof s.endCol !== "number") {
    return false;
  }
  if (s.startLine < s.endLine) return true;
  if (s.startLine > s.endLine) return false;
  return s.startCol < s.endCol;
}

/**
 * Half-open span containment (1-based), matching lexer / Span.contains.
 * @param {{ startLine: number, startCol: number, endLine: number, endCol: number }} s
 * @param {number} line
 * @param {number} col
 */
function spanContains(s, line, col) {
  if (!isValidHalfOpenSpan(s)) return false;
  const afterStart =
    line > s.startLine || (line === s.startLine && col >= s.startCol);
  const beforeEnd =
    line < s.endLine || (line === s.endLine && col < s.endCol);
  return afterStart && beforeEnd;
}

/**
 * @param {{ startLine: number, startCol: number, endLine: number, endCol: number }} s
 * @returns {number}
 */
function spanArea(s) {
  if (!isValidHalfOpenSpan(s)) return Number.POSITIVE_INFINITY;
  if (s.startLine === s.endLine) return s.endCol - s.startCol;
  return (
    (s.endLine - s.startLine) * 10000 + (s.endCol + (10000 - s.startCol))
  );
}

/**
 * @param {any} s
 * @returns {{ startLine: number, startCol: number, endLine: number, endCol: number }}
 */
function scopeSpan(s) {
  return {
    startLine: s.scopeStartLine,
    startCol: s.scopeStartCol,
    endLine: s.scopeEndLine,
    endCol: s.scopeEndCol,
  };
}

/**
 * @param {any[]} ranged
 * @param {number} line 1-based
 * @param {number} col 1-based
 * @returns {any | undefined}
 */
function symbolAtRanged(ranged, line, col) {
  const hits = ranged.filter((s) => spanContains(s, line, col));
  if (hits.length === 0) return undefined;
  let best = hits[0];
  for (let i = 1; i < hits.length; i++) {
    const s = hits[i];
    const aBest = spanArea(best);
    const aS = spanArea(s);
    if (aS < aBest || aS === aBest) best = s;
  }
  return best;
}

/**
 * Use-site: name match + scope contains + non-empty type; smallest scope wins.
 * @param {any[]} ranged
 * @param {number} line
 * @param {number} col
 * @param {string} name
 * @returns {any | undefined}
 */
function symbolAtUseSite(ranged, line, col, name) {
  const candidates = rangedByName(ranged).get(name) || [];
  const hits = candidates.filter((s) => {
    if (typeof s.type !== "string" || s.type.length === 0) return false;
    return spanContains(scopeSpan(s), line, col);
  });
  if (hits.length === 0) return undefined;
  let best = hits[0];
  for (let i = 1; i < hits.length; i++) {
    const s = hits[i];
    const aBest = spanArea(scopeSpan(best));
    const aS = spanArea(scopeSpan(s));
    if (aS < aBest || aS === aBest) best = s;
  }
  return best;
}

/**
 * Normalize diagnose stdout: v2/v3 ranged symbols (legacy v1 name-map ignored).
 * Keeps zero-width prelude placeholders (use-site only; def-span lookup skips them).
 * @param {unknown} raw
 * @returns {{ diagnostics: any[], version: number, ranged: any[], programTy?: string }}
 */
function normalizePayload(raw) {
  if (Array.isArray(raw)) {
    return { diagnostics: raw, version: 0, ranged: [] };
  }
  if (raw && typeof raw === "object") {
    const obj = /** @type {Record<string, unknown>} */ (raw);
    const diags = Array.isArray(obj.diagnostics) ? obj.diagnostics : [];
    const version = typeof obj.version === "number" ? obj.version : 1;
    const programTy =
      typeof obj.programTy === "string" ? obj.programTy : undefined;
    if (Array.isArray(obj.symbols)) {
      const ranged = obj.symbols.filter(isRangedSymbol).map(withScope);
      return { diagnostics: diags, version, ranged, programTy };
    }
    return { diagnostics: diags, version, ranged: [], programTy };
  }
  return { diagnostics: [], version: 0, ranged: [] };
}

/**
 * Emoji / symbol ranges allowed as FHM ident starts (Surface.Lex.isEmoji).
 * @param {number} cp
 */
function isEmojiCodePoint(cp) {
  return (
    (0x1f300 <= cp && cp <= 0x1faff) ||
    (0x2600 <= cp && cp <= 0x27bf) ||
    (0x1f1e6 <= cp && cp <= 0x1f1ff)
  );
}

/**
 * @param {string} ch
 */
function isIdentStartChar(ch) {
  if (!ch) return false;
  const c = ch.charCodeAt(0);
  if (
    (c >= 65 && c <= 90) ||
    (c >= 97 && c <= 122) ||
    c === 95 /* _ */
  ) {
    return true;
  }
  // Non-ASCII: alphabetic or emoji (code-point aware)
  if (c < 128) return false;
  const cp = ch.codePointAt(0);
  if (cp === undefined) return false;
  if (isEmojiCodePoint(cp)) return true;
  try {
    return /\p{L}/u.test(ch);
  } catch {
    return false;
  }
}

/**
 * @param {string} ch
 */
function isIdentContChar(ch) {
  if (!ch) return false;
  const c = ch.charCodeAt(0);
  if (
    (c >= 65 && c <= 90) ||
    (c >= 97 && c <= 122) ||
    (c >= 48 && c <= 57) ||
    c === 95
  ) {
    return true;
  }
  if (c < 128) return false;
  const cp = ch.codePointAt(0);
  if (cp === undefined) return false;
  if (isEmojiCodePoint(cp)) return true;
  try {
    return /[\p{L}\p{N}\p{M}]/u.test(ch);
  } catch {
    return false;
  }
}

/**
 * Find ident under a 0-based column — manual scan (no RegExp.exec loops).
 * @param {string} lineText
 * @param {number} col0
 * @returns {{ word: string, startCol0: number, endCol0: number } | undefined}
 */
function identAtColumn(lineText, col0) {
  if (typeof lineText !== "string" || col0 < 0 || col0 >= lineText.length) {
    return undefined;
  }
  // Walk code points; col0 is a UTF-16 offset (editor columns are UTF-16).
  let i = 0;
  while (i < lineText.length) {
    const cp = lineText.codePointAt(i);
    if (cp === undefined) break;
    const ch = String.fromCodePoint(cp);
    const start = i;
    const advance = cp > 0xffff ? 2 : 1;
    if (!isIdentStartChar(ch)) {
      i += advance;
      continue;
    }
    let j = i + advance;
    while (j < lineText.length) {
      const cp2 = lineText.codePointAt(j);
      if (cp2 === undefined) break;
      const ch2 = String.fromCodePoint(cp2);
      if (!isIdentContChar(ch2)) break;
      j += cp2 > 0xffff ? 2 : 1;
    }
    if (col0 >= start && col0 < j) {
      return {
        word: lineText.slice(start, j),
        startCol0: start,
        endCol0: j,
      };
    }
    i = j;
  }
  return undefined;
}

/**
 * @param {string} kind
 * @returns {string}
 */
function kindBadge(kind) {
  if (kind === "type") return "type";
  if (kind === "ctor") return "ctor";
  if (kind === "param") return "param";
  if (kind === "pat") return "pat";
  if (kind === "lit") return "lit";
  if (kind === "op") return "op";
  return "val";
}

/**
 * @param {any} sym
 */
function symbolHasUsableType(sym) {
  return sym && typeof sym.type === "string" && sym.type.length > 0;
}

/**
 * Tyvar / scheme-param defs should hover even if `type` is briefly empty.
 * @param {any} sym
 */
function isTyvarLike(sym) {
  return (
    sym &&
    (sym.kind === "param" ||
      (typeof sym.type === "string" && sym.type.startsWith("type variable")))
  );
}

/**
 * Convert 1-based diagnose span → 0-based editor range, clamped.
 * @param {any} sym
 * @param {number} line0
 * @param {number} col0
 * @param {number} nameLen
 */
function defSpanToRange(sym, line0, col0, nameLen) {
  const startLine0 = Math.max(0, (sym.startLine || 1) - 1);
  const startCol0 = Math.max(0, (sym.startCol || 1) - 1);
  const endLine0 = Math.max(0, (sym.endLine || 1) - 1);
  const endCol0 = Math.max(0, (sym.endCol || 1) - 1);
  return clampHoverRange(
    { startLine0, startCol0, endLine0, endCol0 },
    line0,
    col0,
    nameLen
  );
}

/**
 * Ensure range is non-empty, not inverted, not enormous, and contains cursor.
 * Monaco re-requests hover forever if the returned range misses the position.
 * @param {{ startLine0: number, startCol0: number, endLine0: number, endCol0: number }} range
 * @param {number} line0
 * @param {number} col0
 * @param {number} nameLen
 */
function clampHoverRange(range, line0, col0, nameLen) {
  const len = Math.max(1, nameLen || 1);
  const fallback = {
    startLine0: line0,
    startCol0: col0,
    endLine0: line0,
    endCol0: col0 + len,
  };

  let { startLine0, startCol0, endLine0, endCol0 } = range;

  if (
    startLine0 > endLine0 ||
    (startLine0 === endLine0 && startCol0 >= endCol0)
  ) {
    return fallback;
  }

  // Giant / multi-line highlights thrash Monaco — keep hover local.
  if (
    endLine0 !== startLine0 ||
    endCol0 - startCol0 > MAX_HOVER_SPAN_COLS
  ) {
    return fallback;
  }

  // Must contain the cursor (half-open).
  if (
    line0 !== startLine0 ||
    col0 < startCol0 ||
    col0 >= endCol0
  ) {
    return fallback;
  }

  return { startLine0, startCol0, endLine0, endCol0 };
}

/**
 * Resolve hover from a diagnose symbol cache.
 * Positions are 0-based (editor); spans in cache are 1-based.
 *
 * @param {any[]} ranged
 * @param {number} line0
 * @param {number} col0
 * @param {string} lineText
 * @returns {{
 *   name: string,
 *   kind: string,
 *   type: string,
 *   startLine0: number,
 *   startCol0: number,
 *   endLine0: number,
 *   endCol0: number
 * } | undefined}
 */
function resolveHover(ranged, line0, col0, lineText) {
  if (!Array.isArray(ranged) || ranged.length === 0) return undefined;

  const line = line0 + 1;
  const col = col0 + 1;

  let sym = symbolAtRanged(ranged, line, col);
  /** @type {{ startLine0: number, startCol0: number, endLine0: number, endCol0: number } | undefined} */
  let range;

  // Phase 0: def-span hit with a usable type, or tyvar/param def (even if type empty).
  if (
    sym &&
    isValidHalfOpenSpan(sym) &&
    (symbolHasUsableType(sym) || isTyvarLike(sym))
  ) {
    const nameLen =
      typeof sym.name === "string" && sym.name.length > 0
        ? sym.name.length
        : 1;
    range = defSpanToRange(sym, line0, col0, nameLen);
    if (!symbolHasUsableType(sym)) {
      sym = { ...sym, type: "type variable" };
    }
  } else {
    const hit = identAtColumn(lineText, col0);
    if (!hit) return undefined;
    if (!symbolHasUsableType(sym)) {
      sym = symbolAtUseSite(ranged, line, col, hit.word);
    }
    if (!symbolHasUsableType(sym)) {
      return undefined;
    }
    range = clampHoverRange(
      {
        startLine0: line0,
        startCol0: hit.startCol0,
        endLine0: line0,
        endCol0: hit.endCol0,
      },
      line0,
      col0,
      hit.word.length
    );
  }

  const name =
    typeof sym.name === "string" && sym.name.length > 0
      ? sym.name
      : lineText.slice(range.startCol0, range.endCol0) || "?";

  const type =
    typeof sym.type === "string" && sym.type.length > 0
      ? sym.type
      : "?";

  // Cap markdown payload size (pathological type strings).
  const typeOut = type.length > 2000 ? type.slice(0, 2000) + "…" : type;

  return {
    name,
    kind: kindBadge(sym.kind || "val"),
    type: typeOut,
    ...range,
  };
}

/**
 * Map diagnose diagnostics to 0-based marker-like objects.
 * @param {any[]} diagArr
 * @returns {{ line0: number, col0: number, message: string, severity: "error" | "warning" }[]}
 */
function diagnosticsToMarkers(diagArr) {
  if (!Array.isArray(diagArr)) return [];
  return diagArr.map((d) => {
    const line0 = Math.max(0, (d.line || 1) - 1);
    const col0 = Math.max(0, (d.col || 1) - 1);
    const severity = d.severity === "warning" ? "warning" : "error";
    return {
      line0,
      col0,
      message: d.message || "error",
      severity,
    };
  });
}

/**
 * Format live `--json` success/failure for the output panel.
 * @param {any} payload
 * @returns {string}
 */
function formatRunOutput(payload) {
  if (!payload || typeof payload !== "object") {
    return "(invalid run response)";
  }
  if (!payload.ok) {
    const stage = payload.stage || "error";
    const msg = payload.message || "failed";
    return `[${stage}] ${msg}`;
  }
  const lines = [];
  if (Array.isArray(payload.bindings)) {
    for (const b of payload.bindings) {
      if (b && typeof b.name === "string" && typeof b.type === "string") {
        lines.push(`  ${b.name}  :  ${b.type}`);
      }
    }
  }
  if (typeof payload.programTy === "string") {
    lines.push(`  <program>  :  ${payload.programTy}`);
  }
  if (payload.timings && typeof payload.timings.checkNs === "number") {
    lines.push(`  (checked in ${formatNs(payload.timings.checkNs)})`);
  }
  lines.push("");
  lines.push(`⟹  ${payload.result ?? "?"}`);
  if (payload.timings && typeof payload.timings.evalNs === "number") {
    lines.push(`  (evaluated in ${formatNs(payload.timings.evalNs)})`);
  }
  return lines.join("\n");
}

/**
 * @param {number} ns
 * @returns {string}
 */
function formatNs(ns) {
  if (ns < 1000) return `${ns}ns`;
  if (ns < 1_000_000) return `${Math.round(ns / 1000)}µs`;
  if (ns < 1_000_000_000) return `${Math.round(ns / 1_000_000)}ms`;
  const whole = Math.floor(ns / 1_000_000_000);
  const frac = Math.floor((ns % 1_000_000_000) / 10_000_000);
  const pad = frac < 10 ? "0" : "";
  return `${whole}.${pad}${frac}s`;
}

module.exports = {
  IDENT_RE,
  MAX_HOVER_SPAN_COLS,
  withScope,
  isRangedSymbol,
  isValidHalfOpenSpan,
  spanContains,
  spanArea,
  scopeSpan,
  rangedByName,
  symbolAtRanged,
  symbolAtUseSite,
  normalizePayload,
  identAtColumn,
  kindBadge,
  clampHoverRange,
  resolveHover,
  diagnosticsToMarkers,
  formatRunOutput,
  formatNs,
};
