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
  return innermostScope(
    candidates.filter((s) => typeof s.type === "string" && s.type.length > 0),
    line,
    col
  );
}

/**
 * Among symbols whose scope contains a 1-based position, the one with the
 * smallest scope (ties: the later one).
 * @param {any[]} syms
 * @param {number} line
 * @param {number} col
 */
function innermostScope(syms, line, col) {
  let best;
  for (const s of syms) {
    if (!spanContains(scopeSpan(s), line, col)) continue;
    if (!best || spanArea(scopeSpan(s)) <= spanArea(scopeSpan(best))) best = s;
  }
  return best;
}

/**
 * Normalize diagnose stdout: v2/v3 ranged symbols (legacy v1 name-map ignored)
 * plus lexer tokens (empty when absent).
 * Keeps zero-width prelude placeholders (use-site only; def-span lookup skips them).
 * @param {unknown} raw
 * @returns {{ diagnostics: any[], version: number, ranged: any[], tokens: any[], programTy?: string }}
 */
function normalizePayload(raw) {
  if (Array.isArray(raw)) {
    return { diagnostics: raw, version: 0, ranged: [], tokens: [] };
  }
  if (raw && typeof raw === "object") {
    const obj = /** @type {Record<string, unknown>} */ (raw);
    const diags = Array.isArray(obj.diagnostics) ? obj.diagnostics : [];
    const version = typeof obj.version === "number" ? obj.version : 1;
    const programTy =
      typeof obj.programTy === "string" ? obj.programTy : undefined;
    const tokens = normalizeTokens(obj.tokens);
    if (Array.isArray(obj.symbols)) {
      const ranged = obj.symbols.filter(isRangedSymbol).map(withScope);
      return { diagnostics: diags, version, ranged, tokens, programTy };
    }
    return { diagnostics: diags, version, ranged: [], tokens, programTy };
  }
  return { diagnostics: [], version: 0, ranged: [], tokens: [] };
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
  if (kind === "expr") return "expr";
  if (kind === "count") return "count";
  return "val";
}

/**
 * Markdown for a hover: the signature as an `fhm` code block, which both
 * VS Code and Monaco highlight with the registered FHM grammar, plus a prose
 * line where the payload's `type` is a description rather than a type, then
 * the definition's doc comment, if any.
 * @param {any} hit
 */
function hoverMarkdown(hit) {
  const doc = typeof hit?.doc === "string" && hit.doc.length > 0 ? hit.doc : "";
  const signature = hoverSignature(hit);
  // Doc comments are Markdown, shown under the signature as in other editors.
  return doc ? `${signature}\n\n---\n\n${doc}` : signature;
}

/**
 * @param {any} hit
 */
function hoverSignature(hit) {
  const kind = kindBadge(hit?.kind);
  const name = String(hit?.name ?? "?");
  const type = String(hit?.type ?? "?");
  const block = (code) => "```fhm\n" + code.replace(/`/g, "'") + "\n```";
  if (kind === "type" || kind === "expr") return block(type);
  if (kind === "param" && type.startsWith("type variable")) {
    return block(name) + "\n\n_" + type.replace(/[_*`]/g, "") + "_";
  }
  if (kind === "op") return block(`(${name}) : ${type}`);
  return block(`${name} : ${type}`);
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
 * Diagnose `tokens` rows (`[startLine, startCol, endLine, endCol, class]`,
 * 1-based half-open, in source order) → objects. Malformed rows are dropped.
 * @param {unknown} raw
 * @returns {{ startLine: number, startCol: number, endLine: number, endCol: number, kind: string }[]}
 */
function normalizeTokens(raw) {
  if (!Array.isArray(raw)) return [];
  const out = [];
  for (const t of raw) {
    if (
      Array.isArray(t) &&
      t.length === 5 &&
      t.slice(0, 4).every((n) => typeof n === "number") &&
      typeof t[4] === "string"
    ) {
      out.push({
        startLine: t[0],
        startCol: t[1],
        endLine: t[2],
        endCol: t[3],
        kind: t[4],
      });
    }
  }
  return out;
}

/**
 * Index of the last token starting at or before a 1-based position, or -1.
 * @param {any[]} tokens
 * @param {number} line
 * @param {number} col
 */
function lastTokenStartingBefore(tokens, line, col) {
  let lo = 0;
  let hi = tokens.length - 1;
  let found = -1;
  while (lo <= hi) {
    const mid = (lo + hi) >> 1;
    const t = tokens[mid];
    if (t.startLine < line || (t.startLine === line && t.startCol <= col)) {
      found = mid;
      lo = mid + 1;
    } else {
      hi = mid - 1;
    }
  }
  return found;
}

/**
 * What a 0-based position is on: `{ token }` (1-based span plus class), or
 * `{ between: true }` for whitespace between two code tokens on one line.
 * Indentation, trailing whitespace and past-the-end give `undefined`.
 * Uses diagnose `tokens` when available; otherwise approximates from the line
 * (identifiers exactly, any other non-blank character as a one-column token).
 * @param {any[] | undefined} tokens
 * @param {string} lineText
 * @param {number} line0
 * @param {number} col0
 * @returns {{ token?: any, between?: boolean } | undefined}
 */
function positionAt(tokens, lineText, line0, col0) {
  const line = line0 + 1;
  const col = col0 + 1;
  if (Array.isArray(tokens) && tokens.length > 0) {
    const i = lastTokenStartingBefore(tokens, line, col);
    if (i >= 0 && spanContains(tokens[i], line, col)) return { token: tokens[i] };
    const prev = tokens[i];
    const next = tokens[i + 1];
    const between =
      prev &&
      next &&
      prev.kind !== "comment" &&
      next.kind !== "comment" &&
      prev.endLine === line &&
      next.startLine === line;
    return between ? { between: true } : undefined;
  }
  if (typeof lineText !== "string" || col0 < 0 || col0 >= lineText.length) {
    return undefined;
  }
  const ident = identAtColumn(lineText, col0);
  if (ident) {
    return {
      token: {
        startLine: line,
        startCol: ident.startCol0 + 1,
        endLine: line,
        endCol: ident.endCol0 + 1,
        kind: "ident",
      },
    };
  }
  if (/\s/.test(lineText[col0])) {
    const before = lineText.slice(0, col0).trim() !== "";
    const after = lineText.slice(col0).trim() !== "";
    return before && after ? { between: true } : undefined;
  }
  return {
    token: { startLine: line, startCol: col, endLine: line, endCol: col + 1, kind: "punct" },
  };
}

/**
 * Source text of a single-line token, or `undefined`.
 * @param {any} token
 * @param {string} lineText
 */
function tokenText(token, lineText) {
  if (!token || token.startLine !== token.endLine || typeof lineText !== "string") {
    return undefined;
  }
  return lineText.slice(token.startCol - 1, token.endCol - 1) || undefined;
}

/**
 * Smallest span among symbols (ties: the later one).
 * @param {any[]} syms
 */
function smallestSpan(syms) {
  let best;
  for (const s of syms) {
    if (!best || spanArea(s) <= spanArea(best)) best = s;
  }
  return best;
}

/**
 * Highlight for a hover on `line0`: the symbol's span clipped to that line
 * (to its code tokens on the line when `tokens` are known), so a multi-line
 * construct highlights its part of the current line. Falls back to the token
 * under the cursor, then to the cursor's own column.
 * @param {any} sym
 * @param {any | undefined} token
 * @param {any[] | undefined} tokens
 * @param {number} line0
 * @param {number} col0
 * @param {string} lineText
 */
function hoverRangeFor(sym, token, tokens, line0, col0, lineText) {
  const line = line0 + 1;
  let startCol0;
  let endCol0;
  const onLine =
    Array.isArray(tokens) && tokens.length > 0
      ? tokens.filter(
          (t) =>
            t.kind !== "comment" &&
            t.startLine === line &&
            t.endLine === line &&
            spanContains(sym, t.startLine, t.startCol)
        )
      : [];
  if (onLine.length > 0) {
    startCol0 = Math.min(...onLine.map((t) => t.startCol)) - 1;
    endCol0 = Math.max(...onLine.map((t) => t.endCol)) - 1;
  } else {
    const text = typeof lineText === "string" ? lineText : "";
    startCol0 =
      sym.startLine === line ? sym.startCol - 1 : text.length - text.trimStart().length;
    endCol0 = sym.endLine === line ? sym.endCol - 1 : text.trimEnd().length;
  }
  const fallback =
    token && token.startLine === line && token.endLine === line
      ? { startLine0: line0, startCol0: token.startCol - 1, endLine0: line0, endCol0: token.endCol - 1 }
      : undefined;
  return clampHoverRange(
    { startLine0: line0, startCol0, endLine0: line0, endCol0 },
    line0,
    col0,
    fallback
  );
}

/**
 * Ensure range is non-empty, single-line, not enormous, and contains cursor;
 * otherwise use `fallback` (if it qualifies) or the cursor's own column.
 * Monaco re-requests hover forever if the returned range misses the position.
 * @param {{ startLine0: number, startCol0: number, endLine0: number, endCol0: number }} range
 * @param {number} line0
 * @param {number} col0
 * @param {{ startLine0: number, startCol0: number, endLine0: number, endCol0: number }} [fallback]
 */
function clampHoverRange(range, line0, col0, fallback) {
  const ok = (r) =>
    r &&
    r.startLine0 === line0 &&
    r.endLine0 === line0 &&
    r.startCol0 < r.endCol0 &&
    r.endCol0 - r.startCol0 <= MAX_HOVER_SPAN_COLS &&
    col0 >= r.startCol0 &&
    col0 < r.endCol0;
  if (ok(range)) return range;
  if (ok(fallback)) return /** @type {any} */ (fallback);
  return { startLine0: line0, startCol0: col0, endLine0: line0, endCol0: col0 + 1 };
}

/**
 * Resolve hover from a diagnose symbol cache.
 * Positions are 0-based (editor); spans in cache are 1-based.
 *
 * - Comments, indentation and trailing whitespace: no hover.
 * - On a token: the smallest non-expression symbol covering it (a binder,
 *   occurrence, literal or operator); else, for an identifier, its binder by
 *   name and scope (e.g. a constructor in a pattern, a type in an annotation);
 *   else, for a keyword or punctuation, the smallest expression containing it
 *   (e.g. `match` → the match).
 * - Whitespace between tokens: the smallest expression containing it, which
 *   is how an unparenthesised application such as `f x` shows its type.
 *
 * @param {any[]} ranged
 * @param {number} line0
 * @param {number} col0
 * @param {string} lineText
 * @param {any[]} [tokens] normalized diagnose tokens (approximated if absent)
 * @returns {{
 *   name: string,
 *   kind: string,
 *   type: string,
 *   startLine0: number,
 *   startCol0: number,
 *   endLine0: number,
 *   endCol0: number,
 *   doc?: string
 * } | undefined}
 */
function resolveHover(ranged, line0, col0, lineText, tokens) {
  if (!Array.isArray(ranged) || ranged.length === 0) return undefined;
  const line = line0 + 1;
  const col = col0 + 1;
  const at = positionAt(tokens, lineText, line0, col0);
  if (!at || (at.token && at.token.kind === "comment")) return undefined;

  const hits = ranged.filter(
    (s) =>
      spanContains(s, line, col) && (symbolHasUsableType(s) || isTyvarLike(s))
  );
  let sym;
  if (at.token) {
    sym = smallestSpan(hits.filter((s) => s.kind !== "expr"));
    if (!sym && at.token.kind === "ident") {
      const word = tokenText(at.token, lineText);
      if (word) sym = symbolAtUseSite(ranged, line, col, word);
    }
  }
  // An identifier means itself: an unresolved one (e.g. while lowering
  // fails) doesn't stand for the expression around it.
  if (!sym && at.token?.kind !== "ident") {
    sym = smallestSpan(hits.filter((s) => s.kind === "expr"));
  }
  if (!sym) return undefined;

  const range = spanContains(sym, line, col)
    ? hoverRangeFor(sym, at.token, tokens, line0, col0, lineText)
    : hoverRangeFor(at.token, at.token, tokens, line0, col0, lineText);

  const name =
    typeof sym.name === "string" && sym.name.length > 0
      ? sym.name
      : lineText.slice(range.startCol0, range.endCol0) || "?";
  let type = symbolHasUsableType(sym) ? sym.type : isTyvarLike(sym) ? "type variable" : "?";
  // Cap markdown payload size (pathological type strings).
  if (type.length > 2000) type = type.slice(0, 2000) + "…";

  return {
    name,
    kind: kindBadge(sym.kind || "val"),
    type,
    ...(typeof sym.doc === "string" && sym.doc.length > 0 ? { doc: sym.doc } : {}),
    ...range,
  };
}

/**
 * Go to definition: the definition site of the identifier at a 0-based
 * position, as a 0-based half-open range. On a definition site, that site
 * itself. Names without a source location (the prelude) give `undefined`.
 * Resolution matches hover's use-site rule: same name, innermost scope.
 * @param {any[]} ranged
 * @param {number} line0
 * @param {number} col0
 * @param {string} lineText
 * @param {any[]} [tokens]
 * @returns {{ startLine0: number, startCol0: number, endLine0: number, endCol0: number } | undefined}
 */
function resolveDefinition(ranged, line0, col0, lineText, tokens) {
  if (!Array.isArray(ranged) || ranged.length === 0) return undefined;
  const at = positionAt(tokens, lineText, line0, col0);
  if (!at || !at.token || at.token.kind !== "ident") return undefined;
  const word = tokenText(at.token, lineText);
  if (!word) return undefined;
  const defs = (rangedByName(ranged).get(word) || []).filter((s) => s.def === true);
  const def =
    defs.find(
      (s) => s.startLine === at.token.startLine && s.startCol === at.token.startCol
    ) || innermostScope(defs, line0 + 1, col0 + 1);
  if (!def || !isValidHalfOpenSpan(def)) return undefined;
  return {
    startLine0: def.startLine - 1,
    startCol0: def.startCol - 1,
    endLine0: def.endLine - 1,
    endCol0: def.endCol - 1,
  };
}

/**
 * Map diagnose diagnostics to 0-based marker-like objects (half-open span).
 * @param {any[]} diagArr
 * @returns {{ line0: number, col0: number, endLine0: number, endCol0: number, message: string, severity: "error" | "warning" }[]}
 */
function diagnosticsToMarkers(diagArr) {
  if (!Array.isArray(diagArr)) return [];
  return diagArr.map((d) => {
    const line0 = Math.max(0, (d.line || 1) - 1);
    const col0 = Math.max(0, (d.col || 1) - 1);
    let endLine0 = Math.max(0, (d.endLine || d.line || 1) - 1);
    let endCol0 = Math.max(0, (d.endCol || (d.col || 1) + 1) - 1);
    // Degenerate / missing end → at least one column.
    if (
      endLine0 < line0 ||
      (endLine0 === line0 && endCol0 <= col0)
    ) {
      endLine0 = line0;
      endCol0 = col0 + 1;
    }
    const severity = d.severity === "warning" ? "warning" : "error";
    return {
      line0,
      col0,
      endLine0,
      endCol0,
      message: d.message || "error",
      severity,
    };
  });
}

/**
 * Escape text for safe HTML insertion.
 * @param {unknown} s
 * @returns {string}
 */
function escapeHtml(s) {
  return String(s)
    .replace(/&/g, "&amp;")
    .replace(/</g, "&lt;")
    .replace(/>/g, "&gt;")
    .replace(/"/g, "&quot;");
}

/**
 * Format live `--json` success/failure as coloured HTML (web playground).
 * @param {any} payload
 * @returns {string}
 */
function formatRunOutputHtml(payload) {
  if (!payload || typeof payload !== "object") {
    return escapeHtml("(invalid run response)");
  }
  if (!payload.ok) {
    const stage = payload.stage || "error";
    const msg = payload.message || "failed";
    return (
      `<span class="tok-stage">[${escapeHtml(stage)}]</span> ` +
      `<span class="tok-err">${escapeHtml(msg)}</span>`
    );
  }
  const lines = [];
  if (Array.isArray(payload.bindings)) {
    for (const b of payload.bindings) {
      if (b && typeof b.name === "string" && typeof b.type === "string") {
        lines.push(
          `  <span class="tok-name">${escapeHtml(b.name)}</span>  ` +
            `<span class="tok-colon">:</span>  ` +
            `<span class="tok-type">${escapeHtml(b.type)}</span>`
        );
      }
    }
  }
  if (typeof payload.programTy === "string") {
    lines.push(
      `  <span class="tok-program">&lt;program&gt;</span>  ` +
        `<span class="tok-colon">:</span>  ` +
        `<span class="tok-type">${escapeHtml(payload.programTy)}</span>`
    );
  }
  if (payload.timings && typeof payload.timings.checkNs === "number") {
    lines.push(
      `<span class="tok-dim">  (checked in ${escapeHtml(formatNs(payload.timings.checkNs))})</span>`
    );
  }
  lines.push("");
  const result = payload.result ?? "?";
  lines.push(
    `<span class="tok-arrow">⟹</span>  ` +
      `<span class="tok-result">${escapeHtml(result)}</span>`
  );
  if (payload.timings && typeof payload.timings.evalNs === "number") {
    lines.push(
      `<span class="tok-dim">  (evaluated in ${escapeHtml(formatNs(payload.timings.evalNs))})</span>`
    );
  }
  return lines.join("\n");
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
  normalizeTokens,
  positionAt,
  identAtColumn,
  kindBadge,
  hoverMarkdown,
  clampHoverRange,
  resolveHover,
  resolveDefinition,
  diagnosticsToMarkers,
  formatRunOutput,
  formatRunOutputHtml,
  formatNs,
  escapeHtml,
};
