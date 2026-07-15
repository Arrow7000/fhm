# Surface Lexer & Parser Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Lex and parse FHM’s Surface language into named `Surface.*` ASTs (exprs first, then programs), with single-infix desugar to `Surface.Expr.primBinOp`, on `fgdorais/lean4-parser`.

**Architecture:** Separate lex (`String` → `Array Token`) then parse (token stream → `Surface.Expr` / `Surface.Program`). Layout via column guards. Infix / `::` / multi-λ desugared in the parser. Spec: `docs/superpowers/specs/2026-07-15-surface-parser-lexer-design.md`.

**Tech Stack:** Lean 4 (`v4.26.0`), Lake, `@fgdorais/Parser` pinned to SHA `b50def30c0b6` (toolchain `v4.26.0`), existing `FHM.SurfaceLang` / `FHM.SurfaceBridge` / `FHM.Pretty`.

## Global Constraints

- Lean toolchain stays `leanprover/lean4:v4.26.0` unless a later task explicitly bumps it.
- Parser dependency: `git = "https://github.com/fgdorais/lean4-parser"`, `rev = "b50def30c0b6"` (or newer **only if** its `lean-toolchain` still matches `v4.26.0`).
- No `sorry` / `admit` / `axiom` / `native_decide` in FHM proofs.
- Do not emit `PrimLitExpr.nat` / `PrimTy.nat` from the parser.
- No bare `intAdd` names; no `DataDecl` field-name AST change (parse-and-discard only).
- Tabs forbidden; block comments nest (depth counter); program body optional → default `.primLit .unit`.
- Follow workspace Lean workflow: prefer LSP diagnostics over full `lake build` during edit loops; full build OK at task boundaries.

---

## File structure

| File | Responsibility |
|------|----------------|
| `lakefile.toml` | Require Parser; add new roots |
| `lake-manifest.json` | Lockfile after `lake update` |
| `FHM/SurfaceLang.lean` | Add `Expr.primBinOp` |
| `FHM/Pretty.lean` | Pretty-print `primBinOp` |
| `FHM/SurfaceBridge.lean` | `lowerExpr` + `LowersExpr` + all `Surface.Expr` cases |
| `FHM/Surface/Lex.lean` | `Token`, spans, `lex` |
| `FHM/Surface/Parse.lean` | Parsers + `parseExpr` / `parseProgram` |
| `FHM/Surface/LexTest.lean` | Lexer `#guard` / examples |
| `FHM/Surface/ParseTest.lean` | Parser `#guard` / examples |

Module names: `FHM.Surface.Lex`, `FHM.Surface.Parse`, etc.

---

### Task 1: Pin lean4-parser for Lean 4.26

**Files:**
- Modify: `lakefile.toml`
- Modify: `lake-manifest.json` (via `lake update`)

**Interfaces:**
- Consumes: nothing
- Produces: `import Parser` works in a scratch module

- [ ] **Step 1: Add the require**

Append to `lakefile.toml`:

```toml
[[require]]
name = "Parser"
git = "https://github.com/fgdorais/lean4-parser"
rev = "b50def30c0b6"
```

- [ ] **Step 2: Update deps**

Run: `lake update Parser`  
Expected: manifest gains Parser (+ its deps, e.g. batteries / UnicodeBasic as required by that rev); no toolchain change away from `v4.26.0`.

- [ ] **Step 3: Smoke import**

Create temporary `FHM/Surface/ParserSmoke.lean`:

```lean
import Parser

#check Parser.SimpleParser
```

Add root `"FHM.Surface.ParserSmoke"` to `lakefile.toml` `roots` (or build via import from an existing root). Run `lake build FHM.Surface.ParserSmoke`.  
Expected: success.

- [ ] **Step 4: Remove smoke file / root** (or leave until Lex lands and delete then)

- [ ] **Step 5: Commit**

```bash
git add lakefile.toml lake-manifest.json
git commit -m "deps: pin fgdorais/lean4-parser for Lean 4.26"
```

---

### Task 2: Add `Surface.Expr.primBinOp` and lower it

**Files:**
- Modify: `FHM/SurfaceLang.lean` (add ctor after `primLit` or near `var`)
- Modify: `FHM/Pretty.lean` (`Surface.Expr.prettyAux`)
- Modify: `FHM/SurfaceBridge.lean` (`lowerExpr`, `LowersExpr`, and every incomplete `Surface.Expr` match — follow compiler holes)

**Interfaces:**
- Consumes: `Core.PrimBinOp` (already imported via `FHM.Core` in SurfaceLang)
- Produces:
  - `Surface.Expr.primBinOp (op : PrimBinOp)`
  - `lowerExpr … (.primBinOp op) = some (.primBinOp op)`
  - `LowersExpr` ctor for primBinOp

- [ ] **Step 1: Extend the inductive**

In `FHM/SurfaceLang.lean`, add:

```lean
| primBinOp (op : PrimBinOp)
```

to `inductive Expr` (alongside other leaves). `PrimBinOp` is already in scope from `import FHM.Core`.

- [ ] **Step 2: Fix Pretty**

In `Surface.Expr.prettyAux`, add:

```lean
| .primBinOp op =>
    match op with
    | .intAdd => "intAdd"  -- pretty name; surface source uses infix, but ToString needs something
    | .intSub => "intSub"
    | .intLt  => "intLt"
    | .charLt => "charLt"
```

(Optional later: pretty infix when used as saturated apps; leaf form as above is fine.)

- [ ] **Step 3: Extend `lowerExpr`**

In `SurfaceBridge.lowerExpr`, add before/near `.var`:

```lean
| .primBinOp op => some (.primBinOp op)
```

- [ ] **Step 4: Extend `LowersExpr`**

Add:

```lean
| primBinOp {op} :
    LowersExpr ctors ke tvs vs (.primBinOp op) (.primBinOp op)
```

Update `lowerExpr_LowersExpr` / related proofs: `cases` on the new ctor → `exact .primBinOp` (or follow existing leaf style for `.ctor`).

- [ ] **Step 5: Close all other `Surface.Expr` matches**

Build / LSP: fix every “missing cases: primBinOp” in `SurfaceBridge` (and any other file). Typical leaf treatment mirrors `.ctor` / `.primLit` (size 1, exhaustive OK, tyFreeVars empty, etc.).

- [ ] **Step 6: Sanity `#guard`**

In `FHM/Examples.lean` or a tiny test:

```lean
#guard (SurfaceBridge.lowerExpr {} [] [] (.primBinOp .intAdd)) == some (.primBinOp .intAdd)
```

- [ ] **Step 7: Commit**

```bash
git add FHM/SurfaceLang.lean FHM/Pretty.lean FHM/SurfaceBridge.lean FHM/Examples.lean
git commit -m "feat(surface): add Expr.primBinOp and lower to Core"
```

---

### Task 3: Token type + lexer skeleton

**Files:**
- Create: `FHM/Surface/Lex.lean`
- Create: `FHM/Surface/LexTest.lean`
- Modify: `lakefile.toml` (add roots `FHM.Surface.Lex`, `FHM.Surface.LexTest`)

**Interfaces:**
- Consumes: none from Parse yet
- Produces:
  - `Surface.Lex.Token` inductive
  - `Surface.Lex.TokenWithSource`
  - `Surface.Lex.LexError`
  - `Surface.Lex.lex : String → Except LexError (Array TokenWithSource)`

- [ ] **Step 1: Define tokens**

```lean
import FHM.SurfaceLang

namespace Surface.Lex

inductive Token
  | whitespace (kind : WhitespaceKind)  -- or omit if skipping WS; keep positions either way
  | lineComment (text : String)
  | blockComment (text : String)
  | ident (raw : String) (isUpper : Bool)
  | keyword (kw : Keyword)   -- let, in, match, with, if, then, else, type, …
  | intLit (n : Int)
  | charLit (c : Char)
  | stringLit (s : String)
  | boolLit (b : Bool)       -- True / False
  | op (o : BinOpToken)      -- plus, minus, lt, cons, …
  | punct (p : Punct)        -- lparen, rparen, lbrace, rbrace, lbrack, rbrack, comma, colon, eq, pipe, arrow, backslash, underscore
  deriving Repr, DecidableEq

structure TokenWithSource where
  token : Token
  startLine : Nat
  startCol  : Nat
  endLine   : Nat
  endCol    : Nat
  deriving Repr

inductive LexError
  | tab (line col : Nat)
  | unexpectedChar (c : Char) (line col : Nat)
  | unfinishedBlockComment (line col : Nat)
  | badEscape (line col : Nat)
  deriving Repr

def lex (input : String) : Except LexError (Array TokenWithSource) :=
  sorry  -- replace in following steps; do not leave sorry in final task commit
```

Replace `sorry` before commit: start with “empty input → `#[]`” and “reject tab”.

- [ ] **Step 2: Failing tests**

`FHM/Surface/LexTest.lean`:

```lean
import FHM.Surface.Lex

open Surface.Lex

#guard (lex "").isOk
#guard (match lex "\t" with | .error (.tab ..) => true | _ => false)
```

- [ ] **Step 3: Implement empty + tab rejection**

Cursor over input; on `\t` return `.error (.tab line col)`; on EOF return `.ok tokens`.

- [ ] **Step 4: Build**

Run: `lake build FHM.Surface.LexTest`  
Expected: PASS.

- [ ] **Step 5: Commit**

```bash
git add FHM/Surface/Lex.lean FHM/Surface/LexTest.lean lakefile.toml
git commit -m "feat(surface): Token ADT and lex skeleton"
```

---

### Task 4: Lex comments, idents, keywords, ints, ops, punct

**Files:**
- Modify: `FHM/Surface/Lex.lean`
- Modify: `FHM/Surface/LexTest.lean`

**Interfaces:**
- Consumes: Task 3 API
- Produces: full `lex` for slice-1 token set (still may skip strings/chars until Task 5 if split preferred — prefer finishing all literal/token kinds here)

- [ ] **Step 1: Tests first** (add `#guard`s)

Cover at least:

- `-- hi\nlet` → lineComment then keyword `let`
- `{- a {- b -} c -}` → one blockComment (nested)
- `foo` / `Foo` / `🎉name` (emoji ident) → ident lower/upper as appropriate
- `True` `False` → boolLit
- `42` `-3` → intLit (single token; `-` before digits only when starting a lit)
- `->` `::` `+` `-` `<` `=` `|` `:` `\` `_` `( ) [ ] { }` `,`
- Disambiguation: `->` not `-` then `>`; `::` not two `:`

- [ ] **Step 2: Implement scanners**

Order matters: longest match for ops (`->`, `::` before `-`, `:`); keywords before idents; `True`/`False` before upper idents; nested block comment with depth counter; `--` to EOL; unicode ident: start with letter or emoji numeric, continue with letter/mark/number/emoji/`_`.

Neg int: when at `-` and next char is digit, consume as intLit (not op minus). When `-` not followed by digit → `op .minus`.

- [ ] **Step 3: Build LexTest**

Expected: all `#guard`s pass.

- [ ] **Step 4: Commit**

```bash
git add FHM/Surface/Lex.lean FHM/Surface/LexTest.lean
git commit -m "feat(surface): full lexer for comments, idents, lits, ops"
```

---

### Task 5: Parse atoms + types + schemes

**Files:**
- Create: `FHM/Surface/Parse.lean`
- Create: `FHM/Surface/ParseTest.lean`
- Modify: `lakefile.toml` (roots)

**Interfaces:**
- Consumes: `Surface.Lex.lex`, token stream
- Produces:
  - `parseTy : String → Except ParseError Surface.Ty` (or parse from tokens)
  - `parsePolyTy : … → Surface.PolyTy`
  - Internal: token parser monad over `Subarray TokenWithSource` / `OfList`

- [ ] **Step 1: Parser plumbing**

```lean
import Parser
import FHM.Surface.Lex
import FHM.SurfaceLang

namespace Surface.Parse

structure ParseError where
  msg : String
  line : Nat
  col : Nat
  deriving Repr

-- Prefer: lex then run SimpleParser (or Basic) on token array.
def parseTokens (tokens : Array Lex.TokenWithSource) : …
def runLexParse (p : …) (src : String) : Except … α :=
  match Lex.lex src with
  | .error e => .error (lexToParse e)
  | .ok toks => runParser p toks
```

Skip whitespace tokens inside parsers (or never emit them from lex — pick one and stick to it; if lex skips WS, still record line/col on every token).

- [ ] **Step 2: Tests**

```lean
#guard (parseTy "Int").isOk
#guard (parseTy "Int -> Bool").isOk
#guard (parseTy "(Int, Bool)").isOk
#guard (parseTy "{a} a -> a") ==
  .ok { foralls := [⟨"a"⟩], body := .arrow (.tvar ⟨"a"⟩) (.tvar ⟨"a"⟩) }
-- adjust ValName ctor to match project (often ValName.mk)
```

Map builtin type names (`Int`, `Bool`, `Char`, `Unit` / `()` ) to `Ty.prim` as the rest of Surface already expects (check `SurfaceBridge` / examples for exact name mapping before coding).

- [ ] **Step 3: Implement `ty` / `polyTy` / atoms needed for types** (`()`, idents, arrows right-assoc, juxtaposition for `customTy`)

- [ ] **Step 4: Build + commit**

```bash
git commit -m "feat(surface): parse types and {a b} schemes"
```

---

### Task 6: Parse expressions — app, λ, literals, pair/list/cons, single infix

**Files:**
- Modify: `FHM/Surface/Parse.lean`
- Modify: `FHM/Surface/ParseTest.lean`

**Interfaces:**
- Produces: `parseExpr : String → Except ParseError Surface.Expr`

- [ ] **Step 1: Tests**

```lean
#guard (parseExpr "1").isOk
#guard (parseExpr "-3").isOk
#guard (parseExpr "True").isOk
#guard (parseExpr "\\x y -> x").isOk   -- nested lambdas, name binders only
#guard (parseExpr "f a b").isOk       -- left app
#guard (parseExpr "1 + 2") ==
  .ok (.app (.app (.primBinOp .intAdd) (.primLit (.int 1))) (.primLit (.int 2)))
#guard (parseExpr "a :: (b :: c)").isOk
#guard (parseExpr "a + b + c").isError  -- no chains without parens
#guard (parseExpr "(a + b) + c").isOk
```

- [ ] **Step 2: Implement expression grammar**

Suggested layers:

1. `atom` — lit, var/ctor (lower/upper), `()`, `(e)`, `[es]`, `\ binders -> e`
2. `appExpr` — juxtaposition
3. `expr` — `appExpr` optional single `(op appExpr)` for `+`/`-`/`<`/`::`

Multi-λ: fold binders right into nested `.lambda (.name x) none body`.  
`::` → `.cons`. Reject a second infix at the same layer.

- [ ] **Step 3: Build + commit**

```bash
git commit -m "feat(surface): parse apps, lambdas, lists, single infix"
```

---

### Task 7: Layout — `let`/`in`, `if`, `match`

**Files:**
- Modify: `FHM/Surface/Parse.lean`
- Modify: `FHM/Surface/ParseTest.lean`

**Interfaces:**
- Extends `parseExpr` with layout-sensitive forms
- Layout helpers: `withBlockCol`, `colEq`, `colGt` (Tigris-style) using `TokenWithSource.startCol` / `startLine`

- [ ] **Step 1: Tests**

```lean
#guard (parseExpr "let x = 1 in x").isOk
#guard (parseExpr "if True then 1 else 0").isOk
#guard (parseExpr "match True with | True -> 1 | False -> 0").isOk
#guard (parseExpr "match True with True -> 1 | False -> 0").isOk  -- leading | optional
```

Multi-binding same-column `let` (use a raw string with newlines in the test file).

- [ ] **Step 2: Implement**

- `let` binding list: first binding sets `blockCol`; siblings at `colEq`; each RHS under `colGt` (or same line).
- `let` binders: **simple name only** (+ optional `: polyTy`).
- `match`: after `with`, branches at indented col; pattern then `->` then expr.
- `if then else` — no special indent required beyond normal expr.

- [ ] **Step 3: Patterns**

Implement `parsePattern` for match: name, `_`, ctor apps, pair, list, right-assoc `::` chains.  
Do **not** use full patterns for λ/`let` binders.

- [ ] **Step 4: Build + commit**

```bash
git commit -m "feat(surface): layout-sensitive let, if, and match"
```

---

### Task 8: Parse `Program` (types + top-level lets + optional body)

**Files:**
- Modify: `FHM/Surface/Parse.lean`
- Modify: `FHM/Surface/ParseTest.lean`

**Interfaces:**
- Produces: `parseProgram : String → Except ParseError Surface.Program`

- [ ] **Step 1: Tests**

```lean
#guard (parseProgram "let x = 1\n").isOk
-- body defaults to unit:
#guard (match parseProgram "let x = 1" with
  | .ok p => p.body == .primLit .unit
  | _ => false)

#guard (parseProgram "type Maybe a = Just a | Nothing\nlet x = Nothing\nx").isOk
```

Ctor fields: `Just (contents : a)` parses but **discards** `contents` → field list `[tvar a]`.

- [ ] **Step 2: Implement**

Top-level: zero or more `type` decls and `let` bindings (F# style — `let` required), then optional expr, then EOF.  
Flatten lets into `Program.groups` as a single group list via existing `Program.ofFlat` / one group per binding for now (document choice; SCC can stay post-parse).

```lean
-- Preferred: reuse SurfaceBridge.Program.ofFlat if available
{ decls := decls, groups := ofFlat binds, body := body.getD (.primLit .unit) }
```

- [ ] **Step 3: End-to-end smoke**

Parse a tiny program → `Program.term` → `lowerExpr` / existing bridge entry if convenient; `#guard` `Option.isSome`.

- [ ] **Step 4: Commit**

```bash
git commit -m "feat(surface): parse Program with optional unit body"
```

---

### Task 9: Polish + wire lakefile roots + headlines/docs pointer

**Files:**
- Modify: `lakefile.toml` (ensure Lex/Parse/tests roots are correct; remove smoke if any)
- Modify: `briefs/` or `FHM/Headlines.lean` only if a one-line “parser exists” pointer is desired — skip unless already editing
- Modify: design status line to `Accepted` if not already

- [ ] **Step 1: Full build of new modules + dependent Examples guards**

Run: `lake build FHM.Surface.LexTest FHM.Surface.ParseTest`  
Expected: green.

- [ ] **Step 2: Spec status**

Set `docs/superpowers/specs/2026-07-15-surface-parser-lexer-design.md` status to **Accepted**.

- [ ] **Step 3: Commit**

```bash
git commit -m "chore(surface): mark parser design accepted; finalize roots"
```

---

## Spec coverage checklist

| Spec item | Task |
|-----------|------|
| Pin Parser / 4.26 | 1 |
| `Surface.primBinOp` + lower | 2 |
| Lex tokens, tabs, `--`, nested `{- -}`, unicode idents, neg ints | 3–4 |
| Types, `{x y} ty`, value-style anns | 5, 7–8 |
| Expr core + single infix + `::` sugar | 6 |
| `let`/`in` columns, `if`, F# `match`, patterns + `::` chains | 7 |
| F# top-level `let`, `type`, optional body → `()` | 8 |
| Parse-and-discard ctor field names | 8 |
| Phase A then B | 6–7 then 8 |

## Placeholder / consistency self-review

- Parser SHA fixed to `b50def30c0b6` (4.26).
- `ValName` / `CtorName` / `TyName` constructors must match repo (`⟨"…"⟩` vs `.mk`) — implementers check `FHM.Core` / existing Surface examples when writing `#guard`s.
- `Program.ofFlat` name verified at Task 8 against `SurfaceBridge`.
- Pretty currently uses `=>` in match; parser accepts `->` per spec — leave pretty as-is unless touching that line.
