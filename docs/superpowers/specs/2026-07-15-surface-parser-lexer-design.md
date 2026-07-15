# Surface lexer & parser design

**Date:** 2026-07-15  
**Status:** Draft for review  
**Scope:** Lex + parse the full current Surface language into named `Surface.*` ASTs, then hand off to the existing desugar / resolve / lower pipeline.

## Goals

- Turn source text into `Surface.Expr` / `Surface.Program` (and types/patterns as needed).
- Elm-flavoured concrete syntax where it fits; F#/`match` and Lean-ish `{x y} ty` where Elm has no precedent.
- Separate lex and parse stages on top of `fgdorais/lean4-parser`.
- Implementation may land in phases (**exprs first, then top-level `Program`**), but the *design* covers the full Surface language as it exists today.

## Non-goals

- Modules, imports, exposing lists
- Records / rows / type aliases
- User-declared infix / fixity (Elm `infix` decls)
- Bare primop names (`intAdd`) or namespaced builtins (`Core.intAdd`) — deferred until namespacing exists
- General unary operators
- Pattern-λ / pattern-`let` bindings (Surface can represent some of this; lowering still rejects nontrivial λ patterns — parser only accepts simple names for λ/`let` binders)
- Literal patterns (`0`, `True` as patterns) — `Surface.Pattern` has no lit ctor yet; match on bools via `True`/`False` **ctors** only
- Storing constructor field names in the AST (parse-and-discard only, for now)
- Proving lexer/parser correctness

## Approach

**Lex → tokens → parse (chosen).**

Char-level-only grammars and an intermediate “sugar AST” (`BinOp`, etc.) were rejected: the former fights indent/keywords; the latter is YAGNI while sugar is small.

Pipeline:

```text
text → lex → Array Token → parse → Surface (named)
     → existing desugar / resolve / lower → Core
```

Infix, `::`, and multi-parameter lambdas are desugared **during parse** into existing Surface constructors (plus new `primBinOp`).

## Dependency note

FHM currently pins **Lean `v4.26.0`**. Upstream `fgdorais/lean4-parser` tracks newer toolchains (recently ~`v4.32.0`). Implementation must either:

1. pin a **lean4-parser commit compatible with 4.26**, or  
2. **bump FHM’s toolchain** (and mathlib) to match a current Parser release.

Decide at implementation kickoff; do not float `main` without a lockfile SHA.

## Concrete syntax

### Lexical

| Item | Choice |
|------|--------|
| Whitespace | Tracked for line/column (skip or keep as tokens — implementation detail). Tabs → hard error. |
| Comments | Elm-style `--` to EOL and nested `{- … -}` (each `{-` needs its own `-}`; depth counter). |
| Identifiers | Unicode-friendly: letters + emoji allowed in names (nice-to-have for surface programs). ASCII keywords remain reserved. Upper vs lower still distinguished like Elm (ctors / types vs values) where the grammar cares. |
| Integers | Single token, optional leading `-` glued into the literal (`-3` is one int lit, not unary minus). **No nat literals** (nats slated for removal; all numeric lits are `Int`). |
| Bools | `True` / `False` |
| Char / string | Basic escapes (`\\`, `\"`, `\n`, `\r`, …) |
| Operators | Builtin tokens: `+`, `-`, `<`, `::`, `->`, `=`, `\|`, `:`, etc. No free `OtherOp` catch-all in v1. |

### Types

- Function: `A -> B` (ASCII only; no `→` / `∀` aliases in v1).
- Pair: `(A, B)`
- App: juxtaposition (`Maybe Int`)
- Prim / custom names as idents (`Int`, `Bool`, `List`, …) mapped later as today
- Schemes: `{x y z} body` → `PolyTy.foralls = [x,y,z]`, `body = …`
- Annotations: value-style only, inline on the binding — `f : {a} a -> a = \x -> x`  
  - **Not** Elm separate-line `f : T` then `f = …`  
  - **Not** `f (a : T) (b : R) : S` (would need real Surface support first)

### Expressions

- Literals, vars, ctors, juxtaposition app, `(e)` grouping (parens are parse-only; **no** `Expr.paren` node)
- Lambda: `\x y -> e` → nested `lambda` (each binder a **simple name** only)
- `let` / `in` with **column-aligned** bindings (YlangYlang/Tigris-style column guards; not OCaml `let…in let…in` chaining as the primary style)
- `if e then e else e`
- Match: F#-style  
  `match e with | P -> e | Q -> e`  
  Leading `|` optional when the first branch shares the line with `with`
- Lists `[a, b]`, pairs `(a, b)`, cons via infix `::`
- **Single** infix expression form: `a ⊕ b` only. Chains need parens, e.g. `(a + b) + c` or `a :: (b :: rest)` (no multi-op chains without parens).

### Infix and “fixity”

**Fixity** here means the pair *(precedence, associativity)* (and sometimes arity). Slice-1 **expression** infix forbids chains, so precedence between `+` and `<` does not come into play for exprs.

| Op | Parse result | Notes |
|----|--------------|--------|
| `+` | `app (app (primBinOp intAdd) a) b` | |
| `-` | `app (app (primBinOp intSub) a) b` | Binary only |
| `<` | `app (app (primBinOp intLt) a) b` | `charLt` not exposed yet |
| `::` | `cons a b` | Sugar, not a primop |

**Pattern** `::` chains are allowed and hardcode **right-associativity**:  
`a :: b :: rest` ⇒ `cons a (cons b rest)`  
(This is pattern structure, not expression infix chaining.)

### Patterns (match)

- `name`, `_`, ctor apps, pair, cons, list
- `a :: b :: rest` as above
- Lambda / `let` binders: **simple names only** (aligned with current lowering)

### Top-level program (F# style)

Prefer **`let` at the root**, not Elm/Haskell bare bindings:

```text
type Maybe a = Just a | Nothing

let f : Int -> Int =
  \x -> x + 1

let g =
  match True with
  | True -> f 1
  | False -> 0

g
```


- `type` decls and `let` bindings are the declaration forms
- A trailing **body expression** is required (feeds `Program.body`)
- Binding groups / SCCs: parser may emit a flat binding list; existing `ofFlat` / `sccGroups` (or author groups) remain the mutual-recursion story — no `mutual` keyword
- Constructor args in `type` decls: allow optional `(name : Ty)` **or** plain `Ty`; **discard names immediately** in the parser — do **not** change `DataDecl` yet (`ctors` stay `List (CtorName × List Ty)`)

## AST / bridge changes

| Change | Detail |
|--------|--------|
| Add `Surface.Expr.primBinOp` | Mirror `Core.PrimBinOp` / `Expr.primBinOp` |
| Teach `lowerExpr` | `.primBinOp op ⇒ some (.primBinOp op)` |
| `DataDecl` field names | **No AST change** in this slice — parse-and-discard only |
| `PrimTy.nat` / `PrimLitExpr.nat` | Parser never emits them |

No paren node. No surface binop node.

## Parser architecture

1. **`Token`** inductive + `TokenWithSource` (line/col/end span).
2. **Lexer:** `String` → `Array Token` (or list); reject tabs; nest block comments; emit int lits with optional `-`.
3. **Parser:** `SimpleParser` (or equivalent) over a token stream (`Subarray` / `OfList`).
4. **Layout:** parser state holds indent/column stack or “current block column”; `colEq` / `colGt` guards around `let` binding lists and `match` branches (same idea as Tigris / YlangYlang, without YY’s heavy window-copy machinery unless needed).
5. **Errors:** lean4-parser `Simple` errors + `withErrorMessage` where helpful; friendly diagnostics can improve later.

### Suggested modules

- `FHM/Surface/Lex.lean` — tokens + lexer  
- `FHM/Surface/Parse.lean` — parsers + public `parseExpr` / `parseProgram`  
- Tests / examples beside them or under `FHM/Examples` as preferred at implementation time  

(Exact names can shift; keep lex and parse separable.)

## Phasing (implementation)

**Phase A — expressions:** lit/var/ctor/app/λ/let/if/match/list/cons/pair/single-infix + types + patterns as needed for those exprs; round-trip through lower on hand-ish programs.

**Phase B — program:** `type` + top-level `let` + trailing body; wire to `Surface.Program`.

Design is complete for both; PRs can still split A then B.

## Testing strategy

- Lexer unit cases: comments (incl. nesting), unicode/emoji idents, negative ints, tab rejection, op vs `->` vs `-` disambiguation.
- Parser golden strings → `Surface.Expr` / `Program` (Repr or pretty).
- A few end-to-end: parse → lower → infer/eval on tiny programs (reuse existing bridge entry points).

## Open implementation choices (non-blocking)

- Keep whitespace as tokens vs skip-while-tracking position
- Exact keyword set and whether `match`/`with`/`type`/`let`/`in`/`if`/`then`/`else` are the full hard set
- How aggressively to share layout helpers between `let` and `match`

## References

- Library: [fgdorais/lean4-parser](https://github.com/fgdorais/lean4-parser) (`@fgdorais/Parser`)
- Indent precedent: YlangYlang column blocks; Tigris `indentCol` / `colGt` on lean4-parser
- Existing AST: `FHM/SurfaceLang.lean`; lowering: `FHM/SurfaceBridge.lean`
