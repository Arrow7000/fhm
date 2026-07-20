# Design: BLSketch element types + mixed Nat/Type schemes

**Date:** 2026-07-20  
**Status:** Agreed — implement in a dedicated session  
**Plan:** [`../plans/2026-07-20-blsketch-elem-poly.md`](../plans/2026-07-20-blsketch-elem-poly.md)

## Why

`BL lo hi` is secretly `BL lo hi Unit`. Fine for bounds demos; not fine for stdlib or for rejecting a `Unit` consed onto a non-`Unit` list.

We have count/`Nat` schemes. We need type/`Type` binders too — explicitly instantiated, no inference in v1.

## Decisions

| Decision | Detail |
| --- | --- |
| `BL lo hi elem` | `elem : Ty` (nested BL allowed by grammar; demos stay shallow) |
| Type vars | `Ty.tbind i`, index space **separate** from count rigids `a,b,…` |
| Telescope | **All count binders, then all type binders** — keeps subst/pretty simple |
| Pretty | `∀ {a b : Nat, α β}. body` — braces = scheme binders (≠ term `λ`); **no** `: Type` annotation (HM + bounds, not dependent types) |
| Instantiation | `Expr.var i (args : List SchemeArg)`; `@` spine follows binder order (`f @2 @5 @Unit`) |
| `nil` | `nilScheme : ∀ {α}. BL 0 0 α`. Keep `Expr.nil` for list-pretty sugar if useful, but **no** `TypeOf`/`synth` success for bare `.nil` |
| Element `Sub` | `elem = elem'` only |
| Second base | Add `Bool` (+ intros). Needed to show `cons unit (nil @Bool)` fails; also the natural predicate result for a future `filter` (which still needs `letRec`) |

## Deliberately not doing

Type inference / generalization · element subtyping · `letRec` · FHM Core/Surface wiring · base-sort hacks without type ∀

## Soft spots (implementer judgment OK)

- Exact names (`SchemeBinder` vs `BinderKind`, …)
- How aggressively to farm `synth_sound` case repairs to subagents

## Locked in session (2026-07-20)

- Keep `Expr.nil` for `[]` pretty; bare `.nil` does not synth (Phase C). No special expected-type check in v1 — use `nil @α`. Revisit if demos hurt.
- `AnnoTy.bl`: bound holes only; **elem is always a concrete `Ty`** (no type inference in this toy).
- Bool intros: bare `Expr.true` / `Expr.false`.
- Phase-gate pings after each plan phase (ready vs need input).

## Explicitly deferred (do not “fix” in this stage)

| Item | v1 | Later |
| --- | --- | --- |
| Elem subtyping | `Sub` / join / `subConstraints` use **`elem = elem'` only** | Recursive `Sub` on element types |
| Bare-`nil` under expected type | Fails (synth-then-`Sub` check) | Optional special `Check` rule |
| Type inference / gen | Explicit `@` | — |
| `letRec` / recursive stdlib | Axiom signatures only | — |
| Nested scheme LN | Story A prenex | — |
