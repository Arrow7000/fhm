# Design: BLSketch element types + mixed Nat/Type schemes

**Date:** 2026-07-20  
**Plan:** `docs/superpowers/plans/2026-07-20-blsketch-elem-poly.md`  
**Status:** Agreed for a dedicated implementation session (not started).

## Problem

Today `BL lo hi` hard-wires element type `Unit`. That is enough to demo bounds, but not enough for a believable stdlib (`nil`, `cons`, `map`, …) or for rejecting `cons () xs` when `xs` is not a list of `Unit`.

We already have **bounds polymorphism** (`BScheme` over `Nat`). We do **not** have type polymorphism.

## Decision

Smallest serious step (no inference):

1. **`Ty.bl lo hi elem`** with `elem : Ty`.
2. **Rigid type binders** in schemes (`Ty.tbind i`), parallel to rigid count binders.
3. **Mixed prenex schemes** — telescope of `Nat` and `Type` binders.
4. **Explicit instantiation** — one `@`-spine; each arg is a `Count` or a `Ty` according to the next binder.
5. **`nil` is a scheme** `∀ {α : Type}. BL 0 0 α`, not a synthesizing nullary constant.
6. **`Sub` on elements = equality** (no elem-subtyping in v1).

## Pretty / surface conventions (toy AST, not a parser yet)

- Schemes: `∀ {a b : Nat, α β : Type}. body` — braces mark *scheme* binders (vs term `λ(x : τ)`).
- Apps: `nil @Unit`, `cons @2 @5 @Unit`, `map @Unit @Bool @0 @3` — same `@` for both sorts.

## Non-goals (this effort)

- Type inference / generalization
- Element subtyping
- `letRec` / recursive stdlib bodies
- Wiring into FHM Core / Surface

## Why not “base sorts only” without type ∀

Annotating every `nil` or monomorphizing `nilInt` / `headInt` works for a tiny demo but will not scale to one `map`/`head`. Prefer real (explicit) type binders from the start.
