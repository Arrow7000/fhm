<!-- Written 2026-07-20 after stdlib/let pretty polish; points at elem+type-poly plan. -->

# Next-agent brief: BLSketch element types + type polymorphism

**Do not start coding in a drive-by chat.** This is a dedicated-session change.

**Plan (execute this):** [`docs/superpowers/plans/2026-07-20-blsketch-elem-poly.md`](../docs/superpowers/plans/2026-07-20-blsketch-elem-poly.md)  
**Design memo:** [`docs/superpowers/specs/2026-07-20-blsketch-elem-poly-design.md`](../docs/superpowers/specs/2026-07-20-blsketch-elem-poly-design.md)  
**Prior BL×Z3 brief (still authoritative for bounds/Z3):** [`next-agent-brief-blsketch-z3.md`](next-agent-brief-blsketch-z3.md)

## One-liner

Add `BL lo hi α` and prenex schemes over `{Nat, Type}` with explicit `@` for both; make `nil` a type scheme; keep Z3 bounds layer and skip inference / elem-subtyping / `letRec`.

## Locked for this effort

| Area | Decision |
| --- | --- |
| Element | `Ty.bl lo hi elem` |
| Type poly | Rigid type binders in schemes; **explicit** `@` only |
| Scheme pretty | `∀ {a b : Nat, α β : Type}. …` (braces = scheme binders) |
| Instantiation | Single `@` spine; kind matches next binder |
| `nil` | Scheme `∀ {α}. BL 0 0 α`, not synthesizing bare `.nil` |
| `Sub` on elem | Equality only |
| Out of scope | Inference, elem-subtyping, `letRec`, Surface/Core wiring |

## Pre-req state (already on `main`)

- Bounds spine + `synth_sound` / `check_sound`
- Pretty + `scratch/blsketch_synth_demos.lean` with `Demo.Stdlib` (Unit-only)
- Multiline let pretty; `head : ∀ a b. BL (a+1) b → Unit`

## Verify before / after

```bash
lake build FHMZ3
lake env lean scratch/blsketch_synth_demos.lean   # needs z3
```
