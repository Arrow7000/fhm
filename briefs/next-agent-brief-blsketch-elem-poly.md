<!-- Written 2026-07-20. Handoff for a dedicated session — not a drive-by. -->

# Next-agent brief: BLSketch element types + type polymorphism

**Plan:** [`docs/superpowers/plans/2026-07-20-blsketch-elem-poly.md`](../docs/superpowers/plans/2026-07-20-blsketch-elem-poly.md)  
**Design:** [`docs/superpowers/specs/2026-07-20-blsketch-elem-poly-design.md`](../docs/superpowers/specs/2026-07-20-blsketch-elem-poly-design.md)  
**Bounds/Z3 context (still authoritative):** [`next-agent-brief-blsketch-z3.md`](next-agent-brief-blsketch-z3.md)

## Goal

`BL lo hi α` + prenex schemes over `Nat` and `Type` with explicit `@` for both. `nil` becomes a type scheme. Z3 bounds layer unchanged. No inference, no elem-subtyping, no `letRec`.

## Workflow (read this)

1. **Lean feedback:** Prefer **lean-lsp-mcp** (`lean_diagnostic_messages`, `lean_goal`, …) over `lake build`. Full builds / `lake env lean …` only when imports are stale, at the end of a chunky phase, or when you need `#eval` demo output. Same spirit as `.cursor/rules/lean-workflow.mdc`.

2. **Parent designs, subagents prove:** When the work splits cleanly, **you** write the definitions, `Prop`s, and theorem *statements* (and the key API shape). Hand **implementations / proof bodies** to a subagent:
   - default: **Composer 2.5**
   - if stuck: **Grok 4.5**
   - If there’s no clean statement/proof split (tangled API migration, Pretty, demos), keep key design decisions yourself and still farm mechanical fallout when it’s worth it.

3. **Commits:** One commit per phase in the plan (or logical sub-phase). Don’t mix doc churn with proof repairs unless tiny.

## Locked

| | |
| --- | --- |
| Element | `Ty.bl lo hi elem` |
| Type binders | `Ty.tbind i` — separate index space from count rigids |
| Scheme telescope | **Counts first, then types** (pretty as `∀ {a b : Nat, α β : Type}. …`) |
| `@` spine | Same order as binders, e.g. `cons @2 @5 @Unit` |
| `nil` | Scheme `∀ {α : Type}. BL 0 0 α`; bare `Expr.nil` does **not** synth |
| `Sub` on elem | Definitional equality only |
| Second base | `Bool` (+ tiny intro forms) required for mismatch demos |
| Out of scope | Inference, elem-subtyping, `letRec`, Surface/Core |

## Starting point on `main`

Bounds spine + soundness; Pretty; `scratch/blsketch_synth_demos.lean` with `Demo.Stdlib` (still Unit-only / count-only schemes).

## Done when

- Demos show typed `nil`/`cons`/`head`/`tail` with `@`
- Element mismatch fails visibly (`Unit` into `BL _ _ Bool`)
- `synth_sound` / `check_sound` still hold for touched rules
- Z3 brief updated with the new locks
