<!-- Written 2026-07-20. Handoff for a dedicated session — landed on main the same day. -->

# Next-agent brief: BLSketch element types + type polymorphism

**Status:** **Done** on `main` (Phases A–D).  
**Plan:** [`docs/superpowers/plans/2026-07-20-blsketch-elem-poly.md`](../docs/superpowers/plans/2026-07-20-blsketch-elem-poly.md)  
**Design:** [`docs/superpowers/specs/2026-07-20-blsketch-elem-poly-design.md`](../docs/superpowers/specs/2026-07-20-blsketch-elem-poly-design.md)  
**Bounds/Z3 context (updated locks):** [`next-agent-brief-blsketch-z3.md`](next-agent-brief-blsketch-z3.md)

## Goal (achieved)

`BL lo hi α` + prenex schemes over `Nat` and `Type` with explicit `@` for both. `nil` is a type scheme. Z3 bounds layer unchanged. No inference, no elem-subtyping, no `letRec`.

## Locked (still)

| | |
| --- | --- |
| Element | `Ty.bl lo hi elem` |
| Type binders | `Ty.tbind i` — separate index space from count rigids |
| Scheme telescope | **Counts first, then types** (pretty as `∀ {a b : Nat, α β}. …` — no `: Type`) |
| `@` spine | Same order as binders, e.g. `cons @2 @5 @Unit` |
| `nil` | Scheme `∀ {α}. BL 0 0 α`; bare `Expr.nil` does **not** synth |
| `Sub` on elem | Definitional equality only |
| Second base | `Bool` (`Expr.true` / `Expr.false`) |
| Out of scope | Inference, elem-subtyping, `letRec`, Surface/Core |

## Landed commits (this session)

| | |
| --- | --- |
| `81c6d6a` / `779732c` | Phase A — `elem` + `tbind`, Unit-hardwired; soundness repair |
| `d426851` | Lint cleanup |
| `6153a0e` | Phase B — mixed schemes + kinded `@` |
| `ca1dc54` | `@[simp]` DemandOK / SchemeWF mirrors |
| `5d5bc6e` | Phase C — typed nil/cons/match; Bool; stdlib |
| *(Phase D)* | Z3 brief lock update |

## Explicitly still deferred

Elem subtyping · bare-`nil` under expected type · type/`@` inference · `letRec` · nested scheme LN · Surface/Core
