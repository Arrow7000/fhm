# Plan: BLSketch `BL lo hi α` + mixed Nat/Type schemes

**Brief:** [`briefs/next-agent-brief-blsketch-elem-poly.md`](../../../briefs/next-agent-brief-blsketch-elem-poly.md)  
**Design:** [`../specs/2026-07-20-blsketch-elem-poly-design.md`](../specs/2026-07-20-blsketch-elem-poly-design.md)

Parent agent owns API shape and theorem *statements*. Prefer lean-lsp-mcp over full builds mid-phase; farm proof/impl bodies to Composer 2.5 (Grok 4.5 if needed). See the brief’s **Workflow** section.

## Phases

### Phase A — Grammar (`elem` + `tbind`), Unit-hardwired

**Touch:** `FHM/BLSketch.lean`, `FHM/BLSketch/Pretty.lean`

- Change `Ty` to:
  ```lean
  | unit | tbind (i : Nat) | arrow … | bl (lo hi : Count) (elem : Ty)
  ```
- Thread `elem` through `AnnoTy`, `Ground`/`fold` (counts only), `DemandOK`, `BinderRigid`, `obsBounds`, etc.
- Temporary: every former `BL` site uses `elem := .unit` so behaviour matches today. **Don’t** change `BScheme` yet.
- Pretty: `BL 0 5 Unit`, `BL a b α`.

**Gate:** file elaborates under LSP; old demos still make sense.  
**Commit:** `feat(bl): BL lo hi carries element type (Unit-hardwired)`

---

### Phase B — Mixed schemes + kinded `@`

**Touch:** `BLSketch.lean` (schemes/subst/var), Pretty, demo call sites

```lean
inductive SchemeBinder where | count | type
inductive SchemeArg where
  | count : Count → SchemeArg
  | ty : Ty → SchemeArg

structure BScheme where
  binders : List SchemeBinder  -- v1: counts then types
  body : Ty
```

- WF: count rigids `< #counts`, `tbind i` with `i < #types`
- `InstantiatesTo` / `instantiate?` kind-check the spine
- `Expr.var idx (args : List SchemeArg)`
- Pretty: `∀ {a b : Nat, α : Type}. …` and `x @2 @Unit`
- Migrate `idScheme` / `flatMapScheme` / demos to `.count …` args

**Gate:** demos green with count-only schemes under the new representation.  
**Commit:** `feat(bl): mixed Nat/Type scheme binders with kinded @`

---

### Phase C — Element-accurate cons/match; `nil` scheme; Bool; stdlib

**Touch:** `TypeOf`/`synth`/`consCtx`/`Sub.bl`, demos `Demo.Stdlib`

1. **cons / match:** head has type `elem`; `consCtx` binds `elem` then `BL (pred lo) (pred hi) elem`; `Sub.bl` requires `elem = elem'`.
2. **nil:** add `nilScheme`; remove successful `TypeOf.nil` / `synth .nil`. Demos use `nil @Unit` / `nil @Bool`.
3. **Bool:** `Ty.bool` + minimal intros (`tt`/`ff` or similar) — required, not optional.
4. **Stdlib bodies** (schemes + real exprs):
   - `singleton : ∀ {α}. α → BL 1 1 α`
   - `cons : ∀ {a b : Nat, α}. α → BL a b α → BL (a+1) (b+1) α`
   - `head : ∀ {a b : Nat, α}. BL (a+1) b α → α`
   - `tail : ∀ {a b : Nat, α}. BL (a+1) (b+1) α → BL a b α`
5. **Demos:** positive typed pipeline; negative `cons unit (nil @Bool)` fails.
6. **Proofs:** repair `synth_sound` / `check_sound` for touched rules only — parent states the lemmas, subagent fills proofs when split is clear.

**Gate:** `#eval` demos show the story; soundness OK.  
**Commit:** `feat(bl): typed nil/cons/match; Bool; stdlib schemes`

---

### Phase D — Docs

- Update `briefs/next-agent-brief-blsketch-z3.md` locked table with the new decisions + pointer here.
- Final `lake build FHMZ3` + run synth + z3 demos.
- **Commit:** `docs(bl): lock elem/type-poly in BLSketch brief`

## Out of scope

Type inference · elem-subtyping · `letRec` / recursive map/filter/flatMap · Surface/Core · nested scheme LN

## Risks

| Risk | Mitigation |
| --- | --- |
| `BLSketch.lean` mechanical blast radius | Phase A hardwires `Unit` first; keep diffs reviewable |
| `synth_sound` case explosion | Touch only broken cases; farm proofs |
| List sugar vs no-synth `.nil` | Pretty may still show `[]`; construction goes through `nil @α` / cons |
| Binder-order confusion | Locked counts-then-types; Pretty and `@` must agree |
