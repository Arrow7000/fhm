<!-- Written 2026-07-14: follow-ups from the post-6522862 audit (Opus review session). -->

# Next-agent brief: audit follow-ups

**Origin.** Opus review of everything since `6522862` (see `briefs/post-6522862-work-and-models-report.md`).
Verdict: the edifice is sound — every headline is axiom-clean (`{propext, Classical.choice, Quot.sound}`),
definitions are honest and non-vacuous, architecture is textbook-correct (arguably more principled than
average: declarative relations *and* executable functions, proven equivalent, avoiding "well-typed = whatever
the typechecker accepts" circularity). No `sorry`, no custom axioms, no `native_decide` leakage.

The residual issues are **under-connection**, not unsoundness: strong properties proven but not always
cashed out into observable, usable guarantees. This brief captures the follow-ups.

## Workflow (do this)
- **Proven division of labour:** the *parent* (statement author) writes Prop/theorem statements; a *smaller
  subagent* (try **sonnet-5**) fills the proofs. A filled proof can't be unsound (kernel-checked); the only
  risks are `sorry` (detectable) or a too-weak/vacuous *statement* (author's job to avoid).
- **Never commit without the user's say-so. Never add `Co-Authored-By` / self-credit to commits.**
- **`#guard` legibility rule (user preference):** only use `#guard` for *clearly legible equalities*.
  Do NOT use `#guard` whose body is a pattern match with `true`/`false` branches — those are hard to read.
  Prefer `example`/`#eval` otherwise.

---

## Verified in the review session (compiled clean + axiom-clean; NOT yet committed)

These were built and checked via `lake env lean` against `FHM.SurfaceBridge`. Preserve them — they are the
seeds of items 1–2. (Namespaces: `open SurfaceBridge SmallStep`.)

### Inversion lemmas (the "universal properties", stated as first-class results)
```lean
theorem TypeOfHM_app_inv {ctx : Ctx} {f x : Expr} {τ : Ty}
    (h : TypeOfHM ctx (.app f x) τ) :
    ∃ argTy, TypeOfHM ctx f (.arrow argTy τ) ∧ TypeOfHM ctx x argTy := by
  cases h with | app hf hx => exact ⟨_, hf, hx⟩

-- Demonstrates the `of_lowers` overlap: a match-free `.pair` has TWO derivation paths.
theorem SurfaceWTExpr_pair_inv {ctors : CtorEnv} {ke : KindEnv} {tvs vs : List ValName}
    {Γ : Env} {a b : Surface.Expr} {τ : Ty}
    (h : SurfaceWTExpr ctors ke tvs vs Γ (.pair a b) τ) :
    (∃ τa τb, SurfaceWTExpr ctors ke tvs vs Γ a τa ∧ SurfaceWTExpr ctors ke tvs vs Γ b τb ∧
        TypeOfHM ⟨Γ, ctors⟩ (.ctor cPair) (.arrow τa (.arrow τb τ)))
    ∨ (SurfaceExprNoMatch (.pair a b) ∧
        ∃ c, LowersExpr ctors ke tvs vs (.pair a b) c ∧ TypeOfHM ⟨Γ, ctors⟩ c τ) := by
  cases h with
  | pair ha hb hc => exact Or.inl ⟨_, _, ha, hb, hc⟩
  | of_lowers hnm hL hT => exact Or.inr ⟨hnm, _, hL, hT⟩
```

### Witnesses (Finding 1: relations are proven-sound but were never *witnessed*)
```lean
example (ctors : CtorEnv) : SurfaceWT ctors (.primLit (.int 0)) :=
  ⟨.prim .int, .of_lowers .primLit .primLitInt .primLitInt⟩

example (ctors : CtorEnv) :                                     -- identity λx.x (structural lambda)
    SurfaceWTExpr ctors (kindEnvOfCtors ctors) [] [] []
      (.lambda (.name ⟨"x"⟩) none (.var ⟨"x"⟩)) (.arrow (.prim .int) (.prim .int)) := by
  apply SurfaceWTExpr.lambda_name
  · exact ContainsBvarsUpTo.prim
  · trivial
  · exact .of_lowers .var (.var (by rfl))
      (TypeOfHM.var (polyTy := PolyTy.mkTrivial (.prim .int)) (instArgs := []) rfl (by simp) .prim)
```

### `ofFlat ⇒ safe` (composition that actually uses `ValidBindingGroups`)
```lean
theorem ofFlat_safe {decls : List Surface.DataDecl} {binds : List Surface.Binding}
    {body : Surface.Expr} {p : Surface.Program} {ctors : CtorEnv} {c : Expr}
    (hof : Program.ofFlat decls binds body = some p)
    (hlow : lowerProgram p = some (ctors, c))
    (htc : (typecheck ctors c).isSome)
    (hcov : SurfaceCovers ctors p.term) :
    ValidBindingGroups binds p.groups ∧
    ∃ e τ, elaborateProgram p = some e ∧
      TypeOfElabHM ⟨[], ctors⟩ e τ ∧ AllMatchesExhaustive ctors e ∧
      ∀ e', Relation.ReflTransGen Step e e' → (IsValue e' ∨ ∃ e'', Step e' e'') :=
  ⟨Program.ofFlat_groups_valid hof, program_type_safe hlow htc hcov⟩
```

### Safe entry point — SUPERSEDED by the `elaborateSafe` redesign (item 2). Kept for reference:
```lean
def elaborateChecked (p : Surface.Program) : Option Expr :=
  match lowerProgram p with
  | none => none
  | some (ctors, c) =>
    if (typecheck ctors c).isSome && checkExhaustive ctors p.term then elaborateProgram p else none

theorem elaborateChecked_safe {p : Surface.Program} {e : Expr}
    (h : elaborateChecked p = some e) :
    ∃ (ctors : CtorEnv) (τ : Ty),
      TypeOfElabHM ⟨[], ctors⟩ e τ ∧ AllMatchesExhaustive ctors e ∧
      ∀ e', Relation.ReflTransGen Step e e' → (IsValue e' ∨ ∃ e'', Step e' e'') := by
  cases hlp : lowerProgram p with
  | none => simp [elaborateChecked, hlp] at h
  | some pair =>
    obtain ⟨ctors, c⟩ := pair
    simp only [elaborateChecked, hlp] at h
    split at h
    · rename_i hguard
      rw [Bool.and_eq_true] at hguard
      obtain ⟨htc, hexh⟩ := hguard
      have hcov := checkExhaustive_sound p.term hexh
      obtain ⟨e', τ, helab, hty, hexh', hsafe⟩ := program_type_safe hlp htc hcov
      rw [helab, Option.some.injEq] at h; subst h
      exact ⟨ctors, τ, hty, hexh', hsafe⟩
    · exact absurd h (by simp)
```

---

## ITEM 1 — Witnesses for the annotated/poly strong constructors (HIGH priority)

**Why.** `letInAnn` / `letRecInAnn` (the Composer-authored, cofinite-premise ctors) are the least-validated
code: a proof by induction over `SurfaceWTExpr` goes through even if a ctor is *dead* (unsatisfiable
premises). Axiom-cleanliness cannot catch this. A witness proves the ctor is genuinely inhabitable.
The `∀ Xs, FreshNames L σ.paramCount Xs → …` premise + `PolyTy.openVars` are the fiddly part; the RHS is the
identity witness above.

**Statement to prove (author-frozen):** an annotated polymorphic identity let.
```lean
-- `let (id : ∀a. a→a) = λx. x in id`  used at `int→int`
example (ctors : CtorEnv) :
    SurfaceWTExpr ctors (kindEnvOfCtors ctors) [] [] []
      (.letIn (.mk "id")
        (some ⟨[.mk "a"], .arrow (.tvar (.mk "a")) (.tvar (.mk "a"))⟩)
        (.lambda (.name (.mk "x")) none (.var (.mk "x")))
        (.var (.mk "id")))
      (.arrow (.prim .int) (.prim .int)) := by
  apply SurfaceWTExpr.letInAnn
  · rfl                                   -- tvs = []
  · rfl                                   -- lowerPoly ke σs = some σ  (check computes; may need `decide`/`native_decide`)
  · /- PolyTy.WF σ -/ sorry
  · /- ∀ Xs, FreshNames L σ.paramCount Xs → SurfaceWTExpr … rhs (σ.openVars Xs) -/ sorry
  · /- body: id : int→int under (id ↦ σ) — TypeOfHM.var + InstantiatesBy on σ.body -/ sorry
```
The subagent should: inspect `FreshNames`, `PolyTy.openVars`, `PolyTy.WF`, `lowerPoly`, `InstantiatesBy`
(`.bvar` case: `tyArgs[i]? = some ty`); intro `Xs`/freshness; compute `σ.openVars [X] = fvar X → fvar X`;
reuse the identity-lambda proof at `paramTy := .fvar X`. If the poly case resists, first land the *mono*
annotated let `let (x:τ) = v in x` (paramCount 0 ⇒ `Xs = []`, `openVars [] = body`) as a fallback witness,
and record the exact obstruction for the poly one. Do NOT leave `sorry`; either finish or downgrade the goal
to the mono witness and note it.

Also add (nice-to-have): a `letRecInAnn` witness (`let rec (id:∀a.a→a) = λx. x in id`).

---

## ITEM 2 — `FHM/Headlines.lean` (the ergonomic, human-readable capabilities surface)

A new façade module (adds ~no new math; re-exports + light glue) so a newcomer reads ONE file to see what the
language guarantees, what it means, and that it's genuinely axiom-clean. It is standalone-compilable via
`lake env lean FHM/Headlines.lean` (do not add to `lakefile.toml` unless the user asks).

**Sections (in order):**

1. **Doc-narrated headline re-exports** (no proofs, just `/-! -/` prose + the names):
   type safety (`surface_type_safe`, `surface_type_safe_of_SurfaceWT`, `program_type_safe`,
   `TypeOfElabHM.type_safety_star`); inference sound+complete (`Infer.sound`, `Infer.complete'`,
   `UnifyRel.complete`); pattern-compilation correctness (`PatComp.compile_correct_surface`,
   `PatComp.lowerMatch_adequate_of_typed`); decidable coverage (`checkExhaustive_sound`); DataDecl bridge.

2. **Universal properties = inversion / canonical-forms lemmas.** Author-frozen statements (subagent proves;
   most are `intro; cases`). Ship at least: `TypeOfHM_app_inv` (above), `TypeOfHM_lambda_inv`,
   `TypeOfHM_pair_inv` (Core-level: `.app (.app (.ctor cPair) a) b`), `TypeOfHM_letIn_inv`,
   plus re-exported canonical-forms (`TypeOfElabHM.canonical_arrow`, `ctor_chain_inversion`). Keep the
   `SurfaceWTExpr_pair_inv` two-case one as a documented example of the `of_lowers` overlap.

3. **Witnesses** — the item-1 examples (literal, identity, annotated poly id), proving the relations are
   inhabited.

4. **The composable safe pipeline (the `elaborateSafe` redesign — keep type-safety and exhaustiveness as
   independent checks; conjoin only the proofs at the return type):**
   ```lean
   /-- Well-typed (closed) — one of the two orthogonal safety concerns. -/
   def WellTyped (ctors : CtorEnv) (e : Expr) : Prop := ∃ τ, TypeOfElabHM ⟨[], ctors⟩ e τ
   -- (exhaustiveness is the existing `AllMatchesExhaustive ctors e` — the other, orthogonal, concern)

   /-- A passport: a term that passed BOTH independent checks, carrying both proofs. -/
   abbrev Safe (ctors : CtorEnv) := { e : Expr // WellTyped ctors e ∧ AllMatchesExhaustive ctors e }

   /-- Run a whole program through both checks; `some ⟨ctors, ⟨e, _⟩⟩` hands back a term that is
       well-typed AND exhaustive, by construction. -/
   def elaborateSafe (p : Surface.Program) : Option (Σ ctors : CtorEnv, Safe ctors) := …
     -- match lowerProgram p; guard (typecheck …).isSome; guard checkExhaustive …; some e ← elaborate …
     -- build the ⟨WellTyped, AllMatchesExhaustive⟩ proof from `program_type_safe` + `checkExhaustive_sound`
     --   (the `WellTyped` conjunct is the ∃τ typing; exhaustiveness is `checkExhaustive_sound`'s `SurfaceCovers`
     --    pushed through `lower_elab_exhaustive`, exactly as in `program_type_safe`).

   /-- The safe runner: a `Safe` term never gets stuck, so `none` means ONLY "out of fuel". -/
   def runSafe (ctors : CtorEnv) (fuel : Nat) (t : Safe ctors) : Option Expr :=
     SmallStep.evaluate fuel t.val
   theorem runSafe_never_stuck (ctors) (fuel) (t : Safe ctors) {v} (h : runSafe ctors fuel t = some v) :
     IsValue v ∧ ∃ τ, TypeOfElabHM ⟨[], ctors⟩ v τ := …   -- via evaluate_sound + type_safety_star
   ```
   Check `SmallStep.evaluate`'s real signature/`evaluate_sound` before finalizing `runSafe*`.

5. **Demos:** a couple of `#eval (elaborateSafe sProg).isSome` / `#eval` of a run, following `Examples`
   (`sIf`, `sMaybeMatch`, `sAnnId`). Respect the #guard legibility rule.

6. **Living axiom-budget guard:** `#print axioms surface_type_safe` etc. (comment the expected
   `{propext, Classical.choice, Quot.sound}`); or `example : True := by …` guards. No `native_decide`.

---

## ITEMS 3–5 (future sessions — regroup first)

3. **`ValidBindingGroups → well-scoped/lowerable` bridge** (medium): the theorem that makes the 2,400-line SCC
   proof "matter" — a valid grouping desugars to a well-scoped term (no unbound group refs). Deeper/harder:
   grouping-invariance (any two valid groupings elaborate observationally-equally).
4. **`typecheck ⇒ SurfaceWT` completeness** (hard): makes the declarative and executable notions provably
   coincide; unifies the two safety headlines.
5. **Cosmetics batch:** restrict `of_lowers` to true leaves (var/ctor/primLit) — kills the inversion
   double-case; NOT a soundness item (verified: `SurfaceExprNoMatch` is an explicit no-catch-all inductive, so
   future ctors can't sneak unsoundness in). Remove unused `_hcov` in `typecheck_of_lower_of_SurfaceWT`. Split
   the 9.7k-line `SurfaceBridge.lean`. Drop `tvs = []` on annotated-let ctors (low pri; always satisfied under
   closed `SurfaceWT`).

Also separate: **compile-time simplification** — see `briefs/next-agent-brief-compile-time-simplify.md`.
