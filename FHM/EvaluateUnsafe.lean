import FHM.Core

/-!
# Unbounded evaluator driver + fuel bridges

Staging file (keep out of `Core` for now):

1. **Fuel ↔ `Step*` bridges** for the existing total `evaluate`.
2. **`evaluateUnsafe`** — `partial` loop on `step`; `Option` for stuck/diverge.
3. **`evaluateUnsafeTyped`** — same loop under typing + exhaustiveness; stuck is
   impossible (`False.elim`), so the return type is plain `Expr` (still `partial`
   for divergence; see the def’s docstring on why a value-subtype won’t work).
-/

namespace SmallStep

/-! ## Helpers for the fuel bridges -/

private theorem IsCtorChain.to_IsValue {e : Expr} (h : IsCtorChain e) : IsValue e := by
  cases h with
  | ctor name => exact .ctor name
  | app hch hv => exact .ctorApp hch hv

/-- Values do not take a step. (Prop-level; `Core`'s `isValue_step_none` is private.) -/
theorem not_IsValue_of_Step {e e' : Expr} (h : Step e e') : ¬ IsValue e := by
  induction h with
  | beta _ =>
    intro hv
    cases hv with
    | ctorApp hch _ => exact nomatch hch
  | letReduce => intro hv; exact nomatch hv
  | matchReduce _ _ _ => intro hv; exact nomatch hv
  | matchWildReduce _ _ => intro hv; exact nomatch hv
  | letRecUnfold => intro hv; exact nomatch hv
  | deltaIntAdd | deltaIntSub | deltaIntLt | deltaCharLt =>
    intro hv
    cases hv with
    | ctorApp hch _ =>
      cases hch with
      | app hch' _ => exact nomatch hch'
  | appFn _ ih =>
    intro hv
    cases hv with
    | ctorApp hch _ => exact ih hch.to_IsValue
    | primBinOpPartial _ => exact ih (.primBinOp _)
  | appArg _ _ ih =>
    intro hv
    cases hv with
    | ctorApp _ hva => exact ih hva
    | primBinOpPartial hva => exact ih hva
  | matchScrut _ ih => intro hv; exact nomatch hv

/-! ## Fuel `evaluate` ↔ multi-step `Step` -/

/-- Soundness: a successful fuel-bounded run reaches a value via `Step*`. -/
theorem evaluate_sound {fuel : Nat} {e v : Expr}
    (h : evaluate fuel e = some v) :
    IsValue v ∧ Relation.ReflTransGen Step e v := by
  induction fuel generalizing e with
  | zero =>
    simp only [evaluate] at h
    split at h
    · rename_i hv
      simp only [Option.some.injEq] at h
      subst h
      exact ⟨isValue_iff_IsValue.mp hv, .refl⟩
    · exact nomatch h
  | succ n ih =>
    simp only [evaluate] at h
    split at h
    · rename_i hv
      simp only [Option.some.injEq] at h
      subst h
      exact ⟨isValue_iff_IsValue.mp hv, .refl⟩
    · match hs : step e with
      | none => simp [hs] at h
      | some e' =>
        simp [hs] at h
        obtain ⟨hv, hstar⟩ := ih h
        exact ⟨hv, .head (step_sound hs) hstar⟩

/-- Completeness: any finite `Step*` path to a value is realized by some fuel. -/
theorem evaluate_complete {e v : Expr}
    (hstar : Relation.ReflTransGen Step e v) (hv : IsValue v) :
    ∃ fuel, evaluate fuel e = some v := by
  induction hstar using Relation.ReflTransGen.head_induction_on with
  | refl =>
    refine ⟨0, ?_⟩
    simp [evaluate, isValue_iff_IsValue.mpr hv]
  | head hstep _ ih =>
    expose_names
    obtain ⟨n, hn⟩ := ih
    refine ⟨n + 1, ?_⟩
    have hs := step_complete hstep
    have hnv : isValue a = false := by
      cases h : isValue a with
      | false => rfl
      | true => exact absurd (isValue_iff_IsValue.mp h) (not_IsValue_of_Step hstep)
    simpa [evaluate, hnv, hs] using hn

theorem evaluate_isValue {fuel : Nat} {e v : Expr}
    (h : evaluate fuel e = some v) : IsValue v :=
  (evaluate_sound h).1

/-! ## Unbounded driver -/

/-- Keep stepping until a value or a stuck non-value.

This is the informal “infinite fuel” runner: its body is visibly just a loop over
the trusted one-step function `step`. Lean will not give kernel equations for a
`partial def`, so prove things about `evaluate` / `Step` instead; use this for
`#eval` / demos where a fixed fuel bound is awkward. -/
partial def evaluateUnsafe : Expr → Option Expr
  | e =>
    if isValue e then some e
    else match step e with
      | some e' => evaluateUnsafe e'
      | none => none

/-- Like `evaluateUnsafe`, but for a closed well-typed exhaustive term: progress
rules out stuck states, so this returns a definite `Expr` rather than `Option`
(still `partial` — divergence is allowed).

`ctx.env = []` is baked into the `TypeOfElabHM ⟨[], ctors⟩` hypothesis (same
shape as `type_safety` / `type_safety_star`).

**Why not `{ v // IsValue v ∧ TypeOfElabHM … v τ }`?** A `partial` definition’s
return type must be `Nonempty` (Lean needs a junk inhabitant for the opaque
constant). That subtype is only inhabited when evaluation terminates, which we
cannot prove in general — so Lean rejects it. The proofs here still earn
something real: they make the stuck/`none` branch a `False.elim`. Informally,
any value this returns is a typed `IsValue`; the kernel just won’t package that
into the return type of a `partial`. -/
partial def evaluateUnsafeTyped {ctors : CtorEnv} {τ : Ty} (e : Expr)
    (h_ty : TypeOfElabHM ⟨[], ctors⟩ e τ)
    (h_exh : AllMatchesExhaustive ctors e) : Expr :=
  if hval : isValue e = true then e
  else
    match hs : step e with
    | some e' =>
      have hstep := step_sound hs
      evaluateUnsafeTyped e'
        (TypeOfElabHM.preservation hstep h_ty)
        (Step.preserves_exhaustive h_exh hstep)
    | none =>
      False.elim <| by
        have nval : ¬ IsValue e := by
          intro hv
          simp [isValue_iff_IsValue.mpr hv] at hval
        match TypeOfElabHM.progress h_ty rfl h_exh with
        | .inl hv => exact nval hv
        | .inr ⟨_, hstep⟩ => simp [step_complete hstep] at hs

end SmallStep
