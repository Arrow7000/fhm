import FHM.Bounds.Typing

/-! # Solver-independent bounds subtyping

This is the semantic target for the restored bounds checker, not yet a
replacement for the legacy `Sub`/`HasBounds` API. Arithmetic validity belongs
in the specification; `DemandOK` and positive solver verdicts belong in the
algorithm. In particular, strengthening assumptions must not require another
successful solver call.
-/

namespace FHM.Bounds

/-- Structural bounds subtyping with semantic interval inclusion. Unlike legacy
    `Sub`, this relation imposes no algorithmic demand-fragment restriction. -/
inductive SemanticSub (Δ : List Constraint) : BoundsTy → BoundsTy → Prop where
  | prim {p} : SemanticSub Δ (.prim p) (.prim p)
  | bvar {i} : SemanticSub Δ (.bvar i) (.bvar i)
  | fvar {i} : SemanticSub Δ (.fvar i) (.fvar i)
  | arrow {a a' b b'} :
      SemanticSub Δ a' a → SemanticSub Δ b b' →
      SemanticSub Δ (.arrow a b) (.arrow a' b')
  | list {lo hi lo' hi' e e'} :
      (Interval.subGoals Δ ⟨lo, hi⟩ ⟨lo', hi'⟩).Valid →
      SemanticSub Δ e e' →
      SemanticSub Δ (.list lo hi e) (.list lo' hi' e')
  | custom {name as bs} :
      List.Forall₂ (SemanticSub Δ) as bs →
      SemanticSub Δ (.custom name as) (.custom name bs)

private theorem interval_refl (Δ : List Constraint) (lo hi : Count) :
    (Interval.subGoals Δ ⟨lo, hi⟩ ⟨lo, hi⟩).Valid := by
  intro σ _ g hg
  simp [Interval.subGoals] at hg
  rcases hg with rfl | rfl
  · change ExtNat.le (lo.eval σ) (lo.eval σ)
    cases lo.eval σ <;> simp [ExtNat.le]
  · change ExtNat.le (hi.eval σ) (hi.eval σ)
    cases hi.eval σ <;> simp [ExtNat.le]

theorem SemanticSub.refl (Δ : List Constraint) (β : BoundsTy) :
    SemanticSub Δ β β := by
  refine BoundsTy.rec
    (motive_1 := fun β => SemanticSub Δ β β)
    (motive_2 := fun as => List.Forall₂ (SemanticSub Δ) as as)
    (fun _ => .prim)
    (fun _ _ ha hb => .arrow ha hb)
    (fun _ => .bvar)
    (fun _ => .fvar)
    (fun lo hi _ he => .list (interval_refl Δ lo hi) he)
    (fun _ _ hargs => .custom hargs)
    List.Forall₂.nil
    (fun _ _ hh ht => List.Forall₂.cons hh ht)
    β

mutual
  /-- Existing subtype derivations are semantically sound, conditional only on
      the existing positive-verdict oracle contract. No converse is claimed. -/
  theorem Sub.semantic {Δ a b} (h : Sub Δ a b) : SemanticSub Δ a b := by
    cases h with
    | prim => exact .prim
    | bvar => exact .bvar
    | fvar => exact .fvar
    | arrow ha hb => exact .arrow ha.semantic hb.semantic
    | list _ _ hv he => exact .list (checkValid_sound _ hv) he.semantic
    | list_refl he => exact .list (interval_refl _ _ _) he.semantic
    | custom hs => exact .custom (subAll_semantic hs)
  termination_by sizeOf a + sizeOf b

  private theorem subAll_semantic {Δ as bs}
      (h : List.Forall₂ (Sub Δ) as bs) :
      List.Forall₂ (SemanticSub Δ) as bs := by
    cases h with
    | nil => exact .nil
    | cons hh ht => exact .cons hh.semantic (subAll_semantic ht)
  termination_by sizeOf as + sizeOf bs
end

mutual
  /-- Strengthening path assumptions preserves semantic subtyping, even when
      the executable solver would return `unknown` for the new query. -/
  theorem SemanticSub.strengthen {Δ Δ' a b} (h : SemanticSub Δ a b)
      (hpre : ∀ c ∈ Δ, c ∈ Δ') : SemanticSub Δ' a b := by
    cases h with
    | prim => exact .prim
    | bvar => exact .bvar
    | fvar => exact .fvar
    | arrow ha hb => exact .arrow (ha.strengthen hpre) (hb.strengthen hpre)
    | list hv he => exact .list (hv.strengthen hpre) (he.strengthen hpre)
    | custom hs => exact .custom (semanticAll_strengthen hs hpre)
  termination_by sizeOf a + sizeOf b

  private theorem semanticAll_strengthen {Δ Δ' as bs}
      (h : List.Forall₂ (SemanticSub Δ) as bs)
      (hpre : ∀ c ∈ Δ, c ∈ Δ') :
      List.Forall₂ (SemanticSub Δ') as bs := by
    cases h with
    | nil => exact .nil
    | cons hh ht => exact .cons (hh.strengthen hpre) (semanticAll_strengthen ht hpre)
  termination_by sizeOf as + sizeOf bs
end

mutual
  /-- A caller may use a derivation under different assumptions only after
      establishing all of its original premises. Mere instantiation or scope
      validation does not provide these facts. -/
  theorem SemanticSub.assuming {Δ Δ' a b} (h : SemanticSub Δ a b)
      (hpre : (⟨Δ', Δ⟩ : ForallProblem).Valid) : SemanticSub Δ' a b := by
    cases h with
    | prim => exact .prim
    | bvar => exact .bvar
    | fvar => exact .fvar
    | arrow ha hb => exact .arrow (ha.assuming hpre) (hb.assuming hpre)
    | list hv he =>
        exact .list (by
          intro σ hp g hg
          exact hv σ (hpre σ hp) g hg) (he.assuming hpre)
    | custom hs => exact .custom (semanticAll_assuming hs hpre)
  termination_by sizeOf a + sizeOf b

  private theorem semanticAll_assuming {Δ Δ' as bs}
      (h : List.Forall₂ (SemanticSub Δ) as bs)
      (hpre : (⟨Δ', Δ⟩ : ForallProblem).Valid) :
      List.Forall₂ (SemanticSub Δ') as bs := by
    cases h with
    | nil => exact .nil
    | cons hh ht => exact .cons (hh.assuming hpre) (semanticAll_assuming ht hpre)
  termination_by sizeOf as + sizeOf bs
end

mutual
  theorem SemanticSub.trans {Δ a b c} (hab : SemanticSub Δ a b)
      (hbc : SemanticSub Δ b c) : SemanticSub Δ a c := by
    cases hab with
    | prim => cases hbc; exact .prim
    | bvar => cases hbc; exact .bvar
    | fvar => cases hbc; exact .fvar
    | arrow ha hb =>
        cases hbc with
        | arrow ha' hb' => exact .arrow (ha'.trans ha) (hb.trans hb')
    | list hv he =>
        cases hbc with
        | list hv' he' => exact .list (Interval.subGoals_valid_trans hv hv') (he.trans he')
    | custom hs =>
        cases hbc with
        | custom hs' => exact .custom (semanticAll_trans hs hs')
  termination_by sizeOf a + sizeOf b + sizeOf c

  private theorem semanticAll_trans {Δ as bs cs}
      (hab : List.Forall₂ (SemanticSub Δ) as bs)
      (hbc : List.Forall₂ (SemanticSub Δ) bs cs) :
      List.Forall₂ (SemanticSub Δ) as cs := by
    cases hab with
    | nil => cases hbc; exact .nil
    | cons hh ht =>
        cases hbc with
        | cons hh' ht' => exact .cons (hh.trans hh') (semanticAll_trans ht ht')
  termination_by sizeOf as + sizeOf bs + sizeOf cs
end

#print axioms SemanticSub.refl
#print axioms Sub.semantic
#print axioms SemanticSub.strengthen
#print axioms SemanticSub.assuming
#print axioms SemanticSub.trans

end FHM.Bounds
