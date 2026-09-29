import FHM.InferW

/-!
# Completeness for Hindley--Milner inference

The foundational sections establish the renaming infrastructure, structural
unification completeness, and gap avoidance needed by the principality proof.

## Contents

1. α-renaming / swap / block-swap kit.
2. Unification completeness: `UnifyRel.complete` / `complete_K` (the
   rigidity-aware relational form) and the executable twins
   `unifyCoreK_complete` / `unify_complete`.
3. Gap-avoidance family: domain/range locality of `Infer` substitutions
   (`Infer.gap_avoid`, `InferBranches.gap_avoid`, `InferRecGroup.gap_avoid`),
   ported onto the monomorphic recursive-group relation and ceiling-based
   `letRec` body environment.
-/

set_option maxHeartbeats 1600000

/-! ## 1. The renaming / swap / block-swap kit

Injective renamings dodge the fresh-binder obstruction: a clean override of
`S₀` mapping a fresh var to the declarative type is unrealisable as a `List`
substitution once the fresh var occurs in `S₀`'s range; swapping it away with
a fresh name restores cleanliness. Type-level only; ported nearly verbatim
-/

mutual
/-- Relabel every free type variable by `f`. An α-renaming when `f` is injective. -/
def Ty.rename (f : Nat → Nat) : Ty → Ty
  | .prim p          => .prim p
  | .arrow a b       => .arrow (a.rename f) (b.rename f)
  | .bvar i          => .bvar i
  | .fvar n          => .fvar (f n)
  | .customTy nm tys => .customTy nm (TyList.rename f tys)

private def TyList.rename (f : Nat → Nat) : List Ty → List Ty
  | []       => []
  | hd :: tl => hd.rename f :: TyList.rename f tl
end

/-! The range guard's orientation lemma.  The executable unifier is called
with the annotation opening on the right and that opening protected in its
rigid set.  Consequently any returned substitution which avoids the protected
set can only put protected variables in its raw images. -/

mutual
theorem UnifyRel.range_within_rhs {K : List Nat} :
    {a b : Ty} → {S : Subst} → UnifyRel a b S →
    (∀ p ∈ S, p.1 ∉ K) →
    (∀ x ∈ b.freeVars, x ∈ K) →
    ∀ p ∈ S, ∀ x ∈ p.2.freeVars, x ∈ K
  | _, _, _, .prim, _, _, p, hp, x, hx => by simp at hp
  | _, _, _, .fvarRefl, _, _, p, hp, x, hx => by simp at hp
  | _, _, _, @UnifyRel.fvarL n t _ _, hav, hb, p, hp, x, hx => by
      rw [List.mem_singleton] at hp
      subst p
      exact hb x hx
  | _, _, _, @UnifyRel.fvarR n t _ _, hav, hb, p, hp, x, hx => by
      have hn : n ∈ K := hb n (by simp [Ty.freeVars])
      exact False.elim (hav (n, t) (by simpa using hp) hn)
  | _, _, _, @UnifyRel.arrow a b c d S₁ S₂ h₁ h₂, hav, hright, p, hp, x, hx => by
      have hc : ∀ y ∈ c.freeVars, y ∈ K :=
        fun y hy => hright y (Ty.mem_freeVars_arrowL hy)
      have hd : ∀ y ∈ d.freeVars, y ∈ K :=
        fun y hy => hright y (Ty.mem_freeVars_arrowR hy)
      have hav₁ : ∀ q ∈ S₁, q.1 ∉ K := fun q hq =>
        hav q (List.mem_append_left _ hq)
      have hav₂ : ∀ q ∈ S₂, q.1 ∉ K := fun q hq =>
        hav q (List.mem_append_right _ hq)
      have h₁range := UnifyRel.range_within_rhs h₁ hav₁ hc
      have hd_fixed : S₁.onTy d = d :=
        Ty.substFvars_eq_self_of_no_key (fun q hq hy => hav₁ q hq (hd q.1 hy))
      rw [List.mem_append] at hp
      rcases hp with hp | hp
      · exact h₁range p hp x hx
      · have h₂range := UnifyRel.range_within_rhs h₂ hav₂ (by
          intro y hy
          rw [hd_fixed] at hy
          exact hd y hy)
        exact h₂range p hp x hx
  | _, _, _, @UnifyRel.customTy nm as bs S hs, hav, hright, p, hp, x, hx => by
      exact UnifyRelList.range_within_rhs hs hav (by
        intro t ht y hy
        exact hright y (Ty.mem_freeVars_customTy ht hy)
        ) p hp x hx

theorem UnifyRelList.range_within_rhs {K : List Nat} :
    {as bs : List Ty} → {S : Subst} → UnifyRelList as bs S →
    (∀ p ∈ S, p.1 ∉ K) →
    (∀ t ∈ bs, ∀ x ∈ t.freeVars, x ∈ K) →
    ∀ p ∈ S, ∀ x ∈ p.2.freeVars, x ∈ K
  | _, _, _, .nil, _, _, p, hp, x, hx => by simp at hp
  | _, _, _, @UnifyRelList.cons a b as bs S₁ S₂ h₁ h₂, hav, hright, p, hp, x, hx => by
      have hb : ∀ y ∈ b.freeVars, y ∈ K := hright b List.mem_cons_self
      have hbs : ∀ t ∈ bs, ∀ y ∈ t.freeVars, y ∈ K :=
        fun t ht => hright t (List.mem_cons_of_mem _ ht)
      have hav₁ : ∀ q ∈ S₁, q.1 ∉ K := fun q hq =>
        hav q (List.mem_append_left _ hq)
      have hav₂ : ∀ q ∈ S₂, q.1 ∉ K := fun q hq =>
        hav q (List.mem_append_right _ hq)
      have h₁range := UnifyRel.range_within_rhs h₁ hav₁ hb
      have hbs_fixed : ∀ t ∈ bs, S₁.onTy t = t := by
        intro t ht
        exact Ty.substFvars_eq_self_of_no_key (fun q hq hy => hav₁ q hq (hbs t ht q.1 hy))
      rw [List.mem_append] at hp
      rcases hp with hp | hp
      · exact h₁range p hp x hx
      · apply UnifyRelList.range_within_rhs h₂ hav₂
          (by
            intro t ht y hy
            obtain ⟨t0, ht0, rfl⟩ := List.mem_map.mp ht
            rw [hbs_fixed t0 ht0] at hy
            exact hbs t0 ht0 y hy) p hp x hx
end

theorem TyList.rename_eq_map (f : Nat → Nat) (tys : List Ty) :
    TyList.rename f tys = tys.map (Ty.rename f) := by
  induction tys with
  | nil => rfl
  | cons hd tl ih => simp only [TyList.rename, List.map_cons, ih]

@[simp] theorem Ty.rename_prim {f : Nat → Nat} {p : PrimTy} :
    Ty.rename f (.prim p) = .prim p := rfl
@[simp] theorem Ty.rename_bvar {f : Nat → Nat} {i : Nat} :
    Ty.rename f (.bvar i) = .bvar i := rfl
@[simp] theorem Ty.rename_fvar {f : Nat → Nat} {n : Nat} :
    Ty.rename f (.fvar n) = .fvar (f n) := rfl
@[simp] theorem Ty.rename_arrow {f : Nat → Nat} {a b : Ty} :
    Ty.rename f (.arrow a b) = .arrow (Ty.rename f a) (Ty.rename f b) := rfl
@[simp] theorem Ty.rename_customTy {f : Nat → Nat} {nm : TyName} {tys : List Ty} :
    Ty.rename f (.customTy nm tys) = .customTy nm (tys.map (Ty.rename f)) := by
  simp [Ty.rename, TyList.rename_eq_map]
/-- Renaming by a function that fixes `τ`'s free vars is the identity. -/
theorem Ty.rename_eq_self {f : Nat → Nat} {τ : Ty}
    (h : ∀ v ∈ τ.freeVars, f v = v) : Ty.rename f τ = τ := by
  induction τ using Ty.rec_strong with
  | prim _ => rfl
  | arrow a b ih_a ih_b =>
    simp only [Ty.rename_arrow, Ty.arrow.injEq]
    refine ⟨ih_a (fun v hv => h v ?_), ih_b (fun v hv => h v ?_)⟩
    · simp only [Ty.freeVars, List.mem_dedup, List.mem_append]; exact Or.inl hv
    · simp only [Ty.freeVars, List.mem_dedup, List.mem_append]; exact Or.inr hv
  | bvar _ => rfl
  | fvar n =>
    have hn := h n (by simp [Ty.freeVars])
    simp only [Ty.rename_fvar, hn]
  | customTy nm tys ih =>
    simp only [Ty.rename_customTy, Ty.customTy.injEq, true_and]
    conv_rhs => rw [← List.map_id tys]
    apply List.map_congr_left
    intro t ht
    exact ih t ht (fun v hv => h v (TyList.mem_freeVars_of_mem ht hv))

/-- Renaming preserves the bvar bound (it only touches `fvar`s). -/
theorem Ty.rename_containsBvars {f : Nat → Nat} {n : Nat} {τ : Ty}
    (h : ContainsBvarsUpTo n τ) : ContainsBvarsUpTo n (Ty.rename f τ) := by
  induction τ using Ty.rec_strong with
  | prim p => exact .prim
  | bvar i => cases h with | bvar hlt => exact .bvar hlt
  | fvar m => exact .fvar
  | arrow a b iha ihb => cases h with | arrow ha hb => exact .arrow (iha ha) (ihb hb)
  | customTy nm tys ih =>
    cases h with
    | customTy hall =>
      simp only [Ty.rename_customTy]
      apply ContainsBvarsUpTo.customTy
      intro t ht
      obtain ⟨t0, ht0, rfl⟩ := List.mem_map.mp ht
      exact ih t0 ht0 (hall t0 ht0)

/-- Renaming preserves local-closedness. -/
theorem Ty.rename_isLC {f : Nat → Nat} {τ : Ty} (h : τ.IsLC) :
    (Ty.rename f τ).IsLC := Ty.rename_containsBvars h

/-- Renaming by an injective `f` commutes with single-var substitution. -/
theorem Ty.rename_substFvar {f : Nat → Nat} (hf : Function.Injective f)
    (z : Nat) (u t : Ty) :
    Ty.rename f (Ty.substFvar z u t)
      = Ty.substFvar (f z) (Ty.rename f u) (Ty.rename f t) := by
  induction t using Ty.rec_strong with
  | prim p => rfl
  | arrow a b iha ihb => simp only [Ty.substFvar, Ty.rename_arrow, iha, ihb]
  | bvar i => rfl
  | fvar m =>
    simp only [Ty.substFvar, Ty.rename_fvar]
    by_cases hm : m = z
    · rw [if_pos hm, if_pos (congrArg f hm)]
    · rw [if_neg hm, if_neg (fun heq => hm (hf heq)), Ty.rename_fvar]
  | customTy nm tys ih =>
    simp only [Ty.substFvar, TyList.substFvar_eq_map, Ty.rename_customTy, List.map_map,
               Ty.customTy.injEq, true_and]
    apply List.map_congr_left
    intro t0 ht0
    exact ih t0 ht0

/-- Swap two naturals. -/
def swapNat (a b n : Nat) : Nat := if n = a then b else if n = b then a else n

@[simp] theorem swapNat_left (a b : Nat) : swapNat a b a = b := by simp [swapNat]
theorem swapNat_right (a b : Nat) : swapNat a b b = a := by
  simp only [swapNat]; split <;> simp_all
theorem swapNat_other {a b n : Nat} (ha : n ≠ a) (hb : n ≠ b) : swapNat a b n = n := by
  simp [swapNat, ha, hb]
theorem swapNat_involutive (a b n : Nat) : swapNat a b (swapNat a b n) = n := by
  by_cases hna : n = a
  · subst hna; rw [swapNat_left, swapNat_right]
  · by_cases hnb : n = b
    · subst hnb; rw [swapNat_right, swapNat_left]
    · rw [swapNat_other hna hnb, swapNat_other hna hnb]
theorem swapNat_injective (a b : Nat) : Function.Injective (swapNat a b) :=
  Function.Involutive.injective (swapNat_involutive a b)

/-- Conjugate a substitution by a renaming: relabel both keys and values. -/
def Subst.conj (f : Nat → Nat) (S : Subst) : Subst :=
  S.map (fun p => (f p.1, Ty.rename f p.2))

/-- Conjugation preserves LC of the replacement types. -/
theorem Subst.conj_lc {f : Nat → Nat} {S : Subst} (hS : ∀ p ∈ S, p.2.IsLC) :
    ∀ p ∈ Subst.conj f S, p.2.IsLC := by
  intro p hp
  simp only [Subst.conj, List.mem_map] at hp
  obtain ⟨p0, hp0, rfl⟩ := hp
  exact Ty.rename_isLC (hS p0 hp0)

/-- The defining property of conjugation: it intertwines `onTy` with the
    renaming (for injective `f`). -/
theorem Subst.onTy_conj {f : Nat → Nat} (hf : Function.Injective f) (S : Subst) (τ : Ty) :
    (Subst.conj f S).onTy (Ty.rename f τ) = Ty.rename f (S.onTy τ) := by
  induction S generalizing τ with
  | nil => simp only [Subst.conj, List.map_nil, Subst.onTy_nil]
  | cons hd S' ih =>
    obtain ⟨z, u⟩ := hd
    show Subst.onTy (Subst.conj f S') (Ty.substFvar (f z) (Ty.rename f u) (Ty.rename f τ))
        = Ty.rename f (Subst.onTy S' (Ty.substFvar z u τ))
    rw [← Ty.rename_substFvar hf, ih]

/-- The 3-element list realising the swap `a ↔ b` (with a fresh intermediate `c`),
    usable with `TypeOfHM.onSubst`. -/
def swapSubst (a b c : Nat) : Subst := [(a, .fvar c), (b, .fvar a), (c, .fvar b)]

theorem swapSubst_lc (a b c : Nat) : ∀ p ∈ swapSubst a b c, p.2.IsLC := by
  intro p hp
  simp only [swapSubst, List.mem_cons, List.not_mem_nil, or_false] at hp
  obtain rfl | rfl | rfl := hp <;> exact ContainsBvarsUpTo.fvar

/-- The swap list acts as `rename (swapNat a b)` on types avoiding the fresh `c`. -/
theorem swapSubst_onTy {a b c : Nat} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    {τ : Ty} (hc : c ∉ τ.freeVars) :
    (swapSubst a b c).onTy τ = Ty.rename (swapNat a b) τ := by
  induction τ using Ty.rec_strong with
  | prim p => simp only [Subst.onTy_prim, Ty.rename_prim]
  | bvar i => simp only [Subst.onTy_bvar, Ty.rename_bvar]
  | arrow a' b' iha ihb =>
    simp only [Ty.freeVars, List.mem_dedup, List.mem_append, not_or] at hc
    simp only [Subst.onTy_arrow, Ty.rename_arrow]
    exact congrArg₂ Ty.arrow (iha hc.1) (ihb hc.2)
  | fvar n =>
    simp only [Ty.freeVars, List.mem_singleton] at hc
    have hnc : n ≠ c := fun h => hc h.symm
    by_cases hna : n = a
    · subst hna
      simp [swapSubst, Subst.onTy, Ty.substFvars, Ty.substFvar, hbc.symm]
    · by_cases hnb : n = b
      · subst hnb
        simp [swapSubst, Subst.onTy, Ty.substFvars, Ty.substFvar, swapNat_right,
              hab.symm, hac]
      · simp [swapSubst, Subst.onTy, Ty.substFvars, Ty.substFvar,
              swapNat_other hna hnb, hna, hnb, hnc]
  | customTy nm tys ih =>
    simp only [Ty.freeVars] at hc
    simp only [Subst.onTy_customTy, Ty.rename_customTy, Ty.customTy.injEq, true_and]
    apply List.map_congr_left
    intro t ht
    exact ih t ht (fun hct => hc (TyList.mem_freeVars_of_mem ht hct))

/-- After swapping `Φ ↔ W`, the var `Φ` is absent provided `W` was absent
    (the only source of `Φ` would have been a pre-existing `W`). -/
theorem Ty.rename_swap_not_mem_left {Φ W : Nat} {Y : Ty} (h : W ∉ Y.freeVars) :
    Φ ∉ (Ty.rename (swapNat Φ W) Y).freeVars := by
  induction Y using Ty.rec_strong with
  | prim p => simp [Ty.freeVars]
  | bvar i => simp [Ty.freeVars]
  | fvar n =>
    simp only [Ty.freeVars, List.mem_singleton] at h
    simp only [Ty.rename_fvar, Ty.freeVars, List.mem_singleton, swapNat]
    split_ifs <;> omega
  | arrow a b iha ihb =>
    simp only [Ty.freeVars, List.mem_dedup, List.mem_append, not_or] at h
    simp only [Ty.rename_arrow, Ty.freeVars, List.mem_dedup, List.mem_append, not_or]
    exact ⟨iha h.1, ihb h.2⟩
  | customTy nm tys ih =>
    simp only [Ty.freeVars] at h
    simp only [Ty.rename_customTy, Ty.freeVars]
    rw [TyList.not_mem_freeVars_iff]
    intro t' ht'
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp ht'
    exact ih t ht (fun hct => h (TyList.mem_freeVars_of_mem ht hct))

/-- Map-back: substituting `W ↦ Φ` undoes the swap `Φ ↔ W` on a `W`-free type. -/
theorem Ty.substFvar_rename_swap {Φ W : Nat} {X : Ty} (h : W ∉ X.freeVars) :
    Ty.substFvar W (.fvar Φ) (Ty.rename (swapNat Φ W) X) = X := by
  induction X using Ty.rec_strong with
  | prim p => rfl
  | bvar i => rfl
  | fvar n =>
    simp only [Ty.freeVars, List.mem_singleton] at h
    simp only [Ty.rename_fvar, Ty.substFvar]
    by_cases hn : n = Φ
    · subst hn; simp [swapNat]
    · rw [swapNat_other hn (fun he => h he.symm), if_neg (fun he => h he.symm)]
  | arrow a b iha ihb =>
    simp only [Ty.freeVars, List.mem_dedup, List.mem_append, not_or] at h
    simp only [Ty.rename_arrow, Ty.substFvar, iha h.1, ihb h.2]
  | customTy nm tys ih =>
    simp only [Ty.freeVars] at h
    simp only [Ty.rename_customTy, Ty.substFvar, TyList.substFvar_eq_map, List.map_map]
    refine congrArg (Ty.customTy nm) ?_
    conv_rhs => rw [← List.map_id tys]
    apply List.map_congr_left
    intro t ht
    exact ih t ht (fun hct => h (TyList.mem_freeVars_of_mem ht hct))

/-- Two distinct fresh names, both `≥ Φ` and avoiding a given finite set. -/
theorem exists_fresh_two_ge (Φ : Nat) (avoid : List Nat) :
    ∃ W c, Φ ≤ W ∧ Φ ≤ c ∧ W ≠ c ∧ W ∉ avoid ∧ c ∉ avoid := by
  obtain ⟨Xs, hlen, hnodup, hav⟩ := exists_fresh_names (List.range Φ ++ avoid) 2
  obtain ⟨W, c, rfl⟩ : ∃ W c, Xs = [W, c] := by
    match Xs, hlen with
    | [W, c], _ => exact ⟨W, c, rfl⟩
  have hWmem : W ∈ [W, c] := by simp
  have hcmem : c ∈ [W, c] := by simp
  have hWav := hav W hWmem
  have hcav := hav c hcmem
  simp only [List.mem_append, not_or] at hWav hcav
  refine ⟨W, c, ?_, ?_, ?_, hWav.2, hcav.2⟩
  · have := hWav.1; simp only [List.mem_range, not_lt] at this; omega
  · have := hcav.1; simp only [List.mem_range, not_lt] at this; omega
  · simp only [List.nodup_cons, List.mem_singleton, List.not_mem_nil, not_false_eq_true,
      List.nodup_nil, and_true] at hnodup
    exact hnodup

/-- `substFvar` keeps `W` fresh when `W` is fresh for the input and the replacement. -/
theorem Ty.not_mem_freeVars_substFvar {Z W : Nat} {U τ : Ty}
    (hτ : W ∉ τ.freeVars) (hU : W ∉ U.freeVars) :
    W ∉ (Ty.substFvar Z U τ).freeVars := by
  induction τ using Ty.rec_strong with
  | prim p => simp [Ty.substFvar, Ty.freeVars]
  | bvar i => simp [Ty.substFvar, Ty.freeVars]
  | fvar n =>
    simp only [Ty.freeVars, List.mem_singleton] at hτ
    simp only [Ty.substFvar]
    by_cases hn : n = Z
    · simp only [if_pos hn]; exact hU
    · simp only [if_neg hn, Ty.freeVars, List.mem_singleton]; exact hτ
  | arrow a b iha ihb =>
    simp only [Ty.freeVars, List.mem_dedup, List.mem_append, not_or] at hτ
    simp only [Ty.substFvar, Ty.freeVars, List.mem_dedup, List.mem_append, not_or]
    exact ⟨iha hτ.1, ihb hτ.2⟩
  | customTy nm tys ih =>
    simp only [Ty.freeVars] at hτ
    simp only [Ty.substFvar, Ty.freeVars, TyList.substFvar_eq_map]
    rw [TyList.not_mem_freeVars_iff]
    intro t' ht'
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp ht'
    exact ih t ht (fun hct => hτ (TyList.mem_freeVars_of_mem ht hct))

/-- A whole substitution keeps `W` fresh when `W` avoids its range and the input. -/
theorem Subst.not_mem_onTy_freeVars {S : Subst} {W : Nat} {τ : Ty}
    (hS : ∀ p ∈ S, W ∉ p.2.freeVars) (hτ : W ∉ τ.freeVars) :
    W ∉ (S.onTy τ).freeVars := by
  induction S generalizing τ with
  | nil => simpa using hτ
  | cons hd S' ih =>
    obtain ⟨Z, U⟩ := hd
    rw [show ((Z, U) :: S') = [(Z, U)] ++ S' from rfl, Subst.onTy_append]
    refine ih (fun p hp => hS p (List.mem_cons_of_mem _ hp)) ?_
    exact Ty.not_mem_freeVars_substFvar hτ (hS (Z, U) List.mem_cons_self)

/-- A substitution that fixes every free variable of a type fixes the whole
    type. (Unlike `substFvars_eq_self_of_no_key`, the keys *may* occur, as long
    as the composite acts as the identity on them.) -/
theorem Subst.onTy_eq_self_of_fixes {S : Subst} :
    ∀ {t : Ty}, (∀ v ∈ t.freeVars, S.onTy (.fvar v) = .fvar v) → S.onTy t = t := by
  intro t
  induction t using Ty.rec_strong with
  | prim p => intro _; simp only [Subst.onTy_prim]
  | bvar i => intro _; simp only [Subst.onTy_bvar]
  | fvar n => intro h; exact h n (by simp [Ty.freeVars])
  | arrow a b iha ihb =>
    intro h
    rw [Subst.onTy_arrow,
        iha (fun v hv => h v (by
          simp only [Ty.freeVars, List.mem_dedup, List.mem_append]; exact Or.inl hv)),
        ihb (fun v hv => h v (by
          simp only [Ty.freeVars, List.mem_dedup, List.mem_append]; exact Or.inr hv))]
  | customTy nm tys ih =>
    intro h
    rw [Subst.onTy_customTy]
    refine congrArg (Ty.customTy nm) ?_
    conv_rhs => rw [← List.map_id tys]
    apply List.map_congr_left
    intro t0 ht0
    exact ih t0 ht0 (fun v hv => h v (TyList.mem_freeVars_of_mem ht0 hv))

/-! ### Block renaming (for the `var`/`letIn` cases, which allocate a block of
    fresh vars at once). Generalises the single-var swap: `blockSwap Φ W k`
    transposes `[Φ,Φ+k)` with `[W,W+k)` (disjoint when `Φ+k ≤ W`). On types that
    avoid the `W`-block, the forward list `blockList` realises it, and the
    backward list `blockListBack` is the map-back. -/

/-- Transpose the blocks `[Φ,Φ+k)` and `[W,W+k)` (disjoint when `Φ+k ≤ W`). -/
def blockSwap (Φ W k n : Nat) : Nat :=
  if Φ ≤ n ∧ n < Φ + k then n + (W - Φ)
  else if W ≤ n ∧ n < W + k then n - (W - Φ)
  else n

/-- Forward renaming list: `Φ+i ↦ .fvar (W+i)`. -/
def blockList (Φ W k : Nat) : Subst := (List.range k).map (fun i => (Φ + i, Ty.fvar (W + i)))

/-- Backward renaming list: `W+i ↦ .fvar (Φ+i)`. -/
def blockListBack (Φ W k : Nat) : Subst := (List.range k).map (fun i => (W + i, Ty.fvar (Φ + i)))

theorem blockSwap_lt {Φ W k n : Nat} (hle : Φ ≤ W) (h : n < Φ) :
    blockSwap Φ W k n = n := by
  simp only [blockSwap]; split_ifs <;> omega

theorem blockSwap_involutive {Φ W k : Nat} (hd : Φ + k ≤ W) (n : Nat) :
    blockSwap Φ W k (blockSwap Φ W k n) = n := by
  simp only [blockSwap]; split_ifs <;> omega

theorem blockSwap_injective {Φ W k : Nat} (hd : Φ + k ≤ W) :
    Function.Injective (blockSwap Φ W k) :=
  Function.Involutive.injective (blockSwap_involutive hd)

theorem blockList_lc (Φ W k : Nat) : ∀ p ∈ blockList Φ W k, p.2.IsLC := by
  intro p hp
  simp only [blockList, List.mem_map] at hp
  obtain ⟨i, _, rfl⟩ := hp
  exact ContainsBvarsUpTo.fvar

theorem blockListBack_lc (Φ W k : Nat) : ∀ p ∈ blockListBack Φ W k, p.2.IsLC := by
  intro p hp
  simp only [blockListBack, List.mem_map] at hp
  obtain ⟨i, _, rfl⟩ := hp
  exact ContainsBvarsUpTo.fvar

/-- A `range`-indexed list of single-var substitutions `a+i ↦ .fvar (b+i)`
    acts on a free variable `n` exactly like the block transposition: if `n`
    is in `[a, a+k)` it becomes `n - a + b`, otherwise it is unchanged. The
    disjointness premise prevents a relabelled var from being touched again. -/
private theorem rangeMapList_onTy_fvar (a b : Nat) (k : Nat)
    (hdisj : a + k ≤ b ∨ b + k ≤ a) (n : Nat) :
    Subst.onTy ((List.range k).map (fun i => (a + i, Ty.fvar (b + i)))) (Ty.fvar n)
      = Ty.fvar (if a ≤ n ∧ n < a + k then n - a + b else n) := by
  induction k with
  | zero =>
    simp only [List.range_zero, List.map_nil, Subst.onTy_nil, Nat.add_zero]
    split_ifs <;> first | rfl | omega
  | succ k ih =>
    have hdisj' : a + k ≤ b ∨ b + k ≤ a := by omega
    simp only [List.range_succ, List.map_append, List.map_cons, List.map_nil,
               Subst.onTy_append]
    rw [ih hdisj']
    simp only [Subst.onTy, Ty.substFvars, Ty.substFvar]
    split_ifs <;> first | rfl | omega | (rw [Ty.fvar.injEq]; omega)

/-- The forward list realises `blockSwap` on `W`-block-avoiding types. -/
theorem blockList_onTy {Φ W k : Nat} (hd : Φ + k ≤ W) {τ : Ty}
    (hτ : ∀ v ∈ τ.freeVars, ¬ (W ≤ v ∧ v < W + k)) :
    (blockList Φ W k).onTy τ = Ty.rename (blockSwap Φ W k) τ := by
  induction τ using Ty.rec_strong with
  | prim p => simp only [Subst.onTy_prim, Ty.rename_prim]
  | bvar i => simp only [Subst.onTy_bvar, Ty.rename_bvar]
  | arrow a b iha ihb =>
    simp only [Subst.onTy_arrow, Ty.rename_arrow]
    refine congrArg₂ Ty.arrow (iha (fun v hv => hτ v ?_)) (ihb (fun v hv => hτ v ?_))
    · simp only [Ty.freeVars, List.mem_dedup, List.mem_append]; exact Or.inl hv
    · simp only [Ty.freeVars, List.mem_dedup, List.mem_append]; exact Or.inr hv
  | fvar n =>
    have hWn : ¬ (W ≤ n ∧ n < W + k) :=
      hτ n (by simp only [Ty.freeVars, List.mem_singleton])
    simp only [blockList]
    rw [rangeMapList_onTy_fvar Φ W k (Or.inl hd) n, Ty.rename_fvar]
    simp only [blockSwap]
    split_ifs <;> first | rfl | omega | (rw [Ty.fvar.injEq]; omega)
  | customTy nm tys ih =>
    simp only [Subst.onTy_customTy, Ty.rename_customTy, Ty.customTy.injEq, true_and]
    apply List.map_congr_left
    intro t ht
    exact ih t ht (fun v hv => hτ v (TyList.mem_freeVars_of_mem ht hv))

/-- Map-back: the backward list undoes `blockSwap` on `W`-block-avoiding types. -/
theorem blockListBack_onTy_rename {Φ W k : Nat} (hd : Φ + k ≤ W) {X : Ty}
    (hX : ∀ v ∈ X.freeVars, ¬ (W ≤ v ∧ v < W + k)) :
    (blockListBack Φ W k).onTy (Ty.rename (blockSwap Φ W k) X) = X := by
  induction X using Ty.rec_strong with
  | prim p => simp only [Ty.rename_prim, Subst.onTy_prim]
  | bvar i => simp only [Ty.rename_bvar, Subst.onTy_bvar]
  | arrow a b iha ihb =>
    simp only [Ty.rename_arrow, Subst.onTy_arrow]
    refine congrArg₂ Ty.arrow (iha (fun v hv => hX v ?_)) (ihb (fun v hv => hX v ?_))
    · simp only [Ty.freeVars, List.mem_dedup, List.mem_append]; exact Or.inl hv
    · simp only [Ty.freeVars, List.mem_dedup, List.mem_append]; exact Or.inr hv
  | fvar n =>
    have hWn : ¬ (W ≤ n ∧ n < W + k) :=
      hX n (by simp only [Ty.freeVars, List.mem_singleton])
    simp only [Ty.rename_fvar, blockListBack]
    rw [rangeMapList_onTy_fvar W Φ k (Or.inr hd) (blockSwap Φ W k n)]
    simp only [blockSwap]
    split_ifs <;> first | rfl | omega | (rw [Ty.fvar.injEq]; omega)
  | customTy nm tys ih =>
    simp only [Ty.rename_customTy, Subst.onTy_customTy, List.map_map, Ty.customTy.injEq, true_and]
    conv_rhs => rw [← List.map_id tys]
    apply List.map_congr_left
    intro t ht
    exact ih t ht (fun v hv => hX v (TyList.mem_freeVars_of_mem ht hv))

/-- The `Φ`-block is absent after renaming a `W`-block-avoiding type. -/
theorem blockSwap_rename_not_mem {Φ W k : Nat} (hd : Φ + k ≤ W) {Y : Ty}
    (hY : ∀ v ∈ Y.freeVars, ¬ (W ≤ v ∧ v < W + k)) :
    ∀ v, Φ ≤ v → v < Φ + k → v ∉ (Ty.rename (blockSwap Φ W k) Y).freeVars := by
  induction Y using Ty.rec_strong with
  | prim p => simp [Ty.freeVars]
  | bvar i => simp [Ty.freeVars]
  | fvar n =>
    intro v hv1 hv2
    have hWn : ¬ (W ≤ n ∧ n < W + k) :=
      hY n (by simp only [Ty.freeVars, List.mem_singleton])
    simp only [Ty.rename_fvar, Ty.freeVars, List.mem_singleton, blockSwap]
    split_ifs <;> omega
  | arrow a b iha ihb =>
    intro v hv1 hv2
    simp only [Ty.rename_arrow, Ty.freeVars, List.mem_dedup, List.mem_append, not_or]
    refine ⟨iha (fun w hw => hY w ?_) v hv1 hv2, ihb (fun w hw => hY w ?_) v hv1 hv2⟩
    · simp only [Ty.freeVars, List.mem_dedup, List.mem_append]; exact Or.inl hw
    · simp only [Ty.freeVars, List.mem_dedup, List.mem_append]; exact Or.inr hw
  | customTy nm tys ih =>
    intro v hv1 hv2
    simp only [Ty.rename_customTy, Ty.freeVars]
    rw [TyList.not_mem_freeVars_iff]
    intro t' ht'
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp ht'
    exact ih t ht (fun w hw => hY w (TyList.mem_freeVars_of_mem ht hw)) v hv1 hv2

/-- Bridge for the `var` completeness case: if `ty` instantiates to `τ` under
    `tyArgs`, then opening `ty` with fresh names `Xs` (nodup, fresh for `τ`) and
    substituting `Xs ↦ tyArgs` recovers `τ`. Only the result `τ`'s freshness is
    needed (used `tyArgs` are subterms of `τ`); unused `tyArgs` never matter, as
    the induction only visits `ty`'s actual bound vars. -/
theorem InstantiatesBy.onTy_openVars_zip {Xs : List Nat} {ty τ : Ty} {tyArgs : List Ty}
    (hinst : InstantiatesBy tyArgs ty τ)
    (hbv : ContainsBvarsUpTo Xs.length ty)
    (hnodup : Xs.Nodup)
    (hXfresh : ∀ x ∈ Xs, x ∉ τ.freeVars) :
    Subst.onTy (Xs.zip tyArgs) (Ty.openVars Xs ty) = τ := by
  induction ty using Ty.rec_strong generalizing τ with
  | prim p => cases hinst; simp only [Ty.openVars_prim, Subst.onTy_prim]
  | fvar n =>
    cases hinst
    simp only [Ty.openVars, Ty.instantiate]
    apply Ty.substFvars_eq_self_of_no_key
    intro p hp hc
    simp only [Ty.freeVars, List.mem_singleton] at hc
    subst hc
    exact hXfresh p.1 (List.of_mem_zip hp).1 (by simp [Ty.freeVars])
  | bvar i =>
    cases hinst with
    | bvar hsome =>
      cases hbv with
      | bvar hlt =>
        have hxi : Xs[i]? = some Xs[i] := List.getElem?_eq_getElem hlt
        simp only [Ty.openVars, Ty.instantiate, hxi, Option.elim_some]
        exact Ty.substFvars_zip_fvar_eq' hnodup hxi hsome hXfresh
  | arrow a b iha ihb =>
    cases hinst with
    | arrow ha hb =>
      cases hbv with
      | arrow hba hbb =>
        simp only [Ty.openVars_arrow, Subst.onTy_arrow]
        refine congrArg₂ Ty.arrow (iha ha hba ?_) (ihb hb hbb ?_)
        · intro x hx hc; exact hXfresh x hx (by
            simp only [Ty.freeVars, List.mem_dedup, List.mem_append]; exact .inl hc)
        · intro x hx hc; exact hXfresh x hx (by
            simp only [Ty.freeVars, List.mem_dedup, List.mem_append]; exact .inr hc)
  | customTy nm tys ih =>
    cases hinst with
    | customTy hforall =>
      cases hbv with
      | customTy hball =>
        simp only [Ty.openVars_customTy, Subst.onTy_customTy]
        refine congrArg (Ty.customTy nm) ?_
        induction hforall with
        | nil => rfl
        | cons hhd htl ihtl =>
          rename_i a instA tys' instTys'
          simp only [List.map_cons, List.cons.injEq]
          refine ⟨ih a List.mem_cons_self hhd (hball a List.mem_cons_self) ?_, ?_⟩
          · intro x hx hc
            apply hXfresh x hx
            simp only [Ty.freeVars, TyList.freeVars, List.mem_dedup, List.mem_append]
            exact Or.inl hc
          · refine ihtl (fun t ht => ih t (List.mem_cons_of_mem _ ht)) ?_
              (fun t ht => hball t (List.mem_cons_of_mem _ ht))
            intro x hx hc
            apply hXfresh x hx
            simp only [Ty.freeVars, TyList.freeVars, List.mem_dedup, List.mem_append] at hc ⊢
            exact Or.inr hc

/-- A single fresh name `W` starting a block `[W,W+k)` disjoint from `[Φ,Φ+k)`
    and above a finite `avoid` set. -/
theorem exists_fresh_block (avoid : List Nat) (Φ k : Nat) :
    ∃ W, Φ + k ≤ W ∧ ∀ v ∈ avoid, v < W := by
  refine ⟨avoid.foldr max 0 + Φ + k + 1, by omega, ?_⟩
  intro v hv
  have := List.le_foldr_max hv
  omega

/-- Opening a scheme body at `[Φ, Φ+k)` and then swapping that block with a
    fresh block `[W, W+k)` is the same as opening directly at the fresh block,
    provided the body's free variables lie below `Φ`. -/
theorem Ty.rename_openVars_blockSwap {Φ W k : Nat} (hd : Φ + k ≤ W) (ty : Ty)
    (hty : ∀ v ∈ ty.freeVars, v < Φ) :
    Ty.rename (blockSwap Φ W k) (Ty.openVars (freshVars Φ k) ty) =
      Ty.openVars (freshVars W k) ty := by
  induction ty using Ty.rec_strong with
  | prim p => simp only [Ty.openVars_prim, Ty.rename_prim]
  | bvar i =>
    simp only [Ty.openVars, Ty.instantiate]
    by_cases hi : i < k
    · have hf : (freshVars Φ k)[i]? = some (Φ + i) := by
        simp only [freshVars, List.getElem?_map, List.getElem?_range hi, Option.map_some]
      have hw : (freshVars W k)[i]? = some (W + i) := by
        simp only [freshVars, List.getElem?_map, List.getElem?_range hi, Option.map_some]
      simp only [hf, hw, Option.elim_some, Ty.rename_fvar, Ty.fvar.injEq, blockSwap]
      split_ifs <;> omega
    · have hf : (freshVars Φ k)[i]? = none :=
        List.getElem?_eq_none (by simp [freshVars_length]; omega)
      have hw : (freshVars W k)[i]? = none :=
        List.getElem?_eq_none (by simp [freshVars_length]; omega)
      simp only [hf, hw, Option.elim_none, Ty.rename_bvar]
  | fvar n =>
    have hn : n < Φ := hty n (by simp [Ty.freeVars])
    simp only [Ty.openVars, Ty.instantiate, Ty.rename_fvar, Ty.fvar.injEq]
    rw [blockSwap_lt (by omega) hn]
  | arrow a b iha ihb =>
    simp only [Ty.openVars_arrow, Ty.rename_arrow]
    refine congrArg₂ Ty.arrow (iha ?_) (ihb ?_)
    · intro v hv; exact hty v (by
        simp only [Ty.freeVars, List.mem_dedup, List.mem_append]; exact Or.inl hv)
    · intro v hv; exact hty v (by
        simp only [Ty.freeVars, List.mem_dedup, List.mem_append]; exact Or.inr hv)
  | customTy nm tys ih =>
    simp only [Ty.openVars_customTy, Ty.rename_customTy, List.map_map]
    congr 1
    apply List.map_congr_left
    intro t ht
    exact ih t ht (fun v hv => hty v (TyList.mem_freeVars_of_mem ht hv))

/-! ## 2. Unification completeness

If two LC types admit an LC unifier, a `UnifyRel` derivation exists (plain and
rigidity-aware forms), and the executable unifiers realise them. -/


/-- Unification completeness (+ the list version), bounded by the measure
    `2 * (size of the unified result) + flag` so a single strong induction on the
    bound `N` covers all recursive calls (`flag = 0` for `UnifyRel`, `1` for the
    list — the offset makes the singleton-list ↔ element step strictly decrease). -/
theorem UnifyRel.complete_aux : ∀ (N : Nat),
    (∀ {a b : Ty} {U : Subst}, 2 * (U.onTy a).size < N → a.IsLC → b.IsLC →
        Unifies U a b → ∃ S, UnifyRel a b S) ∧
    (∀ {as bs : List Ty} {U : Subst}, 2 * TyList.size (as.map U.onTy) + 1 < N →
        (∀ t ∈ as, t.IsLC) → (∀ t ∈ bs, t.IsLC) → as.length = bs.length →
        as.map U.onTy = bs.map U.onTy → ∃ S, UnifyRelList as bs S) := by
  intro N
  induction N with
  | zero => exact ⟨fun h => absurd h (by omega), fun h => absurd h (by omega)⟩
  | succ N ih =>
    obtain ⟨ihU, ihL⟩ := ih
    refine ⟨?_, ?_⟩
    · -- UnifyRel
      intro a b U hsz ha hb hU
      cases a with
      | bvar i => cases ha with | bvar h => omega
      | prim p =>
        cases b with
        | bvar i => cases hb with | bvar h => omega
        | prim q =>
          simp only [Unifies, Subst.onTy_prim, Ty.prim.injEq] at hU
          subst hU; exact ⟨[], .prim⟩
        | fvar m => exact ⟨[(m, .prim p)], .fvarR (by simp) (by simp [Ty.freeVars])⟩
        | arrow b₁ b₂ => simp [Unifies] at hU
        | customTy nm bs => simp [Unifies] at hU
      | fvar n =>
        cases b with
        | bvar i => cases hb with | bvar h => omega
        | fvar m =>
          by_cases hnm : n = m
          · subst hnm; exact ⟨[], .fvarRefl⟩
          · exact ⟨[(n, .fvar m)], .fvarL (by simp only [ne_eq, Ty.fvar.injEq]; omega)
              (by simp only [Ty.freeVars, List.mem_singleton]; omega)⟩
        | prim q =>
          by_cases hocc : n ∈ (Ty.prim q).freeVars
          · have hlt := Ty.size_onTy_fvar_lt (S := U) hocc (by simp)
            simp only [Unifies] at hU; rw [hU] at hlt; omega
          · exact ⟨[(n, .prim q)], .fvarL (by simp) hocc⟩
        | arrow b₁ b₂ =>
          by_cases hocc : n ∈ (Ty.arrow b₁ b₂).freeVars
          · have hlt := Ty.size_onTy_fvar_lt (S := U) hocc (by simp)
            simp only [Unifies] at hU; rw [hU] at hlt; omega
          · exact ⟨[(n, .arrow b₁ b₂)], .fvarL (by simp) hocc⟩
        | customTy nm bs =>
          by_cases hocc : n ∈ (Ty.customTy nm bs).freeVars
          · have hlt := Ty.size_onTy_fvar_lt (S := U) hocc (by simp)
            simp only [Unifies] at hU; rw [hU] at hlt; omega
          · exact ⟨[(n, .customTy nm bs)], .fvarL (by simp) hocc⟩
      | arrow a₁ a₂ =>
        cases ha with
        | arrow ha₁ ha₂ =>
        cases b with
        | bvar i => cases hb with | bvar h => omega
        | fvar m =>
          by_cases hocc : m ∈ (Ty.arrow a₁ a₂).freeVars
          · have hlt := Ty.size_onTy_fvar_lt (S := U) hocc (by simp)
            simp only [Unifies] at hU; rw [hU] at hlt; omega
          · exact ⟨[(m, .arrow a₁ a₂)], .fvarR (by simp) hocc⟩
        | prim q => simp [Unifies] at hU
        | customTy nm bs => simp [Unifies] at hU
        | arrow b₁ b₂ =>
          cases hb with
          | arrow hb₁ hb₂ =>
          have hpsz : (U.onTy (.arrow a₁ a₂)).size
              = 1 + (U.onTy a₁).size + (U.onTy a₂).size := by simp [Subst.onTy_arrow, Ty.size]
          simp only [Unifies, Subst.onTy_arrow, Ty.arrow.injEq] at hU
          obtain ⟨S₁, h₁⟩ := ihU (a := a₁) (b := b₁) (U := U)
            (by rw [hpsz] at hsz; omega) ha₁ hb₁ hU.1
          obtain ⟨R, hR⟩ := UnifyRel.greatest h₁ U hU.1
          have hS₁lc := UnifyRel.lc h₁ ha₁ hb₁
          obtain ⟨S₂, h₂⟩ := ihU (a := S₁.onTy a₂) (b := S₁.onTy b₂) (U := R)
            (by rw [← hR a₂]; rw [hpsz] at hsz; omega)
            (Subst.onTy_lc hS₁lc ha₂) (Subst.onTy_lc hS₁lc hb₂)
            (by show R.onTy (S₁.onTy a₂) = R.onTy (S₁.onTy b₂); rw [← hR a₂, ← hR b₂]; exact hU.2)
          exact ⟨S₁ ++ S₂, .arrow h₁ h₂⟩
      | customTy nm tys₁ =>
        cases b with
        | bvar i => cases hb with | bvar h => omega
        | fvar m =>
          by_cases hocc : m ∈ (Ty.customTy nm tys₁).freeVars
          · have hlt := Ty.size_onTy_fvar_lt (S := U) hocc (by simp)
            simp only [Unifies] at hU; rw [hU] at hlt; omega
          · exact ⟨[(m, .customTy nm tys₁)], .fvarR (by simp) hocc⟩
        | prim q => simp [Unifies] at hU
        | arrow b₁ b₂ => simp [Unifies] at hU
        | customTy nm' tys₂ =>
          have hcsz : (U.onTy (.customTy nm tys₁)).size
              = 1 + TyList.size (tys₁.map U.onTy) := by simp [Subst.onTy_customTy, Ty.size]
          simp only [Unifies, Subst.onTy_customTy, Ty.customTy.injEq] at hU
          obtain ⟨rfl, hmapeq⟩ := hU
          have hlen : tys₁.length = tys₂.length := by
            have := congrArg List.length hmapeq; simpa using this
          obtain ⟨S, hS⟩ := ihL (as := tys₁) (bs := tys₂) (U := U)
            (by rw [hcsz] at hsz; omega)
            (fun t ht => by cases ha with | customTy h => exact h t ht)
            (fun t ht => by cases hb with | customTy h => exact h t ht)
            hlen hmapeq
          exact ⟨S, .customTy hS⟩
    · -- UnifyRelList
      intro as bs U hsz has hbs hlen hmap
      cases as with
      | nil =>
        cases bs with
        | nil => exact ⟨[], .nil⟩
        | cons t₂ ts₂ => simp at hlen
      | cons t₁ ts₁ =>
        cases bs with
        | nil => simp at hlen
        | cons t₂ ts₂ =>
          simp only [List.map_cons, List.cons.injEq] at hmap
          have htsz : TyList.size ((t₁ :: ts₁).map U.onTy)
              = (U.onTy t₁).size + TyList.size (ts₁.map U.onTy) := by
            simp [List.map_cons, TyList.size]
          have ht1pos := @Ty.size_pos (U.onTy t₁)
          obtain ⟨S₁, h₁⟩ := ihU (a := t₁) (b := t₂) (U := U)
            (by rw [htsz] at hsz; omega) (has t₁ List.mem_cons_self)
            (hbs t₂ List.mem_cons_self) hmap.1
          obtain ⟨R, hR⟩ := UnifyRel.greatest h₁ U hmap.1
          have hS₁lc := UnifyRel.lc h₁ (has t₁ List.mem_cons_self) (hbs t₂ List.mem_cons_self)
          have key : ∀ l : List Ty, l.map (R.onTy ∘ S₁.onTy) = l.map U.onTy := by
            intro l; apply List.map_congr_left; intro t _; exact (hR t).symm
          have hkey1 : (ts₁.map S₁.onTy).map R.onTy = ts₁.map U.onTy := by
            rw [List.map_map]; exact key ts₁
          have hmaptail : (ts₁.map S₁.onTy).map R.onTy = (ts₂.map S₁.onTy).map R.onTy := by
            rw [List.map_map, List.map_map, key, key]; exact hmap.2
          obtain ⟨S₂, h₂⟩ := ihL (as := ts₁.map S₁.onTy) (bs := ts₂.map S₁.onTy) (U := R)
            (by rw [hkey1]; rw [htsz] at hsz; omega)
            (by
              intro t ht; obtain ⟨t0, ht0, rfl⟩ := List.mem_map.mp ht
              exact Subst.onTy_lc hS₁lc (has t0 (List.mem_cons_of_mem _ ht0)))
            (by
              intro t ht; obtain ⟨t0, ht0, rfl⟩ := List.mem_map.mp ht
              exact Subst.onTy_lc hS₁lc (hbs t0 (List.mem_cons_of_mem _ ht0)))
            (by simp only [List.length_map]; have := hlen; simpa using this)
            hmaptail
          exact ⟨S₁ ++ S₂, .cons h₁ h₂⟩

/-- Unification completeness: if `a` and `b` (both LC) have a unifier `U`, then a
    `UnifyRel` derivation exists. -/
theorem UnifyRel.complete {a b : Ty} {U : Subst}
    (ha : a.IsLC) (hb : b.IsLC) (hU : Unifies U a b) : ∃ S, UnifyRel a b S :=
  (UnifyRel.complete_aux (2 * (U.onTy a).size + 1)).1 (by omega) ha hb hU

/-! ### Rigidity-aware unification completeness

The **symmetric** `UnifyRel` can always be oriented to **avoid a rigid set `K`**,
given only that some LC unifier `U` keeps every `k ∈ K` fixed — crucially with NO
restriction that one operand's free vars lie in `K`. The structural recursion
threads the `K`-fixing witness via `greatest_K`: var–var is oriented away from
`K`, and a rigid var meeting a non-variable is *vacuous* (`U` fixes it, so it
can't equal a non-var image). The produced `S` avoids `K` by construction, so the
no-skolem-escape obligation (`hesc1`) is structural rather than a property to
re-establish — this is what replaced the old post-hoc escape-check approach. -/
theorem UnifyRel.complete_K_aux {K : List Nat} : ∀ (N : Nat),
    (∀ {a b : Ty} {U : Subst}, 2 * (U.onTy a).size < N → a.IsLC → b.IsLC →
        (∀ p ∈ U, p.2.IsLC) → Unifies U a b → (∀ k ∈ K, U.onTy (.fvar k) = .fvar k) →
        ∃ S, UnifyRel a b S ∧ (∀ p ∈ S, p.1 ∉ K)) ∧
    (∀ {as bs : List Ty} {U : Subst}, 2 * TyList.size (as.map U.onTy) + 1 < N →
        (∀ t ∈ as, t.IsLC) → (∀ t ∈ bs, t.IsLC) → (∀ p ∈ U, p.2.IsLC) →
        as.length = bs.length → as.map U.onTy = bs.map U.onTy →
        (∀ k ∈ K, U.onTy (.fvar k) = .fvar k) →
        ∃ S, UnifyRelList as bs S ∧ (∀ p ∈ S, p.1 ∉ K)) := by
  intro N
  induction N with
  | zero => exact ⟨fun h => absurd h (by omega), fun h => absurd h (by omega)⟩
  | succ N ih =>
    obtain ⟨ihU, ihL⟩ := ih
    refine ⟨?_, ?_⟩
    · intro a b U hsz ha hb hUlc hU hUK
      cases a with
      | bvar i => cases ha with | bvar h => omega
      | prim p =>
        cases b with
        | bvar i => cases hb with | bvar h => omega
        | prim q =>
          simp only [Unifies, Subst.onTy_prim, Ty.prim.injEq] at hU
          subst hU; exact ⟨[], .prim, by simp⟩
        | fvar m =>
          have hmK : m ∉ K := fun hmK => by
            have h1 : U.onTy (Ty.prim p) = U.onTy (Ty.fvar m) := hU
            rw [hUK m hmK, Subst.onTy_prim] at h1; exact absurd h1 (by simp)
          exact ⟨[(m, .prim p)], .fvarR (by simp) (by simp [Ty.freeVars]),
            by intro p' hp'; rw [List.mem_singleton] at hp'; subst hp'; exact hmK⟩
        | arrow b₁ b₂ => simp [Unifies] at hU
        | customTy nm bs => simp [Unifies] at hU
      | fvar n =>
        cases b with
        | bvar i => cases hb with | bvar h => omega
        | fvar m =>
          by_cases hnm : n = m
          · subst hnm; exact ⟨[], .fvarRefl, by simp⟩
          · by_cases hnK : n ∈ K
            · have hmK : m ∉ K := fun hmK => by
                have h1 : U.onTy (Ty.fvar n) = U.onTy (Ty.fvar m) := hU
                rw [hUK n hnK, hUK m hmK] at h1
                simp only [Ty.fvar.injEq] at h1; exact hnm h1
              exact ⟨[(m, .fvar n)], .fvarR (by simp only [ne_eq, Ty.fvar.injEq]; omega)
                (by simp only [Ty.freeVars, List.mem_singleton]; omega),
                by intro p' hp'; rw [List.mem_singleton] at hp'; subst hp'; exact hmK⟩
            · exact ⟨[(n, .fvar m)], .fvarL (by simp only [ne_eq, Ty.fvar.injEq]; omega)
                (by simp only [Ty.freeVars, List.mem_singleton]; omega),
                by intro p' hp'; rw [List.mem_singleton] at hp'; subst hp'; exact hnK⟩
        | prim q =>
          by_cases hocc : n ∈ (Ty.prim q).freeVars
          · have hlt := Ty.size_onTy_fvar_lt (S := U) hocc (by simp)
            simp only [Unifies] at hU; rw [hU] at hlt; omega
          · by_cases hnK : n ∈ K
            · exfalso
              have h1 : U.onTy (Ty.fvar n) = U.onTy (Ty.prim q) := hU
              rw [hUK n hnK, Subst.onTy_prim] at h1; exact absurd h1 (by simp)
            · exact ⟨[(n, .prim q)], .fvarL (by simp) hocc,
                by intro p' hp'; rw [List.mem_singleton] at hp'; subst hp'; exact hnK⟩
        | arrow b₁ b₂ =>
          by_cases hocc : n ∈ (Ty.arrow b₁ b₂).freeVars
          · have hlt := Ty.size_onTy_fvar_lt (S := U) hocc (by simp)
            simp only [Unifies] at hU; rw [hU] at hlt; omega
          · by_cases hnK : n ∈ K
            · exfalso
              have h1 : U.onTy (Ty.fvar n) = U.onTy (Ty.arrow b₁ b₂) := hU
              rw [hUK n hnK, Subst.onTy_arrow] at h1; exact absurd h1 (by simp)
            · exact ⟨[(n, .arrow b₁ b₂)], .fvarL (by simp) hocc,
                by intro p' hp'; rw [List.mem_singleton] at hp'; subst hp'; exact hnK⟩
        | customTy nm bs =>
          by_cases hocc : n ∈ (Ty.customTy nm bs).freeVars
          · have hlt := Ty.size_onTy_fvar_lt (S := U) hocc (by simp)
            simp only [Unifies] at hU; rw [hU] at hlt; omega
          · by_cases hnK : n ∈ K
            · exfalso
              have h1 : U.onTy (Ty.fvar n) = U.onTy (Ty.customTy nm bs) := hU
              rw [hUK n hnK, Subst.onTy_customTy] at h1; exact absurd h1 (by simp)
            · exact ⟨[(n, .customTy nm bs)], .fvarL (by simp) hocc,
                by intro p' hp'; rw [List.mem_singleton] at hp'; subst hp'; exact hnK⟩
      | arrow a₁ a₂ =>
        cases ha with
        | arrow ha₁ ha₂ =>
        cases b with
        | bvar i => cases hb with | bvar h => omega
        | fvar m =>
          by_cases hocc : m ∈ (Ty.arrow a₁ a₂).freeVars
          · have hlt := Ty.size_onTy_fvar_lt (S := U) hocc (by simp)
            simp only [Unifies] at hU; rw [hU] at hlt; omega
          · by_cases hmK : m ∈ K
            · exfalso
              have h1 : U.onTy (Ty.arrow a₁ a₂) = U.onTy (Ty.fvar m) := hU
              rw [hUK m hmK, Subst.onTy_arrow] at h1; exact absurd h1 (by simp)
            · exact ⟨[(m, .arrow a₁ a₂)], .fvarR (by simp) hocc,
                by intro p' hp'; rw [List.mem_singleton] at hp'; subst hp'; exact hmK⟩
        | prim q => simp [Unifies] at hU
        | customTy nm bs => simp [Unifies] at hU
        | arrow b₁ b₂ =>
          cases hb with
          | arrow hb₁ hb₂ =>
          have hpsz : (U.onTy (.arrow a₁ a₂)).size = 1 + (U.onTy a₁).size + (U.onTy a₂).size := by
            simp [Subst.onTy_arrow, Ty.size]
          simp only [Unifies, Subst.onTy_arrow, Ty.arrow.injEq] at hU
          obtain ⟨S₁, h₁, hS₁K⟩ := ihU (a := a₁) (b := b₁) (U := U)
            (by rw [hpsz] at hsz; omega) ha₁ hb₁ hUlc hU.1 hUK
          have hS₁lc := UnifyRel.lc h₁ ha₁ hb₁
          obtain ⟨R, hR, hRlc, hRK⟩ := UnifyRel.greatest_K h₁ U hUlc hU.1 hUK
          obtain ⟨S₂, h₂, hS₂K⟩ := ihU (a := S₁.onTy a₂) (b := S₁.onTy b₂) (U := R)
            (by rw [← hR a₂]; rw [hpsz] at hsz; omega)
            (Subst.onTy_lc hS₁lc ha₂) (Subst.onTy_lc hS₁lc hb₂) hRlc
            (by show R.onTy (S₁.onTy a₂) = R.onTy (S₁.onTy b₂); rw [← hR a₂, ← hR b₂]; exact hU.2) hRK
          exact ⟨S₁ ++ S₂, .arrow h₁ h₂, by
            intro p hp; rcases List.mem_append.mp hp with h | h
            · exact hS₁K p h
            · exact hS₂K p h⟩
      | customTy nm tys₁ =>
        cases b with
        | bvar i => cases hb with | bvar h => omega
        | fvar m =>
          by_cases hocc : m ∈ (Ty.customTy nm tys₁).freeVars
          · have hlt := Ty.size_onTy_fvar_lt (S := U) hocc (by simp)
            simp only [Unifies] at hU; rw [hU] at hlt; omega
          · by_cases hmK : m ∈ K
            · exfalso
              have h1 : U.onTy (Ty.customTy nm tys₁) = U.onTy (Ty.fvar m) := hU
              rw [hUK m hmK, Subst.onTy_customTy] at h1; exact absurd h1 (by simp)
            · exact ⟨[(m, .customTy nm tys₁)], .fvarR (by simp) hocc,
                by intro p' hp'; rw [List.mem_singleton] at hp'; subst hp'; exact hmK⟩
        | prim q => simp [Unifies] at hU
        | arrow b₁ b₂ => simp [Unifies] at hU
        | customTy nm' tys₂ =>
          have hcsz : (U.onTy (.customTy nm tys₁)).size = 1 + TyList.size (tys₁.map U.onTy) := by
            simp [Subst.onTy_customTy, Ty.size]
          simp only [Unifies, Subst.onTy_customTy, Ty.customTy.injEq] at hU
          obtain ⟨rfl, hmapeq⟩ := hU
          have hlen : tys₁.length = tys₂.length := by
            have := congrArg List.length hmapeq; simpa using this
          obtain ⟨S, hS, hSK⟩ := ihL (as := tys₁) (bs := tys₂) (U := U)
            (by rw [hcsz] at hsz; omega)
            (fun t ht => by cases ha with | customTy h => exact h t ht)
            (fun t ht => by cases hb with | customTy h => exact h t ht)
            hUlc hlen hmapeq hUK
          exact ⟨S, .customTy hS, hSK⟩
    · intro as bs U hsz has hbs hUlc hlen hmap hUK
      cases as with
      | nil =>
        cases bs with
        | nil => exact ⟨[], .nil, by simp⟩
        | cons t₂ ts₂ => simp at hlen
      | cons t₁ ts₁ =>
        cases bs with
        | nil => simp at hlen
        | cons t₂ ts₂ =>
          simp only [List.map_cons, List.cons.injEq] at hmap
          have htsz : TyList.size ((t₁ :: ts₁).map U.onTy)
              = (U.onTy t₁).size + TyList.size (ts₁.map U.onTy) := by simp [List.map_cons, TyList.size]
          have ht1pos := @Ty.size_pos (U.onTy t₁)
          obtain ⟨S₁, h₁, hS₁K⟩ := ihU (a := t₁) (b := t₂) (U := U)
            (by rw [htsz] at hsz; omega) (has t₁ List.mem_cons_self) (hbs t₂ List.mem_cons_self)
            hUlc hmap.1 hUK
          have hS₁lc := UnifyRel.lc h₁ (has t₁ List.mem_cons_self) (hbs t₂ List.mem_cons_self)
          obtain ⟨R, hR, hRlc, hRK⟩ := UnifyRel.greatest_K h₁ U hUlc hmap.1 hUK
          have key : ∀ l : List Ty, l.map (R.onTy ∘ S₁.onTy) = l.map U.onTy := by
            intro l; apply List.map_congr_left; intro t _; exact (hR t).symm
          have hkey1 : (ts₁.map S₁.onTy).map R.onTy = ts₁.map U.onTy := by
            rw [List.map_map]; exact key ts₁
          have hmaptail : (ts₁.map S₁.onTy).map R.onTy = (ts₂.map S₁.onTy).map R.onTy := by
            rw [List.map_map, List.map_map, key, key]; exact hmap.2
          obtain ⟨S₂, h₂, hS₂K⟩ := ihL (as := ts₁.map S₁.onTy) (bs := ts₂.map S₁.onTy) (U := R)
            (by rw [hkey1]; rw [htsz] at hsz; omega)
            (by intro t ht; obtain ⟨t0, ht0, rfl⟩ := List.mem_map.mp ht
                exact Subst.onTy_lc hS₁lc (has t0 (List.mem_cons_of_mem _ ht0)))
            (by intro t ht; obtain ⟨t0, ht0, rfl⟩ := List.mem_map.mp ht
                exact Subst.onTy_lc hS₁lc (hbs t0 (List.mem_cons_of_mem _ ht0)))
            hRlc
            (by simp only [List.length_map]; have := hlen; simpa using this)
            hmaptail hRK
          exact ⟨S₁ ++ S₂, .cons h₁ h₂, by
            intro p hp; rcases List.mem_append.mp hp with h | h
            · exact hS₁K p h
            · exact hS₂K p h⟩

/-- A `K`-fixing LC unifier of two LC types yields a `UnifyRel` derivation that
    **avoids `K`** — with no side-condition on the operands' free variables. The
    rigidity-aware orientation that makes annotated-`let` completeness's `hesc1`
    structural. -/
theorem UnifyRel.complete_K {K : List Nat} {a b : Ty} {U : Subst}
    (ha : a.IsLC) (hb : b.IsLC) (hUlc : ∀ p ∈ U, p.2.IsLC)
    (hU : Unifies U a b) (hUK : ∀ k ∈ K, U.onTy (.fvar k) = .fvar k) :
    ∃ S, UnifyRel a b S ∧ (∀ p ∈ S, p.1 ∉ K) :=
  (UnifyRel.complete_K_aux (2 * (U.onTy a).size + 1)).1 (by omega) ha hb hUlc hU hUK


/-! ### Completeness of the executable unifier -/

/-- **Rigidity-aware unify completeness.** When the (LC) inputs admit an LC unifier
    `U` that keeps every `k ∈ K` rigid, the rigidity-aware `unifyCoreK K` succeeds.
    Fuses the size induction of `unifyCore_complete_aux` with the orientation
    reasoning of `UnifyRel.complete_K_aux`: at a variable step the `K`-fixing `U`
    rules out the branch that `unifyCoreK` would refuse (binding a rigid var). -/
theorem unifyCoreK_complete_aux {K : List Nat} : ∀ (N : Nat),
    (∀ {a b : Ty} {U : Subst}, 2 * (U.onTy a).size < N → a.IsLC → b.IsLC →
        (∀ p ∈ U, p.2.IsLC) → Unifies U a b → (∀ k ∈ K, U.onTy (.fvar k) = .fvar k) →
        (unifyCoreK K a b).isSome) ∧
    (∀ {as bs : List Ty} {U : Subst}, 2 * TyList.size (as.map U.onTy) + 1 < N →
        (∀ t ∈ as, t.IsLC) → (∀ t ∈ bs, t.IsLC) → (∀ p ∈ U, p.2.IsLC) →
        as.length = bs.length → as.map U.onTy = bs.map U.onTy →
        (∀ k ∈ K, U.onTy (.fvar k) = .fvar k) →
        (unifyListCoreK K as bs).isSome) := by
  intro N
  induction N with
  | zero => exact ⟨fun h => absurd h (by omega), fun h => absurd h (by omega)⟩
  | succ N ih =>
    obtain ⟨ihU, ihL⟩ := ih
    refine ⟨?_, ?_⟩
    · intro a b U hsz ha hb hUlc hU hUK
      cases a with
      | bvar i => cases ha with | bvar h => omega
      | prim p =>
        cases b with
        | bvar i => cases hb with | bvar h => omega
        | prim q => simp only [Unifies, Subst.onTy_prim, Ty.prim.injEq] at hU; subst hU; simp [unifyCoreK]
        | fvar m =>
          have hmK : m ∉ K := fun hmK => by
            have h1 : U.onTy (Ty.prim p) = U.onTy (Ty.fvar m) := hU
            rw [hUK m hmK, Subst.onTy_prim] at h1; exact absurd h1 (by simp)
          simp [unifyCoreK, hmK, Ty.freeVars]
        | arrow b₁ b₂ => simp [Unifies] at hU
        | customTy nm bs => simp [Unifies] at hU
      | fvar n =>
        cases b with
        | bvar i => cases hb with | bvar h => omega
        | fvar m =>
          by_cases hnm : n = m
          · subst hnm; simp [unifyCoreK]
          · by_cases hnK : n ∈ K
            · have hmK : m ∉ K := fun hmK => by
                have h1 : U.onTy (Ty.fvar n) = U.onTy (Ty.fvar m) := hU
                rw [hUK n hnK, hUK m hmK] at h1; simp only [Ty.fvar.injEq] at h1; exact hnm h1
              simp [unifyCoreK, hnm, hnK, hmK]
            · simp [unifyCoreK, hnm, hnK]
        | prim q =>
          by_cases hocc : n ∈ (Ty.prim q).freeVars
          · have hlt := Ty.size_onTy_fvar_lt (S := U) hocc (by simp)
            simp only [Unifies] at hU; rw [hU] at hlt; omega
          · by_cases hnK : n ∈ K
            · exfalso
              have h1 : U.onTy (Ty.fvar n) = U.onTy (Ty.prim q) := hU
              rw [hUK n hnK, Subst.onTy_prim] at h1; exact absurd h1 (by simp)
            · simp [unifyCoreK, hnK, hocc]
        | arrow b₁ b₂ =>
          by_cases hocc : n ∈ (Ty.arrow b₁ b₂).freeVars
          · have hlt := Ty.size_onTy_fvar_lt (S := U) hocc (by simp)
            simp only [Unifies] at hU; rw [hU] at hlt; omega
          · by_cases hnK : n ∈ K
            · exfalso
              have h1 : U.onTy (Ty.fvar n) = U.onTy (Ty.arrow b₁ b₂) := hU
              rw [hUK n hnK, Subst.onTy_arrow] at h1; exact absurd h1 (by simp)
            · simp [unifyCoreK, hnK, hocc]
        | customTy nm bs =>
          by_cases hocc : n ∈ (Ty.customTy nm bs).freeVars
          · have hlt := Ty.size_onTy_fvar_lt (S := U) hocc (by simp)
            simp only [Unifies] at hU; rw [hU] at hlt; omega
          · by_cases hnK : n ∈ K
            · exfalso
              have h1 : U.onTy (Ty.fvar n) = U.onTy (Ty.customTy nm bs) := hU
              rw [hUK n hnK, Subst.onTy_customTy] at h1; exact absurd h1 (by simp)
            · simp [unifyCoreK, hnK, hocc]
      | arrow a₁ a₂ =>
        cases ha with
        | arrow ha₁ ha₂ =>
        cases b with
        | bvar i => cases hb with | bvar h => omega
        | fvar m =>
          by_cases hocc : m ∈ (Ty.arrow a₁ a₂).freeVars
          · have hlt := Ty.size_onTy_fvar_lt (S := U) hocc (by simp)
            simp only [Unifies] at hU; rw [hU] at hlt; omega
          · by_cases hmK : m ∈ K
            · exfalso
              have h1 : U.onTy (Ty.arrow a₁ a₂) = U.onTy (Ty.fvar m) := hU
              rw [hUK m hmK, Subst.onTy_arrow] at h1; exact absurd h1 (by simp)
            · simp [unifyCoreK, hmK, hocc]
        | prim q => simp [Unifies] at hU
        | customTy nm bs => simp [Unifies] at hU
        | arrow b₁ b₂ =>
          cases hb with
          | arrow hb₁ hb₂ =>
          have hpsz : (U.onTy (.arrow a₁ a₂)).size = 1 + (U.onTy a₁).size + (U.onTy a₂).size := by
            simp [Subst.onTy_arrow, Ty.size]
          simp only [Unifies, Subst.onTy_arrow, Ty.arrow.injEq] at hU
          obtain ⟨⟨S₁, h₁, _⟩, he1⟩ := Option.isSome_iff_exists.mp
            (ihU (a := a₁) (b := b₁) (U := U) (by rw [hpsz] at hsz; omega) ha₁ hb₁ hUlc hU.1 hUK)
          have hS₁lc := UnifyRel.lc h₁ ha₁ hb₁
          obtain ⟨R, hR, hRlc, hRK⟩ := UnifyRel.greatest_K h₁ U hUlc hU.1 hUK
          obtain ⟨⟨S₂, h₂, _⟩, he2⟩ := Option.isSome_iff_exists.mp
            (ihU (a := S₁.onTy a₂) (b := S₁.onTy b₂) (U := R) (by rw [← hR a₂]; rw [hpsz] at hsz; omega)
              (Subst.onTy_lc hS₁lc ha₂) (Subst.onTy_lc hS₁lc hb₂) hRlc
              (by show R.onTy (S₁.onTy a₂) = R.onTy (S₁.onTy b₂); rw [← hR a₂, ← hR b₂]; exact hU.2) hRK)
          rw [unifyCoreK]; simp only [he1, he2, Option.isSome_some]
      | customTy nm tys₁ =>
        cases b with
        | bvar i => cases hb with | bvar h => omega
        | fvar m =>
          by_cases hocc : m ∈ (Ty.customTy nm tys₁).freeVars
          · have hlt := Ty.size_onTy_fvar_lt (S := U) hocc (by simp)
            simp only [Unifies] at hU; rw [hU] at hlt; omega
          · by_cases hmK : m ∈ K
            · exfalso
              have h1 : U.onTy (Ty.customTy nm tys₁) = U.onTy (Ty.fvar m) := hU
              rw [hUK m hmK, Subst.onTy_customTy] at h1; exact absurd h1 (by simp)
            · simp [unifyCoreK, hmK, hocc]
        | prim q => simp [Unifies] at hU
        | arrow b₁ b₂ => simp [Unifies] at hU
        | customTy nm' tys₂ =>
          have hcsz : (U.onTy (.customTy nm tys₁)).size = 1 + TyList.size (tys₁.map U.onTy) := by
            simp [Subst.onTy_customTy, Ty.size]
          simp only [Unifies, Subst.onTy_customTy, Ty.customTy.injEq] at hU
          obtain ⟨rfl, hmapeq⟩ := hU
          have hlen : tys₁.length = tys₂.length := by
            have := congrArg List.length hmapeq; simpa using this
          obtain ⟨⟨S, hS, _⟩, heL⟩ := Option.isSome_iff_exists.mp
            (ihL (as := tys₁) (bs := tys₂) (U := U) (by rw [hcsz] at hsz; omega)
              (fun t ht => by cases ha with | customTy h => exact h t ht)
              (fun t ht => by cases hb with | customTy h => exact h t ht)
              hUlc hlen hmapeq hUK)
          rw [unifyCoreK]; simp [heL]
    · intro as bs U hsz has hbs hUlc hlen hmap hUK
      cases as with
      | nil =>
        cases bs with
        | nil => simp [unifyListCoreK]
        | cons t₂ ts₂ => simp at hlen
      | cons t₁ ts₁ =>
        cases bs with
        | nil => simp at hlen
        | cons t₂ ts₂ =>
          simp only [List.map_cons, List.cons.injEq] at hmap
          have htsz : TyList.size ((t₁ :: ts₁).map U.onTy)
              = (U.onTy t₁).size + TyList.size (ts₁.map U.onTy) := by simp [List.map_cons, TyList.size]
          have ht1pos := @Ty.size_pos (U.onTy t₁)
          obtain ⟨⟨S₁, h₁, _⟩, he1⟩ := Option.isSome_iff_exists.mp
            (ihU (a := t₁) (b := t₂) (U := U) (by rw [htsz] at hsz; omega)
              (has t₁ List.mem_cons_self) (hbs t₂ List.mem_cons_self) hUlc hmap.1 hUK)
          have hS₁lc := UnifyRel.lc h₁ (has t₁ List.mem_cons_self) (hbs t₂ List.mem_cons_self)
          obtain ⟨R, hR, hRlc, hRK⟩ := UnifyRel.greatest_K h₁ U hUlc hmap.1 hUK
          have key : ∀ l : List Ty, l.map (R.onTy ∘ S₁.onTy) = l.map U.onTy := by
            intro l; apply List.map_congr_left; intro t _; exact (hR t).symm
          have hkey1 : (ts₁.map S₁.onTy).map R.onTy = ts₁.map U.onTy := by
            rw [List.map_map]; exact key ts₁
          have hmaptail : (ts₁.map S₁.onTy).map R.onTy = (ts₂.map S₁.onTy).map R.onTy := by
            rw [List.map_map, List.map_map, key, key]; exact hmap.2
          obtain ⟨⟨S₂, h₂, _⟩, he2⟩ := Option.isSome_iff_exists.mp
            (ihL (as := ts₁.map S₁.onTy) (bs := ts₂.map S₁.onTy) (U := R)
              (by rw [hkey1]; rw [htsz] at hsz; omega)
              (by intro t ht; obtain ⟨t0, ht0, rfl⟩ := List.mem_map.mp ht
                  exact Subst.onTy_lc hS₁lc (has t0 (List.mem_cons_of_mem _ ht0)))
              (by intro t ht; obtain ⟨t0, ht0, rfl⟩ := List.mem_map.mp ht
                  exact Subst.onTy_lc hS₁lc (hbs t0 (List.mem_cons_of_mem _ ht0)))
              hRlc (by simp only [List.length_map]; have := hlen; simpa using this) hmaptail hRK)
          rw [unifyListCoreK]; simp only [he1, he2, Option.isSome_some]

/-- `unifyCoreK` completeness wrapper. -/
theorem unifyCoreK_complete {K : List Nat} {a b : Ty} {U : Subst}
    (ha : a.IsLC) (hb : b.IsLC) (hUlc : ∀ p ∈ U, p.2.IsLC)
    (hU : Unifies U a b) (hUK : ∀ k ∈ K, U.onTy (.fvar k) = .fvar k) :
    (unifyCoreK K a b).isSome :=
  (unifyCoreK_complete_aux (2 * (U.onTy a).size + 1)).1 (by omega) ha hb hUlc hU hUK

/-- `unify` completeness: `unify` succeeds whenever the (LC) inputs are unifiable.
    Reduces to `unifyCoreK_complete` at the empty rigid set — the MGU `S` is LC by
    `UnifyRel.lc`, and the empty-`K` fixing condition is vacuous. -/
theorem unify_complete {a b : Ty} {S : Subst} (h : UnifyRel a b S)
    (ha : a.IsLC) (hb : b.IsLC) : (unify a b).isSome := by
  have hcore : (unifyCore a b).isSome := by
    have := unifyCoreK_complete (K := []) ha hb (UnifyRel.lc h ha hb) h.unifies (by simp)
    simpa [unifyCore, Option.isSome_map] using this
  simpa [unify, Option.isSome_map] using hcore
/-! ## 3. Gap avoidance (domain/range locality of `Infer` substitutions)

The executable annotated-`let` arm hard-codes its skolem block
`Ys = freshVars Φ pc`, while the relation `Infer.letInAnn` permits any `N ≥ Φ`.
Bridging the two needs a *given* derivation's output substitution to leave such
a block rigid: domain AND range avoiding `[lo, hi)` below the input frontier.
Ported onto the monomorphic recursive-group relation and ceiling-based `letRec`
body environment. -/

/-- Free type vars contributed by a spec (monotype, or scheme body). -/
def RecSpec.tfvs : RecSpec → List Nat
  | .mono τ => τ.freeVars
  | .poly σ => σ.body.freeVars

/-- A whole substitution applied to an interval-avoiding type yields an
    interval-avoiding type. -/
theorem Subst.onTy_avoidsItv {lo hi : Nat} :
    ∀ {S : Subst}, (∀ p ∈ S, ∀ v ∈ p.2.freeVars, v < lo ∨ hi ≤ v) →
    ∀ {τ : Ty}, (∀ v ∈ τ.freeVars, v < lo ∨ hi ≤ v) →
    ∀ v ∈ (S.onTy τ).freeVars, v < lo ∨ hi ≤ v := by
  intro S
  induction S with
  | nil => intro _ τ hτ v hv; rw [Subst.onTy_nil] at hv; exact hτ v hv
  | cons hd S' ih =>
    obtain ⟨Z, U⟩ := hd
    intro hS τ hτ v hv
    rw [show ((Z, U) :: S') = [(Z, U)] ++ S' from rfl, Subst.onTy_append] at hv
    refine ih (fun p hp => hS p (List.mem_cons_of_mem _ hp)) ?_ v hv
    intro w hw
    rcases Ty.mem_freeVars_substFvar hw with h | h
    · exact hτ w h
    · exact hS (Z, U) (List.mem_cons_self ..) w h

/-- A whole substitution applied to an interval-avoiding context env stays
    interval-avoiding. -/
theorem Subst.onCtx_avoidsItv {lo hi : Nat} {S : Subst} {ctx : Ctx}
    (hS : ∀ p ∈ S, ∀ v ∈ p.2.freeVars, v < lo ∨ hi ≤ v)
    (hctx : ∀ M ∈ ctx.env, ∀ v ∈ M.body.freeVars, v < lo ∨ hi ≤ v) :
    ∀ M ∈ (S.onCtx ctx).env, ∀ v ∈ M.body.freeVars, v < lo ∨ hi ≤ v := by
  intro M hM
  simp only [Subst.onCtx, Subst.onEnv] at hM
  obtain ⟨M0, hM0, rfl⟩ := List.mem_map.mp hM
  simp only [Subst.onPolyTy]
  exact Subst.onTy_avoidsItv hS (hctx M0 hM0)

/-- Opening with interval-avoiding type args preserves interval-avoidance. -/
theorem Ty.openWith_avoidsItv {lo hi : Nat} {Vs : List Ty}
    (hVs : ∀ t ∈ Vs, ∀ v ∈ t.freeVars, v < lo ∨ hi ≤ v) :
    ∀ {X : Ty}, (∀ v ∈ X.freeVars, v < lo ∨ hi ≤ v) →
    ∀ v ∈ (Ty.openWith Vs X).freeVars, v < lo ∨ hi ≤ v := by
  intro X
  induction X using Ty.rec_strong with
  | prim p => intro _ v hv; simp [Ty.openWith, Ty.instantiate, Ty.freeVars] at hv
  | fvar n =>
    intro hX v hv
    simp only [Ty.openWith, Ty.instantiate, Ty.freeVars, List.mem_singleton] at hv
    rw [hv]; exact hX n (by simp [Ty.freeVars])
  | bvar i =>
    intro _ v hv
    simp only [Ty.openWith, Ty.instantiate] at hv
    cases h : Vs[i]? with
    | none => rw [h] at hv; simp [Ty.freeVars] at hv
    | some t =>
      rw [h] at hv; simp only [Option.getD_some] at hv
      exact hVs t (List.mem_of_getElem? h) v hv
  | arrow a b iha ihb =>
    intro hX v hv
    have haa : ∀ w ∈ a.freeVars, w < lo ∨ hi ≤ w := fun w hw =>
      hX w (by simp only [Ty.freeVars, List.mem_dedup, List.mem_append]; exact Or.inl hw)
    have hab : ∀ w ∈ b.freeVars, w < lo ∨ hi ≤ w := fun w hw =>
      hX w (by simp only [Ty.freeVars, List.mem_dedup, List.mem_append]; exact Or.inr hw)
    simp only [Ty.openWith, Ty.instantiate, Ty.freeVars, List.mem_dedup, List.mem_append] at hv
    rcases hv with hv | hv
    · exact iha haa v hv
    · exact ihb hab v hv
  | customTy nm tys ih =>
    intro hX v hv
    simp only [Ty.openWith, Ty.instantiate, TyList.instantiate_eq_map, Ty.freeVars] at hv
    obtain ⟨t', ht', hvt'⟩ := TyList.mem_freeVars_iff.mp hv
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp ht'
    exact ih t ht (fun w hw => hX w (by rw [Ty.freeVars]; exact TyList.mem_freeVars_of_mem ht hw)) v hvt'

mutual
/-- Unifying interval-avoiding monotypes yields an interval-avoiding substitution
    (both domain and range avoid `[lo, hi)`). -/
theorem UnifyRel.gap_avoid {lo hi : Nat} : {a b : Ty} → {S : Subst} → UnifyRel a b S →
    (∀ v ∈ a.freeVars, v < lo ∨ hi ≤ v) → (∀ v ∈ b.freeVars, v < lo ∨ hi ≤ v) →
    (∀ p ∈ S, p.1 < lo ∨ hi ≤ p.1) ∧ (∀ p ∈ S, ∀ v ∈ p.2.freeVars, v < lo ∨ hi ≤ v)
  | _, _, _, .prim, _, _ => ⟨by simp, by simp⟩
  | _, _, _, .fvarRefl, _, _ => ⟨by simp, by simp⟩
  | _, _, _, @UnifyRel.fvarL n τ _ _, ha, hb => by
    refine ⟨?_, ?_⟩
    · intro p hp; rw [List.mem_singleton] at hp; subst hp; exact ha n (by simp [Ty.freeVars])
    · intro p hp v hv; rw [List.mem_singleton] at hp; subst hp; exact hb v hv
  | _, _, _, @UnifyRel.fvarR n τ _ _, ha, hb => by
    refine ⟨?_, ?_⟩
    · intro p hp; rw [List.mem_singleton] at hp; subst hp; exact hb n (by simp [Ty.freeVars])
    · intro p hp v hv; rw [List.mem_singleton] at hp; subst hp; exact ha v hv
  | _, _, _, @UnifyRel.arrow a b c d S₁ S₂ h₁ h₂, ha, hb => by
    have haa : ∀ v ∈ a.freeVars, v < lo ∨ hi ≤ v := fun v hv =>
      ha v (by simp only [Ty.freeVars, List.mem_dedup, List.mem_append]; exact .inl hv)
    have hab : ∀ v ∈ b.freeVars, v < lo ∨ hi ≤ v := fun v hv =>
      ha v (by simp only [Ty.freeVars, List.mem_dedup, List.mem_append]; exact .inr hv)
    have hbc : ∀ v ∈ c.freeVars, v < lo ∨ hi ≤ v := fun v hv =>
      hb v (by simp only [Ty.freeVars, List.mem_dedup, List.mem_append]; exact .inl hv)
    have hbd : ∀ v ∈ d.freeVars, v < lo ∨ hi ≤ v := fun v hv =>
      hb v (by simp only [Ty.freeVars, List.mem_dedup, List.mem_append]; exact .inr hv)
    obtain ⟨hd₁, hr₁⟩ := UnifyRel.gap_avoid h₁ haa hbc
    obtain ⟨hd₂, hr₂⟩ := UnifyRel.gap_avoid h₂ (Subst.onTy_avoidsItv hr₁ hab)
      (Subst.onTy_avoidsItv hr₁ hbd)
    refine ⟨?_, ?_⟩
    · intro p hp; simp only [List.mem_append] at hp; rcases hp with hp | hp
      · exact hd₁ p hp
      · exact hd₂ p hp
    · intro p hp; simp only [List.mem_append] at hp; rcases hp with hp | hp
      · exact hr₁ p hp
      · exact hr₂ p hp
  | _, _, _, @UnifyRel.customTy nm tys₁ tys₂ S hl, ha, hb => by
    exact UnifyRelList.gap_avoid hl
      (fun t ht v hv => ha v (by rw [Ty.freeVars]; exact TyList.mem_freeVars_of_mem ht hv))
      (fun t ht v hv => hb v (by rw [Ty.freeVars]; exact TyList.mem_freeVars_of_mem ht hv))

theorem UnifyRelList.gap_avoid {lo hi : Nat} : {as bs : List Ty} → {S : Subst} →
    UnifyRelList as bs S →
    (∀ t ∈ as, ∀ v ∈ t.freeVars, v < lo ∨ hi ≤ v) →
    (∀ t ∈ bs, ∀ v ∈ t.freeVars, v < lo ∨ hi ≤ v) →
    (∀ p ∈ S, p.1 < lo ∨ hi ≤ p.1) ∧ (∀ p ∈ S, ∀ v ∈ p.2.freeVars, v < lo ∨ hi ≤ v)
  | _, _, _, .nil, _, _ => ⟨by simp, by simp⟩
  | _, _, _, @UnifyRelList.cons t₁ t₂ ts₁ ts₂ S₁ S₂ h₁ ht, ha, hb => by
    obtain ⟨hd₁, hr₁⟩ := UnifyRel.gap_avoid h₁ (ha t₁ List.mem_cons_self)
      (hb t₂ List.mem_cons_self)
    have hmap_a : ∀ t ∈ ts₁.map S₁.onTy, ∀ v ∈ t.freeVars, v < lo ∨ hi ≤ v := by
      intro t htm; obtain ⟨t0, ht0, rfl⟩ := List.mem_map.mp htm
      exact Subst.onTy_avoidsItv hr₁ (ha t0 (List.mem_cons_of_mem _ ht0))
    have hmap_b : ∀ t ∈ ts₂.map S₁.onTy, ∀ v ∈ t.freeVars, v < lo ∨ hi ≤ v := by
      intro t htm; obtain ⟨t0, ht0, rfl⟩ := List.mem_map.mp htm
      exact Subst.onTy_avoidsItv hr₁ (hb t0 (List.mem_cons_of_mem _ ht0))
    obtain ⟨hd₂, hr₂⟩ := UnifyRelList.gap_avoid ht hmap_a hmap_b
    refine ⟨?_, ?_⟩
    · intro p hp; simp only [List.mem_append] at hp; rcases hp with hp | hp
      · exact hd₁ p hp
      · exact hd₂ p hp
    · intro p hp; simp only [List.mem_append] at hp; rcases hp with hp | hp
      · exact hr₁ p hp
      · exact hr₂ p hp
end


/-- An annotation member's scheme-body fvars land in the node's tyFreeVars. -/
private theorem body_freeVars_subset_AnnList {σ : PolyTy} :
    ∀ (anns : List (Option PolyTy)), some σ ∈ anns →
      ∀ v ∈ σ.body.freeVars, v ∈ Expr.tyFreeVars.AnnList.tyFreeVars anns := by
  intro anns
  induction anns with
  | nil => exact fun h => absurd h (by simp)
  | cons a as ih =>
    intro h v hv
    rcases List.mem_cons.mp h with rfl | hm
    · simp only [Expr.tyFreeVars.AnnList.tyFreeVars, Option.elim_some]
      exact List.mem_append.mpr (Or.inl hv)
    · rcases a with _ | σ'
      · simp only [Expr.tyFreeVars.AnnList.tyFreeVars, Option.elim_none]
        exact List.mem_append.mpr (Or.inr (ih hm v hv))
      · simp only [Expr.tyFreeVars.AnnList.tyFreeVars, Option.elim_some]
        exact List.mem_append.mpr (Or.inr (ih hm v hv))

/-- Every spec produced by `RecSpec.init` is a monotype pinned at its block var. -/
private theorem init_spec_mono {Φ : Nat} {anns : List (Option PolyTy)} {s : RecSpec}
    (hs : s ∈ RecSpec.init Φ anns) : ∃ m, Φ ≤ m ∧ s = .mono (.fvar m) := by
  rcases RecSpec.mem_init hs with ⟨m, hmΦ, _, rfl⟩ | ⟨σ', hσ', rfl⟩
  · exact ⟨m, hmΦ, rfl⟩
  · exfalso
    have hmem : RecSpec.ann (.poly σ') ∈ (RecSpec.init Φ anns).map RecSpec.ann :=
      List.mem_map_of_mem hs
    rw [RecSpec.map_ann_init] at hmem
    simpa [RecSpec.ann] using hmem

/-- The `letRec` BODY environment stays interval-avoiding: annotated members
    contribute their declared schemes (whose fvars are the node's annotation
    fvars), unannotated members contribute pool-closed generalisations of their
    solved monotypes (whose fvars are the monotypes'). -/
theorem RecSpecs.ceilingSchemes_avoidsItv {lo hi : Nat} {G : List Nat} {S₁ : Subst}
    (hR₁ : ∀ p ∈ S₁, ∀ v ∈ p.2.freeVars, v < lo ∨ hi ≤ v)
    {Φ : Nat} (hΦ : hi ≤ Φ) :
    ∀ (anns : List (Option PolyTy)),
      (∀ σ, some σ ∈ anns → ∀ v ∈ σ.body.freeVars, v < lo ∨ hi ≤ v) →
      ∀ M ∈ RecSpecs.ceilingSchemes G anns ((RecSpec.init Φ anns).map (RecSpec.onSubst S₁)),
        ∀ v ∈ M.body.freeVars, v < lo ∨ hi ≤ v := by
  intro anns
  induction anns generalizing Φ with
  | nil => intro _ M hM; simp [RecSpecs.ceilingSchemes] at hM
  | cons a as ih =>
    intro hAvoid M hM
    simp only [RecSpec.init, List.map_cons, RecSpecs.ceilingSchemes,
      List.zip_cons_cons, List.map_cons, List.mem_cons] at hM
    rcases hM with rfl | hM
    · intro v hv
      cases a with
      | none =>
        refine Subst.onTy_avoidsItv (S := S₁) (τ := .fvar Φ) hR₁ ?_ v ?_
        · intro w hw
          simp only [Ty.freeVars, List.mem_singleton] at hw
          subst hw
          exact Or.inr hΦ
        · simpa [RecSpec.bodyScheme, RecSpec.onSubst, PolyTy.genGroup] using
            Ty.closeOver_freeVars_subset hv
      | some σ => exact hAvoid σ List.mem_cons_self v hv
    · exact ih (Nat.le_trans hΦ (Nat.le_succ Φ))
        (fun σ hs => hAvoid σ (List.mem_cons_of_mem _ hs)) M hM

mutual
/-- **Gap-avoidance locality** for the source inference relation: a derivation
    whose context env and annotation fvars avoid `[lo, hi)` below the input
    frontier produces an inferred type and an output substitution (domain AND
    range) that avoid it too. -/
theorem Infer.gap_avoid {lo hi : Nat} {Φ ctx e Φ' S τ} (h : Infer Φ ctx e Φ' S τ) :
    hi ≤ Φ → (∀ M ∈ ctx.env, ∀ v ∈ M.body.freeVars, v < lo ∨ hi ≤ v) →
    (∀ y ∈ e.tyFreeVars, y < lo ∨ hi ≤ y) →
    (∀ v ∈ τ.freeVars, v < lo ∨ hi ≤ v) ∧ (∀ p ∈ S, p.1 < lo ∨ hi ≤ p.1) ∧
      (∀ p ∈ S, ∀ v ∈ p.2.freeVars, v < lo ∨ hi ≤ v) := by
  cases h with
  | primLitUnit => intro _ _ _; refine ⟨?_, by simp, by simp⟩; intro v hv; simp [Ty.freeVars, TyList.freeVars] at hv
  | primLitInt => intro _ _ _; refine ⟨?_, by simp, by simp⟩; intro v hv; simp [Ty.freeVars, TyList.freeVars] at hv
  | primLitNat => intro _ _ _; refine ⟨?_, by simp, by simp⟩; intro v hv; simp [Ty.freeVars, TyList.freeVars] at hv
  | primLitChar => intro _ _ _; refine ⟨?_, by simp, by simp⟩; intro v hv; simp [Ty.freeVars, TyList.freeVars] at hv
  | primBinOpIntAdd => intro _ _ _; refine ⟨?_, by simp, by simp⟩; intro v hv; simp [Ty.freeVars, TyList.freeVars] at hv
  | primBinOpIntSub => intro _ _ _; refine ⟨?_, by simp, by simp⟩; intro v hv; simp [Ty.freeVars, TyList.freeVars] at hv
  | primBinOpIntLt => intro _ _ _; refine ⟨?_, by simp, by simp⟩; intro v hv; simp [Ty.freeVars, TyList.freeVars] at hv
  | primBinOpCharLt => intro _ _ _; refine ⟨?_, by simp, by simp⟩; intro v hv; simp [Ty.freeVars, TyList.freeVars] at hv
  | @lambda Φ ctx ann paramTy body Φ₀ Φ' S τb hseed hbody =>
    cases hseed with
    | none =>
      intro hhi hctx htfv
      simp only [Expr.tyFreeVars, Option.elim_none, List.nil_append] at htfv
      have hctx' : ∀ M ∈ ({ ctx with env := PolyTy.mkTrivial (.fvar Φ) :: ctx.env }).env,
          ∀ v ∈ M.body.freeVars, v < lo ∨ hi ≤ v := by
        intro M hM; rcases List.mem_cons.mp hM with rfl | hM
        · intro v hv
          simp only [PolyTy.mkTrivial] at hv
          simp only [Ty.freeVars, List.mem_singleton] at hv
          subst hv; exact Or.inr hhi
        · exact hctx M hM
      obtain ⟨hbτ, hbD, hbR⟩ := Infer.gap_avoid hbody (by omega) hctx' htfv
      have hΦAvoid : ∀ v ∈ (Ty.fvar Φ).freeVars, v < lo ∨ hi ≤ v := fun w hw => by
        simp only [Ty.freeVars, List.mem_singleton] at hw
        subst hw
        exact Or.inr hhi
      refine ⟨?_, hbD, hbR⟩
      intro v hv
      simp only [Ty.freeVars, List.mem_dedup, List.mem_append] at hv
      rcases hv with hv | hv
      · exact Subst.onTy_avoidsItv hbR hΦAvoid v hv
      · exact hbτ v hv
    | some hlc =>
      intro hhi hctx htfv
      simp only [Expr.tyFreeVars, Option.elim_some, List.mem_append] at htfv
      have hTavoid : ∀ v ∈ paramTy.freeVars, v < lo ∨ hi ≤ v := fun v hv => htfv v (.inl hv)
      have hctx' : ∀ M ∈ ({ ctx with env := PolyTy.mkTrivial paramTy :: ctx.env }).env,
          ∀ v ∈ M.body.freeVars, v < lo ∨ hi ≤ v := by
        intro M hM; rcases List.mem_cons.mp hM with rfl | hM
        · exact hTavoid
        · exact hctx M hM
      obtain ⟨hbτ, hbD, hbR⟩ := Infer.gap_avoid hbody hhi hctx' (fun y hy => htfv y (.inr hy))
      refine ⟨?_, hbD, hbR⟩
      intro v hv
      simp only [Ty.freeVars, List.mem_dedup, List.mem_append] at hv
      rcases hv with hv | hv
      · exact Subst.onTy_avoidsItv hbR hTavoid v hv
      · exact hbτ v hv
  | @app Φ ctx f arg Φ₁ Φ₂ S₁ S₂ S₃ τf τa hf harg huni =>
    intro hhi hctx htfv
    simp only [Expr.tyFreeVars, List.mem_append] at htfv
    obtain ⟨hfτ, hfD, hfR⟩ := Infer.gap_avoid hf hhi hctx (fun y hy => htfv y (.inl hy))
    have hle1 := Infer.frontier_le hf
    obtain ⟨hargτ, hargD, hargR⟩ := Infer.gap_avoid harg (by omega)
      (Subst.onCtx_avoidsItv hfR hctx) (fun y hy => htfv y (.inr hy))
    have hle2 := Infer.frontier_le harg
    have hinR : ∀ v ∈ (Ty.arrow τa (Ty.fvar Φ₂)).freeVars, v < lo ∨ hi ≤ v := by
      intro v hv
      simp only [Ty.freeVars, List.mem_dedup, List.mem_append] at hv
      rcases hv with hv | hv
      · exact hargτ v hv
      · simp only [List.mem_singleton] at hv; subst hv; exact Or.inr (by omega)
    obtain ⟨h3D, h3R⟩ := UnifyRel.gap_avoid huni (Subst.onTy_avoidsItv hargR hfτ) hinR
    have hΦ₂Avoid : ∀ v ∈ (Ty.fvar Φ₂).freeVars, v < lo ∨ hi ≤ v := fun w hw => by
      simp only [Ty.freeVars, List.mem_singleton] at hw
      subst hw
      exact Or.inr (by omega)
    refine ⟨?_, ?_, ?_⟩
    · exact Subst.onTy_avoidsItv h3R hΦ₂Avoid
    · intro p hp; simp only [List.mem_append] at hp
      rcases hp with (hp | hp) | hp
      · exact hfD p hp
      · exact hargD p hp
      · exact h3D p hp
    · intro p hp; simp only [List.mem_append] at hp
      rcases hp with (hp | hp) | hp
      · exact hfR p hp
      · exact hargR p hp
      · exact h3R p hp
  | @var Φ ctx i polyTy hlook =>
    intro hhi hctx _
    refine ⟨?_, by simp, by simp⟩
    intro v hv
    rcases Ty.freeVars_openVars_subset v hv with h | h
    · exact hctx polyTy (List.mem_of_getElem? hlook) v h
    · exact Or.inr (by have := freshVars_ge v h; omega)
  | @ctor Φ ctx name ctor hlook =>
    intro hhi _ _
    refine ⟨?_, by simp, by simp⟩
    intro v hv
    rcases Ty.freeVars_openVars_subset v hv with h | h
    · exact absurd h (NoFreeVars.not_mem_freeVars (Ctor.toTy_body_noFreeVars ctor) v)
    · exact Or.inr (by have := freshVars_ge v h; omega)
  | @letIn Φ ctx rhs body Φ₁ Φ₂ S₁ S₂ τ₁ τ₂ hrhs hbody =>
    intro hhi hctx htfv
    simp only [Expr.tyFreeVars, Option.elim_none, List.nil_append, List.mem_append] at htfv
    obtain ⟨hrτ, hrD, hrR⟩ := Infer.gap_avoid hrhs hhi hctx (fun y hy => htfv y (.inl hy))
    have hle1 := Infer.frontier_le hrhs
    have hctx' : ∀ M ∈ ({ (S₁.onCtx ctx) with
        env := genScheme rhs.tyFreeVars (S₁.onCtx ctx).env τ₁ :: (S₁.onCtx ctx).env }).env,
        ∀ v ∈ M.body.freeVars, v < lo ∨ hi ≤ v := by
      intro M hM; rcases List.mem_cons.mp hM with rfl | hM
      · intro v hv; exact hrτ v (Ty.closeOver_freeVars_subset hv)
      · exact Subst.onCtx_avoidsItv hrR hctx M hM
    obtain ⟨hbτ, hbD, hbR⟩ := Infer.gap_avoid hbody (by omega) hctx'
      (fun y hy => htfv y (.inr hy))
    refine ⟨hbτ, ?_, ?_⟩
    · intro p hp; simp only [List.mem_append] at hp; rcases hp with hp | hp
      · exact hrD p hp
      · exact hbD p hp
    · intro p hp; simp only [List.mem_append] at hp; rcases hp with hp | hp
      · exact hrR p hp
      · exact hbR p hp
  | @letInAnn Φ N ctx σ rhs body Φ₁ Φ₂ S₁ Schk S₂ τ₁ τ₂ _ hN hrhs huni _hesc1 _hesc2 hbody =>
    intro hhi hctx htfv
    simp only [Expr.tyFreeVars, Option.elim_some, List.mem_append] at htfv
    have hle1 := Infer.frontier_le hrhs
    have hrhsTfv : ∀ y ∈ (rhs.openTyVars (freshVars N σ.paramCount)).tyFreeVars,
        y < lo ∨ hi ≤ y := by
      intro y hy
      rcases Expr.tyFreeVars_openTyVars hy with hh | hh
      · exact htfv y (Or.inl (Or.inr hh))
      · exact Or.inr (by have := freshVars_ge y hh; omega)
    obtain ⟨hrτ, hrD, hrR⟩ := Infer.gap_avoid hrhs (by omega) hctx hrhsTfv
    have hσopenAvoid : ∀ v ∈ (σ.openVars (freshVars N σ.paramCount)).freeVars,
        v < lo ∨ hi ≤ v := by
      intro v hv
      rcases Ty.freeVars_openVars_subset v hv with hh | hh
      · exact htfv v (Or.inl (Or.inl hh))
      · exact Or.inr (by have := freshVars_ge v hh; omega)
    obtain ⟨hSchkD, hSchkR⟩ := UnifyRel.gap_avoid huni hrτ hσopenAvoid
    have hctx2 := Subst.onCtx_avoidsItv hSchkR (Subst.onCtx_avoidsItv hrR hctx)
    have hctx' : ∀ M ∈ ({ (Schk.onCtx (S₁.onCtx ctx)) with
        env := σ :: (Schk.onCtx (S₁.onCtx ctx)).env }).env,
        ∀ v ∈ M.body.freeVars, v < lo ∨ hi ≤ v := by
      intro M hM; rcases List.mem_cons.mp hM with rfl | hM
      · intro v hv; exact htfv v (Or.inl (Or.inl hv))
      · exact hctx2 M hM
    obtain ⟨hbτ, hbD, hbR⟩ := Infer.gap_avoid hbody (by omega) hctx'
      (fun y hy => htfv y (.inr hy))
    refine ⟨hbτ, ?_, ?_⟩
    · intro p hp; simp only [List.mem_append] at hp
      rcases hp with (hp | hp) | hp
      · exact hrD p hp
      · exact hSchkD p hp
      · exact hbD p hp
    · intro p hp; simp only [List.mem_append] at hp
      rcases hp with (hp | hp) | hp
      · exact hrR p hp
      · exact hSchkR p hp
      · exact hbR p hp
  | @match_ Φ ctx scrut branches Φ₁ Φ₂ S₁ S₂ τs hscrut hne hbr =>
    intro hhi hctx htfv
    simp only [Expr.tyFreeVars, List.mem_append] at htfv
    obtain ⟨hsτ, hsD, hsR⟩ := Infer.gap_avoid hscrut hhi hctx (fun y hy => htfv y (.inl hy))
    have hle1 := Infer.frontier_le hscrut
    have hΦ₁Avoid : ∀ v ∈ (Ty.fvar Φ₁).freeVars, v < lo ∨ hi ≤ v := fun w hw => by
      simp only [Ty.freeVars, List.mem_singleton] at hw
      subst hw
      exact Or.inr (by omega)
    obtain ⟨hρτ, h3D, h3R⟩ := InferBranches.gap_avoid hbr (by omega)
      (Subst.onCtx_avoidsItv hsR hctx) hsτ hΦ₁Avoid
      (fun y hy => htfv y (.inr hy))
    refine ⟨hρτ, ?_, ?_⟩
    · intro p hp; simp only [List.mem_append] at hp
      rcases hp with hp | hp
      · exact hsD p hp
      · exact h3D p hp
    · intro p hp; simp only [List.mem_append] at hp
      rcases hp with hp | hp
      · exact hsR p hp
      · exact h3R p hp
  | @letRec Φ ctx anns bindings body Φ₁ Φ₂ S₁ Sc S₂ τ₂ Kc G specs1 specsC
      _ hgroup hspecs1 hG hSc hspecsC _ hbody =>
    intro hhi hctx htfv
    simp only [Expr.tyFreeVars] at htfv
    have hAnnsAvoid : ∀ σ, some σ ∈ anns → ∀ v ∈ σ.body.freeVars, v < lo ∨ hi ≤ v :=
      fun σ hs v hv => htfv v
        (List.mem_append.mpr (Or.inl
          (List.mem_append.mpr (Or.inl (body_freeVars_subset_AnnList anns hs v hv)))))
    have hBindAvoid : ∀ y ∈ Expr.tyFreeVars.RecGroup.tyFreeVars bindings,
        y < lo ∨ hi ≤ y :=
      fun y hy => htfv y
        (List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inr hy))))
    have hBodyAvoid : ∀ y ∈ body.tyFreeVars, y < lo ∨ hi ≤ y :=
      fun y hy => htfv y (List.mem_append.mpr (Or.inr hy))
    -- the recursive group
    have hGroupCtx : ∀ M ∈ ({ ctx with
        env := (RecSpec.init Φ anns).map (RecSpec.rhsEntry [] []) ++ ctx.env }).env,
        ∀ v ∈ M.body.freeVars, v < lo ∨ hi ≤ v := by
      intro M hM
      rcases List.mem_append.mp hM with hM | hM
      · obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hM
        obtain ⟨m, hmΦ, rfl⟩ := init_spec_mono hs
        intro v hv
        have hv' : v = m := by
          have hv2 : v ∈ (Ty.fvar m).freeVars := by
            simp [RecSpec.rhsEntry, Ty.renameG, PolyTy.mkTrivial, Ty.substFvars] at hv
            simpa using hv
          exact List.mem_singleton.mp hv2
        subst hv'
        exact Or.inr (Nat.le_trans hhi hmΦ)
      · exact hctx M hM
    have hGroupTargets : ∀ β ∈ RecSpec.init Φ anns,
        ∀ v ∈ β.tfvs, v < lo ∨ hi ≤ v := by
      intro β hb
      obtain ⟨m, hmΦ, rfl⟩ := init_spec_mono hb
      intro v hv
      simp only [RecSpec.tfvs, Ty.freeVars, List.mem_singleton] at hv
      subst hv
      exact Or.inr (Nat.le_trans hhi hmΦ)
    obtain ⟨hgD, hgR⟩ := InferRecGroup.gap_avoid hgroup (by omega) hGroupCtx
      hGroupTargets hBindAvoid
    -- The ceiling pass can only write ambient rigid names.  Those are
    -- annotation/binding fvars of this node, hence inherit the gap invariant.
    have hRigidAvoid : ∀ x ∈ RecGroup.rigidVars anns bindings,
        x < lo ∨ hi ≤ x := by
      intro x hx
      simp only [RecGroup.rigidVars, List.mem_append] at hx
      rcases hx with hx | hx
      · exact htfv x (List.mem_append.mpr (Or.inl
          (List.mem_append.mpr (Or.inl hx))))
      · exact htfv x (List.mem_append.mpr (Or.inl
          (List.mem_append.mpr (Or.inr
            (Expr.mem_flatMap_tyFreeVars_iff_recGroup.mp hx)))))
    have hSpecs1Avoid : ∀ s ∈ specs1, ∀ v ∈ s.freeVars,
        v < lo ∨ hi ≤ v := by
      intro s hs v hv
      rw [hspecs1] at hs
      obtain ⟨s0, hs0, rfl⟩ := List.mem_map.mp hs
      obtain ⟨m, hmΦ, rfl⟩ := init_spec_mono hs0
      exact Subst.onTy_avoidsItv hgR
        (fun w hw => by
          simp only [Ty.freeVars, List.mem_singleton] at hw
          subst hw
          exact Or.inr (Nat.le_trans hhi hmΦ)) v hv
    have hScR : ∀ p ∈ Sc, ∀ v ∈ p.2.freeVars, v < lo ∨ hi ≤ v := by
      intro p hp v hv
      exact hRigidAvoid v (RecCeilingConstraints.range_subset_rigid hSc p hp v hv)
    have hScD : ∀ p ∈ Sc, p.1 < lo ∨ hi ≤ p.1 := by
      intro p hp
      by_cases hpΦ : p.1 < Φ₁
      · by_contra hbad
        have hpRigid : p.1 ∉ RecGroup.rigidVars anns bindings :=
          fun hmem => hbad (hRigidAvoid p.1 hmem)
        have hpSpecs : ∀ s ∈ specs1, p.1 ∉ s.freeVars := by
          intro s hs hmem
          exact hbad (hSpecs1Avoid s hs p.1 hmem)
        have hnot := RecCeilingConstraints.dom_avoid hSc hpRigid hpΦ hpSpecs
        apply hnot
        exact List.mem_map.mpr ⟨p, hp, rfl⟩
      · right
        have hΦ₁ : Φ ≤ Φ₁ := by have := InferRecGroup.frontier_le hgroup; omega
        omega
    have hBothR : ∀ p ∈ S₁ ++ Sc, ∀ v ∈ p.2.freeVars, v < lo ∨ hi ≤ v := by
      intro p hp
      rcases List.mem_append.mp hp with hp | hp
      · exact hgR p hp
      · exact hScR p hp
    have hSpecsCEq : specsC =
        (RecSpec.init Φ anns).map (RecSpec.onSubst (S₁ ++ Sc)) := by
      rw [hspecsC, hspecs1, List.map_map]
      apply List.map_congr_left
      intro s _
      exact (RecSpec.onSubst_append S₁ Sc s).symm
    -- the body environment (ceiling schemes over the twice-solved monotypes)
    have hBodyCtx : ∀ M ∈ ({ (Sc.onCtx (S₁.onCtx ctx)) with
        env := RecSpecs.ceilingSchemes
                  G
                  anns
                  specsC
                ++ (Sc.onCtx (S₁.onCtx ctx)).env }).env,
        ∀ v ∈ M.body.freeVars, v < lo ∨ hi ≤ v := by
      intro M hM
      rcases List.mem_append.mp hM with hM | hM
      · rw [hSpecsCEq] at hM
        exact RecSpecs.ceilingSchemes_avoidsItv hBothR hhi anns hAnnsAvoid M hM
      · exact Subst.onCtx_avoidsItv hScR (Subst.onCtx_avoidsItv hgR hctx) M hM
    obtain ⟨hbτ, hbD, hbR⟩ := Infer.gap_avoid hbody
      (by have := InferRecGroup.frontier_le hgroup; omega) hBodyCtx hBodyAvoid
    refine ⟨hbτ, ?_, ?_⟩
    · intro p hp; simp only [List.mem_append] at hp
      rcases hp with (hp | hp) | hp
      · exact hgD p hp
      · exact hScD p hp
      · exact hbD p hp
    · intro p hp; simp only [List.mem_append] at hp
      rcases hp with (hp | hp) | hp
      · exact hgR p hp
      · exact hScR p hp
      · exact hbR p hp
termination_by e.size
decreasing_by
  all_goals (try subst_vars)
  all_goals (try simp only [Expr.size, Expr.size_openTyVars])
  all_goals omega

/-- Gap-avoidance locality through a `match_` branch list. -/
theorem InferBranches.gap_avoid {lo hi : Nat} {Φ ctx scrutTy ρ brs Φ' S}
    (h : InferBranches Φ ctx scrutTy ρ brs Φ' S) :
    hi ≤ Φ → (∀ M ∈ ctx.env, ∀ v ∈ M.body.freeVars, v < lo ∨ hi ≤ v) →
    (∀ v ∈ scrutTy.freeVars, v < lo ∨ hi ≤ v) →
    (∀ v ∈ ρ.freeVars, v < lo ∨ hi ≤ v) →
    (∀ y ∈ Expr.tyFreeVars.BranchList.tyFreeVars brs, y < lo ∨ hi ≤ y) →
    (∀ v ∈ (S.onTy ρ).freeVars, v < lo ∨ hi ≤ v) ∧ (∀ p ∈ S, p.1 < lo ∨ hi ≤ p.1) ∧
      (∀ p ∈ S, ∀ v ∈ p.2.freeVars, v < lo ∨ hi ≤ v) := by
  cases h with
  | nil =>
    intro _ _ _ hρ _
    exact ⟨by simpa [Subst.onTy_nil] using hρ, by simp, by simp⟩
  | @cons Φ ctx scrutTy ρ c n body rest ctor Φ₁ Φ₂ S₀ S₁ S₂ S₃ τb
      hlook hn huni0 hbody huni hrest =>
    intro hhi hctx hscrutTy hρ htfv
    simp only [Expr.tyFreeVars.BranchList.tyFreeVars, List.mem_append] at htfv
    have hcustomAvoid : ∀ v ∈ (Ty.customTy ctor.tyName
        ((freshVars Φ ctor.paramCount).map (Ty.fvar ·))).freeVars, v < lo ∨ hi ≤ v := by
      intro v hv
      rw [Ty.freeVars] at hv
      obtain ⟨t, ht, hvt⟩ := TyList.mem_freeVars_iff.mp hv
      obtain ⟨x, hx, hxeq⟩ := List.mem_map.mp ht
      rw [← hxeq] at hvt
      simp only [Ty.freeVars, List.mem_singleton] at hvt
      exact Or.inr (by have := freshVars_ge x hx; omega)
    obtain ⟨h0D, h0R⟩ := UnifyRel.gap_avoid huni0 hscrutTy hcustomAvoid
    have hta₀ : ∀ t ∈ ((freshVars Φ ctor.paramCount).map (Ty.fvar ·)).map S₀.onTy,
        ∀ v ∈ t.freeVars, v < lo ∨ hi ≤ v := by
      intro t ht v hv
      obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hs
      exact Subst.onTy_avoidsItv h0R (fun w hw => by
        simp only [Ty.freeVars, List.mem_singleton] at hw
        exact Or.inr (by have := freshVars_ge x hx; omega)) v hv
    have hbind : ∀ M ∈ ({ S₀.onCtx ctx with
        env := (ctor.contents.map (Ty.openWith
            (((freshVars Φ ctor.paramCount).map (Ty.fvar ·)).map S₀.onTy))).map PolyTy.mkTrivial
          ++ (S₀.onCtx ctx).env }).env,
        ∀ v ∈ M.body.freeVars, v < lo ∨ hi ≤ v := by
      intro M hM
      rw [List.mem_append] at hM
      rcases hM with hM | hM
      · obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hM
        obtain ⟨c', hc, rfl⟩ := List.mem_map.mp ht
        exact Ty.openWith_avoidsItv hta₀
          (fun v hv => absurd hv (NoFreeVars.not_mem_freeVars (ctor.closed c' hc) v))
      · exact (Subst.onCtx_avoidsItv h0R hctx) M hM
    obtain ⟨hτb, hbD, hbR⟩ := Infer.gap_avoid hbody (by omega) hbind
      (fun y hy => htfv y (.inl hy))
    have hle1 := Infer.frontier_le hbody
    have hS₁S₀ρ : ∀ v ∈ (S₁.onTy (S₀.onTy ρ)).freeVars, v < lo ∨ hi ≤ v :=
      Subst.onTy_avoidsItv hbR (Subst.onTy_avoidsItv h0R hρ)
    obtain ⟨h2D, h2R⟩ := UnifyRel.gap_avoid huni hτb hS₁S₀ρ
    have hscrut' : ∀ v ∈ (S₂.onTy (S₁.onTy (S₀.onTy scrutTy))).freeVars,
        v < lo ∨ hi ≤ v :=
      Subst.onTy_avoidsItv h2R (Subst.onTy_avoidsItv hbR (Subst.onTy_avoidsItv h0R hscrutTy))
    obtain ⟨hresτ, h3D, h3R⟩ := InferBranches.gap_avoid hrest (by omega)
      (Subst.onCtx_avoidsItv h2R (Subst.onCtx_avoidsItv hbR (Subst.onCtx_avoidsItv h0R hctx)))
      hscrut' (Subst.onTy_avoidsItv h2R hS₁S₀ρ)
      (fun y hy => htfv y (.inr hy))
    refine ⟨?_, ?_, ?_⟩
    · rw [Subst.onTy_append, Subst.onTy_append, Subst.onTy_append]; exact hresτ
    · intro p hp; simp only [List.mem_append] at hp
      rcases hp with ((hp | hp) | hp) | hp
      · exact h0D p hp
      · exact hbD p hp
      · exact h2D p hp
      · exact h3D p hp
    · intro p hp; simp only [List.mem_append] at hp
      rcases hp with ((hp | hp) | hp) | hp
      · exact h0R p hp
      · exact hbR p hp
      · exact h2R p hp
      · exact h3R p hp
  | @consWild Φ ctx scrutTy ρ body rest Φ₁ Φ₂ S₁ S₂ S₃ τb hbody huni hrest =>
    intro hhi hctx hscrutTy hρ htfv
    simp only [Expr.tyFreeVars.BranchList.tyFreeVars, List.mem_append] at htfv
    obtain ⟨hτb, hbD, hbR⟩ := Infer.gap_avoid hbody hhi hctx (fun y hy => htfv y (.inl hy))
    have hle1 := Infer.frontier_le hbody
    have hS₁ρ : ∀ v ∈ (S₁.onTy ρ).freeVars, v < lo ∨ hi ≤ v := Subst.onTy_avoidsItv hbR hρ
    obtain ⟨h2D, h2R⟩ := UnifyRel.gap_avoid huni hτb hS₁ρ
    have hscrut' : ∀ v ∈ (S₂.onTy (S₁.onTy scrutTy)).freeVars, v < lo ∨ hi ≤ v :=
      Subst.onTy_avoidsItv h2R (Subst.onTy_avoidsItv hbR hscrutTy)
    obtain ⟨hresτ, h3D, h3R⟩ := InferBranches.gap_avoid hrest (by omega)
      (Subst.onCtx_avoidsItv h2R (Subst.onCtx_avoidsItv hbR hctx)) hscrut'
      (Subst.onTy_avoidsItv h2R hS₁ρ)
      (fun y hy => htfv y (.inr hy))
    refine ⟨?_, ?_, ?_⟩
    · rw [Subst.onTy_append, Subst.onTy_append]; exact hresτ
    · intro p hp; simp only [List.mem_append] at hp
      rcases hp with ((hp | hp) | hp)
      · exact hbD p hp
      · exact h2D p hp
      · exact h3D p hp
    · intro p hp; simp only [List.mem_append] at hp
      rcases hp with ((hp | hp) | hp)
      · exact hbR p hp
      · exact h2R p hp
      · exact h3R p hp
termination_by Expr.sizeBranches brs
decreasing_by
  all_goals (try subst_vars; simp only [Expr.sizeBranches]; omega)

theorem InferRecGroup.gap_avoid {lo hi : Nat} {Φ ctx bindings specs Φ' S}
    (h : InferRecGroup Φ ctx bindings specs Φ' S) :
    hi ≤ Φ → (∀ M ∈ ctx.env, ∀ v ∈ M.body.freeVars, v < lo ∨ hi ≤ v) →
    (∀ β ∈ specs, ∀ v ∈ β.tfvs, v < lo ∨ hi ≤ v) →
    (∀ y ∈ Expr.tyFreeVars.RecGroup.tyFreeVars bindings, y < lo ∨ hi ≤ y) →
    (∀ p ∈ S, p.1 < lo ∨ hi ≤ p.1) ∧ (∀ p ∈ S, ∀ v ∈ p.2.freeVars, v < lo ∨ hi ≤ v) := by
  cases h with
  | nil => intro _ _ _ _; exact ⟨by simp, by simp⟩
  | @cons Φ ctx e rest τ specs Φ₁ Φ₂ S₁ S₂ S₃ τ' he huni hrest =>
    intro hhi hctx hspecs htfv
    obtain ⟨hτ', hD₁, hR₁⟩ := Infer.gap_avoid he hhi hctx
      (fun y hy => htfv y (List.mem_append.mpr (Or.inl hy)))
    have hle1 := Infer.frontier_le he
    have hτav : ∀ v ∈ τ.freeVars, v < lo ∨ hi ≤ v :=
      hspecs (.mono τ) List.mem_cons_self
    obtain ⟨hD₂, hR₂⟩ := UnifyRel.gap_avoid huni hτ' (Subst.onTy_avoidsItv hR₁ hτav)
    have hRboth : ∀ p ∈ S₁ ++ S₂, ∀ v ∈ p.2.freeVars, v < lo ∨ hi ≤ v := by
      intro p hp; rcases List.mem_append.mp hp with hp | hp
      · exact hR₁ p hp
      · exact hR₂ p hp
    obtain ⟨hD₃, hR₃⟩ := InferRecGroup.gap_avoid hrest (by omega)
      (Subst.onCtx_avoidsItv hR₂ (Subst.onCtx_avoidsItv hR₁ hctx))
      (by
        intro β hb v hv
        obtain ⟨s₀, hs₀, rfl⟩ := List.mem_map.mp hb
        cases s₀ with
        | mono t₀ =>
          refine Subst.onTy_avoidsItv (S := S₁ ++ S₂) (τ := t₀) hRboth ?_ v hv
          exact hspecs _ (List.mem_cons_of_mem _ hs₀)
        | poly σ₀ => exact hspecs _ (List.mem_cons_of_mem _ hs₀) v hv)
      (fun y hy => htfv y (List.mem_append.mpr (Or.inr hy)))
    refine ⟨?_, ?_⟩
    · intro p hp; simp only [List.mem_append] at hp
      rcases hp with (hp | hp) | hp
      · exact hD₁ p hp
      · exact hD₂ p hp
      · exact hD₃ p hp
    · intro p hp; simp only [List.mem_append] at hp
      rcases hp with (hp | hp) | hp
      · exact hR₁ p hp
      · exact hR₂ p hp
      · exact hR₃ p hp
termination_by Expr.sizeRecGroup bindings
decreasing_by
  all_goals (try subst_vars)
  all_goals (try simp only [Expr.size, Expr.size_openTyVars, Expr.sizeRecGroup])
  all_goals omega

end


/-! ## 4. Principality of a given inference (the D2 spine)

`Infer.Principal h hwf hbelow` says: whenever the source program `e` (including
its annotations) is declaratively HM-typeable at some type, the given inference
output `(S, τ)` is principal — every such typing factors through `τ` via an LC
residual fixing `K`.

Each Principal also carries the working conjunct
`Subst.AgreesBelow Φ S₀ (S ++ R)`, which sustains K-fixing through residual
composition. -/

/-- `U` factors through `S` with residual `R`. -/
def Subst.Factors (U S R : Subst) : Prop :=
  ∀ τ, U.onTy τ = R.onTy (S.onTy τ)

/-- Principality of the inference output `(S, τ)`: whenever the source program
    types declaratively under an ambient substitution, every such typing factors
    through `τ` via an LC residual fixing `K`. -/
def Infer.Principal {Φ : Nat} {ctx : Ctx} {e : Expr} {Φ' : Nat} {S : Subst} {τ : Ty}
    (_h : Infer Φ ctx e Φ' S τ) : Prop :=
  CtxWF ctx → CtxBelow Φ ctx →
  ∀ (S₀ : Subst) (τe : Ty) (K : List Nat),
    (∀ p ∈ S₀, p.2.IsLC) → (∀ k ∈ K, k < Φ) → (∀ y ∈ e.tyFreeVars, y ∈ K) →
    (∀ k ∈ K, S₀.onTy (.fvar k) = .fvar k) →
    TypeOfHM (S₀.onCtx ctx) e τe →
    ∃ R : Subst, (∀ p ∈ R, p.2.IsLC) ∧
      τe = R.onTy τ ∧ (∀ k ∈ K, R.onTy (.fvar k) = .fvar k) ∧
      Subst.AgreesBelow Φ S₀ (S ++ R)

/-- Principality for a `match_` branch-list thread: given the declarative
    per-branch typings at the ambient
    specialization `S₀`, the threaded result type is principal.

    **UNSOUNDNESS FIX 2026-08-26** (restatement authorised; see the deviation
    note below): the previous statement concluded with the *pure*
    `Subst.AgreesBelow Φ S₀ (S ++ R)` — demanded at every `v < Φ`, which for
    the `match_` caller (`Φ = Φ₁ + 1`) includes `v = Φ₁`, the running result
    variable `.fvar Φ₁` itself. At `v = Φ₁` nothing links the ambient action to
    the unifier-applied output (counterexample: `match (var 0) [wildcard
    primLitInt]` — the only declarative data is the branch's
    `Eq (.fvar 1) (.prim .int)`, which no premise forces), so the old
    statement was FALSE. The restatement:
      * replaces the free `Eq ρe (R.onTy ρ)` conjunct with the
        output-form `Eq ρe (R.onTy (S.onTy ρ))` — the match node's output
        type IS `S₂.onTy (.fvar Φ₁)` (old match-aux STEP 5's `τ₀ = R₂.onTy
        (S₂.onTy (.fvar Φ₁))`, recovered as a first-class conjunct);
      * adds the two IMAGE premises `Eq ρe (S₀.onTy ρ)` and
        `Eq scruT₀ (S₀.onTy scrutTy)` — each is REFLEXIVE at the
        top-level dodge call from COMPLETE-MATCH (`S₀ = U`, `ρe = U.onTy ρ`,
        `scruT₀ = U.onTy scrutTy`), and inside each `cons`/`consWild` step they
        are re-derived at the next residual from the body IH's `AgreesBelow`
        plus the `greatest_K_factors` factoring (old complete's `key_full`/`hUni`
        steps, now Eq-flavoured);
      * states LC/below-ness on the ALGORITHMIC types (`scrutTy`, `ρ`) instead
        of the declarative ones, and drops the scrutinee-term premise `s`
        entirely: the branch premises are transportable between worlds only by
        CONTEXT rewriting (`Subst.onCtx_congr`), keeping `scruT₀`/`ρe`
        unchanged — a changed *declarative* scrutinee/result type is not
        re-constructible from a `TypeOfMatchBranch` up to `Eq` (the `mk`
        rule's `scrut_eq` is structural), so `s`/`scruT₀`-below-ness premises
        would be un-provided by COMPLETE-MATCH. -/
def InferBranches.Principal {Φ : Nat} {ctx : Ctx} {scrutTy : Ty} {ρ : Ty}
    {brs : List (MatchPattern × Expr)} {Φ' : Nat} {S : Subst}
    (_h : InferBranches Φ ctx scrutTy ρ brs Φ' S) (hne : brs ≠ []) : Prop :=
  CtxWF ctx → CtxBelow Φ ctx →
  ∀ (S₀ : Subst) (scruT₀ ρe : Ty) (K : List Nat),
    (∀ p ∈ S₀, p.2.IsLC) → scruT₀.IsLC → scrutTy.IsLC → ρ.IsLC →
    Ty.BelowFvars Φ scrutTy → Ty.BelowFvars Φ ρ →
    (∀ k ∈ K, k < Φ) →
    (∀ y ∈ Expr.tyFreeVars.BranchList.tyFreeVars brs, y ∈ K) →
    (∀ k ∈ K, S₀.onTy (.fvar k) = .fvar k) →
    ρe = S₀.onTy ρ →
    scruT₀ = S₀.onTy scrutTy →
    (∀ b ∈ brs, TypeOfMatchBranch (S₀.onCtx ctx) (b.1, b.2)
        scruT₀ ρe) →
    ∃ R : Subst, (∀ p ∈ R, p.2.IsLC) ∧
      Subst.AgreesBelow Φ S₀ (S ++ R) ∧
      (∀ k ∈ K, R.onTy (.fvar k) = .fvar k) ∧
      ρe = R.onTy (S.onTy ρ)

/-- Principality for a recursive-group thread — **ADOPTED STATEMENT** (2026-08-26,
    design pass, supersedes the interim restatement of commit `874553b`): given
    the declarative DM-cut group premises at the ambient context and per-member
    binding terms — the mono members' RHSs at the `R₀`-transported
    monotypes `(R₀.onTy τ)`, the annotated members'
    RHSs opened at fresh `Ys` against their schemes `σ.openVars Ys` (a poly spec
    is rigid under `R₀`) — an LC residual `R` fixing `K` exists, agreeing with
    `S₀` below the pre-block frontier `Φ₀`.

    Deviation notes (all documented at this site):
    * **`Φ₀`/`hle` (pre-block frontier, 2026-08-26)**: the D2 port revealed that
      `hAgree`/the conclusion CANNOT range over the group's own frontier `Φ`
      (the `Infer.letRec` call runs the tier at `Φ + bindings.length` over the
      init block `fvar (Φ+j)`): the caller's ambient `S₀` fixes `K` only, so its
      action on the block is unconstrained, while `COMPLETE-LETREC` must
      construct `R₀` sending the block onto the declarative opened witnesses
      (`exists_recgroup_residual`) — the block link makes the mono premise
      manufacturable, and `Φ₀`-restricted agreement is exactly what the
      `letRec` node's `Infer.Principal` conclusion consumes. Inside the tier the
      `Φ₀`-agreement is composed from the member IHs' full-frontier agreements
      by restriction (`frontier_le`); `hle : Φ₀ ≤ Φ` carries the inclusion.
    * **`hKsch` added**: the poly head's scheme-relative RHS typing needs the
      scheme's body free vars fixed by the residual, so they must sit in `K`
      (the poly premise quantifies over `σ.openVars Ys`, whose free vars are
      `σ.body.freeVars ∪ Ys`). Vacuous over the all-mono `RecSpec.init` specs of
      the top-level call from COMPLETE-LETREC.
    * No declarative `dspecs`/`annsE`/`Xs`/linking-equation premises: the
      per-member image typings are carried directly over `bindings.zip specs`
      (the pre-check's recommendation; cf.
      briefs/completeness-spine-pivot.md).
    * The `R₀` residual is a PREMISE (the ambient specialization the declarative
      premises sit at), not an output; the output residual `R` is the
      composition-partner of `S` in `AgreesBelow Φ₀ S₀ (S ++ R)`. -/
def InferRecGroup.Principal {Φ₀ Φ : Nat} {ctx : Ctx} {bindings : List Expr}
    {specs : List RecSpec} {Φ' : Nat} {S : Subst}
    (_h : InferRecGroup Φ ctx bindings specs Φ' S) (hle : Φ₀ ≤ Φ) : Prop :=
  CtxWF ctx → CtxBelow Φ ctx →
  ∀ (S₀ : Subst) (L K : List Nat) (R₀ : Subst),
    (∀ p ∈ S₀, p.2.IsLC) → (∀ k ∈ K, k < Φ₀) →
    (∀ y ∈ Expr.tyFreeVars.RecGroup.tyFreeVars bindings, y ∈ K) →
    (∀ k ∈ K, S₀.onTy (.fvar k) = .fvar k) →
    (∀ s ∈ specs, RecSpec.LC s) →
    (∀ s ∈ specs, ∀ τ, s = RecSpec.mono τ → Ty.BelowFvars Φ τ) →
    (∀ s ∈ specs, ∀ σ, s = RecSpec.poly σ → ∀ y ∈ σ.body.freeVars, y ∈ K) →
    (∀ p ∈ R₀, p.2.IsLC) → (∀ k ∈ K, R₀.onTy (.fvar k) = .fvar k) →
    (∀ v, v < Φ₀ → R₀.onTy (.fvar v) = S₀.onTy (.fvar v)) →
    (∀ p ∈ bindings.zip specs, ∀ τ, p.2 = RecSpec.mono τ →
      TypeOfHM (R₀.onCtx ctx) ( p.1)
        ( (R₀.onTy τ))) →
    (∀ p ∈ bindings.zip specs, ∀ σ, p.2 = RecSpec.poly σ →
      ∀ Ys, FreshNames L σ.paramCount Ys →
        TypeOfHM (R₀.onCtx ctx)
          ( (Expr.openTyVars Ys p.1)) (σ.openVars Ys)) →
    ∃ R : Subst, (∀ p ∈ R, p.2.IsLC) ∧ (∀ k ∈ K, R.onTy (.fvar k) = .fvar k) ∧
      Subst.AgreesBelow Φ₀ S₀ (S ++ R) ∧ Subst.AgreesBelow Φ R₀ (S ++ R)

/-! ### Helper lemmas for the D2 spine (branch tier)

The branch tier's `cons` case needs a direct-HM version of the old
`customTy_factor_dodge` (ffc544f): given the branch's own MGU `S₀` (from a
*given* `InferBranches.cons` derivation), the ambient residual `R` factors
through it via a fresh `R₀` that (i) reconciles `R` and `R₀ ∘ S₀` below `Φ`
(the `Subst.AgreesBelow Φ R (S₀ ++ R₀)` working conjunct of
`InferBranches.Principal`), and (ii) sends the S₀-applied fresh block
onto the declarative `tyArgs` — exactly the clause
`branchBindings`'s documentation mentions. The witness is the same
three-zone dodge `fresh ↦ Ws ++ R ++ Ws ↦ tyArgs` as the old unifier-dodge,
with the old structural "`R.onTy scrutTy` = customTy" link replaced by the
Eq image premise `hscrutImg` (reflexive at the top-level call from
COMPLETE-MATCH). -/

/-- A `nil` branch-list derivation is fully determined: the output frontier is
    the input frontier and the output substitution is empty. (Extracted as a
    lemma because `cases` on the derivation inside the branch tier's `cons`
    case clears the enclosing frontier binder from scope.) -/
theorem InferBranches.nil_det {Φ₁ : Nat} {ctx' : Ctx} {scrutTy' ρ' : Ty} {Φ₂ : Nat} {S₃ : Subst}
    (h : InferBranches Φ₁ ctx' scrutTy' ρ' [] Φ₂ S₃) : Φ₂ = Φ₁ ∧ S₃ = [] := by
  cases h with
  | nil => exact ⟨rfl, rfl⟩

/-- The named-branch `customTy` factoring dodge (given-MGU form).
    `R` factors through the branch's MGU `S₀` via an LC, `K`-fixing `R₀` whose
    composition with `S₀` agrees with `R` below `Φ` and maps the
    S₀-applied fresh block onto `tyArgs`. -/
theorem customTy_factor_dodge {Φ : Nat} {scrutTy : Ty} {R S₀ : Subst}
    {K : List Nat} {ctor : Ctor} {tyArgs : List Ty}
    (h₀ : UnifyRel scrutTy
      (.customTy ctor.tyName ((freshVars Φ ctor.paramCount).map (Ty.fvar ·))) S₀)
    (hbscrut : Ty.BelowFvars Φ scrutTy)
    (hR : ∀ p ∈ R, p.2.IsLC)
    (hKΦ : ∀ k ∈ K, k < Φ)
    (hKfix : ∀ k ∈ K, R.onTy (.fvar k) = .fvar k)
    (hpc : ctor.paramCount = tyArgs.length)
    (htyArgs_lc : ∀ t ∈ tyArgs, t.IsLC)
    (hscrutImg : .customTy ctor.tyName tyArgs = R.onTy scrutTy) :
    ∃ R₀ : Subst,
      (∀ p ∈ R₀, p.2.IsLC) ∧
      (∀ k ∈ K, R₀.onTy (.fvar k) = .fvar k) ∧
      (∀ v, v < Φ → R.onTy (.fvar v) = R₀.onTy (S₀.onTy (.fvar v))) ∧
      ((freshVars Φ ctor.paramCount).map (Ty.fvar ·) |>.map S₀.onTy |>.map R₀.onTy)
        = tyArgs := by
  obtain ⟨W, hWge, hWfresh⟩ := exists_fresh_block
    (R.map Prod.fst ++ R.flatMap (fun p => p.2.freeVars) ++
      tyArgs.flatMap Ty.freeVars ++ List.range Φ) Φ ctor.paramCount
  obtain ⟨U, hUdef⟩ : ∃ U : Subst,
    U = (freshVars Φ ctor.paramCount).zip ((freshVars W ctor.paramCount).map (Ty.fvar ·))
        ++ R ++ (freshVars W ctor.paramCount).zip tyArgs := ⟨_, rfl⟩
  have hUonTy : ∀ x, U.onTy x =
      Subst.onTy ((freshVars W ctor.paramCount).zip tyArgs)
        (R.onTy (Subst.onTy ((freshVars Φ ctor.paramCount).zip
          ((freshVars W ctor.paramCount).map (Ty.fvar ·))) x)) := by
    intro x; rw [hUdef, Subst.onTy_append, Subst.onTy_append]
  have hF_i : ∀ (i : Nat) (hi : i < ctor.paramCount),
      (freshVars Φ ctor.paramCount)[i]? = some (Φ + i) := by
    intro i hi
    rw [List.getElem?_eq_getElem (by simpa [freshVars] using hi)]
    simp only [freshVars, List.getElem_map, List.getElem_range]
  have hWi : ∀ (i : Nat) (hi : i < ctor.paramCount),
      (freshVars W ctor.paramCount)[i]? = some (W + i) := by
    intro i hi
    rw [List.getElem?_eq_getElem (by simpa [freshVars] using hi)]
    simp only [freshVars, List.getElem_map, List.getElem_range]
  have htyArgs_belowW : ∀ t ∈ tyArgs, Ty.BelowFvars W t := by
    intro t ht; apply Ty.BelowFvars.of_freeVars_lt
    intro v hv
    exact hWfresh v (by
      simp only [List.mem_append]
      exact Or.inl (Or.inr (List.mem_flatMap.mpr ⟨t, ht, hv⟩)))
  have hA_id : ∀ {x : Ty}, Ty.BelowFvars Φ x →
      Subst.onTy ((freshVars Φ ctor.paramCount).zip
        ((freshVars W ctor.paramCount).map (Ty.fvar ·))) x = x := by
    intro x hx
    apply Ty.substFvars_eq_self_of_no_key
    intro p hp hc
    have hp1 : p.1 ∈ freshVars Φ ctor.paramCount := (List.of_mem_zip hp).1
    have hge := freshVars_ge p.1 hp1
    have hlt := hx.mem_lt p.1 hc
    omega
  have hB_fix : ∀ {t : Ty}, (∀ p ∈ R, ∀ v ∈ p.2.freeVars, v ∉ (freshVars W ctor.paramCount)) →
      (∀ v ∈ t.freeVars, v ∉ freshVars W ctor.paramCount) →
      Subst.onTy ((freshVars W ctor.paramCount).zip tyArgs) t = t := by
    intro t hR hB
    apply Ty.substFvars_eq_self_of_no_key
    intro p hp hc
    have hp1 : p.1 ∈ freshVars W ctor.paramCount := (List.of_mem_zip hp).1
    exact hB p.1 hc hp1
  have hU_fvar : ∀ v, v < Φ → U.onTy (Ty.fvar v) = R.onTy (Ty.fvar v) := by
    intro v hv
    rw [hUonTy]
    rw [hA_id (Ty.BelowFvars.fvar hv)]
    apply hB_fix
    · intro p hp w hw' hwW
      have hwge : W ≤ w := freshVars_ge w hwW
      have := hWfresh w (by
        simp only [List.mem_append]
        exact Or.inl (Or.inl (Or.inr (List.mem_flatMap.mpr ⟨p, hp, hw'⟩))))
      omega
    · intro w hw' hwW
      have hc' : w ∈ (R.onTy (Ty.fvar v)).freeVars := hw'
      rcases Subst.mem_freeVars_onTy hc' with h'' | ⟨q, hq, h''⟩
      · simp only [Ty.freeVars, List.mem_singleton] at h''
        have hvW : w < Φ := h'' ▸ hv
        have hwge : W ≤ w := freshVars_ge w hwW
        have := hWfresh w (by
          simp only [List.mem_append]
          exact Or.inr (List.mem_range.mpr hvW))
        omega
      · have hwge : W ≤ w := freshVars_ge w hwW
        have := hWfresh w (by
          simp only [List.mem_append]
          exact Or.inl (Or.inl (Or.inr (List.mem_flatMap.mpr ⟨q, hq, h''⟩))))
        omega
  have hU_index : ∀ (i : Nat) (hi : i < ctor.paramCount),
      U.onTy (Ty.fvar (Φ + i)) = tyArgs[i]'(by simpa [hpc] using hi) := by
    intro i hi
    have hi' : i < tyArgs.length := by simpa [hpc] using hi
    rw [hUonTy]
    have hfx : (freshVars Φ ctor.paramCount)[i]? = some (Φ + i) := hF_i i hi
    have hWx : (freshVars W ctor.paramCount)[i]? = some (W + i) := hWi i hi
    have hL1 : Subst.onTy ((freshVars Φ ctor.paramCount).zip
        ((freshVars W ctor.paramCount).map (Ty.fvar ·))) (Ty.fvar (Φ + i))
        = Ty.fvar (W + i) := by
      apply Ty.substFvars_zip_fvar_eq' freshVars_nodup hfx
      · rw [List.getElem?_map, hWi i hi]; rfl
      · intro X hX hc
        simp only [Ty.freeVars, List.mem_singleton] at hc
        have hlt := freshVars_lt X hX
        omega
    rw [hL1]
    have hL2 : R.onTy (Ty.fvar (W + i)) = Ty.fvar (W + i) := by
      apply Ty.substFvars_eq_self_of_no_key
      intro p hp hc
      simp only [Ty.freeVars, List.mem_singleton] at hc
      have hkey : p.1 ∈ R.map Prod.fst := List.mem_map.mpr ⟨p, hp, rfl⟩
      rw [hc] at hkey
      have := hWfresh (W + i) (by
        simp only [List.mem_append]
        exact Or.inl (Or.inl (Or.inl hkey)))
      have hge : W ≤ W + i := by omega
      omega
    rw [hL2]
    have htyx : tyArgs[i]? = some (tyArgs[i]) := by
      rw [List.getElem?_eq_getElem hi']
    apply Ty.substFvars_zip_fvar_eq' freshVars_nodup hWx htyx
    intro w hw hc
    have hwge := freshVars_ge w hw
    have hvmem : tyArgs[i] ∈ tyArgs := List.mem_of_getElem? (List.getElem?_eq_getElem hi')
    have := (htyArgs_belowW (tyArgs[i]) hvmem).mem_lt w hc
    omega
  have hmap_U : ((freshVars Φ ctor.paramCount).map (Ty.fvar ·)).map U.onTy = tyArgs := by
    apply List.ext_getElem
    · simp [hpc]
    · intro i hi _
      have hi' : i < (freshVars Φ ctor.paramCount).length := by
        simpa [freshVars_length] using hi
      have hx := hF_i i (by simpa [freshVars_length] using hi')
      have hxi : (freshVars Φ ctor.paramCount)[i] = Φ + i := by
        rw [List.getElem?_eq_getElem hi'] at hx
        exact Option.some.inj hx
      rw [List.getElem_map, List.getElem_map, hxi]
      exact hU_index i (by simpa [hpc] using hi')
  have hUni : Unifies U scrutTy
      (.customTy ctor.tyName ((freshVars Φ ctor.paramCount).map (Ty.fvar ·))) := by
    have hRHS : U.onTy (.customTy ctor.tyName
        ((freshVars Φ ctor.paramCount).map (Ty.fvar ·))) = .customTy ctor.tyName tyArgs := by
      rw [Subst.onTy_customTy, hmap_U]
    show U.onTy scrutTy = U.onTy (.customTy ctor.tyName
      ((freshVars Φ ctor.paramCount).map (Ty.fvar ·)))
    rw [hRHS]
    rw [hUonTy]
    rw [hA_id hbscrut]
    have hB : Subst.onTy ((freshVars W ctor.paramCount).zip tyArgs)
        (R.onTy scrutTy) = R.onTy scrutTy := hB_fix
      (by
        intro p hp w hw' hwW
        have hwge : W ≤ w := freshVars_ge w hwW
        have := hWfresh w (by
          simp only [List.mem_append]
          exact Or.inl (Or.inl (Or.inr (List.mem_flatMap.mpr ⟨p, hp, hw'⟩))))
        omega)
      (by
        intro w hw' hwW
        have hwge : W ≤ w := freshVars_ge w hwW
        rcases Subst.mem_freeVars_onTy hw' with h' | ⟨q, hq, h'⟩
        · have hlt := hbscrut.mem_lt w h'
          have := hWfresh w (by
            simp only [List.mem_append]
            exact Or.inr (List.mem_range.mpr hlt))
          omega
        · have := hWfresh w (by
            simp only [List.mem_append]
            exact Or.inl (Or.inl (Or.inr (List.mem_flatMap.mpr ⟨q, hq, h'⟩))))
          omega)
    rw [hB]
    exact hscrutImg.symm
  have hUlc : ∀ p ∈ U, p.2.IsLC := by
    rw [hUdef]
    intro p hp
    rcases List.mem_append.mp hp with hp' | hp'
    · rcases List.mem_append.mp hp' with hp'' | hp''
      · have hmem := (List.of_mem_zip hp'').2
        obtain ⟨x, _, hxeq⟩ := List.mem_map.mp hmem
        rw [← hxeq]; exact ContainsBvarsUpTo.fvar
      · exact hR p hp''
    · have hmem := (List.of_mem_zip hp').2
      exact htyArgs_lc p.2 hmem
  have hUK : ∀ k ∈ K, U.onTy (Ty.fvar k) = Ty.fvar k := fun k hk =>
    (hU_fvar k (hKΦ k hk)).trans (hKfix k hk)
  obtain ⟨R₀, hR₀fac, hR₀lc, hR₀K⟩ :=
    UnifyRel.greatest_K h₀ U hUlc hUni hUK
  refine ⟨R₀, hR₀lc, hR₀K, ?_, ?_⟩
  · intro v hv
    have h := hR₀fac (Ty.fvar v)
    rwa [hU_fvar v hv] at h
  · rw [List.map_map, List.map_map]
    apply List.ext_getElem?
    intro i
    by_cases hi : i < ctor.paramCount
    · have hx : (freshVars Φ ctor.paramCount)[i]? = some (Φ + i) := hF_i i hi
      rw [List.getElem?_map, hx]
      simp only [Option.map_some, Function.comp_apply]
      rw [List.getElem?_eq_getElem (by simpa [hpc] using hi)]
      have h := hR₀fac (Ty.fvar (Φ + i))
      rw [hU_index i hi] at h
      exact congrArg some h.symm
    · have hlen₁ : i ≥ (freshVars Φ ctor.paramCount).length := by
        rw [freshVars_length]; exact Nat.le_of_not_gt hi
      have hlen₂ : i ≥ tyArgs.length := by
        rw [← hpc]; exact Nat.le_of_not_gt hi
      rw [List.getElem?_eq_none (by simpa [List.length_map, freshVars_length] using hlen₁)]
      rw [List.getElem?_eq_none (by simpa [List.length_map] using hlen₂)]

/-! ### Recursion-group residual bridge

The theorems below re-instantiate the old (ffc544f / caac62d) fused `letRec`
completeness machinery directly for the current HM source relation.

`exists_recgroup_residual` is the purely-structural block residual (verbatim
port of the caac62d theorem of the same name; it no longer exists in the
current InferW.lean). The old fused residual-setup bridge
(caac62d 14150–14370) was DELETED with the superseded `InferRecGroup.Principal`
restatement (2026-08-26): the ADOPTED statement needs no declarative
`dspecs`/`Xs`/linking package — the `R₀`-transported member typings are
premises, so the bridge's construction work moved into the SPINE-GROUP cases. -/

-- [letrec-agent]

/-! ### Recursive-ceiling solver factoring

The `Sc` pass is a sequence of ordinary structural unifications. A single
witness which satisfies one such equation already absorbs the solution chosen
for it.  This is stronger than merely obtaining an arbitrary MGU residual and
is the algebra that lets the same witness thread through the whole pass.
Every equality here is `Eq`: no structural recovery is used. -/

mutual
/-- A unifier of an equation absorbs its `UnifyRel` solution. -/
theorem UnifyRel.factors_self : {a b : Ty} → {S : Subst} → UnifyRel a b S →
    ∀ U : Subst, Unifies U a b → Subst.Factors U S U
  | _, _, _, .prim, U, _ => fun t => by simp only [Subst.onTy_nil]
  | _, _, _, .fvarRefl, U, _ => fun t => by simp only [Subst.onTy_nil]
  | _, _, _, @UnifyRel.fvarL n t _ _, U, hU => by
      intro x
      simp only [Unifies, Subst.onTy] at hU ⊢
      simpa [Subst.onTy] using (Subst.onTy_substFvar hU x).symm
  | _, _, _, @UnifyRel.fvarR n t _ _, U, hU => by
      intro x
      simp only [Unifies, Subst.onTy] at hU ⊢
      simpa [Subst.onTy] using (Subst.onTy_substFvar hU.symm x).symm
  | _, _, _, @UnifyRel.arrow a b c d S₁ S₂ h₁ h₂, U, hU => by
      have hac : Unifies U a c := by
        simp only [Unifies, Subst.onTy_arrow] at hU
        exact (Ty.arrow.inj hU).1
      have hbd : Unifies U b d := by
        simp only [Unifies, Subst.onTy_arrow] at hU
        exact (Ty.arrow.inj hU).2
      have h₁U := UnifyRel.factors_self h₁ U hac
      have h₂U : Unifies U (S₁.onTy b) (S₁.onTy d) := by
        simp only [Unifies] at hbd ⊢
        exact (h₁U b).symm.trans (hbd.trans (h₁U d))
      have h₂Ufac := UnifyRel.factors_self h₂ U h₂U
      intro x
      simp only [Subst.Factors, Subst.onTy_append] at h₁U h₂Ufac ⊢
      exact (h₁U x).trans (h₂Ufac (S₁.onTy x))
  | _, _, _, @UnifyRel.customTy nm as bs S hs, U, hU => by
      have hlist : as.map U.onTy = bs.map U.onTy := by
        simp only [Unifies, Subst.onTy_customTy] at hU
        exact (Ty.customTy.inj hU).2
      exact UnifyRelList.factors_self hs U hlist

/-- List counterpart of `UnifyRel.factors_self`. -/
theorem UnifyRelList.factors_self : {as bs : List Ty} → {S : Subst} →
    UnifyRelList as bs S → ∀ U : Subst,
      as.map U.onTy = bs.map U.onTy → Subst.Factors U S U
  | _, _, _, .nil, U, _ => fun t => by simp only [Subst.onTy_nil]
  | _, _, _, @UnifyRelList.cons a b as bs S₁ S₂ h₁ h₂, U, hU => by
      simp only [List.map_cons, List.cons.injEq] at hU
      obtain ⟨hab, htail⟩ := hU
      have h₁U := UnifyRel.factors_self h₁ U hab
      have h₂U := UnifyRelList.factors_self h₂ U (by
        rw [List.map_map, List.map_map]
        calc
          as.map (fun t => U.onTy (S₁.onTy t)) = as.map U.onTy := by
                apply List.map_congr_left
                intro t _
                exact (h₁U t).symm
          _ = bs.map U.onTy := htail
          _ = bs.map (fun t => U.onTy (S₁.onTy t)) := by
                apply List.map_congr_left
                intro t _
                exact h₁U t)
      intro x
      simp only [Subst.Factors, Subst.onTy_append] at h₁U h₂U ⊢
      exact (h₁U x).trans (h₂U (S₁.onTy x))
end

/-- Pointwise erased satisfaction of a substitution's raw bindings makes the
substitution self-absorbing.  This is the projection-friendly form of the
ceiling factor invariant: after filtering out pool domains one merely keeps
the corresponding pointwise facts. -/
theorem Subst.Factors.of_satisfies {U S : Subst}
    (h : ∀ p ∈ S, U.onTy (.fvar p.1) = U.onTy p.2) :
    Subst.Factors U S U := by
  induction S with
  | nil => intro t; simp only [Subst.onTy_nil]
  | cons hd tl ih =>
      obtain ⟨z, u⟩ := hd
      have hhead : U.onTy (.fvar z) = U.onTy u :=
        h (z, u) List.mem_cons_self
      have htail : Subst.Factors U tl U := ih (fun p hp =>
        h p (List.mem_cons_of_mem _ hp))
      intro t
      have hsubst := Subst.onTy_substFvar hhead t
      simp only [Subst.Factors, Subst.onTy] at htail ⊢
      exact hsubst.symm.trans (htail (Ty.substFvar z u t))

/-- A self-absorbing residual cannot observe a ceiling substitution beneath a
    scheme whose generalisation pool that substitution avoids.  The pool is
    deliberately the one selected *before* the ceiling pass: this is the
    small algebraic fact that keeps `letRec`'s generalisation frontier frozen
    while its member monotypes are refined by `Sc`. -/
theorem Subst.Factors.genGroup_stable {U Sc : Subst} {G : List Nat} {τ : Ty}
    (hfac : Subst.Factors U Sc U)
    (hdom : ∀ p ∈ Sc, p.1 ∉ G)
    (hran : ∀ p ∈ Sc, ∀ u ∈ p.2.freeVars, u ∉ G) :
     (U.onPolyTy (PolyTy.genGroup G (Sc.onTy τ))) =
       (U.onPolyTy (PolyTy.genGroup G τ)) := by
  rw [← Subst.onPolyTy_genGroup hdom hran]
  apply congrArg₂ PolyTy.mk rfl
  exact (hfac (PolyTy.genGroup G τ).body).symm

/-! A `UnifyRel` trace supplies the raw pointwise satisfaction needed above.
Unlike final-action factorisation, this form survives `dropDomains` by plain
membership filtering. -/
mutual
theorem UnifyRel.binding_satisfies : {a b : Ty} → {S : Subst} → UnifyRel a b S →
    ∀ U : Subst, Unifies U a b →
      ∀ p ∈ S, U.onTy (.fvar p.1) = U.onTy p.2
  | _, _, _, .prim, U, hU, p, hp => by simp at hp
  | _, _, _, .fvarRefl, U, hU, p, hp => by simp at hp
  | _, _, _, @UnifyRel.fvarL n t _ _, U, hU, p, hp => by
      rw [List.mem_singleton] at hp
      subst p
      exact hU
  | _, _, _, @UnifyRel.fvarR n t _ _, U, hU, p, hp => by
      rw [List.mem_singleton] at hp
      subst p
      exact hU.symm
  | _, _, _, @UnifyRel.arrow a b c d S₁ S₂ h₁ h₂, U, hU, p, hp => by
      have hac : Unifies U a c := by
        simp only [Unifies, Subst.onTy_arrow] at hU
        exact (Ty.arrow.inj hU).1
      have hbd : Unifies U b d := by
        simp only [Unifies, Subst.onTy_arrow] at hU
        exact (Ty.arrow.inj hU).2
      have h₁fac := UnifyRel.factors_self h₁ U hac
      have h₂uni : Unifies U (S₁.onTy b) (S₁.onTy d) := by
        simp only [Unifies] at hbd ⊢
        exact (h₁fac b).symm.trans (hbd.trans (h₁fac d))
      rw [List.mem_append] at hp
      exact hp.elim
        (fun hp => UnifyRel.binding_satisfies h₁ U hac p hp)
        (fun hp => UnifyRel.binding_satisfies h₂ U h₂uni p hp)
  | _, _, _, @UnifyRel.customTy nm as bs S hs, U, hU, p, hp => by
      have hlist : as.map U.onTy = bs.map U.onTy := by
        simp only [Unifies, Subst.onTy_customTy] at hU
        exact (Ty.customTy.inj hU).2
      exact UnifyRelList.binding_satisfies hs U hlist p hp

theorem UnifyRelList.binding_satisfies : {as bs : List Ty} → {S : Subst} →
    UnifyRelList as bs S → ∀ U : Subst,
      as.map U.onTy = bs.map U.onTy →
      ∀ p ∈ S, U.onTy (.fvar p.1) = U.onTy p.2
  | _, _, _, .nil, U, hU, p, hp => by simp at hp
  | _, _, _, @UnifyRelList.cons a b as bs S₁ S₂ h₁ h₂, U, hU, p, hp => by
      simp only [List.map_cons, List.cons.injEq] at hU
      obtain ⟨hab, htail⟩ := hU
      have h₁fac := UnifyRel.factors_self h₁ U hab
      have htail' :
          (as.map S₁.onTy).map U.onTy = (bs.map S₁.onTy).map U.onTy := by
        rw [List.map_map, List.map_map]
        calc
          as.map (fun t => U.onTy (S₁.onTy t)) = as.map U.onTy := by
                apply List.map_congr_left
                intro t _
                exact (h₁fac t).symm
          _ = bs.map U.onTy := htail
          _ = bs.map (fun t => U.onTy (S₁.onTy t)) := by
                apply List.map_congr_left
                intro t _
                exact h₁fac t
      rw [List.mem_append] at hp
      exact hp.elim
        (fun hp => UnifyRel.binding_satisfies h₁ U hab p hp)
        (fun hp => UnifyRelList.binding_satisfies h₂ U htail' p hp)
end

/-- Projection of a genuine unification trace stays self-factored by every
witness that unifies the original equation. -/
theorem UnifyRel.factors_self_dropDomains {a b : Ty} {S U : Subst}
    (h : UnifyRel a b S) (hU : Unifies U a b) (G : List Nat) :
    Subst.Factors U (S.dropDomains G) U :=
  Subst.Factors.of_satisfies (fun p hp =>
    UnifyRel.binding_satisfies h U hU p (Subst.mem_dropDomains.mp hp).1)

/-- A finite proxy isolates the variables which a scheme closes before an
    ambient residual is run.  This is the witness needed for a ceiling check:
    it behaves exactly as `R` on every unprotected source variable, but routes
    the protected variables through a fresh opening and then the chosen scheme
    instantiation.  The statement is deliberately structural; callers may
    erase it when using `UnifyRel.binding_satisfies`. -/
private theorem Subst.exists_proxy_unifier
    {g keep : List Nat} {τ target : Ty} {R : Subst} {args : List Ty}
    (hg : g.Nodup) (hτ : τ.IsLC) (hR : ∀ p ∈ R, p.2.IsLC)
    (hargs : ∀ t ∈ args, t.IsLC)
    (hinst : InstantiatesBy args (R.onTy (Ty.closeOver g τ)) target)
    (hgtarget : ∀ z ∈ g, z ∉ target.freeVars)
    (hRtarget : ∀ z ∈ target.freeVars, R.onTy (.fvar z) = .fvar z) :
    ∃ U : Subst, Unifies U τ target ∧
      (∀ p ∈ U, p.2.IsLC) ∧
      (∀ z ∈ target.freeVars, U.onTy (.fvar z) = .fvar z) ∧
      (∀ z ∈ τ.freeVars, z ∉ g → U.onTy (.fvar z) = R.onTy (.fvar z)) ∧
      (∀ z ∈ keep, z ∉ g → U.onTy (.fvar z) = R.onTy (.fvar z)) := by
  obtain ⟨Ws, hWlen, hWnd, hWavoid⟩ := exists_fresh_names
    (g ++ (keep ++ (τ.freeVars ++ (R.map Prod.fst ++
      (R.flatMap (fun p => p.2.freeVars) ++ target.freeVars)))))
    g.length
  let proxy : Subst := g.zip (Ws.map (Ty.fvar ·))
  let breal : Subst := Ws.zip args
  let U : Subst := proxy ++ R ++ breal
  have hWg : ∀ w ∈ Ws, w ∉ g := fun w hw hwg =>
    hWavoid w hw (by simp [hwg])
  have hWτ : ∀ w ∈ Ws, w ∉ τ.freeVars := fun w hw hwτ =>
    hWavoid w hw (by simp only [List.mem_append]; tauto)
  have hWkeep : ∀ w ∈ Ws, w ∉ keep := fun w hw hkeep =>
    hWavoid w hw (by simp only [List.mem_append]; tauto)
  have hWRdom : ∀ p ∈ R, p.1 ∉ Ws := fun p hp hmem =>
    hWavoid p.1 hmem (by
      have hdom : p.1 ∈ R.map Prod.fst := List.mem_map.mpr ⟨p, hp, rfl⟩
      simp only [List.mem_append]; tauto)
  have hWRran : ∀ p ∈ R, ∀ w ∈ p.2.freeVars, w ∉ Ws := fun p hp w hw hmem =>
    hWavoid w hmem (by
      have hran : w ∈ R.flatMap (fun p => p.2.freeVars) := List.mem_flatMap.mpr ⟨p, hp, hw⟩
      simp only [List.mem_append]; tauto)
  have hWtarget : ∀ w ∈ Ws, w ∉ target.freeVars := fun w hw hmem =>
    hWavoid w hw (by simp only [List.mem_append]; tauto)
  have hproxy : proxy.onTy τ = Ty.openVars Ws (Ty.closeOver g τ) := by
    rw [Ty.openVars_closeOver_rename hτ hg hWlen (fun z hz zw => hWg z zw hz)]
    rfl
  have hRcomm : R.onTy (Ty.openVars Ws (Ty.closeOver g τ)) =
      Ty.openVars Ws (R.onTy (Ty.closeOver g τ)) :=
    Subst.onTy_openVars hR hWRdom
  have hbv0 : ContainsBvarsUpTo g.length (Ty.closeOver g τ) := by
    exact Ty.closeOver_preserves_bvars hτ
  have hbv : ContainsBvarsUpTo Ws.length (R.onTy (Ty.closeOver g τ)) := by
    rw [hWlen]
    exact ContainsBvarsUpTo.substFvars hR hbv0
  have hreal : breal.onTy (Ty.openVars Ws (R.onTy (Ty.closeOver g τ))) = target := by
    simpa [breal] using InstantiatesBy.onTy_openVars_zip hinst hbv hWnd hWtarget
  refine ⟨U, ?_, ?_, ?_, ?_, ?_⟩
  · change (proxy ++ R ++ breal).onTy τ = (proxy ++ R ++ breal).onTy target
    simp only [Subst.onTy_append]
    rw [hproxy, hRcomm, hreal]
    change target = breal.onTy (R.onTy (proxy.onTy target))
    apply Eq.symm
    calc
      breal.onTy (R.onTy (proxy.onTy target)) = breal.onTy (R.onTy target) := by
        congr 2
        apply Ty.substFvars_eq_self_of_no_key
        intro p hp hz
        change p ∈ g.zip (Ws.map (Ty.fvar ·)) at hp
        exact hgtarget p.1 (List.of_mem_zip hp).1 (by simpa [Ty.freeVars] using hz)
      _ = breal.onTy target := by
        rw [Subst.onTy_eq_self_of_fixes hRtarget]
      _ = target := by
        apply Ty.substFvars_eq_self_of_no_key
        intro p hp hz
        change p ∈ Ws.zip args at hp
        exact hWtarget p.1 (List.of_mem_zip hp).1 (by simpa [Ty.freeVars] using hz)
  · intro p hp
    change p ∈ proxy ++ R ++ breal at hp
    rcases List.mem_append.mp hp with hp | hp
    · rcases List.mem_append.mp hp with hp | hp
      · have ht : p.2 ∈ Ws.map (Ty.fvar ·) := (List.of_mem_zip hp).2
        obtain ⟨w, hw, hwp⟩ := List.mem_map.mp ht
        rw [← hwp]
        exact ContainsBvarsUpTo.fvar
      · exact hR p hp
    · have ht : p.2 ∈ args := (List.of_mem_zip hp).2
      exact hargs p.2 ht
  · intro z hz
    change (proxy ++ R ++ breal).onTy (.fvar z) = .fvar z
    rw [Subst.onTy_append, Subst.onTy_append]
    have hproxyfix : proxy.onTy (.fvar z) = .fvar z := by
      apply Ty.substFvars_eq_self_of_no_key
      intro p hp hz'
      change p ∈ g.zip (Ws.map (Ty.fvar ·)) at hp
      have hpz : p.1 = z := by simpa [Ty.freeVars] using hz'
      exact hgtarget p.1 (List.of_mem_zip hp).1 (hpz.symm ▸ hz)
    rw [hproxyfix, hRtarget z hz]
    apply Ty.substFvars_eq_self_of_no_key
    intro p hp hz'
    change p ∈ Ws.zip args at hp
    have hpz : p.1 = z := by simpa [Ty.freeVars] using hz'
    exact hWtarget p.1 (List.of_mem_zip hp).1 (hpz.symm ▸ hz)
  · intro z hzτ hzg
    change (proxy ++ R ++ breal).onTy (.fvar z) = R.onTy (.fvar z)
    rw [Subst.onTy_append, Subst.onTy_append]
    have hproxyfix : proxy.onTy (.fvar z) = .fvar z := by
      apply Ty.substFvars_eq_self_of_no_key
      intro p hp hz
      change p ∈ g.zip (Ws.map (Ty.fvar ·)) at hp
      apply hzg
      have hpg : p.1 ∈ g := (List.of_mem_zip hp).1
      have hpz : p.1 = z := by simpa [Ty.freeVars] using hz
      exact hpz ▸ hpg
    rw [hproxyfix]
    apply Ty.substFvars_eq_self_of_no_key
    intro p hp hz
    change p ∈ Ws.zip args at hp
    have hpW : p.1 ∈ Ws := (List.of_mem_zip hp).1
    have hpNot : p.1 ∉ (Ty.fvar z).freeVars := by
      simp only [Ty.freeVars, List.mem_singleton]
      intro hpz
      rw [hpz] at hpW
      exact hWτ z hpW hzτ
    exact (Subst.not_mem_onTy_freeVars
      (fun q hq hqv => hWRran q hq p.1 hqv hpW) hpNot) hz
  · intro z hzkeep hzg
    change (proxy ++ R ++ breal).onTy (.fvar z) = R.onTy (.fvar z)
    rw [Subst.onTy_append, Subst.onTy_append]
    have hproxyfix : proxy.onTy (.fvar z) = .fvar z := by
      apply Ty.substFvars_eq_self_of_no_key
      intro p hp hz
      change p ∈ g.zip (Ws.map (Ty.fvar ·)) at hp
      apply hzg
      have hpg : p.1 ∈ g := (List.of_mem_zip hp).1
      have hpz : p.1 = z := by simpa [Ty.freeVars] using hz
      exact hpz ▸ hpg
    rw [hproxyfix]
    apply Ty.substFvars_eq_self_of_no_key
    intro p hp hz
    change p ∈ Ws.zip args at hp
    have hpW : p.1 ∈ Ws := (List.of_mem_zip hp).1
    have hpNot : p.1 ∉ (Ty.fvar z).freeVars := by
      simp only [Ty.freeVars, List.mem_singleton]
      intro hpz
      rw [hpz] at hpW
      exact hWkeep z hpW hzkeep
    exact (Subst.not_mem_onTy_freeVars
      (fun q hq hqv => hWRran q hq p.1 hqv hpW) hpNot) hz

/-- Thread a common residual witness through the sequential ceiling pass.

    The premise deliberately speaks only about the **committed** bindings of a
    head step.  A full annotation check may instantiate the frozen group pool
    differently at each head; those pool-domain bindings are projected away by
    `dropDomains G` and therefore must not be forced to share one unifier.
    What remains is exactly the pointwise statement needed for `Subst.Factors`.

    The let-rec completeness case supplies this premise from its declarative
    member connection.  Keeping this algebraic threading lemma separate makes
    that source-specific argument explicit, and prevents an accidental return
    to a structural factorisation argument. -/
theorem RecCeilingConstraints.factors_of_step_satisfies
    {K rigid G : List Nat} {Φ : Nat} {anns : List (Option PolyTy)}
    {specs : List RecSpec} {Sc Rg : Subst}
    (hSc : RecCeilingConstraints K rigid G Φ anns specs Sc)
    (hstep : ∀ {τ : Ty} {σ : PolyTy} {full step : Subst},
      UnifyRel ( τ)
          ( (σ.openVars (freshVars Φ σ.paramCount))) full →
      step = Subst.dropDomains G full →
      ∀ p ∈ step, Eq (Rg.onTy (.fvar p.1)) (Rg.onTy p.2)) :
    Subst.Factors Rg Sc Rg := by
  apply Subst.Factors.of_satisfies
  induction anns generalizing specs Sc with
  | nil =>
      cases specs <;> simp [RecCeilingConstraints] at hSc
      subst Sc
      simp
  | cons ann anns ih =>
      cases ann with
      | none =>
          cases specs with
          | nil => simp [RecCeilingConstraints] at hSc
          | cons spec specs =>
              intro p hp
              exact ih hSc p hp
      | some σ =>
          cases specs with
          | nil => simp [RecCeilingConstraints] at hSc
          | cons spec specs =>
              cases spec with
              | poly σ' => simp [RecCeilingConstraints] at hSc
              | mono τ =>
                  rcases hSc with ⟨full, step, tail, hfull, _havoid, hdef,
                    _hrange, _hlc, _hwf, _hrigid, htail, rfl⟩
                  intro p hp
                  rcases List.mem_append.mp hp with hp | hp
                  · exact hstep hfull hdef p hp
                  · exact ih htail p hp

/-- Reflect membership through a map on the right side of a zip. -/
private theorem List.mem_zip_map_right {alpha beta gamma : Type _} {g : beta → gamma}
    : ∀ {l : List alpha} {r : List beta} {p : alpha × gamma},
      p ∈ l.zip (r.map g) → ∃ a b, (a, b) ∈ l.zip r ∧ p = (a, g b) := by
  intro l
  induction l with
  | nil => intro r p h; simp at h
  | cons hd tl ih =>
      intro r p h
      cases r with
      | nil => simp at h
      | cons rhd rtl =>
          simp only [List.map_cons, List.zip_cons_cons, List.mem_cons] at h
          cases h with
          | inl heq => exact ⟨hd, rhd, List.mem_cons_self, heq⟩
          | inr h' =>
              obtain ⟨a, b, hmem, heq⟩ := ih h'
              exact ⟨a, b, List.mem_cons_of_mem _ hmem, heq⟩

/-- Positional scheme evidence used by the reverse (principality) direction of
    the recursive ceiling pass.  Only annotated monomorphic entries carry an
    obligation; the impossible annotated-poly case is recorded explicitly. -/
private def CeilingGenInv (G : List Nat) (R : Subst)
    (anns : List (Option PolyTy)) (specs : List RecSpec) : Prop :=
  ∀ {ann spec}, (ann, spec) ∈ anns.zip specs →
    match ann, spec with
    | some σ, .mono τ =>
        ( (R.onPolyTy (PolyTy.genGroup G τ))).Generalizes
          ( σ)
    | some _, .poly _ => False
    | none, _ => True

/-- A sequential ceiling is absorbed once each annotated head is absorbed from
    its scheme-generality witness.  The invariant is transported through a
    committed head using `genGroup_stable`, so each annotation remains free to
    choose its own discarded instantiation of the frozen pool. -/
private theorem RecCeilingConstraints.factors_of_generalizes
    {K rigid G : List Nat} {Phi : Nat} {anns : List (Option PolyTy)}
    {specs : List RecSpec} {Sc R : Subst}
    (hSc : RecCeilingConstraints K rigid G Phi anns specs Sc)
    (hgen : CeilingGenInv G R anns specs)
    (hspecLC : ∀ s ∈ specs, s.LC)
    (hspecBelow : ∀ s ∈ specs, s.BelowFvars Phi)
    (hrigidBelow : ∀ x ∈ rigid, x < Phi)
    (hhead : ∀ {τ : Ty} {σ : PolyTy} {full step : Subst},
      UnifyRel ( τ)
          ( (σ.openVars (freshVars Phi σ.paramCount))) full →
      (∀ p ∈ full, p.1 ∉ K ++ rigid ++ freshVars Phi σ.paramCount) →
      step = Subst.dropDomains G full →
      (∀ p ∈ step, ∀ x ∈ p.2.freeVars, x ∈ rigid ∧ x ∉ G) →
      (∀ p ∈ step, p.2.IsLC) →
      σ.WF →
      (∀ x ∈ σ.body.freeVars, x ∈ rigid) →
      τ.IsLC →
      τ.BelowFvars Phi →
      ( (R.onPolyTy (PolyTy.genGroup G τ))).Generalizes
        ( σ) →
      Subst.Factors R step R) :
    Subst.Factors R Sc R := by
  induction anns generalizing specs Sc with
  | nil =>
      cases specs <;> simp [RecCeilingConstraints] at hSc
      subst Sc
      intro t
      exact Eq.refl _
  | cons ann anns ih =>
      cases ann with
      | none =>
          cases specs with
          | nil => simp [RecCeilingConstraints] at hSc
          | cons spec specs =>
              apply ih hSc
              · intro a s hp
                exact hgen (by
                  rw [List.zip_cons_cons]
                  exact List.mem_cons_of_mem _ hp)
              · intro s hs
                exact hspecLC s (List.mem_cons_of_mem _ hs)
              · intro s hs
                exact hspecBelow s (List.mem_cons_of_mem _ hs)
      | some σ =>
          cases specs with
          | nil => simp [RecCeilingConstraints] at hSc
          | cons spec specs =>
              cases spec with
              | poly σ' => simp [RecCeilingConstraints] at hSc
              | mono τ =>
                  rcases hSc with ⟨full, step, tail, hfull, havoid, hdef,
                    hrange, hstepLC, hσwf, hσrigid, htail, rfl⟩
                  have hgenHead :
                      ( (R.onPolyTy (PolyTy.genGroup G τ))).Generalizes
                        ( σ) :=
                    hgen (by rw [List.zip_cons_cons]; exact List.mem_cons_self)
                  have hfacHead : Subst.Factors R step R :=
                    hhead hfull havoid hdef hrange hstepLC hσwf hσrigid
                      (hspecLC (.mono τ) List.mem_cons_self)
                      (hspecBelow (.mono τ) List.mem_cons_self) hgenHead
                  have hdom : ∀ p ∈ step, p.1 ∉ G := by
                    intro p hp
                    rw [hdef] at hp
                    exact (Subst.mem_dropDomains.mp hp).2
                  have hgenTail : CeilingGenInv G R anns
                      (specs.map (RecSpec.onSubst step)) := by
                    intro a s hs
                    rcases List.mem_zip_map_right hs with ⟨a0, s0, hs0, heq⟩
                    injection heq with ha hs'
                    cases ha
                    cases hs'
                    have hold := hgen (by
                      rw [List.zip_cons_cons]
                      exact List.mem_cons_of_mem _ hs0)
                    cases a with
                    | none => trivial
                    | some σ0 =>
                        cases s0 with
                        | poly σ1 => exact False.elim hold
                        | mono τ0 =>
                            have hstable := Subst.Factors.genGroup_stable
                              (U := R) (Sc := step) (G := G) (τ := τ0)
                              hfacHead hdom (fun p hp x hx => (hrange p hp x hx).2)
                            change
                              (
                                (R.onPolyTy (PolyTy.genGroup G (step.onTy τ0)))).Generalizes
                                ( σ0)
                            rw [hstable]
                            exact hold
                  have hstepBelow : ∀ p ∈ step, p.2.BelowFvars Phi := by
                    intro p hp
                    exact Ty.BelowFvars.of_freeVars_lt (fun x hx =>
                      hrigidBelow x (hrange p hp x hx).1)
                  have hfacTail : Subst.Factors R tail R := ih htail hgenTail
                    (fun s hs => by
                      obtain ⟨s0, hs0, rfl⟩ := List.mem_map.mp hs
                      exact RecSpec.LC.onSubst hstepLC
                        (hspecLC s0 (List.mem_cons_of_mem _ hs0)))
                    (fun s hs => by
                      obtain ⟨s0, hs0, rfl⟩ := List.mem_map.mp hs
                      exact RecSpec.BelowFvars.onSubst hstepBelow
                        (hspecBelow s0 (List.mem_cons_of_mem _ hs0)))
                  intro t
                  simpa [Subst.onTy_append] using
                    Eq.trans (hfacHead t) (hfacTail (step.onTy t))

/-- Free vars of a single type are contained in the free vars of any list
    containing it (`Ty.freeVarsList` flavour; the public twin of Core's private
    `Ty.freeVars_subset_freeVarsList`, needed by `exists_recgroup_residual`). -/
private theorem Ty.mem_freeVarsList_of_mem {t : Ty} {tys : List Ty} {x : Nat}
    (ht : t ∈ tys) (hx : x ∈ t.freeVars) : x ∈ Ty.freeVarsList tys := by
  induction tys with
  | nil => exact absurd ht List.not_mem_nil
  | cons hd tl ih =>
    simp only [Ty.freeVarsList, List.mem_dedup, List.mem_append]
    cases ht with
    | head _ => exact .inl hx
    | tail _ ht' => exact .inr (ih ht')

/-- A scheme generalising its body-type's closed-over form generalises any scheme
    whose body is an opening of that closed form (erase world port of caac62d's
    `genGroup_generalizes`; used by the COMPLETE-LETREC body lift). -/
private theorem genGroup_generalizes {Ginf : List Nat} {τ₁ : Ty} {R : Subst} {M : PolyTy}
    {Xs : List Nat}
    (hτ₁ : τ₁.IsLC) (hR : ∀ p ∈ R, p.2.IsLC) (hMwf : M.WF)
    (hXnodup : Xs.Nodup) (hXlen : Xs.length = M.paramCount)
    (hXMbody : ∀ x ∈ Xs, x ∉ M.body.freeVars)
    (htyr : Ty.openVars Xs M.body = R.onTy τ₁)
    (hXM'' : ∀ x ∈ Xs, x ∉ (R.onPolyTy (PolyTy.genGroup Ginf τ₁)).body.freeVars) :
    (R.onPolyTy (PolyTy.genGroup Ginf τ₁)).Generalizes M :=
  closeOver_generalizes (g := Ty.genFilter Ginf τ₁) hτ₁ hR hMwf hXnodup hXlen hXMbody htyr hXM''

/-- The `renameG`-flavoured group generalisation (verbatim port of caac62d): the
    inferred per-binding scheme `R.onPolyTy (genGroup Ginf τinf)` is at least as
    general as the declarative `genGroup G τdecl`, given the connection
    `R.onTy τinf = renameG G Xsfull τdecl` on a fresh shared opening `Xsfull` of
    the declarative pool `G`. -/
private theorem genGroup_generalizes_renameG {Ginf G Xsfull : List Nat} {τinf τdecl : Ty} {R : Subst}
    (hτinf : τinf.IsLC) (hτdecl : τdecl.IsLC) (hR : ∀ p ∈ R, p.2.IsLC)
    (hG : G.Nodup) (hXlen : Xsfull.length = G.length) (hXnodup : Xsfull.Nodup)
    (hXG : ∀ g ∈ G, g ∉ Xsfull) (hXτ : ∀ x ∈ Xsfull, x ∉ τdecl.freeVars)
    (hconn : R.onTy τinf = Ty.renameG G Xsfull τdecl)
    (hXinf : ∀ x ∈ Xsfull, x ∉ (R.onPolyTy (PolyTy.genGroup Ginf τinf)).body.freeVars) :
    (R.onPolyTy (PolyTy.genGroup Ginf τinf)).Generalizes (PolyTy.genGroup G τdecl) := by
  set Xs := Ty.genFilter Xsfull (Ty.renameG G Xsfull τdecl) with hXsdef
  have hgg : PolyTy.genGroup G τdecl = PolyTy.genGroup Xsfull (Ty.renameG G Xsfull τdecl) :=
    PolyTy.genGroup_renameG hτdecl hXlen hG hXnodup hXG hXτ
  have hXlen_filter : Xs.length = (Ty.genFilter G τdecl).length := by
    have h := congrArg PolyTy.paramCount hgg
    simp only [PolyTy.genGroup] at h
    rw [hXsdef]; exact h.symm
  have hXnodup' : Xs.Nodup := by rw [hXsdef]; unfold Ty.genFilter; exact hXnodup.filter _
  have hXsub : ∀ x ∈ Xs, x ∈ Xsfull := by
    rw [hXsdef]; intro x hx; exact Ty.mem_of_mem_genFilter hx
  have hGFnodup : (Ty.genFilter G τdecl).Nodup := by unfold Ty.genFilter; exact hG.filter _
  have hGFdisj : ∀ g ∈ Ty.genFilter G τdecl, g ∉ Xs :=
    fun g hg hc => hXG g (Ty.mem_of_mem_genFilter hg) (hXsub g hc)
  refine genGroup_generalizes (Ginf := Ginf) (τ₁ := τinf) (M := PolyTy.genGroup G τdecl) (Xs := Xs)
    hτinf hR (PolyTy.genGroup_wf hτdecl) hXnodup'
    (by rw [hXlen_filter]; rfl) ?_ ?_ ?_
  · -- Xs avoids the declarative scheme body's free vars (⊆ τdecl's)
    intro x hx hc
    exact hXτ x (hXsub x hx) (Ty.freeVars_closeOver_subset hc)
  · -- htyr : openVars Xs (genGroup G τdecl).body = R.onTy τinf
    show Ty.openVars Xs (Ty.closeOver (Ty.genFilter G τdecl) τdecl) = R.onTy τinf
    rw [Ty.openVars_closeOver_rename hτdecl hGFnodup hXlen_filter hGFdisj, hconn]
    exact (Ty.renameG_eq_genFilter hXlen hG hXnodup hXG hXτ).symm
  · intro x hx; exact hXinf x (hXsub x hx)

/-- A member type's free var in the group solved monotypes is in the pool's free
    var list (erased world helper). -/
private theorem mem_freeVarsList_monoTys {specs : List RecSpec} {τ : Ty}
    (hτ : τ ∈ RecSpecs.monoTys specs) (h : v ∈ τ.freeVars) :
    v ∈ Ty.freeVarsList (RecSpecs.monoTys specs) := by
  exact Ty.mem_freeVarsList_of_mem hτ h

/-- A solved mono member sits in the group's monotype pool. -/
private theorem mem_monoTys_of_mem_solved {specs : List RecSpec} {τ : Ty}
    (h : RecSpec.mono τ ∈ specs) : τ ∈ RecSpecs.monoTys specs := by
  unfold RecSpecs.monoTys
  simp only [RecSpec.monoTy?, List.mem_filterMap]
  exact ⟨RecSpec.mono τ, h, rfl⟩

/-- Forall₂ built from getElem. -/
private theorem forall₂_of_getElem {α β : Type*} {R : α → β → Prop}
    {l₁ : List α} {l₂ : List β} (hlen : l₁.length = l₂.length)
    (h : ∀ i (h₁ : i < l₁.length) (h₂ : i < l₂.length), R l₁[i] l₂[i]) :
    List.Forall₂ R l₁ l₂ := by
  induction l₁ generalizing l₂ with
  | nil => cases l₂ with | nil => exact .nil | cons => simp at hlen
  | cons a as ih =>
    cases l₂ with
    | nil => simp at hlen
    | cons b bs =>
      refine .cons (h 0 (by simp) (by simp)) (ih (by simpa using hlen) ?_)
      intro i h₁ h₂
      exact h (i + 1) (by simpa using h₁) (by simpa using h₂)

/-- `RecGroup.tyFreeVars` and `flatMap Expr.tyFreeVars` have the same members
    (local copy of InferW's private lemma; used by COMPLETE-LETREC's `hKrigid`). -/
private theorem mem_recGroup_tyFreeVars {bindings : List Expr} {y : Nat} :
    y ∈ Expr.tyFreeVars.RecGroup.tyFreeVars bindings ↔ y ∈ bindings.flatMap Expr.tyFreeVars := by
  induction bindings with
  | nil => simp [Expr.tyFreeVars.RecGroup.tyFreeVars]
  | cons hd tl ih =>
    simp only [Expr.tyFreeVars.RecGroup.tyFreeVars, List.flatMap_cons, List.mem_append, ih]

/-- The zip pair at position `i` is a member of the zip. -/
private theorem getElem_mem_zip {α β : Type _} {as : List α} {bs : List β}
    (i : Nat) (hi : i < as.length) (hi' : i < bs.length) :
    (as[i]'hi, bs[i]'hi') ∈ as.zip bs := by
  rw [List.mem_iff_getElem]
  refine ⟨i, ?_, ?_⟩
  · rw [List.length_zip]
    omega
  · rw [List.getElem_zip]

/-- Pointwise erased agreement on a type's actual free variables is enough to
    transport that type.  This is the finite-support counterpart of
    `Subst.onTy_congr`, used below because a ceiling step only promises
    agreement on its rigid range, not on an entire numerical frontier. -/
private theorem Subst.onTy_congr_of_freeVars {S T : Subst} {t : Ty}
    (h : ∀ v ∈ t.freeVars,
      Eq (S.onTy (.fvar v)) (T.onTy (.fvar v))) :
    Eq (S.onTy t) (T.onTy t) := by
  induction t using Ty.rec_strong with
  | prim p => simp only [Subst.onTy_prim]
  | bvar i => simp only [Subst.onTy_bvar]
  | fvar n => exact h n (by simp [Ty.freeVars])
  | arrow a b iha ihb =>
    simp only [Subst.onTy_arrow, Ty.arrow.injEq]
    exact ⟨iha (fun v hv => h v (by
      simp only [Ty.freeVars, List.mem_dedup, List.mem_append]
      exact Or.inl hv)),
      ihb (fun v hv => h v (by
        simp only [Ty.freeVars, List.mem_dedup, List.mem_append]
        exact Or.inr hv))⟩
  | customTy nm tys ih =>
    simp only [Subst.onTy_customTy, Ty.customTy.injEq, true_and]
    apply List.map_congr_left
    intro u hu
    exact ih u hu (fun v hv => h v (TyList.mem_freeVars_of_mem hu hv))

/-- The fresh-skolem sandwich used by both ceiling principality and producer
    completeness.  It turns a declarative generality witness into a genuine
    erased unifier while keeping a chosen protected set `P`, the annotation's
    rigid names, and the whole opening block fixed.  `P` is deliberately
    independent of `G`: relational completeness uses `K \\ G`, whereas an
    executable caller may use its stronger lexical disjointness invariant. -/
private theorem RecCeilingConstraints.exists_skolem_safe_unifier
    {P rigid G : List Nat} {Φ : Nat} {τ : Ty} {σ : PolyTy} {R : Subst}
    (hG : G.Nodup)
    (hrigidG : ∀ x ∈ rigid, x ∉ G)
    (hPG : ∀ x ∈ P, x ∉ G)
    (hRlc : ∀ p ∈ R, p.2.IsLC)
    (hRP : ∀ x ∈ P, R.onTy (.fvar x) = .fvar x)
    (hRrigid : ∀ x ∈ rigid, R.onTy (.fvar x) = .fvar x)
    (hτlc : τ.IsLC) (hτbelow : τ.BelowFvars Φ)
    (hPbelow : ∀ x ∈ P, x < Φ)
    (hrigidbelow : ∀ x ∈ rigid, x < Φ)
    (hσwf : σ.WF)
    (hσrigid : ∀ x ∈ σ.body.freeVars, x ∈ rigid)
    (hgen : ( (R.onPolyTy (PolyTy.genGroup G τ))).Generalizes
      ( σ)) :
    ∃ U : Subst,
      (∀ p ∈ U, p.2.IsLC) ∧
      Unifies U ( τ)
        ( (σ.openVars (freshVars Φ σ.paramCount))) ∧
      (∀ x ∈ P ++ rigid ++ freshVars Φ σ.paramCount,
        U.onTy (.fvar x) = .fvar x) ∧
      (∀ z ∈ ( τ).freeVars, z ∉ G →
        U.onTy (.fvar z) =
          Subst.onTy (R)
            (.fvar z)) := by
  let τe : Ty :=  τ
  let σe : PolyTy :=  σ
  let Ys : List Nat := freshVars Φ σ.paramCount
  let Rer : Subst := R
  let g : List Nat := Ty.genFilter G τe
  have hτelc : τe.IsLC := hτlc
  have hτebelow : τe.BelowFvars Φ :=
    Ty.BelowFvars.of_freeVars_lt (fun v hv =>
      hτbelow.mem_lt v ((by simpa [τe] using hv)))
  have hσebodybelow : σe.body.BelowFvars Φ :=
    Ty.BelowFvars.of_freeVars_lt (fun v hv =>
      hrigidbelow v (hσrigid v
        ((by simpa [σe] using hv))))
  have hgnodup : g.Nodup := by
    rw [show g = Ty.genFilter G τe from rfl]
    unfold Ty.genFilter
    exact hG.filter _
  have hgsub : ∀ x ∈ g, x ∈ G := fun x hx => Ty.mem_of_mem_genFilter hx
  have hRerlc : ∀ p ∈ Rer, p.2.IsLC := by
    simpa [Rer] using hRlc
  have hRer_fvar : ∀ z : Nat,
      Rer.onTy (.fvar z) =  (R.onTy (.fvar z)) := by
    intro z
    rfl
  have hRerP : ∀ x ∈ P, Rer.onTy (.fvar x) = .fvar x := by
    intro x hx
    rw [hRer_fvar x, hRP x hx]
  have hRerrigid : ∀ x ∈ rigid, Rer.onTy (.fvar x) = .fvar x := by
    intro x hx
    rw [hRer_fvar x, hRrigid x hx]
  obtain ⟨W, hWge, hWfresh⟩ := exists_fresh_block
    (R.map Prod.fst ++ R.flatMap (fun p => p.2.freeVars) ++ P ++ G ++ rigid)
    Φ σ.paramCount
  let Ws : List Nat := freshVars W σ.paramCount
  let block : Subst := blockList Φ W σ.paramCount
  let back : Subst := blockListBack Φ W σ.paramCount
  let targetY : Ty := σe.openVars Ys
  let targetW : Ty := σe.openVars Ws
  have hW_Rdom : ∀ p ∈ R, p.1 < W := by
    intro p hp
    have hmem : p.1 ∈ R.map Prod.fst := List.mem_map.mpr ⟨p, hp, rfl⟩
    exact hWfresh p.1 (by
      simp only [List.mem_append]
      tauto)
  have hW_Rrange : ∀ p ∈ R, ∀ v ∈ p.2.freeVars, v < W := by
    intro p hp v hv
    have hmem : v ∈ R.flatMap (fun p => p.2.freeVars) :=
      List.mem_flatMap.mpr ⟨p, hp, hv⟩
    exact hWfresh v (by
      simp only [List.mem_append]
      tauto)
  have hW_P : ∀ x ∈ P, x < W := by
    intro x hx
    exact hWfresh x (by
      simp only [List.mem_append]
      tauto)
  have hW_G : ∀ x ∈ G, x < W := by
    intro x hx
    exact hWfresh x (by
      simp only [List.mem_append]
      tauto)
  have hW_rigid : ∀ x ∈ rigid, x < W := by
    intro x hx
    exact hWfresh x (by simp only [List.mem_append]; exact Or.inr hx)
  have hWs_ge : ∀ w ∈ Ws, W ≤ w := fun w hw =>
    freshVars_ge w (by simpa [Ws] using hw)
  have hRerWfix : ∀ w ∈ Ws, Rer.onTy (.fvar w) = .fvar w := by
    intro w hw
    apply Ty.substFvars_eq_self_of_no_key
    intro p hp hc
    simp only [Ty.freeVars, List.mem_singleton] at hc
    have hlt := hW_Rdom p hp
    have hge := hWs_ge w hw
    omega
  have hRertargetW : ∀ v ∈ targetW.freeVars,
      Rer.onTy (.fvar v) = .fvar v := by
    intro v hv
    rcases Ty.freeVars_openVars_subset v (by simpa [targetW] using hv) with hv | hv
    · exact hRerrigid v (hσrigid v
        ((by simpa [σe] using hv)))
    · exact hRerWfix v (by simpa [targetW] using hv)
  have hgtargetW : ∀ z ∈ g, z ∉ targetW.freeVars := by
    intro z hzg hzt
    rcases Ty.freeVars_openVars_subset z (by simpa [targetW] using hzt) with hz | hz
    · exact hrigidG z (hσrigid z
        ((by simpa [σe] using hz))) (hgsub z hzg)
    · have hzglt := hW_G z (hgsub z hzg)
      have hzge := hWs_ge z (by simpa [targetW] using hz)
      omega
  have hinstσW : InstantiatesBy (Ws.map (Ty.fvar ·)) σe.body targetW := by
    exact InstantiatesBy.openVars (Xs := Ws) (n := σe.paramCount)
      (by simpa [σe] using hσwf) (by simp [Ws, σe])
  obtain ⟨args, hargsLC, hargs⟩ := hgen (Ws.map (Ty.fvar ·)) targetW
    (fun t ht => by
      obtain ⟨w, hw, rfl⟩ := List.mem_map.mp ht
      exact ContainsBvarsUpTo.fvar) (by simpa [σe] using hinstσW)
  have hinstA : InstantiatesBy args (Rer.onTy (Ty.closeOver g τe)) targetW := by
    simpa [Rer, g, τe, PolyTy.genGroup] using hargs
  obtain ⟨U0, hU0, hU0lc, hU0target, hU0τ, hU0keep⟩ :=
    Subst.exists_proxy_unifier (g := g) (keep := P ++ rigid ++ Ws) (τ := τe)
      (target := targetW) (R := Rer) (args := args)
      hgnodup hτelc hRerlc hargsLC hinstA hgtargetW hRertargetW
  have hblockfix : ∀ z, z < Φ → block.onTy (.fvar z) = .fvar z := by
    intro z hz
    apply Ty.substFvars_eq_self_of_no_key
    intro p hp hc
    rw [show block = blockList Φ W σ.paramCount from rfl] at hp
    simp only [blockList, List.mem_map] at hp
    obtain ⟨i, hi, hp⟩ := hp
    subst p
    simp only [Ty.freeVars, List.mem_singleton] at hc
    omega
  have hblockτ : block.onTy τe = τe := by
    apply Ty.substFvars_eq_self_of_no_key
    intro p hp hc
    rw [show block = blockList Φ W σ.paramCount from rfl] at hp
    simp only [blockList, List.mem_map] at hp
    obtain ⟨i, hi, hp⟩ := hp
    subst p
    have hlt := hτebelow.mem_lt (Φ + i) hc
    omega
  have htargetYavoidW : ∀ v ∈ targetY.freeVars,
      ¬ (W ≤ v ∧ v < W + σ.paramCount) := by
    intro v hv hbad
    rcases Ty.freeVars_openVars_subset v (by simpa [targetY] using hv) with hb | hy
    · have hlt := hσebodybelow.mem_lt v hb
      omega
    · have hlt := freshVars_lt v (by simpa [Ys] using hy)
      omega
  have hblocktarget : block.onTy targetY = targetW := by
    rw [show block = blockList Φ W σ.paramCount from rfl,
      blockList_onTy hWge htargetYavoidW]
    exact Ty.rename_openVars_blockSwap hWge σe.body
      (fun v hv => hσebodybelow.mem_lt v hv)
  have hRer_fvar_below : ∀ z, z < W → ∀ v ∈ (Rer.onTy (.fvar z)).freeVars, v < W := by
    intro z hz v hv
    rcases Subst.mem_freeVars_onTy hv with hv | ⟨p, hp, hv⟩
    · simp only [Ty.freeVars, List.mem_singleton] at hv
      simpa [hv] using hz
    · exact hW_Rrange p hp v hv
  have hbackRer : ∀ z, z < W → back.onTy (Rer.onTy (.fvar z)) = Rer.onTy (.fvar z) := by
    intro z hz
    apply Ty.substFvars_eq_self_of_no_key
    intro p hp hc
    rw [show back = blockListBack Φ W σ.paramCount from rfl] at hp
    simp only [blockListBack, List.mem_map] at hp
    obtain ⟨i, hi, hp⟩ := hp
    subst p
    have hlt := hRer_fvar_below z hz (W + i) hc
    omega
  let U : Subst := block ++ U0 ++ back
  have hUuni : Unifies U τe targetY := by
    unfold Unifies
    simp only [U, Subst.onTy_append]
    rw [hblockτ, hblocktarget]
    exact congrArg back.onTy hU0
  have hUagree : ∀ z ∈ τe.freeVars, z ∉ G →
      U.onTy (.fvar z) = Rer.onTy (.fvar z) := by
    intro z hz hnotG
    have hzΦ := hτebelow.mem_lt z hz
    have hnotg : z ∉ g := fun hzg => hnotG (hgsub z hzg)
    rw [show U = block ++ U0 ++ back from rfl, Subst.onTy_append,
      Subst.onTy_append, hblockfix z hzΦ, hU0τ z hz hnotg]
    apply hbackRer
    exact lt_of_lt_of_le hzΦ (by omega)
  have hblock_fvar : ∀ i, i < σ.paramCount →
      block.onTy (.fvar (Φ + i)) = .fvar (W + i) := by
    intro i hi
    change Subst.onTy ((List.range σ.paramCount).map
      (fun i => (Φ + i, Ty.fvar (W + i)))) (.fvar (Φ + i)) = .fvar (W + i)
    rw [rangeMapList_onTy_fvar Φ W σ.paramCount (Or.inl hWge) (Φ + i)]
    split_ifs <;> congr 1 <;> omega
  have hback_fvar : ∀ i, i < σ.paramCount →
      back.onTy (.fvar (W + i)) = .fvar (Φ + i) := by
    intro i hi
    change Subst.onTy ((List.range σ.paramCount).map
      (fun i => (W + i, Ty.fvar (Φ + i)))) (.fvar (W + i)) = .fvar (Φ + i)
    rw [rangeMapList_onTy_fvar W Φ σ.paramCount (Or.inr hWge) (W + i)]
    split_ifs <;> congr 1 <;> omega
  have hUfixP : ∀ z ∈ P, U.onTy (.fvar z) = .fvar z := by
    intro z hz
    have hzΦ := hPbelow z hz
    have hnotg : z ∉ g := fun hzg => hPG z hz (hgsub z hzg)
    have hU0z := hU0keep z (by
      simpa [List.append_assoc] using List.mem_append_left (rigid ++ Ws) hz) hnotg
    rw [show U = block ++ U0 ++ back from rfl, Subst.onTy_append,
      Subst.onTy_append, hblockfix z hzΦ, hU0z]
    simpa [hRerP z hz] using hbackRer z (lt_of_lt_of_le hzΦ (by omega))
  have hUfixRigid : ∀ z ∈ rigid, U.onTy (.fvar z) = .fvar z := by
    intro z hz
    have hzΦ := hrigidbelow z hz
    have hnotg : z ∉ g := fun hzg => hrigidG z hz (hgsub z hzg)
    have hU0z := hU0keep z (by
      simpa [List.append_assoc] using List.mem_append_right P
        (List.mem_append_left Ws hz)) hnotg
    rw [show U = block ++ U0 ++ back from rfl, Subst.onTy_append,
      Subst.onTy_append, hblockfix z hzΦ, hU0z]
    simpa [hRerrigid z hz] using hbackRer z (lt_of_lt_of_le hzΦ (by omega))
  have hUfixYs : ∀ z ∈ Ys, U.onTy (.fvar z) = .fvar z := by
    intro z hz
    simp only [Ys, freshVars, List.mem_map, List.mem_range] at hz
    obtain ⟨i, hi, hzi⟩ := hz
    subst z
    have hnotg : W + i ∉ g := fun hzg => by
      have hlt := hW_G (W + i) (hgsub _ hzg)
      omega
    have hU0z := hU0keep (W + i) (by
      exact List.mem_append_right (P ++ rigid) (by
        simp only [Ws, freshVars, List.mem_map, List.mem_range]
        exact ⟨i, hi, rfl⟩)) hnotg
    rw [show U = block ++ U0 ++ back from rfl, Subst.onTy_append,
      Subst.onTy_append, hblock_fvar i hi, hU0z, hRerWfix (W + i) (by
        simp only [Ws, freshVars, List.mem_map, List.mem_range]
        exact ⟨i, hi, rfl⟩), hback_fvar i hi]
  refine ⟨U, ?_, ?_, ?_, ?_⟩
  · intro p hp
    change p ∈ block ++ U0 ++ back at hp
    rcases List.mem_append.mp hp with hp | hp
    · rcases List.mem_append.mp hp with hp | hp
      · exact blockList_lc Φ W σ.paramCount p (by simpa [block] using hp)
      · exact hU0lc p hp
    · exact blockListBack_lc Φ W σ.paramCount p (by simpa [back] using hp)
  · simpa [τe, targetY, σe, Ys] using hUuni
  · intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · rcases List.mem_append.mp hx with hx | hx
      · exact hUfixP x hx
      · exact hUfixRigid x hx
    · exact hUfixYs x (by simpa [Ys] using hx)
  · simpa [τe, Rer] using hUagree

/-- A single committed recursive-ceiling step is absorbed by a residual which
    already generalises the pre-ceiling member scheme.

    The non-obvious part is the `Ys -> Ws -> Ys` sandwich.  The annotation is
    checked at the current skolem block `Ys`, but the ambient residual may
    bind those *future* names.  We therefore move the opening to a fresh block
    `Ws`, obtain the generality witness there, and conjugate its unifier by
    `blockList`/`blockListBack`.  The resulting witness still agrees with the
    ambient residual on retained member keys and on rigid range variables. -/
private theorem RecCeilingConstraints.step_absorbed
    {K rigid G : List Nat} {Φ : Nat} {τ : Ty} {σ : PolyTy}
    {full step R : Subst}
    (hG : G.Nodup)
    (hrigidG : ∀ x ∈ rigid, x ∉ G)
    (hRlc : ∀ p ∈ R, p.2.IsLC)
    (hRrigid : ∀ x ∈ rigid, R.onTy (.fvar x) = .fvar x)
    (hτlc : τ.IsLC) (hτbelow : τ.BelowFvars Φ)
    (hrigidbelow : ∀ x ∈ rigid, x < Φ)
    (hfull : UnifyRel ( τ)
      ( (σ.openVars (freshVars Φ σ.paramCount))) full)
    (havoid : ∀ p ∈ full, p.1 ∉ K ++ rigid ++ freshVars Φ σ.paramCount)
    (hstep : step = Subst.dropDomains G full)
    (hrange : ∀ p ∈ step, ∀ x ∈ p.2.freeVars, x ∈ rigid ∧ x ∉ G)
    (_hstepLC : ∀ p ∈ step, p.2.IsLC)
    (hσwf : σ.WF)
    (hσrigid : ∀ x ∈ σ.body.freeVars, x ∈ rigid)
    (hgen : ( (R.onPolyTy (PolyTy.genGroup G τ))).Generalizes
      ( σ)) :
    Subst.Factors R step R := by
  let τe : Ty :=  τ
  let σe : PolyTy :=  σ
  let Ys : List Nat := freshVars Φ σ.paramCount
  let Rer : Subst := R
  let g : List Nat := Ty.genFilter G τe
  have hτelc : τe.IsLC := hτlc
  have hτebelow : τe.BelowFvars Φ :=
    Ty.BelowFvars.of_freeVars_lt (fun v hv =>
      hτbelow.mem_lt v ((by simpa [τe] using hv)))
  have hσebodybelow : σe.body.BelowFvars Φ :=
    Ty.BelowFvars.of_freeVars_lt (fun v hv =>
      hrigidbelow v (hσrigid v
        ((by simpa [σe] using hv))))
  have hgnodup : g.Nodup := by
    rw [show g = Ty.genFilter G τe from rfl]
    unfold Ty.genFilter
    exact hG.filter _
  have hgsub : ∀ x ∈ g, x ∈ G := by
    intro x hx
    exact Ty.mem_of_mem_genFilter hx
  have hRerlc : ∀ p ∈ Rer, p.2.IsLC := by
    simpa [Rer] using hRlc
  have hRer_fvar : ∀ z : Nat,
      Rer.onTy (.fvar z) =  (R.onTy (.fvar z)) := by
    intro z
    rfl
  have hRerrigid : ∀ x ∈ rigid, Rer.onTy (.fvar x) = .fvar x := by
    intro x hx
    rw [hRer_fvar x, hRrigid x hx]
  obtain ⟨W, hWge, hWfresh⟩ := exists_fresh_block
    (R.map Prod.fst ++ R.flatMap (fun p => p.2.freeVars) ++ G ++ rigid) Φ σ.paramCount
  let Ws : List Nat := freshVars W σ.paramCount
  let block : Subst := blockList Φ W σ.paramCount
  let back : Subst := blockListBack Φ W σ.paramCount
  let targetY : Ty := σe.openVars Ys
  let targetW : Ty := σe.openVars Ws
  have hW_Rdom : ∀ p ∈ R, p.1 < W := by
    intro p hp
    exact hWfresh p.1 (by
      simp only [List.mem_append]
      exact Or.inl (Or.inl (Or.inl (List.mem_map.mpr ⟨p, hp, rfl⟩))))
  have hW_Rrange : ∀ p ∈ R, ∀ v ∈ p.2.freeVars, v < W := by
    intro p hp v hv
    exact hWfresh v (by
      simp only [List.mem_append]
      exact Or.inl (Or.inl (Or.inr (List.mem_flatMap.mpr ⟨p, hp, hv⟩))))
  have hW_G : ∀ x ∈ G, x < W := by
    intro x hx
    exact hWfresh x (by
      simp only [List.mem_append]
      exact Or.inl (Or.inr hx))
  have hW_rigid : ∀ x ∈ rigid, x < W := by
    intro x hx
    exact hWfresh x (by
      simp only [List.mem_append]
      exact Or.inr hx)
  have hWs_ge : ∀ w ∈ Ws, W ≤ w := by
    intro w hw
    exact freshVars_ge w (by simpa [Ws] using hw)
  have hRerWfix : ∀ w ∈ Ws, Rer.onTy (.fvar w) = .fvar w := by
    intro w hw
    apply Ty.substFvars_eq_self_of_no_key
    intro p hp hc
    simp only [Ty.freeVars, List.mem_singleton] at hc
    have hlt := hW_Rdom p hp
    have hge := hWs_ge w hw
    omega
  have hRertargetW : ∀ v ∈ targetW.freeVars,
      Rer.onTy (.fvar v) = .fvar v := by
    intro v hv
    rcases Ty.freeVars_openVars_subset v (by simpa [targetW] using hv) with hv | hv
    · exact hRerrigid v (hσrigid v
        ((by simpa [σe] using hv)))
    · exact hRerWfix v (by simpa [targetW] using hv)
  have hgtargetW : ∀ z ∈ g, z ∉ targetW.freeVars := by
    intro z hzg hzt
    rcases Ty.freeVars_openVars_subset z (by simpa [targetW] using hzt) with hz | hz
    · exact hrigidG z (hσrigid z
        ((by simpa [σe] using hz))) (hgsub z hzg)
    · have hzglt := hW_G z (hgsub z hzg)
      have hzge := hWs_ge z (by simpa [targetW] using hz)
      omega
  have hinstσW : InstantiatesBy (Ws.map (Ty.fvar ·)) σe.body targetW := by
    exact InstantiatesBy.openVars (Xs := Ws) (n := σe.paramCount)
      (by simpa [σe] using hσwf) (by simp [Ws, σe])
  obtain ⟨args, hargsLC, hargs⟩ := hgen (Ws.map (Ty.fvar ·)) targetW
    (fun t ht => by
      obtain ⟨w, hw, rfl⟩ := List.mem_map.mp ht
      exact ContainsBvarsUpTo.fvar) (by simpa [σe] using hinstσW)
  have hinstA : InstantiatesBy args (Rer.onTy (Ty.closeOver g τe)) targetW := by
    simpa [Rer, g, τe, PolyTy.genGroup] using hargs
  obtain ⟨U0, hU0, hU0lc, hU0target, hU0τ, hU0rigid⟩ :=
    Subst.exists_proxy_unifier (g := g) (keep := rigid) (τ := τe)
      (target := targetW) (R := Rer) (args := args)
      hgnodup hτelc hRerlc hargsLC hinstA hgtargetW hRertargetW
  have hblockfix : ∀ z, z < Φ → block.onTy (.fvar z) = .fvar z := by
    intro z hz
    apply Ty.substFvars_eq_self_of_no_key
    intro p hp hc
    rw [show block = blockList Φ W σ.paramCount from rfl] at hp
    simp only [blockList, List.mem_map] at hp
    obtain ⟨i, hi, hp⟩ := hp
    subst p
    simp only [Ty.freeVars, List.mem_singleton] at hc
    omega
  have hblockτ : block.onTy τe = τe := by
    apply Ty.substFvars_eq_self_of_no_key
    intro p hp hc
    rw [show block = blockList Φ W σ.paramCount from rfl] at hp
    simp only [blockList, List.mem_map] at hp
    obtain ⟨i, hi, hp⟩ := hp
    subst p
    have hlt := hτebelow.mem_lt (Φ + i) hc
    omega
  have htargetYavoidW : ∀ v ∈ targetY.freeVars,
      ¬ (W ≤ v ∧ v < W + σ.paramCount) := by
    intro v hv hbad
    rcases Ty.freeVars_openVars_subset v (by simpa [targetY] using hv) with hb | hy
    · have hlt := hσebodybelow.mem_lt v hb
      omega
    · have hlt := freshVars_lt v (by simpa [Ys] using hy)
      omega
  have hblocktarget : block.onTy targetY = targetW := by
    rw [show block = blockList Φ W σ.paramCount from rfl,
      blockList_onTy hWge htargetYavoidW]
    exact Ty.rename_openVars_blockSwap hWge σe.body
      (fun v hv => hσebodybelow.mem_lt v hv)
  have hRer_fvar_below : ∀ z, z < W → ∀ v ∈ (Rer.onTy (.fvar z)).freeVars, v < W := by
    intro z hz v hv
    rcases Subst.mem_freeVars_onTy hv with hv | ⟨p, hp, hv⟩
    · simp only [Ty.freeVars, List.mem_singleton] at hv
      simpa [hv] using hz
    · exact hW_Rrange p hp v hv
  have hbackRer : ∀ z, z < W → back.onTy (Rer.onTy (.fvar z)) = Rer.onTy (.fvar z) := by
    intro z hz
    apply Ty.substFvars_eq_self_of_no_key
    intro p hp hc
    rw [show back = blockListBack Φ W σ.paramCount from rfl] at hp
    simp only [blockListBack, List.mem_map] at hp
    obtain ⟨i, hi, hp⟩ := hp
    subst p
    have hlt := hRer_fvar_below z hz (W + i) hc
    omega
  let U : Subst := block ++ U0 ++ back
  have hUuni : Unifies U τe targetY := by
    unfold Unifies
    simp only [U, Subst.onTy_append]
    rw [hblockτ, hblocktarget]
    exact congrArg back.onTy hU0
  have hUuniFull : Unifies U ( τ)
      ( (σ.openVars (freshVars Φ σ.paramCount))) := by
    simpa [τe, targetY, σe, Ys] using hUuni
  have hUeqRerτ : ∀ z ∈ τe.freeVars, z ∉ G →
      U.onTy (.fvar z) = Rer.onTy (.fvar z) := by
    intro z hz hnotG
    have hzΦ := hτebelow.mem_lt z hz
    have hnotg : z ∉ g := fun hzg => hnotG (hgsub z hzg)
    rw [show U = block ++ U0 ++ back from rfl, Subst.onTy_append,
      Subst.onTy_append, hblockfix z hzΦ, hU0τ z hz hnotg]
    apply hbackRer
    exact lt_of_lt_of_le hzΦ (by omega)
  have hUeqRerrigid : ∀ z ∈ rigid,
      U.onTy (.fvar z) = Rer.onTy (.fvar z) := by
    intro z hz
    have hzΦ := hrigidbelow z hz
    have hnotg : z ∉ g := fun hzg => hrigidG z hz (hgsub z hzg)
    rw [show U = block ++ U0 ++ back from rfl, Subst.onTy_append,
      Subst.onTy_append, hblockfix z hzΦ, hU0rigid z hz hnotg]
    apply hbackRer
    exact lt_of_lt_of_le hzΦ (by omega)
  have hUagreesτ : ∀ z ∈ τe.freeVars, z ∉ G →
      Eq (U.onTy (.fvar z)) (R.onTy (.fvar z)) := by
    intro z hz hnotG
    rw [hUeqRerτ z hz hnotG, hRer_fvar z]
  have hUagreesrigid : ∀ z ∈ rigid,
      Eq (U.onTy (.fvar z)) (R.onTy (.fvar z)) := by
    intro z hz
    rw [hUeqRerrigid z hz, hRer_fvar z]
  apply Subst.Factors.of_satisfies
  intro p hpstep
  have hpfull : p ∈ full := by
    rw [hstep] at hpstep
    exact (Subst.mem_dropDomains.mp hpstep).1
  have hpnotG : p.1 ∉ G := by
    rw [hstep] at hpstep
    exact (Subst.mem_dropDomains.mp hpstep).2
  have hUdom : Eq (U.onTy (.fvar p.1)) (R.onTy (.fvar p.1)) := by
    rcases UnifyRel.dom_mem hfull p hpfull with hpτ | hpσ
    · exact hUagreesτ p.1 hpτ hpnotG
    · have hpY : p.1 ∈ targetY.freeVars := by
        rw [show targetY =  (σ.openVars Ys) by simp [targetY, σe]]
        simpa [Ys] using hpσ
      rcases Ty.freeVars_openVars_subset p.1 (by simpa [targetY] using hpY) with hpbody | hpys
      · exact False.elim (havoid p hpfull (by
          simp only [List.mem_append]
          exact Or.inl (Or.inr (hσrigid p.1
            ((by simpa [σe] using hpbody))))))
      · exact False.elim (havoid p hpfull (by
          simp only [List.mem_append]
          exact Or.inr (by simpa [Ys] using hpys)))
  have hUrange : Eq (U.onTy p.2) (R.onTy p.2) :=
    Subst.onTy_congr_of_freeVars (fun z hz =>
      hUagreesrigid z (hrange p hpstep z hz).1)
  exact hUdom.symm.trans
    ((UnifyRel.binding_satisfies hfull U hUuniFull p hpfull).trans hUrange)

/-- **Erase-level body retype** (port of caac62d's `letRecFused_body_retype`): the
    `R₁`-transported algorithmic body schemes (ceilingSchemes) generalise the
    declarative `bodyCtx` schemes, so the declarative body typing transports to
    the `R₁`-transported algorithmic body context. `hconn` is the per-position
    spec-level connection `R₁.onTy (S₁.onTy (fvar (Φ+j)))
    = renameG G Xs τdecl` (derived in COMPLETE-LETREC from the
    group tier's full-frontier R₀-side agreement + the block link); `hσfix` the
    scheme rigidity for annotated members. -/
private theorem letRecFused_body_retype_preSc
    {Φ : Nat} {ctx : Ctx} {S₁ R₁ S₀ : Subst} {anns : List (Option PolyTy)}
    {bindings : List Expr} {body : Expr} {dspecs : List RecSpec} {G Xs : List Nat}
    {τ₀ : Ty} {K : List Nat}
    (hanns_eq : dspecs.map RecSpec.ann = anns)
    (hdlc : ∀ τ, RecSpec.mono τ ∈ dspecs → τ.IsLC)
    (hG : G.Nodup)
    (hXlen : Xs.length = G.length) (hXnodup : Xs.Nodup)
    (hXG : ∀ g ∈ G, g ∉ Xs)
    (hXτs : ∀ x ∈ Xs, ∀ τ, RecSpec.mono τ ∈ dspecs → x ∉ τ.freeVars)
    (hXenv : ∀ x ∈ Xs, x ∉ (S₀.onCtx ctx).env.freeVars)
    (hXrigid : ∀ x ∈ Xs, x ∉ RecGroup.rigidVars anns bindings)
    (hS₁lc : ∀ p ∈ S₁, p.2.IsLC) (hR₁lc : ∀ p ∈ R₁, p.2.IsLC)
    (hctxS₁ : (R₁.onCtx (S₁.onCtx ctx)) = (S₀.onCtx ctx))
    (hKrigid : ∀ y ∈ RecGroup.rigidVars anns bindings, y ∈ K)
    (hR₁K : ∀ k ∈ K, R₁.onTy (Ty.fvar k) = Ty.fvar k)
    (hσfix : ∀ σ, some σ ∈ anns → R₁.onPolyTy σ = σ)
    (hconn : ∀ (j : Nat) (hj : j < dspecs.length) (τdecl : Ty),
        dspecs[j]'hj = RecSpec.mono τdecl →
      Subst.onTy (R₁)
          ( (S₁.onTy (Ty.fvar (Φ + j))))
        = Ty.renameG G Xs ( τdecl))
    (hbodydecl : TypeOfHM (RecSpecs.bodyCtx (S₀.onCtx ctx) dspecs G)
        body ( τ₀)) :
    TypeOfHM (R₁.onCtx ⟨(RecSpecs.ceilingSchemes
          (genGroupVars (RecGroup.rigidVars anns bindings) (S₁.onCtx ctx).env
            (RecSpecs.monoTys ((RecSpec.init Φ anns).map (RecSpec.onSubst S₁))))
          anns ((RecSpec.init Φ anns).map (RecSpec.onSubst S₁)))
        ++ (S₁.onCtx ctx).env, (S₁.onCtx ctx).ctors⟩)
      body ( τ₀) := by
  set rigid := RecGroup.rigidVars anns bindings with hrigid_def
  set envS₁ := (S₁.onCtx ctx).env with henvS₁_def
  set solved := (RecSpec.init Φ anns).map (RecSpec.onSubst S₁) with hsolved_def
  set Ginf := genGroupVars rigid envS₁ (RecSpecs.monoTys solved) with hGinf_def
  set Rer : Subst := R₁ with hRer_def
  have hsolved_len : solved.length = dspecs.length := by
    have h1 := congrArg List.length hanns_eq
    simp only [List.length_map] at h1
    rw [hsolved_def]
    simp [RecSpec.init_length, h1]
  have hsolved_lc_mono : ∀ τ, RecSpec.mono τ ∈ solved → τ.IsLC := by
    intro τ hτ
    rw [hsolved_def] at hτ
    obtain ⟨s, hs, hseq⟩ := List.mem_map.mp hτ
    cases s with
    | mono τ0 =>
      have hτeq : τ = S₁.onTy τ0 := by
        have hred : RecSpec.onSubst S₁ (RecSpec.mono τ0) = RecSpec.mono (S₁.onTy τ0) := rfl
        rw [hred] at hseq
        injection hseq with h
        exact h.symm
      subst hτeq
      rcases RecSpec.mem_init hs with ⟨m, _, _, heq⟩ | ⟨σ0, _, heq⟩
      · cases heq
        exact Subst.onTy_lc hS₁lc ContainsBvarsUpTo.fvar
      · exact absurd heq (by simp)
    | poly σ0 => exact absurd hseq (by simp [RecSpec.onSubst])
  have hRerlc : ∀ p ∈ Rer, p.2.IsLC := by
    simpa [hRer_def] using hR₁lc
  -- pointwise generalisation of the declarative body schemes (erased level)
  set algEntries : List PolyTy := (RecSpecs.ceilingSchemes Ginf anns solved).map
    (fun M =>  (R₁.onPolyTy M)) with halg_def
  set declEntries : List PolyTy := dspecs.map (fun s =>  (RecSpec.bodyScheme G s)) with hdecl_def
  have hlen_alg : algEntries.length = dspecs.length := by
    rw [halg_def, List.length_map]
    unfold RecSpecs.ceilingSchemes
    rw [List.length_map, List.length_zip, hsolved_len]
    have h1 : dspecs.length = anns.length := by
      have h := congrArg List.length hanns_eq
      simpa using h
    omega
  have hforall : List.Forall₂ PolyTy.Generalizes algEntries declEntries := by
    apply forall₂_of_getElem
    · simpa [hdecl_def, List.length_map] using hlen_alg
    · intro i h₁ h₂
      simp only [halg_def, hdecl_def, List.getElem_map]
      have hdi : i < dspecs.length := by omega
      have hiA : i < anns.length := by
        have h1 : dspecs.length = anns.length := by
          have h := congrArg List.length hanns_eq
          simpa using h
        omega
      have hiS : i < solved.length := by
        rw [hsolved_len]
        exact hdi
      have hcs_idx : i < (RecSpecs.ceilingSchemes Ginf anns solved).length := by
        have h := hlen_alg
        rw [halg_def, List.length_map] at h
        omega
      have hcs : (RecSpecs.ceilingSchemes Ginf anns solved)[i]'hcs_idx = match anns[i]'(hiA) with
          | some σ => σ | none => RecSpec.bodyScheme Ginf (solved[i]'hiS) := by
        unfold RecSpecs.ceilingSchemes
        rw [List.getElem_map, List.getElem_zip]
        rfl
      cases hd : dspecs[i]'hdi with
      | mono τdecl =>
        -- the solved spec at `i` is mono, connected through `renameG G Xs`
        have hann_i : anns[i]'(hiA) = none := by
          have h := congrArg (fun l => l[i]?) hanns_eq
          simp only [List.getElem?_map] at h
          rw [List.getElem?_eq_getElem hdi, List.getElem?_eq_getElem hiA] at h
          have h' : RecSpec.ann (dspecs[i]'hdi) = none := by rw [hd]; rfl
          cases hannv : anns[i]'(hiA) with
          | none => rfl
          | some a => simp [h', hannv] at h
        have hinit_i : (RecSpec.init Φ anns)[i]'(by simpa [RecSpec.init_length] using hiA)
            = RecSpec.mono (Ty.fvar (Φ + i)) := by
          have hg : (RecSpec.init Φ anns)[i]? = (anns[i]?).map (fun _ => RecSpec.mono (Ty.fvar (Φ + i))) :=
            RecSpec.init_getElem? Φ anns i
          rw [List.getElem?_eq_getElem (by simpa [RecSpec.init_length] using hiA)] at hg
          have hann' : anns[i]? = some none := by
            rw [List.getElem?_eq_getElem hiA]
            rw [hann_i]
          rw [hann'] at hg
          simpa using hg
        have hsolved_i : solved[i]'hiS = RecSpec.mono (S₁.onTy (Ty.fvar (Φ + i))) := by
          dsimp [solved]
          rw [List.getElem_map]
          show RecSpec.onSubst S₁ ((RecSpec.init Φ anns)[i]'(by simpa [RecSpec.init_length] using hiA))
              = RecSpec.mono (S₁.onTy (Ty.fvar (Φ + i)))
          rw [hinit_i]
          rfl
        have hτinf_mem : RecSpec.mono (S₁.onTy (Ty.fvar (Φ + i))) ∈ solved := by
          rw [hsolved_def]
          refine List.mem_map.mpr ⟨RecSpec.mono (Ty.fvar (Φ + i)), ?_, rfl⟩
          exact hinit_i ▸ List.getElem_mem (by simpa [RecSpec.init_length] using hiA)
        have hτdecl_mem : RecSpec.mono τdecl ∈ dspecs := by
          rw [← hd]
          exact List.getElem_mem hdi
        have hτinf_lc : (S₁.onTy (Ty.fvar (Φ + i))).IsLC :=
          Subst.onTy_lc hS₁lc ContainsBvarsUpTo.fvar
        have hci : Rer.onTy ( (S₁.onTy (Ty.fvar (Φ + i))))
            = Ty.renameG G Xs ( τdecl) := by
          simpa [hRer_def] using (hconn i hdi τdecl hd)
        have hXinf : ∀ x ∈ Xs, x ∉ (Rer.onPolyTy (PolyTy.genGroup Ginf
            ( (S₁.onTy (Ty.fvar (Φ + i)))))).body.freeVars := by
          intro x hx hmem
          change x ∈ (Rer.onTy (Ty.closeOver (Ty.genFilter Ginf
            ( (S₁.onTy (Ty.fvar (Φ + i))))) ( (S₁.onTy (Ty.fvar (Φ + i)))))).freeVars at hmem
          obtain ⟨v, hv, hxv⟩ := Ty.mem_freeVars_onTy_iff.mp hmem
          have hvτ : v ∈ ( (S₁.onTy (Ty.fvar (Φ + i)))).freeVars :=
            Ty.freeVars_closeOver_subset hv
          have hvτ' : v ∈ (S₁.onTy (Ty.fvar (Φ + i))).freeVars :=
            hvτ
          have hvGinf : v ∉ Ginf := by
            intro hgi
            exact Ty.not_mem_closeOver_freeVars
              (by simp only [Ty.genFilter, List.mem_filter, decide_eq_true_eq]
                  exact ⟨hgi, hvτ⟩) hv
          have hv_flist : v ∈ Ty.freeVarsList (RecSpecs.monoTys solved) :=
            mem_freeVarsList_monoTys (mem_monoTys_of_mem_solved hτinf_mem) hvτ'
          have hcase : v ∈ envS₁.freeVars ∨ v ∈ rigid := by
            by_contra hcon
            push_neg at hcon
            apply hvGinf
            rw [hGinf_def]
            simp only [genGroupVars, List.mem_filter, Bool.and_eq_true, Bool.not_eq_eq_eq_not,
              Bool.not_true, List.contains_eq_mem, decide_eq_false_iff_not]
            exact ⟨hv_flist, hcon.1, hcon.2⟩
          rcases hcase with henv | hrig
          · obtain ⟨pt, hpt, hvpt⟩ := Env.mem_freeVars_iff.mp henv
            have hxv' : x ∈ (R₁.onTy (Ty.fvar v)).freeVars := by
              have heq : Rer.onTy (Ty.fvar v) = R₁.onTy (Ty.fvar v) := by
                rw [hRer_def]
              rw [heq] at hxv
              exact hxv
            have hx_onTy : x ∈ (R₁.onTy pt.body).freeVars :=
              Ty.mem_freeVars_onTy_iff.mpr ⟨v, hvpt, hxv'⟩
            have hm2 : R₁.onPolyTy pt ∈ (R₁.onCtx (S₁.onCtx ctx)).env := by
              simp only [Subst.onCtx, Subst.onEnv]; exact List.mem_map.mpr ⟨pt, hpt, rfl⟩
            have hx1 : x ∈ (R₁.onCtx (S₁.onCtx ctx)).env.freeVars :=
              Env.mem_freeVars_iff.mpr ⟨R₁.onPolyTy pt, hm2, hx_onTy⟩
            have hc := congrArg Ctx.env hctxS₁
            have hx_S₀ : x ∈ (S₀.onCtx ctx).env.freeVars := by
              rwa [← hc]
            exact hXenv x hx hx_S₀
          · have hfix : R₁.onTy (Ty.fvar v) = Ty.fvar v := hR₁K v (hKrigid v hrig)
            have hxv' : x ∈ (R₁.onTy (Ty.fvar v)).freeVars := by
              have heq : Rer.onTy (Ty.fvar v) = R₁.onTy (Ty.fvar v) := by
                rw [hRer_def]
              rw [heq] at hxv
              exact hxv
            rw [hfix] at hxv'
            simp only [Ty.freeVars, List.mem_singleton] at hxv'
            exact hXrigid x hx (by rw [hxv']; exact hrig)
        have hgen := genGroup_generalizes_renameG (Ginf := Ginf)
          (G := G) (Xsfull := Xs)
          (τinf :=  (S₁.onTy (Ty.fvar (Φ + i)))) (τdecl :=  τdecl)
          (R := Rer)
          hτinf_lc (hdlc τdecl hτdecl_mem) hRerlc
          hG hXlen hXnodup hXG
          (fun x hx hc => hXτs x hx τdecl hτdecl_mem (hc))
          hci hXinf
        have hgen' : ( (R₁.onPolyTy (RecSpec.bodyScheme Ginf
                (RecSpec.mono (S₁.onTy (Ty.fvar (Φ + i))))))).Generalizes
            ( (RecSpec.bodyScheme G (RecSpec.mono τdecl))) := by
          change ( (R₁.onPolyTy (PolyTy.genGroup Ginf (S₁.onTy (Ty.fvar (Φ + i)))))).Generalizes
            ( (PolyTy.genGroup G τdecl))
          simpa [Rer] using hgen
        simpa [hcs, hann_i, hsolved_i] using hgen'
      | poly σd =>
        -- rigid poly member: the original scheme `σ0` (`anns[i] = some σ0`)
        -- is fixed by `R₁`; both entries collapse to `σd`.
        have hannv : anns[i]'(hiA) ≠ none := by
          have h := congrArg (fun l => l[i]?) hanns_eq
          simp only [List.getElem?_map] at h
          rw [List.getElem?_eq_getElem hdi, List.getElem?_eq_getElem hiA] at h
          have h' : RecSpec.ann (dspecs[i]'hdi) = some σd := by rw [hd]; rfl
          intro hnone
          simp [h', hnone] at h
        cases hann : anns[i]'(hiA) with
        | none => exact absurd hann hannv
        | some σ0 =>
          have hσE : σd =  σ0 := by
            have h := congrArg (fun l => l[i]?) hanns_eq
            simp only [List.getElem?_map] at h
            rw [List.getElem?_eq_getElem hdi, List.getElem?_eq_getElem hiA] at h
            have h' : RecSpec.ann (dspecs[i]'hdi) = some σd := by rw [hd]; rfl
            simp [h', hann] at h
            exact h
          have hσ0_anns : some σ0 ∈ anns := by
            rw [← hann]
            exact List.getElem_mem hiA
          have hσ0fix : R₁.onPolyTy σ0 = σ0 := hσfix σ0 hσ0_anns
          have hrefl : ( (R₁.onPolyTy σ0)).Generalizes
              ( (RecSpec.bodyScheme G (RecSpec.poly σd))) := by
            rw [hσ0fix, hσE]
            simp [RecSpec.bodyScheme]
            exact PolyTy.Generalizes.refl _
          simpa [hcs, hann] using hrefl
  -- the outer env transport and the full Forall₂
  have houter_eq : envS₁.map R₁.onPolyTy
      = (S₀.onCtx ctx).env := by
    have hc := congrArg Ctx.env hctxS₁
    rw [henvS₁_def]
    simpa [Subst.onCtx, Subst.onEnv] using hc
  have hbodydecl' : TypeOfHM ⟨declEntries ++ envS₁.map R₁.onPolyTy,
        (S₀.onCtx ctx).ctors⟩ body ( τ₀) := by
    have hctxbody : (RecSpecs.bodyCtx (S₀.onCtx ctx) dspecs G)
        = ⟨declEntries ++ envS₁.map R₁.onPolyTy,
            (S₀.onCtx ctx).ctors⟩ := by
      apply congrArg₂ Ctx.mk
      · change dspecs.map (RecSpec.bodyScheme G) ++ (S₀.onCtx ctx).env = _
        rw [hdecl_def]
        congr 1
        exact houter_eq.symm
      · rfl
    simpa [hctxbody] using hbodydecl
  have hfinal := TypeOfHM.weaken_schemes hforall hbodydecl'
  have hctx : (R₁.onCtx ⟨RecSpecs.ceilingSchemes Ginf anns solved ++ envS₁, (S₁.onCtx ctx).ctors⟩)
      = ⟨algEntries ++ envS₁.map R₁.onPolyTy,
          (S₀.onCtx ctx).ctors⟩ := by
    apply congrArg₂ Ctx.mk
    · simp only [Subst.onCtx, Subst.onEnv, List.map_append]
      rw [halg_def]
    · simpa [Rer] using congrArg Ctx.ctors hctxS₁
  change TypeOfHM (R₁.onCtx ⟨RecSpecs.ceilingSchemes Ginf anns solved ++ envS₁,
    (S₁.onCtx ctx).ctors⟩) body τ₀
  rw [hctx]
  exact hfinal

/-- The post-ceiling form of the body retyping bridge.  `Ginf` is computed from
    `specs1`, before `Sc`; the solver may refine member monotypes, but it may
    neither touch nor reintroduce a pool variable.  A residual which absorbs
    `Sc` consequently sees exactly the same erased schemes and outer context.

    Keeping this as a thin transport over `..._preSc` is intentional: the
    generalisation proof is about the pre-ceiling group, and should not be
    reproved against a recomputed pool. -/
private theorem letRecFused_body_retype
    {Φ : Nat} {ctx : Ctx} {S₁ Sc R₁ S₀ : Subst} {anns : List (Option PolyTy)}
    {bindings : List Expr} {body : Expr} {dspecs specs1 specsC : List RecSpec} {G Xs : List Nat}
    {τ₀ : Ty} {K : List Nat}
    (hspecs1 : specs1 = (RecSpec.init Φ anns).map (RecSpec.onSubst S₁))
    (hspecsC : specsC = specs1.map (RecSpec.onSubst Sc))
    (hScdom : ∀ p ∈ Sc, p.1 ∉
      genGroupVars (RecGroup.rigidVars anns bindings) (S₁.onCtx ctx).env (RecSpecs.monoTys specs1))
    (hScrange : ∀ p ∈ Sc, ∀ u ∈ p.2.freeVars, u ∉
      genGroupVars (RecGroup.rigidVars anns bindings) (S₁.onCtx ctx).env (RecSpecs.monoTys specs1))
    (hfac : Subst.Factors R₁ Sc R₁)
    (hanns_eq : dspecs.map RecSpec.ann = anns)
    (hdlc : ∀ τ, RecSpec.mono τ ∈ dspecs → τ.IsLC)
    (hG : G.Nodup)
    (hXlen : Xs.length = G.length) (hXnodup : Xs.Nodup)
    (hXG : ∀ g ∈ G, g ∉ Xs)
    (hXτs : ∀ x ∈ Xs, ∀ τ, RecSpec.mono τ ∈ dspecs → x ∉ τ.freeVars)
    (hXenv : ∀ x ∈ Xs, x ∉ (S₀.onCtx ctx).env.freeVars)
    (hXrigid : ∀ x ∈ Xs, x ∉ RecGroup.rigidVars anns bindings)
    (hS₁lc : ∀ p ∈ S₁, p.2.IsLC) (hR₁lc : ∀ p ∈ R₁, p.2.IsLC)
    (hctxS₁ : (R₁.onCtx (S₁.onCtx ctx)) = (S₀.onCtx ctx))
    (hKrigid : ∀ y ∈ RecGroup.rigidVars anns bindings, y ∈ K)
    (hR₁K : ∀ k ∈ K, R₁.onTy (Ty.fvar k) = Ty.fvar k)
    (hσfix : ∀ σ, some σ ∈ anns → R₁.onPolyTy σ = σ)
    (hconn : ∀ (j : Nat) (hj : j < dspecs.length) (τdecl : Ty),
        dspecs[j]'hj = RecSpec.mono τdecl →
      Subst.onTy (R₁)
          ( (S₁.onTy (Ty.fvar (Φ + j))))
        = Ty.renameG G Xs ( τdecl))
    (hbodydecl : TypeOfHM (RecSpecs.bodyCtx (S₀.onCtx ctx) dspecs G)
        body ( τ₀)) :
    TypeOfHM (R₁.onCtx
      { (Sc.onCtx (S₁.onCtx ctx)) with
        env := RecSpecs.ceilingSchemes
                 (genGroupVars (RecGroup.rigidVars anns bindings) (S₁.onCtx ctx).env
                   (RecSpecs.monoTys specs1))
                 anns specsC ++ (Sc.onCtx (S₁.onCtx ctx)).env })
      body ( τ₀) := by
  subst specs1
  subst specsC
  set Ginf := genGroupVars (RecGroup.rigidVars anns bindings) (S₁.onCtx ctx).env
    (RecSpecs.monoTys ((RecSpec.init Φ anns).map (RecSpec.onSubst S₁)))
  have hceil_aux : ∀ (Ψ : Nat) (as : List (Option PolyTy)),
      (RecSpecs.ceilingSchemes Ginf as
        (((RecSpec.init Ψ as).map (RecSpec.onSubst S₁)).map (RecSpec.onSubst Sc))).map
          (fun M =>  (R₁.onPolyTy M))
        =
      (RecSpecs.ceilingSchemes Ginf as
        ((RecSpec.init Ψ as).map (RecSpec.onSubst S₁))).map
          (fun M =>  (R₁.onPolyTy M)) := by
    intro Ψ as
    induction as generalizing Ψ with
    | nil => simp [RecSpecs.ceilingSchemes, RecSpec.init]
    | cons a as ih =>
      cases a with
      | none =>
        have hhead := Subst.Factors.genGroup_stable (U := R₁) (Sc := Sc) (G := Ginf)
          (τ := S₁.onTy (Ty.fvar Ψ)) hfac hScdom hScrange
        simpa [RecSpecs.ceilingSchemes, RecSpec.init, RecSpec.onSubst,
          RecSpec.bodyScheme] using And.intro hhead (ih (Ψ + 1))
      | some σ =>
        simpa [RecSpecs.ceilingSchemes, RecSpec.init, RecSpec.onSubst] using ih (Ψ + 1)
  have hceil := hceil_aux Φ anns
  have honPoly : ∀ M : PolyTy,
       (R₁.onPolyTy (Sc.onPolyTy M)) =
         (R₁.onPolyTy M) := by
    intro M
    apply congrArg₂ PolyTy.mk rfl
    exact (hfac M.body).symm
  have houter : (Sc.onCtx (S₁.onCtx ctx)).env.map R₁.onPolyTy
      = (S₁.onCtx ctx).env.map R₁.onPolyTy := by
    simp only [Subst.onCtx, Subst.onEnv, List.map_map]
    apply List.map_congr_left
    intro M _
    exact honPoly (S₁.onPolyTy M)
  have hpre := letRecFused_body_retype_preSc (Φ := Φ) (ctx := ctx)
    (S₁ := S₁) (R₁ := R₁) (S₀ := S₀) (anns := anns) (bindings := bindings)
    (body := body) (dspecs := dspecs) (G := G) (Xs := Xs) (τ₀ := τ₀) (K := K)
    hanns_eq hdlc hG hXlen hXnodup hXG hXτs hXenv hXrigid hS₁lc hR₁lc hctxS₁
    hKrigid hR₁K hσfix hconn hbodydecl
  have hctx :
      (R₁.onCtx
        { (Sc.onCtx (S₁.onCtx ctx)) with
          env := RecSpecs.ceilingSchemes Ginf anns
                   (((RecSpec.init Φ anns).map (RecSpec.onSubst S₁)).map (RecSpec.onSubst Sc))
                 ++ (Sc.onCtx (S₁.onCtx ctx)).env })
      =
      (R₁.onCtx
        { (S₁.onCtx ctx) with
          env := RecSpecs.ceilingSchemes Ginf anns
                 ((RecSpec.init Φ anns).map (RecSpec.onSubst S₁))
                 ++ (S₁.onCtx ctx).env }) := by
    apply congrArg₂ Ctx.mk ?_ rfl
    change
      (RecSpecs.ceilingSchemes Ginf anns
          (((RecSpec.init Φ anns).map (RecSpec.onSubst S₁)).map (RecSpec.onSubst Sc))
          ++ (Sc.onCtx (S₁.onCtx ctx)).env).map R₁.onPolyTy
        =
      (RecSpecs.ceilingSchemes Ginf anns
          ((RecSpec.init Φ anns).map (RecSpec.onSubst S₁))
          ++ (S₁.onCtx ctx).env).map R₁.onPolyTy
    simp only [List.map_append]
    exact congrArg₂ List.append (by simpa [Function.comp_apply] using hceil) houter
  rw [hctx]
  simpa [Ginf] using hpre

/-- From the cofinite "types at every fresh opening of `σ`" premise, extract a
    typing at one *specific* opening `Ys` (any list of the right length): pick a
    generic fresh `Xs`, type at `σ.openVars Xs`, then rename `Xs → Ys`. (Erase
    world port of caac62d's `typeOfHM_at_block`.) -/
private theorem typeOfHM_at_block {ctx : Ctx} {rhs : Expr} {σ : PolyTy} {L Ys : List Nat}
    (hYlen : Ys.length = σ.paramCount)
    (hcofin : ∀ Xs : List Nat, FreshNames L σ.paramCount Xs →
      TypeOfHM ctx (rhs.openTyVars Xs) (σ.openVars Xs)) :
    TypeOfHM ctx (rhs.openTyVars Ys) (σ.openVars Ys) := by
  obtain ⟨Xs, hXlen, hXnodup, hXavoid⟩ :=
    exists_fresh_names (L ++ ctx.env.freeVars ++ Ys ++ rhs.tyFreeVars ++ σ.body.freeVars)
      σ.paramCount
  have hXL : ∀ x ∈ Xs, x ∉ L := fun x hx hc => hXavoid x hx (by simp only [List.mem_append]; tauto)
  have hXenv : ∀ x ∈ Xs, x ∉ ctx.env.freeVars := fun x hx hc =>
    hXavoid x hx (by simp only [List.mem_append]; tauto)
  have hXYs : ∀ x ∈ Xs, x ∉ Ys := fun x hx hc => hXavoid x hx (by simp only [List.mem_append]; tauto)
  have hXrhs : ∀ x ∈ Xs, x ∉ rhs.tyFreeVars := fun x hx hc =>
    hXavoid x hx (by simp only [List.mem_append]; tauto)
  have hXσ : ∀ x ∈ Xs, x ∉ σ.body.freeVars := fun x hx hc =>
    hXavoid x hx (by simp only [List.mem_append]; tauto)
  set ρ : Subst := Xs.zip (Ys.map (Ty.fvar ·)) with hρ_def
  have hρlc : ∀ p ∈ ρ, p.2.IsLC := by
    intro p hp
    rw [hρ_def] at hp
    obtain ⟨_, hpy⟩ := List.of_mem_zip hp
    obtain ⟨y, _, hyeq⟩ := List.mem_map.mp hpy
    simpa [hyeq] using (ContainsBvarsUpTo.fvar : (Ty.fvar y).IsLC)
  have hρctx : ρ.onCtx ctx = ctx := by
    rw [hρ_def]
    apply congrArg (fun E => (⟨E, ctx.ctors⟩ : Ctx))
    exact Subst.onEnv_eq_self_of_fresh (fun p hp hc =>
      hXenv p.1 (List.of_mem_zip hp).1 hc)
  have hwit := hcofin Xs ⟨hXlen, hXnodup, hXL⟩
  have hren := TypeOfHM.onSubst ρ hρlc hwit
  have hsubj : (rhs.openTyVars Xs).substTyFvars ρ = rhs.openTyVars Ys := by
    rw [hρ_def]
    exact Expr.substTyFvars_zip_openTyVars (Ys := Xs) (Xs := Ys)
      (hXlen.trans hYlen.symm) hXnodup hXrhs hXYs
  have hty : ρ.onTy (σ.openVars Xs) = σ.openVars Ys := by
    rw [hρ_def]
    have h1 : σ.openVars Xs = Ty.openVars Xs σ.body := rfl
    have h2 : σ.openVars Ys = Ty.openVars Ys σ.body := rfl
    rw [h1, h2]
    change Ty.substFvars (Xs.zip (Ys.map (Ty.fvar ·))) (Ty.openVars Xs σ.body)
      = Ty.openVars Ys σ.body
    rw [show Ty.substFvars (Xs.zip (Ys.map (Ty.fvar ·))) (Ty.openVars Xs σ.body)
        = Ty.openVars Ys σ.body from by
      have h3 := Ty.openWith_eq_substFvars_openVars (ty := σ.body)
        (Vs := Ys.map (Ty.fvar ·)) (Xs := Xs)
        ⟨by rw [List.length_map]; exact hYlen.trans hXlen.symm, fun V hV => by
          obtain ⟨y, _, hyeq⟩ := List.mem_map.mp hV
          simpa [hyeq] using (ContainsBvarsUpTo.fvar : (Ty.fvar y).IsLC)⟩
        hXnodup
        (fun x hx hc => hXσ x hx hc)
        (fun x hx hc => hXYs x hx (Ty.mem_freeVarsList_map_fvar.mp hc))
      calc
        Ty.substFvars (Xs.zip (Ys.map (Ty.fvar ·))) (Ty.openVars Xs σ.body)
            = Ty.openWith (Ys.map (Ty.fvar ·)) σ.body := h3.symm
        _ = Ty.openVars Ys σ.body := (Ty.openVars_eq_openWith (Xs := Ys) (ty := σ.body)).symm]
  rw [hρctx, hsubj, hty] at hren
  exact hren

/-- A `zip`-renaming `Ws ↦ vs` (the `Ws` distinct, all fresh for the `vs`)
    sends the key `fvar w` (with `(w, v)` in the zip) to its partner `v`. -/
private theorem Subst.onTy_zip_fvar_get :
    ∀ {Ws : List Nat} {vs : List Ty} {w : Nat} {v : Ty},
    Ws.Nodup → (∀ k ∈ Ws, ∀ t ∈ vs, k ∉ t.freeVars) → (w, v) ∈ Ws.zip vs →
    Subst.onTy (Ws.zip vs) (Ty.fvar w) = v
  | [], _, _, _, _, _, hmem => by simp at hmem
  | _ :: _, [], _, _, _, _, hmem => by simp at hmem
  | w0 :: Ws', v0 :: vs', w, v, hnd, hfresh, hmem => by
    rw [List.zip_cons_cons, show ((w0, v0) :: Ws'.zip vs') = [(w0, v0)] ++ Ws'.zip vs' from rfl,
        Subst.onTy_append]
    rw [List.nodup_cons] at hnd
    have hstep : Subst.onTy [(w0, v0)] (Ty.fvar w) = Ty.substFvar w0 v0 (Ty.fvar w) := rfl
    rw [hstep]
    rcases List.mem_cons.mp hmem with heq | hmemrest
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
      rw [show Ty.substFvar w v (Ty.fvar w) = v from by simp [Ty.substFvar]]
      exact Ty.substFvars_eq_self_of_no_key (fun p hp hc => by
        have hp1 : p.1 ∈ Ws' := (List.of_mem_zip hp).1
        exact hfresh p.1 (List.mem_cons_of_mem _ hp1) v (List.mem_cons_self ..) hc)
    · have hw : w ∈ Ws' := (List.of_mem_zip hmemrest).1
      have hne : w0 ≠ w := fun h => hnd.1 (h ▸ hw)
      rw [Ty.substFvar_fresh (by simp only [Ty.freeVars, List.mem_singleton]; exact hne)]
      exact Subst.onTy_zip_fvar_get hnd.2
        (fun k hk t ht => hfresh k (List.mem_cons_of_mem _ hk) t (List.mem_cons_of_mem _ ht)) hmemrest

/-- **The `letRec` group residual.** Construct an LC residual `R₀` (fixing `K`,
    agreeing with `S₀` below the frontier `Φ`) that sends the group's fresh
    monotype-var block `[Φ, Φ+n)` to the chosen declarative opened monotypes
    `vs`. A proxy-block `[Φ,Φ+n) ↦ [W,W+n)` (fresh `W`) shields the block from
    `S₀`, then a `[W,W+n) ↦ vs` block realises the targets. (Verbatim port of
    the caac62d theorem; purely structural.) -/
theorem exists_recgroup_residual {Φ n : Nat} {S₀ : Subst} {vs : List Ty} {K : List Nat}
    (hn : vs.length = n)
    (hS₀ : ∀ p ∈ S₀, p.2.IsLC) (hvs : ∀ t ∈ vs, t.IsLC)
    (hKΦ : ∀ k ∈ K, k < Φ)
    (hKfix : ∀ k ∈ K, S₀.onTy (Ty.fvar k) = Ty.fvar k) :
    ∃ R₀ : Subst, (∀ p ∈ R₀, p.2.IsLC) ∧ (∀ k ∈ K, R₀.onTy (Ty.fvar k) = Ty.fvar k) ∧
      (∀ v, v < Φ → R₀.onTy (Ty.fvar v) = S₀.onTy (Ty.fvar v)) ∧
      (((freshVars Φ n).map Ty.fvar).map R₀.onTy = vs) := by
  obtain ⟨W, hWge, hWfresh⟩ := exists_fresh_block
    (S₀.map Prod.fst ++ S₀.flatMap (fun p => p.2.freeVars) ++ Ty.freeVarsList vs) Φ n
  have hW_S₀key : ∀ p ∈ S₀, p.1 < W := fun p hp =>
    hWfresh p.1 (List.mem_append_left _ (List.mem_append_left _ (List.mem_map.mpr ⟨p, hp, rfl⟩)))
  have hW_S₀ran : ∀ p ∈ S₀, ∀ u ∈ p.2.freeVars, u < W := fun p hp u hu =>
    hWfresh u (List.mem_append_left _ (List.mem_append_right _ (List.mem_flatMap.mpr ⟨p, hp, hu⟩)))
  have hW_vs : ∀ t ∈ vs, ∀ u ∈ t.freeVars, u < W := fun t ht u hu =>
    hWfresh u (List.mem_append_right _ (Ty.mem_freeVarsList_of_mem ht hu))
  set proxy : Subst := (List.range n).map (fun i => (Φ + i, Ty.fvar (W + i))) with hproxydef
  set breal : Subst := (freshVars W n).zip vs with hbrealdef
  have hproxy_onTy : ∀ m, proxy.onTy (Ty.fvar m)
      = Ty.fvar (if Φ ≤ m ∧ m < Φ + n then m - Φ + W else m) := by
    intro m; rw [hproxydef]; exact rangeMapList_onTy_fvar Φ W n (Or.inl (by omega)) m
  have hbreal_key : ∀ p ∈ breal, W ≤ p.1 := by
    intro p hp; rw [hbrealdef] at hp; exact freshVars_ge p.1 (List.of_mem_zip hp).1
  have hcomp : ∀ m, (proxy ++ S₀ ++ breal).onTy (Ty.fvar m)
      = breal.onTy (S₀.onTy (proxy.onTy (Ty.fvar m))) := by
    intro m; rw [Subst.onTy_append, Subst.onTy_append]
  refine ⟨proxy ++ S₀ ++ breal, ?_, ?_, ?_, ?_⟩
  · intro p hp
    rcases List.mem_append.mp hp with hp' | hp'
    · rcases List.mem_append.mp hp' with hp'' | hp''
      · rw [hproxydef] at hp''; obtain ⟨i, _, rfl⟩ := List.mem_map.mp hp''
        exact ContainsBvarsUpTo.fvar
      · exact hS₀ p hp''
    · rw [hbrealdef] at hp'; exact hvs p.2 (List.of_mem_zip hp').2
  · intro k hk
    have hklt := hKΦ k hk
    rw [hcomp, hproxy_onTy, if_neg (by omega), hKfix k hk]
    exact Ty.substFvars_eq_self_of_no_key (fun p hp hc => by
      simp only [Ty.freeVars, List.mem_singleton] at hc
      have := hbreal_key p hp; omega)
  · intro v hv
    rw [hcomp, hproxy_onTy, if_neg (by omega)]
    exact Ty.substFvars_eq_self_of_no_key (fun p hp hc => by
      have hpW : W ≤ p.1 := hbreal_key p hp
      have hp_notmem : p.1 ∉ (S₀.onTy (Ty.fvar v)).freeVars :=
        Subst.not_mem_onTy_freeVars
          (fun q hq hcq => by have := hW_S₀ran q hq p.1 hcq; omega)
          (by simp only [Ty.freeVars, List.mem_singleton]; omega)
      exact hp_notmem hc)
  · apply List.ext_getElem
    · simp [hn]
    · intro j h1 h2
      simp only [List.getElem_map]
      have hj : j < n := by simpa using h1
      have hfj : (freshVars Φ n)[j]'(by simp [hj]) = Φ + j := by
        simp only [freshVars, List.getElem_map, List.getElem_range]
      rw [hfj, hcomp, hproxy_onTy, if_pos (by omega)]
      have hWj : Φ + j - Φ + W = W + j := by omega
      rw [hWj]
      have hS₀fix : S₀.onTy (Ty.fvar (W + j)) = Ty.fvar (W + j) :=
        Ty.substFvars_eq_self_of_no_key (fun p hp hc => by
          simp only [Ty.freeVars, List.mem_singleton] at hc
          have := hW_S₀key p hp; omega)
      rw [hS₀fix, hbrealdef]
      apply Subst.onTy_zip_fvar_get freshVars_nodup
        (fun k hk t ht hc => by
          have hkW : W ≤ k := freshVars_ge k hk
          have := hW_vs t ht k hc; omega)
      have hfWj : (freshVars W n)[j]'(by simp [hj]) = W + j := by
        simp only [freshVars, List.getElem_map, List.getElem_range]
      have hmem : ((freshVars W n).zip vs)[j]'(by simp [hn, hj]) = (W + j, vs[j]) := by
        rw [List.getElem_zip, hfWj]
      rw [← hmem]
      exact List.getElem_mem _

/-- **D2 spine** (simultaneous, by size induction over the three mutually
    recursive derivation relations). -/
theorem Infer.principals_mut (n : Nat) :
    (∀ {Φ : Nat} {ctx : Ctx} {e : Expr} {Φ' : Nat} {S : Subst} {τ : Ty},
        (_h : Infer Φ ctx e Φ' S τ) → e.size < n → CtxWF ctx → CtxBelow Φ ctx →
        Infer.Principal _h) ∧
    (∀ {Φ : Nat} {ctx : Ctx} {scrutTy ρ : Ty} {brs : List (MatchPattern × Expr)}
        {Φ' : Nat} {S : Subst},
        (_h : InferBranches Φ ctx scrutTy ρ brs Φ' S) → (hne : brs ≠ []) →
        Expr.sizeBranches brs < n → CtxWF ctx → CtxBelow Φ ctx →
        InferBranches.Principal _h hne) ∧
    (∀ {Φ₀ Φ : Nat} {ctx : Ctx} {bindings : List Expr} {specs : List RecSpec}
        {Φ' : Nat} {S : Subst},
        (_h : InferRecGroup Φ ctx bindings specs Φ' S) → (hle : Φ₀ ≤ Φ) →
        Expr.sizeRecGroup bindings < n → CtxWF ctx → CtxBelow Φ ctx →
        InferRecGroup.Principal _h hle) := by
  induction n with
  | zero =>
    refine ⟨?_, ?_, ?_⟩
    · intro Φ ctx e Φ' S τ h hn _ _; exact absurd hn (Nat.not_lt_zero _)
    · intro Φ ctx scrutTy ρ brs Φ' S h hne hn _ _
      exact absurd hn (Nat.not_lt_zero _)
    · intro Φ₀ Φ ctx bindings specs Φ' S h hle hn _ _
      exact absurd hn (Nat.not_lt_zero _)
  | succ n ih =>
    refine ⟨?_, ?_, ?_⟩
    · -- Infer tier (D2 spine; one handler per constructor)
      intro Φ ctx e Φ' S τ h _hn hwf hbelow
      cases h with
      | primLitUnit =>
        intro _ _ S₀ τe K hS₀ hKΦ hKe hKfix hty
        cases hty with
        | primLitUnit =>
          refine ⟨S₀, hS₀, ?_, hKfix, fun v _ => Eq.refl _⟩
          show  (.prim .unit) =  (Subst.onTy S₀ (.prim .unit))
          simp [Subst.onTy_prim]
      | primLitInt =>
        intro _ _ S₀ τe K hS₀ hKΦ hKe hKfix hty
        cases hty with
        | primLitInt =>
          refine ⟨S₀, hS₀, ?_, hKfix, fun v _ => Eq.refl _⟩
          show  (.prim .int) =  (Subst.onTy S₀ (.prim .int))
          simp [Subst.onTy_prim]
      | primLitNat =>
        intro _ _ S₀ τe K hS₀ hKΦ hKe hKfix hty
        cases hty with
        | primLitNat =>
          refine ⟨S₀, hS₀, ?_, hKfix, fun v _ => Eq.refl _⟩
          show  (.prim .nat) =  (Subst.onTy S₀ (.prim .nat))
          simp [Subst.onTy_prim]
      | primLitChar =>
        intro _ _ S₀ τe K hS₀ hKΦ hKe hKfix hty
        cases hty with
        | primLitChar =>
          refine ⟨S₀, hS₀, ?_, hKfix, fun v _ => Eq.refl _⟩
          show  (.prim .char) =  (Subst.onTy S₀ (.prim .char))
          simp [Subst.onTy_prim]
      | primBinOpIntAdd =>
        intro _ _ S₀ τe K hS₀ hKΦ hKe hKfix hty
        cases hty with
        | primBinOpIntAdd =>
          refine ⟨S₀, hS₀, ?_, hKfix, fun v _ => Eq.refl _⟩
          show  ((.arrow (.prim .int) (.arrow (.prim .int) (.prim .int)))) =  (Subst.onTy S₀ ((.arrow (.prim .int) (.arrow (.prim .int) (.prim .int)))))
          simp [Subst.onTy_arrow]
      | primBinOpIntSub =>
        intro _ _ S₀ τe K hS₀ hKΦ hKe hKfix hty
        cases hty with
        | primBinOpIntSub =>
          refine ⟨S₀, hS₀, ?_, hKfix, fun v _ => Eq.refl _⟩
          show  ((.arrow (.prim .int) (.arrow (.prim .int) (.prim .int)))) =  (Subst.onTy S₀ ((.arrow (.prim .int) (.arrow (.prim .int) (.prim .int)))))
          simp [Subst.onTy_arrow]
      | primBinOpIntLt _ _ _ _ =>
        intro _ _ S₀ τe K hS₀ hKΦ hKe hKfix hty
        cases hty with
        | primBinOpIntLt _ _ =>
          refine ⟨S₀, hS₀, ?_, hKfix, fun v _ => Eq.refl _⟩
          show  ((.arrow (.prim .int) (.arrow (.prim .int)
            (.customTy ⟨"Bool"⟩ [])))) =  (Subst.onTy S₀
            (.arrow (.prim .int) (.arrow (.prim .int) (.customTy ⟨"Bool"⟩ []))))
          simp [Subst.onTy_arrow, Subst.onTy_customTy]
      | primBinOpCharLt _ _ _ _ =>
        intro _ _ S₀ τe K hS₀ hKΦ hKe hKfix hty
        cases hty with
        | primBinOpCharLt _ _ =>
          refine ⟨S₀, hS₀, ?_, hKfix, fun v _ => Eq.refl _⟩
          show  ((.arrow (.prim .char) (.arrow (.prim .char)
            (.customTy ⟨"Bool"⟩ [])))) =  (Subst.onTy S₀
            (.arrow (.prim .char) (.arrow (.prim .char) (.customTy ⟨"Bool"⟩ []))))
          simp [Subst.onTy_arrow, Subst.onTy_customTy]
      | @var Φ ctx i polyTy hlook =>
        exact fun hwf hbelow S₀ τe K hS₀ hKΦ hKe hKfix hty => by
          -- STEP 0: the looked-up scheme `polyTy` from the raw `ctx` (`hlook`).
          have hmem : polyTy ∈ ctx.env := List.mem_of_getElem? hlook
          have hwfpoly : ContainsBvarsUpTo polyTy.paramCount polyTy.body := hwf polyTy hmem
          -- STEP 1: fresh block start `W` above everything relevant.
          obtain ⟨W, hd, hWfresh⟩ := exists_fresh_block
            (S₀.map Prod.fst ++ S₀.flatMap (fun p => p.2.freeVars) ++ τe.freeVars) Φ
            polyTy.paramCount
          have hτeW : ∀ v ∈ τe.freeVars, ¬ (W ≤ v ∧ v < W + polyTy.paramCount) := by
            intro v hv hc; have := hWfresh v (List.mem_append_right _ hv); omega
          have hSrange_lt : ∀ p ∈ S₀, ∀ v ∈ p.2.freeVars, v < W := fun p hp v hv =>
            hWfresh v (List.mem_append_left _
              (List.mem_append_right _ (List.mem_flatMap.mpr ⟨p, hp, hv⟩)))
          have hSkey_lt : ∀ p ∈ S₀, p.1 < W := fun p hp =>
            hWfresh p.1 (List.mem_append_left _
              (List.mem_append_left _ (List.mem_map.mpr ⟨p, hp, rfl⟩)))
          have hS₀belowW : ∀ p ∈ S₀, Ty.BelowFvars W p.2 :=
            fun p hp => Ty.BelowFvars.of_freeVars_lt (fun v hv => hSrange_lt p hp v hv)
          have hWblock_of_belowW : ∀ {t : Ty}, Ty.BelowFvars W t →
              ∀ v ∈ t.freeVars, ¬ (W ≤ v ∧ v < W + polyTy.paramCount) :=
            fun {t} ht v hv => by have := ht.mem_lt v hv; omega
          have finj : Function.Injective (blockSwap Φ W polyTy.paramCount) := blockSwap_injective hd
          have hffix : ∀ v, v < Φ → blockSwap Φ W polyTy.paramCount v = v :=
            fun v hv => blockSwap_lt (by omega) hv
          -- STEP 2: rename the declarative typing by the block-swap (erased world).
          have hren := TypeOfHM.onSubst_fixed (blockList Φ W polyTy.paramCount)
            (blockList_lc Φ W polyTy.paramCount)
            (Expr.substTyFvars_eq_self_of_tyFreeVars_nil _ rfl) hty
          have henvpt : ∀ M ∈ ctx.env,
              (blockList Φ W polyTy.paramCount).onPolyTy
                  ( (S₀.onPolyTy M))
              =
                  (Subst.onPolyTy (Subst.conj (blockSwap Φ W polyTy.paramCount) S₀) M) := by
            intro M hM
            have hrenM : Ty.rename (blockSwap Φ W polyTy.paramCount) M.body = M.body :=
              Ty.rename_eq_self (fun v hv => hffix v ((hbelow M hM).mem_lt v hv))
            have hwbl : ∀ v ∈ ( (S₀.onTy M.body)).freeVars,
                ¬ (W ≤ v ∧ v < W + polyTy.paramCount) := fun v hv =>
              hWblock_of_belowW (Subst.onTy_belowFvars hS₀belowW
                ((hbelow M hM).mono (by omega))) v
                (hv)
            simp only [  Subst.onPolyTy]
            rw [blockList_onTy hd hwbl]
            conv_rhs =>
              rw [← hrenM, Subst.onTy_conj finj]
          have hctxeq : (blockList Φ W polyTy.paramCount).onCtx ((S₀.onCtx ctx))
              = ((Subst.conj (blockSwap Φ W polyTy.paramCount) S₀).onCtx ctx) := by
            show Ctx.mk
                (Subst.onEnv (blockList Φ W polyTy.paramCount)
                  ( (Subst.onEnv S₀ ctx.env)))
                ( ctx.ctors)
              = Ctx.mk
                (
                  (Subst.onEnv (Subst.conj (blockSwap Φ W polyTy.paramCount) S₀) ctx.env))
                ( ctx.ctors)
            simp only [Ctx.mk.injEq, and_true]
            simp only [Subst.onEnv,  List.map_map, List.map_map]
            exact List.map_congr_left henvpt
          have htyeq : (blockList Φ W polyTy.paramCount).onTy τe
              = Ty.rename (blockSwap Φ W polyTy.paramCount) τe := blockList_onTy hd hτeW
          have hren2 : TypeOfHM
              (((Subst.conj (blockSwap Φ W polyTy.paramCount) S₀).onCtx ctx))
              (.var i) (Ty.rename (blockSwap Φ W polyTy.paramCount) τe) := by
            rw [hctxeq, htyeq] at hren; exact hren
          -- STEP 3: invert renamed typing — the erased scheme comes out directly.
          cases hren2 with
          | @var _ σE tyArgs2 _ _ hlook2 htyargs2 hinst2 =>
            have hElookup :
                (((Subst.conj (blockSwap Φ W polyTy.paramCount) S₀).onCtx ctx)).env[i]?
                  = some (
                    ((Subst.conj (blockSwap Φ W polyTy.paramCount) S₀).onPolyTy polyTy)) := by
              simp only [Subst.onCtx, Subst.onEnv,
                List.getElem?_map, hlook, Option.map_some]
            have hσE : σE =
                ((Subst.conj (blockSwap Φ W polyTy.paramCount) S₀).onPolyTy polyTy) :=
              Option.some.inj (hlook2.symm.trans hElookup)
            subst hσE
            simp only [Subst.onPolyTy] at hinst2
            let J := Ty.rename (blockSwap Φ W polyTy.paramCount) τe
            have hinstJ : InstantiatesBy tyArgs2
                ((Subst.conj (blockSwap Φ W polyTy.paramCount) S₀).onTy polyTy.body) J := by
              simpa [J] using hinst2
            have hJagree : J = Ty.rename (blockSwap Φ W polyTy.paramCount) τe := rfl
            -- STEP 4: assemble.
            have hdomfresh : ∀ p ∈ Subst.conj (blockSwap Φ W polyTy.paramCount) S₀,
                p.1 ∉ freshVars Φ polyTy.paramCount := by
              intro p hp hmemf
              simp only [Subst.conj, List.mem_map] at hp
              obtain ⟨q, hq, rfl⟩ := hp
              have hq1 : q.1 < W := hSkey_lt q hq
              have hge := freshVars_ge _ hmemf
              have hlt := freshVars_lt _ hmemf
              simp only [blockSwap] at hge hlt
              split_ifs at hge hlt <;> omega
            have hbv2 : ContainsBvarsUpTo (freshVars Φ polyTy.paramCount).length
                ((Subst.conj (blockSwap Φ W polyTy.paramCount) S₀).onTy polyTy.body) := by
              rw [freshVars_length]
              exact Subst.onTy_containsBvars (Subst.conj_lc hS₀) hwfpoly
            have hXfresh2 : ∀ x ∈ freshVars Φ polyTy.paramCount,
                x ∉ (Ty.rename (blockSwap Φ W polyTy.paramCount) τe).freeVars :=
              fun x hx => blockSwap_rename_not_mem hd hτeW x (freshVars_ge x hx)
                (freshVars_lt x hx)
            have hτeE : ∀ v ∈ ( τe).freeVars,
                ¬ (W ≤ v ∧ v < W + polyTy.paramCount) :=
              fun v hv => hτeW v (hv)
            have hXfreshJ : ∀ x ∈ freshVars Φ polyTy.paramCount, x ∉ J.freeVars := by
              simpa [J] using hXfresh2
            have hR'eq : Subst.onTy
                (Subst.conj (blockSwap Φ W polyTy.paramCount) S₀ ++
                  (freshVars Φ polyTy.paramCount).zip tyArgs2)
                (polyTy.openVars (freshVars Φ polyTy.paramCount))
                = J := by
              rw [Subst.onTy_append]
              simp only [PolyTy.openVars]
              rw [Subst.onTy_openVars (Subst.conj_lc hS₀) hdomfresh]
              exact InstantiatesBy.onTy_openVars_zip hinstJ hbv2 freshVars_nodup hXfreshJ
            have hagree : Subst.AgreesBelow Φ S₀
                (([] : Subst) ++ ((Subst.conj (blockSwap Φ W polyTy.paramCount) S₀ ++
                  (freshVars Φ polyTy.paramCount).zip tyArgs2) ++
                  blockListBack Φ W polyTy.paramCount)) := by
              intro v hv
              have hbelowfv : Ty.BelowFvars W (S₀.onTy (.fvar v)) :=
                Subst.onTy_belowFvars hS₀belowW (Ty.BelowFvars.fvar (show v < W by omega))
              have hconjv : Subst.onTy (Subst.conj (blockSwap Φ W polyTy.paramCount) S₀)
                  (.fvar v) = Ty.rename (blockSwap Φ W polyTy.paramCount) (S₀.onTy (.fvar v)) := by
                conv_lhs => rw [show (Ty.fvar v) = Ty.rename (blockSwap Φ W polyTy.paramCount)
                  (Ty.fvar v) by rw [Ty.rename_fvar, hffix v hv]]
                rw [Subst.onTy_conj finj]
              have hzipnoop : Subst.onTy ((freshVars Φ polyTy.paramCount).zip tyArgs2)
                  (Ty.rename (blockSwap Φ W polyTy.paramCount) (S₀.onTy (.fvar v)))
                  = Ty.rename (blockSwap Φ W polyTy.paramCount) (S₀.onTy (.fvar v)) :=
                Ty.substFvars_eq_self_of_no_key (fun p hp =>
                  blockSwap_rename_not_mem hd (hWblock_of_belowW hbelowfv) p.1
                    (freshVars_ge p.1 (List.of_mem_zip hp).1)
                    (freshVars_lt p.1 (List.of_mem_zip hp).1))
              have hback : Subst.onTy (blockListBack Φ W polyTy.paramCount)
                  (Ty.rename (blockSwap Φ W polyTy.paramCount) (S₀.onTy (.fvar v)))
                  = S₀.onTy (.fvar v) :=
                blockListBack_onTy_rename hd (hWblock_of_belowW hbelowfv)
              rw [List.nil_append, Subst.onTy_append, Subst.onTy_append, hconjv, hzipnoop, hback]
            refine ⟨(Subst.conj (blockSwap Φ W polyTy.paramCount) S₀ ++
                (freshVars Φ polyTy.paramCount).zip tyArgs2) ++ blockListBack Φ W polyTy.paramCount,
              ?_, ?_, ?_, hagree⟩
            · intro p hp
              rw [List.mem_append] at hp
              rcases hp with hp | hp
              · rw [List.mem_append] at hp
                rcases hp with hp | hp
                · exact Subst.conj_lc hS₀ p hp
                · exact htyargs2 p.2 (List.of_mem_zip hp).2
              · exact blockListBack_lc Φ W polyTy.paramCount p hp
            · rw [Subst.onTy_append, hR'eq]
              show  τe
                  =  (Subst.onTy (blockListBack Φ W polyTy.paramCount) J)
              rw [hJagree,
                blockListBack_onTy_rename hd hτeE]
            · intro k hk
              have hkΦ : k < Φ := hKΦ k hk
              have hbelowfv : Ty.BelowFvars W (S₀.onTy (.fvar k)) :=
                Subst.onTy_belowFvars hS₀belowW (Ty.BelowFvars.fvar (show k < W by omega))
              have hconjv : Subst.onTy (Subst.conj (blockSwap Φ W polyTy.paramCount) S₀)
                  (.fvar k) = Ty.rename (blockSwap Φ W polyTy.paramCount) (S₀.onTy (.fvar k)) := by
                conv_lhs => rw [show (Ty.fvar k) = Ty.rename (blockSwap Φ W polyTy.paramCount)
                  (Ty.fvar k) by rw [Ty.rename_fvar, hffix k (hKΦ k hk)]]
                rw [Subst.onTy_conj finj]
              have hzipnoop : Subst.onTy ((freshVars Φ polyTy.paramCount).zip tyArgs2)
                  (Ty.rename (blockSwap Φ W polyTy.paramCount) (S₀.onTy (.fvar k)))
                  = Ty.rename (blockSwap Φ W polyTy.paramCount) (S₀.onTy (.fvar k)) :=
                Ty.substFvars_eq_self_of_no_key (fun p hp =>
                  blockSwap_rename_not_mem hd (hWblock_of_belowW hbelowfv) p.1
                    (freshVars_ge p.1 (List.of_mem_zip hp).1)
                    (freshVars_lt p.1 (List.of_mem_zip hp).1))
              have hback : Subst.onTy (blockListBack Φ W polyTy.paramCount)
                  (Ty.rename (blockSwap Φ W polyTy.paramCount) (S₀.onTy (.fvar k)))
                  = S₀.onTy (.fvar k) :=
                blockListBack_onTy_rename hd (hWblock_of_belowW hbelowfv)
              rw [Subst.onTy_append, Subst.onTy_append, hconjv, hzipnoop, hback]
              exact hKfix k hk
      | @ctor Φ ctx name ctorData hlook =>
        exact fun hwf hbelow S₀ τe K hS₀ hKΦ hKe hKfix hty => by
          let ctor := ctorData
          change LookupList.get? ctx.ctors name = some ctor at hlook
          -- STEP 0: the ctor's scheme `ctor.toTy` is always well-formed (no env
          -- lookup needed — ctors live outside the env).
          have hbv : ContainsBvarsUpTo ctor.paramCount ctor.toTy.body := Ctor.toTy_wf ctor
          -- STEP 1: fresh block start `W` above everything relevant.
          obtain ⟨W, hd, hWfresh⟩ := exists_fresh_block
            (S₀.map Prod.fst ++ S₀.flatMap (fun p => p.2.freeVars) ++ τe.freeVars) Φ
            ctor.paramCount
          have hτeW : ∀ v ∈ τe.freeVars, ¬ (W ≤ v ∧ v < W + ctor.paramCount) := by
            intro v hv hc; have := hWfresh v (List.mem_append_right _ hv); omega
          have hSrange_lt : ∀ p ∈ S₀, ∀ v ∈ p.2.freeVars, v < W := fun p hp v hv =>
            hWfresh v (List.mem_append_left _
              (List.mem_append_right _ (List.mem_flatMap.mpr ⟨p, hp, hv⟩)))
          have hSkey_lt : ∀ p ∈ S₀, p.1 < W := fun p hp =>
            hWfresh p.1 (List.mem_append_left _
              (List.mem_append_left _ (List.mem_map.mpr ⟨p, hp, rfl⟩)))
          have hS₀belowW : ∀ p ∈ S₀, Ty.BelowFvars W p.2 :=
            fun p hp => Ty.BelowFvars.of_freeVars_lt (fun v hv => hSrange_lt p hp v hv)
          have hWblock_of_belowW : ∀ {t : Ty}, Ty.BelowFvars W t →
              ∀ v ∈ t.freeVars, ¬ (W ≤ v ∧ v < W + ctor.paramCount) :=
            fun {t} ht v hv => by have := ht.mem_lt v hv; omega
          have finj : Function.Injective (blockSwap Φ W ctor.paramCount) := blockSwap_injective hd
          have hffix : ∀ v, v < Φ → blockSwap Φ W ctor.paramCount v = v :=
            fun v hv => blockSwap_lt (by omega) hv
          -- STEP 2: rename the declarative typing by the block-swap (erased world).
          have hren := TypeOfHM.onSubst_fixed (blockList Φ W ctor.paramCount)
            (blockList_lc Φ W ctor.paramCount)
            (Expr.substTyFvars_eq_self_of_tyFreeVars_nil _ rfl) hty
          have henvpt : ∀ M ∈ ctx.env,
              (blockList Φ W ctor.paramCount).onPolyTy
                  ( (S₀.onPolyTy M))
              =
                  (Subst.onPolyTy (Subst.conj (blockSwap Φ W ctor.paramCount) S₀) M) := by
            intro M hM
            have hrenM : Ty.rename (blockSwap Φ W ctor.paramCount) M.body = M.body :=
              Ty.rename_eq_self (fun v hv => hffix v ((hbelow M hM).mem_lt v hv))
            have hwbl : ∀ v ∈ ( (S₀.onTy M.body)).freeVars,
                ¬ (W ≤ v ∧ v < W + ctor.paramCount) := fun v hv =>
              hWblock_of_belowW (Subst.onTy_belowFvars hS₀belowW
                ((hbelow M hM).mono (by omega))) v
                (hv)
            simp only [  Subst.onPolyTy]
            rw [blockList_onTy hd hwbl]
            conv_rhs =>
              rw [← hrenM, Subst.onTy_conj finj]
          have hctxeq : (blockList Φ W ctor.paramCount).onCtx ((S₀.onCtx ctx))
              = ((Subst.conj (blockSwap Φ W ctor.paramCount) S₀).onCtx ctx) := by
            show Ctx.mk
                (Subst.onEnv (blockList Φ W ctor.paramCount)
                  ( (Subst.onEnv S₀ ctx.env)))
                ( ctx.ctors)
              = Ctx.mk
                (
                  (Subst.onEnv (Subst.conj (blockSwap Φ W ctor.paramCount) S₀) ctx.env))
                ( ctx.ctors)
            simp only [Ctx.mk.injEq, and_true]
            simp only [Subst.onEnv,  List.map_map, List.map_map]
            exact List.map_congr_left henvpt
          have htyeq : (blockList Φ W ctor.paramCount).onTy τe
              = Ty.rename (blockSwap Φ W ctor.paramCount) τe := blockList_onTy hd hτeW
          have hren2 : TypeOfHM
              (((Subst.conj (blockSwap Φ W ctor.paramCount) S₀).onCtx ctx))
              (.ctor name) (Ty.rename (blockSwap Φ W ctor.paramCount) τe) := by
            rw [hctxeq, htyeq] at hren; exact hren
          -- STEP 3: invert renamed typing (`S₀.onCtx` leaves `ctors` untouched;
          -- erasure maps the looked-up ctor to ` ctor`).
          cases hren2 with
          | @ctor _ ctorE tyArgs2 _ _ hlook2 htyargs2 hinst2 =>
            have hElookup :
                LookupList.get? ((Subst.conj (blockSwap Φ W ctor.paramCount) S₀).onCtx
                  ctx).ctors name = some ctor := by
              simpa [Subst.onCtx] using hlook
            have hctorE : ctorE =  ctor :=
              Option.some.inj (hlook2.symm.trans hElookup)
            subst hctorE
            have hinst2' : InstantiatesBy tyArgs2 ( ctor.toTy.body)
                (Ty.rename (blockSwap Φ W ctor.paramCount) τe) := by
              simpa [PolyTy.InstantiatesTo] using hinst2
            clear hinst2
            let J := Ty.rename (blockSwap Φ W ctor.paramCount) τe
            have hinstJ : InstantiatesBy tyArgs2 ctor.toTy.body J := by
              simpa [J] using hinst2'
            have hJagree : J = Ty.rename (blockSwap Φ W ctor.paramCount) τe := rfl
            -- STEP 4: assemble. The ctor scheme is closed, so the conjugated
            -- substitution leaves `ctor.toTy.body` untouched.
            have htoTyNoSubst : (Subst.conj (blockSwap Φ W ctor.paramCount) S₀).onTy
                ctor.toTy.body = ctor.toTy.body :=
              Ty.substFvars_eq_self_of_no_key (fun p hp =>
                NoFreeVars.not_mem_freeVars (Ctor.toTy_body_noFreeVars ctor) p.1)
            have hdomfresh : ∀ p ∈ Subst.conj (blockSwap Φ W ctor.paramCount) S₀,
                p.1 ∉ freshVars Φ ctor.paramCount := by
              intro p hp hmemf
              simp only [Subst.conj, List.mem_map] at hp
              obtain ⟨q, hq, rfl⟩ := hp
              have hq1 : q.1 < W := hSkey_lt q hq
              have hge := freshVars_ge _ hmemf
              have hlt := freshVars_lt _ hmemf
              simp only [blockSwap] at hge hlt
              split_ifs at hge hlt <;> omega
            have hbv2 : ContainsBvarsUpTo (freshVars Φ ctor.paramCount).length
                ctor.toTy.body := by
              rw [freshVars_length]
              exact hbv
            have hXfresh2 : ∀ x ∈ freshVars Φ ctor.paramCount,
                x ∉ (Ty.rename (blockSwap Φ W ctor.paramCount) τe).freeVars :=
              fun x hx => blockSwap_rename_not_mem hd hτeW x (freshVars_ge x hx)
                (freshVars_lt x hx)
            have hτeE : ∀ v ∈ ( τe).freeVars,
                ¬ (W ≤ v ∧ v < W + ctor.paramCount) :=
              fun v hv => hτeW v (hv)
            have hXfreshJ : ∀ x ∈ freshVars Φ ctor.paramCount, x ∉ J.freeVars := by
              simpa [J] using hXfresh2
            have hR'eq : Subst.onTy
                (Subst.conj (blockSwap Φ W ctor.paramCount) S₀ ++
                  (freshVars Φ ctor.paramCount).zip tyArgs2)
                (ctor.toTy.openVars (freshVars Φ ctor.paramCount))
                = J := by
              rw [Subst.onTy_append]
              simp only [PolyTy.openVars]
              rw [Subst.onTy_openVars (Subst.conj_lc hS₀) hdomfresh, htoTyNoSubst]
              exact InstantiatesBy.onTy_openVars_zip hinstJ hbv2 freshVars_nodup hXfreshJ
            have hagree : Subst.AgreesBelow Φ S₀
                (([] : Subst) ++ ((Subst.conj (blockSwap Φ W ctor.paramCount) S₀ ++
                  (freshVars Φ ctor.paramCount).zip tyArgs2) ++
                  blockListBack Φ W ctor.paramCount)) := by
              intro v hv
              have hbelowfv : Ty.BelowFvars W (S₀.onTy (.fvar v)) :=
                Subst.onTy_belowFvars hS₀belowW (Ty.BelowFvars.fvar (show v < W by omega))
              have hconjv : Subst.onTy (Subst.conj (blockSwap Φ W ctor.paramCount) S₀)
                  (.fvar v) = Ty.rename (blockSwap Φ W ctor.paramCount) (S₀.onTy (.fvar v)) := by
                conv_lhs => rw [show (Ty.fvar v) = Ty.rename (blockSwap Φ W ctor.paramCount)
                  (Ty.fvar v) by rw [Ty.rename_fvar, hffix v hv]]
                rw [Subst.onTy_conj finj]
              have hzipnoop : Subst.onTy ((freshVars Φ ctor.paramCount).zip tyArgs2)
                  (Ty.rename (blockSwap Φ W ctor.paramCount) (S₀.onTy (.fvar v)))
                  = Ty.rename (blockSwap Φ W ctor.paramCount) (S₀.onTy (.fvar v)) :=
                Ty.substFvars_eq_self_of_no_key (fun p hp =>
                  blockSwap_rename_not_mem hd (hWblock_of_belowW hbelowfv) p.1
                    (freshVars_ge p.1 (List.of_mem_zip hp).1)
                    (freshVars_lt p.1 (List.of_mem_zip hp).1))
              have hback : Subst.onTy (blockListBack Φ W ctor.paramCount)
                  (Ty.rename (blockSwap Φ W ctor.paramCount) (S₀.onTy (.fvar v)))
                  = S₀.onTy (.fvar v) :=
                blockListBack_onTy_rename hd (hWblock_of_belowW hbelowfv)
              rw [List.nil_append, Subst.onTy_append, Subst.onTy_append, hconjv, hzipnoop, hback]
            refine ⟨(Subst.conj (blockSwap Φ W ctor.paramCount) S₀ ++
                (freshVars Φ ctor.paramCount).zip tyArgs2) ++ blockListBack Φ W ctor.paramCount,
              ?_, ?_, ?_, hagree⟩
            · intro p hp
              rw [List.mem_append] at hp
              rcases hp with hp | hp
              · rw [List.mem_append] at hp
                rcases hp with hp | hp
                · exact Subst.conj_lc hS₀ p hp
                · exact htyargs2 p.2 (List.of_mem_zip hp).2
              · exact blockListBack_lc Φ W ctor.paramCount p hp
            · rw [Subst.onTy_append, hR'eq]
              show  τe
                  =  (Subst.onTy (blockListBack Φ W ctor.paramCount) J)
              rw [hJagree,
                blockListBack_onTy_rename hd hτeE]
            · intro k hk
              have hkΦ : k < Φ := hKΦ k hk
              have hbelowfv : Ty.BelowFvars W (S₀.onTy (.fvar k)) :=
                Subst.onTy_belowFvars hS₀belowW (Ty.BelowFvars.fvar (show k < W by omega))
              have hconjv : Subst.onTy (Subst.conj (blockSwap Φ W ctor.paramCount) S₀)
                  (.fvar k) = Ty.rename (blockSwap Φ W ctor.paramCount) (S₀.onTy (.fvar k)) := by
                conv_lhs => rw [show (Ty.fvar k) = Ty.rename (blockSwap Φ W ctor.paramCount)
                  (Ty.fvar k) by rw [Ty.rename_fvar, hffix k (hKΦ k hk)]]
                rw [Subst.onTy_conj finj]
              have hzipnoop : Subst.onTy ((freshVars Φ ctor.paramCount).zip tyArgs2)
                  (Ty.rename (blockSwap Φ W ctor.paramCount) (S₀.onTy (.fvar k)))
                  = Ty.rename (blockSwap Φ W ctor.paramCount) (S₀.onTy (.fvar k)) :=
                Ty.substFvars_eq_self_of_no_key (fun p hp =>
                  blockSwap_rename_not_mem hd (hWblock_of_belowW hbelowfv) p.1
                    (freshVars_ge p.1 (List.of_mem_zip hp).1)
                    (freshVars_lt p.1 (List.of_mem_zip hp).1))
              have hback : Subst.onTy (blockListBack Φ W ctor.paramCount)
                  (Ty.rename (blockSwap Φ W ctor.paramCount) (S₀.onTy (.fvar k)))
                  = S₀.onTy (.fvar k) :=
                blockListBack_onTy_rename hd (hWblock_of_belowW hbelowfv)
              rw [Subst.onTy_append, Subst.onTy_append, hconjv, hzipnoop, hback]
              exact hKfix k hk
      | @lambda Φ ctx ann paramTy body Φ₀ Φ' S τb hseed hbody =>
        exact fun hwf hbelow S₀ τe K hS₀ hKΦ hKe hKfix hty => by
          cases hty with
          | lambda hpc hann heq hbodyD =>
            subst heq
            rename_i bodyTy paramTyD
            have hsize : body.size < n := by
              have := _hn
              simp [Expr.size] at this
              omega
            cases hseed with
            | none =>
              -- STEP 0: fresh names W (swap partner) and c (swap intermediate)
              obtain ⟨W, c, hΦW, hΦc, hWc, hWav, hcav⟩ := exists_fresh_two_ge Φ
                ([Φ] ++ S₀.map Prod.fst ++ S₀.flatMap (fun p => p.2.freeVars)
                  ++ paramTyD.freeVars ++ bodyTy.freeVars)
              simp only [List.mem_append, List.mem_singleton, List.mem_map, List.mem_flatMap]
                at hWav hcav
              push_neg at hWav hcav
              obtain ⟨⟨⟨⟨hWΦ, hWkey⟩, hWrange⟩, hWparam⟩, hWbody⟩ := hWav
              obtain ⟨⟨⟨⟨hcΦ, hckey⟩, hcrange⟩, hcparam⟩, hcbody⟩ := hcav
              have finj : Function.Injective (swapNat Φ W) := swapNat_injective Φ W
              have hfix : ∀ v, v < Φ → swapNat Φ W v = v := fun v hv =>
                swapNat_other (by omega) (by omega)
              have hWonTy : ∀ {τ : Ty}, W ∉ τ.freeVars → W ∉ (S₀.onTy τ).freeVars :=
                fun h => Subst.not_mem_onTy_freeVars hWrange h
              have herase_swap : ∀ {Y : Ty}, c ∉ Y.freeVars →
                   (Ty.rename (swapNat Φ W) Y)
                    = Ty.rename (swapNat Φ W) ( Y) := by
                intro Y _
                rfl
              have hconΦ : ∀ p ∈ Subst.conj (swapNat Φ W) S₀, p.1 ≠ Φ := by
                intro p hp
                simp only [Subst.conj, List.mem_map] at hp
                obtain ⟨q, hq, rfl⟩ := hp
                intro hc
                apply hWkey q hq
                have hc' : swapNat Φ W q.1 = Φ := hc
                simp only [swapNat] at hc'
                split_ifs at hc' <;> omega
              have hSconjΦ : (Subst.conj (swapNat Φ W) S₀).onTy (.fvar Φ) = .fvar Φ := by
                apply Ty.substFvars_eq_self_of_no_key
                intro p hp hc
                simp only [Ty.freeVars, List.mem_singleton] at hc
                exact hconΦ p hp hc
              -- STEP 1: rename the declarative body derivation (raw extended base),
              -- then move to the substituted context of the IH.
              have hbodyK : ∀ y ∈ body.tyFreeVars, y ∈ K := by
                simpa [Expr.tyFreeVars] using hKe
              have hbodyKe : ∀ y ∈ body.tyFreeVars, y ∈ K := fun y hy =>
                hbodyK y hy
              have hbodyfixE : body.substTyFvars (swapSubst Φ W c)
                  = body :=
                Expr.substTyFvars_eq_self_of_not_mem_tyFreeVars (fun p hp hc => by
                  have hpΦ : Φ ≤ p.1 := by
                    simp only [swapSubst, List.mem_cons, List.not_mem_nil, or_false] at hp
                    obtain rfl | rfl | rfl := hp <;> omega
                  have := hKΦ p.1 (hbodyKe p.1 hc)
                  omega)
              have hrenE := TypeOfHM.onSubst_fixed (swapSubst Φ W c)
                (swapSubst_lc Φ W c) hbodyfixE hbodyD
              -- erased twin of the old context equality
              have henvpt : ∀ M ∈ ctx.env,
                   (Subst.onPolyTy (swapSubst Φ W c)
                      ( (Subst.onPolyTy S₀ M)))
                  =  (Subst.onPolyTy
                      (Subst.conj (swapNat Φ W) S₀
                        ++ [(Φ, Ty.rename (swapNat Φ W) paramTyD)]) M) := by
                intro M hM
                have hMbelow : ∀ v ∈ M.body.freeVars, v < Φ := (hbelow M hM).mem_lt
                have hrenM : Ty.rename (swapNat Φ W) M.body = M.body :=
                  Ty.rename_eq_self (fun v hv => hfix v (hMbelow v hv))
                have hΦnotin : Φ ∉ (Ty.rename (swapNat Φ W) (S₀.onTy M.body)).freeVars :=
                  Ty.rename_swap_not_mem_left (hWonTy (τ := M.body)
                    (fun hv => by have := hMbelow _ hv; omega))
                have hΦE : Φ ∉ (
                    (Ty.rename (swapNat Φ W) (S₀.onTy M.body))).freeVars := fun hc =>
                  hΦnotin (hc)
                have hcrangeE : c ∉ ( (S₀.onTy M.body)).freeVars := fun hc =>
                  Subst.not_mem_onTy_freeVars hcrange
                    (fun hv => by have := hMbelow _ hv; omega)
                    (hc)
                simp only [  Subst.onPolyTy]
                rw [show (swapSubst Φ W c).onTy ( (S₀.onTy M.body))
                      = Ty.rename (swapNat Φ W) ( (S₀.onTy M.body)) from
                    swapSubst_onTy (Ne.symm hWΦ) (Ne.symm hcΦ) hWc hcrangeE]
                conv_rhs =>
                  rw [← hrenM,
                    Subst.onTy_append (Subst.conj (swapNat Φ W) S₀)
                      [(Φ, Ty.rename (swapNat Φ W) paramTyD)],
                    Subst.onTy_conj finj]
                  dsimp [Subst.onTy, Ty.substFvars]
                exact congrArg (fun b : Ty => (⟨M.paramCount, b⟩ : PolyTy))
                  (Ty.substFvar_fresh hΦE).symm
              have hctxeq : ((swapSubst Φ W c).onCtx
                    { (S₀.onCtx ctx) with
                      env := PolyTy.mkTrivial paramTyD :: ((S₀.onCtx ctx)).env })
                  = ((Subst.conj (swapNat Φ W) S₀
                      ++ [(Φ, Ty.rename (swapNat Φ W) paramTyD)]).onCtx
                    { ctx with env := PolyTy.mkTrivial (.fvar Φ) :: ctx.env }) := by
                dsimp only [Subst.onCtx]
                show Ctx.mk
                    ( (Subst.onEnv (swapSubst Φ W c)
                      (PolyTy.mkTrivial paramTyD ::  (Subst.onEnv S₀ ctx.env))))
                    ( ( ctx.ctors))
                  = Ctx.mk
                    ( (Subst.onEnv
                      (Subst.conj (swapNat Φ W) S₀ ++ [(Φ, Ty.rename (swapNat Φ W) paramTyD)])
                      (PolyTy.mkTrivial (.fvar Φ) :: ctx.env)))
                    ( ctx.ctors)
                simp only [Ctx.mk.injEq, true_and]
                constructor
                · -- head: the pinned scheme's erased value is the same on both sides
                  have hh :  (Subst.onPolyTy (swapSubst Φ W c)
                        (PolyTy.mkTrivial paramTyD))
                      =  (Subst.onPolyTy
                          (Subst.conj (swapNat Φ W) S₀
                            ++ [(Φ, Ty.rename (swapNat Φ W) paramTyD)])
                          (PolyTy.mkTrivial (.fvar Φ))) := by
                    simp only [Subst.onPolyTy, PolyTy.mkTrivial]
                    rw [swapSubst_onTy (Ne.symm hWΦ) (Ne.symm hcΦ) hWc hcparam,
                        Subst.onTy_append (Subst.conj (swapNat Φ W) S₀)
                          [(Φ, Ty.rename (swapNat Φ W) paramTyD)] (.fvar Φ),
                        hSconjΦ]
                    simp only [Subst.onTy, Ty.substFvars, Ty.substFvar, if_pos,
                      ]
                  show
                      (Subst.onEnv (swapSubst Φ W c)
                        (PolyTy.mkTrivial paramTyD ::  (Subst.onEnv S₀ ctx.env)))
                    =
                        (Subst.onEnv
                          (Subst.conj (swapNat Φ W) S₀ ++ [(Φ, Ty.rename (swapNat Φ W) paramTyD)])
                          (PolyTy.mkTrivial (.fvar Φ) :: ctx.env))
                  simp only [Subst.onEnv,  List.map_cons, List.map_map]
                  rw [hh]
                  exact congrArg₂ List.cons rfl (List.map_congr_left henvpt)
                · trivial
              rw [hctxeq] at hrenE
              have hτe'eq :  (Subst.onTy (swapSubst Φ W c) bodyTy)
                  = Ty.rename (swapNat Φ W) ( bodyTy) := by
                rw [swapSubst_onTy (Ne.symm hWΦ) (Ne.symm hcΦ) hWc hcbody]
              -- STEP 2: apply the IH to the body under the conjugated specialization
              have hwf_b : CtxWF { ctx with env := PolyTy.mkTrivial (.fvar Φ) :: ctx.env } := by
                intro M hM
                rcases List.mem_cons.mp hM with rfl | hM
                · exact ContainsBvarsUpTo.fvar
                · exact hwf M hM
              have hbelow_b : CtxBelow (Φ + 1) { ctx with env := PolyTy.mkTrivial (.fvar Φ) :: ctx.env } := by
                intro M hM
                rcases List.mem_cons.mp hM with rfl | hM
                · exact .fvar (by omega)
                · exact (hbelow M hM).mono (by omega)
              have hT_lc : ∀ p ∈ Subst.conj (swapNat Φ W) S₀ ++ [(Φ, Ty.rename (swapNat Φ W) paramTyD)],
                  p.2.IsLC := by
                intro p hp
                rw [List.mem_append] at hp
                rcases hp with hp | hp
                · exact Subst.conj_lc hS₀ p hp
                · rw [List.mem_singleton] at hp
                  subst hp
                  exact Ty.rename_isLC hpc
              have hSconjK : ∀ k ∈ K, (Subst.conj (swapNat Φ W) S₀
                  ++ [(Φ, Ty.rename (swapNat Φ W) paramTyD)]).onTy (.fvar k) = .fvar k := by
                intro k hk
                have hklt := hKΦ k hk
                rw [Subst.onTy_append]
                have hconj : (Subst.conj (swapNat Φ W) S₀).onTy (.fvar k) = .fvar k := by
                  have h := Subst.onTy_conj finj S₀ (.fvar k)
                  rw [Ty.rename_fvar, hfix k hklt] at h
                  rw [h, hKfix k hk, Ty.rename_fvar, hfix k hklt]
                rw [hconj]
                exact Ty.substFvars_eq_self_of_no_key (fun p hp hc => by
                  rw [List.mem_singleton] at hp; subst hp
                  simp only [Ty.freeVars, List.mem_singleton] at hc; omega)
              let S₁ : Subst := Subst.conj (swapNat Φ W) S₀ ++ [(Φ, Ty.rename (swapNat Φ W) paramTyD)]
              rw [hτe'eq] at hrenE
              obtain ⟨R_b, hR_b, htyb, hR_bfix, hagb⟩ :=
                ih.1 hbody hsize hwf_b hbelow_b hwf_b hbelow_b S₁
                  (Ty.rename (swapNat Φ W) ( bodyTy)) K
                  hT_lc (fun k hk => by have := hKΦ k hk; omega) hbodyK hSconjK hrenE
              have htyb' : Eq (Ty.rename (swapNat Φ W) bodyTy) (R_b.onTy τb) := by
                exact htyb
              -- STEP 3: assemble the conclusion
              let R : Subst := R_b ++ [(W, Ty.fvar Φ)]
              have hWv : ∀ {v : Nat}, v < Φ → W ∉ (Ty.fvar v).freeVars := by
                intro v hv
                simp only [Ty.freeVars, List.mem_singleton]
                omega
              have hWparam_e : W ∉ ( paramTyD).freeVars := by
                exact hWparam
              have hWbody_e : W ∉ ( bodyTy).freeVars := by
                exact hWbody
              have herase_swap : ∀ {Y : Ty}, c ∉ Y.freeVars →
                   (Ty.rename (swapNat Φ W) Y) = Ty.rename (swapNat Φ W) ( Y) := by
                intro Y _
                rfl
              have hS₁onTyΦ : Subst.onTy S₁ (.fvar Φ) = Ty.rename (swapNat Φ W) paramTyD := by
                simp only [S₁]
                rw [Subst.onTy_append, hSconjΦ]
                simp only [Subst.onTy, Ty.substFvars, Ty.substFvar, if_pos]
              have hR'eq_param : Eq paramTyD (Subst.onTy R (S.onTy (.fvar Φ))) := by
                change  paramTyD =  (Subst.onTy R (S.onTy (.fvar Φ)))
                dsimp [R]
                rw [← Subst.onTy_append, ← List.append_assoc, Subst.onTy_append]
                symm
                calc
                   (Subst.onTy [(W, Ty.fvar Φ)] ((S ++ R_b).onTy (.fvar Φ)))
                      = Ty.substFvar W (.fvar Φ) ( ((S ++ R_b).onTy (.fvar Φ))) := by
                        simp [Subst.onTy, Ty.substFvars]
                  _ = Ty.substFvar W (.fvar Φ) ( (Subst.onTy S₁ (.fvar Φ))) := by
                        rw [hagb Φ (by omega)]
                  _ = Ty.substFvar W (.fvar Φ) ( (Ty.rename (swapNat Φ W) paramTyD)) := by
                        rw [hS₁onTyΦ]
                  _ = Ty.substFvar W (.fvar Φ) (Ty.rename (swapNat Φ W) ( paramTyD)) := by
                        rw [herase_swap hcparam]
                  _ =  paramTyD := Ty.substFvar_rename_swap hWparam_e
              have hR'eq_body : Eq bodyTy (Subst.onTy R τb) := by
                change  bodyTy =  (Subst.onTy R τb)
                dsimp [R]
                rw [Subst.onTy_append]
                symm
                calc
                   (Subst.onTy [(W, Ty.fvar Φ)] (R_b.onTy τb))
                      = Ty.substFvar W (.fvar Φ) ( (R_b.onTy τb)) := by
                        simp [Subst.onTy, Ty.substFvars]
                  _ = Ty.substFvar W (.fvar Φ) ( (Ty.rename (swapNat Φ W) bodyTy)) := by
                        rw [htyb']
                  _ = Ty.substFvar W (.fvar Φ) (Ty.rename (swapNat Φ W) ( bodyTy)) := by
                        rw [herase_swap hcbody]
                  _ =  bodyTy := Ty.substFvar_rename_swap hWbody_e
              have hagree : Subst.AgreesBelow Φ S₀ (S ++ R) := by
                intro v hv
                have hconjv : (Subst.conj (swapNat Φ W) S₀).onTy (.fvar v)
                    = Ty.rename (swapNat Φ W) (S₀.onTy (.fvar v)) := by
                  have h := Subst.onTy_conj finj S₀ (.fvar v)
                  rw [Ty.rename_fvar, hfix v hv] at h
                  exact h
                have hTv : Subst.onTy S₁ (.fvar v) = Ty.rename (swapNat Φ W) (S₀.onTy (.fvar v)) := by
                  simp only [S₁]
                  rw [Subst.onTy_append, hconjv]
                  exact Ty.substFvar_fresh (Ty.rename_swap_not_mem_left
                    (hWonTy (τ := .fvar v) (hWv hv)))
                have hWonTy_v_e : W ∉ ( (S₀.onTy (.fvar v))).freeVars := by
                  exact hWonTy (τ := .fvar v) (hWv hv)
                dsimp [R]
                rw [← List.append_assoc, Subst.onTy_append]
                change  (S₀.onTy (.fvar v)) =
                  (Subst.onTy [(W, Ty.fvar Φ)] ((S ++ R_b).onTy (.fvar v)))
                symm
                calc
                   (Subst.onTy [(W, Ty.fvar Φ)] ((S ++ R_b).onTy (.fvar v)))
                      = Ty.substFvar W (.fvar Φ) ( ((S ++ R_b).onTy (.fvar v))) := by
                        simp [Subst.onTy, Ty.substFvars]
                  _ = Ty.substFvar W (.fvar Φ) ( (Subst.onTy S₁ (.fvar v))) := by
                        rw [hagb v (by omega)]
                  _ = Ty.substFvar W (.fvar Φ) ( (Ty.rename (swapNat Φ W) (S₀.onTy (.fvar v)))) := by
                        rw [hTv]
                  _ = Ty.substFvar W (.fvar Φ) (Ty.rename (swapNat Φ W) ( (S₀.onTy (.fvar v)))) := by
                        rw [herase_swap (Subst.not_mem_onTy_freeVars hcrange
                          (fun hv' => by simp only [Ty.freeVars, List.mem_singleton] at hv'; omega))]
                  _ =  (S₀.onTy (.fvar v)) :=
                        Ty.substFvar_rename_swap hWonTy_v_e
              refine ⟨R, ?_, ?_, ?_, hagree⟩
              · -- residual is LC
                intro p hp
                rw [List.mem_append] at hp
                rcases hp with hp | hp
                · exact hR_b p hp
                · rw [List.mem_singleton] at hp
                  subst hp
                  exact ContainsBvarsUpTo.fvar
              · -- the arrow type is recovered
                change Eq (.arrow paramTyD bodyTy)
                  (Subst.onTy R (.arrow (S.onTy (.fvar Φ)) τb))
                rw [Subst.onTy_arrow]
                show Ty.arrow paramTyD bodyTy =
                  Ty.arrow (Subst.onTy R (S.onTy (.fvar Φ))) (Subst.onTy R τb)
                exact congrArg₂ Ty.arrow hR'eq_param hR'eq_body
              · -- residual fixes the rigid set K
                intro k hk
                rw [Subst.onTy_append, hR_bfix k hk]
                exact Ty.substFvars_eq_self_of_no_key (fun p hp hc => by
                  rw [List.mem_singleton] at hp; subst hp
                  simp only [Ty.freeVars, List.mem_singleton] at hc
                  have := hKΦ k hk; omega)
            | some hlc =>
              rename_i hlc
              have hpeq : paramTyD = paramTy := hann paramTy rfl
              subst paramTyD
              -- raw-world facts for the IH's context (the Infer.lambda body ctx
              -- carries the RAW annotation `paramTy`, not its erasure).
              have hTK : ∀ y ∈ paramTy.freeVars, y ∈ K := fun y hy =>
                hKe y (by simp [Expr.tyFreeVars, List.mem_append]; exact Or.inl hy)
              have hbodyK : ∀ y ∈ body.tyFreeVars, y ∈ K := fun y hy =>
                hKe y (by simp [Expr.tyFreeVars, List.mem_append]; exact Or.inr hy)
              have hTbelow : Ty.BelowFvars Φ paramTy :=
                Ty.BelowFvars.of_freeVars_lt (fun v hv => hKΦ v (hTK v hv))
              have hself : S₀.onTy paramTy = paramTy :=
                Subst.onTy_eq_self_of_fixes (fun v hv => hKfix v (hTK v hv))
              have hwf' : CtxWF { ctx with
                  env := PolyTy.mkTrivial paramTy :: ctx.env } := by
                intro M hM
                rcases List.mem_cons.mp hM with rfl | hM
                · exact hlc
                · exact hwf M hM
              have hbelow' : CtxBelow Φ { ctx with
                  env := PolyTy.mkTrivial paramTy :: ctx.env } := by
                intro M hM
                rcases List.mem_cons.mp hM with rfl | hM
                · exact hTbelow
                · exact hbelow M hM
              -- the substituted context of the raw-extended body derivation is the
              -- IH's premise context for S₀.
              have heqC :
                  ({ (S₀.onCtx ctx) with
                      env := PolyTy.mkTrivial paramTy
                                :: ((S₀.onCtx ctx)).env })
                  = ((S₀.onCtx { ctx with
                          env := PolyTy.mkTrivial paramTy
                                    :: ctx.env })) := by
                dsimp only [Subst.onCtx]
                show Ctx.mk
                    (
                      (PolyTy.mkTrivial paramTy
                        ::  (Subst.onEnv S₀ ctx.env)))
                    ( ( ctx.ctors))
                  = Ctx.mk
                    (
                      (Subst.onEnv S₀ (PolyTy.mkTrivial paramTy :: ctx.env)))
                    ( ctx.ctors)
                simp only [Ctx.mk.injEq, true_and]
                constructor
                · show
                      (PolyTy.mkTrivial paramTy
                        ::  (Subst.onEnv S₀ ctx.env))
                    =
                        (Subst.onEnv S₀
                          (PolyTy.mkTrivial paramTy :: ctx.env))
                  simp [Subst.onEnv,  List.map_cons, Subst.onPolyTy,  PolyTy.mkTrivial, hself,
                    List.map_map]
                · trivial
              have e1 := hbodyD
              rw [heqC] at e1
              obtain ⟨R_b, hR_b, htyb, hR_bfix, hagb⟩ :=
                ih.1 hbody hsize hwf' hbelow' hwf' hbelow' S₀
                  ( bodyTy) K hS₀ hKΦ hbodyK hKfix e1
              have htyb' : Eq bodyTy (R_b.onTy τb) := by
                exact htyb
              have hparam : Eq paramTy
                  (R_b.onTy (S.onTy paramTy)) := by
                change paramTy
                  = R_b.onTy (S.onTy paramTy)
                rw [← Subst.onTy_append, ← Subst.onTy_congr hagb hTbelow, hself]
              refine ⟨R_b, hR_b, ?_, hR_bfix, hagb⟩
              change Eq (.arrow paramTy bodyTy)
                (R_b.onTy (.arrow (S.onTy paramTy) τb))
              rw [Subst.onTy_arrow]
              show Ty.arrow paramTy bodyTy =
                Ty.arrow (R_b.onTy (S.onTy paramTy)) (R_b.onTy τb)
              exact congrArg₂ Ty.arrow hparam htyb'
      | @app Φ ctx f arg Φ₁ Φ₂ S₁ S₂ S₃ τf τa hf harg huni =>
        exact fun hwf hbelow S₀ τe K hS₀ hKΦ hKe hKfix hty => by
          cases hty with
          | app hfD hargD =>
            rename_i argTyD
            have hsize_f : f.size < n := by
              have := _hn
              simp [Expr.size] at this
              omega
            have hsize_a : arg.size < n := by
              have := _hn
              simp [Expr.size] at this
              omega
            have hKf : ∀ y ∈ f.tyFreeVars, y ∈ K := fun y hy => hKe y (by
              simp only [Expr.tyFreeVars, List.mem_append]; exact Or.inl hy)
            have hKa : ∀ y ∈ arg.tyFreeVars, y ∈ K := fun y hy => hKe y (by
              simp only [Expr.tyFreeVars, List.mem_append]; exact Or.inr hy)
            -- STEP 1: recurse on `f` at the ambient specialization `S₀`.
            obtain ⟨R_f, hR_f, htyf, hR_fK, hagf⟩ :=
              ih.1 hf hsize_f hwf hbelow hwf hbelow S₀ (.arrow argTyD τe) K
                hS₀ hKΦ hKf hKfix hfD
            have hfle : Φ ≤ Φ₁ := Infer.frontier_le hf
            have hS₁lc : ∀ p ∈ S₁, p.2.IsLC := (Infer.lc hf hwf).2
            have hτf_bel : Ty.BelowFvars Φ₁ τf :=
              (Infer.belowFvars hf hbelow (fun y hy => hKΦ y (hKf y hy))).1
            have hf_sbel : ∀ p ∈ S₁, Ty.BelowFvars Φ₁ p.2 :=
              (Infer.belowFvars hf hbelow (fun y hy => hKΦ y (hKf y hy))).2
            have hwf₁ : CtxWF (S₁.onCtx ctx) := Subst.onCtx_wf hS₁lc hwf
            have hbelow₁ : CtxBelow Φ₁ (S₁.onCtx ctx) :=
              Subst.onCtx_below hf_sbel hfle hbelow
            have hKΦ₁ : ∀ k ∈ K, k < Φ₁ := fun k hk => lt_of_lt_of_le (hKΦ k hk) hfle
            have harg' : TypeOfHM ((R_f.onCtx (S₁.onCtx ctx))) arg
                argTyD := by
              -- COMPLETE-APP-RESIDUAL (pivot): substitutions agreeing below the
              -- frontier produce equal substituted contexts, so the S₀-world typing of
              -- `arg` IS the R_f-world typing — context identity, type untouched.
              have hid : ((S₀.onCtx ctx))
                  = ((R_f.onCtx (S₁.onCtx ctx))) := by
                rw [← Subst.onCtx_append]
                exact Subst.onCtx_congr hagf hbelow
              rw [hid] at hargD
              exact hargD
            obtain ⟨R_a, hR_a, htya, hR_aK, haga⟩ :=
              ih.1 harg hsize_a hwf₁ hbelow₁ hwf₁ hbelow₁ R_f argTyD K hR_f hKΦ₁ hKa hR_fK harg'
            -- STEP 3: explicit unifier `U` for `S₂.onTy τf` vs `.arrow τa (.fvar Φ₂)`,
            -- via a fresh `W` above everything (mirrors the old application-unifier helper).
            have hargle : Φ₁ ≤ Φ₂ := Infer.frontier_le harg
            have hKΦ₂ : ∀ k ∈ K, k < Φ₂ := fun k hk => lt_of_lt_of_le (hKΦ₁ k hk) hargle
            have hS₂lc : ∀ p ∈ S₂, p.2.IsLC := (Infer.lc harg hwf₁).2
            have hτa_lc : τa.IsLC := (Infer.lc harg hwf₁).1
            have hτf_lc : τf.IsLC := (Infer.lc hf hwf).1
            have hS₂_bel : ∀ p ∈ S₂, Ty.BelowFvars Φ₂ p.2 :=
              (Infer.belowFvars harg hbelow₁ (fun y hy => lt_of_lt_of_le (hKΦ y (hKa y hy)) hfle)).2
            have hτa_bel : Ty.BelowFvars Φ₂ τa :=
              (Infer.belowFvars harg hbelow₁ (fun y hy => lt_of_lt_of_le (hKΦ y (hKa y hy)) hfle)).1
            have hτe_lc : τe.IsLC := by
              have := TypeOfHM.regular hfD
              cases this with | arrow _ hret => exact hret
            have hAgreeFty' : Eq (R_f.onTy τf) (R_a.onTy (S₂.onTy τf)) := by
              have h := Subst.onTy_congr haga hτf_bel
              simpa [Subst.onTy_append] using h
            have hP : Eq (.arrow argTyD τe) (R_a.onTy (S₂.onTy τf)) :=
              Eq.trans htyf hAgreeFty'
            have hτf_bel₂ : Ty.BelowFvars Φ₂ (S₂.onTy τf) := by
              apply Subst.onTy_belowFvars hS₂_bel
              exact hτf_bel.mono hargle
            have hΦ₂A : Φ₂ ∉ (S₂.onTy τf).freeVars := by
              intro hc
              have := Ty.BelowFvars.mem_lt hτf_bel₂ Φ₂ hc
              omega
            have hΦ₂τa : Φ₂ ∉ τa.freeVars := by
              intro hc
              have := Ty.BelowFvars.mem_lt hτa_bel Φ₂ hc
              omega
            obtain ⟨W, hWge, hWfresh⟩ := exists_fresh_block
              (R_a.map Prod.fst ++ R_a.flatMap (fun p => p.2.freeVars) ++ argTyD.freeVars ++ τe.freeVars) Φ₂ 1
            have hWdom : ∀ p ∈ R_a, p.1 ≠ W := by
              intro p hp he
              have := hWfresh p.1 (List.mem_append_left _ (List.mem_append_left _
                (List.mem_append_left _ (List.mem_map.mpr ⟨p, hp, rfl⟩))))
              omega
            have hWrange : ∀ p ∈ R_a, W ∉ p.2.freeVars := by
              intro p hp hc
              have := hWfresh W (List.mem_append_left _ (List.mem_append_left _
                (List.mem_append_right _ (List.mem_flatMap.mpr ⟨p, hp, hc⟩))))
              omega
            have hWargTy : W ∉ argTyD.freeVars := fun hc => by
              have := hWfresh W (List.mem_append_left _ (List.mem_append_right _ hc)); omega
            have hWτe : W ∉ τe.freeVars := fun hc => by
              have := hWfresh W (List.mem_append_right _ hc); omega
            have hWargTyE : W ∉ ( argTyD).freeVars := fun hc =>
              hWargTy hc
            have hWτeE : W ∉ ( τe).freeVars := fun hc =>
              hWτe hc
            have hR_aWfvar : R_a.onTy (Ty.fvar W) = Ty.fvar W := by
              apply Ty.substFvars_eq_self_of_no_key
              intro p hp hc
              simp only [Ty.freeVars, List.mem_singleton] at hc
              exact hWdom p hp hc
            obtain ⟨U, hUdef⟩ : ∃ U : Subst, U = [(Φ₂, Ty.fvar W)] ++ R_a ++ [(W, τe)] := ⟨_, rfl⟩
            have hsingle : ∀ (Z : Nat) (V y : Ty), Subst.onTy [(Z, V)] y = Ty.substFvar Z V y :=
              fun _ _ _ => rfl
            have hsubArrow : ∀ (Z : Nat) (V a b : Ty),
                Ty.substFvar Z V (Ty.arrow a b) = Ty.arrow (Ty.substFvar Z V a) (Ty.substFvar Z V b) :=
              fun _ _ _ _ => rfl
            have hUonTy : ∀ x, U.onTy x = Ty.substFvar W τe (R_a.onTy (Ty.substFvar Φ₂ (Ty.fvar W) x)) := by
              intro x
              rw [hUdef, Subst.onTy_append, Subst.onTy_append, hsingle, hsingle]
            have e1 : Ty.substFvar Φ₂ (Ty.fvar W) (Ty.fvar Φ₂) = Ty.fvar W := by simp [Ty.substFvar]
            have e2 : Ty.substFvar W τe (Ty.fvar W) = τe := by simp [Ty.substFvar]
            have hUniL :  (U.onTy (S₂.onTy τf)) =
                Ty.arrow ( argTyD) ( τe) := by
              rw [hUonTy, Ty.substFvar_fresh hΦ₂A]
              rw [← hP, hsubArrow, Ty.substFvar_fresh hWargTyE,
                Ty.substFvar_fresh hWτeE]
            have hUniR :  (U.onTy (.arrow τa (.fvar Φ₂))) =
                Ty.arrow ( argTyD) ( τe) := by
              rw [hUonTy, hsubArrow, Ty.substFvar_fresh hΦ₂τa, e1, Subst.onTy_arrow,
                hR_aWfvar, hsubArrow, e2]
              rw [← htya, Ty.substFvar_fresh hWargTyE]
            have hU : Unifies U (S₂.onTy τf) (.arrow τa (.fvar Φ₂)) := by
              show  (U.onTy (S₂.onTy τf)) =
                 (U.onTy (.arrow τa (.fvar Φ₂)))
              rw [hUniL, hUniR]
            have hUlc : ∀ p ∈ U, p.2.IsLC := by
              rw [hUdef]
              intro p hp
              rcases List.mem_append.mp hp with hp' | hp'
              · rcases List.mem_append.mp hp' with hp'' | hp''
                · obtain rfl := List.mem_singleton.mp hp''
                  exact ContainsBvarsUpTo.fvar
                · exact hR_a p hp''
              · obtain rfl := List.mem_singleton.mp hp'
                exact hτe_lc
            have hUK : ∀ k ∈ K, U.onTy (.fvar k) = .fvar k := by
              intro k hk
              have hklt : k < Φ₂ := hKΦ₂ k hk
              have hkΦ₂ : Φ₂ ∉ (Ty.fvar k).freeVars := by
                simp only [Ty.freeVars, List.mem_singleton]; omega
              have hkW : W ∉ (Ty.fvar k).freeVars := by
                simp only [Ty.freeVars, List.mem_singleton]; omega
              rw [hUonTy, Ty.substFvar_fresh hkΦ₂, hR_aK k hk, Ty.substFvar_fresh hkW]
            have hUΦ₂ : U.onTy (.fvar Φ₂) = τe := by
              rw [hUonTy, e1, hR_aWfvar, e2]
            have hUbelow : ∀ v < Φ₂, U.onTy (.fvar v) = R_a.onTy (.fvar v) := by
              intro v hv
              have hWv : W ∉ (Ty.fvar v).freeVars := by
                simp only [Ty.freeVars, List.mem_singleton]
                omega
              have hWR_av : W ∉ (R_a.onTy (Ty.fvar v)).freeVars :=
                Subst.not_mem_onTy_freeVars hWrange hWv
              rw [hUonTy, Ty.substFvar_fresh (show Φ₂ ∉ (Ty.fvar v).freeVars by
                simp only [Ty.freeVars, List.mem_singleton]; omega), Ty.substFvar_fresh hWR_av]
            -- STEP 4: factor the witness `U` through the given MGU `huni`.
            obtain ⟨R, hRfac, hRlc, hRK⟩ := UnifyRel.greatest_K huni U hUlc hU hUK
            have hAgree₃ : Subst.AgreesBelow Φ₂ R_a (S₃ ++ R) := by
              intro v hv
              rw [Subst.onTy_append]
              have h := hRfac (Ty.fvar v)
              rwa [hUbelow v hv] at h
            have hAgree₂ : Subst.AgreesBelow Φ₁ R_f ((S₂ ++ S₃) ++ R) :=
              @Subst.AgreesBelow.trans_append Φ₁ Φ₂ R_f S₂ R_a S₃ R hargle haga hS₂_bel hAgree₃
            have hAgree : Subst.AgreesBelow Φ S₀ ((S₁ ++ (S₂ ++ S₃)) ++ R) :=
              @Subst.AgreesBelow.trans_append Φ Φ₁ S₀ S₁ R_f (S₂ ++ S₃) R hfle hagf hf_sbel hAgree₂
            have hAgreeOut : Eq τe (R.onTy (S₃.onTy (.fvar Φ₂))) := by
              have h := hRfac (Ty.fvar Φ₂)
              rwa [hUΦ₂] at h
            refine ⟨R, hRlc, hAgreeOut, hRK, ?_⟩
            · simpa [List.append_assoc] using hAgree
      | @letIn Φ ctx rhs body Φ₁ Φ₂ S₁ S₂ τ₁ τ₂ hrhs hbody =>
        exact fun hwf hbelow S₀ τe K hS₀ hKΦ hKe hKfix hty => by
          -- [letin-agent]
          cases hty with
          | letIn hwfM hann hcofin heq hbodyD =>
            subst heq
            rename_i M L
            have hsize_r : rhs.size < n := by
              have := _hn
              simp [Expr.size] at this
              omega
            have hsize_b : body.size < n := by
              have := _hn
              simp [Expr.size] at this
              omega
            have hKrhs : ∀ y ∈ rhs.tyFreeVars, y ∈ K := fun y hy => hKe y (by
              simp only [Expr.tyFreeVars, List.mem_append]; exact Or.inl (Or.inr hy))
            have hKbody : ∀ y ∈ body.tyFreeVars, y ∈ K := fun y hy => hKe y (by
              simp only [Expr.tyFreeVars, List.mem_append]; exact Or.inr hy)
            -- fresh names for the cofinite instantiation
            obtain ⟨Xs, hXlen, hXnodup, hXavoid⟩ := exists_fresh_names
              (L ++ M.body.freeVars ++ K ++ (S₀.map Prod.fst ++ S₀.flatMap (fun p => p.2.freeVars)) ++ List.range Φ)
              M.paramCount
            have hXfresh : FreshNames L M.paramCount Xs := ⟨hXlen, hXnodup, fun x hx hc =>
              hXavoid x hx (by simp only [List.mem_append]; tauto)⟩
            have hXMbody : ∀ x ∈ Xs, x ∉ M.body.freeVars := fun x hx hc =>
              hXavoid x hx (by simp only [List.mem_append]; tauto)
            have hXK : ∀ x ∈ Xs, x ∉ K := fun x hx hc =>
              hXavoid x hx (by simp only [List.mem_append]; tauto)
            have hXS₀ran : ∀ x ∈ Xs, x ∉ S₀.flatMap (fun p => p.2.freeVars) := fun x hx hc =>
              hXavoid x hx (by simp only [List.mem_append]; tauto)
            have hXrange : ∀ x ∈ Xs, x ∉ List.range Φ := fun x hx hc =>
              hXavoid x hx (by simp only [List.mem_append]; tauto)
            -- STEP 1: recurse on the rhs at the opened scheme type
            obtain ⟨R₁, hR₁, htyr₁, hR₁K, hAgree₁⟩ :=
              ih.1 hrhs hsize_r hwf hbelow hwf hbelow S₀ (M.openVars Xs) K hS₀ hKΦ hKrhs hKfix
                (by simpa [Expr.openBoundTyVars] using hcofin Xs hXfresh)
            have hfle : Φ ≤ Φ₁ := Infer.frontier_le hrhs
            have hKΦ₁ : ∀ k ∈ K, k < Φ₁ := fun k hk => lt_of_lt_of_le (hKΦ k hk) hfle
            obtain ⟨hτ₁_lc, hS₁lc⟩ := Infer.lc hrhs hwf
            have hrhs_below := Infer.belowFvars hrhs hbelow (fun y hy => hKΦ y (hKrhs y hy))
            have hτ₁_bel : Ty.BelowFvars Φ₁ τ₁ := hrhs_below.1
            have hS₁_bel : ∀ p ∈ S₁, Ty.BelowFvars Φ₁ p.2 := hrhs_below.2
            have hwf₁ : CtxWF (S₁.onCtx ctx) := Subst.onCtx_wf hS₁lc hwf
            have hbelow₁ : CtxBelow Φ₁ (S₁.onCtx ctx) := Subst.onCtx_below hS₁_bel hfle hbelow
            -- context bridge: R₁-transported ctx = S₀ ctx
            have hctxBridge : ((R₁.onCtx (S₁.onCtx ctx)))
                = ((S₀.onCtx ctx)) := by
              rw [← Subst.onCtx_append]
              exact (Subst.onCtx_congr hAgree₁ hbelow).symm
            -- STEP 2: the generalisation link — the algorithm scheme generalises M
            set rigid := rhs.tyFreeVars with hrigid_def
            set env₁ := (S₁.onCtx ctx).env with henv₁_def
            set genV := genVars rigid env₁ τ₁ with hgenV_def
            set Rer : Subst := R₁ with hRe_def
            set eτ : Ty :=  τ₁ with heτ_def
            let M' : PolyTy :=  (R₁.onPolyTy (genScheme rigid env₁ τ₁))
            have heτ_lc : eτ.IsLC := by simpa [eτ] using hτ₁_lc
            have hRe_lc : ∀ p ∈ Rer, p.2.IsLC := by
              simpa [Rer] using hR₁
            have hMwf_e : ( M).WF := hwfM
            have hXlen_e : Xs.length = ( M).paramCount := by
              simpa [] using hXlen
            have hXMbody_e : ∀ x ∈ Xs, x ∉ ( M).body.freeVars := by
              intro x hx hc
              exact hXMbody x hx (hc)
            have htyr_e : Ty.openVars Xs ( M).body = Rer.onTy eτ := by
              simpa [Rer, eτ, PolyTy.openVars] using htyr₁
            have hXM'' : ∀ x ∈ Xs, x ∉ (Rer.onPolyTy ⟨genV.length, Ty.closeOver genV eτ⟩).body.freeVars := by
              intro x hx hcx
              rw [Subst.onPolyTy] at hcx
              have hB : Rer.onTy (Ty.closeOver genV eτ) =  (R₁.onTy (Ty.closeOver genV τ₁)) := by
                simp [Rer, eτ]
              rw [hB] at hcx
              rw [Ty.mem_freeVars_onTy_iff] at hcx
              obtain ⟨v, hv, hxv⟩ := hcx
              have hvτ : v ∈ τ₁.freeVars := Ty.freeVars_closeOver_subset hv
              have hvnotg : v ∉ genV := fun hg => Ty.not_mem_closeOver_freeVars hg hv
              have hvenv : v ∈ env₁.freeVars ∨ v ∈ rigid := by
                by_cases h1 : v ∈ env₁.freeVars
                · exact Or.inl h1
                · by_cases h2 : v ∈ rigid
                  · exact Or.inr h2
                  · exfalso
                    exact hvnotg (by
                      rw [hgenV_def, genVars]
                      apply List.mem_filter.mpr
                      exact ⟨hvτ, by
                        simp only [Bool.and_eq_true]
                        exact ⟨by simpa using h1, by simpa using h2⟩⟩)
              rcases hvenv with hvenv | hrigid
              · have hvenv₁ : v ∈ (S₁.onCtx ctx).env.freeVars := by simpa [env₁] using hvenv
                rw [Env.mem_freeVars_iff] at hvenv₁
                simp only [Subst.onCtx, Subst.onEnv, List.mem_map] at hvenv₁
                obtain ⟨σ, hσ, vσ⟩ := hvenv₁
                obtain ⟨M₀, hM₀, rfl⟩ := hσ
                rw [Subst.onPolyTy] at vσ
                rw [Subst.onTy, Ty.mem_freeVars_substFvars_image] at vσ
                obtain ⟨w, hw, vw⟩ := vσ
                have hwlt : w < Φ := (hbelow M₀ hM₀).mem_lt w hw
                have hxS₁R₁ : x ∈ ((S₁ ++ R₁).onTy (Ty.fvar w)).freeVars := by
                  rw [Subst.onTy_append]
                  exact Ty.mem_freeVars_onTy_iff.mpr ⟨v, vw, hxv⟩
                have hxS₀ : x ∈ (S₀.onTy (Ty.fvar w)).freeVars := by
                  rwa [hAgree₁ w hwlt]
                rcases Subst.mem_freeVars_onTy hxS₀ with hxw | ⟨p, hp, hxp⟩
                · simp only [Ty.freeVars, List.mem_singleton] at hxw
                  exact hXrange x hx (List.mem_range.mpr (hxw ▸ hwlt))
                · exact hXS₀ran x hx (List.mem_flatMap.mpr ⟨p, hp, hxp⟩)
              · have hvK : v ∈ K := hKrhs v hrigid
                rw [hR₁K v hvK] at hxv
                simp only [Ty.freeVars, List.mem_singleton] at hxv
                exact hXK x hx (hxv ▸ hvK)
            have hgen : M'.Generalizes ( M) := by
              have hg' : (Rer.onPolyTy ⟨genV.length, Ty.closeOver genV eτ⟩).Generalizes ( M) := by
                exact closeOver_generalizes (g := genV) (τ₁ := eτ) (R := Rer)
                  (M :=  M) (Xs := Xs)
                  heτ_lc hRe_lc hMwf_e hXnodup hXlen_e hXMbody_e htyr_e hXM''
              have hscheme_eq : M' = Rer.onPolyTy ⟨genV.length, Ty.closeOver genV eτ⟩ := by
                dsimp [M']
                simp only [Subst.onPolyTy, genScheme]
                rw [hgenV_def]
              rw [hscheme_eq]
              exact hg'
            -- STEP 3: transport the body derivation to the algorithm scheme
            have hbE : TypeOfHM
                ({ (S₀.onCtx ctx) with
                    env :=  M :: (S₀.onCtx ctx).env })
                body ( τe) := by
              exact hbodyD
            have hbody_alg0 : TypeOfHM
                ({ (S₀.onCtx ctx) with
                    env := M' :: (S₀.onCtx ctx).env })
                body ( τe) := by
              exact TypeOfHM.weaken_scheme (env_post := []) (env := (S₀.onCtx ctx).env)
                (M :=  M) (M' := M') hgen hbE
            let ctx₁ : Ctx := { (S₁.onCtx ctx) with
                env := genScheme rhs.tyFreeVars (S₁.onCtx ctx).env τ₁ :: (S₁.onCtx ctx).env }
            have hbody_alg : TypeOfHM (R₁.onCtx ctx₁) body ( τe) := by
              rw [← hctxBridge] at hbody_alg0
              simpa [ctx₁, M', Subst.onCtx,  Subst.onEnv,
                List.map_cons] using hbody_alg0
            -- STEP 4: recurse on the body at the extended context
            have hwf₁' : CtxWF ctx₁ := by
              intro M hM; rcases List.mem_cons.mp hM with rfl | hM
              · exact genScheme_wf hτ₁_lc
              · exact hwf₁ M hM
            have hbelow₁' : CtxBelow Φ₁ ctx₁ := by
              intro M hM; rcases List.mem_cons.mp hM with rfl | hM
              · exact hτ₁_bel.closeOver
              · exact hbelow₁ M hM
            obtain ⟨R₂, hR₂, htyb₂, hR₂K, hAgree₂⟩ :=
              ih.1 hbody hsize_b hwf₁' hbelow₁' hwf₁' hbelow₁' R₁ ( τe) K
                hR₁ hKΦ₁ hKbody hR₁K hbody_alg
            -- STEP 5: assemble
            have hAgree : Subst.AgreesBelow Φ S₀ ((S₁ ++ S₂) ++ R₂) :=
              @Subst.AgreesBelow.trans_append Φ Φ₁ S₀ S₁ R₁ S₂ R₂ hfle hAgree₁ hS₁_bel hAgree₂
            refine ⟨R₂, hR₂, by simpa [Eq] using htyb₂, hR₂K, hAgree⟩
      | @letInAnn Φ N ctx σ rhs body Φ₁ Φ₂ S₁ Schk S₂ τ₁ τ₂ hσwf hN hrhs huni _hesc1 _hesc2 hbody =>
        exact fun hwf hbelow S₀ τe K hS₀ hKΦ hKe hKfix hty => by
          -- [letinann-agent]
          cases hty with
          | letIn hwfM hann hcofin heq hbodyD =>
            subst heq
            rename_i M L
            have hMσ : M =  σ := hann ( σ) rfl
            subst M
            have hKrhs : ∀ y ∈ rhs.tyFreeVars, y ∈ K := fun y hy => hKe y (by
              simp only [Expr.tyFreeVars, Option.elim_some, List.mem_append]; tauto)
            have hKbody : ∀ y ∈ body.tyFreeVars, y ∈ K := fun y hy => hKe y (by
              simp only [Expr.tyFreeVars, Option.elim_some, List.mem_append]; tauto)
            have hKσ : ∀ y ∈ σ.body.freeVars, y ∈ K := fun y hy => hKe y (by
              simp only [Expr.tyFreeVars, Option.elim_some, List.mem_append]; tauto)
            have hsize_r : (rhs.openTyVars (freshVars N σ.paramCount)).size < n := by
              rw [Expr.size_openTyVars]
              have := _hn
              simp only [Expr.size] at this
              omega
            have hsize_b : body.size < n := by
              have := _hn
              simp [Expr.size] at this
              omega
            set Ys : List Nat := freshVars N σ.paramCount with hYs_def
            have hYs_lt : ∀ y ∈ Ys, y < N + σ.paramCount := fun y hy => freshVars_lt y (by simpa [Ys] using hy)
            have hYs_ge : ∀ y ∈ Ys, N ≤ y := fun y hy => freshVars_ge y (by simpa [Ys] using hy)
            have hYs_Φ : ∀ y ∈ Ys, Φ ≤ y := fun y hy => le_trans hN (hYs_ge y hy)
            have hYs_notK : ∀ y ∈ Ys, y ∉ K := fun y hy hk => by
              have hlt : y < Φ := hKΦ y hk
              have hge : Φ ≤ y := hYs_Φ y hy
              omega
            have hfle : N + σ.paramCount ≤ Φ₁ := Infer.frontier_le hrhs
            have hKΦ₁ : ∀ k ∈ K, k < Φ₁ := fun k hk => lt_of_lt_of_le (hKΦ k hk) (by omega)
            have hKΦ₂ : ∀ k ∈ K, k < Φ' := fun k hk => lt_of_lt_of_le (hKΦ₁ k hk) (Infer.frontier_le hbody)
            have hKΦ' : ∀ k ∈ K ++ Ys, k < N + σ.paramCount := by
              intro k hk
              rcases List.mem_append.mp hk with hk | hk
              · have := hKΦ k hk; omega
              · exact hYs_lt k hk
            have hbelowN : CtxBelow (N + σ.paramCount) ctx := fun M hM => (hbelow M hM).mono (by omega)
            -- STEP 2: transport the cofinite typing to the inference's own skolems Ys
            obtain ⟨Xs, hXlen, hXnodup, hXavoid⟩ := exists_fresh_names
              (L ++ Ys ++ K ++ (S₀.onCtx ctx).env.freeVars) σ.paramCount
            have hXlenYs : Xs.length = Ys.length := by
              rw [hYs_def]; simpa [freshVars_length] using hXlen
            have hXavoidYs : ∀ x ∈ Xs, x ∉ Ys := fun x hx hc =>
              hXavoid x hx (by simp only [List.mem_append]; tauto)
            have hXavoidK : ∀ x ∈ Xs, x ∉ K := fun x hx hc =>
              hXavoid x hx (by simp only [List.mem_append]; tauto)
            have hXavoidCtx : ∀ x ∈ Xs, x ∉ (S₀.onCtx ctx).env.freeVars := fun x hx hc =>
              hXavoid x hx (by simp only [List.mem_append]; tauto)
            have hXfresh : FreshNames L σ.paramCount Xs := ⟨hXlen, hXnodup, fun x hx hc =>
              hXavoid x hx (by simp only [List.mem_append]; tauto)⟩
            have hcofinXs : TypeOfHM (S₀.onCtx ctx) (rhs.openTyVars Xs)
                (( σ).openVars Xs) := by
              simpa [Expr.openBoundTyVars] using hcofin Xs hXfresh
            set ρ : Subst := Xs.zip (Ys.map (Ty.fvar ·)) with hρ_def
            have hρlc : ∀ p ∈ ρ, p.2.IsLC := by
              intro p hp
              rw [hρ_def] at hp
              obtain ⟨_, hpy⟩ := List.of_mem_zip hp
              obtain ⟨y, _, hyeq⟩ := List.mem_map.mp hpy
              simpa [hyeq] using (ContainsBvarsUpTo.fvar : (Ty.fvar y).IsLC)
            have hρctx : ρ.onCtx (S₀.onCtx ctx) = (S₀.onCtx ctx) := by
              rw [hρ_def]
              apply congrArg (fun E => (⟨E, (S₀.onCtx ctx).ctors⟩ : Ctx))
              exact Subst.onEnv_eq_self_of_fresh (fun p hp hc => by
                have hx : p.1 ∈ Xs := (List.of_mem_zip hp).1
                exact hXavoidCtx p.1 hx hc)
            have hρsubj : (rhs.openTyVars Xs).substTyFvars ρ = (rhs.openTyVars Ys) := by
              rw [hρ_def]
              rw [Expr.substTyFvars_zip_openTyVars (Ys := Xs) (Xs := Ys) hXlenYs hXnodup
                (fun y hy hc => hXavoidK y hy (hKrhs y hc))
                hXavoidYs]
            have hρty : ρ.onTy (( σ).openVars Xs) = ( σ).openVars Ys := by
              rw [hρ_def]
              have h1 : ( σ).openVars Xs = Ty.openVars Xs ( σ.body) := rfl
              have h2 : ( σ).openVars Ys = Ty.openVars Ys ( σ.body) := rfl
              rw [h1, h2]
              change Ty.substFvars (Xs.zip (Ys.map (Ty.fvar ·))) (Ty.openVars Xs ( σ.body))
                = Ty.openVars Ys ( σ.body)
              rw [show Ty.substFvars (Xs.zip (Ys.map (Ty.fvar ·))) (Ty.openVars Xs ( σ.body))
                  = Ty.openVars Ys ( σ.body) from by
                have h3 := Ty.openWith_eq_substFvars_openVars (ty :=  σ.body)
                  (Vs := Ys.map (Ty.fvar ·)) (Xs := Xs)
                  ⟨by rw [List.length_map]; exact hXlenYs.symm, fun V hV => by
                    obtain ⟨y, _, hyeq⟩ := List.mem_map.mp hV
                    simpa [hyeq] using (ContainsBvarsUpTo.fvar : (Ty.fvar y).IsLC)⟩
                  hXnodup
                  (fun x hx hc => hXavoidK x hx (hKσ x (hc)))
                  (fun x hx hc => hXavoidYs x hx (Ty.mem_freeVarsList_map_fvar.mp hc))
                calc
                  Ty.substFvars (Xs.zip (Ys.map (Ty.fvar ·))) (Ty.openVars Xs ( σ.body))
                      = Ty.openWith (Ys.map (Ty.fvar ·)) ( σ.body) := h3.symm
                  _ = Ty.openVars Ys ( σ.body) :=
                    (Ty.openVars_eq_openWith (Xs := Ys) (ty :=  σ.body)).symm]
            have hren := TypeOfHM.onSubst ρ hρlc hcofinXs
            rw [hρctx, hρsubj, hρty] at hren
            have hKrhsOpen : ∀ y ∈ (rhs.openTyVars Ys).tyFreeVars, y ∈ K ++ Ys := by
              intro y hy
              rcases Expr.tyFreeVars_openTyVars hy with h | h
              · exact List.mem_append_left _ (hKrhs y h)
              · exact List.mem_append_right _ h
            -- ambient substitution fixing the skolems (fresh block, app-arm pattern):
            -- rename `Ys` to fresh `Ws` before `S₀` and back after it, so `S₀'`
            -- fixes every `y ∈ Ys` while agreeing with `S₀` below `Φ`.
            obtain ⟨W, hWge, hWfresh⟩ := exists_fresh_block
              (S₀.map Prod.fst ++ S₀.flatMap (fun p => p.2.freeVars) ++ Ys ++ List.range Φ)
              Φ σ.paramCount
            set Ws : List Nat := (List.range σ.paramCount).map (W + ·) with hWs_def
            set S₀' : Subst := (Ys.zip (Ws.map (Ty.fvar ·))) ++ S₀ ++ (Ws.zip (Ys.map (Ty.fvar ·)))
              with hS₀'_def
            have hWs_len : Ws.length = σ.paramCount := by
              rw [hWs_def]; simp
            have hWs_nodup : Ws.Nodup := by
              rw [hWs_def]
              apply List.Nodup.map (fun a b hab => by omega) List.nodup_range
            have hWs_ge_W : ∀ w ∈ Ws, W ≤ w := by
              intro w hw
              simp only [hWs_def] at hw
              obtain ⟨i, _, rfl⟩ := List.mem_map.mp hw
              omega
            have hWs_dom_fresh : ∀ w ∈ Ws, w ∉ S₀.map Prod.fst := fun w hw hmem => by
              have hlt : w < W := hWfresh w (List.mem_append_left _
                (List.mem_append_left _ (List.mem_append_left _ hmem)))
              have hge : W ≤ w := hWs_ge_W w hw
              omega
            have hWs_ran_fresh : ∀ w ∈ Ws, w ∉ S₀.flatMap (fun p => p.2.freeVars) :=
              fun w hw hmem => by
              have hlt : w < W := hWfresh w (List.mem_append_left _
                (List.mem_append_left _ (List.mem_append_right _ hmem)))
              have hge : W ≤ w := hWs_ge_W w hw
              omega
            have hWs_notYs : ∀ w ∈ Ws, w ∉ Ys := fun w hw hmem => by
              have hlt : w < W := hWfresh w (List.mem_append_left _ (List.mem_append_right _ hmem))
              have hge : W ≤ w := hWs_ge_W w hw
              omega
            have hS₀'agree : ∀ v < Φ, S₀'.onTy (.fvar v) = S₀.onTy (.fvar v) := by
              intro v hv
              rw [hS₀'_def]
              rw [Subst.onTy_append, Subst.onTy_append]
              have hb1 : Subst.onTy (Ys.zip (Ws.map (fun w => Ty.fvar w))) (.fvar v) = .fvar v := by
                apply Ty.substFvars_eq_self_of_no_key
                intro p hp hc
                simp only [Ty.freeVars, List.mem_singleton] at hc
                have hy : p.1 ∈ Ys := (List.of_mem_zip hp).1
                have : Φ ≤ p.1 := hYs_Φ p.1 hy
                omega
              rw [hb1]
              have hb2 : Subst.onTy (Ws.zip (Ys.map (fun y => Ty.fvar y))) (S₀.onTy (.fvar v))
                  = S₀.onTy (.fvar v) := by
                apply Ty.substFvars_eq_self_of_no_key
                intro p hp hc
                have hw : p.1 ∈ Ws := (List.of_mem_zip hp).1
                have hlt : p.1 < W := by
                  rcases Subst.mem_freeVars_onTy hc with h' | ⟨q, hq, h'⟩
                  · have hpv : p.1 = v := by
                      simp only [Ty.freeVars, List.mem_singleton] at h'
                      exact h'
                    have hvrange : v ∈ List.range Φ := List.mem_range.mpr hv
                    rw [hpv]
                    exact hWfresh v (List.mem_append_right _ hvrange)
                  · have hqmem : p.1 ∈ S₀.flatMap (fun p : Nat × Ty => p.2.freeVars) :=
                      List.mem_flatMap.mpr ⟨q, hq, h'⟩
                    exact hWfresh p.1 (List.mem_append_left _
                      (List.mem_append_left _ (List.mem_append_right _ hqmem)))
                have hge : W ≤ p.1 := hWs_ge_W p.1 hw
                omega
              rw [hb2]
            have hS₀'Ys : ∀ y ∈ Ys, S₀'.onTy (.fvar y) = .fvar y := by
              intro y hy
              rw [hS₀'_def]
              rw [Subst.onTy_append, Subst.onTy_append]
              obtain ⟨i, hi, hyi⟩ := List.mem_iff_getElem.mp hy
              have hget : Ys[i]? = some y := by
                have hg := List.getElem?_eq_getElem hi
                rwa [hyi] at hg
              have hiWs : i < Ws.length := by rw [hWs_len]; simpa [hYs_def, freshVars_length] using hi
              have hWsget : (Ws.map (fun w => Ty.fvar w))[i]? = some (Ty.fvar (Ws[i])) := by
                rw [List.getElem?_map]
                rw [List.getElem?_eq_getElem hiWs]
                rfl
              have hb1 : Subst.onTy (Ys.zip (Ws.map (fun w => Ty.fvar w))) (.fvar y) = Ty.fvar (Ws[i]) := by
                unfold Subst.onTy
                exact Ty.substFvars_zip_fvar_eq (by rw [List.length_map, hWs_len, hYs_def, freshVars_length])
                  (by rw [hYs_def]; exact freshVars_nodup)
                  (fun x hx hc => hWs_notYs x (Ty.mem_freeVarsList_map_fvar.mp hc) hx)
                  hget hWsget
              rw [hb1]
              have hSfix : S₀.onTy (.fvar (Ws[i])) = .fvar (Ws[i]) := by
                apply Ty.substFvars_eq_self_of_no_key
                intro p hp hc
                have hpWs : p.1 = Ws[i] := by
                  simp only [Ty.freeVars, List.mem_singleton] at hc
                  exact hc
                have hmemmap : Ws[i] ∈ S₀.map Prod.fst := by
                  rw [← hpWs]
                  exact List.mem_map_of_mem (f := Prod.fst) hp
                exact hWs_dom_fresh (Ws[i]) (List.getElem_mem hiWs) hmemmap
              rw [hSfix]
              have hWsgeti : Ws[i]? = some (Ws[i]) := List.getElem?_eq_getElem hiWs
              have hYsfvari : (Ys.map (fun y => Ty.fvar y))[i]? = some (Ty.fvar y) := by
                rw [List.getElem?_map]
                rw [hget]
                rfl
              have hb2 : Subst.onTy (Ws.zip (Ys.map (fun y => Ty.fvar y))) (.fvar (Ws[i])) = Ty.fvar y := by
                unfold Subst.onTy
                exact Ty.substFvars_zip_fvar_eq (by rw [List.length_map, hYs_def, freshVars_length, hWs_len])
                  hWs_nodup
                  (fun x hx hc => hWs_notYs x hx (Ty.mem_freeVarsList_map_fvar.mp hc))
                  hWsgeti hYsfvari
              rw [hb2]
            have hS₀'lc : ∀ p ∈ S₀', p.2.IsLC := by
              intro p hp
              rw [hS₀'_def] at hp
              rcases List.mem_append.mp hp with hp | hp
              · rcases List.mem_append.mp hp with hp | hp
                · obtain ⟨_, hpy⟩ := List.of_mem_zip hp
                  obtain ⟨w, _, hyeq⟩ := List.mem_map.mp hpy
                  simpa [hyeq] using (ContainsBvarsUpTo.fvar : (Ty.fvar w).IsLC)
                · exact hS₀ p hp
              · obtain ⟨_, hpy⟩ := List.of_mem_zip hp
                obtain ⟨y, _, hyeq⟩ := List.mem_map.mp hpy
                simpa [hyeq] using (ContainsBvarsUpTo.fvar : (Ty.fvar y).IsLC)
            have hKfix' : ∀ k ∈ K ++ Ys, S₀'.onTy (.fvar k) = .fvar k := by
              intro k hk
              rcases List.mem_append.mp hk with hk | hk
              · rw [hS₀'agree k (hKΦ k hk)]
                exact hKfix k hk
              · exact hS₀'Ys k hk
            have hren' : TypeOfHM (S₀'.onCtx ctx) (rhs.openTyVars Ys)
                (( σ).openVars Ys) := by
              have hctx : S₀'.onCtx ctx = S₀.onCtx ctx := Subst.onCtx_congr hS₀'agree hbelow
              rwa [← hctx] at hren
            obtain ⟨R₁, hR₁, htyr₁, hR₁K, hAgree₁⟩ :=
              ih.1 hrhs hsize_r hwf hbelowN hwf hbelowN S₀' (( σ).openVars Ys) (K ++ Ys)
                hS₀'lc hKΦ' hKrhsOpen hKfix' hren'
            -- STEP 3: factor `R₁` through the given MGU `huni` (app-arm pattern).
            have hR₁lc : ∀ p ∈ R₁, p.2.IsLC := hR₁
            have hR₁fixK : ∀ k ∈ K, R₁.onTy (.fvar k) = .fvar k := fun k hk => hR₁K k (List.mem_append_left _ hk)
            have hτ₁_lc : τ₁.IsLC := (Infer.lc hrhs hwf).1
            have hS₁lc : ∀ p ∈ S₁, p.2.IsLC := (Infer.lc hrhs hwf).2
            have hΦrhs : ∀ y ∈ (rhs.openTyVars Ys).tyFreeVars, y < N + σ.paramCount := fun y hy => by
              rcases Expr.tyFreeVars_openTyVars hy with h | h
              · have := hKΦ y (hKrhs y h); omega
              · exact hYs_lt y h
            obtain ⟨hτ₁_bel, hS₁_bel⟩ := Infer.belowFvars hrhs hbelowN hΦrhs
            have hσbody : Ty.BelowFvars Φ σ.body :=
              Ty.BelowFvars.of_freeVars_lt (fun v hv => hKΦ v (hKσ v hv))
            have hσbody₁ : Ty.BelowFvars Φ₁ σ.body := hσbody.mono (by omega)
            have hσopen : Ty.BelowFvars Φ₁ (σ.openVars Ys) :=
              Ty.openVars_belowFvars hσbody₁ (fun x hx => by
                have := freshVars_lt x (by simpa [Ys] using hx); omega)
            have hσopen_lc : (σ.openVars Ys).IsLC := PolyTy.openVars_isLC hσwf (by simp [Ys])
            have hSchk_lc : ∀ p ∈ Schk, p.2.IsLC := UnifyRel.lc huni hτ₁_lc hσopen_lc
            have hSchk_bel : ∀ p ∈ Schk, Ty.BelowFvars Φ₁ p.2 := UnifyRel.belowFvars huni hτ₁_bel hσopen
            have hR₁σopen : R₁.onTy (σ.openVars Ys) = σ.openVars Ys := by
              refine Subst.onTy_eq_self_of_fixes (fun v hv => ?_)
              rcases Ty.freeVars_openVars_subset v hv with h | h
              · exact hR₁K v (List.mem_append_left _ (hKσ v h))
              · exact hR₁K v (List.mem_append_right _ h)
            have hUnifiesR₁ : Unifies R₁ τ₁ (σ.openVars Ys) := by
              unfold Unifies
              rw [hR₁σopen]
              exact Eq.symm htyr₁
            obtain ⟨V, hV, hVlc, hVK⟩ := UnifyRel.greatest_K huni R₁ hR₁lc hUnifiesR₁ hR₁fixK
            -- STEP 4: assemble the agreement chain.
            have hAgreeRhs' : ∀ v, v < N + σ.paramCount →
                Eq (S₀'.onTy (.fvar v)) (R₁.onTy (S₁.onTy (.fvar v))) := by
              intro v hv
              rw [← Subst.onTy_append]
              exact hAgree₁ v hv
            have hAgreeV : Subst.AgreesBelow (N + σ.paramCount) S₀' ((S₁ ++ Schk) ++ V) := by
              intro v hv
              unfold S₀'
              rw [Subst.onTy_append, Subst.onTy_append, Subst.onTy_append]
              simpa [hS₀'_def, Subst.onTy_append] using Eq.trans (hAgreeRhs' v hv) (hV (S₁.onTy (.fvar v)))
            have hAgreeΦ : Subst.AgreesBelow Φ S₀ ((S₁ ++ Schk) ++ V) := by
              intro v hv
              rw [← hS₀'agree v hv]
              exact hAgreeV v (by omega)
            have hS₁_bel_all : ∀ p ∈ S₁ ++ Schk, Ty.BelowFvars Φ₁ p.2 := by
              intro p hp
              rcases List.mem_append.mp hp with hp | hp
              · exact hS₁_bel p hp
              · exact hSchk_bel p hp
            -- STEP 5: transport the body derivation to the V-world.
            have hwf₁ : CtxWF (S₁.onCtx ctx) := Subst.onCtx_wf hS₁lc hwf
            have hbelow₁ : CtxBelow Φ₁ (S₁.onCtx ctx) := Subst.onCtx_below hS₁_bel hfle hbelowN
            let bodyCtx_alg : Ctx := { (Schk.onCtx (S₁.onCtx ctx)) with
                env := σ :: (Schk.onCtx (S₁.onCtx ctx)).env }
            have hwf₁' : CtxWF bodyCtx_alg := by
              intro M hM; rcases List.mem_cons.mp hM with rfl | hM
              · exact hσwf
              · exact (Subst.onCtx_wf hSchk_lc hwf₁) M hM
            have hbelow₁' : CtxBelow Φ₁ bodyCtx_alg := by
              intro M hM; rcases List.mem_cons.mp hM with rfl | hM
              · exact hσbody₁
              · exact (Subst.onCtx_below hSchk_bel (le_refl _) hbelow₁) M hM
            have hσbodyV : V.onTy σ.body = σ.body := by
              refine Subst.onTy_eq_self_of_fixes (fun v hv => ?_)
              exact hVK v (hKσ v hv)
            have hhead :  (V.onPolyTy σ) =  σ := by
              simp [Subst.onPolyTy,  hσbodyV]
            have hctx_tail : (V.onCtx (Schk.onCtx (S₁.onCtx ctx))) = (S₀.onCtx ctx) := by
              rw [← Subst.onCtx_append, ← Subst.onCtx_append]
              simpa [List.append_assoc] using (Subst.onCtx_congr hAgreeΦ hbelow).symm
            have hbodyctx :
                (V.onCtx bodyCtx_alg)
                = { (V.onCtx (Schk.onCtx (S₁.onCtx ctx))) with
                    env :=  (V.onPolyTy σ)
                      :: (V.onCtx (Schk.onCtx (S₁.onCtx ctx))).env } := by
              simp only [bodyCtx_alg,  Subst.onCtx, Subst.onEnv,
                List.map_cons]
            have hbody_alg : TypeOfHM (V.onCtx bodyCtx_alg) body τe := by
              rw [hbodyctx, hctx_tail, hhead]
              exact hbodyD
            -- STEP 6: recurse on the body and assemble.
            obtain ⟨R₂, hR₂, htyb₂, hR₂K, hAgree₂⟩ :=
              ih.1 hbody hsize_b hwf₁' hbelow₁' hwf₁' hbelow₁' V τe K
                hVlc hKΦ₁ hKbody hVK hbody_alg
            have hAgree : Subst.AgreesBelow Φ S₀ ((S₁ ++ Schk ++ S₂) ++ R₂) :=
              @Subst.AgreesBelow.trans_append Φ Φ₁ S₀ (S₁ ++ Schk) V S₂ R₂
                (by omega) hAgreeΦ hS₁_bel_all hAgree₂
            refine ⟨R₂, hR₂, htyb₂, hR₂K, ?_⟩
            · simpa [List.append_assoc] using hAgree
      | @match_ Φ ctx scrut branches Φ₁ Φ₂ S₁ S₂ τs hscrut hne hbr =>
        exact fun hwf hbelow S₀ τe K hS₀ hKΦ hKe hKfix hty => by
          -- [match-agent]
          cases hty with
          | match_ hscrutD hneD hbrD =>
            rename_i scruT₀
            have hsize_scrut : scrut.size < n := by
              have := _hn
              simp [Expr.size] at this
              omega
            have hsize_br : Expr.sizeBranches branches < n := by
              have := _hn
              simp [Expr.size] at this
              omega
            have hKscrut : ∀ y ∈ scrut.tyFreeVars, y ∈ K := fun y hy => hKe y (by
              simp only [Expr.tyFreeVars, List.mem_append]; exact Or.inl hy)
            have hKbr : ∀ y ∈ Expr.tyFreeVars.BranchList.tyFreeVars branches, y ∈ K := fun y hy => hKe y (by
              simp only [Expr.tyFreeVars, List.mem_append]; exact Or.inr hy)
            have hτe_lc : τe.IsLC := by
              obtain ⟨hd, tl, hcons⟩ := List.exists_cons_of_ne_nil hne
              have hhd : (hd.1, hd.2) ∈ branches.map (fun pb => (pb.1, pb.2)) := by
                rw [hcons]
                exact List.mem_map.mpr ⟨hd, List.mem_cons_self, rfl⟩
              exact TypeOfMatchBranch.regular (hbrD hd (by simpa using hhd))
            -- STEP 1: scrutinee IH.
            obtain ⟨R₁, hR₁, hty₁, hR₁K, hAgree₁⟩ :=
              ih.1 hscrut hsize_scrut hwf hbelow hwf hbelow S₀ scruT₀ K hS₀ hKΦ hKscrut hKfix hscrutD
            have hfle : Φ ≤ Φ₁ := Infer.frontier_le hscrut
            have hKΦ₁ : ∀ k ∈ K, k < Φ₁ := fun k hk => lt_of_lt_of_le (hKΦ k hk) hfle
            obtain ⟨hτs_lc, hS₁lc⟩ := Infer.lc hscrut hwf
            have hscrut_below := Infer.belowFvars hscrut hbelow (fun y hy => hKΦ y (hKscrut y hy))
            have hτs_bel : Ty.BelowFvars Φ₁ τs := hscrut_below.1
            have hS₁_bel : ∀ p ∈ S₁, Ty.BelowFvars Φ₁ p.2 := hscrut_below.2
            have hwf₁ : CtxWF (S₁.onCtx ctx) := Subst.onCtx_wf hS₁lc hwf
            have hbelow₁' : CtxBelow Φ₁ (S₁.onCtx ctx) :=
              Subst.onCtx_below hS₁_bel hfle hbelow
            have hbelow₁ : CtxBelow (Φ₁ + 1) (S₁.onCtx ctx) :=
              Subst.onCtx_below (fun p hp => (hS₁_bel p hp).mono (by omega)) (by omega) hbelow
            have hscruT₀_lc : scruT₀.IsLC := TypeOfHM.regular hscrutD
            -- STEP 2: fresh `W` and the dodge `U = [(Φ₁, fvar W)] ++ R₁ ++ [(W, τe)]`.
            obtain ⟨W, hWge, hWfresh⟩ := exists_fresh_block
              (R₁.map Prod.fst ++ R₁.flatMap (fun p => p.2.freeVars) ++ τe.freeVars) Φ₁ 1
            have hWdom : ∀ p ∈ R₁, p.1 ≠ W := by
              intro p hp he
              have := hWfresh p.1 (by
                simp only [List.mem_append]
                exact Or.inl (Or.inl (List.mem_map.mpr ⟨p, hp, rfl⟩)))
              omega
            have hWrange : ∀ p ∈ R₁, W ∉ p.2.freeVars := by
              intro p hp hc
              have := hWfresh W (by
                simp only [List.mem_append]
                exact Or.inl (Or.inr (List.mem_flatMap.mpr ⟨p, hp, hc⟩)))
              omega
            have hWτe : W ∉ τe.freeVars := fun hc => by
              have := hWfresh W (by
                simp only [List.mem_append]
                exact Or.inr hc)
              omega
            have hR₁Wfvar : R₁.onTy (Ty.fvar W) = Ty.fvar W := by
              apply Ty.substFvars_eq_self_of_no_key
              intro p hp hc
              simp only [Ty.freeVars, List.mem_singleton] at hc
              exact hWdom p hp hc
            obtain ⟨U, hUdef⟩ : ∃ U : Subst, U = [(Φ₁, Ty.fvar W)] ++ R₁ ++ [(W, τe)] := ⟨_, rfl⟩
            have hsingle : ∀ (Z : Nat) (V y : Ty), Subst.onTy [(Z, V)] y = Ty.substFvar Z V y :=
              fun _ _ _ => rfl
            have hUonTy : ∀ x, U.onTy x = Ty.substFvar W τe (R₁.onTy (Ty.substFvar Φ₁ (Ty.fvar W) x)) := by
              intro x
              rw [hUdef, Subst.onTy_append, Subst.onTy_append, hsingle, hsingle]
            have hUlc : ∀ p ∈ U, p.2.IsLC := by
              rw [hUdef]
              intro p hp
              rcases List.mem_append.mp hp with hp' | hp'
              · rcases List.mem_append.mp hp' with hp'' | hp''
                · obtain rfl := List.mem_singleton.mp hp''
                  exact ContainsBvarsUpTo.fvar
                · exact hR₁ p hp''
              · obtain rfl := List.mem_singleton.mp hp'
                exact hτe_lc
            have hUK : ∀ k ∈ K, U.onTy (.fvar k) = .fvar k := by
              intro k hk
              have hklt : k < Φ₁ := hKΦ₁ k hk
              have hkΦ₁ : Φ₁ ∉ (Ty.fvar k).freeVars := by
                simp only [Ty.freeVars, List.mem_singleton]; omega
              have hkW : W ∉ (Ty.fvar k).freeVars := by
                simp only [Ty.freeVars, List.mem_singleton]; omega
              rw [hUonTy, Ty.substFvar_fresh hkΦ₁, hR₁K k hk, Ty.substFvar_fresh hkW]
            have hUΦ₁ : U.onTy (.fvar Φ₁) = τe := by
              rw [hUonTy,
                show Ty.substFvar Φ₁ (Ty.fvar W) (Ty.fvar Φ₁) = Ty.fvar W from by simp [Ty.substFvar],
                hR₁Wfvar,
                show Ty.substFvar W τe (Ty.fvar W) = τe from by simp [Ty.substFvar]]
            have hUeqR₁ : ∀ v, v < Φ₁ → U.onTy (Ty.fvar v) = R₁.onTy (Ty.fvar v) := by
              intro v hv
              have hvΦ₁ : Φ₁ ∉ (Ty.fvar v).freeVars := by simp only [Ty.freeVars, List.mem_singleton]; omega
              have hvW : W ∉ (R₁.onTy (Ty.fvar v)).freeVars := by
                apply Subst.not_mem_onTy_freeVars hWrange
                simp only [Ty.freeVars, List.mem_singleton]; omega
              rw [hUonTy, Ty.substFvar_fresh hvΦ₁, Ty.substFvar_fresh hvW]
            have hUagreeR₁ : Subst.AgreesBelow Φ₁ U R₁ :=
              fun v hv => by rw [hUeqR₁ v hv]
            -- STEP 3: recast the branch premises (context rewrite only; types unchanged).
            have hctxeq : (U.onCtx (S₁.onCtx ctx)) = (S₀.onCtx ctx) := by
              have h1 : (U.onCtx (S₁.onCtx ctx)) = (R₁.onCtx (S₁.onCtx ctx)) := by
                exact Subst.onCtx_congr hUagreeR₁ hbelow₁'
              have h2 : (R₁.onCtx (S₁.onCtx ctx)) = (S₀.onCtx ctx) := by
                rw [← Subst.onCtx_append]
                exact (Subst.onCtx_congr hAgree₁ hbelow).symm
              exact h1.trans h2
            have hbr' : ∀ b ∈ branches, TypeOfMatchBranch (U.onCtx (S₁.onCtx ctx))
                (b.1, b.2) scruT₀ τe := by
              intro b hb
              rw [hctxeq]
              exact hbrD b hb
            -- the two image premises (reflexive at this call).
            have hIMGτe : Eq τe (U.onTy (.fvar Φ₁)) := by
              rw [hUΦ₁]
            have hIMGscru : Eq scruT₀ (U.onTy τs) :=
              Eq.trans hty₁ (Subst.onTy_congr hUagreeR₁ hτs_bel |>.symm)
            have hbτs : Ty.BelowFvars (Φ₁ + 1) τs := hτs_bel.mono (by omega)
            have hbρ : Ty.BelowFvars (Φ₁ + 1) (.fvar Φ₁) := Ty.BelowFvars.fvar (by omega)
            have hKΦ' : ∀ k ∈ K, k < Φ₁ + 1 := fun k hk => lt_of_lt_of_le (hKΦ₁ k hk) (by omega)
            -- STEP 4: the branch tier.
            obtain ⟨R₂, hR₂, hAgree₂, hR₂K, hty₂⟩ :=
              ih.2.1 hbr hne hsize_br hwf₁ hbelow₁ hwf₁ hbelow₁ U scruT₀ τe K
                hUlc hscruT₀_lc hτs_lc ContainsBvarsUpTo.fvar hbτs hbρ hKΦ' hKbr hUK hIMGτe hIMGscru hbr'
            -- STEP 5: assemble.
            have hAgree₂' : Subst.AgreesBelow Φ₁ R₁ (S₂ ++ R₂) := by
              intro v hv
              exact Eq.trans (hUagreeR₁ v hv).symm (hAgree₂ v (by omega))
            have hAgree : Subst.AgreesBelow Φ S₀ ((S₁ ++ S₂) ++ R₂) :=
              @Subst.AgreesBelow.trans_append Φ Φ₁ S₀ S₁ R₁ S₂ R₂ hfle hAgree₁ hS₁_bel hAgree₂'
            refine ⟨R₂, hR₂, hty₂, hR₂K, ?_⟩
            · simpa [List.append_assoc] using hAgree
      | @letRec Φ ctx anns bindings body Φ₁ Φ₂ S₁ Sc S₂ τ₂ Kc G specs1 specsC
          hannswf hgroup hspecs1 hG hSc hspecsC hceiling hbody =>
        exact fun hwf hbelow S₀ τe K hS₀ hKΦ hKe hKfix hty => by
          -- COMPLETE-LETREC (all-mono cut; R₀ via the block residual, body via the
          -- erase-level retype of `letRecFused_body_retype`).
          rw [] at hty
          cases hty with
          | letRec hwfD hlenD hlinkD hlcD hmonoD hceilingD hbodyCtxD hbodyD =>
            rename_i dspecs τsD Gdecl L
            subst hbodyCtxD
            have hsize_group : Expr.sizeRecGroup bindings < n := by
              have := _hn
              simp only [Expr.size] at this
              omega
            have hsize_body : body.size < n := by
              have := _hn
              simp only [Expr.size] at this
              omega
            have hKgrp : ∀ y ∈ Expr.tyFreeVars.RecGroup.tyFreeVars bindings, y ∈ K := fun y hy => hKe y (by
              simp only [Expr.tyFreeVars, List.mem_append]; exact Or.inl (Or.inr hy))
            have hKbody : ∀ y ∈ body.tyFreeVars, y ∈ K := fun y hy => hKe y (by
              simp only [Expr.tyFreeVars, List.mem_append]; exact Or.inr hy)
            have hlen_τsD : bindings.length = τsD.length := by
              simpa [List.length_map] using hlenD
            have hdspec_len : dspecs.length = bindings.length := by
              simpa [List.length_map] using hwfD.length.symm
            have hlen_ab : anns.length = bindings.length := by
              have h1 := InferRecGroup.length_eq hgroup
              rw [RecSpec.init_length] at h1
              exact h1.symm
            have hKrigid : ∀ y ∈ RecGroup.rigidVars anns bindings, y ∈ K := by
              intro y hy
              rcases List.mem_append.mp hy with hy | hy
              · exact hKe y (List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl hy))))
              · have hy' : y ∈ Expr.tyFreeVars.RecGroup.tyFreeVars bindings :=
                  (mem_recGroup_tyFreeVars (bindings := bindings)).mpr hy
                exact hKe y (List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inr hy'))))
            -- fresh shared pool opening for the declarative MonoTypedInit
            let XavoidPool :=
              (L ++ Gdecl ++ dspecs.flatMap RecSpec.monoFreeVars ++
                (S₀.onCtx ctx).env.freeVars ++ K) ++ Ty.freeVarsList τsD
            obtain ⟨Xs, hXlen, hXnodup, hXavoid⟩ := exists_fresh_names
              XavoidPool Gdecl.length
            have hXL : ∀ x ∈ Xs, x ∉ L := fun x hx hc => hXavoid x hx (by
              dsimp [XavoidPool]
              simp only [List.mem_append]
              tauto)
            have hXG : ∀ g ∈ Gdecl, g ∉ Xs := fun g hg hc => hXavoid g hc (by
              dsimp [XavoidPool]
              simp only [List.mem_append]
              tauto)
            have hXτs : ∀ x ∈ Xs, ∀ τ, RecSpec.mono τ ∈ dspecs → x ∉ τ.freeVars := fun x hx τ hτ hc =>
              hXavoid x hx (by
                dsimp [XavoidPool]
                simp only [List.mem_append]
                exact Or.inl (Or.inl (Or.inl
                  (Or.inr (List.mem_flatMap.mpr ⟨RecSpec.mono τ, hτ, hc⟩)))))
            have hXτsD : ∀ x ∈ Xs, ∀ τ ∈ τsD, x ∉ τ.freeVars := by
              intro x hx τ hτ hc
              exact hXavoid x hx (by
                dsimp [XavoidPool]
                exact List.mem_append.mpr (Or.inr (Ty.mem_freeVarsList_of_mem hτ hc)))
            have hXenv : ∀ x ∈ Xs, x ∉ (S₀.onCtx ctx).env.freeVars := fun x hx hc =>
              hXavoid x hx (by dsimp [XavoidPool]; simp only [List.mem_append]; tauto)
            have hXK : ∀ x ∈ Xs, x ∉ K := fun x hx hc => hXavoid x hx (by
              dsimp [XavoidPool]
              simp only [List.mem_append]
              tauto)
            have hXfresh : FreshNames L Gdecl.length Xs := ⟨hXlen, hXnodup, hXL⟩
            have hXrigid : ∀ x ∈ Xs, x ∉ RecGroup.rigidVars anns bindings := fun x hx hc =>
              hXK x hx (hKrigid x hc)
            -- the residual targets: the opened witnesses
            set vs : List Ty := τsD.map (fun τ => Ty.renameG Gdecl Xs τ) with hvs_def
            have hvs_len : vs.length = bindings.length := by
              rw [hvs_def, List.length_map]
              exact hlen_τsD.symm
            have hvs_lc : ∀ t ∈ vs, t.IsLC := by
              intro t ht
              rw [hvs_def] at ht
              obtain ⟨τ, hτ, rfl⟩ := List.mem_map.mp ht
              change (Ty.renameG Gdecl Xs τ).IsLC
              change (Subst.onTy (Gdecl.zip (Xs.map (Ty.fvar ·))) τ).IsLC
              exact Subst.onTy_lc (fun p hp => by
                obtain ⟨w, _, hw⟩ := List.mem_map.mp (List.of_mem_zip hp).2
                rw [← hw]; exact ContainsBvarsUpTo.fvar) (hlcD τ hτ)
            obtain ⟨R₀, hR₀lc, hR₀K, hR₀ag, hR₀block⟩ :=
              exists_recgroup_residual (Φ := Φ) (n := bindings.length) (S₀ := S₀) (vs := vs) (K := K)
                hvs_len hS₀ hvs_lc hKΦ hKfix
            -- the block realisation, positionally: R₀.onTy (fvar (Φ+j)) = renameG G Xs (τsD[j])
            have hR₀blockj : ∀ j (hj : j < bindings.length),
                R₀.onTy (Ty.fvar (Φ + j)) = Ty.renameG Gdecl Xs (τsD[j]'(by rw [← hlen_τsD]; exact hj)) := by
              intro j hj
              have hjT : j < τsD.length := by
                rw [← hlen_τsD]
                exact hj
              have h := congrArg (fun l => l[j]?) hR₀block
              change (List.map R₀.onTy (List.map Ty.fvar (freshVars Φ bindings.length)))[j]? = vs[j]? at h
              rw [List.getElem?_map, List.getElem?_map] at h
              have hfj : (freshVars Φ bindings.length)[j]'(by simpa [freshVars_length] using hj) = Φ + j := by
                simp only [freshVars, List.getElem_map, List.getElem_range]
              rw [List.getElem?_eq_getElem (by simpa [freshVars_length] using hj), hfj] at h
              rw [hvs_def] at h
              rw [List.getElem?_map] at h
              rw [List.getElem?_eq_getElem hjT] at h
              exact Option.some.inj h
            -- the group context invariants
            set groupCtx : Ctx := { ctx with
                env := (RecSpec.init Φ anns).map (RecSpec.rhsEntry [] []) ++ ctx.env } with hgroupCtx_def
            have hinitLC : ∀ s ∈ RecSpec.init Φ anns, s.LC := by
              intro s hs
              rcases RecSpec.mem_init hs with ⟨m, _, _, rfl⟩ | ⟨σ, hσ, rfl⟩
              · exact ContainsBvarsUpTo.fvar
              · exact hannswf σ hσ
            have hinitB : ∀ s ∈ RecSpec.init Φ anns, ∀ τm, s = RecSpec.mono τm →
                Ty.BelowFvars (Φ + bindings.length) τm := by
              intro s hs τm hτm
              rcases RecSpec.mem_init hs with ⟨m, hm1, hm2, rfl⟩ | ⟨σ, hσ, rfl⟩
              · cases hτm
                refine Ty.BelowFvars.of_freeVars_lt (fun v hv => ?_)
                simp only [Ty.freeVars, List.mem_singleton] at hv
                omega
              · exact absurd hτm (by simp)
            have hctxgWF : CtxWF groupCtx := by
              intro M hM
              rcases List.mem_append.mp hM with hM | hM
              · obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hM
                exact RecSpec.rhsEntry_nil_wf (hinitLC s hs)
              · exact hwf M hM
            have hctxgBelow : CtxBelow (Φ + bindings.length) groupCtx := by
              intro M hM
              rcases List.mem_append.mp hM with hM | hM
              · obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hM
                rcases RecSpec.mem_init hs with ⟨m, hm1, hm2, rfl⟩ | ⟨σ, hσ, rfl⟩
                · change Ty.BelowFvars (Φ + bindings.length) (Ty.fvar m)
                  exact Ty.BelowFvars.fvar (by omega)
                · refine Ty.BelowFvars.of_freeVars_lt (fun y hy => ?_)
                  have hK := hKe y (List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl
                    (Expr.scheme_body_mem_annList_tyFreeVars hσ hy)))))
                  have := hKΦ y hK
                  omega
              · exact (hbelow M hM).mono (by omega)
            have hAgree : ∀ v, v < Φ → Eq (R₀.onTy (.fvar v)) (S₀.onTy (.fvar v)) := fun v hv =>
              hR₀ag v hv
            -- the mono premise (per-member, at the R₀-transported group context)
            have hMonoMem : ∀ p ∈ bindings.zip (RecSpec.init Φ anns), ∀ τm,
                p.2 = RecSpec.mono τm →
                TypeOfHM (R₀.onCtx groupCtx) ( p.1)
                  ( (R₀.onTy τm)) := by
              intro p hp τm hτm
              rcases List.mem_iff_getElem.mp hp with ⟨j, hjp, hpeq⟩
              have hjl1 : j < bindings.length := by
                rw [List.length_zip] at hjp; exact lt_of_lt_of_le hjp (min_le_left _ _)
              have hjl2 : j < (RecSpec.init Φ anns).length := by
                rw [List.length_zip] at hjp; exact lt_of_lt_of_le hjp (min_le_right _ _)
              have hpeq' : (bindings[j]'hjl1, (RecSpec.init Φ anns)[j]'hjl2) = p := by
                rw [List.getElem_zip] at hpeq
                exact hpeq
              have hinit_j : (RecSpec.init Φ anns)[j]'hjl2 = RecSpec.mono (Ty.fvar (Φ + j)) := by
                have hg : (RecSpec.init Φ anns)[j]? = (anns[j]?).map (fun _ => RecSpec.mono (Ty.fvar (Φ + j))) :=
                  RecSpec.init_getElem? Φ anns j
                rw [List.getElem?_eq_getElem hjl2] at hg
                have hjA : j < anns.length := by
                  rw [hlen_ab]
                  exact hjl1
                have hann : anns[j]? = some (anns[j]'(hjA)) := by rw [List.getElem?_eq_getElem hjA]
                rw [hann] at hg
                simpa using hg
              have hτm' : τm = Ty.fvar (Φ + j) := by
                have hf := congrArg Prod.snd hpeq'
                exact (RecSpec.mono.inj (by simpa [hinit_j, hτm] using hf)).symm
              subst hτm'
              have hjT : j < τsD.length := by
                rw [← hlen_τsD]
                exact hjl1
              have hjBE : j < bindings.length := by
                exact hjl1
              let bE : Expr := bindings[j]'(hjBE)
              let tD : Ty := τsD[j]'(hjT)
              have hmemD : (bE, tD) ∈ bindings.zip τsD := by
                exact getElem_mem_zip j hjBE hjT
              have hdecl0 := hmonoD Xs hXfresh (bE, tD) hmemD
              have hdeclE := hdecl0
              have hctxE : (RecSpecs.rhsCtx (S₀.onCtx ctx) (τsD.map RecSpec.mono) Gdecl Xs)
                  = (R₀.onCtx groupCtx) := by
                simp only [RecSpecs.rhsCtx, groupCtx, Subst.onCtx, Subst.onEnv, List.map_append]
                congr 1
                · rw [List.map_map, List.map_map]
                  congr 1
                  · refine List.ext_getElem ?_ (fun k hk1 hk2 => ?_)
                    · simp only [List.length_map, RecSpec.init_length]
                      rw [hlen_ab, ← hlen_τsD]
                    have hk2_len : k < τsD.length := by
                      simp only [List.length_map, RecSpec.init_length] at hk2
                      rw [hlen_ab] at hk2
                      rw [← hlen_τsD]; exact hk2
                    have hkB : k < bindings.length := by
                      rw [hlen_τsD]
                      exact hk2_len
                    have hkA : k < anns.length := by
                      rw [hlen_ab]
                      exact hkB
                    have hinit_k : (RecSpec.init Φ anns)[k]'(by simpa [RecSpec.init_length] using hkA)
                        = RecSpec.mono (Ty.fvar (Φ + k)) := by
                      have hg : (RecSpec.init Φ anns)[k]? = (anns[k]?).map (fun _ => RecSpec.mono (Ty.fvar (Φ + k))) :=
                        RecSpec.init_getElem? Φ anns k
                      rw [List.getElem?_eq_getElem (by simpa [RecSpec.init_length] using hkA)] at hg
                      rw [List.getElem?_eq_getElem hkA] at hg
                      simpa using hg
                    have hblk : R₀.onTy (Ty.fvar (Φ + k)) = Ty.renameG Gdecl Xs (τsD[k]'hk2_len) := hR₀blockj k hkB
                    have hblkE : PolyTy.mkTrivial (Ty.renameG Gdecl Xs (τsD[k]'hk2_len)) = PolyTy.mkTrivial (R₀.onTy (Ty.fvar (Φ + k))) := by
                      exact congrArg PolyTy.mkTrivial hblk.symm
                    simp only [List.getElem_map, Function.comp_apply, RecSpec.rhsEntry, hinit_k, Subst.onPolyTy, Ty.renameG_nil_pool, PolyTy.mkTrivial]
                    exact hblkE
                  · refine List.ext_getElem (by simp) (fun k hk1 hk2 => ?_)
                    have hklen : k < ctx.env.length := by simpa using hk2
                    have hMem : ctx.env[k]'hklen ∈ ctx.env := List.getElem_mem hklen
                    have hM' : (ctx.env[k]'hklen) ∈ ctx.env := hMem
                    simp only [List.getElem_map, Function.comp_apply,
                      Subst.onPolyTy]
                    have hrec : (PolyTy.mk (ctx.env[k]'hklen |>.paramCount)
                            ( ( (S₀.onTy (ctx.env[k]'hklen).body))))
                        = (PolyTy.mk (ctx.env[k]'hklen |>.paramCount)
                            ( (R₀.onTy (ctx.env[k]'hklen).body))) := by
                      refine congrArg₂ PolyTy.mk rfl ?_
                      exact Subst.onTy_congr
                        (fun v hv => Eq.symm (hAgree v hv))
                        (hbelow _ hM')
                    exact hrec
              have htyE :  (Ty.renameG Gdecl Xs (τsD[j]'hjT))
                  =  (R₀.onTy (Ty.fvar (Φ + j))) := by
                exact (hR₀blockj j hjl1).symm
              rw [hctxE] at hdeclE
              rw [htyE] at hdeclE
              have hp1 : p.1 = bindings[j]'hjl1 := by
                exact (congrArg Prod.fst hpeq').symm
              have hbE : bE = (bindings[j]'hjl1) := by
                simp [bE]
              rw [hbE, ← hp1] at hdeclE
              exact hdeclE
            -- the tier call (R₀ is the ambient; Φ₀ = Φ the pre-block frontier)
            have hKschInit : ∀ s ∈ RecSpec.init Φ anns, ∀ σ, s = RecSpec.poly σ →
                ∀ y ∈ σ.body.freeVars, y ∈ K := by
              intro s hs σ hσ
              rcases RecSpec.mem_init hs with ⟨m, _, _, rfl⟩ | ⟨σ', hσ2, rfl⟩
              · exact absurd hσ (by simp)
              · intro y hy
                have hσ_eq : σ = σ' := RecSpec.poly.inj hσ.symm
                subst hσ_eq
                exact hKe y (List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl
                  (Expr.scheme_body_mem_annList_tyFreeVars hσ2 hy)))))
            obtain ⟨R_g, hR_g, hR_gK, hAgreeTier, hAgreeTierR⟩ :=
              ih.2.2 hgroup (by omega) hsize_group hctxgWF hctxgBelow hctxgWF hctxgBelow S₀ L K R₀
                hS₀ hKΦ hKgrp hKfix hinitLC hinitB hKschInit hR₀lc hR₀K hAgree hMonoMem (by
                  -- poly premise: vacuous over all-mono init specs
                  intro p hp σ hσ
                  rcases List.mem_iff_getElem.mp hp with ⟨j, hjp, hpeq⟩
                  have hjl2 : j < (RecSpec.init Φ anns).length := by
                    rw [List.length_zip] at hjp; exact lt_of_lt_of_le hjp (min_le_right _ _)
                  have hf := congrArg Prod.snd hpeq
                  rw [List.getElem_zip] at hf
                  have hinit' : (RecSpec.init Φ anns)[j]'hjl2 = RecSpec.mono (Ty.fvar (Φ + j)) := by
                    have hjA : j < anns.length := by
                      rw [hlen_ab]
                      rw [List.length_zip] at hjp
                      exact lt_of_lt_of_le hjp (min_le_left _ _)
                    have hg : (RecSpec.init Φ anns)[j]? = (anns[j]?).map (fun _ => RecSpec.mono (Ty.fvar (Φ + j))) :=
                      RecSpec.init_getElem? Φ anns j
                    rw [List.getElem?_eq_getElem hjl2, List.getElem?_eq_getElem hjA] at hg
                    simpa using hg
                  rw [hinit', hσ] at hf
                  simp at hf)
            -- the body: transport the declarative body typing to the algorithmic
            -- ceilingSchemes context, then recurse.
            have hbodyE : TypeOfHM (RecSpecs.bodyCtx (S₀.onCtx ctx) dspecs Gdecl)
                body ( τe) := by
              exact hbodyD
            have hdlc : ∀ τ, RecSpec.mono τ ∈ dspecs → τ.IsLC := by
              intro τ hτ
              exact hwfD.mono_lc τ hτ
            have hanns_eq : dspecs.map RecSpec.ann = anns := by
              simpa [hwfD.anns_eq]
            have hctxS₁ : (R_g.onCtx (S₁.onCtx ctx)) = (S₀.onCtx ctx) := by
              rw [← Subst.onCtx_append]
              exact (Subst.onCtx_congr hAgreeTier hbelow).symm
            have hS₁lc : ∀ p ∈ S₁, p.2.IsLC :=
              InferRecGroup.lc hgroup hctxgWF hinitLC
            have htfv_below : ∀ y ∈ Expr.tyFreeVars.RecGroup.tyFreeVars bindings,
                y < Φ + bindings.length := fun y hy =>
              Nat.lt_add_right bindings.length (hKΦ y (hKgrp y hy))
            have hinit_bel : ∀ s ∈ RecSpec.init Φ anns,
                RecSpec.BelowFvars (Φ + bindings.length) s := by
              intro s hs
              rcases RecSpec.mem_init hs with ⟨m, _, _, hs'⟩ | ⟨σ, hσ, hs'⟩
              · subst hs'; exact hinitB _ hs _ rfl
              · subst hs'
                exact Ty.BelowFvars.of_freeVars_lt (fun y hy =>
                  Nat.lt_add_right bindings.length (hKΦ y (hKe y
                    (List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl
                      (Expr.scheme_body_mem_annList_tyFreeVars hσ hy))))))))
            have hS₁_bel : ∀ p ∈ S₁, Ty.BelowFvars Φ₁ p.2 :=
              InferRecGroup.belowFvars hgroup hctxgBelow hinit_bel htfv_below
            have hgle : Φ + bindings.length ≤ Φ₁ := InferRecGroup.frontier_le hgroup
            have hKΦ₁ : ∀ k ∈ K, k < Φ₁ := fun k hk =>
              lt_of_lt_of_le (hKΦ k hk)
                (le_trans (Nat.le_add_right Φ bindings.length) hgle)
            have hrigidBelow : ∀ x ∈ RecGroup.rigidVars anns bindings, x < Φ₁ :=
              fun x hx => hKΦ₁ x (hKrigid x hx)
            have hspecs1LC : ∀ s ∈ specs1, s.LC := by
              intro s hs
              rw [hspecs1] at hs
              obtain ⟨s₀, hs₀, rfl⟩ := List.mem_map.mp hs
              exact RecSpec.LC.onSubst hS₁lc (hinitLC s₀ hs₀)
            have hspecs1Below : ∀ s ∈ specs1, s.BelowFvars Φ₁ := by
              intro s hs
              rw [hspecs1] at hs
              obtain ⟨s₀, hs₀, rfl⟩ := List.mem_map.mp hs
              exact RecSpec.BelowFvars.onSubst hS₁_bel ((hinit_bel s₀ hs₀).mono hgle)
            have hGnodup : G.Nodup := by
              rw [hG]
              exact genGroupVars_nodup
            have hGrigid : ∀ g ∈ G, g ∉ RecGroup.rigidVars anns bindings := by
              intro g hg
              rw [hG] at hg
              simp only [genGroupVars, List.mem_filter, Bool.and_eq_true,
                Bool.not_eq_eq_eq_not, Bool.not_true, List.contains_eq_mem,
                decide_eq_false_iff_not] at hg
              exact hg.2.2
            have hScdom : ∀ p ∈ Sc, p.1 ∉ G := fun p hp =>
              (hSc.dom_avoids p hp).2.2
            have hScrange : ∀ p ∈ Sc, ∀ u ∈ p.2.freeVars, u ∉ G :=
              hSc.range_avoids_pool
            have hσfix : ∀ σ, some σ ∈ anns → R_g.onPolyTy σ = σ := by
              intro σ hσ
              simp only [Subst.onPolyTy]
              rw [Subst.onTy_eq_self_of_fixes (fun v hv => hR_gK v (hKe v (List.mem_append.mpr (Or.inl
                (List.mem_append.mpr (Or.inl (Expr.scheme_body_mem_annList_tyFreeVars hσ hv)))))))]
            have hconnAll : ∀ (j : Nat) (hj : j < bindings.length),
              Subst.onTy (R_g)
                  ( (S₁.onTy (Ty.fvar (Φ + j))))
                = Ty.renameG Gdecl Xs
                    ( (τsD[j]'(by rw [← hlen_τsD]; exact hj))) := by
              intro j hj
              have hjT : j < τsD.length := by rw [← hlen_τsD]; exact hj
              have hblockAgree : Eq (R₀.onTy (Ty.fvar (Φ + j)))
                  (R_g.onTy (S₁.onTy (Ty.fvar (Φ + j)))) := by
                rw [← Subst.onTy_append]
                exact hAgreeTierR (Φ + j) (by omega)
              have h3 : Subst.onTy (R_g)
                  ( (S₁.onTy (Ty.fvar (Φ + j))))
                  =  (R_g.onTy (S₁.onTy (Ty.fvar (Φ + j)))) := by
                rfl
              rw [h3]
              calc
                 (R_g.onTy (S₁.onTy (Ty.fvar (Φ + j))))
                    =  (R₀.onTy (Ty.fvar (Φ + j))) := hblockAgree.symm
                _ = Ty.renameG Gdecl Xs ( (τsD[j]'hjT)) := by
                  rw [hR₀blockj j hj]
            have hconnB : ∀ (j : Nat) (hj : j < dspecs.length) (τdecl : Ty),
                dspecs[j]'hj = RecSpec.mono τdecl →
              Subst.onTy (R_g)
                  ( (S₁.onTy (Ty.fvar (Φ + j))))
                = Ty.renameG Gdecl Xs ( τdecl) := by
              intro j hj τdecl hτdecl
              have hjl : j < bindings.length := by
                rw [← hdspec_len]
                exact hj
              have hjT : j < τsD.length := by rw [← hlen_τsD]; exact hjl
              have hlinkτ : τdecl = τsD[j]'hjT := by
                have hmemD : (RecSpec.mono τdecl, τsD[j]'hjT) ∈ dspecs.zip τsD := by
                  simpa [hτdecl] using (getElem_mem_zip j hj hjT)
                exact (hlinkD (RecSpec.mono τdecl, τsD[j]'hjT) hmemD τdecl rfl).symm
              simpa [hlinkτ] using hconnAll j hjl
            set Rer : Subst :=
              R_g with hRer_def
            have hRerlc : ∀ p ∈ Rer, p.2.IsLC := by
              simpa [Rer] using hR_g
            have hgenInit : CeilingGenInv G R_g anns specs1 := by
              intro ann spec hp
              cases ann with
              | none => cases spec <;> trivial
              | some σ =>
                cases spec with
                | poly σ' =>
                  rcases List.mem_iff_getElem.mp hp with ⟨j, hjp, hpeq⟩
                  have hjS : j < specs1.length := by
                    rw [List.length_zip] at hjp
                    exact lt_of_lt_of_le hjp (min_le_right _ _)
                  have hjA : j < anns.length := by
                    rw [List.length_zip] at hjp
                    exact lt_of_lt_of_le hjp (min_le_left _ _)
                  rw [List.getElem_zip] at hpeq
                  have hspecj : specs1[j]'hjS = RecSpec.poly σ' := congrArg Prod.snd hpeq
                  have hinitj : (RecSpec.init Φ anns)[j]'(by
                      simpa [RecSpec.init_length] using hjA) =
                      RecSpec.mono (Ty.fvar (Φ + j)) := by
                    have hg := RecSpec.init_getElem? Φ anns j
                    rw [List.getElem?_eq_getElem (by
                      simpa [RecSpec.init_length] using hjA),
                      List.getElem?_eq_getElem hjA] at hg
                    simpa using hg
                  have hs1j : specs1[j]'hjS =
                      RecSpec.mono (S₁.onTy (Ty.fvar (Φ + j))) := by
                    have hs := congrArg (fun l => l[j]?) hspecs1
                    change specs1[j]? =
                      ((RecSpec.init Φ anns).map (RecSpec.onSubst S₁))[j]? at hs
                    rw [List.getElem?_eq_getElem hjS, List.getElem?_map,
                      List.getElem?_eq_getElem (by simpa [RecSpec.init_length] using hjA),
                      hinitj] at hs
                    exact Option.some.inj hs
                  rw [hs1j] at hspecj
                  simp at hspecj
                | mono τinf =>
                  rcases List.mem_iff_getElem.mp hp with ⟨j, hjp, hpeq⟩
                  have hjA : j < anns.length := by
                    rw [List.length_zip] at hjp
                    exact lt_of_lt_of_le hjp (min_le_left _ _)
                  have hjS : j < specs1.length := by
                    rw [List.length_zip] at hjp
                    exact lt_of_lt_of_le hjp (min_le_right _ _)
                  rw [List.getElem_zip] at hpeq
                  have hannj : anns[j]'hjA = some σ := congrArg Prod.fst hpeq
                  have hspecj : specs1[j]'hjS = RecSpec.mono τinf := congrArg Prod.snd hpeq
                  have hjB : j < bindings.length := by rw [← hlen_ab]; exact hjA
                  have hjT : j < τsD.length := by rw [← hlen_τsD]; exact hjB
                  have hinitj : (RecSpec.init Φ anns)[j]'(by
                      simpa [RecSpec.init_length] using hjA) =
                      RecSpec.mono (Ty.fvar (Φ + j)) := by
                    have hg := RecSpec.init_getElem? Φ anns j
                    rw [List.getElem?_eq_getElem (by
                      simpa [RecSpec.init_length] using hjA),
                      List.getElem?_eq_getElem hjA] at hg
                    simpa using hg
                  have hτinf : τinf = S₁.onTy (Ty.fvar (Φ + j)) := by
                    have hs1j : specs1[j]'hjS =
                        RecSpec.mono (S₁.onTy (Ty.fvar (Φ + j))) := by
                      have hs := congrArg (fun l => l[j]?) hspecs1
                      change specs1[j]? =
                        ((RecSpec.init Φ anns).map (RecSpec.onSubst S₁))[j]? at hs
                      rw [List.getElem?_eq_getElem hjS, List.getElem?_map,
                        List.getElem?_eq_getElem (by simpa [RecSpec.init_length] using hjA),
                        hinitj] at hs
                      exact Option.some.inj hs
                    exact RecSpec.mono.inj (hspecj.symm.trans hs1j)
                  subst τinf
                  have hτalgMem : RecSpec.mono (S₁.onTy (Ty.fvar (Φ + j))) ∈ specs1 :=
                    hspecj ▸ List.getElem_mem hjS
                  have hτDmem : τsD[j]'hjT ∈ τsD := List.getElem_mem hjT
                  have hceilMem :
                      (some ( σ), RecSpec.mono (τsD[j]'hjT)) ∈
                        (anns).zip
                          (τsD.map RecSpec.mono) := by
                    have hm := getElem_mem_zip
                      (as := anns)
                      (bs := τsD.map RecSpec.mono) j (by simpa using hjA) (by simpa using hjT)
                    simpa only [List.getElem_map, hannj, Option.map_some] using hm
                  have hdeclGen := hceilingD.of_mem_zip hceilMem
                  have hdeclGen' :
                      ( (PolyTy.genGroup Gdecl (τsD[j]'hjT))).Generalizes
                        ( σ) := by
                    exact hdeclGen
                  have hτalgLC : (S₁.onTy (Ty.fvar (Φ + j))).IsLC :=
                    Subst.onTy_lc hS₁lc ContainsBvarsUpTo.fvar
                  have hconnj : Rer.onTy
                        ( (S₁.onTy (Ty.fvar (Φ + j)))) =
                      Ty.renameG Gdecl Xs ( (τsD[j]'hjT)) := by
                    simpa [hRer_def] using hconnAll j hjB
                  have hXinf : ∀ x ∈ Xs, x ∉
                      (Rer.onPolyTy (PolyTy.genGroup G
                        ( (S₁.onTy (Ty.fvar (Φ + j)))))).body.freeVars := by
                    intro x hx hmem
                    change x ∈ (Rer.onTy (Ty.closeOver (Ty.genFilter G
                      ( (S₁.onTy (Ty.fvar (Φ + j)))))
                      ( (S₁.onTy (Ty.fvar (Φ + j)))))).freeVars at hmem
                    obtain ⟨v, hv, hxv⟩ := Ty.mem_freeVars_onTy_iff.mp hmem
                    have hvτ : v ∈ (
                        (S₁.onTy (Ty.fvar (Φ + j)))).freeVars :=
                      Ty.freeVars_closeOver_subset hv
                    have hvτ' : v ∈ (S₁.onTy (Ty.fvar (Φ + j))).freeVars :=
                      hvτ
                    have hvG : v ∉ G := by
                      intro hvg
                      exact Ty.not_mem_closeOver_freeVars
                        (by simp only [Ty.genFilter, List.mem_filter, decide_eq_true_eq]
                            exact ⟨hvg, hvτ⟩) hv
                    have hvMono : v ∈ Ty.freeVarsList (RecSpecs.monoTys specs1) :=
                      mem_freeVarsList_monoTys (mem_monoTys_of_mem_solved hτalgMem) hvτ'
                    have hcase : v ∈ (S₁.onCtx ctx).env.freeVars ∨
                        v ∈ RecGroup.rigidVars anns bindings := by
                      by_contra hcon
                      push_neg at hcon
                      apply hvG
                      rw [hG]
                      simp only [genGroupVars, List.mem_filter, Bool.and_eq_true,
                        Bool.not_eq_eq_eq_not, Bool.not_true, List.contains_eq_mem,
                        decide_eq_false_iff_not]
                      exact ⟨hvMono, hcon.1, hcon.2⟩
                    rcases hcase with henv | hrigid
                    · obtain ⟨pt, hpt, hvpt⟩ := Env.mem_freeVars_iff.mp henv
                      have hxv' : x ∈ (R_g.onTy (Ty.fvar v)).freeVars := by
                        have heq : Rer.onTy (Ty.fvar v) =
                             (R_g.onTy (Ty.fvar v)) := by
                          rfl
                        rw [heq] at hxv
                        exact hxv
                      have hxOnTy : x ∈ (R_g.onTy pt.body).freeVars :=
                        Ty.mem_freeVars_onTy_iff.mpr ⟨v, hvpt, hxv'⟩
                      have hm : R_g.onPolyTy pt ∈ (R_g.onCtx (S₁.onCtx ctx)).env := by
                        simp only [Subst.onCtx, Subst.onEnv]
                        exact List.mem_map.mpr ⟨pt, hpt, rfl⟩
                      have hxEnv : x ∈ (R_g.onCtx (S₁.onCtx ctx)).env.freeVars :=
                        Env.mem_freeVars_iff.mpr ⟨R_g.onPolyTy pt, hm, hxOnTy⟩
                      have hxEnvE : x ∈ ((R_g.onCtx (S₁.onCtx ctx))).env.freeVars :=
                        hxEnv
                      have hc := congrArg Ctx.env hctxS₁
                      have hxS₀E : x ∈ ((S₀.onCtx ctx)).env.freeVars := by
                        rwa [← hc]
                      exact hXenv x hx
                        hxS₀E
                    · have hfix : R_g.onTy (Ty.fvar v) = Ty.fvar v :=
                        hR_gK v (hKrigid v hrigid)
                      have hxv' : x ∈ (R_g.onTy (Ty.fvar v)).freeVars := by
                        have heq : Rer.onTy (Ty.fvar v) =
                             (R_g.onTy (Ty.fvar v)) := by
                          rfl
                        rw [heq] at hxv
                        exact hxv
                      rw [hfix] at hxv'
                      simp only [Ty.freeVars, List.mem_singleton] at hxv'
                      exact hXrigid x hx (by rw [hxv']; exact hrigid)
                  have halgDecl := genGroup_generalizes_renameG
                    (Ginf := G) (G := Gdecl) (Xsfull := Xs)
                    (τinf :=  (S₁.onTy (Ty.fvar (Φ + j))))
                    (τdecl :=  (τsD[j]'hjT)) (R := Rer)
                    hτalgLC
                    (hlcD (τsD[j]'hjT) hτDmem) hRerlc
                    hwfD.nodup hXlen hXnodup hXG
                    (fun x hx hc => hXτsD x hx (τsD[j]'hjT) hτDmem
                      hc)
                    hconnj hXinf
                  have halgDecl' :
                      ( (R_g.onPolyTy
                        (PolyTy.genGroup G (S₁.onTy (Ty.fvar (Φ + j)))))).Generalizes
                      ( (PolyTy.genGroup Gdecl (τsD[j]'hjT))) := by
                    simpa [hRer_def] using halgDecl
                  exact halgDecl'.trans hdeclGen'
            have hfac : Subst.Factors R_g Sc R_g :=
              hSc.factors_of_generalizes hgenInit hspecs1LC hspecs1Below hrigidBelow (by
                intro τ σ full step hfull havoid hstep hrange hstepLC hσwf hσrigid
                  hτlc hτbelow hgen
                exact RecCeilingConstraints.step_absorbed hGnodup
                  (fun x hx hxG => hGrigid x hxG hx) hR_g
                  (fun x hx => hR_gK x (hKrigid x hx)) hτlc hτbelow hrigidBelow
                  hfull havoid hstep hrange hstepLC hσwf hσrigid hgen)
            have hbodyAlg0 :=
              letRecFused_body_retype (Φ := Φ) (ctx := ctx) (S₁ := S₁)
                (Sc := Sc) (R₁ := R_g) (S₀ := S₀)
                (anns := anns) (bindings := bindings) (body := body) (dspecs := dspecs)
                (specs1 := specs1) (specsC := specsC)
                (G := Gdecl) (Xs := Xs) (τ₀ := τe) (K := K) hspecs1 hspecsC
                (fun p hp => by rw [← hG]; exact hScdom p hp)
                (fun p hp u hu => by rw [← hG]; exact hScrange p hp u hu) hfac
                hanns_eq hdlc hwfD.nodup hXlen hXnodup hXG hXτs hXenv hXrigid
                hS₁lc hR_g hctxS₁ hKrigid hR_gK hσfix hconnB hbodyE
            have hbodyAlg : TypeOfHM
                (R_g.onCtx
                  { (Sc.onCtx (S₁.onCtx ctx)) with
                    env := RecSpecs.ceilingSchemes G anns specsC ++
                      (Sc.onCtx (S₁.onCtx ctx)).env })
                body ( τe) := by
              simpa only [hG] using hbodyAlg0
            -- recurse on the body at the algorithmic body context
            have hσbody_bel : ∀ σ, some σ ∈ anns → Ty.BelowFvars Φ₁ σ.body := fun σ hσ =>
              Ty.BelowFvars.of_freeVars_lt (fun y hy =>
                have hK := hKe y (List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl
                  (Expr.scheme_body_mem_annList_tyFreeVars hσ hy)))))
                hKΦ₁ y hK)
            have hSc_bel : ∀ p ∈ Sc, Ty.BelowFvars Φ₁ p.2 :=
              hSc.belowFvars hrigidBelow
            have hspecsC_lc : ∀ s ∈ specsC, s.LC := by
              intro s hs
              rw [hspecsC] at hs
              obtain ⟨s₁, hs₁, rfl⟩ := List.mem_map.mp hs
              exact RecSpec.LC.onSubst hSc.lc (hspecs1LC s₁ hs₁)
            have hspecsC_post : ∀ s ∈ specsC, s.BelowFvars Φ₁ := by
              intro s hs
              rw [hspecsC] at hs
              obtain ⟨s₁, hs₁, rfl⟩ := List.mem_map.mp hs
              exact RecSpec.BelowFvars.onSubst hSc_bel (hspecs1Below s₁ hs₁)
            have hwfB : CtxWF
                { (Sc.onCtx (S₁.onCtx ctx)) with
                  env := RecSpecs.ceilingSchemes G anns specsC ++
                    (Sc.onCtx (S₁.onCtx ctx)).env } := by
              intro M hM
              rcases List.mem_append.mp hM with hM | hM
              · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hM
                cases p with
                | mk a s =>
                  cases a with
                  | some σ =>
                    exact hannswf σ (List.of_mem_zip hp).1
                  | none =>
                    exact RecSpec.bodyScheme_wf
                      (hspecsC_lc s (List.of_mem_zip hp).2)
              · exact Subst.onCtx_wf hSc.lc (Subst.onCtx_wf hS₁lc hwf) M hM
            have hbelowB : CtxBelow Φ₁
                { (Sc.onCtx (S₁.onCtx ctx)) with
                  env := RecSpecs.ceilingSchemes G anns specsC ++
                    (Sc.onCtx (S₁.onCtx ctx)).env } := by
              intro M hM
              rcases List.mem_append.mp hM with hM | hM
              · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hM
                cases p with
                | mk a s =>
                  cases a with
                  | some σ =>
                    exact hσbody_bel σ (List.of_mem_zip hp).1
                  | none =>
                    exact RecSpec.bodyScheme_belowFvars
                      (hspecsC_post s (List.of_mem_zip hp).2)
              · exact Subst.onCtx_below hSc_bel (le_refl _)
                  (Subst.onCtx_below hS₁_bel (le_trans (by omega) hgle) hbelow) M hM
            obtain ⟨R_b, hR_b, hty_b, hR_bK, hAgreeB⟩ :=
              ih.1 hbody hsize_body hwfB hbelowB hwfB hbelowB R_g ( τe) K
                hR_g hKΦ₁ hKbody hR_gK hbodyAlg
            -- The committed ceiling is absorbed by the group residual, then the
            -- ordinary body tier composes exactly as in the other W cases.
            have hRgSc : Subst.AgreesBelow Φ₁ R_g (Sc ++ R_g) := by
              intro v hv
              simpa only [Subst.onTy_append] using hfac (Ty.fvar v)
            have hAgreePre : Subst.AgreesBelow Φ S₀ ((S₁ ++ Sc) ++ R_g) :=
              Subst.AgreesBelow.trans_append (by omega) hAgreeTier hS₁_bel hRgSc
            have hS₁Sc_bel : ∀ p ∈ S₁ ++ Sc, Ty.BelowFvars Φ₁ p.2 := by
              intro p hp
              exact (List.mem_append.mp hp).elim (hS₁_bel p) (hSc_bel p)
            have hAgree : Subst.AgreesBelow Φ S₀ (((S₁ ++ Sc) ++ S₂) ++ R_b) :=
              Subst.AgreesBelow.trans_append (by omega) hAgreePre hS₁Sc_bel hAgreeB
            refine ⟨R_b, hR_b, ?_, hR_bK, ?_⟩
            · show  τe =  (R_b.onTy τ)
              exact hty_b
            · simpa [List.append_assoc] using hAgree
    · -- InferBranches tier
      intro Φ ctx scrutTy ρ brs Φ' S h hne _hn hwf hbelow
      cases h with
      | nil =>
        intro; exact absurd rfl hne
      | cons hlook hn h₀ hinfbody h₂ hrest =>
        rename_i c nbr body rest ctor Φ₁ S₀ S₁ S₂ S₃ τb
        exact fun hwf hbelow S₀amb scruT₀ ρe K hS₀amb hscruLC hscrutLC hρLC hbscrut hbρ hKΦ hKe hKfix hIMGρ hIMGscru hbrs => by
          -- [match-agent]
          -- brs = (.named c nbr, body) :: rest; constructor data: `c nbr body rest ctor Φ₁ S₀ S₁ S₂ S₃ τb`
          -- with hlook : get? ctx.ctors c = some ctor, h₀ : UnifyRel scrutTy (customTy ctor fresh) S₀,
          --   hinfbody : Infer (Φ + ctor.paramCount) bodyCtx body Φ₁ S₁ τb,
          --   h₂ : UnifyRel τb (S₁.onTy (S₀.onTy ρ)) S₂, hrest : InferBranches Φ₁ … rest Φ₂ S₃
          have hsize_b : body.size < n := by
            have := _hn
            simp only [Expr.sizeBranches] at this
            omega
          have hsize_rest : Expr.sizeBranches rest < n := by
            have := _hn
            simp only [Expr.sizeBranches] at this
            omega
          have hKbody : ∀ y ∈ body.tyFreeVars, y ∈ K := fun y hy => hKe y (by
            simp only [Expr.tyFreeVars.BranchList.tyFreeVars, List.mem_append]; exact Or.inl hy)
          have hKrest : ∀ y ∈ Expr.tyFreeVars.BranchList.tyFreeVars rest, y ∈ K := fun y hy => hKe y (by
            simp only [Expr.tyFreeVars.BranchList.tyFreeVars, List.mem_append]; exact Or.inr hy)
          -- STEP 0: invert the head branch's declarative premise (erased world).
          have hdhead := hbrs (.named c nbr, body) (List.mem_cons_self ..)
          cases hdhead with
          | mk hspec hctxdef hbodyty =>
            rename_i bodyCtx ctorE tyArgsE instContentsE
            -- `hspec : BranchCtorSpec (S₀amb.onCtx ctx).ctors c' n' scruT₀ ctorE tyArgsE instContentsE`
            have hctorE : ctorE =  ctor := by
              have hl : LookupList.get? (S₀amb.onCtx ctx).ctors c = some ( ctor) := by
                simpa [Subst.onCtx] using hlook
              exact Option.some.inj (hspec.lookup.symm.trans hl)
            have htyArgs_lc : ∀ t ∈ tyArgsE, t.IsLC := by
              have hlc : (Ty.customTy ctor.tyName tyArgsE).IsLC := by
                simpa [hctorE, hspec.scrut_eq] using hscruLC
              cases hlc with | customTy h => exact h
            have hpc' : ctor.paramCount = tyArgsE.length := by
              simpa [hctorE] using hspec.arity
            have hscrutImg' : Eq (.customTy ctor.tyName tyArgsE) (S₀amb.onTy scrutTy) := by
              simpa [hctorE, hspec.scrut_eq] using hIMGscru
            have hinstsE : instContentsE = ctorE.contents.map (Ty.openWith tyArgsE) := by
              refine List.ext_getElem ?_ ?_
              · rw [List.length_map]
                exact hspec.fields.length_eq.symm
              · intro i hi _
                have hlen₂ : i < ctorE.contents.length := hspec.fields.length_eq.symm ▸ hi
                have hinst := hspec.fields.get hlen₂ hi
                rw [List.get_eq_getElem, List.get_eq_getElem] at hinst
                rw [List.getElem_map]
                have hpc'' : tyArgsE.length = ctorE.paramCount := hspec.arity.symm
                exact InstantiatesBy.eq_openWith hinst (ctorE.bound _ (List.getElem_mem hlen₂)) hpc''
            -- STEP 1: the customTy factoring dodge (per-branch MGU `S₀` is given).
            obtain ⟨R₀, hR₀, hR₀K, hAgree₀, hmap₀⟩ :=
              customTy_factor_dodge (R := S₀amb) (S₀ := S₀) (ctor := ctor) (tyArgs := tyArgsE)
                h₀ hbscrut hS₀amb hKΦ hKfix hpc' htyArgs_lc hscrutImg'
            have hAgreeBelow₀ : Subst.AgreesBelow Φ S₀amb (S₀ ++ R₀) :=
              fun v hv => by rw [Subst.onTy_append]; exact hAgree₀ v hv
            have hS₀lc : ∀ p ∈ S₀, p.2.IsLC :=
              UnifyRel.lc h₀ hscrutLC (by
                apply ContainsBvarsUpTo.customTy
                intro t ht
                obtain ⟨x, _, rfl⟩ := List.mem_map.mp ht
                exact ContainsBvarsUpTo.fvar)
            have hS₀_bel : ∀ p ∈ S₀, Ty.BelowFvars (Φ + ctor.paramCount) p.2 :=
              UnifyRel.belowFvars h₀ (hbscrut.mono (by omega)) (by
                apply Ty.BelowFvars.customTy
                intro t ht
                obtain ⟨x, hx, rfl⟩ := List.mem_map.mp ht
                exact Ty.BelowFvars.fvar (by have := freshVars_lt x hx; omega))
            have hfle₀ : Φ ≤ Φ + ctor.paramCount := by omega
            -- STEP 2: the algorithmic body context and its WF/below invariants.
            let bodyCtxAlg : Ctx := { (S₀.onCtx ctx) with
                env := (ctor.contents.map (Ty.openWith
                    (((freshVars Φ ctor.paramCount).map (Ty.fvar ·)).map S₀.onTy))).map PolyTy.mkTrivial
                  ++ (S₀.onCtx ctx).env }
            have hwf_body : CtxWF bodyCtxAlg := by
              dsimp [bodyCtxAlg]
              refine branchBindings_wf (ctorr := ctor)
                (ta := ((freshVars Φ ctor.paramCount).map (Ty.fvar ·)).map S₀.onTy)
                (Subst.onCtx_wf hS₀lc hwf) ?_ (by simp)
              intro t ht
              obtain ⟨v, hv, rfl⟩ := List.mem_map.mp ht
              obtain ⟨x, _, rfl⟩ := List.mem_map.mp hv
              exact Subst.onTy_lc hS₀lc ContainsBvarsUpTo.fvar
            have hbelow_body : CtxBelow (Φ + ctor.paramCount) bodyCtxAlg := by
              dsimp [bodyCtxAlg]
              refine branchBindings_below (ctorr := ctor)
                (ta := ((freshVars Φ ctor.paramCount).map (Ty.fvar ·)).map S₀.onTy)
                (Subst.onCtx_below hS₀_bel hfle₀ hbelow) ?_
              intro t ht
              obtain ⟨v, hv, rfl⟩ := List.mem_map.mp ht
              obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hv
              exact Subst.onTy_belowFvars hS₀_bel (.fvar (by have := freshVars_lt x hx; omega))
            -- STEP 3: transport the declarative body typing into the R₀-world.
            have hctx0 : (R₀.onCtx (S₀.onCtx ctx)) = (S₀amb.onCtx ctx) := by
              rw [← Subst.onCtx_append]
              exact (Subst.onCtx_congr hAgreeBelow₀ hbelow).symm
            have hinstsE_direct :
                instContentsE =
                  ctor.contents.map (fun c => Ty.openWith tyArgsE c) := by
              simpa [hctorE] using hinstsE
            have hbodyCtxEq : (R₀.onCtx bodyCtxAlg) = bodyCtx := by
              calc
                (R₀.onCtx bodyCtxAlg)
                    = { (R₀.onCtx (S₀.onCtx ctx)) with
                        env := (( ctor).contents.map
                          (fun c => Ty.openWith tyArgsE c)).map PolyTy.mkTrivial
                            ++ (R₀.onCtx (S₀.onCtx ctx)).env } := by
                  rw [Subst.onCtx_branchBindings hR₀]
                  rw [hmap₀]
                _ = { (S₀amb.onCtx ctx) with
                        env := (( ctor).contents.map
                          (fun c => Ty.openWith tyArgsE c)).map PolyTy.mkTrivial
                            ++ (S₀amb.onCtx ctx).env } := by
                  rw [hctx0]
                _ = bodyCtx := by
                  rw [hctxdef]
                  simp [hinstsE_direct]
            have hbE : TypeOfHM bodyCtx body ( ρe) := by
              exact hbodyty
            have hbE' : TypeOfHM (R₀.onCtx bodyCtxAlg) body ( ρe) := by
              rwa [← hbodyCtxEq] at hbE
            have hKΦ₀ : ∀ k ∈ K, k < Φ + ctor.paramCount := fun k hk => lt_of_lt_of_le (hKΦ k hk) hfle₀
            -- STEP 4: recurse on the branch body (its declarative type is ρe, erased).
            obtain ⟨R_b, hR_b, htyb, hR_bK, hagb⟩ :=
              ih.1 hinfbody hsize_b hwf_body hbelow_body hwf_body hbelow_body R₀ ( ρe) K
                hR₀ hKΦ₀ hKbody hR₀K hbE'
            have hle_b : Φ + ctor.paramCount ≤ Φ₁ := Infer.frontier_le hinfbody
            have hKΦ₁ : ∀ k ∈ K, k < Φ₁ := fun k hk => lt_of_lt_of_le (hKΦ₀ k hk) hle_b
            have hbodyLC := Infer.lc hinfbody hwf_body
            have hτb_lc : τb.IsLC := hbodyLC.1
            have hS₁lc : ∀ p ∈ S₁, p.2.IsLC := hbodyLC.2
            have hbb := Infer.belowFvars hinfbody hbelow_body (fun y hy => hKΦ₀ y (hKbody y hy))
            have hτb_bel : Ty.BelowFvars Φ₁ τb := hbb.1
            have hS₁_bel : ∀ p ∈ S₁, Ty.BelowFvars Φ₁ p.2 := hbb.2
            have htyb' : Eq ρe (R_b.onTy τb) :=
              htyb
            -- STEP 5: the head body unifies against the running result (ρ-link chain).
            have hρbel₁ : Ty.BelowFvars (Φ + ctor.paramCount) (S₀.onTy ρ) :=
              Subst.onTy_belowFvars hS₀_bel (hbρ.mono hfle₀)
            have hρImg₀ : Eq ρe (R₀.onTy (S₀.onTy ρ)) := by
              rw [← Subst.onTy_append]
              exact Eq.trans hIMGρ (Subst.onTy_congr hAgreeBelow₀ hbρ)
            have hρImg_b : Eq ρe (R_b.onTy (S₁.onTy (S₀.onTy ρ))) := by
              rw [← Subst.onTy_append]
              exact Eq.trans hρImg₀ (Subst.onTy_congr hagb hρbel₁)
            have hUni : Unifies R_b τb (S₁.onTy (S₀.onTy ρ)) := by
              show Eq (R_b.onTy τb) (R_b.onTy (S₁.onTy (S₀.onTy ρ)))
              exact Eq.trans (Eq.symm htyb') hρImg_b
            obtain ⟨R_u, hR_u_fac, hR_u, hR_uK⟩ :=
              UnifyRel.greatest_K h₂ R_b hR_b hUni hR_bK
            have hS₂lc : ∀ p ∈ S₂, p.2.IsLC :=
              UnifyRel.lc h₂ hτb_lc (Subst.onTy_lc hS₁lc (Subst.onTy_lc hS₀lc hρLC))
            have hS₂_bel : ∀ p ∈ S₂, Ty.BelowFvars Φ₁ p.2 :=
              UnifyRel.belowFvars h₂ hτb_bel
                (Subst.onTy_belowFvars hS₁_bel
                  ((Subst.onTy_belowFvars hS₀_bel (hbρ.mono hfle₀)).mono hle_b))
            have hAgreeUni : Subst.AgreesBelow Φ₁ R_b (S₂ ++ R_u) :=
              fun v hv => by rw [Subst.onTy_append]; exact hR_u_fac (Ty.fvar v)
            have hρImg_u : Eq ρe (R_u.onTy (S₂.onTy (S₁.onTy (S₀.onTy ρ)))) :=
              Eq.trans hρImg_b (hR_u_fac (S₁.onTy (S₀.onTy ρ)))
            -- STEP 6: rest recursion premises (declarative types stay scruT₀/ρe).
            have hwf' : CtxWF (S₂.onCtx (S₁.onCtx (S₀.onCtx ctx))) :=
              Subst.onCtx_wf hS₂lc (Subst.onCtx_wf hS₁lc (Subst.onCtx_wf hS₀lc hwf))
            have hbelow' : CtxBelow Φ₁ (S₂.onCtx (S₁.onCtx (S₀.onCtx ctx))) :=
              Subst.onCtx_below hS₂_bel (le_refl _)
                (Subst.onCtx_below hS₁_bel hle_b
                  (Subst.onCtx_below hS₀_bel hfle₀ hbelow))
            have hbscrut' : Ty.BelowFvars Φ₁ (S₂.onTy (S₁.onTy (S₀.onTy scrutTy))) :=
              Subst.onTy_belowFvars hS₂_bel
                (Subst.onTy_belowFvars hS₁_bel
                  ((Subst.onTy_belowFvars hS₀_bel (hbscrut.mono hfle₀)).mono hle_b))
            have hbρ' : Ty.BelowFvars Φ₁ (S₂.onTy (S₁.onTy (S₀.onTy ρ))) :=
              Subst.onTy_belowFvars hS₂_bel
                (Subst.onTy_belowFvars hS₁_bel
                  ((Subst.onTy_belowFvars hS₀_bel (hbρ.mono hfle₀)).mono hle_b))
            have hscrutTy'lc : (S₂.onTy (S₁.onTy (S₀.onTy scrutTy))).IsLC :=
              Subst.onTy_lc hS₂lc (Subst.onTy_lc hS₁lc (Subst.onTy_lc hS₀lc hscrutLC))
            have hρ'lc : (S₂.onTy (S₁.onTy (S₀.onTy ρ))).IsLC :=
              Subst.onTy_lc hS₂lc (Subst.onTy_lc hS₁lc (Subst.onTy_lc hS₀lc hρLC))
            have hScrutStep1 : Eq (S₀amb.onTy scrutTy) (R₀.onTy (S₀.onTy scrutTy)) := by
              rw [← Subst.onTy_append]
              exact Subst.onTy_congr hAgreeBelow₀ hbscrut
            have hScrutStep2 : Eq (R₀.onTy (S₀.onTy scrutTy))
                (R_b.onTy (S₁.onTy (S₀.onTy scrutTy))) := by
              simpa [Subst.onTy_append] using
                (Subst.onTy_congr hagb (Subst.onTy_belowFvars hS₀_bel (hbscrut.mono hfle₀)))
            have hScrutStep3 : Eq (R_b.onTy (S₁.onTy (S₀.onTy scrutTy)))
                (R_u.onTy (S₂.onTy (S₁.onTy (S₀.onTy scrutTy)))) := by
              simpa [Subst.onTy_append] using (hR_u_fac (S₁.onTy (S₀.onTy scrutTy)))
            have hscrutImg' : Eq scruT₀ (R_u.onTy (S₂.onTy (S₁.onTy (S₀.onTy scrutTy)))) :=
              Eq.trans hIMGscru (Eq.trans hScrutStep1 (Eq.trans hScrutStep2 hScrutStep3))
            have hctxeq' : (R_u.onCtx (S₂.onCtx (S₁.onCtx (S₀.onCtx ctx))))
                = (S₀amb.onCtx ctx) := by
              have h1 : (R_u.onCtx (S₂.onCtx (S₁.onCtx (S₀.onCtx ctx))))
                  = (R_b.onCtx (S₁.onCtx (S₀.onCtx ctx))) := by
                rw [← Subst.onCtx_append]
                exact (Subst.onCtx_congr hAgreeUni
                  (Subst.onCtx_below hS₁_bel hle_b
                    (Subst.onCtx_below hS₀_bel hfle₀ hbelow))).symm
              have hAgree01 : Subst.AgreesBelow Φ S₀amb ((S₀ ++ S₁) ++ R_b) :=
                @Subst.AgreesBelow.trans_append Φ (Φ + ctor.paramCount) S₀amb S₀ R₀ S₁ R_b
                  hfle₀ hAgreeBelow₀ hS₀_bel hagb
              have h2 : (R_b.onCtx (S₁.onCtx (S₀.onCtx ctx)))
                  = (S₀amb.onCtx ctx) := by
                simpa [Subst.onCtx_append, List.append_assoc] using
                  (Subst.onCtx_congr hAgree01 hbelow).symm
              exact h1.trans h2
            have hbr' : ∀ br ∈ rest, TypeOfMatchBranch (R_u.onCtx (S₂.onCtx (S₁.onCtx (S₀.onCtx ctx))))
                (br.1, br.2) scruT₀ ρe := by
              intro br hbr
              rw [hctxeq']
              exact hbrs br (List.mem_cons_of_mem _ hbr)
            -- STEP 7: assemble (single-branch tail handled by cases on `rest`).
            by_cases hrestNe : rest = []
            · -- rest = []: the rest derivation is `nil`, so S₃ = [] and Φ₂ = Φ₁.
              subst hrestNe
              have hnil := InferBranches.nil_det hrest
              -- total S = S₀ ++ S₁ ++ S₂; final residual R = R_u
              have hAgree1 : Subst.AgreesBelow Φ S₀amb ((S₀ ++ S₁ ++ S₂) ++ R_u) := by
                have hA : Subst.AgreesBelow Φ S₀amb ((S₀ ++ (S₁ ++ S₂)) ++ R_u) :=
                  @Subst.AgreesBelow.trans_append Φ (Φ + ctor.paramCount) S₀amb S₀ R₀ (S₁ ++ S₂) R_u
                    hfle₀ hAgreeBelow₀ hS₀_bel
                    (@Subst.AgreesBelow.trans_append (Φ + ctor.paramCount) Φ₁ R₀ S₁ R_b S₂ R_u
                      hle_b hagb hS₁_bel hAgreeUni)
                simpa [List.append_assoc] using hA
              rw [hnil.2]
              refine ⟨R_u, hR_u, by simpa [List.append_assoc, List.append_nil] using hAgree1, hR_uK, ?_⟩
              · simpa [Subst.onTy_append, List.append_assoc, List.append_nil] using hρImg_u
            · -- rest ≠ []: recurse with the tier IH.
              have hsize_rest' : Expr.sizeBranches rest < n := hsize_rest
              have hrestNe' : rest ≠ [] := hrestNe
              obtain ⟨R_r, hR_r, hAgreeRest, hR_rK, htyRest⟩ :=
                ih.2.1 hrest hrestNe' hsize_rest' hwf' hbelow' hwf' hbelow' R_u scruT₀ ρe K
                  hR_u hscruLC hscrutTy'lc hρ'lc hbscrut' hbρ' hKΦ₁ hKrest hR_uK hρImg_u hscrutImg' hbr'
              have hAgree1 : Subst.AgreesBelow Φ₁ R_u (S₃ ++ R_r) := hAgreeRest
              have hAgree01 : Subst.AgreesBelow Φ S₀amb ((S₀ ++ S₁ ++ S₂) ++ R_u) := by
                have hA : Subst.AgreesBelow Φ S₀amb ((S₀ ++ (S₁ ++ S₂)) ++ R_u) :=
                  @Subst.AgreesBelow.trans_append Φ (Φ + ctor.paramCount) S₀amb S₀ R₀ (S₁ ++ S₂) R_u
                    hfle₀ hAgreeBelow₀ hS₀_bel
                    (@Subst.AgreesBelow.trans_append (Φ + ctor.paramCount) Φ₁ R₀ S₁ R_b S₂ R_u
                      hle_b hagb hS₁_bel hAgreeUni)
                simpa [List.append_assoc] using hA
              have hAgree : Subst.AgreesBelow Φ S₀amb ((S₀ ++ S₁ ++ S₂ ++ S₃) ++ R_r) := by
                have hA : Subst.AgreesBelow Φ S₀amb (((S₀ ++ S₁ ++ S₂) ++ S₃) ++ R_r) :=
                  @Subst.AgreesBelow.trans_append Φ Φ₁ S₀amb (S₀ ++ S₁ ++ S₂) R_u S₃ R_r (by omega)
                    hAgree01
                    (fun p hp => by
                      rcases List.mem_append.mp hp with hp | hp
                      · rcases List.mem_append.mp hp with hp | hp
                        · exact (hS₀_bel p hp).mono hle_b
                        · exact hS₁_bel p hp
                      · exact hS₂_bel p hp)
                    hAgreeRest
                simpa [List.append_assoc] using hA
              refine ⟨R_r, hR_r, hAgree, hR_rK, ?_⟩
              · simpa [Subst.onTy_append] using htyRest
      | consWild hinfbody h₂ hrest =>
        rename_i body rest Φ₁ S₁ S₂ S₃ τb
        exact fun hwf hbelow S₀amb scruT₀ ρe K hS₀amb hscruLC hscrutLC hρLC hbscrut hbρ hKΦ hKe hKfix hIMGρ hIMGscru hbrs => by
          -- [match-agent]
          -- brs = (.wildcard, body) :: rest; constructor data:
          --   hinfbody : Infer Φ ctx body Φ₁ S₁ τb, h₂ : UnifyRel τb (S₁.onTy ρ) S₂,
          --   hrest : InferBranches Φ₁ (S₂.onCtx (S₁.onCtx ctx)) (S₂.onTy (S₁.onTy scrutTy)) (S₂.onTy (S₁.onTy ρ)) rest Φ₂ S₃
          have hsize_b : body.size < n := by
            have := _hn
            simp only [Expr.sizeBranches] at this
            omega
          have hsize_rest : Expr.sizeBranches rest < n := by
            have := _hn
            simp only [Expr.sizeBranches] at this
            omega
          have hKbody : ∀ y ∈ body.tyFreeVars, y ∈ K := fun y hy => hKe y (by
            simp only [Expr.tyFreeVars.BranchList.tyFreeVars, List.mem_append]; exact Or.inl hy)
          have hKrest : ∀ y ∈ Expr.tyFreeVars.BranchList.tyFreeVars rest, y ∈ K := fun y hy => hKe y (by
            simp only [Expr.tyFreeVars.BranchList.tyFreeVars, List.mem_append]; exact Or.inr hy)
          -- STEP 0: the wildcard body types at the same substituted context, at ρe.
          have hdhead := hbrs (.wildcard, body) (List.mem_cons_self ..)
          have hbodyD : TypeOfHM (S₀amb.onCtx ctx) body ρe := by
            cases hdhead with
            | wildcard hbodyty => exact hbodyty
          -- STEP 1: recurse on the body (ambient unchanged).
          obtain ⟨R_b, hR_b, htyb, hR_bK, hagb⟩ :=
            ih.1 hinfbody hsize_b hwf hbelow hwf hbelow S₀amb ρe K hS₀amb hKΦ hKbody hKfix hbodyD
          have hle_b : Φ ≤ Φ₁ := Infer.frontier_le hinfbody
          have hKΦ₁ : ∀ k ∈ K, k < Φ₁ := fun k hk => lt_of_lt_of_le (hKΦ k hk) hle_b
          have hbodyLC := Infer.lc hinfbody hwf
          have hτb_lc : τb.IsLC := hbodyLC.1
          have hS₁lc : ∀ p ∈ S₁, p.2.IsLC := hbodyLC.2
          have hbb := Infer.belowFvars hinfbody hbelow (fun y hy => hKΦ y (hKbody y hy))
          have hτb_bel : Ty.BelowFvars Φ₁ τb := hbb.1
          have hS₁_bel : ∀ p ∈ S₁, Ty.BelowFvars Φ₁ p.2 := hbb.2
          -- STEP 2: the body's output unifies against the running result.
          have hρImg_b : Eq ρe (R_b.onTy (S₁.onTy ρ)) := by
            rw [← Subst.onTy_append]
            exact Eq.trans hIMGρ (Subst.onTy_congr hagb hbρ)
          have hUni : Unifies R_b τb (S₁.onTy ρ) := by
            show Eq (R_b.onTy τb) (R_b.onTy (S₁.onTy ρ))
            exact Eq.trans (Eq.symm htyb) hρImg_b
          obtain ⟨R_u, hR_u_fac, hR_u, hR_uK⟩ :=
            UnifyRel.greatest_K h₂ R_b hR_b hUni hR_bK
          have hS₂lc : ∀ p ∈ S₂, p.2.IsLC :=
            UnifyRel.lc h₂ hτb_lc (Subst.onTy_lc hS₁lc hρLC)
          have hS₂_bel : ∀ p ∈ S₂, Ty.BelowFvars Φ₁ p.2 :=
            UnifyRel.belowFvars h₂ hτb_bel (Subst.onTy_belowFvars hS₁_bel (hbρ.mono hle_b))
          have hAgreeUni : Subst.AgreesBelow Φ₁ R_b (S₂ ++ R_u) :=
            fun v hv => by rw [Subst.onTy_append]; exact hR_u_fac (Ty.fvar v)
          have hρImg_u : Eq ρe (R_u.onTy (S₂.onTy (S₁.onTy ρ))) :=
            Eq.trans hρImg_b (hR_u_fac (S₁.onTy ρ))
          -- STEP 3: rest recursion premises.
          have hwf' : CtxWF (S₂.onCtx (S₁.onCtx ctx)) :=
            Subst.onCtx_wf hS₂lc (Subst.onCtx_wf hS₁lc hwf)
          have hbelow' : CtxBelow Φ₁ (S₂.onCtx (S₁.onCtx ctx)) :=
            Subst.onCtx_below hS₂_bel (le_refl _) (Subst.onCtx_below hS₁_bel hle_b hbelow)
          have hbscrut' : Ty.BelowFvars Φ₁ (S₂.onTy (S₁.onTy scrutTy)) :=
            Subst.onTy_belowFvars hS₂_bel (Subst.onTy_belowFvars hS₁_bel (hbscrut.mono hle_b))
          have hbρ' : Ty.BelowFvars Φ₁ (S₂.onTy (S₁.onTy ρ)) :=
            Subst.onTy_belowFvars hS₂_bel (Subst.onTy_belowFvars hS₁_bel (hbρ.mono hle_b))
          have hscrutTy'lc : (S₂.onTy (S₁.onTy scrutTy)).IsLC :=
            Subst.onTy_lc hS₂lc (Subst.onTy_lc hS₁lc hscrutLC)
          have hρ'lc : (S₂.onTy (S₁.onTy ρ)).IsLC :=
            Subst.onTy_lc hS₂lc (Subst.onTy_lc hS₁lc hρLC)
          have hScrutStep1 : Eq (S₀amb.onTy scrutTy) (R_b.onTy (S₁.onTy scrutTy)) := by
            simpa [Subst.onTy_append] using (Subst.onTy_congr hagb hbscrut)
          have hScrutStep2 : Eq (R_b.onTy (S₁.onTy scrutTy))
              (R_u.onTy (S₂.onTy (S₁.onTy scrutTy))) := by
            simpa [Subst.onTy_append] using (hR_u_fac (S₁.onTy scrutTy))
          have hscrutImg' : Eq scruT₀ (R_u.onTy (S₂.onTy (S₁.onTy scrutTy))) :=
            Eq.trans hIMGscru (Eq.trans hScrutStep1 hScrutStep2)
          have hctxeq' : (R_u.onCtx (S₂.onCtx (S₁.onCtx ctx)))
              = (S₀amb.onCtx ctx) := by
            have h1 : (R_u.onCtx (S₂.onCtx (S₁.onCtx ctx)))
                = (R_b.onCtx (S₁.onCtx ctx)) := by
              rw [← Subst.onCtx_append]
              exact (Subst.onCtx_congr hAgreeUni (Subst.onCtx_below hS₁_bel hle_b hbelow)).symm
            have h2 : (R_b.onCtx (S₁.onCtx ctx)) = (S₀amb.onCtx ctx) := by
              rw [← Subst.onCtx_append]
              exact (Subst.onCtx_congr hagb hbelow).symm
            exact h1.trans h2
          have hbr' : ∀ br ∈ rest, TypeOfMatchBranch (R_u.onCtx (S₂.onCtx (S₁.onCtx ctx)))
              (br.1, br.2) scruT₀ ρe := by
            intro br hbr
            rw [hctxeq']
            exact hbrs br (List.mem_cons_of_mem _ hbr)
          -- STEP 4: assemble (single-branch tail handled by cases on `rest`).
          by_cases hrestNe : rest = []
          · subst hrestNe
            have hnil := InferBranches.nil_det hrest
            have hAgree : Subst.AgreesBelow Φ S₀amb ((S₁ ++ S₂) ++ R_u) :=
              @Subst.AgreesBelow.trans_append Φ Φ₁ S₀amb S₁ R_b S₂ R_u hle_b hagb hS₁_bel hAgreeUni
            rw [hnil.2]
            refine ⟨R_u, hR_u, by simpa [List.append_assoc, List.append_nil] using hAgree, hR_uK, ?_⟩
            · simpa [Subst.onTy_append, List.append_assoc, List.append_nil] using hρImg_u
          · have hsize_rest' : Expr.sizeBranches rest < n := hsize_rest
            have hrestNe' : rest ≠ [] := hrestNe
            obtain ⟨R_r, hR_r, hAgreeRest, hR_rK, htyRest⟩ :=
              ih.2.1 hrest hrestNe' hsize_rest' hwf' hbelow' hwf' hbelow' R_u scruT₀ ρe K
                hR_u hscruLC hscrutTy'lc hρ'lc hbscrut' hbρ' hKΦ₁ hKrest hR_uK hρImg_u hscrutImg' hbr'
            have hAgree : Subst.AgreesBelow Φ S₀amb ((S₁ ++ S₂ ++ S₃) ++ R_r) := by
              have hA : Subst.AgreesBelow Φ S₀amb (((S₁ ++ S₂) ++ S₃) ++ R_r) :=
                @Subst.AgreesBelow.trans_append Φ Φ₁ S₀amb (S₁ ++ S₂) R_u S₃ R_r hle_b
                  (@Subst.AgreesBelow.trans_append Φ Φ₁ S₀amb S₁ R_b S₂ R_u hle_b hagb hS₁_bel hAgreeUni)
                  (fun p hp => by
                    rcases List.mem_append.mp hp with hp | hp
                    · exact hS₁_bel p hp
                    · exact hS₂_bel p hp)
                  hAgreeRest
              simpa [List.append_assoc] using hA
            refine ⟨R_r, hR_r, hAgree, hR_rK, ?_⟩
            · simpa [Subst.onTy_append] using htyRest
    · -- InferRecGroup tier
      intro Φ₀ Φ ctx bindings specs Φ' S h hle _hn hwf hbelow
      cases h with
      | nil =>
        intro _ _ S₀ L K R₀ hS₀ hKΦ hKe hKfix hSpecLC hSpecBelow hKsch hR₀ hR₀K hAgree hMonoMem hPolyMem
        refine ⟨R₀, hR₀, hR₀K, ?_, ?_⟩
        · rw [List.nil_append]
          exact fun v hv => Eq.symm (hAgree v hv)
        · rw [List.nil_append]
          exact fun v hv => Eq.refl _
      | cons h₀ h₂ hrest =>
        rename_i e rest τ specs Φ₁ S₁ S₂ S₃ τ'
        exact fun hwf hbelow S₀ L K R₀ hS₀ hKΦ hKe hKfix hSpecLC hSpecBelow hKsch hR₀ hR₀K hAgree hMonoMem hPolyMem => by
          -- SPINE-GROUP-MONO
          have hsize_e : e.size < n := by
            have := _hn
            simp only [Expr.sizeRecGroup] at this
            omega
          have hsize_rest : Expr.sizeRecGroup rest < n := by
            have := _hn
            simp only [Expr.sizeRecGroup] at this
            omega
          have hKbody : ∀ y ∈ e.tyFreeVars, y ∈ K := fun y hy => hKe y (by
            simp only [Expr.tyFreeVars.RecGroup.tyFreeVars, List.mem_append]; exact Or.inl hy)
          have hKrest : ∀ y ∈ Expr.tyFreeVars.RecGroup.tyFreeVars rest, y ∈ K := fun y hy => hKe y (by
            simp only [Expr.tyFreeVars.RecGroup.tyFreeVars, List.mem_append]; exact Or.inr hy)
          have hKΦhead : ∀ k ∈ K, k < Φ := fun k hk => lt_of_lt_of_le (hKΦ k hk) hle
          have hSpecLC' : ∀ s ∈ specs, s.LC := fun s hs => hSpecLC s (List.mem_cons_of_mem _ hs)
          have hSpecBelow' : ∀ s ∈ specs, ∀ τm, s = .mono τm → Ty.BelowFvars Φ τm :=
            fun s hs τm hτm => hSpecBelow s (List.mem_cons_of_mem _ hs) τm hτm
          have hKsch' : ∀ s ∈ specs, ∀ σ, s = .poly σ → ∀ y ∈ σ.body.freeVars, y ∈ K :=
            fun s hs σ hσ => hKsch s (List.mem_cons_of_mem _ hs) σ hσ
          -- the head member's declarative typing (the mono premise at the head)
          have hhead : TypeOfHM (R₀.onCtx ctx) ( e)
              ( (R₀.onTy τ)) :=
            hMonoMem (e, .mono τ) (by rw [List.zip_cons_cons]; exact List.mem_cons_self) τ rfl
          -- STEP 1: head IH (ambient R₀).
          obtain ⟨R₁, hR₁, hty₁, hR₁K, hAgree₁⟩ :=
            ih.1 h₀ hsize_e hwf hbelow hwf hbelow R₀ ( (R₀.onTy τ)) K
              hR₀ hKΦhead hKbody hR₀K hhead
          have hfle : Φ ≤ Φ₁ := Infer.frontier_le h₀
          have hKΦ₁ : ∀ k ∈ K, k < Φ₁ := fun k hk => lt_of_lt_of_le (hKΦhead k hk) hfle
          obtain ⟨hτ'_lc, hS₁lc⟩ := Infer.lc h₀ hwf
          have h₀below := Infer.belowFvars h₀ hbelow (fun y hy =>
            lt_of_lt_of_le (hKΦ y (hKbody y hy)) hle)
          have hτ'_bel : Ty.BelowFvars Φ₁ τ' := h₀below.1
          have hS₁_bel : ∀ p ∈ S₁, Ty.BelowFvars Φ₁ p.2 := h₀below.2
          have hβ_lc : τ.IsLC := hSpecLC (.mono τ) List.mem_cons_self
          have hbβ : Ty.BelowFvars Φ τ := hSpecBelow (.mono τ) List.mem_cons_self τ rfl
          have hS₂lc : ∀ p ∈ S₂, p.2.IsLC :=
            UnifyRel.lc h₂ hτ'_lc (Subst.onTy_lc hS₁lc hβ_lc)
          have hS₂_bel : ∀ p ∈ S₂, Ty.BelowFvars Φ₁ p.2 :=
            UnifyRel.belowFvars h₂ hτ'_bel (Subst.onTy_belowFvars hS₁_bel (hbβ.mono hfle))
          have hS₁₂_bel : ∀ p ∈ S₁ ++ S₂, Ty.BelowFvars Φ₁ p.2 := by
            intro p hp
            rcases List.mem_append.mp hp with hp | hp
            · exact hS₁_bel p hp
            · exact hS₂_bel p hp
          -- STEP 2: the head's output unifies against the head spec monotype.
          have hρImg : Eq ( (R₀.onTy τ)) (R₁.onTy (S₁.onTy τ)) := by
            have h1 : Eq (R₀.onTy τ) (R₁.onTy (S₁.onTy τ)) := by
              rw [← Subst.onTy_append]
              exact Subst.onTy_congr hAgree₁ hbβ
            show  ( (R₀.onTy τ)) =  (R₁.onTy (S₁.onTy τ))
            exact h1
          have hUni : Unifies R₁ τ' (S₁.onTy τ) := by
            show Eq (R₁.onTy τ') (R₁.onTy (S₁.onTy τ))
            exact Eq.trans (Eq.symm hty₁) hρImg
          obtain ⟨R_u, hR_u_fac, hR_u, hR_uK⟩ :=
            UnifyRel.greatest_K h₂ R₁ hR₁ hUni hR₁K
          have hAgreeUni : Subst.AgreesBelow Φ₁ R₁ (S₂ ++ R_u) :=
            fun v hv => by rw [Subst.onTy_append]; exact hR_u_fac (Ty.fvar v)
          have hAgreeChain : Subst.AgreesBelow Φ R₀ ((S₁ ++ S₂) ++ R_u) :=
            @Subst.AgreesBelow.trans_append Φ Φ₁ R₀ S₁ R₁ S₂ R_u hfle hAgree₁ hS₁_bel hAgreeUni
          -- STEP 3: tail context identity + type identity (spec-τ below Φ).
          have hctxid : (R_u.onCtx (S₂.onCtx (S₁.onCtx ctx)))
              = (R₀.onCtx ctx) := by
            have h1 : (R₀.onCtx ctx) = (((S₁ ++ S₂) ++ R_u).onCtx ctx) :=
              Subst.onCtx_congr hAgreeChain hbelow
            simpa [Subst.onCtx_append, List.append_assoc] using h1.symm
          have hkey_t : ∀ {t : Ty}, Ty.BelowFvars Φ t →
              Eq (R_u.onTy ((S₁ ++ S₂).onTy t)) (R₀.onTy t) := by
            intro t ht
            have h1 : Eq (R₀.onTy t) (((S₁ ++ S₂) ++ R_u).onTy t) :=
              Subst.onTy_congr hAgreeChain ht
            rw [Subst.onTy_append] at h1
            exact Eq.symm h1
          -- STEP 4: tail recursion premises (context + type rewrites).
          have hwf' : CtxWF (S₂.onCtx (S₁.onCtx ctx)) :=
            Subst.onCtx_wf hS₂lc (Subst.onCtx_wf hS₁lc hwf)
          have hbelow' : CtxBelow Φ₁ (S₂.onCtx (S₁.onCtx ctx)) :=
            Subst.onCtx_below hS₂_bel (le_refl _) (Subst.onCtx_below hS₁_bel hfle hbelow)
          have hMonoMem' : ∀ p ∈ rest.zip (specs.map (RecSpec.onSubst (S₁ ++ S₂))),
              ∀ τm, p.2 = .mono τm →
                TypeOfHM (R_u.onCtx (S₂.onCtx (S₁.onCtx ctx)))
                  ( p.1) ( (R_u.onTy τm)) := by
            intro p hp τm hτm
            rcases List.mem_zip_map_right hp with ⟨e', s₀, hq, hpq⟩
            subst hpq
            cases s₀ with
            | poly σ₀ => exact absurd hτm (by simp [RecSpec.onSubst])
            | mono τ₁ =>
              have hτeq : τm = (S₁ ++ S₂).onTy τ₁ := by
                have hred : RecSpec.onSubst (S₁ ++ S₂) (RecSpec.mono τ₁)
                    = RecSpec.mono ((S₁ ++ S₂).onTy τ₁) := rfl
                rw [hred] at hτm
                exact (RecSpec.mono.inj hτm).symm
              subst hτeq
              rw [hctxid]
              have hbτ₁ : Ty.BelowFvars Φ τ₁ :=
                hSpecBelow' (RecSpec.mono τ₁) (List.of_mem_zip hq).2 τ₁ rfl
              have htype_id :  (R_u.onTy ((S₁ ++ S₂).onTy τ₁))
                  =  (R₀.onTy τ₁) := hkey_t hbτ₁
              rw [htype_id]
              exact hMonoMem (e', .mono τ₁)
                (by rw [List.zip_cons_cons]; exact List.mem_cons_of_mem _ hq) τ₁ rfl
          have hPolyMem' : ∀ p ∈ rest.zip (specs.map (RecSpec.onSubst (S₁ ++ S₂))),
              ∀ σ₀, p.2 = .poly σ₀ → ∀ Ys, FreshNames L σ₀.paramCount Ys →
                TypeOfHM (R_u.onCtx (S₂.onCtx (S₁.onCtx ctx)))
                  ( (Expr.openTyVars Ys p.1)) (σ₀.openVars Ys) := by
            intro p hp σ₀ hσ₀ Ys hYs
            rcases List.mem_zip_map_right hp with ⟨e', s₀, hq, hpq⟩
            subst hpq
            cases s₀ with
            | mono τ₁ => exact absurd hσ₀ (by simp [RecSpec.onSubst])
            | poly σ₁ =>
              have hσeq : σ₀ = σ₁ := by
                have hred : RecSpec.onSubst (S₁ ++ S₂) (RecSpec.poly σ₁) = RecSpec.poly σ₁ := rfl
                rw [hred] at hσ₀
                exact (RecSpec.poly.inj hσ₀).symm
              subst hσeq
              rw [hctxid]
              exact hPolyMem (e', .poly σ₀)
                (by rw [List.zip_cons_cons]; exact List.mem_cons_of_mem _ hq) σ₀ rfl Ys hYs
          -- STEP 5: recurse on the tail (ambient R_u; the tail's own pre-block
          -- frontier is its frontier Φ₁, so its agreement is over Φ₁).
          have hAgreeRefl : ∀ v, v < Φ₁ → Eq (R_u.onTy (.fvar v)) (R_u.onTy (.fvar v)) :=
            fun v hv => Eq.refl _
          have hSpecLC'' : ∀ s' ∈ specs.map (RecSpec.onSubst (S₁ ++ S₂)), s'.LC := by
            intro s' hs'
            obtain ⟨s₀, hs₀, rfl⟩ := List.mem_map.mp hs'
            exact RecSpec.LC.onSubst
              (fun p hp => (List.mem_append.mp hp).elim (fun h1 => hS₁lc p h1) (fun h2 => hS₂lc p h2))
              (hSpecLC' s₀ hs₀)
          have hSpecBelow'' : ∀ s' ∈ specs.map (RecSpec.onSubst (S₁ ++ S₂)),
              ∀ τm, s' = .mono τm → Ty.BelowFvars Φ₁ τm := by
            intro s' hs' τm hτm
            obtain ⟨s₀, hs₀, rfl⟩ := List.mem_map.mp hs'
            cases s₀ with
            | poly σ₀ => exact absurd hτm (by simp [RecSpec.onSubst])
            | mono τ₁ =>
              have hτeq : τm = (S₁ ++ S₂).onTy τ₁ := by
                have hred : RecSpec.onSubst (S₁ ++ S₂) (RecSpec.mono τ₁)
                    = RecSpec.mono ((S₁ ++ S₂).onTy τ₁) := rfl
                rw [hred] at hτm
                exact (RecSpec.mono.inj hτm).symm
              subst hτeq
              exact Subst.onTy_belowFvars hS₁₂_bel
                ((hSpecBelow' (RecSpec.mono τ₁) hs₀ τ₁ rfl).mono hfle)
          have hKsch'' : ∀ s' ∈ specs.map (RecSpec.onSubst (S₁ ++ S₂)),
              ∀ σ, s' = .poly σ → ∀ y ∈ σ.body.freeVars, y ∈ K := by
            intro s' hs' σ hσ
            obtain ⟨s₀, hs₀, rfl⟩ := List.mem_map.mp hs'
            cases s₀ with
            | mono τ₁ => exact absurd hσ (by simp [RecSpec.onSubst])
            | poly σ₀ =>
              have hσeq : σ = σ₀ := by
                have hred : RecSpec.onSubst (S₁ ++ S₂) (RecSpec.poly σ₀) = RecSpec.poly σ₀ := rfl
                rw [hred] at hσ
                exact (RecSpec.poly.inj hσ).symm
              subst hσeq
              exact hKsch' (RecSpec.poly σ) hs₀ σ rfl
          obtain ⟨R_r, hR_r, hR_rK, hAgreeTail, hAgreeTailR⟩ :=
            ih.2.2 hrest (le_refl _) hsize_rest hwf' hbelow' hwf' hbelow' R_u L K R_u
              hR_u hKΦ₁ hKrest hR_uK hSpecLC'' hSpecBelow'' hKsch'' hR_u hR_uK hAgreeRefl hMonoMem' hPolyMem'
          -- STEP 6: assemble (trans_append twice).
          have hAgree0 : Subst.AgreesBelow Φ₀ S₀ (S₁ ++ R₁) := fun v hv =>
            Eq.trans (Eq.symm (hAgree v hv)) (hAgree₁ v (by omega))
          have hAgree12 : Subst.AgreesBelow Φ₀ S₀ ((S₁ ++ S₂) ++ R_u) :=
            @Subst.AgreesBelow.trans_append Φ₀ Φ₁ S₀ S₁ R₁ S₂ R_u (le_trans hle hfle)
              hAgree0 hS₁_bel hAgreeUni
          have hAgree : Subst.AgreesBelow Φ₀ S₀ (((S₁ ++ S₂) ++ S₃) ++ R_r) :=
            @Subst.AgreesBelow.trans_append Φ₀ Φ₁ S₀ (S₁ ++ S₂) R_u S₃ R_r (le_trans hle hfle)
              hAgree12 hS₁₂_bel hAgreeTail
          have hAgreeR : Subst.AgreesBelow Φ R₀ ((S₁ ++ S₂ ++ S₃) ++ R_r) :=
            @Subst.AgreesBelow.trans_append Φ Φ₁ R₀ (S₁ ++ S₂) R_u S₃ R_r hfle
              hAgreeChain hS₁₂_bel hAgreeTail
          refine ⟨R_r, hR_r, hR_rK, ?_, ?_⟩
          · simpa [List.append_assoc] using hAgree
          · simpa [List.append_assoc] using hAgreeR
-- END-SECTION-SPINE

/-! ## 5. Public principality capstones

The mutual size-induction above is intentionally an internal engine. The
theorems in this section expose its expression-level and whole-program
consequences. Factorisation is stated with ordinary structural equality.

The declarative source term is `e`, with source annotations still present. The
executable program is `e.erase` (annotations removed).
`Infer.sourceSound` and `Infer.sound` supply
the two corresponding soundness projections. -/

/-- Principality of a given inference derivation, projected from the mutual D2
    spine. Every declarative type factors through the inferred monotype. -/
theorem Infer.principal {Φ : Nat} {ctx : Ctx} {e : Expr} {Φ' : Nat}
    {S : Subst} {τ : Ty} (h : Infer Φ ctx e Φ' S τ) : Infer.Principal h := by
  intro hwf hbelow
  exact (Infer.principals_mut (e.size + 1)).1 h (Nat.lt_succ_self _) hwf hbelow
    hwf hbelow

/-- Expanded compatibility wrapper around `Infer.principal`. -/
theorem Infer.complete' {Φ : Nat} {ctx : Ctx} {e : Expr} {Φ' : Nat}
    {S : Subst} {τ : Ty} (h : Infer Φ ctx e Φ' S τ)
    (hwf : CtxWF ctx) (hbelow : CtxBelow Φ ctx) {S₀ : Subst} {τ₀ : Ty}
    (hS₀ : ∀ p ∈ S₀, p.2.IsLC) (K : List Nat)
    (hKΦ : ∀ k ∈ K, k < Φ) (hKe : ∀ y ∈ e.tyFreeVars, y ∈ K)
    (hKfix : ∀ k ∈ K, S₀.onTy (.fvar k) = .fvar k)
    (hty : TypeOfHM (S₀.onCtx ctx) e τ₀) :
    ∃ R : Subst, (∀ p ∈ R, p.2.IsLC) ∧
      Eq τ₀ (R.onTy τ) ∧
      (∀ k ∈ K, R.onTy (.fvar k) = .fvar k) ∧
      Subst.AgreesBelow Φ S₀ (S ++ R) := by
  exact Infer.principal h hwf hbelow S₀ τ₀ K hS₀ hKΦ hKe hKfix hty

/-- A computed monotype types the annotated source itself. This
    is stronger in a different direction than operational `principalType_sound`:
    annotations are retained here, while the latter types the runnable erased
    term. -/
theorem principalType_source_sound {ctors : CtorEnv} {e : Expr} {τ : Ty}
    (h : principalType ctors e = some τ) :
    TypeOfHM ⟨[], ctors⟩ e ( τ) := by
  rw [principalType] at h
  rcases hc : inferCore e.tyFreeVars e.freshFloor ⟨[], ctors⟩ e with
    _ | ⟨⟨Φ', S, τ'⟩, hInfer, hSK⟩ <;> rw [hc] at h
  · simp at h
  · simp only [Option.map_some, Option.some.injEq] at h
    subst h
    simpa [Subst.onCtx, Subst.onEnv] using
      Infer.sourceSound hInfer CtxWF.empty CtxBelow.empty
        e.tyFreeVars (fun k hk => Expr.lt_freshFloor hk) (fun y hy => hy) hSK

/-- Monotype principality for the concrete result returned by
    `principalType`.  This is deliberately a source-typing statement
    (`e`); operational soundness for `e.erase` is
    `principalType_sound`. -/
theorem principalType_principal {ctors : CtorEnv} {e : Expr} {τ : Ty}
    (h : principalType ctors e = some τ) :
    ∀ τ₀, TypeOfHM ⟨[], ctors⟩ e τ₀ →
      ∃ R : Subst, (∀ p ∈ R, p.2.IsLC) ∧ Eq τ₀ (R.onTy τ) := by
  rw [principalType] at h
  rcases hc : inferCore e.tyFreeVars e.freshFloor ⟨[], ctors⟩ e with
    _ | ⟨⟨Φ', S, τ'⟩, hInfer, hSK⟩ <;> rw [hc] at h
  · simp at h
  · simp only [Option.map_some, Option.some.injEq] at h
    subst h
    intro τ₀ hτ₀
    obtain ⟨R, _hRlc, hfac, _hRfix, _hag⟩ :=
      Infer.complete' hInfer CtxWF.empty CtxBelow.empty
        (S₀ := []) (τ₀ := τ₀) (by simp) e.tyFreeVars
        (fun k hk => Expr.lt_freshFloor hk) (fun y hy => hy) (by simp) (by
          simpa [Subst.onCtx, Subst.onEnv] using hτ₀)
    exact ⟨R, _hRlc, hfac⟩

/-- A successful whole-program `typecheck` packages a source-sound and
    operationally sound principal monotype. Its closed output scheme is
    `genScheme [] [] τ`; every declarative source type is an instance of `τ`. -/
theorem typecheck_principal {ctors : CtorEnv} {e : Expr} {σ : PolyTy}
    (h : typecheck ctors e = some σ) :
    ∃ τ, σ = genScheme [] [] τ ∧
      TypeOfHM ⟨[], ctors⟩ e ( τ) ∧
      TypeOfHM ⟨[], ctors⟩ e.erase ( τ) ∧
      ∀ τ₀, TypeOfHM ⟨[], ctors⟩ e τ₀ →
        ∃ R : Subst, (∀ p ∈ R, p.2.IsLC) ∧ Eq τ₀ (R.onTy τ) := by
  rw [typecheck] at h
  rcases hc : principalType ctors e with _ | τ <;> rw [hc] at h
  · simp at h
  · simp only [Option.map_some, Option.some.injEq] at h
    exact ⟨τ, h.symm, principalType_source_sound hc, principalType_sound hc,
      principalType_principal hc⟩

/-! ## 6. Producer completeness

The principality spine above starts from an existing `Infer` derivation.  The
remaining completeness direction constructs such a derivation from a
declarative typing over the plain Core expression language.

As in the principality spine, the induction carries an ambient specialization
and an LC residual.  This richer invariant is needed to thread Algorithm W's
fresh variables and substitutions through compound expressions; the public
corollaries will hide it. -/

/-- Producer completeness at one source expression. Any
    declarative typing under an LC specialization is realized by an `Infer`
    derivation whose result factors the declarative type up to `Eq`. -/
def Infer.CompleteAt (e : Expr) : Prop :=
  ∀ {Φ : Nat} {ctx : Ctx} {S₀ : Subst} {τ₀ : Ty} (K : List Nat),
    CtxWF ctx → CtxBelow Φ ctx → (∀ p ∈ S₀, p.2.IsLC) →
    (∀ k ∈ K, k < Φ) → (∀ y ∈ e.tyFreeVars, y ∈ K) →
    (∀ k ∈ K, S₀.onTy (.fvar k) = .fvar k) →
    TypeOfHM (S₀.onCtx ctx) e τ₀ →
    ∃ Φ' S τ R,
      Infer Φ ctx e Φ' S τ ∧
      Subst.AgreesBelow Φ S₀ (S ++ R) ∧
      Eq τ₀ (R.onTy τ) ∧
      (∀ p ∈ R, p.2.IsLC) ∧
      (∀ k ∈ K, R.onTy (.fvar k) = .fvar k) ∧
      (∀ p ∈ S, p.1 ∉ K)

/-- Closing a finite pool preserves every free variable which is not itself
    closed.  The producer-side recursive-ceiling bridge uses this for the
    *retained* (non-pool) variables of a member monotype. -/
private theorem Ty.mem_freeVars_closeOver_of_not_mem
    {gs : List Nat} {τ : Ty} {z : Nat}
    (hz : z ∈ τ.freeVars) (hzgs : z ∉ gs) :
    z ∈ (Ty.closeOver gs τ).freeVars := by
  induction τ using Ty.rec_strong with
  | fvar n =>
      simp only [Ty.closeOver]
      cases hidx : gs.idxOf? n with
      | some i =>
          simp only [Ty.freeVars, List.mem_singleton] at hz
          have hngs : n ∈ gs := by
            by_contra hn
            have hnone : gs.idxOf? n = none := List.idxOf?_eq_none_iff.mpr hn
            rw [hidx] at hnone
            simp at hnone
          exact False.elim (hzgs (hz ▸ hngs))
      | none =>
          simp only [Ty.freeVars, List.mem_singleton] at hz
          subst hz
          simpa [Ty.closeOver, hidx, Ty.freeVars]
  | prim p => simp [Ty.closeOver, Ty.freeVars] at hz
  | bvar i => simp [Ty.closeOver, Ty.freeVars] at hz
  | arrow a b iha ihb =>
      simp only [Ty.closeOver, Ty.freeVars, List.mem_dedup, List.mem_append] at hz ⊢
      rcases hz with hz | hz
      · exact Or.inl (iha hz)
      · exact Or.inr (ihb hz)
  | customTy nm tys ih =>
      have hmap : ∀ ts : List Ty, TyList.closeOver gs ts = ts.map (Ty.closeOver gs) := by
        intro ts
        induction ts with
        | nil => rfl
        | cons hd tl ihtl => simp [TyList.closeOver, ihtl]
      simp only [Ty.closeOver, Ty.freeVars, hmap] at hz ⊢
      rw [mem_TyList_freeVars] at hz ⊢
      obtain ⟨t, ht, hzt⟩ := hz
      exact ⟨Ty.closeOver gs t, List.mem_map.mpr ⟨t, ht, rfl⟩, ih t ht hzt⟩

/-- A generalising group scheme cannot hide a fresh variable in the residual
    image of a member variable which the group did not quantify.  More
    generally, every such image variable is already free in the target
    scheme.  This is the exact fact that rules fresh annotation skolems out of
    the committed (non-pool) part of a recursive-ceiling unifier. -/
private theorem PolyTy.Generalizes.genGroup_nonpool_range
    {G : List Nat} {τ : Ty} {R : Subst} {σ : PolyTy} {z y : Nat}
    (hgen : (R.onPolyTy (PolyTy.genGroup G τ)).Generalizes σ)
    (hzτ : z ∈ τ.freeVars) (hzG : z ∉ G)
    (hy : y ∈ (R.onTy (.fvar z)).freeVars) :
    y ∈ σ.body.freeVars := by
  apply hgen.freeVars_subset
  change y ∈ (R.onTy (Ty.closeOver (Ty.genFilter G τ) τ)).freeVars
  rw [Subst.onTy, Ty.mem_freeVars_substFvars_image]
  refine ⟨z, ?_, hy⟩
  apply Ty.mem_freeVars_closeOver_of_not_mem hzτ
  intro hzfilter
  exact hzG (Ty.mem_of_mem_genFilter hzfilter)

/-- A variable fixed by a substitution survives in every type in which it is
    free.  This is the tiny support fact used to reflect a fresh-skolem
    occurrence through an MGU factorisation. -/
private theorem Subst.mem_freeVars_onTy_of_fixes
    {S : Subst} {t : Ty} {y : Nat}
    (hfix : S.onTy (.fvar y) = .fvar y) (hy : y ∈ t.freeVars) :
    y ∈ (S.onTy t).freeVars := by
  rw [Ty.mem_freeVars_onTy_iff]
  refine ⟨y, hy, ?_⟩
  simpa [hfix, Ty.freeVars]

/-- When recursive-ceiling checks protect only the non-generalised portion of
    an ambient rigid set, their committed projection nevertheless avoids the
    whole set: a domain in `G` is discarded, and every other domain was already
    protected.  This is the `Kc = K \\ G` bridge needed by relational producer
    completeness, where `CompleteAt` permits callers to supply arbitrary
    supersets of lexical rigid names. -/
private theorem Subst.dropDomains_dom_avoids_filter
    {K G : List Nat} {S : Subst}
    (havoid : ∀ p ∈ S, p.1 ∉ K.filter (fun x => !G.contains x)) :
    ∀ p ∈ S.dropDomains G, p.1 ∉ K := by
  intro p hp hpK
  have hpS : p ∈ S := (Subst.mem_dropDomains.mp hp).1
  have hpG : p.1 ∉ G := (Subst.mem_dropDomains.mp hp).2
  apply havoid p hpS
  simp only [List.mem_filter]
  exact ⟨hpK, by simpa [List.contains_eq_mem] using hpG⟩

/-- The sequential form of `dropDomains_dom_avoids_filter`: protecting
    `K \\ G` in every full ceiling and dropping all `G` domains leaves the
    complete committed certificate disjoint from the caller's whole `K`. -/
private theorem RecCeilingConstraints.dom_avoids_filter
    {K rigid G : List Nat} {Φ : Nat} {anns : List (Option PolyTy)}
    {specs : List RecSpec} {Sc : Subst}
    (hSc : RecCeilingConstraints (K.filter (fun x => !G.contains x)) rigid G Φ anns specs Sc) :
    ∀ p ∈ Sc, p.1 ∉ K := by
  intro p hp hpK
  have havoid := hSc.dom_avoids p hp
  apply havoid.1
  simp only [List.mem_filter]
  exact ⟨hpK, by simpa [List.contains_eq_mem] using havoid.2.2⟩

/-- Range side of the recursive-ceiling certificate, stated for an arbitrary
    protected `UnifyRel` result.  Keeping `full` as an input is deliberate:
    the relational bridge uses `complete_K`, while executable completeness can
    apply the same lemma to the particular `unifyCoreK` result before proving
    that its `rangesWithin` test succeeds. -/
private theorem RecCeilingConstraints.dropDomains_range_of_witness
    {K rigid G : List Nat} {Φ : Nat} {τ : Ty} {σ : PolyTy}
    {R U full : Subst}
    (hσrigid : ∀ x ∈ σ.body.freeVars, x ∈ rigid)
    (hrigidG : ∀ x ∈ rigid, x ∉ G)
    (hrigidbelow : ∀ x ∈ rigid, x < Φ)
    (hGbelow : ∀ x ∈ G, x < Φ)
    (hfull : UnifyRel ( τ)
      ( (σ.openVars (freshVars Φ σ.paramCount))) full)
    (havoid : ∀ p ∈ full, p.1 ∉ K ++ rigid ++ freshVars Φ σ.paramCount)
    (hUuni : Unifies U ( τ)
      ( (σ.openVars (freshVars Φ σ.paramCount))))
    (hUfix : ∀ x ∈ K ++ rigid ++ freshVars Φ σ.paramCount,
      U.onTy (.fvar x) = .fvar x)
    (hUagree : ∀ z ∈ ( τ).freeVars, z ∉ G →
      U.onTy (.fvar z) = R.onTy (.fvar z))
    (hRrange : ∀ z ∈ ( τ).freeVars, z ∉ G →
      ∀ x ∈ (R.onTy (.fvar z)).freeVars, x ∈ rigid) :
    ∀ p ∈ Subst.dropDomains G full, ∀ x ∈ p.2.freeVars,
      x ∈ rigid ∧ x ∉ G := by
  let Ys : List Nat := freshVars Φ σ.paramCount
  have htarget_fv : ∀ x ∈ ( (σ.openVars Ys)).freeVars,
      x ∈ rigid ++ Ys := by
    intro x hx
    have hx' : x ∈ (σ.openVars Ys).freeVars :=
      hx
    rcases Ty.freeVars_openVars_subset x hx' with hxbody | hxY
    · exact List.mem_append_left _ (hσrigid x hxbody)
    · exact List.mem_append_right _ (by simpa [Ys] using hxY)
  have htarget_protected : ∀ x ∈ ( (σ.openVars Ys)).freeVars,
      x ∈ K ++ rigid ++ Ys := by
    intro x hx
    simpa [List.append_assoc] using List.mem_append_right K (htarget_fv x hx)
  have hfull_avoid_target : ∀ p ∈ full, p.1 ∉ rigid ++ Ys := by
    intro p hp hbad
    exact havoid p hp (by
      simpa [List.append_assoc] using List.mem_append_right K hbad)
  have hfull_range : ∀ p ∈ full, ∀ x ∈ p.2.freeVars, x ∈ rigid ++ Ys :=
    UnifyRel.range_within_rhs hfull hfull_avoid_target htarget_fv
  intro p hp x hx
  have hpfull : p ∈ full := (Subst.mem_dropDomains.mp hp).1
  have hpnotG : p.1 ∉ G := (Subst.mem_dropDomains.mp hp).2
  have hpτ : p.1 ∈ ( τ).freeVars := by
    rcases UnifyRel.dom_mem hfull p hpfull with hpτ | hptarget
    · exact hpτ
    · exact False.elim (havoid p hpfull (htarget_protected p.1 hptarget))
  have hxRY : x ∈ rigid ++ Ys := hfull_range p hpfull x hx
  constructor
  · rcases List.mem_append.mp hxRY with hxrigid | hxY
    · exact hxrigid
    · exfalso
      have hxfixed : U.onTy (.fvar x) = .fvar x :=
        hUfix x (by
          simpa [List.append_assoc] using List.mem_append_right K
            (List.mem_append_right rigid (by simpa [Ys] using hxY)))
      have hxUrange : x ∈ (U.onTy p.2).freeVars :=
        Subst.mem_freeVars_onTy_of_fixes hxfixed hx
      have hbind := UnifyRel.binding_satisfies hfull U hUuni p hpfull
      have hxUdomE : x ∈ ( (U.onTy (.fvar p.1))).freeVars := by
        rw [hbind]
        exact hxUrange
      have hxUdom : x ∈ (U.onTy (.fvar p.1)).freeVars :=
        hxUdomE
      rw [hUagree p.1 hpτ hpnotG] at hxUdom
      have hxrigid := hRrange p.1 hpτ hpnotG x hxUdom
      have hxge : Φ ≤ x := freshVars_ge x (by simpa [Ys] using hxY)
      exact Nat.not_le_of_gt (hrigidbelow x hxrigid) hxge
  · intro hxG
    rcases List.mem_append.mp hxRY with hxrigid | hxY
    · exact hrigidG x hxrigid hxG
    · have hxlt := hGbelow x hxG
      have hxge := freshVars_ge x (by simpa [Ys] using hxY)
      omega

/-- The semantic core of a recursive-ceiling head is complete.  A locally
    closed unifier which keeps the outer rigid block fixed, agrees with the
    declarative residual on every retained member variable, and whose retained
    residual images are rigid can be normalised to the exact head format
    consumed by `RecCeilingConstraints`.

    In particular, the executable range guard is not an additional typing
    restriction: `range_within_rhs` first confines an MGU to the annotation's
    rigid variables plus its fresh opening; MGU factorisation through `U`
    eliminates that opening on every domain which survives `dropDomains G`. -/
private theorem RecCeilingConstraints.exists_head_of_witness
    {K rigid G : List Nat} {Φ : Nat} {τ : Ty} {σ : PolyTy} {R U : Subst}
    (hτlc : τ.IsLC)
    (hσwf : σ.WF) (hσrigid : ∀ x ∈ σ.body.freeVars, x ∈ rigid)
    (hrigidG : ∀ x ∈ rigid, x ∉ G)
    (hrigidbelow : ∀ x ∈ rigid, x < Φ)
    (hGbelow : ∀ x ∈ G, x < Φ)
    (hUlc : ∀ p ∈ U, p.2.IsLC)
    (hUuni : Unifies U ( τ)
      ( (σ.openVars (freshVars Φ σ.paramCount))))
    (hUfix : ∀ x ∈ K ++ rigid ++ freshVars Φ σ.paramCount,
      U.onTy (.fvar x) = .fvar x)
    (hUagree : ∀ z ∈ ( τ).freeVars, z ∉ G →
      U.onTy (.fvar z) = R.onTy (.fvar z))
    (hRrange : ∀ z ∈ ( τ).freeVars, z ∉ G →
      ∀ x ∈ (R.onTy (.fvar z)).freeVars, x ∈ rigid) :
    ∃ full step,
      UnifyRel ( τ)
          ( (σ.openVars (freshVars Φ σ.paramCount))) full ∧
      (∀ p ∈ full, p.1 ∉ K ++ rigid ++ freshVars Φ σ.paramCount) ∧
      step = Subst.dropDomains G full ∧
      (∀ p ∈ step, ∀ x ∈ p.2.freeVars, x ∈ rigid ∧ x ∉ G) ∧
      (∀ p ∈ step, p.2.IsLC) := by
  let Ys : List Nat := freshVars Φ σ.paramCount
  have hopenlc : (σ.openVars Ys).IsLC :=
    PolyTy.openVars_isLC hσwf (by simp [Ys])
  obtain ⟨full, hfull, havoid⟩ := UnifyRel.complete_K
    hτlc
    (by simpa [Ys] using hopenlc)
    hUlc hUuni hUfix
  let step : Subst := Subst.dropDomains G full
  have hstep_range : ∀ p ∈ step, ∀ x ∈ p.2.freeVars, x ∈ rigid ∧ x ∉ G := by
    simpa [step] using RecCeilingConstraints.dropDomains_range_of_witness
      hσrigid hrigidG hrigidbelow hGbelow hfull havoid hUuni hUfix hUagree hRrange
  refine ⟨full, step, hfull, havoid, rfl, hstep_range, ?_⟩
  intro p hp
  exact UnifyRel.lc hfull hτlc
    (by simpa [Ys] using hopenlc) p
    ((Subst.mem_dropDomains.mp hp).1)

/-- Concrete producer head for a declarative recursive ceiling.  Generality
    supplies the skolem-safe unifier; its non-pool range is forced into the
    annotation's rigid variables, so normalising through `complete_K` meets
    the exact `RecCeilingConstraints` head format. -/
private theorem RecCeilingConstraints.exists_head_of_generalizes
    {P rigid G : List Nat} {Φ : Nat} {τ : Ty} {σ : PolyTy} {R : Subst}
    (hG : G.Nodup)
    (hrigidG : ∀ x ∈ rigid, x ∉ G)
    (hPG : ∀ x ∈ P, x ∉ G)
    (hRlc : ∀ p ∈ R, p.2.IsLC)
    (hRP : ∀ x ∈ P, R.onTy (.fvar x) = .fvar x)
    (hRrigid : ∀ x ∈ rigid, R.onTy (.fvar x) = .fvar x)
    (hτlc : τ.IsLC) (hτbelow : τ.BelowFvars Φ)
    (hPbelow : ∀ x ∈ P, x < Φ)
    (hrigidbelow : ∀ x ∈ rigid, x < Φ)
    (hGbelow : ∀ x ∈ G, x < Φ)
    (hσwf : σ.WF)
    (hσrigid : ∀ x ∈ σ.body.freeVars, x ∈ rigid)
    (hgen : ( (R.onPolyTy (PolyTy.genGroup G τ))).Generalizes
      ( σ)) :
    ∃ full step,
      UnifyRel ( τ)
          ( (σ.openVars (freshVars Φ σ.paramCount))) full ∧
      (∀ p ∈ full, p.1 ∉ P ++ rigid ++ freshVars Φ σ.paramCount) ∧
      step = Subst.dropDomains G full ∧
      (∀ p ∈ step, ∀ x ∈ p.2.freeVars, x ∈ rigid ∧ x ∉ G) ∧
      (∀ p ∈ step, p.2.IsLC) ∧ Subst.Factors R step R := by
  let Rer : Subst := R
  have hgenE :
      (Rer.onPolyTy (PolyTy.genGroup G ( τ))).Generalizes
        ( σ) := by
    rw [show Rer = R from rfl]
    exact hgen
  obtain ⟨U, hUlc, hUuni, hUfix, hUagree⟩ :=
    RecCeilingConstraints.exists_skolem_safe_unifier hG hrigidG hPG
      hRlc hRP hRrigid hτlc hτbelow hPbelow hrigidbelow hσwf hσrigid hgen
  have hRrange : ∀ z ∈ ( τ).freeVars, z ∉ G →
      ∀ x ∈ (Rer.onTy (.fvar z)).freeVars, x ∈ rigid := by
    intro z hz hzG x hx
    exact hσrigid x (PolyTy.Generalizes.genGroup_nonpool_range hgenE hz hzG hx)
  obtain ⟨full, step, hfull, havoid, hstep, hrange, hstepLC⟩ :=
    RecCeilingConstraints.exists_head_of_witness hτlc hσwf hσrigid
      hrigidG hrigidbelow hGbelow hUlc hUuni hUfix hUagree hRrange
  refine ⟨full, step, hfull, havoid, hstep, hrange, hstepLC, ?_⟩
  exact RecCeilingConstraints.step_absorbed hG hrigidG hRlc hRrigid hτlc hτbelow
    hrigidbelow hfull havoid hstep hrange hstepLC hσwf hσrigid hgen

/-- Sequential recursive-ceiling certificates are complete once every
    annotated monomorphic position supplies its semantic head.  The length
    equality is intentional: `CeilingGenInv` quantifies over `zip`, whereas a
    `RecCeilingConstraints` derivation must account for *every* annotation and
    specification position.

    The head factory returns the residual factorisation in addition to the
    concrete ceiling fields.  That is precisely the datum needed to transport
    the per-position generality premise through `dropDomains G` before
    constructing the next head. -/
private theorem RecCeilingConstraints.exists_of_aligned_heads
    {K rigid G : List Nat} {Φ : Nat} {anns : List (Option PolyTy)}
    {specs : List RecSpec} {R : Subst}
    (hlen : anns.length = specs.length)
    (hannsWF : ∀ σ : PolyTy, some σ ∈ anns → σ.WF)
    (hannsRigid : ∀ σ : PolyTy, some σ ∈ anns →
      ∀ x ∈ σ.body.freeVars, x ∈ rigid)
    (hrigidBelow : ∀ x ∈ rigid, x < Φ)
    (hspecLC : ∀ s ∈ specs, s.LC)
    (hspecBelow : ∀ s ∈ specs, s.BelowFvars Φ)
    (hgen : CeilingGenInv G R anns specs)
    (hhead : ∀ {τ : Ty} {σ : PolyTy},
      τ.IsLC → τ.BelowFvars Φ → σ.WF →
      (∀ x ∈ σ.body.freeVars, x ∈ rigid) →
      ( (R.onPolyTy (PolyTy.genGroup G τ))).Generalizes
        ( σ) →
      ∃ full step,
        UnifyRel ( τ)
            ( (σ.openVars (freshVars Φ σ.paramCount))) full ∧
        (∀ p ∈ full, p.1 ∉ K ++ rigid ++ freshVars Φ σ.paramCount) ∧
        step = Subst.dropDomains G full ∧
        (∀ p ∈ step, ∀ x ∈ p.2.freeVars, x ∈ rigid ∧ x ∉ G) ∧
        (∀ p ∈ step, p.2.IsLC) ∧ Subst.Factors R step R) :
    ∃ Sc, RecCeilingConstraints K rigid G Φ anns specs Sc ∧ Subst.Factors R Sc R := by
  induction anns generalizing specs with
  | nil =>
      cases specs with
      | nil =>
          refine ⟨[], rfl, ?_⟩
          intro t
          exact Eq.refl _
      | cons spec specs => simp at hlen
  | cons ann anns ih =>
      cases specs with
      | nil => simp at hlen
      | cons spec specs =>
          have hlenTail : anns.length = specs.length := by simpa using hlen
          cases ann with
          | none =>
              obtain ⟨tail, htail, hfacTail⟩ := ih (specs := specs) hlenTail
                (fun σ hσ => hannsWF σ (List.mem_cons_of_mem _ hσ))
                (fun σ hσ x hx => hannsRigid σ (List.mem_cons_of_mem _ hσ) x hx)
                (fun s hs => hspecLC s (List.mem_cons_of_mem _ hs))
                (fun s hs => hspecBelow s (List.mem_cons_of_mem _ hs))
                (by
                  intro a s hs
                  exact hgen (by
                  rw [List.zip_cons_cons]
                  exact List.mem_cons_of_mem _ hs))
              exact ⟨tail, htail, hfacTail⟩
          | some σ =>
              cases spec with
              | poly σ' =>
                  have hfalse := hgen (by
                    rw [List.zip_cons_cons]
                    exact List.mem_cons_self)
                  exact False.elim hfalse
              | mono τ =>
                  have hσwf : σ.WF := hannsWF σ List.mem_cons_self
                  have hσrigid : ∀ x ∈ σ.body.freeVars, x ∈ rigid :=
                    hannsRigid σ List.mem_cons_self
                  have hτlc : τ.IsLC := by
                    simpa using hspecLC (.mono τ) List.mem_cons_self
                  have hτbelow : τ.BelowFvars Φ := by
                    simpa using hspecBelow (.mono τ) List.mem_cons_self
                  have hgenHead :
                      ( (R.onPolyTy (PolyTy.genGroup G τ))).Generalizes
                        ( σ) :=
                    hgen (by
                      rw [List.zip_cons_cons]
                      exact List.mem_cons_self)
                  obtain ⟨full, step, hfull, havoid, hstep, hrange, hstepLC, hfacHead⟩ :=
                    hhead hτlc hτbelow hσwf hσrigid hgenHead
                  have hdom : ∀ p ∈ step, p.1 ∉ G := by
                    intro p hp
                    rw [hstep] at hp
                    exact (Subst.mem_dropDomains.mp hp).2
                  have hgenTail : CeilingGenInv G R anns
                      (specs.map (RecSpec.onSubst step)) := by
                    intro a s hs
                    rcases List.mem_zip_map_right hs with ⟨a0, s0, hs0, heq⟩
                    injection heq with ha hs'
                    cases ha
                    cases hs'
                    have hold := hgen (by
                      rw [List.zip_cons_cons]
                      exact List.mem_cons_of_mem _ hs0)
                    cases a with
                    | none => trivial
                    | some σ0 =>
                        cases s0 with
                        | poly σ1 => exact False.elim hold
                        | mono τ0 =>
                            have hstable := Subst.Factors.genGroup_stable
                              (U := R) (Sc := step) (G := G) (τ := τ0)
                              hfacHead hdom (fun p hp x hx => (hrange p hp x hx).2)
                            change
                              (
                                (R.onPolyTy (PolyTy.genGroup G (step.onTy τ0)))).Generalizes
                                ( σ0)
                            rw [hstable]
                            exact hold
                  have hstepBelow : ∀ p ∈ step, p.2.BelowFvars Φ := by
                    intro p hp
                    exact Ty.BelowFvars.of_freeVars_lt (fun x hx =>
                      hrigidBelow x (hrange p hp x hx).1)
                  obtain ⟨tail, htail, hfacTail⟩ := ih
                    (specs := specs.map (RecSpec.onSubst step)) (by simpa using hlenTail)
                    (fun σ hσ => hannsWF σ (List.mem_cons_of_mem _ hσ))
                    (fun σ hσ x hx => hannsRigid σ (List.mem_cons_of_mem _ hσ) x hx)
                    (fun s hs => by
                      obtain ⟨s0, hs0, rfl⟩ := List.mem_map.mp hs
                      exact RecSpec.LC.onSubst hstepLC
                        (hspecLC s0 (List.mem_cons_of_mem _ hs0)))
                    (fun s hs => by
                      obtain ⟨s0, hs0, rfl⟩ := List.mem_map.mp hs
                      exact RecSpec.BelowFvars.onSubst hstepBelow
                        (hspecBelow s0 (List.mem_cons_of_mem _ hs0)))
                    hgenTail
                  refine ⟨step ++ tail, ?_⟩
                  refine ⟨⟨full, step, tail, hfull, havoid, hstep, hrange, hstepLC,
                    hσwf, hσrigid, htail, rfl⟩, ?_⟩
                  intro t
                  simpa [Subst.onTy_append] using
                    Eq.trans (hfacHead t) (hfacTail (step.onTy t))

/-- Concrete list-level producer bridge for recursive ceilings.  The protected
    set may be the caller's `K` with group names filtered out; the output still
    avoids the original `K` after `dropDomains G` (via
    `dropDomains_dom_avoids_filter`). -/
private theorem RecCeilingConstraints.exists_of_generalizes
    {P rigid G : List Nat} {Φ : Nat} {anns : List (Option PolyTy)}
    {specs : List RecSpec} {R : Subst}
    (hlen : anns.length = specs.length)
    (hG : G.Nodup)
    (hrigidG : ∀ x ∈ rigid, x ∉ G)
    (hPG : ∀ x ∈ P, x ∉ G)
    (hRlc : ∀ p ∈ R, p.2.IsLC)
    (hRP : ∀ x ∈ P, R.onTy (.fvar x) = .fvar x)
    (hRrigid : ∀ x ∈ rigid, R.onTy (.fvar x) = .fvar x)
    (hPbelow : ∀ x ∈ P, x < Φ)
    (hrigidBelow : ∀ x ∈ rigid, x < Φ)
    (hGbelow : ∀ x ∈ G, x < Φ)
    (hannsWF : ∀ σ : PolyTy, some σ ∈ anns → σ.WF)
    (hannsRigid : ∀ σ : PolyTy, some σ ∈ anns →
      ∀ x ∈ σ.body.freeVars, x ∈ rigid)
    (hspecLC : ∀ s ∈ specs, s.LC)
    (hspecBelow : ∀ s ∈ specs, s.BelowFvars Φ)
    (hgen : CeilingGenInv G R anns specs) :
    ∃ Sc, RecCeilingConstraints P rigid G Φ anns specs Sc ∧ Subst.Factors R Sc R := by
  apply RecCeilingConstraints.exists_of_aligned_heads (K := P) hlen
    hannsWF hannsRigid hrigidBelow hspecLC hspecBelow hgen
  intro τ σ hτlc hτbelow hσwf hσrigid hgenHead
  exact RecCeilingConstraints.exists_head_of_generalizes hG hrigidG hPG
    hRlc hRP hRrigid hτlc hτbelow hPbelow hrigidBelow hGbelow hσwf hσrigid hgenHead

/-- Executable completeness of the sequential recursive-ceiling pass.

    Unlike `exists_of_generalizes`, this theorem runs the particular
    `unifyCoreK` chosen by the implementation.  The skolem-safe witness makes
    that unifier succeed; `dropDomains_range_of_witness` then proves that this
    concrete result passes the executable `rangesWithin` guard.  The explicit
    `K`/`G` disjointness is the lexical invariant of an actual `letRec` call:
    it is stronger than the filtered protection used by relational producer
    completeness, and is exactly what the worker passes to `unifyCoreK`. -/
private theorem RecCeilingConstraints.solve_complete_of_generalizes
    {K rigid G : List Nat} {Φ : Nat} {anns : List (Option PolyTy)}
    {specs : List RecSpec} {R : Subst}
    (hlen : anns.length = specs.length)
    (hG : G.Nodup)
    (hrigidG : ∀ x ∈ rigid, x ∉ G)
    (hKG : ∀ x ∈ K, x ∉ G)
    (hRlc : ∀ p ∈ R, p.2.IsLC)
    (hRK : ∀ x ∈ K, R.onTy (.fvar x) = .fvar x)
    (hRrigid : ∀ x ∈ rigid, R.onTy (.fvar x) = .fvar x)
    (hKbelow : ∀ x ∈ K, x < Φ)
    (hrigidBelow : ∀ x ∈ rigid, x < Φ)
    (hGbelow : ∀ x ∈ G, x < Φ)
    (hannsWF : ∀ σ : PolyTy, some σ ∈ anns → σ.WF)
    (hannsRigid : ∀ σ : PolyTy, some σ ∈ anns →
      ∀ x ∈ σ.body.freeVars, x ∈ rigid)
    (hspecLC : ∀ s ∈ specs, s.LC)
    (hspecBelow : ∀ s ∈ specs, s.BelowFvars Φ)
    (hgen : CeilingGenInv G R anns specs) :
    ∃ out : { Sc : Subst // RecCeilingConstraints K rigid G Φ anns specs Sc ∧
        ∀ p ∈ Sc, p.1 ∉ K },
      solveRecCeilingConstraints K rigid G Φ anns specs hannsWF hannsRigid hspecLC = some out ∧
        Subst.Factors R out.1 R := by
  induction anns generalizing specs with
  | nil =>
      cases specs with
      | nil =>
          refine ⟨⟨[], by simp [RecCeilingConstraints]⟩, ?_, ?_⟩
          · simp [solveRecCeilingConstraints]
          · intro t
            exact Eq.refl _
      | cons spec specs => simp at hlen
  | cons ann anns ih =>
      cases specs with
      | nil => simp at hlen
      | cons spec specs =>
          have hlenTail : anns.length = specs.length := by simpa using hlen
          cases ann with
          | none =>
              have hgenTail : CeilingGenInv G R anns specs := by
                intro a s hs
                exact hgen (by
                  rw [List.zip_cons_cons]
                  exact List.mem_cons_of_mem _ hs)
              obtain ⟨out, hout, hfac⟩ := ih (specs := specs) hlenTail
                (fun σ hσ => hannsWF σ (List.mem_cons_of_mem _ hσ))
                (fun σ hσ x hx => hannsRigid σ (List.mem_cons_of_mem _ hσ) x hx)
                (fun s hs => hspecLC s (List.mem_cons_of_mem _ hs))
                (fun s hs => hspecBelow s (List.mem_cons_of_mem _ hs)) hgenTail
              obtain ⟨tail, htail, htailK⟩ := out
              refine ⟨⟨tail, htail, htailK⟩, ?_, hfac⟩
              simp only [solveRecCeilingConstraints]
              rw [hout]
          | some σ =>
              cases spec with
              | poly σ' =>
                  have hfalse := hgen (by
                    rw [List.zip_cons_cons]
                    exact List.mem_cons_self)
                  exact False.elim hfalse
              | mono τ =>
                  have hσwf : σ.WF := hannsWF σ List.mem_cons_self
                  have hσrigid : ∀ x ∈ σ.body.freeVars, x ∈ rigid :=
                    hannsRigid σ List.mem_cons_self
                  have hτlc : τ.IsLC := by
                    simpa using hspecLC (.mono τ) List.mem_cons_self
                  have hτbelow : τ.BelowFvars Φ := by
                    simpa using hspecBelow (.mono τ) List.mem_cons_self
                  have hgenHead :
                      ( (R.onPolyTy (PolyTy.genGroup G τ))).Generalizes
                        ( σ) :=
                    hgen (by
                      rw [List.zip_cons_cons]
                      exact List.mem_cons_self)
                  let Rer : Subst := R
                  have hgenE :
                      (Rer.onPolyTy (PolyTy.genGroup G ( τ))).Generalizes
                        ( σ) := by
                    rw [show Rer = R from rfl]
                    exact hgenHead
                  obtain ⟨U, hUlc, hUuni, hUfix, hUagree⟩ :=
                    RecCeilingConstraints.exists_skolem_safe_unifier hG hrigidG hKG
                      hRlc hRK hRrigid hτlc hτbelow hKbelow hrigidBelow hσwf hσrigid hgenHead
                  have hRrange : ∀ z ∈ ( τ).freeVars, z ∉ G →
                      ∀ x ∈ (Rer.onTy (.fvar z)).freeVars, x ∈ rigid := by
                    intro z hz hzG x hx
                    exact hσrigid x
                      (PolyTy.Generalizes.genGroup_nonpool_range hgenE hz hzG hx)
                  have hcore :
                      (unifyCoreK (K ++ rigid ++ freshVars Φ σ.paramCount)
                        ( τ)
                        ( (σ.openVars (freshVars Φ σ.paramCount)))).isSome :=
                    unifyCoreK_complete hτlc
                      (PolyTy.openVars_isLC hσwf (by simp)) hUlc hUuni hUfix
                  obtain ⟨⟨full, hfull, havoid⟩, hfullExec⟩ :=
                    Option.isSome_iff_exists.mp hcore
                  let step : Subst := Subst.dropDomains G full
                  have hrange : ∀ p ∈ step, ∀ x ∈ p.2.freeVars, x ∈ rigid ∧ x ∉ G := by
                    simpa [step] using RecCeilingConstraints.dropDomains_range_of_witness
                      hσrigid hrigidG hrigidBelow hGbelow hfull havoid hUuni hUfix hUagree hRrange
                  have hrangeB : step.rangesWithin rigid G = true :=
                    Subst.rangesWithin_iff.mpr hrange
                  have hstepLC : ∀ p ∈ step, p.2.IsLC := by
                    intro p hp
                    exact UnifyRel.lc hfull hτlc
                      (PolyTy.openVars_isLC hσwf (by simp)) p
                      ((Subst.mem_dropDomains.mp hp).1)
                  have hfacHead : Subst.Factors R step R :=
                    RecCeilingConstraints.step_absorbed hG hrigidG hRlc hRrigid hτlc hτbelow
                      hrigidBelow hfull havoid rfl hrange hstepLC hσwf hσrigid hgenHead
                  have hdom : ∀ p ∈ step, p.1 ∉ G := by
                    intro p hp
                    exact (Subst.mem_dropDomains.mp hp).2
                  have hgenTail : CeilingGenInv G R anns
                      (specs.map (RecSpec.onSubst step)) := by
                    intro a s hs
                    rcases List.mem_zip_map_right hs with ⟨a0, s0, hs0, heq⟩
                    injection heq with ha hs'
                    cases ha
                    cases hs'
                    have hold := hgen (by
                      rw [List.zip_cons_cons]
                      exact List.mem_cons_of_mem _ hs0)
                    cases a with
                    | none => trivial
                    | some σ0 =>
                        cases s0 with
                        | poly σ1 => exact False.elim hold
                        | mono τ0 =>
                            have hstable := Subst.Factors.genGroup_stable
                              (U := R) (Sc := step) (G := G) (τ := τ0)
                              hfacHead hdom (fun p hp x hx => (hrange p hp x hx).2)
                            change
                              (
                                (R.onPolyTy (PolyTy.genGroup G (step.onTy τ0)))).Generalizes
                                ( σ0)
                            rw [hstable]
                            exact hold
                  have hstepBelow : ∀ p ∈ step, p.2.BelowFvars Φ := by
                    intro p hp
                    exact Ty.BelowFvars.of_freeVars_lt (fun x hx =>
                      hrigidBelow x (hrange p hp x hx).1)
                  obtain ⟨outTail, htailExec, hfacTail⟩ := ih
                    (specs := specs.map (RecSpec.onSubst step)) (by simpa using hlenTail)
                    (fun σ hσ => hannsWF σ (List.mem_cons_of_mem _ hσ))
                    (fun σ hσ x hx => hannsRigid σ (List.mem_cons_of_mem _ hσ) x hx)
                    (fun s hs => by
                      obtain ⟨s0, hs0, rfl⟩ := List.mem_map.mp hs
                      exact RecSpec.LC.onSubst hstepLC
                        (hspecLC s0 (List.mem_cons_of_mem _ hs0)))
                    (fun s hs => by
                      obtain ⟨s0, hs0, rfl⟩ := List.mem_map.mp hs
                      exact RecSpec.BelowFvars.onSubst hstepBelow
                        (hspecBelow s0 (List.mem_cons_of_mem _ hs0)))
                    hgenTail
                  obtain ⟨tail, htail, htailK⟩ := outTail
                  let hrel : RecCeilingConstraints K rigid G Φ (some σ :: anns)
                      (.mono τ :: specs) (step ++ tail) :=
                    ⟨full, step, tail, hfull, havoid, rfl, hrange, hstepLC,
                      hσwf, hσrigid, htail, rfl⟩
                  refine ⟨⟨step ++ tail, hrel, ?_⟩, ?_, ?_⟩
                  · intro p hp
                    exact (RecCeilingConstraints.dom_avoids hrel p hp).1
                  · simp only [solveRecCeilingConstraints]
                    rw [hfullExec]
                    dsimp
                    split
                    · rw [htailExec]
                    · rename_i hnot
                      exact False.elim (hnot (by simpa [step] using hrangeB))
                  · intro t
                    simpa [Subst.onTy_append] using
                      Eq.trans (hfacHead t) (hfacTail (step.onTy t))

/-- Shared residual construction for variable and constructor leaves. It moves
    the algorithm's fresh opening block out of the way, realizes the
    declarative instantiation there, and swaps the result back. -/
theorem Infer.exists_var_residual {Φ k : Nat} {S₀ : Subst} {K : List Nat}
    {ty : Ty} {instArgs : List Ty} {τ₀ : Ty}
    (hS₀ : ∀ p ∈ S₀, p.2.IsLC)
    (hKΦ : ∀ k ∈ K, k < Φ)
    (hKfix : ∀ k ∈ K, S₀.onTy (Ty.fvar k) = Ty.fvar k)
    (hinst : InstantiatesBy instArgs ( (S₀.onTy ty)) τ₀)
    (hbv : ContainsBvarsUpTo k ty)
    (htyfree : ∀ v ∈ ty.freeVars, v < Φ)
    (hinstLC : ∀ t ∈ instArgs, t.IsLC) :
    ∃ R : Subst, (∀ p ∈ R, p.2.IsLC) ∧
      (∀ k ∈ K, R.onTy (Ty.fvar k) = Ty.fvar k) ∧
      (∀ v, v < Φ → R.onTy (Ty.fvar v) = S₀.onTy (Ty.fvar v)) ∧
      Eq τ₀ (R.onTy (Ty.openVars (freshVars Φ k) ty)) := by
  obtain ⟨W, hWge, hWfresh⟩ := exists_fresh_block
    (S₀.map Prod.fst ++ S₀.flatMap (fun p => p.2.freeVars) ++ τ₀.freeVars) Φ k
  set proxy : Subst := blockList Φ W k with hproxy_def
  set breal : Subst := (freshVars W k).zip instArgs with hbreal_def
  set R : Subst := proxy ++ S₀ ++ breal with hR_def
  have hWΦ : Φ ≤ W := by omega
  have hW_S₀key : ∀ p ∈ S₀, p.1 < W := by
    intro p hp
    exact hWfresh p.1 (List.mem_append_left _ (List.mem_append_left _
      (List.mem_map.mpr ⟨p, hp, rfl⟩)))
  have hW_S₀ran : ∀ p ∈ S₀, ∀ u ∈ p.2.freeVars, u < W := by
    intro p hp u hu
    exact hWfresh u (List.mem_append_left _ (List.mem_append_right _
      (List.mem_flatMap.mpr ⟨p, hp, hu⟩)))
  have hW_τ₀ : ∀ u ∈ τ₀.freeVars, u < W := by
    intro u hu
    exact hWfresh u (List.mem_append_right _ hu)
  have hproxyfix : ∀ m, m < Φ → proxy.onTy (Ty.fvar m) = Ty.fvar m := by
    intro m hm
    rw [hproxy_def]
    apply Ty.substFvars_eq_self_of_no_key
    intro p hp hc
    simp only [blockList, List.mem_map] at hp
    obtain ⟨i, _, rfl⟩ := hp
    simp only [Ty.freeVars, List.mem_singleton] at hc
    omega
  have hτW : ∀ v ∈ (Ty.openVars (freshVars Φ k) ty).freeVars,
      ¬ (W ≤ v ∧ v < W + k) := by
    intro v hv
    rcases Ty.freeVars_openVars_subset v hv with h | h
    · have hvW : v < W := lt_of_lt_of_le (htyfree v h) hWΦ
      omega
    · have hge : Φ ≤ v := freshVars_ge v h
      have hlt : v < Φ + k := freshVars_lt v h
      omega
  have hproxy : proxy.onTy (Ty.openVars (freshVars Φ k) ty) =
      Ty.openVars (freshVars W k) ty := by
    rw [hproxy_def]
    rw [blockList_onTy (Φ := Φ) (W := W) (k := k) hWge hτW]
    exact Ty.rename_openVars_blockSwap hWge ty htyfree
  have hS₀comm : S₀.onTy (Ty.openVars (freshVars W k) ty) =
      Ty.openVars (freshVars W k) (S₀.onTy ty) :=
    Subst.onTy_openVars hS₀ (fun p hp hc => by
      have hlt : p.1 < W := hW_S₀key p hp
      simp only [freshVars, List.mem_map, List.mem_range] at hc
      obtain ⟨i, _, hpq⟩ := hc
      omega)
  have hbv' : ContainsBvarsUpTo k ( (S₀.onTy ty)) :=
    ContainsBvarsUpTo.substFvars hS₀ hbv
  have hzip := InstantiatesBy.onTy_openVars_zip (Xs := freshVars W k)
    (ty :=  (S₀.onTy ty)) (τ := τ₀) (tyArgs := instArgs) hinst
    (by simpa [freshVars_length] using hbv') freshVars_nodup
    (fun x hx hu => by
      have hge : W ≤ x := freshVars_ge x hx
      have hlt : x < W := hW_τ₀ x hu
      omega)
  have hzip' : breal.onTy
      ( (Ty.openVars (freshVars W k) (S₀.onTy ty))) = τ₀ := by
    simpa [hbreal_def] using hzip
  refine ⟨R, ?_, ?_, ?_, ?_⟩
  · intro p hp
    rw [hR_def] at hp
    rcases List.mem_append.mp hp with hp' | hp'
    · rcases List.mem_append.mp hp' with hp'' | hp''
      · rw [hproxy_def] at hp''
        exact blockList_lc Φ W k p hp''
      · exact hS₀ p hp''
    · rw [hbreal_def] at hp'
      exact hinstLC p.2 (List.of_mem_zip hp').2
  · intro k hk
    have hklt := hKΦ k hk
    calc R.onTy (Ty.fvar k)
        = breal.onTy (S₀.onTy (proxy.onTy (Ty.fvar k))) := by
            rw [hR_def, Subst.onTy_append, Subst.onTy_append]
      _ = breal.onTy (S₀.onTy (Ty.fvar k)) := by rw [hproxyfix k hklt]
      _ = breal.onTy (Ty.fvar k) := by rw [hKfix k hk]
      _ = Ty.fvar k := by
        rw [hbreal_def]
        apply Ty.substFvars_eq_self_of_no_key
        intro p hp hc
        have hge : W ≤ p.1 := freshVars_ge p.1 (List.of_mem_zip hp).1
        simp only [Ty.freeVars, List.mem_singleton] at hc
        omega
  · intro v hv
    calc R.onTy (Ty.fvar v)
        = breal.onTy (S₀.onTy (proxy.onTy (Ty.fvar v))) := by
            rw [hR_def, Subst.onTy_append, Subst.onTy_append]
      _ = breal.onTy (S₀.onTy (Ty.fvar v)) := by rw [hproxyfix v hv]
      _ = S₀.onTy (Ty.fvar v) := by
        rw [hbreal_def]
        apply Ty.substFvars_eq_self_of_no_key
        intro p hp hc
        have hge : W ≤ p.1 := freshVars_ge p.1 (List.of_mem_zip hp).1
        have hp_notmem : p.1 ∉ (S₀.onTy (Ty.fvar v)).freeVars :=
          Subst.not_mem_onTy_freeVars
            (fun q hq hcq => by have := hW_S₀ran q hq p.1 hcq; omega)
            (by simp only [Ty.freeVars, List.mem_singleton]; omega)
        exact hp_notmem hc
  · show  τ₀ =
       (R.onTy (Ty.openVars (freshVars Φ k) ty))
    rw [hR_def, Subst.onTy_append, Subst.onTy_append, hproxy, hS₀comm]
    exact hzip'.symm

/-- Producer completeness for primitive literals. -/
theorem Infer.complete_prim {p : PrimLitExpr} : Infer.CompleteAt (.primLit p) := by
  intro Φ ctx S₀ τ₀ K _ _ hS₀ _ _ hKfix hty
  cases p with
  | unit =>
    cases hty with
    | primLitUnit =>
      refine ⟨Φ, [], .prim .unit, S₀, .primLitUnit, ?_, ?_, ?_, ?_, ?_⟩
      · intro v hv; rfl
      · simp [Eq]
      · exact hS₀
      · exact hKfix
      · simp
  | int n =>
    cases hty with
    | primLitInt =>
      refine ⟨Φ, [], .prim .int, S₀, .primLitInt, ?_, ?_, ?_, ?_, ?_⟩
      · intro v hv; rfl
      · simp [Eq]
      · exact hS₀
      · exact hKfix
      · simp
  | nat n =>
    cases hty with
    | primLitNat =>
      refine ⟨Φ, [], .prim .nat, S₀, .primLitNat, ?_, ?_, ?_, ?_, ?_⟩
      · intro v hv; rfl
      · simp [Eq]
      · exact hS₀
      · exact hKfix
      · simp
  | char c =>
    cases hty with
    | primLitChar =>
      refine ⟨Φ, [], .prim .char, S₀, .primLitChar, ?_, ?_, ?_, ?_, ?_⟩
      · intro v hv; rfl
      · simp [Eq]
      · exact hS₀
      · exact hKfix
      · simp

/-- Producer completeness for primitive operators. -/
theorem Infer.complete_primBinOp {op : PrimBinOp} :
    Infer.CompleteAt (.primBinOp op) := by
  intro Φ ctx S₀ τ₀ K _ _ hS₀ _ _ hKfix hty
  cases op with
  | intAdd =>
    cases hty with
    | primBinOpIntAdd =>
      refine ⟨Φ, [], .arrow (.prim .int) (.arrow (.prim .int) (.prim .int)), S₀,
        .primBinOpIntAdd, ?_, ?_, ?_, ?_, ?_⟩
      · intro v hv; rfl
      · simp [Eq]
      · exact hS₀
      · exact hKfix
      · simp
  | intSub =>
    cases hty with
    | primBinOpIntSub =>
      refine ⟨Φ, [], .arrow (.prim .int) (.arrow (.prim .int) (.prim .int)), S₀,
        .primBinOpIntSub, ?_, ?_, ?_, ?_, ?_⟩
      · intro v hv; rfl
      · simp [Eq]
      · exact hS₀
      · exact hKfix
      · simp

  | intLt =>
    cases hty with
    | primBinOpIntLt hT hF =>
      obtain ⟨trueC, hlookT, hbT⟩ :=
        Ctor.isBoolCtor_of_typeOfHM (ctx := S₀.onCtx ctx) hT
      obtain ⟨falseC, hlookF, hbF⟩ :=
        Ctor.isBoolCtor_of_typeOfHM (ctx := S₀.onCtx ctx) hF
      refine ⟨Φ, [],
        .arrow (.prim .int) (.arrow (.prim .int) (.customTy ⟨"Bool"⟩ [])), S₀,
        .primBinOpIntLt hlookT hbT hlookF hbF, ?_, ?_, ?_, ?_, ?_⟩
      · intro v hv; rfl
      · simp [Eq]
      · exact hS₀
      · exact hKfix
      · simp

  | charLt =>
    cases hty with
    | primBinOpCharLt hT hF =>
      obtain ⟨trueC, hlookT, hbT⟩ :=
        Ctor.isBoolCtor_of_typeOfHM (ctx := S₀.onCtx ctx) hT
      obtain ⟨falseC, hlookF, hbF⟩ :=
        Ctor.isBoolCtor_of_typeOfHM (ctx := S₀.onCtx ctx) hF
      refine ⟨Φ, [],
        .arrow (.prim .char) (.arrow (.prim .char) (.customTy ⟨"Bool"⟩ [])), S₀,
        .primBinOpCharLt hlookT hbT hlookF hbF, ?_, ?_, ?_, ?_, ?_⟩
      · intro v hv; rfl
      · simp [Eq]
      · exact hS₀
      · exact hKfix
      · simp

/-- Producer completeness for term variables. The residual block-swap realizes
    any declarative instantiation of the looked-up scheme while inference uses
    its canonical fresh-variable opening. -/
theorem Infer.complete_var {i : Nat} : Infer.CompleteAt (.var i) := by
  intro Φ ctx S₀ τ₀ K hwf hbelow hS₀ hKΦ _ hKfix hty
  cases hty with
  | var hlook hlc hinst =>
    rename_i polyTy instArgs
    obtain ⟨σ, hlkσ, hσ₀'⟩ :
        ∃ σ, ctx.env[i]? = some σ ∧ Subst.onPolyTy S₀ σ = polyTy := by
      simpa [Subst.onCtx, Subst.onEnv] using hlook
    have hbody : polyTy.body =  (S₀.onTy σ.body) := by
      rw [← hσ₀', Subst.onPolyTy]
    have hinst' : InstantiatesBy instArgs ( (S₀.onTy σ.body)) τ₀ := by
      rw [← hbody]
      exact hinst
    have hbv : ContainsBvarsUpTo σ.paramCount σ.body :=
      hwf σ (List.mem_of_getElem? hlkσ)
    have htyfree : ∀ v ∈ σ.body.freeVars, v < Φ :=
      (hbelow σ (List.mem_of_getElem? hlkσ)).mem_lt
    obtain ⟨R, hRlc, hRK, hRag, hRagree⟩ :=
      Infer.exists_var_residual (Φ := Φ) (k := σ.paramCount) (S₀ := S₀) (K := K)
        (ty := σ.body) (instArgs := instArgs) (τ₀ := τ₀)
        hS₀ hKΦ hKfix hinst' hbv htyfree hlc
    refine ⟨Φ + σ.paramCount, [], σ.openVars (freshVars Φ σ.paramCount), R,
      .var hlkσ, ?_, ?_, ?_, ?_, ?_⟩
    · intro v hv; exact (hRag v hv).symm
    · exact hRagree
    · exact hRlc
    · exact hRK
    · simp

/-- Producer completeness for data constructors. -/
theorem Infer.complete_ctor {name : CtorName} : Infer.CompleteAt (.ctor name) := by
  intro Φ ctx S₀ τ₀ K _ _ hS₀ hKΦ _ hKfix hty
  cases hty with
  | ctor hlook hlc hinst =>
    rename_i ctorE tyArgs
    have hlookR : LookupList.get? ctx.ctors name = some ctorE := by
      simpa [Subst.onCtx] using hlook
    have hinst' : InstantiatesBy tyArgs
        ( (S₀.onTy ctorE.toTy.body)) τ₀ := by
      have hclosed : S₀.onTy ctorE.toTy.body = ctorE.toTy.body :=
        Ty.substFvars_eq_self_of_no_key
          (fun p _ hc =>
            NoFreeVars.not_mem_freeVars (Ctor.toTy_body_noFreeVars ctorE) p.1 hc)
      rw [hclosed]
      exact hinst
    obtain ⟨R, hRlc, hRK, hRag, hRagree⟩ :=
      Infer.exists_var_residual (Φ := Φ) (k := ctorE.paramCount) (S₀ := S₀) (K := K)
        (ty := ctorE.toTy.body) (instArgs := tyArgs) (τ₀ := τ₀)
        hS₀ hKΦ hKfix hinst' (Ctor.toTy_wf ctorE)
        (fun v hv =>
          absurd hv (NoFreeVars.not_mem_freeVars (Ctor.toTy_body_noFreeVars ctorE) v))
        hlc
    refine ⟨Φ + ctorE.paramCount, [],
      ctorE.toTy.openVars (freshVars Φ ctorE.paramCount), R,
      .ctor hlookR, ?_, ?_, ?_, ?_, ?_⟩
    · intro v hv; exact (hRag v hv).symm
    · exact hRagree
    · exact hRlc
    · exact hRK
    · simp

/-! ### Lambda producer completeness -/

/-- Producer completeness for an unannotated lambda, with its freshly allocated
    parameter variable realized through the residual passed to the body IH. -/
theorem Infer.complete_lambda_aux {body : Expr} {Φ : Nat} {ctx : Ctx}
    {S₀ : Subst} {paramTy bodyTy : Ty} {K : List Nat}
    (ih : Infer.CompleteAt body)
    (hwf : CtxWF ctx) (hbelow : CtxBelow Φ ctx) (hS₀ : ∀ p ∈ S₀, p.2.IsLC)
    (hparamLC : paramTy.IsLC) (hKΦ : ∀ k ∈ K, k < Φ)
    (hbodyK : ∀ y ∈ body.tyFreeVars, y ∈ K)
    (hKfix : ∀ k ∈ K, S₀.onTy (.fvar k) = .fvar k)
    (hbodyty : TypeOfHM { (S₀.onCtx ctx) with
        env := PolyTy.mkTrivial ( paramTy) :: (S₀.onCtx ctx).env }
        body ( bodyTy)) :
    ∃ Φ' S τ R,
      Infer Φ ctx (.lambda none body) Φ' S τ ∧
      Subst.AgreesBelow Φ S₀ (S ++ R) ∧
      Eq (Ty.arrow paramTy bodyTy) (R.onTy τ) ∧
      (∀ p ∈ R, p.2.IsLC) ∧
      (∀ k ∈ K, R.onTy (.fvar k) = .fvar k) ∧
      (∀ p ∈ S, p.1 ∉ K) := by
  obtain ⟨W, c, hWle, hcle, hWcne, hWav, hcav⟩ := exists_fresh_two_ge Φ
    (Φ :: (S₀.map Prod.fst ++ S₀.flatMap (fun p => p.2.freeVars)))
  have hWneΦ : W ≠ Φ := by
    intro he
    apply hWav
    rw [← he]
    exact List.mem_cons_self
  have hWlt : Φ < W := lt_of_le_of_ne hWle (fun he => hWneΦ he.symm)
  have hWnokey : ∀ p ∈ S₀, p.1 ≠ W := by
    intro p hp he
    apply hWav
    rw [← he]
    apply List.mem_cons_of_mem
    apply List.mem_append_left
    exact List.mem_map.mpr ⟨p, hp, rfl⟩
  have hWnorange : ∀ p ∈ S₀, ∀ v ∈ p.2.freeVars, v ≠ W := by
    intro p hp v hv he
    apply hWav
    rw [← he]
    apply List.mem_cons_of_mem
    apply List.mem_append_right
    exact List.mem_flatMap.mpr ⟨p, hp, hv⟩
  set bodyCtx : Ctx := { ctx with env := PolyTy.mkTrivial (.fvar Φ) :: ctx.env }
  set S₀' : Subst := [(Φ, Ty.fvar W)] ++ (S₀ ++ [(W, paramTy)]) with hS₀'def
  have hbodyCtxWF : CtxWF bodyCtx := by
    intro M hM
    rcases List.mem_cons.mp hM with rfl | hM
    · exact ContainsBvarsUpTo.fvar
    · exact hwf M hM
  have hbodyCtxBelow : CtxBelow (Φ + 1) bodyCtx := by
    intro M hM
    rcases List.mem_cons.mp hM with rfl | hM
    · exact Ty.BelowFvars.fvar (by omega)
    · exact (hbelow M hM).mono (by omega)
  have hS₀' : ∀ p ∈ S₀', p.2.IsLC := by
    intro p hp
    rw [hS₀'def] at hp
    rcases List.mem_append.mp hp with hp' | hp'
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hp'
      rcases hp' with rfl
      exact ContainsBvarsUpTo.fvar
    · rcases List.mem_append.mp hp' with hp'' | hp''
      · exact hS₀ p hp''
      · simp only [List.mem_singleton] at hp''
        rcases hp'' with rfl
        exact hparamLC
  have hS₀'W : S₀.onTy (Ty.fvar W) = Ty.fvar W := by
    exact Ty.substFvars_eq_self_of_no_key (fun p hp hc =>
      hWnokey p hp (by simpa [Ty.freeVars] using hc))
  have hS₀'fvar : S₀'.onTy (Ty.fvar Φ) = paramTy := by
    rw [hS₀'def, Subst.onTy_append, Subst.onTy_append]
    rw [show Subst.onTy [(Φ, Ty.fvar W)] (Ty.fvar Φ) = Ty.fvar W by
      simp [Subst.onTy, Ty.substFvars, Ty.substFvar]]
    rw [hS₀'W]
    rw [show Subst.onTy [(W, paramTy)] (Ty.fvar W) = paramTy by
      simp [Subst.onTy, Ty.substFvars, Ty.substFvar]]
  have hS₀'onEnv : S₀'.onEnv ctx.env = S₀.onEnv ctx.env := by
    simp only [Subst.onEnv]
    apply List.map_congr_left
    intro M hM
    simp only [Subst.onPolyTy]
    congr 1
    rw [hS₀'def, Subst.onTy_append, Subst.onTy_append]
    have hΦM : Φ ∉ M.body.freeVars := by
      intro hc
      have := (hbelow M hM).mem_lt Φ hc
      omega
    rw [show Subst.onTy [(Φ, Ty.fvar W)] M.body = M.body by
      exact Ty.substFvars_eq_self_of_no_key (fun p hp hc => by
        simp only [List.mem_singleton] at hp
        rw [hp] at hc
        exact hΦM hc)]
    have hWM : W ∉ (S₀.onTy M.body).freeVars := by
      exact Subst.not_mem_onTy_freeVars
        (fun p hp hc => hWnorange p hp W hc rfl)
        (by intro hc; have := (hbelow M hM).mem_lt W hc; omega)
    rw [show Subst.onTy [(W, paramTy)] (S₀.onTy M.body) = S₀.onTy M.body by
      exact Ty.substFvars_eq_self_of_no_key (fun p hp hc => by
        simp only [List.mem_singleton] at hp
        rw [hp] at hc
        exact hWM hc)]
  have hctxEq : S₀'.onCtx bodyCtx =
      { S₀.onCtx ctx with env := PolyTy.mkTrivial paramTy :: (S₀.onCtx ctx).env } := by
    cases ctx with
    | mk env ctors =>
      simp only [bodyCtx, Subst.onCtx, Subst.onEnv, List.map_cons, Subst.onPolyTy,
        PolyTy.mkTrivial, hS₀'fvar]
      rw [show List.map S₀'.onPolyTy env = List.map S₀.onPolyTy env by
        simpa [Subst.onEnv] using hS₀'onEnv]
  have hS₀'Kfix : ∀ k ∈ K, S₀'.onTy (Ty.fvar k) = Ty.fvar k := by
    intro k hk
    rw [hS₀'def, Subst.onTy_append, Subst.onTy_append]
    have hΦk : k ≠ Φ := by have hlt := hKΦ k hk; omega
    have hWk : k ≠ W := by have hlt := hKΦ k hk; omega
    rw [show Subst.onTy [(Φ, Ty.fvar W)] (Ty.fvar k) = Ty.fvar k by
      simp [Subst.onTy, Ty.substFvars, Ty.substFvar, hΦk]]
    rw [hKfix k hk]
    rw [show Subst.onTy [(W, paramTy)] (Ty.fvar k) = Ty.fvar k by
      simp [Subst.onTy, Ty.substFvars, Ty.substFvar, hWk]]
  have hS₀'below : ∀ v, v < Φ → S₀'.onTy (Ty.fvar v) = S₀.onTy (Ty.fvar v) := by
    intro v hv
    rw [hS₀'def, Subst.onTy_append, Subst.onTy_append]
    have hΦv : v ≠ Φ := by omega
    have hWv : W ∉ (S₀.onTy (Ty.fvar v)).freeVars := by
      exact Subst.not_mem_onTy_freeVars
        (fun p hp hc => hWnorange p hp W hc rfl)
        (by intro hc; simp [Ty.freeVars] at hc; omega)
    rw [show Subst.onTy [(Φ, Ty.fvar W)] (Ty.fvar v) = Ty.fvar v by
      simp [Subst.onTy, Ty.substFvars, Ty.substFvar, hΦv]]
    rw [show Subst.onTy [(W, paramTy)] (S₀.onTy (Ty.fvar v)) = S₀.onTy (Ty.fvar v) by
      exact Ty.substFvars_eq_self_of_no_key (fun p hp hc => by
        simp only [List.mem_singleton] at hp
        rw [hp] at hc
        exact hWv hc)]
  have hbodyty : TypeOfHM (S₀'.onCtx bodyCtx) body
      ( bodyTy) := by
    simpa [hctxEq] using hbodyty
  have hKΦ' : ∀ k ∈ K, k < Φ + 1 := by intro k hk; have hlt := hKΦ k hk; omega
  obtain ⟨Φ', S, τb, R₁, hInferBody, hAgreeBody, hAgreeTy, hR₁lc, hR₁K, hSK⟩ :=
    @ih (Φ + 1) bodyCtx S₀' ( bodyTy) K
      hbodyCtxWF hbodyCtxBelow hS₀' hKΦ' hbodyK hS₀'Kfix hbodyty
  refine ⟨Φ', S, .arrow (S.onTy (Ty.fvar Φ)) τb, R₁,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact .lambda .none hInferBody
  · intro v hv
    exact Eq.trans (Eq.symm (hS₀'below v hv))
      (hAgreeBody v (by omega))
  · change  (Ty.arrow paramTy bodyTy) =
         (R₁.onTy (.arrow (S.onTy (Ty.fvar Φ)) τb))
    rw [Subst.onTy_arrow]
    have hdom :  (R₁.onTy (S.onTy (Ty.fvar Φ))) =  paramTy := by
      have hΦ := hAgreeBody Φ (by omega)
      calc  (R₁.onTy (S.onTy (Ty.fvar Φ)))
          =  ((S ++ R₁).onTy (Ty.fvar Φ)) := by rw [Subst.onTy_append]
        _ =  (S₀'.onTy (Ty.fvar Φ)) := hΦ.symm
        _ =  paramTy := hS₀'fvar
    rw [hdom]
    have hcod :  (R₁.onTy τb) =  bodyTy := by
      simpa [Eq] using hAgreeTy.symm
    rw [hcod]
  · exact hR₁lc
  · exact hR₁K
  · exact hSK

/-- Producer completeness for an annotated lambda. The pinned parameter type is
    rigid under `K`, so the body IH can reuse the ambient specialization. -/
theorem Infer.complete_lambda_ann_aux {body : Expr} {Φ : Nat} {ctx : Ctx}
    {S₀ : Subst} {T bodyTy : Ty} {K : List Nat}
    (ih : Infer.CompleteAt body)
    (hwf : CtxWF ctx) (hbelow : CtxBelow Φ ctx) (hS₀ : ∀ p ∈ S₀, p.2.IsLC)
    (hTlc : T.IsLC) (hKΦ : ∀ k ∈ K, k < Φ)
    (hTK : ∀ y ∈ T.freeVars, y ∈ K) (hbodyK : ∀ y ∈ body.tyFreeVars, y ∈ K)
    (hKfix : ∀ k ∈ K, S₀.onTy (.fvar k) = .fvar k)
    (hbodyty : TypeOfHM { (S₀.onCtx ctx) with
        env := PolyTy.mkTrivial ( T) :: (S₀.onCtx ctx).env }
        body ( bodyTy)) :
    ∃ Φ' S τ R,
      Infer Φ ctx (.lambda (some T) body) Φ' S τ ∧
      Subst.AgreesBelow Φ S₀ (S ++ R) ∧
      Eq (Ty.arrow T bodyTy) (R.onTy τ) ∧
      (∀ p ∈ R, p.2.IsLC) ∧
      (∀ k ∈ K, R.onTy (.fvar k) = .fvar k) ∧
      (∀ p ∈ S, p.1 ∉ K) := by
  set bodyCtx : Ctx := { ctx with env := PolyTy.mkTrivial T :: ctx.env }
  have hbodyCtxWF : CtxWF bodyCtx := by
    intro M hM
    rcases List.mem_cons.mp hM with rfl | hM
    · exact hTlc
    · exact hwf M hM
  have hbodyCtxBelow : CtxBelow Φ bodyCtx := by
    intro M hM
    rcases List.mem_cons.mp hM with rfl | hM
    · exact Ty.BelowFvars.of_freeVars_lt (fun v hv => hKΦ v (hTK v hv))
    · exact hbelow M hM
  have hS₀T : S₀.onTy T = T := by
    exact Subst.onTy_eq_self_of_fixes (fun v hv => hKfix v (hTK v hv))
  have hctxEq : S₀.onCtx bodyCtx =
      { S₀.onCtx ctx with env := PolyTy.mkTrivial T :: (S₀.onCtx ctx).env } := by
    cases ctx
    simp only [bodyCtx, Subst.onCtx, Subst.onEnv, Subst.onPolyTy, PolyTy.mkTrivial,
      List.map_cons, hS₀T]
  have hbodyty : TypeOfHM (S₀.onCtx bodyCtx) body
      ( bodyTy) := by
    simpa [hctxEq] using hbodyty
  obtain ⟨Φ', S, τb, R₁, hInferBody, hAgreeBody, hAgreeTy, hR₁lc, hR₁K, hSK⟩ :=
    @ih Φ bodyCtx S₀ ( bodyTy) K
      hbodyCtxWF hbodyCtxBelow hS₀ hKΦ hbodyK hKfix hbodyty
  have hST : Eq ((S ++ R₁).onTy T) T := by
    have hbT : Ty.BelowFvars Φ T := Ty.BelowFvars.of_freeVars_lt (fun v hv => hKΦ v (hTK v hv))
    calc  ((S ++ R₁).onTy T)
        =  (S₀.onTy T) := (Subst.onTy_congr hAgreeBody hbT).symm
      _ =  T := hS₀T
  have hdom :  (R₁.onTy (S.onTy T)) =  T := by
    rwa [Subst.onTy_append] at hST
  refine ⟨Φ', S, .arrow (S.onTy T) τb, R₁,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact .lambda (.some T hTlc) hInferBody
  · exact hAgreeBody
  · change  (Ty.arrow T bodyTy) =
         (R₁.onTy (.arrow (S.onTy T) τb))
    rw [Subst.onTy_arrow, hdom]
    have hcod :  (R₁.onTy τb) =  bodyTy := by
      simpa [Eq] using hAgreeTy.symm
    rw [hcod]
  · exact hR₁lc
  · exact hR₁K
  · exact hSK

/-- Producer completeness for lambdas. -/
theorem Infer.complete_lambda {ann : Option Ty} {body : Expr}
    (ih : Infer.CompleteAt body) : Infer.CompleteAt (.lambda ann body) := by
  intro Φ ctx S₀ τ₀ K hwf hbelow hS₀ hKΦ hKtv hKfix hty
  cases ann with
  | none =>
    cases hty with
    | lambda hpc hann heq hbody =>
      rename_i bt pt
      subst heq
      exact complete_lambda_aux (body := body) (Φ := Φ) (ctx := ctx) (S₀ := S₀)
        (paramTy := pt) (bodyTy := bt) (K := K)
        ih hwf hbelow hS₀ hpc hKΦ (fun y hy => hKtv y (by simpa [Expr.tyFreeVars] using hy))
        hKfix hbody
  | some T =>
    cases hty with
    | lambda hpc hann heq hbody =>
      rename_i bt paramTy
      subst heq
      have hparamTy : paramTy = T := hann T rfl
      have hTlc : T.IsLC := by simpa [hparamTy] using hpc
      subst paramTy
      obtain ⟨Φ', S, τ, R, hInfer, hAgree, hAgreeTy, hRlc, hRK, hSK⟩ :=
        complete_lambda_ann_aux (body := body) (Φ := Φ) (ctx := ctx) (S₀ := S₀)
          (T := T) (bodyTy := bt) (K := K)
          ih hwf hbelow hS₀ hTlc hKΦ
          (fun y hy => hKtv y (by simp [Expr.tyFreeVars]; exact Or.inl hy))
          (fun y hy => hKtv y (by simp [Expr.tyFreeVars]; exact Or.inr hy))
          hKfix hbody
      refine ⟨Φ', S, τ, R, hInfer, hAgree, ?_, hRlc, hRK, hSK⟩
      · exact hAgreeTy

/-! ### Application producer completeness -/

/-- Build an erase-level application unifier that realizes the declarative
    argument and result types while preserving the ambient rigid variables. -/
lemma exists_app_unifier {A τa τ₀ argTy : Ty} {Φ₂ : Nat} {R₂ : Subst} {K : List Nat}
    (hP : Eq (Ty.arrow argTy τ₀) (R₂.onTy A))
    (htya : Eq argTy (R₂.onTy τa))
    (hΦ₂A : Φ₂ ∉ A.freeVars) (hΦ₂τa : Φ₂ ∉ τa.freeVars)
    (hR₂ : ∀ p ∈ R₂, p.2.IsLC) (hτ₀LC : τ₀.IsLC)
    (hR₂K : ∀ k ∈ K, R₂.onTy (.fvar k) = .fvar k) (hΦ₂K : ∀ k ∈ K, k < Φ₂) :
    ∃ U, Unifies U A (Ty.arrow τa (Ty.fvar Φ₂)) ∧ (∀ p ∈ U, p.2.IsLC) ∧
      (∀ k ∈ K, U.onTy (.fvar k) = .fvar k) ∧
      U.onTy (Ty.fvar Φ₂) = τ₀ ∧
      (∀ v, v < Φ₂ → U.onTy (.fvar v) = R₂.onTy (.fvar v)) := by
  obtain ⟨W, hWge, hWfresh⟩ := exists_fresh_block
    (R₂.map Prod.fst ++ R₂.flatMap (fun p => p.2.freeVars) ++ argTy.freeVars ++ τ₀.freeVars) Φ₂ 1
  have hWdom : ∀ p ∈ R₂, p.1 ≠ W := by
    intro p hp he
    have := hWfresh p.1 (List.mem_append_left _ (List.mem_append_left _
      (List.mem_append_left _ (List.mem_map.mpr ⟨p, hp, rfl⟩))))
    omega
  have hWrange : ∀ p ∈ R₂, W ∉ p.2.freeVars := by
    intro p hp hc
    have := hWfresh W (List.mem_append_left _ (List.mem_append_left _
      (List.mem_append_right _ (List.mem_flatMap.mpr ⟨p, hp, hc⟩))))
    omega
  have hWargTy : W ∉ argTy.freeVars := fun hc => by
    have := hWfresh W (List.mem_append_left _ (List.mem_append_right _ hc)); omega
  have hWτ₀ : W ∉ τ₀.freeVars := fun hc => by
    have := hWfresh W (List.mem_append_right _ hc); omega
  have hWargTyE : W ∉ ( argTy).freeVars := fun hc =>
    hWargTy (hc)
  have hWτ₀E : W ∉ ( τ₀).freeVars := fun hc =>
    hWτ₀ (hc)
  have hR₂Wfvar : R₂.onTy (Ty.fvar W) = Ty.fvar W := by
    apply Ty.substFvars_eq_self_of_no_key
    intro p hp hc
    simp only [Ty.freeVars, List.mem_singleton] at hc
    exact hWdom p hp hc
  obtain ⟨U, hUdef⟩ : ∃ U : Subst, U = [(Φ₂, Ty.fvar W)] ++ R₂ ++ [(W, τ₀)] := ⟨_, rfl⟩
  have hsingle : ∀ (Z : Nat) (V y : Ty), Subst.onTy [(Z, V)] y = Ty.substFvar Z V y :=
    fun _ _ _ => rfl
  have hsubArrow : ∀ (Z : Nat) (V a b : Ty),
      Ty.substFvar Z V (Ty.arrow a b) = Ty.arrow (Ty.substFvar Z V a) (Ty.substFvar Z V b) :=
    fun _ _ _ _ => rfl
  have hUonTy : ∀ x, U.onTy x = Ty.substFvar W τ₀ (R₂.onTy (Ty.substFvar Φ₂ (Ty.fvar W) x)) := by
    intro x
    rw [hUdef, Subst.onTy_append, Subst.onTy_append, hsingle, hsingle]
  have e1 : Ty.substFvar Φ₂ (Ty.fvar W) (Ty.fvar Φ₂) = Ty.fvar W := by simp [Ty.substFvar]
  have e2 : Ty.substFvar W τ₀ (Ty.fvar W) = τ₀ := by simp [Ty.substFvar]
  have hUniL :  (U.onTy A) = Ty.arrow ( argTy) ( τ₀) := by
    rw [hUonTy, Ty.substFvar_fresh hΦ₂A]
    rw [← hP, hsubArrow, Ty.substFvar_fresh hWargTyE, Ty.substFvar_fresh hWτ₀E]
  have hUniR :  (U.onTy (Ty.arrow τa (Ty.fvar Φ₂))) = Ty.arrow ( argTy) ( τ₀) := by
    rw [hUonTy, hsubArrow, Ty.substFvar_fresh hΦ₂τa, e1, Subst.onTy_arrow, hR₂Wfvar, hsubArrow, e2]
    rw [← htya, Ty.substFvar_fresh hWargTyE]
  refine ⟨U, ?_, ?_, ?_, ?_, ?_⟩
  · show  (U.onTy A) =  (U.onTy (Ty.arrow τa (Ty.fvar Φ₂)))
    rw [hUniL, hUniR]
  · rw [hUdef]
    intro p hp
    rcases List.mem_append.mp hp with hp' | hp'
    · rcases List.mem_append.mp hp' with hp'' | hp''
      · obtain rfl := List.mem_singleton.mp hp''
        exact ContainsBvarsUpTo.fvar
      · exact hR₂ p hp''
    · obtain rfl := List.mem_singleton.mp hp'
      exact hτ₀LC
  · intro k hk
    rw [hUonTy, Ty.substFvar_fresh (show Φ₂ ∉ (Ty.fvar k).freeVars by
        simp only [Ty.freeVars, List.mem_singleton]; have := hΦ₂K k hk; omega), hR₂K k hk]
    exact Ty.substFvar_fresh (show W ∉ (Ty.fvar k).freeVars by
        simp only [Ty.freeVars, List.mem_singleton]; have := hWge; have := hΦ₂K k hk; omega)
  · rw [hUonTy, e1, hR₂Wfvar, e2]
  · intro v hv
    have hWv : W ∉ (Ty.fvar v).freeVars := by
      simp only [Ty.freeVars, List.mem_singleton]
      omega
    have hWR₂v : W ∉ (R₂.onTy (Ty.fvar v)).freeVars :=
      Subst.not_mem_onTy_freeVars hWrange hWv
    rw [hUonTy, Ty.substFvar_fresh (show Φ₂ ∉ (Ty.fvar v).freeVars by
        simp only [Ty.freeVars, List.mem_singleton]; omega), Ty.substFvar_fresh hWR₂v]

/-- Producer completeness for application, factored through the principal
    unifier of the two recursively produced inference derivations. -/
theorem Infer.complete_app_aux {f arg : Expr} {Φ : Nat} {ctx : Ctx} {S₀ : Subst}
    {argTy τ₀ : Ty} {K : List Nat}
    (ihf : Infer.CompleteAt f) (iharg : Infer.CompleteAt arg)
    (hwf : CtxWF ctx) (hbelow : CtxBelow Φ ctx) (hS₀ : ∀ p ∈ S₀, p.2.IsLC)
    (hKΦ : ∀ k ∈ K, k < Φ)
    (hKf : ∀ y ∈ f.tyFreeVars, y ∈ K) (hKa : ∀ y ∈ arg.tyFreeVars, y ∈ K)
    (hKfix : ∀ k ∈ K, S₀.onTy (.fvar k) = .fvar k)
    (hf : TypeOfHM (S₀.onCtx ctx) f (.arrow argTy τ₀))
    (harg : TypeOfHM (S₀.onCtx ctx) arg argTy) :
    ∃ Φ' S τ R,
      Infer Φ ctx (.app f arg) Φ' S τ ∧
      Subst.AgreesBelow Φ S₀ (S ++ R) ∧
      Eq τ₀ (R.onTy τ) ∧
      (∀ p ∈ R, p.2.IsLC) ∧
      (∀ k ∈ K, R.onTy (.fvar k) = .fvar k) ∧
      (∀ p ∈ S, p.1 ∉ K) := by
  obtain ⟨Φ₁, S₁, τf, R₁, hInferF, hAgreeF, hAgreeFty, hR₁lc, hR₁K, hS₁K⟩ :=
    ihf K hwf hbelow hS₀ hKΦ hKf hKfix hf
  have hΦf : ∀ y ∈ f.tyFreeVars, y < Φ := fun y hy => hKΦ y (hKf y hy)
  have hfle : Φ ≤ Φ₁ := Infer.frontier_le hInferF
  have hS₁lc : ∀ p ∈ S₁, p.2.IsLC := (Infer.lc hInferF hwf).2
  have hτf_lc : τf.IsLC := (Infer.lc hInferF hwf).1
  have hτf_bel : Ty.BelowFvars Φ₁ τf := (Infer.belowFvars hInferF hbelow hΦf).1
  have hf_sbel : ∀ p ∈ S₁, Ty.BelowFvars Φ₁ p.2 := (Infer.belowFvars hInferF hbelow hΦf).2
  have hctxWF₁ : CtxWF (S₁.onCtx ctx) := Subst.onCtx_wf hS₁lc hwf
  have hctxBelow₁ : CtxBelow Φ₁ (S₁.onCtx ctx) := Subst.onCtx_below hf_sbel hfle hbelow
  have hKΦ₁ : ∀ k ∈ K, k < Φ₁ := fun k hk => lt_of_lt_of_le (hKΦ k hk) hfle
  have hΦa : ∀ y ∈ arg.tyFreeVars, y < Φ₁ := fun y hy => lt_of_lt_of_le (hKΦ y (hKa y hy)) hfle
  have hctxBridge : (R₁.onCtx (S₁.onCtx ctx)) = (S₀.onCtx ctx) := by
    rw [← Subst.onCtx_append]
    exact (Subst.onCtx_congr hAgreeF hbelow).symm
  have harg' : TypeOfHM (R₁.onCtx (S₁.onCtx ctx)) arg argTy := by
    rwa [← hctxBridge] at harg
  obtain ⟨Φ₂, S₂, τa, R₂, hInferArg, hAgreeArg, hAgreeArgty, hR₂lc, hR₂K, hS₂K⟩ :=
    iharg K hctxWF₁ hctxBelow₁ hR₁lc hKΦ₁ hKa hR₁K harg'
  have hargle : Φ₁ ≤ Φ₂ := Infer.frontier_le hInferArg
  have hKΦ₂ : ∀ k ∈ K, k < Φ₂ := fun k hk => lt_of_lt_of_le (hKΦ₁ k hk) hargle
  have hS₂lc : ∀ p ∈ S₂, p.2.IsLC := (Infer.lc hInferArg hctxWF₁).2
  have hτa_lc : τa.IsLC := (Infer.lc hInferArg hctxWF₁).1
  have hS₂_bel : ∀ p ∈ S₂, Ty.BelowFvars Φ₂ p.2 := (Infer.belowFvars hInferArg hctxBelow₁ hΦa).2
  have hτa_bel : Ty.BelowFvars Φ₂ τa := (Infer.belowFvars hInferArg hctxBelow₁ hΦa).1
  have hτ₀_lc : τ₀.IsLC := by
    have := TypeOfHM.regular hf
    cases this with | arrow _ hret => exact hret
  have hAgreeFty' : Eq (R₁.onTy τf) (R₂.onTy (S₂.onTy τf)) := by
    have h := Subst.onTy_congr hAgreeArg hτf_bel
    simpa [Subst.onTy_append] using h
  have hP : Eq (Ty.arrow argTy τ₀) (R₂.onTy (S₂.onTy τf)) :=
    Eq.trans hAgreeFty hAgreeFty'
  have hτf_bel₂ : Ty.BelowFvars Φ₂ (S₂.onTy τf) := by
    apply Subst.onTy_belowFvars hS₂_bel
    exact hτf_bel.mono hargle
  have hΦ₂A : Φ₂ ∉ (S₂.onTy τf).freeVars := by
    intro hc
    have := Ty.BelowFvars.mem_lt hτf_bel₂ Φ₂ hc
    omega
  have hΦ₂τa : Φ₂ ∉ τa.freeVars := by
    intro hc
    have := Ty.BelowFvars.mem_lt hτa_bel Φ₂ hc
    omega
  obtain ⟨U, hU, hUlc, hUK, hUΦ₂, hUbelow⟩ :=
    exists_app_unifier (A := S₂.onTy τf) hP hAgreeArgty hΦ₂A hΦ₂τa
      hR₂lc hτ₀_lc hR₂K hKΦ₂
  have hAlc : (S₂.onTy τf).IsLC := Subst.onTy_lc hS₂lc hτf_lc
  have hBlc : (Ty.arrow τa (Ty.fvar Φ₂)).IsLC := ContainsBvarsUpTo.arrow hτa_lc ContainsBvarsUpTo.fvar
  obtain ⟨S₃, hS₃uni, hS₃K⟩ := UnifyRel.complete_K hAlc hBlc hUlc hU hUK
  obtain ⟨R₃, hR₃, hR₃lc, hR₃K⟩ := UnifyRel.greatest_K hS₃uni U hUlc hU hUK
  have hAgree₃ : Subst.AgreesBelow Φ₂ R₂ (S₃ ++ R₃) := by
    intro v hv
    rw [Subst.onTy_append]
    have h := hR₃ (Ty.fvar v)
    rwa [hUbelow v hv] at h
  have hAgree₂ : Subst.AgreesBelow Φ₁ R₁ ((S₂ ++ S₃) ++ R₃) :=
    @Subst.AgreesBelow.trans_append Φ₁ Φ₂ R₁ S₂ R₂ S₃ R₃ hargle hAgreeArg hS₂_bel hAgree₃
  have hAgree : Subst.AgreesBelow Φ S₀ ((S₁ ++ (S₂ ++ S₃)) ++ R₃) :=
    @Subst.AgreesBelow.trans_append Φ Φ₁ S₀ S₁ R₁ (S₂ ++ S₃) R₃ hfle hAgreeF hf_sbel hAgree₂
  have hAgreeOut : Eq τ₀ (R₃.onTy (S₃.onTy (.fvar Φ₂))) := by
    have h := hR₃ (Ty.fvar Φ₂)
    rwa [hUΦ₂] at h
  refine ⟨Φ₂ + 1, S₁ ++ S₂ ++ S₃, S₃.onTy (.fvar Φ₂), R₃,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact .app hInferF hInferArg hS₃uni
  · simpa [List.append_assoc] using hAgree
  · exact hAgreeOut
  · exact hR₃lc
  · exact hR₃K
  · intro p hp
    rw [List.mem_append, List.mem_append] at hp
    rcases hp with (hp | hp) | hp
    · exact hS₁K p hp
    · exact hS₂K p hp
    · exact hS₃K p hp

/-- Producer completeness for applications. -/
theorem Infer.complete_app {f arg : Expr}
    (ihf : Infer.CompleteAt f) (iharg : Infer.CompleteAt arg) :
    Infer.CompleteAt (.app f arg) := by
  intro Φ ctx S₀ τ₀ K hwf hbelow hS₀ hKΦ hKtv hKfix hty
  cases hty with
  | app hf harg_ty =>
    rename_i argTy
    have hKf : ∀ y ∈ f.tyFreeVars, y ∈ K := fun y hy =>
      hKtv y (by simpa [Expr.tyFreeVars] using (Or.inl hy))
    have hKa : ∀ y ∈ arg.tyFreeVars, y ∈ K := fun y hy =>
      hKtv y (by simpa [Expr.tyFreeVars] using (Or.inr hy))
    exact Infer.complete_app_aux ihf iharg hwf hbelow hS₀ hKΦ hKf hKa hKfix hf harg_ty

/-! ### Let producer completeness -/

/-- The generalisation bridge shared by relational and executable
    unannotated-let completeness. An inferred RHS result which factors a
    declarative opening yields a generalized scheme at least as general as the
    declarative binder scheme. -/
private theorem genScheme_generalizes_of_agrees
    {Φ : Nat} {ctx : Ctx} {S₀ S₁ R₁ : Subst} {rhs : Expr}
    {M : PolyTy} {K Xs : List Nat} {τ₁ : Ty}
    (hbelow : CtxBelow Φ ctx)
    (hKrhs : ∀ y ∈ rhs.tyFreeVars, y ∈ K)
    (hMwf : M.WF) (hXlen : Xs.length = M.paramCount) (hXnodup : Xs.Nodup)
    (hXMbody : ∀ x ∈ Xs, x ∉ M.body.freeVars)
    (hXK : ∀ x ∈ Xs, x ∉ K)
    (hXS₀ran : ∀ x ∈ Xs, x ∉ S₀.flatMap (fun p => p.2.freeVars))
    (hXrange : ∀ x ∈ Xs, x ∉ List.range Φ)
    (hτ₁_lc : τ₁.IsLC) (hR₁lc : ∀ p ∈ R₁, p.2.IsLC)
    (hR₁K : ∀ k ∈ K, R₁.onTy (.fvar k) = .fvar k)
    (hAgreeRhs : Subst.AgreesBelow Φ S₀ (S₁ ++ R₁))
    (hAgreeRhsTy : Eq (M.openVars Xs) (R₁.onTy τ₁)) :
    (
      (R₁.onPolyTy (genScheme rhs.tyFreeVars (S₁.onCtx ctx).env τ₁))).Generalizes
      ( M) := by
  set rigid := rhs.tyFreeVars with hrigid_def
  set env₁ := (S₁.onCtx ctx).env with henv₁_def
  set genV := genVars rigid env₁ τ₁ with hgenV_def
  have htyr : Ty.openVars Xs M.body = R₁.onTy τ₁ := hAgreeRhsTy
  have hXM'' : ∀ x ∈ Xs,
      x ∉ (R₁.onPolyTy ⟨genV.length, Ty.closeOver genV τ₁⟩).body.freeVars := by
    intro x hx hcx
    rw [Subst.onPolyTy] at hcx
    rw [Ty.mem_freeVars_onTy_iff] at hcx
    obtain ⟨v, hv, hxv⟩ := hcx
    have hvτ : v ∈ τ₁.freeVars := Ty.closeOver_freeVars_subset hv
    have hvnotg : v ∉ genV := fun hg => Ty.not_mem_closeOver_freeVars hg hv
    have hvenv : v ∈ env₁.freeVars ∨ v ∈ rigid := by
      by_cases h₁ : v ∈ env₁.freeVars
      · exact Or.inl h₁
      · by_cases h₂ : v ∈ rigid
        · exact Or.inr h₂
        · exfalso
          exact hvnotg (by
            rw [hgenV_def, genVars]
            apply List.mem_filter.mpr
            exact ⟨hvτ, by
              simp only [Bool.and_eq_true]
              exact ⟨by simpa using h₁, by simpa using h₂⟩⟩)
    rcases hvenv with hvenv | hrigid
    · have hvenv₁ : v ∈ (S₁.onCtx ctx).env.freeVars := by
        simpa [env₁] using hvenv
      rw [Env.mem_freeVars_iff] at hvenv₁
      simp only [Subst.onCtx, Subst.onEnv, List.mem_map] at hvenv₁
      obtain ⟨σ, hσ, vσ⟩ := hvenv₁
      obtain ⟨M₀, hM₀, rfl⟩ := hσ
      rw [Subst.onPolyTy] at vσ
      rw [Subst.onTy, Ty.mem_freeVars_substFvars_image] at vσ
      obtain ⟨w, hw, vw⟩ := vσ
      have hwlt : w < Φ := (hbelow M₀ hM₀).mem_lt w hw
      have hxS₁R₁ : x ∈ ((S₁ ++ R₁).onTy (Ty.fvar w)).freeVars := by
        rw [Subst.onTy_append]
        exact Ty.mem_freeVars_onTy_iff.mpr ⟨v, vw, hxv⟩
      have hxS₀ : x ∈ (S₀.onTy (Ty.fvar w)).freeVars := by
        rw [hAgreeRhs w hwlt]
        exact hxS₁R₁
      rcases Subst.mem_freeVars_onTy hxS₀ with hxw | ⟨p, hp, hxp⟩
      · simp only [Ty.freeVars, List.mem_singleton] at hxw
        exact hXrange x hx (List.mem_range.mpr (hxw ▸ hwlt))
      · exact hXS₀ran x hx (List.mem_flatMap.mpr ⟨p, hp, hxp⟩)
    · have hvK : v ∈ K := hKrhs v hrigid
      rw [hR₁K v hvK] at hxv
      simp only [Ty.freeVars, List.mem_singleton] at hxv
      exact hXK x hx (hxv ▸ hvK)
  have hg' : (R₁.onPolyTy ⟨genV.length, Ty.closeOver genV τ₁⟩).Generalizes M :=
    closeOver_generalizes (g := genV) (τ₁ := τ₁) (R := R₁)
      (M := M) (Xs := Xs) hτ₁_lc hR₁lc hMwf hXnodup hXlen hXMbody htyr hXM''
  simpa [genScheme, hgenV_def] using hg'

/-- Producer completeness for an unannotated let. The rhs's inferred scheme is
    at least as general as the declarative witness used to type the body. -/
theorem Infer.complete_letIn_aux {Φ : Nat} {ctx : Ctx} {S₀ : Subst}
    {rhs body : Expr} {M : PolyTy} {L : List Nat} {τ₀ : Ty} {K : List Nat}
    (iha : Infer.CompleteAt rhs) (ihb : Infer.CompleteAt body)
    (hwf : CtxWF ctx) (hbelow : CtxBelow Φ ctx) (hS₀ : ∀ p ∈ S₀, p.2.IsLC)
    (hKΦ : ∀ k ∈ K, k < Φ) (hKrhs : ∀ y ∈ rhs.tyFreeVars, y ∈ K)
    (hKbody : ∀ y ∈ body.tyFreeVars, y ∈ K)
    (hKfix : ∀ k ∈ K, S₀.onTy (.fvar k) = .fvar k)
    (hMwf : M.WF)
    (hcofin : ∀ Xs : List Nat, FreshNames L M.paramCount Xs →
      TypeOfHM (S₀.onCtx ctx) rhs (M.openVars Xs))
    (hbody : TypeOfHM
        ({ (S₀.onCtx ctx) with env := M :: (S₀.onCtx ctx).env })
        body τ₀) :
    ∃ Φ' S τ R,
      Infer Φ ctx (.letIn none rhs body) Φ' S τ ∧
      Subst.AgreesBelow Φ S₀ (S ++ R) ∧
      Eq τ₀ (R.onTy τ) ∧
      (∀ p ∈ R, p.2.IsLC) ∧
      (∀ k ∈ K, R.onTy (.fvar k) = .fvar k) ∧
      (∀ p ∈ S, p.1 ∉ K) := by
  obtain ⟨Xs, hXlen, hXnodup, hXavoid⟩ := exists_fresh_names
    (L ++ M.body.freeVars ++ K ++ (S₀.map Prod.fst ++ S₀.flatMap (fun p => p.2.freeVars)) ++ List.range Φ)
    M.paramCount
  have hXfresh : FreshNames L M.paramCount Xs := ⟨hXlen, hXnodup, fun x hx hc =>
    hXavoid x hx (by simp only [List.mem_append]; tauto)⟩
  have hXMbody : ∀ x ∈ Xs, x ∉ M.body.freeVars := fun x hx hc =>
    hXavoid x hx (by simp only [List.mem_append]; tauto)
  have hXK : ∀ x ∈ Xs, x ∉ K := fun x hx hc =>
    hXavoid x hx (by simp only [List.mem_append]; tauto)
  have hXS₀ran : ∀ x ∈ Xs, x ∉ S₀.flatMap (fun p => p.2.freeVars) := fun x hx hc =>
    hXavoid x hx (by simp only [List.mem_append]; tauto)
  have hXrange : ∀ x ∈ Xs, x ∉ List.range Φ := fun x hx hc =>
    hXavoid x hx (by simp only [List.mem_append]; tauto)
  obtain ⟨Φ₁, S₁, τ₁, R₁, hInferRhs, hAgreeRhs, hAgreeRhsTy, hR₁lc, hR₁K, hS₁K⟩ :=
    iha K hwf hbelow hS₀ hKΦ hKrhs hKfix (hcofin Xs hXfresh)
  have hΦrhs : ∀ y ∈ rhs.tyFreeVars, y < Φ := fun y hy => hKΦ y (hKrhs y hy)
  have hfle : Φ ≤ Φ₁ := Infer.frontier_le hInferRhs
  obtain ⟨hτ₁_lc, hS₁lc⟩ := Infer.lc hInferRhs hwf
  obtain ⟨hτ₁_bel, hS₁_bel⟩ := Infer.belowFvars hInferRhs hbelow hΦrhs
  have hctxWF₁ : CtxWF (S₁.onCtx ctx) := Subst.onCtx_wf hS₁lc hwf
  have hctxBelow₁ : CtxBelow Φ₁ (S₁.onCtx ctx) := Subst.onCtx_below hS₁_bel hfle hbelow
  have hKΦ₁ : ∀ k ∈ K, k < Φ₁ := fun k hk => lt_of_lt_of_le (hKΦ k hk) hfle
  have hctxBridge : (R₁.onCtx (S₁.onCtx ctx)) = (S₀.onCtx ctx) := by
    rw [← Subst.onCtx_append]
    exact (Subst.onCtx_congr hAgreeRhs hbelow).symm
  have hgen : ( (R₁.onPolyTy (genScheme rhs.tyFreeVars (S₁.onCtx ctx).env τ₁))).Generalizes ( M) := by
    exact genScheme_generalizes_of_agrees hbelow hKrhs hMwf hXlen hXnodup
      hXMbody hXK hXS₀ran hXrange hτ₁_lc hR₁lc hR₁K hAgreeRhs hAgreeRhsTy
  have hbody_bridge : TypeOfHM
      ({ (R₁.onCtx (S₁.onCtx ctx)) with
          env :=  M :: (R₁.onCtx (S₁.onCtx ctx)).env })
      body τ₀ := by
    rw [hctxBridge]
    simpa [  Subst.onCtx, Subst.onEnv] using hbody
  have hbody_alg : TypeOfHM
      ({ (R₁.onCtx (S₁.onCtx ctx)) with
          env :=  (R₁.onPolyTy (genScheme rhs.tyFreeVars (S₁.onCtx ctx).env τ₁))
            :: (R₁.onCtx (S₁.onCtx ctx)).env })
      body τ₀ := by
    refine TypeOfHM.weaken_scheme
      (env_post := [])
      (env := (R₁.onCtx (S₁.onCtx ctx)).env)
      (M :=  M)
      (M' :=  (R₁.onPolyTy (genScheme rhs.tyFreeVars (S₁.onCtx ctx).env τ₁)))
      hgen hbody_bridge
  have hctxWF₁' : CtxWF { (S₁.onCtx ctx) with
      env := genScheme rhs.tyFreeVars (S₁.onCtx ctx).env τ₁ :: (S₁.onCtx ctx).env } := by
    intro M hM; rcases List.mem_cons.mp hM with rfl | hM
    · exact genScheme_wf hτ₁_lc
    · exact hctxWF₁ M hM
  have hctxBelow₁' : CtxBelow Φ₁ { (S₁.onCtx ctx) with
      env := genScheme rhs.tyFreeVars (S₁.onCtx ctx).env τ₁ :: (S₁.onCtx ctx).env } := by
    intro M hM; rcases List.mem_cons.mp hM with rfl | hM
    · exact hτ₁_bel.closeOver
    · exact hctxBelow₁ M hM
  obtain ⟨Φ₂, S₂, τ₂, R₂, hInferBody, hAgreeBody, hAgreeTyBody, hR₂lc, hR₂K, hS₂K⟩ :=
    ihb K hctxWF₁' hctxBelow₁' hR₁lc hKΦ₁ hKbody hR₁K hbody_alg
  refine ⟨Φ₂, S₁ ++ S₂, τ₂, R₂, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact .letIn hInferRhs hInferBody
  · simpa [List.append_assoc] using
      (@Subst.AgreesBelow.trans_append Φ Φ₁ S₀ S₁ R₁ S₂ R₂ hfle hAgreeRhs hS₁_bel hAgreeBody)
  · exact hAgreeTyBody
  · exact hR₂lc
  · exact hR₂K
  · intro p hp
    rw [List.mem_append] at hp
    rcases hp with hp | hp
    · exact hS₁K p hp
    · exact hS₂K p hp

/-- Producer completeness for an annotated let in D2's skolem-first order. -/
theorem Infer.complete_letIn_ann_aux {Φ : Nat} {ctx : Ctx} {S₀ : Subst}
    {rhs body : Expr} {σ : PolyTy} {L : List Nat} {τ₀ : Ty} {K : List Nat}
    (iha : ∀ Ys, Infer.CompleteAt (rhs.openTyVars Ys)) (ihb : Infer.CompleteAt body)
    (hwf : CtxWF ctx) (hbelow : CtxBelow Φ ctx) (hS₀ : ∀ p ∈ S₀, p.2.IsLC)
    (hKΦ : ∀ k ∈ K, k < Φ)
    (hKrhs : ∀ y ∈ rhs.tyFreeVars, y ∈ K) (hKbody : ∀ y ∈ body.tyFreeVars, y ∈ K)
    (hKσ : ∀ y ∈ σ.body.freeVars, y ∈ K)
    (hKfix : ∀ k ∈ K, S₀.onTy (.fvar k) = .fvar k)
    (hσwf : σ.WF)
    -- The source premise is checked directly at the annotation pin.
    (hcofin : ∀ Xs : List Nat, FreshNames L σ.paramCount Xs →
      TypeOfHM (S₀.onCtx ctx) (rhs.openTyVars Xs)
        ( (σ.openVars Xs)))
    (hbody : TypeOfHM
        ({ (S₀.onCtx ctx) with env := σ :: (S₀.onCtx ctx).env })
        body τ₀) :
    ∃ Φ' S τ R,
      Infer Φ ctx (.letIn (some σ) rhs body) Φ' S τ ∧
      Subst.AgreesBelow Φ S₀ (S ++ R) ∧
      Eq τ₀ (R.onTy τ) ∧
      (∀ p ∈ R, p.2.IsLC) ∧
      (∀ k ∈ K, R.onTy (.fvar k) = .fvar k) ∧
      (∀ p ∈ S, p.1 ∉ K) := by
  obtain ⟨N, hNge, hNavoid⟩ := exists_fresh_block
    (ctx.env.freeVars ++ S₀.map Prod.fst ++ S₀.flatMap (fun p => p.2.freeVars) ++ L)
    Φ σ.paramCount
  set Ys : List Nat := freshVars N σ.paramCount with hYs_def
  have hfresh_avoid : ∀ v ∈ ctx.env.freeVars ++ S₀.map Prod.fst ++
      S₀.flatMap (fun p => p.2.freeVars) ++ L, v ∉ Ys := by
    intro v hv hc
    have hvlt : v < N := hNavoid v hv
    have hNle : N ≤ v := freshVars_ge v (by simpa [Ys] using hc)
    omega
  have hYL : ∀ y ∈ Ys, y ∉ L := fun y hy hmemL =>
    hfresh_avoid y (by
      simpa [List.append_assoc] using
        (List.mem_append_right (ctx.env.freeVars ++ S₀.map Prod.fst ++
          S₀.flatMap (fun p => p.2.freeVars)) hmemL)) hy
  have hYdom₀ : ∀ y ∈ Ys, y ∉ S₀.map Prod.fst := fun y hy hmem =>
    hfresh_avoid y (by
      simpa [List.append_assoc] using
        (List.mem_append_right (ctx.env.freeVars)
          (List.mem_append_left (S₀.flatMap (fun p => p.2.freeVars) ++ L) hmem))) hy
  have hYran₀ : ∀ y ∈ Ys, y ∉ S₀.flatMap (fun p => p.2.freeVars) := fun y hy hmem =>
    hfresh_avoid y (by
      simpa [List.append_assoc] using
        (List.mem_append_right (ctx.env.freeVars)
          (List.mem_append_right (S₀.map Prod.fst)
            (List.mem_append_left L hmem)))) hy
  have hYenvctx : ∀ y ∈ Ys, y ∉ ctx.env.freeVars := fun y hy hmem =>
    hfresh_avoid y (by
      simpa [List.append_assoc] using
        (List.mem_append_left (S₀.map Prod.fst ++ S₀.flatMap (fun p => p.2.freeVars) ++ L) hmem)) hy
  have hYenv₀ : ∀ y ∈ Ys, y ∉ (S₀.onCtx ctx).env.freeVars := by
    intro y hy hc
    rw [Env.mem_freeVars_iff] at hc
    obtain ⟨M, hM, hyM⟩ := hc
    have hMmap : M ∈ ctx.env.map S₀.onPolyTy := by simpa [Subst.onCtx, Subst.onEnv] using hM
    obtain ⟨M₀, hM₀, rfl⟩ := List.mem_map.mp hMmap
    rcases Subst.mem_freeVars_onTy hyM with h | h
    · exact hYenvctx y hy (Env.mem_freeVars_iff.mpr ⟨M₀, hM₀, h⟩)
    · obtain ⟨p, hp, hyp⟩ := h
      exact hYran₀ y hy (List.mem_flatMap.mpr ⟨p, hp, hyp⟩)
  have hKfixN : ∀ k ∈ K ++ Ys, S₀.onTy (.fvar k) = .fvar k := by
    intro k hk
    rcases List.mem_append.mp hk with hk | hk
    · exact hKfix k hk
    · rw [Subst.onTy]
      apply Ty.substFvars_eq_self_of_no_key
      intro p hp hc
      have hpk : p.1 = k := by simpa [Ty.freeVars] using hc
      exact hYdom₀ k hk (List.mem_map.mpr ⟨p, hp, hpk⟩)
  have hKΦN : ∀ k ∈ K ++ Ys, k < N + σ.paramCount := by
    intro k hk
    rcases List.mem_append.mp hk with hk | hk
    · exact lt_of_lt_of_le (hKΦ k hk) (by omega)
    · have := freshVars_lt k hk
      omega
  have hKrhsOpen : ∀ y ∈ (rhs.openTyVars Ys).tyFreeVars, y ∈ K ++ Ys := by
    intro y hy
    rcases Expr.tyFreeVars_openTyVars hy with h | h
    · exact List.mem_append_left _ (hKrhs y h)
    · exact List.mem_append_right _ h
  have hbelowN : CtxBelow (N + σ.paramCount) ctx := fun M hM => (hbelow M hM).mono (by omega)
  have hYfresh : FreshNames L σ.paramCount Ys := by
    refine ⟨?_, ?_, ?_⟩
    · simp [Ys]
    · simpa [Ys] using freshVars_nodup
    · exact fun y hy hc => hYL y hy hc
  have htyrhs : TypeOfHM (S₀.onCtx ctx) (rhs.openTyVars Ys)
      ( (σ.openVars Ys)) := hcofin Ys hYfresh
  obtain ⟨Φ₁, S₁, τ₁, R₁, hInferRhs, hAgreeRhs, hAgreeRhsTy, hR₁lc, hR₁K, hS₁K⟩ :=
    iha Ys (K ++ Ys) hwf hbelowN hS₀ hKΦN hKrhsOpen hKfixN htyrhs
  have hfle : N + σ.paramCount ≤ Φ₁ := Infer.frontier_le hInferRhs
  have hKΦ₁ : ∀ k ∈ K, k < Φ₁ := fun k hk => lt_of_lt_of_le (hKΦ k hk) (by omega)
  have hΦrhs : ∀ y ∈ (rhs.openTyVars Ys).tyFreeVars, y < N + σ.paramCount :=
    fun y hy => hKΦN y (hKrhsOpen y hy)
  obtain ⟨hτ₁_lc, hS₁lc⟩ := Infer.lc hInferRhs hwf
  obtain ⟨hτ₁_bel, hS₁_bel⟩ := Infer.belowFvars hInferRhs hbelowN hΦrhs
  have hσbody : Ty.BelowFvars Φ σ.body :=
    Ty.BelowFvars.of_freeVars_lt (fun v hv => hKΦ v (hKσ v hv))
  have hσbody₁ : Ty.BelowFvars Φ₁ σ.body := hσbody.mono (by omega)
  have hσopen : Ty.BelowFvars Φ₁ (σ.openVars Ys) :=
    Ty.openVars_belowFvars hσbody₁ (fun x hx => by
      have := freshVars_lt x (by simpa [Ys] using hx)
      omega)
  have hσopen_lc : (σ.openVars Ys).IsLC := PolyTy.openVars_isLC hσwf (by simp [Ys])
  have hR₁σopen : R₁.onTy (σ.openVars Ys) = σ.openVars Ys := by
    refine Subst.onTy_eq_self_of_fixes (fun v hv => ?_)
    rcases Ty.freeVars_openVars_subset v hv with h | h
    · exact hR₁K v (List.mem_append_left _ (hKσ v h))
    · exact hR₁K v (List.mem_append_right _ h)
  have hUnifiesR₁ : Unifies R₁ τ₁ (σ.openVars Ys) := by
    unfold Unifies
    rw [hR₁σopen]
    exact Eq.symm hAgreeRhsTy
  obtain ⟨Schk, hSchk, hSchkK⟩ := UnifyRel.complete_K hτ₁_lc hσopen_lc hR₁lc hUnifiesR₁ hR₁K
  obtain ⟨V, hV, hVlc, hVK⟩ := UnifyRel.greatest_K hSchk R₁ hR₁lc hUnifiesR₁ hR₁K
  have hesc1 : ∀ y ∈ Ys, y ∉ (S₁ ++ Schk).map Prod.fst := by
    intro y hy hc
    rcases List.mem_map.mp hc with ⟨p, hp, hp1⟩
    rw [List.mem_append] at hp
    rcases hp with hp | hp
    · exact hS₁K p hp (List.mem_append_right _ (hp1 ▸ hy))
    · exact hSchkK p hp (List.mem_append_right _ (hp1 ▸ hy))
  have hesc2 : ∀ y ∈ Ys, y ∉ (Schk.onCtx (S₁.onCtx ctx)).env.freeVars := by
    intro y hy hc
    rw [Env.mem_freeVars_iff] at hc
    obtain ⟨M', hM', hyM'⟩ := hc
    have hM'map : M' ∈ ((S₁.onCtx ctx).env.map Schk.onPolyTy) := by
      simpa [Subst.onCtx, Subst.onEnv] using hM'
    obtain ⟨M, hM, rfl⟩ := List.mem_map.mp hM'map
    have hM'' : M ∈ ctx.env.map S₁.onPolyTy := by
      simpa [Subst.onCtx, Subst.onEnv] using hM
    obtain ⟨M₀, hM₀, rfl⟩ := List.mem_map.mp hM''
    have hyV : y ∈ (V.onTy (Schk.onTy (S₁.onTy M₀.body))).freeVars := by
      apply Ty.mem_freeVars_onTy_iff.mpr
      refine ⟨y, hyM', ?_⟩
      have hVy : V.onTy (.fvar y) = .fvar y := hVK y (List.mem_append_right _ (by simpa [Ys] using hy))
      rw [hVy]
      simp [Ty.freeVars]
    have hAgree_M :  (R₁.onTy (S₁.onTy M₀.body)) =
         (V.onTy (Schk.onTy (S₁.onTy M₀.body))) := hV (S₁.onTy M₀.body)
    have hyR : y ∈ (R₁.onTy (S₁.onTy M₀.body)).freeVars := by
      rwa [hAgree_M]
    have hbelowM₀ : Ty.BelowFvars (N + σ.paramCount) M₀.body := (hbelow M₀ hM₀).mono (by omega)
    have hAgree_M0 : Eq (S₀.onTy M₀.body) (R₁.onTy (S₁.onTy M₀.body)) := by
      simpa [Subst.onTy_append] using Subst.onTy_congr hAgreeRhs hbelowM₀
    have hyS₀ : y ∈ (S₀.onTy M₀.body).freeVars := by
      rwa [hAgree_M0]
    have hyS₀env : y ∈ (S₀.onCtx ctx).env.freeVars :=
      Env.mem_freeVars_iff.mpr ⟨S₀.onPolyTy M₀, by
        simpa [Subst.onCtx, Subst.onEnv] using (List.mem_map.mpr ⟨M₀, hM₀, rfl⟩), hyS₀⟩
    exact hYenv₀ y (by simpa [Ys] using hy) hyS₀env
  have hAgreeRhs' : ∀ v, v < N + σ.paramCount →
      Eq (S₀.onTy (.fvar v)) (R₁.onTy (S₁.onTy (.fvar v))) := by
    intro v hv
    simpa [Subst.onTy_append] using hAgreeRhs v hv
  have hAgreeV : Subst.AgreesBelow (N + σ.paramCount) S₀ ((S₁ ++ Schk) ++ V) := by
    intro v hv
    rw [Subst.onTy_append, Subst.onTy_append]
    exact Eq.trans (hAgreeRhs' v hv) (hV (S₁.onTy (.fvar v)))
  have hAgreeΦ : Subst.AgreesBelow Φ S₀ ((S₁ ++ Schk) ++ V) := fun v hv => hAgreeV v (by omega)
  have hSchk_bel : ∀ p ∈ Schk, Ty.BelowFvars Φ₁ p.2 := UnifyRel.belowFvars hSchk hτ₁_bel hσopen
  have hSchk_lc : ∀ p ∈ Schk, p.2.IsLC := UnifyRel.lc hSchk hτ₁_lc hσopen_lc
  have hS₁_bel_all : ∀ p ∈ S₁ ++ Schk, Ty.BelowFvars Φ₁ p.2 := by
    intro p hp
    rcases List.mem_append.mp hp with hp | hp
    · exact hS₁_bel p hp
    · exact hSchk_bel p hp
  have hctxWF₁ : CtxWF (S₁.onCtx ctx) := Subst.onCtx_wf hS₁lc hwf
  have hctxBelow₁ : CtxBelow Φ₁ (S₁.onCtx ctx) := Subst.onCtx_below hS₁_bel hfle hbelowN
  set bodyCtx_alg : Ctx := { (Schk.onCtx (S₁.onCtx ctx)) with
      env := σ :: (Schk.onCtx (S₁.onCtx ctx)).env } with hbodyCtx_def
  have hctxWF₁' : CtxWF bodyCtx_alg := by
    intro M hM; rcases List.mem_cons.mp hM with rfl | hM
    · exact hσwf
    · exact (Subst.onCtx_wf hSchk_lc hctxWF₁) M hM
  have hctxBelow₁' : CtxBelow Φ₁ bodyCtx_alg := by
    intro M hM; rcases List.mem_cons.mp hM with rfl | hM
    · exact hσbody₁
    · exact (Subst.onCtx_below hSchk_bel (le_refl _) hctxBelow₁) M hM
  have hAgreeV' : Subst.AgreesBelow (N + σ.paramCount) S₀ (S₁ ++ Schk ++ V) := by
    simpa [List.append_assoc] using hAgreeV
  have hctx_tail : (V.onCtx (Schk.onCtx (S₁.onCtx ctx))) = (S₀.onCtx ctx) := by
    rw [← Subst.onCtx_append, ← Subst.onCtx_append]
    simpa [List.append_assoc] using (Subst.onCtx_congr hAgreeV' hbelowN).symm
  have hσbodyV : V.onTy σ.body = σ.body := by
    refine Subst.onTy_eq_self_of_fixes (fun v hv => ?_)
    exact hVK v (List.mem_append_left _ (hKσ v hv))
  have hhead :  (V.onPolyTy σ) =  σ := by
    simp [Subst.onPolyTy,  hσbodyV]
  have hbodyctx :
      (V.onCtx bodyCtx_alg)
      = { (V.onCtx (Schk.onCtx (S₁.onCtx ctx))) with
          env :=  (V.onPolyTy σ)
            :: (V.onCtx (Schk.onCtx (S₁.onCtx ctx))).env } := by
    rw [hbodyCtx_def]
    simp only [  Subst.onCtx, Subst.onEnv,
      List.map_cons]
  have hbody_alg : TypeOfHM (V.onCtx bodyCtx_alg) body τ₀ := by
    rw [hbodyctx, hctx_tail, hhead]
    exact hbody
  obtain ⟨Φ₂, S₂, τ₂, R₂, hInferBody, hAgreeBody, hAgreeTyBody, hR₂lc, hR₂K, hS₂K⟩ :=
    ihb K hctxWF₁' hctxBelow₁' hVlc hKΦ₁ hKbody (fun k hk => hVK k (List.mem_append_left _ hk)) hbody_alg
  have hAgree : Subst.AgreesBelow Φ S₀ (((S₁ ++ Schk) ++ S₂) ++ R₂) :=
    @Subst.AgreesBelow.trans_append Φ Φ₁ S₀ (S₁ ++ Schk) V S₂ R₂
      (by omega) hAgreeΦ hS₁_bel_all hAgreeBody
  refine ⟨Φ₂, S₁ ++ Schk ++ S₂, τ₂, R₂, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [hYs_def, hbodyCtx_def] using
      (@Infer.letInAnn Φ N ctx σ rhs body Φ₁ Φ₂ S₁ Schk S₂ τ₁ τ₂
        hσwf (by omega) hInferRhs hSchk hesc1 hesc2 hInferBody)
  · simpa [List.append_assoc] using hAgree
  · exact hAgreeTyBody
  · exact hR₂lc
  · exact hR₂K
  · intro p hp
    rw [List.mem_append, List.mem_append] at hp
    rcases hp with (hp | hp) | hp
    · intro hc; exact hS₁K p hp (List.mem_append_left _ hc)
    · intro hc; exact hSchkK p hp (List.mem_append_left _ hc)
    · exact hS₂K p hp

/-- Producer completeness for annotated and unannotated lets. -/
theorem Infer.complete_letIn {ann : Option PolyTy} {rhs body : Expr}
    (iha : Infer.CompleteAt rhs)
    (ihao : ∀ Ys, Infer.CompleteAt (rhs.openTyVars Ys))
    (ihb : Infer.CompleteAt body) :
    Infer.CompleteAt (.letIn ann rhs body) := by
  intro Φ ctx S₀ τ₀ K hwf hbelow hS₀ hKΦ hKtv hKfix hty
  cases hty with
  | letIn hMwf hann hcofin hbodyCtx_eq hbody =>
    rename_i bodyCtx M L
    rw [hbodyCtx_eq] at hbody
    cases ann with
    | none =>
      have hKrhs : ∀ y ∈ rhs.tyFreeVars, y ∈ K := fun y hy =>
        hKtv y (by
          simpa [Expr.tyFreeVars, Option.elim_none] using (List.mem_append.mpr (Or.inl hy)))
      have hKbody : ∀ y ∈ body.tyFreeVars, y ∈ K := fun y hy =>
        hKtv y (by
          simpa [Expr.tyFreeVars, Option.elim_none] using (List.mem_append.mpr (Or.inr hy)))
      have hcofin' : ∀ Xs : List Nat, FreshNames L M.paramCount Xs →
          TypeOfHM (S₀.onCtx ctx) rhs (M.openVars Xs) := by
        intro Xs hf
        simpa [Expr.openBoundTyVars] using hcofin Xs hf
      obtain ⟨Φ', S, τ, R, hInfer, hAgree, hAgreeTy, hRlc, hRK, hSK⟩ :=
        Infer.complete_letIn_aux iha ihb hwf hbelow hS₀ hKΦ hKrhs hKbody hKfix hMwf hcofin' hbody
      refine ⟨Φ', S, τ, R, hInfer, hAgree, ?_, hRlc, hRK, hSK⟩
      exact hAgreeTy
    | some σ =>
      have hMσ : M = σ := hann σ rfl
      subst M
      have hKrhs : ∀ y ∈ rhs.tyFreeVars, y ∈ K := fun y hy =>
        hKtv y (by
          simpa [Expr.tyFreeVars, Option.elim_some] using
            (List.mem_append_left (body.tyFreeVars) (List.mem_append_right (σ.body.freeVars) hy)))
      have hKbody : ∀ y ∈ body.tyFreeVars, y ∈ K := fun y hy =>
        hKtv y (by
          simpa [Expr.tyFreeVars, Option.elim_some] using
            (List.mem_append_right (σ.body.freeVars ++ rhs.tyFreeVars) hy))
      have hKσ : ∀ y ∈ σ.body.freeVars, y ∈ K := fun y hy =>
        hKtv y (by
          simpa [Expr.tyFreeVars, Option.elim_some] using
            (List.mem_append_left (body.tyFreeVars) (List.mem_append_left (rhs.tyFreeVars) hy)))
      have hσwf : σ.WF := hMwf
      have hcofin_aux : ∀ Xs : List Nat, FreshNames L σ.paramCount Xs →
          TypeOfHM (S₀.onCtx ctx) (rhs.openTyVars Xs)
            ( (σ.openVars Xs)) := by
        intro Xs hf
        simpa [Expr.openBoundTyVars] using hcofin Xs hf
      exact Infer.complete_letIn_ann_aux ihao ihb hwf hbelow hS₀ hKΦ hKrhs hKbody hKσ hKfix hσwf hcofin_aux hbody

/-! ### Match producer completeness -/

/-- Extend a residual at the match rule's fresh running-result variable while
    preserving its action below the old frontier. -/
lemma exists_residual_at_fresh {τ₀ : Ty} {Φ : Nat} {R : Subst} {K : List Nat}
    (hR : ∀ p ∈ R, p.2.IsLC) (hτ₀LC : τ₀.IsLC)
    (hRK : ∀ k ∈ K, R.onTy (.fvar k) = .fvar k) (hΦK : ∀ k ∈ K, k < Φ) :
    ∃ R' : Subst, (∀ p ∈ R', p.2.IsLC) ∧
      (∀ k ∈ K, R'.onTy (Ty.fvar k) = Ty.fvar k) ∧
      R'.onTy (Ty.fvar Φ) = τ₀ ∧
      (∀ v, v < Φ → R'.onTy (Ty.fvar v) = R.onTy (Ty.fvar v)) := by
  obtain ⟨W, hWge, hWfresh⟩ := exists_fresh_block
    (R.map Prod.fst ++ R.flatMap (fun p => p.2.freeVars)) Φ 1
  have hWdom : ∀ p ∈ R, p.1 ≠ W := by
    intro p hp he
    have := hWfresh p.1 (List.mem_append_left _
      (List.mem_map.mpr ⟨p, hp, rfl⟩))
    omega
  have hWrange : ∀ p ∈ R, W ∉ p.2.freeVars := by
    intro p hp hc
    have := hWfresh W (List.mem_append_right _
      (List.mem_flatMap.mpr ⟨p, hp, hc⟩))
    omega
  have hRWfvar : R.onTy (Ty.fvar W) = Ty.fvar W := by
    apply Ty.substFvars_eq_self_of_no_key
    intro p hp hc
    simp only [Ty.freeVars, List.mem_singleton] at hc
    exact hWdom p hp hc
  obtain ⟨R', hRdef⟩ : ∃ R' : Subst, R' = [(Φ, Ty.fvar W)] ++ R ++ [(W, τ₀)] := ⟨_, rfl⟩
  have hsingle : ∀ (Z : Nat) (V y : Ty), Subst.onTy [(Z, V)] y = Ty.substFvar Z V y :=
    fun _ _ _ => rfl
  have hR'onTy : ∀ x, R'.onTy x = Ty.substFvar W τ₀ (R.onTy (Ty.substFvar Φ (Ty.fvar W) x)) := by
    intro x
    rw [hRdef, Subst.onTy_append, Subst.onTy_append, hsingle, hsingle]
  have e1 : Ty.substFvar Φ (Ty.fvar W) (Ty.fvar Φ) = Ty.fvar W := by simp [Ty.substFvar]
  have e2 : Ty.substFvar W τ₀ (Ty.fvar W) = τ₀ := by simp [Ty.substFvar]
  refine ⟨R', ?_, ?_, ?_, ?_⟩
  · rw [hRdef]
    intro p hp
    rcases List.mem_append.mp hp with hp' | hp'
    · rcases List.mem_append.mp hp' with hp'' | hp''
      · obtain rfl := List.mem_singleton.mp hp''
        exact ContainsBvarsUpTo.fvar
      · exact hR p hp''
    · obtain rfl := List.mem_singleton.mp hp'
      exact hτ₀LC
  · intro k hk
    rw [hR'onTy, Ty.substFvar_fresh (show Φ ∉ (Ty.fvar k).freeVars by
        simp only [Ty.freeVars, List.mem_singleton]; have := hΦK k hk; omega), hRK k hk]
    exact Ty.substFvar_fresh (show W ∉ (Ty.fvar k).freeVars by
        simp only [Ty.freeVars, List.mem_singleton]; have := hWge; have := hΦK k hk; omega)
  · rw [hR'onTy, e1, hRWfvar, e2]
  · intro v hv
    have hWv : W ∉ (Ty.fvar v).freeVars := by
      simp only [Ty.freeVars, List.mem_singleton]
      omega
    have hWRv : W ∉ (R.onTy (Ty.fvar v)).freeVars :=
      Subst.not_mem_onTy_freeVars hWrange hWv
    rw [hR'onTy, Ty.substFvar_fresh (show Φ ∉ (Ty.fvar v).freeVars by
        simp only [Ty.freeVars, List.mem_singleton]; omega), Ty.substFvar_fresh hWRv]

private theorem range_length_map_getD {Vs : List Ty} {d : Ty} :
    (List.range Vs.length).map (fun i => (Vs[i]?).getD d) = Vs := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp only [List.getElem_map, List.getElem_range]
    rw [List.getElem?_eq_getElem h2]
    rfl

private theorem instContents_eq_openWith {Vs : List Ty} {cs insts : List Ty}
    (hforall : List.Forall₂ (InstantiatesBy Vs) cs insts)
    (hbv : ∀ c ∈ cs, ContainsBvarsUpTo Vs.length c) :
    insts = cs.map (Ty.openWith Vs) := by
  induction hforall with
  | nil => rfl
  | @cons c inst cs' insts' hhead _ ih =>
    simp only [List.map_cons]
    have hc_bv : ContainsBvarsUpTo Vs.length c := hbv c List.mem_cons_self
    have heq := InstantiatesBy.eq_openWith_range hhead hc_bv
    rw [range_length_map_getD] at heq
    rw [heq]
    congr 1
    exact ih (fun c' hc' => hbv c' (List.mem_cons_of_mem _ hc'))

private theorem freshVars_getElem? {Φ k i : Nat} (hi : i < k) :
    (freshVars Φ k)[i]? = some (Φ + i) := by
  simp only [freshVars, List.getElem?_map, List.getElem?_range hi, Option.map_some]

/-- Move the constructor's fresh parameter block out of the residual's way and
    realize the declarative constructor arguments there. -/
private theorem customTy_dodge_unifier {Φ : Nat} {scrutTy : Ty} {R : Subst}
    {K : List Nat} {ctor : Ctor} {tyArgs : List Ty}
    (hbscrut : Ty.BelowFvars Φ scrutTy)
    (hR : ∀ p ∈ R, p.2.IsLC) (hKΦ : ∀ k ∈ K, k < Φ)
    (hKfix : ∀ k ∈ K, R.onTy (.fvar k) = .fvar k)
    (htyArgs_lc : ∀ t ∈ tyArgs, t.IsLC) (hpc : ctor.paramCount = tyArgs.length)
    (hscrutEq : Eq (R.onTy scrutTy) (.customTy ctor.tyName tyArgs)) :
    ∃ U : Subst,
      Unifies U scrutTy
        (.customTy ctor.tyName ((freshVars Φ ctor.paramCount).map (Ty.fvar ·))) ∧
      (∀ p ∈ U, p.2.IsLC) ∧
      (∀ k ∈ K, U.onTy (.fvar k) = .fvar k) ∧
      (∀ v, v < Φ → U.onTy (.fvar v) = R.onTy (.fvar v)) ∧
      ((freshVars Φ ctor.paramCount).map (Ty.fvar ·)).map U.onTy = tyArgs := by
  obtain ⟨W₀, hW₀ge, hW₀fresh⟩ := exists_fresh_block
    (R.map Prod.fst ++ R.flatMap (fun p => p.2.freeVars) ++ tyArgs.flatMap Ty.freeVars)
    Φ ctor.paramCount
  obtain ⟨U, hUdef⟩ : ∃ U : Subst,
    U = (freshVars Φ ctor.paramCount).zip ((freshVars W₀ ctor.paramCount).map (Ty.fvar ·))
        ++ R ++ (freshVars W₀ ctor.paramCount).zip tyArgs := ⟨_, rfl⟩
  have hUonTy : ∀ x, U.onTy x =
      Subst.onTy ((freshVars W₀ ctor.paramCount).zip tyArgs)
        (R.onTy (Subst.onTy ((freshVars Φ ctor.paramCount).zip
          ((freshVars W₀ ctor.paramCount).map (Ty.fvar ·))) x)) := by
    intro x; rw [hUdef, Subst.onTy_append, Subst.onTy_append]
  have hWi_mem : ∀ {i : Nat}, i < ctor.paramCount →
      W₀ + i ∈ freshVars W₀ ctor.paramCount := by
    intro i hi; simp only [freshVars, List.mem_map, List.mem_range]; exact ⟨i, hi, rfl⟩
  have hWs_notin_Rkeys : ∀ w ∈ freshVars W₀ ctor.paramCount, w ∉ R.map Prod.fst := by
    intro w hw hc
    have hwge := freshVars_ge w hw
    have := hW₀fresh w (List.mem_append_left _ (List.mem_append_left _ hc)); omega
  have hWs_Rrange : ∀ w ∈ freshVars W₀ ctor.paramCount, ∀ q ∈ R, w ∉ q.2.freeVars := by
    intro w hw q hq hc
    have hwge := freshVars_ge w hw
    have := hW₀fresh w (List.mem_append_left _ (List.mem_append_right _
      (List.mem_flatMap.mpr ⟨q, hq, hc⟩))); omega
  have htyArgs_belowW₀ : ∀ t ∈ tyArgs, Ty.BelowFvars W₀ t := by
    intro t ht; apply Ty.BelowFvars.of_freeVars_lt
    intro v hv
    exact hW₀fresh v (List.mem_append_right _ (List.mem_flatMap.mpr ⟨t, ht, hv⟩))
  have hU_index : ∀ (i : Nat) (v : Ty), i < ctor.paramCount →
      tyArgs[i]? = some v → U.onTy (Ty.fvar (Φ + i)) = v := by
    intro i v hi hvi
    rw [hUonTy]
    have hL1 : Subst.onTy ((freshVars Φ ctor.paramCount).zip
        ((freshVars W₀ ctor.paramCount).map (Ty.fvar ·))) (Ty.fvar (Φ + i))
        = Ty.fvar (W₀ + i) := by
      apply Ty.substFvars_zip_fvar_eq' freshVars_nodup (freshVars_getElem? hi)
      · rw [List.getElem?_map, freshVars_getElem? hi]; rfl
      · intro X hX hc
        simp only [Ty.freeVars, List.mem_singleton] at hc
        have hXlt := freshVars_lt X hX; omega
    rw [hL1]
    have hL2 : R.onTy (Ty.fvar (W₀ + i)) = Ty.fvar (W₀ + i) := by
      apply Ty.substFvars_eq_self_of_no_key
      intro p hp hc
      simp only [Ty.freeVars, List.mem_singleton] at hc
      have hkey : p.1 ∈ R.map Prod.fst := List.mem_map.mpr ⟨p, hp, rfl⟩
      rw [hc] at hkey
      exact hWs_notin_Rkeys (W₀ + i) (hWi_mem hi) hkey
    rw [hL2]
    apply Ty.substFvars_zip_fvar_eq' freshVars_nodup (freshVars_getElem? hi) hvi
    intro w hw hc
    have hwge := freshVars_ge w hw
    have hvmem : v ∈ tyArgs := List.mem_of_getElem? hvi
    have := (htyArgs_belowW₀ v hvmem).mem_lt w hc; omega
  have hmap_eq : ((freshVars Φ ctor.paramCount).map (Ty.fvar ·)).map U.onTy = tyArgs := by
    apply List.ext_getElem?
    intro i
    rcases Nat.lt_or_ge i ctor.paramCount with hi | hi
    · rw [List.getElem?_map, List.getElem?_map, freshVars_getElem? hi]
      simp only [Option.map_some]
      have hi' : i < tyArgs.length := by omega
      rw [List.getElem?_eq_getElem hi']
      congr 1
      exact hU_index i (tyArgs[i]'hi') hi (by rw [List.getElem?_eq_getElem hi'])
    · rw [List.getElem?_eq_none (by simp only [List.length_map, freshVars_length]; exact hi),
        List.getElem?_eq_none (by omega)]
  have hA_id_scrut : Subst.onTy ((freshVars Φ ctor.paramCount).zip
      ((freshVars W₀ ctor.paramCount).map (Ty.fvar ·))) scrutTy = scrutTy := by
    apply Ty.substFvars_eq_self_of_no_key
    intro p hp hc
    have hp1 : p.1 ∈ freshVars Φ ctor.paramCount := (List.of_mem_zip hp).1
    have hge := freshVars_ge p.1 hp1
    have hlt := hbscrut.mem_lt p.1 hc; omega
  have hC_id_custom : Subst.onTy ((freshVars W₀ ctor.paramCount).zip tyArgs)
      (Ty.customTy ctor.tyName tyArgs) = Ty.customTy ctor.tyName tyArgs := by
    apply Ty.substFvars_eq_self_of_no_key
    intro p hp hc
    have hp1 : p.1 ∈ freshVars W₀ ctor.paramCount := (List.of_mem_zip hp).1
    have hge := freshVars_ge p.1 hp1
    have hcb : Ty.BelowFvars W₀ (Ty.customTy ctor.tyName tyArgs) := .customTy htyArgs_belowW₀
    have hlt := hcb.mem_lt p.1 hc; omega
  have hUL : Eq (U.onTy scrutTy) (Ty.customTy ctor.tyName tyArgs) := by
    rw [hUonTy, hA_id_scrut, hscrutEq, hC_id_custom]
  have hUR : U.onTy (Ty.customTy ctor.tyName ((freshVars Φ ctor.paramCount).map (Ty.fvar ·)))
      = Ty.customTy ctor.tyName tyArgs := by
    rw [Subst.onTy_customTy, hmap_eq]
  have hUni : Unifies U scrutTy
      (Ty.customTy ctor.tyName ((freshVars Φ ctor.paramCount).map (Ty.fvar ·))) := by
    show Eq _ _
    rw [hUR]; exact hUL
  have hUlc : ∀ p ∈ U, p.2.IsLC := by
    rw [hUdef]
    intro p hp
    rcases List.mem_append.mp hp with hp' | hp'
    · rcases List.mem_append.mp hp' with hp'' | hp''
      · have hmem := (List.of_mem_zip hp'').2
        obtain ⟨x, _, hxeq⟩ := List.mem_map.mp hmem
        rw [← hxeq]; exact ContainsBvarsUpTo.fvar
      · exact hR p hp''
    · have hmem := (List.of_mem_zip hp').2
      exact htyArgs_lc p.2 hmem
  have hUeqR : ∀ v, v < Φ → U.onTy (Ty.fvar v) = R.onTy (Ty.fvar v) := by
    intro v hv
    rw [hUonTy]
    have hA_id : Subst.onTy ((freshVars Φ ctor.paramCount).zip
        ((freshVars W₀ ctor.paramCount).map (Ty.fvar ·))) (Ty.fvar v) = Ty.fvar v := by
      apply Ty.substFvars_eq_self_of_no_key
      intro p hp hc
      simp only [Ty.freeVars, List.mem_singleton] at hc
      have hp1 : p.1 ∈ freshVars Φ ctor.paramCount := (List.of_mem_zip hp).1
      have := freshVars_ge p.1 hp1; omega
    rw [hA_id]
    apply Ty.substFvars_eq_self_of_no_key
    intro p hp hc
    have hp1 : p.1 ∈ freshVars W₀ ctor.paramCount := (List.of_mem_zip hp).1
    have hge := freshVars_ge p.1 hp1
    exact Subst.not_mem_onTy_freeVars (hWs_Rrange p.1 hp1)
      (by simp only [Ty.freeVars, List.mem_singleton]; omega) hc
  have hUK : ∀ k ∈ K, U.onTy (Ty.fvar k) = Ty.fvar k := fun k hk =>
    (hUeqR k (hKΦ k hk)).trans (hKfix k hk)
  exact ⟨U, hUni, hUlc, hUK, hUeqR, hmap_eq⟩

/-- Produce and factor the named-branch constructor unifier. -/
private theorem customTy_unify_dodge {Φ : Nat} {scrutTy : Ty} {R : Subst}
    {K : List Nat} {ctor : Ctor} {tyArgs : List Ty}
    (hscrutLC : scrutTy.IsLC) (hbscrut : Ty.BelowFvars Φ scrutTy)
    (hR : ∀ p ∈ R, p.2.IsLC) (hKΦ : ∀ k ∈ K, k < Φ)
    (hKfix : ∀ k ∈ K, R.onTy (.fvar k) = .fvar k)
    (htyArgs_lc : ∀ t ∈ tyArgs, t.IsLC) (hpc : ctor.paramCount = tyArgs.length)
    (hscrutEq : Eq (R.onTy scrutTy) (.customTy ctor.tyName tyArgs)) :
    ∃ (S₀ R₀ : Subst),
      UnifyRel scrutTy
        (.customTy ctor.tyName ((freshVars Φ ctor.paramCount).map (Ty.fvar ·))) S₀ ∧
      (∀ p ∈ S₀, p.2.IsLC) ∧
      (∀ p ∈ S₀, Ty.BelowFvars (Φ + ctor.paramCount) p.2) ∧
      (∀ p ∈ S₀, p.1 ∉ K) ∧
      (∀ p ∈ R₀, p.2.IsLC) ∧
      (∀ k ∈ K, R₀.onTy (.fvar k) = .fvar k) ∧
      Subst.AgreesBelow Φ R (S₀ ++ R₀) ∧
      (((freshVars Φ ctor.paramCount).map (Ty.fvar ·)).map S₀.onTy).map R₀.onTy
        = tyArgs := by
  obtain ⟨U, hUni, hUlc, hUK, hUeqR, hmap_eq⟩ :=
    customTy_dodge_unifier hbscrut hR hKΦ hKfix htyArgs_lc hpc hscrutEq
  have hcustomTy_lc : (Ty.customTy ctor.tyName
      ((freshVars Φ ctor.paramCount).map (Ty.fvar ·))).IsLC :=
    ContainsBvarsUpTo.customTy (fun t ht => by
      obtain ⟨x, _, rfl⟩ := List.mem_map.mp ht; exact ContainsBvarsUpTo.fvar)
  obtain ⟨S₀, h₀, hS₀K⟩ := UnifyRel.complete_K hscrutLC hcustomTy_lc hUlc hUni hUK
  obtain ⟨R₀, hR₀eq, hR₀lc, hR₀K⟩ := UnifyRel.greatest_K h₀ U hUlc hUni hUK
  have hS₀ : ∀ p ∈ S₀, p.2.IsLC := UnifyRel.lc h₀ hscrutLC hcustomTy_lc
  have hS₀below : ∀ p ∈ S₀, Ty.BelowFvars (Φ + ctor.paramCount) p.2 := by
    apply UnifyRel.belowFvars h₀ (hbscrut.mono (by omega))
    apply Ty.BelowFvars.customTy
    intro t ht
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp ht
    exact Ty.BelowFvars.fvar (by have := freshVars_lt x hx; omega)
  refine ⟨S₀, R₀, h₀, hS₀, hS₀below, hS₀K, hR₀lc, hR₀K, ?_, ?_⟩
  · intro v hv
    simp only [Subst.onTy_append]
    exact (hUeqR v hv).symm.trans (hR₀eq (Ty.fvar v))
  · rw [← hmap_eq]
    simp only [List.map_map]
    apply List.map_congr_left
    intro x _
    simp only [Function.comp_apply]
    exact (hR₀eq (Ty.fvar x)).symm


/-- Index extraction from a `zip` membership. -/
private theorem List.mem_zip_getElem? {α β : Type _} {l : List α} {r : List β} {p : α × β}
    (h : p ∈ l.zip r) : ∃ i : Nat, l[i]? = some p.1 ∧ r[i]? = some p.2 := by
  obtain ⟨i, hi, hp⟩ := List.mem_iff_getElem.mp h
  have h1 : i < l.length := by rw [List.length_zip] at hi; omega
  have h2 : i < r.length := by rw [List.length_zip] at hi; omega
  refine ⟨i, ?_, ?_⟩
  · rw [List.getElem?_eq_getElem h1, ← hp, List.getElem_zip]
  · rw [List.getElem?_eq_getElem h2, ← hp, List.getElem_zip]

/-- Zip membership from per-index lookups. -/
private theorem List.zip_mem_of_getElem? {α β : Type _} {l : List α} {r : List β}
    {a : α} {b : β} {i : Nat}
    (h1 : l[i]? = some a) (h2 : r[i]? = some b) : (a, b) ∈ l.zip r := by
  have hl : i < l.length := (List.getElem?_eq_some_iff.mp h1).1
  have hr : i < r.length := (List.getElem?_eq_some_iff.mp h2).1
  have hz : i < (l.zip r).length := by rw [List.length_zip]; omega
  have hget : (l.zip r)[i]'hz = (a, b) := by
    rw [List.getElem_zip]
    rw [List.getElem?_eq_getElem hl] at h1
    rw [List.getElem?_eq_getElem hr] at h2
    rw [Option.some.inj h1, Option.some.inj h2]
  rw [← hget]
  exact List.getElem_mem _

/-- Producer completeness for a sequential list of match branches. -/
theorem InferBranches.complete {branches : List (MatchPattern × Expr)} :
    ∀ {Φ : Nat} {ctx : Ctx} {scrutTy : Ty} {ρ : Ty} {R : Subst} (K : List Nat),
    (∀ br ∈ branches, Infer.CompleteAt br.2) →
    CtxWF ctx → CtxBelow Φ ctx →
    scrutTy.IsLC → Ty.BelowFvars Φ scrutTy →
    ρ.IsLC → Ty.BelowFvars Φ ρ →
    (∀ p ∈ R, p.2.IsLC) →
    (∀ k ∈ K, k < Φ) →
    (∀ y ∈ Expr.tyFreeVars.BranchList.tyFreeVars branches, y ∈ K) →
    (∀ k ∈ K, R.onTy (.fvar k) = .fvar k) →
    -- Branch premises remain in the direct declarative source relation.
    (∀ br ∈ branches, TypeOfMatchBranch (R.onCtx ctx)
        (br.1, br.2)
        ( (R.onTy scrutTy)) ( (R.onTy ρ))) →
    ∃ Φ' S R',
      InferBranches Φ ctx scrutTy ρ branches Φ' S ∧
      Subst.AgreesBelow Φ R (S ++ R') ∧
      (∀ p ∈ R', p.2.IsLC) ∧
      (∀ k ∈ K, R'.onTy (.fvar k) = .fvar k) ∧
      (∀ p ∈ S, p.1 ∉ K) := by
  induction branches with
  | nil =>
    intro Φ ctx scrutTy ρ R K hcompl hwf hbelow hscrutLC hscrutB hρLC hρB hR hKΦ hKbr hKfix hbrs
    refine ⟨Φ, [], R, .nil, ?_, ?_, ?_, ?_⟩
    · intro v hv
      rw [List.nil_append]
    · exact hR
    · exact hKfix
    · intro p hp; simp at hp
  | cons br rest ih =>
    intro Φ ctx scrutTy ρ R K hcompl hwf hbelow hscrutLC hscrutB hρLC hρB hR hKΦ hKbr hKfix hbrs
    rcases br with ⟨pat, body⟩
    cases pat with
    | named c n =>
      have hcomplBody : Infer.CompleteAt body :=
        hcompl (MatchPattern.named c n, body) (List.mem_cons_self ..)
      have hcomplRest : ∀ br ∈ rest, Infer.CompleteAt br.2 :=
        fun br hbr => hcompl br (List.mem_cons_of_mem _ hbr)
      have hKbody : ∀ y ∈ body.tyFreeVars, y ∈ K := fun y hy => hKbr y (by
        simp only [Expr.tyFreeVars.BranchList.tyFreeVars, List.mem_append]; exact Or.inl hy)
      have hKrest : ∀ y ∈ Expr.tyFreeVars.BranchList.tyFreeVars rest, y ∈ K := fun y hy => hKbr y (by
        simp only [Expr.tyFreeVars.BranchList.tyFreeVars, List.mem_append]; exact Or.inr hy)
      have hbrsHead : TypeOfMatchBranch (R.onCtx ctx)
          ((MatchPattern.named c n), body)
          ( (R.onTy scrutTy)) ( (R.onTy ρ)) :=
        hbrs (MatchPattern.named c n, body) (List.mem_cons_self ..)
      have hbrsRest : ∀ br ∈ rest, TypeOfMatchBranch (R.onCtx ctx)
          (br.1, br.2)
          ( (R.onTy scrutTy)) ( (R.onTy ρ)) :=
        fun br hbr => hbrs br (List.mem_cons_of_mem _ hbr)
      cases hbrsHead with
      | mk hspec hctxeq hbodyDecl =>
        rename_i ctor tyArgs instContents
        subst hctxeq
        rcases hspec with ⟨hlookE, hscrutEq, hpc, hn, hfields⟩
        have hlook : LookupList.get? ctx.ctors c = some ctor := by
          simpa [Subst.onCtx] using hlookE
        have hscrutErased_lc : ( (R.onTy scrutTy)).IsLC :=
          Subst.onTy_lc hR hscrutLC
        have hcustom_lc : (Ty.customTy ctor.tyName tyArgs).IsLC := by
          rwa [hscrutEq] at hscrutErased_lc
        have htyArgs_lc : ∀ t ∈ tyArgs, t.IsLC := by
          intro t ht
          cases hcustom_lc with
          | customTy hall => exact hall t ht
        obtain ⟨S₀, R₀, hUni₀, hS₀lc, hS₀below, hS₀K, hR₀lc, hR₀K, hAgree₀, hmap_eq⟩ :=
          customTy_unify_dodge (scrutTy := scrutTy) (R := R) (K := K) (ctor := ctor)
            (tyArgs := tyArgs) hscrutLC hscrutB hR hKΦ hKfix htyArgs_lc hpc hscrutEq
        set ta0 : List Ty := (freshVars Φ ctor.paramCount).map (Ty.fvar ·) with hta0
        set taS₀ : List Ty := ta0.map S₀.onTy with htaS₀
        set branchCtx : Ctx :=
          { S₀.onCtx ctx with
            env := (ctor.contents.map (Ty.openWith taS₀)).map PolyTy.mkTrivial
              ++ (S₀.onCtx ctx).env }
          with hbranchCtx
        have htaS₀lc : ∀ t ∈ taS₀, t.IsLC := by
          intro t ht
          rw [htaS₀] at ht
          obtain ⟨v, hv, rfl⟩ := List.mem_map.mp ht
          rw [hta0] at hv
          obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hv
          exact Subst.onTy_lc hS₀lc ContainsBvarsUpTo.fvar
        have htaS₀len : ctor.paramCount = taS₀.length := by
          rw [htaS₀, hta0, List.length_map, List.length_map]
          simp
        have htaS₀bel : ∀ t ∈ taS₀, Ty.BelowFvars (Φ + ctor.paramCount) t := by
          intro t ht
          rw [htaS₀] at ht
          obtain ⟨v, hv, rfl⟩ := List.mem_map.mp ht
          rw [hta0] at hv
          obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hv
          exact Subst.onTy_belowFvars hS₀below
            (.fvar (by have := freshVars_lt x hx; omega))
        have hbodyWF : CtxWF branchCtx := by
          rw [hbranchCtx]
          exact branchBindings_wf (ctorr := ctor) (ta := taS₀)
            (Subst.onCtx_wf hS₀lc hwf) htaS₀lc htaS₀len
        have hbodyBelow : CtxBelow (Φ + ctor.paramCount) branchCtx := by
          rw [hbranchCtx]
          exact branchBindings_below (ctorr := ctor) (ta := taS₀)
            (Subst.onCtx_below hS₀below (by omega) hbelow) htaS₀bel
        have hb1 : R₀.onCtx branchCtx = { R₀.onCtx (S₀.onCtx ctx) with
            env := (ctor.contents.map (Ty.openWith (taS₀.map R₀.onTy))).map PolyTy.mkTrivial
              ++ (R₀.onCtx (S₀.onCtx ctx)).env } := by
          rw [hbranchCtx]
          exact Subst.onCtx_branchBindings (ctorr := ctor) (ta := taS₀)
            (ctx := S₀.onCtx ctx) hR₀lc
        have hargs : taS₀.map R₀.onTy = tyArgs := by
          rw [htaS₀, hta0]
          exact hmap_eq
        have hb2' : (R₀.onCtx branchCtx) =
            { (R₀.onCtx (S₀.onCtx ctx)) with
              env := (( ctor).contents.map (Ty.openWith tyArgs)).map PolyTy.mkTrivial
                ++ (R₀.onCtx (S₀.onCtx ctx)).env } := by
          rw [hargs] at hb1
          exact hb1
        have hAgree₀' : Subst.AgreesBelow Φ (S₀ ++ R₀) R := by
          intro v hv
          exact Eq.symm (hAgree₀ v hv)
        have htail : (R₀.onCtx (S₀.onCtx ctx)) = (R.onCtx ctx) := by
          have h1 : R₀.onCtx (S₀.onCtx ctx) = (S₀ ++ R₀).onCtx ctx := by
            simp only [Subst.onCtx_append]
          rw [h1]
          exact Subst.onCtx_congr (Φ := Φ) (S := S₀ ++ R₀) (T := R) hAgree₀' hbelow
        have hbv : ∀ c ∈ ctor.contents, ContainsBvarsUpTo tyArgs.length c := by
          intro c hc
          simpa [← hpc] using ctor.bound c hc
        have hinst : instContents = ctor.contents.map (Ty.openWith tyArgs) := by
          exact instContents_eq_openWith hfields hbv
        have hprefix : instContents.map PolyTy.mkTrivial
            = (( ctor).contents.map (Ty.openWith tyArgs)).map PolyTy.mkTrivial := by
          rw [hinst]
        have hctxBridge :
            { (R.onCtx ctx) with
                env := instContents.map PolyTy.mkTrivial ++ (R.onCtx ctx).env }
            = (R₀.onCtx branchCtx) := by
          rw [hb2']
          simp only [htail]
          congr 1
          rw [hprefix]
        have hbodyAlg : TypeOfHM (R₀.onCtx branchCtx) body
            ( (R.onTy ρ)) := by
          rw [hctxBridge] at hbodyDecl
          exact hbodyDecl
        have hKΦbody : ∀ k ∈ K, k < Φ + ctor.paramCount := fun k hk => by
          have := hKΦ k hk
          omega
        obtain ⟨Φ₁, S₁, τb, R₁, hInferBody, hAgree₁, hAgreeTy₁, hR₁lc, hR₁K, hS₁K⟩ :=
          hcomplBody K hbodyWF hbodyBelow hR₀lc hKΦbody hKbody hR₀K hbodyAlg
        have hle0 : Φ + ctor.paramCount ≤ Φ₁ := Infer.frontier_le hInferBody
        obtain ⟨hτb_lc, hS₁lc⟩ := Infer.lc hInferBody hbodyWF
        have hS₀ρbel : Ty.BelowFvars (Φ + ctor.paramCount) (S₀.onTy ρ) :=
          Subst.onTy_belowFvars hS₀below (hρB.mono (by omega))
        have hS₀scrutbel : Ty.BelowFvars (Φ + ctor.paramCount) (S₀.onTy scrutTy) :=
          Subst.onTy_belowFvars hS₀below (hscrutB.mono (by omega))
        have hΦbody : ∀ y ∈ body.tyFreeVars, y < Φ + ctor.paramCount := fun y hy => by
          have := hKΦ y (hKbody y hy)
          omega
        obtain ⟨hb_τbel, hb_sbel⟩ := Infer.belowFvars hInferBody hbodyBelow hΦbody
        have hS₁ρ_lc : (S₁.onTy (S₀.onTy ρ)).IsLC :=
          Subst.onTy_lc hS₁lc (Subst.onTy_lc hS₀lc hρLC)
        have hρAgree : Eq (R.onTy ρ) (R₁.onTy (S₁.onTy (S₀.onTy ρ))) := by
          have h1 : Eq (R.onTy ρ) (R₀.onTy (S₀.onTy ρ)) := by
            have h := Subst.onTy_congr (Φ := Φ) (S := R) (T := S₀ ++ R₀) hAgree₀ hρB
            simpa [Subst.onTy_append] using h
          have h2 : Eq (R₀.onTy (S₀.onTy ρ)) (R₁.onTy (S₁.onTy (S₀.onTy ρ))) := by
            have h := Subst.onTy_congr (Φ := Φ + ctor.paramCount) (S := R₀) (T := S₁ ++ R₁)
              hAgree₁ hS₀ρbel
            simpa [Subst.onTy_append] using h
          exact Eq.trans h1 h2
        have hAgreeTy₁' : Eq (R₁.onTy τb) (R.onTy ρ) := by
          exact Eq.symm hAgreeTy₁
        have hUnifies₁ : Unifies R₁ τb (S₁.onTy (S₀.onTy ρ)) := by
          rw [Unifies]
          exact Eq.trans hAgreeTy₁' hρAgree
        obtain ⟨S₂, hUni₂, hS₂K⟩ := UnifyRel.complete_K (a := τb) (b := S₁.onTy (S₀.onTy ρ))
          (U := R₁) hτb_lc hS₁ρ_lc hR₁lc hUnifies₁ hR₁K
        obtain ⟨R₂, hFactors₂, hR₂lc, hR₂K⟩ :=
          UnifyRel.greatest_K hUni₂ R₁ hR₁lc hUnifies₁ hR₁K
        have hAgree₂ : Subst.AgreesBelow Φ₁ R₁ (S₂ ++ R₂) := by
          intro v hv
          rw [Subst.onTy_append]
          exact hFactors₂ (Ty.fvar v)
        have hS₂lc : ∀ p ∈ S₂, p.2.IsLC := UnifyRel.lc hUni₂ hτb_lc hS₁ρ_lc
        have hS₀ρbel₁ : Ty.BelowFvars Φ₁ (S₀.onTy ρ) :=
          (Subst.onTy_belowFvars hS₀below (hρB.mono (by omega))).mono hle0
        have hS₀scrutbel₁ : Ty.BelowFvars Φ₁ (S₀.onTy scrutTy) :=
          (Subst.onTy_belowFvars hS₀below (hscrutB.mono (by omega))).mono hle0
        have hS₁ρbel : Ty.BelowFvars Φ₁ (S₁.onTy (S₀.onTy ρ)) :=
          Subst.onTy_belowFvars hb_sbel hS₀ρbel₁
        have hS₁scrutbel : Ty.BelowFvars Φ₁ (S₁.onTy (S₀.onTy scrutTy)) :=
          Subst.onTy_belowFvars hb_sbel hS₀scrutbel₁
        have hS₂bel : ∀ p ∈ S₂, Ty.BelowFvars Φ₁ p.2 :=
          UnifyRel.belowFvars hUni₂ hb_τbel hS₁ρbel
        have hctx1WF : CtxWF (S₂.onCtx (S₁.onCtx (S₀.onCtx ctx))) :=
          Subst.onCtx_wf hS₂lc (Subst.onCtx_wf hS₁lc (Subst.onCtx_wf hS₀lc hwf))
        have hctx1below : CtxBelow Φ₁ (S₂.onCtx (S₁.onCtx (S₀.onCtx ctx))) :=
          Subst.onCtx_below hS₂bel (le_refl _) (Subst.onCtx_below hb_sbel (le_refl _)
            (Subst.onCtx_below (fun p hp => (hS₀below p hp).mono hle0) (by omega) hbelow))
        have hscrut1_lc : (S₂.onTy (S₁.onTy (S₀.onTy scrutTy))).IsLC :=
          Subst.onTy_lc hS₂lc (Subst.onTy_lc hS₁lc (Subst.onTy_lc hS₀lc hscrutLC))
        have hscrut1_bel : Ty.BelowFvars Φ₁ (S₂.onTy (S₁.onTy (S₀.onTy scrutTy))) :=
          Subst.onTy_belowFvars hS₂bel hS₁scrutbel
        have hρ1_lc : (S₂.onTy (S₁.onTy (S₀.onTy ρ))).IsLC :=
          Subst.onTy_lc hS₂lc (Subst.onTy_lc hS₁lc (Subst.onTy_lc hS₀lc hρLC))
        have hρ1_bel : Ty.BelowFvars Φ₁ (S₂.onTy (S₁.onTy (S₀.onTy ρ))) :=
          Subst.onTy_belowFvars hS₂bel hS₁ρbel
        have hKΦ₁ : ∀ k ∈ K, k < Φ₁ := fun k hk => by
          have := hKΦ k hk
          have := hle0
          omega
        have hAgree₀₁ : Subst.AgreesBelow (Φ + ctor.paramCount) R₀ ((S₁ ++ S₂) ++ R₂) :=
          @Subst.AgreesBelow.trans_append (Φ + ctor.paramCount) Φ₁ R₀ S₁ R₁ S₂ R₂
            hle0 hAgree₁ hb_sbel hAgree₂
        have hAgreeCtx : Subst.AgreesBelow Φ R ((S₀ ++ (S₁ ++ S₂)) ++ R₂) :=
          @Subst.AgreesBelow.trans_append Φ (Φ + ctor.paramCount) R S₀ R₀ (S₁ ++ S₂) R₂
            (by omega) hAgree₀ hS₀below hAgree₀₁
        have hAgreeCtx' : Subst.AgreesBelow Φ ((S₀ ++ (S₁ ++ S₂)) ++ R₂) R := by
          intro v hv
          exact Eq.symm (hAgreeCtx v hv)
        have hctxEq : (R₂.onCtx (S₂.onCtx (S₁.onCtx (S₀.onCtx ctx))))
            = (R.onCtx ctx) := by
          have h1 : R₂.onCtx (S₂.onCtx (S₁.onCtx (S₀.onCtx ctx)))
              = ((S₀ ++ (S₁ ++ S₂)) ++ R₂).onCtx ctx := by
            simp only [Subst.onCtx_append]
          rw [h1]
          exact Subst.onCtx_congr (Φ := Φ) (S := (S₀ ++ (S₁ ++ S₂)) ++ R₂) (T := R)
            hAgreeCtx' hbelow
        have hscrutEq' :  (R₂.onTy (S₂.onTy (S₁.onTy (S₀.onTy scrutTy))))
            =  (R.onTy scrutTy) := by
          have h := Subst.onTy_congr (Φ := Φ) (S := (S₀ ++ (S₁ ++ S₂)) ++ R₂) (T := R)
            hAgreeCtx' hscrutB
          simpa [Subst.onTy_append] using h
        have hρEq' :  (R₂.onTy (S₂.onTy (S₁.onTy (S₀.onTy ρ))))
            =  (R.onTy ρ) := by
          have h := Subst.onTy_congr (Φ := Φ) (S := (S₀ ++ (S₁ ++ S₂)) ++ R₂) (T := R)
            hAgreeCtx' hρB
          simpa [Subst.onTy_append] using h
        have hbrsRest' : ∀ br ∈ rest, TypeOfMatchBranch
            (R₂.onCtx (S₂.onCtx (S₁.onCtx (S₀.onCtx ctx))))
            (br.1, br.2)
            ( (R₂.onTy (S₂.onTy (S₁.onTy (S₀.onTy scrutTy)))))
            ( (R₂.onTy (S₂.onTy (S₁.onTy (S₀.onTy ρ))))) := by
          intro br hbr
          have h := hbrsRest br hbr
          rw [← hctxEq, ← hscrutEq', ← hρEq'] at h
          exact h
        obtain ⟨Φ₂, S₃, R₃, hInferRest, hAgree₃, hR₃lc, hR₃K, hS₃K⟩ :=
          ih K hcomplRest hctx1WF hctx1below hscrut1_lc hscrut1_bel hρ1_lc hρ1_bel
            hR₂lc hKΦ₁ hKrest hR₂K hbrsRest'
        have hAgree₂₃ : Subst.AgreesBelow Φ₁ R₁ ((S₂ ++ S₃) ++ R₃) :=
          @Subst.AgreesBelow.trans_append Φ₁ Φ₁ R₁ S₂ R₂ S₃ R₃
            (le_refl _) hAgree₂ hS₂bel hAgree₃
        have hAgree₁₂₃ : Subst.AgreesBelow (Φ + ctor.paramCount) R₀
            ((S₁ ++ S₂ ++ S₃) ++ R₃) := by
          have h := @Subst.AgreesBelow.trans_append (Φ + ctor.paramCount) Φ₁ R₀ S₁ R₁ (S₂ ++ S₃) R₃
            hle0 hAgree₁ hb_sbel hAgree₂₃
          simpa [List.append_assoc] using h
        have hAgree : Subst.AgreesBelow Φ R ((S₀ ++ S₁ ++ S₂ ++ S₃) ++ R₃) := by
          have h := @Subst.AgreesBelow.trans_append Φ (Φ + ctor.paramCount) R S₀ R₀
            (S₁ ++ S₂ ++ S₃) R₃ (by omega) hAgree₀ hS₀below hAgree₁₂₃
          simpa [List.append_assoc] using h
        refine ⟨Φ₂, S₀ ++ S₁ ++ S₂ ++ S₃, R₃,
          ?_, ?_, ?_, ?_, ?_⟩
        · exact .cons hlook hn hUni₀ hInferBody hUni₂ hInferRest
        · simpa [List.append_assoc] using hAgree
        · exact hR₃lc
        · exact hR₃K
        · intro p hp
          rw [List.mem_append, List.mem_append, List.mem_append] at hp
          rcases hp with ((hp | hp) | hp) | hp
          · exact hS₀K p hp
          · exact hS₁K p hp
          · exact hS₂K p hp
          · exact hS₃K p hp
    | wildcard =>
      have hcomplBody : Infer.CompleteAt body :=
        hcompl (MatchPattern.wildcard, body) (List.mem_cons_self ..)
      have hcomplRest : ∀ br ∈ rest, Infer.CompleteAt br.2 :=
        fun br hbr => hcompl br (List.mem_cons_of_mem _ hbr)
      have hKbody : ∀ y ∈ body.tyFreeVars, y ∈ K := fun y hy => hKbr y (by
        simp only [Expr.tyFreeVars.BranchList.tyFreeVars, List.mem_append]; exact Or.inl hy)
      have hKrest : ∀ y ∈ Expr.tyFreeVars.BranchList.tyFreeVars rest, y ∈ K := fun y hy => hKbr y (by
        simp only [Expr.tyFreeVars.BranchList.tyFreeVars, List.mem_append]; exact Or.inr hy)
      have hbrsHead : TypeOfMatchBranch (R.onCtx ctx)
          ((MatchPattern.wildcard), body)
          ( (R.onTy scrutTy)) ( (R.onTy ρ)) :=
        hbrs (MatchPattern.wildcard, body) (List.mem_cons_self ..)
      have hbrsRest : ∀ br ∈ rest, TypeOfMatchBranch (R.onCtx ctx)
          (br.1, br.2)
          ( (R.onTy scrutTy)) ( (R.onTy ρ)) :=
        fun br hbr => hbrs br (List.mem_cons_of_mem _ hbr)
      cases hbrsHead with
      | wildcard hbodyDecl =>
        obtain ⟨Φ₁, S₁, τb, R₁, hInferBody, hAgree₁, hAgreeTy₁, hR₁lc, hR₁K, hS₁K⟩ :=
          hcomplBody K hwf hbelow hR hKΦ hKbody hKfix hbodyDecl
        have hfle : Φ ≤ Φ₁ := Infer.frontier_le hInferBody
        obtain ⟨hτb_lc, hS₁lc⟩ := Infer.lc hInferBody hwf
        have hΦbody : ∀ y ∈ body.tyFreeVars, y < Φ := fun y hy => hKΦ y (hKbody y hy)
        obtain ⟨hb_τbel, hb_sbel⟩ := Infer.belowFvars hInferBody hbelow hΦbody
        have hS₁ρ_lc : (S₁.onTy ρ).IsLC := Subst.onTy_lc hS₁lc hρLC
        have hρ₁bel : Ty.BelowFvars Φ₁ (S₁.onTy ρ) :=
          Subst.onTy_belowFvars hb_sbel (hρB.mono hfle)
        have hscrut₁bel : Ty.BelowFvars Φ₁ (S₁.onTy scrutTy) :=
          Subst.onTy_belowFvars hb_sbel (hscrutB.mono hfle)
        have hAgree₁' : Subst.AgreesBelow Φ (S₁ ++ R₁) R := by
          intro v hv
          exact Eq.symm (hAgree₁ v hv)
        have hρEq : Eq (R.onTy ρ) (R₁.onTy (S₁.onTy ρ)) := by
          have h := Subst.onTy_congr (Φ := Φ) (S := S₁ ++ R₁) (T := R) hAgree₁' hρB
          simpa [Subst.onTy_append] using h.symm
        have hAgreeTy₁' : Eq (R₁.onTy τb) (R.onTy ρ) := by
          exact Eq.symm hAgreeTy₁
        have hUnifies₁ : Unifies R₁ τb (S₁.onTy ρ) := by
          rw [Unifies]
          exact Eq.trans hAgreeTy₁' hρEq
        obtain ⟨S₂, hUni₂, hS₂K⟩ := UnifyRel.complete_K (a := τb) (b := S₁.onTy ρ)
          (U := R₁) hτb_lc hS₁ρ_lc hR₁lc hUnifies₁ hR₁K
        obtain ⟨R₂, hFactors₂, hR₂lc, hR₂K⟩ :=
          UnifyRel.greatest_K hUni₂ R₁ hR₁lc hUnifies₁ hR₁K
        have hAgree₂ : Subst.AgreesBelow Φ₁ R₁ (S₂ ++ R₂) := by
          intro v hv
          rw [Subst.onTy_append]
          exact hFactors₂ (Ty.fvar v)
        have hS₂lc : ∀ p ∈ S₂, p.2.IsLC := UnifyRel.lc hUni₂ hτb_lc hS₁ρ_lc
        have hS₂bel : ∀ p ∈ S₂, Ty.BelowFvars Φ₁ p.2 := UnifyRel.belowFvars hUni₂ hb_τbel hρ₁bel
        have hctx1WF : CtxWF (S₂.onCtx (S₁.onCtx ctx)) :=
          Subst.onCtx_wf hS₂lc (Subst.onCtx_wf hS₁lc hwf)
        have hctx1below : CtxBelow Φ₁ (S₂.onCtx (S₁.onCtx ctx)) :=
          Subst.onCtx_below hS₂bel (le_refl _) (Subst.onCtx_below hb_sbel hfle hbelow)
        have hscrut1_lc : (S₂.onTy (S₁.onTy scrutTy)).IsLC :=
          Subst.onTy_lc hS₂lc (Subst.onTy_lc hS₁lc hscrutLC)
        have hscrut1_bel : Ty.BelowFvars Φ₁ (S₂.onTy (S₁.onTy scrutTy)) :=
          Subst.onTy_belowFvars hS₂bel hscrut₁bel
        have hρ1_lc : (S₂.onTy (S₁.onTy ρ)).IsLC :=
          Subst.onTy_lc hS₂lc (Subst.onTy_lc hS₁lc hρLC)
        have hρ1_bel : Ty.BelowFvars Φ₁ (S₂.onTy (S₁.onTy ρ)) :=
          Subst.onTy_belowFvars hS₂bel hρ₁bel
        have hKΦ₁ : ∀ k ∈ K, k < Φ₁ := fun k hk => by
          have := hKΦ k hk
          have := hfle
          omega
        have hAgree₀₁ : Subst.AgreesBelow Φ R ((S₁ ++ S₂) ++ R₂) :=
          @Subst.AgreesBelow.trans_append Φ Φ₁ R S₁ R₁ S₂ R₂ hfle hAgree₁ hb_sbel hAgree₂
        have hAgreeCtx' : Subst.AgreesBelow Φ ((S₁ ++ S₂) ++ R₂) R := by
          intro v hv
          exact Eq.symm (hAgree₀₁ v hv)
        have hctxEq : (R₂.onCtx (S₂.onCtx (S₁.onCtx ctx)))
            = (R.onCtx ctx) := by
          have h1 : R₂.onCtx (S₂.onCtx (S₁.onCtx ctx)) = ((S₁ ++ S₂) ++ R₂).onCtx ctx := by
            simp only [Subst.onCtx_append]
          rw [h1]
          exact Subst.onCtx_congr (Φ := Φ) (S := (S₁ ++ S₂) ++ R₂) (T := R) hAgreeCtx' hbelow
        have hscrutEq' :  (R₂.onTy (S₂.onTy (S₁.onTy scrutTy)))
            =  (R.onTy scrutTy) := by
          have h := Subst.onTy_congr (Φ := Φ) (S := (S₁ ++ S₂) ++ R₂) (T := R)
            hAgreeCtx' hscrutB
          simpa [Subst.onTy_append] using h
        have hρEq' :  (R₂.onTy (S₂.onTy (S₁.onTy ρ)))
            =  (R.onTy ρ) := by
          have h := Subst.onTy_congr (Φ := Φ) (S := (S₁ ++ S₂) ++ R₂) (T := R)
            hAgreeCtx' hρB
          simpa [Subst.onTy_append] using h
        have hbrsRest' : ∀ br ∈ rest, TypeOfMatchBranch
            (R₂.onCtx (S₂.onCtx (S₁.onCtx ctx)))
            (br.1, br.2)
            ( (R₂.onTy (S₂.onTy (S₁.onTy scrutTy))))
            ( (R₂.onTy (S₂.onTy (S₁.onTy ρ)))) := by
          intro br hbr
          have h := hbrsRest br hbr
          rw [← hctxEq, ← hscrutEq', ← hρEq'] at h
          exact h
        obtain ⟨Φ₂, S₃, R₃, hInferRest, hAgree₃, hR₃lc, hR₃K, hS₃K⟩ :=
          ih K hcomplRest hctx1WF hctx1below hscrut1_lc hscrut1_bel hρ1_lc hρ1_bel
            hR₂lc hKΦ₁ hKrest hR₂K hbrsRest'
        have hAgree₂₃ : Subst.AgreesBelow Φ₁ R₁ ((S₂ ++ S₃) ++ R₃) :=
          @Subst.AgreesBelow.trans_append Φ₁ Φ₁ R₁ S₂ R₂ S₃ R₃
            (le_refl _) hAgree₂ hS₂bel hAgree₃
        have hAgree : Subst.AgreesBelow Φ R ((S₁ ++ (S₂ ++ S₃)) ++ R₃) :=
          @Subst.AgreesBelow.trans_append Φ Φ₁ R S₁ R₁ (S₂ ++ S₃) R₃ hfle hAgree₁ hb_sbel hAgree₂₃
        refine ⟨Φ₂, S₁ ++ S₂ ++ S₃, R₃,
          ?_, ?_, ?_, ?_, ?_⟩
        · exact .consWild hInferBody hUni₂ hInferRest
        · simpa [List.append_assoc] using hAgree
        · exact hR₃lc
        · exact hR₃K
        · intro p hp
          rw [List.mem_append, List.mem_append] at hp
          rcases hp with (hp | hp) | hp
          · exact hS₁K p hp
          · exact hS₂K p hp
          · exact hS₃K p hp

/-- Producer completeness for a match with its declarative scrutinee and branch
    typings already separated. -/
theorem Infer.complete_match_aux {scrut : Expr} {branches : List (MatchPattern × Expr)}
    {Φ : Nat} {ctx : Ctx} {S₀ : Subst} {scrutTy : Ty} {τ₀ : Ty}
    {K : List Nat}
    (ihscrut : Infer.CompleteAt scrut)
    (ihbranches : ∀ br ∈ branches, Infer.CompleteAt br.2)
    (hwf : CtxWF ctx) (hbelow : CtxBelow Φ ctx) (hS₀ : ∀ p ∈ S₀, p.2.IsLC)
    (hKΦ : ∀ k ∈ K, k < Φ) (hKscrut : ∀ y ∈ scrut.tyFreeVars, y ∈ K)
    (hKbr : ∀ y ∈ Expr.tyFreeVars.BranchList.tyFreeVars branches, y ∈ K)
    (hKfix : ∀ k ∈ K, S₀.onTy (.fvar k) = .fvar k)
    (hscrut_decl : TypeOfHM (S₀.onCtx ctx) scrut scrutTy)
    (hne : branches ≠ [])
    (hbranches_decl : ∀ br ∈ branches,
      TypeOfMatchBranch (S₀.onCtx ctx)
        (br.1, br.2) scrutTy τ₀) :
    ∃ Φ' S τ R,
      Infer Φ ctx (.match_ scrut branches) Φ' S τ ∧
      Subst.AgreesBelow Φ S₀ (S ++ R) ∧
      Eq τ₀ (R.onTy τ) ∧ (∀ p ∈ R, p.2.IsLC) ∧
      (∀ k ∈ K, R.onTy (.fvar k) = .fvar k) ∧
      (∀ p ∈ S, p.1 ∉ K) := by
  obtain ⟨Φ₁, S₁, τs, R₁, hInferScrut, hAgreeScrut, hAgreeScrutTy, hR₁lc, hR₁K, hS₁K⟩ :=
    ihscrut K hwf hbelow hS₀ hKΦ hKscrut hKfix hscrut_decl
  have hΦscrut : ∀ y ∈ scrut.tyFreeVars, y < Φ := fun y hy => hKΦ y (hKscrut y hy)
  have hfle : Φ ≤ Φ₁ := Infer.frontier_le hInferScrut
  have hS₁lc : ∀ p ∈ S₁, p.2.IsLC := (Infer.lc hInferScrut hwf).2
  have hτs_lc : τs.IsLC := (Infer.lc hInferScrut hwf).1
  have hτs_bel : Ty.BelowFvars Φ₁ τs := (Infer.belowFvars hInferScrut hbelow hΦscrut).1
  have hscrut_sbel : ∀ p ∈ S₁, Ty.BelowFvars Φ₁ p.2 :=
    (Infer.belowFvars hInferScrut hbelow hΦscrut).2
  have hctxWF₁ : CtxWF (S₁.onCtx ctx) := Subst.onCtx_wf hS₁lc hwf
  have hctxBelow₁ : CtxBelow Φ₁ (S₁.onCtx ctx) := Subst.onCtx_below hscrut_sbel hfle hbelow
  have hctxBelow₁' : CtxBelow (Φ₁ + 1) (S₁.onCtx ctx) :=
    fun M hM => (hctxBelow₁ M hM).mono (by omega)
  have hKΦ₁ : ∀ k ∈ K, k < Φ₁ := fun k hk => lt_of_lt_of_le (hKΦ k hk) hfle
  have hKΦ₁' : ∀ k ∈ K, k < Φ₁ + 1 := fun k hk => Nat.lt_succ_of_lt (hKΦ₁ k hk)
  have hτs_bel' : Ty.BelowFvars (Φ₁ + 1) τs := hτs_bel.mono (by omega)
  have hρlc : (Ty.fvar Φ₁).IsLC := ContainsBvarsUpTo.fvar
  have hρbel : Ty.BelowFvars (Φ₁ + 1) (.fvar Φ₁) := Ty.BelowFvars.fvar (by omega)
  obtain ⟨hd, tl, hcons⟩ := List.exists_cons_of_ne_nil hne
  have hhd : hd ∈ branches := by rw [hcons]; exact List.mem_cons_self ..
  have hτ₀_lc : τ₀.IsLC :=
    TypeOfMatchBranch.regular (hbranches_decl hd hhd)
  obtain ⟨R₁', hR₁'lc, hR₁'K, hR₁'Φ₁, hR₁'below⟩ :=
    exists_residual_at_fresh (Φ := Φ₁) (R := R₁) (K := K) hR₁lc hτ₀_lc hR₁K hKΦ₁
  have hR₁'agreeR₁ : Subst.AgreesBelow Φ₁ R₁' R₁ := by
    intro v hv
    rw [hR₁'below v hv]
  have hAgreeScrut' : Subst.AgreesBelow Φ (S₁ ++ R₁) S₀ := by
    intro v hv
    exact Eq.symm (hAgreeScrut v hv)
  have hctxEq : (R₁'.onCtx (S₁.onCtx ctx)) = (S₀.onCtx ctx) := by
    calc
      (R₁'.onCtx (S₁.onCtx ctx)) = (R₁.onCtx (S₁.onCtx ctx)) :=
        Subst.onCtx_congr hR₁'agreeR₁ hctxBelow₁
      _ = (S₀.onCtx ctx) := by
        rw [← Subst.onCtx_append]
        exact Subst.onCtx_congr hAgreeScrut' hbelow
  have hscrutEq' :  (R₁'.onTy τs) =  scrutTy := by
    calc
       (R₁'.onTy τs) =  (R₁.onTy τs) :=
        Subst.onTy_congr hR₁'agreeR₁ hτs_bel
      _ =  scrutTy := Eq.symm hAgreeScrutTy
  have hbrs' : ∀ br ∈ branches, TypeOfMatchBranch (R₁'.onCtx (S₁.onCtx ctx))
      (br.1, br.2)
      ( (R₁'.onTy τs)) ( (R₁'.onTy (.fvar Φ₁))) := by
    intro br hbr
    rcases br with ⟨pat, body⟩
    cases hbranches_decl ⟨pat, body⟩ hbr with
    | mk hspec hctxeq hbodyDecl =>
        rename_i ctor c n tyArgs instContents
        rw [hctxeq] at hbodyDecl
        have hbody' :
            TypeOfHM
              { (R₁'.onCtx (S₁.onCtx ctx)) with
                env := instContents.map PolyTy.mkTrivial
                  ++ (R₁'.onCtx (S₁.onCtx ctx)).env }
              body ( (R₁'.onTy (.fvar Φ₁))) := by
          rw [hctxEq, hR₁'Φ₁]
          exact hbodyDecl
        have hspec' : BranchCtorSpec (R₁'.onCtx (S₁.onCtx ctx)).ctors c n
            (R₁'.onTy τs) ctor tyArgs instContents :=
          ⟨by simpa [Subst.onCtx] using hspec.lookup,
            hscrutEq'.trans hspec.scrut_eq, hspec.arity, hspec.bind_count, hspec.fields⟩
        exact TypeOfMatchBranch.mk
          ⟨hspec'.lookup, hspec'.scrut_eq, hspec'.arity, hspec'.bind_count, hspec'.fields⟩
          rfl hbody'
    | wildcard hbodyDecl =>
        have hbody' : TypeOfHM (R₁'.onCtx (S₁.onCtx ctx)) body
            ( (R₁'.onTy (.fvar Φ₁))) := by
          rw [hctxEq, hR₁'Φ₁]
          exact hbodyDecl
        exact TypeOfMatchBranch.wildcard hbody'
  obtain ⟨Φ₂, S₂, R₂, hInferBrs, hAgreeBrs, hR₂lc, hR₂K, hS₂K⟩ :=
    @InferBranches.complete branches (Φ₁ + 1) (S₁.onCtx ctx) τs (.fvar Φ₁) R₁' K
      ihbranches hctxWF₁ hctxBelow₁' hτs_lc hτs_bel' hρlc hρbel hR₁'lc hKΦ₁' hKbr hR₁'K hbrs'
  have hAgreeBrs₁ : Subst.AgreesBelow Φ₁ R₁ (S₂ ++ R₂) := by
    intro v hv
    exact Eq.trans (Eq.symm (hR₁'agreeR₁ v hv)) (hAgreeBrs v (Nat.lt_succ_of_lt hv))
  have hAgree : Subst.AgreesBelow Φ S₀ ((S₁ ++ S₂) ++ R₂) :=
    @Subst.AgreesBelow.trans_append Φ Φ₁ S₀ S₁ R₁ S₂ R₂ hfle hAgreeScrut hscrut_sbel hAgreeBrs₁
  have hAgreeOut : Eq τ₀ (R₂.onTy (S₂.onTy (.fvar Φ₁))) := by
    have h := hAgreeBrs Φ₁ (by omega)
    rw [Subst.onTy_append] at h
    rwa [hR₁'Φ₁] at h
  refine ⟨Φ₂, S₁ ++ S₂, S₂.onTy (.fvar Φ₁), R₂,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact .match_ hInferScrut hne hInferBrs
  · simpa [List.append_assoc] using hAgree
  · exact hAgreeOut
  · exact hR₂lc
  · exact hR₂K
  · intro p hp
    rw [List.mem_append] at hp
    rcases hp with hp | hp
    · exact hS₁K p hp
    · exact hS₂K p hp

/-- Producer completeness for matches. -/
theorem Infer.complete_match {scrut : Expr} {branches : List (MatchPattern × Expr)}
    (ihscrut : Infer.CompleteAt scrut)
    (ihbranches : ∀ br ∈ branches, Infer.CompleteAt br.2) :
    Infer.CompleteAt (.match_ scrut branches) := by
  intro Φ ctx S₀ τ₀ K hwf hbelow hS₀ hKΦ hKtv hKfix hty
  cases hty with
  | match_ hscrut_ty hbrs_ne hbrs =>
    rename_i scrutTy
    have hKscrut : ∀ y ∈ scrut.tyFreeVars, y ∈ K := fun y hy =>
      hKtv y (by simpa [Expr.tyFreeVars] using (Or.inl hy))
    have hKbr : ∀ y ∈ Expr.tyFreeVars.BranchList.tyFreeVars branches, y ∈ K := fun y hy =>
      hKtv y (by simpa [Expr.tyFreeVars] using (Or.inr hy))
    have hne' : branches ≠ [] := by
      intro hb
      simp [hb] at hbrs_ne
    have hbrs_decl : ∀ br ∈ branches, TypeOfMatchBranch (S₀.onCtx ctx)
        (br.1, br.2) scrutTy τ₀ := by
      intro br hbr
      exact hbrs (br.1, br.2) (by simpa only [Prod.eta] using hbr)
    exact Infer.complete_match_aux ihscrut ihbranches hwf hbelow hS₀ hKΦ hKscrut hKbr hKfix
      hscrut_ty hne' hbrs_decl

/-! ### Recursive-group producer completeness (D2 monomorphic tier) -/

/-- Producer completeness for an all-monomorphic recursive-group thread.

    This is deliberately the D2 tier only: every input spec is a `.mono`, so
    no skolem/opened-RHS case is hidden here.  The declarative member premise
    is stated at the current ambient specialization; the returned residual is
    what transports that premise through each W/unification step.  This is the
    form consumed by the eventual `letRec` producer after it has constructed
    the initial recursive block and its declarative monotype witnesses. -/
theorem InferRecGroup.complete_mono
    {Φ : Nat} {ctx : Ctx} {bindings : List Expr} {specs : List RecSpec}
    {S₀ : Subst} {K : List Nat}
    (ih : ∀ e ∈ bindings, Infer.CompleteAt e)
    (hlen : bindings.length = specs.length)
    (hwf : CtxWF ctx) (hbelow : CtxBelow Φ ctx)
    (hS₀ : ∀ p ∈ S₀, p.2.IsLC)
    (hKΦ : ∀ k ∈ K, k < Φ)
    (hKtv : ∀ y ∈ Expr.tyFreeVars.RecGroup.tyFreeVars bindings, y ∈ K)
    (hKfix : ∀ k ∈ K, S₀.onTy (.fvar k) = .fvar k)
    (hspecLC : ∀ s ∈ specs, s.LC)
    (hspecBelow : ∀ s ∈ specs, ∀ τ, s = .mono τ → Ty.BelowFvars Φ τ)
    (hspecMono : ∀ s ∈ specs, ∃ τ, s = .mono τ)
    (hdecl : ∀ p ∈ bindings.zip specs, ∀ τ, p.2 = .mono τ →
      TypeOfHM (S₀.onCtx ctx) p.1
        ( (S₀.onTy τ))) :
    ∃ Φ' S R,
      InferRecGroup Φ ctx bindings specs Φ' S ∧
      Subst.AgreesBelow Φ S₀ (S ++ R) ∧
      (∀ p ∈ R, p.2.IsLC) ∧
      (∀ k ∈ K, R.onTy (.fvar k) = .fvar k) ∧
      (∀ p ∈ S, p.1 ∉ K) := by
  induction bindings generalizing Φ ctx specs S₀ hwf hbelow hS₀ hKΦ hKfix
    hspecLC hspecBelow hspecMono with
  | nil =>
    cases specs with
    | nil =>
      refine ⟨Φ, [], S₀, .nil, ?_, hS₀, hKfix, ?_⟩
      · intro v hv
        simp only [List.nil_append]
      · intro p hp
        simp at hp
    | cons s ss => simp at hlen
  | cons e rest ihrec =>
    cases specs with
    | nil => simp at hlen
    | cons s ss =>
      obtain ⟨τ, hs⟩ := hspecMono s List.mem_cons_self
      subst s
      have hrest_len : rest.length = ss.length := by simpa using hlen
      have hheadIH : Infer.CompleteAt e := ih e List.mem_cons_self
      have hrestIH : ∀ e' ∈ rest, Infer.CompleteAt e' := fun e' he' =>
        ih e' (List.mem_cons_of_mem _ he')
      have hKe : ∀ y ∈ e.tyFreeVars, y ∈ K := fun y hy =>
        hKtv y (by simp [Expr.tyFreeVars.RecGroup.tyFreeVars, hy])
      have hKrest : ∀ y ∈ Expr.tyFreeVars.RecGroup.tyFreeVars rest, y ∈ K := fun y hy =>
        hKtv y (by simp [Expr.tyFreeVars.RecGroup.tyFreeVars, hy])
      have hτbelow : Ty.BelowFvars Φ τ :=
        hspecBelow (.mono τ) List.mem_cons_self τ rfl
      have hτlc : τ.IsLC := by
        have := hspecLC (.mono τ) List.mem_cons_self
        simpa using this
      have hheadDecl : TypeOfHM (S₀.onCtx ctx) e
          ( (S₀.onTy τ)) :=
        hdecl (e, .mono τ) (by simp) τ rfl
      obtain ⟨Φ₁, S₁, τe, R₁, hInferE, hAgreeE, hAgreeTy,
          hR₁lc, hR₁K, hS₁K⟩ :=
        hheadIH K hwf hbelow hS₀ hKΦ hKe hKfix hheadDecl
      have hΦ₁ : Φ ≤ Φ₁ := Infer.frontier_le hInferE
      have hKΦ₁ : ∀ k ∈ K, k < Φ₁ := fun k hk =>
        lt_of_lt_of_le (hKΦ k hk) hΦ₁
      have hE_lc := Infer.lc hInferE hwf
      have hτeLC : τe.IsLC := hE_lc.1
      have hS₁lc : ∀ p ∈ S₁, p.2.IsLC := hE_lc.2
      have hE_below := Infer.belowFvars hInferE hbelow
        (fun y hy => hKΦ y (hKe y hy))
      have hτeBelow : Ty.BelowFvars Φ₁ τe := hE_below.1
      have hS₁Below : ∀ p ∈ S₁, Ty.BelowFvars Φ₁ p.2 := hE_below.2
      have hτAfterLC : (S₁.onTy τ).IsLC := Subst.onTy_lc hS₁lc hτlc
      have hTarget : Eq (S₀.onTy τ) (R₁.onTy (S₁.onTy τ)) := by
        simpa [Subst.onTy_append] using
          (Subst.onTy_congr hAgreeE hτbelow)
      have hUni : Unifies R₁ τe (S₁.onTy τ) := by
        apply Eq.trans hAgreeTy.symm
        exact hTarget
      obtain ⟨S₂, hS₂uni, hS₂K⟩ :=
        UnifyRel.complete_K hτeLC hτAfterLC hR₁lc hUni hR₁K
      obtain ⟨R₂, hR₂fac, hR₂lc, hR₂K⟩ :=
        UnifyRel.greatest_K hS₂uni R₁ hR₁lc hUni hR₁K
      have hS₂lc : ∀ p ∈ S₂, p.2.IsLC :=
        UnifyRel.lc hS₂uni hτeLC hτAfterLC
      have hτAfterBelow : Ty.BelowFvars Φ₁ (S₁.onTy τ) :=
        Subst.onTy_belowFvars hS₁Below (hτbelow.mono hΦ₁)
      have hS₂Below : ∀ p ∈ S₂, Ty.BelowFvars Φ₁ p.2 :=
        UnifyRel.belowFvars hS₂uni hτeBelow hτAfterBelow
      have hAgreeUni : Subst.AgreesBelow Φ₁ R₁ (S₂ ++ R₂) := by
        intro v hv
        rw [Subst.onTy_append]
        exact hR₂fac (.fvar v)
      have hAgreeHead : Subst.AgreesBelow Φ S₀ ((S₁ ++ S₂) ++ R₂) :=
        @Subst.AgreesBelow.trans_append Φ Φ₁ S₀ S₁ R₁ S₂ R₂
          hΦ₁ hAgreeE hS₁Below hAgreeUni
      have hctxWF : CtxWF (S₂.onCtx (S₁.onCtx ctx)) :=
        Subst.onCtx_wf hS₂lc (Subst.onCtx_wf hS₁lc hwf)
      have hctxBelow : CtxBelow Φ₁ (S₂.onCtx (S₁.onCtx ctx)) :=
        Subst.onCtx_below hS₂Below (le_refl _)
          (Subst.onCtx_below hS₁Below hΦ₁ hbelow)
      have hctxEq : (R₂.onCtx (S₂.onCtx (S₁.onCtx ctx))) =
          (S₀.onCtx ctx) := by
        rw [← Subst.onCtx_append]
        simpa [Subst.onCtx_append, List.append_assoc] using
          (Subst.onCtx_congr hAgreeHead hbelow).symm
      have hssLC : ∀ s' ∈ ss.map (RecSpec.onSubst (S₁ ++ S₂)), s'.LC := by
        intro s' hs'
        obtain ⟨s0, hs0, rfl⟩ := List.mem_map.mp hs'
        apply RecSpec.LC.onSubst
        intro p hp
        rcases List.mem_append.mp hp with hp | hp
        · exact hS₁lc p hp
        · exact hS₂lc p hp
        exact hspecLC s0 (List.mem_cons_of_mem _ hs0)
      have hssMono : ∀ s' ∈ ss.map (RecSpec.onSubst (S₁ ++ S₂)),
          ∃ τ', s' = .mono τ' := by
        intro s' hs'
        obtain ⟨s0, hs0, rfl⟩ := List.mem_map.mp hs'
        obtain ⟨τ0, hτ0⟩ := hspecMono s0 (List.mem_cons_of_mem _ hs0)
        subst s0
        exact ⟨(S₁ ++ S₂).onTy τ0, rfl⟩
      have hssBelow : ∀ s' ∈ ss.map (RecSpec.onSubst (S₁ ++ S₂)), ∀ τ',
          s' = .mono τ' → Ty.BelowFvars Φ₁ τ' := by
        intro s' hs' τ' hmono
        obtain ⟨s0, hs0, rfl⟩ := List.mem_map.mp hs'
        obtain ⟨τ0, hτ0⟩ := hspecMono s0 (List.mem_cons_of_mem _ hs0)
        subst s0
        simp only [RecSpec.onSubst] at hmono
        cases hmono
        apply Subst.onTy_belowFvars
        · intro p hp
          rcases List.mem_append.mp hp with hp | hp
          · exact (hS₁Below p hp).mono (le_refl _)
          · exact hS₂Below p hp
        · exact (hspecBelow (.mono τ0) (List.mem_cons_of_mem _ hs0) τ0 rfl).mono hΦ₁
      have hdeclTail : ∀ p ∈ rest.zip (ss.map (RecSpec.onSubst (S₁ ++ S₂))),
          ∀ τ', p.2 = .mono τ' →
          TypeOfHM (R₂.onCtx (S₂.onCtx (S₁.onCtx ctx))) p.1
            ( (R₂.onTy τ')) := by
        intro p hp τ' hmono
        rcases List.mem_zip_map_right hp with ⟨e', s0, hp0, rfl⟩
        obtain ⟨τ0, hτ0⟩ := hspecMono s0 (List.mem_cons_of_mem _ (List.of_mem_zip hp0).2)
        subst s0
        simp only [RecSpec.onSubst] at hmono
        cases hmono
        have hold : TypeOfHM (S₀.onCtx ctx) e'
            ( (S₀.onTy τ0)) :=
          hdecl (e', .mono τ0)
            (by rw [List.zip_cons_cons]; exact List.mem_cons_of_mem _ hp0) τ0 rfl
        rw [hctxEq]
        have htype : Eq (S₀.onTy τ0)
            (R₂.onTy ((S₁ ++ S₂).onTy τ0)) := by
          simpa [Subst.onTy_append] using
            (Subst.onTy_congr hAgreeHead
              ((hspecBelow (.mono τ0) (List.mem_cons_of_mem _ (List.of_mem_zip hp0).2)
                τ0 rfl)))
        rw [htype] at hold
        exact hold
      obtain ⟨Φ₂, S₃, R₃, hRest, hAgreeRest, hR₃lc, hR₃K, hS₃K⟩ :=
        ihrec (Φ := Φ₁) (ctx := S₂.onCtx (S₁.onCtx ctx))
          (specs := ss.map (RecSpec.onSubst (S₁ ++ S₂))) (S₀ := R₂)
          hrestIH (by simpa using hrest_len) hctxWF hctxBelow hR₂lc hKΦ₁ hKrest hR₂K
          hssLC hssBelow hssMono hdeclTail
      have hS₁₂Below : ∀ p ∈ S₁ ++ S₂, Ty.BelowFvars Φ₁ p.2 := by
        intro p hp
        rcases List.mem_append.mp hp with hp | hp
        · exact hS₁Below p hp
        · exact hS₂Below p hp
      have hAgree : Subst.AgreesBelow Φ S₀ (((S₁ ++ S₂) ++ S₃) ++ R₃) :=
        @Subst.AgreesBelow.trans_append Φ Φ₁ S₀ (S₁ ++ S₂) R₂ S₃ R₃
          hΦ₁ hAgreeHead hS₁₂Below hAgreeRest
      refine ⟨Φ₂, S₁ ++ S₂ ++ S₃, R₃, ?_, ?_, hR₃lc, hR₃K, ?_⟩
      · exact .cons hInferE hS₂uni hRest
      · simpa [List.append_assoc] using hAgree
      · intro p hp
        rw [List.mem_append, List.mem_append] at hp
        rcases hp with (hp | hp) | hp
        · exact hS₁K p hp
        · exact hS₂K p hp
        · exact hS₃K p hp

/-- Producer completeness for recursive groups.  The declarative all-monomorphic
    cut is first realised by `InferRecGroup.complete_mono`; the annotation
    ceiling is then reconstructed from its semantic generality witnesses. -/
theorem Infer.complete_letRec {anns : List (Option PolyTy)} {bindings : List Expr}
    {body : Expr}
    (ihbindings : ∀ e ∈ bindings, Infer.CompleteAt e)
    (ihbody : Infer.CompleteAt body) :
    Infer.CompleteAt (.letRec anns bindings body) := by
  intro Φ ctx S₀ τ₀ K hwf hbelow hS₀ hKΦ hKe hKfix hty
  cases hty with
  | letRec hwfD hlenD hlinkD hlcD hmonoD hceilingD hbodyCtxD hbodyD =>
      rename_i dspecs τsD Gdecl L
      subst hbodyCtxD
      have hKgrp : ∀ y ∈ Expr.tyFreeVars.RecGroup.tyFreeVars bindings, y ∈ K :=
        fun y hy => hKe y (by
          simp only [Expr.tyFreeVars, List.mem_append]
          exact Or.inl (Or.inr hy))
      have hKbody : ∀ y ∈ body.tyFreeVars, y ∈ K := fun y hy =>
        hKe y (by
          simp only [Expr.tyFreeVars, List.mem_append]
          exact Or.inr hy)
      have hlen_τsD : bindings.length = τsD.length := by
        simpa [List.length_map] using hlenD
      have hdspec_len : dspecs.length = bindings.length := by
        simpa [List.length_map] using hwfD.length.symm
      have hlen_ab : anns.length = bindings.length := by
        have ha := congrArg List.length hwfD.anns_eq
        simp only [List.length_map] at ha
        omega
      have hKrigid : ∀ y ∈ RecGroup.rigidVars anns bindings, y ∈ K := by
        intro y hy
        rcases List.mem_append.mp hy with hy | hy
        · exact hKe y (List.mem_append.mpr (Or.inl
            (List.mem_append.mpr (Or.inl hy))))
        · have hy' : y ∈ Expr.tyFreeVars.RecGroup.tyFreeVars bindings :=
            (mem_recGroup_tyFreeVars (bindings := bindings)).mpr hy
          exact hKe y (List.mem_append.mpr (Or.inl
            (List.mem_append.mpr (Or.inr hy'))))
      let XavoidPool :=
        (L ++ Gdecl ++ dspecs.flatMap RecSpec.monoFreeVars ++
          (S₀.onCtx ctx).env.freeVars ++ K) ++ Ty.freeVarsList τsD
      obtain ⟨Xs, hXlen, hXnodup, hXavoid⟩ := exists_fresh_names
        XavoidPool Gdecl.length
      have hXL : ∀ x ∈ Xs, x ∉ L := fun x hx hc => hXavoid x hx (by
        dsimp [XavoidPool]
        simp only [List.mem_append]
        tauto)
      have hXG : ∀ g ∈ Gdecl, g ∉ Xs := fun g hg hc => hXavoid g hc (by
        dsimp [XavoidPool]
        simp only [List.mem_append]
        tauto)
      have hXτs : ∀ x ∈ Xs, ∀ τ, RecSpec.mono τ ∈ dspecs → x ∉ τ.freeVars :=
        fun x hx τ hτ hc => hXavoid x hx (by
          dsimp [XavoidPool]
          simp only [List.mem_append]
          exact Or.inl (Or.inl (Or.inl
            (Or.inr (List.mem_flatMap.mpr ⟨RecSpec.mono τ, hτ, hc⟩)))))
      have hXτsD : ∀ x ∈ Xs, ∀ τ ∈ τsD, x ∉ τ.freeVars := by
        intro x hx τ hτ hc
        exact hXavoid x hx (by
          dsimp [XavoidPool]
          exact List.mem_append.mpr (Or.inr (Ty.mem_freeVarsList_of_mem hτ hc)))
      have hXenv : ∀ x ∈ Xs, x ∉ (S₀.onCtx ctx).env.freeVars := fun x hx hc =>
        hXavoid x hx (by
          dsimp [XavoidPool]
          simp only [List.mem_append]
          tauto)
      have hXK : ∀ x ∈ Xs, x ∉ K := fun x hx hc => hXavoid x hx (by
        dsimp [XavoidPool]
        simp only [List.mem_append]
        tauto)
      have hXfresh : FreshNames L Gdecl.length Xs := ⟨hXlen, hXnodup, hXL⟩
      have hXrigid : ∀ x ∈ Xs, x ∉ RecGroup.rigidVars anns bindings :=
        fun x hx hc => hXK x hx (hKrigid x hc)
      set vs : List Ty := τsD.map (fun τ => Ty.renameG Gdecl Xs τ) with hvs_def
      have hvs_len : vs.length = bindings.length := by
        rw [hvs_def, List.length_map]
        exact hlen_τsD.symm
      have hvs_lc : ∀ t ∈ vs, t.IsLC := by
        intro t ht
        rw [hvs_def] at ht
        obtain ⟨τ, hτ, rfl⟩ := List.mem_map.mp ht
        change (Subst.onTy (Gdecl.zip (Xs.map (Ty.fvar ·))) τ).IsLC
        exact Subst.onTy_lc (fun p hp => by
          obtain ⟨w, _, hw⟩ := List.mem_map.mp (List.of_mem_zip hp).2
          rw [← hw]
          exact ContainsBvarsUpTo.fvar) (hlcD τ hτ)
      obtain ⟨R₀, hR₀lc, hR₀K, hR₀ag, hR₀block⟩ :=
        exists_recgroup_residual (Φ := Φ) (n := bindings.length)
          (S₀ := S₀) (vs := vs) (K := K)
          hvs_len hS₀ hvs_lc hKΦ hKfix
      have hR₀blockj : ∀ j (hj : j < bindings.length),
          R₀.onTy (Ty.fvar (Φ + j)) =
            Ty.renameG Gdecl Xs (τsD[j]'(by rw [← hlen_τsD]; exact hj)) := by
        intro j hj
        have hjT : j < τsD.length := by rw [← hlen_τsD]; exact hj
        have h := congrArg (fun l => l[j]?) hR₀block
        change (List.map R₀.onTy
          (List.map Ty.fvar (freshVars Φ bindings.length)))[j]? = vs[j]? at h
        rw [List.getElem?_map, List.getElem?_map] at h
        have hfj : (freshVars Φ bindings.length)[j]'(by
            simpa [freshVars_length] using hj) = Φ + j := by
          simp only [freshVars, List.getElem_map, List.getElem_range]
        rw [List.getElem?_eq_getElem (by simpa [freshVars_length] using hj), hfj] at h
        rw [hvs_def, List.getElem?_map, List.getElem?_eq_getElem hjT] at h
        exact Option.some.inj h
      set groupCtx : Ctx := { ctx with
        env := (RecSpec.init Φ anns).map (RecSpec.rhsEntry [] []) ++ ctx.env } with
        hgroupCtx_def
      have hinitSpec : ∀ s ∈ RecSpec.init Φ anns,
          ∃ j, j < anns.length ∧ s = RecSpec.mono (.fvar (Φ + j)) := by
        intro s hs
        rcases List.mem_iff_getElem.mp hs with ⟨j, hj, rfl⟩
        have hjA : j < anns.length := by
          rw [RecSpec.init_length] at hj
          exact hj
        have hget : (RecSpec.init Φ anns)[j] =
            RecSpec.mono (.fvar (Φ + j)) := by
          have heq := List.getElem?_eq_getElem hj
          rw [RecSpec.init_getElem? Φ anns j,
            List.getElem?_eq_getElem hjA] at heq
          injection heq with heq'
          exact heq'.symm
        exact ⟨j, hjA, hget⟩
      have hinitLC : ∀ s ∈ RecSpec.init Φ anns, s.LC := by
        intro s hs
        obtain ⟨j, _, rfl⟩ := hinitSpec s hs
        exact ContainsBvarsUpTo.fvar
      have hinitB : ∀ s ∈ RecSpec.init Φ anns, ∀ τm,
          s = RecSpec.mono τm → Ty.BelowFvars (Φ + bindings.length) τm := by
        intro s hs τm hτm
        obtain ⟨j, hj, hsj⟩ := hinitSpec s hs
        rw [hsj] at hτm
        injection hτm with heq
        subst τm
        exact Ty.BelowFvars.fvar (by rw [hlen_ab] at hj; omega)
      have hinitMono : ∀ s ∈ RecSpec.init Φ anns, ∃ τ, s = .mono τ := by
        intro s hs
        obtain ⟨j, _, hsj⟩ := hinitSpec s hs
        exact ⟨Ty.fvar (Φ + j), hsj⟩
      have hctxgWF : CtxWF groupCtx := by
        intro M hM
        rcases List.mem_append.mp hM with hM | hM
        · obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hM
          exact RecSpec.rhsEntry_nil_wf (hinitLC s hs)
        · exact hwf M hM
      have hctxgBelow : CtxBelow (Φ + bindings.length) groupCtx := by
        intro M hM
        rcases List.mem_append.mp hM with hM | hM
        · obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hM
          obtain ⟨τ, rfl⟩ := hinitMono s hs
          exact hinitB _ hs _ rfl
        · exact (hbelow M hM).mono (by omega)
      have hMonoMem : ∀ p ∈ bindings.zip (RecSpec.init Φ anns), ∀ τm,
          p.2 = RecSpec.mono τm →
          TypeOfHM (R₀.onCtx groupCtx) p.1
            ( (R₀.onTy τm)) := by
        intro p hp τm hτm
        rcases List.mem_iff_getElem.mp hp with ⟨j, hjp, hpeq⟩
        have hjB : j < bindings.length := by
          rw [List.length_zip] at hjp
          exact lt_of_lt_of_le hjp (min_le_left _ _)
        have hjI : j < (RecSpec.init Φ anns).length := by
          rw [List.length_zip] at hjp
          exact lt_of_lt_of_le hjp (min_le_right _ _)
        have hpeq' : (bindings[j]'hjB, (RecSpec.init Φ anns)[j]'hjI) = p := by
          rw [List.getElem_zip] at hpeq
          exact hpeq
        have hjA : j < anns.length := by rw [hlen_ab]; exact hjB
        have hinit_j : (RecSpec.init Φ anns)[j]'hjI =
            RecSpec.mono (Ty.fvar (Φ + j)) := by
          have hg := RecSpec.init_getElem? Φ anns j
          rw [List.getElem?_eq_getElem hjI, List.getElem?_eq_getElem hjA] at hg
          simpa using hg
        have hτm' : τm = Ty.fvar (Φ + j) := by
          have hf := congrArg Prod.snd hpeq'
          exact (RecSpec.mono.inj (by simpa [hinit_j, hτm] using hf)).symm
        subst hτm'
        have hjT : j < τsD.length := by rw [← hlen_τsD]; exact hjB
        have hjBE : j < bindings.length := hjB
        let bE : Expr := bindings[j]'hjBE
        let tD : Ty := τsD[j]'hjT
        have hmemD : (bE, tD) ∈ bindings.zip τsD :=
          getElem_mem_zip j hjBE hjT
        have hdecl0 := hmonoD Xs hXfresh (bE, tD) hmemD
        have hdeclE := hdecl0
        have hctxE :
            (RecSpecs.rhsCtx (S₀.onCtx ctx)
              (τsD.map RecSpec.mono) Gdecl Xs) =
            (R₀.onCtx groupCtx) := by
          simp only [RecSpecs.rhsCtx, groupCtx, Subst.onCtx, Subst.onEnv,
            List.map_append]
          congr 1
          · rw [List.map_map, List.map_map]
            congr 1
            · refine List.ext_getElem ?_ (fun k hk1 hk2 => ?_)
              · simp only [List.length_map, RecSpec.init_length]
                rw [hlen_ab, ← hlen_τsD]
              have hkT : k < τsD.length := by
                simp only [List.length_map, RecSpec.init_length] at hk2
                rw [hlen_ab] at hk2
                rwa [← hlen_τsD]
              have hkB : k < bindings.length := by rwa [hlen_τsD]
              have hkA : k < anns.length := by rwa [hlen_ab]
              have hinit_k : (RecSpec.init Φ anns)[k]'(by
                  simpa [RecSpec.init_length] using hkA) =
                  RecSpec.mono (Ty.fvar (Φ + k)) := by
                have hg := RecSpec.init_getElem? Φ anns k
                rw [List.getElem?_eq_getElem (by
                    simpa [RecSpec.init_length] using hkA),
                  List.getElem?_eq_getElem hkA] at hg
                simpa using hg
              have hblk := hR₀blockj k hkB
              have hblkE :
                  PolyTy.mkTrivial (Ty.renameG Gdecl Xs (τsD[k]'hkT)) =
                  PolyTy.mkTrivial (R₀.onTy (Ty.fvar (Φ + k))) := by
                exact congrArg PolyTy.mkTrivial hblk.symm
              simp only [List.getElem_map, Function.comp_apply, RecSpec.rhsEntry,
                hinit_k, Subst.onPolyTy, Ty.renameG_nil_pool, PolyTy.mkTrivial]
              exact hblkE
            · refine List.ext_getElem (by simp) (fun k hk1 hk2 => ?_)
              have hklen : k < ctx.env.length := by simpa using hk2
              have hMem : ctx.env[k]'hklen ∈ ctx.env := List.getElem_mem hklen
              simp only [List.getElem_map, Function.comp_apply, Subst.onPolyTy]
              refine congrArg₂ PolyTy.mk rfl ?_
              exact Subst.onTy_congr
                (fun v hv => Eq.symm (hR₀ag v hv))
                (hbelow _ hMem)
        have htyE :
              (Ty.renameG Gdecl Xs (τsD[j]'hjT)) =
             (R₀.onTy (Ty.fvar (Φ + j))) :=
          (hR₀blockj j hjB).symm
        rw [hctxE, htyE] at hdeclE
        have hp1 : p.1 = bindings[j]'hjB := (congrArg Prod.fst hpeq').symm
        have hbE : bE = (bindings[j]'hjB) := by
          simp [bE]
        rw [hbE, ← hp1] at hdeclE
        exact hdeclE
      have hKΦg : ∀ k ∈ K, k < Φ + bindings.length := fun k hk => by
        have := hKΦ k hk
        omega
      obtain ⟨Φ₁, S₁, Rg, hgroup, hAgreeGroup, hRglc, hRgK, hS₁K⟩ :=
        InferRecGroup.complete_mono (Φ := Φ + bindings.length)
          (ctx := groupCtx) (bindings := bindings)
          (specs := RecSpec.init Φ anns) (S₀ := R₀) (K := K)
          ihbindings (by simpa [RecSpec.init_length, hlen_ab])
          hctxgWF hctxgBelow hR₀lc hKΦg hKgrp hR₀K hinitLC hinitB hinitMono hMonoMem
      have hAgreeTier : Subst.AgreesBelow Φ S₀ (S₁ ++ Rg) := by
        intro v hv
        rw [← hR₀ag v hv]
        exact hAgreeGroup v (by omega)
      have hgle : Φ + bindings.length ≤ Φ₁ := InferRecGroup.frontier_le hgroup
      have hS₁lc : ∀ p ∈ S₁, p.2.IsLC :=
        InferRecGroup.lc hgroup hctxgWF hinitLC
      have htfv_below : ∀ y ∈ Expr.tyFreeVars.RecGroup.tyFreeVars bindings,
          y < Φ + bindings.length := fun y hy => by
        have := hKΦ y (hKgrp y hy)
        omega
      have hinit_bel : ∀ s ∈ RecSpec.init Φ anns,
          RecSpec.BelowFvars (Φ + bindings.length) s := by
        intro s hs
        obtain ⟨τ, rfl⟩ := hinitMono s hs
        exact hinitB _ hs _ rfl
      have hS₁_bel : ∀ p ∈ S₁, Ty.BelowFvars Φ₁ p.2 :=
        InferRecGroup.belowFvars hgroup hctxgBelow hinit_bel htfv_below
      have hKΦ₁ : ∀ k ∈ K, k < Φ₁ := fun k hk =>
        lt_of_lt_of_le (hKΦg k hk) hgle
      have hrigidBelow : ∀ x ∈ RecGroup.rigidVars anns bindings, x < Φ₁ :=
        fun x hx => hKΦ₁ x (hKrigid x hx)
      set specs1 := (RecSpec.init Φ anns).map (RecSpec.onSubst S₁) with
        hspecs1
      have hspecs1LC : ∀ s ∈ specs1, s.LC := by
        intro s hs
        rw [hspecs1] at hs
        obtain ⟨s₀, hs₀, rfl⟩ := List.mem_map.mp hs
        exact RecSpec.LC.onSubst hS₁lc (hinitLC s₀ hs₀)
      have hspecs1Below : ∀ s ∈ specs1, s.BelowFvars Φ₁ := by
        intro s hs
        rw [hspecs1] at hs
        obtain ⟨s₀, hs₀, rfl⟩ := List.mem_map.mp hs
        exact RecSpec.BelowFvars.onSubst hS₁_bel
          ((hinit_bel s₀ hs₀).mono hgle)
      set G := genGroupVars (RecGroup.rigidVars anns bindings) (S₁.onCtx ctx).env
        (RecSpecs.monoTys specs1) with hG
      have hannsWF : ∀ σ, some σ ∈ anns → σ.WF := by
        intro σ hσ
        have hσe : some σ ∈ anns := hσ
        rw [← hwfD.anns_eq] at hσe
        obtain ⟨s, hs, hsann⟩ := List.mem_map.mp hσe
        cases s with
        | mono t => simp [RecSpec.ann] at hsann
        | poly σ₀ =>
            have heq : σ₀ =  σ := by
              simpa [RecSpec.ann] using Option.some.inj hsann
            have hσewf : ( σ).WF := by
              rw [← heq]
              exact hwfD.poly_wf σ₀ hs
            exact hσewf
      have hdlc : ∀ τ, RecSpec.mono τ ∈ dspecs → τ.IsLC := by
        intro τ hτ
        exact hwfD.mono_lc τ hτ
      have hanns_eq :
          dspecs.map RecSpec.ann = anns := by
        simpa [hwfD.anns_eq]
      have hctxS₁ : (Rg.onCtx (S₁.onCtx ctx)) =
          (S₀.onCtx ctx) := by
        rw [← Subst.onCtx_append]
        exact (Subst.onCtx_congr hAgreeTier hbelow).symm
      have hGnodup : G.Nodup := by
        rw [hG]
        exact genGroupVars_nodup
      have hGrigid : ∀ g ∈ G, g ∉ RecGroup.rigidVars anns bindings := by
        intro g hg
        rw [hG] at hg
        simp only [genGroupVars, List.mem_filter, Bool.and_eq_true,
          Bool.not_eq_eq_eq_not, Bool.not_true, List.contains_eq_mem,
          decide_eq_false_iff_not] at hg
        exact hg.2.2
      have hσfix : ∀ σ, some σ ∈ anns → Rg.onPolyTy σ = σ := by
        intro σ hσ
        simp only [Subst.onPolyTy]
        rw [Subst.onTy_eq_self_of_fixes (fun v hv => hRgK v (hKe v (List.mem_append.mpr (Or.inl
          (List.mem_append.mpr (Or.inl (Expr.scheme_body_mem_annList_tyFreeVars hσ hv)))))))]
      have hconnAll : ∀ (j : Nat) (hj : j < bindings.length),
        Subst.onTy (Rg)
            ( (S₁.onTy (Ty.fvar (Φ + j))))
          = Ty.renameG Gdecl Xs
              ( (τsD[j]'(by rw [← hlen_τsD]; exact hj))) := by
        intro j hj
        have hjT : j < τsD.length := by rw [← hlen_τsD]; exact hj
        have hblockAgree : Eq (R₀.onTy (Ty.fvar (Φ + j)))
            (Rg.onTy (S₁.onTy (Ty.fvar (Φ + j)))) := by
          rw [← Subst.onTy_append]
          exact hAgreeGroup (Φ + j) (by omega)
        calc
           (Rg.onTy (S₁.onTy (Ty.fvar (Φ + j))))
              =  (R₀.onTy (Ty.fvar (Φ + j))) := hblockAgree.symm
          _ = Ty.renameG Gdecl Xs ( (τsD[j]'hjT)) := by
            rw [hR₀blockj j hj]
      have hconnB : ∀ (j : Nat) (hj : j < dspecs.length) (τdecl : Ty),
          dspecs[j]'hj = RecSpec.mono τdecl →
        Subst.onTy (Rg)
            ( (S₁.onTy (Ty.fvar (Φ + j))))
          = Ty.renameG Gdecl Xs ( τdecl) := by
        intro j hj τdecl hτdecl
        have hjl : j < bindings.length := by
          rw [← hdspec_len]
          exact hj
        have hjT : j < τsD.length := by rw [← hlen_τsD]; exact hjl
        have hlinkτ : τdecl = τsD[j]'hjT := by
          have hmemD : (RecSpec.mono τdecl, τsD[j]'hjT) ∈ dspecs.zip τsD := by
            simpa [hτdecl] using (getElem_mem_zip j hj hjT)
          exact (hlinkD (RecSpec.mono τdecl, τsD[j]'hjT) hmemD τdecl rfl).symm
        simpa [hlinkτ] using hconnAll j hjl
      set Rer : Subst :=
        Rg with hRer_def
      have hRerlc : ∀ p ∈ Rer, p.2.IsLC := by
        simpa [Rer] using hRglc
      have hgenInit : CeilingGenInv G Rg anns specs1 := by
        intro ann spec hp
        cases ann with
        | none => cases spec <;> trivial
        | some σ =>
          cases spec with
          | poly σ' =>
            rcases List.mem_iff_getElem.mp hp with ⟨j, hjp, hpeq⟩
            have hjS : j < specs1.length := by
              rw [List.length_zip] at hjp
              exact lt_of_lt_of_le hjp (min_le_right _ _)
            have hjA : j < anns.length := by
              rw [List.length_zip] at hjp
              exact lt_of_lt_of_le hjp (min_le_left _ _)
            rw [List.getElem_zip] at hpeq
            have hspecj : specs1[j]'hjS = RecSpec.poly σ' := congrArg Prod.snd hpeq
            have hinitj : (RecSpec.init Φ anns)[j]'(by
                simpa [RecSpec.init_length] using hjA) =
                RecSpec.mono (Ty.fvar (Φ + j)) := by
              have hg := RecSpec.init_getElem? Φ anns j
              rw [List.getElem?_eq_getElem (by
                simpa [RecSpec.init_length] using hjA),
                List.getElem?_eq_getElem hjA] at hg
              simpa using hg
            have hs1j : specs1[j]'hjS =
                RecSpec.mono (S₁.onTy (Ty.fvar (Φ + j))) := by
              simp only [specs1, List.getElem_map, hinitj, RecSpec.onSubst]
            rw [hs1j] at hspecj
            simp at hspecj
          | mono τinf =>
            rcases List.mem_iff_getElem.mp hp with ⟨j, hjp, hpeq⟩
            have hjA : j < anns.length := by
              rw [List.length_zip] at hjp
              exact lt_of_lt_of_le hjp (min_le_left _ _)
            have hjS : j < specs1.length := by
              rw [List.length_zip] at hjp
              exact lt_of_lt_of_le hjp (min_le_right _ _)
            rw [List.getElem_zip] at hpeq
            have hannj : anns[j]'hjA = some σ := congrArg Prod.fst hpeq
            have hspecj : specs1[j]'hjS = RecSpec.mono τinf := congrArg Prod.snd hpeq
            have hjB : j < bindings.length := by rw [← hlen_ab]; exact hjA
            have hjT : j < τsD.length := by rw [← hlen_τsD]; exact hjB
            have hinitj : (RecSpec.init Φ anns)[j]'(by
                simpa [RecSpec.init_length] using hjA) =
                RecSpec.mono (Ty.fvar (Φ + j)) := by
              have hg := RecSpec.init_getElem? Φ anns j
              rw [List.getElem?_eq_getElem (by
                simpa [RecSpec.init_length] using hjA),
                List.getElem?_eq_getElem hjA] at hg
              simpa using hg
            have hτinf : τinf = S₁.onTy (Ty.fvar (Φ + j)) := by
              have hs1j : specs1[j]'hjS =
                  RecSpec.mono (S₁.onTy (Ty.fvar (Φ + j))) := by
                simp only [specs1, List.getElem_map, hinitj, RecSpec.onSubst]
              exact RecSpec.mono.inj (hspecj.symm.trans hs1j)
            subst τinf
            have hτalgMem : RecSpec.mono (S₁.onTy (Ty.fvar (Φ + j))) ∈ specs1 :=
              hspecj ▸ List.getElem_mem hjS
            have hτDmem : τsD[j]'hjT ∈ τsD := List.getElem_mem hjT
            have hceilMem :
                (some ( σ), RecSpec.mono (τsD[j]'hjT)) ∈
                  (anns).zip
                    (τsD.map RecSpec.mono) := by
              have hm := getElem_mem_zip
                (as := anns)
                (bs := τsD.map RecSpec.mono) j (by simpa using hjA) (by simpa using hjT)
              simpa only [List.getElem_map, hannj, Option.map_some] using hm
            have hdeclGen := hceilingD.of_mem_zip hceilMem
            have hdeclGen' :
                ( (PolyTy.genGroup Gdecl (τsD[j]'hjT))).Generalizes
                  ( σ) := by
              exact hdeclGen
            have hτalgLC : (S₁.onTy (Ty.fvar (Φ + j))).IsLC :=
              Subst.onTy_lc hS₁lc ContainsBvarsUpTo.fvar
            have hconnj : Rer.onTy
                  ( (S₁.onTy (Ty.fvar (Φ + j)))) =
                Ty.renameG Gdecl Xs ( (τsD[j]'hjT)) := by
              simpa [hRer_def] using hconnAll j hjB
            have hXinf : ∀ x ∈ Xs, x ∉
                (Rer.onPolyTy (PolyTy.genGroup G
                  ( (S₁.onTy (Ty.fvar (Φ + j)))))).body.freeVars := by
              intro x hx hmem
              change x ∈ (Rer.onTy (Ty.closeOver (Ty.genFilter G
                ( (S₁.onTy (Ty.fvar (Φ + j)))))
                ( (S₁.onTy (Ty.fvar (Φ + j)))))).freeVars at hmem
              obtain ⟨v, hv, hxv⟩ := Ty.mem_freeVars_onTy_iff.mp hmem
              have hvτ : v ∈ (
                  (S₁.onTy (Ty.fvar (Φ + j)))).freeVars :=
                Ty.freeVars_closeOver_subset hv
              have hvτ' : v ∈ (S₁.onTy (Ty.fvar (Φ + j))).freeVars :=
                hvτ
              have hvG : v ∉ G := by
                intro hvg
                exact Ty.not_mem_closeOver_freeVars
                  (by simp only [Ty.genFilter, List.mem_filter, decide_eq_true_eq]
                      exact ⟨hvg, hvτ⟩) hv
              have hvMono : v ∈ Ty.freeVarsList (RecSpecs.monoTys specs1) :=
                mem_freeVarsList_monoTys (mem_monoTys_of_mem_solved hτalgMem) hvτ'
              have hcase : v ∈ (S₁.onCtx ctx).env.freeVars ∨
                  v ∈ RecGroup.rigidVars anns bindings := by
                by_contra hcon
                push_neg at hcon
                apply hvG
                rw [hG]
                simp only [genGroupVars, List.mem_filter, Bool.and_eq_true,
                  Bool.not_eq_eq_eq_not, Bool.not_true, List.contains_eq_mem,
                  decide_eq_false_iff_not]
                exact ⟨hvMono, hcon.1, hcon.2⟩
              rcases hcase with henv | hrigid
              · obtain ⟨pt, hpt, hvpt⟩ := Env.mem_freeVars_iff.mp henv
                have hxv' : x ∈ (Rg.onTy (Ty.fvar v)).freeVars := by
                  have heq : Rer.onTy (Ty.fvar v) =
                       (Rg.onTy (Ty.fvar v)) := by
                    rfl
                  rw [heq] at hxv
                  exact hxv
                have hxOnTy : x ∈ (Rg.onTy pt.body).freeVars :=
                  Ty.mem_freeVars_onTy_iff.mpr ⟨v, hvpt, hxv'⟩
                have hm : Rg.onPolyTy pt ∈ (Rg.onCtx (S₁.onCtx ctx)).env := by
                  simp only [Subst.onCtx, Subst.onEnv]
                  exact List.mem_map.mpr ⟨pt, hpt, rfl⟩
                have hxEnv : x ∈ (Rg.onCtx (S₁.onCtx ctx)).env.freeVars :=
                  Env.mem_freeVars_iff.mpr ⟨Rg.onPolyTy pt, hm, hxOnTy⟩
                have hxEnvE : x ∈ ((Rg.onCtx (S₁.onCtx ctx))).env.freeVars :=
                  hxEnv
                have hc := congrArg Ctx.env hctxS₁
                have hxS₀E : x ∈ ((S₀.onCtx ctx)).env.freeVars := by
                  rwa [← hc]
                exact hXenv x hx
                  hxS₀E
              · have hfix : Rg.onTy (Ty.fvar v) = Ty.fvar v :=
                  hRgK v (hKrigid v hrigid)
                have hxv' : x ∈ (Rg.onTy (Ty.fvar v)).freeVars := by
                  have heq : Rer.onTy (Ty.fvar v) =
                       (Rg.onTy (Ty.fvar v)) := by
                    rfl
                  rw [heq] at hxv
                  exact hxv
                rw [hfix] at hxv'
                simp only [Ty.freeVars, List.mem_singleton] at hxv'
                exact hXrigid x hx (by rw [hxv']; exact hrigid)
            have halgDecl := genGroup_generalizes_renameG
              (Ginf := G) (G := Gdecl) (Xsfull := Xs)
              (τinf :=  (S₁.onTy (Ty.fvar (Φ + j))))
              (τdecl :=  (τsD[j]'hjT)) (R := Rer)
              hτalgLC
              (hlcD (τsD[j]'hjT) hτDmem) hRerlc
              hwfD.nodup hXlen hXnodup hXG
              (fun x hx hc => hXτsD x hx (τsD[j]'hjT) hτDmem
                hc)
              hconnj hXinf
            have halgDecl' :
                ( (Rg.onPolyTy
                  (PolyTy.genGroup G (S₁.onTy (Ty.fvar (Φ + j)))))).Generalizes
                ( (PolyTy.genGroup Gdecl (τsD[j]'hjT))) := by
              simpa [hRer_def] using halgDecl
            exact halgDecl'.trans hdeclGen'
      let P := K.filter (fun x => !G.contains x)
      have hPG : ∀ x ∈ P, x ∉ G := by
        intro x hx
        simp only [P, List.mem_filter, Bool.not_eq_eq_eq_not, Bool.not_true,
          List.contains_eq_mem, decide_eq_false_iff_not] at hx
        exact hx.2
      have hRgP : ∀ x ∈ P, Rg.onTy (.fvar x) = .fvar x := by
        intro x hx
        exact hRgK x (List.mem_of_mem_filter hx)
      have hRgrigid : ∀ x ∈ RecGroup.rigidVars anns bindings,
          Rg.onTy (.fvar x) = .fvar x := fun x hx => hRgK x (hKrigid x hx)
      have hPbelow : ∀ x ∈ P, x < Φ₁ := by
        intro x hx
        exact hKΦ₁ x (List.mem_of_mem_filter hx)
      have hGbelow : ∀ x ∈ G, x < Φ₁ := by
        intro x hx
        have hxmono : x ∈ Ty.freeVarsList (RecSpecs.monoTys specs1) := by
          rw [hG] at hx
          simp only [genGroupVars, List.mem_filter, Bool.and_eq_true] at hx
          exact hx.1
        have hfree : ∀ {tys : List Ty}, x ∈ Ty.freeVarsList tys →
            ∃ τ ∈ tys, x ∈ τ.freeVars := by
          intro tys hmem
          induction tys with
          | nil => simp [Ty.freeVarsList] at hmem
          | cons τ tys ih =>
              simp only [Ty.freeVarsList, List.mem_dedup,
                List.mem_append] at hmem
              rcases hmem with hmem | hmem
              · exact ⟨τ, List.mem_cons_self, hmem⟩
              · obtain ⟨τ', hτ', hxτ'⟩ := ih hmem
                exact ⟨τ', List.mem_cons_of_mem _ hτ', hxτ'⟩
        obtain ⟨τ, hτmono, hxτ⟩ := hfree hxmono
        simp only [RecSpecs.monoTys, RecSpec.monoTy?, List.mem_filterMap] at hτmono
        obtain ⟨s, hs, hsome⟩ := hτmono
        cases s with
        | mono τ' =>
            simp only [Option.some.injEq] at hsome
            subst τ'
            exact (hspecs1Below (.mono τ) hs).mem_lt x hxτ
        | poly σ => simp at hsome
      have hannsRigid : ∀ σ, some σ ∈ anns →
          ∀ x ∈ σ.body.freeVars, x ∈ RecGroup.rigidVars anns bindings := by
        intro σ hσ x hx
        exact List.mem_append_left _
          (Expr.scheme_body_mem_annList_tyFreeVars hσ hx)
      have hspecsLen : anns.length = specs1.length := by
        rw [hspecs1, List.length_map, RecSpec.init_length]
      obtain ⟨Sc, hSc, hfac⟩ :=
        RecCeilingConstraints.exists_of_generalizes
          (P := P) (rigid := RecGroup.rigidVars anns bindings)
          (G := G) (R := Rg) hspecsLen hGnodup
          (fun x hx hxG => hGrigid x hxG hx) hPG hRglc hRgP hRgrigid
          hPbelow hrigidBelow hGbelow hannsWF hannsRigid
          hspecs1LC hspecs1Below hgenInit
      set specsC := specs1.map (RecSpec.onSubst Sc) with hspecsC
      have hceiling : RecSpecs.ceilingOK G anns specsC :=
        by simpa [hspecsC] using
          hSc.ceilingOK hspecs1LC hspecs1Below hrigidBelow
      have hScdom : ∀ p ∈ Sc, p.1 ∉ G := fun p hp =>
        (hSc.dom_avoids p hp).2.2
      have hScrange : ∀ p ∈ Sc, ∀ u ∈ p.2.freeVars, u ∉ G :=
        hSc.range_avoids_pool
      have hScK : ∀ p ∈ Sc, p.1 ∉ K := by
        simpa [P] using RecCeilingConstraints.dom_avoids_filter hSc
      have hbodyE : TypeOfHM
          (RecSpecs.bodyCtx (S₀.onCtx ctx) dspecs Gdecl)
          body ( τ₀) := hbodyD
      have hbodyAlg0 :=
        letRecFused_body_retype (Φ := Φ) (ctx := ctx) (S₁ := S₁)
          (Sc := Sc) (R₁ := Rg) (S₀ := S₀)
          (anns := anns) (bindings := bindings) (body := body) (dspecs := dspecs)
          (specs1 := specs1) (specsC := specsC)
          (G := Gdecl) (Xs := Xs) (τ₀ := τ₀) (K := K) hspecs1 hspecsC
          (fun p hp => by rw [← hG]; exact hScdom p hp)
          (fun p hp u hu => by rw [← hG]; exact hScrange p hp u hu) hfac
          hanns_eq hdlc hwfD.nodup hXlen hXnodup hXG hXτs hXenv hXrigid
          hS₁lc hRglc hctxS₁ hKrigid hRgK hσfix hconnB hbodyE
      have hbodyAlg : TypeOfHM
          (Rg.onCtx
            { (Sc.onCtx (S₁.onCtx ctx)) with
              env := RecSpecs.ceilingSchemes G anns specsC ++
                (Sc.onCtx (S₁.onCtx ctx)).env })
          body ( τ₀) := by
        simpa only [hG] using hbodyAlg0
      have hσbody_bel : ∀ σ, some σ ∈ anns →
          Ty.BelowFvars Φ₁ σ.body := fun σ hσ =>
        Ty.BelowFvars.of_freeVars_lt (fun y hy =>
          hKΦ₁ y (hKe y (List.mem_append.mpr (Or.inl
            (List.mem_append.mpr (Or.inl
              (Expr.scheme_body_mem_annList_tyFreeVars hσ hy)))))))
      have hSc_bel : ∀ p ∈ Sc, Ty.BelowFvars Φ₁ p.2 :=
        hSc.belowFvars hrigidBelow
      have hspecsC_lc : ∀ s ∈ specsC, s.LC := by
        intro s hs
        rw [hspecsC] at hs
        obtain ⟨s₁, hs₁, rfl⟩ := List.mem_map.mp hs
        exact RecSpec.LC.onSubst hSc.lc (hspecs1LC s₁ hs₁)
      have hspecsC_post : ∀ s ∈ specsC, s.BelowFvars Φ₁ := by
        intro s hs
        rw [hspecsC] at hs
        obtain ⟨s₁, hs₁, rfl⟩ := List.mem_map.mp hs
        exact RecSpec.BelowFvars.onSubst hSc_bel (hspecs1Below s₁ hs₁)
      let bodyCtx : Ctx :=
        { (Sc.onCtx (S₁.onCtx ctx)) with
          env := RecSpecs.ceilingSchemes G anns specsC ++
            (Sc.onCtx (S₁.onCtx ctx)).env }
      have hwfB : CtxWF bodyCtx := by
        intro M hM
        rcases List.mem_append.mp hM with hM | hM
        · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hM
          cases p with
          | mk a s =>
              cases a with
              | some σ => exact hannsWF σ (List.of_mem_zip hp).1
              | none =>
                  exact RecSpec.bodyScheme_wf
                    (hspecsC_lc s (List.of_mem_zip hp).2)
        · exact Subst.onCtx_wf hSc.lc (Subst.onCtx_wf hS₁lc hwf) M hM
      have hbelowB : CtxBelow Φ₁ bodyCtx := by
        intro M hM
        rcases List.mem_append.mp hM with hM | hM
        · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hM
          cases p with
          | mk a s =>
              cases a with
              | some σ => exact hσbody_bel σ (List.of_mem_zip hp).1
              | none =>
                  exact RecSpec.bodyScheme_belowFvars
                    (hspecsC_post s (List.of_mem_zip hp).2)
        · exact Subst.onCtx_below hSc_bel (le_refl _)
            (Subst.onCtx_below hS₁_bel (le_trans (by omega) hgle) hbelow) M hM
      obtain ⟨Φ₂, S₂, τ₂, Rb, hbodyInfer, hAgreeB, htyB,
          hRblc, hRbK, hS₂K⟩ :=
        ihbody K hwfB hbelowB hRglc hKΦ₁ hKbody hRgK (by
          simpa [bodyCtx] using hbodyAlg)
      have hRgSc : Subst.AgreesBelow Φ₁ Rg (Sc ++ Rg) := by
        intro v hv
        simpa only [Subst.onTy_append] using hfac (Ty.fvar v)
      have hAgreePre : Subst.AgreesBelow Φ S₀ ((S₁ ++ Sc) ++ Rg) :=
        Subst.AgreesBelow.trans_append (by omega) hAgreeTier hS₁_bel hRgSc
      have hS₁Sc_bel : ∀ p ∈ S₁ ++ Sc, Ty.BelowFvars Φ₁ p.2 := by
        intro p hp
        exact (List.mem_append.mp hp).elim (hS₁_bel p) (hSc_bel p)
      have hAgree : Subst.AgreesBelow Φ S₀ (((S₁ ++ Sc) ++ S₂) ++ Rb) :=
        Subst.AgreesBelow.trans_append (by omega) hAgreePre hS₁Sc_bel hAgreeB
      refine ⟨Φ₂, S₁ ++ Sc ++ S₂, τ₂, Rb, ?_, ?_,
        htyB,
        hRblc, hRbK, ?_⟩
      · exact .letRec hannsWF hgroup hspecs1 hG hSc hspecsC hceiling hbodyInfer
      · simpa [List.append_assoc] using hAgree
      · intro p hp
        rw [List.mem_append, List.mem_append] at hp
        rcases hp with (hp | hp) | hp
        · exact hS₁K p hp
        · exact hScK p hp
        · exact hS₂K p hp

/-- Every branch body is no larger than the aggregate branch-list measure.
    This local public-side copy is used by the producer-completeness induction;
    the structurally identical Core helper is intentionally private there. -/
private theorem Expr.size_le_sizeBranches_of_mem
    {br : MatchPattern × Expr} {branches : List (MatchPattern × Expr)}
    (h : br ∈ branches) : br.2.size ≤ Expr.sizeBranches branches := by
  induction branches with
  | nil => exact absurd h List.not_mem_nil
  | cons hd rest ih =>
      rcases List.mem_cons.mp h with rfl | hrest
      · simp only [Expr.sizeBranches]
        omega
      · exact Nat.le_trans (ih hrest) (by
          simp only [Expr.sizeBranches]
          omega)

/-- Every recursive RHS is no larger than the aggregate recursive-group
    measure. -/
private theorem Expr.size_le_sizeRecGroup_of_mem {e : Expr} {bindings : List Expr}
    (h : e ∈ bindings) : e.size ≤ Expr.sizeRecGroup bindings := by
  induction bindings with
  | nil => exact absurd h List.not_mem_nil
  | cons hd rest ih =>
      rcases List.mem_cons.mp h with rfl | hrest
      · simp only [Expr.sizeRecGroup]
        omega
      · exact Nat.le_trans (ih hrest) (by
          simp only [Expr.sizeRecGroup]
          omega)

/-- Relational producer completeness for every source expression.  The
    annotation-insensitive size measure is essential for annotated `let`: its
    RHS is inferred after opening the annotation's binders, and opening
    preserves `Expr.size` even though it does not produce a literal subterm. -/
theorem Infer.complete (e : Expr) : Infer.CompleteAt e := by
  have upto : ∀ n : Nat, ∀ e : Expr, e.size < n → Infer.CompleteAt e := by
    intro n
    induction n with
    | zero =>
        intro e hsize
        omega
    | succ n ih =>
        intro e hsize
        cases e with
        | primLit p => exact Infer.complete_prim
        | primBinOp op => exact Infer.complete_primBinOp
        | var i => exact Infer.complete_var
        | ctor name => exact Infer.complete_ctor
        | lambda ann body =>
            have hbody : body.size < n := by
              simp only [Expr.size] at hsize
              omega
            intro Φ ctx S₀ τ₀ K hwf hbelow hS₀ hKΦ hKtv hKfix hty
            exact Infer.complete_lambda (ih body hbody) K hwf hbelow hS₀
              hKΦ hKtv hKfix hty
        | app f arg =>
            have hf : f.size < n := by
              simp only [Expr.size] at hsize
              omega
            have harg : arg.size < n := by
              simp only [Expr.size] at hsize
              omega
            intro Φ ctx S₀ τ₀ K hwf hbelow hS₀ hKΦ hKtv hKfix hty
            exact Infer.complete_app (ih f hf) (ih arg harg) K hwf hbelow hS₀
              hKΦ hKtv hKfix hty
        | letIn ann rhs body =>
            have hrhs : rhs.size < n := by
              simp only [Expr.size] at hsize
              omega
            have hbody : body.size < n := by
              simp only [Expr.size] at hsize
              omega
            intro Φ ctx S₀ τ₀ K hwf hbelow hS₀ hKΦ hKtv hKfix hty
            exact Infer.complete_letIn (ih rhs hrhs)
                (fun Ys => ih (rhs.openTyVars Ys) (by
                  rw [Expr.size_openTyVars]
                  exact hrhs))
                (ih body hbody) K hwf hbelow hS₀ hKΦ hKtv hKfix hty
        | match_ scrut branches =>
            have hscrut : scrut.size < n := by
              simp only [Expr.size] at hsize
              omega
            have hbranches : ∀ br ∈ branches, br.2.size < n := by
              intro br hbr
              have hle := Expr.size_le_sizeBranches_of_mem hbr
              simp only [Expr.size] at hsize
              omega
            intro Φ ctx S₀ τ₀ K hwf hbelow hS₀ hKΦ hKtv hKfix hty
            exact Infer.complete_match (ih scrut hscrut)
                (fun br hbr => ih br.2 (hbranches br hbr)) K hwf hbelow hS₀
                hKΦ hKtv hKfix hty
        | letRec anns bindings body =>
            have hbody : body.size < n := by
              simp only [Expr.size] at hsize
              omega
            have hbindings : ∀ b ∈ bindings, b.size < n := by
              intro b hb
              have hle := Expr.size_le_sizeRecGroup_of_mem hb
              simp only [Expr.size] at hsize
              omega
            intro Φ ctx S₀ τ₀ K hwf hbelow hS₀ hKΦ hKtv hKfix hty
            exact Infer.complete_letRec
                (fun b hb => ih b (hbindings b hb))
                (ih body hbody) K hwf hbelow hS₀ hKΦ hKtv hKfix hty
  intro Φ ctx S₀ τ₀ K hwf hbelow hS₀ hKΦ hKtv hKfix hty
  exact upto (e.size + 1) e (by omega) K hwf hbelow hS₀ hKΦ hKtv hKfix hty

/-- A relational annotated-let derivation leaves the executable worker's
    canonical skolem block rigid, even when the relation chose a later seed.
    Names below that later seed lie in an allocation gap; names at or above it
    are are protected by the rule's own escape premises. -/
theorem Infer.letInAnn_block_fresh {Φ : Nat} {ctx : Ctx} {σ : PolyTy}
    {rhs body : Expr} {Φ' : Nat} {S : Subst} {τ : Ty}
    (h : Infer Φ ctx (.letIn (some σ) rhs body) Φ' S τ)
    (hbelow : CtxBelow Φ ctx)
    (htfv : ∀ y ∈ (Expr.letIn (some σ) rhs body).tyFreeVars, y < Φ) :
    (∀ y ∈ freshVars Φ σ.paramCount, y ∉ S.map Prod.fst) ∧
    (∀ y ∈ freshVars Φ σ.paramCount, y ∉ (S.onCtx ctx).env.freeVars) := by
  cases h with
  | @letInAnn _ N _ _ _ _ Φ₁ Φ₂ S₁ Schk S₂ τ₁ τ₂
      hσwf hΦN hrhs huni hesc1 hesc2 hbody =>
    simp only [Expr.tyFreeVars, Option.elim_some, List.mem_append] at htfv
    have hctxGap : ∀ M ∈ ctx.env, ∀ v ∈ M.body.freeVars, v < Φ ∨ N ≤ v :=
      fun M hM v hv => Or.inl ((hbelow M hM).mem_lt v hv)
    have hrhsTfvGap :
        ∀ y ∈ (rhs.openTyVars (freshVars N σ.paramCount)).tyFreeVars,
          y < Φ ∨ N ≤ y := by
      intro y hy
      rcases Expr.tyFreeVars_openTyVars hy with hh | hh
      · exact Or.inl (htfv y (.inl (.inr hh)))
      · exact Or.inr (freshVars_ge y hh)
    obtain ⟨hr_τ, hr_D, hr_R⟩ :=
      Infer.gap_avoid hrhs (by omega) hctxGap hrhsTfvGap
    have hσopenGap :
        ∀ v ∈ (σ.openVars (freshVars N σ.paramCount)).freeVars,
          v < Φ ∨ N ≤ v := by
      intro v hv
      rcases Ty.freeVars_openVars_subset v hv with hh | hh
      · exact Or.inl (htfv v (.inl (.inl hh)))
      · exact Or.inr (freshVars_ge v hh)
    obtain ⟨hSchk_D, hSchk_R⟩ := UnifyRel.gap_avoid huni hr_τ hσopenGap
    have hbodyEnvGap :
        ∀ M ∈ (Schk.onCtx (S₁.onCtx ctx)).env, ∀ v ∈ M.body.freeVars,
          v < Φ ∨ Φ + σ.paramCount ≤ v := by
      intro M hM v hv
      rcases Subst.onCtx_avoidsItv hSchk_R
          (Subst.onCtx_avoidsItv hr_R hctxGap) M hM v hv with hlt | hge
      · exact Or.inl hlt
      · by_cases hvlt : v < Φ + σ.paramCount
        · exact absurd (Env.mem_freeVars_iff.mpr ⟨M, hM, hv⟩)
            (hesc2 v (by
              simp only [freshVars, List.mem_map, List.mem_range]
              exact ⟨v - N, by omega, by omega⟩))
        · exact Or.inr (by omega)
    have hle₁ := Infer.frontier_le hrhs
    obtain ⟨hb_τ, hb_D, hb_R⟩ := Infer.gap_avoid hbody
      (show Φ + σ.paramCount ≤ Φ₁ by omega)
      (by
        intro M hM v hv
        rcases List.mem_cons.mp hM with rfl | hM
        · exact Or.inl (htfv v (.inl (.inl hv)))
        · exact hbodyEnvGap M hM v hv)
      (fun y hy => Or.inl (htfv y (.inr hy)))
    refine ⟨?_, ?_⟩
    · intro y hy hmem
      have hyge := freshVars_ge y hy
      have hylt := freshVars_lt y hy
      rw [List.map_append, List.map_append, List.mem_append, List.mem_append] at hmem
      rcases hmem with (hmem | hmem) | hmem
      · obtain ⟨p, hp, hpy⟩ := List.mem_map.mp hmem
        by_cases hyN : y < N
        · rcases hr_D p hp with hh | hh <;> rw [hpy] at hh <;> omega
        · exact hesc1 y (by
            simp only [freshVars, List.mem_map, List.mem_range]
            exact ⟨y - N, by omega, by omega⟩)
            (List.mem_map.mpr ⟨p, List.mem_append_left _ hp, hpy⟩)
      · obtain ⟨p, hp, hpy⟩ := List.mem_map.mp hmem
        by_cases hyN : y < N
        · rcases hSchk_D p hp with hh | hh <;> rw [hpy] at hh <;> omega
        · exact hesc1 y (by
            simp only [freshVars, List.mem_map, List.mem_range]
            exact ⟨y - N, by omega, by omega⟩)
            (List.mem_map.mpr ⟨p, List.mem_append_right _ hp, hpy⟩)
      · obtain ⟨p, hp, hpy⟩ := List.mem_map.mp hmem
        rcases hb_D p hp with hh | hh <;> rw [hpy] at hh <;> omega
    · intro y hy hmem
      have hyge := freshVars_ge y hy
      have hylt := freshVars_lt y hy
      have hSenv :
          ∀ M ∈ ((S₁ ++ Schk ++ S₂).onCtx ctx).env, ∀ v ∈ M.body.freeVars,
            v < Φ ∨ Φ + σ.paramCount ≤ v := by
        rw [Subst.onCtx_append, Subst.onCtx_append]
        exact Subst.onCtx_avoidsItv hb_R hbodyEnvGap
      obtain ⟨M, hM, hyM⟩ := Env.mem_freeVars_iff.mp hmem
      rcases hSenv M hM y hyM with hh | hh <;> omega

/-! ## 7. Executable producer completeness

Relational completeness chooses witnesses existentially.  The executable
worker instead commits to particular fresh blocks and most-general unifiers,
so its completeness proof follows the worker in lockstep and uses the
principality theorem above to retype later subproblems under those concrete
choices. -/

/-- Function-completeness at a source expression: every well-scoped `Infer`
    derivation whose output avoids the worker's rigid set is accepted by the
    concrete worker. -/
def InferCoreComplete (e : Expr) : Prop :=
  ∀ {Φ : Nat} {ctx : Ctx} {Φ' : Nat} {S : Subst} {τ : Ty} (K : List Nat),
    CtxWF ctx → CtxBelow Φ ctx → (∀ k ∈ K, k < Φ) →
    (∀ y ∈ e.tyFreeVars, y ∈ K) → (∀ p ∈ S, p.1 ∉ K) →
    Infer Φ ctx e Φ' S τ →
    (inferWithTypesCore K Φ ctx e).isSome

/-- Synchronize two relational inference runs for the same source expression.
    The first run supplies a declarative typing; principality of the second
    produces the residual that reconciles the concrete worker choices. -/
theorem Infer.sync {e : Expr} {K : List Nat} {ctx : Ctx}
    {N N₁ N₂ : Nat} {S S' : Subst} {τ τ' : Ty}
    (h : Infer N ctx e N₁ S τ) (h' : Infer N ctx e N₂ S' τ')
    (hwf : CtxWF ctx) (hbelow : CtxBelow N ctx)
    (hKN : ∀ k ∈ K, k < N) (hKe : ∀ y ∈ e.tyFreeVars, y ∈ K)
    (hSK : ∀ p ∈ S, p.1 ∉ K) :
    ∃ R : Subst, (∀ p ∈ R, p.2.IsLC) ∧
      Eq ( τ) (R.onTy τ') ∧
      (∀ k ∈ K, R.onTy (.fvar k) = .fvar k) ∧
      Subst.AgreesBelow N S (S' ++ R) := by
  have hSlc : ∀ p ∈ S, p.2.IsLC := (Infer.lc h hwf).2
  have hKfix : ∀ k ∈ K, S.onTy (.fvar k) = .fvar k :=
    fun k hk => Ty.substFvars_eq_self_of_no_key (fun p hp heq => by
      simp only [Ty.freeVars, List.mem_singleton] at heq
      exact hSK p hp (heq ▸ hk))
  exact Infer.complete' h' hwf hbelow hSlc K hKN hKe hKfix
    (Infer.sourceSound h hwf hbelow K hKN hKe hSK)

theorem inferCore_complete_prim {p : PrimLitExpr} :
    InferCoreComplete (.primLit p) := by
  intro Φ ctx Φ' S τ K _ _ _ _ _ h
  cases h <;> simp only [inferWithTypesCore, Option.isSome_some]

theorem inferCore_complete_primBinOp {op : PrimBinOp} :
    InferCoreComplete (.primBinOp op) := by
  intro Φ ctx Φ' S τ K _ _ _ _ _ h
  cases h with
  | primBinOpIntAdd => simp only [inferWithTypesCore, Option.isSome_some]
  | primBinOpIntSub => simp only [inferWithTypesCore, Option.isSome_some]
  | primBinOpIntLt hlookT hbT hlookF hbF =>
      rw [inferWithTypesCore]
      split
      next heqT => rw [hlookT] at heqT; simp at heqT
      next tc heqT =>
        rw [hlookT] at heqT
        obtain rfl := (Option.some.inj heqT).symm
        split
        next heqF => rw [hlookF] at heqF; simp at heqF
        next fc heqF =>
          rw [hlookF] at heqF
          obtain rfl := (Option.some.inj heqF).symm
          rw [dif_pos (Ctor.isBoolCtor_iff.mpr hbT),
            dif_pos (Ctor.isBoolCtor_iff.mpr hbF)]
          rfl
  | primBinOpCharLt hlookT hbT hlookF hbF =>
      rw [inferWithTypesCore]
      split
      next heqT => rw [hlookT] at heqT; simp at heqT
      next tc heqT =>
        rw [hlookT] at heqT
        obtain rfl := (Option.some.inj heqT).symm
        split
        next heqF => rw [hlookF] at heqF; simp at heqF
        next fc heqF =>
          rw [hlookF] at heqF
          obtain rfl := (Option.some.inj heqF).symm
          rw [dif_pos (Ctor.isBoolCtor_iff.mpr hbT),
            dif_pos (Ctor.isBoolCtor_iff.mpr hbF)]
          rfl

theorem inferCore_complete_var {i : Nat} : InferCoreComplete (.var i) := by
  intro Φ ctx Φ' S τ K _ _ _ _ _ h
  cases h with
  | var hlook =>
      rw [inferWithTypesCore]
      split
      · rename_i heq; rw [heq] at hlook; simp at hlook
      · rfl

theorem inferCore_complete_ctor {name : CtorName} :
    InferCoreComplete (.ctor name) := by
  intro Φ ctx Φ' S τ K _ _ _ _ _ h
  cases h with
  | ctor hlook =>
      rw [inferWithTypesCore]
      split
      · rename_i heq; rw [heq] at hlook; simp at hlook
      · rfl

/-- Extending a well-formed context by the fresh monotype used for an
    unannotated lambda preserves well-formedness. -/
private theorem CtxWF.cons_fvar {Φ : Nat} {ctx : Ctx} (hwf : CtxWF ctx) :
    CtxWF { ctx with env := PolyTy.mkTrivial (.fvar Φ) :: ctx.env } := by
  intro M hM
  rcases List.mem_cons.mp hM with rfl | hM
  · exact ContainsBvarsUpTo.fvar
  · exact hwf M hM

/-- The same lambda extension advances the free-variable frontier by one. -/
private theorem CtxBelow.cons_fvar {Φ : Nat} {ctx : Ctx}
    (hbelow : CtxBelow Φ ctx) :
    CtxBelow (Φ + 1) { ctx with env := PolyTy.mkTrivial (.fvar Φ) :: ctx.env } := by
  intro M hM
  rcases List.mem_cons.mp hM with rfl | hM
  · exact .fvar (by omega)
  · exact (hbelow M hM).mono (by omega)

theorem inferCore_complete_lambda {ann : Option Ty} {body : Expr}
    (ih : InferCoreComplete body) : InferCoreComplete (.lambda ann body) := by
  intro Φ ctx Φ' S τ K hwf hbelow hKΦ hKe hSK h
  cases h with
  | lambda hseed hbody =>
      cases hseed
      case none =>
          simp only [Expr.tyFreeVars, Option.elim_none, List.nil_append] at hKe
          have hsome := ih K hwf.cons_fvar hbelow.cons_fvar
            (fun k hk => by have := hKΦ k hk; omega) hKe hSK hbody
          obtain ⟨out, hout⟩ := Option.isSome_iff_exists.mp hsome
          rw [inferWithTypesCore, hout]
          rcases out with ⟨⟨Φo, So, τo, eout, schemes⟩, houtrel, houtavoid⟩
          rfl
      case some hcl =>
          expose_names
          simp only [Expr.tyFreeVars, Option.elim_some, List.mem_append] at hKe
          have hwf' : CtxWF
              { ctx with env := PolyTy.mkTrivial paramTy :: ctx.env } := by
            intro M hM
            rcases List.mem_cons.mp hM with rfl | hM
            · exact hcl
            · exact hwf M hM
          have hbelow' : CtxBelow Φ
              { ctx with env := PolyTy.mkTrivial paramTy :: ctx.env } := by
            intro M hM
            rcases List.mem_cons.mp hM with rfl | hM
            · exact Ty.BelowFvars.of_freeVars_lt
                (fun v hv => hKΦ v (hKe v (.inl hv)))
            · exact hbelow M hM
          have hsome := ih K hwf' hbelow' hKΦ
            (fun y hy => hKe y (.inr hy)) hSK hbody
          obtain ⟨out, hout⟩ := Option.isSome_iff_exists.mp hsome
          rw [inferWithTypesCore,
            dif_pos ((Ty.bvarsBelow_iff paramTy).mpr hcl), hout]
          rcases out with ⟨⟨Φo, So, τo, eout, schemes⟩, houtrel, houtavoid⟩
          rfl

theorem inferCore_complete_app {f arg : Expr}
    (ihf : InferCoreComplete f) (iharg : InferCoreComplete arg) :
    InferCoreComplete (.app f arg) := by
  intro Φ ctx Φ' S τ K hwf hbelow hKΦ hKe hSK h
  have happ := Infer.sourceSound h hwf hbelow K hKΦ hKe hSK
  cases h with
  | @app _ _ _ _ Φ₁ Φ₂ S₁ S₂ S₃ τf τa hf harg huni =>
      simp only [Expr.tyFreeVars, List.mem_append] at hKe
      have hKef : ∀ y ∈ f.tyFreeVars, y ∈ K := fun y hy => hKe y (.inl hy)
      have hKea : ∀ y ∈ arg.tyFreeVars, y ∈ K := fun y hy => hKe y (.inr hy)
      have hKfixS : ∀ k ∈ K, (S₁ ++ S₂ ++ S₃).onTy (.fvar k) = .fvar k :=
        fun k hk => Ty.substFvars_eq_self_of_no_key (fun p hp heq => by
          simp only [Ty.freeVars, List.mem_singleton] at heq
          exact hSK p hp (heq ▸ hk))
      have hSK₁ : ∀ p ∈ S₁, p.1 ∉ K :=
        fun p hp => hSK p (List.mem_append_left _ (List.mem_append_left _ hp))
      obtain ⟨argTy, hfty, hargty⟩ : ∃ argTy,
          TypeOfHM ((S₁ ++ S₂ ++ S₃).onCtx ctx) f
            (.arrow argTy ( (S₃.onTy (.fvar Φ₂)))) ∧
          TypeOfHM ((S₁ ++ S₂ ++ S₃).onCtx ctx) arg argTy := by
        cases happ with
        | app hfty hargty => exact ⟨_, hfty, hargty⟩
      have hSlc : ∀ p ∈ S₁ ++ S₂ ++ S₃, p.2.IsLC :=
        (Infer.lc (Infer.app hf harg huni) hwf).2

      have hsf := ihf K hwf hbelow hKΦ hKef hSK₁ hf
      obtain ⟨outf, hef⟩ := Option.isSome_iff_exists.mp hsf
      rcases outf with ⟨⟨Φ₁', S₁', τf', fOut, fSchemes⟩, hf', havf⟩
      obtain ⟨R_f, hR_flc, hTypef, hR_fK, hAgreef⟩ :=
        Infer.complete' hf' hwf hbelow hSlc K hKΦ hKef hKfixS hfty
      have hS₁' : ∀ p ∈ S₁', p.2.IsLC := (Infer.lc hf' hwf).2
      have hbf := Infer.belowFvars hf' hbelow (fun y hy => hKΦ y (hKef y hy))
      have hle₁ := Infer.frontier_le hf'
      have hwf₁ := Subst.onCtx_wf hS₁' hwf
      have hbelow₁ := Subst.onCtx_below hbf.2 hle₁ hbelow
      have hKΦ₁ : ∀ k ∈ K, k < Φ₁' :=
        fun k hk => lt_of_lt_of_le (hKΦ k hk) hle₁
      have hctxeq : (R_f.onCtx (S₁'.onCtx ctx)) =
          ((S₁ ++ S₂ ++ S₃).onCtx ctx) := by
        rw [← Subst.onCtx_append]
        exact (Subst.onCtx_congr hAgreef hbelow).symm
      have hargty' : TypeOfHM (R_f.onCtx (S₁'.onCtx ctx))
          arg argTy := by
        rw [hctxeq]
        exact hargty
      obtain ⟨_, _, _, _, hinfa, _, _, hR_alc₀, hR_aK₀, hSaK⟩ :=
        (Infer.complete arg) K hwf₁ hbelow₁ hR_flc hKΦ₁ hKea hR_fK hargty'
      have hsa := iharg K hwf₁ hbelow₁ hKΦ₁ hKea hSaK hinfa
      obtain ⟨outa, hea⟩ := Option.isSome_iff_exists.mp hsa
      rcases outa with ⟨⟨Φ₂', S₂', τa', argOut, argSchemes⟩, harg', hava⟩
      obtain ⟨R_a, hR_alc, hTypea, hR_aK, hAgreea⟩ :=
        Infer.complete' harg' hwf₁ hbelow₁ hR_flc K hKΦ₁ hKea hR_fK hargty'

      have hba := Infer.belowFvars harg' hbelow₁
        (fun y hy => hKΦ₁ y (hKea y hy))
      have hle₂ := Infer.frontier_le harg'
      have hcongr_f : Eq (R_f.onTy τf') ((S₂' ++ R_a).onTy τf') :=
        Subst.onTy_congr hAgreea hbf.1
      have hP : Eq
          (.arrow argTy ( (S₃.onTy (.fvar Φ₂))))
          (R_a.onTy (S₂'.onTy τf')) := by
        simpa [Subst.onTy_append] using Eq.trans hTypef hcongr_f
      have hΦ₂τf : Φ₂' ∉ (S₂'.onTy τf').freeVars := fun hm => by
        have hbel := Subst.onTy_belowFvars hba.2 (hbf.1.mono hle₂)
        have := hbel.mem_lt _ hm
        omega
      have hΦ₂τa : Φ₂' ∉ τa'.freeVars := fun hm => by
        have := hba.1.mem_lt _ hm
        omega
      have hτ₀LC : ( (S₃.onTy (.fvar Φ₂))).IsLC := by
        have hreg := TypeOfHM.regular hfty
        cases hreg with
        | arrow _ hT => exact hT
      have hKΦ₂ : ∀ k ∈ K, k < Φ₂' :=
        fun k hk => lt_of_lt_of_le (hKΦ₁ k hk) hle₂
      obtain ⟨U, hUni, hUlc, hUK, _, _⟩ :=
        exists_app_unifier hP hTypea hΦ₂τf hΦ₂τa hR_alc hτ₀LC hR_aK hKΦ₂
      have hτfLC := (Infer.lc hf' hwf).1
      have hτaLC := (Infer.lc harg' hwf₁).1
      have hS₂' := (Infer.lc harg' hwf₁).2
      have huniSome :
          (unifyCoreK K (S₂'.onTy τf') (.arrow τa' (.fvar Φ₂'))).isSome :=
        unifyCoreK_complete (Subst.onTy_lc hS₂' hτfLC)
          (.arrow hτaLC ContainsBvarsUpTo.fvar) hUlc hUni hUK
      obtain ⟨out₃, he₃⟩ := Option.isSome_iff_exists.mp huniSome
      rcases out₃ with ⟨S₃', h₃, hav₃⟩
      rw [inferWithTypesCore, hef]
      simp only [hea, he₃]
      rfl

theorem inferCore_complete_letIn_none {rhs body : Expr}
    (iha : InferCoreComplete rhs) (ihb : InferCoreComplete body) :
    InferCoreComplete (.letIn none rhs body) := by
  intro Φ ctx Φ' S τ K hwf hbelow hKΦ hKe hSK h
  have hSlc : ∀ p ∈ S, p.2.IsLC := (Infer.lc h hwf).2
  have hlet := Infer.sourceSound h hwf hbelow K hKΦ hKe hSK
  simp only [  Option.map_none] at hlet
  cases h with
  | @letIn _ _ _ _ Φ₁d Φ₂d S₁d S₂d τ₁d τ₂ hrhs hbodyRel =>
      cases hlet with
      | letIn hMwf hann hcofin hbodyCtxEq hbodyD =>
        rename_i bodyCtx M L
        rw [hbodyCtxEq] at hbodyD
        have hKrhs : ∀ y ∈ rhs.tyFreeVars, y ∈ K := fun y hy => hKe y (by
          simpa [Expr.tyFreeVars, Option.elim_none] using
            (List.mem_append.mpr (Or.inl hy)))
        have hKbody : ∀ y ∈ body.tyFreeVars, y ∈ K := fun y hy => hKe y (by
          simpa [Expr.tyFreeVars, Option.elim_none] using
            (List.mem_append.mpr (Or.inr hy)))
        have hKfixS : ∀ k ∈ K, (S₁d ++ S₂d).onTy (.fvar k) = .fvar k :=
          fun k hk => Ty.substFvars_eq_self_of_no_key (fun p hp heq => by
            simp only [Ty.freeVars, List.mem_singleton] at heq
            exact hSK p hp (heq ▸ hk))
        have hSK₁ : ∀ p ∈ S₁d, p.1 ∉ K :=
          fun p hp => hSK p (List.mem_append_left _ hp)
        obtain ⟨Xs, hXlen, hXnodup, hXavoid⟩ := exists_fresh_names
          (L ++ M.body.freeVars ++ K ++
            ((S₁d ++ S₂d).map Prod.fst ++
              (S₁d ++ S₂d).flatMap (fun p => p.2.freeVars)) ++ List.range Φ)
          M.paramCount
        have hXfresh : FreshNames L M.paramCount Xs :=
          ⟨hXlen, hXnodup, fun x hx hc =>
            hXavoid x hx (by simp only [List.mem_append]; tauto)⟩
        have hXMbody : ∀ x ∈ Xs, x ∉ M.body.freeVars := fun x hx hc =>
          hXavoid x hx (by simp only [List.mem_append]; tauto)
        have hXK : ∀ x ∈ Xs, x ∉ K := fun x hx hc =>
          hXavoid x hx (by simp only [List.mem_append]; tauto)
        have hXSran : ∀ x ∈ Xs,
            x ∉ (S₁d ++ S₂d).flatMap (fun p => p.2.freeVars) := fun x hx hc =>
          hXavoid x hx (by simp only [List.mem_append]; tauto)
        have hXrange : ∀ x ∈ Xs, x ∉ List.range Φ := fun x hx hc =>
          hXavoid x hx (by simp only [List.mem_append]; tauto)
        have hcofin' : TypeOfHM ((S₁d ++ S₂d).onCtx ctx)
            rhs (M.openVars Xs) := by
          simpa [Expr.openBoundTyVars] using hcofin Xs hXfresh
        have hsr := iha K hwf hbelow hKΦ hKrhs hSK₁ hrhs
        obtain ⟨outr, herhs⟩ := Option.isSome_iff_exists.mp hsr
        rcases outr with
          ⟨⟨Φ₁', S₁', τ₁', rhsOut, rhsSchemes⟩, hrhs', hav₁⟩
        obtain ⟨R₁, hR₁lc, htyr, hR₁K, hAgree₁⟩ :=
          Infer.complete' hrhs' hwf hbelow hSlc K hKΦ hKrhs hKfixS hcofin'
        obtain ⟨hτ₁lc, hS₁lc⟩ := Infer.lc hrhs' hwf
        have hle : Φ ≤ Φ₁' := Infer.frontier_le hrhs'
        obtain ⟨hτ₁bel, hS₁bel⟩ := Infer.belowFvars hrhs' hbelow
          (fun y hy => hKΦ y (hKrhs y hy))
        have hwf₁ : CtxWF (S₁'.onCtx ctx) := Subst.onCtx_wf hS₁lc hwf
        have hbelow₁ : CtxBelow Φ₁' (S₁'.onCtx ctx) :=
          Subst.onCtx_below hS₁bel hle hbelow
        have hKΦ₁ : ∀ k ∈ K, k < Φ₁' :=
          fun k hk => lt_of_lt_of_le (hKΦ k hk) hle
        have hctxBridge : (R₁.onCtx (S₁'.onCtx ctx)) =
            ((S₁d ++ S₂d).onCtx ctx) := by
          rw [← Subst.onCtx_append]
          exact (Subst.onCtx_congr hAgree₁ hbelow).symm
        have hgen := genScheme_generalizes_of_agrees
          (ctx := ctx) (rhs := rhs) (S₀ := S₁d ++ S₂d) (S₁ := S₁')
          (R₁ := R₁) (τ₁ := τ₁') (M := M) (Xs := Xs) (K := K)
          hbelow hKrhs hMwf hXlen hXnodup hXMbody hXK hXSran hXrange
          hτ₁lc hR₁lc hR₁K hAgree₁ htyr
        have hbodyBridge : TypeOfHM
            ({ (R₁.onCtx (S₁'.onCtx ctx)) with
                env :=  M ::
                  (R₁.onCtx (S₁'.onCtx ctx)).env })
            body ( τ) := by
          rw [hctxBridge]
          simpa [Subst.onCtx, Subst.onEnv] using hbodyD
        have hbodyAlg : TypeOfHM
            ({ (R₁.onCtx (S₁'.onCtx ctx)) with
                env :=
                    (R₁.onPolyTy (genScheme rhs.tyFreeVars
                      (S₁'.onCtx ctx).env τ₁')) ::
                  (R₁.onCtx (S₁'.onCtx ctx)).env })
            body ( τ) := by
          exact TypeOfHM.weaken_scheme (env_post := [])
            (env := (R₁.onCtx (S₁'.onCtx ctx)).env)
            (M :=  M)
            (M' :=  (R₁.onPolyTy
              (genScheme rhs.tyFreeVars (S₁'.onCtx ctx).env τ₁')))
            hgen hbodyBridge
        let ctx₁ : Ctx := { (S₁'.onCtx ctx) with
          env := genScheme rhs.tyFreeVars (S₁'.onCtx ctx).env τ₁' ::
            (S₁'.onCtx ctx).env }
        have hwfBody : CtxWF ctx₁ := by
          intro N hN
          rcases List.mem_cons.mp hN with rfl | hN
          · exact genScheme_wf hτ₁lc
          · exact hwf₁ N hN
        have hbelowBody : CtxBelow Φ₁' ctx₁ := by
          intro N hN
          rcases List.mem_cons.mp hN with rfl | hN
          · exact hτ₁bel.closeOver
          · exact hbelow₁ N hN
        have hbodyAlg' : TypeOfHM (R₁.onCtx ctx₁)
            body ( τ) := by
          simpa [ctx₁, Subst.onCtx,  Subst.onEnv,  List.map_cons] using hbodyAlg
        obtain ⟨_, _, _, _, hinfb, _, _, _, _, hSbK⟩ :=
          (Infer.complete body) K hwfBody hbelowBody hR₁lc hKΦ₁
            hKbody hR₁K hbodyAlg'
        have hsb := ihb K hwfBody hbelowBody hKΦ₁ hKbody hSbK hinfb
        obtain ⟨outb, hebody⟩ := Option.isSome_iff_exists.mp hsb
        rcases outb with
          ⟨⟨Φ₂', S₂', τ₂', bodyOut, bodySchemes⟩, hbody', hav₂⟩
        simp only [ctx₁] at hebody
        rw [inferWithTypesCore, herhs]
        simp only [hebody]
        rfl

theorem inferCore_complete_letIn_some {σ : PolyTy} {rhs body : Expr}
    (ihao : ∀ Ys, InferCoreComplete (rhs.openTyVars Ys))
    (ihb : InferCoreComplete body) :
    InferCoreComplete (.letIn (some σ) rhs body) := by
  intro Φ ctx Φ' S τ K hwf hbelow hKΦ hKe hSK h
  have hSlc : ∀ p ∈ S, p.2.IsLC := (Infer.lc h hwf).2
  obtain ⟨hAdom, hBenv⟩ :=
    Infer.letInAnn_block_fresh h hbelow (fun y hy => hKΦ y (hKe y hy))
  have hlet := Infer.sourceSound h hwf hbelow K hKΦ hKe hSK
  simp only [] at hlet
  cases hlet with
  | letIn hMwf hann hcofin hbodyCtxEq hbodyD =>
      rename_i bodyCtx M L
      rw [hbodyCtxEq] at hbodyD
      have hMσ : M =  σ := hann ( σ) rfl
      subst M
      have hσwf : σ.WF := hMwf
      have hKσ : ∀ y ∈ σ.body.freeVars, y ∈ K := fun y hy => hKe y (by
        simpa [Expr.tyFreeVars, Option.elim_some] using
          (List.mem_append_left (body.tyFreeVars)
            (List.mem_append_left (rhs.tyFreeVars) hy)))
      have hKrhs : ∀ y ∈ rhs.tyFreeVars, y ∈ K := fun y hy => hKe y (by
        simpa [Expr.tyFreeVars, Option.elim_some] using
          (List.mem_append_left (body.tyFreeVars)
            (List.mem_append_right (σ.body.freeVars) hy)))
      have hKbody : ∀ y ∈ body.tyFreeVars, y ∈ K := fun y hy => hKe y (by
        simpa [Expr.tyFreeVars, Option.elim_some] using
          (List.mem_append_right (σ.body.freeVars ++ rhs.tyFreeVars) hy))
      have hcofin' : ∀ Xs : List Nat, FreshNames L σ.paramCount Xs →
          TypeOfHM (S.onCtx ctx) (rhs.openTyVars Xs)
            ( (σ.openVars Xs)) := by
        intro Xs hf
        simpa [Expr.openBoundTyVars] using hcofin Xs hf
      let Ys := freshVars Φ σ.paramCount
      have hbelowN : CtxBelow (Φ + σ.paramCount) ctx :=
        fun M hM => (hbelow M hM).mono (by omega)
      have hKΦ' : ∀ k ∈ K ++ Ys, k < Φ + σ.paramCount := by
        intro k hk
        rcases List.mem_append.mp hk with hk | hk
        · have := hKΦ k hk
          omega
        · have := freshVars_lt k (by simpa [Ys] using hk)
          omega
      have hKe' : ∀ y ∈ (rhs.openTyVars Ys).tyFreeVars, y ∈ K ++ Ys := by
        intro y hy
        rcases Expr.tyFreeVars_openTyVars hy with hy | hy
        · exact List.mem_append_left _ (hKrhs y hy)
        · exact List.mem_append_right _ hy
      have hKfix' : ∀ k ∈ K ++ Ys, S.onTy (.fvar k) = .fvar k := by
        intro k hk
        rcases List.mem_append.mp hk with hk | hk
        · exact Ty.substFvars_eq_self_of_no_key (fun p hp heq => by
            simp only [Ty.freeVars, List.mem_singleton] at heq
            exact hSK p hp (heq ▸ hk))
        · apply Ty.substFvars_eq_self_of_no_key
          intro p hp heq
          simp only [Ty.freeVars, List.mem_singleton] at heq
          exact hAdom k (by simpa [Ys] using hk)
            (List.mem_map.mpr ⟨p, hp, heq⟩)
      have htyYs : TypeOfHM (S.onCtx ctx)
          (rhs.openTyVars Ys) ( (σ.openVars Ys)) := by
        exact typeOfHM_at_block
          (ctx := (S.onCtx ctx)) (rhs := rhs)
          (σ :=  σ) (L := L) (Ys := Ys)
          (by simpa [Ys] using (freshVars_length Φ σ.paramCount)) hcofin'
      obtain ⟨_, _, _, _, Drhs, _, _, _, _, hSrhsK⟩ :=
        (Infer.complete (rhs.openTyVars Ys))
          (K ++ Ys) hwf hbelowN hSlc hKΦ' hKe' hKfix' htyYs
      have hrhsSome := ihao Ys (K ++ Ys) hwf hbelowN hKΦ' hKe' hSrhsK
        Drhs
      obtain ⟨rhsResult, herhs⟩ := Option.isSome_iff_exists.mp hrhsSome
      rcases rhsResult with
        ⟨⟨Φ₁, S₁, τ₁, rhsOut, rhsSchemes⟩, hrhs, hav₁⟩
      obtain ⟨R₁, hR₁lc, htya, hR₁K, hAgreeRhs⟩ :=
        Infer.complete' hrhs hwf hbelowN hSlc (K ++ Ys) hKΦ' hKe' hKfix' htyYs
      obtain ⟨hτ₁lc, hS₁lc⟩ := Infer.lc hrhs hwf
      have hle₁ : Φ + σ.paramCount ≤ Φ₁ := Infer.frontier_le hrhs
      obtain ⟨hτ₁bel, hS₁bel⟩ := Infer.belowFvars hrhs hbelowN
        (fun y hy => hKΦ' y (hKe' y hy))
      have hσopenLC : (σ.openVars Ys).IsLC :=
        PolyTy.openVars_isLC hσwf (by simp [Ys])
      have hR₁σopen : R₁.onTy (σ.openVars Ys) = σ.openVars Ys := by
        refine Subst.onTy_eq_self_of_fixes (fun v hv => ?_)
        rcases Ty.freeVars_openVars_subset v hv with hv | hv
        · exact hR₁K v (List.mem_append_left _ (hKσ v hv))
        · exact hR₁K v (List.mem_append_right _ hv)
      have hUuni : Unifies R₁ τ₁ (σ.openVars Ys) := by
        unfold Unifies
        rw [hR₁σopen]
        exact Eq.symm htya
      have huniSome : (unifyCoreK (K ++ Ys) τ₁ (σ.openVars Ys)).isSome := by
        exact unifyCoreK_complete hτ₁lc hσopenLC hR₁lc hUuni hR₁K
      obtain ⟨checkResult, heuni⟩ := Option.isSome_iff_exists.mp huniSome
      rcases checkResult with ⟨Schk, hSchk, havSchk⟩
      have hesc1 : ∀ y ∈ Ys, y ∉ (S₁ ++ Schk).map Prod.fst := by
        intro y hy hc
        obtain ⟨p, hp, hpy⟩ := List.mem_map.mp hc
        rcases List.mem_append.mp hp with hp | hp
        · exact hav₁ p hp (List.mem_append_right _ (hpy ▸ hy))
        · exact havSchk p hp (List.mem_append_right _ (hpy ▸ hy))
      obtain ⟨V, hV, hVlc, hVK⟩ :=
        UnifyRel.greatest_K hSchk R₁ hR₁lc hUuni hR₁K
      have hesc2 : ∀ y ∈ Ys,
          y ∉ (Schk.onCtx (S₁.onCtx ctx)).env.freeVars := by
        intro y hy hc
        rw [Env.mem_freeVars_iff] at hc
        obtain ⟨M', hM', hyM'⟩ := hc
        have hM'map : M' ∈ (S₁.onCtx ctx).env.map Schk.onPolyTy := by
          simpa [Subst.onCtx, Subst.onEnv] using hM'
        obtain ⟨M, hM, rfl⟩ := List.mem_map.mp hM'map
        have hM'' : M ∈ ctx.env.map S₁.onPolyTy := by
          simpa [Subst.onCtx, Subst.onEnv] using hM
        obtain ⟨M₀, hM₀, rfl⟩ := List.mem_map.mp hM''
        have hyV : y ∈ (V.onTy (Schk.onTy (S₁.onTy M₀.body))).freeVars := by
          apply Ty.mem_freeVars_onTy_iff.mpr
          refine ⟨y, hyM', ?_⟩
          have hVy : V.onTy (.fvar y) = .fvar y :=
            hVK y (List.mem_append_right _ hy)
          rw [hVy]
          simp [Ty.freeVars]
        have hAgreeM : Eq (R₁.onTy (S₁.onTy M₀.body))
            (V.onTy (Schk.onTy (S₁.onTy M₀.body))) := hV (S₁.onTy M₀.body)
        have hyR : y ∈ (R₁.onTy (S₁.onTy M₀.body)).freeVars := by
          have hyVE : y ∈
              ( (V.onTy (Schk.onTy (S₁.onTy M₀.body)))).freeVars :=
            hyV
          have hyRE : y ∈ ( (R₁.onTy (S₁.onTy M₀.body))).freeVars := by
            rwa [hAgreeM]
          exact hyRE
        have hbelowM₀ : Ty.BelowFvars (Φ + σ.paramCount) M₀.body :=
          (hbelow M₀ hM₀).mono (by omega)
        have hAgreeM₀ : Eq (S.onTy M₀.body)
            (R₁.onTy (S₁.onTy M₀.body)) := by
          simpa [Subst.onTy_append] using
            Subst.onTy_congr hAgreeRhs hbelowM₀
        have hyS : y ∈ (S.onTy M₀.body).freeVars := by
          have hyRE : y ∈ ( (R₁.onTy (S₁.onTy M₀.body))).freeVars :=
            hyR
          have hySE : y ∈ ( (S.onTy M₀.body)).freeVars := by
            rwa [hAgreeM₀]
          exact hySE
        have hySenv : y ∈ (S.onCtx ctx).env.freeVars :=
          Env.mem_freeVars_iff.mpr ⟨S.onPolyTy M₀, by
            simpa [Subst.onCtx, Subst.onEnv] using
              (List.mem_map.mpr ⟨M₀, hM₀, rfl⟩), hyS⟩
        exact hBenv y (by simpa [Ys] using hy) hySenv
      have hAgreeRhs' : ∀ v, v < Φ + σ.paramCount →
          Eq (S.onTy (.fvar v)) (R₁.onTy (S₁.onTy (.fvar v))) := by
        intro v hv
        simpa [Subst.onTy_append] using hAgreeRhs v hv
      have hAgreeV : Subst.AgreesBelow (Φ + σ.paramCount) S ((S₁ ++ Schk) ++ V) := by
        intro v hv
        rw [Subst.onTy_append, Subst.onTy_append]
        exact Eq.trans (hAgreeRhs' v hv) (hV (S₁.onTy (.fvar v)))
      have hAgreeΦ : Subst.AgreesBelow Φ S ((S₁ ++ Schk) ++ V) :=
        fun v hv => hAgreeV v (by omega)
      have hσbody : Ty.BelowFvars Φ σ.body :=
        Ty.BelowFvars.of_freeVars_lt (fun v hv => hKΦ v (hKσ v hv))
      have hσbody₁ : Ty.BelowFvars Φ₁ σ.body := hσbody.mono (by omega)
      have hσopenBel : Ty.BelowFvars Φ₁ (σ.openVars Ys) :=
        Ty.openVars_belowFvars hσbody₁ (fun x hx => by
          have := freshVars_lt x (by simpa [Ys] using hx)
          omega)
      have hSchkbel : ∀ p ∈ Schk, Ty.BelowFvars Φ₁ p.2 :=
        UnifyRel.belowFvars hSchk hτ₁bel hσopenBel
      have hSchklc : ∀ p ∈ Schk, p.2.IsLC :=
        UnifyRel.lc hSchk hτ₁lc hσopenLC
      have hprefixBel : ∀ p ∈ S₁ ++ Schk, Ty.BelowFvars Φ₁ p.2 := by
        intro p hp
        rcases List.mem_append.mp hp with hp | hp
        · exact hS₁bel p hp
        · exact hSchkbel p hp
      have hctxWF₁ : CtxWF (S₁.onCtx ctx) := Subst.onCtx_wf hS₁lc hwf
      have hctxBelow₁ : CtxBelow Φ₁ (S₁.onCtx ctx) :=
        Subst.onCtx_below hS₁bel hle₁ hbelowN
      let bodyCtx : Ctx := { (Schk.onCtx (S₁.onCtx ctx)) with
        env := σ :: (Schk.onCtx (S₁.onCtx ctx)).env }
      have hbodyWF : CtxWF bodyCtx := by
        intro M hM
        rcases List.mem_cons.mp hM with rfl | hM
        · exact hσwf
        · exact (Subst.onCtx_wf hSchklc hctxWF₁) M hM
      have hbodyBelow : CtxBelow Φ₁ bodyCtx := by
        intro M hM
        rcases List.mem_cons.mp hM with rfl | hM
        · exact hσbody₁
        · exact (Subst.onCtx_below hSchkbel (le_refl _) hctxBelow₁) M hM
      have hctxTail : (V.onCtx (Schk.onCtx (S₁.onCtx ctx))) =
          (S.onCtx ctx) := by
        rw [← Subst.onCtx_append, ← Subst.onCtx_append]
        simpa [List.append_assoc] using
          (Subst.onCtx_congr hAgreeV hbelowN).symm
      have hσbodyV : V.onTy σ.body = σ.body := by
        refine Subst.onTy_eq_self_of_fixes (fun v hv => ?_)
        exact hVK v (List.mem_append_left _ (hKσ v hv))
      have hhead :  (V.onPolyTy σ) =  σ := by
        simp [Subst.onPolyTy,  hσbodyV]
      have hbodyctx : (V.onCtx bodyCtx) =
          { (V.onCtx (Schk.onCtx (S₁.onCtx ctx))) with
            env :=  (V.onPolyTy σ) ::
              (V.onCtx (Schk.onCtx (S₁.onCtx ctx))).env } := by
        simp only [bodyCtx,  Subst.onCtx, Subst.onEnv,  List.map_cons]
      have hbodyAlg : TypeOfHM (V.onCtx bodyCtx)
          body ( τ) := by
        rw [hbodyctx, hctxTail, hhead]
        exact hbodyD
      obtain ⟨_, _, _, _, Dbody, _, _, _, _, hSbodyK⟩ :=
        (Infer.complete body) K hbodyWF hbodyBelow hVlc
          (fun k hk => by have := hKΦ k hk; omega) hKbody
          (fun k hk => hVK k (List.mem_append_left _ hk)) hbodyAlg
      have hbodySome := ihb K hbodyWF hbodyBelow
        (fun k hk => by have := hKΦ k hk; omega) hKbody hSbodyK Dbody
      obtain ⟨bodyResult, hebody⟩ := Option.isSome_iff_exists.mp hbodySome
      rcases bodyResult with
        ⟨⟨Φ₂, S₂, τ₂, bodyOut, bodySchemes⟩, hbody, hav₂⟩
      simp only [Ys, bodyCtx] at herhs heuni hebody hesc1 hesc2
      rw [inferWithTypesCore, dif_pos (PolyTy.wf_iff_bvarsBelow.mpr hσwf)]
      simp only [herhs, heuni]
      rw [dif_pos hesc1, dif_pos hesc2]
      simp only [hebody]
      rfl

theorem inferCore_complete_letIn {ann : Option PolyTy} {rhs body : Expr}
    (iha : InferCoreComplete rhs)
    (ihao : ∀ Ys, InferCoreComplete (rhs.openTyVars Ys))
    (ihb : InferCoreComplete body) :
    InferCoreComplete (.letIn ann rhs body) := by
  cases ann with
  | none => exact inferCore_complete_letIn_none iha ihb
  | some σ => exact inferCore_complete_letIn_some ihao ihb

/-- Function-completeness for the type-metadata-producing branch worker. The branch
    index affects provenance only, so completeness is uniform in its starting
    value. -/
def InferBranchesCoreComplete (branches : List (MatchPattern × Expr)) : Prop :=
  ∀ {Φ : Nat} {ctx : Ctx} {scrutTy ρ : Ty} {Φ' : Nat} {S : Subst}
      (K : List Nat) (branchIndex : Nat),
    CtxWF ctx → CtxBelow Φ ctx → scrutTy.IsLC → Ty.BelowFvars Φ scrutTy →
    ρ.IsLC → Ty.BelowFvars Φ ρ →
    (∀ k ∈ K, k < Φ) →
    (∀ y ∈ Expr.tyFreeVars.BranchList.tyFreeVars branches, y ∈ K) →
    (∀ p ∈ S, p.1 ∉ K) →
    InferBranches Φ ctx scrutTy ρ branches Φ' S →
    (inferBranchesWithTypesCore K Φ ctx scrutTy ρ branchIndex branches).isSome

theorem inferBranchesWithTypesCore_complete : ∀ (branches : List (MatchPattern × Expr)),
    (∀ br ∈ branches, InferCoreComplete br.2) →
    InferBranchesCoreComplete branches := by
  intro branches
  induction branches with
  | nil =>
      intro _ Φ ctx scrutTy ρ Φ' S K branchIndex _ _ _ _ _ _ _ _ _ _
      simp [inferBranchesWithTypesCore]
  | cons head rest ih =>
      intro ihbr
      obtain ⟨pat, body⟩ := head
      intro Φ ctx scrutTy ρ Φ' S K branchIndex hwf hbelow hscrutLC hbscrut
        hρLC hbρ hKΦ hKbr hSK h
      have hKbody : ∀ y ∈ body.tyFreeVars, y ∈ K := fun y hy => hKbr y (by
        simp only [Expr.tyFreeVars.BranchList.tyFreeVars, List.mem_append]
        exact Or.inl hy)
      have hKrest : ∀ y ∈ Expr.tyFreeVars.BranchList.tyFreeVars rest, y ∈ K :=
        fun y hy => hKbr y (by
          simp only [Expr.tyFreeVars.BranchList.tyFreeVars, List.mem_append]
          exact Or.inr hy)
      have hKfixS : ∀ k ∈ K, S.onTy (.fvar k) = .fvar k :=
        fun k hk => Ty.substFvars_eq_self_of_no_key (fun p hp heq => by
          simp only [Ty.freeVars, List.mem_singleton] at heq
          exact hSK p hp (heq ▸ hk))
      have hsource := InferBranches.sourceSound h hwf hbelow hscrutLC hρLC
        hbscrut hbρ K hKΦ hKbr hSK
      have hSlc : ∀ p ∈ S, p.2.IsLC :=
        (InferBranches.lc h hwf hscrutLC hρLC).2
      have hhead := hsource (pat, body) (List.mem_cons_self ..)
      have hrestSource : ∀ br ∈ rest,
          TypeOfMatchBranch (S.onCtx ctx)
            (br.1, br.2)
            ( (S.onTy scrutTy))
            ( (S.onTy ρ)) :=
        fun br hbr => hsource br (List.mem_cons_of_mem _ hbr)
      cases pat with
      | named c n =>
          cases hhead with
          | mk hspec hctxeq hbodyDecl =>
            rename_i ctor tyArgs instContents
            subst hctxeq
            rcases hspec with ⟨hlookE, hscrutEqRaw, hpcE, hnE, hfields⟩
            have hlook : LookupList.get? ctx.ctors c = some ctor := by
              simpa [Subst.onCtx] using hlookE
            have hpc : ctor.paramCount = tyArgs.length := by
              exact hpcE
            have hn : n = ctor.contents.length := by
              exact hnE
            have hscrutEq : Eq (S.onTy scrutTy)
                (.customTy ctor.tyName tyArgs) := by
              exact hscrutEqRaw
            have hscrutErasedLC : (S.onTy scrutTy).IsLC :=
              Subst.onTy_lc hSlc hscrutLC
            have hcustomLC : (Ty.customTy ctor.tyName tyArgs).IsLC := by
              rwa [hscrutEqRaw] at hscrutErasedLC
            have htyArgsLC : ∀ t ∈ tyArgs, t.IsLC := by
              intro t ht
              cases hcustomLC with | customTy ha => exact ha t ht
            have hcustomFreshLC : (Ty.customTy ctor.tyName
                ((freshVars Φ ctor.paramCount).map (Ty.fvar ·))).IsLC :=
              ContainsBvarsUpTo.customTy (fun t ht => by
                obtain ⟨x, _, rfl⟩ := List.mem_map.mp ht
                exact ContainsBvarsUpTo.fvar)
            obtain ⟨U, hUni0, hUlc, hUK, hUeqS, hfreshU⟩ :=
              customTy_dodge_unifier hbscrut hSlc hKΦ hKfixS htyArgsLC hpc hscrutEq
            have huni0Some :=
              unifyCoreK_complete hscrutLC hcustomFreshLC hUlc hUni0 hUK
            obtain ⟨out0, he0⟩ := Option.isSome_iff_exists.mp huni0Some
            rcases out0 with ⟨S₀, huni0, hav0⟩
            obtain ⟨R₀, hFac₀, hR₀lc, hR₀K⟩ :=
              UnifyRel.greatest_K huni0 U hUlc hUni0 hUK
            have hS₀lc : ∀ p ∈ S₀, p.2.IsLC :=
              UnifyRel.lc huni0 hscrutLC hcustomFreshLC
            have hS₀below : ∀ p ∈ S₀,
                Ty.BelowFvars (Φ + ctor.paramCount) p.2 := by
              apply UnifyRel.belowFvars huni0 (hbscrut.mono (by omega))
              apply Ty.BelowFvars.customTy
              intro t ht
              obtain ⟨x, hx, rfl⟩ := List.mem_map.mp ht
              exact Ty.BelowFvars.fvar (by
                have := freshVars_lt x hx
                omega)
            have hAgree₀ : Subst.AgreesBelow Φ S (S₀ ++ R₀) := by
              intro v hv
              simp only [Subst.onTy_append]
              exact (hUeqS v hv).symm.trans
                (hFac₀ (.fvar v))
            have hmapEq :
                ((((freshVars Φ ctor.paramCount).map (Ty.fvar ·)).map S₀.onTy).map
                    R₀.onTy) = tyArgs := by
              rw [← hfreshU]
              simp only [List.map_map]
              apply List.map_congr_left
              intro x _
              exact (hFac₀ (.fvar x)).symm
            set ta0 : List Ty := (freshVars Φ ctor.paramCount).map (Ty.fvar ·) with hta0
            set taS₀ : List Ty := ta0.map S₀.onTy with htaS₀
            set branchCtx : Ctx :=
              { S₀.onCtx ctx with
                env := (ctor.contents.map (Ty.openWith taS₀)).map PolyTy.mkTrivial ++
                  (S₀.onCtx ctx).env } with hbranchCtx
            have htaS₀lc : ∀ t ∈ taS₀, t.IsLC := by
              intro t ht
              rw [htaS₀] at ht
              obtain ⟨v, hv, rfl⟩ := List.mem_map.mp ht
              rw [hta0] at hv
              obtain ⟨x, _, rfl⟩ := List.mem_map.mp hv
              exact Subst.onTy_lc hS₀lc ContainsBvarsUpTo.fvar
            have htaS₀len : ctor.paramCount = taS₀.length := by
              rw [htaS₀, hta0, List.length_map, List.length_map]
              simp
            have htaS₀bel : ∀ t ∈ taS₀,
                Ty.BelowFvars (Φ + ctor.paramCount) t := by
              intro t ht
              rw [htaS₀] at ht
              obtain ⟨v, hv, rfl⟩ := List.mem_map.mp ht
              rw [hta0] at hv
              obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hv
              exact Subst.onTy_belowFvars hS₀below (.fvar (by
                have := freshVars_lt x hx
                omega))
            have hbodyWF : CtxWF branchCtx := by
              rw [hbranchCtx]
              exact branchBindings_wf (ctorr := ctor) (ta := taS₀)
                (Subst.onCtx_wf hS₀lc hwf) htaS₀lc htaS₀len
            have hbodyBelow : CtxBelow (Φ + ctor.paramCount) branchCtx := by
              rw [hbranchCtx]
              exact branchBindings_below (ctorr := ctor) (ta := taS₀)
                (Subst.onCtx_below hS₀below (by omega) hbelow) htaS₀bel
            have hb1 : R₀.onCtx branchCtx =
                { R₀.onCtx (S₀.onCtx ctx) with
                  env := (ctor.contents.map
                    (Ty.openWith (taS₀.map R₀.onTy))).map PolyTy.mkTrivial ++
                    (R₀.onCtx (S₀.onCtx ctx)).env } := by
              rw [hbranchCtx]
              exact Subst.onCtx_branchBindings (ctorr := ctor) (ta := taS₀)
                (ctx := S₀.onCtx ctx) hR₀lc
            have hargs : taS₀.map R₀.onTy = tyArgs := by
              rw [htaS₀, hta0]
              exact hmapEq
            have hb2' : (R₀.onCtx branchCtx) =
                { (R₀.onCtx (S₀.onCtx ctx)) with
                  env := (( ctor).contents.map
                    (Ty.openWith tyArgs)).map PolyTy.mkTrivial ++
                    (R₀.onCtx (S₀.onCtx ctx)).env } := by
              rw [hb1, hargs]
            have hAgree₀' : Subst.AgreesBelow Φ (S₀ ++ R₀) S := by
              intro v hv
              exact Eq.symm (hAgree₀ v hv)
            have htail : (R₀.onCtx (S₀.onCtx ctx)) =
                (S.onCtx ctx) := by
              have ht : R₀.onCtx (S₀.onCtx ctx) = (S₀ ++ R₀).onCtx ctx := by
                simp only [Subst.onCtx_append]
              rw [ht]
              exact Subst.onCtx_congr hAgree₀' hbelow
            have hbv : ∀ d ∈ ctor.contents,
                ContainsBvarsUpTo tyArgs.length d := by
              intro d hd
              simpa [hpc] using ctor.bound d hd
            have hinst : instContents =
                ctor.contents.map (Ty.openWith tyArgs) :=
              instContents_eq_openWith hfields hbv
            have hprefix : instContents.map PolyTy.mkTrivial =
                (( ctor).contents.map
                  (Ty.openWith tyArgs)).map PolyTy.mkTrivial := by
              rw [hinst]
            have hctxBridge :
                { (S.onCtx ctx) with
                  env := instContents.map PolyTy.mkTrivial ++
                    (S.onCtx ctx).env } =
                (R₀.onCtx branchCtx) := by
              rw [hb2']
              simp only [htail]
              congr 1
              rw [hprefix]
            have hbodyAlg : TypeOfHM (R₀.onCtx branchCtx)
                body ( (S.onTy ρ)) := by
              rw [hctxBridge] at hbodyDecl
              exact hbodyDecl
            have hKΦbody : ∀ k ∈ K, k < Φ + ctor.paramCount :=
              fun k hk => by have := hKΦ k hk; omega
            obtain ⟨_, _, _, _, hbodyRel, _, _, _, _, hSbK⟩ :=
              (Infer.complete body) K hbodyWF hbodyBelow hR₀lc
                hKΦbody hKbody hR₀K hbodyAlg
            have hbodySome :=
              (ihbr (.named c n, body) (List.mem_cons_self ..)) K hbodyWF
                hbodyBelow hKΦbody hKbody hSbK hbodyRel
            obtain ⟨bodyResult, hebody⟩ := Option.isSome_iff_exists.mp hbodySome
            rcases bodyResult with
              ⟨⟨Φ₁, S₁, τb, bodyOut, bodySchemes⟩, hbodyActual, hav1⟩
            obtain ⟨R₁, hR₁lc, hAgreeTy₁, hR₁K, hAgree₁⟩ :=
              Infer.complete' hbodyActual hbodyWF hbodyBelow hR₀lc K
                hKΦbody hKbody hR₀K hbodyAlg
            have hle0 : Φ + ctor.paramCount ≤ Φ₁ :=
              Infer.frontier_le hbodyActual
            obtain ⟨hτbLC, hS₁lc⟩ := Infer.lc hbodyActual hbodyWF
            have hΦbody : ∀ y ∈ body.tyFreeVars, y < Φ + ctor.paramCount :=
              fun y hy => by have := hKΦ y (hKbody y hy); omega
            obtain ⟨hτbBel, hS₁bel⟩ :=
              Infer.belowFvars hbodyActual hbodyBelow hΦbody
            have hS₀ρbel : Ty.BelowFvars (Φ + ctor.paramCount) (S₀.onTy ρ) :=
              Subst.onTy_belowFvars hS₀below (hbρ.mono (by omega))
            have hS₀scrutbel : Ty.BelowFvars (Φ + ctor.paramCount)
                (S₀.onTy scrutTy) :=
              Subst.onTy_belowFvars hS₀below (hbscrut.mono (by omega))
            have hρAgree : Eq (S.onTy ρ)
                (R₁.onTy (S₁.onTy (S₀.onTy ρ))) := by
              have h0 : Eq (S.onTy ρ) (R₀.onTy (S₀.onTy ρ)) := by
                have ht := Subst.onTy_congr hAgree₀ hbρ
                simpa [Subst.onTy_append] using ht
              have h1 : Eq (R₀.onTy (S₀.onTy ρ))
                  (R₁.onTy (S₁.onTy (S₀.onTy ρ))) := by
                have ht := Subst.onTy_congr hAgree₁ hS₀ρbel
                simpa [Subst.onTy_append] using ht
              exact Eq.trans h0 h1
            have hAgreeTy₁' : Eq (R₁.onTy τb) (S.onTy ρ) :=
              Eq.symm hAgreeTy₁
            have hUnifies₁ : Unifies R₁ τb (S₁.onTy (S₀.onTy ρ)) := by
              rw [Unifies]
              exact Eq.trans hAgreeTy₁' hρAgree
            have hρInputLC : (S₁.onTy (S₀.onTy ρ)).IsLC :=
              Subst.onTy_lc hS₁lc (Subst.onTy_lc hS₀lc hρLC)
            have huniSome :=
              unifyCoreK_complete hτbLC hρInputLC hR₁lc hUnifies₁ hR₁K
            obtain ⟨uniResult, heuni⟩ := Option.isSome_iff_exists.mp huniSome
            rcases uniResult with ⟨S₂, huni, hav2⟩
            obtain ⟨R₂, hFac₂, hR₂lc, hR₂K⟩ :=
              UnifyRel.greatest_K huni R₁ hR₁lc hUnifies₁ hR₁K
            have hAgree₂ : Subst.AgreesBelow Φ₁ R₁ (S₂ ++ R₂) := by
              intro v _
              simp only [Subst.onTy_append]
              exact hFac₂ (.fvar v)
            have hS₂lc : ∀ p ∈ S₂, p.2.IsLC :=
              UnifyRel.lc huni hτbLC hρInputLC
            have hS₀ρbel₁ : Ty.BelowFvars Φ₁ (S₀.onTy ρ) :=
              hS₀ρbel.mono hle0
            have hS₀scrutbel₁ : Ty.BelowFvars Φ₁ (S₀.onTy scrutTy) :=
              hS₀scrutbel.mono hle0
            have hS₁ρbel : Ty.BelowFvars Φ₁ (S₁.onTy (S₀.onTy ρ)) :=
              Subst.onTy_belowFvars hS₁bel hS₀ρbel₁
            have hS₁scrutbel : Ty.BelowFvars Φ₁ (S₁.onTy (S₀.onTy scrutTy)) :=
              Subst.onTy_belowFvars hS₁bel hS₀scrutbel₁
            have hS₂bel : ∀ p ∈ S₂, Ty.BelowFvars Φ₁ p.2 :=
              UnifyRel.belowFvars huni hτbBel hS₁ρbel
            have hwf' : CtxWF (S₂.onCtx (S₁.onCtx (S₀.onCtx ctx))) :=
              Subst.onCtx_wf hS₂lc
                (Subst.onCtx_wf hS₁lc (Subst.onCtx_wf hS₀lc hwf))
            have hbelow' : CtxBelow Φ₁
                (S₂.onCtx (S₁.onCtx (S₀.onCtx ctx))) :=
              Subst.onCtx_below hS₂bel (le_refl _)
                (Subst.onCtx_below hS₁bel (le_refl _)
                  (Subst.onCtx_below (fun p hp => (hS₀below p hp).mono hle0)
                    (by omega) hbelow))
            have hscrutLC' :
                (S₂.onTy (S₁.onTy (S₀.onTy scrutTy))).IsLC :=
              Subst.onTy_lc hS₂lc
                (Subst.onTy_lc hS₁lc (Subst.onTy_lc hS₀lc hscrutLC))
            have hbscrut' : Ty.BelowFvars Φ₁
                (S₂.onTy (S₁.onTy (S₀.onTy scrutTy))) :=
              Subst.onTy_belowFvars hS₂bel hS₁scrutbel
            have hρ' : (S₂.onTy (S₁.onTy (S₀.onTy ρ))).IsLC :=
              Subst.onTy_lc hS₂lc
                (Subst.onTy_lc hS₁lc (Subst.onTy_lc hS₀lc hρLC))
            have hbρ' : Ty.BelowFvars Φ₁
                (S₂.onTy (S₁.onTy (S₀.onTy ρ))) :=
              Subst.onTy_belowFvars hS₂bel hS₁ρbel
            have hKΦ₁ : ∀ k ∈ K, k < Φ₁ :=
              fun k hk => by have := hKΦ k hk; omega
            have hAgree₀₁ : Subst.AgreesBelow (Φ + ctor.paramCount) R₀
                ((S₁ ++ S₂) ++ R₂) :=
              Subst.AgreesBelow.trans_append hle0 hAgree₁ hS₁bel hAgree₂
            have hAgreeFull : Subst.AgreesBelow Φ S
                ((S₀ ++ (S₁ ++ S₂)) ++ R₂) :=
              Subst.AgreesBelow.trans_append (by omega) hAgree₀ hS₀below hAgree₀₁
            have hAgreeFull' : Subst.AgreesBelow Φ
                ((S₀ ++ (S₁ ++ S₂)) ++ R₂) S :=
              fun v hv => Eq.symm (hAgreeFull v hv)
            have hctxEq :
                (R₂.onCtx (S₂.onCtx (S₁.onCtx (S₀.onCtx ctx)))) =
                  (S.onCtx ctx) := by
              have heq : R₂.onCtx (S₂.onCtx (S₁.onCtx (S₀.onCtx ctx))) =
                  ((S₀ ++ (S₁ ++ S₂)) ++ R₂).onCtx ctx := by
                simp only [Subst.onCtx_append]
              rw [heq]
              exact Subst.onCtx_congr hAgreeFull' hbelow
            have hscrutEq' :
                (R₂.onTy (S₂.onTy (S₁.onTy (S₀.onTy scrutTy)))) =
                 (S.onTy scrutTy) := by
              have ht := Subst.onTy_congr hAgreeFull' hbscrut
              simpa [Subst.onTy_append] using ht
            have hρEq' :
                (R₂.onTy (S₂.onTy (S₁.onTy (S₀.onTy ρ)))) =
                 (S.onTy ρ) := by
              have ht := Subst.onTy_congr hAgreeFull' hbρ
              simpa [Subst.onTy_append] using ht
            have hrestDecl : ∀ br ∈ rest, TypeOfMatchBranch
                (R₂.onCtx (S₂.onCtx (S₁.onCtx (S₀.onCtx ctx))))
                (br.1, br.2)
                ( (R₂.onTy
                  (S₂.onTy (S₁.onTy (S₀.onTy scrutTy)))))
                ( (R₂.onTy
                  (S₂.onTy (S₁.onTy (S₀.onTy ρ))))) := by
              intro br hbr
              have ht := hrestSource br hbr
              rw [← hctxEq, ← hscrutEq', ← hρEq'] at ht
              exact ht
            obtain ⟨_, _, _, hrestRel, _, _, _, hSrestK⟩ :=
              InferBranches.complete K (fun br _ => Infer.complete br.2)
                hwf' hbelow' hscrutLC' hbscrut' hρ' hbρ' hR₂lc
                hKΦ₁ hKrest hR₂K hrestDecl
            have hrestSome := ih
              (fun br hbr => ihbr br (List.mem_cons_of_mem _ hbr)) K
              (branchIndex + 1) hwf' hbelow' hscrutLC' hbscrut' hρ' hbρ'
              hKΦ₁ hKrest hSrestK hrestRel
            obtain ⟨restResult, herest⟩ := Option.isSome_iff_exists.mp hrestSome
            rcases restResult with
              ⟨⟨Φ₂, S₃, restOut, restSchemes⟩, hrestActual, hav3⟩
            simp only [branchCtx, taS₀, ta0] at hebody
            rw [inferBranchesWithTypesCore]
            split
            · rename_i hnone
              rw [hlook] at hnone
              simp at hnone
            · rename_i ctorr hsome
              obtain rfl : ctorr = ctor := by
                rw [hlook] at hsome
                exact (Option.some.inj hsome).symm
              rw [dif_pos hn]
              simp only [he0, hebody, heuni, herest, Option.isSome_some]
      | wildcard =>
          cases hhead with
          | wildcard hbodyDecl =>
            obtain ⟨_, _, _, _, hbodyRel, _, _, _, _, hSbK⟩ :=
              (Infer.complete body) K hwf hbelow hSlc hKΦ hKbody
                hKfixS hbodyDecl
            have hbodySome :=
              (ihbr (.wildcard, body) (List.mem_cons_self ..)) K hwf hbelow
                hKΦ hKbody hSbK hbodyRel
            obtain ⟨bodyResult, hebody⟩ := Option.isSome_iff_exists.mp hbodySome
            rcases bodyResult with
              ⟨⟨Φ₁, S₁, τb, bodyOut, bodySchemes⟩, hbodyActual, hav1⟩
            obtain ⟨R₁, hR₁lc, hAgreeTy₁, hR₁K, hAgree₁⟩ :=
              Infer.complete' hbodyActual hwf hbelow hSlc K hKΦ hKbody
                hKfixS hbodyDecl
            have hle : Φ ≤ Φ₁ := Infer.frontier_le hbodyActual
            obtain ⟨hτbLC, hS₁lc⟩ := Infer.lc hbodyActual hwf
            obtain ⟨hτbBel, hS₁bel⟩ := Infer.belowFvars hbodyActual hbelow
              (fun y hy => hKΦ y (hKbody y hy))
            have hρAgree : Eq (S.onTy ρ)
                (R₁.onTy (S₁.onTy ρ)) := by
              have ht := Subst.onTy_congr hAgree₁ hbρ
              simpa [Subst.onTy_append] using ht
            have hAgreeTy₁' : Eq (R₁.onTy τb) (S.onTy ρ) :=
              Eq.symm hAgreeTy₁
            have hUnifies₁ : Unifies R₁ τb (S₁.onTy ρ) := by
              rw [Unifies]
              exact Eq.trans hAgreeTy₁' hρAgree
            have hρInputLC : (S₁.onTy ρ).IsLC :=
              Subst.onTy_lc hS₁lc hρLC
            have huniSome :=
              unifyCoreK_complete hτbLC hρInputLC hR₁lc hUnifies₁ hR₁K
            obtain ⟨uniResult, heuni⟩ := Option.isSome_iff_exists.mp huniSome
            rcases uniResult with ⟨S₂, huni, hav2⟩
            obtain ⟨R₂, hFac₂, hR₂lc, hR₂K⟩ :=
              UnifyRel.greatest_K huni R₁ hR₁lc hUnifies₁ hR₁K
            have hAgree₂ : Subst.AgreesBelow Φ₁ R₁ (S₂ ++ R₂) := by
              intro v _
              simp only [Subst.onTy_append]
              exact hFac₂ (.fvar v)
            have hS₂lc : ∀ p ∈ S₂, p.2.IsLC :=
              UnifyRel.lc huni hτbLC hρInputLC
            have hρBel₁ : Ty.BelowFvars Φ₁ (S₁.onTy ρ) :=
              Subst.onTy_belowFvars hS₁bel (hbρ.mono hle)
            have hscrutBel₁ : Ty.BelowFvars Φ₁ (S₁.onTy scrutTy) :=
              Subst.onTy_belowFvars hS₁bel (hbscrut.mono hle)
            have hS₂bel : ∀ p ∈ S₂, Ty.BelowFvars Φ₁ p.2 :=
              UnifyRel.belowFvars huni hτbBel hρBel₁
            have hwf' : CtxWF (S₂.onCtx (S₁.onCtx ctx)) :=
              Subst.onCtx_wf hS₂lc (Subst.onCtx_wf hS₁lc hwf)
            have hbelow' : CtxBelow Φ₁ (S₂.onCtx (S₁.onCtx ctx)) :=
              Subst.onCtx_below hS₂bel (le_refl _)
                (Subst.onCtx_below hS₁bel hle hbelow)
            have hscrutLC' : (S₂.onTy (S₁.onTy scrutTy)).IsLC :=
              Subst.onTy_lc hS₂lc (Subst.onTy_lc hS₁lc hscrutLC)
            have hbscrut' : Ty.BelowFvars Φ₁ (S₂.onTy (S₁.onTy scrutTy)) :=
              Subst.onTy_belowFvars hS₂bel hscrutBel₁
            have hρ' : (S₂.onTy (S₁.onTy ρ)).IsLC :=
              Subst.onTy_lc hS₂lc (Subst.onTy_lc hS₁lc hρLC)
            have hbρ' : Ty.BelowFvars Φ₁ (S₂.onTy (S₁.onTy ρ)) :=
              Subst.onTy_belowFvars hS₂bel hρBel₁
            have hKΦ₁ : ∀ k ∈ K, k < Φ₁ :=
              fun k hk => lt_of_lt_of_le (hKΦ k hk) hle
            have hAgreeFull : Subst.AgreesBelow Φ S
                ((S₁ ++ S₂) ++ R₂) :=
              Subst.AgreesBelow.trans_append hle hAgree₁ hS₁bel hAgree₂
            have hAgreeFull' : Subst.AgreesBelow Φ ((S₁ ++ S₂) ++ R₂) S :=
              fun v hv => Eq.symm (hAgreeFull v hv)
            have hctxEq : (R₂.onCtx (S₂.onCtx (S₁.onCtx ctx))) =
                (S.onCtx ctx) := by
              have heq : R₂.onCtx (S₂.onCtx (S₁.onCtx ctx)) =
                  ((S₁ ++ S₂) ++ R₂).onCtx ctx := by
                simp only [Subst.onCtx_append]
              rw [heq]
              exact Subst.onCtx_congr hAgreeFull' hbelow
            have hscrutEq' :
                (R₂.onTy (S₂.onTy (S₁.onTy scrutTy))) =
                 (S.onTy scrutTy) := by
              have ht := Subst.onTy_congr hAgreeFull' hbscrut
              simpa [Subst.onTy_append] using ht
            have hρEq' :  (R₂.onTy (S₂.onTy (S₁.onTy ρ))) =
                 (S.onTy ρ) := by
              have ht := Subst.onTy_congr hAgreeFull' hbρ
              simpa [Subst.onTy_append] using ht
            have hrestDecl : ∀ br ∈ rest, TypeOfMatchBranch
                (R₂.onCtx (S₂.onCtx (S₁.onCtx ctx)))
                (br.1, br.2)
                ( (R₂.onTy (S₂.onTy (S₁.onTy scrutTy))))
                ( (R₂.onTy (S₂.onTy (S₁.onTy ρ)))) := by
              intro br hbr
              have ht := hrestSource br hbr
              rw [← hctxEq, ← hscrutEq', ← hρEq'] at ht
              exact ht
            obtain ⟨_, _, _, hrestRel, _, _, _, hSrestK⟩ :=
              InferBranches.complete K (fun br _ => Infer.complete br.2)
                hwf' hbelow' hscrutLC' hbscrut' hρ' hbρ' hR₂lc
                hKΦ₁ hKrest hR₂K hrestDecl
            have hrestSome := ih
              (fun br hbr => ihbr br (List.mem_cons_of_mem _ hbr)) K
              (branchIndex + 1) hwf' hbelow' hscrutLC' hbscrut' hρ' hbρ'
              hKΦ₁ hKrest hSrestK hrestRel
            obtain ⟨restResult, herest⟩ := Option.isSome_iff_exists.mp hrestSome
            rcases restResult with
              ⟨⟨Φ₂, S₃, restOut, restSchemes⟩, hrestActual, hav3⟩
            rw [inferBranchesWithTypesCore]
            simp only [hebody, heuni, herest, Option.isSome_some]

/-- Executable completeness for matches.  The scrutinee worker fixes the
    concrete first phase; a fresh residual realizes the declarative result type
    at the worker's reserved result variable, after which branch-list
    completeness runs at provenance index zero. -/
theorem inferCore_complete_match {scrut : Expr}
    {branches : List (MatchPattern × Expr)}
    (ihscrut : InferCoreComplete scrut)
    (ihbranches : ∀ br ∈ branches, InferCoreComplete br.2) :
    InferCoreComplete (.match_ scrut branches) := by
  intro Φ ctx Φ' S τ K hwf hbelow hKΦ hKe hSK h
  simp only [Expr.tyFreeVars, List.mem_append] at hKe
  have hKscrut : ∀ y ∈ scrut.tyFreeVars, y ∈ K :=
    fun y hy => hKe y (.inl hy)
  have hKbr : ∀ y ∈ Expr.tyFreeVars.BranchList.tyFreeVars branches, y ∈ K :=
    fun y hy => hKe y (.inr hy)
  let resultTy : Ty :=  τ
  have hsource := Infer.sourceSound h hwf hbelow K hKΦ
    (fun y hy => hKe y (by simpa [Expr.tyFreeVars] using hy)) hSK
  simp only [] at hsource
  have hsource' : TypeOfHM ((S.onCtx ctx))
      (.match_ scrut
        (branches.map fun pe => (pe.1, pe.2))) resultTy := by
    simpa [resultTy] using hsource
  have hSlc : ∀ p ∈ S, p.2.IsLC := (Infer.lc h hwf).2
  cases h with
  | @match_ _ _ _ _ Φ₁d Φ₂d S₁d S₂d τsd hscrutD hne hbranchesD =>
      cases hsource' with
      | match_ hscrutDecl hneSource hbranchesSource =>
        rename_i scrutTy
        obtain ⟨b0, rest, hcons⟩ := List.exists_cons_of_ne_nil hne
        subst hcons
        have hKfixS : ∀ k ∈ K, (S₁d ++ S₂d).onTy (.fvar k) = .fvar k :=
          fun k hk => Ty.substFvars_eq_self_of_no_key (fun p hp heq => by
            simp only [Ty.freeVars, List.mem_singleton] at heq
            exact hSK p hp (heq ▸ hk))
        have hSK₁ : ∀ p ∈ S₁d, p.1 ∉ K :=
          fun p hp => hSK p (List.mem_append_left _ hp)
        have hbranchesDecl : ∀ br ∈ b0 :: rest,
            TypeOfMatchBranch ((S₁d ++ S₂d).onCtx ctx)
              (br.1, br.2) scrutTy resultTy := by
          intro br hbr
          exact hbranchesSource (br.1, br.2) (by
            apply List.mem_map.mpr
            exact ⟨br, hbr, rfl⟩)
        have hτLC : resultTy.IsLC :=
          TypeOfMatchBranch.regular
            (hbranchesDecl b0 (List.mem_cons_self ..))
        have hscrutSome := ihscrut K hwf hbelow hKΦ hKscrut hSK₁
          hscrutD
        obtain ⟨scrutResult, hescrut⟩ :=
          Option.isSome_iff_exists.mp hscrutSome
        rcases scrutResult with
          ⟨⟨Φ₁, S₁, τs, scrutOut, scrutSchemes⟩, hscrutActual, hav1⟩
        obtain ⟨R₁, hR₁lc, hAgreeScrutTy, hR₁K, hAgreeScrut⟩ :=
          Infer.complete' hscrutActual hwf hbelow hSlc K hKΦ hKscrut
            hKfixS hscrutDecl
        have hfle : Φ ≤ Φ₁ := Infer.frontier_le hscrutActual
        obtain ⟨hτsLC, hS₁lc⟩ := Infer.lc hscrutActual hwf
        obtain ⟨hτsBel, hS₁bel⟩ := Infer.belowFvars hscrutActual hbelow
          (fun y hy => hKΦ y (hKscrut y hy))
        have hwf₁ : CtxWF (S₁.onCtx ctx) := Subst.onCtx_wf hS₁lc hwf
        have hbelow₁ : CtxBelow Φ₁ (S₁.onCtx ctx) :=
          Subst.onCtx_below hS₁bel hfle hbelow
        have hbelowBranches : CtxBelow (Φ₁ + 1) (S₁.onCtx ctx) :=
          fun M hM => (hbelow₁ M hM).mono (by omega)
        have hKΦ₁ : ∀ k ∈ K, k < Φ₁ :=
          fun k hk => lt_of_lt_of_le (hKΦ k hk) hfle
        have hKΦBranches : ∀ k ∈ K, k < Φ₁ + 1 :=
          fun k hk => Nat.lt_succ_of_lt (hKΦ₁ k hk)
        have hτsBel' : Ty.BelowFvars (Φ₁ + 1) τs :=
          hτsBel.mono (by omega)
        obtain ⟨R₁', hR₁'lc, hR₁'K, hR₁'Φ₁, hR₁'below⟩ :=
          exists_residual_at_fresh (Φ := Φ₁) (R := R₁) (K := K)
            hR₁lc hτLC hR₁K hKΦ₁
        have hR₁'agreeR₁ : Subst.AgreesBelow Φ₁ R₁' R₁ := by
          intro v hv
          rw [hR₁'below v hv]
        have hAgreeScrut' : Subst.AgreesBelow Φ (S₁ ++ R₁) (S₁d ++ S₂d) :=
          fun v hv => Eq.symm (hAgreeScrut v hv)
        have hctxEq : (R₁'.onCtx (S₁.onCtx ctx)) =
            ((S₁d ++ S₂d).onCtx ctx) := by
          calc
            (R₁'.onCtx (S₁.onCtx ctx)) =
                (R₁.onCtx (S₁.onCtx ctx)) :=
              Subst.onCtx_congr hR₁'agreeR₁ hbelow₁
            _ = ((S₁d ++ S₂d).onCtx ctx) := by
              rw [← Subst.onCtx_append]
              exact Subst.onCtx_congr hAgreeScrut' hbelow
        have hscrutEq :  (R₁'.onTy τs) =
             scrutTy := by
          calc
             (R₁'.onTy τs) =  (R₁.onTy τs) :=
              Subst.onTy_congr hR₁'agreeR₁ hτsBel
            _ =  scrutTy := Eq.symm hAgreeScrutTy
        have hbranchesAlg : ∀ br ∈ b0 :: rest,
            TypeOfMatchBranch (R₁'.onCtx (S₁.onCtx ctx))
              (br.1, br.2)
              ( (R₁'.onTy τs))
              ( (R₁'.onTy (.fvar Φ₁))) := by
          intro br hbr
          simpa [hctxEq, hscrutEq, hR₁'Φ₁] using
            (hbranchesDecl br hbr)
        obtain ⟨_, _, _, hbranchesRel, _, _, _, hSbranchesK⟩ :=
          @InferBranches.complete (b0 :: rest) (Φ₁ + 1) (S₁.onCtx ctx)
            τs (.fvar Φ₁) R₁' K
            (fun br _ => Infer.complete br.2) hwf₁
            hbelowBranches hτsLC hτsBel' ContainsBvarsUpTo.fvar
            (.fvar (by omega)) hR₁'lc hKΦBranches hKbr hR₁'K hbranchesAlg
        have hbranchesSome := inferBranchesWithTypesCore_complete (b0 :: rest)
          ihbranches K 0 hwf₁ hbelowBranches hτsLC hτsBel'
          ContainsBvarsUpTo.fvar (.fvar (by omega)) hKΦBranches hKbr
          hSbranchesK hbranchesRel
        obtain ⟨branchesResult, hebranches⟩ :=
          Option.isSome_iff_exists.mp hbranchesSome
        rcases branchesResult with
          ⟨⟨Φ₂, S₂, branchesOut, branchSchemes⟩, hbranchesActual, hav2⟩
        rw [inferWithTypesCore, hescrut]
        simp only [List.head?_cons, hebranches, Option.isSome_some]
/-- Executable producer completeness for an all-monomorphic recursion-group
thread. Besides success of the concrete metadata-producing worker, the result
carries the residual needed by the outer `letRec` ceiling phase. -/
theorem inferRecGroupWithTypesCore_complete_mono
    {Φ : Nat} {ctx : Ctx} {bindings : List Expr} {specs : List RecSpec}
    {S₀ : Subst} {K : List Nat} (memberIndex : Nat)
    (ihRel : ∀ e ∈ bindings, Infer.CompleteAt e)
    (ihExec : ∀ e ∈ bindings, InferCoreComplete e)
    (hlen : bindings.length = specs.length)
    (hwf : CtxWF ctx) (hbelow : CtxBelow Φ ctx)
    (hS₀ : ∀ p ∈ S₀, p.2.IsLC)
    (hKΦ : ∀ k ∈ K, k < Φ)
    (hKtv : ∀ y ∈ Expr.tyFreeVars.RecGroup.tyFreeVars bindings, y ∈ K)
    (hKfix : ∀ k ∈ K, S₀.onTy (.fvar k) = .fvar k)
    (hspecLC : ∀ s ∈ specs, s.LC)
    (hspecBelow : ∀ s ∈ specs, ∀ τ, s = .mono τ → Ty.BelowFvars Φ τ)
    (hspecMono : ∀ s ∈ specs, ∃ τ, s = .mono τ)
    (hdecl : ∀ p ∈ bindings.zip specs, ∀ τ, p.2 = .mono τ →
      TypeOfHM (S₀.onCtx ctx) p.1
        ( (S₀.onTy τ))) :
    ∃ out R,
      inferRecGroupWithTypesCore K Φ ctx memberIndex bindings specs = some out ∧
      Subst.AgreesBelow Φ S₀ (out.1.2.1 ++ R) ∧
      (∀ p ∈ R, p.2.IsLC) ∧
      (∀ k ∈ K, R.onTy (.fvar k) = .fvar k) := by
  induction bindings generalizing Φ ctx specs S₀ memberIndex hwf hbelow hS₀ hKΦ hKfix
    hspecLC hspecBelow hspecMono with
  | nil =>
    cases specs with
    | nil =>
      let out : { r : Nat × Subst × InferredNodeTypes × InferredBinderSchemes //
          InferRecGroup Φ ctx [] [] r.1 r.2.1 ∧ (∀ p ∈ r.2.1, p.1 ∉ K) } :=
        ⟨(Φ, [], [], []), .nil, by simp⟩
      refine ⟨out, S₀, ?_, ?_, hS₀, hKfix⟩
      · simp [out, inferRecGroupWithTypesCore]
      · intro v hv
        exact Eq.refl _
    | cons s ss => simp at hlen
  | cons e rest ihrec =>
    cases specs with
    | nil => simp at hlen
    | cons s ss =>
      obtain ⟨τ, hs⟩ := hspecMono s List.mem_cons_self
      subst s
      have hrest_len : rest.length = ss.length := by simpa using hlen
      have hheadRel : Infer.CompleteAt e := ihRel e List.mem_cons_self
      have hrestRel : ∀ e' ∈ rest, Infer.CompleteAt e' := fun e' he' =>
        ihRel e' (List.mem_cons_of_mem _ he')
      have hheadExec : InferCoreComplete e := ihExec e List.mem_cons_self
      have hrestExec : ∀ e' ∈ rest, InferCoreComplete e' := fun e' he' =>
        ihExec e' (List.mem_cons_of_mem _ he')
      have hKe : ∀ y ∈ e.tyFreeVars, y ∈ K := fun y hy =>
        hKtv y (by simp [Expr.tyFreeVars.RecGroup.tyFreeVars, hy])
      have hKrest : ∀ y ∈ Expr.tyFreeVars.RecGroup.tyFreeVars rest, y ∈ K := fun y hy =>
        hKtv y (by simp [Expr.tyFreeVars.RecGroup.tyFreeVars, hy])
      have hτbelow : Ty.BelowFvars Φ τ :=
        hspecBelow (.mono τ) List.mem_cons_self τ rfl
      have hτlc : τ.IsLC := by
        have := hspecLC (.mono τ) List.mem_cons_self
        simpa using this
      have hheadDecl : TypeOfHM (S₀.onCtx ctx) e
          ( (S₀.onTy τ)) :=
        hdecl (e, .mono τ) (by simp) τ rfl
      obtain ⟨_, _, _, _, hSeed, _, _, _, _, hSeedK⟩ :=
        hheadRel K hwf hbelow hS₀ hKΦ hKe hKfix hheadDecl
      have hHeadSome := hheadExec K hwf hbelow hKΦ hKe hSeedK hSeed
      obtain ⟨outE, heinfer⟩ := Option.isSome_iff_exists.mp hHeadSome
      obtain ⟨⟨Φ₁, S₁, τe, eNodeTypes, eSchemes⟩, hInferE, hS₁K⟩ := outE
      obtain ⟨R₁, hR₁lc, hAgreeTy, hR₁K, hAgreeE⟩ :=
        Infer.complete' hInferE hwf hbelow hS₀ K hKΦ hKe hKfix hheadDecl
      have hΦ₁ : Φ ≤ Φ₁ := Infer.frontier_le hInferE
      have hKΦ₁ : ∀ k ∈ K, k < Φ₁ := fun k hk =>
        lt_of_lt_of_le (hKΦ k hk) hΦ₁
      have hE_lc := Infer.lc hInferE hwf
      have hτeLC : τe.IsLC := hE_lc.1
      have hS₁lc : ∀ p ∈ S₁, p.2.IsLC := hE_lc.2
      have hE_below := Infer.belowFvars hInferE hbelow
        (fun y hy => hKΦ y (hKe y hy))
      have hτeBelow : Ty.BelowFvars Φ₁ τe := hE_below.1
      have hS₁Below : ∀ p ∈ S₁, Ty.BelowFvars Φ₁ p.2 := hE_below.2
      have hτAfterLC : (S₁.onTy τ).IsLC := Subst.onTy_lc hS₁lc hτlc
      have hTarget : Eq (S₀.onTy τ) (R₁.onTy (S₁.onTy τ)) := by
        simpa [Subst.onTy_append] using
          (Subst.onTy_congr hAgreeE hτbelow)
      have hUni : Unifies R₁ τe (S₁.onTy τ) := by
        apply Eq.trans hAgreeTy.symm
        exact hTarget
      have hUnifySome : (unifyCoreK K τe (S₁.onTy τ)).isSome :=
        unifyCoreK_complete hτeLC hτAfterLC hR₁lc hUni hR₁K
      obtain ⟨outU, heuni⟩ := Option.isSome_iff_exists.mp hUnifySome
      obtain ⟨S₂, hS₂uni, hS₂K⟩ := outU
      obtain ⟨R₂, hR₂fac, hR₂lc, hR₂K⟩ :=
        UnifyRel.greatest_K hS₂uni R₁ hR₁lc hUni hR₁K
      have hS₂lc : ∀ p ∈ S₂, p.2.IsLC :=
        UnifyRel.lc hS₂uni hτeLC hτAfterLC
      have hτAfterBelow : Ty.BelowFvars Φ₁ (S₁.onTy τ) :=
        Subst.onTy_belowFvars hS₁Below (hτbelow.mono hΦ₁)
      have hS₂Below : ∀ p ∈ S₂, Ty.BelowFvars Φ₁ p.2 :=
        UnifyRel.belowFvars hS₂uni hτeBelow hτAfterBelow
      have hAgreeUni : Subst.AgreesBelow Φ₁ R₁ (S₂ ++ R₂) := by
        intro v hv
        rw [Subst.onTy_append]
        exact hR₂fac (.fvar v)
      have hAgreeHead : Subst.AgreesBelow Φ S₀ ((S₁ ++ S₂) ++ R₂) :=
        @Subst.AgreesBelow.trans_append Φ Φ₁ S₀ S₁ R₁ S₂ R₂
          hΦ₁ hAgreeE hS₁Below hAgreeUni
      have hctxWF : CtxWF (S₂.onCtx (S₁.onCtx ctx)) :=
        Subst.onCtx_wf hS₂lc (Subst.onCtx_wf hS₁lc hwf)
      have hctxBelow : CtxBelow Φ₁ (S₂.onCtx (S₁.onCtx ctx)) :=
        Subst.onCtx_below hS₂Below (le_refl _)
          (Subst.onCtx_below hS₁Below hΦ₁ hbelow)
      have hctxEq : (R₂.onCtx (S₂.onCtx (S₁.onCtx ctx))) =
          (S₀.onCtx ctx) := by
        rw [← Subst.onCtx_append]
        simpa [Subst.onCtx_append, List.append_assoc] using
          (Subst.onCtx_congr hAgreeHead hbelow).symm
      have hssLC : ∀ s' ∈ ss.map (RecSpec.onSubst (S₁ ++ S₂)), s'.LC := by
        intro s' hs'
        obtain ⟨s0, hs0, rfl⟩ := List.mem_map.mp hs'
        apply RecSpec.LC.onSubst
        intro p hp
        rcases List.mem_append.mp hp with hp | hp
        · exact hS₁lc p hp
        · exact hS₂lc p hp
        exact hspecLC s0 (List.mem_cons_of_mem _ hs0)
      have hssMono : ∀ s' ∈ ss.map (RecSpec.onSubst (S₁ ++ S₂)),
          ∃ τ', s' = .mono τ' := by
        intro s' hs'
        obtain ⟨s0, hs0, rfl⟩ := List.mem_map.mp hs'
        obtain ⟨τ0, hτ0⟩ := hspecMono s0 (List.mem_cons_of_mem _ hs0)
        subst s0
        exact ⟨(S₁ ++ S₂).onTy τ0, rfl⟩
      have hssBelow : ∀ s' ∈ ss.map (RecSpec.onSubst (S₁ ++ S₂)), ∀ τ',
          s' = .mono τ' → Ty.BelowFvars Φ₁ τ' := by
        intro s' hs' τ' hmono
        obtain ⟨s0, hs0, rfl⟩ := List.mem_map.mp hs'
        obtain ⟨τ0, hτ0⟩ := hspecMono s0 (List.mem_cons_of_mem _ hs0)
        subst s0
        simp only [RecSpec.onSubst] at hmono
        cases hmono
        apply Subst.onTy_belowFvars
        · intro p hp
          rcases List.mem_append.mp hp with hp | hp
          · exact (hS₁Below p hp).mono (le_refl _)
          · exact hS₂Below p hp
        · exact (hspecBelow (.mono τ0) (List.mem_cons_of_mem _ hs0) τ0 rfl).mono hΦ₁
      have hdeclTail : ∀ p ∈ rest.zip (ss.map (RecSpec.onSubst (S₁ ++ S₂))),
          ∀ τ', p.2 = .mono τ' →
          TypeOfHM (R₂.onCtx (S₂.onCtx (S₁.onCtx ctx))) p.1
            ( (R₂.onTy τ')) := by
        intro p hp τ' hmono
        rcases List.mem_zip_map_right hp with ⟨e', s0, hp0, rfl⟩
        obtain ⟨τ0, hτ0⟩ := hspecMono s0 (List.mem_cons_of_mem _ (List.of_mem_zip hp0).2)
        subst s0
        simp only [RecSpec.onSubst] at hmono
        cases hmono
        have hold : TypeOfHM (S₀.onCtx ctx) e'
            ( (S₀.onTy τ0)) :=
          hdecl (e', .mono τ0)
            (by rw [List.zip_cons_cons]; exact List.mem_cons_of_mem _ hp0) τ0 rfl
        rw [hctxEq]
        have htype : Eq (S₀.onTy τ0)
            (R₂.onTy ((S₁ ++ S₂).onTy τ0)) := by
          simpa [Subst.onTy_append] using
            (Subst.onTy_congr hAgreeHead
              ((hspecBelow (.mono τ0) (List.mem_cons_of_mem _ (List.of_mem_zip hp0).2)
                τ0 rfl)))
        rw [htype] at hold
        exact hold
      obtain ⟨outRest, R₃, herest, hAgreeRest, hR₃lc, hR₃K⟩ :=
        ihrec (Φ := Φ₁) (ctx := S₂.onCtx (S₁.onCtx ctx))
          (specs := ss.map (RecSpec.onSubst (S₁ ++ S₂))) (S₀ := R₂)
          (memberIndex := memberIndex + 1) hrestRel hrestExec
          (by simpa using hrest_len) hctxWF hctxBelow hR₂lc hKΦ₁ hKrest hR₂K
          hssLC hssBelow hssMono hdeclTail
      obtain ⟨⟨Φ₂, S₃, restNodeTypes, restSchemes⟩, hRest, hS₃K⟩ := outRest
      have hS₁₂Below : ∀ p ∈ S₁ ++ S₂, Ty.BelowFvars Φ₁ p.2 := by
        intro p hp
        rcases List.mem_append.mp hp with hp | hp
        · exact hS₁Below p hp
        · exact hS₂Below p hp
      have hAgree : Subst.AgreesBelow Φ S₀ (((S₁ ++ S₂) ++ S₃) ++ R₃) :=
        @Subst.AgreesBelow.trans_append Φ Φ₁ S₀ (S₁ ++ S₂) R₂ S₃ R₃
          hΦ₁ hAgreeHead hS₁₂Below hAgreeRest
      let out : { r : Nat × Subst × InferredNodeTypes × InferredBinderSchemes //
          InferRecGroup Φ ctx (e :: rest) (.mono τ :: ss) r.1 r.2.1 ∧
            (∀ p ∈ r.2.1, p.1 ∉ K) } :=
        ⟨(Φ₂, S₁ ++ S₂ ++ S₃,
            (eNodeTypes.onSubst (S₂ ++ S₃)).below (.letRecRhs memberIndex) ++
              restNodeTypes,
            (eSchemes.onSubst (S₂ ++ S₃)).below (.letRecRhs memberIndex) ++ restSchemes),
          .cons hInferE hS₂uni hRest, by
            intro p hp
            rw [List.mem_append, List.mem_append] at hp
            rcases hp with (hp | hp) | hp
            · exact hS₁K p hp
            · exact hS₂K p hp
            · exact hS₃K p hp⟩
      refine ⟨out, R₃, ?_, ?_, hR₃lc, hR₃K⟩
      · simp only [inferRecGroupWithTypesCore, heinfer, heuni, herest]
        rfl
      · simpa [out, List.append_assoc] using hAgree

/-- Executable completeness for Damas--Milner recursive groups.  The proof
    follows the concrete group and ceiling workers, while the relational
    completeness theorem supplies the erased declarative reconstruction used
    to reconcile their committed choices. -/
theorem inferCore_complete_letRec {anns : List (Option PolyTy)}
    {bindings : List Expr} {body : Expr}
    (ihbindings : ∀ e ∈ bindings, InferCoreComplete e)
    (ihbody : InferCoreComplete body) :
    InferCoreComplete (.letRec anns bindings body) := by
  intro Φ ctx Φ' S τ K hwf hbelow hKΦ hKe hSK h
  let S₀ : Subst := S
  let τ₀ : Ty :=  τ
  have hS₀ : ∀ p ∈ S₀, p.2.IsLC := by
    simpa [S₀] using (Infer.lc h hwf).2
  have hKfix : ∀ k ∈ K, S₀.onTy (.fvar k) = .fvar k := by
    intro k hk
    apply Ty.substFvars_eq_self_of_no_key
    intro p hp heq
    simp only [Ty.freeVars, List.mem_singleton] at heq
    exact hSK p (by simpa [S₀] using hp) (heq ▸ hk)
  have hty : TypeOfHM (S₀.onCtx ctx)
      (Expr.letRec anns bindings body) τ₀ := by
    simpa [S₀, τ₀] using Infer.sourceSound h hwf hbelow K hKΦ hKe hSK
  cases hty with
  | letRec hwfD hlenD hlinkD hlcD hmonoD hceilingD hbodyCtxD hbodyD =>
      rename_i dspecs τsD Gdecl L
      subst hbodyCtxD
      have hKgrp : ∀ y ∈ Expr.tyFreeVars.RecGroup.tyFreeVars bindings, y ∈ K :=
        fun y hy => hKe y (by
          simp only [Expr.tyFreeVars, List.mem_append]
          exact Or.inl (Or.inr hy))
      have hKbody : ∀ y ∈ body.tyFreeVars, y ∈ K := fun y hy =>
        hKe y (by
          simp only [Expr.tyFreeVars, List.mem_append]
          exact Or.inr hy)
      have hlen_τsD : bindings.length = τsD.length := by
        simpa [List.length_map] using hlenD
      have hdspec_len : dspecs.length = bindings.length := by
        simpa [List.length_map] using hwfD.length.symm
      have hlen_ab : anns.length = bindings.length := by
        have ha := congrArg List.length hwfD.anns_eq
        simp only [List.length_map] at ha
        omega
      have hKrigid : ∀ y ∈ RecGroup.rigidVars anns bindings, y ∈ K := by
        intro y hy
        rcases List.mem_append.mp hy with hy | hy
        · exact hKe y (List.mem_append.mpr (Or.inl
            (List.mem_append.mpr (Or.inl hy))))
        · have hy' : y ∈ Expr.tyFreeVars.RecGroup.tyFreeVars bindings :=
            (mem_recGroup_tyFreeVars (bindings := bindings)).mpr hy
          exact hKe y (List.mem_append.mpr (Or.inl
            (List.mem_append.mpr (Or.inr hy'))))
      let XavoidPool :=
        (L ++ Gdecl ++ dspecs.flatMap RecSpec.monoFreeVars ++
          (S₀.onCtx ctx).env.freeVars ++ K) ++ Ty.freeVarsList τsD
      obtain ⟨Xs, hXlen, hXnodup, hXavoid⟩ := exists_fresh_names
        XavoidPool Gdecl.length
      have hXL : ∀ x ∈ Xs, x ∉ L := fun x hx hc => hXavoid x hx (by
        dsimp [XavoidPool]
        simp only [List.mem_append]
        tauto)
      have hXG : ∀ g ∈ Gdecl, g ∉ Xs := fun g hg hc => hXavoid g hc (by
        dsimp [XavoidPool]
        simp only [List.mem_append]
        tauto)
      have hXτs : ∀ x ∈ Xs, ∀ τ, RecSpec.mono τ ∈ dspecs → x ∉ τ.freeVars :=
        fun x hx τ hτ hc => hXavoid x hx (by
          dsimp [XavoidPool]
          simp only [List.mem_append]
          exact Or.inl (Or.inl (Or.inl
            (Or.inr (List.mem_flatMap.mpr ⟨RecSpec.mono τ, hτ, hc⟩)))))
      have hXτsD : ∀ x ∈ Xs, ∀ τ ∈ τsD, x ∉ τ.freeVars := by
        intro x hx τ hτ hc
        exact hXavoid x hx (by
          dsimp [XavoidPool]
          exact List.mem_append.mpr (Or.inr (Ty.mem_freeVarsList_of_mem hτ hc)))
      have hXenv : ∀ x ∈ Xs, x ∉ (S₀.onCtx ctx).env.freeVars := fun x hx hc =>
        hXavoid x hx (by
          dsimp [XavoidPool]
          simp only [List.mem_append]
          tauto)
      have hXK : ∀ x ∈ Xs, x ∉ K := fun x hx hc => hXavoid x hx (by
        dsimp [XavoidPool]
        simp only [List.mem_append]
        tauto)
      have hXfresh : FreshNames L Gdecl.length Xs := ⟨hXlen, hXnodup, hXL⟩
      have hXrigid : ∀ x ∈ Xs, x ∉ RecGroup.rigidVars anns bindings :=
        fun x hx hc => hXK x hx (hKrigid x hc)
      set vs : List Ty := τsD.map (fun τ => Ty.renameG Gdecl Xs τ) with hvs_def
      have hvs_len : vs.length = bindings.length := by
        rw [hvs_def, List.length_map]
        exact hlen_τsD.symm
      have hvs_lc : ∀ t ∈ vs, t.IsLC := by
        intro t ht
        rw [hvs_def] at ht
        obtain ⟨τ, hτ, rfl⟩ := List.mem_map.mp ht
        change (Subst.onTy (Gdecl.zip (Xs.map (Ty.fvar ·))) τ).IsLC
        exact Subst.onTy_lc (fun p hp => by
          obtain ⟨w, _, hw⟩ := List.mem_map.mp (List.of_mem_zip hp).2
          rw [← hw]
          exact ContainsBvarsUpTo.fvar) (hlcD τ hτ)
      obtain ⟨R₀, hR₀lc, hR₀K, hR₀ag, hR₀block⟩ :=
        exists_recgroup_residual (Φ := Φ) (n := bindings.length)
          (S₀ := S₀) (vs := vs) (K := K)
          hvs_len hS₀ hvs_lc hKΦ hKfix
      have hR₀blockj : ∀ j (hj : j < bindings.length),
          R₀.onTy (Ty.fvar (Φ + j)) =
            Ty.renameG Gdecl Xs (τsD[j]'(by rw [← hlen_τsD]; exact hj)) := by
        intro j hj
        have hjT : j < τsD.length := by rw [← hlen_τsD]; exact hj
        have h := congrArg (fun l => l[j]?) hR₀block
        change (List.map R₀.onTy
          (List.map Ty.fvar (freshVars Φ bindings.length)))[j]? = vs[j]? at h
        rw [List.getElem?_map, List.getElem?_map] at h
        have hfj : (freshVars Φ bindings.length)[j]'(by
            simpa [freshVars_length] using hj) = Φ + j := by
          simp only [freshVars, List.getElem_map, List.getElem_range]
        rw [List.getElem?_eq_getElem (by simpa [freshVars_length] using hj), hfj] at h
        rw [hvs_def, List.getElem?_map, List.getElem?_eq_getElem hjT] at h
        exact Option.some.inj h
      set groupCtx : Ctx := { ctx with
        env := (RecSpec.init Φ anns).map (RecSpec.rhsEntry [] []) ++ ctx.env } with
        hgroupCtx_def
      have hinitSpec : ∀ s ∈ RecSpec.init Φ anns,
          ∃ j, j < anns.length ∧ s = RecSpec.mono (.fvar (Φ + j)) := by
        intro s hs
        rcases List.mem_iff_getElem.mp hs with ⟨j, hj, rfl⟩
        have hjA : j < anns.length := by
          rw [RecSpec.init_length] at hj
          exact hj
        have hget : (RecSpec.init Φ anns)[j] =
            RecSpec.mono (.fvar (Φ + j)) := by
          have heq := List.getElem?_eq_getElem hj
          rw [RecSpec.init_getElem? Φ anns j,
            List.getElem?_eq_getElem hjA] at heq
          injection heq with heq'
          exact heq'.symm
        exact ⟨j, hjA, hget⟩
      have hinitLC : ∀ s ∈ RecSpec.init Φ anns, s.LC := by
        intro s hs
        obtain ⟨j, _, rfl⟩ := hinitSpec s hs
        exact ContainsBvarsUpTo.fvar
      have hinitB : ∀ s ∈ RecSpec.init Φ anns, ∀ τm,
          s = RecSpec.mono τm → Ty.BelowFvars (Φ + bindings.length) τm := by
        intro s hs τm hτm
        obtain ⟨j, hj, hsj⟩ := hinitSpec s hs
        rw [hsj] at hτm
        injection hτm with heq
        subst τm
        exact Ty.BelowFvars.fvar (by rw [hlen_ab] at hj; omega)
      have hinitMono : ∀ s ∈ RecSpec.init Φ anns, ∃ τ, s = .mono τ := by
        intro s hs
        obtain ⟨j, _, hsj⟩ := hinitSpec s hs
        exact ⟨Ty.fvar (Φ + j), hsj⟩
      have hctxgWF : CtxWF groupCtx := by
        intro M hM
        rcases List.mem_append.mp hM with hM | hM
        · obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hM
          exact RecSpec.rhsEntry_nil_wf (hinitLC s hs)
        · exact hwf M hM
      have hctxgBelow : CtxBelow (Φ + bindings.length) groupCtx := by
        intro M hM
        rcases List.mem_append.mp hM with hM | hM
        · obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hM
          obtain ⟨τ, rfl⟩ := hinitMono s hs
          exact hinitB _ hs _ rfl
        · exact (hbelow M hM).mono (by omega)
      have hMonoMem : ∀ p ∈ bindings.zip (RecSpec.init Φ anns), ∀ τm,
          p.2 = RecSpec.mono τm →
          TypeOfHM (R₀.onCtx groupCtx) p.1
            ( (R₀.onTy τm)) := by
        intro p hp τm hτm
        rcases List.mem_iff_getElem.mp hp with ⟨j, hjp, hpeq⟩
        have hjB : j < bindings.length := by
          rw [List.length_zip] at hjp
          exact lt_of_lt_of_le hjp (min_le_left _ _)
        have hjI : j < (RecSpec.init Φ anns).length := by
          rw [List.length_zip] at hjp
          exact lt_of_lt_of_le hjp (min_le_right _ _)
        have hpeq' : (bindings[j]'hjB, (RecSpec.init Φ anns)[j]'hjI) = p := by
          rw [List.getElem_zip] at hpeq
          exact hpeq
        have hjA : j < anns.length := by rw [hlen_ab]; exact hjB
        have hinit_j : (RecSpec.init Φ anns)[j]'hjI =
            RecSpec.mono (Ty.fvar (Φ + j)) := by
          have hg := RecSpec.init_getElem? Φ anns j
          rw [List.getElem?_eq_getElem hjI, List.getElem?_eq_getElem hjA] at hg
          simpa using hg
        have hτm' : τm = Ty.fvar (Φ + j) := by
          have hf := congrArg Prod.snd hpeq'
          exact (RecSpec.mono.inj (by simpa [hinit_j, hτm] using hf)).symm
        subst hτm'
        have hjT : j < τsD.length := by rw [← hlen_τsD]; exact hjB
        have hjBE : j < bindings.length := hjB
        let bE : Expr := bindings[j]'hjBE
        let tD : Ty := τsD[j]'hjT
        have hmemD : (bE, tD) ∈ bindings.zip τsD :=
          getElem_mem_zip j hjBE hjT
        have hdecl0 := hmonoD Xs hXfresh (bE, tD) hmemD
        have hdeclE := hdecl0
        have hctxE :
            (RecSpecs.rhsCtx (S₀.onCtx ctx)
              (τsD.map RecSpec.mono) Gdecl Xs) =
            (R₀.onCtx groupCtx) := by
          simp only [RecSpecs.rhsCtx, groupCtx, Subst.onCtx, Subst.onEnv,
            List.map_append]
          congr 1
          · rw [List.map_map, List.map_map]
            congr 1
            · refine List.ext_getElem ?_ (fun k hk1 hk2 => ?_)
              · simp only [List.length_map, RecSpec.init_length]
                rw [hlen_ab, ← hlen_τsD]
              have hkT : k < τsD.length := by
                simp only [List.length_map, RecSpec.init_length] at hk2
                rw [hlen_ab] at hk2
                rwa [← hlen_τsD]
              have hkB : k < bindings.length := by rwa [hlen_τsD]
              have hkA : k < anns.length := by rwa [hlen_ab]
              have hinit_k : (RecSpec.init Φ anns)[k]'(by
                  simpa [RecSpec.init_length] using hkA) =
                  RecSpec.mono (Ty.fvar (Φ + k)) := by
                have hg := RecSpec.init_getElem? Φ anns k
                rw [List.getElem?_eq_getElem (by
                    simpa [RecSpec.init_length] using hkA),
                  List.getElem?_eq_getElem hkA] at hg
                simpa using hg
              have hblk := hR₀blockj k hkB
              have hblkE :
                  PolyTy.mkTrivial (Ty.renameG Gdecl Xs (τsD[k]'hkT)) =
                  PolyTy.mkTrivial (R₀.onTy (Ty.fvar (Φ + k))) := by
                exact congrArg PolyTy.mkTrivial hblk.symm
              simp only [List.getElem_map, Function.comp_apply, RecSpec.rhsEntry,
                hinit_k, Subst.onPolyTy, Ty.renameG_nil_pool, PolyTy.mkTrivial]
              exact hblkE
            · refine List.ext_getElem (by simp) (fun k hk1 hk2 => ?_)
              have hklen : k < ctx.env.length := by simpa using hk2
              have hMem : ctx.env[k]'hklen ∈ ctx.env := List.getElem_mem hklen
              simp only [List.getElem_map, Function.comp_apply,
                Subst.onPolyTy]
              refine congrArg₂ PolyTy.mk rfl ?_
              exact Subst.onTy_congr
                (fun v hv => Eq.symm (hR₀ag v hv))
                (hbelow _ hMem)
        have htyE :
              (Ty.renameG Gdecl Xs (τsD[j]'hjT)) =
             (R₀.onTy (Ty.fvar (Φ + j))) :=
          (hR₀blockj j hjB).symm
        rw [hctxE, htyE] at hdeclE
        have hp1 : p.1 = bindings[j]'hjB := (congrArg Prod.fst hpeq').symm
        have hbE : bE = (bindings[j]'hjB) := by
          simp [bE]
        rw [hbE, ← hp1] at hdeclE
        exact hdeclE
      have hKΦg : ∀ k ∈ K, k < Φ + bindings.length := fun k hk => by
        have := hKΦ k hk
        omega
      -- Follow the actual metadata-producing recursion-group worker.
      obtain ⟨groupOut, Rg, hegroup, hAgreeGroup, hRglc, hRgK⟩ :=
        inferRecGroupWithTypesCore_complete_mono (Φ := Φ + bindings.length)
          (ctx := groupCtx) (bindings := bindings)
          (specs := RecSpec.init Φ anns) (S₀ := R₀) (K := K)
          0 (fun e _ => Infer.complete e) ihbindings
          (by simpa [RecSpec.init_length, hlen_ab])
          hctxgWF hctxgBelow hR₀lc hKΦg hKgrp hR₀K hinitLC hinitB hinitMono hMonoMem
      obtain ⟨⟨Φ₁, S₁, bindingsOut, bindingSchemes⟩, hgroup, hS₁K⟩ := groupOut
      have hAgreeTier : Subst.AgreesBelow Φ S₀ (S₁ ++ Rg) := by
        intro v hv
        rw [← hR₀ag v hv]
        exact hAgreeGroup v (by omega)
      have hgle : Φ + bindings.length ≤ Φ₁ := InferRecGroup.frontier_le hgroup
      have hS₁lc : ∀ p ∈ S₁, p.2.IsLC :=
        InferRecGroup.lc hgroup hctxgWF hinitLC
      have htfv_below : ∀ y ∈ Expr.tyFreeVars.RecGroup.tyFreeVars bindings,
          y < Φ + bindings.length := fun y hy => by
        have := hKΦ y (hKgrp y hy)
        omega
      have hinit_bel : ∀ s ∈ RecSpec.init Φ anns,
          RecSpec.BelowFvars (Φ + bindings.length) s := by
        intro s hs
        obtain ⟨τ, rfl⟩ := hinitMono s hs
        exact hinitB _ hs _ rfl
      have hS₁_bel : ∀ p ∈ S₁, Ty.BelowFvars Φ₁ p.2 :=
        InferRecGroup.belowFvars hgroup hctxgBelow hinit_bel htfv_below
      have hKΦ₁ : ∀ k ∈ K, k < Φ₁ := fun k hk =>
        lt_of_lt_of_le (hKΦg k hk) hgle
      have hrigidBelow : ∀ x ∈ RecGroup.rigidVars anns bindings, x < Φ₁ :=
        fun x hx => hKΦ₁ x (hKrigid x hx)
      set specs1 := (RecSpec.init Φ anns).map (RecSpec.onSubst S₁) with
        hspecs1
      have hspecs1LC : ∀ s ∈ specs1, s.LC := by
        intro s hs
        rw [hspecs1] at hs
        obtain ⟨s₀, hs₀, rfl⟩ := List.mem_map.mp hs
        exact RecSpec.LC.onSubst hS₁lc (hinitLC s₀ hs₀)
      have hspecs1Below : ∀ s ∈ specs1, s.BelowFvars Φ₁ := by
        intro s hs
        rw [hspecs1] at hs
        obtain ⟨s₀, hs₀, rfl⟩ := List.mem_map.mp hs
        exact RecSpec.BelowFvars.onSubst hS₁_bel
          ((hinit_bel s₀ hs₀).mono hgle)
      set G := genGroupVars (RecGroup.rigidVars anns bindings) (S₁.onCtx ctx).env
        (RecSpecs.monoTys specs1) with hG
      have hannsWF : ∀ σ, some σ ∈ anns → σ.WF := by
        intro σ hσ
        have hσe : some σ ∈ anns := hσ
        rw [← hwfD.anns_eq] at hσe
        obtain ⟨s, hs, hsann⟩ := List.mem_map.mp hσe
        cases s with
        | mono t => simp [RecSpec.ann] at hsann
        | poly σ₀ =>
            have heq : σ₀ =  σ := by
              simpa [RecSpec.ann] using Option.some.inj hsann
            have hσewf : ( σ).WF := by
              rw [← heq]
              exact hwfD.poly_wf σ₀ hs
            exact hσewf
      have hdlc : ∀ τ, RecSpec.mono τ ∈ dspecs → τ.IsLC := by
        intro τ hτ
        exact hwfD.mono_lc τ hτ
      have hanns_eq :
          dspecs.map RecSpec.ann = anns := by
        simpa [hwfD.anns_eq]
      have hctxS₁ : (Rg.onCtx (S₁.onCtx ctx)) =
          (S₀.onCtx ctx) := by
        rw [← Subst.onCtx_append]
        exact (Subst.onCtx_congr hAgreeTier hbelow).symm
      have hGnodup : G.Nodup := by
        rw [hG]
        exact genGroupVars_nodup
      have hGrigid : ∀ g ∈ G, g ∉ RecGroup.rigidVars anns bindings := by
        intro g hg
        rw [hG] at hg
        simp only [genGroupVars, List.mem_filter, Bool.and_eq_true,
          Bool.not_eq_eq_eq_not, Bool.not_true, List.contains_eq_mem,
          decide_eq_false_iff_not] at hg
        exact hg.2.2
      have hσfix : ∀ σ, some σ ∈ anns → Rg.onPolyTy σ = σ := by
        intro σ hσ
        simp only [Subst.onPolyTy]
        rw [Subst.onTy_eq_self_of_fixes (fun v hv => hRgK v (hKe v (List.mem_append.mpr (Or.inl
          (List.mem_append.mpr (Or.inl (Expr.scheme_body_mem_annList_tyFreeVars hσ hv)))))))]
      have hconnAll : ∀ (j : Nat) (hj : j < bindings.length),
        Subst.onTy (Rg)
            ( (S₁.onTy (Ty.fvar (Φ + j))))
          = Ty.renameG Gdecl Xs
              ( (τsD[j]'(by rw [← hlen_τsD]; exact hj))) := by
        intro j hj
        have hjT : j < τsD.length := by rw [← hlen_τsD]; exact hj
        have hblockAgree : Eq (R₀.onTy (Ty.fvar (Φ + j)))
            (Rg.onTy (S₁.onTy (Ty.fvar (Φ + j)))) := by
          rw [← Subst.onTy_append]
          exact hAgreeGroup (Φ + j) (by omega)
        calc
           (Rg.onTy (S₁.onTy (Ty.fvar (Φ + j))))
              =  (R₀.onTy (Ty.fvar (Φ + j))) := hblockAgree.symm
          _ = Ty.renameG Gdecl Xs ( (τsD[j]'hjT)) := by
            rw [hR₀blockj j hj]
      have hconnB : ∀ (j : Nat) (hj : j < dspecs.length) (τdecl : Ty),
          dspecs[j]'hj = RecSpec.mono τdecl →
        Subst.onTy (Rg)
            ( (S₁.onTy (Ty.fvar (Φ + j))))
          = Ty.renameG Gdecl Xs ( τdecl) := by
        intro j hj τdecl hτdecl
        have hjl : j < bindings.length := by
          rw [← hdspec_len]
          exact hj
        have hjT : j < τsD.length := by rw [← hlen_τsD]; exact hjl
        have hlinkτ : τdecl = τsD[j]'hjT := by
          have hmemD : (RecSpec.mono τdecl, τsD[j]'hjT) ∈ dspecs.zip τsD := by
            simpa [hτdecl] using (getElem_mem_zip j hj hjT)
          exact (hlinkD (RecSpec.mono τdecl, τsD[j]'hjT) hmemD τdecl rfl).symm
        simpa [hlinkτ] using hconnAll j hjl
      set Rer : Subst :=
        Rg with hRer_def
      have hRerlc : ∀ p ∈ Rer, p.2.IsLC := by
        simpa [hRer_def] using hRglc
      have hgenInit : CeilingGenInv G Rg anns specs1 := by
        intro ann spec hp
        cases ann with
        | none => cases spec <;> trivial
        | some σ =>
          cases spec with
          | poly σ' =>
            rcases List.mem_iff_getElem.mp hp with ⟨j, hjp, hpeq⟩
            have hjS : j < specs1.length := by
              rw [List.length_zip] at hjp
              exact lt_of_lt_of_le hjp (min_le_right _ _)
            have hjA : j < anns.length := by
              rw [List.length_zip] at hjp
              exact lt_of_lt_of_le hjp (min_le_left _ _)
            rw [List.getElem_zip] at hpeq
            have hspecj : specs1[j]'hjS = RecSpec.poly σ' := congrArg Prod.snd hpeq
            have hinitj : (RecSpec.init Φ anns)[j]'(by
                simpa [RecSpec.init_length] using hjA) =
                RecSpec.mono (Ty.fvar (Φ + j)) := by
              have hg := RecSpec.init_getElem? Φ anns j
              rw [List.getElem?_eq_getElem (by
                simpa [RecSpec.init_length] using hjA),
                List.getElem?_eq_getElem hjA] at hg
              simpa using hg
            have hs1j : specs1[j]'hjS =
                RecSpec.mono (S₁.onTy (Ty.fvar (Φ + j))) := by
              simp only [specs1, List.getElem_map, hinitj, RecSpec.onSubst]
            rw [hs1j] at hspecj
            simp at hspecj
          | mono τinf =>
            rcases List.mem_iff_getElem.mp hp with ⟨j, hjp, hpeq⟩
            have hjA : j < anns.length := by
              rw [List.length_zip] at hjp
              exact lt_of_lt_of_le hjp (min_le_left _ _)
            have hjS : j < specs1.length := by
              rw [List.length_zip] at hjp
              exact lt_of_lt_of_le hjp (min_le_right _ _)
            rw [List.getElem_zip] at hpeq
            have hannj : anns[j]'hjA = some σ := congrArg Prod.fst hpeq
            have hspecj : specs1[j]'hjS = RecSpec.mono τinf := congrArg Prod.snd hpeq
            have hjB : j < bindings.length := by rw [← hlen_ab]; exact hjA
            have hjT : j < τsD.length := by rw [← hlen_τsD]; exact hjB
            have hinitj : (RecSpec.init Φ anns)[j]'(by
                simpa [RecSpec.init_length] using hjA) =
                RecSpec.mono (Ty.fvar (Φ + j)) := by
              have hg := RecSpec.init_getElem? Φ anns j
              rw [List.getElem?_eq_getElem (by
                simpa [RecSpec.init_length] using hjA),
                List.getElem?_eq_getElem hjA] at hg
              simpa using hg
            have hτinf : τinf = S₁.onTy (Ty.fvar (Φ + j)) := by
              have hs1j : specs1[j]'hjS =
                  RecSpec.mono (S₁.onTy (Ty.fvar (Φ + j))) := by
                simp only [specs1, List.getElem_map, hinitj, RecSpec.onSubst]
              exact RecSpec.mono.inj (hspecj.symm.trans hs1j)
            subst τinf
            have hτalgMem : RecSpec.mono (S₁.onTy (Ty.fvar (Φ + j))) ∈ specs1 :=
              hspecj ▸ List.getElem_mem hjS
            have hτDmem : τsD[j]'hjT ∈ τsD := List.getElem_mem hjT
            have hceilMem :
                (some ( σ), RecSpec.mono (τsD[j]'hjT)) ∈
                  (anns).zip
                    (τsD.map RecSpec.mono) := by
              have hm := getElem_mem_zip
                (as := anns)
                (bs := τsD.map RecSpec.mono) j (by simpa using hjA) (by simpa using hjT)
              simpa only [List.getElem_map, hannj, Option.map_some] using hm
            have hdeclGen := hceilingD.of_mem_zip hceilMem
            have hdeclGen' :
                ( (PolyTy.genGroup Gdecl (τsD[j]'hjT))).Generalizes
                  ( σ) := by
              exact hdeclGen
            have hτalgLC : (S₁.onTy (Ty.fvar (Φ + j))).IsLC :=
              Subst.onTy_lc hS₁lc ContainsBvarsUpTo.fvar
            have hconnj : Rer.onTy
                  ( (S₁.onTy (Ty.fvar (Φ + j)))) =
                Ty.renameG Gdecl Xs ( (τsD[j]'hjT)) := by
              simpa [hRer_def] using hconnAll j hjB
            have hXinf : ∀ x ∈ Xs, x ∉
                (Rer.onPolyTy (PolyTy.genGroup G
                  ( (S₁.onTy (Ty.fvar (Φ + j)))))).body.freeVars := by
              intro x hx hmem
              change x ∈ (Rer.onTy (Ty.closeOver (Ty.genFilter G
                ( (S₁.onTy (Ty.fvar (Φ + j)))))
                ( (S₁.onTy (Ty.fvar (Φ + j)))))).freeVars at hmem
              obtain ⟨v, hv, hxv⟩ := Ty.mem_freeVars_onTy_iff.mp hmem
              have hvτ : v ∈ (
                  (S₁.onTy (Ty.fvar (Φ + j)))).freeVars :=
                Ty.freeVars_closeOver_subset hv
              have hvτ' : v ∈ (S₁.onTy (Ty.fvar (Φ + j))).freeVars :=
                hvτ
              have hvG : v ∉ G := by
                intro hvg
                exact Ty.not_mem_closeOver_freeVars
                  (by simp only [Ty.genFilter, List.mem_filter, decide_eq_true_eq]
                      exact ⟨hvg, hvτ⟩) hv
              have hvMono : v ∈ Ty.freeVarsList (RecSpecs.monoTys specs1) :=
                mem_freeVarsList_monoTys (mem_monoTys_of_mem_solved hτalgMem) hvτ'
              have hcase : v ∈ (S₁.onCtx ctx).env.freeVars ∨
                  v ∈ RecGroup.rigidVars anns bindings := by
                by_contra hcon
                push_neg at hcon
                apply hvG
                rw [hG]
                simp only [genGroupVars, List.mem_filter, Bool.and_eq_true,
                  Bool.not_eq_eq_eq_not, Bool.not_true, List.contains_eq_mem,
                  decide_eq_false_iff_not]
                exact ⟨hvMono, hcon.1, hcon.2⟩
              rcases hcase with henv | hrigid
              · obtain ⟨pt, hpt, hvpt⟩ := Env.mem_freeVars_iff.mp henv
                have hxv' : x ∈ (Rg.onTy (Ty.fvar v)).freeVars := by
                  have heq : Rer.onTy (Ty.fvar v) =
                       (Rg.onTy (Ty.fvar v)) := by
                    rfl
                  rw [heq] at hxv
                  exact hxv
                have hxOnTy : x ∈ (Rg.onTy pt.body).freeVars :=
                  Ty.mem_freeVars_onTy_iff.mpr ⟨v, hvpt, hxv'⟩
                have hm : Rg.onPolyTy pt ∈ (Rg.onCtx (S₁.onCtx ctx)).env := by
                  simp only [Subst.onCtx, Subst.onEnv]
                  exact List.mem_map.mpr ⟨pt, hpt, rfl⟩
                have hxEnv : x ∈ (Rg.onCtx (S₁.onCtx ctx)).env.freeVars :=
                  Env.mem_freeVars_iff.mpr ⟨Rg.onPolyTy pt, hm, hxOnTy⟩
                have hxEnvE : x ∈ ((Rg.onCtx (S₁.onCtx ctx))).env.freeVars :=
                  hxEnv
                have hc := congrArg Ctx.env hctxS₁
                have hxS₀E : x ∈ ((S₀.onCtx ctx)).env.freeVars := by
                  rwa [← hc]
                exact hXenv x hx
                  hxS₀E
              · have hfix : Rg.onTy (Ty.fvar v) = Ty.fvar v :=
                  hRgK v (hKrigid v hrigid)
                have hxv' : x ∈ (Rg.onTy (Ty.fvar v)).freeVars := by
                  have heq : Rer.onTy (Ty.fvar v) =
                       (Rg.onTy (Ty.fvar v)) := by
                    rfl
                  rw [heq] at hxv
                  exact hxv
                rw [hfix] at hxv'
                simp only [Ty.freeVars, List.mem_singleton] at hxv'
                exact hXrigid x hx (by rw [hxv']; exact hrigid)
            have halgDecl := genGroup_generalizes_renameG
              (Ginf := G) (G := Gdecl) (Xsfull := Xs)
              (τinf :=  (S₁.onTy (Ty.fvar (Φ + j))))
              (τdecl :=  (τsD[j]'hjT)) (R := Rer)
              hτalgLC
              (hlcD (τsD[j]'hjT) hτDmem) hRerlc
              hwfD.nodup hXlen hXnodup hXG
              (fun x hx hc => hXτsD x hx (τsD[j]'hjT) hτDmem
                hc)
              hconnj hXinf
            have halgDecl' :
                ( (Rg.onPolyTy
                  (PolyTy.genGroup G (S₁.onTy (Ty.fvar (Φ + j)))))).Generalizes
                ( (PolyTy.genGroup Gdecl (τsD[j]'hjT))) := by
              simpa [hRer_def] using halgDecl
            exact halgDecl'.trans hdeclGen'
      let P := K.filter (fun x => !G.contains x)
      have hPG : ∀ x ∈ P, x ∉ G := by
        intro x hx
        simp only [P, List.mem_filter, Bool.not_eq_eq_eq_not, Bool.not_true,
          List.contains_eq_mem, decide_eq_false_iff_not] at hx
        exact hx.2
      have hRgP : ∀ x ∈ P, Rg.onTy (.fvar x) = .fvar x := by
        intro x hx
        exact hRgK x (List.mem_of_mem_filter hx)
      have hRgrigid : ∀ x ∈ RecGroup.rigidVars anns bindings,
          Rg.onTy (.fvar x) = .fvar x := fun x hx => hRgK x (hKrigid x hx)
      have hPbelow : ∀ x ∈ P, x < Φ₁ := by
        intro x hx
        exact hKΦ₁ x (List.mem_of_mem_filter hx)
      have hGbelow : ∀ x ∈ G, x < Φ₁ := by
        intro x hx
        have hxmono : x ∈ Ty.freeVarsList (RecSpecs.monoTys specs1) := by
          rw [hG] at hx
          simp only [genGroupVars, List.mem_filter, Bool.and_eq_true] at hx
          exact hx.1
        have hfree : ∀ {tys : List Ty}, x ∈ Ty.freeVarsList tys →
            ∃ τ ∈ tys, x ∈ τ.freeVars := by
          intro tys hmem
          induction tys with
          | nil => simp [Ty.freeVarsList] at hmem
          | cons τ tys ih =>
              simp only [Ty.freeVarsList, List.mem_dedup,
                List.mem_append] at hmem
              rcases hmem with hmem | hmem
              · exact ⟨τ, List.mem_cons_self, hmem⟩
              · obtain ⟨τ', hτ', hxτ'⟩ := ih hmem
                exact ⟨τ', List.mem_cons_of_mem _ hτ', hxτ'⟩
        obtain ⟨τ, hτmono, hxτ⟩ := hfree hxmono
        simp only [RecSpecs.monoTys, RecSpec.monoTy?, List.mem_filterMap] at hτmono
        obtain ⟨s, hs, hsome⟩ := hτmono
        cases s with
        | mono τ' =>
            simp only [Option.some.injEq] at hsome
            subst τ'
            exact (hspecs1Below (.mono τ) hs).mem_lt x hxτ
        | poly σ => simp at hsome
      have hannsRigid : ∀ σ, some σ ∈ anns →
          ∀ x ∈ σ.body.freeVars, x ∈ RecGroup.rigidVars anns bindings := by
        intro σ hσ x hx
        exact List.mem_append_left _
          (Expr.scheme_body_mem_annList_tyFreeVars hσ hx)
      have hspecsLen : anns.length = specs1.length := by
        rw [hspecs1, List.length_map, RecSpec.init_length]
      have hGspec : ∀ g ∈ G,
          g ∈ Ty.freeVarsList (RecSpecs.monoTys specs1) ∧
            g ∉ (S₁.onCtx ctx).env.freeVars ∧
            g ∉ RecGroup.rigidVars anns bindings := by
        intro g hg
        rw [hG] at hg
        simp only [genGroupVars, List.mem_filter, Bool.and_eq_true] at hg
        exact ⟨hg.1, by simpa using hg.2.1, by simpa using hg.2.2⟩
      have hGmember : ∀ g ∈ G,
          ∃ j, j < bindings.length ∧
            g ∈ (S₁.onTy (.fvar (Φ + j))).freeVars := by
        intro g hg
        have hg' := hGspec g hg
        have hfree : ∀ {tys : List Ty}, g ∈ Ty.freeVarsList tys →
            ∃ τ ∈ tys, g ∈ τ.freeVars := by
          intro tys hmem
          induction tys with
          | nil => simp [Ty.freeVarsList] at hmem
          | cons τ tys ih =>
              simp only [Ty.freeVarsList, List.mem_dedup,
                List.mem_append] at hmem
              rcases hmem with hmem | hmem
              · exact ⟨τ, List.mem_cons_self, hmem⟩
              · obtain ⟨τ', hτ', hgτ'⟩ := ih hmem
                exact ⟨τ', List.mem_cons_of_mem _ hτ', hgτ'⟩
        obtain ⟨τg, hτg, hgτ⟩ := hfree hg'.1
        rcases List.mem_filterMap.mp hτg with ⟨s, hs, hmono⟩
        have hsmono : s = RecSpec.mono τg := by
          cases s with
          | mono τ' => simpa [RecSpec.monoTy?] using hmono
          | poly σ => simp [RecSpec.monoTy?] at hmono
        obtain ⟨s₀, hs₀, hsub⟩ := List.mem_map.mp hs
        obtain ⟨j, hjA, hsj⟩ := hinitSpec s₀ hs₀
        rw [hsj] at hsub
        rw [← hsub] at hsmono
        injection hsmono with hτeq
        exact ⟨j, (by rwa [hlen_ab] at hjA), by simpa [hτeq] using hgτ⟩
      have hKG : ∀ g ∈ K, g ∉ G := by
        intro g hgK hgG
        have hgΦ : g < Φ := hKΦ g hgK
        obtain ⟨j, hj, hgτ⟩ := hGmember g hgG
        rcases Subst.mem_freeVars_onTy hgτ with hbase | hrange
        · simp only [Ty.freeVars, List.mem_singleton] at hbase
          omega
        · obtain ⟨p, hp, hgp⟩ := hrange
          have hctxAvoid : ∀ M ∈ groupCtx.env, g ∉ M.body.freeVars := by
            intro M hM
            rw [hgroupCtx_def] at hM
            rcases List.mem_append.mp hM with hinit | houter
            · obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hinit
              rw [RecSpec.rhsEntry_nil_body_freeVars]
              obtain ⟨j', hjA', hsj'⟩ := hinitSpec s hs
              rw [hsj']
              intro hc
              simp only [RecSpec.freeVars, Ty.freeVars, List.mem_singleton] at hc
              omega
            · intro hc
              have hsurvive : g ∈ (S₁.onPolyTy M).body.freeVars :=
                Ty.mem_freeVars_onTy_of_not_dom hc (fun q hq heq =>
                  hS₁K q hq (heq ▸ hgK))
              have hgEnv : g ∈ (S₁.onCtx ctx).env.freeVars :=
                Env.mem_freeVars_iff.mpr
                  ⟨S₁.onPolyTy M, List.mem_map.mpr ⟨M, houter, rfl⟩, hsurvive⟩
              exact (hGspec g hgG).2.1 hgEnv
          have hspecAvoid : ∀ s ∈ RecSpec.init Φ anns, g ∉ s.freeVars := by
            intro s hs
            obtain ⟨j', hjA', hsj'⟩ := hinitSpec s hs
            rw [hsj']
            intro hc
            simp only [RecSpec.freeVars, Ty.freeVars, List.mem_singleton] at hc
            omega
          have hbindingsAvoid :
              g ∉ Expr.tyFreeVars.RecGroup.tyFreeVars bindings := by
            intro hc
            exact (hGspec g hgG).2.2
              (List.mem_append_right _ ((mem_recGroup_tyFreeVars).mp hc))
          have hgroupRange := InferRecGroup.eOut_avoid hgroup (w := g)
            (by omega) hctxAvoid hspecAvoid hbindingsAvoid
          exact hgroupRange p hp hgp
      obtain ⟨ceilingOut, heceiling, hfac⟩ :=
        RecCeilingConstraints.solve_complete_of_generalizes
          (K := K) (rigid := RecGroup.rigidVars anns bindings)
          (G := G) (R := Rg) hspecsLen hGnodup
          (fun x hx hxin => hGrigid x hxin hx) hKG hRglc
          hRgK hRgrigid hKΦ₁ hrigidBelow hGbelow hannsWF hannsRigid
          hspecs1LC hspecs1Below hgenInit
      obtain ⟨Sc, hSc, hScKWorker⟩ := ceilingOut
      set specsC := specs1.map (RecSpec.onSubst Sc) with hspecsC
      have hceiling : RecSpecs.ceilingOK G anns specsC :=
        by simpa [hspecsC] using
          hSc.ceilingOK hspecs1LC hspecs1Below hrigidBelow
      have hScdom : ∀ p ∈ Sc, p.1 ∉ G := fun p hp =>
        (hSc.dom_avoids p hp).2.2
      have hScrange : ∀ p ∈ Sc, ∀ u ∈ p.2.freeVars, u ∉ G :=
        hSc.range_avoids_pool
      have hScK : ∀ p ∈ Sc, p.1 ∉ K := by
        exact hScKWorker
      have hbodyE : TypeOfHM
          (RecSpecs.bodyCtx (S₀.onCtx ctx) dspecs Gdecl)
          body ( τ₀) := hbodyD
      have hbodyAlg0 :=
        letRecFused_body_retype (Φ := Φ) (ctx := ctx) (S₁ := S₁)
          (Sc := Sc) (R₁ := Rg) (S₀ := S₀)
          (anns := anns) (bindings := bindings) (body := body) (dspecs := dspecs)
          (specs1 := specs1) (specsC := specsC)
          (G := Gdecl) (Xs := Xs) (τ₀ := τ₀) (K := K) hspecs1 hspecsC
          (fun p hp => by rw [← hG]; exact hScdom p hp)
          (fun p hp u hu => by rw [← hG]; exact hScrange p hp u hu) hfac
          hanns_eq hdlc hwfD.nodup hXlen hXnodup hXG hXτs hXenv hXrigid
          hS₁lc hRglc hctxS₁ hKrigid hRgK hσfix hconnB hbodyE
      have hbodyAlg : TypeOfHM
          (Rg.onCtx
            { (Sc.onCtx (S₁.onCtx ctx)) with
              env := RecSpecs.ceilingSchemes G anns specsC ++
                (Sc.onCtx (S₁.onCtx ctx)).env })
          body ( τ₀) := by
        simpa only [hG] using hbodyAlg0
      have hσbody_bel : ∀ σ, some σ ∈ anns →
          Ty.BelowFvars Φ₁ σ.body := fun σ hσ =>
        Ty.BelowFvars.of_freeVars_lt (fun y hy =>
          hKΦ₁ y (hKe y (List.mem_append.mpr (Or.inl
            (List.mem_append.mpr (Or.inl
              (Expr.scheme_body_mem_annList_tyFreeVars hσ hy)))))))
      have hSc_bel : ∀ p ∈ Sc, Ty.BelowFvars Φ₁ p.2 :=
        hSc.belowFvars hrigidBelow
      have hspecsC_lc : ∀ s ∈ specsC, s.LC := by
        intro s hs
        rw [hspecsC] at hs
        obtain ⟨s₁, hs₁, rfl⟩ := List.mem_map.mp hs
        exact RecSpec.LC.onSubst hSc.lc (hspecs1LC s₁ hs₁)
      have hspecsC_post : ∀ s ∈ specsC, s.BelowFvars Φ₁ := by
        intro s hs
        rw [hspecsC] at hs
        obtain ⟨s₁, hs₁, rfl⟩ := List.mem_map.mp hs
        exact RecSpec.BelowFvars.onSubst hSc_bel (hspecs1Below s₁ hs₁)
      let bodyCtx : Ctx :=
        { (Sc.onCtx (S₁.onCtx ctx)) with
          env := RecSpecs.ceilingSchemes G anns specsC ++
            (Sc.onCtx (S₁.onCtx ctx)).env }
      have hwfB : CtxWF bodyCtx := by
        intro M hM
        rcases List.mem_append.mp hM with hM | hM
        · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hM
          cases p with
          | mk a s =>
              cases a with
              | some σ => exact hannsWF σ (List.of_mem_zip hp).1
              | none =>
                  exact RecSpec.bodyScheme_wf
                    (hspecsC_lc s (List.of_mem_zip hp).2)
        · exact Subst.onCtx_wf hSc.lc (Subst.onCtx_wf hS₁lc hwf) M hM
      have hbelowB : CtxBelow Φ₁ bodyCtx := by
        intro M hM
        rcases List.mem_append.mp hM with hM | hM
        · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hM
          cases p with
          | mk a s =>
              cases a with
              | some σ => exact hσbody_bel σ (List.of_mem_zip hp).1
              | none =>
                  exact RecSpec.bodyScheme_belowFvars
                    (hspecsC_post s (List.of_mem_zip hp).2)
        · exact Subst.onCtx_below hSc_bel (le_refl _)
            (Subst.onCtx_below hS₁_bel (le_trans (by omega) hgle) hbelow) M hM
      obtain ⟨_, _, _, _, hbodySeed, _, _, _, _, hSbodyK⟩ :=
        (Infer.complete body) K hwfB hbelowB hRglc hKΦ₁ hKbody hRgK (by
          simpa [bodyCtx] using hbodyAlg)
      have hbodySome := ihbody K hwfB hbelowB hKΦ₁ hKbody hSbodyK
        hbodySeed
      obtain ⟨bodyOut, hebody⟩ := Option.isSome_iff_exists.mp hbodySome
      obtain ⟨⟨Φ₂, S₂, τ₂, bodyExpr, bodySchemes⟩, hbodyInfer, hS₂K⟩ := bodyOut
      have hannsWFB : ∀ a ∈ anns, ∀ σ, a = some σ →
          Ty.bvarsBelow σ.paramCount σ.body = true := by
        intro a ha σ hEq
        have hsome : some σ ∈ anns := hEq ▸ ha
        exact (PolyTy.wf_iff_bvarsBelow (M := σ)).mpr (hannsWF σ hsome)
      have hspecsLCB : specs1.all RecSpec.isLCB = true :=
        List.all_eq_true.mpr (fun s hs =>
          (RecSpec.isLCB_iff s).mpr (hspecs1LC s hs))
      have hspecsBelowB : specs1.all (RecSpec.belowFvarsB Φ₁) = true :=
        List.all_eq_true.mpr (fun s hs =>
          (RecSpec.belowFvarsB_iff s).mpr (hspecs1Below s hs))
      have hrigidBelowB : (RecGroup.rigidVars anns bindings).all
          (fun x => decide (x < Φ₁)) = true :=
        List.all_eq_true.mpr (fun x hx => by
          exact decide_eq_true (hrigidBelow x hx))
      have hspecsLCBRaw :
          ((RecSpec.init Φ anns).map (RecSpec.onSubst S₁)).all
            RecSpec.isLCB = true := by
        simpa [hspecs1] using hspecsLCB
      have hspecsBelowBRaw :
          ((RecSpec.init Φ anns).map (RecSpec.onSubst S₁)).all
            (RecSpec.belowFvarsB Φ₁) = true := by
        simpa [hspecs1] using hspecsBelowB
      have heceilingRaw : solveRecCeilingConstraints K
          (RecGroup.rigidVars anns bindings)
          (genGroupVars (RecGroup.rigidVars anns bindings)
            (S₁.onCtx ctx).env
            (RecSpecs.monoTys ((RecSpec.init Φ anns).map
              (RecSpec.onSubst S₁))))
          Φ₁ anns ((RecSpec.init Φ anns).map (RecSpec.onSubst S₁))
          hannsWF hannsRigid
          (fun s hs => hspecs1LC s (by simpa [hspecs1] using hs)) =
            some ⟨Sc, hSc, hScKWorker⟩ := by
        simpa [hspecs1, hG] using heceiling
      have hebodyRaw : inferWithTypesCore K Φ₁
          { (Sc.onCtx (S₁.onCtx ctx)) with
            env := RecSpecs.ceilingSchemes
                (genGroupVars (RecGroup.rigidVars anns bindings)
                  (S₁.onCtx ctx).env
                  (RecSpecs.monoTys ((RecSpec.init Φ anns).map
                    (RecSpec.onSubst S₁))))
                anns (((RecSpec.init Φ anns).map
                  (RecSpec.onSubst S₁)).map (RecSpec.onSubst Sc)) ++
              (Sc.onCtx (S₁.onCtx ctx)).env }
          body = some ⟨(Φ₂, S₂, τ₂, bodyExpr, bodySchemes),
            hbodyInfer, hS₂K⟩ := by
        simpa [bodyCtx, hspecs1, hG, hspecsC] using hebody
      rw [inferWithTypesCore, dif_pos hannsWFB, hegroup]
      simp only
      rw [dif_pos hspecsLCBRaw, dif_pos hspecsBelowBRaw,
        dif_pos hrigidBelowB, heceilingRaw]
      simp only
      rw [hebodyRaw]
      rfl

/-- The concrete metadata-producing inference worker accepts every well-scoped
    relational inference derivation for a source expression.  As for
    `Infer.complete`, the size induction is needed because annotated `let`
    opens the annotation binders in its RHS without changing expression size. -/
theorem inferCore_complete (e : Expr) : InferCoreComplete e := by
  have upto : ∀ n : Nat, ∀ e : Expr, e.size < n → InferCoreComplete e := by
    intro n
    induction n with
    | zero =>
        intro e hsize
        omega
    | succ n ih =>
        intro e hsize
        cases e with
        | primLit p => exact inferCore_complete_prim
        | primBinOp op => exact inferCore_complete_primBinOp
        | var i => exact inferCore_complete_var
        | ctor name => exact inferCore_complete_ctor
        | lambda ann body =>
            have hbody : body.size < n := by
              simp only [Expr.size] at hsize
              omega
            have ihbody : InferCoreComplete body := ih body hbody
            intro Φ ctx Φ' S τ K hwf hbelow hKΦ hKe hSK h
            exact inferCore_complete_lambda (ann := ann) (body := body) ihbody
              K hwf hbelow hKΦ hKe hSK h
        | app f arg =>
            have hf : f.size < n := by
              simp only [Expr.size] at hsize
              omega
            have harg : arg.size < n := by
              simp only [Expr.size] at hsize
              omega
            have ihf : InferCoreComplete f := ih f hf
            have iharg : InferCoreComplete arg := ih arg harg
            intro Φ ctx Φ' S τ K hwf hbelow hKΦ hKe hSK h
            exact inferCore_complete_app (f := f) (arg := arg) ihf iharg
              K hwf hbelow hKΦ hKe hSK h
        | letIn ann rhs body =>
            have hrhs : rhs.size < n := by
              simp only [Expr.size] at hsize
              omega
            have hbody : body.size < n := by
              simp only [Expr.size] at hsize
              omega
            have ihrhs : InferCoreComplete rhs := ih rhs hrhs
            have ihopened : ∀ Ys, InferCoreComplete (rhs.openTyVars Ys) :=
              fun Ys => ih (rhs.openTyVars Ys) (by
                  rw [Expr.size_openTyVars]
                  exact hrhs)
            have ihbody : InferCoreComplete body := ih body hbody
            intro Φ ctx Φ' S τ K hwf hbelow hKΦ hKe hSK h
            exact inferCore_complete_letIn (ann := ann) (rhs := rhs)
              (body := body) ihrhs ihopened ihbody K hwf hbelow hKΦ hKe hSK h
        | match_ scrut branches =>
            have hscrut : scrut.size < n := by
              simp only [Expr.size] at hsize
              omega
            have hbranches : ∀ br ∈ branches, br.2.size < n := by
              intro br hbr
              have hle := Expr.size_le_sizeBranches_of_mem hbr
              simp only [Expr.size] at hsize
              omega
            have ihscrut : InferCoreComplete scrut := ih scrut hscrut
            have ihbr : ∀ br ∈ branches, InferCoreComplete br.2 :=
              fun br hbr => ih br.2 (hbranches br hbr)
            intro Φ ctx Φ' S τ K hwf hbelow hKΦ hKe hSK h
            exact inferCore_complete_match (scrut := scrut)
              (branches := branches) ihscrut ihbr K hwf hbelow hKΦ hKe hSK h
        | letRec anns bindings body =>
            have hbody : body.size < n := by
              simp only [Expr.size] at hsize
              omega
            have hbindings : ∀ b ∈ bindings, b.size < n := by
              intro b hb
              have hle := Expr.size_le_sizeRecGroup_of_mem hb
              simp only [Expr.size] at hsize
              omega
            have ihbs : ∀ b ∈ bindings, InferCoreComplete b :=
              fun b hb => ih b (hbindings b hb)
            have ihbody : InferCoreComplete body := ih body hbody
            intro Φ ctx Φ' S τ K hwf hbelow hKΦ hKe hSK h
            exact inferCore_complete_letRec (anns := anns)
              (bindings := bindings) (body := body) ihbs ihbody
              K hwf hbelow hKΦ hKe hSK h
  intro Φ ctx Φ' S τ K hwf hbelow hKΦ hKe hSK h
  exact upto (e.size + 1) e (by omega) K hwf hbelow hKΦ hKe hSK h

/-! ## 8. Public executable-completeness capstones -/

/-- Every declaratively typeable annotated source is accepted by
    the public principal-monotype checker. Source annotations remain part of
    the language accepted by inference. -/
theorem principalType_complete {ctors : CtorEnv} {e : Expr} {τ : Ty}
    (hty : TypeOfHM ⟨[], ctors⟩ e τ) :
    (principalType ctors e).isSome := by
  have hcomplete : Infer.CompleteAt e := Infer.complete e
  unfold Infer.CompleteAt at hcomplete
  obtain ⟨Φ', S, τ', R, hInfer, _hAgree, _hty, _hRlc, _hRK, hSK⟩ :=
    @hcomplete e.freshFloor ⟨[], ctors⟩ [] τ e.tyFreeVars
      CtxWF.empty CtxBelow.empty (by simp)
      (fun k hk => Expr.lt_freshFloor hk) (fun y hy => hy) (by simp) (by
        simpa [Subst.onCtx, Subst.onEnv] using hty)
  have hsome := inferCore_complete e e.tyFreeVars CtxWF.empty CtxBelow.empty
    (fun k hk => Expr.lt_freshFloor hk) (fun y hy => hy) hSK hInfer
  obtain ⟨result, hresult⟩ := Option.isSome_iff_exists.mp hsome
  rcases result with
    ⟨⟨Φr, Sr, τr, nodeTypes, schemes⟩, hResultInfer, hResultAvoid⟩
  rw [principalType, inferCore, hresult]
  rfl

/-- Whole-program type checking accepts every declaratively typeable annotated source. -/
theorem typecheck_complete {ctors : CtorEnv} {e : Expr} {τ : Ty}
    (hty : TypeOfHM ⟨[], ctors⟩ e τ) :
    (typecheck ctors e).isSome := by
  simpa [typecheck] using principalType_complete hty

/-- On source expressions, executable principal-type acceptance is exactly
    declarative HM typeability. -/
theorem principalType_accepts_iff {ctors : CtorEnv} {e : Expr}
    : (principalType ctors e).isSome ↔
      ∃ τ, TypeOfHM ⟨[], ctors⟩ e τ := by
  constructor
  · intro hsome
    obtain ⟨τ, hτ⟩ := Option.isSome_iff_exists.mp hsome
    exact ⟨τ, principalType_source_sound hτ⟩
  · rintro ⟨τ, hτ⟩
    exact principalType_complete hτ

/-- The public whole-program checker succeeds exactly on annotated sources that
    are declaratively HM-typeable. -/
theorem typecheck_accepts_iff {ctors : CtorEnv} {e : Expr}
    : (typecheck ctors e).isSome ↔
      ∃ τ, TypeOfHM ⟨[], ctors⟩ e τ := by
  simpa [typecheck] using principalType_accepts_iff (ctors := ctors) (e := e)
