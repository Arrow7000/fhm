import FHM.InferW

/-!
# Completeness restoration (post-erasure world)

Reinstates the decidability/completeness stack deleted in step 5(c) of the
erasure migration, against the current API: `Expr` without `var.tyArgs`,
`Infer` without an `eOut` output index, and the bounds-blind unification
layer (`Unifies` = `AgreesHM`, `UnifyRel` with the `bl`/`blList`/`listBl`
rules). The reference implementation is commit `ffc544f`; proofs are ported
from there and adapted to the decoration-aware setting.

## The §1 pinning decision (made FIRST, recorded here per the brief)

D2/D3 pin the declarative typing to the inferred output **up to erasure**:

    AgreesHM τ₀ (R.onTy τ)

and NOT plain equality `τ₀ = R.onTy τ`. Plain equality is FALSE when the
inferred type carries a `.bl` head: `Subst.onTy_bl` rewrites only the
*element* of a `.bl` and never its interval slots, so `R.onTy τ` keeps `τ`'s
exact `.bl` decoration, while the declarative relation — whose `var` rule
instantiates schemes existentially — may realise the same HM shape at a
different interval or as a bare `List`. This is precisely the decoration
sensitivity that made `Infer.sound` thread `eraseBounds` through its
conclusion. Equality-flavoured corollaries therefore carry the side condition
`hnorm : Ty.eraseBounds τ₀ = τ₀`, upgrading the pin to
`τ₀ = Ty.eraseBounds (R.onTy τ)`.

## Contents

1. α-renaming / swap / block-swap kit (ported from `ffc544f`, with `bl`
   cases added throughout).
2. Unification completeness: `UnifyRel.complete` / `complete_K` (the
   rigidity-aware relational form) and the executable twins
   `unifyCoreK_complete` / `unify_complete`. Adaptation to bounds-blind
   `Unifies`: shape clashes are read off the *erased* images (erasure
   preserves `Ty.size` exactly, and compound heads survive erasure).
3. Gap-avoidance family: domain/range locality of `Infer` substitutions
   (`Infer.gap_avoid`, `InferBranches.gap_avoid`, `InferRecGroup.gap_avoid`),
   ported onto the DM-cut relations (`consMono`/`consPoly`, ceiling-based
   `letRec` body environment).
-/

set_option maxHeartbeats 1600000

/-! ## 1. The renaming / swap / block-swap kit

Injective renamings dodge the fresh-binder obstruction: a clean override of
`S₀` mapping a fresh var to the declarative type is unrealisable as a `List`
substitution once the fresh var occurs in `S₀`'s range; swapping it away with
a fresh name restores cleanliness. Type-level only; ported nearly verbatim
with `bl` cases added. -/

mutual
/-- Relabel every free type variable by `f`. An α-renaming when `f` is injective. -/
def Ty.rename (f : Nat → Nat) : Ty → Ty
  | .prim p          => .prim p
  | .arrow a b       => .arrow (a.rename f) (b.rename f)
  | .bvar i          => .bvar i
  | .fvar n          => .fvar (f n)
  | .customTy nm tys => .customTy nm (TyList.rename f tys)
  | .bl lo hi e      => .bl lo hi (e.rename f)

private def TyList.rename (f : Nat → Nat) : List Ty → List Ty
  | []       => []
  | hd :: tl => hd.rename f :: TyList.rename f tl
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
@[simp] theorem Ty.rename_bl {f : Nat → Nat} {lo hi : FHM.Bounds.CountSlot} {e : Ty} :
    Ty.rename f (.bl lo hi e) = .bl lo hi (Ty.rename f e) := rfl

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
  | bl _ _ e ih =>
    simp only [Ty.rename_bl, Ty.bl.injEq, true_and]
    exact ih (fun v hv => h v (by simpa [Ty.freeVars] using hv))

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
  | bl _ _ e ih => cases h with | bl he => exact .bl (ih he)

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
  | bl _ _ e ih => simp only [Ty.substFvar, Ty.rename_bl, ih]

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
  | bl _ _ e ih =>
    simp only [Ty.freeVars] at hc
    simp only [Subst.onTy_bl, Ty.rename_bl]
    exact congrArg _ (ih (fun hct => hc (by simpa [Ty.freeVars] using hct)))

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
  | bl _ _ e ih =>
    simp only [Ty.freeVars] at h ⊢
    exact ih h

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
  | bl _ _ e ih =>
    simp only [Ty.freeVars] at h
    simp only [Ty.rename_bl, Ty.substFvar, ih h]

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
  | bl _ _ e ih =>
    simp only [Ty.freeVars] at hτ ⊢
    exact ih hτ

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
  | bl _ _ e ih =>
    intro h
    rw [Subst.onTy_bl, ih (fun v hv => h v (by simpa [Ty.freeVars] using hv))]

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
  | bl _ _ e ih =>
    simp only [Subst.onTy_bl, Ty.rename_bl]
    exact congrArg _ (ih (fun v hv => hτ v (by simpa [Ty.freeVars] using hv)))

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
    simp only [Ty.rename_customTy, Subst.onTy_customTy, List.map_map, Ty.customTy.injEq,
               true_and]
    conv_rhs => rw [← List.map_id tys]
    apply List.map_congr_left
    intro t ht
    exact ih t ht (fun v hv => hX v (TyList.mem_freeVars_of_mem ht hv))
  | bl _ _ e ih =>
    simp only [Ty.rename_bl, Subst.onTy_bl]
    exact congrArg _ (ih (fun v hv => hX v (by simpa [Ty.freeVars] using hv)))

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
  | bl _ _ e ih =>
    intro v hv1 hv2
    simp only [Ty.rename_bl, Ty.freeVars] at *
    exact ih (fun w hw => hY w (by simpa [Ty.freeVars] using hw)) v hv1 hv2

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
  | bl lo hi e ih =>
    cases hinst with
    | bl hinst_e =>
      cases hbv with
      | bl hbv_e =>
        simp only [Ty.openVars_bl, Subst.onTy_bl]
        exact congrArg _ (ih hinst_e hbv_e (fun x hx hc => hXfresh x hx (by
          simpa [Ty.freeVars] using hc)))

/-- A single fresh name `W` starting a block `[W,W+k)` disjoint from `[Φ,Φ+k)`
    and above a finite `avoid` set. -/
theorem exists_fresh_block (avoid : List Nat) (Φ k : Nat) :
    ∃ W, Φ + k ≤ W ∧ ∀ v ∈ avoid, v < W := by
  refine ⟨avoid.foldr max 0 + Φ + k + 1, by omega, ?_⟩
  intro v hv
  have := List.le_foldr_max hv
  omega

/-! ## 2. Unification completeness

If two LC types admit an LC unifier, a `UnifyRel` derivation exists (plain and
rigidity-aware forms), and the executable unifiers realise them.

Adaptation to bounds-blind `Unifies` (`AgreesHM`): every *shape* argument of
the pre-bounds proof goes through the erased images. Two facts make this
painless — erasure preserves `Ty.size` exactly (a `.bl` collapses to a
one-argument bare `List`), and erasure preserves the head of every compound
type (`arrow`/`customTy` stay put, `.bl` becomes `customTy listTyName [_]`). -/

mutual
/-- Erasure preserves `Ty.size` exactly (`BL` ↦ 1-argument bare `List`). -/
theorem Ty.eraseBounds_size : ∀ t : Ty, (Ty.eraseBounds t).size = t.size
  | .prim _ => rfl
  | .bvar _ => rfl
  | .fvar _ => rfl
  | .arrow a b => by
    simp only [Ty.eraseBounds, Ty.size]
    rw [Ty.eraseBounds_size a, Ty.eraseBounds_size b]
  | .customTy nm tys => by
    simp only [Ty.eraseBounds, Ty.size, TyList.eraseBounds_eq_map]
    rw [TyList.eraseBounds_size tys]
  | .bl _ _ e => by
    simp only [Ty.eraseBounds_bl, bareListTy, Ty.size, TyList.size]
    rw [Ty.eraseBounds_size e]; omega

theorem TyList.eraseBounds_size :
    ∀ ts : List Ty, TyList.size (ts.map Ty.eraseBounds) = TyList.size ts
  | [] => rfl
  | a :: as => by
    simp only [List.map_cons, TyList.size]
    rw [Ty.eraseBounds_size a, TyList.eraseBounds_size as]
end

/-- Bounds-blind agreement pins the structural sizes. -/
theorem AgreesHM.size_eq {a b : Ty} (h : AgreesHM a b) : a.size = b.size := by
  calc a.size = (Ty.eraseBounds a).size := (Ty.eraseBounds_size _).symm
    _ = (Ty.eraseBounds b).size := congrArg Ty.size h
    _ = b.size := Ty.eraseBounds_size _

/-- `TyList.size` only sees element sizes. -/
theorem TyList.size_map_congr {f g : Ty → Ty} (h : ∀ t, (f t).size = (g t).size)
    (l : List Ty) : TyList.size (l.map f) = TyList.size (l.map g) := by
  induction l with
  | nil => rfl
  | cons hd tl ih => simp only [List.map_cons, TyList.size]; rw [h hd, ih]

/-- Bounds-blind unifiability pins the structural sizes. -/
theorem Unifies.size_eq {U : Subst} {a b : Ty} (h : Unifies U a b) :
    (U.onTy a).size = (U.onTy b).size := by
  simp only [Unifies, AgreesHM] at h
  calc (U.onTy a).size = (Ty.eraseBounds (U.onTy a)).size := (Ty.eraseBounds_size _).symm
    _ = (Ty.eraseBounds (U.onTy b)).size := congrArg Ty.size h
    _ = (U.onTy b).size := Ty.eraseBounds_size _

/-! Extraction helpers for the mixed `bare List ↔ BL` shapes: under bounds-blind
    agreement a bare-list-headed image can only meet a BL image at name
    `listTyName`, arity 1, with agreeing element images. -/

/-- From bounds-blind agreement between a `customTy`-headed image and a BL image:
    the head name must be `listTyName`. -/
theorem AgreesHM.customTy_bl_name {U : Subst} {nm : TyName} {tys : List Ty}
    {lo hi : FHM.Bounds.CountSlot} {e : Ty}
    (h : AgreesHM (U.onTy (.customTy nm tys)) (U.onTy (.bl lo hi e))) :
    nm = listTyName := by
  simp only [AgreesHM, Subst.onTy_customTy, Subst.onTy_bl, Ty.eraseBounds_customTy,
    Ty.eraseBounds_bl, bareListTy, Ty.customTy.injEq] at h
  exact h.1

/-- From bounds-blind agreement between a `customTy`-headed image and a BL image:
    the head name must be `listTyName`. -/
theorem AgreesHM.customTy_list_elem_bl {U : Subst} {x : Ty}
    {lo hi : FHM.Bounds.CountSlot} {e : Ty}
    (h : AgreesHM (U.onTy (Ty.customTy listTyName [x])) (U.onTy (.bl lo hi e))) :
    AgreesHM (U.onTy x) (U.onTy e) := by
  simpa [AgreesHM, Subst.onTy_customTy, Subst.onTy_bl, Ty.eraseBounds_customTy,
    Ty.eraseBounds_bl, bareListTy, Ty.customTy.injEq, TyList.eraseBounds,
    List.cons.injEq, true_and] using h

theorem AgreesHM.list_elem_bl {U : Subst} {x : Ty} {lo hi : FHM.Bounds.CountSlot} {e : Ty}
    (h : AgreesHM (U.onTy (Ty.customTy listTyName [x])) (U.onTy (.bl lo hi e))) :
    AgreesHM (U.onTy x) (U.onTy e) :=
  AgreesHM.customTy_list_elem_bl h

theorem AgreesHM.bl_elem_list {U : Subst} {x : Ty} {lo hi : FHM.Bounds.CountSlot} {e : Ty}
    (h : AgreesHM (U.onTy (.bl lo hi e)) (U.onTy (Ty.customTy listTyName [x]))) :
    AgreesHM (U.onTy e) (U.onTy x) :=
  (AgreesHM.customTy_list_elem_bl (U := U) (x := x) (lo := lo) (hi := hi) (e := e)
    h.symm).symm

/-- Mapping over an already-mapped list, pointwise form (definitional per element;
    stated with an explicit induction since the composite is a lambda, not `∘`). -/
private theorem List.map_map_pointwise {α : Type} (g : α → Ty) (f : Ty → Ty)
    (l : List α) :
    (l.map g).map f = l.map (fun x => f (g x)) := by
  induction l with
  | nil => rfl
  | cons a l ih => simp only [List.map_cons, ih]

/-- Unification completeness (+ the list version), bounded by the measure
    `2 * (size of the unified result) + flag` so a single strong induction on the
    bound `N` covers all recursive calls (`flag = 0` for `UnifyRel`, `1` for the
    list — the offset makes the singleton-list ↔ element step strictly decrease).
    Adapted to bounds-blind `Unifies`: hypotheses and list agreements are stated
    through `Ty.eraseBounds`; shape clashes are read off the erased images
    (erasure preserves size exactly and preserves compound heads), and the MGU
    factoring used is the honest `greatest_factors` (`FactorsHM`). -/
theorem UnifyRel.complete_aux : ∀ (N : Nat),
    (∀ {a b : Ty} {U : Subst}, 2 * (U.onTy a).size < N → a.IsLC → b.IsLC →
        Unifies U a b → ∃ S, UnifyRel a b S) ∧
    (∀ {as bs : List Ty} {U : Subst}, 2 * TyList.size (as.map U.onTy) + 1 < N →
        (∀ t ∈ as, t.IsLC) → (∀ t ∈ bs, t.IsLC) → as.length = bs.length →
        as.map (fun t => Ty.eraseBounds (U.onTy t))
          = bs.map (fun t => Ty.eraseBounds (U.onTy t)) →
        ∃ S, UnifyRelList as bs S) := by
  intro N
  induction N with
  | zero => exact ⟨fun h => absurd h (by omega), fun h => absurd h (by omega)⟩
  | succ N ih =>
    obtain ⟨ihU, ihL⟩ := ih
    refine ⟨?_, ?_⟩
    · -- UnifyRel
      intro a b U hsz ha hb hU
      have hszeq := Unifies.size_eq hU
      cases a with
      | bvar i => cases ha with | bvar h => omega
      | prim p =>
        cases b with
        | bvar i => cases hb with | bvar h => omega
        | prim q =>
          simp only [Unifies, AgreesHM, Subst.onTy_prim, Ty.eraseBounds] at hU
          cases hU; exact ⟨[], .prim⟩
        | fvar m => exact ⟨[(m, .prim p)], .fvarR (by simp) (by simp [Ty.freeVars])⟩
        | arrow b₁ b₂ => simp [Unifies, AgreesHM, Subst.onTy_arrow, Subst.onTy_prim,
            Ty.eraseBounds_arrow] at hU
        | customTy nm bs => simp [Unifies, AgreesHM, Subst.onTy_customTy,
            Subst.onTy_prim, Ty.eraseBounds_customTy] at hU
        | bl lo hi e => simp [Unifies, AgreesHM, Subst.onTy_bl, Subst.onTy_prim,
            Ty.eraseBounds_bl, bareListTy] at hU
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
          · exfalso; have hlt := Ty.size_onTy_fvar_lt (S := U) hocc (by simp); omega
          · exact ⟨[(n, .prim q)], .fvarL (by simp) hocc⟩
        | arrow b₁ b₂ =>
          by_cases hocc : n ∈ (Ty.arrow b₁ b₂).freeVars
          · exfalso; have hlt := Ty.size_onTy_fvar_lt (S := U) hocc (by simp); omega
          · exact ⟨[(n, .arrow b₁ b₂)], .fvarL (by simp) hocc⟩
        | customTy nm bs =>
          by_cases hocc : n ∈ (Ty.customTy nm bs).freeVars
          · exfalso; have hlt := Ty.size_onTy_fvar_lt (S := U) hocc (by simp); omega
          · exact ⟨[(n, .customTy nm bs)], .fvarL (by simp) hocc⟩
        | bl lo hi e =>
          by_cases hocc : n ∈ (Ty.bl lo hi e).freeVars
          · exfalso; have hlt := Ty.size_onTy_fvar_lt (S := U) hocc (by simp); omega
          · exact ⟨[(n, .bl lo hi e)], .fvarL (by simp) hocc⟩
      | arrow a₁ a₂ =>
        cases ha with
        | arrow ha₁ ha₂ =>
        cases b with
        | bvar i => cases hb with | bvar h => omega
        | fvar m =>
          by_cases hocc : m ∈ (Ty.arrow a₁ a₂).freeVars
          · exfalso; have hlt := Ty.size_onTy_fvar_lt (S := U) hocc (by simp); omega
          · exact ⟨[(m, .arrow a₁ a₂)], .fvarR (by simp) hocc⟩
        | prim q => simp [Unifies, AgreesHM, Subst.onTy_arrow, Subst.onTy_prim,
            Ty.eraseBounds_arrow] at hU
        | customTy nm bs => simp [Unifies, AgreesHM, Subst.onTy_arrow,
            Subst.onTy_customTy, Ty.eraseBounds_arrow, Ty.eraseBounds_customTy] at hU
        | bl lo hi e => simp [Unifies, AgreesHM, Subst.onTy_arrow, Subst.onTy_bl,
            Ty.eraseBounds_arrow, Ty.eraseBounds_bl, bareListTy] at hU
        | arrow b₁ b₂ =>
          cases hb with
          | arrow hb₁ hb₂ =>
          have hpsz : (U.onTy (.arrow a₁ a₂)).size
              = 1 + (U.onTy a₁).size + (U.onTy a₂).size := by simp [Subst.onTy_arrow, Ty.size]
          simp only [Unifies, AgreesHM, Subst.onTy_arrow, Ty.eraseBounds_arrow,
                     Ty.arrow.injEq] at hU
          obtain ⟨S₁, h₁⟩ := ihU (a := a₁) (b := b₁) (U := U)
            (by rw [hpsz] at hsz; omega) ha₁ hb₁ hU.1
          obtain ⟨R, hR⟩ := UnifyRel.greatest_factors h₁ U hU.1
          have hS₁lc := UnifyRel.lc h₁ ha₁ hb₁
          have hU2 : Unifies R (S₁.onTy a₂) (S₁.onTy b₂) := by
            show AgreesHM (R.onTy (S₁.onTy a₂)) (R.onTy (S₁.onTy b₂))
            have e1 := hR a₂
            have e2 := hR b₂
            simp only [AgreesHM] at e1 e2 ⊢
            rw [e1.symm, hU.2, e2]
          obtain ⟨S₂, h₂⟩ := ihU (a := S₁.onTy a₂) (b := S₁.onTy b₂) (U := R)
            (by
              have h : (R.onTy (S₁.onTy a₂)).size = (U.onTy a₂).size :=
                (hR a₂).size_eq.symm
              rw [h]
              rw [hpsz] at hsz; omega)
            (Subst.onTy_lc hS₁lc ha₂) (Subst.onTy_lc hS₁lc hb₂) hU2
          exact ⟨S₁ ++ S₂, .arrow h₁ h₂⟩
      | customTy nm tys₁ =>
        cases b with
        | bvar i => cases hb with | bvar h => omega
        | fvar m =>
          by_cases hocc : m ∈ (Ty.customTy nm tys₁).freeVars
          · exfalso; have hlt := Ty.size_onTy_fvar_lt (S := U) hocc (by simp); omega
          · exact ⟨[(m, .customTy nm tys₁)], .fvarR (by simp) hocc⟩
        | prim q => simp [Unifies, AgreesHM, Subst.onTy_customTy, Subst.onTy_prim,
            Ty.eraseBounds_customTy] at hU
        | arrow b₁ b₂ => simp [Unifies, AgreesHM, Subst.onTy_customTy,
            Subst.onTy_arrow, Ty.eraseBounds_customTy, Ty.eraseBounds_arrow] at hU
        | bl lo hi e =>
          cases hb with
          | bl heb =>
          by_cases hnm : nm = listTyName
          · subst hnm
            match tys₁ with
            | [x] =>
              obtain ⟨S, hS⟩ := ihU (a := x) (b := e) (U := U)
                (by
                  have hcsz : (U.onTy (.customTy listTyName [x])).size
                      = 1 + (U.onTy x).size := by
                    simp [Subst.onTy_customTy, Ty.size, TyList.size]
                  rw [hcsz] at hsz; omega)
                (by cases ha with | customTy h => exact h x List.mem_cons_self) heb
                (AgreesHM.list_elem_bl hU)
              exact ⟨S, .listBl hS⟩
            | [] =>
              exfalso
              exact absurd hU (fun hc => by
                simp only [Unifies, AgreesHM, Subst.onTy_customTy, Subst.onTy_bl,
                  Ty.eraseBounds_customTy, Ty.eraseBounds_bl, bareListTy,
                  Ty.customTy.injEq, List.map_nil, TyList.eraseBounds,
                  List.cons.injEq, true_and, reduceCtorEq] at hc)
            | _ :: _ :: _ =>
              exfalso
              exact absurd hU (fun hc => by
                simp only [Unifies, AgreesHM, Subst.onTy_customTy, Subst.onTy_bl,
                  Ty.eraseBounds_customTy, Ty.eraseBounds_bl, bareListTy,
                  Ty.customTy.injEq, List.map_cons, TyList.eraseBounds,
                  List.cons.injEq, true_and, reduceCtorEq] at hc
                exact hc.2.elim)
          · exact absurd (AgreesHM.customTy_bl_name hU) hnm
        | customTy nm' tys₂ =>
          have hcsz : (U.onTy (.customTy nm tys₁)).size
              = 1 + TyList.size (tys₁.map U.onTy) := by simp [Subst.onTy_customTy, Ty.size]
          simp only [Unifies, AgreesHM, Subst.onTy_customTy, Ty.eraseBounds_customTy,
                     Ty.customTy.injEq, TyList.eraseBounds_eq_map] at hU
          obtain ⟨rfl, hmapeq0⟩ := hU
          have hmapeq : tys₁.map (fun t => Ty.eraseBounds (U.onTy t))
              = tys₂.map (fun t => Ty.eraseBounds (U.onTy t)) := by
            rw [← List.map_map_pointwise U.onTy Ty.eraseBounds tys₁,
                ← List.map_map_pointwise U.onTy Ty.eraseBounds tys₂]
            exact hmapeq0
          have hlen : tys₁.length = tys₂.length := by
            have h := congrArg List.length hmapeq; simpa using h
          obtain ⟨S, hS⟩ := ihL (as := tys₁) (bs := tys₂) (U := U)
            (by rw [hcsz] at hsz; omega)
            (fun t ht => by cases ha with | customTy h => exact h t ht)
            (fun t ht => by cases hb with | customTy h => exact h t ht)
            hlen hmapeq
          exact ⟨S, .customTy hS⟩
      | bl lo₁ hi₁ e₁ =>
        cases ha with
        | bl hea =>
        cases b with
        | bvar i => cases hb with | bvar h => omega
        | fvar m =>
          by_cases hocc : m ∈ (Ty.bl lo₁ hi₁ e₁).freeVars
          · exfalso; have hlt := Ty.size_onTy_fvar_lt (S := U) hocc (by simp); omega
          · exact ⟨[(m, .bl lo₁ hi₁ e₁)], .fvarR (by simp) hocc⟩
        | prim q => simp [Unifies, AgreesHM, Subst.onTy_bl, Subst.onTy_prim,
            Ty.eraseBounds_bl, bareListTy] at hU
        | arrow b₁ b₂ => simp [Unifies, AgreesHM, Subst.onTy_bl, Subst.onTy_arrow,
            Ty.eraseBounds_bl, Ty.eraseBounds_arrow, bareListTy] at hU
        | customTy nm' tys₂ =>
          cases hb with
          | customTy heb =>
          by_cases hnm : nm' = listTyName
          · subst hnm
            match tys₂ with
            | [α] =>
              obtain ⟨S, hS⟩ := ihU (a := e₁) (b := α) (U := U)
                (by
                  have hbsz : (U.onTy (.bl lo₁ hi₁ e₁)).size = 1 + (U.onTy e₁).size := by
                    simp [Subst.onTy_bl, Ty.size]
                  rw [hbsz] at hsz; omega)
                hea (heb α List.mem_cons_self)
                (AgreesHM.bl_elem_list hU)
              exact ⟨S, .blList hS⟩
            | [] =>
              exfalso
              exact absurd hU.symm (fun hc => by
                simp only [Unifies, AgreesHM, Subst.onTy_customTy, Subst.onTy_bl,
                  Ty.eraseBounds_customTy, Ty.eraseBounds_bl, bareListTy,
                  Ty.customTy.injEq, List.map_nil, TyList.eraseBounds,
                  List.cons.injEq, true_and, reduceCtorEq] at hc)
            | _ :: _ :: _ =>
              exfalso
              exact absurd hU.symm (fun hc => by
                simp only [Unifies, AgreesHM, Subst.onTy_customTy, Subst.onTy_bl,
                  Ty.eraseBounds_customTy, Ty.eraseBounds_bl, bareListTy,
                  Ty.customTy.injEq, List.map_cons, TyList.eraseBounds,
                  List.cons.injEq, true_and, reduceCtorEq] at hc
                exact hc.2.elim)
          · exact absurd (AgreesHM.customTy_bl_name hU.symm) hnm
        | bl lo₂ hi₂ e₂ =>
          cases hb with
          | bl heb =>
          have hbsz : (U.onTy (.bl lo₁ hi₁ e₁)).size = 1 + (U.onTy e₁).size := by
            simp [Subst.onTy_bl, Ty.size]
          simp only [Unifies, AgreesHM, Subst.onTy_bl, Ty.eraseBounds_bl, bareListTy,
                     Ty.customTy.injEq, TyList.eraseBounds, List.cons.injEq,
                     true_and, and_true] at hU
          obtain ⟨S, hS⟩ := ihU (a := e₁) (b := e₂) (U := U)
            (by rw [hbsz] at hsz; omega) hea heb hU
          exact ⟨S, .bl hS⟩
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
          obtain ⟨R, hR⟩ := UnifyRel.greatest_factors h₁ U hmap.1
          have hS₁lc := UnifyRel.lc h₁ (has t₁ List.mem_cons_self) (hbs t₂ List.mem_cons_self)
          have key : ∀ t : Ty, AgreesHM (R.onTy (S₁.onTy t)) (U.onTy t) :=
            fun t => (hR t).symm
          have hmaptail : (ts₁.map S₁.onTy).map (fun t => Ty.eraseBounds (R.onTy t))
              = (ts₂.map S₁.onTy).map (fun t => Ty.eraseBounds (R.onTy t)) := by
            rw [List.map_map_pointwise (g := S₁.onTy)
                  (f := fun t => Ty.eraseBounds (R.onTy t)) (l := ts₁),
                List.map_congr_left (fun t (_ : t ∈ ts₁) => key t),
                List.map_map_pointwise (g := S₁.onTy)
                  (f := fun t => Ty.eraseBounds (R.onTy t)) (l := ts₂),
                List.map_congr_left (fun t (_ : t ∈ ts₂) => key t)]
            exact hmap.2
          obtain ⟨S₂, h₂⟩ := ihL (as := ts₁.map S₁.onTy) (bs := ts₂.map S₁.onTy) (U := R)
            (by
              have step1 : (ts₁.map S₁.onTy).map R.onTy
                  = ts₁.map (fun t => R.onTy (S₁.onTy t)) :=
                List.map_map_pointwise _ _ _
              have hsC : TyList.size (ts₁.map (fun t => R.onTy (S₁.onTy t)))
                  = TyList.size (ts₁.map U.onTy) :=
                TyList.size_map_congr (fun t => (key t).size_eq) ts₁
              rw [step1, hsC]
              rw [htsz] at hsz; omega)
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

The symmetric `UnifyRel` can always be oriented to avoid a rigid set `K`, given
only that some LC unifier `U` keeps every `k ∈ K` fixed. Var–var orients away
from `K`; a *rigid* var meeting a compound type is vacuous (`U` fixes it, and
erasure preserves compound heads, so the images cannot agree even up to
`AgreesHM`). The produced `S` avoids `K` by construction. -/
theorem UnifyRel.complete_K_aux {K : List Nat} : ∀ (N : Nat),
    (∀ {a b : Ty} {U : Subst}, 2 * (U.onTy a).size < N → a.IsLC → b.IsLC →
        (∀ p ∈ U, p.2.IsLC) → Unifies U a b → (∀ k ∈ K, U.onTy (.fvar k) = .fvar k) →
        ∃ S, UnifyRel a b S ∧ (∀ p ∈ S, p.1 ∉ K)) ∧
    (∀ {as bs : List Ty} {U : Subst}, 2 * TyList.size (as.map U.onTy) + 1 < N →
        (∀ t ∈ as, t.IsLC) → (∀ t ∈ bs, t.IsLC) → (∀ p ∈ U, p.2.IsLC) →
        as.length = bs.length →
        as.map (fun t => Ty.eraseBounds (U.onTy t))
          = bs.map (fun t => Ty.eraseBounds (U.onTy t)) →
        (∀ k ∈ K, U.onTy (.fvar k) = .fvar k) →
        ∃ S, UnifyRelList as bs S ∧ (∀ p ∈ S, p.1 ∉ K)) := by
  intro N
  induction N with
  | zero => exact ⟨fun h => absurd h (by omega), fun h => absurd h (by omega)⟩
  | succ N ih =>
    obtain ⟨ihU, ihL⟩ := ih
    refine ⟨?_, ?_⟩
    · intro a b U hsz ha hb hUlc hU hUK
      have hszeq := Unifies.size_eq hU
      cases a with
      | bvar i => cases ha with | bvar h => omega
      | prim p =>
        cases b with
        | bvar i => cases hb with | bvar h => omega
        | prim q =>
          simp only [Unifies, AgreesHM, Subst.onTy_prim, Ty.eraseBounds] at hU
          cases hU; exact ⟨[], .prim, by simp⟩
        | fvar m =>
          have hmK : m ∉ K := fun hmK => by
            have h1 : Ty.eraseBounds (U.onTy (Ty.prim p))
                = Ty.eraseBounds (U.onTy (Ty.fvar m)) := hU
            rw [hUK m hmK, Subst.onTy_prim] at h1; simp at h1
          exact ⟨[(m, .prim p)], .fvarR (by simp) (by simp [Ty.freeVars]),
            by intro p' hp'; rw [List.mem_singleton] at hp'; subst hp'; exact hmK⟩
        | arrow b₁ b₂ => simp [Unifies, AgreesHM, Subst.onTy_arrow, Subst.onTy_prim,
            Ty.eraseBounds_arrow] at hU
        | customTy nm bs => simp [Unifies, AgreesHM, Subst.onTy_customTy,
            Subst.onTy_prim, Ty.eraseBounds_customTy] at hU
        | bl lo hi e => simp [Unifies, AgreesHM, Subst.onTy_bl, Subst.onTy_prim,
            Ty.eraseBounds_bl, bareListTy] at hU
      | fvar n =>
        cases b with
        | bvar i => cases hb with | bvar h => omega
        | fvar m =>
          by_cases hnm : n = m
          · subst hnm; exact ⟨[], .fvarRefl, by simp⟩
          · by_cases hnK : n ∈ K
            · have hmK : m ∉ K := fun hmK => by
                have h1 : Ty.eraseBounds (U.onTy (Ty.fvar n))
                    = Ty.eraseBounds (U.onTy (Ty.fvar m)) := hU
                rw [hUK n hnK, hUK m hmK] at h1
                simp only [Ty.eraseBounds, Ty.fvar.injEq] at h1
                exact hnm h1
              exact ⟨[(m, .fvar n)], .fvarR (by simp only [ne_eq, Ty.fvar.injEq]; omega)
                (by simp only [Ty.freeVars, List.mem_singleton]; omega),
                by intro p' hp'; rw [List.mem_singleton] at hp'; subst hp'; exact hmK⟩
            · exact ⟨[(n, .fvar m)], .fvarL (by simp only [ne_eq, Ty.fvar.injEq]; omega)
                (by simp only [Ty.freeVars, List.mem_singleton]; omega),
                by intro p' hp'; rw [List.mem_singleton] at hp'; subst hp'; exact hnK⟩
        | prim q =>
          by_cases hocc : n ∈ (Ty.prim q).freeVars
          · exfalso; have hlt := Ty.size_onTy_fvar_lt (S := U) hocc (by simp); omega
          · by_cases hnK : n ∈ K
            · exfalso
              have h1 : Ty.eraseBounds (U.onTy (Ty.fvar n))
                  = Ty.eraseBounds (U.onTy (Ty.prim q)) := hU
              rw [hUK n hnK, Subst.onTy_prim] at h1; simp at h1
            · exact ⟨[(n, .prim q)], .fvarL (by simp) hocc,
                by intro p' hp'; rw [List.mem_singleton] at hp'; subst hp'; exact hnK⟩
        | arrow b₁ b₂ =>
          by_cases hocc : n ∈ (Ty.arrow b₁ b₂).freeVars
          · exfalso; have hlt := Ty.size_onTy_fvar_lt (S := U) hocc (by simp); omega
          · by_cases hnK : n ∈ K
            · exfalso
              have h1 : Ty.eraseBounds (U.onTy (Ty.fvar n))
                  = Ty.eraseBounds (U.onTy (Ty.arrow b₁ b₂)) := hU
              rw [hUK n hnK, Subst.onTy_arrow] at h1; simp at h1
            · exact ⟨[(n, .arrow b₁ b₂)], .fvarL (by simp) hocc,
                by intro p' hp'; rw [List.mem_singleton] at hp'; subst hp'; exact hnK⟩
        | customTy nm bs =>
          by_cases hocc : n ∈ (Ty.customTy nm bs).freeVars
          · exfalso; have hlt := Ty.size_onTy_fvar_lt (S := U) hocc (by simp); omega
          · by_cases hnK : n ∈ K
            · exfalso
              have h1 : Ty.eraseBounds (U.onTy (Ty.fvar n))
                  = Ty.eraseBounds (U.onTy (Ty.customTy nm bs)) := hU
              rw [hUK n hnK, Subst.onTy_customTy] at h1; simp at h1
            · exact ⟨[(n, .customTy nm bs)], .fvarL (by simp) hocc,
                by intro p' hp'; rw [List.mem_singleton] at hp'; subst hp'; exact hnK⟩
        | bl lo hi e =>
          by_cases hocc : n ∈ (Ty.bl lo hi e).freeVars
          · exfalso; have hlt := Ty.size_onTy_fvar_lt (S := U) hocc (by simp); omega
          · by_cases hnK : n ∈ K
            · -- rigid: `U` maps `.fvar n` to itself, but any BL image erases to a
              -- bare-`List`-headed type — heads cannot agree
              exfalso
              have hUKn : U.onTy (.fvar n) = .fvar n := hUK n hnK
              simp only [Unifies, AgreesHM] at hU
              rw [hUKn] at hU
              simp [Subst.onTy_bl, Ty.eraseBounds_bl, bareListTy] at hU
            · exact ⟨[(n, .bl lo hi e)], .fvarL (by simp) hocc,
                by intro p' hp'; rw [List.mem_singleton] at hp'; subst hp'; exact hnK⟩
      | arrow a₁ a₂ =>
        cases ha with
        | arrow ha₁ ha₂ =>
        cases b with
        | bvar i => cases hb with | bvar h => omega
        | fvar m =>
          by_cases hocc : m ∈ (Ty.arrow a₁ a₂).freeVars
          · exfalso; have hlt := Ty.size_onTy_fvar_lt (S := U) hocc (by simp); omega
          · by_cases hmK : m ∈ K
            · exfalso
              have h1 : Ty.eraseBounds (U.onTy (Ty.arrow a₁ a₂))
                  = Ty.eraseBounds (U.onTy (Ty.fvar m)) := hU
              rw [hUK m hmK, Subst.onTy_arrow] at h1; simp at h1
            · exact ⟨[(m, .arrow a₁ a₂)], .fvarR (by simp) hocc,
                by intro p' hp'; rw [List.mem_singleton] at hp'; subst hp'; exact hmK⟩
        | prim q => simp [Unifies, AgreesHM, Subst.onTy_arrow, Subst.onTy_prim,
            Ty.eraseBounds_arrow] at hU
        | customTy nm bs => simp [Unifies, AgreesHM, Subst.onTy_arrow,
            Subst.onTy_customTy, Ty.eraseBounds_arrow, Ty.eraseBounds_customTy] at hU
        | bl lo hi e =>
          exfalso
          simp [Unifies, AgreesHM, Subst.onTy_arrow, Subst.onTy_bl,
            Ty.eraseBounds_arrow, Ty.eraseBounds_bl, bareListTy] at hU
        | arrow b₁ b₂ =>
          cases hb with
          | arrow hb₁ hb₂ =>
          have hpsz : (U.onTy (.arrow a₁ a₂)).size
              = 1 + (U.onTy a₁).size + (U.onTy a₂).size := by simp [Subst.onTy_arrow, Ty.size]
          simp only [Unifies, AgreesHM, Subst.onTy_arrow, Ty.eraseBounds_arrow,
                     Ty.arrow.injEq] at hU
          obtain ⟨S₁, h₁, hS₁K⟩ := ihU (a := a₁) (b := b₁) (U := U)
            (by rw [hpsz] at hsz; omega) ha₁ hb₁ hUlc hU.1 hUK
          have hS₁lc := UnifyRel.lc h₁ ha₁ hb₁
          obtain ⟨R, hRfac, hRlc, hRK⟩ := UnifyRel.greatest_K_factors h₁ U hUlc hU.1 hUK
          have hU2 : Unifies R (S₁.onTy a₂) (S₁.onTy b₂) := by
            show AgreesHM (R.onTy (S₁.onTy a₂)) (R.onTy (S₁.onTy b₂))
            have e1 := hRfac a₂
            have e2 := hRfac b₂
            simp only [AgreesHM] at e1 e2 ⊢
            rw [e1.symm, hU.2, e2]
          obtain ⟨S₂, h₂, hS₂K⟩ := ihU (a := S₁.onTy a₂) (b := S₁.onTy b₂) (U := R)
            (by
              have h : (R.onTy (S₁.onTy a₂)).size = (U.onTy a₂).size :=
                (hRfac a₂).size_eq.symm
              rw [h]
              rw [hpsz] at hsz; omega)
            (Subst.onTy_lc hS₁lc ha₂) (Subst.onTy_lc hS₁lc hb₂) hRlc hU2 hRK
          exact ⟨S₁ ++ S₂, .arrow h₁ h₂, by
            intro p hp; rcases List.mem_append.mp hp with h | h
            · exact hS₁K p h
            · exact hS₂K p h⟩
      | customTy nm tys₁ =>
        cases b with
        | bvar i => cases hb with | bvar h => omega
        | fvar m =>
          by_cases hocc : m ∈ (Ty.customTy nm tys₁).freeVars
          · exfalso; have hlt := Ty.size_onTy_fvar_lt (S := U) hocc (by simp); omega
          · by_cases hmK : m ∈ K
            · exfalso
              have h1 : Ty.eraseBounds (U.onTy (Ty.customTy nm tys₁))
                  = Ty.eraseBounds (U.onTy (Ty.fvar m)) := hU
              rw [hUK m hmK, Subst.onTy_customTy] at h1; simp at h1
            · exact ⟨[(m, .customTy nm tys₁)], .fvarR (by simp) hocc,
                by intro p' hp'; rw [List.mem_singleton] at hp'; subst hp'; exact hmK⟩
        | prim q => simp [Unifies, AgreesHM, Subst.onTy_customTy, Subst.onTy_prim,
            Ty.eraseBounds_customTy] at hU
        | arrow b₁ b₂ => simp [Unifies, AgreesHM, Subst.onTy_customTy,
            Subst.onTy_arrow, Ty.eraseBounds_customTy, Ty.eraseBounds_arrow] at hU
        | bl lo hi e =>
          cases hb with
          | bl heb =>
          by_cases hnm : nm = listTyName
          · subst hnm
            match tys₁ with
            | [x] =>
              obtain ⟨S, hS, hSK⟩ := ihU (a := x) (b := e) (U := U)
                (by
                  have hcsz : (U.onTy (.customTy listTyName [x])).size
                      = 1 + (U.onTy x).size := by
                    simp [Subst.onTy_customTy, Ty.size, TyList.size]
                  rw [hcsz] at hsz; omega)
                (by cases ha with | customTy h => exact h x List.mem_cons_self) heb hUlc
                (AgreesHM.list_elem_bl hU) hUK
              exact ⟨S, .listBl hS, hSK⟩
            | [] =>
              exfalso
              exact absurd hU (fun hc => by
                simp only [Unifies, AgreesHM, Subst.onTy_customTy, Subst.onTy_bl,
                  Ty.eraseBounds_customTy, Ty.eraseBounds_bl, bareListTy,
                  Ty.customTy.injEq, List.map_nil, TyList.eraseBounds,
                  List.cons.injEq, true_and, reduceCtorEq] at hc)
            | _ :: _ :: _ =>
              exfalso
              exact absurd hU (fun hc => by
                simp only [Unifies, AgreesHM, Subst.onTy_customTy, Subst.onTy_bl,
                  Ty.eraseBounds_customTy, Ty.eraseBounds_bl, bareListTy,
                  Ty.customTy.injEq, List.map_cons, TyList.eraseBounds,
                  List.cons.injEq, true_and, reduceCtorEq] at hc
                exact hc.2.elim)
          · exact absurd (AgreesHM.customTy_bl_name hU) hnm
        | customTy nm' tys₂ =>
          have hcsz : (U.onTy (.customTy nm tys₁)).size
              = 1 + TyList.size (tys₁.map U.onTy) := by simp [Subst.onTy_customTy, Ty.size]
          simp only [Unifies, AgreesHM, Subst.onTy_customTy, Ty.eraseBounds_customTy,
                     Ty.customTy.injEq, TyList.eraseBounds_eq_map] at hU
          obtain ⟨rfl, hmapeq0⟩ := hU
          have hmapeq : tys₁.map (fun t => Ty.eraseBounds (U.onTy t))
              = tys₂.map (fun t => Ty.eraseBounds (U.onTy t)) := by
            rw [← List.map_map_pointwise U.onTy Ty.eraseBounds tys₁,
                ← List.map_map_pointwise U.onTy Ty.eraseBounds tys₂]
            exact hmapeq0
          have hlen : tys₁.length = tys₂.length := by
            have h := congrArg List.length hmapeq; simpa using h
          obtain ⟨S, hS, hSK⟩ := ihL (as := tys₁) (bs := tys₂) (U := U)
            (by rw [hcsz] at hsz; omega)
            (fun t ht => by cases ha with | customTy h => exact h t ht)
            (fun t ht => by cases hb with | customTy h => exact h t ht)
            hUlc hlen hmapeq hUK
          exact ⟨S, .customTy hS, hSK⟩
      | bl lo₁ hi₁ e₁ =>
        cases ha with
        | bl hea =>
        cases b with
        | bvar i => cases hb with | bvar h => omega
        | fvar m =>
          by_cases hocc : m ∈ (Ty.bl lo₁ hi₁ e₁).freeVars
          · exfalso; have hlt := Ty.size_onTy_fvar_lt (S := U) hocc (by simp); omega
          · by_cases hmK : m ∈ K
            · exfalso
              have hUKm : U.onTy (.fvar m) = .fvar m := hUK m hmK
              simp only [Unifies, AgreesHM] at hU
              rw [hUKm] at hU
              simp [Subst.onTy_bl, Ty.eraseBounds_bl, bareListTy] at hU
            · exact ⟨[(m, .bl lo₁ hi₁ e₁)], .fvarR (by simp) hocc,
                by intro p' hp'; rw [List.mem_singleton] at hp'; subst hp'; exact hmK⟩
        | prim q => simp [Unifies, AgreesHM, Subst.onTy_bl, Subst.onTy_prim,
            Ty.eraseBounds_bl, bareListTy] at hU
        | arrow b₁ b₂ => simp [Unifies, AgreesHM, Subst.onTy_bl, Subst.onTy_arrow,
            Ty.eraseBounds_bl, Ty.eraseBounds_arrow, bareListTy] at hU
        | customTy nm' tys₂ =>
          cases hb with
          | customTy heb =>
          by_cases hnm : nm' = listTyName
          · subst hnm
            match tys₂ with
            | [α] =>
              obtain ⟨S, hS, hSK⟩ := ihU (a := e₁) (b := α) (U := U)
                (by
                  have hbsz : (U.onTy (.bl lo₁ hi₁ e₁)).size = 1 + (U.onTy e₁).size := by
                    simp [Subst.onTy_bl, Ty.size]
                  rw [hbsz] at hsz; omega)
                hea (heb α List.mem_cons_self) hUlc (AgreesHM.bl_elem_list hU) hUK
              exact ⟨S, .blList hS, hSK⟩
            | [] =>
              exfalso
              exact absurd hU.symm (fun hc => by
                simp only [Unifies, AgreesHM, Subst.onTy_customTy, Subst.onTy_bl,
                  Ty.eraseBounds_customTy, Ty.eraseBounds_bl, bareListTy,
                  Ty.customTy.injEq, List.map_nil, TyList.eraseBounds,
                  List.cons.injEq, true_and, reduceCtorEq] at hc)
            | _ :: _ :: _ =>
              exfalso
              exact absurd hU.symm (fun hc => by
                simp only [Unifies, AgreesHM, Subst.onTy_customTy, Subst.onTy_bl,
                  Ty.eraseBounds_customTy, Ty.eraseBounds_bl, bareListTy,
                  Ty.customTy.injEq, List.map_cons, TyList.eraseBounds,
                  List.cons.injEq, true_and, reduceCtorEq] at hc
                exact hc.2.elim)
          · exact absurd (AgreesHM.customTy_bl_name hU.symm) hnm
        | bl lo₂ hi₂ e₂ =>
          cases hb with
          | bl heb =>
          have hbsz : (U.onTy (.bl lo₁ hi₁ e₁)).size = 1 + (U.onTy e₁).size := by
            simp [Subst.onTy_bl, Ty.size]
          simp only [Unifies, AgreesHM, Subst.onTy_bl, Ty.eraseBounds_bl, bareListTy,
                     Ty.customTy.injEq, TyList.eraseBounds, List.cons.injEq,
                     true_and, and_true] at hU
          obtain ⟨S, hS, hSK⟩ := ihU (a := e₁) (b := e₂) (U := U)
            (by rw [hbsz] at hsz; omega) hea heb hUlc hU hUK
          exact ⟨S, .bl hS, hSK⟩
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
              = (U.onTy t₁).size + TyList.size (ts₁.map U.onTy) := by
            simp [List.map_cons, TyList.size]
          have ht1pos := @Ty.size_pos (U.onTy t₁)
          obtain ⟨S₁, h₁, hS₁K⟩ := ihU (a := t₁) (b := t₂) (U := U)
            (by rw [htsz] at hsz; omega) (has t₁ List.mem_cons_self)
            (hbs t₂ List.mem_cons_self) hUlc hmap.1 hUK
          have hS₁lc := UnifyRel.lc h₁ (has t₁ List.mem_cons_self) (hbs t₂ List.mem_cons_self)
          obtain ⟨R, hRfac, hRlc, hRK⟩ := UnifyRel.greatest_K_factors h₁ U hUlc hmap.1 hUK
          have key : ∀ t : Ty, AgreesHM (R.onTy (S₁.onTy t)) (U.onTy t) :=
            fun t => (hRfac t).symm
          have hmaptail : (ts₁.map S₁.onTy).map (fun t => Ty.eraseBounds (R.onTy t))
              = (ts₂.map S₁.onTy).map (fun t => Ty.eraseBounds (R.onTy t)) := by
            rw [List.map_map_pointwise (g := S₁.onTy)
                  (f := fun t => Ty.eraseBounds (R.onTy t)) (l := ts₁),
                List.map_congr_left (fun t (_ : t ∈ ts₁) => key t),
                List.map_map_pointwise (g := S₁.onTy)
                  (f := fun t => Ty.eraseBounds (R.onTy t)) (l := ts₂),
                List.map_congr_left (fun t (_ : t ∈ ts₂) => key t)]
            exact hmap.2
          obtain ⟨S₂, h₂, hS₂K⟩ := ihL (as := ts₁.map S₁.onTy) (bs := ts₂.map S₁.onTy)
            (U := R)
            (by
              have step1 : (ts₁.map S₁.onTy).map R.onTy
                  = ts₁.map (fun t => R.onTy (S₁.onTy t)) :=
                List.map_map_pointwise _ _ _
              have hsC : TyList.size (ts₁.map (fun t => R.onTy (S₁.onTy t)))
                  = TyList.size (ts₁.map U.onTy) :=
                TyList.size_map_congr (fun t => (key t).size_eq) ts₁
              rw [step1, hsC]
              rw [htsz] at hsz; omega)
            (by
              intro t ht; obtain ⟨t0, ht0, rfl⟩ := List.mem_map.mp ht
              exact Subst.onTy_lc hS₁lc (has t0 (List.mem_cons_of_mem _ ht0)))
            (by
              intro t ht; obtain ⟨t0, ht0, rfl⟩ := List.mem_map.mp ht
              exact Subst.onTy_lc hS₁lc (hbs t0 (List.mem_cons_of_mem _ ht0)))
            hRlc
            (by simp only [List.length_map]; have := hlen; simpa using this)
            hmaptail hRK
          exact ⟨S₁ ++ S₂, .cons h₁ h₂, by
            intro p hp; rcases List.mem_append.mp hp with h | h
            · exact hS₁K p h
            · exact hS₂K p h⟩

/-- A `K`-fixing LC unifier of two LC types yields a `UnifyRel` derivation that
    **avoids `K`**. -/
theorem UnifyRel.complete_K {K : List Nat} {a b : Ty} {U : Subst}
    (ha : a.IsLC) (hb : b.IsLC) (hUlc : ∀ p ∈ U, p.2.IsLC)
    (hU : Unifies U a b) (hUK : ∀ k ∈ K, U.onTy (.fvar k) = .fvar k) :
    ∃ S, UnifyRel a b S ∧ (∀ p ∈ S, p.1 ∉ K) :=
  (UnifyRel.complete_K_aux (2 * (U.onTy a).size + 1)).1 (by omega) ha hb hUlc hU hUK


/-! ### Rigidity-aware completeness of the *executable* unifier

`unifyCoreK` refuses to bind rigid vars; the `K`-fixing witness rules out every
branch it would refuse, so success follows from the same size induction. -/
theorem unifyCoreK_complete_aux {K : List Nat} : ∀ (N : Nat),
    (∀ {a b : Ty} {U : Subst}, 2 * (U.onTy a).size < N → a.IsLC → b.IsLC →
        (∀ p ∈ U, p.2.IsLC) → Unifies U a b → (∀ k ∈ K, U.onTy (.fvar k) = .fvar k) →
        (unifyCoreK K a b).isSome) ∧
    (∀ {as bs : List Ty} {U : Subst}, 2 * TyList.size (as.map U.onTy) + 1 < N →
        (∀ t ∈ as, t.IsLC) → (∀ t ∈ bs, t.IsLC) → (∀ p ∈ U, p.2.IsLC) →
        as.length = bs.length →
        as.map (fun t => Ty.eraseBounds (U.onTy t))
          = bs.map (fun t => Ty.eraseBounds (U.onTy t)) →
        (∀ k ∈ K, U.onTy (.fvar k) = .fvar k) →
        (unifyListCoreK K as bs).isSome) := by
  intro N
  induction N with
  | zero => exact ⟨fun h => absurd h (by omega), fun h => absurd h (by omega)⟩
  | succ N ih =>
    obtain ⟨ihU, ihL⟩ := ih
    refine ⟨?_, ?_⟩
    · intro a b U hsz ha hb hUlc hU hUK
      have hszeq := Unifies.size_eq hU
      cases a with
      | bvar i => cases ha with | bvar h => omega
      | prim p =>
        cases b with
        | bvar i => cases hb with | bvar h => omega
        | prim q =>
          simp only [Unifies, AgreesHM, Subst.onTy_prim, Ty.eraseBounds] at hU
          cases hU; simp [unifyCoreK]
        | fvar m =>
          have hmK : m ∉ K := fun hmK => by
            have h1 : Ty.eraseBounds (U.onTy (Ty.prim p))
                = Ty.eraseBounds (U.onTy (Ty.fvar m)) := hU
            rw [hUK m hmK, Subst.onTy_prim] at h1; simp at h1
          simp [unifyCoreK, hmK, Ty.freeVars]
        | arrow b₁ b₂ => simp [Unifies, AgreesHM, Subst.onTy_arrow, Subst.onTy_prim,
            Ty.eraseBounds_arrow] at hU
        | customTy nm bs => simp [Unifies, AgreesHM, Subst.onTy_customTy,
            Subst.onTy_prim, Ty.eraseBounds_customTy] at hU
        | bl lo hi e => simp [Unifies, AgreesHM, Subst.onTy_bl, Subst.onTy_prim,
            Ty.eraseBounds_bl, bareListTy] at hU
      | fvar n =>
        cases b with
        | bvar i => cases hb with | bvar h => omega
        | fvar m =>
          by_cases hnm : n = m
          · subst hnm; simp [unifyCoreK]
          · by_cases hnK : n ∈ K
            · have hmK : m ∉ K := fun hmK => by
                have h1 : Ty.eraseBounds (U.onTy (Ty.fvar n))
                    = Ty.eraseBounds (U.onTy (Ty.fvar m)) := hU
                rw [hUK n hnK, hUK m hmK] at h1
                simp only [Ty.eraseBounds, Ty.fvar.injEq] at h1
                exact hnm h1
              simp [unifyCoreK, hnm, hnK, hmK]
            · simp [unifyCoreK, hnm, hnK]
        | prim q =>
          by_cases hocc : n ∈ (Ty.prim q).freeVars
          · exfalso; have hlt := Ty.size_onTy_fvar_lt (S := U) hocc (by simp); omega
          · by_cases hnK : n ∈ K
            · exfalso
              have h1 : Ty.eraseBounds (U.onTy (Ty.fvar n))
                  = Ty.eraseBounds (U.onTy (Ty.prim q)) := hU
              rw [hUK n hnK, Subst.onTy_prim] at h1; simp at h1
            · simp [unifyCoreK, hnK, hocc]
        | arrow b₁ b₂ =>
          by_cases hocc : n ∈ (Ty.arrow b₁ b₂).freeVars
          · exfalso; have hlt := Ty.size_onTy_fvar_lt (S := U) hocc (by simp); omega
          · by_cases hnK : n ∈ K
            · exfalso
              have h1 : Ty.eraseBounds (U.onTy (Ty.fvar n))
                  = Ty.eraseBounds (U.onTy (Ty.arrow b₁ b₂)) := hU
              rw [hUK n hnK, Subst.onTy_arrow] at h1; simp at h1
            · simp [unifyCoreK, hnK, hocc]
        | customTy nm bs =>
          by_cases hocc : n ∈ (Ty.customTy nm bs).freeVars
          · exfalso; have hlt := Ty.size_onTy_fvar_lt (S := U) hocc (by simp); omega
          · by_cases hnK : n ∈ K
            · exfalso
              have h1 : Ty.eraseBounds (U.onTy (Ty.fvar n))
                  = Ty.eraseBounds (U.onTy (Ty.customTy nm bs)) := hU
              rw [hUK n hnK, Subst.onTy_customTy] at h1; simp at h1
            · simp [unifyCoreK, hnK, hocc]
        | bl lo hi e =>
          by_cases hocc : n ∈ (Ty.bl lo hi e).freeVars
          · exfalso; have hlt := Ty.size_onTy_fvar_lt (S := U) hocc (by simp); omega
          · by_cases hnK : n ∈ K
            · exfalso
              have hUKn : U.onTy (.fvar n) = .fvar n := hUK n hnK
              simp only [Unifies, AgreesHM] at hU
              rw [hUKn] at hU
              simp [Subst.onTy_bl, Ty.eraseBounds_bl, bareListTy] at hU
            · simp [unifyCoreK, hnK, hocc]
      | arrow a₁ a₂ =>
        cases ha with
        | arrow ha₁ ha₂ =>
        cases b with
        | bvar i => cases hb with | bvar h => omega
        | fvar m =>
          by_cases hocc : m ∈ (Ty.arrow a₁ a₂).freeVars
          · exfalso; have hlt := Ty.size_onTy_fvar_lt (S := U) hocc (by simp); omega
          · by_cases hmK : m ∈ K
            · exfalso
              have h1 : Ty.eraseBounds (U.onTy (Ty.arrow a₁ a₂))
                  = Ty.eraseBounds (U.onTy (Ty.fvar m)) := hU
              rw [hUK m hmK, Subst.onTy_arrow] at h1; simp at h1
            · simp [unifyCoreK, hmK, hocc]
        | prim q => simp [Unifies, AgreesHM, Subst.onTy_arrow, Subst.onTy_prim,
            Ty.eraseBounds_arrow] at hU
        | customTy nm bs => simp [Unifies, AgreesHM, Subst.onTy_arrow,
            Subst.onTy_customTy, Ty.eraseBounds_arrow, Ty.eraseBounds_customTy] at hU
        | bl lo hi e =>
          exfalso
          simp [Unifies, AgreesHM, Subst.onTy_arrow, Subst.onTy_bl,
            Ty.eraseBounds_arrow, Ty.eraseBounds_bl, bareListTy] at hU
        | arrow b₁ b₂ =>
          cases hb with
          | arrow hb₁ hb₂ =>
          have hpsz : (U.onTy (.arrow a₁ a₂)).size
              = 1 + (U.onTy a₁).size + (U.onTy a₂).size := by simp [Subst.onTy_arrow, Ty.size]
          simp only [Unifies, AgreesHM, Subst.onTy_arrow, Ty.eraseBounds_arrow,
                     Ty.arrow.injEq] at hU
          obtain ⟨⟨S₁, h₁, _⟩, he1⟩ := Option.isSome_iff_exists.mp
            (ihU (a := a₁) (b := b₁) (U := U)
              (by rw [hpsz] at hsz; omega) ha₁ hb₁ hUlc hU.1 hUK)
          have hS₁lc := UnifyRel.lc h₁ ha₁ hb₁
          obtain ⟨R, hRfac, hRlc, hRK⟩ := UnifyRel.greatest_K_factors h₁ U hUlc hU.1 hUK
          obtain ⟨⟨S₂, h₂, _⟩, he2⟩ := Option.isSome_iff_exists.mp
            (ihU (a := S₁.onTy a₂) (b := S₁.onTy b₂) (U := R)
              (by
                have h : (R.onTy (S₁.onTy a₂)).size = (U.onTy a₂).size :=
                  (hRfac a₂).size_eq.symm
                rw [h]
                rw [hpsz] at hsz; omega)
              (Subst.onTy_lc hS₁lc ha₂) (Subst.onTy_lc hS₁lc hb₂) hRlc
              (by
                show AgreesHM (R.onTy (S₁.onTy a₂)) (R.onTy (S₁.onTy b₂))
                have e1 := hRfac a₂
                have e2 := hRfac b₂
                simp only [AgreesHM] at e1 e2 ⊢
                rw [e1.symm, hU.2, e2]) hRK)
          rw [unifyCoreK]; simp only [he1, he2, Option.isSome_some]
      | customTy nm tys₁ =>
        cases b with
        | bvar i => cases hb with | bvar h => omega
        | fvar m =>
          by_cases hocc : m ∈ (Ty.customTy nm tys₁).freeVars
          · exfalso; have hlt := Ty.size_onTy_fvar_lt (S := U) hocc (by simp); omega
          · by_cases hmK : m ∈ K
            · exfalso
              have h1 : Ty.eraseBounds (U.onTy (Ty.customTy nm tys₁))
                  = Ty.eraseBounds (U.onTy (Ty.fvar m)) := hU
              rw [hUK m hmK, Subst.onTy_customTy] at h1; simp at h1
            · simp [unifyCoreK, hmK, hocc]
        | prim q => simp [Unifies, AgreesHM, Subst.onTy_customTy, Subst.onTy_prim,
            Ty.eraseBounds_customTy] at hU
        | arrow b₁ b₂ => simp [Unifies, AgreesHM, Subst.onTy_customTy,
            Subst.onTy_arrow, Ty.eraseBounds_customTy, Ty.eraseBounds_arrow] at hU
        | bl lo hi e =>
          by_cases hnm : nm = listTyName
          · subst hnm
            match tys₁ with
            | [x] =>
              -- the dedicated bare-`List` ↔ BL arm applies; recurse into elements
              have key := hU
              simp only [Unifies, AgreesHM] at key
              have hE : Ty.eraseBounds (U.onTy x) = Ty.eraseBounds (U.onTy e) :=
                AgreesHM.list_elem_bl hU
              have hcsz : (U.onTy (.customTy listTyName [x])).size
                  = 1 + (U.onTy x).size := by
                simp [Subst.onTy_customTy, Ty.size, TyList.size]
              rw [hcsz] at hsz
              obtain ⟨⟨S₁, h₁, _⟩, he1⟩ := Option.isSome_iff_exists.mp
                (ihU (a := x) (b := e) (U := U)
                  (by have := @Ty.size_pos (U.onTy e); omega)
                  (by cases ha with | customTy h => exact h x List.mem_cons_self)
                  (by cases hb with | bl heb => exact heb) hUlc hE hUK)
              rw [unifyCoreK, dif_pos rfl]; simp [he1]
            | [] =>
              exfalso
              exact absurd hU (fun hc => by
                simp only [Unifies, AgreesHM, Subst.onTy_customTy, Subst.onTy_bl,
                  Ty.eraseBounds_customTy, Ty.eraseBounds_bl, bareListTy,
                  Ty.customTy.injEq, List.map_nil, TyList.eraseBounds,
                  List.cons.injEq, true_and, reduceCtorEq] at hc)
            | _ :: _ :: _ =>
              exfalso
              exact absurd hU (fun hc => by
                simp only [Unifies, AgreesHM, Subst.onTy_customTy, Subst.onTy_bl,
                  Ty.eraseBounds_customTy, Ty.eraseBounds_bl, bareListTy,
                  Ty.customTy.injEq, List.map_cons, TyList.eraseBounds,
                  List.cons.injEq, true_and, reduceCtorEq] at hc
                exact hc.2.elim)
          · exfalso
            exact absurd (AgreesHM.customTy_bl_name hU) hnm
        | customTy nm' tys₂ =>
          have hcsz : (U.onTy (.customTy nm tys₁)).size
              = 1 + TyList.size (tys₁.map U.onTy) := by simp [Subst.onTy_customTy, Ty.size]
          simp only [Unifies, AgreesHM, Subst.onTy_customTy, Ty.eraseBounds_customTy,
                     Ty.customTy.injEq, TyList.eraseBounds_eq_map] at hU
          obtain ⟨rfl, hmapeq0⟩ := hU
          have hmapeq : tys₁.map (fun t => Ty.eraseBounds (U.onTy t))
              = tys₂.map (fun t => Ty.eraseBounds (U.onTy t)) := by
            rw [← List.map_map_pointwise U.onTy Ty.eraseBounds tys₁,
                ← List.map_map_pointwise U.onTy Ty.eraseBounds tys₂]
            exact hmapeq0
          have hlen : tys₁.length = tys₂.length := by
            have h := congrArg List.length hmapeq; simpa using h
          obtain ⟨⟨S, hS, _⟩, heL⟩ := Option.isSome_iff_exists.mp
            (ihL (as := tys₁) (bs := tys₂) (U := U)
              (by rw [hcsz] at hsz; omega)
              (fun t ht => by cases ha with | customTy h => exact h t ht)
              (fun t ht => by cases hb with | customTy h => exact h t ht)
              hUlc hlen hmapeq hUK)
          rw [unifyCoreK]; simp [heL]
      | bl lo₁ hi₁ e₁ =>
        cases ha with
        | bl hea =>
        cases b with
        | bvar i => cases hb with | bvar h => omega
        | fvar m =>
          by_cases hocc : m ∈ (Ty.bl lo₁ hi₁ e₁).freeVars
          · exfalso; have hlt := Ty.size_onTy_fvar_lt (S := U) hocc (by simp); omega
          · by_cases hmK : m ∈ K
            · exfalso
              have hUKm : U.onTy (.fvar m) = .fvar m := hUK m hmK
              simp only [Unifies, AgreesHM] at hU
              rw [hUKm] at hU
              simp [Subst.onTy_bl, Ty.eraseBounds_bl, bareListTy] at hU
            · simp [unifyCoreK, hmK, hocc]
        | prim q => simp [Unifies, AgreesHM, Subst.onTy_bl, Subst.onTy_prim,
            Ty.eraseBounds_bl, bareListTy] at hU
        | arrow b₁ b₂ => simp [Unifies, AgreesHM, Subst.onTy_bl, Subst.onTy_arrow,
            Ty.eraseBounds_bl, Ty.eraseBounds_arrow, bareListTy] at hU
        | customTy nm' tys₂ =>
          by_cases hnm : nm' = listTyName
          · subst hnm
            match tys₂ with
            | [α] =>
              cases hb with
              | customTy heb =>
              have hbsz : (U.onTy (.bl lo₁ hi₁ e₁)).size = 1 + (U.onTy e₁).size := by
                simp [Subst.onTy_bl, Ty.size]
              rw [hbsz] at hsz
              obtain ⟨⟨S₁, h₁, _⟩, he1⟩ := Option.isSome_iff_exists.mp
                (ihU (a := e₁) (b := α) (U := U)
                  (by have := @Ty.size_pos (U.onTy α); omega)
                  hea (heb α List.mem_cons_self) hUlc (AgreesHM.bl_elem_list hU) hUK)
              rw [unifyCoreK, dif_pos rfl]; simp [he1]
            | [] =>
              exfalso
              exact absurd hU.symm (fun hc => by
                simp only [Unifies, AgreesHM, Subst.onTy_customTy, Subst.onTy_bl,
                  Ty.eraseBounds_customTy, Ty.eraseBounds_bl, bareListTy,
                  Ty.customTy.injEq, List.map_nil, TyList.eraseBounds,
                  List.cons.injEq, true_and, reduceCtorEq] at hc)
            | _ :: _ :: _ =>
              exfalso
              exact absurd hU.symm (fun hc => by
                simp only [Unifies, AgreesHM, Subst.onTy_customTy, Subst.onTy_bl,
                  Ty.eraseBounds_customTy, Ty.eraseBounds_bl, bareListTy,
                  Ty.customTy.injEq, List.map_cons, TyList.eraseBounds,
                  List.cons.injEq, true_and, reduceCtorEq] at hc
                exact hc.2.elim)
          · exfalso
            exact absurd (AgreesHM.customTy_bl_name hU.symm) hnm
        | bl lo₂ hi₂ e₂ =>
          cases hb with
          | bl heb =>
          have hbsz : (U.onTy (.bl lo₁ hi₁ e₁)).size = 1 + (U.onTy e₁).size := by
            simp [Subst.onTy_bl, Ty.size]
          simp only [Unifies, AgreesHM, Subst.onTy_bl, Ty.eraseBounds_bl, bareListTy,
                     Ty.customTy.injEq, TyList.eraseBounds, List.cons.injEq,
                     true_and, and_true] at hU
          obtain ⟨⟨S₁, h₁, _⟩, he1⟩ := Option.isSome_iff_exists.mp
            (ihU (a := e₁) (b := e₂) (U := U)
              (by rw [hbsz] at hsz; omega) hea heb hUlc hU hUK)
          rw [unifyCoreK]; simp only [he1, Option.isSome_some]
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
              = (U.onTy t₁).size + TyList.size (ts₁.map U.onTy) := by
            simp [List.map_cons, TyList.size]
          have ht1pos := @Ty.size_pos (U.onTy t₁)
          obtain ⟨⟨S₁, h₁, _⟩, he1⟩ := Option.isSome_iff_exists.mp
            (ihU (a := t₁) (b := t₂) (U := U)
              (by rw [htsz] at hsz; omega) (has t₁ List.mem_cons_self)
              (hbs t₂ List.mem_cons_self) hUlc hmap.1 hUK)
          have hS₁lc := UnifyRel.lc h₁ (has t₁ List.mem_cons_self) (hbs t₂ List.mem_cons_self)
          obtain ⟨R, hRfac, hRlc, hRK⟩ := UnifyRel.greatest_K_factors h₁ U hUlc hmap.1 hUK
          have key : ∀ t : Ty, AgreesHM (R.onTy (S₁.onTy t)) (U.onTy t) :=
            fun t => (hRfac t).symm
          have hmaptail : (ts₁.map S₁.onTy).map (fun t => Ty.eraseBounds (R.onTy t))
              = (ts₂.map S₁.onTy).map (fun t => Ty.eraseBounds (R.onTy t)) := by
            rw [List.map_map_pointwise (g := S₁.onTy)
                  (f := fun t => Ty.eraseBounds (R.onTy t)) (l := ts₁),
                List.map_congr_left (fun t (_ : t ∈ ts₁) => key t),
                List.map_map_pointwise (g := S₁.onTy)
                  (f := fun t => Ty.eraseBounds (R.onTy t)) (l := ts₂),
                List.map_congr_left (fun t (_ : t ∈ ts₂) => key t)]
            exact hmap.2
          obtain ⟨⟨S₂, h₂, _⟩, he2⟩ := Option.isSome_iff_exists.mp
            (ihL (as := ts₁.map S₁.onTy) (bs := ts₂.map S₁.onTy) (U := R)
              (by
                have step1 : (ts₁.map S₁.onTy).map R.onTy
                    = ts₁.map (fun t => R.onTy (S₁.onTy t)) :=
                  List.map_map_pointwise _ _ _
                have hsC : TyList.size (ts₁.map (fun t => R.onTy (S₁.onTy t)))
                    = TyList.size (ts₁.map U.onTy) :=
                  TyList.size_map_congr (fun t => (key t).size_eq) ts₁
                rw [step1, hsC]
                rw [htsz] at hsz; omega)
              (by
                intro t ht; obtain ⟨t0, ht0, rfl⟩ := List.mem_map.mp ht
                exact Subst.onTy_lc hS₁lc (has t0 (List.mem_cons_of_mem _ ht0)))
              (by
                intro t ht; obtain ⟨t0, ht0, rfl⟩ := List.mem_map.mp ht
                exact Subst.onTy_lc hS₁lc (hbs t0 (List.mem_cons_of_mem _ ht0)))
              hRlc
              (by simp only [List.length_map]; have := hlen; simpa using this)
              hmaptail hRK)
          rw [unifyListCoreK]; simp only [he1, he2, Option.isSome_some]

/-- `unifyCoreK` completeness wrapper. -/
theorem unifyCoreK_complete {K : List Nat} {a b : Ty} {U : Subst}
    (ha : a.IsLC) (hb : b.IsLC) (hUlc : ∀ p ∈ U, p.2.IsLC)
    (hU : Unifies U a b) (hUK : ∀ k ∈ K, U.onTy (.fvar k) = .fvar k) :
    (unifyCoreK K a b).isSome :=
  (unifyCoreK_complete_aux (2 * (U.onTy a).size + 1)).1 (by omega) ha hb hUlc hU hUK

/-- `unify` completeness: `unify` succeeds whenever the (LC) inputs are unifiable.
    Reduces to `unifyCoreK_complete` at the empty rigid set. -/
theorem unify_complete {a b : Ty} {S : Subst} (h : UnifyRel a b S)
    (ha : a.IsLC) (hb : b.IsLC) : (unify a b).isSome := by
  have hcore : (unifyCore a b).isSome := by
    have h1 := unifyCoreK_complete (K := []) ha hb (UnifyRel.lc h ha hb) h.unifies (by simp)
    unfold unifyCore
    simpa [Option.isSome_map] using h1
  simpa [unify, Option.isSome_map] using hcore


/-! ## 3. Gap avoidance (domain/range locality of `Infer` substitutions)

The executable annotated-`let` arm hard-codes its skolem block
`Ys = freshVars Φ pc`, while the relation `Infer.letInAnn` permits any `N ≥ Φ`.
Bridging the two needs a *given* derivation's output substitution to leave such
a block rigid: domain AND range avoiding `[lo, hi)` below the input frontier.
Ported onto the DM-cut relations (`consMono`/`consPoly`, ceiling-based `letRec`
body environment). -/

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
  | bl _ _ e ih =>
    intro hX v hv
    simp only [Ty.openWith, Ty.instantiate, Ty.freeVars] at hv ⊢
    exact ih (fun w hw => hX w (by simpa [Ty.freeVars] using hw)) v hv

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
  | _, _, _, @UnifyRel.bl lo₁ hi₁ lo₂ hi₂ e₁ e₂ S h, ha, hb =>
    UnifyRel.gap_avoid h ha hb
  | _, _, _, @UnifyRel.blList lo hi e α S h, ha, hb => by
    obtain ⟨hd, hr⟩ := UnifyRel.gap_avoid h
      (fun v hv => ha v (by simpa [Ty.freeVars] using hv))
      (fun v hv => hb v (by
        simp only [Ty.freeVars, TyList.freeVars, List.mem_append, List.mem_singleton,
          or_false, List.not_mem_nil, List.mem_dedup]
        exact hv))
    exact ⟨hd, hr⟩
  | _, _, _, @UnifyRel.listBl lo hi e α S h, ha, hb => by
    obtain ⟨hd, hr⟩ := UnifyRel.gap_avoid h
      (fun v hv => ha v (by
        simp only [Ty.freeVars, TyList.freeVars, List.mem_append, List.mem_singleton,
          or_false, List.not_mem_nil, List.mem_dedup]
        exact hv))
      (fun v hv => hb v (by simpa [Ty.freeVars] using hv))
    exact ⟨hd, hr⟩

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
  | @letRec Φ ctx anns bindings body Φ₁ Φ₂ S₁ S₂ τ₂ _ hgroup _ hbody =>
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
    -- the body environment (ceiling schemes over the solved monotypes)
    have hBodyCtx : ∀ M ∈ ({ (S₁.onCtx ctx) with
        env := RecSpecs.ceilingSchemes
                  (genGroupVars (RecGroup.rigidVars anns bindings) (S₁.onCtx ctx).env
                    (RecSpecs.monoTys ((RecSpec.init Φ anns).map (RecSpec.onSubst S₁))))
                  anns
                  ((RecSpec.init Φ anns).map (RecSpec.onSubst S₁))
                ++ (S₁.onCtx ctx).env }).env,
        ∀ v ∈ M.body.freeVars, v < lo ∨ hi ≤ v := by
      intro M hM
      rcases List.mem_append.mp hM with hM | hM
      · exact RecSpecs.ceilingSchemes_avoidsItv hgR hhi anns hAnnsAvoid M hM
      · exact Subst.onCtx_avoidsItv hgR hctx M hM
    obtain ⟨hbτ, hbD, hbR⟩ := Infer.gap_avoid hbody
      (by have := InferRecGroup.frontier_le hgroup; omega) hBodyCtx hBodyAvoid
    refine ⟨hbτ, ?_, ?_⟩
    · intro p hp; simp only [List.mem_append] at hp
      rcases hp with hp | hp
      · exact hgD p hp
      · exact hbD p hp
    · intro p hp; simp only [List.mem_append] at hp
      rcases hp with hp | hp
      · exact hgR p hp
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
  | @consMono Φ ctx e rest τ specs Φ₁ Φ₂ S₁ S₂ S₃ τ' he huni hrest =>
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
  | @consPoly Φ N ctx σ specs e rest Φ₁ Φ₂ S₁ Schk S₂ τ hN he huni _hesc1 _hesc2 hrest =>
    intro hhi hctx hspecs htfv
    set Ys := freshVars N σ.paramCount with hYsdef
    have hσav : ∀ v ∈ σ.body.freeVars, v < lo ∨ hi ≤ v :=
      hspecs (.poly σ) List.mem_cons_self
    simp only [RecSpec.tfvs] at hσav
    have hrTfv : ∀ y ∈ (e.openTyVars Ys).tyFreeVars, y < lo ∨ hi ≤ y := by
      intro y hy
      rcases Expr.tyFreeVars_openTyVars hy with hh | hh
      · exact htfv y (List.mem_append.mpr (Or.inl hh))
      · exact Or.inr (by have := freshVars_ge y hh; omega)
    obtain ⟨hτ, hD₁, hR₁⟩ := Infer.gap_avoid he (by omega) hctx hrTfv
    have hle1 := Infer.frontier_le he
    have hσOpenAvoid : ∀ v ∈ (σ.openVars Ys).freeVars, v < lo ∨ hi ≤ v := by
      intro v hv
      rcases Ty.freeVars_openVars_subset v hv with hh | hh
      · exact hσav v hh
      · exact Or.inr (by have := freshVars_ge v hh; omega)
    obtain ⟨hD₂, hR₂⟩ := UnifyRel.gap_avoid huni hτ hσOpenAvoid
    have hRboth : ∀ p ∈ S₁ ++ Schk, ∀ v ∈ p.2.freeVars, v < lo ∨ hi ≤ v := by
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
          refine Subst.onTy_avoidsItv (S := S₁ ++ Schk) (τ := t₀) hRboth ?_ v hv
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


/-! ### Erasure-transfer kit for the pivoted spine premises (used by §4)

The spine's declarative premises are stated at erased contexts **and** erased
terms (`TypeOfHM (S₀.onCtx ctx).eraseBounds e.eraseBounds τe`). Three small
facts move sub-derivation data across that boundary:

1. `Ty.eraseBounds_rename`: erasure commutes with α-renaming, so the block-swap
   dance works verbatim at erased contexts.
2. `InstantiatesBy.erase_agrees`: an instantiation of an *erased* scheme body
   lifts to an instantiation of the raw body **by the same args**, with a result
   agreeing up to erasure (backward twin of `InstantiatesBy.eraseBounds`). The
   conclusion is `AgreesHM`-shaped, not equality: a decorated witness may
   instantiate the erased body verbatim while the raw body reproduces it only
   at a bare-`List` shape (the `.bl` position).
3. `Subst.onCtx_congr_hm` (InferW): substitutions agreeing below the frontier
   produce EQUAL erased contexts, so erased premises transport across residual
   points by context-identity, with declarative types untouched (this discharges
   COMPLETE-APP-RESIDUAL). -/

theorem Ty.eraseBounds_rename (τ : Ty) (f : Nat → Nat) :
    Ty.eraseBounds (Ty.rename f τ) = Ty.rename f (Ty.eraseBounds τ) := by
  induction τ using Ty.rec_strong with
  | prim p => rfl
  | bvar i => rfl
  | fvar n => rfl
  | arrow a b iha ihb => simp only [Ty.rename_arrow, Ty.eraseBounds_arrow, iha, ihb]
  | customTy nm tys ih =>
    simp only [Ty.rename_customTy, Ty.eraseBounds_customTy, TyList.eraseBounds_eq_map,
      List.map_map]
    exact congrArg (Ty.customTy nm) (List.map_congr_left fun t ht => ih t ht)
  | bl lo hi e ih =>
    show Ty.customTy listTyName [Ty.eraseBounds (Ty.rename f e)]
        = Ty.rename f (Ty.customTy listTyName [Ty.eraseBounds e])
    rw [ih]
    rfl

/-- Agreement-congruence under the `arrow` head. -/
theorem AgreesHM.arrow {a₁ b₁ a₂ b₂ : Ty} (h₁ : AgreesHM a₁ a₂) (h₂ : AgreesHM b₁ b₂) :
    AgreesHM (.arrow a₁ b₁) (.arrow a₂ b₂) :=
  congrArg₂ _ ((h₁ : Ty.eraseBounds a₁ = Ty.eraseBounds a₂))
              ((h₂ : Ty.eraseBounds b₁ = Ty.eraseBounds b₂))

/-- Agreement-congruence under the `customTy` head. -/
theorem AgreesHM.customTy {nm : TyName} {as bs : List Ty}
    (h : TyList.eraseBounds as = TyList.eraseBounds bs) :
    AgreesHM (.customTy nm as) (.customTy nm bs) := by
  show Ty.customTy nm (TyList.eraseBounds as) = Ty.customTy nm (TyList.eraseBounds bs)
  rw [h]

/-- A bare-`List`-headed type agrees with the `BL` whose element it agrees with
    (both erase to the same one-element bare list). -/
theorem AgreesHM.customTy_singleton_bl {x y : Ty} {lo hi : FHM.Bounds.CountSlot}
    (h : AgreesHM x y) :
    AgreesHM (Ty.customTy listTyName [x]) (.bl lo hi y) := by
  show Ty.customTy listTyName [Ty.eraseBounds x] = Ty.customTy listTyName [Ty.eraseBounds y]
  exact congrArg (fun z => Ty.customTy listTyName [z])
    (h : Ty.eraseBounds x = Ty.eraseBounds y)

private theorem InstantiatesBy.erase_agrees_forall2 {ts : List Ty} :
    ∀ (tys instTys : List Ty),
      List.Forall₂ (InstantiatesBy ts) (TyList.eraseBounds tys) instTys →
      (∀ t ∈ tys, ∀ {τ : Ty}, InstantiatesBy ts (Ty.eraseBounds t) τ →
        ∃ j, InstantiatesBy ts t j ∧ AgreesHM τ j) →
      ∃ js : List Ty, List.Forall₂ (InstantiatesBy ts) tys js ∧
        TyList.eraseBounds js = TyList.eraseBounds instTys := by
  intro tys
  induction tys with
  | nil =>
    intro instTys hF _
    cases hF with | nil => exact ⟨[], .nil, rfl⟩
  | cons t₀ tys₀ ih =>
    intro instTys hF hall
    cases hF with
    | cons h₁ h₂ =>
      obtain ⟨j₀, hj₀, hag₀⟩ := hall t₀ List.mem_cons_self h₁
      obtain ⟨js, hjs, hags⟩ := ih _ h₂ fun t ht => hall t (List.mem_cons_of_mem _ ht)
      refine ⟨j₀ :: js, .cons hj₀ hjs, ?_⟩
      simp only [TyList.eraseBounds]
      have e1 : ∀ x : Ty, AgreesHM x j₀ → Ty.eraseBounds x = Ty.eraseBounds j₀ :=
        fun _ h => h
      rw [e1 _ hag₀]
      exact congrArg (fun l => Ty.eraseBounds j₀ :: l) hags

/-- An instantiation of an **erased** scheme body lifts to an instantiation of
    the raw body by the SAME arguments, with an `AgreesHM`-related result.
    Backward twin of `InstantiatesBy.eraseBounds`. -/
theorem InstantiatesBy.erase_agrees {ts : List Ty} {B : Ty} :
    ∀ {τ : Ty}, InstantiatesBy ts (Ty.eraseBounds B) τ →
      ∃ τ₂, InstantiatesBy ts B τ₂ ∧ AgreesHM τ τ₂ := by
  induction B using Ty.rec_strong with
  | prim p => intro τ h; cases h with | prim => exact ⟨_, .prim, AgreesHM.refl _⟩
  | bvar i => intro τ h; cases h with | bvar hs => exact ⟨_, .bvar hs, AgreesHM.refl _⟩
  | fvar n => intro τ h; cases h with | fvar => exact ⟨_, .fvar, AgreesHM.refl _⟩
  | arrow a b iha ihb =>
    intro τ h
    cases h with
    | arrow h₁ h₂ =>
      obtain ⟨x, hx, hagx⟩ := iha h₁
      obtain ⟨y, hy, hogy⟩ := ihb h₂
      refine ⟨_, .arrow hx hy, ?_⟩
      simp only [AgreesHM, Ty.eraseBounds_arrow]
      exact congrArg₂ Ty.arrow hagx hogy
  | customTy nm tys ih =>
    intro τ h
    cases h with
    | customTy hF =>
      obtain ⟨js, hjs, hags⟩ :=
        InstantiatesBy.erase_agrees_forall2 tys _ hF (fun t ht => ih t ht)
      exact ⟨_, .customTy hjs, AgreesHM.customTy hags.symm⟩
  | bl lo hi e ih =>
    intro τ h
    simp only [Ty.eraseBounds_bl, bareListTy] at h
    cases h with
    | customTy hF =>
      -- `[erase e]` forces a singleton `Forall₂`
      cases hF with
      | @cons _ _ _ l' h₁ h₂ =>
        cases h₂            -- source tail is `[]`, forcing `l' = []`
        obtain ⟨j, hj, hag⟩ := ih h₁
        exact ⟨_, .bl hj, AgreesHM.customTy_singleton_bl hag⟩

/-! ## 4. Principality of a given inference (the D2 spine)

`Infer.Principal h hwf hbelow` says: whenever the source program `e` (WITH its
annotations) is declaratively HM-typeable in the erased context at some type,
the given inference output `(S, τ)` is principal — every such typing factors
through `τ` via an LC residual fixing `K`.

Statement notes (deviations from the brief's §1 sketch, verified before
proving): the declarative premise is at the ERASED TERM `e.eraseBounds`, not
the original annotated `e`. The original step-4 skeleton kept premises at
`TypeOfHM (S₀.onCtx ctx) e τe` (raw context AND raw term) so that `Pins`
stayed structural; but with raw-context premises, transporting a declarative
typing under a residual is exactly the decoration-lifting the design memo
records as false (the COMPLETE-APP-RESIDUAL blocker of commit `ee2cc99`). The
fix decided 2026-08-26 (supersedes the "original ANNOTATED term" clause):
erase BOTH the context and the term — `TypeOfHM (S₀.onCtx ctx).eraseBounds
e.eraseBounds τe`. Pins SURVIVE this: `Expr.eraseBounds` maps annotations via
`ann.map Ty.eraseBounds` rather than dropping them, so `Option.Pins` remains
meaningful at erase level (`λ(x : BL 3 5 Int)` still pins the binder to
`List Int`), which is all the erase-level conclusions (`AgreesHM`) ever
consume. Keeping the annotated term was investigated and is NOT manufacturable:
a *specific-type* coercion into erased contexts dies on decorated lambda pins,
and an ∃-type coercion dies on `letIn` cofinite / `match_` result uniformity /
`letRec` MonoTyped specificity. Erased-term premises make every IH re-entry
constructible from existing lemmas (`TypeOfHM.eraseBounds_of`,
`TypeOfHM.onSubst_eraseBounds_fixed`, `Subst.onCtx_congr_hm` — the latter
gives COMPLETE-APP-RESIDUAL by context identity). Each Principal also carries
the working conjunct `Subst.AgreesBelow Φ S₀ (S ++ R)` (old `CompleteAt`'s
agreement clause), which sustains K-fixing through residual composition. -/

/-- Principality of the inference output `(S, τ)`: whenever the source program
    types declaratively (erased context, erased term — Pins survive at erase
    level), every such typing factors through `τ` via an LC residual fixing `K`. -/
def Infer.Principal {Φ : Nat} {ctx : Ctx} {e : Expr} {Φ' : Nat} {S : Subst} {τ : Ty}
    (_h : Infer Φ ctx e Φ' S τ) : Prop :=
  CtxWF ctx → CtxBelow Φ ctx →
  ∀ (S₀ : Subst) (τe : Ty) (K : List Nat),
    (∀ p ∈ S₀, p.2.IsLC) → (∀ k ∈ K, k < Φ) → (∀ y ∈ e.tyFreeVars, y ∈ K) →
    (∀ k ∈ K, S₀.onTy (.fvar k) = .fvar k) →
    TypeOfHM (S₀.onCtx ctx).eraseBounds e.eraseBounds τe →
    ∃ R : Subst, (∀ p ∈ R, p.2.IsLC) ∧
      AgreesHM τe (R.onTy τ) ∧ (∀ k ∈ K, R.onTy (.fvar k) = .fvar k) ∧
      Subst.AgreesBelow Φ S₀ (S ++ R)

/-- Principality for a `match_` branch-list thread: given the declarative
    scrutinee typing and per-branch typings (erased contexts, erased terms),
    the threaded result type is principal. -/
def InferBranches.Principal {Φ : Nat} {ctx : Ctx} {scrutTy : Ty} {ρ : Ty}
    {brs : List (MatchPattern × Expr)} {Φ' : Nat} {S : Subst}
    (_h : InferBranches Φ ctx scrutTy ρ brs Φ' S) (hne : brs ≠ []) : Prop :=
  CtxWF ctx → CtxBelow Φ ctx →
  ∀ (s : Expr) (S₀ : Subst) (scruT₀ ρe : Ty) (K : List Nat),
    (∀ p ∈ S₀, p.2.IsLC) → (∀ k ∈ K, k < Φ) →
    (∀ y ∈ Expr.tyFreeVars.BranchList.tyFreeVars brs, y ∈ K) →
    (∀ k ∈ K, S₀.onTy (.fvar k) = .fvar k) →
    TypeOfHM (S₀.onCtx ctx).eraseBounds s.eraseBounds scruT₀ →
    (∀ b ∈ brs, TypeOfMatchBranch (S₀.onCtx ctx).eraseBounds (b.1, b.2.eraseBounds)
        scruT₀ ρe) →
    ∃ R : Subst, (∀ p ∈ R, p.2.IsLC) ∧
      Subst.AgreesBelow Φ S₀ (S ++ R) ∧
      AgreesHM ρe (R.onTy ρ) ∧ (∀ k ∈ K, R.onTy (.fvar k) = .fvar k)

/-- Principality for a recursive-group thread: given the declarative DM-cut
    group premises (erased contexts, erased binding terms), an LC residual
    fixing `K` exists. -/
def InferRecGroup.Principal {Φ : Nat} {ctx : Ctx} {bindings : List Expr}
    {specs : List RecSpec} {Φ' : Nat} {S : Subst}
    (_h : InferRecGroup Φ ctx bindings specs Φ' S) : Prop :=
  CtxWF ctx → CtxBelow Φ ctx →
  ∀ (S₀ : Subst) (G L : List Nat) (K : List Nat),
    (∀ p ∈ S₀, p.2.IsLC) → (∀ k ∈ K, k < Φ) →
    (∀ y ∈ Expr.tyFreeVars.RecGroup.tyFreeVars bindings, y ∈ K) →
    (∀ k ∈ K, S₀.onTy (.fvar k) = .fvar k) →
    RecSpecs.MonoTyped TypeOfHM (S₀.onCtx ctx).eraseBounds
      (bindings.map Expr.eraseBounds) specs G L →
    RecSpecs.PolyTyped TypeOfHM (S₀.onCtx ctx).eraseBounds
      (bindings.map Expr.eraseBounds) specs G L →
    ∃ R : Subst, (∀ p ∈ R, p.2.IsLC) ∧ (∀ k ∈ K, R.onTy (.fvar k) = .fvar k) ∧
      Subst.AgreesBelow Φ S₀ (S ++ R)


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
    (∀ {Φ : Nat} {ctx : Ctx} {bindings : List Expr} {specs : List RecSpec}
        {Φ' : Nat} {S : Subst},
        (_h : InferRecGroup Φ ctx bindings specs Φ' S) →
        Expr.sizeRecGroup bindings < n → CtxWF ctx → CtxBelow Φ ctx →
        InferRecGroup.Principal _h) := by
  induction n with
  | zero =>
    refine ⟨?_, ?_, ?_⟩
    · intro Φ ctx e Φ' S τ h hn _ _; exact absurd hn (Nat.not_lt_zero _)
    · intro Φ ctx scrutTy ρ brs Φ' S h hne hn _ _
      exact absurd hn (Nat.not_lt_zero _)
    · intro Φ ctx bindings specs Φ' S h hn _ _
      exact absurd hn (Nat.not_lt_zero _)
  | succ n ih =>
    refine ⟨?_, ?_, ?_⟩
    · -- Infer tier (D2 spine; one handler per constructor)
      intro Φ ctx e Φ' S τ h _hn hwf hbelow
      cases h with
      | primLitUnit =>
        intro _ _ S₀ τe K hS₀ hKΦ hKe hKfix hty
        simp only [Expr.eraseBounds] at hty
        cases hty with
        | primLitUnit =>
          refine ⟨S₀, hS₀, ?_, hKfix, fun v _ => AgreesHM.refl _⟩
          show Ty.eraseBounds (.prim .unit) = Ty.eraseBounds (Subst.onTy S₀ (.prim .unit))
          simp [Subst.onTy_prim]
      | primLitInt =>
        intro _ _ S₀ τe K hS₀ hKΦ hKe hKfix hty
        simp only [Expr.eraseBounds] at hty
        cases hty with
        | primLitInt =>
          refine ⟨S₀, hS₀, ?_, hKfix, fun v _ => AgreesHM.refl _⟩
          show Ty.eraseBounds (.prim .int) = Ty.eraseBounds (Subst.onTy S₀ (.prim .int))
          simp [Subst.onTy_prim]
      | primLitNat =>
        intro _ _ S₀ τe K hS₀ hKΦ hKe hKfix hty
        simp only [Expr.eraseBounds] at hty
        cases hty with
        | primLitNat =>
          refine ⟨S₀, hS₀, ?_, hKfix, fun v _ => AgreesHM.refl _⟩
          show Ty.eraseBounds (.prim .nat) = Ty.eraseBounds (Subst.onTy S₀ (.prim .nat))
          simp [Subst.onTy_prim]
      | primLitChar =>
        intro _ _ S₀ τe K hS₀ hKΦ hKe hKfix hty
        simp only [Expr.eraseBounds] at hty
        cases hty with
        | primLitChar =>
          refine ⟨S₀, hS₀, ?_, hKfix, fun v _ => AgreesHM.refl _⟩
          show Ty.eraseBounds (.prim .char) = Ty.eraseBounds (Subst.onTy S₀ (.prim .char))
          simp [Subst.onTy_prim]
      | primBinOpIntAdd =>
        intro _ _ S₀ τe K hS₀ hKΦ hKe hKfix hty
        simp only [Expr.eraseBounds] at hty
        cases hty with
        | primBinOpIntAdd =>
          refine ⟨S₀, hS₀, ?_, hKfix, fun v _ => AgreesHM.refl _⟩
          show Ty.eraseBounds ((.arrow (.prim .int) (.arrow (.prim .int) (.prim .int)))) = Ty.eraseBounds (Subst.onTy S₀ ((.arrow (.prim .int) (.arrow (.prim .int) (.prim .int)))))
          simp [Subst.onTy_arrow]
      | primBinOpIntSub =>
        intro _ _ S₀ τe K hS₀ hKΦ hKe hKfix hty
        simp only [Expr.eraseBounds] at hty
        cases hty with
        | primBinOpIntSub =>
          refine ⟨S₀, hS₀, ?_, hKfix, fun v _ => AgreesHM.refl _⟩
          show Ty.eraseBounds ((.arrow (.prim .int) (.arrow (.prim .int) (.prim .int)))) = Ty.eraseBounds (Subst.onTy S₀ ((.arrow (.prim .int) (.arrow (.prim .int) (.prim .int)))))
          simp [Subst.onTy_arrow]
      | primBinOpIntLt _ _ _ _ =>
        intro _ _ S₀ τe K hS₀ hKΦ hKe hKfix hty
        simp only [Expr.eraseBounds] at hty
        cases hty with
        | primBinOpIntLt _ _ =>
          refine ⟨S₀, hS₀, ?_, hKfix, fun v _ => AgreesHM.refl _⟩
          show Ty.eraseBounds ((.arrow (.prim .int) (.arrow (.prim .int)
            (.customTy ⟨"Bool"⟩ [])))) = Ty.eraseBounds (Subst.onTy S₀
            (.arrow (.prim .int) (.arrow (.prim .int) (.customTy ⟨"Bool"⟩ []))))
          simp [Subst.onTy_arrow, Subst.onTy_customTy]
      | primBinOpCharLt _ _ _ _ =>
        intro _ _ S₀ τe K hS₀ hKΦ hKe hKfix hty
        simp only [Expr.eraseBounds] at hty
        cases hty with
        | primBinOpCharLt _ _ =>
          refine ⟨S₀, hS₀, ?_, hKfix, fun v _ => AgreesHM.refl _⟩
          show Ty.eraseBounds ((.arrow (.prim .char) (.arrow (.prim .char)
            (.customTy ⟨"Bool"⟩ [])))) = Ty.eraseBounds (Subst.onTy S₀
            (.arrow (.prim .char) (.arrow (.prim .char) (.customTy ⟨"Bool"⟩ []))))
          simp [Subst.onTy_arrow, Subst.onTy_customTy]
      | @var Φ ctx i polyTy hlook =>
        exact fun hwf hbelow S₀ τe K hS₀ hKΦ hKe hKfix hty => by
          rw [Expr.eraseBounds_var] at hty
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
                  (PolyTy.eraseBounds (S₀.onPolyTy M))
              = PolyTy.eraseBounds
                  (Subst.onPolyTy (Subst.conj (blockSwap Φ W polyTy.paramCount) S₀) M) := by
            intro M hM
            have hrenM : Ty.rename (blockSwap Φ W polyTy.paramCount) M.body = M.body :=
              Ty.rename_eq_self (fun v hv => hffix v ((hbelow M hM).mem_lt v hv))
            have hwbl : ∀ v ∈ (Ty.eraseBounds (S₀.onTy M.body)).freeVars,
                ¬ (W ≤ v ∧ v < W + polyTy.paramCount) := fun v hv =>
              hWblock_of_belowW (Subst.onTy_belowFvars hS₀belowW
                ((hbelow M hM).mono (by omega))) v
                ((Ty.mem_freeVars_eraseBounds _ v).mp hv)
            simp only [PolyTy.eraseBounds, Subst.onPolyTy]
            rw [blockList_onTy hd hwbl]
            conv_rhs =>
              rw [← hrenM, Subst.onTy_conj finj, Ty.eraseBounds_rename]
          have hctxeq : (blockList Φ W polyTy.paramCount).onCtx ((S₀.onCtx ctx).eraseBounds)
              = ((Subst.conj (blockSwap Φ W polyTy.paramCount) S₀).onCtx ctx).eraseBounds := by
            show Ctx.mk
                (Subst.onEnv (blockList Φ W polyTy.paramCount)
                  (Env.eraseBounds (Subst.onEnv S₀ ctx.env)))
                (CtorEnv.eraseBounds ctx.ctors)
              = Ctx.mk
                (Env.eraseBounds
                  (Subst.onEnv (Subst.conj (blockSwap Φ W polyTy.paramCount) S₀) ctx.env))
                (CtorEnv.eraseBounds ctx.ctors)
            simp only [Ctx.mk.injEq, and_true]
            simp only [Subst.onEnv, Env.eraseBounds, List.map_map, List.map_map]
            exact List.map_congr_left henvpt
          have htyeq : (blockList Φ W polyTy.paramCount).onTy τe
              = Ty.rename (blockSwap Φ W polyTy.paramCount) τe := blockList_onTy hd hτeW
          have hren2 : TypeOfHM
              (((Subst.conj (blockSwap Φ W polyTy.paramCount) S₀).onCtx ctx).eraseBounds)
              (.var i) (Ty.rename (blockSwap Φ W polyTy.paramCount) τe) := by
            rw [hctxeq, htyeq] at hren; exact hren
          -- STEP 3: invert renamed typing — the erased scheme comes out directly.
          cases hren2 with
          | @var _ σE tyArgs2 _ _ hlook2 htyargs2 hinst2 =>
            have hElookup :
                (((Subst.conj (blockSwap Φ W polyTy.paramCount) S₀).onCtx ctx).eraseBounds).env[i]?
                  = some (PolyTy.eraseBounds
                    ((Subst.conj (blockSwap Φ W polyTy.paramCount) S₀).onPolyTy polyTy)) := by
              simp only [Subst.onCtx, Subst.onEnv, Ctx.eraseBounds, Env.eraseBounds_getElem?,
                List.getElem?_map, hlook, Option.map_some]
            have hσE : σE = PolyTy.eraseBounds
                ((Subst.conj (blockSwap Φ W polyTy.paramCount) S₀).onPolyTy polyTy) :=
              Option.some.inj (hlook2.symm.trans hElookup)
            subst hσE
            simp only [Subst.onPolyTy, PolyTy.eraseBounds_body] at hinst2
            -- pinning: lift the erased-scheme instantiation to the RAW scheme body
            obtain ⟨J, hinstJ, hJagree⟩ := InstantiatesBy.erase_agrees hinst2
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
            have hτeE : ∀ v ∈ (Ty.eraseBounds τe).freeVars,
                ¬ (W ≤ v ∧ v < W + polyTy.paramCount) :=
              fun v hv => hτeW v ((Ty.mem_freeVars_eraseBounds τe v).mp hv)
            have hXfreshJ : ∀ x ∈ freshVars Φ polyTy.paramCount, x ∉ J.freeVars := by
              intro x hx hmem
              apply hXfresh2 x hx
              have e1 : x ∈ (Ty.eraseBounds J).freeVars :=
                (Ty.mem_freeVars_eraseBounds J x).mpr hmem
              rw [show (Ty.eraseBounds J)
                    = Ty.rename (blockSwap Φ W polyTy.paramCount) (Ty.eraseBounds τe) from by
                    rw [← hJagree, Ty.eraseBounds_rename]] at e1
              rw [← Ty.eraseBounds_rename] at e1
              exact (Ty.mem_freeVars_eraseBounds _ x).mp e1
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
              rfl
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
              -- agreement up to erasure through the fvar-valued back-list
              show Ty.eraseBounds τe
                  = Ty.eraseBounds (Subst.onTy (blockListBack Φ W polyTy.paramCount) J)
              have hbackE : Ty.eraseBounds (Subst.onTy (blockListBack Φ W polyTy.paramCount) J)
                  = Subst.onTy (blockListBack Φ W polyTy.paramCount) (Ty.eraseBounds J) := by
                simp only [Subst.onTy, Ty.eraseBounds_substFvars, blockListBack,
                  List.map_map, Function.comp_apply, Ty.eraseBounds_fvar]
                exact congrArg (fun l : List (Nat × Ty) => Ty.substFvars l (Ty.eraseBounds J))
                  (List.map_congr_left (fun i _ => by simp [Ty.eraseBounds_fvar]))
              rw [hbackE,
                show (Ty.eraseBounds J)
                  = Ty.rename (blockSwap Φ W polyTy.paramCount) (Ty.eraseBounds τe) from by
                  rw [← hJagree, Ty.eraseBounds_rename],
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
      | @ctor Φ ctx name ctor hlook =>
        exact fun hwf hbelow S₀ τe K hS₀ hKΦ hKe hKfix hty => by
          simp only [Expr.eraseBounds] at hty
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
                  (PolyTy.eraseBounds (S₀.onPolyTy M))
              = PolyTy.eraseBounds
                  (Subst.onPolyTy (Subst.conj (blockSwap Φ W ctor.paramCount) S₀) M) := by
            intro M hM
            have hrenM : Ty.rename (blockSwap Φ W ctor.paramCount) M.body = M.body :=
              Ty.rename_eq_self (fun v hv => hffix v ((hbelow M hM).mem_lt v hv))
            have hwbl : ∀ v ∈ (Ty.eraseBounds (S₀.onTy M.body)).freeVars,
                ¬ (W ≤ v ∧ v < W + ctor.paramCount) := fun v hv =>
              hWblock_of_belowW (Subst.onTy_belowFvars hS₀belowW
                ((hbelow M hM).mono (by omega))) v
                ((Ty.mem_freeVars_eraseBounds _ v).mp hv)
            simp only [PolyTy.eraseBounds, Subst.onPolyTy]
            rw [blockList_onTy hd hwbl]
            conv_rhs =>
              rw [← hrenM, Subst.onTy_conj finj, Ty.eraseBounds_rename]
          have hctxeq : (blockList Φ W ctor.paramCount).onCtx ((S₀.onCtx ctx).eraseBounds)
              = ((Subst.conj (blockSwap Φ W ctor.paramCount) S₀).onCtx ctx).eraseBounds := by
            show Ctx.mk
                (Subst.onEnv (blockList Φ W ctor.paramCount)
                  (Env.eraseBounds (Subst.onEnv S₀ ctx.env)))
                (CtorEnv.eraseBounds ctx.ctors)
              = Ctx.mk
                (Env.eraseBounds
                  (Subst.onEnv (Subst.conj (blockSwap Φ W ctor.paramCount) S₀) ctx.env))
                (CtorEnv.eraseBounds ctx.ctors)
            simp only [Ctx.mk.injEq, and_true]
            simp only [Subst.onEnv, Env.eraseBounds, List.map_map, List.map_map]
            exact List.map_congr_left henvpt
          have htyeq : (blockList Φ W ctor.paramCount).onTy τe
              = Ty.rename (blockSwap Φ W ctor.paramCount) τe := blockList_onTy hd hτeW
          have hren2 : TypeOfHM
              (((Subst.conj (blockSwap Φ W ctor.paramCount) S₀).onCtx ctx).eraseBounds)
              (.ctor name) (Ty.rename (blockSwap Φ W ctor.paramCount) τe) := by
            rw [hctxeq, htyeq] at hren; exact hren
          -- STEP 3: invert renamed typing (`S₀.onCtx` leaves `ctors` untouched;
          -- erasure maps the looked-up ctor to `Ctor.eraseBounds ctor`).
          cases hren2 with
          | @ctor _ ctorE tyArgs2 _ _ hlook2 htyargs2 hinst2 =>
            have hElookup :
                LookupList.get? ((Subst.conj (blockSwap Φ W ctor.paramCount) S₀).onCtx
                  ctx).eraseBounds.ctors name = some (Ctor.eraseBounds ctor) := by
              have hm := congrArg (Option.map Ctor.eraseBounds) hlook
              simpa [Ctx.eraseBounds, CtorEnv.eraseBounds_get?, Option.map_some] using hm
            have hctorE : ctorE = Ctor.eraseBounds ctor :=
              Option.some.inj (hlook2.symm.trans hElookup)
            subst hctorE
            -- pinning: lift the erased-scheme instantiation to the RAW scheme body
            have hinst2' : InstantiatesBy tyArgs2 (Ty.eraseBounds ctor.toTy.body)
                (Ty.rename (blockSwap Φ W ctor.paramCount) τe) := by
              simpa [PolyTy.InstantiatesTo, PolyTy.eraseBounds_body, Ctor.eraseBounds_toTy]
                using hinst2
            clear hinst2
            obtain ⟨J, hinstJ, hJagree⟩ := InstantiatesBy.erase_agrees hinst2'
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
            have hτeE : ∀ v ∈ (Ty.eraseBounds τe).freeVars,
                ¬ (W ≤ v ∧ v < W + ctor.paramCount) :=
              fun v hv => hτeW v ((Ty.mem_freeVars_eraseBounds τe v).mp hv)
            have hXfreshJ : ∀ x ∈ freshVars Φ ctor.paramCount, x ∉ J.freeVars := by
              intro x hx hmem
              apply hXfresh2 x hx
              have e1 : x ∈ (Ty.eraseBounds J).freeVars :=
                (Ty.mem_freeVars_eraseBounds J x).mpr hmem
              rw [show (Ty.eraseBounds J)
                    = Ty.rename (blockSwap Φ W ctor.paramCount) (Ty.eraseBounds τe) from by
                    rw [← hJagree, Ty.eraseBounds_rename]] at e1
              rw [← Ty.eraseBounds_rename] at e1
              exact (Ty.mem_freeVars_eraseBounds _ x).mp e1
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
              rfl
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
              -- agreement up to erasure through the fvar-valued back-list
              show Ty.eraseBounds τe
                  = Ty.eraseBounds (Subst.onTy (blockListBack Φ W ctor.paramCount) J)
              have hbackE : Ty.eraseBounds (Subst.onTy (blockListBack Φ W ctor.paramCount) J)
                  = Subst.onTy (blockListBack Φ W ctor.paramCount) (Ty.eraseBounds J) := by
                simp only [Subst.onTy, Ty.eraseBounds_substFvars, blockListBack,
                  List.map_map, Function.comp_apply, Ty.eraseBounds_fvar]
                exact congrArg (fun l : List (Nat × Ty) => Ty.substFvars l (Ty.eraseBounds J))
                  (List.map_congr_left (fun i _ => by simp [Ty.eraseBounds_fvar]))
              rw [hbackE,
                show (Ty.eraseBounds J)
                  = Ty.rename (blockSwap Φ W ctor.paramCount) (Ty.eraseBounds τe) from by
                  rw [← hJagree, Ty.eraseBounds_rename],
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
          rw [Expr.eraseBounds_lambda] at hty
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
                  Ty.eraseBounds (Ty.rename (swapNat Φ W) Y)
                    = Ty.rename (swapNat Φ W) (Ty.eraseBounds Y) := by
                intro Y hYc
                have h1 : (swapSubst Φ W c).onTy Y = Ty.rename (swapNat Φ W) Y :=
                  swapSubst_onTy (Ne.symm hWΦ) (Ne.symm hcΦ) hWc hYc
                have h2 : (swapSubst Φ W c).onTy (Ty.eraseBounds Y)
                    = Ty.rename (swapNat Φ W) (Ty.eraseBounds Y) :=
                  swapSubst_onTy (Ne.symm hWΦ) (Ne.symm hcΦ) hWc
                    (fun hc' => hYc ((Ty.mem_freeVars_eraseBounds Y c).1 hc'))
                calc
                  Ty.eraseBounds (Ty.rename (swapNat Φ W) Y)
                      = Ty.eraseBounds ((swapSubst Φ W c).onTy Y) := by rw [h1]
                  _ = (swapSubst Φ W c).onTy (Ty.eraseBounds Y) := by
                        simp [swapSubst, Subst.onTy, Ty.eraseBounds_substFvars]
                  _ = Ty.rename (swapNat Φ W) (Ty.eraseBounds Y) := h2
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
              -- STEP 1: rename the declarative body derivation (raw extended base,
              -- erased subject), then move to the fully erased context of the IH.
              have hbodyK : ∀ y ∈ body.tyFreeVars, y ∈ K := by
                simpa [Expr.tyFreeVars] using hKe
              have hbodyKe : ∀ y ∈ body.eraseBounds.tyFreeVars, y ∈ K := fun y hy =>
                hbodyK y ((Expr.mem_tyFreeVars_eraseBounds body y).mp hy)
              have hbodyfixE : body.eraseBounds.substTyFvars (swapSubst Φ W c)
                  = body.eraseBounds :=
                Expr.substTyFvars_eq_self_of_not_mem_tyFreeVars (fun p hp hc => by
                  have hpΦ : Φ ≤ p.1 := by
                    simp only [swapSubst, List.mem_cons, List.not_mem_nil, or_false] at hp
                    obtain rfl | rfl | rfl := hp <;> omega
                  have := hKΦ p.1 (hbodyKe p.1 hc)
                  omega)
              have e1 := TypeOfHM.eraseBounds_of hbodyD
              have hrenE := TypeOfHM.onSubst_eraseBounds_fixed (swapSubst Φ W c)
                (swapSubst_lc Φ W c) hbodyfixE e1
              clear e1
              -- erased twin of the old context equality
              have henvpt : ∀ M ∈ ctx.env,
                  PolyTy.eraseBounds (Subst.onPolyTy (swapSubst Φ W c)
                      (PolyTy.eraseBounds (Subst.onPolyTy S₀ M)))
                  = PolyTy.eraseBounds (Subst.onPolyTy
                      (Subst.conj (swapNat Φ W) S₀
                        ++ [(Φ, Ty.rename (swapNat Φ W) paramTyD)]) M) := by
                intro M hM
                have hMbelow : ∀ v ∈ M.body.freeVars, v < Φ := (hbelow M hM).mem_lt
                have hrenM : Ty.rename (swapNat Φ W) M.body = M.body :=
                  Ty.rename_eq_self (fun v hv => hfix v (hMbelow v hv))
                have hΦnotin : Φ ∉ (Ty.rename (swapNat Φ W) (S₀.onTy M.body)).freeVars :=
                  Ty.rename_swap_not_mem_left (hWonTy (τ := M.body)
                    (fun hv => by have := hMbelow _ hv; omega))
                have hΦE : Φ ∉ (Ty.eraseBounds
                    (Ty.rename (swapNat Φ W) (S₀.onTy M.body))).freeVars := fun hc =>
                  hΦnotin ((Ty.mem_freeVars_eraseBounds _ Φ).mp hc)
                have hcrangeE : c ∉ (Ty.eraseBounds (S₀.onTy M.body)).freeVars := fun hc =>
                  Subst.not_mem_onTy_freeVars hcrange
                    (fun hv => by have := hMbelow _ hv; omega)
                    ((Ty.mem_freeVars_eraseBounds _ c).mp hc)
                simp only [PolyTy.eraseBounds, Subst.onPolyTy]
                rw [show (swapSubst Φ W c).onTy (Ty.eraseBounds (S₀.onTy M.body))
                      = Ty.rename (swapNat Φ W) (Ty.eraseBounds (S₀.onTy M.body)) from
                    swapSubst_onTy (Ne.symm hWΦ) (Ne.symm hcΦ) hWc hcrangeE,
                  ← Ty.eraseBounds_rename]
                conv_rhs =>
                  rw [← hrenM,
                    Subst.onTy_append (Subst.conj (swapNat Φ W) S₀)
                      [(Φ, Ty.rename (swapNat Φ W) paramTyD)],
                    Subst.onTy_conj finj]
                  dsimp [Subst.onTy, Ty.substFvars]
                  rw [Ty.eraseBounds_substFvar,
                    show Ty.eraseBounds (Ty.rename (swapNat Φ W) paramTyD)
                        = Ty.rename (swapNat Φ W) (Ty.eraseBounds paramTyD) from
                      Ty.eraseBounds_rename paramTyD _]
                rw [Ty.eraseBounds_idem]
                exact congrArg (fun b : Ty => (⟨M.paramCount, b⟩ : PolyTy))
                  (Ty.substFvar_fresh hΦE).symm
              have hctxeq : ((swapSubst Φ W c).onCtx
                    { (S₀.onCtx ctx).eraseBounds with
                      env := PolyTy.mkTrivial paramTyD :: ((S₀.onCtx ctx).eraseBounds).env }).eraseBounds
                  = ((Subst.conj (swapNat Φ W) S₀
                      ++ [(Φ, Ty.rename (swapNat Φ W) paramTyD)]).onCtx
                    { ctx with env := PolyTy.mkTrivial (.fvar Φ) :: ctx.env }).eraseBounds := by
                dsimp only [Subst.onCtx, Ctx.eraseBounds]
                show Ctx.mk
                    (Env.eraseBounds (Subst.onEnv (swapSubst Φ W c)
                      (PolyTy.mkTrivial paramTyD :: Env.eraseBounds (Subst.onEnv S₀ ctx.env))))
                    (CtorEnv.eraseBounds (CtorEnv.eraseBounds ctx.ctors))
                  = Ctx.mk
                    (Env.eraseBounds (Subst.onEnv
                      (Subst.conj (swapNat Φ W) S₀ ++ [(Φ, Ty.rename (swapNat Φ W) paramTyD)])
                      (PolyTy.mkTrivial (.fvar Φ) :: ctx.env)))
                    (CtorEnv.eraseBounds ctx.ctors)
                simp only [Ctx.mk.injEq, true_and]
                constructor
                · -- head: the pinned scheme's erased value is the same on both sides
                  have hh : PolyTy.eraseBounds (Subst.onPolyTy (swapSubst Φ W c)
                        (PolyTy.mkTrivial paramTyD))
                      = PolyTy.eraseBounds (Subst.onPolyTy
                          (Subst.conj (swapNat Φ W) S₀
                            ++ [(Φ, Ty.rename (swapNat Φ W) paramTyD)])
                          (PolyTy.mkTrivial (.fvar Φ))) := by
                    simp only [Subst.onPolyTy, PolyTy.eraseBounds_mkTrivial,
                      PolyTy.mkTrivial]
                    rw [swapSubst_onTy (Ne.symm hWΦ) (Ne.symm hcΦ) hWc hcparam,
                        Subst.onTy_append (Subst.conj (swapNat Φ W) S₀)
                          [(Φ, Ty.rename (swapNat Φ W) paramTyD)] (.fvar Φ),
                        hSconjΦ]
                    simp only [Subst.onTy, Ty.substFvars, Ty.substFvar, if_pos,
                      Ty.eraseBounds_rename, Ty.eraseBounds_idem]
                  show Env.eraseBounds
                      (Subst.onEnv (swapSubst Φ W c)
                        (PolyTy.mkTrivial paramTyD :: Env.eraseBounds (Subst.onEnv S₀ ctx.env)))
                    = Env.eraseBounds
                        (Subst.onEnv
                          (Subst.conj (swapNat Φ W) S₀ ++ [(Φ, Ty.rename (swapNat Φ W) paramTyD)])
                          (PolyTy.mkTrivial (.fvar Φ) :: ctx.env))
                  simp only [Subst.onEnv, Env.eraseBounds, List.map_cons, List.map_map]
                  rw [hh]
                  exact congrArg₂ List.cons rfl (List.map_congr_left henvpt)
                · exact CtorEnv.eraseBounds_idem ctx.ctors
              rw [hctxeq] at hrenE
              have hτe'eq : Ty.eraseBounds (Subst.onTy (swapSubst Φ W c) bodyTy)
                  = Ty.rename (swapNat Φ W) (Ty.eraseBounds bodyTy) := by
                rw [swapSubst_onTy (Ne.symm hWΦ) (Ne.symm hcΦ) hWc hcbody,
                  Ty.eraseBounds_rename]
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
              rw [Expr.eraseBounds_idem] at hrenE
              obtain ⟨R_b, hR_b, htyb, hR_bfix, hagb⟩ :=
                ih.1 hbody hsize hwf_b hbelow_b hwf_b hbelow_b S₁
                  (Ty.rename (swapNat Φ W) (Ty.eraseBounds bodyTy)) K
                  hT_lc (fun k hk => by have := hKΦ k hk; omega) hbodyK hSconjK hrenE
              have htyb' : AgreesHM (Ty.rename (swapNat Φ W) bodyTy) (R_b.onTy τb) := by
                show Ty.eraseBounds (Ty.rename (swapNat Φ W) bodyTy)
                    = Ty.eraseBounds (R_b.onTy τb)
                calc
                  Ty.eraseBounds (Ty.rename (swapNat Φ W) bodyTy)
                      = Ty.rename (swapNat Φ W) (Ty.eraseBounds bodyTy) := herase_swap hcbody
                  _ = Ty.eraseBounds (Ty.rename (swapNat Φ W) (Ty.eraseBounds bodyTy)) := by
                        rw [← Ty.eraseBounds_rename]
                        rw [Ty.eraseBounds_idem]
                  _ = Ty.eraseBounds (R_b.onTy τb) := htyb
              -- STEP 3: assemble the conclusion
              let R : Subst := R_b ++ [(W, Ty.fvar Φ)]
              have hWv : ∀ {v : Nat}, v < Φ → W ∉ (Ty.fvar v).freeVars := by
                intro v hv
                simp only [Ty.freeVars, List.mem_singleton]
                omega
              have hWparam_e : W ∉ (Ty.eraseBounds paramTyD).freeVars := by
                intro hc
                exact hWparam ((Ty.mem_freeVars_eraseBounds paramTyD W).1 hc)
              have hWbody_e : W ∉ (Ty.eraseBounds bodyTy).freeVars := by
                intro hc
                exact hWbody ((Ty.mem_freeVars_eraseBounds bodyTy W).1 hc)
              have herase_swap : ∀ {Y : Ty}, c ∉ Y.freeVars →
                  Ty.eraseBounds (Ty.rename (swapNat Φ W) Y) = Ty.rename (swapNat Φ W) (Ty.eraseBounds Y) := by
                intro Y hYc
                have h1 : (swapSubst Φ W c).onTy Y = Ty.rename (swapNat Φ W) Y :=
                  swapSubst_onTy (Ne.symm hWΦ) (Ne.symm hcΦ) hWc hYc
                have h2 : (swapSubst Φ W c).onTy (Ty.eraseBounds Y) = Ty.rename (swapNat Φ W) (Ty.eraseBounds Y) :=
                  swapSubst_onTy (Ne.symm hWΦ) (Ne.symm hcΦ) hWc
                    (fun hc' => hYc ((Ty.mem_freeVars_eraseBounds Y c).1 hc'))
                calc
                  Ty.eraseBounds (Ty.rename (swapNat Φ W) Y)
                      = Ty.eraseBounds ((swapSubst Φ W c).onTy Y) := by rw [h1]
                  _ = (swapSubst Φ W c).onTy (Ty.eraseBounds Y) := by
                        simp [swapSubst, Subst.onTy, Ty.eraseBounds_substFvars]
                  _ = Ty.rename (swapNat Φ W) (Ty.eraseBounds Y) := h2
              have hS₁onTyΦ : Subst.onTy S₁ (.fvar Φ) = Ty.rename (swapNat Φ W) paramTyD := by
                simp only [S₁]
                rw [Subst.onTy_append, hSconjΦ]
                simp only [Subst.onTy, Ty.substFvars, Ty.substFvar, if_pos]
              have hR'eq_param : AgreesHM paramTyD (Subst.onTy R (S.onTy (.fvar Φ))) := by
                change Ty.eraseBounds paramTyD = Ty.eraseBounds (Subst.onTy R (S.onTy (.fvar Φ)))
                dsimp [R]
                rw [← Subst.onTy_append, ← List.append_assoc, Subst.onTy_append]
                symm
                calc
                  Ty.eraseBounds (Subst.onTy [(W, Ty.fvar Φ)] ((S ++ R_b).onTy (.fvar Φ)))
                      = Ty.substFvar W (.fvar Φ) (Ty.eraseBounds ((S ++ R_b).onTy (.fvar Φ))) := by
                        simp [Subst.onTy, Ty.substFvars, Ty.eraseBounds_substFvar]
                  _ = Ty.substFvar W (.fvar Φ) (Ty.eraseBounds (Subst.onTy S₁ (.fvar Φ))) := by
                        rw [hagb Φ (by omega)]
                  _ = Ty.substFvar W (.fvar Φ) (Ty.eraseBounds (Ty.rename (swapNat Φ W) paramTyD)) := by
                        rw [hS₁onTyΦ]
                  _ = Ty.substFvar W (.fvar Φ) (Ty.rename (swapNat Φ W) (Ty.eraseBounds paramTyD)) := by
                        rw [herase_swap hcparam]
                  _ = Ty.eraseBounds paramTyD := Ty.substFvar_rename_swap hWparam_e
              have hR'eq_body : AgreesHM bodyTy (Subst.onTy R τb) := by
                change Ty.eraseBounds bodyTy = Ty.eraseBounds (Subst.onTy R τb)
                dsimp [R]
                rw [Subst.onTy_append]
                symm
                calc
                  Ty.eraseBounds (Subst.onTy [(W, Ty.fvar Φ)] (R_b.onTy τb))
                      = Ty.substFvar W (.fvar Φ) (Ty.eraseBounds (R_b.onTy τb)) := by
                        simp [Subst.onTy, Ty.substFvars, Ty.eraseBounds_substFvar]
                  _ = Ty.substFvar W (.fvar Φ) (Ty.eraseBounds (Ty.rename (swapNat Φ W) bodyTy)) := by
                        rw [htyb']
                  _ = Ty.substFvar W (.fvar Φ) (Ty.rename (swapNat Φ W) (Ty.eraseBounds bodyTy)) := by
                        rw [herase_swap hcbody]
                  _ = Ty.eraseBounds bodyTy := Ty.substFvar_rename_swap hWbody_e
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
                have hWonTy_v_e : W ∉ (Ty.eraseBounds (S₀.onTy (.fvar v))).freeVars := by
                  intro hc
                  exact hWonTy (τ := .fvar v) (hWv hv)
                    ((Ty.mem_freeVars_eraseBounds (S₀.onTy (.fvar v)) W).1 hc)
                dsimp [R]
                rw [← List.append_assoc, Subst.onTy_append]
                change Ty.eraseBounds (S₀.onTy (.fvar v)) = Ty.eraseBounds
                  (Subst.onTy [(W, Ty.fvar Φ)] ((S ++ R_b).onTy (.fvar v)))
                symm
                calc
                  Ty.eraseBounds (Subst.onTy [(W, Ty.fvar Φ)] ((S ++ R_b).onTy (.fvar v)))
                      = Ty.substFvar W (.fvar Φ) (Ty.eraseBounds ((S ++ R_b).onTy (.fvar v))) := by
                        simp [Subst.onTy, Ty.substFvars, Ty.eraseBounds_substFvar]
                  _ = Ty.substFvar W (.fvar Φ) (Ty.eraseBounds (Subst.onTy S₁ (.fvar v))) := by
                        rw [hagb v (by omega)]
                  _ = Ty.substFvar W (.fvar Φ) (Ty.eraseBounds (Ty.rename (swapNat Φ W) (S₀.onTy (.fvar v)))) := by
                        rw [hTv]
                  _ = Ty.substFvar W (.fvar Φ) (Ty.rename (swapNat Φ W) (Ty.eraseBounds (S₀.onTy (.fvar v)))) := by
                        rw [herase_swap (Subst.not_mem_onTy_freeVars hcrange
                          (fun hv' => by simp only [Ty.freeVars, List.mem_singleton] at hv'; omega))]
                  _ = Ty.eraseBounds (S₀.onTy (.fvar v)) :=
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
                change AgreesHM (.arrow paramTyD bodyTy)
                  (Subst.onTy R (.arrow (S.onTy (.fvar Φ)) τb))
                rw [Subst.onTy_arrow]
                show Ty.eraseBounds (.arrow paramTyD bodyTy) = Ty.eraseBounds
                  (.arrow (Subst.onTy R (S.onTy (.fvar Φ))) (Subst.onTy R τb))
                rw [Ty.eraseBounds_arrow, Ty.eraseBounds_arrow]
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
              have hpeq : paramTyD = Ty.eraseBounds paramTy :=
                hann (Ty.eraseBounds paramTy) rfl
              subst hpeq
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
              -- the erased context of the raw-extended body derivation IS the IH's
              -- premise context for S₀: heads via K-fixing of the pinned scheme,
              -- tails/ctors by erasure idempotence.
              have heqC :
                  ({ (S₀.onCtx ctx).eraseBounds with
                      env := PolyTy.mkTrivial (Ty.eraseBounds paramTy)
                                :: ((S₀.onCtx ctx).eraseBounds).env }).eraseBounds
                  = ((S₀.onCtx { ctx with
                          env := PolyTy.mkTrivial paramTy
                                    :: ctx.env })).eraseBounds := by
                dsimp only [Subst.onCtx, Ctx.eraseBounds]
                show Ctx.mk
                    (Env.eraseBounds
                      (PolyTy.mkTrivial (Ty.eraseBounds paramTy)
                        :: Env.eraseBounds (Subst.onEnv S₀ ctx.env)))
                    (CtorEnv.eraseBounds (CtorEnv.eraseBounds ctx.ctors))
                  = Ctx.mk
                    (Env.eraseBounds
                      (Subst.onEnv S₀ (PolyTy.mkTrivial paramTy :: ctx.env)))
                    (CtorEnv.eraseBounds ctx.ctors)
                simp only [Ctx.mk.injEq, true_and]
                constructor
                · show Env.eraseBounds
                      (PolyTy.mkTrivial (Ty.eraseBounds paramTy)
                        :: Env.eraseBounds (Subst.onEnv S₀ ctx.env))
                    = Env.eraseBounds
                        (Subst.onEnv S₀
                          (PolyTy.mkTrivial paramTy :: ctx.env))
                  simp [Subst.onEnv, Env.eraseBounds, List.map_cons, Subst.onPolyTy,
                    PolyTy.eraseBounds, PolyTy.mkTrivial, hself, Ty.eraseBounds_idem,
                    List.map_map]
                · exact CtorEnv.eraseBounds_idem ctx.ctors
              have e1 := TypeOfHM.eraseBounds_of hbodyD
              rw [heqC] at e1
              rw [Expr.eraseBounds_idem] at e1
              obtain ⟨R_b, hR_b, htyb, hR_bfix, hagb⟩ :=
                ih.1 hbody hsize hwf' hbelow' hwf' hbelow' S₀
                  (Ty.eraseBounds bodyTy) K hS₀ hKΦ hbodyK hKfix e1
              have htyb' : AgreesHM bodyTy (R_b.onTy τb) := by
                show Ty.eraseBounds bodyTy = Ty.eraseBounds (R_b.onTy τb)
                rw [← Ty.eraseBounds_idem]
                exact htyb
              have hparam : AgreesHM (Ty.eraseBounds paramTy)
                  (R_b.onTy (S.onTy paramTy)) := by
                change Ty.eraseBounds (Ty.eraseBounds paramTy)
                  = Ty.eraseBounds (R_b.onTy (S.onTy paramTy))
                rw [← Subst.onTy_append, ← Subst.onTy_congr_hm hagb hTbelow, hself,
                  Ty.eraseBounds_idem]
              refine ⟨R_b, hR_b, ?_, hR_bfix, hagb⟩
              change AgreesHM (.arrow (Ty.eraseBounds paramTy) bodyTy)
                (R_b.onTy (.arrow (S.onTy paramTy) τb))
              rw [Subst.onTy_arrow]
              show Ty.eraseBounds (.arrow (Ty.eraseBounds paramTy) bodyTy) = Ty.eraseBounds
                (.arrow (R_b.onTy (S.onTy paramTy)) (R_b.onTy τb))
              rw [Ty.eraseBounds_arrow, Ty.eraseBounds_arrow]
              exact congrArg₂ Ty.arrow hparam htyb'
      | @app Φ ctx f arg Φ₁ Φ₂ S₁ S₂ S₃ τf τa hf harg huni =>
        exact fun hwf hbelow S₀ τe K hS₀ hKΦ hKe hKfix hty => by
          rw [Expr.eraseBounds_app] at hty
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
            have harg' : TypeOfHM ((R_f.onCtx (S₁.onCtx ctx)).eraseBounds) arg.eraseBounds
                argTyD := by
              -- COMPLETE-APP-RESIDUAL (pivot): substitutions agreeing below the
              -- frontier produce EQUAL erased contexts, so the S₀-world typing of
              -- `arg` IS the R_f-world typing — context identity, type untouched.
              have hid : ((S₀.onCtx ctx).eraseBounds)
                  = ((R_f.onCtx (S₁.onCtx ctx)).eraseBounds) := by
                rw [← Subst.onCtx_append]
                exact Subst.onCtx_congr_hm hagf hbelow
              rw [hid] at hargD
              exact hargD
            obtain ⟨R_a, hR_a, htya, hR_aK, haga⟩ :=
              ih.1 harg hsize_a hwf₁ hbelow₁ hwf₁ hbelow₁ R_f argTyD K hR_f hKΦ₁ hKa hR_fK harg'
            -- STEP 3: explicit unifier `U` for `S₂.onTy τf` vs `.arrow τa (.fvar Φ₂)`,
            -- via a fresh `W` above everything (mirrors the old aux / exists_app_unifier_erase).
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
            have hAgreeFty' : AgreesHM (R_f.onTy τf) (R_a.onTy (S₂.onTy τf)) := by
              have h := Subst.onTy_congr_hm haga hτf_bel
              simpa [Subst.onTy_append] using h
            have hP : AgreesHM (.arrow argTyD τe) (R_a.onTy (S₂.onTy τf)) :=
              AgreesHM.trans htyf hAgreeFty'
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
            have hWargTyE : W ∉ (Ty.eraseBounds argTyD).freeVars := fun hc =>
              hWargTy ((Ty.mem_freeVars_eraseBounds argTyD W).1 hc)
            have hWτeE : W ∉ (Ty.eraseBounds τe).freeVars := fun hc =>
              hWτe ((Ty.mem_freeVars_eraseBounds τe W).1 hc)
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
            have hUniL : Ty.eraseBounds (U.onTy (S₂.onTy τf)) =
                Ty.arrow (Ty.eraseBounds argTyD) (Ty.eraseBounds τe) := by
              rw [hUonTy, Ty.substFvar_fresh hΦ₂A, Ty.eraseBounds_substFvar]
              rw [← hP, Ty.eraseBounds_arrow, hsubArrow, Ty.substFvar_fresh hWargTyE,
                Ty.substFvar_fresh hWτeE]
            have hUniR : Ty.eraseBounds (U.onTy (.arrow τa (.fvar Φ₂))) =
                Ty.arrow (Ty.eraseBounds argTyD) (Ty.eraseBounds τe) := by
              rw [hUonTy, hsubArrow, Ty.substFvar_fresh hΦ₂τa, e1, Subst.onTy_arrow,
                hR_aWfvar, hsubArrow, e2]
              rw [Ty.eraseBounds_arrow, Ty.eraseBounds_substFvar]
              rw [← htya, Ty.substFvar_fresh hWargTyE]
            have hU : Unifies U (S₂.onTy τf) (.arrow τa (.fvar Φ₂)) := by
              show Ty.eraseBounds (U.onTy (S₂.onTy τf)) =
                Ty.eraseBounds (U.onTy (.arrow τa (.fvar Φ₂)))
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
            obtain ⟨R, hRfac, hRlc, hRK⟩ := UnifyRel.greatest_K_factors huni U hUlc hU hUK
            have hAgree₃ : Subst.AgreesBelow Φ₂ R_a (S₃ ++ R) := by
              intro v hv
              rw [Subst.onTy_append]
              have h := hRfac (Ty.fvar v)
              rwa [hUbelow v hv] at h
            have hAgree₂ : Subst.AgreesBelow Φ₁ R_f ((S₂ ++ S₃) ++ R) :=
              @Subst.AgreesBelow.trans_append Φ₁ Φ₂ R_f S₂ R_a S₃ R hargle haga hS₂_bel hAgree₃
            have hAgree : Subst.AgreesBelow Φ S₀ ((S₁ ++ (S₂ ++ S₃)) ++ R) :=
              @Subst.AgreesBelow.trans_append Φ Φ₁ S₀ S₁ R_f (S₂ ++ S₃) R hfle hagf hf_sbel hAgree₂
            have hAgreeOut : AgreesHM τe (R.onTy (S₃.onTy (.fvar Φ₂))) := by
              have h := hRfac (Ty.fvar Φ₂)
              rwa [hUΦ₂] at h
            refine ⟨R, hRlc, hAgreeOut, hRK, ?_⟩
            · simpa [List.append_assoc] using hAgree
      | @letIn Φ ctx rhs body Φ₁ Φ₂ S₁ S₂ τ₁ τ₂ hrhs hbody =>
        exact fun hwf hbelow S₀ τe K hS₀ hKΦ hKe hKfix hty => by
          -- [letin-agent]
          rw [Expr.eraseBounds_letIn] at hty
          simp only [Option.map_none] at hty
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
            have hctxBridge : ((R₁.onCtx (S₁.onCtx ctx)).eraseBounds)
                = ((S₀.onCtx ctx).eraseBounds) := by
              rw [← Subst.onCtx_append]
              exact (Subst.onCtx_congr_hm hAgree₁ hbelow).symm
            -- STEP 2: the generalisation link — the algorithm scheme generalises M
            set rigid := rhs.tyFreeVars with hrigid_def
            set env₁ := (S₁.onCtx ctx).env with henv₁_def
            set genV := genVars rigid env₁ τ₁ with hgenV_def
            set Rer : Subst := R₁.map (fun p => (p.1, Ty.eraseBounds p.2)) with hRe_def
            set eτ : Ty := Ty.eraseBounds τ₁ with heτ_def
            let M' : PolyTy := PolyTy.eraseBounds (R₁.onPolyTy (genScheme rigid env₁ τ₁))
            have heτ_lc : eτ.IsLC := Ty.IsLC.eraseBounds hτ₁_lc
            have hRe_lc : ∀ p ∈ Rer, p.2.IsLC := by
              intro p hp; rw [hRe_def] at hp; obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
              exact Ty.IsLC.eraseBounds (hR₁ q hq)
            have hMwf_e : (PolyTy.eraseBounds M).WF := PolyTy.WF.eraseBounds hwfM
            have hXlen_e : Xs.length = (PolyTy.eraseBounds M).paramCount := by
              simpa [PolyTy.eraseBounds] using hXlen
            have hXMbody_e : ∀ x ∈ Xs, x ∉ (PolyTy.eraseBounds M).body.freeVars := by
              intro x hx hc
              exact hXMbody x hx ((Ty.mem_freeVars_eraseBounds M.body x).mp hc)
            have htyr_e : Ty.openVars Xs (PolyTy.eraseBounds M).body = Rer.onTy eτ := by
              rw [PolyTy.eraseBounds_body]
              have h1 : Ty.eraseBounds (M.openVars Xs) = Ty.openVars Xs (Ty.eraseBounds M.body) :=
                Ty.eraseBounds_openVars Xs M.body
              have h2 : Ty.eraseBounds (R₁.onTy τ₁) = Rer.onTy (Ty.eraseBounds τ₁) := by
                rw [hRe_def, Subst.onTy, Subst.onTy]
                exact Ty.eraseBounds_substFvars R₁ τ₁
              rw [heτ_def]
              rw [← h2, h1.symm]
              exact htyr₁
            have hXM'' : ∀ x ∈ Xs, x ∉ (Rer.onPolyTy ⟨genV.length, Ty.closeOver genV eτ⟩).body.freeVars := by
              intro x hx hcx
              rw [Subst.onPolyTy] at hcx
              have hB : Rer.onTy (Ty.closeOver genV eτ) = Ty.eraseBounds (R₁.onTy (Ty.closeOver genV τ₁)) := by
                rw [Subst.onTy, Subst.onTy, heτ_def]
                rw [Ty.eraseBounds_substFvars R₁ (Ty.closeOver genV τ₁)]
                rw [Ty.eraseBounds_closeOver]
              rw [hB] at hcx
              rw [Ty.mem_freeVars_eraseBounds (R₁.onTy (Ty.closeOver genV τ₁)) x] at hcx
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
                  have h1 : x ∈ (Ty.eraseBounds ((S₁ ++ R₁).onTy (Ty.fvar w))).freeVars :=
                    (Ty.mem_freeVars_eraseBounds ((S₁ ++ R₁).onTy (Ty.fvar w)) x).mpr hxS₁R₁
                  have h2 : x ∈ (Ty.eraseBounds (S₀.onTy (Ty.fvar w))).freeVars := by
                    rwa [hAgree₁ w hwlt]
                  exact (Ty.mem_freeVars_eraseBounds (S₀.onTy (Ty.fvar w)) x).mp h2
                rcases Subst.mem_freeVars_onTy hxS₀ with hxw | ⟨p, hp, hxp⟩
                · simp only [Ty.freeVars, List.mem_singleton] at hxw
                  exact hXrange x hx (List.mem_range.mpr (hxw ▸ hwlt))
                · exact hXS₀ran x hx (List.mem_flatMap.mpr ⟨p, hp, hxp⟩)
              · have hvK : v ∈ K := hKrhs v hrigid
                rw [hR₁K v hvK] at hxv
                simp only [Ty.freeVars, List.mem_singleton] at hxv
                exact hXK x hx (hxv ▸ hvK)
            have hgen : M'.Generalizes (PolyTy.eraseBounds M) := by
              have hg' : (Rer.onPolyTy ⟨genV.length, Ty.closeOver genV eτ⟩).Generalizes (PolyTy.eraseBounds M) := by
                exact closeOver_generalizes (g := genV) (τ₁ := eτ) (R := Rer)
                  (M := PolyTy.eraseBounds M) (Xs := Xs)
                  heτ_lc hRe_lc hMwf_e hXnodup hXlen_e hXMbody_e htyr_e hXM''
              have hscheme_eq : M' = Rer.onPolyTy ⟨genV.length, Ty.closeOver genV eτ⟩ := by
                dsimp [M']
                simp only [Subst.onPolyTy, genScheme, PolyTy.eraseBounds]
                rw [hgenV_def]
                congr 1
                rw [Subst.onTy, Subst.onTy]
                rw [Ty.eraseBounds_substFvars R₁ (Ty.closeOver genV τ₁)]
                rw [Ty.eraseBounds_closeOver]
              rw [hscheme_eq]
              exact hg'
            -- STEP 3: transport the body derivation to the algorithm scheme
            have hbE : TypeOfHM
                ({ (S₀.onCtx ctx).eraseBounds with
                    env := PolyTy.eraseBounds M :: (S₀.onCtx ctx).eraseBounds.env })
                body.eraseBounds (Ty.eraseBounds τe) := by
              simpa [Subst.onCtx, CtorEnv.eraseBounds_idem, Expr.eraseBounds_idem]
                using (TypeOfHM.eraseBounds_of hbodyD)
            have hbody_alg0 : TypeOfHM
                ({ (S₀.onCtx ctx).eraseBounds with
                    env := M' :: (S₀.onCtx ctx).eraseBounds.env })
                body.eraseBounds (Ty.eraseBounds τe) := by
              exact TypeOfHM.weaken_scheme (env_post := []) (env := (S₀.onCtx ctx).eraseBounds.env)
                (M := PolyTy.eraseBounds M) (M' := M') hgen hbE
            let ctx₁ : Ctx := { (S₁.onCtx ctx) with
                env := genScheme rhs.tyFreeVars (S₁.onCtx ctx).env τ₁ :: (S₁.onCtx ctx).env }
            have hbody_alg : TypeOfHM (R₁.onCtx ctx₁).eraseBounds body.eraseBounds (Ty.eraseBounds τe) := by
              rw [← hctxBridge] at hbody_alg0
              simpa [ctx₁, M', Subst.onCtx, Ctx.eraseBounds, Subst.onEnv, Env.eraseBounds,
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
              ih.1 hbody hsize_b hwf₁' hbelow₁' hwf₁' hbelow₁' R₁ (Ty.eraseBounds τe) K
                hR₁ hKΦ₁ hKbody hR₁K hbody_alg
            -- STEP 5: assemble
            have hAgree : Subst.AgreesBelow Φ S₀ ((S₁ ++ S₂) ++ R₂) :=
              @Subst.AgreesBelow.trans_append Φ Φ₁ S₀ S₁ R₁ S₂ R₂ hfle hAgree₁ hS₁_bel hAgree₂
            refine ⟨R₂, hR₂, by simpa [AgreesHM] using htyb₂, hR₂K, hAgree⟩
      | @letInAnn Φ N ctx σ rhs body Φ₁ Φ₂ S₁ Schk S₂ τ₁ τ₂ hσwf hN hrhs huni _hesc1 _hesc2 hbody =>
        exact fun hwf hbelow S₀ τe K hS₀ hKΦ hKe hKfix hty => by
          -- [letinann-agent]
          rw [Expr.eraseBounds_letIn] at hty
          cases hty with
          | letIn hwfM hann hcofin heq hbodyD =>
            subst heq
            rename_i M L
            have hMσ : M = PolyTy.eraseBounds σ := hann (PolyTy.eraseBounds σ) rfl
            subst hMσ
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
            have hcofinXs : TypeOfHM (S₀.onCtx ctx).eraseBounds (rhs.openTyVars Xs).eraseBounds
                ((PolyTy.eraseBounds σ).openVars Xs) := by
              simpa [Expr.openBoundTyVars, Expr.eraseBounds_openTyVars] using hcofin Xs hXfresh
            set ρ : Subst := Xs.zip (Ys.map (Ty.fvar ·)) with hρ_def
            have hρlc : ∀ p ∈ ρ, p.2.IsLC := by
              intro p hp
              rw [hρ_def] at hp
              obtain ⟨_, hpy⟩ := List.of_mem_zip hp
              obtain ⟨y, _, hyeq⟩ := List.mem_map.mp hpy
              simpa [hyeq] using (ContainsBvarsUpTo.fvar : (Ty.fvar y).IsLC)
            have hρctx : ρ.onCtx (S₀.onCtx ctx).eraseBounds = (S₀.onCtx ctx).eraseBounds := by
              rw [hρ_def]
              apply congrArg (fun E => (⟨E, (S₀.onCtx ctx).eraseBounds.ctors⟩ : Ctx))
              exact Subst.onEnv_eq_self_of_fresh (fun p hp hc => by
                have hx : p.1 ∈ Xs := (List.of_mem_zip hp).1
                exact hXavoidCtx p.1 hx ((Env.mem_freeVars_eraseBounds _ p.1).mp hc))
            have hρsubj : (rhs.openTyVars Xs).eraseBounds.substTyFvars ρ = (rhs.openTyVars Ys).eraseBounds := by
              rw [hρ_def, Expr.eraseBounds_openTyVars, Expr.eraseBounds_openTyVars]
              rw [Expr.substTyFvars_zip_openTyVars (Ys := Xs) (Xs := Ys) hXlenYs hXnodup
                (fun y hy hc => hXavoidK y hy (hKrhs y ((Expr.mem_tyFreeVars_eraseBounds rhs y).mp hc)))
                hXavoidYs]
            have hρty : ρ.onTy ((PolyTy.eraseBounds σ).openVars Xs) = (PolyTy.eraseBounds σ).openVars Ys := by
              rw [hρ_def]
              have h1 : (PolyTy.eraseBounds σ).openVars Xs = Ty.openVars Xs (Ty.eraseBounds σ.body) := rfl
              have h2 : (PolyTy.eraseBounds σ).openVars Ys = Ty.openVars Ys (Ty.eraseBounds σ.body) := rfl
              rw [h1, h2]
              change Ty.substFvars (Xs.zip (Ys.map (Ty.fvar ·))) (Ty.openVars Xs (Ty.eraseBounds σ.body))
                = Ty.openVars Ys (Ty.eraseBounds σ.body)
              rw [show Ty.substFvars (Xs.zip (Ys.map (Ty.fvar ·))) (Ty.openVars Xs (Ty.eraseBounds σ.body))
                  = Ty.openVars Ys (Ty.eraseBounds σ.body) from by
                have h3 := Ty.openWith_eq_substFvars_openVars (ty := Ty.eraseBounds σ.body)
                  (Vs := Ys.map (Ty.fvar ·)) (Xs := Xs)
                  ⟨by rw [List.length_map]; exact hXlenYs.symm, fun V hV => by
                    obtain ⟨y, _, hyeq⟩ := List.mem_map.mp hV
                    simpa [hyeq] using (ContainsBvarsUpTo.fvar : (Ty.fvar y).IsLC)⟩
                  hXnodup
                  (fun x hx hc => hXavoidK x hx (hKσ x ((Ty.mem_freeVars_eraseBounds σ.body x).mp hc)))
                  (fun x hx hc => hXavoidYs x hx (Ty.mem_freeVarsList_map_fvar.mp hc))
                calc
                  Ty.substFvars (Xs.zip (Ys.map (Ty.fvar ·))) (Ty.openVars Xs (Ty.eraseBounds σ.body))
                      = Ty.openWith (Ys.map (Ty.fvar ·)) (Ty.eraseBounds σ.body) := h3.symm
                  _ = Ty.openVars Ys (Ty.eraseBounds σ.body) :=
                    (Ty.openVars_eq_openWith (Xs := Ys) (ty := Ty.eraseBounds σ.body)).symm]
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
            have hren' : TypeOfHM (S₀'.onCtx ctx).eraseBounds (rhs.openTyVars Ys).eraseBounds
                ((PolyTy.eraseBounds σ).openVars Ys) := by
              have hctx : S₀'.onCtx ctx = S₀.onCtx ctx := Subst.onCtx_congr hS₀'agree hbelow
              rwa [← hctx] at hren
            obtain ⟨R₁, hR₁, htyr₁, hR₁K, hAgree₁⟩ :=
              ih.1 hrhs hsize_r hwf hbelowN hwf hbelowN S₀' ((PolyTy.eraseBounds σ).openVars Ys) (K ++ Ys)
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
              simpa [AgreesHM, Ty.eraseBounds_idem] using (AgreesHM.symm htyr₁)
            obtain ⟨V, hV, hVlc, hVK⟩ := UnifyRel.greatest_K_factors huni R₁ hR₁lc hUnifiesR₁ hR₁fixK
            -- STEP 4: assemble the agreement chain.
            have hAgreeRhs' : ∀ v, v < N + σ.paramCount →
                AgreesHM (S₀'.onTy (.fvar v)) (R₁.onTy (S₁.onTy (.fvar v))) := by
              intro v hv
              rw [← Subst.onTy_append]
              exact hAgree₁ v hv
            have hAgreeV : Subst.AgreesBelow (N + σ.paramCount) S₀' ((S₁ ++ Schk) ++ V) := by
              intro v hv
              unfold S₀'
              rw [Subst.onTy_append, Subst.onTy_append, Subst.onTy_append]
              simpa [hS₀'_def, Subst.onTy_append] using AgreesHM.trans (hAgreeRhs' v hv) (hV (S₁.onTy (.fvar v)))
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
            have hhead : PolyTy.eraseBounds (V.onPolyTy σ) = PolyTy.eraseBounds σ := by
              simp [Subst.onPolyTy, PolyTy.eraseBounds, hσbodyV]
            have hctx_tail : (V.onCtx (Schk.onCtx (S₁.onCtx ctx))).eraseBounds = (S₀.onCtx ctx).eraseBounds := by
              rw [← Subst.onCtx_append, ← Subst.onCtx_append]
              simpa [List.append_assoc] using (Subst.onCtx_congr_hm hAgreeΦ hbelow).symm
            have hbodyctx :
                (V.onCtx bodyCtx_alg).eraseBounds
                = { (V.onCtx (Schk.onCtx (S₁.onCtx ctx))).eraseBounds with
                    env := PolyTy.eraseBounds (V.onPolyTy σ)
                      :: (V.onCtx (Schk.onCtx (S₁.onCtx ctx))).eraseBounds.env } := by
              simp only [bodyCtx_alg, Ctx.eraseBounds, Subst.onCtx, Subst.onEnv, Env.eraseBounds,
                List.map_cons]
            have hbody_alg : TypeOfHM (V.onCtx bodyCtx_alg).eraseBounds body.eraseBounds τe := by
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
          sorry  -- COMPLETE-MATCH
      | @letRec Φ ctx anns bindings body Φ₁ Φ₂ S₁ S₂ τ₂ _ hgroup _ hbody =>
        exact fun hwf hbelow S₀ τe K hS₀ hKΦ hKe hKfix hty => by
          sorry  -- COMPLETE-LETREC
    · -- InferBranches tier
      intro Φ ctx scrutTy ρ brs Φ' S h hne _hn hwf hbelow
      cases h with
      | nil =>
        exact fun _ _ _ _ _ _ _ _ _ _ _ _ => absurd rfl hne
      | cons =>
        exact fun hwf hbelow s S₀ scruT₀ ρe K hS₀ hKΦ hKe hKfix hscrut hbrs => by
          sorry  -- SPINE-BRANCHES-CONS
      | consWild =>
        exact fun hwf hbelow s S₀ scruT₀ ρe K hS₀ hKΦ hKe hKfix _ _ => by
          sorry  -- SPINE-BRANCHES-WILD
    · -- InferRecGroup tier
      intro Φ ctx bindings specs Φ' S h _hn hwf hbelow
      cases h with
      | nil =>
        intro _ _ S₀ G L K hS₀ hKΦ hKe hKfix _ _
        refine ⟨S₀, hS₀, hKfix, fun v _ => congrArg Ty.eraseBounds rfl⟩
      | consMono =>
        exact fun hwf hbelow S₀ G L K hS₀ hKΦ hKe hKfix hmono hpoly => by
          sorry  -- SPINE-GROUP-MONO
      | consPoly =>
        exact fun hwf hbelow S₀ G L K hS₀ hKΦ hKe hKfix hmono hpoly => by
          sorry  -- SPINE-GROUP-POLY

-- END-SECTION-SPINE



