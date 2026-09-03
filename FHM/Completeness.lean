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
    per-branch typings (erased contexts, erased terms) at the ambient
    specialization `S₀`, the threaded result type is principal.

    **UNSOUNDNESS FIX 2026-08-26** (restatement authorised; see the deviation
    note below): the previous statement concluded with the *pure*
    `Subst.AgreesBelow Φ S₀ (S ++ R)` — demanded at every `v < Φ`, which for
    the `match_` caller (`Φ = Φ₁ + 1`) includes `v = Φ₁`, the running result
    variable `.fvar Φ₁` itself. At `v = Φ₁` nothing links the ambient action to
    the unifier-applied output (counterexample: `match (var 0) [wildcard
    primLitInt]` — the only declarative data is the branch's
    `AgreesHM (.fvar 1) (.prim .int)`, which no premise forces), so the old
    statement was FALSE. The restatement:
      * replaces the free `AgreesHM ρe (R.onTy ρ)` conjunct with the
        output-form `AgreesHM ρe (R.onTy (S.onTy ρ))` — the match node's output
        type IS `S₂.onTy (.fvar Φ₁)` (old match-aux STEP 5's `τ₀ = R₂.onTy
        (S₂.onTy (.fvar Φ₁))`, recovered as a first-class conjunct);
      * adds the two IMAGE premises `AgreesHM ρe (S₀.onTy ρ)` and
        `AgreesHM scruT₀ (S₀.onTy scrutTy)` — each is REFLEXIVE at the
        top-level dodge call from COMPLETE-MATCH (`S₀ = U`, `ρe = U.onTy ρ`,
        `scruT₀ = U.onTy scrutTy`), and inside each `cons`/`consWild` step they
        are re-derived at the next residual from the body IH's `AgreesBelow`
        plus the `greatest_K_factors` factoring (old complete's `key_full`/`hUni`
        steps, now AgreesHM-flavoured);
      * states LC/below-ness on the ALGORITHMIC types (`scrutTy`, `ρ`) instead
        of the declarative ones, and drops the scrutinee-term premise `s`
        entirely: the branch premises are transportable between worlds only by
        CONTEXT rewriting (`Subst.onCtx_congr_hm`), keeping `scruT₀`/`ρe`
        unchanged — a changed *declarative* scrutinee/result type is not
        re-constructible from a `TypeOfMatchBranch` up to `AgreesHM` (the `mk`
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
    AgreesHM ρe (S₀.onTy ρ) →
    AgreesHM scruT₀ (S₀.onTy scrutTy) →
    (∀ b ∈ brs, TypeOfMatchBranch (S₀.onCtx ctx).eraseBounds (b.1, b.2.eraseBounds)
        scruT₀ ρe) →
    ∃ R : Subst, (∀ p ∈ R, p.2.IsLC) ∧
      Subst.AgreesBelow Φ S₀ (S ++ R) ∧
      (∀ k ∈ K, R.onTy (.fvar k) = .fvar k) ∧
      AgreesHM ρe (R.onTy (S.onTy ρ))

/-- Principality for a recursive-group thread — **ADOPTED STATEMENT** (2026-08-26,
    design pass, supersedes the interim restatement of commit `874553b`): given
    the declarative DM-cut group premises at the ERASED context and per-member
    erased binding terms — the mono members' RHSs at the `R₀`-transported
    erase-projected monotypes `Ty.eraseBounds (R₀.onTy τ)`, the poly members'
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
    (∀ v, v < Φ₀ → AgreesHM (R₀.onTy (.fvar v)) (S₀.onTy (.fvar v))) →
    (∀ p ∈ bindings.zip specs, ∀ τ, p.2 = RecSpec.mono τ →
      TypeOfHM (R₀.onCtx ctx).eraseBounds (Expr.eraseBounds p.1)
        (Ty.eraseBounds (R₀.onTy τ))) →
    (∀ p ∈ bindings.zip specs, ∀ σ, p.2 = RecSpec.poly σ →
      ∀ Ys, FreshNames L σ.paramCount Ys →
        TypeOfHM (R₀.onCtx ctx).eraseBounds
          (Expr.eraseBounds (Expr.openTyVars Ys p.1)) (σ.openVars Ys)) →
    ∃ R : Subst, (∀ p ∈ R, p.2.IsLC) ∧ (∀ k ∈ K, R.onTy (.fvar k) = .fvar k) ∧
      Subst.AgreesBelow Φ₀ S₀ (S ++ R) ∧ Subst.AgreesBelow Φ R₀ (S ++ R)

/-! ### Helper lemmas for the D2 spine (branch tier)

The branch tier's `cons` case needs an erased-world twin of the old
`customTy_factor_dodge` (ffc544f): given the branch's own MGU `S₀` (from a
*given* `InferBranches.cons` derivation), the ambient residual `R` factors
through it via a fresh `R₀` that (i) reconciles `R` and `R₀ ∘ S₀` below `Φ`
up to erasure (the `Subst.AgreesBelow Φ R (S₀ ++ R₀)` working conjunct of the
restated `InferBranches.Principal`), and (ii) sends the S₀-applied fresh block
onto the declarative `tyArgs` up to erasure — exactly the clause
`Ctx.eraseBounds_branchBindings`'s docstring mentions. The witness is the same
three-zone dodge `fresh ↦ Ws ++ R ++ Ws ↦ tyArgs` as the old unifier-dodge,
with the old structural "`R.onTy scrutTy` = customTy" link replaced by the
AgreesHM image premise `hscrutImg` (reflexive at the top-level call from
COMPLETE-MATCH). -/

/-- A declarative type agrees with its own erasure (idempotence). Used to lift
    a branch body's erased typing (`Ty.eraseBounds ρe`) back to the un-erased
    declarative result type `ρe`. -/
theorem AgreesHM.of_eraseBounds (τ : Ty) : AgreesHM τ (Ty.eraseBounds τ) := by
  rw [AgreesHM, Ty.eraseBounds_idem]

/-- Erasing the range of a `zip` commutes with mapping the pair's second
    component through `Ty.eraseBounds`. -/
theorem Subst.map_zip_erase_snd {Xs : List Nat} {Vs : List Ty} :
    (Xs.zip Vs).map (fun p => (p.1, Ty.eraseBounds p.2)) = Xs.zip (Vs.map Ty.eraseBounds) := by
  induction Xs generalizing Vs with
  | nil => rfl
  | cons x xs ih =>
    cases Vs with
    | nil => rfl
    | cons v vs => simp only [List.map_cons, List.zip_cons_cons, ih]

/-- A `nil` branch-list derivation is fully determined: the output frontier is
    the input frontier and the output substitution is empty. (Extracted as a
    lemma because `cases` on the derivation inside the branch tier's `cons`
    case clears the enclosing frontier binder from scope.) -/
theorem InferBranches.nil_det {Φ₁ : Nat} {ctx' : Ctx} {scrutTy' ρ' : Ty} {Φ₂ : Nat} {S₃ : Subst}
    (h : InferBranches Φ₁ ctx' scrutTy' ρ' [] Φ₂ S₃) : Φ₂ = Φ₁ ∧ S₃ = [] := by
  cases h with
  | nil => exact ⟨rfl, rfl⟩

/-- The named-branch `customTy` factoring dodge (given-MGU form, erased world).
    `R` factors through the branch's MGU `S₀` via an LC, `K`-fixing `R₀` whose
    composition with `S₀` agrees with `R` below `Φ` up to erasure and maps the
    S₀-applied fresh block onto `tyArgs` up to erasure. -/
theorem customTy_factor_dodge_erase {Φ : Nat} {scrutTy : Ty} {R S₀ : Subst}
    {K : List Nat} {ctor : Ctor} {tyArgs : List Ty}
    (h₀ : UnifyRel scrutTy
      (.customTy ctor.tyName ((freshVars Φ ctor.paramCount).map (Ty.fvar ·))) S₀)
    (hbscrut : Ty.BelowFvars Φ scrutTy)
    (hR : ∀ p ∈ R, p.2.IsLC)
    (hKΦ : ∀ k ∈ K, k < Φ)
    (hKfix : ∀ k ∈ K, R.onTy (.fvar k) = .fvar k)
    (hpc : ctor.paramCount = tyArgs.length)
    (htyArgs_lc : ∀ t ∈ tyArgs, t.IsLC)
    (hscrutImg : AgreesHM (.customTy ctor.tyName tyArgs) (R.onTy scrutTy)) :
    ∃ R₀ : Subst,
      (∀ p ∈ R₀, p.2.IsLC) ∧
      (∀ k ∈ K, R₀.onTy (.fvar k) = .fvar k) ∧
      (∀ v, v < Φ → AgreesHM (R.onTy (.fvar v)) (R₀.onTy (S₀.onTy (.fvar v)))) ∧
      ((freshVars Φ ctor.paramCount).map (Ty.fvar ·) |>.map S₀.onTy |>.map R₀.onTy).map
          Ty.eraseBounds = tyArgs.map Ty.eraseBounds := by
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
    show AgreesHM (U.onTy scrutTy) (U.onTy (.customTy ctor.tyName
      ((freshVars Φ ctor.paramCount).map (Ty.fvar ·))))
    rw [hRHS]
    rw [hUonTy]
    rw [hA_id hbscrut]
    unfold AgreesHM
    have hB_erase : Ty.eraseBounds (Subst.onTy ((freshVars W ctor.paramCount).zip tyArgs)
        (R.onTy scrutTy))
        = Ty.substFvars ((freshVars W ctor.paramCount).zip (tyArgs.map Ty.eraseBounds))
          (Ty.eraseBounds (R.onTy scrutTy)) := by
      rw [Subst.onTy, Ty.eraseBounds_substFvars, Subst.map_zip_erase_snd]
    rw [hB_erase]
    have hWavoid : ∀ p ∈ (freshVars W ctor.paramCount).zip (tyArgs.map Ty.eraseBounds),
        p.1 ∉ (Ty.eraseBounds (R.onTy scrutTy)).freeVars := by
      intro p hp hc
      have hp1 : p.1 ∈ freshVars W ctor.paramCount := (List.of_mem_zip hp).1
      have hge := freshVars_ge p.1 hp1
      have hc' : p.1 ∈ (R.onTy scrutTy).freeVars :=
        (Ty.mem_freeVars_eraseBounds (R.onTy scrutTy) p.1).mp hc
      rcases Subst.mem_freeVars_onTy hc' with h' | ⟨q, hq, h'⟩
      · have hlt := hbscrut.mem_lt p.1 h'
        have := hWfresh p.1 (by
          simp only [List.mem_append]
          exact Or.inr (List.mem_range.mpr hlt))
        omega
      · have := hWfresh p.1 (by
          simp only [List.mem_append]
          exact Or.inl (Or.inl (Or.inr (List.mem_flatMap.mpr ⟨q, hq, h'⟩))))
        omega
    rw [Ty.substFvars_eq_self_of_no_key hWavoid]
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
    UnifyRel.greatest_K_factors h₀ U hUlc hUni hUK
  refine ⟨R₀, hR₀lc, hR₀K, ?_, ?_⟩
  · intro v hv
    have h := hR₀fac (Ty.fvar v)
    rwa [hU_fvar v hv] at h
  · rw [List.map_map, List.map_map, List.map_map]
    apply List.ext_getElem?
    intro i
    by_cases hi : i < ctor.paramCount
    · have hx : (freshVars Φ ctor.paramCount)[i]? = some (Φ + i) := hF_i i hi
      rw [List.getElem?_map, hx]
      rw [List.getElem?_map, List.getElem?_eq_getElem (by simpa [hpc] using hi)]
      have h := hR₀fac (Ty.fvar (Φ + i))
      rw [hU_index i hi] at h
      unfold AgreesHM at h
      exact congrArg some h.symm
    · have hlen₁ : i ≥ (freshVars Φ ctor.paramCount).length := by
        rw [freshVars_length]; exact Nat.le_of_not_gt hi
      have hlen₂ : i ≥ tyArgs.length := by
        rw [← hpc]; exact Nat.le_of_not_gt hi
      rw [List.getElem?_eq_none (by simpa [List.length_map, freshVars_length] using hlen₁)]
      rw [List.getElem?_eq_none (by simpa [List.length_map] using hlen₂)]

/-! ### Recursion-group residual bridge (erase level) — `-- [letrec-agent]`

The theorems below re-instantiate the old (ffc544f / caac62d) fused `letRec`
completeness machinery at the erase level, per the 97b0bad flag ("Restate them
at the erase level when `Infer.complete_letRec` is attacked; its proof body
should largely survive").

`exists_recgroup_residual` is the purely-structural block residual (verbatim
port of the caac62d theorem of the same name; it no longer exists in the
current InferW.lean). The old fused `letRecFused_residual_setup_erase` bridge
(caac62d 14150–14370) was DELETED with the superseded `InferRecGroup.Principal`
restatement (2026-08-26): the ADOPTED statement needs no declarative
`dspecs`/`Xs`/linking package — the `R₀`-transported member typings are
premises, so the bridge's construction work moved into the SPINE-GROUP cases. -/

-- [letrec-agent]

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

/-- A member of `l.zip (r.map g)` reflects to a member of `l.zip r`: the
    `InferRecGroup` tier's `consMono`/`consPoly` tail premises must be
    reconstructed from a `rest.zip (specs.map (RecSpec.onSubst S))` member. -/
private theorem List.mem_zip_map_right {α β γ : Type _} {g : β → γ}
    : ∀ {l : List α} {r : List β} {p : α × γ},
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

/-- A scheme generalising its body-type's closed-over form generalises any scheme
    whose body is an opening of that closed form (erase world port of caac62d's
    `genGroup_generalizes`; used by the COMPLETE-LETREC body lift). -/
private theorem genGroup_generalizes_erase {Ginf : List Nat} {τ₁ : Ty} {R : Subst} {M : PolyTy}
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
private theorem genGroup_generalizes_renameG_erase {Ginf G Xsfull : List Nat} {τinf τdecl : Ty} {R : Subst}
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
  refine genGroup_generalizes_erase (Ginf := Ginf) (τ₁ := τinf) (M := PolyTy.genGroup G τdecl) (Xs := Xs)
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

/-- Erasure commutes with the `R`-transported `genGroup` scheme:
    `eraseBounds (R.onPolyTy (genGroup G τ)) = (R.map erase).onPolyTy (genGroup G (eraseBounds τ))`. -/
private theorem eraseBounds_onPolyTy_genGroup {G : List Nat} {τ : Ty} (R : Subst) :
    PolyTy.eraseBounds (Subst.onPolyTy R (PolyTy.genGroup G τ))
      = Subst.onPolyTy (R.map (fun p : Nat × Ty => (p.1, Ty.eraseBounds p.2))) (PolyTy.genGroup G (Ty.eraseBounds τ)) := by
  apply congrArg₂ PolyTy.mk
  · simp only [Subst.onPolyTy, PolyTy.genGroup, List.length_map]
    rw [Ty.genFilter_eraseBounds]
  · simp only [Subst.onPolyTy, PolyTy.eraseBounds, PolyTy.genGroup, Subst.onTy]
    rw [Ty.eraseBounds_substFvars, Ty.eraseBounds_closeOver]
    congr 1
    rw [Ty.genFilter_eraseBounds]

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

/-- `R`-erasure on an fvar is the erasure of `R.onTy (fvar v)`. -/
private theorem Subst.onTy_erase_fvar (S : Subst) (v : Nat) :
    Subst.onTy (S.map (fun p : Nat × Ty => (p.1, Ty.eraseBounds p.2))) (Ty.fvar v)
      = Ty.eraseBounds (Subst.onTy S (Ty.fvar v)) := by
  simp only [Subst.onTy]
  rw [Ty.eraseBounds_substFvars]
  simp

/-- Generalisation is reflexive. -/
private theorem PolyTy.Generalizes.refl (M : PolyTy) : M.Generalizes M := by
  intro tyArgs ty hlc hinst
  exact ⟨tyArgs, hlc, hinst⟩

/-- **Erase-level body retype** (port of caac62d's `letRecFused_body_retype`): the
    `R₁`-transported algorithmic body schemes (ceilingSchemes) generalise the
    declarative `bodyCtx` schemes, so the declarative body typing transports to
    the `R₁`-transported algorithmic body context. `hconn` is the per-position
    spec-level connection `(R₁.map erase).onTy (eraseBounds (S₁.onTy (fvar (Φ+j))))
    = renameG G Xs (eraseBounds τdecl)` (derived in COMPLETE-LETREC from the
    group tier's full-frontier R₀-side agreement + the block link); `hσfix` the
    scheme rigidity for annotated members. -/
private theorem letRecFused_body_retype_erase
    {Φ : Nat} {ctx : Ctx} {S₁ R₁ S₀ : Subst} {anns : List (Option PolyTy)}
    {bindings : List Expr} {body : Expr} {dspecs : List RecSpec} {G Xs : List Nat}
    {τ₀ : Ty} {K : List Nat}
    (hanns_eq : dspecs.map RecSpec.ann = anns.map (Option.map PolyTy.eraseBounds))
    (hdlc : ∀ τ, RecSpec.mono τ ∈ dspecs → τ.IsLC)
    (hG : G.Nodup)
    (hXlen : Xs.length = G.length) (hXnodup : Xs.Nodup)
    (hXG : ∀ g ∈ G, g ∉ Xs)
    (hXτs : ∀ x ∈ Xs, ∀ τ, RecSpec.mono τ ∈ dspecs → x ∉ τ.freeVars)
    (hXenv : ∀ x ∈ Xs, x ∉ (S₀.onCtx ctx).env.freeVars)
    (hXrigid : ∀ x ∈ Xs, x ∉ RecGroup.rigidVars anns bindings)
    (hS₁lc : ∀ p ∈ S₁, p.2.IsLC) (hR₁lc : ∀ p ∈ R₁, p.2.IsLC)
    (hctxS₁ : (R₁.onCtx (S₁.onCtx ctx)).eraseBounds = (S₀.onCtx ctx).eraseBounds)
    (hKrigid : ∀ y ∈ RecGroup.rigidVars anns bindings, y ∈ K)
    (hR₁K : ∀ k ∈ K, R₁.onTy (Ty.fvar k) = Ty.fvar k)
    (hσfix : ∀ σ, some σ ∈ anns → R₁.onPolyTy σ = σ)
    (hconn : ∀ (j : Nat) (hj : j < dspecs.length) (τdecl : Ty),
        dspecs[j]'hj = RecSpec.mono τdecl →
      Subst.onTy (R₁.map (fun p : Nat × Ty => (p.1, Ty.eraseBounds p.2)))
          (Ty.eraseBounds (S₁.onTy (Ty.fvar (Φ + j))))
        = Ty.renameG G Xs (Ty.eraseBounds τdecl))
    (hbodydecl : TypeOfHM (RecSpecs.bodyCtx (S₀.onCtx ctx).eraseBounds dspecs G).eraseBounds
        body.eraseBounds (Ty.eraseBounds τ₀)) :
    TypeOfHM (R₁.onCtx ⟨(RecSpecs.ceilingSchemes
          (genGroupVars (RecGroup.rigidVars anns bindings) (S₁.onCtx ctx).env
            (RecSpecs.monoTys ((RecSpec.init Φ anns).map (RecSpec.onSubst S₁))))
          anns ((RecSpec.init Φ anns).map (RecSpec.onSubst S₁)))
        ++ (S₁.onCtx ctx).env, (S₁.onCtx ctx).ctors⟩).eraseBounds
      body.eraseBounds (Ty.eraseBounds τ₀) := by
  set rigid := RecGroup.rigidVars anns bindings with hrigid_def
  set envS₁ := (S₁.onCtx ctx).env with henvS₁_def
  set solved := (RecSpec.init Φ anns).map (RecSpec.onSubst S₁) with hsolved_def
  set Ginf := genGroupVars rigid envS₁ (RecSpecs.monoTys solved) with hGinf_def
  set Rer : Subst := R₁.map (fun p : Nat × Ty => (p.1, Ty.eraseBounds p.2)) with hRer_def
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
    intro p hp
    rw [hRer_def] at hp
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
    exact Ty.IsLC.eraseBounds (hR₁lc q hq)
  -- pointwise generalisation of the declarative body schemes (erased level)
  set algEntries : List PolyTy := (RecSpecs.ceilingSchemes Ginf anns solved).map
    (fun M => PolyTy.eraseBounds (R₁.onPolyTy M)) with halg_def
  set declEntries : List PolyTy := dspecs.map (fun s => PolyTy.eraseBounds (RecSpec.bodyScheme G s)) with hdecl_def
  have hlen_alg : algEntries.length = dspecs.length := by
    rw [halg_def, List.length_map]
    unfold RecSpecs.ceilingSchemes
    rw [List.length_map, List.length_zip, hsolved_len]
    have h1 : dspecs.length = anns.length := by
      have h := congrArg List.length hanns_eq
      rw [List.length_map, List.length_map] at h
      exact h
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
          rw [List.length_map, List.length_map] at h
          exact h
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
        have hci : Rer.onTy (Ty.eraseBounds (S₁.onTy (Ty.fvar (Φ + i))))
            = Ty.renameG G Xs (Ty.eraseBounds τdecl) := by
          simpa [hRer_def] using (hconn i hdi τdecl hd)
        have hXinf : ∀ x ∈ Xs, x ∉ (Rer.onPolyTy (PolyTy.genGroup Ginf
            (Ty.eraseBounds (S₁.onTy (Ty.fvar (Φ + i)))))).body.freeVars := by
          intro x hx hmem
          change x ∈ (Rer.onTy (Ty.closeOver (Ty.genFilter Ginf
            (Ty.eraseBounds (S₁.onTy (Ty.fvar (Φ + i))))) (Ty.eraseBounds (S₁.onTy (Ty.fvar (Φ + i)))))).freeVars at hmem
          obtain ⟨v, hv, hxv⟩ := Ty.mem_freeVars_onTy_iff.mp hmem
          have hvτ : v ∈ (Ty.eraseBounds (S₁.onTy (Ty.fvar (Φ + i)))).freeVars :=
            Ty.freeVars_closeOver_subset hv
          have hvτ' : v ∈ (S₁.onTy (Ty.fvar (Φ + i))).freeVars :=
            (Ty.mem_freeVars_eraseBounds (S₁.onTy (Ty.fvar (Φ + i))) v).mp hvτ
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
              have heq : Rer.onTy (Ty.fvar v) = Ty.eraseBounds (R₁.onTy (Ty.fvar v)) := by
                rw [hRer_def]
                exact Subst.onTy_erase_fvar R₁ v
              rw [heq] at hxv
              exact (Ty.mem_freeVars_eraseBounds (R₁.onTy (Ty.fvar v)) x).mp hxv
            have hx_onTy : x ∈ (R₁.onTy pt.body).freeVars :=
              Ty.mem_freeVars_onTy_iff.mpr ⟨v, hvpt, hxv'⟩
            have hm2 : R₁.onPolyTy pt ∈ (R₁.onCtx (S₁.onCtx ctx)).env := by
              simp only [Subst.onCtx, Subst.onEnv]; exact List.mem_map.mpr ⟨pt, hpt, rfl⟩
            have hx1 : x ∈ (R₁.onCtx (S₁.onCtx ctx)).env.freeVars :=
              Env.mem_freeVars_iff.mpr ⟨R₁.onPolyTy pt, hm2, hx_onTy⟩
            have hx1E : x ∈ ((R₁.onCtx (S₁.onCtx ctx)).eraseBounds).env.freeVars :=
              (Env.mem_freeVars_eraseBounds ((R₁.onCtx (S₁.onCtx ctx)).env) x).mpr hx1
            have hc := congrArg Ctx.env hctxS₁
            have hx2E : x ∈ ((S₀.onCtx ctx).eraseBounds).env.freeVars := by
              rwa [← hc]
            have hx_S₀ : x ∈ (S₀.onCtx ctx).env.freeVars :=
              (Env.mem_freeVars_eraseBounds ((S₀.onCtx ctx).env) x).mp hx2E
            exact hXenv x hx hx_S₀
          · have hfix : R₁.onTy (Ty.fvar v) = Ty.fvar v := hR₁K v (hKrigid v hrig)
            have hxv' : x ∈ (R₁.onTy (Ty.fvar v)).freeVars := by
              have heq : Rer.onTy (Ty.fvar v) = Ty.eraseBounds (R₁.onTy (Ty.fvar v)) := by
                rw [hRer_def]
                exact Subst.onTy_erase_fvar R₁ v
              rw [heq] at hxv
              exact (Ty.mem_freeVars_eraseBounds (R₁.onTy (Ty.fvar v)) x).mp hxv
            rw [hfix] at hxv'
            simp only [Ty.freeVars, List.mem_singleton] at hxv'
            exact hXrigid x hx (by rw [hxv']; exact hrig)
        have hgen := genGroup_generalizes_renameG_erase (Ginf := Ginf)
          (G := G) (Xsfull := Xs)
          (τinf := Ty.eraseBounds (S₁.onTy (Ty.fvar (Φ + i)))) (τdecl := Ty.eraseBounds τdecl)
          (R := Rer)
          (Ty.IsLC.eraseBounds hτinf_lc) (Ty.IsLC.eraseBounds (hdlc τdecl hτdecl_mem)) hRerlc
          hG hXlen hXnodup hXG
          (fun x hx hc => hXτs x hx τdecl hτdecl_mem ((Ty.mem_freeVars_eraseBounds τdecl x).mp hc))
          hci hXinf
        have hgen' : (PolyTy.eraseBounds (R₁.onPolyTy (RecSpec.bodyScheme Ginf
                (RecSpec.mono (S₁.onTy (Ty.fvar (Φ + i))))))).Generalizes
            (PolyTy.eraseBounds (RecSpec.bodyScheme G (RecSpec.mono τdecl))) := by
          change (PolyTy.eraseBounds (R₁.onPolyTy (PolyTy.genGroup Ginf (S₁.onTy (Ty.fvar (Φ + i)))))).Generalizes
            (PolyTy.eraseBounds (PolyTy.genGroup G τdecl))
          rw [eraseBounds_onPolyTy_genGroup, PolyTy.eraseBounds_genGroup]
          simpa [Rer] using hgen
        simpa [hcs, hann_i, hsolved_i] using hgen'
      | poly σd =>
        -- rigid poly member: the ORIGINAL scheme `σ0` (anns[i] = some σ0 with
        -- eraseBounds σ0 = σd) is FIXED by `R₁`; both entries collapse to σd.
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
          have hσE : σd = PolyTy.eraseBounds σ0 := by
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
          have hrefl : (PolyTy.eraseBounds (R₁.onPolyTy σ0)).Generalizes
              (PolyTy.eraseBounds (RecSpec.bodyScheme G (RecSpec.poly σd))) := by
            rw [hσ0fix, hσE]
            simp [RecSpec.bodyScheme]
            exact PolyTy.Generalizes.refl _
          simpa [hcs, hann] using hrefl
  -- the outer env transport and the full Forall₂
  have houter_eq : (envS₁.map R₁.onPolyTy).map PolyTy.eraseBounds
      = (S₀.onCtx ctx).eraseBounds.env := by
    have hc := congrArg Ctx.env hctxS₁
    rw [henvS₁_def]
    simpa [Subst.onCtx, Subst.onEnv, Env.eraseBounds] using hc
  have hbodydecl' : TypeOfHM ⟨declEntries ++ (envS₁.map R₁.onPolyTy).map PolyTy.eraseBounds,
        (S₀.onCtx ctx).eraseBounds.ctors⟩ body.eraseBounds (Ty.eraseBounds τ₀) := by
    have hctxbody : (RecSpecs.bodyCtx (S₀.onCtx ctx).eraseBounds dspecs G).eraseBounds
        = ⟨declEntries ++ (envS₁.map R₁.onPolyTy).map PolyTy.eraseBounds,
            (S₀.onCtx ctx).eraseBounds.ctors⟩ := by
      apply congrArg₂ Ctx.mk
      · unfold RecSpecs.bodyCtx
        rw [Env.eraseBounds, List.map_append, List.map_map]
        rw [hdecl_def]
        congr 1
        · change Env.eraseBounds (Env.eraseBounds (List.map S₀.onPolyTy ctx.env)) =
            (envS₁.map R₁.onPolyTy).map PolyTy.eraseBounds
          rw [Env.eraseBounds_idem]
          exact houter_eq.symm
      · simp [RecSpecs.bodyCtx, Ctx.eraseBounds, CtorEnv.eraseBounds_idem]
    simpa [hctxbody] using hbodydecl
  have hfinal := TypeOfHM.weaken_schemes hforall hbodydecl'
  have hctx : (R₁.onCtx ⟨RecSpecs.ceilingSchemes Ginf anns solved ++ envS₁, (S₁.onCtx ctx).ctors⟩).eraseBounds
      = ⟨algEntries ++ (envS₁.map R₁.onPolyTy).map PolyTy.eraseBounds,
          (S₀.onCtx ctx).eraseBounds.ctors⟩ := by
    simp only [Ctx.eraseBounds, Subst.onCtx, Subst.onEnv, Env.eraseBounds, List.map_append,
      CtorEnv.eraseBounds_idem]
    congr 1
    rw [halg_def]
    congr 1
    rw [List.map_map]
    rfl
  simpa [← hrigid_def, ← hGinf_def, ← hsolved_def, ← henvS₁_def, hctx, List.map_map] using hfinal

/-- From the cofinite "types at every fresh opening of `σ`" premise, extract a
    typing at one *specific* opening `Ys` (any list of the right length): pick a
    generic fresh `Xs`, type at `σ.openVars Xs`, then rename `Xs → Ys`. (Erase
    world port of caac62d's `typeOfHM_at_block`; the `consPoly` group tier
    instantiates the poly member premise at the algorithmic skolems.) -/
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
          -- [match-agent]
          simp only [Expr.eraseBounds] at hty
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
              have hhd : (hd.1, hd.2.eraseBounds) ∈ branches.map (fun pb => (pb.1, pb.2.eraseBounds)) := by
                rw [hcons]
                exact List.mem_map.mpr ⟨hd, List.mem_cons_self, rfl⟩
              exact TypeOfMatchBranch.regular (hbrD (hd.1, hd.2.eraseBounds) hhd)
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
              fun v hv => by rw [hUeqR₁ v hv]; exact AgreesHM.refl _
            -- STEP 3: recast the branch premises (context rewrite only; types unchanged).
            have hctxeq : (U.onCtx (S₁.onCtx ctx)).eraseBounds = (S₀.onCtx ctx).eraseBounds := by
              have h1 : (U.onCtx (S₁.onCtx ctx)).eraseBounds = (R₁.onCtx (S₁.onCtx ctx)).eraseBounds := by
                exact Subst.onCtx_congr_hm hUagreeR₁ hbelow₁'
              have h2 : (R₁.onCtx (S₁.onCtx ctx)).eraseBounds = (S₀.onCtx ctx).eraseBounds := by
                rw [← Subst.onCtx_append]
                exact (Subst.onCtx_congr_hm hAgree₁ hbelow).symm
              exact h1.trans h2
            have hbr' : ∀ b ∈ branches, TypeOfMatchBranch (U.onCtx (S₁.onCtx ctx)).eraseBounds
                (b.1, b.2.eraseBounds) scruT₀ τe := by
              intro b hb
              have hb' : (b.1, b.2.eraseBounds) ∈ branches.map (fun pb => (pb.1, pb.2.eraseBounds)) :=
                List.mem_map.mpr ⟨b, hb, rfl⟩
              rw [hctxeq]
              exact hbrD (b.1, b.2.eraseBounds) hb'
            -- the two image premises (reflexive at this call).
            have hIMGτe : AgreesHM τe (U.onTy (.fvar Φ₁)) := by
              rw [hUΦ₁]
              exact AgreesHM.refl _
            have hIMGscru : AgreesHM scruT₀ (U.onTy τs) :=
              AgreesHM.trans hty₁ (Subst.onTy_congr_hm hUagreeR₁ hτs_bel |>.symm)
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
              exact AgreesHM.trans (hUagreeR₁ v hv).symm (hAgree₂ v (by omega))
            have hAgree : Subst.AgreesBelow Φ S₀ ((S₁ ++ S₂) ++ R₂) :=
              @Subst.AgreesBelow.trans_append Φ Φ₁ S₀ S₁ R₁ S₂ R₂ hfle hAgree₁ hS₁_bel hAgree₂'
            refine ⟨R₂, hR₂, hty₂, hR₂K, ?_⟩
            · simpa [List.append_assoc] using hAgree
      | @letRec Φ ctx anns bindings body Φ₁ Φ₂ S₁ S₂ τ₂ hannswf hgroup hceiling hbody =>
        exact fun hwf hbelow S₀ τe K hS₀ hKΦ hKe hKfix hty => by
          -- COMPLETE-LETREC (all-mono cut; R₀ via the block residual, body via the
          -- erase-level retype of `letRecFused_body_retype`).
          rw [Expr.eraseBounds] at hty
          cases hty with
          | letRec hwfD hlenD hlinkD hlcD hmonoD hbodyCtxD hbodyD =>
            rename_i dspecs τsD G L
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
            obtain ⟨Xs, hXlen, hXnodup, hXavoid⟩ := exists_fresh_names
              (L ++ G ++ dspecs.flatMap RecSpec.monoFreeVars ++ (S₀.onCtx ctx).env.freeVars ++ K) G.length
            have hXL : ∀ x ∈ Xs, x ∉ L := fun x hx hc => hXavoid x hx (by simp only [List.mem_append]; tauto)
            have hXG : ∀ g ∈ G, g ∉ Xs := fun g hg hc => hXavoid g hc (by simp only [List.mem_append]; tauto)
            have hXτs : ∀ x ∈ Xs, ∀ τ, RecSpec.mono τ ∈ dspecs → x ∉ τ.freeVars := fun x hx τ hτ hc =>
              hXavoid x hx (by
                simp only [List.mem_append]
                exact Or.inl (Or.inl (Or.inr (List.mem_flatMap.mpr ⟨RecSpec.mono τ, hτ, hc⟩))))
            have hXenv : ∀ x ∈ Xs, x ∉ (S₀.onCtx ctx).env.freeVars := fun x hx hc =>
              hXavoid x hx (by simp only [List.mem_append]; tauto)
            have hXK : ∀ x ∈ Xs, x ∉ K := fun x hx hc => hXavoid x hx (by simp only [List.mem_append]; tauto)
            have hXfresh : FreshNames L G.length Xs := ⟨hXlen, hXnodup, hXL⟩
            have hXrigid : ∀ x ∈ Xs, x ∉ RecGroup.rigidVars anns bindings := fun x hx hc =>
              hXK x hx (hKrigid x hc)
            -- the residual targets: the opened witnesses
            set vs : List Ty := τsD.map (fun τ => Ty.renameG G Xs τ) with hvs_def
            have hvs_len : vs.length = bindings.length := by
              rw [hvs_def, List.length_map]
              exact hlen_τsD.symm
            have hvs_lc : ∀ t ∈ vs, t.IsLC := by
              intro t ht
              rw [hvs_def] at ht
              obtain ⟨τ, hτ, rfl⟩ := List.mem_map.mp ht
              change (Ty.renameG G Xs τ).IsLC
              change (Subst.onTy (G.zip (Xs.map (Ty.fvar ·))) τ).IsLC
              exact Subst.onTy_lc (fun p hp => by
                obtain ⟨w, _, hw⟩ := List.mem_map.mp (List.of_mem_zip hp).2
                rw [← hw]; exact ContainsBvarsUpTo.fvar) (hlcD τ hτ)
            obtain ⟨R₀, hR₀lc, hR₀K, hR₀ag, hR₀block⟩ :=
              exists_recgroup_residual (Φ := Φ) (n := bindings.length) (S₀ := S₀) (vs := vs) (K := K)
                hvs_len hS₀ hvs_lc hKΦ hKfix
            -- the block realisation, positionally: R₀.onTy (fvar (Φ+j)) = renameG G Xs (τsD[j])
            have hR₀blockj : ∀ j (hj : j < bindings.length),
                R₀.onTy (Ty.fvar (Φ + j)) = Ty.renameG G Xs (τsD[j]'(by rw [← hlen_τsD]; exact hj)) := by
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
            have hAgree : ∀ v, v < Φ → AgreesHM (R₀.onTy (.fvar v)) (S₀.onTy (.fvar v)) := fun v hv =>
              congrArg Ty.eraseBounds (hR₀ag v hv)
            -- the mono premise (per-member, at the R₀-transported group context)
            have hMonoMem : ∀ p ∈ bindings.zip (RecSpec.init Φ anns), ∀ τm,
                p.2 = RecSpec.mono τm →
                TypeOfHM (R₀.onCtx groupCtx).eraseBounds (Expr.eraseBounds p.1)
                  (Ty.eraseBounds (R₀.onTy τm)) := by
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
              have hjBE : j < (bindings.map Expr.eraseBounds).length := by
                simp [List.length_map]
                exact hjl1
              let bE : Expr := (bindings.map Expr.eraseBounds)[j]'(hjBE)
              let tD : Ty := τsD[j]'(hjT)
              have hmemD : (bE, tD) ∈ (bindings.map Expr.eraseBounds).zip τsD := by
                exact getElem_mem_zip j hjBE hjT
              have hdecl0 := hmonoD Xs hXfresh (bE, tD) hmemD
              have hdeclE := TypeOfHM.eraseBounds_of hdecl0
              have hctxE : (RecSpecs.rhsCtx (S₀.onCtx ctx).eraseBounds (τsD.map RecSpec.mono) G Xs).eraseBounds
                  = (R₀.onCtx groupCtx).eraseBounds := by
                simp only [RecSpecs.rhsCtx, groupCtx, Subst.onCtx, Subst.onEnv, Ctx.eraseBounds, Env.eraseBounds, List.map_append]
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
                    have hblk : R₀.onTy (Ty.fvar (Φ + k)) = Ty.renameG G Xs (τsD[k]'hk2_len) := hR₀blockj k hkB
                    have hblkE : PolyTy.mkTrivial (Ty.renameG G Xs (τsD[k]'hk2_len)).eraseBounds = PolyTy.mkTrivial (R₀.onTy (Ty.fvar (Φ + k))).eraseBounds := by
                      simp only [Ty.eraseBounds_renameG, hblk]
                    simp only [List.getElem_map, Function.comp_apply, RecSpec.rhsEntry, hinit_k, Subst.onPolyTy, PolyTy.eraseBounds_mkTrivial, Ty.renameG_nil_pool, PolyTy.eraseBounds, PolyTy.mkTrivial]
                    exact hblkE
                  · refine List.ext_getElem (by simp) (fun k hk1 hk2 => ?_)
                    have hklen : k < ctx.env.length := by simpa using hk2
                    have hMem : ctx.env[k]'hklen ∈ ctx.env := List.getElem_mem hklen
                    have hM' : (ctx.env[k]'hklen) ∈ ctx.env := hMem
                    simp only [List.getElem_map, Function.comp_apply,
                      PolyTy.eraseBounds_mkTrivial, PolyTy.eraseBounds, Subst.onPolyTy]
                    have hrec : (PolyTy.mk (ctx.env[k]'hklen |>.paramCount)
                            (Ty.eraseBounds (Ty.eraseBounds (S₀.onTy (ctx.env[k]'hklen).body))))
                        = (PolyTy.mk (ctx.env[k]'hklen |>.paramCount)
                            (Ty.eraseBounds (R₀.onTy (ctx.env[k]'hklen).body))) := by
                      refine congrArg₂ PolyTy.mk rfl ?_
                      rw [Ty.eraseBounds_idem]
                      exact Subst.onTy_congr_hm
                        (fun v hv => AgreesHM.symm (hAgree v hv))
                        (hbelow _ hM')
                    exact hrec
                · simp [Subst.onCtx, CtorEnv.eraseBounds_idem]
              have htyE : Ty.eraseBounds (Ty.renameG G Xs (τsD[j]'hjT))
                  = Ty.eraseBounds (R₀.onTy (Ty.fvar (Φ + j))) := by
                exact congrArg (fun T => Ty.eraseBounds T) (hR₀blockj j hjl1).symm
              rw [hctxE] at hdeclE
              rw [htyE] at hdeclE
              have hp1 : p.1 = bindings[j]'hjl1 := by
                exact (congrArg Prod.fst hpeq').symm
              have hbE : bE = (bindings[j]'hjl1).eraseBounds := by
                simp [bE, List.getElem_map]
              rw [hbE, ← hp1] at hdeclE
              simpa [Expr.eraseBounds_idem] using hdeclE
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
            have hbodyE : TypeOfHM (RecSpecs.bodyCtx (S₀.onCtx ctx).eraseBounds dspecs G).eraseBounds
                body.eraseBounds (Ty.eraseBounds τe) := by
              simpa [Expr.eraseBounds_idem] using (TypeOfHM.eraseBounds_of hbodyD)
            have hdlc : ∀ τ, RecSpec.mono τ ∈ dspecs → τ.IsLC := by
              intro τ hτ
              exact hwfD.mono_lc τ hτ
            have hanns_eq : dspecs.map RecSpec.ann = anns.map (Option.map PolyTy.eraseBounds) := by
              simpa [hwfD.anns_eq]
            have hctxS₁ : (R_g.onCtx (S₁.onCtx ctx)).eraseBounds = (S₀.onCtx ctx).eraseBounds := by
              rw [← Subst.onCtx_append]
              exact (Subst.onCtx_congr_hm hAgreeTier hbelow).symm
            have hσfix : ∀ σ, some σ ∈ anns → R_g.onPolyTy σ = σ := by
              intro σ hσ
              simp only [Subst.onPolyTy]
              rw [Subst.onTy_eq_self_of_fixes (fun v hv => hR_gK v (hKe v (List.mem_append.mpr (Or.inl
                (List.mem_append.mpr (Or.inl (Expr.scheme_body_mem_annList_tyFreeVars hσ hv)))))))]
            have hconnB : ∀ (j : Nat) (hj : j < dspecs.length) (τdecl : Ty),
                dspecs[j]'hj = RecSpec.mono τdecl →
              Subst.onTy (R_g.map (fun p : Nat × Ty => (p.1, Ty.eraseBounds p.2)))
                  (Ty.eraseBounds (S₁.onTy (Ty.fvar (Φ + j))))
                = Ty.renameG G Xs (Ty.eraseBounds τdecl) := by
              intro j hj τdecl hτdecl
              have hjl : j < bindings.length := by
                rw [← hdspec_len]
                exact hj
              have hjT : j < τsD.length := by rw [← hlen_τsD]; exact hjl
              have hblockAgree : AgreesHM (R₀.onTy (Ty.fvar (Φ + j)))
                  (R_g.onTy (S₁.onTy (Ty.fvar (Φ + j)))) := by
                rw [← Subst.onTy_append]
                exact hAgreeTierR (Φ + j) (by have := hjl; omega)
              have hblk := hR₀blockj j hjl
              have hlinkτ : τdecl = τsD[j]'hjT := by
                have hmemD : (RecSpec.mono τdecl, τsD[j]'hjT) ∈ dspecs.zip τsD := by
                  simpa [hτdecl] using (getElem_mem_zip j hj hjT)
                exact (hlinkD (RecSpec.mono τdecl, τsD[j]'hjT) hmemD τdecl rfl).symm
              have h3 : Subst.onTy (R_g.map (fun p : Nat × Ty => (p.1, Ty.eraseBounds p.2)))
                  (Ty.eraseBounds (S₁.onTy (Ty.fvar (Φ + j))))
                  = Ty.eraseBounds (R_g.onTy (S₁.onTy (Ty.fvar (Φ + j)))) := by
                simp only [Subst.onTy, Ty.eraseBounds_substFvars]
              rw [h3]
              have hstep1 : Ty.eraseBounds (R_g.onTy (S₁.onTy (Ty.fvar (Φ + j))))
                  = Ty.eraseBounds (R₀.onTy (Ty.fvar (Φ + j))) := hblockAgree.symm
              have hstep2 : Ty.eraseBounds (R₀.onTy (Ty.fvar (Φ + j)))
                  = Ty.renameG G Xs (Ty.eraseBounds (τsD[j]'hjT)) := by
                rw [hblk, Ty.eraseBounds_renameG]
              rw [hstep1, hstep2, ← hlinkτ]
            have hbodyAlg : TypeOfHM
                (R_g.onCtx ⟨(RecSpecs.ceilingSchemes
                    (genGroupVars (RecGroup.rigidVars anns bindings) (S₁.onCtx ctx).env
                      (RecSpecs.monoTys ((RecSpec.init Φ anns).map (RecSpec.onSubst S₁))))
                    anns ((RecSpec.init Φ anns).map (RecSpec.onSubst S₁)))
                  ++ (S₁.onCtx ctx).env, (S₁.onCtx ctx).ctors⟩).eraseBounds
                body.eraseBounds (Ty.eraseBounds τe) :=
              letRecFused_body_retype_erase (Φ := Φ) (ctx := ctx) (S₁ := S₁) (R₁ := R_g) (S₀ := S₀)
                (anns := anns) (bindings := bindings) (body := body) (dspecs := dspecs)
                (G := G) (Xs := Xs) (τ₀ := τe) (K := K)
                hanns_eq hdlc hwfD.nodup hXlen hXnodup hXG hXτs hXenv hXrigid
                (InferRecGroup.lc hgroup hctxgWF hinitLC) hR_g hctxS₁ hKrigid hR_gK hσfix hconnB hbodyE
            -- recurse on the body at the algorithmic body context
            have hS₁lc : ∀ p ∈ S₁, p.2.IsLC := InferRecGroup.lc hgroup hctxgWF hinitLC
            have htfv_below : ∀ y ∈ Expr.tyFreeVars.RecGroup.tyFreeVars bindings,
                y < Φ + bindings.length := fun y hy =>
              Nat.lt_add_right bindings.length (hKΦ y (hKgrp y hy))
            have hinit_bel : ∀ s ∈ RecSpec.init Φ anns, RecSpec.BelowFvars (Φ + bindings.length) s := by
              intro s hs
              rcases RecSpec.mem_init hs with ⟨m, hm1, hm2, hs'⟩ | ⟨σ, hσ, hs'⟩
              · subst hs'; exact hinitB _ hs _ rfl
              · subst hs'; exact Ty.BelowFvars.of_freeVars_lt (fun y hy => Nat.lt_add_right bindings.length (hKΦ y (hKe y (List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl (Expr.scheme_body_mem_annList_tyFreeVars hσ hy))))))))
            have hS₁_bel : ∀ p ∈ S₁, Ty.BelowFvars Φ₁ p.2 :=
              InferRecGroup.belowFvars hgroup hctxgBelow hinit_bel htfv_below
            have hgle : Φ + bindings.length ≤ Φ₁ := InferRecGroup.frontier_le hgroup
            have hKΦ₁ : ∀ k ∈ K, k < Φ₁ := fun k hk =>
              lt_of_lt_of_le (hKΦ k hk) (le_trans (Nat.le_add_right Φ bindings.length) hgle)
            have hσbody_bel : ∀ σ, some σ ∈ anns → Ty.BelowFvars Φ₁ σ.body := fun σ hσ =>
              Ty.BelowFvars.of_freeVars_lt (fun y hy =>
                have hK := hKe y (List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl
                  (Expr.scheme_body_mem_annList_tyFreeVars hσ hy)))))
                hKΦ₁ y hK)
            have hmono_bel : ∀ τm, RecSpec.mono τm ∈ (RecSpec.init Φ anns).map (RecSpec.onSubst S₁) →
                Ty.BelowFvars Φ₁ τm := by
              intro τm hτm
              obtain ⟨s, hs, hseq⟩ := List.mem_map.mp hτm
              rcases RecSpec.mem_init hs with ⟨m, hm1, hm2, rfl⟩ | ⟨σ, hσ, rfl⟩
              · cases hseq
                exact Subst.onTy_belowFvars hS₁_bel (.fvar (by omega))
              · exact absurd hseq (by simp [RecSpec.onSubst])
            have hinit_not_poly : ∀ {Φ} {anns : List (Option PolyTy)} {s : RecSpec},
                s ∈ RecSpec.init Φ anns → ∀ σ, s ≠ RecSpec.poly σ := by
              intro Φ anns
              induction anns generalizing Φ with
              | nil => intro s hs; simp [RecSpec.init] at hs
              | cons a as ih =>
                intro s hs σ
                simp only [RecSpec.init, List.mem_cons] at hs
                rcases hs with rfl | hs
                · intro h; cases h
                · exact ih hs σ
            have hmono_nopoly : ∀ s ∈ (RecSpec.init Φ anns).map (RecSpec.onSubst S₁),
                ¬ ∃ σ, s = RecSpec.poly σ := by
              intro s hs ⟨σ, hσ⟩
              obtain ⟨s₀, hs₀, rfl⟩ := List.mem_map.mp hs
              cases s₀ with
              | mono τ =>
                simp [RecSpec.onSubst] at hσ
              | poly σ₀ =>
                exact hinit_not_poly hs₀ σ₀ rfl
            have hwfB : CtxWF ⟨(RecSpecs.ceilingSchemes
                  (genGroupVars (RecGroup.rigidVars anns bindings) (S₁.onCtx ctx).env
                    (RecSpecs.monoTys ((RecSpec.init Φ anns).map (RecSpec.onSubst S₁))))
                  anns ((RecSpec.init Φ anns).map (RecSpec.onSubst S₁)))
                ++ (S₁.onCtx ctx).env, (S₁.onCtx ctx).ctors⟩ := by
              intro M hM
              rcases List.mem_append.mp hM with hM | hM
              · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hM
                cases p with
                | mk a s =>
                  cases a with
                  | some σ =>
                    exact hannswf σ (List.of_mem_zip hp).1
                  | none =>
                    cases hs : s with
                    | mono τm =>
                      have hτm_lc : τm.IsLC := by
                        have hmem := (List.of_mem_zip hp).2
                        rw [hs] at hmem
                        obtain ⟨s₀, hs₀, hs_eq⟩ := List.mem_map.mp hmem
                        rcases RecSpec.mem_init hs₀ with ⟨m', _, _, rfl⟩ | ⟨σ', _, rfl⟩
                        · simp [RecSpec.onSubst] at hs_eq
                          cases hs; cases hs_eq
                          exact Subst.onTy_lc hS₁lc ContainsBvarsUpTo.fvar
                        · simp [RecSpec.onSubst] at hs_eq
                      exact PolyTy.genGroup_wf hτm_lc
                    | poly σ => exact False.elim ((hmono_nopoly s (List.of_mem_zip hp).2) ⟨σ, hs⟩)
              · exact Subst.onCtx_wf hS₁lc hwf M hM
            have hbelowB : CtxBelow Φ₁ ⟨(RecSpecs.ceilingSchemes
                  (genGroupVars (RecGroup.rigidVars anns bindings) (S₁.onCtx ctx).env
                    (RecSpecs.monoTys ((RecSpec.init Φ anns).map (RecSpec.onSubst S₁))))
                  anns ((RecSpec.init Φ anns).map (RecSpec.onSubst S₁)))
                ++ (S₁.onCtx ctx).env, (S₁.onCtx ctx).ctors⟩ := by
              intro M hM
              rcases List.mem_append.mp hM with hM | hM
              · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hM
                cases p with
                | mk a s =>
                  cases a with
                  | some σ =>
                    exact hσbody_bel σ (List.of_mem_zip hp).1
                  | none =>
                    cases hs : s with
                    | mono τm =>
                      refine Ty.BelowFvars.of_freeVars_lt (fun v hv => ?_)
                      have hmem := (List.of_mem_zip hp).2
                      rw [hs] at hmem
                      have hτ := hmono_bel τm hmem
                      have hvτ : v ∈ τm.freeVars :=
                        Ty.freeVars_closeOver_subset (by simpa [RecSpec.bodyScheme, PolyTy.genGroup] using hv)
                      exact hτ.mem_lt v hvτ
                    | poly σ => exact False.elim ((hmono_nopoly s (List.of_mem_zip hp).2) ⟨σ, hs⟩)
              · exact (Subst.onCtx_below hS₁_bel (le_trans (by omega) hgle) hbelow) M hM
            obtain ⟨R_b, hR_b, hty_b, hR_bK, hAgreeB⟩ :=
              ih.1 hbody hsize_body hwfB hbelowB hwfB hbelowB R_g (Ty.eraseBounds τe) K
                hR_g hKΦ₁ hKbody hR_gK hbodyAlg
            -- assemble (trans_append)
            have hAgree : Subst.AgreesBelow Φ S₀ ((S₁ ++ S₂) ++ R_b) :=
              Subst.AgreesBelow.trans_append (by omega) hAgreeTier hS₁_bel hAgreeB
            refine ⟨R_b, hR_b, ?_, hR_bK, ?_⟩
            · show Ty.eraseBounds τe = Ty.eraseBounds (R_b.onTy τ)
              rw [← Ty.eraseBounds_idem]
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
            -- `hspec : BranchCtorSpec (S₀amb.onCtx ctx).eraseBounds.ctors c' n' scruT₀ ctorE tyArgsE instContentsE`
            have hctorE : ctorE = Ctor.eraseBounds ctor := by
              have hl : LookupList.get? (S₀amb.onCtx ctx).eraseBounds.ctors c = some (Ctor.eraseBounds ctor) := by
                have hlook' := congrArg (Option.map Ctor.eraseBounds) hlook
                simpa [Ctx.eraseBounds, Subst.onCtx, CtorEnv.eraseBounds_get?] using hlook'
              exact Option.some.inj (hspec.lookup.symm.trans hl)
            have htyArgs_lc : ∀ t ∈ tyArgsE, t.IsLC := by
              have hlc : (Ty.customTy ctor.tyName tyArgsE).IsLC := by
                simpa [hctorE, hspec.scrut_eq] using hscruLC
              cases hlc with | customTy h => exact h
            have hpc' : ctor.paramCount = tyArgsE.length := by
              simpa [hctorE] using hspec.arity
            have hscrutImg' : AgreesHM (.customTy ctor.tyName tyArgsE) (S₀amb.onTy scrutTy) := by
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
              customTy_factor_dodge_erase (R := S₀amb) (S₀ := S₀) (ctor := ctor) (tyArgs := tyArgsE)
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
            have hctx0 : (R₀.onCtx (S₀.onCtx ctx)).eraseBounds = (S₀amb.onCtx ctx).eraseBounds := by
              rw [← Subst.onCtx_append]
              exact (Subst.onCtx_congr_hm hAgreeBelow₀ hbelow).symm
            have hinstsE_erase :
                instContentsE.map Ty.eraseBounds =
                  (Ctor.eraseBounds ctor).contents.map (fun c => Ty.openWith (tyArgsE.map Ty.eraseBounds) c) := by
              rw [hinstsE, hctorE]
              rw [List.map_map]
              apply List.map_congr_left
              intro c hc
              rw [Function.comp_apply, Ty.eraseBounds_openWith]
              congr 1
              obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hc
              exact Ty.eraseBounds_idem t
            have hbodyCtxEq : (R₀.onCtx bodyCtxAlg).eraseBounds = bodyCtx.eraseBounds := by
              calc
                (R₀.onCtx bodyCtxAlg).eraseBounds
                    = { (R₀.onCtx (S₀.onCtx ctx)).eraseBounds with
                        env := ((Ctor.eraseBounds ctor).contents.map
                          (fun c => Ty.openWith (tyArgsE.map Ty.eraseBounds) c)).map PolyTy.mkTrivial
                            ++ (R₀.onCtx (S₀.onCtx ctx)).eraseBounds.env } := by
                  rw [Subst.onCtx_branchBindings hR₀]
                  rw [Ctx.eraseBounds_branchBindings ctor
                    ((freshVars Φ ctor.paramCount).map (Ty.fvar ·) |>.map S₀.onTy |>.map R₀.onTy)
                    (R₀.onCtx (S₀.onCtx ctx))]
                  rw [hmap₀]
                _ = { (S₀amb.onCtx ctx).eraseBounds with
                        env := ((Ctor.eraseBounds ctor).contents.map
                          (fun c => Ty.openWith (tyArgsE.map Ty.eraseBounds) c)).map PolyTy.mkTrivial
                            ++ (S₀amb.onCtx ctx).eraseBounds.env } := by
                  rw [hctx0]
                _ = bodyCtx.eraseBounds := by
                  rw [hctxdef]
                  simp [Ctx.eraseBounds, Env.eraseBounds_append, Env.eraseBounds_map_mkTrivial,
                    hinstsE_erase, Env.eraseBounds_idem, CtorEnv.eraseBounds_idem]
            have hbE : TypeOfHM bodyCtx.eraseBounds body.eraseBounds (Ty.eraseBounds ρe) := by
              simpa [Expr.eraseBounds_idem] using (TypeOfHM.eraseBounds_of hbodyty)
            have hbE' : TypeOfHM (R₀.onCtx bodyCtxAlg).eraseBounds body.eraseBounds (Ty.eraseBounds ρe) := by
              rwa [← hbodyCtxEq] at hbE
            have hKΦ₀ : ∀ k ∈ K, k < Φ + ctor.paramCount := fun k hk => lt_of_lt_of_le (hKΦ k hk) hfle₀
            -- STEP 4: recurse on the branch body (its declarative type is ρe, erased).
            obtain ⟨R_b, hR_b, htyb, hR_bK, hagb⟩ :=
              ih.1 hinfbody hsize_b hwf_body hbelow_body hwf_body hbelow_body R₀ (Ty.eraseBounds ρe) K
                hR₀ hKΦ₀ hKbody hR₀K hbE'
            have hle_b : Φ + ctor.paramCount ≤ Φ₁ := Infer.frontier_le hinfbody
            have hKΦ₁ : ∀ k ∈ K, k < Φ₁ := fun k hk => lt_of_lt_of_le (hKΦ₀ k hk) hle_b
            have hbodyLC := Infer.lc hinfbody hwf_body
            have hτb_lc : τb.IsLC := hbodyLC.1
            have hS₁lc : ∀ p ∈ S₁, p.2.IsLC := hbodyLC.2
            have hbb := Infer.belowFvars hinfbody hbelow_body (fun y hy => hKΦ₀ y (hKbody y hy))
            have hτb_bel : Ty.BelowFvars Φ₁ τb := hbb.1
            have hS₁_bel : ∀ p ∈ S₁, Ty.BelowFvars Φ₁ p.2 := hbb.2
            have htyb' : AgreesHM ρe (R_b.onTy τb) :=
              AgreesHM.trans (AgreesHM.of_eraseBounds ρe) htyb
            -- STEP 5: the head body unifies against the running result (ρ-link chain).
            have hρbel₁ : Ty.BelowFvars (Φ + ctor.paramCount) (S₀.onTy ρ) :=
              Subst.onTy_belowFvars hS₀_bel (hbρ.mono hfle₀)
            have hρImg₀ : AgreesHM ρe (R₀.onTy (S₀.onTy ρ)) := by
              rw [← Subst.onTy_append]
              exact AgreesHM.trans hIMGρ (Subst.onTy_congr_hm hAgreeBelow₀ hbρ)
            have hρImg_b : AgreesHM ρe (R_b.onTy (S₁.onTy (S₀.onTy ρ))) := by
              rw [← Subst.onTy_append]
              exact AgreesHM.trans hρImg₀ (Subst.onTy_congr_hm hagb hρbel₁)
            have hUni : Unifies R_b τb (S₁.onTy (S₀.onTy ρ)) := by
              show AgreesHM (R_b.onTy τb) (R_b.onTy (S₁.onTy (S₀.onTy ρ)))
              exact AgreesHM.trans (AgreesHM.symm htyb') hρImg_b
            obtain ⟨R_u, hR_u_fac, hR_u, hR_uK⟩ :=
              UnifyRel.greatest_K_factors h₂ R_b hR_b hUni hR_bK
            have hS₂lc : ∀ p ∈ S₂, p.2.IsLC :=
              UnifyRel.lc h₂ hτb_lc (Subst.onTy_lc hS₁lc (Subst.onTy_lc hS₀lc hρLC))
            have hS₂_bel : ∀ p ∈ S₂, Ty.BelowFvars Φ₁ p.2 :=
              UnifyRel.belowFvars h₂ hτb_bel
                (Subst.onTy_belowFvars hS₁_bel
                  ((Subst.onTy_belowFvars hS₀_bel (hbρ.mono hfle₀)).mono hle_b))
            have hAgreeUni : Subst.AgreesBelow Φ₁ R_b (S₂ ++ R_u) :=
              fun v hv => by rw [Subst.onTy_append]; exact hR_u_fac (Ty.fvar v)
            have hρImg_u : AgreesHM ρe (R_u.onTy (S₂.onTy (S₁.onTy (S₀.onTy ρ)))) :=
              AgreesHM.trans hρImg_b (hR_u_fac (S₁.onTy (S₀.onTy ρ)))
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
            have hScrutStep1 : AgreesHM (S₀amb.onTy scrutTy) (R₀.onTy (S₀.onTy scrutTy)) := by
              rw [← Subst.onTy_append]
              exact Subst.onTy_congr_hm hAgreeBelow₀ hbscrut
            have hScrutStep2 : AgreesHM (R₀.onTy (S₀.onTy scrutTy))
                (R_b.onTy (S₁.onTy (S₀.onTy scrutTy))) := by
              simpa [Subst.onTy_append] using
                (Subst.onTy_congr_hm hagb (Subst.onTy_belowFvars hS₀_bel (hbscrut.mono hfle₀)))
            have hScrutStep3 : AgreesHM (R_b.onTy (S₁.onTy (S₀.onTy scrutTy)))
                (R_u.onTy (S₂.onTy (S₁.onTy (S₀.onTy scrutTy)))) := by
              simpa [Subst.onTy_append] using (hR_u_fac (S₁.onTy (S₀.onTy scrutTy)))
            have hscrutImg' : AgreesHM scruT₀ (R_u.onTy (S₂.onTy (S₁.onTy (S₀.onTy scrutTy)))) :=
              AgreesHM.trans hIMGscru (AgreesHM.trans hScrutStep1 (AgreesHM.trans hScrutStep2 hScrutStep3))
            have hctxeq' : (R_u.onCtx (S₂.onCtx (S₁.onCtx (S₀.onCtx ctx)))).eraseBounds
                = (S₀amb.onCtx ctx).eraseBounds := by
              have h1 : (R_u.onCtx (S₂.onCtx (S₁.onCtx (S₀.onCtx ctx)))).eraseBounds
                  = (R_b.onCtx (S₁.onCtx (S₀.onCtx ctx))).eraseBounds := by
                rw [← Subst.onCtx_append]
                exact (Subst.onCtx_congr_hm hAgreeUni
                  (Subst.onCtx_below hS₁_bel hle_b
                    (Subst.onCtx_below hS₀_bel hfle₀ hbelow))).symm
              have hAgree01 : Subst.AgreesBelow Φ S₀amb ((S₀ ++ S₁) ++ R_b) :=
                @Subst.AgreesBelow.trans_append Φ (Φ + ctor.paramCount) S₀amb S₀ R₀ S₁ R_b
                  hfle₀ hAgreeBelow₀ hS₀_bel hagb
              have h2 : (R_b.onCtx (S₁.onCtx (S₀.onCtx ctx))).eraseBounds
                  = (S₀amb.onCtx ctx).eraseBounds := by
                simpa [Subst.onCtx_append, List.append_assoc] using
                  (Subst.onCtx_congr_hm hAgree01 hbelow).symm
              exact h1.trans h2
            have hbr' : ∀ br ∈ rest, TypeOfMatchBranch (R_u.onCtx (S₂.onCtx (S₁.onCtx (S₀.onCtx ctx)))).eraseBounds
                (br.1, br.2.eraseBounds) scruT₀ ρe := by
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
          -- STEP 0: the wildcard body types at the SAME erased context, at ρe.
          have hdhead := hbrs (.wildcard, body) (List.mem_cons_self ..)
          have hbodyD : TypeOfHM (S₀amb.onCtx ctx).eraseBounds body.eraseBounds ρe := by
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
          have hρImg_b : AgreesHM ρe (R_b.onTy (S₁.onTy ρ)) := by
            rw [← Subst.onTy_append]
            exact AgreesHM.trans hIMGρ (Subst.onTy_congr_hm hagb hbρ)
          have hUni : Unifies R_b τb (S₁.onTy ρ) := by
            show AgreesHM (R_b.onTy τb) (R_b.onTy (S₁.onTy ρ))
            exact AgreesHM.trans (AgreesHM.symm htyb) hρImg_b
          obtain ⟨R_u, hR_u_fac, hR_u, hR_uK⟩ :=
            UnifyRel.greatest_K_factors h₂ R_b hR_b hUni hR_bK
          have hS₂lc : ∀ p ∈ S₂, p.2.IsLC :=
            UnifyRel.lc h₂ hτb_lc (Subst.onTy_lc hS₁lc hρLC)
          have hS₂_bel : ∀ p ∈ S₂, Ty.BelowFvars Φ₁ p.2 :=
            UnifyRel.belowFvars h₂ hτb_bel (Subst.onTy_belowFvars hS₁_bel (hbρ.mono hle_b))
          have hAgreeUni : Subst.AgreesBelow Φ₁ R_b (S₂ ++ R_u) :=
            fun v hv => by rw [Subst.onTy_append]; exact hR_u_fac (Ty.fvar v)
          have hρImg_u : AgreesHM ρe (R_u.onTy (S₂.onTy (S₁.onTy ρ))) :=
            AgreesHM.trans hρImg_b (hR_u_fac (S₁.onTy ρ))
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
          have hScrutStep1 : AgreesHM (S₀amb.onTy scrutTy) (R_b.onTy (S₁.onTy scrutTy)) := by
            simpa [Subst.onTy_append] using (Subst.onTy_congr_hm hagb hbscrut)
          have hScrutStep2 : AgreesHM (R_b.onTy (S₁.onTy scrutTy))
              (R_u.onTy (S₂.onTy (S₁.onTy scrutTy))) := by
            simpa [Subst.onTy_append] using (hR_u_fac (S₁.onTy scrutTy))
          have hscrutImg' : AgreesHM scruT₀ (R_u.onTy (S₂.onTy (S₁.onTy scrutTy))) :=
            AgreesHM.trans hIMGscru (AgreesHM.trans hScrutStep1 hScrutStep2)
          have hctxeq' : (R_u.onCtx (S₂.onCtx (S₁.onCtx ctx))).eraseBounds
              = (S₀amb.onCtx ctx).eraseBounds := by
            have h1 : (R_u.onCtx (S₂.onCtx (S₁.onCtx ctx))).eraseBounds
                = (R_b.onCtx (S₁.onCtx ctx)).eraseBounds := by
              rw [← Subst.onCtx_append]
              exact (Subst.onCtx_congr_hm hAgreeUni (Subst.onCtx_below hS₁_bel hle_b hbelow)).symm
            have h2 : (R_b.onCtx (S₁.onCtx ctx)).eraseBounds = (S₀amb.onCtx ctx).eraseBounds := by
              rw [← Subst.onCtx_append]
              exact (Subst.onCtx_congr_hm hagb hbelow).symm
            exact h1.trans h2
          have hbr' : ∀ br ∈ rest, TypeOfMatchBranch (R_u.onCtx (S₂.onCtx (S₁.onCtx ctx))).eraseBounds
              (br.1, br.2.eraseBounds) scruT₀ ρe := by
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
          exact fun v hv => AgreesHM.symm (hAgree v hv)
        · rw [List.nil_append]
          exact fun v hv => AgreesHM.refl _
      | consMono h₀ h₂ hrest =>
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
          have hhead : TypeOfHM (R₀.onCtx ctx).eraseBounds (Expr.eraseBounds e)
              (Ty.eraseBounds (R₀.onTy τ)) :=
            hMonoMem (e, .mono τ) (by rw [List.zip_cons_cons]; exact List.mem_cons_self) τ rfl
          -- STEP 1: head IH (ambient R₀).
          obtain ⟨R₁, hR₁, hty₁, hR₁K, hAgree₁⟩ :=
            ih.1 h₀ hsize_e hwf hbelow hwf hbelow R₀ (Ty.eraseBounds (R₀.onTy τ)) K
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
          have hρImg : AgreesHM (Ty.eraseBounds (R₀.onTy τ)) (R₁.onTy (S₁.onTy τ)) := by
            have h1 : AgreesHM (R₀.onTy τ) (R₁.onTy (S₁.onTy τ)) := by
              rw [← Subst.onTy_append]
              exact Subst.onTy_congr_hm hAgree₁ hbβ
            show Ty.eraseBounds (Ty.eraseBounds (R₀.onTy τ)) = Ty.eraseBounds (R₁.onTy (S₁.onTy τ))
            rw [Ty.eraseBounds_idem]
            exact h1
          have hUni : Unifies R₁ τ' (S₁.onTy τ) := by
            show AgreesHM (R₁.onTy τ') (R₁.onTy (S₁.onTy τ))
            exact AgreesHM.trans (AgreesHM.symm hty₁) hρImg
          obtain ⟨R_u, hR_u_fac, hR_u, hR_uK⟩ :=
            UnifyRel.greatest_K_factors h₂ R₁ hR₁ hUni hR₁K
          have hAgreeUni : Subst.AgreesBelow Φ₁ R₁ (S₂ ++ R_u) :=
            fun v hv => by rw [Subst.onTy_append]; exact hR_u_fac (Ty.fvar v)
          have hAgreeChain : Subst.AgreesBelow Φ R₀ ((S₁ ++ S₂) ++ R_u) :=
            @Subst.AgreesBelow.trans_append Φ Φ₁ R₀ S₁ R₁ S₂ R_u hfle hAgree₁ hS₁_bel hAgreeUni
          -- STEP 3: tail context identity + type identity (spec-τ below Φ).
          have hctxid : (R_u.onCtx (S₂.onCtx (S₁.onCtx ctx))).eraseBounds
              = (R₀.onCtx ctx).eraseBounds := by
            have h1 : (R₀.onCtx ctx).eraseBounds = (((S₁ ++ S₂) ++ R_u).onCtx ctx).eraseBounds :=
              Subst.onCtx_congr_hm hAgreeChain hbelow
            simpa [Subst.onCtx_append, List.append_assoc] using h1.symm
          have hkey_t : ∀ {t : Ty}, Ty.BelowFvars Φ t →
              AgreesHM (R_u.onTy ((S₁ ++ S₂).onTy t)) (R₀.onTy t) := by
            intro t ht
            have h1 : AgreesHM (R₀.onTy t) (((S₁ ++ S₂) ++ R_u).onTy t) :=
              Subst.onTy_congr_hm hAgreeChain ht
            rw [Subst.onTy_append] at h1
            exact AgreesHM.symm h1
          -- STEP 4: tail recursion premises (context + type rewrites).
          have hwf' : CtxWF (S₂.onCtx (S₁.onCtx ctx)) :=
            Subst.onCtx_wf hS₂lc (Subst.onCtx_wf hS₁lc hwf)
          have hbelow' : CtxBelow Φ₁ (S₂.onCtx (S₁.onCtx ctx)) :=
            Subst.onCtx_below hS₂_bel (le_refl _) (Subst.onCtx_below hS₁_bel hfle hbelow)
          have hMonoMem' : ∀ p ∈ rest.zip (specs.map (RecSpec.onSubst (S₁ ++ S₂))),
              ∀ τm, p.2 = .mono τm →
                TypeOfHM (R_u.onCtx (S₂.onCtx (S₁.onCtx ctx))).eraseBounds
                  (Expr.eraseBounds p.1) (Ty.eraseBounds (R_u.onTy τm)) := by
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
              have htype_id : Ty.eraseBounds (R_u.onTy ((S₁ ++ S₂).onTy τ₁))
                  = Ty.eraseBounds (R₀.onTy τ₁) := hkey_t hbτ₁
              rw [htype_id]
              exact hMonoMem (e', .mono τ₁)
                (by rw [List.zip_cons_cons]; exact List.mem_cons_of_mem _ hq) τ₁ rfl
          have hPolyMem' : ∀ p ∈ rest.zip (specs.map (RecSpec.onSubst (S₁ ++ S₂))),
              ∀ σ₀, p.2 = .poly σ₀ → ∀ Ys, FreshNames L σ₀.paramCount Ys →
                TypeOfHM (R_u.onCtx (S₂.onCtx (S₁.onCtx ctx))).eraseBounds
                  (Expr.eraseBounds (Expr.openTyVars Ys p.1)) (σ₀.openVars Ys) := by
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
          have hAgreeRefl : ∀ v, v < Φ₁ → AgreesHM (R_u.onTy (.fvar v)) (R_u.onTy (.fvar v)) :=
            fun v hv => AgreesHM.refl _
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
            AgreesHM.trans (AgreesHM.symm (hAgree v hv)) (hAgree₁ v (by omega))
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
      | consPoly =>
        rename_i N σ specs e rest Φ₁ S₁ Schk S₂ τ huni hesc1 hN h₀ hesc2 hrest
        exact fun hwf hbelow S₀ L K R₀ hS₀ hKΦ hKe hKfix hSpecLC hSpecBelow hKsch hR₀ hR₀K hAgree hMonoMem hPolyMem => by
          -- SPINE-GROUP-POLY (block-swap skolem dodge, ported from the closed
          -- `[letinann-agent]` shape; the poly member's scheme-relative premise
          -- is transported from `R₀` to the skolem-fixing `R₀' = conj f R₀`).
          have hsize_e : (e.openTyVars (freshVars N σ.paramCount)).size < n := by
            rw [Expr.size_openTyVars]
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
          have hKσ : ∀ y ∈ σ.body.freeVars, y ∈ K := hKsch (.poly σ) List.mem_cons_self σ rfl
          have hSpecLC' : ∀ s ∈ specs, s.LC := fun s hs => hSpecLC s (List.mem_cons_of_mem _ hs)
          have hSpecBelow' : ∀ s ∈ specs, ∀ τm, s = .mono τm → Ty.BelowFvars Φ τm :=
            fun s hs τm hτm => hSpecBelow s (List.mem_cons_of_mem _ hs) τm hτm
          have hKsch' : ∀ s ∈ specs, ∀ σ', s = .poly σ' → ∀ y ∈ σ'.body.freeVars, y ∈ K :=
            fun s hs σ' hσ' => hKsch s (List.mem_cons_of_mem _ hs) σ' hσ'
          have hσwf : σ.WF := hSpecLC (.poly σ) List.mem_cons_self
          -- the head's cofinite scheme-relative typing at the R₀-context
          have hcofin_head : ∀ Xs : List Nat, FreshNames L σ.paramCount Xs →
              TypeOfHM (R₀.onCtx ctx).eraseBounds (e.eraseBounds.openTyVars Xs) (σ.openVars Xs) := by
            intro Xs hX
            simpa [Expr.eraseBounds_openTyVars] using
              hPolyMem (e, .poly σ) (by rw [List.zip_cons_cons]; exact List.mem_cons_self) σ rfl Xs hX
          set Ys : List Nat := freshVars N σ.paramCount with hYs_def
          have hYs_len : Ys.length = σ.paramCount := by rw [hYs_def]; exact freshVars_length N σ.paramCount
          have hYs_lt : ∀ y ∈ Ys, y < N + σ.paramCount := fun y hy =>
            freshVars_lt y (by simpa [hYs_def] using hy)
          have hYs_ge : ∀ y ∈ Ys, N ≤ y := fun y hy => freshVars_ge y (by simpa [hYs_def] using hy)
          have hYs_Φ : ∀ y ∈ Ys, Φ₀ ≤ y := fun y hy => le_trans (le_trans hle hN) (hYs_ge y hy)
          have hfle : N + σ.paramCount ≤ Φ₁ := Infer.frontier_le h₀
          have hΦΦ₁ : Φ ≤ Φ₁ := le_trans hN (le_trans (Nat.le_add_right N σ.paramCount) hfle)
          have hKΦ₁ : ∀ k ∈ K, k < Φ₁ := fun k hk =>
            lt_of_lt_of_le (hKΦ k hk) (le_trans hle hΦΦ₁)
          have hKΦKY : ∀ k ∈ K ++ Ys, k < N + σ.paramCount := by
            intro k hk
            rcases List.mem_append.mp hk with hk | hk
            · have := hKΦ k hk; omega
            · exact hYs_lt k hk
          have hbelowN : CtxBelow (N + σ.paramCount) ctx :=
            fun M hM => (hbelow M hM).mono (by omega)
          -- STEP 1: fresh block `M₀` and the skolem-fixing ambient `R₀' = conj f R₀`.
          obtain ⟨M₀, hd, hM₀fresh⟩ := exists_fresh_block
            (R₀.map Prod.fst ++ R₀.flatMap (fun p => p.2.freeVars) ++ List.range N) N σ.paramCount
          have hR₀key_lt : ∀ p ∈ R₀, p.1 < M₀ := fun p hp =>
            hM₀fresh p.1 (List.mem_append_left _ (List.mem_append_left _ (List.mem_map.mpr ⟨p, hp, rfl⟩)))
          have hR₀range_lt : ∀ p ∈ R₀, ∀ v ∈ p.2.freeVars, v < M₀ := fun p hp v hv =>
            hM₀fresh v (List.mem_append_left _ (List.mem_append_right _ (List.mem_flatMap.mpr ⟨p, hp, hv⟩)))
          have hR₀belowM₀ : ∀ p ∈ R₀, Ty.BelowFvars M₀ p.2 :=
            fun p hp => Ty.BelowFvars.of_freeVars_lt (fun v hv => hR₀range_lt p hp v hv)
          have hNrange : ∀ x ∈ List.range N, x < M₀ := fun x hx =>
            hM₀fresh x (List.mem_append_right _ hx)
          have finj : Function.Injective (blockSwap N M₀ σ.paramCount) := blockSwap_injective hd
          have hffix : ∀ v, v < N → blockSwap N M₀ σ.paramCount v = v :=
            fun v hv => blockSwap_lt (by omega) hv
          set R₀' : Subst := Subst.conj (blockSwap N M₀ σ.paramCount) R₀ with hR₀'_def
          have hconj_below : ∀ v, v < N → R₀'.onTy (.fvar v) = Ty.rename (blockSwap N M₀ σ.paramCount) (R₀.onTy (.fvar v)) := by
            intro v hv
            have h := Subst.onTy_conj finj R₀ (Ty.fvar v)
            rw [Ty.rename_fvar, hffix v hv] at h
            rw [hR₀'_def]
            exact h
          have hR₀'lc : ∀ p ∈ R₀', p.2.IsLC := by
            rw [hR₀'_def]
            exact Subst.conj_lc hR₀
          have hR₀'K : ∀ k ∈ K, R₀'.onTy (.fvar k) = .fvar k := by
            intro k hk
            have hklt : k < N := by
              have := hKΦ k hk; omega
            rw [hconj_below k hklt, hR₀K k hk, Ty.rename_fvar, hffix k hklt]
          have hR₀'Ys : ∀ Y ∈ Ys, R₀'.onTy (.fvar Y) = .fvar Y := by
            intro Y hY
            rw [hR₀'_def]
            apply Ty.substFvars_eq_self_of_no_key
            intro p hp hc
            simp only [Ty.freeVars, List.mem_singleton] at hc
            simp only [Subst.conj, List.mem_map] at hp
            obtain ⟨q, hq, rfl⟩ := hp
            have hqlt : q.1 < M₀ := hR₀key_lt q hq
            have hYge : N ≤ Y := hYs_ge Y hY
            have hYlt : Y < N + σ.paramCount := hYs_lt Y hY
            simp only [blockSwap] at hc
            split_ifs at hc <;> omega
          -- STEP 2: transport the cofinite premise to the R₀'-world (erased type).
          have hctxeq_gen : (blockList N M₀ σ.paramCount).onCtx (R₀.onCtx ctx)
              = R₀'.onCtx ctx := by
            rw [hR₀'_def]
            simp only [Subst.onCtx, Subst.onEnv, List.map_map]
            congr 1
            apply List.map_congr_left
            intro M hM
            simp only [Function.comp_apply, Subst.onPolyTy]
            congr 1
            rw [blockList_onTy hd (fun v hv => by
              have hlt := (Subst.onTy_belowFvars hR₀belowM₀
                ((hbelow M hM).mono (by omega))).mem_lt v hv
              omega)]
            conv_rhs => rw [← Ty.rename_eq_self (f := blockSwap N M₀ σ.paramCount) (τ := M.body)
              (fun v hv => hffix v (by have := (hbelow M hM).mem_lt v hv; omega))]
            rw [Subst.onTy_conj finj]
          have hcofin' : ∀ Xs : List Nat, FreshNames (L ++ Ys) σ.paramCount Xs →
              TypeOfHM (R₀'.onCtx ctx).eraseBounds (e.eraseBounds.openTyVars Xs)
                (Ty.eraseBounds (σ.openVars Xs)) := by
            intro Xs hXs
            obtain ⟨hXlen, hXnodup, hXavoid⟩ := hXs
            have hXL : FreshNames L σ.paramCount Xs :=
              ⟨hXlen, hXnodup, fun x hx hc => hXavoid x hx (List.mem_append_left _ hc)⟩
            have hXYs : ∀ x ∈ Xs, x ∉ Ys := fun x hx hc => hXavoid x hx (List.mem_append_right _ hc)
            have hfix : (e.eraseBounds.openTyVars Xs).substTyFvars (blockList N M₀ σ.paramCount)
                = e.eraseBounds.openTyVars Xs := by
              apply Expr.substTyFvars_eq_self_of_not_mem_tyFreeVars
              intro p hp hc
              simp only [blockList, List.mem_map] at hp
              obtain ⟨i, hi, rfl⟩ := hp
              rcases Expr.tyFreeVars_openTyVars hc with h | h
              · have := hKΦ (N + i) (hKbody (N + i) ((Expr.mem_tyFreeVars_eraseBounds e (N + i)).mp h)); omega
              · exact hXYs (N + i) h (by
                  simp only [Ys, freshVars, List.mem_map, List.mem_range]
                  exact ⟨i, List.mem_range.mp hi, rfl⟩)
            have hfixσ : (blockList N M₀ σ.paramCount).onTy (σ.openVars Xs) = σ.openVars Xs := by
              apply Ty.substFvars_eq_self_of_no_key
              intro p hp hc
              simp only [blockList, List.mem_map] at hp
              obtain ⟨i, hi, rfl⟩ := hp
              rcases Ty.freeVars_openVars_subset (N + i) hc with h | h
              · have := hKΦ (N + i) (hKσ (N + i) h); omega
              · exact hXYs (N + i) h (by
                  simp only [Ys, freshVars, List.mem_map, List.mem_range]
                  exact ⟨i, List.mem_range.mp hi, rfl⟩)
            have hcofin_headE : TypeOfHM (R₀.onCtx ctx).eraseBounds
                ((e.eraseBounds.openTyVars Xs).eraseBounds) (Ty.eraseBounds (σ.openVars Xs)) := by
              have h := TypeOfHM.eraseBounds_of (hcofin_head Xs hXL)
              simpa [Ctx.eraseBounds, Env.eraseBounds_idem, CtorEnv.eraseBounds_idem] using h
            have hren := TypeOfHM.onSubst_eraseBounds_fixed
              (blockList N M₀ σ.paramCount) (blockList_lc N M₀ σ.paramCount) hfix hcofin_headE
            have hctx : ((blockList N M₀ σ.paramCount).onCtx (R₀.onCtx ctx)).eraseBounds
                = (R₀'.onCtx ctx).eraseBounds := by
              rw [hR₀'_def]
              exact congrArg Ctx.eraseBounds hctxeq_gen
            rw [hctx, hfixσ] at hren
            simpa [Expr.eraseBounds_openTyVars, Expr.eraseBounds_idem] using hren
          -- instantiate at the algorithmic skolems `Ys` (rename `Xs → Ys`)
          have hhead : TypeOfHM (R₀'.onCtx ctx).eraseBounds (e.eraseBounds.openTyVars Ys)
              (Ty.eraseBounds (σ.openVars Ys)) := by
            have hcofinE : ∀ Xs : List Nat, FreshNames (L ++ Ys) (PolyTy.eraseBounds σ).paramCount Xs →
                TypeOfHM (R₀'.onCtx ctx).eraseBounds (e.eraseBounds.openTyVars Xs)
                  ((PolyTy.eraseBounds σ).openVars Xs) := by
              intro Xs hX
              have hXL : FreshNames (L ++ Ys) σ.paramCount Xs := by
                simpa [PolyTy.eraseBounds] using hX
              have h := hcofin' Xs hXL
              simpa [PolyTy.eraseBounds_openVars] using h
            have hYs_lenE : Ys.length = (PolyTy.eraseBounds σ).paramCount := by
              simpa [PolyTy.eraseBounds] using hYs_len
            have hblock := typeOfHM_at_block (L := L ++ Ys) (Ys := Ys) (σ := PolyTy.eraseBounds σ)
              (rhs := e.eraseBounds) (ctx := (R₀'.onCtx ctx).eraseBounds) hYs_lenE hcofinE
            simpa [PolyTy.eraseBounds_openVars] using hblock
          -- STEP 3: the head IH (ambient R₀', K ∪ Ys).
          have hKe' : ∀ y ∈ (e.openTyVars Ys).tyFreeVars, y ∈ K ++ Ys := by
            intro y hy
            rcases Expr.tyFreeVars_openTyVars hy with h | h
            · exact List.mem_append_left _ (hKbody y h)
            · exact List.mem_append_right _ h
          have hR₀'Kfix : ∀ k ∈ K ++ Ys, R₀'.onTy (.fvar k) = .fvar k := by
            intro k hk
            rcases List.mem_append.mp hk with hk | hk
            · exact hR₀'K k hk
            · exact hR₀'Ys k hk
          have hhead' : TypeOfHM (R₀'.onCtx ctx).eraseBounds ((e.openTyVars Ys).eraseBounds)
              (Ty.eraseBounds (σ.openVars Ys)) := by
            simpa [Expr.eraseBounds_openTyVars] using hhead
          obtain ⟨R₁, hR₁lc, hty₁, hR₁K, hAgree₁⟩ :=
            ih.1 h₀ hsize_e hwf hbelowN hwf hbelowN R₀' (Ty.eraseBounds (σ.openVars Ys)) (K ++ Ys)
              hR₀'lc hKΦKY hKe' hR₀'Kfix hhead'
          have hτ_lc : τ.IsLC := (Infer.lc h₀ hwf).1
          have hS₁lc : ∀ p ∈ S₁, p.2.IsLC := (Infer.lc h₀ hwf).2
          have h₀below := Infer.belowFvars h₀ hbelowN (fun y hy => by
            rcases Expr.tyFreeVars_openTyVars hy with h | h
            · have := hKΦ y (hKbody y h); omega
            · have := freshVars_lt y h; omega)
          have hτ_bel : Ty.BelowFvars Φ₁ τ := h₀below.1
          have hS₁_bel : ∀ p ∈ S₁, Ty.BelowFvars Φ₁ p.2 := h₀below.2
          -- the scheme opening is fixed by R₁ (σ's body vars ⊆ K, skolems ∈ K ∪ Ys)
          have hσfix : R₁.onTy (σ.openVars Ys) = σ.openVars Ys := by
            apply Subst.onTy_eq_self_of_fixes
            intro z hz
            rcases Ty.freeVars_openVars_subset z hz with h | h
            · exact hR₁K z (List.mem_append_left _ (hKσ z h))
            · exact hR₁K z (List.mem_append_right _ h)
          have hσopen_lc : (σ.openVars Ys).IsLC :=
            PolyTy.openVars_isLC hσwf (by omega)
          -- STEP 4: unify the head output against the scheme opening.
          have hUni : Unifies R₁ τ (σ.openVars Ys) := by
            show AgreesHM (R₁.onTy τ) (R₁.onTy (σ.openVars Ys))
            rw [hσfix]
            show AgreesHM (R₁.onTy τ) (σ.openVars Ys)
            show Ty.eraseBounds (R₁.onTy τ) = Ty.eraseBounds (σ.openVars Ys)
            rw [← Ty.eraseBounds_idem (σ.openVars Ys)]
            exact AgreesHM.symm hty₁
          obtain ⟨V, hVfac, hVlc, hVK⟩ :=
            UnifyRel.greatest_K_factors huni R₁ hR₁lc hUni hR₁K
          have hSchk_lc : ∀ p ∈ Schk, p.2.IsLC := UnifyRel.lc huni hτ_lc hσopen_lc
          have hσbody_bel : Ty.BelowFvars Φ₁ σ.body :=
            Ty.BelowFvars.of_freeVars_lt (fun y hy => hKΦ₁ y (hKσ y hy))
          have hSchk_bel : ∀ p ∈ Schk, Ty.BelowFvars Φ₁ p.2 :=
            UnifyRel.belowFvars huni hτ_bel
              (Ty.openVars_belowFvars hσbody_bel
                (fun x hx => by have := freshVars_lt x hx; omega))
          set blk : Subst := V ++ blockListBack N M₀ σ.paramCount with hblk_def
          -- STEP 5: the R₀-side agreement chain (block-swap-back), over the tier
          -- frontier `Φ` (so the tail re-derivation can use spec-τ `BelowFvars Φ`).
          have hblk_agree : ∀ {a b : Ty}, AgreesHM a b →
              AgreesHM ((blockListBack N M₀ σ.paramCount).onTy a) ((blockListBack N M₀ σ.paramCount).onTy b) := by
            intro a b hab
            change Ty.eraseBounds (Ty.substFvars (blockListBack N M₀ σ.paramCount) a)
              = Ty.eraseBounds (Ty.substFvars (blockListBack N M₀ σ.paramCount) b)
            rw [Ty.eraseBounds_substFvars, Ty.eraseBounds_substFvars]
            exact congrArg (fun E => Ty.substFvars (List.map (fun p : Nat × Ty => (p.1, Ty.eraseBounds p.2))
              (blockListBack N M₀ σ.paramCount)) E) hab
          have hAgreeMid : Subst.AgreesBelow Φ R₀ ((S₁ ++ Schk) ++ blk) := by
            intro v hv
            have hvN : v < N := by omega
            have hR₀v_block : ∀ w ∈ (R₀.onTy (.fvar v)).freeVars,
                ¬ (M₀ ≤ w ∧ w < M₀ + σ.paramCount) := by
              intro w hw
              have := (Subst.onTy_belowFvars hR₀belowM₀ (Ty.BelowFvars.fvar (by omega))).mem_lt w hw
              omega
            have hstep1 : AgreesHM (R₀.onTy (.fvar v))
                ((blockListBack N M₀ σ.paramCount).onTy (R₀'.onTy (.fvar v))) := by
              rw [hconj_below v hvN]
              exact congrArg Ty.eraseBounds (blockListBack_onTy_rename hd hR₀v_block).symm
            have hstep2 : AgreesHM ((blockListBack N M₀ σ.paramCount).onTy (R₀'.onTy (.fvar v)))
                ((blockListBack N M₀ σ.paramCount).onTy ((S₁ ++ R₁).onTy (.fvar v))) :=
              hblk_agree (hAgree₁ v (by omega))
            have hstep3 : AgreesHM ((blockListBack N M₀ σ.paramCount).onTy ((S₁ ++ R₁).onTy (.fvar v)))
                ((blockListBack N M₀ σ.paramCount).onTy
                  (V.onTy (Schk.onTy (S₁.onTy (.fvar v))))) := by
              rw [Subst.onTy_append]
              exact hblk_agree (hVfac (S₁.onTy (.fvar v)))
            have hstep3' : AgreesHM (R₀.onTy (.fvar v))
                (((S₁ ++ Schk) ++ (V ++ blockListBack N M₀ σ.paramCount)).onTy (.fvar v)) := by
              rw [Subst.onTy_append, Subst.onTy_append, Subst.onTy_append]
              exact AgreesHM.trans hstep1 (AgreesHM.trans hstep2 hstep3)
            simpa [hblk_def] using hstep3'

          -- STEP 6: tail context identity + type identity (spec-τ below Φ).
          have hctxid : (blk.onCtx (Schk.onCtx (S₁.onCtx ctx))).eraseBounds
              = (R₀.onCtx ctx).eraseBounds := by
            have h1 : (R₀.onCtx ctx).eraseBounds = (((S₁ ++ Schk) ++ blk).onCtx ctx).eraseBounds :=
              Subst.onCtx_congr_hm hAgreeMid hbelow
            simpa [Subst.onCtx_append, List.append_assoc, hblk_def] using h1.symm
          have hkey_t : ∀ {t : Ty}, Ty.BelowFvars Φ t →
              AgreesHM (blk.onTy ((S₁ ++ Schk).onTy t)) (R₀.onTy t) := by
            intro t ht
            have h1 : AgreesHM (R₀.onTy t) (((S₁ ++ Schk) ++ blk).onTy t) :=
              Subst.onTy_congr_hm hAgreeMid ht
            rw [Subst.onTy_append] at h1
            exact AgreesHM.symm h1
          -- STEP 7: tail recursion premises (context + type rewrites).
          have hwf₁ : CtxWF (Schk.onCtx (S₁.onCtx ctx)) :=
            Subst.onCtx_wf hSchk_lc (Subst.onCtx_wf hS₁lc hwf)
          have hbelow₁ : CtxBelow Φ₁ (Schk.onCtx (S₁.onCtx ctx)) :=
            Subst.onCtx_below hSchk_bel (le_refl _) (Subst.onCtx_below hS₁_bel (by omega) hbelowN)
          have hAgreeRefl : ∀ v, v < Φ₁ → AgreesHM (blk.onTy (.fvar v)) (blk.onTy (.fvar v)) :=
            fun v hv => AgreesHM.refl _
          have hMonoMem' : ∀ p ∈ rest.zip (specs.map (RecSpec.onSubst (S₁ ++ Schk))),
              ∀ τm, p.2 = .mono τm →
                TypeOfHM (blk.onCtx (Schk.onCtx (S₁.onCtx ctx))).eraseBounds
                  (Expr.eraseBounds p.1) (Ty.eraseBounds (blk.onTy τm)) := by
            intro p hp τm hτm
            rcases List.mem_zip_map_right hp with ⟨e', s₀, hq, hpq⟩
            subst hpq
            cases s₀ with
            | poly σ₀ => exact absurd hτm (by simp [RecSpec.onSubst])
            | mono τ₁ =>
              have hτeq : τm = (S₁ ++ Schk).onTy τ₁ := by
                have hred : RecSpec.onSubst (S₁ ++ Schk) (RecSpec.mono τ₁)
                    = RecSpec.mono ((S₁ ++ Schk).onTy τ₁) := rfl
                rw [hred] at hτm
                exact (RecSpec.mono.inj hτm).symm
              subst hτeq
              rw [hctxid]
              have hbτ₁ : Ty.BelowFvars Φ τ₁ :=
                hSpecBelow' (RecSpec.mono τ₁) (List.of_mem_zip hq).2 τ₁ rfl
              have htype_id : Ty.eraseBounds (blk.onTy ((S₁ ++ Schk).onTy τ₁))
                  = Ty.eraseBounds (R₀.onTy τ₁) := hkey_t hbτ₁
              rw [htype_id]
              exact hMonoMem (e', .mono τ₁)
                (by rw [List.zip_cons_cons]; exact List.mem_cons_of_mem _ hq) τ₁ rfl
          have hPolyMem' : ∀ p ∈ rest.zip (specs.map (RecSpec.onSubst (S₁ ++ Schk))),
              ∀ σ₀, p.2 = .poly σ₀ → ∀ Ys', FreshNames L σ₀.paramCount Ys' →
                TypeOfHM (blk.onCtx (Schk.onCtx (S₁.onCtx ctx))).eraseBounds
                  (Expr.eraseBounds (Expr.openTyVars Ys' p.1)) (σ₀.openVars Ys') := by
            intro p hp σ₀ hσ₀ Ys' hYs'
            rcases List.mem_zip_map_right hp with ⟨e', s₀, hq, hpq⟩
            subst hpq
            cases s₀ with
            | mono τ₁ => exact absurd hσ₀ (by simp [RecSpec.onSubst])
            | poly σ₁ =>
              have hσeq : σ₀ = σ₁ := by
                have hred : RecSpec.onSubst (S₁ ++ Schk) (RecSpec.poly σ₁) = RecSpec.poly σ₁ := rfl
                rw [hred] at hσ₀
                exact (RecSpec.poly.inj hσ₀).symm
              subst hσeq
              rw [hctxid]
              exact hPolyMem (e', .poly σ₀)
                (by rw [List.zip_cons_cons]; exact List.mem_cons_of_mem _ hq) σ₀ rfl Ys' hYs'
          have hSpecLC'' : ∀ s' ∈ specs.map (RecSpec.onSubst (S₁ ++ Schk)), s'.LC := by
            intro s' hs'
            obtain ⟨s₀, hs₀, rfl⟩ := List.mem_map.mp hs'
            exact RecSpec.LC.onSubst
              (fun p hp => (List.mem_append.mp hp).elim (fun h1 => hS₁lc p h1) (fun h2 => hSchk_lc p h2))
              (hSpecLC' s₀ hs₀)
          have hSpecBelow'' : ∀ s' ∈ specs.map (RecSpec.onSubst (S₁ ++ Schk)),
              ∀ τm, s' = .mono τm → Ty.BelowFvars Φ₁ τm := by
            intro s' hs' τm hτm
            obtain ⟨s₀, hs₀, rfl⟩ := List.mem_map.mp hs'
            cases s₀ with
            | poly σ₀ => exact absurd hτm (by simp [RecSpec.onSubst])
            | mono τ₁ =>
              have hτeq : τm = (S₁ ++ Schk).onTy τ₁ := by
                have hred : RecSpec.onSubst (S₁ ++ Schk) (RecSpec.mono τ₁)
                    = RecSpec.mono ((S₁ ++ Schk).onTy τ₁) := rfl
                rw [hred] at hτm
                exact (RecSpec.mono.inj hτm).symm
              subst hτeq
              exact Subst.onTy_belowFvars (fun p hp => by
                rcases List.mem_append.mp hp with hp | hp
                · exact hS₁_bel p hp
                · exact hSchk_bel p hp)
                ((hSpecBelow' (RecSpec.mono τ₁) hs₀ τ₁ rfl).mono (by omega))
          have hKsch'' : ∀ s' ∈ specs.map (RecSpec.onSubst (S₁ ++ Schk)),
              ∀ σ', s' = .poly σ' → ∀ y ∈ σ'.body.freeVars, y ∈ K := by
            intro s' hs' σ' hσ'
            obtain ⟨s₀, hs₀, rfl⟩ := List.mem_map.mp hs'
            cases s₀ with
            | mono τ₁ => exact absurd hσ' (by simp [RecSpec.onSubst])
            | poly σ₀ =>
              have hσeq : σ' = σ₀ := by
                have hred : RecSpec.onSubst (S₁ ++ Schk) (RecSpec.poly σ₀) = RecSpec.poly σ₀ := rfl
                rw [hred] at hσ'
                exact (RecSpec.poly.inj hσ').symm
              subst hσeq
              exact hKsch' (RecSpec.poly σ') hs₀ σ' rfl
          -- STEP 8: recurse on the tail (ambient `blk`, reflexive over Φ₁).
          have hblklc : ∀ p ∈ blk, p.2.IsLC := by
            rw [hblk_def]
            intro p hp
            rcases List.mem_append.mp hp with hp | hp
            · exact hVlc p hp
            · exact blockListBack_lc N M₀ σ.paramCount p hp
          have hblkK : ∀ k ∈ K, blk.onTy (.fvar k) = .fvar k := by
            intro k hk
            rw [hblk_def, Subst.onTy_append, hVK k (List.mem_append_left _ hk)]
            apply Ty.substFvars_eq_self_of_no_key
            intro p hp hc
            simp only [blockListBack, List.mem_map] at hp
            obtain ⟨i, _, rfl⟩ := hp
            simp only [Ty.freeVars, List.mem_singleton] at hc
            have hklt : k < Φ₀ := hKΦ k hk
            omega
          obtain ⟨R_r, hR_r, hR_rK, hAgreeTail, hAgreeTailR⟩ :=
            ih.2.2 hrest (le_refl _) hsize_rest hwf₁ hbelow₁ hwf₁ hbelow₁ blk L K blk
              hblklc hKΦ₁ hKrest hblkK hSpecLC'' hSpecBelow'' hKsch'' hblklc hblkK hAgreeRefl hMonoMem' hPolyMem'
          -- STEP 9: assemble.
          have hAgree0 : Subst.AgreesBelow Φ₀ S₀ ((S₁ ++ Schk) ++ blk) := fun v hv =>
            AgreesHM.trans (AgreesHM.symm (hAgree v hv)) (hAgreeMid v (by omega))
          have hbelowS₁Schk : ∀ p ∈ S₁ ++ Schk, Ty.BelowFvars Φ₁ p.2 := by
            intro p hp
            rcases List.mem_append.mp hp with hp | hp
            · exact hS₁_bel p hp
            · exact hSchk_bel p hp
          have hAgree : Subst.AgreesBelow Φ₀ S₀ (((S₁ ++ Schk) ++ S₂) ++ R_r) :=
            @Subst.AgreesBelow.trans_append Φ₀ Φ₁ S₀ (S₁ ++ Schk) blk S₂ R_r (le_trans hle hΦΦ₁)
              hAgree0 hbelowS₁Schk hAgreeTail
          have hAgreeR : Subst.AgreesBelow Φ R₀ ((S₁ ++ Schk ++ S₂) ++ R_r) :=
            @Subst.AgreesBelow.trans_append Φ Φ₁ R₀ (S₁ ++ Schk) blk S₂ R_r hΦΦ₁
              hAgreeMid hbelowS₁Schk hAgreeTail
          refine ⟨R_r, hR_r, hR_rK, ?_, ?_⟩
          · simpa [List.append_assoc, hblk_def] using hAgree
          · simpa [List.append_assoc, hblk_def] using hAgreeR

-- END-SECTION-SPINE



