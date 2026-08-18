import FHM.Core

/-! # Promoting unannotated `letRec` members to annotated ones

The letRec promotion described in `briefs/complexity-budget.md` §3. This module holds the
promotion and its transport metatheory — originally the reference proof
`FHM/SpikeLetRecPromote.lean`, now part of the built library (imported by `InferW`, which uses
`promoteScheme` / `retargetStored` / `monoTyped_to_polyTyped` / `polyTyped_to_monoTyped` in the
`letRec` elaboration and its soundness proof). Derivations are declarative (`TypeOfElabHM`);
`Infer` itself is deliberately not involved here.

## The encoding

`Infer.letRec` currently elaborates a mixed recursion group into `Expr.letRecElab`: an `n`-deep
nest of `letIn`s, each wrapping a whole copy of the group projected at one member. It does that
because an unannotated member is generalised for the body but has **no Λ-binder in the term**
for `.var j tyArgs` to instantiate — so the Λ is hoisted outside as a `letIn` scheme. The nest
changes the elaboratum's *shape*, which is what forces `Infer.sourceSound` to be a second full
induction rather than a corollary of `Infer.sound`.

The alternative proved here puts the Λ *inside* the node, using the `anns` slot that is already
there: promote each `.mono τ` member to `.poly ⟨|G|, Ty.closeOver G τ⟩` — generalising over the
**full pool `G`**, not `Ty.genFilter G τ` — and retarget group-internal uses from `.var j []`
to `.var j (Ty.bvarRangeFrom d |G|)`.

The full pool is used rather than the filter so that every promoted member has the *same* arity
`|G|` and the same binder positions: a sibling reference `.var j (bvarRange |G|)` then uniformly
means "instantiate sibling `j` at **my** pool binders", which is exactly what reconstitutes the
shared-monotype link that `RecSpecs.MonoTyped`'s "same `Xs` for the whole group" enforces. Under
`genFilter` the arities differ per member and the indices would not line up.

This is legal because `PolyTy.WF M := ContainsBvarsUpTo M.paramCount M.body` is an *upper
bound*, not a usage requirement — vacuous binders are well-formed. **`Expr` is unchanged
throughout**: this is slot-filling, the same kind elaboration already does for `letIn`.

## What this file contains

- `promoteScheme` / `promoteSpecs` / `promoteAnns` and their basic facts (well-formedness, every
  slot filled). `promoteScheme_wf` and `promoteScheme_openVars` are the type-level core; the
  latter shows that opening the promoted scheme at fresh `Ys` recovers exactly the shared-pool
  opening the mono regime types members at.
- Concrete derivations, mono and promoted, covering: no self-reference (`smoke_*_noref`),
  self-reference (`smoke_*_selfref`), mutual recursion with a vacuous binder (`mutual_*`), and
  index alignment across members using different pool slots (`mutual_mixed_*`).
- The transport lemmas that make the promotion a *sound* transform rather than a syntactic
  reshuffle:
  - `retarget_transport`: a `TypeOfElabHM` derivation over a monomorphic env prefix carries to
    one over the promoted schemes, with group-variable uses retargeted to `Vs`.
  - `retarget_untransport`: the reverse ("forgetting") direction.
  - `monoTyped_to_polyTyped` / `polyTyped_to_monoTyped`: the letRec-shaped corollaries, proving
    the two `RecSpec` regimes are interchangeable at the promoted schemes. Together they are the
    prerequisite for `Infer.sourceSound` becoming a decoration-forgetting corollary.
- `promoted_preservation`: preservation for a promoted group, shown to be a corollary of the
  general `TypeOfElabHM.preservation` (the promotion touches neither `Expr`, `SmallStep.Step`,
  nor `TypeOfElabHM`).
- `retargetStored` and its commute lemma `retargetStored_openTyVars`: the *stored*-form
  traversal the real elaborator emits (with `Ty.bvarRangeFrom d |G|` at type-binder depth `d`),
  and its commute with `openTyVars` — this discharges the `hopen` hypothesis that the transport
  corollaries leave open.

A `#print axioms` guard at the bottom records that every headline result is axiom-clean
(`propext`, `Classical.choice`, `Quot.sound` — no `sorryAx`).
-/

namespace LetRecPromote

/-! ## The promotion -/

/-- Promote a mono member's shared monotype to a scheme over the **full** pool `G`.
    Contrast `PolyTy.genGroup G τ = ⟨(Ty.genFilter G τ).length, Ty.closeOver (genFilter G τ) τ⟩`,
    which generalises only over `G ∩ ftv τ` and so has a member-dependent arity. -/
def promoteScheme (G : List Nat) (τ : Ty) : PolyTy :=
  ⟨G.length, Ty.closeOver G τ⟩

/-- Promote a whole spec list: monos become polys at their full-pool schemes; already-poly
    members are left alone. -/
def promoteSpecs (G : List Nat) (specs : List RecSpec) : List RecSpec :=
  specs.map fun
    | .mono τ => .poly (promoteScheme G τ)
    | .poly σ => .poly σ

/-- The stored `anns` after promotion — every slot is `some`. -/
def promoteAnns (G : List Nat) (specs : List RecSpec) : List (Option PolyTy) :=
  (promoteSpecs G specs).map RecSpec.ann

@[simp] theorem promoteSpecs_length {G : List Nat} {specs : List RecSpec} :
    (promoteSpecs G specs).length = specs.length := by
  simp [promoteSpecs]

/-- Every promoted spec is a `poly`. This is what makes `RecSpecs.MonoTyped` vacuous. -/
theorem promoteSpecs_all_poly {G : List Nat} {specs : List RecSpec} :
    ∀ s ∈ promoteSpecs G specs, ∃ σ, s = .poly σ := by
  intro s hs
  simp only [promoteSpecs, List.mem_map] at hs
  obtain ⟨s', _, rfl⟩ := hs
  cases s' with
  | mono τ => exact ⟨promoteScheme G τ, rfl⟩
  | poly σ => exact ⟨σ, rfl⟩

/-- Every promoted ann is `some` — i.e. the elaboratum's `anns` slot is fully filled. -/
theorem promoteAnns_all_some {G : List Nat} {specs : List RecSpec} :
    ∀ a ∈ promoteAnns G specs, ∃ σ, a = some σ := by
  intro a ha
  simp only [promoteAnns, List.mem_map] at ha
  obtain ⟨s, hs, rfl⟩ := ha
  obtain ⟨σ, rfl⟩ := promoteSpecs_all_poly s hs
  exact ⟨σ, rfl⟩

/-- Is a spec an unannotated (mono) member? -/
def RecSpec.isMono : RecSpec → Bool
  | .mono _ => true
  | .poly _ => false

/-- The group-local mono-membership predicate for a spec list: member `k` is mono iff
    `specs[k]` is `.mono`. -/
def specsMono (specs : List RecSpec) (k : Nat) : Bool :=
  match specs[k]? with
  | some s => RecSpec.isMono s
  | none => false

@[simp] theorem specsMono_getElem {specs : List RecSpec} {k : Nat} (hk : k < specs.length) :
    specsMono specs k = RecSpec.isMono (specs[k]'hk) := by
  simp [specsMono, List.getElem?_eq_getElem hk]

@[simp] theorem specsMono_of_ge {specs : List RecSpec} {k : Nat} (h : specs.length ≤ k) :
    specsMono specs k = false := by
  unfold specsMono
  have hnone : specs[k]? = none := List.getElem?_eq_none_iff.mpr h
  simp [hnone]

/-- Promote one spec: mono members to `some (promoteScheme G τ)`, poly members to their own
    scheme. The scheme-level face of `promoteSpecs`. -/
def promoteSpec (G : List Nat) : RecSpec → PolyTy
  | .mono τ => promoteScheme G τ
  | .poly σ => σ

@[simp] theorem promoteSpec_poly {G : List Nat} {σ : PolyTy} :
    promoteSpec G (.poly σ) = σ := rfl

@[simp] theorem promoteSpec_mono {G : List Nat} {τ : Ty} :
    promoteSpec G (.mono τ) = promoteScheme G τ := rfl

/-- `promoteSpecs G specs` maps to `.poly (promoteSpec G s)`, so its `rhsEntry` at any pool
    opening is just `promoteSpec G s` (a `.poly` entry ignores the pool). -/
theorem promoteSpecs_rhsEntry {G Xs : List Nat} {specs : List RecSpec} :
    (promoteSpecs G specs).map (RecSpec.rhsEntry G Xs) = specs.map (promoteSpec G) := by
  simp only [promoteSpecs, List.map_map]
  apply List.map_congr_left
  intro s _
  cases s with
  | mono τ => rfl
  | poly σ => rfl

/-! ## The type-level core

These two facts carry the whole encoding. They are one-liners, and their brevity is the point:
the full-pool promotion needs none of the filter-nodup / filter-disjointness bookkeeping that
`PolyTy.genGroup`'s analogues (`Ty.renameG_eq_genFilter`, `PolyTy.genGroup_renameG`) route
through — roughly half of `TypeOfElabHM.rewrap_hasScheme_mono`'s 79 lines. -/

/-- The promoted scheme is well-formed even when `τ` mentions only part of `G` (i.e. even with
    vacuous binders). The fact the whole encoding rests on. -/
theorem promoteScheme_wf {G : List Nat} {τ : Ty} (hτ : τ.IsLC) :
    (promoteScheme G τ).WF :=
  Ty.closeOver_preserves_bvars hτ

/-- The pivotal type-level fact. Opening the promoted scheme at `Xs` recovers exactly
    the shared pool opening the mono regime types members at. So `RecSpecs.PolyTyped`'s
    conclusion type for a promoted member is *literally* `RecSpecs.MonoTyped`'s conclusion
    type, with `Ys` playing the role of `Xs`.

    Immediate from `Ty.openVars_closeOver_rename` (`Core.lean:4161`), whose RHS is
    definitionally `Ty.renameG` (`Core.lean:2911`) — no filter round-trip. -/
theorem promoteScheme_openVars {G Xs : List Nat} {τ : Ty}
    (hτ : τ.IsLC) (hG : G.Nodup) (hlen : Xs.length = G.length)
    (hdisj : ∀ g ∈ G, g ∉ Xs) :
    (promoteScheme G τ).openVars Xs = Ty.renameG G Xs τ :=
  Ty.openVars_closeOver_rename hτ hG hlen hdisj

/-- `Forall₂` of two pointwise maps follows from the pointwise relation (local copy of InferW's
    private helper, needed because this module imports only `Core`). -/
private theorem forall₂_self_map {α β} {R : α → β → Prop} {f : α → β} :
    ∀ {l : List α}, (∀ x ∈ l, R x (f x)) → List.Forall₂ R l (l.map f)
  | [], _ => .nil
  | _ :: _, h =>
    .cons (h _ (List.mem_cons_self ..))
      (forall₂_self_map (fun x hx => h x (List.mem_cons_of_mem _ hx)))

/-- Opening a scheme body (bvars `< Xs.length`) with fresh *names* is an instantiation by those
    names-as-`fvar`s (local copy of InferW's `InstantiatesBy.openVars`). -/
theorem InstantiatesBy.openVars {Xs : List Nat} {n : Nat} {ty : Ty}
    (hty : ContainsBvarsUpTo n ty) (hn : n ≤ Xs.length) :
    InstantiatesBy (Xs.map (Ty.fvar ·)) ty (ty.openVars Xs) := by
  induction ty using Ty.rec_strong with
  | prim p => exact .prim
  | fvar m => exact .fvar
  | bvar i =>
    cases hty with
    | bvar hlt =>
      have hi : i < Xs.length := by omega
      simp only [Ty.openVars, Ty.instantiate, List.getElem?_eq_getElem hi, Option.elim_some]
      exact .bvar (by simp [List.getElem?_map, List.getElem?_eq_getElem hi])
  | arrow a b iha ihb => cases hty with | arrow ha hb => exact .arrow (iha ha) (ihb hb)
  | customTy nm tys ih =>
    cases hty with
    | customTy hball =>
      simp only [Ty.openVars, Ty.instantiate, TyList.instantiate_eq_map]
      exact .customTy (forall₂_self_map (fun t ht => ih t ht (hball t ht)))
  | bl lo hi e ih =>
    cases hty with
    | bl he =>
      simp only [Ty.openVars, Ty.instantiate]
      exact .bl (ih he)

/-- A promoted scheme instantiated at the fresh `Ys` recovers the `G ↦ Ys` renaming of its
    monotype — the transport's per-member instantiation fact. -/
theorem promoteScheme_instantiatesTo {G Ys : List Nat} {μ : Ty}
    (hμ : μ.IsLC) (hG : G.Nodup) (hlen : Ys.length = G.length)
    (hdisj : ∀ g ∈ G, g ∉ Ys) :
    (promoteScheme G μ).paramCount = (Ys.map Ty.fvar).length ∧
      (promoteScheme G μ).InstantiatesTo (Ys.map Ty.fvar) (Ty.renameG G Ys μ) := by
  constructor
  · simp [promoteScheme, hlen]
  · show InstantiatesBy (Ys.map Ty.fvar) (Ty.closeOver G μ) (Ty.renameG G Ys μ)
    rw [show Ty.renameG G Ys μ = (Ty.closeOver G μ).openVars Ys from
      (Ty.openVars_closeOver_rename hμ hG hlen hdisj).symm]
    exact InstantiatesBy.openVars (Ty.closeOver_preserves_bvars hμ) (Nat.le_of_eq hlen.symm)

/-! ## Concrete derivations (warm-up)

Mono and promoted derivations of the same programs, in the empty context `⟨[], []⟩`. They
establish the encoding on concrete terms before the transport lemmas generalise it.

In `.letRec anns bindings body`, `bindings` and `body` are in scope of the group's binders —
member `j` at index `j`. Inside `bindings[0] = .lambda none e`, index `0` is the lambda
parameter and index `1` is the group member. -/

/-- Pool and monotype for the smoke tests: `G = [0]`, `τ = fvar 0 → fvar 0`. -/
private def sG : List Nat := [0]
private def sτ : Ty := .arrow (.fvar 0) (.fvar 0)

/-- The promoted scheme, which should be `∀a. a → a`. -/
private def sσ : PolyTy := promoteScheme sG sτ

/-- Shape check on the promotion itself, before any typing. -/
example : sσ = ⟨1, .arrow (.bvar 0) (.bvar 0)⟩ := by
  rfl

/-- No group-internal reference, mono regime (as today): the member is typed monomorphically
    at `fvar 0 → fvar 0` inside the group and generalised for the body, which uses it at
    `int`. -/
theorem smoke_mono_noref :
    TypeOfElabHM ⟨[], []⟩
      (.letRec [none] [.lambda none (.var 0 [])] (.var 0 [.prim .int]))
      (.arrow (.prim .int) (.prim .int)) := by
  refine TypeOfElabHM.letRec (specs := [.mono sτ]) (G := sG) (L := [])
    ⟨rfl, rfl, ?_, ?_, ?_⟩ ?_ ?_ rfl ?_
  · show sG.Nodup
    simp [sG]
  · intro τ hτ
    simp only [List.mem_singleton, RecSpec.mono.injEq] at hτ
    subst hτ
    show sτ.IsLC
    exact .arrow .fvar .fvar
  · intro σ hσ
    simp only [List.mem_singleton] at hσ
    exact RecSpec.noConfusion hσ
  · intro Xs hfresh p hp τ hτ
    simp only [List.zip_cons_cons, List.zip_nil_right, List.mem_singleton] at hp
    subst hp
    injection hτ with hτ'
    subst hτ'
    obtain ⟨x, rfl⟩ : ∃ x, Xs = [x] := List.length_eq_one_iff.mp hfresh.length
    show TypeOfElabHM ⟨[PolyTy.mkTrivial (Ty.renameG sG [x] sτ)], []⟩
      (.lambda none (.var 0 [])) (Ty.renameG sG [x] sτ)
    have hren : Ty.renameG sG [x] sτ = .arrow (.fvar x) (.fvar x) := by
      simp [Ty.renameG, Ty.substFvars, Ty.substFvar, sG, sτ]
    rw [hren]
    refine TypeOfElabHM.lambda (paramTy := .fvar x) .fvar (fun T h => Option.noConfusion h) rfl ?_
    exact TypeOfElabHM.var (polyTy := PolyTy.mkTrivial (.fvar x)) (tyArgs := []) rfl
      ⟨rfl, by intro t ht; cases ht⟩ .fvar
  · intro Xs hfresh p hp σ hσ Ys hYs
    simp only [List.zip_cons_cons, List.zip_nil_right, List.mem_singleton] at hp
    subst hp
    exact RecSpec.noConfusion hσ
  · exact TypeOfElabHM.var (polyTy := sσ) (tyArgs := [.prim .int]) rfl
      ⟨rfl, by intro t ht; simp only [List.mem_singleton] at ht; subst ht; exact .prim⟩
      (.arrow (.bvar rfl) (.bvar rfl))

/-- The same program with the generalised scheme written into the `anns` slot. Same
    constructor, same shape, same body — only the slot is filled. -/
theorem smoke_promoted_noref :
    TypeOfElabHM ⟨[], []⟩
      (.letRec [some sσ] [.lambda none (.var 0 [])] (.var 0 [.prim .int]))
      (.arrow (.prim .int) (.prim .int)) := by
  refine TypeOfElabHM.letRec (specs := [.poly sσ]) (G := sG) (L := [])
    ⟨rfl, rfl, ?_, ?_, ?_⟩ ?_ ?_ rfl ?_
  · show sG.Nodup
    simp [sG]
  · intro τ hτ
    simp only [List.mem_singleton] at hτ
    exact RecSpec.noConfusion hτ
  · intro σ hσ
    simp only [List.mem_singleton, RecSpec.poly.injEq] at hσ
    subst hσ
    exact promoteScheme_wf (.arrow .fvar .fvar)
  · intro Xs hfresh p hp τ hτ
    simp only [List.zip_cons_cons, List.zip_nil_right, List.mem_singleton] at hp
    subst hp
    exact RecSpec.noConfusion hτ
  · intro Xs hfresh p hp σ hσ Ys hYs
    simp only [List.zip_cons_cons, List.zip_nil_right, List.mem_singleton] at hp
    subst hp
    injection hσ with hσσ
    subst hσσ
    obtain ⟨y, rfl⟩ : ∃ y, Ys = [y] := List.length_eq_one_iff.mp hYs.length
    show TypeOfElabHM ⟨[sσ], []⟩ (.lambda none (.var 0 [])) ((Ty.fvar y).arrow (.fvar y))
    refine TypeOfElabHM.lambda (paramTy := .fvar y) .fvar (fun T h => Option.noConfusion h) rfl ?_
    exact TypeOfElabHM.var (polyTy := PolyTy.mkTrivial (.fvar y)) (tyArgs := []) rfl
      ⟨rfl, by intro t ht; cases ht⟩ .fvar
  · exact TypeOfElabHM.var (polyTy := sσ) (tyArgs := [.prim .int]) rfl
      ⟨rfl, by intro t ht; simp only [List.mem_singleton] at ht; subst ht; exact .prim⟩
      (.arrow (.bvar rfl) (.bvar rfl))

/-- Self-reference, mono regime: `λx. self x`. Inside the binding, index `1` is the group
    member; in the mono regime it is bound at `mkTrivial`, so its use carries `tyArgs = []`. -/
theorem smoke_mono_selfref :
    TypeOfElabHM ⟨[], []⟩
      (.letRec [none] [.lambda none (.app (.var 1 []) (.var 0 []))] (.var 0 [.prim .int]))
      (.arrow (.prim .int) (.prim .int)) := by
  refine TypeOfElabHM.letRec (specs := [.mono sτ]) (G := sG) (L := [])
    ⟨rfl, rfl, ?_, ?_, ?_⟩ ?_ ?_ rfl ?_
  · show sG.Nodup
    simp [sG]
  · intro τ hτ
    simp only [List.mem_singleton, RecSpec.mono.injEq] at hτ
    subst hτ
    show sτ.IsLC
    exact .arrow .fvar .fvar
  · intro σ hσ
    simp only [List.mem_singleton] at hσ
    exact RecSpec.noConfusion hσ
  · intro Xs hfresh p hp τ hτ
    simp only [List.zip_cons_cons, List.zip_nil_right, List.mem_singleton] at hp
    subst hp
    injection hτ with hτ'
    subst hτ'
    obtain ⟨x, rfl⟩ : ∃ x, Xs = [x] := List.length_eq_one_iff.mp hfresh.length
    show TypeOfElabHM ⟨[PolyTy.mkTrivial (Ty.renameG sG [x] sτ)], []⟩
      (.lambda none (.app (.var 1 []) (.var 0 []))) (Ty.renameG sG [x] sτ)
    have hren : Ty.renameG sG [x] sτ = .arrow (.fvar x) (.fvar x) := by
      simp [Ty.renameG, Ty.substFvars, Ty.substFvar, sG, sτ]
    rw [hren]
    refine TypeOfElabHM.lambda (paramTy := .fvar x) .fvar (fun T h => Option.noConfusion h) rfl ?_
    refine TypeOfElabHM.app (argTy := .fvar x) ?_ ?_
    · exact TypeOfElabHM.var
        (polyTy := PolyTy.mkTrivial ((Ty.fvar x).arrow (.fvar x))) (tyArgs := []) rfl
        ⟨rfl, by intro t ht; cases ht⟩ (.arrow .fvar .fvar)
    · exact TypeOfElabHM.var (polyTy := PolyTy.mkTrivial (.fvar x)) (tyArgs := []) rfl
        ⟨rfl, by intro t ht; cases ht⟩ .fvar
  · intro Xs hfresh p hp σ hσ Ys hYs
    simp only [List.zip_cons_cons, List.zip_nil_right, List.mem_singleton] at hp
    subst hp
    exact RecSpec.noConfusion hσ
  · exact TypeOfElabHM.var (polyTy := sσ) (tyArgs := [.prim .int]) rfl
      ⟨rfl, by intro t ht; simp only [List.mem_singleton] at ht; subst ht; exact .prim⟩
      (.arrow (.bvar rfl) (.bvar rfl))

/-- Self-reference, promoted: the same program, scheme in the slot, and the self-reference
    retargeted from `.var 1 []` to `.var 1 [.bvar 0]` — the member instantiating its own `1`-ary
    scheme at its own pool binder (`Ty.bvarRangeFrom 0 1 = [.bvar 0]`). This is the smallest
    derivation that exercises the retarget, and the make-or-break case for the encoding. -/
theorem smoke_promoted_selfref :
    TypeOfElabHM ⟨[], []⟩
      (.letRec [some sσ] [.lambda none (.app (.var 1 [.bvar 0]) (.var 0 []))]
        (.var 0 [.prim .int]))
      (.arrow (.prim .int) (.prim .int)) := by
  refine TypeOfElabHM.letRec (specs := [.poly sσ]) (G := sG) (L := [])
    ⟨rfl, rfl, ?_, ?_, ?_⟩ ?_ ?_ rfl ?_
  · show sG.Nodup
    simp [sG]
  · intro τ hτ
    simp only [List.mem_singleton] at hτ
    exact RecSpec.noConfusion hτ
  · intro σ hσ
    simp only [List.mem_singleton, RecSpec.poly.injEq] at hσ
    subst hσ
    exact promoteScheme_wf (.arrow .fvar .fvar)
  · intro Xs hfresh p hp τ hτ
    simp only [List.zip_cons_cons, List.zip_nil_right, List.mem_singleton] at hp
    subst hp
    exact RecSpec.noConfusion hτ
  · intro Xs hfresh p hp σ hσ Ys hYs
    simp only [List.zip_cons_cons, List.zip_nil_right, List.mem_singleton] at hp
    subst hp
    injection hσ with hσσ
    subst hσσ
    obtain ⟨y, rfl⟩ : ∃ y, Ys = [y] := List.length_eq_one_iff.mp hYs.length
    show TypeOfElabHM ⟨[sσ], []⟩
      (.lambda none (.app (.var 1 [.fvar y]) (.var 0 []))) ((Ty.fvar y).arrow (.fvar y))
    refine TypeOfElabHM.lambda (paramTy := .fvar y) .fvar (fun T h => Option.noConfusion h) rfl ?_
    refine TypeOfElabHM.app (argTy := .fvar y) ?_ ?_
    · exact TypeOfElabHM.var (polyTy := sσ) (tyArgs := [.fvar y]) rfl
        ⟨rfl, by intro t ht; simp only [List.mem_singleton] at ht; subst ht; exact .fvar⟩
        (.arrow (.bvar rfl) (.bvar rfl))
    · exact TypeOfElabHM.var (polyTy := PolyTy.mkTrivial (.fvar y)) (tyArgs := []) rfl
        ⟨rfl, by intro t ht; cases ht⟩ .fvar
  · exact TypeOfElabHM.var (polyTy := sσ) (tyArgs := [.prim .int]) rfl
      ⟨rfl, by intro t ht; simp only [List.mem_singleton] at ht; subst ht; exact .prim⟩
      (.arrow (.bvar rfl) (.bvar rfl))

/-! ## Mutual recursion: the cases the warm-ups miss

The warm-ups use `n = 1` and a monotype that mentions **all** of `G`, so `Ty.genFilter G τ = G`
and the full-pool choice is indistinguishable from the filtered one. They also have no
siblings, so the mechanism that motivates the full pool — uniform arity, so that a *sibling*
reference `.var j (bvarRange |G|)` lines up — is never exercised. These two do exercise it.
Pool `G₂ = [0, 1]` throughout.

- `mutual_*` — genuine mutual reference, both members at `τA = fvar 0 → fvar 0`. Neither
  mentions pool var `1`, so each promoted scheme carries a **vacuous** second binder. Under
  `genFilter` both would be arity 1; under the full pool both are arity 2.
- `mutual_mixed_*` — members at `τA` and `τB = fvar 1 → fvar 1`. Under the full pool these are
  `⟨2, bvar 0 → bvar 0⟩` and `⟨2, bvar 1 → bvar 1⟩` — same arity, **different binder
  positions**, each vacuous in the other's slot. Under `genFilter` both would collapse to
  `⟨1, bvar 0 → bvar 0⟩` and member 1's index would *shift*. This is the index-alignment test.

Consequence to carry into the implementation: promotion changes the **body**'s `tyArgs` arity
too (the mono body sees `PolyTy.genGroup G τ` at filtered arity; the promoted body sees the
full-pool scheme), so the retarget applies to the body as well as to the bindings.

De Bruijn reminder: with `n = 2`, at group level member `j` is at index `j`; under one lambda,
member 0 is at index 1 and member 1 at index 2. -/

private def G₂ : List Nat := [0, 1]
private def τA : Ty := .arrow (.fvar 0) (.fvar 0)
private def τB : Ty := .arrow (.fvar 1) (.fvar 1)

private def σA : PolyTy := promoteScheme G₂ τA
private def σB : PolyTy := promoteScheme G₂ τB

/-- Shape checks: `σA` is vacuous in its second binder, `σB` in its first. -/
example : σA = ⟨2, .arrow (.bvar 0) (.bvar 0)⟩ := by rfl
example : σB = ⟨2, .arrow (.bvar 1) (.bvar 1)⟩ := by rfl

/-- Confirms the discriminator is real: under `genFilter` these two schemes would collapse to
    the *same* arity-1 scheme, losing `σB`'s binder position. -/
example : PolyTy.genGroup G₂ τA = ⟨1, .arrow (.bvar 0) (.bvar 0)⟩ ∧
          PolyTy.genGroup G₂ τB = ⟨1, .arrow (.bvar 0) (.bvar 0)⟩ := by exact ⟨rfl, rfl⟩

/-- Mutually recursive pair, both at `τA`, mono regime; body uses member 0 at `int`. -/
theorem mutual_mono :
    TypeOfElabHM ⟨[], []⟩
      (.letRec [none, none]
        [.lambda none (.app (.var 2 []) (.var 0 [])),
         .lambda none (.app (.var 1 []) (.var 0 []))]
        (.var 0 [.prim .int]))
      (.arrow (.prim .int) (.prim .int)) := by
  refine TypeOfElabHM.letRec (specs := [.mono τA, .mono τA]) (G := G₂) (L := G₂)
    ⟨rfl, rfl, ?_, ?_, ?_⟩ ?_ ?_ rfl ?_
  · show G₂.Nodup
    simp [G₂]
  · intro τ hτ
    simp only [List.mem_cons, List.not_mem_nil, or_false, RecSpec.mono.injEq] at hτ
    rcases hτ with hτ | hτ <;> subst hτ <;> exact .arrow .fvar .fvar
  · intro σ hσ
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hσ
    rcases hσ with hσ | hσ <;> exact RecSpec.noConfusion hσ
  · intro Xs hfresh p hp τ hτ
    obtain ⟨x0, x1, rfl⟩ := List.length_eq_two.mp hfresh.length
    have hx0 : x0 ∉ G₂ := hfresh.avoid x0 List.mem_cons_self
    have hx0' : x0 ≠ 1 := by simp [G₂] at hx0; exact hx0.2
    have hren : Ty.renameG G₂ [x0, x1] τA = .arrow (.fvar x0) (.fvar x0) := by
      simp [Ty.renameG, Ty.substFvars, Ty.substFvar, G₂, τA, hx0']
    simp only [List.zip_cons_cons, List.zip_nil_right, List.mem_cons, List.not_mem_nil,
      or_false] at hp
    rcases hp with rfl | rfl
    · injection hτ with hτ'
      subst hτ'
      show TypeOfElabHM
          ⟨[PolyTy.mkTrivial (Ty.renameG G₂ [x0, x1] τA),
            PolyTy.mkTrivial (Ty.renameG G₂ [x0, x1] τA)], []⟩
          (.lambda none (.app (.var 2 []) (.var 0 []))) (Ty.renameG G₂ [x0, x1] τA)
      rw [hren]
      refine TypeOfElabHM.lambda (paramTy := .fvar x0) .fvar (fun T h => Option.noConfusion h) rfl ?_
      refine TypeOfElabHM.app (argTy := .fvar x0) ?_ ?_
      · exact TypeOfElabHM.var
          (polyTy := PolyTy.mkTrivial ((Ty.fvar x0).arrow (.fvar x0))) (tyArgs := []) rfl
          ⟨rfl, by intro t ht; cases ht⟩ (.arrow .fvar .fvar)
      · exact TypeOfElabHM.var (polyTy := PolyTy.mkTrivial (.fvar x0)) (tyArgs := []) rfl
          ⟨rfl, by intro t ht; cases ht⟩ .fvar
    · injection hτ with hτ'
      subst hτ'
      show TypeOfElabHM
          ⟨[PolyTy.mkTrivial (Ty.renameG G₂ [x0, x1] τA),
            PolyTy.mkTrivial (Ty.renameG G₂ [x0, x1] τA)], []⟩
          (.lambda none (.app (.var 1 []) (.var 0 []))) (Ty.renameG G₂ [x0, x1] τA)
      rw [hren]
      refine TypeOfElabHM.lambda (paramTy := .fvar x0) .fvar (fun T h => Option.noConfusion h) rfl ?_
      refine TypeOfElabHM.app (argTy := .fvar x0) ?_ ?_
      · exact TypeOfElabHM.var
          (polyTy := PolyTy.mkTrivial ((Ty.fvar x0).arrow (.fvar x0))) (tyArgs := []) rfl
          ⟨rfl, by intro t ht; cases ht⟩ (.arrow .fvar .fvar)
      · exact TypeOfElabHM.var (polyTy := PolyTy.mkTrivial (.fvar x0)) (tyArgs := []) rfl
          ⟨rfl, by intro t ht; cases ht⟩ .fvar
  · intro Xs hfresh p hp σ hσ
    simp only [List.zip_cons_cons, List.zip_nil_right, List.mem_cons, List.not_mem_nil,
      or_false] at hp
    rcases hp with rfl | rfl <;> exact RecSpec.noConfusion hσ
  · exact TypeOfElabHM.var (polyTy := PolyTy.genGroup G₂ τA) (tyArgs := [.prim .int]) rfl
      ⟨rfl, by intro t ht; simp only [List.mem_singleton] at ht; subst ht; exact .prim⟩
      (.arrow (.bvar rfl) (.bvar rfl))

/-- Same group, promoted: schemes in the slots, sibling references retargeted to
    `[.bvar 0, .bvar 1]`, body at the full-pool arity. Exercises: mutual sibling reference, a
    vacuous binder, uniform arity 2, and a 2-element retargeted `tyArgs`. -/
theorem mutual_promoted :
    TypeOfElabHM ⟨[], []⟩
      (.letRec [some σA, some σA]
        [.lambda none (.app (.var 2 [.bvar 0, .bvar 1]) (.var 0 [])),
         .lambda none (.app (.var 1 [.bvar 0, .bvar 1]) (.var 0 []))]
        (.var 0 [.prim .int, .prim .int]))
      (.arrow (.prim .int) (.prim .int)) := by
  refine TypeOfElabHM.letRec (specs := [.poly σA, .poly σA]) (G := G₂) (L := [])
    ⟨rfl, rfl, ?_, ?_, ?_⟩ ?_ ?_ rfl ?_
  · show G₂.Nodup
    simp [G₂]
  · intro τ hτ
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hτ
    rcases hτ with hτ | hτ <;> exact RecSpec.noConfusion hτ
  · intro σ hσ
    simp only [List.mem_cons, List.not_mem_nil, or_false, RecSpec.poly.injEq] at hσ
    rcases hσ with hσ | hσ <;> subst hσ <;> exact promoteScheme_wf (.arrow .fvar .fvar)
  · intro Xs hfresh p hp τ hτ
    simp only [List.zip_cons_cons, List.zip_nil_right, List.mem_cons, List.not_mem_nil,
      or_false] at hp
    rcases hp with rfl | rfl <;> exact RecSpec.noConfusion hτ
  · intro Xs hfresh p hp σ hσ Ys hYs
    simp only [List.zip_cons_cons, List.zip_nil_right, List.mem_cons, List.not_mem_nil,
      or_false] at hp
    rcases hp with rfl | rfl
    · injection hσ with hσσ
      subst hσσ
      obtain ⟨y0, y1, rfl⟩ := List.length_eq_two.mp hYs.length
      show TypeOfElabHM ⟨[σA, σA], []⟩
        (.lambda none (.app (.var 2 [.fvar y0, .fvar y1]) (.var 0 [])))
        ((Ty.fvar y0).arrow (.fvar y0))
      refine TypeOfElabHM.lambda (paramTy := .fvar y0) .fvar (fun T h => Option.noConfusion h) rfl ?_
      refine TypeOfElabHM.app (argTy := .fvar y0) ?_ ?_
      · exact TypeOfElabHM.var (polyTy := σA) (tyArgs := [.fvar y0, .fvar y1]) rfl
          ⟨rfl, by intro t ht; simp only [List.mem_cons, List.not_mem_nil, or_false] at ht; rcases ht with rfl | rfl <;> exact .fvar⟩
          (.arrow (.bvar rfl) (.bvar rfl))
      · exact TypeOfElabHM.var (polyTy := PolyTy.mkTrivial (.fvar y0)) (tyArgs := []) rfl
          ⟨rfl, by intro t ht; cases ht⟩ .fvar
    · injection hσ with hσσ
      subst hσσ
      obtain ⟨y0, y1, rfl⟩ := List.length_eq_two.mp hYs.length
      show TypeOfElabHM ⟨[σA, σA], []⟩
        (.lambda none (.app (.var 1 [.fvar y0, .fvar y1]) (.var 0 [])))
        ((Ty.fvar y0).arrow (.fvar y0))
      refine TypeOfElabHM.lambda (paramTy := .fvar y0) .fvar (fun T h => Option.noConfusion h) rfl ?_
      refine TypeOfElabHM.app (argTy := .fvar y0) ?_ ?_
      · exact TypeOfElabHM.var (polyTy := σA) (tyArgs := [.fvar y0, .fvar y1]) rfl
          ⟨rfl, by intro t ht; simp only [List.mem_cons, List.not_mem_nil, or_false] at ht; rcases ht with rfl | rfl <;> exact .fvar⟩
          (.arrow (.bvar rfl) (.bvar rfl))
      · exact TypeOfElabHM.var (polyTy := PolyTy.mkTrivial (.fvar y0)) (tyArgs := []) rfl
          ⟨rfl, by intro t ht; cases ht⟩ .fvar
  · exact TypeOfElabHM.var (polyTy := σA) (tyArgs := [.prim .int, .prim .int]) rfl
      ⟨rfl, by intro t ht; simp only [List.mem_cons, List.not_mem_nil, or_false] at ht; rcases ht with rfl | rfl <;> exact .prim⟩
      (.arrow (.bvar rfl) (.bvar rfl))

/-- Members at `τA` and `τB`, mono regime — different pool usage, self-recursive each. -/
theorem mutual_mixed_mono :
    TypeOfElabHM ⟨[], []⟩
      (.letRec [none, none]
        [.lambda none (.app (.var 1 []) (.var 0 [])),
         .lambda none (.app (.var 2 []) (.var 0 []))]
        (.var 0 [.prim .int]))
      (.arrow (.prim .int) (.prim .int)) := by
  refine TypeOfElabHM.letRec (specs := [.mono τA, .mono τB]) (G := G₂) (L := G₂)
    ⟨rfl, rfl, ?_, ?_, ?_⟩ ?_ ?_ rfl ?_
  · show G₂.Nodup
    simp [G₂]
  · intro τ hτ
    simp only [List.mem_cons, List.not_mem_nil, or_false, RecSpec.mono.injEq] at hτ
    rcases hτ with hτ | hτ <;> subst hτ <;> exact .arrow .fvar .fvar
  · intro σ hσ
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hσ
    rcases hσ with hσ | hσ <;> exact RecSpec.noConfusion hσ
  · intro Xs hfresh p hp τ hτ
    obtain ⟨x0, x1, rfl⟩ := List.length_eq_two.mp hfresh.length
    have hx0 : x0 ∉ G₂ := hfresh.avoid x0 List.mem_cons_self
    have hx0' : x0 ≠ 1 := by simp [G₂] at hx0; exact hx0.2
    have hrenA : Ty.renameG G₂ [x0, x1] τA = .arrow (.fvar x0) (.fvar x0) := by
      simp [Ty.renameG, Ty.substFvars, Ty.substFvar, G₂, τA, hx0']
    have hrenB : Ty.renameG G₂ [x0, x1] τB = .arrow (.fvar x1) (.fvar x1) := by
      simp [Ty.renameG, Ty.substFvars, Ty.substFvar, G₂, τB]
    simp only [List.zip_cons_cons, List.zip_nil_right, List.mem_cons, List.not_mem_nil,
      or_false] at hp
    rcases hp with rfl | rfl
    · injection hτ with hτ'
      subst hτ'
      show TypeOfElabHM
          ⟨[PolyTy.mkTrivial (Ty.renameG G₂ [x0, x1] τA),
            PolyTy.mkTrivial (Ty.renameG G₂ [x0, x1] τB)], []⟩
          (.lambda none (.app (.var 1 []) (.var 0 []))) (Ty.renameG G₂ [x0, x1] τA)
      rw [hrenA, hrenB]
      refine TypeOfElabHM.lambda (paramTy := .fvar x0) .fvar (fun T h => Option.noConfusion h) rfl ?_
      refine TypeOfElabHM.app (argTy := .fvar x0) ?_ ?_
      · exact TypeOfElabHM.var
          (polyTy := PolyTy.mkTrivial ((Ty.fvar x0).arrow (.fvar x0))) (tyArgs := []) rfl
          ⟨rfl, by intro t ht; cases ht⟩ (.arrow .fvar .fvar)
      · exact TypeOfElabHM.var (polyTy := PolyTy.mkTrivial (.fvar x0)) (tyArgs := []) rfl
          ⟨rfl, by intro t ht; cases ht⟩ .fvar
    · injection hτ with hτ'
      subst hτ'
      show TypeOfElabHM
          ⟨[PolyTy.mkTrivial (Ty.renameG G₂ [x0, x1] τA),
            PolyTy.mkTrivial (Ty.renameG G₂ [x0, x1] τB)], []⟩
          (.lambda none (.app (.var 2 []) (.var 0 []))) (Ty.renameG G₂ [x0, x1] τB)
      rw [hrenA, hrenB]
      refine TypeOfElabHM.lambda (paramTy := .fvar x1) .fvar (fun T h => Option.noConfusion h) rfl ?_
      refine TypeOfElabHM.app (argTy := .fvar x1) ?_ ?_
      · exact TypeOfElabHM.var
          (polyTy := PolyTy.mkTrivial ((Ty.fvar x1).arrow (.fvar x1))) (tyArgs := []) rfl
          ⟨rfl, by intro t ht; cases ht⟩ (.arrow .fvar .fvar)
      · exact TypeOfElabHM.var (polyTy := PolyTy.mkTrivial (.fvar x1)) (tyArgs := []) rfl
          ⟨rfl, by intro t ht; cases ht⟩ .fvar
  · intro Xs hfresh p hp σ hσ
    simp only [List.zip_cons_cons, List.zip_nil_right, List.mem_cons, List.not_mem_nil,
      or_false] at hp
    rcases hp with rfl | rfl <;> exact RecSpec.noConfusion hσ
  · exact TypeOfElabHM.var (polyTy := PolyTy.genGroup G₂ τA) (tyArgs := [.prim .int]) rfl
      ⟨rfl, by intro t ht; simp only [List.mem_singleton] at ht; subst ht; exact .prim⟩
      (.arrow (.bvar rfl) (.bvar rfl))

/-- The index-alignment test, promoted: `σA` and `σB` are vacuous in *opposite* binder slots
    but share arity 2, so the single uniform retarget `[.bvar 0, .bvar 1]` must work for both.
    Under `genFilter` it could not: the two schemes would have different binder positions at
    the same index. -/
theorem mutual_mixed_promoted :
    TypeOfElabHM ⟨[], []⟩
      (.letRec [some σA, some σB]
        [.lambda none (.app (.var 1 [.bvar 0, .bvar 1]) (.var 0 [])),
         .lambda none (.app (.var 2 [.bvar 0, .bvar 1]) (.var 0 []))]
        (.var 0 [.prim .int, .prim .int]))
      (.arrow (.prim .int) (.prim .int)) := by
  refine TypeOfElabHM.letRec (specs := [.poly σA, .poly σB]) (G := G₂) (L := [])
    ⟨rfl, rfl, ?_, ?_, ?_⟩ ?_ ?_ rfl ?_
  · show G₂.Nodup
    simp [G₂]
  · intro τ hτ
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hτ
    rcases hτ with hτ | hτ <;> exact RecSpec.noConfusion hτ
  · intro σ hσ
    simp only [List.mem_cons, List.not_mem_nil, or_false, RecSpec.poly.injEq] at hσ
    rcases hσ with hσ | hσ <;> subst hσ <;> exact promoteScheme_wf (.arrow .fvar .fvar)
  · intro Xs hfresh p hp τ hτ
    simp only [List.zip_cons_cons, List.zip_nil_right, List.mem_cons, List.not_mem_nil,
      or_false] at hp
    rcases hp with rfl | rfl <;> exact RecSpec.noConfusion hτ
  · intro Xs hfresh p hp σ hσ Ys hYs
    simp only [List.zip_cons_cons, List.zip_nil_right, List.mem_cons, List.not_mem_nil,
      or_false] at hp
    rcases hp with rfl | rfl
    · injection hσ with hσσ
      subst hσσ
      obtain ⟨y0, y1, rfl⟩ := List.length_eq_two.mp hYs.length
      show TypeOfElabHM ⟨[σA, σB], []⟩
        (.lambda none (.app (.var 1 [.fvar y0, .fvar y1]) (.var 0 [])))
        ((Ty.fvar y0).arrow (.fvar y0))
      refine TypeOfElabHM.lambda (paramTy := .fvar y0) .fvar (fun T h => Option.noConfusion h) rfl ?_
      refine TypeOfElabHM.app (argTy := .fvar y0) ?_ ?_
      · exact TypeOfElabHM.var (polyTy := σA) (tyArgs := [.fvar y0, .fvar y1]) rfl
          ⟨rfl, by intro t ht; simp only [List.mem_cons, List.not_mem_nil, or_false] at ht; rcases ht with rfl | rfl <;> exact .fvar⟩
          (.arrow (.bvar rfl) (.bvar rfl))
      · exact TypeOfElabHM.var (polyTy := PolyTy.mkTrivial (.fvar y0)) (tyArgs := []) rfl
          ⟨rfl, by intro t ht; cases ht⟩ .fvar
    · injection hσ with hσσ
      subst hσσ
      obtain ⟨y0, y1, rfl⟩ := List.length_eq_two.mp hYs.length
      show TypeOfElabHM ⟨[σA, σB], []⟩
        (.lambda none (.app (.var 2 [.fvar y0, .fvar y1]) (.var 0 [])))
        ((Ty.fvar y1).arrow (.fvar y1))
      refine TypeOfElabHM.lambda (paramTy := .fvar y1) .fvar (fun T h => Option.noConfusion h) rfl ?_
      refine TypeOfElabHM.app (argTy := .fvar y1) ?_ ?_
      · exact TypeOfElabHM.var (polyTy := σB) (tyArgs := [.fvar y0, .fvar y1]) rfl
          ⟨rfl, by intro t ht; simp only [List.mem_cons, List.not_mem_nil, or_false] at ht; rcases ht with rfl | rfl <;> exact .fvar⟩
          (.arrow (.bvar rfl) (.bvar rfl))
      · exact TypeOfElabHM.var (polyTy := PolyTy.mkTrivial (.fvar y1)) (tyArgs := []) rfl
          ⟨rfl, by intro t ht; cases ht⟩ .fvar
  · exact TypeOfElabHM.var (polyTy := σA) (tyArgs := [.prim .int, .prim .int]) rfl
      ⟨rfl, by intro t ht; simp only [List.mem_cons, List.not_mem_nil, or_false] at ht; rcases ht with rfl | rfl <;> exact .prim⟩
      (.arrow (.bvar rfl) (.bvar rfl))

/-! ## The transport

The concrete derivations above exhibit mono and promoted derivations *independently*. This
section proves the general claim they do not establish: that a mono-regime derivation can be
**converted** into a promoted one (and back).

### Why this is new work

`TypeOfHM.weaken_schemes` (`InferW.lean:15487`) already swaps a whole env prefix for more
general schemes — but on `TypeOfHM`, whose `var` rule instantiates *existentially*, so the term
is untouched. `TypeOfElabHM.var` stores `tyArgs` and pins their arity
(`Ty.AreLC polyTy.paramCount tyArgs`), so replacing `PolyTy.mkTrivial τ` (arity 0, `tyArgs = []`)
with a scheme of arity `|G|` **forces** the term to change. Nothing in the codebase does that
today, because `letRecElab` sidesteps it by hoisting the Λ outside instead.

### Scope

The transport is stated on **opened** terms: `Vs` are concrete `Ty`s (the pool opening as
`fvar`s), not `bvar`s. That removes type-binder depth tracking from the retarget entirely —
`Vs` is depth-independent — leaving only term-binder depth `b`. The stored-vs-opened commute
(`(retargetStored … e).openTyVars Ys = retargetVars … (e.openTyVars Ys)`) is a separate lemma
at the end of the file. -/

mutual

/-- Retarget group-variable uses in an **opened** term: a use of a *mono* group binder
    (`mono k` true for group-local index `k`) at term-depth `b` gets `tyArgs := Vs`
    instead of `[]`; poly binders are left untouched. `mono` is defined on group-local
    indices `[0, n)` and is `false` outside. -/
def retargetVars (mono : Nat → Bool) (Vs : List Ty) (b : Nat) : Expr → Expr
  | .primLit p          => .primLit p
  | .primBinOp op       => .primBinOp op
  | .lambda ann body    => .lambda ann (retargetVars mono Vs (b + 1) body)
  | .app f arg          => .app (retargetVars mono Vs b f) (retargetVars mono Vs b arg)
  | .letIn ann rhs body =>
      .letIn ann (retargetVars mono Vs b rhs) (retargetVars mono Vs (b + 1) body)
  | .var i tyArgs       => if b ≤ i ∧ mono (i - b) then .var i Vs else .var i tyArgs
  | .ctor c             => .ctor c
  | .match_ scrut brs   =>
      .match_ (retargetVars mono Vs b scrut) (retargetBranches mono Vs b brs)
  | .letRec anns bs body =>
      .letRec anns (retargetGroup mono Vs (b + bs.length) bs)
        (retargetVars mono Vs (b + bs.length) body)

def retargetBranches (mono : Nat → Bool) (Vs : List Ty) (b : Nat) :
    List (MatchPattern × Expr) → List (MatchPattern × Expr)
  | []                  => []
  | (pat, body) :: rest =>
      (pat, retargetVars mono Vs (b + pat.bindCount) body) :: retargetBranches mono Vs b rest

def retargetGroup (mono : Nat → Bool) (Vs : List Ty) (b : Nat) : List Expr → List Expr
  | []        => []
  | e :: rest => retargetVars mono Vs b e :: retargetGroup mono Vs b rest

end

/-! ### Retarget bookkeeping -/

/-- Instantiating a type with the empty argument list recovers the type itself
    (impossible for any body containing a `bvar`). -/
theorem InstantiatesBy_empty_eq {ty τ : Ty} (h : InstantiatesBy [] ty τ) : τ = ty := by
  induction ty using Ty.rec_strong generalizing τ with
  | prim p => cases h; rfl
  | fvar n => cases h; rfl
  | bvar i => cases h with | bvar hlook => cases hlook
  | arrow a b iha ihb =>
      cases h with
      | arrow ha hb => rw [iha ha, ihb hb]
  | customTy nm tys ih =>
      cases h with
      | customTy hbrs =>
          congr
          apply List.ext_getElem
          · exact hbrs.length_eq.symm
          · intro i hiInst hiTy
            have hrel := List.Forall₂.get hbrs hiTy hiInst
            exact ih (tys[i]) (List.getElem_mem hiTy) hrel
  | bl lo hi e ih =>
      cases h with
      | bl hb => rw [ih hb]

/-- Opening an LC type is the identity: LC types have no `bvar`s to open. -/
theorem List.map_openVarsFrom_lc {d : Nat} {Xs : List Nat} {Vs : List Ty}
    (hVsLC : ∀ V ∈ Vs, V.IsLC) : Vs.map (Ty.openVarsFrom d Xs) = Vs := by
  have h : ∀ V ∈ Vs, Ty.openVarsFrom d Xs V = V := fun V hV =>
    Ty.openVarsFrom_eq_self_of_bvars (d := d) (Xs := Xs) (t := V)
      (ContainsBvarsUpTo.mono (Nat.zero_le d) (hVsLC V hV))
  simpa using List.map_congr_left h

/-- `retargetGroup` preserves lengths. -/
theorem retargetGroup_length {mono : Nat → Bool} {b : Nat} {Vs : List Ty} (bs : List Expr) :
    (retargetGroup mono Vs b bs).length = bs.length := by
  induction bs with
  | nil => rfl
  | cons e tl ih => simp only [retargetGroup, List.length_cons, ih]

/-- Retargeting a term commutes with opening its scoped type variables: the
    retarget only replaces the `tyArgs` of group-window `var`s with the LC `Vs`,
    and opening only touches `bvar`s, which `Vs` does not contain. -/
theorem retargetVars_openTyVarsAux {mono : Nat → Bool} {b d : Nat} {Vs : List Ty} {Xs : List Nat} {e : Expr}
    (hVsLC : ∀ V ∈ Vs, V.IsLC) :
    (retargetVars mono Vs b e).openTyVarsAux d Xs = retargetVars mono Vs b (e.openTyVarsAux d Xs) := by
  induction e using Expr.rec_strong generalizing b d with
  | primLit p => rfl
  | primBinOp op => rfl
  | ctor nm => rfl
  | var i tyArgs =>
      by_cases hwin : b ≤ i ∧ mono (i - b)
      · simp [retargetVars, Expr.openTyVarsAux, hwin, List.map_openVarsFrom_lc hVsLC]
      · simp [retargetVars, Expr.openTyVarsAux, hwin]
  | lambda ann body ih =>
      simp only [retargetVars, Expr.openTyVarsAux, ih (b := b + 1) (d := d)]
  | app f arg ihf iharg =>
      simp only [retargetVars, Expr.openTyVarsAux, ihf (b := b) (d := d), iharg (b := b) (d := d)]
  | letIn ann rhs body ihr ihb =>
      cases ann with
      | none =>
          simp only [retargetVars, Expr.openTyVarsAux, ihr (b := b) (d := d), ihb (b := b + 1) (d := d)]
      | some σ =>
          simp only [retargetVars, Expr.openTyVarsAux, ihr (b := b) (d := d + σ.paramCount), ihb (b := b + 1) (d := d)]
  | match_ scrut brs ihscrut ihbrs =>
      simp only [retargetVars, Expr.openTyVarsAux, ihscrut (b := b) (d := d)]
      have hbrs : BranchList.openTyVarsAux d Xs (retargetBranches mono Vs b brs)
          = retargetBranches mono Vs b (BranchList.openTyVarsAux d Xs brs) := by
        induction brs with
        | nil => rfl
        | cons br rest ih =>
            cases br with
            | mk pat body =>
                have hhead : (retargetVars mono Vs (b + pat.bindCount) body).openTyVarsAux d Xs
                    = retargetVars mono Vs (b + pat.bindCount) (body.openTyVarsAux d Xs) :=
                  ihbrs pat body (List.mem_cons_self ..) (b := b + pat.bindCount) (d := d)
                simp only [retargetBranches, BranchList.openTyVarsAux]
                rw [hhead]
                congr 1
                exact ih (fun pat' e' he' => ihbrs pat' e' (List.mem_cons_of_mem _ he'))
      rw [hbrs]
  | letRec anns bs body ihbs ihbody =>
      simp only [retargetVars, Expr.openTyVarsAux, ihbody (b := b + bs.length) (d := d)]
      have hbs' : ∀ (D : Nat) (anns : List (Option PolyTy)),
          RecGroup.openTyVarsAux d Xs anns (retargetGroup mono Vs D bs)
            = retargetGroup mono Vs D (RecGroup.openTyVarsAux d Xs anns bs) := by
        intro D
        induction bs generalizing anns with
        | nil => intro anns; rfl
        | cons e tl ih =>
            intro anns
            cases anns with
            | nil =>
                simp only [retargetGroup, RecGroup.openTyVarsAux]
                rw [ihbs e (List.mem_cons_self ..) (b := D) (d := d)]
                congr 1
                exact ih [] (fun e' he' => ihbs e' (List.mem_cons_of_mem _ he')) []
            | cons a as =>
                simp only [retargetGroup, RecGroup.openTyVarsAux]
                rw [ihbs e (List.mem_cons_self ..) (b := D) (d := d + RecAnn.params a)]
                congr 1
                exact ih [] (fun e' he' => ihbs e' (List.mem_cons_of_mem _ he')) as
      rw [RecGroup.openTyVarsAux_length]
      rw [hbs' (b + bs.length) anns]

/-- Top-level form (`d = 0`). -/
theorem retargetVars_openTyVars {mono : Nat → Bool} {b : Nat} {Vs : List Ty} {Xs : List Nat} {e : Expr}
    (hVsLC : ∀ V ∈ Vs, V.IsLC) :
    (retargetVars mono Vs b e).openTyVars Xs = retargetVars mono Vs b (e.openTyVars Xs) := by
  simpa only [Expr.openTyVars] using retargetVars_openTyVarsAux (d := 0) (hVsLC := hVsLC) (e := e)

/-- The `let` rule's cofinite opener commutes with the retarget. -/
theorem retargetVars_openBoundTyVars {mono : Nat → Bool} {b : Nat} {Vs : List Ty} {Xs : List Nat} {e : Expr}
    {ann : Option PolyTy} (hVsLC : ∀ V ∈ Vs, V.IsLC) :
    retargetVars mono Vs b (Expr.openBoundTyVars ann Xs e)
      = Expr.openBoundTyVars ann Xs (retargetVars mono Vs b e) := by
  cases ann with
  | none => rfl
  | some σ => simpa only [Expr.openBoundTyVars, Expr.openTyVars] using
      (retargetVars_openTyVarsAux (d := 0) (hVsLC := hVsLC) (e := e)).symm

/-- Every pair of the retargeted-zip is the retarget of a pair of the original zip. -/
theorem retargetGroup_zip_mem {mono : Nat → Bool} {b : Nat} {Vs : List Ty} :
    ∀ (bs : List Expr) (specs : List RecSpec) (p : Expr × RecSpec),
      p ∈ (retargetGroup mono Vs b bs).zip specs →
        ∃ q, q ∈ bs.zip specs ∧ p.1 = retargetVars mono Vs b q.1 ∧ p.2 = q.2 := by
  intro bs specs p hp
  revert hp specs
  induction bs with
  | nil =>
      intro specs hp
      simp [retargetGroup, List.zip_nil_left] at hp
  | cons e tl ih =>
      intro specs hp
      cases specs with
      | nil =>
          simp [retargetGroup, List.zip_nil_right] at hp
      | cons s ss =>
          simp only [retargetGroup, List.zip_cons_cons, List.mem_cons] at hp
          rcases hp with hp | hp
          · subst hp
            exact ⟨(e, s), List.mem_cons_self .., rfl, rfl⟩
          · rcases ih ss hp with ⟨q, hq, h1, h2⟩
            exact ⟨q, List.mem_cons_of_mem _ hq, h1, h2⟩

/-- Retargeting preserves non-emptiness of the branch list. -/
theorem retargetBranches_ne_nil {mono : Nat → Bool} {b : Nat} {Vs : List Ty}
    {brs : List (MatchPattern × Expr)} (h : brs ≠ []) :
    retargetBranches mono Vs b brs ≠ [] := by
  intro h'
  cases brs with
  | nil => exact h rfl
  | cons br rest =>
      simp only [retargetBranches, List.cons_ne_nil] at h'

/-- Every retargeted branch is the retarget of an original branch (pattern kept). -/
theorem retargetBranches_mem {mono : Nat → Bool} {b : Nat} {Vs : List Ty} :
    ∀ (brs : List (MatchPattern × Expr)) (br' : MatchPattern × Expr),
      br' ∈ retargetBranches mono Vs b brs →
        ∃ pat body, (pat, body) ∈ brs ∧ br' = (pat, retargetVars mono Vs (b + pat.bindCount) body) := by
  intro brs br' hmem
  induction brs with
  | nil =>
      simp [retargetBranches] at hmem
  | cons br rest ih =>
      cases br with
      | mk pat body =>
          simp only [retargetBranches, List.mem_cons] at hmem
          rcases hmem with hmem | hmem
          · subst hmem
            exact ⟨pat, body, List.mem_cons_self .., rfl⟩
          · rcases ih hmem with ⟨pat', body', hmem', heq⟩
            exact ⟨pat', body', List.mem_cons_of_mem _ hmem', heq⟩

/-- A `TypeOfElabHM` derivation over a mixed recursion-group env prefix
    `specs.map (RecSpec.rhsEntry G Xs)` transports to one over the promoted prefix
    `(promoteSpecs G specs).map (RecSpec.rhsEntry G Xs)`, retargeting mono-member uses
    (arity `0`) to the pool opening `Xs`-as-`fvar`s and leaving poly-member uses untouched.
    This is the mixed analogue of `TypeOfHM.weaken_schemes` with the term rewrite the
    type-passing `var` rule forces. -/
theorem retarget_transport
    {ctors : CtorEnv} {env : Env} {e : Expr} {τ : Ty}
    {specs : List RecSpec} {G Xs : List Nat}
    (hGnodup : G.Nodup) (hlen : Xs.length = G.length) (hdisj : ∀ g ∈ G, g ∉ Xs)
    (hmonoLC : ∀ τ, RecSpec.mono τ ∈ specs → τ.IsLC)
    (h : TypeOfElabHM ⟨specs.map (RecSpec.rhsEntry G Xs) ++ env, ctors⟩ e τ) :
    TypeOfElabHM ⟨(promoteSpecs G specs).map (RecSpec.rhsEntry G Xs) ++ env, ctors⟩
      (retargetVars (specsMono specs) (Xs.map Ty.fvar) 0 e) τ := by
  have hVsLC : ∀ V ∈ Xs.map Ty.fvar, V.IsLC := by
    intro V hV
    rcases List.mem_map.mp hV with ⟨x, _, rfl⟩
    exact .fvar
  have H : ∀ {ctx : Ctx} {e₀ : Expr} {τ₀ : Ty}, TypeOfElabHM ctx e₀ τ₀ →
      ∀ ep : Env, ctx.env = ep ++ specs.map (RecSpec.rhsEntry G Xs) ++ env →
      TypeOfElabHM ⟨ep ++ (promoteSpecs G specs).map (RecSpec.rhsEntry G Xs) ++ env, ctx.ctors⟩
        (retargetVars (specsMono specs) (Xs.map Ty.fvar) ep.length e₀) τ₀ := by
    intro ctx e₀ τ₀ hd
    induction hd using TypeOfElabHM.rec_strong with
    | primLitUnit => intro ep heq; exact .primLitUnit
    | primLitInt => intro ep heq; exact .primLitInt
    | primLitNat => intro ep heq; exact .primLitNat
    | primLitChar => intro ep heq; exact .primLitChar
    | primBinOpIntAdd => intro ep heq; exact .primBinOpIntAdd
    | primBinOpIntSub => intro ep heq; exact .primBinOpIntSub
    | primBinOpIntLt htrue hfalse ihtrue ihfalse =>
        intro ep heq
        exact .primBinOpIntLt (ihtrue ep heq) (ihfalse ep heq)
    | primBinOpCharLt htrue hfalse ihtrue ihfalse =>
        intro ep heq
        exact .primBinOpCharLt (ihtrue ep heq) (ihfalse ep heq)
    | @lambda paramTy ann bodyCtx ctx body bodyTy hpc hann heqctx hbody ihbody =>
        intro ep heq
        refine TypeOfElabHM.lambda hpc hann rfl ?_
        have hbc := ihbody (PolyTy.mkTrivial paramTy :: ep)
          (by simp only [heqctx, heq, List.cons_append, List.append_assoc])
        simpa only [heqctx, List.cons_append, List.append_assoc, List.length_cons] using hbc
    | app hf hinput ihf ihinput =>
        intro ep heq
        exact .app (ihf ep heq) (ihinput ep heq)
    | @letIn ann ctx boundExpr bodyCtx body bodyTy M L hwf hann hcofin heqctx hbody ihcofin ihbody =>
        intro ep heq
        refine TypeOfElabHM.letIn (L := L) hwf hann ?_ rfl ?_
        · intro Xs hf
          have hc := ihcofin Xs hf ep heq
          rw [← retargetVars_openBoundTyVars (hVsLC := hVsLC)]
          exact hc
        · have hbc := ihbody (M :: ep)
            (by simp only [heqctx, heq, List.cons_append, List.append_assoc])
          simpa only [heqctx, List.cons_append, List.append_assoc, List.length_cons] using hbc
    | @var dbl polyTy tyArgs ty ctx hlook hlc hinst' =>
        intro ep heq
        rw [heq] at hlook
        by_cases hwin : ep.length ≤ dbl ∧ dbl < ep.length + specs.length
        · let k : Nat := dbl - ep.length
          have hk : k < specs.length := by
            dsimp [k]
            omega
          have hdbl : dbl - ep.length = k := rfl
          have hlook_rhs : (ep ++ specs.map (RecSpec.rhsEntry G Xs) ++ env)[dbl]? =
              some (RecSpec.rhsEntry G Xs (specs[k])) := by
            rw [List.append_assoc, List.getElem?_append_right (by omega : ep.length ≤ dbl)]
            rw [hdbl]
            rw [List.getElem?_append_left (by simpa using hk)]
            simp [List.getElem?_map, List.getElem?_eq_getElem hk]
          have hpolyTy : polyTy = RecSpec.rhsEntry G Xs (specs[k]) :=
            Option.some.inj (hlook.symm.trans hlook_rhs)
          cases hk' : specs[k] with
          | mono τk =>
              rw [hk'] at hpolyTy
              simp only [RecSpec.rhsEntry] at hpolyTy
              subst polyTy
              have htyArgs : tyArgs = [] := by
                rcases hlc with ⟨hlen0, _⟩
                exact List.eq_nil_of_length_eq_zero hlen0
              have hty : ty = Ty.renameG G Xs τk := by
                have hinst0 : InstantiatesBy [] (Ty.renameG G Xs τk) ty := by
                  simpa [PolyTy.InstantiatesTo, htyArgs] using hinst'
                exact InstantiatesBy_empty_eq hinst0
              have hτkLC : τk.IsLC := hmonoLC τk (hk' ▸ List.getElem_mem hk)
              have hinstP := promoteScheme_instantiatesTo hτkLC hGnodup hlen hdisj
              have hmonoK : specsMono specs k = true := by
                rw [specsMono_getElem hk, hk', RecSpec.isMono]
              have hlook_prom : (ep ++ (promoteSpecs G specs).map (RecSpec.rhsEntry G Xs) ++ env)[dbl]? =
                  some (promoteScheme G τk) := by
                rw [List.append_assoc, List.getElem?_append_right (by omega : ep.length ≤ dbl)]
                rw [hdbl]
                rw [List.getElem?_append_left (by simpa [promoteSpecs_length] using hk)]
                rw [promoteSpecs_rhsEntry]
                simp [List.getElem?_map, List.getElem?_eq_getElem hk, hk']
              simp only [retargetVars]
              rw [if_pos (by exact ⟨hwin.1, hmonoK⟩)]
              refine TypeOfElabHM.var (polyTy := promoteScheme G τk) (tyArgs := Xs.map Ty.fvar) ?_ ?_ ?_
              · exact hlook_prom
              · show Ty.AreLC (promoteScheme G τk).paramCount (Xs.map Ty.fvar)
                exact ⟨hinstP.1.symm, hVsLC⟩
              · show (promoteScheme G τk).InstantiatesTo (Xs.map Ty.fvar) ty
                rw [hty]
                exact hinstP.2
          | poly σk =>
              rw [hk'] at hpolyTy
              simp only [RecSpec.rhsEntry] at hpolyTy
              subst polyTy
              have hmonoK : specsMono specs k = false := by
                rw [specsMono_getElem hk, hk', RecSpec.isMono]
              have hlook_prom : (ep ++ (promoteSpecs G specs).map (RecSpec.rhsEntry G Xs) ++ env)[dbl]? =
                  some σk := by
                rw [List.append_assoc, List.getElem?_append_right (by omega : ep.length ≤ dbl)]
                rw [hdbl]
                rw [List.getElem?_append_left (by simpa [promoteSpecs_length] using hk)]
                rw [promoteSpecs_rhsEntry]
                simp [List.getElem?_map, List.getElem?_eq_getElem hk, hk']
              simp only [retargetVars]
              rw [if_neg (by intro hh; rw [hmonoK] at hh; cases hh.2)]
              refine TypeOfElabHM.var (polyTy := σk) ?_ hlc hinst'
              exact hlook_prom
        · by_cases hlt : dbl < ep.length
          · simp only [retargetVars]
            rw [if_neg (by intro hh; exact (by omega : ¬ ep.length ≤ dbl) hh.1)]
            refine TypeOfElabHM.var ?_ hlc hinst'
            show (ep ++ (promoteSpecs G specs).map (RecSpec.rhsEntry G Xs) ++ env)[dbl]? = some polyTy
            rw [List.append_assoc, List.getElem?_append_left hlt]
            rw [List.append_assoc, List.getElem?_append_left hlt] at hlook
            exact hlook
          · have hle : ep.length ≤ dbl := by omega
            have hge : ep.length + specs.length ≤ dbl := by omega
            simp only [retargetVars]
            rw [if_neg (by intro hh; rw [specsMono_of_ge (by omega)] at hh; cases hh.2)]
            refine TypeOfElabHM.var ?_ hlc hinst'
            show (ep ++ (promoteSpecs G specs).map (RecSpec.rhsEntry G Xs) ++ env)[dbl]? = some polyTy
            rw [List.append_assoc, List.getElem?_append_right hle]
            rw [List.append_assoc, List.getElem?_append_right hle] at hlook
            have hdProm : ((promoteSpecs G specs).map (RecSpec.rhsEntry G Xs)).length ≤ dbl - ep.length := by
              simp [promoteSpecs_length]
              omega
            have hdm : (specs.map (RecSpec.rhsEntry G Xs)).length ≤ dbl - ep.length := by
              simp
              omega
            rw [List.getElem?_append_right hdProm]
            rw [List.getElem?_append_right hdm] at hlook
            rw [show (dbl - ep.length) - ((promoteSpecs G specs).map (RecSpec.rhsEntry G Xs)).length
                = (dbl - ep.length) - (specs.map (RecSpec.rhsEntry G Xs)).length from by
              simp [promoteSpecs_length]]
            exact hlook
    | ctor hlook htyargs hinst' =>
        intro ep heq
        exact .ctor hlook htyargs hinst'
    | @match_ ctx scrutinee scrutTy branches resultTy hscrut hne hbrs ihscrut ihbrs =>
        intro ep heq
        refine TypeOfElabHM.match_ (ihscrut ep heq) (retargetBranches_ne_nil hne) ?_
        intro br' hmem'
        rcases retargetBranches_mem branches br' hmem' with ⟨pat, body, hmemb, heqbr'⟩
        subst heqbr'
        rcases ihbrs (pat, body) hmemb with
          ⟨ctorr, c, n, tyArgs, instContents, hpat, hspec, hbody, ihbody⟩ |
          ⟨hpat, hbody, ihbody⟩
        · subst hpat
          refine TypeOfElabMatchBranch.mk hspec rfl ?_
          have hbc := ihbody (instContents.map PolyTy.mkTrivial ++ ep)
            (by simp only [List.append_assoc, heq])
          have hlenInst : instContents.length = (MatchPattern.named c n).bindCount := by
            rw [hspec.fields.length_eq.symm, hspec.bind_count]
            rfl
          simpa only [List.append_assoc, List.length_append, List.length_map,
            hlenInst, Nat.add_comm] using hbc
        · subst hpat
          have hw : TypeOfElabHM ⟨ep ++ (promoteSpecs G specs).map (RecSpec.rhsEntry G Xs) ++ env, ctx.ctors⟩
              (retargetVars (specsMono specs) (Xs.map Ty.fvar)
                (ep.length + (MatchPattern.wildcard).bindCount) body) resultTy := by
            simpa [MatchPattern.bindCount] using ihbody ep heq
          exact TypeOfElabMatchBranch.wildcard hw
    | @letRec ctx bodyCtx anns bindings specs G L body ρ hwf hmono hpoly heqctx hbody ihmono ihpoly ihbody =>
        intro ep heq
        subst heqctx
        refine TypeOfElabHM.letRec (specs := specs) (G := G) (L := L) ?_ ?_ ?_ rfl ?_
        · exact ⟨hwf.anns_eq, by simp [retargetGroup_length, hwf.length], hwf.nodup,
            hwf.mono_lc, hwf.poly_wf⟩
        · intro Xs hf p hp τ hτ
          rcases retargetGroup_zip_mem bindings specs p hp with ⟨q, hq, hp1, hp2⟩
          rw [hp2] at hτ
          have hc := ihmono Xs hf q hq τ hτ
          have hcc := hc (specs.map (RecSpec.rhsEntry G Xs) ++ ep)
            (by simp only [RecSpecs.rhsCtx, heq, List.append_assoc])
          rw [hp1]
          simpa only [RecSpecs.rhsCtx, List.append_assoc, List.length_append, List.length_map,
            hwf.length, Nat.add_comm] using hcc
        · intro Xs hf p hp σ hσ Ys hfY
          rcases retargetGroup_zip_mem bindings specs p hp with ⟨q, hq, hp1, hp2⟩
          rw [hp2] at hσ
          have hc := ihpoly Xs hf q hq σ hσ Ys hfY
          have hcc := hc (specs.map (RecSpec.rhsEntry G Xs) ++ ep)
            (by simp only [RecSpecs.rhsCtx, heq, List.append_assoc])
          rw [hp1]
          rw [retargetVars_openTyVars (hVsLC := hVsLC)]
          simpa only [RecSpecs.rhsCtx, List.append_assoc, List.length_append, List.length_map,
            hwf.length, Nat.add_comm] using hcc
        · have hb := ihbody (specs.map (RecSpec.bodyScheme G) ++ ep)
            (by simp only [RecSpecs.bodyCtx, heq, List.append_assoc])
          simpa only [RecSpecs.bodyCtx, List.append_assoc, List.length_append, List.length_map,
            hwf.length, Nat.add_comm] using hb
  exact H h [] (by simp)

/-! ### The forgetting direction

`retarget_transport` transports a derivation UP (mono env, `tyArgs = []` → scheme env,
`tyArgs = Vs`). The converse — used by `polyTyped_to_monoTyped` below — must go DOWN: the scheme
env's `var` rule pins `tyArgs = Vs` (the term is the retarget), the instantiation is
deterministic (`det_same`), so each use collapses to the shared monotype and the `var` becomes
`tyArgs = []`. -/

/-- Same-`tyArgs` instantiation is deterministic: one scheme body instantiated at the same
    arguments gives one result type. No boundedness side condition (unlike `det_agree`) — the
    recursion is pointwise on the proof. -/
theorem InstantiatesBy.det_same {tyArgs : List Ty} : ∀ {ty t1 t2 : Ty},
    InstantiatesBy tyArgs ty t1 → InstantiatesBy tyArgs ty t2 → t1 = t2 := by
  intro ty
  induction ty using Ty.rec_strong with
  | prim p => intro t1 t2 h1 h2; cases h1; cases h2; rfl
  | fvar n => intro t1 t2 h1 h2; cases h1; cases h2; rfl
  | bvar i =>
      intro t1 t2 h1 h2
      cases h1 with
      | bvar hs1 => cases h2 with | bvar hs2 => exact Option.some.inj (hs1.symm.trans hs2)
  | arrow a b iha ihb =>
      intro t1 t2 h1 h2
      cases h1 with
      | arrow h1a h1b =>
          cases h2 with
          | arrow h2a h2b => rw [iha h1a h2a, ihb h1b h2b]
  | customTy nm tys ih =>
      intro t1 t2 h1 h2
      cases h1 with
      | customTy hf1 =>
          cases h2 with
          | customTy hf2 =>
              congr 1
              rename_i inst1 inst2
              have hdet : ∀ (i1 i2 : List Ty),
                  List.Forall₂ (InstantiatesBy tyArgs) tys i1 →
                  List.Forall₂ (InstantiatesBy tyArgs) tys i2 → i1 = i2 := by
                intro i1 i2 hg1 hg2
                apply List.ext_getElem
                · exact hg1.length_eq.symm.trans hg2.length_eq
                · intro i hi1 hi2
                  have hiTys : i < tys.length := by
                    rw [← hg1.length_eq] at hi1
                    exact hi1
                  have h1 : InstantiatesBy tyArgs (tys[i]) (i1[i]) :=
                    List.Forall₂.get hg1 hiTys hi1
                  have h2 : InstantiatesBy tyArgs (tys[i]) (i2[i]) :=
                    List.Forall₂.get hg2 hiTys hi2
                  exact ih (tys[i]) (List.getElem_mem hiTys) h1 h2
              exact hdet inst1 inst2 hf1 hf2
  | bl lo hi e ih =>
      intro t1 t2 h1 h2
      cases h1 with
      | bl he1 => cases h2 with | bl he2 => rw [ih he1 he2]

/-- Iterated `substFvar` by LC replacements preserves local-closedness (public copy of the
    private `Ty.IsLC.substFvars`). -/
theorem Ty.substFvars_lc {s : List (Nat × Ty)} {τ : Ty}
    (hs : ∀ p ∈ s, p.2.IsLC) (hτ : τ.IsLC) : (Ty.substFvars s τ).IsLC := by
  induction s generalizing τ with
  | nil => exact hτ
  | cons hd tl ih =>
      obtain ⟨Z, U⟩ := hd
      simp only [Ty.substFvars]
      exact ih (fun p hp => hs p (List.mem_cons_of_mem _ hp))
        (Ty.IsLC.substFvar (hs (Z, U) List.mem_cons_self) hτ)

/-- `renameG` (a renaming to fresh `fvar`s) preserves local-closedness. Public copy of the
    private `Ty.renameG_isLC` (`Core.lean:5477`), which `polyTyped_to_monoTyped` needs for the
    forgetting map's `hmonoLC` hypothesis. -/
theorem Ty.renameG_lc {G Xs : List Nat} {τ : Ty} (hτ : τ.IsLC) : (Ty.renameG G Xs τ).IsLC := by
  unfold Ty.renameG
  exact Ty.substFvars_lc (fun p hp => by
    obtain ⟨x, _, hx⟩ := List.mem_map.mp (List.of_mem_zip hp).2
    rw [← hx]; exact .fvar) hτ

/-- The retargeted image of a branch is a member of the retargeted branch list. -/
theorem retargetBranches_mem_map {mono : Nat → Bool} {b : Nat} {Vs : List Ty}
    {brs : List (MatchPattern × Expr)} {pat : MatchPattern} {body : Expr}
    (h : (pat, body) ∈ brs) :
    (pat, retargetVars mono Vs (b + pat.bindCount) body) ∈ retargetBranches mono Vs b brs := by
  induction brs with
  | nil => exact absurd h List.not_mem_nil
  | cons hd tl ih =>
      cases hd with
      | mk pat' body' =>
          simp only [retargetBranches, List.mem_cons] at h ⊢
          cases h with
          | inl heq =>
              simp only [Prod.mk.injEq] at heq
              obtain ⟨rfl, rfl⟩ := heq
              exact Or.inl rfl
          | inr h' => exact Or.inr (ih h')

/-- The retargeted image of a zip member is a member of the retargeted-zip. -/
theorem retargetGroup_zip_mem_map {mono : Nat → Bool} {b : Nat} {Vs : List Ty} :
    ∀ (bs : List Expr) (specs : List RecSpec) (p : Expr × RecSpec),
      p ∈ bs.zip specs →
        ∃ q, q ∈ (retargetGroup mono Vs b bs).zip specs ∧ q.1 = retargetVars mono Vs b p.1 ∧ q.2 = p.2 := by
  intro bs specs p hp
  revert hp specs
  induction bs with
  | nil =>
      intro specs hp
      simp [List.zip_nil_left] at hp
  | cons e tl ih =>
      intro specs hp
      cases specs with
      | nil =>
          simp [List.zip_nil_right] at hp
      | cons s ss =>
          simp only [List.zip_cons_cons, List.mem_cons] at hp
          rcases hp with hp | hp
          · subst hp
            exact ⟨(retargetVars mono Vs b e, s), List.mem_cons_self .., rfl, rfl⟩
          · rcases ih ss hp with ⟨q, hq, h1, h2⟩
            exact ⟨q, List.mem_cons_of_mem _ hq, h1, h2⟩

/-- The forgetting direction: a `TypeOfElabHM` derivation over a promoted (scheme) env prefix,
    on a term whose group-window `var`s carry `Xs`-as-`fvar`s, degrades to a derivation over the
    same source term with those `var`s carrying `[]`, in the monomorphic env prefix. The exact
    reverse of `retarget_transport`.

    Proof mirrors `retarget_transport` case-by-case, with the roles of the env prefixes swapped
    and an extra hypothesis threading the SOURCE term `e₁` (the hypothesis derivation is over
    the retarget of `e₁`), so the `var` case knows the pinned `tyArgs` are `Xs.map Ty.fvar` for
    mono slots (pinned by `InstantiatesBy.det_same`) and leaves poly slots untouched. -/
theorem retarget_untransport
    {ctors : CtorEnv} {env : Env} {e : Expr} {τ : Ty}
    {specs : List RecSpec} {G Xs : List Nat}
    (hGnodup : G.Nodup) (hlen : Xs.length = G.length) (hdisj : ∀ g ∈ G, g ∉ Xs)
    (hmonoLC : ∀ τ, RecSpec.mono τ ∈ specs → τ.IsLC)
    (h : TypeOfElabHM ⟨(promoteSpecs G specs).map (RecSpec.rhsEntry G Xs) ++ env, ctors⟩
          (retargetVars (specsMono specs) (Xs.map Ty.fvar) 0 e) τ) :
    TypeOfElabHM ⟨specs.map (RecSpec.rhsEntry G Xs) ++ env, ctors⟩
      (retargetVars (specsMono specs) [] 0 e) τ := by
  have hVsLC : ∀ V ∈ Xs.map Ty.fvar, V.IsLC := by
    intro V hV
    rcases List.mem_map.mp hV with ⟨x, _, rfl⟩
    exact .fvar
  have H : ∀ {ctx : Ctx} {e₀ : Expr} {τ₀ : Ty}, TypeOfElabHM ctx e₀ τ₀ →
      ∀ (ep : Env) (e₁ : Expr), ctx.env = ep ++ (promoteSpecs G specs).map (RecSpec.rhsEntry G Xs) ++ env →
      e₀ = retargetVars (specsMono specs) (Xs.map Ty.fvar) ep.length e₁ →
      TypeOfElabHM ⟨ep ++ specs.map (RecSpec.rhsEntry G Xs) ++ env, ctx.ctors⟩
        (retargetVars (specsMono specs) [] ep.length e₁) τ₀ := by
    intro ctx e₀ τ₀ hd
    induction hd using TypeOfElabHM.rec_strong with
    | primLitUnit =>
        intro ep e₁ heq heq'
        cases e₁ with
        | primLit p =>
            simp only [retargetVars] at heq'
            injection heq' with hp
            subst hp
            exact .primLitUnit
        | var i tyArgs₁ =>
            simp only [retargetVars] at heq'
            by_cases hwin : ep.length ≤ i ∧ specsMono specs (i - ep.length)
            · rw [if_pos hwin] at heq'; cases heq'
            · rw [if_neg hwin] at heq'; cases heq'
        | _ => simp only [retargetVars] at heq'; cases heq'
    | primLitInt =>
        intro ep e₁ heq heq'
        cases e₁ with
        | primLit p =>
            simp only [retargetVars] at heq'
            injection heq' with hp
            subst hp
            exact .primLitInt
        | var i tyArgs₁ =>
            simp only [retargetVars] at heq'
            by_cases hwin : ep.length ≤ i ∧ specsMono specs (i - ep.length)
            · rw [if_pos hwin] at heq'; cases heq'
            · rw [if_neg hwin] at heq'; cases heq'
        | _ => simp only [retargetVars] at heq'; cases heq'
    | primLitNat =>
        intro ep e₁ heq heq'
        cases e₁ with
        | primLit p =>
            simp only [retargetVars] at heq'
            injection heq' with hp
            subst hp
            exact .primLitNat
        | var i tyArgs₁ =>
            simp only [retargetVars] at heq'
            by_cases hwin : ep.length ≤ i ∧ specsMono specs (i - ep.length)
            · rw [if_pos hwin] at heq'; cases heq'
            · rw [if_neg hwin] at heq'; cases heq'
        | _ => simp only [retargetVars] at heq'; cases heq'
    | primLitChar =>
        intro ep e₁ heq heq'
        cases e₁ with
        | primLit p =>
            simp only [retargetVars] at heq'
            injection heq' with hp
            subst hp
            exact .primLitChar
        | var i tyArgs₁ =>
            simp only [retargetVars] at heq'
            by_cases hwin : ep.length ≤ i ∧ specsMono specs (i - ep.length)
            · rw [if_pos hwin] at heq'; cases heq'
            · rw [if_neg hwin] at heq'; cases heq'
        | _ => simp only [retargetVars] at heq'; cases heq'
    | primBinOpIntAdd =>
        intro ep e₁ heq heq'
        cases e₁ with
        | primBinOp op =>
            simp only [retargetVars] at heq'
            injection heq' with hop
            subst hop
            exact .primBinOpIntAdd
        | var i tyArgs₁ =>
            simp only [retargetVars] at heq'
            by_cases hwin : ep.length ≤ i ∧ specsMono specs (i - ep.length)
            · rw [if_pos hwin] at heq'; cases heq'
            · rw [if_neg hwin] at heq'; cases heq'
        | _ => simp only [retargetVars] at heq'; cases heq'
    | primBinOpIntSub =>
        intro ep e₁ heq heq'
        cases e₁ with
        | primBinOp op =>
            simp only [retargetVars] at heq'
            injection heq' with hop
            subst hop
            exact .primBinOpIntSub
        | var i tyArgs₁ =>
            simp only [retargetVars] at heq'
            by_cases hwin : ep.length ≤ i ∧ specsMono specs (i - ep.length)
            · rw [if_pos hwin] at heq'; cases heq'
            · rw [if_neg hwin] at heq'; cases heq'
        | _ => simp only [retargetVars] at heq'; cases heq'
    | primBinOpIntLt htrue hfalse ihtrue ihfalse =>
        intro ep e₁ heq heq'
        cases e₁ with
        | primBinOp op =>
            simp only [retargetVars] at heq'
            injection heq' with hop
            subst hop
            exact .primBinOpIntLt (ihtrue ep (.ctor ⟨"True"⟩) heq (by rfl))
              (ihfalse ep (.ctor ⟨"False"⟩) heq (by rfl))
        | var i tyArgs₁ =>
            simp only [retargetVars] at heq'
            by_cases hwin : ep.length ≤ i ∧ specsMono specs (i - ep.length)
            · rw [if_pos hwin] at heq'; cases heq'
            · rw [if_neg hwin] at heq'; cases heq'
        | _ => simp only [retargetVars] at heq'; cases heq'
    | primBinOpCharLt htrue hfalse ihtrue ihfalse =>
        intro ep e₁ heq heq'
        cases e₁ with
        | primBinOp op =>
            simp only [retargetVars] at heq'
            injection heq' with hop
            subst hop
            exact .primBinOpCharLt (ihtrue ep (.ctor ⟨"True"⟩) heq (by rfl))
              (ihfalse ep (.ctor ⟨"False"⟩) heq (by rfl))
        | var i tyArgs₁ =>
            simp only [retargetVars] at heq'
            by_cases hwin : ep.length ≤ i ∧ specsMono specs (i - ep.length)
            · rw [if_pos hwin] at heq'; cases heq'
            · rw [if_neg hwin] at heq'; cases heq'
        | _ => simp only [retargetVars] at heq'; cases heq'
    | @lambda paramTy ann bodyCtx ctx body bodyTy hpc hann heqctx hbody ihbody =>
        intro ep e₁ heq heq'
        cases e₁ with
        | lambda ann' body' =>
            simp only [retargetVars] at heq'
            injection heq' with hann' hbody'
            subst hann'
            refine TypeOfElabHM.lambda hpc hann rfl ?_
            have hbc := ihbody (PolyTy.mkTrivial paramTy :: ep) body'
              (by simp only [heqctx, heq, List.cons_append, List.append_assoc])
              (by rw [hbody']; simp)
            simpa only [heqctx, List.cons_append, List.append_assoc, List.length_cons] using hbc
        | var i tyArgs₁ =>
            simp only [retargetVars] at heq'
            by_cases hwin : ep.length ≤ i ∧ specsMono specs (i - ep.length)
            · rw [if_pos hwin] at heq'; cases heq'
            · rw [if_neg hwin] at heq'; cases heq'
        | _ => simp only [retargetVars] at heq'; cases heq'
    | app hf hinput ihf ihinput =>
        intro ep e₁ heq heq'
        cases e₁ with
        | app f' arg' =>
            simp only [retargetVars] at heq'
            injection heq' with hf' harg'
            exact .app (ihf ep f' heq hf') (ihinput ep arg' heq harg')
        | var i tyArgs₁ =>
            simp only [retargetVars] at heq'
            by_cases hwin : ep.length ≤ i ∧ specsMono specs (i - ep.length)
            · rw [if_pos hwin] at heq'; cases heq'
            · rw [if_neg hwin] at heq'; cases heq'
        | _ => simp only [retargetVars] at heq'; cases heq'
    | @letIn ann ctx boundExpr bodyCtx body bodyTy M L hwf hann hcofin heqctx hbody ihcofin ihbody =>
        intro ep e₁ heq heq'
        cases e₁ with
        | letIn ann' boundExpr' body' =>
            simp only [retargetVars] at heq'
            injection heq' with hann' hbound' hbody'
            subst hann'
            refine TypeOfElabHM.letIn (L := L) hwf hann ?_ rfl ?_
            · intro Xs hf
              have hc := ihcofin Xs hf ep (Expr.openBoundTyVars ann Xs boundExpr')
                (by simp only [heq, List.append_assoc])
                (by
                  rw [hbound']
                  exact (retargetVars_openBoundTyVars (hVsLC := hVsLC)).symm)
              rw [← retargetVars_openBoundTyVars (Vs := ([] : List Ty))
                (hVsLC := by intro V hV; simp at hV)]
              exact hc
            · have hb := ihbody (M :: ep) body'
                (by simp only [heqctx, heq, List.cons_append, List.append_assoc])
                (by rw [hbody']; simp)
              simpa only [heqctx, List.cons_append, List.append_assoc, List.length_cons] using hb
        | var i tyArgs₁ =>
            simp only [retargetVars] at heq'
            by_cases hwin : ep.length ≤ i ∧ specsMono specs (i - ep.length)
            · rw [if_pos hwin] at heq'; cases heq'
            · rw [if_neg hwin] at heq'; cases heq'
        | _ => simp only [retargetVars] at heq'; cases heq'
    | @var dbl polyTy tyArgs ty ctx hlook hlc hinst' =>
        intro ep e₁ heq heq'
        rw [heq] at hlook
        cases e₁ with
        | var dbl' tyArgs₁ =>
            simp only [retargetVars] at heq'
            by_cases hwin : ep.length ≤ dbl' ∧ specsMono specs (dbl' - ep.length)
            · rw [if_pos hwin] at heq'
              injection heq' with hdbl htyArgs
              subst hdbl
              subst htyArgs
              let k : Nat := dbl - ep.length
              have hk : k < specs.length := by
                dsimp [k]
                by_contra hnot
                have hge : specs.length ≤ dbl - ep.length := Nat.le_of_not_gt hnot
                have : specsMono specs (dbl - ep.length) = false := specsMono_of_ge hge
                rw [this] at hwin
                cases hwin.2
              have hkdef : dbl - ep.length = k := rfl
              have hlook_prom : (ep ++ (promoteSpecs G specs).map (RecSpec.rhsEntry G Xs) ++ env)[dbl]? =
                  some (promoteSpec G (specs[k])) := by
                rw [List.append_assoc, List.getElem?_append_right (by omega : ep.length ≤ dbl)]
                rw [hkdef]
                rw [List.getElem?_append_left (by simpa [promoteSpecs_length] using hk)]
                rw [promoteSpecs_rhsEntry]
                simp [List.getElem?_map, List.getElem?_eq_getElem hk]
              have hpolyTy : polyTy = promoteSpec G (specs[k]) :=
                Option.some.inj (hlook.symm.trans hlook_prom)
              cases hk' : specs[k] with
              | mono τk =>
                  rw [hk'] at hpolyTy
                  simp only [promoteSpec] at hpolyTy
                  subst polyTy
                  have hτkLC : τk.IsLC := hmonoLC τk (hk' ▸ List.getElem_mem hk)
                  have hinstP := promoteScheme_instantiatesTo hτkLC hGnodup hlen hdisj
                  have hty : ty = Ty.renameG G Xs τk := by
                    exact InstantiatesBy.det_same (ty := (promoteScheme G τk).body)
                      (by simpa [PolyTy.InstantiatesTo] using hinst')
                      (by simpa [PolyTy.InstantiatesTo] using hinstP.2)
                  have hmonoK : specsMono specs k = true := by
                    rw [specsMono_getElem hk, hk', RecSpec.isMono]
                  have hlook_mono : (ep ++ specs.map (RecSpec.rhsEntry G Xs) ++ env)[dbl]? =
                      some (PolyTy.mkTrivial (Ty.renameG G Xs τk)) := by
                    rw [List.append_assoc, List.getElem?_append_right (by omega : ep.length ≤ dbl)]
                    rw [hkdef]
                    rw [List.getElem?_append_left (by simpa using hk)]
                    simp [List.getElem?_map, List.getElem?_eq_getElem hk, hk', RecSpec.rhsEntry]
                  simp only [retargetVars]
                  rw [if_pos (by exact ⟨hwin.1, hmonoK⟩)]
                  refine TypeOfElabHM.var (polyTy := PolyTy.mkTrivial (Ty.renameG G Xs τk)) ?_ ?_ ?_
                  · exact hlook_mono
                  · show Ty.AreLC (PolyTy.mkTrivial (Ty.renameG G Xs τk)).paramCount []
                    simp [Ty.AreLC, PolyTy.mkTrivial]
                  · show (PolyTy.mkTrivial (Ty.renameG G Xs τk)).InstantiatesTo [] ty
                    rw [hty]
                    show InstantiatesBy [] (Ty.renameG G Xs τk) (Ty.renameG G Xs τk)
                    exact InstantiatesBy.refl_of_closed (Ty.renameG_lc hτkLC)
              | poly σk =>
                  rw [specsMono_getElem hk, hk'] at hwin
                  simp [RecSpec.isMono] at hwin
            · rw [if_neg hwin] at heq'
              injection heq' with hdbl htyArgs
              subst hdbl
              subst htyArgs
              by_cases hlt : dbl < ep.length
              · simp only [retargetVars]
                rw [if_neg (by intro hh; exact (by omega : ¬ ep.length ≤ dbl) hh.1)]
                refine TypeOfElabHM.var ?_ hlc hinst'
                show (ep ++ specs.map (RecSpec.rhsEntry G Xs) ++ env)[dbl]? = some polyTy
                rw [List.append_assoc, List.getElem?_append_left hlt]
                rw [List.append_assoc, List.getElem?_append_left hlt] at hlook
                exact hlook
              · have hle : ep.length ≤ dbl := by omega
                let k : Nat := dbl - ep.length
                by_cases hk' : k < specs.length
                · have hkdef : dbl - ep.length = k := rfl
                  have hlook_prom : ((promoteSpecs G specs).map (RecSpec.rhsEntry G Xs) ++ env)[dbl - ep.length]? =
                      some (promoteSpec G (specs[k])) := by
                    rw [List.getElem?_append_left (by simpa [promoteSpecs_length] using hk')]
                    rw [promoteSpecs_rhsEntry]
                    rw [hkdef]
                    simp [List.getElem?_map, List.getElem?_eq_getElem hk']
                  have hpolyTy : polyTy = promoteSpec G (specs[k]) :=
                    Option.some.inj (hlook.symm.trans (by
                      rw [List.append_assoc, List.getElem?_append_right hle]
                      rw [hkdef]
                      exact hlook_prom))
                  cases hk'' : specs[k] with
                  | mono τk =>
                      have hm : specsMono specs k = true := by
                        rw [specsMono_getElem hk', hk'', RecSpec.isMono]
                      exact False.elim (hwin ⟨hle, by simpa [k] using hm⟩)
                  | poly σk =>
                      rw [hk''] at hpolyTy
                      simp only [promoteSpec] at hpolyTy
                      subst polyTy
                      have hlook_mono : (ep ++ specs.map (RecSpec.rhsEntry G Xs) ++ env)[dbl]? =
                          some σk := by
                        rw [List.append_assoc, List.getElem?_append_right hle]
                        rw [hkdef]
                        rw [List.getElem?_append_left (by simpa using hk')]
                        simp [List.getElem?_map, List.getElem?_eq_getElem hk', hk'', RecSpec.rhsEntry]
                      simp only [retargetVars]
                      rw [if_neg hwin]
                      refine TypeOfElabHM.var (polyTy := σk) ?_ hlc hinst'
                      exact hlook_mono
                · have hge : ep.length + specs.length ≤ dbl := by
                    dsimp [k] at hk'
                    omega
                  simp only [retargetVars]
                  rw [if_neg hwin]
                  refine TypeOfElabHM.var ?_ hlc hinst'
                  show (ep ++ specs.map (RecSpec.rhsEntry G Xs) ++ env)[dbl]? = some polyTy
                  rw [List.append_assoc, List.getElem?_append_right hle]
                  rw [List.append_assoc, List.getElem?_append_right hle] at hlook
                  have hdm : (specs.map (RecSpec.rhsEntry G Xs)).length ≤ dbl - ep.length := by
                    simp; omega
                  rw [List.getElem?_append_right hdm]
                  have hdM : ((promoteSpecs G specs).map (RecSpec.rhsEntry G Xs)).length ≤ dbl - ep.length := by
                    simp [promoteSpecs_length]; omega
                  rw [List.getElem?_append_right hdM] at hlook
                  have hidx : (dbl - ep.length) - (specs.map (RecSpec.rhsEntry G Xs)).length
                      = (dbl - ep.length) - ((promoteSpecs G specs).map (RecSpec.rhsEntry G Xs)).length := by
                    simp [promoteSpecs_length]
                  rw [hidx]
                  exact hlook
        | _ => simp only [retargetVars] at heq'; cases heq'
    | ctor hlook htyargs hinst' =>
        intro ep e₁ heq heq'
        cases e₁ with
        | ctor name =>
            simp only [retargetVars] at heq'
            injection heq' with hname
            subst hname
            exact .ctor hlook htyargs hinst'
        | var i tyArgs₁ =>
            simp only [retargetVars] at heq'
            by_cases hwin : ep.length ≤ i ∧ specsMono specs (i - ep.length)
            · rw [if_pos hwin] at heq'; cases heq'
            · rw [if_neg hwin] at heq'; cases heq'
        | _ => simp only [retargetVars] at heq'; cases heq'
    | @match_ ctx scrutinee scrutTy branches resultTy hscrut hne hbrs ihscrut ihbrs =>
        intro ep e₁ heq heq'
        cases e₁ with
        | match_ scrut' branches' =>
            simp only [retargetVars] at heq'
            injection heq' with hsc heqbr
            have hne' : branches' ≠ [] := by
              intro hnil
              subst hnil
              simp [retargetBranches] at heqbr
              exact hne heqbr
            refine TypeOfElabHM.match_ (ihscrut ep scrut' heq hsc) (retargetBranches_ne_nil hne') ?_
            intro br' hmem'
            rcases retargetBranches_mem branches' br' hmem' with ⟨pat, body, hmemb, heqbr'⟩
            subst heqbr'
            have hmemVs : (pat, retargetVars (specsMono specs) (Xs.map Ty.fvar) (ep.length + pat.bindCount) body) ∈ branches := by
              rw [heqbr]
              exact retargetBranches_mem_map (mono := specsMono specs) (b := ep.length)
                (Vs := Xs.map Ty.fvar) hmemb
            rcases ihbrs (pat, retargetVars (specsMono specs) (Xs.map Ty.fvar) (ep.length + pat.bindCount) body) hmemVs with
              ⟨ctorr, c, m, tyArgs, instContents, hpat, hspec, hbody, ihbody⟩ |
              ⟨hpat, hbody, ihbody⟩
            · subst hpat
              refine TypeOfElabMatchBranch.mk hspec rfl ?_
              have hlenInst : instContents.length = (MatchPattern.named c m).bindCount := by
                rw [hspec.fields.length_eq.symm, hspec.bind_count]
                rfl
              have hbc := ihbody (instContents.map PolyTy.mkTrivial ++ ep) body
                (by simp only [List.append_assoc, heq])
                (by simp [hlenInst, List.length_append, List.length_map, Nat.add_comm])
              simpa only [List.append_assoc, List.length_append, List.length_map,
                hlenInst, Nat.add_comm] using hbc
            · subst hpat
              have hw : TypeOfElabHM ⟨ep ++ specs.map (RecSpec.rhsEntry G Xs) ++ env, ctx.ctors⟩
                  (retargetVars (specsMono specs) ([] : List Ty) (ep.length + (MatchPattern.wildcard).bindCount) body) resultTy := by
                simpa [MatchPattern.bindCount] using ihbody ep body heq
                  (by simp [MatchPattern.bindCount])
              exact TypeOfElabMatchBranch.wildcard hw
        | var i tyArgs₁ =>
            simp only [retargetVars] at heq'
            by_cases hwin : ep.length ≤ i ∧ specsMono specs (i - ep.length)
            · rw [if_pos hwin] at heq'; cases heq'
            · rw [if_neg hwin] at heq'; cases heq'
        | _ => simp only [retargetVars] at heq'; cases heq'
    | @letRec ctx bodyCtx anns bindings specs₀ G₀ L₀ body ρ hwf hmono hpoly heqctx hbody ihmono ihpoly ihbody =>
        intro ep e₁ heq heq'
        subst heqctx
        cases e₁ with
        | letRec anns' bindings' body' =>
            simp only [retargetVars] at heq'
            injection heq' with hanns hbindings hbody
            subst hanns
            have hlenb : bindings'.length = specs₀.length := by
              calc
                bindings'.length = (retargetGroup (specsMono specs) (Xs.map Ty.fvar) (ep.length + bindings'.length) bindings').length :=
                  (retargetGroup_length (b := ep.length + bindings'.length) bindings').symm
                _ = bindings.length := (congrArg List.length hbindings).symm
                _ = specs₀.length := hwf.length
            refine TypeOfElabHM.letRec (specs := specs₀) (G := G₀) (L := L₀) ?_ ?_ ?_ rfl ?_
            · exact ⟨hwf.anns_eq, by
                rw [retargetGroup_length (Vs := ([] : List Ty)) (b := ep.length + bindings'.length) bindings']
                exact hlenb, hwf.nodup, hwf.mono_lc, hwf.poly_wf⟩
            · intro Xs' hf p hp τ hτ
              rcases retargetGroup_zip_mem (Vs := ([] : List Ty)) (b := ep.length + bindings'.length)
                  bindings' specs₀ p hp with ⟨q, hq, hp1, hp2⟩
              rw [hp2] at hτ
              rcases retargetGroup_zip_mem_map (mono := specsMono specs) (Vs := Xs.map Ty.fvar)
                  (b := ep.length + bindings'.length) bindings' specs₀ q hq with ⟨p', hp', hp1', hp2'⟩
              rw [← hbindings] at hp'
              rw [← hp2'] at hτ
              have hc := ihmono Xs' hf p' hp' τ hτ
              have hcc := hc (specs₀.map (RecSpec.rhsEntry G₀ Xs') ++ ep) q.1
                (by simp only [RecSpecs.rhsCtx, heq, List.append_assoc])
                (by
                  rw [hp1']
                  rw [hlenb]
                  simp [List.length_append, List.length_map, Nat.add_comm])
              rw [hp1]
              simpa only [RecSpecs.rhsCtx, List.append_assoc, List.length_append, List.length_map,
                hlenb, Nat.add_comm] using hcc
            · intro Xs' hf p hp σ hσ Ys hfY
              rcases retargetGroup_zip_mem (Vs := ([] : List Ty)) (b := ep.length + bindings'.length)
                  bindings' specs₀ p hp with ⟨q, hq, hp1, hp2⟩
              rw [hp2] at hσ
              rcases retargetGroup_zip_mem_map (mono := specsMono specs) (Vs := Xs.map Ty.fvar)
                  (b := ep.length + bindings'.length) bindings' specs₀ q hq with ⟨p', hp', hp1', hp2'⟩
              rw [← hbindings] at hp'
              rw [← hp2'] at hσ
              have hc := ihpoly Xs' hf p' hp' σ hσ Ys hfY
              have hcc := hc (specs₀.map (RecSpec.rhsEntry G₀ Xs') ++ ep) (q.1.openTyVars Ys)
                (by simp only [RecSpecs.rhsCtx, heq, List.append_assoc])
                (by
                  rw [hp1']
                  rw [retargetVars_openTyVars (hVsLC := hVsLC)]
                  rw [hlenb]
                  simp [List.length_append, List.length_map, Nat.add_comm])
              rw [hp1]
              rw [retargetVars_openTyVars (hVsLC := by intro V hV; simp at hV)]
              simpa only [RecSpecs.rhsCtx, List.append_assoc, List.length_append, List.length_map,
                hlenb, Nat.add_comm] using hcc
            · have hb := ihbody (specs₀.map (RecSpec.bodyScheme G₀) ++ ep) body'
                (by simp only [RecSpecs.bodyCtx, heq, List.append_assoc])
                (by
                  rw [hbody]
                  rw [hlenb]
                  simp [List.length_append, List.length_map, Nat.add_comm])
              simpa only [RecSpecs.bodyCtx, List.append_assoc, List.length_append, List.length_map,
                hlenb, Nat.add_comm] using hb
        | var i tyArgs₁ =>
            simp only [retargetVars] at heq'
            by_cases hwin : ep.length ≤ i ∧ specsMono specs (i - ep.length)
            · rw [if_pos hwin] at heq'; cases heq'
            · rw [if_neg hwin] at heq'; cases heq'
        | _ => simp only [retargetVars] at heq'; cases heq'
  exact H h [] e (by simp) (by rfl)


/-! ### The letRec corollary (mono → poly) -/

/-- A member of a zip is the pair of the two lists' `getElem`s at a common index. -/
theorem List.zip_mem_getElem {α β : Type} {l1 : List α} {l2 : List β} {p : α × β}
    (hp : p ∈ l1.zip l2) : ∃ i, ∃ h1 : i < l1.length, ∃ h2 : i < l2.length,
      p.1 = l1[i]'h1 ∧ p.2 = l2[i]'h2 := by
  rcases List.mem_iff_getElem.mp hp with ⟨i, hizip, hget⟩
  have h1 : i < l1.length := List.lt_length_left_of_zip hizip
  have h2 : i < l2.length := List.lt_length_right_of_zip hizip
  have hz : p = (l1[i]'h1, l2[i]'h2) := by
    rw [← List.getElem_zip (h := hizip)]
    exact hget.symm
  exact ⟨i, h1, h2, by simpa using congrArg Prod.fst hz, by simpa using congrArg Prod.snd hz⟩

/-- The pair of the two lists' `getElem`s at a common index lies in the zip. -/
theorem List.getElem_mem_zip {α β : Type} {l1 : List α} {l2 : List β} {i : Nat}
    (h1 : i < l1.length) (h2 : i < l2.length) : (l1[i], l2[i]) ∈ l1.zip l2 := by
  induction l1 generalizing l2 i with
  | nil => simp at h1
  | cons a as ih =>
      cases l2 with
      | nil => simp at h2
      | cons b bs =>
          cases i with
          | zero => simp
          | succ i' =>
              have h1' : i' < as.length := by
                have := h1
                simp [List.length_cons] at this
                omega
              have h2' : i' < bs.length := by
                have := h2
                simp [List.length_cons] at this
                omega
              simp only [List.zip_cons_cons, List.getElem_cons_succ, List.mem_cons]
              exact Or.inr (ih (l2 := bs) (i := i') h1' h2')

/-- `Forall₂` of two pointwise maps follows from the pointwise relation. -/
theorem Forall₂_map_of_forall {α β γ : Type} {P : β → γ → Prop} {f : α → β} {g : α → γ}
    {l : List α} (h : ∀ a ∈ l, P (f a) (g a)) : List.Forall₂ P (l.map f) (l.map g) := by
  induction l with
  | nil => exact List.Forall₂.nil
  | cons a as ih =>
      exact List.Forall₂.cons (h a (List.mem_cons_self ..))
         (ih (fun x hx => h x (List.mem_cons_of_mem _ hx)))

/-- The letRec-shaped corollary, mono → poly: a mono group's `RecSpecs.MonoTyped` premise yields
    the promoted group's `RecSpecs.PolyTyped` premise at the full-pool schemes.

    Given `retarget_transport`, the remaining content is `promoteScheme_openVars` to see that
    `(promoteScheme G τ).openVars Ys` **is** `Ty.renameG G Ys τ` — so the promoted member's
    target type is literally the mono member's — plus the observation that once every spec is
    `poly`, `RecSpecs.rhsCtx` no longer depends on the pool opening.

    `bindings'` is left universally quantified with its defining equation as a hypothesis
    (`hopen`), so this lemma does not depend on the stored-vs-opened commute
    (`retargetStored_openTyVars`). -/
theorem monoTyped_to_polyTyped
    {ctx : Ctx} {bindings bindings' : List Expr} {monos : List Ty} {G L : List Nat}
    (hGnodup : G.Nodup)
    (hmonoLC : ∀ μ ∈ monos, μ.IsLC)
    (hlen : bindings.length = monos.length)
    (hmono : RecSpecs.MonoTyped TypeOfElabHM ctx bindings (monos.map RecSpec.mono) G L)
    (hopen : ∀ Ys, FreshNames (L ++ G) G.length Ys →
      ∀ p ∈ bindings.zip bindings',
        p.2.openTyVars Ys = retargetVars (specsMono (monos.map RecSpec.mono)) (Ys.map Ty.fvar) 0 p.1) :
    RecSpecs.PolyTyped TypeOfElabHM ctx bindings'
      (monos.map (fun μ => RecSpec.poly (promoteScheme G μ))) [] (L ++ G) := by
  intro Xs hfXs p hp σ hσ Ys hfYs
  obtain rfl : Xs = [] := List.eq_nil_of_length_eq_zero hfXs.length
  rcases List.zip_mem_getElem hp with ⟨k, hkbs', hks, hp1, hp2⟩
  have hkMonos : k < monos.length := by simpa [List.length_map] using hks
  have hkBind : k < bindings.length := by simpa [hlen] using hkMonos
  have hmonoElem : (monos.map (fun μ : Ty => RecSpec.poly (promoteScheme G μ)))[k]
      = RecSpec.poly (promoteScheme G (monos[k])) := by
    simp
  have hσ' : σ = promoteScheme G (monos[k]) := by
    apply RecSpec.poly.inj
    exact hσ.symm.trans (hp2.trans hmonoElem)
  have hfYs' : FreshNames (L ++ G) G.length Ys := by
    simpa [hσ', List.append_nil, promoteScheme] using hfYs
  have hdisj : ∀ g ∈ G, g ∉ Ys := by
    intro g hg gy
    have ha : g ∉ L ++ G := hfYs'.avoid g gy
    exact ha (List.mem_append_right _ hg)
  have hFreshL : FreshNames L G.length Ys := ⟨hfYs'.length, hfYs'.nodup, by
    intro y hy hL
    exact hfYs'.avoid y hy (List.mem_append_left _ hL)⟩
  have hmonoLCmem : monos[k] ∈ monos := List.getElem_mem hkMonos
  have hmonoPair : (bindings[k], RecSpec.mono (monos[k])) ∈
      bindings.zip (monos.map RecSpec.mono) := by
    have hkmap : k < (monos.map RecSpec.mono).length := by simpa [List.length_map] using hkMonos
    simpa [List.getElem_map] using List.getElem_mem_zip hkBind hkmap
  have hpair : (bindings[k], bindings'[k]) ∈ bindings.zip bindings' := by
    exact List.getElem_mem_zip hkBind hkbs'
  have hmono_der : TypeOfElabHM
      ⟨(monos.map RecSpec.mono).map (RecSpec.rhsEntry G Ys) ++ ctx.env, ctx.ctors⟩
      (bindings[k]) (Ty.renameG G Ys (monos[k])) := by
    simpa [RecSpecs.rhsCtx] using
      hmono Ys hFreshL (bindings[k], RecSpec.mono (monos[k])) hmonoPair (monos[k]) rfl
  have hmonoLC' : ∀ τ, RecSpec.mono τ ∈ monos.map RecSpec.mono → τ.IsLC := by
    intro τ hτ
    obtain ⟨μ, hμ, heq⟩ := List.mem_map.mp hτ
    exact (RecSpec.mono.inj heq) ▸ (hmonoLC μ hμ)
  have htrans := retarget_transport (specs := monos.map RecSpec.mono) (G := G) (Xs := Ys)
    hGnodup hfYs'.length hdisj hmonoLC' hmono_der
  rw [hp1, hσ']
  rw [hopen Ys hfYs' (bindings[k], bindings'[k]) hpair]
  rw [promoteScheme_openVars (hmonoLC (monos[k]) hmonoLCmem) hGnodup hfYs'.length hdisj]
  simpa only [RecSpecs.rhsCtx, RecSpec.rhsEntry, List.map_map, List.length_map,
    promoteSpecs_rhsEntry] using htrans

/-! ## The converse (poly → mono)

`monoTyped_to_polyTyped` promotes mono → poly. The headline reason to do this refactor is that
with elaboration shape-preserving, `Infer.sourceSound` should stop being a second full induction
and become a corollary of `Infer.sound` via a decoration-forgetting faithfulness lemma
`Decorates e e' → TypeOfElabHM ctx e' τ → TypeOfHM ctx e τ`.

That lemma needs the CONVERSE of `monoTyped_to_polyTyped` at `letRec`. The converse is true, but
it is not automatic: it requires two hypotheses that a first attempt will omit, so they are
stated explicitly and documented here.

**Why the converse is not vacuous.** The source node keeps `anns = none` for unannotated
members, and `RecSpecs.WF.anns_eq` forces those specs to be `.mono` — so a source derivation
*must* use `MonoTyped`, where every sibling use sits at one shared monotype. An arbitrary
elaborated derivation of the promoted (all-`poly`) node looks as though it could instantiate a
sibling at *different* types in different places, which `MonoTyped` cannot express. That
objection does not in fact bite, for a reason worth recording: `TypeOfElabHM` reads `tyArgs`
from the *term*, and `retargetVars` assigns *every* in-window use the *same* `Vs`, so the term
itself pins one shared instance per sibling — exactly what `MonoTyped` says. Type-passing, the
feature that causes much of the complexity elsewhere, is what makes the converse hold.

Two hypotheses are still needed, both easy to miss:

- **(length)** the promoted and source binding lists must have equal length
  (`hlen' : bindings'.length = bindings.length`); otherwise the poly derivation cannot be
  indexed at member `k`.
- **(source `tyArgs`)** `retargetVars` *overwrites* `tyArgs`, so the retarget does not constrain
  the *source*'s group-use `tyArgs` at all: a source binding carrying `.var 1 [int]` maps to the
  same retargeted term as one carrying `.var 1 []`, but only the latter can be `MonoTyped`
  (arity 0). This is expressed by requiring that retargeting to `[]` is the identity on the
  source bindings (`hsrcNil`), i.e. every in-window use already carries `[]`.

Provided the faithfulness lemma's `Decorates` relation is *tight* at `letRec` (uniform `tyArgs`
on group-member uses — which is what `Infer` produces), the converse makes `Infer.sourceSound` a
decoration-forgetting corollary. -/

/-- The converse of `monoTyped_to_polyTyped`: a `PolyTyped` derivation at the promoted schemes
    yields the `MonoTyped` derivation the source node requires, given the length relation
    (`hlen'`) and the source-`tyArgs` condition (`hsrcNil`) documented above. -/
theorem polyTyped_to_monoTyped
    {ctx : Ctx} {bindings bindings' : List Expr} {monos : List Ty} {G L : List Nat}
    (hGnodup : G.Nodup)
    (hmonoLC : ∀ μ ∈ monos, μ.IsLC)
    (hlen' : bindings'.length = bindings.length)
    (hsrcNil : ∀ e ∈ bindings, retargetVars (specsMono (monos.map RecSpec.mono)) [] 0 e = e)
    (hpoly : RecSpecs.PolyTyped TypeOfElabHM ctx bindings'
      (monos.map (fun μ => RecSpec.poly (promoteScheme G μ))) [] (L ++ G))
    (hopen : ∀ Ys, FreshNames (L ++ G) G.length Ys →
      ∀ p ∈ bindings.zip bindings',
        p.2.openTyVars Ys
          = retargetVars (specsMono (monos.map RecSpec.mono)) (Ys.map Ty.fvar) 0 p.1) :
    RecSpecs.MonoTyped TypeOfElabHM ctx bindings (monos.map RecSpec.mono) G (L ++ G) := by
  intro Xs hfXs p hp τ hτ
  rcases List.zip_mem_getElem hp with ⟨k, hkBind, hkSpec, hp1, hp2⟩
  have hkMonos : k < monos.length := by simpa [List.length_map] using hkSpec
  have hkbs' : k < bindings'.length := by rw [hlen']; exact hkBind
  have hτk : τ = monos[k] := by
    apply RecSpec.mono.inj
    calc
      .mono τ = p.2 := hτ.symm
      _ = (monos.map RecSpec.mono)[k] := hp2
      _ = .mono (monos[k]) := by simp
  subst hτk
  have hmemMonos : monos[k] ∈ monos := List.getElem_mem hkMonos
  have hkPoly : k < (monos.map (fun μ => RecSpec.poly (promoteScheme G μ))).length := by
    simpa [List.length_map] using hkMonos
  have hpairPoly : (bindings'[k], RecSpec.poly (promoteScheme G (monos[k]))) ∈
      bindings'.zip (monos.map (fun μ => RecSpec.poly (promoteScheme G μ))) := by
    simpa [List.getElem_map] using List.getElem_mem_zip hkbs' hkPoly
  have hpair : (bindings[k], bindings'[k]) ∈ bindings.zip bindings' :=
    List.getElem_mem_zip hkBind hkbs'
  have hfXs' : FreshNames (L ++ G) 0 [] := ⟨rfl, List.nodup_nil, by intro x hx; simp at hx⟩
  have hfYs : FreshNames ((L ++ G) ++ []) G.length Xs :=
    ⟨hfXs.length, hfXs.nodup, fun x hx hc => hfXs.avoid x hx (by simpa using hc)⟩
  have hpolyD : TypeOfElabHM (RecSpecs.rhsCtx ctx
      (monos.map (fun μ => RecSpec.poly (promoteScheme G μ))) [] [])
      (bindings'[k].openTyVars Xs) ((promoteScheme G (monos[k])).openVars Xs) :=
    hpoly [] hfXs' (bindings'[k], RecSpec.poly (promoteScheme G (monos[k]))) hpairPoly
      (promoteScheme G (monos[k])) rfl Xs hfYs
  have hdisj : ∀ g ∈ G, g ∉ Xs := by
    intro g hg gx
    have hgX : g ∈ L ++ G := List.mem_append_right _ hg
    exact hfXs.avoid g gx hgX
  have hopenD : (bindings'[k]).openTyVars Xs
      = retargetVars (specsMono (monos.map RecSpec.mono)) (Xs.map Ty.fvar) 0 (bindings[k]) :=
    hopen Xs hfXs (bindings[k], bindings'[k]) hpair
  have hpolyD' : TypeOfElabHM
      ⟨(promoteSpecs G (monos.map RecSpec.mono)).map (RecSpec.rhsEntry G Xs) ++ ctx.env, ctx.ctors⟩
      (retargetVars (specsMono (monos.map RecSpec.mono)) (Xs.map Ty.fvar) 0 (bindings[k]))
      (Ty.renameG G Xs (monos[k])) := by
    simpa only [RecSpecs.rhsCtx, RecSpec.rhsEntry, List.map_map, hopenD, promoteSpecs,
      promoteScheme_openVars (hmonoLC (monos[k]) hmemMonos) hGnodup hfXs.length hdisj] using hpolyD
  have hmonoLC' : ∀ τ, RecSpec.mono τ ∈ monos.map RecSpec.mono → τ.IsLC := by
    intro τ hτ
    obtain ⟨μ, hμ, heq⟩ := List.mem_map.mp hτ
    exact (RecSpec.mono.inj heq) ▸ (hmonoLC μ hμ)
  have huntrans := retarget_untransport (specs := monos.map RecSpec.mono) (G := G) (Xs := Xs)
    hGnodup hfXs.length hdisj hmonoLC' hpolyD'
  have hsrc : retargetVars (specsMono (monos.map RecSpec.mono)) [] 0 (bindings[k]) = bindings[k] :=
    hsrcNil (bindings[k]) (List.getElem_mem hkBind)
  rw [hp1]
  simpa only [RecSpecs.rhsCtx, RecSpec.rhsEntry, List.map_map, List.length_map, hsrc] using huntrans

/-! ## Preservation for a promoted group

The promotion changes neither `Expr`, nor `SmallStep.Step`, nor `TypeOfElabHM`. A promoted
`letRec` is an ordinary well-typed term of the existing language, so the *already-proved*
`TypeOfElabHM.preservation` (`Core.lean:9442`) applies to it directly — no new metatheory. The
theorem here makes that concrete: preservation for a promoted group is a one-line application of
the general lemma. -/

open SmallStep (Step) in

theorem promoted_preservation {e' : Expr}
    (hstep : Step
      (.letRec [some σA, some σA]
        [.lambda none (.app (.var 2 [.bvar 0, .bvar 1]) (.var 0 [])),
         .lambda none (.app (.var 1 [.bvar 0, .bvar 1]) (.var 0 []))]
        (.var 0 [.prim .int, .prim .int])) e') :
    TypeOfElabHM ⟨[], []⟩ e' (.arrow (.prim .int) (.prim .int)) :=
  TypeOfElabHM.preservation hstep mutual_promoted

/-! ## The stored-form retarget

`retargetVars` works on *opened* terms (`Vs` concrete, depth-independent). The real elaborator
must emit the **stored** form, with `Ty.bvarRangeFrom d |G|` at type-binder depth `d`. The
commute lemma at the end of this section is exactly what discharges `monoTyped_to_polyTyped` /
`polyTyped_to_monoTyped`'s `hopen` hypothesis, after which the transport chain is closed end to
end. -/

mutual

def retargetStored (mono : Nat → Bool) (gLen : Nat) (d b : Nat) : Expr → Expr
  | .primLit p          => .primLit p
  | .primBinOp op       => .primBinOp op
  | .lambda ann body    => .lambda ann (retargetStored mono gLen d (b + 1) body)
  | .app f arg          => .app (retargetStored mono gLen d b f) (retargetStored mono gLen d b arg)
  | .letIn (some σ) rhs body =>
      .letIn (some σ) (retargetStored mono gLen (d + σ.paramCount) b rhs)
        (retargetStored mono gLen d (b + 1) body)
  | .letIn none rhs body =>
      .letIn none (retargetStored mono gLen d b rhs) (retargetStored mono gLen d (b + 1) body)
  | .var i tyArgs       =>
      if b ≤ i ∧ mono (i - b) then .var i (Ty.bvarRangeFrom d gLen) else .var i tyArgs
  | .ctor c             => .ctor c
  | .match_ scrut brs   =>
      .match_ (retargetStored mono gLen d b scrut) (retargetStoredBranches mono gLen d b brs)
  | .letRec anns bs body =>
      .letRec anns (retargetStoredGroup mono gLen d (b + bs.length) anns bs)
        (retargetStored mono gLen d (b + bs.length) body)

def retargetStoredBranches (mono : Nat → Bool) (gLen : Nat) (d b : Nat) :
    List (MatchPattern × Expr) → List (MatchPattern × Expr)
  | []                  => []
  | (pat, body) :: rest =>
      (pat, retargetStored mono gLen d (b + pat.bindCount) body)
        :: retargetStoredBranches mono gLen d b rest

/-- The stored-form retarget of a recursion group's bindings, each binding descended at
    `d + RecAnn.params aⱼ` (shielding its own scheme's variables when annotated), the `anns`
    consumed in lockstep — mirroring `RecGroup.openTyVarsAux`. This is the stored-form analogue
    of `retargetGroup`.

    NOTE: the annotations must shield, so that the pool `bvar`s placed at type-depth `d` inside
    an ANNOTATED binding are opened at `d + σ.paramCount` (where the enclosing scope's vars sit
    per `Expr.openTyVarsAux`), exactly as `letIn (some σ)` shields its rhs. Without the shield
    `retargetStored_openTyVars` fails: the pool `bvar`s stay unopened. -/
def retargetStoredGroup (mono : Nat → Bool) (gLen d b : Nat) :
    List (Option PolyTy) → List Expr → List Expr
  | _,       []        => []
  | [],      e :: rest => retargetStored mono gLen d b e :: retargetStoredGroup mono gLen d b [] rest
  | a :: as, e :: rest => retargetStored mono gLen (d + RecAnn.params a) b e
      :: retargetStoredGroup mono gLen d b as rest

end

/-- Opening `bvarRangeFrom d gLen` at `d ↦ Ys` recovers `Ys` as `fvar`s — the stored-form
    retarget's `tyArgs` become exactly the opened-form retarget's `Vs`. -/
theorem bvarRangeFrom_length {d n : Nat} : (Ty.bvarRangeFrom d n).length = n := by
  induction n generalizing d with
  | zero => simp [Ty.bvarRangeFrom]
  | succ n ih => simp [Ty.bvarRangeFrom, ih (d := d + 1)]

/-- Opening the `k`-th pool binder at the same depth reads back `Ys[k]`. -/
theorem openVarsFrom_bvar_add {d k : Nat} {Ys : List Nat} (hk : k < Ys.length) :
    Ty.openVarsFrom d Ys (.bvar (d + k)) = .fvar (Ys[k]) := by
  simp [Ty.openVarsFrom, Ty.instantiate, List.getElem?_eq_getElem (by simpa using hk),
    Option.elim_some]

theorem bvarRangeFrom_openVarsFrom_map {d : Nat} {Ys : List Nat} {gLen : Nat}
    (hYsLen : Ys.length = gLen) :
    (Ty.bvarRangeFrom d gLen).map (Ty.openVarsFrom d Ys) = Ys.map Ty.fvar := by
  subst gLen
  apply List.ext_getElem
  · simp [List.length_map, bvarRangeFrom_length]
  · intro i hiL hiR
    have hiYs : i < Ys.length := by simpa using hiR
    have hbLen : i < (Ty.bvarRangeFrom d Ys.length).length := by
      simpa [List.length_map] using hiL
    have hb : (Ty.bvarRangeFrom d Ys.length)[i] = Ty.bvar (d + i) := by
      have h1 := Ty.bvarRangeFrom_getElem? Ys.length d i hiYs
      have h2 := List.getElem?_eq_getElem hbLen
      exact Option.some.inj (h2.symm.trans h1)
    rw [List.getElem_map (Ty.openVarsFrom d Ys) (h := hiL)]
    rw [hb]
    rw [List.getElem_map Ty.fvar (h := hiR)]
    exact openVarsFrom_bvar_add hiYs

/-- The general stored-form commute: at type-binder depth `d`, opening the stored retarget at
    `d ↦ Ys` is the opened retarget at `Ys`-as-`fvar`s. The mutual `retargetStored*` family is
    handled by the per-`letRec`/`match_` sub-inductions, mirroring `retargetVars_openTyVarsAux`. -/
theorem retargetStored_openTyVarsAux {mono : Nat → Bool} {gLen d b : Nat} {Ys : List Nat} {e : Expr}
    (hYsLen : Ys.length = gLen) :
    (retargetStored mono gLen d b e).openTyVarsAux d Ys
      = retargetVars mono (Ys.map Ty.fvar) b (e.openTyVarsAux d Ys) := by
  induction e using Expr.rec_strong generalizing b d with
  | primLit p => rfl
  | primBinOp op => rfl
  | ctor nm => rfl
  | var i tyArgs =>
      by_cases hwin : b ≤ i ∧ mono (i - b)
      · simp [retargetStored, retargetVars, Expr.openTyVarsAux, hwin,
          bvarRangeFrom_openVarsFrom_map hYsLen]
      · simp [retargetStored, retargetVars, Expr.openTyVarsAux, hwin]
  | lambda ann body ih =>
      simp only [retargetStored, retargetVars, Expr.openTyVarsAux,
        ih (b := b + 1) (d := d)]
  | app f arg ihf iharg =>
      simp only [retargetStored, retargetVars, Expr.openTyVarsAux,
        ihf (b := b) (d := d), iharg (b := b) (d := d)]
  | letIn ann rhs body ihr ihb =>
      cases ann with
      | none =>
          simp only [retargetStored, retargetVars, Expr.openTyVarsAux,
            ihr (b := b) (d := d), ihb (b := b + 1) (d := d)]
      | some σ =>
          simp only [retargetStored, retargetVars, Expr.openTyVarsAux,
            ihr (b := b) (d := d + σ.paramCount), ihb (b := b + 1) (d := d)]
  | match_ scrut brs ihscrut ihbrs =>
      simp only [retargetStored, retargetVars, Expr.openTyVarsAux, ihscrut (b := b) (d := d)]
      have hbrs : BranchList.openTyVarsAux d Ys (retargetStoredBranches mono gLen d b brs)
          = retargetBranches mono (Ys.map Ty.fvar) b (BranchList.openTyVarsAux d Ys brs) := by
        induction brs with
        | nil => rfl
        | cons br rest ih =>
            cases br with
            | mk pat body =>
                have hhead : (retargetStored mono gLen d (b + pat.bindCount) body).openTyVarsAux d Ys
                    = retargetVars mono (Ys.map Ty.fvar) (b + pat.bindCount)
                        (body.openTyVarsAux d Ys) :=
                  ihbrs pat body (List.mem_cons_self ..) (b := b + pat.bindCount) (d := d)
                simp only [retargetStoredBranches, retargetBranches, BranchList.openTyVarsAux]
                rw [hhead]
                congr 1
                exact ih (fun pat' e' he' => ihbrs pat' e' (List.mem_cons_of_mem _ he'))
      rw [hbrs]
  | letRec anns bs body ihbs ihbody =>
      simp only [retargetStored, retargetVars, Expr.openTyVarsAux,
        ihbody (b := b + bs.length) (d := d)]
      have hbs' : ∀ (D : Nat) (anns' : List (Option PolyTy)),
          RecGroup.openTyVarsAux d Ys anns' (retargetStoredGroup mono gLen d D anns' bs)
            = retargetGroup mono (Ys.map Ty.fvar) D (RecGroup.openTyVarsAux d Ys anns' bs) := by
        intro D anns'
        revert anns'
        induction bs with
        | nil => intro anns'; rfl
        | cons e tl ih =>
            intro anns'
            cases anns' with
            | nil =>
                simp only [retargetStoredGroup, retargetGroup, RecGroup.openTyVarsAux]
                rw [ihbs e (List.mem_cons_self ..) (b := D) (d := d)]
                congr 1
                exact ih (fun e' he' => ihbs e' (List.mem_cons_of_mem _ he')) []
            | cons a as =>
                simp only [retargetStoredGroup, retargetGroup, RecGroup.openTyVarsAux]
                rw [ihbs e (List.mem_cons_self ..) (b := D) (d := d + RecAnn.params a)]
                congr 1
                exact ih (fun e' he' => ihbs e' (List.mem_cons_of_mem _ he')) as
      rw [RecGroup.openTyVarsAux_length]
      rw [hbs' (b + bs.length) anns]

/-- The stored/open commute: opening the stored-form retarget at `Ys` gives the opened-form
    retarget at `Ys`-as-fvars. This discharges `hopen`. -/
theorem retargetStored_openTyVars {mono : Nat → Bool} {gLen b : Nat} {Ys : List Nat} {e : Expr}
    (hYsLen : Ys.length = gLen) :
    (retargetStored mono gLen 0 b e).openTyVars Ys
      = retargetVars mono (Ys.map Ty.fvar) b (e.openTyVars Ys) := by
  simpa only [Expr.openTyVars] using retargetStored_openTyVarsAux (d := 0) (hYsLen := hYsLen) (e := e)

/-! ## The body transport (spread design)

`retarget_transport` promotes the RHS environment of a recursion group (opened monotypes →
promoted schemes). The BODY, however, types at `PolyTy.genGroup G τ = ⟨|genFilter G τ|, closeOver
(genFilter G τ) τ⟩` — a member-DEPENDENT arity — while the promoted body types at
`promoteScheme G τ = ⟨|G|, closeOver G τ⟩` with the FULL pool arity. This section transports a
mono body derivation to the promoted env, extending each group-member use's `tyArgs` from
`genFilter`-arity to full-pool arity by **spreading** them into `G` order, filling the gaps
(unused pool positions) with `unit`. -/

/-- Spread `tyArgs` (in `genFilter G μ` order) into `G` order: at each pool position `g`, if
    `g ∈ μ.freeVars` consume the next `tyArgs` element, else emit `unit`. Invariant (assumed):
    `tyArgs.length = (Ty.genFilter G μ).length`. -/
def spreadTyArgs (G : List Nat) (μ : Ty) (tyArgs : List Ty) : List Ty :=
  match G with
  | [] => []
  | g :: gs =>
      if g ∈ μ.freeVars then
        match tyArgs with
        | [] => Ty.prim .unit :: spreadTyArgs gs μ []
        | t :: ts => t :: spreadTyArgs gs μ ts
      else
        Ty.prim .unit :: spreadTyArgs gs μ tyArgs

mutual

/-- Extend each mono-member `var`'s `tyArgs` from `genGroup G` (filtered) arity to
    `promoteScheme G` (full pool) arity via the spread. `b` is term-binder depth; mono members
    occupy de Bruijn indices `[b, b + monos.length)`. -/
def bodyExtend (monos : List Ty) (G : List Nat) (b : Nat) : Expr → Expr
  | .primLit p          => .primLit p
  | .primBinOp op       => .primBinOp op
  | .lambda ann body    => .lambda ann (bodyExtend monos G (b + 1) body)
  | .app f arg          => .app (bodyExtend monos G b f) (bodyExtend monos G b arg)
  | .letIn ann rhs body => .letIn ann (bodyExtend monos G b rhs) (bodyExtend monos G (b + 1) body)
  | .var i tyArgs       =>
      if b ≤ i ∧ i < b + monos.length then
        .var i (spreadTyArgs G (monos.getD (i - b) (Ty.prim .unit)) tyArgs)
      else .var i tyArgs
  | .ctor c             => .ctor c
  | .match_ scrut brs   => .match_ (bodyExtend monos G b scrut) (bodyExtendBranches monos G b brs)
  | .letRec anns bs body => .letRec anns (bodyExtendGroup monos G (b + bs.length) bs) (bodyExtend monos G (b + bs.length) body)

def bodyExtendBranches (monos : List Ty) (G : List Nat) (b : Nat) :
    List (MatchPattern × Expr) → List (MatchPattern × Expr)
  | []                  => []
  | (pat, body) :: rest => (pat, bodyExtend monos G (b + pat.bindCount) body) :: bodyExtendBranches monos G b rest

def bodyExtendGroup (monos : List Ty) (G : List Nat) (b : Nat) : List Expr → List Expr
  | []        => []
  | e :: rest => bodyExtend monos G b e :: bodyExtendGroup monos G b rest
end

/-- `bodyExtendGroup` preserves lengths. -/
theorem bodyExtendGroup_length {monos : List Ty} {G : List Nat} {b : Nat} (bs : List Expr) :
    (bodyExtendGroup monos G b bs).length = bs.length := by
  induction bs with
  | nil => rfl
  | cons e tl ih => simp only [bodyExtendGroup, List.length_cons, ih]

/-- Retargeting preserves non-emptiness of the branch list. -/
theorem bodyExtendBranches_ne_nil {monos : List Ty} {G : List Nat} {b : Nat}
    {brs : List (MatchPattern × Expr)} (h : brs ≠ []) :
    bodyExtendBranches monos G b brs ≠ [] := by
  intro h'
  cases brs with
  | nil => exact h rfl
  | cons br rest =>
      simp only [bodyExtendBranches, List.cons_ne_nil] at h'

/-- Every extended branch is the extension of an original branch (pattern kept). -/
theorem bodyExtendBranches_mem {monos : List Ty} {G : List Nat} {b : Nat} :
    ∀ (brs : List (MatchPattern × Expr)) (br' : MatchPattern × Expr),
      br' ∈ bodyExtendBranches monos G b brs →
        ∃ pat body, (pat, body) ∈ brs ∧ br' = (pat, bodyExtend monos G (b + pat.bindCount) body) := by
  intro brs br' hmem
  induction brs with
  | nil =>
      simp [bodyExtendBranches] at hmem
  | cons br rest ih =>
      cases br with
      | mk pat body =>
          simp only [bodyExtendBranches, List.mem_cons] at hmem
          rcases hmem with hmem | hmem
          · subst hmem
            exact ⟨pat, body, List.mem_cons_self .., rfl⟩
          · rcases ih hmem with ⟨pat', body', hmem', heq⟩
            exact ⟨pat', body', List.mem_cons_of_mem _ hmem', heq⟩

/-- Every pair of the extended-zip is the extension of a pair of the original zip. -/
theorem bodyExtendGroup_zip_mem {monos : List Ty} {G : List Nat} {b : Nat} :
    ∀ (bs : List Expr) (specs : List RecSpec) (p : Expr × RecSpec),
      p ∈ (bodyExtendGroup monos G b bs).zip specs →
        ∃ q, q ∈ bs.zip specs ∧ p.1 = bodyExtend monos G b q.1 ∧ p.2 = q.2 := by
  intro bs specs p hp
  revert hp specs
  induction bs with
  | nil =>
      intro specs hp
      simp [bodyExtendGroup, List.zip_nil_left] at hp
  | cons e tl ih =>
      intro specs hp
      cases specs with
      | nil =>
          simp [bodyExtendGroup, List.zip_nil_right] at hp
      | cons s ss =>
          simp only [bodyExtendGroup, List.zip_cons_cons, List.mem_cons] at hp
          rcases hp with hp | hp
          · subst hp
            exact ⟨(e, s), List.mem_cons_self .., rfl, rfl⟩
          · rcases ih ss hp with ⟨q, hq, h1, h2⟩
            exact ⟨q, List.mem_cons_of_mem _ hq, h1, h2⟩

/-! ### Spread bookkeeping -/

/-- The spread emits exactly one argument per pool position. -/
theorem spreadTyArgs_length {G : List Nat} {μ : Ty} {tyArgs : List Ty}
    (hlen : tyArgs.length = (Ty.genFilter G μ).length) :
    (spreadTyArgs G μ tyArgs).length = G.length := by
  induction G generalizing tyArgs with
  | nil => simp [spreadTyArgs]
  | cons g gs ih =>
      by_cases hg : g ∈ μ.freeVars
      · have hglen : (Ty.genFilter (g :: gs) μ).length = (Ty.genFilter gs μ).length + 1 := by
          unfold Ty.genFilter
          simp [hg]
        have hlen' : tyArgs.length = (Ty.genFilter gs μ).length + 1 := by
          omega
        cases tyArgs with
        | nil =>
            have hzero : (0 : Nat) = (Ty.genFilter gs μ).length + 1 := by
              exact hlen'
            omega
        | cons t ts =>
            have hlen'' : ts.length = (Ty.genFilter gs μ).length := by
              have h' : ts.length + 1 = (Ty.genFilter gs μ).length + 1 := by
                simpa using hlen'
              omega
            conv_lhs => rw [spreadTyArgs.eq_def]
            simp [hg]
            rw [ih (tyArgs := ts) hlen'']
      · have hlen' : tyArgs.length = (Ty.genFilter gs μ).length := by
          have h := hlen
          unfold Ty.genFilter at h
          simp [hg] at h
          simpa [Ty.genFilter] using h
        conv_lhs => rw [spreadTyArgs.eq_def]
        simp [hg]
        rw [ih (tyArgs := tyArgs) hlen']

/-- Opening the spread's gap-filling `unit`s is a no-op, so opening the spread pointwise is
    spreading the pointwise-opening. -/
theorem spreadTyArgs_map_openVarsFrom {G : List Nat} {μ : Ty} {d : Nat} {Ys : List Nat}
    {tyArgs : List Ty} :
    (spreadTyArgs G μ tyArgs).map (Ty.openVarsFrom d Ys)
      = spreadTyArgs G μ (tyArgs.map (Ty.openVarsFrom d Ys)) := by
  induction G generalizing tyArgs with
  | nil => simp [spreadTyArgs]
  | cons g gs ih =>
      by_cases hg : g ∈ μ.freeVars
      · cases tyArgs with
        | nil =>
            have hfun : Ty.openVarsFrom d Ys (Ty.prim .unit) = Ty.prim .unit := by
              rfl
            conv_lhs => rw [spreadTyArgs.eq_def]
            conv_rhs => rw [spreadTyArgs.eq_def]
            simp [hg, hfun]
            rw [ih (tyArgs := [])]
            simp
        | cons t ts =>
            conv_lhs => rw [spreadTyArgs.eq_def]
            conv_rhs => rw [spreadTyArgs.eq_def]
            simp [hg]
            rw [ih (tyArgs := ts)]
      · have hfun : Ty.openVarsFrom d Ys (Ty.prim .unit) = Ty.prim .unit := by
          rfl
        conv_lhs => rw [spreadTyArgs.eq_def]
        conv_rhs => rw [spreadTyArgs.eq_def]
        simp [hg, hfun]
        rw [ih (tyArgs := tyArgs)]

/-- The spread preserves local-closedness: its elements are either original `tyArgs` elements
    or `unit`. -/
theorem spreadTyArgs_lc {G : List Nat} {μ : Ty} {tyArgs : List Ty}
    (hlc : ∀ t ∈ tyArgs, t.IsLC) :
    ∀ t ∈ spreadTyArgs G μ tyArgs, t.IsLC := by
  induction G generalizing tyArgs with
  | nil => simp [spreadTyArgs]
  | cons g gs ih =>
      by_cases hg : g ∈ μ.freeVars
      · cases tyArgs with
        | nil =>
            intro t ht
            have hstep : spreadTyArgs (g :: gs) μ [] = Ty.prim .unit :: spreadTyArgs gs μ [] := by
              conv_lhs => rw [spreadTyArgs.eq_def]
              simp [hg]
            rw [hstep] at ht
            simp [List.mem_cons] at ht
            rcases ht with h1 | h2
            · rw [h1]
              exact .prim
            · exact ih (tyArgs := []) (fun t' ht' => False.elim (List.not_mem_nil ht')) t h2
        | cons t ts =>
            intro t' ht'
            have hstep : spreadTyArgs (g :: gs) μ (t :: ts) = t :: spreadTyArgs gs μ ts := by
              conv_lhs => rw [spreadTyArgs.eq_def]
              simp [hg]
            rw [hstep] at ht'
            simp [List.mem_cons] at ht'
            rcases ht' with h1 | h2
            · rw [h1]
              exact hlc t (List.mem_cons_self ..)
            · exact ih (tyArgs := ts) (fun u hu => hlc u (List.mem_cons_of_mem _ hu)) t' h2
      · intro t ht
        have hstep : spreadTyArgs (g :: gs) μ tyArgs = Ty.prim .unit :: spreadTyArgs gs μ tyArgs := by
          conv_lhs => rw [spreadTyArgs.eq_def]
          simp [hg]
        rw [hstep] at ht
        simp [List.mem_cons] at ht
        rcases ht with h1 | h2
        · rw [h1]
          exact .prim
        · exact ih (tyArgs := tyArgs) hlc t h2

/-- The spread at an in-`G`-freeVar position is the corresponding (filtered-order) `tyArgs`
    element. -/
private theorem spreadTyArgs_getElem {G : List Nat} {μ : Ty} {tyArgs : List Ty}
    (hlen : tyArgs.length = (Ty.genFilter G μ).length) :
    ∀ (i : Nat) (hi : i < G.length), G[i]'hi ∈ μ.freeVars →
      ∃ (j : Nat) (hj : j < tyArgs.length),
        (Ty.genFilter G μ)[j]? = some (G[i]'hi) ∧
        (spreadTyArgs G μ tyArgs)[i]? = some (tyArgs[j]'hj) := by
  induction G generalizing tyArgs with
  | nil => intro i hi hg; simp at hi
  | cons g gs ih =>
      intro i hi hg
      by_cases hg0 : g ∈ μ.freeVars
      · have hglen : (Ty.genFilter (g :: gs) μ).length = (Ty.genFilter gs μ).length + 1 := by
          unfold Ty.genFilter
          simp [hg0]
        have hlen' : tyArgs.length = (Ty.genFilter gs μ).length + 1 := by
          omega
        cases tyArgs with
        | nil =>
            have hzero : (0 : Nat) = (Ty.genFilter gs μ).length + 1 := by
              exact hlen'
            omega
        | cons t ts =>
            have hlen'' : ts.length = (Ty.genFilter gs μ).length := by
              have h' : ts.length + 1 = (Ty.genFilter gs μ).length + 1 := by
                simpa using hlen'
              omega
            cases i with
            | zero =>
                refine ⟨0, ?_, ?_, ?_⟩
                · omega
                · simp [Ty.genFilter, hg0]
                · simp [spreadTyArgs, hg0]
            | succ i' =>
                have hi' : i' < gs.length := by
                  have := hi
                  simp at this
                  exact this
                have hg' : gs[i'] ∈ μ.freeVars := by simpa using hg
                rcases ih (tyArgs := ts) hlen'' i' hi' hg' with ⟨j', hj', hgetj', hval'⟩
                refine ⟨j' + 1, ?_, ?_, ?_⟩
                · omega
                · simpa [Ty.genFilter, hg0] using hgetj'
                · simpa [spreadTyArgs, hg0] using hval'
      · have hlen' : tyArgs.length = (Ty.genFilter gs μ).length := by
          have h := hlen
          unfold Ty.genFilter at h
          simp [hg0] at h
          simpa [Ty.genFilter] using h
        cases i with
        | zero =>
            have : g ∈ μ.freeVars := by simpa using hg
            exact False.elim (hg0 this)
        | succ i' =>
            have hi' : i' < gs.length := by
              have := hi
              simp at this
              exact this
            have hg' : gs[i'] ∈ μ.freeVars := by simpa using hg
            rcases ih (tyArgs := tyArgs) hlen' i' hi' hg' with ⟨j', hj', hgetj', hval'⟩
            refine ⟨j', ?_, ?_, ?_⟩
            · exact hj'
            · simpa [Ty.genFilter, hg0] using hgetj'
            · simpa [spreadTyArgs, hg0] using hval'

/-- For a nodup list, `idxOf?` of the element at index `i` is `some i`. -/
private theorem List.idxOf?_getElem_self {α : Type*} [BEq α] [LawfulBEq α]
    {l : List α} (hnd : l.Nodup) {i : Nat} (hi : i < l.length) :
    l.idxOf? l[i] = some i := by
  induction l generalizing i with
  | nil => simp at hi
  | cons x xs ih =>
      rw [List.nodup_cons] at hnd
      cases i with
      | zero => simp [List.idxOf?_cons]
      | succ j =>
          have hj : j < xs.length := by simpa using hi
          have hxne : (x == xs[j]) = false := by
            have hmem : xs[j] ∈ xs := List.getElem_mem hj
            have hxnot : x ∉ xs := hnd.1
            exact beq_eq_false_iff_ne.mpr (fun h => hxnot (h ▸ hmem))
          simp [List.idxOf?_cons, hxne, ih hnd.2 hj]

/-- `closeOver` over a list of types is the pointwise map. -/
private theorem TyList.closeOver_eq_map (gs : List Nat) (tys : List Ty) :
    TyList.closeOver gs tys = tys.map (Ty.closeOver gs) := by
  induction tys with
  | nil => rfl
  | cons hd tl ih => simp [TyList.closeOver, ih]

/-- The pivotal type-level fact. Substituting the spread over the full pool restricts to
    substituting over the filtered pool: opening the full-pool `closeOver` at the spread is
    opening the filtered `closeOver` at the original `tyArgs`. -/
theorem spreadTyArgs_renameG {G : List Nat} {μ : Ty} {tyArgs : List Ty}
    (hG : G.Nodup) (hlen : tyArgs.length = (Ty.genFilter G μ).length) (hLC : μ.IsLC) :
    Ty.openWith (spreadTyArgs G μ tyArgs) (Ty.closeOver G μ)
      = Ty.openWith tyArgs (Ty.closeOver (Ty.genFilter G μ) μ) := by
  -- generalise to subterms `τ` whose free vars are all in `μ`'s (the spread consumes based on
  -- the WHOLE `μ`, so subterms share the full `G`-spread / filtered-`μ` index spaces)
  have aux : ∀ τ : Ty, (∀ n ∈ τ.freeVars, n ∈ μ.freeVars) → τ.IsLC →
      Ty.openWith (spreadTyArgs G μ tyArgs) (Ty.closeOver G τ)
        = Ty.openWith tyArgs (Ty.closeOver (Ty.genFilter G μ) τ) := by
    intro τ
    induction τ using Ty.rec_strong with
    | prim p =>
        intro hsub hLC
        rfl
    | bvar i =>
        intro hsub hLC
        exfalso
        cases hLC with
        | bvar hlt => omega
    | fvar n =>
        intro hsub hLC
        have hn : n ∈ μ.freeVars := hsub n (by simp [Ty.freeVars])
        by_cases hnG : n ∈ G
        · rcases List.mem_iff_getElem?.mp hnG with ⟨i, hGi?⟩
          rcases List.getElem?_eq_some_iff.mp hGi? with ⟨hi, hgeti⟩
          have hg : G[i]'hi ∈ μ.freeVars := by simpa [hgeti] using hn
          have hGidx : G.idxOf? n = some i := by
            have h := List.idxOf?_getElem_self hG hi
            simpa [hgeti] using h
          rcases spreadTyArgs_getElem hlen i hi hg with ⟨j, hj, hgetj, hval⟩
          rcases List.getElem?_eq_some_iff.mp hgetj with ⟨hjG, hgetj'⟩
          have hGFnodup : (Ty.genFilter G μ).Nodup := by
            simpa [Ty.genFilter] using (List.Nodup.filter (fun g : Nat => decide (g ∈ μ.freeVars)) hG)
          have hGjidx : (Ty.genFilter G μ).idxOf? n = some j := by
            have h := List.idxOf?_getElem_self hGFnodup hjG
            simpa [hgeti, hgetj'] using h
          rw [Ty.closeOver.eq_6, hGidx, Ty.closeOver.eq_6, hGjidx]
          simp [Ty.openWith, Ty.instantiate, hval, List.getElem?_eq_getElem hj]
        · have hnGidx : G.idxOf? n = none := List.idxOf?_eq_none_iff.mpr hnG
          have hnGF : n ∉ Ty.genFilter G μ := fun hg => hnG (Ty.mem_of_mem_genFilter hg)
          have hnGFidx : (Ty.genFilter G μ).idxOf? n = none := List.idxOf?_eq_none_iff.mpr hnGF
          rw [Ty.closeOver.eq_6, hnGidx, Ty.closeOver.eq_6, hnGFidx]
          rfl
    | arrow a b iha ihb =>
        intro hsub hLC
        have hsub_a : ∀ n ∈ a.freeVars, n ∈ μ.freeVars := fun n hn =>
          hsub n (by
            simp only [Ty.freeVars, List.mem_dedup, List.mem_append]
            exact Or.inl hn)
        have hsub_b : ∀ n ∈ b.freeVars, n ∈ μ.freeVars := fun n hn =>
          hsub n (by
            simp only [Ty.freeVars, List.mem_dedup, List.mem_append]
            exact Or.inr hn)
        cases hLC with
        | arrow hLCa hLCb =>
            rw [show Ty.closeOver G (Ty.arrow a b) = Ty.arrow (Ty.closeOver G a) (Ty.closeOver G b) by rfl]
            rw [show Ty.closeOver (Ty.genFilter G μ) (Ty.arrow a b)
                = Ty.arrow (Ty.closeOver (Ty.genFilter G μ) a) (Ty.closeOver (Ty.genFilter G μ) b) by rfl]
            rw [show Ty.openWith (spreadTyArgs G μ tyArgs)
                  (Ty.arrow (Ty.closeOver G a) (Ty.closeOver G b))
                  = Ty.arrow (Ty.openWith (spreadTyArgs G μ tyArgs) (Ty.closeOver G a))
                      (Ty.openWith (spreadTyArgs G μ tyArgs) (Ty.closeOver G b)) by
                simp [Ty.openWith, Ty.instantiate]]
            rw [show Ty.openWith tyArgs
                  (Ty.arrow (Ty.closeOver (Ty.genFilter G μ) a) (Ty.closeOver (Ty.genFilter G μ) b))
                  = Ty.arrow (Ty.openWith tyArgs (Ty.closeOver (Ty.genFilter G μ) a))
                      (Ty.openWith tyArgs (Ty.closeOver (Ty.genFilter G μ) b)) by
                simp [Ty.openWith, Ty.instantiate]]
            rw [iha hsub_a hLCa, ihb hsub_b hLCb]
    | customTy nm tys ih =>
        intro hsub hLC
        have hsub_t : ∀ t ∈ tys, ∀ n ∈ t.freeVars, n ∈ μ.freeVars := fun t ht n hn =>
          hsub n (TyList.mem_freeVars_iff.mpr ⟨t, ht, hn⟩)
        cases hLC with
        | customTy hball =>
            rw [show Ty.closeOver G (Ty.customTy nm tys)
                = Ty.customTy nm (tys.map (Ty.closeOver G)) by
                simp [Ty.closeOver, TyList.closeOver_eq_map]]
            rw [show Ty.closeOver (Ty.genFilter G μ) (Ty.customTy nm tys)
                = Ty.customTy nm (tys.map (Ty.closeOver (Ty.genFilter G μ))) by
                simp [Ty.closeOver, TyList.closeOver_eq_map]]
            rw [show Ty.openWith (spreadTyArgs G μ tyArgs) (Ty.customTy nm (tys.map (Ty.closeOver G)))
                  = Ty.customTy nm (tys.map (Ty.openWith (spreadTyArgs G μ tyArgs) ∘ Ty.closeOver G)) by
                simp [Ty.openWith, Ty.instantiate, TyList.instantiate_eq_map]]
            rw [show Ty.openWith tyArgs (Ty.customTy nm (tys.map (Ty.closeOver (Ty.genFilter G μ))))
                  = Ty.customTy nm (tys.map (Ty.openWith tyArgs ∘ Ty.closeOver (Ty.genFilter G μ))) by
                simp [Ty.openWith, Ty.instantiate, TyList.instantiate_eq_map]]
            congr 1
            apply List.map_congr_left
            intro t ht
            exact ih t ht (hsub_t t ht) (hball t ht)
    | bl lo hi e ih =>
        intro hsub hLC
        cases hLC with
        | bl hLCe =>
            rw [show Ty.closeOver G (Ty.bl lo hi e) = Ty.bl lo hi (Ty.closeOver G e) by rfl]
            rw [show Ty.closeOver (Ty.genFilter G μ) (Ty.bl lo hi e)
                = Ty.bl lo hi (Ty.closeOver (Ty.genFilter G μ) e) by rfl]
            rw [show Ty.openWith (spreadTyArgs G μ tyArgs) (Ty.bl lo hi (Ty.closeOver G e))
                  = Ty.bl lo hi (Ty.openWith (spreadTyArgs G μ tyArgs) (Ty.closeOver G e)) by
                simp [Ty.openWith, Ty.instantiate]]
            rw [show Ty.openWith tyArgs (Ty.bl lo hi (Ty.closeOver (Ty.genFilter G μ) e))
                  = Ty.bl lo hi (Ty.openWith tyArgs (Ty.closeOver (Ty.genFilter G μ) e)) by
                simp [Ty.openWith, Ty.instantiate]]
            rw [ih (fun n hn => hsub n (by simpa [Ty.freeVars] using hn)) hLCe]
  exact aux μ (fun n hn => hn) hLC

/-! ### Opening the body transport commutes with opening -/

/-- Opening a scheme body with LC args is an instantiation by those args. -/
theorem InstantiatesBy.openWith {Vs : List Ty} {n : Nat} {ty : Ty}
    (hbv : ContainsBvarsUpTo n ty) (hn : n ≤ Vs.length) :
    InstantiatesBy Vs ty (Ty.openWith Vs ty) := by
  induction ty using Ty.rec_strong with
  | prim p => exact .prim
  | fvar m => exact .fvar
  | bvar i =>
      cases hbv with
      | bvar hlt =>
        have hi : i < Vs.length := by omega
        simp only [Ty.openWith, Ty.instantiate, List.getElem?_eq_getElem hi, Option.getD_some]
        exact .bvar (List.getElem?_eq_getElem hi)
  | arrow a b iha ihb => cases hbv with | arrow ha hb => exact .arrow (iha ha) (ihb hb)
  | customTy nm tys ih =>
      cases hbv with
      | customTy hball =>
        simp only [Ty.openWith, Ty.instantiate, TyList.instantiate_eq_map]
        exact .customTy (forall₂_self_map (fun t ht => ih t ht (hball t ht)))
  | bl lo hi e ih =>
      cases hbv with
      | bl he =>
        simp only [Ty.openWith, Ty.instantiate]
        exact .bl (ih he)

/-- Extending a term commutes with opening its scoped type variables: the extension only
    reorders (and gap-fills with `unit`) the `tyArgs` of group-window `var`s, and opening only
    touches `bvar`s. -/
theorem bodyExtend_openTyVarsAux {monos : List Ty} {G : List Nat} {b d : Nat} {Ys : List Nat} {e : Expr} :
    (bodyExtend monos G b e).openTyVarsAux d Ys = bodyExtend monos G b (e.openTyVarsAux d Ys) := by
  induction e using Expr.rec_strong generalizing b d with
  | primLit p => rfl
  | primBinOp op => rfl
  | ctor nm => rfl
  | var i tyArgs =>
      by_cases hwin : b ≤ i ∧ i < b + monos.length
      · rw [show (bodyExtend monos G b (Expr.var i tyArgs)) = Expr.var i
          (spreadTyArgs G (monos.getD (i - b) (Ty.prim .unit)) tyArgs) by
          simp [bodyExtend, hwin]]
        rw [show (Expr.var i (spreadTyArgs G (monos.getD (i - b) (Ty.prim .unit)) tyArgs)).openTyVarsAux d Ys
            = Expr.var i ((spreadTyArgs G (monos.getD (i - b) (Ty.prim .unit)) tyArgs).map (Ty.openVarsFrom d Ys)) by
          rfl]
        rw [show (Expr.var i tyArgs).openTyVarsAux d Ys
            = Expr.var i (tyArgs.map (Ty.openVarsFrom d Ys)) by rfl]
        simp [bodyExtend, hwin, spreadTyArgs_map_openVarsFrom]
      · simp [bodyExtend, Expr.openTyVarsAux, hwin]
  | lambda ann body ih =>
      simp only [bodyExtend, Expr.openTyVarsAux, ih (b := b + 1) (d := d)]
  | app f arg ihf iharg =>
      simp only [bodyExtend, Expr.openTyVarsAux, ihf (b := b) (d := d), iharg (b := b) (d := d)]
  | letIn ann rhs body ihr ihb =>
      cases ann with
      | none =>
          simp only [bodyExtend, Expr.openTyVarsAux, ihr (b := b) (d := d), ihb (b := b + 1) (d := d)]
      | some σ =>
          simp only [bodyExtend, Expr.openTyVarsAux, ihr (b := b) (d := d + σ.paramCount), ihb (b := b + 1) (d := d)]
  | match_ scrut brs ihscrut ihbrs =>
      simp only [bodyExtend, Expr.openTyVarsAux, ihscrut (b := b) (d := d)]
      have hbrs : BranchList.openTyVarsAux d Ys (bodyExtendBranches monos G b brs)
          = bodyExtendBranches monos G b (BranchList.openTyVarsAux d Ys brs) := by
        induction brs with
        | nil => rfl
        | cons br rest ih =>
            cases br with
            | mk pat body =>
                have hhead : (bodyExtend monos G (b + pat.bindCount) body).openTyVarsAux d Ys
                    = bodyExtend monos G (b + pat.bindCount) (body.openTyVarsAux d Ys) :=
                  ihbrs pat body (List.mem_cons_self ..) (b := b + pat.bindCount) (d := d)
                simp only [bodyExtendBranches, BranchList.openTyVarsAux]
                rw [hhead]
                congr 1
                exact ih (fun pat' e' he' => ihbrs pat' e' (List.mem_cons_of_mem _ he'))
      rw [hbrs]
  | letRec anns bs body ihbs ihbody =>
      simp only [bodyExtend, Expr.openTyVarsAux, ihbody (b := b + bs.length) (d := d)]
      have hbs' : ∀ (D : Nat) (anns : List (Option PolyTy)),
          RecGroup.openTyVarsAux d Ys anns (bodyExtendGroup monos G D bs)
            = bodyExtendGroup monos G D (RecGroup.openTyVarsAux d Ys anns bs) := by
        intro D
        induction bs generalizing anns with
        | nil => intro anns; rfl
        | cons e tl ih =>
            intro anns
            cases anns with
            | nil =>
                simp only [bodyExtendGroup, RecGroup.openTyVarsAux]
                rw [ihbs e (List.mem_cons_self ..) (b := D) (d := d)]
                congr 1
                exact ih [] (fun e' he' => ihbs e' (List.mem_cons_of_mem _ he')) []
            | cons a as =>
                simp only [bodyExtendGroup, RecGroup.openTyVarsAux]
                rw [ihbs e (List.mem_cons_self ..) (b := D) (d := d + RecAnn.params a)]
                congr 1
                exact ih [] (fun e' he' => ihbs e' (List.mem_cons_of_mem _ he')) as
      rw [RecGroup.openTyVarsAux_length]
      rw [hbs' (b + bs.length) anns]

/-- Top-level form (`d = 0`). -/
theorem bodyExtend_openTyVars {monos : List Ty} {G : List Nat} {b : Nat} {Ys : List Nat} {e : Expr} :
    (bodyExtend monos G b e).openTyVars Ys = bodyExtend monos G b (e.openTyVars Ys) := by
  simpa only [Expr.openTyVars] using bodyExtend_openTyVarsAux (d := 0) (e := e)

/-- The `let` rule's cofinite opener commutes with the extension. -/
theorem bodyExtend_openBoundTyVars {monos : List Ty} {G : List Nat} {b : Nat} {Ys : List Nat}
    {ann : Option PolyTy} {e : Expr} :
    bodyExtend monos G b (Expr.openBoundTyVars ann Ys e)
      = Expr.openBoundTyVars ann Ys (bodyExtend monos G b e) := by
  cases ann with
  | none => rfl
  | some σ => simpa only [Expr.openBoundTyVars, Expr.openTyVars] using
      (bodyExtend_openTyVars (e := e)).symm

/-! ### The body transport theorem -/

/-- Weakening the body env from `PolyTy.genGroup G` (filtered) to `promoteScheme G`
    (full pool), spreading group-member uses' type arguments. -/
theorem bodyScheme_weaken
    {ctors : CtorEnv} {env : Env} {e : Expr} {τ : Ty}
    {monos : List Ty} {G : List Nat}
    (hGnodup : G.Nodup) (hmonoLC : ∀ μ ∈ monos, μ.IsLC)
    (h : TypeOfElabHM ⟨monos.map (PolyTy.genGroup G) ++ env, ctors⟩ e τ) :
    TypeOfElabHM ⟨monos.map (promoteScheme G) ++ env, ctors⟩
      (bodyExtend monos G 0 e) τ := by
  have H : ∀ {ctx : Ctx} {e₀ : Expr} {τ₀ : Ty}, TypeOfElabHM ctx e₀ τ₀ →
      ∀ ep : Env, ctx.env = ep ++ monos.map (PolyTy.genGroup G) ++ env →
      TypeOfElabHM ⟨ep ++ monos.map (promoteScheme G) ++ env, ctx.ctors⟩
        (bodyExtend monos G ep.length e₀) τ₀ := by
    intro ctx e₀ τ₀ hd
    induction hd using TypeOfElabHM.rec_strong with
    | primLitUnit => intro ep heq; exact .primLitUnit
    | primLitInt => intro ep heq; exact .primLitInt
    | primLitNat => intro ep heq; exact .primLitNat
    | primLitChar => intro ep heq; exact .primLitChar
    | primBinOpIntAdd => intro ep heq; exact .primBinOpIntAdd
    | primBinOpIntSub => intro ep heq; exact .primBinOpIntSub
    | primBinOpIntLt htrue hfalse ihtrue ihfalse =>
        intro ep heq
        exact .primBinOpIntLt (ihtrue ep heq) (ihfalse ep heq)
    | primBinOpCharLt htrue hfalse ihtrue ihfalse =>
        intro ep heq
        exact .primBinOpCharLt (ihtrue ep heq) (ihfalse ep heq)
    | @lambda paramTy ann bodyCtx ctx body bodyTy hpc hann heqctx hbody ihbody =>
        intro ep heq
        refine TypeOfElabHM.lambda hpc hann rfl ?_
        have hbc := ihbody (PolyTy.mkTrivial paramTy :: ep)
          (by simp only [heqctx, heq, List.cons_append, List.append_assoc])
        simpa only [heqctx, List.cons_append, List.append_assoc, List.length_cons] using hbc
    | app hf hinput ihf ihinput =>
        intro ep heq
        exact .app (ihf ep heq) (ihinput ep heq)
    | @letIn ann ctx boundExpr bodyCtx body bodyTy M L hwf hann hcofin heqctx hbody ihcofin ihbody =>
        intro ep heq
        refine TypeOfElabHM.letIn (L := L) hwf hann ?_ rfl ?_
        · intro Xs hf
          have hc := ihcofin Xs hf ep heq
          rw [← bodyExtend_openBoundTyVars]
          exact hc
        · have hbc := ihbody (M :: ep)
            (by simp only [heqctx, heq, List.cons_append, List.append_assoc])
          simpa only [heqctx, List.cons_append, List.append_assoc, List.length_cons] using hbc
    | @var dbl polyTy tyArgs ty ctx hlook hlc hinst' =>
        intro ep heq
        rw [heq] at hlook
        by_cases hwin : ep.length ≤ dbl ∧ dbl < ep.length + monos.length
        · let k : Nat := dbl - ep.length
          have hk : k < monos.length := by
            dsimp [k]
            omega
          have hdbl : dbl - ep.length = k := rfl
          have hlook_rhs : (ep ++ monos.map (PolyTy.genGroup G) ++ env)[dbl]? =
              some (PolyTy.genGroup G (monos[k])) := by
            rw [List.append_assoc, List.getElem?_append_right (by omega : ep.length ≤ dbl)]
            rw [hdbl]
            rw [List.getElem?_append_left (by simpa using hk)]
            simp [List.getElem?_map, List.getElem?_eq_getElem hk]
          have hpolyTy : polyTy = PolyTy.genGroup G (monos[k]) :=
            Option.some.inj (hlook.symm.trans hlook_rhs)
          subst polyTy
          have htyArgs : tyArgs.length = (Ty.genFilter G (monos[k])).length := by
            rcases hlc with ⟨hlen0, _⟩
            exact hlen0
          have hty : ty = Ty.openWith tyArgs (Ty.closeOver (Ty.genFilter G (monos[k])) (monos[k])) := by
            have hinst0 : InstantiatesBy tyArgs (Ty.closeOver (Ty.genFilter G (monos[k])) (monos[k])) ty := by
              simpa [PolyTy.genGroup, PolyTy.InstantiatesTo] using hinst'
            exact InstantiatesBy.eq_openWith hinst0
              (Ty.closeOver_preserves_bvars (hmonoLC (monos[k]) (List.getElem_mem hk))) htyArgs
          have hspreadLen : (spreadTyArgs G (monos[k]) tyArgs).length = G.length :=
            spreadTyArgs_length htyArgs
          have hspreadRename : Ty.openWith (spreadTyArgs G (monos[k]) tyArgs) (Ty.closeOver G (monos[k]))
              = Ty.openWith tyArgs (Ty.closeOver (Ty.genFilter G (monos[k])) (monos[k])) :=
            spreadTyArgs_renameG hGnodup htyArgs (hmonoLC (monos[k]) (List.getElem_mem hk))
          have hlook_prom : (ep ++ monos.map (promoteScheme G) ++ env)[dbl]? =
              some (promoteScheme G (monos[k])) := by
            rw [List.append_assoc, List.getElem?_append_right (by omega : ep.length ≤ dbl)]
            rw [hdbl]
            rw [List.getElem?_append_left (by simpa using hk)]
            simp [List.getElem?_map, List.getElem?_eq_getElem hk]
          have hgetD : monos.getD (dbl - ep.length) (Ty.prim .unit) = monos[k] := by
            rw [hdbl]
            change (monos[k]?).getD (Ty.prim .unit) = monos[k]
            rw [List.getElem?_eq_getElem (by simpa using hk)]
            rfl
          simp only [bodyExtend]
          rw [if_pos (by exact hwin)]
          rw [hgetD]
          refine TypeOfElabHM.var (polyTy := promoteScheme G (monos[k]))
            (tyArgs := spreadTyArgs G (monos[k]) tyArgs) ?_ ?_ ?_
          · exact hlook_prom
          · show Ty.AreLC (promoteScheme G (monos[k])).paramCount (spreadTyArgs G (monos[k]) tyArgs)
            constructor
            · rw [hspreadLen]
              rfl
            · exact spreadTyArgs_lc (fun t ht => hlc.2 t ht)
          · show (promoteScheme G (monos[k])).InstantiatesTo (spreadTyArgs G (monos[k]) tyArgs) ty
            rw [hty]
            rw [← hspreadRename]
            exact InstantiatesBy.openWith
              (Ty.closeOver_preserves_bvars (hmonoLC (monos[k]) (List.getElem_mem hk)))
              (Nat.le_of_eq hspreadLen.symm)
        · by_cases hlt : dbl < ep.length
          · simp only [bodyExtend]
            rw [if_neg (by intro hh; exact (by omega : ¬ ep.length ≤ dbl) hh.1)]
            refine TypeOfElabHM.var ?_ hlc hinst'
            show (ep ++ monos.map (promoteScheme G) ++ env)[dbl]? = some polyTy
            rw [List.append_assoc, List.getElem?_append_left hlt]
            rw [List.append_assoc, List.getElem?_append_left hlt] at hlook
            exact hlook
          · have hle : ep.length ≤ dbl := by omega
            have hge : ep.length + monos.length ≤ dbl := by omega
            simp only [bodyExtend]
            rw [if_neg (by intro hh; exact (by omega : ¬ dbl < ep.length + monos.length) hh.2)]
            refine TypeOfElabHM.var ?_ hlc hinst'
            show (ep ++ monos.map (promoteScheme G) ++ env)[dbl]? = some polyTy
            rw [List.append_assoc, List.getElem?_append_right hle]
            rw [List.append_assoc, List.getElem?_append_right hle] at hlook
            have hdProm : (monos.map (promoteScheme G)).length ≤ dbl - ep.length := by
              simp
              omega
            have hdm : (monos.map (PolyTy.genGroup G)).length ≤ dbl - ep.length := by
              simp
              omega
            rw [List.getElem?_append_right hdProm]
            rw [List.getElem?_append_right hdm] at hlook
            rw [show (dbl - ep.length) - (monos.map (promoteScheme G)).length
                = (dbl - ep.length) - (monos.map (PolyTy.genGroup G)).length from by
              simp]
            exact hlook
    | ctor hlook htyargs hinst' =>
        intro ep heq
        exact .ctor hlook htyargs hinst'
    | @match_ ctx scrutinee scrutTy branches resultTy hscrut hne hbrs ihscrut ihbrs =>
        intro ep heq
        refine TypeOfElabHM.match_ (ihscrut ep heq) (bodyExtendBranches_ne_nil hne) ?_
        intro br' hmem'
        rcases bodyExtendBranches_mem branches br' hmem' with ⟨pat, body, hmemb, heqbr'⟩
        subst heqbr'
        rcases ihbrs (pat, body) hmemb with
          ⟨ctorr, c, n, tyArgs, instContents, hpat, hspec, hbody, ihbody⟩ |
          ⟨hpat, hbody, ihbody⟩
        · subst hpat
          refine TypeOfElabMatchBranch.mk hspec rfl ?_
          have hbc := ihbody (instContents.map PolyTy.mkTrivial ++ ep)
            (by simp only [List.append_assoc, heq])
          have hlenInst : instContents.length = (MatchPattern.named c n).bindCount := by
            rw [hspec.fields.length_eq.symm, hspec.bind_count]
            rfl
          simpa only [List.append_assoc, List.length_append, List.length_map,
            hlenInst, Nat.add_comm] using hbc
        · subst hpat
          have hw : TypeOfElabHM ⟨ep ++ monos.map (promoteScheme G) ++ env, ctx.ctors⟩
              (bodyExtend monos G (ep.length + (MatchPattern.wildcard).bindCount) body) resultTy := by
            simpa [MatchPattern.bindCount] using ihbody ep heq
          exact TypeOfElabMatchBranch.wildcard hw
    | @letRec ctx bodyCtx anns bindings specs G₀ L₀ body ρ hwf hmono hpoly heqctx hbody ihmono ihpoly ihbody =>
        intro ep heq
        subst heqctx
        refine TypeOfElabHM.letRec (specs := specs) (G := G₀) (L := L₀) ?_ ?_ ?_ rfl ?_
        · exact ⟨hwf.anns_eq, by simp [bodyExtendGroup_length, hwf.length], hwf.nodup,
            hwf.mono_lc, hwf.poly_wf⟩
        · intro Xs hf p hp τ hτ
          rcases bodyExtendGroup_zip_mem bindings specs p hp with ⟨q, hq, hp1, hp2⟩
          rw [hp2] at hτ
          have hc := ihmono Xs hf q hq τ hτ
          have hcc := hc (specs.map (RecSpec.rhsEntry G₀ Xs) ++ ep)
            (by simp only [RecSpecs.rhsCtx, heq, List.append_assoc])
          rw [hp1]
          simpa only [RecSpecs.rhsCtx, List.append_assoc, List.length_append, List.length_map,
            hwf.length, Nat.add_comm] using hcc
        · intro Xs hf p hp σ hσ Ys hfY
          rcases bodyExtendGroup_zip_mem bindings specs p hp with ⟨q, hq, hp1, hp2⟩
          rw [hp2] at hσ
          have hc := ihpoly Xs hf q hq σ hσ Ys hfY
          have hcc := hc (specs.map (RecSpec.rhsEntry G₀ Xs) ++ ep)
            (by simp only [RecSpecs.rhsCtx, heq, List.append_assoc])
          rw [hp1]
          rw [bodyExtend_openTyVars]
          simpa only [RecSpecs.rhsCtx, List.append_assoc, List.length_append, List.length_map,
            hwf.length, Nat.add_comm] using hcc
        · have hb := ihbody (specs.map (RecSpec.bodyScheme G₀) ++ ep)
            (by simp only [RecSpecs.bodyCtx, heq, List.append_assoc])
          simpa only [RecSpecs.bodyCtx, List.append_assoc, List.length_append, List.length_map,
            hwf.length, Nat.add_comm] using hb
  exact H h [] (by simp)

/-! ## Path R commutes for the promoted traversals

The promoted all-mono elaboratum (`Expr.letRecElabOut`, in `InferW`) is
`.letRec (promoteAnns G specs) (bs.map (retargetStored … (closeTyVars G ·))) (bodyExtend … body)`.
`Infer.sound` and the `…Out` mirrors are stated at the **erased** level
(`Expr.eraseBounds` / `Expr.substTyFvars`), so the two new traversals must commute with erase and
substitution, and must not leak free type variables. These are structural inductions; the nested
`letRec`/`match_` cases are handled inline (mutual `retargetStoredGroup`/`retargetStoredBranches`,
`bodyExtendGroup`/`bodyExtendBranches`), exactly as `retargetStored_openTyVarsAux` does.

The substitution side conditions below (`hSG`, `hSran`) are the same as
`Expr.substTyFvars_letRecElab`: the keys of `S` and the free vars of its range must both avoid the
pool `G`, so the `g ∈ μ.freeVars` test of `spreadTyArgs` and the `closeOver` binder discipline are
stable under `S`. -/

/-- Erase is the identity on `bvarRangeFrom` (every element is a `bvar`). -/
private lemma bvarRangeFrom_map_eraseBounds (d n : Nat) :
    (Ty.bvarRangeFrom d n).map Ty.eraseBounds = Ty.bvarRangeFrom d n := by
  induction n generalizing d with
  | zero => simp [Ty.bvarRangeFrom]
  | succ n ih => simp [Ty.bvarRangeFrom, ih (d := d + 1)]

/-- Substitution leaves `bvarRangeFrom` fixed (every element is a `bvar`). -/
private lemma bvarRangeFrom_map_substFvars {S : List (Nat × Ty)} (d n : Nat) :
    (Ty.bvarRangeFrom d n).map (Ty.substFvars S) = Ty.bvarRangeFrom d n := by
  induction n generalizing d with
  | zero => simp [Ty.bvarRangeFrom]
  | succ n ih => simp [Ty.bvarRangeFrom, Ty.substFvars_bvar, ih (d := d + 1)]

/-- `bvarRangeFrom` contains no free type variables. -/
private lemma bvarRangeFrom_flatMap_freeVars (d n : Nat) :
    (Ty.bvarRangeFrom d n).flatMap Ty.freeVars = [] := by
  induction n generalizing d with
  | zero => rfl
  | succ n ih => simp [Ty.bvarRangeFrom, Ty.freeVars, ih (d := d + 1)]

/-- Erase preserves a recursion-group annotation's type-binder count. -/
private lemma recAnnParams_map_eraseBounds (a : Option PolyTy) :
    RecAnn.params (Option.map PolyTy.eraseBounds a) = RecAnn.params a := by
  cases a with
  | none => rfl
  | some σ => simp [RecAnn.params, PolyTy.eraseBounds_paramCount]

/-- Substitution preserves a recursion-group annotation's type-binder count. -/
private lemma recAnnParams_map_substFvars (S : List (Nat × Ty)) (a : Option PolyTy) :
    RecAnn.params (RecAnn.substFvars S a) = RecAnn.params a := by
  cases a with
  | none => simp [RecAnn.params, RecAnn.substFvars_none]
  | some σ => simp [RecAnn.params, RecAnn.substFvars_some, PolyTy.substFvars_eq]

/-- A type-fvar substitution is the identity on terms with no type annotations. -/
private lemma Expr.substTyFvars_eq_self_of_tyFreeVars_eq_nil {S : List (Nat × Ty)} {e : Expr}
    (h : e.tyFreeVars = []) : e.substTyFvars S = e := by
  exact Expr.substTyFvars_eq_self_of_not_mem_tyFreeVars (pairs := S) (e := e) (by simp [h])

/-- `retargetStored` commutes with `Expr.eraseBounds` (the inserted `Ty.bvarRangeFrom` is
    bounds-free, so erase is the identity on it). -/
theorem retargetStored_eraseBounds {mono : Nat → Bool} {gLen d b : Nat} {e : Expr} :
    (retargetStored mono gLen d b e).eraseBounds = retargetStored mono gLen d b e.eraseBounds := by
  induction e using Expr.rec_strong generalizing b d with
  | primLit p => simp [retargetStored, Expr.eraseBounds]
  | primBinOp op => simp [retargetStored, Expr.eraseBounds]
  | ctor nm => simp [retargetStored, Expr.eraseBounds]
  | var i tyArgs =>
      by_cases hwin : b ≤ i ∧ mono (i - b)
      · have hmap : (Ty.bvarRangeFrom d gLen).map Ty.eraseBounds = Ty.bvarRangeFrom d gLen :=
          bvarRangeFrom_map_eraseBounds d gLen
        simp [retargetStored, Expr.eraseBounds, hwin, hmap]
      · simp [retargetStored, Expr.eraseBounds, hwin]
  | lambda ann body ih =>
      simp only [retargetStored, Expr.eraseBounds, ih (b := b + 1) (d := d)]
  | app f arg ihf iharg =>
      simp only [retargetStored, Expr.eraseBounds,
        ihf (b := b) (d := d), iharg (b := b) (d := d)]
  | letIn ann rhs body ihr ihb =>
      cases ann with
      | none =>
          simp only [retargetStored, Expr.eraseBounds, Option.map_none,
            ihr (b := b) (d := d), ihb (b := b + 1) (d := d)]
      | some σ =>
          simp only [retargetStored, Expr.eraseBounds, Option.map_some,
            PolyTy.eraseBounds_paramCount,
            ihr (b := b) (d := d + σ.paramCount), ihb (b := b + 1) (d := d)]
  | match_ scrut brs ihscrut ihbrs =>
      simp only [retargetStored, Expr.eraseBounds, ihscrut (b := b) (d := d)]
      have hbrs : (retargetStoredBranches mono gLen d b brs).map
            (fun pe => (pe.1, pe.2.eraseBounds))
          = retargetStoredBranches mono gLen d b (brs.map (fun pe => (pe.1, pe.2.eraseBounds))) := by
        induction brs with
        | nil => rfl
        | cons br rest ih =>
            cases br with
            | mk pat body =>
                have hhead : (retargetStored mono gLen d (b + pat.bindCount) body).eraseBounds
                    = retargetStored mono gLen d (b + pat.bindCount) body.eraseBounds :=
                  ihbrs pat body (List.mem_cons_self ..) (b := b + pat.bindCount) (d := d)
                simp only [retargetStoredBranches, List.map_cons]
                rw [hhead]
                congr 1
                exact ih (fun pat' e' he' => ihbrs pat' e' (List.mem_cons_of_mem _ he'))
      rw [hbrs]
  | letRec anns bs body ihbs ihbody =>
      simp only [retargetStored, Expr.eraseBounds, List.length_map,
        ihbody (b := b + bs.length) (d := d)]
      have hbs' : ∀ (D : Nat) (anns' : List (Option PolyTy)),
          (retargetStoredGroup mono gLen d D anns' bs).map Expr.eraseBounds
            = retargetStoredGroup mono gLen d D
                (anns'.map (Option.map PolyTy.eraseBounds)) (bs.map Expr.eraseBounds) := by
        intro D anns'
        revert anns'
        induction bs with
        | nil => intro anns'; rfl
        | cons e tl ih =>
            intro anns'
            cases anns' with
            | nil =>
                simp only [retargetStoredGroup, List.map_cons]
                rw [ihbs e (List.mem_cons_self ..) (b := D) (d := d)]
                congr 1
                exact ih (fun e' he' => ihbs e' (List.mem_cons_of_mem _ he')) []
            | cons a as =>
                simp only [retargetStoredGroup, List.map_cons]
                rw [recAnnParams_map_eraseBounds a]
                rw [ihbs e (List.mem_cons_self ..) (b := D) (d := d + RecAnn.params a)]
                congr 1
                exact ih (fun e' he' => ihbs e' (List.mem_cons_of_mem _ he')) as
      rw [hbs' (b + bs.length) anns]

/-- `retargetStored` commutes with `Expr.substTyFvars` unconditionally (the inserted
    `Ty.bvarRangeFrom` contains only `bvar`s, which substitution leaves alone). -/
theorem retargetStored_substTyFvars {mono : Nat → Bool} {gLen d b : Nat} {S : List (Nat × Ty)}
    {e : Expr} :
    (retargetStored mono gLen d b e).substTyFvars S = retargetStored mono gLen d b (e.substTyFvars S) := by
  induction e using Expr.rec_strong generalizing b d with
  | primLit p =>
      have h : (Expr.primLit p).substTyFvars S = Expr.primLit p :=
        Expr.substTyFvars_eq_self_of_tyFreeVars_eq_nil (e := Expr.primLit p) (by simp [Expr.tyFreeVars])
      simp [retargetStored, h]
  | primBinOp op =>
      have h : (Expr.primBinOp op).substTyFvars S = Expr.primBinOp op :=
        Expr.substTyFvars_eq_self_of_tyFreeVars_eq_nil (e := Expr.primBinOp op) (by simp [Expr.tyFreeVars])
      simp [retargetStored, h]
  | ctor nm =>
      have h : (Expr.ctor nm).substTyFvars S = Expr.ctor nm :=
        Expr.substTyFvars_eq_self_of_tyFreeVars_eq_nil (e := Expr.ctor nm) (by simp [Expr.tyFreeVars])
      simp [retargetStored, h]
  | var i tyArgs =>
      by_cases hwin : b ≤ i ∧ mono (i - b)
      · have hmap : (Ty.bvarRangeFrom d gLen).map (Ty.substFvars S) = Ty.bvarRangeFrom d gLen :=
          bvarRangeFrom_map_substFvars d gLen
        have hret : retargetStored mono gLen d b (Expr.var i tyArgs)
            = Expr.var i (Ty.bvarRangeFrom d gLen) := by
          rw [retargetStored]
          exact if_pos hwin
        have hret' : retargetStored mono gLen d b (Expr.var i (tyArgs.map (Ty.substFvars S)))
            = Expr.var i (Ty.bvarRangeFrom d gLen) := by
          rw [retargetStored]
          exact if_pos hwin
        rw [Expr.substTyFvars_var]
        rw [hret]
        rw [hret']
        rw [Expr.substTyFvars_var]
        rw [hmap]
      · have hret : retargetStored mono gLen d b (Expr.var i tyArgs)
            = Expr.var i tyArgs := by
          rw [retargetStored]
          exact if_neg hwin
        have hret' : retargetStored mono gLen d b (Expr.var i (tyArgs.map (Ty.substFvars S)))
            = Expr.var i (tyArgs.map (Ty.substFvars S)) := by
          rw [retargetStored]
          exact if_neg hwin
        rw [Expr.substTyFvars_var]
        rw [hret]
        rw [hret']
        rw [Expr.substTyFvars_var]
  | lambda ann body ih =>
      simp only [retargetStored, Expr.substTyFvars_lambda, ih (b := b + 1) (d := d)]
  | app f arg ihf iharg =>
      simp only [retargetStored, Expr.substTyFvars_app,
        ihf (b := b) (d := d), iharg (b := b) (d := d)]
  | letIn ann rhs body ihr ihb =>
      cases ann with
      | none =>
          simp only [retargetStored, Expr.substTyFvars_letIn, Option.map_none,
            ihr (b := b) (d := d), ihb (b := b + 1) (d := d)]
      | some σ =>
          simp only [retargetStored, Expr.substTyFvars_letIn, Option.map_some,
            ihr (b := b) (d := d + σ.paramCount), ihb (b := b + 1) (d := d)]
  | match_ scrut brs ihscrut ihbrs =>
      simp only [retargetStored, Expr.substTyFvars_match, ihscrut (b := b) (d := d)]
      have hbrs : (retargetStoredBranches mono gLen d b brs).map
            (fun pb => (pb.1, pb.2.substTyFvars S))
          = retargetStoredBranches mono gLen d b (brs.map (fun pb => (pb.1, pb.2.substTyFvars S))) := by
        induction brs with
        | nil => rfl
        | cons br rest ih =>
            cases br with
            | mk pat body =>
                have hhead : (retargetStored mono gLen d (b + pat.bindCount) body).substTyFvars S
                    = retargetStored mono gLen d (b + pat.bindCount) (body.substTyFvars S) :=
                  ihbrs pat body (List.mem_cons_self ..) (b := b + pat.bindCount) (d := d)
                simp only [retargetStoredBranches, List.map_cons]
                rw [hhead]
                congr 1
                exact ih (fun pat' e' he' => ihbrs pat' e' (List.mem_cons_of_mem _ he'))
      rw [hbrs]
  | letRec anns bs body ihbs ihbody =>
      simp only [retargetStored, Expr.substTyFvars_letRec, List.length_map,
        ihbody (b := b + bs.length) (d := d)]
      have hbs' : ∀ (D : Nat) (anns' : List (Option PolyTy)),
          (retargetStoredGroup mono gLen d D anns' bs).map (·.substTyFvars S)
            = retargetStoredGroup mono gLen d D
                (anns'.map (RecAnn.substFvars S)) (bs.map (·.substTyFvars S)) := by
        intro D anns'
        revert anns'
        induction bs with
        | nil => intro anns'; rfl
        | cons e tl ih =>
            intro anns'
            cases anns' with
            | nil =>
                simp only [retargetStoredGroup, List.map_cons]
                rw [ihbs e (List.mem_cons_self ..) (b := D) (d := d)]
                congr 1
                exact ih (fun e' he' => ihbs e' (List.mem_cons_of_mem _ he')) []
            | cons a as =>
                simp only [retargetStoredGroup, List.map_cons]
                rw [recAnnParams_map_substFvars S a]
                rw [ihbs e (List.mem_cons_self ..) (b := D) (d := d + RecAnn.params a)]
                congr 1
                exact ih (fun e' he' => ihbs e' (List.mem_cons_of_mem _ he')) as
      rw [hbs' (b + bs.length) anns]

/-- `retargetStored` does not introduce free type variables (it only *overwrites* `tyArgs` with
    bounds-free `bvar`s). -/
theorem retargetStored_tyFreeVars_subset {mono : Nat → Bool} {gLen d b : Nat} {e : Expr} {y : Nat} :
    y ∈ (retargetStored mono gLen d b e).tyFreeVars → y ∈ e.tyFreeVars := by
  induction e using Expr.rec_strong generalizing b d with
  | primLit p => intro hy; simp [retargetStored, Expr.tyFreeVars] at hy
  | primBinOp op => intro hy; simp [retargetStored, Expr.tyFreeVars] at hy
  | ctor nm => intro hy; simp [retargetStored, Expr.tyFreeVars] at hy
  | var i tyArgs =>
      by_cases hwin : b ≤ i ∧ mono (i - b)
      · intro hy
        have hf : (Ty.bvarRangeFrom d gLen).flatMap Ty.freeVars = [] :=
          bvarRangeFrom_flatMap_freeVars d gLen
        simp [retargetStored, Expr.tyFreeVars, hwin, hf] at hy
      · intro hy
        simpa [retargetStored, Expr.tyFreeVars, hwin] using hy
  | lambda ann body ih =>
      simp only [retargetStored, Expr.tyFreeVars, List.mem_append]
      intro hy
      rcases hy with h | h
      · exact Or.inl h
      · exact Or.inr (ih (b := b + 1) (d := d) h)
  | app f arg ihf iharg =>
      simp only [retargetStored, Expr.tyFreeVars, List.mem_append]
      intro hy
      rcases hy with h | h
      · exact Or.inl (ihf (b := b) (d := d) h)
      · exact Or.inr (iharg (b := b) (d := d) h)
  | letIn ann rhs body ihr ihb =>
      cases ann with
      | none =>
          simp only [retargetStored, Expr.tyFreeVars, List.mem_append, Option.elim_none,
            List.nil_append]
          intro hy
          rcases hy with h | h
          · exact Or.inl (ihr (b := b) (d := d) h)
          · exact Or.inr (ihb (b := b + 1) (d := d) h)
      | some σ =>
          simp only [retargetStored, Expr.tyFreeVars, List.mem_append, Option.elim_some]
          intro hy
          rcases hy with h | h
          · rcases h with h | h
            · exact Or.inl (Or.inl h)
            · exact Or.inl (Or.inr (ihr (b := b) (d := d + σ.paramCount) h))
          · exact Or.inr (ihb (b := b + 1) (d := d) h)
  | match_ scrut brs ihscrut ihbrs =>
      simp only [retargetStored, Expr.tyFreeVars, List.mem_append]
      have hbrs : y ∈ Expr.tyFreeVars.BranchList.tyFreeVars (retargetStoredBranches mono gLen d b brs)
          → y ∈ Expr.tyFreeVars.BranchList.tyFreeVars brs := by
        induction brs with
        | nil => intro hy; simp [Expr.tyFreeVars.BranchList.tyFreeVars, retargetStoredBranches] at hy
        | cons br rest ih =>
            cases br with
            | mk pat body =>
                intro hy
                simp only [retargetStoredBranches, Expr.tyFreeVars.BranchList.tyFreeVars,
                  List.mem_append] at hy ⊢
                rcases hy with h | h
                · exact Or.inl
                    (ihbrs pat body (List.mem_cons_self ..) (b := b + pat.bindCount) (d := d) h)
                · exact Or.inr
                    (ih (fun pat' e' he' => ihbrs pat' e' (List.mem_cons_of_mem _ he')) h)
      intro hy
      rcases hy with h | h
      · exact Or.inl (ihscrut (b := b) (d := d) h)
      · exact Or.inr (hbrs h)
  | letRec anns bs body ihbs ihbody =>
      simp only [retargetStored, Expr.tyFreeVars, List.mem_append]
      have hbs' : ∀ (D : Nat) (anns' : List (Option PolyTy)),
          y ∈ Expr.tyFreeVars.RecGroup.tyFreeVars (retargetStoredGroup mono gLen d D anns' bs)
            → y ∈ Expr.tyFreeVars.RecGroup.tyFreeVars bs := by
        intro D anns'
        revert anns'
        induction bs with
        | nil => intro anns' hy; simp [Expr.tyFreeVars.RecGroup.tyFreeVars, retargetStoredGroup] at hy
        | cons e tl ih =>
            intro anns' hy
            cases anns' with
            | nil =>
                simp only [retargetStoredGroup, Expr.tyFreeVars.RecGroup.tyFreeVars,
                  List.mem_append] at hy ⊢
                rcases hy with h | h
                · exact Or.inl (ihbs e (List.mem_cons_self ..) (b := D) (d := d) h)
                · exact Or.inr (ih (fun e' he' => ihbs e' (List.mem_cons_of_mem _ he')) [] h)
            | cons a as =>
                simp only [retargetStoredGroup, Expr.tyFreeVars.RecGroup.tyFreeVars,
                  List.mem_append] at hy ⊢
                rcases hy with h | h
                · exact Or.inl
                    (ihbs e (List.mem_cons_self ..) (b := D) (d := d + RecAnn.params a) h)
                · exact Or.inr
                    (ih (fun e' he' => ihbs e' (List.mem_cons_of_mem _ he')) as h)
      intro hy
      rcases hy with h | h
      · rcases h with h | h
        · exact Or.inl (Or.inl h)
        · exact Or.inl (Or.inr (hbs' (b + bs.length) anns h))
      · exact Or.inr (ihbody (b := b + bs.length) (d := d) h)

/-- `List.getD` commutes with `map`. -/
private lemma List.getD_map {α β : Type} (f : α → β) (l : List α) (n : Nat) (a : α) :
    (l.map f).getD n (f a) = f (l.getD n a) := by
  induction l generalizing n with
  | nil => simp [List.getD]
  | cons hd tl ih =>
      cases n with
      | zero => simp [List.getD]
      | succ n => exact ih n

/-- Erase preserves a type's free variables. -/
private lemma Ty.mem_freeVars_eraseBounds {x : Nat} {τ : Ty} :
    x ∈ (Ty.eraseBounds τ).freeVars ↔ x ∈ τ.freeVars := by
  induction τ using Ty.rec_strong with
  | prim p => simp [Ty.eraseBounds, Ty.freeVars]
  | bvar i => simp [Ty.eraseBounds, Ty.freeVars]
  | fvar i => simp [Ty.eraseBounds, Ty.freeVars]
  | arrow a b iha ihb =>
      rw [Ty.eraseBounds_arrow, Ty.freeVars, Ty.freeVars]
      simp only [List.mem_dedup, List.mem_append]
      constructor <;> intro h <;> rcases h with h | h
      · exact Or.inl (iha.mp h)
      · exact Or.inr (ihb.mp h)
      · exact Or.inl (iha.mpr h)
      · exact Or.inr (ihb.mpr h)
  | customTy nm tys ih =>
      rw [Ty.eraseBounds_customTy, Ty.freeVars, Ty.freeVars, TyList.eraseBounds_eq_map]
      rw [TyList.mem_freeVars_iff, TyList.mem_freeVars_iff]
      constructor
      · rintro ⟨t', ht', hx⟩
        obtain ⟨t, ht, rfl⟩ := List.mem_map.mp ht'
        exact ⟨t, ht, (ih t ht).mp hx⟩
      · rintro ⟨t, ht, hx⟩
        exact ⟨Ty.eraseBounds t, List.mem_map_of_mem ht, (ih t ht).mpr hx⟩
  | bl lo hi e ih =>
      simpa [Ty.eraseBounds_bl, bareListTy, Ty.freeVars, TyList.freeVars, List.mem_dedup,
        List.mem_append] using ih

/-- Substituting a list of pairs whose keys and range free vars both avoid `g` leaves the
    membership of `g` in the free-var set unchanged. -/
private lemma Ty.mem_freeVars_substFvars_of {S : List (Nat × Ty)} {g : Nat} {τ : Ty}
    (hS : ∀ p ∈ S, p.1 ≠ g) (hSran : ∀ p ∈ S, g ∉ p.2.freeVars) :
    g ∈ (Ty.substFvars S τ).freeVars ↔ g ∈ τ.freeVars := by
  induction S generalizing τ with
  | nil => rfl
  | cons hd tl ih =>
      obtain ⟨Z, U⟩ := hd
      have hZ : g ≠ Z := fun heq => hS (Z, U) List.mem_cons_self heq.symm
      have hU : g ∉ U.freeVars := hSran (Z, U) List.mem_cons_self
      have hS' : ∀ p ∈ tl, p.1 ≠ g := fun p hp => hS p (List.mem_cons_of_mem _ hp)
      have hSran' : ∀ p ∈ tl, g ∉ p.2.freeVars := fun p hp => hSran p (List.mem_cons_of_mem _ hp)
      simp only [Ty.substFvars]
      rw [ih (τ := Ty.substFvar Z U τ) hS' hSran']
      exact Ty.mem_freeVars_substFvar_of hZ hU

/-- The spread commutes with `Ty.eraseBounds` pointwise. -/
private lemma spreadTyArgs_map_eraseBounds {G : List Nat} {μ : Ty} {tyArgs : List Ty} :
    (spreadTyArgs G μ tyArgs).map Ty.eraseBounds
      = spreadTyArgs G (Ty.eraseBounds μ) (tyArgs.map Ty.eraseBounds) := by
  induction G generalizing tyArgs with
  | nil => simp [spreadTyArgs]
  | cons g gs ih =>
      by_cases hmem : g ∈ μ.freeVars
      · have hmem' : g ∈ (Ty.eraseBounds μ).freeVars :=
          (Ty.mem_freeVars_eraseBounds (τ := μ)).mpr hmem
        cases tyArgs with
        | nil =>
            simp [spreadTyArgs, hmem, hmem']
            exact ih (tyArgs := [])
        | cons t ts =>
            simp [spreadTyArgs, hmem, hmem']
            exact ih (tyArgs := ts)
      · have hmem' : g ∉ (Ty.eraseBounds μ).freeVars := fun hg =>
          hmem ((Ty.mem_freeVars_eraseBounds (τ := μ)).mp hg)
        simp [spreadTyArgs, hmem, hmem']
        exact ih (tyArgs := tyArgs)

/-- The spread commutes with `Ty.substFvars S` pointwise, provided `S`'s keys and range
    free vars both avoid the pool `G`. -/
private lemma spreadTyArgs_map_substFvars {S : List (Nat × Ty)} {G : List Nat} {μ : Ty}
    {tyArgs : List Ty}
    (hSG : ∀ p ∈ S, p.1 ∉ G) (hSran : ∀ p ∈ S, ∀ u ∈ p.2.freeVars, u ∉ G) :
    (spreadTyArgs G μ tyArgs).map (Ty.substFvars S)
      = spreadTyArgs G (Ty.substFvars S μ) (tyArgs.map (Ty.substFvars S)) := by
  induction G generalizing tyArgs with
  | nil => simp [spreadTyArgs]
  | cons g gs ih =>
      have hSG' : ∀ p ∈ S, p.1 ∉ gs := fun p hp hg => hSG p hp (List.mem_cons_of_mem _ hg)
      have hSran' : ∀ p ∈ S, ∀ u ∈ p.2.freeVars, u ∉ gs := fun p hp u hu hg =>
        hSran p hp u hu (List.mem_cons_of_mem _ hg)
      have hgmem : g ∈ g :: gs := List.mem_cons_self
      have hgneq : ∀ p ∈ S, p.1 ≠ g := fun p hp heq => hSG p hp (heq ▸ hgmem)
      have hgran : ∀ p ∈ S, g ∉ p.2.freeVars := fun p hp hg => hSran p hp g hg hgmem
      by_cases hmem : g ∈ μ.freeVars
      · have hmem' : g ∈ (Ty.substFvars S μ).freeVars :=
          (Ty.mem_freeVars_substFvars_of (S := S) (g := g) (τ := μ) hgneq hgran).mpr hmem
        cases tyArgs with
        | nil =>
            simp [spreadTyArgs, hmem, hmem', Ty.substFvars_prim]
            exact ih hSG' hSran' (tyArgs := [])
        | cons t ts =>
            simp [spreadTyArgs, hmem, hmem']
            exact ih hSG' hSran' (tyArgs := ts)
      · have hmem' : g ∉ (Ty.substFvars S μ).freeVars := fun hg =>
          hmem ((Ty.mem_freeVars_substFvars_of (S := S) (g := g) (τ := μ) hgneq hgran).mp hg)
        simp [spreadTyArgs, hmem, hmem', Ty.substFvars_prim]
        exact ih hSG' hSran' (tyArgs := tyArgs)

/-- The spread emits only `unit` fillers or elements of the original `tyArgs`, so it
    introduces no free variables. -/
private lemma spreadTyArgs_flatMap_freeVars_subset {G : List Nat} {μ : Ty} {tyArgs : List Ty}
    {y : Nat} :
    y ∈ (spreadTyArgs G μ tyArgs).flatMap Ty.freeVars → y ∈ tyArgs.flatMap Ty.freeVars := by
  induction G generalizing tyArgs with
  | nil => simp [spreadTyArgs]
  | cons g gs ih =>
      intro hy
      rw [List.mem_flatMap] at hy
      rcases hy with ⟨a, ha, hya⟩
      by_cases hmem : g ∈ μ.freeVars
      · cases tyArgs with
        | nil =>
            simp only [spreadTyArgs, hmem] at ha
            by_cases h_eq : a = Ty.prim .unit
            · subst a
              simp [Ty.freeVars] at hya
            · have ha' : a ∈ spreadTyArgs gs μ [] := by
                exact (List.mem_cons.mp ha).resolve_left h_eq
              exact ih (tyArgs := []) (List.mem_flatMap.mpr ⟨a, ha', hya⟩)
        | cons t ts =>
            simp only [spreadTyArgs, hmem] at ha
            by_cases h_eq : a = t
            · subst a
              rw [List.mem_flatMap]
              exact ⟨t, List.mem_cons_self .., hya⟩
            · have ha' : a ∈ spreadTyArgs gs μ ts := by
                exact (List.mem_cons.mp ha).resolve_left h_eq
              have hih : y ∈ ts.flatMap Ty.freeVars :=
                ih (tyArgs := ts) (List.mem_flatMap.mpr ⟨a, ha', hya⟩)
              rcases List.mem_flatMap.mp hih with ⟨a', ha'', hya'⟩
              rw [List.mem_flatMap]
              exact ⟨a', List.mem_cons_of_mem t ha'', hya'⟩
      · simp only [spreadTyArgs, hmem] at ha
        by_cases h_eq : a = Ty.prim .unit
        · subst a
          simp [Ty.freeVars] at hya
        · have ha' : a ∈ spreadTyArgs gs μ tyArgs := by
            exact (List.mem_cons.mp ha).resolve_left h_eq
          have hih : y ∈ tyArgs.flatMap Ty.freeVars :=
            ih (tyArgs := tyArgs) (List.mem_flatMap.mpr ⟨a, ha', hya⟩)
          rcases List.mem_flatMap.mp hih with ⟨a', ha'', hya'⟩
          rw [List.mem_flatMap]
          exact ⟨a', ha'', hya'⟩

/-- Erase commutes with `closeOver` (`eraseBounds` only replaces `bl` by bare `List`, which
    leaves the `fvar ↦ bvar` correspondence of `closeOver` intact). -/
private lemma Ty.eraseBounds_closeOver {G : List Nat} {τ : Ty} :
    Ty.eraseBounds (Ty.closeOver G τ) = Ty.closeOver G (Ty.eraseBounds τ) := by
  induction τ using Ty.rec_strong with
  | prim p => simp [Ty.closeOver, Ty.eraseBounds]
  | bvar i => simp [Ty.closeOver, Ty.eraseBounds]
  | fvar n =>
      cases h : G.idxOf? n with
      | none => simp [Ty.closeOver, Ty.eraseBounds, h]
      | some i => simp [Ty.closeOver, Ty.eraseBounds, h]
  | arrow a b iha ihb => simp [Ty.closeOver, Ty.eraseBounds, iha, ihb]
  | customTy nm tys ih =>
      simp only [Ty.closeOver, Ty.eraseBounds, TyList.closeOver_eq_map, TyList.eraseBounds_eq_map,
        List.map_map]
      apply congrArg (Ty.customTy nm)
      apply List.map_congr_left
      intro t ht
      exact ih t ht
  | bl lo hi e ih =>
      simp [Ty.closeOver, Ty.eraseBounds_bl, bareListTy, TyList.closeOver_eq_map, ih]

/-- Substitution commutes with `closeOver`, provided the substituted keys and the free vars
    of their replacements all avoid the closed-over pool `G`. -/
private lemma Ty.substFvars_closeOver {S : List (Nat × Ty)} {G : List Nat} {τ : Ty}
    (hSG : ∀ p ∈ S, p.1 ∉ G) (hSran : ∀ p ∈ S, ∀ u ∈ p.2.freeVars, u ∉ G) :
    Ty.substFvars S (Ty.closeOver G τ) = Ty.closeOver G (Ty.substFvars S τ) := by
  induction S generalizing τ with
  | nil => rfl
  | cons hd tl ih =>
      obtain ⟨Z, U⟩ := hd
      have hZ : Z ∉ G := hSG (Z, U) List.mem_cons_self
      have hU : ∀ g ∈ G, g ∉ U.freeVars := fun g hg hc => hSran (Z, U) List.mem_cons_self g hc hg
      have hSG' : ∀ p ∈ tl, p.1 ∉ G := fun p hp => hSG p (List.mem_cons_of_mem _ hp)
      have hSran' : ∀ p ∈ tl, ∀ u ∈ p.2.freeVars, u ∉ G := fun p hp u hu =>
        hSran p (List.mem_cons_of_mem _ hp) u hu
      simp only [Ty.substFvars]
      rw [Ty.substFvar_closeOver_comm hZ hU]
      rw [ih hSG' hSran']

/-- `bodyExtend` commutes with `Expr.eraseBounds` (the `g ∈ μ.freeVars` test of `spreadTyArgs`
    is stable because `Ty.eraseBounds` preserves free variables, and the `unit` fillers are
    bounds-free). -/
theorem bodyExtend_eraseBounds {monos : List Ty} {G : List Nat} {b : Nat} {e : Expr} :
    (bodyExtend monos G b e).eraseBounds = bodyExtend (monos.map Ty.eraseBounds) G b e.eraseBounds := by
  induction e using Expr.rec_strong generalizing b with
  | primLit p => simp [bodyExtend, Expr.eraseBounds]
  | primBinOp op => simp [bodyExtend, Expr.eraseBounds]
  | ctor nm => simp [bodyExtend, Expr.eraseBounds]
  | var i tyArgs =>
      by_cases hwin : b ≤ i ∧ i < b + monos.length
      · rw [show bodyExtend monos G b (Expr.var i tyArgs) = Expr.var i
            (spreadTyArgs G (monos.getD (i - b) (Ty.prim .unit)) tyArgs) by
            simp [bodyExtend, hwin]]
        rw [show bodyExtend (monos.map Ty.eraseBounds) G b ((Expr.var i tyArgs).eraseBounds)
            = Expr.var i
              (spreadTyArgs G ((monos.map Ty.eraseBounds).getD (i - b) (Ty.prim .unit))
                (tyArgs.map Ty.eraseBounds)) by
            simp [bodyExtend, Expr.eraseBounds, hwin]]
        rw [show (Expr.var i (spreadTyArgs G (monos.getD (i - b) (Ty.prim .unit)) tyArgs)).eraseBounds
            = Expr.var i ((spreadTyArgs G (monos.getD (i - b) (Ty.prim .unit)) tyArgs).map Ty.eraseBounds) by
            simp [Expr.eraseBounds]]
        rw [spreadTyArgs_map_eraseBounds]
        congr 2
        have hget := List.getD_map (f := Ty.eraseBounds) (l := monos) (n := i - b) (a := Ty.prim .unit)
        simpa using hget.symm
      · simp [bodyExtend, Expr.eraseBounds, hwin]
  | lambda ann body ih =>
      simp only [bodyExtend, Expr.eraseBounds, ih (b := b + 1)]
  | app f arg ihf iharg =>
      simp only [bodyExtend, Expr.eraseBounds, ihf (b := b), iharg (b := b)]
  | letIn ann rhs body ihr ihb =>
      simp only [bodyExtend, Expr.eraseBounds, ihr (b := b), ihb (b := b + 1)]
  | match_ scrut brs ihscrut ihbrs =>
      simp only [bodyExtend, Expr.eraseBounds, ihscrut (b := b)]
      have hbrs : (bodyExtendBranches monos G b brs).map
            (fun pe => (pe.1, pe.2.eraseBounds))
          = bodyExtendBranches (monos.map Ty.eraseBounds) G b
              (brs.map (fun pe => (pe.1, pe.2.eraseBounds))) := by
        induction brs with
        | nil => rfl
        | cons br rest ih =>
            cases br with
            | mk pat body =>
                have hhead : (bodyExtend monos G (b + pat.bindCount) body).eraseBounds
                    = bodyExtend (monos.map Ty.eraseBounds) G (b + pat.bindCount) body.eraseBounds :=
                  ihbrs pat body (List.mem_cons_self ..) (b := b + pat.bindCount)
                simp only [bodyExtendBranches, List.map_cons]
                rw [hhead]
                congr 1
                exact ih (fun pat' e' he' => ihbrs pat' e' (List.mem_cons_of_mem _ he'))
      rw [hbrs]
  | letRec anns bs body ihbs ihbody =>
      simp only [bodyExtend, Expr.eraseBounds, List.length_map,
        ihbody (b := b + bs.length)]
      have hbs' : ∀ (D : Nat),
          (bodyExtendGroup monos G D bs).map Expr.eraseBounds
            = bodyExtendGroup (monos.map Ty.eraseBounds) G D (bs.map Expr.eraseBounds) := by
        intro D
        induction bs with
        | nil => rfl
        | cons e tl ih =>
            simp only [bodyExtendGroup, List.map_cons]
            rw [ihbs e (List.mem_cons_self ..) (b := D)]
            congr 1
            exact ih (fun e' he' => ihbs e' (List.mem_cons_of_mem _ he'))
      rw [hbs' (b + bs.length)]

/-- `bodyExtend` commutes with `Expr.substTyFvars`, provided the substitution's keys and range
    free vars avoid the pool `G` (stability of `spreadTyArgs`' `g ∈ μ.freeVars` test). -/
theorem bodyExtend_substTyFvars {monos : List Ty} {G : List Nat} {b : Nat} {S : List (Nat × Ty)}
    {e : Expr}
    (hSG : ∀ p ∈ S, p.1 ∉ G) (hSran : ∀ p ∈ S, ∀ u ∈ p.2.freeVars, u ∉ G) :
    (bodyExtend monos G b e).substTyFvars S
      = bodyExtend (monos.map (Ty.substFvars S)) G b (e.substTyFvars S) := by
  induction e using Expr.rec_strong generalizing b with
  | primLit p =>
      have h : (Expr.primLit p).substTyFvars S = Expr.primLit p :=
        Expr.substTyFvars_eq_self_of_tyFreeVars_eq_nil (e := Expr.primLit p) (by simp [Expr.tyFreeVars])
      simp [bodyExtend, h]
  | primBinOp op =>
      have h : (Expr.primBinOp op).substTyFvars S = Expr.primBinOp op :=
        Expr.substTyFvars_eq_self_of_tyFreeVars_eq_nil (e := Expr.primBinOp op) (by simp [Expr.tyFreeVars])
      simp [bodyExtend, h]
  | ctor nm =>
      have h : (Expr.ctor nm).substTyFvars S = Expr.ctor nm :=
        Expr.substTyFvars_eq_self_of_tyFreeVars_eq_nil (e := Expr.ctor nm) (by simp [Expr.tyFreeVars])
      simp [bodyExtend, h]
  | var i tyArgs =>
      by_cases hwin : b ≤ i ∧ i < b + monos.length
      · rw [show bodyExtend monos G b (Expr.var i tyArgs) = Expr.var i
            (spreadTyArgs G (monos.getD (i - b) (Ty.prim .unit)) tyArgs) by
            simp [bodyExtend, hwin]]
        rw [show bodyExtend (monos.map (Ty.substFvars S)) G b ((Expr.var i tyArgs).substTyFvars S)
            = Expr.var i
                (spreadTyArgs G ((monos.map (Ty.substFvars S)).getD (i - b) (Ty.prim .unit))
                  (tyArgs.map (Ty.substFvars S))) by
            rw [Expr.substTyFvars_var]
            simp [bodyExtend, hwin]]
        rw [show (Expr.var i (spreadTyArgs G (monos.getD (i - b) (Ty.prim .unit)) tyArgs)).substTyFvars S
            = Expr.var i ((spreadTyArgs G (monos.getD (i - b) (Ty.prim .unit)) tyArgs).map (Ty.substFvars S)) by
            simp [Expr.substTyFvars_var]]
        rw [spreadTyArgs_map_substFvars hSG hSran]
        congr 2
        have hget := List.getD_map (f := Ty.substFvars S) (l := monos) (n := i - b) (a := Ty.prim .unit)
        simpa [Ty.substFvars_prim] using hget.symm
      · simp [bodyExtend, Expr.substTyFvars_var, hwin]
  | lambda ann body ih =>
      simp only [bodyExtend, Expr.substTyFvars_lambda, ih (b := b + 1)]
  | app f arg ihf iharg =>
      simp only [bodyExtend, Expr.substTyFvars_app, ihf (b := b), iharg (b := b)]
  | letIn ann rhs body ihr ihb =>
      simp only [bodyExtend, Expr.substTyFvars_letIn, ihr (b := b), ihb (b := b + 1)]
  | match_ scrut brs ihscrut ihbrs =>
      simp only [bodyExtend, Expr.substTyFvars_match, ihscrut (b := b)]
      have hbrs : (bodyExtendBranches monos G b brs).map
            (fun pb => (pb.1, pb.2.substTyFvars S))
          = bodyExtendBranches (monos.map (Ty.substFvars S)) G b
              (brs.map (fun pb => (pb.1, pb.2.substTyFvars S))) := by
        induction brs with
        | nil => rfl
        | cons br rest ih =>
            cases br with
            | mk pat body =>
                have hhead : (bodyExtend monos G (b + pat.bindCount) body).substTyFvars S
                    = bodyExtend (monos.map (Ty.substFvars S)) G (b + pat.bindCount)
                        (body.substTyFvars S) :=
                  ihbrs pat body (List.mem_cons_self ..) (b := b + pat.bindCount)
                simp only [bodyExtendBranches, List.map_cons]
                rw [hhead]
                congr 1
                exact ih (fun pat' e' he' => ihbrs pat' e' (List.mem_cons_of_mem _ he'))
      rw [hbrs]
  | letRec anns bs body ihbs ihbody =>
      simp only [bodyExtend, Expr.substTyFvars_letRec, List.length_map,
        ihbody (b := b + bs.length)]
      have hbs' : ∀ (D : Nat),
          (bodyExtendGroup monos G D bs).map (·.substTyFvars S)
            = bodyExtendGroup (monos.map (Ty.substFvars S)) G D (bs.map (·.substTyFvars S)) := by
        intro D
        induction bs with
        | nil => rfl
        | cons e tl ih =>
            simp only [bodyExtendGroup, List.map_cons]
            rw [ihbs e (List.mem_cons_self ..) (b := D)]
            congr 1
            exact ih (fun e' he' => ihbs e' (List.mem_cons_of_mem _ he'))
      rw [hbs' (b + bs.length)]

/-- `bodyExtend` does not introduce free type variables (`spreadTyArgs` emits `unit` fillers or
    the original `tyArgs`, never fresh `fvar`s). -/
theorem bodyExtend_tyFreeVars_subset {monos : List Ty} {G : List Nat} {b : Nat} {e : Expr} {y : Nat} :
    y ∈ (bodyExtend monos G b e).tyFreeVars → y ∈ e.tyFreeVars := by
  induction e using Expr.rec_strong generalizing b with
  | primLit p => intro hy; simp [bodyExtend, Expr.tyFreeVars] at hy
  | primBinOp op => intro hy; simp [bodyExtend, Expr.tyFreeVars] at hy
  | ctor nm => intro hy; simp [bodyExtend, Expr.tyFreeVars] at hy
  | var i tyArgs =>
      by_cases hwin : b ≤ i ∧ i < b + monos.length
      · intro hy
        have hy' : y ∈ (spreadTyArgs G (monos.getD (i - b) (Ty.prim .unit)) tyArgs).flatMap Ty.freeVars := by
          simpa [bodyExtend, Expr.tyFreeVars, hwin] using hy
        simpa [Expr.tyFreeVars] using
          spreadTyArgs_flatMap_freeVars_subset (G := G) (μ := monos.getD (i - b) (Ty.prim .unit)) hy'
      · intro hy
        simpa [bodyExtend, Expr.tyFreeVars, hwin] using hy
  | lambda ann body ih =>
      simp only [bodyExtend, Expr.tyFreeVars, List.mem_append]
      intro hy
      rcases hy with h | h
      · exact Or.inl h
      · exact Or.inr (ih (b := b + 1) h)
  | app f arg ihf iharg =>
      simp only [bodyExtend, Expr.tyFreeVars, List.mem_append]
      intro hy
      rcases hy with h | h
      · exact Or.inl (ihf (b := b) h)
      · exact Or.inr (iharg (b := b) h)
  | letIn ann rhs body ihr ihb =>
      cases ann with
      | none =>
          simp only [bodyExtend, Expr.tyFreeVars, List.mem_append, Option.elim_none,
            List.nil_append]
          intro hy
          rcases hy with h | h
          · exact Or.inl (ihr (b := b) h)
          · exact Or.inr (ihb (b := b + 1) h)
      | some σ =>
          simp only [bodyExtend, Expr.tyFreeVars, List.mem_append, Option.elim_some]
          intro hy
          rcases hy with h | h
          · rcases h with h | h
            · exact Or.inl (Or.inl h)
            · exact Or.inl (Or.inr (ihr (b := b) h))
          · exact Or.inr (ihb (b := b + 1) h)
  | match_ scrut brs ihscrut ihbrs =>
      simp only [bodyExtend, Expr.tyFreeVars, List.mem_append]
      have hbrs : y ∈ Expr.tyFreeVars.BranchList.tyFreeVars (bodyExtendBranches monos G b brs)
          → y ∈ Expr.tyFreeVars.BranchList.tyFreeVars brs := by
        induction brs with
        | nil => intro hy; simp [Expr.tyFreeVars.BranchList.tyFreeVars, bodyExtendBranches] at hy
        | cons br rest ih =>
            cases br with
            | mk pat body =>
                intro hy
                simp only [bodyExtendBranches, Expr.tyFreeVars.BranchList.tyFreeVars,
                  List.mem_append] at hy ⊢
                rcases hy with h | h
                · exact Or.inl (ihbrs pat body (List.mem_cons_self ..) (b := b + pat.bindCount) h)
                · exact Or.inr (ih (fun pat' e' he' => ihbrs pat' e' (List.mem_cons_of_mem _ he')) h)
      intro hy
      rcases hy with h | h
      · exact Or.inl (ihscrut (b := b) h)
      · exact Or.inr (hbrs h)
  | letRec anns bs body ihbs ihbody =>
      simp only [bodyExtend, Expr.tyFreeVars, List.mem_append]
      have hbs' : ∀ (D : Nat),
          y ∈ Expr.tyFreeVars.RecGroup.tyFreeVars (bodyExtendGroup monos G D bs)
            → y ∈ Expr.tyFreeVars.RecGroup.tyFreeVars bs := by
        intro D
        induction bs with
        | nil => intro hy; simp [Expr.tyFreeVars.RecGroup.tyFreeVars, bodyExtendGroup] at hy
        | cons e tl ih =>
            intro hy
            simp only [bodyExtendGroup, Expr.tyFreeVars.RecGroup.tyFreeVars, List.mem_append]
              at hy ⊢
            rcases hy with h | h
            · exact Or.inl (ihbs e (List.mem_cons_self ..) (b := D) h)
            · exact Or.inr (ih (fun e' he' => ihbs e' (List.mem_cons_of_mem _ he')) h)
      intro hy
      rcases hy with h | h
      · rcases h with h | h
        · exact Or.inl (Or.inl h)
        · exact Or.inl (Or.inr (hbs' (b + bs.length) h))
      · exact Or.inr (ihbody (b := b + bs.length) h)

/-- Erase commutes with the promoted scheme: `PolyTy.eraseBounds (promoteScheme G τ) =
    promoteScheme G (Ty.eraseBounds τ)` (the body fact is `Ty.eraseBounds_closeOver`, restated
    here at the `promoteScheme` level since `LetRecPromote` imports only `Core`). -/
theorem promoteScheme_eraseBounds {G : List Nat} {τ : Ty} :
    PolyTy.eraseBounds (promoteScheme G τ) = promoteScheme G (Ty.eraseBounds τ) := by
  simp [promoteScheme, PolyTy.eraseBounds, Ty.eraseBounds_closeOver]

/-- Substitution commutes with the promoted scheme, provided the substitution avoids the pool
    `G` in both keys and range (so `closeOver`'s binder discipline is stable). -/
theorem promoteScheme_substFvars {G : List Nat} {τ : Ty} {S : List (Nat × Ty)}
    (hSG : ∀ p ∈ S, p.1 ∉ G) (hSran : ∀ p ∈ S, ∀ u ∈ p.2.freeVars, u ∉ G) :
    PolyTy.substFvars S (promoteScheme G τ) = promoteScheme G (Ty.substFvars S τ) := by
  rw [PolyTy.substFvars_eq]
  simp [promoteScheme, Ty.substFvars_closeOver hSG hSran]

/-! ### TyBvarBounded commutes for the promoted traversals

`letRecElabOut`'s all-mono node is `.letRec (promoteAnns G specs) (bs.map (retargetStored … (closeTyVars
G ·))) (bodyExtend … body)`. For `Expr.letRecElabOut_tyBvarBounded` we need that the two new traversals
respect the `TyBvarBounded` depth discipline: `retargetStored` raises the bound by `gLen` (it inserts
`Ty.bvarRangeFrom d gLen` at type-depth `d`), while `bodyExtend` preserves it (its `spreadTyArgs` emits
only `unit` fillers or the original `tyArgs`). -/

/-- Every entry of `Ty.bvarRangeFrom s n` is a `bvar` bounded by `s + n` (Core's
    `ContainsBvarsUpTo.bvarRangeFrom` is `private`, so restated here; public so the
    `InferW` mirror `Expr.letRecElabOut_tyBvarBounded` can use it). -/
lemma bvarRangeFrom_ContainsBvarsUpTo (s n : Nat) :
    ∀ t ∈ Ty.bvarRangeFrom s n, ContainsBvarsUpTo (s + n) t := by
  induction n generalizing s with
  | zero => intro t ht; simp [Ty.bvarRangeFrom] at ht
  | succ k ih =>
      intro t ht
      simp only [Ty.bvarRangeFrom, List.mem_cons] at ht
      rcases ht with rfl | ht
      · exact .bvar (by omega)
      · exact (ih (s + 1) t ht).mono (by omega)

/-- `prim .unit` has no `bvar`s, so is bounded by any bound. -/
private lemma ContainsBvarsUpTo_prim_unit {n : Nat} : ContainsBvarsUpTo n (Ty.prim .unit) := by
  exact .prim

/-- The spread preserves `ContainsBvarsUpTo n` pointwise: every emitted entry is either an
    original `tyArgs` element (bounded by hypothesis) or the `unit` filler (bounded trivially). -/
private lemma spreadTyArgs_ContainsBvarsUpTo {G : List Nat} {μ : Ty} {tyArgs : List Ty} {n : Nat}
    (h : ∀ t ∈ tyArgs, ContainsBvarsUpTo n t) :
    ∀ t ∈ spreadTyArgs G μ tyArgs, ContainsBvarsUpTo n t := by
  induction G generalizing tyArgs with
  | nil => simp [spreadTyArgs]
  | cons g gs ih =>
      by_cases hg : g ∈ μ.freeVars
      · cases tyArgs with
        | nil =>
            intro t ht
            have hstep : spreadTyArgs (g :: gs) μ [] = Ty.prim .unit :: spreadTyArgs gs μ [] := by
              conv_lhs => rw [spreadTyArgs.eq_def]
              simp [hg]
            rw [hstep] at ht
            simp [List.mem_cons] at ht
            rcases ht with h1 | h2
            · rw [h1]
              exact .prim
            · exact ih (tyArgs := []) (fun t' ht' => False.elim (List.not_mem_nil ht')) t h2
        | cons t ts =>
            intro t' ht'
            have hstep : spreadTyArgs (g :: gs) μ (t :: ts) = t :: spreadTyArgs gs μ ts := by
              conv_lhs => rw [spreadTyArgs.eq_def]
              simp [hg]
            rw [hstep] at ht'
            simp [List.mem_cons] at ht'
            rcases ht' with h1 | h2
            · rw [h1]
              exact h t (List.mem_cons_self ..)
            · exact ih (tyArgs := ts) (fun u hu => h u (List.mem_cons_of_mem _ hu)) t' h2
      · intro t ht
        have hstep : spreadTyArgs (g :: gs) μ tyArgs = Ty.prim .unit :: spreadTyArgs gs μ tyArgs := by
          conv_lhs => rw [spreadTyArgs.eq_def]
          simp [hg]
        rw [hstep] at ht
        simp [List.mem_cons] at ht
        rcases ht with h1 | h2
        · rw [h1]
          exact .prim
        · exact ih (tyArgs := tyArgs) h t h2

/-- `retargetStored` raises the bvar bound by `gLen`: a term bounded at type-depth `d` retargets to
    one bounded at `d + gLen` (the inserted pool `bvar`s are exactly `[d, d + gLen)`). -/
theorem retargetStored_tyBvarBounded {mono : Nat → Bool} {gLen d b : Nat} {e : Expr} :
    e.TyBvarBounded d → (retargetStored mono gLen d b e).TyBvarBounded (d + gLen) := by
  induction e using Expr.rec_strong generalizing b d with
  | primLit p => simp [retargetStored, Expr.TyBvarBounded]
  | primBinOp op => simp [retargetStored, Expr.TyBvarBounded]
  | ctor nm => simp [retargetStored, Expr.TyBvarBounded]
  | var i tyArgs =>
      intro h
      by_cases hwin : b ≤ i ∧ mono (i - b)
      · simp [retargetStored, Expr.TyBvarBounded, hwin]
        exact bvarRangeFrom_ContainsBvarsUpTo d gLen
      · simp [retargetStored, Expr.TyBvarBounded, hwin]
        intro t ht
        exact (h t ht).mono (by omega)
  | lambda ann body ih =>
      intro h
      rcases h with ⟨hann, hbody⟩
      simp only [retargetStored, Expr.TyBvarBounded]
      constructor
      · intro t ht
        exact (hann t ht).mono (by omega)
      · exact ih (b := b + 1) (d := d) hbody
  | app f arg ihf iharg =>
      intro h
      rcases h with ⟨hf, harg⟩
      simp only [retargetStored, Expr.TyBvarBounded]
      exact ⟨ihf (b := b) (d := d) hf, iharg (b := b) (d := d) harg⟩
  | letIn ann rhs body ihr ihb =>
      intro h
      cases ann with
      | none =>
          rcases h with ⟨hr, hb⟩
          simp only [retargetStored, Expr.TyBvarBounded]
          exact ⟨ihr (b := b) (d := d) hr, ihb (b := b + 1) (d := d) hb⟩
      | some σ =>
          rcases h with ⟨hσ, hr, hb⟩
          simp only [retargetStored, Expr.TyBvarBounded]
          constructor
          · exact hσ.mono (by omega)
          · constructor
            · have hd : (d + σ.paramCount) + gLen = (d + gLen) + σ.paramCount := by omega
              rw [← hd]
              exact ihr (b := b) (d := d + σ.paramCount) hr
            · exact ihb (b := b + 1) (d := d) hb
  | match_ scrut brs ihscrut ihbrs =>
      have hbrs' : Expr.TyBvarBounded.BranchList d brs →
          Expr.TyBvarBounded.BranchList (d + gLen) (retargetStoredBranches mono gLen d b brs) := by
        induction brs with
        | nil => simp [Expr.TyBvarBounded.BranchList, retargetStoredBranches]
        | cons br rest ih =>
            cases br with
            | mk pat body =>
                intro hb0
                simp only [Expr.TyBvarBounded.BranchList, retargetStoredBranches] at hb0 ⊢
                rcases hb0 with ⟨hb, htail⟩
                constructor
                · exact ihbrs pat body (List.mem_cons_self ..) (b := b + pat.bindCount) (d := d) hb
                · exact ih (fun pat' e' he' => ihbrs pat' e' (List.mem_cons_of_mem _ he')) htail
      intro h
      rcases h with ⟨hscrut, hbrs0⟩
      simp only [retargetStored, Expr.TyBvarBounded]
      exact ⟨ihscrut (b := b) (d := d) hscrut, hbrs' hbrs0⟩
  | letRec anns bs body ihbs ihbody =>
      have hbs' : ∀ (D : Nat) (anns' : List (Option PolyTy)),
          Expr.TyBvarBounded.RecGroup d anns' bs →
          Expr.TyBvarBounded.RecGroup (d + gLen) anns'
            (retargetStoredGroup mono gLen d D anns' bs) := by
        intro D anns'
        revert anns'
        induction bs with
        | nil => intro anns' h'; simp [Expr.TyBvarBounded.RecGroup, retargetStoredGroup]
        | cons e tl ih =>
            intro anns' h'
            cases anns' with
            | nil =>
                simp only [retargetStoredGroup, Expr.TyBvarBounded.RecGroup] at h' ⊢
                rcases h' with ⟨he, htl⟩
                constructor
                · exact ihbs e (List.mem_cons_self ..) (b := D) (d := d) he
                · exact ih (fun e' he' => ihbs e' (List.mem_cons_of_mem _ he')) [] htl
            | cons a as =>
                simp only [retargetStoredGroup, Expr.TyBvarBounded.RecGroup] at h' ⊢
                rcases h' with ⟨he, htl⟩
                constructor
                · have hd : (d + RecAnn.params a) + gLen = (d + gLen) + RecAnn.params a := by omega
                  rw [← hd]
                  exact ihbs e (List.mem_cons_self ..) (b := D) (d := d + RecAnn.params a) he
                · exact ih (fun e' he' => ihbs e' (List.mem_cons_of_mem _ he')) as htl
      intro h
      rcases h with ⟨hann, hrec, hbody⟩
      simp only [retargetStored, Expr.TyBvarBounded]
      constructor
      · intro σ hσ
        exact (hann σ hσ).mono (by omega)
      · constructor
        · exact hbs' (b + bs.length) anns hrec
        · exact ihbody (b := b + bs.length) (d := d) hbody

/-- `bodyExtend` preserves the bvar bound (`spreadTyArgs` emits `unit` fillers or original `tyArgs`,
    never new `bvar`s). -/
theorem bodyExtend_tyBvarBounded {monos : List Ty} {G : List Nat} {b n : Nat} {e : Expr} :
    e.TyBvarBounded n → (bodyExtend monos G b e).TyBvarBounded n := by
  induction e using Expr.rec_strong generalizing b n with
  | primLit p => simp [bodyExtend, Expr.TyBvarBounded]
  | primBinOp op => simp [bodyExtend, Expr.TyBvarBounded]
  | ctor nm => simp [bodyExtend, Expr.TyBvarBounded]
  | var i tyArgs =>
      intro h
      by_cases hwin : b ≤ i ∧ i < b + monos.length
      · simp [bodyExtend, Expr.TyBvarBounded, hwin]
        exact spreadTyArgs_ContainsBvarsUpTo h
      · simp [bodyExtend, Expr.TyBvarBounded, hwin]
        exact h
  | lambda ann body ih =>
      intro h
      rcases h with ⟨hann, hbody⟩
      simp only [bodyExtend, Expr.TyBvarBounded]
      exact ⟨hann, ih (b := b + 1) hbody⟩
  | app f arg ihf iharg =>
      intro h
      rcases h with ⟨hf, harg⟩
      simp only [bodyExtend, Expr.TyBvarBounded]
      exact ⟨ihf (b := b) hf, iharg (b := b) harg⟩
  | letIn ann rhs body ihr ihb =>
      intro h
      cases ann with
      | none =>
          rcases h with ⟨hr, hb⟩
          simp only [bodyExtend, Expr.TyBvarBounded]
          exact ⟨ihr (b := b) hr, ihb (b := b + 1) hb⟩
      | some σ =>
          rcases h with ⟨hσ, hr, hb⟩
          simp only [bodyExtend, Expr.TyBvarBounded]
          exact ⟨hσ, ihr (b := b) hr, ihb (b := b + 1) hb⟩
  | match_ scrut brs ihscrut ihbrs =>
      have hbrs' : Expr.TyBvarBounded.BranchList n brs →
          Expr.TyBvarBounded.BranchList n (bodyExtendBranches monos G b brs) := by
        induction brs with
        | nil => simp [Expr.TyBvarBounded.BranchList, bodyExtendBranches]
        | cons br rest ih =>
            cases br with
            | mk pat body =>
                intro hb0
                simp only [Expr.TyBvarBounded.BranchList, bodyExtendBranches] at hb0 ⊢
                rcases hb0 with ⟨hb, htail⟩
                constructor
                · exact ihbrs pat body (List.mem_cons_self ..) (b := b + pat.bindCount) hb
                · exact ih (fun pat' e' he' => ihbrs pat' e' (List.mem_cons_of_mem _ he')) htail
      intro h
      rcases h with ⟨hscrut, hbrs0⟩
      simp only [bodyExtend, Expr.TyBvarBounded]
      exact ⟨ihscrut (b := b) hscrut, hbrs' hbrs0⟩
  | letRec anns bs body ihbs ihbody =>
      have hbs' : ∀ (D : Nat) (anns' : List (Option PolyTy)),
          Expr.TyBvarBounded.RecGroup n anns' bs →
          Expr.TyBvarBounded.RecGroup n anns' (bodyExtendGroup monos G D bs) := by
        intro D anns'
        revert anns'
        induction bs with
        | nil => intro anns' h'; simp [Expr.TyBvarBounded.RecGroup, bodyExtendGroup]
        | cons e tl ih =>
            intro anns' h'
            cases anns' with
            | nil =>
                simp only [bodyExtendGroup, Expr.TyBvarBounded.RecGroup] at h' ⊢
                rcases h' with ⟨he, htl⟩
                constructor
                · exact ihbs e (List.mem_cons_self ..) (b := D) he
                · exact ih (fun e' he' => ihbs e' (List.mem_cons_of_mem _ he')) [] htl
            | cons a as =>
                simp only [bodyExtendGroup, Expr.TyBvarBounded.RecGroup] at h' ⊢
                rcases h' with ⟨he, htl⟩
                constructor
                · exact ihbs e (List.mem_cons_self ..) (b := D) (n := n + RecAnn.params a) he
                · exact ih (fun e' he' => ihbs e' (List.mem_cons_of_mem _ he')) as htl
      intro h
      rcases h with ⟨hann, hrec, hbody⟩
      simp only [bodyExtend, Expr.TyBvarBounded]
      constructor
      · exact hann
      · constructor
        · exact hbs' (b + bs.length) anns hrec
        · exact ihbody (b := b + bs.length) hbody

/-! ## Axiom guard

Records that the results rest only on the standard axioms (`propext`, `Classical.choice`,
`Quot.sound`) — no `sorryAx`. -/

#print axioms retarget_transport
#print axioms monoTyped_to_polyTyped
#print axioms polyTyped_to_monoTyped
#print axioms retargetStored_openTyVars
#print axioms promoted_preservation
#print axioms promoteScheme_wf
#print axioms promoteScheme_openVars
#print axioms smoke_promoted_selfref
#print axioms mutual_promoted
#print axioms mutual_mixed_promoted
#print axioms bodyScheme_weaken

end LetRecPromote
