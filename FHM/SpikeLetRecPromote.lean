import FHM.InferW

/-! # Spike: promote unannotated `letRec` members to annotated ones

**Not in `defaultTargets`.** Companion to `briefs/complexity-budget.md` §3.4. Style follows
the retired `SpikeLetRecMixed` (declarative derivations, no `Infer` involvement).

## The question

`Infer.letRec` currently elaborates a mixed group into `Expr.letRecElab`: an `n`-deep nest of
`letIn`s, each wrapping a whole copy of the group projected at one member. It does that
because an unannotated member is generalised for the body but has **no Λ-binder in the term**
for `.var j tyArgs` to instantiate — so the Λ is hoisted outside as a `letIn` scheme.

The nest changes the elaboratum's *shape*, which is what forces `Infer.sourceSound` to be a
second full induction rather than a corollary of `Infer.sound`.

**Proposed alternative:** put the Λ *inside* the node, using the `anns` slot that is already
there. Promote each `.mono τ` member to `.poly ⟨|G|, Ty.closeOver G τ⟩` — generalising over
the **full pool `G`**, not `Ty.genFilter G τ` — and retarget group-internal uses from
`.var j []` to `.var j (Ty.bvarRangeFrom d |G|)`.

Full pool rather than the filter, because then every promoted member has the *same* arity
`|G|` and the same binder positions, so a sibling reference `.var j (bvarRange |G|)` uniformly
means "instantiate sibling `j` at **my** pool binders" — which is exactly what reconstitutes
the shared-monotype link that `RecSpecs.MonoTyped`'s "same `Xs` for the whole group" enforces.
Under `genFilter` the arities differ per member and the indices would not line up.

Legal because `PolyTy.WF M := ContainsBvarsUpTo M.paramCount M.body` is an *upper bound*, not
a usage requirement — vacuous binders are well-formed.

**`Expr` is unchanged throughout.** This is slot-filling, the same kind elaboration already
does for `letIn`.

## Scope of this spike

Deliberately narrow: does the **encoding** work at all? `P1`/`P2` are the type-level core;
`S1`–`S2'` are concrete derivations, and `S2'` is make-or-break.

Explicitly **out of scope**, and only worth writing if `S2'` goes through:

- the general retarget traversal (a depth-tracking map over all `Expr` cases — `d` for
  type-binder depth, `b` for term depth). `Expr.openTyVarsAux` already descends into `var`'s
  `tyArgs` (`Core.lean:2344`) and `Ty.bvarRangeFrom` (`Core.lean:367`) is the depth-shifted
  builder, so the pieces exist.
- the general transport `MonoTyped … → PolyTyped … (promoteSpecs G specs) []`. Sketch: fix a
  fresh `Ys`; rename `G ↦ Ys` through the mono derivation
  (`TypeOfElabHM.typ_subst_preservation_uniform`); sibling `k`'s env entry changes from
  `PolyTy.mkTrivial (Ty.renameG G Ys τₖ)` to `promoteScheme G τₖ`, and by `P2` the latter
  opened at `Ys` *is* the former's body — so each sibling use is reconstituted by the `var`
  rule at `tyArgs = Ys`, which is what the retarget put in the term.

Note that once every member is `poly`, `RecSpecs.rhsCtx` stops depending on the pool opening,
so `MonoTyped` becomes vacuous and `PolyTyped`'s outer `Xs` quantifier collapses — which is
where the `RecSpec` mono/poly split goes away.
-/

namespace SpikeLetRecPromote

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

/-! ## P1 / P2 — the type-level core

If these are one-liners, the brief's "full pool is *cheaper* than `genFilter`" claim holds:
`PolyTy.genGroup`'s analogues (`Ty.renameG_eq_genFilter`, `PolyTy.genGroup_renameG`) have to
route through filter-nodup / filter-disjointness bookkeeping to reach the same place — that
is roughly half of `TypeOfElabHM.rewrap_hasScheme_mono`'s 79 lines. -/

/-- **P1.** The promoted scheme is well-formed even when `τ` mentions only part of `G`
    (i.e. even with vacuous binders). The fact the whole encoding rests on. -/
theorem promoteScheme_wf {G : List Nat} {τ : Ty} (hτ : τ.IsLC) :
    (promoteScheme G τ).WF :=
  Ty.closeOver_preserves_bvars hτ

/-- **P2 — the pivotal type-level fact.** Opening the promoted scheme at `Xs` recovers exactly
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

/-! ## S1 / S2 — concrete smoke tests

`S1` has no group-internal reference (so no retarget is needed); `S2` does, and is the
retarget in miniature. Both use the empty context `⟨[], []⟩`.

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

/-- **S1 (mono, as today).** The member is typed monomorphically at `fvar 0 → fvar 0` inside
    the group and generalised for the body, which uses it at `int`. -/
theorem S1_mono :
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

/-- **S1' (promoted).** The same program with the generalised scheme written into the `anns`
    slot. Same constructor, same shape, same body — only the slot is filled. -/
theorem S1_promoted :
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

/-- **S2 (mono, with self-reference).** `λx. self x`. Inside the binding, index `1` is the
    group member; in the mono regime it is bound at `mkTrivial`, so its use carries
    `tyArgs = []`. -/
theorem S2_mono :
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

/-- **S2' (promoted, retargeted) — the make-or-break test.** Same program, scheme in the slot,
    and the self-reference retargeted from `.var 1 []` to `.var 1 [.bvar 0]`: the member
    instantiating its own `1`-ary scheme at its own pool binder
    (`Ty.bvarRangeFrom 0 1 = [.bvar 0]`).

    If this goes through, the encoding works and §3.4 of the brief is viable. If it does not,
    §3.4 is dead and the brief needs restating — **report rather than working around it.** -/
theorem S2_promoted :
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

/-! ## D1 / D2 — the discriminating tests

`S1`–`S2'` above are warm-ups: they use `n = 1` and a monotype that mentions **all** of `G`,
so `Ty.genFilter G τ = G` and the full-pool choice is indistinguishable from the filtered one.
They also have no siblings, so the mechanism that motivates the full pool — uniform arity, so
that a *sibling* reference `.var j (bvarRange |G|)` lines up — is never exercised.

These two do exercise it. Pool `G₂ = [0, 1]` throughout.

- **D1** — genuine *mutual* reference, both members at `τA = fvar 0 → fvar 0`. Neither
  mentions pool var `1`, so each promoted scheme carries a **vacuous** second binder. Under
  `genFilter` both would be arity 1; under the full pool both are arity 2.
- **D2** — members at `τA` and `τB = fvar 1 → fvar 1`. Under the full pool these are
  `⟨2, bvar 0 → bvar 0⟩` and `⟨2, bvar 1 → bvar 1⟩` — same arity, **different binder
  positions**, each vacuous in the other's slot. Under `genFilter` both would collapse to
  `⟨1, bvar 0 → bvar 0⟩` and member 1's index would *shift*. This is the index-alignment test.

Note a consequence surfaced while writing these: promotion changes the **body**'s `tyArgs`
arity too (mono body sees `PolyTy.genGroup G τ` at filtered arity; promoted body sees the
full-pool scheme), so the retarget applies to the body as well as to the bindings. Record that
in the brief if D1/D2 pass — it slightly widens the traversal described in §3.4.

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

/-- **D1 (mono).** Mutually recursive pair, both at `τA`; body uses member 0 at `int`. -/
theorem D1_mono :
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

/-- **D1' (promoted).** Same group, schemes in the slots, sibling references retargeted to
    `[.bvar 0, .bvar 1]`, body at the full-pool arity. Exercises: mutual sibling reference,
    a vacuous binder, uniform arity 2, and a 2-element retargeted `tyArgs`. -/
theorem D1_promoted :
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

/-- **D2 (mono).** Members at `τA` and `τB` — different pool usage, self-recursive each. -/
theorem D2_mono :
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

/-- **D2' (promoted) — the index-alignment test.** `σA` and `σB` are vacuous in *opposite*
    binder slots but share arity 2, so the single uniform retarget `[.bvar 0, .bvar 1]` must
    work for both. Under `genFilter` it could not: the two schemes would have different binder
    positions at the same index.

    If this fails, the full-pool choice does not do what §3.4 claims and the brief needs
    restating — **report the obstruction, do not weaken the statement.** -/
theorem D2_promoted :
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

/-! ## T — the transport (THE GATE)

`D1`/`D2` exhibit mono and promoted derivations *independently* for concrete programs. This
section attempts the general claim they do not establish: that a mono-regime derivation can be
**converted** into a promoted one.

### Why this is new work

`TypeOfHM.weaken_schemes` (`InferW.lean:15487`) already swaps a whole env prefix for more
general schemes — but on `TypeOfHM`, whose `var` rule instantiates *existentially*, so the term
is untouched. `TypeOfElabHM.var` stores `tyArgs` and pins their arity
(`Ty.AreLC polyTy.paramCount tyArgs`), so replacing `PolyTy.mkTrivial τ` (arity 0, `tyArgs = []`)
with a scheme of arity `|G|` **forces** the term to change. Nothing in the codebase does that
today, because `letRecElab` sidesteps it by hoisting the Λ outside instead.

### Scope

Stated on **opened** terms: `Vs` are concrete `Ty`s (the pool opening as `fvar`s), not `bvar`s.
That removes type-binder depth tracking from the retarget entirely — `Vs` is depth-independent
— leaving only term-binder depth `b`. The stored-vs-opened commute
(`(storedRetarget e).openTyVars Ys = retargetVars … (e.openTyVars Ys)`) is bookkeeping for
later; it is not the gate.

**`T1` is the gate.** If it holds, the promotion is a valid refactor modulo bookkeeping. If it
fails, §3.4 of the brief is dead and should be struck. -/

mutual

/-- Retarget group-variable uses in an **opened** term: a use of one of the `n` innermost
    binders at term-depth `b` gets `tyArgs := Vs` instead of `[]`. -/
def retargetVars (n : Nat) (Vs : List Ty) (b : Nat) : Expr → Expr
  | .primLit p          => .primLit p
  | .primBinOp op       => .primBinOp op
  | .lambda ann body    => .lambda ann (retargetVars n Vs (b + 1) body)
  | .app f arg          => .app (retargetVars n Vs b f) (retargetVars n Vs b arg)
  | .letIn ann rhs body =>
      .letIn ann (retargetVars n Vs b rhs) (retargetVars n Vs (b + 1) body)
  | .var i tyArgs       => if b ≤ i ∧ i < b + n then .var i Vs else .var i tyArgs
  | .ctor c             => .ctor c
  | .match_ scrut brs   =>
      .match_ (retargetVars n Vs b scrut) (retargetBranches n Vs b brs)
  | .letRec anns bs body =>
      .letRec anns (retargetGroup n Vs (b + bs.length) bs)
        (retargetVars n Vs (b + bs.length) body)

def retargetBranches (n : Nat) (Vs : List Ty) (b : Nat) :
    List (MatchPattern × Expr) → List (MatchPattern × Expr)
  | []                  => []
  | (pat, body) :: rest =>
      (pat, retargetVars n Vs (b + pat.bindCount) body) :: retargetBranches n Vs b rest

def retargetGroup (n : Nat) (Vs : List Ty) (b : Nat) : List Expr → List Expr
  | []        => []
  | e :: rest => retargetVars n Vs b e :: retargetGroup n Vs b rest

end

/-! ### T1 machinery: retarget bookkeeping -/

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
theorem retargetGroup_length {n b : Nat} {Vs : List Ty} (bs : List Expr) :
    (retargetGroup n Vs b bs).length = bs.length := by
  induction bs with
  | nil => rfl
  | cons e tl ih => simp only [retargetGroup, List.length_cons, ih]

/-- Retargeting a term commutes with opening its scoped type variables: the
    retarget only replaces the `tyArgs` of group-window `var`s with the LC `Vs`,
    and opening only touches `bvar`s, which `Vs` does not contain. -/
theorem retargetVars_openTyVarsAux {n b d : Nat} {Vs : List Ty} {Xs : List Nat} {e : Expr}
    (hVsLC : ∀ V ∈ Vs, V.IsLC) :
    (retargetVars n Vs b e).openTyVarsAux d Xs = retargetVars n Vs b (e.openTyVarsAux d Xs) := by
  induction e using Expr.rec_strong generalizing b d with
  | primLit p => rfl
  | primBinOp op => rfl
  | ctor nm => rfl
  | var i tyArgs =>
      by_cases hwin : b ≤ i ∧ i < b + n
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
      have hbrs : BranchList.openTyVarsAux d Xs (retargetBranches n Vs b brs)
          = retargetBranches n Vs b (BranchList.openTyVarsAux d Xs brs) := by
        induction brs with
        | nil => rfl
        | cons br rest ih =>
            cases br with
            | mk pat body =>
                have hhead : (retargetVars n Vs (b + pat.bindCount) body).openTyVarsAux d Xs
                    = retargetVars n Vs (b + pat.bindCount) (body.openTyVarsAux d Xs) :=
                  ihbrs pat body (List.mem_cons_self ..) (b := b + pat.bindCount) (d := d)
                simp only [retargetBranches, BranchList.openTyVarsAux]
                rw [hhead]
                congr 1
                exact ih (fun pat' e' he' => ihbrs pat' e' (List.mem_cons_of_mem _ he'))
      rw [hbrs]
  | letRec anns bs body ihbs ihbody =>
      simp only [retargetVars, Expr.openTyVarsAux, ihbody (b := b + bs.length) (d := d)]
      have hbs' : ∀ (D : Nat) (anns : List (Option PolyTy)),
          RecGroup.openTyVarsAux d Xs anns (retargetGroup n Vs D bs)
            = retargetGroup n Vs D (RecGroup.openTyVarsAux d Xs anns bs) := by
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
theorem retargetVars_openTyVars {n b : Nat} {Vs : List Ty} {Xs : List Nat} {e : Expr}
    (hVsLC : ∀ V ∈ Vs, V.IsLC) :
    (retargetVars n Vs b e).openTyVars Xs = retargetVars n Vs b (e.openTyVars Xs) := by
  simpa only [Expr.openTyVars] using retargetVars_openTyVarsAux (d := 0) (hVsLC := hVsLC) (e := e)

/-- The `let` rule's cofinite opener commutes with the retarget. -/
theorem retargetVars_openBoundTyVars {n b : Nat} {Vs : List Ty} {Xs : List Nat} {e : Expr}
    {ann : Option PolyTy} (hVsLC : ∀ V ∈ Vs, V.IsLC) :
    retargetVars n Vs b (Expr.openBoundTyVars ann Xs e)
      = Expr.openBoundTyVars ann Xs (retargetVars n Vs b e) := by
  cases ann with
  | none => rfl
  | some σ => simpa only [Expr.openBoundTyVars, Expr.openTyVars] using
      (retargetVars_openTyVarsAux (d := 0) (hVsLC := hVsLC) (e := e)).symm

/-- Every pair of the retargeted-zip is the retarget of a pair of the original zip. -/
theorem retargetGroup_zip_mem {n b : Nat} {Vs : List Ty} :
    ∀ (bs : List Expr) (specs : List RecSpec) (p : Expr × RecSpec),
      p ∈ (retargetGroup n Vs b bs).zip specs →
        ∃ q, q ∈ bs.zip specs ∧ p.1 = retargetVars n Vs b q.1 ∧ p.2 = q.2 := by
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
theorem retargetBranches_ne_nil {n b : Nat} {Vs : List Ty}
    {brs : List (MatchPattern × Expr)} (h : brs ≠ []) :
    retargetBranches n Vs b brs ≠ [] := by
  intro h'
  cases brs with
  | nil => exact h rfl
  | cons br rest =>
      simp only [retargetBranches, List.cons_ne_nil] at h'

/-- Every retargeted branch is the retarget of an original branch (pattern kept). -/
theorem retargetBranches_mem {n b : Nat} {Vs : List Ty} :
    ∀ (brs : List (MatchPattern × Expr)) (br' : MatchPattern × Expr),
      br' ∈ retargetBranches n Vs b brs →
        ∃ pat body, (pat, body) ∈ brs ∧ br' = (pat, retargetVars n Vs (b + pat.bindCount) body) := by
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

/-- **T1 — THE GATE.** A `TypeOfElabHM` derivation over an env prefix of *monomorphic* entries
    transports to one over promoted **schemes**, provided each scheme instantiated at `Vs`
    yields the corresponding monotype, and group-variable uses are retargeted to `Vs`.

    This is the `TypeOfElabHM` analogue of `TypeOfHM.weaken_schemes`, with the term rewrite
    that the type-passing `var` rule forces.

    Expected shape: induction via `TypeOfElabHM.rec_strong`, generalising over the env prefix
    (as `weaken_schemes` does with its `ep` accumulator) so that binder-introducing cases can
    push `b`. The `var` case is where the content is: in the mono env the entry is
    `PolyTy.mkTrivial μₖ` with `InstantiatesTo [] μₖ`; in the promoted env it is `Mₖ` with
    `InstantiatesTo Vs μₖ` — the same result type, which is exactly `hinst`. -/
theorem T1_retarget_transport
    {ctors : CtorEnv} {env : Env} {e : Expr} {τ : Ty}
    {monos : List Ty} {Ms : List PolyTy} {Vs : List Ty}
    (hVsLC : ∀ V ∈ Vs, V.IsLC)
    (hinst : List.Forall₂
      (fun (M : PolyTy) (μ : Ty) => M.paramCount = Vs.length ∧ M.InstantiatesTo Vs μ) Ms monos)
    (h : TypeOfElabHM ⟨monos.map PolyTy.mkTrivial ++ env, ctors⟩ e τ) :
    TypeOfElabHM ⟨Ms ++ env, ctors⟩ (retargetVars Ms.length Vs 0 e) τ := by
  have hlen : Ms.length = monos.length := List.Forall₂.length_eq hinst
  have H : ∀ {ctx : Ctx} {e₀ : Expr} {τ₀ : Ty}, TypeOfElabHM ctx e₀ τ₀ →
      ∀ ep : Env, ctx.env = ep ++ monos.map PolyTy.mkTrivial ++ env →
      TypeOfElabHM ⟨ep ++ Ms ++ env, ctx.ctors⟩ (retargetVars Ms.length Vs ep.length e₀) τ₀ := by
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
        by_cases hwin : ep.length ≤ dbl ∧ dbl < ep.length + Ms.length
        · have hwin_mono : ep.length ≤ dbl ∧ dbl < ep.length + monos.length := by
            rcases hwin with ⟨h1, h2⟩
            exact ⟨h1, by simpa [hlen] using h2⟩
          let k : Nat := dbl - ep.length
          have hk : k < monos.length := by
            dsimp [k]
            omega
          have hkM : k < Ms.length := by
            rw [hlen]
            exact hk
          have hdbl : dbl - ep.length = k := rfl
          have hlook_prom : (ep ++ Ms ++ env)[dbl]? = some (Ms[k]) := by
            rw [List.append_assoc, List.getElem?_append_right (by omega : ep.length ≤ dbl)]
            rw [hdbl]
            rw [List.getElem?_append_left hkM]
            rw [List.getElem?_eq_getElem hkM]
          have hkMap : k < (monos.map PolyTy.mkTrivial).length := by
            simpa using hk
          have hlook_mono : (ep ++ monos.map PolyTy.mkTrivial ++ env)[dbl]? =
              some (PolyTy.mkTrivial (monos[k])) := by
            rw [List.append_assoc, List.getElem?_append_right (by omega : ep.length ≤ dbl)]
            rw [hdbl]
            rw [List.getElem?_append_left hkMap]
            rw [List.getElem?_eq_getElem hkMap]
            simp
          have hpoly_eq : polyTy = PolyTy.mkTrivial (monos[k]) :=
            Option.some.inj (hlook.symm.trans hlook_mono)
          subst hpoly_eq
          have htyArgs : tyArgs = [] := by
            rcases hlc with ⟨hlen0, _⟩
            exact List.eq_nil_of_length_eq_zero hlen0
          have hty : ty = monos[k] := by
            have hinst0 : InstantiatesBy [] (monos[k]) ty := by
              simpa [PolyTy.InstantiatesTo, htyArgs] using hinst'
            exact InstantiatesBy_empty_eq hinst0
          have hrel := List.Forall₂.get hinst hkM hk
          simp only [retargetVars]
          rw [if_pos hwin]
          refine TypeOfElabHM.var (polyTy := Ms[k]) ?_ ?_ ?_
          · show (ep ++ Ms ++ env)[dbl]? = some (Ms[k])
            exact hlook_prom
          · show Ty.AreLC (Ms[k]).paramCount Vs
            exact ⟨hrel.1.symm, hVsLC⟩
          · show (Ms[k]).InstantiatesTo Vs ty
            rw [hty]
            exact hrel.2
        · have hnotwin : ¬ (ep.length ≤ dbl ∧ dbl < ep.length + monos.length) := by
            intro h
            rcases h with ⟨h1, h2⟩
            exact hwin ⟨h1, by simpa [hlen] using h2⟩
          by_cases hlt : dbl < ep.length
          · simp only [retargetVars]
            rw [if_neg hwin]
            refine TypeOfElabHM.var ?_ hlc hinst'
            show (ep ++ Ms ++ env)[dbl]? = some polyTy
            rw [List.append_assoc, List.getElem?_append_left hlt]
            rw [List.append_assoc, List.getElem?_append_left hlt] at hlook
            exact hlook
          · have hle : ep.length ≤ dbl := by omega
            have hnlt : ¬ dbl < ep.length + Ms.length := by
              intro h
              exact hwin ⟨hle, h⟩
            have hge : ep.length + Ms.length ≤ dbl := by omega
            have hge_mono : ep.length + monos.length ≤ dbl := by simpa [hlen] using hge
            simp only [retargetVars]
            rw [if_neg hwin]
            refine TypeOfElabHM.var ?_ hlc hinst'
            show (ep ++ Ms ++ env)[dbl]? = some polyTy
            rw [List.append_assoc, List.getElem?_append_right hle]
            rw [List.append_assoc, List.getElem?_append_right hle] at hlook
            have hdM : Ms.length ≤ dbl - ep.length := by omega
            have hdm : monos.length ≤ dbl - ep.length := by omega
            have hdm' : (monos.map PolyTy.mkTrivial).length ≤ dbl - ep.length := by
              simpa using hdm
            rw [List.getElem?_append_right hdM]
            rw [List.getElem?_append_right hdm'] at hlook
            have hidx : (dbl - ep.length) - Ms.length = (dbl - ep.length) - monos.length := by
              rw [hlen]
            rw [hidx]
            rw [show (dbl - ep.length) - (monos.map PolyTy.mkTrivial).length
                = (dbl - ep.length) - monos.length from by simp] at hlook
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
          have hw : TypeOfElabHM ⟨ep ++ Ms ++ env, ctx.ctors⟩
              (retargetVars Ms.length Vs (ep.length + (MatchPattern.wildcard).bindCount) body) resultTy := by
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

/-! ### T2 machinery -/

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

/-- The pivotal fact for T2: a promoted scheme instantiated at the fresh `Ys` recovers the
    `G ↦ Ys` renaming of its monotype — exactly `T1`'s `hinst` hypothesis at each member. -/
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

/-- **T2.** The letRec-shaped corollary: a mono group's `RecSpecs.MonoTyped` premise yields the
    promoted group's `RecSpecs.PolyTyped` premise at the full-pool schemes.

    Given `T1`, the remaining content is `promoteScheme_openVars` (P2) to see that
    `(promoteScheme G τ).openVars Ys` **is** `Ty.renameG G Ys τ` — so the promoted member's
    target type is literally the mono member's — plus the observation that once every spec is
    `poly`, `RecSpecs.rhsCtx` no longer depends on the pool opening.

    `bindings'` is left universally quantified with its defining equation as a hypothesis, so
    T2 does not depend on the stored-vs-opened commute. -/
theorem T2_monoTyped_to_polyTyped
    {ctx : Ctx} {bindings bindings' : List Expr} {monos : List Ty} {G L : List Nat}
    (hGnodup : G.Nodup)
    (hmonoLC : ∀ μ ∈ monos, μ.IsLC)
    (hlen : bindings.length = monos.length)
    (hmono : RecSpecs.MonoTyped TypeOfElabHM ctx bindings (monos.map RecSpec.mono) G L)
    (hopen : ∀ Ys, FreshNames (L ++ G) G.length Ys →
      ∀ p ∈ bindings.zip bindings',
        p.2.openTyVars Ys
          = retargetVars monos.length (Ys.map Ty.fvar) 0 p.1) :
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
      ⟨(monos.map (Ty.renameG G Ys ·)).map PolyTy.mkTrivial ++ ctx.env, ctx.ctors⟩
      (bindings[k]) (Ty.renameG G Ys (monos[k])) := by
    simpa [RecSpecs.rhsCtx, List.map_map, RecSpec.rhsEntry] using
      hmono Ys hFreshL (bindings[k], RecSpec.mono (monos[k])) hmonoPair (monos[k]) rfl
  have hinst_list : List.Forall₂
      (fun (M : PolyTy) (μ : Ty) =>
        M.paramCount = (Ys.map Ty.fvar).length ∧ M.InstantiatesTo (Ys.map Ty.fvar) μ)
      (monos.map (promoteScheme G ·)) (monos.map (Ty.renameG G Ys ·)) := by
    apply Forall₂_map_of_forall
    intro μ hμ
    exact promoteScheme_instantiatesTo (hmonoLC μ hμ) hGnodup hfYs'.length hdisj
  have hVsLC : ∀ V ∈ Ys.map Ty.fvar, V.IsLC := by
    intro V hV
    rcases List.mem_map.mp hV with ⟨y, _, rfl⟩
    exact .fvar
  have hT1 := T1_retarget_transport (Ms := monos.map (promoteScheme G ·))
    (monos := monos.map (Ty.renameG G Ys ·)) (Vs := Ys.map Ty.fvar) (env := ctx.env)
    (ctors := ctx.ctors) (e := bindings[k]) (τ := Ty.renameG G Ys (monos[k]))
    hVsLC hinst_list hmono_der
  rw [hp1, hσ']
  rw [hopen Ys hfYs' (bindings[k], bindings'[k]) hpair]
  rw [promoteScheme_openVars (hmonoLC (monos[k]) hmonoLCmem) hGnodup hfYs'.length hdisj]
  simpa only [RecSpecs.rhsCtx, RecSpec.rhsEntry, List.map_map, List.length_map] using hT1

/-! ## Axiom guard

Living check that the spike's conclusions rest only on the standard axioms — in particular
that neither the gate (`T1`) nor the concrete derivations smuggle in `sorryAx`. Should print
`[propext, Classical.choice, Quot.sound]` for every entry. -/

#print axioms T1_retarget_transport
#print axioms T2_monoTyped_to_polyTyped
#print axioms promoteScheme_wf
#print axioms promoteScheme_openVars
#print axioms S2_promoted
#print axioms D1_promoted
#print axioms D2_promoted

end SpikeLetRecPromote
