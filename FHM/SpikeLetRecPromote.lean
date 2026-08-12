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

end SpikeLetRecPromote
