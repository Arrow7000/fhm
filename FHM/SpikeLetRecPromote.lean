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

/-! ### T1' machinery — the forgetting direction

`T1` transports a derivation UP (mono env, `tyArgs = []` → scheme env, `tyArgs = Vs`). The
converse — the `T3'` forgetting map — must go DOWN: the scheme env's `var` rule pins
`tyArgs = Vs` (the term is the retarget), the instantiation is deterministic (`det_same`), so
each use collapses to the shared monotype and the `var` becomes `tyArgs = []`. -/

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
    private `Ty.renameG_isLC` (`Core.lean:5477`), which `T3'` needs for the forgetting map's
    `hmonoLC` hypothesis. -/
theorem Ty.renameG_lc {G Xs : List Nat} {τ : Ty} (hτ : τ.IsLC) : (Ty.renameG G Xs τ).IsLC := by
  unfold Ty.renameG
  exact Ty.substFvars_lc (fun p hp => by
    obtain ⟨x, _, hx⟩ := List.mem_map.mp (List.of_mem_zip hp).2
    rw [← hx]; exact .fvar) hτ

/-- The retargeted image of a branch is a member of the retargeted branch list. -/
theorem retargetBranches_mem_map {n b : Nat} {Vs : List Ty}
    {brs : List (MatchPattern × Expr)} {pat : MatchPattern} {body : Expr}
    (h : (pat, body) ∈ brs) :
    (pat, retargetVars n Vs (b + pat.bindCount) body) ∈ retargetBranches n Vs b brs := by
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
theorem retargetGroup_zip_mem_map {n b : Nat} {Vs : List Ty} :
    ∀ (bs : List Expr) (specs : List RecSpec) (p : Expr × RecSpec),
      p ∈ bs.zip specs →
        ∃ q, q ∈ (retargetGroup n Vs b bs).zip specs ∧ q.1 = retargetVars n Vs b p.1 ∧ q.2 = p.2 := by
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
            exact ⟨(retargetVars n Vs b e, s), List.mem_cons_self .., rfl, rfl⟩
          · rcases ih ss hp with ⟨q, hq, h1, h2⟩
            exact ⟨q, List.mem_cons_of_mem _ hq, h1, h2⟩

/-- **T1' — the forgetting direction.** A `TypeOfElabHM` derivation over a promoted (scheme) env
    prefix, on a term whose group-window `var`s carry `Vs`, degrades to a derivation over the
    same source term with those `var`s carrying `[]`, in the monomorphic env prefix — provided
    each scheme instantiated at `Vs` yields the monotype (`hinst`) and the monotypes are locally
    closed. The exact reverse of `T1_retarget_transport`; this is the `T3'` forgetting map.

    Proof mirrors `T1` case-by-case, with the roles of the env prefixes swapped and an extra
    hypothesis threading the SOURCE term `e₁` (the hypothesis derivation is over the retarget
    of `e₁`), so the `var` case knows the pinned `tyArgs` are `Vs`. -/
theorem retargetUntransport
    {ctors : CtorEnv} {env : Env} {e : Expr} {τ : Ty}
    {monos : List Ty} {Ms : List PolyTy} {Vs : List Ty}
    (hmonoLC : ∀ μ ∈ monos, μ.IsLC)
    (hVsLC : ∀ V ∈ Vs, V.IsLC)
    (hinst : List.Forall₂
      (fun (M : PolyTy) (μ : Ty) => M.paramCount = Vs.length ∧ M.InstantiatesTo Vs μ) Ms monos)
    (h : TypeOfElabHM ⟨Ms ++ env, ctors⟩ (retargetVars Ms.length Vs 0 e) τ) :
    TypeOfElabHM ⟨monos.map PolyTy.mkTrivial ++ env, ctors⟩ (retargetVars Ms.length [] 0 e) τ := by
  have hlen : Ms.length = monos.length := List.Forall₂.length_eq hinst
  have H : ∀ {ctx : Ctx} {e₀ : Expr} {τ₀ : Ty}, TypeOfElabHM ctx e₀ τ₀ →
      ∀ (ep : Env) (e₁ : Expr), ctx.env = ep ++ Ms ++ env →
      e₀ = retargetVars Ms.length Vs ep.length e₁ →
      TypeOfElabHM ⟨ep ++ monos.map PolyTy.mkTrivial ++ env, ctx.ctors⟩
        (retargetVars Ms.length [] ep.length e₁) τ₀ := by
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
            by_cases hwin : ep.length ≤ i ∧ i < ep.length + Ms.length
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
            by_cases hwin : ep.length ≤ i ∧ i < ep.length + Ms.length
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
            by_cases hwin : ep.length ≤ i ∧ i < ep.length + Ms.length
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
            by_cases hwin : ep.length ≤ i ∧ i < ep.length + Ms.length
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
            by_cases hwin : ep.length ≤ i ∧ i < ep.length + Ms.length
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
            by_cases hwin : ep.length ≤ i ∧ i < ep.length + Ms.length
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
            by_cases hwin : ep.length ≤ i ∧ i < ep.length + Ms.length
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
            by_cases hwin : ep.length ≤ i ∧ i < ep.length + Ms.length
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
            by_cases hwin : ep.length ≤ i ∧ i < ep.length + Ms.length
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
            by_cases hwin : ep.length ≤ i ∧ i < ep.length + Ms.length
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
            by_cases hwin : ep.length ≤ i ∧ i < ep.length + Ms.length
            · rw [if_pos hwin] at heq'; cases heq'
            · rw [if_neg hwin] at heq'; cases heq'
        | _ => simp only [retargetVars] at heq'; cases heq'
    | @var dbl polyTy tyArgs ty ctx hlook hlc hinst' =>
        intro ep e₁ heq heq'
        rw [heq] at hlook
        cases e₁ with
        | var dbl' tyArgs₁ =>
            simp only [retargetVars] at heq'
            by_cases hwin : ep.length ≤ dbl' ∧ dbl' < ep.length + Ms.length
            · rw [if_pos hwin] at heq'
              injection heq' with hdbl htyArgs
              subst hdbl
              subst htyArgs
              have hwin_mono : ep.length ≤ dbl ∧ dbl < ep.length + monos.length := by
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
              have hpoly_eq : polyTy = Ms[k] :=
                Option.some.inj (hlook.symm.trans hlook_prom)
              subst hpoly_eq
              have hkMap : k < (monos.map PolyTy.mkTrivial).length := by
                simpa using hk
              have hlook_mono : (ep ++ monos.map PolyTy.mkTrivial ++ env)[dbl]? =
                  some (PolyTy.mkTrivial (monos[k])) := by
                rw [List.append_assoc, List.getElem?_append_right (by omega : ep.length ≤ dbl)]
                rw [hdbl]
                rw [List.getElem?_append_left hkMap]
                rw [List.getElem?_eq_getElem hkMap]
                simp
              have hrel := List.Forall₂.get hinst hkM hk
              have htyEq : ty = monos[k] :=
                InstantiatesBy.det_same (ty := Ms[k].body)
                  (by simpa [PolyTy.InstantiatesTo] using hinst')
                  (by simpa [PolyTy.InstantiatesTo] using hrel.2)
              simp only [retargetVars]
              rw [if_pos hwin]
              refine TypeOfElabHM.var (polyTy := PolyTy.mkTrivial (monos[k])) ?_ ?_ ?_
              · show (ep ++ monos.map PolyTy.mkTrivial ++ env)[dbl]? = some (PolyTy.mkTrivial (monos[k]))
                exact hlook_mono
              · show Ty.AreLC (PolyTy.mkTrivial (monos[k])).paramCount []
                simp [Ty.AreLC, PolyTy.mkTrivial]
              · show (PolyTy.mkTrivial (monos[k])).InstantiatesTo [] ty
                rw [htyEq]
                show InstantiatesBy [] (monos[k]) (monos[k])
                exact InstantiatesBy.refl_of_closed (hmonoLC (monos[k]) (List.getElem_mem hk))
            · rw [if_neg hwin] at heq'
              injection heq' with hdbl htyArgs
              subst hdbl
              subst htyArgs
              have hnotwin : ¬ (ep.length ≤ dbl ∧ dbl < ep.length + monos.length) := by
                intro h
                rcases h with ⟨h1, h2⟩
                exact hwin ⟨h1, by simpa [hlen] using h2⟩
              by_cases hlt : dbl < ep.length
              · simp only [retargetVars]
                rw [if_neg hwin]
                refine TypeOfElabHM.var ?_ hlc hinst'
                show (ep ++ monos.map PolyTy.mkTrivial ++ env)[dbl]? = some polyTy
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
                show (ep ++ monos.map PolyTy.mkTrivial ++ env)[dbl]? = some polyTy
                rw [List.append_assoc, List.getElem?_append_right hle]
                rw [List.append_assoc, List.getElem?_append_right hle] at hlook
                have hdM : Ms.length ≤ dbl - ep.length := by omega
                have hdm : monos.length ≤ dbl - ep.length := by omega
                have hdm' : (monos.map PolyTy.mkTrivial).length ≤ dbl - ep.length := by
                  simpa [List.length_map] using hdm
                rw [List.getElem?_append_right hdm']
                rw [show (dbl - ep.length) - (monos.map PolyTy.mkTrivial).length
                    = (dbl - ep.length) - monos.length from by simp]
                rw [List.getElem?_append_right hdM] at hlook
                have hidx : (dbl - ep.length) - Ms.length = (dbl - ep.length) - monos.length := by
                  rw [hlen]
                rw [hidx] at hlook
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
            by_cases hwin : ep.length ≤ i ∧ i < ep.length + Ms.length
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
            have hmemVs : (pat, retargetVars Ms.length Vs (ep.length + pat.bindCount) body) ∈ branches := by
              rw [heqbr]
              exact retargetBranches_mem_map (n := Ms.length) (b := ep.length) (Vs := Vs) hmemb
            rcases ihbrs (pat, retargetVars Ms.length Vs (ep.length + pat.bindCount) body) hmemVs with
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
              have hw : TypeOfElabHM ⟨ep ++ monos.map PolyTy.mkTrivial ++ env, ctx.ctors⟩
                  (retargetVars Ms.length [] (ep.length + (MatchPattern.wildcard).bindCount) body) resultTy := by
                simpa [MatchPattern.bindCount] using ihbody ep body heq
                  (by simp [MatchPattern.bindCount])
              exact TypeOfElabMatchBranch.wildcard hw
        | var i tyArgs₁ =>
            simp only [retargetVars] at heq'
            by_cases hwin : ep.length ≤ i ∧ i < ep.length + Ms.length
            · rw [if_pos hwin] at heq'; cases heq'
            · rw [if_neg hwin] at heq'; cases heq'
        | _ => simp only [retargetVars] at heq'; cases heq'
    | @letRec ctx bodyCtx anns bindings specs G L body ρ hwf hmono hpoly heqctx hbody ihmono ihpoly ihbody =>
        intro ep e₁ heq heq'
        subst heqctx
        cases e₁ with
        | letRec anns' bindings' body' =>
            simp only [retargetVars] at heq'
            injection heq' with hanns hbindings hbody
            subst hanns
            have hlenb : bindings'.length = specs.length := by
              calc
                bindings'.length = (retargetGroup Ms.length Vs (ep.length + bindings'.length) bindings').length :=
                  (retargetGroup_length (n := Ms.length) (Vs := Vs) (b := ep.length + bindings'.length) bindings').symm
                _ = bindings.length := (congrArg List.length hbindings).symm
                _ = specs.length := hwf.length
            refine TypeOfElabHM.letRec (specs := specs) (G := G) (L := L) ?_ ?_ ?_ rfl ?_
            · exact ⟨hwf.anns_eq, by
                rw [retargetGroup_length (n := Ms.length) (Vs := ([] : List Ty))
                  (b := ep.length + bindings'.length) bindings']
                exact hlenb, hwf.nodup, hwf.mono_lc, hwf.poly_wf⟩
            · intro Xs hf p hp τ hτ
              rcases retargetGroup_zip_mem (Vs := []) (b := ep.length + bindings'.length)
                  bindings' specs p hp with ⟨q, hq, hp1, hp2⟩
              rw [hp2] at hτ
              rcases retargetGroup_zip_mem_map (n := Ms.length) (Vs := Vs)
                  (b := ep.length + bindings'.length) bindings' specs q hq with ⟨p', hp', hp1', hp2'⟩
              rw [← hbindings] at hp'
              rw [← hp2'] at hτ
              have hc := ihmono Xs hf p' hp' τ hτ
              have hcc := hc (specs.map (RecSpec.rhsEntry G Xs) ++ ep) q.1
                (by simp only [RecSpecs.rhsCtx, heq, List.append_assoc])
                (by
                  rw [hp1']
                  rw [hlenb]
                  simp [List.length_append, List.length_map, Nat.add_comm])
              rw [hp1]
              simpa only [RecSpecs.rhsCtx, List.append_assoc, List.length_append, List.length_map,
                hlenb, Nat.add_comm] using hcc
            · intro Xs hf p hp σ hσ Ys hfY
              rcases retargetGroup_zip_mem (Vs := []) (b := ep.length + bindings'.length)
                  bindings' specs p hp with ⟨q, hq, hp1, hp2⟩
              rw [hp2] at hσ
              rcases retargetGroup_zip_mem_map (n := Ms.length) (Vs := Vs)
                  (b := ep.length + bindings'.length) bindings' specs q hq with ⟨p', hp', hp1', hp2'⟩
              rw [← hbindings] at hp'
              rw [← hp2'] at hσ
              have hc := ihpoly Xs hf p' hp' σ hσ Ys hfY
              have hcc := hc (specs.map (RecSpec.rhsEntry G Xs) ++ ep) (q.1.openTyVars Ys)
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
            · have hb := ihbody (specs.map (RecSpec.bodyScheme G) ++ ep) body'
                (by simp only [RecSpecs.bodyCtx, heq, List.append_assoc])
                (by
                  rw [hbody]
                  rw [hlenb]
                  simp [List.length_append, List.length_map, Nat.add_comm])
              simpa only [RecSpecs.bodyCtx, List.append_assoc, List.length_append, List.length_map,
                hlenb, Nat.add_comm] using hb
        | var i tyArgs₁ =>
            simp only [retargetVars] at heq'
            by_cases hwin : ep.length ≤ i ∧ i < ep.length + Ms.length
            · rw [if_pos hwin] at heq'; cases heq'
            · rw [if_neg hwin] at heq'; cases heq'
        | _ => simp only [retargetVars] at heq'; cases heq'
  exact H h [] e (by simp) (by rfl)

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

/-! ## T3 — the CONVERSE, and whether the §2.2 payoff is real

`T2` promotes mono → poly. The headline reason to do this refactor is §2.2 of the brief: with
elaboration shape-preserving, `Infer.sourceSound` should stop being a second 656-line induction
and become a corollary of `Infer.sound` via a decoration-forgetting faithfulness lemma
`Decorates e e' → TypeOfElabHM ctx e' τ → TypeOfHM ctx e τ`.

**That lemma needs the CONVERSE of `T2` at `letRec`, and the converse looks false.** The source
node keeps `anns = none` for unannotated members, and `RecSpecs.WF.anns_eq` forces those specs
to be `.mono` — so a source derivation *must* use `MonoTyped`, where every sibling use sits at
one shared monotype. An arbitrary elaborated derivation of the promoted (all-`poly`) node may
instantiate a sibling at *different* types in different places, which `MonoTyped` cannot
express. Promotion is sound because we *construct* the poly derivation from a mono one; nothing
constrains an arbitrary one.

If that is right, the §2.2 payoff needs qualifying: `sourceSound` would still need
`Infer`-specific information at `letRec` rather than falling out of a pure term relation. It
may still be much cheaper than today (same tree shape), but "it becomes a corollary" would be
too strong.

`T3` states the converse directly. **A failure here is the expected and useful outcome** — the
asymmetry between `T2` (proved) and `T3` is itself the finding. Do not contort to force it. -/

/-- **T3 — expected to FAIL.** The converse of `T2`: does an arbitrary `PolyTyped` derivation
    at the promoted schemes yield the `MonoTyped` derivation the *source* node requires?

    If this is false, report the obstruction precisely: the case, the goal, and whether the
    blocker is what §T3's docstring predicts (a sibling instantiated at two different types,
    inexpressible in `MonoTyped`). A concrete counterexample would be ideal but the obstruction
    alone is enough. -/
theorem T3_polyTyped_to_monoTyped
    {ctx : Ctx} {bindings bindings' : List Expr} {monos : List Ty} {G L : List Nat}
    (hGnodup : G.Nodup)
    (hmonoLC : ∀ μ ∈ monos, μ.IsLC)
    (hlen : bindings.length = monos.length)
    (hpoly : RecSpecs.PolyTyped TypeOfElabHM ctx bindings'
      (monos.map (fun μ => RecSpec.poly (promoteScheme G μ))) [] (L ++ G))
    (hopen : ∀ Ys, FreshNames (L ++ G) G.length Ys →
      ∀ p ∈ bindings.zip bindings',
        p.2.openTyVars Ys
          = retargetVars monos.length (Ys.map Ty.fvar) 0 p.1) :
    RecSpecs.MonoTyped TypeOfElabHM ctx bindings (monos.map RecSpec.mono) G (L ++ G) := by
  sorry

/-! ## T3' — the converse, with the hypotheses `T3` was missing

The `T3` probe found `T3` false, but for two **statement bugs of mine**, not for the predicted
reason:

- **(A)** nothing related `bindings'.length` to `bindings.length`, so `hpoly` could not even be
  indexed at member `k`;
- **(B)** `retargetVars` *overwrites* `tyArgs`, so `hopen` left the **source**'s group-use
  `tyArgs` unconstrained — a source binding carrying `.var 1 [int]` maps to the same retargeted
  term as one carrying `.var 1 []`, but only the latter can be `MonoTyped` (arity 0).

More importantly it refuted the predicted obstruction. I argued an arbitrary poly derivation
could instantiate a sibling at different types at different sites, which `MonoTyped` cannot
express. **It cannot** — `TypeOfElabHM` reads `tyArgs` from the *term*, `hopen` pins the term
to be the retarget, and `retargetVars` assigns *every* in-window use the *same* `Vs`. So the
term itself forces one shared instance per sibling, which is exactly what `MonoTyped` says.
Type-passing — the feature that causes so much of the complexity elsewhere — is what rescues
this.

`T3'` restores both hypotheses. **If it holds, the §2.2 payoff is real** and `Infer.sourceSound`
can become a corollary via a decoration-forgetting lemma, provided that lemma's `Decorates`
relation is *tight* at `letRec` (uniform `tyArgs` on group-member uses — which is what `Infer`
produces). (B) is expressed with the existing machinery: retargeting to `[]` is the identity
exactly when every in-window use already carries `[]`. -/

theorem T3'_polyTyped_to_monoTyped
    {ctx : Ctx} {bindings bindings' : List Expr} {monos : List Ty} {G L : List Nat}
    (hGnodup : G.Nodup)
    (hmonoLC : ∀ μ ∈ monos, μ.IsLC)
    (hlen : bindings.length = monos.length)
    (hlen' : bindings'.length = bindings.length)
    (hsrcNil : ∀ e ∈ bindings, retargetVars monos.length [] 0 e = e)
    (hpoly : RecSpecs.PolyTyped TypeOfElabHM ctx bindings'
      (monos.map (fun μ => RecSpec.poly (promoteScheme G μ))) [] (L ++ G))
    (hopen : ∀ Ys, FreshNames (L ++ G) G.length Ys →
      ∀ p ∈ bindings.zip bindings',
        p.2.openTyVars Ys
          = retargetVars monos.length (Ys.map Ty.fvar) 0 p.1) :
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
      = retargetVars monos.length (Xs.map Ty.fvar) 0 (bindings[k]) :=
    hopen Xs hfXs (bindings[k], bindings'[k]) hpair
  have hpolyD' : TypeOfElabHM ⟨monos.map (promoteScheme G ·) ++ ctx.env, ctx.ctors⟩
      (retargetVars monos.length (Xs.map Ty.fvar) 0 (bindings[k])) (Ty.renameG G Xs (monos[k])) := by
    simpa only [RecSpecs.rhsCtx, RecSpec.rhsEntry, List.map_map, hopenD,
      promoteScheme_openVars (hmonoLC (monos[k]) hmemMonos) hGnodup hfXs.length hdisj] using hpolyD
  have hinst_list : List.Forall₂
      (fun (M : PolyTy) (μ : Ty) =>
        M.paramCount = (Xs.map Ty.fvar).length ∧ M.InstantiatesTo (Xs.map Ty.fvar) μ)
      (monos.map (promoteScheme G ·)) (monos.map (Ty.renameG G Xs ·)) := by
    apply Forall₂_map_of_forall
    intro μ hμ
    exact promoteScheme_instantiatesTo (hmonoLC μ hμ) hGnodup hfXs.length hdisj
  have hVsLC : ∀ V ∈ Xs.map Ty.fvar, V.IsLC := by
    intro V hV
    rcases List.mem_map.mp hV with ⟨x, _, rfl⟩
    exact .fvar
  have hmonoLC' : ∀ μ ∈ monos.map (Ty.renameG G Xs ·), μ.IsLC := by
    intro μ hμ
    rcases List.mem_map.mp hμ with ⟨μ₀, hμ₀, rfl⟩
    exact Ty.renameG_lc (hmonoLC μ₀ hμ₀)
  have hT1' := retargetUntransport (Ms := monos.map (promoteScheme G ·))
    (monos := monos.map (Ty.renameG G Xs ·)) (Vs := Xs.map Ty.fvar) (env := ctx.env)
    (ctors := ctx.ctors) (e := bindings[k]) (τ := Ty.renameG G Xs (monos[k]))
    hmonoLC' hVsLC hinst_list (by simpa [List.length_map] using hpolyD')
  have hsrc : retargetVars monos.length [] 0 (bindings[k]) = bindings[k] :=
    hsrcNil (bindings[k]) (List.getElem_mem hkBind)
  rw [hp1]
  simpa only [RecSpecs.rhsCtx, RecSpec.rhsEntry, List.map_map, List.length_map, hsrc] using hT1'

/-! ## PRES — preservation for the promoted node costs nothing

The promotion changes neither `Expr`, nor `SmallStep.Step`, nor `TypeOfElabHM`. A promoted
`letRec` is an ordinary well-typed term of the existing language, so the *already-proved*
`TypeOfElabHM.preservation` (`Core.lean:9442`) applies to it directly — no new metatheory.

This was listed as an open risk in `briefs/complexity-budget.md` §3.6 three times. It is not a
risk; it is a corollary. This theorem exists to make that concrete rather than asserted. -/

open SmallStep (Step) in

theorem PRES_D1_promoted {e' : Expr}
    (hstep : Step
      (.letRec [some σA, some σA]
        [.lambda none (.app (.var 2 [.bvar 0, .bvar 1]) (.var 0 [])),
         .lambda none (.app (.var 1 [.bvar 0, .bvar 1]) (.var 0 []))]
        (.var 0 [.prim .int, .prim .int])) e') :
    TypeOfElabHM ⟨[], []⟩ e' (.arrow (.prim .int) (.prim .int)) :=
  TypeOfElabHM.preservation hstep D1_promoted

/-! ## STORED — the stored-form retarget, and the last missing link

`retargetVars` works on *opened* terms (`Vs` concrete, depth-independent). The real elaborator
must emit the **stored** form, with `Ty.bvarRangeFrom d |G|` at type-binder depth `d`. The
commute below is exactly what discharges `T2`/`T3'`'s `hopen` hypothesis, after which the
transport chain is closed end to end.

This is the "200–400 line depth-tracking traversal" §3.4 estimated. Its actual size is the
best available proxy for whether the remaining refactor is mechanical or a slog — so if you
prove it, **report the line count**. -/

mutual

def retargetStored (n gLen : Nat) (d b : Nat) : Expr → Expr
  | .primLit p          => .primLit p
  | .primBinOp op       => .primBinOp op
  | .lambda ann body    => .lambda ann (retargetStored n gLen d (b + 1) body)
  | .app f arg          => .app (retargetStored n gLen d b f) (retargetStored n gLen d b arg)
  | .letIn (some σ) rhs body =>
      .letIn (some σ) (retargetStored n gLen (d + σ.paramCount) b rhs)
        (retargetStored n gLen d (b + 1) body)
  | .letIn none rhs body =>
      .letIn none (retargetStored n gLen d b rhs) (retargetStored n gLen d (b + 1) body)
  | .var i tyArgs       =>
      if b ≤ i ∧ i < b + n then .var i (Ty.bvarRangeFrom d gLen) else .var i tyArgs
  | .ctor c             => .ctor c
  | .match_ scrut brs   =>
      .match_ (retargetStored n gLen d b scrut) (retargetStoredBranches n gLen d b brs)
  | .letRec anns bs body =>
      .letRec anns (retargetStoredGroup n gLen d (b + bs.length) anns bs)
        (retargetStored n gLen d (b + bs.length) body)

def retargetStoredBranches (n gLen : Nat) (d b : Nat) :
    List (MatchPattern × Expr) → List (MatchPattern × Expr)
  | []                  => []
  | (pat, body) :: rest =>
      (pat, retargetStored n gLen d (b + pat.bindCount) body)
        :: retargetStoredBranches n gLen d b rest

/-- The stored-form retarget of a recursion group's bindings, each binding descended at
    `d + RecAnn.params aⱼ` (shielding its own scheme's variables when annotated), the `anns`
    consumed in lockstep — mirroring `RecGroup.openTyVarsAux`. This is the stored-form analogue
    of `retargetGroup`.

    NOTE: the annotations must shield, so that the pool `bvar`s placed at type-depth `d` inside
    an ANNOTATED binding are opened at `d + σ.paramCount` (where the enclosing scope's vars sit
    per `Expr.openTyVarsAux`), exactly as `letIn (some σ)` shields its rhs. Without the shield
    `retargetStored_openTyVars` fails: the pool `bvar`s stay unopened. -/
def retargetStoredGroup (n gLen d b : Nat) :
    List (Option PolyTy) → List Expr → List Expr
  | _,       []        => []
  | [],      e :: rest => retargetStored n gLen d b e :: retargetStoredGroup n gLen d b [] rest
  | a :: as, e :: rest => retargetStored n gLen (d + RecAnn.params a) b e
      :: retargetStoredGroup n gLen d b as rest

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
theorem retargetStored_openTyVarsAux {n gLen d b : Nat} {Ys : List Nat} {e : Expr}
    (hYsLen : Ys.length = gLen) :
    (retargetStored n gLen d b e).openTyVarsAux d Ys
      = retargetVars n (Ys.map Ty.fvar) b (e.openTyVarsAux d Ys) := by
  induction e using Expr.rec_strong generalizing b d with
  | primLit p => rfl
  | primBinOp op => rfl
  | ctor nm => rfl
  | var i tyArgs =>
      by_cases hwin : b ≤ i ∧ i < b + n
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
      have hbrs : BranchList.openTyVarsAux d Ys (retargetStoredBranches n gLen d b brs)
          = retargetBranches n (Ys.map Ty.fvar) b (BranchList.openTyVarsAux d Ys brs) := by
        induction brs with
        | nil => rfl
        | cons br rest ih =>
            cases br with
            | mk pat body =>
                have hhead : (retargetStored n gLen d (b + pat.bindCount) body).openTyVarsAux d Ys
                    = retargetVars n (Ys.map Ty.fvar) (b + pat.bindCount)
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
          RecGroup.openTyVarsAux d Ys anns' (retargetStoredGroup n gLen d D anns' bs)
            = retargetGroup n (Ys.map Ty.fvar) D (RecGroup.openTyVarsAux d Ys anns' bs) := by
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

/-- **STORED — the last missing link.** Opening the stored-form retarget at `Ys` gives the
    opened-form retarget at `Ys`-as-fvars. Discharges `hopen`. -/
theorem retargetStored_openTyVars {n gLen b : Nat} {Ys : List Nat} {e : Expr}
    (hYsLen : Ys.length = gLen) :
    (retargetStored n gLen 0 b e).openTyVars Ys
      = retargetVars n (Ys.map Ty.fvar) b (e.openTyVars Ys) := by
  simpa only [Expr.openTyVars] using retargetStored_openTyVarsAux (d := 0) (hYsLen := hYsLen) (e := e)

/-! ## Axiom guard

Living check that the spike's conclusions rest only on the standard axioms — in particular
that neither the gate (`T1`) nor the concrete derivations smuggle in `sorryAx`. Should print
`[propext, Classical.choice, Quot.sound]` for every entry. -/

#print axioms T1_retarget_transport
#print axioms T2_monoTyped_to_polyTyped
#print axioms T3'_polyTyped_to_monoTyped
#print axioms retargetStored_openTyVars
#print axioms PRES_D1_promoted
#print axioms promoteScheme_wf
#print axioms promoteScheme_openVars
#print axioms S2_promoted
#print axioms D1_promoted
#print axioms D2_promoted

end SpikeLetRecPromote
