import FHM.InferW

/-! # SPIKE: mixed annotated/unannotated mutual recursion (`letRecMixed`)

Standalone validation of the **fused** declarative rule for a mutual-recursion
group in which SOME bindings carry scheme annotations (checked at their declared
schemes, polymorphic recursion allowed — the `letRecAnn` regime) and the others
are unannotated (typed at shared monotypes linked through a common gen-var pool,
generalised only for the body — the `letRec` regime). This is roadmap step 4
("the hard one") of `briefs/next-agent-brief-primitives-typedecls-surface.md`.

The crux being validated: the two shipped rules use structurally different
cofinite regimes — `letRec` opens ONE shared `Xs` for the whole pool `G`,
`letRecAnn` opens EACH binding at its own `Ys` — and a mixed block needs both
**nested**: the per-binding annotated openings `Ys` live *inside* the shared-pool
quantifier `Xs`, because every binding's checking env simultaneously contains
annotated members at their full schemes `σⱼ` and unannotated members at their
opened shared monotypes `τₖ[G↦Xs]`.

We state the fused rule as a derived predicate `MixedRule` over the existing
typing relations (parameterised, so it instantiates to both `TypeOfElabHM` and
the decoration-blind source spec `TypeOfHM`), then:

1. prove the **degeneracy** directions: all-`none` coincides with Core's
   `letRec` rule and all-`some` with Core's `letRecAnn` rule (both directions) —
   the representation claim that the two shipped rules are boundary cases;
2. prove a genuinely **mixed positive witness** (cross-boundary mutual calls in
   both directions, polymorphic recursion in the annotated member, and an
   unannotated member that instantiates the annotated sibling *at a pool
   variable* and is then generalised for the body);
3. prove the **skolem-leak negative witness**: an annotated member that forces
   an unannotated sibling's shared monotype to mention its own skolem is
   REJECTED — the quantifier nesting (`τs` fixed outside `Ys`) makes the rule
   underivable, machine-checked by instantiating the cofinite premise at two
   distinct fresh skolems;
4. sanity-check `weaken_env` / `typ_subst` tractability for the nested-quantifier
   rule (the two historically dangerous lemmas).

No edits to `Core`/`InferW`. -/

namespace SpikeLetRecMixed

/-! ## Local copies of Core-private list/type helpers -/

/-- Local copy of Core's private `List.mem_zip_map_left`. -/
private theorem mem_zip_map_left {α β γ : Type _} {f : α → γ} :
    ∀ {l : List α} {r : List β} {p : γ × β},
      p ∈ (l.map f).zip r → ∃ a b, a ∈ l ∧ (a, b) ∈ l.zip r ∧ p = (f a, b) := by
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
      | inl heq => exact ⟨hd, rhd, List.mem_cons_self, List.mem_cons_self, heq⟩
      | inr h' =>
        obtain ⟨a, b, ha, hmem, heq⟩ := ih h'
        exact ⟨a, b, List.mem_cons_of_mem _ ha, List.mem_cons_of_mem _ hmem, heq⟩

/-- Mirror of `mem_zip_map_left` for a map on the RIGHT list (∃-form). -/
private theorem mem_zip_map_right' {α β γ : Type _} {g : β → γ} :
    ∀ {l : List α} {r : List β} {p : α × γ},
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

/-- Local copy of Core's private `List.mem_zip_map` (both lists mapped). -/
private theorem mem_zip_map {α β γ δ : Type _} {f : α → γ} {g : β → δ} :
    ∀ {l : List α} {r : List β} {p : γ × δ},
      p ∈ (l.map f).zip (r.map g) → ∃ a b, (a, b) ∈ l.zip r ∧ p = (f a, g b) := by
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

/-- Local copy of Core's private `List.mem_zip_map_right` (constructive form). -/
private theorem mem_zip_map_right {α β γ : Type _} {g : β → γ}
    {l : List α} {r : List β} {a : α} {b : β}
    (h : (a, b) ∈ l.zip r) : (a, g b) ∈ l.zip (r.map g) := by
  induction l generalizing r with
  | nil => simp at h
  | cons hd tl ih =>
    cases r with
    | nil => simp at h
    | cons rhd rtl =>
      simp only [List.zip_cons_cons, List.mem_cons, Prod.mk.injEq] at h
      simp only [List.map_cons, List.zip_cons_cons, List.mem_cons, Prod.mk.injEq]
      cases h with
      | inl heq => exact Or.inl ⟨heq.1, heq.2 ▸ rfl⟩
      | inr h' => exact Or.inr (ih h')

/-- Members of a self-zip are diagonal. -/
private theorem mem_zip_self_eq {α : Type _} : ∀ {l : List α} {p : α × α},
    p ∈ l.zip l → p.1 = p.2 := by
  intro l
  induction l with
  | nil => intro p h; simp at h
  | cons hd tl ih =>
    intro p h
    simp only [List.zip_cons_cons, List.mem_cons] at h
    cases h with
    | inl heq => rw [heq]
    | inr h' => exact ih h'

/-- Pointwise agreement along a zip pins the right list to a map of the left. -/
private theorem zip_pointwise_eq_map {α β : Type _} {f : α → β} :
    ∀ {l : List α} {r : List β}, l.length = r.length →
      (∀ p ∈ l.zip r, p.2 = f p.1) → r = l.map f := by
  intro l
  induction l with
  | nil => intro r hlen _; cases r with
    | nil => rfl
    | cons _ _ => simp at hlen
  | cons hd tl ih =>
    intro r hlen hpt
    cases r with
    | nil => simp at hlen
    | cons rhd rtl =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
      simp only [List.map_cons, List.cons.injEq]
      exact ⟨(hpt (hd, rhd) (by simp [List.zip_cons_cons])).symm ▸ rfl,
        ih hlen (fun p hp => hpt p (by simp only [List.zip_cons_cons, List.mem_cons]; exact Or.inr hp))⟩

/-- Local copy of Core's private `Ty.IsLC.substFvars`. -/
private theorem isLC_substFvars {s : List (Nat × Ty)} {τ : Ty}
    (hs : ∀ p ∈ s, p.2.IsLC) (hτ : τ.IsLC) : (Ty.substFvars s τ).IsLC := by
  induction s generalizing τ with
  | nil => exact hτ
  | cons hd tl ih =>
    obtain ⟨Z, U⟩ := hd
    exact ih (fun p hp => hs p (List.mem_cons_of_mem _ hp))
      (Ty.IsLC.substFvar (hs (Z, U) List.mem_cons_self) hτ)

/-- Local copy of Core's private `Ty.renameG_isLC`. -/
private theorem renameG_isLC {G Xs : List Nat} {τ : Ty}
    (hτ : τ.IsLC) : (Ty.renameG G Xs τ).IsLC := by
  unfold Ty.renameG
  refine isLC_substFvars ?_ hτ
  intro p hp
  obtain ⟨x, _, hx⟩ := List.mem_map.mp (List.of_mem_zip hp).2
  rw [← hx]; exact .fvar


/-! ## The per-binding spec

A `RecSpec` is the derivation-internal datum for one group member: unannotated
members carry their shared monotype `τ` (a rule-internal existential, like
`letRec`'s `τs`), annotated members carry their declared scheme `σ` (pinned to
the stored annotation). The would-be Core node stores only `RecSpec.ann`. -/

inductive RecSpec
  | mono (τ : Ty)
  | poly (σ : PolyTy)

/-- What the node would store: `none` for unannotated, the scheme for annotated. -/
def RecSpec.ann : RecSpec → Option PolyTy
  | .mono _ => none
  | .poly σ => some σ

/-- The env entry member `j` presents while the group's RHSs are checked, inside
    the shared opening `G ↦ Xs`: unannotated members at their opened shared
    monotypes (the `letRec` regime), annotated members at their FULL schemes
    (the `letRecAnn` regime — this is what enables polymorphic recursion and
    cross-boundary polymorphic use). -/
def RecSpec.rhsEntry (G Xs : List Nat) : RecSpec → PolyTy
  | .mono τ => PolyTy.mkTrivial (Ty.renameG G Xs τ)
  | .poly σ => σ

/-- The env entry member `j` presents to the BODY: unannotated members
    generalised over the shared pool `G` (per-binding, `∀ (G ∩ ftv τ). τ`),
    annotated members at their declared schemes. -/
def RecSpec.bodyScheme (G : List Nat) : RecSpec → PolyTy
  | .mono τ => PolyTy.genGroup G τ
  | .poly σ => σ

theorem RecSpec.ann_eq_none {s : RecSpec} (h : s.ann = none) : ∃ τ, s = .mono τ := by
  cases s with
  | mono τ => exact ⟨τ, rfl⟩
  | poly σ => simp [RecSpec.ann] at h

theorem RecSpec.ann_eq_some {s : RecSpec} {σ : PolyTy} (h : s.ann = some σ) : s = .poly σ := by
  cases s with
  | mono τ => simp [RecSpec.ann] at h
  | poly σ' => simpa [RecSpec.ann] using h


/-! ## The fused rule

Rule shape (would-be `TypeOfElabHM.letRecMixed` constructor over a node
`letRecMixed (anns : List (Option PolyTy)) (bindings) (body)`; `specs`/`G`/`L`
are constructor-implicit like `letRec`'s `{τs Ms G L}`):

- ONE shared cofinite opening `∀ Xs, FreshNames L G.length Xs` for the whole
  pool (the `letRec` linking discipline — the same `Xs` for every unannotated
  member keeps mutual monotype-sharing intact);
- NESTED inside it, per annotated member, its own cofinite skolemisation
  `∀ Ys, FreshNames (L ++ Xs) σ.paramCount Ys` (the `letRecAnn` discipline;
  `Ys` additionally dodges the pool skolems `Xs`);
- every RHS is checked in the SAME env `specs.map (rhsEntry G Xs)`: annotated
  members visible at full schemes, unannotated at opened monotypes. Annotated
  RHSs are opened scheme-relatively (`openTyVars Ys`), unannotated RHSs are
  typed as stored;
- the body sees `specs.map (bodyScheme G)`: generalisations for the unannotated,
  declared schemes for the annotated.

Note the quantifier order is load-bearing: the shared monotypes `τ` (inside
`specs`) are fixed BEFORE any `Ys` is chosen, so an unannotated member's
monotype can never mention an annotated sibling's skolem — see the negative
witness below. -/
def MixedRule (TypeOf : Ctx → Expr → Ty → Prop) (ctx : Ctx)
    (anns : List (Option PolyTy)) (bindings : List Expr) (body : Expr) (ρ : Ty) : Prop :=
  ∃ (specs : List RecSpec) (G L : List Nat),
    specs.map RecSpec.ann = anns ∧
    bindings.length = specs.length ∧
    G.Nodup ∧
    (∀ τ, RecSpec.mono τ ∈ specs → τ.IsLC) ∧
    (∀ σ, RecSpec.poly σ ∈ specs → σ.WF) ∧
    (∀ Xs, FreshNames L G.length Xs →
      ∀ p ∈ bindings.zip specs,
        (∀ τ, p.2 = .mono τ →
          TypeOf { ctx with env := specs.map (RecSpec.rhsEntry G Xs) ++ ctx.env }
            p.1 (Ty.renameG G Xs τ)) ∧
        (∀ σ, p.2 = .poly σ →
          ∀ Ys, FreshNames (L ++ Xs) σ.paramCount Ys →
            TypeOf { ctx with env := specs.map (RecSpec.rhsEntry G Xs) ++ ctx.env }
              (p.1.openTyVars Ys) (σ.openVars Ys))) ∧
    TypeOf { ctx with env := specs.map (RecSpec.bodyScheme G) ++ ctx.env } body ρ


/-! ## Degeneracy: the two shipped rules are the boundary cases

All-`none` coincides with `TypeOfElabHM.letRec` and all-`some` with
`TypeOfElabHM.letRecAnn`, in BOTH directions. This validates the agreed
representation (one node with per-binding `Option PolyTy`; `letRec`/`letRecAnn`
as degenerate cases whose proofs transfer). -/

/-- An all-`none` spec list is a `.mono` list. -/
private theorem specs_all_mono {specs : List RecSpec} {n : Nat}
    (h : specs.map RecSpec.ann = List.replicate n none) :
    ∃ τs : List Ty, specs = τs.map RecSpec.mono := by
  induction specs generalizing n with
  | nil => exact ⟨[], rfl⟩
  | cons s tl ih =>
    cases n with
    | zero => simp at h
    | succ m =>
      simp only [List.map_cons, List.replicate_succ, List.cons.injEq] at h
      obtain ⟨h1, h2⟩ := h
      obtain ⟨τ, rfl⟩ := RecSpec.ann_eq_none h1
      obtain ⟨τs, rfl⟩ := ih h2
      exact ⟨τ :: τs, rfl⟩

/-- An all-`some` spec list is the `.poly` image of its schemes. -/
private theorem specs_all_poly : ∀ {specs : List RecSpec} {schemes : List PolyTy},
    specs.map RecSpec.ann = schemes.map Option.some →
    specs = schemes.map RecSpec.poly := by
  intro specs
  induction specs with
  | nil =>
    intro schemes h
    cases schemes with
    | nil => rfl
    | cons _ _ => simp at h
  | cons s tl ih =>
    intro schemes h
    cases schemes with
    | nil => simp at h
    | cons σ stl =>
      simp only [List.map_cons, List.cons.injEq] at h
      obtain ⟨h1, h2⟩ := h
      rw [RecSpec.ann_eq_some h1, ih h2, List.map_cons]

/-- All-mono specs present exactly `letRec`'s monomorphic RHS environment. -/
private theorem map_mono_rhsEntry (G Xs : List Nat) (τs : List Ty) :
    (τs.map RecSpec.mono).map (RecSpec.rhsEntry G Xs)
      = (τs.map (Ty.renameG G Xs)).map PolyTy.mkTrivial := by
  simp only [List.map_map]
  rfl

/-- All-mono specs present exactly `letRec`'s generalised body environment. -/
private theorem map_mono_bodyScheme (G : List Nat) (τs : List Ty) :
    (τs.map RecSpec.mono).map (RecSpec.bodyScheme G) = τs.map (PolyTy.genGroup G) := by
  simp only [List.map_map]
  rfl

/-- All-poly specs present exactly `letRecAnn`'s full-scheme RHS environment
    (for ANY pool `G`/opening `Xs` — annotated entries ignore the pool). -/
private theorem map_poly_rhsEntry (G Xs : List Nat) (schemes : List PolyTy) :
    (schemes.map RecSpec.poly).map (RecSpec.rhsEntry G Xs) = schemes := by
  simp only [List.map_map]
  exact List.map_id'' (fun _ => rfl) schemes

/-- All-poly specs present exactly `letRecAnn`'s body environment. -/
private theorem map_poly_bodyScheme (G : List Nat) (schemes : List PolyTy) :
    (schemes.map RecSpec.poly).map (RecSpec.bodyScheme G) = schemes := by
  simp only [List.map_map]
  exact List.map_id'' (fun _ => rfl) schemes

/-- **`letRec` embeds** (all-`none` direction 1): a Core `letRec` derivation is a
    `MixedRule` derivation with every binding unannotated. -/
theorem MixedRule.of_letRec {ctx : Ctx} {bindings : List Expr} {body : Expr} {ρ : Ty}
    (h : TypeOfElabHM ctx (.letRec bindings body) ρ) :
    MixedRule TypeOfElabHM ctx (List.replicate bindings.length none) bindings body ρ := by
  cases h with
  | letRec hlen hlen2 hlc hG hgen hcofin heq hbody =>
    subst heq
    expose_names
    refine ⟨τs.map RecSpec.mono, G, L, ?_, by simpa using hlen, hG, ?_, ?_, ?_, ?_⟩
    · rw [List.map_map]
      show τs.map (fun _ => none) = _
      rw [List.map_const', hlen]
    · intro τ hτ
      simp only [List.mem_map, RecSpec.mono.injEq] at hτ
      obtain ⟨τ', hτ', rfl⟩ := hτ
      exact hlc τ' hτ'
    · intro σ hσ
      simp at hσ
    · intro Xs hfresh p hp
      obtain ⟨e, s, hes, heq2⟩ := mem_zip_map_right' hp
      subst heq2
      refine ⟨?_, ?_⟩
      · intro τ hτ
        injection hτ with hττ
        rw [← hττ]
        have hmem := mem_zip_map_right (g := Ty.renameG G Xs) hes
        have hty := hcofin Xs hfresh (e, Ty.renameG G Xs s) hmem
        rwa [← map_mono_rhsEntry G Xs τs] at hty
      · intro σ hσ
        exact RecSpec.noConfusion hσ
    · rw [map_mono_bodyScheme, ← zip_pointwise_eq_map hlen2 hgen]
      exact hbody

/-- **`letRec` projects** (all-`none` direction 2): a `MixedRule` derivation with
    every binding unannotated yields a Core `letRec` derivation. -/
theorem MixedRule.to_letRec {ctx : Ctx} {bindings : List Expr} {body : Expr} {ρ : Ty}
    (h : MixedRule TypeOfElabHM ctx (List.replicate bindings.length none) bindings body ρ) :
    TypeOfElabHM ctx (.letRec bindings body) ρ := by
  obtain ⟨specs, G, L, hanns, hlen, hG, hlc, _hwf, hcofin, hbody⟩ := h
  obtain ⟨τs, rfl⟩ := specs_all_mono hanns
  refine TypeOfElabHM.letRec (τs := τs) (Ms := τs.map (PolyTy.genGroup G)) (G := G) (L := L)
    (by simpa using hlen) (by simp) ?_ hG ?_ ?_ rfl ?_
  · intro τ hτ
    exact hlc τ (List.mem_map_of_mem hτ)
  · intro p hp
    obtain ⟨a, b, hab, rfl⟩ := mem_zip_map_right' hp
    have hd := mem_zip_self_eq hab
    simp only at hd
    rw [hd]
  · intro Xs hfresh p hp
    obtain ⟨e, τ, heτ, rfl⟩ := mem_zip_map_right' hp
    have hty := (hcofin Xs hfresh (e, .mono τ) (mem_zip_map_right heτ)).1 τ rfl
    rwa [map_mono_rhsEntry G Xs τs] at hty
  · rwa [map_mono_bodyScheme] at hbody

/-- **`letRecAnn` embeds** (all-`some` direction 1): a Core `letRecAnn`
    derivation is a `MixedRule` derivation with every binding annotated (empty
    pool `G = []`). -/
theorem MixedRule.of_letRecAnn {ctx : Ctx} {schemes : List PolyTy} {bindings : List Expr}
    {body : Expr} {ρ : Ty}
    (h : TypeOfElabHM ctx (.letRecAnn schemes bindings body) ρ) :
    MixedRule TypeOfElabHM ctx (schemes.map Option.some) bindings body ρ := by
  cases h with
  | letRecAnn hlen hwf hcofin heq hbody =>
    subst heq
    expose_names
    refine ⟨schemes.map RecSpec.poly, [], L, by rw [List.map_map]; rfl,
      by simpa using hlen, List.nodup_nil, ?_, ?_, ?_, ?_⟩
    · intro τ hτ
      simp at hτ
    · intro σ hσ
      simp only [List.mem_map, RecSpec.poly.injEq] at hσ
      obtain ⟨σ', hσ', rfl⟩ := hσ
      exact hwf σ' hσ'
    · intro Xs _hfresh p hp
      obtain ⟨e, σ, heσ, heq2⟩ := mem_zip_map_right' hp
      subst heq2
      refine ⟨fun τ hτ => RecSpec.noConfusion hτ, ?_⟩
      intro σ' hσ' Ys hYs
      injection hσ' with hσσ
      subst hσσ
      have hYsL : FreshNames L σ.paramCount Ys :=
        ⟨hYs.length, hYs.nodup, fun y hy hc => hYs.avoid y hy (List.mem_append_left _ hc)⟩
      have hty := hcofin (e, σ) heσ Ys hYsL
      rwa [← map_poly_rhsEntry [] Xs schemes] at hty
    · rwa [← map_poly_bodyScheme [] schemes] at hbody

/-- **`letRecAnn` projects** (all-`some` direction 2): a `MixedRule` derivation
    with every binding annotated yields a Core `letRecAnn` derivation. The pool
    `G` the mixed derivation carries is vacuous (no unannotated member mentions
    it), and cofiniteness lets us fold the pool opening `Xs` into the
    constructor's exclusion set. -/
theorem MixedRule.to_letRecAnn {ctx : Ctx} {schemes : List PolyTy} {bindings : List Expr}
    {body : Expr} {ρ : Ty}
    (h : MixedRule TypeOfElabHM ctx (schemes.map Option.some) bindings body ρ) :
    TypeOfElabHM ctx (.letRecAnn schemes bindings body) ρ := by
  obtain ⟨specs, G, L, hanns, hlen, _hG, _hlc, hwf, hcofin, hbody⟩ := h
  have hspecs := specs_all_poly hanns
  subst hspecs
  -- Fix ONE pool opening; the constructor's exclusion set then also excludes it.
  obtain ⟨Xs, hXlen, hXnodup, hXavoid⟩ := exists_fresh_names L G.length
  have hXfresh : FreshNames L G.length Xs := ⟨hXlen, hXnodup, hXavoid⟩
  refine TypeOfElabHM.letRecAnn (schemes := schemes) (L := L ++ Xs)
    (by simpa using hlen) ?_ ?_ rfl ?_
  · intro σ hσ
    exact hwf σ (List.mem_map_of_mem hσ)
  · intro p hp Ys hYs
    have hty := (hcofin Xs hXfresh (p.1, .poly p.2) (mem_zip_map_right hp)).2 p.2 rfl Ys hYs
    rwa [map_poly_rhsEntry G Xs schemes] at hty
  · rwa [map_poly_bodyScheme G schemes] at hbody

/-! ## Positive witness: a genuinely mixed group

```
let rec (f : ∀a. a → a) = λx. let _ = f () in x   -- annotated, poly-recursive
        g                = λx. f x                 -- unannotated
in g 0
```

Both regimes are exercised at once, with cross-boundary interaction:
- `f` recursively instantiates ITS OWN scheme at `unit` while being checked at a
  fresh skolem `Y` — polymorphic recursion (the `letRecAnn` regime), so the
  group has no all-unannotated reading (`f`'s monotype would be pinned to
  `unit → unit`, and then `g 0` in the body fails);
- `g` instantiates the annotated sibling `f` at `g`'s own shared pool variable
  (`τ_g = g0 → g0` with pool `G = [g0]`, presented opened as `X → X` while
  checking), and is then GENERALISED over the pool for the body (`letRec`
  regime): the body uses `g` at `int`. And it has no all-annotated reading
  as written, since `g` carries no annotation.

Stated for `TypeOfHM` (the decoration-blind source spec — the right home for a
typeability witness). The elaborated/decorated (`TypeOfElabHM`) counterpart
goes through the Λ-outside `letIn` nest exactly as for the shipped `letRec`
(bare-node decorations cannot vary with the cofinite opening; that is a known
property of the shipped rule, not a new obstruction). -/

/-- `∀a. a → a`. -/
def selfSig : PolyTy := ⟨1, .arrow (.bvar 0) (.bvar 0)⟩

/-- `g`'s shared monotype `g0 → g0`, carrying the pool var `g0 = 0`. -/
def gMono : Ty := .arrow (.fvar 0) (.fvar 0)

/-- `f`'s RHS: `λx. let _ = f () in x` (under the λ: `f = var 1`; under the
    inner let: `x = var 1`). The recursive call instantiates `f`'s scheme at
    `unit` — polymorphic recursion. -/
def fRhs : Expr :=
  .lambda none (.letIn none (.app (.var 1 []) (.primLit .unit)) (.var 1 []))

/-- `g`'s RHS: `λx. f x` (under the λ: `f = var 1`, `x = var 0`): the
    unannotated member calls the annotated sibling at `g`'s own pool variable. -/
def gRhs : Expr := .lambda none (.app (.var 1 []) (.var 0 []))

/-- The body `g 0`: uses the GENERALISED `g` at `int` (`g = var 1`). -/
def mixedBody : Expr := .app (.var 1 []) (.primLit (.int 0))

theorem mixed_typeable :
    MixedRule TypeOfHM ⟨[], []⟩ [some selfSig, none] [fRhs, gRhs] mixedBody (.prim .int) := by
  refine ⟨[.poly selfSig, .mono gMono], [0], [0], rfl, rfl, by simp, ?_, ?_, ?_, ?_⟩
  · -- mono monotypes are LC
    intro τ hτ
    simp only [List.mem_cons, List.not_mem_nil, or_false, reduceCtorEq, false_or] at hτ
    injection hτ with h
    rw [h]
    exact .arrow .fvar .fvar
  · -- poly schemes are WF
    intro σ hσ
    simp only [List.mem_cons, List.not_mem_nil, or_false, reduceCtorEq, or_false] at hσ
    injection hσ with h
    rw [h]
    show ContainsBvarsUpTo 1 (Ty.arrow (.bvar 0) (.bvar 0))
    exact .arrow (.bvar (by omega)) (.bvar (by omega))
  · -- the fused cofinite premise
    intro Xs hfresh
    obtain ⟨X, rfl⟩ : ∃ X, Xs = [X] := List.length_eq_one_iff.mp hfresh.length
    intro p hp
    simp only [List.zip_cons_cons, List.zip_nil_right, List.mem_cons, List.not_mem_nil,
      or_false] at hp
    rcases hp with rfl | rfl
    · -- annotated member `f`, checked at its own nested skolem opening `Y`
      refine ⟨fun τ h => RecSpec.noConfusion h, ?_⟩
      intro σ hσ
      injection hσ with h
      rw [← h]
      intro Ys hYs
      obtain ⟨Y, rfl⟩ : ∃ Y, Ys = [Y] := List.length_eq_one_iff.mp hYs.length
      -- env: f at its FULL scheme, g at its OPENED shared monotype `X → X`
      show TypeOfHM ⟨[selfSig, PolyTy.mkTrivial (.arrow (.fvar X) (.fvar X))], []⟩
        fRhs (.arrow (.fvar Y) (.fvar Y))
      refine TypeOfHM.lambda .fvar (fun T h => Option.noConfusion h) rfl ?_
      -- `let _ = f ()`: the recursive call instantiates `σ_f` at `unit`
      refine TypeOfHM.letIn (M := PolyTy.mkTrivial (.prim .unit)) (L := [])
        .prim (fun σ' h => Option.noConfusion h) ?_ rfl ?_
      · intro Xs' hfresh'
        obtain rfl : Xs' = [] := List.eq_nil_of_length_eq_zero hfresh'.length
        refine TypeOfHM.app ?_ TypeOfHM.primLitUnit
        exact TypeOfHM.var (polyTy := selfSig) (instArgs := [.prim .unit]) rfl
          (by intro t ht; simp only [List.mem_singleton] at ht; subst ht; exact .prim)
          (.arrow (.bvar rfl) (.bvar rfl))
      · exact TypeOfHM.var (polyTy := PolyTy.mkTrivial (.fvar Y)) (instArgs := []) rfl
          (by intro t ht; cases ht) .fvar
    · -- unannotated member `g`, checked at its opened shared monotype `X → X`
      refine ⟨?_, fun σ h => RecSpec.noConfusion h⟩
      intro τ hτ
      injection hτ with h
      rw [← h]
      show TypeOfHM ⟨[selfSig, PolyTy.mkTrivial (.arrow (.fvar X) (.fvar X))], []⟩
        gRhs (.arrow (.fvar X) (.fvar X))
      refine TypeOfHM.lambda .fvar (fun T h => Option.noConfusion h) rfl ?_
      refine TypeOfHM.app (argTy := .fvar X) ?_ ?_
      · -- cross-boundary: instantiate the annotated sibling at the pool skolem `X`
        exact TypeOfHM.var (polyTy := selfSig) (instArgs := [.fvar X]) rfl
          (by intro t ht; simp only [List.mem_singleton] at ht; subst ht; exact .fvar)
          (.arrow (.bvar rfl) (.bvar rfl))
      · exact TypeOfHM.var (polyTy := PolyTy.mkTrivial (.fvar X)) (instArgs := []) rfl
          (by intro t ht; cases ht) .fvar
  · -- the body sees `f : ∀a. a→a` (declared) and `g : ∀a. a→a` (GENERALISED
    -- from `g0 → g0` over the pool `[g0]`), and uses `g` at `int`
    show TypeOfHM ⟨[selfSig, selfSig], []⟩ mixedBody (.prim .int)
    refine TypeOfHM.app (argTy := .prim .int) ?_ TypeOfHM.primLitInt
    exact TypeOfHM.var (polyTy := selfSig) (instArgs := [.prim .int]) rfl
      (by intro t ht; simp only [List.mem_singleton] at ht; subst ht; exact .prim)
      (.arrow (.bvar rfl) (.bvar rfl))

/-! Sanity (mirrors `SpikeLetRecAnn`'s `monoRec_untypeable` check): the SAME
program's all-unannotated reading — drop `f`'s annotation and read the group as
a plain `letRec` — is REJECTED by the shipped checker: the recursive call
`f ()` pins `f`'s monotype to `unit → unit`, so `g : unit → unit` and the
body's `g 0` fails. The mixed witness above genuinely needs the annotated
regime for `f` (and, since `g` has no annotation, the unannotated regime for
`g`): neither shipped rule covers it alone. -/
#guard (typecheck [] (.letRec [fRhs, gRhs] mixedBody)).isSome = false


/-! ## Negative witness: the skolem-leak program is REJECTED

```
let rec (f : ∀a. a → a) = λx. g x   -- forces τ_g = Y → Y at f's OWN skolem Y
        g                = …
in …
```

Checking `f` at a fresh opening `Y` of its scheme forces the unannotated
sibling's monotype to be `Y → Y`. But the shared monotypes live OUTSIDE the
per-binding skolem quantifier (the load-bearing nesting), so `τ_g` is fixed
before `Y` is chosen — cofiniteness then supplies a `Y` avoiding `τ_g`'s free
variables, and the forced equation `τ_g[G↦Xs] = ? → Y` is unsatisfiable.

Machine-checks the claim that the fused rule cannot leak a rigid annotation
variable into the shared pool: this program is untypeable for EVERY `g`-RHS,
body, and result type. (An HM-correct rejection: `g` would need to be `a → a`
at `f`'s rigid `a`, which a monomorphic binding cannot be for all `a`.) -/

/-- `f`'s RHS: `λx. g x` (under the λ: `f = var 1`, `g = var 2`). -/
def fLeakRhs : Expr := .lambda none (.app (.var 2 []) (.var 0 []))

theorem skolemLeak_untypeable (gAny body : Expr) (ρ : Ty) :
    ¬ MixedRule TypeOfHM ⟨[], []⟩ [some selfSig, none] [fLeakRhs, gAny] body ρ := by
  rintro ⟨specs, G, L, hanns, hlen, hG, hlc, hwf, hcofin, hbody⟩
  -- The spec list is forced: `[.poly selfSig, .mono τg]` for some `τg`.
  match specs, hanns with
  | [s1, s2], hanns =>
    simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hanns
    obtain ⟨h1, h2⟩ := hanns
    cases RecSpec.ann_eq_some h1
    obtain ⟨τg, rfl⟩ := RecSpec.ann_eq_none h2
    clear h1 h2
    -- Fix ONE pool opening `Xs`; `T := τg[G↦Xs]` is then a FIXED type.
    obtain ⟨Xs, hXlen, hXnodup, hXavoid⟩ := exists_fresh_names L G.length
    -- Cofiniteness: pick the skolem `Y` fresh ALSO for `T`'s free variables.
    obtain ⟨Ys, hYlen, hYnodup, hYavoid⟩ :=
      exists_fresh_names (L ++ Xs ++ (Ty.renameG G Xs τg).freeVars) 1
    obtain ⟨Y, rfl⟩ : ∃ Y, Ys = [Y] := List.length_eq_one_iff.mp hYlen
    have hYfresh : FreshNames (L ++ Xs) 1 [Y] :=
      ⟨hYlen, hYnodup, fun y hy hc => hYavoid y hy (List.mem_append_left _ hc)⟩
    have hty := (hcofin Xs ⟨hXlen, hXnodup, hXavoid⟩
        (fLeakRhs, .poly selfSig)
        (by simp only [List.zip_cons_cons]; exact List.mem_cons_self)).2
      selfSig rfl [Y] hYfresh
    -- `hty : λx. g x  :  Y → Y` in env `[σ_f, mkTrivial T]`. Invert it.
    have hty' : TypeOfHM
        ⟨[selfSig, PolyTy.mkTrivial (Ty.renameG G Xs τg)], []⟩
        (.lambda none (.app (.var 2 []) (.var 0 [])))
        (.arrow (.fvar Y) (.fvar Y)) := hty
    cases hty' with
    | lambda hbv hann heq hbody' =>
      subst heq
      cases hbody' with
      | app hf _harg =>
        cases hf with
        | var hlook hLC hinst =>
          -- The looked-up scheme at index 2 is `g`'s (trivial) monotype entry.
          simp only [List.getElem?_cons_succ, List.getElem?_cons_zero,
            Option.some.injEq] at hlook
          rw [← hlook] at hinst
          -- `T` is LC, so instantiation is the identity: `T = ? → Y`.
          have hTlc : (Ty.renameG G Xs τg).IsLC :=
            renameG_isLC (hlc τg (by simp))
          have heqT := InstantiatesBy.eq_openWith_range hinst hTlc
          simp only [List.range_zero, List.map_nil, Ty.openWith_nil] at heqT
          -- So `Y ∈ T.freeVars` — contradicting `Y`'s freshness for `T`.
          have hYT : Y ∈ (Ty.renameG G Xs τg).freeVars := by
            rw [show (Ty.renameG G Xs τg) = (PolyTy.mkTrivial (Ty.renameG G Xs τg)).body from rfl,
              ← heqT]
            simp [Ty.freeVars, List.mem_dedup]
          exact hYavoid Y List.mem_cons_self (List.mem_append_right _ hYT)

/-! ## Tractability 1: `weaken_env`

The historically dangerous lemma (the §2.3 existential-premise redesign died
here). Both cofinite openings are quantified (never pinned), so weakening
delegates every RHS/body to `TypeOfElabHM.weaken_env` with NO freshness side
condition and NO growth of `L` — the nesting adds no friction: the `Ys`
quantifier rides along untouched inside the `Xs` one. -/
theorem MixedRule.weaken_env_front {ctors : CtorEnv} {env_extra env : Env}
    {anns : List (Option PolyTy)} {bindings : List Expr} {body : Expr} {ρ : Ty}
    (h : MixedRule TypeOfElabHM ⟨env, ctors⟩ anns bindings body ρ) :
    MixedRule TypeOfElabHM ⟨env_extra ++ env, ctors⟩ anns
      (bindings.map (·.shiftFrom bindings.length env_extra.length))
      (body.shiftFrom bindings.length env_extra.length) ρ := by
  obtain ⟨specs, G, L, hanns, hlen, hG, hlc, hwf, hcofin, hbody⟩ := h
  refine ⟨specs, G, L, hanns, by simpa using hlen, hG, hlc, hwf, ?_, ?_⟩
  · intro Xs hfresh p hp
    obtain ⟨a, b, _ha, hab, rfl⟩ := mem_zip_map_left hp
    refine ⟨?_, ?_⟩
    · intro τ hτ
      have hty := (hcofin Xs hfresh (a, b) hab).1 τ hτ
      have hw := TypeOfElabHM.weaken_env (env_pre := specs.map (RecSpec.rhsEntry G Xs))
        (env_extra := env_extra) (env := env) hty
      rw [List.append_assoc] at hw
      simpa only [List.length_map, ← hlen] using hw
    · intro σ hσ Ys hYs
      have hty := (hcofin Xs hfresh (a, b) hab).2 σ hσ Ys hYs
      have hw := TypeOfElabHM.weaken_env (env_pre := specs.map (RecSpec.rhsEntry G Xs))
        (env_extra := env_extra) (env := env) hty
      rw [List.append_assoc, Expr.shiftFrom_openTyVars] at hw
      simpa only [List.length_map, ← hlen] using hw
  · have hw := TypeOfElabHM.weaken_env (env_pre := specs.map (RecSpec.bodyScheme G))
      (env_extra := env_extra) (env := env) hbody
    rw [List.append_assoc] at hw
    simpa only [List.length_map, ← hlen] using hw


/-! ## Tractability 2: `typ_subst`

Pushing `[Z ↦ U]` through the fused rule = Core's `letRec` case machinery
(freshen the pool `G ↦ W` to dodge `Z`/`U`, transport monotypes by
`renameG_substFvar_comm`/`renameG_renameG`/`genGroup_renameG`) PLUS Core's
`letRecAnn` case machinery (schemes substituted pointwise, `openTyVars`/`openVars`
commutation) — running SIMULTANEOUSLY on the same env. The one genuinely new
ingredient is the per-constructor env transport
`specs'.map (rhsEntry W Xs) = (specs.map (rhsEntry G Xs)).substFvar Z U`,
which splits pointwise by `RecSpec` constructor into exactly those two known
computations. Every lemma needed already exists in Core. -/

/-- Free vars contributed by a spec's shared monotype (poly schemes are handled
    pointwise and need no pool-freshening). -/
private def monoFvs : RecSpec → List Nat
  | .mono τ => τ.freeVars
  | .poly _ => []

/-- The spec transport for `[Z ↦ U]` under a pool-freshening `G ↦ W`. -/
private def RecSpec.subst (Z : Nat) (U : Ty) (G W : List Nat) : RecSpec → RecSpec
  | .mono τ => .mono (Ty.substFvar Z U (Ty.renameG G W τ))
  | .poly σ => .poly (PolyTy.substFvar Z U σ)

theorem MixedRule.typ_subst {ctors : CtorEnv} {env : Env}
    {anns : List (Option PolyTy)} {bindings : List Expr} {body : Expr} {ρ : Ty}
    {Z : Nat} {U : Ty}
    (hZ : Z ∉ env.freeVars) (hUlc : U.IsLC)
    (h : MixedRule TypeOfElabHM ⟨env, ctors⟩ anns bindings body ρ) :
    MixedRule TypeOfElabHM ⟨env, ctors⟩
      (anns.map (Option.map (PolyTy.substFvar Z U)))
      (bindings.map (·.substTyFvar Z U)) (body.substTyFvar Z U)
      (Ty.substFvar Z U ρ) := by
  obtain ⟨specs, G, L, hanns, hlen, hG, hlc, hwf, hcofin, hbody⟩ := h
  -- Freshen the pool `G ↦ W` to dodge `Z`, `U`'s free vars, and the monotypes'.
  obtain ⟨W, hWlen0, hWnodup, hWavoid⟩ :=
    exists_fresh_names (G ++ [Z] ++ U.freeVars ++ specs.flatMap monoFvs) G.length
  have hWG : ∀ w ∈ W, w ∉ G := fun w hw hc =>
    hWavoid w hw (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ hc)))
  have hGW : ∀ g ∈ G, g ∉ W := fun g hg hc => hWG g hc hg
  have hZW : Z ∉ W := fun hc =>
    hWavoid Z hc (List.mem_append_left _ (List.mem_append_left _
      (List.mem_append_right _ (List.mem_singleton.2 rfl))))
  have hUW : ∀ u ∈ U.freeVars, u ∉ W := fun u hu hc =>
    hWavoid u hc (List.mem_append_left _ (List.mem_append_right _ hu))
  have hWmono : ∀ τ, RecSpec.mono τ ∈ specs → ∀ w ∈ W, w ∉ τ.freeVars :=
    fun τ hτ w hw hc =>
      hWavoid w hw (List.mem_append_right _
        (List.mem_flatMap.mpr ⟨.mono τ, hτ, hc⟩))
  refine ⟨specs.map (RecSpec.subst Z U G W), W, Z :: (G ++ W ++ L), ?_, ?_, hWnodup,
    ?_, ?_, ?_, ?_⟩
  · -- the stored annotations transport pointwise
    rw [List.map_map, ← hanns, List.map_map]
    apply List.map_congr_left
    intro s _
    cases s <;> rfl
  · simpa using hlen
  · -- transported monotypes are LC
    intro τ' hτ'
    obtain ⟨s, hs, hsubst⟩ := List.mem_map.mp hτ'
    cases s with
    | mono τ =>
      injection hsubst with hττ
      rw [← hττ]
      exact Ty.IsLC.substFvar hUlc (renameG_isLC (hlc τ hs))
    | poly σ => exact RecSpec.noConfusion hsubst
  · -- transported schemes are WF
    intro σ' hσ'
    obtain ⟨s, hs, hsubst⟩ := List.mem_map.mp hσ'
    cases s with
    | mono τ => exact RecSpec.noConfusion hsubst
    | poly σ =>
      injection hsubst with hσσ
      rw [← hσσ]
      exact PolyTy.WF.substFvar hUlc (hwf σ hs)
  · -- the fused cofinite premise
    intro Xs hfresh
    -- freshness bookkeeping for the pool opening
    have hXlenW : Xs.length = W.length := hfresh.length
    have hXlenG : Xs.length = G.length := hXlenW.trans hWlen0
    have hZXs : Z ∉ Xs := fun hc => hfresh.avoid Z hc List.mem_cons_self
    have hGXs : ∀ g ∈ G, g ∉ Xs := fun g hg hc =>
      hfresh.avoid g hc (List.mem_cons_of_mem _ (List.mem_append_left _ (List.mem_append_left _ hg)))
    have hWXs : ∀ w ∈ W, w ∉ Xs := fun w hw hc =>
      hfresh.avoid w hc (List.mem_cons_of_mem _ (List.mem_append_left _ (List.mem_append_right _ hw)))
    have hXsL : FreshNames L G.length Xs :=
      ⟨hXlenG, hfresh.nodup, fun x hx hc =>
        hfresh.avoid x hx (List.mem_cons_of_mem _ (List.mem_append_right _ hc))⟩
    -- the pointwise monotype transport (Core's `key` computation)
    have key : ∀ τ, RecSpec.mono τ ∈ specs →
        Ty.renameG W Xs (Ty.substFvar Z U (Ty.renameG G W τ))
          = Ty.substFvar Z U (Ty.renameG G Xs τ) := by
      intro τ hτ
      rw [Ty.renameG_substFvar_comm hUlc hZW hUW hZXs
            (renameG_isLC (hlc τ hτ)) hWnodup hXlenW hWXs,
          Ty.renameG_renameG (hlc τ hτ) hG hWnodup hWlen0 hXlenG hGW (hWmono τ hτ) hWXs hGXs]
    -- the RHS-env transport: pointwise by constructor
    have henv_rhs : (specs.map (RecSpec.subst Z U G W)).map (RecSpec.rhsEntry W Xs)
        = Env.substFvar Z U (specs.map (RecSpec.rhsEntry G Xs)) := by
      show _ = (specs.map (RecSpec.rhsEntry G Xs)).map (PolyTy.substFvar Z U)
      rw [List.map_map, List.map_map]
      apply List.map_congr_left
      intro s hs
      cases s with
      | mono τ =>
        show PolyTy.mkTrivial (Ty.renameG W Xs (Ty.substFvar Z U (Ty.renameG G W τ)))
          = PolyTy.substFvar Z U (PolyTy.mkTrivial (Ty.renameG G Xs τ))
        rw [key τ hs]
        rfl
      | poly σ => rfl
    intro p hp
    obtain ⟨a, b, hab, rfl⟩ := mem_zip_map hp
    refine ⟨?_, ?_⟩
    · -- unannotated member: `letRec`-case transport
      intro τ' hτ'
      cases b with
      | poly σ => exact RecSpec.noConfusion hτ'
      | mono τ =>
        injection hτ' with hττ
        rw [← hττ, key τ (List.of_mem_zip hab).2]
        have hty := (hcofin Xs hXsL (a, .mono τ) hab).1 τ rfl
        have hsub := TypeOfElabHM.typ_subst_preservation
          (env_post := specs.map (RecSpec.rhsEntry G Xs)) (env_outer := env) hZ hUlc hty
        rwa [← henv_rhs] at hsub
    · -- annotated member: `letRecAnn`-case transport, nested inside the pool
      intro σ' hσ' Ys hYs
      cases b with
      | mono τ => exact RecSpec.noConfusion hσ'
      | poly σ =>
        injection hσ' with hσσ
        rw [← hσσ]
        have hpc : σ'.paramCount = σ.paramCount := by rw [← hσσ]; rfl
        have hZYs : Z ∉ Ys := fun hc =>
          hYs.avoid Z hc (List.mem_append_left _ List.mem_cons_self)
        have hYsOld : FreshNames (L ++ Xs) σ.paramCount Ys := by
          refine ⟨hYs.length.trans hpc, hYs.nodup, ?_⟩
          intro y hy hc
          rcases List.mem_append.mp hc with hcL | hcXs
          · exact hYs.avoid y hy (List.mem_append_left _
              (List.mem_cons_of_mem _ (List.mem_append_right _ hcL)))
          · exact hYs.avoid y hy (List.mem_append_right _ hcXs)
        have hty := (hcofin Xs hXsL (a, .poly σ) hab).2 σ rfl Ys hYsOld
        have hsub := TypeOfElabHM.typ_subst_preservation
          (env_post := specs.map (RecSpec.rhsEntry G Xs)) (env_outer := env) hZ hUlc hty
        rwa [← henv_rhs, Expr.substTyFvar_openTyVars hUlc hZYs,
          ← PolyTy.substFvar_openVars hUlc hZYs] at hsub
  · -- the body: env transport pointwise by constructor
    have henv_body : (specs.map (RecSpec.subst Z U G W)).map (RecSpec.bodyScheme W)
        = Env.substFvar Z U (specs.map (RecSpec.bodyScheme G)) := by
      show _ = (specs.map (RecSpec.bodyScheme G)).map (PolyTy.substFvar Z U)
      rw [List.map_map, List.map_map]
      apply List.map_congr_left
      intro s hs
      cases s with
      | mono τ =>
        show PolyTy.genGroup W (Ty.substFvar Z U (Ty.renameG G W τ))
          = PolyTy.substFvar Z U (PolyTy.genGroup G τ)
        rw [PolyTy.genGroup_renameG (hlc τ hs) hWlen0 hG hWnodup hGW (hWmono τ hs),
          PolyTy.genGroup_substFvar hZW hUW]
      | poly σ => rfl
    have hsub := TypeOfElabHM.typ_subst_preservation
      (env_post := specs.map (RecSpec.bodyScheme G)) (env_outer := env) hZ hUlc hbody
    rwa [← henv_body] at hsub

end SpikeLetRecMixed
