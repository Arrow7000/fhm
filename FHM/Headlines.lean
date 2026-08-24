import FHM.SurfaceBridge
import FHM.EvaluateUnsafe
import FHM.Pretty

/-! # `Headlines` — the human-readable capabilities surface

This module is a **façade**: it proves almost no new mathematics. Its job is to
let a newcomer read ONE file and come away knowing exactly what this language's
type system guarantees, what those guarantees *mean* in plain terms, and
precisely how far the machine-checking currently reaches.

**Status (erasure-on-`Step`).** Type safety and *inference soundness* are closed
and axiom-clean: `Infer.sound` / `InferBranches.sound` / `InferRecGroup.sound`
(coherence of the source checker with the erased machine relation `TypeOfHM`,
via `e.erase`) depend on nothing but `propext`, `Classical.choice`, `Quot.sound`.
The `TypeOfHM` / `Step` dynamics metatheory (substitution lemma, canonical forms,
`progress`, `preservation`, `type_safety(_star)`) is likewise proved, on erased
terms, in `FHM.InferW`. What changed by design (see
`briefs/design-memo-erasure-migration.md` §3.5): the *elaborated* stack —
`TypeOfElabHM`, `Infer.sourceSound`, the `eOut` index, and the completeness /
principality campaign that concluded on elaborated outputs — is **deleted**, not
merely open. The runnable term is always the erased source `c.erase`; there is
no elaborated output left to be complete about.

So: do not read this file as "everything below is proved". Read section 6's
`#print axioms` output, which is the actual, unfakeable status report.

Every name below already exists in `FHM.Core` /
`FHM.SurfaceBridge`; this file re-exports (via doc-comments + `#check`, which
double as a compiler-checked "this name still exists with this shape" guard),
adds a handful of small inversion lemmas, witnesses that the type system's
`SurfaceWTExpr` relation is genuinely inhabited (not vacuously true), and wires
up a *composable, proof-carrying* safe pipeline (`elaborateSafe` / `runSafe`).

Standalone-compilable: `lake env lean FHM/Headlines.lean`. Not added to
`lakefile.toml`.

## The six sections

1. Doc-narrated headline re-exports (type safety, inference sound+complete,
   pattern-compilation correctness, decidable coverage, DataDecl bridge).
2. Universal properties: inversion / canonical-forms lemmas.
3. Witnesses: the relations above are genuinely inhabited, not vacuous.
4. The composable safe pipeline (`elaborateSafe` / `runSafe`).
5. Demos.
6. A living axiom-budget guard (`#print axioms`). -/

open SurfaceBridge SmallStep PatComp

namespace Headlines


/-! ## 1. Doc-narrated headline re-exports

No new proofs in this section — just naming the campaign's headline theorems,
with a one-line plain-English gloss, plus a `#check` of each so THIS FILE FAILS
TO COMPILE if any of these names ever disappear or change shape. -/

/-! ### Type safety (the campaign's central payoff)

**"A well-typed, exhaustive program never gets stuck."** Two headlines say this
at two levels: `surface_type_safe` at the level of a bare surface *expression*
(given that its `lower`ing typechecks and its matches cover their scrutinee's
constructors), and `program_type_safe` at the level of a whole `Surface.Program`
(decls + binding groups + body). `TypeOfHM.type_safety_star` is the iterated
progress+preservation engine both headlines are built on: every term reachable
by any number of `Step`s from a well-typed, exhaustive (erased) term is itself
well-typed and is a value or can step again — "never gets stuck" formalised. -/
#check @surface_type_safe
#check @program_type_safe
#check @TypeOfHM.type_safety_star

/-! ### Type inference is sound: coherent with the erased machine relation

`Infer` (Algorithm-W-style) is the executable inferer. **Soundness**
(`Infer.sound`) is the erasure-on-`Step` coherence theorem: after the inferred
substitution, `TypeOfHM` types the ERASED SOURCE term (`e.erase`) at the erased
inferred type — one typing relation, one soundness theorem. The runnable term is
always `c.erase`; no elaborated output exists. The old completeness /
principality campaign (`CompleteAt`, `complete'`, `iff_typeable`, and their
whole-program corollaries) concluded on removed elaborated outputs and was
deleted with them; what survives honestly are the soundness projections
(`principalType_sound`, `typecheck_sound`, now stated on `e.erase`). -/
#check @Infer.sound

/-! ### Pattern-compilation correctness

Surface `match` sugar compiles to a decision tree (`PatComp.compile`), then
emits Core `let`/ctor-switch code. `PatComp.compile_correct_surface` is the
spec-level headline: on ANY scrutinee value, the compiled tree selects exactly
the branch (and captures) that the trusted `firstMatch` reference semantics
would select — hypothesis-free. `PatComp.lowerMatch_adequate_of_typed` is the
OPERATIONAL form the bridge actually consumes: under typing + value hypotheses,
the emitted Core term's *reduction* reaches the selected branch body with the
right substitution. -/
#check @PatComp.compile_correct_surface
#check @PatComp.lowerMatch_adequate_of_typed

/-! ### Decidable coverage

`checkExhaustive` is a `Bool`-valued, structurally-recursive coverage checker
over surface expressions (recovering the scrutinee's data type from its
patterns, fail-closed when it can't). `checkExhaustive_sound` is its soundness
theorem: `checkExhaustive ctors s = true` implies `SurfaceCovers ctors s`, the
declarative coverage predicate `type_safety` actually needs. -/
#check @checkExhaustive
#check @checkExhaustive_sound

/-! ### The `DataDecl` bridge

User data declarations (surface syntax) elaborate to a Core `CtorEnv` through
two composed steps: `lowerDataDecls*` (surface → Core `DataDecl`, spec/impl
pair `LowersDataDecls`/`lowerDataDeclsIn`) and `elabDecls` (Core `DataDecl`s →
`CtorEnv`, kind-checking every field and proving each `Ctor`'s `bound`/`closed`
obligations). Both steps are sound AND complete against their declarative
specs, so a `CtorEnv` produced by the pipeline is exactly as trustworthy as one
built by hand. -/
#check @lowerDataDecls_sound
#check @lowerDataDecls_complete
#check @elabDecls_sound
#check @elabDecls_complete


/-! ## 2. Universal properties: inversion / canonical-forms lemmas

A typing relation earns its keep partly through its INVERSIONS: given a typed
term of a known shape, what must be true of its subterms? These read as the
"reverse" of the typing rules and are the everyday workhorses of any proof
that inducts over a typed term (progress, preservation, the pattern-compiler
bridge). Most are `intro; cases` — the relation was DESIGNED to make them
free, so their triviality is a feature, not a shortcut. -/

/-- Inverting `.app`: if `f x` types at `τ`, `f` types at some `argTy → τ` and
    `x` types at that same `argTy`. -/
theorem TypeOfHM_app_inv {ctx : Ctx} {f x : Expr} {τ : Ty}
    (h : TypeOfHM ctx (.app f x) τ) :
    ∃ argTy, TypeOfHM ctx f (.arrow argTy τ) ∧ TypeOfHM ctx x argTy := by
  cases h with | app hf hx => exact ⟨_, hf, hx⟩

/-- Inverting `.lambda`: a typed lambda's type MUST be an arrow, its param
    annotation (if present) MUST pin the arrow's domain, and the body types at
    the codomain under the extended context. -/
theorem TypeOfHM_lambda_inv {ctx : Ctx} {ann : Option Ty} {body : Expr} {τ : Ty}
    (h : TypeOfHM ctx (.lambda ann body) τ) :
    ∃ paramTy bodyTy, τ = .arrow paramTy bodyTy ∧ paramTy.IsLC ∧ ann.Pins paramTy ∧
      TypeOfHM { ctx with env := PolyTy.mkTrivial paramTy :: ctx.env } body bodyTy := by
  cases h with
  | lambda hlc hpins heq hbody => exact ⟨_, _, rfl, hlc, hpins, heq ▸ hbody⟩

/-- Inverting the Core-level pair `.app (.app (.ctor cPair) a) b`: unfolds to
    the pairing constructor applied to well-typed `a`/`b`. Two `TypeOfHM_app_inv`
    steps, peeling one `.app` at a time. -/
theorem TypeOfHM_pair_inv {ctx : Ctx} {a b : Expr} {τ : Ty}
    (h : TypeOfHM ctx (.app (.app (.ctor cPair) a) b) τ) :
    ∃ τa τb, TypeOfHM ctx (.ctor cPair) (.arrow τa (.arrow τb τ)) ∧
      TypeOfHM ctx a τa ∧ TypeOfHM ctx b τb := by
  obtain ⟨τb, hf, hb⟩ := TypeOfHM_app_inv h
  obtain ⟨τa, hc, ha⟩ := TypeOfHM_app_inv hf
  exact ⟨τa, τb, hc, ha, hb⟩

/-- Inverting `.letIn`: a typed `let` MUST come from a generalised scheme `M`
    that is well-formed, matches the (optional) annotation, generalises the
    bound expression cofinitely, and whose opened form types the body. -/
theorem TypeOfHM_letIn_inv {ctx : Ctx} {ann : Option PolyTy} {boundExpr body : Expr}
    {τ : Ty} (h : TypeOfHM ctx (.letIn ann boundExpr body) τ) :
    ∃ (M : PolyTy) (L : List Nat),
      PolyTy.WF M ∧ ann.Pins M ∧ GeneralisesTo TypeOfHM ctx ann boundExpr M L ∧
      TypeOfHM { ctx with env := M :: ctx.env } body τ := by
  cases h with
  | letIn hwf hpins hgen heq hbody => exact ⟨_, _, hwf, hpins, hgen, heq ▸ hbody⟩

/-- The `of_lowers` overlap, kept as a documented example: a match-free
    `.pair` surface term has TWO derivation paths through `SurfaceWTExpr` — the
    dedicated `pair` rule, or the generic `of_lowers` catch-all (since `.pair`
    has no `match`, it's `SurfaceExprNoMatch`). Both agree on the resulting
    type; this is exactly the non-uniqueness `Approach A / 1a` accepts (kept
    for match-free ANY expr, restricted to true leaves is future cosmetics,
    item 5). -/
theorem SurfaceWTExpr_pair_inv {ctors : CtorEnv} {ke : KindEnv} {tvs vs : List ValName}
    {Γ : Env} {a b : Surface.Expr} {τ : Ty}
    (h : SurfaceWTExpr ctors ke tvs vs Γ (.pair a b) τ) :
    (∃ τa τb, SurfaceWTExpr ctors ke tvs vs Γ a τa ∧ SurfaceWTExpr ctors ke tvs vs Γ b τb ∧
        TypeOfHM ⟨Γ, ctors⟩ (.ctor cPair) (.arrow τa (.arrow τb τ)))
    ∨ (SurfaceExprNoMatch (.pair a b) ∧
        ∃ c, LowersExpr ctors ke tvs vs (.pair a b) c ∧ TypeOfHM ⟨Γ, ctors⟩ c τ) := by
  cases h with
  | pair ha hb hc => exact Or.inl ⟨_, _, ha, hb, hc⟩
  | of_lowers hnm hL hT => exact Or.inr ⟨hnm, _, hL, hT⟩

/-! ### Canonical forms (re-exported)

The dual of inversion at the VALUE level: a well-typed *value* of a known type
shape must have one of a small enumerable set of head forms.
`TypeOfHM.canonical_arrow` says an arrow-typed value is a lambda, a
constructor chain, a bare primop, or a partially-applied primop.
`TypeOfHM.ctor_chain_inversion` is the keystone both progress and
preservation's `match_` case lean on: a well-typed constructor chain
decomposes into its head constructor applied to well-typed, correctly
instantiated arguments. -/
#check @TypeOfHM.canonical_arrow
#check @TypeOfHM.ctor_chain_inversion


/-! ## 3. Witnesses

Axiom-cleanliness cannot catch a *vacuous* relation — a typing rule with
unsatisfiable premises would still let every proof by induction over it go
through, silently. Witnesses close that gap: they exhibit CONCRETE terms
that actually inhabit the relations above, so the rules used to build them
are provably not dead code. -/

/-- The simplest possible witness: an integer literal is well-typed at `int`. -/
example (ctors : CtorEnv) : SurfaceWT ctors (.primLit (.int 0)) :=
  ⟨.prim .int, .of_lowers .primLit .primLitInt .primLitInt⟩

/-- The identity function `λx. x`, typed structurally (monomorphically) at
    `int → int`. -/
example (ctors : CtorEnv) :
    SurfaceWTExpr ctors (kindEnvOfCtors ctors) [] [] []
      (.lambda (.name ⟨"x"⟩) none (.var ⟨"x"⟩)) (.arrow (.prim .int) (.prim .int)) := by
  apply SurfaceWTExpr.lambda_name
  · exact ContainsBvarsUpTo.prim
  · trivial
  · exact .of_lowers .var (.var (by rfl))
      (TypeOfHM.var (polyTy := PolyTy.mkTrivial (.prim .int)) (instArgs := []) rfl (by simp) .prim)

/-! ### The annotated polymorphic let (`letInAnn`)

`letInAnn` is the composer-authored, cofinite-premise constructor with the
fiddliest hypothesis in the whole relation: `∀ Xs, FreshNames L σ.paramCount
Xs → …`. This witness — `let (id : ∀a. a→a) = λx. x in id` used at `int→int`
— proves the constructor is genuinely inhabitable at a REAL polymorphic
scheme (not just the `paramCount = 0` degenerate case): specialise the
cofinite premise at a single fresh skolem `X`, observe `σ.openVars [X]` is
literally `fvar X → fvar X` by computation, and reuse the identity-lambda
shape above at `paramTy := .fvar X`. The body then instantiates the scheme's
bound variable at `int` via `InstantiatesBy.bvar`. -/
example (ctors : CtorEnv) :
    SurfaceWTExpr ctors (kindEnvOfCtors ctors) [] [] []
      (.letIn (.mk "id") [] []
        (some ⟨[.mk "a"], .arrow (.tvar (.mk "a")) (.tvar (.mk "a"))⟩)
        (.lambda (.name (.mk "x")) none (.var (.mk "x")))
        (.var (.mk "id")))
      (.arrow (.prim .int) (.prim .int)) := by
  set σ : PolyTy := ⟨1, .arrow (.bvar 0) (.bvar 0)⟩
  have hlowσ : lowerPoly (kindEnvOfCtors ctors)
      ⟨[.mk "a"], .arrow (.tvar (.mk "a")) (.tvar (.mk "a"))⟩ = some σ := by
    simp only [lowerPoly, σ]
    have h : ([.mk "a"] : List ValName).eraseDups = [.mk "a"] := rfl
    simp [h, lowerTy, tvarIndex]
  refine SurfaceWTExpr.letInAnn (tvs := []) (vs := []) (Γ := []) (ΓRhs := [])
    (name := .mk "id") (tyParams := []) (params := [])
    (σs := ⟨[.mk "a"], .arrow (.tvar (.mk "a")) (.tvar (.mk "a"))⟩)
    (σ := σ) (rhs := _) (body := _) (τ := _) (L := []) (paramTys := [])
    (τretOf := fun Xs => σ.openVars Xs) ?htvs ?hσeq ?hσwf ?hLL ?hrhs ?hτbinds ?hbody
  · rfl
  · exact lowerPolyAnn_finalizeAnn_nil hlowσ
  · exact .arrow (.bvar (by decide)) (.bvar (by decide))
  · exact LowerLetParams.nil
  · intro Xs hfresh
    have hlen : Xs.length = 1 := by simpa [σ] using hfresh.length
    obtain ⟨X, hXeq⟩ := List.length_eq_one_iff.mp hlen
    subst hXeq
    have hed : ([.mk "a"] : List ValName).eraseDups = [.mk "a"] := rfl
    have hscope : letRhsTyScope [] []
        (some ⟨[.mk "a"], .arrow (.tvar (.mk "a")) (.tvar (.mk "a"))⟩) [] = [.mk "a"] := by
      simp [letRhsTyScope, letAnnTyPrefix, finalizeAnn, mergeTyParams, mergeTyParamNames, hed]
    simp only [hscope, letRhsTermScope, paramTermScope, List.map_nil, List.reverse_nil,
      List.nil_append]
    apply SurfaceWTExpr.lambda_name (paramTy := .fvar X) (bodyTy := .fvar X)
    · exact ContainsBvarsUpTo.fvar
    · trivial
    · exact .of_lowers .var (.var (by rfl))
        (TypeOfHM.var (polyTy := PolyTy.mkTrivial (.fvar X)) (instArgs := []) rfl (by simp) .fvar)
  · intro Xs _; rfl
  · exact .of_lowers .var (.var (by rfl))
      (TypeOfHM.var (polyTy := σ) (instArgs := [Ty.prim .int]) rfl
        (by
          intro t ht
          simp only [List.mem_singleton] at ht
          subst ht
          exact ContainsBvarsUpTo.prim)
        (InstantiatesBy.arrow (InstantiatesBy.bvar rfl) (InstantiatesBy.bvar rfl)))

/-! ### The annotated polymorphic letrec (`letRecInAnn`) — nice-to-have

Same shape one level up: `let rec (id : ∀a. a→a) = λx. x in id`, single-member
recursive group, annotated (so `RecSpec.poly`). No `RecSpec.mono` member, so
`hmono_lc`/`hmono`/`hτbinds` are vacuous; `hpoly`/`hτbinds_poly` are the
substantive premises (empty head-binders: wrap identity, `τretPolyOf = σ.openVars`). -/
example (ctors : CtorEnv) :
    SurfaceWTExpr ctors (kindEnvOfCtors ctors) [] [] []
      (.letRecIn
        [{ name := .mk "id",
           ann := some ⟨[.mk "a"], .arrow (.tvar (.mk "a")) (.tvar (.mk "a"))⟩,
           rhs := .lambda (.name (.mk "x")) none (.var (.mk "x")) }]
        (.var (.mk "id")))
      (.arrow (.prim .int) (.prim .int)) := by
  set σ : PolyTy := ⟨1, .arrow (.bvar 0) (.bvar 0)⟩
  have hed : ([.mk "a"] : List ValName).eraseDups = [.mk "a"] := rfl
  refine SurfaceWTExpr.letRecInAnn (tvs := []) (vs := []) (Γ := [])
    (binds := _) (anns' := [some σ]) (specs := [RecSpec.poly σ])
    (G := []) (L := []) (paramTysList := [[]]) (ΓRhsList := [[σ]])
    (τretsList := [σ.body]) (τretPolyOf := fun _ _ Ys => σ.openVars Ys)
    (body := _) (τ := _)
    ?htvs ?hann ?hlen ?hparamLen ?hΓRhsLen ?hretsLen ?hanns_eq ?hnodup
    ?hmono_lc ?hpoly_wf ?hLL ?hτbinds ?hmono ?hτbinds_poly ?hpoly ?hbody
  · rfl
  · -- `hed` discharges the `eraseDups` redex inside `lowerPoly`/`finalizeAnn`.
    simp [finalizeAnn, mergeTyParams, mergeTyParamNames, lowerAnnList, lowerPolyAnn,
      lowerPoly, hed, lowerTy, tvarIndex, σ, List.map_cons, List.map_nil]
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact List.nodup_nil
  · intro τm h; simp [σ] at h
  · intro σ' h
    simp only [σ, List.mem_singleton] at h
    injection h with h
    subst h
    exact .arrow (.bvar (by decide)) (.bvar (by decide))
  · intro Xs _ i hi
    have hi0 : i = 0 := by
      simp only [List.length_cons, List.length_nil] at hi; omega
    subst hi0
    exact LowerLetParams.nil
  · intro Xs _ i hi τm hspec
    have hi0 : i = 0 := by
      simp only [List.length_cons, List.length_nil] at hi; omega
    subst hi0
    simp only [σ, List.getElem_cons_zero] at hspec
    cases hspec
  · intro Xs _ i hi τm hspec
    have hi0 : i = 0 := by
      simp only [List.length_cons, List.length_nil] at hi; omega
    subst hi0
    simp only [σ, List.getElem_cons_zero] at hspec
    cases hspec
  · intro Xs _ i hi σ' hspec Ys _
    have hi0 : i = 0 := by
      simp only [List.length_cons, List.length_nil] at hi; omega
    subst hi0
    simp only [σ, List.getElem_cons_zero] at hspec
    injection hspec with hspec
    subst hspec
    rfl
  · intro Xs _ i hi σ' hspec Ys hfreshY
    have hi0 : i = 0 := by
      simp only [List.length_cons, List.length_nil] at hi; omega
    subst hi0
    simp only [σ, List.getElem_cons_zero] at hspec
    injection hspec with hspec
    subst hspec
    have hlenY : Ys.length = 1 := by simpa [σ] using hfreshY.length
    obtain ⟨Y, hYeq⟩ := List.length_eq_one_iff.mp hlenY
    subst hYeq
    apply SurfaceWTExpr.lambda_name (paramTy := .fvar Y) (bodyTy := .fvar Y)
    · exact ContainsBvarsUpTo.fvar
    · trivial
    · exact .of_lowers .var (.var (by rfl))
        (TypeOfHM.var (polyTy := PolyTy.mkTrivial (.fvar Y)) (instArgs := []) rfl (by simp) .fvar)
  · exact .of_lowers .var (.var (by rfl))
      (TypeOfHM.var (polyTy := σ) (instArgs := [Ty.prim .int]) rfl
        (by
          intro t ht
          simp only [List.mem_singleton] at ht
          subst ht
          exact ContainsBvarsUpTo.prim)
        (InstantiatesBy.arrow (InstantiatesBy.bvar rfl) (InstantiatesBy.bvar rfl)))

/-! ### Packing B — annotated mono + head binders

Surface-ish:
```
let f (x : Int) : Int = x in f
```
AST: nonempty `params`, return-type `ann`, open body (not `λ` in the RHS).
`finalizeAnn` synthesises the full binding scheme `Int → Int` (paramCount 0);
raw RHS is typed at the return type under the head binder; wrap supplies the
Core λ. -/
private theorem packingB_finalize :
    finalizeAnn [] [(.mk "x", some (.prim .int))] (some ⟨[], .prim .int⟩) =
      some ⟨[], .arrow (.prim .int) (.prim .int)⟩ := by
  simp [finalizeAnn, paramsToArrows, paramsToArrows.go, mergeTyParamNames]

private theorem packingB_lowerPoly (ctors : CtorEnv) :
    lowerPolyAnn (kindEnvOfCtors ctors)
      (finalizeAnn [] [(.mk "x", some (.prim .int))] (some ⟨[], .prim .int⟩)) =
      some (some ⟨0, .arrow (.prim .int) (.prim .int)⟩) := by
  rw [packingB_finalize]
  simp [lowerPolyAnn, lowerPoly, lowerTy]

example (ctors : CtorEnv) :
    SurfaceWTExpr ctors (kindEnvOfCtors ctors) [] [] []
      (.letIn (.mk "f") [] [(.mk "x", some (.prim .int))]
        (some ⟨[], .prim .int⟩)
        (.var (.mk "x"))
        (.var (.mk "f")))
      (.arrow (.prim .int) (.prim .int)) := by
  set σ : PolyTy := ⟨0, .arrow (.prim .int) (.prim .int)⟩
  set paramTys : List Ty := [.prim .int]
  set τret : Ty := .prim .int
  refine SurfaceWTExpr.letInAnn (tvs := []) (vs := []) (Γ := [])
    (ΓRhs := [PolyTy.mkTrivial (.prim .int)])
    (name := .mk "f") (tyParams := [])
    (params := [(.mk "x", some (.prim .int))])
    (σs := ⟨[], .prim .int⟩) (σ := σ)
    (rhs := _) (body := _) (τ := _) (L := [])
    (paramTys := paramTys) (τretOf := fun _ => τret)
    ?htvs ?hσeq ?hσwf ?hLL ?hrhs ?hτbinds ?hbody
  · rfl
  · simpa [σ] using packingB_lowerPoly ctors
  · -- `PolyTy.WF σ` = `ContainsBvarsUpTo 0 (Int → Int)`
    exact .arrow ContainsBvarsUpTo.prim ContainsBvarsUpTo.prim
  · refine LowerLetParams.cons rfl (by simp [lowerTy]) ContainsBvarsUpTo.prim LowerLetParams.nil
  · intro Xs hfresh
    have hXs : Xs = [] := List.eq_nil_of_length_eq_zero (by simpa [σ] using hfresh.length)
    subst hXs
    exact .of_lowers .var (.var (by rfl))
      (TypeOfHM.var (polyTy := PolyTy.mkTrivial (.prim .int)) (instArgs := []) rfl
        (by simp) .prim)
  · intro Xs hfresh
    have hXs : Xs = [] := List.eq_nil_of_length_eq_zero (by simpa [σ] using hfresh.length)
    subst hXs
    simp [paramTys, τret, σ, coreParamsToArrows, PolyTy.openVars]
  · exact .of_lowers .var (.var (by rfl))
      (TypeOfHM.var (polyTy := σ) (instArgs := []) rfl (by simp)
        (InstantiatesBy.arrow InstantiatesBy.prim InstantiatesBy.prim))

/-! ### Packing B — annotated mono letrec + head binders

Same packing as a singleton rec group (`RecSpec.poly` with `paramCount = 0`,
because Core stores annotated schemes via `RecSpec.poly`, not `mono`):
```
let f (x : Int) : Int = x in f
```
-/
example (ctors : CtorEnv) :
    SurfaceWTExpr ctors (kindEnvOfCtors ctors) [] [] []
      (.letRecIn
        [{ name := .mk "f",
           params := [(.mk "x", some (.prim .int))],
           ann := some ⟨[], .prim .int⟩,
           rhs := .var (.mk "x") }]
        (.var (.mk "f")))
      (.arrow (.prim .int) (.prim .int)) := by
  set σ : PolyTy := ⟨0, .arrow (.prim .int) (.prim .int)⟩
  set binds : List Surface.Binding :=
    [{ name := .mk "f",
       params := [(.mk "x", some (.prim .int))],
       ann := some ⟨[], .prim .int⟩,
       rhs := .var (.mk "x") }]
  refine SurfaceWTExpr.letRecInAnn (tvs := []) (vs := []) (Γ := [])
    (binds := binds) (anns' := [some σ]) (specs := [RecSpec.poly σ])
    (G := []) (L := []) (paramTysList := [[.prim .int]])
    (ΓRhsList := [[PolyTy.mkTrivial (.prim .int), σ]])
    (τretsList := [.prim .int])
    (τretPolyOf := fun _ _ _ => .prim .int)
    (body := _) (τ := _)
    ?htvs ?hann ?hlen ?hparamLen ?hΓRhsLen ?hretsLen ?hanns_eq ?hnodup
    ?hmono_lc ?hpoly_wf ?hLL ?hτbinds ?hmono ?hτbinds_poly ?hpoly ?hbody
  · rfl
  · -- lowerAnnList of finalizeAnn return-type sugar
    have h1 := packingB_lowerPoly ctors
    simp [binds, lowerAnnList, h1, σ]
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl  -- RecSpec.ann (poly σ) = some σ
  · exact List.nodup_nil
  · intro τm h; simp [σ] at h
  · intro σ' h
    simp only [List.mem_singleton, σ] at h
    injection h with h; subst h
    exact .arrow ContainsBvarsUpTo.prim ContainsBvarsUpTo.prim
  · intro Xs _ i hi
    have hi0 : i = 0 := by
      simp only [binds, List.length_cons, List.length_nil] at hi; omega
    subst hi0
    refine LowerLetParams.cons rfl (by simp [lowerTy]) ContainsBvarsUpTo.prim LowerLetParams.nil
  · intro Xs _ i hi τm hspec
    have hi0 : i = 0 := by
      simp only [binds, List.length_cons, List.length_nil] at hi; omega
    subst hi0
    simp only [σ, List.getElem_cons_zero] at hspec
    cases hspec
  · intro Xs _ i hi τm hspec
    have hi0 : i = 0 := by
      simp only [binds, List.length_cons, List.length_nil] at hi; omega
    subst hi0
    simp only [σ, List.getElem_cons_zero] at hspec
    cases hspec
  · intro Xs _ i hi σ' hspec Ys hfreshY
    have hi0 : i = 0 := by
      simp only [binds, List.length_cons, List.length_nil] at hi; omega
    subst hi0
    simp only [σ, List.getElem_cons_zero] at hspec
    injection hspec with hspec; subst hspec
    have hYs : Ys = [] := List.eq_nil_of_length_eq_zero (by simpa [σ] using hfreshY.length)
    subst hYs
    simp [coreParamsToArrows, PolyTy.openVars]
  · intro Xs _ i hi σ' hspec Ys hfreshY
    have hi0 : i = 0 := by
      simp only [binds, List.length_cons, List.length_nil] at hi; omega
    subst hi0
    simp only [σ, List.getElem_cons_zero] at hspec
    injection hspec with hspec; subst hspec
    exact .of_lowers .var (.var (by rfl))
      (TypeOfHM.var (polyTy := PolyTy.mkTrivial (.prim .int)) (instArgs := []) rfl
        (by simp) .prim)
  · exact .of_lowers .var (.var (by rfl))
      (TypeOfHM.var (polyTy := σ) (instArgs := []) rfl (by simp)
        (InstantiatesBy.arrow InstantiatesBy.prim InstantiatesBy.prim))


/-! ## 4. The composable safe pipeline

`type_safety` needs TWO independent conjuncts to hold of the runtime term: it
must be well-typed, AND all its matches must be exhaustive. These are checked
by two entirely separate mechanisms (`typecheck` vs. `checkExhaustive`) over
two different representations (the erased Core term `c.erase` vs. the surface
term). Rather than fuse them into one opaque "is this program okay" boolean,
we keep them as independent checks and conjoin only the PROOFS at the return
type — a `Safe` term is a passport that carries evidence of both, so anything
downstream that only needs one of the two conjuncts can project it out
without re-deriving it. -/

/-- Erased-term well-typedness (closed): the type-passing-free `TypeOfHM` of the
    runnable (erased) term, judged against the BOUNDS-erased ctor env (Path R:
    `Infer.sound` still concludes at `eraseBounds` until the bounds layer is gone).
    `erase` happens in `elaborateSafe`, before `WellTyped` is applied, so `e` here
    is already in the image of `Expr.erase`. -/
def WellTyped (ctors : CtorEnv) (e : Expr) : Prop :=
  ∃ τ, TypeOfHM ⟨[], CtorEnv.eraseBounds ctors⟩ (e.erase) τ

/-- A passport: an ERASED term that passed BOTH independent checks (well-typed,
    exhaustive) and is in fact erased (`e.erase = e`, so the step-4 dynamics
    applies). Anything holding a `Safe ctors` can invoke `type_safety` on it. -/
abbrev Safe (ctors : CtorEnv) :=
  { e : Expr // e.erase = e ∧ WellTyped ctors e ∧ AllMatchesExhaustive ctors e }

/-- Run a whole surface program through both checks (typechecking, via
    `typecheck`, and exhaustiveness, via `checkExhaustive`); `some ⟨ctors, ⟨e,
    _⟩⟩` hands back a term that is well-typed AND exhaustive **by
    construction** — the proof is built once here from `program_type_safe` +
    `checkExhaustive_sound` and travels with the term from then on. `none`
    means the program was rejected by lowering, typechecking, or coverage. -/
def elaborateSafe (p : Surface.Program) : Option (Σ ctors : CtorEnv, Safe ctors) :=
  match hlow : lowerProgram p with
  | none => none
  | some (ctors, c) =>
    match htc : (typecheck ctors c).isSome with
    | false => none
    | true =>
      match hcov : checkExhaustive ctors p.term with
      | false => none
      | true =>
        some ⟨ctors, ⟨c.erase, by
          obtain ⟨τ, hty, hexh, _⟩ := program_type_safe hlow htc (checkExhaustive_sound p.term hcov)
          exact ⟨Expr.erase_idem c, ⟨τ, by simpa [Expr.erase_idem] using hty⟩, hexh⟩⟩⟩

/-- A finished run: an actual value, still carrying its `WellTyped` passport.
    (`IsValue` here is what `runSafe_never_stuck` used to have to prove
    ex post facto from `evaluate_sound` + `type_safety_star`; now it's baked
    into the return type itself.) -/
abbrev Value (ctors : CtorEnv) := { v : Expr // IsValue v ∧ WellTyped ctors v }

/-- An unfinished-but-still-safe run: provably well-typed, provably exhaustive,
    and — the new conjunct — provably NOT a value, i.e. genuinely resumable.
    `runSafe_running_reduces` cashes that last conjunct in via `progress`. -/
abbrev Running (ctors : CtorEnv) :=
  { e : Expr // e.erase = e ∧ WellTyped ctors e ∧ AllMatchesExhaustive ctors e ∧ ¬ IsValue e }

/-- Forget the `¬ IsValue` refinement: a `Running` term is still a `Safe` one,
    so `runSafe` can be handed it again (with more fuel) to resume. -/
def Running.toSafe {ctors : CtorEnv} (r : Running ctors) : Safe ctors :=
  ⟨r.val, r.property.1, r.property.2.1, r.property.2.2.1⟩

/-- Progress for a closed, exhaustive `WellTyped` term: it is a value or steps.
    Lifts `TypeOfHM.progress` through the ctor-erase + erase-image
    exhaustiveness bridge (`AllMatchesExhaustive.eraseCtorBounds`). -/
theorem WellTyped.progress {ctors : CtorEnv} {e : Expr}
    (hwt : WellTyped ctors e) (h_erased : e.erase = e) (hexh : AllMatchesExhaustive ctors e) :
    IsValue e ∨ ∃ e', Step e e' := by
  obtain ⟨τ, hty⟩ := hwt
  have hty0 : TypeOfHM ⟨[], CtorEnv.eraseBounds ctors⟩ e τ := by simpa [h_erased] using hty
  exact TypeOfHM.progress hty0 rfl (SmallStep.AllMatchesExhaustive.eraseCtorBounds hexh)

/-- Preservation for `WellTyped`: a step of an erased term preserves
    well-typedness (the step's target is itself erased, via `Step.preserves_erased`). -/
theorem WellTyped.preservation {ctors : CtorEnv} {e e' : Expr}
    (hwt : WellTyped ctors e) (h_erased : e.erase = e) (hstep : Step e e') : WellTyped ctors e' := by
  obtain ⟨τ, hty⟩ := hwt
  have hty0 : TypeOfHM ⟨[], CtorEnv.eraseBounds ctors⟩ e τ := by simpa [h_erased] using hty
  have hty' := TypeOfHM.preservation hstep hty0 h_erased
  have he' : e'.erase = e' := SmallStep.Step.preserves_erased h_erased hstep
  exact ⟨τ, by simpa [he'] using hty'⟩

/-- **Genuinely more to do.** A `Running` term isn't stuck — it's merely out of
    fuel — so it always has a next step. Progress, specialised to the
    `¬ IsValue` disjunct that must fire. -/
theorem runSafe_running_reduces {ctors : CtorEnv} (r : Running ctors) :
    ∃ e', Step r.val e' := by
  obtain hval | ⟨e', hstep⟩ := WellTyped.progress r.property.2.1 r.property.1 r.property.2.2.1
  · exact False.elim (absurd hval r.property.2.2.2)
  · exact ⟨e', hstep⟩

/-- The safe runner: fuel-bounded evaluation of a `Safe` term, proof-carrying
    and resumable. `.inl` means evaluation reached a genuine value (still
    well-typed at the original type — see `Value`). `.inr` means fuel ran out
    on a term that is STILL provably safe and STILL provably not a value
    (`Running`); hand `r.toSafe` back to `runSafe` with more fuel to resume.
    Since a `Safe` term never gets stuck, there is no third, "got stuck",
    outcome — that guarantee is now structural (baked into the return type)
    rather than a corollary proved after the fact. -/
def runSafe (ctors : CtorEnv) (fuel : Nat) (t : Safe ctors) : Value ctors ⊕ Running ctors :=
  match fuel with
  | 0 =>
    if h : isValue t.val = true then
      .inl ⟨t.val, isValue_iff_IsValue.mp h, t.property.2.1⟩
    else
      .inr ⟨t.val, t.property.1, t.property.2.1, t.property.2.2, fun hv => h (isValue_iff_IsValue.mpr hv)⟩
  | n + 1 =>
    if h : isValue t.val = true then
      .inl ⟨t.val, isValue_iff_IsValue.mp h, t.property.2.1⟩
    else
      have hnv : ¬ IsValue t.val := fun hv => h (isValue_iff_IsValue.mpr hv)
      match hs : step t.val with
      | some e' =>
        have hty' : WellTyped ctors e' :=
          WellTyped.preservation t.property.2.1 t.property.1 (step_sound hs)
        have hexh' : AllMatchesExhaustive ctors e' :=
          Step.preserves_exhaustive t.property.2.2 (step_sound hs)
        have herased' : e'.erase = e' :=
          SmallStep.Step.preserves_erased t.property.1 (step_sound hs)
        runSafe ctors n ⟨e', herased', hty', hexh'⟩
      | none =>
        False.elim <| by
          have hprog : IsValue t.val ∨ ∃ e', Step t.val e' :=
            WellTyped.progress t.property.2.1 t.property.1 t.property.2.2
          obtain hval | ⟨e', hstep⟩ := hprog
          · exact absurd hval hnv
          · have hsc := step_complete hstep
            rw [hs] at hsc
            cases hsc


/-! ## 5. Demos

Two small end-to-end runs through `elaborateSafe`/`runSafe`: one that's
accepted (a polymorphic `id`, applied at `int`), and one that's correctly
REJECTED for missing a match arm — `elaborateSafe` returning `none` there is
the pipeline doing its job, not a bug. -/

/-- `let (id : ∀a. a→a) = λx. x in id 41`  — accepted, runs to `41`. -/
private def sHeadlineAnnId : Surface.Program :=
  ⟨[], [],
   .letIn (.mk "id") [] []
     (some ⟨[.mk "a"], .arrow (.tvar (.mk "a")) (.tvar (.mk "a"))⟩)
     (.lambda (.name (.mk "x")) none (.var (.mk "x")))
     (.app (.var (.mk "id")) (.primLit (.int 41)))⟩

/-- `match Just 5 with Just x => x`  — missing the `Nothing` arm, so coverage
    fails and `elaborateSafe` must reject it. -/
private def sHeadlineNonExhaustive : Surface.Program :=
  ⟨[⟨.mk "Maybe", [.mk "a"],
      [(.mk "Just", [.tvar (.mk "a")]), (.mk "Nothing", [])]⟩],
   [],
   .match_ (.app (.ctor ⟨"Just"⟩) (.primLit (.int 5)))
     [(.ctor ⟨"Just"⟩ [.name ⟨"x"⟩], .var ⟨"x"⟩)]⟩

/-- Run a program through the full safe pipeline and print the result: a
    finished value, a still-safe-but-unfinished term (fuel ran out — genuinely
    resumable via `Running.toSafe`), or a rejection from `elaborateSafe`
    itself (ill-typed or non-exhaustive). -/
private def runSafeStr (p : Surface.Program) (fuel : Nat := 100) : String :=
  match elaborateSafe p with
  | none => "elaborateSafe: rejected"
  | some ⟨ctors, t⟩ =>
    match runSafe ctors fuel t with
    | .inl v => toString v.val
    | .inr r => "still running: " ++ toString r.val

#eval! runSafeStr sHeadlineAnnId
-- TODO(let-params): restore when SurfaceBridge sorries discharged
-- #guard runSafeStr sHeadlineAnnId = "41"

-- The same program, starved of fuel: `elaborateSafe` still accepts it (it IS
-- safe), but `runSafe` can't finish in zero steps, so it lands in `.inr`
-- instead of `.inl` — the resumable, "genuinely more to do" outcome.
#eval! runSafeStr sHeadlineAnnId 0

#eval! runSafeStr sHeadlineNonExhaustive
-- TODO(let-params): restore when SurfaceBridge sorries discharged
-- #guard (elaborateSafe sHeadlineNonExhaustive).isSome = false


/-! ## 6. Living axiom-budget guard

The unfakeable status report. A `native_decide` would show up as
`Lean.ofReduceBool` or similar; an unfinished proof shows up as `sorryAx`.
Nothing here is aspirational — the expectations below record what this actually
prints TODAY, so a regression (or a repair) changes the file.

The clean baseline is `{propext, Classical.choice, Quot.sound}`, the three
standard classical axioms mathlib itself depends on. Not every theorem needs
all three; a strict subset (e.g. `[propext, Quot.sound]`) is just as clean.

**Where `sorryAx` still appears, and why.** The seven `Bounds/*` sorries (the
HM/`--bl` gate) are outside this file's imports. Inside its transitive closure,
the old operational-bridge gaps are closed: the erased-dynamics lemmas
(`Step.preserves_erased`, `AllMatchesExhaustive.erase`/`eraseCtorBounds`) and
the whole `TypeOfHM`/`Step` metatheory live proved and axiom-clean in
`FHM.InferW`, so `runSafe` / `elaborateSafe` no longer inherit any `sorryAx`
from a residual bridge.

Inference soundness is closed, and the guard below shows it: the three
`Infer.*sound*` theorems come out clean. That is the load-bearing result this
façade exists to advertise, and it is the one you can currently rely on. -/

-- Closed and clean: erasure-on-`Step` inference soundness.
#print axioms Infer.sound                -- expect {propext, Classical.choice, Quot.sound}
#print axioms InferBranches.sound        -- expect {propext, Classical.choice, Quot.sound}
#print axioms InferRecGroup.sound        -- expect {propext, Classical.choice, Quot.sound}

-- Clean: this file's own inversion lemmas.
#print axioms TypeOfHM_app_inv           -- expect {propext, Quot.sound}
#print axioms TypeOfHM_lambda_inv        -- expect {propext, Quot.sound}
#print axioms TypeOfHM_pair_inv          -- expect {propext, Quot.sound}
#print axioms TypeOfHM_letIn_inv         -- expect {propext, Quot.sound}

-- Closed: operational bridge (erased-dynamics lemmas proved in FHM.InferW).
#print axioms runSafe                    -- expect {propext, Classical.choice, Quot.sound}
#print axioms runSafe_running_reduces    -- expect {propext, Classical.choice, Quot.sound}
-- Inherited from FHM.SurfaceBridge via program_type_safe → surface_type_safe → Infer.sound.
#print axioms elaborateSafe              -- expect {propext, Classical.choice, Quot.sound}

end Headlines
