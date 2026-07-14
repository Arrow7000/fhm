import FHM.SurfaceBridge
import FHM.EvaluateUnsafe
import FHM.Pretty

/-! # `Headlines` — the human-readable capabilities surface

This module is a **façade**: it proves almost no new mathematics. Its job is to
let a newcomer read ONE file and come away knowing exactly what this language's
type system guarantees, what those guarantees *mean* in plain terms, and that
the whole edifice is genuinely axiom-clean (no `sorry`, no custom axioms, no
`native_decide`). Every name below already exists in `FHM.Core` /
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
(decls + binding groups + body). `surface_type_safe_of_SurfaceWT` is the
DECLARATIVE mirror of `surface_type_safe`: it starts from the `SurfaceWTExpr`
typing *relation* (rather than the executable `lower`/`typecheck` pipeline),
closing the spec/impl loop. `TypeOfElabHM.type_safety_star` is the iterated
progress+preservation engine both headlines are built on: every term reachable
by any number of `Step`s from a well-typed, exhaustive term is itself
well-typed and is a value or can step again — "never gets stuck" formalised. -/
#check @surface_type_safe
#check @surface_type_safe_of_SurfaceWT
#check @program_type_safe
#check @TypeOfElabHM.type_safety_star

/-! ### Type inference is sound AND complete

`Infer` (Algorithm-W-style) is the executable inferer. **Soundness**
(`Infer.sound`): whatever `Infer` derives is a genuine declarative typing
(`TypeOfElabHM`) once its substitution is applied. **Completeness**
(`Infer.complete'`): if a declarative typing exists at all, `Infer`'s derived
type is *principal* — every other typing factors through it via a residual
substitution. So `Infer` neither invents nor misses typings. Both rest on
`UnifyRel.complete`: if two locally-closed types have ANY unifier, the
`Unify` search finds one (algorithm ⊇ spec on the unification sub-problem
too). -/
#check @Infer.sound
#check @Infer.complete'
#check @UnifyRel.complete

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
`TypeOfElabHM.canonical_arrow` says an arrow-typed value is a lambda, a
constructor chain, a bare primop, or a partially-applied primop.
`TypeOfElabHM.ctor_chain_inversion` is the keystone both progress and
preservation's `match_` case lean on: a well-typed constructor chain
decomposes into its head constructor applied to well-typed, correctly
instantiated arguments. -/
#check @TypeOfElabHM.canonical_arrow
#check @TypeOfElabHM.ctor_chain_inversion


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
      (.letIn (.mk "id")
        (some ⟨[.mk "a"], .arrow (.tvar (.mk "a")) (.tvar (.mk "a"))⟩)
        (.lambda (.name (.mk "x")) none (.var (.mk "x")))
        (.var (.mk "id")))
      (.arrow (.prim .int) (.prim .int)) := by
  apply SurfaceWTExpr.letInAnn (L := [])
  · rfl                                   -- tvs = []
  · rfl                                   -- lowerPoly ke σs = some σ
  · exact .arrow (.bvar (by decide)) (.bvar (by decide))   -- PolyTy.WF σ
  · -- ∀ Xs, FreshNames [] σ.paramCount Xs → SurfaceWTExpr … rhs (σ.openVars Xs)
    intro Xs hfresh
    obtain ⟨X, hXeq⟩ := List.length_eq_one_iff.mp hfresh.length
    subst hXeq
    show SurfaceWTExpr ctors (kindEnvOfCtors ctors) [] [] []
      (.lambda (.name (.mk "x")) none (.var (.mk "x"))) (.arrow (.fvar X) (.fvar X))
    apply SurfaceWTExpr.lambda_name
    · exact ContainsBvarsUpTo.fvar
    · trivial
    · exact .of_lowers .var (.var (by rfl))
        (TypeOfHM.var (polyTy := PolyTy.mkTrivial (.fvar X)) (instArgs := []) rfl (by simp) .fvar)
  · -- body: `id` used at `int → int`, instantiating σ's bvar at `.prim .int`.
    exact .of_lowers .var (.var (by rfl))
      (TypeOfHM.var (polyTy := ⟨1, .arrow (.bvar 0) (.bvar 0)⟩) (instArgs := [Ty.prim .int]) rfl
        (by
          intro t ht
          simp only [List.mem_singleton] at ht
          subst ht
          exact ContainsBvarsUpTo.prim)
        (InstantiatesBy.arrow (InstantiatesBy.bvar rfl) (InstantiatesBy.bvar rfl)))

/-! ### The annotated polymorphic letrec (`letRecInAnn`) — nice-to-have

Same shape one level up: `let rec (id : ∀a. a→a) = λx. x in id`, single-member
recursive group, annotated (so `RecSpec.poly`). No `RecSpec.mono` member, so
`hmono_lc`/`hmono` are vacuous; `hpoly` is the substantive premise and gets
the identical specialise-at-one-fresh-skolem treatment as `letInAnn` above. -/
example (ctors : CtorEnv) :
    SurfaceWTExpr ctors (kindEnvOfCtors ctors) [] [] []
      (.letRecIn
        [(.mk "id", some ⟨[.mk "a"], .arrow (.tvar (.mk "a")) (.tvar (.mk "a"))⟩,
          .lambda (.name (.mk "x")) none (.var (.mk "x")))]
        (.var (.mk "id")))
      (.arrow (.prim .int) (.prim .int)) := by
  apply SurfaceWTExpr.letRecInAnn (G := []) (L := [])
    (specs := [RecSpec.poly ⟨1, .arrow (.bvar 0) (.bvar 0)⟩])
    (anns' := [some ⟨1, .arrow (.bvar 0) (.bvar 0)⟩])
  -- goal order (per `apply`'s dependency-driven ordering):
  -- htvs, hann, hanns_eq, hnodup, hmono_lc, hpoly_wf, hmono, hpoly, hbody, hlen
  · rfl                                    -- htvs : tvs = []
  · rfl                                    -- hann : lowerAnnList …
  · rfl                                    -- hanns_eq : specs.map RecSpec.ann = anns'
  · exact List.nodup_nil                   -- hnodup : G.Nodup
  · intro τm h; simp at h                  -- hmono_lc (vacuous)
  · intro σ' h                             -- hpoly_wf
    simp only [List.mem_singleton] at h
    injection h with h
    subst h
    exact .arrow (.bvar (by decide)) (.bvar (by decide))
  · intro Xs hfresh i hi τm hspec          -- hmono (vacuous: specs[0] is .poly)
    simp only [List.length_cons, List.length_nil] at hi
    have hi0 : i = 0 := by omega
    subst hi0
    simp only [List.getElem_cons_zero] at hspec
    cases hspec
  · intro Xs hfreshG i hi σ' hspec Ys hfreshY   -- hpoly
    simp only [List.length_cons, List.length_nil] at hi
    have hi0 : i = 0 := by omega
    subst hi0
    simp only [List.getElem_cons_zero] at hspec
    injection hspec with hspec
    subst hspec
    obtain ⟨Y, hYeq⟩ := List.length_eq_one_iff.mp hfreshY.length
    subst hYeq
    show SurfaceWTExpr ctors (kindEnvOfCtors ctors) [] [.mk "id"]
      [RecSpec.rhsEntry [] Xs (RecSpec.poly ⟨1, .arrow (.bvar 0) (.bvar 0)⟩)]
      (.lambda (.name (.mk "x")) none (.var (.mk "x"))) (.arrow (.fvar Y) (.fvar Y))
    apply SurfaceWTExpr.lambda_name
    · exact ContainsBvarsUpTo.fvar
    · trivial
    · exact .of_lowers .var (.var (by rfl))
        (TypeOfHM.var (polyTy := PolyTy.mkTrivial (.fvar Y)) (instArgs := []) rfl (by simp) .fvar)
  · -- hbody: id : int→int under (id ↦ σ)
    exact .of_lowers .var (.var (by rfl))
      (TypeOfHM.var (polyTy := ⟨1, .arrow (.bvar 0) (.bvar 0)⟩) (instArgs := [Ty.prim .int]) rfl
        (by
          intro t ht
          simp only [List.mem_singleton] at ht
          subst ht
          exact ContainsBvarsUpTo.prim)
        (InstantiatesBy.arrow (InstantiatesBy.bvar rfl) (InstantiatesBy.bvar rfl)))
  · rfl                                    -- hlen : binds.length = specs.length


/-! ## 4. The composable safe pipeline

`type_safety` needs TWO independent conjuncts to hold of the runtime term: it
must be well-typed, AND all its matches must be exhaustive. These are checked
by two entirely separate mechanisms (`typecheck` vs. `checkExhaustive`) over
two different representations (the elaborated Core term vs. the surface
term). Rather than fuse them into one opaque "is this program okay" boolean,
we keep them as independent checks and conjoin only the PROOFS at the return
type — a `Safe` term is a passport that carries evidence of both, so anything
downstream that only needs one of the two conjuncts can project it out
without re-deriving it. -/

/-- Well-typed (closed) — one of the two orthogonal safety concerns. The other
    is the existing `AllMatchesExhaustive ctors e`. -/
def WellTyped (ctors : CtorEnv) (e : Expr) : Prop := ∃ τ, TypeOfElabHM ⟨[], ctors⟩ e τ

/-- A passport: a term that passed BOTH independent checks, carrying both
    proofs. Anything holding a `Safe ctors` can invoke `type_safety_star` on
    it with no further side conditions. -/
abbrev Safe (ctors : CtorEnv) := { e : Expr // WellTyped ctors e ∧ AllMatchesExhaustive ctors e }

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
        match helab : elaborateProgram p with
        | none => none
        | some e =>
          some ⟨ctors, ⟨e, by
            obtain ⟨e', τ, helab', hty, hexh, _hsafe⟩ :=
              program_type_safe hlow htc (checkExhaustive_sound p.term hcov)
            rw [helab] at helab'
            obtain rfl := Option.some.inj helab'
            exact ⟨⟨τ, hty⟩, hexh⟩⟩⟩

/-- A finished run: an actual value, still carrying its `WellTyped` passport.
    (`IsValue` here is what `runSafe_never_stuck` used to have to prove
    ex post facto from `evaluate_sound` + `type_safety_star`; now it's baked
    into the return type itself.) -/
abbrev Value (ctors : CtorEnv) := { v : Expr // IsValue v ∧ WellTyped ctors v }

/-- An unfinished-but-still-safe run: provably well-typed, provably exhaustive,
    and — the new conjunct — provably NOT a value, i.e. genuinely resumable.
    `runSafe_running_reduces` cashes that last conjunct in via `progress`. -/
abbrev Running (ctors : CtorEnv) :=
  { e : Expr // WellTyped ctors e ∧ AllMatchesExhaustive ctors e ∧ ¬ IsValue e }

/-- Forget the `¬ IsValue` refinement: a `Running` term is still a `Safe` one,
    so `runSafe` can be handed it again (with more fuel) to resume. -/
def Running.toSafe {ctors : CtorEnv} (r : Running ctors) : Safe ctors :=
  ⟨r.val, r.property.1, r.property.2.1⟩

/-- **Genuinely more to do.** A `Running` term isn't stuck — it's merely out of
    fuel — so it always has a next step. Progress, specialised to the
    `¬ IsValue` disjunct that must fire. -/
theorem runSafe_running_reduces {ctors : CtorEnv} (r : Running ctors) :
    ∃ e', Step r.val e' := by
  obtain ⟨hty, hexh, hnv⟩ := r.property
  obtain ⟨τ, hτ⟩ := hty
  cases TypeOfElabHM.progress hτ rfl hexh with
  | inl hv => exact absurd hv hnv
  | inr h => exact h

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
      .inl ⟨t.val, isValue_iff_IsValue.mp h, t.property.1⟩
    else
      .inr ⟨t.val, t.property.1, t.property.2, fun hv => h (isValue_iff_IsValue.mpr hv)⟩
  | n + 1 =>
    if h : isValue t.val = true then
      .inl ⟨t.val, isValue_iff_IsValue.mp h, t.property.1⟩
    else
      have hnv : ¬ IsValue t.val := fun hv => h (isValue_iff_IsValue.mpr hv)
      match hs : step t.val with
      | some e' =>
        have hty' : WellTyped ctors e' := by
          obtain ⟨τ, hτ⟩ := t.property.1
          exact ⟨τ, TypeOfElabHM.preservation (step_sound hs) hτ⟩
        have hexh' : AllMatchesExhaustive ctors e' :=
          Step.preserves_exhaustive t.property.2 (step_sound hs)
        runSafe ctors n ⟨e', hty', hexh'⟩
      | none =>
        False.elim <| by
          obtain ⟨τ, hτ⟩ := t.property.1
          match TypeOfElabHM.progress hτ rfl t.property.2 with
          | .inl hv => exact hnv hv
          | .inr ⟨_, hstep⟩ => simp [step_complete hstep] at hs


/-! ## 5. Demos

Two small end-to-end runs through `elaborateSafe`/`runSafe`: one that's
accepted (a polymorphic `id`, applied at `int`), and one that's correctly
REJECTED for missing a match arm — `elaborateSafe` returning `none` there is
the pipeline doing its job, not a bug. -/

/-- `let (id : ∀a. a→a) = λx. x in id 41`  — accepted, runs to `41`. -/
private def sHeadlineAnnId : Surface.Program :=
  ⟨[], [],
   .letIn (.mk "id")
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

#eval runSafeStr sHeadlineAnnId
#guard runSafeStr sHeadlineAnnId = "41"

-- The same program, starved of fuel: `elaborateSafe` still accepts it (it IS
-- safe), but `runSafe` can't finish in zero steps, so it lands in `.inr`
-- instead of `.inl` — the resumable, "genuinely more to do" outcome.
#eval runSafeStr sHeadlineAnnId 0

#eval runSafeStr sHeadlineNonExhaustive
#guard (elaborateSafe sHeadlineNonExhaustive).isSome = false


/-! ## 6. Living axiom-budget guard

Every theorem in this file — including ones that FOLD IN the whole campaign
(`elaborateSafe` composes `program_type_safe` with `checkExhaustive_sound`;
`runSafe` composes `TypeOfElabHM.progress`/`.preservation` with
`Step.preserves_exhaustive` at every step) — rests on nothing but the three
standard classical axioms mathlib itself depends on. No `sorry`, no
project-specific axiom, no `native_decide` leakage (a `native_decide` would
show up here as `Lean.ofReduceBool` or similar). If this ever prints anything
OUTSIDE `{propext, Classical.choice, Quot.sound}`, something upstream started
cheating — that's precisely why this guard is `#print axioms`, not a comment.
(Not every theorem needs all three; a strict subset — e.g. `[propext,
Quot.sound]` with no `Classical.choice` — is just as clean.) -/

#print axioms TypeOfHM_app_inv          -- expect ⊆ {propext, Classical.choice, Quot.sound}
#print axioms TypeOfHM_lambda_inv        -- expect ⊆ {propext, Classical.choice, Quot.sound}
#print axioms TypeOfHM_pair_inv          -- expect ⊆ {propext, Classical.choice, Quot.sound}
#print axioms TypeOfHM_letIn_inv         -- expect ⊆ {propext, Classical.choice, Quot.sound}
#print axioms runSafe                    -- expect ⊆ {propext, Classical.choice, Quot.sound}  (= here)
#print axioms runSafe_running_reduces    -- expect ⊆ {propext, Classical.choice, Quot.sound}  (= here)
#print axioms elaborateSafe              -- expect ⊆ {propext, Classical.choice, Quot.sound}  (= here)

end Headlines
