import FHM.SurfaceBridge
import FHM.InferW
import FHM.Completeness
import FHM.Pretty

/-! # `Headlines` — canonical verified capabilities

This compact façade presents the production surface-to-`InferInput` lowering
pipeline, canonical inference guarantees, pattern compilation and coverage,
Core inversion/canonical-forms lemmas, and the proof-carrying erased-term runner.

The historical surface-to-complete-Core lowering, structural `SurfaceWTExpr`
witnesses, and its `elaborateSafe` demonstration remain available from the
opt-in `FHM.Headlines.CompleteCore` module.

This module is part of the default verified build. -/

open SurfaceBridge SmallStep PatComp

namespace Headlines

/-! ## Core runtime type safety -/

#check @TypeOfHM.type_safety_star

/-! ### Surface lowering into canonical inference input

The lowering theorem starts with a surface syntax tree. It preserves partial
annotations in `InferInput`; inference then supplies independent input typing,
annotation fidelity, completed Core typing, and exact runtime erasure. Parsing
source text and joining source spans to editor artifacts are separate concerns. -/
#check @lowerExpr_sound
#check @lowerExpr_complete
#check @LowersExpr.unique
#check @lower_sound
#check @lower_complete
#check @lowerProgram_sound
#check @lowerProgram_complete

-- Guard the public relation's target: it describes partial inference input.
example (ctors : CtorEnv) (ke : KindEnv) :
    List ValName → List ValName → Surface.Expr → InferInput → Prop :=
  LowersExpr ctors ke

/-- The verified surface-to-input and input-to-Core stages compose without a
second lowering or inference pass. -/
theorem lower_and_infer_sound {ctors : CtorEnv} {source : Surface.Expr}
    {input : InferInput} {result : InferenceResult}
    (hlow : lower ctors source = some input)
    (hinfer : inferWithTypes ctors input = some result) :
    Lowers ctors source input ∧
      InputTyping input.rigidVars ⟨[], ctors⟩ input result.ty ∧
      AnnotationCompletion input.rigidVars input result.completedExpr ∧
      TypeOfHM ⟨[], ctors⟩ result.completedExpr result.ty ∧
      result.completedExpr.erase = input.erase := by
  exact ⟨lower_sound hlow, inferWithTypes_input_sound hinfer,
    (inferWithTypes_infer hinfer).completes CtxWF.empty,
    inferWithTypes_source_sound hinfer, inferWithTypes_erase hinfer⟩

/-! ### Canonical partial-input elaboration: exact output and source guarantees

Production lowering preserves anonymous holes in `InferInput` and shared
pattern emission. `inferWithTypes` completes that input once, returning the exact
Core expression executed after erasure and the maps used by editor joins.
`Infer.sourceSound` types that completed expression; `Infer.inputSound` independently
types the authored input when the provisional context is empty. `Infer.completes`
records exact annotation fidelity, and `Infer.erase` preserves runtime syntax.
The `_source` variants also cover internal mutable provisional contexts.
`Infer.principal` factors independently typed candidates through the inferred
result. `Infer.complete` and the executable completeness wrappers establish
acceptance of independently typed inputs, including recursive groups.
The metadata field guards preserve the artifact API; editor source joins remain
operational code outside the verified boundary. -/
#check @Infer.sourceSound
#check @Infer.inputSound_source
#check @Infer.inputSound
#check @Infer.completes_source
#check @Infer.completes
#check @Infer.erase
#check @Infer.sound
#check @InferBranches.sourceSound
#check @InferBranches.inputSound_source
#check @InferBranches.completes_source
#check @InferBranches.erase
#check @inferWithTypes_source_sound
#check @inferWithTypes_input_sound
#check @inferWithTypes_erase
#check @Infer.principal
#check @Infer.complete
#check @inferWithTypesCore_sourceComplete
#check @inferWithTypesCore_complete
#check @inferCore_complete
#check @inferCore_accepts_iff
#check @inferCore_empty_accepts_iff
#check @inferWithTypes_complete
#check @inferWithTypes_accepts_iff
#check @inferWithTypes_principal
#check @inferWithTypes_infer

example (h : Infer K F frontier ctx input next subst output ty) : Infer.Principal h :=
  h.principal

example (input : InferInput) : InferWithTypesCoreSourceComplete input :=
  inferWithTypesCore_sourceComplete input

example (input : InferInput) : InferWithTypesCoreComplete input :=
  inferWithTypesCore_complete input

example (input : InferInput) : InferCoreComplete input := inferCore_complete input

example {ctors : CtorEnv} {input : InferInput} :
    (inferWithTypes ctors input).isSome ↔
      ∃ ty, InputTyping input.rigidVars ⟨[], ctors⟩ input ty :=
  inferWithTypes_accepts_iff

example (result : InferenceResult) : Expr := result.completedExpr
example (result : InferenceResult) : NodeTypeMap := result.nodeTypes
example (result : InferenceResult) : BinderSchemeMap := result.binderSchemes


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


/-! ## Universal properties: inversion / canonical-forms lemmas

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


/-! ## The composable safe pipeline

`type_safety` needs TWO independent conjuncts to hold of the runtime term: it
must be well-typed, AND all its matches must be exhaustive. These are checked
by two entirely separate mechanisms (canonical inference vs. `checkExhaustive`) over
two different representations (the erased Core term `c.erase` vs. the surface
term). Rather than fuse them into one opaque "is this program okay" boolean,
we keep them as independent checks and conjoin only the PROOFS at the return
type — a `Safe` term is a passport that carries evidence of both, so anything
downstream that only needs one of the two conjuncts can project it out
without re-deriving it. -/

/-- Erased-term well-typedness (closed): the proof-only `RunWT` judgment for
    the runnable term under its actual constructor environment. -/
def WellTyped (ctors : CtorEnv) (e : Expr) : Prop :=
  ∃ τ, RuntimeTyping.RunWT ⟨[], ctors⟩ e τ

/-- A passport: an ERASED term that passed BOTH independent checks (well-typed,
    exhaustive) and is in fact erased (`e.erase = e`, so the runtime dynamics
    applies). Anything holding a `Safe ctors` can invoke `type_safety` on it. -/
abbrev Safe (ctors : CtorEnv) :=
  { e : Expr // e.erase = e ∧ WellTyped ctors e ∧ AllMatchesExhaustive ctors e }

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

/-- Progress for a closed, exhaustive `WellTyped` term: it is a value or steps. -/
theorem WellTyped.progress {ctors : CtorEnv} {e : Expr}
    (hwt : WellTyped ctors e) (h_erased : e.erase = e) (hexh : AllMatchesExhaustive ctors e) :
    IsValue e ∨ ∃ e', Step e e' := by
  obtain ⟨τ, hty⟩ := hwt
  exact RuntimeTyping.RunWT.progress hty rfl hexh h_erased

/-- Preservation for `WellTyped`: a step of an erased term preserves
    well-typedness (the step's target is itself erased, via `Step.preserves_erased`). -/
theorem WellTyped.preservation {ctors : CtorEnv} {e e' : Expr}
    (hwt : WellTyped ctors e) (hstep : Step e e') : WellTyped ctors e' := by
  obtain ⟨τ, hty⟩ := hwt
  exact ⟨τ, RuntimeTyping.RunWT.preservation hstep hty⟩

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
          WellTyped.preservation t.property.2.1 (step_sound hs)
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



/-! ## Living axiom-budget guard

Canonical lowering, inference, erasure, principality, completeness, Core
inversions, and the erased-term runner are checked here. Complete-Core adapter
guards live in `FHM.Headlines.CompleteCore`. -/

-- Closed and clean: source-to-runtime bridge and erased-term dynamics.
#print axioms TypeOfHM.erase_preserves_typing -- expect {propext, Classical.choice, Quot.sound}
#print axioms RuntimeTyping.RunWT.progress    -- expect {propext, Classical.choice, Quot.sound}
#print axioms RuntimeTyping.RunWT.preservation -- expect {propext, Classical.choice, Quot.sound}
#print axioms TypeOfHM.type_safety_star       -- expect {propext, Classical.choice, Quot.sound}

-- Checked for all canonical constructors, including partial recursive signatures.
#print axioms lower_and_infer_sound
#print axioms Infer.sourceSound
#print axioms Infer.inputSound_source
#print axioms Infer.inputSound
#print axioms Infer.completes_source
#print axioms Infer.completes
#print axioms Infer.erase
#print axioms Infer.sound
#print axioms InferBranches.sourceSound
#print axioms InferBranches.inputSound_source
#print axioms InferBranches.completes_source
#print axioms InferBranches.erase
#print axioms inferWithTypes_source_sound
#print axioms inferWithTypes_input_sound
#print axioms inferWithTypes_erase
#print axioms Infer.principal
#print axioms Infer.complete
#print axioms inferWithTypesCore_sourceComplete
#print axioms inferWithTypesCore_complete
#print axioms inferCore_complete
#print axioms inferCore_accepts_iff
#print axioms inferCore_empty_accepts_iff
#print axioms inferWithTypes_complete
#print axioms inferWithTypes_accepts_iff
#print axioms inferWithTypes_principal

-- Clean: this file's own inversion lemmas.
#print axioms TypeOfHM_app_inv           -- expect {propext, Quot.sound}
#print axioms TypeOfHM_lambda_inv        -- expect {propext, Quot.sound}
#print axioms TypeOfHM_pair_inv          -- expect {propext, Quot.sound}
#print axioms TypeOfHM_letIn_inv         -- expect {propext, Quot.sound}

-- Closed: operational bridge (erased-dynamics lemmas proved in FHM.InferW).
#print axioms runSafe                    -- expect {propext, Classical.choice, Quot.sound}
#print axioms runSafe_running_reduces    -- expect {propext, Classical.choice, Quot.sound}


end Headlines
