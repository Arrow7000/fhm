import FHM.Bounds.Commit
import FHM.Bounds.Typing

/-!
# R3 — Escape classification for free count outs (API / props)

**Status:** executable skeleton + theorem *statements* (proofs: fill next).
Wire residual construction + `Check` pack path after this API is green.

At **output-visible escape** (top binder β / program body β), free inferable counts
must be classified before we print or generalise them (design memo §5 F):

| Class | Residual on free outs | Dual-stack action |
|-------|----------------------|-------------------|
| **vacuous** | no free outs, or residual goals empty | `packScheme?` → `∀` OK |
| **unique** | sat + unique on outs | may commit witness `σ` |
| **multi** | sat + not unique | **`uniqueOnly` reject** + let-ascription |
| **unsat** | no witness | reject |

**Not mid-case:** join → unique range type `BL 1 3`; free interval into solid hull
`BL 3 5`; vacuous free → `∀`.

Canonical mid-case: `f : {x} BL x (2*x) α → BL x (2*x) β`, `e : BL 10 10 α`, `f e`
⇒ `5 ≤ ?x ≤ 10`, result mentions `x` → multi models for printed result.

Building residual `ExistsProblem` from dual-stack synth (affine app, exact-length
inst + band) is **follow-up**; this module defines policy on a **given** `ψ` + `outs`.
-/

namespace FHM.Bounds

/-! ## Verdicts -/

/-- Elaborator decision at escape (after residual `ψ` is known). -/
inductive EscapeVerdict where
  /-- No free outs, or residual goals empty → generalise (`packScheme?`). -/
  | vacuousGeneralise
  /-- Residual sat with unique outs; `σ` is the witness. -/
  | uniqueCommit (σ : Assign)
  /-- Residual sat but outs not unique under `uniqueOnly`. -/
  | multiModelReject
  /-- Residual unsat / unknown (no usable witness). -/
  | unsatReject

/-! ## Outs from a bounds type -/

/-- Free inferable indices of `β` as count expressions (escape outs). -/
def BoundsTy.escapeOuts (β : BoundsTy) : List Count :=
  β.freeInferables.map fun i => .var ⟨.inferable, i⟩

/-- All count slots of `β` (lo/hi spines) — BLSketch-style `obsBounds`. -/
def BoundsTy.escapeObsBounds (β : BoundsTy) : List Count :=
  β.obsBounds

/-! ## Residual exists-problem helpers -/

/-- Ambient `Δ` + residual goals `cons` over free vars.

When `cons = []`, residual is **vacuous** → generalise, not multi-model. -/
def mkEscapeProblem (Δ : List Constraint) (inferables : List Var)
    (cons : List Constraint) : ExistsProblem where
  inferables := inferables
  prem := Δ
  cons := cons

/-- Inferable vars mentioned in a count (dedup order-preserving). -/
def Count.inferVarsIn : Count → List Var
  | .lit _ | .inf => []
  | .var v => if v.kind = .inferable then [v] else []
  | .add a b | .mul a b | .min a b | .max a b =>
      let va := inferVarsIn a
      va ++ (inferVarsIn b).filter fun v => !(va.contains v)
  | .pred a => inferVarsIn a

def countsInferVars (cs : List Count) : List Var :=
  cs.foldl (fun acc c =>
    acc ++ (Count.inferVarsIn c).filter fun v => !(acc.contains v)) []

def constraintsInferVars (cs : List Constraint) : List Var :=
  countsInferVars (cs.flatMap fun c => [c.lhs, c.rhs])

/-- Escape problem from free outs of `β` and residual goals. -/
def BoundsTy.escapeProblem (β : BoundsTy) (Δ : List Constraint)
    (cons : List Constraint) : ExistsProblem :=
  let outs := β.escapeOuts
  let vs :=
    countsInferVars outs ++
      (constraintsInferVars cons).filter fun v => !(countsInferVars outs).contains v
  mkEscapeProblem Δ vs cons

/-! ## Classification (executable) -/

/-- Classify residual `ψ` with output counts `outs` under policy `k`.

* Empty `outs` or empty `ψ.cons` → `vacuousGeneralise`.
* Else gather solve+unique evidence and apply `decideCommit k`.
-/
def classifyEscape (k : PolicyKind) (ψ : ExistsProblem) (outs : List Count) :
    EscapeVerdict :=
  if outs.isEmpty then
    .vacuousGeneralise
  else if ψ.cons.isEmpty then
    .vacuousGeneralise
  else
    let e := gatherNarrowingEvidence ψ outs
    match e with
    | .none => .unsatReject
    | .unique σ _ _ =>
        match decideCommit k e with
        | .accept _ => .uniqueCommit σ
        | .reject => .unsatReject
    | .some_ σ _ =>
        match decideCommit k e with
        | .accept _ => .uniqueCommit σ
        | .reject => .multiModelReject

/-- Dual-stack default: uniqueOnly. -/
def classifyEscapeDefault (ψ : ExistsProblem) (outs : List Count) : EscapeVerdict :=
  classifyEscape .uniqueOnly ψ outs

/-! ## Declarative classification (partial; extend with evidence cases) -/

/-- Spec for vacuous branches of `classifyEscape`. Full evidence cases via theorems. -/
inductive EscapeClassifies :
    PolicyKind → ExistsProblem → List Count → EscapeVerdict → Prop where
  | vacuous_empty_outs {k ψ} :
      EscapeClassifies k ψ [] .vacuousGeneralise
  | vacuous_empty_cons {k ψ outs} :
      outs ≠ [] →
      ψ.cons = [] →
      EscapeClassifies k ψ outs .vacuousGeneralise

/-! ## Theorems -/

theorem classifyEscape_vacuous_empty_outs (k : PolicyKind) (ψ : ExistsProblem) :
    classifyEscape k ψ [] = .vacuousGeneralise := by
  simp [classifyEscape]

theorem classifyEscape_vacuous_empty_cons (k : PolicyKind) (ψ : ExistsProblem)
    (outs : List Count) (_houts : outs ≠ []) (hcons : ψ.cons = []) :
    classifyEscape k ψ outs = .vacuousGeneralise := by
  sorry

/-- Under `uniqueOnly`, a non-unique solve witness is multi-model reject. -/
theorem classifyEscape_uniqueOnly_of_some
    {ψ : ExistsProblem} {outs : List Count} {σ : Assign}
    (_hσ : solve ψ = .witness σ)
    (_hcons : ψ.cons ≠ [])
    (_houts : outs ≠ [])
    (_hmult : unique ψ outs = .multiple ∨ unique ψ outs = .unknown) :
    classifyEscape .uniqueOnly ψ outs = .multiModelReject := by
  sorry

/-- Under `uniqueOnly`, unique solve witness commits. -/
theorem classifyEscape_uniqueOnly_of_unique
    {ψ : ExistsProblem} {outs : List Count} {σ : Assign}
    (_hσ : solve ψ = .witness σ)
    (_hu : unique ψ outs = .unique)
    (_hcons : ψ.cons ≠ [])
    (_houts : outs ≠ []) :
    classifyEscape .uniqueOnly ψ outs = .uniqueCommit σ := by
  sorry

/-- `uniqueOnly` rejects non-unique evidence (`Commits` link). -/
theorem decideCommit_uniqueOnly_some_reject
    {ψ : ExistsProblem} {outs : List Count} {σ : Assign}
    (hσ : solve ψ = .witness σ) :
    decideCommit .uniqueOnly (ψ := ψ) (outs := outs) (.some_ σ hσ) = .reject := by
  rfl

theorem decideCommit_uniqueOnly_unique_accept
    {ψ : ExistsProblem} {outs : List Count} {σ : Assign}
    (hσ : solve ψ = .witness σ) (hu : unique ψ outs = .unique) :
    decideCommit .uniqueOnly (ψ := ψ) (outs := outs) (.unique σ hσ hu) = .accept σ := by
  rfl

/-- Soundness target for vacuous fragment of `EscapeClassifies`. -/
theorem classifyEscape_sound_vacuous (k : PolicyKind) (ψ : ExistsProblem)
    (outs : List Count) :
    (outs = [] ∨ ψ.cons = []) →
    EscapeClassifies k ψ outs (classifyEscape k ψ outs) := by
  sorry

/-! ## Check integration contract (not wired)

After pin/synth of a top binder β, with residual goals `cons` from mid-case sites:

```
let outs := β.escapeOuts
let ψ := β.escapeProblem Δ cons
match classifyEscapeDefault ψ outs with
| .vacuousGeneralise => packScheme? β
| .uniqueCommit σ => … apply σ …
| .multiModelReject => throw "bounds: non-unique lengths on escape; add a let ascription"
| .unsatReject => throw "bounds: unsatisfiable bounds on escape"
```

**Gap:** Check does not yet accumulate `cons` for free outs (affine app bands,
exact-length inst bands). R3 wire = produce those constraints + call classify.
-/

end FHM.Bounds
