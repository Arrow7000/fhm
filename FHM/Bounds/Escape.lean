import FHM.Bounds.Commit
import FHM.Bounds.Typing

/-!
# R3 — Escape classification for free count outs (API / props)

**Status:** wired on `Check` pack path via `packAtEscape`; vacuous residual
(`cons = []`) preserves today’s `packScheme?` behaviour. Residual construction
from pinned ascriptions is best-effort (`escapeResidualCons?`); full affine-app
mid-case bands are follow-up — **see design memo §5 B “R3 handoff”.**

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
    (outs : List Count) (houts : outs ≠ []) (hcons : ψ.cons = []) :
    classifyEscape k ψ outs = .vacuousGeneralise := by
  simp [classifyEscape, hcons, List.isEmpty_iff, houts]

/-- Under `uniqueOnly`, a non-unique solve witness is multi-model reject. -/
theorem classifyEscape_uniqueOnly_of_some
    {ψ : ExistsProblem} {outs : List Count} {σ : Assign}
    (hσ : solve ψ = .witness σ)
    (hcons : ψ.cons ≠ [])
    (houts : outs ≠ [])
    (hmult : unique ψ outs = .multiple ∨ unique ψ outs = .unknown) :
    classifyEscape .uniqueOnly ψ outs = .multiModelReject := by
  simp only [classifyEscape, List.isEmpty_iff, hcons, houts]
  rw [gatherNarrowingEvidence_witness_some hσ hmult]
  simp [decideCommit]

/-- Under `uniqueOnly`, unique solve witness commits. -/
theorem classifyEscape_uniqueOnly_of_unique
    {ψ : ExistsProblem} {outs : List Count} {σ : Assign}
    (hσ : solve ψ = .witness σ)
    (hu : unique ψ outs = .unique)
    (hcons : ψ.cons ≠ [])
    (houts : outs ≠ []) :
    classifyEscape .uniqueOnly ψ outs = .uniqueCommit σ := by
  simp only [classifyEscape, List.isEmpty_iff, hcons, houts]
  rw [gatherNarrowingEvidence_witness_unique hσ hu]
  simp [decideCommit]

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
  intro h
  rcases h with h | h
  · subst h
    rw [classifyEscape_vacuous_empty_outs]
    exact EscapeClassifies.vacuous_empty_outs
  · by_cases houts : outs = []
    · subst houts
      rw [classifyEscape_vacuous_empty_outs]
      exact EscapeClassifies.vacuous_empty_outs
    · rw [classifyEscape_vacuous_empty_cons k ψ outs houts h]
      exact EscapeClassifies.vacuous_empty_cons houts h

/-! ## Sub residual goals (BLSketch-style; BoundsTy) -/

mutual
/-- Interval/element Sub goals when demand `β'` accepts synth `β` (mirrors `subConstraints`). -/
def BoundsTy.subConstraints? (β' β : BoundsTy) : Option (List Constraint) :=
  match β', β with
  | .prim p, .prim q => if p == q then some [] else none
  | .bvar i, .bvar j => if i == j then some [] else none
  | .fvar i, .fvar j => if i == j then some [] else none
  | .list lo hi e, .list lo' hi' e' =>
      match BoundsTy.subConstraints? e' e with
      | none => none
      | some cs =>
        if lo == lo' && hi == hi' then
          some cs
        else if lo'.isDemandOK && hi'.isDemandOK then
          some (cs ++ [⟨lo', lo⟩, ⟨hi, hi'⟩])
        else
          none
  | .arrow a b, .arrow a' b' =>
      match BoundsTy.subConstraints? a' a, BoundsTy.subConstraints? b b' with
      | some cs₁, some cs₂ => some (cs₁ ++ cs₂)
      | _, _ => none
  | .custom n as, .custom m bs =>
      if n == m && as.length == bs.length then
        subConstraintsAll? as bs
      else
        none
  | _, _ => none
termination_by sizeOf β' + sizeOf β

def subConstraintsAll? (as bs : List BoundsTy) : Option (List Constraint) :=
  match as, bs with
  | [], [] => some []
  | a :: as, b :: bs =>
      match BoundsTy.subConstraints? a b, subConstraintsAll? as bs with
      | some cs₁, some cs₂ => some (cs₁ ++ cs₂)
      | _, _ => none
  | _, _ => none
termination_by sizeOf as + sizeOf bs
end

/-- Best-effort residual goals when pinned demand `β'` meets origin-synth `β`.
    Empty when intervals agree or demand bounds are not `DemandOK`. -/
def BoundsTy.escapeResidualCons? (β' β : BoundsTy) : List Constraint :=
  (BoundsTy.subConstraints? β' β).getD []

/-! ## Check pack path -/

/-- Classify free outs under residual goals, then pack or reject.
    Empty residual cons ⇒ vacuousGeneralise ⇒ `packScheme?` (today's behaviour).
    multiModelReject / unsatReject ⇒ `Except.error` with clear message. -/
def BoundsTy.packAtEscape (Δ : List Constraint) (β : BoundsTy)
    (residualCons : List Constraint := []) : Except String BoundBinding :=
  let outs := β.escapeOuts
  let ψ := β.escapeProblem Δ residualCons
  match classifyEscapeDefault ψ outs with
  | .vacuousGeneralise => pure (packScheme? β)
  | .uniqueCommit _ => pure (packScheme? β)
  | .multiModelReject =>
      throw "bounds: non-unique lengths on escape; add a let ascription with solid BL bounds"
  | .unsatReject =>
      throw "bounds: unsatisfiable bounds on escape"

end FHM.Bounds
