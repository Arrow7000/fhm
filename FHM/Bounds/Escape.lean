import FHM.Bounds.Commit
import FHM.Bounds.Typing

/-!
# R3 — Escape classification for free count outs

**Status:** classifier + `packAtEscape` on Check binder pack. Mid-case needs a
**non-empty residual** from Synth app/inst meet (`Synth.meetForApp`); empty
`cons` ⇒ always `vacuousGeneralise` ⇒ same as bare `packScheme?`.

**Prop-first:** `EscapeClassifies` is the full declarative north-star for escape
verdicts (vacuous + evidence under policy). `classifyEscape` is proved sound and
complete against it (`classifyEscape_iff`).

At **output-visible escape** (binder pack), free inferable counts are classified
before generalise/print (design memo §5 F):

| Class | Residual on free outs | Dual-stack action |
|-------|----------------------|-------------------|
| **vacuous** | no free outs, or residual goals empty | `packScheme?` → `∀` OK |
| **unique** | sat + unique on outs | commit witness `σ` into β, then pack |
| **multi** | sat + not unique | **`uniqueOnly` reject** + let-ascription |
| **unsat** | no witness | reject |

**Not mid-case:** join → unique range type `BL 1 3`; free interval into solid hull
`BL 3 5`; vacuous free → `∀`.

Canonical mid-case: `f : {x} BL x (2*x) α → BL x (2*x) β`, `e : BL 10 10 α`, `f e`
⇒ residual `5 ≤ ?x ≤ 10`, result mentions `x` → multi → reject at pack.
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

/-! ## Declarative classification (north-star spec)

`EscapeClassifies` is the full prop-level story for escape under a `PolicyKind`.
Executable `classifyEscape` is defined to match it; soundness/completeness below.
-/

/-- How `decideCommit` on non-vacuous evidence becomes an `EscapeVerdict`. -/
inductive EscapeVerdictOf :
    PolicyKind → {ψ : ExistsProblem} → {outs : List Count} →
      NarrowingEvidence ψ outs → EscapeVerdict → Prop where
  | unsat {k ψ outs} :
      EscapeVerdictOf k (ψ := ψ) (outs := outs) .none .unsatReject
  | unique_accept {k ψ outs σ hσ hu} :
      decideCommit k (ψ := ψ) (outs := outs) (.unique σ hσ hu) = .accept σ →
      EscapeVerdictOf k (ψ := ψ) (outs := outs) (.unique σ hσ hu) (.uniqueCommit σ)
  | unique_reject {k ψ outs σ hσ hu} :
      decideCommit k (ψ := ψ) (outs := outs) (.unique σ hσ hu) = .reject →
      EscapeVerdictOf k (ψ := ψ) (outs := outs) (.unique σ hσ hu) .unsatReject
  | some_accept {k ψ outs σ hσ} :
      decideCommit k (ψ := ψ) (outs := outs) (.some_ σ hσ) = .accept σ →
      EscapeVerdictOf k (ψ := ψ) (outs := outs) (.some_ σ hσ) (.uniqueCommit σ)
  | some_reject {k ψ outs σ hσ} :
      decideCommit k (ψ := ψ) (outs := outs) (.some_ σ hσ) = .reject →
      EscapeVerdictOf k (ψ := ψ) (outs := outs) (.some_ σ hσ) .multiModelReject

/-- Full escape classification spec (vacuous + evidence under policy). -/
inductive EscapeClassifies :
    PolicyKind → ExistsProblem → List Count → EscapeVerdict → Prop where
  | vacuous_empty_outs {k ψ} :
      EscapeClassifies k ψ [] .vacuousGeneralise
  | vacuous_empty_cons {k ψ outs} :
      outs ≠ [] →
      ψ.cons = [] →
      EscapeClassifies k ψ outs .vacuousGeneralise
  | of_evidence {k ψ outs e v} :
      outs ≠ [] →
      ψ.cons ≠ [] →
      e = gatherNarrowingEvidence ψ outs →
      EscapeVerdictOf k (ψ := ψ) (outs := outs) e v →
      EscapeClassifies k ψ outs v

/-! ## Theorems: executable ↔ spec -/

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

/-- Soundness: executable verdict always matches the declarative spec. -/
theorem classifyEscape_sound (k : PolicyKind) (ψ : ExistsProblem) (outs : List Count) :
    EscapeClassifies k ψ outs (classifyEscape k ψ outs) := by
  by_cases houts : outs = []
  · subst houts
    simp only [classifyEscape]
    exact .vacuous_empty_outs
  · by_cases hcons : ψ.cons = []
    · simp only [classifyEscape, List.isEmpty_iff, houts, hcons]
      exact .vacuous_empty_cons houts hcons
    · simp only [classifyEscape, List.isEmpty_iff, houts, hcons]
      -- Non-vacuous: case on oracle evidence.
      cases he : gatherNarrowingEvidence ψ outs with
      | none =>
          exact .of_evidence houts hcons he.symm .unsat
      | unique σ hσ hu =>
          -- `decideCommit` always accepts unique evidence.
          have hdec : decideCommit k (ψ := ψ) (outs := outs) (.unique σ hσ hu) = .accept σ := by
            cases k <;> rfl
          simp only [hdec]
          exact .of_evidence houts hcons he.symm (.unique_accept hdec)
      | some_ σ hσ =>
          cases k with
          | uniqueOnly =>
              have hdec :
                  decideCommit .uniqueOnly (ψ := ψ) (outs := outs) (.some_ σ hσ) = .reject := rfl
              simp only [decideCommit]
              exact .of_evidence houts hcons he.symm (.some_reject hdec)
          | anyWitness =>
              have hdec :
                  decideCommit .anyWitness (ψ := ψ) (outs := outs) (.some_ σ hσ) = .accept σ := rfl
              simp only [decideCommit]
              exact .of_evidence houts hcons he.symm (.some_accept hdec)

/-- Completeness: any declarative classification is realized by `classifyEscape`. -/
theorem classifyEscape_complete {k ψ outs v}
    (h : EscapeClassifies k ψ outs v) :
    classifyEscape k ψ outs = v := by
  cases h with
  | vacuous_empty_outs =>
      simp [classifyEscape]
  | vacuous_empty_cons houts hcons =>
      simp [classifyEscape, List.isEmpty_iff, houts, hcons]
  | of_evidence houts hcons he hvo =>
      simp only [classifyEscape, List.isEmpty_iff, houts, hcons]
      rw [← he]
      cases hvo with
      | unsat => rfl
      | unique_accept hdec => simp [hdec]
      | unique_reject hdec => simp [hdec]
      | some_accept hdec => simp [hdec]
      | some_reject hdec => simp [hdec]

theorem classifyEscape_iff (k : PolicyKind) (ψ : ExistsProblem) (outs : List Count)
    (v : EscapeVerdict) :
    EscapeClassifies k ψ outs v ↔ classifyEscape k ψ outs = v :=
  ⟨classifyEscape_complete, fun h => h ▸ classifyEscape_sound k ψ outs⟩

/-! ## Sub residual goals (BLSketch `subtypeProblem` style) -/

/-- Ground inferable slots of `β` under assignment `σ` (unique-commit path). -/
def Count.applyAssign (σ : Assign) : Count → Count
  | .lit n => .lit n
  | .inf => .inf
  | .var ⟨.inferable, i⟩ => .lit (σ ⟨.inferable, i⟩)
  | .var v => .var v
  | .add a b => .add (applyAssign σ a) (applyAssign σ b)
  | .mul a b => .mul (applyAssign σ a) (applyAssign σ b)
  | .pred a => .pred (applyAssign σ a)
  | .min a b => .min (applyAssign σ a) (applyAssign σ b)
  | .max a b => .max (applyAssign σ a) (applyAssign σ b)

def BoundsTy.applyAssign (σ : Assign) : BoundsTy → BoundsTy
  | .prim p => .prim p
  | .bvar i => .bvar i
  | .fvar i => .fvar i
  | .arrow d c => .arrow (applyAssign σ d) (applyAssign σ c)
  | .list lo hi e =>
      .list (Count.applyAssign σ lo) (Count.applyAssign σ hi) (applyAssign σ e)
  | .custom n as => .custom n (as.map (applyAssign σ))

mutual
/-- Exists-style Sub goals: demand `want` accepts synth `got`.

Mirrors `Interval.subGoals` on list endpoints:
`want.lo ≤ got.lo` and `got.hi ≤ want.hi` when endpoints differ and demand is
`DemandOK`. Element/arrow walk is the same polarity as `checkSub` (got <: want).

`none` = shape mismatch; `some []` = equal / no residual goals. -/
def BoundsTy.subConstraints? (want got : BoundsTy) : Option (List Constraint) :=
  match want, got with
  | .prim p, .prim q => if p == q then some [] else none
  | .bvar i, .bvar j => if i == j then some [] else none
  | .fvar i, .fvar j => if i == j then some [] else none
  -- HM erase stubs (fvar/bvar) soft-match like `checkSubInst` — no residual goals.
  | .fvar _, _ => some []
  | .bvar _, _ => some []
  | _, .fvar _ => some []
  | _, .bvar _ => some []
  | .list wlo whi we, .list glo ghi ge =>
      match BoundsTy.subConstraints? we ge with
      | none => none
      | some cs =>
        if wlo == glo && whi == ghi then
          some cs
        else if wlo.isDemandOK && whi.isDemandOK then
          -- Same inequalities as `Interval.subGoals Δ ⟨glo,ghi⟩ ⟨wlo,whi⟩`.
          some (cs ++ [⟨wlo, glo⟩, ⟨ghi, whi⟩])
        else
          none
  | .arrow wd wc, .arrow gd gc =>
      -- Arrow Sub: want.dom <: got.dom (contravariant) and got.cod <: want.cod.
      match BoundsTy.subConstraints? gd wd, BoundsTy.subConstraints? wc gc with
      | some cs₁, some cs₂ => some (cs₁ ++ cs₂)
      | _, _ => none
  | .custom n as, .custom m bs =>
      if n == m && as.length == bs.length then
        subConstraintsAll? as bs
      else
        none
  | _, _ => none
termination_by sizeOf want + sizeOf got

def subConstraintsAll? (wants gots : List BoundsTy) : Option (List Constraint) :=
  match wants, gots with
  | [], [] => some []
  | w :: ws, g :: gs =>
      match BoundsTy.subConstraints? w g, subConstraintsAll? ws gs with
      | some cs₁, some cs₂ => some (cs₁ ++ cs₂)
      | _, _ => none
  | _, _ => none
termination_by sizeOf wants + sizeOf gots
end

/-- Residual goals when demand `want` meets synth `got` (`[]` if unavailable). -/
def BoundsTy.escapeResidualCons? (want got : BoundsTy) : List Constraint :=
  (BoundsTy.subConstraints? want got).getD []

/-! ## Check pack path -/

/-- Classify free outs under residual goals, then pack or reject.
    Empty residual cons ⇒ vacuousGeneralise ⇒ `packScheme?`.
    multiModelReject / unsatReject ⇒ clear product error. -/
def BoundsTy.packAtEscape (Δ : List Constraint) (β : BoundsTy)
    (residualCons : List Constraint := []) : Except String BoundBinding :=
  let outs := β.escapeOuts
  let ψ := β.escapeProblem Δ residualCons
  match classifyEscapeDefault ψ outs with
  | .vacuousGeneralise => pure (packScheme? β)
  | .uniqueCommit σ => pure (packScheme? (β.applyAssign σ))
  | .multiModelReject =>
      throw "bounds: non-unique lengths on escape; add a let ascription with solid BL bounds"
  | .unsatReject =>
      throw "bounds: unsatisfiable bounds on escape"

end FHM.Bounds
