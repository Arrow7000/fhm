import EPL.Runtime

/-!
# The evaluator

`Eval.step?` computes exactly the `Eval.Step` relation, which is
deterministic, and values are exactly the expressions `isValue` accepts.
None of this mentions types.
-/

namespace EPL
namespace Eval

/-! ## Spine facts -/

/-- The spine is its head and its arguments. -/
private theorem spine_eta {A : Type} (expr : Expr A) : expr.spine = (expr.spine.1, expr.spine.2) := by
  cases expr.spine
  rfl

/-- Every argument on a value's spine is itself a value. -/
private theorem Value.mem_spine {expr : RuntimeExpr} (value : Value expr) :
    ∀ arg ∈ expr.spine.2, Value arg := by
  cases value with
  | lit => intro arg h; simp [Expr.spine] at h
  | primOp => intro arg h; simp [Expr.spine] at h
  | lambda => intro arg h; simp [Expr.spine] at h
  | primOpPartial harg =>
      intro arg h
      simp only [Expr.spine, List.nil_append, List.mem_singleton] at h
      subst h
      exact harg
  | ctor hspine hall =>
      intro arg h
      rw [hspine] at h
      exact hall arg h

/-- The fields of an application's constructor spine are the arguments of the
function's spine together with the argument. -/
private theorem mem_spine_app {f a arg : RuntimeExpr} {ref : CtorRef} {fields : List RuntimeExpr}
    (hspine : (Expr.app f a).spine = (.ctor ref, fields)) :
    arg ∈ fields ↔ arg ∈ f.spine.2 ∨ arg = a := by
  have hsnd : f.spine.2 ++ [a] = fields := by simpa using congrArg Prod.snd hspine
  rw [← hsnd, List.mem_append, List.mem_singleton]

/-- If an application's spine is a constructor spine whose fields are values,
the function part is itself a value. -/
private theorem Value.of_app_spine {f a : RuntimeExpr} {ref : CtorRef} {fields : List RuntimeExpr}
    (hspine : (Expr.app f a).spine = (.ctor ref, fields))
    (hall : ∀ field ∈ fields, Value field) : Value f := by
  have hfst : f.spine.1 = .ctor ref := by simpa using congrArg Prod.fst hspine
  have hsnd : f.spine.2 ++ [a] = fields := by simpa using congrArg Prod.snd hspine
  refine Value.ctor (fields := f.spine.2) (ref := ref) ?_ ?_
  · rw [spine_eta, hfst]
  · intro field hfield
    exact hall field (by rw [← hsnd]; exact List.mem_append_left _ hfield)

/-- An application of a constructor-spined value to a value is a value. -/
private theorem Value.of_app_ctor {f a : RuntimeExpr} {ref : CtorRef}
    (hf : Value f) (ha : Value a) (hfst : f.spine.1 = .ctor ref) : Value (.app f a) := by
  have hspine : (Expr.app f a).spine = (.ctor ref, f.spine.2 ++ [a]) := by
    rw [spine_eta]
    show (f.spine.1, f.spine.2 ++ [a]) = (.ctor ref, f.spine.2 ++ [a])
    rw [hfst]
  refine Value.ctor hspine ?_
  intro field hfield
  rcases List.mem_append.mp hfield with hfield | hfield
  · exact Value.mem_spine hf field hfield
  · rw [List.mem_singleton] at hfield
    subst hfield
    exact ha

/-- An application whose constructor spine is known passes the `isValue` check
as soon as its two parts do. -/
private theorem isValue_app_of_spine {f a : RuntimeExpr} {ref : CtorRef} {fields : List RuntimeExpr}
    (hspine : (Expr.app f a).spine = (.ctor ref, fields))
    (hf : isValue f = true) (ha : isValue a = true) : isValue (.app f a) = true := by
  have hfst : f.spine.1 = .ctor ref := by simpa using congrArg Prod.fst hspine
  cases f with
  | primOp op => simp [Expr.spine] at hfst
  | lit l => simp [Expr.spine] at hfst
  | var i => simp [Expr.spine] at hfst
  | lambda param body => simp [Expr.spine] at hfst
  | letIn ann rhs body => simp [Expr.spine] at hfst
  | fix self body => simp [Expr.spine] at hfst
  | «match» scrutinee branches => simp [Expr.spine] at hfst
  | ctor c => simp [isValue, Expr.spine, ha]
  | app g b => simp [isValue, hf, ha, hfst]

/-- Values pass the `isValue` check. -/
private theorem isValue_of_value {expr : RuntimeExpr} (value : Value expr) : isValue expr = true := by
  induction expr using Expr.induction with
  | lit _ =>
      cases value with
      | lit => rfl
      | ctor hspine _ => simp [Expr.spine] at hspine
  | primOp _ =>
      cases value with
      | primOp => rfl
      | ctor hspine _ => simp [Expr.spine] at hspine
  | ctor _ =>
      cases value with
      | ctor _ _ => rfl
  | var _ =>
      cases value with
      | ctor hspine _ => simp [Expr.spine] at hspine
  | lambda _ _ =>
      cases value with
      | lambda => rfl
      | ctor hspine _ => simp [Expr.spine] at hspine
  | letIn _ _ _ =>
      cases value with
      | ctor hspine _ => simp [Expr.spine] at hspine
  | fix _ _ =>
      cases value with
      | ctor hspine _ => simp [Expr.spine] at hspine
  | «match» _ _ =>
      cases value with
      | ctor hspine _ => simp [Expr.spine] at hspine
  | app f a ihf iha =>
      cases value with
      | primOpPartial h => simp [isValue, iha h]
      | ctor hspine hall =>
          have ha : Value a := hall a ((mem_spine_app hspine).mpr (Or.inr rfl))
          cases hf : f with
          | primOp op =>
              subst hf
              simp [Expr.spine] at hspine
          | lit l =>
              subst hf
              simp [Expr.spine] at hspine
          | var i =>
              subst hf
              simp [Expr.spine] at hspine
          | lambda param body =>
              subst hf
              simp [Expr.spine] at hspine
          | letIn ann rhs body =>
              subst hf
              simp [Expr.spine] at hspine
          | fix self body =>
              subst hf
              simp [Expr.spine] at hspine
          | «match» scrutinee branches =>
              subst hf
              simp [Expr.spine] at hspine
          | ctor ctorRef =>
              subst hf
              simp [isValue, Expr.spine, iha ha]
          | app g b =>
              subst hf
              have vf : Value (Expr.app g b) := Value.of_app_spine hspine hall
              exact isValue_app_of_spine hspine (ihf vf) (iha ha)

theorem isValue_iff : isValue expr = true ↔ Value expr := by
  constructor
  · intro h
    induction expr using Expr.induction with
    | lit _ => exact .lit
    | primOp _ => exact .primOp
    | ctor _ => exact .ctor rfl (by intro field hfield; simp at hfield)
    | var _ => simp [isValue] at h
    | lambda _ _ => exact .lambda
    | letIn _ _ _ => simp [isValue] at h
    | fix _ _ => simp [isValue] at h
    | «match» _ _ => simp [isValue] at h
    | app f a ihf iha =>
        cases hf : f with
        | primOp op =>
            subst hf
            simp only [isValue] at h
            exact .primOpPartial (iha h)
        | lit l =>
            subst hf
            simp [isValue, Expr.spine] at h
        | var i =>
            subst hf
            simp [isValue, Expr.spine] at h
        | lambda param body =>
            subst hf
            simp [isValue, Expr.spine] at h
        | letIn ann rhs body =>
            subst hf
            simp [isValue, Expr.spine] at h
        | fix self body =>
            subst hf
            simp [isValue, Expr.spine] at h
        | «match» scrutinee branches =>
            subst hf
            simp [isValue, Expr.spine] at h
        | ctor ref =>
            subst hf
            simp [isValue, Expr.spine] at h
            exact Value.of_app_ctor (.ctor rfl (by intro field hfield; simp at hfield))
              (iha h) rfl
        | app g b =>
            subst hf
            simp only [isValue, Bool.and_eq_true] at h
            obtain ⟨⟨hvf, hva⟩, hsp⟩ := h
            cases hs : (Expr.app g b).spine.1 with
            | ctor ref =>
                exact Value.of_app_ctor (ihf hvf) (iha hva) hs
            | lit l => simp [hs] at hsp
            | primOp op => simp [hs] at hsp
            | var i => simp [hs] at hsp
            | lambda param body => simp [hs] at hsp
            | app x y => simp [hs] at hsp
            | letIn ann rhs body => simp [hs] at hsp
            | fix self body => simp [hs] at hsp
            | «match» scrutinee branches => simp [hs] at hsp
  · exact isValue_of_value

/-- A successful `reduceMatch` is the scrutinee's constructor case applied to
its fields. -/
private theorem reduceMatch_some {scrutinee result : RuntimeExpr}
    {branches : List (CtorRef × RuntimeExpr)}
    (found : reduceMatch scrutinee branches = some result) :
    ∃ (ref : CtorRef) (fields : List RuntimeExpr) (body : RuntimeExpr),
      scrutinee.spine = (.ctor ref, fields) ∧
        Expr.findBranch ref branches = some body ∧ result = Expr.apps body fields := by
  unfold reduceMatch at found
  split at found
  · rename_i ref fields hspine
    cases hfind : Expr.findBranch ref branches with
    | none => simp [hfind] at found
    | some body =>
        simp only [hfind, Option.map_some, Option.some.injEq] at found
        exact ⟨ref, fields, body, hspine, hfind, found.symm⟩
  · simp at found

/-- A constructor scrutinee with a branch reduces to that branch applied to the
scrutinee's fields. -/
private theorem reduceMatch_eq_some {scrutinee : RuntimeExpr}
    {branches : List (CtorRef × RuntimeExpr)} {ref : CtorRef} {fields : List RuntimeExpr}
    {body : RuntimeExpr} (hspine : scrutinee.spine = (.ctor ref, fields))
    (hfind : Expr.findBranch ref branches = some body) :
    reduceMatch scrutinee branches = some (Expr.apps body fields) := by
  simp [reduceMatch, hspine, hfind]

/-- Contracting an application of two values is a step. -/
private theorem reduceApp_sound {f a next : RuntimeExpr} (found : reduceApp f a = some next)
    (hf : Value f) (ha : Value a) : Step (.app f a) next := by
  simp only [reduceApp] at found
  split at found
  · injection found with found
    rw [← found]
    exact .beta ha
  · exact .primOp found
  · simp at found

/-- Values do not step. -/
theorem Value.irreducible (value : Value expr) : ¬ Step expr next := by
  intro step
  induction step with
  | beta argument =>
      cases value with
      | ctor hspine _ => simp [Expr.spine] at hspine
  | appFunction step ih =>
      cases value with
      | primOpPartial _ => cases step
      | ctor hspine hall => exact ih (Value.of_app_spine hspine hall)
  | appArgument functionValue step ih =>
      cases value with
      | primOpPartial h => exact ih h
      | ctor hspine hall =>
          exact ih (hall _ ((mem_spine_app hspine).mpr (Or.inr rfl)))
  | primOp h =>
      cases value with
      | ctor hspine _ => simp [Expr.spine] at hspine
  | matchScrutinee step ih =>
      cases value with
      | ctor hspine _ => simp [Expr.spine] at hspine
  | matchCtor scrutineeValue hspine hfind =>
      cases value with
      | ctor hspine' _ => simp [Expr.spine] at hspine'
  | letRhs step ih =>
      cases value with
      | ctor hspine _ => simp [Expr.spine] at hspine
  | letValue h =>
      cases value with
      | ctor hspine _ => simp [Expr.spine] at hspine
  | fixUnfold =>
      cases value with
      | ctor hspine _ => simp [Expr.spine] at hspine

theorem step?_sound (found : step? expr = some next) : Step expr next := by
  induction expr using Expr.induction generalizing next with
  | lit _ | primOp _ | ctor _ | var _ | lambda _ _ => simp [step?] at found
  | letIn ann rhs body ihr ihb =>
      simp only [step?] at found
      split at found
      · rename_i rhs' hstep
        cases found
        exact .letRhs (ihr hstep)
      · split at found
        · rename_i hval
          cases found
          exact .letValue (isValue_iff.mp hval)
        · simp at found
  | fix self body ih =>
      simp only [step?] at found
      cases found
      exact Step.fixUnfold
  | app f a ihf iha =>
      simp only [step?] at found
      split at found
      · rename_i f' hstepf
        cases found
        exact .appFunction (ihf hstepf)
      · split at found
        · rename_i hval
          split at found
          · rename_i a' hstepa
            cases found
            exact .appArgument (isValue_iff.mp hval) (iha hstepa)
          · split at found
            · rename_i hvala
              exact reduceApp_sound found (isValue_iff.mp hval) (isValue_iff.mp hvala)
            · simp at found
        · simp at found
  | «match» scrutinee branches ih ihs =>
      simp only [step?] at found
      split at found
      · rename_i scrutinee' hstep
        cases found
        exact .matchScrutinee (ih hstep)
      · split at found
        · rename_i hval
          obtain ⟨ref, fields, body, hspine, hfind, rfl⟩ := reduceMatch_some found
          exact .matchCtor (isValue_iff.mp hval) hspine hfind
        · simp at found

/-- Values do not step. -/
theorem step?_none_of_value {expr : RuntimeExpr} (value : Value expr) : step? expr = none := by
  cases h : step? expr with
  | none => rfl
  | some next => exact absurd (step?_sound h) (Value.irreducible value)

theorem step?_complete (step : Step expr next) : step? expr = some next := by
  induction step with
  | beta valueArg =>
      simp [isValue, step?, reduceApp, step?_none_of_value valueArg, isValue_iff.mpr valueArg]
  | appFunction hstep ih =>
      simp [step?, ih]
  | appArgument valueFunction hstep ih =>
      simp [step?, step?_none_of_value valueFunction, isValue_iff.mpr valueFunction, ih]
  | primOp h =>
      simp [isValue, step?, reduceApp, h]
  | matchScrutinee hstep ih =>
      simp [step?, ih]
  | matchCtor value hspine hfind =>
      simp [step?, step?_none_of_value value, isValue_iff.mpr value,
        reduceMatch_eq_some hspine hfind]
  | letRhs hstep ih =>
      simp [step?, ih]
  | letValue h =>
      simp [step?, step?_none_of_value h, isValue_iff.mpr h]
  | fixUnfold =>
      simp [step?]

theorem Step.deterministic (first : Step expr a) (second : Step expr b) : a = b := by
  have := step?_complete second
  rw [step?_complete first] at this
  exact Option.some.inj this

theorem run_steps (fuel : Nat) (expr : RuntimeExpr) : Steps expr (run fuel expr) := by
  induction fuel generalizing expr with
  | zero => exact Relation.ReflTransGen.refl
  | succ fuel ih =>
      rw [run]
      cases h : step? expr with
      | none => exact Relation.ReflTransGen.refl
      | some next => exact Relation.ReflTransGen.head (step?_sound h) (ih next)

/-- `run` stays at a value. -/
theorem run_value (value : Value expr) (fuel : Nat) : run fuel expr = expr := by
  cases fuel with
  | zero => rfl
  | succ fuel => rw [run, step?_none_of_value value]

/-- Every execution reaching a value is found by `run` with enough fuel, and
with any larger fuel. -/
theorem run_complete (steps : Steps expr result) (value : Value result) :
    ∃ fuel, ∀ extra, run (fuel + extra) expr = result := by
  induction steps using Relation.ReflTransGen.head_induction_on with
  | refl => exact ⟨0, fun extra => by rw [Nat.zero_add, run_value value]⟩
  | head step _ ih =>
      obtain ⟨fuel, found⟩ := ih
      refine ⟨fuel + 1, fun extra => ?_⟩
      rw [Nat.add_right_comm, run, step?_complete step]
      exact found extra

end Eval
end EPL
