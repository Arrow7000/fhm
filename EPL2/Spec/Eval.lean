import EPL2.Runtime

/-!
# The evaluator

`Eval.step?` computes exactly the `Eval.Step` relation, which is
deterministic, and values are exactly the expressions `isValue` accepts.
None of this mentions types.
-/

namespace EPL2
namespace Eval

/-! ## Spine facts -/

/-- The spine is its head and its arguments. -/
theorem spine_eta {A : Type} (expr : Expr A) : expr.spine = (expr.spine.1, expr.spine.2) := by
  cases expr.spine
  rfl

/-- The match in `isValue` succeeds exactly when the spine has a constant head
with few enough arguments. -/
theorem isValue_spine_iff {sig : Signature} {expr : RuntimeExpr} :
    (match expr.spine with
      | (.const c, args) =>
          match sig.valueArity c with
          | some arity => decide (args.length ≤ arity)
          | none => false
      | _ => false) = true ↔
    ∃ (c : DataConst) (args : List RuntimeExpr) (arity : Nat),
      expr.spine = (.const c, args) ∧ sig.valueArity c = some arity ∧ args.length ≤ arity := by
  obtain ⟨head, tail⟩ := expr.spine
  cases head with
  | const c => cases hv : sig.valueArity c <;> simp [hv]
  | lit l => simp
  | primOp op => simp
  | var index => simp
  | lambda p b => simp
  | app f a => simp
  | letIn ann rhs body => simp
  | fix self body => simp

/-- Every argument on a value's spine is itself a value. -/
theorem Value.mem_spine {sig : Signature} {expr : RuntimeExpr} (value : Value sig expr) :
    ∀ arg ∈ expr.spine.2, Value sig arg := by
  cases value with
  | lit => intro arg h; simp [Expr.spine] at h
  | primOp => intro arg h; simp [Expr.spine] at h
  | lambda => intro arg h; simp [Expr.spine] at h
  | primOpPartial harg =>
      intro arg h
      simp only [Expr.spine, List.nil_append, List.mem_singleton] at h
      subst h
      exact harg
  | const hspine harity hlen hall =>
      intro arg h
      rw [hspine] at h
      exact hall arg h

/-- If an application's spine is a constant spine with few enough value
arguments, the function part is itself a value. -/
theorem Value.of_app_spine {sig : Signature} {f a : RuntimeExpr} {c : DataConst}
    {args : List RuntimeExpr} {arity : Nat}
    (hspine : (Expr.app f a).spine = (.const c, args))
    (harity : sig.valueArity c = some arity) (hlen : args.length ≤ arity)
    (hall : ∀ arg ∈ args, Value sig arg) : Value sig f := by
  have h1 : f.spine.1 = .const c := by
    simpa using congrArg Prod.fst hspine
  have h2 : f.spine.2 ++ [a] = args := by
    simpa using congrArg Prod.snd hspine
  have hsp : f.spine = (.const c, f.spine.2) := by
    rw [spine_eta, h1]
  refine Value.const hsp harity ?_ ?_
  · have h := hlen
    rw [← h2] at h
    simp only [List.length_append, List.length_singleton] at h
    omega
  · intro x hx
    exact hall x (by rw [← h2]; exact List.mem_append_left _ hx)

theorem isValue_iff : isValue sig expr = true ↔ Value sig expr := by
  induction expr with
  | lit literal => simp [isValue, Value.lit]
  | primOp op => simp [isValue, Value.primOp]
  | const c =>
      simp only [isValue]
      constructor
      · intro h
        cases hv : sig.valueArity c with
        | none => simp [hv] at h
        | some arity =>
            refine Value.const (args := []) rfl hv ?_ ?_
            · simp
            · intro arg harg
              simp at harg
      · intro v
        cases v with
        | const hspine harity hlen hall =>
            simp [Expr.spine] at hspine
            obtain ⟨rfl, rfl⟩ := hspine
            simp only [Option.isSome]
            rw [harity]
  | var index =>
      simp [isValue]
      intro v
      cases v; simp [Expr.spine] at *
  | lambda param body ih => simp [isValue, Value.lambda]
  | app f a ihf iha =>
      cases f with
      | primOp op =>
          simp only [isValue]
          constructor
          · intro h
            exact Value.primOpPartial (iha.mp h)
          · intro v
            cases v with
            | primOpPartial h => exact iha.mpr h
            | const hspine _ _ _ => simp [Expr.spine] at hspine
      | const c =>
          simp only [isValue, Expr.spine]
          constructor
          · intro h
            simp only [Bool.and_eq_true] at h
            obtain ⟨⟨hsome, ha⟩, hlen⟩ := h
            cases hv : sig.valueArity c with
            | none =>
                rw [hv] at hsome
                simp at hsome
            | some arity =>
                rw [hv] at hlen
                simp at hlen
                refine Value.const (args := [a]) rfl hv ?_ ?_
                · simpa using hlen
                · intro arg harg
                  simp only [List.mem_singleton] at harg
                  subst harg
                  exact iha.mp ha
          · intro v
            cases v with
            | const hspine harity hlen hall =>
                simp [Expr.spine] at hspine
                obtain ⟨hc, hargs⟩ := hspine
                subst hc
                subst hargs
                simp [harity, iha.mpr (hall a (by simp))]
                simpa using hlen
      | app g b =>
          simp only [isValue]
          constructor
          · intro h
            simp only [Bool.and_eq_true] at h
            obtain ⟨⟨hf, ha⟩, hsp⟩ := h
            have vf := ihf.mp hf
            have va := iha.mp ha
            obtain ⟨c, args, arity, hspine, harity, hlen⟩ := isValue_spine_iff.mp hsp
            refine Value.const hspine harity hlen ?_
            intro arg harg
            have h2 : (Expr.app g b).spine.2 ++ [a] = args := by
              simpa using congrArg Prod.snd hspine
            rw [← h2] at harg
            rcases List.mem_append.mp harg with hmem | hmem
            · exact Value.mem_spine vf arg hmem
            · simp only [List.mem_singleton] at hmem
              subst hmem
              exact va
          · intro v
            cases v with
            | const hspine harity hlen hall =>
                rename_i args c arity
                have h2 : (Expr.app g b).spine.2 ++ [a] = args := by
                  simpa using congrArg Prod.snd hspine
                have ha : Value sig a := hall a (by rw [← h2]; simp)
                have vf : Value sig (Expr.app g b) :=
                  Value.of_app_spine hspine harity hlen hall
                have hspbool := (isValue_spine_iff (expr := Expr.app (Expr.app g b) a)).mpr
                  ⟨c, args, arity, hspine, harity, hlen⟩
                simp only [ihf.mpr vf, iha.mpr ha, Bool.true_and]
                exact hspbool
      | lit literal =>
          simp [isValue, Expr.spine]
          intro v
          cases v; simp [Expr.spine] at *
      | var index =>
          simp [isValue, Expr.spine]
          intro v
          cases v; simp [Expr.spine] at *
      | lambda p b =>
          simp [isValue, Expr.spine]
          intro v
          cases v; simp [Expr.spine] at *
      | letIn ann rhs body =>
          simp [isValue, Expr.spine]
          intro v
          cases v; simp [Expr.spine] at *
      | fix self body =>
          simp [isValue, Expr.spine]
          intro v
          cases v; simp [Expr.spine] at *
  | letIn ann rhs body ih =>
      simp [isValue]
      intro v
      cases v; simp [Expr.spine] at *
  | fix self body =>
      simp [isValue]
      intro v
      cases v; simp [Expr.spine] at *

/-- A saturated eliminator redex is never a value: its spine has one more
argument than `valueArity` allows. -/
theorem reduceConst_ne_of_length {sig : Signature} {c : DataConst}
    {args : List RuntimeExpr} {result : RuntimeExpr} {arity : Nat}
    (harity : sig.valueArity c = some arity) (hlen : args.length ≤ arity)
    (hred : reduceConst sig c args = some result) : False := by
  cases c with
  | ctor type index => simp [reduceConst] at hred
  | elim type =>
      cases args with
      | nil => simp [reduceConst] at hred
      | cons scrutinee branches =>
          cases hd : sig[type]? with
          | none => simp [reduceConst, hd] at hred
          | some decl =>
              by_cases hne : branches.length = decl.ctors.length
              · have harity' : decl.ctors.length = arity := by
                  simp only [Signature.valueArity] at harity
                  simpa [hd] using harity
                simp only [List.length_cons] at hlen
                omega
              · simp [reduceConst, hd, hne] at hred

theorem Value.irreducible (value : Value sig expr) : ¬ Step sig expr next := by
  intro step
  induction step with
  | beta valueArg =>
      cases value with
      | const hspine harity hlen hall => simp [Expr.spine] at hspine
  | appFunction step ih =>
      cases value with
      | primOpPartial h => cases step
      | const hspine harity hlen hall =>
          exact ih (Value.of_app_spine hspine harity hlen hall)
  | appArgument valueFunction step ih =>
      rename_i function argument argument'
      cases value with
      | primOpPartial h => exact ih h
      | const hspine harity hlen hall =>
          rename_i args c arity
          have h2 : function.spine.2 ++ [argument] = args := by
            simpa using congrArg Prod.snd hspine
          exact ih (hall argument (by rw [← h2]; simp))
  | primOp h =>
      cases value with
      | const hspine harity hlen hall => simp [Expr.spine] at hspine
  | const hspine' hall' hred =>
      cases value with
      | primOpPartial h => simp [Expr.spine] at hspine'
      | const hspine harity hlen hall =>
          rw [hspine] at hspine'
          obtain ⟨rfl, rfl⟩ := hspine'
          exact reduceConst_ne_of_length harity hlen hred
  | letRhs step ih =>
      cases value with
      | const hspine harity hlen hall => simp [Expr.spine] at hspine
  | letValue h =>
      cases value with
      | const hspine harity hlen hall => simp [Expr.spine] at hspine
  | fixUnfold =>
      cases value with
      | const hspine harity hlen hall => simp [Expr.spine] at hspine

/-- Contracting an application of two values is a step. -/
theorem reduceApp_sound {sig : Signature} {f a next : RuntimeExpr}
    (h : reduceApp sig f a = some next) (hf : Value sig f) (ha : Value sig a) :
    Step sig (.app f a) next := by
  simp only [reduceApp] at h
  split at h
  · injection h with hnext
    subst hnext
    exact Step.beta ha
  · exact Step.primOp h
  · split at h
    · rename_i c args heq
      refine Step.const heq ?_ h
      intro arg harg
      have h2 : f.spine.2 ++ [a] = args := by simpa using congrArg Prod.snd heq
      rw [← h2] at harg
      rcases List.mem_append.mp harg with hmem | hmem
      · exact Value.mem_spine hf arg hmem
      · simp only [List.mem_singleton] at hmem
        subst hmem
        exact ha
    · simp at h

theorem step?_sound (found : step? sig expr = some next) : Step sig expr next := by
  induction expr generalizing next with
  | lit literal => simp [step?] at found
  | primOp op => simp [step?] at found
  | const c => simp [step?] at found
  | var index => simp [step?] at found
  | lambda p b => simp [step?] at found
  | letIn ann rhs body ih =>
      simp only [step?] at found
      split at found
      · rename_i rhs' hstep
        injection found with hnext
        subst hnext
        exact Step.letRhs (ih (next := rhs') hstep)
      · split at found
        · rename_i hval
          injection found with hnext
          subst hnext
          exact Step.letValue (isValue_iff.mp hval)
        · simp at found
  | fix self body =>
      simp only [step?] at found
      injection found with hnext
      subst hnext
      exact Step.fixUnfold
  | app f a ihf iha =>
      simp only [step?] at found
      split at found
      · rename_i f' hstepf
        injection found with hnext
        subst hnext
        exact Step.appFunction (ihf (next := f') hstepf)
      · split at found
        · rename_i hval
          split at found
          · rename_i a' hstepa
            injection found with hnext
            subst hnext
            exact Step.appArgument (isValue_iff.mp hval) (iha (next := a') hstepa)
          · split at found
            · rename_i hvala
              exact reduceApp_sound found (isValue_iff.mp hval) (isValue_iff.mp hvala)
            · simp at found
        · simp at found

/-- Facts about the argument list of a successful `reduceConst`: it is a
nonempty eliminator spine whose tail has exactly the eliminator's arity. -/
theorem reduceConst_some_valueArity {sig : Signature} {c : DataConst}
    {args : List RuntimeExpr} {result : RuntimeExpr}
    (hred : reduceConst sig c args = some result) :
    ∃ arity : Nat, sig.valueArity c = some arity ∧
      ∃ first rest, args = first :: rest ∧ rest.length = arity := by
  cases c with
  | ctor type index => simp [reduceConst] at hred
  | elim type =>
      cases args with
      | nil => simp [reduceConst] at hred
      | cons scrutinee branches =>
          cases hd : sig[type]? with
          | none => simp [reduceConst, hd] at hred
          | some decl =>
              by_cases hne : branches.length = decl.ctors.length
              · refine ⟨decl.ctors.length, ?_, scrutinee, branches, rfl, hne⟩
                simp [Signature.valueArity, hd]
              · simp [reduceConst, hd, hne] at hred

/-- `reduceApp` contracts a constant spine. -/
theorem reduceApp_of_spine_const {sig : Signature} {f a : RuntimeExpr}
    {c : DataConst} {args : List RuntimeExpr} {result : RuntimeExpr}
    (hspine : (Expr.app f a).spine = (.const c, args))
    (hred : reduceConst sig c args = some result) :
    reduceApp sig f a = some result := by
  simp only [reduceApp]
  split
  · simp [Expr.spine] at hspine
  · simp [Expr.spine] at hspine
  · rw [hspine]
    exact hred

/-- Values do not step. -/
theorem step?_none_of_value {sig : Signature} {expr : RuntimeExpr} (value : Value sig expr) :
    step? sig expr = none := by
  cases h : step? sig expr with
  | none => rfl
  | some next => exact absurd (step?_sound h) (Value.irreducible value)

theorem step?_complete (step : Step sig expr next) : step? sig expr = some next := by
  induction step with
  | beta valueArg =>
      rename_i arg p b
      rw [step?]
      rw [step?_none_of_value (Value.lambda (param := p) (body := b))]
      rw [if_pos (isValue_iff.mpr (Value.lambda (param := p) (body := b)))]
      rw [step?_none_of_value valueArg]
      rw [if_pos (isValue_iff.mpr valueArg)]
      simp [reduceApp]
  | appFunction hstep ih =>
      rw [step?]
      rw [ih]
  | appArgument valueFunction hstep ih =>
      rw [step?]
      rw [step?_none_of_value valueFunction]
      rw [if_pos (isValue_iff.mpr valueFunction)]
      rw [ih]
  | primOp h =>
      rename_i result op left right
      have inner : Value sig (.app (.primOp op) (.lit left)) := Value.primOpPartial Value.lit
      rw [step?]
      rw [step?_none_of_value inner]
      rw [if_pos (isValue_iff.mpr inner)]
      rw [step?_none_of_value (Value.lit (literal := right))]
      rw [if_pos (isValue_iff.mpr (Value.lit (literal := right)))]
      simp [reduceApp, h]
  | const hspine hall hred =>
      rename_i f a args c result
      obtain ⟨arity, harity, first, rest, hargs, hrest⟩ := reduceConst_some_valueArity hred
      have h2 : f.spine.2 ++ [a] = args := by simpa using congrArg Prod.snd hspine
      have h1 : f.spine.1 = .const c := by simpa using congrArg Prod.fst hspine
      have vf : Value sig f := by
        refine Value.const (args := f.spine.2) ?_ harity ?_ ?_
        · rw [show f.spine = (f.spine.1, f.spine.2) from by cases f.spine; rfl, h1]
        · have hlen := congrArg List.length h2
          rw [hargs] at hlen
          simp only [List.length_append, List.length_cons] at hlen
          omega
        · intro x hx
          exact hall x (by rw [← h2]; exact List.mem_append_left _ hx)
      have va : Value sig a := hall a (by rw [← h2]; simp)
      rw [step?]
      rw [step?_none_of_value vf]
      rw [if_pos (isValue_iff.mpr vf)]
      rw [step?_none_of_value va]
      rw [if_pos (isValue_iff.mpr va)]
      exact reduceApp_of_spine_const hspine hred
  | letRhs hstep ih =>
      rw [step?]
      rw [ih]
  | letValue h =>
      rw [step?]
      rw [step?_none_of_value h]
      rw [if_pos (isValue_iff.mpr h)]
  | fixUnfold =>
      rw [step?]

theorem Step.deterministic (first : Step sig expr a) (second : Step sig expr b) : a = b := by
  have h1 := step?_complete first
  have h2 := step?_complete second
  rw [h1] at h2
  exact Option.some.inj h2

theorem run_steps (fuel : Nat) (expr : RuntimeExpr) : Steps sig expr (run sig fuel expr) := by
  induction fuel generalizing expr with
  | zero => exact Relation.ReflTransGen.refl
  | succ fuel ih =>
      rw [run]
      cases h : step? sig expr with
      | none => exact Relation.ReflTransGen.refl
      | some next => exact Relation.ReflTransGen.head (step?_sound h) (ih next)

/-- Every terminating execution is found by `run` with enough fuel. -/
theorem run_complete (steps : Steps sig expr result) (value : Value sig result) :
    ∃ fuel, run sig fuel expr = result := by
  have _h := value
  induction steps using Relation.ReflTransGen.head_induction_on with
  | refl => exact ⟨0, rfl⟩
  | head hstep hrest ih =>
      obtain ⟨fuel, hfuel⟩ := ih
      refine ⟨fuel + 1, ?_⟩
      rw [run, step?_complete hstep]
      exact hfuel

end Eval
end EPL2
