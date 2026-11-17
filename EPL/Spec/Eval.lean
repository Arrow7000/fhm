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
  | lit _ | primOp _ | var _ | lambda _ _ | app _ _ | letIn _ _ _ | fix _ _ => simp

/-- The arguments of `Expr.app f a` are the arguments of `f` together with `a`. -/
private theorem mem_spine_app {f a arg : RuntimeExpr} {c : DataConst} {args : List RuntimeExpr}
    (hspine : (Expr.app f a).spine = (.const c, args)) :
    arg ∈ args ↔ arg ∈ f.spine.2 ∨ arg = a := by
  have h : f.spine.2 ++ [a] = args := by simpa using congrArg Prod.snd hspine
  rw [← h, List.mem_append, List.mem_singleton]

/-- Every argument on a value's spine is itself a value. -/
theorem Value.mem_spine {sig : Signature} {expr : RuntimeExpr} (value : Value sig expr) :
    ∀ arg ∈ expr.spine.2, Value sig arg := by
  cases value with
  | lit | primOp | lambda => intro arg h; simp [Expr.spine] at h
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
  · rw [← h2] at hlen
    simp only [List.length_append, List.length_singleton] at hlen
    omega
  · intro x hx
    exact hall x ((mem_spine_app hspine).mpr (Or.inl hx))

/-- Values pass the `isValue` check. -/
private theorem isValue_of_value {sig : Signature} {expr : RuntimeExpr} (value : Value sig expr) :
    isValue sig expr = true := by
  induction expr with
  | lit _ =>
      cases value with
      | lit => rfl
      | const hspine _ _ _ => simp [Expr.spine] at hspine
  | primOp _ =>
      cases value with
      | primOp => rfl
      | const hspine _ _ _ => simp [Expr.spine] at hspine
  | lambda _ _ =>
      cases value with
      | lambda => rfl
      | const hspine _ _ _ => simp [Expr.spine] at hspine
  | var _ | letIn _ _ _ | fix _ _ =>
      cases value with
      | const hspine _ _ _ => simp [Expr.spine] at hspine
  | const c =>
      cases value with
      | const hspine harity _ _ =>
          simp [Expr.spine] at hspine
          obtain ⟨rfl, rfl⟩ := hspine
          simp [isValue, harity]
  | app f a ihf iha =>
      cases value with
      | primOpPartial h => simp [isValue, iha h]
      | const hspine harity hlen hall =>
          cases f with
          | primOp _ => simp [Expr.spine] at hspine
          | lit _ | var _ | lambda _ _ | letIn _ _ _ | fix _ _ => simp [Expr.spine] at hspine
          | const c' =>
              simp only [Expr.spine, List.nil_append] at hspine
              injection hspine with hc hargs
              injection hc with hc
              subst hc
              rw [← hargs] at hlen
              simp [isValue, Expr.spine, iha (hall a (by rw [← hargs]; simp)), harity]
              exact hlen
          | app g b =>
              have vf : Value sig (Expr.app g b) := Value.of_app_spine hspine harity hlen hall
              have va : Value sig a := hall a ((mem_spine_app hspine).mpr (Or.inr rfl))
              simp [isValue, ihf vf, iha va, hspine, harity, hlen]

theorem isValue_iff : isValue sig expr = true ↔ Value sig expr := by
  constructor
  · intro h
    induction expr with
    | lit _ => exact .lit
    | primOp _ => exact .primOp
    | lambda _ _ => exact .lambda
    | var _ | letIn _ _ _ | fix _ _ => simp [isValue] at h
    | const c =>
        obtain ⟨arity, harity⟩ := Option.isSome_iff_exists.mp h
        exact .const rfl harity (by simp) (by simp)
    | app f a ihf iha =>
        cases hf : f with
        | primOp op =>
            subst hf
            simp only [isValue] at h
            exact .primOpPartial (iha h)
        | lit _ | var _ | lambda _ _ | letIn _ _ _ | fix _ _ =>
            subst hf
            simp [isValue, Expr.spine] at h
        | const c =>
            subst hf
            simp only [isValue, Bool.and_eq_true] at h
            obtain ⟨⟨hvf, hva⟩, hsp⟩ := h
            obtain ⟨c', args, arity, hspine, harity, hlen⟩ :=
              (isValue_spine_iff (expr := Expr.app (Expr.const c) a)).mp hsp
            refine .const hspine harity hlen ?_
            intro arg harg
            rcases (mem_spine_app hspine).mp harg with hmem | rfl
            · exact Value.mem_spine (ihf hvf) arg hmem
            · exact iha hva
        | app g b =>
            subst hf
            simp only [isValue, Bool.and_eq_true] at h
            obtain ⟨⟨hvf, hva⟩, hsp⟩ := h
            obtain ⟨c, args, arity, hspine, harity, hlen⟩ :=
              (isValue_spine_iff (expr := Expr.app (Expr.app g b) a)).mp hsp
            refine .const hspine harity hlen ?_
            intro arg harg
            rcases (mem_spine_app hspine).mp harg with hmem | rfl
            · exact Value.mem_spine (ihf hvf) arg hmem
            · exact iha hva
  · exact isValue_of_value

/-- A successful `reduceConst` is an eliminator spine with one scrutinee and
exactly one branch per constructor. -/
private theorem reduceConst_some_elim {sig : Signature} {c : DataConst}
    {args : List RuntimeExpr} {result : RuntimeExpr}
    (hred : reduceConst sig c args = some result) :
    ∃ (type : Nat) (decl : DataDecl) (scrutinee : RuntimeExpr) (branches : List RuntimeExpr),
      c = .elim type ∧ args = scrutinee :: branches ∧ sig[type]? = some decl ∧
        branches.length = decl.ctors.length := by
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
              · exact ⟨type, decl, scrutinee, branches, rfl, rfl, hd, hne⟩
              · simp [reduceConst, hd, hne] at hred

/-- A saturated eliminator redex is never a value: its spine has one more
argument than `valueArity` allows. -/
theorem reduceConst_ne_of_length {sig : Signature} {c : DataConst}
    {args : List RuntimeExpr} {result : RuntimeExpr} {arity : Nat}
    (harity : sig.valueArity c = some arity) (hlen : args.length ≤ arity)
    (hred : reduceConst sig c args = some result) : False := by
  obtain ⟨_, decl, _, branches, rfl, hargs, hd, hne⟩ := reduceConst_some_elim hred
  have harity' : decl.ctors.length = arity := by simpa [Signature.valueArity, hd] using harity
  rw [hargs] at hlen
  simp only [List.length_cons] at hlen
  omega

theorem Value.irreducible (value : Value sig expr) : ¬ Step sig expr next := by
  intro step
  induction step with
  | beta _ =>
      cases value with
      | const hspine _ _ _ => simp [Expr.spine] at hspine
  | appFunction step ih =>
      cases value with
      | primOpPartial h => cases step
      | const hspine harity hlen hall =>
          exact ih (Value.of_app_spine hspine harity hlen hall)
  | appArgument _ step ih =>
      cases value with
      | primOpPartial h => exact ih h
      | const hspine _ _ hall =>
          exact ih (hall _ ((mem_spine_app hspine).mpr (Or.inr rfl)))
  | primOp _ =>
      cases value with
      | const hspine _ _ _ => simp [Expr.spine] at hspine
  | const hspine' _ hred =>
      cases value with
      | primOpPartial _ => simp [Expr.spine] at hspine'
      | const hspine harity hlen hall =>
          rw [hspine] at hspine'
          obtain ⟨rfl, rfl⟩ := hspine'
          exact reduceConst_ne_of_length harity hlen hred
  | letRhs _ _ | letValue _ | fixUnfold =>
      cases value with
      | const hspine _ _ _ => simp [Expr.spine] at hspine

/-- Contracting an application of two values is a step. -/
theorem reduceApp_sound {sig : Signature} {f a next : RuntimeExpr}
    (h : reduceApp sig f a = some next) (hf : Value sig f) (ha : Value sig a) :
    Step sig (.app f a) next := by
  simp only [reduceApp] at h
  split at h
  · cases h
    exact Step.beta ha
  · exact Step.primOp h
  · split at h
    · rename_i c args heq
      refine Step.const heq ?_ h
      intro arg harg
      rcases (mem_spine_app heq).mp harg with hmem | rfl
      · exact Value.mem_spine hf arg hmem
      · exact ha
    · simp at h

theorem step?_sound (found : step? sig expr = some next) : Step sig expr next := by
  induction expr generalizing next with
  | lit _ | primOp _ | const _ | var _ | lambda _ _ => simp [step?] at found
  | letIn ann rhs body ih =>
      simp only [step?] at found
      split at found
      · rename_i rhs' hstep
        cases found
        exact .letRhs (ih hstep)
      · split at found
        · rename_i hval
          cases found
          exact .letValue (isValue_iff.mp hval)
        · simp at found
  | fix self body =>
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

/-- Facts about the argument list of a successful `reduceConst`: it is a
nonempty eliminator spine whose tail has exactly the eliminator's arity. -/
theorem reduceConst_some_valueArity {sig : Signature} {c : DataConst}
    {args : List RuntimeExpr} {result : RuntimeExpr}
    (hred : reduceConst sig c args = some result) :
    ∃ arity : Nat, sig.valueArity c = some arity ∧
      ∃ first rest, args = first :: rest ∧ rest.length = arity := by
  obtain ⟨_, decl, scrutinee, branches, rfl, hargs, hd, hne⟩ := reduceConst_some_elim hred
  exact ⟨decl.ctors.length, by simp [Signature.valueArity, hd], scrutinee, branches, hargs, hne⟩

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

/-- The function part of a saturated constant spine is a value as soon as the
spine's arguments are. -/
private theorem value_function_of_reduceConst {sig : Signature} {f a : RuntimeExpr}
    {c : DataConst} {args : List RuntimeExpr} {result : RuntimeExpr}
    (hspine : (Expr.app f a).spine = (.const c, args))
    (hred : reduceConst sig c args = some result) (hall : ∀ arg ∈ args, Value sig arg) :
    Value sig f := by
  obtain ⟨arity, harity, _, rest, hargs, hrest⟩ := reduceConst_some_valueArity hred
  have hfst : f.spine.1 = .const c := by simpa using congrArg Prod.fst hspine
  have hargs' : f.spine.2 ++ [a] = args := by simpa using congrArg Prod.snd hspine
  have hlen : f.spine.2.length ≤ arity := by
    have := congrArg List.length hargs'
    rw [hargs, List.length_cons, hrest] at this
    simp only [List.length_append, List.length_cons] at this
    omega
  refine Value.const (by rw [spine_eta, hfst]) harity hlen ?_
  intro x hx
  exact hall x ((mem_spine_app hspine).mpr (Or.inl hx))

theorem step?_complete (step : Step sig expr next) : step? sig expr = some next := by
  induction step with
  | beta valueArg =>
      simp [isValue, step?, reduceApp, step?_none_of_value valueArg, isValue_iff.mpr valueArg]
  | appFunction hstep ih =>
      simp [step?, ih]
  | appArgument valueFunction hstep ih =>
      simp [step?, step?_none_of_value valueFunction, isValue_iff.mpr valueFunction, ih]
  | primOp h =>
      rename_i result op left right
      simp [isValue, Expr.spine, step?, reduceApp, h]
  | const hspine hall hred =>
      rename_i f a args c result
      have vf : Value sig f := value_function_of_reduceConst hspine hred hall
      have va : Value sig a := hall a ((mem_spine_app hspine).mpr (Or.inr rfl))
      simp [step?, step?_none_of_value vf, isValue_iff.mpr vf, step?_none_of_value va,
        isValue_iff.mpr va, reduceApp_of_spine_const hspine hred]
  | letRhs hstep ih =>
      simp [step?, ih]
  | letValue h =>
      simp [step?, step?_none_of_value h, isValue_iff.mpr h]
  | fixUnfold =>
      simp [step?]

theorem Step.deterministic (first : Step sig expr a) (second : Step sig expr b) : a = b := by
  have := step?_complete second
  rw [step?_complete first] at this
  exact Option.some.inj this

theorem run_steps (fuel : Nat) (expr : RuntimeExpr) : Steps sig expr (run sig fuel expr) := by
  induction fuel generalizing expr with
  | zero => exact Relation.ReflTransGen.refl
  | succ fuel ih =>
      rw [run]
      cases h : step? sig expr with
      | none => exact Relation.ReflTransGen.refl
      | some next => exact Relation.ReflTransGen.head (step?_sound h) (ih next)

/-- `run` stays at a value. -/
theorem run_value (value : Value sig expr) (fuel : Nat) : run sig fuel expr = expr := by
  cases fuel with
  | zero => rfl
  | succ fuel => rw [run, step?_none_of_value value]

/-- Every execution reaching a value is found by `run` with enough fuel, and
with any larger fuel. -/
theorem run_complete (steps : Steps sig expr result) (value : Value sig result) :
    ∃ fuel, ∀ extra, run sig (fuel + extra) expr = result := by
  induction steps using Relation.ReflTransGen.head_induction_on with
  | refl => exact ⟨0, fun extra => by rw [Nat.zero_add, run_value value]⟩
  | head step _ ih =>
      obtain ⟨fuel, found⟩ := ih
      refine ⟨fuel + 1, fun extra => ?_⟩
      rw [Nat.add_right_comm, run, step?_complete step]
      exact found extra

end Eval
end EPL
