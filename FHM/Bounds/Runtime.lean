import FHM.Bounds.BoolBranches
import FHM.Bounds.ListBranches

/-! # Bounds meaning in the existing erased small-step semantics

This is the runtime target, not another evaluator or acceptance algorithm.
Finite observation budgets permit divergence while detecting stuck states and
checking every value observed with positive budget. Arrows describe the actual
behaviour of applications, rather than only their erased HM shape.

Nominal data is currently restricted to the supported List/Bool fragment.
Other constructors require their field/variance semantics before a fundamental
theorem may cover them. Free and bound HM identities have explicit semantic
environments; their downward-closure obligations belong to environment validity.
The checker-to-runtime fundamental theorem is NOT supplied by these definitions.
-/

namespace FHM.Bounds.Runtime

/-- An exact number of steps of the existing language, with no new rules. -/
inductive Reduces : Nat → Expr → Expr → Prop where
  | refl (e) : Reduces 0 e e
  | step : SmallStep.Step e e' → Reduces n e' v → Reduces (n + 1) e v

/-- Concrete saturated List values, retaining every actual element and length. -/
inductive ListValue (element : Expr → Prop) : Expr → Nat → Prop where
  | nil : ListValue element (.ctor nilCtorName) 0
  | cons : element h → ListValue element t n →
      ListValue element (.app (.app (.ctor consCtorName) h) t) (n + 1)

theorem ListValue.map {p q : Expr → Prop} (hpq : ∀ v, p v → q v)
    (h : ListValue p v n) : ListValue q v n := by
  induction h with
  | nil => exact .nil
  | cons hh _ ih => exact .cons (hpq _ hh) ih

/-- Explicit domain of the initial runtime theorem; not an inference guard. -/
inductive Supported : BoundsTy → Prop where
  | prim : Supported (.prim p)
  | bvar : Supported (.bvar i)
  | fvar : Supported (.fvar i)
  | arrow : Supported a → Supported b → Supported (.arrow a b)
  | list : Supported elem → Supported (.list lo hi elem)
  | bool : Supported (.custom boolTyName [])

abbrev TypeEnv := Nat → Nat → Expr → Prop

mutual
  /-- At positive budgets, values are closed and have the promised runtime
      contents. An arrow accepts every argument at any budget up to its own;
      the application budget includes the beta/delta step itself. -/
  def ValueAt (bound free : TypeEnv) (σ : Assign) (budget : Nat)
      (β : BoundsTy) (v : Expr) : Prop :=
    match budget with
    | 0 => True
    | n + 1 =>
      SmallStep.IsValue v ∧ v.varsBelow 0 = true ∧
      match β with
      | .prim p => ∃ literal, v = .primLit literal ∧ literal.ty = .prim p
      | .bvar i => bound i (n + 1) v
      | .fvar i => free i (n + 1) v
      | .arrow domain result =>
          ∀ j, j ≤ n + 1 → ∀ arg, ValueAt bound free σ j domain arg →
            TermAt bound free σ j result (.app v arg)
      | .list lo hi elem =>
          ∃ len, ListValue (ValueAt bound free σ (n + 1) elem) v len ∧
            (⟨lo, hi⟩ : Interval).Contains σ (.ofNat len)
      | .custom name args =>
          name = boolTyName ∧ args = [] ∧
            (v = .ctor BoolBranches.trueCtorName ∨ v = .ctor BoolBranches.falseCtorName)
  termination_by (sizeOf β, 0)
  decreasing_by
    all_goals apply Prod.Lex.left _ _
    all_goals simp
    all_goals omega

  /-- Every state reached before the budget expires either steps, or is a
      value satisfying the bounds at its remaining observation budget. -/
  def TermAt (bound free : TypeEnv) (σ : Assign) (budget : Nat)
      (β : BoundsTy) (e : Expr) : Prop :=
    ∀ steps v, Reduces steps e v → steps < budget →
      (SmallStep.IsValue v → ValueAt bound free σ (budget - steps) β v) ∧
      (¬ SmallStep.IsValue v → ∃ next, SmallStep.Step v next)
  termination_by (sizeOf β, 1)
  decreasing_by exact Prod.Lex.right _ (by omega)
end

/-- Instantiated type meanings must remain valid when observation fuel shrinks.
    This is a semantic environment condition, not a guessed bounds origin. -/
def TypeEnv.Downward (env : TypeEnv) : Prop :=
  ∀ i small large v, small ≤ large → env i large v → env i small v

theorem ValueAt.down {bound free σ small large β v}
    (hb : TypeEnv.Downward bound) (hf : TypeEnv.Downward free)
    (le : small ≤ large) (h : ValueAt bound free σ large β v) :
    ValueAt bound free σ small β v := by
  cases small with
  | zero => simp only [ValueAt]
  | succ small =>
    cases large with
    | zero => omega
    | succ large =>
      rw [ValueAt.eq_def] at h ⊢
      obtain ⟨value, closed, meaning⟩ := h
      refine ⟨value, closed, ?_⟩
      cases β with
      | prim p => exact meaning
      | bvar i => exact hb i _ _ v le meaning
      | fvar i => exact hf i _ _ v le meaning
      | arrow domain result =>
          intro j before arg argument
          exact meaning j (by omega) arg argument
      | list lo hi elem =>
          obtain ⟨len, elements, interval⟩ := meaning
          exact ⟨len, elements.map (fun _ hv => ValueAt.down hb hf le hv), interval⟩
      | custom name args => exact meaning
termination_by sizeOf β

theorem TermAt.down {bound free σ small large β e}
    (hb : TypeEnv.Downward bound) (hf : TypeEnv.Downward free)
    (le : small ≤ large) (h : TermAt bound free σ large β e) :
    TermAt bound free σ small β e := by
  unfold TermAt at h ⊢
  intro steps v reduction before
  obtain ⟨value, next⟩ := h steps v reduction (by omega)
  exact ⟨fun hv => (value hv).down hb hf (by omega), next⟩

theorem TermAt.of_values {bound free σ budget a b e}
    (convert : ∀ n v, ValueAt bound free σ n a v → ValueAt bound free σ n b v)
    (h : TermAt bound free σ budget a e) : TermAt bound free σ budget b e := by
  unfold TermAt at h ⊢
  intro steps v reduction before
  obtain ⟨value, steps⟩ := h steps v reduction before
  exact ⟨fun hv => convert _ _ (value hv), steps⟩

/-- Structural semantic subtyping implies inclusion of actual runtime meanings,
    including contravariant higher-order arguments. No solver call or axiom. -/
theorem subtype {Δ a b} (h : SemanticSub Δ a b)
    (ha : Supported a) (hb : Supported b) (bound free : TypeEnv) (σ : Assign)
    (premises : ∀ c ∈ Δ, c.Holds σ) :
    ∀ budget v, ValueAt bound free σ budget a v → ValueAt bound free σ budget b v := by
  cases h with
  | prim => exact fun _ _ hv => hv
  | bvar => exact fun _ _ hv => hv
  | fvar => exact fun _ _ hv => hv
  | arrow domainSub resultSub =>
      cases ha with
      | arrow haDomain haResult =>
        cases hb with
        | arrow hbDomain hbResult =>
          intro budget v hv
          cases budget with
          | zero => simp only [ValueAt]
          | succ n =>
            rw [ValueAt] at hv ⊢
            obtain ⟨value, closed, behaviour⟩ := hv
            refine ⟨value, closed, ?_⟩
            intro j before arg argument
            exact TermAt.of_values (subtype resultSub haResult hbResult bound free σ premises)
              (behaviour j before arg
                (subtype domainSub hbDomain haDomain bound free σ premises j arg argument))
  | list inclusion elemSub =>
      cases ha with
      | list haElem =>
        cases hb with
        | list hbElem =>
          intro budget v hv
          cases budget with
          | zero => simp only [ValueAt]
          | succ n =>
            rw [ValueAt] at hv ⊢
            obtain ⟨value, closed, len, elements, contained⟩ := hv
            exact ⟨value, closed, len,
              elements.map (subtype elemSub haElem hbElem bound free σ premises (n + 1)),
              contained.of_subGoals inclusion premises⟩
  | custom args =>
      cases ha with
      | bool =>
        cases args with
        | nil => exact fun _ _ hv => hv
termination_by sizeOf a + sizeOf b

/-- One existing-language step consumes one unit of semantic safety budget. -/
theorem TermAt.step {bound free σ budget β e e'}
    (h : TermAt bound free σ (budget + 1) β e) (step : SmallStep.Step e e') :
    TermAt bound free σ budget β e' := by
  unfold TermAt at h ⊢
  intro steps v reduction before
  have reached := h (steps + 1) v (.step step reduction) (by omega)
  simpa only [Nat.add_sub_add_right] using reached

/-- Unbounded observational safety allows infinite reductions; it does not
    claim termination or infer recursive invariants. -/
def Safe (bound free : TypeEnv) (σ : Assign) (β : BoundsTy) (e : Expr) : Prop :=
  ∀ budget, TermAt bound free σ budget β e

theorem Safe.subtype {bound free σ Δ a b e} (h : Safe bound free σ a e)
    (sub : SemanticSub Δ a b) (ha : Supported a) (hb : Supported b)
    (premises : ∀ c ∈ Δ, c.Holds σ) : Safe bound free σ b e :=
  fun budget => TermAt.of_values (Runtime.subtype sub ha hb bound free σ premises) (h budget)

theorem Safe.step {bound free σ β e e'} (h : Safe bound free σ β e)
    (step : SmallStep.Step e e') : Safe bound free σ β e' :=
  fun budget => (h (budget + 1)).step step

theorem Safe.progress {bound free σ β e} (h : Safe bound free σ β e) :
    SmallStep.IsValue e ∨ ∃ next, SmallStep.Step e next := by
  by_cases value : SmallStep.IsValue e
  · exact .inl value
  · have observation := h 1
    unfold TermAt at observation
    exact .inr ((observation 0 e (.refl e) (by omega)).2 value)

/-- The desired observable consequence: any finitely reached List value has
    an actual constructor-spine length inside the declared interval. -/
theorem Safe.list_length {bound free σ lo hi elem e v steps}
    (h : Safe bound free σ (.list lo hi elem) e) (reduction : Reduces steps e v)
    (value : SmallStep.IsValue v) :
    ∃ len, ListValue (ValueAt bound free σ 1 elem) v len ∧
      (⟨lo, hi⟩ : Interval).Contains σ (.ofNat len) := by
  have observation := h (steps + 1)
  unfold TermAt at observation
  have observed := (observation steps v reduction (by omega)).1 value
  have : steps + 1 - steps = 1 := by omega
  rw [this] at observed
  rw [ValueAt] at observed
  exact observed.2.2

#print axioms subtype
#print axioms ValueAt.down
#print axioms TermAt.down
#print axioms Safe.subtype
#print axioms Safe.step
#print axioms Safe.progress
#print axioms Safe.list_length

end FHM.Bounds.Runtime
