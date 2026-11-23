import EPL.Spec.Syntax
import EPL.Runtime

/-!
# Exhaustiveness

The check agrees with the relation, and exhaustiveness survives erasure and
evaluation, so progress can be applied after every step.
-/

namespace EPL

/-- The check `Signature.covers` decides the relation `Signature.Covers`. -/
private theorem Signature.covers_iff {sig : Signature} {patterns : List CtorRef} :
    sig.covers patterns = true ↔ sig.Covers patterns := by
  rw [Signature.covers, List.all_eq_true]
  constructor
  · intro covered pattern mem decl found index inRange
    have patternCovered := covered pattern mem
    rw [found, List.all_eq_true] at patternCovered
    exact List.contains_iff_mem.mp
      (patternCovered index (List.mem_range.mpr inRange))
  · intro covered pattern mem
    cases found : sig[pattern.type]? with
    | none => rfl
    | some decl =>
        change (List.range decl.ctors.length).all
          (fun index => patterns.contains ⟨pattern.type, index⟩) = true
        rw [List.all_eq_true]
        intro index inRange
        exact List.contains_iff_mem.mpr
          (covered pattern mem decl found index (List.mem_range.mp inRange))

/-- `Expr.exhaustiveBranches` accepts exactly the lists whose branch bodies
are exhaustive. -/
private theorem Expr.exhaustiveBranches_eq_true {sig : Signature}
    {branches : List (Pattern × Expr A)} :
    Expr.exhaustiveBranches sig branches = true ↔
      ∀ branch ∈ branches, branch.2.exhaustive sig = true := by
  induction branches with
  | nil => simp [Expr.exhaustiveBranches]
  | cons branch rest ih =>
      obtain ⟨pattern, body⟩ := branch
      simp only [Expr.exhaustiveBranches, Bool.and_eq_true, ih]
      constructor
      · rintro ⟨bodyExhaustive, restExhaustive⟩ next nextMem
        rcases List.mem_cons.mp nextMem with rfl | nextMem
        · exact bodyExhaustive
        · exact restExhaustive next nextMem
      · intro allExhaustive
        exact ⟨allExhaustive (pattern, body) (by simp),
          fun next nextMem => allExhaustive next (List.mem_cons_of_mem _ nextMem)⟩

/-- The check decides the relation. -/
theorem Expr.exhaustive_iff {sig : Signature} {expr : Expr A} :
    expr.exhaustive sig = true ↔ Exhaustive sig expr := by
  induction expr using Expr.induction with
  | lit literal => exact ⟨fun _ => .lit, fun _ => rfl⟩
  | primOp op => exact ⟨fun _ => .primOp, fun _ => rfl⟩
  | ctor ref => exact ⟨fun _ => .ctor, fun _ => rfl⟩
  | var index => exact ⟨fun _ => .var, fun _ => rfl⟩
  | lambda param body ih =>
      simp only [Expr.exhaustive]
      exact ⟨fun bodyExhaustive => .lambda (ih.mp bodyExhaustive),
        fun exhaustive => by cases exhaustive with | lambda bodyExhaustive => exact ih.mpr bodyExhaustive⟩
  | app function argument functionIh argumentIh =>
      simp only [Expr.exhaustive, Bool.and_eq_true]
      exact ⟨fun ⟨functionExhaustive, argumentExhaustive⟩ =>
          .app (functionIh.mp functionExhaustive) (argumentIh.mp argumentExhaustive),
        fun exhaustive => by
          cases exhaustive with
          | app functionExhaustive argumentExhaustive =>
              exact ⟨functionIh.mpr functionExhaustive, argumentIh.mpr argumentExhaustive⟩⟩
  | letIn ann rhs body rhsIh bodyIh =>
      simp only [Expr.exhaustive, Bool.and_eq_true]
      exact ⟨fun ⟨rhsExhaustive, bodyExhaustive⟩ =>
          .letIn (rhsIh.mp rhsExhaustive) (bodyIh.mp bodyExhaustive),
        fun exhaustive => by
          cases exhaustive with
          | letIn rhsExhaustive bodyExhaustive =>
              exact ⟨rhsIh.mpr rhsExhaustive, bodyIh.mpr bodyExhaustive⟩⟩
  | fix self body ih =>
      simp only [Expr.exhaustive]
      exact ⟨fun bodyExhaustive => .fix (ih.mp bodyExhaustive),
        fun exhaustive => by cases exhaustive with | fix bodyExhaustive => exact ih.mpr bodyExhaustive⟩
  | «match» scrutinee branches scrutineeIh branchIhs =>
      have branchesIff : Expr.exhaustiveBranches sig branches = true ↔
          ∀ branch ∈ branches, Exhaustive sig branch.2 := by
        rw [Expr.exhaustiveBranches_eq_true]
        constructor
        · intro allExhaustive branch branchMem
          exact (branchIhs branch branchMem).mp (allExhaustive branch branchMem)
        · intro allExhaustive branch branchMem
          exact (branchIhs branch branchMem).mpr (allExhaustive branch branchMem)
      simp only [Expr.exhaustive, Bool.and_eq_true, scrutineeIh, branchesIff,
        Signature.covers_iff]
      exact ⟨fun ⟨⟨scrutineeExhaustive, branchesExhaustive⟩, covers⟩ =>
          .match scrutineeExhaustive branchesExhaustive covers,
        fun exhaustive => by
          cases exhaustive with
          | «match» scrutineeExhaustive branchesExhaustive covers =>
              exact ⟨⟨scrutineeExhaustive, branchesExhaustive⟩, covers⟩⟩

instance (sig : Signature) (expr : Expr A) : Decidable (Exhaustive sig expr) :=
  decidable_of_iff _ Expr.exhaustive_iff

/-- Erasure keeps every match and its patterns. -/
theorem Exhaustive.erase {sig : Signature} {expr : Expr A} (exhaustive : Exhaustive sig expr) :
    Exhaustive sig expr.erase := by
  induction exhaustive with
  | lit => exact .lit
  | primOp => exact .primOp
  | ctor => exact .ctor
  | var => exact .var
  | lambda _ ih => exact .lambda ih
  | app _ _ functionIh argumentIh => exact .app functionIh argumentIh
  | letIn _ _ rhsIh bodyIh => exact .letIn rhsIh bodyIh
  | fix _ ih => exact .fix ih
  | «match» _ branchesExhaustive covers scrutineeIh branchIhs =>
      simp only [Expr.erase, Expr.eraseBranches_eq]
      refine .match scrutineeIh ?_ ?_
      · intro branch branchMem
        obtain ⟨original, originalMem, rfl⟩ := List.mem_map.mp branchMem
        exact branchIhs original originalMem
      · simpa only [List.map_map, Function.comp_def] using covers

/-- Shifting keeps every match and its patterns. -/
theorem Exhaustive.shift {sig : Signature} {expr : Expr A} (exhaustive : Exhaustive sig expr)
    (cutoff amount : Nat) : Exhaustive sig (expr.shift cutoff amount) := by
  induction exhaustive generalizing cutoff with
  | lit => exact .lit
  | primOp => exact .primOp
  | ctor => exact .ctor
  | var => exact .var
  | lambda _ ih => exact .lambda (ih (cutoff + 1))
  | app _ _ functionIh argumentIh => exact .app (functionIh cutoff) (argumentIh cutoff)
  | letIn _ _ rhsIh bodyIh => exact .letIn (rhsIh cutoff) (bodyIh (cutoff + 1))
  | fix _ ih => exact .fix (ih (cutoff + 1))
  | «match» _ branchesExhaustive covers scrutineeIh branchIhs =>
      simp only [Expr.shift, Expr.shiftBranches_eq]
      refine .match (scrutineeIh cutoff) ?_ ?_
      · intro branch branchMem
        obtain ⟨original, originalMem, rfl⟩ := List.mem_map.mp branchMem
        exact branchIhs original originalMem (cutoff + original.1.binders)
      · simpa only [List.map_map, Function.comp_def] using covers

/-- Substituting an exhaustive value into an exhaustive term. -/
theorem Exhaustive.substAt {sig : Signature} {expr value : Expr A}
    (exhaustive : Exhaustive sig expr) (valueExhaustive : Exhaustive sig value) (depth : Nat) :
    Exhaustive sig (expr.substAt depth value) := by
  induction exhaustive generalizing depth with
  | lit => exact .lit
  | primOp => exact .primOp
  | ctor => exact .ctor
  | var =>
      simp only [Expr.substAt]
      split_ifs
      · exact .var
      · exact valueExhaustive.shift 0 depth
      · exact .var
  | lambda _ ih => exact .lambda (ih (depth + 1))
  | app _ _ functionIh argumentIh => exact .app (functionIh depth) (argumentIh depth)
  | letIn _ _ rhsIh bodyIh => exact .letIn (rhsIh depth) (bodyIh (depth + 1))
  | fix _ ih => exact .fix (ih (depth + 1))
  | «match» _ branchesExhaustive covers scrutineeIh branchIhs =>
      simp only [Expr.substAt, Expr.substAtBranches_eq]
      refine .match (scrutineeIh depth) ?_ ?_
      · intro branch branchMem
        obtain ⟨original, originalMem, rfl⟩ := List.mem_map.mp branchMem
        exact branchIhs original originalMem (depth + original.1.binders)
      · simpa only [List.map_map, Function.comp_def] using covers

/-- Substituting exhaustive values into an exhaustive body is exhaustive. -/
private theorem Expr.substMany_exhaustive {sig : Signature} {body : Expr A}
    {values : List (Expr A)} (bodyExhaustive : Exhaustive sig body)
    (valuesExhaustive : ∀ value ∈ values, Exhaustive sig value) :
    Exhaustive sig (body.substMany values) := by
  induction values generalizing body with
  | nil => simpa [Expr.substMany] using bodyExhaustive
  | cons value rest ih =>
      exact ih (Exhaustive.substAt bodyExhaustive (valuesExhaustive value (by simp)) _)
        fun next nextMem => valuesExhaustive next (by simp [nextMem])

/-- The fields of an exhaustive expression's spine are exhaustive. -/
private theorem Exhaustive.spine {sig : Signature} {expr : Expr A} (exhaustive : Exhaustive sig expr) :
    Exhaustive sig expr.spine.1 ∧ ∀ field ∈ expr.spine.2, Exhaustive sig field := by
  induction exhaustive with
  | lit => exact ⟨.lit, by simp [Expr.spine]⟩
  | primOp => exact ⟨.primOp, by simp [Expr.spine]⟩
  | ctor => exact ⟨.ctor, by simp [Expr.spine]⟩
  | var => exact ⟨.var, by simp [Expr.spine]⟩
  | lambda bodyExhaustive ih =>
      exact ⟨.lambda bodyExhaustive, by simp [Expr.spine]⟩
  | app functionExhaustive argumentExhaustive functionIh argumentIh =>
      simp only [Expr.spine]
      refine ⟨functionIh.1, ?_⟩
      intro field fieldMem
      rcases List.mem_append.mp fieldMem with fieldMem | fieldMem
      · exact functionIh.2 field fieldMem
      · rw [List.mem_singleton] at fieldMem
        subst fieldMem
        exact argumentExhaustive
  | letIn rhsExhaustive bodyExhaustive rhsIh bodyIh =>
      exact ⟨.letIn rhsExhaustive bodyExhaustive, by simp [Expr.spine]⟩
  | fix bodyExhaustive ih =>
      exact ⟨.fix bodyExhaustive, by simp [Expr.spine]⟩
  | «match» scrutineeExhaustive branchesExhaustive covers scrutineeIh branchIhs =>
      exact ⟨.match scrutineeExhaustive branchesExhaustive covers, by simp [Expr.spine]⟩

/-- A successful primitive operation produces an exhaustive expression. -/
private theorem Exhaustive.eval {sig : Signature} {op : PrimOp} {left right : PrimLit}
    {result : RuntimeExpr} (eval : op.eval left right = some result) :
    Exhaustive sig result := by
  cases op <;> cases left <;> cases right <;>
    simp [PrimOp.eval] at eval
  all_goals
    first
    | subst result; exact .lit
    | subst result; exact .ctor

/-- Exhaustiveness survives a step. Proof: induction on the step;
`beta`/`letValue`/`fixUnfold` by `Exhaustive.substAt`; `matchCtor` because
the taken branch and the scrutinee's fields are exhaustive (substituting
exhaustive values into an exhaustive body is exhaustive). -/
theorem Exhaustive.step {sig : Signature} {expr next : RuntimeExpr}
    (exhaustive : Exhaustive sig expr) (step : Eval.Step expr next) :
    Exhaustive sig next := by
  revert exhaustive
  induction step with
  | beta value =>
      intro exhaustive
      cases exhaustive with
      | app lambdaExhaustive argumentExhaustive =>
          cases lambdaExhaustive with
          | lambda bodyExhaustive =>
              simpa only [Expr.subst1] using
                Exhaustive.substAt bodyExhaustive argumentExhaustive 0
  | appFunction step ih =>
      intro exhaustive
      cases exhaustive with
      | app functionExhaustive argumentExhaustive =>
          exact .app (ih functionExhaustive) argumentExhaustive
  | appArgument value step ih =>
      intro exhaustive
      cases exhaustive with
      | app functionExhaustive argumentExhaustive =>
          exact .app functionExhaustive (ih argumentExhaustive)
  | primOp eval =>
      intro exhaustive
      cases exhaustive with
      | app outerExhaustive _ =>
          cases outerExhaustive with
          | app operatorExhaustive _ =>
              cases operatorExhaustive with
              | primOp => exact Exhaustive.eval eval
  | matchScrutinee step ih =>
      intro exhaustive
      cases exhaustive with
      | «match» scrutineeExhaustive branchesExhaustive covers =>
          exact .match (ih scrutineeExhaustive) branchesExhaustive covers
  | matchCtor value spine find =>
      intro exhaustive
      cases exhaustive with
      | «match» scrutineeExhaustive branchesExhaustive covers =>
          have fieldsExhaustive := (Exhaustive.spine scrutineeExhaustive).2
          rw [spine] at fieldsExhaustive
          obtain ⟨_, _, mem⟩ := Expr.findBranch_mem find
          exact Expr.substMany_exhaustive (branchesExhaustive _ mem) fieldsExhaustive
  | letRhs step ih =>
      intro exhaustive
      cases exhaustive with
      | letIn rhsExhaustive bodyExhaustive =>
          exact .letIn (ih rhsExhaustive) bodyExhaustive
  | letValue value =>
      intro exhaustive
      cases exhaustive with
      | letIn rhsExhaustive bodyExhaustive =>
          simpa only [Expr.subst1] using
            Exhaustive.substAt bodyExhaustive rhsExhaustive 0
  | fixUnfold =>
      intro exhaustive
      cases exhaustive with
      | fix bodyExhaustive =>
          simpa only [Expr.subst1] using
            Exhaustive.substAt bodyExhaustive (.fix bodyExhaustive) 0

end EPL
