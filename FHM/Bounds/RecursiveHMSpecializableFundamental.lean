import FHM.Bounds.RecursiveHMNestedInternalRealizer

/-! # Semantic interface for specializable body proofs

`SpecializableEnvFamily` fixes one lexical Core term vector while giving its
meaning at every observation budget and recursively closed world.  This file
states the semantic target for the forthcoming parallel body fundamental
theorem.  It intentionally does not convert an ordinary `RuntimeReady`
proof: ordinary body bindings lose the raw recursive provenance needed at a
closed-world boundary.
-/

namespace FHM.Bounds.RecursiveHMClosedExit

open RecursiveHMJudgement SchemeSpecialization CountSubstitution ScopedScheme
open RecursiveHMUniform

/-- The result-bound interpretation selected by a closed world.  This local
    spelling keeps the semantic interface independent of the still-evolving
    static body-view transport module. -/
def closedBound (world : EnvSpecialization env) (beta : BoundsTy) : BoundsTy :=
  mapFree world.types (bounds world.outer beta)

/-- The canonical no-op interpretation of count and HM variables.  It still
    closes raw recursive bindings into their closed-contract representation;
    only the bounds interpretation itself is identity. -/
def EnvSpecialization.identity (env : List Binding) : EnvSpecialization env where
  outer := []
  types := BoundsTy.fvar
  outerFinite := by intro row member; simp at member
  countTarget := []
  outerScope := by intro row member; simp at member
  typesLC := by
    intro i
    simpa [Synth.BoundsTy.toTy] using
      (ContainsBvarsUpTo.fvar : (Ty.fvar i).IsLC)
  typeTarget := []
  typesScope := by intro i; trivial
  fresh := by
    intro binding member
    cases binding with
    | exported scheme =>
        exact ⟨by intro i captured; rfl, by intro i free; rfl⟩
    | mono | recursive | recursiveClosure | closure => trivial
  typesSupported := by intro i; exact .fvar

/-- The family exposes the same Core substitution in every closed world. -/
theorem SpecializableEnvFamily.specializedTerms
    {bound free : Runtime.TypeEnv} {sigma : Assign} {env : List Binding}
    (family : SpecializableEnvFamily bound free sigma env)
    (budget : Nat) (world : EnvSpecialization env) :
    ((family.world budget).specialized world).terms = family.terms :=
  ((family.world budget).specializedTerms world).trans (family.worldTerms budget)

/-- A term is sound in every recursively closed interpretation of a fixed
    lexical term vector.  Premises and the result bound are interpreted in
    each world's count/HM substitution, while the Core substitution remains
    `family.terms`. -/
structure SpecializableTermAt
    (bound free : Runtime.TypeEnv) (sigma : Assign) {env : List Binding}
    (family : SpecializableEnvFamily bound free sigma env)
    (Delta : List Constraint) (expr : Expr) (beta : BoundsTy) : Prop where
  run : ∀ (budget : Nat) (world : EnvSpecialization env),
    (∀ p ∈ Delta.map (constraint world.outer), p.Holds sigma) →
    Runtime.TermAt bound free sigma budget (closedBound world beta)
      (expr.substN 0 family.terms)

namespace SpecializableTermAt

/-- Primitive literals are independent of the closed lexical world. -/
def literal
    {bound free : Runtime.TypeEnv} {sigma : Assign} {env : List Binding}
    {family : SpecializableEnvFamily bound free sigma env} {Delta : List Constraint}
    (p : PrimLitExpr) :
    SpecializableTermAt bound free sigma family Delta (.primLit p) (boundInfoOfPrimLit p) where
  run budget world premises := by
    apply Runtime.TermAt.value (.primLit _)
    have stable : closedBound world (boundInfoOfPrimLit p) = boundInfoOfPrimLit p := by
      cases p <;> rfl
    rw [stable]
    exact Runtime.ValueAt.literal bound free sigma budget p

/-- Primitive operators are independent of the closed lexical world. -/
def primBinOp
    {bound free : Runtime.TypeEnv} {sigma : Assign} {env : List Binding}
    {family : SpecializableEnvFamily bound free sigma env} {Delta : List Constraint}
    (op : PrimBinOp) :
    SpecializableTermAt bound free sigma family Delta (.primBinOp op)
      (Typed.primOpBounds op) where
  run budget world premises := by
    apply Runtime.TermAt.value (.primBinOp _)
    have stable : closedBound world (Typed.primOpBounds op) = Typed.primOpBounds op := by
      cases op <;> rfl
    rw [stable]
    exact Runtime.ValueAt.primBinOp bound free sigma budget op

/-- The semantic continuation required below a lambda.  It deliberately
    ranges over an arbitrary value at the current closed-world interpretation
    of the parameter rather than pretending that such a value extends the
    family's source fixed environment. -/
structure LambdaBody
    {bound free : Runtime.TypeEnv} {sigma : Assign} {env : List Binding}
    (family : SpecializableEnvFamily bound free sigma env)
    (Delta : List Constraint) (param result : BoundsTy) (body : Expr) : Prop where
  run : ∀ (budget : Nat) (world : EnvSpecialization env)
    (_premises : ∀ p ∈ Delta.map (constraint world.outer), p.Holds sigma)
    (arg : Expr),
    Runtime.ValueAt bound free sigma (budget + 1) (closedBound world param) arg →
    Runtime.TermAt bound free sigma budget (closedBound world result)
      (body.substN 0 (arg :: family.terms))

/-- The semantic continuation required after a monomorphic local binding.
    Like `LambdaBody`, it records the runtime value directly.  A future
    Kripke induction can construct this from the per-world RHS theorem; no
    conversion of a source fixed environment is asserted here. -/
structure MonoLetBody
    {bound free : Runtime.TypeEnv} {sigma : Assign} {env : List Binding}
    (family : SpecializableEnvFamily bound free sigma env)
    (Delta : List Constraint) (actual result : BoundsTy) (body : Expr) : Prop where
  run : ∀ (budget : Nat) (world : EnvSpecialization env)
    (_premises : ∀ p ∈ Delta.map (constraint world.outer), p.Holds sigma)
    (value : Expr),
    Runtime.ValueAt bound free sigma (budget + 1) (closedBound world actual) value →
    Runtime.TermAt bound free sigma budget (closedBound world result)
      (body.substN 0 (value :: family.terms))

/-- Evaluate a family-indexed semantic proof in the canonical base world.
    The result is deliberately expressed at `closedBound identity`; a later
    normalization lemma may identify this bound with the source bound without
    changing the semantic interface. -/
def base
    {bound free : Runtime.TypeEnv} {sigma : Assign} {env : List Binding}
    {family : SpecializableEnvFamily bound free sigma env}
    {Delta : List Constraint} {expr : Expr} {beta : BoundsTy}
    (safe : SpecializableTermAt bound free sigma family Delta expr beta)
    (budget : Nat)
    (premises : ∀ p ∈ Delta.map (constraint ([] : Bindings)), p.Holds sigma) :
    Runtime.TermAt bound free sigma budget
      (closedBound (EnvSpecialization.identity env) beta)
      (expr.substN 0 family.terms) :=
  safe.run budget (EnvSpecialization.identity env) premises

/-- Semantic subsumption is pointwise in the recursively closed world. -/
def subsumption
    {bound free : Runtime.TypeEnv} {sigma : Assign} {env : List Binding}
    {family : SpecializableEnvFamily bound free sigma env}
    {Delta : List Constraint} {expr : Expr} {actual demand : BoundsTy}
    (safe : SpecializableTermAt bound free sigma family Delta expr actual)
    (inclusion : ∀ world : EnvSpecialization env,
      SemanticSub (Delta.map (constraint world.outer))
        (closedBound world actual) (closedBound world demand))
    (actualSupported : ∀ world : EnvSpecialization env,
      Runtime.Supported (closedBound world actual))
    (demandSupported : ∀ world : EnvSpecialization env,
      Runtime.Supported (closedBound world demand)) :
    SpecializableTermAt bound free sigma family Delta expr demand where
  run budget world premises :=
    (safe.run budget world premises).of_values
      (Runtime.subtype (inclusion world) (actualSupported world) (demandSupported world)
        bound free sigma premises)

/-- Application is likewise pointwise: the argument is first semantically
    widened to the function domain in the current closed world. -/
def app
    {bound free : Runtime.TypeEnv} {sigma : Assign} {env : List Binding}
    {family : SpecializableEnvFamily bound free sigma env}
    {Delta : List Constraint} {fn arg : Expr}
    {domain actual result : BoundsTy}
    (hb : Runtime.TypeEnv.Downward bound) (hf : Runtime.TypeEnv.Downward free)
    (function : SpecializableTermAt bound free sigma family Delta fn (.arrow domain result))
    (argument : SpecializableTermAt bound free sigma family Delta arg actual)
    (inclusion : ∀ world : EnvSpecialization env,
      SemanticSub (Delta.map (constraint world.outer))
        (closedBound world actual) (closedBound world domain))
    (actualSupported : ∀ world : EnvSpecialization env,
      Runtime.Supported (closedBound world actual))
    (domainSupported : ∀ world : EnvSpecialization env,
      Runtime.Supported (closedBound world domain)) :
    SpecializableTermAt bound free sigma family Delta (.app fn arg) result where
  run budget world premises := by
    have functionAt : Runtime.TermAt bound free sigma budget
        (.arrow (closedBound world domain) (closedBound world result))
        (fn.substN 0 family.terms) := by
      simpa [closedBound, bounds, mapFree] using
        function.run budget world premises
    have argumentAt := argument.run budget world premises
    exact Runtime.TermAt.app hb hf functionAt
      (argumentAt.of_values
        (Runtime.subtype (inclusion world) (actualSupported world) (domainSupported world)
          bound free sigma premises))

end SpecializableTermAt

end FHM.Bounds.RecursiveHMClosedExit
