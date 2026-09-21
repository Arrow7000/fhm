import FHM.Bounds.RecursiveHMClosedExportEnvironment

/-! # Substitution-indexed runtime environments

An enclosing recursive environment cannot in general be represented by one
`EnvAt` when it occurs beneath a generalized group.  Each use of a closed
group exit induces its own protected count/HM substitution, and the member
implementation is checked in `closeRecursiveEnv` at precisely that world.

`SpecializableEnvAt` records the corresponding Kripke invariant: one list of
runtime terms realizes the fixed body view, the ordinary (exported) body view,
and every lawful recursively closed specialization.  It is semantic evidence,
not executable checker state.
-/

namespace FHM.Bounds.RecursiveHMUniform

open RecursiveHMJudgement SchemeSpecialization CountSubstitution ScopedScheme

/-- The side conditions under which `ScopedDerives.closeRecursive` transports
    a source derivation.  Packaging them makes the runtime witness range over
    exactly the static worlds which can arise below a generalized group. -/
structure EnvSpecialization (env : List Binding) where
  outer : Bindings
  types : Nat → BoundsTy
  outerFinite : Finite outer
  countTarget : List Nat
  outerScope : ∀ row ∈ outer, Scope.CountScoped countTarget row.2
  typesLC : ∀ i, (Synth.BoundsTy.toTy (types i)).IsLC
  typeTarget : List Nat
  typesScope : ∀ i, BoundsScoped typeTarget (types i)
  fresh : CloseRecursiveFresh outer types env
  typesSupported : ∀ i, Runtime.Supported (types i)

/-- A single closed term vector, observed through all three environments used
    by the recursive-body fundamental theorem.  The equalities are essential:
    merely having three unrelated inhabitants would not justify closing a
    nested group's source terms once and reusing them in every specialization. -/
structure SpecializableEnvAt (bound free : Runtime.TypeEnv) (sigma : Assign)
    (budget : Nat) (env : List Binding) where
  fixed : BodyEnvAt bound free sigma budget (fixedBodyEnv env)
  ordinary : BodyEnvAt bound free sigma budget (ordinaryBodyEnv env)
  ordinaryTerms : ordinary.terms = fixed.terms
  specialized : ∀ world : EnvSpecialization env,
    EnvAt bound free sigma budget
      (closeRecursiveEnv world.outer world.types env)
  specializedTerms : ∀ world, (specialized world).terms = fixed.terms

namespace EnvAt

/-- Reindex an environment without changing its runtime term vector. -/
def castEnv {bound free sigma budget source target}
    (same : source = target) (e : EnvAt bound free sigma budget source) :
    EnvAt bound free sigma budget target := by
  cases same
  exact e

@[simp] theorem castEnv_terms {bound free sigma budget source target}
    (same : source = target) (e : EnvAt bound free sigma budget source) :
    (castEnv same e).terms = e.terms := by
  cases same
  rfl

/-- Concatenate two semantic environments and their term vectors. -/
def append {bound free sigma budget left right}
    (head : EnvAt bound free sigma budget left)
    (tail : EnvAt bound free sigma budget right) :
    EnvAt bound free sigma budget (left ++ right) where
  terms := head.terms ++ tail.terms
  arity := by simp only [List.length_append, head.arity, tail.arity]
  closed := by
    intro term member
    exact (List.mem_append.mp member).elim (head.closed term) (tail.closed term)
  denotes := by
    intro i inside
    by_cases inHead : i < left.length
    · rw [List.getElem_append_left inHead, List.getElem_append_left]
      exact head.denotes i inHead
    · have inTail : i - left.length < right.length := by
        simp only [List.length_append] at inside
        omega
      have afterHead : left.length ≤ i := by omega
      have afterTerms : head.terms.length ≤ i := by
        simpa only [head.arity] using afterHead
      rw [List.getElem_append_right afterHead,
        List.getElem_append_right afterTerms]
      simpa only [head.arity] using tail.denotes (i - left.length) inTail

end EnvAt

theorem CloseRecursiveFresh.left {outer types left right}
    (fresh : CloseRecursiveFresh outer types (left ++ right)) :
    CloseRecursiveFresh outer types left := by
  intro binding member
  exact fresh binding (List.mem_append_left right member)

theorem CloseRecursiveFresh.right {outer types left right}
    (fresh : CloseRecursiveFresh outer types (left ++ right)) :
    CloseRecursiveFresh outer types right := by
  intro binding member
  exact fresh binding (List.mem_append_right left member)

/-- The empty lexical environment is specializable in every lawful world. -/
def SpecializableEnvAt.empty (bound free : Runtime.TypeEnv) (sigma : Assign)
    (budget : Nat) : SpecializableEnvAt bound free sigma budget [] := by
  let empty : EnvAt bound free sigma budget [] :=
    { terms := []
      arity := rfl
      closed := by simp
      denotes := by simp }
  exact
    { fixed := empty
      ordinary := empty
      ordinaryTerms := rfl
      specialized := fun _ => empty
      specializedTerms := fun _ => rfl }

/-- Kripke monotonicity in the observation budget.  The runtime terms do not
    change when the observer is weakened. -/
def SpecializableEnvAt.down {bound free sigma small large env}
    (e : SpecializableEnvAt bound free sigma large env)
    (hb : Runtime.TypeEnv.Downward bound) (hf : Runtime.TypeEnv.Downward free)
    (le : small ≤ large) : SpecializableEnvAt bound free sigma small env where
  fixed := e.fixed.down hb hf le
  ordinary := e.ordinary.down hb hf le
  ordinaryTerms := e.ordinaryTerms
  specialized := fun world => (e.specialized world).down hb hf le
  specializedTerms := e.specializedTerms

/-- Independent specializable environments compose.  Every view uses the
    same left-to-right concatenation of the two canonical term vectors. -/
def SpecializableEnvAt.append {bound free sigma budget left right}
    (head : SpecializableEnvAt bound free sigma budget left)
    (tail : SpecializableEnvAt bound free sigma budget right) :
    SpecializableEnvAt bound free sigma budget (left ++ right) := by
  let fixed := EnvAt.append head.fixed tail.fixed
  let ordinary := EnvAt.append head.ordinary tail.ordinary
  have ordinaryEq : ordinaryBodyEnv left ++ ordinaryBodyEnv right =
      ordinaryBodyEnv (left ++ right) := by
    simp only [ordinaryBodyEnv, List.map_append]
  refine
    { fixed := ?_
      ordinary := ?_
      ordinaryTerms := ?_
      specialized := ?_
      specializedTerms := ?_ }
  · exact fixed
  · exact EnvAt.castEnv ordinaryEq ordinary
  · rw [EnvAt.castEnv_terms]
    simp only [ordinary, fixed, EnvAt.append, head.ordinaryTerms, tail.ordinaryTerms]
  · intro world
    let leftWorld : EnvSpecialization left :=
      { outer := world.outer
        types := world.types
        outerFinite := world.outerFinite
        countTarget := world.countTarget
        outerScope := world.outerScope
        typesLC := world.typesLC
        typeTarget := world.typeTarget
        typesScope := world.typesScope
        fresh := CloseRecursiveFresh.left world.fresh
        typesSupported := world.typesSupported }
    let rightWorld : EnvSpecialization right :=
      { outer := world.outer
        types := world.types
        outerFinite := world.outerFinite
        countTarget := world.countTarget
        outerScope := world.outerScope
        typesLC := world.typesLC
        typeTarget := world.typeTarget
        typesScope := world.typesScope
        fresh := CloseRecursiveFresh.right world.fresh
        typesSupported := world.typesSupported }
    have specializedEq :
        closeRecursiveEnv world.outer world.types left ++
            closeRecursiveEnv world.outer world.types right =
          closeRecursiveEnv world.outer world.types (left ++ right) := by
      simp only [closeRecursiveEnv, List.map_append]
    exact EnvAt.castEnv specializedEq
      (EnvAt.append (head.specialized leftWorld) (tail.specialized rightWorld))
  · intro world
    rw [EnvAt.castEnv_terms]
    simp only [EnvAt.append, head.specializedTerms, tail.specializedTerms, fixed]

end FHM.Bounds.RecursiveHMUniform
