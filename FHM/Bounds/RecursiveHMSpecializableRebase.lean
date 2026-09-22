import FHM.Bounds.RecursiveHMSpecializableEnvironment

/-! # Rebasing specializable semantic environments

A lexical semantic environment may be closed at one stable count/HM world and
then used as the lexical input to a nested derivation.  This module shows that
the resulting closed environment is itself specializable.  Later worlds are
composed with the base world, while the canonical runtime term vector remains
unchanged.
-/

namespace FHM.Bounds.RecursiveHMUniform

open RecursiveHMJudgement SchemeSpecialization CountSubstitution ScopedScheme

private theorem rebaseRowsScoped
    {rows worldRows : Bindings} {target worldTarget : List Nat}
    (rowsScope : ∀ row ∈ rows, Scope.CountScoped target row.2)
    (worldScope : ∀ row ∈ worldRows, Scope.CountScoped worldTarget row.2) :
    ∀ row ∈ CountAlgebra.compose worldRows rows,
      Scope.CountScoped (target ++ worldTarget) row.2 := by
  intro row member
  rcases List.mem_append.mp member with mapped | outer
  · obtain ⟨source, sourceMember, rfl⟩ := List.mem_map.mp mapped
    exact ScopedScheme.count_scoped (rowsScope source sourceMember)
      (fun entry entryMember =>
        HMInterpretation.count_mono (worldScope entry entryMember)
          (fun _ h => List.mem_append_right _ h))
      (fun i h _ => List.mem_append_left _ h)
  · exact HMInterpretation.count_mono (worldScope row outer)
      (fun _ h => List.mem_append_right _ h)

private theorem rebaseTypesLC
    {rows : Bindings} {types worldTypes : Nat → BoundsTy}
    (typesLC : ∀ i, (Synth.BoundsTy.toTy (types i)).IsLC)
    (worldLC : ∀ i, (Synth.BoundsTy.toTy (worldTypes i)).IsLC) :
    ∀ i, (Synth.BoundsTy.toTy
      (mapFree worldTypes (bounds rows (types i)))).IsLC := by
  intro i
  apply FreeAlgebra.bvars worldTypes worldLC
  simpa only [CountSubstitution.bounds_shape] using typesLC i

private theorem rebaseTypesScoped
    {rows : Bindings} {types worldTypes : Nat → BoundsTy}
    {target rowTarget typeTarget : List Nat}
    (typesScope : ∀ i, BoundsScoped target (types i))
    (rowsScope : ∀ row ∈ rows, Scope.CountScoped rowTarget row.2)
    (worldTypesScope : ∀ i, BoundsScoped typeTarget (worldTypes i)) :
    ∀ i, BoundsScoped ((target ++ rowTarget) ++ typeTarget)
      (mapFree worldTypes (bounds rows (types i))) := by
  intro i
  apply HMInterpretation.map_scope
  · exact ScopedScheme.bounds_scoped (typesScope i)
      (fun row member => HMInterpretation.count_mono (rowsScope row member)
        (fun _ h => List.mem_append_right _ h))
      (fun j h _ => List.mem_append_left _ h)
  · exact worldTypesScope

private theorem closeRecursiveBinding_compose
    (outer inner : Bindings) (f g : Nat → BoundsTy) (binding : Binding) :
    closeRecursiveBinding outer f (closeRecursiveBinding inner g binding) =
      closeRecursiveBinding (CountAlgebra.compose outer inner)
        (fun i => mapFree f (bounds outer (g i))) binding := by
  cases binding with
  | mono beta =>
      simp only [closeRecursiveBinding, CountAlgebra.bounds_compose,
        HMInterpretation.counts, HMInterpretation.compose]
  | recursive contract =>
      cases contract with
      | mk template hm fixed =>
          cases fixed
          simp [closeRecursiveBinding, closedMapCounts, closedMapTypes,
            RecursiveHMContract.Closed.ofFixed,
            HMCountSchemeClosure.interpretedCountCaptures_compose,
            HMCountSchemeClosure.interpretedTypeCaptures_map,
            CountAlgebra.bounds_compose, HMInterpretation.counts,
            HMInterpretation.compose]
  | recursiveClosure contract =>
      cases contract
      simp [closeRecursiveBinding, closedMapCounts, closedMapTypes,
        CountAlgebra.count_compose, CountAlgebra.bounds_compose,
        HMInterpretation.counts, HMInterpretation.compose]
  | exported scheme => rfl
  | closure scheme countCaptures typeCaptures =>
      simp [closeRecursiveBinding, CountAlgebra.count_compose,
        CountAlgebra.bounds_compose, HMInterpretation.counts,
        HMInterpretation.compose]

/-- Closing an environment in two stages is exactly closing it once in the
    composed count/HM world. -/
theorem closeRecursiveEnv_compose
    (outer inner : Bindings) (f g : Nat → BoundsTy) (env : List Binding) :
    closeRecursiveEnv outer f (closeRecursiveEnv inner g env) =
      closeRecursiveEnv (CountAlgebra.compose outer inner)
        (fun i => mapFree f (bounds outer (g i))) env := by
  unfold closeRecursiveEnv
  simp only [List.map_map, Function.comp_def]
  apply List.map_congr_left
  intro binding _
  exact closeRecursiveBinding_compose outer inner f g binding

/-- A recursively closed environment contains no raw recursive assumptions,
    so its ordinary body view is definitionally unchanged. -/
theorem ordinaryBodyEnv_closeRecursiveEnv
    (outer : Bindings) (types : Nat → BoundsTy) (env : List Binding) :
    ordinaryBodyEnv (closeRecursiveEnv outer types env) =
      closeRecursiveEnv outer types env := by
  unfold ordinaryBodyEnv closeRecursiveEnv
  simp only [List.map_map, Function.comp_def]
  apply List.map_congr_left
  intro binding _
  cases binding <;> rfl

/-- Compose an arbitrary static specialization world with a later stable
    specialization of the environment it closes.  Stability is required only
    of the later world: the result is a static transport world, so captured
    monomorphic bindings in the original environment need not be fixed by the
    base substitution. -/
def EnvSpecialization.compose {env : List Binding}
    (base : EnvSpecialization env)
    (later : StableEnvSpecialization
      (closeRecursiveEnv base.outer base.types env)) :
    EnvSpecialization env where
  outer := CountAlgebra.compose later.outer base.outer
  types := fun i => mapFree later.types (bounds later.outer (base.types i))
  outerFinite := CountAlgebra.finite_compose later.outerFinite base.outerFinite
  countTarget := base.countTarget ++ later.countTarget
  outerScope := rebaseRowsScoped base.outerScope later.outerScope
  typesLC := rebaseTypesLC base.typesLC later.typesLC
  typeTarget := (base.typeTarget ++ later.countTarget) ++ later.typeTarget
  typesScope := rebaseTypesScoped base.typesScope later.outerScope later.typesScope
  fresh := by
    intro binding member
    cases binding with
    | mono beta => trivial
    | recursive contract => trivial
    | recursiveClosure contract => trivial
    | closure scheme countCaptures typeCaptures => trivial
    | exported scheme =>
        have baseFresh := base.fresh (.exported scheme) member
        have closedMember : .exported scheme ∈
            closeRecursiveEnv base.outer base.types env := by
          exact List.mem_map_of_mem
            (f := closeRecursiveBinding base.outer base.types) member
        have laterFresh := later.fresh (.exported scheme) closedMember
        constructor
        · intro i captured
          rw [CountAlgebra.lookup_compose, baseFresh.1 i captured,
            laterFresh.1 i captured]
        · intro i free
          simp only [baseFresh.2 i free, CountSubstitution.bounds, mapFree]
          exact laterFresh.2 i free
  typesSupported := by
    intro i
    exact Runtime.Supported.types later.types later.typesSupported
      (Runtime.Supported.counts later.outer (base.typesSupported i))

@[simp] theorem EnvSpecialization.compose_outer {env : List Binding}
    (base : EnvSpecialization env)
    (later : StableEnvSpecialization
      (closeRecursiveEnv base.outer base.types env)) :
    (base.compose later).outer = CountAlgebra.compose later.outer base.outer := rfl

@[simp] theorem EnvSpecialization.compose_types {env : List Binding}
    (base : EnvSpecialization env)
    (later : StableEnvSpecialization
      (closeRecursiveEnv base.outer base.types env)) :
    (base.compose later).types i =
      mapFree later.types (bounds later.outer (base.types i)) := rfl

/-- The composed broad world closes the source environment to exactly the
    same bindings as closing first at `base` and then at `later`. -/
@[simp] theorem EnvSpecialization.closeRecursiveEnv_compose {env : List Binding}
    (base : EnvSpecialization env)
    (later : StableEnvSpecialization
      (closeRecursiveEnv base.outer base.types env)) :
    closeRecursiveEnv (base.compose later).outer (base.compose later).types env =
      closeRecursiveEnv later.outer later.types
        (closeRecursiveEnv base.outer base.types env) := by
  exact (FHM.Bounds.RecursiveHMUniform.closeRecursiveEnv_compose
    later.outer base.outer
    later.types base.types env).symm

private def StableEnvSpecialization.compose
    {env : List Binding} (base : StableEnvSpecialization env)
    (later : StableEnvSpecialization
      (closeRecursiveEnv base.outer base.types env)) :
    StableEnvSpecialization env := by
  let composedRows := CountAlgebra.compose later.outer base.outer
  let composedTypes := fun i => mapFree later.types (bounds later.outer (base.types i))
  let composedTarget := (base.typeTarget ++ later.countTarget) ++ later.typeTarget
  refine
    { outer := composedRows
      types := composedTypes
      outerFinite := CountAlgebra.finite_compose later.outerFinite base.outerFinite
      countTarget := base.countTarget ++ later.countTarget
      outerScope := rebaseRowsScoped base.outerScope later.outerScope
      typesLC := rebaseTypesLC base.typesLC later.typesLC
      typeTarget := composedTarget
      typesScope := rebaseTypesScoped base.typesScope later.outerScope later.typesScope
      fresh := ?_
      typesSupported := ?_
      monoCounts := ?_
      monoTypes := ?_ }
  · intro binding member
    cases binding with
    | mono beta => trivial
    | recursive contract => trivial
    | recursiveClosure contract => trivial
    | closure scheme countCaptures typeCaptures => trivial
    | exported scheme =>
        have baseFresh := base.fresh (.exported scheme) member
        have closedMember : .exported scheme ∈
            closeRecursiveEnv base.outer base.types env := by
          exact List.mem_map_of_mem (f := closeRecursiveBinding base.outer base.types) member
        have laterFresh := later.fresh (.exported scheme) closedMember
        constructor
        · intro i captured
          rw [CountAlgebra.lookup_compose, baseFresh.1 i captured,
            laterFresh.1 i captured]
        · intro i free
          simp only [composedTypes, baseFresh.2 i free, CountSubstitution.bounds,
            mapFree]
          exact laterFresh.2 i free
  · intro i
    exact Runtime.Supported.types later.types later.typesSupported
      (Runtime.Supported.counts later.outer (base.typesSupported i))
  · intro beta member
    have closedMember : .mono beta ∈
        closeRecursiveEnv base.outer base.types env := by
      have mapped := List.mem_map_of_mem
        (f := closeRecursiveBinding base.outer base.types) member
      simpa only [closeRecursiveBinding, base.monoStable beta member] using mapped
    simp only [composedRows, CountAlgebra.bounds_compose,
      base.monoCounts beta member]
    exact later.monoCounts beta closedMember
  · intro beta member i free
    have closedMember : .mono beta ∈
        closeRecursiveEnv base.outer base.types env := by
      have mapped := List.mem_map_of_mem
        (f := closeRecursiveBinding base.outer base.types) member
      simpa only [closeRecursiveBinding, base.monoStable beta member] using mapped
    simp only [composedTypes, base.monoTypes beta member i free,
      CountSubstitution.bounds, mapFree]
    exact later.monoTypes beta closedMember i free

/-- Rebase a specializable environment at one stable world.  The closed
    environment supports every later stable specialization by composing that
    later world with the base, and all views retain the original term vector. -/
def SpecializableEnvAt.rebase {bound free sigma budget env}
    (lexical : SpecializableEnvAt bound free sigma budget env)
    (base : StableEnvSpecialization env) :
    SpecializableEnvAt bound free sigma budget
      (closeRecursiveEnv base.outer base.types env) := by
  let canonical := lexical.specialized base
  refine
    { fixed := canonical
      ordinary := EnvAt.castEnv (ordinaryBodyEnv_closeRecursiveEnv _ _ _).symm canonical
      ordinaryTerms := ?_
      specialized := ?_
      specializedTerms := ?_ }
  · rw [EnvAt.castEnv_terms]
  · intro later
    let composed := StableEnvSpecialization.compose base later
    exact EnvAt.castEnv
      (closeRecursiveEnv_compose later.outer base.outer later.types base.types env).symm
      (lexical.specialized composed)
  · intro later
    rw [EnvAt.castEnv_terms]
    exact (lexical.specializedTerms
      (StableEnvSpecialization.compose base later)).trans
        (lexical.specializedTerms base).symm

@[simp] theorem SpecializableEnvAt.rebase_fixed_terms {bound free sigma budget env}
    (lexical : SpecializableEnvAt bound free sigma budget env)
    (base : StableEnvSpecialization env) :
    (lexical.rebase base).fixed.terms = lexical.fixed.terms := by
  exact lexical.specializedTerms base

#print axioms closeRecursiveEnv_compose
#print axioms EnvSpecialization.compose
#print axioms EnvSpecialization.closeRecursiveEnv_compose
#print axioms SpecializableEnvAt.rebase
#print axioms SpecializableEnvAt.rebase_fixed_terms

end FHM.Bounds.RecursiveHMUniform
