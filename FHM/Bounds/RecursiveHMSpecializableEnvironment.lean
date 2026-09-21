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

/-- A closing world fixes the monomorphic bindings already present in its
lexical environment.  This is intentionally separate from
`CloseRecursiveFresh`: the latter is the broad static transport condition and
is vacuous on mono bindings. -/
def MonoStable (env : List Binding) (outer : Bindings) (types : Nat → BoundsTy) : Prop :=
  ∀ β, .mono β ∈ env → mapFree types (bounds outer β) = β

namespace MonoStable

theorem lookup_append (left right : Bindings) (i : Nat) :
    lookup (left ++ right) i = match lookup left i with
      | some c => some c
      | none => lookup right i := by
  induction left with
  | nil => rfl
  | cons head tail ih =>
      simp only [List.cons_append, lookup]
      split <;> simp only [*]

mutual
theorem count_append_fixed (pre outer : Bindings) {ids c}
    (hs : Scope.CountScoped ids c)
    (fresh : ∀ i ∈ ids, lookup pre i = none) :
    count (pre ++ outer) c = count outer c := by
  induction c with
  | lit | inf => rfl
  | var v =>
      cases v with
      | mk kind i =>
          cases kind with
          | inferable => rfl
          | rigid =>
              simp only [count, lookup_append]
              rw [fresh i hs]
  | add a b ha hb | mul a b ha hb | min a b ha hb | max a b ha hb =>
      simp only [count, ha hs.1, hb hs.2]
  | pred a ha => simp only [count, ha hs]

theorem bounds_append_fixed (pre outer : Bindings) {ids β}
    (hs : BoundsScoped ids β)
    (fresh : ∀ i ∈ ids, lookup pre i = none) :
    bounds (pre ++ outer) β = bounds outer β := by
  cases β with
  | prim | fvar | bvar => rfl
  | arrow a b => simp only [bounds, bounds_append_fixed pre outer hs.1 fresh,
      bounds_append_fixed pre outer hs.2 fresh]
  | list lo hi elem => simp only [bounds, count_append_fixed pre outer hs.1 fresh,
      count_append_fixed pre outer hs.2.1 fresh, bounds_append_fixed pre outer hs.2.2 fresh]
  | custom name as => exact congrArg (BoundsTy.custom name) (boundsList_append_fixed pre outer hs fresh)
termination_by sizeOf β

theorem boundsList_append_fixed (pre outer : Bindings) {ids as}
    (hs : ScopedScheme.BoundsListScoped ids as)
    (fresh : ∀ i ∈ ids, lookup pre i = none) :
    boundsList (pre ++ outer) as = boundsList outer as := by
  cases as with
  | nil => rfl
  | cons a as => simp only [boundsList, bounds_append_fixed pre outer hs.1 fresh,
      boundsList_append_fixed pre outer hs.2 fresh]
termination_by sizeOf as
end

mutual
theorem count_empty (c : Count) : count [] c = c := by
  induction c with
  | lit | inf => rfl
  | var v =>
      cases v with
      | mk kind i => cases kind <;> rfl
  | add a b ha hb | mul a b ha hb | min a b ha hb | max a b ha hb =>
      simp only [count, ha, hb]
  | pred a ha => simp only [count, ha]

theorem bounds_empty (β : BoundsTy) : bounds [] β = β := by
  cases β with
  | prim | fvar | bvar => rfl
  | arrow a b => simp only [bounds, bounds_empty a, bounds_empty b]
  | list lo hi elem => simp only [bounds, count_empty, bounds_empty elem]
  | custom name as => exact congrArg (BoundsTy.custom name) (boundsList_empty as)
termination_by sizeOf β

theorem boundsList_empty (as : List BoundsTy) : boundsList [] as = as := by
  cases as with
  | nil => rfl
  | cons a as => simp only [boundsList, bounds_empty a, boundsList_empty as]
termination_by sizeOf as
end

theorem empty (outer : Bindings) (types : Nat → BoundsTy) : MonoStable [] outer types := by
  intro β member
  simp at member

theorem left {outer types left right}
    (stable : MonoStable (left ++ right) outer types) : MonoStable left outer types := by
  intro β member
  exact stable β (List.mem_append_left right member)

theorem right {outer types left right}
    (stable : MonoStable (left ++ right) outer types) : MonoStable right outer types := by
  intro β member
  exact stable β (List.mem_append_right left member)

theorem of_parts {env outer types}
    (counts : ∀ β, .mono β ∈ env → bounds outer β = β)
    (free : ∀ β, .mono β ∈ env →
      ∀ i ∈ (Synth.BoundsTy.toTy β).freeVars, types i = .fvar i) :
    MonoStable env outer types := by
  intro β member
  rw [counts β member]
  exact SchemeSpecialization.fixed (free β member)

end MonoStable

theorem GeneralizedGroup.protectedMonoCounts
    {output metadata path captures premises bodyTypes outerEnv calleeΔ found caller}
    (group : GeneralizedGroup output metadata path captures premises bodyTypes outerEnv)
    (offset : Nat) (inside : offset < group.exports.length)
    (used : HMCountScheme.Use
      (HMCountSchemeClosure.close
        (group.selected offset inside).rhs.certificate.interface.scheme) calleeΔ found caller)
    (outer : Bindings) (ambientCounts : ∀ β, .mono β ∈ outerEnv → bounds outer β = β) :
    ∀ β, .mono β ∈ outerEnv → bounds (group.protectedRows offset inside used outer) β = β := by
  intro β member
  let selected := group.selected offset inside
  let source := group.sourceExitUse offset inside used
  have captured : BoundsScoped selected.rhs.certificate.interface.scheme.counts.captures β :=
    selected.rhs.captured.mono β (List.mem_append_right _ member)
  have fresh : ∀ i ∈ selected.rhs.certificate.interface.scheme.counts.captures,
      lookup (selected.rhs.certificate.interface.scheme.counts.quantified.zip source.counts) i = none := by
    intro i hi
    apply lookup_none
    rw [List.map_fst_zip (Nat.le_of_eq source.countInstance.arity)]
    exact source.countInstance.wf.2.1 i hi
  calc
    bounds (group.protectedRows offset inside used outer) β = bounds outer β := by
      exact MonoStable.bounds_append_fixed _ _ captured fresh
    _ = β := ambientCounts β member

theorem GeneralizedGroup.protectedMonoTypes
    {output metadata path captures premises bodyTypes outerEnv calleeΔ found caller}
    (group : GeneralizedGroup output metadata path captures premises bodyTypes outerEnv)
    (offset : Nat) (inside : offset < group.exports.length)
    (used : HMCountScheme.Use
      (HMCountSchemeClosure.close
        (group.selected offset inside).rhs.certificate.interface.scheme) calleeΔ found caller)
    (ambient : Nat → BoundsTy)
    (ambientTypes : ∀ β, .mono β ∈ outerEnv →
      ∀ i ∈ (Synth.BoundsTy.toTy β).freeVars, ambient i = .fvar i) :
    ∀ β, .mono β ∈ outerEnv →
      ∀ i ∈ (Synth.BoundsTy.toTy β).freeVars,
        group.protectedTypes offset inside used ambient i = .fvar i := by
  intro β member i free
  let selected := group.selected offset inside
  let source := group.sourceExitUse offset inside used
  let f := SchemeSpecialization.argument
    selected.rhs.certificate.implementation.opening.ids (SchemeUse.vector source.types)
  have fixed : f i = .fvar i :=
    (group.checked.exitMapOuterTypesFixed offset inside source.types).mono β member i free
  cases located : selected.rhs.certificate.implementation.opening.ids.idxOf? i with
  | none =>
      rw [group.protectedTypes_ambient offset inside used ambient i
        (List.idxOf?_eq_none_iff.mp located)]
      exact ambientTypes β member i free
  | some slot =>
      rw [group.protectedTypes_opening offset inside used ambient i slot located]
      simpa only [f, SchemeSpecialization.argument, located] using fixed

/-- Semantic recursive-specialization worlds strengthen the broad static
world with mono stability.  Static body-view transport continues to quantify
over `EnvSpecialization`; only runtime realizers demand this refinement. -/
structure StableEnvSpecialization (env : List Binding) extends EnvSpecialization env where
  monoCounts : ∀ β, .mono β ∈ env → bounds outer β = β
  monoTypes : ∀ β, .mono β ∈ env →
    ∀ i ∈ (Synth.BoundsTy.toTy β).freeVars, types i = .fvar i

theorem StableEnvSpecialization.monoStable {env} (world : StableEnvSpecialization env) :
    MonoStable env world.outer world.types :=
  MonoStable.of_parts world.monoCounts world.monoTypes

/-- A single closed term vector, observed through all three environments used
    by the recursive-body fundamental theorem.  The equalities are essential:
    merely having three unrelated inhabitants would not justify closing a
    nested group's source terms once and reusing them in every specialization. -/
structure SpecializableEnvAt (bound free : Runtime.TypeEnv) (sigma : Assign)
    (budget : Nat) (env : List Binding) where
  fixed : BodyEnvAt bound free sigma budget (fixedBodyEnv env)
  ordinary : BodyEnvAt bound free sigma budget (ordinaryBodyEnv env)
  ordinaryTerms : ordinary.terms = fixed.terms
  specialized : ∀ world : StableEnvSpecialization env,
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

/-- Extend every view by the same closed monomorphic term.  Stable worlds fix
    the new head's bound, so the ordinary `EnvAt.extendMono` witness can be
    reindexed to the recursively closed environment without changing syntax. -/
def SpecializableEnvAt.consMono {bound free sigma budget env}
    (e : SpecializableEnvAt bound free sigma budget env)
    (beta : BoundsTy) (term : Expr)
    (closed : term.varsBelow 0 = true)
    (safe : Runtime.TermAt bound free sigma budget beta term) :
    SpecializableEnvAt bound free sigma budget (.mono beta :: env) := by
  let fixed := e.fixed.extendMono beta term closed safe
  let ordinary := e.ordinary.extendMono beta term closed safe
  refine
    { fixed := fixed
      ordinary := ordinary
      ordinaryTerms := ?_
      specialized := ?_
      specializedTerms := ?_ }
  · simp only [ordinary, fixed, EnvAt.extendMono, e.ordinaryTerms]
  · intro world
    let tailWorld : StableEnvSpecialization env :=
      { outer := world.outer
        types := world.types
        outerFinite := world.outerFinite
        countTarget := world.countTarget
        outerScope := world.outerScope
        typesLC := world.typesLC
        typeTarget := world.typeTarget
        typesScope := world.typesScope
        fresh := by
          intro binding member
          exact world.fresh binding (List.mem_cons_of_mem _ member)
        typesSupported := world.typesSupported
        monoCounts := fun gamma member =>
          world.monoCounts gamma (List.mem_cons_of_mem _ member)
        monoTypes := fun gamma member =>
          world.monoTypes gamma (List.mem_cons_of_mem _ member) }
    let extended := (e.specialized tailWorld).extendMono beta term closed safe
    have stable : mapFree world.types (bounds world.outer beta) = beta :=
      world.monoStable beta List.mem_cons_self
    have envEq : .mono beta :: closeRecursiveEnv world.outer world.types env =
        closeRecursiveEnv world.outer world.types (.mono beta :: env) := by
      simp only [closeRecursiveEnv, List.map_cons, closeRecursiveBinding, stable]
    exact EnvAt.castEnv envEq extended
  · intro world
    rw [EnvAt.castEnv_terms]
    simp only [EnvAt.extendMono, fixed, e.specializedTerms]

/-- Extend by a branch's ordered monomorphic fields.  Pairing each demanded
    bound with its runtime value makes alignment explicit and avoids a partial
    zip operation. -/
def SpecializableEnvAt.prependMonos {bound free sigma budget env}
    (e : SpecializableEnvAt bound free sigma budget env) :
    (entries : List (BoundsTy × Expr)) →
    (∀ entry ∈ entries, entry.2.varsBelow 0 = true) →
    (∀ entry ∈ entries,
      Runtime.TermAt bound free sigma budget entry.1 entry.2) →
    SpecializableEnvAt bound free sigma budget
      (entries.map (fun entry => Binding.mono entry.1) ++ env)
  | [], _, _ => by simpa using e
  | entry :: rest, closed, safe => by
      have restClosed : ∀ item ∈ rest, item.2.varsBelow 0 = true :=
        fun item member => closed item (List.mem_cons_of_mem entry member)
      have restSafe : ∀ item ∈ rest,
          Runtime.TermAt bound free sigma budget item.1 item.2 :=
        fun item member => safe item (List.mem_cons_of_mem entry member)
      have tail := e.prependMonos rest restClosed restSafe
      simpa only [List.map_cons, List.cons_append] using
        tail.consMono entry.1 entry.2
          (closed entry List.mem_cons_self) (safe entry List.mem_cons_self)

@[simp] theorem SpecializableEnvAt.prependMonos_fixed_terms
    {bound free sigma budget env}
    (e : SpecializableEnvAt bound free sigma budget env)
    (entries : List (BoundsTy × Expr))
    (closed : ∀ entry ∈ entries, entry.2.varsBelow 0 = true)
    (safe : ∀ entry ∈ entries,
      Runtime.TermAt bound free sigma budget entry.1 entry.2) :
    (e.prependMonos entries closed safe).fixed.terms =
      entries.map Prod.snd ++ e.fixed.terms := by
  induction entries with
  | nil => rfl
  | cons entry rest ih =>
      simp only [SpecializableEnvAt.prependMonos, List.map_cons, List.cons_append,
        SpecializableEnvAt.consMono, EnvAt.extendMono]
      exact congrArg (List.cons entry.2) (ih _ _)

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
    let leftWorld : StableEnvSpecialization left :=
      { outer := world.outer
        types := world.types
        outerFinite := world.outerFinite
        countTarget := world.countTarget
        outerScope := world.outerScope
        typesLC := world.typesLC
        typeTarget := world.typeTarget
        typesScope := world.typesScope
        fresh := CloseRecursiveFresh.left world.fresh
        typesSupported := world.typesSupported
        monoCounts := fun β h => world.monoCounts β (List.mem_append_left right h)
        monoTypes := fun β h => world.monoTypes β (List.mem_append_left right h) }
    let rightWorld : StableEnvSpecialization right :=
      { outer := world.outer
        types := world.types
        outerFinite := world.outerFinite
        countTarget := world.countTarget
        outerScope := world.outerScope
        typesLC := world.typesLC
        typeTarget := world.typeTarget
        typesScope := world.typesScope
        fresh := CloseRecursiveFresh.right world.fresh
        typesSupported := world.typesSupported
        monoCounts := fun β h => world.monoCounts β (List.mem_append_right left h)
        monoTypes := fun β h => world.monoTypes β (List.mem_append_right left h) }
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
