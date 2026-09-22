import FHM.Bounds.RecursiveHMSpecializableEnvironment

/-! # Protected-exit rebasing of lexical tails

The member-local count prefix installed by a closed generalized exit is
invisible to the checked lexical tail.  This is a checker invariant: fixed
count data is scoped by the selected member's captures, while recursive
scheme captures are fresh for its quantified rows.

The analogous statement for the protected HM map needs an explicit stability
hypothesis.  An arbitrary `EnvSpecialization` may assign a member-opening
identity nontrivially, whereas `protectedTypes` deliberately replaces that
identity by the selected source argument.
-/

namespace FHM.Bounds.RecursiveHMUniform

open RecursiveHMJudgement SchemeSpecialization CountSubstitution ScopedScheme

private theorem map_eq_of_pointwise {α β} (f g : α → β) (xs : List α)
    (same : ∀ x ∈ xs, f x = g x) : xs.map f = xs.map g := by
  exact List.map_congr_left same

private theorem mem_of_mem_eraseDups {a : Nat} {l : List Nat}
    (h : a ∈ l.eraseDups) : a ∈ l := by
  have go : ∀ n, ∀ (l : List Nat), l.length = n → ∀ a, a ∈ l.eraseDups → a ∈ l := by
    intro n
    refine Nat.strongRecOn n (motive := fun n =>
      ∀ (l : List Nat), l.length = n → ∀ a, a ∈ l.eraseDups → a ∈ l) fun n ih => ?_
    intro l hn a member
    match l with
    | [] => cases member
    | b :: rest =>
        simp only [List.length_cons] at hn
        simp only [List.eraseDups_cons, List.mem_cons] at member
        rcases member with rfl | tail
        · simp
        · have smaller : (rest.filter (fun x => !x == b)).length < n := by
            rw [← hn]
            exact Nat.lt_add_one_of_le (List.length_filter_le _ rest)
          exact List.mem_cons_of_mem b
            (List.mem_of_mem_filter (ih _ smaller _ rfl _ tail))
  exact go l.length l rfl a h

private theorem protectedTailBindingCounts
    {output metadata path captures premises bodyTypes outerEnv calleeΔ found caller}
    (group : GeneralizedGroup output metadata path captures premises bodyTypes outerEnv)
    (offset : Nat) (inside : offset < group.exports.length)
    (used : HMCountScheme.Use
      (HMCountSchemeClosure.close
        (group.selected offset inside).rhs.certificate.interface.scheme) calleeΔ found caller)
    (outer : Bindings) (types : Nat → BoundsTy) (binding : Binding)
    (member : binding ∈ outerEnv) :
    closeRecursiveBinding (group.protectedRows offset inside used outer) types binding =
      closeRecursiveBinding outer types binding := by
  let selected := group.selected offset inside
  let source := group.sourceExitUse offset inside used
  let localRows := selected.rhs.certificate.interface.scheme.counts.quantified.zip source.counts
  have prefixFresh : ∀ i ∈ selected.rhs.certificate.interface.scheme.counts.captures,
      lookup localRows i = none := by
    intro i hi
    apply lookup_none
    rw [List.map_fst_zip (Nat.le_of_eq source.countInstance.arity)]
    exact source.countInstance.wf.2.1 i hi
  have countFixed {c : Count} (hscope : Scope.CountScoped
      selected.rhs.certificate.interface.scheme.counts.captures c) :
      count (localRows ++ outer) c = count outer c :=
    MonoStable.count_append_fixed localRows outer hscope prefixFresh
  have boundsFixed {beta : BoundsTy} (hscope : BoundsScoped
      selected.rhs.certificate.interface.scheme.counts.captures beta) :
      bounds (localRows ++ outer) beta = bounds outer beta :=
    MonoStable.bounds_append_fixed localRows outer hscope prefixFresh
  have recursiveCaptureFresh {c : Contract}
      (hc : Binding.recursive c ∈ outerEnv) :
      ∀ i ∈ c.template.counts.captures, lookup localRows i = none := by
    intro i hi
    apply lookup_none
    rw [List.map_fst_zip (Nat.le_of_eq source.countInstance.arity)]
    exact selected.rhs.countFresh c (List.mem_append_right _ hc) i hi
  change closeRecursiveBinding (localRows ++ outer) types binding = _
  cases binding with
  | mono beta =>
      simp only [closeRecursiveBinding]
      rw [boundsFixed (selected.rhs.captured.mono beta
        (List.mem_append_right _ member))]
  | recursive contract =>
      simp only [closeRecursiveBinding, RecursiveHMContract.Closed.ofFixed]
      have fixedTypes :
          (contract.fixed.types.map (bounds (localRows ++ outer))).map (mapFree types) =
            (contract.fixed.types.map (bounds outer)).map (mapFree types) := by
        congr 1
        apply map_eq_of_pointwise
        intro beta betaMember
        exact boundsFixed (selected.rhs.captured.recursive contract
          (List.mem_append_right _ member) beta betaMember)
      have countCaptures :
          HMCountSchemeClosure.interpretedCountCaptures (localRows ++ outer) contract.template =
            HMCountSchemeClosure.interpretedCountCaptures outer contract.template := by
        unfold HMCountSchemeClosure.interpretedCountCaptures
        apply map_eq_of_pointwise
        intro i hi
        have hi' : i ∈ contract.template.counts.captures :=
          mem_of_mem_eraseDups (by simpa [HMCountSchemeClosure.countCaptures] using hi)
        exact MonoStable.count_append_fixed localRows outer
          (by simp only [Scope.CountScoped]; exact hi')
          (recursiveCaptureFresh member)
      congr
  | recursiveClosure contract =>
      simp only [closeRecursiveBinding, closedMapCounts, closedMapTypes]
      have fixedTypes : contract.fixedTypes.map (bounds (localRows ++ outer)) =
          contract.fixedTypes.map (bounds outer) := by
        apply map_eq_of_pointwise
        intro beta betaMember
        exact boundsFixed (selected.rhs.captured.recursiveClosureFixedTypes contract
          (List.mem_append_right _ member) beta betaMember)
      have countCaptures : contract.countCaptures.map (count (localRows ++ outer)) =
          contract.countCaptures.map (count outer) := by
        apply map_eq_of_pointwise
        intro c countMember
        exact countFixed (selected.rhs.captured.recursiveClosureCounts contract
          (List.mem_append_right _ member) c countMember)
      have typeCaptures : contract.typeCaptures.map (bounds (localRows ++ outer)) =
          contract.typeCaptures.map (bounds outer) := by
        apply map_eq_of_pointwise
        intro beta betaMember
        exact boundsFixed (selected.rhs.captured.recursiveClosureTypeCaptures contract
          (List.mem_append_right _ member) beta betaMember)
      congr
  | exported scheme => rfl
  | closure scheme countCaptures typeCaptures =>
      simp only [closeRecursiveBinding]
      have counts : countCaptures.map (count (localRows ++ outer)) =
          countCaptures.map (count outer) := by
        apply map_eq_of_pointwise
        intro c countMember
        exact countFixed (selected.rhs.captured.closureCounts scheme countCaptures typeCaptures
          (List.mem_append_right _ member) c countMember)
      have mappedTypes : typeCaptures.map (bounds (localRows ++ outer)) =
          typeCaptures.map (bounds outer) := by
        apply map_eq_of_pointwise
        intro beta betaMember
        exact boundsFixed (selected.rhs.captured.closureTypes scheme countCaptures typeCaptures
          (List.mem_append_right _ member) beta betaMember)
      rw [counts, mappedTypes]

/-- The protected member-local count prefix is invisible to every binding in
    the checked lexical tail.  The protected HM interpretation is retained on
    both sides because a broad world need not fix member-opening identities. -/
theorem GeneralizedGroup.closeRecursiveEnv_protectedRows_tail
    {output metadata path captures premises bodyTypes outerEnv calleeΔ found caller}
    (group : GeneralizedGroup output metadata path captures premises bodyTypes outerEnv)
    (offset : Nat) (inside : offset < group.exports.length)
    (used : HMCountScheme.Use
      (HMCountSchemeClosure.close
        (group.selected offset inside).rhs.certificate.interface.scheme) calleeΔ found caller)
    (base : EnvSpecialization outerEnv) :
    closeRecursiveEnv (group.protectedRows offset inside used base.outer)
        (group.protectedTypes offset inside used base.types) outerEnv =
      closeRecursiveEnv base.outer
        (group.protectedTypes offset inside used base.types) outerEnv := by
  unfold closeRecursiveEnv
  apply List.map_congr_left
  intro binding member
  exact protectedTailBindingCounts group offset inside used base.outer _ binding member

/-- The exact remaining obligation for the full protected-tail rebase is HM
    agreement.  This corollary is intentionally not built into
    `EnvSpecialization`: a broad world is allowed to interpret opening
    identities nontrivially. -/
theorem GeneralizedGroup.closeRecursiveEnv_protected_tail_of_types_eq
    {output metadata path captures premises bodyTypes outerEnv calleeΔ found caller}
    (group : GeneralizedGroup output metadata path captures premises bodyTypes outerEnv)
    (offset : Nat) (inside : offset < group.exports.length)
    (used : HMCountScheme.Use
      (HMCountSchemeClosure.close
        (group.selected offset inside).rhs.certificate.interface.scheme) calleeΔ found caller)
    (base : EnvSpecialization outerEnv)
    (typesEq : group.protectedTypes offset inside used base.types = base.types) :
    closeRecursiveEnv (group.protectedRows offset inside used base.outer)
        (group.protectedTypes offset inside used base.types) outerEnv =
      closeRecursiveEnv base.outer base.types outerEnv := by
  rw [group.closeRecursiveEnv_protectedRows_tail offset inside used base, typesEq]

#print axioms GeneralizedGroup.closeRecursiveEnv_protectedRows_tail
#print axioms GeneralizedGroup.closeRecursiveEnv_protected_tail_of_types_eq

end FHM.Bounds.RecursiveHMUniform
