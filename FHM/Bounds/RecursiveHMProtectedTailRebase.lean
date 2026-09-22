import FHM.Bounds.RecursiveHMSpecializableEnvironment

/-! # Protected-exit rebasing of lexical tails

The member-local count prefix installed by a closed generalized exit is
invisible to the checked lexical tail.  This is a checker invariant: fixed
count data is scoped by the selected member's captures, while recursive
scheme captures are fresh for its quantified rows.

The protected HM override is likewise invisible on the finite support of the
lexical tail.  Checked outer-type representation connects every stored HM
component to the selected member's opening-freshness proof; raw recursive
scheme captures use the certificate's direct `typeFresh` invariant.
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

mutual
private theorem mapFree_eq_of_agree (f g : Nat → BoundsTy) (beta : BoundsTy)
    (same : ∀ i ∈ (Synth.BoundsTy.toTy beta).freeVars, f i = g i) :
    mapFree f beta = mapFree g beta := by
  cases beta with
  | prim | bvar => rfl
  | fvar i =>
      exact same i (by simp [Synth.BoundsTy.toTy, Ty.freeVars])
  | arrow a b =>
      simp only [mapFree]
      congr 1
      · exact mapFree_eq_of_agree f g a
          (fun i hi => same i (by simp [Synth.BoundsTy.toTy, Ty.freeVars, hi]))
      · exact mapFree_eq_of_agree f g b
          (fun i hi => same i (by simp [Synth.BoundsTy.toTy, Ty.freeVars, hi]))
  | list lo hi elem =>
      exact congrArg (BoundsTy.list lo hi) (mapFree_eq_of_agree f g elem
        (fun i hi => same i (by simpa [Synth.BoundsTy.toTy, listTy,
          Ty.freeVars, TyList.freeVars] using hi)))
  | custom name args =>
      exact congrArg (BoundsTy.custom name)
        (mapFreeList_eq_of_agree f g args
          (by simpa only [Synth.BoundsTy.toTy, Ty.freeVars] using same))
termination_by sizeOf beta

private theorem mapFreeList_eq_of_agree (f g : Nat → BoundsTy) (args : List BoundsTy)
    (same : ∀ i ∈ TyList.freeVars (args.map Synth.BoundsTy.toTy), f i = g i) :
    SchemeSpecialization.mapFreeList f args = SchemeSpecialization.mapFreeList g args := by
  cases args with
  | nil => rfl
  | cons head tail =>
      simp only [SchemeSpecialization.mapFreeList]
      congr 1
      · exact mapFree_eq_of_agree f g head
          (fun i hi => same i (by simp [TyList.freeVars, hi]))
      · exact mapFreeList_eq_of_agree f g tail
          (fun i hi => same i (by simp [TyList.freeVars, hi]))
termination_by sizeOf args
end

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

/-- Every free identity represented by the checked outer type guard is absent
    from the selected member's opening block, so the protected map falls
    through to its ambient map there. -/
theorem GeneralizedGroup.protectedTypes_outerAmbient
    {output metadata path captures premises bodyTypes outerEnv calleeΔ found caller}
    (group : GeneralizedGroup output metadata path captures premises bodyTypes outerEnv)
    (offset : Nat) (inside : offset < group.exports.length)
    (used : HMCountScheme.Use
      (HMCountSchemeClosure.close
        (group.selected offset inside).rhs.certificate.interface.scheme) calleeΔ found caller)
    (ambient : Nat → BoundsTy) {t : Ty} (member : t ∈ bodyTypes) {i : Nat}
    (free : i ∈ t.freeVars) :
    group.protectedTypes offset inside used ambient i = ambient i := by
  apply group.protectedTypes_ambient offset inside used ambient i
  intro owned
  let selected := group.selected offset inside
  exact selected.member.reconciled.opening.fresh i owned t
    (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_append_left _
      (List.mem_cons_of_mem _ (List.mem_append_right _ member))))) free

private theorem protectedTailBindingTypes
    {output metadata path captures premises bodyTypes outerEnv calleeΔ found caller}
    (group : GeneralizedGroup output metadata path captures premises bodyTypes outerEnv)
    (offset : Nat) (inside : offset < group.exports.length)
    (used : HMCountScheme.Use
      (HMCountSchemeClosure.close
        (group.selected offset inside).rhs.certificate.interface.scheme) calleeΔ found caller)
    (outer : Bindings) (ambient : Nat → BoundsTy) (binding : Binding)
    (member : binding ∈ outerEnv) :
    closeRecursiveBinding outer (group.protectedTypes offset inside used ambient) binding =
      closeRecursiveBinding outer ambient binding := by
  let selected := group.selected offset inside
  let protectedMap := group.protectedTypes offset inside used ambient
  have mapFixed {beta : BoundsTy} (represented : Synth.BoundsTy.toTy beta ∈ bodyTypes) :
      mapFree protectedMap beta = mapFree ambient beta := by
    apply mapFree_eq_of_agree
    intro i free
    exact group.protectedTypes_outerAmbient offset inside used ambient represented free
  have mapBoundsFixed {beta : BoundsTy}
      (represented : Synth.BoundsTy.toTy beta ∈ bodyTypes) :
      mapFree protectedMap (bounds outer beta) = mapFree ambient (bounds outer beta) := by
    apply mapFree_eq_of_agree
    intro i free
    apply group.protectedTypes_outerAmbient offset inside used ambient represented
    simpa only [CountSubstitution.bounds_shape] using free
  cases binding with
  | mono beta =>
      simp only [closeRecursiveBinding]
      exact congrArg Binding.mono
        (mapBoundsFixed (group.checked.outerMonoRepresented beta member))
  | recursive contract =>
      simp only [closeRecursiveBinding, RecursiveHMContract.Closed.ofFixed]
      have fixedTypes :
          (contract.fixed.types.map (bounds outer)).map (mapFree protectedMap) =
            (contract.fixed.types.map (bounds outer)).map (mapFree ambient) := by
        apply map_eq_of_pointwise
        intro beta betaMember
        obtain ⟨sourceBeta, sourceMember, rfl⟩ := List.mem_map.mp betaMember
        exact mapBoundsFixed
          (group.checked.outerFixedRepresented contract member sourceBeta sourceMember)
      have typeCaptures :
          HMCountSchemeClosure.interpretedTypeCaptures protectedMap contract.template =
            HMCountSchemeClosure.interpretedTypeCaptures ambient contract.template := by
        unfold HMCountSchemeClosure.interpretedTypeCaptures
        apply map_eq_of_pointwise
        intro i hi
        have free : i ∈ contract.template.hm.body.freeVars :=
          mem_of_mem_eraseDups (by simpa [HMCountSchemeClosure.typeCaptures] using hi)
        apply group.protectedTypes_ambient offset inside used ambient i
        intro owned
        exact selected.rhs.certificate.implementation.typeFresh contract
          (List.mem_append_right _ member) i owned free
      congr
  | recursiveClosure contract =>
      simp only [closeRecursiveBinding, closedMapCounts, closedMapTypes]
      have fixedTypes :
          (contract.fixedTypes.map (bounds outer)).map (mapFree protectedMap) =
            (contract.fixedTypes.map (bounds outer)).map (mapFree ambient) := by
        apply map_eq_of_pointwise
        intro beta betaMember
        obtain ⟨sourceBeta, sourceMember, rfl⟩ := List.mem_map.mp betaMember
        exact mapBoundsFixed
          (group.checked.outerClosedFixedRepresented contract member sourceBeta sourceMember)
      have typeCaptures :
          (contract.typeCaptures.map (bounds outer)).map (mapFree protectedMap) =
            (contract.typeCaptures.map (bounds outer)).map (mapFree ambient) := by
        apply map_eq_of_pointwise
        intro beta betaMember
        obtain ⟨sourceBeta, sourceMember, rfl⟩ := List.mem_map.mp betaMember
        exact mapBoundsFixed
          (group.checked.outerClosedCaptureRepresented contract member sourceBeta sourceMember)
      congr
  | exported scheme => rfl
  | closure scheme countCaptures typeCaptures =>
      simp only [closeRecursiveBinding]
      have mappedTypes :
          (typeCaptures.map (bounds outer)).map (mapFree protectedMap) =
            (typeCaptures.map (bounds outer)).map (mapFree ambient) := by
        apply map_eq_of_pointwise
        intro beta betaMember
        obtain ⟨sourceBeta, sourceMember, rfl⟩ := List.mem_map.mp betaMember
        exact mapBoundsFixed
          (group.checked.outerClosureRepresented scheme countCaptures typeCaptures member
            sourceBeta sourceMember)
      rw [mappedTypes]

/-- The protected member-local count prefix is invisible to every binding in
    the checked lexical tail. -/
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

/-- A selected closed exit leaves the entire already-closed lexical tail
    unchanged.  Count invisibility follows from capture scope/freshness; HM
    invisibility follows from checked outer representation and opening
    freshness.  No stability strengthening of the broad base world is needed. -/
theorem GeneralizedGroup.closeRecursiveEnv_protected_tail
    {output metadata path captures premises bodyTypes outerEnv calleeΔ found caller}
    (group : GeneralizedGroup output metadata path captures premises bodyTypes outerEnv)
    (offset : Nat) (inside : offset < group.exports.length)
    (used : HMCountScheme.Use
      (HMCountSchemeClosure.close
        (group.selected offset inside).rhs.certificate.interface.scheme) calleeΔ found caller)
    (base : EnvSpecialization outerEnv) :
    closeRecursiveEnv (group.protectedRows offset inside used base.outer)
        (group.protectedTypes offset inside used base.types) outerEnv =
      closeRecursiveEnv base.outer base.types outerEnv := by
  rw [group.closeRecursiveEnv_protectedRows_tail offset inside used base]
  unfold closeRecursiveEnv
  apply List.map_congr_left
  intro binding member
  exact protectedTailBindingTypes group offset inside used base.outer base.types binding member

#print axioms GeneralizedGroup.closeRecursiveEnv_protectedRows_tail
#print axioms GeneralizedGroup.protectedTypes_outerAmbient
#print axioms GeneralizedGroup.closeRecursiveEnv_protected_tail

end FHM.Bounds.RecursiveHMUniform
