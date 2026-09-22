import FHM.Bounds.RecursiveHMUniform

/-! # Freshness of closure-normal recursive environments

The combined recursive-closing boundary promotes raw recursive contracts to
`recursiveClosure` entries.  Generalized bindings crossing a lexical boundary
must already be represented by `closure`; a raw `exported` entry at that point
would still retain source count and type captures.
-/

namespace FHM.Bounds.RecursiveHMUniform

open RecursiveHMJudgement CountSubstitution

/-- An environment is closure-normal when it contains no legacy raw generalized
    export. Other bindings, including the raw contracts of the SCC currently
    being tied, are permitted. -/
def ClosureNormal (env : List Binding) : Prop :=
  ∀ s, .exported s ∉ env

/-- The internal environment of a generalized group is fresh for the combined
    recursive-closing boundary whenever its captured outer environment is
    closure-normal. The current SCC's raw recursive prefix is vacuous for
    `CloseRecursiveFresh`; closure-normality eliminates the only sensitive
    outer case. -/
theorem GeneralizedGroup.internalCloseRecursiveFresh
    {output metadata path captures premises bodyTypes outerEnv}
    (group : GeneralizedGroup output metadata path captures premises bodyTypes outerEnv)
    (outer : Bindings) (f : Nat → BoundsTy)
    (normal : ClosureNormal outerEnv) :
    CloseRecursiveFresh outer f group.internal := by
  intro binding member
  rcases List.mem_append.mp member with internal | external
  · rcases List.mem_map.mp internal with ⟨contract, _, rfl⟩
    trivial
  · cases binding with
    | mono _ => trivial
    | recursive _ => trivial
    | recursiveClosure _ => trivial
    | exported scheme => exact (normal scheme external).elim
    | closure _ _ _ => trivial

/-- Prepending the current SCC's raw recursive contracts cannot introduce a
    sensitive binding.  Consequently the internal environment is fresh under
    any world in which its captured lexical tail is already fresh. -/
theorem GeneralizedGroup.internalCloseRecursiveFreshOfTail
    {output metadata path captures premises bodyTypes outerEnv}
    (group : GeneralizedGroup output metadata path captures premises bodyTypes outerEnv)
    (outer : Bindings) (f : Nat → BoundsTy)
    (tailFresh : CloseRecursiveFresh outer f outerEnv) :
    CloseRecursiveFresh outer f group.internal := by
  intro binding member
  rcases List.mem_append.mp member with internal | external
  · rcases List.mem_map.mp internal with ⟨contract, _, rfl⟩
    trivial
  · exact tailFresh binding external

/-- A selected member's protected interpretation preserves freshness of the
    checked lexical tail.  Count protection follows from the certificate's
    exported-capture freshness, and HM protection from its exported-body
    opening freshness. -/
theorem GeneralizedGroup.protectedCloseRecursiveFreshTail
    {output metadata path captures premises bodyTypes outerEnv calleeDelta found caller}
    (group : GeneralizedGroup output metadata path captures premises bodyTypes outerEnv)
    (offset : Nat) (inside : offset < group.exports.length)
    (used : HMCountScheme.Use
      (HMCountSchemeClosure.close
        (group.selected offset inside).rhs.certificate.interface.scheme)
      calleeDelta found caller)
    (outer : Bindings) (ambient : Nat → BoundsTy)
    (tailFresh : CloseRecursiveFresh outer ambient outerEnv) :
    CloseRecursiveFresh
      (group.protectedRows offset inside used outer)
      (group.protectedTypes offset inside used ambient) outerEnv := by
  intro binding member
  cases binding with
  | mono _ => trivial
  | recursive _ => trivial
  | recursiveClosure _ => trivial
  | closure _ _ _ => trivial
  | exported scheme =>
      have sourceFresh := tailFresh (.exported scheme) member
      constructor
      · intro i captured
        apply ScopedScheme.lookup_none
        intro keyMember
        obtain ⟨row, rowMember, rfl⟩ := List.mem_map.mp keyMember
        rcases List.mem_append.mp rowMember with headMember | external
        · have keyMember : row.1 ∈
              (group.selected offset inside).rhs.certificate.interface.scheme.counts.quantified := by
            rw [← List.map_fst_zip
              (Nat.le_of_eq (group.sourceExitUse offset inside used).countInstance.arity)]
            exact List.mem_map.mpr ⟨row, headMember, rfl⟩
          exact (group.selected offset inside).rhs.certificate.implementation.exportCountFresh
            scheme (List.mem_append_right _ member) row.1 captured keyMember
        · exact (ScopedScheme.lookup_none_iff.mp (sourceFresh.1 row.1 captured))
            (List.mem_map.mpr ⟨row, external, rfl⟩)
      · intro i free
        calc
          group.protectedTypes offset inside used ambient i = ambient i := by
            apply group.protectedTypes_ambient offset inside used ambient i
            intro opened
            exact (group.selected offset inside).rhs.certificate.implementation.exportTypeFresh
              scheme (List.mem_append_right _ member) i opened free
          _ = .fvar i := sourceFresh.2 i free

#print axioms GeneralizedGroup.internalCloseRecursiveFresh
#print axioms GeneralizedGroup.internalCloseRecursiveFreshOfTail
#print axioms GeneralizedGroup.protectedCloseRecursiveFreshTail

end FHM.Bounds.RecursiveHMUniform
