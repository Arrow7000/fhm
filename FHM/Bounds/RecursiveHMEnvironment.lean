import FHM.Bounds.RecursiveHMSigned

/-! Count-environment reconciliation for joint recursive HM/count certificates.
The callee's fixed HM vector initially contains opaque HM identities and captured
counts, not the current member's universally instantiated count coordinates.
That property must be proved before erasing an environment transport from `use`.
-/

namespace FHM.Bounds.RecursiveHMEnvironment

open RecursiveHMJudgement CountSubstitution ScopedScheme

private theorem fixed_ext {s found} {a b : RecursiveHMContract.Fixed s found}
    (types : a.types = b.types) : a = b := by
  cases a
  cases b
  cases types
  rfl

def Captured (ids : List Nat) (env : List RecursiveHMJudgement.Binding) : Prop :=
  (∀ β, .mono β ∈ env → BoundsScoped ids β) ∧
    ∀ c, .recursive c ∈ env → ∀ β ∈ c.fixed.types, BoundsScoped ids β

/-- Callee templates need not be count-substituted to instantiate one member's
    RHS. The fixed HM vector remains unchanged when its counts are captures. -/
theorem fixed (rows : Bindings) {ids env} (captures : Captured ids env)
    (keep : ∀ i ∈ ids, lookup rows i = none) : env.map (mapCountBinding rows) = env := by
  conv_rhs => rw [← List.map_id env]
  apply List.map_congr_left
  intro b hb
  cases b with
  | mono β => exact congrArg Binding.mono (CountTransport.bounds_fixed rows (captures.1 β hb) keep)
  | recursive c =>
      have hv : c.fixed.mapCounts rows = c.fixed := by
        apply fixed_ext
        change c.fixed.types.map (bounds rows) = c.fixed.types
        conv_rhs => rw [← List.map_id c.fixed.types]
        apply List.map_congr_left
        intro β hβ
        exact CountTransport.bounds_fixed rows (captures.2 c hb β hβ) keep
      change Binding.recursive ⟨c.template, c.hm, c.fixed.mapCounts rows⟩ = Binding.recursive c
      rw [hv]

/-- A member's scoped finite instantiation leaves the common recursive count
    environment intact when the group has checked the captured-vector property. -/
theorem instantiated {s : ScopedScheme.Scheme} {counts caller env}
    (inst : Instance s counts caller) (captures : Captured s.captures env) :
    env.map (mapCountBinding (s.quantified.zip counts)) = env := by
  apply fixed _ captures
  intro i hi
  apply lookup_none
  rw [List.map_fst_zip (Nat.le_of_eq inst.arity)]
  exact inst.wf.2.1 i hi

/-- Captured-vector evidence is automatic for opaque HM openings; source
    count interval payloads stay in their closed template, not in the vector. -/
theorem opaqueVector {s found typeCaptures} (o : HMCountScheme.Opening s found typeCaptures)
    (ids : List Nat) : ∀ β ∈ (RecursiveHMContract.fromOpaque o).types, BoundsScoped ids β := by
  intro β hβ
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp hβ
  trivial

#print axioms fixed
#print axioms instantiated
#print axioms opaqueVector

end FHM.Bounds.RecursiveHMEnvironment
