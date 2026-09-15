import FHM.Bounds.HMReconciliation
import FHM.Bounds.RecursiveHMUniversal
import FHM.Bounds.RecursiveHMSigned
import FHM.Bounds.RecursiveHMWalk

/-! Checked symbolic RHS results become universal certificates without losing
their original source HM interpretation. Closed recursive templates still need
explicit count independence; metadata decoding alone never certifies an RHS. -/

namespace FHM.Bounds.RecursiveHMReconciled

open RecursiveHMJudgement ScopedScheme

def fromChecked {output path node schemes site s captures env}
    (checked : @HMReconciliation.Checked output path node schemes site s captures)
    (rhs : HMReconciliation.RHSChecked checked env)
    (represented : ∀ c, .recursive c ∈ env → c.template.hm.body ∈ captures)
    (exportsRepresented : ∀ t, .exported t ∈ env → t.hm.body ∈ captures)
    (countFresh : ∀ c, .recursive c ∈ env → ∀ i ∈ c.template.counts.captures,
      i ∉ s.counts.quantified)
    (exportCountFresh : ∀ t, .exported t ∈ env → ∀ i ∈ t.counts.captures,
      i ∉ s.counts.quantified) :
    RecursiveHMUniversal.Certified s (node.view checked.interpretation) (node.original :: captures)
      (env.map (mapBinding checked.interpretation checked.interpretationLC))
      node.inner.stripFound checked.interpretation := by
  refine
    { opening := checked.opening
      actual := rhs.typed.actual
      shape := ?_
      actualScope := rhs.typed.checked.inScope
      typing := rhs.typed.derivation
      inclusion := rhs.inclusion
      typeFresh := ?_
      exportTypeFresh := ?_
      countFresh := ?_
      exportCountFresh := ?_ }
  · rw [← rhs.typed.checked.shape]
    exact (FreeAlgebra.shape_erased _).symm
  · intro c hc i hi used
    obtain ⟨b, hb, he⟩ := List.mem_map.mp hc
    cases b with
    | mono β => cases he
    | recursive d =>
        cases he
        exact checked.opening.fresh i hi d.template.hm.body
          (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (represented d hb))) used
    | exported t => cases he
  · intro t ht i hi used
    obtain ⟨b, hb, he⟩ := List.mem_map.mp ht
    cases b with
    | mono β => cases he
    | recursive d => cases he
    | exported original =>
        cases he
        exact checked.opening.fresh i hi t.hm.body
          (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (exportsRepresented t hb))) used
  · intro c hc i hi
    obtain ⟨b, hb, he⟩ := List.mem_map.mp hc
    cases b with
    | mono β => cases he
    | recursive d =>
        cases he
        exact countFresh d hb i hi
    | exported t => cases he
  · intro t ht i hi
    obtain ⟨b, hb, he⟩ := List.mem_map.mp ht
    cases b with
    | mono β => cases he
    | recursive d => cases he
    | exported original =>
        cases he
        exact exportCountFresh t hb i hi

#print axioms fromChecked

def fromAnnotated {output path node schemes site annotation quantified captures premises typeCaptures env}
    (interface : HMCountScheme.Annotated annotation quantified captures premises)
    (checked : @HMReconciliation.Checked output path node schemes site interface.scheme typeCaptures)
    (rhs : HMReconciliation.RHSChecked checked env)
    (represented : ∀ c, .recursive c ∈ env → c.template.hm.body ∈ typeCaptures)
    (exportsRepresented : ∀ t, .exported t ∈ env → t.hm.body ∈ typeCaptures)
    (countFresh : ∀ c, .recursive c ∈ env → ∀ i ∈ c.template.counts.captures, i ∉ quantified)
    (exportCountFresh : ∀ t, .exported t ∈ env → ∀ i ∈ t.counts.captures, i ∉ quantified) :
    RecursiveHMSigned.Certified annotation quantified captures premises
      (node.view checked.interpretation) (node.original :: typeCaptures)
      (env.map (mapBinding checked.interpretation checked.interpretationLC))
      node.inner.stripFound checked.interpretation :=
  ⟨interface, fromChecked checked rhs represented exportsRepresented countFresh exportCountFresh⟩

#print axioms fromAnnotated

structure LocatedChecked {output path node schemes site s captures}
    (checked : @HMReconciliation.Checked output path node schemes site s captures)
    (env : List Binding) where
  rhs : HMReconciliation.RHSChecked checked env
  nodes : List Typed.NodeResult

/-- Construct the symbolic derivation by traversing the exact original found
    RHS, rather than requiring a caller-supplied proof at an identity opening.
    The source demand guides checking, but actual bounds and inclusion remain
    separate. Unsupported traversal cases reject with no legacy fallback. -/
def checkLocated {output path node schemes site s captures}
    (checked : @HMReconciliation.Checked output path node schemes site s captures)
    (env : List Binding) : Except String (LocatedChecked checked env) := do
  let interpretedEnv := env.map (mapBinding checked.interpretation checked.interpretationLC)
  let walked ← RecursiveHMWalk.walk checked.interpretation
    (s.counts.quantified ++ s.counts.captures) [] (s.counts.quantified ++ s.counts.captures)
    s.counts.premises interpretedEnv path (.found node.original node.inner) schemes
    (some checked.opening.bounds)
  let derivation : Derives checked.interpretation (s.counts.quantified ++ s.counts.captures) []
      s.counts.premises interpretedEnv node.inner.stripFound walked.bounds := by
    simpa only [Expr.stripFound] using walked.derivation
  let typed ← HMFoundView.checkTyped node checked.interpretation
    (s.counts.quantified ++ s.counts.captures) [] s.counts.premises interpretedEnv
    (s.counts.quantified ++ s.counts.captures) walked.bounds derivation
  let inclusion ← Typed.subtype s.counts.premises typed.actual checked.opening.bounds
  pure ⟨⟨typed, inclusion.down⟩, walked.nodes⟩

#print axioms checkLocated

end FHM.Bounds.RecursiveHMReconciled
