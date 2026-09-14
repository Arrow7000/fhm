import FHM.Bounds.HMReconciliation
import FHM.Bounds.RecursiveHMUniversal
import FHM.Bounds.RecursiveHMSigned

/-! Checked symbolic RHS results become universal certificates without losing
their original source HM interpretation. Closed recursive templates still need
explicit count independence; metadata decoding alone never certifies an RHS. -/

namespace FHM.Bounds.RecursiveHMReconciled

open RecursiveHMJudgement ScopedScheme

def fromChecked {output path node schemes site s captures env}
    (checked : @HMReconciliation.Checked output path node schemes site s captures)
    (rhs : HMReconciliation.RHSChecked checked env)
    (represented : ∀ c, .recursive c ∈ env → c.template.hm.body ∈ captures)
    (countFresh : ∀ c, .recursive c ∈ env → ∀ i ∈ c.template.counts.captures,
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
      countFresh := ?_ }
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
  · intro c hc i hi
    obtain ⟨b, hb, he⟩ := List.mem_map.mp hc
    cases b with
    | mono β => cases he
    | recursive d =>
        cases he
        exact countFresh d hb i hi

#print axioms fromChecked

def fromAnnotated {output path node schemes site annotation quantified captures premises typeCaptures env}
    (interface : HMCountScheme.Annotated annotation quantified captures premises)
    (checked : @HMReconciliation.Checked output path node schemes site interface.scheme typeCaptures)
    (rhs : HMReconciliation.RHSChecked checked env)
    (represented : ∀ c, .recursive c ∈ env → c.template.hm.body ∈ typeCaptures)
    (countFresh : ∀ c, .recursive c ∈ env → ∀ i ∈ c.template.counts.captures, i ∉ quantified) :
    RecursiveHMSigned.Certified annotation quantified captures premises
      (node.view checked.interpretation) (node.original :: typeCaptures)
      (env.map (mapBinding checked.interpretation checked.interpretationLC))
      node.inner.stripFound checked.interpretation :=
  ⟨interface, fromChecked checked rhs represented countFresh⟩

#print axioms fromAnnotated

end FHM.Bounds.RecursiveHMReconciled
