import FHM.Bounds.HMDeclaredReconciliation
import FHM.Bounds.ScopedDeclaration

/-! Actual source-site RHS acceptance after declared-interface reconciliation.
The source node, signature, captured identities and actual bounds stay linked.
Universal certification keeps its explicitly specialized recursive environment;
whole-group introduction/export remains separate and production stays guarded. -/

namespace FHM.Bounds.HMDeclaredRHS

open HMDeclaredReconciliation RecursiveHMJudgement ScopedScheme

/-- Count telescopes are selected from the original lowering metadata at the
    SAME source site. Retain the selection equality instead of guessing IDs. -/
structure Prepared (output : Expr) (metadata : Scope.Metadata) (site : CoreBinderSite)
    (captures : List Nat) (premises : List Constraint) (typeCaptures : List Ty) where
  declaration : Declaration output site
  quantified : List Nat
  resolved : metadata.problems.isEmpty = true
  telescope : ScopedDeclaration.telescope metadata site = .ok quantified
  reconciled : HMDeclaredReconciliation.Checked declaration quantified captures premises typeCaptures

def prepare (output : Expr) (metadata : Scope.Metadata) (site : CoreBinderSite)
    (signatureIds : List Nat) (captures : List Nat := []) (typeCaptures : List Ty := [])
    (premises : List Constraint := []) : Except String (Prepared output metadata site captures premises typeCaptures) := do
  if hp : metadata.problems.isEmpty = true then
    let declaration ← HMDeclaredReconciliation.locate output site
    match ht : ScopedDeclaration.telescope metadata site with
    | .error message => throw message
    | .ok quantified =>
        let reconciled ← HMDeclaredReconciliation.check declaration quantified captures signatureIds typeCaptures premises
        pure ⟨declaration, quantified, hp, ht, reconciled⟩
  else throw "bounds: unresolved or duplicate count scope in declared RHS metadata"

structure Checked {output site d quantified captures premises typeCaptures}
    (c : @HMDeclaredReconciliation.Checked output site d quantified captures premises typeCaptures)
    (env : List Binding) where
  located : RecursiveHMWalk.LocatedResult d.node c.interpretation (slotsFor site c.signatureIds)
    (quantified ++ captures) [] (quantified ++ captures) premises
    (env.map (mapBinding c.interpretation c.interpretationLC))
  inclusion : SemanticSub premises located.typed.actual c.opening.bounds

/-- Check the ORIGINAL source-site RHS, not an identity-expanded reconstruction.
    The signature is guidance; actual result inclusion is independently checked. -/
def check {output site d quantified captures premises typeCaptures}
    (c : @HMDeclaredReconciliation.Checked output site d quantified captures premises typeCaptures)
    (env : List Binding) (schemes : BinderSchemeMap := []) : Except String (Checked c env) := do
  let located ← RecursiveHMWalk.checkLocated d.node c.interpretation (slotsFor site c.signatureIds)
    (quantified ++ captures) [] (quantified ++ captures) premises
    (env.map (mapBinding c.interpretation c.interpretationLC)) schemes (some c.opening.bounds)
  let inclusion ← Typed.subtype premises located.typed.actual c.opening.bounds
  pure ⟨located, inclusion.down⟩

/-- The common environment's CLOSED recursive captures must be represented in
    the declaration's protected interface. Actual fixed HM vectors still map
    uniformly; count/HM group export is not asserted by this certificate. -/
def certify {output site d quantified captures premises typeCaptures env}
    (c : @HMDeclaredReconciliation.Checked output site d quantified captures premises typeCaptures)
    (rhs : Checked c env)
    (represented : ∀ b, .recursive b ∈ env → b.template.hm.body ∈ typeCaptures)
    (exportsRepresented : ∀ t, .exported t ∈ env → t.hm.body ∈ typeCaptures)
    (countFresh : ∀ b, .recursive b ∈ env → ∀ i ∈ b.template.counts.captures, i ∉ quantified)
    (exportCountFresh : ∀ t, .exported t ∈ env → ∀ i ∈ t.counts.captures, i ∉ quantified) :
    RecursiveHMSigned.Certified d.annotation quantified captures premises
      (ScopedHMInterpretation.AtNode.view d.node c.interpretation (slotsFor site c.signatureIds))
      (d.node.original :: guardedTypes d typeCaptures)
      (env.map (mapBinding c.interpretation c.interpretationLC))
      d.node.inner.stripFound c.interpretation (slotsFor site c.signatureIds) := by
  refine ⟨c.interface, RecursiveHMUniversal.fromScopedChecked d.node c.opening
    rhs.located.typed rhs.inclusion ?_ ?_ ?_ ?_⟩
  · intro b hb i hi used
    obtain ⟨original, ho, he⟩ := List.mem_map.mp hb
    cases original with
    | mono β => cases he
    | recursive original =>
        cases he
        have guarded : original.template.hm.body ∈ guardedTypes d typeCaptures := by
          unfold guardedTypes
          exact List.mem_cons_of_mem _ (List.mem_append_left _ (represented original ho))
        exact c.opening.fresh i hi original.template.hm.body
          (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ guarded)) used
    | exported t => cases he
  · intro t ht i hi used
    obtain ⟨original, ho, he⟩ := List.mem_map.mp ht
    cases original with
    | mono β => cases he
    | recursive c => cases he
    | exported original =>
        cases he
        have guarded : t.hm.body ∈ guardedTypes d typeCaptures := by
          unfold guardedTypes
          exact List.mem_cons_of_mem _ (List.mem_append_left _ (exportsRepresented t ho))
        exact c.opening.fresh i hi t.hm.body
          (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ guarded)) used
  · intro b hb i hi
    obtain ⟨original, ho, he⟩ := List.mem_map.mp hb
    cases original with
    | mono β => cases he
    | recursive original =>
        cases he
        exact countFresh original ho i hi
    | exported t => cases he
  · intro t ht i hi
    obtain ⟨original, ho, he⟩ := List.mem_map.mp ht
    cases original with
    | mono β => cases he
    | recursive c => cases he
    | exported original =>
        cases he
        exact exportCountFresh t ho i hi

/-- Recover the canonical free source reader from the actual reconciled RHS
    proof. Opening and implementation evidence are retained, not reconstructed
    from metadata; lexical slots and exact-node reports remain separate. -/
def certifySource {output site d quantified captures premises typeCaptures env}
    (c : @HMDeclaredReconciliation.Checked output site d quantified captures premises typeCaptures)
    (rhs : Checked c env)
    (represented : ∀ b, .recursive b ∈ env → b.template.hm.body ∈ typeCaptures)
    (exportsRepresented : ∀ t, .exported t ∈ env → t.hm.body ∈ typeCaptures)
    (countFresh : ∀ b, .recursive b ∈ env → ∀ i ∈ b.template.counts.captures, i ∉ quantified)
    (exportCountFresh : ∀ t, .exported t ∈ env → ∀ i ∈ t.counts.captures, i ∉ quantified) :=
  (certify c rhs represented exportsRepresented countFresh exportCountFresh).implementation.sourceFree
    (sourceTypes' := BoundsTy.fvar)
    (fun _ named => c.sourceIdentity named)

theorem certifySource_runtimeReady {output site d quantified captures premises typeCaptures env}
    (c : @HMDeclaredReconciliation.Checked output site d quantified captures premises typeCaptures)
    (rhs : Checked c env)
    (represented : ∀ b, .recursive b ∈ env → b.template.hm.body ∈ typeCaptures)
    (exportsRepresented : ∀ t, .exported t ∈ env → t.hm.body ∈ typeCaptures)
    (countFresh : ∀ b, .recursive b ∈ env → ∀ i ∈ b.template.counts.captures, i ∉ quantified)
    (exportCountFresh : ∀ t, .exported t ∈ env → ∀ i ∈ t.counts.captures, i ∉ quantified)
    (ready : ScopedDerives.RuntimeReady rhs.located.typed.derivation) :
    ScopedDerives.RuntimeReady
      (certifySource c rhs represented exportsRepresented countFresh exportCountFresh).typing :=
  RecursiveHMUniversal.Certified.sourceFree_runtimeReady
    (certify c rhs represented exportsRepresented countFresh exportCountFresh).implementation
    (fun _ named => c.sourceIdentity named) ready

#print axioms check
#print axioms prepare
#print axioms certify
#print axioms certifySource
#print axioms certifySource_runtimeReady

end FHM.Bounds.HMDeclaredRHS
