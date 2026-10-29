import FHM.Completeness

/-! Recursive annotation completions precede every pool opening. These checks
retain the existing dependency cuts, written prefixes, and implicit polymorphism. -/

namespace RecMatchingTests

def ann : CheckAnn := .partialForall 1 (.arrow (.fixed (.bvar 0)) .hole)
def checked : Ty := .arrow (.fvar 5) (.fvar 6)

theorem checkedMatches : ann.RecMatches [5] [5, 6] checked := by
  apply PartialCore.Ann.RecFits.close (Q := [])
  · exact ⟨rfl, [], by simp [PartialCore.HoleAssignment.Unique], .arrow .fixed .hole⟩
  · rfl
  · decide
  · simp
  · decide
  · exact .arrow .fvar .fvar
  · simp [ann, PartialCore.Ann.rigidVars, PartialCore.Template.rigidVars, Ty.freeVars]
  · simp

-- The written prefix remains first, followed by the independently inferred hole.
example : recScheme [5] [5, 6] checked = ⟨2, .arrow (.bvar 0) (.bvar 1)⟩ := rfl

example : ann.RecFits [20] (.arrow (.fvar 20) (.fvar 21)) := by
  exact checkedMatches.open (.arrow .fvar .fvar) (Xs := [20, 21]) rfl
    (by decide) (by decide) (by simp) (by simp)

example : ann.RecFits [30] (.arrow (.fvar 30) (.fvar 31)) := by
  exact checkedMatches.open (.arrow .fvar .fvar) (Xs := [30, 31]) rfl
    (by decide) (by decide) (by simp) (by simp)

example : ann.RecMatches [20] [20, 21] (.arrow (.fvar 20) (.fvar 21)) := by
  exact checkedMatches.rename_pool (.arrow .fvar .fvar) (W := [20, 21]) rfl
    (by decide) (by decide) (by simp) (by simp [checked, Ty.freeVars])
    (by decide) (by simp)

-- An extra inferred binder cannot scope an authored out-of-scope fixed leaf.
theorem outOfScope_rejected :
    ¬ (PartialCore.Ann.partialForall 1 (.fixed (.bvar 1))).RecMatches [5] [5, 6] checked := by
  intro h
  obtain ⟨hc⟩ := h.completion
  cases hc with
  | partialForall _ hs _ => cases hs with | fixed hb => cases hb with | bvar hi => omega

theorem conflictingFixed_rejected :
    ¬ (PartialCore.Ann.template (.fixed (.prim .int))).RecMatches [] [] (.prim .char) := by
  intro h
  obtain ⟨hc⟩ := h.completion
  cases hc with
  | template _ hc => cases hc.fits

def outerAnn : CheckAnn := .partialForall 1 (.arrow (.fixed (.fvar 7)) .hole)
def outerTy : Ty := .arrow (.fvar 7) (.fvar 6)

theorem outerMatches : outerAnn.RecMatches [5] [5, 6] outerTy := by
  apply PartialCore.Ann.RecFits.close (Q := [7])
  · exact ⟨rfl, [], by simp [PartialCore.HoleAssignment.Unique], .arrow .fixed .hole⟩
  · rfl
  · decide
  · simp
  · decide
  · exact .arrow .fvar .fvar
  · simp [outerAnn, PartialCore.Ann.rigidVars, PartialCore.Template.rigidVars, Ty.freeVars]
  · simp

example : (outerAnn.substSourceTyFvars [(7, .prim .int)]).RecMatches [5] [5, 6]
    (Subst.onTy [(7, .prim .int)] outerTy) := by
  apply outerMatches.onSubst_source
  · intro p hp
    simp only [List.mem_singleton] at hp
    subst p
    exact .prim
  · simp
  · simp [Ty.freeVars]
  · simp

def bindings : List InputRecBinding :=
  [{ ann := some ⟨1, .arrow (.fixed (.bvar 0)) .hole⟩,
     rhs := .lambda (some (.fixed (.bvar 0))) (.var 0) }]
def body : InferInput := .letIn none (.app (.var 0) (.primLit (.int 1)))
  (.app (.var 1) (.primLit (.char 'x')))
def program : InferInput := .letRec bindings body
def omitted : InferInput := .letRec [{ ann := none, rhs := .lambda none (.var 0) }] body

#guard match inferWithTypes [] program with
  | some r => match r.ty with | .prim .char => true | _ => false
  | none => false
#guard match inferWithTypes [] omitted with
  | some r => match r.ty with | .prim .char => true | _ => false
  | none => false
#guard match SmallStep.evaluate 24 program.erase with
  | some (.primLit (.char 'x')) => true
  | _ => false

-- Complete recursive signatures retain their previous polymorphic recursion mode.
def complete : InferInput := .letRec
  [{ ann := (Option.ofCore (some ⟨1, .arrow (.bvar 0) (.bvar 0)⟩)),
     rhs := .lambda (some (.fixed (.bvar 0))) (.var 0) }] body
#guard match inferWithTypes [] complete with
  | some r => match r.ty with | .prim .char => true | _ => false
  | none => false

-- Hole-free structured templates select the same complete contract as their
-- fixed-type spelling. This is the parser's existing polymorphic recursion policy.
def structuredAnn : BindingAnn :=
  some ⟨1, .arrow (.fixed (.bvar 0)) (.fixed (.prim .int))⟩

example : structuredAnn.annotationView = .complete ⟨1, .arrow (.bvar 0) (.prim .int)⟩ := rfl

def structuredPolyrec : InferInput := .letRec
  [{ ann := structuredAnn,
     rhs := .lambda (some (.fixed (.bvar 0)))
       (.letIn none (.app (.var 1) (.primLit (.int 1)))
         (.app (.var 2) (.primLit (.char 'x')))) }]
  (.app (.var 0) (.primLit (.int 0)))

#guard match inferWithTypes [] structuredPolyrec with
  | some r => match r.ty with | .prim .int => true | _ => false
  | none => false

/-- Production inference exposes one closed witness per annotation, before any
component/pool-opening quantifier; inversion preserves those witnesses. -/
theorem inferred_completions_once (h : inferWithTypes [] program = some result) :
    ∃ (specs : List RecSpec) (prefixes : List (List Nat)) (pool : List Nat),
      RecAnnotationsMatch bindings specs prefixes pool := by
  obtain ⟨specs, _, prefixes, pool, _, _, _, _, _, hm, _, _, _⟩ :=
    (inferWithTypes_input_sound h).rec_inv
  exact ⟨specs, prefixes, pool, hm⟩

#print axioms PartialCore.Ann.RecMatches.ofCofinite
#print axioms PartialCore.Ann.RecMatches.rename_pool
#print axioms PartialCore.Ann.RecMatches.onSubst_source
#print axioms RecAnnotationsMatch.subst_fresh_pool
#print axioms RecState.InputTrace.annotationMatches
#print axioms ScopedTyping.rec_inv
#print axioms ScopedTyping.rec_inv_high
#print axioms inferred_completions_once

end RecMatchingTests
