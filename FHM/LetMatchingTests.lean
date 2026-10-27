import FHM.Completeness

/-! Production ordinary-let annotation matching. Generalization remains the
existing policy; these tests check only the new stored-completion boundary. -/

namespace LetMatchingTests

def pairTemplate : TyTemplate := .custom ⟨"Pair"⟩ [.hole, .hole]
def pairScheme : PolyTy := ⟨2, .customTy ⟨"Pair"⟩ [.bvar 0, .bvar 1]⟩

/-- Independent anonymous occurrences select distinct bound types once. -/
theorem pairMatches : (PartialCore.Ann.template pairTemplate).MonoMatches pairScheme := by
  refine ⟨rfl, ⟨.template (.custom ?_) ?_⟩⟩
  · intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl <;> exact .hole
  · refine ⟨[], by simp [PartialCore.HoleAssignment.Unique],
      by simp [PartialCore.HoleAssignment.Scoped], .custom (.cons .hole (.cons .hole .nil)), .customTy ?_⟩
    intro ty ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl <;> exact .bvar (by decide)

example : (PartialCore.Ann.template pairTemplate).FitsMono
    (.customTy ⟨"Pair"⟩ [.fvar 20, .fvar 21]) := pairMatches.open [20, 21] (by decide)

example {ann : BindingAnn} {scheme : PolyTy} {avoid : List Nat} (hwf : scheme.WF) :
    ann.MonoMatches scheme ↔
      ∀ Xs, FreshNames avoid scheme.paramCount Xs → ann.FitsMono (scheme.openVars Xs) :=
  PartialCore.Ann.MonoMatches.iff_cofinite hwf avoid

-- An ordinary annotation has no authored type binders, even if its inferred
-- scheme subsequently generalizes variables.
theorem outOfScope_rejected :
    ¬ (PartialCore.Ann.template (.fixed (.bvar 0))).MonoMatches ⟨1, .bvar 0⟩ := by
  intro h
  obtain ⟨hm⟩ := h.completion
  cases hm with
  | template hs _ => cases hs with | fixed hb => cases hb with | bvar hi => omega

theorem fixedConstraint_retained :
    ¬ (PartialCore.Ann.template (.fixed (.prim .int))).MonoMatches ⟨1, .bvar 0⟩ := by
  intro h
  obtain ⟨hm⟩ := h.completion
  cases hm with
  | template _ hc => cases hc.fits

def outerAnn : BindingAnn := .template (.arrow (.fixed (.fvar 7)) .hole)
def outerScheme : PolyTy := ⟨1, .arrow (.fvar 7) (.bvar 0)⟩

theorem outerMatches : outerAnn.MonoMatches outerScheme := by
  refine ⟨rfl, ⟨.template (.arrow (.fixed .fvar) .hole) ?_⟩⟩
  exact ⟨[], by simp [PartialCore.HoleAssignment.Unique],
    by simp [PartialCore.HoleAssignment.Scoped], .arrow .fixed .hole,
    .arrow .fvar (.bvar (by decide))⟩

example : (outerAnn.substTyFvars [(7, .prim .int)]).MonoMatches
    (Subst.onPolyTy [(7, .prim .int)] outerScheme) :=
  outerMatches.onSubst_source _ (by
    intro pair hp
    simp only [List.mem_singleton] at hp
    subst pair
    exact .prim)

def identityTemplate : TyTemplate := .arrow .hole .hole
def body : InferInput := .letIn .absent (.app (.var 0) (.primLit (.int 1)))
  (.app (.var 1) (.primLit (.char 'x')))
def program : InferInput := .letIn (.template identityTemplate) (.lambda none (.var 0)) body
def omitted : InferInput := .letIn .absent (.lambda none (.var 0)) body

-- Both uses of id are checked: the ordinary let still generalizes implicitly.
#guard match inferWithTypes [] program with
  | some result => match result.ty with | .prim .char => true | _ => false
  | none => false
#guard match inferWithTypes [] omitted with
  | some result => match result.ty with | .prim .char => true | _ => false
  | none => false
#guard match SmallStep.evaluate 16 program.erase with
  | some (.primLit (.char 'x')) => true
  | _ => false

/-- The production inference theorem supplies the single pre-opening witness. -/
theorem inferred_completion_once (h : inferWithTypes [] program = some result) :
    ∃ (scheme : PolyTy) (avoid : List Nat)
      (completion : PartialCore.Completion scheme.paramCount identityTemplate scheme.body),
      ∀ Xs, FreshNames avoid scheme.paramCount Xs →
        PartialCore.Template.Fits (PartialCore.HoleAssignment.map (Ty.openVars Xs) completion.holes)
          identityTemplate (scheme.openVars Xs) := by
  obtain ⟨scheme, avoid, completion, _, hopen, _, _⟩ :=
    (inferWithTypes_input_sound h).template_completion
  exact ⟨scheme, avoid, completion, hopen⟩

#print axioms PartialCore.Ann.MonoMatches.ofCofinite
#print axioms PartialCore.Ann.MonoMatches.onSubst_source
#print axioms InputTyping.template_completion
#print axioms inferred_completion_once

end LetMatchingTests
