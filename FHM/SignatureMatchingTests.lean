import FHM.Completeness

/-! Regression proofs for the production closed-signature witness. This file
does not change implicit generalization or recursive dependency cuts. -/

namespace SignatureMatchingTests

def extraAnn : CheckAnn := .partialForall 1 (.arrow (.fixed (.bvar 0)) .hole)
def extraScheme : PolyTy := ⟨2, .arrow (.bvar 0) (.bvar 1)⟩

/-- Written binders precede inferred binders, and a hole selects one of those
binders in the closed scheme, once. -/
theorem extraMatches : extraAnn.SignatureMatches extraScheme := by
  refine ⟨rfl, ⟨.partialForall (by change 1 ≤ 2; decide) ?_ ?_⟩⟩
  · exact .arrow (.fixed (.bvar (by decide))) .hole
  · exact ⟨[], by simp [PartialCore.HoleAssignment.Unique],
      by simp [PartialCore.HoleAssignment.Scoped], .arrow .fixed .hole,
      .arrow (.bvar (by decide)) (.bvar (by decide))⟩

example : extraAnn.SignatureFits extraScheme [20, 21] := extraMatches.open _ (by decide)
example : extraAnn.SignatureFits extraScheme [30, 31] := extraMatches.open _ (by decide)

-- The previous anonymous-hole contract and the new stored witness are equivalent.
example {scheme : PolyTy} {ann : CheckAnn} {avoid : List Nat} (hwf : scheme.WF) : ann.SignatureMatches scheme ↔
    ∀ Xs, FreshNames avoid scheme.paramCount Xs → ann.SignatureFits scheme Xs :=
  PartialCore.Ann.SignatureMatches.iff_cofinite hwf avoid

def outerAnn : CheckAnn := .partialForall 1 (.arrow (.fixed (.fvar 7)) .hole)
def outerScheme : PolyTy := ⟨2, .arrow (.fvar 7) (.bvar 1)⟩

theorem outerMatches : outerAnn.SignatureMatches outerScheme := by
  refine ⟨rfl, ⟨.partialForall (by change 1 ≤ 2; decide) ?_ ?_⟩⟩
  · exact .arrow (.fixed .fvar) .hole
  · exact ⟨[], by simp [PartialCore.HoleAssignment.Unique],
      by simp [PartialCore.HoleAssignment.Scoped], .arrow .fixed .hole,
      .arrow .fvar (.bvar (by decide))⟩

example (completion : PartialCore.Completion n template ty) (S : Subst)
    (hS : ∀ pair ∈ S, pair.2.IsLC) :
    (completion.onSubst S hS).holes = PartialCore.HoleAssignment.map S.onTy completion.holes := rfl

example : (outerAnn.substSourceTyFvars [(7, .prim .int)]).SignatureMatches
    (Subst.onPolyTy [(7, .prim .int)] outerScheme) :=
  outerMatches.onSubst_source _ (by
    intro pair hp
    simp only [List.mem_singleton] at hp
    subst pair
    exact .prim)

-- An extra inferred binder must not retrospectively scope authored syntax.
theorem outOfScope_rejected :
    ¬ (PartialCore.Ann.partialForall 1 (.fixed (.bvar 1))).SignatureMatches ⟨2, .bvar 1⟩ := by
  intro h
  obtain ⟨hc⟩ := h.completion
  cases hc with
  | partialForall _ hs _ =>
      cases hs with
      | fixed hb => cases hb with | bvar hb => omega

def signed : InferInput := .letIn (some ⟨1, .arrow (.fixed (.bvar 0)) .hole⟩)
  (.lambda (some (.fixed (.bvar 0))) (.var 0))
  (.app (.var 0) (.primLit (.int 42)))

#guard match inferWithTypes [] signed with
  | some result => match result.ty with | .prim .int => true | _ => false
  | none => false

/-- Actual production inference now supplies the closed witness. -/
theorem inferred_signature_once (h : inferWithTypes [] signed = some result) :
    ∃ (scheme : PolyTy) (avoid : List Nat)
      (completion : PartialCore.Completion scheme.paramCount
        (.arrow (.fixed (.bvar 0)) .hole) scheme.body),
      ∀ Xs, FreshNames avoid scheme.paramCount Xs →
        PartialCore.Template.Fits (PartialCore.HoleAssignment.map (Ty.openVars Xs) completion.holes)
          ((PartialCore.Template.arrow (.fixed (.bvar 0)) .hole).map
            (Ty.openVars (Xs.take 1))) (scheme.openVars Xs) := by
  obtain ⟨scheme, avoid, completion, _, _, hopen, _, _⟩ :=
    (inferWithTypes_input_sound h).partialSignature_completion rfl
  exact ⟨scheme, avoid, completion, hopen⟩

#print axioms PartialCore.Ann.SignatureMatches.ofCofinite
#print axioms PartialCore.Ann.SignatureMatches.onSubst_source
#print axioms ScopedTyping.partialSignature_completion
#print axioms inferred_signature_once

end SignatureMatchingTests
