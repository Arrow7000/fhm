import FHM.Bounds.RecursiveHMJudgement

namespace FHM.Bounds.ScopedHMJudgementTests

open RecursiveHMJudgement SchemeSpecialization CountSubstitution

private def source : Expr := .lambda (some (.bvar 0))
  (.lambda (some (.fvar 90)) (.var 1))

/-- Lexical slots and captured free identities are separate simultaneous
    interfaces throughout the unchanged source implementation. -/
theorem annotatedTwoInterfaces (free slots : Nat → BoundsTy) :
    ScopedDerives free slots [] [] [] [] source
      (.arrow (slots 0) (.arrow (free 90) (slots 0))) := by
  refine .lambda ?_ (.lambda ?_ (.varMono rfl))
  · refine ⟨⟨.bvar 0, True.intro, by simp [Synth.BoundsTy.toTy, Ty.eraseBounds]⟩,
      by simp [ScopedAnnotation.decode, pure, Except.pure], ?_⟩
    exact SemanticSub.refl _ _
  · refine ⟨⟨.fvar 90, True.intro, by simp [Synth.BoundsTy.toTy, Ty.eraseBounds]⟩,
      by simp [ScopedAnnotation.decode, pure, Except.pure], ?_⟩
    exact SemanticSub.refl _ _

/-- Full caller types, including their inner count intervals, specialize both
    interfaces without reopening or changing either source annotation. -/
theorem bothInterfacesTypes (free slots outer : Nat → BoundsTy)
    (lc : ∀ i, (Synth.BoundsTy.toTy (outer i)).IsLC) (caller : List Nat)
    (scope : ∀ i, ScopedScheme.BoundsScoped caller (outer i)) :
    ScopedDerives (fun i => mapFree outer (free i)) (fun i => mapFree outer (slots i))
      [] [] [] [] source
      (.arrow (mapFree outer (slots 0)) (.arrow (mapFree outer (free 90)) (mapFree outer (slots 0)))) := by
  simpa only [List.map_nil, mapFree] using
    transportScopedTypes outer lc caller scope (annotatedTwoInterfaces free slots)
      (by intro c hc; cases hc)

/-- Count transport also descends into the full bounds types inserted through
    lexical slots; it does not alter the original source expression. -/
theorem bothInterfacesCounts (free slots : Nat → BoundsTy) (outer : Bindings)
    (finite : Finite outer) (caller : List Nat)
    (scope : ∀ row ∈ outer, Scope.CountScoped caller row.2) :
    ScopedDerives (fun i => bounds outer (free i)) (fun i => bounds outer (slots i))
      [] (CountAlgebra.compose outer []) [] [] source
      (.arrow (bounds outer (slots 0)) (.arrow (bounds outer (free 90)) (bounds outer (slots 0)))) := by
  simpa only [List.map_nil, bounds] using
    transportScopedCounts outer finite caller scope (annotatedTwoInterfaces free slots)
      (by intro c hc; cases hc)

#print axioms annotatedTwoInterfaces
#print axioms bothInterfacesTypes
#print axioms bothInterfacesCounts

end FHM.Bounds.ScopedHMJudgementTests
