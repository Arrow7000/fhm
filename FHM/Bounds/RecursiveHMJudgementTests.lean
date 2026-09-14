import FHM.Bounds.RecursiveHMJudgement

namespace FHM.Bounds.RecursiveHMJudgementTests

open RecursiveHMJudgement SchemeSpecialization

private def n : Count := .var ⟨.rigid, 7⟩
private def exact (a : BoundsTy) : BoundsTy := .list n n a
private def source : Expr := .lambda (some (.fvar 90)) (.var 0)

private theorem annotatedIdentity : Derives BoundsTy.fvar [] [] [] [] source
    (.arrow (.fvar 90) (.fvar 90)) := by
  refine .lambda ?_ (.varMono rfl)
  refine ⟨⟨.fvar 90, True.intro, by simp [Synth.BoundsTy.toTy, Ty.eraseBounds]⟩,
    by simp [ScopedAnnotation.decode, pure, Except.pure], ?_⟩
  exact .fvar

private def replacement (arg : BoundsTy) (i : Nat) : BoundsTy :=
  if i = 90 then arg else .fvar i

private theorem replacementLC {arg : BoundsTy} (lc : (Synth.BoundsTy.toTy arg).IsLC) :
    ∀ i, (Synth.BoundsTy.toTy (replacement arg i)).IsLC := by
  intro i
  by_cases hi : i = 90
  · simpa [replacement, hi] using lc
  · simp only [replacement, hi, if_false, Synth.BoundsTy.toTy]
    exact .fvar

private theorem replacementScope {arg : BoundsTy} {ids : List Nat} (scope : ScopedScheme.BoundsScoped ids arg) :
    ∀ i, ScopedScheme.BoundsScoped ids (replacement arg i) := by
  intro i
  by_cases hi : i = 90
  · simpa [replacement, hi] using scope
  · simp [replacement, hi, ScopedScheme.BoundsScoped]

/-- The unchanged source annotation names opaque identity 90, but the shared
    proof-side interpretation specializes it to the entire caller bounds type. -/
theorem annotatedIdentityAllBounds (arg : BoundsTy) (ids : List Nat)
    (lc : (Synth.BoundsTy.toTy arg).IsLC) (scope : ScopedScheme.BoundsScoped ids arg) :
    Derives (replacement arg) [] [] [] [] source (.arrow arg arg) := by
  have h := transportTypes (replacement arg) (replacementLC lc) ids (replacementScope scope)
    annotatedIdentity (by intro c hc; cases hc)
  simpa [mapFree, replacement] using h

private def scheme : HMCountScheme.Scheme :=
  { hm := ⟨1, .arrow (listTy (.bvar 0)) (listTy (.bvar 0))⟩
    counts := ⟨[7], [], [], .arrow (exact (.bvar 0)) (exact (.bvar 0))⟩
    hmWF := (Ty.bvarsBelow_iff _).mp (by decide)
    countWF := ScopedScheme.Scheme.wfBool_sound (by decide)
    shape := by simp [exact, Synth.BoundsTy.toTy, listTy, FHM.Bounds.listTyName] }

private def opening : HMCountScheme.Opening scheme (.arrow (listTy (.fvar 90)) (listTy (.fvar 90))) [] :=
  ⟨[90], rfl, by decide, by
      intro i hi t ht
      have ht : t = scheme.hm.body := by simpa using ht
      subst t
      simp [scheme, Ty.freeVars, TyList.freeVars, listTy],
    (by simp [HMCountScheme.opened, scheme, exact, TypeSubstitution.substitute, SchemeUse.vector,
      Synth.BoundsTy.toTy, listTy, Ty.eraseBounds, TyList.eraseBounds, FHM.Bounds.listTyName]),
    (Ty.bvarsBelow_iff _).mp (by decide)⟩

private def contract : Contract := ⟨scheme, _, RecursiveHMContract.fromOpaque opening⟩

private def symbolic : ScopedScheme.Instance scheme.counts [n] [7] :=
  { wf := scheme.countWF, arity := rfl
    finiteArgs := by
      intro a ha
      have ha : a = n := by simpa using ha
      subst a
      exact .var
    argsScoped := by
      intro a ha
      have ha : a = n := by simpa using ha
      subst a
      simp [n, Scope.CountScoped]
    capturesScoped := by simp [scheme]
    bodyScoped := by
      simp [scheme, exact, ScopedScheme.BoundsScoped, CountSubstitution.bounds,
        CountSubstitution.count, CountSubstitution.lookup, Scope.CountScoped, n]
    premisesScoped := by simp [scheme] }

private def recursiveUse : RecursiveHMContract.Use contract.fixed [] contract.hm [7] :=
  ⟨[n], symbolic, by
      intro σ _ g hg
      simp [ScopedScheme.Instance.premises, contract, scheme] at hg,
    by decide, rfl⟩

private def loop : Expr := .lambda none (.app (.var 1) (.var 0))

private theorem recursiveIdentity : Derives BoundsTy.fvar [7] [] [] [.recursive contract] loop
    (.arrow (exact (.fvar 90)) (exact (.fvar 90))) := by
  refine .lambda True.intro (.app ?_ (.varMono rfl) (SemanticSub.refl _ _))
  exact .varRecursive rfl recursiveUse

/-- Every complete locally closed/scoped caller type specializes the SAME
    recursive interface throughout the implementation. No polymorphic recursion. -/
theorem recursiveIdentityAllBounds (arg : BoundsTy) (ids : List Nat)
    (lc : (Synth.BoundsTy.toTy arg).IsLC) (scope : ScopedScheme.BoundsScoped ids arg) :
    Derives (replacement arg) [7] [] []
      ([.recursive contract].map (mapBinding (replacement arg) (replacementLC lc))) loop
      (.arrow (exact arg) (exact arg)) := by
  have fresh : CapturesFixed (replacement arg) [.recursive contract] := by
    intro c hc i hi
    have hc : c = contract := by simpa using hc
    subst c
    have impossible : False := by simpa [contract, scheme, Ty.freeVars, TyList.freeVars, listTy] using hi
    exact impossible.elim
  have h := transportTypes (replacement arg) (replacementLC lc) ids (replacementScope scope)
    recursiveIdentity fresh
  simpa [mapFree, replacement, exact] using h

#print axioms annotatedIdentityAllBounds
#print axioms recursiveIdentityAllBounds

end FHM.Bounds.RecursiveHMJudgementTests
