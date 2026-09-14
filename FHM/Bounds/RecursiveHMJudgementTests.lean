import FHM.Bounds.RecursiveHMEnvironment

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

private def universal : RecursiveHMUniversal.Certified scheme contract.hm [] [.recursive contract] loop :=
  { opening := opening
    actual := .arrow (exact (.fvar 90)) (exact (.fvar 90))
    shape := opening.shape
    actualScope := by simp [scheme, exact, ScopedScheme.BoundsScoped, Scope.CountScoped, n]
    typing := recursiveIdentity
    inclusion := SemanticSub.refl _ _
    typeFresh := by
      intro c hc i hi ht
      have hc : c = contract := by simpa using hc
      subst c
      simp [contract, scheme, Ty.freeVars, TyList.freeVars, listTy] at ht
    countFresh := by
      intro c hc i hi
      have hc : c = contract := by simpa using hc
      subst c
      simp [contract, scheme] at hi }

/-- Joint quantification is kernel-checked for any finite scoped count vector
    and full caller bounds argument, not sampled at a few primitive types. -/
theorem jointRecursiveInstances {counts caller} (inst : ScopedScheme.Instance scheme.counts counts caller)
    (arg : BoundsTy) (lc : (Synth.BoundsTy.toTy arg).IsLC)
    (scope : ScopedScheme.BoundsScoped caller arg) :
    ∃ types env, Derives types [7] (scheme.counts.quantified.zip counts) inst.premises env loop
      (RecursiveHMUniversal.actual universal counts [arg]) ∧
    SemanticSub inst.premises (RecursiveHMUniversal.actual universal counts [arg])
      (RecursiveHMUniversal.demand scheme counts [arg]) ∧
    scheme.hm.InstantiatesTo [Synth.BoundsTy.toTy arg]
      (Synth.BoundsTy.toTy (RecursiveHMUniversal.actual universal counts [arg])) ∧
    ScopedScheme.BoundsScoped caller (RecursiveHMUniversal.actual universal counts [arg]) := by
  have h := RecursiveHMUniversal.use universal inst [arg] rfl
    (by
      intro a ha
      have he : a = arg := by simpa using ha
      subst a
      exact lc)
    (by simpa using ScopedScheme.boundsScopedBool_complete scope)
  exact ⟨_, _, h⟩

example : RecursiveHMUniversal.demand scheme [.lit 3] [.list n n (.prim .int)] =
    .arrow (.list (.lit 3) (.lit 3) (.list n n (.prim .int)))
      (.list (.lit 3) (.lit 3) (.list n n (.prim .int))) := by
  simp [RecursiveHMUniversal.demand, TypeSubstitution.combined, TypeSubstitution.substitute,
    CountSubstitution.bounds, CountSubstitution.count, CountSubstitution.lookup,
    SchemeUse.vector, scheme, exact, n]

#print axioms jointRecursiveInstances

private def sourceSignature : PolyTy :=
  ⟨1, .arrow (.bl (.solid n) (.solid n) (.bvar 0)) (.bl (.solid n) (.solid n) (.bvar 0))⟩

private def sourceInterface : HMCountScheme.Annotated sourceSignature [7] [] [] :=
  { source :=
      { annotation :=
          { bounds := scheme.counts.body
            inScope := scheme.countWF.2.2.1
            shape := by simp [sourceSignature, scheme, exact, Synth.BoundsTy.toTy,
              Ty.eraseBounds, listTy, bareListTy, FHM.Bounds.listTyName, _root_.listTyName] }
        wf := scheme.countWF
        decoded := by
          simp [ScopedAnnotation.decode, ScopedScheme.countScopedBool, sourceSignature,
            scheme, exact, n, bind, pure, Except.bind, Except.pure] }
    hmWF := (Ty.bvarsBelow_iff _).mp (by decide) }

private theorem sourceInterfaceScheme : sourceInterface.scheme = scheme := by
  rfl

private def signed : RecursiveHMSigned.Certified sourceSignature [7] [] [] contract.hm []
    [.recursive contract] loop :=
  ⟨sourceInterface, by simpa only [sourceInterfaceScheme] using universal⟩

/-- The written forall signature is justified by universal recursive RHS typing,
    not just by its decoded demand or by one monomorphic use. -/
theorem writtenPolymorphicRecursiveSignature {counts caller}
    (inst : ScopedScheme.Instance sourceInterface.scheme.counts counts caller)
    (arg : BoundsTy) (lc : (Synth.BoundsTy.toTy arg).IsLC)
    (scope : ScopedScheme.BoundsScoped caller arg) :
    RecursiveHMSigned.BindingOK [7] ([7].zip counts) [arg] inst.premises sourceSignature
      (RecursiveHMUniversal.actual signed.implementation counts [arg]) := by
  exact RecursiveHMSigned.signatureInstances signed inst [arg] rfl
    (by
      intro a ha
      have he : a = arg := by simpa using ha
      subst a
      exact lc)
    (by simpa using ScopedScheme.boundsScopedBool_complete scope)

#print axioms writtenPolymorphicRecursiveSignature

private theorem capturedOpaqueEnvironment : RecursiveHMEnvironment.Captured [] [.recursive contract] := by
  constructor
  · intro β hb
    simp at hb
  · intro c hc β hβ
    have hc : c = contract := by simpa using hc
    subst c
    exact RecursiveHMEnvironment.opaqueVector opening [] β hβ

theorem unchangedCountEnvironment {counts caller} (inst : ScopedScheme.Instance scheme.counts counts caller) :
    [.recursive contract].map (mapCountBinding (scheme.counts.quantified.zip counts)) = [.recursive contract] :=
  RecursiveHMEnvironment.instantiated inst capturedOpaqueEnvironment

#print axioms unchangedCountEnvironment

private def originalOutput : Expr := .found contract.hm loop
private def originalNode : HMFoundView.AtNode originalOutput [] :=
  ⟨contract.hm, loop, by simp [originalOutput, Expr.atCorePath]⟩

private def nodeCertificate : RecursiveHMUniversal.Certified scheme originalNode.original []
    [.recursive contract] originalNode.inner.stripFound := by
  simpa only [originalNode, loop, Expr.stripFound] using universal

private def signedNodeCertificate : RecursiveHMSigned.Certified sourceSignature [7] [] []
    originalNode.original [] [.recursive contract] originalNode.inner.stripFound := by
  simpa only [originalNode, loop, Expr.stripFound] using signed

/-- Every caller instance yields a typed view at the unchanged original site,
    with exactly the certified implementation bounds, not inferred top bounds. -/
theorem exactRecursiveNodeInstances {counts caller}
    (inst : ScopedScheme.Instance scheme.counts counts caller) (types : List BoundsTy)
    (arity : types.length = scheme.hm.paramCount)
    (lc : ∀ a ∈ types, (Synth.BoundsTy.toTy a).IsLC)
    (scope : types.all (ScopedScheme.boundsScopedBool caller) = true) :
    (RecursiveHMUniversal.atNode originalNode nodeCertificate inst types arity lc scope).actual =
      RecursiveHMUniversal.actual nodeCertificate counts types := rfl

/-- Source-signature evidence is about the very same exact-node actual result. -/
theorem exactSignedRecursiveNodeInstances {counts caller}
    (inst : ScopedScheme.Instance signedNodeCertificate.interface.scheme.counts counts caller)
    (types : List BoundsTy) (arity : types.length = sourceSignature.paramCount)
    (lc : ∀ a ∈ types, (Synth.BoundsTy.toTy a).IsLC)
    (scope : types.all (ScopedScheme.boundsScopedBool caller) = true) :
    RecursiveHMSigned.BindingOK [7] ([7].zip counts) types inst.premises sourceSignature
      (RecursiveHMSigned.atNode originalNode signedNodeCertificate inst types arity lc scope).typed.actual :=
  (RecursiveHMSigned.atNode originalNode signedNodeCertificate inst types arity lc scope).signature

/-- The captured-vector proof removes count environment transport while keeping
    the one shared HM specialization of every recursive assumption explicit. -/
theorem exactGroupEnvironmentNodeInstances {counts caller}
    (inst : ScopedScheme.Instance scheme.counts counts caller) (types : List BoundsTy)
    (arity : types.length = scheme.hm.paramCount)
    (lc : ∀ a ∈ types, (Synth.BoundsTy.toTy a).IsLC)
    (scope : types.all (ScopedScheme.boundsScopedBool caller) = true) :
    Derives (argument nodeCertificate.opening.ids (SchemeUse.vector types)) [7] ([7].zip counts)
      inst.premises (RecursiveHMUniversal.typeEnvironment nodeCertificate types lc)
      originalNode.inner.stripFound
      (RecursiveHMEnvironment.atNode originalNode nodeCertificate inst capturedOpaqueEnvironment
        types arity lc scope).actual :=
  (RecursiveHMEnvironment.atNode originalNode nodeCertificate inst capturedOpaqueEnvironment
    types arity lc scope).derivation

private def recursiveNodeCheck : Bool :=
  let arg : BoundsTy := .list n n (.prim .int)
  let checked := RecursiveHMUniversal.atNode originalNode nodeCertificate symbolic [arg] rfl
    (by
      intro a ha
      have he : a = arg := by simpa using ha
      subst a
      apply (Ty.bvarsBelow_iff _).mp
      simp [arg, Synth.BoundsTy.toTy, listTy, Ty.bvarsBelow, TyList.bvarsBelow])
    (by decide)
  match checked.actual with
  | .arrow (.list lo hi (.list callerLo callerHi (.prim .int)))
      (.list resultLo resultHi (.list nestedLo nestedHi (.prim .int))) =>
    lo == n && hi == n && callerLo == n && callerHi == n &&
      resultLo == n && resultHi == n && nestedLo == n && nestedHi == n
  | _ => false

#eval if recursiveNodeCheck then IO.println "PASS: recursive exact-node specialization preserves nested caller counts even at callee ID collision"
  else throw (IO.userError "recursive exact-node specialization lost implementation bounds")

#print axioms exactRecursiveNodeInstances
#print axioms exactSignedRecursiveNodeInstances
#print axioms exactGroupEnvironmentNodeInstances

end FHM.Bounds.RecursiveHMJudgementTests
