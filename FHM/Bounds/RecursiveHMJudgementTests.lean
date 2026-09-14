import FHM.Bounds.RecursiveHMEnvironment
import FHM.Bounds.RecursiveHMUniform

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

private def artifactOnlyReader (i : Nat) : BoundsTy :=
  if i = 65 then .list (.lit 1) (.lit 1) (.prim .int) else .fvar i

private theorem sourceReaderAgreement : ∀ i ∈ source.tyFreeVars,
    BoundsTy.fvar i = artifactOnlyReader i := by
  intro i named
  have identity : i = 90 := by simpa [source, Expr.tyFreeVars, Ty.freeVars] using named
  subst i
  simp [artifactOnlyReader]

/-- Solving an unrelated artifact identity cannot reinterpret named source
    identity 90, nor change the actual annotated program or its bounds. -/
theorem artifactReaderSourceSafe (bound free : Runtime.TypeEnv) (σ : Assign)
    (hb : Runtime.TypeEnv.Downward bound) (hf : Runtime.TypeEnv.Downward free) :
    Runtime.Safe bound free σ (.arrow (.fvar 90) (.fvar 90)) source := by
  have annotation : ScopedHMAnnotation.ParamOK BoundsTy.fvar BoundsTy.bvar [] [] []
      (some (.fvar 90)) (.fvar 90) := by
    refine ⟨⟨.fvar 90, True.intro, by simp [Synth.BoundsTy.toTy, Ty.eraseBounds]⟩,
      by simp [ScopedAnnotation.decode, pure, Except.pure], ?_⟩
    exact .fvar
  have ready : ScopedDerives.RuntimeReady annotatedIdentity :=
    .lambda (ann := some (.fvar 90)) annotation .fvar (.varMono (i := 0) rfl .fvar)
  exact (ready.sourceFree sourceReaderAgreement).safeClosed bound free σ hb hf (by simp)

#print axioms artifactReaderSourceSafe

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

private def anyInts : BoundsTy := .list (.lit 0) .inf (.prim .int)
private def tailInts : BoundsTy := .list (.pred (.lit 0)) (.pred .inf) (.prim .int)
private def tailBranches : List (MatchPattern × Expr) :=
  [(.named nilCtorName 0, .ctor nilCtorName), (.named consCtorName 2, .var 1)]
private def tailFunction : Expr := .lambda none (.match_ (.var 0) tailBranches)
private def tailActuals (i : Nat) : BoundsTy :=
  if i = 0 then .list (.lit 0) (.lit 0) (.prim .int) else tailInts

private theorem tailBodies (i : Nat) (br : MatchPattern × Expr)
    (atIndex : tailBranches[i]? = some br) :
    Derives BoundsTy.fvar [] [] (RecursiveTyping.branchRefine br.1 (.lit 0) .inf)
      (branchEnv br.1 (.lit 0) .inf (.prim .int) [.mono anyInts]) br.2 (tailActuals i) := by
  cases i with
  | zero =>
      have same : br = (.named nilCtorName 0, .ctor nilCtorName) := by simpa [tailBranches] using atIndex.symm
      subst br
      exact .nil
  | succ i =>
      cases i with
      | zero =>
          have same : br = (.named consCtorName 2, .var 1) := by simpa [tailBranches] using atIndex.symm
          subst br
          exact .varMono rfl
      | succ i => simp [tailBranches] at atIndex

private theorem tailSubs (i : Nat) (br : MatchPattern × Expr)
    (atIndex : tailBranches[i]? = some br) :
    SemanticSub (RecursiveTyping.branchRefine br.1 (.lit 0) .inf) (tailActuals i) anyInts := by
  cases i with
  | zero =>
      refine .list ?_ .prim
      intro σ _ goal member
      simp [Interval.subGoals, tailActuals, anyInts] at member
      rcases member with rfl | rfl <;> simp [Constraint.Holds, Count.eval, ExtNat.le]
  | succ i =>
      refine .list ?_ .prim
      intro σ _ goal member
      simp [Interval.subGoals, tailActuals, tailInts, anyInts] at member
      rcases member with rfl | rfl <;> simp [Constraint.Holds, Count.eval, ExtNat.pred, ExtNat.le]

private theorem tailPatterns : ∀ br ∈ tailBranches, RecursiveTyping.ListPattern br.1 := by
  intro br member
  simp only [tailBranches, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact .inr (.inl rfl)
  · exact .inr (.inr rfl)

private theorem tailCoverage : ListBranches.Covers [] ⟨.lit 0, .inf⟩ tailBranches :=
  .full ⟨.ctor nilCtorName, by simp [tailBranches]⟩ ⟨.var 1, by simp [tailBranches]⟩

private theorem tailTyping : Derives BoundsTy.fvar [] [] [] [] tailFunction (.arrow anyInts anyInts) :=
  .lambda True.intro (.matchList (.varMono rfl) tailCoverage tailPatterns tailBodies tailSubs)

private theorem tailReady : ScopedDerives.RuntimeReady tailTyping := by
  have branchesReady : ∀ i br atIndex, ScopedDerives.RuntimeReady (tailBodies i br atIndex) := by
    intro i br atIndex
    cases i with
    | zero =>
        have same : br = (.named nilCtorName 0, .ctor nilCtorName) := by simpa [tailBranches] using atIndex.symm
        subst br
        exact .nil .prim
    | succ i =>
        cases i with
        | zero =>
            have same : br = (.named consCtorName 2, .var 1) := by simpa [tailBranches] using atIndex.symm
            subst br
            exact .varMono rfl (.list .prim)
        | succ i => simp [tailBranches] at atIndex
  have matchReady : ScopedDerives.RuntimeReady
      (ScopedDerives.matchList (.varMono rfl) tailCoverage tailPatterns tailBodies tailSubs) :=
    .matchList tailCoverage tailPatterns tailBodies tailSubs
      (.varMono (i := 0) rfl (.list .prim)) branchesReady (.list .prim)
  exact ScopedDerives.RuntimeReady.lambda (ann := none) True.intro (.list .prim) matchReady

/-- This is obtained from the actual refined-branch typing proof, not a
    separately postulated runtime callback contract. -/
theorem typedTailRuntimeSafe (bound free : Runtime.TypeEnv) (σ : Assign)
    (hb : Runtime.TypeEnv.Downward bound) (hf : Runtime.TypeEnv.Downward free) :
    Runtime.Safe bound free σ (.arrow anyInts anyInts) tailFunction :=
  tailReady.safeClosed bound free σ hb hf (by simp)

#print axioms typedTailRuntimeSafe

private theorem selfMemberSafe (bound free : Runtime.TypeEnv) (σ : Assign) (budget : Nat)
    (e : EnvAt bound free σ budget [.recursive contract]) (i : Nat)
    (inside : i < [Binding.recursive contract].length) :
    BindingAt bound free σ budget ([Binding.recursive contract][i])
      (([Expr.var 0][i]'(by simpa using inside)).substN 0 e.terms) := by
  have zero : i = 0 := by simp only [List.length_singleton] at inside; omega
  subst i
  change BindingAt bound free σ budget (.recursive contract) ((Expr.var 0).substN 0 e.terms)
  rw [Runtime.closing_var e.terms e.closed 0 (by rw [e.arity]; decide)]
  exact e.denotes 0 (by decide)

/-- A genuinely cyclic recursive assumption is realized at every checked
    count instance. Its implementation diverges; finite-budget safety must
    accept that without using an invariant as an unproved runtime promise. -/
theorem recursiveSelfRuntimeSafe (bound free : Runtime.TypeEnv) (σ : Assign) :
    Runtime.Safe bound free σ recursiveUse.bounds (.letRec [none] [.var 0] (.var 0)) := by
  intro budget
  let tied := EnvAt.tieGroup [none] [.var 0] (env := [.recursive contract]) rfl
    (by intro rhs member; obtain rfl := List.mem_singleton.mp member; decide)
    (selfMemberSafe bound free σ) budget
  have behavior := tied.val.varRecursive (i := 0) rfl recursiveUse (by simp)
  rw [tied.property] at behavior
  rw [Runtime.closing_var _ (Runtime.recursiveTerms_closed
    (by intro rhs member; obtain rfl := List.mem_singleton.mp member; decide)) 0 (by decide)] at behavior
  exact behavior

private def mutualRhss : List Expr := [.var 1, .ctor nilCtorName]
private def emptyInts : BoundsTy := .list (.lit 0) (.lit 0) (.prim .int)
private def mutualEnv : List Binding := [.mono emptyInts, .mono emptyInts]

private theorem mutualMembersSafe (bound free : Runtime.TypeEnv) (σ : Assign) (budget : Nat)
    (e : EnvAt bound free σ budget mutualEnv) (i : Nat) (inside : i < mutualEnv.length) :
    BindingAt bound free σ budget mutualEnv[i]
      ((mutualRhss[i]'(by simpa [mutualEnv, mutualRhss] using inside)).substN 0 e.terms) := by
  cases i with
  | zero => exact e.varMono (i := 1) rfl
  | succ i =>
      have zero : i = 0 := by simp [mutualEnv] at inside; omega
      subst i
      exact Runtime.TermAt.value (.ctor _) (Runtime.ValueAt.nil bound free σ budget _)

/-- A two-member group uses the simultaneously tied environment, not a
    sequential prefix. The first RHS calls the second, which returns Nil. -/
theorem mutualGroupRuntimeSafe (bound free : Runtime.TypeEnv) (σ : Assign)
    (hb : Runtime.TypeEnv.Downward bound) (hf : Runtime.TypeEnv.Downward free) :
    Runtime.Safe bound free σ emptyInts (.letRec [none, none] mutualRhss (.var 0)) := by
  have bodyTyping : Derives BoundsTy.fvar [] [] [] mutualEnv (.var 0) emptyInts := .varMono rfl
  have bodyReady : ScopedDerives.RuntimeReady bodyTyping := .varMono (i := 0) rfl (.list .prim)
  exact bodyReady.safeGroup bound free σ hb hf [none, none] mutualRhss rfl
    (by
      intro rhs member
      simp only [mutualRhss, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl <;> decide)
    (mutualMembersSafe bound free σ) (by simp)

#print axioms recursiveSelfRuntimeSafe
#print axioms mutualGroupRuntimeSafe

private theorem recursiveIdentityReady : ScopedDerives.RuntimeReady recursiveIdentity := by
  have callTyping : Derives BoundsTy.fvar [7] [] []
      [.mono (exact (.fvar 90)), .recursive contract] (.app (.var 1) (.var 0)) (exact (.fvar 90)) :=
    .app (.varRecursive rfl recursiveUse) (.varMono rfl) (SemanticSub.refl _ _)
  have callReady : ScopedDerives.RuntimeReady callTyping :=
    .app (SemanticSub.refl _ _)
      (.varRecursive (i := 1) rfl recursiveUse (.arrow (.list .fvar) (.list .fvar)))
      (.varMono (i := 0) rfl (.list .fvar))
  exact ScopedDerives.RuntimeReady.lambda (ann := none) True.intro (.list .fvar) callReady

/-- The same original recursive lambda has a runtime implementation proof at
    every complete supported full-HM/count specialization. Caller-owned nested
    bounds are retained by the existing count-first/full-HM-second certificate. -/
theorem universalRecursiveRhsRuntime {counts caller}
    (inst : ScopedScheme.Instance scheme.counts counts caller)
    (f : Nat → BoundsTy) (lc : ∀ i, (Synth.BoundsTy.toTy (f i)).IsLC)
    (scope : ∀ i, ScopedScheme.BoundsScoped caller (f i))
    (arguments : ∀ i, Runtime.Supported (f i))
    (fixed : CapturesFixed f [.recursive contract])
    (bound free : Runtime.TypeEnv) (σ : Assign)
    (hb : Runtime.TypeEnv.Downward bound) (hf : Runtime.TypeEnv.Downward free)
    (budget : Nat) (premises : ∀ p ∈ inst.premises, p.Holds σ)
    (e : EnvAt bound free σ budget ([.recursive contract].map (mapBinding f lc))) :
    Runtime.TermAt bound free σ budget (RecursiveHMUniform.demand universal counts f)
      (loop.substN 0 e.terms) := by
  have ready : ScopedDerives.RuntimeReady universal.typing := recursiveIdentityReady
  let result := RecursiveHMUniform.fromCertified universal inst f lc scope capturedOpaqueEnvironment fixed
  have specialized := RecursiveHMUniform.fromCertified_runtimeReady universal ready inst f lc scope
    arguments capturedOpaqueEnvironment fixed
  have demandSupport : Runtime.Supported (RecursiveHMUniform.demand universal counts f) := by
    change Runtime.Supported (SchemeSpecialization.mapFree f
      (CountSubstitution.bounds ([7].zip counts) (.arrow (exact (.fvar 90)) (exact (.fvar 90)))))
    exact ((Runtime.Supported.arrow (.list .fvar) (.list .fvar)).counts _).types f arguments
  exact result.termAt specialized demandSupport bound free σ hb hf budget premises e

#print axioms universalRecursiveRhsRuntime

end FHM.Bounds.RecursiveHMJudgementTests
