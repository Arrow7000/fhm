import FHM.Bounds.RecursiveHMUniform
import FHM.Bounds.HMDeclaredCoordinates
import FHM.Bounds.Found

namespace FHM.Bounds.RecursiveHMUniformTests

open HMDeclaredGroup RecursiveHMJudgement RecursiveHMUniform
open SurfaceBridge.Provenance

private def count (i : Nat) : Count := .var ⟨.rigid, i⟩
private def argument (i : Nat) : BoundsTy :=
  .list (count 7) (count 7) (.prim (if i % 2 == 0 then .int else .char))
private theorem argumentLC : ∀ i, (Synth.BoundsTy.toTy (argument i)).IsLC := by
  intro i
  apply (Ty.bvarsBelow_iff _).mp
  simp [argument, Synth.BoundsTy.toTy, listTy, Ty.bvarsBelow, TyList.bvarsBelow]
private theorem argumentScope : ∀ i, ScopedScheme.BoundsScoped [7] (argument i) := by
  intro i
  exact ScopedScheme.boundsScopedBool_sound (by
    simp [argument, count, ScopedScheme.boundsScopedBool, ScopedScheme.countScopedBool])

private def signature (i : Nat) (swap : Bool := false) : PolyTy :=
  ⟨2, .arrow (.bl (.solid (count i)) (.solid (count i)) (.bvar (if swap then 1 else 0)))
    (.bl (.solid (count i)) (.solid (count i)) (.bvar (if swap then 0 else 1)))⟩

private def exercise {output metadata path captures premises typeCaptures env index vectors}
    {ps : Interfaces output metadata path captures premises typeCaptures index vectors}
    (ms : CheckedMembers env ps) (uniform : RecursiveHMUniform.Members argument argumentLC argumentScope ms) :
    Except String Bool := do
  match ms, uniform with
  | .nil, .nil => pure true
  | .cons (p := p) checked rest, .cons obligations others =>
      let cert := checked.certificate
      let counts := p.quantified.map (fun _ => Count.lit 3)
      let inst ← cert.interface.scheme.counts.instantiate counts [7]
      let r := obligations counts inst
      let own : Contract := ⟨cert.interface.scheme, _, RecursiveHMContract.fromOpaque cert.implementation.opening⟩
      let fixed ← RecursiveHMEnvironment.checkTemplateFixed argument [.recursive own]
      have sourceFixed : ∀ i ∈ cert.interface.scheme.hm.body.freeVars, argument i = .fvar i :=
        fixed.down own (by simp)
      let signed := RecursiveHMUniform.atSignedNode p.declaration.node cert r sourceFixed
      let bounds := signed.typed.actual
      let exactCounts := match bounds with
        | .prim .int => true
        | .arrow (.list lo hi (.list a b _)) (.list lo' hi' (.list a' b' _)) =>
            lo == .lit 3 && hi == .lit 3 && lo' == .lit 3 && hi' == .lit 3 &&
            a == count 7 && b == count 7 && a' == count 7 && b' == count 7
        | _ => false
      let tail ← exercise rest others
      pure (exactCounts && tail)

private def actual : Except String Bool := do
  let ctors : CtorEnv := (elabDecls preludeDecls).getD []
  let source := Expr.letRec [some (signature 7), some (signature 8 true), some ⟨0, .prim .int⟩]
    [.lambda none (.app (.var 2) (.var 0)), .lambda none (.app (.var 1) (.var 0)), .primLit (.int 0)]
    (.primLit (.int 0))
  let a ← match inferFound ctors source with
    | some a => pure a | none => throw "test: permuted mutual group HM inference failed"
  let metadata : Scope.Metadata :=
    { telescopes := [⟨.letRec [] 0, [(⟨"n"⟩, 7)]⟩, ⟨.letRec [] 1, [(⟨"m"⟩, 8)]⟩] }
  let g ← HMDeclaredCoordinates.check a.output metadata [] (schemes := a.binderSchemes)
  let env := g.checked.interfaces.contracts.map Binding.recursive ++ []
  let fixed ← RecursiveHMEnvironment.checkTemplateFixed argument env
  let all := RecursiveHMUniform.allMembers g.checked.members argument argumentLC argumentScope fixed.down
  for offset in List.finRange g.checked.exports.length do
    let selected := g.checked.members.memberAt offset.val offset.isLt
    if selected.sourceIndex != offset.val ||
        !selected.member.declaration.node.inner.stripFound.varsBelow g.checked.rhss.length then
      throw "test: total universal-member selection lost original source order or group scope"
    let counts := selected.member.quantified.map (fun _ => Count.lit 3)
    let inst ← selected.rhs.certificate.interface.scheme.counts.instantiate counts [7]
    let result := all.memberAt offset.val offset.isLt counts inst
    let bounds := (RecursiveHMUniform.atNode selected.member.declaration.node
      selected.rhs.certificate.implementation result).actual
    if !(match bounds with | .arrow _ _ | .prim .int => true | _ => false) then
      throw "test: ordered universal-member selection lost its actual specialized RHS proof"
  exercise g.checked.members all

private def changedCapture : Except String Bool := do
  let template ← HMCountScheme.decode ⟨0, .arrow (.fvar 90) (.fvar 90)⟩ [] []
  let found := Ty.arrow (.fvar 90) (.fvar 90)
  let fixed ← RecursiveHMContract.fix template found []
  let c : Contract := ⟨template, found, fixed⟩
  match RecursiveHMEnvironment.checkTemplateFixed argument [.recursive c] with
  | .ok _ => throw "test: uniform group map rewrote a closed template's captured HM identity"
  | .error _ => pure true

private def bodySignature (i : Nat) : PolyTy :=
  ⟨1, .arrow (.bl (.solid (count i)) (.solid (count i)) (.bvar 0))
    (.bl (.solid (count i)) (.solid (count i)) (.bvar 0))⟩

/-- Actual argument origins determine both count and HM instantiation; the
    second call crosses a local binder and uses the SAME export at Char. -/
private def bodyCalls (badLocal : Bool := false) (polyLocal : Bool := false)
    (capturedLocal : Bool := false) (forgedRoot : Bool := false)
    (nested : Bool := false) : Except String Bool := do
  let ctors : CtorEnv := (elabDecls preludeDecls).getD []
  let singleton (p : PrimLitExpr) : Expr :=
    .app (.app (.ctor consCtorName) (.primLit p)) (.ctor nilCtorName)
  let localAnn : Option PolyTy := if polyLocal then
    some ⟨1, if capturedLocal then .prim .int else listTy (.prim .int)⟩ else if badLocal then
    some ⟨0, .bl (.solid (.lit 2)) (.solid (.lit 2)) (.prim .int)⟩ else none
  let secondArg := if nested then
    .app (.app (.ctor consCtorName) (singleton (.char 'a'))) (.ctor nilCtorName)
    else singleton (.char 'a')
  let localRhs := if polyLocal && capturedLocal then .var 2 else if polyLocal then singleton (.int 1) else
    .app (.var 0) (singleton (.int 1))
  let source := Expr.letRec
    [some (bodySignature 7), some (bodySignature 8), some ⟨0, .prim .int⟩]
    [.lambda none (.app (.var 2) (.var 0)), .lambda none (.app (.var 1) (.var 0)), .primLit (.int 0)]
    (.letIn localAnn localRhs
      (.app (.var 1) secondArg))
  let a ← match inferFound ctors source with
    | some a => pure a | none => throw "test: generalized body HM inference failed"
  let metadata : Scope.Metadata :=
    { telescopes := [⟨.letRec [] 0, [(⟨"n"⟩, 7)]⟩, ⟨.letRec [] 1, [(⟨"m"⟩, 8)]⟩] }
  let output := if forgedRoot then
    match a.output with | .found _ inner => .found (.prim .int) inner | e => e
    else a.output
  let program ← RecursiveHMUniform.checkClosedProgram output metadata a.binderSchemes
  let result := program.body
  if !result.runtimeSafety?.isSome then
    throw "test: supported recursive Int/Char body report lost its runtime theorem"
  let exact := match result.bounds with
    | .list lo hi elem =>
        let inner := match elem with
          | .prim .char => !nested
          | .list a b (.prim .char) => nested &&
              a.eval (fun _ => 0) == .ofNat 1 && b.eval (fun _ => 0) == .ofNat 1
          | _ => false
        lo.eval (fun _ => 0) == .ofNat 1 && hi.eval (fun _ => 0) == .ofNat 1 && inner
    | _ => false
  pure (exact && program.assembled.checked.exports.length == 3 &&
    exactlyOnce (logicalCorePaths output) (result.nodes.map (·.path)))

example {output metadata} (program : ProgramResult output metadata) :
    BodyDerives [] [] [] [] output.stripFound program.body.bounds := program.body.typing

example {output metadata Δ} (program : ProgramResult output metadata)
    (premises : (⟨Δ, []⟩ : ForallProblem).Valid) :
    BodyDerives [] [] Δ [] output.stripFound program.body.bounds :=
  program.body.typing.assuming premises

/-- The report theorem uses the exact artifact-indexed derivation, not a
    replacement program or an assumed runtime contract. Readiness remains an
    explicit supported-fragment obligation until the checker bridge closes it. -/
example {output metadata} (program : ProgramResult output metadata)
    (ready : BodyDerives.RuntimeReady program.body.typing)
    (bound free : Runtime.TypeEnv) (σ : Assign)
    (hb : Runtime.TypeEnv.Downward bound) (hf : Runtime.TypeEnv.Downward free) :
    Runtime.Safe bound free σ program.body.bounds output.stripFound :=
  ready.safeClosed bound free σ hb hf (by simp)

private def runtimeIdScheme : HMCountScheme.Scheme :=
  { hm := ⟨1, .arrow (.bvar 0) (.bvar 0)⟩
    counts := ⟨[], [], [], .arrow (.bvar 0) (.bvar 0)⟩
    hmWF := by exact .arrow (.bvar (by decide)) (.bvar (by decide))
    countWF := by simp [ScopedScheme.Scheme.WF, ScopedScheme.BoundsScoped]
    shape := by simp [Synth.BoundsTy.toTy] }

private def runtimeIdUse (p : PrimTy) :
    HMCountScheme.Use runtimeIdScheme [] (.arrow (.prim p) (.prim p)) [] :=
  { counts := []
    countInstance :=
      { arity := rfl
        wf := runtimeIdScheme.countWF
        argsScoped := by simp
        finiteArgs := by simp
        capturesScoped := by simp [runtimeIdScheme]
        bodyScoped := by simp [runtimeIdScheme, CountSubstitution.bounds, ScopedScheme.BoundsScoped]
        premisesScoped := by simp [runtimeIdScheme] }
    usable := by intro σ _ goal member; simp [ScopedScheme.Instance.premises, runtimeIdScheme] at member
    types := [.prim p]
    arity := rfl
    typesLC := by
      intro a member
      obtain rfl := List.mem_singleton.mp member
      have closed : (Ty.prim p).IsLC := .prim
      simpa only [Synth.BoundsTy.toTy] using closed
    typesScoped := rfl
    shape := by simp [runtimeIdScheme, TypeSubstitution.combined, CountSubstitution.bounds,
      TypeSubstitution.substitute, SchemeUse.vector, Synth.BoundsTy.toTy, Ty.eraseBounds] }

private def runtimePolyBody : Expr :=
  .letIn none (.app (.var 0) (.primLit (.int 1)))
    (.app (.var 1) (.primLit (.char 'a')))

private theorem runtimePolyTyping :
    BodyDerives [] [] [] [.exported runtimeIdScheme] runtimePolyBody (.prim .char) :=
  .letMono True.intro
    (.app (.varExported rfl (runtimeIdUse .int)) .literal (SemanticSub.refl _ _))
    (.app (.varExported rfl (runtimeIdUse .char)) .literal (SemanticSub.refl _ _))

private theorem runtimePolyReady : BodyDerives.RuntimeReady runtimePolyTyping := by
  have intReady : BodyDerives.RuntimeReady
      (BodyDerives.varExported (ids := []) (rows := []) (env := [.exported runtimeIdScheme])
        (i := 0) rfl (runtimeIdUse .int)) :=
    .varExported rfl (runtimeIdUse .int) (.arrow .prim .prim)
      (by intro a member; obtain rfl := List.mem_singleton.mp member; exact .prim)
  have charReady : BodyDerives.RuntimeReady
      (BodyDerives.varExported (ids := []) (rows := [])
        (env := [.mono (.prim .int), .exported runtimeIdScheme])
        (i := 1) rfl (runtimeIdUse .char)) :=
    .varExported rfl (runtimeIdUse .char) (.arrow .prim .prim)
      (by intro a member; obtain rfl := List.mem_singleton.mp member; exact .prim)
  exact BodyDerives.RuntimeReady.letMono (ann := none) True.intro
    (.app (SemanticSub.refl _ _) intReady .literal)
    (.app (SemanticSub.refl _ _) charReady .literal)

/-- The SAME generalized identity is called at Int and Char across a mono local
    binder. Its runtime meaning is proved from lambda reduction, not asserted. -/
theorem generalizedBodyRuntimeSafe (bound free : Runtime.TypeEnv) (σ : Assign)
    (hb : Runtime.TypeEnv.Downward bound) (hf : Runtime.TypeEnv.Downward free) :
    Runtime.Safe bound free σ (.prim .char)
      (runtimePolyBody.substN 0 [.lambda none (.var 0)]) := by
  intro budget
  let e : BodyEnvAt bound free σ budget [.exported runtimeIdScheme] :=
    { terms := [.lambda none (.var 0)]
      arity := rfl
      closed := by intro term member; obtain rfl := List.mem_singleton.mp member; rfl
      denotes := by
        intro i inside
        have zero : i = 0 := by simp at inside; omega
        subst i
        intro Δ found caller used _ _
        change Runtime.TermAt bound free σ budget
          (TypeSubstitution.combined ([] : List (Nat × Count)) (SchemeUse.vector used.types)
            (.arrow (.bvar 0) (.bvar 0))) (.lambda none (.var 0))
        simp only [TypeSubstitution.combined, CountSubstitution.bounds, TypeSubstitution.substitute]
        exact Runtime.TermAt.value (.lambda _ _) (Runtime.ValueAt.identity hb hf) }
  exact runtimePolyReady.termAt bound free σ hb hf budget (by simp) e

#print axioms generalizedBodyRuntimeSafe

private def scopedBodySource : Expr :=
  .lambda (some (.bvar 0)) (.lambda (some (.fvar 90)) (.var 1))

/-- Lexical annotation slots and captured free identities are interpreted
    independently in the existing body rules; the source annotations stay put. -/
theorem scopedBodyTyping (types slots : Nat → BoundsTy) :
    ScopedBodyDerives types slots [] [] [] [] scopedBodySource
      (.arrow (slots 0) (.arrow (types 90) (slots 0))) := by
  refine .lambda ?_ (.lambda ?_ (.varMono rfl))
  · refine ⟨⟨.bvar 0, True.intro, by simp [Synth.BoundsTy.toTy, Ty.eraseBounds]⟩,
      by simp [ScopedAnnotation.decode, pure, Except.pure], ?_⟩
    exact SemanticSub.refl _ _
  · refine ⟨⟨.fvar 90, True.intro, by simp [Synth.BoundsTy.toTy, Ty.eraseBounds]⟩,
      by simp [ScopedAnnotation.decode, pure, Except.pure], ?_⟩
    exact SemanticSub.refl _ _

private theorem scopedBodyReady (types slots : Nat → BoundsTy)
    (lexical : Runtime.Supported (slots 0)) (captured : Runtime.Supported (types 90)) :
    BodyDerives.RuntimeReady (scopedBodyTyping types slots) := by
  refine BodyDerives.RuntimeReady.lambda (ann := some (.bvar 0)) ?_ lexical
    (BodyDerives.RuntimeReady.lambda (ann := some (.fvar 90)) ?_ captured
      (.varMono (i := 1) rfl lexical))
  · refine ⟨⟨.bvar 0, True.intro, by simp [Synth.BoundsTy.toTy, Ty.eraseBounds]⟩,
      by simp [ScopedAnnotation.decode, pure, Except.pure], ?_⟩
    exact SemanticSub.refl _ _
  · refine ⟨⟨.fvar 90, True.intro, by simp [Synth.BoundsTy.toTy, Ty.eraseBounds]⟩,
      by simp [ScopedAnnotation.decode, pure, Except.pure], ?_⟩
    exact SemanticSub.refl _ _

theorem scopedBodyRuntimeSafe (types slots : Nat → BoundsTy)
    (lexical : Runtime.Supported (slots 0)) (captured : Runtime.Supported (types 90))
    (bound free : Runtime.TypeEnv) (σ : Assign)
    (hb : Runtime.TypeEnv.Downward bound) (hf : Runtime.TypeEnv.Downward free) :
    Runtime.Safe bound free σ (.arrow (slots 0) (.arrow (types 90) (slots 0))) scopedBodySource :=
  (scopedBodyReady types slots lexical captured).safeClosed bound free σ hb hf (by simp)

example {Δ} (hp : (⟨Δ, []⟩ : ForallProblem).Valid) :
    BodyDerives.RuntimeReady (runtimePolyTyping.assuming hp) := runtimePolyReady.assuming hp

example {output metadata Δ} (program : ProgramResult output metadata)
    (hp : (⟨Δ, []⟩ : ForallProblem).Valid) :
    (program.body.assuming hp).bounds = program.body.bounds ∧
    (program.body.assuming hp).nodes = program.body.nodes ∧
    (program.body.assuming hp).runtimeReady.isSome = program.body.runtimeReady.isSome := by
  simp [BodyResult.assuming]

#print axioms scopedBodyTyping
#print axioms scopedBodyRuntimeSafe

private def runtimeLocalRhs : Expr := .lambda (some (.bvar 0)) (.var 0)
private def runtimeLocalProgram : Expr := .letIn (some runtimeIdScheme.hm) runtimeLocalRhs runtimePolyBody

private theorem runtimeLocalAnnotation : LocalAnnotationOK runtimeIdScheme (some runtimeIdScheme.hm) := by
  let declared : HMCountScheme.Annotated runtimeIdScheme.hm [] [] [] :=
    { source :=
        { annotation :=
            { bounds := .arrow (.bvar 0) (.bvar 0)
              inScope := ⟨True.intro, True.intro⟩
              shape := by simp [runtimeIdScheme, Synth.BoundsTy.toTy, Ty.eraseBounds] }
          wf := runtimeIdScheme.countWF
          decoded := by simp [runtimeIdScheme, ScopedAnnotation.decode, pure, Except.pure,
            bind, Except.bind] }
      hmWF := runtimeIdScheme.hmWF }
  refine ⟨declared, ?_⟩
  simp [declared, HMCountScheme.Annotated.scheme, ScopedAnnotation.Contract.scheme,
    runtimeIdScheme, PolyTy.eraseBounds, Ty.eraseBounds]

private def runtimeLocalFrame : LocalFrame runtimeIdScheme [] runtimeLocalRhs where
  owned := [91]
  arity := rfl
  distinct := by decide
  fresh := by simp [runtimeLocalRhs, Expr.tyFreeVars, runtimeIdScheme, Ty.freeVars]
  countFresh := by simp [runtimeIdScheme]
  capturesScoped := by simp [runtimeIdScheme]

private theorem runtimeLocalParam (types slots : Nat → BoundsTy) :
    ScopedHMAnnotation.ParamOK types slots [] [] []
      (some (.bvar 0)) (slots 0) := by
  refine ⟨⟨.bvar 0, True.intro, by simp [Synth.BoundsTy.toTy, Ty.eraseBounds]⟩,
    by simp [ScopedAnnotation.decode, pure, Except.pure], ?_⟩
  exact SemanticSub.refl _ _

private theorem runtimeLocalOpaqueTyping :
    ScopedDerives BoundsTy.fvar
      (localSlots (some runtimeIdScheme.hm) BoundsTy.bvar (runtimeLocalFrame.owned.map BoundsTy.fvar))
      [] [] [] [] runtimeLocalRhs (.arrow (.fvar 91) (.fvar 91)) := by
  have typed : ScopedDerives BoundsTy.fvar
      (localSlots (some runtimeIdScheme.hm) BoundsTy.bvar (runtimeLocalFrame.owned.map BoundsTy.fvar))
      [] [] [] []
      runtimeLocalRhs (.arrow
        (localSlots (some runtimeIdScheme.hm) BoundsTy.bvar (runtimeLocalFrame.owned.map BoundsTy.fvar) 0)
        (localSlots (some runtimeIdScheme.hm) BoundsTy.bvar (runtimeLocalFrame.owned.map BoundsTy.fvar) 0)) :=
    .lambda (runtimeLocalParam _ _) (.varMono rfl)
  simpa [localSlots, runtimeIdScheme, runtimeLocalFrame, SchemeUse.vector] using typed

private def runtimeLocalCertificate :
    RecursiveHMUniversal.Certified runtimeIdScheme (.arrow (.fvar 91) (.fvar 91)) [] []
      runtimeLocalRhs BoundsTy.fvar
      (localSlots (some runtimeIdScheme.hm) BoundsTy.bvar (runtimeLocalFrame.owned.map BoundsTy.fvar)) where
  opening :=
    { ids := [91]
      arity := rfl
      distinct := by decide
      fresh := by simp [runtimeIdScheme, Ty.freeVars]
      shape := by simp [runtimeIdScheme, HMCountScheme.opened, SchemeUse.vector,
        TypeSubstitution.substitute, Synth.BoundsTy.toTy, Ty.eraseBounds]
      lc := .arrow .fvar .fvar }
  actual := .arrow (.fvar 91) (.fvar 91)
  shape := by simp [Synth.BoundsTy.toTy, Ty.eraseBounds]
  actualScope := by simp [ScopedScheme.BoundsScoped]
  typing := runtimeLocalOpaqueTyping
  inclusion := by
    simpa [HMCountScheme.Opening.bounds, HMCountScheme.opened, runtimeIdScheme,
      TypeSubstitution.substitute, SchemeUse.vector] using
      SemanticSub.refl [] (.arrow (.fvar 91) (.fvar 91))
  typeFresh := by simp
  countFresh := by simp

private theorem runtimeLocalOpaqueReady : ScopedDerives.RuntimeReady runtimeLocalCertificate.typing := by
  have element : Runtime.Supported
      (localSlots (some runtimeIdScheme.hm) BoundsTy.bvar (runtimeLocalFrame.owned.map BoundsTy.fvar) 0) := by
    simpa [localSlots, runtimeIdScheme, runtimeLocalFrame, SchemeUse.vector] using
      (Runtime.Supported.fvar (i := 91))
  have ready : ScopedDerives.RuntimeReady
      (ScopedDerives.lambda (env := [])
        (runtimeLocalParam BoundsTy.fvar
          (localSlots (some runtimeIdScheme.hm) BoundsTy.bvar (runtimeLocalFrame.owned.map BoundsTy.fvar)))
        (ScopedDerives.varMono (i := 0) rfl)) :=
    .lambda (ann := some (.bvar 0)) (runtimeLocalParam _ _) element (.varMono (i := 0) rfl element)
  simpa [runtimeLocalCertificate, localSlots, runtimeIdScheme, runtimeLocalFrame, SchemeUse.vector] using ready

private def runtimeLocalInstances (calleeΔ : List Constraint) (found : Ty) (caller : List Nat)
    (used : HMCountScheme.Use runtimeIdScheme calleeΔ found caller) :=
  localRhsInstances (Δ := []) runtimeLocalFrame runtimeLocalAnnotation runtimeLocalCertificate rfl used

private theorem runtimeLocalCasesReady (calleeΔ : List Constraint) (found : Ty) (caller : List Nat)
    (used : HMCountScheme.Use runtimeIdScheme calleeΔ found caller)
    (arguments : ∀ a ∈ used.types, Runtime.Supported a) :
    BodyDerives.RuntimeReady (runtimeLocalInstances calleeΔ found caller used) := by
  exact localRhsInstances_runtimeReady runtimeLocalFrame runtimeLocalAnnotation runtimeLocalCertificate rfl
    runtimeLocalOpaqueReady used arguments

private theorem runtimeLocalTyping : BodyDerives [] [] [] [] runtimeLocalProgram (.prim .char) :=
  ScopedBodyDerives.letExported runtimeLocalFrame runtimeLocalAnnotation (by decide)
    runtimeLocalInstances runtimePolyTyping

private theorem runtimeLocalReady : BodyDerives.RuntimeReady runtimeLocalTyping :=
  .letExported (s := runtimeIdScheme) (ann := some runtimeIdScheme.hm)
    (ids := []) (rows := []) (Δ := []) (env := [])
    runtimeLocalFrame runtimeLocalAnnotation (by decide) runtimeLocalInstances runtimeLocalCasesReady runtimePolyReady

/-- Instantiating a local telescope cannot reinterpret a captured source identity. -/
example {s ids rhs} (frame : LocalFrame s ids rhs) (parent : Nat → BoundsTy)
    (arguments : List BoundsTy) (captured : 90 ∈ rhs.tyFreeVars) :
    localTypes frame.owned parent arguments 90 = parent 90 :=
  frame.annotationTypes parent arguments captured

/-- Slots beyond the local telescope retain the enclosing annotation interpretation. -/
example (parent : Nat → BoundsTy) (arguments : List BoundsTy) :
    localSlots (some runtimeIdScheme.hm) parent arguments 1 = parent 0 := by
  simpa [runtimeIdScheme] using localSlots_parent (some runtimeIdScheme.hm) parent arguments 0

/-- A caller count inside a full HM argument survives even when the local
    source count substitution uses the same numeric identity. -/
example : SchemeSpecialization.mapFree
    (SchemeSpecialization.argument [91] (SchemeUse.vector [.list (count 91) (count 91) (.prim .int)]))
    (CountSubstitution.bounds [(91, .lit 3)]
      (localSlots (some runtimeIdScheme.hm) BoundsTy.bvar [.fvar 91] 0)) =
    .list (count 91) (count 91) (.prim .int) := by
  simpa [localSlots, runtimeIdScheme, SchemeUse.vector] using
    congrFun (localSlots_specialize (some runtimeIdScheme.hm) [91] [(91, .lit 3)]
      [.list (count 91) (count 91) (.prim .int)] (by decide) (by simp [runtimeIdScheme])) 0

/-- A generalized LOCAL is introduced from actual universal RHS derivations,
    then used at Int and Char. No generalized runtime contract is postulated. -/
theorem universalLocalRuntimeSafe (bound free : Runtime.TypeEnv) (σ : Assign)
    (hb : Runtime.TypeEnv.Downward bound) (hf : Runtime.TypeEnv.Downward free) :
    Runtime.Safe bound free σ (.prim .char) runtimeLocalProgram :=
  runtimeLocalReady.safeClosed bound free σ hb hf (by simp)

theorem incorrectUniversalRhsRejected {types slots ids rows Δ env} :
    ¬ ScopedBodyDerives types slots ids rows Δ env (.primLit (.int 1)) (.prim .char) := by
  intro typing
  have impossible := typing.primLitBounds (.int 1) rfl
  cases impossible

private theorem nilIntervalWidening :
    SemanticSub [] (.list (.lit 0) (.lit 0) (.prim .int))
      (.list (.lit 0) (.lit 2) (.prim .int)) := by
  apply SemanticSub.list
  · simp [ForallProblem.Valid, Interval.subGoals, Constraint.Holds, Count.eval, ExtNat.le]
  · exact .prim

private theorem widenedNilTyping : BodyDerives [] [] [] [] (.ctor nilCtorName)
    (.list (.lit 0) (.lit 2) (.prim .int)) :=
  .subsumption .nil nilIntervalWidening

/-- A real narrower implementation may satisfy a wider declared demand;
    this changes neither the source term nor its underlying HM type. -/
theorem widenedNilRuntimeSafe (bound free : Runtime.TypeEnv) (σ : Assign)
    (hb : Runtime.TypeEnv.Downward bound) (hf : Runtime.TypeEnv.Downward free) :
    Runtime.Safe bound free σ (.list (.lit 0) (.lit 2) (.prim .int)) (.ctor nilCtorName) := by
  have ready : BodyDerives.RuntimeReady widenedNilTyping :=
    .subsumption nilIntervalWidening (.nil .prim) (.list .prim)
  exact ready.safeClosed bound free σ hb hf (by simp)

#print axioms universalLocalRuntimeSafe
#print axioms incorrectUniversalRhsRejected
#print axioms widenedNilRuntimeSafe

private def unsupportedIntermediate : Except String Bool := do
  let opaqueName : TyName := ⟨"Opaque"⟩
  let domain := BoundsTy.custom opaqueName []
  let e := Expr.found (.prim .int)
    (.app (.found (.arrow (.customTy opaqueName []) (.prim .int)) (.var 0))
      (.found (.customTy opaqueName []) (.var 1)))
  let result ← RecursiveHMWalk.walkScoped BoundsTy.fvar BoundsTy.bvar [] [] [] []
    [.mono (.arrow domain (.prim .int)), .mono domain] [] e []
  pure ((Runtime.supported? result.bounds).isSome && !result.runtimeReady.isSome)

private def bodyMatches (kind : Nat) (onlyNil : Bool := false) (onlyCons : Bool := false)
    (badDemand : Bool := false) :
    Except String Bool := do
  let ctors : CtorEnv := (elabDecls preludeDecls).getD []
  let singleton : Expr := .app (.app (.ctor consCtorName) (.primLit (.int 1))) (.ctor nilCtorName)
  let call (i : Nat) (arg : Expr) := Expr.app (.var i) arg
  let body := if kind == 0 then
    .match_ (.ctor BoolBranches.trueCtorName)
      [(.named BoolBranches.trueCtorName 0, call 0 singleton),
        (.named BoolBranches.falseCtorName 0, call 0 (.ctor nilCtorName))]
    else .match_ (call 0 (if kind == 2 then .ctor nilCtorName else singleton))
      (if onlyNil then [(.named nilCtorName 0, call 0 (.ctor nilCtorName))] else if onlyCons then
        [(.named consCtorName 2, call 2 (.var 1))] else
        [(.named consCtorName 2, call 2 (.var 1)),
          (.named nilCtorName 0, call 0 (.ctor nilCtorName))])
  let source := Expr.letRec [some (bodySignature 7)]
    [.lambda none (.app (.var 1) (.var 0))] body
  let a ← match inferFound ctors source with
    | some a => pure a | none => throw "test: generalized match HM inference failed"
  let metadata : Scope.Metadata := { telescopes := [⟨.letRec [] 0, [(⟨"n"⟩, 7)]⟩] }
  let expected := if badDemand then some (BoundsTy.list (.lit 2) (.lit 2) (.prim .int)) else none
  let program ← checkClosedProgram a.output metadata a.binderSchemes expected
  if !program.body.runtimeSafety?.isSome then
    throw "test: supported recursive List/Bool match report lost its runtime theorem"
  let exact := match program.body.bounds with
    | .list lo hi _ => lo.eval (fun _ => 0) == .ofNat 0 &&
        hi.eval (fun _ => 0) == .ofNat (if kind == 0 then 1 else 0)
    | _ => false
  pure (exact && exactlyOnce (logicalCorePaths a.output) (program.body.nodes.map (·.path)))

private def bodyPatternGuard : Bool :=
  let e := Expr.found (.prim .int) (.match_ (.found (listTy (.prim .int)) (.var 0))
    [(.named consCtorName 1, .found (.prim .int) (.primLit (.int 1))),
      (.wildcard, .found (.prim .int) (.primLit (.int 0)))])
  match walkBody [] [] [] [] [.mono (.list (.lit 1) (.lit 1) (.prim .int))] [] e [] with
  | .error message => (message.splitOn "unsupported pattern or constructor arity").length > 1
  | .ok _ => false

private def bodyBoolCoverageGuard : Bool :=
  let e := Expr.found (.prim .int) (.match_ (.found (.customTy boolTyName []) (.ctor BoolBranches.trueCtorName))
    [(.named BoolBranches.trueCtorName 0, .found (.prim .int) (.primLit (.int 0)))])
  match walkBody [] [] [] [] [] [] e [] with
  | .error message => (message.splitOn "missing False coverage").length > 1
  | .ok _ => false

/-- A context assumption supplies the actual argument origin; quantified count
    7 is instantiated with caller count 7, but its precondition still needs proof. -/
private def bodyCallerPremises (established : Bool) : Except String Bool := do
  let premise : Constraint := ⟨.lit 1, count 7⟩
  let s ← HMCountScheme.decode (bodySignature 7) [7] [] [premise]
  let hm := listTy (.prim .int)
  let e := Expr.found hm (.app (.found (.arrow hm hm) (.var 0)) (.found hm (.var 1)))
  let Δ := if established then [premise] else []
  let result ← walkBody [] [] [7] Δ
    [.exported s, .mono (.list (count 7) (count 7) (.prim .int))] [] e []
  pure (result.bounds.pretty == (BoundsTy.list (count 7) (count 7) (.prim .int)).pretty)

private def fullBodySpine (kind : Nat := 0) (badFirst : Bool := false)
    (partialCall : Bool := false) (forgedPrefix : Bool := false)
    (recursive : Bool := false) : Except String Bool := do
  let list (n : Count) (elem : Ty) := Ty.bl (.solid n) (.solid n) elem
  let σ : PolyTy := if kind == 2 then ⟨1, .arrow (.bvar 0) (.arrow (.bvar 0) (.bvar 0))⟩
    else if kind == 1 then
      ⟨1, .arrow (list (.add (count 7) (.lit 1)) (.bvar 0))
        (.arrow (list (count 7) (.bvar 0)) (list (count 7) (.bvar 0)))⟩
    else ⟨2, .arrow (list (count 7) (.bvar 0))
      (.arrow (list (count 8) (.bvar 1)) (list (count 8) (.bvar 1)))⟩
  let singleton (p : PrimLitExpr) : Expr :=
    .app (.app (.ctor consCtorName) (.primLit p)) (.ctor nilCtorName)
  let double (p : PrimLitExpr) : Expr :=
    .app (.app (.ctor consCtorName) (.primLit p)) (singleton p)
  let first := if kind == 1 && !badFirst then double (.int 1) else singleton (.int 1)
  let second := if kind == 0 then double (.char 'a') else
    if kind == 2 then double (.int 2) else singleton (.int 2)
  let firstCall := Expr.app (.var 0) first
  let rhs := Expr.lambda none (.lambda none
    (if recursive then .app (.app (.var 2) (.var 1)) (.var 0) else .var 0))
  let source := Expr.letRec [some σ] [rhs]
    (if partialCall then firstCall else .app firstCall second)
  let ctors : CtorEnv := (elabDecls preludeDecls).getD []
  let a ← match inferFound ctors source with
    | some a => pure a | none => throw "test: full generalized spine HM inference failed"
  let metadata : Scope.Metadata :=
    if kind == 2 then {} else
      { telescopes := [⟨.letRec [] 0, if kind == 1 then [(⟨"n"⟩, 7)] else [(⟨"n"⟩, 7), (⟨"m"⟩, 8)]⟩] }
  let output := if forgedPrefix then
    match a.output with
    | .found root (.letRec anns rhss (.found hm (.app (.found _ prefixInner) arg))) =>
        .found root (.letRec anns rhss (.found hm (.app (.found (.prim .int) prefixInner) arg)))
    | e => e
    else a.output
  let program ← checkClosedProgram output metadata a.binderSchemes
  if !program.body.runtimeSafety?.isSome then
    throw "test: supported full recursive application spine lost its runtime theorem"
  let exact := match program.body.bounds with
    | .list lo hi (.prim p) => lo.eval (fun _ => 0) == .ofNat (if kind == 0 then 2 else 1) &&
        hi.eval (fun _ => 0) == .ofNat (if kind == 0 then 2 else 1) &&
        p == (if kind == 0 then .char else .int)
    | _ => false
  pure (exact && exactlyOnce (logicalCorePaths output) (program.body.nodes.map (·.path)))

private def fullBodyCapture : Except String Bool := do
  let list (elem : Ty) := Ty.bl (.solid (count 7)) (.solid (count 7)) elem
  let s ← HMCountScheme.decode ⟨2, .arrow (list (.bvar 0)) (.arrow (list (.bvar 1)) (list (.bvar 1)))⟩ [7] []
  let int := BoundsTy.list (count 7) (count 7) (.prim .int)
  let char := BoundsTy.list (count 7) (count 7) (.prim .char)
  let first := BoundsTy.list (.lit 1) (.lit 1) int
  let second := BoundsTy.list (.lit 1) (.lit 1) char
  let a := Synth.BoundsTy.toTy first
  let b := Synth.BoundsTy.toTy second
  let e := Expr.found b (.app (.found (.arrow b b)
    (.app (.found (.arrow a (.arrow b b)) (.var 0)) (.found a (.var 1)))) (.found b (.var 2)))
  let result ← walkBody [] [] [7] [] [.exported s, .mono first, .mono second] [] e []
  pure (result.bounds.pretty == second.pretty && exactlyOnce (logicalCorePaths e) (result.nodes.map (·.path)))

private def fullMutualSpine : Except String Bool := do
  let signature (n m : Nat) : PolyTy :=
    let list (id : Nat) (elem : Ty) := Ty.bl (.solid (count id)) (.solid (count id)) elem
    ⟨2, .arrow (list n (.bvar 0)) (.arrow (list m (.bvar 1)) (list m (.bvar 1)))⟩
  let rhs (callee : Nat) := Expr.lambda none (.lambda none (.app (.app (.var callee) (.var 1)) (.var 0)))
  let singleton (p : PrimLitExpr) : Expr :=
    .app (.app (.ctor consCtorName) (.primLit p)) (.ctor nilCtorName)
  let first := Expr.app (.app (.var 0) (singleton (.int 1))) (singleton (.char 'a'))
  -- The local binder shifts g to index 2; its independent exit use reverses
  -- the full caller HM arguments while both RHSs retain the shared fixed vector.
  let second := Expr.app (.app (.var 2) (singleton (.char 'b'))) (singleton (.int 2))
  let source := Expr.letRec [some (signature 7 8), some (signature 9 10)] [rhs 3, rhs 2]
    (.letIn none first second)
  let ctors : CtorEnv := (elabDecls preludeDecls).getD []
  let a ← match inferFound ctors source with
    | some a => pure a | none => throw "test: full mutual recursive spine HM inference failed"
  let metadata : Scope.Metadata := { telescopes :=
    [⟨.letRec [] 0, [(⟨"n"⟩, 7), (⟨"m"⟩, 8)]⟩,
      ⟨.letRec [] 1, [(⟨"p"⟩, 9), (⟨"q"⟩, 10)]⟩] }
  let program ← checkClosedProgram a.output metadata a.binderSchemes
  if !program.body.runtimeSafety?.isSome then
    throw "test: supported mutual recursive spines lost their runtime theorem"
  let exact := match program.body.bounds with
    | .list lo hi (.prim .int) => lo.eval (fun _ => 0) == .ofNat 1 && hi.eval (fun _ => 0) == .ofNat 1
    | _ => false
  pure (exact && program.assembled.checked.exports.length == 2 &&
    exactlyOnce (logicalCorePaths a.output) (program.body.nodes.map (·.path)))

private def deferredRecursiveProgram (badCallback : Bool := false) (onlyDeferred : Bool := false) :
    Except String Bool := do
  let list := Ty.bl (.solid (count 7)) (.solid (count 7)) (.prim .int)
  let callback := Ty.arrow list list
  let σ : PolyTy := ⟨0, .arrow callback (if onlyDeferred then list else .arrow list list)⟩
  let deferred := Expr.lambda none (if badCallback then .ctor nilCtorName else .var 0)
  let rhs := if onlyDeferred then Expr.lambda none (.app (.var 1) deferred) else
    .lambda none (.lambda none (.app (.app (.var 2) deferred) (.var 0)))
  let bodyCallback := Expr.lambda (some (.bl (.solid (.lit 1)) (.solid (.lit 1)) (.prim .int))) (.var 0)
  let singleton := Expr.app (.app (.ctor consCtorName) (.primLit (.int 1))) (.ctor nilCtorName)
  let body := Expr.app (.var 0) bodyCallback
  let source := Expr.letRec [some σ] [rhs] (if onlyDeferred then body else .app body singleton)
  let ctors : CtorEnv := (elabDecls preludeDecls).getD []
  let a ← match inferFound ctors source with
    | some a => pure a | none => throw "test: deferred recursive callback HM inference failed"
  let metadata : Scope.Metadata := { telescopes := [⟨.letRec [] 0, [(⟨"n"⟩, 7)]⟩] }
  let program ← checkClosedProgram a.output metadata a.binderSchemes
  if !program.body.runtimeSafety?.isSome then
    throw "test: deferred recursive callback lost its runtime theorem"
  let exact := match program.body.bounds with
    | .list lo hi (.prim .int) => lo.eval (fun _ => 0) == .ofNat 1 && hi.eval (fun _ => 0) == .ofNat 1
    | _ => false
  pure (exact && exactlyOnce (logicalCorePaths a.output) (program.body.nodes.map (·.path)))

def main : IO Unit := do
  match actual with
  | .ok true => IO.println "PASS: every actual member universally specializes through one full group HM map with permuted slots and distinct count telescopes"
  | .error message => throw (IO.userError message)
  | .ok false => throw (IO.userError "uniform group transport captured caller counts inside full HM arguments")
  match changedCapture with
  | .ok true => IO.println "PASS: uniform group specialization cannot rewrite closed recursive template captures"
  | .error message => throw (IO.userError message)
  | .ok false => throw (IO.userError "closed recursive template capture guard failed")
  match bodyCalls with
  | .ok true => IO.println "PASS: all-member universal introduction checks actual Int/Char body calls and reports every original group/RHS/body occurrence exactly once"
  | .error message => throw (IO.userError message)
  | .ok false => throw (IO.userError "generalized body origins, type/count specialization or complete node coverage failed")
  match bodyCalls true with
  | .error message =>
      unless (message.splitOn "inclusion").length > 1 do
        throw (IO.userError s!"wrong generalized body rejection: {message}")
      IO.println "PASS: an HM-valid local annotation cannot widen an exact singleton body result to an exact length-two contract"
  | .ok _ => throw (IO.userError "generalized body ignored a false local bounds annotation")
  match bodyCalls (polyLocal := true) with
  | .ok true => IO.println "PASS: a closed generalized local let is introduced from its exact source RHS certificate"
  | .error message => throw (IO.userError message)
  | .ok false => throw (IO.userError "closed generalized local let lost body bounds or exact source-node coverage")
  match bodyCalls (polyLocal := true) (capturedLocal := true) with
  | .ok true => IO.println "PASS: a generalized local RHS may retain a fixed-monomorphic enclosing group use"
  | .error message => throw (IO.userError message)
  | .ok false => throw (IO.userError "captured generalized local lost body bounds or exact source-node coverage")
  match bodyCalls (forgedRoot := true) with
  | .error message =>
      unless (message.splitOn "original found payload").length > 1 do
        throw (IO.userError s!"wrong original root-shape rejection: {message}")
      IO.println "PASS: automatic closed-program assembly certifies the exact input and rejects a forged original root HM payload"
  | .ok _ => throw (IO.userError "automatic closed-program assembly ignored the original root HM payload")
  match bodyCalls (nested := true) with
  | .ok true => IO.println "PASS: actual nested singleton origins survive full exported HM insertion without widening inner List bounds"
  | .error message => throw (IO.userError message)
  | .ok false => throw (IO.userError "automatic generalized program lost nested List origins or source-node coverage")
  for kind in [0, 1, 2] do
    match bodyMatches kind (onlyNil := kind == 2) with
    | .ok true => IO.println s!"PASS: generalized body match kind {kind} checks every original arm, coverage and full origins with exact node reports"
    | .error message => throw (IO.userError message)
    | .ok false => throw (IO.userError "generalized body match lost branch refinements, result bounds or original node coverage")
  match bodyMatches 1 (onlyNil := true) with
  | .error message =>
      unless (message.splitOn "every admitted List is empty").length > 1 do
        throw (IO.userError s!"wrong generalized List coverage rejection: {message}")
      IO.println "PASS: generalized body Nil-only coverage cannot discard an admitted nonempty input"
  | .ok _ => throw (IO.userError "generalized body accepted uncovered nonempty List inputs")
  match bodyMatches 1 (onlyCons := true) with
  | .ok true => IO.println "PASS: generalized body Cons-only coverage discharges semantic nonemptiness from the actual singleton origin"
  | .error message => throw (IO.userError message)
  | .ok false => throw (IO.userError "generalized body Cons-only match lost predecessor tail bounds or coverage")
  match bodyMatches 0 (badDemand := true) with
  | .error message =>
      unless (message.splitOn "inclusion").length > 1 do
        throw (IO.userError s!"wrong generalized branch-demand rejection: {message}")
      IO.println "PASS: a common demanded match result cannot replace checking actual arm bounds"
  | .ok _ => throw (IO.userError "generalized body fabricated a demanded match result without arm inclusion")
  unless bodyPatternGuard do
    throw (IO.userError "a wildcard hid a malformed generalized body Cons pattern")
  IO.println "PASS: a wildcard cannot hide a malformed Cons field arity in a generalized body"
  unless bodyBoolCoverageGuard do
    throw (IO.userError "generalized body accepted incomplete Bool coverage")
  IO.println "PASS: generalized body Bool coverage checks both finite constructors independently of arithmetic validity"
  match bodyCallerPremises true with
  | .ok true => IO.println "PASS: established caller count premises permit actual origin-backed exported specialization"
  | .error message => throw (IO.userError message)
  | .ok false => throw (IO.userError "exported specialization changed a caller count origin")
  match bodyCallerPremises false with
  | .error message =>
      unless (message.splitOn "premises").length > 1 do
        throw (IO.userError s!"wrong caller-premise rejection: {message}")
      IO.println "PASS: exported calls cannot simply append unestablished callee count premises"
  | .ok _ => throw (IO.userError "generalized body assumed an unestablished callee premise")
  for kind in [0, 1] do
    match fullBodySpine kind with
    | .ok true => IO.println s!"PASS: full generalized body spine {kind} uses later HM/count origins and checks every original application frame"
    | .error message => throw (IO.userError message)
    | .ok false => throw (IO.userError "full generalized body spine lost result bounds or exact original-node coverage")
  for (result, part, name) in [
      (fullBodySpine 1 (badFirst := true), "inclusion", "later count origins cannot hide a false earlier compound-domain obligation"),
      (fullBodySpine 2, "inclusion", "one repeated full HM slot checks every argument's inner List bounds"),
      (fullBodySpine (partialCall := true), "later argument origin", "partial exported calls cannot guess unsupplied count coordinates"),
      (fullBodySpine (forgedPrefix := true), "original found payload", "every intermediate original found payload is independently checked")] do
    match result with
    | .error message =>
        unless (message.splitOn part).length > 1 do throw (IO.userError s!"wrong spine rejection ({name}): {message}")
        IO.println s!"PASS: {name}"
    | .ok _ => throw (IO.userError s!"accepted invalid generalized body spine: {name}")
  match fullBodyCapture with
  | .ok true => IO.println "PASS: one whole-spine count instantiation cannot capture caller counts inside either full HM argument"
  | .error message => throw (IO.userError message)
  | .ok false => throw (IO.userError "whole-spine specialization captured caller counts or dropped original nodes")
  for kind in [0, 1] do
    match fullBodySpine kind (recursive := true) with
    | .ok true => IO.println s!"PASS: actual recursive RHS spine {kind} keeps one fixed full HM vector and one count instance before generalized body uses"
    | .error message => throw (IO.userError message)
    | .ok false => throw (IO.userError "full recursive RHS/body program lost result bounds or exact original-node coverage")
  match fullMutualSpine with
  | .ok true => IO.println "PASS: mutually recursive full RHS spines retain a shared fixed HM vector across distinct count telescopes and independent Int/Char exit uses"
  | .error message => throw (IO.userError message)
  | .ok false => throw (IO.userError "full mutual recursive program lost source-member identity, exact bounds or original nodes")
  match deferredRecursiveProgram with
  | .ok true => IO.println "PASS: a recursive RHS checks its formerly unguided List lambda only after a later actual argument supplies the count origin"
  | .error message => throw (IO.userError message)
  | .ok false => throw (IO.userError "deferred recursive callback lost actual body proof, result bounds or original node coverage")
  for (result, part, name) in [
      (deferredRecursiveProgram (badCallback := true), "inclusion", "a false deferred callback still fails actual domain inclusion"),
      (deferredRecursiveProgram (onlyDeferred := true), "independent origin", "deferred callbacks cannot manufacture their own count origins")] do
    match result with
    | .error message =>
        unless (message.splitOn part).length > 1 do throw (IO.userError s!"wrong deferred RHS rejection ({name}): {message}")
        IO.println s!"PASS: {name}"
    | .ok _ => throw (IO.userError s!"unexpected deferred RHS acceptance: {name}")

#eval do
  let ctors : CtorEnv := (elabDecls preludeDecls).getD []
  unless (inferFound ctors runtimeLocalProgram).isSome do
    throw (IO.userError "universal local runtime fixture is not accepted by the actual HM layer")
  unless (inferFound ctors (.letIn (some ⟨1, .bvar 0⟩)
      (.primLit (.int 1)) (.primLit (.int 0)))).isNone do
    throw (IO.userError "a constant RHS satisfied an unjustified forall-a-a local annotation")
  match unsupportedIntermediate with
  | .ok true => IO.println "PASS: a supported root cannot hide an unsupported intermediate runtime domain"
  | .ok false => throw (IO.userError "unsupported intermediate type acquired a runtime witness")
  | .error message => throw (IO.userError s!"fragment metadata changed static acceptance: {message}")

#eval main

end FHM.Bounds.RecursiveHMUniformTests
