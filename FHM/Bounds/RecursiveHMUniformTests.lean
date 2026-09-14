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
    (forgedRoot : Bool := false) (nested : Bool := false) : Except String Bool := do
  let ctors : CtorEnv := (elabDecls preludeDecls).getD []
  let singleton (p : PrimLitExpr) : Expr :=
    .app (.app (.ctor consCtorName) (.primLit p)) (.ctor nilCtorName)
  let localAnn : Option PolyTy := if polyLocal then some ⟨1, listTy (.prim .int)⟩ else if badLocal then
    some ⟨0, .bl (.solid (.lit 2)) (.solid (.lit 2)) (.prim .int)⟩ else none
  let secondArg := if nested then
    .app (.app (.ctor consCtorName) (singleton (.char 'a'))) (.ctor nilCtorName)
    else singleton (.char 'a')
  let source := Expr.letRec
    [some (bodySignature 7), some (bodySignature 8), some ⟨0, .prim .int⟩]
    [.lambda none (.app (.var 2) (.var 0)), .lambda none (.app (.var 1) (.var 0)), .primLit (.int 0)]
    (.letIn localAnn (.app (.var 0) (singleton (.int 1)))
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
  | .error message =>
      unless (message.splitOn "polymorphic").length > 1 do
        throw (IO.userError s!"wrong generalized local-let guard: {message}")
      IO.println "PASS: an HM-valid generalized local let fails explicitly until its own universal introduction is available"
  | .ok _ => throw (IO.userError "generalized local let silently fell back to mono body checking")
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

#eval main

end FHM.Bounds.RecursiveHMUniformTests
