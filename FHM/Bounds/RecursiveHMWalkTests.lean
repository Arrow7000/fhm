import FHM.Bounds.RecursiveHMWalk
import FHM.Bounds.Found
import FHM.Bounds.RecursiveHMReconciled

namespace FHM.Bounds.RecursiveHMWalkTests

open RecursiveHMJudgement SurfaceBridge.Provenance

private def n : Count := .var ⟨.rigid, 7⟩
private def callerType : BoundsTy := .list n n (.prim .int)
private def types (i : Nat) : BoundsTy := if i = 90 then callerType else .fvar i
private def identityHM : Ty := .arrow (.fvar 90) (.fvar 90)
private def identity (ann : Option Ty := none) : Expr :=
  .found identityHM (.lambda ann (.found (.fvar 90) (.var 0)))
private def expected : BoundsTy := .arrow callerType callerType

private def run (e : Expr := identity) (env : List Binding := []) (schemes : BinderSchemeMap := [])
    (hint : Option BoundsTy := some expected) (caller : List Nat := [7]) : Except String String := do
  let r ← RecursiveHMWalk.walk types [7] [(7, .lit 3)] caller [] env [] e schemes hint
  unless exactlyOnce (logicalCorePaths e) (r.nodes.map (·.path)) do
    throw "test: interpreted walker lost or duplicated logical Core nodes"
  pure r.bounds.pretty

private def localLet (ann : Option PolyTy := none) : Expr :=
  .found identityHM (.lambda none
    (.found (.fvar 90) (.letIn ann (.found (.fvar 90) (.var 0)) (.found (.fvar 90) (.var 0)))))
private def letFacts (σ : PolyTy := ⟨0, .fvar 90⟩) : BinderSchemeMap := [(.letIn [.lambdaBody], σ)]

private def cons (wrongPartial : Bool := false) (wrongCtor : Bool := false) : Expr :=
  let l := listTy (.prim .int)
  let partialHM := if wrongPartial then Ty.prim .char else .arrow l l
  let ctor := if wrongCtor then Ty.prim .char else .arrow (.prim .int) (.arrow l l)
  .found l (.app (.found partialHM (.app (.found ctor (.ctor consCtorName))
    (.found (.prim .int) (.primLit (.int 1))))) (.found l (.ctor nilCtorName)))

private def recursiveSignature : PolyTy :=
  ⟨1, .arrow (.bl (.solid n) (.solid n) (.bvar 0)) (.bl (.solid n) (.solid n) (.bvar 0))⟩
private def recursiveHM : Ty := .arrow (listTy (.fvar 90)) (listTy (.fvar 90))
private def loop (member : Nat := 1) (wrongCall : Bool := false) : Expr :=
  let callee := if wrongCall then Ty.arrow (listTy (.prim .char)) (listTy (.prim .char)) else recursiveHM
  .found recursiveHM (.lambda (some (.bl (.solid n) (.solid n) (.fvar 90)))
    (.found (listTy (.fvar 90)) (.app (.found callee (.var member))
      (.found (listTy (.fvar 90)) (.var 0)))))

private def recursive (isMutual : Bool := false) (wrongCall : Bool := false) : Except String String := do
  let s ← HMCountScheme.decode recursiveSignature [7] []
  let found := HMFoundView.ty types recursiveHM
  let fixed ← RecursiveHMContract.fix s found [callerType]
  let c : Contract := ⟨s, found, fixed⟩
  let env := if isMutual then [.recursive c, .recursive c] else [.recursive c]
  let hint := BoundsTy.arrow (.list n n callerType) (.list n n callerType)
  run (loop (if isMutual then 2 else 1) wrongCall) env [] (some hint)

private def monoApplication : Expr := .found (.fvar 90)
  (.app (.found identityHM (.var 0)) (.found (.fvar 90) (.var 1)))

private def realArtifact (annotatedBinding : Bool := false) (withMatch : Bool := false) : Except String Bool := do
  let ctors : CtorEnv := (elabDecls preludeDecls).getD []
  let contract := if withMatch then
      PolyTy.mk 1 (.arrow (.bl (.solid n) (.solid n) (.bvar 0))
        (.bl (.solid (.lit 0)) (.solid n) (.bvar 0)))
    else recursiveSignature
  let rhs : Expr := if withMatch then .lambda none (.match_ (.var 0)
      [(.named consCtorName 2, .var 1), (.named nilCtorName 0, .ctor nilCtorName)])
    else .lambda none (.var 0)
  let source : Expr := .letIn (if annotatedBinding then some contract else none) rhs (.primLit (.int 0))
  let artifact ← match inferFound ctors source with
    | some artifact => pure artifact | none => throw "test: real HM artifact inference failed"
  let node ← HMFoundView.locate artifact.output [.letRhs]
  let skeleton ← Typed.shapeTop node.original.eraseBounds
  let interface ← HMCountScheme.decodeAnnotated contract [7] []
  let fresh := node.original.freeVars.foldl max 0 + 1
  let checked ← HMReconciliation.check node artifact.binderSchemes (.letIn [])
    interface.scheme skeleton [fresh] []
  let located ← RecursiveHMReconciled.checkLocated checked []
  let cert := RecursiveHMReconciled.fromAnnotated interface checked located.rhs
    (by intro c hc; cases hc) (by intro s hs; cases hs)
    (by intro c hc; cases hc) (by intro s hs; cases hs)
  let scopedInstance ← interface.scheme.counts.instantiate [.lit 2] []
  let used := RecursiveHMSigned.atInterpretedNode node cert scopedInstance [.prim .int]
    (by cases withMatch <;> simp [contract, recursiveSignature])
    (by
      intro a ha
      have he : a = BoundsTy.prim .int := by simpa using ha
      subst a
      simp only [Synth.BoundsTy.toTy]
      exact .prim)
    (by decide)
  let expectedResult := if withMatch then "BL 2 2 Int → BL 0 2 Int" else "BL 2 2 Int → BL 2 2 Int"
  pure (used.typed.actual.pretty == expectedResult &&
    exactlyOnce (logicalCorePaths (.found node.original node.inner))
      (located.nodes.map fun node => node.path.drop 1))

private def prematurePartial : Except String String := do
  let m : Count := .var ⟨.rigid, 8⟩
  let list : Ty := .bl (.solid m) (.solid m) (.prim .int)
  let annotation : PolyTy := ⟨0, .arrow (.prim .int) (.arrow list list)⟩
  let s ← HMCountScheme.decode annotation [8] []
  let hm := annotation.body.eraseBounds
  let fixed ← RecursiveHMContract.fix s hm []
  let c : Contract := ⟨s, hm, fixed⟩
  let resultHM := Ty.arrow (listTy (.prim .int)) (listTy (.prim .int))
  run (.found resultHM (.app (.found hm (.var 0)) (.found (.prim .int) (.primLit (.int 1)))))
    [.recursive c] [] none []

private def boolMatch (branches : List (MatchPattern × Expr)) : Expr :=
  .found (listTy (.prim .int)) (.match_
    (.found (.customTy boolTyName []) (.ctor BoolBranches.trueCtorName)) branches)

private def fullFixedSpine (wrongHead : Bool := false) (wrongPrefix : Bool := false) :
    Except String String := do
  let m : Count := .var ⟨.rigid, 8⟩
  let list (c : Count) : Ty := .bl (.solid c) (.solid c) (.prim .int)
  let annotation : PolyTy := ⟨0, .arrow (list n) (.arrow (list m) (list m))⟩
  let s ← HMCountScheme.decode annotation [7, 8] []
  let hm := annotation.body.eraseBounds
  let fixed ← RecursiveHMContract.fix s hm []
  let c : Contract := ⟨s, hm, fixed⟩
  let l := listTy (.prim .int)
  let headHM := if wrongHead then .arrow (listTy (.prim .char)) (.arrow l l) else hm
  let firstHM := if wrongPrefix then Ty.prim .int else .arrow l l
  let e := Expr.found l (.app (.found firstHM (.app (.found headHM (.var 0)) (.found l (.var 1))))
    (.found l (.var 2)))
  let r ← RecursiveHMWalk.walk BoundsTy.fvar [] [] [] []
    [.recursive c, .mono (.list (.lit 1) (.lit 1) (.prim .int)),
      .mono (.list (.lit 2) (.lit 2) (.prim .int))] [] e []
  unless exactlyOnce (logicalCorePaths e) (r.nodes.map (·.path)) do
    throw "test: fixed recursive full spine lost original node coverage"
  pure r.bounds.pretty

private def boolArms : List (MatchPattern × Expr) := [
  (.named BoolBranches.trueCtorName 0, .found (listTy (.prim .int)) (.ctor nilCtorName)),
  (.named BoolBranches.falseCtorName 0, cons)]
private def boolUnion : Except String Bool := do
  let e := boolMatch boolArms
  let r ← RecursiveHMWalk.walk types [] [] [] [] [] [] e []
  pure (match r.bounds with
    | .list lo hi (.prim .int) =>
        match lo.eval (fun _ => 0), hi.eval (fun _ => 0) with
        | .ofNat a, .ofNat b => a == 0 && b == 1 && exactlyOnce
            (logicalCorePaths e) (r.nodes.map (·.path))
        | _, _ => false
    | _ => false)

private def tailArms : List (MatchPattern × Expr) := [
  (.named consCtorName 2, .found (listTy (.fvar 90)) (.var 1)),
  (.named nilCtorName 0, .found (listTy (.fvar 90)) (.ctor nilCtorName))]
private def tailMatch (branches : List (MatchPattern × Expr) := tailArms) : Expr :=
  .found recursiveHM (.lambda none (.found (listTy (.fvar 90))
    (.match_ (.found (listTy (.fvar 90)) (.var 0)) branches)))
private def tailExpected : BoundsTy :=
  .arrow (.list n n callerType) (.list (.lit 0) n callerType)
private def trueResult (r : Except String Bool) : Bool := match r with | .ok ok => ok | _ => false

private def succeeds (r : Except String α) : Bool := match r with | .ok _ => true | _ => false
private def returns (r : Except String String) (s : String) : Bool := match r with | .ok a => a == s | _ => false
private def fails (r : Except String α) (needle : String) : Bool :=
  match r with | .error m => (m.splitOn needle).length > 1 | _ => false

private def cases : List (String × Bool) := [
  ("full fixed recursive spine gathers later count origins and preserves every source frame",
    match fullFixedSpine with | .ok text => text == "BL 2 2 Int" | _ => false),
  ("full recursive head cannot change the common fixed HM instance",
    fails (fullFixedSpine (wrongHead := true)) "HM-interpreted"),
  ("full recursive prefix cannot hide a forged original HM payload",
    fails (fullFixedSpine (wrongPrefix := true)) "HM-interpreted"),
  ("interpreted lambda constructs its actual RHS proof from the original found tree", returns run expected.pretty),
  ("named carried parameter annotation uses its full HM replacement", returns (run (identity (some (.fvar 90)))) expected.pretty),
  ("interpreted lambda still checks every body payload", fails
    (run (.found identityHM (.lambda none (.found (.prim .char) (.var 0))))) "found payload"),
  ("actual interpreted caller counts cannot escape", fails (run identity [] [] (some expected) []) "outside caller scope"),
  ("unguided List lambda is explicitly unsupported rather than inventing counts", fails
    (run identity [] [] none) "non-scalar parameter"),
  ("monomorphic local let retains exact caller-origin intervals", returns (run localLet [] letFacts) expected.pretty),
  ("carried mono local annotation is checked under the same interpretation", returns
    (run (localLet (some ⟨0, .fvar 90⟩)) [] letFacts) expected.pretty),
  ("annotated mono local needs its source obligation rather than an invented inferred fact", returns
    (run (localLet (some ⟨0, .fvar 90⟩))) expected.pretty),
  ("mono local fact must agree with the original payload before interpretation", fails
    (run localLet [] (letFacts ⟨0, .fvar 91⟩)) "original found payload"),
  ("polymorphic annotated local remains explicitly guarded", fails
    (run (localLet (some ⟨1, .bvar 0⟩))) "polymorphic HM internal binding"),
  ("local let cannot omit its machine binder fact", fails (run localLet) "missing inferred local"),
  ("local let cannot use duplicate machine binder facts", fails (run localLet [] (letFacts ++ letFacts)) "duplicate inferred local"),
  ("inferred generalized local let cannot masquerade as monomorphic", fails
    (run localLet [] (letFacts ⟨1, .bvar 0⟩)) "generalized local HM let"),
  ("Cons derives exact length and reports every original Core node", returns (run cons [] [] none []) "BL 1 1 Int"),
  ("partial Cons payload is checked, not silently skipped", fails (run (cons true) [] [] none []) "partial Cons"),
  ("Cons constructor payload is checked, not silently skipped", fails (run (cons false true) [] [] none []) "Cons found"),
  ("monomorphic function application retains actual argument bounds", returns
    (run monoApplication [.mono expected, .mono callerType] [] none) callerType.pretty),
  ("self recursion checks count-only use of the fixed full HM vector", succeeds recursive),
  ("mutual recursion uses the same fixed full HM vector in the common environment", succeeds (recursive true)),
  ("recursive call cannot change its group's fixed HM instantiation", fails (recursive false true) "found payload"),
  ("nested recursive groups still reject in universally checked RHSs", fails
    (run (.found identityHM (.letRec [] [] identity))) "nested groups"),
  ("missing found wrapper cannot invent a node type", fails (run (.var 0)) "missing found")]
  ++ [
  ("Bool constructor uses the interpreted finite-constructor rule", succeeds
    (run (.found (.customTy boolTyName []) (.ctor BoolBranches.trueCtorName)) [] [] none [])),
  ("real inferred artifact supplies machine facts, original RHS typing and universal exact-node use", match realArtifact with
    | .ok ok => ok | .error _ => false),
  ("annotated forall artifact cannot bypass the lexical bound-slot reader boundary", fails
    (realArtifact true) "missing inferred binder scheme"),
  ("partial recursive call cannot fix a later-domain count to a guessed zero", fails
    prematurePartial "later argument origin"),
  ("Bool arms synthesize their variance-correct interval union with every node reported", trueResult boolUnion),
  ("Bool match rejects missing constructor coverage", fails
    (run (boolMatch (boolArms.take 1)) [] [] none []) "False coverage"),
  ("Bool wildcard coverage works under interpreted checking", succeeds
    (run (boolMatch [(.wildcard, cons)]) [] [] none [])),
  ("Bool constructor-pattern arity cannot hide behind wildcard coverage", fails
    (run (boolMatch [(.named BoolBranches.trueCtorName 1, cons), (.wildcard, cons)]) [] [] none []) "pattern or constructor arity"),
  ("a common match demand checks all actual branches rather than asserting it", fails
    (run (boolMatch boolArms) [] [] (some (.list (.lit 0) (.lit 0) (.prim .int))) []) "interval inclusion"),
  ("List Cons/Nil arms retain interpreted element origins and path-refined tail bounds", returns
    (run tailMatch [] [] (some tailExpected)) tailExpected.pretty),
  ("List coverage still includes the empty case at an unknown caller length", !succeeds
    (run (tailMatch (tailArms.take 1)) [] [] (some tailExpected))),
  ("List constructor arity is checked before branch-environment extension", fails
    (run (tailMatch [(.named consCtorName 1, .found (listTy (.fvar 90)) (.var 0)),
      (.wildcard, .found (listTy (.fvar 90)) (.var 0))]) [] [] (some tailExpected)) "pattern or constructor arity"),
  ("real List-match artifact constructs and specializes a universal RHS certificate", trueResult
    (realArtifact false true))]

def main : IO Unit := do
  for (name, ok) in cases do
    IO.println s!"{if ok then "PASS" else "FAIL"}: {name}"
    unless ok do throw (IO.userError s!"interpreted walker regression failed: {name}")

#eval main

end FHM.Bounds.RecursiveHMWalkTests
