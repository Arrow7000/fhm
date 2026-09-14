import FHM.Bounds.RecursiveGroup
import FHM.Bounds.Found

namespace FHM.Bounds.RecursiveGroupTests

open RecursiveTyping CountSubstitution SurfaceBridge.Provenance

private def ctors : CtorEnv := (elabDecls preludeDecls).getD []
private def span : Surface.Span.Span := ⟨1, 1, 1, 100⟩
private def leaf : Surface.Span.SpannedExpr := .leaf span
private def n : ValName := ⟨"n"⟩
private def xs : ValName := ⟨"xs"⟩
private def f : ValName := ⟨"f"⟩
private def g : ValName := ⟨"g"⟩
private def exact (c : Surface.Count := .var n) : Surface.Ty := .bl (.solid c) (.solid c) (.prim .int)
private def listInt : Surface.Ty := .customTy listTyName [.prim .int]
private def cons (tail : Surface.Expr) : Surface.Expr :=
  .app (.app (.ctor consCtorName) (.primLit (.int 1))) tail
private def consSpan (tail : Surface.Span.SpannedExpr := leaf) : Surface.Span.SpannedExpr :=
  .app span (.app span leaf leaf) tail
private def ignored (callee : ValName := f) (arg : Surface.Expr := .var xs) : Surface.Expr :=
  .app (.lambda (.name ⟨"ignored"⟩) (some listInt) (.var xs)) (.app (.var callee) arg)
private def ignoredSpan (arg : Surface.Span.SpannedExpr := leaf) : Surface.Span.SpannedExpr :=
  .app span (.lambda span leaf) (.app span leaf arg)
private def binding (name : ValName := f) (body : Surface.Expr := ignored) : Surface.Binding :=
  { name, natBinders := [n], ann := some ⟨[], .arrow (exact (.var n)) (exact (.var n))⟩
    rhs := .lambda (.name xs) (some (exact (.var n))) body }
private def self : Surface.Binding := binding
private def selfSpan : Surface.Span.SpannedExpr := .lambda span (ignoredSpan leaf)
private def call (callee : ValName := f) (arg : Surface.Expr := .ctor nilCtorName) : Surface.Expr :=
  .app (.var callee) arg
private def callSpan (arg : Surface.Span.SpannedExpr := leaf) : Surface.Span.SpannedExpr :=
  .app span leaf arg

private def artifact (bs : List Surface.Binding) (spans : List Surface.Span.SpannedExpr)
    (body : Surface.Expr := call) (bodySpan : Surface.Span.SpannedExpr := callSpan) :
    Except String TypedLowered := do
  let lower ← match lowerWithProvenance ctors (.letRecIn bs body) (.letRecIn span spans bodySpan) with
    | some l => pure l | none => throw "test: group lowering failed"
  match inferWithProvenance ctors lower with
  | some a => pure a | none => throw "test: group HM inference failed"

private def check (a : TypedLowered) : Except String (RecursiveGroup.Result [] [] [] [] [] a.inference.output) :=
  RecursiveGroup.check [] [] [] [] [] [] a.inference.output a.inference.binderSchemes a.lowering.counts

private def run (bs : List Surface.Binding := [self]) (spans : List Surface.Span.SpannedExpr := [selfSpan])
    (body : Surface.Expr := call) (bodySpan : Surface.Span.SpannedExpr := callSpan) : Except String String := do
  let a ← artifact bs spans body bodySpan
  let result ← check a
  unless exactlyOnce (logicalCorePaths a.inference.output) (result.nodes.map (·.path)) do
    throw "test: group report lost or duplicated logical Core nodes"
  pure result.bounds.pretty

private def fails (r : Except String α) (needle : String) : Bool :=
  match r with | .error m => (m.splitOn needle).length > 1 | _ => false
private def succeeds (r : Except String α) : Bool := match r with | .ok _ => true | _ => false
private def returns (r : Except String String) (expected : String) : Bool :=
  match r with | .ok s => s == expected | _ => false

private def changedMetadata (modify : Scope.Metadata → Scope.Metadata) : Except String Unit := do
  let a ← artifact [binding f (ignored g), binding g (ignored f)] [selfSpan, selfSpan]
  let _ ← RecursiveGroup.check [] [] [] [] [] [] a.inference.output a.inference.binderSchemes
    (modify a.lowering.counts)
  pure ()

private def overlap (m : Scope.Metadata) : Scope.Metadata :=
  match m.telescopes with
  | first :: second :: tail =>
      {m with telescopes := {first with binders := first.binders ++ second.binders} :: second :: tail}
  | _ => m

private def changedExpr (modify : Expr → Expr) : Except String Unit := do
  let a ← artifact [self] [selfSpan]
  let _ ← RecursiveGroup.check [] [] [] [] [] [] (modify a.inference.output)
    a.inference.binderSchemes a.lowering.counts
  pure ()

private def badCapture : Except String Unit := do
  let a ← artifact [self] [selfSpan]
  let k : Count := .var ⟨.rigid, 777⟩
  let _ ← RecursiveGroup.check [] [] [] [] [.mono (.list k k (.prim .int))] []
    a.inference.output a.inference.binderSchemes a.lowering.counts
  pure ()

private def nonRoot : Except String Bool := do
  let surface := Surface.Expr.lambda (.name ⟨"outer"⟩) (some (.prim .int)) (.letRecIn [self] call)
  let spanned := Surface.Span.SpannedExpr.lambda span (.letRecIn span [selfSpan] callSpan)
  let lower ← match lowerWithProvenance ctors surface spanned with
    | some l => pure l | none => throw "test: nested-site lowering failed"
  let a ← match inferWithProvenance ctors lower with
    | some a => pure a | none => throw "test: nested-site HM inference failed"
  let e ← match a.inference.output.atCorePath [.lambdaBody] with
    | some e => pure e | none => throw "test: nested group not found"
  let result ← RecursiveGroup.check [] [] [] [] [.mono (.prim .int)] [.lambdaBody] e
    a.inference.binderSchemes a.lowering.counts
  pure (result.bounds.pretty == "BL 0 0 Int" && exactlyOnce (logicalCorePaths e)
    (result.nodes.map fun node => node.path.drop 1))

example {ids rows Δ env anns rhss body} (cert : RecursiveGroup.Certified ids rows Δ env anns rhss body) :
    Derives ids rows Δ env (.letRec anns (rhss.map Expr.stripFound) body.stripFound) cert.result := cert.typing

private def cases : List (String × Bool) := [
  ("consecutive empty group checks through the same group introduction", succeeds
    (changedExpr (fun
      | .found hm (.letRec anns rhss body) =>
          .found hm (.letRec anns rhss (.found hm (.letRec [] [] body)))
      | e => e))),
  ("forged inner group root is checked before outer acceptance", fails
    (changedExpr (fun
      | .found hm (.letRec anns rhss body) =>
          .found hm (.letRec anns rhss (.found (.prim .char) (.letRec [] [] body)))
      | e => e)) "body disagrees"),
  ("missing inner found group payload is not reconstructed", fails
    (changedExpr (fun
      | .found hm (.letRec anns rhss body) =>
          .found hm (.letRec anns rhss (.letRec [] [] body))
      | e => e)) "not a found recursive group"),
  ("whole self-recursive group checks and body gets exact Nil result", returns (run) "BL 0 0 Int"),
  ("whole mutual group checks all members before accepting body", returns
    (run [binding f (ignored g), binding g (ignored f (cons (.var xs)))]
      [selfSpan, .lambda span (ignoredSpan (consSpan leaf))]) "BL 0 0 Int"),
  ("recursive count use in group body follows actual Cons origin", returns
    (run [self] [selfSpan] (call f (cons (.ctor nilCtorName))) (callSpan (consSpan leaf))) "BL 1 1 Int"),
  ("one incorrect mutual RHS rejects entire group", fails
    (run [binding f (ignored g), binding g (cons (call f (.var xs)))]
      [selfSpan, .lambda span (consSpan (callSpan leaf))]) "interval inclusion"),
  ("valid recursive RHSs do not excuse an invalid group body", fails
    (run [self] [selfSpan]
      (.app (.lambda (.name ⟨"demand"⟩) (some (exact (.lit 1))) (.primLit (.int 1))) call)
      (.app span (.lambda span leaf) callSpan)) "interval inclusion"),
  ("count-polymorphic standalone recursive value explicitly needs origin", fails
    (run [self] [selfSpan] (.var f) leaf) "needs an argument origin"),
  ("missing recursive signature does not export assumed contract", fails
    (run [{self with ann := none}] [selfSpan]) "requires declared bounds contracts"),
  ("overlapping member telescopes reject whole group", fails (changedMetadata overlap) "telescopes overlap"),
  ("duplicate exact-site telescope is rejected", fails (changedMetadata (fun m =>
    {m with telescopes := m.telescopes ++ m.telescopes.take 1})) "duplicate count telescope"),
  ("missing source telescope is not guessed", fails (changedMetadata (fun m => {m with telescopes := []})) "scope"),
  ("outer environment cannot escape declared count captures", fails badCapture "environment escapes"),
  ("forged group root type rejects body", fails (changedExpr (fun
    | .found _ e => .found (.prim .char) e | e => e)) "body disagrees"),
  ("missing member found payload rejects group", fails (changedExpr (fun
    | .found hm (.letRec anns (rhs :: rhss) body) => .found hm (.letRec anns (rhs.stripFound :: rhss) body)
    | e => e)) "member lacks found"),
  ("annotation/RHS arity mismatch rejects group", fails (changedExpr (fun
    | .found hm (.letRec anns rhss body) => .found hm (.letRec (none :: anns) rhss body)
    | e => e)) "arity mismatch"),
  ("missing parallel annotation rejects group before certification", fails (changedExpr (fun
    | .found hm (.letRec _ rhss body) => .found hm (.letRec [] rhss body)
    | e => e)) "arity mismatch"),
  ("group checker requires found group root", fails (changedExpr Expr.stripFound) "not a found recursive group"),
  ("non-root group uses exact rebased Core sites and reports", match nonRoot with | .ok true => true | _ => false),
  ("empty group introduces no recursive assumptions", succeeds (RecursiveGroup.check [] [] [] [] [] []
    (.found (.prim .int) (.letRec [] [] (.found (.prim .int) (.primLit (.int 1))))) [] {}))]

def main : IO Unit := do
  for (name, ok) in cases do
    IO.println s!"{if ok then "PASS" else "FAIL"}: {name}"
    unless ok do throw (IO.userError s!"recursive group regression: {name}")

#eval main

end FHM.Bounds.RecursiveGroupTests
