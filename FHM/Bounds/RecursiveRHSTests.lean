import FHM.Bounds.RecursiveRHS
import FHM.Bounds.Found

namespace FHM.Bounds.RecursiveRHSTests

open RecursiveContract RecursiveTyping CountSubstitution ScopedScheme SurfaceBridge.Provenance

private def ctors : CtorEnv := (elabDecls preludeDecls).getD []
private def span : Surface.Span.Span := ⟨1, 1, 1, 100⟩
private def leaf : Surface.Span.SpannedExpr := .leaf span
private def n : ValName := ⟨"n"⟩
private def xs : ValName := ⟨"xs"⟩
private def f : ValName := ⟨"f"⟩
private def exact (c : Surface.Count := .var n) : Surface.Ty := .bl (.solid c) (.solid c) (.prim .int)
private def listInt : Surface.Ty := .customTy listTyName [.prim .int]
private def cons (tail : Surface.Expr) : Surface.Expr :=
  .app (.app (.ctor consCtorName) (.primLit (.int 1))) tail
private def ignored (arg : Surface.Expr) (ann : Surface.Ty := listInt) (callee : ValName := f) : Surface.Expr :=
  .app (.lambda (.name ⟨"ignored"⟩) (some ann) (.var xs)) (.app (.var callee) arg)
private def binding (body : Surface.Expr) : Surface.Binding :=
  { name := f, natBinders := [n], ann := some ⟨[], .arrow (exact (.var n)) (exact (.var n))⟩
    rhs := .lambda (.name xs) (some (exact (.var n))) body }
private def consSpan : Surface.Span.SpannedExpr := .app span (.app span leaf leaf) leaf
private def ignoredSpan (arg : Surface.Span.SpannedExpr := leaf) : Surface.Span.SpannedExpr :=
  .app span (.lambda span leaf) (.app span leaf arg)

private def artifact (b : Surface.Binding) (bodySpan : Surface.Span.SpannedExpr) : Except String TypedLowered := do
  let lower ← match lowerWithProvenance ctors (.letRecIn [b] (.primLit (.int 1)))
      (.letRecIn span [.lambda span bodySpan] leaf) with
    | some l => pure l | none => throw "test: recursive RHS lowering failed"
  match inferWithProvenance ctors lower with
  | some a => pure a | none => throw "test: recursive RHS HM inference failed"

private def prepare (a : TypedLowered) (member : Nat := 0) : Except String Declared := do
  let rhs ← ScopedDeclaration.locate a.inference.output (.letRec [] member)
  let ann ← match rhs.annotation with | some a => pure a | none => throw "test: missing contract"
  let hm ← match Typed.rootHM? rhs.expr with | some h => pure h | none => throw "test: missing found type"
  let q ← ScopedDeclaration.telescope a.lowering.counts (.letRec [] member)
  RecursiveContract.decode ann hm q []

private def run (b : Surface.Binding) (bodySpan : Surface.Span.SpannedExpr) : Except String String := do
  let a ← artifact b bodySpan
  let c ← prepare a
  let checked ← RecursiveRHS.check a.inference.output a.inference.binderSchemes a.lowering.counts
    (.letRec [] 0) c [.recursive c]
  let inst ← c.counts.instantiate [.lit 3] []
  let _ := RecursiveRHS.use checked.certificate inst
  unless exactlyOnce (logicalCorePaths checked.rhs.expr) (checked.typed.nodes.map fun n =>
      n.path.drop checked.rhs.path.length) do throw "test: RHS report lost a logical Core path"
  pure (bounds (c.counts.quantified.zip [.lit 3]) checked.certificate.actual).pretty

private def succeeds (r : Except String α) : Bool := match r with | .ok _ => true | _ => false
private def fails (r : Except String α) (needle : String) : Bool :=
  match r with | .error m => (m.splitOn needle).length > 1 | _ => false
private def identity : Surface.Binding := binding (ignored (.var xs))

private def metadataRejected (modify : Scope.Metadata → Scope.Metadata) : Bool :=
  match artifact identity (ignoredSpan leaf) with
  | .error _ => false
  | .ok a => match prepare a with
    | .error _ => false
    | .ok c => match RecursiveRHS.check a.inference.output a.inference.binderSchemes (modify a.lowering.counts)
        (.letRec [] 0) c [.recursive c] with
      | .error m => (m.splitOn "telescope disagrees").length > 1
      | _ => false

private def environmentRejected : Bool :=
  match artifact identity (ignoredSpan leaf) with
  | .error _ => false
  | .ok a => match prepare a with
    | .error _ => false
    | .ok c => match c.counts.quantified with
      | [id] =>
          let k : Count := .var ⟨.rigid, id⟩
          let bad := Binding.mono (.list k k (.prim .int))
          match RecursiveRHS.check a.inference.output a.inference.binderSchemes a.lowering.counts
              (.letRec [] 0) c [.recursive c, bad] with
          | .error m => (m.splitOn "capture or quantified-count freshness").length > 1
          | _ => false
      | _ => false

private def mutualCertificates : Except String Bool := do
  let g : ValName := ⟨"g"⟩
  let first := binding (ignored (.var xs) listInt g)
  let second := {binding (ignored (cons (.var xs))) with name := g}
  let lower ← match lowerWithProvenance ctors (.letRecIn [first, second] (.primLit (.int 1)))
      (.letRecIn span [.lambda span (ignoredSpan leaf), .lambda span (ignoredSpan consSpan)] leaf) with
    | some l => pure l | none => throw "test: mutual RHS lowering failed"
  let a ← match inferWithProvenance ctors lower with
    | some a => pure a | none => throw "test: mutual RHS inference failed"
  let cs ← (List.range 2).mapM (fun member => prepare a member)
  unless independentBool cs do throw "test: mutual count interfaces not independent"
  let env := cs.map Binding.recursive
  let results ← cs.mapIdxM fun member c => do
    let checked ← RecursiveRHS.check a.inference.output a.inference.binderSchemes a.lowering.counts
      (.letRec [] member) c env
    let inst ← c.counts.instantiate [.lit 3] []
    let _ := RecursiveRHS.use checked.certificate inst
    pure ((bounds (c.counts.quantified.zip [.lit 3]) checked.certificate.actual).pretty == "BL 3 3 Int → BL 3 3 Int")
  pure (results.all id)

example {c env rhs ann args caller} (cert : RecursiveRHS.Certified c env rhs ann)
    (inst : Instance c.counts args caller) :
    Derives (c.counts.quantified ++ c.counts.captures) (c.counts.quantified.zip args)
      inst.premises env rhs (bounds (c.counts.quantified.zip args) cert.actual) ∧
      SemanticSub inst.premises (bounds (c.counts.quantified.zip args) cert.actual) inst.bounds :=
  ⟨(RecursiveRHS.use cert inst).typing, (RecursiveRHS.use cert inst).inclusion⟩

private def cases : List (String × Bool) := [
  ("real recursive RHS generates universal count certificate", match run identity (ignoredSpan leaf) with
    | .ok s => s == "BL 3 3 Int → BL 3 3 Int" | _ => false),
  ("count-polymorphic recursive call may use n plus one", succeeds
    (run (binding (ignored (cons (.var xs)))) (ignoredSpan consSpan))),
  ("recursive call result must meet containing lambda parameter annotation", fails
    (run (binding (ignored (cons (.var xs)) (exact (.var n)))) (ignoredSpan consSpan)) "interval inclusion"),
  ("recursive increment cannot pretend it preserves declared length", fails
    (run (binding (cons (.app (.var f) (.var xs))))
      (.app span (.app span leaf leaf) (.app span leaf leaf))) "interval inclusion"),
  ("direct self-call with more-general HM result explicitly deferred", fails
    (run (binding (.app (.var f) (cons (.var xs)))) (.app span leaf consSpan)) "needs specialization"),
  ("nested carried binding contract remains an obligation", fails
    (run (binding (.letIn ⟨"alias"⟩ [] [] (some ⟨[], exact (.add (.var n) (.lit 1))⟩)
      (.var xs) (ignored (.var xs)))) (.letIn span leaf (ignoredSpan leaf))) "interval inclusion"),
  ("recursive RHS missing count telescope is not guessed", metadataRejected (fun m => {m with telescopes := []})),
  ("recursive RHS wrong count telescope is not reconciled by names", metadataRejected (fun m =>
    {m with telescopes := m.telescopes.map fun t => {t with binders := [(n, 777)]}})),
  ("recursive RHS rejects source-quantified counts in outer captures", environmentRejected),
  ("actual mutual RHSs generate universal certificates with different recursive counts", match mutualCertificates with
    | .ok true => true | _ => false)]

def main : IO Unit := do
  for (name, ok) in cases do
    IO.println s!"{if ok then "PASS" else "FAIL"}: {name}"
    unless ok do throw (IO.userError s!"recursive RHS regression: {name}")

#eval main

end FHM.Bounds.RecursiveRHSTests
