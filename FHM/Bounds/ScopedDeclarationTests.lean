import FHM.Bounds.ScopedDeclaration
import FHM.Bounds.Found

namespace FHM.Bounds.ScopedDeclarationTests

open CountSubstitution SurfaceBridge.Provenance

private def span : Surface.Span.Span := ⟨1, 1, 1, 80⟩
private def leaf : Surface.Span.SpannedExpr := .leaf span
private def n : ValName := ⟨"n"⟩
private def xs : ValName := ⟨"xs"⟩
private def exact (c : Surface.Count) : Surface.Ty := .bl (.solid c) (.solid c) (.prim .int)
private def ctors : CtorEnv := (elabDecls preludeDecls).getD []
private def binding (output : Surface.Count) (body : Surface.Expr) : Surface.Binding :=
  { name := ⟨"f"⟩, natBinders := [n]
    ann := some ⟨[], .arrow (exact (.var n)) (exact output)⟩
    rhs := .lambda (.name xs) (some (exact (.var n))) body }

private def artifact (b : Surface.Binding) (bodySpan : Surface.Span.SpannedExpr := leaf) :
    Option TypedLowered := do
  let lowered ← lowerWithProvenance ctors (.letRecIn [b] (.primLit (.int 1)))
    (.letRecIn span [.lambda span bodySpan] leaf)
  inferWithProvenance ctors lowered

private def identity : Option TypedLowered := artifact (binding (.var n) (.var xs))
private def consArtifact : Option TypedLowered :=
  artifact (binding (.add (.var n) (.lit 1))
    (.app (.app (.ctor consCtorName) (.primLit (.int 1))) (.var xs)))
    (.app span (.app span leaf leaf) leaf)

private def accepts (a : Option TypedLowered) (expected : String) (count : Nat := 3) : Bool :=
  match a with
  | none => false
  | some a => match ScopedDeclaration.checkRHS a.inference.output a.inference.binderSchemes
      a.lowering.counts (.letRec [] 0) with
    | .error _ => false
    | .ok checked =>
        let hm := checked.typed.hm
        match CountContract.check checked.certificate [] hm [.lit count] [] [] with
        | .error _ => false
        | .ok used => used.bounds.pretty == expected &&
            exactlyOnce (logicalCorePaths checked.rhs.expr) (checked.typed.nodes.map fun n =>
              n.path.drop checked.rhs.path.length)

private def rejects (a : Option TypedLowered) (needle : String) : Bool :=
  match a with
  | none => false
  | some a => match ScopedDeclaration.checkRHS a.inference.output a.inference.binderSchemes
      a.lowering.counts (.letRec [] 0) with
    | .error message => (message.splitOn needle).length > 1
    | .ok _ => false

private def metadataRejected (change : Scope.Metadata → Scope.Metadata) (needle : String) : Bool :=
  match identity with
  | none => false
  | some a => match ScopedDeclaration.checkRHS a.inference.output a.inference.binderSchemes
      (change a.lowering.counts) (.letRec [] 0) with
    | .error message => (message.splitOn needle).length > 1
    | .ok _ => false

private def factsRejected (duplicate : Bool) : Bool :=
  match artifact {binding (.var n) (.var xs) with ann := none} with
  | none => false
  | some a =>
      let facts := if duplicate then a.inference.binderSchemes ++ a.inference.binderSchemes else []
      match ScopedDeclaration.checkRHS a.inference.output facts a.lowering.counts (.letRec [] 0) with
      | .error message => (message.splitOn (if duplicate then "duplicate" else "missing")).length > 1
      | .ok _ => false

private def nested (bad : Bool) : Option TypedLowered :=
  artifact (binding (.var n)
    (.letIn ⟨"alias"⟩ [] [] (some ⟨[], exact (if bad then .add (.var n) (.lit 1) else .var n)⟩)
      (.var xs) (.var ⟨"alias"⟩))) (.letIn span leaf leaf)

private def cn : Count := .var ⟨.rigid, 7⟩
private def cm : Count := .var ⟨.rigid, 99⟩
private def coreAnn : Ty := .bl (.solid cn) (.solid cn) (.prim .int)
private def interpreted (ids : List Nat) (rows : Bindings) (caller : List Nat) (expected : String) : Bool :=
  match InterpretedAnnotation.decode ids rows caller coreAnn with
  | .ok d => d.bounds.pretty == expected
  | _ => false

private def quantifiedEnvRejected : Bool :=
  match identity with
  | none => false
  | some a => match ScopedDeclaration.telescope a.lowering.counts (.letRec [] 0) with
    | .ok [id] =>
        let env := [.list (.var ⟨.rigid, id⟩) (.var ⟨.rigid, id⟩) (.prim .int)]
        match ScopedDeclaration.checkRHS a.inference.output a.inference.binderSchemes
            a.lowering.counts (.letRec [] 0) [] env with
        | .error msg => (msg.splitOn "outside explicit captures").length > 1
        | .ok _ => false
    | _ => false

private def capturedEnvAccepted : Bool :=
  match identity with
  | none => false
  | some a =>
      let env := [.list cm cm (.prim .int)]
      match ScopedDeclaration.checkRHS a.inference.output a.inference.binderSchemes
          a.lowering.counts (.letRec [] 0) [99] env with
      | .error _ => false
      | .ok c => match CountContract.check c.certificate [] c.typed.hm [.lit 3] [] [99] with
        | .ok r => r.bounds.pretty == "BL 3 3 Int → BL 3 3 Int"
        | .error _ => false

private def cases : List (String × Bool) := [
  ("actual inferred symbolic declaration produces usable certificate", accepts identity "BL 3 3 Int → BL 3 3 Int"),
  ("one checked declaration supports independent counts", accepts identity "BL 1 1 Int → BL 1 1 Int" 1 &&
    accepts identity "BL 8 8 Int → BL 8 8 Int" 8),
  ("Cons RHS proves symbolic length increment", accepts consArtifact "BL 3 3 Int → BL 4 4 Int"),
  ("incorrect symbolic result contract rejected", rejects
    (artifact (binding (.var n) (.list [.primLit (.int 1)])) (.list span [leaf])) "interval inclusion"),
  ("nested symbolic binding obligation checked", accepts (nested false) "BL 3 3 Int → BL 3 3 Int"),
  ("incorrect nested symbolic binding rejected", rejects (nested true) "interval inclusion"),
  ("more-general annotated RHS needs explicit HM specialization", rejects
    (artifact (binding (.var n) (.list [])) (.list span [])) "HM specialization"),
  ("quantified declaration counts cannot be outer captures", quantifiedEnvRejected),
  ("actual declaration preserves explicit captured environment counts", capturedEnvAccepted),
  ("recursive calls are not enabled by RHS inspection", rejects
    (artifact (binding (.var n) (.app (.var ⟨"f"⟩) (.var xs))) (.app span leaf leaf)) "outside scoped RHS"),
  ("missing machine binder fact rejected", factsRejected false),
  ("duplicate machine binder fact rejected", factsRejected true),
  ("missing count telescope is not guessed", metadataRejected (fun m => {m with telescopes := []}) "lexical scope"),
  ("wrong-site count telescope is not reconciled by name", metadataRejected
    (fun m => {m with telescopes := m.telescopes.map fun t => {t with site := .letRec [] 1}}) "lexical scope"),
  ("duplicate exact-site telescope rejected", metadataRejected
    (fun m => {m with telescopes := m.telescopes ++ m.telescopes}) "duplicate count telescope"),
  ("symbolic source annotation interpreted without rewriting it", interpreted [7] [(7, .lit 3)] [] "BL 3 3 Int"),
  ("symbolic replacement checked in caller scope", interpreted [7] [(7, cm)] [99] "BL n99 n99 Int"),
  ("source lexical scope checked before interpretation", match InterpretedAnnotation.decode [] [(7, .lit 3)] [] coreAnn with
    | .error _ => true | _ => false),
  ("unscoped interpreted count rejected", match InterpretedAnnotation.decode [7] [(7, cm)] [] coreAnn with
    | .error _ => true | _ => false),
  ("infinite Nat interpretation rejected", match InterpretedAnnotation.decode [7] [(7, .inf)] [] coreAnn with
    | .error _ => true | _ => false),
  ("nested interpretation composes selected coordinates", count (CountAlgebra.compose [(99, .lit 4)] [(7, cm)]) cn == .lit 4),
  ("inner interpretation wins over same-key outer row", count (CountAlgebra.compose [(7, .lit 9)] [(7, .lit 2)]) cn == .lit 2),
  ("simultaneous caller identity is not recursively substituted", count (CountAlgebra.compose [] [(7, cm), (99, .lit 4)]) cn == cm)]

-- Proof-level specialization leaves the same source annotation in the term;
-- only its interpretation changes. It is not an AST rewrite for execution.
example {ids rows Δ env e β} (h : ScopedTyping.Derives ids rows Δ env e β)
    (outer : Bindings) (hf : Finite outer) :
    ScopedTyping.Derives ids (CountAlgebra.compose outer rows) (Δ.map (constraint outer))
      (env.map (bounds outer)) e (bounds outer β) := ScopedTyping.transport outer hf h

def main : IO Unit := do
  for (name, ok) in cases do
    IO.println s!"{if ok then "PASS" else "FAIL"}: {name}"
    unless ok do throw (IO.userError s!"scoped declaration regression: {name}")

#eval main

end FHM.Bounds.ScopedDeclarationTests
