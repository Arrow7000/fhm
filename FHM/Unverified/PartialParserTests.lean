import FHM.Unverified.EditorSupport

/-! Focused integration canaries complement the frozen differential corpus,
independent AST generator, token fuzzing and generated damage/repair suite. -/
namespace FHM.Unverified.PartialParserTests
open Surface.Parse Surface.Span

#guard match parseExprPartial "(1 + , 2 + )" with
  | .ok parsed => parsed.holes.length == 2 && Surface.PartialSyntax.hasHole parsed.expr &&
      parsed.holes.all (fun h => h.first == h.last)
  | .error _ => false

#guard match parseExprPartial "(\\x -> if True then (2 + ) else x + 1)" with
  | .ok parsed => parsed.holes.length == 1 && parsed.binders.any (fun b => b.name == "x")
  | .error _ => false

#guard !(parseExpr "$syntax/1/2").isOk
#guard (PartialProgram.toStrict ⟨⟨[], [], .var (.mk "$syntax/1/2")⟩, [], { groups := [], body := .leaf Span.empty }, []⟩).isOk == false

private def report (source : String) : Option HoverReport := do
  let parsed ← FHM.Unverified.ParserRecovery.check source |>.toOption
  pure (collectParseRecoveredHover source parsed)
private def definition (r : HoverReport) (name : String) : Option String :=
  (r.symbols.find? (fun s => s.isDef && s.name == name && s.kind == "val")).map (·.type_)

#guard match report "let bad : Int = (1 + )\nlet use=bad\nlet healthy=7\nhealthy\n" with
  | some r => r.diagnostics.length == 1 && definition r "bad" == some "type unknown (error in syntax at 1:22)" &&
      ((definition r "use").map (·.startsWith "type unknown")).getD false && definition r "healthy" == some "Int"
  | none => false

-- An unrecoverable later header must not discard an earlier partial function.
#guard match report "let broken x = ((1 + ), x + 1)\nlet bad : = 2\nlet healthy=7\nhealthy\n" with
  | some r => r.diagnostics.length == 2 && definition r "healthy" == some "Int" &&
      r.symbols.any (fun s => s.isDef && s.name == "x" && s.kind == "param" && s.type_ == "Int")
  | none => false

-- A soft declaration prefix cannot acquire a guessed constructor signature.
#guard match report "type Bad = MkBad (Int,)\nlet use=MkBad\nlet healthy=7\nhealthy\n" with
  | some r => r.diagnostics.length == 1 && definition r "healthy" == some "Int" &&
      ((definition r "use").map (·.startsWith "type unknown")).getD false
  | none => false

-- Complete valid syntax uses the exact strict result, including metadata.
example {source : String} {expr : Surface.Expr} {binders : List BinderSpan} {spanned : SpannedExpr}
    (h : parseExprWithSpans source = .ok (expr, binders, spanned)) :
    parseExprPartial source = .ok ⟨expr, binders, spanned, []⟩ :=
  parseExprPartial_of_strict h

end FHM.Unverified.PartialParserTests
