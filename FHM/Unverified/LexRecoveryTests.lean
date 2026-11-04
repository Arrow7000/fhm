import FHM.Unverified.EditorSupport

/-! Native lexer checkpoints preserve healthy prefix/suffix code while no
malformed token can silently turn into a typechecked repaired expression. -/
namespace FHM.Unverified.LexRecoveryTests
open Surface.Parse Surface.Span

private def hover (source : String) : Option HoverReport :=
  (ParserRecovery.check source).toOption.map (collectParseRecoveredHover source)
private def value (report : HoverReport) (name : String) : Option String :=
  (report.symbols.find? (fun symbol => symbol.name == name && symbol.kind == "val" && symbol.isDef)).map (·.type_)

private def closed : String := "let before=1\nlet broken=\"bad\\q\"\nlet healthy=2\nhealthy\n"
#guard !(Surface.Lex.lex closed).isOk
#guard (LexRecovery.check closed).gaps.length == 1
#guard match hover closed with
  | some report => report.diagnostics.length == 1 && value report "before" == some "Int" &&
      value report "healthy" == some "Int" && report.programTy == "Int" &&
      ((value report "broken").map (·.startsWith "type unknown")).getD false
  | none => false

-- Deleting an invalid character could repair arithmetic; recovery must withhold
-- the owning binding and its dependent uses instead of exporting an Int scheme.
#guard match hover "let bad=1 @ + 2\nlet use=bad\nlet healthy=7\nhealthy\n" with
  | some report => report.diagnostics.length == 1 && value report "healthy" == some "Int" &&
      ((value report "bad").map (·.startsWith "type unknown")).getD false &&
      ((value report "use").map (·.startsWith "type unknown")).getD false
  | none => false

-- An earlier grammar failure cannot hide ownership of a later lexical gap.
#guard match hover ("let syntaxBroken=(\nlet lexicalBroken=1 @ + 2\n" ++
    "let use=lexicalBroken\nlet healthy=7\nhealthy\n") with
  | some report => report.diagnostics.length == 2 && value report "healthy" == some "Int" &&
      ((value report "use").map (·.startsWith "type unknown")).getD false
  | none => false

-- Closed malformed multiline literals contain no real declaration keywords.
#guard match hover ("let broken=\"bad\\q\nlet ghost=99\nend\"\nlet healthy=7\nhealthy\n") with
  | some report => report.diagnostics.length == 1 && value report "healthy" == some "Int" &&
      (value report "ghost").isNone
  | none => false

-- An unfinished string keeps the prefix, but its entire tail remains text.
#guard match hover "let before=7\nlet broken=\"unterminated\nlet ghost=99\nbefore\n" with
  | some report => report.diagnostics.length == 1 && value report "before" == some "Int" &&
      (value report "ghost").isNone && report.programTy.isEmpty
  | none => false

-- Comments do not change the meaning of the prefix. Gap markers keep comment
-- text from participating in editor identifier hover/navigation fallbacks.
#guard match hover "let good=7\ngood\n/-\nlet ghost=99\n" with
  | some report => report.diagnostics.length == 1 && value report "good" == some "Int" &&
      (value report "ghost").isNone && report.programTy == "Int"
  | none => false
#guard match hover "let id x=x\n--\t id\nlet good=id 7\ngood\n" with
  | some report => report.diagnostics.length == 1 && value report "good" == some "Int" &&
      report.programTy == "Int"
  | none => false

-- Layout errors quarantine the owning header as well.
#guard match hover "let\tbad=1\nlet use=bad\nlet good=7\ngood\n" with
  | some report => report.diagnostics.length == 1 && value report "good" == some "Int" &&
      ((value report "use").map (·.startsWith "type unknown")).getD false
  | none => false

#guard match (ParserRecovery.check "let bad=1 @ +2 #\nlet good=7\ngood\n").toOption with
  | some result => result.errors.length == 2 &&
      ((result.seed.values.find? (·.1 == ValName.mk "bad")).map (·.2.length)) == some 2
  | none => false

end FHM.Unverified.LexRecoveryTests
