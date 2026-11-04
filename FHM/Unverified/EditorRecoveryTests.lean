import FHM.Unverified.EditorSupport

/-! Recovery consumes certified contextual inference; failed groups do not
produce schemes, and dependencies never acquire guessed placeholder types. -/
namespace FHM.Unverified.EditorRecoveryTests
open Surface.Parse Surface.Span

private def recover (source : String) : Option EditorRecovery.Result := do
  let (program, binders, spanned) ← (parseProgramWithSpans source).toOption
  (EditorRecovery.check program spanned binders (programWideScope binders spanned)).toOption

private def hover (source : String) : Option HoverReport := do
  let (program, binders, spanned) ← (parseProgramWithSpans source).toOption
  pure (collectHover source program binders spanned)

private def definition (report : HoverReport) (name : String) : Option String :=
  (report.symbols.find? (fun symbol => symbol.name == name && symbol.isDef && symbol.kind == "val")).map (·.type_)

private def unknown (report : HoverReport) (name : String) : Bool :=
  ((definition report name).map (·.startsWith "type unknown (error in ")).getD false

private def independent : String :=
  "let id x = x\nlet bad : Int = True\nlet missing = absent\n" ++
  "let number = id 1\nlet truth = id True\n(number, truth)\n"

#guard match hover independent with
  | some report => report.diagnostics.length == 2 &&
      report.diagnostics.any (·.code? == some "type.annotationMismatch") &&
      report.diagnostics.any (·.code? == some "lower.unboundName") &&
      definition report "number" == some "Int" && definition report "truth" == some "Bool" &&
      unknown report "bad" && unknown report "missing" &&
      report.programTy == "(Int, Bool)"
  | none => false

private def dependencyChain : String :=
  "let failed : Int = True\nlet direct = failed + 1\nlet indirect = direct + 1\n" ++
  "let unrelated x = x\nunrelated 7\n"
#guard match recover dependencyChain with
  | some result => result.diagnostics.length == 1 &&
      result.blocked.any (fun blocked => blocked.names == [ValName.mk "direct"] && blocked.causes == [ValName.mk "failed"]) &&
      result.blocked.any (fun blocked => blocked.names == [ValName.mk "indirect"] && blocked.causes == [ValName.mk "failed"])
  | none => false
#guard match hover dependencyChain with
  | some report => report.diagnostics.length == 1 && report.programTy == "Int" &&
      unknown report "direct" && unknown report "indirect" &&
      (definition report "unrelated").isSome
  | none => false

-- Lexical shadowing must not turn a healthy group into a dependant.
#guard match hover "let bad : Int = True\nlet good bad = bad\ngood 7\n" with
  | some report => report.diagnostics.length == 1 && report.programTy == "Int" &&
      (definition report "good").isSome
  | none => false

-- A syntactic SCC is atomic, even if another member has a complete signature.
private def failedMutual : String :=
  "let f : Int -> Int = \\x -> if True then True else g x\n" ++
  "let g x = f x\nlet blocked = g 1\nlet healthy = 9\nhealthy\n"
#guard match hover failedMutual with
  | some report => report.diagnostics.length == 1 && definition report "healthy" == some "Int" &&
      unknown report "f" && unknown report "g" && unknown report "blocked"
  | none => false

-- Declared and inferred schemes both cross recovery boundaries polymorphically.
#guard match hover ("let failed = absent\nlet id : {a} a -> a = \\x -> x\n" ++
    "let length xs = match xs with | [] -> 0 | h :: t -> 1 + length t\n" ++
    "let numbers = length [id 1]\nlet truths = length [id True]\n(numbers, truths)\n") with
  | some report => report.diagnostics.length == 1 &&
      definition report "numbers" == some "Int" && definition report "truths" == some "Int" &&
      report.programTy == "(Int, Int)"
  | none => false

-- SCC reordering preserves independent forward-reference chains and spans.
#guard match hover ("let answer = identity 7\nlet failed : Int = True\n" ++
    "let identity x = x\nanswer\n") with
  | some report => report.diagnostics.length == 1 && definition report "answer" == some "Int" &&
      report.diagnostics.all (·.line == 2) && report.programTy == "Int"
  | none => false

-- The final expression can fail independently, or be suppressed by dependency.
#guard match hover "let failed : Int = True\n1 True\n" with
  | some report => report.diagnostics.length == 2 && report.programTy.isEmpty &&
      report.diagnostics.any (·.code? == some "type.notFunction")
  | none => false
#guard match hover "let failed : Int = True\nfailed + 1\n" with
  | some report => report.diagnostics.length == 1 && report.programTy.isEmpty
  | none => false

-- This first slice does not speculate past an invalid declaration environment.
#guard match hover "type Bad = Bad _\nlet another = absent\n1\n" with
  | some report => report.diagnostics.length == 1 && report.symbols.isEmpty &&
      report.diagnostics.all (·.code? == some "lower.holeNotAllowed")
  | none => false

end FHM.Unverified.EditorRecoveryTests
