import FHM.Unverified.EditorSupport

/-! Parser recovery keeps native parsing and source positions, withholds rejected
headers, and resumes only at top-level boundaries outside comment/string tokens. -/
namespace FHM.Unverified.ParserRecoveryTests
open Surface.Parse Surface.Span

private def recover (source : String) : Option ParserRecovery.Result :=
  (ParserRecovery.check source).toOption
private def hover (source : String) : Option HoverReport :=
  (recover source).map (collectParseRecoveredHover source)
private def value (report : HoverReport) (name : String) : Option String :=
  (report.symbols.find? (fun symbol => symbol.name == name && symbol.kind == "val" && symbol.isDef)).map (·.type_)

private def simple : String := "let broken = (\nlet good = 7\nlet alsoBad = 1 True\ngood\n"
#guard match recover simple with
  | some result => result.errors.length == 1 && result.errors.all (·.line == 1) &&
      result.seed.values.any (·.1 == ValName.mk "broken") && result.seed.body.isEmpty &&
      (result.program.groups.flatten.map (·.name)).contains ⟨"good"⟩
  | none => false
#guard match hover simple with
  | some report => report.diagnostics.length == 2 && value report "good" == some "Int" &&
      report.programTy == "Int" && report.diagnostics.any (·.code? == some "type.notFunction")
  | none => false

-- Multiple malformed items do not prevent declaration or value recovery.
#guard match hover ("type Broken =\nlet bad (x : Int) =\nlet alsoBad = (\n" ++
    "type Good = Good Int\nlet healthy = Good 7\nhealthy\n") with
  | some report => report.diagnostics.length == 3 && value report "healthy" == some "Good" &&
      report.programTy == "Good"
  | none => false

-- A malformed type header blocks dependent declarations, annotations and ctors.
#guard match hover ("type Broken =\ntype Dep = Dep Broken\nlet use = Dep 1\n" ++
    "let annotated (x : Broken) = x\nlet good = 41\ngood\n") with
  | some report => report.diagnostics.length == 1 && value report "good" == some "Int" &&
      ((value report "use").map (·.startsWith "type unknown (error in syntax at ")).getD false
  | none => false

-- A softly parsed declaration prefix is not an accepted declaration when its
-- trailing field syntax failed on the same line.
#guard match recover "type Bad = Bad (\nlet good=7\ngood\n" with
  | some result => result.errors.length == 1 && result.program.decls.isEmpty &&
      result.seed.types.any (·.1 == TyName.mk "Bad") &&
      result.seed.constructors.any (·.1 == CtorName.mk "Bad")
  | none => false

-- Duplicate source definitions are all excluded, including a later well-formed
-- definition with the same name as an earlier syntactically rejected header.
#guard match hover "let f=1\nlet f=True\nlet use = f\nlet healthy=7\nhealthy\n" with
  | some report => report.diagnostics.length == 1 && value report "healthy" == some "Int" &&
      ((value report "use").map (·.startsWith "type unknown")).getD false &&
      report.programTy == "Int"
  | none => false
#guard match hover "let f = (\nlet f=1\nlet use=f\nlet healthy=7\nhealthy\n" with
  | some report => report.diagnostics.length == 1 && value report "healthy" == some "Int" &&
      ((value report "use").map (·.startsWith "type unknown")).getD false
  | none => false

-- No failed final expression can acquire the synthetic unit body's type.
#guard match hover "let good=7\n(good,\n" with
  | some report => report.diagnostics.length == 1 && value report "good" == some "Int" &&
      report.programTy.isEmpty
  | none => false
#guard match hover "(1,\nlet good=7\ngood\n" with
  | some report => report.diagnostics.length == 1 && report.programTy == "Int"
  | none => false

-- Native tokenisation prevents false boundaries inside multiline strings or
-- comments; nested let declarations must not become top-level exports either.
#guard match recover ("let broken = (\n  /-\nlet ghost=99\n  -/\n" ++
    "  let local = (\nlet good=7\ngood\n") with
  | some result => result.errors.length == 1 &&
      !(result.program.groups.flatten.map (·.name)).contains ⟨"ghost"⟩ &&
      !(result.program.groups.flatten.map (·.name)).contains ⟨"local"⟩
  | none => false

-- Documentation remains attached to the following valid authored declaration.
#guard match hover "let broken = (\n--- Healthy documentation.\nlet good=7\ngood\n" with
  | some report => report.diagnostics.length == 1 &&
      report.symbols.any (fun symbol => symbol.isDef && symbol.name == "good" &&
        symbol.doc == some "Healthy documentation.")
  | none => false
#guard match hover "--- orphan docs\n1\n" with
  | some report => report.diagnostics.length == 1 && report.programTy == "Int"
  | none => false

-- The strict parser and runner interfaces remain strict.
#guard !(parseProgramWithSpans simple).isOk
#guard (parseProgramWithSpans "let good=7\ngood\n").isOk

end FHM.Unverified.ParserRecoveryTests
