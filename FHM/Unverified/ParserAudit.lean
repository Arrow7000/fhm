import FHM.Unverified.Surface.Parse
import Lean.Data.Json

/-! Opt-in parser verification executable. Structural JSON is independent of
pretty-printing; public spans and binder metadata are compared separately. -/
namespace FHM.Unverified.ParserAudit
open Surface Surface.Parse Lean
private def arr (xs : List Json) : Json := .arr xs.toArray
private def str := Json.str
private def val (name : ValName) : Json := match name with | .mk s => str s
private def ctor (name : CtorName) : Json := match name with | .mk s => str s

private def polyJson (sig : Surface.PolyTy) : Json := arr [arr (sig.foralls.map val), str (reprStr sig.body)]

partial def patternJson : Pattern → Json
  | .name n => arr [str "name", val n]
  | .wildcard => arr [str "wildcard"]
  | .pair a b => arr [str "pair", patternJson a, patternJson b]
  | .cons a b => arr [str "cons", patternJson a, patternJson b]
  | .list xs => arr [str "list", arr (xs.map patternJson)]
  | .ctor n xs => arr [str "ctor", ctor n, arr (xs.map patternJson)]

mutual
partial def exprJson : Surface.Expr → Json
  | .primLit .unit => arr [str "unit"]
  | .primLit (.int n) => arr [str "int", str (toString n)]
  | .primLit (.nat n) => arr [str "nat", str (toString n)]
  | .primLit (.bool b) => arr [str "bool", .bool b]
  | .primLit (.char c) => arr [str "char", str (String.singleton c)]
  | .primBinOp op => arr [str "op", str (reprStr op)]
  | .var n => arr [str "var", val n]
  | .ctor n => arr [str "ctor", ctor n]
  | .pair a b => arr [str "pair", exprJson a, exprJson b]
  | .cons a b => arr [str "cons", exprJson a, exprJson b]
  | .list xs => arr [str "list", arr (xs.map exprJson)]
  | .app a b => arr [str "app", exprJson a, exprJson b]
  | .lambda p ann body => arr [str "lambda", patternJson p, (ann.map (str ∘ reprStr)).getD .null, exprJson body]
  | .ife c t f => arr [str "if", exprJson c, exprJson t, exprJson f]
  | .match_ e arms => arr [str "match", exprJson e, arr (arms.map fun (p, b) => arr [patternJson p, exprJson b])]
  | .letIn n tvs ps ann rhs body => arr [str "let", val n, arr (tvs.map val),
      arr (ps.map fun (n, a) => arr [val n, (a.map (str ∘ reprStr)).getD .null]),
      (ann.map polyJson).getD .null, exprJson rhs, exprJson body]
  | .letRecIn bs body => arr [str "rec", arr (bs.map bindingJson), exprJson body]
partial def bindingJson (b : Surface.Binding) : Json :=
  arr [val b.name, arr (b.tyParams.map val),
    arr (b.params.map fun (n, a) => arr [val n, (a.map (str ∘ reprStr)).getD .null]),
    (b.ann.map polyJson).getD .null, exprJson b.rhs]
end

def programJson (p : Surface.Program) : Json := Json.mkObj [
  ("decls", str (reprStr p.decls)), ("groups", arr (p.groups.map fun g => arr (g.map bindingJson))),
  ("body", exprJson p.body)]

def errorJson (e : ParseError) : Json := Json.mkObj [
  ("ok", .bool false), ("message", str e.msg), ("line", toJson e.line), ("col", toJson e.col),
  ("endLine", toJson e.endLine), ("endCol", toJson e.endCol)]

def strict (source kind : String) : Json :=
  if kind == "expr" then
    match parseExprWithSpans source with
    | .error e => errorJson e
    | .ok (e, bs, sp) => Json.mkObj [("ok", .bool true), ("ast", exprJson e),
        ("binders", str (reprStr bs)), ("spans", str (reprStr sp))]
  else
    match parseProgramWithSpans source with
    | .error e => errorJson e
    | .ok (p, bs, sp) => Json.mkObj [("ok", .bool true), ("ast", programJson p),
        ("binders", str (reprStr bs)), ("spans", str (reprStr sp))]

def request (input : Json) : Json :=
  match input.getObjValAs? String "source" with
  | .error e => Json.mkObj [("error", str e)]
  | .ok source => strict source ((input.getObjValAs? String "kind").toOption.getD "program")
end FHM.Unverified.ParserAudit

def main : IO Unit := do
  let stdin ← IO.getStdin
  let stdout ← IO.getStdout
  repeat
    let line ← stdin.getLine
    if line.isEmpty then break
    let output := match Lean.Json.parse line with
      | .error error => Lean.Json.mkObj [("error", .str error)]
      | .ok input => FHM.Unverified.ParserAudit.request input
    stdout.putStrLn output.compress
