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

private def holeJson (h : ExprHole) : Json := Json.mkObj [
  ("name", val h.name), ("first", toJson h.first), ("last", toJson h.last),
  ("span", str (reprStr h.span)), ("error", errorJson h.error)]

private def inside (a b : Surface.Span.Span) : Bool :=
  (b.startLine < a.startLine || (b.startLine == a.startLine && b.startCol ≤ a.startCol)) &&
  (a.endLine < b.endLine || (a.endLine == b.endLine && a.endCol ≤ b.endCol))

/-- Desugared prefix applications and inner head-parameter lambdas/lets have
source hulls but are not standalone surface expressions. Audit their children. -/
private def syntheticRoot (tokens : Array Tok) (e : Surface.Expr) (span : Surface.Span.Span) : Bool :=
  let first := ((tokens.toList.filter fun t => inside (Surface.Span.Span.ofTok t) span && !isComment t.token).head?).map (·.token)
  match e with
  | .primBinOp _ | .app (.primBinOp _) _ => true
  | .lambda .. => first != some (.punct .backslash) && first != some (.punct .lparen)
  | .letIn .. | .letRecIn .. => first != some (.keyword .«let») && first != some (.punct .lparen)
  | _ => false

partial def fragments (tokens : Array Tok) (e : Surface.Expr) (tree : Surface.Span.SpannedExpr) : List Json := Id.run do
  if tree.span == Surface.Span.Span.empty then return []
  match tree with
  | .generated _ => return []
  | .generatedRoot child => return fragments tokens e child
  | _ => pure ()
  if !Surface.PartialSyntax.hasHole e && !syntheticRoot tokens e tree.span then
    let selected := tokens.filter fun t => inside (Surface.Span.Span.ofTok t) tree.span
    let parsed := runTokP expr selected
    let checked := match parsed with
      | .error error => errorJson error
      | .ok (actual, _, _) => Json.mkObj [("ok", .bool true), ("ast", exprJson actual)]
    return [Json.mkObj [("span", str (reprStr tree.span)), ("ast", exprJson e), ("parsed", checked)]]
  match e, tree with
  | .pair a b, .pair _ sa sb | .cons a b, .cons _ sa sb | .app a b, .app _ sa sb =>
      return fragments tokens a sa ++ fragments tokens b sb
  | .list xs, .list _ ss => return (xs.zip ss).flatMap (fun (e, s) => fragments tokens e s)
  | .lambda _ _ b, .lambda _ sb => return fragments tokens b sb
  | .letIn _ _ _ _ r b, .letIn _ sr sb => return fragments tokens r sr ++ fragments tokens b sb
  | .letRecIn bs b, .letRecIn _ rs sb => return (bs.zip rs).flatMap (fun (b, s) => fragments tokens b.rhs s) ++ fragments tokens b sb
  | .ife a b c, .ife _ sa sb sc => return fragments tokens a sa ++ fragments tokens b sb ++ fragments tokens c sc
  | .match_ e arms, .match_ _ se ss => return fragments tokens e se ++ (arms.zip ss).flatMap (fun ((_, e), s) => fragments tokens e s)
  | _, _ => return []

private def registryOk (e : Surface.Expr) (holes : List ExprHole) : Bool :=
  let names := (Surface.freeNames [] e).filter isRecoveryName
  names.all (fun name => holes.any (·.name == name)) &&
    holes.all (fun h => names.contains h.name && h.first ≤ h.last) &&
    (holes.map (·.name)).eraseDups.length == holes.length

def recovering (source kind : String) : Json :=
  match Surface.Lex.lex source with
  | .error e => errorJson (lexToParse e)
  | .ok tokens =>
    if kind == "expr" then
      match parseExprPartial source with
      | .error e => errorJson e
      | .ok r => Json.mkObj [("ok", .bool true), ("ast", exprJson r.expr),
          ("binders", str (reprStr r.binders)), ("spans", str (reprStr r.spanned)),
          ("holes", arr (r.holes.map holeJson)), ("registryOk", .bool (registryOk r.expr r.holes)),
          ("fragments", arr (fragments tokens r.expr r.spanned))]
    else
      match parseProgramTokensPartial tokens with
      | .error e => errorJson e
      | .ok r => Json.mkObj [("ok", .bool true), ("ast", programJson r.program),
          ("binders", str (reprStr r.binders)), ("spans", str (reprStr r.spanned)),
          ("holes", arr (r.holes.map holeJson)), ("registryOk", .bool (registryOk r.program.term r.holes)),
          ("strictProjection", .bool r.toStrict.isOk),
          ("fragments", arr (fragments tokens r.program.body r.spanned.body ++
            ((r.program.groups.flatten).zip r.spanned.groups.flatten).flatMap (fun (b, s) => fragments tokens b.rhs s)))]

def request (input : Json) : Json :=
  match input.getObjValAs? String "source" with
  | .error e => Json.mkObj [("error", str e)]
  | .ok source =>
      let kind := (input.getObjValAs? String "kind").toOption.getD "program"
      if (input.getObjValAs? String "mode").toOption == some "partial" then recovering source kind
      else strict source kind
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
