import FHM.Z3.Query

/-!
# FHM — SMT-LIB encoding

Adapted from Percissus.Fresh.Z3 (String symbols instead of Lean `Name`).
-/

namespace FHM.Z3
namespace Encode

private def isSafeSymbolChar (c : Char) : Bool :=
  c.isAlphanum || c == '_' || c == '-'

private def hexHi (n : Nat) : Char :=
  let d := n / 16 % 16
  if d < 10 then Char.ofNat (d + '0'.toNat)
  else Char.ofNat (d - 10 + 'A'.toNat)

private def hexLo (n : Nat) : Char :=
  let d := n % 16
  if d < 10 then Char.ofNat (d + '0'.toNat)
  else Char.ofNat (d - 10 + 'A'.toNat)

private def escapeQuotedChar (c : Char) : String :=
  if c = '_' || c = '|' || c = '\\' then
    let n := c.toNat
    String.ofList ['_', hexHi n, hexLo n]
  else
    String.ofList [c]

private def escapeQuoted (s : String) : String :=
  s.toList.map escapeQuotedChar |>.foldl (· ++ ·) ""

def smtSymbol (n : String) : String :=
  let prefixed := "fhm_" ++ n
  if prefixed.all isSafeSymbolChar then
    prefixed
  else
    "|" ++ escapeQuoted prefixed ++ "|"

def smtExpr : Expr → String
  | .lit n => toString n
  | .name x => smtSymbol x
  | .add a b => s!"(+ {smtExpr a} {smtExpr b})"
  | .mul a b => s!"(* {smtExpr a} {smtExpr b})"
  | .pred a =>
      let inner := smtExpr a
      s!"(ite (= {inner} 0) 0 (- {inner} 1))"
  | .min a b =>
      let ea := smtExpr a
      let eb := smtExpr b
      s!"(ite (<= {ea} {eb}) {ea} {eb})"
  | .max a b =>
      let ea := smtExpr a
      let eb := smtExpr b
      s!"(ite (<= {ea} {eb}) {eb} {ea})"

def smtAtom : Atom → String
  | .eq l r => s!"(= {smtExpr l} {smtExpr r})"
  | .le l r => s!"(<= {smtExpr l} {smtExpr r})"
  | .lt l r => s!"(< {smtExpr l} {smtExpr r})"

def smtAnd (terms : List String) : String :=
  match terms with
  | [] => "true"
  | [t] => t
  | ts => "(and " ++ String.intercalate " " ts ++ ")"

private def declareInt (name : String) : String :=
  s!"(declare-const {smtSymbol name} Int)"

private def assertNonNeg (name : String) : String :=
  s!"(assert (>= {smtSymbol name} 0))"

private def universalNames (q : Query) : List String :=
  q.universalNames.mergeSort

private def unknownNames (q : Query) : List String :=
  q.unknowns.eraseDups.mergeSort

/-- ∃∀ witness script for a conjunction of goals. Requires `goals` nonempty. -/
def toWitnessScriptGoals
    (unknowns : List String) (assumptions : Assumptions) (goals : List Atom)
    (cfg : Config) : String :=
  let allGoalNames := (goals.flatMap Atom.names).eraseDups
  let allAssumpNames := (assumptions.flatMap Atom.names).eraseDups
  let universals :=
    (allAssumpNames ++ allGoalNames).eraseDups.filter (fun n => !unknowns.contains n) |>.mergeSort
  let unknowns' := unknowns.eraseDups.mergeSort
  let header :=
    [ "(set-logic NIA)"
    , s!"(set-option :timeout {cfg.timeoutMs})"
    , "(set-option :produce-models true)"
    ]
  let unknownDecls := unknowns'.map declareInt
  let unknownNonNegs := unknowns'.map assertNonNeg
  let mentionsAnyUniversal (a : Atom) : Bool :=
    a.names.any (fun n => universals.contains n)
  let (innerAssumps, outerAssumps) :=
    assumptions.partition mentionsAnyUniversal
  let outerAsserts := outerAssumps.map fun a => s!"(assert {smtAtom a})"
  let universalDecls :=
    if universals.isEmpty then ""
    else
      let typed := universals.map fun n => s!"({smtSymbol n} Int)"
      "(" ++ String.intercalate " " typed ++ ")"
  let universalNonNegs :=
    smtAnd (universals.map fun n => s!"(>= {smtSymbol n} 0)")
  let assumptionConj :=
    smtAnd (innerAssumps.map smtAtom)
  let goalConj := smtAnd (goals.map smtAtom)
  let body := s!"(=> (and {universalNonNegs} {assumptionConj}) {goalConj})"
  let universalAssert :=
    if universals.isEmpty then
      s!"(assert {body})"
    else
      s!"(assert (forall {universalDecls} {body}))"
  let trailer :=
    [ "(check-sat)"
    , "(get-model)"
    ]
  String.intercalate "\n"
    (header ++ unknownDecls ++ unknownNonNegs ++ outerAsserts
      ++ [universalAssert] ++ trailer)

def Query.toWitnessScript (q : Query) (cfg : Config) : String :=
  toWitnessScriptGoals q.unknowns q.assumptions [q.goal] cfg

def Query.toCheckScript (q : Query) (cfg : Config) : String :=
  let names := q.allNames.mergeSort
  let header :=
    [ "(set-logic QF_NIA)"
    , s!"(set-option :timeout {cfg.timeoutMs})"
    , "(set-option :produce-models true)"
    ]
  let decls := names.map declareInt
  let nonNegs := names.map assertNonNeg
  let assumptionAsserts := q.assumptions.map fun a =>
    s!"(assert {smtAtom a})"
  let negatedGoal :=
    s!"(assert (not {smtAtom q.goal}))"
  let trailer :=
    [ "(check-sat)"
    , "(get-model)"
    ]
  String.intercalate "\n"
    (header ++ decls ++ nonNegs ++ assumptionAsserts ++ [negatedGoal] ++ trailer)

def Query.toScript (q : Query) (cfg : Config) : String :=
  if q.unknowns.isEmpty then Encode.Query.toCheckScript q cfg
  else Encode.Query.toWitnessScript q cfg

def toSatScript (assumptions : Assumptions) (cfg : Config) : String :=
  let names := (assumptions.flatMap Atom.names).eraseDups.mergeSort
  let header :=
    [ "(set-logic QF_NIA)"
    , s!"(set-option :timeout {cfg.timeoutMs})"
    , "(set-option :produce-models true)"
    ]
  let decls := names.map declareInt
  let nonNegs := names.map assertNonNeg
  let assumptionAsserts := assumptions.map fun a =>
    s!"(assert {smtAtom a})"
  let trailer :=
    [ "(check-sat)"
    , "(get-model)"
    ]
  String.intercalate "\n"
    (header ++ decls ++ nonNegs ++ assumptionAsserts ++ trailer)

end Encode
end FHM.Z3
