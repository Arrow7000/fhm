import FHM.Unverified.EditorSupport

/-! Complete declared interfaces cut editor dependencies without certifying
implementations. Incomplete, malformed and quarantined contracts do not. -/
namespace FHM.Unverified.InterfaceRecoveryTests
open Surface.Parse Surface.Span

private def hover (source : String) : Option HoverReport := do
  let (p, bs, sp) ← (parseProgramWithSpans source).toOption
  pure (collectHover source p bs sp)
private def definition (r : HoverReport) (name : String) : Option RangedSymbol :=
  r.symbols.find? (fun s => s.name == name && s.kind == "val" && s.isDef)
private def typed (r : HoverReport) (name ty : String) : Bool :=
  ((definition r name).map (·.type_ == ty)).getD false
private def declared (r : HoverReport) (name : String) : Bool :=
  ((definition r name).map (·.declared)).getD false
private def assumes (r : HoverReport) (name dependency : String) : Bool :=
  ((definition r name).map fun s => s.assumptions.any (·.name == ValName.mk dependency)).getD false
private def unknown (r : HoverReport) (name : String) : Bool :=
  ((definition r name).map (·.type_.startsWith "type unknown")).getD false

#guard match hover ("let broken : Int -> Int = \\x -> True\nlet number = broken 3\n" ++
    "let wrong = broken False\nnumber\n") with
  | some r => typed r "broken" "Int → Int" && declared r "broken" && typed r "number" "Int" &&
      assumes r "number" "broken" && unknown r "wrong" && r.programTy == "Int" &&
      r.assumptions.any (·.name == ValName.mk "broken") &&
      r.diagnostics.map (·.code?) == [some "type.annotationMismatch", some "type.argumentMismatch"]
  | none => false

-- A signed member cuts a source cycle, allowing the unsigned member to infer.
#guard match hover ("let f : Int -> Int = \\x -> if True then True else g x\n" ++
    "let g x = f x\nlet number = g 3\nnumber\n") with
  | some r => declared r "f" && typed r "g" "Int → Int" && assumes r "g" "f" &&
      typed r "number" "Int" && assumes r "number" "f" && r.diagnostics.length == 1
  | none => false

#guard match hover ("let bad : {item} item -> item = \\x -> 1 True\n" ++
    "let number = bad 1\nlet truth = bad False\n(number, truth)\n") with
  | some r => typed r "bad" "∀ item. item → item" && declared r "bad" &&
      typed r "number" "Int" && typed r "truth" "Bool" && r.programTy == "(Int, Bool)" &&
      r.diagnostics.length == 1
  | none => false

#guard match hover "let bad : _ -> Int = \\x -> True\nlet use = bad False\nuse\n" with
  | some r => unknown r "bad" && unknown r "use" && r.assumptions.isEmpty && r.programTy.isEmpty
  | none => false
#guard match hover "let bad : ?a -> Int = \\x -> True\nlet use = bad False\nuse\n" with
  | some r => unknown r "bad" && unknown r "use" && r.assumptions.isEmpty
  | none => false
#guard match hover "type Bad = MkBad _\nlet bad : Bad = MkBad 1\nlet use = bad\n0\n" with
  | some r => unknown r "bad" && unknown r "use" && r.diagnostics.length == 1
  | none => false
#guard match hover "let bad : List = 1\nlet use = bad\n0\n" with
  | some r => unknown r "bad" && unknown r "use" && r.diagnostics.length == 1
  | none => false

-- Contract assumptions do not taint a healthy lexical shadow or unrelated use.
#guard match hover "let bad : Int = True\nlet good bad = bad\nlet use = good False\nuse\n" with
  | some r => declared r "bad" && typed r "use" "Bool" &&
      ((definition r "good").map (·.assumptions.isEmpty)).getD false &&
      ((definition r "use").map (·.assumptions.isEmpty)).getD false && r.assumptions.isEmpty
  | none => false

-- Local declarations are visible to the continuation, preserving source types.
#guard match hover "let outer x = let bad : Int -> Int = \\y -> True in (bad x, bad False)\n0\n" with
  | some r => declared r "bad" && typed r "bad" "Int → Int" && unknown r "outer" &&
      r.diagnostics.map (·.code?) == [some "type.annotationMismatch", some "type.argumentMismatch"]
  | none => false

-- Repair restores the ordinary strict artifact path and removes assumptions.
#guard match hover "let bad : Int -> Int = \\x -> x\nlet use = bad 1\nuse\n" with
  | some r => typed r "bad" "Int → Int" && typed r "use" "Int" && !declared r "bad" &&
      r.symbols.all (·.assumptions.isEmpty) && r.assumptions.isEmpty && r.diagnostics.isEmpty
  | none => false

end FHM.Unverified.InterfaceRecoveryTests
