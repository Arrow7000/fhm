import FHM.Unverified.EditorSupport

/-! Operational recovery canaries: native fragments can constrain their real
context, but a rejected enclosing binding never becomes an exported scheme. -/
namespace FHM.Unverified.ExpressionRecoveryTests
open Surface.Parse Surface.Span

private def hover (source : String) : Option HoverReport := do
  let (program, binders, spanned) ← (parseProgramWithSpans source).toOption
  pure (collectHover source program binders spanned)

private def codes (report : HoverReport) : List (Option String) := report.diagnostics.map (·.code?)
private def definitions (report : HoverReport) (name : String) : List String :=
  report.symbols.filterMap fun symbol =>
    if symbol.isDef && symbol.name == name then some symbol.type_ else none
private def unknown (report : HoverReport) (name : String) : Bool :=
  (definitions report name).all (·.startsWith "type unknown") && !(definitions report name).isEmpty

#guard match hover "let f x = (1 True, (2 False, x + 1))\nlet blocked = f 3\n0\n" with
  | some report => codes report == [some "type.notFunction", some "type.notFunction"] &&
      definitions report "x" == ["Int"] && unknown report "f" && unknown report "blocked"
  | none => false

#guard match hover ("let f x = let bad = 1 True in let good = x + 1 in (2 False, (good, bad))\n0\n") with
  | some report => report.diagnostics.length == 2 && definitions report "good" == ["Int"] &&
      definitions report "x" == ["Int"] && unknown report "bad" && unknown report "f"
  | none => false

-- Constraints from successful siblings share the enclosing monomorphic x.
#guard match hover "let f x = (1 True, (x + 1, if x then 0 else 1))\n0\n" with
  | some report => codes report == [some "type.notFunction", some "type.mismatch"] &&
      definitions report "x" == ["Int"] && unknown report "f"
  | none => false

#guard match hover "let f xs = match xs with | x :: tail -> (1 True, x + 1) | [] -> 2 False\n0\n" with
  | some report => codes report == [some "type.notFunction", some "type.notFunction"] &&
      definitions report "xs" == ["List Int"] && definitions report "x" == ["Int"] &&
      definitions report "tail" == ["List Int"] && unknown report "f"
  | none => false

-- Unavailable declarations suppress pattern cascades, not independent bodies.
#guard match hover "type Bad = MkBad _\nlet f x = match x with | MkBad y -> (1 True, y)\n0\n" with
  | some report => codes report == [some "lower.holeNotAllowed", some "type.notFunction"] &&
      unknown report "y" && unknown report "f"
  | none => false

#guard match hover ("let f : Int -> Int = \\x -> if True then True else g x\n" ++
    "let g : Int -> Int = \\x -> if True then False else f 1\nlet blocked = f 1\n0\n") with
  | some report => codes report == [some "type.annotationMismatch", some "type.annotationMismatch"] &&
      definitions report "f" == ["Int → Int"] && definitions report "g" == ["Int → Int"] && definitions report "blocked" == ["Int"]
  | none => false

#guard match hover "let f : {item} item -> item = \\x -> let bad = 1 True in (2 False, x)\n0\n" with
  | some report => report.diagnostics.length == 2 && definitions report "x" == ["item"] &&
      unknown report "bad" && definitions report "f" == ["∀ item. item → item"]
  | none => false

-- A rejected local forall cannot constrain the outer x to its rigid variable.
#guard match hover ("let f x = let bad : {a} a -> a = \\y -> if True then x else y in (1 True, x + 1)\n0\n") with
  | some report => codes report == [some "type.escapingVariable", some "type.notFunction"] &&
      definitions report "x" == ["Int"] && definitions report "bad" == ["∀ a. a → a"] && unknown report "f"
  | none => false

-- A concrete non-function is wrong regardless of an unavailable argument.
#guard match hover "let bad : Int = True\nlet next = 1 bad\n0\n" with
  | some report => codes report == [some "type.annotationMismatch", some "type.notFunction"] && unknown report "next"
  | none => false

-- Successful constraints inside a rejected forall remain shared when safe.
#guard match hover ("let f x = let bad : {a} a -> a = \\y -> let ok = x + 1 in " ++
    "let fail = 1 True in y in if x then 0 else 1\n0\n") with
  | some report => codes report == [some "type.notFunction", some "type.mismatch"] &&
      definitions report "x" == ["Int"] && definitions report "bad" == ["∀ a. a → a"]
  | none => false

end FHM.Unverified.ExpressionRecoveryTests
