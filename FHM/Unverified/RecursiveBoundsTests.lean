import FHM.Bounds.RecursiveFound
import FHM.Unverified.Surface.Parse
import FHM.Unverified.HMArtifacts

/-! Parsed `.fhm` regressions for the optional recursive bounds boundary.
These exercise the actual parser, source count scopes, inferred found trees and
per-occurrence provenance; they do not invoke the legacy BL pipeline.
-/

namespace FHM.Unverified.RecursiveBoundsTests

open SurfaceBridge SurfaceBridge.Provenance FHM.Bounds

private def selfSource : String :=
  "let f : {n : Nat} BL n n Int -> BL n n Int =\n" ++
  "  \\(xs : BL n n Int) -> (\\(ignored : List Int) -> xs) (f xs)\n"

private def artifact (src : String) : Except String TypedLowered := do
  let (p, _, sp) ← match Surface.Parse.parseProgramWithSpans src with
    | .ok p => pure p | .error e => throw s!"test: .fhm parse failed: {repr e}"
  let decls ← match lowerDataDeclsIn preludeKindEnv p.decls with
    | some ds => pure ds | none => throw "test: source declarations failed"
  let ctors ← match elabDecls (preludeDecls ++ decls) with
    | some cs => pure cs | none => throw "test: constructor elaboration failed"
  let wide : Surface.Span.Span := ⟨1, 1, (src.splitOn "\n").length + 1, 1⟩
  let spanned ← match HMArtifacts.programSpanned p sp wide with
    | some s => pure s | none => throw "test: source provenance shape failed"
  let lower ← match lowerWithProvenance ctors p.term spanned with
    | some l => pure l | none => throw "test: source lowering failed"
  match inferWithProvenance ctors lower with
  | some a => pure a | none => throw "test: source HM inference failed"

private def run (src : String) : Except String String := do
  let a ← artifact src
  let (result, reports) ← RecursiveFound.synthNodes a
  unless reports.length = (logicalCorePaths a.inference.output).length do
    throw "test: source report cardinality mismatch"
  unless exactlyOnce (result.nodes.map (·.path)) (reports.map (·.node.path)) do
    throw "test: provenance join dropped or duplicated an occurrence"
  pure result.bounds.pretty

private def returns (r : Except String String) (expected : String) : Bool :=
  match r with | .ok s => s == expected | _ => false
private def fails (r : Except String α) (needle : String) : Bool :=
  match r with | .error m => (m.splitOn needle).length > 1 | _ => false

private def mutualSource : String :=
  "let f : {n : Nat} BL n n Int -> BL n n Int =\n" ++
  "  \\(xs : BL n n Int) -> (\\(ignored : List Int) -> xs) (g xs)\n" ++
  "let g : {n : Nat} BL n n Int -> BL n n Int =\n" ++
  "  \\(xs : BL n n Int) -> (\\(ignored : List Int) -> xs) (f (1 :: xs))\n" ++
  "f []\n"

private def provenanceRejected (modify : TypedLowered → TypedLowered) : Except String Unit := do
  let a ← artifact (selfSource ++ "f []\n")
  let _ ← RecursiveFound.synthNodes (modify a)
  pure ()

private def cases : List (String × Bool) := [
  ("parsed self-recursive contract and exact empty body result", returns (run (selfSource ++ "f []\n")) "BL 0 0 Int"),
  ("parsed self-recursive contract follows singleton argument origin", returns (run (selfSource ++ "f [1]\n")) "BL 1 1 Int"),
  ("parsed mutual recursion uses independent same-named count binders", returns (run mutualSource) "BL 0 0 Int"),
  ("parsed recursive caller may pass n plus one", returns (run (
    "let f : {n : Nat} BL n n Int -> BL n n Int =\n" ++
    "  \\(xs : BL n n Int) -> (\\(ignored : List Int) -> xs) (f (1 :: xs))\nf []\n")) "BL 0 0 Int"),
  ("parsed nested annotation cannot conceal bad length", fails (run (
    "let f : {n : Nat} BL n n Int -> BL n n Int =\n" ++
    "  \\(xs : BL n n Int) -> (\\(ignored : BL n n Int) -> xs) (f (1 :: xs))\nf []\n")) "interval inclusion"),
  ("parsed contract checked against actual recursive implementation", fails (run (
    "let f : {n : Nat} BL n n Int -> BL n n Int =\n" ++
    "  \\(xs : BL n n Int) -> 1 :: f xs\nf []\n")) "interval inclusion"),
  ("parsed body remains an independent annotation obligation", fails
    (run (selfSource ++ "(\\(demand : BL 1 1 Int) -> 1) (f [])\n")) "interval inclusion"),
  ("parsed count-polymorphic value is not instantiated by guesswork", fails (run (selfSource ++ "f\n")) "needs an argument origin"),
  ("parsed fixed polymorphic HM signature explicitly deferred", fails (run (
    "let f : {n : Nat, a} BL n n a -> BL n n a =\n" ++
    "  \\xs -> f xs\nf []\n")) "polymorphic recursive annotation"),
  ("parsed local binding annotation captures enclosing count binder", returns (run (
    "let f : {n : Nat} BL n n Int -> BL n n Int =\n" ++
    "  \\(xs : BL n n Int) -> let ys : BL n n Int = xs in\n" ++
    "    (\\(ignored : List Int) -> ys) (f ys)\nf []\n")) "BL 0 0 Int"),
  ("parsed local captured annotation remains checked", fails (run (
    "let f : {n : Nat} BL n n Int -> BL n n Int =\n" ++
    "  \\(xs : BL n n Int) -> let ys : BL (n + 1) (n + 1) Int = xs in\n" ++
    "    (\\(ignored : List Int) -> xs) (f xs)\nf []\n")) "interval inclusion"),
  ("unbound nested count parses and passes HM but rejects at count scope", fails (run (
    "let f : {n : Nat} BL n n Int -> BL n n Int =\n" ++
    "  \\(xs : BL typo typo Int) -> (\\(ignored : List Int) -> xs) (f xs)\nf []\n")) "unresolved recursive group count scope"),
  ("type foralls do not become Nat binders through permissive syntax", fails (run (
    "let f : {n m} BL (n * m) (n * m) Int -> BL (n * m) (n * m) Int =\n" ++
    "  \\xs -> xs\nf []\n")) "unresolved recursive group count scope"),
  ("parsed more-general RHS explicitly needs annotation specialization", fails (run (
    "let f : {n : Nat} BL n n Int -> BL n n Int =\n" ++
    "  \\(xs : BL n n Int) -> f xs\nf []\n")) "needs specialization"),
  ("parsed matches stay unsupported rather than using legacy synthesis", fails (run (
    "let f : {n : Nat} BL n n Int -> BL n n Int =\n" ++
    "  \\(xs : BL n n Int) -> match xs with | [] -> xs | h :: t -> xs\nf []\n")) "unsupported"),
  ("missing source origins reject report adapter", fails (provenanceRejected (fun a =>
    {a with lowering := {a.lowering with coreOrigins := []}})) "incomplete typed provenance"),
  ("duplicate source origins reject report adapter", fails (provenanceRejected (fun a =>
    {a with lowering := {a.lowering with coreOrigins := a.lowering.coreOrigins ++ a.lowering.coreOrigins.take 1}}))
      "incomplete typed provenance"),
  ("missing found/source join rejects report adapter", fails (provenanceRejected (fun a =>
    {a with sourceTypes := []})) "incomplete typed provenance")]

def main : IO Unit := do
  for (name, ok) in cases do
    IO.println s!"{if ok then "PASS" else "FAIL"}: {name}"
    unless ok do throw (IO.userError s!"parsed recursive bounds regression: {name}")

#eval main

end FHM.Unverified.RecursiveBoundsTests
