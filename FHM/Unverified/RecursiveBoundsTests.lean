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

private def copySource (empty : String := "[]") (nonempty : String := "h :: f t") : String :=
  "let f : {n : Nat} BL n n Int -> BL n n Int =\n" ++
  "  \\(xs : BL n n Int) -> match xs with | [] -> " ++ empty ++
  " | h :: t -> " ++ nonempty ++ "\n"

private def mutualCopy : String :=
  "let f : {n : Nat} BL n n Int -> BL n n Int =\n" ++
  "  \\(xs : BL n n Int) -> match xs with | [] -> [] | h :: t -> h :: g t\n" ++
  "let g : {n : Nat} BL n n Int -> BL n n Int =\n" ++
  "  \\(xs : BL n n Int) -> match xs with | [] -> [] | h :: t -> h :: f t\n" ++
  "f [1, 2, 3]\n"

private def unannotatedCopy (body : String := "(h + 0) :: f t") : String :=
  "let f : {n : Nat} BL n n Int -> BL n n Int =\n" ++
  "  \\xs -> match xs with | [] -> [] | h :: t -> " ++ body ++ "\n"

private def filterSource (body : String := "if h < 0 then f t else h :: f t")
    (lower : String := "0") : String :=
  "let f : {n : Nat} BL n n Int -> BL " ++ lower ++ " n Int =\n" ++
  "  \\xs -> match xs with | [] -> [] | h :: t -> " ++ body ++ "\n"

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
  ("parsed matches preserve exact input under each constructor path", returns (run (
    "let f : {n : Nat} BL n n Int -> BL n n Int =\n" ++
    "  \\(xs : BL n n Int) -> match xs with | [] -> xs | h :: t -> xs\nf []\n")) "BL 0 0 Int"),
  ("parsed recursive copy checks Nil at count zero", returns
    (run (copySource ++ "f []\n")) "BL 0 0 Int"),
  ("parsed recursive copy checks singleton tail count", returns
    (run (copySource ++ "f [1]\n")) "BL 1 1 Int"),
  ("parsed recursive copy preserves longer exact lengths", returns
    (run (copySource ++ "f [1, 2, 3]\n")) "BL 3 3 Int"),
  ("parsed mutually recursive copies transport predecessor arguments", returns
    (run mutualCopy) "BL 3 3 Int"),
  ("parsed bad empty recursive arm rejects", fails
    (run (copySource "[1]" ++ "f []\n")) "interval inclusion"),
  ("parsed recursive duplication rejects claimed exact length", fails
    (run (copySource "[]" "1 :: (h :: f t)" ++ "f []\n")) "interval inclusion"),
  ("parsed recursive head loss rejects claimed exact length", fails
    (run (copySource "[]" "(\\(r : List Int) -> r) (f t)" ++ "f []\n")) "interval inclusion"),
  ("parsed missing Nil arm cannot cover count-polymorphic input", fails (run (
    "let f : {n : Nat} BL n n Int -> BL n n Int =\n" ++
    "  \\(xs : BL n n Int) -> match xs with | h :: t -> h :: f t\nf []\n")) "Cons-only"),
  ("parsed missing Cons arm cannot cover count-polymorphic input", fails (run (
    "let f : {n : Nat} BL n n Int -> BL n n Int =\n" ++
    "  \\(xs : BL n n Int) -> (\\(r : List Int) -> r) " ++
    "(match xs with | [] -> f xs)\nf []\n")) "Nil-only"),
  ("parsed wildcard recursive identity remains supported", returns (run (
    "let f : {n : Nat} BL n n Int -> BL n n Int =\n" ++
    "  \\(xs : BL n n Int) -> match xs with | _ -> " ++
    "(\\(ignored : List Int) -> xs) (f xs)\nf [1, 2]\n")) "BL 2 2 Int"),
  ("parsed local annotated match uses its checked common result", returns (run (
    "let f : {n : Nat} BL n n Int -> BL n n Int =\n" ++
    "  \\(xs : BL n n Int) -> let ys : BL n n Int = " ++
    "match xs with | [] -> [] | h :: t -> h :: t in\n" ++
    "    (\\(ignored : List Int) -> ys) (f ys)\nf [1, 2]\n")) "BL 2 2 Int"),
  ("parsed unannotated recursive List parameter uses declared count bounds", returns
    (run (unannotatedCopy ++ "f [1, 2, 3]\n")) "BL 3 3 Int"),
  ("parsed unannotated recursive copy still checks count zero", returns
    (run (unannotatedCopy ++ "f []\n")) "BL 0 0 Int"),
  ("parsed unannotated parameter does not excuse a bad recursive length", fails
    (run (unannotatedCopy "1 :: ((h + 0) :: f t)" ++ "f []\n")) "interval inclusion"),
  ("parsed generalized parameter HM identity still requires specialization", fails (run (
    "let f : {n : Nat} BL n n Int -> BL n n Int =\n" ++
    "  \\xs -> match xs with | [] -> [] | h :: t -> h :: f t\nf []\n")) "needs specialization"),
  ("parsed higher-order argument receives captured declared count bounds", returns (run (
    "let f : {n : Nat} BL n n Int -> BL n n Int =\n" ++
    "  \\(xs : BL n n Int) -> " ++
    "(\\(g : BL n n Int -> BL n n Int) -> " ++
    "(\\(ignored : List Int) -> g xs) (f xs)) (\\ys -> ys)\nf [1, 2]\n")) "BL 2 2 Int"),
  ("parsed higher-order argument cannot satisfy a false result bound", fails (run (
    "let f : {n : Nat} BL n n Int -> BL n n Int =\n" ++
    "  \\(xs : BL n n Int) -> " ++
    "(\\(g : BL n n Int -> BL (n + 1) (n + 1) Int) -> " ++
    "(\\(ignored : List Int) -> xs) (f xs)) (\\ys -> ys)\nf []\n")) "interval inclusion"),
  ("parsed recursive filtering checks empty input", returns
    (run (filterSource ++ "f []\n")) "BL 0 0 Int"),
  ("parsed recursive filtering exports zero-to-input-length bounds", returns
    (run (filterSource ++ "f [1, 2, 3]\n")) "BL 0 3 Int"),
  ("parsed conditional copying preserves exact length under List paths", returns
    (run (filterSource "if h < 0 then h :: f t else h :: f t" "n" ++ "f [1, 2]\n")) "BL 2 2 Int"),
  ("parsed filtering cannot claim every element is retained", fails
    (run (filterSource "if h < 0 then f t else h :: f t" "n" ++ "f []\n")) "interval inclusion"),
  ("parsed filtering cannot duplicate beyond its upper bound", fails
    (run (filterSource "if h < 0 then 1 :: (h :: f t) else f t" ++ "f []\n")) "interval inclusion"),
  ("parsed Bool conditions do not invent count refinements", fails (run (
    "let f : {n : Nat} BL n n Int -> BL n n Int =\n" ++
    "  \\(xs : BL n n Int) -> if True then [] else " ++
    "(\\(ignored : List Int) -> xs) (f xs)\nf []\n")) "interval inclusion"),
  ("parsed ordinary scalar recursion can return Bool", returns (run (
    "let f : Int -> Bool = \\n -> if n < 1 then True else f (n - 1)\nf 3\n")) "Bool"),
  ("parsed mutually recursive filters retain independent count scopes", returns (run (
    "let f : {n : Nat} BL n n Int -> BL 0 n Int =\n" ++
    "  \\xs -> match xs with | [] -> [] | h :: t -> if h < 0 then g t else h :: g t\n" ++
    "let g : {n : Nat} BL n n Int -> BL 0 n Int =\n" ++
    "  \\xs -> match xs with | [] -> [] | h :: t -> if h < 0 then h :: f t else f t\n" ++
    "f [1, 2]\n")) "BL 0 2 Int"),
  ("missing source origins reject report adapter", fails (provenanceRejected (fun a =>
    {a with lowering := {a.lowering with coreOrigins := []}})) "incomplete typed provenance"),
  ("duplicate source origins reject report adapter", fails (provenanceRejected (fun a =>
    {a with lowering := {a.lowering with coreOrigins := a.lowering.coreOrigins ++ a.lowering.coreOrigins.take 1}}))
      "incomplete typed provenance"),
  ("missing found/source join rejects report adapter", fails (provenanceRejected (fun a =>
    {a with sourceTypes := []})) "incomplete typed provenance")]

def main : IO Unit := do
  let mut failures := 0
  for (name, ok) in cases do
    IO.println s!"{if ok then "PASS" else "FAIL"}: {name}"
    unless ok do failures := failures + 1
  unless failures = 0 do throw (IO.userError s!"{failures} parsed recursive bounds regressions failed")

#eval main

end FHM.Unverified.RecursiveBoundsTests
