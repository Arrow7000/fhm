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

private def runtimeCertified (src : String) : Except String Unit := do
  let a ← artifact src
  let (result, _) ← RecursiveFound.synthNodes a
  unless result.runtimeReady.isSome do
    throw "test: accepted bounds program lost its runtime theorem"

private def returns (r : Except String String) (expected : String) : Bool :=
  match r with | .ok s => s == expected | _ => false
private def fails (r : Except String α) (needle : String) : Bool :=
  match r with | .error m => (m.splitOn needle).length > 1 | _ => false
private def succeeds (r : Except String α) : Bool :=
  match r with | .ok _ => true | .error _ => false

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

private def mapSource (body : String := "(transform (h + 0) + 0) :: f transform t") : String :=
  "let f : {n : Nat} (Int -> Int) -> BL n n Int -> BL n n Int =\n" ++
  "  \\transform xs -> match xs with | [] -> [] | h :: t -> " ++ body ++ "\n"

private def appendSource : String :=
  "let f : {n m : Nat} BL n n Int -> BL m m Int -> BL (n + m) (n + m) Int =\n" ++
  "  \\xs ys -> match xs with | [] -> ys | h :: t -> (h + 0) :: f t ys\n"

private def repeatedSource : String :=
  "let f : {n : Nat} BL n n Int -> BL n n Int -> BL n n Int =\n" ++
  "  \\(xs : BL n n Int) (ys : BL n n Int) -> " ++
  "(\\(ignored : List Int) -> xs) (f xs ys)\n"

private def compoundSource : String :=
  "let f : {n : Nat} BL (n + 1) (n + 1) Int -> BL n n Int -> BL n n Int =\n" ++
  "  \\(xs : BL (n + 1) (n + 1) Int) (ys : BL n n Int) -> " ++
  "(\\(ignored : List Int) -> ys) (f xs ys)\n"

private def callbackSource : String :=
  "let f : {n : Nat} (BL n n Int -> BL n n Int) -> BL n n Int -> BL n n Int =\n" ++
  "  \\(transform : BL n n Int -> BL n n Int) (xs : BL n n Int) -> " ++
  "(\\(ignored : List Int) -> transform xs) (f transform xs)\n"

private def soleCallbackSource (domain : String) : String :=
  "let f : {n : Nat} (" ++ domain ++ " -> BL n n Int) -> Int =\n" ++
  "  \\(g : " ++ domain ++ " -> BL n n Int) -> " ++
  "(\\(ignored : Int) -> 1) (f g)\n"

private def consecutiveSource (body : String := "f xs") : String :=
  selfSource ++
  "let g : {m : Nat} BL m m Int -> BL m m Int =\n" ++
  "  \\(xs : BL m m Int) -> (\\(ignored : List Int) -> " ++ body ++ ") (g xs)\n"

private def provenanceRejected (modify : TypedLowered → TypedLowered) : Except String Unit := do
  let a ← artifact (selfSource ++ "f []\n")
  let _ ← RecursiveFound.synthNodes (modify a)
  pure ()

private def cases : List (String × Bool) := [
  ("parsed program without a recursive root checks scalar operations", returns
    (run "1 + 2\n") "Int"),
  ("parsed program without a recursive root infers exact List bounds", returns
    (run "[1, 2]\n") "BL 2 2 Int"),
  ("parsed ordinary monomorphic root let retains its checked List bounds", returns
    (run "let xs : BL 2 2 Int = [1, 2]\nxs\n") "BL 2 2 Int"),
  ("parsed ordinary root let still checks its source annotation", fails
    (run "let xs : BL 0 0 Int = [1]\nxs\n") "interval inclusion"),
  ("parsed hole-annotated identity generalizes RHS-induced count sharing", returns (run (
    "let listId : BL _ _ Int -> BL _ _ Int = \\xs -> xs\n" ++
    "(listId [1, 2], listId [1, 2, 3])\n"))
      "(BL 2 2 Int, BL 3 3 Int)"),
  ("generalized hole escape retains the runtime fundamental witness", succeeds
    (runtimeCertified (
      "let listId : BL _ _ Int -> BL _ _ Int = \\xs -> xs\n" ++
      "listId [1, 2]\n"))),
  ("parsed program without recursion uses the same Bool branch checker", returns
    (run "if True then 1 else 2\n") "Int"),
  ("parsed Pair construction retains both field bounds", returns
    (run "([1, 2], True)\n") "(BL 2 2 Int, Bool)"),
  ("parsed nested Pair construction retains inner origins", returns
    (run "(1, ([2], [3, 4]))\n") "(Int, (BL 1 1 Int, BL 2 2 Int))"),
  ("parsed Pair pattern opens both fields with their exact bounds", returns (run (
    "let headFst : (BL 2 2 Int, Int) -> Int = \\p -> " ++
    "match p with | (xs, y) -> match xs with | h :: t -> h\n" ++
    "headFst ([1, 2], 0)\n")) "Int"),
  ("parsed Pair wildcard is exhaustive without opening fields", returns (run (
    "let ignorePair : (BL 2 2 Int, Int) -> BL 1 1 Int = \\p -> " ++
    "match p with | _ -> [1]\nignorePair ([1, 2], 0)\n")) "BL 1 1 Int"),
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
  ("parsed count-polymorphic value is not instantiated by guesswork", fails (run (selfSource ++ "f\n")) "origin-backed arguments"),
  ("parsed fixed polymorphic HM signature retains one in-group instance", succeeds (run (
    "let f : {n : Nat, a} BL n n a -> BL n n a =\n" ++
    "  \\xs -> f xs\nf []\n"))),
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
    "  \\(xs : BL typo typo Int) -> (\\(ignored : List Int) -> xs) (f xs)\nf []\n")) "unresolved count scope"),
  ("type foralls do not become Nat binders through permissive syntax", fails (run (
    "let f : {n m} BL (n * m) (n * m) Int -> BL (n * m) (n * m) Int =\n" ++
    "  \\xs -> xs\nf []\n")) "unresolved count scope"),
  ("parsed more-general RHS is checked against its narrower annotation", returns (run (
    "let f : {n : Nat} BL n n Int -> BL n n Int =\n" ++
    "  \\(xs : BL n n Int) -> f xs\nf []\n")) "BL 0 0 Int"),
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
  ("parsed generalized parameter receives declared recursive guidance", returns (run (
    "let f : {n : Nat} BL n n Int -> BL n n Int =\n" ++
    "  \\xs -> match xs with | [] -> [] | h :: t -> h :: f t\nf []\n")) "BL 0 0 Int"),
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
  ("parsed curried monomorphic map obtains length from its second argument", returns
    (run (mapSource ++ "f (\\x -> x + 1) [1, 2, 3]\n")) "BL 3 3 Int"),
  ("parsed curried map checks its empty case", returns
    (run (mapSource ++ "f (\\x -> x + 1) []\n")) "BL 0 0 Int"),
  ("parsed curried map rejects an extra output element", fails
    (run (mapSource "1 :: ((transform (h + 0) + 0) :: f transform t)" ++
      "f (\\x -> x + 1) []\n")) "interval inclusion"),
  ("parsed partial curried map requests a later origin", fails
    (run (mapSource ++ "f (\\x -> x + 1)\n")) "later argument origin"),
  ("parsed curried append transports two counts and their sum", returns
    (run (appendSource ++ "f [1, 2] [3]\n")) "BL 3 3 Int"),
  ("parsed curried append preserves the second count at Nil", returns
    (run (appendSource ++ "f [] [1, 2]\n")) "BL 2 2 Int"),
  ("parsed repeated count accepts both actual domains", returns
    (run (repeatedSource ++ "f [1] [2]\n")) "BL 1 1 Int"),
  ("parsed repeated count rejects inconsistent later argument", fails
    (run (repeatedSource ++ "f [] [1]\n")) "interval inclusion"),
  ("parsed later direct count supplies an earlier compound endpoint", returns
    (run (compoundSource ++ "f [1, 2] [3]\n")) "BL 1 1 Int"),
  ("parsed earlier compound domain is still checked", fails
    (run (compoundSource ++ "f [1] [2]\n")) "interval inclusion"),
  ("parsed third-argument length is not prematurely fixed", returns (run (
    "let f : {n : Nat} Int -> (Int -> Int) -> BL n n Int -> BL n n Int =\n" ++
    "  \\seed transform xs -> match xs with | [] -> [] | h :: t -> " ++
    "(transform (h + seed) + 0) :: f seed transform t\n" ++
    "f 1 (\\x -> x + 1) [1, 2]\n")) "BL 2 2 Int"),
  ("parsed mutually recursive curried maps keep independent telescopes", returns (run (
    "let f : {n : Nat} (Int -> Int) -> BL n n Int -> BL n n Int =\n" ++
    "  \\transform xs -> match xs with | [] -> [] | h :: t -> (transform (h + 0) + 0) :: g transform t\n" ++
    "let g : {n : Nat} (Int -> Int) -> BL n n Int -> BL n n Int =\n" ++
    "  \\transform xs -> match xs with | [] -> [] | h :: t -> (transform (h + 0) + 0) :: f transform t\n" ++
    "f (\\x -> x + 1) [1, 2]\n")) "BL 2 2 Int"),
  ("parsed deferred List callback obtains a later actual origin", returns
    (run (callbackSource ++ "f (\\ys -> ys) [1, 2]\n")) "BL 2 2 Int"),
  ("parsed deferred List callback checks count zero", returns
    (run (callbackSource ++ "f (\\ys -> ys) []\n")) "BL 0 0 Int"),
  ("parsed deferred callback cannot increase the required exact length", fails
    (run (callbackSource ++ "f (\\ys -> 1 :: ys) [1, 2]\n")) "interval inclusion"),
  ("parsed deferred callback still checks its internal source annotation", fails
    (run (callbackSource ++ "f (\\ys -> let bad : BL 0 0 Int = ys in bad) [1, 2]\n")) "interval inclusion"),
  ("parsed unknown List callback does not manufacture its own count origin", fails
    (run (soleCallbackSource "BL n n Int" ++ "f (\\ys -> ys)\n")) "independent origin"),
  ("parsed scalar callback remains a synthesized sole count origin", returns
    (run (soleCallbackSource "Int" ++ "f (\\x -> [])\n")) "Int"),
  ("parsed curried callback receives guidance through its lambda telescope", returns (run (
    "let f : {n : Nat} (Int -> BL n n Int -> BL n n Int) -> BL n n Int -> BL n n Int =\n" ++
    "  \\(g : Int -> BL n n Int -> BL n n Int) (xs : BL n n Int) -> " ++
    "(\\(ignored : List Int) -> g 0 xs) (f g xs)\nf (\\seed ys -> ys) [1, 2]\n")) "BL 2 2 Int"),
  ("parsed deferred callback remains checked at a captured caller count", returns (run (
    callbackSource.replace "(f transform xs)" "(g xs)" ++
    "let g : {m : Nat} BL m m Int -> BL m m Int =\n" ++
    "  \\(xs : BL m m Int) -> f (\\ys -> ys) xs\n" ++
    "g [1, 2]\n")) "BL 2 2 Int"),
  ("parsed consecutive groups retain distinct telescopes and outer calls", returns
    (run (consecutiveSource ++ "g [1, 2]\n")) "BL 2 2 Int"),
  ("parsed consecutive group body can still call the earlier group", returns
    (run (consecutiveSource ++ "f [1, 2, 3]\n")) "BL 3 3 Int"),
  ("parsed bad later group rejects rather than exporting earlier reports", fails
    (run (consecutiveSource "1 :: f xs" ++ "f []\n")) "interval inclusion"),
  ("parsed later group still checks final body inclusion", fails
    (run (consecutiveSource ++ "(\\(xs : BL 0 0 Int) -> 1) (g [1])\n")) "interval inclusion"),
  ("parsed deferred callback works across consecutive groups", returns (run (
    callbackSource ++
    "let g : {m : Nat} BL m m Int -> BL m m Int =\n" ++
    "  \\(xs : BL m m Int) -> (\\(ignored : List Int) -> f (\\ys -> ys) xs) (g xs)\n" ++
    "g [1, 2]\n")) "BL 2 2 Int"),
  ("parsed recursive group in a universal RHS still needs transport", fails (run (
    "let f : {n : Nat} BL n n Int -> BL n n Int =\n" ++
    "  \\(xs : BL n n Int) -> let g : {m : Nat} Int -> Int = \\i -> g i in " ++
    "(\\(ignored : Int) -> xs) (g 1)\nf []\n")) "nested groups unsupported"),
  ("parsed scalar prefix is captured by a later recursive map", returns (run (
    "(let offset : Int = 1 in\n" ++
    mapSource "(transform (h + offset) + 0) :: f transform t" ++
    "in f (\\x -> x + 1) [1, 2])\n")) "BL 2 2 Int"),
  ("parsed unannotated monomorphic prefix keeps its actual List count", returns (run (
    "(let saved = [1, 2] in\n" ++ selfSource ++ "in f saved)\n")) "BL 2 2 Int"),
  ("parsed annotated prefix still rejects an incorrect count", fails (run (
    "(let saved : BL 0 0 Int = [1] in\n" ++ selfSource ++ "in f [])\n")) "interval inclusion"),
  ("parsed monomorphic let between groups keeps certified outer call bounds", returns (run (
    "(" ++ selfSource ++ "in let saved : BL 2 2 Int = f [1, 2] in\n" ++
    "let g : {m : Nat} BL m m Int -> BL m m Int =\n" ++
    "  \\(xs : BL m m Int) -> (\\(ignored : List Int) -> f xs) (g xs)\n" ++
    "in g saved)\n")) "BL 2 2 Int"),
  ("parsed generalized prefix is not silently treated as monomorphic", fails (run (
    "(let id = \\x -> x in\n" ++ selfSource ++ "in f [])\n")) "generalized local HM let"),
  ("parsed polymorphic source prefix is checked as a generalized declaration", returns (run (
    "(let id : {a} a -> a = \\x -> x in\n" ++ selfSource ++ "in f [])\n")) "BL 0 0 Int"),
  ("parsed program lambda can contain a certified recursive group", returns (run (
    "\\(xs : BL 2 2 Int) ->\n" ++ selfSource ++ "in f xs\n")) "BL 2 2 Int → BL 2 2 Int"),
  ("parsed program lambda captures its scalar assumption in an inner group", returns (run (
    "\\(offset : Int) ->\n" ++ mapSource "(transform (h + offset) + 0) :: f transform t" ++
    "in f (\\x -> x + 1) [1, 2]\n")) "Int → BL 2 2 Int"),
  ("parsed unannotated scalar lambda still checks its inner group's result", returns (run (
    "\\offset ->\n" ++ mapSource "(transform (h + offset) + 0) :: f transform t" ++
    "in f (\\x -> x + 1) [1, 2]\n")) "Int → BL 2 2 Int"),
  ("parsed program lambda cannot hide an invalid inner contract", fails (run (
    "\\(xs : BL 2 2 Int) ->\n" ++
    unannotatedCopy "1 :: ((h + 0) :: f t)" ++ "in f xs\n")) "interval inclusion"),
  ("parsed monomorphic let RHS can introduce a certified recursive group", returns (run (
    "(let result : BL 2 2 Int = (\n" ++ selfSource ++ "in f [1, 2]) in result)\n")) "BL 2 2 Int"),
  ("parsed unannotated monomorphic let RHS retains an inner group certificate", returns (run (
    "(let result = (\n" ++ selfSource ++ "in f [1, 2]) in result)\n")) "BL 2 2 Int"),
  ("parsed enclosing let still checks the actual inner group result bounds", fails (run (
    "(let result : BL 0 0 Int = (\n" ++ selfSource ++ "in f [1, 2]) in result)\n")) "interval inclusion"),
  ("parsed invalid group in a monomorphic let RHS rejects the whole program", fails (run (
    "(let result : BL 2 2 Int = (\n" ++ unannotatedCopy "1 :: ((h + 0) :: f t)" ++
    "in f [1, 2]) in result)\n")) "interval inclusion"),
  ("parsed program lambda demand guides an unannotated List domain", returns (run (
    "(let copy : BL 2 2 Int -> BL 2 2 Int = \\xs -> " ++
    "match xs with | [] -> [] | h :: t -> (h + 0) :: t in copy [1, 2])\n")) "BL 2 2 Int"),
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
