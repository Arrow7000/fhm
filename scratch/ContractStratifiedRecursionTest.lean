import FHM.Unverified.Surface.Parse
import FHM.SurfaceBridge
import FHM.InferW
import FHM.Pretty

/-!
# Contract-stratified recursive-group acceptance tests

This executable fixture pins the intended GHC/Elm-style source-language
boundary for mixed recursive groups:

1. complete annotations are contracts and therefore dependency cuts;
2. unannotated members are inferred and generalized against those contracts;
3. annotated right-hand sides are then checked with the inferred schemes in
   scope; and
4. recursion without a complete annotation is still ordinary monomorphic HM
   recursion.

The two contract-stratified positive cases are deliberately red under the older,
simultaneous mixed-group rule. Run this file after changing that rule with:

```text
lake env lean --run scratch/ContractStratifiedRecursionTest.lean
```
-/

open Surface.Parse
open SurfaceBridge

inductive Expected where
  | accept
  | reject
  deriving BEq

structure Case where
  name : String
  source : String
  expected : Expected
  why : String

/-- Exercise the real surface-to-core-to-inference path, stopping before
evaluation so this fixture isolates the static acceptance boundary. -/
def inferSource (source : String) : Except String Ty := do
  let parsed <- match parseProgram source with
    | .error e => throw s!"parse failure: {e.msg} (line {e.line}, col {e.col})"
    | .ok program => pure program
  let (ctors, core) <- match lowerProgram parsed with
    | none => throw "lowering failure"
    | some lowered => pure lowered
  match infer core.freshFloor ⟨[], ctors⟩ core with
  | none => throw "inference rejection"
  | some (_, _, ty) => pure ty

def ordinaryMutualIdentity : String :=
  "let f = \\x -> if True then x else g x\n" ++
  "let g = \\x -> f x\n" ++
  "(f 1, g True)\n"

/-- The exact annotation-monotonicity regression.  Removing `f`'s annotation
gives `ordinaryMutualIdentity`, which ordinary HM already accepts.  Adding the
valid principal annotation must not make the same cycle fail merely because
the rigid `a` passes through the unannotated sibling `g`.

With contract stratification, `f`'s signature is assumed, `g` is inferred and
generalized as `{b} b -> b`, and only then is `f` checked using that scheme. -/
def annotatedMutualIdentity : String :=
  "let f : {a} a -> a = \\x -> if True then x else g x\n" ++
  "let g = \\x -> f x\n" ++
  "(f 1, g True)\n"

/-- A stronger, genuinely cyclic example.  The annotated member uses inferred
`g` at `Int` and `Bool` in the same RHS.  Conversely, `g` mentions `f`, so SCC
analysis cannot split the declarations before the typing rule does so by
contract.  The dead branch makes the dependency real to the typechecker while
keeping the example operationally harmless should it later be evaluated. -/
def annotatedConsumerOfInferredPoly : String :=
  "let f : Int -> (Int, Bool) =\n" ++
  "  \\n -> (g n, g True)\n" ++
  "let g =\n" ++
  "  \\x -> if True then x else let ignored = f 0 in x\n" ++
  "f 1\n"

/-- No contract means no dependency cut: inferring this self-recursive binding
would require solving `a = List a`, so ordinary HM must continue to reject it. -/
def unannotatedPolyrec : String :=
  "let f =\n" ++
  "  \\x -> if True then x else f [x]\n" ++
  "f 1\n"

/-- Regression guard for complete schemes and scoped type variables.  The
outer rigid `a` remains in scope in the parameter and local annotation, while
the nested complete scheme binds and scopes its own `b`. -/
def scopedAnnotations : String :=
  "let outer : {a} a -> (a, a) =\n" ++
  "  \\(x : a) ->\n" ++
  "    let id : {b} b -> b = \\(y : b) -> y in\n" ++
  "    let kept : a = id x in\n" ++
  "    (kept, x)\n" ++
  "(outer 1, outer True)\n"

def cases : List Case :=
  [ { name := "ordinary mutual identity baseline"
      source := ordinaryMutualIdentity
      expected := .accept
      why := "ordinary HM accepts the unannotated cycle" }
  , { name := "annotation monotonicity across an unannotated sibling"
      source := annotatedMutualIdentity
      expected := .accept
      why := "a principal complete annotation must not make the cycle fail" }
  , { name := "annotated member consumes an inferred sibling polymorphically"
      source := annotatedConsumerOfInferredPoly
      expected := .accept
      why := "contract stratification generalizes g before checking f" }
  , { name := "unannotated polymorphic recursion remains rejected"
      source := unannotatedPolyrec
      expected := .reject
      why := "there is no complete contract at which to cut the dependency" }
  , { name := "complete schemes retain scoped variables"
      source := scopedAnnotations
      expected := .accept
      why := "stratification must preserve annotation scoping" }
  ]

def runCase (test : Case) : IO Bool := do
  IO.println s!"=== {test.name} ==="
  IO.println s!"  {test.why}"
  match inferSource test.source, test.expected with
  | .ok ty, .accept =>
      IO.println s!"  PASS (accepted as {ty.pretty})"
      pure true
  | .error _, .reject =>
      IO.println "  PASS (rejected as intended)"
      pure true
  | .ok ty, .reject =>
      IO.println s!"  FAIL (unexpectedly accepted as {ty.pretty})"
      pure false
  | .error err, .accept =>
      IO.println s!"  FAIL ({err})"
      pure false

def main : IO UInt32 := do
  let results <- cases.mapM runCase
  let passed := results.count true
  IO.println s!"--- {passed}/{results.length} cases behaved as specified ---"
  pure (if passed == results.length then 0 else 1)
