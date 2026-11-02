# Anonymous type holes

Anonymous `_` holes are supported throughout expression annotations in the
parser, editor and execution pipeline. Each occurrence is independent. Named
`?name` holes share one type only within their enclosing annotation; see
[canonical partial Core](partial-core.md) for the architecture and proofs.

## Try it

Run [the commented playground](../scratch/anonymous-type-holes.fhm) with
`.lake/build/bin/fhm run scratch/anonymous-type-holes.fhm`, or open it in the
editor and hover its parameters and annotation holes. Its six sections mix
function heads, explicit lambdas, structured and datatype holes, patterns,
matches, partial forall signatures and terminating mutual recursion.
[The rejected example](../scratch/anonymous-type-holes-errors.fhm) shows that a
hole still enforces the fixed parts of its annotation; change its `True`
argument to `41` to make it succeed.

## Function heads

Head parameters may be unannotated, concretely annotated, or contain holes:

```text
let add (x : Int) y : Int = x + y
let pair left right = (left, right)
let apply (fn : _ -> _) value = fn value
let keep {element} (value : element) ignored : element = value
```

A type after the parameters is the return type, so `add` has two `Int`
parameters and an `Int` result. Missing parameter and result annotations are
inferred. Written forall variables remain in scope through the RHS, including
nested headed bindings; unused written binders are retained. Heads without
annotations use ordinary HM inference. Explicit lambda RHSs remain supported.

## Architecture and proofs

Source syntax is `InferInput := Expr TyTemplate` in `Core`. `InputTyping` in
`SourceTyping` directly judges it. It has no inference protection set, and its
annotation premises choose local matching witnesses before fresh openings.
There is no completed-source AST or complete-Core compatibility API.

`SourceSupport` supplies source operations, annotation premises, the internal
`ScopedTyping` refinement and recursive state. `InferW` contains `InferCert`,
the executable worker and soundness. `Completeness` proves completeness and
expression-type principality. `AnnotationMatching` and `AnnotationAllocation`
separate declarative matching from certified metavariable allocation.

The worker returns a type and substitution/frontier, together with editor node
and binder facts. The CLI evaluates erasure of the original source. Node and
binder maps are joined with provenance by the deliberately unverified editor
pipeline; end-to-end hover correctness has never been part of the inference
certificate.

## Recursive signatures

Partial written-forall slots remain provisional monotypes while their residual
SCC is solved. Each member retains its written prefix and may infer additional
binders under the existing generalization policy. Complete written signatures
permit polymorphic recursive calls; partial signatures do not. Ordinary let
polymorphism and recursive SCC/generalization policy are unchanged.

## Regression coverage

`FHM.Examples` contains source derivations and semantic canaries.
`FHM.Examples.Programs` exercises source and surface programs, including the
ported ordinary and annotated recursion examples. `FHM.Unverified.EditorSupportTests`
checks lowering, provenance and inferred artifacts. The scratch audit, CLI/editor
smoke suite, web hover snapshots and grammar tests cover the operational path.
Current commands and verification results are recorded in
[the verification section](partial-core.md#verification).
