# Annotated in-block polymorphism with erased execution

**Status:** production implementation complete on `annotated-polyrec-erased`, 2026-10-03

**Current implementation baseline:** a recursive member with a complete explicit
scheme is polymorphic inside its SCC, while an unannotated member remains
monomorphic and is generalized only for the body. Runtime terms remain completely
type-erased. [`FHM/Core.lean`](../FHM/Core.lean) specifies this mixed source rule;
[`FHM/InferW.lean`](../FHM/InferW.lean) implements its focused `consPoly`/`consMono`
checker; and [`FHM/RuntimeTyping.lean`](../FHM/RuntimeTyping.lean) provides the
proof-only mixed runtime judgment over the real Core `Expr`/`Ctx` types. The latter
proves preservation for the complete real `Step` relation, including recursive
unfolding and constructor match reduction. Soundness crosses from source `TypeOfHM`
to erased `RunWT`; source principality and completeness deliberately stay on
`TypeOfHM`.

The structural and scoped-opening gates are now present in
[`FHM/AnnotatedPolyRecErasure.lean`](../FHM/AnnotatedPolyRecErasure.lean). It is a
small calculus over the repository's real `Ty`/`PolyTy` definitions. It proves a
cofinite structural source-to-runtime erasure bridge, a direct-self-use witness,
and a closed nested-scoped witness in which an outer `forall c` opens through
`forall a. a -> c` in a recursive RHS. The corresponding runtime terms contain
neither annotations nor type applications. The module is part of the default
verified build and has no `sorry` axioms.

The all-annotated hard gate is now complete: erased recursive unfolding preserves
`RunWT`. The proof passes through cofinite rigid opening, proof-only type
substitution, concrete scheme inhabitation, recursive-member rewrapping, de Bruijn
weakening, and simultaneous term substitution. No type abstraction, type
application, or scheme survives in runtime syntax.

The mixed runtime rule is now fixed in
[`FHM/AnnotatedPolyRecHybrid.lean`](../FHM/AnnotatedPolyRecHybrid.lean): annotated
members carry proof-only schemes, while unannotated members carry shared monotypes
inside the SCC and `genGroup` schemes in the enclosing body. A concrete mixed group
is typed under that rule with no specs in its runtime syntax. The mixed hard gate is
also complete: the module proves type substitution with shared-pool freshening,
rewrapping at every exported scheme instance for both `.poly` and `.mono` members,
simultaneous term substitution, and preservation of erased recursive unfolding.

## Executive summary

Explicitly annotated polymorphic recursion is compatible with a completely
type-erased runtime. The source annotation makes checking decidable; after checking,
the annotation and all inferred instantiations may be erased. The runtime evaluator
does not need types.

The old FHM investigation reached the opposite conclusion because it silently
required one syntax-directed typing relation to do two different jobs:

1. specify which annotated source programs the compiler accepts; and
2. reconstruct all required recursive schemes from every residual runtime term.

Under that requirement, a load-bearing recursive annotation had to remain in the
machine term. If it mentioned a type variable bound by an enclosing annotation,
ordinary term substitution could orphan that variable. Runtime type application and
type-beta then looked unavoidable.

The missing design was to erase the recursive annotation from the runtime term while
retaining its scheme as a witness in the **typing derivation**. A proof may remember
static information that the evaluator does not. This yields the following pipeline:

```text
annotated source e
    │
    │ source inference/checking
    ▼
Dsrc : SourceWT Γ e τ
    │
    │ erasure soundness
    ▼
Drun : RunWT Γ (erase e) τ
    │
    │ ordinary type-free reduction and preservation
    ▼
RunWT Γ r τ  for every runtime reduct r
```

`RunWT` may contain implicit or existential polymorphic-recursive schemes in its
proof objects. It need not be an executable inference system. The compiler never
reconstructs a type for `erase e`; it transfers the scheme supplied by the source
annotation from `Dsrc` into `Drun`.

Bidirectional checking is a convenient way to formulate the source rules, but it is
neither necessary nor sufficient by itself. The essential architectural move is the
separation between source acceptance evidence and erased-runtime safety evidence.

## The feature under discussion

The feature is **annotation-directed polymorphism inside a recursive dependency
group**. For example, an explicitly polymorphic member may be instantiated at
different types by itself or by siblings while the group is being checked:

```text
let rec
  f : forall a. a -> Int
  f x = if condition then f 0 else f True
in
  f "hello"
```

The interesting scoped-variable case is a nested recursive annotation that refers
both to its own quantified variable and to an enclosing one:

```text
outer : forall c. c -> ...
outer (w : c) =
  let rec
    f : forall a. Nest a -> c
    f xs = ... f nestedXs ...
  in
    ... f ... w ...
```

Here `a` belongs to `f`, while `c` is the rigid type of the current invocation of
`outer`. Recursive occurrences of `f` may instantiate `a` differently, but they must
retain that same `c`.

This is stronger than the HM-only language selected by the reset. In the selected
language every occurrence of every recursive member within one SCC shares one
monotype, regardless of annotations.

Three cases were historically conflated:

1. **Own quantifiers:** `f : forall a. ...`, where every variable in the scheme is
   bound by `f`'s own `forall`.
2. **Ambient rigid variables:** a scheme containing an already free, rigid type
   identity from the surrounding static context.
3. **Nested scoped variables:** a local scheme such as `forall a. a -> c`, where `c`
   is bound by an enclosing source annotation and must be specialized when that
   enclosing scheme is instantiated.

The third case exposed the old source-shaped runtime problem. The proof-only design
in this note is specifically intended to handle it without runtime types.

## What is and is not undecidable

Unannotated polymorphic-recursive inference is undecidable in general. Algorithm W
cannot be extended to discover arbitrary polymorphic-recursive schemes while
retaining the ordinary HM inference guarantees.

Checking a definition against a supplied rank-1 scheme is a different problem. Given

```text
f : forall a. T(a)
```

the checker can:

1. skolemize the annotation with fresh rigid variables `A`;
2. check `f`'s RHS against `T(A)`;
3. put the full declared scheme `forall a. T(a)` in the recursive-use environment;
4. instantiate that scheme freshly at every recursive occurrence; and
5. reject the definition if its RHS does not meet the declared scheme.

A schematic checking premise is:

```text
fresh A
Γ, f : (forall a. T(a)) ⊢src rhs ⇐ T(A)
```

The current invocation is checked at rigid `A`; a recursive lookup of `f` obtains the
scheme and may instantiate it at some other type. No unknown recursive scheme is
being inferred.

Without the annotation, inference instead starts with one monotype:

```text
Γ, f : β ⊢src rhs ⇒ τ
```

All recursive occurrences constrain the same `β`. Supporting arbitrary fresh
instances here would require discovering the polymorphic-recursive scheme, which is
the undecidable problem.

## External language research

The runnable comparison corpus in
[`recursion-language-comparison/`](../recursion-language-comparison/README.md) checks
the boundary using compilers from the caller's ambient `<nixpkgs>` in a Nix shell. It
prints the selected compiler versions and the real diagnostics for the expected
failures, but the repository currently does not pin a nixpkgs revision.

| Language | Verified accepted case | Nearby rejected case | Relevant policy |
|---|---|---|---|
| OCaml | `let rec f : 'a. ...` | An ordinary `'a` annotation | Explicit universal annotation enables polymorphic recursion. |
| Haskell/GHC | Recursive binding with a complete signature | Same body without a signature | Signed recursive bindings may be checked polymorphically; ordinary type parameters are erased before execution. |
| F# | Recursive function with explicit `<'T>` | Ordinary `'T` annotation | A full signature enables early generalization/checking. |
| Elm | Annotated member instantiated differently by sibling members in a real cycle | Differently typed direct self-uses; unannotated mutual uses | Elm has a deliberately asymmetric rule rather than uniform per-SCC polymorphism. |
| Standard ML | Polymorphism after the recursive declaration exits | Differently typed uses inside the recursive declaration | Closest precedent for FHM's selected HM-only rule. |

Important conclusions from these probes:

- “supports polymorphic recursion” is too coarse. The annotation form, direct
  self-use, sibling use, SCC splitting, and early-generalization policy all matter.
- Scoped type variables are static lexical identities. They do not by themselves
  imply runtime type passing.
- GHC's typed System FC intermediate language should not be confused with its
  runtime behavior. Ordinary parametric type arguments are erased. A typed
  intermediate language is one proof and compiler architecture, not a semantic
  requirement for executing the feature.
- Elm demonstrates that useful but nonuniform points between HM recursion and full
  annotated polymorphic recursion exist. Such rules need independent specification;
  they do not fall out automatically from ordinary HM inference.

Primary references:

- Fritz Henglein, [*Type inference with polymorphic recursion*](https://doi.org/10.1145/169701.169692), ACM TOPLAS 15(2), 1993.
- A. J. Kfoury, J. Tiuryn, and P. Urzyczyn, [*Type reconstruction in the presence of polymorphic recursion*](https://doi.org/10.1145/169701.169687), ACM TOPLAS 15(2), 1993.
- Alan Mycroft, *Polymorphic type schemes and recursive definitions*, International Symposium on Programming, 1984.
- [OCaml manual: polymorphic recursion](https://ocaml.org/manual/5.4/polymorphism.html#s:polymorphic-recursion).
- [Haskell Report: function and pattern bindings](https://www.haskell.org/onlinereport/decls.html#sect4.4.1) and [GHC recursive binding groups](https://ghc.gitlab.haskell.org/ghc/doc/users_guide/bugs.html#typechecking-of-recursive-binding-groups).
- [GHC scoped type variables](https://ghc.gitlab.haskell.org/ghc/doc/users_guide/exts/scoped_type_variables.html).
- [F# specification: processing recursive groups](https://fsharp.github.io/fslang-spec/inference-procedures/#1465-processing-recursive-groups-of-definitions).
- [The Definition of Standard ML, rule 26 and commentary](https://smlfamily.github.io/sml97-defn.pdf#page=42).
- Martin Sulzmann et al., [*System F with type equality coercions*](https://www.microsoft.com/en-us/research/wp-content/uploads/2016/07/fc-new-tyco.pdf), the basis of GHC's typed System FC core.
- Simon Peyton Jones and Mark Shields, [*Lexically scoped type variables*](https://www.microsoft.com/en-us/research/publication/lexically-scoped-type-variables/), 2002.

## Historical path through FHM

### 1. The original erasure result was sound

Commit `e374bc9` added scoped type variables and found that literal subject reduction
on annotated source terms was false. An enclosing annotated `let` could reduce away
while an annotation within its RHS still referred to the enclosing type binder.

The correct repair at that point was already “check with annotations, run erased.”
The development proved that erasing ordinary lambda and `let` annotations preserved
typing, then stated runtime safety over erased terms.

### 2. Recursive schemes were later only partially erased

When annotated polymorphic recursion was added, its recursive scheme was considered
“load-bearing for typeability.” The erasure function therefore kept recursive
schemes, and `IsTyErased` was relaxed to classify terms containing those schemes as
erased. Reduction rewrapped the recursive group with the same schemes.

This supported self-contained schemes such as `forall a. Nest a -> Int`, because
their type variables were all bound by the retained scheme itself.

It failed for a nested scheme such as `forall a. Nest a -> c`. The outer source
binder for `c` disappeared through term reduction while the retained recursive
annotation survived. The surviving annotation then contained a dangling type
variable.

### 3. A constrained impossibility result became a universal claim

The investigation correctly showed that none of these repairs worked while the
recursive scheme had to remain recoverable from runtime syntax:

1. **Keep the scheme unchanged:** its reference to the consumed outer binder dangles.
2. **Drop the scheme:** the existing syntax-directed `TypeOfHM` treats the recursive
   binding monomorphically and cannot type its polymorphic recursive calls.
3. **Pre-open the outer variable to a fresh free variable:** the fresh variable is
   rigid and cannot later become each concrete instantiation demanded by the outer
   scheme.

The mistaken conclusion was that scoped variables inside polymorphic-recursive
annotations were incompatible with erasure. The actual conclusion was narrower:

> They are incompatible with partially erased source-shaped runtime terms whose
> schemes must be reconstructed by the same syntax-directed source typing relation.

The hidden premise is visible in
[`design-memo-erasure-migration.md`](design-memo-erasure-migration.md): “the term is
the machine state” was taken to imply that the term was the only possible place to
record an instantiation. That implication is false. A typing derivation may contain
static evidence absent from the evaluator state.

### 4. Type passing solved the stronger, unnecessary problem

The type-passing design made each variable occurrence carry its type arguments,
made generalization explicit as term-level type abstraction, and made substitution
perform type-beta through all retained annotations. It thereby recovered literal
subject reduction for annotated, source-shaped machine states.

It also caused the large costs recorded elsewhere in the repository:

- `Expr.var` acquired type arguments used by reduction;
- term substitution had to traverse and instantiate types;
- inference became an elaborator producing a distinct term;
- recursive generalization produced a term-level `Λ` nest containing repeated group
  structure, leading to quadratic elaborated AST growth;
- `TypeOfElabHM`, faithfulness, source soundness, and extensive opening/closing
  infrastructure were required;
- every later feature and proof inherited the source/elaborated/runtime distinction.

This machinery was coherent, but it was not forced by the desired surface feature.
It was forced by the stronger chosen invariant.

## The naive theorem shape and why it fails

The troublesome architecture uses annotated expressions as evaluator states and asks
one relation to type both original source and every reduct:

```lean
inductive TypeOfSource : TyVarCtx -> Ctx -> Expr -> Ty -> Prop
  | letRecAnn
      (schemes : List PolyTy)
      (hrhs : TypeOfRecGroup schemes ctx rhss)
      (hbody : TypeOfSource (schemes ++ ctx) body result) :
      TypeOfSource ctx (.letRec anns rhss body) result
  -- ...

inductive Step : Expr -> Expr -> Prop
  -- substitutes source-shaped RHS expressions into source-shaped bodies

theorem preservation_naive
    (ht : TypeOfSource typeVars ctx e ty)
    (hs : Step e e') :
    TypeOfSource typeVars ctx e' ty
```

For nested scoped annotations, substitution can remove the syntax that binds an outer
type variable while copying a nested annotation that mentions it. The conclusion is
then ill-scoped. Keeping literal preservation requires the reduction itself to know
the selected type instantiation:

```lean
| var (index : Nat) (typeArgs : List Ty)

-- term substitution also performs type substitution
subst (.var i typeArgs) values = instTy typeArgs values[i]
```

Once this is the runtime syntax, explicit type abstraction, elaboration, and their
proof infrastructure follow naturally. The theorem is achievable, but it purchases a
stronger property than an erased language needs.

## A fully erased formulation

The cleaner design separates author-facing checking from runtime safety.

### Source syntax and source checking

Source syntax retains annotations:

```lean
inductive SourceExpr
  | var : Nat -> SourceExpr
  | letRec : List (Option PolyTy × SourceExpr) -> SourceExpr -> SourceExpr
  -- ...
```

The source relation records the intended acceptance boundary. One possible
bidirectional sketch is:

```lean
inductive Infer : SourceCtx -> SourceExpr -> Ty -> Prop
inductive Check : SourceCtx -> SourceExpr -> Ty -> Prop

-- For an explicitly polymorphic member:
--   * skolems check the implementation at the declared scheme;
--   * the whole scheme is available for recursive occurrences.
inductive CheckRecGroup :
    SourceCtx -> List (PolyTy × SourceExpr) -> Prop
  | cons
      (hscoped : SchemeScoped outerDepth sigma)
      (hfresh : FreshNames avoid sigma.paramCount skolems)
      (hrhs : Check (openScheme sigma skolems :: recSchemes ++ ctx)
                    (openScopedExpr skolems rhs)
                    (openSchemeBody sigma skolems))
      (hrest : CheckRecGroup ctx rest) :
      CheckRecGroup ctx ((sigma, rhs) :: rest)
```

The exact group rule must treat all members simultaneously and specify how annotated
and unannotated members mix. The important point is that only explicit complete
schemes receive polymorphic recursive use. Unannotated members remain monomorphic.

The existing Algorithm-W relation need not necessarily be rewritten wholesale as a
bidirectional system. An annotated-recursive-group checking mode can be embedded in
an otherwise synthesizing algorithm. Bidirectionality mainly makes the distinction
and error reporting clearer.

### Runtime syntax

Runtime syntax contains no annotations or type applications:

```lean
inductive RuntimeExpr
  | var : Nat -> RuntimeExpr
  | letRec : List RuntimeExpr -> RuntimeExpr -> RuntimeExpr
  -- ...

def erase : SourceExpr -> RuntimeExpr
  | .var i => .var i
  | .letRec bindings body =>
      .letRec (bindings.map fun (_, rhs) => erase rhs) (erase body)
  -- erase every other annotation structurally
```

`RuntimeStep` performs only ordinary term substitution. It has no `instTy`, type
arguments, or type-beta rule.

### Proof-only runtime typing

`RunWT` types erased terms. Recursive schemes are witnesses in its derivation rather
than fields of `RuntimeExpr`:

```lean
inductive RunWT : TyVarCtx -> RunCtx -> RuntimeExpr -> Ty -> Prop
  | var
      (hlookup : ctx[i]? = some sigma)
      (hinst : Instantiates sigma ty) :
      RunWT typeVars ctx (.var i) ty

  | letRecPoly
      (schemes : List PolyTy)
      (hwf : SchemesWF typeVars schemes)
      (hrhss : RunRecGroupWT typeVars (schemes ++ ctx) rhss schemes)
      (hbody : RunWT typeVars (schemes ++ ctx) body result) :
      RunWT typeVars ctx (.letRec rhss body) result
```

`RunRecGroupWT` would check each erased RHS at a fresh rigid opening of its selected
scheme, with the full selected scheme environment available at recursive uses. For a
mixed group, it may contain polymorphic schemes for explicitly annotated members and
trivial one-instance schemes for unannotated members.

Searching for `schemes` from an arbitrary erased `letRec` is not required to be
decidable. `RunWT` is a semantic invariant, not the compiler algorithm.

### The crucial erasure bridge

The source checker supplies exactly the witnesses that the runtime term no longer
contains:

```lean
theorem check_erasure_sound
    (h : SourceWT sourceCtx e ty) :
    RunWT (eraseCtx sourceCtx) (erase e) (eraseTy ty)
```

Or, directly from the algorithmic relation:

```lean
theorem infer_erasure_sound
    (h : Infer rigid sourceCtx e subst ty) :
    RunWT (eraseCtx (subst.onCtx sourceCtx))
          (erase e)
          (subst.onTy ty)
```

In the annotated recursive case, the proof takes the declared schemes from `h`,
opens enclosing scoped variables in those schemes at the proof level, and supplies
the resulting list as the witness to `RunWT.letRecPoly`. No scheme is written into
the erased term.

### Runtime safety

The normal erased-term theorems then have ordinary statements:

```lean
theorem run_progress
    (hclosed : RunWT emptyCtx e ty) :
    RuntimeValue e ∨ ∃ e', RuntimeStep e e'

theorem run_preservation
    (ht : RunWT ctx e ty)
    (hs : RuntimeStep e e') :
    RunWT ctx e' ty

theorem checked_program_safe
    (hc : checkProgram source = some ty)
    (hs : RuntimeStepStar (erase source) runtime) :
    RuntimeValue runtime ∨ ∃ runtime', RuntimeStep runtime runtime'
```

When an enclosing scheme is instantiated, the preservation proof applies type
substitution to the **derivation**, including nested proof-only recursive schemes.
The runtime expression is unchanged by that type substitution. This is the precise
place where the old architecture instead performed runtime `instTy`.

The critical supporting facts would look roughly like:

```lean
-- Opening or substituting types in source annotations has no runtime effect.
theorem erase_openTyVars
    (e : SourceExpr) (types : List Ty) :
    erase (openTyVars types e) = erase e

-- Type substitution transforms static witnesses, contexts, and result types,
-- but not the already-erased runtime expression.
theorem RunWT.typeSubst
    (h : RunWT (c :: typeVars) ctx runtime ty) :
    RunWT typeVars (theta.onCtx ctx) runtime (theta.onTy ty)

-- Ordinary value substitution is enough for runtime beta/let reduction.
theorem RunWT.termSubst
    (hbody : RunWT typeVars (sigma :: ctx) body ty)
    (hvalue : HasScheme typeVars ctx value sigma) :
    RunWT typeVars ctx (body.subst value) ty
```

Mutual recursive unfolding needs the corresponding simultaneous substitution and
rewrapping lemma. `HasScheme` can be a cofinite proposition saying that the same
erased expression has the opened scheme body at every suitable fresh rigid opening.
Again, the scheme belongs to the proof, not to `value`.

## Relation to inference, completeness, and principality

The separation creates two distinct notions of completeness:

1. **Source completeness:** the executable checker succeeds for every program in the
   deliberately chosen annotated source specification, and returns a principal result
   where the language promises one.
2. **Runtime typability:** an erased term may possess some `RunWT` derivation.

`RunWT` should not be the specification against which Algorithm W is complete. If
`RunWT.letRecPoly` existentially chooses arbitrary schemes, an erased unannotated
polymorphic-recursive term can be `RunWT`-typable even though reconstructing those
schemes is undecidable and the source checker intentionally rejects it.

This is harmless provided the statements remain honest:

```lean
-- Desired
SourceWT ctx e ty -> exists result, infer ctx e = some result

-- Desired
infer ctx e = some result -> RunWT ... (erase e) ...

-- Not desired
RunWT ctx (erase e) ty -> exists result, infer ctx e = some result
```

The last implication would recreate the impossible demand that the algorithm infer
arbitrary polymorphic recursion from erased syntax.

The source specification can remain rank-1 and decidable by requiring complete
annotations at the polymorphic-recursive boundary. Higher-rank, impredicative, partial,
or inference-created recursive schemes are separate features and must not be smuggled
in by the runtime relation.

This architecture also assumes parametric types do not affect execution. Typecase,
reflection, representation-directed primitives, typeclass dictionaries, or explicit
runtime type representations would require separate value-level evidence. Effects
would additionally require an explicit value-restriction/generalization policy. None
of those concerns is present in the pure FHM language considered here.

## Alternative proof architectures

The proof-only `RunWT` design is the closest match for a small erased FHM, but it is
not the only sound architecture.

### Typed intermediate language followed by erasure

The checker may elaborate to System F or a similar explicitly typed core, prove that
core well typed, then erase type abstractions and applications before evaluation.
This is conventional and makes instantiation evidence explicit to compiler passes.
It also introduces a second AST, elaboration correctness, correspondence, and erasure
proofs. The old FHM migration additionally allowed type operations into the runtime
step, which is not necessary even with a typed intermediate language.

### Direct logical-relations proof

One can prove directly that erasing a successful source derivation produces a term
with the required runtime behavior, without defining a separate syntactic `RunWT`.
This may avoid one declarative relation but usually moves the complexity into a
semantic typing/logical relation. It is less aligned with the current progress and
preservation style.

### Environment machine with typed proof invariants

A closure-based evaluator can keep lexical term environments rather than repeatedly
substituting source expressions. Its proofs can attach schemes to closures without
putting them in executable syntax. This can make recursive sharing operationally
better, but changing machines is not required for erasure and should be justified
independently.

## Costs and unresolved design choices

The erased design avoids the old runtime machinery, but supporting the feature would
still be a real language and proof project.

### Static language choices

The implementation branch fixes the formerly open choices as follows:

| Case | Intended result |
|---|---|
| Complete annotation, differently typed direct self-calls | Accept |
| Complete annotation, differently typed calls from siblings | Accept |
| Mixed SCC: annotated member used polymorphically by an unannotated sibling | Accept |
| Unannotated member used at different types inside its SCC | Reject |
| Annotated member passes its rigid variable through an unannotated sibling | Reject unless that sibling is also annotated |
| Annotated scheme mentioning an enclosing scoped variable | Accept |
| Partial annotation, type holes, or head-binder scheme sugar | Unsupported |

Groups remain simultaneous for term scope and runtime recursion, but no longer force
annotated members to share one recursive monotype. Each annotated member is checked
at a fresh rigid opening of its own scheme, with all complete annotated schemes and
all unannotated monotypes already present in the group environment. The written
scheme is the recursive and exported interface; an implementation may be more
general so long as it checks against that interface.

The questions below are retained as the historical checklist that led to those
decisions:

- What counts as a complete polymorphic annotation?
- May annotations enable polymorphism for direct self-use, sibling use, or both?
- Are groups checked as syntactic groups or dependency SCCs?
- Can annotated and unannotated members be mixed, and which dependencies constrain
  the latter?
- Does an annotation state the exact exported scheme or merely a ceiling that a more
  general implementation may satisfy?
- How are nested scoped variables represented, opened, and protected from unification?
- Will partial annotations/type holes participate? FHM should keep head-binder sugar
  unsupported until this has a coherent answer.

### Metatheory

- Source soundness and completeness must refer to the source acceptance relation,
  not arbitrary `RunWT` typability.
- `RunWT` needs weakening, type substitution, term substitution, recursive-group
  rewrapping/unfolding, progress, and preservation.
- The erasure theorem must transport outer scoped-variable instantiation through
  nested proof-only schemes.
- Mixed recursive groups need a precise simultaneous rule and corresponding
  substitution lemmas.
- Error reporting should distinguish “recursive occurrence fixed to one monotype”
  from “complete annotation required for polymorphic recursion.”

These are substantial costs, but they are localized to static checking and proof
evidence. They do not require a type-directed evaluator or type-bearing Core terms.

## Implementation plan and progress

The active implementation deliberately begins without altering `Expr` or `Step`.

1. **Freeze examples first.** **Done at the semantic-policy level above;** production
   fixtures will be flipped only when the new checker path lands. The spike now has
   positive direct-self, sibling, and nested-scoped witnesses. Missing-annotation
   and skolem-leak negatives belong in the production checker: the all-annotated
   declarative spike has neither absent annotations nor inference metavariables, so
   pretending to test those there would not exercise the intended failure mode.
2. **Spike a tiny erased calculus.** **Cofinite structural/scoped checkpoint done:**
   [`FHM/AnnotatedPolyRecErasure.lean`](../FHM/AnnotatedPolyRecErasure.lean). Include only variables, functions, application,
   `let`, and `let rec`. Define annotated `SourceWT`, annotation-free `RunWT`, full
   erasure, and the nested `forall a. ... c ...` witness.
3. **Prove the hard bridge first.** **Done for fully annotated and mixed recursive
   groups.** Before touching production FHM, prove
   `SourceWT e τ -> RunWT (erase e) τ` for the nested scoped polymorphic-recursive
   example and prove preservation of its unfolding step. The hybrid spike now proves
   the harder selected rule: complete annotations remain polymorphic inside the SCC,
   ordinary members share monotypes there and are generalized only outside it, and
   both kinds can be substituted during type-free unfolding.
4. **Audit theorem boundaries.** **Done.** Algorithm-W completeness and principality
   remain about source `TypeOfHM`; operational soundness crosses by erasure into
   proof-only `RunWT`. No completeness theorem is claimed for arbitrary `RunWT`.
5. **Choose checker organization.** **Done.** Restore the focused historical
   `InferRecGroup.consPoly` path beside `consMono`; do not turn the whole inferencer
   into a bidirectional calculus and do not change runtime syntax.
6. **Integrate after the mixed spike gate.** **Done.** The real-Core source rule,
   focused checker, proof-only runtime relation, surface bridge, soundness boundary,
   principality, relational and executable completeness, and acceptance fixtures now
   form one coherent vertical slice. Runtime type substitution, fixed-opening
   rewrapping, scheme inhabitation, term weakening, simultaneous term substitution,
   and full `Step` preservation are proved. This includes mixed recursive unfolding,
   the independent constructor instantiations that meet at match reduction, a fully
   erased direct-self unfolding witness, scoped annotations, and public node-type
   metadata that closes temporary checking skolems back to source bound variables.

The stop condition for the spike is important: if the supposedly small calculus once
again demands type arguments on runtime variables, term-level `Λ`, or an elaborated
recursive group copied into executable syntax, the design has accidentally restored
the old invariant and should be reconsidered before migration work begins.

The spike now includes its three meaningful positive witnesses—own-`forall` self
recursion, annotated siblings instantiated differently, and the nested
`forall a. ... c ...` case. Missing-annotation and skolem-leak controls are reserved
for the mixed executable checker, where those failure modes actually exist.

### Production checker shape selected for this branch

The old fused checker already contains most of the useful static vocabulary:
`RecSpec.mono`, `RecSpec.poly`, rigid skolem openings, and the historical
`InferRecGroup.consPoly` rule. The implementation revives those pieces without
reviving their former elaborated/runtime consumers:

1. `RecSpec.init` maps `none` to a fresh `.mono β` and `some σ` to `.poly σ`.
2. The recursive environment renders `.mono β` as a trivial scheme and `.poly σ`
   as the complete declared scheme.
3. `consMono` retains ordinary Damas–Milner inference and one shared monotype.
4. `consPoly` opens the member's scoped variables at fresh rigid skolems, infers the
   opened RHS, checks it against the rigid opening of `σ`, performs the usual escape
   checks, and leaves `σ` itself rigid in the environment.
5. Only solved `.mono` members contribute to the post-group generalisation pool.
   The body sees their inferred schemes and sees each `.poly σ` exactly as `σ`.

This makes the current annotation-ceiling phase unnecessary for annotated members.
That phase exists because the HM-only checker first solves *every* member at a
monotype and checks an annotation afterwards. Under annotation-directed checking,
the annotated RHS has already been checked against its public scheme. Keeping both
mechanisms would duplicate policy and obscure which check grants in-block
polymorphism.

The production source specification now describes the hybrid rule above; the
proof-only runtime relation existentially retains the
same mixed list of schemes after all source annotations have erased. Existing
Algorithm-W completeness and principality claims remain about this decidable source
relation. They must not be generalized to arbitrary proof-only runtime typability.

One important consequence is that the existing same-relation theorem

```text
TypeOfHM Γ e τ -> TypeOfHM Γ (erase e) τ
```

cannot remain the operational bridge. If `TypeOfHM` allowed an annotation-free
runtime group to existentially recover polymorphic schemes, it would also make an
authored, unannotated polymorphic-recursive group declaratively typable. Completeness
of the decidable source inferencer would then be false. Production therefore uses
the honest split already exercised by the spike:

```text
TypeOfHM Γ e τ -> RunWT Γ (erase e) τ
```

Inference soundness, surface safety, and program safety end in `RunWT`; inference
completeness and principality continue to quantify only over annotated-source
`TypeOfHM`. There is deliberately no converse from arbitrary `RunWT` evidence to
successful source inference.

The historical implementation can be mined selectively rather than rediscovered:

- `78cf9a1^` contains the mixed declarative `MonoTyped`/`PolyTyped` group premises;
- `16ae7bc^` contains the deleted relational `InferRecGroup.consPoly` and much of
  its invariant proof structure;
- `7bd7020` activates `.poly` in `RecSpec.init`; and
- `b36ca3d` / `78cf9a1^` contain mixed-group principality and completeness proofs.

Only their static checking structure should be restored. Their elaborated or
type-passing runtime architecture is specifically not part of this design.

## Present decision

FHM now implements the annotation-directed exception while retaining ordinary
HM behavior as the default:

```text
unannotated member: monomorphic inside the SCC, generalized afterwards
complete annotated member: checked and recursively available at that scheme
all members: erased at runtime
```

The proof-first spike, mixed production source/checker, executable completeness,
erasure bridge, runtime preservation, surface safety boundary, examples, and editor
metadata canaries are complete. Head-binder sugar and partial annotations remain out
of scope; they still require a separately designed type-hole story.
