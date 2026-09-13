# BL restoration: contract and checkpoints

Status: implementation started 2026-09-13. This document applies the corrected
DM-erased memo; it does not revive the historical bounds-preserving AST rewrite.

## Protected foundation

The HM checker and its proved D2 metatheory remain authoritative for HM typing.
Bounds are downstream and never influence HM unification or erased execution
(Path R). Within a recursive group, each member has one HM monotype; annotation
quantifiers do not enable in-group HM polymorphic recursion. At group exit, use
the inferred binder schemes, not user annotation slots as invented metadata.

The input to the new bounds pass is the final `.found` output, carried user
annotations, keyed binder schemes and separate provenance. The pass must not
rerun HM inference, reconstruct missing HM types, or strip the typed tree before
walking it. Existing `synthRoot` remains a legacy root-only demonstration.

## Semantic and executable boundaries

Semantic interval inclusion means that under every assignment satisfying the
path conditions, the demanded lower bound is at most the actual lower bound,
and the actual upper bound is at most the demanded upper bound. Structural
subtyping is contravariant in arrow domains and covariant in arrow results,
list elements and supported data-type parameters. Demand-fragment restrictions
and solver `unknown` responses are algorithmic limitations, not definitions of
semantic truth.

`SemanticSub` is the initial solver-independent specification. Legacy `Sub`
derivations translate to it through `checkValid_sound`; the reverse is not
claimed. Semantic strengthening, reflexivity and transitivity do not depend on
solver axioms. `Interval.Contains.of_subGoals` connects valid inclusion to actual
contained lengths, also without a solver axiom.
This does not yet establish soundness of `checkSub` or `checkSubInst`, nor migrate
`HasBounds`, match coverage or escape checking to the semantic specification.

Positive solver answers remain an explicit trusted boundary. No solver
completeness, verdict monotonicity or axiom-elimination project is implied.

## Initial supported-fragment policy

Start with literal/list origins, typed lambda parameters, application and
bindings, then add branch refinement and recursive contracts. Missing support
must produce a specific error rather than silently falling back to the old
checker or treating unchecked bounds as successful.

Bare `List` supplies shape, not an exact length. `Nil` supplies length zero;
`Cons` increments a tail interval. Fresh bounds for an open parameter are
unknowns subject to the parameter's semantic context, not a concrete interval
asserted without justification. Carried BL annotations are obligations at all
nesting depths, not merely formatting or demands that overwrite an actual bound.

Recursive BL contracts need a separate, explicit rule: assume the declared
contract for recursive calls and prove each RHS meets its contract under those
assumptions. This is not permission for HM polymorphic recursion. Count-scheme
instantiation at recursive calls, unannotated recursive bounds inference,
count-variable scope/escape and constructor-field variance require design and
proof before acceptance; do not enable them through provisional dummy types.
Arbitrary recursive invariant inference is not a launch requirement.

## Required theorem targets

1. Typed artifact coherence: node monotypes and binder schemes correspond to
   the HM derivation; stripping the artifact recovers the source. Existing
   executable coverage checks alone are not proofs of these facts.
2. Arithmetic/structural checker soundness: successful checking establishes
   semantic inclusion, including application instantiation and residual goals.
3. Bounds-walk soundness: accepted node results have a declarative derivation;
   every carried annotation is checked in its actual scope.
4. Runtime interpretation: list intervals describe lengths of runtime values;
   substitution and reduction preserve the required semantic invariant.
   Higher-order closures and recursive contracts need suitable environments,
   not simply `BoundsTy.toTy` or HM-shape agreement.
5. Coverage soundness: accepted matches cover every reachable constructor under
   the current path assumptions and bounds, without requiring unreachable arms.
6. Report integrity: every supported logical node has a result keyed by its
   Core path; provenance joins distinguish source and generated nodes. Multiple
   Core occurrences of one source node must not be silently discarded.

Do not promise unrestricted BL completeness/principality. Define any such
theorem relative to an explicit supported fragment and inference/escape policy;
solver `unknown`, subtyping and recursive invariants make the HM statement an
inappropriate template.

## Checkpoints and acceptance gates

1. Semantic foundation: independent inclusion, strengthening and compatibility
   bridge. No new axioms or `sorry`; record inherited oracle dependencies.
2. Typed vertical slice: child `.found` types actually consumed, annotations
   checked, Core-path reports produced. Tests include an unannotated lambda and
   a nested annotation; unsupported forms fail explicitly.
3. Applications and schemes: sound shape specialization, count instantiation,
   residual discharge and escaping unknown policy; no `checkSubInst` shortcuts
   accepted merely because HM already unified.
4. Branches and recursion: one coverage authority, semantic path refinement,
   mutual-group contract checks and positive/negative `.fhm` regressions.
5. Product integration: replace legacy CLI `--bl`; BL editor reports consume
   the same artifact as HM. Delete obsolete sidecars only after parity tests.
6. Theorem campaign: complete the theorem family above and document remaining
   trust. Passing demos is not this checkpoint's acceptance criterion.

At semantic checkpoints run the default HM build, relevant optional Bounds
builds and the scratch HM audit. Do not widen this campaign to experimental
`BLSketch` or unrelated front-end changes just to make an aggregate build green.

## Implementation record

2026-09-13, checkpoint 1: added semantic subtyping with reflexivity,
transitivity and premise-strengthening, plus the legacy derivation bridge.
Added interval containment, semantic endpoint characterization and inclusion
composition to the arithmetic kernel. No executable BL acceptance behaviour
changed. Solver-free regression proofs cover widening, arrow variance,
strengthening, concrete containment and rejection of reverse widening. The
scratch HM audit remains 28 accepted / 8 expected rejections / 0 failures. The
typed bounds traversal and full soundness family remain pending.

2026-09-13, checkpoint 2: added `Bounds.Typed.walk`, consuming `.found` types at
every supported logical node. Successful results carry a derivation in the new
semantic `Derives` relation, a root-payload correspondence and HM-shape equality.
The derivation checks annotations on lambdas and monomorphic lets; arithmetic
obligations carry `SemanticSub` evidence. This is fragment-level static
soundness, not a runtime safety or full artifact-coherence theorem.

Supported: primitive literals, Nil/Cons chains, variables with monomorphic
bounds, unannotated scalar/type-variable lambdas, supported solid-annotated
parameters, and monomorphic binding uses. Bare List demand/phantom element
shapes use top information, not an exact origin. General application, fresh
List parameter origins, count holes, polymorphic annotations, recursive groups,
matches and arbitrary ADTs remain explicitly rejected. The inferred-scheme
map is not consumed yet; general polymorphic binding use is not supported.

`Found.synthNodes` joins each Core occurrence to its separate provenance and
checks report-path coverage/uniqueness. Saturated Cons scaffolding has validated
HM payloads and explicit report entries with no synthesized bounds; complete
per-node function bounds await the application/scheme checkpoint. These coverage
checks are executable guards, not a proved report-integrity family. CLI `--bl`
and editor behaviour are unchanged.

Validation: `lake build FHM FHMBounds` passes (751 jobs), all 13 typed-slice
regressions pass, and the scratch HM audit remains 28 accepted / 8 expected
rejections / 0 failures. New code contains no `sorry`, axioms or partial defs.
`walk` inherits `checkValid_sound`; the fragment derivation projection uses
only standard Lean axioms. The seven legacy BL proof placeholders remain.
