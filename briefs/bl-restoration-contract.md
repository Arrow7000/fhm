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

2026-09-13, checkpoint 3a: general monomorphic application now checks the
argument against the function domain with certified semantic subtyping and
retains the function result bounds. Primitive binary operators have their fixed
bounds spines. Tests cover scalar application, curried arithmetic, exact List
contracts and wrong-length rejection (16 regressions total). Count-scheme and HM
scheme instantiation remain separate pending work; no unification shortcuts or
unproved count substitutions were enabled.

2026-09-13, checkpoint 3b: `Bounds.Scheme` proves Boolean scheme well-formedness
soundness, executable `applyArgs` correspondence to `Count.Subst`/`BoundsTy.Subst`,
and `BScheme.instantiate?` soundness against `InstantiatesTo`. No solver axioms
are required. For finite count arguments, substitution commutes with evaluation
under the induced Nat assignment. `instantiateNat` carries substitution and
finite-argument evidence; it conservatively rejects arguments containing `inf`.
Literal infinity endpoints in scheme bodies remain legal. Seven executable
regressions cover finite/symbolic arguments, arity, binder scope and infinity.

Front-end scope audit: `lowerPolyAnn`/`lowerAnnList` in ordinary and
provenance-aware lowering do not thread `Binding.natBinders`. `lowerCountSolid`
explicitly maps an unresolved surface count name to rigid index 0 as a temporary
scaffold. Thus the typed artifact does not yet justify named count scopes or
quantification. The new typed annotation decoder now rejects symbolic counts
until their telescopes are preserved; all 17 typed-slice regressions pass.

Next design/proof checkpoint: preserve count telescopes by stable binder
identity without perturbing the proved HM `PolyTy`/D2 rules; establish count
scope, generalization, simultaneous HM/bounds scheme instantiation and escape
contracts. `Scheme` is a certified reusable foundation, not yet a wired
count-polymorphic walk. Recommend high reasoning for this interconnected step.

Validation after 3b: `lake build FHM FHMBounds` passes (754 jobs), the 17 typed
and seven scheme regressions pass, and the scratch HM audit is unchanged. No
new proof placeholders, axioms or partial definitions were added. Legacy CLI
behaviour remains untouched.

2026-09-13, checkpoint 3c: count telescopes now survive construction-time
provenance lowering in `Lowered.counts`, keyed by Core binder sites. Their
identities are injectively encoded from source ID, recursive member and count
parameter position, not reused local rigid indices. Nested scopes shadow by
name while captured outer identities remain unchanged. Compiler cloning and
rebasing move sites, not count identities; eliminated-arm metadata follows the
existing emitted-arm construction trace rather than being guessed afterwards.

Carried annotations resolve count names while they are lowered. Unresolved
names and duplicate count binders are retained as explicit BL problems; they
do not cause HM to reject a bounds-only error. `Found.synthNodes` rejects these
problems before checking. The legacy verified `lowerExpr` remains unchanged;
the provenance-aware front end now preserves this extra static information.

`Scope` proves count-ID injectivity, lexical membership transport under
renaming, count-evaluation transport and invariance of HM-erased types under
count renaming. These are not a complete formal correctness theorem for the
front-end name resolver or count metadata. Six executable regressions cover
member isolation, shadowing/capture, invalid-name HM blindness, duplicate
binders, identity-preserving rebasing and retention of distinct cloned sites.
Symbolic checking remains disabled
until the quantified scheme/generalization contract is proved and integrated.

2026-09-13, checkpoint 3d: `CountSubstitution` provides simultaneous substitution
of selected stable rigid identities, retaining captured identities and the
separate inferable namespace. For finite Nat replacements it proves evaluation
transport, validity transport (premises and goals together), semantic-subtyping
transport and unchanged HM type skeletons. None require solver axioms. Theorems
are deliberately about count substitution, not permission to generalize an
escaping unknown or to instantiate an unchecked recursive contract.

Four executable regressions and additional ordinary Lean proofs cover
capture retention, replacement assignments, namespace isolation, simultaneous
nonrecursive replacement and the unsoundness of leaving old premises behind.
Together with stable telescope preservation, these form the foundation for a
scoped quantified-bounds judgement. The old `BScheme` closed-binder format
alone is insufficient for arbitrary captured outer counts; do not silently
flatten those captures into the scheme's quantified slots.

Validation after 3d: `lake build FHM FHMBounds FHMEditorTests fhm` passes
(1703 jobs). All 34 executable BL regressions pass: 17 typed, seven closed
scheme, six front-end count-scope and four capture-safe substitution tests.
The rebuilt CLI's scratch HM audit remains 28 accepted / eight expected
rejections / zero unexpected failures; the unverified-boundary guard passes.
No new axioms, proof placeholders or partial definitions were introduced.

2026-09-13, checkpoint 3e: `ScopedScheme` distinguishes quantified stable
identities from captured lexical identities. Its guarded instantiation checks
unique quantifiers, disjoint captures, scope of the body and premises, arity,
finite Nat arguments, caller scope and capture availability. Successful results
carry proofs of caller-scoped bounds and premises, unchanged captures and
unchanged HM skeletons. Distinct uses instantiate independently.

Instantiation retains the substituted premises as obligations; it does not
establish them. `Instance.Usable` is a separate semantic call-site certificate,
with conservative `checkPremises` construction through the existing positive
validity oracle contract. `SemanticSub.assuming` and `Instance.useSubtype` prove
that discharged premises let transported subtype evidence be used under the
caller's assumptions. These transport theorems require no solver axioms;
only executable premise discharge inherits `checkValid_sound`.

Nineteen executable regressions plus ordinary Lean proofs cover captures,
independent instantiation, invalid interfaces and true/false call requirements.
This does not yet check an implementation against a declared scheme or consume
schemes in `Typed.walk`; count-polymorphic `.fhm` acceptance remains pending.

Validation after 3e: the full HM/Bounds/editor/CLI build passes (1705 jobs),
all 53 executable BL regressions pass, and the scratch HM audit and boundary
guard remain unchanged. No new axioms, placeholders or partial defs were added.

2026-09-13, checkpoint 3f: `ScopedAnnotation.decode` reads carried solid counts
in an explicit lexical scope and produces proof-carrying bounds demands with
exact HM-erased skeleton equality. It traverses arrows, nested lists and data
arguments, rejects holes and unresolved/inferable lexical counts, and treats
bare List as a top interval. `contract` checks the explicit quantified/captured
interface and premise scope; neither API establishes RHS conformance.

Eighteen executable regressions and two construction-trace regressions exercise
the bridge from lowering through `.found` inference to scoped contract decoding
and instantiation, including nested shadowing with retained outer captures.
All new decoding/shape proofs require only standard Lean axioms. The existing
ground-only `Typed.walk` annotation policy and legacy CLI acceptance are unchanged.

HM specialization warning: legacy `BoundsTy.instTyArgs` replaces both `.bvar`
and `.fvar` by indexing the supplied type arguments. Free inference identities
are not scheme-slot indices. Likewise `fvarsToBVars` is not valid abstraction
without a witnessed binder-slot map. Do not reuse either operation in the new
scheme-use path; preserve captured HM fvars and specialize only bound slots.

Validation after 3f: the full build passes (1707 jobs); all 73 executable BL
regressions pass. The default HM stack is unchanged, the last rebuilt CLI scratch
audit remains clean, and no axioms, placeholders or partial defs were introduced.

2026-09-13, checkpoint 3g: `TypeSubstitution` specializes only HM `.bvar`
slots, preserves free HM identities and inserts the full supplied bounds rather
than a shape-only template. It proves HM skeleton correspondence, semantic
subtyping and caller count-scope preservation. Combined specialization replaces
scheme counts before inserting caller type arguments, leaving the counts inside
those arguments untouched even when their numeric identities overlap.

`found_shape` proves exact correspondence to an HM scheme-instantiation witness,
not merely structural resemblance to a guessed type. Ten executable regressions
and ordinary Lean proofs cover free captures, simultaneous replacement, nested
bounds, substitution ordering, variance and an exact HM instance. All transport
and correspondence theorems require only standard Lean axioms.

Still pending: extract the actual inferred binder-slot abstraction and HM
instantiation witnesses from the artifact, justify argument bounds in the
typing environment, check declared RHS contracts, and consume these certificates
in scheme-aware `Typed.walk` rules. This checkpoint does not enable unrestricted
polymorphic binding use or count-polymorphic recursion on its own.

Validation after 3g: `lake build FHM FHMBounds FHMEditorTests fhm` passes
(1709 jobs), all 83 executable BL regressions pass, and the fresh scratch audit
is 28 accepted / eight expected rejections / zero failures. The unverified
boundary guard and diff whitespace checks pass. No new proof placeholders,
axioms or partial defs were introduced; the seven legacy BL placeholders and
existing positive-oracle trust boundary remain unchanged.

2026-09-13, checkpoint 3h: `BinderBridge` connects inferred binder schemes to
actual bounds monotypes and `.found` uses. Structural matching only proposes
arguments; accepted instances carry a complete `InstantiatesBy` witness and
checked arity/scope. Repeated slots must agree and free HM captures must match
exactly. Unused slots have explicit Unit witnesses, never out-of-range defaults.

Abstraction recovers an injective generalized free-identity pool from the
certified opening, checks freshness against a supplied captured type interface,
and proves its closed bounds body has exactly the inferred scheme's erased HM
skeleton. Closing preserves count scope and never changes count payloads.
`use_shape` joins the checked abstraction and use certificates to the combined
specialization theorem. None of these proofs require solver axioms.

Artifact-backed `Typed.walk` now consumes `FoundResult.binderSchemes` at every
unannotated let. It requires exactly one fact at the exact Core site and includes
environment types and source annotation identities in the captured interface.
Annotated declarations remain separate: the existing HM artifact deliberately
does not emit inferred facts for them. Hand-built standalone fragment tests can
still omit the map. The existing bounds derivation remains authoritative; no
new polymorphic variable rule is assumed. A depth-aligned restriction tracks
generalized binders and reports unsupported polymorphic uses specifically,
without confusing shadowing lambda parameters or monomorphic lets with them.

Twenty-four bridge regressions and fourteen artifact/traversal regressions cover
repeated slots, captures, count/type namespace isolation, invalid metadata,
compiler clones, source annotation freshness, de Bruijn shadowing and the
explicit polymorphic-use boundary. This is not a complete formal artifact
coherence theorem. Abstraction with enclosing HM bound slots remains explicitly
unsupported, and count-polymorphic expression checking is still pending.

Next theorem/implementation target: bounds derivation transport under fresh HM
free-type substitutions, followed by a genuine generalized-RHS judgement and
scheme-aware variable/let rules. Only then should checked abstractions enable
polymorphic uses. Declared count contracts subsequently need directed RHS
checking and the separate simultaneous recursive-contract rule.

Validation after 3h: `lake build FHM FHMBounds FHMEditorTests fhm` passes
(1711 jobs); all 121 executable BL regressions pass. The fresh scratch HM audit
is unchanged at 28 accepted / eight expected rejections / zero failures. The
unverified-boundary guard and diff checks pass; no new axioms, placeholders or
partial definitions were introduced. HM inference, D2 rules, Path R and the
legacy CLI `--bl` launch boundary are unchanged.

2026-09-14, checkpoint 3i: `Generalization` proves free-HM substitution transport
for the current `Typed.Derives` fragment. A generalized identity can be replaced
by complete caller bounds, including structured list bounds, while semantic
subtyping is transported and all count payloads remain unchanged. Source
annotations must be fresh; successful decoding preserves that freshness and
therefore leaves carried demands fixed. Captured environment types must also
be fresh to obtain a universal RHS fact in the unchanged environment.

`GeneralizedRHS` records universality for left-to-right free substitutions drawn
from the generalized pool. `fromBinder` derives it from the actual checked
`BinderBridge.Abstraction` freshness interface and a fragment RHS derivation.
This is a typing theorem, not merely HM skeleton agreement. Sequential free
substitution is explicitly distinct from simultaneous bound-slot specialization;
the exact closed-scheme specialization bridge remains to be proved before use.

Twelve executable regressions and ordinary Lean proofs cover structured caller
bounds, namespaces, nested type arguments, sequential substitution, captured
environment exclusion and source-annotation exclusion. All new theorem targets
depend only on standard Lean axioms, not the positive solver oracle.

Still pending: scheme-aware bounds environments, variable/let typing and
executable rules, transport/generalization for that enlarged judgement, and the
exact correspondence from RHS specialization to the closed scheme's caller
instance. No polymorphic-use acceptance has been enabled; the legacy CLI/LSP
BL boundary remains unchanged. Count generalization, caller count scope and
recursive contract checking are separate subsequent obligations.

Validation after 3i: `lake build FHM FHMBounds FHMEditorTests fhm` passes
(1713 jobs), including all 133 executable BL component/adapter regressions.
The fresh scratch HM audit remains 28 accepted / eight expected rejections /
zero failures. The unverified-boundary guard and diff whitespace checks pass.
No new axioms, placeholders or partial definitions were introduced.

2026-09-14, checkpoint 3j: `SchemeSpecialization` closes the exact RHS-to-closed-
scheme bridge. Simultaneous free-identity mapping transports the current bounds
typing fragment while fixing source annotations and captures. On locally closed
RHS bounds, mapping the generalized identities is exactly bound-slot
specialization of the checked closed scheme. Caller arguments are inserted
without respecializing their own free identities, even when these overlap the
generalized pool; no caller/generalized disjointness assumption is needed.

`checked_use` joins that RHS typing theorem with the actual HM use witness and
proves exact final `.found` skeleton agreement. `caller_scope` separately
transports explicit caller count scope. All new proofs are solver-independent.
Twelve executable regressions and ordinary Lean proofs include the concrete
collision where sequential replacement would incorrectly rewrite a caller's
type argument. The sequential theorem from 3i remains valid but is not used as
the simultaneous scheme-use bridge.

Validation after 3j: the full HM/Bounds/editor/CLI build passes (1715 jobs), with
145 executable BL component/adapter regressions. Boundary and whitespace guards
pass. No polymorphic-use acceptance, new axioms, placeholders or partial defs
have been introduced. The next step is a checked executable use certificate,
followed by scheme-aware environment/variable/let rules and their expanded
judgement transport; count-polymorphic contracts remain separate work.

2026-09-14, checkpoint 3k: `SchemeUse.check` constructs an executable use
certificate from a checked binder abstraction, its RHS typing derivation,
actual supplied bounds arguments and final HM use type. The full argument
vector must match the independently checked HM instance; missing, extra,
inconsistent or differently shaped arguments are rejected. Caller arguments
must be locally closed, and both supplied counts and captured RHS counts must
be available in the explicit caller scope. Inferable counts are not lexical
captures. Successful output carries RHS typing, exact final HM shape and count
scope proofs, all independent of solver axioms.

This API does not invent bounds arguments or prove that caller arguments
describe an expression's actual value; the consuming application rule must
establish argument-origin typing. No scheme-aware variable/let rule or CLI/LSP
acceptance is enabled by this helper alone.

Validation after 3k: the full build passes (1717 jobs), including 159 BL
component/adapter executable regressions and ordinary Lean proof examples.
The fresh scratch audit remains 28 accepted / eight expected rejections / zero
failures. Boundary and whitespace guards pass; no new axioms, placeholders or
partial definitions were added.
