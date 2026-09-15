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

### Metatheory-first closure order (2026-09-14)

The final goal is a verified, usable BL layer, not a demo-first release. The
earlier numbered checkpoints do not authorize postponing the central runtime
argument until after product integration. The active closure order is:

1. Fix the runtime target in `Runtime`: concrete erased values/reductions,
   higher-order meanings, permitted divergence, and explicit supported nominal
   data. Prove semantic subtyping includes those meanings.
2. Prove compatibility and the fundamental theorem for the ordinary rules
   shared by `RecursiveHMJudgement.ScopedDerives` and
   `RecursiveHMUniform.BodyDerives`. Closing environments must justify actual
   variable denotations; static HM-shape agreement is not that justification.
3. Extend the fundamental theorem to count/HM scheme instantiation and ALL-member
   recursive contracts using finite observation budgets. This must justify the
   existing `SmallStep.Step.letRecUnfold`, not invent alternative execution.
4. Assemble generalized locals, enclosing bindings and nested groups into one
   canonical whole-program route, extending its semantic proof at each rule.
   No parallel walker generation solely to avoid the common-scope obligation.
5. Establish the HM-artifact and source/report coherence bridges and expose the
   same checked whole-program route to CLI/LSP. Retire superseded engines after
   proof/regression parity; provide an explicit test entry point.

Deferred callback inference is an eventual supported-language obligation, but
further inference conveniences must not displace these closure gates. Explicit
annotations may exercise a sound fragment without falsely claiming the missing
inference is implemented. Arbitrary recursive invariant inference and
unrestricted BL completeness/principality remain outside the promised target.

`Runtime.Supported` initially permits primitives, HM variables, arrows, Lists
and Bool. Arbitrary nominal datatypes need justified constructor-field variance;
the structural `SemanticSub.custom` rule is not sufficient runtime evidence for
a negative occurrence of a type parameter. This is an explicit theorem boundary,
not permission to silently change the supported language or HM semantics.

Current runtime bridge: `Runtime.subtype` proves value-meaning inclusion;
`ValueAt.down`/`TermAt.down` prove finite-budget weakening under valid semantic
type environments; `Safe.step`, `Safe.progress` and `Safe.list_length` give
observable consequences of the runtime target. These use only standard Lean
axioms. These consequences alone do NOT establish that accepted checker
artifacts imply `Safe`; group introduction and the artifact bridge remain
required before claiming end-to-end BL safety.

Runtime compatibility now covers ordinary application at the SAME finite
budget, beta/lambda introduction, literal/Nil/Cons value meanings and Cons
evaluation, and List/Bool matching through the actual first selected branch and
actual `substN` contents. `TermAt.prepend` and `TermAt.bind` reuse existing Core
step determinism and congruence, not new execution rules. The lambda body is
required safe at a strictly smaller budget, leaving room for the recursive
fundamental argument.

`ValueAt.counts`/`TermAt.counts` connect count substitution to assignments;
`ValueAt.types`/`TermAt.types` connect simultaneous full HM substitution to its
semantic environment. Combined `specialize` explicitly freezes inserted full
caller type meanings at the CALLER count assignment before interpreting the
callee's count telescope. Kernel-checked examples prove identity preserves any
full type meaning and refute both nonempty-Nil claims and a callback whose actual
beta reduct drops a singleton to Nil. These are proofs, not PASS/FAIL printing.

The ordinary RHS fundamental theorem is now
`ScopedDerives.RuntimeReady.termAt`: the existing supported derivation, established
path premises and a realizing `EnvAt` imply safety of the actual closed term at
every finite budget. It covers all ordinary RHS rules, including call-by-name
`let`, higher-order application and refined List/Bool matches. `safeClosed`
discharges the environment obligation for closed ordinary terms. `RuntimeReady`
is proof metadata indexed by the existing derivation, not another checker or
language acceptance judgment; it records supported INTERMEDIATE types as well
as the root. A kernel fixture derives the safety of a List-tail function from
its actual Nil/Cons typing derivation.

`firstMatch_unclose` recovers the original selected branch after capture closing;
coverage and first-match precedence survive closing. `EnvAt.listBranch` derives
Nil/Cons arithmetic refinements from concrete lengths and constructs the exact
head-first/tail-second branch environment. `closing_compose` then identifies
branch reduction with that combined closing substitution. Recursive variables
are still conditional on a REALIZING environment: ALL-member cyclic environment
construction and scheme/group introduction remain the next fundamental-proof
obligations. The checker/artifact bridge must also establish readiness throughout
its supported fragment; a supported root alone is insufficient. No CLI/LSP
acceptance was enabled.

Validation of the runtime compatibility/specialization batch:
`lake build FHM FHMBounds fhm` passes (1806 jobs). Every displayed runtime theorem
dependency uses only standard Lean axioms, without the arithmetic oracle or
`sorryAx`; there are no new axioms, placeholders or partial definitions. The HM
audit remains 36 files / 28 accepted / eight expected rejects / zero failures.

All four primitive operators now satisfy their runtime arrow meanings through
the actual Core delta rules, including partially applied functions and saturated
Bool comparisons. `ScopedDerives.varsBelow` proves lexical scope directly from
the existing RHS derivation, with exact two-field Cons and zero-field Bool branch
opening. Neither proof adds another typing judgment or acceptance engine.

`Runtime.closing_compose` proves that closing outer captures then substituting
local contents equals one combined Core substitution, including beneath match
binders and mutual groups. `Runtime.closing_scoped` proves the actual substituted
term retains exactly the remaining lexical scope. Inserted terms must be closed;
neither scope nor capture avoidance is asserted from HM-shape agreement.

`RecursiveHMJudgement.EnvAt` now gives one closing environment for the existing
RHS judgment. Mono entries denote actual safe terms; recursive entries denote
safe terms at every checked count instance whose RAW instantiated premises hold
at the actual assignment. The predicate is independent of the ambient static
path context, so branch refinement does not accidentally weaken an assumption's
runtime contract. Budget weakening and mono extension are checked constructions;
`EnvAt.varMono` and `EnvAt.varRecursive` prove the actual closing substitution
sound for both variable rules. Recursive use obtains its raw premises from
`used.usable` and established caller premises, never by appending requirements.

The simultaneous runtime closure lemma is now `EnvAt.tieGroup`: induction on
observation budget constructs ALL Core recursive replacement terms in one
realizing environment, including genuine mutual cycles. `RuntimeReady.safeGroup`
uses it and the ordinary fundamental theorem to prove actual erased group-body
safety after the single Core `letRecUnfold` step. The premise still requires
every actual RHS to establish its `BindingAt` obligation under a realizing
environment; it is not an assumption that the cyclic replacement terms already
obey their annotations. Kernel fixtures cover a genuinely cyclic recursive
count contract (divergent, therefore no fabricated termination claim) and a
two-member dependency whose second RHS returns Nil.

Readiness now transports through established caller/path assumptions, count
specialization and full HM specialization (`RuntimeReady.assuming`, `.counts`,
`.types`). `RecursiveHMUniform.fromCertified_runtimeReady` connects those facts
to the ACTUAL existing count-first/full-HM-second member certificate constructor;
`Result.termAt` derives its demand-bound runtime behaviour under a realizing
environment. A kernel fixture checks a recursive lambda at every supported
full-HM/count specialization, preserving nested caller counts.

The gate-3 assembly below discharges ALL members in source order, realizes
generalized exports and connects `BodyDerives`.
Readiness of the original supported checker proofs must also be established.
The cyclic closure lemma is not by itself a theorem that the current
whole-artifact checker is runtime-sound.

The ALL-member fixed-HM runtime environment assembly is now
`HMDeclaredGroup.Checked.runtimeEnvironment`. It consumes readiness and supported
demands for every original member, specializes each actual certificate at its
checked recursive count use, and ties the whole group with one common full HM
map. Caller-scope weakening accommodates shared arguments whose counts one
member does not use; it changes neither instance bounds nor raw premises.
`MemberChecked.demandAtRecursiveUse` proves the specialized implementation demand
is exactly that use's fixed-vector bounds.

The source-order bridge is total `CheckedMembers.memberAt` plus
`Members.memberAt`, keeping the actual certificate, generalized export and fixed
recursive contract together. `Checked.memberRhs`/`memberAtRhs` identify its exact
original `.found` RHS using verified Core-path composition, and `rhssScoped`
obtains ALL actual erased RHS scope proofs from the checked member derivations.
The certificate constructor now preserves source/template/opening data directly;
only proof fields requiring environment equality are transported. This removes
an opaque whole-certificate cast without changing language acceptance.

Generalized exit implementation safety is now `Checked.exportedMemberSafe`:
every supported complete full-HM/count exit use denotes the same actual erased
recursive implementation. `exitMapFixed` protects ALL recursive templates' free
captures, `exitMapVector` recovers exactly the caller vector (including unused
forall slots), and `fixedExitUse_bounds` proves that the induced fixed in-group
use has exactly the exit bounds. Different exit uses may choose different maps;
within each recursive implementation proof the whole group has ONE common map.
`EnvAt.recursiveMemberSafe` turns the realized environment into actual wrapped-RHS
safety, not just a safe variable lookup. These proofs use only standard Lean
axioms, without the arithmetic oracle or placeholders.

The generalized-body runtime environment is now `BodyEnvAt`, with
`Checked.exportEnvironment` realizing ALL source-ordered exits by the original
Core recursive replacements. Each exported entry promises every complete
supported HM/count instance; supporting unused HM arguments is explicit too.
`BodyDerives.varsBelow` proves actual scope, including closed group introduction.
`BodyEnvAt.listBranch` preserves generalized exports behind the concrete List
fields and derives arithmetic branch premises from their observed lengths.

`BodyDerives.RuntimeReady.termAt` now proves the fundamental theorem for ALL
existing supported body rules: primitives, constructors, mono/generalized uses,
applications, lambdas, call-by-name mono locals, List/Bool matches and CLOSED
recursive-group introduction. The group case constructs the export environment
from original member certificates; it does not assume recursive annotation
soundness. `safeClosed` gives safety of the exact erased body/program. A kernel
fixture calls the same proved generalized identity at Int and Char across a
local binder. These theorems require source-member and intermediate-type
readiness, not merely a supported root; their dependencies exclude the
arithmetic oracle and `sorryAx`.

The existing canonical RHS/body traversals now BUILD runtime readiness while
building their original static derivations. `ScopedResult.runtimeReady`,
exact-node `TypedChecked.runtimeReady` and `BodyResult.runtimeReady` carry an
optional proof witness. Application/constructor/local/branch assembly consumes
the actual child witnesses; no proof is inferred from root support alone.
`MemberChecked.runtimeReady` transports the original RHS witness through the
existing common-environment reconciliation, and `CheckedMembers.runtimeReady`
collects ALL original member witnesses and supported declaration demands.
Closed group checking uses those and the real body witness to construct the
group's readiness. `BodyResult.runtimeSafety?` extracts the resulting theorem
for the EXACT erased input artifact and inferred bounds.

`Runtime.supported?` is a total proof-producing check for the current runtime
type fragment, with completeness proved for `Runtime.Supported`; unsupported
cases simply have no witness. Static acceptance is unchanged, and CLI/LSP
production is still guarded. Regression gates require runtime theorem witnesses
for actual Int/Char exit uses, full/mutual/deferred recursive spines and List/Bool
matches. A negative gate checks that a supported Int root with an unsupported
intermediate custom-type domain does NOT get a runtime witness.

This closes supported runtime readiness at the canonical CLOSED-root
checker/report boundary, not the remaining mixed-scope/nested-group language
rules. The existing static arithmetic-validity oracle remains a separate trust
boundary; the new runtime theorem/extraction code adds no oracle or proof hole.
`ScopedBodyDerives` is now the same body judgment indexed by separate free-HM
and lexical-slot interpretations, plus its count identities/rows. These are
indices, not fixed inductive parameters: later local generalization must allow
an RHS to be checked in its own argument/count frame without creating a second
body language. `BodyDerives` remains the identity-interpreted compatibility
view used by the current checker. Scope, premise transport and the entire
runtime fundamental theorem have been generalized in place. A kernel fixture
proves actual annotated lexical/captured interfaces safe at arbitrary supported
full types, leaving both written source annotations unchanged.

`RuntimeReady.assuming` and `BodyResult.assuming` preserve proof witnesses under
established path premises, including all member evidence and complete HM
vectors. Report bounds, original nodes and presence of runtime proof evidence
are unchanged. This enables scope/path assembly; it does NOT yet license or
enable generalized local lets, enclosing captures or nested groups in the checker.

The metatheory now has `ScopedBodyDerives.letExported`: local generalization
requires actual RHS derivations at EVERY full HM/count use, checked in the
local's argument/count frame. The original outer premises are preserved and
combined with RAW instance premises; requirements are not appended to caller
assumptions. Written local annotations must retain the exact decoded declared
scheme through `LocalAnnotationOK`. The scope premise applies to the original
RHS. `LocalFrame` requires fresh, distinct owned HM identities and fresh owned
count identities, with count captures scoped in the parent. The canonical
`localTypes` interpretation preserves captured source identities; `localSlots`
preserves parent lexical slots beyond the local annotation telescope. Arbitrary
RHS interpreter functions are not accepted. Kernel preservation fixtures check
both capture boundaries. The runtime fundamental theorem constructs the generalized local's meaning
from these derivations and its captured closing environment before the actual
Core call-by-name let step. Runtime readiness and premise transport cover this
rule too. No generalized runtime contract is postulated.

A kernel fixture introduces a written polymorphic identity with an actual
lexically annotated RHS, then uses it at Int and Char across another local
binder. The SAME Core fixture also passes real HM inference. Constant-to-Char
RHS derivations are formally impossible, and the HM regression rejects
`forall a. a = 1` even when unused. These are proof/specification checkpoints:
the executable local checker must still CONSTRUCT those universal certificates
from the existing source-site scheme facts and count/HM transports. Generalized
locals therefore remain explicitly guarded in production; no demo shortcut or
new acceptance engine was enabled.

Ordinary `ScopedDerives` RHS proofs and their complete runtime readiness now
embed into this SAME scoped body judgment in mono captured environments,
including annotated scopes and List/Bool branch refinements. Fixed recursive
assumptions are explicitly excluded from this bridge; no universal export is
inferred from them. The polymorphic-local kernel fixture now reuses ordinary
RHS proofs through this bridge rather than constructing a parallel body proof.
Semantic `subsumption` retains the actual implementation derivation alongside
its independent demand inclusion. The runtime theorem transports actual bounds
to demand bounds, requiring supported types on both sides. A kernel Nil fixture
checks genuine interval widening, and literal-type preservation still proves
that Int implementations cannot satisfy Char demands. This is the proof reuse
needed to consume existing count-first/full-HM-second RHS certificates at local
introduction, not an executable generalized-local acceptance shortcut.

`localRhsInstances` now eliminates ONE ordinary opaque-opening certificate into
EVERY actual full HM/count use required by local introduction, in the initial
closed term-capture slice. It transports source counts first, inserts full HM
arguments second, independently weakens actual implementation bounds to the
declared demand, and preserves outer path premises without assuming caller
requirements. `localRhsInstances_runtimeReady` transports the corresponding
runtime proof witnesses. `LocalFrame.slotsFit`, `localSlots_specialize` and
`localTypes_specialize` reconcile this transport with the capture-preserving
local frame. The polymorphic identity fixture now checks one opaque RHS proof
and derives all Int/Char uses through this shared certificate eliminator.
A kernel regression retains a caller count inside a complete type argument even
when the source count telescope substitutes the same numeric identity.

The certificate must still be assembled from exact source-site reconciliation:
its source interpreter and annotation-slot interface have to be reconciled with
the canonical local frame, and original reports must be retained. The ordinary
mono-capture proof bridge is available, but this eliminator does not yet handle
nonempty captured term environments or generalized captures. Production local
guards therefore remain unchanged.

Free source-reader reconciliation is now proved through the ordinary RHS
judgment and all runtime readiness cases. `ScopedHMInterpretation.congrFree`
and bounds-erasure membership preservation establish that reader changes
outside carried annotation identities are irrelevant. Source obligations and
`ScopedDerives.sourceFree` preserve the exact expression, implementation bounds,
environment and count frames; readiness transport includes refined List/Bool
arms. `RecursiveHMUniversal.Certified.sourceFree` retains the original opaque
opening, actual implementation and independent demand inclusion. It explicitly
does NOT assert a new found-artifact interpretation.

The actual source-site reconciliation proves `Checked.sourceIdentity` using
its existing protected annotation identities. `HMDeclaredRHS.certifySource`
therefore recovers the canonical free source reader from checked RHS evidence,
not metadata alone. Real declared-RHS regressions require supported readiness
and transport it through this reconciliation, retaining the same actual bounds
and opening identities. A named-source fixture checks that solving unrelated
artifact identity 65 leaves source annotation identity 90 unchanged.

Next at this boundary: lexical-slot reconciliation with the canonical local
frame and exact report retention, followed by nonempty/generalized captured
term environments and nested groups. Executable generalized-local acceptance
remains guarded until this assembly is proved and exercised end to end.

Next: generalized locals, enclosing bindings and nested groups, then the general
artifact/report bridge and CLI/LSP migration. No whole-language BL runtime
soundness or BL LSP support is claimed yet.

Closing-environment validation: full `lake build FHM FHMBounds fhm` passes
(1806 jobs), including all existing Bounds regression gates. Scope, primitive,
closing and variable-realization proofs use only standard Lean axioms; no new
oracle axioms, placeholders or partial definitions. Boundary/whitespace pass.

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

2026-09-14, checkpoint 3l: `SchemeTyping` adds explicit monomorphic/polymorphic
environment entries and declarative variable/let rules. Scheme bodies have
checked HM shape and well-formedness. Polymorphic let introduction requires a
universally typed RHS; `let_fromBinder` supplies that premise from the existing
certified fragment RHS theorem. `ofMonomorphic` embeds the old judgement without
changing its bounds, and `instance_shape` proves every permitted scheme instance
is an actual relational HM opening. A formal example types one identity binding
at Int and Char across an intervening monomorphic let; lambda parameters remain
monomorphic. Annotated polymorphic declarations are not enabled.

`SchemeVariable.check` implements the exact de Bruijn variable rule with supplied
bounds arguments, final `.found` HM shape, count scope and local-closure checks.
Successful output carries a derivation of the enlarged judgement. Its environment
is an assumption: only a sound environment-introduction rule can justify stored
schemes. This does not certify externally invented schemes as source facts or
wire the main traversal/CLI/LSP to the new judgement.

Validation after 3l: the full build passes (1721 jobs), with 181 BL executable
component/adapter regressions plus formal examples. All new theorem/checker
targets require only standard Lean axioms. Boundary and whitespace guards pass;
no new axioms, placeholders or partial definitions were added. Generalization
transport for RHSs in mixed scheme environments and origin-backed application
argument selection remain pending before general traversal acceptance.

2026-09-14, checkpoint 3m: `SchemeApplication.check` implements an origin-backed
polymorphic application slice for a function whose domain is its sole HM slot.
The argument's existing scheme-aware bounds derivation supplies the complete
slot bounds; no HM-shape reconstruction or interval guess is used. Variable use
certificates now identify the exact selected environment entry and specialized
bounds, not just the erased shape. Successful application output carries its
declarative derivation, exact result HM payload agreement and caller count scope.
The direct-domain application subtype premise is reflexivity, requiring no
solver axiom. Other arities and structural slot inference fail explicitly.

Twelve executable regressions cover Int/Char uses, exact Nil and singleton Cons
origins, symbolic captured argument bounds, caller scope, shadowing depth,
callee/result payload mismatches and explicit unsupported cases. This is a
checker component, not general `.fhm` traversal acceptance or LSP integration.
Universal RHS typing in mixed scheme environments remains the next proof target;
its transport must preserve arbitrary caller arguments without accidentally
substituting captured HM identities into those inserted arguments.

Validation after 3m: the full HM/Bounds/editor/CLI build passes (1723 jobs), with
193 executable BL component/adapter regressions. The fresh scratch HM audit is
28 accepted / eight expected rejections / zero failures. Boundary and whitespace
guards pass. All new checker/theorem targets are solver-independent; no new
axioms, placeholders or partial definitions were introduced.

2026-09-14, checkpoint 3n: `FreeAlgebra` and `SchemeTransport` close full free-HM
substitution transport for the enlarged scheme-aware judgement. This includes
polymorphic uses in RHSs and nested polymorphic lets. At a nested universal RHS,
the proof first opens its slots at a finite fresh identity block, protects those
placeholders while transporting captures, then simultaneously specializes them
to arbitrary locally closed caller bounds. Caller identities need not be
disjoint from generalized or placeholder identities. The proof recurses on
source term size, not on the potentially repeated universal derivations.

`SchemeTransport.binder_instances` and `let_fromBinder` now establish artifact-
certified generalization in arbitrary mixed bounds environments. Their capture
interface uses a monotype for monomorphic entries and the stored closed HM body
for polymorphic entries; bound slots are not misclassified as free captures.
Stored scheme HM metadata is explicitly canonical/bounds-blind (`σ.eraseBounds`),
while its bounds body retains counts and source annotations stay in the term.
This makes identity environment transport exact rather than an unproved quotient
over equivalent metadata. No executable HM inference or Path R rule changed.

The LC side condition is essential: non-LC free replacements can be captured by
later bound-slot substitution. The commutation/congruence and well-formedness
lemmas prove the required boundaries. Eight executable regressions and formal
examples exercise a genuinely mixed RHS, a nested polymorphic let, and the
critical instance where an outer captured fvar7 becomes a bounded List but a
caller-provided slot fvar7 must remain fvar7. All new theorem targets require only
standard Lean axioms, without solver trust or proof placeholders.

Validation after 3n: the full HM/Bounds/editor/CLI build passes (1726 jobs), with
201 executable BL component/adapter regressions. Boundary and whitespace guards
pass. The main typed traversal and CLI/LSP launch boundary remain unchanged;
integrating these universal premises into a scheme-aware traversal is next.

2026-09-14, checkpoint 3o: `SchemeWalk.walk` consumes final found artifacts and
mandatory exact-site machine binder facts. Unannotated generalized lets use the
mixed-environment universal RHS proof from 3n, rather than treating successful
syntactic abstraction as permission to generalize. Monomorphic uses, supported
annotations, literals, Nil/Cons, lambdas and applications retain proof-carrying
semantic checks. Direct sole-slot polymorphic applications use the argument's
certified bounds, preserving concrete list origins through identity calls.

`SchemeFound.synthNodes` is an opt-in adapter joining this traversal to existing
provenance with coverage/uniqueness guards. Its successful result carries a
declarative scheme-aware derivation, root HM shape and count scope. These guards
are not full formal artifact/report coherence. Constructor scaffolding retains
explicit bounds-free reports. CLI/editor launch routes have not been switched.

Fifteen executable regressions use actual HM inference artifacts, including
Int/Char uses of one generalized binding, mixed and nested generalized RHSs,
exact Nil/Cons lengths, shadowing, missing/duplicate binder facts, incorrect
callee payloads, positive/negative nested List annotations and a surface
inference/provenance join. Standalone polymorphic uses, polymorphic annotations,
structural/multiple-slot polymorphic applications, count contracts/holes, fresh
open List parameters, matches and recursive groups remain explicitly deferred.

Validation after 3o: the full HM/Bounds/editor/CLI build passes (1729 jobs), with
216 executable BL component/adapter regressions. The fresh scratch HM audit is
28 accepted / eight expected rejections / zero failures. Boundary and whitespace
guards pass. No new axioms, proof placeholders or partial definitions were added.
The walk inherits only the established positive solver trust for inclusion;
its derivation projection requires standard Lean axioms only. HM and Path R are
unchanged. Structural origin-backed applications are the next component target.

2026-09-14, checkpoint 3p: `StructuralApplication.check` proposes HM-slot bounds
from the certified argument's structural bounds. Exact `SchemeVariable.check`
evidence validates the complete HM instance, local closure and caller count
scope; semantic subtyping separately proves argument inclusion in the opened
domain. Successful applications carry both the callee typing and application
typing. The traversal now reports the specialized callee domain, not the
potentially narrower argument bounds as though they were the function domain.

The component supports nested List and arrow slots and multiple HM slots.
Repeated occurrences select one origin-backed proposal and validate all uses;
there is no join-search or claim of completeness. Slots absent from the domain
receive an explicit Unit witness, accepted only if it agrees with the entire
found HM instance. Other missing slot bounds fail rather than being fabricated
from a result's HM shape. Quantified count contracts remain separate work.

Eleven component regressions cover nested origins, multiple/repeated slots,
interval rejection, arrow variance, missing-slot policy and count/LC guards.
Two additional actual-inference traversal regressions exercise a two-slot
curried constant with an unused Unit slot and conservative rejection for Int.
The component's structural capabilities do not mean arbitrary structural source
functions now pass: general unannotated List/higher-order parameter introduction
and standalone polymorphic values are still unsupported, as are polymorphic
annotations, holes, count contracts, matches and recursion. CLI/LSP remain on
their existing paths; no runtime or full artifact-coherence result is claimed.

Validation after 3p: full HM/Bounds/editor/CLI build passes (1731 jobs), with 229
BL component/adapter regressions. Fresh scratch HM audit: 28 accepted / eight
expected rejections / zero failures. Boundary and whitespace checks pass. No new
axioms, placeholders or partial definitions; inclusion retains the established
positive solver trust. HM metatheory and Path R are unchanged.

2026-09-14, checkpoint 3q: `CountTransport.transport` proves simultaneous finite
selected count substitution for the full mixed-scheme fragment judgement,
including nested polymorphic lets. Path conditions, bounds environments and
existing use arguments are transported together. At a universal RHS, fresh HM
placeholders are transported first and arbitrary caller bounds inserted only
afterwards. Caller counts overlapping quantified/captured identities are not
accidentally rewritten. HM scheme metadata remains exactly unchanged.

`assuming` transports entire mixed derivations when caller assumptions imply
the old premises; instantiated requirements are never simply asserted as facts.
Scope-based fixed-environment lemmas keep explicit captured counts untouched.
Ground annotation demands are proved fixed under selected substitution. This
does not yet change the ground-only annotation judgement or enable quantified
declaration checking; it supplies the safe transport boundary for certified
count-contract uses. Finiteness is essential for Nat assignment semantics, with
an explicit infinite-replacement counterexample in the formal regressions.

Eight executable regressions and formal collision/nested-let/annotation proofs
pass. Full HM/Bounds/editor/CLI build: 1733 jobs, 237 BL regressions. Fresh scratch
HM audit: 28 accepted / eight expected rejections / zero failures. Boundary and
whitespace checks pass. New proof targets use standard Lean axioms only, with
no positive-solver dependency, new axioms, placeholders or partial definitions.
HM/Path R and CLI/LSP routes are unchanged.

2026-09-14, checkpoint 3r: `CountContract.Certified` separates an RHS-certified
HM/count contract from merely decoded annotation metadata. It requires exact
body agreement, a well-scoped count telescope, an environment containing only
explicit captured counts, and universal RHS typing at its HM scheme. Quantified
count substitution is proved to leave that captured environment unchanged.

`CountContract.use` and executable `check` specialize a certified declaration's
counts before inserting arbitrary caller HM-slot bounds. The call independently
checks count arity/finiteness/scope, retained captures, instantiated premises,
the complete relational HM instance, slot local closure and slot count scope.
Successful results carry the specialized RHS derivation, final HM shape and
caller count scope. No shape-only List arguments or unproved premises are used.
Origin typing for supplied HM bounds remains the consuming application's duty.

Nineteen executable regressions use formal implementation certificates, not
invented production binder maps. They exercise independent uses, caller count
collisions, symbolic scope, finite Nat boundaries, missing/extra/wrong HM slots,
premise discharge/rejection and an actual captured outer-count environment.
The certificate and `use` theorem require only standard Lean axioms; `check`
inherits the established positive solver trust solely for premise discharge.

This is not yet declaration synthesis: typed artifacts cannot manufacture the
required universal RHS certificate just by decoding their annotations. The
existing fragment's carried annotation obligations remain ground-only; scoped
symbolic declarations need a corresponding judgement/interpretation boundary
before launch. Recursion, fresh unknown inference, branch coverage, runtime
soundness and CLI/LSP integration remain separate. No HM/Path R rule changed.

Validation after 3r: full HM/Bounds/editor/CLI build passes (1735 jobs), with 256
BL regressions. Fresh scratch HM audit: 28 accepted / eight expected rejections /
zero failures. Boundary and whitespace guards pass; no new axioms, placeholders
or partial definitions were introduced.

2026-09-14, checkpoint 3s: `CountAlgebra` proves finite composition of
simultaneous count interpretations. `InterpretedAnnotation` keeps original
annotations and lexical identities unchanged, while checking their interpreted
demands in a separate caller scope. Decoder scope, finite Nat interpretation,
HM shape and semantic inclusion are independent evidence boundaries.

`ScopedTyping` supplies an annotation-aware monomorphic fragment indexed by
source count scope and interpretation. Every lambda/let annotation remains a
checked obligation. Count transport changes interpretation, path assumptions,
environment and result, not source syntax. Its annotation-forgetting theorem
produces bounds typing for the existing erased runtime term; it is not runtime
length soundness. Transport/forgetting/assuming require standard Lean axioms only.

`ScopedWalk` consumes found children and checks scoped symbolic annotations at
all supported nesting depths. `ScopedDeclaration.checkRHS` selects an exact-site
count telescope, checks the real typed RHS and declared obligation, validates
monomorphic HM shape/local closure, and constructs a `CountContract.Certified`
value through the proved erasure bridge. The environment's counts must belong
only to explicit captures, never the declaration's quantified coordinates.

HM binder facts currently cover unannotated declarations only. Those continue
to require their unique exact-site machine fact. Annotated monomorphic RHSs use
their actual found payload and separately checked carried signature; no missing
machine fact or generalized annotation slots are invented. RHSs needing HM
specialization to a narrower signature explicitly defer, as do generalized HM
declarations/lets, nested count telescopes, holes, open parameter unknowns,
matches and recursive assumptions. Surface count telescopes currently occur on
recursive bindings: inspecting a member's RHS is NOT acceptance of its group.
The checker has no recursive group introduction or recursive-call contract rule.

Twenty-three real-artifact/interpretation regressions cover symbolic identity,
independent count uses, Cons length increment, incorrect result/nested contracts,
scope and metadata failures, forbidden recursive calls, deferred RHS HM
specialization, captured environments and overlapping interpretation rows.
The checked artifacts now generate certificates rather than relying only on
handwritten implementation certificates. CLI/LSP launch routes and HM/Path R
remain unchanged; no full artifact-coherence or runtime theorem is claimed.

Validation after 3s: full HM/Bounds/editor/CLI build passes (1741 jobs), with 279
BL regressions. Fresh scratch HM audit: 28 accepted / eight expected rejections /
zero failures. Boundary and whitespace checks pass; no new axioms, placeholders
or partial definitions. Executable inclusion retains positive solver trust.

2026-09-14, checkpoint 3t: scoped declaration certificates now support
unannotated HM generalization as well as count quantification. The unique,
exact-site machine binder scheme is checked against the actual RHS bounds and
closed at fresh HM identities. Freshness includes both the captured environment
and original source annotations; erasing an already-checked annotation does not
make its fixed identity generalizable.

`ScopedTyping.binder_instances` reuses the proved erased RHS specialization
bridge to construct the universal HM premise of `CountContract.Certified`.
The count scheme stores the closed HM body, so count interpretation precedes
insertion of complete caller HM bounds. Caller count identities remain untouched
even when they coincide numerically with declaration count identities. This
proof requires only standard Lean axioms, not a solver axiom.

Five new real-artifact regressions cover independent HM uses, combined HM/count
instantiation with a caller-name collision, two-slot specialization in the
machine's actual slot order, malformed alias metadata and a source-annotation
identity incorrectly claimed as generalizable. The scoped declaration suite
now contains 28 cases.

This expands RHS certification, not recursive-group acceptance. Annotated HM
polymorphism and specialization of a more-general RHS to a narrower annotation
remain explicit unsupported cases, as do generalized internal lets, recursive
assumptions and matches. CLI/LSP launch and HM/Path R remain unchanged; runtime
length soundness and full artifact coherence are still separate theorem targets.

Validation after 3t: full HM/Bounds/editor/CLI build passes (1741 jobs). Fresh
scratch HM audit: 28 accepted / eight expected rejections / zero failures.
Boundary and whitespace guards pass; no new axioms, placeholders or partial
definitions were introduced. Executable inclusion retains positive solver trust.

2026-09-14, checkpoint 3u: `CountApplication` connects a certified HM/count RHS
use to an independently typed argument. Successful results retain function and
argument derivations, both caller scopes, semantic argument-to-domain inclusion,
and a derivation for the application with exact found function/result shapes.
Explicit complete HM arguments cannot bypass the actual argument obligation.

Structural HM proposals share `StructuralApplication.propose`; they preserve
full argument bounds and remain untrusted until the same checking path succeeds.
Slots absent from the domain receive Unit only, so a result-only List or other
non-Unit HM slot still needs separately supplied full bounds. Count arguments
remain explicit at this component boundary; count inference is not yet supplied.

Twenty-five regressions use certificates constructed from actual lowered and
inferred declaration RHS artifacts. They cover Nil/Cons lengths, an incrementing
implementation, generic and nested origins, caller-count collisions, count
scope/arity/finiteness, independently discharged premises, mismatched HM and
result payloads, higher-order variance, result-only slots and scalar contracts.
The existing structural application regressions also pass after sharing the
proposal collector.

These are applications of the certified RHS term, not uses of a recursively
assumed variable. Recursive-group introduction/call environments, match rules,
CLI/LSP migration, runtime length soundness and artifact coherence remain pending.
The checker inherits only the established positive solver trust beyond standard
Lean axioms. HM/D2 and bounds-blind Path R are unchanged.

Validation after 3u: full HM/Bounds/editor/CLI build passes (1743 jobs). Fresh
scratch HM audit: 28 accepted / eight expected rejections / zero failures.
Boundary and whitespace guards pass; no new axioms, placeholders or partial
definitions were introduced.

2026-09-14, checkpoint 3v: `CountProposal` supplies conservative implicit count
arguments from directly exposed interval endpoints in the argument's actual
bounds. Proposal order follows the declaration telescope, captures remain
untouched, and opaque HM slots do not expose their caller counts as declaration
coordinates. Repeated coordinates retain the first proposal; every endpoint
and structural variance obligation is still checked afterward.

Compound-only occurrences explicitly report unsupported arithmetic inversion.
Coordinates absent from the domain receive zero as a finite proposed witness;
their premises are still discharged independently, not silently assumed. This
is a supported-fragment policy, not completeness, principality or arbitrary
recursive invariant inference.

`CountApplication.infer` sends count proposals and full structural HM proposals
through the existing certified application path. No scope, finite Nat, premise,
HM-shape, variance or semantic inclusion check is bypassed. Ordinary source
application currently has no explicit count-argument syntax, so this supplies a
needed component for later source-call integration without changing the parser.

Fourteen additional regressions cover implicit Nil/Cons/increment calls, unused
coordinates, caller count collisions, independently checked premises, direct
upper endpoints, compound deferral with successful explicit specialization,
telescope order, captures, opaque slots, conflicting repeated endpoints and an
infinite endpoint that must not become a Nat argument. The application suite now
contains 39 cases. The proposal computation requires only standard Lean axioms;
accepted applications retain the existing positive solver trust.

Validation after 3v: full HM/Bounds/editor/CLI build passes (1744 jobs). Fresh
scratch HM audit: 28 accepted / eight expected rejections / zero failures.
Boundary and whitespace guards pass; no new axioms, placeholders or partial
definitions. Recursive-group/call-environment rules, generalized internal scoped
lets, matches, production CLI/LSP migration, artifact coherence and runtime
length soundness remain pending. HM/D2 and bounds-blind Path R remain unchanged.

2026-09-14, checkpoint 4a: `RecursiveContract.Declared` represents a declared
recursive assumption separately from `CountContract.Certified`. Its HM type is
one locally closed monotype, not an instantiable HM scheme. Count uses check
finite/scoped arguments, captures and independently discharged premises, then
compare their found payload with that exact monotype. Free HM identities remain
fixed too; no caller HM argument array or slot-proposal path exists here.

`RecursiveTyping` extends the scoped annotation judgement with explicit
recursive bindings and a simultaneous group rule. Group introduction requires
each RHS, at every scoped finite count instantiation, to have a derivation,
satisfy its original interpreted annotation, and lie within its declared bounds
contract. All three universal premises are required; decoding or sampling a
contract does not supply them. Group count telescopes must be distinct and no
member may capture another member's quantified coordinate. Captured outer
bindings must fit every member's explicit capture interface.

The initial group body retains fixed HM monotypes; exit HM generalization is
not implemented by this judgement. Monomorphic HM carried signatures must align
exactly with found payloads. Valid HM artifacts whose RHS is more general than
its annotation explicitly defer for specialization. Opening polymorphic HM
annotations at the actual shared group identities also remains separate work;
this is not permission to reinstantiate those annotations at recursive calls.

`RecursiveVariable` constructs conditional variable/application derivations
under these explicit assumptions. Implicit calls propose counts from actual
argument origins, then check scope, finiteness, premises, semantic domain
inclusion and exact function/result HM payloads. These results do NOT accept a
group or export an RHS certificate.

The solver-free `recursive_var_shape` theorem proves fixed HM spines for all
declarative recursive-variable uses, not just checked ones. Existing scoped
derivations embed unchanged, and premise strengthening preserves the universal
group obligations. Two solver-free group regression proofs exercise universal
self-recursive calls and retained symbolic lambda/binding annotations. Thirty-one
executable cases exercise actual self/mutually recursive HM artifacts, independent
counts, forbidden HM specialization, caller scope/captures/premises, Nil/Cons
applications, malformed interfaces and valid-HM specialization deferral.

Validation after 4a: full HM/Bounds/editor/CLI build passes (1748 jobs). Fresh
scratch HM audit: 28 accepted / eight expected rejections / zero failures.
Boundary and whitespace guards pass. New theorem dependencies are standard Lean
axioms only; executable premise/inclusion checks retain positive solver trust.
No new axioms, placeholders or partial definitions. Legacy Bounds placeholders
are unchanged. Executable symbolic-RHS/group checking still needs a capture-safe
recursive count-transport bridge before universal certificates can be generated.
Matches, CLI/LSP migration, artifact coherence and runtime length soundness remain
pending; HM/D2 and Path R are unchanged.

2026-09-14, checkpoint 4b: `RecursiveCountTransport` proves caller count
transport with protected callee telescopes. Instantiating a contract and then
transforming its caller counts equals transforming the arguments and opening
the unchanged contract template. Captured coordinates must remain fixed.
The equality covers self-recursive calls whose selected caller identity is also
the callee's quantified identity, and transforms contract premises in lockstep.

Transported instances retain finite/scoped arguments and captures; their caller
interface conservatively keeps the previous scope and adds the replacement
scope. Usability transports by semantic validity, not a fresh solver verdict or
an assumption appended to the context. No HM identities or schemes are opened.

The `transport` theorem lifts this algebra to annotation-aware derivations with
recursive assumptions. Monomorphic local bounds and call arguments are mapped,
recursive templates remain unchanged, and original source annotations use a
separate composed interpretation. An explicit source-fragment condition excludes
nested recursive groups and matches; nested groups may capture enclosing counts
and require captured-template transport rather than this fixed-capture rule.

`universal_rhs` now generates every scoped finite count instance from one checked
symbolic RHS derivation, captured outer monomorphic bounds, and recursive capture
freshness. Group interface independence supplies the relevant freshness for
other members. A concrete solver-free regression generates the universal
self-recursive RHS premise from a symbolic proof rather than proving each use
directly. This is the needed theorem bridge, not yet an executable RHS walker or
whole-group acceptance route.

Twelve executable transport regressions cover protected self-recursive IDs,
lockstep premises, distinct caller coordinates, symbolic replacements, fixed
captures, arity/scope, infinite and inferable replacement rejection, and
simultaneous insertion without recursive resubstitution. All new transport and
universal-RHS proofs depend only on standard Lean axioms, not solver trust.

Validation after 4b: full HM/Bounds/editor/CLI build passes (1750 jobs). Fresh
scratch HM audit: 28 accepted / eight expected rejections / zero failures.
Boundary and whitespace guards pass; no new axioms, placeholders or partial
definitions. Legacy Bounds placeholders are unchanged. Found-driven recursive
RHS checking and universal group-certificate construction are next integration
targets; narrower annotation specialization, fixed polymorphic HM openings,
exit HM generalization, matches, CLI/LSP migration, artifact coherence and
runtime length soundness remain separate. HM/D2 and Path R are unchanged.

2026-09-14, checkpoint 4c: `RecursiveWalk` consumes found children to check
symbolic RHSs under fixed-HM recursive assumptions. Direct recursive variable
applications use argument-origin count proposals and the checked conditional
application rule. Literal/list origins, primitive operations, interpreted lambda
annotations, monomorphic internal lets and ordinary applications retain their
obligations. Every success carries a derivation, count scope, exact root shape,
Core-path reports and the explicit fragment proof needed by count transport.

Standalone count-polymorphic recursive variables explicitly require an argument
origin; generalized internal HM lets, nested groups, matches and unsupported
origins remain explicit errors. There is no fallback to a legacy synthesizer or
independent recursive HM scheme instantiation.

`RecursiveRHS.check` reconciles the declaration telescope at its exact Core site,
checks the actual found RHS, its carried binding annotation and its declared
contract, then validates captured monomorphic bounds and recursive capture
freshness. `Certified` stores all of that evidence. Its solver-free `use` bridge
supplies universal typing, retained annotation and contract-inclusion premises
for every scoped finite count instance using the proved symbolic transport.
Certificates remain conditional on the simultaneous assumption environment;
checking one RHS alone does NOT accept a group or export an assumed contract.

Ten executable regressions use actual lowered/inferred recursive artifacts.
They generate universal certificates, accept count-polymorphic calls at n+1
when the surrounding obligations permit them, reject incorrect recursive length
claims and nested annotations, enforce exact metadata/capture boundaries, retain
valid-HM specialization deferral, and check both mutually recursive RHSs under
the same environment at differing recursive counts. Successful single-member
tests also check exactly-once logical Core-path report coverage; that remains an
executable check, not formal artifact coherence.

Validation after 4c: full HM/Bounds/editor/CLI build passes (1753 jobs). Fresh
scratch HM audit: 28 accepted / eight expected rejections / zero failures.
Boundary and whitespace guards pass. Certificate specialization requires only
standard Lean axioms; executable inclusion checks retain positive solver trust.
No new axioms, placeholders or partial definitions; legacy Bounds placeholders
are unchanged. Whole-group certificate assembly/introduction and group-body
checking are next. Narrower annotation specialization, fixed polymorphic HM
openings, exit HM generalization, matches, CLI/LSP migration, artifact coherence
and runtime length soundness remain separate. HM/D2 and Path R are unchanged.

### Checkpoint 4d — whole recursive groups discharge their assumptions

`RecursiveGroup.Members` indexes certificates by the complete ordered contract,
RHS and annotation lists. Its universal obligations discharge all three RHS
premises of `RecursiveTyping.Derives.letRec`; `Certified.typing` introduces the
whole group only after its body has also been derived under the same assumptions.
There is no API exporting a successful body from unchecked members.

The optional found-driven group checker decodes each declared interface at its
exact Core member site, validates telescope independence and outer capture scope,
checks every RHS with `RecursiveRHS`, then checks the body. Count instantiation is
available in the body from actual argument origins; recursive HM types remain
fixed. The located RHS helper is indexed by its actual input child, preserving
the source link without an expression-equality reconciliation pass.

Eighteen executable regressions cover actual self/mutually recursive artifacts,
different count arguments, one bad member rejecting a group, a bad group body,
standalone count-polymorphic values without an origin, missing contracts,
overlapping/duplicate/missing telescopes, outer capture escapes, forged/missing
found payloads, parallel-list arity, empty groups, and rebased non-root sites.
Successful whole groups retain exactly-once logical-node coverage. This remains
an executable guard, not a formal provenance/coherence theorem.

Validation: full HM/Bounds/editor/CLI build passes (1755 jobs); scratch HM audit
remains 28 accepted / eight expected rejections / zero failures. Boundary and
whitespace guards pass. Group introduction uses only standard Lean axioms;
executable inclusion retains the existing positive solver trust. No new axioms,
placeholders or partial definitions. The body still uses fixed HM monotypes;
annotation specialization, fixed polymorphic annotation opening, exit HM
generalization, nested groups, matches and unified product wiring are not yet
supplied. HM/D2, erased runtime and Path R remain unchanged.

### Checkpoint 4e — parsed recursive contracts and source reports

`RecursiveFound.synthNodes` is an opt-in adapter from an already inferred
provenanced artifact to whole-group acceptance and per-occurrence source reports.
It guards input provenance, complete logical-node coverage and origin joins. It
does not replace the production CLI/LSP BL launch or certify full artifact
coherence.

Eighteen new parser-to-report regressions exercise actual `.fhm` source syntax,
self/mutual recursion at distinct counts, literal list origins, retained nested
lambda/let annotations, bad implementations/bodies, and missing/duplicate source
joins. Polymorphic signatures, more-general RHS specialization, matches and
standalone count-polymorphic values remain explicit unsupported cases.

These tests uncovered a frontend gap: expression annotations parsed their counts
under an empty declared-name context, so a signature's `n` could not occur in an
inner lambda or ordinary let annotation. `Parse.CountContext` now distinguishes
closed standalone type/scheme parsing from lexically deferred expression
annotations. Construction-time `CountScope` remains the name/scope authority;
no parser-invented identities or substitutions are introduced. Named count atoms
also work as operands of `pred`, `min` and `max`.

Unbound named counts in program annotations now parse and remain invisible to HM;
the new BL adapter rejects their recorded scope problems. Regressions ensure type
foralls do not silently become Nat binders. Standalone `parseTy`/`parsePolyTy`
retain their declared-name restrictions. This is syntax/scope plumbing, not a
change to the HM rules or erased semantics.

Validation: full HM/Bounds/editor/CLI build passes (1757 jobs); scratch HM audit
remains 28 accepted / eight expected rejections / zero failures. Boundary and
whitespace guards pass. No new axioms, placeholders or partial definitions;
parser partials remain under `FHM/Unverified`. Existing positive solver trust and
legacy Bounds placeholders are unchanged. Runtime soundness, annotation HM
opening/specialization, exit generalization, matches and unified product launch
remain future work.

### Checkpoint 4f — semantic branch upper/lower candidates

`BranchMerge` specifies structural upper and lower candidates independently of
the solver. List upper candidates use interval union; lower candidates use
intersection. Arrow domains flip the mode, including through nested arrows;
codomains retain it. Successful construction carries a `Combines` derivation.
Proved consequences establish both semantic inclusions at every premise context,
exact agreement with both input HM spines, and preservation of explicit count
scope. No unrestricted principality/minimality theorem is claimed.

This deliberately does not reuse legacy `joinBoundsTy`: that function unions
arrow domains as well as results and has an HM-shape theorem, not the semantic
upper-bound guarantee needed here. For example, merging domains of exact lengths
one and two must not make both functions callable on either length. Their safe
upper function candidate has the empty intersection domain `[2,1]`. Such an
interval fabricates no inhabitant and is not evidence that an arm is unreachable.
The legacy launch remains untouched until unified-pipeline migration.

Sixteen solver-free regressions cover unions/intersections, disjoint domains,
higher-order variance, nested Lists, infinity, symbolic counts and fixed HM
identity/constructor boundaries. Full HM/Bounds/editor/CLI build passes (1759
jobs); scratch HM audit remains 28 accepted / eight expected rejections / zero
failures. Boundary/whitespace guards pass. All new merge proofs/construction use
only standard Lean axioms; no new solver trust, placeholders or partials.

This is match groundwork, not acceptance of matches. Path-refined coverage and
branch typing are still needed. Annotated recursive functions additionally need
branch results checked against their common declared result under each path's
assumptions; an unconditional interval union alone can lose the correlation
needed for an exact length-preserving contract. HM/D2 and Path R are unchanged.

### Checkpoint 4g — semantic List coverage and path arithmetic

`ListBranches.Covers` expresses List coverage using arithmetic validity rather
than executable verdicts. `Covers.sound` proves that every finite length admitted
by the interval has an appropriate proper-arity Nil/Cons branch or wildcard.
The executable checker constructs that evidence and rejects unsupported coverage;
the legacy coverage relation has a one-way semantic bridge retaining its existing
positive-verdict trust. This is the intended List coverage specification for the
new typed match layer, not a second enabled product-level pass.

Coverage transports through finite count substitution with its premises, without
another solver verdict. Constructor arithmetic proves Nil/Cons path refinements,
predecessor tail containment, and reconstruction of the original interval only
under the nonempty path premise. That premise is essential at zero because
`pred 0 = 0`. Tail interpretation commutes with count substitution.

Eighteen executable regressions exercise full/wildcard/single-constructor
coverage, incorrect arities/names, symbolic path evidence, infinity, tail lengths
and the truncated-predecessor counterexample. The specification and arithmetic
proofs use only standard Lean axioms; executable coverage retains positive
solver trust. Full HM/Bounds/editor/CLI build passes (1761 jobs); scratch HM audit
remains 28 accepted / eight expected rejections / zero failures. Boundary and
whitespace guards pass; no new axioms, placeholders or partial definitions.

These are finite-length arithmetic/coverage components. They do not yet connect
interval membership to all Core runtime values, introduce bounds derivations for
match expressions, or enable matches in the found walker. Branch typing and
count transport through matches, contract-guided result checking, HM annotation
opening/specialization, exit generalization and unified product wiring remain.

### Checkpoint 4h — typed List matches and universal count transport

The existing `RecursiveTyping` judgement now includes List matches, with proper
Nil/Cons/wildcard patterns, semantic coverage, constructor-specific path premises
and head-before-tail Cons binder layout. Every arm has an actual bounds derivation
and a semantic inclusion into a common result under its own path. Strengthening
premises and finite count transport preserve the rule, including the refined
tail environment. Consequently the existing universal recursive RHS certificates
and simultaneous group introduction work for matches without a new trust premise.
Nested recursive groups remain explicitly excluded from this transport fragment.

`RecursiveWalk` consumes the same found artifact and keeps exact ordered branch
evidence. Unannotated match synthesis uses the proved variance-correct semantic
merge. A result demand from a recursive contract or monomorphic local annotation
instead checks each arm against that common result under the arm's path. This
avoids losing the empty/nonempty correlation needed for exact-length copy. Actual
arm reports remain unchanged; a declaration is not substituted for arm evidence.
Demand guidance is not an unchecked global subsumption rule, and the outer RHS
annotation and contract inclusions are still checked.

Twenty new found-tree regressions cover coverage, malformed patterns alongside
wildcards, tail scopes, nested matches, forged HM shapes, bad length claims and
function-valued matches with disjoint arrow domains. Eleven new parsed-source
regressions cover exact-length recursive and mutually recursive copies, count
zero/singleton/longer calls, bad arms, incomplete coverage, wildcard recursion and
captured local annotated matches. The old parsed "matches unsupported" regression
now checks acceptance. A solver-independent formal regression generates every
finite scoped count instance from a symbolic match derivation.

The production CLI/LSP route is unchanged. HM/D2 and bounds-blind Path R are
unchanged. This is typed coverage/count-certificate work, not whole-runtime length
soundness, full artifact coherence or termination checking. HM annotation opening
and specialization, contract-guided unannotated List parameters, exit/internal-let
generalization, captured nested groups and unified product wiring remain.

Validation: full HM/Bounds/editor/CLI build passes (1762 jobs); scratch HM audit
remains 28 accepted / eight expected rejections / zero failures. Boundary and
whitespace guards pass. The new typing/transport proofs and universal-match
regression use only standard Lean axioms; executable checking retains the existing
positive solver-verdict trust. No new axioms, placeholders or partial definitions.

### Checkpoint 4i — contract-guided lambda domains and application arguments

An unannotated lambda checked against an explicit arrow demand now introduces
the declared domain as its parameter assumption, after requiring exact agreement
with the found HM parameter spine. Curried guidance reaches inner parameters.
Carried parameter annotations are still decoded and checked independently rather
than overridden. Without a demand, open List parameters remain explicitly
unsupported; no fresh count origin is guessed. Caller-scope checks and the outer
RHS contract inclusion remain mandatory.

Known computed-function and monomorphic-variable domains also guide argument
checking. This admits higher-order unannotated lambda arguments and path-correlated
match arguments, while retaining the application rule's actual argument inclusion.
Count-polymorphic recursive argument proposals still require an actual origin;
this change does not use an uninstantiated callee telescope as caller information.

Twelve new walker regressions cover fixed/symbolic/captured domains, curried
checking, absent demands, wrong output claims, differing HM identities, count
escape, carried annotations, higher-order arguments and correlated match arguments.
Six new parsed-source regressions exercise monomorphic recursive copies with
unannotated parameters and captured-count higher-order arguments, including bad
claims and the still-explicit need for HM annotation specialization.

The production route and HM/D2/Path R are unchanged. General polymorphic recursive
annotation opening/specialization, fresh open-parameter origin inference, Bool/data
matches, exit/internal-let generalization and captured nested groups remain separate.

Validation: all 32 walker and 35 parsed-source regressions pass, along with the
full HM/Bounds/editor/CLI build (1762 jobs). Scratch HM audit remains 28 accepted /
eight expected rejections / zero failures. Boundary and whitespace guards pass;
no new axioms, placeholders or partial definitions, and solver trust is unchanged.

### Checkpoint 4j — typed Bool matches, conditionals and recursive filtering

`BoolBranches` specifies proper True/False/wildcard coverage and proves that it
covers both constructor cases without arithmetic solver trust. `RecursiveTyping`
now has Bool constructor and match rules. Both premise strengthening and finite
count transport preserve them, so the same universal recursive RHS and whole-group
certificates also cover conditionals. Bool comparison outcomes introduce no extra
count or length refinements.

The found walker uses one ordered branch traversal for List and Bool, with an
explicit context selecting patterns, premises and binder environment. Bool arms
retain the caller's premises and environment; List arms retain their proved
constructor refinements. Both synthesis and common-result checking use the same
semantic inclusion/report machinery. This accepts the Core form to which surface
`if` lowers; it does not perform constant-condition dead-arm elimination.

Fourteen new Bool walker regressions check literals, comparison results, full and
wildcard coverage, wrong arities/constructor names, interval union, bad result
claims even in a constant condition, forged HM types and nested reports. Eight
new parsed-source regressions check recursive and mutually recursive keep/drop
filters with `0..n` result contracts, conditional exact-length copying, incorrect
retention/duplication claims, the absence of invented count refinements and
ordinary scalar recursion returning Bool. A formal symbolic Bool-match regression
generates every finite scoped count instance with only standard Lean axioms.

These are monomorphic-HM examples with explicit count contracts. General `map`
and `filter` signatures still require HM annotation opening/specialization, and
curried count-polymorphic applications must infer from the relevant full argument
spine rather than guess at the first argument. Product CLI/LSP migration, fresh
open origins, generalized lets/group exit, captured nested groups and general data
matches remain. HM/D2 and Path R are unchanged; no runtime length or termination
theorem is claimed by these certificates.

Validation: all 14 Bool, 32 List/checking-guidance and 43 parsed-source regressions
pass. Full HM/Bounds/editor/CLI build passes (1764 jobs); scratch HM audit remains
28 accepted / eight expected rejections / zero failures. Boundary/whitespace guards
pass. Bool coverage introduces no solver trust; typed/count-transport proofs retain
only standard Lean axioms and executable inclusion retains the existing positive
verdict axiom. No new axioms, placeholders or partial definitions.

### Checkpoint 4k — full curried recursive application spines

`CountProposal.proposeArguments` collects one untrusted count vector across all
supplied input domains, in telescope order. Repeated coordinates retain their
first witness, and a later direct endpoint can supply an earlier compound one.
Compound-only occurrences still reject rather than invert arithmetic. A count
appearing only in an unsupplied input domain requests a later origin; truly
result-only coordinates retain the documented finite-witness policy.

`RecursiveSpine` keeps the exact found application spine and each argument's
derivation, scope and report nodes. Acceptance introduces the existing recursive
variable rule once, discharging the instantiated premises and checking its fixed
HM identity, then introduces the existing application rule at every frame. Every
actual domain inclusion and intermediate found HM payload is checked. No new
typing rule or HM inference pass is used, and existing universal count transport
and whole-group certification apply unchanged. Argument collection accumulates
in reverse once instead of repeatedly appending to an argument vector.

The same found walker intercepts recursive application spines before synthesizing
a partial callee. Ordinary monomorphic argument guidance remains unchanged, and
there is no second unary recursive proposal authority in this product slice.
Twenty new executable proposal/spine regressions exercise multiple/later origins,
partial calls, repeated/compound/captured coordinates, fixed HM identities,
intermediate payloads, premises, finite/caller scopes and exact-once reports.
Twelve new parsed-source regressions check curried monomorphic map, mutual map,
third-argument origins, two-count append with an `n + m` result contract, repeated
count mismatches and earlier compound-domain validation.

HM/D2, bounds-blind Path R and the legacy production CLI/LSP route are unchanged.
Polymorphic HM annotation opening/specialization and exit generalization remain.
An unannotated List-parameter callback that needs bounds inferred from another
argument still requires a two-phase argument-checking route: origins first,
then checking deferred lambdas at the instantiated caller-scoped domain. This
checkpoint does not invent an origin to get such a callback through synthesis.

Validation: all 20 spine and 55 parsed-source regressions pass, as does the full
HM/Bounds/editor/CLI build (1766 jobs). Scratch HM audit remains 28 accepted /
eight expected rejections / zero failures. Boundary and whitespace guards pass.
The spine uses the existing positive-verdict trust only; no new axioms,
placeholders or partial definitions were introduced.

### Checkpoint 4l — origins first, deferred callback checking second

Recursive spines now explicitly prepare argument origins before checking lambda
telescopes containing unannotated non-scalar domains. `Prepared` stores `none`
for those arguments: no bounds or derivation is fabricated. `proposeOrigins`
is the single proposal authority, and `proposeArguments` delegates to it.
Coordinates appearing in deferred domains require an independent actual origin;
they cannot silently receive the result-only zero witness or be obtained by
arithmetic inversion. Synthesizable scalar and annotated callbacks remain actual
origins, including a scalar callback that supplies the only count witness.

Completion checks the recursive variable once, including finite arguments,
caller scope, declared premises and fixed HM identity. Each deferred callback is
then checked under the actual instantiated domain, and every application frame
still verifies inclusion and its intermediate found HM payload. `Completed`
contains all exact source argument derivations. The new `append` helper shares
the existing ordinary application proof; it does not repeatedly reinstantiate
the callee or rewalk already synthesized arguments. The verified walker remains
total, with a checked lexicographic termination measure for the two phases.

Five new proposal regressions and eight parsed-source regressions cover missing
origins, later origins, mixed scalar/List lambda telescopes, zero counts, bad
output lengths, internal annotations and a mutually recursive caller's distinct
count identities. The mutual fixture deliberately forms one group: sequential
nested groups still reject at the existing captured-template transport boundary.

Validation: 25 spine/proposal and 63 parsed-source regressions pass. Full
HM/Bounds/editor/CLI build passes (1766 jobs), as do the boundary and whitespace
guards. The fresh scratch HM audit remains 28 accepted / eight expected
rejections / zero failures. HM/D2, Path R, production CLI/LSP launch and the
existing solver trust boundary are unchanged; no new axioms, placeholders or
partial definitions were introduced.

The next major dependency is genuinely polymorphic HM contract opening and RHS
specialization/generalization, not another application-spine patch. Merely
matching a forall annotation against a found type is insufficient: the current
annotation-aware recursive judgement intentionally has monomorphic binding
obligations, so its universal RHS/group certificates must be extended together.
Recursive calls must retain the group's one fixed HM opening throughout; only
group exit can export a generalized HM scheme. Captured type/count identities
and caller bounds inside HM arguments need capture-safe simultaneous transport.
Nested groups, fresh open origins, general data matches, runtime length soundness,
artifact coherence and unified product wiring remain subsequent work.

### Checkpoint 4m — consecutive program groups and non-recursive roots

`RecursiveGroup.check` now checks consecutive recursive groups in program bodies
with the same whole-group introduction theorem at every group. The caller count
interpretation is unchanged when moving to a later body: no universal RHS
transport is assumed or manufactured. Each later group's exact metadata site,
environment captures, fixed HM identities and all member obligations are still
checked before the outer result/report can be returned. Invalid later groups or
final bodies reject the entire result. Recursion is structurally decreasing on
the found expression, without a partial definition.

Non-recursive found roots delegate to the existing expression walker and retain
its derivation, HM shape and count-scope evidence. Thus the opt-in provenance
adapter also accepts scalar operations, exact List literals, ordinary monomorphic
root lets and Bool conditionals, rather than requiring a recursive root.

Eleven new parsed regressions cover those non-recursive roots, consecutive groups,
calls to earlier groups, deferred callbacks at a later group's count identities,
bad later contracts and invalid final bodies. Three kernel-side regressions check
empty consecutive groups, forged inner HM payloads and missing inner found roots.
Groups inside universal RHSs still explicitly reject: they need protected
captured-template transport, unlike consecutive groups in program bodies.

Validation: 74 parsed-source and 21 group regressions pass, along with the full
1766-job HM/Bounds/editor/CLI build. Boundary/whitespace guards pass; the scratch
HM audit remains 28 accepted / eight expected rejections / zero failures. No new
axioms, placeholders or partial definitions; HM/D2, Path R and production launch
are unchanged. Polymorphic HM opening/exit generalization and general program
wrappers are not claimed complete by this narrower extension.

### Checkpoint 4n — monomorphic expression lets around program groups

Program checking now handles expression-level monomorphic `let ... in ...`
prefixes before and between recursive groups. RHS bounds are synthesized with
the existing annotation hint; the shared `RecursiveWalk.checkMonoBinding`
checks the actual source annotation and, for unannotated lets, the exact inferred
binder scheme and captured HM identities. The program body recurses through the
same group checker under the actual RHS bounds. The existing `Derives.letMono`
rule supplies the proof; the let root's found HM payload is independently checked.
The universal RHS walker shares this admission helper but retains `NoGroups`.

Six parsed regressions cover captured scalar prefixes, an unannotated concrete
List prefix, a bad count annotation, a monomorphic let between groups, and both
inferred/declared polymorphic lets rejecting at the generalization boundary.
Three kernel regressions check forged let HM payloads and missing exact found
RHS/body nodes. All 80 parsed and 24 group regressions pass, with the full
1766-job HM/Bounds/editor/CLI build, boundary/whitespace guards and fresh scratch
HM audit (28 accepted / eight expected rejections / zero failures).

Source distinction matters: top-level declarations desugar as groups, whereas
expression `let ... in ...` nodes use `letMono`. An unannotated top-level singleton
group still needs declared contracts in this slice; this checkpoint does not
silently rewrite it as a monomorphic let or skip generalized HM obligations.
Groups inside a monomorphic let RHS or a universal recursive RHS still require
further program/template handling. No new axioms, placeholders or partial
definitions; HM/D2, Path R and production CLI/LSP launch remain unchanged.

### Checkpoint 4o — ordinary program binders can contain checked groups

The program checker now descends through ordinary lambda bodies and monomorphic
let RHSs, introducing the existing lambda/let/group rules under the unchanged
caller interpretation. It does not transport a nested group through a universal
recursive RHS certificate: that harder boundary remains explicit in
`RecursiveWalk.NoGroups`. Source annotations, captured environment scope and
every inner member certificate still apply. The shared lambda-domain admission
preserves carried annotations and requires exact found HM agreement.

An optional checking demand now travels through program binders to the existing
walker. It guides unannotated lambda domains and checked branch results; it is
not an unchecked coercion. Enclosing binding/application obligations remain
mandatory. Lambda roots verify their entire HM arrow and caller count scope,
including unused parameter domains, before returning a result/report.

Nine parsed regressions cover program lambdas with inner groups, scalar captures,
unannotated scalar domains, invalid inner contracts, annotated/unannotated
monomorphic let RHS groups, enclosing count obligations and signature-guided
unannotated List domains. Four kernel regressions cover forged/non-arrow lambda
HM payloads, missing body wrappers and an out-of-scope checking-domain count.
All 89 parsed and 28 group regressions pass, as does the full 1766-job
HM/Bounds/editor/CLI build, boundary/whitespace guards and fresh scratch HM audit
(28 accepted / eight expected rejections / zero failures). No new axioms,
placeholders or partial definitions; HM/D2, Path R and production launch unchanged.

This is not unrestricted descent into every expression context: applications
and match arms still use the universal-RHS walker and reject contained groups.
Genuinely polymorphic HM signatures/lets and top-level unannotated groups still
need their proper opening/generalization interfaces. The main proof dependency
remains capture-safe joint HM/count transport and sealed group-exit schemes,
followed by complete program descent and production LSP integration. Runtime
length soundness and formal artifact/report coherence remain separate claims.

### Checkpoint 4p — closed HM/count templates and opaque interfaces

`HMCountScheme` separates the declared HM slots, quantified counts and captured
identities in one well-formed closed template. `openFixed` checks explicit opaque
free HM identities against the actual fixed found monotype: exact arity, distinct
slots, freshness for both declared free captures and the surrounding type
interface, and local closure. It supports legitimate unused forall slots without
imposing a guessed Unit argument. The opening preserves all source counts and
has certified count-interface well-formedness and relational HM instantiation.

External `check` takes explicit caller bounds arguments, checks their HM arity,
local closure and count scope, instantiates finite caller count arguments and
discharges declared premises. Counts are substituted before caller bounds are
inserted at HM slots. The resulting certificate proves the exact found HM
instance, caller scope and transport of semantic inclusions. It does not invent
argument-origin evidence or prove an RHS.

`RecursiveContract.decodeOpaque` retains the closed template and its fixed
opening; the derived `Declared` uses the existing count-only recursive-variable
rule. The monomorphic group decoder delegates to the same interface machinery,
but its polymorphic guard stays until the source annotation/universal RHS/group
proofs are extended together. Interface decoding is not group acceptance.

Twenty-six new regressions cover repeated/distinct/aliased HM slots, declared and
nested captures, separate type/count namespaces, vacuous quantifiers, fixed
recursive HM calls, independent external Int/Char instances, caller bound-slot
and count escapes, finite Nat witnesses, failed premises and a caller count ID
overlapping the callee telescope inside an inserted nested List type.

Validation: all new and existing contract regressions pass; full
HM/Bounds/editor/CLI build passes (1768 jobs), including all 89 parsed-source
regressions. Boundary/whitespace guards pass and scratch HM audit remains
28 accepted / eight expected rejections / zero failures. Pure template/opening
proofs add no oracle trust; checked premise discharge retains the existing
positive-verdict axiom only. No new axioms, placeholders or partial definitions;
HM/D2, Path R and production launch unchanged. Next is a bounds-preserving
opaque close/open bridge into genuine RHS universality, followed by the joint
recursive-group generalization/annotation judgement rather than enabling a
decoder guard in isolation.

### Checkpoint 4q — exact opaque closure and genuine fragment RHS universality

`HMCountScheme.close_opened` proves that opening well-scoped HM slots at distinct
fresh free identities and then closing those identities recovers the ENTIRE
bounds template, including every count payload and declared free capture.
`Opening.close` specializes this theorem to checked interfaces. `Opening.abstraction`
builds a genuine `BinderBridge.Abstraction` with its explicit slot vector,
including unused forall slots, rather than trying to recover those from a
defaulted Unit opening. `Opening.specialize` connects simultaneous free bounds
replacement at opaque identities to specialization of the exact closed template.

`Opening.rhs_instances` joins that bridge to a real `Typed.Derives` RHS proof,
with freshness for the captured environment and source annotations. It gives
every full bounds argument instance in the existing initial non-recursive typed
fragment. Kernel-checked identity examples cover arbitrary nested caller bounds
and a vacuous forall; neither relies on a solver oracle or executable samples.
This is not yet universal recursive-assumption transport or a polymorphic source
binding/group rule, and it does not authorize exporting decoded assumptions.

All interface regressions and the full 1768-job HM/Bounds/editor/CLI build pass,
including all 89 parsed-source regressions. Scratch HM audit remains 28 accepted /
eight expected rejections / zero failures; boundary/whitespace guards pass.
The closure, abstraction and RHS universality proofs use only standard Lean
axioms, with no added oracle trust, placeholders or partial definitions.
HM/D2, Path R and production launch remain unchanged.

Next dependency: recursive specialization must retain closed count templates
and fixed HM bounds arguments separately. Embedding a caller bounds argument in
a telescope body before count substitution can capture caller counts when IDs
overlap. The external template checker already avoids this with count-first,
type-insertion-second instantiation; the recursive assumption/rule/transport
extension must preserve the same separation. Fixed HM arguments are per-group
interfaces, not HM re-instantiation at recursive calls and not runtime
type-passing elaborata. Valid HM RHSs more general than a declared signature also
need a checked payload interpretation/specialization seam, not another inference
pass or an unchecked cast of their found root.

### Checkpoint 4r — generalize actual RHS intervals and contract inclusion together

`Opening.abstractActual` uses the checked opaque slot vector to close an actual
RHS bounds type with the authoritative HM shape. It preserves the actual count
payloads; it does not replace them with the annotation's intervals.
`Opening.rhs_subinstances` requires both a genuine initial-fragment RHS derivation
and independently proved semantic inclusion in the opened contract. Every full
caller bounds specialization then retains the actual RHS derivation AND its
inclusion in the exact closed contract. Decoding an HM-shaped demand is still
not an RHS proof, and this theorem is not recursive-group introduction.

A kernel-checked universally quantified identity example preserves exact `n`
result bounds while meeting a weaker `0..n` demand for any caller bounds type.
Executable regressions check that closing retains the tighter intervals and
reject an HM-shaped RHS claiming an unjustified exact result count. All 28
HM/count interface regressions pass, as do the full 1768-job build and all 89
parsed-source regressions. Scratch HM audit remains 28 accepted / eight expected
rejections / zero failures; boundary and whitespace guards pass. New theorem
proofs use standard Lean axioms only. No new axioms, placeholders or partial
definitions; HM/D2, Path R and production launch remain unchanged.

Next is a closed-template/fixed-HM-argument recursive assumption interface and
its count-only use/specialization proofs, retaining the count-first/type-second
boundary before integrating universal recursive RHS and group-exit rules.

### Checkpoint 4s — fixed HM vectors with protected recursive count transport

`RecursiveHMContract.Fixed` stores the closed HM/count template and one fixed
vector of complete HM bounds arguments separately. `fix` reconciles that vector
with the authoritative group monotype, checking exact arity, local closure and
repeated-slot alignment. `fromOpaque` starts from the explicit fresh opening.
Neither is an implementation certificate. The optional module is not yet used
by the existing executable group walker.

Recursive `check` accepts count arguments only: callers cannot reopen the fixed
HM vector. Its `Use` certificate checks finite scoped count instantiation,
discharges premises, checks caller count scope for the separately inserted full
HM types, and preserves the exact call's found monotype. Bounds substitute the
closed count telescope BEFORE inserting those types. Scope, exact HM shape and
semantic contract-inclusion transport follow through the existing certified
external HM/count interface.

`Fixed.map` / `Use.map_bounds` prove simultaneous specialization of the entire
fixed interface and assumption uses, leaving captured free HM identities fixed
and retaining count witnesses/premises. This is a proof tool for specializing a
whole group, not permission to change HM arguments independently at calls.
`opaque_count_coherence` proves exact equality with the existing count-only
recursive rule before opaque HM arguments are replaced by full caller bounds.

`Fixed.mapCounts` maps caller-owned counts inside the fixed HM argument vector
without touching the callee's closed telescope. `Use.mapCounts` transports finite
caller count arguments and path assumptions together, protects callee captures,
and proves caller scope automatically. `Use.mapCounts_bounds` identifies the
result with semantic count substitution of the original use. This includes the
self-recursive overlapping-ID case. Supporting additions prove completeness of
the existing executable count/bounds scope predicates and expose the existing
count-scope monotonicity lemma; their specifications and algorithms are unchanged.

Seventeen new regressions cover opaque/specialized fixed HM calls, rejected
per-call HM reopening, repeated slots, arity, bound slots, count scope, finite
witnesses, failed premises, vacuous forall slots, overlapping caller/callee count
IDs, and outer transport with symbolic versus literal callee arguments. Generic
kernel-checked full-bounds and finite-count use transport proofs add no oracle
trust. The full 1770-job build and all 89 parsed-source regressions pass; scratch
HM audit stays 28 accepted / eight expected rejections / zero failures. Boundary
and whitespace guards pass. No new axioms, placeholders or partial definitions;
HM/D2, Path R and production launch remain unchanged.

Still required before enabling polymorphic recursive contracts: integrate this
assumption representation into recursive typing/walking and source-annotation
interpretation, prove whole-RHS HM transport rather than variable-use transport
alone, check specialization of more-general RHS found payloads, and introduce
joint universal HM/count RHS and generalized group-exit certificates. Removing
the current decoder/annotation guards before those proofs would be unsound.

### Checkpoint 4t — full recursive RHS HM/count transport and checked-fragment embedding

`HMInterpretation` makes source HM interpretation explicit and proof-side. Its
annotation judgement decodes the original scoped source, interprets source
counts first, then simultaneously inserts full bounds at free HM identities.
Composition and count-transport laws preserve caller-owned counts inside those
inserted types. The original source annotations and runtime expression stay
unchanged. Monomorphic local binding annotations retain their existing guard;
top-level polymorphic contract obligations remain a separate group concern.

`RecursiveHMJudgement` supplies the generalized no-group RHS target judgement.
Its recursive assumptions use closed templates and one fixed HM bounds vector;
one HM interpretation is shared by the whole derivation. `transportTypes` proves
full RHS specialization through applications, explicit lambda annotations,
local lets, recursive calls and every List/Bool match arm. It preserves captured
free HM template identities and checks caller scope for inserted types.
`transportCounts` transports the whole RHS, its source interpretation, path
assumptions, mono bindings, caller-owned fixed HM types and recursive count
witnesses together, while protecting callee count telescopes/captures. These
are genuine derivation transport theorems, not variable-interface checks alone.

`RecursiveHMEmbedding.typing` embeds every existing checked no-group recursive
derivation at the identity HM interpretation, preserving exact actual intervals,
unchanged source terms, annotation obligations, coverage and inclusions. Its
`certified` theorem applies directly to `RecursiveRHS.Certified`; old executable
RHS certificates therefore have a checked path into the new judgement. Group
acceptance and the production launch still use the original guarded route.

Kernel-checked examples specialize an explicitly annotated identity lambda and
a genuinely self-recursive RHS to arbitrary complete locally closed/scoped
caller bounds, under one fixed recursive interface throughout. All new proofs
use standard Lean axioms only. Full 1774-job build, existing parsed-source
regressions and scratch HM audit pass (28 accepted / eight expected rejections /
zero failures); boundary/whitespace guards pass. No new axioms, placeholders or
partials; HM/D2, Path R, source expressions and production launch unchanged.

Next: join whole-RHS HM and finite-count transport into one universal contract
certificate preserving actual RHS intervals and independently proved demand
inclusion; then connect generalized group-exit/source-annotation obligations
and the executable fixed-HM artifact interpretation seam before enabling the
polymorphic decoder path. Nested groups inside universally checked RHSs remain
outside this deliberately explicit no-group fragment.

### Checkpoint 4u — joint universal recursive RHS contract certificates

`RecursiveHMUniversal.Certified` packages a real recursive RHS derivation at a
checked opaque interface, exact actual HM shape, actual count scope and separate
semantic demand inclusion. HM-template captures and recursive count captures
have explicit freshness premises. `use` jointly quantifies over every finite
scoped count instance and full locally closed/scoped HM vector of exact arity.
It proves the unchanged RHS derivation under the uniformly specialized recursive
environment, preserves actual RHS bounds, proves contract inclusion, and provides
the exact relational HM instance and caller count scope. Count substitution is
performed BEFORE inserting caller HM bounds, including nested caller counts.

`close_counts` certifies the count/HM closure interchange used to specialize
actual intervals rather than overwrite them with the demand. A kernel-checked
self-recursive identity example covers arbitrary full HM bounds and arbitrary
finite scoped count vectors; a concrete equality checks a caller count ID equal
to the callee telescope ID stays caller-owned inside the inserted type.

Existing `RecursiveRHS.Checked` / `LocatedChecked` now carry `actualEq`, linking
their certificate's actual bounds to their typed output's actual bounds. This
local artifact agreement is proved by construction and lets `fromChecked` /
`fromLocatedChecked` reuse genuine checked count scope. These bridges certify
existing executable RHSs in the joint universal judgement without guessing bounds
from their HM shape. They do not remove monomorphic source guards or reclassify
decoded assumptions as accepted implementations.

Full 1775-job build, parsed-source regressions and scratch HM audit pass (28
accepted / eight expected rejections / zero failures); boundary/whitespace guards
pass. New proofs use standard Lean axioms only. No new axioms, placeholders or
partials; HM/D2, Path R and production launch remain unchanged.

Next is exact source-annotation agreement for the closed universal contract,
followed by the generalized group-exit/environment reconciliation and executable
fixed-HM found-payload interpretation. The explicitly specialized environment in
`use` is not yet a whole-group/generalized-export judgement; its reconciliation
must be proved, not assumed from per-member universal certificates.

### Checkpoint 4v — written polymorphic signatures and count-environment agreement

Scoped annotation contracts now retain their exact source decoder equality.
`HMCountScheme.Annotated` keeps that evidence with source count interface and
HM well-formedness; the existing `decode` delegates to `decodeAnnotated` and
still returns the same closed `Scheme` API. This is source provenance for the
contract, not source spans inside `.found` nodes.

`RecursiveHMSigned.BindingOK` is a genuine polymorphic source-signature
judgement: well-formed forall slots, exact HM vector arity, original source
decoding and semantic inclusion in count-first/HM-second specialization of THAT
decoded source demand. `Certified` ties the annotated interface to its joint
universal RHS implementation. `signatureInstances` proves the written signature
at every finite scoped count and full HM bounds instance; no assumption decoder,
single HM instance or root-shape comparison is an implementation certificate.
A kernel-checked self-recursive forall/List signature example covers arbitrary
full caller bounds and finite scoped count vectors.

`RecursiveHMEnvironment.Captured` records count scope for mono captures and
callee fixed HM vectors. `instantiated` proves a member's count instantiation
leaves the common group environment unchanged when that evidence is available.
The closed callee templates are not substituted. `opaqueVector` supplies the
fixed-vector premise automatically for genuine opaque openings; the concrete
recursive example proves the count environment unchanged at every finite scoped
count instantiation. This reconciles count transport, not HM generalized export:
the group's fixed HM vectors still need one uniform whole-group specialization.

Full 1777-job build, parsed-source regressions and scratch HM audit pass (28
accepted / eight expected rejections / zero failures); boundary/whitespace guards
pass. New proofs use standard Lean axioms only. No new axioms, placeholders or
partials; HM/D2, Path R and the guarded production launch remain unchanged.

Next is the exact-node found-payload interpretation seam for more-general HM
RHSs, then joint group/environment/signature acceptance and generalized export.
The polymorphic source judgement above is proof-side; it does NOT enable the
existing executable group decoder or claim whole-program BL support yet.

### Checkpoint 4w — exact-node interpreted found views with genuine typing evidence

`HMFoundView` applies one simultaneous HM interpretation to the discovered
payload at an exact original Core path. Neither the expression artifact, paths,
nor separate source provenance are rewritten. The view is bounds-blind: changing
count intervals in supplied types cannot change its HM result, and inserted
caller identities are not recursively reinterpreted. `AtNode.coherent` proves
agreement with transported actual bounds from original node agreement.

The executable `checkShape` checks interpreted HM agreement and actual caller
count scope, indexed by the exact supplied bounds. It deliberately does not
manufacture an origin proof. `checkTyped` additionally retains a genuine
`RecursiveHMJudgement.Derives` proof for the unchanged original source node.
Twelve regressions cover root/body paths, shape and scope failures, missing or
non-found nodes, simultaneous interpretation, and real typed-node acceptance.

Full 1779-job build, parsed-source regressions and scratch HM audit pass (28
accepted / eight expected rejections / zero failures); boundary/whitespace guards
pass. New declarations use standard Lean axioms only, with no new placeholders
or partials. Existing legacy Pipeline placeholders are unchanged. HM/D2, Path R
and the guarded production launch remain unchanged.

This is an exact-node seam, not yet an interpreted recursive walker or a
generalized group-exit rule. Next work must connect universal RHS specialization
to these views and reconcile the common recursive environment before export;
the polymorphic executable source guards remain intact.

### Checkpoint 4x — universal recursive certificates consume exact found nodes

`RecursiveHMUniversal.actual_transport` identifies count-first/HM-second actual
implementation specialization with the same simultaneous HM interpretation used
by node views. `atNode` consumes a certificate for the exact original node's
source expression and returns `HMFoundView.TypedChecked`: real recursive typing,
interpreted HM agreement, caller scope and unchanged implementation intervals.
`atNode_actual` is a construction equality, not an assumed root reconciliation.

`RecursiveHMSigned.NodeChecked` / `atNode` attach the written source signature
obligation to that SAME typed actual result. `RecursiveHMEnvironment.interpreted`
proves the count-transported environment equals the uniformly HM-interpreted
common environment under captured-vector evidence; its `atNode` reuses that
equality to return the real derivation in the reconciled environment. HM vectors
remain fixed per specialization throughout the recursive group, preserving D2.

Kernel-checked recursive examples quantify over arbitrary finite scoped count
vectors and full HM bounds arguments, linking exact node bounds, written
signature and common environment. An executable nested-List regression confirms
caller counts survive even when their ID equals the callee telescope ID.
Full 1779-job build and parsed-source regressions pass; scratch HM audit remains
28 accepted / eight expected rejections / zero failures. New declarations use
standard Lean axioms only; no new placeholders, partials or production changes.

This connects the universal proof to exact-node consumption, but does not yet
construct those universal certificates with an interpreted executable walker,
introduce generalized group exit, or remove polymorphic source guards. A
more-general inferred RHS still needs explicit machine-binder/signature HM
reconciliation before its original found payloads can supply that walker.

### Checkpoint 4y — checked machine-binder/source-signature HM reconciliation

`HMReconciliation.check` reads a unique machine binder fact for the exact
original RHS path, verifies its generalized identities and captured interface,
and proposes full bounds replacements from a fresh opaque source demand.
Complete interpreted HM agreement, local closure, count scope and both source
and machine freshness are checked. `Checked.machineInstance` proves an exact
relational instance of the ORIGINAL inferred scheme with the selected bounds
vector. Source identities (including unused forall slots) and captures remain
fixed by the interpretation. No expression, `.found` payload or provenance is
rewritten, and no inference is rerun.

Metadata reconciliation is explicitly not RHS acceptance. `checkRHS` additionally
requires a real derivation for the original node, with recursive captured
templates represented in the capture interface. It transports that derivation,
checks exact-node shape and actual count scope, then independently checks actual
bounds inclusion in the opaque source demand. The result retains the same exact
implementation bounds and genuine derivation. Nineteen regressions include a
more-general identity, root/body views, fresh/vacuous slots, missing/duplicate or
wrong-site machine facts, unjustified forall, incompatible HM slots, and both
loose and unjustifiably tight result intervals.

Full 1781-job build and parsed-source regressions pass; scratch HM audit remains
28 accepted / eight expected rejections / zero failures. Pure metadata proofs use
standard Lean axioms only; executable RHS inclusion uses the existing bounds
solver soundness boundary (`checkValid_sound`), not a new axiom. No new placeholders
or partials; HM/D2, Path R and production guards remain unchanged.

The new symbolic RHS seam still needs a universally specialized source HM
interpretation (including count payloads inside its replacements), then executable
walker construction and generalized group export. The original universal
certificate starts at the identity source interpretation, so more-general
reconciled source annotations cannot simply be shoved into it unchanged.

### Checkpoint 4z — universally specialize reconciled source HM interpretations

`RecursiveHMUniversal.Certified` and `RecursiveHMSigned.Certified` now take an
explicit source HM interpretation, defaulting to the old identity interpretation
so existing clients remain compatible. `useInterpreted` transports count payloads
INSIDE that source interpretation before inserting full caller bounds types.
The existing `use` remains its identity-source compatibility theorem. Actual RHS
intervals, inclusion, exact relational HM instances and caller scope are retained.

`HMFoundView.composition` / `specialization` prove the corresponding view at
every original Ty node. Universal and signed `atInterpretedNode` consume the
ORIGINAL found node, not a rewritten virtual expression. Their result retains
the real source-node derivation under the composed source interpretation.
`RecursiveHMEnvironment` also reconciles the common count environment for these
nonidentity certificates, keeping the one fixed HM vector per group member.

`RecursiveHMReconciled.fromChecked` / `fromAnnotated` turn genuinely accepted
symbolic RHS results into universal certificates with their checked source HM
interpretation intact. Recursive closed-template capture representation and count
independence remain explicit proof obligations. The annotated factory additionally
retains the exact decoded written source signature, not merely its HM skeleton.

The 22 reconciliation regressions now include end-to-end symbolic RHS acceptance,
universal written-signature/exact-original-node specialization, count substitution
inside source replacements before nested caller insertion, and carried lambda
annotations using that same interpretation. The caller/callee count-ID collision
regression preserves outer exact [3,3] and inner caller-owned [n,n]; a loose source
result demand does not replace the implementation's precise actual interval.

Full 1782-job build and parsed-source regressions pass; scratch HM audit remains
28 accepted / eight expected rejections / zero failures. Boundary and whitespace
guards pass. New transport, factory and view proofs use standard Lean axioms only;
RHS executable inclusion retains the existing bounds solver soundness boundary.
No new placeholders, axioms or partials; HM/D2, Path R and production unchanged.

Remaining integration is to CONSTRUCT these interpreted RHS derivations with the
executable recursive walker, jointly accept the complete group, and introduce
generalized group export. Current factories consume genuine proof-carrying RHS
results; they do not yet make the existing guarded recursive source decoder accept
polymorphic annotations or deliver full BL/LSP support. Nested groups under
universal RHS checking and local HM-polymorphic bindings remain separate work.

### Checkpoint 4aa — executable interpreted RHS construction (initial slice)

`RecursiveHMAnnotation` now decodes and checks carried source annotations under
the shared HM interpretation. Source counts are substituted before full HM bounds
are inserted; source lexical scope, final caller scope, finite Nat replacements,
parameter HM agreement and actual inclusion are checked independently. Named
source identities therefore denote their full interpreted type, not a stale
opaque variable. Mono local-binding obligations and hints use the same reader.

`RecursiveHMWalk.walk` constructs actual `RecursiveHMJudgement.Derives` evidence
from the unchanged found tree for literals/operators, Nil/Bool/Cons constructors,
mono variables, lambdas, applications, mono local lets and direct count-polymorphic
recursive calls. Cons validates and reports its partial/constructor nodes too.
Local lets require exactly one original machine fact and reject inferred
generalization rather than laundering it into mono typing. Recursive calls retain
the common fixed HM vector; count proposals inspect the CLOSED template and reject
unresolved later-domain coordinates instead of prematurely selecting zero.

`RecursiveHMReconciled.checkLocated` connects this traversal to symbolic RHS
acceptance, independently checking the actual result against the opaque demand.
Existing reconciliation/universal regressions now use executable traversal rather
than hand-supplied RHS proofs. Sixteen annotation and 23 traversal regressions
cover scope, exact-node coverage, false intervals, local binders, self/mutual
fixed-vector recursion, incomplete partial calls and a real `inferFound` artifact.
The real inferred binder is checked, then universally specialized at the original
RHS node without rerunning inference or rewriting source annotations.

The real annotated-forall artifact test documents another integration boundary:
inference intentionally omits machine facts for declared binders and closes their
RHS types to lexical bound slots. The current reconciliation abstraction requires
free generalized identities. An explicit lexical HM bound-slot reader/interface
is still required; adding a made-up inferred fact or reopening/replacing the
expression artifact is not a valid fix. This case is a deliberate test rejection.

Full 1786-job build and parsed-source regressions pass; scratch HM audit remains
28 accepted / eight expected rejections / zero failures. Boundary/whitespace guards
pass. New pure metadata proofs use standard Lean axioms; executable inclusion
uses only the existing bounds solver soundness boundary. No new placeholders,
axioms or partials; HM/D2, Path R and production guards remain unchanged.

Next traversal migrations are bounds-aware List/Bool matches and full recursive
application spines/deferred callbacks. Lexical forall-slot reading, generalized
local lets, complete simultaneous group acceptance and generalized export still
remain; this initial executable slice is not full polymorphic BL/LSP support.

### Checkpoint 4ab — interpreted List/Bool matches and universal artifact regression

The interpreted walker now checks List and Bool matches with original ordered
branch evidence. List coverage uses actual scrutinee intervals; Cons arms receive
the existing path constraints and exact predecessor tail bounds. Bool coverage
is finite constructor coverage, with no invented arithmetic premises. Every arm
retains its actual derivation and semantic inclusion in a variance-correct merged
result, or in an independently checked common demand. Found payloads, constructor
arities and caller scope remain checked inside each arm, with no fallback.

Branch synthesis reuses `BranchMerge`'s solver-independent sound union/intersection
proofs, including arrow variance. Pattern/environment rules and stripFound branch
indexing are proved in the interpreted judgement, so universal HM/count transport
can consume these actual match derivations. The report includes every original
scrutinee/arm node at its original logical path.

The walker matrix has 32 regressions, adding Bool interval union, complete and
wildcard coverage, wrong pattern arity, a false common result demand, interpreted
List element origins, Cons tail path refinements and the empty-list case. A real
`inferFound` List-match artifact is reconciled and checked by traversal, then
universally certified and specialized at the unchanged original RHS node.

Full 1786-job build and parsed-source regressions pass; scratch HM audit remains
28 accepted / eight expected rejections / zero failures. Boundary/whitespace guards
pass. No new placeholders, axioms or partials; executable inclusion retains only
the existing bounds solver soundness boundary. HM/D2, Path R and production guards
are unchanged.

Next is the lexical forall bound-slot reader/interface documented at 4aa, alongside
full recursive spines/deferred callbacks. Generalized local lets, complete group
acceptance/export and BL/LSP launch remain outstanding. The passing real artifacts
here use genuine inferred binders; declared-forall binder artifacts still reject
at the explicitly guarded lexical-slot seam rather than invent machine facts.

### Checkpoint 4ac — simultaneous lexical bound/free HM reader groundwork

`ScopedHMInterpretation.read` / `ty` give separate simultaneous interfaces for
original free identities and lexical bound slots. Inserted full bounds types are
not reinterpreted through either namespace. Missing vector coordinates stay bound,
not Unit or guessed type witnesses. `identity_slots` recovers the existing free
reader, while kernel-checked full-type/count transport and HM shape/coherence
lemmas cover the new reader. Count blindness holds for BOTH replacement interfaces,
retaining Path R.

Six executable tests cover namespace separation, count-first insertion, ordinary
List views, out-of-range and arbitrary supplied slots. A real annotated-forall
identity artifact retains its original bound-slot root, body and carried parameter
annotation; all three read as the SAME fresh opaque identity without any inferred
fact being manufactured for the declared binder. Three generic kernel examples
cover type transport, count transport and bounds-blind views.

Full 1788-job build and parsed-source regressions pass; scratch HM audit remains
28 accepted / eight expected rejections / zero failures. Boundary/whitespace guards
pass. New reader proofs use standard Lean axioms only; no new placeholders,
axioms or partials. HM/D2, Path R and production guards remain unchanged.

This checkpoint supplies the lexical reader, NOT scoped RHS acceptance. The
source-annotation judgement, recursive derivation transport and executable walker
must still carry both interfaces before a declared-forall artifact can be checked.
The initial free-identity walker therefore still rejects that artifact; the passing
new annotated test is explicit metadata/coherence evidence, not a typing proof.

### Checkpoint 4ad — lexical annotation obligations and shared free-only compatibility

`ScopedHMAnnotation.AnnotationOK` carries both simultaneous HM interfaces through
source decoding, full-type specialization, count specialization and stronger path
premises. The original annotation stays unchanged. Executable decoding retains
source lexical count scope, finite replacements and final caller scope; checking
independently validates actual semantic inclusion in the interpreted demand.
Transport proofs update BOTH replacement interfaces, not only free identities.

The existing `HMInterpretation.AnnotationOK` is now the identity-bound-slot
compatibility view of this SAME obligation, with old proof and checker APIs kept
compatible. Existing free-only annotation demands use that same reader; the
`identity_slots` theorem proves equivalence to the previous free mapper. This is
not a second interpretation with separately drifting acceptance rules.

The pure scoped reader no longer imports its own artifact consumers. Exact-node
views now live in `ScopedHMFoundView`, above both reader and original found-node
API. That dependency separation allows recursive typing to import the scoped
annotation layer without a typing/artifact cycle.

Ten executable lexical-annotation tests cover count-first insertion, named
free/bound identities, escaped and undeclared counts, finite witnesses, actual
inclusion and false OUTER and NESTED count assertions. Missing lexical coordinates
are preserved as bound slots, not guessed Unit; these metadata demands do not
assert signature slot arity or local closure. The consuming scoped signature
interface must supply those checks. Two generic kernel examples cover arbitrary
full-type and finite-count obligation transport.

Full 1791-job build and parsed-source regressions pass; scratch HM audit remains
28 accepted / eight expected rejections / zero failures. Boundary/whitespace guards
pass. New pure transport proofs use standard Lean axioms; executable inclusion
uses the existing bounds solver boundary. No new placeholders, axioms or partials;
HM/D2, Path R and production guards remain unchanged.

Next structural work is to parameterize recursive source typing/transport and
its executable walker by the lexical interface, retaining the current identity-
slot API as compatibility. The scoped annotation reader alone does not yet accept
declared-forall RHS artifacts, generalized local lets or groups, and no machine
fact is fabricated for those annotated bindings.

### Checkpoint 4ae — canonical lexical-interface RHS typing and transport

`RecursiveHMJudgement.ScopedDerives` is now the canonical recursive RHS
judgement, carrying independent free-identity and lexical-slot interfaces.
Annotated lambda/mono-let obligations use `ScopedHMAnnotation`; all other rules,
including fixed-HM recursive assumptions and List/Bool matches, remain unchanged.
The original `Derives` API and constructor names are identity-slot compatibility
views of this SAME judgement, not a separately maintained typing system.

Whole-RHS HM and finite-count transport now transform BOTH interfaces. Existing
closed-template capture protection remains explicit. The old transport theorems
specialize these proofs to identity slots. Generic kernel regressions check an
unchanged RHS containing both a bound-slot parameter and a captured free-identity
parameter, and arbitrary full-type/count specialization of both interfaces.

Full 1792-job build passes; scratch HM audit remains 28 accepted / eight expected
rejections / zero failures. Boundary and whitespace checks pass. New judgement
transport and regression proofs use only standard Lean axioms. No new solver
axiom, placeholder or partial; HM/D2, Path R and production guards unchanged.
The executable walker still needs this lexical interface; this checkpoint alone
does not certify a declared-forall artifact or introduce/export a recursive group.

### Checkpoint 4af — executable lexical RHS traversal and exact-node evidence

`RecursiveHMWalk.walkScoped` now consumes both free/lexical interfaces and
constructs `ScopedDerives` on the ORIGINAL stripped RHS. Every primitive,
annotation, Cons payload, application and List/Bool branch reads through the
same simultaneous interface. Logical Core paths and per-node reports remain
unchanged. The original `walk`/`Result` APIs are identity-slot views of this SAME
traversal, with compatibility shape lemmas. Annotation demands/checks now reuse
the canonical `ScopedHMAnnotation` implementation rather than duplicate it.

`ScopedHMFoundView` retains exact-node shape/scope checks plus genuine scoped RHS
derivations. `RecursiveHMWalk.checkLocated` connects the traversal to that node's
original expression and exact address, without annotation rewriting or fake
machine binder facts. Actual bounds remain separate from declared demands;
whole-RHS inclusion is independently checked by the consumer.

Eight executable regressions use real HM-produced annotated-forall identity,
List-match, self-recursive and mutually recursive artifacts, including full
count-bearing caller types inserted AFTER source count substitution. False
written result claims, escaped caller counts and forged found payloads reject.
Free and bound namespaces remain separate even when an inserted slot contains a
free identity also interpreted differently in original source syntax.

Important interface distinction: annotated ordinary lets close their checked RHS
at lexical bvars; recursive inference preserves solved monomorphic free IDs.
Recursive tests match the real source declaration (not invented inferred facts)
where the solved HM shape is an exact declaration instance. A more-general RHS
such as an unconstrained diverging alpha-to-beta loop can satisfy a narrower
written ceiling without its ORIGINAL root being an instance of that ceiling;
the forthcoming declared-interface reconciler must allow the correct direction
of specialization. These tests do NOT license generalization from arbitrary
free IDs. Source lambda bvars not opened by recursive HM inference must not be
silently treated as valid recursive HM inputs by BL.

Full 1793-job build passes; HM scratch audit 28 accepted / eight expected rejects /
zero failures; boundary/whitespace checks pass. New exact-node pure helpers use
standard Lean axioms; executable RHS inclusion retains the existing solver
boundary. No new placeholder/axiom/partial; HM/D2, Path R and production guards
unchanged. Next: joint universal certificates carrying lexical slots and a
checked declared interface, followed by complete group/environment reconciliation.
Generalized local lets, nested groups and deferred full spines remain guarded.

### Checkpoint 4ag — joint universal certificates retain lexical interfaces

`RecursiveHMUniversal.Certified` now retains a trailing, defaulted lexical-slot
interface as well as its free-identity interpretation. Existing certificates
default to identity slots. `useScopedInterpreted` jointly transports BOTH source
interfaces, the actual implementation bounds and the fixed recursive environment
through finite count specialization followed by full caller HM insertion.
Existing free-only `useInterpreted`/`use` views remain compatible.

`ScopedHMFoundView.composition`/`specialization` prove that the final reader agrees
at every original type with this two-stage specialization. `atScopedNode` retains
the exact original source node/address and actual RHS derivation in its final
caller context. `fromScopedChecked` requires a checked opaque signature opening,
genuine exact-node scoped typing, independent actual inclusion and explicit
closed-template HM/count capture protection; the walker alone cannot generalize.

Two real HM artifact regressions take annotated-forall identity/List-match RHSs
through original-node checking at a fresh opaque lexical opening, universal
certificate construction, then count 7 -> 3 and a FULL caller List type whose
inner count still names caller 7. The inner count is preserved rather than
accidentally replaced by the source telescope. Original machine metadata remains
unchanged (annotated bindings have no inference-produced binder fact).

Full 1794-job build passes; scratch HM audit 28 accepted / eight expected rejects /
zero failures; boundary and whitespace checks pass. New universal/coherence
proofs use standard Lean axioms; executable inclusion uses the existing solver
boundary. HM/D2, Path R and production guards unchanged. This does not yet provide
the complete source-site declared-interface reconciler, signed lexical-node
package, recursive group acceptance/export or production BL LSP launch.

### Checkpoint 4ah — written signatures share scoped universal node evidence

`RecursiveHMSigned.Certified` now retains the same defaulted lexical-slot
interface as its universal implementation. `signatureInstances` works for BOTH
interfaces and proves the original written polymorphic signature at every finite
count/full-HM instance; its exact decoded source body cannot be swapped.
Existing identity/free-only signed APIs remain compatible.

`ScopedNodeChecked`/`atScopedNode` attach the written source obligation to the
SAME actual bounds and exact-original-node scoped derivation. The real annotated
identity/List-match regression pipeline now consumes these signed packages,
including the source-count/caller-count identity collision case. It does not
merely compare the final node's HM shape or test one primitive HM witness.

Full 1794-job build passes; scratch HM audit 28 accepted / eight expected rejects /
zero failures; boundary and whitespace guards pass. New signed universal proofs
use standard Lean axioms. No placeholders, partials or new solver axiom. HM/D2,
Path R and production guards unchanged.

Next substantive seam: a checked SOURCE-SITE declared-interface reconciler for
annotated bindings (where omitted inferred machine facts are intentional), then
complete common recursive-environment reconciliation and generalized group
export. It must handle a genuine more-general solved RHS under a narrower
written ceiling, protect captured source free IDs and enclosing lexical slots,
and never infer universal permission merely from arbitrary freeVars or decoded
metadata. The scoped signed package is real universal RHS evidence in an
EXPLICIT specialized environment, not yet that whole-group introduction rule.
Generalized local lets, nested groups, deferred full application spines and
production BL LSP activation remain guarded; no user decision is pending.

### Checkpoint 4ai — actual source-site declared reconciliation and RHS acceptance

`HMDeclaredReconciliation.SourceAt`/`Declaration` select a written annotation
from the exact ORIGINAL found declaration and retain its source-site proof plus
exact RHS node. Annotated bindings need no invented inferred binder fact.
Ordinary annotated lets use their own lexical forall slots; recursive RHSs use
their solved monomorphic free identities. Enclosing lexical scopes remain an
explicit unsupported case in this INITIAL closed-HM-scope interface.

Structural specialization goes from the MORE GENERAL original solved RHS to the
narrower written ceiling, not the reverse. Candidate free identities are only
metadata proposals. Captured surrounding types, free IDs in the source signature
and rigid IDs in carried source annotations are protected. Fresh opaque source
coordinates, unused-slot arity, LC/count scope and exact final shape are checked
independently. There is no machine-generalization certificate fabricated from
`freeVars`, and metadata reconciliation alone cannot accept an implementation.

`HMDeclaredRHS.prepare` selects count telescopes from the SAME lowering metadata
site, retaining resolution and exact selection equalities; unresolved/duplicate
scope rejects. `check` constructs an actual original-node RHS derivation in the
explicit interpreted environment and independently checks its bounds inclusion.
`certify` additionally requires represented CLOSED recursive type captures and
count freshness, yielding a universal signed source-node certificate in that
EXPLICIT specialized environment. No whole-group introduction/export is claimed.

Twenty-two regressions cover real annotated-forall RHSs and the unconstrained
recursive alpha-to-beta loop under its narrower forall/List ceiling, followed
through actual RHS checking and full caller specialization. Caller-owned inner
count 7 survives source count 7 -> 3. False non-recursive result bounds fail
actual inclusion. Source-site mismatch, missing annotations, malformed recursion,
captured/rigid identity specialization, repeated/aliased/unused/out-of-scope HM
coordinates and malformed count metadata are checked separately.

Full 1798-job build and scratch HM audit (28 accepted / eight expected rejects /
zero failures) pass, as do boundary/whitespace guards. New metadata/source-site
and certification proofs use standard Lean axioms; executable RHS inclusion
uses the existing solver boundary. No new placeholders/axioms/partials. HM/D2,
Path R and production guards unchanged.

Next: fix scoped mono-local binder consumption (outer lexical captures are not
new forall slots; annotated locals intentionally omit inferred facts), then
complete common-group reconciliation/generalized export and enclosing-scope
declared interfaces. Generalized local lets, nested groups and deferred full
application spines remain guarded; production BL LSP activation is still later.

### Checkpoint 4aj — mono local binders retain enclosing lexical captures

The canonical scoped RHS walker now distinguishes local source annotations from
inference-produced binder facts. Unannotated locals still require one unique
zero-forall machine fact. Annotated mono locals need their actual source
obligation, not an invented machine fact; optional compatibility facts are
cross-checked, and duplicates reject. Generalized inferred/annotated locals stay
explicitly guarded.

A mono fact can contain bound slots captured from the enclosing source forall.
These are NOT newly generalized local slots, so closed-scheme WF/instantiation
was the wrong check. The walker now checks the mono fact's exact ORIGINAL erased
payload against the actual original RHS payload, before shared interpretation.
The existing scoped judgement then retains real local typing, scope and
independent source inclusion without changing the local generalization policy.

Three real HM-artifact regressions take inferred/annotated mono locals under an
outer forall through universal signed original-node specialization, preserving
count-bearing caller types. A false local interval claim rejects independently.
Three walker regressions cover absent annotated-local facts, mismatched original
mono payloads and the polymorphic annotated-local guard.

Full 1798-job build passes; scratch HM audit 28 accepted / eight expected rejects /
zero failures; boundary/whitespace guards pass. No new placeholders, partials or
axioms; HM/D2, Path R and production guards unchanged. Next is a shared-group
exercise with distinct member count telescopes, then complete common-group
reconciliation/generalized export and enclosing-scope declared interfaces.

### Checkpoint 4ak — shared mutual vector and distinct member count telescopes

Declared reconciliation now retains `openingIds`: checked opaque opening IDs
are EXACTLY the chosen signature coordinates. This matters for vacuous slots
and common-group assembly; runtime equality is independently checked rather
than assumed from opening construction. `signatureIdentityFixed`,
`interpretationScope` and `fixedTypes` expose the corresponding pure invariants.
In particular, fixed recursive arguments equal the full opaque source-coordinate
vector, including unused forall slots.

`HMDeclaredMutualTests` checks BOTH real mutually recursive annotated members
whose original solved RHSs remain more general than their written List ceilings.
They have distinct count telescopes 7/8 but one common fixed opaque HM vector and
one common recursive environment. Shared chosen IDs yield kernel-proved equality
of their fixed vectors. Each actual RHS independently yields a universally
signed exact-original-node certificate. External full caller specialization
preserves both nodes' implementation bounds, all logical paths and the SAME
full fixed argument vector in both specialized environments; caller count 7
inside that inserted vector survives member source-count substitution.

Full 1799-job build passes; scratch HM audit 28 accepted / eight expected rejects /
zero failures; boundary/whitespace guards pass. New identity/vector/scope proofs
use standard Lean axioms; executable inclusion retains the old solver boundary.
No new placeholders, partials or axioms. HM/D2, Path R and production guards
unchanged.

This is evidence for a shared-group exercise, NOT a full arbitrary-group
acceptance/export rule. Next structural work remains reconciling arbitrary
member slot vectors with the common solved HM interface, consuming all member
certificates together and exporting generalized bindings to body checking.
Enclosing lexical declared interfaces, generalized local lets, nested groups
and full/deferred application spines remain guarded; production BL LSP is later.

### Checkpoint 4al — scoped node evidence in the SAME common environment

`RecursiveHMEnvironment.interpreted` now works with arbitrary source lexical-slot
interfaces as well as free interpretations. The existing captured-vector count
reconciliation proof is reused, not duplicated or assumed. `atScopedNode` and
`atScopedSignedNode` retain actual original-node evidence and the written source
obligation in the SAME common environment with only uniform full HM transport;
member count instantiation does not rewrite closed callee templates or its
captured fixed vector.

`capturedBool`/`capturedBool_sound`/`checkCaptured` independently validate the
required premise on actual mono captures and FULL fixed recursive HM arguments.
Counts in CLOSED callee telescopes are not caller-vector counts and are ignored.
The check is performed BEFORE inserting final caller HM types; a vector carrying
member-local counts cannot silently be treated as invariant under specialization.

The real mutual-source regression now obtains checked captured-vector evidence
for both interpreted environments and consumes scoped signed node results in
their common type-only environments. Full fixed argument vectors and caller-owned
inner counts remain equal. Additional regressions reject member-local counts in
mono/fixed-vector captures and accept explicitly captured count-bearing types.

Full 1799-job build passes; scratch HM audit 28 accepted / eight expected rejects /
zero failures; boundary and whitespace guards pass. New scope-check and scoped
common-environment proofs use standard Lean axioms, with no new placeholders,
partials or solver axiom. HM/D2, Path R and production guards remain unchanged.
Next structural work is still the arbitrary-group member-vector reconciliation,
combined acceptance and generalized body/export rule; enclosing lexical declared
interfaces, generalized local lets, nested groups and full spines remain guarded.

### Checkpoint 4am — checked source-HM stability of the common group environment

`RecursiveHMEnvironment.TypesFixed` and its executable checker inspect full
opaque recursive argument vectors and mono captures. `typesFixed` proves that
uniform source reconciliation leaves the actual common environment unchanged,
not merely shape-compatible. Recursive HM payloads must be erase-normal;
member-local count scope remains independently checked by `checkCaptured`.

Both real mutual RHSs now obtain this stability evidence. Negative regressions
reject reconciliation that specializes a sibling's opaque vector or an outer
mono capture. New equality/stability proofs use standard Lean axioms only.

`lake build FHM FHMBounds fhm` passes (1797 jobs); the scratch HM audit remains
28 accepted / eight expected rejects / zero failures. Boundary and whitespace
guards pass. No new placeholders, partials or axioms. HM/D2, Path R and production
BL guards unchanged. Ordered arbitrary-size RHS certificate assembly is next;
generalized export and group-body introduction remain separate.

### Checkpoint 4an — ordered arbitrary-size universally signed RHS assembly

`HMDeclaredGroup` consumes exact sequential source sites and metadata, with one
explicit opaque vector per member. Source annotation/RHS/vector arities are
checked; the ordered indexed family and `memberCount` prevent omitted or extra
RHS certificates. Each actual RHS is checked and universally signed in the SAME
common recursive environment, using checked HM-vector stability, count capture
scope, protected closed templates and count independence.

Shared solved free identities must have equal COMPLETE erased replacement types.
Different member count telescopes need not have equal interval payloads. This
accepts different HM arities without equating every member's entire vector.
Opaque vectors remain checked proposals, not fabricated machine binder facts.

Nine regressions cover all three real HM-produced members (two more-general
mutual RHSs and a mono member) through universal original-node specialization;
skipped/extra members, unrelated coordinates for shared HM variables, aliased
count telescopes and a false final contract reject the whole assembly.
Unannotated recursive contracts remain deliberately guarded in this entry point.

Full `lake build FHM FHMBounds fhm` passes (1799 jobs); HM audit stays 28 accepted /
eight expected rejects / zero failures; boundary/whitespace guards pass. New
assembly/certificate/equality proofs use standard Lean axioms, with executable
inclusion retaining the existing solver boundary. No new placeholders, partials
or axioms; HM/D2, Path R and production BL guards unchanged.

This assembles universal RHS obligations, NOT group-body introduction or export.
Next is automatic compatible opaque-coordinate proposal, then generalized body
interfaces and nested scoped bindings; production BL LSP activation is later.

### Checkpoint 4ao — automatic compatible opaque-coordinate proposals

`HMDeclaredCoordinates` chooses fresh full vectors from source forall arities,
then aligns only opaque slot identities required by shared solved HM shapes.
Finite eager equivalence classes handle transitive/permuted slot relationships
without partial functions or recursive representative lookup. Original count
telescopes stay separate. Freshness includes ALL original found/source types,
outer mono/recursive interfaces and machine binder scheme captures.

The proposal algorithm has no acceptance authority: final vectors run through
the SAME exact-source, full-shape, fresh/distinct-slot, common-environment and
actual universally signed RHS checker. Unsupported equations requiring more
than opaque slot renaming reject explicitly; this is not a completeness claim.
No HM inference/unification is rerun and no per-call HM polymorphism is added.

Six real-artifact regressions cover automatic three-member acceptance, permuted
two-slot signatures, preserved independent vacuous slots, outer capture freshness,
false final bounds and malformed source arities. All prior assembly tests pass.
Full `lake build FHM FHMBounds fhm` passes (1801 jobs), HM audit is still 28 accepted /
eight expected rejects / zero failures, and boundary/whitespace guards pass.
No new placeholders/partials/axioms. Proposal proofs use standard Lean axioms;
actual inclusion retains the existing solver boundary. HM/D2, Path R and
production BL guards unchanged. Generalized body/export and nested scope work
remain ahead; automatic RHS assembly alone does not accept the group body.

### Checkpoint 4ap — actual signed RHS use in discharged caller contexts

`RecursiveHMJudgement.ScopedDerives.assuming` transports the entire canonical
scoped derivation, including recursive uses, nested annotations and List branch
refinements, under a semantic premise implication. No contract premises are
silently appended to the caller's assumptions.

`RecursiveHMCaller` first checks caller HM/count arguments, scope and instantiated
premises using the existing checked interface. It then retains exact original
source-node typing, the written signature, implementation bounds, caller found
shape and independent actual inclusion in ONE proof package under caller Δ.
Whole-package environment transport avoids extracting incoherent independently
cast typed/signature fields. `actual_demand_shape` relates exact implementation
bounds to the same caller HM shape without discarding interval precision.

Seven real automatic-group regressions exercise Int and Char callers, caller-owned
inner count collisions, exact Nil results under a wider written ceiling, unmet
premises, escaping caller counts and unrelated found HM shapes. All earlier HM
and bounds suites remain green; full build passes (1803 jobs), HM audit stays
28 accepted / eight expected rejects / zero failures, boundary/whitespace pass.
Transport/assembly proofs use standard Lean axioms only; positive executable
inclusion/premise answers retain the existing solver boundary. No new placeholders,
partials or axioms. HM/D2, Path R and production guards unchanged.

This is certified RHS caller use, not argument-origin validation, generalized
group-body introduction or runtime closure soundness. Uniform ALL-member HM
specialization in one common group environment is the next assembly proof;
generalized body/export and nested scopes remain ahead.

### Checkpoint 4aq — ALL RHSs specialize under ONE full group HM map

`RecursiveHMUniform.fromCertified` specializes member counts FIRST, removes the
common environment's count transport using checked captured-vector evidence,
then transports actual RHS typing through one uniform full HM map. Its result
is indexed by the SAME `env.map (mapBinding f lc)` for every member, including
opaque slots unused by the member being checked. Implementation and demand
bounds remain distinct; scope and semantic inclusion are proved independently.

`allMembers` constructs ordered universal obligations for EVERY checked original
member under this common full interpretation. `demand_instance`, `Result.signature`
and `atSignedNode` retain the exact written decoder, own-slot vector from the
uniform map, original found node/path and actual implementation bounds. Caller
premise implication transports whole RHS obligations without adding assumptions.

`checkTemplateFixed` validates closed callee template captures, intentionally
distinct from `checkTypesFixed`: uniform group specialization MAY change opaque
fixed argument vectors but MUST NOT rewrite captured source identities.

The real three-member regression includes mutually recursive two-slot signatures
in different orders, distinct count telescopes and a mono member. It consumes the
ALL-member universal family and exact signed original-node results, with full
caller HM arguments containing Int/Char and inner count 7 surviving member count
7 -> 3. A second regression rejects rewriting a closed template's captured HM ID.

Full `lake build FHM FHMBounds fhm` passes (1805 jobs); scratch HM audit remains
28 accepted / eight expected rejects / zero failures. Boundary/whitespace pass.
Uniform transport, signature, exact-node and ALL-member proofs use only standard
Lean axioms. No new placeholders, partial defs or axioms; existing executable
solver trust is unchanged. HM/D2, Path R and production BL guards unchanged.

Next is generalized body/export introduction using these combined obligations,
then enclosing lexical declarations, generalized local lets/nested groups and
full/deferred recursive application spines. No group body or production BL LSP
is accepted merely from this RHS family; those remain separate gates.

### Checkpoint 4ar — ordered generalized exit interfaces retain real source RHSs

`HMDeclaredGroup.Checked.exports` is produced from the ALL-member accepted
certificate family. `exportCount` proves exact output/source-member arity.
`CheckedMembers.select` returns source index, exact original declaration,
universally checked implementation and a kernel-proved exit-array selection
together; signatures cannot be swapped independently of their RHS certificate.

`checkExportedUse` joins this selection with checked caller HM/count arguments,
actual source-node evidence and discharged caller premises. Annotated members
use their exact source declarations; no machine binder fact is invented. This
entry point does not cover unannotated/inferred exports, whose genuinely inferred
schemes remain authoritative on their separate reconciliation path.

Two regressions use actual body function payloads for Int/Char instantiations of
the SAME member across a local-let de Bruijn shift, plus a mono member and a
rejected out-of-range export. Argument-origin and body-environment derivations
remain the consuming body's obligations: exit-use evidence alone is not a
whole-program typing theorem.

Full build passes (1805 jobs); scratch HM audit is 28 accepted / eight expected
rejects / zero failures, boundary/whitespace pass. Selection/arity proofs use
standard Lean axioms; executable caller acceptance retains existing solver trust.
No new files, placeholders, partial defs or axioms. HM/D2, Path R and production
BL guards unchanged. Next is actual generalized body expression typing and the
group-introduction rule that consumes these exports and ALL universal members.

### Checkpoint 4as — actual generalized body checking and closed-group introduction

The initial body slice now lives in the existing `RecursiveHMUniform` module.
Its context deliberately distinguishes mono locals from generalized exits;
recursive RHS assumptions still use the original FIXED-HM recursive context.
`BodyDerives.letRec` consumes the ordered ALL-member universal family and an
actual body derivation under precisely those members' exported interfaces.
This is a checked static fragment, NOT the wider BL runtime progress/preservation
or artifact-coherence theorem campaign.

`checkBody` checks actual original `.found` body occurrences: literals/scalar
operators, List origins, lambdas, mono lets, ordinary applications and direct
origin-backed exported calls. Full HM/count proposals come from certified actual
arguments; specialization, premises, domain inclusion, source local annotations,
original HM shapes and caller count scope are independently validated. The
existing exact-site mono-local metadata checker is shared, not duplicated.

The same actual source export is called at Int then Char across a local binder;
the result retains exact singleton length. Reports include ALL original RHSs,
body nodes and group root, with executable exactly-once coverage checked in the
regression. An HM-valid length-two local contract on a singleton rejects; an
HM-valid vacuously polymorphic local let is explicitly guarded until universal
local-let introduction is implemented. Matches, nested groups and later-origin
deferred calls remain guarded rather than accepted through a legacy fallback.

Full `lake build FHM FHMBounds fhm` passes (1805 jobs); the scratch HM audit is
28 accepted / eight expected rejects / zero failures, boundary/whitespace pass.
No new files, placeholders, partial defs or axioms. The executable body checker
retains only the existing arithmetic solver trust boundary plus standard Lean
axioms; the earlier universal specialization proofs remain solver-independent.
HM/D2, Path R and production BL guards are unchanged. Next is a source-linked
automatic closed-program entry point, then enclosing scopes/generalized locals,
matches, full/deferred spines and product integration; no full-language claim.

### Checkpoint 4at — automatic exact-input closed-program certification

`RecursiveHMUniform.checkClosedProgram` accepts an original root recursive HM
artifact, count metadata and real binder facts. It automatically reconciles
coordinates, checks ALL RHSs, introduces their generalized exports and checks
the original body. `ProgramResult.body.typing` is indexed by the exact INPUT
artifact's erased term, with the checked assembly retained alongside it; the
root source equality rewrites the entire dependent result, not isolated fields.
This adapter covers CLOSED ROOT groups only, not ordinary enclosing program
prefixes, generalized locals or nested groups. Expected bounds are synthesis
guidance, not a fabricated final inclusion theorem. Production BL stays guarded.

The actual Int/Char body regression now uses this automatic entry point. A
forged original root payload rejects independently of correct members/body.
The new nested singleton case revealed a precision gap: the body slice initially
widened the element of `Cons head Nil` via HM-only `shapeTop`. It now follows the
existing RHS walker's head-origin/Nil guidance, independently checking original
HM shape and caller count scope. Full nested singleton bounds survive exported
HM insertion, and every original occurrence remains reported exactly once.

Full `lake build FHM FHMBounds fhm` passes (1805 jobs), with all seven uniform/
body/program regressions green; HM audit remains 28 accepted / eight expected
rejects / zero failures from this batch. Boundary/whitespace pass. No new files,
placeholders, partial defs or axioms; exact-input acceptance retains the existing
solver trust boundary. HM/D2 and Path R are unchanged. Remaining gates are mixed
enclosing scopes/generalized locals, matches, full/deferred origins, product
integration, wider runtime/artifact proofs and consolidation of replaced routes.

### Checkpoint 4au — generalized body List/Bool branches consume actual origins

One `BodyBranchContext`/branch traversal in the existing uniform module connects
generalized body typing to the established semantic List and finite Bool
coverage APIs. List arms open mono head/tail bindings ahead of the SAME exported
interfaces; tail bounds use predecessors and constructor path premises remain
explicit. A full-bounds equality, not an HM-only reconstruction, connects the
actual scrutinee with that branch context. Structural branch-erasure/index
lemmas are shared with the original RHS walker instead of copied.

`BodyDerives.match_` requires coverage, every valid pattern, every actual arm
derivation and each arm's semantic inclusion into the result. Branch merging
uses the existing proved `BranchMerge` upper combination. Expected result
guidance still checks actual arms independently; it cannot manufacture success.
Each original match/scrutinee/arm occurrence stays in the exact-path report.

Real HM-artifact regressions cover Bool branch results of length zero/one, List
tail calls across Cons's two-binder export shift, semantically justified Nil-only
and Cons-only matches, and rejection of Nil-only coverage on a singleton. Extra
guards reject malformed Cons arity even behind a wildcard, incomplete Bool
coverage and a false common demanded result. Generalized locals, nested groups,
ordinary enclosing program prefixes and full/deferred origin spines still have
their existing gates; no production BL fallback is enabled.

Full `lake build FHM FHMBounds fhm` passes (1805 jobs); all 15 uniform/body/
program regressions pass. Scratch HM audit: 28 accepted / eight expected rejects /
zero failures. Boundary/whitespace pass.
No new files, placeholders, partial defs or axioms. The new static fragment is
not a claim of completed BL runtime safety/artifact-coherence proofs; executable
acceptance retains the existing arithmetic solver boundary. HM/D2 and Path R
are unchanged. Consolidation is still tracked below, not falsely called done.

### Checkpoint 4av — established premises transport the whole generalized body

`BodyDerives.assuming` transports an entire body derivation whenever the new
caller/path context semantically establishes the old premises. It covers source
lambda/mono-local obligations, generalized uses, every List/Bool arm with its
constructor refinements and ALL-member recursive introduction. The checked
source-annotation transport lemmas are shared with `RecursiveHMJudgement`, not
reimplemented. Coverage transport reuses `ListBranches.Covers.assuming`; Bool
coverage remains independent of arithmetic premises.

Generalized uses preserve the exact HM/count arguments and instantiated contract;
only the proof discharging its premises changes. A real origin-backed symbolic
caller test with symbolic count `n` (identity 7) succeeds when `1 <= n` is
established and rejects without that premise. Callee requirements are NEVER merely
appended to the caller's assumptions. A kernel-checked exact-input program example consumes the whole-body
transport theorem, including group introduction.

Full `lake build FHM FHMBounds fhm` passes (1805 jobs), including all 17 uniform/
body/program regressions. Whole-body and branch-coverage transport proofs use
only standard Lean axioms; scratch HM audit remains 28 accepted / eight expected
rejects / zero failures. Boundary/whitespace pass.
This is pure logical transport, not another execution path or a runtime safety
claim. No new files, placeholders, partial defs or axioms; HM/D2, Path R and
production BL guards remain unchanged. Full mixed-scope nested introduction and
deferred/full-spine origins remain the next substantial assembly work.

### Checkpoint 4aw — one exported HM/count instance for a full actual body spine

The generalized body walker now gathers every supplied source argument before
choosing a single HM/count vector. It reuses `RecursiveSpine.Syntax` and its
original callee payload rather than introducing another parser or source rewrite.
`StructuralApplication.proposeArguments` gathers full HM-slot proposals across
ALL supplied domains; `CountProposal.proposeArguments` continues scanning the
CLOSED template so inserted caller counts never become callee origins.

`useBodySpine` uses the existing exported-variable rule ONCE at the head and the
ordinary application rule at EVERY original frame. Each domain inclusion,
intermediate/final original `.found` payload and count scope is independently
checked. Ordinary non-exported applications share the same application helper.
The earlier single-argument exported route is replaced, not retained in parallel.

Real closed-group regressions cover different HM/count slots first supplied by
different arguments, and an earlier compound count resolved by a later direct
origin. Invalid earlier domain bounds, conflicting repeated full HM slots,
unsupplied later count origins and a forged intermediate payload all reject.
A separate origin-backed caller case specializes callee count 7 to one while
preserving caller count 7 inside BOTH full HM arguments and every source node.

Full `lake build FHM FHMBounds fhm` passes (1805 jobs), with all 24 uniform/body/
program regressions green. HM audit: 28 accepted / eight expected rejects / zero
failures. Boundary/whitespace pass.
This checkpoint concerns generalized body exports. Full count-only recursive RHS
spines, deferred argument checking, nested groups/generalized locals and program
prefixes remain separate gates; no production BL fallback is enabled. No new
files, placeholders, partial defs or axioms. Existing solver trust is unchanged;
HM/D2 and Path R remain untouched.

### Checkpoint 4ax — full recursive RHS spines retain the common fixed HM vector

The original-node RHS walker now gathers every actual argument of a recursive
application spine before proposing ONE count vector. It uses the same existing
source-indexed `RecursiveSpine.Syntax`, but does NOT propose new HM arguments:
the callee's common-group fixed HM vector remains authoritative throughout.
`useScopedSpine` derives the head with the existing recursive-variable rule and
checks every application using ordinary application typing, semantic domain
inclusion and the original HM payload under the SAME source interpretation.
The older single-argument recursive route is replaced, not duplicated.

Actual self-recursive two-argument groups now assemble universally before their
generalized Int/Char body uses, including compound-first/later-direct count
origins. The mutual regression gives the two members distinct count telescopes
while their RHSs keep a shared fixed HM vector; separate body uses reverse the
full Int/Char caller vector across a mono-local binder shift. Every original RHS,
body and application occurrence remains reported exactly once. Direct negative
tests reject changing the recursive head's fixed HM instance and forging an
intermediate original payload.

Full `lake build FHM FHMBounds fhm` passes (1805 jobs), including all 27 uniform/
body/program regressions and the three new fixed-RHS cases. This batch's HM audit
remains 28 accepted / eight expected rejects / zero failures; boundary/whitespace
pass. No new typing rule, source rewrite, files, placeholders, partial defs or axioms.
The existing executable arithmetic-solver trust boundary is unchanged; HM/D2,
Path R and production BL guards remain unchanged. Deferred expected-dependent
arguments, nested/generalized-local introduction and enclosing program prefixes
remain the next assembly gates, not silently accepted through old engines.

### Checkpoint 4ay — independently originated count vectors precede deferred RHS checks

Recursive RHS spine preparation now preserves optional independent argument
proofs: a failed unguided argument has NO invented bounds, origin or typing.
`CountProposal.proposeOrigins` requires every coordinate in a deferred domain to
have an independent supplied origin before instantiation. Only then does
`completeScopedSpine` check missing arguments against the real instantiated
callee domains and independently check EVERY application inclusion/payload.
The common HM vector stays fixed, and no count re-proposal incorporates guided
pending arguments. Missing proofs cannot survive in the accepted RHS derivation.

The real self-recursive program supplies a List lambda inside its RHS, whose
parameter cannot be inferred unguided. A later actual argument supplies its
count; the callback then produces a real source-indexed lambda/body proof.
The program's explicitly annotated external callback lets the full closed-program
slice verify the resulting singleton and exactly-once coverage of every node.
A wrong deferred callback fails actual function-domain inclusion; an all-deferred
call without an independent count origin remains explicitly unsupported.

This replaces the independent-only RHS completion rather than adding a parallel
engine. No new files, typing rules, placeholders, partial defs or axioms. Solver
trust, HM/D2, Path R and production BL guards are unchanged. Generalized BODY
callbacks with later HM origins still need staged partial-HM guidance; this
checkpoint does not infer full caller bounds from a found-type skeleton.

Validation: `lake build FHM FHMBounds fhm` passes (1805 jobs), including
all 30 uniform/body/program regressions; boundary and whitespace checks pass.

### Checkpoint 4az — generalized local RHSs may consume earlier exports

The mixed body environment now distinguishes an earlier generalized export
from both recursive group contracts and monomorphic binders.  Its source rule
checks a real `HMCountScheme.Use`; its runtime rule requires supported concrete
bounds/type arguments; and its capture invariants preserve the export's whole
scheme rather than pretending it is a fixed monotype.  Type/count freshness and
fixed-capture evidence are threaded through the same universal local
certificate, group certificate and reconciliation route.

Consequently a later generalized local can use an earlier generalized local in
its own universally checked RHS.  The production `RecursiveHMWalk` validates
the full exported application spine inside that RHS, including the original
found HM payload.  The real regression introduces polymorphic `id`, defines
polymorphic `copy` through it, and specializes `copy` at Char; the result keeps
its runtime theorem and exact source-node coverage.

This extends the existing binding/certificate family rather than adding an
alternate local engine.  No new placeholder, partial definition or axiom was
introduced.  Full `lake build FHM FHMBounds fhm` passes (1806 jobs); HM/D2,
Path R and the solver trust boundary are unchanged.

### Checkpoint 4ba — later origins discharge deferred generalized-body arguments

The generalized body spine now stages optional independently checked argument
proofs.  `StructuralApplication.proposeOrigins` and the existing count-origin
collector inspect the entire supplied spine before specialization: a missing
argument contributes no proposal, and each type/count coordinate occurring in
its domain must come from another independently checked argument.  Coordinates
absent from every domain retain the established irrelevant-witness convention.

After the ONE whole-spine HM/count instance is checked, every missing argument
is traversed again under its actual instantiated domain.  Acceptance therefore
contains a genuine derivation, runtime evidence and original source paths for
the formerly unguided expression.  Every application frame still checks actual
domain inclusion and its original `.found` payload; no guided argument is fed
back into origin proposal, and an unresolved partial call rejects.

The end-to-end regression uses `∀a n. (List[n] a → List[n] a) → List[n] a →
List[n] a`.  An unannotated List identity callback is initially uncheckable;
the later singleton Char argument supplies both `a` and `n`, after which the
callback checks with exact singleton bounds and full runtime/source coverage.
A callback returning `Nil` fails actual inclusion, and the partial call fails
the independent-origin guard.  This replaces the independent-only body-spine
completion, not a parallel execution path.  No new files, typing rules,
placeholders, partial definitions or axioms were introduced.

Validation: `lake build FHM FHMBounds fhm` passes (1806 jobs), including the
positive staged-body case and both independent negative guards; boundary and
whitespace checks pass.

### Checkpoint 4bb — nested groups retain captured lexical runtime environments

The generalized body judgment and its runtime fundamental theorem now admit a
checked recursive group above an arbitrary represented outer environment.
`EnvAt.tieGroupCaptured` first closes the already realized outer terms into each
source RHS, then ties the mutually recursive replacements by the same finite
observation-budget induction as a root group.  A substitution-composition proof
shows this is exactly Core's single `inner ++ outer` closing substitution; outer
terms are neither captured by the new binders nor duplicated.

Generalized exits additionally prove that every later full-HM opening leaves
outer mono types and fixed recursive argument vectors unchanged.  The group
checker records their presence in the guarded outer type list, so this transport
is derived from opening freshness and the original erase-normality check rather
than from the weaker template-only freshness condition.

The source-linked body walker now assembles nested groups at their exact Core
path, checks every member universally, extends the precise `BodyCapture`, checks
the nested body under its generalized exits, and returns one ordinary `letRec`
derivation with runtime evidence.  Regressions cover capture of an earlier group
export, capture through an intervening monomorphic let, exact singleton bounds,
complete source-node coverage, and rejection of a false inner result ceiling.
No fallback traversal, reconstructed source node, termination premise, partial
definition, placeholder or new axiom is introduced.  HM/D2, Path R and the
existing arithmetic-solver trust boundary remain unchanged.

### Checkpoint 4bc — one canonical checker starts before recursive groups

`RecursiveHMUniform.checkProgram` now starts the source-linked body traversal in
an explicitly empty represented environment.  It checks ordinary literals,
applications, lambdas, monomorphic/generalized lets and matches before, around
and after recursive groups, instead of requiring the whole artifact to have a
root `letRec`.  A group encountered at any supported path goes through the same
all-member assembly, captured-environment introduction and runtime theorem as
checkpoint 4bb; there is no prefix-specific group rule.

The regression wraps a captured nested group inside an ordinary lambda and
application, retains exact singleton bounds, covers every original Core node
once and extracts the closed runtime-safety theorem.  Tightening the nested
group to a false length-two ceiling still fails its independent inclusion check.
The older `checkClosedProgram` root result remains temporarily for compatibility;
the new entry point is the intended verified program boundary for report/LSP
wiring.  No new axiom, placeholder, partial definition or fallback engine is
introduced.

### Checkpoint 4bd — the source report adapter uses the canonical checker

`RecursiveFound.synthNodes` now invokes `RecursiveHMUniform.checkProgram`
instead of the earlier fixed-HM `RecursiveGroup` traversal.  Consequently the
typed-provenance adapter, its exact-once Core/source join, and the parsed `.fhm`
regression suite all exercise the same verified whole-program judgment that
supports ordinary prefixes, generalized declarations and nested groups.  The
suite remains build-failing on any failed expectation; its printed PASS lines
are a readable report, not a substitute for an exit failure.

Parity exposed one real shape omission: nullary custom types such as `Bool`
were already present in the bounds syntax, subtyping and runtime model, but the
typed decoder rejected them.  `Typed.shapeTop` and `Typed.annotation` now decode
that existing case, while the freshness, type-specialization and count-transport
proofs establish that it is fixed under their respective maps.  The parsed
suite covers scalar recursive Bool results as well as List/count behavior.

Expectations that represented superseded implementation frontiers now record
the established semantics: an annotated recursive member has one fixed
in-group HM instance and may be generalized only on exit; its RHS is checked
against the declared instance even when inference found a more-general type;
and declared generalized ordinary lets are checked rather than rejected.
Unsupported inferred generalized lets and recursive groups nested inside a
universally interpreted recursive RHS remain explicit errors.  No fallback to
the retired checker, placeholder, partial definition or new axiom is introduced.

### Checkpoint 4be — `run --bl` consumes the canonical artifact

The CLI now parses spans, performs provenance-aware lowering and runs found
inference once in both modes.  `run --bl` passes that exact typed artifact to
`RecursiveFound.synthNodes`; successful execution erases the accepted inferred
term, while HM mode continues to apply its ordinary surface exhaustiveness
check.  The legacy surface-erasing `Check` and `BoundCovers` pipeline no longer
decide BL acceptance or coverage.

The deprecated erase package remains temporarily in the unverified CLI only
to preserve the spelling of authored bounds annotations in `ProgramReport`.
It supplies no input to inference, checking, evaluation or node provenance.
The canonical checked body bounds now supply the BL program result display.

Product smoke checks establish that `bl-live.fhm` and the ascribed List-lambda
fixture typecheck and evaluate, while invalid interval and Nil-only coverage
fixtures fail at the bounds stage through the new checker.  Older showcase
fixtures now honestly expose three remaining fragment boundaries instead of
falling back: annotation holes/escape inference, unannotated recursive exports,
and runtime support for parameterized nominal data such as pairs.  These are
language-coverage tasks, not adapter defects.  HM editor/CLI smoke remains
28 accepted, eight expected HM rejections and zero audit failures.

### Checkpoint 4bf — editor diagnostics consume the canonical artifact

Bounds editor mode now runs `RecursiveFound.synthNodes` over the same
provenance-rich inferred term as `run --bl`. Successful node reports supply
binding, occurrence, arbitrary-expression and program-result bounds; failure is
surfaced as a diagnostic while the already valid HM/provenance symbols remain
available. No source span or display reconciliation participates in acceptance.

The report presentation aligns the canonical checker's locally opened type
variables structurally with the HM artifact at the same Core path and with the
validated declaration enclosing that path. Consequently authored names such as
`a` and count names such as `n` survive through a declaration, lambda parameter
and RHS expression instead of leaking worker IDs or unrelated alpha names.
Hovering whitespace within an authored compound expression selects the smallest
enclosing expression report and displays its checked `BoundsTy`.

`diagnose --hm` retains Path-R bounds blindness, `--bl` requests the canonical
checker, and `--auto` selects it exactly when the parsed program contains `BL`.
The batch default remains HM for compatibility; VS Code and the web editor use
auto, with an explicit VS Code setting to force either mode. The mode detector
and CLI policy now live under `FHM/Unverified`; Live no longer imports the legacy
proof-holed `Bounds.Pipeline` merely for an enum/detector. Build-failing editor
guards cover canonical success, named skolems/counts, whitespace expression
hover and retained symbols on rejection. HM semantic smoke, the 36-file scratch
audit, VS Code lifecycle checks and the exhaustive web hover sweep remain green.

### Checkpoint 4bg — nominal bounds retain their parameter structure

The typed decoder no longer treats every non-`List` nominal type as nullary.
Shape demands and authored annotations recurse through all nominal arguments,
and semantic subtyping checks equal constructors, equal arities and pointwise
argument subtyping. `List` remains the distinguished interval-carrying type and
rejects malformed arity rather than silently becoming an ordinary nominal.

The corresponding freshness, simultaneous HM-specialization and count-
transport lemmas now recurse over nominal argument lists as well. Thus the
executable generalisation is covered by the same proof transformations used by
declarations and recursive groups; it is not merely a pretty-printing or editor
exception. Build-failing regressions cover nested exact List bounds inside a
Pair-shaped type, pointwise subtyping and arity rejection. The full verified
bounds suite remains green without a new axiom or placeholder. This establishes
the static shape layer needed for parameterized nominal runtime support; it does
not yet claim runtime meaning or traversal rules for Pair construction/matches.

### Checkpoint 4bh — saturated Pair construction has a runtime meaning

`Pair` joins primitive values, arrows, bounded Lists and Bool in the explicit
runtime-supported fragment. A positive-budget Pair value is the existing erased
saturated constructor applied to two values, with each field satisfying its own
full `BoundsTy`; support, downward closure, count substitution, simultaneous HM
specialization and semantic subtyping all recurse pointwise through those field
meanings. The construction theorem uses only the existing small-step value
rules, and a corresponding `TermAt.pair` composes evaluation of both fields.

The canonical generalized-body judgment and source-linked walker now have a
dedicated saturated-Pair rule. They validate the inferred full and partial
constructor payloads, preserve exact child reports and attach the runtime proof
only when both children possess one. Parsed build-failing regressions establish
both a Pair containing an exact bounded List and nested Pairs with independently
precise List origins. Pair pattern elimination remains the next separate unit:
construction support does not pretend that coverage or field opening is proved.

### Checkpoint 4bi — Pair elimination opens semantically justified fields

Pair matches now have a verified one-constructor coverage checker: either a
`Pair` pattern of arity two or a wildcard is exhaustive, and no other pattern is
accepted by the bounds traversal. The runtime fundamental theorem follows the
existing erased match reduction, extracts the two concrete constructor fields,
and opens the branch environment with their full left/right `BoundsTy`
meanings. This is semantic field evidence, not a reconstruction from erased HM
shape; nested List intervals therefore remain exact inside Pair patterns.

Both ordinary annotated RHS derivations and the canonical generalized-body
judgment carry the Pair construction/elimination rules through premise
strengthening, source-slot agreement, simultaneous HM specialization, count
transport, ordinary-environment conversion and runtime readiness. The source
walker validates full and partial Pair constructor payloads, checks Pair branch
coverage, and emits the same exact per-node reports consumed by CLI/editor
diagnostics. The `.fhm` regression exercises a Pair field containing `BL 2 2
Int`, then safely performs a List match on that opened field; a wildcard Pair
match separately checks the zero-binder exhaustive case. The complete bounds
suite and executable smoke test remain green without a new axiom or placeholder.

## Consolidation / retirement ledger

The file count is not a target architecture. Many files are regression suites;
several traversal generations are also retained during verified migration.
Retirement must follow replacement/parity, not delete useful proofs blindly.

- `RecursiveWalk` / `RecursiveGroup` / `RecursiveFound`: earlier checked fixed-HM
  program path. Retire executable duplication after universal generalized body
  traversal covers matches, nested groups, curried/deferred calls and ordinary
  program prefixes, with its current positive/negative regressions ported.
- `SchemeWalk` / `ScopedWalk` and their adapters: intermediate non-recursive
  scheme/count slices. Reuse their algebra/proofs; consolidate their independent
  entry points once the canonical mixed-scope/program path subsumes their tests.
- `HMReconciliation` / `RecursiveHMReconciled` are NOT obsolete merely because
  declared reconciliation exists: they consume real INFERRED machine facts,
  whereas `HMDeclared*` consumes original annotated declarations. Preserve this
  semantic distinction while consolidating shared helpers.
- Legacy `Pipeline` / root-only `synthRoot` / old product adapters: retire after
  the new verified report/program route has CLI/LSP parity; existing proof holes
  in that legacy path are not silently accepted as part of the new metatheory.
- `ScopedHMInterpretation`, count/free algebra and exact-node readers are shared
  foundations, not additional language engines. Keep provenance/front-end/LSP
  reconciliation outside verified syntax, as already agreed.

Final cleanup must make the active entry point and supported language obvious,
leave one authority per acceptance rule, and organize tests so experimental or
superseded engines do not masquerade as the finished verified language.
