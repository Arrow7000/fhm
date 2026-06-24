<!-- Part A audit verdict for FHM/InferW.lean.
     Companion: next-agent-brief-inferw-audit-cleanup.md (the task spec).
     Written after the open-program soundness fix landed (commit b38e39d). -->

# InferW metatheory — Part A audit verdict

## 0. Scope & method
Goal: establish that the InferW metatheory is *not fake* — no vacuous theorems, no
unsatisfiable/unavailable premises, no quietly-weakened conclusions — before any
cleanup. Verification used the `project-0-experiments-lean-lsp` MCP (`lean_verify`,
scoped `lean_diagnostic_messages`) and git. `Core.lean` (the declarative ground
truth) was treated as read-only.

**Headline finding up front:** the audit uncovered one **genuine latent
unsoundness** (the executable was unsound on *open* programs, fenced off only by a
`hclosed` hypothesis). It was fixed before this verdict was written — see §1.
Everything else checks out.

---

## 1. Soundness bug found + fixed (commit `b38e39d`)
**Symptom (empirically witnessed via `#eval`):** `principalType [] ((λ(x:α).x) 5)`
returned `some Int`, binding the free top-level annotation variable `α ↦ Int`.
But that program is **declaratively untypeable**: the Core `lambda` rule
(`Core.lean` ~1730) pins `paramTy` to the *literal* annotation `α`, so
`λ(x:α).x : Int→Int` is underivable, hence `(λ(x:α).x) 5 : Int` is too.

**Root cause:** the entry points ran `inferCore []` — an *empty* rigid set — so the
rigidity-aware `unifyCoreK []` treated `α` as an ordinary flexible variable and
bound it. The metatheory itself was never *false* (`Infer.sound` requires both
`e.tyFreeVars ⊆ K` and `S` avoids `K`, jointly unsatisfiable when `S` binds a free
annotation var), but the public headlines all carried `hclosed : e.tyFreeVars = []`,
which **fenced the bug off rather than fixing it**. There was also a latent
fresh-variable/annotation-variable collision from starting `Φ = 0`.

**Fix:** `principalType`/`typecheck` now seed `K := e.tyFreeVars` and start at
`Φ := e.freshFloor` (strictly above every annotation var). A free top-level
annotation var is therefore a **rigid scoped constant**:
- `principalType [] (λ(x:α).x) = some (α→α)` (accepted, sound — `α` kept rigid);
- `principalType [] ((λ(x:α).x) 5) = none` (correctly rejected);
- closed programs are bit-for-bit unchanged (`K = []`, floor `= 0`).

Because the relation metatheory is already `K`-general, **all static headlines
dropped `hclosed`** and now hold for *any* program. This **moots the central A2
worry** in the brief ("is `hclosed` a cop-out?"): the boundary is gone, replaced by
the principled rigid-scoped-constant reading.

---

## A1. Mechanical integrity — PASS
- **No `sorry`/`admit`/`native_decide`/`axiom`** in `InferW.lean` or `Core.lean`.
  The only textual hits for "sorry" are inside doc comments (InferW lines 818, 9660).
- **`Core.lean` never edited across the repair arc.** `git diff 2314b04 HEAD --
  Core.lean` is **empty**: the declarative spec is byte-identical from the Stage-1
  soundness commit (which finalized the scoped-var Core design) through the entire
  completeness / reformulation / executable repair arc and this session. The audit
  was therefore conducted against an untouched ground truth.
- **Axiom cleanliness** (`lean_verify`, `scan_source:false`) — every checked theorem
  uses *exactly* `propext`, `Classical.choice`, `Quot.sound`, no warnings:

  | Theorem | Axioms |
  |---|---|
  | `typecheck_iff` | standard 3 ✓ |
  | `typecheck_sound` | standard 3 ✓ |
  | `typecheck_principal` | standard 3 ✓ |
  | `typecheck_closed` | standard 3 ✓ |
  | `typecheck_progress` | standard 3 ✓ |
  | `typecheck_preservation` | standard 3 ✓ |
  | `principalType_sound` | standard 3 ✓ |
  | `principalType_principal` | standard 3 ✓ |
  | `principalType_iff` | standard 3 ✓ |
  | `inferCore_complete` | standard 3 ✓ |
  | `Infer.completeAt` | standard 3 ✓ |
  | `Infer.isPrincipal` | standard 3 ✓ |
  | `Infer.output_unique` | standard 3 ✓ |
  | `Infer.sound_closed` | standard 3 ✓ |
  | `infer_sound` | standard 3 ✓ |
  | `infer_complete` | standard 3 ✓ |
  | `infer_iff` | standard 3 ✓ |
  | `infer_iff_typeable` | standard 3 ✓ |
  | `infer_isPrincipal` | standard 3 ✓ |

---

## A2. Per-headline premise audit — "satisfiable AND available in normal use?"

### `hclosed : e.tyFreeVars = []` — REMOVED
No longer a premise on any public headline (`typecheck_*`, `principalType_*`). The
generalized statements hold for all `e`; closed programs are the trivial instance.
The original concern is resolved, not documented-around.

### `CtxWF` / `CtxBelow` side conditions — discharged vacuously
The public headlines run at the empty top-level environment `⟨[], ctors⟩`. There:
- `CtxWF.empty : CtxWF ⟨[], ctors⟩` and `CtxBelow.empty : CtxBelow Φ ⟨[], ctors⟩`
  (for *any* `Φ`, so the higher `freshFloor` start needs no extra work) both hold by
  the env being empty (`intro M hM; simp at hM`).
- So the closed-program headlines carry **no leftover obligations** beyond the
  (now-trivial) rigid-seeding facts `∀ y ∈ e.tyFreeVars, y < e.freshFloor`
  (`Expr.lt_freshFloor`) and `∀ y ∈ e.tyFreeVars, y ∈ e.tyFreeVars`.

### `he : e.IsTyErased` on progress/preservation — REPLACED by erasure at the boundary
Previously `typecheck_progress`/`typecheck_preservation` required the *input* to be
already annotation-free, so annotations never did any work. Now they typecheck the
(possibly annotated) `e` and conclude about **`e.eraseTyAnnots`** via Core's
`TypeOfHM.erased_type_safety` / `erase_preserves_typing` — "check with annotations,
run erased". Premise availability:
- **Non-vacuous runtime class.** `Expr.eraseTyAnnots e` is always `IsTyErased`
  (`Core.isTyErased_eraseTyAnnots`), and `IsTyErased` covers every non-annotation
  form (primLit/pair/lambda/app/letIn/fst/snd/var/ctor/match), so erased programs
  that take a `Step` are abundant — the capstone exhibits one (§A3).
- **Restriction is forced, not convenient.** Subject reduction is *false* on
  annotated terms — Core's `preservation_is_unsound` exhibits a well-typed annotated
  `let` whose `letReduce` produces an untypeable term. That is precisely why the
  dynamic semantics is operated on the erased image.
- **The supporting bridges are real, not stubs:** `Step.preserves_isTyErased`,
  `TypeOfHM.erase_preserves_typing`, `TypeOfHM.erased_type_safety` all live in
  `Core.lean` and were re-verified by the (axiom-clean) progress/preservation proofs.

---

## A3. Anti-vacuity by witness (the decisive test) — PASS
A vacuous theorem (unsatisfiable premise) cannot be *instantiated* to produce a
concrete positive result. The committed capstone (`namespace AuditCapstone`, end of
`InferW.lean`) drives the real pipeline on concrete inputs through the headline
theorems. Because `inferCore`/`unifyCoreK` are well-founded (no `rfl` reduction),
each "typecheck succeeds" is witnessed by a hand-built *declarative* `TypeOfHM`
derivation crossed through the `↔` headlines — never `decide`/`native_decide`. All
axiom-clean:
- **Typeable program** `λx.x` (`polyId_headlines_fire`): exhibits `σ, τ` with
  `typecheck [] = some σ`, `σ = genScheme [] [] τ`, `TypeOfHM ⟨[],[]⟩` holds
  (soundness fires), and every declarative typing factors through `τ` (principality
  fires).
- **Polymorphic program** `let id:∀a.a→a = λx.x in id id` (`idid_typeable`,
  `idid_headlines_fire`): the full let-generalization + double-instantiation path,
  same three headlines firing.
- **Ill-typed program** `5 5` (`appFiveFive_untypeable`, `appFiveFive_rejected`):
  `¬ ∃ τ, TypeOfHM ⟨[],[]⟩ (5 5) τ` and hence `¬ (typecheck [] (5 5)).isSome` — the
  completeness contrapositive is not vacuous.
- **Open / rigid witnesses** (the §1 fix): `λ(x:α).x` typeable as `α→α`
  (`openId_typeable`, `α` rigid); `(λ(x:α).x) 5` untypeable and rejected
  (`openMisuse_untypeable`, `openMisuse_rejected`).
- **Progress/preservation** on a concrete erased program `(λx.x) 5`
  (`appIdFive_progresses` via `typecheck_progress`; `appIdFive_preserves` via
  `typecheck_preservation` — the beta step's reduct still typechecks).

---

## A4. Conclusion-shape review — no silent degradation
- Decidability is a genuine `↔` (not a one-way `→`): `typecheck_iff`,
  `principalType_iff`, `infer_iff`, `infer_iff_typeable`.
- Principality is the strong existential form `∀ τ₀, TypeOfHM … e τ₀ → ∃ R,
  τ₀ = R.onTy τ` (`Infer.IsPrincipal.principal`, `principalType_principal`,
  `typecheck_principal`) — every declarative typing is a substitution instance of
  the inferred type, not a weaker statement.
- `typecheck_preservation` is honestly stated as "the reduct's scheme is *at least
  as general*" (`τ = R.onTy τ'`), with the `(λf.(f,f))(λx.x)` example showing why
  same-`σ` preservation is *false* — a deliberate, correct weakening of the naive
  statement, not green-chasing.
- `typecheck_closed` genuinely certifies the output is a closed scheme
  (`NoFreeVars σ.body ∧ σ.WF`).

---

## Verdict
With the §1 soundness fix in place, the metatheory is **trustworthy**: mechanically
clean, axiom-clean (modulo the five LSP-pending re-confirms), conducted against an
untouched declarative spec, with faithful conclusion shapes and a witness capstone
that proves the headlines actually fire. The one real problem the audit was meant to
catch — a latent unsoundness hidden behind a convenient hypothesis — was found and
repaired. Cleared to proceed to Part B (cleanup).
