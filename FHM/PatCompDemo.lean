import FHM.PatComp
import FHM.Decls
import FHM.Pretty

/-! # A guided tour of verified pattern-match compilation

This file is a **pedagogical companion** to `FHM/PatComp.lean` (the "Option B"
campaign — see `briefs/design-memo-verified-pattern-compilation.md`). It proves
nothing new; every theorem it cites already exists, fully proved, in
`PatComp.lean`. Its only job is to walk through the campaign's headline results
on small, fully concrete examples, in increasing order of sophistication, so
that the shape of the result — and exactly what is and isn't claimed — is easy
to see.

## The journey

1. **Compile a tiny match, look at the tree.** `compile` turns a *matrix* of
   nested surface patterns into a `DTree` — a flat sequence of single-level
   ctor-tag tests (`switch`), following Maranget's matrix-decomposition
   algorithm.
2. **The reference semantics.** `firstMatch` (and its matrix-shaped cousin
   `matrixSem`) is the naive, obviously-correct "try each source pattern in
   order" interpreter — the SPEC everything else is judged against.
3. **The compiled tree agrees with the reference, always.**
   `compile_correct_surface` says `evalDTree`-on-the-compiled-tree and
   `firstMatch`-on-the-source-patterns are literally the same function. We
   instantiate this on concrete scrutinees.
4. **The compiled tree is not just an abstract spec — it is real code.**
   `emit` lowers a `DTree` to actual Core `match_`/`letIn` syntax; the
   headline operational theorem (`lowerMatch_adequate_of_typed`) says the
   emitted term *reduces, by Core's real small-step relation*, to the right
   branch body with the right values substituted in. We build a tiny typed
   universe and instantiate this unconditionally on a concrete well-typed
   scrutinee — including the keystone lemma (`compile_ctorSwitches`) that
   discharges the one structural side-condition (`CtorSwitches`) straight from
   the scrutinee's Core typing derivation.
5. **Exhaustiveness for free.** `compile_surface_total_iff` says the compiled
   tree is total on a value iff the source patterns are — a match with no
   catch-all really does fail exactly where the naive semantics says it does,
   and nowhere else.

Throughout, "value" means a Core `Expr` accepted by `SmallStep.IsValue`; ctor
data is decomposed with `SmallStep.getCtorArgs`. Captures come out in
**pre-order** (left-to-right occurrence order of the source pattern) — see
`compile`'s "pop rule" documentation in `PatComp.lean` for why that is the
tricky part of the whole campaign. -/

namespace PatCompDemo

open PatComp
open SmallStep (IsValue IsCtorChain getCtorArgs Step)

/-! ## Part 0 — a tiny universe of values and patterns

We work with a `Maybe a` type (`Just`/`Nothing`) and a `Pair` type, the same
minimal universe `PatComp.lean`'s own executable test suite uses. Nothing here
needs a `CtorEnv` yet — `compile`/`firstMatch`/`emit` are all untyped, purely
structural functions over `Expr`/`Surface.Pattern`. -/

/-- The Core value `n : Int`. -/
def vInt (n : Int) : Expr := .primLit (.int n)

/-- The Core value `Just v`. -/
def vJust (v : Expr) : Expr := .app (.ctor ⟨"Just"⟩) v

/-- The Core value `Nothing`. -/
def vNothing : Expr := .ctor ⟨"Nothing"⟩

/-- The Core value `Pair a b`. -/
def vPair (a b : Expr) : Expr := .app (.app (.ctor ⟨"Pair"⟩) a) b

/-- Source pattern `Just x`. -/
def pJustX : Surface.Pattern := .ctor ⟨"Just"⟩ [.name ⟨"x"⟩]

/-- Source pattern `Nothing`. -/
def pNothing : Surface.Pattern := .ctor ⟨"Nothing"⟩ []

/-! ## Part 1 — compiling a match, and looking at the tree

Consider the surface match

```
match scrut with
| Just x  => ⋯      -- branch 0
| Nothing => ⋯      -- branch 1
```

`initMatrix [pJustX, pNothing]` builds the starting one-column pattern matrix
(row `i` = branch `i`, nothing captured yet); `compile [[]] M` compiles it,
where `[[]]` is the one-element occurrence vector naming the scrutinee itself
(`[]` = "the root value"). -/

/-! The decision tree `compile` produces for `Just x | Nothing`: a single
    `switch` on the scrutinee's own occurrence (`[]`), with a `Just` case that
    (after popping its irrefutable field-0 column) captures that field and
    fires branch 0, a `Nothing` case that fires branch 1 with no captures, and
    `fail` as the default (there is no catch-all). This is checked by pattern
    matching against the literal tree shape — `#guard` runs it through Lean's
    compiled evaluator, not the kernel, so `compile`'s well-founded recursion
    poses no difficulty. -/
#guard match compile [[]] (initMatrix [pJustX, pNothing]) with
  | .switch [] [(⟨"Just"⟩, 1, .leaf 0 [[0]]), (⟨"Nothing"⟩, 0, .leaf 1 [])] .fail => true
  | _ => false

-- A visual look at the same tree (via the derived `Repr` instance):
#eval compile [[]] (initMatrix [pJustX, pNothing])

/-! A more interesting example: a NESTED pattern, and the "pop rule" pathology
    the design memo calls out as the load-bearing discovery of the whole
    campaign. Consider

```
match scrut with
| (x, Just y) => ⋯    -- branch 0
| _           => ⋯    -- branch 1
```

    `initMatrix` puts the WHOLE pattern `(x, Just y)` into one column at the
    root occurrence `[]`, so the tree necessarily starts with a `Pair` test
    (we don't yet know the scrutinee is even a pair). But ONCE inside that
    `Pair` case, column 0 (`x`) is irrefutable — nothing to switch on — while
    column 1 (`Just y` / wildcard-from-branch-1) still has a ctor test. A
    naive compiler that captures a binding only when it finally switches would
    capture `y` (forced by the switch on column 1) BEFORE `x` (whose column is
    never switched on) — violating the surface's left-to-right capture order.
    `compile`'s pop rule consumes the irrefutable `x` column immediately
    (silently — no tree node), so `x` is captured before the tree ever
    descends into the `Just`/`Nothing` test on the pair's second field. -/

/-- Source pattern `(x, Just y)`. -/
def pPairXJustY : Surface.Pattern := .pair (.name ⟨"x"⟩) pJustX

/-! The compiled tree: an outer switch on `Pair` (unavoidable — arity 2,
    fields at occurrences `[0]`/`[1]`); inside that case, `x`'s column is
    popped invisibly, then an inner switch on occurrence `[1]` tests
    `Just`/`Nothing`; its `Just` leaf's captures are `[[0], [1, 0]]` — `x`
    (popped earlier) BEFORE `y` (just bound by this switch) — pre-order,
    exactly as `firstMatch` would report, even though `x` never got a switch
    node of its own. -/
#guard match compile [[]] (initMatrix [pPairXJustY, .wildcard]) with
  | .switch [] [(⟨"Pair"⟩, 2,
        .switch [1] [(⟨"Just"⟩, 1, .leaf 0 [[0], [1, 0]])] (.leaf 1 []))]
      (.leaf 1 []) => true
  | _ => false

#eval compile [[]] (initMatrix [pPairXJustY, .wildcard])

/-! ## Part 2 — the reference semantics

`matchPat`/`firstMatch` is the trusted, "obviously correct" surface-level spec:
try each pattern in turn, first match wins, report its captures in pre-order.
No matrices, no trees — just direct structural recursion on `Surface.Pattern`.
This is what the compiled tree is proven against. -/

-- `Just x` matches `Just 5`, capturing `[5]`.
#guard match matchPat (vJust (vInt 5)) pJustX with
  | some [.primLit (.int 5)] => true | _ => false

-- `Just x` refutes `Nothing`.
#guard (matchPat vNothing pJustX).isNone

-- first-match order: branch 0 (`Just x`) wins over branch 1 on `Just 5` …
#guard match firstMatch (vJust (vInt 5)) [pJustX, pNothing] with
  | some (0, [.primLit (.int 5)]) => true | _ => false

-- … and branch 1 (`Nothing`) wins on `Nothing`.
#guard match firstMatch vNothing [pJustX, pNothing] with
  | some (1, []) => true | _ => false

-- the pop-rule pathology at the SPEC level: captures come out `[x, y]` in
-- source order, regardless of which column happens to force the match.
#guard match firstMatch (vPair (vInt 1) (vJust (vInt 2))) [pPairXJustY, .wildcard] with
  | some (0, [.primLit (.int 1), .primLit (.int 2)]) => true | _ => false

/-! ## Part 3 — the correctness theorem, instantiated

`PatComp.compile_correct_surface` is the H1 headline:

```
theorem compile_correct_surface (v : Expr) (ps : List Surface.Pattern) :
    evalDTree v (compile [[]] (initMatrix ps)) = firstMatch v ps
```

No hypotheses at all — it holds for *every* scrutinee `v` and pattern list
`ps`. Below we apply it to the concrete data from Parts 1–2: the equality
`example`s below typecheck by literally handing the general theorem the
concrete arguments (no `rfl`/`decide` needed, and hence no dependence on how
`compile` happens to be compiled/reduced) — this is the "instantiate on
concrete examples" step, made completely explicit. -/

/-- On `Just 5`, evaluating the compiled tree and running the naive reference
    semantics are the SAME computation (not merely provably equal — this term
    literally IS `compile_correct_surface` applied to concrete data). -/
example :
    evalDTree (vJust (vInt 5)) (compile [[]] (initMatrix [pJustX, pNothing]))
      = firstMatch (vJust (vInt 5)) [pJustX, pNothing] :=
  compile_correct_surface (vJust (vInt 5)) [pJustX, pNothing]

-- …and that common value is concretely `some (0, [5])`:
#guard match evalDTree (vJust (vInt 5)) (compile [[]] (initMatrix [pJustX, pNothing])) with
  | some (0, [.primLit (.int 5)]) => true | _ => false

/-- Same instantiation on `Nothing`: both sides pick branch 1, no captures. -/
example :
    evalDTree vNothing (compile [[]] (initMatrix [pJustX, pNothing]))
      = firstMatch vNothing [pJustX, pNothing] :=
  compile_correct_surface vNothing [pJustX, pNothing]

/-- And on the pop-rule example: the compiled tree's `[[0], [1,0]]`-indexed
    captures and the spec's pre-order `[x, y]` captures denote the same
    values, on the nose. -/
example :
    evalDTree (vPair (vInt 1) (vJust (vInt 2)))
        (compile [[]] (initMatrix [pPairXJustY, .wildcard]))
      = firstMatch (vPair (vInt 1) (vJust (vInt 2))) [pPairXJustY, .wildcard] :=
  compile_correct_surface (vPair (vInt 1) (vJust (vInt 2))) [pPairXJustY, .wildcard]

/-! `compile_correct_surface` is itself the `occs = [[]]`/`M = initMatrix ps`
    specialisation of the more general matrix-level theorem `compile_correct`,
    which is what is actually proved by induction (mirroring `compile`'s own
    recursion via `compile.induct`). We record its general shape here so the
    "matrix" vocabulary from Part 1 is visibly the thing being inducted on: -/
#check @compile_correct
-- compile_correct (root : Expr) (occs : List Occ) (M : Matrix) :
--   ∀ vals, (width invariant) → (occs fetch to vals) → (captures fetchable) →
--     evalDTree root (compile occs M) = matrixSem root vals M

/-! ## Part 4 — the operational bridge: real Core reduction

Correctness-as-equal-functions (Part 3) is a DENOTATIONAL statement about
`evalDTree`, an interpreter that never touches Core's actual reduction
machinery. The second half of the campaign (H2, "adequacy") is an
OPERATIONAL statement: the Core term `emit` actually *renders* — nested
`match_`/`letIn` syntax — really reduces, by Core's real `SmallStep.Step`
relation, to the right branch body with the right values substituted in. This
is materially different from H1: H1 could in principle hold even if `emit`
produced ill-formed or non-reducing garbage that merely happened to *denote*
the right thing under `evalDTree`; H2 is the guarantee that running the
compiled program actually goes there.

`lowerMatch scrut ps bodies` packages one whole surface match: it lets-binds
the scrutinee (so the tree's occurrence vector starts `[[]]` = "var 0 holds
the scrutinee") and emits the compiled tree against it.

The fully general theorem is `lowerMatch_adequate`, but it carries one
structural side-condition, `CtorSwitches root tree`: informally, "every
switch the tree's evaluation *actually reaches* tests a value that really is
a constructor chain" — true for any well-typed scrutinee (a switch only ever
tests an ADT-typed position), false in general for ill-typed junk. Rather
than hand-discharge that condition, we go straight for the theorem that
DOES discharge it — `lowerMatch_adequate_of_typed` — by building a tiny real
`CtorEnv` and a real Core typing derivation for a concrete scrutinee. -/

/-! ### A two-constructor `Maybe` type, by hand

`PatComp.lean` never needs a `CtorEnv` (it is deliberately Core+SurfaceLang
only — see the design memo, decision 10), so there is no existing demo env to
import; we build the smallest possible one directly as a `CtorEnv := List
(CtorName × Ctor)`, discharging each `Ctor`'s `bound`/`closed` obligations by
hand (they are one-line for these two constructors). This is the same shape
`FHM.Decls.elabDecls` would produce from a `type Maybe a = Just a | Nothing`
declaration — we just skip the elaborator since the env is small enough to
write directly. -/

/-- `Just : a → Maybe a`. -/
def justCtor : Ctor where
  paramCount := 1
  tyName := ⟨"Maybe"⟩
  contents := [.bvar 0]
  bound := by
    intro ty hty
    simp only [List.mem_singleton] at hty
    subst hty
    exact .bvar (by omega)
  closed := by
    intro ty hty
    simp only [List.mem_singleton] at hty
    subst hty
    exact .bvar

/-- `Nothing : Maybe a`. -/
def nothingCtor : Ctor where
  paramCount := 1
  tyName := ⟨"Maybe"⟩
  contents := []
  bound := by simp
  closed := by simp

/-- The two-constructor `Maybe` environment. -/
def maybeCtors : CtorEnv := [(⟨"Just"⟩, justCtor), (⟨"Nothing"⟩, nothingCtor)]

/-- `Just : Int → Maybe Int` types under `maybeCtors`, instantiating the
    scheme's one parameter at `Int`. -/
theorem justCtorTyped :
    TypeOfElabHM ⟨[], maybeCtors⟩ (.ctor ⟨"Just"⟩)
      (.arrow (.prim .int) (.customTy ⟨"Maybe"⟩ [.prim .int])) :=
  TypeOfElabHM.ctor (tyArgs := [.prim .int]) rfl
    (by
      intro tyArg htyArg
      simp only [List.mem_singleton] at htyArg
      subst htyArg
      exact .prim)
    (.arrow (.bvar rfl) (.customTy (.cons (.bvar rfl) .nil)))

/-- `Just n : Maybe Int` for any integer literal `n`. -/
theorem justAppliedTyped (n : Int) :
    TypeOfElabHM ⟨[], maybeCtors⟩ (vJust (vInt n)) (.customTy ⟨"Maybe"⟩ [.prim .int]) :=
  .app justCtorTyped .primLitInt

/-- `Nothing : Maybe Int`. -/
theorem nothingTyped :
    TypeOfElabHM ⟨[], maybeCtors⟩ vNothing (.customTy ⟨"Maybe"⟩ [.prim .int]) :=
  TypeOfElabHM.ctor (tyArgs := [.prim .int]) rfl
    (by
      intro tyArg htyArg
      simp only [List.mem_singleton] at htyArg
      subst htyArg
      exact .prim)
    (.customTy (.cons (.bvar rfl) .nil))

/-- `Just n` is a genuine Core VALUE (a fully-applied ctor chain over a
    literal), for any `n`. -/
theorem justValue (n : Int) : IsValue (vJust (vInt n)) :=
  .ctorApp (.ctor _) (.primLit _)

theorem nothingValue : IsValue vNothing := .ctor _

/-! ### The patterns are well-formed against `Maybe Int`

`GPatWF`/`GPatWFList` is the type-directed well-formedness relation that lets
`compile_ctorSwitches` (below) discharge `CtorSwitches` purely from typing: a
`gctor c` test is well-formed only at `c`'s own ADT type, with sub-patterns
fitting `c`'s instantiated field types. Both our patterns normalise to
`gctor` tests at exactly `Maybe Int` — `Just x ↦ gctor Just [gbind]`,
`Nothing ↦ gctor Nothing []` — so both are trivially well-formed. -/

theorem justPatternWF :
    GPatWF maybeCtors (.gctor ⟨"Just"⟩ [.gbind]) (.customTy ⟨"Maybe"⟩ [.prim .int]) :=
  GPatWF.gctor rfl rfl (.cons (.bvar rfl) .nil) (.cons .gbind .nil)

theorem nothingPatternWF :
    GPatWF maybeCtors (.gctor ⟨"Nothing"⟩ []) (.customTy ⟨"Maybe"⟩ [.prim .int]) :=
  GPatWF.gctor rfl rfl .nil .nil

/-- Every row of the initial matrix for `[Just x, Nothing]` is well-formed
    against the scrutinee type `Maybe Int` — the `hwf` hypothesis
    `compile_ctorSwitches`/`lowerMatch_adequate_of_typed` need. -/
theorem maybeMatrixWF :
    ∀ r ∈ initMatrix [pJustX, pNothing],
      GPatWFList maybeCtors r.pats [.customTy ⟨"Maybe"⟩ [.prim .int]] := by
  intro r hr
  simp only [initMatrix, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact .cons justPatternWF .nil
  · exact .cons nothingPatternWF .nil

/-! ### The keystone: `CtorSwitches` discharged from typing alone

`compile_ctorSwitches` is the integration keystone the design memo's status
log calls out as the hardest late-breaking fix of the whole campaign (a
global, non-path-sensitive version of `CtorSwitches` was briefly FALSE before
being reshaped — see the memo's 2026-07-08 entry). Applied here, it needs
only: the scrutinee is a well-typed `Maybe Int` value, and the patterns are
well-formed against that type — both of which we just built. -/

theorem maybeCtorSwitches (n : Int) :
    CtorSwitches (vJust (vInt n)) (compile [[]] (initMatrix [pJustX, pNothing])) :=
  compile_ctorSwitches (justAppliedTyped n) (justValue n) [pJustX, pNothing] maybeMatrixWF

/-! ### The unconditional headline, on a concrete value

`lowerMatch_adequate_of_typed` composes: `compile_correct_surface` (H1),
`compile_ctorSwitches` (the typing discharge above), and `emit_adequate`/
`emitLets_adequate` (H2, the "leaf-lets" capture-binding argument) into one
statement with NO residual structural side-condition — only scrutinee typing
and pattern well-formedness, both ordinary front-end obligations. -/

/-- The branch bodies of `match _ with | Just x => x + 1 | Nothing => 0`. -/
def maybeBodies : Nat → Expr :=
  fun i => if i = 0
    then .app (.app (.primBinOp .intAdd) (.var 0 [])) (vInt 1)
    else vInt 0

-- The reference semantics: on `Just 41`, branch 0 fires, capturing `[41]`.
theorem maybeJust41Matches :
    firstMatch (vJust (vInt 41)) [pJustX, pNothing] = some (0, [vInt 41]) := rfl

/-- **The concrete instance of the headline theorem.** Lowering
    `match Just 41 with Just x => x + 1 | Nothing => 0` and running it under
    Core's REAL small-step relation reaches `(x + 1).substN 0 [41]` — no
    hand-waving about `CtorSwitches`, just scrutinee typing
    (`justAppliedTyped`) and pattern well-formedness (`maybeMatrixWF`). -/
theorem maybeJust41Reduces :
    Relation.ReflTransGen Step
      (lowerMatch (vJust (vInt 41)) [pJustX, pNothing] maybeBodies)
      ((maybeBodies 0).substN 0 [vInt 41]) :=
  lowerMatch_adequate_of_typed (justAppliedTyped 41) (justValue 41)
    [pJustX, pNothing] maybeBodies maybeMatrixWF maybeJust41Matches

/-- Cross-check: actually running the emitted term with Core's *executable*
    step function (fuel-bounded iteration, exactly what `maybeJust41Reduces`
    promises is reachable) really does land on `42`. This does not re-derive
    `maybeJust41Reduces` — it independently confirms, by brute-force
    execution, that the target the theorem names is the value we expect. -/
private def runN : Nat → Expr → Expr
  | 0, e => e
  | n + 1, e =>
    match SmallStep.step e with
    | some e' => runN n e'
    | none => e

#guard match runN 32 (lowerMatch (vJust (vInt 41)) [pJustX, pNothing] maybeBodies) with
  | .primLit (.int 42) => true | _ => false

-- The `Nothing` branch, same theorem, same env — reaches literal `0`.
theorem maybeNothingMatches :
    firstMatch vNothing [pJustX, pNothing] = some (1, ([] : List Expr)) := rfl

theorem maybeNothingReduces :
    Relation.ReflTransGen Step
      (lowerMatch vNothing [pJustX, pNothing] maybeBodies)
      ((maybeBodies 1).substN 0 []) :=
  lowerMatch_adequate_of_typed nothingTyped nothingValue
    [pJustX, pNothing] maybeBodies maybeMatrixWF maybeNothingMatches

#guard match runN 32 (lowerMatch vNothing [pJustX, pNothing] maybeBodies) with
  | .primLit (.int 0) => true | _ => false

/-! ## Part 5 — exhaustiveness comes along for free

`compile_surface_total_iff` says the compiled tree selects SOME branch on `v`
iff the source spec does — pointwise, no extra proof effort, immediate from
H1 (`compile_correct_surface`) since the two sides are literally equal. A
match with no catch-all really is incomplete exactly where — and only where —
the naive reference semantics says it is. -/

#check @PatComp.compile_surface_total_iff
-- compile_surface_total_iff (v : Expr) (ps : List Surface.Pattern) :
--   (evalDTree v (compile [[]] (initMatrix ps))).isSome ↔ (firstMatch v ps).isSome

/-- `[Just x]` alone (no `Nothing`/catch-all branch) is non-exhaustive: on
    `Nothing`, both the compiled tree and the reference spec correctly refuse
    to pick a branch. -/
example :
    (evalDTree vNothing (compile [[]] (initMatrix [pJustX]))).isSome
      ↔ (firstMatch vNothing [pJustX]).isSome :=
  compile_surface_total_iff vNothing [pJustX]

#guard (evalDTree vNothing (compile [[]] (initMatrix [pJustX]))).isNone
#guard (firstMatch vNothing [pJustX]).isNone

/-- Add the catch-all back (`[Just x, Nothing]`) and totality is restored on
    the same value — again witnessed by the very same theorem. -/
example :
    (evalDTree vNothing (compile [[]] (initMatrix [pJustX, pNothing]))).isSome
      ↔ (firstMatch vNothing [pJustX, pNothing]).isSome :=
  compile_surface_total_iff vNothing [pJustX, pNothing]

#guard (evalDTree vNothing (compile [[]] (initMatrix [pJustX, pNothing]))).isSome
#guard (firstMatch vNothing [pJustX, pNothing]).isSome

/-! ## Coda: what this file did and didn't do

* Parts 1–3 are purely DENOTATIONAL: `compile`/`evalDTree`/`firstMatch` never
  touch Core's execution model. `compile_correct_surface` is unconditional —
  it holds for every `Expr`, well-typed or not.
* Part 4 is OPERATIONAL and needs typing: `lowerMatch_adequate_of_typed`
  requires the scrutinee to be a well-typed value of some ADT
  (`TypeOfElabHM ⟨[], ctors⟩ root (.customTy T tyArgs)`, `IsValue root`) and
  the source patterns to be well-formed against that type (`GPatWFList`).
  Both were built by hand here for a two-constructor toy `Maybe`; in the real
  front end they come from the surface elaborator's own typing pass.
* Part 5's totality is pointwise in the scrutinee, not yet lifted to "for
  every well-typed `v` of the ADT, some branch fires" (that lift, plus the
  connection to Core's `AllMatchesExhaustive`/`progress`, is bridge-integration
  work noted as future scope in the design memo).
* Nothing here needed `sorry` or a new `axiom` — every step either computes
  (`#guard`/`#eval`, Lean's compiled evaluator) or applies an already-proven
  `PatComp.lean` theorem to concrete data. -/

end PatCompDemo
