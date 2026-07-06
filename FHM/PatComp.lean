import FHM.Core
import FHM.SurfaceLang

/-! # Verified pattern-match compilation (definitions + executable pipeline)

This module is the "Option B" campaign (see
`briefs/design-memo-verified-pattern-compilation.md` and
`briefs/next-agent-brief-verified-pattern-compilation.md`): compile the surface
language's **nested** patterns into Core's **flat, single-level** `match_`, with
a machine-checked proof that the compiled code selects the same branch and
binds the same values as the surface match — for every well-typed scrutinee.

This file contains the full **definition layer** and the executable pipeline:

* `matchPat` / `firstMatch` — the trusted surface-side SPEC: which branch of a
  nested surface match fires on a given (Core) value, capturing which values.
* `GPat` / `norm` — surface patterns normalised to a single generic-ctor form
  (pair/cons/list are ctor tests in disguise), so the matrix algorithm handles
  ONE refutable pattern shape.
* `Row` / `Matrix` / `matrixSem` — the pattern-matrix vocabulary the compiler
  recurses over, with its (root-relative) first-match semantics.
* `DTree` / `evalDTree` — the decision-tree IR and its occurrence-indexed
  interpreter: the shared denotational pivot both proof halves are stated
  against.
* `compile` — the naive leftmost-column (Maranget-style, heuristics-free)
  matrix compiler. Termination is by the lexicographic measure
  (total `gctor` count, column count) — see `Matrix.ctorCount`.
* `emit` — render a `DTree` as nested Core `match_`es, PARAMETRIC in the leaf
  bodies (crucial: `Step` runs on *elaborated* terms, so adequacy must not
  bake in literal bodies). Leaves re-bind their captures with `letIn`s so the
  body sees capture `j` at de Bruijn index `j` ("leaf-lets" design).

No theorems yet beyond what termination requires; the proof campaign (H1
algorithm correctness, H2 adequacy against `SmallStep.Step`) is stated and
scheduled in the design memo. Nothing here touches Core.

Value convention: a "value" throughout is a Core `Expr` that `SmallStep.isValue`
accepts; ctor data is decomposed with `SmallStep.getCtorArgs` (name + args in
application order). The surface has no independent runtime.

Capture-order convention (load-bearing!): captures are reported in **pre-order**
(left-to-right occurrence order) of the surface pattern. The compiler preserves
this because it resolves columns strictly left to right: the **pop rule** (see
`compile`) consumes an all-irrefutable leading column instead of ever switching
past it, so a bind is consumed exactly when its column is leftmost. Without the
pop rule, appending to `Row.captured` would produce out-of-order captures
whenever a later column forces the switch. -/

namespace PatComp

open SmallStep (getCtorArgs)


/-! ## Occurrences

A path of field indices into a ctor-chain value: `[]` is the scrutinee itself,
`[1]` its second ctor argument, `[1, 0]` the first argument *of* that, etc.
Occurrences are the single source of truth for binding: the surface name
resolver maps names to occurrences, and `emit` maps occurrences to de Bruijn
indices — both read the same leaf vector. -/

abbrev Occ := List Nat

/-- Navigate a value along an occurrence. `none` if the path doesn't exist
    (a non-ctor value, or a field index out of range). -/
def fetch : Expr → Occ → Option Expr
  | v, [] => some v
  | v, i :: rest => do
    let (_, args) ← getCtorArgs v
    let a ← args[i]?
    fetch a rest


/-! ## The surface-side spec: `matchPat` and `firstMatch`

THE trusted artefact of the whole campaign. Everything else — the matrix
algorithm, the decision tree, the emitted Core — is proven against these two
little functions. They are deliberately direct structural recursions over
`Surface.Pattern`, readable by inspection. -/

mutual

/-- `some vs` = the pattern matches value `v`, capturing sub-values `vs` in
    pre-order (left-to-right occurrence order); `none` = the pattern refutes
    `v`. `name` captures the whole value, `wildcard` captures nothing;
    `pair`/`cons`/`list` are `Pair`/`Cons`/`Nil` ctor tests in disguise. -/
def matchPat (v : Expr) : Surface.Pattern → Option (List Expr)
  | .name _ => some [v]
  | .wildcard => some []
  | .ctor cn ps => do
    let (c, args) ← getCtorArgs v
    guard (c = cn ∧ args.length = ps.length)
    matchPats args ps
  | .pair p q => do
    let (c, args) ← getCtorArgs v
    match args with
    | [a, b] => do
      guard (c = .mk "Pair")
      pure ((← matchPat a p) ++ (← matchPat b q))
    | _ => none
  | .cons hp tp => do
    let (c, args) ← getCtorArgs v
    match args with
    | [h, t] => do
      guard (c = .mk "Cons")
      pure ((← matchPat h hp) ++ (← matchPat t tp))
    | _ => none
  | .list items => matchListPat v items

/-- Pointwise matching of a value vector against a pattern vector,
    concatenating captures. `none` on length mismatch or any refutation. -/
def matchPats : List Expr → List Surface.Pattern → Option (List Expr)
  | [], [] => some []
  | v :: vs, p :: ps => do pure ((← matchPat v p) ++ (← matchPats vs ps))
  | _, _ => none

/-- A `[p₁, …, pₙ]` list pattern unrolled against `Cons`/`Nil` chains. -/
def matchListPat (v : Expr) : List Surface.Pattern → Option (List Expr)
  | [] => do
    let (c, args) ← getCtorArgs v
    match args with
    | [] => do guard (c = .mk "Nil"); pure []
    | _ => none
  | p :: ps => do
    let (c, args) ← getCtorArgs v
    match args with
    | [h, t] => do
      guard (c = .mk "Cons")
      pure ((← matchPat h p) ++ (← matchListPat t ps))
    | _ => none

end

/-- First-match semantics over a whole branch list: the index of the first
    branch whose pattern matches, with its captures. This is what "which branch
    fires, binding what" MEANS for a surface match. -/
def firstMatch (v : Expr) : List Surface.Pattern → Option (Nat × List Expr)
  | [] => none
  | p :: ps =>
    match matchPat v p with
    | some vs => some (0, vs)
    | none => (firstMatch v ps).map (fun (i, vs) => (i + 1, vs))


/-! ## Generic patterns (`GPat`) and normalisation

The matrix algorithm wants exactly one refutable pattern form. `norm` maps the
six surface constructors onto three: generic ctor test, bind, wildcard. -/

inductive GPat
  /-- Test for ctor `name` at arity `args.length`, then match the fields. -/
  | gctor (name : CtorName) (args : List GPat)
  /-- Irrefutable; captures the whole value (surface `name`). -/
  | gbind
  /-- Irrefutable; captures nothing. -/
  | gwild
  deriving Repr

mutual

/-- Normalise a surface pattern: `pair` ↦ `Pair`, `cons` ↦ `Cons`, `list` ↦
    unrolled `Cons`/`Nil` — capture structure preserved verbatim. -/
def norm : Surface.Pattern → GPat
  | .name _ => .gbind
  | .wildcard => .gwild
  | .ctor cn ps => .gctor cn (normList ps)
  | .pair p q => .gctor (.mk "Pair") [norm p, norm q]
  | .cons hp tp => .gctor (.mk "Cons") [norm hp, norm tp]
  | .list items => normListPat items

def normList : List Surface.Pattern → List GPat
  | [] => []
  | p :: ps => norm p :: normList ps

def normListPat : List Surface.Pattern → GPat
  | [] => .gctor (.mk "Nil") []
  | p :: ps => .gctor (.mk "Cons") [norm p, normListPat ps]

end

mutual

/-- `matchPat`'s twin over generic patterns (the form `matrixSem` builds on).
    The factoring `matchPat v p = matchG v (norm p)` is a theorem of the
    campaign, NOT a definition — the spec stays surface-level. -/
def matchG (v : Expr) : GPat → Option (List Expr)
  | .gbind => some [v]
  | .gwild => some []
  | .gctor c pats => do
    let (name, args) ← getCtorArgs v
    guard (name = c ∧ args.length = pats.length)
    matchGs args pats

def matchGs : List Expr → List GPat → Option (List Expr)
  | [], [] => some []
  | v :: vs, p :: ps => do pure ((← matchG v p) ++ (← matchGs vs ps))
  | _, _ => none

end


/-! ## Pattern matrices

A `Row` is one surface branch mid-compilation: the patterns still to test (one
per column; column `i` corresponds to occurrence `occs[i]` of the scrutinee),
the occurrences already captured (in pre-order — see the pop rule), and the
branch index it stands for. -/

structure Row where
  /-- Occurrences already bound by this row, in pre-order. -/
  captured : List Occ
  /-- Patterns still to be tested, parallel to the compiler's `occs` vector.
      INVARIANT (carried by the proofs, not the type): all rows of a matrix
      have `pats.length = occs.length`. -/
  pats : List GPat
  /-- Which surface branch this row is (its index in the original match). -/
  act : Nat
  deriving Repr

abbrev Matrix := List Row

/-- One row's outcome on the value vector `vals` (the values at the current
    column occurrences), relative to the `root` scrutinee (needed to fetch the
    already-`captured` occurrences). -/
def rowSem (root : Expr) (vals : List Expr) (r : Row) : Option (Nat × List Expr) := do
  let pre ← r.captured.mapM (fetch root)
  let cs ← matchGs vals r.pats
  pure (r.act, pre ++ cs)

/-- First-match semantics of a matrix: the first row that matches wins.
    This is the spec `compile` is proven against (H1). -/
def matrixSem (root : Expr) (vals : List Expr) : Matrix → Option (Nat × List Expr)
  | [] => none
  | r :: rest => rowSem root vals r <|> matrixSem root vals rest

/-- The initial one-column matrix of a surface match: row `i` = branch `i`,
    nothing captured, the whole (normalised) pattern in the single column
    (which corresponds to occurrence `[]`, the scrutinee itself). -/
def initMatrix (pats : List Surface.Pattern) (firstAct : Nat := 0) : Matrix :=
  match pats with
  | [] => []
  | p :: rest => { captured := [], pats := [norm p], act := firstAct }
      :: initMatrix rest (firstAct + 1)


/-! ## The decision-tree IR -/

inductive DTree
  /-- No row matches (a non-exhaustive match fell through). -/
  | fail
  /-- Fire branch `act`, binding the values at `binds` (in pre-order). -/
  | leaf (act : Nat) (binds : List Occ)
  /-- Multi-way test on the ctor tag of the value at `occ`: first matching
      `(ctor, arity, subtree)` case fires, else `default`. -/
  | switch (occ : Occ) (cases : List (CtorName × Nat × DTree)) (default : DTree)
  deriving Repr

mutual

/-- The tree interpreter: the Core-side denotation carrier. Returns the
    selected branch and captured values, like `firstMatch`/`matrixSem`. A
    non-ctor value at a switched occurrence falls to the default (mirroring
    Core's leading-wildcard rule; under the typing hypotheses of the campaign
    this case never arises, since switches only test ADT-typed occurrences). -/
def evalDTree (root : Expr) : DTree → Option (Nat × List Expr)
  | .fail => none
  | .leaf act binds => (binds.mapM (fetch root)).map (fun vs => (act, vs))
  | .switch occ cases dflt =>
    match fetch root occ with
    | none => none
    | some v =>
      match getCtorArgs v with
      | some (name, args) => evalSwitch root name args.length cases dflt
      | none => evalDTree root dflt
termination_by t => sizeOf t

def evalSwitch (root : Expr) (name : CtorName) (arity : Nat) :
    List (CtorName × Nat × DTree) → DTree → Option (Nat × List Expr)
  | [], dflt => evalDTree root dflt
  | (c, a, t) :: rest, dflt =>
    if c = name ∧ a = arity then evalDTree root t
    else evalSwitch root name arity rest dflt
termination_by cases dflt => sizeOf cases + sizeOf dflt

end


/-! ## The compiler

Naive leftmost-column matrix compilation (Maranget's `S(c,M)`/`D(M)` machinery
with the column heuristic fixed to "always column 0"), plus the pop rule. -/

/-- The head-ctor test of a pattern, if it is one. -/
def GPat.headCtor : GPat → Option (CtorName × Nat)
  | .gctor c args => some (c, args.length)
  | _ => none

/-- The distinct `(ctor, arity)` tests appearing in column 0. Empty iff the
    column is all-irrefutable (⇒ the pop rule applies). -/
def colHeads (M : Matrix) : List (CtorName × Nat) :=
  (M.filterMap (fun r => r.pats.head? >>= GPat.headCtor)).dedup

/-- The sub-occurrences (fields) of `occ` at arity `arity`. -/
def subOccs (occ : Occ) (arity : Nat) : List Occ :=
  (List.range arity).map (fun i => occ ++ [i])

/-- Specialise one row by "column 0's value is ctor `c` at arity `arity`":
    a `gctor c` row unfolds its sub-patterns into the column; another ctor
    refutes (row dropped); `gbind` captures the column occurrence NOW (its
    column is leftmost — pre-order preserved) and survives as `arity`
    wildcards; `gwild` likewise without capturing. -/
def specializeRow (c : CtorName) (arity : Nat) (occ0 : Occ) (r : Row) : Option Row :=
  match r.pats with
  | [] => none
  | .gctor c' args :: rest =>
    if c' = c ∧ args.length = arity then some { r with pats := args ++ rest } else none
  | .gbind :: rest =>
    some { r with captured := r.captured ++ [occ0],
                  pats := List.replicate arity .gwild ++ rest }
  | .gwild :: rest =>
    some { r with pats := List.replicate arity .gwild ++ rest }

/-- Maranget's `S(c, M)`. -/
def specialize (c : CtorName) (arity : Nat) (occ0 : Occ) (M : Matrix) : Matrix :=
  M.filterMap (specializeRow c arity occ0)

/-- Default one row: "column 0's value matches none of the column's ctor
    tests". Ctor rows refute; `gbind` captures the column occurrence and moves
    on; `gwild` just moves on. (Also reused as the POP rule when the column has
    no ctor tests at all.) -/
def defaultRow (occ0 : Occ) (r : Row) : Option Row :=
  match r.pats with
  | [] => none
  | .gctor _ _ :: _ => none
  | .gbind :: rest => some { r with captured := r.captured ++ [occ0], pats := rest }
  | .gwild :: rest => some { r with pats := rest }

/-- Maranget's `D(M)`. -/
def defaultMatrix (occ0 : Occ) (M : Matrix) : Matrix :=
  M.filterMap (defaultRow occ0)


/-! ### Termination measure

`compile` recurses on `S(c,M)`/`D(M)`, which are not structurally smaller
(specialising a wildcard row at arity 3 grows it). The measure is
lexicographic: (total ctor-node count of the matrix, number of columns).
Switching always strictly consumes a ctor node (the chosen column has at least
one, which every case either unfolds or drops); the pop rule leaves the count
unchanged but drops a column. -/

mutual

def GPat.ctorCount : GPat → Nat
  | .gctor _ args => 1 + GPat.ctorCountList args
  | _ => 0

def GPat.ctorCountList : List GPat → Nat
  | [] => 0
  | p :: ps => p.ctorCount + GPat.ctorCountList ps

end

def Row.ctorCount (r : Row) : Nat := GPat.ctorCountList r.pats

def Matrix.ctorCount (M : Matrix) : Nat := (M.map Row.ctorCount).sum

/-! ### Helper lemmas for the measure -/

/-- `ctorCountList` distributes over append. -/
private theorem GPat.ctorCountList_append :
    ∀ (l₁ l₂ : List GPat),
      GPat.ctorCountList (l₁ ++ l₂)
        = GPat.ctorCountList l₁ + GPat.ctorCountList l₂
  | [], l₂ => by simp [GPat.ctorCountList]
  | p :: ps, l₂ => by
      simp only [List.cons_append, GPat.ctorCountList, GPat.ctorCountList_append ps l₂]
      omega

/-- A block of `gwild`s contributes no ctor nodes. -/
private theorem GPat.ctorCountList_replicate_gwild :
    ∀ (n : Nat), GPat.ctorCountList (List.replicate n .gwild) = 0
  | 0 => by simp [GPat.ctorCountList]
  | n + 1 => by
      simp [List.replicate_succ, GPat.ctorCountList, GPat.ctorCount,
        GPat.ctorCountList_replicate_gwild n]

/-- The measure of a `filterMap`ed matrix splits off the head row's
    contribution (`0` if the row is dropped). -/
private theorem sum_ctorCount_filterMap_cons (f : Row → Option Row) (a : Row) (l : Matrix) :
    (((a :: l).filterMap f).map Row.ctorCount).sum
      = (f a).elim 0 Row.ctorCount + ((l.filterMap f).map Row.ctorCount).sum := by
  cases hfa : f a with
  | none => simp [hfa]
  | some b => simp [hfa]

/-- If a per-row transformation never grows a row's count, the whole matrix
    count doesn't grow. -/
private theorem sum_ctorCount_filterMap_le (f : Row → Option Row)
    (hbound : ∀ r : Row, (f r).elim 0 Row.ctorCount ≤ r.ctorCount) :
    ∀ l : Matrix,
      ((l.filterMap f).map Row.ctorCount).sum ≤ (l.map Row.ctorCount).sum
  | [] => by simp
  | a :: l => by
      have ih := sum_ctorCount_filterMap_le f hbound l
      have hcons := sum_ctorCount_filterMap_cons f a l
      have hb := hbound a
      simp only [List.map_cons, List.sum_cons]
      omega

/-- …and if additionally some witnessing row's count strictly drops, the whole
    matrix count strictly drops. -/
private theorem sum_ctorCount_filterMap_lt (f : Row → Option Row)
    (hbound : ∀ r : Row, (f r).elim 0 Row.ctorCount ≤ r.ctorCount) :
    ∀ (l : Matrix) (r0 : Row), r0 ∈ l →
      (f r0).elim 0 Row.ctorCount < r0.ctorCount →
      ((l.filterMap f).map Row.ctorCount).sum < (l.map Row.ctorCount).sum
  | [], _, hr0, _ => by simp at hr0
  | a :: l, r0, hr0, hstrict => by
      have hcons := sum_ctorCount_filterMap_cons f a l
      have hb := hbound a
      simp only [List.map_cons, List.sum_cons]
      rcases List.mem_cons.mp hr0 with rfl | hr0'
      · have ihle := sum_ctorCount_filterMap_le f hbound l
        omega
      · have ihlt := sum_ctorCount_filterMap_lt f hbound l r0 hr0' hstrict
        omega

/-- Per-row bound for `defaultRow`: dropping / stripping an irrefutable head
    never grows the count. -/
private theorem defaultRow_ctorCount_le (occ0 : Occ) (r : Row) :
    (defaultRow occ0 r).elim 0 Row.ctorCount ≤ r.ctorCount := by
  rcases r with ⟨captured, pats, act⟩
  cases pats with
  | nil => simp [defaultRow, Row.ctorCount, GPat.ctorCountList]
  | cons p rest =>
      cases p with
      | gctor c args => simp [defaultRow]
      | gbind => simp [defaultRow, Row.ctorCount, GPat.ctorCountList, GPat.ctorCount]
      | gwild => simp [defaultRow, Row.ctorCount, GPat.ctorCountList, GPat.ctorCount]

/-- Per-row bound for `specializeRow`: unfolding a matching ctor drops a node,
    a non-match drops the row, and wildcard expansion adds only ctor-free
    `gwild`s — so the count never grows. -/
private theorem specializeRow_ctorCount_le (c : CtorName) (arity : Nat) (occ0 : Occ) (r : Row) :
    (specializeRow c arity occ0 r).elim 0 Row.ctorCount ≤ r.ctorCount := by
  rcases r with ⟨captured, pats, act⟩
  cases pats with
  | nil => simp [specializeRow, Row.ctorCount, GPat.ctorCountList]
  | cons p rest =>
      cases p with
      | gctor c' args =>
          by_cases hcond : c' = c ∧ args.length = arity
          · simp only [specializeRow, if_pos hcond, Option.elim, Row.ctorCount,
              GPat.ctorCountList_append, GPat.ctorCountList, GPat.ctorCount]
            omega
          · simp [specializeRow, hcond]
      | gbind =>
          simp [specializeRow, Row.ctorCount, GPat.ctorCountList, GPat.ctorCount,
            GPat.ctorCountList_append, GPat.ctorCountList_replicate_gwild]
      | gwild =>
          simp [specializeRow, Row.ctorCount, GPat.ctorCountList, GPat.ctorCount,
            GPat.ctorCountList_append, GPat.ctorCountList_replicate_gwild]

/-- A `(c, arity)` head witnessed in `colHeads` yields a row of `M` whose head
    is exactly `gctor c args` with `args.length = arity`. -/
private theorem colHeads_mem_witness (M : Matrix) (c : CtorName) (arity : Nat)
    (h : (c, arity) ∈ colHeads M) :
    ∃ r ∈ M, ∃ args rest, r.pats = GPat.gctor c args :: rest ∧ args.length = arity := by
  simp only [colHeads, List.mem_dedup, List.mem_filterMap] at h
  obtain ⟨r, hrmem, hgr⟩ := h
  refine ⟨r, hrmem, ?_⟩
  cases hpats : r.pats with
  | nil => rw [hpats] at hgr; simp at hgr
  | cons q t =>
      cases q with
      | gctor c' cargs =>
          rw [hpats] at hgr
          simp [GPat.headCtor] at hgr
          obtain ⟨rfl, ha⟩ := hgr
          exact ⟨cargs, t, rfl, ha⟩
      | gbind => rw [hpats] at hgr; simp [GPat.headCtor] at hgr
      | gwild => rw [hpats] at hgr; simp [GPat.headCtor] at hgr

/-- A nonempty `colHeads` yields a ctor-headed row of `M`. -/
private theorem colHeads_ne_nil_witness (M : Matrix) (h : colHeads M ≠ []) :
    ∃ r ∈ M, ∃ c args rest, r.pats = GPat.gctor c args :: rest := by
  obtain ⟨hd, tl, hcons⟩ := List.exists_cons_of_ne_nil h
  have hmem : hd ∈ colHeads M := by rw [hcons]; exact List.mem_cons_self ..
  obtain ⟨r, hrmem, args, rest, hpats, _⟩ :=
    colHeads_mem_witness M hd.1 hd.2 (by rw [Prod.mk.eta]; exact hmem)
  exact ⟨r, hrmem, hd.1, args, rest, hpats⟩

/-- Dropping / shrinking rows never grows the count. -/
theorem defaultMatrix_ctorCount_le (occ0 : Occ) (M : Matrix) :
    (defaultMatrix occ0 M).ctorCount ≤ M.ctorCount := by
  simp only [defaultMatrix, Matrix.ctorCount]
  exact sum_ctorCount_filterMap_le (defaultRow occ0) (defaultRow_ctorCount_le occ0) M

/-- If column 0 contains at least one ctor test, `D(M)` drops that row
    entirely — strict decrease. -/
theorem defaultMatrix_ctorCount_lt (occ0 : Occ) (M : Matrix)
    (h : colHeads M ≠ []) :
    (defaultMatrix occ0 M).ctorCount < M.ctorCount := by
  obtain ⟨r0, hr0, c, args, rest, hpats⟩ := colHeads_ne_nil_witness M h
  simp only [defaultMatrix, Matrix.ctorCount]
  refine sum_ctorCount_filterMap_lt (defaultRow occ0) (defaultRow_ctorCount_le occ0) M r0 hr0 ?_
  have hnone : defaultRow occ0 r0 = none := by simp [defaultRow, hpats]
  rw [hnone]
  simp only [Option.elim, Row.ctorCount, hpats, GPat.ctorCountList, GPat.ctorCount]
  omega

/-- If `(c, arity)` is one of column 0's head ctors, `S(c, M)` unfolds that
    row's head ctor node — strict decrease (all other rows shrink or drop;
    wildcard expansion adds only ctor-free wildcards). -/
theorem specialize_ctorCount_lt (c : CtorName) (arity : Nat) (occ0 : Occ)
    (M : Matrix) (h : (c, arity) ∈ colHeads M) :
    (specialize c arity occ0 M).ctorCount < M.ctorCount := by
  obtain ⟨r0, hr0, args, rest, hpats, harity⟩ := colHeads_mem_witness M c arity h
  simp only [specialize, Matrix.ctorCount]
  refine sum_ctorCount_filterMap_lt (specializeRow c arity occ0)
    (specializeRow_ctorCount_le c arity occ0) M r0 hr0 ?_
  have hsome : specializeRow c arity occ0 r0 = some { r0 with pats := args ++ rest } := by
    simp [specializeRow, hpats, harity]
  rw [hsome]
  simp only [Option.elim, Row.ctorCount, hpats, GPat.ctorCountList_append,
    GPat.ctorCountList, GPat.ctorCount]
  omega

/-- The compiler. Row 1 exhausted ⇒ leaf (first-match: rows below are dead).
    All-irrefutable column 0 ⇒ pop (consume it silently, no tree node).
    Otherwise switch on column 0, one case per head ctor, `D(M)` as default. -/
def compile (occs : List Occ) (M : Matrix) : DTree :=
  match M with
  | [] => .fail
  | r1 :: rest =>
    match occs with
    | [] => .leaf r1.act r1.captured
    | occ0 :: orest =>
      match _hh : colHeads (r1 :: rest) with
      | [] => compile orest (defaultMatrix occ0 (r1 :: rest))
      | hhd :: htl =>
        .switch occ0
          ((hhd :: htl).attach.map (fun x =>
            (x.1.1, x.1.2,
             compile (subOccs occ0 x.1.2 ++ orest)
                     (specialize x.1.1 x.1.2 occ0 (r1 :: rest)))))
          (compile orest (defaultMatrix occ0 (r1 :: rest)))
termination_by (M.ctorCount, occs.length)
decreasing_by
  · -- pop rule: count non-increasing, column count strictly down
    have hle := defaultMatrix_ctorCount_le occ0 (r1 :: rest)
    rcases Nat.lt_or_eq_of_le hle with hlt | heq
    · exact Prod.Lex.left _ _ hlt
    · rw [heq]
      exact Prod.Lex.right _ (Nat.lt_succ_self orest.length)
  · -- switch case: the chosen head ctor is consumed
    have hmem : (x.1.1, x.1.2) ∈ colHeads (r1 :: rest) := by
      rw [_hh]; exact x.2
    exact Prod.Lex.left _ _ (specialize_ctorCount_lt x.1.1 x.1.2 occ0 _ hmem)
  · -- switch default: the ctor rows are dropped
    have hne : colHeads (r1 :: rest) ≠ [] := by
      rw [_hh]; simp
    exact Prod.Lex.left _ _ (defaultMatrix_ctorCount_lt occ0 _ hne)


/-! ## Emission: `DTree → Core.Expr`

Parametric in the leaf bodies (`bodies : Nat → Expr`), so adequacy quantifies
over arbitrary (e.g. elaborated) branch bodies.

The de Bruijn story: `env : List Occ` maps index `j` to the occurrence whose
value the var at index `j` holds. A switch's Core `match_` binds the tested
ctor's fields at indices `0..arity-1` (Core opens branch bodies with
`substN 0 (args.take bindCount)`), so inside a case branch the env is
`subOccs occ arity ++ env` — old entries shift automatically because position
IS the index. The scrutinee itself must be var-bound by the caller
(`lowerMatch` wraps in a `letIn`), so `env = [[]]` at the root.

Leaves re-bind their captures with nested `letIn`s ("leaf-lets"): the body then
sees capture `j` at de Bruijn index `j` exactly — the innermost let is capture
0. Body vars ≥ (number of captures) are outer-context references and are
shifted past the match/let binders introduced by the tree. -/

/-- The var currently holding the value at `occ`. (Garbage if `occ ∉ env`;
    the emit invariant of the campaign proves every emitted occurrence is
    bound.) -/
def resolveOcc (env : List Occ) (occ : Occ) : Expr :=
  .var (env.idxOf occ) []

/-- Wrap `body` in `letIn`s re-binding `binds` so that capture `j` sits at de
    Bruijn index `j` in `body` (innermost let = capture 0). RHS `i` (counting
    from the outermost let, which re-binds the LAST capture) sits under `i`
    lets, so its env lookup is shifted by `i`. Body vars past the captures are
    shifted over the `env` binders the tree introduced. -/
def emitLets (env : List Occ) (binds : List Occ) (body : Expr) : Expr :=
  go binds.reverse 0
where
  go : List Occ → Nat → Expr
    | [], _ => body.shiftFrom binds.length env.length
    | b :: rest, depth =>
      .letIn none (.var (env.idxOf b + depth) []) (go rest (depth + 1))

mutual

/-- Render a tree as nested Core matches. A switch becomes a `match_` on the
    var holding its occurrence, with one `named` branch per case and a trailing
    `wildcard` branch for the default. `fail` becomes a canonical stuck term
    (a branchless match on an inert ctor) — unreachable when the surface match
    is exhaustive. -/
def emit (env : List Occ) (bodies : Nat → Expr) : DTree → Expr
  | .fail => .match_ (.ctor (.mk "PatCompFail")) []
  | .leaf act binds => emitLets env binds (bodies act)
  | .switch occ cases dflt =>
    .match_ (resolveOcc env occ)
      (emitCases env bodies occ cases ++ [(.wildcard, emit env bodies dflt)])

def emitCases (env : List Occ) (bodies : Nat → Expr) (occ : Occ) :
    List (CtorName × Nat × DTree) → List (MatchPattern × Expr)
  | [] => []
  | (c, a, t) :: rest =>
    (.named c a, emit (subOccs occ a ++ env) bodies t)
      :: emitCases env bodies occ rest

end

/-- The packaged lowering of one surface match: bind the scrutinee, then run
    the compiled tree against it (env `[[]]`: var 0 = the scrutinee). -/
def lowerMatch (scrut : Expr) (pats : List Surface.Pattern) (bodies : Nat → Expr) : Expr :=
  .letIn none scrut (emit [[]] bodies (compile [[]] (initMatrix pats)))


/-! ## Executable sanity checks

Value/pattern helpers for the tests, then `#guard`s at three levels:
1. the surface spec (`matchPat`/`firstMatch`) behaves as documented;
2. H1 instances: `evalDTree ∘ compile` agrees with `matrixSem`/`firstMatch`;
3. H2 instances (end-to-end): the EMITTED Core term, run under Core's real
   executable `step`, reaches the right branch body with the right values.
(`Expr` has no `DecidableEq`, so outcomes are checked by pattern matching.) -/

private def vInt (n : Int) : Expr := .primLit (.int n)
private def vJust (v : Expr) : Expr := .app (.ctor (.mk "Just")) v
private def vNothing : Expr := .ctor (.mk "Nothing")
private def vPair (a b : Expr) : Expr := .app (.app (.ctor (.mk "Pair")) a) b

private def pJustX : Surface.Pattern := .ctor (.mk "Just") [.name (.mk "x")]
private def pNothing : Surface.Pattern := .ctor (.mk "Nothing") []

/-- Iterate Core's executable small-step until value/stuck (fuel-bounded). -/
private def runN : Nat → Expr → Expr
  | 0, e => e
  | n + 1, e =>
    match SmallStep.step e with
    | some e' => runN n e'
    | none => e

-- ── level 1: the surface spec ─────────────────────────────────────────

-- matchPat (Just 5) (Just x) = some [5]
#guard match matchPat (vJust (vInt 5)) pJustX with
  | some [.primLit (.int 5)] => true | _ => false

-- matchPat Nothing (Just x) = none
#guard (matchPat vNothing pJustX).isNone

-- wildcard matches anything, captures nothing
#guard match matchPat (vInt 7) .wildcard with
  | some [] => true | _ => false

-- nested pair: matchPat (Pair (Just 3) 7) (pair (Just x) y) = some [3, 7]
#guard match matchPat (vPair (vJust (vInt 3)) (vInt 7))
              (.pair pJustX (.name (.mk "y"))) with
  | some [.primLit (.int 3), .primLit (.int 7)] => true | _ => false

-- first-match order: (Just x) before wildcard on (Just 5) picks branch 0 …
#guard match firstMatch (vJust (vInt 5)) [pJustX, .wildcard] with
  | some (0, [.primLit (.int 5)]) => true | _ => false

-- … and on Nothing falls to branch 1
#guard match firstMatch vNothing [pJustX, .wildcard] with
  | some (1, []) => true | _ => false

-- capture-order pathology (the pop-rule case): (x, Just y) — the switch is
-- forced by column 1, but captures must still come out [x-value, y-value]
#guard match matchPat (vPair (vInt 1) (vJust (vInt 2)))
              (.pair (.name (.mk "x")) pJustX) with
  | some [.primLit (.int 1), .primLit (.int 2)] => true | _ => false

-- ── level 2: H1 instances (tree vs spec) ──────────────────────────────

private def treeOf (pats : List Surface.Pattern) : DTree :=
  compile [[]] (initMatrix pats)

-- (Just x | Nothing) on Just 5 / Nothing: same act + captures as firstMatch
#guard match evalDTree (vJust (vInt 5)) (treeOf [pJustX, pNothing]) with
  | some (0, [.primLit (.int 5)]) => true | _ => false
#guard match evalDTree vNothing (treeOf [pJustX, pNothing]) with
  | some (1, []) => true | _ => false

-- nested: ((Just x, y) | (Nothing, y)) — branch selection AND capture order
private def nestedPats : List Surface.Pattern :=
  [ .pair pJustX (.name (.mk "y")),
    .pair pNothing (.name (.mk "y")) ]

#guard match evalDTree (vPair (vJust (vInt 3)) (vInt 7)) (treeOf nestedPats) with
  | some (0, [.primLit (.int 3), .primLit (.int 7)]) => true | _ => false
#guard match evalDTree (vPair vNothing (vInt 7)) (treeOf nestedPats) with
  | some (1, [.primLit (.int 7)]) => true | _ => false

-- the pop-rule pathology, through the compiler: (x, Just y) must capture
-- [1, 2] in THAT order even though the only ctor test is in column 1
#guard match evalDTree (vPair (vInt 1) (vJust (vInt 2)))
              (treeOf [.pair (.name (.mk "x")) pJustX, .wildcard]) with
  | some (0, [.primLit (.int 1), .primLit (.int 2)]) => true | _ => false

-- refutation: no branch matches ⇒ none (a non-exhaustive match)
#guard (evalDTree vNothing (treeOf [pJustX])).isNone

-- ── level 3: H2 instances (emitted Core under the real `step`) ────────

-- match (Just 41) with Just x => x + 1 | Nothing => 0   ~~>  42
#guard match runN 32 (lowerMatch (vJust (vInt 41)) [pJustX, pNothing]
    (fun i => if i = 0
      then .app (.app (.primBinOp .intAdd) (.var 0 [])) (vInt 1)
      else vInt 0)) with
  | .primLit (.int 42) => true | _ => false

-- match Nothing with Just x => x + 1 | Nothing => 0   ~~>  0
#guard match runN 32 (lowerMatch vNothing [pJustX, pNothing]
    (fun i => if i = 0
      then .app (.app (.primBinOp .intAdd) (.var 0 [])) (vInt 1)
      else vInt 0)) with
  | .primLit (.int 0) => true | _ => false

-- nested + binding order: match (Just 3, 7) with (Just x, y) => x - y | _ => 0
-- x must land at var 0 and y at var 1 (pre-order): 3 - 7 = -4
#guard match runN 32 (lowerMatch (vPair (vJust (vInt 3)) (vInt 7)) nestedPats
    (fun i => if i = 0
      then .app (.app (.primBinOp .intSub) (.var 0 [])) (.var 1 [])
      else vInt 0)) with
  | .primLit (.int (-4)) => true | _ => false

-- second branch of the nested match: (Nothing, 9) ⇒ y = 9 at var 0
#guard match runN 32 (lowerMatch (vPair vNothing (vInt 9)) nestedPats
    (fun i => if i = 0 then vInt 0 else .var 0 [])) with
  | .primLit (.int 9) => true | _ => false

-- pop-rule pathology end-to-end: match (1, Just 2) with (x, Just y) => x - y
-- pre-order demands x@var0, y@var1: 1 - 2 = -1 (a binding swap would give 1)
#guard match runN 32 (lowerMatch (vPair (vInt 1) (vJust (vInt 2)))
    [.pair (.name (.mk "x")) pJustX, .wildcard]
    (fun i => if i = 0
      then .app (.app (.primBinOp .intSub) (.var 0 [])) (.var 1 [])
      else vInt 99)) with
  | .primLit (.int (-1)) => true | _ => false

-- deep nesting (H4 stress): match Just (Just 5) with Just (Just x) => x
#guard match runN 32 (lowerMatch (vJust (vJust (vInt 5)))
    [.ctor (.mk "Just") [pJustX], .wildcard]
    (fun i => if i = 0 then .var 0 [] else vInt 0)) with
  | .primLit (.int 5) => true | _ => false

end PatComp
