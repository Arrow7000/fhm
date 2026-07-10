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

open SmallStep (getCtorArgs IsValue IsCtorChain Step CtorAppliedTo)


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


/-! ### `matchGs` list algebra

The vector-splicing kit H1's `S`/`D` lemmas lean on: length discipline,
append-splitting, wildcard blocks, and the ctor-case characterisation. -/

/-- `guard` in the `Option` monad, positive case. -/
private theorem guard_pos {p : Prop} [Decidable p] (h : p) :
    (guard p : Option Unit) = some () := by
  unfold guard
  rw [if_pos h]
  rfl

/-- `guard` in the `Option` monad, negative case. -/
private theorem guard_neg {p : Prop} [Decidable p] (h : ¬p) :
    (guard p : Option Unit) = none := by
  unfold guard
  rw [if_neg h]
  rfl

/-- `guard` as an `ite`, so `simp` can decide the condition. -/
private theorem guard_eq_ite {p : Prop} [Decidable p] :
    (guard p : Option Unit) = if p then some () else none := by
  by_cases h : p
  · rw [guard_pos h, if_pos h]
  · rw [guard_neg h, if_neg h]

@[simp] theorem matchG_gbind (v : Expr) : matchG v .gbind = some [v] := by
  simp [matchG]

@[simp] theorem matchG_gwild (v : Expr) : matchG v .gwild = some [] := by
  simp [matchG]

/-- A successful `matchGs` forces the vectors to the same length. -/
theorem matchGs_length {vs : List Expr} {ps : List GPat} {cs : List Expr}
    (h : matchGs vs ps = some cs) : vs.length = ps.length := by
  induction vs generalizing ps cs with
  | nil =>
    cases ps with
    | nil => rfl
    | cons p ps => simp [matchGs] at h
  | cons v vs ih =>
    cases ps with
    | nil => simp [matchGs] at h
    | cons p ps =>
      cases hA : matchG v p with
      | none => simp [matchGs, hA] at h
      | some a =>
        cases hB : matchGs vs ps with
        | none => simp [matchGs, hA, hB] at h
        | some b => simp [ih hB]

/-- `matchGs` splits over appends when the first halves line up in length
    (captures concatenate). Stated in the `do`/bind normal form matching
    `matchGs`'s own cons equation, so it rewrites cleanly. -/
theorem matchGs_append {vs₁ vs₂ : List Expr} {ps₁ ps₂ : List GPat}
    (h : vs₁.length = ps₁.length) :
    matchGs (vs₁ ++ vs₂) (ps₁ ++ ps₂)
      = (do pure ((← matchGs vs₁ ps₁) ++ (← matchGs vs₂ ps₂))) := by
  induction vs₁ generalizing ps₁ with
  | nil =>
    cases ps₁ with
    | nil => cases hm : matchGs vs₂ ps₂ <;> simp [matchGs, hm]
    | cons p ps => simp at h
  | cons v vs₁ ih =>
    cases ps₁ with
    | nil => simp at h
    | cons p ps₁ =>
      simp only [List.cons_append, matchGs]
      rw [ih (by simpa using h)]
      cases matchG v p <;> cases matchGs vs₁ ps₁ <;>
        cases matchGs vs₂ ps₂ <;> simp

/-- A block of wildcards of the right width always matches, capturing
    nothing. -/
theorem matchGs_replicate_gwild {vs : List Expr} {n : Nat}
    (h : vs.length = n) :
    matchGs vs (List.replicate n .gwild) = some [] := by
  induction vs generalizing n with
  | nil => subst h; simp [matchGs]
  | cons v vs ih =>
    subst h
    simp [List.replicate_succ, matchGs, ih rfl]

/-- What a successful generic-ctor match MEANS: the value decomposes under
    that ctor at the right arity and the fields match pointwise. -/
theorem matchG_gctor_iff {v : Expr} {c : CtorName} {pats : List GPat}
    {cs : List Expr} :
    matchG v (.gctor c pats) = some cs
      ↔ ∃ args, getCtorArgs v = some (c, args) ∧ args.length = pats.length
          ∧ matchGs args pats = some cs := by
  cases hget : getCtorArgs v with
  | none => simp [matchG, hget]
  | some ca =>
    obtain ⟨name, args⟩ := ca
    constructor
    · intro h
      simp only [matchG, hget, Option.bind_eq_bind, Option.bind_some] at h
      by_cases hcond : name = c ∧ args.length = pats.length
      · obtain ⟨rfl, hlen⟩ := hcond
        refine ⟨args, rfl, hlen, ?_⟩
        rw [guard_pos (show name = name ∧ args.length = pats.length
          from ⟨rfl, hlen⟩)] at h
        simpa using h
      · rw [guard_neg hcond] at h
        simp at h
    · rintro ⟨args', hget', hlen, hms⟩
      obtain ⟨rfl, rfl⟩ : name = c ∧ args = args' := by
        simpa using hget'
      simp [matchG, hget, guard_eq_ite, hlen, hms]


/-! ### Factoring: the surface spec runs through `norm`

`matchPat` (the trusted spec) and `matchG ∘ norm` agree ON THE NOSE, so the
matrix campaign only ever reasons about `matchG`. The mutual induction mirrors
the `matchPat`/`matchPats`/`matchListPat` recursion structure exactly. -/

private theorem normList_length : ∀ ps : List Surface.Pattern,
    (normList ps).length = ps.length
  | [] => rfl
  | p :: ps => by simp [normList, normList_length ps]

mutual

/-- The factoring theorem: the surface spec is `matchG` after `norm`. -/
theorem matchPat_eq_matchG_norm : ∀ (v : Expr) (p : Surface.Pattern),
    matchPat v p = matchG v (norm p)
  | v, .name _ => by simp [matchPat, norm]
  | v, .wildcard => by simp [matchPat, norm]
  | v, .ctor cn ps => by
    simp only [matchPat, norm, matchG, normList_length]
    cases hget : getCtorArgs v with
    | none => rfl
    | some ca =>
      obtain ⟨c, args⟩ := ca
      simp only [Option.bind_eq_bind, Option.bind_some]
      by_cases hcond : c = cn ∧ args.length = ps.length
      · simp [guard_pos hcond, matchPats_eq_matchGs_normList args ps]
      · simp [guard_neg hcond]
  | v, .pair p q => by
    simp only [matchPat, norm, matchG]
    cases hget : getCtorArgs v with
    | none => rfl
    | some ca =>
      obtain ⟨c, args⟩ := ca
      simp only [Option.bind_eq_bind, Option.bind_some]
      match args with
      | [] => simp [guard_eq_ite]
      | [a] => simp [guard_eq_ite]
      | [a, b] =>
        by_cases hc : c = CtorName.mk "Pair"
        · cases hA : matchG a (norm p) <;> cases hB : matchG b (norm q) <;>
            simp [guard_eq_ite, hc, matchGs, hA, hB,
              matchPat_eq_matchG_norm a p, matchPat_eq_matchG_norm b q]
        · simp [guard_eq_ite, hc]
      | _ :: _ :: _ :: _ => simp [guard_eq_ite]
  | v, .cons hp tp => by
    simp only [matchPat, norm, matchG]
    cases hget : getCtorArgs v with
    | none => rfl
    | some ca =>
      obtain ⟨c, args⟩ := ca
      simp only [Option.bind_eq_bind, Option.bind_some]
      match args with
      | [] => simp [guard_eq_ite]
      | [a] => simp [guard_eq_ite]
      | [a, b] =>
        by_cases hc : c = CtorName.mk "Cons"
        · cases hA : matchG a (norm hp) <;> cases hB : matchG b (norm tp) <;>
            simp [guard_eq_ite, hc, matchGs, hA, hB,
              matchPat_eq_matchG_norm a hp, matchPat_eq_matchG_norm b tp]
        · simp [guard_eq_ite, hc]
      | _ :: _ :: _ :: _ => simp [guard_eq_ite]
  | v, .list items => matchListPat_eq_matchG_normListPat v items

/-- Pointwise companion: `matchPats` is `matchGs` after `normList`. -/
theorem matchPats_eq_matchGs_normList : ∀ (vs : List Expr) (ps : List Surface.Pattern),
    matchPats vs ps = matchGs vs (normList ps)
  | [], [] => by simp [matchPats, normList, matchGs]
  | [], _ :: _ => by simp [matchPats, normList, matchGs]
  | _ :: _, [] => by simp [matchPats, normList, matchGs]
  | v :: vs, p :: ps => by
    simp only [matchPats, normList, matchGs]
    rw [matchPat_eq_matchG_norm v p, matchPats_eq_matchGs_normList vs ps]

/-- List-pattern companion: unrolling matches the normalised `Cons`/`Nil`
    chain. -/
theorem matchListPat_eq_matchG_normListPat : ∀ (v : Expr) (items : List Surface.Pattern),
    matchListPat v items = matchG v (normListPat items)
  | v, [] => by
    simp only [matchListPat, normListPat, matchG]
    cases hget : getCtorArgs v with
    | none => rfl
    | some ca =>
      obtain ⟨c, args⟩ := ca
      simp only [Option.bind_eq_bind, Option.bind_some]
      match args with
      | [] =>
        by_cases hc : c = CtorName.mk "Nil"
        · simp [guard_eq_ite, hc, matchGs]
        · simp [guard_eq_ite, hc]
      | _ :: _ => simp [guard_eq_ite]
  | v, p :: ps => by
    simp only [matchListPat, normListPat, matchG]
    cases hget : getCtorArgs v with
    | none => rfl
    | some ca =>
      obtain ⟨c, args⟩ := ca
      simp only [Option.bind_eq_bind, Option.bind_some]
      match args with
      | [] => simp [guard_eq_ite]
      | [a] => simp [guard_eq_ite]
      | [a, b] =>
        by_cases hc : c = CtorName.mk "Cons"
        · cases hA : matchG a (norm p) <;>
            cases hB : matchG b (normListPat ps) <;>
            simp [guard_eq_ite, hc, matchGs, hA, hB,
              matchPat_eq_matchG_norm a p,
              matchListPat_eq_matchG_normListPat b ps]
        · simp [guard_eq_ite, hc]
      | _ :: _ :: _ :: _ => simp [guard_eq_ite]

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

/-- Generalisation of `firstMatch_eq_matrixSem` over the starting act index:
    `initMatrix` numbers its rows from `k`, so `matrixSem` reports the
    `firstMatch` index shifted by `k`. -/
private theorem matrixSem_initMatrix_shift (v : Expr) (ps : List Surface.Pattern)
    (k : Nat) :
    matrixSem v [v] (initMatrix ps k)
      = (firstMatch v ps).map (fun x => (x.1 + k, x.2)) := by
  induction ps generalizing k with
  | nil => simp [initMatrix, matrixSem, firstMatch]
  | cons p ps ih =>
    have hfac := (matchPat_eq_matchG_norm v p).symm
    simp only [initMatrix, matrixSem, firstMatch]
    cases hm : matchPat v p with
    | some cs =>
      have hg : matchG v (norm p) = some cs := hfac.trans hm
      simp [rowSem, matchGs, hg]
    | none =>
      have hg : matchG v (norm p) = none := hfac.trans hm
      simp only [rowSem, matchGs, hg]
      simp [ih (k + 1)]
      cases hf : firstMatch v ps with
      | none => rfl
      | some x =>
        obtain ⟨i, vs⟩ := x
        simp
        omega

/-- Bridging F-corollary: on the initial one-column matrix, `matrixSem` IS the
    surface `firstMatch`. -/
theorem firstMatch_eq_matrixSem (v : Expr) (ps : List Surface.Pattern) :
    matrixSem v [v] (initMatrix ps) = firstMatch v ps := by
  rw [matrixSem_initMatrix_shift v ps 0]
  cases firstMatch v ps with
  | none => rfl
  | some x => simp


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


/-! ### H1: compiler correctness

`evalDTree ∘ compile` against `matrixSem` — the irreducible heart of the
campaign. First a plumbing layer (occurrence/fetch algebra, width and
captured-occurrence preservation, `evalSwitch` as a `find?`), then Maranget's
S/D equations in capture-aware form, then the main functional induction and
the hypothesis-free surface headline. -/

/-- Occurrence paths compose: fetching along `o₁ ++ o₂` is fetching `o₁` then
    `o₂` from there. -/
private theorem fetch_append (root : Expr) (o₁ o₂ : Occ) :
    fetch root (o₁ ++ o₂) = (fetch root o₁).bind (fun v => fetch v o₂) := by
  induction o₁ generalizing root with
  | nil => simp [fetch]
  | cons i o₁ ih =>
    simp only [List.cons_append, fetch]
    cases hget : getCtorArgs root with
    | none => rfl
    | some ca =>
      obtain ⟨c, args⟩ := ca
      simp only [Option.bind_eq_bind, Option.bind_some]
      cases hidx : args[i]? with
      | none => rfl
      | some a => simp [ih a]

/-- One-step fetch extension: `occ0 ++ [i]` reads field `i` of the ctor value
    at `occ0`. -/
private theorem fetch_snoc_index {root v : Expr} {name : CtorName}
    {args : List Expr} (occ0 : Occ) (i : Nat)
    (hocc : fetch root occ0 = some v)
    (hget : getCtorArgs v = some (name, args)) :
    fetch root (occ0 ++ [i]) = args[i]? := by
  rw [fetch_append, hocc, Option.bind_some]
  simp only [fetch, hget, Option.bind_eq_bind, Option.bind_some]
  cases args[i]? <;> rfl

/-- Reading every index of `args` in order gives back `args`. -/
private theorem range_mapM_getElem? : ∀ (args : List Expr),
    (List.range args.length).mapM (fun i => args[i]?) = some args
  | [] => rfl
  | a :: args => by
    rw [List.length_cons, List.range_succ_eq_map]
    simp [List.mapM_map, Function.comp_def, range_mapM_getElem? args]

/-- The field occurrences of a ctor value all fetch, yielding exactly the
    ctor's argument vector. -/
private theorem fetch_subOccs {v : Expr} {name : CtorName} {args : List Expr}
    (root : Expr) (occ0 : Occ) (hocc : fetch root occ0 = some v)
    (hget : getCtorArgs v = some (name, args)) :
    (subOccs occ0 args.length).mapM (fetch root) = some args := by
  have hfun : (fetch root ∘ fun i => occ0 ++ [i]) = (fun i : Nat => args[i]?) := by
    funext i
    exact fetch_snoc_index occ0 i hocc hget
  rw [subOccs, List.mapM_map, hfun, range_mapM_getElem?]

/-- Inversion of a successful `mapM` on a cons. -/
private theorem mapM_cons_some {f : Occ → Option Expr} {o : Occ} {os : List Occ}
    {vals : List Expr} (h : (o :: os).mapM f = some vals) :
    ∃ v vrest, vals = v :: vrest ∧ f o = some v ∧ os.mapM f = some vrest := by
  cases hv : f o with
  | none => rw [List.mapM_cons, hv] at h; simp at h
  | some v =>
    cases hrest : os.mapM f with
    | none => rw [List.mapM_cons, hv, hrest] at h; simp at h
    | some vrest =>
      rw [List.mapM_cons, hv, hrest] at h
      simp only [Option.bind_eq_bind, Option.bind_some, Option.pure_def,
        Option.some.injEq] at h
      exact ⟨v, vrest, h.symm, rfl, rfl⟩

/-- All-`isSome` pointwise ⇒ the whole `mapM` succeeds. -/
private theorem mapM_isSome {f : Occ → Option Expr} :
    ∀ {l : List Occ}, (∀ o ∈ l, (f o).isSome) → ∃ vs, l.mapM f = some vs
  | [], _ => ⟨[], rfl⟩
  | o :: l, h => by
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp (h o (List.mem_cons_self ..))
    obtain ⟨vs, hvs⟩ := mapM_isSome (fun o' ho' => h o' (List.mem_cons_of_mem _ ho'))
    exact ⟨v :: vs, by rw [List.mapM_cons, hv, hvs]; rfl⟩

/-- A `gctor`-headed row registers its `(ctor, arity)` in `colHeads`. -/
private theorem head_mem_colHeads {M : Matrix} {r : Row} {c : CtorName}
    {pats rest : List GPat} (hr : r ∈ M) (hp : r.pats = .gctor c pats :: rest) :
    (c, pats.length) ∈ colHeads M := by
  simp only [colHeads, List.mem_dedup, List.mem_filterMap]
  exact ⟨r, hr, by rw [hp]; rfl⟩

/-- Row-level width bookkeeping for `specializeRow`. -/
private theorem specializeRow_width {c : CtorName} {a : Nat} {occ0 : Occ}
    {r r' : Row} {w : Nat} (hw : r.pats.length = w + 1)
    (hs : specializeRow c a occ0 r = some r') : r'.pats.length = a + w := by
  obtain ⟨captured, pats, act⟩ := r
  cases pats with
  | nil => simp [specializeRow] at hs
  | cons p prest =>
    have hplen : prest.length = w := by simpa using hw
    cases p with
    | gctor c' cargs =>
      simp only [specializeRow] at hs
      split at hs
      · rename_i hcond
        simp only [Option.some.injEq] at hs
        subst hs
        simp [hcond.2, hplen]
      · simp at hs
    | gbind =>
      simp only [specializeRow, Option.some.injEq] at hs
      subst hs
      simp [hplen]
    | gwild =>
      simp only [specializeRow, Option.some.injEq] at hs
      subst hs
      simp [hplen]

/-- Row-level width bookkeeping for `defaultRow`. -/
private theorem defaultRow_width {occ0 : Occ} {r r' : Row} {w : Nat}
    (hw : r.pats.length = w + 1) (hs : defaultRow occ0 r = some r') :
    r'.pats.length = w := by
  obtain ⟨captured, pats, act⟩ := r
  cases pats with
  | nil => simp [defaultRow] at hs
  | cons p prest =>
    have hplen : prest.length = w := by simpa using hw
    cases p with
    | gctor c' cargs => simp [defaultRow] at hs
    | gbind =>
      simp only [defaultRow, Option.some.injEq] at hs
      subst hs
      simpa using hplen
    | gwild =>
      simp only [defaultRow, Option.some.injEq] at hs
      subst hs
      simpa using hplen

/-- `specialize` preserves the row-width invariant (columns: 1 consumed,
    `a` fields opened). -/
private theorem specialize_width {M : Matrix} {w : Nat}
    (hw : ∀ r ∈ M, r.pats.length = w + 1) (c : CtorName) (a : Nat) (occ0 : Occ) :
    ∀ r' ∈ specialize c a occ0 M, r'.pats.length = a + w := by
  intro r' hr'
  simp only [specialize, List.mem_filterMap] at hr'
  obtain ⟨r, hr, hs⟩ := hr'
  exact specializeRow_width (hw r hr) hs

/-- `defaultMatrix` preserves the row-width invariant (one column consumed). -/
private theorem defaultMatrix_width {M : Matrix} {w : Nat}
    (hw : ∀ r ∈ M, r.pats.length = w + 1) (occ0 : Occ) :
    ∀ r' ∈ defaultMatrix occ0 M, r'.pats.length = w := by
  intro r' hr'
  simp only [defaultMatrix, List.mem_filterMap] at hr'
  obtain ⟨r, hr, hs⟩ := hr'
  exact defaultRow_width (hw r hr) hs

/-- `specializeRow` only ever adds `occ0` to a row's captures. -/
private theorem specializeRow_captured_sub {c : CtorName} {a : Nat} {occ0 : Occ}
    {r r' : Row} (hs : specializeRow c a occ0 r = some r') :
    ∀ o ∈ r'.captured, o ∈ r.captured ∨ o = occ0 := by
  obtain ⟨captured, pats, act⟩ := r
  cases pats with
  | nil => simp [specializeRow] at hs
  | cons p prest =>
    cases p with
    | gctor c' cargs =>
      simp only [specializeRow] at hs
      split at hs
      · simp only [Option.some.injEq] at hs
        subst hs
        intro o ho
        exact Or.inl ho
      · simp at hs
    | gbind =>
      simp only [specializeRow, Option.some.injEq] at hs
      subst hs
      intro o ho
      simpa using ho
    | gwild =>
      simp only [specializeRow, Option.some.injEq] at hs
      subst hs
      intro o ho
      exact Or.inl ho

/-- `defaultRow` only ever adds `occ0` to a row's captures. -/
private theorem defaultRow_captured_sub {occ0 : Occ} {r r' : Row}
    (hs : defaultRow occ0 r = some r') :
    ∀ o ∈ r'.captured, o ∈ r.captured ∨ o = occ0 := by
  obtain ⟨captured, pats, act⟩ := r
  cases pats with
  | nil => simp [defaultRow] at hs
  | cons p prest =>
    cases p with
    | gctor c' cargs => simp [defaultRow] at hs
    | gbind =>
      simp only [defaultRow, Option.some.injEq] at hs
      subst hs
      intro o ho
      simpa using ho
    | gwild =>
      simp only [defaultRow, Option.some.injEq] at hs
      subst hs
      intro o ho
      exact Or.inl ho

/-- `specialize` keeps every captured occurrence fetchable. -/
private theorem specialize_captured {root : Expr} {M : Matrix}
    (hc : ∀ r ∈ M, ∀ o ∈ r.captured, (fetch root o).isSome)
    {occ0 : Occ} (hocc : (fetch root occ0).isSome) (c : CtorName) (a : Nat) :
    ∀ r' ∈ specialize c a occ0 M, ∀ o ∈ r'.captured, (fetch root o).isSome := by
  intro r' hr' o ho
  simp only [specialize, List.mem_filterMap] at hr'
  obtain ⟨r, hr, hs⟩ := hr'
  rcases specializeRow_captured_sub hs o ho with h | rfl
  · exact hc r hr o h
  · exact hocc

/-- `defaultMatrix` keeps every captured occurrence fetchable. -/
private theorem defaultMatrix_captured {root : Expr} {M : Matrix}
    (hc : ∀ r ∈ M, ∀ o ∈ r.captured, (fetch root o).isSome)
    {occ0 : Occ} (hocc : (fetch root occ0).isSome) :
    ∀ r' ∈ defaultMatrix occ0 M, ∀ o ∈ r'.captured, (fetch root o).isSome := by
  intro r' hr' o ho
  simp only [defaultMatrix, List.mem_filterMap] at hr'
  obtain ⟨r, hr, hs⟩ := hr'
  rcases defaultRow_captured_sub hs o ho with h | rfl
  · exact hc r hr o h
  · exact hocc

/-- `evalSwitch` is first-match search over the case list. -/
private theorem evalSwitch_eq_find (root : Expr) (name : CtorName) (arity : Nat) :
    ∀ (cases : List (CtorName × Nat × DTree)) (dflt : DTree),
      evalSwitch root name arity cases dflt
        = match cases.find? (fun x => decide (x.1 = name ∧ x.2.1 = arity)) with
          | some x => evalDTree root x.2.2
          | none => evalDTree root dflt
  | [], dflt => by simp [evalSwitch]
  | (c, a, t) :: rest, dflt => by
    rw [evalSwitch]
    by_cases hca : c = name ∧ a = arity
    · rw [if_pos hca, List.find?_cons_of_pos (by simpa using hca)]
    · rw [if_neg hca, List.find?_cons_of_neg (by simpa using hca),
        evalSwitch_eq_find root name arity rest dflt]

/-- `find?` over a `(ctor, arity, subtree)` case list built from `l` by a
    function of the `(ctor, arity)` pair: a member is found, and — since the
    subtree is DETERMINED by the pair — the result is canonical (duplicates
    carry identical subtrees, so dedup-uniqueness is never needed). -/
private theorem find?_casesList_mem {l : List (CtorName × Nat)} {name : CtorName}
    {arity : Nat} (g : CtorName × Nat → DTree) (hmem : (name, arity) ∈ l) :
    (l.map (fun p => (p.1, p.2, g p))).find?
        (fun x => decide (x.1 = name ∧ x.2.1 = arity))
      = some (name, arity, g (name, arity)) := by
  induction l with
  | nil => simp at hmem
  | cons hd tl ih =>
    obtain ⟨hc, ha⟩ := hd
    rw [List.map_cons]
    by_cases hhd : (hc, ha) = (name, arity)
    · injection hhd with h1 h2
      subst h1
      subst h2
      rw [List.find?_cons_of_pos (by simp)]
    · rw [List.find?_cons_of_neg (by
        simp only [decide_eq_true_eq]
        rintro ⟨h1, h2⟩
        exact hhd (by rw [h1, h2]))]
      refine ih ?_
      rcases List.mem_cons.mp hmem with heq | h
      · exact absurd heq.symm hhd
      · exact h

/-- `find?` fails on a case list none of whose pairs is `(name, arity)`. -/
private theorem find?_casesList_not_mem {l : List (CtorName × Nat)}
    {name : CtorName} {arity : Nat} (g : CtorName × Nat → DTree)
    (hmem : (name, arity) ∉ l) :
    (l.map (fun p => (p.1, p.2, g p))).find?
        (fun x => decide (x.1 = name ∧ x.2.1 = arity)) = none := by
  rw [List.find?_eq_none]
  intro x hx
  simp only [List.mem_map] at hx
  obtain ⟨p, hp, rfl⟩ := hx
  obtain ⟨pc, pa⟩ := p
  simp only [decide_eq_true_eq]
  rintro ⟨h1, h2⟩
  subst h1
  subst h2
  exact hmem hp

/-- Composite: a hit case in a pair-determined case list runs its subtree. -/
private theorem evalSwitch_casesList_mem (root : Expr)
    {l : List (CtorName × Nat)} {name : CtorName} {arity : Nat}
    (g : CtorName × Nat → DTree) (hmem : (name, arity) ∈ l) (dflt : DTree) :
    evalSwitch root name arity (l.map (fun p => (p.1, p.2, g p))) dflt
      = evalDTree root (g (name, arity)) := by
  rw [evalSwitch_eq_find, find?_casesList_mem g hmem]

/-- Composite: a missed case list falls through to the default. -/
private theorem evalSwitch_casesList_not_mem (root : Expr)
    {l : List (CtorName × Nat)} {name : CtorName} {arity : Nat}
    (g : CtorName × Nat → DTree) (hmem : (name, arity) ∉ l) (dflt : DTree) :
    evalSwitch root name arity (l.map (fun p => (p.1, p.2, g p))) dflt
      = evalDTree root dflt := by
  rw [evalSwitch_eq_find, find?_casesList_not_mem g hmem]


/-! ### The S/D equations (capture-aware Maranget) -/

/-- Per-row specialization equation: on a ctor value, a row means exactly what
    its specialization means (dropped rows mean `none`). -/
private theorem rowSem_specializeRow {root v0 : Expr} {vrest : List Expr}
    {occ0 : Occ} {name : CtorName} {args : List Expr}
    (hocc : fetch root occ0 = some v0)
    (hget : getCtorArgs v0 = some (name, args)) (r : Row) :
    rowSem root (v0 :: vrest) r
      = (specializeRow name args.length occ0 r).bind
          (rowSem root (args ++ vrest)) := by
  obtain ⟨captured, pats, act⟩ := r
  cases pats with
  | nil =>
    simp only [specializeRow, Option.bind_none, rowSem, matchGs]
    cases captured.mapM (fetch root) <;> simp
  | cons p prest =>
    cases p with
    | gctor c' cargs =>
      by_cases hcond : c' = name ∧ cargs.length = args.length
      · obtain ⟨rfl, hlen⟩ := hcond
        have hmg : matchG v0 (.gctor c' cargs) = matchGs args cargs := by
          simp [matchG, hget, guard_eq_ite, hlen]
        have hs : specializeRow c' args.length occ0
            ⟨captured, .gctor c' cargs :: prest, act⟩
              = some ⟨captured, cargs ++ prest, act⟩ := by
          simp [specializeRow, hlen]
        rw [hs, Option.bind_some]
        simp only [rowSem, matchGs, hmg]
        rw [matchGs_append hlen.symm]
      · have hmg : matchG v0 (.gctor c' cargs) = none := by
          simp only [matchG, hget, Option.bind_eq_bind, Option.bind_some]
          rw [guard_neg (fun hand => hcond ⟨hand.1.symm, hand.2.symm⟩)]
          rfl
        have hs : specializeRow name args.length occ0
            ⟨captured, .gctor c' cargs :: prest, act⟩ = none := by
          simp [specializeRow, hcond]
        rw [hs, Option.bind_none]
        simp only [rowSem, matchGs, hmg]
        cases captured.mapM (fetch root) <;> simp
    | gbind =>
      simp only [specializeRow, Option.bind_some]
      simp only [rowSem, matchGs, matchG_gbind]
      rw [matchGs_append (by simp :
            args.length = (List.replicate args.length GPat.gwild).length),
          matchGs_replicate_gwild rfl, List.mapM_append]
      simp only [List.mapM_cons, List.mapM_nil, hocc]
      cases captured.mapM (fetch root) <;> cases matchGs vrest prest <;> simp
    | gwild =>
      simp only [specializeRow, Option.bind_some]
      simp only [rowSem, matchGs, matchG_gwild]
      rw [matchGs_append (by simp :
            args.length = (List.replicate args.length GPat.gwild).length),
          matchGs_replicate_gwild rfl]

/-- Maranget's S: on a ctor value, the matrix means exactly what its
    specialization means on the unfolded value vector. -/
theorem matrixSem_specialize {root v0 : Expr} {vrest : List Expr} {occ0 : Occ}
    (M : Matrix) {name : CtorName} {args : List Expr}
    (hocc : fetch root occ0 = some v0)
    (hget : getCtorArgs v0 = some (name, args)) :
    matrixSem root (v0 :: vrest) M
      = matrixSem root (args ++ vrest) (specialize name args.length occ0 M) := by
  induction M with
  | nil => rfl
  | cons r M ih =>
    simp only [matrixSem]
    rw [rowSem_specializeRow hocc hget r, ih]
    simp only [specialize, List.filterMap_cons]
    cases specializeRow name args.length occ0 r with
    | none => simp
    | some r' => simp [matrixSem]

/-- Per-row default equation: when the row's head (if a ctor test) refutes
    the column value, a row means what its default means. -/
private theorem rowSem_defaultRow {root v0 : Expr} {vrest : List Expr}
    {occ0 : Occ} (hocc : fetch root occ0 = some v0) (r : Row)
    (hrefute : ∀ c pats rest, r.pats = .gctor c pats :: rest →
      matchG v0 (.gctor c pats) = none) :
    rowSem root (v0 :: vrest) r = (defaultRow occ0 r).bind (rowSem root vrest) := by
  obtain ⟨captured, pats, act⟩ := r
  cases pats with
  | nil =>
    simp only [defaultRow, Option.bind_none, rowSem, matchGs]
    cases captured.mapM (fetch root) <;> simp
  | cons p prest =>
    cases p with
    | gctor c cargs =>
      have hmg := hrefute c cargs prest rfl
      simp only [defaultRow, Option.bind_none, rowSem, matchGs, hmg]
      cases captured.mapM (fetch root) <;> simp
    | gbind =>
      simp only [defaultRow, Option.bind_some]
      simp only [rowSem, matchGs, matchG_gbind]
      rw [List.mapM_append]
      simp only [List.mapM_cons, List.mapM_nil, hocc]
      cases captured.mapM (fetch root) <;> cases matchGs vrest prest <;> simp
    | gwild =>
      simp only [defaultRow, Option.bind_some]
      simp only [rowSem, matchGs, matchG_gwild]
      cases captured.mapM (fetch root) <;> cases matchGs vrest prest <;> simp

/-- Maranget's D: when no row's head ctor test matches the column value, the
    matrix means what its default means on the popped value vector. Serves the
    pop rule, the switch default, and non-ctor column values alike. -/
theorem matrixSem_default {root v0 : Expr} {vrest : List Expr} {occ0 : Occ}
    (M : Matrix) (hocc : fetch root occ0 = some v0)
    (hrefute : ∀ r ∈ M, ∀ c pats rest, r.pats = .gctor c pats :: rest →
      matchG v0 (.gctor c pats) = none) :
    matrixSem root (v0 :: vrest) M = matrixSem root vrest (defaultMatrix occ0 M) := by
  induction M with
  | nil => rfl
  | cons r M ih =>
    simp only [matrixSem]
    rw [rowSem_defaultRow hocc r (hrefute r (List.mem_cons_self ..)),
        ih (fun r' hr' => hrefute r' (List.mem_cons_of_mem _ hr'))]
    simp only [defaultMatrix, List.filterMap_cons]
    cases defaultRow occ0 r with
    | none => simp
    | some r' => simp [matrixSem]


/-! ### The main theorem -/

/-- H1, matrix form: the compiled tree denotes exactly the matrix semantics,
    given the width invariant, a fully-fetchable occurrence vector, and
    fetchable captured occurrences. Functional induction mirroring `compile`'s
    four cases. -/
theorem compile_correct (root : Expr) (occs : List Occ) (M : Matrix) :
    ∀ vals : List Expr,
      (∀ r ∈ M, r.pats.length = occs.length) →
      occs.mapM (fetch root) = some vals →
      (∀ r ∈ M, ∀ o ∈ r.captured, (fetch root o).isSome) →
      evalDTree root (compile occs M) = matrixSem root vals M := by
  induction occs, M using compile.induct with
  | case1 occs =>
    intro vals _ _ _
    simp [compile, evalDTree, matrixSem]
  | case2 r1 rest =>
    intro vals hw hv hc
    have hvals : vals = [] := by simpa using hv.symm
    subst hvals
    obtain ⟨pre, hpre⟩ := mapM_isSome (hc r1 (List.mem_cons_self ..))
    have hpats : r1.pats = [] :=
      List.length_eq_zero_iff.mp (hw r1 (List.mem_cons_self ..))
    simp [compile, evalDTree, matrixSem, rowSem, hpre, hpats, matchGs]
  | case3 r1 rest occ0 orest hh ih =>
    intro vals hw hv hc
    obtain ⟨v0, vrest, rfl, hocc, hvrest⟩ := mapM_cons_some hv
    have hw' : ∀ r ∈ (r1 :: rest), r.pats.length = orest.length + 1 :=
      fun r hr => by simpa using hw r hr
    have hrefute : ∀ r ∈ (r1 :: rest), ∀ c pats prest,
        r.pats = .gctor c pats :: prest → matchG v0 (.gctor c pats) = none := by
      intro r hr c pats prest hp
      exact absurd (head_mem_colHeads hr hp) (by simp [hh])
    rw [matrixSem_default (r1 :: rest) hocc hrefute]
    rw [compile]
    split
    · exact ih vrest (defaultMatrix_width hw' occ0) hvrest
        (defaultMatrix_captured hc (by simp [hocc]))
    · rename_i heq
      rw [hh] at heq
      exact absurd heq.symm (List.cons_ne_nil _ _)
  | case4 r1 rest occ0 orest hhd htl hh ihcases ihdflt =>
    intro vals hw hv hc
    obtain ⟨v0, vrest, rfl, hocc, hvrest⟩ := mapM_cons_some hv
    have hw' : ∀ r ∈ (r1 :: rest), r.pats.length = orest.length + 1 :=
      fun r hr => by simpa using hw r hr
    rw [compile]
    split
    · rename_i heq
      rw [hh] at heq
      exact absurd heq (List.cons_ne_nil _ _)
    · rename_i hhd' htl' heq
      rw [hh] at heq
      injection heq with h1 h2
      subst h1
      subst h2
      rw [List.attach_map_val (l := hhd :: htl)
        (f := fun p => (p.1, p.2,
          compile (subOccs occ0 p.2 ++ orest)
                  (specialize p.1 p.2 occ0 (r1 :: rest))))]
      cases hgetv : getCtorArgs v0 with
      | none =>
        -- non-ctor column value: the switch falls to the default (iii)
        simp only [evalDTree, hocc, hgetv]
        have hrefute : ∀ r ∈ (r1 :: rest), ∀ c pats prest,
            r.pats = .gctor c pats :: prest → matchG v0 (.gctor c pats) = none := by
          intro r hr c pats prest hp
          simp [matchG, hgetv]
        rw [matrixSem_default (r1 :: rest) hocc hrefute]
        exact ihdflt vrest (defaultMatrix_width hw' occ0) hvrest
          (defaultMatrix_captured hc (by simp [hocc]))
      | some ca =>
        obtain ⟨name, args⟩ := ca
        simp only [evalDTree, hocc, hgetv]
        by_cases hmem : (name, args.length) ∈ hhd :: htl
        · -- hit case: run the specialized subtree
          rw [evalSwitch_casesList_mem root
            (fun p => compile (subOccs occ0 p.2 ++ orest)
              (specialize p.1 p.2 occ0 (r1 :: rest))) hmem,
            matrixSem_specialize (r1 :: rest) hocc hgetv]
          refine ihcases ⟨(name, args.length), hmem⟩ (args ++ vrest) ?_ ?_ ?_
          · intro r' hr'
            have hlen := specialize_width hw' name args.length occ0 r' hr'
            simp only [List.length_append, subOccs, List.length_map,
              List.length_range]
            omega
          · rw [List.mapM_append, fetch_subOccs root occ0 hocc hgetv, hvrest]
            rfl
          · exact specialize_captured hc (by simp [hocc]) name args.length
        · -- miss case: no head test matches — default (ii)
          rw [evalSwitch_casesList_not_mem root
            (fun p => compile (subOccs occ0 p.2 ++ orest)
              (specialize p.1 p.2 occ0 (r1 :: rest))) hmem]
          have hrefute : ∀ r ∈ (r1 :: rest), ∀ c pats prest,
              r.pats = .gctor c pats :: prest → matchG v0 (.gctor c pats) = none := by
            intro r hr c pats prest hp
            cases hm : matchG v0 (.gctor c pats) with
            | none => rfl
            | some cs =>
              obtain ⟨args', hget', hlen', -⟩ := matchG_gctor_iff.mp hm
              rw [hgetv] at hget'
              simp only [Option.some.injEq, Prod.mk.injEq] at hget'
              obtain ⟨rfl, rfl⟩ := hget'
              have hin : (name, pats.length) ∈ colHeads (r1 :: rest) :=
                head_mem_colHeads hr hp
              rw [hh, ← hlen'] at hin
              exact absurd hin hmem
          rw [matrixSem_default (r1 :: rest) hocc hrefute]
          exact ihdflt vrest (defaultMatrix_width hw' occ0) hvrest
            (defaultMatrix_captured hc (by simp [hocc]))

/-- Width of the initial matrix: one column. -/
private theorem initMatrix_width : ∀ (ps : List Surface.Pattern) (k : Nat),
    ∀ r ∈ initMatrix ps k, r.pats.length = 1
  | [], _ => by simp [initMatrix]
  | p :: ps, k => by
    intro r hr
    rw [initMatrix] at hr
    rcases List.mem_cons.mp hr with rfl | hr'
    · rfl
    · exact initMatrix_width ps (k + 1) r hr'

/-- The initial matrix captures nothing yet. -/
private theorem initMatrix_captured : ∀ (ps : List Surface.Pattern) (k : Nat),
    ∀ r ∈ initMatrix ps k, r.captured = []
  | [], _ => by simp [initMatrix]
  | p :: ps, k => by
    intro r hr
    rw [initMatrix] at hr
    rcases List.mem_cons.mp hr with rfl | hr'
    · rfl
    · exact initMatrix_captured ps (k + 1) r hr'

/-- The H1 headline, hypothesis-free: on ANY scrutinee value, the compiled
    tree of a surface match selects exactly the branch (and captures) that the
    trusted surface spec `firstMatch` selects. -/
theorem compile_correct_surface (v : Expr) (ps : List Surface.Pattern) :
    evalDTree v (compile [[]] (initMatrix ps)) = firstMatch v ps := by
  rw [compile_correct v [[]] (initMatrix ps) [v]
      (fun r hr => initMatrix_width ps 0 r hr)
      (by simp [fetch])
      (fun r hr o ho => by
        rw [initMatrix_captured ps 0 r hr] at ho
        simp at ho),
    firstMatch_eq_matrixSem]

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
    -- When the default is `.fail` (complete signature — no surface catch-all,
    -- default matrix empty) emit NO wildcard branch: the named cases already
    -- cover every constructor, so the match is exhaustive AND typeable. Emitting
    -- a `.wildcard` here unconditionally (as an earlier version did) rendered
    -- `.fail` as an untypeable `PatCompFail` sentinel in the wildcard body, which
    -- broke `typecheck` for every enumerated/complete match (including `if`). A
    -- non-`fail` default is a genuine catch-all body → emitted as the wildcard.
    .match_ (resolveOcc env occ)
      (emitCases env bodies occ cases ++
        (match dflt with
          | .fail => []
          | d     => [(.wildcard, emit env bodies d)]))

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


/-! ## Exhaustiveness — internal totality layer (plan step 7, partial)

The behavioural theorem (H1+H2) is done. The remaining **(X)** exhaustiveness
corollary splits into an INTERNAL part (here: pointwise totality
equivalences, immediate from H1) and an INTEGRATION part (surface matrix
covers all ctors of `T` ⇒ emitted term satisfies Core's
`AllMatchesExhaustive` ⇒ feeds `progress`; needs the `CtorEnv` + scrutinee
typing — deferred to bridge integration). A structural `DTree.NoFail`
predicate and its forward-to-totality lemma belong with that integration
slice (they connect to `AllMatchesExhaustive`'s recursive body-exhaustiveness
check and need the ctor-chain `CtorSwitches` hypothesis anyway). -/

/-- `compile`'s tree is total on a value iff the matrix semantics is: by H1
    the two are equal, so totality agrees. Pointwise in the scrutinee. -/
theorem compile_total_iff (root : Expr) (occs : List Occ) (M : Matrix) (vals : List Expr)
    (hw : ∀ r ∈ M, r.pats.length = occs.length)
    (hv : occs.mapM (fetch root) = some vals)
    (hc : ∀ r ∈ M, ∀ o ∈ r.captured, (fetch root o).isSome) :
    (evalDTree root (compile occs M)).isSome ↔ (matrixSem root vals M).isSome := by
  rw [compile_correct root occs M vals hw hv hc]

/-- Surface-level totality: the compiled tree selects a branch on `v` iff the
    surface spec does. This is the pointwise exhaustiveness equivalence; the
    "for all well-typed `v`" lift is integration (needs the scrutinee's ADT
    type to prune non-ctor values, where a non-exhaustive match correctly
    refutes). -/
theorem compile_surface_total_iff (v : Expr) (ps : List Surface.Pattern) :
    (evalDTree v (compile [[]] (initMatrix ps))).isSome ↔ (firstMatch v ps).isSome := by
  rw [compile_correct_surface]



/-! ## H2: adequacy of `emit` against Core's `Step`

The compiled-and-emitted Core term, run under the real small-step semantics,
reaches exactly the branch body and bindings the surface spec prescribes.
Leaf-lets (nested `letIn`s at `DTree` leaves) re-bind captured values at
canonical de Bruijn indices 0..k-1; the proof's base case is
`substN_shiftFrom_cancel` at the leaf-lets' threshold. See the design memo
for the full architecture. Two structural side conditions: `OccsBound`
(every tree occurrence is bound in the emission env — holds for every
`compile` product via `compile_occsBound`) and `CtorSwitches` (every
switched occurrence holds a ctor-chain value — discharged from scrutinee
typing at bridge integration). -/



/-! ## Local `substN`/`shiftFrom`/`instTyAux` node algebra

Core's `BranchList.substN`/`RecGroup.substN` (and the `shiftFrom`/`instTyAux`
companions) are `private`, and ExprClosed's projection lemmas around them are
likewise private — so we re-derive the small kit here, routed through the
public projections `Expr.matchBranchesOf`/`Expr.letRecBindingsOf` (defined in
ExprClosed). Everything reduces definitionally. -/

/-- Rewrite a map to the identity when it is pointwise the identity. -/
private theorem List.map_self_of_mem {α : Type _} {f : α → α} :
    ∀ {l : List α}, (∀ a ∈ l, f a = a) → l.map f = l := by
  intro l
  induction l with
  | nil => intro _; rfl
  | cons a t ih =>
    intro h
    simp only [List.map_cons]
    rw [h a List.mem_cons_self, ih (fun x hx => h x (List.mem_cons_of_mem _ hx))]

/- ### `substN` on `match_`/`letRec` nodes -/

private theorem Expr.substN_match_cons (scrut : Expr) (pat : MatchPattern)
    (body : Expr) (rest : List (MatchPattern × Expr)) (k : Nat) (vs : List Expr) :
    ((Expr.match_ scrut ((pat, body) :: rest)).substN k vs).matchBranchesOf
      = (pat, body.substN (k + pat.bindCount) vs)
        :: ((Expr.match_ scrut rest).substN k vs).matchBranchesOf := rfl

private theorem Expr.substN_matchBranches (vs : List Expr) (scrut : Expr) :
    ∀ (brs : List (MatchPattern × Expr)) (k : Nat),
      ((Expr.match_ scrut brs).substN k vs).matchBranchesOf
        = brs.map (fun pb => (pb.1, pb.2.substN (k + pb.1.bindCount) vs)) := by
  intro brs
  induction brs with
  | nil => intro k; rfl
  | cons hd tl ih =>
    obtain ⟨pat, body⟩ := hd
    intro k
    rw [Expr.substN_match_cons, ih k]
    simp only [List.map_cons]

private theorem Expr.substN_match_eq (scrut : Expr) (brs : List (MatchPattern × Expr))
    (k : Nat) (vs : List Expr) :
    (Expr.match_ scrut brs).substN k vs
      = Expr.match_ (scrut.substN k vs) ((Expr.match_ scrut brs).substN k vs).matchBranchesOf :=
  rfl

/-- `substN` on a `match_`, fully in `List.map` form (the public face of Core's
    private `BranchList.substN`). -/
private theorem Expr.substN_match (scrut : Expr) (brs : List (MatchPattern × Expr))
    (k : Nat) (vs : List Expr) :
    (Expr.match_ scrut brs).substN k vs
      = Expr.match_ (scrut.substN k vs)
          (brs.map (fun pb => (pb.1, pb.2.substN (k + pb.1.bindCount) vs))) := by
  rw [Expr.substN_match_eq, Expr.substN_matchBranches]

private theorem Expr.substN_letRec_headtail (anns : List (Option PolyTy)) (e : Expr)
    (rest : List Expr) (body : Expr) (k : Nat) (vs : List Expr) :
    ((Expr.letRec anns (e :: rest) body).substN k vs).letRecBindingsOf
      = e.substN (k + (e :: rest).length) vs
        :: ((Expr.letRec anns (e :: rest) body).substN k vs).letRecBindingsOf.tail := rfl

private theorem Expr.substN_letRec_bridge (anns : List (Option PolyTy)) (e : Expr)
    (rest : List Expr) (body : Expr) (base : Nat) (vs : List Expr) :
    ((Expr.letRec anns (e :: rest) body).substN base vs).letRecBindingsOf.tail
      = ((Expr.letRec anns rest body).substN (base + 1) vs).letRecBindingsOf := by
  simp only [Expr.substN, Expr.letRecBindingsOf, List.length_cons]
  rw [show base + (rest.length + 1) = base + 1 + rest.length from by omega]
  rfl

private theorem Expr.substN_letRecBindings (vs : List Expr) :
    ∀ (bs : List Expr) (base : Nat) (anns : List (Option PolyTy)) (body : Expr),
      ((Expr.letRec anns bs body).substN base vs).letRecBindingsOf
        = bs.map (·.substN (base + bs.length) vs) := by
  intro bs
  induction bs with
  | nil => intro base anns body; rfl
  | cons e rest ih =>
    intro base anns body
    rw [Expr.substN_letRec_headtail, Expr.substN_letRec_bridge, ih (base + 1) anns body]
    simp only [List.map_cons, List.length_cons]
    congr 1
    apply List.map_congr_left
    intro x _
    congr 1
    omega

private theorem Expr.substN_letRec_eq (anns : List (Option PolyTy)) (bs : List Expr)
    (body : Expr) (k : Nat) (vs : List Expr) :
    (Expr.letRec anns bs body).substN k vs
      = Expr.letRec anns ((Expr.letRec anns bs body).substN k vs).letRecBindingsOf
          (body.substN (k + bs.length) vs) :=
  rfl

/-- `substN` on a `letRec`, fully in `List.map` form. -/
private theorem Expr.substN_letRec (anns : List (Option PolyTy)) (bs : List Expr)
    (body : Expr) (k : Nat) (vs : List Expr) :
    (Expr.letRec anns bs body).substN k vs
      = Expr.letRec anns (bs.map (·.substN (k + bs.length) vs))
          (body.substN (k + bs.length) vs) := by
  rw [Expr.substN_letRec_eq, Expr.substN_letRecBindings]

/- ### `shiftFrom` on `match_`/`letRec` nodes -/

private theorem Expr.shiftFrom_match_cons (scrut : Expr) (pat : MatchPattern)
    (body : Expr) (rest : List (MatchPattern × Expr)) (t n : Nat) :
    ((Expr.match_ scrut ((pat, body) :: rest)).shiftFrom t n).matchBranchesOf
      = (pat, body.shiftFrom (t + pat.bindCount) n)
        :: ((Expr.match_ scrut rest).shiftFrom t n).matchBranchesOf := rfl

private theorem Expr.shiftFrom_matchBranches (n : Nat) (scrut : Expr) :
    ∀ (brs : List (MatchPattern × Expr)) (t : Nat),
      ((Expr.match_ scrut brs).shiftFrom t n).matchBranchesOf
        = brs.map (fun pb => (pb.1, pb.2.shiftFrom (t + pb.1.bindCount) n)) := by
  intro brs
  induction brs with
  | nil => intro t; rfl
  | cons hd tl ih =>
    obtain ⟨pat, body⟩ := hd
    intro t
    rw [Expr.shiftFrom_match_cons, ih t]
    simp only [List.map_cons]

private theorem Expr.shiftFrom_match_eq (scrut : Expr) (brs : List (MatchPattern × Expr))
    (t n : Nat) :
    (Expr.match_ scrut brs).shiftFrom t n
      = Expr.match_ (scrut.shiftFrom t n) ((Expr.match_ scrut brs).shiftFrom t n).matchBranchesOf :=
  rfl

/-- `shiftFrom` on a `match_`, fully in `List.map` form. -/
private theorem Expr.shiftFrom_match (scrut : Expr) (brs : List (MatchPattern × Expr))
    (t n : Nat) :
    (Expr.match_ scrut brs).shiftFrom t n
      = Expr.match_ (scrut.shiftFrom t n)
          (brs.map (fun pb => (pb.1, pb.2.shiftFrom (t + pb.1.bindCount) n))) := by
  rw [Expr.shiftFrom_match_eq, Expr.shiftFrom_matchBranches]

private theorem Expr.shiftFrom_letRec_headtail (anns : List (Option PolyTy)) (e : Expr)
    (rest : List Expr) (body : Expr) (t n : Nat) :
    ((Expr.letRec anns (e :: rest) body).shiftFrom t n).letRecBindingsOf
      = e.shiftFrom (t + (e :: rest).length) n
        :: ((Expr.letRec anns (e :: rest) body).shiftFrom t n).letRecBindingsOf.tail := rfl

private theorem Expr.shiftFrom_letRec_bridge (anns : List (Option PolyTy)) (e : Expr)
    (rest : List Expr) (body : Expr) (base n : Nat) :
    ((Expr.letRec anns (e :: rest) body).shiftFrom base n).letRecBindingsOf.tail
      = ((Expr.letRec anns rest body).shiftFrom (base + 1) n).letRecBindingsOf := by
  simp only [Expr.shiftFrom, Expr.letRecBindingsOf, List.length_cons]
  rw [show base + (rest.length + 1) = base + 1 + rest.length from by omega]
  rfl

private theorem Expr.shiftFrom_letRecBindings (n : Nat) :
    ∀ (bs : List Expr) (base : Nat) (anns : List (Option PolyTy)) (body : Expr),
      ((Expr.letRec anns bs body).shiftFrom base n).letRecBindingsOf
        = bs.map (·.shiftFrom (base + bs.length) n) := by
  intro bs
  induction bs with
  | nil => intro base anns body; rfl
  | cons e rest ih =>
    intro base anns body
    rw [Expr.shiftFrom_letRec_headtail, Expr.shiftFrom_letRec_bridge, ih (base + 1) anns body]
    simp only [List.map_cons, List.length_cons]
    congr 1
    apply List.map_congr_left
    intro x _
    congr 1
    omega

private theorem Expr.shiftFrom_letRec_eq (anns : List (Option PolyTy)) (bs : List Expr)
    (body : Expr) (t n : Nat) :
    (Expr.letRec anns bs body).shiftFrom t n
      = Expr.letRec anns ((Expr.letRec anns bs body).shiftFrom t n).letRecBindingsOf
          (body.shiftFrom (t + bs.length) n) :=
  rfl

/-- `shiftFrom` on a `letRec`, fully in `List.map` form. -/
private theorem Expr.shiftFrom_letRec (anns : List (Option PolyTy)) (bs : List Expr)
    (body : Expr) (t n : Nat) :
    (Expr.letRec anns bs body).shiftFrom t n
      = Expr.letRec anns (bs.map (·.shiftFrom (t + bs.length) n))
          (body.shiftFrom (t + bs.length) n) := by
  rw [Expr.shiftFrom_letRec_eq, Expr.shiftFrom_letRecBindings]

/- ### `substN` on `var` nodes (the three zones) -/

private theorem Expr.substN_var_lt {i k : Nat} (h : i < k) (vs : List Expr)
    (tyArgs : List Ty) :
    (Expr.var i tyArgs).substN k vs = .var i tyArgs := by
  simp only [Expr.substN, if_pos h]

private theorem Expr.substN_var_hit {i k : Nat} {vs : List Expr} (h1 : ¬ i < k)
    (h2 : i - k < vs.length) (tyArgs : List Ty) :
    (Expr.var i tyArgs).substN k vs = ((vs[i - k]).instTy tyArgs).shiftFrom 0 k := by
  simp only [Expr.substN, if_neg h1]
  rw [dif_pos h2]

private theorem Expr.substN_var_beyond {i k : Nat} {vs : List Expr} (h1 : ¬ i < k)
    (h2 : ¬ i - k < vs.length) (tyArgs : List Ty) :
    (Expr.var i tyArgs).substN k vs = .var (i - vs.length) tyArgs := by
  simp only [Expr.substN, if_neg h1]
  rw [dif_neg h2]


/-! ## Closedness / value plumbing for fetched sub-values -/

/-- Term-closedness passes to ctor-chain arguments. -/
theorem varsBelow_getCtorArgs {n : Nat} {v : Expr} {c : CtorName}
    {args : List Expr} (hv : Expr.varsBelow n v = true)
    (hget : getCtorArgs v = some (c, args)) :
    ∀ a ∈ args, Expr.varsBelow n a = true := by
  induction v using Expr.rec_strong generalizing c args with
  | ctor nm =>
    simp only [getCtorArgs, Option.some.injEq, Prod.mk.injEq] at hget
    obtain ⟨rfl, rfl⟩ := hget
    intro a ha
    exact absurd ha (List.not_mem_nil)
  | app f arg ihf _ =>
    simp only [Expr.varsBelow, Bool.and_eq_true] at hv
    cases hf : getCtorArgs f with
    | none => simp [getCtorArgs, hf] at hget
    | some ca =>
      obtain ⟨c', args'⟩ := ca
      simp only [getCtorArgs, hf, Option.bind_eq_bind, Option.bind_some] at hget
      obtain ⟨rfl, rfl⟩ := hget
      intro a ha
      rcases List.mem_append.mp ha with h' | h'
      · exact ihf hv.1 hf a h'
      · rw [List.mem_singleton.mp h']
        exact hv.2
  | primLit p => simp [getCtorArgs] at hget
  | primBinOp op => simp [getCtorArgs] at hget
  | lambda ann body _ => simp [getCtorArgs] at hget
  | var i tyArgs => simp [getCtorArgs] at hget
  | letIn ann rhs body _ _ => simp [getCtorArgs] at hget
  | match_ s brs _ _ => simp [getCtorArgs] at hget
  | letRec anns bs body _ _ => simp [getCtorArgs] at hget

/-- A ctor chain is itself a value. -/
private theorem isValue_of_isCtorChain {v : Expr} (h : IsCtorChain v) : IsValue v := by
  cases h with
  | ctor name => exact .ctor name
  | app hf hv => exact .ctorApp hf hv

/-- Value-ness passes to ctor-chain arguments. -/
theorem isValue_getCtorArgs {v : Expr} {c : CtorName} {args : List Expr}
    (hv : IsValue v) (hget : getCtorArgs v = some (c, args)) :
    ∀ a ∈ args, IsValue a := by
  induction v using Expr.rec_strong generalizing c args with
  | ctor nm =>
    simp only [getCtorArgs, Option.some.injEq, Prod.mk.injEq] at hget
    obtain ⟨rfl, rfl⟩ := hget
    intro a ha
    exact absurd ha (List.not_mem_nil)
  | app f arg ihf _ =>
    cases hf : getCtorArgs f with
    | none => simp [getCtorArgs, hf] at hget
    | some ca =>
      obtain ⟨c', args'⟩ := ca
      simp only [getCtorArgs, hf, Option.bind_eq_bind, Option.bind_some] at hget
      obtain ⟨rfl, rfl⟩ := hget
      cases hv with
      | ctorApp hcf hvarg =>
        intro a ha
        rcases List.mem_append.mp ha with h' | h'
        · exact ihf (isValue_of_isCtorChain hcf) hf a h'
        · rw [List.mem_singleton.mp h']
          exact hvarg
      | primBinOpPartial _ => simp [getCtorArgs] at hf
  | primLit p => simp [getCtorArgs] at hget
  | primBinOp op => simp [getCtorArgs] at hget
  | lambda ann body _ => simp [getCtorArgs] at hget
  | var i tyArgs => simp [getCtorArgs] at hget
  | letIn ann rhs body _ _ => simp [getCtorArgs] at hget
  | match_ s brs _ _ => simp [getCtorArgs] at hget
  | letRec anns bs body _ _ => simp [getCtorArgs] at hget

/-- `getCtorArgs` soundness towards the declarative decomposition used by
    `Step.matchReduce`. (Core has this bridge but keeps it `private`.) -/
theorem getCtorArgs_ctorAppliedTo {v : Expr} {c : CtorName} {args : List Expr}
    (hget : getCtorArgs v = some (c, args)) : CtorAppliedTo v c args := by
  induction v using Expr.rec_strong generalizing c args with
  | ctor nm =>
    simp only [getCtorArgs, Option.some.injEq, Prod.mk.injEq] at hget
    obtain ⟨rfl, rfl⟩ := hget
    exact .base nm
  | app f arg ihf _ =>
    cases hf : getCtorArgs f with
    | none => simp [getCtorArgs, hf] at hget
    | some ca =>
      obtain ⟨c', args'⟩ := ca
      simp only [getCtorArgs, hf, Option.bind_eq_bind, Option.bind_some] at hget
      obtain ⟨rfl, rfl⟩ := hget
      exact .step (ihf hf)
  | primLit p => simp [getCtorArgs] at hget
  | primBinOp op => simp [getCtorArgs] at hget
  | lambda ann body _ => simp [getCtorArgs] at hget
  | var i tyArgs => simp [getCtorArgs] at hget
  | letIn ann rhs body _ _ => simp [getCtorArgs] at hget
  | match_ s brs _ _ => simp [getCtorArgs] at hget
  | letRec anns bs body _ _ => simp [getCtorArgs] at hget

/-- A ctor chain always decomposes via `getCtorArgs` (Core's version of this
    bridge is `private`). -/
private theorem getCtorArgs_of_isCtorChain {v : Expr} (h : IsCtorChain v) :
    ∃ c args, getCtorArgs v = some (c, args) := by
  induction v using Expr.rec_strong with
  | ctor nm => exact ⟨nm, [], rfl⟩
  | app f arg ihf _ =>
    cases h with
    | app hf hv =>
      obtain ⟨c, args, hget⟩ := ihf hf
      exact ⟨c, args ++ [arg], by simp [getCtorArgs, hget]⟩
  | primLit p => cases h
  | primBinOp op => cases h
  | lambda ann body _ => cases h
  | var i tyArgs => cases h
  | letIn ann rhs body _ _ => cases h
  | match_ s brs _ _ => cases h
  | letRec anns bs body _ _ => cases h

/-- Fetched sub-values of a closed value are closed values. -/
theorem fetch_varsBelow {root v : Expr} {o : Occ}
    (hroot : Expr.varsBelow 0 root = true) (h : fetch root o = some v) :
    Expr.varsBelow 0 v = true := by
  induction o generalizing root with
  | nil =>
    simp only [fetch, Option.some.injEq] at h
    exact h ▸ hroot
  | cons i rest ih =>
    simp only [fetch] at h
    cases hget : getCtorArgs root with
    | none => rw [hget] at h; simp at h
    | some ca =>
      obtain ⟨c, args⟩ := ca
      rw [hget] at h
      simp only [Option.bind_eq_bind, Option.bind_some] at h
      cases hidx : args[i]? with
      | none => rw [hidx] at h; simp at h
      | some a =>
        rw [hidx] at h
        simp only [Option.bind_some] at h
        exact ih (varsBelow_getCtorArgs hroot hget a (List.mem_of_getElem? hidx)) h

theorem fetch_isValue {root v : Expr} {o : Occ}
    (hroot : IsValue root) (h : fetch root o = some v) : IsValue v := by
  induction o generalizing root with
  | nil =>
    simp only [fetch, Option.some.injEq] at h
    exact h ▸ hroot
  | cons i rest ih =>
    simp only [fetch] at h
    cases hget : getCtorArgs root with
    | none => rw [hget] at h; simp at h
    | some ca =>
      obtain ⟨c, args⟩ := ca
      rw [hget] at h
      simp only [Option.bind_eq_bind, Option.bind_some] at h
      cases hidx : args[i]? with
      | none => rw [hidx] at h; simp at h
      | some a =>
        rw [hidx] at h
        simp only [Option.bind_some] at h
        exact ih (isValue_getCtorArgs hroot hget a (List.mem_of_getElem? hidx)) h

/-! ### `instTyAux` node algebra (Core's branch-list/rec-group companions are
    private; same projection route as for `substN`/`shiftFrom` above). -/

private theorem Expr.instTyAux_match_eq (Ts : List Ty) (s : Expr)
    (brs : List (MatchPattern × Expr)) (d : Nat) :
    (Expr.match_ s brs).instTyAux d Ts
      = Expr.match_ (s.instTyAux d Ts)
          (((Expr.match_ s brs).instTyAux d Ts).matchBranchesOf) := rfl

private theorem Expr.instTyAux_match_cons (Ts : List Ty) (s : Expr) (p : MatchPattern)
    (b : Expr) (rest : List (MatchPattern × Expr)) (d : Nat) :
    ((Expr.match_ s ((p, b) :: rest)).instTyAux d Ts).matchBranchesOf
      = (p, b.instTyAux d Ts) :: ((Expr.match_ s rest).instTyAux d Ts).matchBranchesOf := rfl

private theorem Expr.instTyAux_letRec_eq (Ts : List Ty) (anns : List (Option PolyTy))
    (bs : List Expr) (body : Expr) (d : Nat) :
    (Expr.letRec anns bs body).instTyAux d Ts
      = Expr.letRec (RecGroup.instAnns d Ts anns)
          (((Expr.letRec anns bs body).instTyAux d Ts).letRecBindingsOf)
          (body.instTyAux d Ts) := rfl

private theorem Expr.instTyAux_letRec_cons_ann (Ts : List Ty) (a : Option PolyTy)
    (as : List (Option PolyTy)) (e : Expr) (rest : List Expr) (body : Expr) (d : Nat) :
    ((Expr.letRec (a :: as) (e :: rest) body).instTyAux d Ts).letRecBindingsOf
      = e.instTyAux (d + RecAnn.params a) Ts
        :: ((Expr.letRec as rest body).instTyAux d Ts).letRecBindingsOf := rfl

private theorem Expr.instTyAux_letRec_cons_nil (Ts : List Ty) (e : Expr)
    (rest : List Expr) (body : Expr) (d : Nat) :
    ((Expr.letRec [] (e :: rest) body).instTyAux d Ts).letRecBindingsOf
      = e.instTyAux d Ts :: ((Expr.letRec [] rest body).instTyAux d Ts).letRecBindingsOf := rfl

private theorem Expr.instTyAux_letRec_nil (Ts : List Ty) (anns : List (Option PolyTy))
    (body : Expr) (d : Nat) :
    ((Expr.letRec anns [] body).instTyAux d Ts).letRecBindingsOf = [] := by
  cases anns <;> rfl

private theorem instTyAux_letRecBindings_length (Ts : List Ty) (body : Expr) :
    ∀ (bs : List Expr) (anns : List (Option PolyTy)) (d : Nat),
      ((Expr.letRec anns bs body).instTyAux d Ts).letRecBindingsOf.length = bs.length := by
  intro bs
  induction bs with
  | nil => intro anns d; rw [Expr.instTyAux_letRec_nil]
  | cons e rest ih =>
    intro anns d
    cases anns with
    | nil => rw [Expr.instTyAux_letRec_cons_nil]; simp only [List.length_cons, ih]
    | cons a as => rw [Expr.instTyAux_letRec_cons_ann]; simp only [List.length_cons, ih]

/-- Type instantiation never touches term variables (any depth). -/
private theorem Expr.varsBelow_instTyAux (Ts : List Ty) :
    ∀ (e : Expr) (n d : Nat),
      Expr.varsBelow n (e.instTyAux d Ts) = Expr.varsBelow n e := by
  intro e
  induction e using Expr.rec_strong with
  | primLit p => intro n d; rfl
  | primBinOp op => intro n d; rfl
  | ctor nm => intro n d; rfl
  | var i tyArgs => intro n d; rfl
  | lambda ann body ih =>
    intro n d
    simp only [Expr.instTyAux, Expr.varsBelow, ih]
  | app f arg ihf iharg =>
    intro n d
    simp only [Expr.instTyAux, Expr.varsBelow, ihf, iharg]
  | letIn ann rhs body ihrhs ihbody =>
    intro n d
    cases ann with
    | none => simp only [Expr.instTyAux, Expr.varsBelow, ihrhs, ihbody]
    | some σ => simp only [Expr.instTyAux, Expr.varsBelow, ihrhs, ihbody]
  | match_ scrut branches ihscrut ihbrs =>
    intro n d
    rw [Expr.instTyAux_match_eq]
    simp only [Expr.varsBelow]
    rw [ihscrut n d]
    congr 1
    induction branches with
    | nil => rfl
    | cons hd tl ihtl =>
      obtain ⟨p, b⟩ := hd
      rw [Expr.instTyAux_match_cons]
      simp only [BranchListClosed.varsBelow]
      rw [ihbrs p b List.mem_cons_self (n + p.bindCount) d,
        ihtl (fun p' b' hm => ihbrs p' b' (List.mem_cons_of_mem _ hm))]
  | letRec anns bindings body ihbindings ihbody =>
    intro n d
    rw [Expr.instTyAux_letRec_eq]
    simp only [Expr.varsBelow]
    rw [instTyAux_letRecBindings_length Ts body bindings anns d,
      ihbody (n + bindings.length) d]
    congr 1
    have key : ∀ (bs : List Expr) (as : List (Option PolyTy)),
        (∀ e ∈ bs, ∀ n' d', Expr.varsBelow n' (e.instTyAux d' Ts) = Expr.varsBelow n' e) →
        ∀ d', RecGroupClosed.varsBelow (n + bindings.length)
            (((Expr.letRec as bs body).instTyAux d' Ts).letRecBindingsOf)
          = RecGroupClosed.varsBelow (n + bindings.length) bs := by
      intro bs
      induction bs with
      | nil => intro as _ d'; rw [Expr.instTyAux_letRec_nil]
      | cons e rest ihrest =>
        intro as hb d'
        cases as with
        | nil =>
          rw [Expr.instTyAux_letRec_cons_nil]
          simp only [RecGroupClosed.varsBelow]
          rw [hb e List.mem_cons_self (n + bindings.length) d',
            ihrest [] (fun x hx => hb x (List.mem_cons_of_mem _ hx)) d']
        | cons a as' =>
          rw [Expr.instTyAux_letRec_cons_ann]
          simp only [RecGroupClosed.varsBelow]
          rw [hb e List.mem_cons_self (n + bindings.length) (d' + RecAnn.params a),
            ihrest as' (fun x hx => hb x (List.mem_cons_of_mem _ hx)) d']
    exact key bindings anns ihbindings d

/-- Type instantiation never touches term variables. -/
theorem Expr.varsBelow_instTy {n : Nat} (e : Expr) (tys : List Ty) :
    Expr.varsBelow n (e.instTy tys) = Expr.varsBelow n e :=
  Expr.varsBelow_instTyAux tys e n 0


/-! ## The substN composition law (the H4 workhorse)

Opening a branch body in two stages — first the pending outer substitution at
threshold `k + ws.length`, then the match's own opening `substN k ws` — equals
opening in one go with the concatenated environment. Requires the OUTER values
closed (they are: they're fetched sub-values of a closed scrutinee); the inner
`ws` need not be. -/

theorem Expr.substN_substN_append (e : Expr) (k : Nat) (ws vs : List Expr)
    (hcl : ∀ v ∈ vs, Expr.varsBelow 0 v = true) :
    (e.substN (k + ws.length) vs).substN k ws = e.substN k (ws ++ vs) := by
  induction e using Expr.rec_strong generalizing k with
  | primLit p => rfl
  | primBinOp op => rfl
  | ctor nm => rfl
  | var i tyArgs =>
    by_cases h1 : i < k
    · -- below every threshold: all three substitutions are the identity
      rw [Expr.substN_var_lt (by omega : i < k + ws.length),
        Expr.substN_var_lt h1, Expr.substN_var_lt h1]
    · by_cases h2 : i - k < ws.length
      · -- the `ws` zone: outer substitution skips, inner and combined agree
        rw [Expr.substN_var_lt (by omega : i < k + ws.length),
          Expr.substN_var_hit h1 h2,
          Expr.substN_var_hit h1 (by simp only [List.length_append]; omega)]
        congr 2
        exact (List.getElem_append_left h2).symm
      · by_cases h3 : i - (k + ws.length) < vs.length
        · -- the `vs` zone: the substituted value is closed, so both sides
          -- collapse to it (shifts and the second substitution are no-ops)
          rw [Expr.substN_var_hit (by omega : ¬ i < k + ws.length) h3,
            Expr.substN_var_hit h1 (by simp only [List.length_append]; omega)]
          have hv : Expr.varsBelow 0 (vs[i - (k + ws.length)]) = true :=
            hcl _ (List.getElem_mem _)
          have hv' : Expr.varsBelow 0 ((vs[i - (k + ws.length)]).instTy tyArgs) = true := by
            rw [Expr.varsBelow_instTy]; exact hv
          have happ : (ws ++ vs)[i - k]'(by simp only [List.length_append]; omega)
              = vs[i - (k + ws.length)]'h3 := by
            rw [List.getElem_append_right (by omega : ws.length ≤ i - k)]
            congr 1
            omega
          rw [happ, Expr.shiftFrom_of_closed hv', Expr.shiftFrom_of_closed hv']
          exact Expr.substN_of_varsBelow ws _ k
            (Expr.varsBelow_mono _ (Nat.zero_le k) hv')
        · -- beyond both: pure index arithmetic
          rw [Expr.substN_var_beyond (by omega : ¬ i < k + ws.length) h3,
            Expr.substN_var_beyond (by omega : ¬ i - vs.length < k) (by omega),
            Expr.substN_var_beyond h1 (by simp only [List.length_append]; omega)]
          simp only [List.length_append]
          congr 1
          omega
  | lambda ann body ih =>
    simp only [Expr.substN]
    rw [show k + ws.length + 1 = (k + 1) + ws.length from by omega, ih (k + 1)]
  | app f arg ihf iharg =>
    simp only [Expr.substN, ihf k, iharg k]
  | letIn ann rhs body ihrhs ihbody =>
    simp only [Expr.substN]
    rw [ihrhs k, show k + ws.length + 1 = (k + 1) + ws.length from by omega,
      ihbody (k + 1)]
  | match_ scrut branches ihscrut ihbrs =>
    rw [Expr.substN_match, Expr.substN_match, Expr.substN_match, ihscrut k,
      List.map_map]
    congr 1
    apply List.map_congr_left
    intro pb hmem
    obtain ⟨pat, body⟩ := pb
    simp only [Function.comp_apply]
    rw [show k + ws.length + pat.bindCount = (k + pat.bindCount) + ws.length from by omega,
      ihbrs pat body hmem (k + pat.bindCount)]
  | letRec anns bindings body ihbindings ihbody =>
    rw [Expr.substN_letRec, Expr.substN_letRec, Expr.substN_letRec, List.map_map,
      List.length_map]
    congr 1
    · apply List.map_congr_left
      intro e hmem
      simp only [Function.comp_apply]
      rw [show k + ws.length + bindings.length
            = (k + bindings.length) + ws.length from by omega,
        ihbindings e hmem (k + bindings.length)]
    · rw [show k + ws.length + bindings.length
            = (k + bindings.length) + ws.length from by omega,
        ihbody (k + bindings.length)]

/-- `substN` with no values is the identity. -/
theorem Expr.substN_nil (e : Expr) (k : Nat) : e.substN k [] = e := by
  induction e using Expr.rec_strong generalizing k with
  | primLit p => rfl
  | primBinOp op => rfl
  | ctor nm => rfl
  | var i tyArgs =>
    by_cases h : i < k
    · rw [Expr.substN_var_lt h]
    · rw [Expr.substN_var_beyond h (by simp)]
      simp
  | lambda ann body ih => simp only [Expr.substN, ih]
  | app f arg ihf iharg => simp only [Expr.substN, ihf, iharg]
  | letIn ann rhs body ihrhs ihbody => simp only [Expr.substN, ihrhs, ihbody]
  | match_ scrut branches ihscrut ihbrs =>
    rw [Expr.substN_match, ihscrut k]
    congr 1
    apply List.map_self_of_mem
    intro pb hmem
    obtain ⟨pat, body⟩ := pb
    simp only [ihbrs pat body hmem]
  | letRec anns bindings body ihbindings ihbody =>
    rw [Expr.substN_letRec, ihbody]
    congr 1
    apply List.map_self_of_mem
    intro e hmem
    exact ihbindings e hmem _

/-- Substitution consumes exactly the shift that made room for it: shift
    `vs.length` binders in at `k`, substitute `vs` at `k`, and you're back
    where you started. (This is what makes the leaf-lets' uniform
    `shiftFrom binds.length env.length` on the body cancel against the
    pending env substitution.) -/
theorem Expr.substN_shiftFrom_cancel (e : Expr) (k : Nat) (vs : List Expr) :
    (e.shiftFrom k vs.length).substN k vs = e := by
  induction e using Expr.rec_strong generalizing k with
  | primLit p => rfl
  | primBinOp op => rfl
  | ctor nm => rfl
  | var i tyArgs =>
    by_cases h : i < k
    · simp only [Expr.shiftFrom, if_pos h]
      rw [Expr.substN_var_lt h]
    · simp only [Expr.shiftFrom, if_neg h]
      rw [Expr.substN_var_beyond (by omega) (by omega)]
      simp
  | lambda ann body ih => simp only [Expr.shiftFrom, Expr.substN, ih]
  | app f arg ihf iharg => simp only [Expr.shiftFrom, Expr.substN, ihf, iharg]
  | letIn ann rhs body ihrhs ihbody =>
    simp only [Expr.shiftFrom, Expr.substN, ihrhs, ihbody]
  | match_ scrut branches ihscrut ihbrs =>
    rw [Expr.shiftFrom_match, Expr.substN_match, List.map_map, ihscrut k]
    congr 1
    apply List.map_self_of_mem
    intro pb hmem
    obtain ⟨pat, body⟩ := pb
    simp only [Function.comp_apply, ihbrs pat body hmem]
  | letRec anns bindings body ihbindings ihbody =>
    rw [Expr.shiftFrom_letRec, Expr.substN_letRec, List.map_map, List.length_map,
      ihbody]
    congr 1
    apply List.map_self_of_mem
    intro e hmem
    simp only [Function.comp_apply, ihbindings e hmem]


/-! ## The structural side conditions -/

/-- Every occurrence referenced by the tree is bound in the emission env
    (switches thread `subOccs occ a ++ env` exactly as `emit` does). -/
inductive OccsBound : List Occ → DTree → Prop
  | fail {env} : OccsBound env .fail
  | leaf {env act binds} :
      (∀ o ∈ binds, o ∈ env) →
      OccsBound env (.leaf act binds)
  | switch {env occ cases dflt} :
      occ ∈ env →
      (∀ c a t', (c, a, t') ∈ cases → OccsBound (subOccs occ a ++ env) t') →
      OccsBound env dflt →
      OccsBound env (.switch occ cases dflt)

/-- `specializeRow` only ever adds `occ0` to a row's captures (re-derivation of
    PatComp's private `specializeRow_captured_sub`). -/
private theorem specializeRow_captured_sub' {c : CtorName} {a : Nat} {occ0 : Occ}
    {r r' : Row} (hs : specializeRow c a occ0 r = some r') :
    ∀ o ∈ r'.captured, o ∈ r.captured ∨ o = occ0 := by
  obtain ⟨captured, pats, act⟩ := r
  cases pats with
  | nil => simp [specializeRow] at hs
  | cons p prest =>
    cases p with
    | gctor c' cargs =>
      simp only [specializeRow] at hs
      split at hs
      · simp only [Option.some.injEq] at hs
        subst hs
        intro o ho
        exact Or.inl ho
      · simp at hs
    | gbind =>
      simp only [specializeRow, Option.some.injEq] at hs
      subst hs
      intro o ho
      simpa using ho
    | gwild =>
      simp only [specializeRow, Option.some.injEq] at hs
      subst hs
      intro o ho
      exact Or.inl ho

/-- `defaultRow` only ever adds `occ0` to a row's captures (re-derivation of
    PatComp's private `defaultRow_captured_sub`). -/
private theorem defaultRow_captured_sub' {occ0 : Occ} {r r' : Row}
    (hs : defaultRow occ0 r = some r') :
    ∀ o ∈ r'.captured, o ∈ r.captured ∨ o = occ0 := by
  obtain ⟨captured, pats, act⟩ := r
  cases pats with
  | nil => simp [defaultRow] at hs
  | cons p prest =>
    cases p with
    | gctor c' cargs => simp [defaultRow] at hs
    | gbind =>
      simp only [defaultRow, Option.some.injEq] at hs
      subst hs
      intro o ho
      simpa using ho
    | gwild =>
      simp only [defaultRow, Option.some.injEq] at hs
      subst hs
      intro o ho
      exact Or.inl ho

/-- `compile` only ever references occurrences from its column vector and its
    rows' capture lists. -/
theorem compile_occsBound (occs : List Occ) (M : Matrix) (env : List Occ)
    (hoccs : ∀ o ∈ occs, o ∈ env)
    (hcap : ∀ r ∈ M, ∀ o ∈ r.captured, o ∈ env) :
    OccsBound env (compile occs M) := by
  revert env
  induction occs, M using compile.induct with
  | case1 occs =>
    intro env _ _
    simp only [compile]
    exact .fail
  | case2 r1 rest =>
    intro env _ hcap
    simp only [compile]
    exact .leaf (hcap r1 (List.mem_cons_self ..))
  | case3 r1 rest occ0 orest hh ih =>
    intro env hoccs hcap
    rw [compile]
    split
    · refine ih env (fun o ho => hoccs o (List.mem_cons_of_mem _ ho)) ?_
      intro r' hr' o ho
      simp only [defaultMatrix, List.mem_filterMap] at hr'
      obtain ⟨r, hr, hs⟩ := hr'
      rcases defaultRow_captured_sub' hs o ho with h | rfl
      · exact hcap r hr o h
      · exact hoccs _ (List.mem_cons_self ..)
    · rename_i heq
      rw [hh] at heq
      exact absurd heq.symm (List.cons_ne_nil _ _)
  | case4 r1 rest occ0 orest hhd htl hh ihcases ihdflt =>
    intro env hoccs hcap
    rw [compile]
    split
    · rename_i heq
      rw [hh] at heq
      exact absurd heq (List.cons_ne_nil _ _)
    · rename_i hhd' htl' heq
      rw [hh] at heq
      injection heq with h1 h2
      subst h1
      subst h2
      rw [List.attach_map_val (l := hhd :: htl)
        (f := fun p => (p.1, p.2,
          compile (subOccs occ0 p.2 ++ orest)
                  (specialize p.1 p.2 occ0 (r1 :: rest))))]
      refine .switch (hoccs occ0 (List.mem_cons_self ..)) ?_ ?_
      · -- each emitted case's subtree, at the field-extended env
        intro c a t' hmem
        simp only [List.mem_map] at hmem
        obtain ⟨p, hp, heq'⟩ := hmem
        obtain ⟨pc, pa⟩ := p
        injection heq' with hc heq''
        injection heq'' with ha ht
        subst hc; subst ha; subst ht
        refine ihcases ⟨(pc, pa), hp⟩ (subOccs occ0 pa ++ env) ?_ ?_
        · intro o ho
          rcases List.mem_append.mp ho with h' | h'
          · exact List.mem_append_left _ h'
          · exact List.mem_append_right _ (hoccs o (List.mem_cons_of_mem _ h'))
        · intro r' hr' o ho
          simp only [specialize, List.mem_filterMap] at hr'
          obtain ⟨r, hr, hs⟩ := hr'
          rcases specializeRow_captured_sub' hs o ho with h | rfl
          · exact List.mem_append_right _ (hcap r hr o h)
          · exact List.mem_append_right _ (hoccs _ (List.mem_cons_self ..))
      · -- the default subtree, same env
        refine ihdflt env (fun o ho => hoccs o (List.mem_cons_of_mem _ ho)) ?_
        intro r' hr' o ho
        simp only [defaultMatrix, List.mem_filterMap] at hr'
        obtain ⟨r, hr, hs⟩ := hr'
        rcases defaultRow_captured_sub' hs o ho with h | rfl
        · exact hcap r hr o h
        · exact hoccs _ (List.mem_cons_self ..)

/-- Every switch the tree *actually reaches* — following `root`'s real ctor at
    each tested occurrence — tests a value that has a constructor. This is
    PATH-SENSITIVE: at a switch we descend only into the single case that
    `root`'s ctor selects (`hit`), or into the default when it selects none
    (`miss`), mirroring `evalDTree`. Off-path subtrees (cases for ctors `root`
    doesn't have at that occurrence) are left unconstrained — crucial, since
    their occurrences may point into a differently-shaped part of `root`.

    Contrast the earlier global form (which recursed into *every* case): that
    was unsatisfiable for well-typed roots whose actual ctor differs from a
    branch's assumption (e.g. `A 5` against patterns testing `B`'s field),
    because an unreached switch would demand `IsCtorChain` of a non-ctor value.
    Dischargeable from scrutinee typing + pattern well-formedness. -/
inductive CtorSwitches (root : Expr) : DTree → Prop
  | fail : CtorSwitches root .fail
  | leaf {act binds} : CtorSwitches root (.leaf act binds)
  | hit {occ cases dflt v name args t'} :
      fetch root occ = some v →
      getCtorArgs v = some (name, args) →
      cases.find? (fun c => decide (c.1 = name ∧ c.2.1 = args.length))
        = some (name, args.length, t') →
      CtorSwitches root t' →
      CtorSwitches root (.switch occ cases dflt)
  | miss {occ cases dflt v name args} :
      fetch root occ = some v →
      getCtorArgs v = some (name, args) →
      cases.find? (fun c => decide (c.1 = name ∧ c.2.1 = args.length)) = none →
      CtorSwitches root dflt →
      CtorSwitches root (.switch occ cases dflt)


/-! ## `mapM (fetch root)` plumbing

`mapM_cons_some` is defined in the H1 section above and reused by the H2
proofs; the remaining lemmas in this subsection are H2-specific. -/

/-- A successful `mapM` preserves length. -/
private theorem mapM_length {f : Occ → Option Expr} :
    ∀ {l : List Occ} {vs : List Expr}, l.mapM f = some vs → vs.length = l.length := by
  intro l
  induction l with
  | nil =>
    intro vs h
    simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at h
    rw [← h]
    rfl
  | cons o os ih =>
    intro vs h
    obtain ⟨v, vrest, rfl, _, hrest⟩ := mapM_cons_some h
    simp only [List.length_cons, ih hrest]

/-- Every value produced by `mapM (fetch root)` on a closed root is closed. -/
private theorem mapM_fetch_closed {root : Expr} (hroot : Expr.varsBelow 0 root = true) :
    ∀ {l : List Occ} {vs : List Expr}, l.mapM (fetch root) = some vs →
      ∀ v ∈ vs, Expr.varsBelow 0 v = true := by
  intro l
  induction l with
  | nil =>
    intro vs h v hv
    simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at h
    rw [← h] at hv
    exact absurd hv (List.not_mem_nil)
  | cons o os ih =>
    intro vs h v hv
    obtain ⟨w, vrest, rfl, hw, hrest⟩ := mapM_cons_some h
    rcases List.mem_cons.mp hv with rfl | hv'
    · exact fetch_varsBelow hroot hw
    · exact ih hrest v hv'

/-- The value vector of a `mapM` serves `idxOf` lookups: position `idxOf o`
    holds `f o` (first occurrence wins; duplicates are harmless since the same
    occurrence fetches the same value). -/
private theorem mapM_idxOf {f : Occ → Option Expr} :
    ∀ {l : List Occ} {vals : List Expr} {o : Occ},
      l.mapM f = some vals → o ∈ l → vals[l.idxOf o]? = f o := by
  intro l
  induction l with
  | nil => intro vals o _ ho; exact absurd ho (List.not_mem_nil)
  | cons e rest ih =>
    intro vals o h ho
    obtain ⟨v, vrest, rfl, hfe, hrest⟩ := mapM_cons_some h
    by_cases heq : e = o
    · subst heq
      rw [List.idxOf_cons_self]
      simpa using hfe.symm
    · rw [List.idxOf_cons_ne _ heq]
      have ho' : o ∈ rest := by
        rcases List.mem_cons.mp ho with rfl | h'
        · exact absurd rfl heq
        · exact h'
      simpa using ih hrest ho'

/-- `substN` on a var node hitting the substitution zone, `getElem?` form. -/
private theorem Expr.substN_var_hit' {i k : Nat} {vs : List Expr} {w : Expr}
    (h1 : ¬ i < k) (h2 : vs[i - k]? = some w) (tyArgs : List Ty) :
    (Expr.var i tyArgs).substN k vs = (w.instTy tyArgs).shiftFrom 0 k := by
  obtain ⟨hlt, hget⟩ := List.getElem?_eq_some_iff.mp h2
  rw [Expr.substN_var_hit h1 hlt, hget]

/-- `substN` pushes through a `letIn` (definitional; named so the leaf-lets
    proof can rewrite one binder layer at a time). -/
private theorem Expr.substN_letIn (ann : Option PolyTy) (rhs body : Expr)
    (k : Nat) (vs : List Expr) :
    (Expr.letIn ann rhs body).substN k vs
      = Expr.letIn ann (rhs.substN k vs) (body.substN (k + 1) vs) := rfl

/-- The emitted var for a bound occurrence, under the pending substitution at
    let-depth `d`, resolves to the occurrence's fetched value. -/
private theorem substN_var_resolve {root : Expr} {env : List Occ} {envVals : List Expr}
    (henv : env.mapM (fetch root) = some envVals)
    (hroot : Expr.varsBelow 0 root = true)
    {o : Occ} {w : Expr} (ho : o ∈ env) (hw : fetch root o = some w) (d : Nat) :
    (Expr.var (env.idxOf o + d) []).substN d envVals = w := by
  have hidx : envVals[env.idxOf o]? = some w := (mapM_idxOf henv ho).trans hw
  rw [Expr.substN_var_hit' (by omega)
    (by rw [Nat.add_sub_cancel]; exact hidx) []]
  rw [Expr.instTy_nil]
  exact Expr.shiftFrom_of_closed (fetch_varsBelow hroot hw) 0 d


/-! ## Leaf-lets adequacy -/

/-- The `emitLets.go` engine: descending the (reversed) capture list at depth
    `d = pendOccs.length`, with the already-reduced outer lets' values
    accumulated as a pending substitution `substN 0 pendVals`, the term
    multi-steps to the body opened with ALL the captures. Generalizes
    `emitLets_adequate` over the (processed, remaining) split. -/
private theorem emitLets_go_adequate {root : Expr} {env : List Occ} {body : Expr}
    {envVals : List Expr} {binds : List Occ} {ws : List Expr}
    (henv : env.mapM (fetch root) = some envVals)
    (hroot : Expr.varsBelow 0 root = true)
    (hws : binds.mapM (fetch root) = some ws)
    (henvlen : envVals.length = env.length) :
    ∀ (rem pendOccs : List Occ) (pendVals : List Expr),
      rem.reverse ++ pendOccs = binds →
      (∀ o ∈ rem, o ∈ env) →
      pendOccs.mapM (fetch root) = some pendVals →
      Relation.ReflTransGen Step
        (((emitLets.go env binds body rem pendOccs.length).substN
            pendOccs.length envVals).substN 0 pendVals)
        (body.substN 0 ws) := by
  intro rem
  induction rem with
  | nil =>
    intro pendOccs pendVals hsplit hb hpend
    simp only [List.reverse_nil, List.nil_append] at hsplit
    have hpw : pendVals = ws := by
      rw [hsplit, hws] at hpend
      exact (Option.some.inj hpend).symm
    show Relation.ReflTransGen Step
      (((body.shiftFrom binds.length env.length).substN
          pendOccs.length envVals).substN 0 pendVals)
      (body.substN 0 ws)
    rw [hsplit, hpw, ← henvlen, Expr.substN_shiftFrom_cancel]
  | cons b rest ih =>
    intro pendOccs pendVals hsplit hb hpend
    -- the value at the head bind
    have hbmem : b ∈ env := hb b List.mem_cons_self
    have hlt : env.idxOf b < envVals.length := by
      rw [henvlen]; exact List.idxOf_lt_length_of_mem hbmem
    obtain ⟨u, hu⟩ : ∃ u, fetch root b = some u :=
      ⟨envVals[env.idxOf b], (mapM_idxOf henv hbmem).symm.trans
        (List.getElem?_eq_getElem hlt)⟩
    have hucl : Expr.varsBelow 0 u = true := fetch_varsBelow hroot hu
    have hpendcl : ∀ v ∈ pendVals, Expr.varsBelow 0 v = true :=
      mapM_fetch_closed hroot hpend
    -- shape of the substituted term: one let with a value RHS
    have hterm :
        ((emitLets.go env binds body (b :: rest) pendOccs.length).substN
            pendOccs.length envVals).substN 0 pendVals
          = .letIn none u
              (((emitLets.go env binds body rest (pendOccs.length + 1)).substN
                  (pendOccs.length + 1) envVals).substN 1 pendVals) := by
      show ((Expr.letIn none (.var (env.idxOf b + pendOccs.length) [])
          (emitLets.go env binds body rest (pendOccs.length + 1))).substN
            pendOccs.length envVals).substN 0 pendVals = _
      rw [Expr.substN_letIn, substN_var_resolve henv hroot hbmem hu,
        Expr.substN_letIn, Expr.substN_of_closed hucl, Nat.zero_add]
    rw [hterm]
    -- the single letReduce step, then compose with the recursive chain
    refine Relation.ReflTransGen.head Step.letReduce ?_
    have hcomp := Expr.substN_substN_append
      ((emitLets.go env binds body rest (pendOccs.length + 1)).substN
        (pendOccs.length + 1) envVals) 0 [u] pendVals hpendcl
    simp only [List.length_singleton, Nat.zero_add, List.singleton_append] at hcomp
    rw [hcomp]
    have hsplit' : rest.reverse ++ (b :: pendOccs) = binds := by
      rw [← hsplit, List.reverse_cons, List.append_assoc]
      rfl
    have hpend' : (b :: pendOccs).mapM (fetch root) = some (u :: pendVals) := by
      rw [List.mapM_cons, hu, hpend]
      rfl
    have := ih (b :: pendOccs) (u :: pendVals) hsplit'
      (fun o ho => hb o (List.mem_cons_of_mem _ ho)) hpend'
    simpa using this

/-- After the pending substitution, the `emitLets` wrapper reduces (by
    `ws.length` `letReduce` steps) to the body opened with exactly the
    captures: capture `j` at de Bruijn `j`, outer refs down by `ws.length` —
    i.e. `body.substN 0 ws`. -/
theorem emitLets_adequate {root : Expr} (env : List Occ) (binds : List Occ)
    (body : Expr) (envVals ws : List Expr)
    (henv : env.mapM (fetch root) = some envVals)
    (hws : binds.mapM (fetch root) = some ws)
    (hroot : Expr.varsBelow 0 root = true)
    (hbound : ∀ o ∈ binds, o ∈ env) :
    Relation.ReflTransGen Step
      ((emitLets env binds body).substN 0 envVals)
      (body.substN 0 ws) := by
  have h := emitLets_go_adequate (body := body) henv hroot hws (mapM_length henv)
    binds.reverse [] []
    (by simp)
    (fun o ho => hbound o (List.mem_reverse.mp ho))
    rfl
  rw [Expr.substN_nil] at h
  exact h


/-! ## Switch plumbing: emitted case lists, `evalSwitch` as `find?`,
    `FirstMatchingBranch` construction, field-occurrence fetching -/

/-- Strong structural recursion over `DTree` exposing membership in a switch's
    case list (the auto-generated recursor buries the nested list). -/
private def DTree.recStrong {motive : DTree → Prop}
    (fail : motive .fail)
    (leaf : ∀ act binds, motive (.leaf act binds))
    (switch : ∀ occ cases dflt,
      (∀ c a t', (c, a, t') ∈ cases → motive t') →
      motive dflt →
      motive (.switch occ cases dflt)) :
    (t : DTree) → motive t
  | .fail => fail
  | .leaf act binds => leaf act binds
  | .switch occ cases dflt =>
      switch occ cases dflt
        (fun _c _a t' _hmem => DTree.recStrong fail leaf switch t')
        (DTree.recStrong fail leaf switch dflt)
termination_by t => sizeOf t
decreasing_by
  all_goals simp_wf
  all_goals first
    | omega
    | (have h := List.sizeOf_lt_of_mem _hmem
       simp only [Prod.mk.sizeOf_spec] at h
       omega)

/-- `emitCases` in `List.map` form. -/
private theorem emitCases_eq_map (env : List Occ) (bodies : Nat → Expr) (occ : Occ) :
    ∀ (cases : List (CtorName × Nat × DTree)),
      emitCases env bodies occ cases
        = cases.map (fun x => (MatchPattern.named x.1 x.2.1,
            emit (subOccs occ x.2.1 ++ env) bodies x.2.2))
  | [] => rfl
  | (c, a, t) :: rest => by
    rw [emitCases, emitCases_eq_map env bodies occ rest, List.map_cons]

/-- `evalSwitch` is first-match search over the case list (re-derivation of
    PatComp's private `evalSwitch_eq_find`). -/
private theorem evalSwitch_eq_find' (root : Expr) (name : CtorName) (arity : Nat) :
    ∀ (cases : List (CtorName × Nat × DTree)) (dflt : DTree),
      evalSwitch root name arity cases dflt
        = match cases.find? (fun x => decide (x.1 = name ∧ x.2.1 = arity)) with
          | some x => evalDTree root x.2.2
          | none => evalDTree root dflt
  | [], dflt => by simp [evalSwitch]
  | (c, a, t) :: rest, dflt => by
    rw [evalSwitch]
    by_cases hca : c = name ∧ a = arity
    · rw [if_pos hca, List.find?_cons_of_pos (by simpa using hca)]
    · rw [if_neg hca, List.find?_cons_of_neg (by simpa using hca),
        evalSwitch_eq_find' root name arity rest dflt]

/-- A hit in the case-list search produces the corresponding
    `FirstMatchingBranch` of the emitted (and post-processed, via `F`) branch
    list: earlier cases fail `matchesCtor`, the found one matches. -/
private theorem firstMatchingBranch_found {name : CtorName} {arity : Nat}
    (F : CtorName × Nat × DTree → Expr) (trailing : List (MatchPattern × Expr)) :
    ∀ (cases : List (CtorName × Nat × DTree)) (x : CtorName × Nat × DTree),
      cases.find? (fun y => decide (y.1 = name ∧ y.2.1 = arity)) = some x →
      SmallStep.FirstMatchingBranch name arity
        (cases.map (fun y => (MatchPattern.named y.1 y.2.1, F y)) ++ trailing)
        (.named x.1 x.2.1) (F x) := by
  intro cases
  induction cases with
  | nil => intro x h; simp at h
  | cons hd tl ih =>
    intro x h
    simp only [List.map_cons, List.cons_append]
    by_cases hp : hd.1 = name ∧ hd.2.1 = arity
    · rw [List.find?_cons_of_pos (by simpa using hp)] at h
      injection h with h
      subst h
      exact .here (by simp [MatchPattern.matchesCtor, hp.1, hp.2])
    · rw [List.find?_cons_of_neg (by simpa using hp)] at h
      refine .there ?_ (ih x h)
      simp only [MatchPattern.matchesCtor, Bool.and_eq_false_iff, beq_eq_false_iff_ne, ne_eq]
      tauto

/-- A miss on every case falls through to the trailing wildcard branch. -/
private theorem firstMatchingBranch_default {name : CtorName} {arity : Nat}
    (F : CtorName × Nat × DTree → Expr) (wbody : Expr) :
    ∀ (cases : List (CtorName × Nat × DTree)),
      (∀ x ∈ cases, ¬(x.1 = name ∧ x.2.1 = arity)) →
      SmallStep.FirstMatchingBranch name arity
        (cases.map (fun y => (MatchPattern.named y.1 y.2.1, F y)) ++ [(.wildcard, wbody)])
        .wildcard wbody := by
  intro cases
  induction cases with
  | nil => intro _; exact .here rfl
  | cons hd tl ih =>
    intro hall
    simp only [List.map_cons, List.cons_append]
    refine .there ?_ (ih (fun x hx => hall x (List.mem_cons_of_mem _ hx)))
    have := hall hd List.mem_cons_self
    simp only [MatchPattern.matchesCtor, Bool.and_eq_false_iff, beq_eq_false_iff_ne, ne_eq]
    tauto

/-- Occurrence paths compose (re-derivation of PatComp's private
    `fetch_append`). -/
private theorem fetch_append' (root : Expr) (o₁ o₂ : Occ) :
    fetch root (o₁ ++ o₂) = (fetch root o₁).bind (fun v => fetch v o₂) := by
  induction o₁ generalizing root with
  | nil => simp [fetch]
  | cons i o₁ ih =>
    simp only [List.cons_append, fetch]
    cases hget : getCtorArgs root with
    | none => rfl
    | some ca =>
      obtain ⟨c, args⟩ := ca
      simp only [Option.bind_eq_bind, Option.bind_some]
      cases hidx : args[i]? with
      | none => rfl
      | some a => simp [ih a]

/-- One-step fetch extension (re-derivation of PatComp's private
    `fetch_snoc_index`). -/
private theorem fetch_snoc_index' {root v : Expr} {name : CtorName}
    {args : List Expr} (occ0 : Occ) (i : Nat)
    (hocc : fetch root occ0 = some v)
    (hget : getCtorArgs v = some (name, args)) :
    fetch root (occ0 ++ [i]) = args[i]? := by
  rw [fetch_append', hocc, Option.bind_some]
  simp only [fetch, hget, Option.bind_eq_bind, Option.bind_some]
  cases args[i]? <;> rfl

/-- Reading every index of `args` in order gives back `args` (re-derivation of
    PatComp's private `range_mapM_getElem?`). -/
private theorem range_mapM_getElem?' : ∀ (args : List Expr),
    (List.range args.length).mapM (fun i => args[i]?) = some args
  | [] => rfl
  | a :: args => by
    rw [List.length_cons, List.range_succ_eq_map]
    simp [List.mapM_map, Function.comp_def, range_mapM_getElem?' args]

/-- The field occurrences of a ctor value fetch to exactly its argument vector
    (re-derivation of PatComp's private `fetch_subOccs`). -/
private theorem fetch_subOccs' {v : Expr} {name : CtorName} {args : List Expr}
    (root : Expr) (occ0 : Occ) (hocc : fetch root occ0 = some v)
    (hget : getCtorArgs v = some (name, args)) :
    (subOccs occ0 args.length).mapM (fetch root) = some args := by
  have hfun : (fetch root ∘ fun i => occ0 ++ [i]) = (fun i : Nat => args[i]?) := by
    funext i
    exact fetch_snoc_index' occ0 i hocc hget
  rw [subOccs, List.mapM_map, hfun, range_mapM_getElem?']

/-- `substN_var_resolve` at let-depth 0 (the `resolveOcc` shape). -/
private theorem substN_var_resolve0 {root : Expr} {env : List Occ} {envVals : List Expr}
    (henv : env.mapM (fetch root) = some envVals)
    (hroot : Expr.varsBelow 0 root = true)
    {o : Occ} {w : Expr} (ho : o ∈ env) (hw : fetch root o = some w) :
    (Expr.var (env.idxOf o) []).substN 0 envVals = w := by
  have := substN_var_resolve henv hroot ho hw 0
  rwa [Nat.add_zero] at this


/-! ## The main adequacy theorem -/

set_option linter.unusedVariables false in  -- the ∀-binder names are docs
/-- **H2.** If the tree selects branch `i` with captures `ws`, the emitted
    Core term — under the pending substitution of its environment's values —
    multi-steps to branch `i`'s body opened with `ws`. Parametric in
    `bodies`, so it applies verbatim to elaborated branch bodies. -/
theorem emit_adequate {root : Expr} (hval : IsValue root)
    (hroot : Expr.varsBelow 0 root = true)
    (bodies : Nat → Expr) :
    ∀ (t : DTree) (env : List Occ) (envVals : List Expr)
      (henv : env.mapM (fetch root) = some envVals)
      (hbound : OccsBound env t)
      (hctor : CtorSwitches root t)
      {i : Nat} {ws : List Expr}
      (heval : evalDTree root t = some (i, ws)),
    Relation.ReflTransGen Step
      ((emit env bodies t).substN 0 envVals)
      ((bodies i).substN 0 ws) := by
  intro t
  induction t using DTree.recStrong with
  | fail =>
    intro env envVals henv hbound hctor i ws heval
    simp [evalDTree] at heval
  | leaf act binds =>
    intro env envVals henv hbound hctor i ws heval
    simp only [evalDTree, Option.map_eq_some_iff] at heval
    obtain ⟨vs, hvs, heq⟩ := heval
    have h1 : act = i := congrArg Prod.fst heq
    have h2 : vs = ws := congrArg Prod.snd heq
    rw [← h1, ← h2]
    cases hbound with
    | leaf hb =>
      exact emitLets_adequate env binds (bodies act) envVals vs henv hvs hroot hb
  | switch occ cases dflt ihcases ihdflt =>
    intro env envVals henv hbound hctor i ws heval
    cases hbound with
    | switch hoccmem hbcases hbdflt =>
    cases hctor with
    | hit hfetch hgc hfind hrec =>
      rename_i v name args t'
      simp only [evalDTree, hfetch, hgc] at heval
      rw [evalSwitch_eq_find' root name args.length cases dflt, hfind] at heval
      have hmem : (name, args.length, t') ∈ cases := List.mem_of_find?_eq_some hfind
      -- Named-branch reduction is independent of the trailing list; case on `dflt`
      -- only so the trailing is concrete (`[]` vs `[wildcard]`) and we avoid
      -- writing a `match dflt` that would generalize dflt-dependent hyps.
      cases dflt with
      | fail =>
        have hemit : (emit env bodies (.switch occ cases .fail)).substN 0 envVals
              = .match_ v (cases.map (fun x => (MatchPattern.named x.1 x.2.1,
                      (emit (subOccs occ x.2.1 ++ env) bodies x.2.2).substN x.2.1 envVals))
                    ++ ([] : List (MatchPattern × Expr))) := by
          show (Expr.match_ (resolveOcc env occ) (emitCases env bodies occ cases
                ++ ([] : List (MatchPattern × Expr)))).substN 0 envVals = _
          rw [Expr.substN_match, resolveOcc, substN_var_resolve0 henv hroot hoccmem hfetch,
            List.map_append, emitCases_eq_map, List.map_map]
          congr 1; congr 1; apply List.map_congr_left; intro x hx
          simp only [Function.comp_apply, MatchPattern.bindCount, Nat.zero_add]
        have hFMB := firstMatchingBranch_found
          (fun x => (emit (subOccs occ x.2.1 ++ env) bodies x.2.2).substN x.2.1 envVals)
          ([] : List (MatchPattern × Expr))
          cases (name, args.length, t') hfind
        have hstep : Step ((emit env bodies (.switch occ cases .fail)).substN 0 envVals)
            (((emit (subOccs occ args.length ++ env) bodies t').substN args.length envVals).substN 0
              (args.take (MatchPattern.named name args.length).bindCount)) := by
          rw [hemit]
          exact Step.matchReduce (fetch_isValue hval hfetch) (getCtorArgs_ctorAppliedTo hgc) hFMB
        rw [show (MatchPattern.named name args.length).bindCount = args.length from rfl,
          List.take_length] at hstep
        have hcomp := Expr.substN_substN_append
          (emit (subOccs occ args.length ++ env) bodies t') 0 args envVals
          (mapM_fetch_closed hroot henv)
        rw [Nat.zero_add] at hcomp
        rw [hcomp] at hstep
        refine Relation.ReflTransGen.head hstep ?_
        have henv' : (subOccs occ args.length ++ env).mapM (fetch root) = some (args ++ envVals) := by
          rw [List.mapM_append, fetch_subOccs' root occ hfetch hgc, henv]; rfl
        exact ihcases name args.length t' hmem (subOccs occ args.length ++ env)
          (args ++ envVals) henv' (hbcases name args.length t' hmem) hrec heval
      | leaf act binds =>
        have hemit : (emit env bodies (.switch occ cases (.leaf act binds))).substN 0 envVals
              = .match_ v (cases.map (fun x => (MatchPattern.named x.1 x.2.1,
                      (emit (subOccs occ x.2.1 ++ env) bodies x.2.2).substN x.2.1 envVals))
                    ++ [(.wildcard, (emit env bodies (.leaf act binds)).substN 0 envVals)]) := by
          show (Expr.match_ (resolveOcc env occ) (emitCases env bodies occ cases
                ++ [(.wildcard, emit env bodies (.leaf act binds))])).substN 0 envVals = _
          rw [Expr.substN_match, resolveOcc, substN_var_resolve0 henv hroot hoccmem hfetch,
            List.map_append, emitCases_eq_map, List.map_map]
          congr 1; congr 1; apply List.map_congr_left; intro x hx
          simp only [Function.comp_apply, MatchPattern.bindCount, Nat.zero_add]
        have hFMB := firstMatchingBranch_found
          (fun x => (emit (subOccs occ x.2.1 ++ env) bodies x.2.2).substN x.2.1 envVals)
          [(.wildcard, (emit env bodies (.leaf act binds)).substN 0 envVals)]
          cases (name, args.length, t') hfind
        have hstep : Step ((emit env bodies (.switch occ cases (.leaf act binds))).substN 0 envVals)
            (((emit (subOccs occ args.length ++ env) bodies t').substN args.length envVals).substN 0
              (args.take (MatchPattern.named name args.length).bindCount)) := by
          rw [hemit]
          exact Step.matchReduce (fetch_isValue hval hfetch) (getCtorArgs_ctorAppliedTo hgc) hFMB
        rw [show (MatchPattern.named name args.length).bindCount = args.length from rfl,
          List.take_length] at hstep
        have hcomp := Expr.substN_substN_append
          (emit (subOccs occ args.length ++ env) bodies t') 0 args envVals
          (mapM_fetch_closed hroot henv)
        rw [Nat.zero_add] at hcomp
        rw [hcomp] at hstep
        refine Relation.ReflTransGen.head hstep ?_
        have henv' : (subOccs occ args.length ++ env).mapM (fetch root) = some (args ++ envVals) := by
          rw [List.mapM_append, fetch_subOccs' root occ hfetch hgc, henv]; rfl
        exact ihcases name args.length t' hmem (subOccs occ args.length ++ env)
          (args ++ envVals) henv' (hbcases name args.length t' hmem) hrec heval
      | switch occ' cases' dflt' =>
        have hemit : (emit env bodies (.switch occ cases (.switch occ' cases' dflt'))).substN 0 envVals
              = .match_ v (cases.map (fun x => (MatchPattern.named x.1 x.2.1,
                      (emit (subOccs occ x.2.1 ++ env) bodies x.2.2).substN x.2.1 envVals))
                    ++ [(.wildcard, (emit env bodies (.switch occ' cases' dflt')).substN 0 envVals)]) := by
          show (Expr.match_ (resolveOcc env occ) (emitCases env bodies occ cases
                ++ [(.wildcard, emit env bodies (.switch occ' cases' dflt'))])).substN 0 envVals = _
          rw [Expr.substN_match, resolveOcc, substN_var_resolve0 henv hroot hoccmem hfetch,
            List.map_append, emitCases_eq_map, List.map_map]
          congr 1; congr 1; apply List.map_congr_left; intro x hx
          simp only [Function.comp_apply, MatchPattern.bindCount, Nat.zero_add]
        have hFMB := firstMatchingBranch_found
          (fun x => (emit (subOccs occ x.2.1 ++ env) bodies x.2.2).substN x.2.1 envVals)
          [(.wildcard, (emit env bodies (.switch occ' cases' dflt')).substN 0 envVals)]
          cases (name, args.length, t') hfind
        have hstep : Step ((emit env bodies (.switch occ cases (.switch occ' cases' dflt'))).substN 0 envVals)
            (((emit (subOccs occ args.length ++ env) bodies t').substN args.length envVals).substN 0
              (args.take (MatchPattern.named name args.length).bindCount)) := by
          rw [hemit]
          exact Step.matchReduce (fetch_isValue hval hfetch) (getCtorArgs_ctorAppliedTo hgc) hFMB
        rw [show (MatchPattern.named name args.length).bindCount = args.length from rfl,
          List.take_length] at hstep
        have hcomp := Expr.substN_substN_append
          (emit (subOccs occ args.length ++ env) bodies t') 0 args envVals
          (mapM_fetch_closed hroot henv)
        rw [Nat.zero_add] at hcomp
        rw [hcomp] at hstep
        refine Relation.ReflTransGen.head hstep ?_
        have henv' : (subOccs occ args.length ++ env).mapM (fetch root) = some (args ++ envVals) := by
          rw [List.mapM_append, fetch_subOccs' root occ hfetch hgc, henv]; rfl
        exact ihcases name args.length t' hmem (subOccs occ args.length ++ env)
          (args ++ envVals) henv' (hbcases name args.length t' hmem) hrec heval
    | miss hfetch hgc hfind hrec =>
      rename_i v name args
      simp only [evalDTree, hfetch, hgc] at heval
      rw [evalSwitch_eq_find' root name args.length cases dflt, hfind] at heval
      cases dflt with
      | fail =>
        simp [evalDTree] at heval
      | leaf act binds =>
        have hemit : (emit env bodies (.switch occ cases (.leaf act binds))).substN 0 envVals
              = .match_ v (cases.map (fun x => (MatchPattern.named x.1 x.2.1,
                      (emit (subOccs occ x.2.1 ++ env) bodies x.2.2).substN x.2.1 envVals))
                    ++ [(.wildcard, (emit env bodies (.leaf act binds)).substN 0 envVals)]) := by
          show (Expr.match_ (resolveOcc env occ) (emitCases env bodies occ cases
                ++ [(.wildcard, emit env bodies (.leaf act binds))])).substN 0 envVals = _
          rw [Expr.substN_match, resolveOcc, substN_var_resolve0 henv hroot hoccmem hfetch,
            List.map_append, emitCases_eq_map, List.map_map]
          congr 1; congr 1; apply List.map_congr_left; intro x hx
          simp only [Function.comp_apply, MatchPattern.bindCount, Nat.zero_add]
        have hall : ∀ x ∈ cases, ¬(x.1 = name ∧ x.2.1 = args.length) := by
          intro x hx; simpa using List.find?_eq_none.mp hfind x hx
        have hFMB := firstMatchingBranch_default
          (fun x => (emit (subOccs occ x.2.1 ++ env) bodies x.2.2).substN x.2.1 envVals)
          ((emit env bodies (.leaf act binds)).substN 0 envVals) cases hall
        have hstep : Step ((emit env bodies (.switch occ cases (.leaf act binds))).substN 0 envVals)
            (((emit env bodies (.leaf act binds)).substN 0 envVals).substN 0
              (args.take MatchPattern.wildcard.bindCount)) := by
          rw [hemit]
          exact Step.matchReduce (fetch_isValue hval hfetch) (getCtorArgs_ctorAppliedTo hgc) hFMB
        rw [show MatchPattern.wildcard.bindCount = 0 from rfl, List.take_zero, Expr.substN_nil] at hstep
        exact Relation.ReflTransGen.head hstep (ihdflt env envVals henv hbdflt hrec heval)
      | switch occ' cases' dflt' =>
        have hemit : (emit env bodies (.switch occ cases (.switch occ' cases' dflt'))).substN 0 envVals
              = .match_ v (cases.map (fun x => (MatchPattern.named x.1 x.2.1,
                      (emit (subOccs occ x.2.1 ++ env) bodies x.2.2).substN x.2.1 envVals))
                    ++ [(.wildcard, (emit env bodies (.switch occ' cases' dflt')).substN 0 envVals)]) := by
          show (Expr.match_ (resolveOcc env occ) (emitCases env bodies occ cases
                ++ [(.wildcard, emit env bodies (.switch occ' cases' dflt'))])).substN 0 envVals = _
          rw [Expr.substN_match, resolveOcc, substN_var_resolve0 henv hroot hoccmem hfetch,
            List.map_append, emitCases_eq_map, List.map_map]
          congr 1; congr 1; apply List.map_congr_left; intro x hx
          simp only [Function.comp_apply, MatchPattern.bindCount, Nat.zero_add]
        have hall : ∀ x ∈ cases, ¬(x.1 = name ∧ x.2.1 = args.length) := by
          intro x hx; simpa using List.find?_eq_none.mp hfind x hx
        have hFMB := firstMatchingBranch_default
          (fun x => (emit (subOccs occ x.2.1 ++ env) bodies x.2.2).substN x.2.1 envVals)
          ((emit env bodies (.switch occ' cases' dflt')).substN 0 envVals) cases hall
        have hstep : Step ((emit env bodies (.switch occ cases (.switch occ' cases' dflt'))).substN 0 envVals)
            (((emit env bodies (.switch occ' cases' dflt')).substN 0 envVals).substN 0
              (args.take MatchPattern.wildcard.bindCount)) := by
          rw [hemit]
          exact Step.matchReduce (fetch_isValue hval hfetch) (getCtorArgs_ctorAppliedTo hgc) hFMB
        rw [show MatchPattern.wildcard.bindCount = 0 from rfl, List.take_zero, Expr.substN_nil] at hstep
        exact Relation.ReflTransGen.head hstep (ihdflt env envVals henv hbdflt hrec heval)


/-! ## The composed headline (uses H1 = `compile_correct_surface`) -/

/-- The initial matrix captures nothing yet (re-derivation of PatComp's
    private `initMatrix_captured`). -/
private theorem initMatrix_captured' : ∀ (ps : List Surface.Pattern) (k : Nat),
    ∀ r ∈ initMatrix ps k, r.captured = []
  | [], _ => by simp [initMatrix]
  | p :: ps, k => by
    intro r hr
    rw [initMatrix] at hr
    rcases List.mem_cons.mp hr with rfl | hr'
    · rfl
    · exact initMatrix_captured' ps (k + 1) r hr'

/-- **Top-level behavioural correctness of one lowered match** (modulo the
    typing-dischargeable `CtorSwitches`): if the surface spec says branch `i`
    fires with captures `ws`, the compiled-and-emitted Core term reduces,
    under Core's real small-step semantics, to branch `i`'s body with exactly
    those values substituted. -/
theorem lowerMatch_adequate {v : Expr} {ps : List Surface.Pattern}
    (bodies : Nat → Expr)
    (hval : IsValue v) (hclosed : Expr.varsBelow 0 v = true)
    (hctor : CtorSwitches v (compile [[]] (initMatrix ps)))
    {i : Nat} {ws : List Expr}
    (hmatch : firstMatch v ps = some (i, ws)) :
    Relation.ReflTransGen Step
      (lowerMatch v ps bodies)
      ((bodies i).substN 0 ws) := by
  refine Relation.ReflTransGen.head Step.letReduce ?_
  refine emit_adequate hval hclosed bodies _ [[]] [v] ?_ ?_ hctor ?_
  · -- the singleton env fetches to the scrutinee itself
    rfl
  · -- every referenced occurrence is bound in the root env `[[]]`
    refine compile_occsBound [[]] (initMatrix ps) [[]] (fun o ho => ho) ?_
    intro r hr o ho
    rw [initMatrix_captured' ps 0 r hr] at ho
    exact absurd ho (List.not_mem_nil)
  · -- H1 turns the tree's verdict into the surface verdict
    rw [compile_correct_surface]
    exact hmatch


/-! ## Discharging `CtorSwitches` from typing — the integration keystone

`lowerMatch_adequate` above is conditional on `CtorSwitches root tree`. Here we
DISCHARGE that hypothesis from scrutinee typing + pattern well-formedness,
making the theorem unconditional (the final form the surface bridge consumes).

The keystone is `GPatWF`: a well-formedness relation typing the (normalised)
patterns against the scrutinee's Core type. A `gctor c` test is well-formed
only at a `customTy`, and its sub-patterns must respect `c`'s (instantiated)
field types — exactly what rules out ctor-tests at non-ADT positions, which
would otherwise make the (path-sensitive) `CtorSwitches` unprovable. -/

mutual
/-- A generic pattern is well-formed at Core type `τ` wrt a ctor env: binds and
    wildcards fit any type; a `gctor c` test requires `τ` to be `c`'s ADT type
    and its sub-patterns to fit `c`'s instantiated field types. -/
inductive GPatWF (ctors : CtorEnv) : GPat → Ty → Prop
  | gbind {τ} : GPatWF ctors .gbind τ
  | gwild {τ} : GPatWF ctors .gwild τ
  | gctor {c args T tyArgs ctor fieldTys} :
      LookupList.get? ctors c = some ctor →
      ctor.tyName = T →
      List.Forall₂ (InstantiatesBy tyArgs) ctor.contents fieldTys →
      GPatWFList ctors args fieldTys →
      GPatWF ctors (.gctor c args) (.customTy T tyArgs)
/-- Pointwise `GPatWF` of a pattern vector against a column-type vector. -/
inductive GPatWFList (ctors : CtorEnv) : List GPat → List Ty → Prop
  | nil : GPatWFList ctors [] []
  | cons {p ps τ τs} :
      GPatWF ctors p τ → GPatWFList ctors ps τs →
      GPatWFList ctors (p :: ps) (τ :: τs)
end

/-- Path invariant: the value at occurrence `occ` in `root` is present, a value,
    and well-typed at the column type `τ`. Threaded (parallel to the `occs`
    vector) through `compile`'s recursion; maintained across a `hit` because the
    matched ctor's fields inherit its instantiated field types. -/
def OccTyped (ctors : CtorEnv) (root : Expr) (occ : Occ) (τ : Ty) : Prop :=
  ∃ w, fetch root occ = some w ∧ IsValue w ∧ TypeOfElabHM ⟨[], ctors⟩ w τ

/-! ### Helpers for `compile_ctorSwitches_aux`

These thread `GPatWF`/`OccTyped` through `compile`'s matrix reshaping
(`defaultRow`/`specializeRow`) and relate a typed ctor-chain value's fields to
a `gctor` pattern's instantiated field types (the crux of the `hit` case). -/

private theorem GPatWFList.forall₂ {ctors : CtorEnv} {l t} :
    GPatWFList ctors l t → List.Forall₂ (GPatWF ctors) l t
  | .nil => .nil
  | .cons hp htl => .cons hp htl.forall₂

private theorem GPatWFList.of_forall₂ {ctors : CtorEnv} : ∀ {l t},
    List.Forall₂ (GPatWF ctors) l t → GPatWFList ctors l t
  | _, _, .nil => .nil
  | _, _, .cons hp htl => .cons hp (GPatWFList.of_forall₂ htl)

private theorem Forall₂_append {α β : Type _} (R : α → β → Prop) {l1 t1 l2 t2}
    (h1 : List.Forall₂ R l1 t1) (h2 : List.Forall₂ R l2 t2) :
    List.Forall₂ R (l1 ++ l2) (t1 ++ t2) := by
  induction h1 with
  | nil => simp only [List.nil_append]; exact h2
  | cons hp hps ih => simp only [List.cons_append]; exact .cons hp ih

private theorem Forall₂_length {α β : Type _} (R : α → β → Prop) :
    ∀ {l1 l2}, List.Forall₂ R l1 l2 → l1.length = l2.length := by
  intro l1 l2 h
  induction h with
  | nil => rfl
  | cons _ htl ih => simp only [List.length_cons, ih]

private theorem GPatWFList_append {ctors : CtorEnv} {l1 t1 l2 t2}
    (h1 : GPatWFList ctors l1 t1) (h2 : GPatWFList ctors l2 t2) :
    GPatWFList ctors (l1 ++ l2) (t1 ++ t2) :=
  GPatWFList.of_forall₂ (Forall₂_append _ h1.forall₂ h2.forall₂)

/-- Inversion of `GPatWF.gctor`, naming every existential (the type args, the ctor
    entry, and the instantiated field types). -/
private theorem GPatWF.gctor_inv {ctors : CtorEnv} {c : CtorName} {cargs : List GPat} {τ : Ty}
    (h : GPatWF ctors (.gctor c cargs) τ) :
    ∃ T tyArgs ctor fieldTys, τ = .customTy T tyArgs ∧ LookupList.get? ctors c = some ctor ∧
      ctor.tyName = T ∧ List.Forall₂ (InstantiatesBy tyArgs) ctor.contents fieldTys ∧
      GPatWFList ctors cargs fieldTys := by
  cases h with
  | gctor hlook hname hinst hwfargs => exact ⟨_, _, _, _, rfl, hlook, hname, hinst, hwfargs⟩

private theorem GPatWFList_replicate_gwild : ∀ (n : Nat) (tys : List Ty),
    tys.length = n → GPatWFList ctors (List.replicate n GPat.gwild) tys
  | 0, [], _ => .nil
  | 0, _ :: _, h => by simp at h
  | n + 1, [], h => by simp at h
  | n + 1, τ :: τs, h => by
    rw [List.length_cons] at h
    simp only [List.replicate_succ]
    exact .cons .gwild (GPatWFList_replicate_gwild n τs (by omega))

/-- `defaultRow` keeps `gbind`/`gwild`-headed rows (dropping their head column),
    so the tail of the row's `GPatWFList` (at the tail column types) is preserved. -/
private theorem defaultRow_wf {ctors : CtorEnv} {occ0 : Occ} {τ0 : Ty} {ttys : List Ty}
    {r r' : Row} (hwf : GPatWFList ctors r.pats (τ0 :: ttys))
    (hs : defaultRow occ0 r = some r') :
    GPatWFList ctors r'.pats ttys := by
  obtain ⟨captured, pats, act⟩ := r
  cases pats with
  | nil => simp [defaultRow] at hs
  | cons p prest =>
    cases p with
    | gctor c cargs => simp [defaultRow] at hs
    | gbind =>
      simp only [defaultRow, Option.some.injEq] at hs
      subst hs
      cases hwf with | cons _ htl => exact htl
    | gwild =>
      simp only [defaultRow, Option.some.injEq] at hs
      subst hs
      cases hwf with | cons _ htl => exact htl

/-- Two pointwise instantiations of one source list coincide when the two
    argument lists agree below `n` and the source is `bvar`-bounded by `n`. -/
private theorem InstantiatesBy_forall2_det_agree {tyArgs1 tyArgs2 : List Ty} {n : Nat}
    (hag : ∀ k, k < n → tyArgs1[k]? = tyArgs2[k]?)
    {tys l1 l2 : List Ty}
    (hbound : ∀ c ∈ tys, ContainsBvarsUpTo n c)
    (h1 : List.Forall₂ (InstantiatesBy tyArgs1) tys l1)
    (h2 : List.Forall₂ (InstantiatesBy tyArgs2) tys l2) : l1 = l2 := by
  induction h1 generalizing l2 with
  | nil => cases h2; rfl
  | cons hi1 h1tl ih =>
    cases h2 with
    | cons hi2 h2tl =>
      have hhd := InstantiatesBy.det_agree hag (hbound _ List.mem_cons_self) hi1 hi2
      rw [hhd, ih (fun c hc => hbound c (List.mem_cons_of_mem _ hc)) h2tl]

private theorem get?_cons_zero {α : Type _} (a : α) (l : List α) : (a :: l)[0]? = some a := rfl

private theorem get?_cons_succ {α : Type _} (a : α) (l : List α) (n : Nat) :
    (a :: l)[n + 1]? = l[n]? := rfl

/-- From `Forall₂ (InstantiatesBy tyArgs') (bvarRangeFrom start n) tyArgs`: the
    `k`-th entry (k < n) forces `tyArgs[k]? = tyArgs'[start + k]?`. -/
private theorem bvarRangeFrom_forall₂_agreement {tyArgs tyArgs' : List Ty} :
    ∀ {start n : Nat},
      List.Forall₂ (InstantiatesBy tyArgs') (Ty.bvarRangeFrom start n) tyArgs →
      ∀ k, k < n → tyArgs[k]? = tyArgs'[start + k]?
  | start, 0, h, k, hk => by simp [Ty.bvarRangeFrom] at h; cases h; omega
  | start, n + 1, h, k, hk => by
    simp only [Ty.bvarRangeFrom] at h
    cases h with
    | cons hhd htl =>
      cases hhd with
      | bvar hidx =>
        cases k with
        | zero => rw [get?_cons_zero, Nat.add_zero, hidx]
        | succ k =>
          rw [get?_cons_succ, bvarRangeFrom_forall₂_agreement htl k (by omega),
            show (start + 1) + k = start + (k + 1) from by omega]

private theorem bvarRange_forall₂_agreement {tyArgs tyArgs' : List Ty} {n : Nat}
    (h : List.Forall₂ (InstantiatesBy tyArgs') (Ty.bvarRange n) tyArgs) (k : Nat) (hk : k < n) :
    tyArgs[k]? = tyArgs'[k]? := by
  have := bvarRangeFrom_forall₂_agreement h k hk
  rwa [Nat.zero_add] at this

/-- A successful `mapM` gives a pointwise `Forall₂` of `f a = some b`. -/
private theorem mapM_forall₂_of_eq {α β : Type _} (f : α → Option β) :
    ∀ {l : List α} {vs : List β}, l.mapM f = some vs →
      List.Forall₂ (fun a b => f a = some b) l vs
  | [], vs => by
    intro h; rw [List.mapM_nil] at h; injection h with hvs; subst hvs; exact .nil
  | a :: l, vs => by
    intro h
    rw [List.mapM_cons] at h
    cases hfa : f a with
    | none => simp [hfa] at h
    | some b =>
      cases hrest : l.mapM f with
      | none => simp [hrest] at h
      | some rest =>
        rw [hfa, hrest] at h
        simp only [Option.bind_eq_bind, Option.bind_some, Option.pure_def,
          Option.some.injEq] at h
        obtain rfl := h.symm
        exact .cons hfa (mapM_forall₂_of_eq f hrest)

/-- Combine `Forall₂ R` with a pointwise `P` over the left list. -/
private theorem Forall₂_and_of_forall {α β : Type _} (R : α → β → Prop) (P : α → Prop)
    {l1 l2} (hR : List.Forall₂ R l1 l2) (hP : ∀ a ∈ l1, P a) :
    List.Forall₂ (fun a b => P a ∧ R a b) l1 l2 := by
  induction hR with
  | nil => exact .nil
  | cons hhd htl ih =>
    exact .cons ⟨hP _ List.mem_cons_self, hhd⟩
      (ih (fun a ha => hP a (List.mem_cons_of_mem _ ha)))

/-- Relay two `Forall₂`s through a shared middle list. -/
private theorem Forall₂_relay {α β γ : Type _} (R : α → β → Prop) (S : β → γ → Prop)
    (T : α → γ → Prop) (hrel : ∀ a b c, R a b → S b c → T a c)
    {l1 l2 l3} (h1 : List.Forall₂ R l1 l2) (h2 : List.Forall₂ S l2 l3) :
    List.Forall₂ T l1 l3 := by
  induction h1 generalizing l3 with
  | nil => cases h2; exact .nil
  | cons hr h1tl ih =>
    cases h2 with
    | cons hs h2tl => exact .cons (hrel _ _ _ hr hs) (ih h2tl)

/-- A ctor-chain value's args are typed at the `gctor` pattern's instantiated field
    types: the inversion's per-arg types (instantiated by the value's `tyArgs'`)
    coincide with the pattern's (`tyArgs`) by `InstantiatesBy.det_agree`, since the
    two argument lists agree below `ctor.paramCount` (from the saturated
    `customTy` instantiation) and the field types are `bvar`-bounded. -/
private theorem args_typed_fieldTys {ctors : CtorEnv} {ctor : Ctor}
    {tyArgs tyArgs' : List Ty} {fieldTys : List Ty} {args : List Expr}
    (hbound : ∀ c ∈ ctor.contents, ContainsBvarsUpTo ctor.paramCount c)
    (hinst : List.Forall₂ (InstantiatesBy tyArgs) ctor.contents fieldTys)
    (hfor : List.Forall₂
      (fun a c => ∃ ct, InstantiatesBy tyArgs' c ct ∧ TypeOfElabHM ⟨[], ctors⟩ a ct)
      args ctor.contents)
    (hagr : List.Forall₂ (InstantiatesBy tyArgs') (Ty.bvarRange ctor.paramCount) tyArgs) :
    List.Forall₂ (fun a ft => TypeOfElabHM ⟨[], ctors⟩ a ft) args fieldTys := by
  revert hbound hinst hfor
  generalize ctor.contents = c
  intro hbound hinst hfor
  have hag : ∀ k, k < ctor.paramCount → tyArgs[k]? = tyArgs'[k]? :=
    fun k hk => bvarRange_forall₂_agreement hagr k hk
  induction hfor generalizing fieldTys with
  | nil => cases hinst; exact .nil
  | cons hhd hfortl ih =>
    obtain ⟨ct, hct, htyped⟩ := hhd
    cases hinst with
    | cons hinst_hd hinst_tl =>
      have hdet := InstantiatesBy.det_agree hag (hbound _ List.mem_cons_self) hinst_hd hct
      subst hdet
      exact .cons htyped
        (ih (fun c' hc' => hbound c' (List.mem_cons_of_mem _ hc')) hinst_tl)

/-- The field occurrences of a ctor value are `OccTyped` at the field types:
    each `occ0 ++ [i]` fetches `args[i]` (a value, well-typed at `fieldTys[i]`). -/
private theorem occTyped_subOccs {ctors : CtorEnv} {root v : Expr} {name : CtorName}
    {args : List Expr} {occ0 : Occ} {fieldTys : List Ty}
    (hfetch : fetch root occ0 = some v)
    (hget : getCtorArgs v = some (name, args))
    (hvals : ∀ a ∈ args, IsValue a)
    (htyped : List.Forall₂ (fun a ft => TypeOfElabHM ⟨[], ctors⟩ a ft) args fieldTys) :
    List.Forall₂ (OccTyped ctors root) (subOccs occ0 args.length) fieldTys := by
  have hfetch₂ : List.Forall₂ (fun o a => fetch root o = some a)
      (subOccs occ0 args.length) args :=
    mapM_forall₂_of_eq (fetch root) (fetch_subOccs root occ0 hfetch hget)
  have hboth : List.Forall₂ (fun a ft => IsValue a ∧ TypeOfElabHM ⟨[], ctors⟩ a ft)
      args fieldTys :=
    Forall₂_and_of_forall (fun (a : Expr) (ft : Ty) => TypeOfElabHM ⟨[], ctors⟩ a ft)
      IsValue htyped hvals
  exact Forall₂_relay _ _ _
    (fun o a ft hfo ⟨hval, hty⟩ => ⟨a, hfo, hval, hty⟩) hfetch₂ hboth

/-- `specializeRow c arity` reshapes a row's patterns against the field types of
    `c`: a `gctor c` row unfolds its sub-patterns (WF at the field types, which
    equal `c`'s instantiated contents by `InstantiatesBy` determinism); a
    `gbind`/`gwild` head becomes `arity` wildcards (WF at any field types of
    matching length); other `gctor c'` rows refute (dropped). -/
private theorem specializeRow_wf {ctors : CtorEnv} {c : CtorName} {arity : Nat} {occ0 : Occ}
    {T : TyName} {tyArgs : List Ty} {ctor : Ctor} {fieldTys ttys : List Ty} {r r' : Row}
    (hlook : LookupList.get? ctors c = some ctor)
    (hinst : List.Forall₂ (InstantiatesBy tyArgs) ctor.contents fieldTys)
    (hlen : fieldTys.length = arity)
    (hwf : GPatWFList ctors r.pats (.customTy T tyArgs :: ttys))
    (hs : specializeRow c arity occ0 r = some r') :
    GPatWFList ctors r'.pats (fieldTys ++ ttys) := by
  obtain ⟨captured, pats, act⟩ := r
  cases pats with
  | nil => simp [specializeRow] at hs
  | cons p prest =>
    cases p with
    | gctor c' cargs =>
      by_cases hcond : c' = c ∧ cargs.length = arity
      · simp only [specializeRow, if_pos hcond, Option.some.injEq] at hs
        subst hs
        cases hwf with
        | cons hwf_hd hwf_tl =>
          obtain ⟨hc', _⟩ := hcond
          rw [hc'] at hwf_hd
          cases hwf_hd with
          | gctor hlook' hname' hinst' hwfargs =>
            rw [hlook'] at hlook
            injection hlook with hceq
            rw [hceq] at hinst' hname'
            have hdet := InstantiatesBy_forall2_det_agree (fun _ _ => rfl) ctor.bound hinst' hinst
            rw [hdet] at hwfargs
            exact GPatWFList_append hwfargs hwf_tl
      · simp only [specializeRow, if_neg hcond] at hs
        simp at hs
    | gbind =>
      simp only [specializeRow, Option.some.injEq] at hs
      subst hs
      cases hwf with
      | cons _ hwf_tl =>
        exact GPatWFList_append (GPatWFList_replicate_gwild arity fieldTys hlen) hwf_tl
    | gwild =>
      simp only [specializeRow, Option.some.injEq] at hs
      subst hs
      cases hwf with
      | cons _ hwf_tl =>
        exact GPatWFList_append (GPatWFList_replicate_gwild arity fieldTys hlen) hwf_tl

/-- The workhorse: for a value `root`, if every current occurrence is typed at
    its column type (`OccTyped`) and the matrix is well-formed against those
    column types, then the compiled tree is `CtorSwitches`-safe. By induction on
    `compile`; a `switch` fires `hit`/`miss` per `root`'s actual ctor. -/
theorem compile_ctorSwitches_aux {ctors : CtorEnv} {root : Expr} (_hrootval : IsValue root)
    (occs : List Occ) (M : Matrix) (tys : List Ty)
    (hocctys : List.Forall₂ (OccTyped ctors root) occs tys)
    (hMwf : ∀ r ∈ M, GPatWFList ctors r.pats tys) :
    CtorSwitches root (compile occs M) := by
  revert tys hocctys hMwf
  induction occs, M using compile.induct with
  | case1 occs =>
    intro _ _ _
    simp only [compile]
    exact .fail
  | case2 r1 rest =>
    intro _ _ _
    simp only [compile]
    exact .leaf
  | case3 r1 rest occ0 orest hh ih =>
    intro tys hocctys hMwf
    rw [compile]
    split
    · cases hocctys with
      | cons hocc0 hoccRest =>
        rename_i τ0 ttys
        clear hocc0
        refine ih ttys hoccRest ?_
        intro r' hr'
        obtain ⟨r, hr, hs⟩ := List.mem_filterMap.mp hr'
        exact defaultRow_wf (hMwf r hr) hs
    · rename_i heq
      rw [hh] at heq
      exact absurd heq.symm (List.cons_ne_nil _ _)
  | case4 r1 rest occ0 orest hhd htl hh ihcases ihdflt =>
    intro tys hocctys hMwf
    cases hocctys with
    | cons hocc0 hoccRest =>
      rename_i τ0 ttys
      obtain ⟨v, hfetch, hval, hty⟩ := hocc0
      have hhdmem : hhd ∈ colHeads (r1 :: rest) := by rw [hh]; exact List.mem_cons_self
      obtain ⟨r0, hr0, cargs0, rest0, hpats0, hlen0⟩ :=
        colHeads_mem_witness (r1 :: rest) hhd.1 hhd.2 hhdmem
      have hwf0 := hMwf r0 hr0
      rw [hpats0] at hwf0
      cases hwf0 with
      | cons hwf0_hd _ =>
        obtain ⟨T0, tyArgs0, _, _, hTy0, _, _, _, _⟩ := GPatWF.gctor_inv hwf0_hd
        subst hTy0
        have hchain : IsCtorChain v := TypeOfElabHM.canonical_customTy hty hval
        obtain ⟨name, args, hget⟩ := getCtorArgs_of_isCtorChain hchain
        have hvals : ∀ a ∈ args, IsValue a := isValue_getCtorArgs hval hget
        rw [compile]
        split
        · rename_i heq
          rw [hh] at heq
          exact absurd heq (List.cons_ne_nil _ _)
        · rename_i hhd' htl' heq
          rw [hh] at heq
          injection heq with h1 h2
          subst h1
          subst h2
          let g := fun (p : CtorName × Nat) => compile (subOccs occ0 p.2 ++ orest)
            (specialize p.1 p.2 occ0 (r1 :: rest))
          rw [List.attach_map_val (l := hhd :: htl)
            (f := fun p => (p.1, p.2, g p))]
          by_cases hmem : (name, args.length) ∈ hhd :: htl
          · -- HIT: the value's ctor selects a compiled case
            have hfind := find?_casesList_mem (g := g) hmem
            obtain ⟨rN, hrN, cargsN, restN, hpatsN, hlenN⟩ :=
              colHeads_mem_witness (r1 :: rest) name args.length
                (by rw [hh]; exact hmem)
            have hwfN := hMwf rN hrN
            rw [hpatsN] at hwfN
            cases hwfN with
            | cons hwfN_hd hwfN_tl =>
              obtain ⟨TN, tyArgsN, ctorN, fieldTysN, hTyN, hlookN, hnameN, hinstN, hwfargsN⟩ :=
                GPatWF.gctor_inv hwfN_hd
              injection hTyN with hTN hTyArgsN
              subst hTN
              subst hTyArgsN
              have hinv := TypeOfElabHM.ctor_chain_inversion hchain hty
              obtain ⟨nameInv, argsInv, ctorInv, tyArgs', consumed, remaining,
                hcat, hlookInv, hbv, hcc, hforInv, hinstInv⟩ := hinv
              have hcat2 : CtorAppliedTo v name args := getCtorArgs_ctorAppliedTo hget
              obtain ⟨hnameEq, hargsEq⟩ := CtorAppliedTo.det hcat2 hcat
              subst hnameEq
              subst hargsEq
              rw [hlookInv] at hlookN
              injection hlookN with hctorEq
              rw [← hctorEq] at hinstN
              cases remaining with
              | nil =>
                simp only [Ty.wrapArrows] at hinstInv
                cases hinstInv with
                | customTy hbv2 =>
                  rw [List.append_nil] at hcc
                  rw [← hcc] at hforInv
                  have hargTyped := args_typed_fieldTys ctorInv.bound hinstN hforInv hbv2
                  have hoccSub := occTyped_subOccs hfetch hget hvals hargTyped
                  have hoccAll : List.Forall₂ (OccTyped ctors root)
                      (subOccs occ0 args.length ++ orest) (fieldTysN ++ ttys) :=
                    Forall₂_append _ hoccSub hoccRest
                  have h1 := Forall₂_length _ hforInv
                  have h2 := Forall₂_length _ hinstN
                  have hspec : ∀ r ∈ specialize name args.length occ0 (r1 :: rest),
                      GPatWFList ctors r.pats (fieldTysN ++ ttys) := by
                    intro r' hr'
                    obtain ⟨rS, hrS, hsS⟩ := List.mem_filterMap.mp hr'
                    exact specializeRow_wf hlookInv hinstN (by omega) (hMwf rS hrS) hsS
                  exact CtorSwitches.hit hfetch hget hfind
                    (ihcases ⟨(name, args.length), hmem⟩ (fieldTysN ++ ttys) hoccAll hspec)
              | cons rc rrest =>
                simp only [Ty.wrapArrows] at hinstInv
                cases hinstInv
          · -- MISS: the value's ctor selects no case, fall to default
            have hfind := find?_casesList_not_mem (g := g) hmem
            have hdefwf : ∀ r ∈ defaultMatrix occ0 (r1 :: rest),
                GPatWFList ctors r.pats ttys := by
              intro r' hr'
              obtain ⟨rD, hrD, hsD⟩ := List.mem_filterMap.mp hr'
              exact defaultRow_wf (hMwf rD hrD) hsD
            exact CtorSwitches.miss hfetch hget hfind
              (ihdflt ttys hoccRest hdefwf)

/-- **The keystone.** For a well-typed scrutinee VALUE of an ADT type, if the
    (normalised) surface patterns are well-formed against that type, the
    compiled tree is `CtorSwitches`-safe — no residual hypothesis. -/
theorem compile_ctorSwitches {ctors : CtorEnv} {root : Expr} {T : TyName} {tyArgs : List Ty}
    (hty : TypeOfElabHM ⟨[], ctors⟩ root (.customTy T tyArgs))
    (hval : IsValue root)
    (ps : List Surface.Pattern)
    (hwf : ∀ r ∈ initMatrix ps, GPatWFList ctors r.pats [.customTy T tyArgs]) :
    CtorSwitches root (compile [[]] (initMatrix ps)) := by
  refine compile_ctorSwitches_aux hval [[]] (initMatrix ps) [.customTy T tyArgs] ?_ hwf
  exact List.Forall₂.cons ⟨root, rfl, hval, hty⟩ List.Forall₂.nil

/-- **Unconditional adequacy** — the final form the bridge consumes. With the
    scrutinee typed at an ADT type and the patterns well-formed, the compiled-
    and-emitted Core term reduces to the surface-selected branch body with the
    right captures. `CtorSwitches` is discharged (`compile_ctorSwitches`) and
    closedness comes from typing (`TypeOfElabHM.closed`). -/
theorem lowerMatch_adequate_of_typed {ctors : CtorEnv} {root : Expr}
    {T : TyName} {tyArgs : List Ty}
    (hty : TypeOfElabHM ⟨[], ctors⟩ root (.customTy T tyArgs))
    (hval : IsValue root)
    (ps : List Surface.Pattern) (bodies : Nat → Expr)
    (hwf : ∀ r ∈ initMatrix ps, GPatWFList ctors r.pats [.customTy T tyArgs])
    {i : Nat} {ws : List Expr}
    (hmatch : firstMatch root ps = some (i, ws)) :
    Relation.ReflTransGen Step (lowerMatch root ps bodies) ((bodies i).substN 0 ws) :=
  lowerMatch_adequate bodies hval (TypeOfElabHM.closed hty)
    (compile_ctorSwitches hty hval ps hwf) hmatch


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

-- ── realistic demo: List patterns (cons/list sugar → Cons/Nil) ─────────
-- These exercise the .cons/.list normalization path (norm maps .cons hp tp
-- → Cons[hp, tp], .list [] → Nil) — the existing Maybe/pair tests don't.

private def vNil : Expr := .ctor (.mk "Nil")
private def vCons (h t : Expr) : Expr := .app (.app (.ctor (.mk "Cons")) h) t

-- List.head with a default:  match xs with h :: t => h | [] => 0
-- (Cons is arity-2; only h is used, t is captured but the body ignores it)
#guard match runN 32 (lowerMatch (vCons (vInt 42) vNil)
    [.cons (.name (.mk "h")) (.name (.mk "t")), .list []]
    (fun i => if i = 0 then .var 0 [] else vInt 0)) with
  | .primLit (.int 42) => true | _ => false

-- List.head on Nil falls to the [] branch:  0
#guard match runN 32 (lowerMatch vNil
    [.cons (.name (.mk "h")) (.name (.mk "t")), .list []]
    (fun i => if i = 0 then .var 0 [] else vInt 0)) with
  | .primLit (.int 0) => true | _ => false

-- List.head on a multi-element list: Cons 7 (Cons 8 Nil)  ⇒  7
-- (the tail is itself a Cons value — the compiler binds h=7, t=Cons 8 Nil)
#guard match runN 32 (lowerMatch (vCons (vInt 7) (vCons (vInt 8) vNil))
    [.cons (.name (.mk "h")) (.name (.mk "t")), .list []]
    (fun i => if i = 0 then .var 0 [] else vInt 0)) with
  | .primLit (.int 7) => true | _ => false

-- nested List-of-Maybe:  match xs with Just x :: _ => x | _ => 0
-- (cons + ctor nesting; the wildcard tail is never bound; _ catches Nil/Nothing-head)
#guard match runN 32 (lowerMatch (vCons (vJust (vInt 99)) vNil)
    [.cons pJustX .wildcard, .wildcard]
    (fun i => if i = 0 then .var 0 [] else vInt 0)) with
  | .primLit (.int 99) => true | _ => false

-- same, but the head is Nothing ⇒ the cons pattern fails (Just ≠ Nothing),
-- falls through to the catch-all wildcard:  0
#guard match runN 32 (lowerMatch (vCons vNothing vNil)
    [.cons pJustX .wildcard, .wildcard]
    (fun i => if i = 0 then .var 0 [] else vInt 0)) with
  | .primLit (.int 0) => true | _ => false

-- same, but the list is Nil ⇒ the cons pattern fails (Nil ≠ Cons), catches:  0
#guard match runN 32 (lowerMatch vNil
    [.cons pJustX .wildcard, .wildcard]
    (fun i => if i = 0 then .var 0 [] else vInt 0)) with
  | .primLit (.int 0) => true | _ => false

-- two-level List-of-List:  match xss with (x :: _) :: _ => x | _ => 0
-- (cons inside cons — arity-2 ctor at depth 2; pre-order capture gives x@var0)
#guard match runN 32 (lowerMatch (vCons (vCons (vInt 5) vNil) vNil)
    [.cons (.cons (.name (.mk "x")) .wildcard) .wildcard, .wildcard]
    (fun i => if i = 0 then .var 0 [] else vInt 0)) with
  | .primLit (.int 5) => true | _ => false

end PatComp
