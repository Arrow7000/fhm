import FHM.PatComp
import FHM.ExprClosed

/-! # H2: adequacy of `emit` against Core's `Step`

The H2 slice of the verified-pattern-compilation campaign (design memo plan
step 6), sorry-free: statements are the parent-written skeleton verbatim, the
proofs and private helpers fill it in.

The shape (memo §3-H2, validated by hand on the de Bruijn arithmetic):

At runtime, by the time control reaches a tree node, every enclosing
`matchReduce` has already substituted the fields it bound. So the *runtime
term* at a node emitted with environment `env` is
`(emit env bodies t).substN 0 envVals` where `envVals = env.mapM (fetch root)`.
The main theorem says: if `evalDTree root t = some (i, ws)`, that term
multi-steps to `(bodies i).substN 0 ws` — branch `i`'s body opened with
exactly the captures, which is verbatim what an ideal one-step match would
produce. The de Bruijn bookkeeping nets out: emit shifts body outer-refs up by
`env.length`, the `envVals` substitution brings them down by `env.length`, and
the `ws.length` leaf-lets bring them down by `ws.length` — matching
`substN 0 ws` exactly.

Within the tree only `matchReduce` and `letReduce` ever fire: inner scrutinees
are values by substitution, so `matchScrut`/`matchWildReduce` never appear.

Two side conditions, both structural:

* `OccsBound env t` — every occurrence the tree references is bound in the
  emission environment. Holds for every tree `compile` produces
  (`compile_occsBound`); this is what makes `resolveOcc`'s `idxOf` meaningful.
* `CtorSwitches root t` — every occurrence the tree switches on holds a
  ctor-chain value (when it fetches at all). Core's `matchWildReduce` only
  fires when the wildcard branch is FIRST, so an emitted switch (named cases
  first, wildcard default last) is STUCK on a non-ctor scrutinee even though
  `evalDTree` defaults; this hypothesis excludes that. It is discharged from
  scrutinee well-typedness at integration time (switches only test ADT-typed
  columns; canonical forms) — until the bridge lands it stays an explicit
  hypothesis, per the house "hypotheses on internal lemmas" rule. -/

namespace PatComp

open SmallStep (getCtorArgs IsValue IsCtorChain Step CtorAppliedTo)


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

/-- Every occurrence the tree switches on holds a ctor chain, whenever it
    fetches at all. (Conditional form: off-path occurrences that don't fetch
    for this particular value are vacuous.) Discharged from typing at
    integration time. -/
inductive CtorSwitches (root : Expr) : DTree → Prop
  | fail : CtorSwitches root .fail
  | leaf {act binds} : CtorSwitches root (.leaf act binds)
  | switch {occ cases dflt} :
      (∀ v, fetch root occ = some v → IsCtorChain v) →
      (∀ c a t', (c, a, t') ∈ cases → CtorSwitches root t') →
      CtorSwitches root dflt →
      CtorSwitches root (.switch occ cases dflt)


/-! ## `mapM (fetch root)` plumbing -/

/-- Inversion of a successful `mapM` on a cons (re-derivation of PatComp's
    private `mapM_cons_some`). -/
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
    | switch hcocc hccases hcdflt =>
    -- the switched occurrence's value: a ctor chain
    have hlt : env.idxOf occ < envVals.length := by
      rw [mapM_length henv]; exact List.idxOf_lt_length_of_mem hoccmem
    obtain ⟨v0, hv0⟩ : ∃ v, fetch root occ = some v :=
      ⟨envVals[env.idxOf occ], (mapM_idxOf henv hoccmem).symm.trans
        (List.getElem?_eq_getElem hlt)⟩
    have hchain : IsCtorChain v0 := hcocc v0 hv0
    obtain ⟨name, args, hget⟩ := getCtorArgs_of_isCtorChain hchain
    simp only [evalDTree, hv0, hget] at heval
    rw [evalSwitch_eq_find' root name args.length cases dflt] at heval
    -- the substituted emitted term: a match on the fetched value
    have hemit :
        (emit env bodies (.switch occ cases dflt)).substN 0 envVals
          = .match_ v0
              (cases.map (fun x => (MatchPattern.named x.1 x.2.1,
                  (emit (subOccs occ x.2.1 ++ env) bodies x.2.2).substN x.2.1 envVals))
                ++ [(.wildcard, (emit env bodies dflt).substN 0 envVals)]) := by
      show (Expr.match_ (resolveOcc env occ)
          (emitCases env bodies occ cases
            ++ [(.wildcard, emit env bodies dflt)])).substN 0 envVals = _
      rw [Expr.substN_match, resolveOcc, substN_var_resolve0 henv hroot hoccmem hv0,
        List.map_append, emitCases_eq_map, List.map_map]
      congr 1
      congr 1
      apply List.map_congr_left
      intro x hx
      simp only [Function.comp_apply, MatchPattern.bindCount, Nat.zero_add]
    cases hfind : cases.find? (fun y => decide (y.1 = name ∧ y.2.1 = args.length)) with
    | some x =>
      -- FOUND: matchReduce into the case's subtree
      rw [hfind] at heval
      obtain ⟨c, a, t'⟩ := x
      obtain ⟨rfl, rfl⟩ : c = name ∧ a = args.length := by
        simpa using List.find?_some hfind
      -- NB: the substs above may rename `name`/`args.length` to `c`/`a` in
      -- context; everything below is phrased via `c` to be direction-proof
      have hmem : (c, args.length, t') ∈ cases := List.mem_of_find?_eq_some hfind
      have hFMB := firstMatchingBranch_found
        (fun x => (emit (subOccs occ x.2.1 ++ env) bodies x.2.2).substN x.2.1 envVals)
        [(.wildcard, (emit env bodies dflt).substN 0 envVals)]
        cases (c, args.length, t') hfind
      have hstep : Step ((emit env bodies (.switch occ cases dflt)).substN 0 envVals)
          (((emit (subOccs occ args.length ++ env) bodies t').substN
              args.length envVals).substN 0
            (args.take (MatchPattern.named c args.length).bindCount)) := by
        rw [hemit]
        exact Step.matchReduce (fetch_isValue hval hv0)
          (getCtorArgs_ctorAppliedTo hget) hFMB
      rw [show (MatchPattern.named c args.length).bindCount = args.length from rfl,
        List.take_length] at hstep
      have hcomp := Expr.substN_substN_append
        (emit (subOccs occ args.length ++ env) bodies t') 0 args envVals
        (mapM_fetch_closed hroot henv)
      rw [Nat.zero_add] at hcomp
      rw [hcomp] at hstep
      refine Relation.ReflTransGen.head hstep ?_
      have henv' : (subOccs occ args.length ++ env).mapM (fetch root)
          = some (args ++ envVals) := by
        rw [List.mapM_append, fetch_subOccs' root occ hv0 hget, henv]
        rfl
      exact ihcases c args.length t' hmem (subOccs occ args.length ++ env)
        (args ++ envVals) henv' (hbcases c args.length t' hmem)
        (hccases c args.length t' hmem) heval
    | none =>
      -- NOT FOUND: matchReduce into the trailing wildcard (the default tree)
      rw [hfind] at heval
      have hall : ∀ x ∈ cases, ¬(x.1 = name ∧ x.2.1 = args.length) := by
        intro x hx
        simpa using List.find?_eq_none.mp hfind x hx
      have hFMB := firstMatchingBranch_default
        (fun x => (emit (subOccs occ x.2.1 ++ env) bodies x.2.2).substN x.2.1 envVals)
        ((emit env bodies dflt).substN 0 envVals) cases hall
      have hstep : Step ((emit env bodies (.switch occ cases dflt)).substN 0 envVals)
          (((emit env bodies dflt).substN 0 envVals).substN 0
            (args.take MatchPattern.wildcard.bindCount)) := by
        rw [hemit]
        exact Step.matchReduce (fetch_isValue hval hv0)
          (getCtorArgs_ctorAppliedTo hget) hFMB
      rw [show MatchPattern.wildcard.bindCount = 0 from rfl, List.take_zero,
        Expr.substN_nil] at hstep
      exact Relation.ReflTransGen.head hstep
        (ihdflt env envVals henv hbdflt hcdflt heval)


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

end PatComp
