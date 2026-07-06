import FHM.Core

/-! # Term-level closedness for Core expressions

Core has `Ty.isClosed` for types but NO term-level free-variable machinery.
The verified pattern-compilation campaign (see
`briefs/design-memo-verified-pattern-compilation.md`, prerequisite for its H2
adequacy proof) needs exactly this: captured scrutinee sub-values are closed,
so Core's `substN`/`shiftFrom` leave them untouched as they are pushed through
the emitted nested matches.

`Expr.varsBelow n e` = every free term-level de Bruijn var of `e` is `< n`;
`e.varsBelow 0` = closed. Type-level variables (`tyArgs`, annotations) are
irrelevant to it throughout.

This is a LEAF module: it imports Core and adds nothing to Core's metatheory.
The lemma layer (monotonicity; `shiftFrom`/`substN` act as identity on closed
terms; values of closed programs stay closed under `Step`) is filled in by the
campaign as needed — see the design memo's plan step 4.
-/

mutual

/-- Every free term-var of `e` is `< n`. Binders raise the bound: `lambda`/
    `letIn` bodies by 1, a match branch body by its pattern's `bindCount`, a
    `letRec` group's bindings and body by the group size (mirroring
    `Expr.shiftFrom`/`Expr.substN`'s threshold bookkeeping). -/
def Expr.varsBelow (n : Nat) : Expr → Bool
  | .var i _ => decide (i < n)
  | .primLit _ => true
  | .primBinOp _ => true
  | .ctor _ => true
  | .lambda _ body => Expr.varsBelow (n + 1) body
  | .app f arg => Expr.varsBelow n f && Expr.varsBelow n arg
  | .letIn _ rhs body => Expr.varsBelow n rhs && Expr.varsBelow (n + 1) body
  | .match_ scrut branches =>
      Expr.varsBelow n scrut && BranchListClosed.varsBelow n branches
  | .letRec _ bindings body =>
      RecGroupClosed.varsBelow (n + bindings.length) bindings
        && Expr.varsBelow (n + bindings.length) body

def BranchListClosed.varsBelow (n : Nat) : List (MatchPattern × Expr) → Bool
  | [] => true
  | (pat, body) :: rest =>
      Expr.varsBelow (n + pat.bindCount) body
        && BranchListClosed.varsBelow n rest

def RecGroupClosed.varsBelow (n : Nat) : List Expr → Bool
  | [] => true
  | e :: rest => Expr.varsBelow n e && RecGroupClosed.varsBelow n rest

end

/-! ## Monotonicity

Raising the bound preserves `varsBelow`: if every free var is `< m` and `m ≤ n`,
then every free var is `< n`. Proved by structural induction on the expression
(via `Expr.rec_strong`), with the branch-list / rec-group companions handling the
embedded lists. -/

/-- Monotonicity of `Expr.varsBelow` in the bound. -/
theorem Expr.varsBelow_mono (e : Expr) :
    ∀ {m n : Nat}, m ≤ n → Expr.varsBelow m e = true → Expr.varsBelow n e = true := by
  induction e using Expr.rec_strong with
  | primLit p => intro m n _ _; rfl
  | primBinOp op => intro m n _ _; rfl
  | ctor nm => intro m n _ _; rfl
  | var i tyArgs =>
    intro m n hmn h
    simp only [Expr.varsBelow, decide_eq_true_eq] at h ⊢
    omega
  | lambda ann body ih =>
    intro m n hmn h
    simp only [Expr.varsBelow] at h ⊢
    exact ih (by omega) h
  | app f arg ihf iharg =>
    intro m n hmn h
    simp only [Expr.varsBelow, Bool.and_eq_true] at h ⊢
    exact ⟨ihf hmn h.1, iharg hmn h.2⟩
  | letIn ann rhs body ihrhs ihbody =>
    intro m n hmn h
    simp only [Expr.varsBelow, Bool.and_eq_true] at h ⊢
    exact ⟨ihrhs hmn h.1, ihbody (by omega : m + 1 ≤ n + 1) h.2⟩
  | match_ scrut branches ihscrut ihbrs =>
    intro m n hmn h
    simp only [Expr.varsBelow, Bool.and_eq_true] at h ⊢
    obtain ⟨h1, h2⟩ := h
    refine ⟨ihscrut hmn h1, ?_⟩
    have key : ∀ (brs : List (MatchPattern × Expr)),
        (∀ pat e, (pat, e) ∈ brs →
          ∀ a b, a ≤ b → Expr.varsBelow a e = true → Expr.varsBelow b e = true) →
        BranchListClosed.varsBelow m brs = true → BranchListClosed.varsBelow n brs = true := by
      intro brs
      induction brs with
      | nil => intro _ _; rfl
      | cons hd tl ih =>
        obtain ⟨pat, body⟩ := hd
        intro hmono hh
        simp only [BranchListClosed.varsBelow, Bool.and_eq_true] at hh ⊢
        refine ⟨hmono pat body List.mem_cons_self _ _ (by omega) hh.1, ?_⟩
        exact ih (fun p e hmem => hmono p e (List.mem_cons_of_mem _ hmem)) hh.2
    exact key branches ihbrs h2
  | letRec anns bindings body ihbindings ihbody =>
    intro m n hmn h
    simp only [Expr.varsBelow, Bool.and_eq_true] at h ⊢
    obtain ⟨h1, h2⟩ := h
    refine ⟨?_, ihbody (by omega : m + bindings.length ≤ n + bindings.length) h2⟩
    have key : ∀ (bs : List Expr),
        (∀ e ∈ bs, ∀ a b, a ≤ b → Expr.varsBelow a e = true → Expr.varsBelow b e = true) →
        RecGroupClosed.varsBelow (m + bindings.length) bs = true →
        RecGroupClosed.varsBelow (n + bindings.length) bs = true := by
      intro bs
      induction bs with
      | nil => intro _ _; rfl
      | cons hd tl ih =>
        intro hmono hh
        simp only [RecGroupClosed.varsBelow, Bool.and_eq_true] at hh ⊢
        refine ⟨hmono hd List.mem_cons_self _ _ (by omega) hh.1, ?_⟩
        exact ih (fun e hmem => hmono e (List.mem_cons_of_mem _ hmem)) hh.2
    exact key bindings ihbindings h1

/-- Branch-list companion of `Expr.varsBelow_mono`. -/
theorem BranchListClosed.varsBelow_mono {m n : Nat} (hmn : m ≤ n) :
    ∀ (branches : List (MatchPattern × Expr)),
      BranchListClosed.varsBelow m branches = true → BranchListClosed.varsBelow n branches = true := by
  intro branches
  induction branches with
  | nil => intro _; rfl
  | cons hd tl ih =>
    obtain ⟨pat, body⟩ := hd
    intro h
    simp only [BranchListClosed.varsBelow, Bool.and_eq_true] at h ⊢
    exact ⟨Expr.varsBelow_mono body (by omega : m + pat.bindCount ≤ n + pat.bindCount) h.1, ih h.2⟩

/-- Rec-group companion of `Expr.varsBelow_mono`. -/
theorem RecGroupClosed.varsBelow_mono {m n : Nat} (hmn : m ≤ n) :
    ∀ (bindings : List Expr),
      RecGroupClosed.varsBelow m bindings = true → RecGroupClosed.varsBelow n bindings = true := by
  intro bindings
  induction bindings with
  | nil => intro _; rfl
  | cons hd tl ih =>
    intro h
    simp only [RecGroupClosed.varsBelow, Bool.and_eq_true] at h ⊢
    exact ⟨Expr.varsBelow_mono hd hmn h.1, ih h.2⟩

/-! ## `shiftFrom` is the identity on terms with all vars below the shift threshold

`Expr.shiftFrom`'s branch-list / rec-group companions are `private` in Core, so we
cannot name them. We instead work through the `match_`/`letRec` nodes themselves:
tiny structural projections (`matchBranchesOf`, `letRecBindingsOf`, `letRecBodyOf`)
let us state the branch/binding equalities that Core's private helpers produce, and
these reduce definitionally against `Expr.shiftFrom`/`Expr.substN`. -/

/-- Project the branch list of a `match_` (else `[]`). -/
def Expr.matchBranchesOf : Expr → List (MatchPattern × Expr)
  | .match_ _ brs => brs
  | _ => []

/-- Project the binding list of a `letRec` (else `[]`). -/
def Expr.letRecBindingsOf : Expr → List Expr
  | .letRec _ bs _ => bs
  | _ => []

/-- Rewrite the whole map to the list when it is pointwise the identity. -/
private theorem List.map_self_of_mem {α : Type _} {f : α → α} :
    ∀ {l : List α}, (∀ a ∈ l, f a = a) → l.map f = l := by
  intro l
  induction l with
  | nil => intro _; rfl
  | cons a t ih =>
    intro h
    simp only [List.map_cons]
    rw [h a List.mem_cons_self, ih (fun x hx => h x (List.mem_cons_of_mem _ hx))]

/-- Each branch body of a closed branch list is closed under its raised bound. -/
theorem BranchListClosed.varsBelow_of_mem {n : Nat} :
    ∀ {brs : List (MatchPattern × Expr)}, BranchListClosed.varsBelow n brs = true →
      ∀ pat body, (pat, body) ∈ brs → Expr.varsBelow (n + pat.bindCount) body = true := by
  intro brs
  induction brs with
  | nil => intro _ pat body hmem; exact absurd hmem (List.not_mem_nil)
  | cons hd tl ih =>
    obtain ⟨p, b⟩ := hd
    intro h pat body hmem
    simp only [BranchListClosed.varsBelow, Bool.and_eq_true] at h
    rcases List.mem_cons.mp hmem with heq | hmem'
    · obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ heq
      exact h.1
    · exact ih h.2 pat body hmem'

/-- Each binding of a closed rec-group is closed under the shared bound. -/
theorem RecGroupClosed.varsBelow_of_mem {n : Nat} :
    ∀ {bs : List Expr}, RecGroupClosed.varsBelow n bs = true →
      ∀ e ∈ bs, Expr.varsBelow n e = true := by
  intro bs
  induction bs with
  | nil => intro _ e hmem; exact absurd hmem (List.not_mem_nil)
  | cons hd tl ih =>
    intro h e hmem
    simp only [RecGroupClosed.varsBelow, Bool.and_eq_true] at h
    rcases List.mem_cons.mp hmem with rfl | hmem'
    · exact h.1
    · exact ih h.2 e hmem'

/-- One `Expr.shiftFrom` step over a `match_` branch list, exposed through
    projections (Core's `BranchList.shiftFrom` reduces to exactly this). -/
private theorem Expr.shiftFrom_match_cons (scrut : Expr) (pat : MatchPattern)
    (body : Expr) (rest : List (MatchPattern × Expr)) (t n : Nat) :
    ((Expr.match_ scrut ((pat, body) :: rest)).shiftFrom t n).matchBranchesOf
      = (pat, body.shiftFrom (t + pat.bindCount) n)
        :: ((Expr.match_ scrut rest).shiftFrom t n).matchBranchesOf := rfl

/-- The shifted branch list of a `match_` equals the pointwise shift of the
    branches (the public face of Core's private `BranchList.shiftFrom`). -/
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

/-- One `Expr.shiftFrom` step over a `letRec` binding list, head split off with
    the tail kept at the *same* threshold. -/
private theorem Expr.shiftFrom_letRec_headtail (anns : List (Option PolyTy)) (e : Expr)
    (rest : List Expr) (body : Expr) (t n : Nat) :
    ((Expr.letRec anns (e :: rest) body).shiftFrom t n).letRecBindingsOf
      = e.shiftFrom (t + (e :: rest).length) n
        :: ((Expr.letRec anns (e :: rest) body).shiftFrom t n).letRecBindingsOf.tail := rfl

/-- Peeling the head binding shifts the recursion base by one; the tail of the
    shifted `(e :: rest)` binding list is the shifted `rest` list (at the base
    incremented past `e`'s binder). -/
private theorem Expr.shiftFrom_letRec_bridge (anns : List (Option PolyTy)) (e : Expr)
    (rest : List Expr) (body : Expr) (base n : Nat) :
    ((Expr.letRec anns (e :: rest) body).shiftFrom base n).letRecBindingsOf.tail
      = ((Expr.letRec anns rest body).shiftFrom (base + 1) n).letRecBindingsOf := by
  simp only [Expr.shiftFrom, Expr.letRecBindingsOf, List.length_cons]
  rw [show base + (rest.length + 1) = base + 1 + rest.length from by omega]
  rfl

/-- The shifted binding list of a `letRec` equals the pointwise shift of the
    bindings (the public face of Core's private `RecGroup.shiftFrom`). -/
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

/-- Definitional unfolding of `Expr.shiftFrom` on a `match_`, with the branch list
    named through `matchBranchesOf`. -/
private theorem Expr.shiftFrom_match_eq (scrut : Expr) (brs : List (MatchPattern × Expr))
    (t n : Nat) :
    (Expr.match_ scrut brs).shiftFrom t n
      = Expr.match_ (scrut.shiftFrom t n) ((Expr.match_ scrut brs).shiftFrom t n).matchBranchesOf :=
  rfl

/-- Definitional unfolding of `Expr.shiftFrom` on a `letRec`, with the binding list
    named through `letRecBindingsOf`. -/
private theorem Expr.shiftFrom_letRec_eq (anns : List (Option PolyTy)) (bs : List Expr)
    (body : Expr) (t n : Nat) :
    (Expr.letRec anns bs body).shiftFrom t n
      = Expr.letRec anns ((Expr.letRec anns bs body).shiftFrom t n).letRecBindingsOf
          (body.shiftFrom (t + bs.length) n) :=
  rfl

/-- `shiftFrom` is the identity on an expression all of whose free term-vars are
    below the shift threshold `t`. -/
theorem Expr.shiftFrom_of_varsBelow (n : Nat) :
    ∀ (e : Expr) (t : Nat), Expr.varsBelow t e = true → e.shiftFrom t n = e := by
  intro e
  induction e using Expr.rec_strong with
  | primLit p => intro t _; rfl
  | primBinOp op => intro t _; rfl
  | ctor nm => intro t _; rfl
  | var i tyArgs =>
    intro t h
    simp only [Expr.varsBelow, decide_eq_true_eq] at h
    simp only [Expr.shiftFrom, if_pos h]
  | lambda ann body ih =>
    intro t h
    simp only [Expr.varsBelow] at h
    simp only [Expr.shiftFrom, ih (t + 1) h]
  | app f arg ihf iharg =>
    intro t h
    simp only [Expr.varsBelow, Bool.and_eq_true] at h
    simp only [Expr.shiftFrom, ihf t h.1, iharg t h.2]
  | letIn ann rhs body ihrhs ihbody =>
    intro t h
    simp only [Expr.varsBelow, Bool.and_eq_true] at h
    simp only [Expr.shiftFrom, ihrhs t h.1, ihbody (t + 1) h.2]
  | match_ scrut branches ihscrut ihbrs =>
    intro t h
    simp only [Expr.varsBelow, Bool.and_eq_true] at h
    obtain ⟨hs, hbrs⟩ := h
    rw [Expr.shiftFrom_match_eq, Expr.shiftFrom_matchBranches, ihscrut t hs]
    congr 1
    apply List.map_self_of_mem
    intro pb hmem
    obtain ⟨pat, body⟩ := pb
    have := ihbrs pat body hmem (t + pat.bindCount)
      (BranchListClosed.varsBelow_of_mem hbrs pat body hmem)
    simp only [this]
  | letRec anns bindings body ihbindings ihbody =>
    intro t h
    simp only [Expr.varsBelow, Bool.and_eq_true] at h
    obtain ⟨hbd, hbody⟩ := h
    rw [Expr.shiftFrom_letRec_eq, Expr.shiftFrom_letRecBindings,
      ihbody (t + bindings.length) hbody]
    congr 1
    apply List.map_self_of_mem
    intro e hmem
    exact ihbindings e hmem (t + bindings.length)
      (RecGroupClosed.varsBelow_of_mem hbd e hmem)

/-- `shiftFrom` is the identity on closed terms, at any threshold. -/
theorem Expr.shiftFrom_of_closed {e : Expr} (h : Expr.varsBelow 0 e = true) (t n : Nat) :
    e.shiftFrom t n = e :=
  Expr.shiftFrom_of_varsBelow n e t (Expr.varsBelow_mono e (Nat.zero_le t) h)

/-! ## `substN` is the identity on terms with all vars below the substitution depth

Same structure as the `shiftFrom` layer: Core's `BranchList.substN`/`RecGroup.substN`
are `private`, so we route through the `match_`/`letRec` node projections. -/

/-- One `Expr.substN` step over a `match_` branch list, exposed through projections. -/
private theorem Expr.substN_match_cons (scrut : Expr) (pat : MatchPattern)
    (body : Expr) (rest : List (MatchPattern × Expr)) (k : Nat) (vs : List Expr) :
    ((Expr.match_ scrut ((pat, body) :: rest)).substN k vs).matchBranchesOf
      = (pat, body.substN (k + pat.bindCount) vs)
        :: ((Expr.match_ scrut rest).substN k vs).matchBranchesOf := rfl

/-- The substituted branch list of a `match_` equals the pointwise substitution of
    the branches (the public face of Core's private `BranchList.substN`). -/
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

/-- One `Expr.substN` step over a `letRec` binding list, head split off with the
    tail kept at the same depth. -/
private theorem Expr.substN_letRec_headtail (anns : List (Option PolyTy)) (e : Expr)
    (rest : List Expr) (body : Expr) (k : Nat) (vs : List Expr) :
    ((Expr.letRec anns (e :: rest) body).substN k vs).letRecBindingsOf
      = e.substN (k + (e :: rest).length) vs
        :: ((Expr.letRec anns (e :: rest) body).substN k vs).letRecBindingsOf.tail := rfl

/-- Peeling the head binding bumps the recursion base by one. -/
private theorem Expr.substN_letRec_bridge (anns : List (Option PolyTy)) (e : Expr)
    (rest : List Expr) (body : Expr) (base : Nat) (vs : List Expr) :
    ((Expr.letRec anns (e :: rest) body).substN base vs).letRecBindingsOf.tail
      = ((Expr.letRec anns rest body).substN (base + 1) vs).letRecBindingsOf := by
  simp only [Expr.substN, Expr.letRecBindingsOf, List.length_cons]
  rw [show base + (rest.length + 1) = base + 1 + rest.length from by omega]
  rfl

/-- The substituted binding list of a `letRec` equals the pointwise substitution of
    the bindings (the public face of Core's private `RecGroup.substN`). -/
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

/-- Definitional unfolding of `Expr.substN` on a `match_`. -/
private theorem Expr.substN_match_eq (scrut : Expr) (brs : List (MatchPattern × Expr))
    (k : Nat) (vs : List Expr) :
    (Expr.match_ scrut brs).substN k vs
      = Expr.match_ (scrut.substN k vs) ((Expr.match_ scrut brs).substN k vs).matchBranchesOf :=
  rfl

/-- Definitional unfolding of `Expr.substN` on a `letRec`. -/
private theorem Expr.substN_letRec_eq (anns : List (Option PolyTy)) (bs : List Expr)
    (body : Expr) (k : Nat) (vs : List Expr) :
    (Expr.letRec anns bs body).substN k vs
      = Expr.letRec anns ((Expr.letRec anns bs body).substN k vs).letRecBindingsOf
          (body.substN (k + bs.length) vs) :=
  rfl

/-- `substN` is the identity on an expression all of whose free term-vars are below
    the substitution depth `k`: there is nothing in range to replace. -/
theorem Expr.substN_of_varsBelow (vs : List Expr) :
    ∀ (e : Expr) (k : Nat), Expr.varsBelow k e = true → e.substN k vs = e := by
  intro e
  induction e using Expr.rec_strong with
  | primLit p => intro k _; rfl
  | primBinOp op => intro k _; rfl
  | ctor nm => intro k _; rfl
  | var i tyArgs =>
    intro k h
    simp only [Expr.varsBelow, decide_eq_true_eq] at h
    simp only [Expr.substN, if_pos h]
  | lambda ann body ih =>
    intro k h
    simp only [Expr.varsBelow] at h
    simp only [Expr.substN, ih (k + 1) h]
  | app f arg ihf iharg =>
    intro k h
    simp only [Expr.varsBelow, Bool.and_eq_true] at h
    simp only [Expr.substN, ihf k h.1, iharg k h.2]
  | letIn ann rhs body ihrhs ihbody =>
    intro k h
    simp only [Expr.varsBelow, Bool.and_eq_true] at h
    simp only [Expr.substN, ihrhs k h.1, ihbody (k + 1) h.2]
  | match_ scrut branches ihscrut ihbrs =>
    intro k h
    simp only [Expr.varsBelow, Bool.and_eq_true] at h
    obtain ⟨hs, hbrs⟩ := h
    rw [Expr.substN_match_eq, Expr.substN_matchBranches, ihscrut k hs]
    congr 1
    apply List.map_self_of_mem
    intro pb hmem
    obtain ⟨pat, body⟩ := pb
    have := ihbrs pat body hmem (k + pat.bindCount)
      (BranchListClosed.varsBelow_of_mem hbrs pat body hmem)
    simp only [this]
  | letRec anns bindings body ihbindings ihbody =>
    intro k h
    simp only [Expr.varsBelow, Bool.and_eq_true] at h
    obtain ⟨hbd, hbody⟩ := h
    rw [Expr.substN_letRec_eq, Expr.substN_letRecBindings,
      ihbody (k + bindings.length) hbody]
    congr 1
    apply List.map_self_of_mem
    intro e hmem
    exact ihbindings e hmem (k + bindings.length)
      (RecGroupClosed.varsBelow_of_mem hbd e hmem)

/-- `substN` is the identity on closed terms, at any depth. -/
theorem Expr.substN_of_closed {e : Expr} (h : Expr.varsBelow 0 e = true) (k : Nat)
    (vs : List Expr) : e.substN k vs = e :=
  Expr.substN_of_varsBelow vs e k (Expr.varsBelow_mono e (Nat.zero_le k) h)

/-! ## `varsBelow` ignores type-variable opening

`Expr.openTyVarsAux` (hence `openTyVars`/`openBoundTyVars`) only rewrites type
annotations and `var` `tyArgs`; it never touches a term-var's de Bruijn index or
the binder skeleton, so it leaves `varsBelow` unchanged. This is what lets the
typing lemma reflect the cofinite premises (which type the *opened* bound
expressions) back to the stored terms. -/

/-- `openTyVarsAux` preserves `varsBelow` at every term-bound `n` and type-depth `d`. -/
theorem Expr.varsBelow_openTyVarsAux (Xs : List Nat) :
    ∀ (e : Expr) (n d : Nat),
      Expr.varsBelow n (e.openTyVarsAux d Xs) = Expr.varsBelow n e := by
  intro e
  induction e using Expr.rec_strong with
  | primLit p => intro n d; rfl
  | primBinOp op => intro n d; rfl
  | ctor nm => intro n d; rfl
  | var i tyArgs => intro n d; rfl
  | lambda ann body ih =>
    intro n d
    simp only [Expr.openTyVarsAux, Expr.varsBelow, ih]
  | app f arg ihf iharg =>
    intro n d
    simp only [Expr.openTyVarsAux, Expr.varsBelow, ihf, iharg]
  | letIn ann rhs body ihrhs ihbody =>
    intro n d
    cases ann with
    | none => simp only [Expr.openTyVarsAux, Expr.varsBelow, ihrhs, ihbody]
    | some σ => simp only [Expr.openTyVarsAux, Expr.varsBelow, ihrhs, ihbody]
  | match_ scrut branches ihscrut ihbrs =>
    intro n d
    simp only [Expr.openTyVarsAux, Expr.varsBelow, ihscrut]
    congr 1
    have key : ∀ (brs : List (MatchPattern × Expr)),
        (∀ pat body, (pat, body) ∈ brs →
          ∀ n' d', Expr.varsBelow n' (body.openTyVarsAux d' Xs) = Expr.varsBelow n' body) →
        BranchListClosed.varsBelow n (BranchList.openTyVarsAux d Xs brs)
          = BranchListClosed.varsBelow n brs := by
      intro brs
      induction brs with
      | nil => intro _; rfl
      | cons hd tl ih =>
        obtain ⟨pat, body⟩ := hd
        intro hb
        simp only [BranchList.openTyVarsAux, BranchListClosed.varsBelow,
          hb pat body List.mem_cons_self (n + pat.bindCount) d]
        rw [ih (fun p b hm => hb p b (List.mem_cons_of_mem _ hm))]
    exact key branches ihbrs
  | letRec anns bindings body ihbindings ihbody =>
    intro n d
    simp only [Expr.openTyVarsAux, Expr.varsBelow, ihbody]
    have hlen : (RecGroup.openTyVarsAux d Xs anns bindings).length = bindings.length := by
      clear ihbindings ihbody
      induction bindings generalizing anns with
      | nil => rfl
      | cons e rest ih =>
        cases anns with
        | nil => simp only [RecGroup.openTyVarsAux, List.length_cons, ih]
        | cons a as => simp only [RecGroup.openTyVarsAux, List.length_cons, ih]
    rw [hlen]
    congr 1
    have key : ∀ (bs : List Expr) (as : List (Option PolyTy)),
        (∀ e ∈ bs, ∀ n' d', Expr.varsBelow n' (e.openTyVarsAux d' Xs) = Expr.varsBelow n' e) →
        RecGroupClosed.varsBelow (n + bindings.length) (RecGroup.openTyVarsAux d Xs as bs)
          = RecGroupClosed.varsBelow (n + bindings.length) bs := by
      intro bs
      induction bs with
      | nil => intro as _; rfl
      | cons e rest ih =>
        intro as hb
        cases as with
        | nil =>
          simp only [RecGroup.openTyVarsAux, RecGroupClosed.varsBelow,
            hb e List.mem_cons_self (n + bindings.length) d]
          rw [ih [] (fun x hx => hb x (List.mem_cons_of_mem _ hx))]
        | cons a as' =>
          simp only [RecGroup.openTyVarsAux, RecGroupClosed.varsBelow,
            hb e List.mem_cons_self (n + bindings.length) (d + RecAnn.params a)]
          rw [ih as' (fun x hx => hb x (List.mem_cons_of_mem _ hx))]
    exact key bindings anns ihbindings

/-- `varsBelow` is invariant under scoped type-variable opening. -/
theorem Expr.varsBelow_openTyVars (Xs : List Nat) (e : Expr) (n : Nat) :
    Expr.varsBelow n (e.openTyVars Xs) = Expr.varsBelow n e :=
  Expr.varsBelow_openTyVarsAux Xs e n 0

/-- `varsBelow` is invariant under `let`-bound type-variable opening. -/
theorem Expr.varsBelow_openBoundTyVars (ann : Option PolyTy) (Xs : List Nat) (e : Expr) (n : Nat) :
    Expr.varsBelow n (Expr.openBoundTyVars ann Xs e) = Expr.varsBelow n e := by
  cases ann with
  | none => rfl
  | some σ => exact Expr.varsBelow_openTyVars Xs e n

/-! ## Well-typed terms have every free var below the context length

The declarative typing relation `TypeOfElabHM` maintains the invariant that a
well-typed expression is `varsBelow ctx.env.length`: the `var` rule forces an
in-range context lookup, and every binder rule extends the env by exactly the
amount `varsBelow`'s bookkeeping expects (`lambda`/`letIn` +1, a match branch by
its `bindCount`, a `letRec` group by its length). Type-level machinery (scheme
instantiation, scoped-var openings in the cofinite premises) is irrelevant — only
the term-var context lookups matter, and the openings are absorbed by
`Expr.varsBelow_openTyVars`. -/

/-- Assemble a closed branch list from per-branch closedness. -/
theorem RecGroupClosed.varsBelow_of_forall {n : Nat} :
    ∀ {bs : List Expr}, (∀ e ∈ bs, Expr.varsBelow n e = true) →
      RecGroupClosed.varsBelow n bs = true := by
  intro bs
  induction bs with
  | nil => intro _; rfl
  | cons e rest ih =>
    intro h
    simp only [RecGroupClosed.varsBelow, Bool.and_eq_true]
    exact ⟨h e List.mem_cons_self, ih (fun x hx => h x (List.mem_cons_of_mem _ hx))⟩

/-- Every left element of a length-matched pair of lists occurs in their zip. -/
private theorem mem_zip_of_mem_left {α β : Type _} :
    ∀ {l : List α} {r : List β}, l.length = r.length → ∀ {a : α}, a ∈ l →
      ∃ b, (a, b) ∈ l.zip r := by
  intro l
  induction l with
  | nil => intro r _ a ha; exact absurd ha (List.not_mem_nil)
  | cons x xs ih =>
    intro r hlen a ha
    cases r with
    | nil => simp only [List.length_cons, List.length_nil] at hlen; exact absurd hlen (by omega)
    | cons y ys =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
      rcases List.mem_cons.mp ha with rfl | ha'
      · exact ⟨y, by rw [List.zip_cons_cons]; exact List.mem_cons_self⟩
      · obtain ⟨b, hb⟩ := ih hlen ha'
        exact ⟨b, by rw [List.zip_cons_cons]; exact List.mem_cons_of_mem _ hb⟩

/-- The `match_` per-branch motive of `TypeOfElabHM.varsBelow`: each branch body is
    closed under the context extended by the pattern's `bindCount`. -/
private theorem branchMotive_varsBelow {ctx : Ctx} {pat : MatchPattern} {body : Expr}
    {scrutTy resultTy : Ty}
    (h : TypeOfElabHM.BranchMotive (fun c e _ _ => Expr.varsBelow c.env.length e = true)
          ctx (pat, body) scrutTy resultTy) :
    Expr.varsBelow (ctx.env.length + pat.bindCount) body = true := by
  rcases h with ⟨ctor, c, m, tyArgs, instContents, hpat, hspec, _, ihb⟩ | ⟨hpat, _, ihb⟩
  · simp only at hpat
    subst hpat
    have hlen : instContents.length = m := by
      have hfe := hspec.fields.length_eq
      rw [hspec.bind_count]; omega
    simp only [MatchPattern.bindCount]
    simp only [List.length_append, List.length_map] at ihb
    rw [hlen] at ihb
    rwa [Nat.add_comm] at ihb
  · simp only at hpat
    subst hpat
    simpa only [MatchPattern.bindCount, Nat.add_zero] using ihb

/-- Assemble a closed branch list from the per-branch motives. -/
private theorem branchList_varsBelow_of_motive {ctx : Ctx} {scrutTy resultTy : Ty} :
    ∀ (brs : List (MatchPattern × Expr)),
      (∀ branch ∈ brs, TypeOfElabHM.BranchMotive
        (fun c e _ _ => Expr.varsBelow c.env.length e = true) ctx branch scrutTy resultTy) →
      BranchListClosed.varsBelow ctx.env.length brs = true := by
  intro brs
  induction brs with
  | nil => intro _; rfl
  | cons hd tl ih =>
    obtain ⟨pat, body⟩ := hd
    intro hbrs
    simp only [BranchListClosed.varsBelow, Bool.and_eq_true]
    exact ⟨branchMotive_varsBelow (hbrs (pat, body) List.mem_cons_self),
      ih (fun br hbr => hbrs br (List.mem_cons_of_mem _ hbr))⟩

/-- **Well-typed ⇒ all free term-vars below the context length.** By induction on
    the (elaborated declarative) typing derivation. -/
theorem TypeOfElabHM.varsBelow {ctx : Ctx} {e : Expr} {τ : Ty}
    (h : TypeOfElabHM ctx e τ) : Expr.varsBelow ctx.env.length e = true := by
  induction h using TypeOfElabHM.rec_strong with
  | primLitUnit => rfl
  | primLitInt => rfl
  | primLitNat => rfl
  | primLitChar => rfl
  | primBinOpIntAdd => rfl
  | primBinOpIntSub => rfl
  | primBinOpIntLt _ _ _ _ => rfl
  | primBinOpCharLt _ _ _ _ => rfl
  | ctor _ _ _ => rfl
  | var hlook _ _ =>
    simp only [Expr.varsBelow, decide_eq_true_eq]
    by_contra hle
    push_neg at hle
    rw [List.getElem?_eq_none hle] at hlook
    exact Option.noConfusion hlook
  | lambda hpc hann heq hbody ihbody =>
    subst heq
    simpa only [Expr.varsBelow, List.length_cons] using ihbody
  | app hf hinput ihf ihinput =>
    simp only [Expr.varsBelow, Bool.and_eq_true]
    exact ⟨ihf, ihinput⟩
  | letIn hwf hann hcofin heq hbody ihcofin ihbody =>
    expose_names
    subst heq
    simp only [Expr.varsBelow, Bool.and_eq_true]
    refine ⟨?_, by simpa only [List.length_cons] using ihbody⟩
    obtain ⟨Xs, hXlen, hXnodup, hXavoid⟩ := exists_fresh_names L M.paramCount
    have hc := ihcofin Xs ⟨hXlen, hXnodup, hXavoid⟩
    rwa [Expr.varsBelow_openBoundTyVars] at hc
  | match_ hscrut hne hbrs ihscrut ihbrs =>
    simp only [Expr.varsBelow, Bool.and_eq_true]
    exact ⟨ihscrut, branchList_varsBelow_of_motive _ ihbrs⟩
  | letRec hwf hmono hpoly heq hbody ihmono ihpoly ihbody =>
    expose_names
    subst heq
    simp only [Expr.varsBelow, Bool.and_eq_true]
    have hspecslen : bindings.length = specs.length := hwf.length
    refine ⟨?_, ?_⟩
    · -- every binding is closed under the group-extended context
      apply RecGroupClosed.varsBelow_of_forall
      intro bnd hmem
      obtain ⟨s, hs⟩ := mem_zip_of_mem_left hspecslen hmem
      obtain ⟨Xs, hXlen, hXnodup, hXavoid⟩ := exists_fresh_names L G.length
      rcases s with τ | σ
      · have hc := ihmono Xs ⟨hXlen, hXnodup, hXavoid⟩ (bnd, .mono τ) hs τ rfl
        simp only [RecSpecs.rhsCtx, List.length_append, List.length_map] at hc
        rwa [Nat.add_comm, ← hspecslen] at hc
      · obtain ⟨Ys, hYlen, hYnodup, hYavoid⟩ := exists_fresh_names (L ++ Xs) σ.paramCount
        have hc := ihpoly Xs ⟨hXlen, hXnodup, hXavoid⟩ (bnd, .poly σ) hs σ rfl Ys
          ⟨hYlen, hYnodup, hYavoid⟩
        simp only [RecSpecs.rhsCtx, List.length_append, List.length_map] at hc
        rw [Expr.varsBelow_openTyVars] at hc
        rwa [Nat.add_comm, ← hspecslen] at hc
    · -- the body is closed under the group-extended context
      simp only [RecSpecs.bodyCtx, List.length_append, List.length_map] at ihbody
      rwa [Nat.add_comm, ← hspecslen] at ihbody

/-- **Well-typed in the empty context ⇒ closed.** -/
theorem TypeOfElabHM.closed {ctors : CtorEnv} {e : Expr} {τ : Ty}
    (h : TypeOfElabHM ⟨[], ctors⟩ e τ) : Expr.varsBelow 0 e = true :=
  TypeOfElabHM.varsBelow h
