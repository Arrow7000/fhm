import FHM.Bounds.BoolBranches
import FHM.Bounds.ListBranches
import FHM.Bounds.SchemeSpecialization

/-! # Bounds meaning in the existing erased small-step semantics

This is the runtime target, not another evaluator or acceptance algorithm.
Finite observation budgets permit divergence while detecting stuck states and
checking every value observed with positive budget. Arrows describe the actual
behaviour of applications, rather than only their erased HM shape.

Nominal data is currently restricted to the supported List/Bool fragment.
Other constructors require their field/variance semantics before a fundamental
theorem may cover them. Free and bound HM identities have explicit semantic
environments; their downward-closure obligations belong to environment validity.
The checker-to-runtime fundamental theorem is NOT supplied by these definitions.
-/

namespace FHM.Bounds.Runtime

/-- An exact number of steps of the existing language, with no new rules. -/
inductive Reduces : Nat → Expr → Expr → Prop where
  | refl (e) : Reduces 0 e e
  | step : SmallStep.Step e e' → Reduces n e' v → Reduces (n + 1) e v

/-- Concrete saturated List values, retaining every actual element and length. -/
inductive ListValue (element : Expr → Prop) : Expr → Nat → Prop where
  | nil : ListValue element (.ctor nilCtorName) 0
  | cons : element h → ListValue element t n →
      ListValue element (.app (.app (.ctor consCtorName) h) t) (n + 1)

theorem ListValue.map {p q : Expr → Prop} (hpq : ∀ v, p v → q v)
    (h : ListValue p v n) : ListValue q v n := by
  induction h with
  | nil => exact .nil
  | cons hh _ ih => exact .cons (hpq _ hh) ih

theorem ListValue.value {p : Expr → Prop} (elements : ∀ v, p v → SmallStep.IsValue v)
    (list : ListValue p v n) : SmallStep.IsValue v := by
  induction list with
  | nil => exact .ctor _
  | cons hh _ ih => exact .ctorApp (.app (.ctor _) (elements _ hh)) ih

theorem ListValue.closed {p : Expr → Prop} (elements : ∀ v, p v → v.varsBelow 0 = true)
    (list : ListValue p v n) : v.varsBelow 0 = true := by
  induction list with
  | nil => rfl
  | cons hh _ ih => simp only [Expr.varsBelow, elements _ hh, ih, Bool.and_self]

private theorem ctorChain_value (h : SmallStep.IsCtorChain e) : SmallStep.IsValue e := by
  cases h with
  | ctor name => exact .ctor name
  | app chain value => exact .ctorApp chain value

/-- Values cannot reduce under the existing execution rules. -/
theorem value_no_step (value : SmallStep.IsValue e) (step : SmallStep.Step e e') : False := by
  induction step with
  | beta _ => cases value with | ctorApp chain _ => cases chain
  | letReduce => cases value
  | letRecUnfold => cases value
  | matchReduce _ _ _ => cases value
  | matchWildReduce _ _ => cases value
  | matchScrut _ _ => cases value
  | deltaIntAdd | deltaIntSub | deltaIntLt | deltaCharLt =>
      cases value with
      | ctorApp chain _ => cases chain with | app base _ => cases base
  | appFn _ ih =>
      cases value with
      | ctorApp chain _ => exact ih (ctorChain_value chain)
      | primBinOpPartial _ => exact ih (.primBinOp _)
  | appArg _ _ ih =>
      cases value with
      | ctorApp _ arg => exact ih arg
      | primBinOpPartial arg => exact ih arg

theorem Reduces.from_value (value : SmallStep.IsValue e) (h : Reduces n e v) :
    n = 0 ∧ v = e := by
  cases h with
  | refl => exact ⟨rfl, rfl⟩
  | step step _ => exact False.elim (value_no_step value step)

private theorem subst_var_protected (small : i < depth) (terms : List Expr) :
    (Expr.var i).substN depth terms = .var i := by
  simp [Expr.substN, small]

private theorem subst_var_present (terms : List Expr)
    (closed : ∀ e ∈ terms, e.varsBelow 0 = true) (depth i : Nat) (small : i < terms.length) :
    (Expr.var (depth + i)).substN depth terms = terms[i] := by
  simpa only [Expr.substN, Nat.add_sub_cancel_left, if_neg (by omega : ¬ depth + i < depth),
    dif_pos small] using Expr.shiftFrom_of_closed (closed _ (List.getElem_mem small)) 0 depth

theorem closing_var (terms : List Expr) (closed : ∀ e ∈ terms, e.varsBelow 0 = true)
    (i : Nat) (inside : i < terms.length) : (Expr.var i).substN 0 terms = terms[i] := by
  simpa only [Nat.zero_add] using subst_var_present terms closed 0 i inside

private theorem subst_var_missing (large : depth ≤ i) (outside : terms.length ≤ i - depth) :
    (Expr.var i).substN depth terms = .var (i - terms.length) := by
  simp [Expr.substN, show ¬ i < depth by omega, show ¬ i - depth < terms.length by omega]

private theorem subst_var_compose (outer inner : List Expr)
    (ho : ∀ e ∈ outer, e.varsBelow 0 = true) (hi : ∀ e ∈ inner, e.varsBelow 0 = true)
    (depth i : Nat) :
    ((Expr.var i).substN (depth + inner.length) outer).substN depth inner =
      (Expr.var i).substN depth (inner ++ outer) := by
  have combined : ∀ e ∈ inner ++ outer, e.varsBelow 0 = true := by
    intro e member
    exact (List.mem_append.mp member).elim (hi e) (ho e)
  by_cases underBinder : i < depth
  · rw [subst_var_protected (by omega), subst_var_protected underBinder,
      subst_var_protected underBinder]
  · obtain ⟨j, rfl⟩ : ∃ j, i = depth + j := ⟨i - depth, by omega⟩
    by_cases inside : j < inner.length
    · rw [subst_var_protected (by omega), subst_var_present inner hi depth j inside,
        subst_var_present (inner ++ outer) combined depth j (by simp; omega),
        List.getElem_append_left inside]
    · by_cases inOuter : j - inner.length < outer.length
      · have position : depth + j = (depth + inner.length) + (j - inner.length) := by omega
        rw [position, subst_var_present outer ho _ _ inOuter,
          Expr.substN_of_closed (ho _ (List.getElem_mem inOuter))]
        rw [← position, subst_var_present (inner ++ outer) combined depth j (by simp; omega),
          List.getElem_append_right (by omega)]
      · rw [subst_var_missing (by omega) (by omega), subst_var_missing (by omega) (by omega),
          subst_var_missing (by omega) (by simp; omega)]
        congr 1
        simp only [List.length_append]
        omega

private theorem subst_match_branches (scrut : Expr) (branches : List (MatchPattern × Expr))
    (depth : Nat) (terms : List Expr) :
    ((Expr.match_ scrut branches).substN depth terms).matchBranchesOf =
      branches.map (fun br => (br.1, br.2.substN (depth + br.1.bindCount) terms)) := by
  induction branches with
  | nil => rfl
  | cons br rest ih =>
      have peel : ((Expr.match_ scrut (br :: rest)).substN depth terms).matchBranchesOf =
          (br.1, br.2.substN (depth + br.1.bindCount) terms) ::
            ((Expr.match_ scrut rest).substN depth terms).matchBranchesOf := rfl
      rw [peel, ih]
      rfl

private theorem subst_match (scrut : Expr) (branches : List (MatchPattern × Expr))
    (depth : Nat) (terms : List Expr) :
    (Expr.match_ scrut branches).substN depth terms =
      .match_ (scrut.substN depth terms)
        (branches.map (fun br => (br.1, br.2.substN (depth + br.1.bindCount) terms))) := by
  change Expr.match_ _ (((Expr.match_ scrut branches).substN depth terms).matchBranchesOf) = _
  rw [subst_match_branches]

/-- Close captures without changing patterns or first-match precedence. -/
def closeBranches (terms : List Expr) (branches : List (MatchPattern × Expr)) :=
  branches.map (fun br => (br.1, br.2.substN br.1.bindCount terms))

theorem closing_match (scrut : Expr) (branches : List (MatchPattern × Expr))
    (terms : List Expr) :
    (Expr.match_ scrut branches).substN 0 terms =
      .match_ (scrut.substN 0 terms) (closeBranches terms branches) := by
  simpa only [closeBranches, Nat.zero_add] using subst_match scrut branches 0 terms

theorem firstMatch_close {name arity branches pat body}
    (selected : SmallStep.FirstMatchingBranch name arity branches pat body) (terms : List Expr) :
    SmallStep.FirstMatchingBranch name arity (closeBranches terms branches)
      pat (body.substN pat.bindCount terms) := by
  induction selected with
  | here fires => exact .here fires
  | there misses _ ih => exact .there misses ih

/-- Recover the original branch proof, rather than guessing a source body
    from the result of substitution. -/
theorem firstMatch_unclose {name arity branches pat closedBody} (terms : List Expr)
    (selected : SmallStep.FirstMatchingBranch name arity (closeBranches terms branches) pat closedBody) :
    ∃ body, SmallStep.FirstMatchingBranch name arity branches pat body ∧
      closedBody = body.substN pat.bindCount terms := by
  induction branches with
  | nil => cases selected
  | cons br rest ih =>
      cases selected with
      | here fires => exact ⟨br.2, .here fires, rfl⟩
      | there misses next =>
          obtain ⟨body, original, same⟩ := ih next
          exact ⟨body, .there misses original, same⟩

private theorem member_close {pat body branches} (member : (pat, body) ∈ branches)
    (terms : List Expr) : (pat, body.substN pat.bindCount terms) ∈ closeBranches terms branches :=
  List.mem_map.mpr ⟨(pat, body), member, rfl⟩

theorem listCoverage_close {Δ i branches} (coverage : ListBranches.Covers Δ i branches)
    (terms : List Expr) : ListBranches.Covers Δ i (closeBranches terms branches) := by
  cases coverage with
  | full hn hc =>
      obtain ⟨bn, hn⟩ := hn
      obtain ⟨bc, hc⟩ := hc
      exact .full ⟨_, member_close hn terms⟩ ⟨_, member_close hc terms⟩
  | emptyOnly valid hn =>
      obtain ⟨body, hn⟩ := hn
      exact .emptyOnly valid ⟨_, member_close hn terms⟩
  | nonemptyOnly valid hc =>
      obtain ⟨body, hc⟩ := hc
      exact .nonemptyOnly valid ⟨_, member_close hc terms⟩
  | wildcard hw =>
      obtain ⟨body, hw⟩ := hw
      exact .wildcard ⟨_, member_close hw terms⟩

theorem boolCoverage_close {branches} (coverage : BoolBranches.Covers branches)
    (terms : List Expr) : BoolBranches.Covers (closeBranches terms branches) := by
  cases coverage with
  | full ht hf =>
      obtain ⟨bt, ht⟩ := ht
      obtain ⟨bf, hf⟩ := hf
      exact .full ⟨_, member_close ht terms⟩ ⟨_, member_close hf terms⟩
  | wildcard hw =>
      obtain ⟨body, hw⟩ := hw
      exact .wildcard ⟨_, member_close hw terms⟩

private theorem subst_rec_bindings (terms : List Expr) (depth : Nat) (bindings : List Expr) :
    RecGroup.substN depth terms bindings = bindings.map (fun e => e.substN depth terms) := by
  induction bindings with
  | nil => rfl
  | cons e rest ih => simp only [RecGroup.substN, List.map_cons, ih]

/-- Closing outer captures then opening local contents is the SAME actual Core
    substitution as closing the combined environment. Valid below arbitrary
    lambdas, match binders and mutual groups; inserted terms must be closed.
    This is the term-substitution bridge used by the runtime fundamental proof. -/
theorem closing_compose (outer inner : List Expr)
    (ho : ∀ e ∈ outer, e.varsBelow 0 = true) (hi : ∀ e ∈ inner, e.varsBelow 0 = true)
    (e : Expr) : ∀ depth,
    (e.substN (depth + inner.length) outer).substN depth inner =
      e.substN depth (inner ++ outer) := by
  induction e using Expr.rec_strong with
  | primLit | primBinOp | ctor => intro depth; rfl
  | var i => exact fun depth => subst_var_compose outer inner ho hi depth i
  | lambda ann body ih =>
      intro depth
      simp only [Expr.substN]
      congr 1
      simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ih (depth + 1)
  | app fn arg ihf iha => intro depth; simp only [Expr.substN, ihf depth, iha depth]
  | letIn ann rhs body ihr ihb =>
      intro depth
      simp only [Expr.substN]
      congr 1
      · exact ihr depth
      · simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ihb (depth + 1)
  | found ty inner ih => intro depth; simp only [Expr.substN, ih depth]
  | match_ scrut branches ihscrut ihbranches =>
      intro depth
      rw [subst_match, subst_match, subst_match, List.map_map, ihscrut depth]
      congr 1
      apply List.map_congr_left
      intro br member
      rcases br with ⟨pat, body⟩
      simp only [Function.comp_apply]
      congr 1
      simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        ihbranches pat body member (depth + pat.bindCount)
  | letRec anns bindings body ihbindings ihbody =>
      intro depth
      simp only [Expr.substN, subst_rec_bindings, List.length_map, List.map_map]
      congr 1
      · apply List.map_congr_left
        intro binding member
        simp only [Function.comp_apply]
        simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
          ihbindings binding member (depth + bindings.length)
      · simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
          ihbody (depth + bindings.length)

#print axioms closing_compose

theorem closing_singleton (outer : List Expr) (closed : ∀ e ∈ outer, e.varsBelow 0 = true)
    (inner : Expr) (innerClosed : inner.varsBelow 0 = true) (body : Expr) :
    (body.substN 1 outer).substN 0 [inner] = body.substN 0 (inner :: outer) := by
  simpa only [List.length_singleton, Nat.zero_add, List.singleton_append] using
    closing_compose outer [inner] closed
      (by intro e member; obtain rfl := List.mem_singleton.mp member; exact innerClosed) body 0

private theorem branches_scoped {depth branches}
    (h : ∀ br ∈ branches, br.2.varsBelow (depth + br.1.bindCount) = true) :
    BranchListClosed.varsBelow depth branches = true := by
  induction branches with
  | nil => rfl
  | cons br rest ih =>
      simp only [BranchListClosed.varsBelow, Bool.and_eq_true]
      exact ⟨h br (by simp), ih (fun br member => h br (List.mem_cons_of_mem _ member))⟩

private theorem bindings_scoped {depth bindings}
    (h : ∀ e ∈ bindings, e.varsBelow depth = true) :
    RecGroupClosed.varsBelow depth bindings = true := by
  induction bindings with
  | nil => rfl
  | cons e rest ih =>
      simp only [RecGroupClosed.varsBelow, Bool.and_eq_true]
      exact ⟨h e (by simp), ih (fun e member => h e (List.mem_cons_of_mem _ member))⟩

/-- Exactly the recursive replacements constructed by Core `letRecUnfold`.
    This does not build a type-passing elaboratum or expand RHS environments. -/
def recursiveTerms (annotations : List (Option PolyTy)) (rhss : List Expr) : List Expr :=
  rhss.map (fun rhs => .letRec annotations rhss rhs)

theorem recursiveTerms_closed {annotations rhss}
    (scope : ∀ rhs ∈ rhss, rhs.varsBelow rhss.length = true) :
    ∀ term ∈ recursiveTerms annotations rhss, term.varsBelow 0 = true := by
  intro term member
  obtain ⟨rhs, rhsMember, rfl⟩ := List.mem_map.mp member
  simp only [Expr.varsBelow, Nat.zero_add, Bool.and_eq_true]
  exact ⟨bindings_scoped scope, scope rhs rhsMember⟩

/-- Actual closing substitution removes exactly its environment's free term
    slots. Scope under nested and mutual binders is retained, not assumed. -/
theorem closing_scoped (terms : List Expr)
    (closed : ∀ e ∈ terms, e.varsBelow 0 = true) (e : Expr) : ∀ depth,
    e.varsBelow (depth + terms.length) = true →
      (e.substN depth terms).varsBelow depth = true := by
  induction e using Expr.rec_strong with
  | primLit | primBinOp | ctor => intro depth _; rfl
  | var i =>
      intro depth sourceScope
      simp only [Expr.varsBelow, decide_eq_true_eq] at sourceScope
      by_cases underBinder : i < depth
      · rw [subst_var_protected underBinder]
        simpa only [Expr.varsBelow, decide_eq_true_eq] using underBinder
      · obtain ⟨j, rfl⟩ : ∃ j, i = depth + j := ⟨i - depth, by omega⟩
        rw [subst_var_present terms closed depth j (by omega)]
        exact Expr.varsBelow_mono _ (Nat.zero_le depth) (closed _ (List.getElem_mem (by omega)))
  | lambda ann body ih =>
      intro depth sourceScope
      simp only [Expr.substN, Expr.varsBelow] at sourceScope ⊢
      exact ih (depth + 1) (by
        simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using sourceScope)
  | app fn arg ihf iha =>
      intro depth sourceScope
      simp only [Expr.substN, Expr.varsBelow, Bool.and_eq_true] at sourceScope ⊢
      exact ⟨ihf depth sourceScope.1, iha depth sourceScope.2⟩
  | letIn ann rhs body ihr ihb =>
      intro depth sourceScope
      simp only [Expr.substN, Expr.varsBelow, Bool.and_eq_true] at sourceScope ⊢
      exact ⟨ihr depth sourceScope.1, ihb (depth + 1) (by
        simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using sourceScope.2)⟩
  | found ty inner ih =>
      intro depth sourceScope
      simp only [Expr.substN, Expr.varsBelow] at sourceScope ⊢
      exact ih depth sourceScope
  | match_ scrut branches ihscrut ihbranches =>
      intro depth sourceScope
      simp only [Expr.varsBelow, Bool.and_eq_true] at sourceScope
      rw [subst_match]
      simp only [Expr.varsBelow, Bool.and_eq_true]
      refine ⟨ihscrut depth sourceScope.1, branches_scoped ?_⟩
      intro br member
      obtain ⟨original, inSource, rfl⟩ := List.mem_map.mp member
      rcases original with ⟨pat, body⟩
      apply ihbranches pat body inSource (depth + pat.bindCount)
      simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        BranchListClosed.varsBelow_of_mem sourceScope.2 pat body inSource
  | letRec anns bindings body ihbindings ihbody =>
      intro depth sourceScope
      simp only [Expr.varsBelow, Bool.and_eq_true] at sourceScope
      simp only [Expr.substN, subst_rec_bindings, Expr.varsBelow, List.length_map, Bool.and_eq_true]
      refine ⟨bindings_scoped ?_, ihbody (depth + bindings.length) ?_⟩
      · intro e member
        obtain ⟨original, inSource, rfl⟩ := List.mem_map.mp member
        apply ihbindings original inSource (depth + bindings.length)
        simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
          RecGroupClosed.varsBelow_of_mem sourceScope.1 original inSource
      · simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using sourceScope.2

#print axioms closing_scoped

/-- Explicit domain of the initial runtime theorem; not an inference guard. -/
inductive Supported : BoundsTy → Prop where
  | prim : Supported (.prim p)
  | bvar : Supported (.bvar i)
  | fvar : Supported (.fvar i)
  | arrow : Supported a → Supported b → Supported (.arrow a b)
  | list : Supported elem → Supported (.list lo hi elem)
  | bool : Supported (.custom boolTyName [])

abbrev TypeEnv := Nat → Nat → Expr → Prop

theorem Supported.counts (rows : CountSubstitution.Bindings) (h : Supported β) :
    Supported (CountSubstitution.bounds rows β) := by
  induction h with
  | prim => exact .prim
  | bvar => exact .bvar
  | fvar => exact .fvar
  | bool => exact .bool
  | arrow _ _ domain result => exact .arrow domain result
  | list _ element => exact .list element

theorem Supported.types (f : Nat → BoundsTy) (arguments : ∀ i, Supported (f i))
    (h : Supported β) : Supported (SchemeSpecialization.mapFree f β) := by
  induction h with
  | prim => exact .prim
  | bvar => exact .bvar
  | fvar => exact arguments _
  | bool => exact .bool
  | arrow _ _ domain result => exact .arrow domain result
  | list _ element => exact .list element

mutual
  /-- At positive budgets, values are closed and have the promised runtime
      contents. An arrow accepts every argument at any budget up to its own;
      the application budget includes the beta/delta step itself. -/
  def ValueAt (bound free : TypeEnv) (σ : Assign) (budget : Nat)
      (β : BoundsTy) (v : Expr) : Prop :=
    match budget with
    | 0 => True
    | n + 1 =>
      SmallStep.IsValue v ∧ v.varsBelow 0 = true ∧
      match β with
      | .prim p => ∃ literal, v = .primLit literal ∧ literal.ty = .prim p
      | .bvar i => bound i (n + 1) v
      | .fvar i => free i (n + 1) v
      | .arrow domain result =>
          ∀ j, j ≤ n + 1 → ∀ arg, ValueAt bound free σ j domain arg →
            TermAt bound free σ j result (.app v arg)
      | .list lo hi elem =>
          ∃ len, ListValue (ValueAt bound free σ (n + 1) elem) v len ∧
            (⟨lo, hi⟩ : Interval).Contains σ (.ofNat len)
      | .custom name args =>
          name = boolTyName ∧ args = [] ∧
            (v = .ctor BoolBranches.trueCtorName ∨ v = .ctor BoolBranches.falseCtorName)
  termination_by (sizeOf β, 0)
  decreasing_by
    all_goals apply Prod.Lex.left _ _
    all_goals simp
    all_goals omega

  /-- Every state reached before the budget expires either steps, or is a
      value satisfying the bounds at its remaining observation budget. -/
  def TermAt (bound free : TypeEnv) (σ : Assign) (budget : Nat)
      (β : BoundsTy) (e : Expr) : Prop :=
    ∀ steps v, Reduces steps e v → steps < budget →
      (SmallStep.IsValue v → ValueAt bound free σ (budget - steps) β v) ∧
      (¬ SmallStep.IsValue v → ∃ next, SmallStep.Step v next)
  termination_by (sizeOf β, 1)
  decreasing_by exact Prod.Lex.right _ (by omega)
end

/-- Instantiated type meanings must remain valid when observation fuel shrinks.
    This is a semantic environment condition, not a guessed bounds origin. -/
def TypeEnv.Downward (env : TypeEnv) : Prop :=
  ∀ i small large v, small ≤ large → env i large v → env i small v

theorem ValueAt.down {bound free σ small large β v}
    (hb : TypeEnv.Downward bound) (hf : TypeEnv.Downward free)
    (le : small ≤ large) (h : ValueAt bound free σ large β v) :
    ValueAt bound free σ small β v := by
  cases small with
  | zero => simp only [ValueAt]
  | succ small =>
    cases large with
    | zero => omega
    | succ large =>
      rw [ValueAt.eq_def] at h ⊢
      obtain ⟨value, closed, meaning⟩ := h
      refine ⟨value, closed, ?_⟩
      cases β with
      | prim p => exact meaning
      | bvar i => exact hb i _ _ v le meaning
      | fvar i => exact hf i _ _ v le meaning
      | arrow domain result =>
          intro j before arg argument
          exact meaning j (by omega) arg argument
      | list lo hi elem =>
          obtain ⟨len, elements, interval⟩ := meaning
          exact ⟨len, elements.map (fun _ hv => ValueAt.down hb hf le hv), interval⟩
      | custom name args => exact meaning
termination_by sizeOf β

theorem TermAt.down {bound free σ small large β e}
    (hb : TypeEnv.Downward bound) (hf : TypeEnv.Downward free)
    (le : small ≤ large) (h : TermAt bound free σ large β e) :
    TermAt bound free σ small β e := by
  unfold TermAt at h ⊢
  intro steps v reduction before
  obtain ⟨value, next⟩ := h steps v reduction (by omega)
  exact ⟨fun hv => (value hv).down hb hf (by omega), next⟩

theorem TermAt.of_values {bound free σ budget a b e}
    (convert : ∀ n v, ValueAt bound free σ n a v → ValueAt bound free σ n b v)
    (h : TermAt bound free σ budget a e) : TermAt bound free σ budget b e := by
  unfold TermAt at h ⊢
  intro steps v reduction before
  obtain ⟨value, steps⟩ := h steps v reduction before
  exact ⟨fun hv => convert _ _ (value hv), steps⟩

/-- Changing the type/count environment is sound only with pointwise evidence
    that it denotes the same runtime values. Reduction itself stays unchanged. -/
theorem TermAt.congr_values {bound free bound' free' σ σ' budget a b e}
    (equiv : ∀ n v, ValueAt bound free σ n a v ↔ ValueAt bound' free' σ' n b v) :
    TermAt bound free σ budget a e ↔ TermAt bound' free' σ' budget b e := by
  unfold TermAt
  constructor
  · intro h steps v reduction before
    obtain ⟨value, next⟩ := h steps v reduction before
    exact ⟨fun hv => (equiv _ _).mp (value hv), next⟩
  · intro h steps v reduction before
    obtain ⟨value, next⟩ := h steps v reduction before
    exact ⟨fun hv => (equiv _ _).mpr (value hv), next⟩

theorem ValueAt.arrow_congr {bound free bound' free' σ σ' budget a a' b b' v}
    (domain : ∀ n v, ValueAt bound free σ n a v ↔ ValueAt bound' free' σ' n a' v)
    (result : ∀ n v, ValueAt bound free σ n b v ↔ ValueAt bound' free' σ' n b' v) :
    ValueAt bound free σ budget (.arrow a b) v ↔
      ValueAt bound' free' σ' budget (.arrow a' b') v := by
  cases budget with
  | zero => simp only [ValueAt]
  | succ budget =>
      rw [ValueAt, ValueAt]
      constructor
      · rintro ⟨value, closed, behaviour⟩
        refine ⟨value, closed, ?_⟩
        intro j before arg argument
        exact (TermAt.congr_values result).mp
          (behaviour j before arg ((domain j arg).mpr argument))
      · rintro ⟨value, closed, behaviour⟩
        refine ⟨value, closed, ?_⟩
        intro j before arg argument
        exact (TermAt.congr_values result).mpr
          (behaviour j before arg ((domain j arg).mp argument))

theorem ValueAt.list_congr {bound free bound' free' σ σ' budget lo hi lo' hi' elem elem' v}
    (element : ∀ n v, ValueAt bound free σ n elem v ↔ ValueAt bound' free' σ' n elem' v)
    (interval : ∀ len, (⟨lo, hi⟩ : Interval).Contains σ (.ofNat len) ↔
      (⟨lo', hi'⟩ : Interval).Contains σ' (.ofNat len)) :
    ValueAt bound free σ budget (.list lo hi elem) v ↔
      ValueAt bound' free' σ' budget (.list lo' hi' elem') v := by
  cases budget with
  | zero => simp only [ValueAt]
  | succ budget =>
      rw [ValueAt, ValueAt]
      constructor
      · rintro ⟨value, closed, len, elements, contained⟩
        exact ⟨value, closed, len,
          elements.map (fun v hv => (element (budget + 1) v).mp hv), (interval len).mp contained⟩
      · rintro ⟨value, closed, len, elements, contained⟩
        exact ⟨value, closed, len,
          elements.map (fun v hv => (element (budget + 1) v).mpr hv), (interval len).mpr contained⟩

/-- Count instantiation has its actual semantic meaning, even below arrows.
    The same HM environment is retained: full caller type meanings are not
    accidentally reinterpreted under the callee's substituted count telescope. -/
theorem ValueAt.counts (rows : CountSubstitution.Bindings)
    (finite : CountSubstitution.Finite rows) {β} (supported : Supported β)
    (bound free : TypeEnv) (σ : Assign) :
    ∀ budget v, ValueAt bound free σ budget (CountSubstitution.bounds rows β) v ↔
      ValueAt bound free (CountSubstitution.assignment rows σ) budget β v := by
  intro budget v
  cases budget with
  | zero => simp only [ValueAt]
  | succ budget =>
    cases supported with
    | prim | bvar | fvar | bool =>
        simp only [CountSubstitution.bounds, CountSubstitution.boundsList, ValueAt]
    | arrow domain result =>
        exact ValueAt.arrow_congr (ValueAt.counts rows finite domain bound free σ)
          (ValueAt.counts rows finite result bound free σ)
    | list elem =>
        apply ValueAt.list_congr (ValueAt.counts rows finite elem bound free σ)
        intro len
        simp only [Interval.Contains, CountSubstitution.count_eval rows finite]
termination_by sizeOf β

theorem TermAt.counts (rows : CountSubstitution.Bindings)
    (finite : CountSubstitution.Finite rows) {β} (supported : Supported β)
    (bound free : TypeEnv) (σ : Assign) (budget : Nat) (e : Expr) :
    TermAt bound free σ budget (CountSubstitution.bounds rows β) e ↔
      TermAt bound free (CountSubstitution.assignment rows σ) budget β e :=
  TermAt.congr_values (ValueAt.counts rows finite supported bound free σ)

/-- Simultaneous insertion denotes each full caller type in the original caller
    environment, never recursively rewriting it through another source slot. -/
def freeEnv (bound free : TypeEnv) (σ : Assign) (types : Nat → BoundsTy) : TypeEnv :=
  fun i budget v => ValueAt bound free σ budget (types i) v

theorem freeEnv.down {bound free σ types}
    (hb : TypeEnv.Downward bound) (hf : TypeEnv.Downward free) :
  TypeEnv.Downward (freeEnv bound free σ types) :=
  fun _ _ _ _ le h => ValueAt.down hb hf le h

theorem ValueAt.types (types : Nat → BoundsTy) {β} (supported : Supported β)
    (bound free : TypeEnv) (σ : Assign) :
    ∀ budget v, ValueAt bound free σ budget (SchemeSpecialization.mapFree types β) v ↔
      ValueAt bound (freeEnv bound free σ types) σ budget β v := by
  intro budget v
  cases budget with
  | zero => simp only [ValueAt]
  | succ budget =>
    cases supported with
    | prim | bvar | bool =>
        simp only [SchemeSpecialization.mapFree, SchemeSpecialization.mapFreeList, ValueAt]
    | fvar =>
        rw [SchemeSpecialization.mapFree, ValueAt]
        change ValueAt bound free σ (budget + 1) _ v ↔
          SmallStep.IsValue v ∧ v.varsBelow 0 = true ∧ ValueAt bound free σ (budget + 1) _ v
        constructor
        · intro h
          have physical := h
          rw [ValueAt.eq_def] at physical
          exact ⟨physical.1, physical.2.1, h⟩
        · exact fun h => h.2.2
    | arrow domain result =>
        exact ValueAt.arrow_congr (ValueAt.types types domain bound free σ)
          (ValueAt.types types result bound free σ)
    | list elem =>
        exact ValueAt.list_congr (ValueAt.types types elem bound free σ) (fun _ => Iff.rfl)
termination_by sizeOf β

theorem TermAt.types (types : Nat → BoundsTy) {β} (supported : Supported β)
    (bound free : TypeEnv) (σ : Assign) (budget : Nat) (e : Expr) :
    TermAt bound free σ budget (SchemeSpecialization.mapFree types β) e ↔
      TermAt bound (freeEnv bound free σ types) σ budget β e :=
  TermAt.congr_values (ValueAt.types types supported bound free σ)

/-- The actual count-first/full-HM-second specialization used by universal RHS
    certificates. Notice that `freeEnv` is frozen at CALLER assignment `σ`, not
    at the callee assignment: caller counts inside inserted types stay owned. -/
theorem ValueAt.specialize (rows : CountSubstitution.Bindings)
    (finite : CountSubstitution.Finite rows) (types : Nat → BoundsTy) {β}
    (supported : Supported β) (bound free : TypeEnv) (σ : Assign) (budget : Nat) (v : Expr) :
    ValueAt bound free σ budget (SchemeSpecialization.mapFree types (CountSubstitution.bounds rows β)) v ↔
      ValueAt bound (freeEnv bound free σ types) (CountSubstitution.assignment rows σ) budget β v :=
  (ValueAt.types types (supported.counts rows) bound free σ budget v).trans
    (ValueAt.counts rows finite supported bound (freeEnv bound free σ types) σ budget v)

theorem TermAt.specialize (rows : CountSubstitution.Bindings)
    (finite : CountSubstitution.Finite rows) (types : Nat → BoundsTy) {β}
    (supported : Supported β) (bound free : TypeEnv) (σ : Assign) (budget : Nat) (e : Expr) :
    TermAt bound free σ budget (SchemeSpecialization.mapFree types (CountSubstitution.bounds rows β)) e ↔
      TermAt bound (freeEnv bound free σ types) (CountSubstitution.assignment rows σ) budget β e :=
  TermAt.congr_values (fun n v => ValueAt.specialize rows finite types supported bound free σ n v)

/-- Structural semantic subtyping implies inclusion of actual runtime meanings,
    including contravariant higher-order arguments. No solver call or axiom. -/
theorem subtype {Δ a b} (h : SemanticSub Δ a b)
    (ha : Supported a) (hb : Supported b) (bound free : TypeEnv) (σ : Assign)
    (premises : ∀ c ∈ Δ, c.Holds σ) :
    ∀ budget v, ValueAt bound free σ budget a v → ValueAt bound free σ budget b v := by
  cases h with
  | prim => exact fun _ _ hv => hv
  | bvar => exact fun _ _ hv => hv
  | fvar => exact fun _ _ hv => hv
  | arrow domainSub resultSub =>
      cases ha with
      | arrow haDomain haResult =>
        cases hb with
        | arrow hbDomain hbResult =>
          intro budget v hv
          cases budget with
          | zero => simp only [ValueAt]
          | succ n =>
            rw [ValueAt] at hv ⊢
            obtain ⟨value, closed, behaviour⟩ := hv
            refine ⟨value, closed, ?_⟩
            intro j before arg argument
            exact TermAt.of_values (subtype resultSub haResult hbResult bound free σ premises)
              (behaviour j before arg
                (subtype domainSub hbDomain haDomain bound free σ premises j arg argument))
  | list inclusion elemSub =>
      cases ha with
      | list haElem =>
        cases hb with
        | list hbElem =>
          intro budget v hv
          cases budget with
          | zero => simp only [ValueAt]
          | succ n =>
            rw [ValueAt] at hv ⊢
            obtain ⟨value, closed, len, elements, contained⟩ := hv
            exact ⟨value, closed, len,
              elements.map (subtype elemSub haElem hbElem bound free σ premises (n + 1)),
              contained.of_subGoals inclusion premises⟩
  | custom args =>
      cases ha with
      | bool =>
        cases args with
        | nil => exact fun _ _ hv => hv
termination_by sizeOf a + sizeOf b

/-- One existing-language step consumes one unit of semantic safety budget. -/
theorem TermAt.step {bound free σ budget β e e'}
    (h : TermAt bound free σ (budget + 1) β e) (step : SmallStep.Step e e') :
    TermAt bound free σ budget β e' := by
  unfold TermAt at h ⊢
  intro steps v reduction before
  have reached := h (steps + 1) v (.step step reduction) (by omega)
  simpa only [Nat.add_sub_add_right] using reached

/-- Backwards safety through one actual step, using language determinism.
    This is the compatibility direction needed for beta/let/group unfolding. -/
theorem TermAt.prepend {bound free σ budget β e e'}
    (step : SmallStep.Step e e') (h : TermAt bound free σ budget β e') :
    TermAt bound free σ (budget + 1) β e := by
  unfold TermAt at h ⊢
  intro steps v reduction before
  cases reduction with
  | refl =>
      exact ⟨fun value => False.elim (value_no_step value step),
        fun _ => ⟨e', step⟩⟩
  | step first rest =>
      have same := SmallStep.step_deterministic first step
      subst same
      have observed := h _ v rest (by omega)
      simpa only [Nat.add_sub_add_right] using observed

theorem TermAt.value {bound free σ budget β v}
    (value : SmallStep.IsValue v) (h : ValueAt bound free σ budget β v) :
    TermAt bound free σ budget β v := by
  unfold TermAt
  intro steps reached reduction before
  obtain ⟨zero, same⟩ := reduction.from_value value
  subst zero
  subst same
  exact ⟨fun _ => by simpa only [Nat.sub_zero] using h,
    fun notValue => False.elim (notValue value)⟩

/-- Evaluation contexts are proof-side functions, not a second runtime AST.
    Both laws refer solely to the existing value/step relations. -/
structure Context (plug : Expr → Expr) : Prop where
  step : ∀ {e e'}, SmallStep.Step e e' → SmallStep.Step (plug e) (plug e')
  value : ∀ {e}, SmallStep.IsValue (plug e) → SmallStep.IsValue e

/-- Evaluate an input before its continuation. Budgets shrink with every
    actual context step; the continuation receives only actual value evidence. -/
theorem TermAt.bind {bound free σ budget input output e plug}
    (context : Context plug) (h : TermAt bound free σ budget input e)
    (continuation : ∀ j, j ≤ budget → ∀ v, ValueAt bound free σ j input v →
      TermAt bound free σ j output (plug v)) :
    TermAt bound free σ budget output (plug e) := by
  induction budget generalizing e with
  | zero => unfold TermAt; intro steps v _ before; omega
  | succ budget ih =>
      have observation := h
      unfold TermAt at observation
      have initial := observation 0 e (.refl e) (by omega)
      by_cases value : SmallStep.IsValue e
      · exact continuation (budget + 1) (by omega) e
          (by simpa only [Nat.sub_zero] using initial.1 value)
      · obtain ⟨next, step⟩ := initial.2 value
        exact TermAt.prepend (context.step step)
          (ih (h.step step) (fun j before => continuation j (by omega)))

private theorem app_right_value (h : SmallStep.IsValue (.app f arg)) : SmallStep.IsValue arg := by
  cases h with
  | ctorApp _ value => exact value
  | primBinOpPartial value => exact value

private theorem app_left_value (h : SmallStep.IsValue (.app f arg)) : SmallStep.IsValue f := by
  cases h with
  | ctorApp chain _ => exact ctorChain_value chain
  | primBinOpPartial _ => exact .primBinOp _

/-- Ordinary application is semantically safe at the SAME finite budget.
    Arrow evidence describes actual applications; no HM-shape shortcut. -/
theorem TermAt.app {bound free σ budget domain result fn arg}
    (hb : TypeEnv.Downward bound) (hf : TypeEnv.Downward free)
    (function : TermAt bound free σ budget (.arrow domain result) fn)
    (argument : TermAt bound free σ budget domain arg) :
    TermAt bound free σ budget result (.app fn arg) := by
  apply function.bind
    (⟨fun step => .appFn step, app_left_value⟩ : Context (fun f => .app f arg))
  intro j before vf meaning
  cases j with
  | zero => unfold TermAt; intro steps v _ before; omega
  | succ j =>
      rw [ValueAt] at meaning
      obtain ⟨value, _, behaviour⟩ := meaning
      apply (argument.down hb hf before).bind
        (⟨fun step => .appArg value step, app_right_value⟩ : Context (fun v => .app vf v))
      exact behaviour

/-- Beta compatibility consumes a step before asking for the body's invariant.
    This is why recursive correctness can be proved without termination. -/
theorem ValueAt.lambda {bound free σ budget ann body param result}
    (closed : (Expr.lambda ann body).varsBelow 0 = true)
    (bodySafe : ∀ j, j < budget → ∀ arg, ValueAt bound free σ (j + 1) param arg →
      TermAt bound free σ j result (body.substN 0 [arg])) :
    ValueAt bound free σ budget (.arrow param result) (.lambda ann body) := by
  cases budget with
  | zero => simp only [ValueAt]
  | succ budget =>
      rw [ValueAt]
      refine ⟨.lambda ann body, closed, ?_⟩
      intro j before arg argument
      cases j with
      | zero => unfold TermAt; intro steps v _ before; omega
      | succ j =>
          have value := argument
          rw [ValueAt.eq_def] at value
          exact TermAt.prepend (.beta value.1) (bodySafe j (by omega) arg argument)

/-- Kernel-checked higher-order example: identity preserves arbitrary full
    runtime type meanings, including nested bounded lists and function types. -/
theorem ValueAt.identity {bound free σ budget β}
    (hb : TypeEnv.Downward bound) (hf : TypeEnv.Downward free) :
    ValueAt bound free σ budget (.arrow β β) (.lambda none (.var 0)) := by
  apply ValueAt.lambda (by rfl)
  intro j _ arg argument
  have actual := argument
  rw [ValueAt.eq_def] at actual
  have replacement : (Expr.var 0).substN 0 [arg] = arg := by
    simp [Expr.substN, Expr.shiftFrom_of_closed actual.2.1]
  rw [replacement]
  exact TermAt.value actual.1 (argument.down hb hf (by omega))

theorem ValueAt.literal (bound free : TypeEnv) (σ : Assign) (budget : Nat) (p : PrimLitExpr) :
    ValueAt bound free σ budget (boundInfoOfPrimLit p) (.primLit p) := by
  cases budget with
  | zero => simp only [ValueAt]
  | succ budget =>
      cases p <;> rw [boundInfoOfPrimLit, ValueAt] <;>
        exact ⟨.primLit _, rfl, _, rfl, rfl⟩

theorem ValueAt.bool (bound free : TypeEnv) (σ : Assign) (budget : Nat)
    (name : CtorName) (nameOK : BoolBranches.IsCtor name) :
    ValueAt bound free σ budget (.custom boolTyName []) (.ctor name) := by
  cases budget with
  | zero => simp only [ValueAt]
  | succ budget =>
      rw [ValueAt]
      exact ⟨.ctor _, rfl, rfl, rfl, nameOK.elim (fun h => .inl (congrArg Expr.ctor h))
        (fun h => .inr (congrArg Expr.ctor h))⟩

/-- One proof for curried primitive application, instantiated below by the
    actual Core delta rules. Ill-typed literal combinations supply no evidence. -/
private theorem curried_primitive (bound free : TypeEnv) (σ : Assign)
    (op : PrimBinOp) (domain : PrimTy) (result : BoundsTy)
    (delta : ∀ p q, p.ty = .prim domain → q.ty = .prim domain →
      ∃ value, SmallStep.Step (.app (.app (.primBinOp op) (.primLit p)) (.primLit q)) value ∧
        ∀ budget, ValueAt bound free σ budget result value) (budget : Nat) :
    ValueAt bound free σ budget (.arrow (.prim domain) (.arrow (.prim domain) result)) (.primBinOp op) := by
  cases budget with
  | zero => simp only [ValueAt]
  | succ budget =>
      rw [ValueAt]
      refine ⟨.primBinOp _, rfl, ?_⟩
      intro j _ arg argument
      cases j with
      | zero => unfold TermAt; intro steps v _ before; omega
      | succ j =>
          rw [ValueAt] at argument
          obtain ⟨_, _, p, rfl, pType⟩ := argument
          apply TermAt.value (.primBinOpPartial (.primLit p))
          rw [ValueAt]
          refine ⟨.primBinOpPartial (.primLit p), rfl, ?_⟩
          intro k _ arg argument
          cases k with
          | zero => unfold TermAt; intro steps v _ before; omega
          | succ k =>
              rw [ValueAt] at argument
              obtain ⟨_, _, q, rfl, qType⟩ := argument
              obtain ⟨value, step, meaning⟩ := delta p q pType qType
              have actual := meaning 1
              rw [ValueAt.eq_def] at actual
              exact TermAt.prepend step (TermAt.value actual.1 (meaning k))

/-- All four builtins satisfy their bounds types under the REAL delta rules,
    including saturated comparisons producing actual Bool constructors. -/
theorem ValueAt.primBinOp (bound free : TypeEnv) (σ : Assign) (budget : Nat) (op : PrimBinOp) :
    ValueAt bound free σ budget (Typed.primOpBounds op) (.primBinOp op) := by
  cases op with
  | intAdd =>
      apply curried_primitive bound free σ .intAdd .int (.prim .int) _ budget
      intro p q pType qType
      cases p <;> cases q <;> simp_all [PrimLitExpr.ty]
      exact ⟨_, .deltaIntAdd, fun n => ValueAt.literal bound free σ n (.int _)⟩
  | intSub =>
      apply curried_primitive bound free σ .intSub .int (.prim .int) _ budget
      intro p q pType qType
      cases p <;> cases q <;> simp_all [PrimLitExpr.ty]
      exact ⟨_, .deltaIntSub, fun n => ValueAt.literal bound free σ n (.int _)⟩
  | intLt =>
      apply curried_primitive bound free σ .intLt .int (.custom boolTyName []) _ budget
      intro p q pType qType
      cases p <;> cases q <;> simp_all [PrimLitExpr.ty]
      refine ⟨_, .deltaIntLt, ?_⟩
      intro n
      apply ValueAt.bool
      split <;> simp [BoolBranches.IsCtor, BoolBranches.trueCtorName, BoolBranches.falseCtorName]
  | charLt =>
      apply curried_primitive bound free σ .charLt .char (.custom boolTyName []) _ budget
      intro p q pType qType
      cases p <;> cases q <;> simp_all [PrimLitExpr.ty]
      refine ⟨_, .deltaCharLt, ?_⟩
      intro n
      apply ValueAt.bool
      split <;> simp [BoolBranches.IsCtor, BoolBranches.trueCtorName, BoolBranches.falseCtorName]

theorem ValueAt.nil (bound free : TypeEnv) (σ : Assign) (budget : Nat) (elem : BoundsTy) :
    ValueAt bound free σ budget (.list (.lit 0) (.lit 0) elem) (.ctor nilCtorName) := by
  cases budget with
  | zero => simp only [ValueAt]
  | succ budget =>
      rw [ValueAt]
      exact ⟨.ctor _, rfl, 0, .nil, by simp [Interval.Contains, ExtNat.le]⟩

private theorem interval_add_one {σ lo hi len}
    (h : (⟨lo, hi⟩ : Interval).Contains σ (.ofNat len)) :
    (⟨.add lo (.lit 1), .add hi (.lit 1)⟩ : Interval).Contains σ (.ofNat (len + 1)) := by
  obtain ⟨lower, upper⟩ := h
  constructor
  · change ExtNat.le (ExtNat.add (lo.eval σ) (.ofNat 1)) (.ofNat (len + 1))
    cases evaluation : lo.eval σ with
    | inf => simp [evaluation, ExtNat.le] at lower
    | ofNat n => simp_all [ExtNat.add, ExtNat.le]
  · change ExtNat.le (.ofNat (len + 1)) (ExtNat.add (hi.eval σ) (.ofNat 1))
    cases evaluation : hi.eval σ with
    | inf => trivial
    | ofNat n => simp_all [ExtNat.add, ExtNat.le]

theorem ValueAt.cons {bound free σ budget elem lo hi head tail}
    (hhead : ValueAt bound free σ budget elem head)
    (htail : ValueAt bound free σ budget (.list lo hi elem) tail) :
    ValueAt bound free σ budget (.list (.add lo (.lit 1)) (.add hi (.lit 1)) elem)
      (.app (.app (.ctor consCtorName) head) tail) := by
  cases budget with
  | zero => simp only [ValueAt]
  | succ budget =>
      have actualHead := hhead
      rw [ValueAt.eq_def] at actualHead
      rw [ValueAt] at htail ⊢
      obtain ⟨tailValue, tailClosed, len, elements, contained⟩ := htail
      refine ⟨.ctorApp (.app (.ctor _) actualHead.1) tailValue, ?_, len + 1,
        .cons hhead elements, interval_add_one contained⟩
      simp [Expr.varsBelow, actualHead.2.1, tailClosed]

theorem TermAt.cons {bound free σ budget elem lo hi head tail}
    (hb : TypeEnv.Downward bound) (hf : TypeEnv.Downward free)
    (hhead : TermAt bound free σ budget elem head)
    (htail : TermAt bound free σ budget (.list lo hi elem) tail) :
    TermAt bound free σ budget (.list (.add lo (.lit 1)) (.add hi (.lit 1)) elem)
      (.app (.app (.ctor consCtorName) head) tail) := by
  apply hhead.bind
    (⟨fun step => .appFn (.appArg (.ctor _) step),
      fun value => app_right_value (app_left_value value)⟩ :
      Context (fun h => .app (.app (.ctor consCtorName) h) tail))
  intro j before h headMeaning
  cases j with
  | zero => unfold TermAt; intro steps v _ before; omega
  | succ j =>
      have actualHead := headMeaning
      rw [ValueAt.eq_def] at actualHead
      apply (htail.down hb hf before).bind
        (⟨fun step => .appArg (.ctorApp (.ctor _) actualHead.1) step, app_right_value⟩ :
          Context (fun t => .app (.app (.ctor consCtorName) h) t))
      intro k smaller t tailMeaning
      cases k with
      | zero => unfold TermAt; intro steps v _ before; omega
      | succ k =>
          have actualTail := tailMeaning
          rw [ValueAt] at actualTail
          exact TermAt.value (.ctorApp (.app (.ctor _) actualHead.1) actualTail.1)
            (ValueAt.cons (headMeaning.down hb hf smaller) tailMeaning)

private theorem firstMatch_exists {name arity branches}
    (matched : ∃ pat body, (pat, body) ∈ branches ∧ pat.matchesCtor name arity = true) :
    ∃ pat body, SmallStep.FirstMatchingBranch name arity branches pat body := by
  induction branches with
  | nil => obtain ⟨_, _, impossible, _⟩ := matched; cases impossible
  | cons br rest ih =>
      by_cases headMatches : br.1.matchesCtor name arity = true
      · exact ⟨br.1, br.2, .here headMatches⟩
      · obtain ⟨pat, body, member, fires⟩ := matched
        have inRest : (pat, body) ∈ rest := by
          rcases List.mem_cons.mp member with same | inRest
          · subst br; exact False.elim (headMatches fires)
          · exact inRest
        obtain ⟨pat, body, first⟩ := ih ⟨pat, body, inRest, fires⟩
        exact ⟨pat, body, .there (by cases h : br.1.matchesCtor name arity <;> simp_all) first⟩

/-- Semantic coverage selects an actual FIRST branch for a concrete List value,
    exactly as the existing evaluator does (including wildcard precedence). -/
theorem ListValue.covered {element : Expr → Prop} {Δ σ lo hi branches v len}
    (list : ListValue element v len) (coverage : ListBranches.Covers Δ ⟨lo, hi⟩ branches)
    (premises : ∀ c ∈ Δ, c.Holds σ)
    (contained : (⟨lo, hi⟩ : Interval).Contains σ (.ofNat len)) :
    ∃ name args pat body, SmallStep.CtorAppliedTo v name args ∧
      SmallStep.FirstMatchingBranch name args.length branches pat body := by
  have admitted := coverage.sound premises contained
  cases list with
  | nil =>
      have matched : ∃ pat body, (pat, body) ∈ branches ∧
          pat.matchesCtor nilCtorName 0 = true := by
        rcases admitted with wild | ⟨_, empty⟩ | ⟨nonempty, _⟩
        · obtain ⟨body, member⟩ := wild
          exact ⟨.wildcard, body, member, rfl⟩
        · obtain ⟨body, member⟩ := empty
          exact ⟨.named nilCtorName 0, body, member, by simp [MatchPattern.matchesCtor]⟩
        · omega
      obtain ⟨pat, body, first⟩ := firstMatch_exists matched
      exact ⟨nilCtorName, [], pat, body, .base _, first⟩
  | @cons h t n _ _ =>
      have matched : ∃ pat body, (pat, body) ∈ branches ∧
          pat.matchesCtor consCtorName 2 = true := by
        rcases admitted with wild | ⟨empty, _⟩ | ⟨_, cons⟩
        · obtain ⟨body, member⟩ := wild
          exact ⟨.wildcard, body, member, rfl⟩
        · omega
        · obtain ⟨body, member⟩ := cons
          exact ⟨.named consCtorName 2, body, member, by simp [MatchPattern.matchesCtor]⟩
      obtain ⟨pat, body, first⟩ := firstMatch_exists matched
      exact ⟨consCtorName, [h, t], pat, body, .step (.step (.base _) :
        SmallStep.CtorAppliedTo (.app (.ctor consCtorName) h) consCtorName [h]), first⟩

/-- The branch premise is about the actual selected arm and actual substituted
    contents. The fundamental theorem must obtain it from branch derivations
    and the refined closing environment, not from a syntactic exhaustiveness flag. -/
theorem TermAt.matchList {bound free σ budget Δ lo hi elem result scrut branches}
    (scrutinee : TermAt bound free σ budget (.list lo hi elem) scrut)
    (coverage : ListBranches.Covers Δ ⟨lo, hi⟩ branches)
    (premises : ∀ c ∈ Δ, c.Holds σ)
    (branchSafe : ∀ j, j < budget → ∀ v len name args pat body,
      ListValue (ValueAt bound free σ (j + 1) elem) v len →
      (⟨lo, hi⟩ : Interval).Contains σ (.ofNat len) →
      SmallStep.CtorAppliedTo v name args →
      SmallStep.FirstMatchingBranch name args.length branches pat body →
      TermAt bound free σ j result (body.substN 0 (args.take pat.bindCount))) :
    TermAt bound free σ budget result (.match_ scrut branches) := by
  apply scrutinee.bind
    (⟨fun step => .matchScrut step, fun value => by cases value⟩ :
      Context (fun v => .match_ v branches))
  intro j before v meaning
  cases j with
  | zero => unfold TermAt; intro steps v _ before; omega
  | succ j =>
      rw [ValueAt] at meaning
      obtain ⟨value, _, len, list, contained⟩ := meaning
      obtain ⟨name, args, pat, body, applied, selected⟩ := list.covered coverage premises contained
      exact TermAt.prepend (.matchReduce value applied selected)
        (branchSafe j (by omega) v len name args pat body list contained applied selected)

private theorem bool_covered {name branches} (nameOK : BoolBranches.IsCtor name)
    (coverage : BoolBranches.Covers branches) :
    ∃ pat body, SmallStep.FirstMatchingBranch name 0 branches pat body := by
  have covered : hasWildcardBranch branches ∨
      ∃ body, (.named name 0, body) ∈ branches := by
    rcases nameOK with rfl | rfl
    · exact coverage.sound true
    · exact coverage.sound false
  apply firstMatch_exists
  rcases covered with ⟨body, member⟩ | ⟨body, member⟩
  · exact ⟨.wildcard, body, member, rfl⟩
  · exact ⟨.named name 0, body, member, by simp [MatchPattern.matchesCtor]⟩

theorem TermAt.matchBool {bound free σ budget result scrut branches}
    (scrutinee : TermAt bound free σ budget (.custom boolTyName []) scrut)
    (coverage : BoolBranches.Covers branches)
    (branchSafe : ∀ j, j < budget → ∀ name pat body,
      BoolBranches.IsCtor name → SmallStep.FirstMatchingBranch name 0 branches pat body →
      TermAt bound free σ j result (body.substN 0 (([] : List Expr).take pat.bindCount))) :
    TermAt bound free σ budget result (.match_ scrut branches) := by
  apply scrutinee.bind
    (⟨fun step => .matchScrut step, fun value => by cases value⟩ :
      Context (fun v => .match_ v branches))
  intro j before v meaning
  cases j with
  | zero => unfold TermAt; intro steps v _ before; omega
  | succ j =>
      rw [ValueAt] at meaning
      obtain ⟨value, _, _, _, constructor⟩ := meaning
      have choose : ∀ name, BoolBranches.IsCtor name → v = .ctor name →
          TermAt bound free σ (j + 1) result (.match_ v branches) := by
        intro name nameOK same
        obtain ⟨pat, body, selected⟩ := bool_covered nameOK coverage
        subst v
        exact TermAt.prepend (.matchReduce value (.base name) selected)
          (branchSafe j (by omega) name pat body nameOK selected)
      rcases constructor with trueValue | falseValue
      · exact choose _ (.inl rfl) trueValue
      · exact choose _ (.inr rfl) falseValue

/-- Unbounded observational safety allows infinite reductions; it does not
    claim termination or infer recursive invariants. -/
def Safe (bound free : TypeEnv) (σ : Assign) (β : BoundsTy) (e : Expr) : Prop :=
  ∀ budget, TermAt bound free σ budget β e

theorem Safe.app {bound free σ domain result fn arg}
    (hb : TypeEnv.Downward bound) (hf : TypeEnv.Downward free)
    (function : Safe bound free σ (.arrow domain result) fn)
    (argument : Safe bound free σ domain arg) : Safe bound free σ result (.app fn arg) :=
  fun budget => (function budget).app hb hf (argument budget)

theorem Safe.primBinOp (bound free : TypeEnv) (σ : Assign) (op : PrimBinOp) :
    Safe bound free σ (Typed.primOpBounds op) (.primBinOp op) :=
  fun budget => TermAt.value (.primBinOp op) (ValueAt.primBinOp bound free σ budget op)

theorem Safe.subtype {bound free σ Δ a b e} (h : Safe bound free σ a e)
    (sub : SemanticSub Δ a b) (ha : Supported a) (hb : Supported b)
    (premises : ∀ c ∈ Δ, c.Holds σ) : Safe bound free σ b e :=
  fun budget => TermAt.of_values (Runtime.subtype sub ha hb bound free σ premises) (h budget)

theorem Safe.step {bound free σ β e e'} (h : Safe bound free σ β e)
    (step : SmallStep.Step e e') : Safe bound free σ β e' :=
  fun budget => (h (budget + 1)).step step

theorem Safe.progress {bound free σ β e} (h : Safe bound free σ β e) :
    SmallStep.IsValue e ∨ ∃ next, SmallStep.Step e next := by
  by_cases value : SmallStep.IsValue e
  · exact .inl value
  · have observation := h 1
    unfold TermAt at observation
    exact .inr ((observation 0 e (.refl e) (by omega)).2 value)

/-- The desired observable consequence: any finitely reached List value has
    an actual constructor-spine length inside the declared interval. -/
theorem Safe.list_length {bound free σ lo hi elem e v steps}
    (h : Safe bound free σ (.list lo hi elem) e) (reduction : Reduces steps e v)
    (value : SmallStep.IsValue v) :
    ∃ len, ListValue (ValueAt bound free σ 1 elem) v len ∧
      (⟨lo, hi⟩ : Interval).Contains σ (.ofNat len) := by
  have observation := h (steps + 1)
  unfold TermAt at observation
  have observed := (observation steps v reduction (by omega)).1 value
  have : steps + 1 - steps = 1 := by omega
  rw [this] at observed
  rw [ValueAt] at observed
  exact observed.2.2

/-- A proof-based negative regression: Nil cannot satisfy a nonempty interval,
    regardless of the assignment, element type or opaque HM environment. -/
theorem Safe.not_nonempty_nil (bound free : TypeEnv) (σ : Assign) (hi : Count) (elem : BoundsTy) :
    ¬ Safe bound free σ (.list (.lit 1) hi elem) (.ctor nilCtorName) := by
  intro safe
  obtain ⟨len, list, interval⟩ := safe.list_length (.refl _) (.ctor _)
  cases list
  have lower := interval.1
  change 1 ≤ 0 at lower
  omega

/-- Higher-order negative regression: the model rejects a callback returning
    Nil when applied to a singleton, by inspecting the actual beta reduct. -/
theorem Safe.not_dropping_callback (bound free : TypeEnv) (σ : Assign) :
    ¬ Safe bound free σ
      (.arrow (.list (.lit 1) (.lit 1) (.prim .int))
        (.list (.lit 1) (.lit 1) (.prim .int))) (.lambda none (.ctor nilCtorName)) := by
  intro safe
  have observation := safe 2
  unfold TermAt at observation
  have function := (observation 0 _ (.refl _) (by omega)).1 (.lambda _ _)
  simp only [Nat.sub_zero] at function
  rw [ValueAt] at function
  let singleton : Expr := .app (.app (.ctor consCtorName) (.primLit (.int 1))) (.ctor nilCtorName)
  have argument : ValueAt bound free σ 2 (.list (.lit 1) (.lit 1) (.prim .int)) singleton := by
    simpa only [ValueAt, Interval.Contains, Count.eval, ExtNat.add, Nat.zero_add,
      boundInfoOfPrimLit] using ValueAt.cons (ValueAt.literal bound free σ 2 (.int 1))
      (ValueAt.nil bound free σ 2 (.prim .int))
  have application := function.2.2 2 (by omega) singleton argument
  have actual := argument
  rw [ValueAt] at actual
  unfold TermAt at application
  have wrong := (application 1 (.ctor nilCtorName)
    (.step (.beta actual.1) (.refl _)) (by omega)).1 (.ctor _)
  rw [ValueAt] at wrong
  obtain ⟨_, _, len, list, interval⟩ := wrong
  cases list
  have lower := interval.1
  change 1 ≤ 0 at lower
  omega

#print axioms subtype
#print axioms closing_match
#print axioms firstMatch_close
#print axioms firstMatch_unclose
#print axioms listCoverage_close
#print axioms boolCoverage_close
#print axioms ValueAt.down
#print axioms TermAt.down
#print axioms ValueAt.counts
#print axioms TermAt.counts
#print axioms ValueAt.types
#print axioms TermAt.types
#print axioms ValueAt.specialize
#print axioms TermAt.specialize
#print axioms value_no_step
#print axioms TermAt.prepend
#print axioms TermAt.bind
#print axioms TermAt.app
#print axioms ValueAt.lambda
#print axioms ValueAt.identity
#print axioms ValueAt.primBinOp
#print axioms Safe.app
#print axioms Safe.primBinOp
#print axioms ValueAt.cons
#print axioms TermAt.cons
#print axioms ListValue.covered
#print axioms TermAt.matchList
#print axioms TermAt.matchBool
#print axioms Safe.not_nonempty_nil
#print axioms Safe.not_dropping_callback
#print axioms Safe.subtype
#print axioms Safe.step
#print axioms Safe.progress
#print axioms Safe.list_length

end FHM.Bounds.Runtime
