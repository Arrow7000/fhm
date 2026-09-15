import FHM.Bounds.RecursiveHMContract
import FHM.Bounds.HMInterpretation
import FHM.Bounds.Runtime
import FHM.Bounds.NominalBranches

/-! # Recursive RHS typing with an explicit proof-side HM interpretation

This is the HM-generalization target of the checked recursive RHS fragment.
Source annotations are interpreted using one simultaneous map for the whole
derivation. Recursive assumptions retain closed templates and fixed HM vectors.
Group introduction is separate: this judgement alone licenses no assumptions.
-/

namespace FHM.Bounds.RecursiveHMJudgement

open CountSubstitution SchemeSpecialization HMInterpretation

structure Contract where
  template : HMCountScheme.Scheme
  hm : Ty
  fixed : RecursiveHMContract.Fixed template hm

inductive Binding where
  | mono (bounds : BoundsTy)
  | recursive (contract : Contract)
  | exported (scheme : HMCountScheme.Scheme)

def branchEnv (p : MatchPattern) (lo hi : Count) (elem : BoundsTy) (env : List Binding) : List Binding :=
  if p = .named consCtorName 2 then
    .mono elem :: .mono (.list (.pred lo) (.pred hi) elem) :: env
  else env

def pairBranchEnv (p : MatchPattern) (left right : BoundsTy)
    (env : List Binding) : List Binding :=
  if p = .named pairCtorName 2 then .mono left :: .mono right :: env else env

inductive ScopedDerives (types slots : Nat → BoundsTy) : List Nat → Bindings → List Constraint →
    List Binding → Expr → BoundsTy → Prop where
  | literal {env p} : ScopedDerives types slots ids rows Δ env (.primLit p) (boundInfoOfPrimLit p)
  | primBinOp {env op} : ScopedDerives types slots ids rows Δ env (.primBinOp op) (Typed.primOpBounds op)
  | nil {env elem} : ScopedDerives types slots ids rows Δ env (.ctor nilCtorName) (.list (.lit 0) (.lit 0) elem)
  | boolCtor {env name} : BoolBranches.IsCtor name →
      ScopedDerives types slots ids rows Δ env (.ctor name) (.custom boolTyName [])
  | ctor {env name β} : name ≠ nilCtorName →
      ScopedDerives types slots ids rows Δ env (.ctor name) β
  | cons {env h t head elem lo hi} :
      ScopedDerives types slots ids rows Δ env h head → ScopedDerives types slots ids rows Δ env t (.list lo hi elem) →
      SemanticSub Δ head elem →
      ScopedDerives types slots ids rows Δ env (.app (.app (.ctor consCtorName) h) t)
        (.list (.add lo (.lit 1)) (.add hi (.lit 1)) elem)
  | pair {env left right leftTy rightTy} :
      ScopedDerives types slots ids rows Δ env left leftTy →
      ScopedDerives types slots ids rows Δ env right rightTy →
      ScopedDerives types slots ids rows Δ env
        (.app (.app (.ctor pairCtorName) left) right)
        (.custom pairTyName [leftTy, rightTy])
  | varMono {env i β} : env[i]? = some (.mono β) → ScopedDerives types slots ids rows Δ env (.var i) β
  | varRecursive {env i c caller} : env[i]? = some (.recursive c) →
      (u : RecursiveHMContract.Use c.fixed Δ c.hm caller) →
      ScopedDerives types slots ids rows Δ env (.var i) u.bounds
  | varExported {env i s found caller} : env[i]? = some (.exported s) →
      (u : HMCountScheme.Use s Δ found caller) →
      ScopedDerives types slots ids rows Δ env (.var i) u.bounds
  | app {env f arg domain actual result} :
      ScopedDerives types slots ids rows Δ env f (.arrow domain result) → ScopedDerives types slots ids rows Δ env arg actual →
      SemanticSub Δ actual domain → ScopedDerives types slots ids rows Δ env (.app f arg) result
  | lambda {env ann body param result} :
      ScopedHMAnnotation.ParamOK types slots ids rows Δ ann param →
      ScopedDerives types slots ids rows Δ (.mono param :: env) body result →
      ScopedDerives types slots ids rows Δ env (.lambda ann body) (.arrow param result)
  | letMono {env ann rhs body actual result} :
      ScopedHMAnnotation.BindingOK types slots ids rows Δ ann actual →
      ScopedDerives types slots ids rows Δ env rhs actual → ScopedDerives types slots ids rows Δ (.mono actual :: env) body result →
      ScopedDerives types slots ids rows Δ env (.letIn ann rhs body) result
  | matchList {env scrut branches lo hi elem result} {actuals : Nat → BoundsTy} :
      ScopedDerives types slots ids rows Δ env scrut (.list lo hi elem) →
      ListBranches.Covers Δ ⟨lo, hi⟩ branches →
      (∀ br ∈ branches, RecursiveTyping.ListPattern br.1) →
      (∀ i br, branches[i]? = some br →
        ScopedDerives types slots ids rows (Δ ++ RecursiveTyping.branchRefine br.1 lo hi)
          (branchEnv br.1 lo hi elem env) br.2 (actuals i)) →
      (∀ i br, branches[i]? = some br →
        SemanticSub (Δ ++ RecursiveTyping.branchRefine br.1 lo hi) (actuals i) result) →
      ScopedDerives types slots ids rows Δ env (.match_ scrut branches) result
  | matchBool {env scrut branches result} {actuals : Nat → BoundsTy} :
      ScopedDerives types slots ids rows Δ env scrut (.custom boolTyName []) → BoolBranches.Covers branches →
      (∀ br ∈ branches, BoolBranches.Pattern br.1) →
      (∀ i br, branches[i]? = some br → ScopedDerives types slots ids rows Δ env br.2 (actuals i)) →
      (∀ i br, branches[i]? = some br → SemanticSub Δ (actuals i) result) →
      ScopedDerives types slots ids rows Δ env (.match_ scrut branches) result
  | matchPair {env scrut branches left right result} {actuals : Nat → BoundsTy} :
      ScopedDerives types slots ids rows Δ env scrut (.custom pairTyName [left, right]) →
      PairBranches.Covers branches →
      (∀ br ∈ branches, PairBranches.Pattern br.1) →
      (∀ i br, branches[i]? = some br →
        ScopedDerives types slots ids rows Δ (pairBranchEnv br.1 left right env)
          br.2 (actuals i)) →
      (∀ i br, branches[i]? = some br → SemanticSub Δ (actuals i) result) →
      ScopedDerives types slots ids rows Δ env (.match_ scrut branches) result
  | matchNominal {env scrut branches typeName args result} {ctors : CtorEnv}
      (fieldss : Nat → List BoundsTy) (actuals : Nat → BoundsTy) :
      ScopedDerives types slots ids rows Δ env scrut (.custom typeName args) →
      NominalBranches.Covers ctors typeName branches →
      (∀ i br, branches[i]? = some br →
        NominalBranches.PatternFields ctors typeName args br.1 (fieldss i)) →
      (∀ i br, branches[i]? = some br →
        ScopedDerives types slots ids rows Δ
          ((fieldss i).map Binding.mono ++ env) br.2 (actuals i)) →
      (∀ i br, branches[i]? = some br → SemanticSub Δ (actuals i) result) →
      ScopedDerives types slots ids rows Δ env (.match_ scrut branches) result
  /-- A wildcard-only match exposes no constructor fields and is exhaustive for
      every HM shape.  Surface variable patterns lower through this form, so it
      must not be confused with declaration-indexed nominal matching. -/
  | matchOpaque {env scrut branches scrutinee result} {actuals : Nat → BoundsTy} :
      ScopedDerives types slots ids rows Δ env scrut scrutinee →
      (∀ br ∈ branches, br.1 = .wildcard) →
      (∀ i br, branches[i]? = some br →
        ScopedDerives types slots ids rows Δ env br.2 (actuals i)) →
      (∀ i br, branches[i]? = some br → SemanticSub Δ (actuals i) result) →
      ScopedDerives types slots ids rows Δ env (.match_ scrut branches) result

/-- Compatibility view: the original API leaves lexical slots unchanged. -/
abbrev Derives (types : Nat → BoundsTy) := ScopedDerives types BoundsTy.bvar

private theorem variable_scoped {env : List α} {i value} (lookup : env[i]? = some value) :
    (Expr.var i).varsBelow env.length = true := by
  obtain ⟨small, _⟩ := List.getElem?_eq_some_iff.mp lookup
  simpa only [Expr.varsBelow, decide_eq_true_eq] using small

private theorem branches_scoped {depth branches}
    (bodies : ∀ br ∈ branches, br.2.varsBelow (depth + br.1.bindCount) = true) :
    BranchListClosed.varsBelow depth branches = true := by
  induction branches with
  | nil => rfl
  | cons br rest ih =>
      simp only [BranchListClosed.varsBelow, Bool.and_eq_true]
      exact ⟨bodies br (by simp), ih (fun br member => bodies br (List.mem_cons_of_mem _ member))⟩

/-- A real RHS derivation supplies lexical scope, not merely HM/count shape.
    Cons branches open exactly the two contents used by Core match reduction.
    This is a prerequisite for closing environments in runtime soundness. -/
theorem ScopedDerives.varsBelow {types slots ids rows Δ env e β}
    (h : ScopedDerives types slots ids rows Δ env e β) : e.varsBelow env.length = true := by
  induction h with
  | literal | primBinOp | nil | boolCtor | ctor => rfl
  | cons _ _ _ ihh iht => simp [Expr.varsBelow, ihh, iht]
  | pair _ _ ihLeft ihRight => simp [Expr.varsBelow, ihLeft, ihRight]
  | varMono lookup => exact variable_scoped lookup
  | varRecursive lookup _ => exact variable_scoped lookup
  | varExported lookup _ => exact variable_scoped lookup
  | app _ _ _ ihf iha => simp [Expr.varsBelow, ihf, iha]
  | lambda _ _ ih => simpa only [Expr.varsBelow, List.length_cons] using ih
  | letMono _ _ _ ihr ihb =>
      simp only [Expr.varsBelow, Bool.and_eq_true]
      exact ⟨ihr, by simpa only [List.length_cons] using ihb⟩
  | matchList _ _ patterns _ _ ihscrut ihbranches =>
      simp only [Expr.varsBelow, Bool.and_eq_true]
      refine ⟨ihscrut, branches_scoped ?_⟩
      intro br member
      obtain ⟨i, atIndex⟩ := List.mem_iff_getElem?.mp member
      have bodyScope := ihbranches i br atIndex
      rcases br with ⟨pat, body⟩
      rcases patterns (pat, body) member with rfl | rfl | rfl <;>
        simpa [branchEnv, MatchPattern.bindCount, nilCtorName, consCtorName] using bodyScope
  | matchBool _ _ patterns _ _ ihscrut ihbranches =>
      simp only [Expr.varsBelow, Bool.and_eq_true]
      refine ⟨ihscrut, branches_scoped ?_⟩
      intro br member
      obtain ⟨i, atIndex⟩ := List.mem_iff_getElem?.mp member
      have bodyScope := ihbranches i br atIndex
      rcases br with ⟨pat, body⟩
      rcases patterns (pat, body) member with rfl | rfl | rfl <;>
        simpa [MatchPattern.bindCount] using bodyScope
  | matchPair _ _ patterns _ _ ihscrut ihbranches =>
      simp only [Expr.varsBelow, Bool.and_eq_true]
      refine ⟨ihscrut, branches_scoped ?_⟩
      intro br member
      obtain ⟨i, atIndex⟩ := List.mem_iff_getElem?.mp member
      have bodyScope := ihbranches i br atIndex
      rcases br with ⟨pat, body⟩
      rcases patterns (pat, body) member with rfl | rfl <;>
        simpa [pairBranchEnv, MatchPattern.bindCount] using bodyScope
  | matchNominal _ _ _ _ fields _ _ ihscrut ihbranches =>
      simp only [Expr.varsBelow, Bool.and_eq_true]
      refine ⟨ihscrut, branches_scoped ?_⟩
      intro br member
      obtain ⟨i, atIndex⟩ := List.mem_iff_getElem?.mp member
      have bodyScope := ihbranches i br atIndex
      have fieldCount := (fields i br atIndex).length
      simpa only [List.length_append, List.length_map, fieldCount, Nat.add_comm] using bodyScope
  | matchOpaque _ patterns _ _ ihscrut ihbranches =>
      simp only [Expr.varsBelow, Bool.and_eq_true]
      refine ⟨ihscrut, branches_scoped ?_⟩
      intro br member
      obtain ⟨i, atIndex⟩ := List.mem_iff_getElem?.mp member
      have bodyScope := ihbranches i br atIndex
      rcases br with ⟨pat, body⟩
      rw [patterns (pat, body) member]
      simpa [MatchPattern.bindCount] using bodyScope

#print axioms ScopedDerives.varsBelow

private theorem branch_typeFree {branches : List (MatchPattern × Expr)} {br i}
    (member : br ∈ branches) (used : i ∈ br.2.tyFreeVars) :
    i ∈ Expr.tyFreeVars.BranchList.tyFreeVars branches := by
  induction branches with
  | nil => cases member
  | cons head tail ih =>
      rcases List.mem_cons.mp member with rfl | rest
      · exact List.mem_append_left _ used
      · exact List.mem_append_right _ (ih rest)

/-- Solved artifact identities need not share a source interpreter. Agreement
    on identities actually named in source annotations preserves the exact RHS
    proof, its bounds, count frames and environment. No source rewriting. -/
theorem ScopedDerives.sourceFree {types types' slots ids rows Δ env e β}
    (h : ScopedDerives types slots ids rows Δ env e β) :
    (∀ i ∈ e.tyFreeVars, types i = types' i) →
    ScopedDerives types' slots ids rows Δ env e β := by
  induction h with
  | literal => intro _; exact .literal
  | primBinOp => intro _; exact .primBinOp
  | nil => intro _; exact .nil
  | boolCtor ctor => intro _; exact .boolCtor ctor
  | ctor hn => intro _; exact .ctor hn
  | pair _ _ ihLeft ihRight =>
      intro agree
      exact .pair (ihLeft (fun i hi => agree i (by simp [Expr.tyFreeVars, hi])))
        (ihRight (fun i hi => agree i (by simp [Expr.tyFreeVars, hi])))
  | varMono lookup => intro _; exact .varMono lookup
  | varRecursive lookup used => intro _; exact .varRecursive lookup used
  | varExported lookup used => intro _; exact .varExported lookup used
  | cons _ _ sub ihh iht =>
      intro agree
      exact .cons (ihh (fun i hi => agree i (by simp [Expr.tyFreeVars, hi])))
        (iht (fun i hi => agree i (by simp [Expr.tyFreeVars, hi]))) sub
  | app _ _ sub ihf iha =>
      intro agree
      exact .app (ihf (fun i hi => agree i (by simp [Expr.tyFreeVars, hi])))
        (iha (fun i hi => agree i (by simp [Expr.tyFreeVars, hi]))) sub
  | lambda annotation _ ih =>
      intro agree
      exact .lambda
        (ScopedHMAnnotation.ParamOK.congrFree annotation
          (fun i hi => agree i (by simp [Expr.tyFreeVars, hi])))
        (ih (fun i hi => agree i (by simp [Expr.tyFreeVars, hi])))
  | letMono annotation _ _ ihr ihb =>
      intro agree
      exact .letMono
        (ScopedHMAnnotation.BindingOK.congrFree annotation
          (fun i hi => agree i (by simp [Expr.tyFreeVars, hi])))
        (ihr (fun i hi => agree i (by simp [Expr.tyFreeVars, hi])))
        (ihb (fun i hi => agree i (by simp [Expr.tyFreeVars, hi])))
  | matchList _ coverage patterns bodies subs ihs ihb =>
      intro agree
      refine .matchList (ihs (fun i hi => agree i (by simp [Expr.tyFreeVars, hi])))
        coverage patterns ?_ subs
      intro index br atIndex
      exact ihb index br atIndex (fun i hi => agree i
        (List.mem_append_right _ (branch_typeFree (List.mem_of_getElem? atIndex) hi)))
  | matchBool _ coverage patterns bodies subs ihs ihb =>
      intro agree
      refine .matchBool (ihs (fun i hi => agree i (by simp [Expr.tyFreeVars, hi])))
        coverage patterns ?_ subs
      intro index br atIndex
      exact ihb index br atIndex (fun i hi => agree i
        (List.mem_append_right _ (branch_typeFree (List.mem_of_getElem? atIndex) hi)))
  | matchPair _ coverage patterns bodies subs ihs ihb =>
      intro agree
      refine .matchPair (ihs (fun i hi => agree i (by simp [Expr.tyFreeVars, hi])))
        coverage patterns ?_ subs
      intro index br atIndex
      exact ihb index br atIndex (fun i hi => agree i
        (List.mem_append_right _ (branch_typeFree (List.mem_of_getElem? atIndex) hi)))
  | matchNominal fieldss actuals _ coverage fields bodies subs ihs ihb =>
      intro agree
      refine .matchNominal fieldss actuals
        (ihs (fun i hi => agree i (by simp [Expr.tyFreeVars, hi]))) coverage fields ?_ subs
      intro index br atIndex
      exact ihb index br atIndex (fun i hi => agree i
        (List.mem_append_right _ (branch_typeFree (List.mem_of_getElem? atIndex) hi)))
  | matchOpaque _ patterns bodies subs ihs ihb =>
      intro agree
      refine .matchOpaque (ihs (fun i hi => agree i (by simp [Expr.tyFreeVars, hi])))
        patterns ?_ subs
      intro index br atIndex
      exact ihb index br atIndex (fun i hi => agree i
        (List.mem_append_right _ (branch_typeFree (List.mem_of_getElem? atIndex) hi)))

#print axioms ScopedDerives.sourceFree

private theorem letMono_sourceSlots {types slots slots' ids rows Δ ann actual rhs body n}
    (annotation : ScopedHMAnnotation.BindingOK types slots ids rows Δ ann actual)
    (bounded : (Expr.letIn ann rhs body).TyBvarBounded n)
    (agree : ∀ i < n, slots i = slots' i) :
    ScopedHMAnnotation.BindingOK types slots' ids rows Δ ann actual ∧
      rhs.TyBvarBounded n ∧ body.TyBvarBounded n := by
  cases ann with
  | none => exact ⟨trivial, bounded.1, bounded.2⟩
  | some σ =>
      refine ⟨ScopedHMAnnotation.BindingOK.congrSlots annotation
        (fun _ equality => by cases equality; exact bounded.1) agree, ?_, bounded.2.2⟩
      simpa [annotation.1] using bounded.2.1

/-- Changing the lexical reader outside the slots scoped over the source term
    preserves its exact RHS derivation. Full types inserted by the reader stay
    opaque; only source annotations are subject to the slot bound. -/
theorem ScopedDerives.sourceSlots {types slots slots' ids rows Δ env e β n}
    (h : ScopedDerives types slots ids rows Δ env e β)
    (bounded : e.TyBvarBounded n)
    (agree : ∀ i < n, slots i = slots' i) :
    ScopedDerives types slots' ids rows Δ env e β := by
  induction h with
  | literal => exact .literal
  | primBinOp => exact .primBinOp
  | nil => exact .nil
  | boolCtor ctor => exact .boolCtor ctor
  | ctor hn => exact .ctor hn
  | pair _ _ ihLeft ihRight =>
      simp only [Expr.TyBvarBounded] at bounded
      exact .pair (ihLeft bounded.1.2) (ihRight bounded.2)
  | varMono lookup => exact .varMono lookup
  | varRecursive lookup used => exact .varRecursive lookup used
  | varExported lookup used => exact .varExported lookup used
  | cons _ _ sub ihh iht =>
      simp only [Expr.TyBvarBounded] at bounded
      exact .cons (ihh bounded.1.2) (iht bounded.2) sub
  | app _ _ sub ihf iha =>
      exact .app (ihf bounded.1) (iha bounded.2) sub
  | lambda annotation _ ih =>
      exact .lambda (ScopedHMAnnotation.ParamOK.congrSlots annotation bounded.1 agree)
        (ih bounded.2)
  | letMono annotation _ _ ihr ihb =>
      have moved := letMono_sourceSlots annotation bounded agree
      exact .letMono moved.1 (ihr moved.2.1) (ihb moved.2.2)
  | matchList _ coverage patterns bodies subs ihs ihb =>
      refine .matchList (ihs bounded.1) coverage patterns ?_ subs
      intro index br atIndex
      exact ihb index br atIndex
        (Expr.TyBvarBounded.BranchList_iff.mp bounded.2 br.1 br.2
          (List.mem_of_getElem? atIndex))
  | matchBool _ coverage patterns bodies subs ihs ihb =>
      refine .matchBool (ihs bounded.1) coverage patterns ?_ subs
      intro index br atIndex
      exact ihb index br atIndex
        (Expr.TyBvarBounded.BranchList_iff.mp bounded.2 br.1 br.2
          (List.mem_of_getElem? atIndex))
  | matchPair _ coverage patterns bodies subs ihs ihb =>
      refine .matchPair (ihs bounded.1) coverage patterns ?_ subs
      intro index br atIndex
      exact ihb index br atIndex
        (Expr.TyBvarBounded.BranchList_iff.mp bounded.2 br.1 br.2
          (List.mem_of_getElem? atIndex))
  | matchNominal fieldss actuals _ coverage fields bodies subs ihs ihb =>
      refine .matchNominal fieldss actuals (ihs bounded.1) coverage fields ?_ subs
      intro index br atIndex
      exact ihb index br atIndex
        (Expr.TyBvarBounded.BranchList_iff.mp bounded.2 br.1 br.2
          (List.mem_of_getElem? atIndex))
  | matchOpaque _ patterns bodies subs ihs ihb =>
      refine .matchOpaque (ihs bounded.1) patterns ?_ subs
      intro index br atIndex
      exact ihb index br atIndex
        (Expr.TyBvarBounded.BranchList_iff.mp bounded.2 br.1 br.2
          (List.mem_of_getElem? atIndex))

#print axioms ScopedDerives.sourceSlots

/-- Runtime realization of an assumption. Recursive entries promise actual
    behaviour at every usable count instance, not just the fixed HM skeleton.
    Raw instantiated premises must hold at the actual count assignment. The
    ambient static path context is intentionally not baked into this predicate. -/
def BindingAt (bound free : Runtime.TypeEnv) (σ : Assign) (budget : Nat)
    (binding : Binding) (term : Expr) : Prop :=
  match binding with
  | .mono β => Runtime.TermAt bound free σ budget β term
  | .recursive c =>
      ∀ Δ caller (used : RecursiveHMContract.Use c.fixed Δ c.hm caller),
        (∀ p ∈ used.inst.premises, p.Holds σ) →
          Runtime.TermAt bound free σ budget used.bounds term
  | .exported s =>
      ∀ Δ found caller (used : HMCountScheme.Use s Δ found caller),
        (∀ a ∈ used.types, Runtime.Supported a) →
        (∀ p ∈ used.countInstance.premises, p.Holds σ) →
        Runtime.TermAt bound free σ budget used.bounds term

/-- One closing environment for the existing RHS judgment. These are semantic
    proof obligations, not a new typing judgment or executable checker. -/
structure EnvAt (bound free : Runtime.TypeEnv) (σ : Assign) (budget : Nat)
    (env : List Binding) where
  terms : List Expr
  arity : terms.length = env.length
  closed : ∀ e ∈ terms, e.varsBelow 0 = true
  denotes : ∀ i (inside : i < env.length),
    BindingAt bound free σ budget env[i]
      (terms[i]'(by rw [arity]; exact inside))

theorem BindingAt.zero (bound free : Runtime.TypeEnv) (σ : Assign) (binding : Binding) (term : Expr) :
    BindingAt bound free σ 0 binding term := by
  have vacuous : ∀ β, Runtime.TermAt bound free σ 0 β term := by
    intro β
    unfold Runtime.TermAt
    intro steps value _ before
    omega
  cases binding with
  | mono β => exact vacuous β
  | recursive c => exact fun _ _ _ _ => vacuous _
  | exported s => exact fun _ _ _ _ _ _ => vacuous _

theorem BindingAt.prepend {bound free σ budget binding term next}
    (step : SmallStep.Step term next) (safe : BindingAt bound free σ budget binding next) :
    BindingAt bound free σ (budget + 1) binding term := by
  cases binding with
  | mono β => exact Runtime.TermAt.prepend step safe
  | recursive c =>
      exact fun Δ caller used premises => Runtime.TermAt.prepend step (safe Δ caller used premises)
  | exported s =>
      exact fun Δ found caller used arguments premises =>
        Runtime.TermAt.prepend step (safe Δ found caller used arguments premises)

/-- Tie ALL members simultaneously by induction on observation budget. The
    premise checks each actual RHS under a realizing assumption environment;
    it does not assume the recursive replacements already satisfy a contract.
    The resulting terms are exactly Core's replacements, even for mutual cycles.
    Static universal-member certificates must discharge this RHS premise. -/
def EnvAt.tieGroup {bound free σ env} (annotations : List (Option PolyTy)) (rhss : List Expr)
    (arity : rhss.length = env.length)
    (scope : ∀ rhs ∈ rhss, rhs.varsBelow rhss.length = true)
    (rhsSafe : ∀ budget (e : EnvAt bound free σ budget env) i (inside : i < env.length),
      BindingAt bound free σ budget env[i]
        (rhss[i]'(by rw [arity]; exact inside) |>.substN 0 e.terms)) :
    ∀ budget, { e : EnvAt bound free σ budget env // e.terms = Runtime.recursiveTerms annotations rhss }
  | 0 =>
      ⟨{ terms := Runtime.recursiveTerms annotations rhss
         arity := by simp only [Runtime.recursiveTerms, List.length_map, arity]
         closed := Runtime.recursiveTerms_closed scope
         denotes := fun i inside => BindingAt.zero bound free σ env[i] _ }, rfl⟩
  | budget + 1 => by
      let previous := EnvAt.tieGroup annotations rhss arity scope rhsSafe budget
      refine ⟨{ terms := Runtime.recursiveTerms annotations rhss
                arity := by simp only [Runtime.recursiveTerms, List.length_map, arity]
                closed := Runtime.recursiveTerms_closed scope
                denotes := ?_ }, rfl⟩
      intro i inside
      have memberSafe := rhsSafe budget previous.val i inside
      rw [previous.property] at memberSafe
      simp only [Runtime.recursiveTerms, List.getElem_map]
      exact BindingAt.prepend SmallStep.Step.letRecUnfold memberSafe

#print axioms EnvAt.tieGroup

def EnvAt.down {bound free σ small large env}
    (e : EnvAt bound free σ large env)
    (hb : Runtime.TypeEnv.Downward bound) (hf : Runtime.TypeEnv.Downward free)
    (le : small ≤ large) : EnvAt bound free σ small env := by
  refine ⟨e.terms, e.arity, e.closed, ?_⟩
  intro i inside
  have actual := e.denotes i inside
  cases kind : env[i] with
  | mono β =>
      simp only [BindingAt, kind] at actual ⊢
      exact actual.down hb hf le
  | recursive c =>
      simp only [BindingAt, kind] at actual ⊢
      intro Δ caller used premises
      exact (actual Δ caller used premises).down hb hf le
  | exported s =>
      simp only [BindingAt, kind] at actual ⊢
      intro Δ found caller used arguments premises
      exact (actual Δ found caller used arguments premises).down hb hf le

/-- Close only the outer variables of every recursive RHS.  The first
    `rhss.length` variables remain protected for the simultaneously tied group. -/
def closeOuterRhss (rhss : List Expr) (outer : List Expr) : List Expr :=
  rhss.map fun rhs => rhs.substN rhss.length outer

theorem closeOuterRhss_length (rhss outer : List Expr) :
    (closeOuterRhss rhss outer).length = rhss.length := by
  simp [closeOuterRhss]

theorem closeOuterRhss_scoped {bound free σ budget outerEnv}
    (outer : EnvAt bound free σ budget outerEnv) {rhss : List Expr}
    (scope : ∀ rhs ∈ rhss, rhs.varsBelow (rhss.length + outerEnv.length) = true) :
    ∀ rhs ∈ closeOuterRhss rhss outer.terms, rhs.varsBelow rhss.length = true := by
  intro rhs member
  obtain ⟨source, sourceMember, rfl⟩ := List.mem_map.mp member
  apply Runtime.closing_scoped outer.terms outer.closed source rhss.length
  rw [outer.arity]
  exact scope source sourceMember

/-- Tie a recursive group while retaining an already realized outer lexical
    environment.  Recursive replacements contain the outer-closing
    substitution exactly once; the member premise is still checked against the
    single combined `inner ++ outer` assumption environment.

    This is the captured analogue of `tieGroup`, proved by the same finite
    observation-budget induction.  It does not assume termination and does not
    grant any group interface on its own. -/
def EnvAt.tieGroupCaptured {bound free σ innerEnv outerEnv}
    (annotations : List (Option PolyTy)) (rhss : List Expr)
    (arity : rhss.length = innerEnv.length)
    (scope : ∀ rhs ∈ rhss, rhs.varsBelow (rhss.length + outerEnv.length) = true)
    (hb : Runtime.TypeEnv.Downward bound) (hf : Runtime.TypeEnv.Downward free)
    (rhsSafe : ∀ budget (e : EnvAt bound free σ budget (innerEnv ++ outerEnv))
      i (inside : i < innerEnv.length),
      BindingAt bound free σ budget innerEnv[i]
        (rhss[i]'(by rw [arity]; exact inside) |>.substN 0 e.terms)) :
    ∀ budget (outer : EnvAt bound free σ budget outerEnv),
      { e : EnvAt bound free σ budget (innerEnv ++ outerEnv) //
        e.terms = Runtime.recursiveTerms annotations (closeOuterRhss rhss outer.terms) ++
          outer.terms }
  | 0, outer => by
      let closedRhss := closeOuterRhss rhss outer.terms
      let recursive := Runtime.recursiveTerms annotations closedRhss
      have recursiveClosed : ∀ term ∈ recursive, term.varsBelow 0 = true :=
        Runtime.recursiveTerms_closed (by
          simpa only [closedRhss, closeOuterRhss_length] using
            closeOuterRhss_scoped outer scope)
      refine ⟨{ terms := recursive ++ outer.terms
                arity := ?_
                closed := ?_
                denotes := fun i inside => BindingAt.zero bound free σ _ _ }, rfl⟩
      · simp only [List.length_append, recursive, Runtime.recursiveTerms, List.length_map,
          closedRhss, closeOuterRhss_length, outer.arity, arity]
      · intro term member
        exact (List.mem_append.mp member).elim (recursiveClosed term) (outer.closed term)
  | budget + 1, outer => by
      let previousOuter := outer.down hb hf (by omega : budget ≤ budget + 1)
      let previous := EnvAt.tieGroupCaptured annotations rhss arity scope hb hf rhsSafe
        budget previousOuter
      let closedRhss := closeOuterRhss rhss outer.terms
      let recursive := Runtime.recursiveTerms annotations closedRhss
      have recursiveClosed : ∀ term ∈ recursive, term.varsBelow 0 = true :=
        Runtime.recursiveTerms_closed (by
          simpa only [closedRhss, closeOuterRhss_length] using
            closeOuterRhss_scoped outer scope)
      refine ⟨{ terms := recursive ++ outer.terms
                arity := ?_
                closed := ?_
                denotes := ?_ }, rfl⟩
      · simp only [List.length_append, recursive, Runtime.recursiveTerms, List.length_map,
          closedRhss, closeOuterRhss_length, outer.arity, arity]
      · intro term member
        exact (List.mem_append.mp member).elim (recursiveClosed term) (outer.closed term)
      · intro i inside
        by_cases inner : i < innerEnv.length
        · have rhsInside : i < rhss.length := by rw [arity]; exact inner
          have safe := rhsSafe budget previous.val i inner
          have previousTerms : previousOuter.terms = outer.terms := rfl
          rw [previous.property, previousTerms] at safe
          have composed := Runtime.closing_compose outer.terms recursive outer.closed
            recursiveClosed (rhss[i]'rhsInside) 0
          have recursiveLength : recursive.length = rhss.length := by
            simp only [recursive, Runtime.recursiveTerms, List.length_map,
              closedRhss, closeOuterRhss_length]
          rw [Nat.zero_add, recursiveLength] at composed
          rw [← composed] at safe
          have closedInside : i < closedRhss.length := by
            rw [closeOuterRhss_length]
            exact rhsInside
          have recursiveInside : i < recursive.length := by rw [recursiveLength]; exact rhsInside
          have rhsEntry : closedRhss[i]'closedInside =
              (rhss[i]'rhsInside).substN rhss.length outer.terms := by
            simp only [closedRhss, closeOuterRhss, List.getElem_map]
          have recursiveEntry : recursive[i]'recursiveInside =
              .letRec annotations closedRhss (closedRhss[i]'closedInside) := by
            simp only [recursive, Runtime.recursiveTerms, List.getElem_map]
          rw [List.getElem_append_left inner, List.getElem_append_left recursiveInside]
          rw [recursiveEntry, rhsEntry]
          exact BindingAt.prepend SmallStep.Step.letRecUnfold safe
        · have outerInside : i - innerEnv.length < outerEnv.length := by
            simp only [List.length_append] at inside
            omega
          have meaning := outer.denotes (i - innerEnv.length) outerInside
          have recursiveLength : recursive.length = innerEnv.length := by
            simp only [recursive, Runtime.recursiveTerms, List.length_map,
              closedRhss, closeOuterRhss_length, arity]
          have envPosition : innerEnv.length ≤ i := by omega
          have recursivePosition : recursive.length ≤ i := by rw [recursiveLength]; exact envPosition
          rw [List.getElem_append_right envPosition,
            List.getElem_append_right recursivePosition]
          simpa only [recursiveLength] using meaning

#print axioms EnvAt.tieGroupCaptured

def EnvAt.extendMono {bound free σ budget env}
    (e : EnvAt bound free σ budget env) (β : BoundsTy) (term : Expr)
    (closed : term.varsBelow 0 = true) (safe : Runtime.TermAt bound free σ budget β term) :
    EnvAt bound free σ budget (.mono β :: env) where
  terms := term :: e.terms
  arity := by simp only [List.length_cons, e.arity]
  closed := by
    intro v member
    rcases List.mem_cons.mp member with rfl | rest
    · exact closed
    · exact e.closed v rest
  denotes := by
    intro i inside
    cases i with
    | zero => exact safe
    | succ i =>
        have small : i < env.length := by simp only [List.length_cons] at inside; omega
        simpa only [List.getElem_cons_succ] using e.denotes i small

#print axioms EnvAt.down
#print axioms EnvAt.extendMono

theorem EnvAt.varMono {bound free σ budget env i β}
    (e : EnvAt bound free σ budget env) (lookup : env[i]? = some (.mono β)) :
    Runtime.TermAt bound free σ budget β ((Expr.var i).substN 0 e.terms) := by
  obtain ⟨inside, entry⟩ := List.getElem?_eq_some_iff.mp lookup
  rw [Runtime.closing_var e.terms e.closed i (by rw [e.arity]; exact inside)]
  have meaning := e.denotes i inside
  simpa only [BindingAt, entry] using meaning

theorem EnvAt.varRecursive {bound free σ budget env i c Δ caller}
    (e : EnvAt bound free σ budget env) (lookup : env[i]? = some (.recursive c))
    (used : RecursiveHMContract.Use c.fixed Δ c.hm caller)
    (premises : ∀ p ∈ Δ, p.Holds σ) :
    Runtime.TermAt bound free σ budget used.bounds ((Expr.var i).substN 0 e.terms) := by
  obtain ⟨inside, entry⟩ := List.getElem?_eq_some_iff.mp lookup
  rw [Runtime.closing_var e.terms e.closed i (by rw [e.arity]; exact inside)]
  have meaning := e.denotes i inside
  simp only [BindingAt, entry] at meaning
  exact meaning Δ caller used (used.usable σ premises)

theorem EnvAt.varExported {bound free σ budget env i s Δ found caller}
    (e : EnvAt bound free σ budget env) (lookup : env[i]? = some (.exported s))
    (used : HMCountScheme.Use s Δ found caller)
    (arguments : ∀ a ∈ used.types, Runtime.Supported a)
    (premises : ∀ p ∈ Δ, p.Holds σ) :
    Runtime.TermAt bound free σ budget used.bounds ((Expr.var i).substN 0 e.terms) := by
  obtain ⟨inside, entry⟩ := List.getElem?_eq_some_iff.mp lookup
  rw [Runtime.closing_var e.terms e.closed i (by rw [e.arity]; exact inside)]
  have meaning := e.denotes i inside
  simp only [BindingAt, entry] at meaning
  exact meaning Δ found caller used arguments (used.usable σ premises)

#print axioms EnvAt.varMono
#print axioms EnvAt.varRecursive
#print axioms EnvAt.varExported

/-- A uniformly realized group gives actual recursive implementation safety,
    not merely safety of an environment lookup. Raw instantiated premises are
    sufficient; a caller's unrelated ambient context is not assumed to hold. -/
theorem EnvAt.recursiveMemberSafe {bound free σ env annotations rhss c Δ caller rhs} {i : Nat}
    (realized : ∀ budget, { e : EnvAt bound free σ budget env //
      e.terms = Runtime.recursiveTerms annotations rhss })
    (lookup : env[i]? = some (Binding.recursive c))
    (used : RecursiveHMContract.Use c.fixed Δ c.hm caller)
    (premises : ∀ p ∈ used.inst.premises, p.Holds σ)
    (rhsLookup : rhss[i]? = some rhs) :
    Runtime.Safe bound free σ used.bounds (.letRec annotations rhss rhs) := by
  intro budget
  let e := realized budget
  obtain ⟨inside, entry⟩ := List.getElem?_eq_some_iff.mp lookup
  have closedVariable : Runtime.TermAt bound free σ budget used.bounds ((Expr.var i).substN 0 e.val.terms) := by
    rw [Runtime.closing_var e.val.terms e.val.closed i (by rw [e.val.arity]; exact inside)]
    have actual := e.val.denotes i inside
    simp only [BindingAt, entry] at actual
    exact actual Δ caller used premises
  rw [e.property] at closedVariable
  have termInside : i < (Runtime.recursiveTerms annotations rhss).length := by
    rw [← e.property, e.val.arity]
    exact inside
  have termsClosed : ∀ term ∈ Runtime.recursiveTerms annotations rhss, term.varsBelow 0 = true := by
    simpa only [e.property] using e.val.closed
  rw [Runtime.closing_var _ termsClosed i termInside] at closedVariable
  obtain ⟨rhsInside, rhsEntry⟩ := List.getElem?_eq_some_iff.mp rhsLookup
  simpa only [Runtime.recursiveTerms, List.getElem_map, rhsEntry] using closedVariable

#print axioms EnvAt.recursiveMemberSafe

theorem EnvAt.closes {bound free σ budget env types slots ids rows Δ expr β}
    (e : EnvAt bound free σ budget env)
    (h : ScopedDerives types slots ids rows Δ env expr β) :
    (expr.substN 0 e.terms).varsBelow 0 = true := by
  apply Runtime.closing_scoped e.terms e.closed expr 0
  simpa only [Nat.zero_add, e.arity] using h.varsBelow

/-- The actual contents selected by a List match realize exactly the branch
    context, and justify its arithmetic path premises. No branch-local count
    assumption is added without a corresponding concrete constructor. -/
theorem EnvAt.listBranch {bound free σ budget env lo hi elem v len name args pat body branches}
    (e : EnvAt bound free σ budget env)
    (hb : Runtime.TypeEnv.Downward bound) (hf : Runtime.TypeEnv.Downward free)
    (list : Runtime.ListValue (Runtime.ValueAt bound free σ (budget + 1) elem) v len)
    (contained : (⟨lo, hi⟩ : Interval).Contains σ (.ofNat len))
    (applied : SmallStep.CtorAppliedTo v name args)
    (selected : SmallStep.FirstMatchingBranch name args.length branches pat body)
    (pattern : RecursiveTyping.ListPattern pat) :
    (∀ p ∈ RecursiveTyping.branchRefine pat lo hi, p.Holds σ) ∧
      ∃ opened : EnvAt bound free σ budget (branchEnv pat lo hi elem env),
        opened.terms = args.take pat.bindCount ++ e.terms := by
  rcases pattern with rfl | rfl | rfl
  · simp only [RecursiveTyping.branchRefine, branchEnv, MatchPattern.bindCount,
      List.take_zero, List.nil_append]
    exact ⟨by simp [nilCtorName, consCtorName], by simpa [nilCtorName, consCtorName] using ⟨e, rfl⟩⟩
  · cases list with
    | nil =>
        obtain ⟨rfl, rfl⟩ := applied.det (.base nilCtorName)
        simp only [RecursiveTyping.branchRefine, branchEnv, MatchPattern.bindCount,
          List.take_zero, List.nil_append]
        exact ⟨by simpa using ListBranches.nil_refine contained,
          by simpa [nilCtorName, consCtorName] using ⟨e, rfl⟩⟩
    | @cons headTerm tailTerm n head tail =>
        have canonical : SmallStep.CtorAppliedTo _ consCtorName [headTerm, tailTerm] :=
          .step (.step (.base consCtorName))
        obtain ⟨rfl, rfl⟩ := applied.det canonical
        have fires := selected.ctor_eq
        simp [MatchPattern.matchesCtor, nilCtorName, consCtorName] at fires
  · cases list with
    | nil =>
        obtain ⟨rfl, rfl⟩ := applied.det (.base nilCtorName)
        have fires := selected.ctor_eq
        simp [MatchPattern.matchesCtor, nilCtorName, consCtorName] at fires
    | @cons headTerm tailTerm n head tail =>
        have canonical : SmallStep.CtorAppliedTo _ consCtorName [headTerm, tailTerm] :=
          .step (.step (.base consCtorName))
        obtain ⟨rfl, rfl⟩ := applied.det canonical
        have headFacts := head
        rw [Runtime.ValueAt.eq_def] at headFacts
        have tailValue := tail.value (fun v hv => by rw [Runtime.ValueAt.eq_def] at hv; exact hv.1)
        have tailClosed := tail.closed (fun v hv => by rw [Runtime.ValueAt.eq_def] at hv; exact hv.2.1)
        have tailBounds : Runtime.ValueAt bound free σ (budget + 1)
            (.list (.pred lo) (.pred hi) elem) tailTerm := by
          rw [Runtime.ValueAt]
          exact ⟨tailValue, tailClosed, n, tail, ListBranches.tail_contains contained⟩
        let opened := (e.extendMono (.list (.pred lo) (.pred hi) elem) tailTerm tailClosed
          (Runtime.TermAt.value tailValue (tailBounds.down hb hf (by omega)))).extendMono
            elem headTerm headFacts.2.1
            (Runtime.TermAt.value headFacts.1 (head.down hb hf (by omega)))
        refine ⟨?_, ?_⟩
        · simpa [RecursiveTyping.branchRefine, nilCtorName, consCtorName] using
            ListBranches.cons_refine contained
        · refine ⟨?_, ?_⟩
          · simpa only [branchEnv, if_pos rfl] using opened
          · rfl

#print axioms EnvAt.listBranch

/-- The two concrete fields selected by a Pair match realize the exact branch
    environment. Pair patterns carry no arithmetic refinement. -/
theorem EnvAt.pairBranch {bound free σ budget env leftTy rightTy left right pat}
    (e : EnvAt bound free σ budget env)
    (hb : Runtime.TypeEnv.Downward bound) (hf : Runtime.TypeEnv.Downward free)
    (leftMeaning : Runtime.ValueAt bound free σ (budget + 1) leftTy left)
    (rightMeaning : Runtime.ValueAt bound free σ (budget + 1) rightTy right)
    (pattern : PairBranches.Pattern pat) :
    ∃ opened : EnvAt bound free σ budget (pairBranchEnv pat leftTy rightTy env),
      opened.terms = [left, right].take pat.bindCount ++ e.terms := by
  rcases pattern with rfl | rfl
  · simpa [pairBranchEnv, MatchPattern.bindCount] using ⟨e, rfl⟩
  · have leftFacts := leftMeaning
    have rightFacts := rightMeaning
    rw [Runtime.ValueAt.eq_def] at leftFacts rightFacts
    let opened := (e.extendMono rightTy right rightFacts.2.1
      (Runtime.TermAt.value rightFacts.1 (rightMeaning.down hb hf (by omega)))).extendMono
        leftTy left leftFacts.2.1
        (Runtime.TermAt.value leftFacts.1 (leftMeaning.down hb hf (by omega)))
    refine ⟨?_, ?_⟩
    · simpa only [pairBranchEnv, if_pos rfl] using opened
    · rfl

#print axioms EnvAt.pairBranch

namespace ScopedDerives

/-- Proof-fragment metadata on an EXISTING derivation, not a second acceptance
    judgment. Every intermediate type used by semantic inclusion must have a
    justified runtime interpretation. In particular, supporting only the final
    result would silently overlook an unsupported application domain. -/
inductive RuntimeReady {types slots ids rows} :
    {Δ : List Constraint} → {env : List Binding} → {e : Expr} → {β : BoundsTy} →
    ScopedDerives types slots ids rows Δ env e β → Prop where
  | literal : RuntimeReady (.literal (p := p))
  | primBinOp : RuntimeReady (.primBinOp (op := op))
  | nil : Runtime.Supported elem → RuntimeReady (.nil (elem := elem))
  | boolCtor (nameOK : BoolBranches.IsCtor name) : RuntimeReady (.boolCtor nameOK)
  | cons {hh : ScopedDerives types slots ids rows Δ env h head}
      {ht : ScopedDerives types slots ids rows Δ env t (.list lo hi elem)}
      (sub : SemanticSub Δ head elem) : RuntimeReady hh → RuntimeReady ht →
      RuntimeReady (.cons hh ht sub)
  | pair {hleft : ScopedDerives types slots ids rows Δ env left leftTy}
      {hright : ScopedDerives types slots ids rows Δ env right rightTy} :
      RuntimeReady hleft → RuntimeReady hright → RuntimeReady (.pair hleft hright)
  | varMono (lookup : env[i]? = some (Binding.mono β)) :
      Runtime.Supported β → RuntimeReady (.varMono lookup)
  | varRecursive (lookup : env[i]? = some (Binding.recursive c))
      (used : RecursiveHMContract.Use c.fixed Δ c.hm caller) :
      Runtime.Supported used.bounds → RuntimeReady (.varRecursive lookup used)
  | varExported (lookup : env[i]? = some (Binding.exported s))
      (used : HMCountScheme.Use s Δ found caller) :
      Runtime.Supported used.bounds → (∀ a ∈ used.types, Runtime.Supported a) →
      RuntimeReady (.varExported lookup used)
  | app {hfn : ScopedDerives types slots ids rows Δ env f (.arrow domain result)}
      {ha : ScopedDerives types slots ids rows Δ env arg actual}
      (sub : SemanticSub Δ actual domain) : RuntimeReady hfn → RuntimeReady ha →
      RuntimeReady (.app hfn ha sub)
  | lambda {param : BoundsTy} (annOK : ScopedHMAnnotation.ParamOK types slots ids rows Δ ann param)
      {hbody : ScopedDerives types slots ids rows Δ (.mono param :: env) body result} :
      Runtime.Supported param → RuntimeReady hbody → RuntimeReady (.lambda annOK hbody)
  | letMono (annOK : ScopedHMAnnotation.BindingOK types slots ids rows Δ ann actual)
      {hrhs : ScopedDerives types slots ids rows Δ env rhs actual}
      {hbody : ScopedDerives types slots ids rows Δ (.mono actual :: env) body result} :
      RuntimeReady hrhs → RuntimeReady hbody → RuntimeReady (.letMono annOK hrhs hbody)
  | matchList {actuals : Nat → BoundsTy}
      {hs : ScopedDerives types slots ids rows Δ env scrut (.list lo hi elem)}
      (coverage : ListBranches.Covers Δ ⟨lo, hi⟩ branches)
      (patterns : ∀ br ∈ branches, RecursiveTyping.ListPattern br.1)
      (bodies : ∀ i br, branches[i]? = some br →
        ScopedDerives types slots ids rows (Δ ++ RecursiveTyping.branchRefine br.1 lo hi)
          (branchEnv br.1 lo hi elem env) br.2 (actuals i))
      (subs : ∀ i br, branches[i]? = some br →
        SemanticSub (Δ ++ RecursiveTyping.branchRefine br.1 lo hi) (actuals i) result) :
      RuntimeReady hs → (∀ i br atIndex, RuntimeReady (bodies i br atIndex)) →
      Runtime.Supported result → RuntimeReady (.matchList hs coverage patterns bodies subs)
  | matchBool {actuals : Nat → BoundsTy}
      {hs : ScopedDerives types slots ids rows Δ env scrut (.custom boolTyName [])}
      (coverage : BoolBranches.Covers branches)
      (patterns : ∀ br ∈ branches, BoolBranches.Pattern br.1)
      (bodies : ∀ i br, branches[i]? = some br →
        ScopedDerives types slots ids rows Δ env br.2 (actuals i))
      (subs : ∀ i br, branches[i]? = some br → SemanticSub Δ (actuals i) result) :
      RuntimeReady hs → (∀ i br atIndex, RuntimeReady (bodies i br atIndex)) →
      Runtime.Supported result → RuntimeReady (.matchBool hs coverage patterns bodies subs)
  | matchPair {actuals : Nat → BoundsTy}
      {hs : ScopedDerives types slots ids rows Δ env scrut (.custom pairTyName [left, right])}
      (coverage : PairBranches.Covers branches)
      (patterns : ∀ br ∈ branches, PairBranches.Pattern br.1)
      (bodies : ∀ i br, branches[i]? = some br →
        ScopedDerives types slots ids rows Δ (pairBranchEnv br.1 left right env)
          br.2 (actuals i))
      (subs : ∀ i br, branches[i]? = some br → SemanticSub Δ (actuals i) result) :
      RuntimeReady hs → (∀ i br atIndex, RuntimeReady (bodies i br atIndex)) →
      Runtime.Supported result → RuntimeReady (.matchPair hs coverage patterns bodies subs)

theorem RuntimeReady.supported {types slots ids rows Δ env e β}
    {h : ScopedDerives types slots ids rows Δ env e β} (ready : RuntimeReady h) :
    Runtime.Supported β := by
  induction ready with
  | literal => rename_i p; cases p <;> exact .prim
  | primBinOp => rename_i op; cases op <;> exact .arrow .prim (.arrow .prim (by first | exact .prim | exact .bool))
  | nil elem => exact .list elem
  | boolCtor => exact .bool
  | cons _ _ _ _ tail => cases tail with | list elem => exact .list elem
  | pair _ _ left right => exact .pair left right
  | varMono _ support | varRecursive _ _ support | varExported _ _ support _ => exact support
  | app _ _ _ fn _ => cases fn with | arrow _ result => exact result
  | lambda _ param _ result => exact .arrow param result
  | letMono _ _ _ _ body => exact body
  | matchList _ _ _ _ _ _ result => exact result
  | matchBool _ _ _ _ _ _ result => exact result
  | matchPair _ _ _ _ _ _ result => exact result

/-- Fundamental theorem for the supported ordinary RHS rules. Recursive
    variables are justified by a realizing environment, NOT by their declared
    contract alone. Group introduction must construct that environment. -/
theorem RuntimeReady.termAt {types slots ids rows Δ env expr β}
    {h : ScopedDerives types slots ids rows Δ env expr β} (ready : RuntimeReady h)
    (bound free : Runtime.TypeEnv) (σ : Assign)
    (hb : Runtime.TypeEnv.Downward bound) (hf : Runtime.TypeEnv.Downward free) :
    ∀ budget, (∀ p ∈ Δ, p.Holds σ) → (e : EnvAt bound free σ budget env) →
      Runtime.TermAt bound free σ budget β (expr.substN 0 e.terms) := by
  induction ready with
  | literal =>
      intro budget _ e
      exact Runtime.TermAt.value (.primLit _) (Runtime.ValueAt.literal bound free σ budget _)
  | primBinOp =>
      intro budget _ e
      exact Runtime.TermAt.value (.primBinOp _) (Runtime.ValueAt.primBinOp bound free σ budget _)
  | nil _ =>
      intro budget _ e
      exact Runtime.TermAt.value (.ctor _) (Runtime.ValueAt.nil bound free σ budget _)
  | boolCtor nameOK =>
      intro budget _ e
      exact Runtime.TermAt.value (.ctor _) (Runtime.ValueAt.bool bound free σ budget _ nameOK)
  | cons sub headReady tailReady ihh iht =>
      intro budget premises e
      have tailSupport := tailReady.supported
      cases tailSupport with
      | list elemSupport =>
          exact Runtime.TermAt.cons hb hf
            ((ihh budget premises e).of_values (Runtime.subtype sub headReady.supported elemSupport bound free σ premises))
            (iht budget premises e)
  | pair leftReady rightReady ihLeft ihRight =>
      intro budget premises e
      exact Runtime.TermAt.pair hb hf (ihLeft budget premises e) (ihRight budget premises e)
  | varMono lookup _ =>
      intro budget _ e
      exact e.varMono lookup
  | varRecursive lookup used _ =>
      intro budget premises e
      exact e.varRecursive lookup used premises
  | varExported lookup used _ arguments =>
      intro budget premises e
      exact e.varExported lookup used arguments premises
  | app sub fnReady argReady ihf iha =>
      intro budget premises e
      have fnSupport := fnReady.supported
      cases fnSupport with
      | arrow domainSupport _ =>
          exact Runtime.TermAt.app hb hf (ihf budget premises e)
            ((iha budget premises e).of_values
              (Runtime.subtype sub argReady.supported domainSupport bound free σ premises))
  | lambda annOK _ bodyReady ih =>
      intro budget premises e
      apply Runtime.TermAt.value (.lambda _ _)
      apply Runtime.ValueAt.lambda
      · exact e.closes (.lambda annOK (by assumption))
      · intro j before arg argument
        have facts := argument
        rw [Runtime.ValueAt.eq_def] at facts
        let opened := (e.down hb hf (by omega : j ≤ budget)).extendMono _ arg facts.2.1
          (Runtime.TermAt.value facts.1 (argument.down hb hf (by omega)))
        have bodySafe := ih j premises opened
        change Runtime.TermAt bound free σ j _ (Expr.substN 0 (arg :: e.terms) _) at bodySafe
        rw [Runtime.closing_singleton e.terms e.closed arg facts.2.1]
        exact bodySafe
  | letMono annOK rhsReady bodyReady ihr ihb =>
      intro budget premises e
      cases budget with
      | zero => unfold Runtime.TermAt; intro steps v _ before; omega
      | succ j =>
          have rhsClosed := e.closes (by assumption)
          let opened := (e.down hb hf (by omega : j ≤ j + 1)).extendMono _ _ rhsClosed
            (ihr j premises (e.down hb hf (by omega)))
          have bodySafe := ihb j premises opened
          apply Runtime.TermAt.prepend SmallStep.Step.letReduce
          change Runtime.TermAt bound free σ j _ (Expr.substN 0 (_ :: e.terms) _) at bodySafe
          rw [Runtime.closing_singleton e.terms e.closed _ rhsClosed]
          exact bodySafe
  | matchList coverage patterns bodies subs scrutReady branchReady resultSupport ihs ihb =>
      rename_i pathΔ branchEnv' scrut lo hi elem branches result actuals hs
      intro budget premises e
      rw [Runtime.closing_match]
      apply Runtime.TermAt.matchList (ihs budget premises e)
        (Runtime.listCoverage_close coverage e.terms) premises
      intro j before v len name args pat closedBody list contained applied selected
      obtain ⟨body, original, rfl⟩ := Runtime.firstMatch_unclose e.terms selected
      obtain ⟨i, atIndex⟩ := List.mem_iff_getElem?.mp original.mem
      obtain ⟨refined, opened, terms⟩ := (e.down hb hf (by omega : j ≤ budget)).listBranch
        hb hf list contained applied original (patterns _ original.mem)
      have path : ∀ p ∈ pathΔ ++ RecursiveTyping.branchRefine pat lo hi, p.Holds σ := by
        intro p member
        rcases List.mem_append.mp member with outer | localPath
        · exact premises p outer
        · exact refined p localPath
      have branchSafe := (ihb i (pat, body) atIndex j path opened).of_values
        (Runtime.subtype (subs i (pat, body) atIndex) (branchReady i _ atIndex).supported
          resultSupport bound free σ path)
      rw [terms] at branchSafe
      have contentsLength : (args.take pat.bindCount).length = pat.bindCount := by
        have arity := opened.arity
        rw [terms, List.length_append] at arity
        change (args.take pat.bindCount).length + e.terms.length =
          (branchEnv pat lo hi elem branchEnv').length at arity
        rw [e.arity] at arity
        rcases patterns _ original.mem with rfl | rfl | rfl <;>
          simp [branchEnv, MatchPattern.bindCount, nilCtorName, consCtorName] at arity ⊢ <;> omega
      have contentsClosed : ∀ term ∈ args.take pat.bindCount, term.varsBelow 0 = true := by
        intro term member
        exact opened.closed term (by rw [terms]; exact List.mem_append_left _ member)
      have closing := Runtime.closing_compose e.terms (args.take pat.bindCount) e.closed contentsClosed body 0
      simp only [Nat.zero_add, contentsLength] at closing
      rw [closing]
      exact branchSafe
  | matchBool coverage patterns bodies subs scrutReady branchReady resultSupport ihs ihb =>
      intro budget premises e
      rw [Runtime.closing_match]
      apply Runtime.TermAt.matchBool (ihs budget premises e)
        (Runtime.boolCoverage_close coverage e.terms)
      intro j before name pat closedBody nameOK selected
      obtain ⟨body, original, rfl⟩ := Runtime.firstMatch_unclose e.terms selected
      obtain ⟨i, atIndex⟩ := List.mem_iff_getElem?.mp original.mem
      have zero : pat.bindCount = 0 := by
        rcases patterns _ original.mem with rfl | rfl | rfl <;> rfl
      simp only [zero, List.take_zero]
      rw [Expr.substN_of_closed (e.closes (bodies i (pat, body) atIndex))]
      exact (ihb i (pat, body) atIndex j premises (e.down hb hf (by omega))).of_values
        (Runtime.subtype (subs i (pat, body) atIndex) (branchReady i _ atIndex).supported
          resultSupport bound free σ premises)
  | matchPair coverage patterns bodies subs scrutReady branchReady resultSupport ihs ihb =>
      rename_i pathΔ branchEnv' scrut leftTy rightTy branches result actuals hs
      intro budget premises e
      rw [Runtime.closing_match]
      apply Runtime.TermAt.matchPair (ihs budget premises e)
        (Runtime.pairCoverage_close coverage e.terms)
      intro j before left right pat closedBody leftMeaning rightMeaning selected
      obtain ⟨body, original, rfl⟩ := Runtime.firstMatch_unclose e.terms selected
      obtain ⟨i, atIndex⟩ := List.mem_iff_getElem?.mp original.mem
      obtain ⟨opened, terms⟩ := (e.down hb hf (by omega : j ≤ budget)).pairBranch
        hb hf leftMeaning rightMeaning (patterns _ original.mem)
      have branchSafe := (ihb i (pat, body) atIndex j premises opened).of_values
        (Runtime.subtype (subs i (pat, body) atIndex) (branchReady i _ atIndex).supported
          resultSupport bound free σ premises)
      rw [terms] at branchSafe
      have contentsLength : ([left, right].take pat.bindCount).length = pat.bindCount := by
        have arity := opened.arity
        rw [terms, List.length_append] at arity
        change ([left, right].take pat.bindCount).length + e.terms.length =
          (pairBranchEnv pat leftTy rightTy branchEnv').length at arity
        rw [e.arity] at arity
        rcases patterns _ original.mem with rfl | rfl <;>
          simp [pairBranchEnv, MatchPattern.bindCount] at arity ⊢ <;> omega
      have contentsClosed : ∀ term ∈ [left, right].take pat.bindCount,
          term.varsBelow 0 = true := by
        intro term member
        exact opened.closed term (by rw [terms]; exact List.mem_append_left _ member)
      have closing := Runtime.closing_compose e.terms ([left, right].take pat.bindCount)
        e.closed contentsClosed body 0
      simp only [Nat.zero_add, contentsLength] at closing
      rw [closing]
      exact branchSafe

#print axioms RuntimeReady.supported
#print axioms RuntimeReady.termAt

theorem RuntimeReady.safeClosed {types slots ids rows Δ expr β}
    {h : ScopedDerives types slots ids rows Δ [] expr β} (ready : RuntimeReady h)
    (bound free : Runtime.TypeEnv) (σ : Assign)
    (hb : Runtime.TypeEnv.Downward bound) (hf : Runtime.TypeEnv.Downward free)
    (premises : ∀ p ∈ Δ, p.Holds σ) : Runtime.Safe bound free σ β expr := by
  intro budget
  let empty : EnvAt bound free σ budget [] :=
    ⟨[], rfl, by simp, by intro i inside; simp at inside⟩
  have safe := ready.termAt bound free σ hb hf budget premises empty
  simpa only [Expr.substN_of_closed h.varsBelow] using safe

#print axioms RuntimeReady.safeClosed

/-- Actual erased group introduction, once ALL member implementations establish
    their runtime obligations. This connects simultaneous cyclic realization to
    the existing fundamental theorem and Core's single unfolding rule. -/
theorem RuntimeReady.safeGroup {types slots ids rows Δ env body β}
    {h : ScopedDerives types slots ids rows Δ env body β} (ready : RuntimeReady h)
    (bound free : Runtime.TypeEnv) (σ : Assign)
    (hb : Runtime.TypeEnv.Downward bound) (hf : Runtime.TypeEnv.Downward free)
    (annotations : List (Option PolyTy)) (rhss : List Expr)
    (arity : rhss.length = env.length)
    (scope : ∀ rhs ∈ rhss, rhs.varsBelow rhss.length = true)
    (rhsSafe : ∀ budget (e : EnvAt bound free σ budget env) i (inside : i < env.length),
      BindingAt bound free σ budget env[i]
        (rhss[i]'(by rw [arity]; exact inside) |>.substN 0 e.terms))
    (premises : ∀ p ∈ Δ, p.Holds σ) :
    Runtime.Safe bound free σ β (.letRec annotations rhss body) := by
  intro budget
  cases budget with
  | zero => unfold Runtime.TermAt; intro steps v _ before; omega
  | succ budget =>
      let realized := EnvAt.tieGroup annotations rhss arity scope rhsSafe budget
      have bodySafe := ready.termAt bound free σ hb hf budget premises realized.val
      rw [realized.property] at bodySafe
      exact Runtime.TermAt.prepend SmallStep.Step.letRecUnfold bodySafe

#print axioms RuntimeReady.safeGroup

end ScopedDerives


namespace Derives
abbrev literal {types : Nat → BoundsTy} := @ScopedDerives.literal types BoundsTy.bvar
abbrev primBinOp {types : Nat → BoundsTy} := @ScopedDerives.primBinOp types BoundsTy.bvar
abbrev nil {types : Nat → BoundsTy} := @ScopedDerives.nil types BoundsTy.bvar
abbrev boolCtor {types : Nat → BoundsTy} := @ScopedDerives.boolCtor types BoundsTy.bvar
abbrev cons {types : Nat → BoundsTy} := @ScopedDerives.cons types BoundsTy.bvar
abbrev pair {types : Nat → BoundsTy} := @ScopedDerives.pair types BoundsTy.bvar
abbrev varMono {types : Nat → BoundsTy} := @ScopedDerives.varMono types BoundsTy.bvar
abbrev varRecursive {types : Nat → BoundsTy} := @ScopedDerives.varRecursive types BoundsTy.bvar
abbrev varExported {types : Nat → BoundsTy} := @ScopedDerives.varExported types BoundsTy.bvar
abbrev app {types : Nat → BoundsTy} := @ScopedDerives.app types BoundsTy.bvar
abbrev lambda {types : Nat → BoundsTy} := @ScopedDerives.lambda types BoundsTy.bvar
abbrev letMono {types : Nat → BoundsTy} := @ScopedDerives.letMono types BoundsTy.bvar
abbrev matchList {types : Nat → BoundsTy} := @ScopedDerives.matchList types BoundsTy.bvar
abbrev matchBool {types : Nat → BoundsTy} := @ScopedDerives.matchBool types BoundsTy.bvar
abbrev matchPair {types : Nat → BoundsTy} := @ScopedDerives.matchPair types BoundsTy.bvar
abbrev matchOpaque {types : Nat → BoundsTy} := @ScopedDerives.matchOpaque types BoundsTy.bvar
end Derives

/-- Shared source-parameter obligation transport for RHS and body judgments. -/
theorem param_assuming {types slots ids rows Δ Δ' ann β}
    (h : ScopedHMAnnotation.ParamOK types slots ids rows Δ ann β)
    (hp : (⟨Δ', Δ⟩ : ForallProblem).Valid) :
    ScopedHMAnnotation.ParamOK types slots ids rows Δ' ann β := by
  cases ann with
  | none => trivial
  | some τ => exact h.assuming hp

/-- Shared source mono-binding obligation transport; forall guards remain intact. -/
theorem binding_assuming {types slots ids rows Δ Δ' ann β}
    (h : ScopedHMAnnotation.BindingOK types slots ids rows Δ ann β)
    (hp : (⟨Δ', Δ⟩ : ForallProblem).Valid) :
    ScopedHMAnnotation.BindingOK types slots ids rows Δ' ann β := by
  cases ann with
  | none => trivial
  | some σ => exact ⟨h.1, h.2.assuming hp⟩

/-- A caller must establish instantiated contract premises. Transport the
    entire actual RHS, including nested source obligations and refined arms,
    into that caller context rather than silently appending assumptions. -/
theorem ScopedDerives.assuming {types slots ids rows Δ Δ' env e β}
    (h : ScopedDerives types slots ids rows Δ env e β)
    (hp : (⟨Δ', Δ⟩ : ForallProblem).Valid) : ScopedDerives types slots ids rows Δ' env e β := by
  induction h generalizing Δ' with
  | literal => exact .literal
  | primBinOp => exact .primBinOp
  | nil => exact .nil
  | boolCtor hn => exact .boolCtor hn
  | ctor hn => exact .ctor hn
  | cons _ _ hs ihh iht => exact .cons (ihh hp) (iht hp) (hs.assuming hp)
  | pair _ _ ihLeft ihRight => exact .pair (ihLeft hp) (ihRight hp)
  | varMono hv => exact .varMono hv
  | varRecursive hv used =>
      let next : RecursiveHMContract.Use _ Δ' _ _ :=
        ⟨used.counts, used.inst, by
          intro σ hΔ goal hgoal
          exact used.usable σ (fun c hc => hp σ hΔ c hc) goal hgoal,
          used.typesScoped, used.fixedHM⟩
      exact .varRecursive hv next
  | varExported hv used =>
      let next : HMCountScheme.Use _ Δ' _ _ :=
        ⟨used.counts, used.countInstance, by
          intro σ hΔ goal hgoal
          exact used.usable σ (fun c hc => hp σ hΔ c hc) goal hgoal,
          used.types, used.arity, used.typesLC, used.typesScoped, used.shape⟩
      exact .varExported hv next
  | app _ _ hs ihh iht => exact .app (ihh hp) (iht hp) (hs.assuming hp)
  | lambda hparam _ ih => exact .lambda (param_assuming hparam hp) (ih hp)
  | letMono hbind _ _ ihr ihb => exact .letMono (binding_assuming hbind hp) (ihr hp) (ihb hp)
  | matchList _ hc hpat _ hsub ihscrut ihbranches =>
      exact .matchList (ihscrut hp) (hc.assuming hp) hpat
        (fun i br hb => ihbranches i br hb (RecursiveTyping.assuming_append hp))
        (fun i br hb => (hsub i br hb).assuming (RecursiveTyping.assuming_append hp))
  | matchBool _ hc hpat _ hsub ihscrut ihbranches =>
      exact .matchBool (ihscrut hp) hc hpat
        (fun i br hb => ihbranches i br hb hp)
        (fun i br hb => (hsub i br hb).assuming hp)
  | matchPair _ hc hpat _ hsub ihscrut ihbranches =>
      exact .matchPair (ihscrut hp) hc hpat
        (fun i br hb => ihbranches i br hb hp)
        (fun i br hb => (hsub i br hb).assuming hp)
  | matchNominal fieldss actuals _ coverage fields bodies subs ihscrut ihbranches =>
      exact .matchNominal fieldss actuals (ihscrut hp) coverage fields
        (fun i br hb => ihbranches i br hb hp)
        (fun i br hb => (subs i br hb).assuming hp)
  | matchOpaque _ hpat _ hsub ihscrut ihbranches =>
      exact .matchOpaque (ihscrut hp) hpat
        (fun i br hb => ihbranches i br hb hp)
        (fun i br hb => (hsub i br hb).assuming hp)

/-- Established caller/path assumptions preserve the supported proof fragment,
    including every selected-arm intermediate type. This accompanies the
    existing whole-derivation transport; it makes no new solver request. -/
theorem ScopedDerives.RuntimeReady.assuming {types slots ids rows Δ Δ' env e β}
    {h : ScopedDerives types slots ids rows Δ env e β} (ready : ScopedDerives.RuntimeReady h)
    (hp : (⟨Δ', Δ⟩ : ForallProblem).Valid) : ScopedDerives.RuntimeReady (h.assuming hp) := by
  induction ready generalizing Δ' with
  | literal => exact .literal
  | primBinOp => exact .primBinOp
  | nil support => exact .nil support
  | boolCtor nameOK => exact .boolCtor nameOK
  | cons sub _ _ ihh iht => exact .cons (sub.assuming hp) (ihh hp) (iht hp)
  | pair _ _ ihLeft ihRight => exact .pair (ihLeft hp) (ihRight hp)
  | varMono lookup support => exact .varMono lookup support
  | varRecursive lookup used support =>
      let next : RecursiveHMContract.Use _ Δ' _ _ :=
        ⟨used.counts, used.inst, fun σ premises => used.usable σ (hp σ premises),
          used.typesScoped, used.fixedHM⟩
      exact .varRecursive lookup next support
  | varExported lookup used support arguments =>
      let next : HMCountScheme.Use _ Δ' _ _ :=
        ⟨used.counts, used.countInstance, (fun σ hΔ => used.usable σ (hp σ hΔ)),
          used.types, used.arity, used.typesLC, used.typesScoped, used.shape⟩
      exact .varExported lookup next support arguments
  | app sub _ _ ihf iha => exact .app (sub.assuming hp) (ihf hp) (iha hp)
  | lambda annotation support _ ih =>
      exact .lambda (param_assuming annotation hp) support (ih hp)
  | letMono annotation _ _ ihr ihb =>
      exact .letMono (binding_assuming annotation hp) (ihr hp) (ihb hp)
  | matchList coverage patterns bodies subs _ _ support ihs ihb =>
      exact .matchList (coverage.assuming hp) patterns
        (fun i br atIndex => (bodies i br atIndex).assuming (RecursiveTyping.assuming_append hp))
        (fun i br atIndex => (subs i br atIndex).assuming (RecursiveTyping.assuming_append hp))
        (ihs hp) (fun i br atIndex => ihb i br atIndex (RecursiveTyping.assuming_append hp)) support
  | matchBool coverage patterns bodies subs _ _ support ihs ihb =>
      exact .matchBool coverage patterns
        (fun i br atIndex => (bodies i br atIndex).assuming hp)
        (fun i br atIndex => (subs i br atIndex).assuming hp)
        (ihs hp) (fun i br atIndex => ihb i br atIndex hp) support
  | matchPair coverage patterns bodies subs _ _ support ihs ihb =>
      exact .matchPair coverage patterns
        (fun i br atIndex => (bodies i br atIndex).assuming hp)
        (fun i br atIndex => (subs i br atIndex).assuming hp)
        (ihs hp) (fun i br atIndex => ihb i br atIndex hp) support

#print axioms ScopedDerives.RuntimeReady.assuming

theorem ScopedDerives.RuntimeReady.sourceFree {types types' slots : Nat → BoundsTy} {ids rows Δ env e β}
    {h : ScopedDerives types slots ids rows Δ env e β} (ready : ScopedDerives.RuntimeReady h) :
    ∀ agree : ∀ i ∈ e.tyFreeVars, types i = types' i,
      ScopedDerives.RuntimeReady (h.sourceFree agree) := by
  induction ready with
  | literal => intro _; exact .literal
  | primBinOp => intro _; exact .primBinOp
  | nil supported => intro _; exact .nil supported
  | boolCtor ctor => intro _; exact .boolCtor ctor
  | varMono lookup supported => intro _; exact .varMono lookup supported
  | varRecursive lookup used supported => intro _; exact .varRecursive lookup used supported
  | varExported lookup used supported arguments =>
      intro _; exact .varExported lookup used supported arguments
  | cons sub _ _ ihh iht =>
      intro agree
      exact .cons sub (ihh (fun i hi => agree i (by simp [Expr.tyFreeVars, hi])))
        (iht (fun i hi => agree i (by simp [Expr.tyFreeVars, hi])))
  | pair _ _ ihLeft ihRight =>
      intro agree
      exact .pair (ihLeft (fun i hi => agree i (by simp [Expr.tyFreeVars, hi])))
        (ihRight (fun i hi => agree i (by simp [Expr.tyFreeVars, hi])))
  | app sub _ _ ihf iha =>
      intro agree
      exact .app sub (ihf (fun i hi => agree i (by simp [Expr.tyFreeVars, hi])))
        (iha (fun i hi => agree i (by simp [Expr.tyFreeVars, hi])))
  | lambda annotation supported _ ih =>
      intro agree
      exact .lambda
        (ScopedHMAnnotation.ParamOK.congrFree annotation
          (fun i hi => agree i (by simp [Expr.tyFreeVars, hi])))
        supported (ih (fun i hi => agree i (by simp [Expr.tyFreeVars, hi])))
  | letMono annotation _ _ ihr ihb =>
      intro agree
      exact .letMono
        (ScopedHMAnnotation.BindingOK.congrFree annotation
          (fun i hi => agree i (by simp [Expr.tyFreeVars, hi])))
        (ihr (fun i hi => agree i (by simp [Expr.tyFreeVars, hi])))
        (ihb (fun i hi => agree i (by simp [Expr.tyFreeVars, hi])))
  | matchList coverage patterns bodies subs _ _ supported ihs ihb =>
      intro agree
      refine .matchList coverage patterns
        (fun index br atIndex => (bodies index br atIndex).sourceFree (fun i hi => agree i
          (List.mem_append_right _ (branch_typeFree (List.mem_of_getElem? atIndex) hi))))
        subs (ihs (fun i hi => agree i (by simp [Expr.tyFreeVars, hi]))) ?_ supported
      intro index br atIndex
      exact ihb index br atIndex (fun i hi => agree i
        (List.mem_append_right _ (branch_typeFree (List.mem_of_getElem? atIndex) hi)))
  | matchBool coverage patterns bodies subs _ _ supported ihs ihb =>
      intro agree
      refine .matchBool coverage patterns
        (fun index br atIndex => (bodies index br atIndex).sourceFree (fun i hi => agree i
          (List.mem_append_right _ (branch_typeFree (List.mem_of_getElem? atIndex) hi))))
        subs (ihs (fun i hi => agree i (by simp [Expr.tyFreeVars, hi]))) ?_ supported
      intro index br atIndex
      exact ihb index br atIndex (fun i hi => agree i
        (List.mem_append_right _ (branch_typeFree (List.mem_of_getElem? atIndex) hi)))
  | matchPair coverage patterns bodies subs _ _ supported ihs ihb =>
      intro agree
      refine .matchPair coverage patterns
        (fun index br atIndex => (bodies index br atIndex).sourceFree (fun i hi => agree i
          (List.mem_append_right _ (branch_typeFree (List.mem_of_getElem? atIndex) hi))))
        subs (ihs (fun i hi => agree i (by simp [Expr.tyFreeVars, hi]))) ?_ supported
      intro index br atIndex
      exact ihb index br atIndex (fun i hi => agree i
        (List.mem_append_right _ (branch_typeFree (List.mem_of_getElem? atIndex) hi)))

#print axioms ScopedDerives.RuntimeReady.sourceFree

theorem ScopedDerives.RuntimeReady.sourceSlots {types slots slots' : Nat → BoundsTy}
    {ids rows Δ env e β n} {h : ScopedDerives types slots ids rows Δ env e β}
    (ready : ScopedDerives.RuntimeReady h) (agree : ∀ i < n, slots i = slots' i) :
    ∀ bounded : e.TyBvarBounded n,
      ScopedDerives.RuntimeReady (h.sourceSlots bounded agree) := by
  induction ready with
  | literal => intro _; exact .literal
  | primBinOp => intro _; exact .primBinOp
  | nil supported => intro _; exact .nil supported
  | boolCtor ctor => intro _; exact .boolCtor ctor
  | varMono lookup supported => intro _; exact .varMono lookup supported
  | varRecursive lookup used supported => intro _; exact .varRecursive lookup used supported
  | varExported lookup used supported arguments =>
      intro _; exact .varExported lookup used supported arguments
  | cons sub _ _ ihh iht =>
      intro bounded
      simp only [Expr.TyBvarBounded] at bounded
      exact .cons sub (ihh bounded.1.2) (iht bounded.2)
  | pair _ _ ihLeft ihRight =>
      intro bounded
      simp only [Expr.TyBvarBounded] at bounded
      exact .pair (ihLeft bounded.1.2) (ihRight bounded.2)
  | app sub _ _ ihf iha =>
      intro bounded
      exact .app sub (ihf bounded.1) (iha bounded.2)
  | lambda annotation supported _ ih =>
      intro bounded
      exact .lambda (ScopedHMAnnotation.ParamOK.congrSlots annotation bounded.1 agree)
        supported (ih bounded.2)
  | letMono annotation _ _ ihr ihb =>
      intro bounded
      have moved := letMono_sourceSlots annotation bounded agree
      exact .letMono moved.1 (ihr moved.2.1) (ihb moved.2.2)
  | matchList coverage patterns bodies subs _ _ supported ihs ihb =>
      intro bounded
      refine .matchList coverage patterns
        (fun index br atIndex => (bodies index br atIndex).sourceSlots
          (Expr.TyBvarBounded.BranchList_iff.mp bounded.2 br.1 br.2
            (List.mem_of_getElem? atIndex)) agree)
        subs (ihs bounded.1) ?_ supported
      intro index br atIndex
      exact ihb index br atIndex
        (Expr.TyBvarBounded.BranchList_iff.mp bounded.2 br.1 br.2
          (List.mem_of_getElem? atIndex))
  | matchBool coverage patterns bodies subs _ _ supported ihs ihb =>
      intro bounded
      refine .matchBool coverage patterns
        (fun index br atIndex => (bodies index br atIndex).sourceSlots
          (Expr.TyBvarBounded.BranchList_iff.mp bounded.2 br.1 br.2
            (List.mem_of_getElem? atIndex)) agree)
        subs (ihs bounded.1) ?_ supported
      intro index br atIndex
      exact ihb index br atIndex
        (Expr.TyBvarBounded.BranchList_iff.mp bounded.2 br.1 br.2
          (List.mem_of_getElem? atIndex))
  | matchPair coverage patterns bodies subs _ _ supported ihs ihb =>
      intro bounded
      refine .matchPair coverage patterns
        (fun index br atIndex => (bodies index br atIndex).sourceSlots
          (Expr.TyBvarBounded.BranchList_iff.mp bounded.2 br.1 br.2
            (List.mem_of_getElem? atIndex)) agree)
        subs (ihs bounded.1) ?_ supported
      intro index br atIndex
      exact ihb index br atIndex
        (Expr.TyBvarBounded.BranchList_iff.mp bounded.2 br.1 br.2
          (List.mem_of_getElem? atIndex))

#print axioms ScopedDerives.RuntimeReady.sourceSlots

def Contract.mapTypes (c : Contract) (f : Nat → BoundsTy)
    (hf : ∀ i, (Synth.BoundsTy.toTy (f i)).IsLC) : Contract :=
  ⟨c.template, Synth.BoundsTy.toTy (HMCountScheme.opened c.template (c.fixed.types.map (mapFree f))),
    c.fixed.mapTypes f hf⟩

def mapBinding (f : Nat → BoundsTy) (hf : ∀ i, (Synth.BoundsTy.toTy (f i)).IsLC) : Binding → Binding
  | .mono β => .mono (mapFree f β)
  | .recursive c => .recursive (c.mapTypes f hf)
  | .exported s => .exported s

def CapturesFixed (f : Nat → BoundsTy) (env : List Binding) : Prop :=
  ∀ b ∈ env, match b with
    | .mono _ => True
    | .recursive c => ∀ i ∈ c.template.hm.body.freeVars, f i = .fvar i
    | .exported s => ∀ i ∈ s.hm.body.freeVars, f i = .fvar i

theorem CapturesFixed.recursive {f env c} (h : CapturesFixed f env)
    (member : .recursive c ∈ env) :
    ∀ i ∈ c.template.hm.body.freeVars, f i = .fvar i := h _ member

theorem CapturesFixed.exported {f env s} (h : CapturesFixed f env)
    (member : .exported s ∈ env) :
    ∀ i ∈ s.hm.body.freeVars, f i = .fvar i := h _ member

private theorem captures_cons {f env β} (h : CapturesFixed f env) : CapturesFixed f (.mono β :: env) := by
  intro b hb
  rcases List.mem_cons.mp hb with head | rest
  · cases head; trivial
  · exact h b rest

private theorem captures_branch {f env p lo hi elem} (h : CapturesFixed f env) :
    CapturesFixed f (branchEnv p lo hi elem env) := by
  unfold branchEnv
  split
  · exact captures_cons (captures_cons h)
  · exact h

private theorem captures_pairBranch {f env p left right} (h : CapturesFixed f env) :
    CapturesFixed f (pairBranchEnv p left right env) := by
  unfold pairBranchEnv
  split
  · exact captures_cons (captures_cons h)
  · exact h

private theorem captures_monos {f env} (h : CapturesFixed f env)
    (fields : List BoundsTy) :
    CapturesFixed f (fields.map Binding.mono ++ env) := by
  induction fields with
  | nil => simpa using h
  | cons field rest ih =>
      simpa only [List.map_cons, List.cons_append] using captures_cons ih

/-- Enlarge caller count scope without changing the instance, its bounds or
    raw premises. Shared group arguments may mention counts unused by one member. -/
def weakenInstance {s args caller} (inst : ScopedScheme.Instance s args caller) (target : List Nat) :
    ScopedScheme.Instance s args (caller ++ target) :=
  { wf := inst.wf, arity := inst.arity, finiteArgs := inst.finiteArgs
    argsScoped := fun a ha => count_mono (inst.argsScoped a ha) (fun _ hi => List.mem_append_left _ hi)
    capturesScoped := fun i hi => List.mem_append_left _ (inst.capturesScoped i hi)
    bodyScoped := scope_mono inst.bodyScoped (fun _ hi => List.mem_append_left _ hi)
    premisesScoped := fun c hc =>
      ⟨count_mono (inst.premisesScoped c hc).1 (fun _ hi => List.mem_append_left _ hi),
        count_mono (inst.premisesScoped c hc).2 (fun _ hi => List.mem_append_left _ hi)⟩ }

private def mapUse {c : Contract} {Δ caller} (u : RecursiveHMContract.Use c.fixed Δ c.hm caller)
    (f : Nat → BoundsTy) (hf : ∀ i, (Synth.BoundsTy.toTy (f i)).IsLC) (target : List Nat)
    (scope : ∀ i, ScopedScheme.BoundsScoped target (f i)) :
    RecursiveHMContract.Use (c.mapTypes f hf).fixed Δ (c.mapTypes f hf).hm (caller ++ target) := by
  refine ⟨u.counts, weakenInstance u.inst target, u.usable, ?_, rfl⟩
  apply List.all_eq_true.mpr
  intro a ha
  obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
  exact ScopedScheme.boundsScopedBool_complete
    (map_scope (ScopedScheme.boundsScopedBool_sound (List.all_eq_true.mp u.typesScoped b hb)) f scope)

private theorem mapUse_bounds {c : Contract} {Δ caller} (u : RecursiveHMContract.Use c.fixed Δ c.hm caller)
    (f : Nat → BoundsTy) (hf : ∀ i, (Synth.BoundsTy.toTy (f i)).IsLC) (target : List Nat)
    (scope : ∀ i, ScopedScheme.BoundsScoped target (f i))
    (captured : ∀ i ∈ c.template.hm.body.freeVars, f i = .fvar i) :
    (mapUse u f hf target scope).bounds = mapFree f u.bounds :=
  (RecursiveHMContract.map_combined c.template c.fixed.types _ f hf captured).symm

private def mapExportedUse {s : HMCountScheme.Scheme} {Δ found caller}
    (u : HMCountScheme.Use s Δ found caller)
    (f : Nat → BoundsTy) (hf : ∀ i, (Synth.BoundsTy.toTy (f i)).IsLC)
    (target : List Nat) (scope : ∀ i, ScopedScheme.BoundsScoped target (f i))
    (captured : ∀ i ∈ s.hm.body.freeVars, f i = .fvar i) :
    HMCountScheme.Use s Δ (Synth.BoundsTy.toTy (mapFree f u.bounds)) (caller ++ target) := by
  refine ⟨u.counts, weakenInstance u.countInstance target, u.usable,
    u.types.map (mapFree f), by simpa using u.arity, ?_, ?_, ?_⟩
  · intro a ha
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
    exact FreeAlgebra.bvars f hf (u.typesLC b hb)
  · apply List.all_eq_true.mpr
    intro a ha
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
    exact ScopedScheme.boundsScopedBool_complete
      (map_scope (ScopedScheme.boundsScopedBool_sound
        (List.all_eq_true.mp u.typesScoped b hb)) f scope)
  · rw [FreeAlgebra.shape_erased]
    exact congrArg Synth.BoundsTy.toTy
      (RecursiveHMContract.map_combined s u.types _ f hf captured).symm

private theorem mapExportedUse_bounds {s : HMCountScheme.Scheme} {Δ found caller}
    (u : HMCountScheme.Use s Δ found caller)
    (f : Nat → BoundsTy) (hf : ∀ i, (Synth.BoundsTy.toTy (f i)).IsLC)
    (target : List Nat) (scope : ∀ i, ScopedScheme.BoundsScoped target (f i))
    (captured : ∀ i ∈ s.hm.body.freeVars, f i = .fvar i) :
    (mapExportedUse u f hf target scope captured).bounds = mapFree f u.bounds :=
  (RecursiveHMContract.map_combined s u.types _ f hf captured).symm

private theorem param_types {types slots ids rows Δ ann β}
    (h : ScopedHMAnnotation.ParamOK types slots ids rows Δ ann β) (f : Nat → BoundsTy) :
    ScopedHMAnnotation.ParamOK (fun i => mapFree f (types i)) (fun i => mapFree f (slots i)) ids rows Δ ann (mapFree f β) := by
  cases ann with
  | none => trivial
  | some τ => exact h.types f

private theorem binding_types {types slots ids rows Δ ann β}
    (h : ScopedHMAnnotation.BindingOK types slots ids rows Δ ann β) (f : Nat → BoundsTy) :
    ScopedHMAnnotation.BindingOK (fun i => mapFree f (types i)) (fun i => mapFree f (slots i)) ids rows Δ ann (mapFree f β) := by
  cases ann with
  | none => trivial
  | some σ => exact ⟨h.1, h.2.types f⟩

/-- Full RHS HM transport, including annotated lambdas, lets, recursive calls
    and all match arms. One map interprets the whole source derivation. -/
theorem transportScopedTypes (f : Nat → BoundsTy) (hf : ∀ i, (Synth.BoundsTy.toTy (f i)).IsLC)
    (target : List Nat) (scope : ∀ i, ScopedScheme.BoundsScoped target (f i))
    {types slots ids rows Δ env e β} (h : ScopedDerives types slots ids rows Δ env e β)
    (fresh : CapturesFixed f env) :
    ScopedDerives (fun i => mapFree f (types i)) (fun i => mapFree f (slots i)) ids rows Δ (env.map (mapBinding f hf)) e (mapFree f β) := by
  induction h with
  | literal => cases ‹PrimLitExpr› <;> exact .literal
  | primBinOp => cases ‹PrimBinOp› <;> exact .primBinOp
  | nil => exact .nil
  | boolCtor hn => exact .boolCtor hn
  | ctor hn => exact .ctor hn
  | cons _ _ hs ihh iht => exact .cons (ihh fresh) (iht fresh) (SchemeSpecialization.subtype f hs)
  | pair _ _ ihLeft ihRight => exact .pair (ihLeft fresh) (ihRight fresh)
  | varMono hv => exact .varMono (by simpa [mapBinding] using congrArg (Option.map (mapBinding f hf)) hv)
  | varRecursive hv u =>
      rw [← mapUse_bounds u f hf target scope (fresh.recursive (List.mem_of_getElem? hv))]
      exact .varRecursive (by simpa [mapBinding] using congrArg (Option.map (mapBinding f hf)) hv)
        (mapUse u f hf target scope)
  | varExported hv u =>
      have captured := fresh.exported (List.mem_of_getElem? hv)
      rw [← mapExportedUse_bounds u f hf target scope captured]
      exact .varExported
        (by simpa [mapBinding] using congrArg (Option.map (mapBinding f hf)) hv)
        (mapExportedUse u f hf target scope captured)
  | app _ _ hs ihf iha =>
      exact .app (ihf fresh) (iha fresh) (SchemeSpecialization.subtype f hs)
  | lambda hp _ ih =>
      exact .lambda (param_types hp f) (by
        simpa [mapBinding] using ih (captures_cons fresh))
  | letMono hp _ _ ihr ihb =>
      exact .letMono (binding_types hp f) (ihr fresh) (by
        simpa [mapBinding] using ihb (captures_cons fresh))
  | matchList _ hc hpat _ hsub ihscrut ihbranches =>
      apply ScopedDerives.matchList (ihscrut fresh) hc hpat
      · intro i br hb
        have ht := ihbranches i br hb (captures_branch fresh)
        by_cases hcbr : br.1 = .named consCtorName 2
        · simpa [branchEnv, hcbr, mapBinding, mapFree] using ht
        · simpa [branchEnv, hcbr] using ht
      · intro i br hb
        exact SchemeSpecialization.subtype f (hsub i br hb)
  | matchBool _ hc hpat _ hsub ihscrut ihbranches =>
      exact .matchBool (ihscrut fresh) hc hpat
        (fun i br hb => ihbranches i br hb fresh)
        (fun i br hb => SchemeSpecialization.subtype f (hsub i br hb))
  | matchPair _ hc hpat _ hsub ihscrut ihbranches =>
      apply ScopedDerives.matchPair (ihscrut fresh) hc hpat
      · intro i br hb
        have moved := ihbranches i br hb (captures_pairBranch fresh)
        by_cases hp : br.1 = .named pairCtorName 2
        · simpa [pairBranchEnv, hp, mapBinding, mapFree] using moved
        · simpa [pairBranchEnv, hp] using moved
      · intro i br hb
        exact SchemeSpecialization.subtype f (hsub i br hb)
  | matchNominal fieldss actuals _ hc fields bodies hsub ihscrut ihbranches =>
      apply ScopedDerives.matchNominal
        (fieldss := fun i => SchemeSpecialization.mapFreeList f (fieldss i))
        (actuals := fun i => SchemeSpecialization.mapFree f (actuals i))
        (ihscrut fresh) hc
      · intro i br hb
        exact (fields i br hb).types f hf
      · intro i br hb
        have moved := ihbranches i br hb (captures_monos fresh (fieldss i))
        have mappedFields :
            ((fieldss i).map Binding.mono).map (mapBinding f hf) =
              (SchemeSpecialization.mapFreeList f (fieldss i)).map Binding.mono := by
          induction (fieldss i) with
          | nil => rfl
          | cons field rest ih => simp [SchemeSpecialization.mapFreeList, mapBinding, ih]
        simpa only [List.map_append, mappedFields] using moved
      · intro i br hb
        exact SchemeSpecialization.subtype f (hsub i br hb)
  | matchOpaque _ hpat _ hsub ihscrut ihbranches =>
      exact .matchOpaque (ihscrut fresh) hpat
        (fun i br hb => ihbranches i br hb fresh)
        (fun i br hb => SchemeSpecialization.subtype f (hsub i br hb))

def Contract.mapCounts (c : Contract) (outer : Bindings) : Contract :=
  ⟨c.template, c.hm, c.fixed.mapCounts outer⟩

def mapCountBinding (outer : Bindings) : Binding → Binding
  | .mono β => .mono (bounds outer β)
  | .recursive c => .recursive (c.mapCounts outer)
  | .exported s => .exported s

def CountCapturesFixed (outer : Bindings) (env : List Binding) : Prop :=
  ∀ b ∈ env, match b with
    | .mono _ => True
    | .recursive c => ∀ i ∈ c.template.counts.captures, lookup outer i = none
    | .exported s => ∀ i ∈ s.counts.captures, lookup outer i = none

theorem CountCapturesFixed.recursive {outer env c} (h : CountCapturesFixed outer env)
    (member : .recursive c ∈ env) :
    ∀ i ∈ c.template.counts.captures, lookup outer i = none := h _ member

theorem CountCapturesFixed.exported {outer env s} (h : CountCapturesFixed outer env)
    (member : .exported s ∈ env) :
    ∀ i ∈ s.counts.captures, lookup outer i = none := h _ member

private theorem count_captures_cons {outer env β} (h : CountCapturesFixed outer env) :
    CountCapturesFixed outer (.mono β :: env) := by
  intro b hb
  rcases List.mem_cons.mp hb with head | rest
  · cases head; trivial
  · exact h b rest

private theorem count_captures_branch {outer env p lo hi elem} (h : CountCapturesFixed outer env) :
    CountCapturesFixed outer (branchEnv p lo hi elem env) := by
  unfold branchEnv
  split
  · exact count_captures_cons (count_captures_cons h)
  · exact h

private theorem count_captures_pairBranch {outer env p left right}
    (h : CountCapturesFixed outer env) :
    CountCapturesFixed outer (pairBranchEnv p left right env) := by
  unfold pairBranchEnv
  split
  · exact count_captures_cons (count_captures_cons h)
  · exact h

private theorem count_captures_monos {outer env} (h : CountCapturesFixed outer env)
    (fields : List BoundsTy) :
    CountCapturesFixed outer (fields.map Binding.mono ++ env) := by
  induction fields with
  | nil => simpa using h
  | cons field rest ih =>
      simpa only [List.map_cons, List.cons_append] using count_captures_cons ih

private def mapExportedUseCounts {s : HMCountScheme.Scheme} {Δ found caller}
    (u : HMCountScheme.Use s Δ found caller)
    (outer : Bindings) (hf : Finite outer) (target : List Nat)
    (scope : ∀ row ∈ outer, Scope.CountScoped target row.2)
    (captured : ∀ i ∈ s.counts.captures, lookup outer i = none) :
    HMCountScheme.Use s (Δ.map (constraint outer)) found (caller ++ target) := by
  refine ⟨u.counts.map (count outer),
    RecursiveCountTransport.instanceTransport u.countInstance outer hf target scope captured,
    RecursiveCountTransport.usable_transport u.countInstance u.usable outer hf target scope captured,
    u.types.map (bounds outer), by simpa using u.arity, ?_, ?_, ?_⟩
  · intro a ha
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
    rw [bounds_shape]
    exact u.typesLC b hb
  · apply List.all_eq_true.mpr
    intro a ha
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
    apply ScopedScheme.boundsScopedBool_complete
    exact ScopedScheme.bounds_scoped (ScopedScheme.boundsScopedBool_sound
      (List.all_eq_true.mp u.typesScoped b hb))
      (fun row hr => RecursiveCountTransport.scope_mono (scope row hr)
        (fun _ hi => List.mem_append_right _ hi))
      (fun _ hi _ => List.mem_append_left _ hi)
  · simpa only [TypeSubstitution.combined, TypeSubstitution.shape,
      CountTransport.vector_mapped, bounds_shape] using u.shape

private theorem mapExportedUseCounts_bounds {s : HMCountScheme.Scheme} {Δ found caller}
    (u : HMCountScheme.Use s Δ found caller)
    (outer : Bindings) (hf : Finite outer) (target : List Nat)
    (scope : ∀ row ∈ outer, Scope.CountScoped target row.2)
    (captured : ∀ i ∈ s.counts.captures, lookup outer i = none) :
    (mapExportedUseCounts u outer hf target scope captured).bounds = bounds outer u.bounds := by
  change TypeSubstitution.substitute (SchemeUse.vector (u.types.map (bounds outer)))
      (bounds (s.counts.quantified.zip (u.counts.map (count outer))) s.counts.body) =
    bounds outer (TypeSubstitution.substitute (SchemeUse.vector u.types) u.countInstance.bounds)
  rw [CountTransport.instantiate_commute,
    RecursiveCountTransport.bounds_transport u.countInstance outer captured]
  congr 1
  funext i
  exact CountTransport.vector_mapped outer u.types i

private theorem param_counts {types slots ids rows Δ ann β}
    (h : ScopedHMAnnotation.ParamOK types slots ids rows Δ ann β) (outer : Bindings) (hf : Finite outer) :
    ScopedHMAnnotation.ParamOK (fun i => bounds outer (types i)) (fun i => bounds outer (slots i)) ids (CountAlgebra.compose outer rows)
      (Δ.map (constraint outer)) ann (bounds outer β) := by
  cases ann with
  | none => trivial
  | some τ => exact h.counts outer hf

private theorem binding_counts {types slots ids rows Δ ann β}
    (h : ScopedHMAnnotation.BindingOK types slots ids rows Δ ann β) (outer : Bindings) (hf : Finite outer) :
    ScopedHMAnnotation.BindingOK (fun i => bounds outer (types i)) (fun i => bounds outer (slots i)) ids (CountAlgebra.compose outer rows)
      (Δ.map (constraint outer)) ann (bounds outer β) := by
  cases ann with
  | none => trivial
  | some σ => exact ⟨h.1, h.2.counts outer hf⟩

/-- Whole-RHS count transport also maps counts inside inserted HM types. Closed
    callee telescopes stay protected and source annotations stay unchanged. -/
theorem transportScopedCounts (outer : Bindings) (hf : Finite outer) (target : List Nat)
    (scope : ∀ row ∈ outer, Scope.CountScoped target row.2)
    {types slots ids rows Δ env e β} (h : ScopedDerives types slots ids rows Δ env e β)
    (fresh : CountCapturesFixed outer env) :
    ScopedDerives (fun i => bounds outer (types i)) (fun i => bounds outer (slots i)) ids (CountAlgebra.compose outer rows)
      (Δ.map (constraint outer)) (env.map (mapCountBinding outer)) e (bounds outer β) := by
  induction h with
  | literal => cases ‹PrimLitExpr› <;> exact .literal
  | primBinOp => cases ‹PrimBinOp› <;> exact .primBinOp
  | nil => exact .nil
  | boolCtor hn => exact .boolCtor hn
  | ctor hn => exact .ctor hn
  | cons _ _ hs ihh iht =>
      exact .cons (ihh fresh) (iht fresh) (CountSubstitution.subtype outer hf hs)
  | pair _ _ ihLeft ihRight => exact .pair (ihLeft fresh) (ihRight fresh)
  | varMono hv => exact .varMono (by simpa [mapCountBinding] using congrArg (Option.map (mapCountBinding outer)) hv)
  | @varRecursive Δ ids rows env i c caller hv u =>
      have captured := fresh.recursive (List.mem_of_getElem? hv)
      rw [← u.mapCounts_bounds outer hf target scope captured]
      exact .varRecursive (env := env.map (mapCountBinding outer)) (i := i) (c := c.mapCounts outer) (by
        simpa only [List.getElem?_map, mapCountBinding, Option.map_some] using
          congrArg (Option.map (mapCountBinding outer)) hv)
        (u.mapCounts outer hf target scope captured)
  | varExported hv u =>
      have captured := fresh.exported (List.mem_of_getElem? hv)
      rw [← mapExportedUseCounts_bounds u outer hf target scope captured]
      exact .varExported
        (by simpa [mapCountBinding] using congrArg (Option.map (mapCountBinding outer)) hv)
        (mapExportedUseCounts u outer hf target scope captured)
  | app _ _ hs ihf iha =>
      exact .app (ihf fresh) (iha fresh) (CountSubstitution.subtype outer hf hs)
  | lambda hp _ ih =>
      exact .lambda (param_counts hp outer hf) (by
        simpa [mapCountBinding] using ih (count_captures_cons fresh))
  | letMono hp _ _ ihr ihb =>
      exact .letMono (binding_counts hp outer hf) (ihr fresh)
        (by simpa [mapCountBinding] using ihb (count_captures_cons fresh))
  | matchList _ hc hpat _ hsub ihscrut ihbranches =>
      apply ScopedDerives.matchList (ihscrut fresh) (hc.transport outer hf) hpat
      · intro i br hb
        have ht := ihbranches i br hb (count_captures_branch fresh)
        by_cases hcbr : br.1 = .named consCtorName 2
        · simpa [branchEnv, hcbr, mapCountBinding, bounds, List.map_append,
            RecursiveCountTransport.branchRefine_transport] using ht
        · simpa [branchEnv, hcbr, List.map_append, RecursiveCountTransport.branchRefine_transport] using ht
      · intro i br hb
        simpa only [List.map_append, RecursiveCountTransport.branchRefine_transport] using
          CountSubstitution.subtype outer hf (hsub i br hb)
  | matchBool _ hc hpat _ hsub ihscrut ihbranches =>
      exact .matchBool (ihscrut fresh) hc hpat
        (fun i br hb => ihbranches i br hb fresh)
        (fun i br hb => CountSubstitution.subtype outer hf (hsub i br hb))
  | matchPair _ hc hpat _ hsub ihscrut ihbranches =>
      apply ScopedDerives.matchPair (ihscrut fresh) hc hpat
      · intro i br hb
        have moved := ihbranches i br hb (count_captures_pairBranch fresh)
        by_cases hp : br.1 = .named pairCtorName 2
        · simpa [pairBranchEnv, hp, mapCountBinding, bounds] using moved
        · simpa [pairBranchEnv, hp] using moved
      · intro i br hb
        exact CountSubstitution.subtype outer hf (hsub i br hb)
  | matchNominal fieldss actuals _ hc fields bodies hsub ihscrut ihbranches =>
      apply ScopedDerives.matchNominal
        (fieldss := fun i => CountSubstitution.boundsList outer (fieldss i))
        (actuals := fun i => CountSubstitution.bounds outer (actuals i))
        (ihscrut fresh) hc
      · intro i br hb
        exact (fields i br hb).counts outer
      · intro i br hb
        have moved := ihbranches i br hb (count_captures_monos fresh (fieldss i))
        have mappedFields :
            ((fieldss i).map Binding.mono).map (mapCountBinding outer) =
              (CountSubstitution.boundsList outer (fieldss i)).map Binding.mono := by
          induction (fieldss i) with
          | nil => rfl
          | cons field rest ih => simp [CountSubstitution.boundsList, mapCountBinding, ih]
        simpa only [List.map_append, mappedFields] using moved
      · intro i br hb
        exact CountSubstitution.subtype outer hf (hsub i br hb)
  | matchOpaque _ hpat _ hsub ihscrut ihbranches =>
      exact .matchOpaque (ihscrut fresh) hpat
        (fun i br hb => ihbranches i br hb fresh)
        (fun i br hb => CountSubstitution.subtype outer hf (hsub i br hb))

/-- Count specialization preserves readiness of the whole existing proof,
    not merely support of its final type. Callee captures remain protected. -/
theorem ScopedDerives.RuntimeReady.counts (outer : Bindings) (hf : Finite outer) (target : List Nat)
    (scope : ∀ row ∈ outer, Scope.CountScoped target row.2)
    {types slots ids rows Δ env e β} {h : ScopedDerives types slots ids rows Δ env e β}
    (ready : ScopedDerives.RuntimeReady h) (fresh : CountCapturesFixed outer env) :
    ScopedDerives.RuntimeReady (transportScopedCounts outer hf target scope h fresh) := by
  induction ready with
  | literal => cases ‹PrimLitExpr› <;> exact .literal
  | primBinOp => cases ‹PrimBinOp› <;> exact .primBinOp
  | nil support => exact .nil (support.counts outer)
  | boolCtor nameOK => exact .boolCtor nameOK
  | cons sub _ _ ihh iht =>
      exact .cons (CountSubstitution.subtype outer hf sub) (ihh fresh) (iht fresh)
  | pair _ _ ihLeft ihRight => exact .pair (ihLeft fresh) (ihRight fresh)
  | varMono lookup support =>
      exact .varMono (by simpa [mapCountBinding] using congrArg (Option.map (mapCountBinding outer)) lookup)
        (support.counts outer)
  | @varRecursive env' i c pathΔ caller lookup used support =>
      have captured := fresh.recursive (List.mem_of_getElem? lookup)
      have moved := ScopedDerives.RuntimeReady.varRecursive
        (types := fun i => bounds outer (types i)) (slots := fun i => bounds outer (slots i))
        (ids := ids) (rows := CountAlgebra.compose outer rows)
        (env := env'.map (mapCountBinding outer)) (i := i) (c := c.mapCounts outer)
        (by simpa only [List.getElem?_map, Option.map_some, mapCountBinding]
          using congrArg (Option.map (mapCountBinding outer)) lookup)
        (used.mapCounts outer hf target scope captured)
        (by simpa only [used.mapCounts_bounds outer hf target scope captured] using support.counts outer)
      simpa only [used.mapCounts_bounds outer hf target scope captured] using moved
  | @varExported env' i s pathΔ found caller lookup used support arguments =>
      have captured := fresh.exported (List.mem_of_getElem? lookup)
      have moved := ScopedDerives.RuntimeReady.varExported
        (types := fun i => bounds outer (types i)) (slots := fun i => bounds outer (slots i))
        (ids := ids) (rows := CountAlgebra.compose outer rows)
        (env := env'.map (mapCountBinding outer)) (i := i) (s := s)
        (by simpa only [List.getElem?_map, Option.map_some, mapCountBinding]
          using congrArg (Option.map (mapCountBinding outer)) lookup)
        (mapExportedUseCounts used outer hf target scope captured)
        (by simpa only [mapExportedUseCounts_bounds used outer hf target scope captured]
          using support.counts outer)
        (by
          intro a ha
          obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
          exact (arguments b hb).counts outer)
      simpa only [mapExportedUseCounts_bounds used outer hf target scope captured] using moved
  | app sub _ _ ihf iha =>
      exact .app (CountSubstitution.subtype outer hf sub) (ihf fresh) (iha fresh)
  | lambda annotation support _ ih =>
      exact .lambda (param_counts annotation outer hf) (support.counts outer)
        (by simpa [mapCountBinding] using ih (count_captures_cons fresh))
  | letMono annotation _ _ ihr ihb =>
      exact .letMono (binding_counts annotation outer hf) (ihr fresh)
        (by simpa [mapCountBinding] using ihb (count_captures_cons fresh))
  | matchList coverage patterns bodies subs scrutReady branchesReady support ihs ihb =>
      rename_i pathΔ env' scrut lo hi elem branches result actuals hs
      have movedBodies : ∀ i br (atIndex : branches[i]? = some br),
          ScopedDerives (fun i => bounds outer (types i)) (fun i => bounds outer (slots i))
            ids (CountAlgebra.compose outer rows)
            (pathΔ.map (constraint outer) ++ RecursiveTyping.branchRefine br.1 (count outer lo) (count outer hi))
            (branchEnv br.1 (count outer lo) (count outer hi) (bounds outer elem)
              (env'.map (mapCountBinding outer))) br.2 (bounds outer (actuals i)) := by
        intro i br atIndex
        have moved := transportScopedCounts outer hf target scope (bodies i br atIndex)
          (count_captures_branch fresh)
        by_cases isCons : br.1 = .named consCtorName 2
        · simpa [branchEnv, isCons, mapCountBinding, bounds, List.map_append,
            RecursiveCountTransport.branchRefine_transport] using moved
        · simpa [branchEnv, isCons, List.map_append, RecursiveCountTransport.branchRefine_transport] using moved
      refine .matchList (coverage.transport outer hf) patterns movedBodies
        (fun i br atIndex => by simpa only [List.map_append, RecursiveCountTransport.branchRefine_transport]
          using CountSubstitution.subtype outer hf (subs i br atIndex))
        (ihs fresh) ?_ (support.counts outer)
      intro i br atIndex
      have moved := ihb i br atIndex (count_captures_branch fresh)
      by_cases isCons : br.1 = .named consCtorName 2
      · simpa [branchEnv, isCons, mapCountBinding, bounds, List.map_append,
          RecursiveCountTransport.branchRefine_transport] using moved
      · simpa [branchEnv, isCons, List.map_append, RecursiveCountTransport.branchRefine_transport] using moved
  | matchBool coverage patterns bodies subs _ _ support ihs ihb =>
      exact .matchBool coverage patterns
        (fun i br atIndex => transportScopedCounts outer hf target scope
          (bodies i br atIndex) fresh)
        (fun i br atIndex => CountSubstitution.subtype outer hf (subs i br atIndex))
        (ihs fresh) (fun i br atIndex => ihb i br atIndex fresh)
        (support.counts outer)
  | matchPair coverage patterns bodies subs _ _ support ihs ihb =>
      have movedBodies := fun i br atIndex => transportScopedCounts outer hf target scope
        (bodies i br atIndex) (count_captures_pairBranch fresh)
      refine .matchPair coverage patterns ?_
        (fun i br atIndex => CountSubstitution.subtype outer hf (subs i br atIndex))
        (ihs fresh) ?_ (support.counts outer)
      · intro i br atIndex
        by_cases hp : br.1 = .named pairCtorName 2
        · simpa [pairBranchEnv, hp, mapCountBinding, bounds] using movedBodies i br atIndex
        · simpa [pairBranchEnv, hp] using movedBodies i br atIndex
      · intro i br atIndex
        have moved := ihb i br atIndex (count_captures_pairBranch fresh)
        by_cases hp : br.1 = .named pairCtorName 2
        · simpa [pairBranchEnv, hp, mapCountBinding, bounds] using moved
        · simpa [pairBranchEnv, hp] using moved

#print axioms ScopedDerives.RuntimeReady.counts

/-- Full HM specialization preserves every intermediate runtime interpretation.
    Only supported full arguments may enlarge this proof fragment; an erased
    HM-shape check cannot justify an unsupported nominal runtime meaning. -/
theorem ScopedDerives.RuntimeReady.types (f : Nat → BoundsTy)
    (hf : ∀ i, (Synth.BoundsTy.toTy (f i)).IsLC)
    (target : List Nat) (scope : ∀ i, ScopedScheme.BoundsScoped target (f i))
    (arguments : ∀ i, Runtime.Supported (f i))
    {types slots ids rows Δ env e β} {h : ScopedDerives types slots ids rows Δ env e β}
    (ready : ScopedDerives.RuntimeReady h) (fresh : CapturesFixed f env) :
    ScopedDerives.RuntimeReady (transportScopedTypes f hf target scope h fresh) := by
  induction ready with
  | literal => cases ‹PrimLitExpr› <;> exact .literal
  | primBinOp => cases ‹PrimBinOp› <;> exact .primBinOp
  | nil support => exact .nil (support.types f arguments)
  | boolCtor nameOK => exact .boolCtor nameOK
  | cons sub _ _ ihh iht =>
      exact .cons (SchemeSpecialization.subtype f sub) (ihh fresh) (iht fresh)
  | pair _ _ ihLeft ihRight => exact .pair (ihLeft fresh) (ihRight fresh)
  | varMono lookup support =>
      exact .varMono (by simpa [mapBinding] using congrArg (Option.map (mapBinding f hf)) lookup)
        (support.types f arguments)
  | @varRecursive env' i c pathΔ caller lookup used support =>
      have captured := fresh.recursive (List.mem_of_getElem? lookup)
      have moved := ScopedDerives.RuntimeReady.varRecursive
        (types := fun i => mapFree f (types i)) (slots := fun i => mapFree f (slots i))
        (ids := ids) (rows := rows) (env := env'.map (mapBinding f hf)) (i := i) (c := c.mapTypes f hf)
        (by simpa only [List.getElem?_map, Option.map_some, mapBinding]
          using congrArg (Option.map (mapBinding f hf)) lookup)
        (mapUse used f hf target scope)
        (by simpa only [mapUse_bounds used f hf target scope captured] using support.types f arguments)
      simpa only [mapUse_bounds used f hf target scope captured] using moved
  | @varExported env' i s pathΔ found caller lookup used support usedArguments =>
      have captured := fresh.exported (List.mem_of_getElem? lookup)
      have moved := ScopedDerives.RuntimeReady.varExported
        (types := fun i => mapFree f (types i)) (slots := fun i => mapFree f (slots i))
        (ids := ids) (rows := rows) (env := env'.map (mapBinding f hf)) (i := i) (s := s)
        (by simpa only [List.getElem?_map, Option.map_some, mapBinding]
          using congrArg (Option.map (mapBinding f hf)) lookup)
        (mapExportedUse used f hf target scope captured)
        (by simpa only [mapExportedUse_bounds used f hf target scope captured]
          using support.types f arguments)
        (by
          intro a ha
          obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
          exact (usedArguments b hb).types f arguments)
      simpa only [mapExportedUse_bounds used f hf target scope captured] using moved
  | app sub _ _ ihf iha =>
      exact .app (SchemeSpecialization.subtype f sub) (ihf fresh) (iha fresh)
  | lambda annotation support _ ih =>
      exact .lambda (param_types annotation f) (support.types f arguments)
        (by simpa [mapBinding] using ih (captures_cons fresh))
  | letMono annotation _ _ ihr ihb =>
      exact .letMono (binding_types annotation f) (ihr fresh)
        (by simpa [mapBinding] using ihb (captures_cons fresh))
  | matchList coverage patterns bodies subs scrutReady branchesReady support ihs ihb =>
      rename_i pathΔ env' scrut lo hi elem branches result actuals hs
      have movedBodies : ∀ i br (atIndex : branches[i]? = some br),
          ScopedDerives (fun i => mapFree f (types i)) (fun i => mapFree f (slots i)) ids rows
            (pathΔ ++ RecursiveTyping.branchRefine br.1 lo hi)
            (branchEnv br.1 lo hi (mapFree f elem) (env'.map (mapBinding f hf))) br.2 (mapFree f (actuals i)) := by
        intro i br atIndex
        have moved := transportScopedTypes f hf target scope (bodies i br atIndex)
          (captures_branch fresh)
        by_cases isCons : br.1 = .named consCtorName 2
        · simpa [branchEnv, isCons, mapBinding, mapFree] using moved
        · simpa [branchEnv, isCons] using moved
      refine .matchList coverage patterns movedBodies
        (fun i br atIndex => SchemeSpecialization.subtype f (subs i br atIndex))
        (ihs fresh) ?_ (support.types f arguments)
      intro i br atIndex
      have moved := ihb i br atIndex (captures_branch fresh)
      by_cases isCons : br.1 = .named consCtorName 2
      · simpa [branchEnv, isCons, mapBinding, mapFree] using moved
      · simpa [branchEnv, isCons] using moved
  | matchBool coverage patterns bodies subs _ _ support ihs ihb =>
      exact .matchBool coverage patterns
        (fun i br atIndex => transportScopedTypes f hf target scope
          (bodies i br atIndex) fresh)
        (fun i br atIndex => SchemeSpecialization.subtype f (subs i br atIndex))
        (ihs fresh) (fun i br atIndex => ihb i br atIndex fresh)
        (support.types f arguments)
  | matchPair coverage patterns bodies subs _ _ support ihs ihb =>
      have movedBodies := fun i br atIndex => transportScopedTypes f hf target scope
        (bodies i br atIndex) (captures_pairBranch fresh)
      refine .matchPair coverage patterns ?_
        (fun i br atIndex => SchemeSpecialization.subtype f (subs i br atIndex))
        (ihs fresh) ?_ (support.types f arguments)
      · intro i br atIndex
        by_cases hp : br.1 = .named pairCtorName 2
        · simpa [pairBranchEnv, hp, mapBinding, mapFree] using movedBodies i br atIndex
        · simpa [pairBranchEnv, hp] using movedBodies i br atIndex
      · intro i br atIndex
        have moved := ihb i br atIndex (captures_pairBranch fresh)
        by_cases hp : br.1 = .named pairCtorName 2
        · simpa [pairBranchEnv, hp, mapBinding, mapFree] using moved
        · simpa [pairBranchEnv, hp] using moved

#print axioms ScopedDerives.RuntimeReady.types

/-- Identity-slot specialization of the canonical scoped transport. -/
theorem transportTypes (f : Nat → BoundsTy) (hf : ∀ i, (Synth.BoundsTy.toTy (f i)).IsLC)
    (target : List Nat) (scope : ∀ i, ScopedScheme.BoundsScoped target (f i))
    {types ids rows Δ env e β} (h : Derives types ids rows Δ env e β)
    (fresh : CapturesFixed f env) :
    Derives (fun i => mapFree f (types i)) ids rows Δ (env.map (mapBinding f hf)) e (mapFree f β) := by
  simpa only [mapFree] using transportScopedTypes f hf target scope h fresh

/-- Identity-slot specialization of the canonical scoped count transport. -/
theorem transportCounts (outer : Bindings) (hf : Finite outer) (target : List Nat)
    (scope : ∀ row ∈ outer, Scope.CountScoped target row.2)
    {types ids rows Δ env e β} (h : Derives types ids rows Δ env e β)
    (fresh : CountCapturesFixed outer env) :
    Derives (fun i => bounds outer (types i)) ids (CountAlgebra.compose outer rows)
      (Δ.map (constraint outer)) (env.map (mapCountBinding outer)) e (bounds outer β) := by
  simpa only [bounds] using transportScopedCounts outer hf target scope h fresh

#print axioms transportScopedTypes
#print axioms transportScopedCounts
#print axioms transportTypes
#print axioms transportCounts

end FHM.Bounds.RecursiveHMJudgement
