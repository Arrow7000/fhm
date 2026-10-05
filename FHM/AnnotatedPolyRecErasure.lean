import FHM.Core
import Mathlib.Data.List.TakeDrop

/-!
# Annotated polymorphic recursion with an erased runtime

This module is the first, deliberately small formal spike described in
`briefs/annotated-polyrec-with-erasure.md`.  It isolates the architectural point
from the production language:

* source `let rec` nodes carry complete schemes;
* those schemes are available at every recursive occurrence while each RHS is
  checked at its own scheme;
* runtime terms contain no schemes or type applications; and
* the runtime typing derivation, rather than runtime syntax, remembers the
  recursive schemes.

The calculus contains only integers, variables, functions, application, `let`,
and annotated recursive groups.  It establishes structural erasure, derives
concrete scheme instances from cofinite rigid checking, and proves preservation
for type-free recursive unfolding.  It does not yet model the hybrid
annotated/unannotated production rule.
-/

namespace AnnotatedPolyRecErasure

/-- Author-facing terms.  Every member of the tiny calculus's recursive groups
has a complete scheme annotation. -/
inductive SourceExpr
  | int (n : Int)
  | var (index : Nat)
  | lam (body : SourceExpr)
  | app (fn arg : SourceExpr)
  | letIn (scheme : PolyTy) (rhs body : SourceExpr)
  | letRec (schemes : List PolyTy) (bindings : List SourceExpr) (body : SourceExpr)

/-- Machine terms.  Recursive schemes are absent. -/
inductive RunExpr
  | int (n : Int)
  | var (index : Nat)
  | lam (body : RunExpr)
  | app (fn arg : RunExpr)
  | letIn (rhs body : RunExpr)
  | letRec (bindings : List RunExpr) (body : RunExpr)
  deriving Repr

/-- Full type erasure.  In particular, a recursive member's scheme is not
retained on the runtime node. -/
def SourceExpr.erase : SourceExpr → RunExpr
  | .int n => .int n
  | .var i => .var i
  | .lam body => .lam body.erase
  | .app fn arg => .app fn.erase arg.erase
  | .letIn _ rhs body => .letIn rhs.erase body.erase
  | .letRec _ bindings body =>
      .letRec (bindings.map SourceExpr.erase) body.erase
termination_by e => sizeOf e
decreasing_by
  all_goals simp_wf
  all_goals first
    | omega
    | (have h := List.sizeOf_lt_of_mem ‹_›; omega)

@[simp] theorem SourceExpr.erase_int (n : Int) :
    (SourceExpr.int n).erase = .int n := by simp only [SourceExpr.erase]

@[simp] theorem SourceExpr.erase_var (i : Nat) :
    (SourceExpr.var i).erase = .var i := by simp only [SourceExpr.erase]

@[simp] theorem SourceExpr.erase_lam (body : SourceExpr) :
    (SourceExpr.lam body).erase = .lam body.erase := by simp only [SourceExpr.erase]

@[simp] theorem SourceExpr.erase_app (fn arg : SourceExpr) :
    (SourceExpr.app fn arg).erase = .app fn.erase arg.erase := by simp only [SourceExpr.erase]

@[simp] theorem SourceExpr.erase_letIn (scheme : PolyTy) (rhs body : SourceExpr) :
    (SourceExpr.letIn scheme rhs body).erase = .letIn rhs.erase body.erase := by
  simp only [SourceExpr.erase]

@[simp] theorem SourceExpr.erase_letRec (schemes : List PolyTy)
    (bindings : List SourceExpr) (body : SourceExpr) :
    (SourceExpr.letRec schemes bindings body).erase =
      .letRec (bindings.map SourceExpr.erase) body.erase := by
  simp only [SourceExpr.erase]

/-! ### Lockstep opening of authored scoped type variables

An annotated binding's quantified variables scope over its RHS.  When an outer
annotation is opened, nested annotations shield their own binders while references
to the outer binders are opened through them.  Runtime erasure subsequently removes
all of this structure. -/

mutual

def SourceExpr.openTyVarsAux (depth : Nat) (names : List Nat) : SourceExpr → SourceExpr
  | .int n => .int n
  | .var i => .var i
  | .lam body => .lam (body.openTyVarsAux depth names)
  | .app fn arg =>
      .app (fn.openTyVarsAux depth names) (arg.openTyVarsAux depth names)
  | .letIn scheme rhs body =>
      let innerDepth := depth + scheme.paramCount
      let openedScheme :=
        { scheme with body := Ty.openTyFrom innerDepth (names.map Ty.fvar) scheme.body }
      .letIn openedScheme (rhs.openTyVarsAux innerDepth names)
        (body.openTyVarsAux depth names)
  | .letRec schemes bindings body =>
      let opened := openRecGroupTyVarsAux depth names schemes bindings
      .letRec opened.1 opened.2 (body.openTyVarsAux depth names)
termination_by e => sizeOf e

def openRecGroupTyVarsAux (depth : Nat) (names : List Nat) :
    List PolyTy → List SourceExpr → List PolyTy × List SourceExpr
  | [], [] => ([], [])
  | [], rhs :: rest =>
      let opened := openRecGroupTyVarsAux depth names [] rest
      (opened.1, rhs.openTyVarsAux depth names :: opened.2)
  | scheme :: schemes, [] =>
      let innerDepth := depth + scheme.paramCount
      let openedScheme :=
        { scheme with body := Ty.openTyFrom innerDepth (names.map Ty.fvar) scheme.body }
      let opened := openRecGroupTyVarsAux depth names schemes []
      (openedScheme :: opened.1, opened.2)
  | scheme :: schemes, rhs :: rest =>
      let innerDepth := depth + scheme.paramCount
      let openedScheme :=
        { scheme with body := Ty.openTyFrom innerDepth (names.map Ty.fvar) scheme.body }
      let opened := openRecGroupTyVarsAux depth names schemes rest
      (openedScheme :: opened.1,
        rhs.openTyVarsAux innerDepth names :: opened.2)
termination_by schemes bindings => sizeOf schemes + sizeOf bindings
end

def SourceExpr.openTyVars (names : List Nat) (e : SourceExpr) : SourceExpr :=
  e.openTyVarsAux 0 names

/-! The generated recursor does not expose induction hypotheses for expressions
stored in the `bindings` list.  This stronger recursor does, which is exactly
what the lockstep-opening proofs need. -/

@[elab_as_elim]
def SourceExpr.rec_strong.{u} {motive : SourceExpr → Sort u}
    (int : ∀ n, motive (.int n))
    (var : ∀ index, motive (.var index))
    (lam : ∀ body, motive body → motive (.lam body))
    (app : ∀ fn arg, motive fn → motive arg → motive (.app fn arg))
    (letIn : ∀ scheme rhs body, motive rhs → motive body →
      motive (.letIn scheme rhs body))
    (letRec : ∀ schemes bindings body,
      (∀ e ∈ bindings, motive e) → motive body →
      motive (.letRec schemes bindings body)) :
    (e : SourceExpr) → motive e
  | .int n => int n
  | .var index => var index
  | .lam body =>
      lam body (SourceExpr.rec_strong int var lam app letIn letRec body)
  | .app fn arg =>
      app fn arg
        (SourceExpr.rec_strong int var lam app letIn letRec fn)
        (SourceExpr.rec_strong int var lam app letIn letRec arg)
  | .letIn scheme rhs body =>
      letIn scheme rhs body
        (SourceExpr.rec_strong int var lam app letIn letRec rhs)
        (SourceExpr.rec_strong int var lam app letIn letRec body)
  | .letRec schemes bindings body =>
      letRec schemes bindings body
        (fun e _he => SourceExpr.rec_strong int var lam app letIn letRec e)
        (SourceExpr.rec_strong int var lam app letIn letRec body)
termination_by e => sizeOf e
decreasing_by
  all_goals simp_wf
  all_goals first
    | omega
    | (have h := List.sizeOf_lt_of_mem _he; omega)

private theorem openRecGroupTyVarsAux_erases (depth : Nat) (names : List Nat)
    (schemes : List PolyTy) (bindings : List SourceExpr) :
    (∀ rhs ∈ bindings, ∀ depth names,
      (rhs.openTyVarsAux depth names).erase = rhs.erase) →
    (openRecGroupTyVarsAux depth names schemes bindings).2.map SourceExpr.erase =
      bindings.map SourceExpr.erase := by
  intro hbindings
  induction bindings generalizing schemes with
  | nil =>
      induction schemes with
      | nil => simp [openRecGroupTyVarsAux]
      | cons scheme schemes ih => simp [openRecGroupTyVarsAux, ih]
  | cons rhs rest ih =>
      have hrhs := hbindings rhs (by simp)
      have hrest : ∀ e ∈ rest, ∀ depth names,
          (e.openTyVarsAux depth names).erase = e.erase := by
        intro e he
        exact hbindings e (by simp [he])
      cases schemes with
      | nil => simp [openRecGroupTyVarsAux, hrhs, ih [] hrest]
      | cons scheme schemes =>
          simp [openRecGroupTyVarsAux, hrhs, ih schemes hrest]

/-- Opening source-only type annotations has no runtime effect. -/
theorem SourceExpr.erase_openTyVarsAux (e : SourceExpr) :
    ∀ depth names, (e.openTyVarsAux depth names).erase = e.erase := by
  induction e using SourceExpr.rec_strong with
  | int n => intro depth names; simp [SourceExpr.openTyVarsAux]
  | var i => intro depth names; simp [SourceExpr.openTyVarsAux]
  | lam body ih =>
      intro depth names
      simp [SourceExpr.openTyVarsAux, ih]
  | app fn arg ihfn iharg =>
      intro depth names
      simp [SourceExpr.openTyVarsAux, ihfn, iharg]
  | letIn scheme rhs body ihrhs ihbody =>
      intro depth names
      simp [SourceExpr.openTyVarsAux, ihrhs, ihbody]
  | letRec schemes bindings body ihbindings ihbody =>
      intro depth names
      simp [SourceExpr.openTyVarsAux, ihbody,
        openRecGroupTyVarsAux_erases depth names schemes bindings ihbindings]

@[simp] theorem SourceExpr.erase_openTyVars (e : SourceExpr) (names : List Nat) :
    (e.openTyVars names).erase = e.erase :=
  e.erase_openTyVarsAux 0 names

/-- A list of locally closed types of the right arity is a legal scheme
instantiation. -/
def InstArgs (scheme : PolyTy) (args : List Ty) : Prop :=
  args.length = scheme.paramCount ∧ ∀ arg ∈ args, arg.IsLC

/-! ### Cofinite source openings

Each recursive RHS lies beneath the quantifiers written on its own annotation.
`openRecRhsOwn` opens those binders in the RHS—including references reaching
through annotations nested inside that RHS—using the same slice with which
`PolyTy.openGroup` opens its expected type.  It deliberately leaves the other
members' RHSs to their own slices. -/

def SourceExpr.openRecRhsOwn :
    List PolyTy → List SourceExpr → List Nat → List SourceExpr
  | [], bindings, _ => bindings
  | _ :: _, [], _ => []
  | scheme :: schemes, rhs :: rest, names =>
      rhs.openTyVars (names.take scheme.paramCount) ::
        SourceExpr.openRecRhsOwn schemes rest (names.drop scheme.paramCount)

@[simp] theorem SourceExpr.erase_openRecRhsOwn
    (schemes : List PolyTy) (bindings : List SourceExpr) (names : List Nat) :
    (SourceExpr.openRecRhsOwn schemes bindings names).map SourceExpr.erase =
      bindings.map SourceExpr.erase := by
  induction schemes generalizing bindings names with
  | nil => simp [SourceExpr.openRecRhsOwn]
  | cons scheme schemes ih =>
      cases bindings with
      | nil => simp [SourceExpr.openRecRhsOwn]
      | cons rhs rest =>
          simp [SourceExpr.openRecRhsOwn, SourceExpr.erase_openTyVars, ih]

/-! ## Type-free runtime operations -/

mutual

/-- Shift free term variables.  Types cannot be shifted because `RunExpr`
contains none. -/
def RunExpr.shiftFrom (threshold amount : Nat) : RunExpr → RunExpr
  | .int n => .int n
  | .var i => if i < threshold then .var i else .var (i + amount)
  | .lam body => .lam (body.shiftFrom (threshold + 1) amount)
  | .app fn arg => .app (fn.shiftFrom threshold amount) (arg.shiftFrom threshold amount)
  | .letIn rhs body =>
      .letIn (rhs.shiftFrom threshold amount) (body.shiftFrom (threshold + 1) amount)
  | .letRec bindings body =>
      .letRec (shiftGroup (threshold + bindings.length) amount bindings)
        (body.shiftFrom (threshold + bindings.length) amount)

/-- Shift every member of a recursive group under the same simultaneous binder
depth. -/
def shiftGroup (threshold amount : Nat) : List RunExpr → List RunExpr
  | [] => []
  | rhs :: rest => rhs.shiftFrom threshold amount :: shiftGroup threshold amount rest

end

mutual

/-- Capture-avoiding simultaneous substitution for de Bruijn term variables. -/
def RunExpr.substN (depth : Nat) (values : List RunExpr) : RunExpr → RunExpr
  | .int n => .int n
  | .var i =>
      if i < depth then .var i
      else if h : i - depth < values.length then
        (values[i - depth]).shiftFrom 0 depth
      else .var (i - values.length)
  | .lam body => .lam (body.substN (depth + 1) values)
  | .app fn arg => .app (fn.substN depth values) (arg.substN depth values)
  | .letIn rhs body =>
      .letIn (rhs.substN depth values) (body.substN (depth + 1) values)
  | .letRec bindings body =>
      .letRec (substGroup (depth + bindings.length) values bindings)
        (body.substN (depth + bindings.length) values)

/-- Substitute through every member of a simultaneous recursive group. -/
def substGroup (depth : Nat) (values : List RunExpr) : List RunExpr → List RunExpr
  | [] => []
  | rhs :: rest => rhs.substN depth values :: substGroup depth values rest

end

/-- One ordinary, entirely type-free recursive unfolding step. -/
inductive RunStep : RunExpr → RunExpr → Prop
  | letRecUnfold :
      RunStep (.letRec bindings body)
        (body.substN 0 (bindings.map fun rhs => .letRec bindings rhs))

/-! ## Source and runtime typing

The cofinite premises are definitions parameterised by the typing relation.
This keeps the inductive relations strictly positive while giving their
recursors induction hypotheses for every packaged subderivation. -/

/-- An annotated nonrecursive RHS checks at every sufficiently fresh rigid
opening of its authored scheme.  The exact same names open scoped occurrences
inside nested source annotations. -/
def SourceGeneralisesTo
    (TypeOf : Env → SourceExpr → Ty → Prop) (env : Env)
    (scheme : PolyTy) (rhs : SourceExpr) (avoid : List Nat) : Prop :=
  ∀ names, FreshNames avoid scheme.paramCount names →
    TypeOf env (rhs.openTyVars names) (scheme.openVars names)

/-- Every annotated recursive RHS checks at every sufficiently fresh opening
of all group quantifiers.  Recursive uses see all declared schemes; the RHS and
its expected type are opened with the same member-specific name slice. -/
def SourceRecGroupChecks
    (TypeOf : Env → SourceExpr → Ty → Prop) (env : Env)
    (schemes : List PolyTy) (bindings : List SourceExpr)
    (avoid : List Nat) : Prop :=
  ∀ names, FreshNames avoid (PolyTy.totalParams schemes) names →
    ∀ pair ∈ (SourceExpr.openRecRhsOwn schemes bindings names).zip
        (PolyTy.openGroup schemes names),
      TypeOf (schemes ++ env) pair.1 pair.2

/-- The runtime counterpart needs no expression opening: annotations have
already disappeared.  Only the proof's expected types are rigidly opened. -/
def RunGeneralisesTo
    (TypeOf : Env → RunExpr → Ty → Prop) (env : Env)
    (scheme : PolyTy) (rhs : RunExpr) (avoid : List Nat) : Prop :=
  ∀ names, FreshNames avoid scheme.paramCount names →
    TypeOf env rhs (scheme.openVars names)

def RunRecGroupChecks
    (TypeOf : Env → RunExpr → Ty → Prop) (env : Env)
    (schemes : List PolyTy) (bindings : List RunExpr)
    (avoid : List Nat) : Prop :=
  ∀ names, FreshNames avoid (PolyTy.totalParams schemes) names →
    ∀ pair ∈ bindings.zip (PolyTy.openGroup schemes names),
      TypeOf (schemes ++ env) pair.1 pair.2

inductive SourceWT : Env → SourceExpr → Ty → Prop
  | int : SourceWT env (.int n) (.prim .int)
  | var :
      env[index]? = some scheme →
      InstArgs scheme args →
      SourceWT env (.var index) (scheme.openWith args)
  | lam :
      SourceWT (PolyTy.mkTrivial paramTy :: env) body resultTy →
      SourceWT env (.lam body) (.arrow paramTy resultTy)
  | app :
      SourceWT env fn (.arrow argTy resultTy) →
      SourceWT env arg argTy →
      SourceWT env (.app fn arg) resultTy
  | letIn {avoid : List Nat} :
      scheme.WF →
      SourceGeneralisesTo SourceWT env scheme rhs avoid →
      SourceWT (scheme :: env) body resultTy →
      SourceWT env (.letIn scheme rhs body) resultTy
  | letRec {avoid : List Nat} :
      bindings.length = schemes.length →
      (∀ scheme ∈ schemes, scheme.WF) →
      SourceRecGroupChecks SourceWT env schemes bindings avoid →
      SourceWT (schemes ++ env) body resultTy →
      SourceWT env (.letRec schemes bindings body) resultTy

/-- Typing for annotation-free machine terms.  `schemes` in `letRec` is an
existential proof witness: it is not a field of `RunExpr` and the evaluator never
inspects it. -/
inductive RunWT : Env → RunExpr → Ty → Prop
  | int : RunWT env (.int n) (.prim .int)
  | var :
      env[index]? = some scheme →
      InstArgs scheme args →
      RunWT env (.var index) (scheme.openWith args)
  | lam :
      RunWT (PolyTy.mkTrivial paramTy :: env) body resultTy →
      RunWT env (.lam body) (.arrow paramTy resultTy)
  | app :
      RunWT env fn (.arrow argTy resultTy) →
      RunWT env arg argTy →
      RunWT env (.app fn arg) resultTy
  | letIn {scheme : PolyTy} {avoid : List Nat} :
      scheme.WF →
      RunGeneralisesTo RunWT env scheme rhs avoid →
      RunWT (scheme :: env) body resultTy →
      RunWT env (.letIn rhs body) resultTy
  | letRec {schemes : List PolyTy} {avoid : List Nat} :
      bindings.length = schemes.length →
      (∀ scheme ∈ schemes, scheme.WF) →
      RunRecGroupChecks RunWT env schemes bindings avoid →
      RunWT (schemes ++ env) body resultTy →
      RunWT env (.letRec bindings body) resultTy

private theorem SourceGeneralisesTo.erase
    {env : Env} {scheme : PolyTy} {rhs : SourceExpr} {avoid : List Nat}
    (_hsource : SourceGeneralisesTo SourceWT env scheme rhs avoid)
    (herased : ∀ names, FreshNames avoid scheme.paramCount names →
      RunWT env (rhs.openTyVars names).erase (scheme.openVars names)) :
    RunGeneralisesTo RunWT env scheme rhs.erase avoid := by
  intro names hfresh
  simpa only [SourceExpr.erase_openTyVars] using herased names hfresh

private theorem SourceRecGroupChecks.erase
    {env : Env} {schemes : List PolyTy} {bindings : List SourceExpr}
    {avoid : List Nat}
    (_hsource : SourceRecGroupChecks SourceWT env schemes bindings avoid)
    (herased : ∀ names,
      FreshNames avoid (PolyTy.totalParams schemes) names →
      ∀ pair ∈ (SourceExpr.openRecRhsOwn schemes bindings names).zip
          (PolyTy.openGroup schemes names),
        RunWT (schemes ++ env) pair.1.erase pair.2) :
    RunRecGroupChecks RunWT env schemes (bindings.map SourceExpr.erase) avoid := by
  intro names hfresh pair hpair
  have hmap :
      (SourceExpr.openRecRhsOwn schemes bindings names).map SourceExpr.erase =
        bindings.map SourceExpr.erase :=
    SourceExpr.erase_openRecRhsOwn schemes bindings names
  rw [← hmap] at hpair
  rw [List.zip_map_left] at hpair
  obtain ⟨sourcePair, hsourcePair, rfl⟩ := List.mem_map.mp hpair
  simpa using herased names hfresh sourcePair hsourcePair

/-- Erasure transports source typing to the proof-only runtime relation. -/
theorem SourceWT.erase_sound {env : Env} {e : SourceExpr} {ty : Ty}
    (h : SourceWT env e ty) : RunWT env e.erase ty := by
  induction h with
  | int => simpa using (RunWT.int)
  | var hlookup hargs => simpa using (RunWT.var hlookup hargs)
  | lam _ ih => simpa using (RunWT.lam ih)
  | app _ _ ihfn iharg => simpa using (RunWT.app ihfn iharg)
  | letIn hwf hgeneralises _ ihgeneralises ihbody =>
      simpa only [SourceExpr.erase_letIn] using
        RunWT.letIn hwf (SourceGeneralisesTo.erase hgeneralises ihgeneralises) ihbody
  | letRec hlen hwf hgroup _ ihgroup ihbody =>
      simpa only [SourceExpr.erase_letRec] using
        RunWT.letRec (by simpa using hlen) hwf
          (SourceRecGroupChecks.erase hgroup ihgroup) ihbody

/-! ## Runtime type substitution

The evaluator never performs this substitution.  It is proof infrastructure:
checking an annotated RHS at arbitrary fresh rigid names entails typing at every
concrete instantiation of the scheme. -/

private theorem Ty.substFvar_openWith_local {Z : Nat} {U : Ty}
    (hU : U.IsLC) (args : List Ty) (ty : Ty) :
    Ty.substFvar Z U (Ty.openWith args ty) =
      Ty.openWith (args.map (Ty.substFvar Z U)) (Ty.substFvar Z U ty) := by
  induction ty using Ty.rec_strong with
  | prim p => rfl
  | bvar i =>
      simp only [Ty.openWith, Ty.instantiate, Ty.substFvar, List.getElem?_map]
      cases args[i]? <;> rfl
  | fvar n =>
      simp only [Ty.openWith, Ty.instantiate]
      by_cases h : n = Z
      · subst n
        simp only [Ty.substFvar]
        exact (Ty.instantiate_eq_self_of_lc hU).symm
      · simp only [Ty.substFvar, if_neg h, Ty.instantiate]
  | arrow a b iha ihb =>
      simp only [Ty.openWith, Ty.instantiate, Ty.substFvar, Ty.arrow.injEq]
      exact ⟨iha, ihb⟩
  | customTy name tys ih =>
      simp only [Ty.openWith, Ty.instantiate, Ty.substFvar,
        TyList.instantiate_eq_map, TyList.substFvar_eq_map, List.map_map,
        Ty.customTy.injEq, true_and]
      apply List.map_congr_left
      intro t ht
      simpa only [Ty.openWith, Function.comp_apply] using ih t ht

private theorem InstArgs.substFvar {scheme : PolyTy} {args : List Ty}
    {Z : Nat} {U : Ty} (hU : U.IsLC) (h : InstArgs scheme args) :
    InstArgs (scheme.substFvar Z U) (args.map (Ty.substFvar Z U)) := by
  constructor
  · simpa [PolyTy.substFvar] using h.1
  · intro arg harg
    obtain ⟨arg0, harg0, rfl⟩ := List.mem_map.mp harg
    exact Ty.IsLC.substFvar hU (h.2 arg0 harg0)

theorem FreshNames.of_append_left {left right : List Nat} {n : Nat}
    {names : List Nat} (h : FreshNames (left ++ right) n names) :
    FreshNames right n names :=
  ⟨h.length, h.nodup, fun x hx hright => h.avoid x hx (by simp [hright])⟩

theorem FreshNames.not_mem_of_mem_avoid {avoid : List Nat} {n : Nat}
    {names : List Nat} (h : FreshNames avoid n names) {x : Nat}
    (hx : x ∈ avoid) : x ∉ names := by
  intro hmem
  exact h.avoid x hmem hx

theorem RunWT.substFvar {env : Env} {e : RunExpr} {ty U : Ty} {Z : Nat}
    (hU : U.IsLC) (h : RunWT env e ty) :
    RunWT (env.substFvar Z U) e (Ty.substFvar Z U ty) := by
  induction h with
  | int => exact .int
  | @var env index scheme args hlookup hargs =>
      have hlookup' : (env.substFvar Z U)[index]? =
          some (scheme.substFvar Z U) := by
        simp only [Env.substFvar, List.getElem?_map, hlookup, Option.map_some]
      have hv := RunWT.var hlookup' (hargs.substFvar hU)
      simpa [PolyTy.substFvar, PolyTy.openWith,
        Ty.substFvar_openWith_local hU] using hv
  | @lam paramTy env body resultTy _ ih =>
      have hb := ih
      simpa [Env.substFvar, PolyTy.mkTrivial] using
        (RunWT.lam (paramTy := Ty.substFvar Z U paramTy) hb)
  | app _ _ ihfn iharg => exact .app ihfn iharg
  | @letIn env rhs body resultTy scheme avoid hwf hgen _ ihgen ihbody =>
      let avoid' := [Z] ++ avoid
      apply RunWT.letIn (scheme := scheme.substFvar Z U) (avoid := avoid')
      · exact hwf.substFvar hU
      · intro names hfresh
        have hfresh0 : FreshNames avoid scheme.paramCount names := by
          simpa [avoid', PolyTy.substFvar] using FreshNames.of_append_left hfresh
        have hZ : Z ∉ names :=
          FreshNames.not_mem_of_mem_avoid hfresh (by simp [avoid'])
        have hrhs := ihgen names hfresh0
        rw [PolyTy.substFvar_openVars hU hZ]
        exact hrhs
      · simpa [Env.substFvar] using ihbody
  | @letRec env bindings body resultTy schemes avoid hlen hwf hgroup _ ihgroup ihbody =>
      let schemes' := schemes.map (PolyTy.substFvar Z U)
      let avoid' := [Z] ++ avoid
      apply RunWT.letRec (schemes := schemes') (avoid := avoid')
      · simpa [schemes'] using hlen
      · intro scheme' hscheme'
        obtain ⟨scheme, hscheme, rfl⟩ := List.mem_map.mp hscheme'
        exact (hwf scheme hscheme).substFvar hU
      · intro names hfresh pair hpair
        have hfresh0 : FreshNames avoid (PolyTy.totalParams schemes) names := by
          have := FreshNames.of_append_left hfresh
          simpa [avoid', schemes', PolyTy.totalParams_map_substFvar] using this
        have hZ : Z ∉ names :=
          FreshNames.not_mem_of_mem_avoid hfresh (by simp [avoid'])
        rw [PolyTy.openGroup_map_substFvar hU schemes hZ] at hpair
        rw [List.zip_map_right] at hpair
        obtain ⟨oldPair, holdPair, rfl⟩ := List.mem_map.mp hpair
        have htyped := ihgroup names hfresh0 oldPair holdPair
        simpa [schemes', Env.substFvar, Env.substFvar_append] using htyped
      · simpa [schemes', Env.substFvar, Env.substFvar_append] using ihbody

private def substFvarsEnv : List (Nat × Ty) → Env → Env
  | [], env => env
  | (name, replacement) :: rest, env =>
      substFvarsEnv rest (env.substFvar name replacement)

private theorem RunWT.substFvars {env : Env} {e : RunExpr} {ty : Ty}
    {pairs : List (Nat × Ty)}
    (hlc : ∀ pair ∈ pairs, pair.2.IsLC) (h : RunWT env e ty) :
    RunWT (substFvarsEnv pairs env) e (Ty.substFvars pairs ty) := by
  induction pairs generalizing env ty with
  | nil => simpa [substFvarsEnv, Ty.substFvars] using h
  | cons pair rest ih =>
      obtain ⟨name, replacement⟩ := pair
      simp only [substFvarsEnv, Ty.substFvars]
      exact ih (fun pair hpair => hlc pair (List.mem_cons_of_mem _ hpair))
        (h.substFvar (hlc (name, replacement) List.mem_cons_self))

private theorem substFvarsEnv_eq_self_of_fresh {pairs : List (Nat × Ty)}
    {env : Env} (hfresh : ∀ pair ∈ pairs, pair.1 ∉ env.freeVars) :
    substFvarsEnv pairs env = env := by
  induction pairs generalizing env with
  | nil => rfl
  | cons pair rest ih =>
      obtain ⟨name, replacement⟩ := pair
      simp only [substFvarsEnv]
      rw [Env.substFvar_fresh (hfresh (name, replacement) List.mem_cons_self)]
      exact ih (fun pair hpair => hfresh pair (List.mem_cons_of_mem _ hpair))

/-- A machine term has a scheme when it has every locally closed instance.
The quantification belongs to the typing proof, never to runtime syntax. -/
def RunHasScheme (env : Env) (value : RunExpr) (scheme : PolyTy) : Prop :=
  ∀ args, InstArgs scheme args → RunWT env value (scheme.openWith args)

private theorem pairs_zip_values_lc {names : List Nat} {args : List Ty}
    (hlc : ∀ arg ∈ args, arg.IsLC) :
    ∀ pair ∈ names.zip args, pair.2.IsLC := by
  intro pair hpair
  exact hlc pair.2 (List.of_mem_zip hpair).2

private theorem pairs_zip_names_fresh {names : List Nat} {args : List Ty}
    {env : Env} (hfresh : ∀ name ∈ names, name ∉ env.freeVars) :
    ∀ pair ∈ names.zip args, pair.1 ∉ env.freeVars := by
  intro pair hpair
  exact hfresh pair.1 (List.of_mem_zip hpair).1

/-- Cofinite rigid checking entails every concrete instance. -/
theorem RunHasScheme.ofGeneralisesTo {env : Env} {rhs : RunExpr}
    {scheme : PolyTy} {avoid : List Nat} (_hwf : scheme.WF)
    (h : RunGeneralisesTo RunWT env scheme rhs avoid) :
    RunHasScheme env rhs scheme := by
  intro args hargs
  obtain ⟨names, hlen, hnodup, hfresh⟩ := exists_fresh_names
    (avoid ++ env.freeVars ++ scheme.body.freeVars ++ Ty.freeVarsList args)
    scheme.paramCount
  have hcofinite : FreshNames avoid scheme.paramCount names :=
    ⟨hlen, hnodup, fun x hx hmem => hfresh x hx (by simp [hmem])⟩
  have htyped := h names hcofinite
  have hnames_env : ∀ x ∈ names, x ∉ env.freeVars := by
    intro x hx hmem
    exact hfresh x hx (by simp [List.mem_append, hmem])
  have hnames_body : ∀ x ∈ names, x ∉ scheme.body.freeVars := by
    intro x hx hmem
    exact hfresh x hx (by simp [List.mem_append, hmem])
  have hnames_args : ∀ x ∈ names, x ∉ Ty.freeVarsList args := by
    intro x hx hmem
    exact hfresh x hx (by simp [List.mem_append, hmem])
  have hsub := RunWT.substFvars (pairs := names.zip args)
    (pairs_zip_values_lc (names := names) hargs.2) htyped
  rw [substFvarsEnv_eq_self_of_fresh
    (pairs_zip_names_fresh hnames_env)] at hsub
  have hopen := Ty.openWith_eq_substFvars_openVars
    (ty := scheme.body) (Vs := args) (Xs := names)
    (⟨hargs.1.trans hlen.symm, hargs.2⟩ : Ty.AreLC names.length args)
    hnodup hnames_body hnames_args
  simpa [PolyTy.openVars, PolyTy.openWith, hopen] using hsub

private theorem openGroup_zip_member {schemes : List PolyTy}
    {bindings : List RunExpr} {names : List Nat} {rhs : RunExpr}
    {scheme : PolyTy} (hnames : names.length = PolyTy.totalParams schemes)
    (hmember : (rhs, scheme) ∈ bindings.zip schemes) :
    ∃ memberNames,
      memberNames.length = scheme.paramCount ∧
      List.Sublist memberNames names ∧
      (rhs, scheme.openVars memberNames) ∈
        bindings.zip (PolyTy.openGroup schemes names) := by
  induction schemes generalizing bindings names with
  | nil => simp at hmember
  | cons headScheme tailSchemes ih =>
      cases bindings with
      | nil => simp at hmember
      | cons headRhs tailBindings =>
          simp only [List.zip_cons_cons, List.mem_cons] at hmember ⊢
          rcases hmember with hhead | htail
          · injection hhead with hrhs hscheme
            subst rhs
            subst scheme
            refine ⟨names.take headScheme.paramCount, ?_,
              List.take_sublist headScheme.paramCount names, ?_⟩
            · rw [List.length_take, min_eq_left]
              simp only [PolyTy.totalParams, List.map_cons, List.sum_cons] at hnames
              omega
            · simp only [PolyTy.openGroup, List.zip_cons_cons, List.mem_cons]
              exact Or.inl trivial
          · have hdrop : (names.drop headScheme.paramCount).length =
                PolyTy.totalParams tailSchemes := by
              rw [List.length_drop]
              simp only [PolyTy.totalParams, List.map_cons, List.sum_cons] at hnames ⊢
              omega
            obtain ⟨memberNames, hmemberLen, hsub, hopened⟩ :=
              ih hdrop htail
            refine ⟨memberNames, hmemberLen,
              hsub.trans (List.drop_sublist headScheme.paramCount names), ?_⟩
            simp only [PolyTy.openGroup, List.zip_cons_cons, List.mem_cons]
            exact Or.inr hopened

/-- Every recursive member can be rewrapped at every instance of its declared
scheme.  The wrapper retains the schemes only in this derivation. -/
theorem RunHasScheme.ofRecMember {env : Env} {schemes : List PolyTy}
    {bindings : List RunExpr} {avoid : List Nat} {rhs : RunExpr}
    {scheme : PolyTy}
    (hlen : bindings.length = schemes.length)
    (hwf : ∀ scheme ∈ schemes, scheme.WF)
    (hgroup : RunRecGroupChecks RunWT env schemes bindings avoid)
    (hmember : (rhs, scheme) ∈ bindings.zip schemes) :
    RunHasScheme env (.letRec bindings rhs) scheme := by
  intro args hargs
  obtain ⟨names, hnamesLen, hnamesNodup, hnamesFresh⟩ := exists_fresh_names
    (avoid ++ Env.freeVars (schemes ++ env) ++ scheme.body.freeVars ++ Ty.freeVarsList args)
    (PolyTy.totalParams schemes)
  have hfresh : FreshNames avoid (PolyTy.totalParams schemes) names :=
    ⟨hnamesLen, hnamesNodup, fun x hx hmem => hnamesFresh x hx (by simp [hmem])⟩
  obtain ⟨memberNames, hmemberLen, hmemberSub, hopenedMember⟩ :=
    openGroup_zip_member hnamesLen hmember
  have htyped := hgroup names hfresh _ hopenedMember
  have hmemberNodup : memberNames.Nodup := hnamesNodup.sublist hmemberSub
  have hmemberEnv : ∀ x ∈ memberNames, x ∉ Env.freeVars (schemes ++ env) := by
    intro x hx hmem
    exact hnamesFresh x (hmemberSub.subset hx) (by simp [List.mem_append, hmem])
  have hmemberBody : ∀ x ∈ memberNames, x ∉ scheme.body.freeVars := by
    intro x hx hmem
    exact hnamesFresh x (hmemberSub.subset hx) (by simp [List.mem_append, hmem])
  have hmemberArgs : ∀ x ∈ memberNames, x ∉ Ty.freeVarsList args := by
    intro x hx hmem
    exact hnamesFresh x (hmemberSub.subset hx) (by simp [List.mem_append, hmem])
  have hsub := RunWT.substFvars (pairs := memberNames.zip args)
    (pairs_zip_values_lc (names := memberNames) hargs.2) htyped
  rw [substFvarsEnv_eq_self_of_fresh
    (pairs_zip_names_fresh hmemberEnv)] at hsub
  have hopen := Ty.openWith_eq_substFvars_openVars
    (ty := scheme.body) (Vs := args) (Xs := memberNames)
    (⟨hargs.1.trans hmemberLen.symm, hargs.2⟩ : Ty.AreLC memberNames.length args)
    hmemberNodup hmemberBody hmemberArgs
  apply RunWT.letRec (schemes := schemes) (avoid := avoid) hlen hwf hgroup
  simpa [PolyTy.openVars, PolyTy.openWith, hopen] using hsub

@[simp] private theorem shiftGroup_eq_map (threshold amount : Nat)
    (bindings : List RunExpr) :
    shiftGroup threshold amount bindings =
      bindings.map (RunExpr.shiftFrom threshold amount) := by
  induction bindings with
  | nil => rfl
  | cons rhs rest ih => simp [shiftGroup, ih]

/-- Inserting a term environment segment and shifting de Bruijn indices
preserves erased-runtime typing. -/
theorem RunWT.weakenEnv {envPre envExtra env : Env} {e : RunExpr} {ty : Ty}
    (h : RunWT (envPre ++ env) e ty) :
    RunWT (envPre ++ envExtra ++ env)
      (e.shiftFrom envPre.length envExtra.length) ty := by
  suffices H : ∀ {env0 : Env} {e0 : RunExpr} {ty0 : Ty}, RunWT env0 e0 ty0 →
      ∀ pre : Env, env0 = pre ++ env →
        RunWT (pre ++ envExtra ++ env)
          (e0.shiftFrom pre.length envExtra.length) ty0 by
    exact H h envPre rfl
  intro env0 e0 ty0 hd
  induction hd with
  | int => intro pre _; exact .int
  | @var env0 index scheme args hlookup hargs =>
      intro pre henv
      rw [henv] at hlookup
      simp only [RunExpr.shiftFrom]
      by_cases hlt : index < pre.length
      · rw [if_pos hlt]
        refine .var ?_ hargs
        rw [List.getElem?_append_left
          (by simp only [List.length_append]; omega : index < (pre ++ envExtra).length),
          List.getElem?_append_left hlt]
        rwa [List.getElem?_append_left hlt] at hlookup
      · rw [if_neg hlt]
        refine .var ?_ hargs
        rw [List.getElem?_append_right
          (by simp only [List.length_append]; omega :
            (pre ++ envExtra).length ≤ index + envExtra.length)]
        rw [show index + envExtra.length - (pre ++ envExtra).length =
              index - pre.length by simp only [List.length_append]; omega]
        rwa [List.getElem?_append_right (by omega)] at hlookup
  | @lam paramTy env0 body resultTy _ ih =>
      intro pre henv
      simp only [RunExpr.shiftFrom]
      have hb := ih (PolyTy.mkTrivial paramTy :: pre) (by rw [henv, List.cons_append])
      simpa only [List.cons_append, List.length_cons] using RunWT.lam hb
  | app _ _ ihfn iharg =>
      intro pre henv
      exact .app (ihfn pre henv) (iharg pre henv)
  | @letIn env0 rhs body resultTy scheme avoid hwf hgen _ ihgen ihbody =>
      intro pre henv
      simp only [RunExpr.shiftFrom]
      apply RunWT.letIn (scheme := scheme) (avoid := avoid) hwf
      · intro names hfresh
        exact ihgen names hfresh pre henv
      · have hb := ihbody (scheme :: pre) (by rw [henv, List.cons_append])
        simpa only [List.cons_append, List.length_cons] using hb
  | @letRec env0 bindings body resultTy schemes avoid hlen hwf hgroup _ ihgroup ihbody =>
      intro pre henv
      simp only [RunExpr.shiftFrom, shiftGroup_eq_map]
      apply RunWT.letRec (schemes := schemes) (avoid := avoid)
      · simpa using hlen
      · exact hwf
      · intro names hfresh pair hpair
        rw [List.zip_map_left] at hpair
        obtain ⟨oldPair, holdPair, rfl⟩ := List.mem_map.mp hpair
        have ht := ihgroup names hfresh oldPair holdPair
          (schemes ++ pre) (by rw [henv, List.append_assoc])
        simp only [List.length_append] at ht
        rw [← hlen, Nat.add_comm bindings.length pre.length] at ht
        simpa only [List.append_assoc] using ht
      · have hb := ihbody (schemes ++ pre) (by rw [henv, List.append_assoc])
        simp only [List.length_append] at hb
        rw [← hlen, Nat.add_comm bindings.length pre.length] at hb
        simpa only [List.append_assoc] using hb

@[simp] private theorem substGroup_eq_map (depth : Nat) (values : List RunExpr)
    (bindings : List RunExpr) :
    substGroup depth values bindings =
      bindings.map (RunExpr.substN depth values) := by
  induction bindings with
  | nil => rfl
  | cons rhs rest ih => simp [substGroup, ih]

/-- Simultaneous substitution of terms which inhabit every instance of their
schemes.  This is the operational heart of recursive unfolding. -/
theorem RunWT.substMany {envPre env : Env} {schemes : List PolyTy}
    {values : List RunExpr} {e : RunExpr} {ty : Ty}
    (hvalues : List.Forall₂ (RunHasScheme env) values schemes)
    (h : RunWT (envPre ++ schemes ++ env) e ty) :
    RunWT (envPre ++ env) (e.substN envPre.length values) ty := by
  have hvaluesLen : values.length = schemes.length := hvalues.length_eq
  suffices H : ∀ {env0 : Env} {e0 : RunExpr} {ty0 : Ty}, RunWT env0 e0 ty0 →
      ∀ pre : Env, env0 = pre ++ schemes ++ env →
        RunWT (pre ++ env) (e0.substN pre.length values) ty0 by
    exact H h envPre rfl
  intro env0 e0 ty0 hd
  induction hd with
  | int => intro pre _; exact .int
  | @var env0 index scheme args hlookup hargs =>
      intro pre henv
      rw [henv] at hlookup
      rw [List.append_assoc] at hlookup
      simp only [RunExpr.substN]
      by_cases hlt : index < pre.length
      · rw [if_pos hlt]
        refine .var ?_ hargs
        rw [List.getElem?_append_left hlt]
        rwa [List.getElem?_append_left hlt] at hlookup
      · rw [if_neg hlt]
        by_cases hin : index - pre.length < values.length
        · rw [dif_pos hin]
          have hschemeLt : index - pre.length < schemes.length := by omega
          rw [List.getElem?_append_right (by omega),
            List.getElem?_append_left hschemeLt,
            List.getElem?_eq_getElem hschemeLt, Option.some.injEq] at hlookup
          subst scheme
          have hs : RunHasScheme env values[index - pre.length]
              schemes[index - pre.length] :=
            (List.forall₂_iff_get.mp hvalues).2 _ hin hschemeLt
          have hv := hs args hargs
          simpa only [List.nil_append] using
            (RunWT.weakenEnv (envPre := []) (envExtra := pre) hv)
        · rw [dif_neg hin]
          refine .var ?_ hargs
          rw [List.getElem?_append_right (by omega : pre.length ≤ index - values.length)]
          rw [List.getElem?_append_right (by omega),
            List.getElem?_append_right (by omega : schemes.length ≤ index - pre.length)]
            at hlookup
          rw [show index - values.length - pre.length =
              index - pre.length - schemes.length by omega]
          exact hlookup
  | @lam paramTy env0 body resultTy _ ih =>
      intro pre henv
      simp only [RunExpr.substN]
      have hb := ih (PolyTy.mkTrivial paramTy :: pre) (by
        rw [henv]
        simp only [List.cons_append, List.append_assoc])
      simpa only [List.cons_append, List.length_cons] using RunWT.lam hb
  | app _ _ ihfn iharg =>
      intro pre henv
      exact .app (ihfn pre henv) (iharg pre henv)
  | @letIn env0 rhs body resultTy scheme avoid hwf hgen _ ihgen ihbody =>
      intro pre henv
      simp only [RunExpr.substN]
      apply RunWT.letIn (scheme := scheme) (avoid := avoid) hwf
      · intro names hfresh
        exact ihgen names hfresh pre henv
      · have hb := ihbody (scheme :: pre) (by
          rw [henv]
          simp only [List.cons_append, List.append_assoc])
        simpa only [List.cons_append, List.length_cons] using hb
  | @letRec env0 bindings body resultTy recSchemes avoid hlen hwf hgroup _ ihgroup ihbody =>
      intro pre henv
      simp only [RunExpr.substN, substGroup_eq_map]
      apply RunWT.letRec (schemes := recSchemes) (avoid := avoid)
      · simpa using hlen
      · exact hwf
      · intro names hfresh pair hpair
        rw [List.zip_map_left] at hpair
        obtain ⟨oldPair, holdPair, rfl⟩ := List.mem_map.mp hpair
        have ht := ihgroup names hfresh oldPair holdPair
          (recSchemes ++ pre) (by rw [henv]; simp only [List.append_assoc])
        simp only [List.length_append] at ht
        rw [← hlen, Nat.add_comm bindings.length pre.length] at ht
        simpa only [List.append_assoc] using ht
      · have hb := ihbody (recSchemes ++ pre) (by
          rw [henv]
          simp only [List.append_assoc])
        simp only [List.length_append] at hb
        rw [← hlen, Nat.add_comm bindings.length pre.length] at hb
        simpa only [List.append_assoc] using hb

private theorem recursiveValuesHaveSchemes {env : Env}
    {schemes : List PolyTy} {bindings : List RunExpr} {avoid : List Nat}
    (hlen : bindings.length = schemes.length)
    (hwf : ∀ scheme ∈ schemes, scheme.WF)
    (hgroup : RunRecGroupChecks RunWT env schemes bindings avoid) :
    List.Forall₂ (RunHasScheme env)
      (bindings.map (fun rhs => .letRec bindings rhs)) schemes := by
  have hall : ∀ pair ∈ bindings.zip schemes,
      RunHasScheme env (.letRec bindings pair.1) pair.2 := by
    intro pair hpair
    exact RunHasScheme.ofRecMember hlen hwf hgroup hpair
  have go : ∀ (bs : List RunExpr) (ss : List PolyTy),
      bs.length = ss.length →
      (∀ pair ∈ bs.zip ss,
        RunHasScheme env (.letRec bindings pair.1) pair.2) →
      List.Forall₂ (RunHasScheme env)
        (bs.map (fun rhs => .letRec bindings rhs)) ss := by
    intro bs
    induction bs with
    | nil =>
        intro ss hlen _
        cases ss with
        | nil => exact .nil
        | cons _ _ => simp at hlen
    | cons rhs rest ih =>
        intro ss hlen hmembers
        cases ss with
        | nil => simp at hlen
        | cons scheme schemes =>
            refine .cons
              (hmembers (rhs, scheme) (by simp))
              (ih schemes (by simpa using hlen) ?_)
            intro pair hpair
            exact hmembers pair (by simp [hpair])
  exact go bindings schemes hlen hall

/-- Subject reduction for the type-free runtime.  Its only current step is
recursive unfolding; the recursive schemes are recovered solely from the
`RunWT` derivation. -/
theorem RunWT.preservation {env : Env} {e e' : RunExpr} {ty : Ty}
    (htyped : RunWT env e ty) (hstep : RunStep e e') :
    RunWT env e' ty := by
  cases hstep with
  | letRecUnfold =>
      cases htyped with
      | letRec hlen hwf hgroup hbody =>
          have hvalues := recursiveValuesHaveSchemes hlen hwf hgroup
          simpa only [List.nil_append] using
            (RunWT.substMany (envPre := []) hvalues hbody)

#print axioms RunWT.substFvar
#print axioms RunHasScheme.ofRecMember
#print axioms RunWT.substMany
#print axioms RunWT.preservation

/-! ## Headline witnesses -/

/-- `forall a. a -> Int`. -/
def polyConstInt : PolyTy := ⟨1, .arrow (.bvar 0) (.prim .int)⟩

/-- Once an enclosing annotation has been opened, its scoped variable is a rigid
free variable in a nested local scheme. -/
def nestedResult (outer : Nat) : PolyTy :=
  ⟨1, .arrow (.bvar 0) (.fvar outer)⟩

theorem polyConstInt_wf : polyConstInt.WF := by
  show ContainsBvarsUpTo 1 (.arrow (.bvar 0) (.prim .int))
  exact .arrow (.bvar (by simp)) .prim

theorem nestedResult_wf (outer : Nat) : (nestedResult outer).WF := by
  show ContainsBvarsUpTo 1 (.arrow (.bvar 0) (.fvar outer))
  exact .arrow (.bvar (by simp)) .fvar

/-- The canonical direct-self-use witness.  While checking `f` at arbitrary
`a`, its recursive occurrences instantiate the full `forall b. b -> Int`
scheme independently at `Int` and at the current `a`.

`f = fun x => (fun _ => f x) (f 0)`
-/
def selfPolyRhs : SourceExpr :=
  .lam (.app
    (.lam (.app (.var 2) (.var 1)))
    (.app (.var 1) (.int 0)))

theorem selfPolyRhs_typed :
    ∀ args, InstArgs polyConstInt args →
      SourceWT [polyConstInt] selfPolyRhs (polyConstInt.openWith args) := by
  intro args hargs
  obtain ⟨a, rfl⟩ : ∃ a, args = [a] := by
    apply List.length_eq_one_iff.mp
    simpa [InstArgs, polyConstInt] using hargs.1
  have ha : a.IsLC := hargs.2 a (by simp)
  change SourceWT [polyConstInt] selfPolyRhs (.arrow a (.prim .int))
  refine .lam ?_
  refine .app (argTy := .prim .int) (.lam (paramTy := .prim .int) ?_) ?_
  · refine .app (.var (index := 2) (scheme := polyConstInt) (args := [a]) (by rfl) ?_) ?_
    · exact ⟨by simp [polyConstInt], by simpa using ha⟩
    · have hx := SourceWT.var
        (env := [PolyTy.mkTrivial (.prim .int), PolyTy.mkTrivial a, polyConstInt])
        (index := 1) (scheme := PolyTy.mkTrivial a) (args := [])
        (by rfl) ⟨rfl, by simp⟩
      simpa [PolyTy.openWith, Ty.openWith, PolyTy.mkTrivial,
        Ty.instantiate_eq_self_of_lc ha] using hx
  · refine .app (.var (index := 1) (scheme := polyConstInt)
      (args := [.prim .int]) (by rfl) ?_) .int
    exact ⟨by simp [polyConstInt], by simp; exact ContainsBvarsUpTo.prim⟩

def selfPolySource : SourceExpr :=
  .letRec [polyConstInt] [selfPolyRhs] (.var 0)

theorem selfPolySource_typed :
    SourceWT [] selfPolySource (.arrow (.prim .int) (.prim .int)) := by
  apply SourceWT.letRec (avoid := []) (schemes := [polyConstInt])
    (bindings := [selfPolyRhs])
  · simp
  · intro scheme hscheme
    simp only [List.mem_singleton] at hscheme
    subst scheme
    exact polyConstInt_wf
  · intro names hfresh pair hpair
    have hnames : names.take polyConstInt.paramCount = names := by
      apply (List.take_eq_self_iff names).2
      have hlength : names.length = 1 := by
        simpa [PolyTy.totalParams, polyConstInt] using hfresh.length
      simp [polyConstInt, hlength]
    have hopen : selfPolyRhs.openTyVars
        (names.take polyConstInt.paramCount) = selfPolyRhs := by
      simp [selfPolyRhs, SourceExpr.openTyVars, SourceExpr.openTyVarsAux]
    have hpair' : pair =
        (selfPolyRhs,
          polyConstInt.openVars (names.take polyConstInt.paramCount)) := by
      simpa [SourceExpr.openRecRhsOwn, PolyTy.openGroup, hopen] using hpair
    subst pair
    have hargs : InstArgs polyConstInt (names.map Ty.fvar) := by
      constructor
      · simpa [polyConstInt] using hfresh.length
      · intro arg harg
        obtain ⟨name, _, rfl⟩ := List.mem_map.mp harg
        exact ContainsBvarsUpTo.fvar
    have hrhs := selfPolyRhs_typed (names.map Ty.fvar) hargs
    rw [hnames]
    simpa [PolyTy.openVars, Ty.openVars_eq_openWith] using hrhs
  · exact .var (index := 0) (scheme := polyConstInt) (args := [.prim .int]) rfl
      ⟨by simp [polyConstInt], by simp; exact ContainsBvarsUpTo.prim⟩

/-- The erased machine term is typable although it contains no occurrence of
`polyConstInt`; the scheme is retained only by the `RunWT` derivation produced
by `erase_sound`. -/
theorem selfPolyRuntime_typed :
    RunWT [] selfPolySource.erase (.arrow (.prim .int) (.prim .int)) :=
  SourceWT.erase_sound selfPolySource_typed

/-! ### Annotated sibling polymorphism

Both members of this group declare `forall a. a -> Int`.  While the first RHS
is being checked at its own rigid `a`, it instantiates the *second* member at
both `Int` and that rigid `a`:

`f = fun x => (fun _ => g x) (g 0)`
`g = fun _ => 0`

Thus this is genuinely in-block sibling polymorphism, rather than two uses made
only after the recursive group has been checked. -/

def siblingPolyCallerRhs : SourceExpr :=
  .lam (.app
    (.lam (.app (.var 3) (.var 1)))
    (.app (.var 2) (.int 0)))

def siblingPolyCalleeRhs : SourceExpr :=
  .lam (.int 0)

theorem siblingPolyCallerRhs_typed :
    ∀ args, InstArgs polyConstInt args →
      SourceWT [polyConstInt, polyConstInt] siblingPolyCallerRhs
        (polyConstInt.openWith args) := by
  intro args hargs
  obtain ⟨a, rfl⟩ : ∃ a, args = [a] := by
    apply List.length_eq_one_iff.mp
    simpa [InstArgs, polyConstInt] using hargs.1
  have ha : a.IsLC := hargs.2 a (by simp)
  change SourceWT [polyConstInt, polyConstInt] siblingPolyCallerRhs
    (.arrow a (.prim .int))
  refine .lam ?_
  refine .app (argTy := .prim .int) (.lam (paramTy := .prim .int) ?_) ?_
  · refine .app
      (.var (index := 3) (scheme := polyConstInt) (args := [a]) (by rfl) ?_)
      ?_
    · exact ⟨by simp [polyConstInt], by simpa using ha⟩
    · have hx := SourceWT.var
        (env := [PolyTy.mkTrivial (.prim .int), PolyTy.mkTrivial a,
          polyConstInt, polyConstInt])
        (index := 1) (scheme := PolyTy.mkTrivial a) (args := [])
        (by rfl) ⟨rfl, by simp⟩
      simpa [PolyTy.openWith, Ty.openWith, PolyTy.mkTrivial,
        Ty.instantiate_eq_self_of_lc ha] using hx
  · refine .app
      (.var (index := 2) (scheme := polyConstInt) (args := [.prim .int])
        (by rfl) ?_)
      .int
    exact ⟨by simp [polyConstInt], by simp; exact ContainsBvarsUpTo.prim⟩

theorem siblingPolyCalleeRhs_typed :
    ∀ args, InstArgs polyConstInt args →
      SourceWT [polyConstInt, polyConstInt] siblingPolyCalleeRhs
        (polyConstInt.openWith args) := by
  intro args hargs
  obtain ⟨a, rfl⟩ : ∃ a, args = [a] := by
    apply List.length_eq_one_iff.mp
    simpa [InstArgs, polyConstInt] using hargs.1
  change SourceWT [polyConstInt, polyConstInt] siblingPolyCalleeRhs
    (.arrow a (.prim .int))
  exact .lam .int

def siblingPolySource : SourceExpr :=
  .letRec [polyConstInt, polyConstInt]
    [siblingPolyCallerRhs, siblingPolyCalleeRhs]
    (.var 0)

theorem siblingPolySource_typed :
    SourceWT [] siblingPolySource (.arrow (.prim .int) (.prim .int)) := by
  apply SourceWT.letRec (avoid := [])
    (schemes := [polyConstInt, polyConstInt])
    (bindings := [siblingPolyCallerRhs, siblingPolyCalleeRhs])
  · simp
  · intro scheme hscheme
    simp at hscheme
    subst scheme
    exact polyConstInt_wf
  · intro names hfresh pair hpair
    obtain ⟨firstName, secondName, rfl⟩ :
        ∃ firstName secondName, names = [firstName, secondName] := by
      have hlength : names.length = 2 := by
        simpa [PolyTy.totalParams, polyConstInt] using hfresh.length
      cases names with
      | nil => simp at hlength
      | cons firstName rest =>
          cases rest with
          | nil => simp at hlength
          | cons secondName tail =>
              cases tail with
              | nil => exact ⟨firstName, secondName, rfl⟩
              | cons thirdName tail => simp at hlength
    simp [SourceExpr.openRecRhsOwn, polyConstInt,
      SourceExpr.openTyVars, PolyTy.openGroup] at hpair
    rcases hpair with rfl | rfl
    · have hargs : InstArgs polyConstInt [Ty.fvar firstName] := by
        exact ⟨by simp [polyConstInt], by simp; exact ContainsBvarsUpTo.fvar⟩
      simpa [polyConstInt, PolyTy.openVars, Ty.openVars,
        siblingPolyCallerRhs, SourceExpr.openTyVars,
        SourceExpr.openTyVarsAux] using siblingPolyCallerRhs_typed _ hargs
    · have hargs : InstArgs polyConstInt [Ty.fvar secondName] := by
        exact ⟨by simp [polyConstInt], by simp; exact ContainsBvarsUpTo.fvar⟩
      simpa [polyConstInt, PolyTy.openVars, Ty.openVars,
        siblingPolyCalleeRhs, SourceExpr.openTyVars,
        SourceExpr.openTyVarsAux] using siblingPolyCalleeRhs_typed _ hargs
  · exact .var (index := 0) (scheme := polyConstInt)
      (args := [.prim .int]) rfl
      ⟨by simp [polyConstInt], by simp; exact ContainsBvarsUpTo.prim⟩

/-- Erasure keeps the sibling-polymorphic group typable without retaining either
annotation in the runtime term. -/
theorem siblingPolyRuntime_typed :
    RunWT [] siblingPolySource.erase (.arrow (.prim .int) (.prim .int)) :=
  siblingPolySource_typed.erase_sound

/-- A post-opened nested scheme may combine its own quantified variable with an
ambient rigid variable, and erasure still removes all type information.  The
closed witness below uses this lemma after opening a genuinely enclosing
`forall`. -/
theorem ambient_rigid_erasure_witness (outer : Nat) :
    let scheme := nestedResult outer
    let rhs : SourceExpr := .lam (.var 2)
    SourceWT [PolyTy.mkTrivial (.fvar outer)]
      (.letRec [scheme] [rhs] (.var 0))
      (.arrow (.prim .int) (.fvar outer)) ∧
    RunWT [PolyTy.mkTrivial (.fvar outer)]
      (SourceExpr.erase (.letRec [scheme] [rhs] (.var 0)))
      (.arrow (.prim .int) (.fvar outer)) := by
  dsimp
  have hrhs : ∀ args, InstArgs (nestedResult outer) args →
      SourceWT (nestedResult outer :: [PolyTy.mkTrivial (.fvar outer)])
        (.lam (.var 2)) ((nestedResult outer).openWith args) := by
    intro args hargs
    obtain ⟨a, rfl⟩ : ∃ a, args = [a] := by
      apply List.length_eq_one_iff.mp
      simpa [InstArgs, nestedResult] using hargs.1
    change SourceWT _ (.lam (.var 2)) (.arrow a (.fvar outer))
    exact .lam (.var (index := 2) (scheme := PolyTy.mkTrivial (.fvar outer))
      (args := []) (by rfl) ⟨rfl, by simp⟩)
  have hsrc : SourceWT [PolyTy.mkTrivial (.fvar outer)]
      (.letRec [nestedResult outer] [.lam (.var 2)] (.var 0))
      (.arrow (.prim .int) (.fvar outer)) := by
    apply SourceWT.letRec (avoid := [outer]) (schemes := [nestedResult outer])
      (bindings := [.lam (.var 2)])
    · simp
    · intro scheme hscheme
      simp only [List.mem_singleton] at hscheme
      subst scheme
      exact nestedResult_wf outer
    · intro names hfresh pair hpair
      have hnames : names.take (nestedResult outer).paramCount = names := by
        apply (List.take_eq_self_iff names).2
        have hlength : names.length = 1 := by
          simpa [PolyTy.totalParams, nestedResult] using hfresh.length
        simp [nestedResult, hlength]
      have hopen : SourceExpr.openTyVars
          (names.take (nestedResult outer).paramCount) (.lam (.var 2)) =
          (.lam (.var 2) : SourceExpr) := by
        simp [SourceExpr.openTyVars, SourceExpr.openTyVarsAux]
      have hpair' : pair =
          ((.lam (.var 2) : SourceExpr),
            (nestedResult outer).openVars
              (names.take (nestedResult outer).paramCount)) := by
        simpa [SourceExpr.openRecRhsOwn, PolyTy.openGroup, hopen] using hpair
      subst pair
      have hargs : InstArgs (nestedResult outer) (names.map Ty.fvar) := by
        constructor
        · simpa [nestedResult] using hfresh.length
        · intro arg harg
          obtain ⟨name, _, rfl⟩ := List.mem_map.mp harg
          exact ContainsBvarsUpTo.fvar
      have hopened := hrhs (names.map Ty.fvar) hargs
      rw [hnames]
      simpa [PolyTy.openVars, Ty.openVars_eq_openWith] using hopened
    · exact .var (index := 0) (scheme := nestedResult outer)
        (args := [.prim .int]) rfl
        ⟨by simp [nestedResult], by simp; exact ContainsBvarsUpTo.prim⟩
  exact ⟨hsrc, hsrc.erase_sound⟩

/-! ### A genuinely scoped nested annotation

The source below is closed.  The outer `forall c` scopes through its RHS into
the nested annotation `forall a. a -> c`.  In de Bruijn form that nested `c` is
`.bvar 1`: its own `a` occupies `.bvar 0`.  When the outer scheme is checked at
rigid `C`, lockstep opening changes only `.bvar 1`, yielding
`nestedResult C = forall a. a -> C`. -/

/-- `forall c. c -> Int -> c`. -/
def scopedOuterScheme : PolyTy :=
  ⟨1, .arrow (.bvar 0) (.arrow (.prim .int) (.bvar 0))⟩

/-- Authored beneath the outer `c`: `forall a. a -> c`.  This scheme is not
closed in isolation; it becomes well formed when the enclosing annotation is
opened for checking. -/
def nestedAuthoredScheme : PolyTy :=
  ⟨1, .arrow (.bvar 0) (.bvar 1)⟩

def genuinelyScopedOuterRhs : SourceExpr :=
  .lam (.letRec [nestedAuthoredScheme] [.lam (.var 2)] (.var 0))

def genuinelyScopedSource : SourceExpr :=
  .letIn scopedOuterScheme genuinelyScopedOuterRhs (.var 0)

theorem scopedOuterScheme_wf : scopedOuterScheme.WF := by
  show ContainsBvarsUpTo 1
    (.arrow (.bvar 0) (.arrow (.prim .int) (.bvar 0)))
  exact .arrow (.bvar (by simp))
    (.arrow .prim (.bvar (by simp)))

theorem genuinelyScopedOuterRhs_open (outer : Nat) :
    genuinelyScopedOuterRhs.openTyVars [outer] =
      .lam (.letRec [nestedResult outer] [.lam (.var 2)] (.var 0)) := by
  simp [genuinelyScopedOuterRhs, nestedAuthoredScheme, nestedResult,
    SourceExpr.openTyVars, SourceExpr.openTyVarsAux,
    openRecGroupTyVarsAux, Ty.openTyFrom, Ty.instantiate]

theorem genuinelyScopedSource_typed :
    SourceWT [] genuinelyScopedSource
      (.arrow (.prim .int) (.arrow (.prim .int) (.prim .int))) := by
  apply SourceWT.letIn (avoid := []) scopedOuterScheme_wf
  · intro names hfresh
    obtain ⟨outer, rfl⟩ : ∃ outer, names = [outer] := by
      apply List.length_eq_one_iff.mp
      simpa [scopedOuterScheme] using hfresh.length
    rw [genuinelyScopedOuterRhs_open]
    have hinner := (ambient_rigid_erasure_witness outer).1
    have hlambda := SourceWT.lam hinner
    simpa [scopedOuterScheme, PolyTy.openVars, Ty.openVars] using hlambda
  · exact .var (index := 0) (scheme := scopedOuterScheme)
      (args := [.prim .int]) rfl
      ⟨by simp [scopedOuterScheme], by simp; exact ContainsBvarsUpTo.prim⟩

/-- The closed source witness transports to a runtime term containing neither
the outer scheme nor the nested recursive scheme. -/
theorem genuinelyScopedRuntime_typed :
    RunWT [] genuinelyScopedSource.erase
      (.arrow (.prim .int) (.arrow (.prim .int) (.prim .int))) :=
  genuinelyScopedSource_typed.erase_sound

#print axioms SourceWT.erase_sound
#print axioms selfPolyRuntime_typed
#print axioms siblingPolyRuntime_typed
#print axioms ambient_rigid_erasure_witness
#print axioms genuinelyScopedRuntime_typed

end AnnotatedPolyRecErasure
