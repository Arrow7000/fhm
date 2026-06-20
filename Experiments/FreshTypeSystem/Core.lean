import Mathlib
import Experiments.HasItem


/-- Name of a type -/
inductive TyName
  | mk (str : String)
  deriving DecidableEq, Repr

/-- Name of a type constructor -/
inductive CtorName
  | mk (str : String)
  deriving DecidableEq, Repr

/-- Name of a value binding (or type variable) -/
inductive ValName
  | mk (str : String)
  deriving DecidableEq, Repr







abbrev LookupList (key : Type) (value : Type) := List (key × value)

namespace LookupList

def get? {k v} [DecidableEq k] (l : LookupList k v) (key : k) :=
  match l with
  | [] => none
  | ⟨key', val⟩ :: rest =>
    if key = key' then some val else get? rest key

/-- Proof that lookup list `l` contains the given key -/
inductive HasKey {k v : Type} (key : k) : (l : LookupList k v) → Prop
  | here : HasKey key (⟨key, val⟩ :: rest)
  | there : HasKey key l → HasKey key (⟨key', val⟩ :: l)

/-- Proof that lookup list `l` contains the given value at the specified key -/
inductive Has {k v : Type} (key : k) (val : v) : (l : LookupList k v) → Prop
  | here : Has key val (⟨key, val⟩ :: rest)
  | there : Has key val l → Has key val (⟨key', val'⟩ :: l)

end LookupList










inductive PrimTy
  | unit
  | int
  | nat
  | str
  deriving DecidableEq, Repr


inductive Ty
  | prim : PrimTy → Ty
  | arrow : (from_ to_ : Ty) → Ty
  /-- Bound var – only makes sense within the context of a polytype -/
  | bvar : Nat → Ty
  /-- Free var – unbound var. In spec-land this signifies an unconstrained variable. In algorithm-land this is a unification variable. -/
  | fvar : Nat → Ty
  /-- A custom type with its type params -/
  | customTy : TyName → List Ty → Ty
  deriving Repr



structure PolyTy where
  paramCount : Nat
  /-- May reference params by `.bvar`s in range of `paramCount`  -/
  body : Ty

/-- Make a polytype with no type vars -/
def PolyTy.mkTrivial (bodyTy : Ty) : PolyTy :=
  { paramCount := 0, body := bodyTy }





/-- `ty` can only contain `bvar`s that are lower than `n`. If `n = 0` `ty` contains no `bvar`s at all. -/
inductive ContainsBvarsUpTo (n : Nat) : (ty : Ty) → Prop
  | prim :
    ContainsBvarsUpTo n (.prim p)

  | arrow :
    ContainsBvarsUpTo n fst →
    ContainsBvarsUpTo n snd →
    ContainsBvarsUpTo n (.arrow fst snd)

  | fvar :
    ContainsBvarsUpTo n (.fvar i)

  | customTy :
    (∀ ty ∈ tys, ContainsBvarsUpTo n ty) →
    ContainsBvarsUpTo n (.customTy name tys)

  | bvar :
    i < n →
    ContainsBvarsUpTo n (.bvar i)



/-- ty contains no `fvar`s at all -/
inductive NoFreeVars : (ty : Ty) → Prop
  | prim :
    NoFreeVars (.prim p)

  | arrow :
    NoFreeVars fst →
    NoFreeVars snd →
    NoFreeVars (.arrow fst snd)

  | customTy :
    (∀ ty ∈ tys, NoFreeVars ty) →
    NoFreeVars (.customTy name tys)

  | bvar :
    NoFreeVars (.bvar i)







/-- A constructor for a type. E.g. `Result.Ok`, `Maybe.Some`, `Maybe.None` -/
structure Ctor where
  /-- How many type params the type has -/
  paramCount : Nat
  /-- The name of the type this is a constructor for -/
  tyName : TyName
  /-- What this constructor actually contains.
      Can reference `.bvar`s in range of `paramCount` -/
  contents : List Ty
  /-- Proof that all tys are appropriately bound -/
  bound : ∀ ty ∈ contents, ContainsBvarsUpTo paramCount ty
  /-- Contains no free vars -/
  closed : ∀ ty ∈ contents, NoFreeVars ty

/-- Which type constructors exist -/
abbrev CtorEnv := LookupList CtorName Ctor





/-- Maps from de Bruijn index of value bindings to their types -/
abbrev Env := List PolyTy










/-- Primitive literals -/
inductive PrimLitExpr
  | unit : PrimLitExpr
  | int : Int → PrimLitExpr
  | nat : Nat → PrimLitExpr
  | str : String → PrimLitExpr



inductive MatchPattern
  /-- `contents` is basically just a binding range. i.e. if 2 this means we've bound 2 new "names" to the context -/
  | named (ctor : CtorName) (contents : Nat)
  | wildcard
  deriving DecidableEq, Repr

/-- How many variables a branch pattern binds: a `named` ctor binds its
    `contents`-many fields; `wildcard` binds nothing. -/
def MatchPattern.bindCount : MatchPattern → Nat
  | .named _ n => n
  | .wildcard  => 0

/-- Does this branch pattern fire for constructor `name` of the given `arity`?
    A `named` pattern matches its exact ctor+arity; `wildcard` matches anything. -/
def MatchPattern.matchesCtor : MatchPattern → CtorName → Nat → Bool
  | .named c n, name, arity => c == name && n == arity
  | .wildcard,  _,    _     => true


/-- An expression in our language -/
inductive Expr
  | primLit (prim : PrimLitExpr)
  /-- A lambda. `paramAnn` is an optional type ascription on the parameter
      (surface `λ(x : T). body`); `none` means the param type is inferred. -/
  | lambda (paramAnn : Option Ty) (body : Expr)
  | app (f input : Expr)
  /-- A let binding. `ann` is an optional scheme ascription on the bound
      expression (surface `let x : σ = e in body`); `none` means the scheme is
      generalised by inference. -/
  | letIn (ann : Option PolyTy) (bindingExpr body : Expr)
  | var (deBruijnIndex : Nat)
  /-- A type constructor -/
  | ctor (name : CtorName)
  | match_ (scrutinee : Expr) (branches : List (MatchPattern × Expr))







/-- Build `[.bvar start, .bvar (start+1), ..., .bvar (start+count-1)]`. -/
def Ty.bvarRangeFrom (start : Nat) : Nat → List Ty
  | 0     => []
  | n + 1 => .bvar start :: bvarRangeFrom (start + 1) n


/-- Build `[.bvar 0, .bvar 1, ..., .bvar (count-1)]`. -/
def Ty.bvarRange : Nat → List Ty :=
  Ty.bvarRangeFrom 0


/-- Wrap a list of argument types in right-nested arrows ending at a result type:

    `[a₁, a₂, ..., aₙ]`, `r` ↦ `a₁ → a₂ → ... → aₙ → r`. -/
def Ty.wrapArrows (result : Ty) : List Ty → Ty
  | []          => result
  | arg :: rest => .arrow arg (wrapArrows result rest)

/--
  Convert a constructor entry to its polytype.

  E.g. for `Result.ok`:
    `{ paramCount := 2, tyName := Result, contents := [.bvar 1] }`

  produces the polytype `∀ e t. t → Result e t`:
    `{ paramCount := 2,
       body       := .arrow (.bvar 1)
                            (.customTy Result [.bvar 0, .bvar 1]) }`. -/
def Ctor.toTy (ctor : Ctor) : PolyTy :=
  let resultTy :=
    Ty.customTy ctor.tyName (Ty.bvarRange ctor.paramCount)

  let body := Ty.wrapArrows resultTy ctor.contents
  { paramCount := ctor.paramCount, body }












/-- Full context. Contains both bindings and type constructors maps. -/
structure Ctx where
  /-- Value bindings -/
  env : Env
  /-- Which type constructors exist here -/
  ctors : CtorEnv




mutual

/-- Get all the `.fvar`s from the `Ty`, deduped -/
def Ty.freeVars : Ty → List Nat
  | .prim _ => []
  | .arrow a b => (a.freeVars ++ b.freeVars).dedup
  | .fvar n => [n]
  | .bvar _ => []
  | .customTy _ tys => TyList.freeVars tys

def TyList.freeVars : List Ty → List Nat
  | [] => []
  | head :: tail => (head.freeVars ++ TyList.freeVars tail).dedup

end


mutual
/-- A *closed monotype*: no free **and** no bound type variables. This is the
    decidable check used to validate parameter annotations (`λ(x : T). …`),
    which must be closed (`Ty.isClosed_iff`: `↔ NoFreeVars ∧ ContainsBvarsUpTo 0`). -/
def Ty.isClosed : Ty → Bool
  | .prim _          => true
  | .arrow a b       => a.isClosed && b.isClosed
  | .fvar _          => false
  | .bvar _          => false
  | .customTy _ tys  => TyList.isClosed tys
def TyList.isClosed : List Ty → Bool
  | []      => true
  | t :: ts => t.isClosed && TyList.isClosed ts
end

theorem TyList.isClosed_iff_forall (tys : List Ty) :
    TyList.isClosed tys = true ↔ ∀ t ∈ tys, t.isClosed = true := by
  induction tys with
  | nil => simp [TyList.isClosed]
  | cons hd tl ih =>
    simp only [TyList.isClosed, Bool.and_eq_true, List.mem_cons]
    rw [ih]
    constructor
    · rintro ⟨hhd, htl⟩ t (rfl | ht)
      · exact hhd
      · exact htl t ht
    · intro h
      exact ⟨h hd (Or.inl rfl), fun t ht => h t (Or.inr ht)⟩



def Env.freeVars : Env → List Nat
  | [] => []
  | polyTy :: tail =>
    (polyTy.body.freeVars ++ freeVars tail).dedup


mutual

/-- For every `.fvar i`, if `i < vars.length`, replace the `.fvar` with `.bvar vars[i]`.

In other words, remove the given free vars and bind them back up. I.e. close them up, to make a polytype with `vars.length` binders ✨ -/
def Ty.closeOver (vars : List Nat) : Ty → Ty
  | .prim p          => .prim p
  | .arrow a b       => .arrow (a.closeOver vars) (b.closeOver vars)
  | .bvar i          => .bvar i
  | .customTy nm tys => .customTy nm (TyList.closeOver vars tys)
  | .fvar n          =>
      match vars.idxOf? n with
      | some i => .bvar i
      | none   => .fvar n


def TyList.closeOver (vars : List Nat) : List Ty → List Ty
  | []        => []
  | hd :: tl  => hd.closeOver vars :: TyList.closeOver vars tl

end

private lemma List.findIdx?_go_lt {p : α → Bool} {l : List α} {n i : Nat}
    (h : List.findIdx?.go p l n = some i) : i - n < l.length := by
  induction l generalizing n with
  | nil => simp [List.findIdx?.go] at h
  | cons hd tl ih =>
    simp [List.findIdx?.go] at h
    split at h
    · simp at h;
      subst h
      simp
    · have := ih h; simp; omega

private lemma List.idxOf?_lt_length {a : α} [BEq α] {l : List α} {i : Nat}
    (h : l.idxOf? a = some i) : i < l.length := by
  have := List.findIdx?_go_lt (n := 0) h
  omega

/-- Closing doesn't add any more bvars than it is expected to -/
theorem Ty.closeOver_preserves_bvars : ContainsBvarsUpTo 0 ty → ContainsBvarsUpTo vars.length (ty.closeOver vars) := by
  intro prem
  induction ty using Ty.closeOver.induct vars (motive_2 := fun tys ↦ (∀ t ∈ tys, ContainsBvarsUpTo 0 t) → ∀ t ∈ tys, ContainsBvarsUpTo vars.length (t.closeOver vars)) with
  | case1 =>
    simp [closeOver]
    constructor
  | case2 a b aih bih =>
    cases prem
    tauto
  | case3 =>
    simp [closeOver]
    constructor
    cases prem
    omega
  | case4 nm tys ih =>
    cases prem
    constructor
    intro ty tyin
    have : ∀ l, TyList.closeOver vars l = l.map (Ty.closeOver vars) := by
      intro l; induction l with
      | nil => simp [TyList.closeOver]
      | cons hd tl ihl => simp [TyList.closeOver, ihl]
    rw [this] at tyin
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp tyin
    exact ih (by assumption) t ht
  | case5 n i hsome =>
    rw [Ty.closeOver.eq_5]
    simp [hsome]
    refine .bvar ?_
    exact List.idxOf?_lt_length hsome
  | case6 n hnone =>
    rw [Ty.closeOver.eq_5]
    simp [hnone]
    exact .fvar
  | case7 =>
    rename_i h
    simp at h
  | case8 arg rest ih_arg ih_rest =>
    rename_i hall t ht
    simp [List.mem_cons] at ht
    rcases ht with rfl | ht
    · exact ih_arg (hall _ (by simp))
    · exact ih_rest (fun t ht => hall t (List.mem_cons_of_mem _ ht)) t ht


/--
Strong induction principle for `Ty` that gives a useful IH for the `customTy`
case: `(∀ t ∈ tys, motive t)`, rather than the bare `motive tys` you'd get from
the auto-generated recursor (which doesn't recurse into the embedded `List Ty`).

Usage:
```
theorem some_property : ∀ ty : Ty, P ty := by
  intro ty
  induction ty using Ty.rec_strong
  case prim p           => ...
  case arrow a b iha ihb => ...
  case bvar n           => ...
  case fvar n           => ...
  case customTy nm tys ih => ...   -- ih : ∀ t ∈ tys, P t
```
-/
@[elab_as_elim]
def Ty.rec_strong.{u} {motive : Ty → Sort u}
    (prim     : ∀ p, motive (.prim p))
    (arrow    : ∀ a b, motive a → motive b → motive (.arrow a b))
    (bvar     : ∀ n, motive (.bvar n))
    (fvar     : ∀ n, motive (.fvar n))
    (customTy : ∀ nm tys, (∀ t ∈ tys, motive t) → motive (.customTy nm tys)) :
    (ty : Ty) → motive ty
  | .prim p          => prim p
  | .arrow a b       =>
      arrow a b
        (Ty.rec_strong prim arrow bvar fvar customTy a)
        (Ty.rec_strong prim arrow bvar fvar customTy b)
  | .bvar n          => bvar n
  | .fvar n          => fvar n
  | .customTy nm tys =>
      customTy nm tys
        (fun t _ht => Ty.rec_strong prim arrow bvar fvar customTy t)
termination_by ty => sizeOf ty
decreasing_by
  all_goals simp_wf
  all_goals first
    | omega
    | (have := List.sizeOf_lt_of_mem _ht; omega)

theorem Ty.isClosed_iff (t : Ty) :
    t.isClosed = true ↔ NoFreeVars t ∧ ContainsBvarsUpTo 0 t := by
  induction t using Ty.rec_strong with
  | prim p => exact iff_of_true rfl ⟨.prim, .prim⟩
  | fvar n =>
    refine iff_of_false (by simp [Ty.isClosed]) ?_
    rintro ⟨hnfv, _⟩; cases hnfv
  | bvar i =>
    refine iff_of_false (by simp [Ty.isClosed]) ?_
    rintro ⟨_, hbv⟩; cases hbv with | bvar h => omega
  | arrow a b iha ihb =>
    simp only [Ty.isClosed, Bool.and_eq_true]
    rw [iha, ihb]
    constructor
    · rintro ⟨⟨na, ca⟩, nb, cb⟩; exact ⟨.arrow na nb, .arrow ca cb⟩
    · rintro ⟨hn, hc⟩
      cases hn with | arrow na nb => cases hc with | arrow ca cb => exact ⟨⟨na, ca⟩, nb, cb⟩
  | customTy name tys ih =>
    show TyList.isClosed tys = true ↔ _
    rw [TyList.isClosed_iff_forall]
    constructor
    · intro h
      refine ⟨.customTy fun t ht => ((ih t ht).mp (h t ht)).1,
              .customTy fun t ht => ((ih t ht).mp (h t ht)).2⟩
    · rintro ⟨hn, hc⟩ t ht
      cases hn with
      | customTy hn' => cases hc with
        | customTy hc' => exact (ih t ht).mpr ⟨hn' t ht, hc' t ht⟩


/--
Strong induction principle for `Expr` that gives a useful IH for the `match_`
case: `(∀ pat e, (pat, e) ∈ branches → motive e)`, rather than the bare
`motive branches` you'd get from the auto-generated recursor (which doesn't
recurse into the embedded `List (MatchPattern × Expr)`).

Usage:
```
theorem some_property : ∀ e : Expr, P e := by
  intro e
  induction e using Expr.rec_strong
  case primLit p                       => ...
  case lambda paramAnn body ih         => ...
  case app f input ihf ihi             => ...
  case letIn ann be body ihbe ihbo     => ...
  case var n                           => ...
  case ctor nm                         => ...
  case match_ scrutinee branches ihs ihbs => ...
    -- ihbs : ∀ pat e, (pat, e) ∈ branches → P e
```
-/
@[elab_as_elim]
def Expr.rec_strong.{u} {motive : Expr → Sort u}
    (primLit    : ∀ p, motive (.primLit p))
    (lambda     : ∀ paramAnn body, motive body → motive (.lambda paramAnn body))
    (app        : ∀ f input, motive f → motive input → motive (.app f input))
    (letIn      : ∀ ann bindingExpr body,
                    motive bindingExpr → motive body →
                    motive (.letIn ann bindingExpr body))
    (var        : ∀ n, motive (.var n))
    (ctor       : ∀ nm, motive (.ctor nm))
    (match_     : ∀ scrutinee branches,
                    motive scrutinee →
                    (∀ pat e, (pat, e) ∈ branches → motive e) →
                    motive (.match_ scrutinee branches)) :
    (e : Expr) → motive e
  | .primLit p          => primLit p
  | .lambda paramAnn body        =>
      lambda paramAnn body
        (Expr.rec_strong primLit lambda app letIn var ctor match_ body)
  | .app f input        =>
      app f input
        (Expr.rec_strong primLit lambda app letIn var ctor match_ f)
        (Expr.rec_strong primLit lambda app letIn var ctor match_ input)
  | .letIn ann be body      =>
      letIn ann be body
        (Expr.rec_strong primLit lambda app letIn var ctor match_ be)
        (Expr.rec_strong primLit lambda app letIn var ctor match_ body)
  | .var n              => var n
  | .ctor nm            => ctor nm
  | .match_ scrutinee branches =>
      match_ scrutinee branches
        (Expr.rec_strong primLit lambda app letIn var ctor match_ scrutinee)
        (fun _pat e _hb =>
          Expr.rec_strong primLit lambda app letIn var ctor match_ e)
termination_by e => sizeOf e
decreasing_by
  all_goals simp_wf
  all_goals first
    | omega
    | (have h := List.sizeOf_lt_of_mem _hb
       simp only [Prod.mk.sizeOf_spec] at h
       omega)




mutual

/-- Replace all `.bvar`s with some other `Ty` -/
def Ty.instantiate (subst : Nat → Ty) : Ty → Ty
  | .prim p => .prim p
  | .arrow a b => .arrow (a.instantiate subst) (b.instantiate subst)
  | .bvar n => subst n
  | .fvar n => .fvar n
  | .customTy name tys => .customTy name (TyList.instantiate subst tys)

def TyList.instantiate (subst : Nat → Ty) : List Ty → List Ty
  | [] => []
  | head :: tail => head.instantiate subst :: TyList.instantiate subst tail

end





/-- Resulting type is the input type with the `.bvar i`s swapped out for the `i`th item in `tyArgs`.

Cannot be produced for a `bvar` whose index is out of range of `tyArgs`. Thus if tyArgs doesn't contain any `bvar`s, neither does the output.

@TODO: hm maybe should make the source type here be a PolyTy, and then we can also ensure that all bvars are within range of the original polyty paramCount? then it's also just nicer to work with tbh. instantiation is semantically always from a polyty to a monoty, so it's odd that as it is it is a monoty to another monoty.
-/
inductive InstantiatesBy (tyArgs : List Ty) : Ty → Ty → Prop
  | prim :
    InstantiatesBy tyArgs (.prim p) (.prim p)

  | arrow :
    InstantiatesBy tyArgs fst instFst →
    InstantiatesBy tyArgs snd instSnd →
    InstantiatesBy tyArgs (.arrow fst snd) (.arrow instFst instSnd)

  | fvar :
    InstantiatesBy tyArgs (.fvar n) (.fvar n)

  | customTy :
    List.Forall₂ (InstantiatesBy tyArgs) tys instTys →
    InstantiatesBy tyArgs (.customTy name tys) (.customTy name instTys)

  | bvar :
    tyArgs[i]? = some ty →
    InstantiatesBy tyArgs (.bvar i) ty








/-! ## Small-step operational semantics

Call-by-value reduction on closed terms. Uses de Bruijn *indices* for term-level
variables: `var 0` is the innermost binder. Substitution is the standard
"substitute-and-eliminate" variant that shifts other vars to account for the
disappearing binder.

The machine here is independent of type checking — it would run on any
syntactically well-formed `Expr`. Type soundness (progress + preservation) is
the bridge between this and `TypeOfHM`. -/

mutual

/--
Shift all `.var i` with `i ≥ threshold` up by `n`. Traverses into binders with
`threshold` incremented by the number of new bindings introduced.

Used by `substN`: when a value is inserted at substitution depth `k`, it has
to pass under `k` new binders, which shifts its free vars up by `k`.
-/
def Expr.shiftFrom (threshold : Nat) (n : Nat) : Expr → Expr
  | .var i             => if i < threshold then .var i else .var (i + n)
  | .primLit p         => .primLit p
  | .lambda ann body   => .lambda ann (body.shiftFrom (threshold + 1) n)
  | .app f arg         => .app (f.shiftFrom threshold n) (arg.shiftFrom threshold n)
  | .letIn ann rhs body =>
      .letIn ann (rhs.shiftFrom threshold n) (body.shiftFrom (threshold + 1) n)
  | .ctor c            => .ctor c
  | .match_ scrut branches =>
      .match_ (scrut.shiftFrom threshold n)
        (BranchList.shiftFrom threshold n branches)

private def BranchList.shiftFrom (threshold : Nat) (n : Nat) :
    List (MatchPattern × Expr) → List (MatchPattern × Expr)
  | []                  => []
  | (pat, body) :: rest =>
      (pat, body.shiftFrom (threshold + pat.bindCount) n)
        :: BranchList.shiftFrom threshold n rest

end

mutual

/--
Capture-avoiding multi-substitution under de Bruijn *indices* (innermost = 0).

Replaces `.var (k + j)` with `(vs[j]).shiftFrom 0 k` for `j ∈ [0, vs.length)`,
and shifts higher indices down by `vs.length`. The `shiftFrom 0 k` accounts
for the `k` binders the substitution has traversed into.

When traversing into a binder, `k` is incremented by the number of binders
introduced (1 for `lambda`/`letIn`, `pat.contents` for each match branch body).

Used to implement beta, let-reduction, and match-reduction in one uniform
operation.

Replaces `.var`s that are `≥ k` with their corresponding item in `vs`. If the var index is higher than `k+vs.length`, just shift it down by `vs.length`.

In other words, this replaces a bunch of specific vars with their values and leaves other one untouched.
-/
def Expr.substN (k : Nat) (vs : List Expr) : Expr → Expr
  | .var i =>
      if i < k then .var i
      else if h : i - k < vs.length then (vs[i - k]).shiftFrom 0 k
      else .var (i - vs.length)
  | .primLit p         => .primLit p
  | .lambda ann body   => .lambda ann (body.substN (k + 1) vs)
  | .app f arg         => .app (f.substN k vs) (arg.substN k vs)
  | .letIn ann rhs body =>
      .letIn ann (rhs.substN k vs) (body.substN (k + 1) vs)
  | .ctor n            => .ctor n
  | .match_ scrut branches =>
      .match_ (scrut.substN k vs) (BranchList.substN k vs branches)

private def BranchList.substN (k : Nat) (vs : List Expr) :
    List (MatchPattern × Expr) → List (MatchPattern × Expr)
  | []                  => []
  | (pat, body) :: rest =>
      (pat, body.substN (k + pat.bindCount) vs)
        :: BranchList.substN k vs rest

end

/-- Single-var substitution. Beta-reduces `(λ. body) v` to `body.subst1 0 v`.

In other words, replaces all references to `.var k` with value `v`. This could be either during function application or replacing a let binding with its referent value. It also shifts all `.var`s up or down where appropriate so things stay well-indexed. -/
def Expr.subst1 (k : Nat) (v : Expr) : Expr → Expr :=
  Expr.substN k [v]




namespace SmallStep

mutual

/-- A fully-reduced expression: a value of one of the built-in or user-defined types. -/
inductive IsValue : Expr → Prop
  | primLit (p) :
      IsValue (.primLit p)
  | lambda ann body :
      IsValue (.lambda ann body)
  | ctor (name) :
      IsValue (.ctor name)
  | ctorApp {f v} :
      IsCtorChain f → IsValue v →
      IsValue (.app f v)

/-- A constructor optionally applied to zero or more *values*. Both `.ctor c`
    (zero args) and `.app (.app (.ctor c) v₁) v₂` (multiple args) qualify. -/
inductive IsCtorChain : Expr → Prop
  | ctor (name) :
      IsCtorChain (.ctor name)
  | app {f v} :
      IsCtorChain f → IsValue v →
      IsCtorChain (.app f v)

end

/-- Decompose a ctor chain into its ctor name and the list of applied args
    in *application order* (first applied arg first). -/
inductive CtorAppliedTo : Expr → CtorName → List Expr → Prop
  | base (name) :
      CtorAppliedTo (.ctor name) name []
  | step {f arg name args} :
      CtorAppliedTo f name args →
      CtorAppliedTo (.app f arg) name (args ++ [arg])




/-- `(pat, body)` is the *first* branch in `branches` whose pattern matches the
    given constructor name and arity. Mirrors `findMatchingBranch`. -/
inductive FirstMatchingBranch (name : CtorName) (arity : Nat) :
    List (MatchPattern × Expr) → MatchPattern → Expr → Prop
  | here :
    pat.matchesCtor name arity = true →
    FirstMatchingBranch name arity ((pat, body) :: rest) pat body
  | there :
    pat'.matchesCtor name arity = false →
    FirstMatchingBranch name arity rest pat body →
    FirstMatchingBranch name arity ((pat', body') :: rest) pat body


/-- Call-by-value small-step reduction. Left-to-right evaluation order. -/
inductive Step : Expr → Expr → Prop

  -- ─── reduction rules ────────────────────────────────────────────────

  /-- Beta. (NB: `body.substN 0 [v]` substitutes the argument `v` into `body`;
      written via `substN` rather than `subst1` because `_.subst1 0 v` misfires
      under dot notation — `subst1`'s first `Expr` parameter is `v`, not the
      target.) -/
  | beta {ann body v} :
      IsValue v →
      Step (.app (.lambda ann body) v) (body.substN 0 [v])

  /-- Let reduction (after rhs has been reduced to a value). -/
  | letReduce {ann v body} :
      IsValue v →
      Step (.letIn ann v body) (body.substN 0 [v])

  /-- Match reduction. The scrutinee must be a fully-evaluated ctor chain
      whose ctor name matches the *first* applicable branch pattern. -/
  | matchReduce {scrut branches name args pat body} :
      IsValue scrut →
      CtorAppliedTo scrut name args →
      FirstMatchingBranch name args.length branches pat body →
      Step (.match_ scrut branches) (body.substN 0 (args.take pat.bindCount))

  -- ─── congruence rules (enforce left-to-right CBV) ─────────────────

  /-- Reduce the function position of an application. -/
  | appFn {f f' arg} :
      Step f f' →
      Step (.app f arg) (.app f' arg)

  /-- Once the function is a value, reduce the argument. -/
  | appArg {v arg arg'} :
      IsValue v → Step arg arg' →
      Step (.app v arg) (.app v arg')

  /-- Reduce the rhs of a let-binding. -/
  | letInRhs {ann rhs rhs' body} :
      Step rhs rhs' →
      Step (.letIn ann rhs body) (.letIn ann rhs' body)

  /-- Reduce the scrutinee of a match. -/
  | matchScrut {scrut scrut' branches} :
      Step scrut scrut' →
      Step (.match_ scrut branches) (.match_ scrut' branches)



/-! ### Decidable value / ctor-chain checks -/

mutual

def isValue : Expr → Bool
  | .primLit _ => true
  | .lambda _ _ => true
  | .ctor _ => true
  | .app f v => isCtorChain f && isValue v
  | _ => false

def isCtorChain : Expr → Bool
  | .ctor _ => true
  | .app f v => isCtorChain f && isValue v
  | _ => false

end

/-! ### Ctor-chain decomposition -/

def getCtorArgs : Expr → Option (CtorName × List Expr)
  | .ctor name => some (name, [])
  | .app f arg => do
    let (name, args) ← getCtorArgs f
    return (name, args ++ [arg])
  | _ => none

def findMatchingBranch (name : CtorName) (args : List Expr) :
    List (MatchPattern × Expr) → Option Expr
  | [] => none
  | (pat, body) :: rest =>
    if pat.matchesCtor name args.length then
      some (body.substN 0 (args.take pat.bindCount))
    else
      findMatchingBranch name args rest

/-! ### Small-step evaluation function -/

/-- Compute one step of CBV reduction, returning `none` if the expression is
    already a value or is stuck (ill-typed / open term). -/
def step : Expr → Option Expr
  | .app f arg =>
    if isValue f then
      if isValue arg then
        match f with
        | .lambda _ body => some (body.substN 0 [arg])
        | _ => none
      else do let arg' ← step arg; return .app f arg'
    else do let f' ← step f; return .app f' arg

  | .letIn ann rhs body =>
    if isValue rhs then some (body.substN 0 [rhs])
    else do let rhs' ← step rhs; return .letIn ann rhs' body

  | .match_ scrut branches =>
    if isValue scrut then
      match getCtorArgs scrut with
      | some (name, args) => findMatchingBranch name args branches
      | none => none
    else do let scrut' ← step scrut; return .match_ scrut' branches

  | _ => none

/-- Multi-step evaluator with fuel. Returns `some v` when a value is reached,
    `none` if stuck or out of fuel. -/
def evaluate : Nat → Expr → Option Expr
  | 0, e => if isValue e then some e else none
  | n + 1, e =>
    if isValue e then some e
    else match step e with
    | some e' => evaluate n e'
    | none => none

/-! ### Bool ↔ Prop correspondence for IsValue / IsCtorChain -/

private theorem isValue_isCtorChain_correct (e : Expr) :
    (isValue e = true ↔ IsValue e) ∧ (isCtorChain e = true ↔ IsCtorChain e) := by
  induction e using Expr.rec_strong with
  | primLit p => exact ⟨⟨fun _ => .primLit p, fun _ => rfl⟩, ⟨nofun, nofun⟩⟩
  | lambda ann body _ => exact ⟨⟨fun _ => .lambda ann body, fun _ => rfl⟩, ⟨nofun, nofun⟩⟩
  | ctor name => exact ⟨⟨fun _ => .ctor name, fun _ => rfl⟩, ⟨fun _ => .ctor name, fun _ => rfl⟩⟩
  | app f arg ihf iharg =>
    simp only [isValue, isCtorChain, Bool.and_eq_true]
    exact ⟨⟨fun ⟨hf, ha⟩ => .ctorApp (ihf.2.mp hf) (iharg.1.mp ha),
            fun h => by cases h with | ctorApp hc hv => exact ⟨ihf.2.mpr hc, iharg.1.mpr hv⟩⟩,
           ⟨fun ⟨hf, ha⟩ => .app (ihf.2.mp hf) (iharg.1.mp ha),
            fun h => by cases h with | app hc hv => exact ⟨ihf.2.mpr hc, iharg.1.mpr hv⟩⟩⟩
  | var _ => exact ⟨⟨nofun, nofun⟩, ⟨nofun, nofun⟩⟩
  | letIn _ _ _ _ _ => exact ⟨⟨nofun, nofun⟩, ⟨nofun, nofun⟩⟩
  | match_ _ _ _ _ => exact ⟨⟨nofun, nofun⟩, ⟨nofun, nofun⟩⟩

theorem isValue_iff_IsValue {e : Expr} : isValue e = true ↔ IsValue e :=
  (isValue_isCtorChain_correct e).1


/-! ### Helper lemmas -/

private theorem CtorAppliedTo_of_getCtorArgs {e name args}
    (h : getCtorArgs e = some (name, args)) :
    CtorAppliedTo e name args := by
  induction e using Expr.rec_strong generalizing name args with
  | ctor n =>
    simp [getCtorArgs] at h
    obtain ⟨rfl, rfl⟩ := h
    exact .base n
  | app f arg ih _ =>
    unfold getCtorArgs at h
    match hf : getCtorArgs f with
    | .none => simp [hf] at h
    | .some ⟨n, as⟩ =>
      simp [hf] at h
      obtain ⟨rfl, rfl⟩ := h
      exact .step (ih hf)
  | _ => simp [getCtorArgs] at h

private theorem getCtorArgs_of_CtorAppliedTo {e name args}
    (h : CtorAppliedTo e name args) : getCtorArgs e = some (name, args) := by
  induction h with
  | base => simp [getCtorArgs]
  | step _ ih => simp [getCtorArgs, ih]

private theorem findMatchingBranch_to_FirstMatch {name args branches e'}
    (h : findMatchingBranch name args branches = some e') :
    ∃ pat body, FirstMatchingBranch name args.length branches pat body ∧
      e' = body.substN 0 (args.take pat.bindCount) := by
  induction branches with
  | nil => simp [findMatchingBranch] at h
  | cons hd tl ih =>
    obtain ⟨pat, body⟩ := hd
    simp only [findMatchingBranch] at h
    split at h
    · rename_i hm
      simp at h
      exact ⟨pat, body, .here hm, h.symm⟩
    · rename_i hnm
      obtain ⟨p, b, hfirst, heq⟩ := ih h
      exact ⟨p, b, .there ((Bool.not_eq_true _).mp hnm) hfirst, heq⟩

private theorem FirstMatch_to_findMatchingBranch {name : CtorName} {arity : Nat}
    {branches : List (MatchPattern × Expr)} {pat : MatchPattern} {body : Expr}
    (h : FirstMatchingBranch name arity branches pat body)
    {args : List Expr} (hlen : arity = args.length) :
    findMatchingBranch name args branches = some (body.substN 0 (args.take pat.bindCount)) := by
  induction h with
  | here hm =>
    subst hlen
    simp [findMatchingBranch, hm]
  | there hnot _ ih =>
    subst hlen
    unfold findMatchingBranch
    rw [if_neg ((Bool.not_eq_true _).mpr hnot)]
    exact ih

private theorem isCtorChain_imp_isValue {e : Expr}
    (h : isCtorChain e = true) : isValue e = true := by
  cases e <;> simp_all [isValue, isCtorChain]

private theorem isValue_step_none {e : Expr} (hv : isValue e = true) :
    step e = none := by
  match e with
  | .primLit _ | .lambda _ _ | .ctor _ => rfl
  | .app f arg =>
    simp only [isValue, Bool.and_eq_true] at hv
    simp only [step, isCtorChain_imp_isValue hv.1, hv.2, ite_true]
    cases f <;> (first | rfl | simp [isCtorChain] at hv)
  | .var _ | .letIn _ _ _ | .match_ _ _ => simp [isValue] at hv

private theorem step_some_not_isValue {e e' : Expr}
    (h : step e = some e') : isValue e = false := by
  cases hv : isValue e with
  | false => rfl
  | true => exact absurd h (by rw [isValue_step_none hv]; nofun)

/-! ### Soundness of `step` w.r.t. the `Step` relation -/

theorem step_sound {e e' : Expr} (h : step e = some e') : Step e e' := by
  induction e using Expr.rec_strong generalizing e' with
  | primLit _ | lambda _ _ _ | ctor _ | var _ => simp [step] at h
  | app f arg ihf iharg =>
    unfold step at h
    split at h
    · rename_i hvf
      split at h
      · rename_i hvarg
        split at h
        · simp at h; subst h
          exact .beta (isValue_iff_IsValue.mp hvarg)
        · exact nomatch h
      · match harg : step arg with
        | .none => simp [harg] at h
        | .some arg' =>
          simp [harg] at h; subst h; exact .appArg (isValue_iff_IsValue.mp hvf) (iharg harg)
    · match hf : step f with
      | .none => simp [hf] at h
      | .some f' => simp [hf] at h; subst h; exact .appFn (ihf hf)
  | letIn ann rhs body ihrhs _ =>
    unfold step at h
    split at h
    · rename_i hvrhs
      simp at h; subst h
      exact .letReduce (isValue_iff_IsValue.mp hvrhs)
    · match hrhs : step rhs with
      | .none => simp [hrhs] at h
      | .some rhs' => simp [hrhs] at h; subst h; exact .letInRhs (ihrhs hrhs)
  | match_ scrut branches ihscrut _ =>
    unfold step at h
    split at h
    · rename_i hvscrut
      revert h
      cases hga : getCtorArgs scrut with
      | none => intro h; exact nomatch h
      | some p =>
        obtain ⟨name, args⟩ := p
        intro h
        obtain ⟨pat, body, hfirst, rfl⟩ := findMatchingBranch_to_FirstMatch h
        exact .matchReduce (isValue_iff_IsValue.mp hvscrut)
          (CtorAppliedTo_of_getCtorArgs hga) hfirst
    · match hscrut : step scrut with
      | .none => simp [hscrut] at h
      | .some scrut' =>
        simp [hscrut] at h; subst h; exact .matchScrut (ihscrut hscrut)

/-! ### Completeness of `step` w.r.t. the `Step` relation -/

theorem step_complete {e e' : Expr} (h : Step e e') : step e = some e' := by
  induction h with
  | beta hval =>
    have := isValue_iff_IsValue.mpr hval
    unfold step; simp [isValue, this]
  | letReduce hval =>
    have := isValue_iff_IsValue.mpr hval
    unfold step; simp [this]
  | matchReduce hval hctor hfirst =>
    have := isValue_iff_IsValue.mpr hval
    have := getCtorArgs_of_CtorAppliedTo hctor
    have := FirstMatch_to_findMatchingBranch hfirst rfl
    unfold step; simp [*]
  | appFn _ ih =>
    have := step_some_not_isValue ih
    unfold step; simp [this, ih]
  | appArg hval _ ih =>
    have hvf := isValue_iff_IsValue.mpr hval
    have hva := step_some_not_isValue ih
    unfold step; simp [hvf, hva, ih]
  | letInRhs _ ih =>
    have := step_some_not_isValue ih
    unfold step; simp [this, ih]
  | matchScrut _ ih =>
    have := step_some_not_isValue ih
    unfold step; simp [this, ih]

theorem step_deterministic {e e₁ e₂ : Expr}
    (h₁ : Step e e₁) (h₂ : Step e e₂) : e₁ = e₂ := by
  have := step_complete h₁
  have := step_complete h₂
  simp_all




end SmallStep




/-! ## Well-scopedness

`WellScopedUnder n e` means every `.var i` in `e` satisfies `i < n`. Under de
Bruijn indices with the cons-on-binder convention, the typing relation maintains
the invariant that any well-typed expression is well-scoped under
`ctx.env.length`.

Lambda/let/match introduce 1, 1, or `pat.contents` new levels respectively,
raising the scope bound inside their body. -/

mutual

inductive Expr.WellScopedUnder : Nat → Expr → Prop
  | primLit {n p}            : Expr.WellScopedUnder n (.primLit p)
  | ctor    {n c}            : Expr.WellScopedUnder n (.ctor c)
  | var     {n i}            : i < n → Expr.WellScopedUnder n (.var i)
  | lambda  {n ann body}       :
      Expr.WellScopedUnder (n + 1) body →
      Expr.WellScopedUnder n (.lambda ann body)
  | app     {n f arg}        :
      Expr.WellScopedUnder n f → Expr.WellScopedUnder n arg →
      Expr.WellScopedUnder n (.app f arg)
  | letIn   {n ann rhs body}   :
      Expr.WellScopedUnder n rhs →
      Expr.WellScopedUnder (n + 1) body →
      Expr.WellScopedUnder n (.letIn ann rhs body)
  | match_  {n scrut branches} :
      Expr.WellScopedUnder n scrut →
      Expr.BranchListWellScoped n branches →
      Expr.WellScopedUnder n (.match_ scrut branches)

inductive Expr.BranchListWellScoped : Nat → List (MatchPattern × Expr) → Prop
  | nil  {n}          : Expr.BranchListWellScoped n []
  | cons {n pat body rest} :
      Expr.WellScopedUnder (n + pat.bindCount) body →
      Expr.BranchListWellScoped n rest →
      Expr.BranchListWellScoped n ((pat, body) :: rest)

end


/-- Instantation doesn't add more bvars than are in `tyArgs` -/
theorem InstantiatesBy.preserves_bvars : (∀ tyArg ∈ tyArgs, ContainsBvarsUpTo 0 tyArg) → InstantiatesBy tyArgs polyTy ty → ContainsBvarsUpTo 0 ty := by
  intro prem hinst
  cases hinst with
  | prim => constructor
  | arrow a b =>
    expose_names
    constructor
    · exact a.preserves_bvars prem
    · exact b.preserves_bvars prem
  | fvar => refine .fvar
  | bvar hin =>
    have : ty ∈ tyArgs := by grind
    exact prem ty this
  | customTy rels =>
    expose_names
    constructor
    intro ty tyin
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp tyin
    have hlen := rels.length_eq
    have := List.Forall₂.get rels (by omega) hi
    exact this.preserves_bvars prem











/-! ### Env helpers used by `weaken_env` and `subst_lemma`. -/

/-- An element is in an env's freeVars iff some polytype in env mentions it. -/
theorem Env.mem_freeVars_iff {env : Env} {x : Nat} :
    x ∈ env.freeVars ↔ ∃ pt ∈ env, x ∈ pt.body.freeVars := by
  induction env with
  | nil => simp [Env.freeVars]
  | cons hd tl ih =>
    simp only [Env.freeVars, List.mem_dedup, List.mem_append]
    rw [ih]
    constructor
    · rintro (h | ⟨pt, hmem, h⟩)
      · exact ⟨hd, List.mem_cons_self, h⟩
      · exact ⟨pt, List.mem_cons_of_mem _ hmem, h⟩
    · rintro ⟨pt, hmem, h⟩
      cases hmem with
      | head _ => exact .inl h
      | tail _ h' => exact .inr ⟨pt, h', h⟩


/-! ## Canonical forms

Inversion lemmas that say "if a value has such-and-such a type, it has such-and-
such a syntactic form". Used in progress to conclude that the next step exists
when we see a value in a particular type position.

Note the asymmetry vs. simpler languages: a value of arrow type can be either
a `lambda` *or* a partial ctor application (since constructors are curried). -/

/-- Instantiation preserves the `wrapArrows ... (customTy ...)` shape: if you
    instantiate a type of that shape, you get back a type of the same shape with
    the same `customTy` name and the same number of arrow wrappers. -/
private lemma InstantiatesBy.wrapArrows_customTy_form
    {name : TyName} {args tys : List Ty} {τ : Ty}
    (h : InstantiatesBy env (Ty.wrapArrows (.customTy name args) tys) τ) :
    ∃ instArgs instTys, τ = Ty.wrapArrows (.customTy name instArgs) instTys := by
  induction tys generalizing τ with
  | nil =>
    cases h with
    | customTy _ => exact ⟨_, [], rfl⟩
  | cons _ rest ih =>
    cases h with
    | arrow _ h_rest =>
      expose_names
      obtain ⟨instArgs, instRest, h_eq⟩ := ih h_rest
      refine ⟨instArgs, instFst :: instRest, ?_⟩
      simp [Ty.wrapArrows, h_eq]


/-! ## Progress -/

namespace SmallStep

mutual

/-- Every match expression (transitively) inside `e` is exhaustive: for each
    match node, every constructor of the matched type `tyName` has a
    corresponding branch.  The `tyName` at each match node is existentially
    quantified — when *building* the proof the caller picks the type that the
    match covers (typically from the typing derivation). -/
inductive AllMatchesExhaustive : CtorEnv → Expr → Prop where
  | primLit : AllMatchesExhaustive ctors (.primLit p)
  | var : AllMatchesExhaustive ctors (.var n)
  | ctor : AllMatchesExhaustive ctors (.ctor name)
  | lambda :
    AllMatchesExhaustive ctors body →
    AllMatchesExhaustive ctors (.lambda ann body)
  | app :
    AllMatchesExhaustive ctors f → AllMatchesExhaustive ctors arg →
    AllMatchesExhaustive ctors (.app f arg)
  | letIn :
    AllMatchesExhaustive ctors rhs → AllMatchesExhaustive ctors body →
    AllMatchesExhaustive ctors (.letIn ann rhs body)
  /-- Exhaustiveness for match: every constructor in the ctor env whose type
      matches `tyName` has a corresponding branch. The `tyName` is existentially
      quantified — the caller picks it (typically from the typing derivation) —
      but it is pinned to the branches: every branch's pattern must be a
      constructor of `tyName`, so a bogus ctor-less type cannot be chosen. -/
  | match_ {tyName : TyName} :
    AllMatchesExhaustive ctors scrut →
    AllBranchBodiesExhaustive ctors branches →
    (∀ c n body, (MatchPattern.named c n, body) ∈ branches →
       ∃ ctor, LookupList.get? ctors c = some ctor ∧ ctor.tyName = tyName) →
    (∀ (ctorName : CtorName) (ctor : Ctor),
      LookupList.get? ctors ctorName = some ctor →
      ctor.tyName = tyName →
      ∃ pat body, (pat, body) ∈ branches ∧
        pat.matchesCtor ctorName ctor.contents.length = true) →
    AllMatchesExhaustive ctors (.match_ scrut branches)

/-- All branch bodies are recursively exhaustive. -/
inductive AllBranchBodiesExhaustive : CtorEnv → List (MatchPattern × Expr) → Prop where
  | nil : AllBranchBodiesExhaustive ctors []
  | cons :
    AllMatchesExhaustive ctors body →
    AllBranchBodiesExhaustive ctors rest →
    AllBranchBodiesExhaustive ctors ((pat, body) :: rest)

end


/-- If a matching branch exists in the list, `findMatchingBranch` succeeds. -/
theorem findMatchingBranch_of_exists {name : CtorName} {args : List Expr}
    {branches : List (MatchPattern × Expr)}
    (h : ∃ pat body, (pat, body) ∈ branches ∧
         pat.matchesCtor name args.length = true) :
    ∃ e', findMatchingBranch name args branches = some e' := by
  induction branches with
  | nil => obtain ⟨_, _, hmem, _⟩ := h; exact nomatch hmem
  | cons hd tl ih =>
    obtain ⟨pat, body, hmem, hcov⟩ := h
    unfold findMatchingBranch
    split
    · exact ⟨_, rfl⟩
    · rename_i hnm
      cases hmem with
      | head _ => exact absurd hcov hnm
      | tail _ hmem' => exact ih ⟨pat, body, hmem', hcov⟩


end SmallStep


/-! ## Type inference: locally-nameless + cofinite quantification

### Design source

Faithful port of Chargueraud's mini-ML formalisation
(`charguer/formalmetacoq/ln/ML_{Definitions,Infrastructure,Soundness}.v`), the
canonical application of Aydemir et al.'s "Engineering Formal Metatheory"
(POPL 2008) to Hindley-Milner with let-polymorphism.

### The core idea: cofinite quantification

The let rule must generalise the type variables of the bound expression that
aren't fixed by the environment. The subtle part is formalising "a fresh choice
of those variables" so that it survives induction.

The naive **exists-fresh** phrasing — pick one concrete `ftvs ⊆ FV(τ) \ FV(Γ)`
(what an earlier `Generalise` relation, since removed, did) — fails: a
derivation commits to one choice, and when the environment grows in a recursive
`subst_lemma`/`weaken_env` call those particular vars may now clash, with no way
to renege.

The **cofinite** phrasing flips the quantifier: the rule says the body checks
**for every** opening by names `Xs` avoiding some *finite* set `L`. The
induction hypothesis is then *universal* in the choice of fresh names — when the
environment grows we just re-instantiate it at names fresh for the bigger env.
This is the "rename to dodge clashes" move baked into the rule, rather than
bolted on as a separate equivariance lemma. The payoff: `weaken_env` and
`subst_lemma` need **no** environment-freshness side conditions.

### Variable encodings (three distinct things)

- `Ty.bvar i` — a type variable bound by a scheme; de Bruijn *index* scoped
  within one `PolyTy` (`i < paramCount`).
- `Ty.fvar n` — a free type variable; a locally-nameless *name* (`Nat`).
  Declaratively these are abstract/rigid type variables; they become
  unification variables only in the algorithmic phase.
- `Expr.var i` — a term variable; de Bruijn *index* into the environment.

Because term variables are de Bruijn indices (not locally-nameless names), the
*term*-side cofinite quantifier from Chargueraud vanishes for us; only the
*type*-side cofinite quantification (in `letIn`) remains.

### The pieces

- `Ty.substFvar`/`substFvars`, `Env.substFvar` — type-variable substitution
  (`[Z ↦ U]`), used by `typ_subst_preservation`.
- `Ty.openVars Xs` — open a scheme body's bvars with fresh *names*;
  `Ty.openWith Vs` — open them with arbitrary *types* (instantiation,
  generalising `InstantiatesBy`).
- `Ty.IsLC` (`= ContainsBvarsUpTo 0`) — locally-closed (no bvars).
- `PolyTy.WF M` — well-formed scheme (`M.body`'s bvars are `< M.paramCount`).
- `FreshNames L n Xs` — `n` distinct names avoiding `L`.
- `HasSchemeVars` / `HasScheme` — "types at every fresh opening" / "types at
  every concrete instantiation", bridged by `HasScheme.fromHasSchemeVars`.

No value restriction: the language is pure, so let-generalising arbitrary
expressions is sound (plain Damas-Milner). -/

mutual

/-- `[Z ↦ U] · ty` — replace every `.fvar Z` in `ty` with `U`.

    NOTE the explicit (non-dot) recursive call style: dot notation
    (`a.substFvar Z U`) would pick `U` for the `Ty` slot since it's the first
    `Ty`-typed positional arg, causing both an argument-order bug and a
    termination-check failure. -/
def Ty.substFvar (Z : Nat) (U : Ty) : Ty → Ty
  | .prim p          => .prim p
  | .arrow a b       => .arrow (Ty.substFvar Z U a) (Ty.substFvar Z U b)
  | .bvar n          => .bvar n
  | .fvar n          => if n = Z then U else .fvar n
  | .customTy nm tys => .customTy nm (TyList.substFvar Z U tys)

private def TyList.substFvar (Z : Nat) (U : Ty) : List Ty → List Ty
  | []        => []
  | hd :: tl  => Ty.substFvar Z U hd :: TyList.substFvar Z U tl

end

/-- Iterated `substFvar`: apply a list of `(Z, U)` substitutions left-to-right. -/
def Ty.substFvars : List (Nat × Ty) → Ty → Ty
  | []              , ty => ty
  | (Z, U) :: rest  , ty => Ty.substFvars rest (Ty.substFvar Z U ty)

/-- Open a scheme body's bvars with named fvars: `.bvar i ↦ .fvar (Xs.get i)`. -/
def Ty.openVars (Xs : List Nat) (ty : Ty) : Ty :=
  ty.instantiate (fun i => (Xs[i]?).elim (.bvar i) .fvar)

/-- Open a scheme body's bvars with arbitrary LC types. -/
def Ty.openWith (Vs : List Ty) (ty : Ty) : Ty :=
  ty.instantiate (fun i => (Vs[i]?).getD (.bvar i))

def PolyTy.substFvar (Z : Nat) (U : Ty) (pt : PolyTy) : PolyTy :=
  -- NOTE: explicit (non-dot) call: `pt.body.substFvar Z U` would misfire because
  -- `Ty.substFvar` has two `Ty` args and dot notation fills the wrong one.
  { paramCount := pt.paramCount, body := Ty.substFvar Z U pt.body }

def PolyTy.openVars (Xs : List Nat) (pt : PolyTy) : Ty := pt.body.openVars Xs

def PolyTy.openWith (Vs : List Ty) (pt : PolyTy) : Ty := pt.body.openWith Vs

def Env.substFvar (Z : Nat) (U : Ty) (env : Env) : Env :=
  env.map (PolyTy.substFvar Z U)

/-! ### Type-variable operations on terms

Pushing type-level substitution / opening through the *type annotations* embedded
in a term (`lambda` param annotations and `letIn` scheme annotations). These are
the term-level analogues of `Ty.substFvar` / `Ty.openVars`, and they exist to
support **scoped type variables**: an annotation inside a `let`-bound expression
may mention the type variables bound by an enclosing `let`'s scheme. -/

mutual
/-- Substitute a free type variable `Z ↦ U` through every annotation in a term.
    Free type variables are global names, so (unlike opening) this needs no
    binder-depth bookkeeping. Used by `typ_subst_preservation`. -/
def Expr.substTyFvar (Z : Nat) (U : Ty) : Expr → Expr
  | .primLit p          => .primLit p
  | .lambda ann body    => .lambda (ann.map (Ty.substFvar Z U)) (body.substTyFvar Z U)
  | .app f arg          => .app (f.substTyFvar Z U) (arg.substTyFvar Z U)
  | .letIn ann rhs body =>
      .letIn (ann.map (PolyTy.substFvar Z U)) (rhs.substTyFvar Z U) (body.substTyFvar Z U)
  | .var i              => .var i
  | .ctor c             => .ctor c
  | .match_ scrut branches =>
      .match_ (scrut.substTyFvar Z U) (BranchList.substTyFvar Z U branches)

private def BranchList.substTyFvar (Z : Nat) (U : Ty) :
    List (MatchPattern × Expr) → List (MatchPattern × Expr)
  | []                  => []
  | (pat, body) :: rest => (pat, body.substTyFvar Z U) :: BranchList.substTyFvar Z U rest
end

/-- Iterated `Expr.substTyFvar` (left-to-right), mirroring `Ty.substFvars`. -/
def Expr.substTyFvars : List (Nat × Ty) → Expr → Expr
  | []             , e => e
  | (Z, U) :: rest , e => Expr.substTyFvars rest (Expr.substTyFvar Z U e)

/-- Open the `bvar (d + i)` of a type (offset `d`) to `.fvar (Xs[i])`, leaving
    `bvar`s `< d` (those bound by *inner* schemes) untouched. `d = 0` coincides
    with `Ty.openVars`. -/
def Ty.openVarsFrom (d : Nat) (Xs : List Nat) (t : Ty) : Ty :=
  t.instantiate (fun i => if i < d then .bvar i else (Xs[i - d]?).elim (.bvar i) .fvar)

mutual
/-- Open the scoped type variables of an enclosing scheme inside a term's
    annotations: replace the `bvar`s referencing that scheme by `.fvar (Xs[i])`.
    `d` tracks how many *type*-binder levels (introduced by annotated polymorphic
    `let`s) we've descended through, so only the targeted scheme's vars are
    opened. Term binders (`lambda`, match patterns) and a `let`'s *continuation*
    bind no type variables, so they leave `d` unchanged. -/
def Expr.openTyVarsAux (d : Nat) (Xs : List Nat) : Expr → Expr
  | .primLit p          => .primLit p
  | .lambda ann body    => .lambda (ann.map (Ty.openVarsFrom d Xs)) (body.openTyVarsAux d Xs)
  | .app f arg          => .app (f.openTyVarsAux d Xs) (arg.openTyVarsAux d Xs)
  | .letIn (some σ) rhs body =>
      -- `σ` introduces `σ.paramCount` inner type binders over `σ.body` and `rhs`
      -- (the signature scopes over the bound expression), but **not** over the
      -- continuation `body`.
      .letIn (some { σ with body := Ty.openVarsFrom (d + σ.paramCount) Xs σ.body })
        (rhs.openTyVarsAux (d + σ.paramCount) Xs)
        (body.openTyVarsAux d Xs)
  | .letIn none rhs body =>
      .letIn none (rhs.openTyVarsAux d Xs) (body.openTyVarsAux d Xs)
  | .var i              => .var i
  | .ctor c             => .ctor c
  | .match_ scrut branches =>
      .match_ (scrut.openTyVarsAux d Xs) (BranchList.openTyVarsAux d Xs branches)

private def BranchList.openTyVarsAux (d : Nat) (Xs : List Nat) :
    List (MatchPattern × Expr) → List (MatchPattern × Expr)
  | []                  => []
  | (pat, body) :: rest => (pat, body.openTyVarsAux d Xs) :: BranchList.openTyVarsAux d Xs rest
end

/-- Open an enclosing scheme's scoped type variables throughout a (bound) term:
    the term-level analogue of `PolyTy.openVars`. -/
def Expr.openTyVars (Xs : List Nat) (e : Expr) : Expr := e.openTyVarsAux 0 Xs

/-- The bound-expression form used by the `let` typing rule's cofinite premise:
    open the bound expression's scoped type variables at `Xs` **iff** the `let`
    carries a scheme annotation (the annotation is what binds those variables).
    An unannotated `let` introduces no scoped type variables, so its bound
    expression is typed unchanged. -/
def Expr.openBoundTyVars : Option PolyTy → List Nat → Expr → Expr
  | none,   _,  e => e
  | some _, Xs, e => e.openTyVars Xs


/-! ### Locally-closed-ness. -/

/-- Locally-closed monotype: no `.bvar`s. Existing `ContainsBvarsUpTo 0`. -/
abbrev Ty.IsLC (ty : Ty) : Prop := ContainsBvarsUpTo 0 ty

/-- All types in the list are LC, AND the list has the expected length. -/
def Ty.AreLC (n : Nat) (Vs : List Ty) : Prop :=
  Vs.length = n ∧ ∀ V ∈ Vs, V.IsLC

/-- A well-formed scheme: every bound variable in the body is within the
    declared arity (`< paramCount`).

    Intuition: this is exactly the condition that makes `M` a *real* `∀`-scheme
    — equivalently, opening it with any `paramCount`-many names yields a
    locally-closed type (no dangling bvars escape). We use this elementary
    *syntactic* form (rather than the "opening is always LC" semantic form)
    because it's what the proofs actually consume, and it's trivially preserved
    by the operations we perform on schemes. -/
def PolyTy.WF (M : PolyTy) : Prop :=
  ContainsBvarsUpTo M.paramCount M.body


/-! ### Freshness packaging. -/

/-- `Xs` is a list of `n` distinct names, all disjoint from `L`. -/
structure FreshNames (L : List Nat) (n : Nat) (Xs : List Nat) : Prop where
  length : Xs.length = n
  nodup  : Xs.Nodup
  avoid  : ∀ x ∈ Xs, x ∉ L


/-! ### The declarative typing relation `TypeOfHM`.

Syntax-directed Hindley–Milner typing. All rules are standard except the
let-generalising rule (`letIn`), which uses a **cofinite**
"for-all-fresh" premise to express generalisation (see the module doc above):

```
  PolyTy.WF M →
  (∀ Xs, FreshNames L M.paramCount Xs → TypeOfHM ctx boundExpr (M.openVars Xs)) →
  bodyCtx = { ctx with env := M :: ctx.env } →
  TypeOfHM bodyCtx body bodyTy →
  TypeOfHM ctx (.letIn ann boundExpr body) bodyTy
```

The cofinite premise's IH is *universally quantified in `Xs`*, so when
`subst_lemma`/`weaken_env` descend through a `letIn` and the env grows, they
re-instantiate it at names fresh for the bigger env — no side conditions.

`var`/`ctor`/`match_` instantiate schemes via `InstantiatesBy` (equivalent to
`openWith` on a well-formed scheme). -/

mutual

/-- Cofinite (locally-nameless-style) declarative typing relation. -/
inductive TypeOfHM : Ctx → Expr → Ty → Prop
  | primLitUnit :
    TypeOfHM ctx (.primLit .unit) (.prim .unit)

  | primLitInt :
    TypeOfHM ctx (.primLit (.int n)) (.prim .int)

  | primLitNat :
    TypeOfHM ctx (.primLit (.nat n)) (.prim .nat)

  -- | primLitBool :
  --   TypeOfHM ctx (.primLit (.bool b)) (.prim .bool)

  | primLitStr :
    TypeOfHM ctx (.primLit (.str s)) (.prim .str)

  | lambda :
    -- `paramTy` is locally closed (no dangling type `bvar`s). When the lambda
    -- sits inside a `let`-bound expression, its annotation may mention the
    -- enclosing scheme's type variables; those are `bvar`s in the stored term but
    -- get replaced by fresh `fvar`s (via `Expr.openTyVars`) before this rule
    -- fires, so `paramTy` is `bvar`-free here while still possibly carrying free
    -- type variables — the scoped ones.
    ContainsBvarsUpTo 0 paramTy →
    -- When a parameter annotation is present it pins the parameter type. The
    -- annotation need NOT be closed: a free type variable in it is a scoped type
    -- variable bound by an enclosing signature (Elm/GHC `ScopedTypeVariables`).
    -- Consistency under type substitution is kept by `typ_subst_preservation`
    -- pushing `[Z↦U]` through the term's annotations (`Expr.substTyFvar`).
    (∀ T, ann = some T → paramTy = T) →
    bodyCtx = { ctx with env := PolyTy.mkTrivial paramTy :: ctx.env } →
    TypeOfHM bodyCtx body bodyTy →
    TypeOfHM ctx (.lambda ann body) (.arrow paramTy bodyTy)

  | app :
    TypeOfHM ctx f (.arrow argTy retTy) →
    TypeOfHM ctx input argTy →
    TypeOfHM ctx (.app f input) retTy

  /-- Cofinite let-generalisation. See module doc above. `M` is the
      generalised scheme; the premise says `boundExpr` types at *every*
      sufficiently-fresh opening of `M`.

      NOTE: no value restriction — our language is pure (no effects/refs), so
      generalising an arbitrary let-bound expression is sound (plain
      Damas–Milner). Chargueraud needs `value boundExpr` only because mini-ML
      has mutable refs. -/
  | letIn {M : PolyTy} {L : List Nat} :
    PolyTy.WF M →
    -- When a scheme annotation is present, the generalised scheme *is* the
    -- annotation `σ`. The cofinite premise below (`boundExpr` types at every
    -- fresh opening of `M = σ`) then enforces "the annotation is not more
    -- general than `boundExpr` actually is" for free. The annotation need NOT be
    -- closed: free type variables in `σ.body` are scoped type variables bound by
    -- an enclosing signature.
    (∀ σ, ann = some σ → M = σ) →
    -- `boundExpr` is typed at every fresh opening `Xs` of `M`, with the
    -- annotation's own scoped type variables opened to the *same* `Xs`
    -- (`Expr.openBoundTyVars`; for an unannotated `let` this is just `boundExpr`).
    -- This ties annotations inside `boundExpr` that reference the signature to the
    -- cofinite fresh names — the spec-level home of scoped type variables.
    (∀ Xs : List Nat, FreshNames L M.paramCount Xs →
        TypeOfHM ctx (Expr.openBoundTyVars ann Xs boundExpr) (M.openVars Xs)) →
    bodyCtx = { ctx with env := M :: ctx.env } →
    TypeOfHM bodyCtx body bodyTy →
    TypeOfHM ctx (.letIn ann boundExpr body) bodyTy

  | var :
    ctx.env[dbl]? = some polyTy →
    (∀ tyArg ∈ tyArgs, ContainsBvarsUpTo 0 tyArg) →
    InstantiatesBy tyArgs polyTy.body ty →
    TypeOfHM ctx (.var dbl) ty

  | ctor :
    LookupList.get? ctx.ctors name = some ctor →
    (∀ tyArg ∈ tyArgs, ContainsBvarsUpTo 0 tyArg) →
    InstantiatesBy tyArgs ctor.toTy.body ty →
    TypeOfHM ctx (.ctor name) ty

  | match_ :
    TypeOfHM ctx scrutinee (.customTy tyName tyArgs) →
    branches ≠ [] →
    (∀ branch ∈ branches, TypeOfMatchBranch ctx branch tyName tyArgs resultTy) →
    TypeOfHM ctx (.match_ scrutinee branches) resultTy


/-- Match-branch typing for `TypeOfHM`. Verbatim copy of `TypeOfMatchBranch`
    with the relation renamed: pattern bindings are monomorphic (`Sch 0`), so
    no cofinite type-var quantifier is needed, and the term-var quantifier
    vanishes under de Bruijn levels. -/
inductive TypeOfMatchBranch :
  (ctx : Ctx) → (MatchPattern × Expr) → (tyName : TyName) → (tyArgs : List Ty) → (resultTy : Ty) → Prop
  | mk {ctor : Ctor} {ctx : Ctx} {c : CtorName} {n : Nat} :
    LookupList.get? ctx.ctors c = some ctor →
    ctor.tyName = tyName →
    ctor.paramCount = tyArgs.length →
    n = ctor.contents.length →
    List.Forall₂ (InstantiatesBy tyArgs) ctor.contents instContents →
    patternBindings = instContents.map PolyTy.mkTrivial →
    bodyCtx = {ctx with env := patternBindings ++ ctx.env} →
    TypeOfHM bodyCtx bodyExpr resultTy →
    TypeOfMatchBranch ctx (.named c n, bodyExpr) tyName tyArgs resultTy
  /-- A wildcard branch binds nothing and types its body in the unextended
      context; it imposes no constraint on the scrutinee's constructors. -/
  | wildcard {ctx : Ctx} :
    TypeOfHM ctx bodyExpr resultTy →
    TypeOfMatchBranch ctx (.wildcard, bodyExpr) tyName tyArgs resultTy

end


/-! ### Cofinite typing-at-scheme predicates. -/

/-- `t` types at *every* opening of `M` by sufficiently-fresh names. The `L`
    is the cofinite exclusion set; existentially quantified at the use site.
    This is exactly the cofinite premise of `TypeOfHM.letIn`, packaged. -/
def HasSchemeVars (L : List Nat) (ctx : Ctx) (e : Expr) (M : PolyTy) : Prop :=
  ∀ Xs : List Nat, FreshNames L M.paramCount Xs →
    TypeOfHM ctx e (M.openVars Xs)

/-- `t` types at *every* type-level instance of `M` (by LC types of the
    right arity). This is what `subst_lemma`'s `u` premise demands. -/
def HasScheme (ctx : Ctx) (e : Expr) (M : PolyTy) : Prop :=
  ∀ Vs : List Ty, Ty.AreLC M.paramCount Vs →
    TypeOfHM ctx e (M.openWith Vs)


/-! ### Key commute lemmas. -/

/-- An element is not in `TyList.freeVars tys` iff it's not in any element's
    freeVars. Standard distribution over dedup'd concatenation. -/
theorem TyList.not_mem_freeVars_iff {Z : Nat} {tys : List Ty} :
    Z ∉ TyList.freeVars tys ↔ ∀ t ∈ tys, Z ∉ t.freeVars := by
  induction tys with
  | nil => simp [TyList.freeVars]
  | cons hd tl ih =>
    simp only [TyList.freeVars, List.mem_dedup, List.mem_append, not_or,
               List.mem_cons, forall_eq_or_imp]
    rw [ih]

/-- If every element of `tys` is unchanged by `Ty.substFvar Z U`, then so is
    `TyList.substFvar Z U tys`. Plain list induction; used in `customTy`
    cases of the LHS lemmas. -/
private theorem TyList.substFvar_eq_self_of_all
    {Z : Nat} {U : Ty} {tys : List Ty}
    (h_all : ∀ t ∈ tys, Ty.substFvar Z U t = t) :
    TyList.substFvar Z U tys = tys := by
  induction tys with
  | nil => rfl
  | cons hd tl ih =>
    simp only [TyList.substFvar, List.cons.injEq]
    refine ⟨h_all hd List.mem_cons_self, ih ?_⟩
    intro t ht
    exact h_all t (List.mem_cons_of_mem _ ht)

theorem Ty.substFvar_fresh {Z : Nat} {U ty : Ty}
    (h : Z ∉ ty.freeVars) :
    Ty.substFvar Z U ty = ty := by
  induction ty using Ty.rec_strong with
  | prim _ => rfl
  | arrow a b ih_a ih_b =>
    simp only [Ty.freeVars, List.mem_dedup, List.mem_append, not_or] at h
    simp only [Ty.substFvar, Ty.arrow.injEq]
    exact ⟨ih_a h.1, ih_b h.2⟩
  | bvar _ => rfl
  | fvar n =>
    simp only [Ty.freeVars, List.mem_singleton] at h
    simp only [Ty.substFvar, if_neg (Ne.symm h)]
  | customTy _ tys ih =>
    simp only [Ty.freeVars] at h
    have h' : ∀ t ∈ tys, Z ∉ t.freeVars :=
      TyList.not_mem_freeVars_iff.mp h
    simp only [Ty.substFvar, Ty.customTy.injEq, true_and]
    exact TyList.substFvar_eq_self_of_all (fun t ht => ih t ht (h' t ht))

/-- Instantiation is a no-op on locally-closed types: nothing to instantiate. -/
private theorem TyList.instantiate_eq_self_of_all_lc
    {σ : Nat → Ty} {tys : List Ty}
    (h_all : ∀ t ∈ tys, Ty.IsLC t)
    (ih : ∀ t ∈ tys, Ty.IsLC t → Ty.instantiate σ t = t) :
    TyList.instantiate σ tys = tys := by
  induction tys with
  | nil => rfl
  | cons hd tl ih_tl =>
    simp only [TyList.instantiate, List.cons.injEq]
    refine ⟨ih hd List.mem_cons_self (h_all hd List.mem_cons_self), ?_⟩
    exact ih_tl
      (fun t ht => h_all t (List.mem_cons_of_mem _ ht))
      (fun t ht => ih t (List.mem_cons_of_mem _ ht))

theorem Ty.instantiate_eq_self_of_lc {σ : Nat → Ty} {ty : Ty}
    (h : Ty.IsLC ty) :
    Ty.instantiate σ ty = ty := by
  induction ty using Ty.rec_strong with
  | prim _ => rfl
  | arrow a b ih_a ih_b =>
    cases h with
    | arrow h_a h_b =>
      simp only [Ty.instantiate, Ty.arrow.injEq]
      exact ⟨ih_a h_a, ih_b h_b⟩
  | bvar _ =>
    cases h with
    | bvar h_lt => exact absurd h_lt (by omega)
  | fvar _ => rfl
  | customTy nm tys ih =>
    cases h with
    | customTy h_all =>
      simp only [Ty.instantiate, Ty.customTy.injEq, true_and]
      exact TyList.instantiate_eq_self_of_all_lc h_all ih

/-- `substFvar` swaps with `instantiate` element-wise on a list, given the
    pointwise swap on each element. -/
private theorem TyList.substFvar_instantiate_swap
    {Z : Nat} {U : Ty} {σ : Nat → Ty} {tys : List Ty}
    (ih : ∀ t ∈ tys,
            Ty.substFvar Z U (Ty.instantiate σ t)
              = Ty.instantiate σ (Ty.substFvar Z U t)) :
    TyList.substFvar Z U (TyList.instantiate σ tys)
      = TyList.instantiate σ (TyList.substFvar Z U tys) := by
  induction tys with
  | nil => rfl
  | cons hd tl ih_tl =>
    simp only [TyList.substFvar, TyList.instantiate, List.cons.injEq]
    refine ⟨ih hd List.mem_cons_self, ?_⟩
    exact ih_tl (fun t ht => ih t (List.mem_cons_of_mem _ ht))

theorem Ty.substFvar_openVars
    {Z : Nat} {U ty : Ty} {Xs : List Nat}
    (h_lc : Ty.IsLC U)
    (h_Z_not_in_Xs : Z ∉ Xs) :
    Ty.substFvar Z U (Ty.openVars Xs ty)
      = Ty.openVars Xs (Ty.substFvar Z U ty) := by
  -- `openVars` is just `instantiate` with the specific substitution
  -- `i ↦ Xs[i]? .elim (.bvar i) .fvar`. Unfold and induct on `ty`.
  unfold Ty.openVars
  induction ty using Ty.rec_strong with
  | prim _ => rfl
  | arrow a b ih_a ih_b =>
    simp only [Ty.instantiate, Ty.substFvar, Ty.arrow.injEq]
    exact ⟨ih_a, ih_b⟩
  | bvar i =>
    simp only [Ty.instantiate, Ty.substFvar]
    -- Goal: substFvar Z U (Xs[i]?.elim (.bvar i) .fvar) = Xs[i]?.elim (.bvar i) .fvar
    cases h_xs : Xs[i]? with
    | none => simp [Ty.substFvar]
    | some x =>
      have h_mem : x ∈ Xs := List.mem_of_getElem? h_xs
      have h_ne : x ≠ Z := fun heq => h_Z_not_in_Xs (heq ▸ h_mem)
      simp [Ty.substFvar, h_ne]
  | fvar n =>
    simp only [Ty.instantiate, Ty.substFvar]
    -- LHS: if n=Z then U else .fvar n
    -- RHS: instantiate σ (if n=Z then U else .fvar n)
    by_cases h_n : n = Z
    · simp only [if_pos h_n]
      -- Need U = instantiate σ U
      exact (Ty.instantiate_eq_self_of_lc h_lc).symm
    · simp only [if_neg h_n, Ty.instantiate]
  | customTy nm tys ih =>
    simp only [Ty.instantiate, Ty.substFvar, Ty.customTy.injEq, true_and]
    exact TyList.substFvar_instantiate_swap (fun t ht => ih t ht)

/-- `substFvar` commutes with offset opening (`Ty.openVarsFrom`), mirroring
    `Ty.substFvar_openVars`: the only new wrinkle is the `i < d` guard. -/
theorem Ty.substFvar_openVarsFrom
    {Z d : Nat} {U ty : Ty} {Xs : List Nat}
    (h_lc : Ty.IsLC U) (h_Z_not_in_Xs : Z ∉ Xs) :
    Ty.substFvar Z U (Ty.openVarsFrom d Xs ty)
      = Ty.openVarsFrom d Xs (Ty.substFvar Z U ty) := by
  unfold Ty.openVarsFrom
  induction ty using Ty.rec_strong with
  | prim _ => rfl
  | arrow a b ih_a ih_b =>
    simp only [Ty.instantiate, Ty.substFvar, Ty.arrow.injEq]; exact ⟨ih_a, ih_b⟩
  | bvar i =>
    simp only [Ty.instantiate, Ty.substFvar]
    by_cases h_d : i < d
    · simp only [if_pos h_d, Ty.substFvar]
    · simp only [if_neg h_d]
      cases h_xs : Xs[i - d]? with
      | none => simp [Ty.substFvar]
      | some x =>
        have h_ne : x ≠ Z := fun heq => h_Z_not_in_Xs (heq ▸ List.mem_of_getElem? h_xs)
        simp [Ty.substFvar, h_ne]
  | fvar n =>
    simp only [Ty.instantiate, Ty.substFvar]
    by_cases h_n : n = Z
    · simp only [if_pos h_n]; exact (Ty.instantiate_eq_self_of_lc h_lc).symm
    · simp only [if_neg h_n, Ty.instantiate]
  | customTy nm tys ih =>
    simp only [Ty.instantiate, Ty.substFvar, Ty.customTy.injEq, true_and]
    exact TyList.substFvar_instantiate_swap (fun t ht => ih t ht)

/-- `substTyFvar` commutes with `openTyVarsAux` (offset opening of a term's scoped
    type variables), given the substituted-in type is locally closed and `Z` is
    not an opening name. The term-level analogue of `Ty.substFvar_openVarsFrom`. -/
theorem Expr.substTyFvar_openTyVarsAux
    {Z : Nat} {U : Ty} {Xs : List Nat}
    (h_lc : Ty.IsLC U) (h_Z : Z ∉ Xs) :
    ∀ (e : Expr) (d : Nat),
      (e.openTyVarsAux d Xs).substTyFvar Z U
        = (e.substTyFvar Z U).openTyVarsAux d Xs := by
  intro e
  induction e using Expr.rec_strong with
  | primLit p => intro d; rfl
  | app f inp ih_f ih_i =>
    intro d; simp only [Expr.openTyVarsAux, Expr.substTyFvar]; rw [ih_f d, ih_i d]
  | lambda ann body ih =>
    intro d
    cases ann with
    | none => simp only [Expr.openTyVarsAux, Expr.substTyFvar, Option.map_none]; rw [ih d]
    | some t =>
      simp only [Expr.openTyVarsAux, Expr.substTyFvar, Option.map_some]
      rw [Ty.substFvar_openVarsFrom h_lc h_Z, ih d]
  | letIn ann be body ih_be ih_body =>
    intro d
    cases ann with
    | none =>
      simp only [Expr.openTyVarsAux, Expr.substTyFvar, Option.map_none]
      rw [ih_be d, ih_body d]
    | some σ =>
      simp only [Expr.openTyVarsAux, Expr.substTyFvar, Option.map_some, PolyTy.substFvar]
      rw [Ty.substFvar_openVarsFrom h_lc h_Z, ih_be (d + σ.paramCount), ih_body d]
  | var n => intro d; rfl
  | ctor nm => intro d; rfl
  | match_ scrut branches ih_scrut ih_branches =>
    intro d
    simp only [Expr.openTyVarsAux, Expr.substTyFvar, Expr.match_.injEq]
    refine ⟨ih_scrut d, ?_⟩
    revert ih_branches
    induction branches with
    | nil => intro _; rfl
    | cons hd tl ih_tl =>
      intro ih_branches
      obtain ⟨pat, body⟩ := hd
      simp only [BranchList.openTyVarsAux, BranchList.substTyFvar]
      rw [ih_branches pat body List.mem_cons_self d,
          ih_tl (fun pat' body' hm => ih_branches pat' body' (List.mem_cons_of_mem _ hm))]

/-- `substTyFvar` commutes with the top-level `Expr.openTyVars`. -/
theorem Expr.substTyFvar_openTyVars
    {Z : Nat} {U : Ty} {Xs : List Nat} {e : Expr}
    (h_lc : Ty.IsLC U) (h_Z : Z ∉ Xs) :
    (e.openTyVars Xs).substTyFvar Z U = (e.substTyFvar Z U).openTyVars Xs := by
  unfold Expr.openTyVars
  exact Expr.substTyFvar_openTyVarsAux h_lc h_Z e 0

/-- `substTyFvar` commutes with `openBoundTyVars` (the `let`-rule opener),
    threading the substitution through the annotation. -/
theorem Expr.substTyFvar_openBoundTyVars
    {Z : Nat} {U : Ty} {Xs : List Nat} {ann : Option PolyTy} {e : Expr}
    (h_lc : Ty.IsLC U) (h_Z : Z ∉ Xs) :
    (Expr.openBoundTyVars ann Xs e).substTyFvar Z U
      = Expr.openBoundTyVars (ann.map (PolyTy.substFvar Z U)) Xs (e.substTyFvar Z U) := by
  cases ann with
  | none => rfl
  | some σ =>
    simp only [Expr.openBoundTyVars, Option.map_some]
    exact Expr.substTyFvar_openTyVars h_lc h_Z

/-- `shiftFrom` (a term-variable renumbering) commutes with `openTyVarsAux`
    (opening scoped type variables in annotations): they touch disjoint parts of
    a term, so the order is irrelevant. Needed for `weaken_env`'s `letIn`
    cofinite case (the opened bound expression must be weakened). -/
theorem Expr.shiftFrom_openTyVarsAux {Xs : List Nat} (n : Nat) :
    ∀ (e : Expr) (d k : Nat),
      (e.openTyVarsAux d Xs).shiftFrom k n = (e.shiftFrom k n).openTyVarsAux d Xs := by
  intro e
  induction e using Expr.rec_strong with
  | primLit p => intro d k; rfl
  | app f inp ih_f ih_i =>
    intro d k; simp only [Expr.openTyVarsAux, Expr.shiftFrom]; rw [ih_f d k, ih_i d k]
  | lambda ann body ih =>
    intro d k; simp only [Expr.openTyVarsAux, Expr.shiftFrom]; rw [ih d (k + 1)]
  | letIn ann be body ih_be ih_body =>
    intro d k
    cases ann with
    | none =>
      simp only [Expr.openTyVarsAux, Expr.shiftFrom]; rw [ih_be d k, ih_body d (k + 1)]
    | some σ =>
      simp only [Expr.openTyVarsAux, Expr.shiftFrom]
      rw [ih_be (d + σ.paramCount) k, ih_body d (k + 1)]
  | var m => intro d k; simp only [Expr.openTyVarsAux, Expr.shiftFrom]; split <;> rfl
  | ctor nm => intro d k; rfl
  | match_ scrut branches ih_scrut ih_branches =>
    intro d k
    simp only [Expr.openTyVarsAux, Expr.shiftFrom, Expr.match_.injEq]
    refine ⟨ih_scrut d k, ?_⟩
    revert ih_branches
    induction branches with
    | nil => intro _; rfl
    | cons hd tl ih_tl =>
      intro ih_branches
      obtain ⟨pat, body⟩ := hd
      simp only [BranchList.openTyVarsAux, BranchList.shiftFrom]
      rw [ih_branches pat body List.mem_cons_self d (k + pat.bindCount),
          ih_tl (fun pat' body' hm => ih_branches pat' body' (List.mem_cons_of_mem _ hm))]

/-- `shiftFrom` commutes with the top-level `Expr.openTyVars`. -/
theorem Expr.shiftFrom_openTyVars {Xs : List Nat} {e : Expr} (k n : Nat) :
    (e.openTyVars Xs).shiftFrom k n = (e.shiftFrom k n).openTyVars Xs := by
  unfold Expr.openTyVars
  exact Expr.shiftFrom_openTyVarsAux n e 0 k

/-- `shiftFrom` commutes with `openBoundTyVars` (the `let`-rule opener). The
    annotation is untouched by `shiftFrom`. -/
theorem Expr.shiftFrom_openBoundTyVars {ann : Option PolyTy} {Xs : List Nat} {e : Expr}
    (k n : Nat) :
    (Expr.openBoundTyVars ann Xs e).shiftFrom k n
      = Expr.openBoundTyVars ann Xs (e.shiftFrom k n) := by
  cases ann with
  | none => rfl
  | some σ =>
    simp only [Expr.openBoundTyVars]
    exact Expr.shiftFrom_openTyVars k n

/-- Free vars of a list of types (used in `openWith_eq_substFvars_openVars`'s
    freshness condition). -/
def Ty.freeVarsList : List Ty → List Nat
  | []       => []
  | hd :: tl => (hd.freeVars ++ Ty.freeVarsList tl).dedup

/-! #### `substFvars` distribution + key lemmas (toward `typ_substs_intro`). -/

theorem TyList.substFvar_eq_map {Z : Nat} {U : Ty} {tys : List Ty} :
    TyList.substFvar Z U tys = tys.map (Ty.substFvar Z U) := by
  induction tys with
  | nil => rfl
  | cons hd tl ih => simp only [TyList.substFvar, List.map_cons, ih]

theorem TyList.instantiate_eq_map {σ : Nat → Ty} {tys : List Ty} :
    TyList.instantiate σ tys = tys.map (Ty.instantiate σ) := by
  induction tys with
  | nil => rfl
  | cons hd tl ih => simp only [TyList.instantiate, List.map_cons, ih]

theorem Ty.substFvars_prim {pairs : List (Nat × Ty)} {p : PrimTy} :
    Ty.substFvars pairs (.prim p) = .prim p := by
  induction pairs with
  | nil => rfl
  | cons hd tl ih => obtain ⟨Z, U⟩ := hd; simpa only [Ty.substFvars, Ty.substFvar] using ih

theorem Ty.substFvars_bvar {pairs : List (Nat × Ty)} {i : Nat} :
    Ty.substFvars pairs (.bvar i) = .bvar i := by
  induction pairs with
  | nil => rfl
  | cons hd tl ih => obtain ⟨Z, U⟩ := hd; simpa only [Ty.substFvars, Ty.substFvar] using ih

theorem Ty.substFvars_arrow {pairs : List (Nat × Ty)} {a b : Ty} :
    Ty.substFvars pairs (.arrow a b)
      = .arrow (Ty.substFvars pairs a) (Ty.substFvars pairs b) := by
  induction pairs generalizing a b with
  | nil => rfl
  | cons hd tl ih => obtain ⟨Z, U⟩ := hd; simpa only [Ty.substFvars, Ty.substFvar] using ih

theorem Ty.substFvars_customTy {pairs : List (Nat × Ty)} {nm : TyName} {tys : List Ty} :
    Ty.substFvars pairs (.customTy nm tys)
      = .customTy nm (tys.map (Ty.substFvars pairs)) := by
  induction pairs generalizing tys with
  | nil => simp only [Ty.substFvars, List.map_id_fun', id_eq]
  | cons hd tl ih =>
    obtain ⟨Z, U⟩ := hd
    simp only [Ty.substFvars, Ty.substFvar, TyList.substFvar_eq_map]
    rw [ih, List.map_map]
    rfl

/-- Free vars of a single type are contained in the free vars of any list
    containing it (`Ty.freeVarsList` flavour, used for the `Vs` freshness). -/
private theorem Ty.freeVars_subset_freeVarsList {V : Ty} {Vs : List Ty}
    (h : V ∈ Vs) : ∀ x ∈ V.freeVars, x ∈ Ty.freeVarsList Vs := by
  induction Vs with
  | nil => exact absurd h List.not_mem_nil
  | cons hd tl ih =>
    intro x hx
    simp only [Ty.freeVarsList, List.mem_dedup, List.mem_append]
    cases h with
    | head _ => exact .inl hx
    | tail _ h' => exact .inr (ih h' x hx)

/-- Same, but for the private `TyList.freeVars` used inside `(customTy _ _).freeVars`. -/
theorem TyList.mem_freeVars_of_mem {t : Ty} {tys : List Ty} {x : Nat}
    (ht : t ∈ tys) (hx : x ∈ t.freeVars) : x ∈ TyList.freeVars tys := by
  induction tys with
  | nil => exact absurd ht List.not_mem_nil
  | cons hd tl ih =>
    simp only [TyList.freeVars, List.mem_dedup, List.mem_append]
    cases ht with
    | head _ => exact .inl hx
    | tail _ h' => exact .inr (ih h')

/-- Substituting a list of `(key, value)` pairs none of whose keys occur in
    `ty` leaves `ty` unchanged. -/
theorem Ty.substFvars_eq_self_of_no_key {pairs : List (Nat × Ty)} {ty : Ty}
    (h : ∀ p ∈ pairs, p.1 ∉ ty.freeVars) :
    Ty.substFvars pairs ty = ty := by
  induction pairs generalizing ty with
  | nil => rfl
  | cons hd tl ih =>
    obtain ⟨Z, U⟩ := hd
    have hZ : Z ∉ ty.freeVars := h (Z, U) List.mem_cons_self
    simp only [Ty.substFvars]
    rw [Ty.substFvar_fresh hZ]
    exact ih (fun p hp => h p (List.mem_cons_of_mem _ hp))

/-- The key lemma for the `bvar` case of `typ_substs_intro`: substituting the
    zipped `(Xs, Vs)` pairs into `fvar x` (where `x = Xs[i]`, `v = Vs[i]`)
    yields `v`. The first `i` substitutions don't fire (distinct keys, `Xs`
    nodup); the `i`-th fires; later ones don't touch `v` (`Xs` fresh for `Vs`). -/
theorem Ty.substFvars_zip_fvar_eq {Xs : List Nat} {Vs : List Ty}
    {i : Nat} {x : Nat} {v : Ty}
    (h_len : Vs.length = Xs.length)
    (h_nodup : Xs.Nodup)
    (h_fresh : ∀ X ∈ Xs, X ∉ Ty.freeVarsList Vs)
    (hx : Xs[i]? = some x)
    (hv : Vs[i]? = some v) :
    Ty.substFvars (Xs.zip Vs) (.fvar x) = v := by
  induction Xs generalizing Vs i x v with
  | nil => simp at hx
  | cons X0 Xs' ih =>
    cases Vs with
    | nil => simp at h_len
    | cons V0 Vs' =>
      cases i with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hx hv
        -- hx : X0 = x, hv : V0 = v
        simp only [List.zip_cons_cons, Ty.substFvars]
        rw [← hx, show Ty.substFvar X0 V0 (.fvar X0) = V0 by simp [Ty.substFvar], ← hv]
        -- substFvars (Xs'.zip Vs') V0 = V0: no key (∈ Xs') touches V0's fvars
        apply Ty.substFvars_eq_self_of_no_key
        intro p hp hcontra
        have hp1 : p.1 ∈ Xs' := (List.of_mem_zip hp).1
        refine h_fresh p.1 (List.mem_cons_of_mem _ hp1) ?_
        exact Ty.freeVars_subset_freeVarsList List.mem_cons_self p.1 hcontra
      | succ k =>
        simp only [List.getElem?_cons_succ] at hx hv
        have h_X0_notin : X0 ∉ Xs' := (List.nodup_cons.mp h_nodup).1
        have h_x_mem : x ∈ Xs' := List.mem_of_getElem? hx
        have h_ne : x ≠ X0 := fun h => h_X0_notin (h ▸ h_x_mem)
        have h_len' : Vs'.length = Xs'.length := by
          simp only [List.length_cons] at h_len; omega
        have h_fresh' : ∀ X ∈ Xs', X ∉ Ty.freeVarsList Vs' := by
          intro X hX hc
          refine h_fresh X (List.mem_cons_of_mem _ hX) ?_
          simp only [Ty.freeVarsList, List.mem_dedup, List.mem_append]
          exact .inr hc
        simp only [List.zip_cons_cons, Ty.substFvars]
        rw [show Ty.substFvar X0 V0 (.fvar x) = .fvar x by simp [Ty.substFvar, h_ne]]
        exact ih h_len' (List.nodup_cons.mp h_nodup).2 h_fresh' hx hv

/-- The "rename-open" intro lemma — Chargueraud's `typ_substs_intro`.
    Opening `ty` with `Vs` factors through opening with fresh `Xs` followed
    by substituting each `Xi` by the corresponding `Vi`.

    Crucial freshness: `Xs` must be disjoint not only from `ty.freeVars` but
    also from each `Vi.freeVars` — otherwise iterated substitution can
    "double-substitute" (substituting `X₀` into `V₁` if `X₀ ∈ V₁.freeVars`).
    My initial sketch had this incomplete; restored per Chargueraud's actual
    statement. -/
theorem Ty.openWith_eq_substFvars_openVars
    {ty : Ty} {Vs : List Ty} {Xs : List Nat}
    (h_lc_Vs : Ty.AreLC Xs.length Vs)
    (h_Xs_nodup : Xs.Nodup)
    (h_Xs_fresh_ty : ∀ X ∈ Xs, X ∉ ty.freeVars)
    (h_Xs_fresh_Vs : ∀ X ∈ Xs, X ∉ Ty.freeVarsList Vs) :
    Ty.openWith Vs ty
      = Ty.substFvars (Xs.zip Vs) (Ty.openVars Xs ty) := by
  obtain ⟨h_len, _⟩ := h_lc_Vs
  unfold Ty.openWith Ty.openVars
  induction ty using Ty.rec_strong with
  | prim _ =>
    simp only [Ty.instantiate]
    exact (Ty.substFvars_prim).symm
  | arrow a b ih_a ih_b =>
    simp only [Ty.instantiate]
    rw [Ty.substFvars_arrow]
    have ha : ∀ X ∈ Xs, X ∉ a.freeVars := fun X hX hc =>
      h_Xs_fresh_ty X hX (by simp only [Ty.freeVars, List.mem_dedup, List.mem_append]; exact .inl hc)
    have hb : ∀ X ∈ Xs, X ∉ b.freeVars := fun X hX hc =>
      h_Xs_fresh_ty X hX (by simp only [Ty.freeVars, List.mem_dedup, List.mem_append]; exact .inr hc)
    rw [ih_a ha, ih_b hb]
  | bvar i =>
    simp only [Ty.instantiate]
    by_cases h_i : i < Xs.length
    · -- in range: openVars → fvar Xs[i], openWith → Vs[i]
      obtain ⟨x, hx⟩ : ∃ x, Xs[i]? = some x := ⟨_, List.getElem?_eq_getElem h_i⟩
      obtain ⟨v, hv⟩ : ∃ v, Vs[i]? = some v :=
        ⟨_, List.getElem?_eq_getElem (by omega)⟩
      rw [hx, hv]
      simp only [Option.getD, Option.elim]
      exact (Ty.substFvars_zip_fvar_eq h_len h_Xs_nodup h_Xs_fresh_Vs hx hv).symm
    · -- out of range: both sides are bvar i
      have hXi : Xs[i]? = none := List.getElem?_eq_none (by omega)
      have hVi : Vs[i]? = none := List.getElem?_eq_none (by omega)
      rw [hXi, hVi]
      simp only [Option.getD, Option.elim]
      exact (Ty.substFvars_bvar).symm
  | fvar n =>
    simp only [Ty.instantiate]
    -- n ∉ Xs (from freshness), so no substitution fires
    have h_n_notin : n ∉ Xs := by
      intro hn
      exact h_Xs_fresh_ty n hn (by simp [Ty.freeVars])
    refine (Ty.substFvars_eq_self_of_no_key ?_).symm
    intro p hp hc
    -- p.1 ∈ Xs and p.1 ∈ (fvar n).freeVars = [n] ⇒ p.1 = n ⇒ n ∈ Xs, contradiction
    have hp1 : p.1 ∈ Xs := (List.of_mem_zip hp).1
    simp only [Ty.freeVars, List.mem_singleton] at hc
    exact h_n_notin (hc ▸ hp1)
  | customTy nm tys ih =>
    simp only [Ty.instantiate]
    rw [TyList.instantiate_eq_map, TyList.instantiate_eq_map, Ty.substFvars_customTy,
        List.map_map]
    apply congrArg (Ty.customTy nm)
    apply List.map_congr_left
    intro t ht
    have ht_fresh : ∀ X ∈ Xs, X ∉ t.freeVars := fun X hX hc =>
      h_Xs_fresh_ty X hX (TyList.mem_freeVars_of_mem ht hc)
    simpa using ih t ht ht_fresh


/-- **Rename the opening (type level, depth-general).** Opening `t`'s scoped
    `bvar`s (offset `d`) at a fresh block `Ys`, then renaming `Ys ↦ Xs` (as
    `fvar`s), equals opening directly at `Xs`. The freshness side conditions
    (`Ys` nodup, disjoint from `t`'s pre-existing free vars and from `Xs`) ensure
    the rename only touches names introduced by the opening. This is the
    depth-general fact the term-level renamer below recurses with through nested
    schemes; `Ty.openWith_eq_substFvars_openVars` is essentially its `d = 0`
    converse. -/
theorem Ty.substFvars_zip_openVarsFrom {d : Nat} {t : Ty} {Ys Xs : List Nat}
    (h_len : Ys.length = Xs.length) (h_Ys_nodup : Ys.Nodup)
    (h_Ys_t : ∀ y ∈ Ys, y ∉ t.freeVars) (h_Ys_Xs : ∀ y ∈ Ys, y ∉ Xs) :
    Ty.substFvars (Ys.zip (Xs.map (Ty.fvar ·))) (Ty.openVarsFrom d Ys t)
      = Ty.openVarsFrom d Xs t := by
  have h_lenV : (Xs.map (Ty.fvar ·)).length = Ys.length := by
    rw [List.length_map, ← h_len]
  have h_freshV : ∀ Y ∈ Ys, Y ∉ Ty.freeVarsList (Xs.map (Ty.fvar ·)) := by
    intro Y hY hc
    refine h_Ys_Xs Y hY ?_
    clear hY h_len h_Ys_nodup h_Ys_t h_Ys_Xs h_lenV
    induction Xs with
    | nil => simp only [List.map_nil, Ty.freeVarsList] at hc; exact absurd hc List.not_mem_nil
    | cons x xs ih =>
      simp only [List.map_cons, Ty.freeVarsList, List.mem_dedup, List.mem_append] at hc
      cases hc with
      | inl h => simp only [Ty.freeVars, List.mem_singleton] at h; exact h ▸ List.mem_cons_self
      | inr h => exact List.mem_cons_of_mem _ (ih h)
  unfold Ty.openVarsFrom
  induction t using Ty.rec_strong with
  | prim p => simp only [Ty.instantiate, Ty.substFvars_prim]
  | bvar i =>
    simp only [Ty.instantiate]
    by_cases h_d : i < d
    · simp only [if_pos h_d, Ty.substFvars_bvar]
    · simp only [if_neg h_d]
      cases h_ys : Ys[i - d]? with
      | none =>
        have h_xs : Xs[i - d]? = none := by
          rw [List.getElem?_eq_none_iff] at h_ys ⊢; omega
        simp only [h_xs, Option.elim, Ty.substFvars_bvar]
      | some y =>
        have hlt : i - d < Ys.length := by
          obtain ⟨h, _⟩ := List.getElem?_eq_some_iff.mp h_ys; exact h
        have h_xs : Xs[i - d]? = some Xs[i - d] := List.getElem?_eq_getElem (by omega)
        have hvx : (Xs.map (Ty.fvar ·))[i - d]? = some (Ty.fvar Xs[i - d]) := by
          rw [List.getElem?_map, h_xs]; rfl
        simp only [h_xs, Option.elim]
        exact Ty.substFvars_zip_fvar_eq h_lenV h_Ys_nodup h_freshV h_ys hvx
  | fvar n =>
    simp only [Ty.instantiate]
    apply Ty.substFvars_eq_self_of_no_key
    intro p hp hc
    simp only [Ty.freeVars, List.mem_singleton] at hc
    exact h_Ys_t p.1 (List.of_mem_zip hp).1 (hc ▸ by simp [Ty.freeVars])
  | arrow a b iha ihb =>
    simp only [Ty.instantiate, Ty.substFvars_arrow]
    rw [iha (fun y hy hc => h_Ys_t y hy (by
          simp only [Ty.freeVars, List.mem_dedup, List.mem_append]; exact .inl hc)),
        ihb (fun y hy hc => h_Ys_t y hy (by
          simp only [Ty.freeVars, List.mem_dedup, List.mem_append]; exact .inr hc))]
  | customTy nm tys ih =>
    simp only [Ty.instantiate, TyList.instantiate_eq_map, Ty.substFvars_customTy, List.map_map]
    apply congrArg (Ty.customTy nm)
    apply List.map_congr_left
    intro t ht
    have ht_fresh : ∀ y ∈ Ys, y ∉ t.freeVars := fun y hy hc =>
      h_Ys_t y hy (by simp only [Ty.freeVars]; exact TyList.mem_freeVars_of_mem ht hc)
    simpa using ih t ht ht_fresh


/-! ### `substFvar` interaction with the typing-side predicates.

Helpers needed by `typ_subst_preservation`. -/

/-- `substFvar` by an LC type preserves local-closedness. (The `bvar` case is
    vacuous: an LC type has no bvars.) -/
theorem Ty.IsLC.substFvar {Z : Nat} {U ty : Ty}
    (h_U : Ty.IsLC U) (h : Ty.IsLC ty) :
    Ty.IsLC (Ty.substFvar Z U ty) := by
  induction ty using Ty.rec_strong with
  | prim _ => exact .prim
  | arrow a b iha ihb => cases h with | arrow ha hb => exact .arrow (iha ha) (ihb hb)
  | bvar i => cases h with | bvar hlt => exact absurd hlt (by omega)
  | fvar m =>
    simp only [Ty.substFvar]
    by_cases hm : m = Z
    · simp only [if_pos hm]; exact h_U
    · simp only [if_neg hm]; exact .fvar
  | customTy nm tys ih =>
    cases h with
    | customTy hall =>
      simp only [Ty.substFvar]
      apply ContainsBvarsUpTo.customTy
      rw [TyList.substFvar_eq_map]
      intro t ht
      obtain ⟨t0, ht0, rfl⟩ := List.mem_map.mp ht
      exact ih t0 ht0 (hall t0 ht0)

/-- Instantiation is the identity on locally-closed types (reverse of
    `InstantiatesBy.eq_of_closed`): if `ty` has no bvars, it instantiates to
    itself under any `tyArgs`. -/
theorem InstantiatesBy.refl_of_closed {tyArgs : List Ty} {ty : Ty}
    (h : ContainsBvarsUpTo 0 ty) : InstantiatesBy tyArgs ty ty := by
  induction ty using Ty.rec_strong with
  | prim _ => exact .prim
  | arrow a b iha ihb => cases h with | arrow ha hb => exact .arrow (iha ha) (ihb hb)
  | bvar i => cases h with | bvar hlt => exact absurd hlt (by omega)
  | fvar n => exact .fvar
  | customTy nm tys ih =>
    cases h with
    | customTy hall =>
      apply InstantiatesBy.customTy
      have aux : ∀ ts : List Ty, (∀ t ∈ ts, ContainsBvarsUpTo 0 t) →
          (∀ t ∈ ts, InstantiatesBy tyArgs t t) →
          List.Forall₂ (InstantiatesBy tyArgs) ts ts := by
        intro ts
        induction ts with
        | nil => intro _ _; exact .nil
        | cons hd tl ihts =>
          intro hall' hinst'
          exact .cons (hinst' hd List.mem_cons_self)
            (ihts (fun t ht => hall' t (List.mem_cons_of_mem _ ht))
                  (fun t ht => hinst' t (List.mem_cons_of_mem _ ht)))
      exact aux tys hall (fun t ht => ih t ht (hall t ht))

/-- `substFvar` commutes with `InstantiatesBy` (when the replacement `U` is
    LC): substituting fvars then instantiating bvars equals instantiating
    bvars (with the substituted `tyArgs`) then substituting fvars. -/
theorem InstantiatesBy.substFvar {Z : Nat} {U : Ty}
    (h_U_lc : Ty.IsLC U) {ty1 ty2 : Ty} {tyArgs : List Ty}
    (h : InstantiatesBy tyArgs ty1 ty2) :
    InstantiatesBy (tyArgs.map (Ty.substFvar Z U))
      (Ty.substFvar Z U ty1) (Ty.substFvar Z U ty2) := by
  induction ty1 using Ty.rec_strong generalizing ty2 with
  | prim _ => cases h; exact .prim
  | arrow a b iha ihb =>
    cases h with | arrow ha hb => exact .arrow (iha ha) (ihb hb)
  | bvar i =>
    cases h with
    | bvar hsome =>
      simp only [Ty.substFvar]
      apply InstantiatesBy.bvar
      rw [List.getElem?_map, hsome]; rfl
  | fvar n =>
    cases h with
    | fvar =>
      by_cases hn : n = Z
      · simp only [Ty.substFvar, if_pos hn]
        exact InstantiatesBy.refl_of_closed h_U_lc
      · simp only [Ty.substFvar, if_neg hn]; exact .fvar
  | customTy nm tys ih =>
    cases h with
    | customTy hforall =>
      simp only [Ty.substFvar]
      rw [TyList.substFvar_eq_map, TyList.substFvar_eq_map]
      apply InstantiatesBy.customTy
      induction hforall with
      | nil => exact .nil
      | cons hhd htl ihtl =>
        rename_i hd_ty hd_it tl_tys tl_it
        refine .cons (ih hd_ty List.mem_cons_self hhd) ?_
        exact ihtl (fun t ht => ih t (List.mem_cons_of_mem _ ht))

/-- `Env.substFvar` by a fresh `Z` is the identity. -/
theorem Env.substFvar_fresh {Z : Nat} {U : Ty} {env : Env}
    (h : Z ∉ env.freeVars) : env.substFvar Z U = env := by
  induction env with
  | nil => rfl
  | cons hd tl ih =>
    simp only [Env.freeVars, List.mem_dedup, List.mem_append, not_or] at h
    simp only [Env.substFvar, List.map_cons]
    have hd_eq : PolyTy.substFvar Z U hd = hd := by
      obtain ⟨pc, body⟩ := hd
      simp only [PolyTy.substFvar]
      rw [Ty.substFvar_fresh h.1]
    rw [hd_eq]
    have htl : Env.substFvar Z U tl = tl := ih h.2
    simp only [Env.substFvar] at htl
    rw [htl]

theorem Env.substFvar_append {Z : Nat} {U : Ty} {a b : Env} :
    Env.substFvar Z U (a ++ b) = Env.substFvar Z U a ++ Env.substFvar Z U b := by
  simp only [Env.substFvar, List.map_append]

/-- `ContainsBvarsUpTo` is monotone in the bound. -/
theorem ContainsBvarsUpTo.mono {m n : Nat} {ty : Ty} (hle : m ≤ n)
    (h : ContainsBvarsUpTo m ty) : ContainsBvarsUpTo n ty := by
  induction h with
  | prim => exact .prim
  | arrow _ _ iha ihb => exact .arrow iha ihb
  | fvar => exact .fvar
  | customTy _ ih => exact .customTy (fun t ht => ih t ht)
  | bvar hlt => exact .bvar (by omega)

/-- `substFvar` by an LC type preserves any bvar bound (the replacement adds no
    bvars; the original's bvars are untouched). Generalises `Ty.IsLC.substFvar`
    (which is the `n = 0` case). -/
theorem ContainsBvarsUpTo.substFvar {n Z : Nat} {U ty : Ty}
    (h_U : Ty.IsLC U) (h : ContainsBvarsUpTo n ty) :
    ContainsBvarsUpTo n (Ty.substFvar Z U ty) := by
  induction ty using Ty.rec_strong with
  | prim _ => exact .prim
  | arrow a b iha ihb => cases h with | arrow ha hb => exact .arrow (iha ha) (ihb hb)
  | bvar i =>
    cases h with
    | bvar hlt => simp only [Ty.substFvar]; exact .bvar hlt
  | fvar m =>
    simp only [Ty.substFvar]
    by_cases hm : m = Z
    · simp only [if_pos hm]; exact h_U.mono (Nat.zero_le n)
    · simp only [if_neg hm]; exact .fvar
  | customTy nm tys ih =>
    cases h with
    | customTy hall =>
      simp only [Ty.substFvar]
      apply ContainsBvarsUpTo.customTy
      rw [TyList.substFvar_eq_map]
      intro t ht
      obtain ⟨t0, ht0, rfl⟩ := List.mem_map.mp ht
      exact ih t0 ht0 (hall t0 ht0)

/-- Well-formedness of a scheme is preserved by `substFvar` (with LC
    replacement). -/
theorem PolyTy.WF.substFvar {Z : Nat} {U : Ty} {M : PolyTy}
    (h_U_lc : Ty.IsLC U) (h : M.WF) : (M.substFvar Z U).WF :=
  ContainsBvarsUpTo.substFvar h_U_lc h


/-- A type with no free vars contains no particular free var. -/
theorem NoFreeVars.not_mem_freeVars {ty : Ty} (h : NoFreeVars ty) (Z : Nat) :
    Z ∉ ty.freeVars := by
  induction h with
  | prim => simp [Ty.freeVars]
  | arrow _ _ iha ihb =>
    simp only [Ty.freeVars, List.mem_dedup, List.mem_append, not_or]; exact ⟨iha, ihb⟩
  | bvar => simp [Ty.freeVars]
  | customTy _ ih =>
    simp only [Ty.freeVars]
    exact TyList.not_mem_freeVars_iff.mpr (fun t ht => ih t ht)

/-- Substituting a type-fvar is a no-op on a *closed* scheme (one whose body has
    no free type vars). Used to keep annotated-`let` schemes stable under
    `typ_subst_preservation`. -/
theorem PolyTy.substFvar_eq_self_of_closed {Z : Nat} {U : Ty} {σ : PolyTy}
    (h : NoFreeVars σ.body) : PolyTy.substFvar Z U σ = σ := by
  obtain ⟨pc, b⟩ := σ
  simp only [PolyTy.substFvar, Ty.substFvar_fresh (h.not_mem_freeVars Z)]

/-- Every entry of a `bvarRangeFrom` list is a (free-var-free) bound variable. -/
private theorem NoFreeVars.bvarRangeFrom (s n : Nat) :
    ∀ t ∈ Ty.bvarRangeFrom s n, NoFreeVars t := by
  induction n generalizing s with
  | zero => intro t ht; simp [Ty.bvarRangeFrom] at ht
  | succ k ih =>
    intro t ht
    simp only [Ty.bvarRangeFrom, List.mem_cons] at ht
    rcases ht with rfl | ht
    · exact .bvar
    · exact ih (s + 1) t ht

/-- Right-nested arrows over free-var-free pieces are free-var-free. -/
private theorem NoFreeVars.wrapArrows {result : Ty} {args : List Ty}
    (hres : NoFreeVars result) (hargs : ∀ a ∈ args, NoFreeVars a) :
    NoFreeVars (Ty.wrapArrows result args) := by
  induction args with
  | nil => exact hres
  | cons hd tl ih =>
    simp only [Ty.wrapArrows]
    exact .arrow (hargs hd List.mem_cons_self)
      (ih (fun a ha => hargs a (List.mem_cons_of_mem _ ha)))

/-- `substFvar` applied element-wise through a `Forall₂ InstantiatesBy`. -/
theorem InstantiatesBy.forall2_substFvar {Z : Nat} {U : Ty}
    (h_U_lc : Ty.IsLC U) {srcs insts tyArgs : List Ty}
    (h : List.Forall₂ (InstantiatesBy tyArgs) srcs insts) :
    List.Forall₂ (InstantiatesBy (tyArgs.map (Ty.substFvar Z U)))
      (srcs.map (Ty.substFvar Z U)) (insts.map (Ty.substFvar Z U)) := by
  induction h with
  | nil => exact .nil
  | cons hhd _ ih => exact .cons (InstantiatesBy.substFvar h_U_lc hhd) ih

/-- `substFvar` distributes over a list of trivial (monomorphic) bindings,
    landing inside both the `map` and the trivialisation. -/
theorem Env.substFvar_map_mkTrivial {Z : Nat} {U : Ty} {ics : List Ty} :
    Env.substFvar Z U (ics.map PolyTy.mkTrivial)
      = (ics.map (Ty.substFvar Z U)).map PolyTy.mkTrivial := by
  simp only [Env.substFvar, List.map_map]
  apply List.map_congr_left
  intro c _
  rfl

/-- A constructor's polytype body has no free type variables (its only type
    variables are the bound ones from the constructor's own `paramCount`). -/
theorem Ctor.toTy_body_noFreeVars (ctor : Ctor) : NoFreeVars ctor.toTy.body := by
  show NoFreeVars (Ty.wrapArrows (Ty.customTy ctor.tyName (Ty.bvarRange ctor.paramCount))
    ctor.contents)
  apply NoFreeVars.wrapArrows
  · exact NoFreeVars.customTy (fun t ht => NoFreeVars.bvarRangeFrom 0 ctor.paramCount t ht)
  · exact ctor.closed

private theorem ContainsBvarsUpTo.wrapArrows {n : Nat} {result : Ty} {args : List Ty}
    (hres : ContainsBvarsUpTo n result) (hargs : ∀ a ∈ args, ContainsBvarsUpTo n a) :
    ContainsBvarsUpTo n (Ty.wrapArrows result args) := by
  induction args with
  | nil => exact hres
  | cons hd tl ih =>
    exact .arrow (hargs hd (List.mem_cons_self ..))
      (ih (fun a ha => hargs a (List.mem_cons_of_mem _ ha)))

private theorem ContainsBvarsUpTo.bvarRangeFrom (s n : Nat) :
    ∀ t ∈ Ty.bvarRangeFrom s n, ContainsBvarsUpTo (s + n) t := by
  induction n generalizing s with
  | zero => intro t ht; simp [Ty.bvarRangeFrom] at ht
  | succ k ih =>
    intro t ht
    simp only [Ty.bvarRangeFrom, List.mem_cons] at ht
    rcases ht with rfl | ht
    · exact .bvar (by omega)
    · exact (ih (s + 1) t ht).mono (by omega)

/-- A constructor's type scheme is well-formed: its body's bvars all lie within
    `paramCount` (from `Ctor.bound` on the contents and the result `customTy`). -/
theorem Ctor.toTy_wf (ctor : Ctor) : ctor.toTy.WF := by
  show ContainsBvarsUpTo ctor.paramCount
    (Ty.wrapArrows (Ty.customTy ctor.tyName (Ty.bvarRange ctor.paramCount)) ctor.contents)
  apply ContainsBvarsUpTo.wrapArrows
  · exact .customTy (fun t ht => by
      simpa using ContainsBvarsUpTo.bvarRangeFrom 0 ctor.paramCount t ht)
  · exact ctor.bound


/-! ### Metatheory infrastructure. -/

/-- The per-branch motive used internally by `TypeOfHM.rec_strong`. For a branch
    `(pat, body)` it bundles the inverted `TypeOfMatchBranch` structure (the
    constructor lookup, type-name/arity agreements, the field instantiations)
    together with an induction hypothesis on the branch *body* derivation.

    Phrased existentially so the `mk` minor premise of the auto-generated mutual
    recursor `TypeOfHM.rec` can produce it from the body IH, and the `match_`
    case of a `rec_strong` proof can destructure it to rebuild each branch. -/
abbrev TypeOfHM.BranchMotive
    (motive : (ctx : Ctx) → (e : Expr) → (τ : Ty) → TypeOfHM ctx e τ → Prop)
    (ctx : Ctx) (branch : MatchPattern × Expr) (tyName : TyName)
    (tyArgs : List Ty) (resultTy : Ty) : Prop :=
  (∃ (ctor : Ctor) (c : CtorName) (n : Nat) (instContents : List Ty),
    branch.1 = .named c n ∧
    LookupList.get? ctx.ctors c = some ctor ∧
    ctor.tyName = tyName ∧
    ctor.paramCount = tyArgs.length ∧
    n = ctor.contents.length ∧
    List.Forall₂ (InstantiatesBy tyArgs) ctor.contents instContents ∧
    ∃ hbody : TypeOfHM ⟨instContents.map PolyTy.mkTrivial ++ ctx.env, ctx.ctors⟩ branch.2 resultTy,
      motive ⟨instContents.map PolyTy.mkTrivial ++ ctx.env, ctx.ctors⟩ branch.2 resultTy hbody)
  ∨
  (branch.1 = .wildcard ∧
    ∃ hbody : TypeOfHM ctx branch.2 resultTy,
      motive ctx branch.2 resultTy hbody)

/--
Strong induction principle for the mutual `TypeOfHM`/`TypeOfMatchBranch`
relation, packaged with a *single* motive on `TypeOfHM` derivations so the
metatheory can do `induction h using TypeOfHM.rec_strong` and never touch the
mutual recursor / `motive_2` directly.

Each constructor's minor premise carries induction hypotheses for its recursive
sub-derivations. The crucial cases:

* `letIn`: the cofinite premise `hcofin` (which types the *opened* bound
  expression `Expr.openBoundTyVars ann Xs boundExpr` — a transform of
  `boundExpr`, not a structural subterm) comes with an IH
  `∀ Xs hf, motive … (hcofin Xs hf)`, plus the body IH. This is what the
  structural `Expr.rec_strong` cannot provide.
* `match_`: each branch carries (via `BranchMotive`) the inverted branch
  structure together with an IH on that branch's body derivation.

Built on the auto-generated `TypeOfHM.rec` with an internal
`motive_2 := BranchMotive`. -/
@[elab_as_elim]
theorem TypeOfHM.rec_strong
    {motive : (ctx : Ctx) → (e : Expr) → (τ : Ty) → TypeOfHM ctx e τ → Prop}
    (primLitUnit : ∀ {ctx : Ctx}, motive ctx (.primLit .unit) (.prim .unit) .primLitUnit)
    (primLitInt : ∀ {ctx : Ctx} {n : ℤ}, motive ctx (.primLit (.int n)) (.prim .int) .primLitInt)
    (primLitNat : ∀ {ctx : Ctx} {n : ℕ}, motive ctx (.primLit (.nat n)) (.prim .nat) .primLitNat)
    -- (primLitBool : ∀ {ctx : Ctx} {b : Bool}, motive ctx (.primLit (.bool b)) (.prim .bool) .primLitBool)
    (primLitStr : ∀ {ctx : Ctx} {s : String}, motive ctx (.primLit (.str s)) (.prim .str) .primLitStr)
    (lambda : ∀ {paramTy : Ty} {ann : Option Ty} {bodyCtx ctx : Ctx} {body : Expr} {bodyTy : Ty}
      (hpc : ContainsBvarsUpTo 0 paramTy) (hann : ∀ T, ann = some T → paramTy = T)
      (heq : bodyCtx = { env := PolyTy.mkTrivial paramTy :: ctx.env, ctors := ctx.ctors })
      (hbody : TypeOfHM bodyCtx body bodyTy),
      motive bodyCtx body bodyTy hbody →
      motive ctx (.lambda ann body) (.arrow paramTy bodyTy) (.lambda hpc hann heq hbody))
    (app : ∀ {ctx : Ctx} {f : Expr} {argTy retTy : Ty} {input : Expr}
      (hf : TypeOfHM ctx f (.arrow argTy retTy)) (hinput : TypeOfHM ctx input argTy),
      motive ctx f (.arrow argTy retTy) hf → motive ctx input argTy hinput →
      motive ctx (.app f input) retTy (.app hf hinput))
    (letIn : ∀ {ann : Option PolyTy} {ctx : Ctx} {boundExpr : Expr} {bodyCtx : Ctx} {body : Expr}
      {bodyTy : Ty} {M : PolyTy} {L : List Nat}
      (hwf : M.WF) (hann : ∀ σ, ann = some σ → M = σ)
      (hcofin : ∀ Xs, FreshNames L M.paramCount Xs →
        TypeOfHM ctx (Expr.openBoundTyVars ann Xs boundExpr) (M.openVars Xs))
      (heq : bodyCtx = { env := M :: ctx.env, ctors := ctx.ctors })
      (hbody : TypeOfHM bodyCtx body bodyTy),
      (∀ Xs (hf : FreshNames L M.paramCount Xs),
        motive ctx (Expr.openBoundTyVars ann Xs boundExpr) (M.openVars Xs) (hcofin Xs hf)) →
      motive bodyCtx body bodyTy hbody →
      motive ctx (.letIn ann boundExpr body) bodyTy (.letIn hwf hann hcofin heq hbody))
    (var : ∀ {dbl : Nat} {polyTy : PolyTy} {tyArgs : List Ty} {ty : Ty} {ctx : Ctx}
      (hlook : ctx.env[dbl]? = some polyTy) (htyargs : ∀ tyArg ∈ tyArgs, ContainsBvarsUpTo 0 tyArg)
      (hinst : InstantiatesBy tyArgs polyTy.body ty),
      motive ctx (.var dbl) ty (.var hlook htyargs hinst))
    (ctor : ∀ {name : CtorName} {ctorr : Ctor} {tyArgs : List Ty} {ty : Ty} {ctx : Ctx}
      (hlook : LookupList.get? ctx.ctors name = some ctorr)
      (htyargs : ∀ tyArg ∈ tyArgs, ContainsBvarsUpTo 0 tyArg)
      (hinst : InstantiatesBy tyArgs ctorr.toTy.body ty),
      motive ctx (.ctor name) ty (.ctor hlook htyargs hinst))
    (match_ : ∀ {ctx : Ctx} {scrutinee : Expr} {tyName : TyName} {tyArgs : List Ty}
      {branches : List (MatchPattern × Expr)} {resultTy : Ty}
      (hscrut : TypeOfHM ctx scrutinee (.customTy tyName tyArgs)) (hne : branches ≠ [])
      (hfirst : ∃ c n body rest, branches = (MatchPattern.named c n, body) :: rest)
      (hbrs : ∀ branch ∈ branches, TypeOfMatchBranch ctx branch tyName tyArgs resultTy),
      motive ctx scrutinee (.customTy tyName tyArgs) hscrut →
      (∀ branch ∈ branches, TypeOfHM.BranchMotive motive ctx branch tyName tyArgs resultTy) →
      motive ctx (.match_ scrutinee branches) resultTy (.match_ hscrut hne hfirst hbrs))
    {ctx : Ctx} {e : Expr} {τ : Ty} (h : TypeOfHM ctx e τ) : motive ctx e τ h := by
  induction h using TypeOfHM.rec
    (motive_2 := fun ctx br tyName tyArgs resultTy _ =>
      TypeOfHM.BranchMotive motive ctx br tyName tyArgs resultTy) with
  | primLitUnit => exact primLitUnit
  | primLitInt => exact primLitInt
  | primLitNat => exact primLitNat
  -- | primLitBool => exact primLitBool
  | primLitStr => exact primLitStr
  | lambda hpc hann heq hbody ihbody => exact lambda hpc hann heq hbody ihbody
  | app hf hinput ihf ihinput => exact app hf hinput ihf ihinput
  | letIn hwf hann hcofin heq hbody ihcofin ihbody =>
      exact letIn hwf hann hcofin heq hbody ihcofin ihbody
  | var hlook htyargs hinst => exact var hlook htyargs hinst
  | ctor hlook htyargs hinst => exact ctor hlook htyargs hinst
  | match_ hscrut hne hfirst hbrs ihscrut ihbrs => exact match_ hscrut hne hfirst hbrs ihscrut ihbrs
  | mk hlook htyName hpc hcontents hinstC hpb heq hbodyT ih =>
      subst hpb; subst heq
      exact Or.inl ⟨_, _, _, _, rfl, hlook, htyName, hpc, hcontents, hinstC, hbodyT, ih⟩
  | wildcard hbodyT ih =>
      exact Or.inr ⟨rfl, hbodyT, ih⟩

/-- Membership in a `BranchList.substTyFvar`ed branch list reflects back to the
    original: each member is `(pat, body.substTyFvar Z U)` for an original
    `(pat, body) ∈ branches`. -/
theorem BranchList.mem_substTyFvar {Z : Nat} {U : Ty}
    {branches : List (MatchPattern × Expr)} {branch' : MatchPattern × Expr}
    (h : branch' ∈ BranchList.substTyFvar Z U branches) :
    ∃ pat body, (pat, body) ∈ branches ∧ branch' = (pat, body.substTyFvar Z U) := by
  induction branches with
  | nil => simp only [BranchList.substTyFvar] at h; exact absurd h List.not_mem_nil
  | cons hd tl ih =>
    obtain ⟨pat, body⟩ := hd
    simp only [BranchList.substTyFvar, List.mem_cons] at h
    cases h with
    | inl heq => exact ⟨pat, body, List.mem_cons_self, heq⟩
    | inr h' =>
      obtain ⟨p, b, hmem, heq⟩ := ih h'
      exact ⟨p, b, List.mem_cons_of_mem _ hmem, heq⟩

/-- Membership in a `BranchList.shiftFrom`ed branch list reflects back to the
    original: each member is `(pat, body.shiftFrom (threshold + pat.bindCount) n)`
    for an original `(pat, body) ∈ branches`. -/
theorem BranchList.mem_shiftFrom {threshold n : Nat}
    {branches : List (MatchPattern × Expr)} {branch' : MatchPattern × Expr}
    (h : branch' ∈ BranchList.shiftFrom threshold n branches) :
    ∃ pat body, (pat, body) ∈ branches ∧
      branch' = (pat, body.shiftFrom (threshold + pat.bindCount) n) := by
  induction branches with
  | nil => simp only [BranchList.shiftFrom] at h; exact absurd h List.not_mem_nil
  | cons hd tl ih =>
    obtain ⟨pat, body⟩ := hd
    simp only [BranchList.shiftFrom, List.mem_cons] at h
    cases h with
    | inl heq => exact ⟨pat, body, List.mem_cons_self, heq⟩
    | inr h' =>
      obtain ⟨p, b, hmem, heq⟩ := ih h'
      exact ⟨p, b, List.mem_cons_of_mem _ hmem, heq⟩

/-- Membership in a `BranchList.substN`ed branch list reflects to the original:
    each member is `(pat, body.substN (k + pat.bindCount) vs)` for an original
    `(pat, body) ∈ branches`. -/
theorem BranchList.mem_substN {k : Nat} {vs : List Expr}
    {branches : List (MatchPattern × Expr)} {branch' : MatchPattern × Expr}
    (h : branch' ∈ BranchList.substN k vs branches) :
    ∃ pat body, (pat, body) ∈ branches ∧
      branch' = (pat, body.substN (k + pat.bindCount) vs) := by
  induction branches with
  | nil => simp only [BranchList.substN] at h; exact absurd h List.not_mem_nil
  | cons hd tl ih =>
    obtain ⟨pat, body⟩ := hd
    simp only [BranchList.substN, List.mem_cons] at h
    cases h with
    | inl heq => exact ⟨pat, body, List.mem_cons_self, heq⟩
    | inr h' =>
      obtain ⟨p, b, hmem, heq⟩ := ih h'
      exact ⟨p, b, List.mem_cons_of_mem _ hmem, heq⟩

/-- Type-substitution preserves typing (uniform form): substituting a single
    type variable `Z ↦ U` (with `U` locally closed) simultaneously through the
    env, the term's annotations (`Expr.substTyFvar`), and the type preserves the
    derivation. Proven by induction on the derivation (`rec_strong`) so the
    `letIn` cofinite case — whose premise types a *transform* of the bound
    expression, not a structural subterm — goes through.

    Chargueraud's `typing_typ_subst`. -/
theorem TypeOfHM.typ_subst_preservation_uniform {Z : Nat} {U : Ty} (h_U_lc : U.IsLC)
    {ctx : Ctx} {e : Expr} {τ : Ty} (h : TypeOfHM ctx e τ) :
    TypeOfHM ⟨ctx.env.substFvar Z U, ctx.ctors⟩ (e.substTyFvar Z U) (Ty.substFvar Z U τ) := by
  induction h using TypeOfHM.rec_strong with
  | primLitUnit => exact .primLitUnit
  | primLitInt => exact .primLitInt
  | primLitNat => exact .primLitNat
  -- | primLitBool => exact .primLitBool
  | primLitStr => exact .primLitStr
  | app _ _ ihf ihinput =>
    simp only [Expr.substTyFvar]
    simp only [Ty.substFvar] at ihf
    exact .app ihf ihinput
  | lambda hpc hann heq hbody ihbody =>
    subst heq
    expose_names
    simp only [Ty.substFvar, Expr.substTyFvar]
    refine TypeOfHM.lambda (Ty.IsLC.substFvar h_U_lc hpc) ?_ rfl ?_
    · intro T hT
      rcases ann with _ | T₀
      · simp at hT
      · simp only [Option.map_some, Option.some.injEq] at hT
        subst hT
        rw [hann T₀ rfl]
    · simpa only [Env.substFvar, List.map_cons, PolyTy.substFvar, PolyTy.mkTrivial] using ihbody
  | var hlook htyargs hinst =>
    simp only [Expr.substTyFvar]
    have hlook' := congrArg (Option.map (PolyTy.substFvar Z U)) hlook
    simp only [Option.map_some] at hlook'
    rw [← List.getElem?_map] at hlook'
    refine TypeOfHM.var hlook' ?_ (InstantiatesBy.substFvar h_U_lc hinst)
    intro tyArg hmem
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hmem
    exact Ty.IsLC.substFvar h_U_lc (htyargs t ht)
  | ctor hlook htyargs hinst =>
    simp only [Expr.substTyFvar]
    have hbody := InstantiatesBy.substFvar (Z := Z) (U := U) h_U_lc hinst
    rw [Ty.substFvar_fresh (NoFreeVars.not_mem_freeVars (Ctor.toTy_body_noFreeVars _) Z)] at hbody
    refine TypeOfHM.ctor hlook ?_ hbody
    intro tyArg hmem
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hmem
    exact Ty.IsLC.substFvar h_U_lc (htyargs t ht)
  | letIn hwf hann hcofin heq hbody ihcofin ihbody =>
    subst heq
    expose_names
    simp only [Expr.substTyFvar]
    refine TypeOfHM.letIn (M := PolyTy.substFvar Z U M) (L := Z :: L)
      (PolyTy.WF.substFvar h_U_lc hwf) ?_ ?_ rfl ?_
    · intro σ hσ
      rcases ann with _ | σ₀
      · simp at hσ
      · simp only [Option.map_some, Option.some.injEq] at hσ
        subst hσ
        rw [hann σ₀ rfl]
    · intro Xs hfresh
      have hZ_notin : Z ∉ Xs := fun hc => hfresh.avoid Z hc List.mem_cons_self
      have hXs_freshL : FreshNames L M.paramCount Xs :=
        ⟨by simpa using hfresh.length, hfresh.nodup,
         fun x hx hc => hfresh.avoid x hx (List.mem_cons_of_mem _ hc)⟩
      have hbe := ihcofin Xs hXs_freshL
      rw [Expr.substTyFvar_openBoundTyVars h_U_lc hZ_notin] at hbe
      have hopen : (M.substFvar Z U).openVars Xs = Ty.substFvar Z U (M.openVars Xs) := by
        unfold PolyTy.openVars PolyTy.substFvar
        exact (Ty.substFvar_openVars h_U_lc hZ_notin).symm
      rw [hopen]
      exact hbe
    · simpa only [Env.substFvar, List.map_cons] using ihbody
  | match_ hscrut hne hfirst hbrs ihscrut ihbrs =>
    simp only [Expr.substTyFvar]
    have hscrut' := ihscrut
    simp only [Ty.substFvar, TyList.substFvar_eq_map] at hscrut'
    refine TypeOfHM.match_ hscrut' ?_ ?_ ?_
    · intro hcontra
      obtain ⟨⟨p, b⟩, rest, hb⟩ := List.exists_cons_of_ne_nil hne
      rw [hb] at hcontra
      simp [BranchList.substTyFvar] at hcontra
    · obtain ⟨c, n, body, rest, heq⟩ := hfirst
      exact ⟨c, n, body.substTyFvar Z U, BranchList.substTyFvar Z U rest, by rw [heq]; rfl⟩
    · intro branch' hmem'
      obtain ⟨pat, body, hmem, rfl⟩ := BranchList.mem_substTyFvar hmem'
      rcases ihbrs (pat, body) hmem with
        ⟨ct, c, n, instContents, hpat, hlook, htyName, hpc, hcontents, hinstC, _, hbodyIH⟩ |
        ⟨hpat, _, hbodyIH⟩
      · subst hpat
        have hcc : ct.contents.map (Ty.substFvar Z U) = ct.contents := by
          have hpt : ∀ c ∈ ct.contents, Ty.substFvar Z U c = id c := fun c hc =>
            Ty.substFvar_fresh ((ct.closed c hc).not_mem_freeVars Z)
          rw [List.map_congr_left hpt, List.map_id]
        have hinstC' := InstantiatesBy.forall2_substFvar (Z := Z) (U := U) h_U_lc hinstC
        rw [hcc] at hinstC'
        rw [Env.substFvar_append, Env.substFvar_map_mkTrivial] at hbodyIH
        exact TypeOfMatchBranch.mk hlook htyName (by simpa using hpc) hcontents hinstC' rfl rfl hbodyIH
      · subst hpat
        exact TypeOfMatchBranch.wildcard hbodyIH

theorem TypeOfHM.typ_subst_preservation
    {ctors : CtorEnv} {env_post env_outer : Env}
    {e : Expr} {τ : Ty} {Z : Nat} {U : Ty}
    (h_Z_fresh_outer : Z ∉ env_outer.freeVars)
    (h_U_lc : U.IsLC)
    (h : TypeOfHM ⟨env_post ++ env_outer, ctors⟩ e τ) :
    TypeOfHM ⟨env_post.substFvar Z U ++ env_outer, ctors⟩ (e.substTyFvar Z U) (Ty.substFvar Z U τ) := by
  -- A direct corollary of the uniform version: uniform substitution turns the
  -- whole env `env_post ++ env_outer` into `(env_post ++ env_outer).substFvar Z U`,
  -- and `env_outer` is unchanged since `Z` is fresh for it.
  have huniform := TypeOfHM.typ_subst_preservation_uniform (Z := Z) (U := U) h_U_lc h
  rwa [show (⟨env_post ++ env_outer, ctors⟩ : Ctx).env.substFvar Z U
        = env_post.substFvar Z U ++ env_outer from by
      show Env.substFvar Z U (env_post ++ env_outer) = _
      rw [Env.substFvar_append, Env.substFvar_fresh h_Z_fresh_outer]] at huniform

/- Values are preserved under `shiftFrom` (it only renumbers free term vars,
   leaving the value shape intact). Mutual with `IsCtorChain.shiftFrom`. -/
mutual
theorem SmallStep.IsValue.shiftFrom {e : Expr} (k n : Nat)
    (h : SmallStep.IsValue e) : SmallStep.IsValue (e.shiftFrom k n) := by
  cases h with
  | primLit p => exact .primLit p
  | lambda ann body => exact .lambda _ _
  | ctor name => exact .ctor name
  | ctorApp hf hv => exact .ctorApp (hf.shiftFrom k n) (hv.shiftFrom k n)
theorem SmallStep.IsCtorChain.shiftFrom {e : Expr} (k n : Nat)
    (h : SmallStep.IsCtorChain e) : SmallStep.IsCtorChain (e.shiftFrom k n) := by
  cases h with
  | ctor name => exact .ctor name
  | app hf hv => exact .app (hf.shiftFrom k n) (hv.shiftFrom k n)
end

/-- Weakening: insert `env_extra` in the middle of the environment (shifting the
    expression's term-var indices to match), with **no** env-freshness side
    condition. This goes through precisely because the cofinite `letIn`
    rule lets us grow the exclusion set `L` to dodge `env_extra`'s
    type vars on the fly inside the IH.

    Chargueraud's `typing_weaken`. -/
theorem TypeOfHM.weaken_env
    {ctors : CtorEnv} {env_pre env_extra env : Env} {e : Expr} {τ : Ty}
    (h : TypeOfHM ⟨env_pre ++ env, ctors⟩ e τ) :
    TypeOfHM ⟨env_pre ++ env_extra ++ env, ctors⟩
      (e.shiftFrom env_pre.length env_extra.length) τ := by
  -- Derivation induction (`rec_strong`): the `letIn` cofinite case needs an IH
  -- for the *opened* bound expression, which structural induction can't reach.
  -- Generalize over the env split point `env_pre'` (it grows under binders).
  suffices H : ∀ {ctx' : Ctx} {e' : Expr} {τ' : Ty}, TypeOfHM ctx' e' τ' →
      ∀ (env_pre' : Env), ctx'.env = env_pre' ++ env →
        TypeOfHM ⟨env_pre' ++ env_extra ++ env, ctx'.ctors⟩
          (e'.shiftFrom env_pre'.length env_extra.length) τ' by
    exact H h env_pre rfl
  intro ctx' e' τ' hd
  induction hd using TypeOfHM.rec_strong with
  | primLitUnit => intro env_pre' _; exact .primLitUnit
  | primLitInt => intro env_pre' _; exact .primLitInt
  | primLitNat => intro env_pre' _; exact .primLitNat
  -- | primLitBool => intro env_pre' _; exact .primLitBool
  | primLitStr => intro env_pre' _; exact .primLitStr
  | app hf hinput ihf ihinput =>
    intro env_pre' hctx
    simp only [Expr.shiftFrom]
    exact .app (ihf env_pre' hctx) (ihinput env_pre' hctx)
  | ctor hlook htyargs hinst =>
    intro env_pre' _
    exact .ctor hlook htyargs hinst
  | var hlook htyargs hinst =>
    intro env_pre' hctx
    expose_names
    rw [hctx] at hlook
    simp only [Expr.shiftFrom]
    by_cases h_lt : dbl < env_pre'.length
    · rw [if_pos h_lt]
      refine .var ?_ htyargs hinst
      show (env_pre' ++ env_extra ++ env)[dbl]? = _
      rw [List.getElem?_append_left
            (by simp only [List.length_append]; omega : dbl < (env_pre' ++ env_extra).length),
          List.getElem?_append_left h_lt]
      rwa [List.getElem?_append_left h_lt] at hlook
    · push_neg at h_lt
      rw [if_neg (Nat.not_lt.mpr h_lt)]
      refine .var ?_ htyargs hinst
      show (env_pre' ++ env_extra ++ env)[dbl + env_extra.length]? = _
      rw [List.getElem?_append_right
            (by simp only [List.length_append]; omega :
              (env_pre' ++ env_extra).length ≤ dbl + env_extra.length)]
      rw [show dbl + env_extra.length - (env_pre' ++ env_extra).length = dbl - env_pre'.length
            from by simp only [List.length_append]; omega]
      rwa [List.getElem?_append_right h_lt] at hlook
  | lambda hpc hann heq hbody ihbody =>
    intro env_pre' hctx
    subst heq
    simp only [Expr.shiftFrom]
    refine TypeOfHM.lambda hpc hann rfl ?_
    expose_names
    have hb := ihbody (PolyTy.mkTrivial paramTy :: env_pre') (by rw [hctx, List.cons_append])
    simpa only [List.cons_append, List.length_cons] using hb
  | letIn hwf hann hcofin heq hbody ihcofin ihbody =>
    intro env_pre' hctx
    subst heq
    expose_names
    simp only [Expr.shiftFrom]
    refine TypeOfHM.letIn (M := M) (L := L) hwf hann ?_ rfl ?_
    · intro Xs hfresh
      have hc := ihcofin Xs hfresh env_pre' hctx
      rwa [Expr.shiftFrom_openBoundTyVars] at hc
    · have hb := ihbody (M :: env_pre') (by rw [hctx, List.cons_append])
      simpa only [List.cons_append, List.length_cons] using hb
  | match_ hscrut hne hfirst hbrs ihscrut ihbrs =>
    intro env_pre' hctx
    simp only [Expr.shiftFrom]
    refine TypeOfHM.match_ (ihscrut env_pre' hctx) ?_ ?_ ?_
    · intro hcontra
      obtain ⟨⟨p, b⟩, rest, hb⟩ := List.exists_cons_of_ne_nil hne
      rw [hb] at hcontra
      simp [BranchList.shiftFrom] at hcontra
    · obtain ⟨c, n, body, rest, rfl⟩ := hfirst
      exact ⟨c, n, _, _, rfl⟩
    · intro branch' hmem'
      obtain ⟨pat, body, hmem, rfl⟩ := BranchList.mem_shiftFrom hmem'
      rcases ihbrs (pat, body) hmem with
        ⟨ct, c, n, instContents, hpat, hlook, htyName, hpc, hcontents, hinstC, _, hbodyIH⟩ |
        ⟨hpat, _, hbodyIH⟩
      · subst hpat
        simp only [MatchPattern.bindCount]
        have hib := hbodyIH (instContents.map PolyTy.mkTrivial ++ env_pre')
          (by rw [hctx, List.append_assoc])
        simp only [List.length_append, List.length_map] at hib
        rw [← hinstC.length_eq, ← hcontents,
            show n + env_pre'.length = env_pre'.length + n
              from Nat.add_comm _ _] at hib
        refine TypeOfMatchBranch.mk hlook htyName hpc hcontents hinstC rfl rfl ?_
        rw [show env_pre' ++ env_extra ++ env = env_pre' ++ (env_extra ++ env)
              from List.append_assoc _ _ _]
        rw [List.append_assoc, List.append_assoc] at hib
        exact hib
      · subst hpat
        simp only [MatchPattern.bindCount, Nat.add_zero]
        exact TypeOfMatchBranch.wildcard (hbodyIH env_pre' hctx)

/-- Iterated type substitution preserves typing: substituting each `(Zᵢ, Uᵢ)`
    in turn (with every `Zᵢ` fresh for the env and every `Uᵢ` locally closed)
    preserves the derivation. Chargueraud's `typing_typ_substs`. -/
theorem TypeOfHM.typ_substs_preservation {ctx : Ctx} {e : Expr}
    (pairs : List (Nat × Ty))
    (h_fresh : ∀ p ∈ pairs, p.1 ∉ ctx.env.freeVars)
    (h_lc : ∀ p ∈ pairs, Ty.IsLC p.2)
    {τ : Ty} (h : TypeOfHM ctx e τ) :
    TypeOfHM ctx (e.substTyFvars pairs) (Ty.substFvars pairs τ) := by
  induction pairs generalizing e τ with
  | nil => exact h
  | cons hd tl ih =>
    obtain ⟨Z, U⟩ := hd
    simp only [Expr.substTyFvars, Ty.substFvars]
    have hZ : Z ∉ ctx.env.freeVars := h_fresh (Z, U) List.mem_cons_self
    have hU : Ty.IsLC U := h_lc (Z, U) List.mem_cons_self
    have hstep := TypeOfHM.typ_subst_preservation (env_post := []) (env_outer := ctx.env)
      (ctors := ctx.ctors) hZ hU h
    simp only [Env.substFvar, List.map_nil, List.nil_append] at hstep
    exact ih (fun p hp => h_fresh p (List.mem_cons_of_mem _ hp))
             (fun p hp => h_lc p (List.mem_cons_of_mem _ hp)) hstep

/-- Every element of a list is `≤` its `max`-fold. -/
theorem List.le_foldr_max {a : Nat} {l : List Nat}
    (h : a ∈ l) : a ≤ l.foldr max 0 := by
  induction l with
  | nil => exact absurd h List.not_mem_nil
  | cons hd tl ih =>
    simp only [List.foldr_cons]
    cases h with
    | head => exact le_max_left _ _
    | tail _ h' => exact le_trans (ih h') (le_max_right _ _)

/-- For any finite `avoid` list and any `n`, there exist `n` distinct names
    avoiding `avoid`. (Take `n` consecutive numbers above `max avoid`.) -/
theorem exists_fresh_names (avoid : List Nat) (n : Nat) :
    ∃ Xs : List Nat, Xs.length = n ∧ Xs.Nodup ∧ ∀ x ∈ Xs, x ∉ avoid := by
  refine ⟨(List.range n).map (· + (avoid.foldr max 0 + 1)), ?_, ?_, ?_⟩
  · simp
  · apply List.Nodup.map (fun a b hab => by omega) List.nodup_range
  · intro x hx hmem
    simp only [List.mem_map, List.mem_range] at hx
    obtain ⟨i, _, rfl⟩ := hx
    have hle := List.le_foldr_max hmem
    omega

/-- The free type variables occurring in a term's *annotations* (lambda param
    annotations and `let` scheme annotations), collected recursively. A
    type-fvar substitution whose keys all avoid this set leaves the term fixed
    (`Expr.substTyFvars_eq_self_of_not_mem_tyFreeVars`). -/
def Expr.tyFreeVars : Expr → List Nat
  | .primLit _          => []
  | .lambda ann body    => (ann.elim [] Ty.freeVars) ++ body.tyFreeVars
  | .app f arg          => f.tyFreeVars ++ arg.tyFreeVars
  | .letIn ann rhs body => (ann.elim [] (fun σ => σ.body.freeVars)) ++ rhs.tyFreeVars ++ body.tyFreeVars
  | .var _              => []
  | .ctor _             => []
  | .match_ scrut branches => scrut.tyFreeVars ++ BranchList.tyFreeVars branches
where BranchList.tyFreeVars : List (MatchPattern × Expr) → List Nat
  | []                  => []
  | (_, body) :: rest   => body.tyFreeVars ++ Expr.tyFreeVars.BranchList.tyFreeVars rest

/-- Substituting a fresh type variable (one not occurring in the term's
    annotations) is a no-op. -/
theorem Expr.substTyFvar_eq_self_of_not_mem_tyFreeVars {Z : Nat} {U : Ty} {e : Expr}
    (h : Z ∉ e.tyFreeVars) : e.substTyFvar Z U = e := by
  induction e using Expr.rec_strong with
  | primLit p => rfl
  | app f arg ihf iha =>
    simp only [Expr.tyFreeVars, List.mem_append, not_or] at h
    simp only [Expr.substTyFvar, ihf h.1, iha h.2]
  | var n => rfl
  | ctor nm => rfl
  | lambda ann body ih =>
    simp only [Expr.tyFreeVars, List.mem_append, not_or] at h
    simp only [Expr.substTyFvar, ih h.2]
    congr 1
    cases ann with
    | none => rfl
    | some T => simp only [Option.map_some, Option.some.injEq]; exact Ty.substFvar_fresh h.1
  | letIn ann rhs body ihr ihb =>
    simp only [Expr.tyFreeVars, List.mem_append, not_or] at h
    obtain ⟨⟨hann, hrhs⟩, hbody⟩ := h
    simp only [Expr.substTyFvar, ihr hrhs, ihb hbody]
    congr 1
    cases ann with
    | none => rfl
    | some σ =>
      simp only [Option.map_some, Option.some.injEq]
      show PolyTy.substFvar Z U σ = σ
      unfold PolyTy.substFvar
      rw [Ty.substFvar_fresh hann]
  | match_ scrut branches ihscrut ihbranches =>
    simp only [Expr.tyFreeVars, List.mem_append, not_or] at h
    obtain ⟨hscrut, hbranches⟩ := h
    simp only [Expr.substTyFvar, ihscrut hscrut]
    congr 1
    clear ihscrut hscrut
    induction branches with
    | nil => rfl
    | cons hd tl ihtl =>
      obtain ⟨pat, body⟩ := hd
      simp only [Expr.tyFreeVars.BranchList.tyFreeVars, List.mem_append, not_or] at hbranches
      simp only [BranchList.substTyFvar, List.cons.injEq, Prod.mk.injEq, true_and]
      refine ⟨ihbranches pat body List.mem_cons_self hbranches.1, ?_⟩
      exact ihtl (fun p e hp => ihbranches p e (List.mem_cons_of_mem _ hp)) hbranches.2

/-- Iterated version: a list of type-fvar substitutions whose keys all avoid the
    term's annotation free variables leaves the term fixed. -/
theorem Expr.substTyFvars_eq_self_of_not_mem_tyFreeVars {pairs : List (Nat × Ty)} :
    ∀ {e : Expr}, (∀ p ∈ pairs, p.1 ∉ e.tyFreeVars) → e.substTyFvars pairs = e := by
  induction pairs with
  | nil => intro e _; rfl
  | cons hd tl ih =>
    intro e h
    obtain ⟨Z, U⟩ := hd
    have hZ : Z ∉ e.tyFreeVars := h (Z, U) List.mem_cons_self
    simp only [Expr.substTyFvars]
    rw [Expr.substTyFvar_eq_self_of_not_mem_tyFreeVars hZ]
    exact ih (fun p hp => h p (List.mem_cons_of_mem _ hp))

/-! ### `substTyFvars` structural distribution (toward the term-level rename lemma).

`Expr.substTyFvars` (a left-to-right fold of `Expr.substTyFvar`) pushes through
every term constructor; the annotation cases map the corresponding `Ty`/`PolyTy`
substitution over the stored annotation. These mirror the `Ty.substFvars_*`
distribution lemmas. -/

private theorem BranchList.substTyFvar_eq_map {Z : Nat} {U : Ty}
    {brs : List (MatchPattern × Expr)} :
    BranchList.substTyFvar Z U brs = brs.map (fun pb => (pb.1, pb.2.substTyFvar Z U)) := by
  induction brs with
  | nil => rfl
  | cons hd tl ih => obtain ⟨p, b⟩ := hd; simp only [BranchList.substTyFvar, List.map_cons, ih]

private theorem BranchList.openTyVarsAux_eq_map {d : Nat} {Xs : List Nat}
    {brs : List (MatchPattern × Expr)} :
    BranchList.openTyVarsAux d Xs brs = brs.map (fun pb => (pb.1, pb.2.openTyVarsAux d Xs)) := by
  induction brs with
  | nil => rfl
  | cons hd tl ih => obtain ⟨p, b⟩ := hd; simp only [BranchList.openTyVarsAux, List.map_cons, ih]

theorem Expr.substTyFvars_app {σ : List (Nat × Ty)} {f arg : Expr} :
    Expr.substTyFvars σ (.app f arg) = .app (f.substTyFvars σ) (arg.substTyFvars σ) := by
  induction σ generalizing f arg with
  | nil => rfl
  | cons hd tl ih => obtain ⟨Z, U⟩ := hd; simp only [Expr.substTyFvars, Expr.substTyFvar, ih]

theorem Expr.substTyFvars_lambda {σ : List (Nat × Ty)} {ann : Option Ty} {body : Expr} :
    Expr.substTyFvars σ (.lambda ann body)
      = .lambda (ann.map (Ty.substFvars σ)) (body.substTyFvars σ) := by
  induction σ generalizing ann body with
  | nil => cases ann <;> rfl
  | cons hd tl ih =>
    obtain ⟨Z, U⟩ := hd
    simp only [Expr.substTyFvars, Expr.substTyFvar]
    rw [ih]
    cases ann with
    | none => rfl
    | some t => simp only [Option.map_some, Ty.substFvars]

theorem Expr.substTyFvars_letIn {σ : List (Nat × Ty)} {ann : Option PolyTy} {rhs body : Expr} :
    Expr.substTyFvars σ (.letIn ann rhs body)
      = .letIn (ann.map (fun M => ⟨M.paramCount, Ty.substFvars σ M.body⟩))
          (rhs.substTyFvars σ) (body.substTyFvars σ) := by
  induction σ generalizing ann rhs body with
  | nil => cases ann <;> rfl
  | cons hd tl ih =>
    obtain ⟨Z, U⟩ := hd
    simp only [Expr.substTyFvars, Expr.substTyFvar]
    rw [ih]
    cases ann with
    | none => rfl
    | some M => simp only [Option.map_some, PolyTy.substFvar, Ty.substFvars]

theorem Expr.substTyFvars_match {σ : List (Nat × Ty)} {scrut : Expr}
    {branches : List (MatchPattern × Expr)} :
    Expr.substTyFvars σ (.match_ scrut branches)
      = .match_ (scrut.substTyFvars σ) (branches.map (fun pb => (pb.1, pb.2.substTyFvars σ))) := by
  induction σ generalizing scrut branches with
  | nil =>
    simp only [Expr.substTyFvars]
    congr 1
    conv_lhs => rw [← List.map_id branches]
    apply List.map_congr_left
    rintro ⟨p, b⟩ _; rfl
  | cons hd tl ih =>
    obtain ⟨Z, U⟩ := hd
    simp only [Expr.substTyFvars, Expr.substTyFvar, BranchList.substTyFvar_eq_map, ih,
      List.map_map, Function.comp_def]

/-- A branch body's annotation free vars are among the branch list's. -/
private theorem Expr.mem_branchList_tyFreeVars {p : MatchPattern} {b : Expr} {y : Nat}
    {brs : List (MatchPattern × Expr)} (hmem : (p, b) ∈ brs) (hy : y ∈ b.tyFreeVars) :
    y ∈ Expr.tyFreeVars.BranchList.tyFreeVars brs := by
  induction brs with
  | nil => exact absurd hmem List.not_mem_nil
  | cons hd tl ih =>
    obtain ⟨p', b'⟩ := hd
    simp only [Expr.tyFreeVars.BranchList.tyFreeVars, List.mem_append]
    rcases List.mem_cons.mp hmem with h | h
    · rw [Prod.mk.injEq] at h; obtain ⟨_, rfl⟩ := h; exact .inl hy
    · exact .inr (ih h)

/-- **Rename the opening (term level, depth-general).** Opening a term `e`'s
    scoped type variables (offset `d`) at a fresh block `Ys`, then renaming
    `Ys ↦ Xs` (as `fvar`s through the annotations), equals opening directly at
    `Xs`. The annotation cases use `Ty.substFvars_zip_openVarsFrom`. Freshness
    side conditions (`Ys` nodup, disjoint from `e`'s pre-existing annotation free
    vars and from `Xs`) ensure the rename only touches names introduced by the
    opening. -/
theorem Expr.substTyFvars_zip_openTyVarsAux {Ys Xs : List Nat}
    (h_len : Ys.length = Xs.length) (h_Ys_nodup : Ys.Nodup) (h_Ys_Xs : ∀ y ∈ Ys, y ∉ Xs) :
    ∀ (e : Expr) (d : Nat), (∀ y ∈ Ys, y ∉ e.tyFreeVars) →
      (e.openTyVarsAux d Ys).substTyFvars (Ys.zip (Xs.map (Ty.fvar ·)))
        = e.openTyVarsAux d Xs := by
  intro e
  induction e using Expr.rec_strong with
  | primLit p =>
    intro d _; simp only [Expr.openTyVarsAux]
    exact Expr.substTyFvars_eq_self_of_not_mem_tyFreeVars (by simp [Expr.tyFreeVars])
  | var n =>
    intro d _; simp only [Expr.openTyVarsAux]
    exact Expr.substTyFvars_eq_self_of_not_mem_tyFreeVars (by simp [Expr.tyFreeVars])
  | ctor nm =>
    intro d _; simp only [Expr.openTyVarsAux]
    exact Expr.substTyFvars_eq_self_of_not_mem_tyFreeVars (by simp [Expr.tyFreeVars])
  | app f arg ihf iharg =>
    intro d hfresh
    simp only [Expr.openTyVarsAux, Expr.substTyFvars_app]
    rw [ihf d (fun y hy hc => hfresh y hy (by simp only [Expr.tyFreeVars, List.mem_append]; tauto)),
        iharg d (fun y hy hc => hfresh y hy (by simp only [Expr.tyFreeVars, List.mem_append]; tauto))]
  | lambda ann body ih =>
    intro d hfresh
    simp only [Expr.openTyVarsAux, Expr.substTyFvars_lambda]
    rw [ih d (fun y hy hc => hfresh y hy (by simp only [Expr.tyFreeVars, List.mem_append]; tauto))]
    cases ann with
    | none => rfl
    | some t =>
      simp only [Option.map_some]
      rw [Ty.substFvars_zip_openVarsFrom h_len h_Ys_nodup
        (fun y hy hc => hfresh y hy (by simp only [Expr.tyFreeVars, Option.elim, List.mem_append]; tauto))
        h_Ys_Xs]
  | letIn ann rhs body ihrhs ihbody =>
    intro d hfresh
    cases ann with
    | none =>
      simp only [Expr.openTyVarsAux, Expr.substTyFvars_letIn, Option.map_none]
      rw [ihrhs d (fun y hy hc => hfresh y hy (by simp only [Expr.tyFreeVars, Option.elim, List.mem_append]; tauto)),
          ihbody d (fun y hy hc => hfresh y hy (by simp only [Expr.tyFreeVars, Option.elim, List.mem_append]; tauto))]
    | some σ =>
      simp only [Expr.openTyVarsAux, Expr.substTyFvars_letIn]
      rw [ihrhs (d + σ.paramCount) (fun y hy hc => hfresh y hy (by simp only [Expr.tyFreeVars, Option.elim, List.mem_append]; tauto)),
          ihbody d (fun y hy hc => hfresh y hy (by simp only [Expr.tyFreeVars, Option.elim, List.mem_append]; tauto))]
      simp only [Option.map_some]
      rw [Ty.substFvars_zip_openVarsFrom h_len h_Ys_nodup
        (fun y hy hc => hfresh y hy (by simp only [Expr.tyFreeVars, Option.elim, List.mem_append]; tauto))
        h_Ys_Xs]
  | match_ scrut branches ihscrut ihbranches =>
    intro d hfresh
    simp only [Expr.openTyVarsAux, BranchList.openTyVarsAux_eq_map, Expr.substTyFvars_match]
    rw [ihscrut d (fun y hy hc => hfresh y hy (by simp only [Expr.tyFreeVars, List.mem_append]; tauto))]
    congr 1
    rw [List.map_map]
    apply List.map_congr_left
    rintro ⟨p, b⟩ hpb
    simp only [Function.comp_def]
    rw [ihbranches p b hpb d (fun y hy hc => hfresh y hy (by
      simp only [Expr.tyFreeVars, List.mem_append]
      exact .inr (Expr.mem_branchList_tyFreeVars hpb hc)))]

/-- Top-level form of `Expr.substTyFvars_zip_openTyVarsAux`
    (`Expr.openTyVars = Expr.openTyVarsAux 0`). The key bridge for soundness of
    scoped type variables: the algorithm checks the bound expression opened at one
    skolem block `Ys`; this lets the declarative cofinite premise be recovered by
    renaming `Ys` to any fresh `Xs`. -/
theorem Expr.substTyFvars_zip_openTyVars {Ys Xs : List Nat} {e : Expr}
    (h_len : Ys.length = Xs.length) (h_Ys_nodup : Ys.Nodup)
    (h_Ys_e : ∀ y ∈ Ys, y ∉ e.tyFreeVars) (h_Ys_Xs : ∀ y ∈ Ys, y ∉ Xs) :
    (e.openTyVars Ys).substTyFvars (Ys.zip (Xs.map (Ty.fvar ·))) = e.openTyVars Xs := by
  unfold Expr.openTyVars
  exact Expr.substTyFvars_zip_openTyVarsAux h_len h_Ys_nodup h_Ys_Xs e 0 h_Ys_e

/-! ### Annotation-free structural size (a well-founded measure for derivation
    recursion). The D2 algorithm infers the bound expression *opened* at skolems
    (`rhs.openTyVars Ys`), which is not a structural subterm of the `let`, so the
    default term measure no longer decreases for the `Infer`-recursive metatheory.
    `Expr.size` ignores type annotations, so `openTyVars` preserves it
    (`Expr.size_openTyVars`), giving a measure that *does* decrease. -/
mutual
def Expr.size : Expr → Nat
  | .primLit _          => 1
  | .lambda _ body      => 1 + body.size
  | .app f arg          => 1 + f.size + arg.size
  | .letIn _ rhs body   => 1 + rhs.size + body.size
  | .var _              => 1
  | .ctor _             => 1
  | .match_ scrut branches => 1 + scrut.size + Expr.sizeBranches branches
def Expr.sizeBranches : List (MatchPattern × Expr) → Nat
  | []                  => 0
  | (_, b) :: rest      => 1 + b.size + Expr.sizeBranches rest
end

/-- `Expr.size` is invariant under opening scoped type variables (it ignores the
    annotations that `openTyVars` rewrites). The match-case branch reasoning lives
    here in `Core` where `BranchList.openTyVarsAux` is in scope. -/
theorem Expr.size_openTyVarsAux {Xs : List Nat} :
    ∀ (e : Expr) (d : Nat), (e.openTyVarsAux d Xs).size = e.size := by
  intro e
  induction e using Expr.rec_strong with
  | primLit p => intro d; rfl
  | app f inp ihf ihi => intro d; simp only [Expr.openTyVarsAux, Expr.size, ihf, ihi]
  | lambda ann body ih => intro d; simp only [Expr.openTyVarsAux, Expr.size, ih]
  | letIn ann be body ihbe ihbody =>
    intro d
    cases ann with
    | none => simp only [Expr.openTyVarsAux, Expr.size, ihbe, ihbody]
    | some σ => simp only [Expr.openTyVarsAux, Expr.size, ihbe, ihbody]
  | var n => intro d; rfl
  | ctor nm => intro d; rfl
  | match_ scrut branches ihs ihbs =>
    intro d
    simp only [Expr.openTyVarsAux, Expr.size]
    rw [ihs d]
    congr 1
    revert ihbs
    induction branches with
    | nil => intro _; rfl
    | cons hd tl ihtl =>
      intro ihbs
      obtain ⟨pat, body⟩ := hd
      simp only [BranchList.openTyVarsAux, Expr.sizeBranches]
      rw [ihbs pat body List.mem_cons_self d,
          ihtl (fun p e hm => ihbs p e (List.mem_cons_of_mem _ hm))]

theorem Expr.size_openTyVars {Xs : List Nat} {e : Expr} :
    (e.openTyVars Xs).size = e.size := Expr.size_openTyVarsAux e 0

/-! ### Free-variable containment under opening

Opening a term's scoped type variables (`Expr.openTyVars Xs`) can only introduce
the fresh opening names `Xs` into the term's annotation free vars — every other
free var was already there. The `letInAnn` soundness case uses this to bound the
*opened* bound expression's annotation fvars by `K ∪ Ys` (the ambient skolem set
extended with the freshly-allocated skolems). Type-level first, then lifted
through terms (the match-branch reasoning lives here in `Core`, where the private
`BranchList.openTyVarsAux` is in scope, exactly as for `Expr.size_openTyVars`). -/

@[simp] theorem Ty.openVarsFrom_arrow {d : Nat} {Xs : List Nat} {a b : Ty} :
    Ty.openVarsFrom d Xs (.arrow a b)
      = .arrow (Ty.openVarsFrom d Xs a) (Ty.openVarsFrom d Xs b) := rfl
@[simp] theorem Ty.openVarsFrom_customTy {d : Nat} {Xs : List Nat} {nm : TyName} {tys : List Ty} :
    Ty.openVarsFrom d Xs (.customTy nm tys)
      = .customTy nm (tys.map (Ty.openVarsFrom d Xs)) := by
  unfold Ty.openVarsFrom
  simp only [Ty.instantiate, TyList.instantiate_eq_map]

/-- The free vars of an offset opening are among the original free vars or the
    opening names (depth-general form; `Ty.freeVars_openVars_subset` is `d = 0`). -/
theorem Ty.freeVars_openVarsFrom_subset {d : Nat} {Xs : List Nat} {t : Ty} :
    ∀ z ∈ (Ty.openVarsFrom d Xs t).freeVars, z ∈ t.freeVars ∨ z ∈ Xs := by
  induction t using Ty.rec_strong with
  | prim p => intro z hz; simp [Ty.openVarsFrom, Ty.instantiate, Ty.freeVars] at hz
  | fvar n => intro z hz; left; simpa only [Ty.openVarsFrom, Ty.instantiate, Ty.freeVars] using hz
  | bvar i =>
    intro z hz
    simp only [Ty.openVarsFrom, Ty.instantiate] at hz
    by_cases hi : i < d
    · rw [if_pos hi] at hz; simp [Ty.freeVars] at hz
    · rw [if_neg hi] at hz
      cases hh : Xs[i - d]? with
      | none => rw [hh] at hz; simp [Ty.freeVars] at hz
      | some x =>
        rw [hh] at hz
        simp only [Option.elim_some, Ty.freeVars, List.mem_singleton] at hz
        subst hz; exact .inr (List.mem_of_getElem? hh)
  | arrow a b iha ihb =>
    intro z hz
    rw [Ty.openVarsFrom_arrow] at hz
    simp only [Ty.freeVars, List.mem_dedup, List.mem_append] at hz ⊢
    rcases hz with hz | hz
    · rcases iha z hz with h | h
      · exact .inl (.inl h)
      · exact .inr h
    · rcases ihb z hz with h | h
      · exact .inl (.inr h)
      · exact .inr h
  | customTy nm tys ih =>
    intro z hz
    rw [Ty.openVarsFrom_customTy, Ty.freeVars] at hz
    have hex : ∃ t' ∈ tys.map (Ty.openVarsFrom d Xs), z ∈ t'.freeVars := by
      by_contra hcon
      push_neg at hcon
      exact (TyList.not_mem_freeVars_iff.mpr hcon) hz
    obtain ⟨t', ht', hzt'⟩ := hex
    obtain ⟨t0, ht0, rfl⟩ := List.mem_map.mp ht'
    rcases ih t0 ht0 z hzt' with h | h
    · exact .inl (by rw [Ty.freeVars]; exact TyList.mem_freeVars_of_mem ht0 h)
    · exact .inr h

/-- Term-level free-variable containment under offset opening: every annotation
    free var of `e.openTyVarsAux d Xs` was already an annotation free var of `e`,
    or is one of the opening names `Xs`. -/
theorem Expr.tyFreeVars_openTyVarsAux {Xs : List Nat} :
    ∀ (e : Expr) (d : Nat) (z : Nat),
      z ∈ (e.openTyVarsAux d Xs).tyFreeVars → z ∈ e.tyFreeVars ∨ z ∈ Xs := by
  intro e
  induction e using Expr.rec_strong with
  | primLit p => intro d z hz; simp [Expr.openTyVarsAux, Expr.tyFreeVars] at hz
  | var n => intro d z hz; simp [Expr.openTyVarsAux, Expr.tyFreeVars] at hz
  | ctor nm => intro d z hz; simp [Expr.openTyVarsAux, Expr.tyFreeVars] at hz
  | app f arg ihf iha =>
    intro d z hz
    simp only [Expr.openTyVarsAux, Expr.tyFreeVars, List.mem_append] at hz ⊢
    rcases hz with hz | hz
    · rcases ihf d z hz with h | h
      · exact .inl (.inl h)
      · exact .inr h
    · rcases iha d z hz with h | h
      · exact .inl (.inr h)
      · exact .inr h
  | lambda ann body ih =>
    intro d z hz
    cases ann with
    | none =>
      -- `lambda none` opens/erases-annotations to `body` definitionally.
      exact ih d z hz
    | some T =>
      simp only [Expr.openTyVarsAux, Expr.tyFreeVars, Option.map_some, Option.elim_some,
        List.mem_append] at hz ⊢
      rcases hz with hz | hz
      · rcases Ty.freeVars_openVarsFrom_subset z hz with h | h
        · exact .inl (.inl h)
        · exact .inr h
      · rcases ih d z hz with h | h
        · exact .inl (.inr h)
        · exact .inr h
  | letIn ann rhs body ihr ihb =>
    intro d z hz
    cases ann with
    | none =>
      simp only [Expr.openTyVarsAux, Expr.tyFreeVars, Option.elim_none, List.nil_append,
        List.mem_append] at hz ⊢
      rcases hz with hz | hz
      · rcases ihr d z hz with h | h
        · exact .inl (.inl h)
        · exact .inr h
      · rcases ihb d z hz with h | h
        · exact .inl (.inr h)
        · exact .inr h
    | some σ =>
      simp only [Expr.openTyVarsAux, Expr.tyFreeVars, Option.elim_some, List.mem_append] at hz ⊢
      rcases hz with (hz | hz) | hz
      · rcases Ty.freeVars_openVarsFrom_subset z hz with h | h
        · exact .inl (.inl (.inl h))
        · exact .inr h
      · rcases ihr (d + σ.paramCount) z hz with h | h
        · exact .inl (.inl (.inr h))
        · exact .inr h
      · rcases ihb d z hz with h | h
        · exact .inl (.inr h)
        · exact .inr h
  | match_ scrut branches ihs ihbs =>
    intro d z hz
    simp only [Expr.openTyVarsAux, Expr.tyFreeVars, List.mem_append] at hz ⊢
    rcases hz with hz | hz
    · rcases ihs d z hz with h | h
      · exact .inl (.inl h)
      · exact .inr h
    · have hbr : z ∈ Expr.tyFreeVars.BranchList.tyFreeVars branches ∨ z ∈ Xs := by
        revert hz
        revert ihbs
        induction branches with
        | nil =>
          intro _ hz
          simp [BranchList.openTyVarsAux, Expr.tyFreeVars.BranchList.tyFreeVars] at hz
        | cons hd tl ihtl =>
          intro ihbs hz
          obtain ⟨pat, body⟩ := hd
          simp only [BranchList.openTyVarsAux, Expr.tyFreeVars.BranchList.tyFreeVars,
            List.mem_append] at hz ⊢
          rcases hz with hz | hz
          · rcases ihbs pat body List.mem_cons_self d z hz with h | h
            · exact .inl (.inl h)
            · exact .inr h
          · rcases ihtl (fun p e hm => ihbs p e (List.mem_cons_of_mem _ hm)) hz with h | h
            · exact .inl (.inr h)
            · exact .inr h
      rcases hbr with h | h
      · exact .inl (.inr h)
      · exact .inr h

/-- Top-level free-variable containment under opening (`d = 0`). The bridge the
    `letInAnn` soundness case needs: the opened bound expression's annotation
    fvars are among `rhs`'s original ones or the skolems `Xs`. -/
theorem Expr.tyFreeVars_openTyVars {Xs : List Nat} {e : Expr} {z : Nat}
    (hz : z ∈ (e.openTyVars Xs).tyFreeVars) : z ∈ e.tyFreeVars ∨ z ∈ Xs :=
  Expr.tyFreeVars_openTyVarsAux e 0 z hz

/-- The bridge: a cofinite-vars witness gives a "for-all-instances" witness.
    Chargueraud's `has_scheme_from_vars`. For any `Vs`, pick `Xs` fresh for
    everything relevant, use the cofinite witness at `Xs`, then iteratively
    `typ_subst_preservation`-substitute each `Xᵢ ↦ Vᵢ` (the
    `openWith = substFvars ∘ openVars` identity bridges the two openings). The
    `Xs` are also chosen fresh for `e`'s own annotation free vars, so the
    `substTyFvars` ripple introduced by `typ_substs_preservation` collapses back
    to `e`. -/
theorem HasScheme.fromHasSchemeVars
    {L : List Nat} {ctx : Ctx} {e : Expr} {M : PolyTy}
    (h : HasSchemeVars L ctx e M) :
    HasScheme ctx e M := by
  intro Vs hVs
  obtain ⟨hVlen, hVlc⟩ := hVs
  obtain ⟨Xs, hXlen, hXnodup, hXavoid⟩ :=
    exists_fresh_names
      (L ++ M.body.freeVars ++ Ty.freeVarsList Vs ++ ctx.env.freeVars ++ e.tyFreeVars) M.paramCount
  -- split the combined freshness into its parts
  have hX_L : ∀ x ∈ Xs, x ∉ L := fun x hx hc =>
    hXavoid x hx (by simp only [List.mem_append]; tauto)
  have hX_Mbody : ∀ x ∈ Xs, x ∉ M.body.freeVars := fun x hx hc =>
    hXavoid x hx (by simp only [List.mem_append]; tauto)
  have hX_Vs : ∀ x ∈ Xs, x ∉ Ty.freeVarsList Vs := fun x hx hc =>
    hXavoid x hx (by simp only [List.mem_append]; tauto)
  have hX_env : ∀ x ∈ Xs, x ∉ ctx.env.freeVars := fun x hx hc =>
    hXavoid x hx (by simp only [List.mem_append]; tauto)
  have hX_e : ∀ x ∈ Xs, x ∉ e.tyFreeVars := fun x hx hc =>
    hXavoid x hx (by simp only [List.mem_append]; tauto)
  have hVlen' : Vs.length = Xs.length := by rw [hVlen, hXlen]
  -- the cofinite witness, instantiated at our fresh Xs
  have hwit := h Xs ⟨hXlen, hXnodup, hX_L⟩
  -- bridge openWith to substFvars ∘ openVars
  have hrewrite : M.openWith Vs = Ty.substFvars (Xs.zip Vs) (M.openVars Xs) := by
    unfold PolyTy.openWith PolyTy.openVars
    exact Ty.openWith_eq_substFvars_openVars ⟨hVlen', hVlc⟩ hXnodup hX_Mbody hX_Vs
  show TypeOfHM ctx e (M.openWith Vs)
  rw [hrewrite]
  have hsub := TypeOfHM.typ_substs_preservation (Xs.zip Vs)
    (fun p hp => hX_env p.1 (List.of_mem_zip hp).1)
    (fun p hp => hVlc p.2 (List.of_mem_zip hp).2) hwit
  rwa [Expr.substTyFvars_eq_self_of_not_mem_tyFreeVars
        (fun p hp => hX_e p.1 (List.of_mem_zip hp).1)] at hsub

/-- Instantiation with the "identity on bvars" substitution is a no-op. Used
    in `HasScheme.ofTypeOfHM` to show that opening an arity-0 scheme with the
    empty arg list returns the underlying type unchanged. -/
private theorem Ty.instantiate_bvar_id {ty : Ty} :
    Ty.instantiate (fun i => .bvar i) ty = ty := by
  induction ty using Ty.rec_strong with
  | prim _ => rfl
  | arrow _ _ ih_a ih_b =>
    simp only [Ty.instantiate, Ty.arrow.injEq]; exact ⟨ih_a, ih_b⟩
  | bvar _ => rfl
  | fvar _ => rfl
  | customTy _ tys ih =>
    simp only [Ty.instantiate, Ty.customTy.injEq, true_and]
    induction tys with
    | nil => rfl
    | cons hd tl ih_tl =>
      simp only [TyList.instantiate, List.cons.injEq]
      refine ⟨ih hd List.mem_cons_self, ?_⟩
      exact ih_tl (fun t ht => ih t (List.mem_cons_of_mem _ ht))

/-- Opening with the empty list of types is identity: nothing to instantiate. -/
theorem Ty.openWith_nil {ty : Ty} : Ty.openWith [] ty = ty := by
  unfold Ty.openWith
  have heq : (fun i => ([] : List Ty)[i]?.getD (.bvar i)) = (fun i => Ty.bvar i) := by
    funext i; simp
  rw [heq]
  exact Ty.instantiate_bvar_id

/-- Monomorphic `has_scheme`: a regular typing is a `HasScheme` for the
    trivial 0-binder scheme. Chargueraud's `has_scheme_from_typ`. -/
theorem HasScheme.ofTypeOfHM
    {ctx : Ctx} {e : Expr} {τ : Ty}
    (h : TypeOfHM ctx e τ) :
    HasScheme ctx e (PolyTy.mkTrivial τ) := by
  intro Vs h_lc
  obtain ⟨h_len, _⟩ := h_lc
  -- PolyTy.mkTrivial τ has paramCount = 0, so Vs = []
  have h_vs_nil : Vs = [] := List.length_eq_zero_iff.mp h_len
  subst h_vs_nil
  show TypeOfHM ctx e (PolyTy.openWith [] (PolyTy.mkTrivial τ))
  unfold PolyTy.openWith PolyTy.mkTrivial
  rw [Ty.openWith_nil]
  exact h


/- Values are preserved under multi-substitution (`substN` only rewrites free
   term vars / descends under binders; value shape is untouched). Mutual with
   `IsCtorChain.substN`. -/
mutual
theorem SmallStep.IsValue.substN {e : Expr} (k : Nat) (vs : List Expr)
    (h : SmallStep.IsValue e) : SmallStep.IsValue (e.substN k vs) := by
  cases h with
  | primLit p => exact .primLit p
  | lambda ann body => exact .lambda _ _
  | ctor name => exact .ctor name
  | ctorApp hf hv => exact .ctorApp (hf.substN k vs) (hv.substN k vs)
theorem SmallStep.IsCtorChain.substN {e : Expr} (k : Nat) (vs : List Expr)
    (h : SmallStep.IsCtorChain e) : SmallStep.IsCtorChain (e.substN k vs) := by
  cases h with
  | ctor name => exact .ctor name
  | app hf hv => exact .app (hf.substN k vs) (hv.substN k vs)
end

/-- If `ty`'s bvars are all `< n` and `ty` instantiates to `τ` under `tyArgs`,
    then `τ` is the result of opening `ty` with the length-`n` prefix of
    `tyArgs` (padding unused slots, which `ty` can't reference, with `unit`).
    This bridges the var rule's `InstantiatesBy` to the scheme's `openWith`. -/
theorem InstantiatesBy.eq_openWith_range {tyArgs : List Ty} {n : Nat} {ty τ : Ty}
    (h : InstantiatesBy tyArgs ty τ) (h_bv : ContainsBvarsUpTo n ty) :
    τ = Ty.openWith ((List.range n).map (fun i => (tyArgs[i]?).getD (.prim .unit))) ty := by
  induction ty using Ty.rec_strong generalizing τ with
  | prim p => cases h; rfl
  | arrow a b iha ihb =>
    cases h_bv with
    | arrow hba hbb =>
      cases h with
      | arrow ha hb =>
        simp only [Ty.openWith, Ty.instantiate] at *
        rw [iha ha hba, ihb hb hbb]
  | bvar i =>
    cases h_bv with
    | bvar h_lt =>
      cases h with
      | bvar hsome =>
        simp only [Ty.openWith, Ty.instantiate, List.getElem?_map, List.getElem?_range,
          h_lt, Option.map_some, Option.getD_some, hsome]
  | fvar m => cases h; rfl
  | customTy nm tys ih =>
    cases h_bv with
    | customTy hball =>
      cases h with
      | customTy hforall =>
        simp only [Ty.openWith, Ty.instantiate]
        congr 1
        rw [TyList.instantiate_eq_map]
        induction hforall with
        | nil => rfl
        | cons hhd htl ihtl =>
          rename_i hd_ty hd_inst tl_tys tl_inst
          have h_hd := ih hd_ty List.mem_cons_self hhd (hball hd_ty List.mem_cons_self)
          have h_tl := ihtl
            (fun t ht => ih t (List.mem_cons_of_mem _ ht))
            (fun t ht => hball t (List.mem_cons_of_mem _ ht))
          simp only [List.map_cons]
          simp only [Ty.openWith] at h_hd
          rw [← h_hd, h_tl]


section PreservationProbe
/- PERMANENT RECORD — justification for type-erasing the dynamic semantics.

   This section proves (`preservation_is_unsound`) that the *literal* subject
   reduction `Step e e' → e : τ → e' : τ` is FALSE once annotations may carry
   scoped type variables. Concretely, the `letReduce` of an *annotated* `let`
   whose annotation introduces a scoped type variable: the let-bound value
   `λ(x : a). x` (with `a` a scoped type variable = `bvar 0`) is well-typed only
   *after opening* (via the cofinite premise), but `letReduce` substitutes the
   *unopened* value into the body, producing an untypeable term.

   This is exactly why the dynamic-soundness layer is re-based onto
   annotation-erased terms (`Expr.eraseTyAnnots`, `TypeOfHM.erased_type_safety`):
   annotations are runtime-irrelevant, so we "check with annotations, run
   erased". The static system (`TypeOfHM`, scoped type variables) is unchanged. -/

/-- `σ = ∀ a. a → a`. -/
private def probeSig : PolyTy := ⟨1, .arrow (.bvar 0) (.bvar 0)⟩
/-- The let-bound value `λ(x : a). x`, where `a` is the scoped type variable
    `bvar 0` (referencing `σ`'s binder). -/
private def probeV : Expr := .lambda (some (.bvar 0)) (.var 0)
/-- `let f : σ = (λ(x:a). x) in f`. -/
private def probeLHS : Expr := .letIn (some probeSig) probeV (.var 0)

/-- The reduct `λ(x : a). x` (with a dangling scoped type-`bvar` in its
    annotation) is untypeable at any type: the `lambda` rule pins `paramTy` to
    the annotation `bvar 0` yet also demands `ContainsBvarsUpTo 0 paramTy`. -/
private theorem probe_reduct_untypeable (ctx : Ctx) (τ : Ty) :
    ¬ TypeOfHM ctx probeV τ := by
  intro h
  cases h with
  | lambda hpc hann _ _ =>
    rw [hann _ rfl] at hpc
    cases hpc with
    | bvar hlt => omega

/-- The LHS `let f : σ = (λ(x:a).x) in f` *is* well-typed (at `Int → Int`): the
    cofinite premise types the *opened* bound expression `λ(x : X). x` at
    `X → X`, and the body uses `f` at the instance `Int → Int`. -/
private theorem probe_LHS_typeable :
    TypeOfHM ⟨[], []⟩ probeLHS (.arrow (.prim .int) (.prim .int)) := by
  apply TypeOfHM.letIn (M := probeSig) (L := [])
  · show ContainsBvarsUpTo 1 (Ty.arrow (Ty.bvar 0) (Ty.bvar 0))
    exact .arrow (.bvar (by omega)) (.bvar (by omega))
  · intro σ' h; exact Option.some.inj h
  · intro Xs hfresh
    have hlen : Xs.length = 1 := hfresh.length
    rcases Xs with _ | ⟨X, _ | ⟨Y, tl⟩⟩
    · simp at hlen
    · have hterm : Expr.openBoundTyVars (some probeSig) [X] probeV
          = .lambda (some (.fvar X)) (.var 0) := rfl
      have htype : probeSig.openVars [X] = .arrow (.fvar X) (.fvar X) := rfl
      rw [hterm, htype]
      exact TypeOfHM.lambda .fvar (fun T h => Option.some.inj h) rfl
        (TypeOfHM.var (tyArgs := []) rfl (by intro t ht; cases ht) .fvar)
    · simp at hlen
  · rfl
  · exact TypeOfHM.var (polyTy := probeSig) (tyArgs := [.prim .int]) rfl
      (by intro t ht; simp only [List.mem_singleton] at ht; subst ht; exact .prim)
      (.arrow (.bvar rfl) (.bvar rfl))

/-- Therefore subject reduction is FALSE as stated: there is a well-typed term
    that steps (via `letReduce`) to an untypeable one. -/
private theorem preservation_is_unsound :
    ¬ (∀ {ctx : Ctx} {e e' : Expr} {τ : Ty},
        SmallStep.Step e e' → TypeOfHM ctx e τ → TypeOfHM ctx e' τ) := by
  intro pres
  have hstep : SmallStep.Step probeLHS ((Expr.var 0).substN 0 [probeV]) :=
    SmallStep.Step.letReduce (SmallStep.IsValue.lambda _ _)
  exact probe_reduct_untypeable _ _ (pres hstep probe_LHS_typeable)

end PreservationProbe

/-! ### Type erasure of annotations

Annotations are runtime-irrelevant in HM: we *check with annotations* (`TypeOfHM`)
but *run erased*. `Expr.eraseTyAnnots` drops every `lambda`/`letIn` annotation
(replacing it with `none`); on the resulting annotation-free terms the cofinite
`letIn` premise's `openBoundTyVars` collapses to the bare bound expression, so
the dynamic metatheory (`subst_lemma`/`progress`/`preservation`) goes through by
essentially the original argument. `erase_preserves_typing` (below) is the bridge
that makes this sound: erasing preserves typeability. -/

mutual
/-- Drop every type annotation in a term (lambda param annotations and `let`
    scheme annotations become `none`), recursively. -/
def Expr.eraseTyAnnots : Expr → Expr
  | .primLit p          => .primLit p
  | .lambda _ body      => .lambda none body.eraseTyAnnots
  | .app f arg          => .app f.eraseTyAnnots arg.eraseTyAnnots
  | .letIn _ rhs body   => .letIn none rhs.eraseTyAnnots body.eraseTyAnnots
  | .var i              => .var i
  | .ctor c             => .ctor c
  | .match_ scrut branches => .match_ scrut.eraseTyAnnots (BranchList.eraseTyAnnots branches)
private def BranchList.eraseTyAnnots :
    List (MatchPattern × Expr) → List (MatchPattern × Expr)
  | []                  => []
  | (pat, body) :: rest => (pat, body.eraseTyAnnots) :: BranchList.eraseTyAnnots rest
end

/-- Annotation-free terms: every `lambda`/`letIn` annotation is `none`. The
    image of `Expr.eraseTyAnnots`; preserved by the dynamic semantics. -/
inductive Expr.IsTyErased : Expr → Prop
  | primLit (p) : IsTyErased (.primLit p)
  | lambda {body} : body.IsTyErased → IsTyErased (.lambda none body)
  | app {f arg} : f.IsTyErased → arg.IsTyErased → IsTyErased (.app f arg)
  | letIn {rhs body} : rhs.IsTyErased → body.IsTyErased → IsTyErased (.letIn none rhs body)
  | var (i) : IsTyErased (.var i)
  | ctor (c) : IsTyErased (.ctor c)
  | match_ {scrut branches} : scrut.IsTyErased →
      (∀ pat e, (pat, e) ∈ branches → e.IsTyErased) → IsTyErased (.match_ scrut branches)

/-- Membership in an erased branch list reflects to the original. -/
theorem BranchList.mem_eraseTyAnnots {branches : List (MatchPattern × Expr)}
    {branch' : MatchPattern × Expr} (h : branch' ∈ BranchList.eraseTyAnnots branches) :
    ∃ pat body, (pat, body) ∈ branches ∧ branch' = (pat, body.eraseTyAnnots) := by
  induction branches with
  | nil => simp only [BranchList.eraseTyAnnots] at h; exact absurd h List.not_mem_nil
  | cons hd tl ih =>
    obtain ⟨pat, body⟩ := hd
    simp only [BranchList.eraseTyAnnots, List.mem_cons] at h
    cases h with
    | inl heq => exact ⟨pat, body, List.mem_cons_self, heq⟩
    | inr h' => obtain ⟨p, b, hm, he⟩ := ih h'; exact ⟨p, b, List.mem_cons_of_mem _ hm, he⟩

/-- The erased image of a branch is a member of the erased branch list. -/
theorem BranchList.mem_eraseTyAnnots_of_mem {branches : List (MatchPattern × Expr)}
    {pat : MatchPattern} {body : Expr} (h : (pat, body) ∈ branches) :
    (pat, body.eraseTyAnnots) ∈ BranchList.eraseTyAnnots branches := by
  induction branches with
  | nil => exact absurd h List.not_mem_nil
  | cons hd tl ih =>
    obtain ⟨p, b⟩ := hd
    simp only [BranchList.eraseTyAnnots, List.mem_cons] at h ⊢
    cases h with
    | inl heq => simp only [Prod.mk.injEq] at heq; obtain ⟨rfl, rfl⟩ := heq; exact Or.inl rfl
    | inr h' => exact Or.inr (ih h')

/-- Opening scoped type variables only rewrites annotations, which erasure
    deletes — so opening then erasing equals just erasing. -/
theorem Expr.eraseTyAnnots_openTyVarsAux {Xs : List Nat} :
    ∀ (e : Expr) (d : Nat), (e.openTyVarsAux d Xs).eraseTyAnnots = e.eraseTyAnnots := by
  intro e
  induction e using Expr.rec_strong with
  | primLit p => intro d; rfl
  | app f inp ihf ihi => intro d; simp only [Expr.openTyVarsAux, Expr.eraseTyAnnots]; rw [ihf d, ihi d]
  | lambda ann body ih => intro d; simp only [Expr.openTyVarsAux, Expr.eraseTyAnnots]; rw [ih d]
  | letIn ann be body ihbe ihbody =>
    intro d
    cases ann with
    | none => simp only [Expr.openTyVarsAux, Expr.eraseTyAnnots]; rw [ihbe d, ihbody d]
    | some σ =>
      simp only [Expr.openTyVarsAux, Expr.eraseTyAnnots]
      rw [ihbe (d + σ.paramCount), ihbody d]
  | var n => intro d; rfl
  | ctor nm => intro d; rfl
  | match_ scrut branches ihs ihbs =>
    intro d
    simp only [Expr.openTyVarsAux, Expr.eraseTyAnnots, Expr.match_.injEq]
    refine ⟨ihs d, ?_⟩
    revert ihbs
    induction branches with
    | nil => intro _; rfl
    | cons hd tl ihtl =>
      intro ihbs
      obtain ⟨pat, body⟩ := hd
      simp only [BranchList.openTyVarsAux, BranchList.eraseTyAnnots]
      rw [ihbs pat body List.mem_cons_self d,
          ihtl (fun p e hm => ihbs p e (List.mem_cons_of_mem _ hm))]

theorem Expr.eraseTyAnnots_openTyVars {Xs : List Nat} {e : Expr} :
    (e.openTyVars Xs).eraseTyAnnots = e.eraseTyAnnots :=
  Expr.eraseTyAnnots_openTyVarsAux e 0

theorem Expr.eraseTyAnnots_openBoundTyVars {ann : Option PolyTy} {Xs : List Nat} {e : Expr} :
    (Expr.openBoundTyVars ann Xs e).eraseTyAnnots = e.eraseTyAnnots := by
  cases ann with
  | none => rfl
  | some σ => exact Expr.eraseTyAnnots_openTyVars

/-- `eraseTyAnnots` produces an annotation-free term. -/
theorem Expr.isTyErased_eraseTyAnnots (e : Expr) : e.eraseTyAnnots.IsTyErased := by
  induction e using Expr.rec_strong with
  | primLit p => exact .primLit p
  | lambda ann body ih => exact .lambda ih
  | app f arg ihf iha => exact .app ihf iha
  | letIn ann rhs body ihr ihb => exact .letIn ihr ihb
  | var n => exact .var n
  | ctor nm => exact .ctor nm
  | match_ scrut branches ihs ihbs =>
    refine .match_ ihs ?_
    intro pat e hmem
    obtain ⟨p, body, hm, heq⟩ := BranchList.mem_eraseTyAnnots hmem
    rw [Prod.mk.injEq] at heq
    rw [heq.2]
    exact ihbs p body hm

/-- **Linchpin of the erasure approach**: erasing a term's type annotations
    preserves typeability. Erasing only *relaxes* the typing rules — the
    `lambda`/`letIn` annotation-pinning premises (`ann = some _ → …`) become
    vacuous, and the cofinite `letIn` premise's `openBoundTyVars` collapses (no
    annotation ⇒ no opening) to the bare bound expression. The scheme `M` and
    parameter type `paramTy` are kept verbatim. Proven by induction on the typing
    derivation (`rec_strong`). This is the bridge that makes "check with
    annotations, run erased" sound. -/
theorem TypeOfHM.erase_preserves_typing {ctx : Ctx} {e : Expr} {τ : Ty}
    (h : TypeOfHM ctx e τ) : TypeOfHM ctx e.eraseTyAnnots τ := by
  induction h using TypeOfHM.rec_strong with
  | primLitUnit => exact .primLitUnit
  | primLitInt => exact .primLitInt
  | primLitNat => exact .primLitNat
  -- | primLitBool => exact .primLitBool
  | primLitStr => exact .primLitStr
  | app _ _ ihf ihinput => exact .app ihf ihinput
  | var hlook htyargs hinst => exact .var hlook htyargs hinst
  | ctor hlook htyargs hinst => exact .ctor hlook htyargs hinst
  | lambda hpc hann heq hbody ihbody =>
    subst heq
    exact TypeOfHM.lambda hpc (fun T h => Option.noConfusion h) rfl ihbody
  | letIn hwf hann hcofin heq hbody ihcofin ihbody =>
    subst heq
    expose_names
    refine TypeOfHM.letIn (M := M) (L := L) hwf (fun σ h => Option.noConfusion h) ?_ rfl ihbody
    intro Xs hfresh
    have hc := ihcofin Xs hfresh
    rwa [Expr.eraseTyAnnots_openBoundTyVars] at hc
  | match_ hscrut hne hfirst hbrs ihscrut ihbrs =>
    refine TypeOfHM.match_ ihscrut ?_ ?_ ?_
    · intro hcontra
      obtain ⟨⟨p, b⟩, rest, hb⟩ := List.exists_cons_of_ne_nil hne
      rw [hb] at hcontra
      simp [BranchList.eraseTyAnnots] at hcontra
    · obtain ⟨c, n, body, rest, rfl⟩ := hfirst
      exact ⟨c, n, _, _, rfl⟩
    · intro branch' hmem'
      obtain ⟨pat, body, hmem, rfl⟩ := BranchList.mem_eraseTyAnnots hmem'
      rcases ihbrs (pat, body) hmem with
        ⟨ct, c, n, instContents, hpat, hlook, htyName, hpc, hcontents, hinstC, _, hbodyIH⟩ |
        ⟨hpat, _, hbodyIH⟩
      · subst hpat
        exact TypeOfMatchBranch.mk hlook htyName hpc hcontents hinstC rfl rfl hbodyIH
      · subst hpat
        exact TypeOfMatchBranch.wildcard hbodyIH

/-! ### The clean substitution lemma (no side condition!). -/

/-- Chargueraud's `typing_trm_subst`, adapted to our de-Bruijn-level
    term-var encoding. Substituting `v` (a value) for the variable at
    position `env_post.length` preserves typing, provided `v` types at
    every instance of the scheme `M` that bound that variable.

    For beta-reduction, `M = PolyTy.mkTrivial paramTy` and
    `HasScheme ctx v (mkTrivial paramTy)` reduces to `TypeOfHM ctx v paramTy`
    via `HasScheme.ofTypeOfHM`.

    For let-reduction, `M` is the generalised scheme and `HasScheme` is
    obtained via `HasScheme.fromHasSchemeVars` from the cofinite premise of
    the `letIn` rule that introduced `M`. -/
theorem TypeOfHM.subst_lemma
    {ctors : CtorEnv} {env_post env : Env}
    {e : Expr} {τ : Ty} {M : PolyTy} {v : Expr}
    (h_M_wf : M.WF)
    (h_body : TypeOfHM ⟨env_post ++ [M] ++ env, ctors⟩ e τ)
    (h_v : HasScheme ⟨env, ctors⟩ v M)
    (he : e.IsTyErased) :
    TypeOfHM ⟨env_post ++ env, ctors⟩
      (e.substN env_post.length [v]) τ := by
  induction e using Expr.rec_strong generalizing env_post τ with
  | primLit p =>
    cases h_body with
    | primLitUnit => exact .primLitUnit
    | primLitInt  => exact .primLitInt
    | primLitNat  => exact .primLitNat
    -- | primLitBool => exact .primLitBool
    | primLitStr  => exact .primLitStr
  | app f inp ih_f ih_i =>
    cases he with
    | app hf_e hi_e =>
    cases h_body with
    | app hf hi =>
      simp only [Expr.substN]
      exact .app (ih_f hf hf_e) (ih_i hi hi_e)
  | lambda ann body ih =>
    cases he with
    | lambda hbody_e =>
    cases h_body with
    | lambda hpc hann heq hbody =>
      subst heq
      simp only [Expr.substN]
      refine TypeOfHM.lambda hpc hann rfl ?_
      exact ih (env_post := PolyTy.mkTrivial _ :: env_post) hbody hbody_e
  | letIn ann boundExpr body ih_be ih_body =>
    cases he with
    | letIn hbe_e hbody_e =>
    cases h_body with
    | letIn hsch hann hcofin heq hbodyinner =>
      subst heq
      simp only [Expr.substN]
      -- annotation is `none` (erased), so `openBoundTyVars none = id`: the
      -- cofinite premise types `boundExpr` directly and the structural IH applies.
      refine TypeOfHM.letIn hsch hann
        (fun Xs hfresh => ih_be (hcofin Xs hfresh) hbe_e) rfl ?_
      exact ih_body (env_post := _ :: env_post) hbodyinner hbody_e
  | ctor name =>
    cases h_body with
    | ctor hlook htyargs hinst =>
      exact .ctor hlook htyargs hinst
  | var i =>
    cases h_body with
    | var h_lookup h_tyArgs_closed h_inst =>
      rcases lt_trichotomy i env_post.length with h_lt | h_eq | h_gt
      · -- i < env_post.length: substN keeps `.var i`
        have h_subst : (Expr.var i).substN env_post.length [v] = .var i := by
          simp [Expr.substN, h_lt]
        rw [h_subst]
        refine .var ?_ h_tyArgs_closed h_inst
        show (env_post ++ env)[i]? = _
        rw [List.getElem?_append_left h_lt]
        rw [List.append_assoc, List.getElem?_append_left h_lt] at h_lookup
        exact h_lookup
      · -- i = env_post.length: the substituted position
        subst h_eq
        have h_subst : (Expr.var env_post.length).substN env_post.length [v]
            = v.shiftFrom 0 env_post.length := by simp [Expr.substN]
        rw [h_subst]
        rw [List.append_assoc, List.getElem?_append_right (Nat.le_refl _),
            Nat.sub_self] at h_lookup
        simp only [List.singleton_append, List.getElem?_cons_zero,
          Option.some.injEq] at h_lookup
        subst h_lookup
        expose_names
        -- `h_inst : InstantiatesBy tyArgs M.body τ`; produce `v : τ` from `h_v`
        set Vs := (List.range M.paramCount).map
            (fun i => (tyArgs[i]?).getD (Ty.prim PrimTy.unit)) with hVs
        have hVs_lc : Ty.AreLC M.paramCount Vs := by
          refine ⟨by simp [hVs], ?_⟩
          intro V hV
          simp only [hVs, List.mem_map, List.mem_range] at hV
          obtain ⟨j, _, rfl⟩ := hV
          cases htj : tyArgs[j]? with
          | none => simp only [Option.getD_none]; exact .prim
          | some t =>
            simp only [Option.getD_some]
            exact h_tyArgs_closed t (List.mem_of_getElem? htj)
        have hτ : τ = M.openWith Vs := by
          have := InstantiatesBy.eq_openWith_range h_inst h_M_wf
          simpa [hVs, PolyTy.openWith] using this
        have hv_typed : TypeOfHM ⟨env, ctors⟩ v τ := by
          rw [hτ]; exact h_v Vs hVs_lc
        have hw := TypeOfHM.weaken_env (env_pre := []) (env_extra := env_post)
          (env := env) hv_typed
        exact hw
      · -- i > env_post.length: substN returns `.var (i - 1)`
        have h_not_lt : ¬ (i < env_post.length) := by omega
        have h_not_lt' : ¬ (i - env_post.length < (1 : Nat)) := by omega
        have h_subst : (Expr.var i).substN env_post.length [v] = .var (i - 1) := by
          simp [Expr.substN, h_not_lt, h_not_lt']
        rw [h_subst]
        refine .var ?_ h_tyArgs_closed h_inst
        have h_le_i : env_post.length ≤ i := by omega
        rw [List.getElem?_append_right (by omega : env_post.length ≤ i - 1)]
        rw [List.append_assoc, List.getElem?_append_right h_le_i] at h_lookup
        rw [show ([M] ++ env) = (M :: env) from rfl] at h_lookup
        rw [show (i - env_post.length) = (i - env_post.length - 1) + 1 from by omega]
            at h_lookup
        simp only [List.getElem?_cons_succ] at h_lookup
        rw [show (i - 1 - env_post.length) = (i - env_post.length - 1) from by omega]
        exact h_lookup
  | match_ scrut branches ih_scrut ih_branches =>
    cases he with
    | match_ hscrut_e hbr_e =>
    cases h_body with
    | match_ h_scrut h_ne h_brs =>
      simp only [Expr.substN]
      refine TypeOfHM.match_ (ih_scrut h_scrut hscrut_e) ?_ ?_
      · intro hcontra
        obtain ⟨⟨p, b⟩, rest, hb⟩ := List.exists_cons_of_ne_nil h_ne
        rw [hb] at hcontra
        simp [BranchList.substN] at hcontra
      · intro branch' hmem'
        obtain ⟨pat, body, hmem, rfl⟩ := BranchList.mem_substN hmem'
        cases pat with
        | named c n =>
          simp only [MatchPattern.bindCount]
          cases h_brs (.named c n, body) hmem with
          | mk h_lookup h_tyName h_paramCount h_contents h_inst h_pb h_ctx h_bodyT =>
            subst h_ctx
            subst h_pb
            expose_names
            rw [show (instContents.map PolyTy.mkTrivial ++ (env_post ++ [M] ++ env))
                  = (instContents.map PolyTy.mkTrivial ++ env_post) ++ [M] ++ env
                  by rw [List.append_assoc, List.append_assoc, List.append_assoc]]
              at h_bodyT
            have ih_b :=
              ih_branches (.named c n) body hmem
                (env_post := instContents.map PolyTy.mkTrivial ++ env_post)
                h_bodyT (hbr_e (.named c n) body hmem)
            simp only [List.length_append, List.length_map] at ih_b
            rw [← h_inst.length_eq, ← h_contents] at ih_b
            rw [show n + env_post.length = env_post.length + n
                  from Nat.add_comm _ _] at ih_b
            refine TypeOfMatchBranch.mk h_lookup h_tyName h_paramCount h_contents
              h_inst rfl rfl ?_
            rw [List.append_assoc] at ih_b
            exact ih_b
        | wildcard =>
          simp only [MatchPattern.bindCount, Nat.add_zero]
          cases h_brs (.wildcard, body) hmem with
          | wildcard h_bodyT =>
            exact TypeOfMatchBranch.wildcard
              (ih_branches .wildcard body hmem (env_post := env_post)
                h_bodyT (hbr_e .wildcard body hmem))


/-- Multi-binding substitution: substitute a whole block of values `vs` for a
    block of schemes `Ms` (each `vs[j]` typing at every instance of `Ms[j]`).
    Generalises `subst_lemma` from `[v]`/`[M]` to lists — needed for the
    `match_` (n bindings) reduction case of
    preservation. Only the `var` case differs from `subst_lemma` (its
    trichotomy becomes three *ranges*); every other case is verbatim. -/
theorem TypeOfHM.subst_lemma_many
    {ctors : CtorEnv} {env_post env Ms : Env}
    {e : Expr} {τ : Ty} {vs : List Expr}
    (h_Ms_wf : ∀ M ∈ Ms, M.WF)
    (h_body : TypeOfHM ⟨env_post ++ Ms ++ env, ctors⟩ e τ)
    (h_vs : List.Forall₂ (fun v M => HasScheme ⟨env, ctors⟩ v M) vs Ms)
    (he : e.IsTyErased) :
    TypeOfHM ⟨env_post ++ env, ctors⟩ (e.substN env_post.length vs) τ := by
  have h_len : vs.length = Ms.length := h_vs.length_eq
  induction e using Expr.rec_strong generalizing env_post τ with
  | primLit p =>
    cases h_body with
    | primLitUnit => exact .primLitUnit
    | primLitInt  => exact .primLitInt
    | primLitNat  => exact .primLitNat
    -- | primLitBool => exact .primLitBool
    | primLitStr  => exact .primLitStr
  | app f inp ih_f ih_i =>
    cases he with
    | app hf_e hi_e =>
    cases h_body with
    | app hf hi =>
      simp only [Expr.substN]
      exact .app (ih_f hf hf_e) (ih_i hi hi_e)
  | lambda ann body ih =>
    cases he with
    | lambda hbody_e =>
    cases h_body with
    | lambda hpc hann heq hbody =>
      subst heq
      simp only [Expr.substN]
      refine TypeOfHM.lambda hpc hann rfl ?_
      exact ih (env_post := PolyTy.mkTrivial _ :: env_post) hbody hbody_e
  | letIn ann boundExpr body ih_be ih_body =>
    cases he with
    | letIn hbe_e hbody_e =>
    cases h_body with
    | letIn hsch hann hcofin heq hbodyinner =>
      subst heq
      simp only [Expr.substN]
      refine TypeOfHM.letIn hsch hann
        (fun Xs hfresh => ih_be (hcofin Xs hfresh) hbe_e) rfl ?_
      exact ih_body (env_post := _ :: env_post) hbodyinner hbody_e
  | ctor name =>
    cases h_body with
    | ctor hlook htyargs hinst =>
      exact .ctor hlook htyargs hinst
  | var i =>
    cases h_body with
    | var h_lookup h_tyArgs_closed h_inst =>
      by_cases h_lt : i < env_post.length
      · -- below the substituted block: keep `.var i`
        have h_subst : (Expr.var i).substN env_post.length vs = .var i := by
          simp [Expr.substN, h_lt]
        rw [h_subst]
        refine .var ?_ h_tyArgs_closed h_inst
        show (env_post ++ env)[i]? = _
        rw [List.getElem?_append_left h_lt]
        rw [List.append_assoc, List.getElem?_append_left h_lt] at h_lookup
        exact h_lookup
      · push_neg at h_lt
        by_cases h_in : i - env_post.length < vs.length
        · -- inside the substituted block: pick `vs[i - env_post.length]`
          have hj_Ms : i - env_post.length < Ms.length := by omega
          have h_subst : (Expr.var i).substN env_post.length vs
              = (vs[i - env_post.length]).shiftFrom 0 env_post.length := by
            simp only [Expr.substN]
            rw [if_neg (by omega), dif_pos h_in]
          rw [h_subst]
          rw [List.append_assoc, List.getElem?_append_right h_lt,
              List.getElem?_append_left hj_Ms,
              List.getElem?_eq_getElem hj_Ms] at h_lookup
          simp only [Option.some.injEq] at h_lookup
          subst h_lookup
          expose_names
          have hMj_wf : (Ms[i - env_post.length]).WF :=
            h_Ms_wf _ (List.getElem_mem hj_Ms)
          have hvj : HasScheme ⟨env, ctors⟩ (vs[i - env_post.length])
              (Ms[i - env_post.length]) := h_vs.get h_in hj_Ms
          set Vs := (List.range (Ms[i - env_post.length]).paramCount).map
              (fun k => (tyArgs[k]?).getD (Ty.prim PrimTy.unit)) with hVs
          have hVs_lc : Ty.AreLC (Ms[i - env_post.length]).paramCount Vs := by
            refine ⟨by simp [hVs], ?_⟩
            intro V hV
            simp only [hVs, List.mem_map, List.mem_range] at hV
            obtain ⟨k, _, rfl⟩ := hV
            cases htk : tyArgs[k]? with
            | none => simp only [Option.getD_none]; exact .prim
            | some t =>
              simp only [Option.getD_some]
              exact h_tyArgs_closed t (List.mem_of_getElem? htk)
          have hτ : τ = (Ms[i - env_post.length]).openWith Vs := by
            have := InstantiatesBy.eq_openWith_range h_inst hMj_wf
            simpa [hVs, PolyTy.openWith] using this
          have hv_typed : TypeOfHM ⟨env, ctors⟩ (vs[i - env_post.length]) τ := by
            rw [hτ]; exact hvj Vs hVs_lc
          exact TypeOfHM.weaken_env (env_pre := []) (env_extra := env_post)
            (env := env) hv_typed
        · -- above the block: shift down by `vs.length`
          push_neg at h_in
          have h_subst : (Expr.var i).substN env_post.length vs
              = .var (i - vs.length) := by
            simp only [Expr.substN]
            rw [if_neg (by omega), dif_neg (by omega)]
          rw [h_subst]
          refine .var ?_ h_tyArgs_closed h_inst
          rw [List.getElem?_append_right (by omega : env_post.length ≤ i - vs.length)]
          rw [List.append_assoc, List.getElem?_append_right h_lt,
              List.getElem?_append_right (by omega : Ms.length ≤ i - env_post.length)]
            at h_lookup
          rw [show (i - vs.length) - env_post.length
                = (i - env_post.length) - Ms.length by omega]
          exact h_lookup
  | match_ scrut branches ih_scrut ih_branches =>
    cases he with
    | match_ hscrut_e hbr_e =>
    cases h_body with
    | match_ h_scrut h_ne h_brs =>
      simp only [Expr.substN]
      refine TypeOfHM.match_ (ih_scrut h_scrut hscrut_e) ?_ ?_
      · intro hcontra
        obtain ⟨⟨p, b⟩, rest, hb⟩ := List.exists_cons_of_ne_nil h_ne
        rw [hb] at hcontra
        simp [BranchList.substN] at hcontra
      · intro branch' hmem'
        obtain ⟨pat, body, hmem, rfl⟩ := BranchList.mem_substN hmem'
        cases pat with
        | named c n =>
          simp only [MatchPattern.bindCount]
          cases h_brs (.named c n, body) hmem with
          | mk h_lookup h_tyName h_paramCount h_contents h_inst h_pb h_ctx h_bodyT =>
            subst h_ctx
            subst h_pb
            expose_names
            rw [show (instContents.map PolyTy.mkTrivial ++ (env_post ++ Ms ++ env))
                  = (instContents.map PolyTy.mkTrivial ++ env_post) ++ Ms ++ env
                  by rw [List.append_assoc, List.append_assoc, List.append_assoc]]
              at h_bodyT
            have ih_b :=
              ih_branches (.named c n) body hmem
                (env_post := instContents.map PolyTy.mkTrivial ++ env_post)
                h_bodyT (hbr_e (.named c n) body hmem)
            simp only [List.length_append, List.length_map] at ih_b
            rw [← h_inst.length_eq, ← h_contents] at ih_b
            rw [show n + env_post.length = env_post.length + n
                  from Nat.add_comm _ _] at ih_b
            refine TypeOfMatchBranch.mk h_lookup h_tyName h_paramCount h_contents
              h_inst rfl rfl ?_
            rw [List.append_assoc] at ih_b
            exact ih_b
        | wildcard =>
          simp only [MatchPattern.bindCount, Nat.add_zero]
          cases h_brs (.wildcard, body) hmem with
          | wildcard h_bodyT =>
            exact TypeOfMatchBranch.wildcard
              (ih_branches .wildcard body hmem (env_post := env_post)
                h_bodyT (hbr_e .wildcard body hmem))


/-! ## Canonical forms

Inversion lemmas: a *value* of a given type has a particular syntactic shape.
Used by progress to conclude the next step exists when a value sits in a given
type position. These only invert the value constructors (`lambda`/`pair`/
`ctor`/ctor-chains), so they're unaffected by the cofinite `let` rules. -/

/-- A well-typed constructor chain has a `wrapArrows … (customTy …)` type:
    a prefix of arrows ending in a `customTy`.

    Inducts syntactically on `e` (rather than on `h_chain`) because `IsCtorChain`
    is mutually defined with `IsValue`, so the `induction` tactic refuses it. -/
private lemma TypeOfHM.ctor_chain_has_customTy_form
    {ctx e τ}
    (h_chain : SmallStep.IsCtorChain e) (h_ty : TypeOfHM ctx e τ) :
    ∃ name args tys, τ = Ty.wrapArrows (.customTy name args) tys := by
  induction e using Expr.rec_strong generalizing ctx τ with
  | ctor _ =>
    cases h_ty with
    | ctor _ _ h_inst =>
      have ⟨instArgs, instTys, h_eq⟩ :=
        InstantiatesBy.wrapArrows_customTy_form h_inst
      exact ⟨_, instArgs, instTys, h_eq⟩
  | app _ _ ihf _ =>
    cases h_chain with
    | app h_chain' _ =>
      cases h_ty with
      | app h_f_ty _ =>
        obtain ⟨name, args, tys, h_eq⟩ := ihf h_chain' h_f_ty
        cases tys with
        | nil => simp [Ty.wrapArrows] at h_eq
        | cons _ rest =>
          simp only [Ty.wrapArrows] at h_eq
          injection h_eq with _ h_ret
          exact ⟨name, args, rest, h_ret⟩
  | primLit _      => cases h_chain
  | lambda _ _ _   => cases h_chain
  | letIn _ _ _ _ _ => cases h_chain
  | var _          => cases h_chain
  | match_ _ _ _ _ => cases h_chain

theorem TypeOfHM.canonical_arrow {ctx e argTy retTy}
    (h_ty : TypeOfHM ctx e (.arrow argTy retTy))
    (h_val : SmallStep.IsValue e) :
    (∃ ann body, e = .lambda ann body) ∨ SmallStep.IsCtorChain e := by
  cases h_val with
  | primLit _ => cases h_ty
  | lambda ann body => exact .inl ⟨ann, body, rfl⟩
  | ctor name => exact .inr (.ctor name)
  | ctorApp h_chain h_v => exact .inr (.app h_chain h_v)

theorem TypeOfHM.canonical_customTy {ctx e tyName tyArgs}
    (h_ty : TypeOfHM ctx e (.customTy tyName tyArgs))
    (h_val : SmallStep.IsValue e) :
    SmallStep.IsCtorChain e := by
  cases h_val with
  | primLit _ => cases h_ty
  | lambda _ _ => cases h_ty
  | ctor name => exact .ctor name
  | ctorApp h_chain h_v => exact .app h_chain h_v


/-! ## Constructor-chain typing inversion

The keystone for both progress (the matched-constructor's type name and arity)
and preservation's `match_` case (the applied arguments are well-typed at the
instantiated field types). Inducting over the chain, each `app` consumes one of
the constructor's `contents` (one arrow of its `wrapArrows` type). We track the
already-`consumed` fields and the `remaining` ones explicitly. -/

private theorem List.Forall₂.snoc {α β : Type _} {R : α → β → Prop}
    {l1 : List α} {l2 : List β} {a : α} {b : β}
    (h : List.Forall₂ R l1 l2) (hab : R a b) :
    List.Forall₂ R (l1 ++ [a]) (l2 ++ [b]) := by
  induction h with
  | nil => exact .cons hab .nil
  | cons hhd _ ih => exact .cons hhd ih

/-- A well-typed constructor chain decomposes into a head constructor applied to
    args, where the consumed fields are well-typed at their instantiations and
    the result type is the remaining fields wrapped over the (instantiated)
    `customTy`. -/
theorem TypeOfHM.ctor_chain_inversion {ctx : Ctx} {e : Expr} {τ : Ty}
    (h_chain : SmallStep.IsCtorChain e) (h_ty : TypeOfHM ctx e τ) :
    ∃ (name : CtorName) (args : List Expr) (ctor : Ctor)
      (tyArgs consumed remaining : List Ty),
      SmallStep.CtorAppliedTo e name args ∧
      LookupList.get? ctx.ctors name = some ctor ∧
      (∀ t ∈ tyArgs, ContainsBvarsUpTo 0 t) ∧
      ctor.contents = consumed ++ remaining ∧
      List.Forall₂ (fun a c => ∃ ct, InstantiatesBy tyArgs c ct ∧ TypeOfHM ctx a ct)
        args consumed ∧
      InstantiatesBy tyArgs
        (Ty.wrapArrows (.customTy ctor.tyName (Ty.bvarRange ctor.paramCount)) remaining) τ := by
  induction e using Expr.rec_strong generalizing τ with
  | ctor name =>
    cases h_ty with
    | ctor hlook htyargs hinst =>
      exact ⟨name, [], _, _, [], _, .base name, hlook, htyargs, rfl, .nil,
        by simpa [Ctor.toTy] using hinst⟩
  | app f arg ihf _ =>
    cases h_chain with
    | app hchainf hvarg =>
      cases h_ty with
      | app hf harg =>
        obtain ⟨name, args, ctor, tyArgs, consumed, remaining, hcat, hlook, htyargs,
          hcontents, hforall, hinst_f⟩ := ihf hchainf hf
        cases remaining with
        | nil =>
          simp only [Ty.wrapArrows] at hinst_f
          cases hinst_f
        | cons c rest =>
          simp only [Ty.wrapArrows] at hinst_f
          cases hinst_f with
          | arrow hc hrest =>
            refine ⟨name, args ++ [arg], ctor, tyArgs, consumed ++ [c], rest,
              .step hcat, hlook, htyargs, ?_, hforall.snoc ⟨_, hc, harg⟩, hrest⟩
            rw [hcontents]
            exact (List.append_assoc consumed [c] rest).symm
  | primLit _ => cases h_chain
  | lambda _ _ _ => cases h_chain
  | letIn _ _ _ _ _ => cases h_chain
  | var _ => cases h_chain
  | match_ _ _ _ _ => cases h_chain


/-! ## Progress

A well-typed, closed term whose matches are all exhaustive is either a value or
can take a step. The interesting case is `match_`: the scrutinee value is a
constructor chain (`canonical_customTy` + `ctor_chain_inversion`), and the
strengthened `AllMatchesExhaustive.match_` guarantees that the head constructor's
type — which is pinned to the branches — has a covering branch. -/

open SmallStep in
theorem TypeOfHM.progress {ctx : Ctx} {e : Expr} {τ : Ty}
    (h_ty : TypeOfHM ctx e τ) (h_closed : ctx.env = [])
    (h_exh : AllMatchesExhaustive ctx.ctors e) (he : e.IsTyErased) :
    IsValue e ∨ ∃ e', Step e e' := by
  induction e using Expr.rec_strong generalizing ctx τ with
  | primLit p => exact .inl (.primLit p)
  | lambda _ _ _ => exact .inl (.lambda _ _)
  | ctor name => exact .inl (.ctor name)
  | var n =>
    cases h_ty with
    | var h_lookup _ _ => rw [h_closed] at h_lookup; simp at h_lookup
  | app f arg ihf iharg =>
    cases he with
    | app hf_e harg_e =>
    cases h_exh with
    | app h_exh_f h_exh_arg =>
      cases h_ty with
      | app h_f h_arg =>
        rcases ihf h_f h_closed h_exh_f hf_e with hvf | ⟨f', hf⟩
        · rcases iharg h_arg h_closed h_exh_arg harg_e with hva | ⟨arg', harg⟩
          · rcases TypeOfHM.canonical_arrow h_f hvf with ⟨ann, body, rfl⟩ | hchain
            · exact .inr ⟨_, .beta hva⟩
            · exact .inl (.ctorApp hchain hva)
          · exact .inr ⟨_, .appArg hvf harg⟩
        · exact .inr ⟨_, .appFn hf⟩
  | letIn ann rhs body ihrhs _ =>
    cases he with
    | letIn hrhs_e _ =>
    cases h_exh with
    | letIn h_exh_rhs _ =>
      cases h_ty with
      | letIn hwf _ hcofin heq hbody =>
        expose_names
        obtain ⟨Xs, hXlen, hXnodup, hXavoid⟩ := exists_fresh_names L M.paramCount
        -- annotation erased ⇒ `openBoundTyVars none = id`: the cofinite premise
        -- types `rhs` directly, so the structural IH applies.
        have h_rhs := hcofin Xs ⟨hXlen, hXnodup, hXavoid⟩
        rcases ihrhs h_rhs h_closed h_exh_rhs hrhs_e with hvr | ⟨rhs', hrhs⟩
        · exact .inr ⟨_, .letReduce hvr⟩
        · exact .inr ⟨_, .letInRhs hrhs⟩
  | match_ scrut branches ihscrut _ =>
    cases he with
    | match_ hscrut_e _ =>
    cases h_exh with
    | match_ h_exh_scrut _ h_branch_ty h_match_exh =>
      cases h_ty with
      | match_ h_scrut h_ne h_brs =>
        rcases ihscrut h_scrut h_closed h_exh_scrut hscrut_e with hvs | ⟨scrut', hscrut⟩
        · -- scrutinee is a value of customTy type ⇒ a constructor chain
          have hchain := TypeOfHM.canonical_customTy h_scrut hvs
          obtain ⟨name, args, ctor, tyArgs', consumed, remaining,
            hcat, hlook, _, hcontents, hforall, hinst⟩ :=
            TypeOfHM.ctor_chain_inversion hchain h_scrut
          cases remaining with
          | cons c rest => simp only [Ty.wrapArrows] at hinst; cases hinst
          | nil =>
            simp only [Ty.wrapArrows] at hinst
            rw [List.append_nil] at hcontents
            have hlen : args.length = ctor.contents.length := by
              rw [hcontents]; exact hforall.length_eq
            -- `hinst : InstantiatesBy _ (.customTy ctor.tyName _) (.customTy Tscrut tyArgs)`;
            -- inverting it unifies the scrutinee's type name with `ctor.tyName`.
            cases hinst with
            | customTy _ =>
              -- the scrutinee's type name is now `ctor.tyName`. Find a branch
              -- whose pattern matches the head constructor: a wildcard branch
              -- covers directly; a named branch lets us pin the exhaustiveness
              -- type name (via cover1) and invoke coverage (cover2).
              obtain ⟨⟨pat0, body0⟩, rest0, hbeq⟩ := List.exists_cons_of_ne_nil h_ne
              have hb0 : (pat0, body0) ∈ branches := by
                rw [hbeq]; exact List.mem_cons_self
              have hcover : ∃ pat body, (pat, body) ∈ branches ∧
                  pat.matchesCtor name args.length = true := by
                cases pat0 with
                | wildcard => exact ⟨.wildcard, body0, hb0, rfl⟩
                | named c0 n0 =>
                  obtain ⟨pat, body, hmem, hcov⟩ :=
                    h_match_exh name ctor hlook (by
                      obtain ⟨ctorB, hlookB, htyB⟩ := h_branch_ty c0 n0 body0 hb0
                      cases h_brs (.named c0 n0, body0) hb0 with
                      | mk hlookA htyA _ _ _ _ _ _ =>
                        rw [← htyA, Option.some.inj (hlookA.symm.trans hlookB)]
                        exact htyB)
                  exact ⟨pat, body, hmem, by rw [hlen]; exact hcov⟩
              obtain ⟨pat, body, hmem, hcov⟩ := hcover
              obtain ⟨e', hfmb⟩ := findMatchingBranch_of_exists ⟨pat, body, hmem, hcov⟩
              obtain ⟨pat', body', hfirst, _⟩ := findMatchingBranch_to_FirstMatch hfmb
              exact .inr ⟨_, .matchReduce hvs hcat hfirst⟩
        · exact .inr ⟨_, .matchScrut hscrut⟩


/-! ## Preservation

Subject reduction: a well-typed term that takes a step stays well-typed at the
same type. The reduction cases reuse the substitution lemmas; the `matchReduce`
case is the substantial one — it lines up the scrutinee's constructor-chain
typing (`ctor_chain_inversion`) with the matched branch's typing
(`TypeOfMatchBranch`), proving that the two type-argument lists agree on the
relevant bvar indices so the field instantiations coincide. -/

/-- `bvarRangeFrom` reads back its definition pointwise. -/
theorem Ty.bvarRangeFrom_getElem? : ∀ (n s k : Nat), k < n →
    (Ty.bvarRangeFrom s n)[k]? = some (.bvar (s + k)) := by
  intro n
  induction n with
  | zero => intro s k hk; omega
  | succ m ih =>
    intro s k hk
    cases k with
    | zero => simp [Ty.bvarRangeFrom]
    | succ j =>
      simp only [Ty.bvarRangeFrom, List.getElem?_cons_succ]
      have heq : s + 1 + j = s + (j + 1) := by omega
      rw [ih (s + 1) j (by omega), heq]

/-- The `k`-th element of `bvarRange n` is `.bvar k` (for `k < n`). -/
theorem Ty.bvarRange_getElem? {n k : Nat} (hk : k < n) :
    (Ty.bvarRange n)[k]? = some (Ty.bvar k) := by
  unfold Ty.bvarRange
  simpa using Ty.bvarRangeFrom_getElem? n 0 k hk

open SmallStep in
/-- A value is applied to a unique constructor name and argument list. -/
theorem SmallStep.CtorAppliedTo.det {e : Expr} {n1 n2 : CtorName} {a1 a2 : List Expr}
    (h1 : CtorAppliedTo e n1 a1) (h2 : CtorAppliedTo e n2 a2) : n1 = n2 ∧ a1 = a2 := by
  induction h1 generalizing n2 a2 with
  | base name => cases h2 with | base => exact ⟨rfl, rfl⟩
  | step h1' ih =>
    cases h2 with
    | step h2' => obtain ⟨hn, ha⟩ := ih h2'; subst hn; subst ha; exact ⟨rfl, rfl⟩

open SmallStep in
/-- The matched branch is a member of the branch list. -/
theorem SmallStep.FirstMatchingBranch.mem {name arity} {branches} {pat body}
    (h : FirstMatchingBranch name arity branches pat body) : (pat, body) ∈ branches := by
  induction h with
  | here _ => exact List.mem_cons_self
  | there _ _ ih => exact List.mem_cons_of_mem _ ih

open SmallStep in
/-- The matched branch's pattern fires for the matched constructor (it either
    names that constructor at the right arity, or is a wildcard). -/
theorem SmallStep.FirstMatchingBranch.ctor_eq {name arity branches pat body}
    (h : FirstMatchingBranch name arity branches pat body) :
    pat.matchesCtor name arity = true := by
  induction h with
  | here hc => exact hc
  | there _ _ ih => exact ih

/-- Element-wise determinism for two `Forall₂ (InstantiatesBy …)` over a common
    source list, given a per-element determinism hypothesis. -/
private theorem InstantiatesBy.forall2_det {tyArgs1 tyArgs2 : List Ty} :
    ∀ {tys its1 its2 : List Ty},
      (∀ t ∈ tys, ∀ {a b : Ty},
        InstantiatesBy tyArgs1 t a → InstantiatesBy tyArgs2 t b → a = b) →
      List.Forall₂ (InstantiatesBy tyArgs1) tys its1 →
      List.Forall₂ (InstantiatesBy tyArgs2) tys its2 →
      its1 = its2 := by
  intro tys
  induction tys with
  | nil =>
    intro its1 its2 _ hf1 hf2
    cases hf1; cases hf2; rfl
  | cons hd tl ih =>
    intro its1 its2 hdet hf1 hf2
    cases hf1 with
    | cons h1hd h1tl =>
      cases hf2 with
      | cons h2hd h2tl =>
        have hhd : _ = _ := hdet hd List.mem_cons_self h1hd h2hd
        have htl := ih (fun t ht => hdet t (List.mem_cons_of_mem _ ht)) h1tl h2tl
        rw [hhd, htl]

/-- Two instantiations of a `ContainsBvarsUpTo n` type coincide whenever the two
    argument lists agree on every index below `n`. -/
theorem InstantiatesBy.det_agree {n : Nat} {tyArgs1 tyArgs2 : List Ty}
    (hag : ∀ k, k < n → tyArgs1[k]? = tyArgs2[k]?) :
    ∀ {ty t1 t2 : Ty}, ContainsBvarsUpTo n ty →
      InstantiatesBy tyArgs1 ty t1 → InstantiatesBy tyArgs2 ty t2 → t1 = t2 := by
  intro ty
  induction ty using Ty.rec_strong with
  | prim _ => intro t1 t2 _ h1 h2; cases h1; cases h2; rfl
  | arrow a b iha ihb =>
    intro t1 t2 hbv h1 h2
    cases hbv with
    | arrow hba hbb =>
      cases h1 with
      | arrow h1a h1b =>
        cases h2 with
        | arrow h2a h2b => rw [iha hba h1a h2a, ihb hbb h1b h2b]
  | bvar i =>
    intro t1 t2 hbv h1 h2
    cases hbv with
    | bvar hlt =>
      cases h1 with
      | bvar hs1 =>
        cases h2 with
        | bvar hs2 => have h := hag i hlt; rw [hs1, hs2] at h; simpa using h
  | fvar _ => intro t1 t2 _ h1 h2; cases h1; cases h2; rfl
  | customTy nm tys ih =>
    intro t1 t2 hbv h1 h2
    cases hbv with
    | customTy hall =>
      cases h1 with
      | customTy hf1 =>
        cases h2 with
        | customTy hf2 =>
          congr 1
          exact InstantiatesBy.forall2_det
            (fun t ht {_ _} ha hb => ih t ht (hall t ht) ha hb) hf1 hf2

/-- Assemble the per-argument `HasScheme` list for the `match` reduction: each
    matched argument is well-typed at the corresponding instantiated field type
    (the two instantiations coincide by `det_agree`), so it has the trivial
    scheme of that type. -/
private theorem InstantiatesBy.build_match_vs
    {ctx : Ctx} {n : Nat} {tyArgs tyArgsS : List Ty}
    (hag : ∀ k, k < n → tyArgs[k]? = tyArgsS[k]?) :
    ∀ {contents instContents : List Ty} {args : List Expr},
      (∀ c ∈ contents, ContainsBvarsUpTo n c) →
      List.Forall₂ (InstantiatesBy tyArgs) contents instContents →
      List.Forall₂ (fun a c => ∃ ct, InstantiatesBy tyArgsS c ct ∧ TypeOfHM ctx a ct)
        args contents →
      List.Forall₂ (fun v M => HasScheme ctx v M) args (instContents.map PolyTy.mkTrivial) := by
  intro contents
  induction contents with
  | nil =>
    intro instContents args _ hinst hfor
    cases hinst
    cases hfor
    exact .nil
  | cons hd tl ih =>
    intro instContents args hbound hinst hfor
    cases hinst with
    | cons hihd hitl =>
      cases hfor with
      | cons hfhd hftl =>
        obtain ⟨ct, hctS, htyA⟩ := hfhd
        have hdet := InstantiatesBy.det_agree hag (hbound hd List.mem_cons_self) hihd hctS
        refine List.Forall₂.cons ?_
          (ih (fun c hc => hbound c (List.mem_cons_of_mem _ hc)) hitl hftl)
        rw [hdet]
        exact HasScheme.ofTypeOfHM htyA

open SmallStep in
/-- Subject reduction for the **type-erased** dynamic semantics (`he : e` is
    annotation-free). This REPLACES the literal `preservation`, which is false
    for scoped-var annotations (see `preservation_is_unsound`). On erased terms
    every `letIn` annotation is `none`, so the cofinite premise's
    `openBoundTyVars` collapses (`openBoundTyVars none = id`) and the original
    subject-reduction argument goes through: the `substN ⟂ openTyVarsAux`
    obstruction disappears because there are no annotations to open. -/
theorem TypeOfHM.preservation {ctx : Ctx} {e e' : Expr} {τ : Ty}
    (h_step : Step e e') (h_ty : TypeOfHM ctx e τ) (he : e.IsTyErased) :
    TypeOfHM ctx e' τ := by
  induction h_step generalizing τ with
  | beta hval =>
    cases he with
    | app he_lam he_v =>
    cases he_lam with
    | lambda hbody_e =>
    cases h_ty with
    | app hf hi =>
      cases hf with
      | lambda hpc _ heq hbody =>
        subst heq
        exact TypeOfHM.subst_lemma (env_post := []) (M := PolyTy.mkTrivial _)
          hpc hbody (HasScheme.ofTypeOfHM hi) hbody_e
  | letReduce hval =>
    cases he with
    | letIn hv_e hbody_e =>
    cases h_ty with
    | letIn hwf _ hcofin heq hbody =>
      subst heq
      -- annotation `none` ⇒ `hcofin` is literally a `HasSchemeVars` witness for `v`.
      exact TypeOfHM.subst_lemma (env_post := []) hwf hbody
        (HasScheme.fromHasSchemeVars hcofin) hbody_e
  | matchReduce hval hctor hfirst =>
    rename_i scrut branches name args pat body
    cases he with
    | match_ hscrut_e hbr_e =>
    cases h_ty with
    | match_ h_scrut h_ne h_brs =>
      rename_i tyName tyArgs
      have hmem := hfirst.mem
      have hpeq := hfirst.ctor_eq
      cases pat with
      | wildcard =>
        -- A wildcard binds nothing: the reduct is `body.substN 0 [] = body`, and
        -- the wildcard branch types `body` directly in `ctx`.
        simp only [MatchPattern.bindCount, List.take_zero]
        cases h_brs (.wildcard, body) hmem with
        | wildcard hbodyW =>
          exact TypeOfHM.subst_lemma_many (env_post := []) (Ms := []) (by simp)
            hbodyW List.Forall₂.nil (hbr_e _ _ hmem)
      | named c n =>
        -- A matched named branch binds exactly the chain's args
        -- (`n = args.length`), so `args.take pat.bindCount = args`.
        simp only [MatchPattern.matchesCtor, Bool.and_eq_true, beq_iff_eq] at hpeq
        obtain ⟨hcname, hnlen⟩ := hpeq
        simp only [MatchPattern.bindCount]
        rw [hnlen, List.take_length]
        cases h_brs (.named c n, body) hmem with
        | mk hlookB htyNameB hpcB hcontentsB hinstB hpbB hctxB hbodyB =>
          subst hctxB
          subst hpbB
          have hchain := TypeOfHM.canonical_customTy h_scrut hval
          obtain ⟨name', args', ctorS, tyArgsS, consumedS, remainingS,
            hcatS, hlookS, htyargsS, hcontentsS, hforallS, hinstS⟩ :=
            TypeOfHM.ctor_chain_inversion hchain h_scrut
          obtain ⟨hnEq, haEq⟩ := hctor.det hcatS
          subst hnEq
          subst haEq
          rw [hcname] at hlookB
          have hcc := Option.some.inj (hlookS.symm.trans hlookB)
          obtain ⟨instCts, hinstB', hbodyB'⟩ :
              ∃ ic, List.Forall₂ (InstantiatesBy tyArgs) ctorS.contents ic ∧
                TypeOfHM ⟨ic.map PolyTy.mkTrivial ++ ctx.env, ctx.ctors⟩ body τ := by
            refine ⟨_, ?_, hbodyB⟩
            rw [hcc]; exact hinstB
          cases remainingS with
          | cons c rest => simp only [Ty.wrapArrows] at hinstS; cases hinstS
          | nil =>
            rw [List.append_nil] at hcontentsS
            subst hcontentsS
            simp only [Ty.wrapArrows] at hinstS
            cases hinstS with
            | customTy hbvr =>
              have hpc_len : tyArgs.length = ctorS.paramCount := by
                rw [hcc]; exact hpcB.symm
              have hagree : ∀ k, k < ctorS.paramCount → tyArgs[k]? = tyArgsS[k]? := by
                intro k hk
                have hkt : k < tyArgs.length := by omega
                have hkr : k < (Ty.bvarRange ctorS.paramCount).length := by
                  rw [hbvr.length_eq]; exact hkt
                have hrel := List.Forall₂.get hbvr hkr hkt
                simp only [List.get_eq_getElem] at hrel
                have helem : (Ty.bvarRange ctorS.paramCount)[k] = Ty.bvar k := by
                  have h1 := Ty.bvarRange_getElem? (n := ctorS.paramCount) (k := k) hk
                  rw [List.getElem?_eq_getElem hkr] at h1
                  exact Option.some.inj h1
                rw [helem] at hrel
                cases hrel with
                | bvar hsome =>
                  rw [hsome]
                  exact List.getElem?_eq_getElem hkt
              have htyArgs_lc : ∀ t ∈ tyArgs, ContainsBvarsUpTo 0 t := by
                intro t ht
                obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp ht
                have hkpc : k < ctorS.paramCount := by omega
                have hag := hagree k hkpc
                rw [List.getElem?_eq_getElem hk] at hag
                exact htyargsS _ (List.mem_of_getElem? hag.symm)
              have h_Ms_wf : ∀ M ∈ instCts.map PolyTy.mkTrivial, M.WF := by
                intro M hM
                obtain ⟨ic, hic, rfl⟩ := List.mem_map.mp hM
                obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hic
                have hrel := List.Forall₂.get hinstB'
                  (by have := hinstB'.length_eq; omega) hi
                exact InstantiatesBy.preserves_bvars htyArgs_lc hrel
              have h_vs := InstantiatesBy.build_match_vs hagree ctorS.bound hinstB' hforallS
              exact TypeOfHM.subst_lemma_many (env_post := [])
                h_Ms_wf hbodyB' h_vs (hbr_e (.named c n) body hmem)
  | appFn _ ih =>
    cases he with
    | app hf_e harg_e =>
    cases h_ty with
    | app hf hi => exact .app (ih hf hf_e) hi
  | appArg hv _ ih =>
    cases he with
    | app hf_e harg_e =>
    cases h_ty with
    | app hf hi => exact .app hf (ih hi harg_e)
  | letInRhs _ ih =>
    cases he with
    | letIn hrhs_e hbody_e =>
    cases h_ty with
    | letIn hwf hann hcofin heq hbody =>
      exact .letIn hwf hann (fun Xs hfresh => ih (hcofin Xs hfresh) hrhs_e) heq hbody
  | matchScrut _ ih =>
    cases he with
    | match_ hscrut_e _ =>
    cases h_ty with
    | match_ h_scrut h_ne h_brs => exact .match_ (ih h_scrut hscrut_e) h_ne h_brs

open SmallStep in
/-- Erasure preserves branch-body exhaustiveness (companion to
    `exhaustive_eraseTyAnnots`). -/
theorem exhaustive_branches_eraseTyAnnots {ctors : CtorEnv}
    {branches : List (MatchPattern × Expr)}
    (ih : ∀ pat e, (pat, e) ∈ branches →
      AllMatchesExhaustive ctors e → AllMatchesExhaustive ctors e.eraseTyAnnots)
    (h : AllBranchBodiesExhaustive ctors branches) :
    AllBranchBodiesExhaustive ctors (BranchList.eraseTyAnnots branches) := by
  induction branches with
  | nil => exact .nil
  | cons hd tl ih_tl =>
    obtain ⟨pat, body⟩ := hd
    cases h with
    | cons hbody hrest =>
      simp only [BranchList.eraseTyAnnots]
      exact .cons (ih pat body List.mem_cons_self hbody)
        (ih_tl (fun p e hm hae => ih p e (List.mem_cons_of_mem _ hm) hae) hrest)

open SmallStep in
/-- Type erasure preserves match-exhaustiveness: it only drops annotations, so
    every match's branch patterns/coverage are unchanged. -/
theorem exhaustive_eraseTyAnnots {ctors : CtorEnv} :
    ∀ {e : Expr}, AllMatchesExhaustive ctors e → AllMatchesExhaustive ctors e.eraseTyAnnots := by
  intro e
  induction e using Expr.rec_strong with
  | primLit p => intro _; exact .primLit
  | var n => intro _; exact .var
  | ctor nm => intro _; exact .ctor
  | lambda ann body ih => intro h; cases h with | lambda hb => exact .lambda (ih hb)
  | app f arg ihf iha => intro h; cases h with | app hf ha => exact .app (ihf hf) (iha ha)
  | letIn ann rhs body ihr ihb =>
    intro h; cases h with | letIn hr hb => exact .letIn (ihr hr) (ihb hb)
  | match_ scrut branches ihs ihbs =>
    intro h
    cases h with
    | match_ h_scrut h_bodies h_cover1 h_cover2 =>
      simp only [Expr.eraseTyAnnots]
      exact AllMatchesExhaustive.match_ (ihs h_scrut)
        (exhaustive_branches_eraseTyAnnots ihbs h_bodies)
        (fun c n body hmem => by
          obtain ⟨p, b, hm, heq⟩ := BranchList.mem_eraseTyAnnots hmem
          rw [Prod.mk.injEq] at heq
          obtain ⟨hp, -⟩ := heq
          subst hp
          exact h_cover1 c n b hm)
        (fun ctorName ctor hlook htyName => by
          obtain ⟨pat, body, hmem, hcov⟩ := h_cover2 ctorName ctor hlook htyName
          exact ⟨pat, body.eraseTyAnnots, BranchList.mem_eraseTyAnnots_of_mem hmem, hcov⟩)

open SmallStep in
/-- **Type safety for the erased dynamic semantics** ("check with annotations,
    run erased"): a closed, well-typed program's type-erasure is well-typed at
    the same type (via the linchpin `erase_preserves_typing`), makes progress
    (it is a value or steps), and any step preserves typing. Together these say
    the erased program never gets stuck. The static scoped-type-variable feature
    is fully retained — annotations are only dropped at *run* time. -/
theorem TypeOfHM.erased_type_safety {ctors : CtorEnv} {e : Expr} {τ : Ty}
    (h_ty : TypeOfHM ⟨[], ctors⟩ e τ)
    (h_exh : AllMatchesExhaustive ctors e) :
    TypeOfHM ⟨[], ctors⟩ e.eraseTyAnnots τ ∧
    (IsValue e.eraseTyAnnots ∨ ∃ e', Step e.eraseTyAnnots e') ∧
    (∀ e', Step e.eraseTyAnnots e' → TypeOfHM ⟨[], ctors⟩ e' τ) := by
  have h_ty' : TypeOfHM ⟨[], ctors⟩ e.eraseTyAnnots τ := TypeOfHM.erase_preserves_typing h_ty
  have h_erased := Expr.isTyErased_eraseTyAnnots e
  have h_exh' : AllMatchesExhaustive ctors e.eraseTyAnnots := exhaustive_eraseTyAnnots h_exh
  refine ⟨h_ty', ?_, ?_⟩
  · exact TypeOfHM.progress h_ty' rfl h_exh' h_erased
  · intro e' hstep
    exact TypeOfHM.preservation hstep h_ty' h_erased


/-! ## Iterated (multi-step) erased type safety

The single-step `erased_type_safety` is now lifted to the reflexive-transitive
closure of `Step`: a closed, well-typed program's erasure never gets stuck across
*any* number of steps and keeps its type throughout. The new ingredients are two
closure lemmas — `Step` preserves `Expr.IsTyErased` and `AllMatchesExhaustive` —
which let `progress` be re-applied to every reachable term. Both rest on the fact
that the substitutions performed by reduction (`substN`/`shiftFrom`) preserve
those structural predicates. -/

/-- The shifted image of a branch is a member of the shifted branch list. -/
theorem BranchList.mem_shiftFrom_of_mem {threshold n : Nat}
    {branches : List (MatchPattern × Expr)} {pat : MatchPattern} {body : Expr}
    (h : (pat, body) ∈ branches) :
    (pat, body.shiftFrom (threshold + pat.bindCount) n)
      ∈ BranchList.shiftFrom threshold n branches := by
  induction branches with
  | nil => exact absurd h List.not_mem_nil
  | cons hd tl ih =>
    obtain ⟨p, b⟩ := hd
    simp only [BranchList.shiftFrom, List.mem_cons] at h ⊢
    cases h with
    | inl heq => simp only [Prod.mk.injEq] at heq; obtain ⟨rfl, rfl⟩ := heq; exact Or.inl rfl
    | inr h' => exact Or.inr (ih h')

/-- The substituted image of a branch is a member of the substituted branch list. -/
theorem BranchList.mem_substN_of_mem {k : Nat} {vs : List Expr}
    {branches : List (MatchPattern × Expr)} {pat : MatchPattern} {body : Expr}
    (h : (pat, body) ∈ branches) :
    (pat, body.substN (k + pat.bindCount) vs) ∈ BranchList.substN k vs branches := by
  induction branches with
  | nil => exact absurd h List.not_mem_nil
  | cons hd tl ih =>
    obtain ⟨p, b⟩ := hd
    simp only [BranchList.substN, List.mem_cons] at h ⊢
    cases h with
    | inl heq => simp only [Prod.mk.injEq] at heq; obtain ⟨rfl, rfl⟩ := heq; exact Or.inl rfl
    | inr h' => exact Or.inr (ih h')

/-- `shiftFrom` (a term-variable renumbering) preserves annotation-freeness:
    it never touches annotations, only `.var` indices. -/
theorem Expr.IsTyErased.shiftFrom :
    ∀ {e : Expr}, e.IsTyErased → ∀ (threshold n : Nat),
      (e.shiftFrom threshold n).IsTyErased := by
  intro e
  induction e using Expr.rec_strong with
  | primLit p => intro _ threshold n; exact .primLit _
  | var m => intro _ threshold n; simp only [Expr.shiftFrom]; split <;> exact .var _
  | ctor nm => intro _ threshold n; exact .ctor _
  | lambda ann body ih =>
    intro he threshold n; cases he with
    | lambda hbody => simp only [Expr.shiftFrom]; exact .lambda (ih hbody (threshold + 1) n)
  | app f arg ihf iharg =>
    intro he threshold n; cases he with
    | app hf ha => simp only [Expr.shiftFrom]; exact .app (ihf hf threshold n) (iharg ha threshold n)
  | letIn ann rhs body ihr ihb =>
    intro he threshold n; cases he with
    | letIn hr hb =>
      simp only [Expr.shiftFrom]; exact .letIn (ihr hr threshold n) (ihb hb (threshold + 1) n)
  | match_ scrut branches ihs ihbr =>
    intro he threshold n; cases he with
    | match_ hscrut hbr =>
      simp only [Expr.shiftFrom]
      refine .match_ (ihs hscrut threshold n) ?_
      intro pat e hmem
      obtain ⟨p, body, hmemO, heq⟩ := BranchList.mem_shiftFrom hmem
      rw [Prod.mk.injEq] at heq
      obtain ⟨-, rfl⟩ := heq
      exact ihbr p body hmemO (hbr p body hmemO) (threshold + p.bindCount) n

/-- `substN` preserves annotation-freeness, provided every substituted value is
    annotation-free: reduction only ever inserts erased sub-terms (and `shiftFrom`
    keeps them erased) into erased terms. -/
theorem Expr.IsTyErased.substN {vs : List Expr} (hvs : ∀ v ∈ vs, v.IsTyErased) :
    ∀ {e : Expr}, e.IsTyErased → ∀ (k : Nat), (e.substN k vs).IsTyErased := by
  intro e
  induction e using Expr.rec_strong with
  | primLit p => intro _ k; exact .primLit _
  | var m =>
    intro _ k
    simp only [Expr.substN]
    split
    · exact .var _
    · split
      · next h => exact (hvs _ (List.getElem_mem h)).shiftFrom 0 k
      · exact .var _
  | ctor nm => intro _ k; exact .ctor _
  | lambda ann body ih =>
    intro he k; cases he with
    | lambda hbody => simp only [Expr.substN]; exact .lambda (ih hbody (k + 1))
  | app f arg ihf iharg =>
    intro he k; cases he with
    | app hf ha => simp only [Expr.substN]; exact .app (ihf hf k) (iharg ha k)
  | letIn ann rhs body ihr ihb =>
    intro he k; cases he with
    | letIn hr hb => simp only [Expr.substN]; exact .letIn (ihr hr k) (ihb hb (k + 1))
  | match_ scrut branches ihs ihbr =>
    intro he k; cases he with
    | match_ hscrut hbr =>
      simp only [Expr.substN]
      refine .match_ (ihs hscrut k) ?_
      intro pat e hmem
      obtain ⟨p, body, hmemO, heq⟩ := BranchList.mem_substN hmem
      rw [Prod.mk.injEq] at heq
      obtain ⟨-, rfl⟩ := heq
      exact ihbr p body hmemO (hbr p body hmemO) (k + p.bindCount)


namespace SmallStep

/-- `shiftFrom` preserves branch-body exhaustiveness (companion to
    `AllMatchesExhaustive.shiftFrom`). -/
theorem AllBranchBodiesExhaustive.shiftFrom {ctors : CtorEnv} {threshold n : Nat}
    {branches : List (MatchPattern × Expr)}
    (ih : ∀ pat e, (pat, e) ∈ branches →
      AllMatchesExhaustive ctors e → ∀ (threshold n : Nat),
        AllMatchesExhaustive ctors (e.shiftFrom threshold n))
    (h : AllBranchBodiesExhaustive ctors branches) :
    AllBranchBodiesExhaustive ctors (BranchList.shiftFrom threshold n branches) := by
  induction branches with
  | nil => exact .nil
  | cons hd tl ih_tl =>
    obtain ⟨pat, body⟩ := hd
    cases h with
    | cons hbody hrest =>
      simp only [BranchList.shiftFrom]
      exact .cons (ih pat body List.mem_cons_self hbody (threshold + pat.bindCount) n)
        (ih_tl (fun p e hm hae => ih p e (List.mem_cons_of_mem _ hm) hae) hrest)

/-- `shiftFrom` (a term-variable renumbering) preserves match-exhaustiveness: it
    never touches a match's patterns or the ctor env, only `.var` indices. -/
theorem AllMatchesExhaustive.shiftFrom {ctors : CtorEnv} :
    ∀ {e : Expr}, AllMatchesExhaustive ctors e → ∀ (threshold n : Nat),
      AllMatchesExhaustive ctors (e.shiftFrom threshold n) := by
  intro e
  induction e using Expr.rec_strong with
  | primLit p => intro _ threshold n; exact .primLit
  | var m => intro _ threshold n; simp only [Expr.shiftFrom]; split <;> exact .var
  | ctor nm => intro _ threshold n; exact .ctor
  | lambda ann body ih =>
    intro h threshold n; cases h with
    | lambda hb => simp only [Expr.shiftFrom]; exact .lambda (ih hb (threshold + 1) n)
  | app f arg ihf iharg =>
    intro h threshold n; cases h with
    | app hf ha => simp only [Expr.shiftFrom]; exact .app (ihf hf threshold n) (iharg ha threshold n)
  | letIn ann rhs body ihr ihb =>
    intro h threshold n; cases h with
    | letIn hr hb =>
      simp only [Expr.shiftFrom]; exact .letIn (ihr hr threshold n) (ihb hb (threshold + 1) n)
  | match_ scrut branches ihs ihbr =>
    intro h threshold n; cases h with
    | match_ h_scrut h_bodies h_cover1 h_cover2 =>
      simp only [Expr.shiftFrom]
      exact AllMatchesExhaustive.match_ (ihs h_scrut threshold n)
        (AllBranchBodiesExhaustive.shiftFrom ihbr h_bodies)
        (fun c n body hmem => by
          obtain ⟨p, b, hm, heq⟩ := BranchList.mem_shiftFrom hmem
          rw [Prod.mk.injEq] at heq
          obtain ⟨hp, -⟩ := heq
          subst hp
          exact h_cover1 c n b hm)
        (fun ctorName ctor hlook htyName => by
          obtain ⟨pat, body, hmem, hcov⟩ := h_cover2 ctorName ctor hlook htyName
          exact ⟨pat, body.shiftFrom (threshold + pat.bindCount) n,
            BranchList.mem_shiftFrom_of_mem hmem, hcov⟩)

/-- `substN` preserves branch-body exhaustiveness (companion to
    `AllMatchesExhaustive.substN`). -/
theorem AllBranchBodiesExhaustive.substN {ctors : CtorEnv} {k : Nat} {vs : List Expr}
    {branches : List (MatchPattern × Expr)}
    (ih : ∀ pat e, (pat, e) ∈ branches →
      AllMatchesExhaustive ctors e → ∀ (k' : Nat),
        AllMatchesExhaustive ctors (e.substN k' vs))
    (h : AllBranchBodiesExhaustive ctors branches) :
    AllBranchBodiesExhaustive ctors (BranchList.substN k vs branches) := by
  induction branches with
  | nil => exact .nil
  | cons hd tl ih_tl =>
    obtain ⟨pat, body⟩ := hd
    cases h with
    | cons hbody hrest =>
      simp only [BranchList.substN]
      exact .cons (ih pat body List.mem_cons_self hbody (k + pat.bindCount))
        (ih_tl (fun p e hm hae => ih p e (List.mem_cons_of_mem _ hm) hae) hrest)

/-- `substN` preserves match-exhaustiveness, provided every substituted value is
    exhaustive: substitution leaves a match's patterns and the ctor env untouched,
    so coverage is unchanged; the only inserted sub-terms are the (exhaustive)
    values, shifted by `shiftFrom` (which also preserves exhaustiveness). -/
theorem AllMatchesExhaustive.substN {ctors : CtorEnv} {vs : List Expr}
    (hvs : ∀ v ∈ vs, AllMatchesExhaustive ctors v) :
    ∀ {e : Expr}, AllMatchesExhaustive ctors e → ∀ (k : Nat),
      AllMatchesExhaustive ctors (e.substN k vs) := by
  intro e
  induction e using Expr.rec_strong with
  | primLit p => intro _ k; exact .primLit
  | var m =>
    intro _ k
    simp only [Expr.substN]
    split
    · exact .var
    · split
      · next h => exact (hvs _ (List.getElem_mem h)).shiftFrom 0 k
      · exact .var
  | ctor nm => intro _ k; exact .ctor
  | lambda ann body ih =>
    intro h k; cases h with
    | lambda hb => simp only [Expr.substN]; exact .lambda (ih hb (k + 1))
  | app f arg ihf iharg =>
    intro h k; cases h with
    | app hf ha => simp only [Expr.substN]; exact .app (ihf hf k) (iharg ha k)
  | letIn ann rhs body ihr ihb =>
    intro h k; cases h with
    | letIn hr hb => simp only [Expr.substN]; exact .letIn (ihr hr k) (ihb hb (k + 1))
  | match_ scrut branches ihs ihbr =>
    intro h k; cases h with
    | match_ h_scrut h_bodies h_cover1 h_cover2 =>
      simp only [Expr.substN]
      exact AllMatchesExhaustive.match_ (ihs h_scrut k)
        (AllBranchBodiesExhaustive.substN ihbr h_bodies)
        (fun c n body hmem => by
          obtain ⟨p, b, hm, heq⟩ := BranchList.mem_substN hmem
          rw [Prod.mk.injEq] at heq
          obtain ⟨hp, -⟩ := heq
          subst hp
          exact h_cover1 c n b hm)
        (fun ctorName ctor hlook htyName => by
          obtain ⟨pat, body, hmem, hcov⟩ := h_cover2 ctorName ctor hlook htyName
          exact ⟨pat, body.substN (k + pat.bindCount) vs,
            BranchList.mem_substN_of_mem hmem, hcov⟩)

/-- Every argument of a constructor-chain value is annotation-free if the chain is. -/
theorem CtorAppliedTo.args_isTyErased {e : Expr} {name : CtorName} {args : List Expr}
    (h : CtorAppliedTo e name args) (he : e.IsTyErased) : ∀ a ∈ args, a.IsTyErased := by
  induction h with
  | base name => intro a ha; exact absurd ha List.not_mem_nil
  | step _ ih =>
    cases he with
    | app hf harg =>
      intro a ha
      rw [List.mem_append] at ha
      cases ha with
      | inl h_in => exact ih hf a h_in
      | inr h_in => rw [List.mem_singleton] at h_in; subst h_in; exact harg

/-- Every argument of a constructor-chain value is exhaustive if the chain is. -/
theorem CtorAppliedTo.args_exhaustive {ctors : CtorEnv} {e : Expr} {name : CtorName}
    {args : List Expr} (h : CtorAppliedTo e name args)
    (he : AllMatchesExhaustive ctors e) : ∀ a ∈ args, AllMatchesExhaustive ctors a := by
  induction h with
  | base name => intro a ha; exact absurd ha List.not_mem_nil
  | step _ ih =>
    cases he with
    | app hf harg =>
      intro a ha
      rw [List.mem_append] at ha
      cases ha with
      | inl h_in => exact ih hf a h_in
      | inr h_in => rw [List.mem_singleton] at h_in; subst h_in; exact harg

/-- A branch body drawn from an exhaustively-checked branch list is itself
    exhaustive. -/
theorem AllBranchBodiesExhaustive.mem {ctors : CtorEnv} :
    ∀ {branches : List (MatchPattern × Expr)} {pat : MatchPattern} {body : Expr},
      AllBranchBodiesExhaustive ctors branches → (pat, body) ∈ branches →
      AllMatchesExhaustive ctors body := by
  intro branches
  induction branches with
  | nil => intro pat body _ hmem; exact absurd hmem List.not_mem_nil
  | cons hd tl ih =>
    intro pat body h hmem
    obtain ⟨pat', body'⟩ := hd
    cases h with
    | cons hbody hrest =>
      cases hmem with
      | head => exact hbody
      | tail _ hmem' => exact ih hrest hmem'

/-- **Reduction preserves annotation-freeness.** Every `Step` only rearranges
    erased sub-terms or substitutes erased values (via `substN`) into erased
    bodies, so the reduct stays in the image of `eraseTyAnnots`. -/
theorem Step.preserves_isTyErased {e e' : Expr}
    (h_step : Step e e') (he : e.IsTyErased) : e'.IsTyErased := by
  induction h_step with
  | beta hval =>
    cases he with
    | app he_lam he_v =>
      cases he_lam with
      | lambda hbody =>
        exact Expr.IsTyErased.substN
          (fun x hx => by rw [List.mem_singleton] at hx; subst hx; exact he_v) hbody 0
  | letReduce hval =>
    cases he with
    | letIn he_v he_body =>
      exact Expr.IsTyErased.substN
        (fun x hx => by rw [List.mem_singleton] at hx; subst hx; exact he_v) he_body 0
  | matchReduce hval hctor hfirst =>
    cases he with
    | match_ hscrut_e hbr_e =>
      exact Expr.IsTyErased.substN
        (fun a ha => CtorAppliedTo.args_isTyErased hctor hscrut_e a (List.mem_of_mem_take ha))
        (hbr_e _ _ hfirst.mem) 0
  | appFn _ ih => cases he with | app hf ha => exact .app (ih hf) ha
  | appArg hv _ ih => cases he with | app hf ha => exact .app hf (ih ha)
  | letInRhs _ ih => cases he with | letIn hr hb => exact .letIn (ih hr) hb
  | matchScrut _ ih => cases he with | match_ hscrut hbr => exact .match_ (ih hscrut) hbr

/-- **Reduction preserves match-exhaustiveness.** Reduction never invents new
    match patterns: congruence steps keep the same matches, and the substituting
    steps insert exhaustive values into exhaustive bodies (`AllMatchesExhaustive`
    is closed under `substN`). The `matchReduce` case selects a branch body, which
    is exhaustive because the whole branch list was. -/
theorem Step.preserves_exhaustive {ctors : CtorEnv} {e e' : Expr}
    (h_exh : AllMatchesExhaustive ctors e) (h_step : Step e e') :
    AllMatchesExhaustive ctors e' := by
  induction h_step with
  | beta hval =>
    cases h_exh with
    | app h_lam h_v =>
      cases h_lam with
      | lambda h_body =>
        exact AllMatchesExhaustive.substN
          (fun x hx => by rw [List.mem_singleton] at hx; subst hx; exact h_v) h_body 0
  | letReduce hval =>
    cases h_exh with
    | letIn h_v h_body =>
      exact AllMatchesExhaustive.substN
        (fun x hx => by rw [List.mem_singleton] at hx; subst hx; exact h_v) h_body 0
  | matchReduce hval hctor hfirst =>
    cases h_exh with
    | match_ h_scrut h_bodies h_cover1 h_cover2 =>
      exact AllMatchesExhaustive.substN
        (fun a ha => CtorAppliedTo.args_exhaustive hctor h_scrut a (List.mem_of_mem_take ha))
        (h_bodies.mem hfirst.mem) 0
  | appFn _ ih => cases h_exh with | app hf ha => exact .app (ih hf) ha
  | appArg hv _ ih => cases h_exh with | app hf ha => exact .app hf (ih ha)
  | letInRhs _ ih => cases h_exh with | letIn hr hb => exact .letIn (ih hr) hb
  | matchScrut _ ih =>
    cases h_exh with
    | match_ h_scrut h_bodies h_cover1 h_cover2 =>
      exact .match_ (ih h_scrut) h_bodies h_cover1 h_cover2

end SmallStep

open SmallStep in
/-- **Iterated subject reduction (erased).** Across any number of `Step`s, a
    closed annotation-free well-typed term keeps its type, and stays both
    annotation-free and exhaustive (so `progress` can be re-applied at the end).
    Proven by induction on the reflexive-transitive closure: each tail step uses
    single-step `preservation` together with the two closure lemmas
    (`Step.preserves_isTyErased`, `Step.preserves_exhaustive`). -/
theorem TypeOfHM.preservation_star {ctors : CtorEnv} {e e' : Expr} {τ : Ty}
    (h_rtc : Relation.ReflTransGen Step e e')
    (h_ty : TypeOfHM ⟨[], ctors⟩ e τ) (he : e.IsTyErased)
    (h_exh : AllMatchesExhaustive ctors e) :
    TypeOfHM ⟨[], ctors⟩ e' τ ∧ e'.IsTyErased ∧ AllMatchesExhaustive ctors e' := by
  induction h_rtc with
  | refl => exact ⟨h_ty, he, h_exh⟩
  | tail _ h_bc ih =>
    obtain ⟨h_ty_b, h_b, h_exh_b⟩ := ih
    exact ⟨TypeOfHM.preservation h_bc h_ty_b h_b,
      Step.preserves_isTyErased h_bc h_b,
      Step.preserves_exhaustive h_exh_b h_bc⟩

open SmallStep in
/-- **Iterated type safety for the erased dynamic semantics** ("check with
    annotations, run erased"): a closed, well-typed program's type-erasure never
    gets stuck across *any* number of steps and preserves its type throughout.
    For every term `e'` reachable from `e.eraseTyAnnots` by the reflexive-
    transitive closure of `Step`, `e'` is still well-typed at `τ` and is either a
    value or can take another step. This lifts the single-step
    `erased_type_safety` via `preservation_star` (iterated preservation, staying
    erased + exhaustive) followed by `progress`. -/
theorem TypeOfHM.erased_type_safety_star {ctors : CtorEnv} {e : Expr} {τ : Ty}
    (h_ty : TypeOfHM ⟨[], ctors⟩ e τ) (h_exh : AllMatchesExhaustive ctors e) :
    ∀ e', Relation.ReflTransGen Step e.eraseTyAnnots e' →
      TypeOfHM ⟨[], ctors⟩ e' τ ∧ (IsValue e' ∨ ∃ e'', Step e' e'') := by
  intro e' h_rtc
  obtain ⟨h_ty', he', h_exh'⟩ :=
    TypeOfHM.preservation_star h_rtc
      (TypeOfHM.erase_preserves_typing h_ty)
      (Expr.isTyErased_eraseTyAnnots e)
      (exhaustive_eraseTyAnnots h_exh)
  exact ⟨h_ty', TypeOfHM.progress h_ty' rfl h_exh' he'⟩
