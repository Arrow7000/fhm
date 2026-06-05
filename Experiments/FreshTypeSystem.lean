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

/-- Name of a value binding -/
inductive ValName
  | mk (str : String)
  deriving DecidableEq, Repr







-- abbrev TyCtx (ty : Type) := List (ty)
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
  | bool
  | str
  deriving DecidableEq, Repr


inductive Ty
  | prim : PrimTy → Ty
  | pair : (fst snd : Ty) → Ty
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

  | pair :
    ContainsBvarsUpTo n fst →
    ContainsBvarsUpTo n snd →
    ContainsBvarsUpTo n (.pair fst snd)

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

  | pair :
    NoFreeVars fst →
    NoFreeVars snd →
    NoFreeVars (.pair fst snd)

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
  | bool : Bool → PrimLitExpr
  | str : String → PrimLitExpr


/-- Only supporting type constructor name matches for now -/
structure MatchPattern where
  ctor : CtorName
  /-- this is basically just a binding range. i.e. if 2 this means we've bound 2 new "names" to the context -/
  contents : Nat


/-- An expression in our language -/
inductive Expr
  | primLit (prim : PrimLitExpr)
  | pair (a b : Expr)
  | lambda (body : Expr)
  | app (f input : Expr)
  | letIn (bindingExpr body : Expr)
  /-- Destructuring a pair `let (a,b) = pairExpr in body` -/
  | letPairIn (pairExpr body : Expr)
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





def CtorEnv.toTy (ctorEnv : CtorEnv) (ctorName : CtorName) : Option PolyTy :=
  ctorEnv.get? ctorName
  |>.map (·.toTy)







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
  | .pair a b => (a.freeVars ++ b.freeVars).dedup
  | .arrow a b => (a.freeVars ++ b.freeVars).dedup
  | .fvar n => [n]
  | .bvar _ => []
  | .customTy _ tys => TyList.freeVars tys

private def TyList.freeVars : List Ty → List Nat
  | [] => []
  | head :: tail => (head.freeVars ++ TyList.freeVars tail).dedup

end



def Env.freeVars : Env → List Nat
  | [] => []
  | polyTy :: tail =>
    (polyTy.body.freeVars ++ freeVars tail).dedup


mutual

/-- For every `.fvar i`, if `i < vars.length`, replace the `.fvar` with `.bvar vars[i]`.

In other words, remove the given free vars and bind them back up. I.e. close them up, to make a polytype with `vars.length` binders ✨ -/
def Ty.closeOver (vars : List Nat) : Ty → Ty
  | .prim p          => .prim p
  | .pair a b        => .pair (a.closeOver vars) (b.closeOver vars)
  | .arrow a b       => .arrow (a.closeOver vars) (b.closeOver vars)
  | .bvar i          => .bvar i
  | .customTy nm tys => .customTy nm (TyList.closeOver vars tys)
  | .fvar n          =>
      match vars.idxOf? n with
      | some i => .bvar i
      | none   => .fvar n


private def TyList.closeOver (vars : List Nat) : List Ty → List Ty
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
  | case2 a b aih bih
  | case3 a b aih bih =>
    cases prem
    tauto
  | case4 =>
    simp [closeOver]
    constructor
    cases prem
    omega
  | case5 nm tys ih =>
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
  | case6 n i hsome =>
    rw [Ty.closeOver.eq_6]
    simp [hsome]
    refine .bvar ?_
    exact List.idxOf?_lt_length hsome
  | case7 n hnone =>
    rw [Ty.closeOver.eq_6]
    simp [hnone]
    exact .fvar
  | case8 =>
    rename_i h
    simp at h
  | case9 arg rest ih_arg ih_rest =>
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
  case pair a b iha ihb => ...
  case arrow a b iha ihb => ...
  case bvar n           => ...
  case fvar n           => ...
  case customTy nm tys ih => ...   -- ih : ∀ t ∈ tys, P t
```
-/
@[elab_as_elim]
def Ty.rec_strong.{u} {motive : Ty → Sort u}
    (prim     : ∀ p, motive (.prim p))
    (pair     : ∀ a b, motive a → motive b → motive (.pair a b))
    (arrow    : ∀ a b, motive a → motive b → motive (.arrow a b))
    (bvar     : ∀ n, motive (.bvar n))
    (fvar     : ∀ n, motive (.fvar n))
    (customTy : ∀ nm tys, (∀ t ∈ tys, motive t) → motive (.customTy nm tys)) :
    (ty : Ty) → motive ty
  | .prim p          => prim p
  | .pair a b        =>
      pair a b
        (Ty.rec_strong prim pair arrow bvar fvar customTy a)
        (Ty.rec_strong prim pair arrow bvar fvar customTy b)
  | .arrow a b       =>
      arrow a b
        (Ty.rec_strong prim pair arrow bvar fvar customTy a)
        (Ty.rec_strong prim pair arrow bvar fvar customTy b)
  | .bvar n          => bvar n
  | .fvar n          => fvar n
  | .customTy nm tys =>
      customTy nm tys
        (fun t _ht => Ty.rec_strong prim pair arrow bvar fvar customTy t)
termination_by ty => sizeOf ty
decreasing_by
  all_goals simp_wf
  all_goals first
    | omega
    | (have := List.sizeOf_lt_of_mem _ht; omega)


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
  case pair a b iha ihb                => ...
  case lambda body ih                  => ...
  case app f input ihf ihi             => ...
  case letIn be body ihbe ihbo         => ...
  case letPairIn pe body ihpe ihbo     => ...
  case var n                           => ...
  case ctor nm                         => ...
  case match_ scrutinee branches ihs ihbs => ...
    -- ihbs : ∀ pat e, (pat, e) ∈ branches → P e
```
-/
@[elab_as_elim]
def Expr.rec_strong.{u} {motive : Expr → Sort u}
    (primLit    : ∀ p, motive (.primLit p))
    (pair       : ∀ a b, motive a → motive b → motive (.pair a b))
    (lambda     : ∀ body, motive body → motive (.lambda body))
    (app        : ∀ f input, motive f → motive input → motive (.app f input))
    (letIn      : ∀ bindingExpr body,
                    motive bindingExpr → motive body →
                    motive (.letIn bindingExpr body))
    (letPairIn  : ∀ pairExpr body,
                    motive pairExpr → motive body →
                    motive (.letPairIn pairExpr body))
    (var        : ∀ n, motive (.var n))
    (ctor       : ∀ nm, motive (.ctor nm))
    (match_     : ∀ scrutinee branches,
                    motive scrutinee →
                    (∀ pat e, (pat, e) ∈ branches → motive e) →
                    motive (.match_ scrutinee branches)) :
    (e : Expr) → motive e
  | .primLit p          => primLit p
  | .pair a b           =>
      pair a b
        (Expr.rec_strong primLit pair lambda app letIn letPairIn var ctor match_ a)
        (Expr.rec_strong primLit pair lambda app letIn letPairIn var ctor match_ b)
  | .lambda body        =>
      lambda body
        (Expr.rec_strong primLit pair lambda app letIn letPairIn var ctor match_ body)
  | .app f input        =>
      app f input
        (Expr.rec_strong primLit pair lambda app letIn letPairIn var ctor match_ f)
        (Expr.rec_strong primLit pair lambda app letIn letPairIn var ctor match_ input)
  | .letIn be body      =>
      letIn be body
        (Expr.rec_strong primLit pair lambda app letIn letPairIn var ctor match_ be)
        (Expr.rec_strong primLit pair lambda app letIn letPairIn var ctor match_ body)
  | .letPairIn pe body  =>
      letPairIn pe body
        (Expr.rec_strong primLit pair lambda app letIn letPairIn var ctor match_ pe)
        (Expr.rec_strong primLit pair lambda app letIn letPairIn var ctor match_ body)
  | .var n              => var n
  | .ctor nm            => ctor nm
  | .match_ scrutinee branches =>
      match_ scrutinee branches
        (Expr.rec_strong primLit pair lambda app letIn letPairIn var ctor match_ scrutinee)
        (fun _pat e _hb =>
          Expr.rec_strong primLit pair lambda app letIn letPairIn var ctor match_ e)
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
  | .pair a b => .pair (a.instantiate subst) (b.instantiate subst)
  | .arrow a b => .arrow (a.instantiate subst) (b.instantiate subst)
  | .bvar n => subst n
  | .fvar n => .fvar n
  | .customTy name tys => .customTy name (TyList.instantiate subst tys)

def TyList.instantiate (subst : Nat → Ty) : List Ty → List Ty
  | [] => []
  | head :: tail => head.instantiate subst :: TyList.instantiate subst tail

end


/-- Get the `i`th item from the `tyArgs` list. Otherwise return a `.bvar i` -/
def Ty.instSubst (tyArgs : List Ty) (i : Nat) : Ty :=
  tyArgs[i]?.getD (.bvar i)



/-- Resulting type is the input type with the `.bvar i`s swapped out for the `i`th item in `tyArgs`.

Cannot be produced for a `bvar` whose index is out of range of `tyArgs`. Thus if tyArgs doesn't contain any `bvar`s, neither does the output.

@TODO: hm maybe should make the source type here be a PolyTy, and then we can also ensure that all bvars are within range of the original polyty paramCount? then it's also just nicer to work with tbh. instantiation is semantically always from a polyty to a monoty, so it's odd that as it is it is a monoty to another monoty.
-/
inductive InstantiatesBy (tyArgs : List Ty) : Ty → Ty → Prop
  | prim :
    InstantiatesBy tyArgs (.prim p) (.prim p)

  | pair :
    InstantiatesBy tyArgs fst instFst →
    InstantiatesBy tyArgs snd instSnd →
    InstantiatesBy tyArgs (.pair fst snd) (.pair instFst instSnd)

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








/-- `ty` can only contain `bvar`s that are in `vars`. If `vars` is empty, `ty` contains no `bvar`s at all. -/
inductive OnlyContainsBvars (vars : List Nat) : (ty : Ty) → Prop
  | prim :
    OnlyContainsBvars vars (.prim p)

  | pair :
    OnlyContainsBvars vars fst →
    OnlyContainsBvars vars snd →
    OnlyContainsBvars vars (.pair fst snd)

  | arrow :
    OnlyContainsBvars vars fst →
    OnlyContainsBvars vars snd →
    OnlyContainsBvars vars (.arrow fst snd)

  | fvar :
    OnlyContainsBvars vars (.fvar n)

  | customTy :
    (∀ ty ∈ tys, OnlyContainsBvars vars ty) →
    OnlyContainsBvars vars (.customTy name tys)

  | bvar :
    i ∈ vars →
    OnlyContainsBvars vars (.bvar i)








mutual
/-- If there are no `bvar`s in `tyArgs`, `instTy` won't contain any `bvar`s -/
theorem InstantiatesBy.no_bvars_if_nin_tyArgs
    (h_args : ∀ ty' ∈ tyArgs, OnlyContainsBvars [] ty')
    (h_inst : InstantiatesBy tyArgs ty instTy) :
    OnlyContainsBvars [] instTy := by
  cases h_inst
  case prim => exact .prim
  case pair _ _ a b => exact .pair (no_bvars_if_nin_tyArgs h_args a) (no_bvars_if_nin_tyArgs h_args b)
  case arrow _ _ a b => exact .arrow (no_bvars_if_nin_tyArgs h_args a) (no_bvars_if_nin_tyArgs h_args b)
  case fvar => exact .fvar
  case bvar h => exact h_args _ (List.mem_of_getElem? h)
  case customTy h_forall =>
    apply OnlyContainsBvars.customTy
    exact list_no_bvars_if_nin_tyArgs h_args h_forall

theorem InstantiatesBy.list_no_bvars_if_nin_tyArgs
    (h_args : ∀ ty' ∈ tyArgs, OnlyContainsBvars [] ty')
    (h_forall : List.Forall₂ (InstantiatesBy tyArgs) tys instTys) :
    ∀ ty ∈ instTys, OnlyContainsBvars [] ty := by
  intro ty mem
  induction h_forall with
  | nil => exact absurd mem List.not_mem_nil
  | cons hd tl ih =>
    cases mem with
    | head _ => exact no_bvars_if_nin_tyArgs h_args hd
    | tail _ h => exact ih h
end



/-- The zipping of two lists. Lists must be equal in length. -/
inductive Zipped : List α → List β → List (α × β) → Prop
  | nil :
    Zipped [] [] []

  | cons {as bs abs} :
    Zipped as bs abs →
    Zipped (a :: as) (b :: bs) ((a,b) :: abs)




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
  | .pair a b          => .pair (a.shiftFrom threshold n) (b.shiftFrom threshold n)
  | .lambda body       => .lambda (body.shiftFrom (threshold + 1) n)
  | .app f arg         => .app (f.shiftFrom threshold n) (arg.shiftFrom threshold n)
  | .letIn rhs body    =>
      .letIn (rhs.shiftFrom threshold n) (body.shiftFrom (threshold + 1) n)
  | .letPairIn rhs body =>
      .letPairIn (rhs.shiftFrom threshold n) (body.shiftFrom (threshold + 2) n)
  | .ctor c            => .ctor c
  | .match_ scrut branches =>
      .match_ (scrut.shiftFrom threshold n)
        (BranchList.shiftFrom threshold n branches)

private def BranchList.shiftFrom (threshold : Nat) (n : Nat) :
    List (MatchPattern × Expr) → List (MatchPattern × Expr)
  | []                  => []
  | (pat, body) :: rest =>
      (pat, body.shiftFrom (threshold + pat.contents) n)
        :: BranchList.shiftFrom threshold n rest

end

mutual

/--
Capture-avoiding multi-substitution under de Bruijn *indices* (innermost = 0).

Replaces `.var (k + j)` with `(vs[j]).shiftFrom 0 k` for `j ∈ [0, vs.length)`,
and shifts higher indices down by `vs.length`. The `shiftFrom 0 k` accounts
for the `k` binders the substitution has traversed into.

When traversing into a binder, `k` is incremented by the number of binders
introduced (1 for `lambda`/`letIn`, 2 for `letPairIn`, `pat.contents` for each
match branch body).

Used to implement beta, let-reduction, letPair-reduction, and match-reduction
in one uniform operation.

Replaces `.var`s that are `≥ k` with their corresponding item in `vs`. If the var index is higher than `k+vs.length`, just shift it down by `vs.length`.

In other words, this replaces a bunch of specific vars with their values and leaves other one untouched.
-/
def Expr.substN (k : Nat) (vs : List Expr) : Expr → Expr
  | .var i =>
      if i < k then .var i
      else if h : i - k < vs.length then (vs[i - k]).shiftFrom 0 k
      else .var (i - vs.length)
  | .primLit p         => .primLit p
  | .pair a b          => .pair (a.substN k vs) (b.substN k vs)
  | .lambda body       => .lambda (body.substN (k + 1) vs)
  | .app f arg         => .app (f.substN k vs) (arg.substN k vs)
  | .letIn rhs body    =>
      .letIn (rhs.substN k vs) (body.substN (k + 1) vs)
  | .letPairIn rhs body =>
      .letPairIn (rhs.substN k vs) (body.substN (k + 2) vs)
  | .ctor n            => .ctor n
  | .match_ scrut branches =>
      .match_ (scrut.substN k vs) (BranchList.substN k vs branches)

private def BranchList.substN (k : Nat) (vs : List Expr) :
    List (MatchPattern × Expr) → List (MatchPattern × Expr)
  | []                  => []
  | (pat, body) :: rest =>
      (pat, body.substN (k + pat.contents) vs)
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
  | lambda body :
      IsValue (.lambda body)
  | pair {v₁ v₂} :
      IsValue v₁ → IsValue v₂ →
      IsValue (.pair v₁ v₂)
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
    pat.ctor = name →
    pat.contents = arity →
    FirstMatchingBranch name arity ((pat, body) :: rest) pat body
  | there :
    ¬(pat'.ctor = name ∧ pat'.contents = arity) →
    FirstMatchingBranch name arity rest pat body →
    FirstMatchingBranch name arity ((pat', body') :: rest) pat body


/-- Call-by-value small-step reduction. Left-to-right evaluation order. -/
inductive Step : Expr → Expr → Prop

  -- ─── reduction rules ────────────────────────────────────────────────

  /-- Beta. (NB: `body.substN 0 [v]` substitutes the argument `v` into `body`;
      written via `substN` rather than `subst1` because `_.subst1 0 v` misfires
      under dot notation — `subst1`'s first `Expr` parameter is `v`, not the
      target.) -/
  | beta {body v} :
      IsValue v →
      Step (.app (.lambda body) v) (body.substN 0 [v])

  /-- Let reduction (after rhs has been reduced to a value). -/
  | letReduce {v body} :
      IsValue v →
      Step (.letIn v body) (body.substN 0 [v])

  /-- Let-pair destructure on a fully-reduced pair. -/
  | letPairReduce {v₁ v₂ body} :
      IsValue v₁ → IsValue v₂ →
      Step (.letPairIn (.pair v₁ v₂) body) (body.substN 0 [v₂, v₁])

  /-- Match reduction. The scrutinee must be a fully-evaluated ctor chain
      whose ctor name matches the *first* applicable branch pattern. -/
  | matchReduce {scrut branches name args pat body} :
      IsValue scrut →
      CtorAppliedTo scrut name args →
      FirstMatchingBranch name args.length branches pat body →
      Step (.match_ scrut branches) (body.substN 0 args)

  -- ─── congruence rules (enforce left-to-right CBV) ─────────────────

  /-- Reduce the first component of a pair. -/
  | pairFst {a a' b} :
      Step a a' →
      Step (.pair a b) (.pair a' b)

  /-- Once the first component is a value, reduce the second. -/
  | pairSnd {v b b'} :
      IsValue v → Step b b' →
      Step (.pair v b) (.pair v b')

  /-- Reduce the function position of an application. -/
  | appFn {f f' arg} :
      Step f f' →
      Step (.app f arg) (.app f' arg)

  /-- Once the function is a value, reduce the argument. -/
  | appArg {v arg arg'} :
      IsValue v → Step arg arg' →
      Step (.app v arg) (.app v arg')

  /-- Reduce the rhs of a let-binding. -/
  | letInRhs {rhs rhs' body} :
      Step rhs rhs' →
      Step (.letIn rhs body) (.letIn rhs' body)

  /-- Reduce the rhs of a let-pair-binding. -/
  | letPairRhs {rhs rhs' body} :
      Step rhs rhs' →
      Step (.letPairIn rhs body) (.letPairIn rhs' body)

  /-- Reduce the scrutinee of a match. -/
  | matchScrut {scrut scrut' branches} :
      Step scrut scrut' →
      Step (.match_ scrut branches) (.match_ scrut' branches)



/-! ### Decidable value / ctor-chain checks -/

mutual

def isValue : Expr → Bool
  | .primLit _ => true
  | .lambda _ => true
  | .pair a b => isValue a && isValue b
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
    if pat.ctor = name ∧ pat.contents = args.length then
      some (body.substN 0 args)
    else
      findMatchingBranch name args rest

/-! ### Small-step evaluation function -/

/-- Compute one step of CBV reduction, returning `none` if the expression is
    already a value or is stuck (ill-typed / open term). -/
def step : Expr → Option Expr
  | .pair a b =>
    if isValue a then
      if isValue b then none
      else do let b' ← step b; return .pair a b'
    else do let a' ← step a; return .pair a' b

  | .app f arg =>
    if isValue f then
      if isValue arg then
        match f with
        | .lambda body => some (body.substN 0 [arg])
        | _ => none
      else do let arg' ← step arg; return .app f arg'
    else do let f' ← step f; return .app f' arg

  | .letIn rhs body =>
    if isValue rhs then some (body.substN 0 [rhs])
    else do let rhs' ← step rhs; return .letIn rhs' body

  | .letPairIn rhs body =>
    if isValue rhs then
      match rhs with
      | .pair v₁ v₂ => some (body.substN 0 [v₂, v₁])
      | _ => none
    else do let rhs' ← step rhs; return .letPairIn rhs' body

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
  | lambda body _ => exact ⟨⟨fun _ => .lambda body, fun _ => rfl⟩, ⟨nofun, nofun⟩⟩
  | ctor name => exact ⟨⟨fun _ => .ctor name, fun _ => rfl⟩, ⟨fun _ => .ctor name, fun _ => rfl⟩⟩
  | pair a b iha ihb =>
    refine ⟨⟨fun h => ?_, fun h => ?_⟩, ⟨nofun, nofun⟩⟩
    · simp only [isValue, Bool.and_eq_true] at h
      exact .pair (iha.1.mp h.1) (ihb.1.mp h.2)
    · cases h with | pair ha hb =>
      simp only [isValue, Bool.and_eq_true]
      exact ⟨iha.1.mpr ha, ihb.1.mpr hb⟩
  | app f arg ihf iharg =>
    simp only [isValue, isCtorChain, Bool.and_eq_true]
    exact ⟨⟨fun ⟨hf, ha⟩ => .ctorApp (ihf.2.mp hf) (iharg.1.mp ha),
            fun h => by cases h with | ctorApp hc hv => exact ⟨ihf.2.mpr hc, iharg.1.mpr hv⟩⟩,
           ⟨fun ⟨hf, ha⟩ => .app (ihf.2.mp hf) (iharg.1.mp ha),
            fun h => by cases h with | app hc hv => exact ⟨ihf.2.mpr hc, iharg.1.mpr hv⟩⟩⟩
  | var _ => exact ⟨⟨nofun, nofun⟩, ⟨nofun, nofun⟩⟩
  | letIn _ _ _ _ => exact ⟨⟨nofun, nofun⟩, ⟨nofun, nofun⟩⟩
  | letPairIn _ _ _ _ => exact ⟨⟨nofun, nofun⟩, ⟨nofun, nofun⟩⟩
  | match_ _ _ _ _ => exact ⟨⟨nofun, nofun⟩, ⟨nofun, nofun⟩⟩

theorem isValue_iff_IsValue {e : Expr} : isValue e = true ↔ IsValue e :=
  (isValue_isCtorChain_correct e).1

theorem isCtorChain_iff_IsCtorChain {e : Expr} : isCtorChain e = true ↔ IsCtorChain e :=
  (isValue_isCtorChain_correct e).2

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
      e' = body.substN 0 args := by
  induction branches with
  | nil => simp [findMatchingBranch] at h
  | cons hd tl ih =>
    obtain ⟨pat, body⟩ := hd
    simp only [findMatchingBranch] at h
    split at h
    · rename_i hm
      simp at h
      exact ⟨pat, body, .here hm.1 hm.2, h.symm⟩
    · rename_i hnm
      obtain ⟨p, b, hfirst, heq⟩ := ih h
      exact ⟨p, b, .there hnm hfirst, heq⟩

private theorem FirstMatch_to_findMatchingBranch {name : CtorName} {arity : Nat}
    {branches : List (MatchPattern × Expr)} {pat : MatchPattern} {body : Expr}
    (h : FirstMatchingBranch name arity branches pat body)
    {args : List Expr} (hlen : arity = args.length) :
    findMatchingBranch name args branches = some (body.substN 0 args) := by
  induction h with
  | here hctor harity =>
    subst hlen
    simp [findMatchingBranch, hctor, harity]
  | there hnot _ ih =>
    subst hlen
    simp only [findMatchingBranch, if_neg hnot]
    exact ih

private theorem isCtorChain_imp_isValue {e : Expr}
    (h : isCtorChain e = true) : isValue e = true := by
  cases e <;> simp_all [isValue, isCtorChain]

private theorem isValue_step_none {e : Expr} (hv : isValue e = true) :
    step e = none := by
  match e with
  | .primLit _ | .lambda _ | .ctor _ => rfl
  | .pair a b =>
    simp only [isValue, Bool.and_eq_true] at hv
    simp [step, hv.1, hv.2]
  | .app f arg =>
    simp only [isValue, Bool.and_eq_true] at hv
    simp only [step, isCtorChain_imp_isValue hv.1, hv.2, ite_true]
    cases f <;> (first | rfl | simp [isCtorChain] at hv)
  | .var _ | .letIn _ _ | .letPairIn _ _ | .match_ _ _ => simp [isValue] at hv

private theorem step_some_not_isValue {e e' : Expr}
    (h : step e = some e') : isValue e = false := by
  cases hv : isValue e with
  | false => rfl
  | true => exact absurd h (by rw [isValue_step_none hv]; nofun)

/-! ### Soundness of `step` w.r.t. the `Step` relation -/

theorem step_sound {e e' : Expr} (h : step e = some e') : Step e e' := by
  induction e using Expr.rec_strong generalizing e' with
  | primLit _ | lambda _ _ | ctor _ | var _ => simp [step] at h
  | pair a b iha ihb =>
    unfold step at h
    split at h
    · rename_i hva
      split at h
      · exact nomatch h
      · match hb : step b with
        | .none => simp [hb] at h
        | .some b' =>
          simp [hb] at h; subst h; exact .pairSnd (isValue_iff_IsValue.mp hva) (ihb hb)
    · match ha : step a with
      | .none => simp [ha] at h
      | .some a' => simp [ha] at h; subst h; exact .pairFst (iha ha)
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
  | letIn rhs body ihrhs _ =>
    unfold step at h
    split at h
    · rename_i hvrhs
      simp at h; subst h
      exact .letReduce (isValue_iff_IsValue.mp hvrhs)
    · match hrhs : step rhs with
      | .none => simp [hrhs] at h
      | .some rhs' => simp [hrhs] at h; subst h; exact .letInRhs (ihrhs hrhs)
  | letPairIn rhs body ihrhs _ =>
    unfold step at h
    split at h
    · rename_i hvrhs
      split at h
      · simp at h; subst h
        simp only [isValue, Bool.and_eq_true] at hvrhs
        exact .letPairReduce (isValue_iff_IsValue.mp hvrhs.1) (isValue_iff_IsValue.mp hvrhs.2)
      · exact nomatch h
    · match hrhs : step rhs with
      | .none => simp [hrhs] at h
      | .some rhs' => simp [hrhs] at h; subst h; exact .letPairRhs (ihrhs hrhs)
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
  | letPairReduce hv1 hv2 =>
    have := isValue_iff_IsValue.mpr hv1
    have := isValue_iff_IsValue.mpr hv2
    unfold step; simp [isValue, *]
  | matchReduce hval hctor hfirst =>
    have := isValue_iff_IsValue.mpr hval
    have := getCtorArgs_of_CtorAppliedTo hctor
    have := FirstMatch_to_findMatchingBranch hfirst rfl
    unfold step; simp [*]
  | pairFst _ ih =>
    have := step_some_not_isValue ih
    unfold step; simp [this, ih]
  | pairSnd hval _ ih =>
    have := isValue_iff_IsValue.mpr hval
    have := step_some_not_isValue ih
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
  | letPairRhs _ ih =>
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

Lambda/let/letPair/match introduce 1, 1, 2, or `pat.contents` new levels
respectively, raising the scope bound inside their body. -/

mutual

inductive Expr.WellScopedUnder : Nat → Expr → Prop
  | primLit {n p}            : Expr.WellScopedUnder n (.primLit p)
  | ctor    {n c}            : Expr.WellScopedUnder n (.ctor c)
  | var     {n i}            : i < n → Expr.WellScopedUnder n (.var i)
  | pair    {n a b}          :
      Expr.WellScopedUnder n a → Expr.WellScopedUnder n b →
      Expr.WellScopedUnder n (.pair a b)
  | lambda  {n body}       :
      Expr.WellScopedUnder (n + 1) body →
      Expr.WellScopedUnder n (.lambda body)
  | app     {n f arg}        :
      Expr.WellScopedUnder n f → Expr.WellScopedUnder n arg →
      Expr.WellScopedUnder n (.app f arg)
  | letIn   {n rhs body}   :
      Expr.WellScopedUnder n rhs →
      Expr.WellScopedUnder (n + 1) body →
      Expr.WellScopedUnder n (.letIn rhs body)
  | letPairIn {n rhs body} :
      Expr.WellScopedUnder n rhs →
      Expr.WellScopedUnder (n + 2) body →
      Expr.WellScopedUnder n (.letPairIn rhs body)
  | match_  {n scrut branches} :
      Expr.WellScopedUnder n scrut →
      Expr.BranchListWellScoped n branches →
      Expr.WellScopedUnder n (.match_ scrut branches)

inductive Expr.BranchListWellScoped : Nat → List (MatchPattern × Expr) → Prop
  | nil  {n}          : Expr.BranchListWellScoped n []
  | cons {n pat body rest} :
      Expr.WellScopedUnder (n + pat.contents) body →
      Expr.BranchListWellScoped n rest →
      Expr.BranchListWellScoped n ((pat, body) :: rest)

end


/-- Instantation doesn't add more bvars than are in `tyArgs` -/
theorem InstantiatesBy.preserves_bvars : (∀ tyArg ∈ tyArgs, ContainsBvarsUpTo 0 tyArg) → InstantiatesBy tyArgs polyTy ty → ContainsBvarsUpTo 0 ty := by
  intro prem hinst
  cases hinst with
  | prim => constructor
  | pair a b
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
private theorem Env.mem_freeVars_iff {env : Env} {x : Nat} :
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

/-- If every polytype in `l₁` appears in `l₂`, then `l₁`'s freeVars are a
    subset of `l₂`'s freeVars. -/
private theorem Env.freeVars_subset_of_subset {l₁ l₂ : Env}
    (h : ∀ pt ∈ l₁, pt ∈ l₂) :
    l₁.freeVars ⊆ l₂.freeVars := by
  intro x hx
  rw [Env.mem_freeVars_iff] at hx ⊢
  obtain ⟨pt, hpt_mem, hpt_x⟩ := hx
  exact ⟨pt, h pt hpt_mem, hpt_x⟩

/-- Inserting an extra polytype between two halves of an env can only grow its
    freeVars. -/
private theorem Env.freeVars_subset_insert_middle
    (l₁ l₃ : Env) (pt : PolyTy) :
    (l₁ ++ l₃).freeVars ⊆ (l₁ ++ [pt] ++ l₃).freeVars := by
  apply Env.freeVars_subset_of_subset
  intro pt' hpt'
  simp only [List.mem_append, List.mem_singleton] at hpt' ⊢
  tauto

/-- Inserting an env-block with no freeVars between two halves doesn't change
    the freeVars (set-wise): they're equal subsets of each other. We only need
    one direction here. -/
private theorem Env.freeVars_subset_append_left (l₁ l₂ : Env) :
    l₂.freeVars ⊆ (l₁ ++ l₂).freeVars := by
  intro x hx
  rw [Env.mem_freeVars_iff] at hx ⊢
  obtain ⟨pt, hpt_mem, hpt_x⟩ := hx
  exact ⟨pt, List.mem_append_right _ hpt_mem, hpt_x⟩

private theorem Env.freeVars_subset_insert_closed_middle
    {env l₂ l₃ : Env} (h_l₂ : l₂.freeVars ⊆ (env ++ l₃).freeVars) :
    (env ++ l₂ ++ l₃).freeVars ⊆ (env ++ l₃).freeVars := by
  intro x hx
  rw [Env.mem_freeVars_iff] at hx ⊢
  obtain ⟨pt, hpt_mem, hpt_x⟩ := hx
  simp only [List.mem_append] at hpt_mem
  rcases hpt_mem with (hpre | hmid) | hpost
  · exact ⟨pt, by simp only [List.mem_append]; tauto, hpt_x⟩
  · have h_in_l₂ : x ∈ l₂.freeVars := by
      rw [Env.mem_freeVars_iff]; exact ⟨pt, hmid, hpt_x⟩
    exact Env.mem_freeVars_iff.mp (h_l₂ h_in_l₂)
  · exact ⟨pt, by simp only [List.mem_append]; tauto, hpt_x⟩


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
  | pair :
    AllMatchesExhaustive ctors a → AllMatchesExhaustive ctors b →
    AllMatchesExhaustive ctors (.pair a b)
  | lambda :
    AllMatchesExhaustive ctors body →
    AllMatchesExhaustive ctors (.lambda body)
  | app :
    AllMatchesExhaustive ctors f → AllMatchesExhaustive ctors arg →
    AllMatchesExhaustive ctors (.app f arg)
  | letIn :
    AllMatchesExhaustive ctors rhs → AllMatchesExhaustive ctors body →
    AllMatchesExhaustive ctors (.letIn rhs body)
  | letPairIn :
    AllMatchesExhaustive ctors rhs → AllMatchesExhaustive ctors body →
    AllMatchesExhaustive ctors (.letPairIn rhs body)
  /-- Exhaustiveness for match: every constructor in the ctor env whose type
      matches `tyName` has a corresponding branch. The `tyName` is existentially
      quantified — the caller picks it (typically from the typing derivation) —
      but it is pinned to the branches: every branch's pattern must be a
      constructor of `tyName`, so a bogus ctor-less type cannot be chosen. -/
  | match_ {tyName : TyName} :
    AllMatchesExhaustive ctors scrut →
    AllBranchBodiesExhaustive ctors branches →
    (∀ pat body, (pat, body) ∈ branches →
       ∃ ctor, LookupList.get? ctors pat.ctor = some ctor ∧ ctor.tyName = tyName) →
    (∀ (ctorName : CtorName) (ctor : Ctor),
      LookupList.get? ctors ctorName = some ctor →
      ctor.tyName = tyName →
      ∃ pat body, (pat, body) ∈ branches ∧ pat.ctor = ctorName ∧
        pat.contents = ctor.contents.length) →
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
    (h : ∃ pat body, (pat, body) ∈ branches ∧ pat.ctor = name ∧
         pat.contents = args.length) :
    ∃ e', findMatchingBranch name args branches = some e' := by
  induction branches with
  | nil => obtain ⟨_, _, hmem, _⟩ := h; exact nomatch hmem
  | cons hd tl ih =>
    obtain ⟨pat, body, hmem, hctor, harity⟩ := h
    unfold findMatchingBranch
    split
    · exact ⟨_, rfl⟩
    · rename_i hnm
      cases hmem with
      | head _ => exact absurd (And.intro hctor harity) hnm
      | tail _ hmem' => exact ih ⟨pat, body, hmem', hctor, harity⟩


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
*type*-side cofinite quantification (in `letIn`/`letPairIn`) remains.

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
  | .pair a b        => .pair (Ty.substFvar Z U a) (Ty.substFvar Z U b)
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

Syntax-directed Hindley–Milner typing. All rules are standard except the two
let-generalising rules (`letIn`, `letPairIn`), which use a **cofinite**
"for-all-fresh" premise to express generalisation (see the module doc above):

```
  PolyTy.WF M →
  (∀ Xs, FreshNames L M.paramCount Xs → TypeOfHM ctx boundExpr (M.openVars Xs)) →
  bodyCtx = { ctx with env := M :: ctx.env } →
  TypeOfHM bodyCtx body bodyTy →
  TypeOfHM ctx (.letIn boundExpr body) bodyTy
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

  | primLitBool :
    TypeOfHM ctx (.primLit (.bool b)) (.prim .bool)

  | primLitStr :
    TypeOfHM ctx (.primLit (.str s)) (.prim .str)

  | pair :
    TypeOfHM ctx fst fstTy →
    TypeOfHM ctx snd sndTy →
    TypeOfHM ctx (.pair fst snd) (.pair fstTy sndTy)

  | lambda :
    ContainsBvarsUpTo 0 paramTy →
    bodyCtx = { ctx with env := PolyTy.mkTrivial paramTy :: ctx.env } →
    TypeOfHM bodyCtx body bodyTy →
    TypeOfHM ctx (.lambda body) (.arrow paramTy bodyTy)

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
    (∀ Xs : List Nat, FreshNames L M.paramCount Xs →
        TypeOfHM ctx boundExpr (M.openVars Xs)) →
    bodyCtx = { ctx with env := M :: ctx.env } →
    TypeOfHM bodyCtx body bodyTy →
    TypeOfHM ctx (.letIn boundExpr body) bodyTy

  /-- Cofinite pair-let-generalisation. The two component schemes share an
      arity and are opened with a *shared* fresh list `Xs` — this is the price
      of cofinite encoding: a type variable common to both halves of the pair
      must be renamed consistently (the type-substitution lemma renames a var
      everywhere at once). The old lax `Generalise` allowed fully independent
      generalisation of the two halves; that esoteric freedom is given up
      here. (No value restriction, as in `letIn`.) -/
  | letPairIn {Mfst Msnd : PolyTy} {L : List Nat} :
    PolyTy.WF Mfst →
    PolyTy.WF Msnd →
    Mfst.paramCount = Msnd.paramCount →
    (∀ Xs : List Nat, FreshNames L Mfst.paramCount Xs →
        TypeOfHM ctx boundExpr (.pair (Mfst.openVars Xs) (Msnd.openVars Xs))) →
    bodyCtx = { ctx with env := Msnd :: Mfst :: ctx.env } →
    TypeOfHM bodyCtx body bodyTy →
    TypeOfHM ctx (.letPairIn boundExpr body) bodyTy

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
  | mk {ctor : Ctor} {ctx : Ctx} {pattern : MatchPattern} :
    LookupList.get? ctx.ctors pattern.ctor = some ctor →
    ctor.tyName = tyName →
    ctor.paramCount = tyArgs.length →
    pattern.contents = ctor.contents.length →
    List.Forall₂ (InstantiatesBy tyArgs) ctor.contents instContents →
    patternBindings = instContents.map PolyTy.mkTrivial →
    bodyCtx = {ctx with env := patternBindings ++ ctx.env} →
    TypeOfHM bodyCtx bodyExpr resultTy →
    TypeOfMatchBranch ctx (pattern, bodyExpr) tyName tyArgs resultTy

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
private theorem TyList.not_mem_freeVars_iff {Z : Nat} {tys : List Ty} :
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
  | pair a b ih_a ih_b =>
    simp only [Ty.freeVars, List.mem_dedup, List.mem_append, not_or] at h
    simp only [Ty.substFvar, Ty.pair.injEq]
    exact ⟨ih_a h.1, ih_b h.2⟩
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
  | pair a b ih_a ih_b =>
    cases h with
    | pair h_a h_b =>
      simp only [Ty.instantiate, Ty.pair.injEq]
      exact ⟨ih_a h_a, ih_b h_b⟩
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
  | pair a b ih_a ih_b =>
    simp only [Ty.instantiate, Ty.substFvar, Ty.pair.injEq]
    exact ⟨ih_a, ih_b⟩
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

/-- Free vars of a list of types (used in `openWith_eq_substFvars_openVars`'s
    freshness condition). -/
def Ty.freeVarsList : List Ty → List Nat
  | []       => []
  | hd :: tl => (hd.freeVars ++ Ty.freeVarsList tl).dedup

/-- Opening with anything is a no-op on locally-closed types: nothing to
    instantiate (no bvars to replace). -/
theorem Ty.openWith_eq_self_of_lc {Vs : List Ty} {ty : Ty}
    (h : Ty.IsLC ty) : Ty.openWith Vs ty = ty :=
  Ty.instantiate_eq_self_of_lc h

/-- `substFvar` commutes with `openWith` when the replacement is LC.
    Direct corollary: opening then substituting equals substituting (in both
    body and the args list) then opening. -/
private theorem TyList.substFvar_openWith_swap
    {Z : Nat} {U : Ty} {Vs : List Ty} {tys : List Ty}
    (ih : ∀ t ∈ tys,
            Ty.substFvar Z U (Ty.openWith Vs t)
              = Ty.openWith (Vs.map (Ty.substFvar Z U)) (Ty.substFvar Z U t)) :
    TyList.substFvar Z U (TyList.instantiate (fun i => Vs[i]?.getD (.bvar i)) tys)
      = TyList.instantiate (fun i => (Vs.map (Ty.substFvar Z U))[i]?.getD (.bvar i))
          (TyList.substFvar Z U tys) := by
  induction tys with
  | nil => rfl
  | cons hd tl ih_tl =>
    simp only [TyList.substFvar, TyList.instantiate, List.cons.injEq]
    refine ⟨ih hd List.mem_cons_self, ?_⟩
    exact ih_tl (fun t ht => ih t (List.mem_cons_of_mem _ ht))

theorem Ty.substFvar_openWith
    {Z : Nat} {U ty : Ty} {Vs : List Ty}
    (h_U_lc : Ty.IsLC U) :
    Ty.substFvar Z U (Ty.openWith Vs ty)
      = Ty.openWith (Vs.map (Ty.substFvar Z U)) (Ty.substFvar Z U ty) := by
  unfold Ty.openWith
  induction ty using Ty.rec_strong with
  | prim _ => rfl
  | pair _ _ ih_a ih_b =>
    simp only [Ty.instantiate, Ty.substFvar, Ty.pair.injEq]
    exact ⟨ih_a, ih_b⟩
  | arrow _ _ ih_a ih_b =>
    simp only [Ty.instantiate, Ty.substFvar, Ty.arrow.injEq]
    exact ⟨ih_a, ih_b⟩
  | bvar i =>
    simp only [Ty.instantiate, Ty.substFvar, List.getElem?_map]
    cases h_vs : Vs[i]? with
    | none => simp [Ty.substFvar]
    | some v => simp
  | fvar n =>
    simp only [Ty.instantiate, Ty.substFvar]
    by_cases h_n : n = Z
    · simp only [if_pos h_n]
      exact (Ty.instantiate_eq_self_of_lc h_U_lc).symm
    · simp only [if_neg h_n, Ty.instantiate]
  | customTy _ tys ih =>
    simp only [Ty.instantiate, Ty.substFvar, Ty.customTy.injEq, true_and]
    exact TyList.substFvar_openWith_swap (fun t ht => ih t ht)

/-! #### `substFvars` distribution + key lemmas (toward `typ_substs_intro`). -/

private theorem TyList.substFvar_eq_map {Z : Nat} {U : Ty} {tys : List Ty} :
    TyList.substFvar Z U tys = tys.map (Ty.substFvar Z U) := by
  induction tys with
  | nil => rfl
  | cons hd tl ih => simp only [TyList.substFvar, List.map_cons, ih]

private theorem TyList.instantiate_eq_map {σ : Nat → Ty} {tys : List Ty} :
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

theorem Ty.substFvars_pair {pairs : List (Nat × Ty)} {a b : Ty} :
    Ty.substFvars pairs (.pair a b)
      = .pair (Ty.substFvars pairs a) (Ty.substFvars pairs b) := by
  induction pairs generalizing a b with
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
private theorem TyList.mem_freeVars_of_mem {t : Ty} {tys : List Ty} {x : Nat}
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
  | pair a b ih_a ih_b =>
    simp only [Ty.instantiate]
    rw [Ty.substFvars_pair]
    have ha : ∀ X ∈ Xs, X ∉ a.freeVars := fun X hX hc =>
      h_Xs_fresh_ty X hX (by simp only [Ty.freeVars, List.mem_dedup, List.mem_append]; exact .inl hc)
    have hb : ∀ X ∈ Xs, X ∉ b.freeVars := fun X hX hc =>
      h_Xs_fresh_ty X hX (by simp only [Ty.freeVars, List.mem_dedup, List.mem_append]; exact .inr hc)
    rw [ih_a ha, ih_b hb]
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


/-! ### `substFvar` interaction with the typing-side predicates.

Helpers needed by `typ_subst_preservation`. -/

/-- `substFvar` by an LC type preserves local-closedness. (The `bvar` case is
    vacuous: an LC type has no bvars.) -/
theorem Ty.IsLC.substFvar {Z : Nat} {U ty : Ty}
    (h_U : Ty.IsLC U) (h : Ty.IsLC ty) :
    Ty.IsLC (Ty.substFvar Z U ty) := by
  induction ty using Ty.rec_strong with
  | prim _ => exact .prim
  | pair a b iha ihb => cases h with | pair ha hb => exact .pair (iha ha) (ihb hb)
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
  | pair a b iha ihb => cases h with | pair ha hb => exact .pair (iha ha) (ihb hb)
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
  | pair a b iha ihb =>
    cases h with | pair ha hb => exact .pair (iha ha) (ihb hb)
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
  | pair _ _ iha ihb => exact .pair iha ihb
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
  | pair a b iha ihb => cases h with | pair ha hb => exact .pair (iha ha) (ihb hb)
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
  | pair _ _ iha ihb =>
    simp only [Ty.freeVars, List.mem_dedup, List.mem_append, not_or]; exact ⟨iha, ihb⟩
  | arrow _ _ iha ihb =>
    simp only [Ty.freeVars, List.mem_dedup, List.mem_append, not_or]; exact ⟨iha, ihb⟩
  | bvar => simp [Ty.freeVars]
  | customTy _ ih =>
    simp only [Ty.freeVars]
    exact TyList.not_mem_freeVars_iff.mpr (fun t ht => ih t ht)

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


/-! ### Metatheory infrastructure. -/

/-- Type-substitution preserves typing. Substituting a single fresh type
    variable `Z` (one not appearing in the outer env) by any LC type `U`
    preserves the typing derivation.

    Chargueraud's `typing_typ_subst`. -/
theorem TypeOfHM.typ_subst_preservation
    {ctors : CtorEnv} {env_post env_outer : Env}
    {e : Expr} {τ : Ty} {Z : Nat} {U : Ty}
    (h_Z_fresh_outer : Z ∉ env_outer.freeVars)
    (h_U_lc : U.IsLC)
    (h : TypeOfHM ⟨env_post ++ env_outer, ctors⟩ e τ) :
    TypeOfHM ⟨env_post.substFvar Z U ++ env_outer, ctors⟩ e (Ty.substFvar Z U τ) := by
  induction e using Expr.rec_strong generalizing env_post τ with
  | primLit p =>
    cases h with
    | primLitUnit => exact .primLitUnit
    | primLitInt  => exact .primLitInt
    | primLitNat  => exact .primLitNat
    | primLitBool => exact .primLitBool
    | primLitStr  => exact .primLitStr
  | pair a b ih_a ih_b =>
    cases h with
    | pair ha hb =>
      simp only [Ty.substFvar]
      exact .pair (ih_a ha) (ih_b hb)
  | app f inp ih_f ih_i =>
    cases h with
    | app hf hi =>
      have hf' := ih_f hf
      simp only [Ty.substFvar] at hf'
      exact .app hf' (ih_i hi)
  | lambda body ih =>
    cases h with
    | lambda hparamLC heq hbody =>
      subst heq
      simp only [Ty.substFvar]
      refine TypeOfHM.lambda (Ty.IsLC.substFvar h_U_lc hparamLC) rfl ?_
      have hb := ih (env_post := PolyTy.mkTrivial _ :: env_post) hbody
      simpa only [Env.substFvar, List.map_cons, PolyTy.substFvar, PolyTy.mkTrivial,
        List.cons_append] using hb
  | var dbl =>
    cases h with
    | var hlook htyargs hinst =>
      have hlook' := congrArg (Option.map (PolyTy.substFvar Z U)) hlook
      simp only [Option.map_some] at hlook'
      rw [← List.getElem?_map] at hlook'
      have henv : env_post.substFvar Z U ++ env_outer
          = (env_post ++ env_outer).map (PolyTy.substFvar Z U) := by
        show Env.substFvar Z U env_post ++ env_outer
          = Env.substFvar Z U (env_post ++ env_outer)
        rw [Env.substFvar_append, Env.substFvar_fresh h_Z_fresh_outer]
      rw [← henv] at hlook'
      refine TypeOfHM.var hlook' ?_ (InstantiatesBy.substFvar h_U_lc hinst)
      intro tyArg hmem
      obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hmem
      exact Ty.IsLC.substFvar h_U_lc (htyargs t ht)
  | letIn boundExpr body ih_be ih_body =>
    cases h with
    | letIn hsch hcofin heq hbodyinner =>
      subst heq
      expose_names
      refine TypeOfHM.letIn (M := PolyTy.substFvar Z U M) (L := Z :: L)
        (PolyTy.WF.substFvar h_U_lc hsch) ?_ rfl ?_
      · intro Xs hfresh
        have hZ_notin : Z ∉ Xs := fun hc => hfresh.avoid Z hc List.mem_cons_self
        have hXs_freshL : FreshNames L M.paramCount Xs :=
          ⟨by simpa using hfresh.length, hfresh.nodup,
           fun x hx hc => hfresh.avoid x hx (List.mem_cons_of_mem _ hc)⟩
        have hbe := ih_be (hcofin Xs hXs_freshL)
        have hopen : (M.substFvar Z U).openVars Xs = Ty.substFvar Z U (M.openVars Xs) := by
          unfold PolyTy.openVars PolyTy.substFvar
          exact (Ty.substFvar_openVars h_U_lc hZ_notin).symm
        rw [hopen]
        exact hbe
      · have hb := ih_body (env_post := M :: env_post) hbodyinner
        simpa only [Env.substFvar, List.map_cons, List.cons_append] using hb
  | letPairIn pe body ih_pe ih_body =>
    cases h with
    | letPairIn hschf hschs harity hcofin heq hbodyinner =>
      subst heq
      expose_names
      refine TypeOfHM.letPairIn (Mfst := PolyTy.substFvar Z U Mfst)
        (Msnd := PolyTy.substFvar Z U Msnd) (L := Z :: L)
        (PolyTy.WF.substFvar h_U_lc hschf)
        (PolyTy.WF.substFvar h_U_lc hschs) harity ?_ rfl ?_
      · intro Xs hfresh
        have hZ_notin : Z ∉ Xs := fun hc => hfresh.avoid Z hc List.mem_cons_self
        have hXs_freshL : FreshNames L Mfst.paramCount Xs :=
          ⟨by simpa using hfresh.length, hfresh.nodup,
           fun x hx hc => hfresh.avoid x hx (List.mem_cons_of_mem _ hc)⟩
        have hpe := ih_pe (hcofin Xs hXs_freshL)
        have hopenf : (Mfst.substFvar Z U).openVars Xs
            = Ty.substFvar Z U (Mfst.openVars Xs) := by
          unfold PolyTy.openVars PolyTy.substFvar
          exact (Ty.substFvar_openVars h_U_lc hZ_notin).symm
        have hopens : (Msnd.substFvar Z U).openVars Xs
            = Ty.substFvar Z U (Msnd.openVars Xs) := by
          unfold PolyTy.openVars PolyTy.substFvar
          exact (Ty.substFvar_openVars h_U_lc hZ_notin).symm
        simp only [Ty.substFvar] at hpe
        rw [hopenf, hopens]
        exact hpe
      · have hb := ih_body (env_post := Msnd :: Mfst :: env_post) hbodyinner
        simpa only [Env.substFvar, List.map_cons, List.cons_append] using hb
  | ctor name =>
    cases h with
    | ctor hlook htyargs hinst =>
      expose_names
      have hbody := InstantiatesBy.substFvar (Z := Z) (U := U) h_U_lc hinst
      rw [Ty.substFvar_fresh
          (NoFreeVars.not_mem_freeVars (Ctor.toTy_body_noFreeVars ctor) Z)] at hbody
      refine TypeOfHM.ctor hlook ?_ hbody
      intro tyArg hmem
      obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hmem
      exact Ty.IsLC.substFvar h_U_lc (htyargs t ht)
  | match_ scrut branches ih_scrut ih_branches =>
    cases h with
    | match_ hscrut hne hbrs =>
      have hscrut' := ih_scrut hscrut
      simp only [Ty.substFvar, TyList.substFvar_eq_map] at hscrut'
      refine TypeOfHM.match_ hscrut' hne ?_
      clear ih_scrut hscrut hscrut' hne
      revert hbrs ih_branches
      induction branches with
      | nil =>
        intro _ _ b hmem
        exact absurd hmem List.not_mem_nil
      | cons hd tl ih_tl =>
        intro ih_branches hbrs branch hmem
        obtain ⟨pat, body⟩ := hd
        simp only [List.mem_cons] at hmem
        cases hmem with
        | inl heq =>
          subst heq
          have hbranch := hbrs (pat, body) List.mem_cons_self
          cases hbranch with
          | mk hlook htyName hpc hcontents hinstC hpb hctx hbodyT =>
            subst hctx; subst hpb
            expose_names
            -- ctor.contents are closed, so substFvar leaves them fixed
            have hcc : ctor.contents.map (Ty.substFvar Z U) = ctor.contents := by
              have hpt : ∀ c ∈ ctor.contents, Ty.substFvar Z U c = id c := fun c hc =>
                Ty.substFvar_fresh ((ctor.closed c hc).not_mem_freeVars Z)
              rw [List.map_congr_left hpt, List.map_id]
            have hinstC' := InstantiatesBy.forall2_substFvar (Z := Z) (U := U) h_U_lc hinstC
            rw [hcc] at hinstC'
            -- recurse on the branch body (reassociate env first)
            rw [show instContents.map PolyTy.mkTrivial ++ (env_post ++ env_outer)
                  = (instContents.map PolyTy.mkTrivial ++ env_post) ++ env_outer
                  from (List.append_assoc _ _ _).symm] at hbodyT
            have hib := ih_branches pat body List.mem_cons_self
              (env_post := instContents.map PolyTy.mkTrivial ++ env_post) hbodyT
            rw [Env.substFvar_append, Env.substFvar_map_mkTrivial,
                List.append_assoc] at hib
            exact TypeOfMatchBranch.mk hlook htyName (by simpa using hpc)
              hcontents hinstC' rfl rfl hib
        | inr hmem' =>
          exact ih_tl
            (fun pat' e' hm => ih_branches pat' e' (List.mem_cons_of_mem _ hm))
            (fun b hm => hbrs b (List.mem_cons_of_mem _ hm))
            branch hmem'

/- Values are preserved under `shiftFrom` (it only renumbers free term vars,
   leaving the value shape intact). Mutual with `IsCtorChain.shiftFrom`. -/
mutual
theorem SmallStep.IsValue.shiftFrom {e : Expr} (k n : Nat)
    (h : SmallStep.IsValue e) : SmallStep.IsValue (e.shiftFrom k n) := by
  cases h with
  | primLit p => exact .primLit p
  | lambda body => exact .lambda _
  | pair h1 h2 => exact .pair (h1.shiftFrom k n) (h2.shiftFrom k n)
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
    condition. This goes through precisely because the cofinite `letIn`/
    `letPairIn` rules let us grow the exclusion set `L` to dodge `env_extra`'s
    type vars on the fly inside the IH.

    Chargueraud's `typing_weaken`. -/
theorem TypeOfHM.weaken_env
    {ctors : CtorEnv} {env_pre env_extra env : Env} {e : Expr} {τ : Ty}
    (h : TypeOfHM ⟨env_pre ++ env, ctors⟩ e τ) :
    TypeOfHM ⟨env_pre ++ env_extra ++ env, ctors⟩
      (e.shiftFrom env_pre.length env_extra.length) τ := by
  induction e using Expr.rec_strong generalizing env_pre τ with
  | primLit p =>
    cases h with
    | primLitUnit => exact .primLitUnit
    | primLitInt  => exact .primLitInt
    | primLitNat  => exact .primLitNat
    | primLitBool => exact .primLitBool
    | primLitStr  => exact .primLitStr
  | pair a b ih_a ih_b =>
    cases h with
    | pair ha hb =>
      simp only [Expr.shiftFrom]
      exact .pair (ih_a ha) (ih_b hb)
  | app f inp ih_f ih_i =>
    cases h with
    | app hf hi =>
      simp only [Expr.shiftFrom]
      exact .app (ih_f hf) (ih_i hi)
  | var i =>
    cases h with
    | var h_lookup h_tyArgs_closed h_inst =>
      simp only [Expr.shiftFrom]
      by_cases h_lt : i < env_pre.length
      · rw [if_pos h_lt]
        refine .var ?_ h_tyArgs_closed h_inst
        show (env_pre ++ env_extra ++ env)[i]? = _
        rw [List.getElem?_append_left
              (by simp only [List.length_append]; omega :
                  i < (env_pre ++ env_extra).length)]
        rw [List.getElem?_append_left h_lt]
        have h_lookup' : (env_pre ++ env)[i]? = _ := h_lookup
        rw [List.getElem?_append_left h_lt] at h_lookup'
        exact h_lookup'
      · push_neg at h_lt
        rw [if_neg (Nat.not_lt.mpr h_lt)]
        refine .var ?_ h_tyArgs_closed h_inst
        show (env_pre ++ env_extra ++ env)[i + env_extra.length]? = _
        have h_left : (env_pre ++ env_extra).length ≤ i + env_extra.length := by
          simp only [List.length_append]; omega
        rw [List.getElem?_append_right h_left]
        have h_eq_idx :
            i + env_extra.length - (env_pre ++ env_extra).length
            = i - env_pre.length := by
          simp only [List.length_append]; omega
        rw [h_eq_idx]
        have h_lookup' : (env_pre ++ env)[i]? = _ := h_lookup
        rw [List.getElem?_append_right h_lt] at h_lookup'
        exact h_lookup'
  | lambda body ih =>
    cases h with
    | lambda h_paramTy_closed h_eq h_body_lam =>
      subst h_eq
      simp only [Expr.shiftFrom]
      refine TypeOfHM.lambda h_paramTy_closed rfl ?_
      exact ih (env_pre := PolyTy.mkTrivial _ :: env_pre) h_body_lam
  | letIn boundExpr body ih_be ih_body =>
    cases h with
    | letIn hsch hcofin heq hbodyinner =>
      subst heq
      expose_names
      simp only [Expr.shiftFrom]
      refine TypeOfHM.letIn (M := M) (L := L) hsch ?_ rfl ?_
      · intro Xs hfresh
        exact ih_be (hcofin Xs hfresh)
      · exact ih_body (env_pre := M :: env_pre) hbodyinner
  | letPairIn pe body ih_pe ih_body =>
    cases h with
    | letPairIn hschf hschs harity hcofin heq hbodyinner =>
      subst heq
      expose_names
      simp only [Expr.shiftFrom]
      refine TypeOfHM.letPairIn (Mfst := Mfst) (Msnd := Msnd) (L := L)
        hschf hschs harity ?_ rfl ?_
      · intro Xs hfresh
        exact ih_pe (hcofin Xs hfresh)
      · exact ih_body (env_pre := Msnd :: Mfst :: env_pre) hbodyinner
  | ctor name =>
    cases h with
    | ctor hlook htyargs hinst =>
      exact .ctor hlook htyargs hinst
  | match_ scrutinee branches ihs ihbs =>
    cases h with
    | match_ h_scrut h_ne h_brs =>
      simp only [Expr.shiftFrom]
      have h_shift_nonempty :
          BranchList.shiftFrom env_pre.length env_extra.length branches ≠ [] := by
        intro h_eq
        cases branches with
        | nil => exact h_ne rfl
        | cons _ _ => simp [BranchList.shiftFrom] at h_eq
      refine TypeOfHM.match_ (ihs h_scrut) h_shift_nonempty ?_
      clear ihs h_scrut h_ne h_shift_nonempty
      revert h_brs ihbs
      induction branches with
      | nil =>
        intro _ _ b h_mem
        simp [BranchList.shiftFrom] at h_mem
      | cons hd tl ih_tl =>
        intro ihbs h_brs branch h_mem
        obtain ⟨pat, body⟩ := hd
        simp only [BranchList.shiftFrom, List.mem_cons] at h_mem
        cases h_mem with
        | inl h_eq =>
          subst h_eq
          have h_branch := h_brs (pat, body) List.mem_cons_self
          cases h_branch with
          | mk h_lookup h_tyName h_paramCount h_contents h_inst h_pb h_ctx h_body =>
            subst h_ctx
            subst h_pb
            expose_names
            rw [show (instContents.map PolyTy.mkTrivial ++ (env_pre ++ env))
                  = (instContents.map PolyTy.mkTrivial ++ env_pre) ++ env
                  from (List.append_assoc _ _ _).symm] at h_body
            have ih_body :=
              ihbs pat body List.mem_cons_self
                (env_pre := instContents.map PolyTy.mkTrivial ++ env_pre)
                h_body
            simp only [List.length_append, List.length_map] at ih_body
            rw [← h_inst.length_eq, ← h_contents] at ih_body
            rw [show pat.contents + env_pre.length = env_pre.length + pat.contents
                  from Nat.add_comm _ _] at ih_body
            refine TypeOfMatchBranch.mk h_lookup h_tyName h_paramCount h_contents
              h_inst rfl rfl ?_
            rw [List.append_assoc, List.append_assoc] at ih_body
            rw [show env_pre ++ env_extra ++ env = env_pre ++ (env_extra ++ env)
                  from List.append_assoc _ _ _]
            exact ih_body
        | inr h_mem' =>
          exact ih_tl
            (fun pat' e' hmem => ihbs pat' e' (List.mem_cons_of_mem _ hmem))
            (fun branch hmem => h_brs branch (List.mem_cons_of_mem _ hmem))
            branch h_mem'

/-- Iterated type substitution preserves typing: substituting each `(Zᵢ, Uᵢ)`
    in turn (with every `Zᵢ` fresh for the env and every `Uᵢ` locally closed)
    preserves the derivation. Chargueraud's `typing_typ_substs`. -/
theorem TypeOfHM.typ_substs_preservation {ctx : Ctx} {e : Expr}
    (pairs : List (Nat × Ty))
    (h_fresh : ∀ p ∈ pairs, p.1 ∉ ctx.env.freeVars)
    (h_lc : ∀ p ∈ pairs, Ty.IsLC p.2)
    {τ : Ty} (h : TypeOfHM ctx e τ) :
    TypeOfHM ctx e (Ty.substFvars pairs τ) := by
  induction pairs generalizing τ with
  | nil => exact h
  | cons hd tl ih =>
    obtain ⟨Z, U⟩ := hd
    simp only [Ty.substFvars]
    refine ih (fun p hp => h_fresh p (List.mem_cons_of_mem _ hp))
              (fun p hp => h_lc p (List.mem_cons_of_mem _ hp)) ?_
    have hZ : Z ∉ ctx.env.freeVars := h_fresh (Z, U) List.mem_cons_self
    have hU : Ty.IsLC U := h_lc (Z, U) List.mem_cons_self
    exact TypeOfHM.typ_subst_preservation (env_post := []) (env_outer := ctx.env)
      (ctors := ctx.ctors) hZ hU h

/-- Every element of a list is `≤` its `max`-fold. -/
private theorem List.le_foldr_max {a : Nat} {l : List Nat}
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

/-- The bridge: a cofinite-vars witness gives a "for-all-instances" witness.
    Chargueraud's `has_scheme_from_vars`. For any `Vs`, pick `Xs` fresh for
    everything relevant, use the cofinite witness at `Xs`, then iteratively
    `typ_subst_preservation`-substitute each `Xᵢ ↦ Vᵢ` (the
    `openWith = substFvars ∘ openVars` identity bridges the two openings). -/
theorem HasScheme.fromHasSchemeVars
    {L : List Nat} {ctx : Ctx} {e : Expr} {M : PolyTy}
    (h : HasSchemeVars L ctx e M) :
    HasScheme ctx e M := by
  intro Vs hVs
  obtain ⟨hVlen, hVlc⟩ := hVs
  obtain ⟨Xs, hXlen, hXnodup, hXavoid⟩ :=
    exists_fresh_names
      (L ++ M.body.freeVars ++ Ty.freeVarsList Vs ++ ctx.env.freeVars) M.paramCount
  -- split the combined freshness into its four parts
  have hX_L : ∀ x ∈ Xs, x ∉ L := fun x hx hc =>
    hXavoid x hx (by simp only [List.mem_append]; tauto)
  have hX_Mbody : ∀ x ∈ Xs, x ∉ M.body.freeVars := fun x hx hc =>
    hXavoid x hx (by simp only [List.mem_append]; tauto)
  have hX_Vs : ∀ x ∈ Xs, x ∉ Ty.freeVarsList Vs := fun x hx hc =>
    hXavoid x hx (by simp only [List.mem_append]; tauto)
  have hX_env : ∀ x ∈ Xs, x ∉ ctx.env.freeVars := fun x hx hc =>
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
  refine TypeOfHM.typ_substs_preservation (Xs.zip Vs) ?_ ?_ hwit
  · intro p hp
    exact hX_env p.1 (List.of_mem_zip hp).1
  · intro p hp
    exact hVlc p.2 (List.of_mem_zip hp).2

/-- Instantiation with the "identity on bvars" substitution is a no-op. Used
    in `HasScheme.ofTypeOfHM` to show that opening an arity-0 scheme with the
    empty arg list returns the underlying type unchanged. -/
private theorem Ty.instantiate_bvar_id {ty : Ty} :
    Ty.instantiate (fun i => .bvar i) ty = ty := by
  induction ty using Ty.rec_strong with
  | prim _ => rfl
  | pair _ _ ih_a ih_b =>
    simp only [Ty.instantiate, Ty.pair.injEq]; exact ⟨ih_a, ih_b⟩
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
  | lambda body => exact .lambda _
  | pair h1 h2 => exact .pair (h1.substN k vs) (h2.substN k vs)
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
  | pair a b iha ihb =>
    cases h_bv with
    | pair hba hbb =>
      cases h with
      | pair ha hb =>
        simp only [Ty.openWith, Ty.instantiate] at *
        rw [iha ha hba, ihb hb hbb]
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
    (h_v : HasScheme ⟨env, ctors⟩ v M) :
    TypeOfHM ⟨env_post ++ env, ctors⟩
      (e.substN env_post.length [v]) τ := by
  induction e using Expr.rec_strong generalizing env_post τ with
  | primLit p =>
    cases h_body with
    | primLitUnit => exact .primLitUnit
    | primLitInt  => exact .primLitInt
    | primLitNat  => exact .primLitNat
    | primLitBool => exact .primLitBool
    | primLitStr  => exact .primLitStr
  | pair a b ih_a ih_b =>
    cases h_body with
    | pair ha hb =>
      simp only [Expr.substN]
      exact .pair (ih_a ha) (ih_b hb)
  | app f inp ih_f ih_i =>
    cases h_body with
    | app hf hi =>
      simp only [Expr.substN]
      exact .app (ih_f hf) (ih_i hi)
  | lambda body ih =>
    cases h_body with
    | lambda hpc heq hbody =>
      subst heq
      simp only [Expr.substN]
      refine TypeOfHM.lambda hpc rfl ?_
      exact ih (env_post := PolyTy.mkTrivial _ :: env_post) hbody
  | letIn boundExpr body ih_be ih_body =>
    cases h_body with
    | letIn hsch hcofin heq hbodyinner =>
      subst heq
      simp only [Expr.substN]
      refine TypeOfHM.letIn hsch
        (fun Xs hfresh => ih_be (hcofin Xs hfresh)) rfl ?_
      exact ih_body (env_post := _ :: env_post) hbodyinner
  | letPairIn pe body ih_pe ih_body =>
    cases h_body with
    | letPairIn hschf hschs harity hcofin heq hbodyinner =>
      subst heq
      simp only [Expr.substN]
      refine TypeOfHM.letPairIn hschf hschs harity
        (fun Xs hfresh => ih_pe (hcofin Xs hfresh)) rfl ?_
      exact ih_body (env_post := _ :: _ :: env_post) hbodyinner
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
    cases h_body with
    | match_ h_scrut h_ne h_brs =>
      simp only [Expr.substN]
      have h_subst_nonempty :
          BranchList.substN env_post.length [v] branches ≠ [] := by
        intro h_eq
        cases branches with
        | nil => exact h_ne rfl
        | cons _ _ => simp [BranchList.substN] at h_eq
      refine TypeOfHM.match_ (ih_scrut h_scrut) h_subst_nonempty ?_
      clear ih_scrut h_scrut h_ne h_subst_nonempty
      revert h_brs ih_branches
      induction branches with
      | nil =>
        intro _ _ b h_mem
        simp [BranchList.substN] at h_mem
      | cons hd tl ih_tl =>
        intro ih_branches h_brs branch h_mem
        obtain ⟨pat, body⟩ := hd
        simp only [BranchList.substN, List.mem_cons] at h_mem
        cases h_mem with
        | inl h_eq =>
          subst h_eq
          have h_branch := h_brs (pat, body) List.mem_cons_self
          cases h_branch with
          | mk h_lookup h_tyName h_paramCount h_contents h_inst h_pb h_ctx h_body =>
            subst h_ctx
            subst h_pb
            expose_names
            rw [show (instContents.map PolyTy.mkTrivial ++ (env_post ++ [M] ++ env))
                  = (instContents.map PolyTy.mkTrivial ++ env_post) ++ [M] ++ env
                  by rw [List.append_assoc, List.append_assoc, List.append_assoc]]
              at h_body
            have ih_body :=
              ih_branches pat body List.mem_cons_self
                (env_post := instContents.map PolyTy.mkTrivial ++ env_post)
                h_body
            simp only [List.length_append, List.length_map] at ih_body
            rw [← h_inst.length_eq, ← h_contents] at ih_body
            rw [show pat.contents + env_post.length = env_post.length + pat.contents
                  from Nat.add_comm _ _] at ih_body
            refine TypeOfMatchBranch.mk h_lookup h_tyName h_paramCount h_contents
              h_inst rfl rfl ?_
            rw [List.append_assoc] at ih_body
            exact ih_body
        | inr h_mem' =>
          exact ih_tl
            (fun pat' e' hmem => ih_branches pat' e' (List.mem_cons_of_mem _ hmem))
            (fun branch hmem => h_brs branch (List.mem_cons_of_mem _ hmem))
            branch h_mem'


/-- Multi-binding substitution: substitute a whole block of values `vs` for a
    block of schemes `Ms` (each `vs[j]` typing at every instance of `Ms[j]`).
    Generalises `subst_lemma` from `[v]`/`[M]` to lists — needed for the
    `letPairIn` (2 bindings) and `match_` (n bindings) reduction cases of
    preservation. Only the `var` case differs from `subst_lemma` (its
    trichotomy becomes three *ranges*); every other case is verbatim. -/
theorem TypeOfHM.subst_lemma_many
    {ctors : CtorEnv} {env_post env Ms : Env}
    {e : Expr} {τ : Ty} {vs : List Expr}
    (h_Ms_wf : ∀ M ∈ Ms, M.WF)
    (h_body : TypeOfHM ⟨env_post ++ Ms ++ env, ctors⟩ e τ)
    (h_vs : List.Forall₂ (fun v M => HasScheme ⟨env, ctors⟩ v M) vs Ms) :
    TypeOfHM ⟨env_post ++ env, ctors⟩ (e.substN env_post.length vs) τ := by
  have h_len : vs.length = Ms.length := h_vs.length_eq
  induction e using Expr.rec_strong generalizing env_post τ with
  | primLit p =>
    cases h_body with
    | primLitUnit => exact .primLitUnit
    | primLitInt  => exact .primLitInt
    | primLitNat  => exact .primLitNat
    | primLitBool => exact .primLitBool
    | primLitStr  => exact .primLitStr
  | pair a b ih_a ih_b =>
    cases h_body with
    | pair ha hb =>
      simp only [Expr.substN]
      exact .pair (ih_a ha) (ih_b hb)
  | app f inp ih_f ih_i =>
    cases h_body with
    | app hf hi =>
      simp only [Expr.substN]
      exact .app (ih_f hf) (ih_i hi)
  | lambda body ih =>
    cases h_body with
    | lambda hpc heq hbody =>
      subst heq
      simp only [Expr.substN]
      refine TypeOfHM.lambda hpc rfl ?_
      exact ih (env_post := PolyTy.mkTrivial _ :: env_post) hbody
  | letIn boundExpr body ih_be ih_body =>
    cases h_body with
    | letIn hsch hcofin heq hbodyinner =>
      subst heq
      simp only [Expr.substN]
      refine TypeOfHM.letIn hsch
        (fun Xs hfresh => ih_be (hcofin Xs hfresh)) rfl ?_
      exact ih_body (env_post := _ :: env_post) hbodyinner
  | letPairIn pe body ih_pe ih_body =>
    cases h_body with
    | letPairIn hschf hschs harity hcofin heq hbodyinner =>
      subst heq
      simp only [Expr.substN]
      refine TypeOfHM.letPairIn hschf hschs harity
        (fun Xs hfresh => ih_pe (hcofin Xs hfresh)) rfl ?_
      exact ih_body (env_post := _ :: _ :: env_post) hbodyinner
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
    cases h_body with
    | match_ h_scrut h_ne h_brs =>
      simp only [Expr.substN]
      have h_subst_nonempty :
          BranchList.substN env_post.length vs branches ≠ [] := by
        intro h_eq
        cases branches with
        | nil => exact h_ne rfl
        | cons _ _ => simp [BranchList.substN] at h_eq
      refine TypeOfHM.match_ (ih_scrut h_scrut) h_subst_nonempty ?_
      clear ih_scrut h_scrut h_ne h_subst_nonempty
      revert h_brs ih_branches
      induction branches with
      | nil =>
        intro _ _ b h_mem
        simp [BranchList.substN] at h_mem
      | cons hd tl ih_tl =>
        intro ih_branches h_brs branch h_mem
        obtain ⟨pat, body⟩ := hd
        simp only [BranchList.substN, List.mem_cons] at h_mem
        cases h_mem with
        | inl h_eq =>
          subst h_eq
          have h_branch := h_brs (pat, body) List.mem_cons_self
          cases h_branch with
          | mk h_lookup h_tyName h_paramCount h_contents h_inst h_pb h_ctx h_body =>
            subst h_ctx
            subst h_pb
            expose_names
            rw [show (instContents.map PolyTy.mkTrivial ++ (env_post ++ Ms ++ env))
                  = (instContents.map PolyTy.mkTrivial ++ env_post) ++ Ms ++ env
                  by rw [List.append_assoc, List.append_assoc, List.append_assoc]]
              at h_body
            have ih_body :=
              ih_branches pat body List.mem_cons_self
                (env_post := instContents.map PolyTy.mkTrivial ++ env_post)
                h_body
            simp only [List.length_append, List.length_map] at ih_body
            rw [← h_inst.length_eq, ← h_contents] at ih_body
            rw [show pat.contents + env_post.length = env_post.length + pat.contents
                  from Nat.add_comm _ _] at ih_body
            refine TypeOfMatchBranch.mk h_lookup h_tyName h_paramCount h_contents
              h_inst rfl rfl ?_
            rw [List.append_assoc] at ih_body
            exact ih_body
        | inr h_mem' =>
          exact ih_tl
            (fun pat' e' hmem => ih_branches pat' e' (List.mem_cons_of_mem _ hmem))
            (fun branch hmem => h_brs branch (List.mem_cons_of_mem _ hmem))
            branch h_mem'


/-- If `ty` is closed (no `bvar`s), then `InstantiatesBy` on it is the identity:
    no `bvar` ever gets matched, so the structural recursion just reproduces `ty`. -/
private lemma InstantiatesBy.eq_of_closed
    {tyArgs : List Ty} {ty τ : Ty}
    (h_closed : OnlyContainsBvars [] ty)
    (h_inst : InstantiatesBy tyArgs ty τ) :
    τ = ty := by
  induction ty using Ty.rec_strong generalizing τ with
  | prim _ =>
    cases h_inst; rfl
  | pair _ _ ih_a ih_b =>
    cases h_closed with
    | pair h_a h_b =>
      cases h_inst with
      | pair hi_a hi_b => rw [ih_a h_a hi_a, ih_b h_b hi_b]
  | arrow _ _ ih_a ih_b =>
    cases h_closed with
    | arrow h_a h_b =>
      cases h_inst with
      | arrow hi_a hi_b => rw [ih_a h_a hi_a, ih_b h_b hi_b]
  | bvar _ =>
    cases h_closed with
    | bvar h_mem => exact absurd h_mem List.not_mem_nil
  | fvar _ =>
    cases h_inst; rfl
  | customTy _ _ ih_tys =>
    cases h_closed with
    | customTy h_all =>
      cases h_inst with
      | customTy h_forall =>
        congr 1
        induction h_forall with
        | nil => rfl
        | cons h_hd h_tl ih_tl =>
          rename_i hd_ty _ tl_tys _
          have h_hd_eq :=
            ih_tys hd_ty List.mem_cons_self
              (h_all hd_ty List.mem_cons_self) h_hd
          have h_tl_eq :=
            ih_tl
              (fun ty h => ih_tys ty (List.mem_cons_of_mem _ h))
              (fun ty h => h_all ty (List.mem_cons_of_mem _ h))
          rw [h_hd_eq, h_tl_eq]




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
  | pair _ _ _ _   => cases h_chain
  | lambda _ _     => cases h_chain
  | letIn _ _ _ _  => cases h_chain
  | letPairIn _ _ _ _ => cases h_chain
  | var _          => cases h_chain
  | match_ _ _ _ _ => cases h_chain

theorem TypeOfHM.canonical_prim {ctx e p}
    (h_ty : TypeOfHM ctx e (.prim p))
    (h_val : SmallStep.IsValue e) :
    ∃ pl, e = .primLit pl := by
  cases h_val with
  | primLit p' => exact ⟨p', rfl⟩
  | lambda _ => cases h_ty
  | pair _ _ => cases h_ty
  | ctor name =>
    exfalso
    have ⟨_, _, tys, h_eq⟩ :=
      TypeOfHM.ctor_chain_has_customTy_form (.ctor name) h_ty
    cases tys with
    | nil => simp [Ty.wrapArrows] at h_eq
    | cons _ _ => simp [Ty.wrapArrows] at h_eq
  | ctorApp h_chain h_v =>
    exfalso
    have ⟨_, _, tys, h_eq⟩ :=
      TypeOfHM.ctor_chain_has_customTy_form (.app h_chain h_v) h_ty
    cases tys with
    | nil => simp [Ty.wrapArrows] at h_eq
    | cons _ _ => simp [Ty.wrapArrows] at h_eq

theorem TypeOfHM.canonical_pair {ctx e fstTy sndTy}
    (h_ty : TypeOfHM ctx e (.pair fstTy sndTy))
    (h_val : SmallStep.IsValue e) :
    ∃ a b, e = .pair a b ∧ SmallStep.IsValue a ∧ SmallStep.IsValue b := by
  cases h_val with
  | primLit _ => cases h_ty
  | lambda _ => cases h_ty
  | pair h_a h_b => exact ⟨_, _, rfl, h_a, h_b⟩
  | ctor name =>
    exfalso
    have ⟨_, _, tys, h_eq⟩ :=
      TypeOfHM.ctor_chain_has_customTy_form (.ctor name) h_ty
    cases tys with
    | nil => simp [Ty.wrapArrows] at h_eq
    | cons _ _ => simp [Ty.wrapArrows] at h_eq
  | ctorApp h_chain h_v =>
    exfalso
    have ⟨_, _, tys, h_eq⟩ :=
      TypeOfHM.ctor_chain_has_customTy_form (.app h_chain h_v) h_ty
    cases tys with
    | nil => simp [Ty.wrapArrows] at h_eq
    | cons _ _ => simp [Ty.wrapArrows] at h_eq

theorem TypeOfHM.canonical_arrow {ctx e argTy retTy}
    (h_ty : TypeOfHM ctx e (.arrow argTy retTy))
    (h_val : SmallStep.IsValue e) :
    (∃ body, e = .lambda body) ∨ SmallStep.IsCtorChain e := by
  cases h_val with
  | primLit _ => cases h_ty
  | lambda body => exact .inl ⟨body, rfl⟩
  | pair _ _ => cases h_ty
  | ctor name => exact .inr (.ctor name)
  | ctorApp h_chain h_v => exact .inr (.app h_chain h_v)

theorem TypeOfHM.canonical_customTy {ctx e tyName tyArgs}
    (h_ty : TypeOfHM ctx e (.customTy tyName tyArgs))
    (h_val : SmallStep.IsValue e) :
    SmallStep.IsCtorChain e := by
  cases h_val with
  | primLit _ => cases h_ty
  | lambda _ => cases h_ty
  | pair _ _ => cases h_ty
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
  | pair _ _ _ _ => cases h_chain
  | lambda _ _ => cases h_chain
  | letIn _ _ _ _ => cases h_chain
  | letPairIn _ _ _ _ => cases h_chain
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
    (h_exh : AllMatchesExhaustive ctx.ctors e) :
    IsValue e ∨ ∃ e', Step e e' := by
  induction e using Expr.rec_strong generalizing ctx τ with
  | primLit p => exact .inl (.primLit p)
  | lambda _ _ => exact .inl (.lambda _)
  | ctor name => exact .inl (.ctor name)
  | var n =>
    cases h_ty with
    | var h_lookup _ _ => rw [h_closed] at h_lookup; simp at h_lookup
  | pair a b iha ihb =>
    cases h_exh with
    | pair h_exh_a h_exh_b =>
      cases h_ty with
      | pair h_a h_b =>
        rcases iha h_a h_closed h_exh_a with hva | ⟨a', ha⟩
        · rcases ihb h_b h_closed h_exh_b with hvb | ⟨b', hb⟩
          · exact .inl (.pair hva hvb)
          · exact .inr ⟨_, .pairSnd hva hb⟩
        · exact .inr ⟨_, .pairFst ha⟩
  | app f arg ihf iharg =>
    cases h_exh with
    | app h_exh_f h_exh_arg =>
      cases h_ty with
      | app h_f h_arg =>
        rcases ihf h_f h_closed h_exh_f with hvf | ⟨f', hf⟩
        · rcases iharg h_arg h_closed h_exh_arg with hva | ⟨arg', harg⟩
          · rcases TypeOfHM.canonical_arrow h_f hvf with ⟨body, rfl⟩ | hchain
            · exact .inr ⟨_, .beta hva⟩
            · exact .inl (.ctorApp hchain hva)
          · exact .inr ⟨_, .appArg hvf harg⟩
        · exact .inr ⟨_, .appFn hf⟩
  | letIn rhs body ihrhs _ =>
    cases h_exh with
    | letIn h_exh_rhs _ =>
      cases h_ty with
      | letIn hwf hcofin heq hbody =>
        expose_names
        obtain ⟨Xs, hXlen, hXnodup, hXavoid⟩ := exists_fresh_names L M.paramCount
        have h_rhs := hcofin Xs ⟨hXlen, hXnodup, hXavoid⟩
        rcases ihrhs h_rhs h_closed h_exh_rhs with hvr | ⟨rhs', hrhs⟩
        · exact .inr ⟨_, .letReduce hvr⟩
        · exact .inr ⟨_, .letInRhs hrhs⟩
  | letPairIn rhs body ihrhs _ =>
    cases h_exh with
    | letPairIn h_exh_rhs _ =>
      cases h_ty with
      | letPairIn hwff hwfs harity hcofin heq hbody =>
        expose_names
        obtain ⟨Xs, hXlen, hXnodup, hXavoid⟩ := exists_fresh_names L Mfst.paramCount
        have h_rhs := hcofin Xs ⟨hXlen, hXnodup, hXavoid⟩
        rcases ihrhs h_rhs h_closed h_exh_rhs with hvr | ⟨rhs', hrhs⟩
        · obtain ⟨v₁, v₂, rfl, hv₁, hv₂⟩ := TypeOfHM.canonical_pair h_rhs hvr
          exact .inr ⟨_, .letPairReduce hv₁ hv₂⟩
        · exact .inr ⟨_, .letPairRhs hrhs⟩
  | match_ scrut branches ihscrut _ =>
    cases h_exh with
    | match_ h_exh_scrut _ h_branch_ty h_match_exh =>
      cases h_ty with
      | match_ h_scrut h_ne h_brs =>
        rcases ihscrut h_scrut h_closed h_exh_scrut with hvs | ⟨scrut', hscrut⟩
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
              -- the scrutinee's type name is now `ctor.tyName`; reconcile it with
              -- the exhaustiveness type name via any branch (`branches ≠ []`).
              obtain ⟨pat, body, hmem, hpctor, hparity⟩ :=
                h_match_exh name ctor hlook (by
                  obtain ⟨⟨pat0, body0⟩, htl0, hbeq⟩ :=
                    List.exists_cons_of_ne_nil h_ne
                  have hb0 : (pat0, body0) ∈ branches := by simp [hbeq]
                  obtain ⟨ctorB, hlookB, htyB⟩ := h_branch_ty pat0 body0 hb0
                  cases h_brs (pat0, body0) hb0 with
                  | mk hlookA htyA _ _ _ _ _ _ =>
                    rw [← htyA, Option.some.inj (hlookA.symm.trans hlookB)]
                    exact htyB)
              obtain ⟨e', hfmb⟩ := findMatchingBranch_of_exists
                ⟨pat, body, hmem, hpctor, hparity.trans hlen.symm⟩
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
  | here _ _ => exact List.mem_cons_self
  | there _ _ ih => exact List.mem_cons_of_mem _ ih

open SmallStep in
/-- The matched branch's pattern names the matched constructor. -/
theorem SmallStep.FirstMatchingBranch.ctor_eq {name arity branches pat body}
    (h : FirstMatchingBranch name arity branches pat body) : pat.ctor = name := by
  induction h with
  | here hc _ => exact hc
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
  | pair a b iha ihb =>
    intro t1 t2 hbv h1 h2
    cases hbv with
    | pair hba hbb =>
      cases h1 with
      | pair h1a h1b =>
        cases h2 with
        | pair h2a h2b => rw [iha hba h1a h2a, ihb hbb h1b h2b]
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
theorem TypeOfHM.preservation {ctx : Ctx} {e e' : Expr} {τ : Ty}
    (h_step : Step e e') (h_ty : TypeOfHM ctx e τ) :
    TypeOfHM ctx e' τ := by
  induction h_step generalizing τ with
  | beta hval =>
    cases h_ty with
    | app hf hi =>
      cases hf with
      | lambda hpc heq hbody =>
        subst heq
        exact TypeOfHM.subst_lemma (env_post := []) (M := PolyTy.mkTrivial _)
          hpc hbody (HasScheme.ofTypeOfHM hi)
  | letReduce hval =>
    cases h_ty with
    | letIn hwf hcofin heq hbody =>
      subst heq
      exact TypeOfHM.subst_lemma (env_post := []) hwf hbody
        (HasScheme.fromHasSchemeVars hcofin)
  | letPairReduce hv₁ hv₂ =>
    cases h_ty with
    | letPairIn hwff hwfs harity hcofin heq hbody =>
      subst heq
      have hv1_sch : HasSchemeVars _ ⟨ctx.env, ctx.ctors⟩ _ _ := fun Xs hfresh => by
        cases hcofin Xs hfresh with | pair h1 _ => exact h1
      have hv2_sch : HasSchemeVars _ ⟨ctx.env, ctx.ctors⟩ _ _ := fun Xs hfresh => by
        cases hcofin Xs ⟨by rw [harity]; exact hfresh.length, hfresh.nodup, hfresh.avoid⟩
          with | pair _ h2 => exact h2
      refine TypeOfHM.subst_lemma_many (env_post := [])
        (Ms := [_, _]) (vs := [_, _]) ?_ hbody ?_
      · intro M hM
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hM
        rcases hM with rfl | rfl
        · exact hwfs
        · exact hwff
      · exact .cons (HasScheme.fromHasSchemeVars hv2_sch)
          (.cons (HasScheme.fromHasSchemeVars hv1_sch) .nil)
  | matchReduce hval hctor hfirst =>
    rename_i scrut branches name args pat body
    cases h_ty with
    | match_ h_scrut h_ne h_brs =>
      rename_i tyName tyArgs
      have hmem := hfirst.mem
      have hpeq := hfirst.ctor_eq
      have hbranch := h_brs (pat, body) hmem
      cases hbranch with
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
        rw [hpeq] at hlookB
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
              h_Ms_wf hbodyB' h_vs
  | pairFst _ ih =>
    cases h_ty with
    | pair ha hb => exact .pair (ih ha) hb
  | pairSnd hv _ ih =>
    cases h_ty with
    | pair ha hb => exact .pair ha (ih hb)
  | appFn _ ih =>
    cases h_ty with
    | app hf hi => exact .app (ih hf) hi
  | appArg hv _ ih =>
    cases h_ty with
    | app hf hi => exact .app hf (ih hi)
  | letInRhs _ ih =>
    cases h_ty with
    | letIn hwf hcofin heq hbody =>
      exact .letIn hwf (fun Xs hfresh => ih (hcofin Xs hfresh)) heq hbody
  | letPairRhs _ ih =>
    cases h_ty with
    | letPairIn hwff hwfs harity hcofin heq hbody =>
      exact .letPairIn hwff hwfs harity
        (fun Xs hfresh => ih (hcofin Xs hfresh)) heq hbody
  | matchScrut _ ih =>
    cases h_ty with
    | match_ h_scrut h_ne h_brs => exact .match_ (ih h_scrut) h_ne h_brs


/-! ## Scaffolding for the algorithmic phase

Not used yet. Once we move from the declarative relation to algorithmic
inference, `.fvar`s stop being abstract/rigid type variables and become
*unification variables*, each pointing at an entry in a unification context. -/

/-- Either a constrained (`conc`) or unconstrained (`unspec`) unification var. -/
inductive TyMaybe where
  | unspec
  | conc (ty : Ty)

/-- The unification-var context. Each `.fvar` references an item in this list. -/
abbrev FvarCtx := List TyMaybe


/-! ## Algorithmic phase, step 1: substitution algebra

The declarative `TypeOfHM` treats `.fvar`s as rigid/abstract type variables.
The algorithm reinterprets them as *unification variables* and solves equality
constraints between monotypes by computing a most-general unifier (MGU).

A unification substitution maps `.fvar` names to types. We reuse the proven
`Ty.substFvars` machinery: a substitution is a `List (Nat × Ty)` applied
left-to-right, so **composition is list append** (`Subst.onTy_append`). This
algebra is shared scaffolding needed by *any* algorithmic presentation
(Algorithm W / M / J or constraint-based) — all of them rest on unification. -/

/-- A unification substitution: maps `.fvar` names to types, applied
    left-to-right via `Ty.substFvars`. Composition of `S` then `T` is `S ++ T`. -/
abbrev Subst := List (Nat × Ty)

/-- Apply a substitution to a monotype. -/
def Subst.onTy (S : Subst) : Ty → Ty := Ty.substFvars S

/-- Apply a substitution to a scheme. `substFvars` only rewrites free vars, so
    the scheme's bound vars (`.bvar`s `< paramCount`) are left untouched. -/
def Subst.onPolyTy (S : Subst) (M : PolyTy) : PolyTy :=
  { paramCount := M.paramCount, body := S.onTy M.body }

/-- Apply a substitution to a value environment. -/
def Subst.onEnv (S : Subst) (env : Env) : Env := env.map S.onPolyTy

/-- Apply a substitution to a typing context. Constructors are closed
    (`Ctor.closed`), so only the value env is affected. -/
def Subst.onCtx (S : Subst) (ctx : Ctx) : Ctx :=
  { env := S.onEnv ctx.env, ctors := ctx.ctors }

/-- `substFvars` of an append applies the prefix first, then the suffix — the
    elementary fact making list-append the composition of substitutions. -/
theorem Ty.substFvars_append (S T : Subst) (τ : Ty) :
    Ty.substFvars (S ++ T) τ = Ty.substFvars T (Ty.substFvars S τ) := by
  induction S generalizing τ with
  | nil => rfl
  | cons hd tl ih =>
    obtain ⟨Z, U⟩ := hd
    simp only [List.cons_append, Ty.substFvars]
    exact ih (Ty.substFvar Z U τ)

/-- Composition of substitutions is concatenation: `(S ++ T)` applies `S` first,
    then `T`. -/
theorem Subst.onTy_append (S T : Subst) (τ : Ty) :
    (S ++ T).onTy τ = T.onTy (S.onTy τ) := by
  simp only [Subst.onTy, Ty.substFvars_append]

@[simp] theorem Subst.onPolyTy_nil (M : PolyTy) : Subst.onPolyTy [] M = M := rfl

@[simp] theorem Subst.onEnv_nil (env : Env) : Subst.onEnv [] env = env := by
  show env.map (Subst.onPolyTy []) = env
  rw [show (Subst.onPolyTy [] : PolyTy → PolyTy) = id from funext Subst.onPolyTy_nil]
  exact List.map_id env

@[simp] theorem Subst.onCtx_nil (ctx : Ctx) : Subst.onCtx [] ctx = ctx := by
  simp only [Subst.onCtx, Subst.onEnv_nil]

theorem Subst.onPolyTy_append (S T : Subst) (M : PolyTy) :
    (S ++ T).onPolyTy M = T.onPolyTy (S.onPolyTy M) := by
  simp only [Subst.onPolyTy, Subst.onTy_append]

theorem Subst.onEnv_append (S T : Subst) (env : Env) :
    (S ++ T).onEnv env = T.onEnv (S.onEnv env) := by
  simp only [Subst.onEnv, List.map_map]
  apply List.map_congr_left
  intro M _
  exact Subst.onPolyTy_append S T M

theorem Subst.onCtx_append (S T : Subst) (ctx : Ctx) :
    (S ++ T).onCtx ctx = T.onCtx (S.onCtx ctx) := by
  simp only [Subst.onCtx, Subst.onEnv_append]


/-! ### Substitution preserves typing

Substituting over the *whole* context needs no environment-freshness side
condition (the freshness premise of `typ_subst_preservation` is vacuous with an
empty outer env) — only that each replacement type is locally-closed. This is
the workhorse for `Infer` soundness: applying the threaded substitution to a
`TypeOfHM` derivation yields another. -/

/-- Single-variable substitution preserves typing across the whole context. -/
theorem TypeOfHM.onSubstFvar {ctx : Ctx} {e : Expr} {τ : Ty} (Z : Nat) (U : Ty)
    (hU : U.IsLC) (h : TypeOfHM ctx e τ) :
    TypeOfHM (Subst.onCtx [(Z, U)] ctx) e (Subst.onTy [(Z, U)] τ) := by
  have key := TypeOfHM.typ_subst_preservation (ctors := ctx.ctors) (env_post := ctx.env)
    (env_outer := []) (Z := Z) (U := U) (by simp [Env.freeVars]) hU
    (by rw [List.append_nil]; exact h)
  rw [List.append_nil] at key
  exact key

/-- A whole substitution preserves typing, given each replacement is LC. -/
theorem TypeOfHM.onSubst {ctx : Ctx} {e : Expr} {τ : Ty} (S : Subst)
    (h_lc : ∀ p ∈ S, p.2.IsLC) (h : TypeOfHM ctx e τ) :
    TypeOfHM (S.onCtx ctx) e (S.onTy τ) := by
  induction S generalizing ctx τ with
  | nil => simpa using h
  | cons hd S' ih =>
    obtain ⟨Z, U⟩ := hd
    have hU : U.IsLC := h_lc (Z, U) (List.mem_cons_self ..)
    have hS' : ∀ p ∈ S', p.2.IsLC := fun p hp => h_lc p (List.mem_cons_of_mem _ hp)
    have step := TypeOfHM.onSubstFvar Z U hU h
    have rest := ih hS' step
    rw [show ((Z, U) :: S') = [(Z, U)] ++ S' from rfl, Subst.onCtx_append, Subst.onTy_append]
    exact rest


/-! ### Most-general unifier specification

`Unifies S τ₁ τ₂` says `S` equates the two monotypes; `IsMGU S τ₁ τ₂` adds that
*every* unifier factors through `S` (`S` is the least committal one). Because
composition is `++` and `(S ++ R).onTy τ = R.onTy (S.onTy τ)`, "`S'` factors
through `S`" means `∃ R, S' acts as (S then R)`.

The occurs check needs no new notion: `.fvar Z` occurs in `τ` exactly when
`Z ∈ τ.freeVars`. -/

/-- `S` makes `τ₁` and `τ₂` syntactically equal. -/
def Unifies (S : Subst) (τ₁ τ₂ : Ty) : Prop := S.onTy τ₁ = S.onTy τ₂

/-- `S` is a most-general unifier of `τ₁` and `τ₂`: it unifies them, and any
    other unifier `S'` is an extension of `S` (factors as `S` then some `R`). -/
structure IsMGU (S : Subst) (τ₁ τ₂ : Ty) : Prop where
  unifies : Unifies S τ₁ τ₂
  greatest : ∀ S', Unifies S' τ₁ τ₂ → ∃ R : Subst, ∀ τ, S'.onTy τ = R.onTy (S.onTy τ)


/-! ### The unification relation

`UnifyRel τ₁ τ₂ S` is the *graph of unification on success*: it holds when the
two monotypes unify and `S` is a resulting most-general unifier. Failure is the
*absence* of a derivation (constructor clash, arity clash, or occurs-check), so
no negative side-conditions are needed and there is no termination obligation —
this is the relation-first stage; a `unify` function comes later (stage 3).

Compound types thread the prefix substitution into the remaining sub-problems
(`UnifyRel (S₁.onTy b) (S₁.onTy d) S₂`), exactly as Algorithm W's unifier does.
The occurs check is the freshness premise `n ∉ τ.freeVars` on the var rules;
together with `substFvar_fresh` it is what makes `[(n, τ)]` an actual unifier. -/
mutual

inductive UnifyRel : Ty → Ty → Subst → Prop
  | prim {p} :
    UnifyRel (.prim p) (.prim p) []
  | fvarRefl {n} :
    UnifyRel (.fvar n) (.fvar n) []
  | fvarL {n τ} :
    τ ≠ .fvar n → n ∉ τ.freeVars →
    UnifyRel (.fvar n) τ [(n, τ)]
  | fvarR {n τ} :
    τ ≠ .fvar n → n ∉ τ.freeVars →
    UnifyRel τ (.fvar n) [(n, τ)]
  | arrow {a b c d S₁ S₂} :
    UnifyRel a c S₁ →
    UnifyRel (S₁.onTy b) (S₁.onTy d) S₂ →
    UnifyRel (.arrow a b) (.arrow c d) (S₁ ++ S₂)
  | pair {a b c d S₁ S₂} :
    UnifyRel a c S₁ →
    UnifyRel (S₁.onTy b) (S₁.onTy d) S₂ →
    UnifyRel (.pair a b) (.pair c d) (S₁ ++ S₂)
  | customTy {nm tys₁ tys₂ S} :
    UnifyRelList tys₁ tys₂ S →
    UnifyRel (.customTy nm tys₁) (.customTy nm tys₂) S

/-- Pairwise unification of equal-length type lists, threading the substitution
    left-to-right. Used for the arguments of a custom type constructor. -/
inductive UnifyRelList : List Ty → List Ty → Subst → Prop
  | nil :
    UnifyRelList [] [] []
  | cons {t₁ t₂ ts₁ ts₂ S₁ S₂} :
    UnifyRel t₁ t₂ S₁ →
    UnifyRelList (ts₁.map S₁.onTy) (ts₂.map S₁.onTy) S₂ →
    UnifyRelList (t₁ :: ts₁) (t₂ :: ts₂) (S₁ ++ S₂)

end


/-! ### `onTy` distributes over the type formers -/

@[simp] theorem Subst.onTy_nil {τ : Ty} : Subst.onTy [] τ = τ := rfl

@[simp] theorem Subst.onTy_prim {S : Subst} {p : PrimTy} :
    S.onTy (.prim p) = .prim p := Ty.substFvars_prim

@[simp] theorem Subst.onTy_bvar {S : Subst} {i : Nat} :
    S.onTy (.bvar i) = .bvar i := Ty.substFvars_bvar

@[simp] theorem Subst.onTy_pair {S : Subst} {a b : Ty} :
    S.onTy (.pair a b) = .pair (S.onTy a) (S.onTy b) := Ty.substFvars_pair

@[simp] theorem Subst.onTy_arrow {S : Subst} {a b : Ty} :
    S.onTy (.arrow a b) = .arrow (S.onTy a) (S.onTy b) := Ty.substFvars_arrow

@[simp] theorem Subst.onTy_customTy {S : Subst} {nm : TyName} {tys : List Ty} :
    S.onTy (.customTy nm tys) = .customTy nm (tys.map S.onTy) := Ty.substFvars_customTy

/-- Mapping a composed substitution over a list = mapping each factor in turn. -/
theorem Subst.map_onTy_append (S T : Subst) (ts : List Ty) :
    ts.map (S ++ T).onTy = (ts.map S.onTy).map T.onTy := by
  rw [List.map_map]
  apply List.map_congr_left
  intro x _
  exact Subst.onTy_append S T x


/-! ### Soundness, part 1: a derived substitution is a unifier -/

mutual

/-- Any substitution produced by `UnifyRel` actually unifies the two types. -/
theorem UnifyRel.unifies : {τ₁ τ₂ : Ty} → {S : Subst} → UnifyRel τ₁ τ₂ S →
    Unifies S τ₁ τ₂
  | _, _, _, .prim => rfl
  | _, _, _, .fvarRefl => rfl
  | _, _, _, .fvarL _ hocc => by
    simp [Unifies, Subst.onTy, Ty.substFvars, Ty.substFvar, Ty.substFvar_fresh hocc]
  | _, _, _, .fvarR _ hocc => by
    simp [Unifies, Subst.onTy, Ty.substFvars, Ty.substFvar, Ty.substFvar_fresh hocc]
  | _, _, _, .arrow h₁ h₂ => by
    have e1 := UnifyRel.unifies h₁
    have e2 := UnifyRel.unifies h₂
    simp only [Unifies, Subst.onTy_append, Subst.onTy_arrow] at e1 e2 ⊢
    rw [Ty.arrow.injEq]
    exact ⟨by rw [e1], e2⟩
  | _, _, _, .pair h₁ h₂ => by
    have e1 := UnifyRel.unifies h₁
    have e2 := UnifyRel.unifies h₂
    simp only [Unifies, Subst.onTy_append, Subst.onTy_pair] at e1 e2 ⊢
    rw [Ty.pair.injEq]
    exact ⟨by rw [e1], e2⟩
  | _, _, _, .customTy hl => by
    have el := UnifyRelList.unifies hl
    simp only [Unifies, Subst.onTy_customTy, el]

/-- The list version: a list-unifier equalises the two lists pointwise. -/
theorem UnifyRelList.unifies : {ts₁ ts₂ : List Ty} → {S : Subst} →
    UnifyRelList ts₁ ts₂ S → ts₁.map S.onTy = ts₂.map S.onTy
  | _, _, _, .nil => rfl
  | _, _, _, .cons h₁ ht => by
    have e1 := UnifyRel.unifies h₁
    have et := UnifyRelList.unifies ht
    simp only [Unifies] at e1
    simp only [List.map_cons, Subst.onTy_append, Subst.map_onTy_append]
    rw [e1, et]

end


-- theorem UnifyRelList.unifies_rel : {ts₁ ts₂ : List Ty} → {S : Subst} →
--     UnifyRelList ts₁ ts₂ S → List.Forall₂ (Unifies S) ts₁ ts₂ := by sorry
--     -- UnifyRelList ts₁ ts₂ S → List.Forall₂ (UnifyRel · · S) ts₁ ts₂ := by sorry

/-! ### Soundness, part 2: a derived substitution is *most general*

The backbone of the var cases: if `S'` already equates `.fvar n` with `U`, then
applying `S'` is unchanged by first substituting `[n ↦ U]`. -/

theorem Subst.onTy_substFvar {S' : Subst} {n : Nat} {U : Ty}
    (h : S'.onTy (.fvar n) = S'.onTy U) :
    ∀ τ, S'.onTy (Ty.substFvar n U τ) = S'.onTy τ := by
  intro τ
  induction τ using Ty.rec_strong with
  | prim p => rfl
  | bvar i => rfl
  | fvar m =>
    by_cases hm : m = n
    · subst hm
      simp only [Ty.substFvar, if_true]
      exact h.symm
    · simp only [Ty.substFvar, if_neg hm]
  | pair a b iha ihb => simp only [Ty.substFvar, Subst.onTy_pair, iha, ihb]
  | arrow a b iha ihb => simp only [Ty.substFvar, Subst.onTy_arrow, iha, ihb]
  | customTy nm tys ih =>
    simp only [Ty.substFvar, TyList.substFvar_eq_map, Subst.onTy_customTy, List.map_map]
    apply congrArg (Ty.customTy nm)
    apply List.map_congr_left
    intro t ht
    exact ih t ht

/-! Every substitution produced by `UnifyRel` is a *most general* unifier: any
    other unifier `S'` factors through it. The compound cases thread the
    sub-problem unifiers (`R₁` then `R₂`) and return the final `R₂`; the var
    cases use `onTy_substFvar`. -/
mutual

theorem UnifyRel.greatest : {τ₁ τ₂ : Ty} → {S : Subst} → UnifyRel τ₁ τ₂ S →
    ∀ S' : Subst, Unifies S' τ₁ τ₂ → ∃ R : Subst, ∀ τ, S'.onTy τ = R.onTy (S.onTy τ)
  | _, _, _, .prim, S', _ => ⟨S', fun τ => by simp only [Subst.onTy_nil]⟩
  | _, _, _, .fvarRefl, S', _ => ⟨S', fun τ => by simp only [Subst.onTy_nil]⟩
  | _, _, _, .fvarL _ _, S', hS' =>
    ⟨S', fun τ => (Subst.onTy_substFvar hS' τ).symm⟩
  | _, _, _, .fvarR _ _, S', hS' =>
    ⟨S', fun τ => (Subst.onTy_substFvar (Eq.symm hS') τ).symm⟩
  | _, _, _, @UnifyRel.arrow a b c d S₁ S₂ h₁ h₂, S', hS' => by
    simp only [Unifies, Subst.onTy_arrow, Ty.arrow.injEq] at hS'
    obtain ⟨hac, hbd⟩ := hS'
    obtain ⟨R₁, hR₁⟩ := UnifyRel.greatest h₁ S' hac
    have hR₁bd : Unifies R₁ (S₁.onTy b) (S₁.onTy d) := by
      show R₁.onTy (S₁.onTy b) = R₁.onTy (S₁.onTy d)
      rw [← hR₁ b, ← hR₁ d]; exact hbd
    obtain ⟨R₂, hR₂⟩ := UnifyRel.greatest h₂ R₁ hR₁bd
    refine ⟨R₂, fun τ => ?_⟩
    rw [Subst.onTy_append, ← hR₂ (S₁.onTy τ), hR₁ τ]
  | _, _, _, @UnifyRel.pair a b c d S₁ S₂ h₁ h₂, S', hS' => by
    simp only [Unifies, Subst.onTy_pair, Ty.pair.injEq] at hS'
    obtain ⟨hac, hbd⟩ := hS'
    obtain ⟨R₁, hR₁⟩ := UnifyRel.greatest h₁ S' hac
    have hR₁bd : Unifies R₁ (S₁.onTy b) (S₁.onTy d) := by
      show R₁.onTy (S₁.onTy b) = R₁.onTy (S₁.onTy d)
      rw [← hR₁ b, ← hR₁ d]; exact hbd
    obtain ⟨R₂, hR₂⟩ := UnifyRel.greatest h₂ R₁ hR₁bd
    refine ⟨R₂, fun τ => ?_⟩
    rw [Subst.onTy_append, ← hR₂ (S₁.onTy τ), hR₁ τ]
  | _, _, _, .customTy hl, S', hS' => by
    simp only [Unifies, Subst.onTy_customTy, Ty.customTy.injEq, true_and] at hS'
    exact UnifyRelList.greatest hl S' hS'

theorem UnifyRelList.greatest : {ts₁ ts₂ : List Ty} → {S : Subst} →
    UnifyRelList ts₁ ts₂ S → ∀ S' : Subst, ts₁.map S'.onTy = ts₂.map S'.onTy →
      ∃ R : Subst, ∀ τ, S'.onTy τ = R.onTy (S.onTy τ)
  | _, _, _, .nil, S', _ => ⟨S', fun τ => by simp only [Subst.onTy_nil]⟩
  | _, _, _, @UnifyRelList.cons t₁ t₂ ts₁ ts₂ S₁ S₂ h₁ ht, S', hS' => by
    simp only [List.map_cons, List.cons.injEq] at hS'
    obtain ⟨ht1t2, htail⟩ := hS'
    obtain ⟨R₁, hR₁⟩ := UnifyRel.greatest h₁ S' ht1t2
    have key : ∀ (l : List Ty), l.map (R₁.onTy ∘ S₁.onTy) = l.map S'.onTy := by
      intro l; apply List.map_congr_left; intro t _; exact (hR₁ t).symm
    have hlist : (ts₁.map S₁.onTy).map R₁.onTy = (ts₂.map S₁.onTy).map R₁.onTy := by
      rw [List.map_map, List.map_map, key, key]; exact htail
    obtain ⟨R₂, hR₂⟩ := UnifyRelList.greatest ht R₁ hlist
    refine ⟨R₂, fun τ => ?_⟩
    rw [Subst.onTy_append, ← hR₂ (S₁.onTy τ), hR₁ τ]

end

/-- Unification soundness, assembled: a derivation yields a most-general unifier. -/
theorem UnifyRel.isMGU {τ₁ τ₂ : Ty} {S : Subst} (h : UnifyRel τ₁ τ₂ S) :
    IsMGU S τ₁ τ₂ :=
  ⟨h.unifies, h.greatest⟩


/-! ### Local-closedness of substitutions

Applying an LC substitution preserves local-closedness, and unification of two
LC monotypes yields an LC substitution (each replacement is a sub-part of an LC
input). These feed the `Infer.lc` invariant. -/

/-- Applying a substitution whose replacements are all LC preserves LC. -/
theorem Subst.onTy_lc {S : Subst} (h_lc : ∀ p ∈ S, p.2.IsLC) :
    ∀ {τ : Ty}, τ.IsLC → (S.onTy τ).IsLC := by
  induction S with
  | nil => intro τ hτ; simpa using hτ
  | cons hd S' ih =>
    obtain ⟨Z, U⟩ := hd
    have hU : U.IsLC := h_lc (Z, U) (List.mem_cons_self ..)
    have hS' : ∀ p ∈ S', p.2.IsLC := fun p hp => h_lc p (List.mem_cons_of_mem _ hp)
    intro τ hτ
    rw [show ((Z, U) :: S') = [(Z, U)] ++ S' from rfl, Subst.onTy_append]
    exact ih hS' (Ty.IsLC.substFvar hU hτ)

mutual

/-- Unifying two locally-closed monotypes yields an LC substitution. -/
theorem UnifyRel.lc : {a b : Ty} → {S : Subst} → UnifyRel a b S →
    a.IsLC → b.IsLC → ∀ p ∈ S, p.2.IsLC
  | _, _, _, .prim, _, _ => by simp
  | _, _, _, .fvarRefl, _, _ => by simp
  | _, _, _, .fvarL _ _, _, hb => by
    intro p hp; rw [List.mem_singleton] at hp; subst hp; exact hb
  | _, _, _, .fvarR _ _, ha, _ => by
    intro p hp; rw [List.mem_singleton] at hp; subst hp; exact ha
  | _, _, _, .arrow h₁ h₂, ha, hb => by
    cases ha with | arrow ha_a ha_b => cases hb with | arrow hb_c hb_d =>
    have h1lc := UnifyRel.lc h₁ ha_a hb_c
    have h2lc := UnifyRel.lc h₂ (Subst.onTy_lc h1lc ha_b) (Subst.onTy_lc h1lc hb_d)
    intro p hp; rw [List.mem_append] at hp
    rcases hp with hp | hp
    · exact h1lc p hp
    · exact h2lc p hp
  | _, _, _, .pair h₁ h₂, ha, hb => by
    cases ha with | pair ha_a ha_b => cases hb with | pair hb_c hb_d =>
    have h1lc := UnifyRel.lc h₁ ha_a hb_c
    have h2lc := UnifyRel.lc h₂ (Subst.onTy_lc h1lc ha_b) (Subst.onTy_lc h1lc hb_d)
    intro p hp; rw [List.mem_append] at hp
    rcases hp with hp | hp
    · exact h1lc p hp
    · exact h2lc p hp
  | _, _, _, .customTy hl, ha, hb => by
    cases ha with | customTy ha_all => cases hb with | customTy hb_all =>
    exact UnifyRelList.lc hl ha_all hb_all

/-- List version: unifying two LC type lists yields an LC substitution. -/
theorem UnifyRelList.lc : {ts₁ ts₂ : List Ty} → {S : Subst} → UnifyRelList ts₁ ts₂ S →
    (∀ t ∈ ts₁, t.IsLC) → (∀ t ∈ ts₂, t.IsLC) → ∀ p ∈ S, p.2.IsLC
  | _, _, _, .nil, _, _ => by simp
  | _, _, _, @UnifyRelList.cons t₁ t₂ ts₁ ts₂ S₁ S₂ h₁ ht, hts₁, hts₂ => by
    have ht1 : t₁.IsLC := hts₁ t₁ (List.mem_cons_self ..)
    have ht2 : t₂.IsLC := hts₂ t₂ (List.mem_cons_self ..)
    have h1lc := UnifyRel.lc h₁ ht1 ht2
    have hmap₁ : ∀ t ∈ ts₁.map S₁.onTy, t.IsLC := by
      intro t htm; obtain ⟨t0, ht0, rfl⟩ := List.mem_map.mp htm
      exact Subst.onTy_lc h1lc (hts₁ t0 (List.mem_cons_of_mem _ ht0))
    have hmap₂ : ∀ t ∈ ts₂.map S₁.onTy, t.IsLC := by
      intro t htm; obtain ⟨t0, ht0, rfl⟩ := List.mem_map.mp htm
      exact Subst.onTy_lc h1lc (hts₂ t0 (List.mem_cons_of_mem _ ht0))
    have h2lc := UnifyRelList.lc ht hmap₁ hmap₂
    intro p hp; rw [List.mem_append] at hp
    rcases hp with hp | hp
    · exact h1lc p hp
    · exact h2lc p hp

end


/-! ## Algorithmic phase, step 2: the inference relation (Algorithm W, relational)

`Infer Φ ctx e Φ' S τ` is Algorithm W phrased as a *relation* (no function /
termination obligation yet — that is stage 3). It reads: starting with the
fresh-variable frontier `Φ` (every unification var in play is `< Φ`), expression
`e` infers type `τ` under the most-general substitution `S`, allocating fresh
vars up to the new frontier `Φ'`. `.fvar`s are the unification variables;
composition of the threaded substitutions is `++`.

This v1 covers the let-polymorphic core (`primLit`, `pair`, `lambda`, `app`,
`var`, `letIn`); `ctor`/`match_`/`letPairIn` are added once the core soundness
bridge to `TypeOfHM` is in place. The relation being partial on those forms is
harmless — it is a *sound* (not yet complete) specification.

The plan: prove `Infer.sound` (algo type ⟹ declarative type, iterating
`typ_subst_preservation` and using `UnifyRel.isMGU`), then completeness. -/

/-- The `k` fresh unification-var names starting at frontier `Φ`. -/
def freshVars (Φ k : Nat) : List Nat := (List.range k).map (Φ + ·)

/-- Generalization candidates: the free unification vars of `τ` that are *not*
    fixed by `env` (these are the ones a `let` may generalize over). -/
def genVars (env : Env) (τ : Ty) : List Nat :=
  τ.freeVars.filter (fun x => !env.freeVars.contains x)

/-- The principal generalization of `τ` relative to `env`: the scheme quantifying
    over exactly the free vars of `τ` not fixed by `env` (`genVars`). Reuses the
    existing `Ty.closeOver` (`fvar` ↦ `bvar` by position), whose
    `closeOver_preserves_bvars` immediately gives `genScheme … |>.WF`. -/
def genScheme (env : Env) (τ : Ty) : PolyTy :=
  { paramCount := (genVars env τ).length, body := Ty.closeOver (genVars env τ) τ }

/-- A generalized scheme is well-formed when its body type is locally-closed —
    closing introduces only the `paramCount`-many fresh bound vars. -/
theorem genScheme_wf {env : Env} {τ : Ty} (hτ : τ.IsLC) : (genScheme env τ).WF :=
  Ty.closeOver_preserves_bvars hτ

/-- `freeVars` is always duplicate-free (it dedups). -/
theorem Ty.freeVars_nodup {τ : Ty} : τ.freeVars.Nodup := by
  cases τ with
  | prim => simp [Ty.freeVars]
  | bvar => simp [Ty.freeVars]
  | fvar => simp [Ty.freeVars]
  | pair a b => simp [Ty.freeVars, List.nodup_dedup]
  | arrow a b => simp [Ty.freeVars, List.nodup_dedup]
  | customTy nm tys =>
    cases tys with
    | nil => simp [Ty.freeVars, TyList.freeVars]
    | cons hd tl => simp [Ty.freeVars, TyList.freeVars, List.nodup_dedup]

/-- The generalization candidates are duplicate-free. -/
theorem genVars_nodup {env : Env} {τ : Ty} : (genVars env τ).Nodup :=
  Ty.freeVars_nodup.filter _

/-- Algorithm W as a substitution-threading relation.
@TODO: remember to add constructors for the remaining Expr variants: `letPairIn`, `ctor`, `match_`
-/
inductive Infer : Nat → Ctx → Expr → Nat → Subst → Ty → Prop
  | primLitUnit {Φ ctx} :
    Infer Φ ctx (.primLit .unit) Φ [] (.prim .unit)
  | primLitInt {Φ ctx n} :
    Infer Φ ctx (.primLit (.int n)) Φ [] (.prim .int)
  | primLitNat {Φ ctx n} :
    Infer Φ ctx (.primLit (.nat n)) Φ [] (.prim .nat)
  | primLitBool {Φ ctx b} :
    Infer Φ ctx (.primLit (.bool b)) Φ [] (.prim .bool)
  | primLitStr {Φ ctx s} :
    Infer Φ ctx (.primLit (.str s)) Φ [] (.prim .str)
  | pair {Φ ctx a b Φ₁ Φ₂ S₁ S₂ τa τb} :
    Infer Φ ctx a Φ₁ S₁ τa →
    Infer Φ₁ (S₁.onCtx ctx) b Φ₂ S₂ τb →
    Infer Φ ctx (.pair a b) Φ₂ (S₁ ++ S₂) (.pair (S₂.onTy τa) τb)
  | lambda {Φ ctx body Φ' S τb} :
    Infer (Φ + 1) { ctx with env := PolyTy.mkTrivial (.fvar Φ) :: ctx.env } body Φ' S τb →
    Infer Φ ctx (.lambda body) Φ' S (.arrow (S.onTy (.fvar Φ)) τb)
  | app {Φ ctx f arg Φ₁ Φ₂ S₁ S₂ S₃ τf τa} :
    Infer Φ ctx f Φ₁ S₁ τf →
    Infer Φ₁ (S₁.onCtx ctx) arg Φ₂ S₂ τa →
    UnifyRel (S₂.onTy τf) (.arrow τa (.fvar Φ₂)) S₃ →
    Infer Φ ctx (.app f arg) (Φ₂ + 1) (S₁ ++ S₂ ++ S₃) (S₃.onTy (.fvar Φ₂))
  | var {Φ ctx i polyTy} :
    ctx.env[i]? = some polyTy →
    Infer Φ ctx (.var i) (Φ + polyTy.paramCount) []
      (polyTy.openVars (freshVars Φ polyTy.paramCount))
  | letIn {Φ ctx rhs body Φ₁ Φ₂ S₁ S₂ τ₁ τ₂} :
    Infer Φ ctx rhs Φ₁ S₁ τ₁ →
    Infer Φ₁
      { (S₁.onCtx ctx) with
        env := genScheme (S₁.onCtx ctx).env τ₁ :: (S₁.onCtx ctx).env }
      body Φ₂ S₂ τ₂ →
    Infer Φ ctx (.letIn rhs body) Φ₂ (S₁ ++ S₂) τ₂


/-! ### Invariant layer for `Infer` soundness -/

/-- The fresh-variable frontier only ever grows. -/
theorem Infer.frontier_le {Φ ctx e Φ' S τ} (h : Infer Φ ctx e Φ' S τ) : Φ ≤ Φ' := by
  induction h <;> omega

/-- A context is well-formed when every scheme in its env is well-formed. -/
def CtxWF (ctx : Ctx) : Prop := ∀ M ∈ ctx.env, M.WF

@[simp] theorem freshVars_length (Φ k : Nat) : (freshVars Φ k).length = k := by
  simp [freshVars]

/-- A whole substitution (LC replacements) preserves any bvar bound. -/
theorem Subst.onTy_containsBvars {S : Subst} (h_lc : ∀ p ∈ S, p.2.IsLC) :
    ∀ {n : Nat} {τ : Ty}, ContainsBvarsUpTo n τ → ContainsBvarsUpTo n (S.onTy τ) := by
  induction S with
  | nil => intro n τ hτ; simpa using hτ
  | cons hd S' ih =>
    obtain ⟨Z, U⟩ := hd
    have hU : U.IsLC := h_lc (Z, U) (List.mem_cons_self ..)
    have hS' : ∀ p ∈ S', p.2.IsLC := fun p hp => h_lc p (List.mem_cons_of_mem _ hp)
    intro n τ hτ
    rw [show ((Z, U) :: S') = [(Z, U)] ++ S' from rfl, Subst.onTy_append]
    exact ih hS' (ContainsBvarsUpTo.substFvar hU hτ)

/-- A whole substitution preserves scheme well-formedness. -/
theorem Subst.onPolyTy_wf {S : Subst} (h_lc : ∀ p ∈ S, p.2.IsLC) {M : PolyTy}
    (hM : M.WF) : (S.onPolyTy M).WF :=
  Subst.onTy_containsBvars h_lc hM

/-- A whole substitution preserves context well-formedness. -/
theorem Subst.onCtx_wf {S : Subst} (h_lc : ∀ p ∈ S, p.2.IsLC) {ctx : Ctx}
    (h : CtxWF ctx) : CtxWF (S.onCtx ctx) := by
  intro M hM
  simp only [Subst.onCtx, Subst.onEnv] at hM
  obtain ⟨M0, hM0, rfl⟩ := List.mem_map.mp hM
  exact Subst.onPolyTy_wf h_lc (h M0 hM0)

/-- Instantiating all bvars below `n` with LC types yields an LC type. -/
theorem Ty.instantiate_isLC {σ : Nat → Ty} {n : Nat}
    (hσ : ∀ i, i < n → (σ i).IsLC) {ty : Ty} (hty : ContainsBvarsUpTo n ty) :
    (ty.instantiate σ).IsLC := by
  induction ty using Ty.rec_strong with
  | prim p => exact .prim
  | bvar i => cases hty with | bvar hlt => exact hσ i hlt
  | fvar m => exact .fvar
  | pair a b iha ihb => cases hty with | pair ha hb => exact .pair (iha ha) (ihb hb)
  | arrow a b iha ihb => cases hty with | arrow ha hb => exact .arrow (iha ha) (ihb hb)
  | customTy nm tys ih =>
    cases hty with
    | customTy hall =>
      simp only [Ty.instantiate, TyList.instantiate_eq_map]
      apply ContainsBvarsUpTo.customTy
      intro t ht
      obtain ⟨t0, ht0, rfl⟩ := List.mem_map.mp ht
      exact ih t0 ht0 (hall t0 ht0)

/-- Opening a type whose bvars are `< Xs.length` with fresh names is LC. -/
theorem Ty.openVars_isLC {Xs : List Nat} {n : Nat} {ty : Ty}
    (hty : ContainsBvarsUpTo n ty) (hn : n ≤ Xs.length) :
    (Ty.openVars Xs ty).IsLC := by
  simp only [Ty.openVars]
  refine Ty.instantiate_isLC (fun i hi => ?_) hty
  rw [List.getElem?_eq_getElem (show i < Xs.length by omega)]
  exact .fvar

/-- Opening a well-formed scheme with enough fresh names is LC. -/
theorem PolyTy.openVars_isLC {Xs : List Nat} {M : PolyTy}
    (hM : M.WF) (hn : M.paramCount ≤ Xs.length) : (M.openVars Xs).IsLC :=
  Ty.openVars_isLC hM hn

/-- Local-closedness invariant: from a well-formed context, `Infer` yields an LC
    type and a substitution whose replacements are all LC. (Context
    well-formedness of `S.onCtx ctx` follows separately via `Subst.onCtx_wf`.) -/
theorem Infer.lc {Φ ctx e Φ' S τ} (h : Infer Φ ctx e Φ' S τ) :
    CtxWF ctx → τ.IsLC ∧ (∀ p ∈ S, p.2.IsLC) := by
  induction h with
  | primLitUnit => intro _; exact ⟨.prim, by simp⟩
  | primLitInt => intro _; exact ⟨.prim, by simp⟩
  | primLitNat => intro _; exact ⟨.prim, by simp⟩
  | primLitBool => intro _; exact ⟨.prim, by simp⟩
  | primLitStr => intro _; exact ⟨.prim, by simp⟩
  | pair ha hb iha ihb =>
    intro hctx
    obtain ⟨ha_lc, ha_s⟩ := iha hctx
    obtain ⟨hb_lc, hb_s⟩ := ihb (Subst.onCtx_wf ha_s hctx)
    refine ⟨.pair (Subst.onTy_lc hb_s ha_lc) hb_lc, ?_⟩
    intro p hp; rw [List.mem_append] at hp
    rcases hp with hp | hp
    · exact ha_s p hp
    · exact hb_s p hp
  | lambda hbody ih =>
    intro hctx
    obtain ⟨hb_lc, hb_s⟩ := ih (by
      intro M hM
      rcases List.mem_cons.mp hM with rfl | hM
      · exact ContainsBvarsUpTo.fvar
      · exact hctx M hM)
    exact ⟨.arrow (Subst.onTy_lc hb_s ContainsBvarsUpTo.fvar) hb_lc, hb_s⟩
  | app hf harg huni ihf iharg =>
    intro hctx
    obtain ⟨hf_lc, hf_s⟩ := ihf hctx
    obtain ⟨harg_lc, harg_s⟩ := iharg (Subst.onCtx_wf hf_s hctx)
    have hs3 := huni.lc (Subst.onTy_lc harg_s hf_lc) (.arrow harg_lc ContainsBvarsUpTo.fvar)
    refine ⟨Subst.onTy_lc hs3 ContainsBvarsUpTo.fvar, ?_⟩
    intro p hp; rw [List.mem_append, List.mem_append] at hp
    rcases hp with (hp | hp) | hp
    · exact hf_s p hp
    · exact harg_s p hp
    · exact hs3 p hp
  | var hlook =>
    intro hctx
    exact ⟨PolyTy.openVars_isLC (hctx _ (List.mem_of_getElem? hlook)) (by simp), by simp⟩
  | letIn hrhs hbody ihrhs ihbody =>
    intro hctx
    obtain ⟨hrhs_lc, hrhs_s⟩ := ihrhs hctx
    obtain ⟨hbody_lc, hbody_s⟩ := ihbody (by
      intro M hM
      rcases List.mem_cons.mp hM with rfl | hM
      · exact genScheme_wf hrhs_lc
      · exact (Subst.onCtx_wf hrhs_s hctx) M hM)
    refine ⟨hbody_lc, ?_⟩
    intro p hp; rw [List.mem_append] at hp
    rcases hp with hp | hp
    · exact hrhs_s p hp
    · exact hbody_s p hp

private theorem List.forall₂_self_map {α β} {R : α → β → Prop} {f : α → β} :
    ∀ {l : List α}, (∀ x ∈ l, R x (f x)) → List.Forall₂ R l (l.map f)
  | [], _ => .nil
  | _ :: _, h =>
    .cons (h _ (List.mem_cons_self ..))
      (List.forall₂_self_map (fun x hx => h x (List.mem_cons_of_mem _ hx)))

/-- Opening a scheme body (bvars `< Xs.length`) with fresh *names* is an
    instantiation by those names-as-`fvar`s. Bridges the `var` rule: the
    algorithm's `openVars` result is what the declarative `var` rule's
    `InstantiatesBy` premise demands. -/
theorem InstantiatesBy.openVars {Xs : List Nat} {n : Nat} {ty : Ty}
    (hty : ContainsBvarsUpTo n ty) (hn : n ≤ Xs.length) :
    InstantiatesBy (Xs.map (Ty.fvar ·)) ty (ty.openVars Xs) := by
  induction ty using Ty.rec_strong with
  | prim p => exact .prim
  | fvar m => exact .fvar
  | bvar i =>
    cases hty with
    | bvar hlt =>
      have hi : i < Xs.length := by omega
      simp only [Ty.openVars, Ty.instantiate, List.getElem?_eq_getElem hi, Option.elim_some]
      exact .bvar (by simp [List.getElem?_map, List.getElem?_eq_getElem hi])
  | pair a b iha ihb => cases hty with | pair ha hb => exact .pair (iha ha) (ihb hb)
  | arrow a b iha ihb => cases hty with | arrow ha hb => exact .arrow (iha ha) (ihb hb)
  | customTy nm tys ih =>
    cases hty with
    | customTy hball =>
      simp only [Ty.openVars, Ty.instantiate, TyList.instantiate_eq_map]
      exact .customTy (List.forall₂_self_map (fun t ht => ih t ht (hball t ht)))


/-! ### Cofinite-generalization machinery for the `letIn` soundness case -/

/-- A generalization candidate is, by construction, not fixed by the env. -/
theorem genVars_not_mem {env : Env} {τ : Ty} {g : Nat}
    (h : g ∈ genVars env τ) : g ∉ env.freeVars := by
  simp only [genVars, List.mem_filter] at h
  simpa using h.2

/-- A substitution whose domain avoids `Xs` commutes with opening by `Xs`. -/
theorem Subst.onTy_openVars {S : Subst} {Xs : List Nat}
    (h_lc : ∀ p ∈ S, p.2.IsLC) (h_fresh : ∀ p ∈ S, p.1 ∉ Xs) :
    ∀ {ty : Ty}, S.onTy (Ty.openVars Xs ty) = Ty.openVars Xs (S.onTy ty) := by
  induction S with
  | nil => intro ty; simp only [Subst.onTy_nil]
  | cons hd S' ih =>
    obtain ⟨Z, U⟩ := hd
    have hU : U.IsLC := h_lc (Z, U) (List.mem_cons_self ..)
    have hZ : Z ∉ Xs := h_fresh (Z, U) (List.mem_cons_self ..)
    intro ty
    simp only [Subst.onTy, Ty.substFvars]
    rw [Ty.substFvar_openVars hU hZ]
    exact ih (fun p hp => h_lc p (List.mem_cons_of_mem _ hp))
             (fun p hp => h_fresh p (List.mem_cons_of_mem _ hp))

@[simp] theorem Ty.openVars_prim {Xs : List Nat} {p : PrimTy} :
    Ty.openVars Xs (.prim p) = .prim p := rfl
@[simp] theorem Ty.openVars_pair {Xs : List Nat} {a b : Ty} :
    Ty.openVars Xs (.pair a b) = .pair (Ty.openVars Xs a) (Ty.openVars Xs b) := rfl
@[simp] theorem Ty.openVars_arrow {Xs : List Nat} {a b : Ty} :
    Ty.openVars Xs (.arrow a b) = .arrow (Ty.openVars Xs a) (Ty.openVars Xs b) := rfl

@[simp] theorem Ty.openVars_customTy {Xs : List Nat} {nm : TyName} {tys : List Ty} :
    Ty.openVars Xs (.customTy nm tys) = .customTy nm (tys.map (Ty.openVars Xs)) := by
  unfold Ty.openVars
  simp only [Ty.instantiate, TyList.instantiate_eq_map]

/-- Opening with fresh *names* `Xs` is opening with those names as `fvar` types. -/
theorem Ty.openVars_eq_openWith {Xs : List Nat} {ty : Ty} :
    Ty.openVars Xs ty = Ty.openWith (Xs.map (Ty.fvar ·)) ty := by
  unfold Ty.openVars Ty.openWith
  congr 1
  funext i
  rcases h : Xs[i]? with _ | x
  · simp [h]
  · simp [h, List.getElem?_map]

/-- `idxOf?` pinpoints the element: if it returns index `i`, then `l[i]? = a`. -/
private theorem List.getElem?_of_idxOf? {α : Type*} [BEq α] [LawfulBEq α]
    {l : List α} {a : α} {i : Nat} (h : l.idxOf? a = some i) : l[i]? = some a := by
  induction l generalizing i with
  | nil => simp [List.idxOf?_nil] at h
  | cons x xs ih =>
    rw [List.idxOf?_cons] at h
    split at h
    · rename_i hxa
      simp only [Option.some.injEq] at h
      subst h
      simp [eq_of_beq hxa]
    · obtain ⟨j, hj, rfl⟩ := Option.map_eq_some_iff.mp h
      simpa using ih hj

private theorem TyList.closeOver_eq_map (gs : List Nat) (tys : List Ty) :
    TyList.closeOver gs tys = tys.map (Ty.closeOver gs) := by
  induction tys with
  | nil => rfl
  | cons hd tl ih => simp [TyList.closeOver, ih]

/-- Closing over `gs` then opening with the *same* `gs` is the identity on an LC
    type (`gs` nodup ⇒ each closed var reopens to itself). -/
theorem Ty.openVars_closeOver_self {gs : List Nat} :
    ∀ {τ : Ty}, τ.IsLC → Ty.openVars gs (Ty.closeOver gs τ) = τ := by
  intro τ hτ
  induction τ using Ty.rec_strong with
  | prim p => rfl
  | bvar i => cases hτ with | bvar h => omega
  | fvar n =>
    rw [Ty.closeOver.eq_6]
    cases h_idx : gs.idxOf? n with
    | none => simp [Ty.openVars, Ty.instantiate]
    | some i =>
      have hgi : gs[i]? = some n := List.getElem?_of_idxOf? h_idx
      simp [Ty.openVars, Ty.instantiate, hgi]
  | pair a b iha ihb =>
    cases hτ with | pair ha hb => simp only [Ty.closeOver, Ty.openVars_pair, iha ha, ihb hb]
  | arrow a b iha ihb =>
    cases hτ with | arrow ha hb => simp only [Ty.closeOver, Ty.openVars_arrow, iha ha, ihb hb]
  | customTy nm tys ih =>
    cases hτ with
    | customTy hall =>
      simp only [Ty.closeOver, TyList.closeOver_eq_map, Ty.openVars_customTy, List.map_map]
      apply congrArg (Ty.customTy nm)
      conv_rhs => rw [← List.map_id tys]
      apply List.map_congr_left
      intro t ht
      exact ih t ht (hall t ht)

/-- The free vars of a list of `fvar`s are exactly the names. -/
theorem Ty.mem_freeVarsList_map_fvar {Xs : List Nat} {g : Nat} :
    g ∈ Ty.freeVarsList (Xs.map (Ty.fvar ·)) ↔ g ∈ Xs := by
  induction Xs with
  | nil => simp [Ty.freeVarsList]
  | cons x xs ih =>
    simp [Ty.freeVarsList, Ty.freeVars, ih]

/-- A closed-over var no longer occurs free. -/
theorem Ty.not_mem_closeOver_freeVars {gs : List Nat} {g : Nat} (hg : g ∈ gs) :
    ∀ {τ : Ty}, g ∉ (Ty.closeOver gs τ).freeVars := by
  intro τ
  induction τ using Ty.rec_strong with
  | prim p => simp [Ty.closeOver, Ty.freeVars]
  | bvar i => simp [Ty.closeOver, Ty.freeVars]
  | fvar n =>
    rw [Ty.closeOver.eq_6]
    cases h_idx : gs.idxOf? n with
    | none =>
      have hn : n ∉ gs := List.idxOf?_eq_none_iff.mp h_idx
      simp only [Ty.freeVars, List.mem_singleton]
      intro hgn; exact hn (hgn ▸ hg)
    | some i => simp [Ty.freeVars]
  | pair a b iha ihb => simp [Ty.closeOver, Ty.freeVars, List.mem_dedup, List.mem_append, iha, ihb]
  | arrow a b iha ihb => simp [Ty.closeOver, Ty.freeVars, List.mem_dedup, List.mem_append, iha, ihb]
  | customTy nm tys ih =>
    simp only [Ty.closeOver, Ty.freeVars, TyList.closeOver_eq_map]
    rw [TyList.not_mem_freeVars_iff]
    intro t' ht'
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp ht'
    exact ih t ht

/-- The full round-trip: closing over `gs` then opening with fresh `Xs` renames
    each `gs[i]` to `Xs[i]`. -/
theorem Ty.openVars_closeOver_rename {gs Xs : List Nat} {τ : Ty}
    (hτ : τ.IsLC) (h_gs_nodup : gs.Nodup) (h_len : Xs.length = gs.length)
    (h_disj : ∀ g ∈ gs, g ∉ Xs) :
    Ty.openVars Xs (Ty.closeOver gs τ)
      = Ty.substFvars (gs.zip (Xs.map (Ty.fvar ·))) τ := by
  rw [Ty.openVars_eq_openWith,
    Ty.openWith_eq_substFvars_openVars (Xs := gs) (Vs := Xs.map (Ty.fvar ·))
      ⟨by simp [h_len], fun V hV => by obtain ⟨x, _, rfl⟩ := List.mem_map.mp hV; exact .fvar⟩
      h_gs_nodup
      (fun g hg => Ty.not_mem_closeOver_freeVars hg)
      (fun g hg hc => h_disj g hg (Ty.mem_freeVarsList_map_fvar.mp hc)),
    Ty.openVars_closeOver_self hτ]

/-- The `letIn` soundness case, factored out (named binders avoid the
    inaccessible-name problem inside the `Infer.sound` induction). The cofinite
    premise is built by renaming the generalization candidates `genVars` to the
    fresh `Xs` (they are not fixed by the env, `genVars_not_mem`), then pushing
    `S₂` through (it avoids `Xs` by the cofinite `L`). -/
theorem Infer.sound_letIn {ctx : Ctx} {rhs body : Expr} {S₁ S₂ : Subst} {τ₁ τ₂ : Ty}
    (hrhs_ty : TypeOfHM (S₁.onCtx ctx) rhs τ₁) (hrhs_lc : τ₁.IsLC)
    (hbody_s : ∀ p ∈ S₂, p.2.IsLC)
    (hbody_ty : TypeOfHM (S₂.onCtx
      { (S₁.onCtx ctx) with
        env := genScheme (S₁.onCtx ctx).env τ₁ :: (S₁.onCtx ctx).env }) body τ₂) :
    TypeOfHM ((S₁ ++ S₂).onCtx ctx) (.letIn rhs body) τ₂ := by
  rw [Subst.onCtx_append]
  refine TypeOfHM.letIn (M := Subst.onPolyTy S₂ (genScheme (S₁.onCtx ctx).env τ₁))
    (L := genVars (S₁.onCtx ctx).env τ₁ ++ S₂.map Prod.fst)
    (Subst.onPolyTy_wf hbody_s (genScheme_wf hrhs_lc)) ?cofin rfl hbody_ty
  intro Xs hXfresh
  obtain ⟨hXlen, hXnodup, hXavoid⟩ := hXfresh
  have hgs_X : ∀ g ∈ genVars (S₁.onCtx ctx).env τ₁, g ∉ Xs :=
    fun g hg hc => hXavoid g hc (List.mem_append_left _ hg)
  have hX_S₂ : ∀ p ∈ S₂, p.1 ∉ Xs :=
    fun p hp hc => hXavoid p.1 hc (List.mem_append_right _ (List.mem_map.mpr ⟨p, hp, rfl⟩))
  have hrename : TypeOfHM (S₁.onCtx ctx) rhs
      (Ty.substFvars ((genVars (S₁.onCtx ctx).env τ₁).zip (Xs.map (Ty.fvar ·))) τ₁) := by
    refine TypeOfHM.typ_substs_preservation _ ?_ ?_ hrhs_ty
    · intro p hp; exact genVars_not_mem (List.of_mem_zip hp).1
    · intro p hp
      obtain ⟨x, _, hx⟩ := List.mem_map.mp (List.of_mem_zip hp).2
      exact hx ▸ ContainsBvarsUpTo.fvar
  rw [← Ty.openVars_closeOver_rename hrhs_lc genVars_nodup hXlen hgs_X] at hrename
  have hfin := TypeOfHM.onSubst S₂ hbody_s hrename
  rw [Subst.onTy_openVars hbody_s hX_S₂] at hfin
  exact hfin

/-- Soundness of `Infer` against the declarative `TypeOfHM`: applying the
    inferred substitution to the context yields a declarative typing. -/
theorem Infer.sound {Φ ctx e Φ' S τ} (h : Infer Φ ctx e Φ' S τ) :
    CtxWF ctx → TypeOfHM (S.onCtx ctx) e τ := by
  induction h with
  | primLitUnit => intro _; simp only [Subst.onCtx_nil]; exact .primLitUnit
  | primLitInt => intro _; simp only [Subst.onCtx_nil]; exact .primLitInt
  | primLitNat => intro _; simp only [Subst.onCtx_nil]; exact .primLitNat
  | primLitBool => intro _; simp only [Subst.onCtx_nil]; exact .primLitBool
  | primLitStr => intro _; simp only [Subst.onCtx_nil]; exact .primLitStr
  | pair ha hb iha ihb =>
    intro hctx
    have ha_s := (Infer.lc ha hctx).2
    have hb_s := (Infer.lc hb (Subst.onCtx_wf ha_s hctx)).2
    have ha_ty := TypeOfHM.onSubst _ hb_s (iha hctx)
    rw [Subst.onCtx_append]
    exact .pair ha_ty (ihb (Subst.onCtx_wf ha_s hctx))
  | lambda hbody ih =>
    intro hctx
    exact TypeOfHM.lambda
      (Subst.onTy_lc (Infer.lc hbody (by
        intro M hM; rcases List.mem_cons.mp hM with rfl | hM
        · exact ContainsBvarsUpTo.fvar
        · exact hctx M hM)).2 ContainsBvarsUpTo.fvar)
      rfl
      (ih (by
        intro M hM; rcases List.mem_cons.mp hM with rfl | hM
        · exact ContainsBvarsUpTo.fvar
        · exact hctx M hM))
  | app hf harg huni ihf iharg =>
    intro hctx
    obtain ⟨hf_lc, hf_s⟩ := Infer.lc hf hctx
    have hctx1 := Subst.onCtx_wf hf_s hctx
    obtain ⟨harg_lc, harg_s⟩ := Infer.lc harg hctx1
    have hs3 := huni.lc (Subst.onTy_lc harg_s hf_lc) (.arrow harg_lc ContainsBvarsUpTo.fvar)
    have f2 := TypeOfHM.onSubst _ hs3 (TypeOfHM.onSubst _ harg_s (ihf hctx))
    have a1 := TypeOfHM.onSubst _ hs3 (iharg hctx1)
    have hueq := huni.unifies
    simp only [Unifies, Subst.onTy_arrow] at hueq
    rw [hueq] at f2
    rw [Subst.onCtx_append, Subst.onCtx_append]
    exact .app f2 a1
  | var hlook =>
    intro hctx
    simp only [Subst.onCtx_nil]
    refine TypeOfHM.var hlook (fun tyArg ht => ?_)
      (InstantiatesBy.openVars (hctx _ (List.mem_of_getElem? hlook)) (by simp))
    obtain ⟨x, _, rfl⟩ := List.mem_map.mp ht
    exact .fvar
  | letIn hrhs hbody ihrhs ihbody =>
    intro hctx
    obtain ⟨hrhs_lc, hrhs_s⟩ := Infer.lc hrhs hctx
    exact Infer.sound_letIn (ihrhs hctx) hrhs_lc
      (Infer.lc hbody (by
        intro M hM; rcases List.mem_cons.mp hM with rfl | hM
        · exact genScheme_wf hrhs_lc
        · exact (Subst.onCtx_wf hrhs_s hctx) M hM)).2
      (ihbody (by
        intro M hM; rcases List.mem_cons.mp hM with rfl | hM
        · exact genScheme_wf hrhs_lc
        · exact (Subst.onCtx_wf hrhs_s hctx) M hM))


/-! ## Algorithmic phase, step 2b: completeness (principality) scaffolding

Foundations for `Infer.complete`, independent of how the residual-substitution
obstruction is resolved. -/

/-- All free type vars of `τ` are below `Φ`. The `fvar` analogue of
    `ContainsBvarsUpTo`; clean to push through substitution. -/
inductive Ty.BelowFvars (Φ : Nat) : Ty → Prop
  | prim : Ty.BelowFvars Φ (.prim p)
  | pair : Ty.BelowFvars Φ a → Ty.BelowFvars Φ b → Ty.BelowFvars Φ (.pair a b)
  | arrow : Ty.BelowFvars Φ a → Ty.BelowFvars Φ b → Ty.BelowFvars Φ (.arrow a b)
  | bvar : Ty.BelowFvars Φ (.bvar i)
  | fvar : i < Φ → Ty.BelowFvars Φ (.fvar i)
  | customTy : (∀ t ∈ tys, Ty.BelowFvars Φ t) → Ty.BelowFvars Φ (.customTy nm tys)

theorem Ty.BelowFvars.mono {Φ Φ' : Nat} {τ : Ty} (hle : Φ ≤ Φ')
    (h : Ty.BelowFvars Φ τ) : Ty.BelowFvars Φ' τ := by
  induction h with
  | prim => exact .prim
  | pair _ _ iha ihb => exact .pair iha ihb
  | arrow _ _ iha ihb => exact .arrow iha ihb
  | bvar => exact .bvar
  | fvar hlt => exact .fvar (by omega)
  | customTy _ ih => exact .customTy (fun t ht => ih t ht)

/-- `substFvar` by a below-`Φ` type preserves below-`Φ`. -/
theorem Ty.BelowFvars.substFvar {Φ Z : Nat} {U τ : Ty}
    (hU : Ty.BelowFvars Φ U) (h : Ty.BelowFvars Φ τ) :
    Ty.BelowFvars Φ (Ty.substFvar Z U τ) := by
  induction τ using Ty.rec_strong with
  | prim _ => exact .prim
  | pair a b iha ihb => cases h with | pair ha hb => exact .pair (iha ha) (ihb hb)
  | arrow a b iha ihb => cases h with | arrow ha hb => exact .arrow (iha ha) (ihb hb)
  | bvar i => simp only [Ty.substFvar]; exact .bvar
  | fvar m =>
    simp only [Ty.substFvar]
    by_cases hm : m = Z
    · simp only [if_pos hm]; exact hU
    · simp only [if_neg hm]; cases h with | fvar hlt => exact .fvar hlt
  | customTy nm tys ih =>
    cases h with
    | customTy hall =>
      simp only [Ty.substFvar]
      apply Ty.BelowFvars.customTy
      rw [TyList.substFvar_eq_map]
      intro t ht
      obtain ⟨t0, ht0, rfl⟩ := List.mem_map.mp ht
      exact ih t0 ht0 (hall t0 ht0)

/-- A whole substitution with below-`Φ` replacements preserves below-`Φ`. -/
theorem Subst.onTy_belowFvars {Φ : Nat} {S : Subst} (hS : ∀ p ∈ S, Ty.BelowFvars Φ p.2) :
    ∀ {τ : Ty}, Ty.BelowFvars Φ τ → Ty.BelowFvars Φ (S.onTy τ) := by
  induction S with
  | nil => intro τ hτ; simpa using hτ
  | cons hd S' ih =>
    obtain ⟨Z, U⟩ := hd
    have hU : Ty.BelowFvars Φ U := hS (Z, U) (List.mem_cons_self ..)
    have hS' : ∀ p ∈ S', Ty.BelowFvars Φ p.2 := fun p hp => hS p (List.mem_cons_of_mem _ hp)
    intro τ hτ
    rw [show ((Z, U) :: S') = [(Z, U)] ++ S' from rfl, Subst.onTy_append]
    exact ih hS' (Ty.BelowFvars.substFvar hU hτ)

/-- Bridge to the `freeVars` characterisation: a below-`Φ` type's free vars are
    all `< Φ` (so any `w ≥ Φ` is fresh for it). -/
theorem Ty.BelowFvars.mem_lt {Φ : Nat} {τ : Ty} (h : Ty.BelowFvars Φ τ) :
    ∀ v ∈ τ.freeVars, v < Φ := by
  induction h with
  | prim => intro v hv; simp [Ty.freeVars] at hv
  | bvar => intro v hv; simp [Ty.freeVars] at hv
  | fvar hlt => intro v hv; simp only [Ty.freeVars, List.mem_singleton] at hv; exact hv ▸ hlt
  | pair _ _ iha ihb =>
    intro v hv; simp only [Ty.freeVars, List.mem_dedup, List.mem_append] at hv
    rcases hv with h | h
    · exact iha v h
    · exact ihb v h
  | arrow _ _ iha ihb =>
    intro v hv; simp only [Ty.freeVars, List.mem_dedup, List.mem_append] at hv
    rcases hv with h | h
    · exact iha v h
    · exact ihb v h
  | customTy hall ih =>
    intro v hv
    simp only [Ty.freeVars] at hv
    by_contra hge
    refine (TyList.not_mem_freeVars_iff.mpr ?_) hv
    intro t ht hc
    exact hge (ih t ht v hc)

/-- Every scheme body of `ctx` has its free type vars below the frontier `Φ`
    (the "new_tv" discipline: vars `Infer` allocates `≥ Φ` are genuinely fresh). -/
def CtxBelow (Φ : Nat) (ctx : Ctx) : Prop := ∀ M ∈ ctx.env, Ty.BelowFvars Φ M.body

/-- A whole substitution preserves context-below (with frontier growth). -/
theorem Subst.onCtx_below {Φ Φ' : Nat} {S : Subst} {ctx : Ctx}
    (hS : ∀ p ∈ S, Ty.BelowFvars Φ' p.2) (hle : Φ ≤ Φ') (hb : CtxBelow Φ ctx) :
    CtxBelow Φ' (S.onCtx ctx) := by
  intro M hM
  simp only [Subst.onCtx, Subst.onEnv] at hM
  obtain ⟨M0, hM0, rfl⟩ := List.mem_map.mp hM
  exact Subst.onTy_belowFvars hS ((hb M0 hM0).mono hle)

/-- The `k` fresh names allocated from frontier `Φ` are all `< Φ + k`. -/
theorem freshVars_lt {Φ k : Nat} : ∀ x ∈ freshVars Φ k, x < Φ + k := by
  intro x hx
  simp only [freshVars, List.mem_map, List.mem_range] at hx
  obtain ⟨i, hi, rfl⟩ := hx
  omega

/-- Opening a below-`Φ` type with fresh names all `< Φ` stays below-`Φ`. -/
theorem Ty.openVars_belowFvars {Φ : Nat} {Xs : List Nat} {τ : Ty}
    (hτ : Ty.BelowFvars Φ τ) (hXs : ∀ x ∈ Xs, x < Φ) :
    Ty.BelowFvars Φ (Ty.openVars Xs τ) := by
  induction τ using Ty.rec_strong with
  | prim p => exact .prim
  | pair a b iha ihb => cases hτ with | pair ha hb => exact .pair (iha ha) (ihb hb)
  | arrow a b iha ihb => cases hτ with | arrow ha hb => exact .arrow (iha ha) (ihb hb)
  | bvar i =>
    simp only [Ty.openVars, Ty.instantiate]
    cases h : Xs[i]? with
    | none => exact .bvar
    | some x => exact .fvar (hXs x (List.mem_of_getElem? h))
  | fvar n => cases hτ with | fvar hlt => exact .fvar hlt
  | customTy nm tys ih =>
    cases hτ with
    | customTy hall =>
      simp only [Ty.openVars_customTy]
      apply Ty.BelowFvars.customTy
      intro t' ht'
      obtain ⟨t, ht, rfl⟩ := List.mem_map.mp ht'
      exact ih t ht (hall t ht)

mutual

/-- Unifying two below-`Φ` monotypes yields a below-`Φ` substitution. -/
theorem UnifyRel.belowFvars {Φ : Nat} : {a b : Ty} → {S : Subst} → UnifyRel a b S →
    Ty.BelowFvars Φ a → Ty.BelowFvars Φ b → ∀ p ∈ S, Ty.BelowFvars Φ p.2
  | _, _, _, .prim, _, _ => by simp
  | _, _, _, .fvarRefl, _, _ => by simp
  | _, _, _, .fvarL _ _, _, hb => by
    intro p hp; rw [List.mem_singleton] at hp; subst hp; exact hb
  | _, _, _, .fvarR _ _, ha, _ => by
    intro p hp; rw [List.mem_singleton] at hp; subst hp; exact ha
  | _, _, _, .arrow h₁ h₂, ha, hb => by
    cases ha with | arrow ha_a ha_b => cases hb with | arrow hb_c hb_d =>
    have h1lc := UnifyRel.belowFvars h₁ ha_a hb_c
    have h2lc := UnifyRel.belowFvars h₂ (Subst.onTy_belowFvars h1lc ha_b) (Subst.onTy_belowFvars h1lc hb_d)
    intro p hp; rw [List.mem_append] at hp
    rcases hp with hp | hp
    · exact h1lc p hp
    · exact h2lc p hp
  | _, _, _, .pair h₁ h₂, ha, hb => by
    cases ha with | pair ha_a ha_b => cases hb with | pair hb_c hb_d =>
    have h1lc := UnifyRel.belowFvars h₁ ha_a hb_c
    have h2lc := UnifyRel.belowFvars h₂ (Subst.onTy_belowFvars h1lc ha_b) (Subst.onTy_belowFvars h1lc hb_d)
    intro p hp; rw [List.mem_append] at hp
    rcases hp with hp | hp
    · exact h1lc p hp
    · exact h2lc p hp
  | _, _, _, .customTy hl, ha, hb => by
    cases ha with | customTy ha_all => cases hb with | customTy hb_all =>
    exact UnifyRelList.belowFvars hl ha_all hb_all

/-- List version: unifying two below-`Φ` type lists yields a below-`Φ` substitution. -/
theorem UnifyRelList.belowFvars {Φ : Nat} : {ts₁ ts₂ : List Ty} → {S : Subst} → UnifyRelList ts₁ ts₂ S →
    (∀ t ∈ ts₁, Ty.BelowFvars Φ t) → (∀ t ∈ ts₂, Ty.BelowFvars Φ t) → ∀ p ∈ S, Ty.BelowFvars Φ p.2
  | _, _, _, .nil, _, _ => by simp
  | _, _, _, @UnifyRelList.cons t₁ t₂ ts₁ ts₂ S₁ S₂ h₁ ht, hts₁, hts₂ => by
    have ht1 : Ty.BelowFvars Φ t₁ := hts₁ t₁ (List.mem_cons_self ..)
    have ht2 : Ty.BelowFvars Φ t₂ := hts₂ t₂ (List.mem_cons_self ..)
    have h1lc := UnifyRel.belowFvars h₁ ht1 ht2
    have hmap₁ : ∀ t ∈ ts₁.map S₁.onTy, Ty.BelowFvars Φ t := by
      intro t htm; obtain ⟨t0, ht0, rfl⟩ := List.mem_map.mp htm
      exact Subst.onTy_belowFvars h1lc (hts₁ t0 (List.mem_cons_of_mem _ ht0))
    have hmap₂ : ∀ t ∈ ts₂.map S₁.onTy, Ty.BelowFvars Φ t := by
      intro t htm; obtain ⟨t0, ht0, rfl⟩ := List.mem_map.mp htm
      exact Subst.onTy_belowFvars h1lc (hts₂ t0 (List.mem_cons_of_mem _ ht0))
    have h2lc := UnifyRelList.belowFvars ht hmap₁ hmap₂
    intro p hp; rw [List.mem_append] at hp
    rcases hp with hp | hp
    · exact h1lc p hp
    · exact h2lc p hp

end

/-- Closing over `gs` only removes free vars, so it preserves below-`Φ`. -/
theorem Ty.BelowFvars.closeOver {Φ : Nat} {gs : List Nat} :
    ∀ {τ : Ty}, Ty.BelowFvars Φ τ → Ty.BelowFvars Φ (Ty.closeOver gs τ) := by
  intro τ h
  induction τ using Ty.rec_strong with
  | prim p => exact .prim
  | bvar i => exact .bvar
  | fvar n =>
    rw [Ty.closeOver.eq_6]
    cases h_idx : gs.idxOf? n with
    | none => cases h with | fvar hlt => exact .fvar hlt
    | some i => exact .bvar
  | pair a b iha ihb => cases h with | pair ha hb => exact .pair (iha ha) (ihb hb)
  | arrow a b iha ihb => cases h with | arrow ha hb => exact .arrow (iha ha) (ihb hb)
  | customTy nm tys ih =>
    cases h with
    | customTy hall =>
      simp only [Ty.closeOver, TyList.closeOver_eq_map]
      apply Ty.BelowFvars.customTy
      intro t' ht'; obtain ⟨t, ht, rfl⟩ := List.mem_map.mp ht'
      exact ih t ht (hall t ht)

/-! Regularity: any declaratively-typed term has a locally-closed type. (Each
    rule produces an LC type; `var`/`ctor` via `InstantiatesBy.preserves_bvars`
    on LC `tyArgs`, `lambda` via the LC param premise, the rest by induction.) -/
mutual
theorem TypeOfHM.regular : {ctx : Ctx} → {e : Expr} → {τ : Ty} →
    TypeOfHM ctx e τ → τ.IsLC
  | _, _, _, .primLitUnit => .prim
  | _, _, _, .primLitInt => .prim
  | _, _, _, .primLitNat => .prim
  | _, _, _, .primLitBool => .prim
  | _, _, _, .primLitStr => .prim
  | _, _, _, .pair ha hb => .pair (TypeOfHM.regular ha) (TypeOfHM.regular hb)
  | _, _, _, .lambda hpc _ hbody => .arrow hpc (TypeOfHM.regular hbody)
  | _, _, _, .app hf _ => by
    have := TypeOfHM.regular hf; cases this with | arrow _ hret => exact hret
  | _, _, _, .letIn _ _ _ hbody => TypeOfHM.regular hbody
  | _, _, _, .letPairIn _ _ _ _ _ hbody => TypeOfHM.regular hbody
  | _, _, _, .var _ htyargs hinst => InstantiatesBy.preserves_bvars htyargs hinst
  | _, _, _, .ctor _ htyargs hinst => InstantiatesBy.preserves_bvars htyargs hinst
  | _, _, _, @TypeOfHM.match_ _ _ _ _ branches _ hscrut hne hbrs => by
    obtain ⟨hd, tl, rfl⟩ := List.exists_cons_of_ne_nil hne
    exact TypeOfMatchBranch.regular (hbrs hd (List.mem_cons_self ..))

theorem TypeOfMatchBranch.regular : {ctx : Ctx} → {br : MatchPattern × Expr} →
    {tn : TyName} → {ta : List Ty} → {rt : Ty} →
    TypeOfMatchBranch ctx br tn ta rt → rt.IsLC
  | _, _, _, _, _, .mk _ _ _ _ _ _ _ hbody => TypeOfHM.regular hbody
end

/-- Frontier invariant: from a context whose schemes are below the input frontier
    `Φ`, `Infer` yields a type and a substitution whose replacements are all below
    the *output* frontier `Φ'` (so `mono` everything up to `Φ'`). (Named
    `belowFvars` rather than `below`, since `Infer.below` is reserved by Lean's
    auto-generated course-of-values recursor for the `Infer` inductive.) -/
theorem Infer.belowFvars {Φ ctx e Φ' S τ} (h : Infer Φ ctx e Φ' S τ) :
    CtxBelow Φ ctx → Ty.BelowFvars Φ' τ ∧ (∀ p ∈ S, Ty.BelowFvars Φ' p.2) := by
  induction h with
  | primLitUnit => intro _; exact ⟨.prim, by simp⟩
  | primLitInt => intro _; exact ⟨.prim, by simp⟩
  | primLitNat => intro _; exact ⟨.prim, by simp⟩
  | primLitBool => intro _; exact ⟨.prim, by simp⟩
  | primLitStr => intro _; exact ⟨.prim, by simp⟩
  | pair ha hb iha ihb =>
    intro hctx
    obtain ⟨ha_τ, ha_s⟩ := iha hctx
    have hctx1 := Subst.onCtx_below ha_s (Infer.frontier_le ha) hctx
    obtain ⟨hb_τ, hb_s⟩ := ihb hctx1
    have hle := Infer.frontier_le hb
    refine ⟨.pair (Subst.onTy_belowFvars hb_s (ha_τ.mono hle)) hb_τ, ?_⟩
    intro p hp; rw [List.mem_append] at hp
    rcases hp with hp | hp
    · exact (ha_s p hp).mono hle
    · exact hb_s p hp
  | lambda hbody ih =>
    intro hctx
    obtain ⟨hb_τ, hb_s⟩ := ih (by
      intro M hM
      rcases List.mem_cons.mp hM with rfl | hM
      · exact .fvar (by omega)
      · exact (hctx M hM).mono (by omega))
    refine ⟨.arrow (Subst.onTy_belowFvars hb_s (.fvar ?_)) hb_τ, hb_s⟩
    have := Infer.frontier_le hbody
    omega
  | app hf harg huni ihf iharg =>
    intro hctx
    obtain ⟨hf_τ, hf_s⟩ := ihf hctx
    have hctx1 := Subst.onCtx_below hf_s (Infer.frontier_le hf) hctx
    obtain ⟨harg_τ, harg_s⟩ := iharg hctx1
    have h1 := Infer.frontier_le hf
    have h2 := Infer.frontier_le harg
    refine ⟨Subst.onTy_belowFvars
        (UnifyRel.belowFvars huni
          (Subst.onTy_belowFvars (fun p hp => (harg_s p hp).mono (by omega)) (hf_τ.mono (by omega)))
          (.arrow (harg_τ.mono (by omega)) (.fvar (by omega))))
        (.fvar (by omega)), ?_⟩
    intro p hp; rw [List.mem_append, List.mem_append] at hp
    rcases hp with (hp | hp) | hp
    · exact (hf_s p hp).mono (by omega)
    · exact (harg_s p hp).mono (by omega)
    · exact UnifyRel.belowFvars huni
        (Subst.onTy_belowFvars (fun p hp => (harg_s p hp).mono (by omega)) (hf_τ.mono (by omega)))
        (.arrow (harg_τ.mono (by omega)) (.fvar (by omega))) p hp
  | var hlook =>
    intro hctx
    refine ⟨?_, by simp⟩
    exact Ty.openVars_belowFvars ((hctx _ (List.mem_of_getElem? hlook)).mono (by omega))
      (fun x hx => by have := freshVars_lt x hx; omega)
  | letIn hrhs hbody ihrhs ihbody =>
    intro hctx
    obtain ⟨hr_τ, hr_s⟩ := ihrhs hctx
    have hctx1 := Subst.onCtx_below hr_s (Infer.frontier_le hrhs) hctx
    obtain ⟨hb_τ, hb_s⟩ := ihbody (by
      intro M hM
      rcases List.mem_cons.mp hM with rfl | hM
      · exact hr_τ.closeOver
      · exact hctx1 M hM)
    refine ⟨hb_τ, ?_⟩
    intro p hp; rw [List.mem_append] at hp
    rcases hp with hp | hp
    · exact (hr_s p hp).mono (Infer.frontier_le hbody)
    · exact hb_s p hp


/-! ### Completeness foundations: core fragment + substitution agreement

`Infer` (v1) covers the let-polymorphic core, so principality is stated for
core expressions; it extends once `ctor`/`match_`/`letPairIn` are added to
`Infer`. The agreement lemmas let us swap one substitution for another that
agrees on the in-scope (`< Φ`) variables. -/

/-- The expressions `Infer` (v1) handles: the let-polymorphic core. -/
inductive Expr.Core : Expr → Prop
  | primLit : Expr.Core (.primLit p)
  | pair : Expr.Core a → Expr.Core b → Expr.Core (.pair a b)
  | lambda : Expr.Core body → Expr.Core (.lambda body)
  | app : Expr.Core f → Expr.Core arg → Expr.Core (.app f arg)
  | var : Expr.Core (.var i)
  | letIn : Expr.Core rhs → Expr.Core body → Expr.Core (.letIn rhs body)

/-- Two substitutions agreeing on all vars `< Φ` act identically on a
    below-`Φ` type. -/
theorem Subst.onTy_congr {Φ : Nat} {S T : Subst}
    (hag : ∀ v, v < Φ → S.onTy (.fvar v) = T.onTy (.fvar v)) :
    ∀ {τ : Ty}, Ty.BelowFvars Φ τ → S.onTy τ = T.onTy τ := by
  intro τ hτ
  induction τ using Ty.rec_strong with
  | prim p => simp only [Subst.onTy_prim]
  | bvar i => simp only [Subst.onTy_bvar]
  | fvar n => cases hτ with | fvar hlt => exact hag n hlt
  | pair a b iha ihb => cases hτ with | pair ha hb => simp only [Subst.onTy_pair, iha ha, ihb hb]
  | arrow a b iha ihb => cases hτ with | arrow ha hb => simp only [Subst.onTy_arrow, iha ha, ihb hb]
  | customTy nm tys ih =>
    cases hτ with
    | customTy hall =>
      simp only [Subst.onTy_customTy]
      apply congrArg (Ty.customTy nm)
      apply List.map_congr_left
      intro t ht
      exact ih t ht (hall t ht)

/-- Agreeing substitutions act identically on a below-`Φ` context. -/
theorem Subst.onCtx_congr {Φ : Nat} {S T : Subst} {ctx : Ctx}
    (hag : ∀ v, v < Φ → S.onTy (.fvar v) = T.onTy (.fvar v)) (hb : CtxBelow Φ ctx) :
    S.onCtx ctx = T.onCtx ctx := by
  simp only [Subst.onCtx, Subst.onEnv]
  congr 1
  apply List.map_congr_left
  intro M hM
  simp only [Subst.onPolyTy, Subst.onTy_congr hag (hb M hM)]


/-! ### Principality (completeness) — per-expression statement + case lemmas

`Infer.CompleteAt e` packages the principality property at a single expression,
abstracted over the frontier `Φ`, context `ctx`, input specialization `S₀`, and
declarative type `τ₀`. Each syntactic form gets its own case lemma (taking the
sub-expressions' `CompleteAt` as hypotheses, exactly the shape produced by
inducting on `Expr.Core`); `Infer.complete` then just composes them. Keeping the
universally-quantified `Φ ctx S₀ τ₀` inside the predicate means each case lemma
is independently stated and verifiable. -/

/-- The principality property at `e`: for *any* declarative typing of `e` under
    an LC specialization `S₀` of a WF, frontier-bounded context, `Infer`
    succeeds with `(S, τ)` and the typing factors through it via an LC residual
    `R` (`S₀ = R ∘ S` below the frontier, `τ₀ = R.onTy τ`). -/
def Infer.CompleteAt (e : Expr) : Prop :=
  ∀ {Φ : Nat} {ctx : Ctx} {S₀ : Subst} {τ₀ : Ty},
    CtxWF ctx → CtxBelow Φ ctx → (∀ p ∈ S₀, p.2.IsLC) →
    TypeOfHM (S₀.onCtx ctx) e τ₀ →
    ∃ Φ' S τ R,
      Infer Φ ctx e Φ' S τ ∧
      (∀ v, v < Φ → S₀.onTy (.fvar v) = (S ++ R).onTy (.fvar v)) ∧
      τ₀ = R.onTy τ ∧
      (∀ p ∈ R, p.2.IsLC)

/-- Principality, primitive-literal case: `Infer` returns the literal's type
    with the empty substitution; the residual is `S₀` unchanged. -/
theorem Infer.complete_prim {p : PrimLitExpr} : Infer.CompleteAt (.primLit p) := by
  intro Φ ctx S₀ τ₀ _ _ hS₀ hty
  cases hty with
  | primLitUnit => exact ⟨Φ, [], _, S₀, .primLitUnit, fun v _ => by rw [List.nil_append], by simp, hS₀⟩
  | primLitInt  => exact ⟨Φ, [], _, S₀, .primLitInt,  fun v _ => by rw [List.nil_append], by simp, hS₀⟩
  | primLitNat  => exact ⟨Φ, [], _, S₀, .primLitNat,  fun v _ => by rw [List.nil_append], by simp, hS₀⟩
  | primLitBool => exact ⟨Φ, [], _, S₀, .primLitBool, fun v _ => by rw [List.nil_append], by simp, hS₀⟩
  | primLitStr  => exact ⟨Φ, [], _, S₀, .primLitStr,  fun v _ => by rw [List.nil_append], by simp, hS₀⟩

/-- Principality, pair case. No fresh variables are introduced here, so no
    renaming is needed: the residual `R₁` from the first component becomes the
    specialization for the second (it reproduces `S₀` on `ctx` by the agreement
    clause + `onCtx_congr`), and the second residual `R₂` serves as the pair's
    residual. The first component's type is transported across the agreement via
    `onTy_congr` (it is below the intermediate frontier `Φ₁`). -/
theorem Infer.complete_pair {a b : Expr}
    (iha : Infer.CompleteAt a) (ihb : Infer.CompleteAt b) :
    Infer.CompleteAt (.pair a b) := by
  intro Φ ctx S₀ τ₀ hwf hbelow hS₀ hty
  cases hty with
  | pair hta htb =>
    obtain ⟨Φ₁, S₁, τa, R₁, hinfa, haga, htya, hR₁⟩ := iha hwf hbelow hS₀ hta
    have hS₁ : ∀ p ∈ S₁, p.2.IsLC := (Infer.lc hinfa hwf).2
    have hle : Φ ≤ Φ₁ := Infer.frontier_le hinfa
    have hbelowτa : Ty.BelowFvars Φ₁ τa := (Infer.belowFvars hinfa hbelow).1
    have hbelowS₁ : ∀ p ∈ S₁, Ty.BelowFvars Φ₁ p.2 := (Infer.belowFvars hinfa hbelow).2
    have hwf₁ : CtxWF (S₁.onCtx ctx) := Subst.onCtx_wf hS₁ hwf
    have hbelow₁ : CtxBelow Φ₁ (S₁.onCtx ctx) := Subst.onCtx_below hbelowS₁ hle hbelow
    have hctx_eq : R₁.onCtx (S₁.onCtx ctx) = S₀.onCtx ctx := by
      rw [← Subst.onCtx_append]
      exact Subst.onCtx_congr (fun v hv => (haga v hv).symm) hbelow
    have htb' : TypeOfHM (R₁.onCtx (S₁.onCtx ctx)) b _ := hctx_eq ▸ htb
    obtain ⟨Φ₂, S₂, τb, R₂, hinfb, hagb, htyb, hR₂⟩ := ihb hwf₁ hbelow₁ hR₁ htb'
    refine ⟨Φ₂, S₁ ++ S₂, .pair (S₂.onTy τa) τb, R₂, .pair hinfa hinfb, ?_, ?_, hR₂⟩
    · intro v hv
      have hbv : Ty.BelowFvars Φ₁ (S₁.onTy (.fvar v)) :=
        Subst.onTy_belowFvars hbelowS₁ (.fvar (by omega))
      calc S₀.onTy (.fvar v)
          = (S₁ ++ R₁).onTy (.fvar v) := haga v hv
        _ = R₁.onTy (S₁.onTy (.fvar v)) := by rw [Subst.onTy_append]
        _ = (S₂ ++ R₂).onTy (S₁.onTy (.fvar v)) := Subst.onTy_congr hagb hbv
        _ = ((S₁ ++ S₂) ++ R₂).onTy (.fvar v) := by
              rw [List.append_assoc, Subst.onTy_append S₁ (S₂ ++ R₂)]
    · rw [Subst.onTy_pair]
      refine congrArg₂ Ty.pair ?_ htyb
      rw [htya, ← Subst.onTy_append]
      exact Subst.onTy_congr hagb hbelowτa


/-! ### Injective renaming of free type variables (principality binder cases)

The list-substitution residual hits an obstruction at fresh binders: a clean
override of `S₀` mapping the fresh var to the declarative type is unrealisable as
a `List` once the fresh var occurs in `S₀`'s range (or the declarative
instantiation types). We dodge it by α-renaming the declarative derivation with a
*swap* `Φ ↔ W` (`W` fresh) so the clash disappears, then mapping the residual
back. `Ty.rename` applies a variable relabelling; the swap is realised as the
3-element list `swapSubst` (with a fresh intermediate `c`) so the existing
`TypeOfHM.onSubst` carries the renaming through the derivation. -/

mutual
/-- Relabel every free type variable by `f`. An α-renaming when `f` is injective. -/
def Ty.rename (f : Nat → Nat) : Ty → Ty
  | .prim p          => .prim p
  | .pair a b        => .pair (a.rename f) (b.rename f)
  | .arrow a b       => .arrow (a.rename f) (b.rename f)
  | .bvar i          => .bvar i
  | .fvar n          => .fvar (f n)
  | .customTy nm tys => .customTy nm (TyList.rename f tys)

private def TyList.rename (f : Nat → Nat) : List Ty → List Ty
  | []       => []
  | hd :: tl => hd.rename f :: TyList.rename f tl
end

theorem TyList.rename_eq_map (f : Nat → Nat) (tys : List Ty) :
    TyList.rename f tys = tys.map (Ty.rename f) := by
  induction tys with
  | nil => rfl
  | cons hd tl ih => simp only [TyList.rename, List.map_cons, ih]

@[simp] theorem Ty.rename_prim {f : Nat → Nat} {p : PrimTy} :
    Ty.rename f (.prim p) = .prim p := rfl
@[simp] theorem Ty.rename_bvar {f : Nat → Nat} {i : Nat} :
    Ty.rename f (.bvar i) = .bvar i := rfl
@[simp] theorem Ty.rename_fvar {f : Nat → Nat} {n : Nat} :
    Ty.rename f (.fvar n) = .fvar (f n) := rfl
@[simp] theorem Ty.rename_pair {f : Nat → Nat} {a b : Ty} :
    Ty.rename f (.pair a b) = .pair (Ty.rename f a) (Ty.rename f b) := rfl
@[simp] theorem Ty.rename_arrow {f : Nat → Nat} {a b : Ty} :
    Ty.rename f (.arrow a b) = .arrow (Ty.rename f a) (Ty.rename f b) := rfl
@[simp] theorem Ty.rename_customTy {f : Nat → Nat} {nm : TyName} {tys : List Ty} :
    Ty.rename f (.customTy nm tys) = .customTy nm (tys.map (Ty.rename f)) := by
  simp [Ty.rename, TyList.rename_eq_map]

/-- Renaming composes. -/
theorem Ty.rename_comp (f g : Nat → Nat) (τ : Ty) :
    Ty.rename g (Ty.rename f τ) = Ty.rename (g ∘ f) τ := by
  induction τ using Ty.rec_strong with
  | prim p => rfl
  | pair a b iha ihb => simp only [Ty.rename_pair, iha, ihb]
  | arrow a b iha ihb => simp only [Ty.rename_arrow, iha, ihb]
  | bvar i => rfl
  | fvar n => rfl
  | customTy nm tys ih =>
    simp only [Ty.rename_customTy, List.map_map, Ty.customTy.injEq, true_and]
    apply List.map_congr_left
    intro t ht
    exact ih t ht

/-- Renaming by a function that fixes `τ`'s free vars is the identity. -/
theorem Ty.rename_eq_self {f : Nat → Nat} {τ : Ty}
    (h : ∀ v ∈ τ.freeVars, f v = v) : Ty.rename f τ = τ := by
  induction τ using Ty.rec_strong with
  | prim _ => rfl
  | pair a b ih_a ih_b =>
    simp only [Ty.rename_pair, Ty.pair.injEq]
    refine ⟨ih_a (fun v hv => h v ?_), ih_b (fun v hv => h v ?_)⟩
    · simp only [Ty.freeVars, List.mem_dedup, List.mem_append]; exact Or.inl hv
    · simp only [Ty.freeVars, List.mem_dedup, List.mem_append]; exact Or.inr hv
  | arrow a b ih_a ih_b =>
    simp only [Ty.rename_arrow, Ty.arrow.injEq]
    refine ⟨ih_a (fun v hv => h v ?_), ih_b (fun v hv => h v ?_)⟩
    · simp only [Ty.freeVars, List.mem_dedup, List.mem_append]; exact Or.inl hv
    · simp only [Ty.freeVars, List.mem_dedup, List.mem_append]; exact Or.inr hv
  | bvar _ => rfl
  | fvar n =>
    have hn := h n (by simp [Ty.freeVars])
    simp only [Ty.rename_fvar, hn]
  | customTy nm tys ih =>
    simp only [Ty.rename_customTy, Ty.customTy.injEq, true_and]
    conv_rhs => rw [← List.map_id tys]
    apply List.map_congr_left
    intro t ht
    exact ih t ht (fun v hv => h v (TyList.mem_freeVars_of_mem ht hv))

/-- Renaming preserves the bvar bound (it only touches `fvar`s). -/
theorem Ty.rename_containsBvars {f : Nat → Nat} {n : Nat} {τ : Ty}
    (h : ContainsBvarsUpTo n τ) : ContainsBvarsUpTo n (Ty.rename f τ) := by
  induction τ using Ty.rec_strong with
  | prim p => exact .prim
  | bvar i => cases h with | bvar hlt => exact .bvar hlt
  | fvar m => exact .fvar
  | pair a b iha ihb => cases h with | pair ha hb => exact .pair (iha ha) (ihb hb)
  | arrow a b iha ihb => cases h with | arrow ha hb => exact .arrow (iha ha) (ihb hb)
  | customTy nm tys ih =>
    cases h with
    | customTy hall =>
      simp only [Ty.rename_customTy]
      apply ContainsBvarsUpTo.customTy
      intro t ht
      obtain ⟨t0, ht0, rfl⟩ := List.mem_map.mp ht
      exact ih t0 ht0 (hall t0 ht0)

/-- Renaming preserves local-closedness. -/
theorem Ty.rename_isLC {f : Nat → Nat} {τ : Ty} (h : τ.IsLC) :
    (Ty.rename f τ).IsLC := Ty.rename_containsBvars h

/-- Renaming by an injective `f` commutes with single-var substitution. -/
theorem Ty.rename_substFvar {f : Nat → Nat} (hf : Function.Injective f)
    (z : Nat) (u t : Ty) :
    Ty.rename f (Ty.substFvar z u t)
      = Ty.substFvar (f z) (Ty.rename f u) (Ty.rename f t) := by
  induction t using Ty.rec_strong with
  | prim p => rfl
  | pair a b iha ihb => simp only [Ty.substFvar, Ty.rename_pair, iha, ihb]
  | arrow a b iha ihb => simp only [Ty.substFvar, Ty.rename_arrow, iha, ihb]
  | bvar i => rfl
  | fvar m =>
    simp only [Ty.substFvar, Ty.rename_fvar]
    by_cases hm : m = z
    · rw [if_pos hm, if_pos (congrArg f hm)]
    · rw [if_neg hm, if_neg (fun heq => hm (hf heq)), Ty.rename_fvar]
  | customTy nm tys ih =>
    simp only [Ty.substFvar, TyList.substFvar_eq_map, Ty.rename_customTy, List.map_map,
               Ty.customTy.injEq, true_and]
    apply List.map_congr_left
    intro t0 ht0
    exact ih t0 ht0

/-- Renaming commutes with opening (the opened names get renamed too). -/
theorem Ty.rename_openVars {f : Nat → Nat} {Xs : List Nat} {t : Ty} :
    Ty.rename f (Ty.openVars Xs t) = Ty.openVars (Xs.map f) (Ty.rename f t) := by
  induction t using Ty.rec_strong with
  | prim p => rfl
  | pair a b iha ihb => simp only [Ty.openVars_pair, Ty.rename_pair, iha, ihb]
  | arrow a b iha ihb => simp only [Ty.openVars_arrow, Ty.rename_arrow, iha, ihb]
  | fvar n => rfl
  | bvar i =>
    simp only [Ty.openVars, Ty.instantiate, Ty.rename_bvar, List.getElem?_map]
    cases h : Xs[i]? with
    | none => rfl
    | some x => rfl
  | customTy nm tys ih =>
    simp only [Ty.openVars_customTy, Ty.rename_customTy, List.map_map,
               Ty.customTy.injEq, true_and]
    apply List.map_congr_left
    intro t0 ht0
    exact ih t0 ht0

/-- Swap two naturals. -/
def swapNat (a b n : Nat) : Nat := if n = a then b else if n = b then a else n

@[simp] theorem swapNat_left (a b : Nat) : swapNat a b a = b := by simp [swapNat]
theorem swapNat_right (a b : Nat) : swapNat a b b = a := by
  simp only [swapNat]; split <;> simp_all
theorem swapNat_other {a b n : Nat} (ha : n ≠ a) (hb : n ≠ b) : swapNat a b n = n := by
  simp [swapNat, ha, hb]
theorem swapNat_involutive (a b n : Nat) : swapNat a b (swapNat a b n) = n := by
  by_cases hna : n = a
  · subst hna; rw [swapNat_left, swapNat_right]
  · by_cases hnb : n = b
    · subst hnb; rw [swapNat_right, swapNat_left]
    · rw [swapNat_other hna hnb, swapNat_other hna hnb]
theorem swapNat_injective (a b : Nat) : Function.Injective (swapNat a b) :=
  Function.Involutive.injective (swapNat_involutive a b)

/-- Conjugate a substitution by a renaming: relabel both keys and values. -/
def Subst.conj (f : Nat → Nat) (S : Subst) : Subst :=
  S.map (fun p => (f p.1, Ty.rename f p.2))

/-- Conjugation preserves LC of the replacement types. -/
theorem Subst.conj_lc {f : Nat → Nat} {S : Subst} (hS : ∀ p ∈ S, p.2.IsLC) :
    ∀ p ∈ Subst.conj f S, p.2.IsLC := by
  intro p hp
  simp only [Subst.conj, List.mem_map] at hp
  obtain ⟨p0, hp0, rfl⟩ := hp
  exact Ty.rename_isLC (hS p0 hp0)

/-- The defining property of conjugation: it intertwines `onTy` with the
    renaming (for injective `f`). -/
theorem Subst.onTy_conj {f : Nat → Nat} (hf : Function.Injective f) (S : Subst) (τ : Ty) :
    (Subst.conj f S).onTy (Ty.rename f τ) = Ty.rename f (S.onTy τ) := by
  induction S generalizing τ with
  | nil => simp only [Subst.conj, List.map_nil, Subst.onTy_nil]
  | cons hd S' ih =>
    obtain ⟨z, u⟩ := hd
    show Subst.onTy (Subst.conj f S') (Ty.substFvar (f z) (Ty.rename f u) (Ty.rename f τ))
        = Ty.rename f (Subst.onTy S' (Ty.substFvar z u τ))
    rw [← Ty.rename_substFvar hf, ih]

/-- The 3-element list realising the swap `a ↔ b` (with a fresh intermediate `c`),
    usable with `TypeOfHM.onSubst`. -/
def swapSubst (a b c : Nat) : Subst := [(a, .fvar c), (b, .fvar a), (c, .fvar b)]

theorem swapSubst_lc (a b c : Nat) : ∀ p ∈ swapSubst a b c, p.2.IsLC := by
  intro p hp
  simp only [swapSubst, List.mem_cons, List.not_mem_nil, or_false] at hp
  obtain rfl | rfl | rfl := hp <;> exact ContainsBvarsUpTo.fvar

/-- The swap list acts as `rename (swapNat a b)` on types avoiding the fresh `c`. -/
theorem swapSubst_onTy {a b c : Nat} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    {τ : Ty} (hc : c ∉ τ.freeVars) :
    (swapSubst a b c).onTy τ = Ty.rename (swapNat a b) τ := by
  induction τ using Ty.rec_strong with
  | prim p => simp only [Subst.onTy_prim, Ty.rename_prim]
  | bvar i => simp only [Subst.onTy_bvar, Ty.rename_bvar]
  | pair a' b' iha ihb =>
    simp only [Ty.freeVars, List.mem_dedup, List.mem_append, not_or] at hc
    simp only [Subst.onTy_pair, Ty.rename_pair]
    exact congrArg₂ Ty.pair (iha hc.1) (ihb hc.2)
  | arrow a' b' iha ihb =>
    simp only [Ty.freeVars, List.mem_dedup, List.mem_append, not_or] at hc
    simp only [Subst.onTy_arrow, Ty.rename_arrow]
    exact congrArg₂ Ty.arrow (iha hc.1) (ihb hc.2)
  | fvar n =>
    simp only [Ty.freeVars, List.mem_singleton] at hc
    have hnc : n ≠ c := fun h => hc h.symm
    by_cases hna : n = a
    · subst hna
      simp [swapSubst, Subst.onTy, Ty.substFvars, Ty.substFvar, hbc.symm]
    · by_cases hnb : n = b
      · subst hnb
        simp [swapSubst, Subst.onTy, Ty.substFvars, Ty.substFvar, swapNat_right,
              hab.symm, hac]
      · simp [swapSubst, Subst.onTy, Ty.substFvars, Ty.substFvar,
              swapNat_other hna hnb, hna, hnb, hnc]
  | customTy nm tys ih =>
    simp only [Ty.freeVars] at hc
    simp only [Subst.onTy_customTy, Ty.rename_customTy, Ty.customTy.injEq, true_and]
    apply List.map_congr_left
    intro t ht
    exact ih t ht (fun hct => hc (TyList.mem_freeVars_of_mem ht hct))

/-- After swapping `Φ ↔ W`, the var `Φ` is absent provided `W` was absent
    (the only source of `Φ` would have been a pre-existing `W`). -/
theorem Ty.rename_swap_not_mem_left {Φ W : Nat} {Y : Ty} (h : W ∉ Y.freeVars) :
    Φ ∉ (Ty.rename (swapNat Φ W) Y).freeVars := by
  induction Y using Ty.rec_strong with
  | prim p => simp [Ty.freeVars]
  | bvar i => simp [Ty.freeVars]
  | fvar n =>
    simp only [Ty.freeVars, List.mem_singleton] at h
    simp only [Ty.rename_fvar, Ty.freeVars, List.mem_singleton, swapNat]
    split_ifs <;> omega
  | pair a b iha ihb =>
    simp only [Ty.freeVars, List.mem_dedup, List.mem_append, not_or] at h
    simp only [Ty.rename_pair, Ty.freeVars, List.mem_dedup, List.mem_append, not_or]
    exact ⟨iha h.1, ihb h.2⟩
  | arrow a b iha ihb =>
    simp only [Ty.freeVars, List.mem_dedup, List.mem_append, not_or] at h
    simp only [Ty.rename_arrow, Ty.freeVars, List.mem_dedup, List.mem_append, not_or]
    exact ⟨iha h.1, ihb h.2⟩
  | customTy nm tys ih =>
    simp only [Ty.freeVars] at h
    simp only [Ty.rename_customTy, Ty.freeVars]
    rw [TyList.not_mem_freeVars_iff]
    intro t' ht'
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp ht'
    exact ih t ht (fun hct => h (TyList.mem_freeVars_of_mem ht hct))

/-- Map-back: substituting `W ↦ Φ` undoes the swap `Φ ↔ W` on a `W`-free type. -/
theorem Ty.substFvar_rename_swap {Φ W : Nat} {X : Ty} (h : W ∉ X.freeVars) :
    Ty.substFvar W (.fvar Φ) (Ty.rename (swapNat Φ W) X) = X := by
  induction X using Ty.rec_strong with
  | prim p => rfl
  | bvar i => rfl
  | fvar n =>
    simp only [Ty.freeVars, List.mem_singleton] at h
    simp only [Ty.rename_fvar, Ty.substFvar]
    by_cases hn : n = Φ
    · subst hn; simp [swapNat]
    · rw [swapNat_other hn (fun he => h he.symm), if_neg (fun he => h he.symm)]
  | pair a b iha ihb =>
    simp only [Ty.freeVars, List.mem_dedup, List.mem_append, not_or] at h
    simp only [Ty.rename_pair, Ty.substFvar, iha h.1, ihb h.2]
  | arrow a b iha ihb =>
    simp only [Ty.freeVars, List.mem_dedup, List.mem_append, not_or] at h
    simp only [Ty.rename_arrow, Ty.substFvar, iha h.1, ihb h.2]
  | customTy nm tys ih =>
    simp only [Ty.freeVars] at h
    simp only [Ty.rename_customTy, Ty.substFvar, TyList.substFvar_eq_map, List.map_map]
    refine congrArg (Ty.customTy nm) ?_
    conv_rhs => rw [← List.map_id tys]
    apply List.map_congr_left
    intro t ht
    exact ih t ht (fun hct => h (TyList.mem_freeVars_of_mem ht hct))

/-- Two distinct fresh names, both `≥ Φ` and avoiding a given finite set. -/
theorem exists_fresh_two_ge (Φ : Nat) (avoid : List Nat) :
    ∃ W c, Φ ≤ W ∧ Φ ≤ c ∧ W ≠ c ∧ W ∉ avoid ∧ c ∉ avoid := by
  obtain ⟨Xs, hlen, hnodup, hav⟩ := exists_fresh_names (List.range Φ ++ avoid) 2
  obtain ⟨W, c, rfl⟩ : ∃ W c, Xs = [W, c] := by
    match Xs, hlen with
    | [W, c], _ => exact ⟨W, c, rfl⟩
  have hWmem : W ∈ [W, c] := by simp
  have hcmem : c ∈ [W, c] := by simp
  have hWav := hav W hWmem
  have hcav := hav c hcmem
  simp only [List.mem_append, not_or] at hWav hcav
  refine ⟨W, c, ?_, ?_, ?_, hWav.2, hcav.2⟩
  · have := hWav.1; simp only [List.mem_range, not_lt] at this; omega
  · have := hcav.1; simp only [List.mem_range, not_lt] at this; omega
  · simp only [List.nodup_cons, List.mem_singleton, List.not_mem_nil, not_false_eq_true,
      List.nodup_nil, and_true] at hnodup
    exact hnodup

/-- `substFvar` keeps `W` fresh when `W` is fresh for the input and the replacement. -/
theorem Ty.not_mem_freeVars_substFvar {Z W : Nat} {U τ : Ty}
    (hτ : W ∉ τ.freeVars) (hU : W ∉ U.freeVars) :
    W ∉ (Ty.substFvar Z U τ).freeVars := by
  induction τ using Ty.rec_strong with
  | prim p => simp [Ty.substFvar, Ty.freeVars]
  | bvar i => simp [Ty.substFvar, Ty.freeVars]
  | fvar n =>
    simp only [Ty.freeVars, List.mem_singleton] at hτ
    simp only [Ty.substFvar]
    by_cases hn : n = Z
    · simp only [if_pos hn]; exact hU
    · simp only [if_neg hn, Ty.freeVars, List.mem_singleton]; exact hτ
  | pair a b iha ihb =>
    simp only [Ty.freeVars, List.mem_dedup, List.mem_append, not_or] at hτ
    simp only [Ty.substFvar, Ty.freeVars, List.mem_dedup, List.mem_append, not_or]
    exact ⟨iha hτ.1, ihb hτ.2⟩
  | arrow a b iha ihb =>
    simp only [Ty.freeVars, List.mem_dedup, List.mem_append, not_or] at hτ
    simp only [Ty.substFvar, Ty.freeVars, List.mem_dedup, List.mem_append, not_or]
    exact ⟨iha hτ.1, ihb hτ.2⟩
  | customTy nm tys ih =>
    simp only [Ty.freeVars] at hτ
    simp only [Ty.substFvar, Ty.freeVars, TyList.substFvar_eq_map]
    rw [TyList.not_mem_freeVars_iff]
    intro t' ht'
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp ht'
    exact ih t ht (fun hct => hτ (TyList.mem_freeVars_of_mem ht hct))

/-- A whole substitution keeps `W` fresh when `W` avoids its range and the input. -/
theorem Subst.not_mem_onTy_freeVars {S : Subst} {W : Nat} {τ : Ty}
    (hS : ∀ p ∈ S, W ∉ p.2.freeVars) (hτ : W ∉ τ.freeVars) :
    W ∉ (S.onTy τ).freeVars := by
  induction S generalizing τ with
  | nil => simpa using hτ
  | cons hd S' ih =>
    obtain ⟨Z, U⟩ := hd
    rw [show ((Z, U) :: S') = [(Z, U)] ++ S' from rfl, Subst.onTy_append]
    refine ih (fun p hp => hS p (List.mem_cons_of_mem _ hp)) ?_
    exact Ty.not_mem_freeVars_substFvar hτ (hS (Z, U) List.mem_cons_self)

/-- Principality, lambda case (factored with named binders to avoid the
    inaccessible-name problem). The fresh param var `Φ` may clash with `S₀`'s
    range, so we α-rename the declarative derivation by the swap `Φ ↔ W`
    (`W` fresh), apply the IH to the body under the conjugated specialization
    `S₀ᵃ ++ [(Φ, paramTyᵃ)]` (now `Φ ∉ dom`), then map the residual back with
    `[(W, .fvar Φ)]` (the swap's involution recovers the originals). -/
theorem Infer.complete_lambda_aux {body : Expr} {Φ : Nat} {ctx : Ctx} {S₀ : Subst}
    {paramTy bodyTy : Ty}
    (ih : Infer.CompleteAt body)
    (hwf : CtxWF ctx) (hbelow : CtxBelow Φ ctx) (hS₀ : ∀ p ∈ S₀, p.2.IsLC)
    (hparamLC : paramTy.IsLC)
    (hbodyty : TypeOfHM { (S₀.onCtx ctx) with
        env := PolyTy.mkTrivial paramTy :: (S₀.onCtx ctx).env } body bodyTy) :
    ∃ Φ' S τ R,
      Infer Φ ctx (.lambda body) Φ' S τ ∧
      (∀ v, v < Φ → S₀.onTy (.fvar v) = (S ++ R).onTy (.fvar v)) ∧
      Ty.arrow paramTy bodyTy = R.onTy τ ∧
      (∀ p ∈ R, p.2.IsLC) := by
  -- STEP 0: fresh names
  obtain ⟨W, c, hΦW, hΦc, hWc, hWav, hcav⟩ := exists_fresh_two_ge Φ
    ([Φ] ++ S₀.map Prod.fst ++ S₀.flatMap (fun p => p.2.freeVars)
      ++ paramTy.freeVars ++ bodyTy.freeVars)
  simp only [List.mem_append, List.mem_singleton, List.mem_map, List.mem_flatMap] at hWav hcav
  push_neg at hWav hcav
  obtain ⟨⟨⟨⟨hWΦ, hWkey⟩, hWrange⟩, hWparam⟩, hWbody⟩ := hWav
  obtain ⟨⟨⟨⟨hcΦ, hckey⟩, hcrange⟩, hcparam⟩, hcbody⟩ := hcav
  have finj : Function.Injective (swapNat Φ W) := swapNat_injective Φ W
  have hfix : ∀ v, v < Φ → swapNat Φ W v = v := fun v hv =>
    swapNat_other (by omega) (by omega)
  have hWonTy : ∀ {τ : Ty}, W ∉ τ.freeVars → W ∉ (S₀.onTy τ).freeVars :=
    fun h => Subst.not_mem_onTy_freeVars hWrange h
  have hconΦ : ∀ p ∈ Subst.conj (swapNat Φ W) S₀, p.1 ≠ Φ := by
    intro p hp
    simp only [Subst.conj, List.mem_map] at hp
    obtain ⟨q, hq, rfl⟩ := hp
    intro hc
    apply hWkey q hq
    have hc' : swapNat Φ W q.1 = Φ := hc
    simp only [swapNat] at hc'
    split_ifs at hc' <;> omega
  have hSconjΦ : (Subst.conj (swapNat Φ W) S₀).onTy (.fvar Φ) = .fvar Φ := by
    apply Ty.substFvars_eq_self_of_no_key
    intro p hp hc
    simp only [Ty.freeVars, List.mem_singleton] at hc
    exact hconΦ p hp hc
  -- STEP 1: rename the body derivation and reinterpret its context
  have hctxeq : (swapSubst Φ W c).onCtx
        { (S₀.onCtx ctx) with env := PolyTy.mkTrivial paramTy :: (S₀.onCtx ctx).env }
      = (Subst.conj (swapNat Φ W) S₀ ++ [(Φ, Ty.rename (swapNat Φ W) paramTy)]).onCtx
        { ctx with env := PolyTy.mkTrivial (.fvar Φ) :: ctx.env } := by
    simp only [Subst.onCtx, Subst.onEnv, List.map_cons, List.map_map]
    congr 1
    congr 1
    · -- head
      simp only [Subst.onPolyTy, PolyTy.mkTrivial, PolyTy.mk.injEq, true_and]
      rw [swapSubst_onTy (Ne.symm hWΦ) (Ne.symm hcΦ) hWc hcparam,
          Subst.onTy_append (Subst.conj (swapNat Φ W) S₀)
            [(Φ, Ty.rename (swapNat Φ W) paramTy)] (.fvar Φ),
          hSconjΦ]
      simp only [Subst.onTy, Ty.substFvars, Ty.substFvar, if_pos]
    · -- tail
      apply List.map_congr_left
      intro M hM
      have hMbelow : ∀ v ∈ M.body.freeVars, v < Φ := (hbelow M hM).mem_lt
      have hrenM : Ty.rename (swapNat Φ W) M.body = M.body :=
        Ty.rename_eq_self (fun v hv => hfix v (hMbelow v hv))
      have hΦnotin : Φ ∉ (Ty.rename (swapNat Φ W) (S₀.onTy M.body)).freeVars :=
        Ty.rename_swap_not_mem_left (hWonTy (τ := M.body) (fun hv => by have := hMbelow _ hv; omega))
      simp only [Function.comp, Subst.onPolyTy, PolyTy.mk.injEq, true_and]
      rw [swapSubst_onTy (Ne.symm hWΦ) (Ne.symm hcΦ) hWc
            (Subst.not_mem_onTy_freeVars hcrange (fun hv => by have := hMbelow _ hv; omega)),
          Subst.onTy_append (Subst.conj (swapNat Φ W) S₀)
            [(Φ, Ty.rename (swapNat Φ W) paramTy)] M.body]
      conv_rhs => rw [← hrenM, Subst.onTy_conj finj]
      exact (Ty.substFvar_fresh hΦnotin).symm
  have hbodyTyeq : (swapSubst Φ W c).onTy bodyTy = Ty.rename (swapNat Φ W) bodyTy :=
    swapSubst_onTy (Ne.symm hWΦ) (Ne.symm hcΦ) hWc hcbody
  have hren := TypeOfHM.onSubst (swapSubst Φ W c) (swapSubst_lc Φ W c) hbodyty
  rw [hctxeq, hbodyTyeq] at hren
  -- STEP 2: apply the IH to the body under the conjugated specialization
  have hwf_b : CtxWF { ctx with env := PolyTy.mkTrivial (.fvar Φ) :: ctx.env } := by
    intro M hM
    rcases List.mem_cons.mp hM with rfl | hM
    · exact ContainsBvarsUpTo.fvar
    · exact hwf M hM
  have hbelow_b : CtxBelow (Φ + 1) { ctx with env := PolyTy.mkTrivial (.fvar Φ) :: ctx.env } := by
    intro M hM
    rcases List.mem_cons.mp hM with rfl | hM
    · exact .fvar (by omega)
    · exact (hbelow M hM).mono (by omega)
  have hT_lc : ∀ p ∈ Subst.conj (swapNat Φ W) S₀ ++ [(Φ, Ty.rename (swapNat Φ W) paramTy)],
      p.2.IsLC := by
    intro p hp
    rw [List.mem_append] at hp
    rcases hp with hp | hp
    · exact Subst.conj_lc hS₀ p hp
    · rw [List.mem_singleton] at hp
      subst hp
      exact Ty.rename_isLC hparamLC
  obtain ⟨Φ', S, τb, R_b, hinfb, hagb, htyb, hR_b⟩ := ih hwf_b hbelow_b hT_lc hren
  -- STEP 3: assemble the conclusion
  refine ⟨Φ', S, .arrow (S.onTy (.fvar Φ)) τb, R_b ++ [(W, .fvar Φ)], ?_, ?_, ?_, ?_⟩
  · exact Infer.lambda hinfb
  · -- agreement below Φ
    intro v hv
    have hWv : W ∉ (Ty.fvar v).freeVars := by
      simp only [Ty.freeVars, List.mem_singleton]; omega
    have hconjv : (Subst.conj (swapNat Φ W) S₀).onTy (.fvar v)
        = Ty.rename (swapNat Φ W) (S₀.onTy (.fvar v)) := by
      have h := Subst.onTy_conj finj S₀ (.fvar v)
      rw [Ty.rename_fvar, hfix v hv] at h
      exact h
    have hTv : (Subst.conj (swapNat Φ W) S₀ ++ [(Φ, Ty.rename (swapNat Φ W) paramTy)]).onTy (.fvar v)
        = Ty.rename (swapNat Φ W) (S₀.onTy (.fvar v)) := by
      rw [Subst.onTy_append (Subst.conj (swapNat Φ W) S₀)
            [(Φ, Ty.rename (swapNat Φ W) paramTy)] (.fvar v), hconjv]
      exact Ty.substFvar_fresh (Ty.rename_swap_not_mem_left (hWonTy (τ := .fvar v) hWv))
    rw [← List.append_assoc, Subst.onTy_append (S ++ R_b) [(W, .fvar Φ)] (.fvar v),
        ← hagb v (by omega), hTv]
    exact (Ty.substFvar_rename_swap (hWonTy (τ := .fvar v) hWv)).symm
  · -- the arrow type is recovered
    have hTΦ : (Subst.conj (swapNat Φ W) S₀ ++ [(Φ, Ty.rename (swapNat Φ W) paramTy)]).onTy (.fvar Φ)
        = Ty.rename (swapNat Φ W) paramTy := by
      rw [Subst.onTy_append (Subst.conj (swapNat Φ W) S₀)
            [(Φ, Ty.rename (swapNat Φ W) paramTy)] (.fvar Φ), hSconjΦ]
      simp only [Subst.onTy, Ty.substFvars, Ty.substFvar, if_pos]
    rw [Subst.onTy_arrow]
    refine congrArg₂ Ty.arrow ?_ ?_
    · rw [Subst.onTy_append R_b [(W, .fvar Φ)] (S.onTy (.fvar Φ)),
          ← Subst.onTy_append S R_b (.fvar Φ),
          ← hagb Φ (by omega), hTΦ]
      exact (Ty.substFvar_rename_swap hWparam).symm
    · rw [Subst.onTy_append R_b [(W, .fvar Φ)] τb, ← htyb]
      exact (Ty.substFvar_rename_swap hWbody).symm
  · -- residual is LC
    intro p hp
    rw [List.mem_append] at hp
    rcases hp with hp | hp
    · exact hR_b p hp
    · rw [List.mem_singleton] at hp
      subst hp
      exact ContainsBvarsUpTo.fvar

/-- Principality, lambda case. -/
theorem Infer.complete_lambda {body : Expr}
    (ih : Infer.CompleteAt body) : Infer.CompleteAt (.lambda body) := by
  intro Φ ctx S₀ τ₀ hwf hbelow hS₀ hty
  cases hty with
  | lambda hparamLC heq hbodyty =>
    subst heq
    exact Infer.complete_lambda_aux ih hwf hbelow hS₀ hparamLC hbodyty


/-! ### Block renaming (for the `var`/`letIn` cases, which allocate a block of
    fresh vars at once). Generalises the single-var swap: `blockSwap Φ W k`
    transposes `[Φ,Φ+k)` with `[W,W+k)` (disjoint when `Φ+k ≤ W`). On types that
    avoid the `W`-block, the forward list `blockList` realises it, and the
    backward list `blockListBack` is the map-back. -/

/-- Transpose the blocks `[Φ,Φ+k)` and `[W,W+k)` (disjoint when `Φ+k ≤ W`). -/
def blockSwap (Φ W k n : Nat) : Nat :=
  if Φ ≤ n ∧ n < Φ + k then n + (W - Φ)
  else if W ≤ n ∧ n < W + k then n - (W - Φ)
  else n

/-- Forward renaming list: `Φ+i ↦ .fvar (W+i)`. -/
def blockList (Φ W k : Nat) : Subst := (List.range k).map (fun i => (Φ + i, Ty.fvar (W + i)))

/-- Backward renaming list: `W+i ↦ .fvar (Φ+i)`. -/
def blockListBack (Φ W k : Nat) : Subst := (List.range k).map (fun i => (W + i, Ty.fvar (Φ + i)))

theorem blockSwap_lt {Φ W k n : Nat} (hle : Φ ≤ W) (h : n < Φ) :
    blockSwap Φ W k n = n := by
  simp only [blockSwap]; split_ifs <;> omega

theorem blockSwap_block {Φ W k i : Nat} (hle : Φ ≤ W) (hi : i < k) :
    blockSwap Φ W k (Φ + i) = W + i := by
  simp only [blockSwap]; split_ifs <;> omega

theorem blockSwap_involutive {Φ W k : Nat} (hd : Φ + k ≤ W) (n : Nat) :
    blockSwap Φ W k (blockSwap Φ W k n) = n := by
  simp only [blockSwap]; split_ifs <;> omega

theorem blockSwap_injective {Φ W k : Nat} (hd : Φ + k ≤ W) :
    Function.Injective (blockSwap Φ W k) :=
  Function.Involutive.injective (blockSwap_involutive hd)

theorem blockList_lc (Φ W k : Nat) : ∀ p ∈ blockList Φ W k, p.2.IsLC := by
  intro p hp
  simp only [blockList, List.mem_map] at hp
  obtain ⟨i, _, rfl⟩ := hp
  exact ContainsBvarsUpTo.fvar

theorem blockListBack_lc (Φ W k : Nat) : ∀ p ∈ blockListBack Φ W k, p.2.IsLC := by
  intro p hp
  simp only [blockListBack, List.mem_map] at hp
  obtain ⟨i, _, rfl⟩ := hp
  exact ContainsBvarsUpTo.fvar

/-- A `range`-indexed list of single-var substitutions `a+i ↦ .fvar (b+i)`
    acts on a free variable `n` exactly like the block transposition: if `n`
    is in `[a, a+k)` it becomes `n - a + b`, otherwise it is unchanged. The
    disjointness premise prevents a relabelled var from being touched again. -/
private theorem rangeMapList_onTy_fvar (a b : Nat) (k : Nat)
    (hdisj : a + k ≤ b ∨ b + k ≤ a) (n : Nat) :
    Subst.onTy ((List.range k).map (fun i => (a + i, Ty.fvar (b + i)))) (Ty.fvar n)
      = Ty.fvar (if a ≤ n ∧ n < a + k then n - a + b else n) := by
  induction k with
  | zero =>
    simp only [List.range_zero, List.map_nil, Subst.onTy_nil, Nat.add_zero]
    split_ifs <;> first | rfl | omega
  | succ k ih =>
    have hdisj' : a + k ≤ b ∨ b + k ≤ a := by omega
    simp only [List.range_succ, List.map_append, List.map_cons, List.map_nil,
               Subst.onTy_append]
    rw [ih hdisj']
    simp only [Subst.onTy, Ty.substFvars, Ty.substFvar]
    split_ifs <;> first | rfl | omega | (rw [Ty.fvar.injEq]; omega)

/-- The forward list realises `blockSwap` on `W`-block-avoiding types. -/
theorem blockList_onTy {Φ W k : Nat} (hd : Φ + k ≤ W) {τ : Ty}
    (hτ : ∀ v ∈ τ.freeVars, ¬ (W ≤ v ∧ v < W + k)) :
    (blockList Φ W k).onTy τ = Ty.rename (blockSwap Φ W k) τ := by
  induction τ using Ty.rec_strong with
  | prim p => simp only [Subst.onTy_prim, Ty.rename_prim]
  | bvar i => simp only [Subst.onTy_bvar, Ty.rename_bvar]
  | pair a b iha ihb =>
    simp only [Subst.onTy_pair, Ty.rename_pair]
    refine congrArg₂ Ty.pair (iha (fun v hv => hτ v ?_)) (ihb (fun v hv => hτ v ?_))
    · simp only [Ty.freeVars, List.mem_dedup, List.mem_append]; exact Or.inl hv
    · simp only [Ty.freeVars, List.mem_dedup, List.mem_append]; exact Or.inr hv
  | arrow a b iha ihb =>
    simp only [Subst.onTy_arrow, Ty.rename_arrow]
    refine congrArg₂ Ty.arrow (iha (fun v hv => hτ v ?_)) (ihb (fun v hv => hτ v ?_))
    · simp only [Ty.freeVars, List.mem_dedup, List.mem_append]; exact Or.inl hv
    · simp only [Ty.freeVars, List.mem_dedup, List.mem_append]; exact Or.inr hv
  | fvar n =>
    have hWn : ¬ (W ≤ n ∧ n < W + k) :=
      hτ n (by simp only [Ty.freeVars, List.mem_singleton])
    simp only [blockList]
    rw [rangeMapList_onTy_fvar Φ W k (Or.inl hd) n, Ty.rename_fvar]
    simp only [blockSwap]
    split_ifs <;> first | rfl | omega | (rw [Ty.fvar.injEq]; omega)
  | customTy nm tys ih =>
    simp only [Subst.onTy_customTy, Ty.rename_customTy, Ty.customTy.injEq, true_and]
    apply List.map_congr_left
    intro t ht
    exact ih t ht (fun v hv => hτ v (TyList.mem_freeVars_of_mem ht hv))

/-- Map-back: the backward list undoes `blockSwap` on `W`-block-avoiding types. -/
theorem blockListBack_onTy_rename {Φ W k : Nat} (hd : Φ + k ≤ W) {X : Ty}
    (hX : ∀ v ∈ X.freeVars, ¬ (W ≤ v ∧ v < W + k)) :
    (blockListBack Φ W k).onTy (Ty.rename (blockSwap Φ W k) X) = X := by
  induction X using Ty.rec_strong with
  | prim p => simp only [Ty.rename_prim, Subst.onTy_prim]
  | bvar i => simp only [Ty.rename_bvar, Subst.onTy_bvar]
  | pair a b iha ihb =>
    simp only [Ty.rename_pair, Subst.onTy_pair]
    refine congrArg₂ Ty.pair (iha (fun v hv => hX v ?_)) (ihb (fun v hv => hX v ?_))
    · simp only [Ty.freeVars, List.mem_dedup, List.mem_append]; exact Or.inl hv
    · simp only [Ty.freeVars, List.mem_dedup, List.mem_append]; exact Or.inr hv
  | arrow a b iha ihb =>
    simp only [Ty.rename_arrow, Subst.onTy_arrow]
    refine congrArg₂ Ty.arrow (iha (fun v hv => hX v ?_)) (ihb (fun v hv => hX v ?_))
    · simp only [Ty.freeVars, List.mem_dedup, List.mem_append]; exact Or.inl hv
    · simp only [Ty.freeVars, List.mem_dedup, List.mem_append]; exact Or.inr hv
  | fvar n =>
    have hWn : ¬ (W ≤ n ∧ n < W + k) :=
      hX n (by simp only [Ty.freeVars, List.mem_singleton])
    simp only [Ty.rename_fvar, blockListBack]
    rw [rangeMapList_onTy_fvar W Φ k (Or.inr hd) (blockSwap Φ W k n)]
    simp only [blockSwap]
    split_ifs <;> first | rfl | omega | (rw [Ty.fvar.injEq]; omega)
  | customTy nm tys ih =>
    simp only [Ty.rename_customTy, Subst.onTy_customTy, List.map_map, Ty.customTy.injEq,
               true_and]
    conv_rhs => rw [← List.map_id tys]
    apply List.map_congr_left
    intro t ht
    exact ih t ht (fun v hv => hX v (TyList.mem_freeVars_of_mem ht hv))

/-- The `Φ`-block is absent after renaming a `W`-block-avoiding type. -/
theorem blockSwap_rename_not_mem {Φ W k : Nat} (hd : Φ + k ≤ W) {Y : Ty}
    (hY : ∀ v ∈ Y.freeVars, ¬ (W ≤ v ∧ v < W + k)) :
    ∀ v, Φ ≤ v → v < Φ + k → v ∉ (Ty.rename (blockSwap Φ W k) Y).freeVars := by
  induction Y using Ty.rec_strong with
  | prim p => simp [Ty.freeVars]
  | bvar i => simp [Ty.freeVars]
  | fvar n =>
    intro v hv1 hv2
    have hWn : ¬ (W ≤ n ∧ n < W + k) :=
      hY n (by simp only [Ty.freeVars, List.mem_singleton])
    simp only [Ty.rename_fvar, Ty.freeVars, List.mem_singleton, blockSwap]
    split_ifs <;> omega
  | pair a b iha ihb =>
    intro v hv1 hv2
    simp only [Ty.rename_pair, Ty.freeVars, List.mem_dedup, List.mem_append, not_or]
    refine ⟨iha (fun w hw => hY w ?_) v hv1 hv2, ihb (fun w hw => hY w ?_) v hv1 hv2⟩
    · simp only [Ty.freeVars, List.mem_dedup, List.mem_append]; exact Or.inl hw
    · simp only [Ty.freeVars, List.mem_dedup, List.mem_append]; exact Or.inr hw
  | arrow a b iha ihb =>
    intro v hv1 hv2
    simp only [Ty.rename_arrow, Ty.freeVars, List.mem_dedup, List.mem_append, not_or]
    refine ⟨iha (fun w hw => hY w ?_) v hv1 hv2, ihb (fun w hw => hY w ?_) v hv1 hv2⟩
    · simp only [Ty.freeVars, List.mem_dedup, List.mem_append]; exact Or.inl hw
    · simp only [Ty.freeVars, List.mem_dedup, List.mem_append]; exact Or.inr hw
  | customTy nm tys ih =>
    intro v hv1 hv2
    simp only [Ty.rename_customTy, Ty.freeVars]
    rw [TyList.not_mem_freeVars_iff]
    intro t' ht'
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp ht'
    exact ih t ht (fun w hw => hY w (TyList.mem_freeVars_of_mem ht hw)) v hv1 hv2

/-- Refinement of `Ty.substFvars_zip_fvar_eq` needing freshness only of the
    *selected* value `v` (not all of `Vs`), and no length condition. Substituting
    along `Xs.zip Vs` sends `.fvar Xs[i]` to `Vs[i]`. -/
theorem Ty.substFvars_zip_fvar_eq' {Xs : List Nat} {Vs : List Ty} {i : Nat} {x : Nat} {v : Ty}
    (h_nodup : Xs.Nodup) (hx : Xs[i]? = some x) (hv : Vs[i]? = some v)
    (h_fresh : ∀ X ∈ Xs, X ∉ v.freeVars) :
    Ty.substFvars (Xs.zip Vs) (.fvar x) = v := by
  induction Xs generalizing Vs i x v with
  | nil => simp at hx
  | cons X0 Xs' ih =>
    cases Vs with
    | nil => simp at hv
    | cons V0 Vs' =>
      cases i with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hx hv
        simp only [List.zip_cons_cons, Ty.substFvars]
        rw [← hx, show Ty.substFvar X0 V0 (.fvar X0) = V0 by simp [Ty.substFvar], ← hv]
        apply Ty.substFvars_eq_self_of_no_key
        intro p hp hcontra
        have hp1 : p.1 ∈ Xs' := (List.of_mem_zip hp).1
        exact h_fresh p.1 (List.mem_cons_of_mem _ hp1) (hv ▸ hcontra)
      | succ k =>
        simp only [List.getElem?_cons_succ] at hx hv
        have h_X0_notin : X0 ∉ Xs' := (List.nodup_cons.mp h_nodup).1
        have h_ne : x ≠ X0 := fun h => h_X0_notin (h ▸ List.mem_of_getElem? hx)
        simp only [List.zip_cons_cons, Ty.substFvars]
        rw [show Ty.substFvar X0 V0 (.fvar x) = .fvar x by simp [Ty.substFvar, h_ne]]
        exact ih (List.nodup_cons.mp h_nodup).2 hx hv
          (fun X hX => h_fresh X (List.mem_cons_of_mem _ hX))

/-- Bridge for the `var` completeness case: if `ty` instantiates to `τ` under
    `tyArgs`, then opening `ty` with fresh names `Xs` (nodup, fresh for `τ`) and
    substituting `Xs ↦ tyArgs` recovers `τ`. Only the result `τ`'s freshness is
    needed (used `tyArgs` are subterms of `τ`); unused `tyArgs` never matter, as
    the induction only visits `ty`'s actual bound vars. -/
theorem InstantiatesBy.onTy_openVars_zip {Xs : List Nat} {ty τ : Ty} {tyArgs : List Ty}
    (hinst : InstantiatesBy tyArgs ty τ)
    (hbv : ContainsBvarsUpTo Xs.length ty)
    (hnodup : Xs.Nodup)
    (hXfresh : ∀ x ∈ Xs, x ∉ τ.freeVars) :
    Subst.onTy (Xs.zip tyArgs) (Ty.openVars Xs ty) = τ := by
  induction ty using Ty.rec_strong generalizing τ with
  | prim p => cases hinst; simp only [Ty.openVars_prim, Subst.onTy_prim]
  | fvar n =>
    cases hinst
    simp only [Ty.openVars, Ty.instantiate]
    apply Ty.substFvars_eq_self_of_no_key
    intro p hp hc
    simp only [Ty.freeVars, List.mem_singleton] at hc
    subst hc
    exact hXfresh p.1 (List.of_mem_zip hp).1 (by simp [Ty.freeVars])
  | bvar i =>
    cases hinst with
    | bvar hsome =>
      cases hbv with
      | bvar hlt =>
        have hxi : Xs[i]? = some Xs[i] := List.getElem?_eq_getElem hlt
        simp only [Ty.openVars, Ty.instantiate, hxi, Option.elim_some]
        exact Ty.substFvars_zip_fvar_eq' hnodup hxi hsome hXfresh
  | pair a b iha ihb =>
    cases hinst with
    | pair ha hb =>
      cases hbv with
      | pair hba hbb =>
        simp only [Ty.openVars_pair, Subst.onTy_pair]
        refine congrArg₂ Ty.pair (iha ha hba ?_) (ihb hb hbb ?_)
        · intro x hx hc; exact hXfresh x hx (by
            simp only [Ty.freeVars, List.mem_dedup, List.mem_append]; exact .inl hc)
        · intro x hx hc; exact hXfresh x hx (by
            simp only [Ty.freeVars, List.mem_dedup, List.mem_append]; exact .inr hc)
  | arrow a b iha ihb =>
    cases hinst with
    | arrow ha hb =>
      cases hbv with
      | arrow hba hbb =>
        simp only [Ty.openVars_arrow, Subst.onTy_arrow]
        refine congrArg₂ Ty.arrow (iha ha hba ?_) (ihb hb hbb ?_)
        · intro x hx hc; exact hXfresh x hx (by
            simp only [Ty.freeVars, List.mem_dedup, List.mem_append]; exact .inl hc)
        · intro x hx hc; exact hXfresh x hx (by
            simp only [Ty.freeVars, List.mem_dedup, List.mem_append]; exact .inr hc)
  | customTy nm tys ih =>
    cases hinst with
    | customTy hforall =>
      cases hbv with
      | customTy hball =>
        simp only [Ty.openVars_customTy, Subst.onTy_customTy]
        refine congrArg (Ty.customTy nm) ?_
        induction hforall with
        | nil => rfl
        | cons hhd htl ihtl =>
          rename_i a instA tys' instTys'
          simp only [List.map_cons, List.cons.injEq]
          refine ⟨ih a List.mem_cons_self hhd (hball a List.mem_cons_self) ?_, ?_⟩
          · intro x hx hc
            apply hXfresh x hx
            simp only [Ty.freeVars, TyList.freeVars, List.mem_dedup, List.mem_append]
            exact Or.inl hc
          · refine ihtl (fun t ht => ih t (List.mem_cons_of_mem _ ht)) ?_
              (fun t ht => hball t (List.mem_cons_of_mem _ ht))
            intro x hx hc
            apply hXfresh x hx
            simp only [Ty.freeVars, TyList.freeVars, List.mem_dedup, List.mem_append] at hc ⊢
            exact Or.inr hc

/-- Converse of `Ty.BelowFvars.mem_lt`: all free vars `< Φ` gives `BelowFvars Φ`. -/
theorem Ty.BelowFvars.of_freeVars_lt {Φ : Nat} {τ : Ty}
    (h : ∀ v ∈ τ.freeVars, v < Φ) : Ty.BelowFvars Φ τ := by
  induction τ using Ty.rec_strong with
  | prim p => exact .prim
  | bvar i => exact .bvar
  | fvar n => exact .fvar (h n (by simp [Ty.freeVars]))
  | pair a b iha ihb =>
    refine .pair (iha fun v hv => h v ?_) (ihb fun v hv => h v ?_)
    · simp only [Ty.freeVars, List.mem_dedup, List.mem_append]; exact .inl hv
    · simp only [Ty.freeVars, List.mem_dedup, List.mem_append]; exact .inr hv
  | arrow a b iha ihb =>
    refine .arrow (iha fun v hv => h v ?_) (ihb fun v hv => h v ?_)
    · simp only [Ty.freeVars, List.mem_dedup, List.mem_append]; exact .inl hv
    · simp only [Ty.freeVars, List.mem_dedup, List.mem_append]; exact .inr hv
  | customTy nm tys ih =>
    refine .customTy fun t ht => ih t ht (fun v hv => h v ?_)
    simp only [Ty.freeVars]
    exact TyList.mem_freeVars_of_mem ht hv

theorem freshVars_nodup {Φ k : Nat} : (freshVars Φ k).Nodup :=
  (List.nodup_range).map (fun _ _ h => by omega)

theorem freshVars_ge {Φ k : Nat} : ∀ x ∈ freshVars Φ k, Φ ≤ x := by
  intro x hx
  simp only [freshVars, List.mem_map, List.mem_range] at hx
  obtain ⟨i, _, rfl⟩ := hx
  omega

/-- A single fresh name `W` starting a block `[W,W+k)` disjoint from `[Φ,Φ+k)`
    and above a finite `avoid` set. -/
theorem exists_fresh_block (avoid : List Nat) (Φ k : Nat) :
    ∃ W, Φ + k ≤ W ∧ ∀ v ∈ avoid, v < W := by
  refine ⟨avoid.foldr max 0 + Φ + k + 1, by omega, ?_⟩
  intro v hv
  have := List.le_foldr_max hv
  omega

/-- Principality, variable case. The algorithm opens the looked-up scheme with a
    fresh block `[Φ,Φ+pc)`; these may clash with `S₀`'s range or the declarative
    instantiation `tyArgs`, so we α-rename the derivation by the block-swap
    `[Φ,Φ+pc) ↔ [W,W+pc)` (`W` fresh), read off the residual from the clean
    (block-avoiding) renamed instantiation via `InstantiatesBy.onTy_openVars_zip`,
    then map back with `blockListBack`. -/
theorem Infer.complete_var {i : Nat} : Infer.CompleteAt (.var i) := by
  intro Φ ctx S₀ τ₀ hwf hbelow hS₀ hty
  -- STEP 0: looked-up scheme from `ctx`, without consuming `hty`.
  obtain ⟨polyTy, hlook_orig⟩ : ∃ pt, ctx.env[i]? = some pt := by
    cases hty with
    | var hlook _ _ =>
      have hmap : (S₀.onCtx ctx).env[i]? = (ctx.env[i]?).map S₀.onPolyTy := by
        show (ctx.env.map S₀.onPolyTy)[i]? = _
        rw [List.getElem?_map]
      rw [hmap] at hlook
      obtain ⟨pt, h, _⟩ := Option.map_eq_some_iff.mp hlook
      exact ⟨pt, h⟩
  have hmem : polyTy ∈ ctx.env := List.mem_of_getElem? hlook_orig
  set pc := polyTy.paramCount with hpc
  have hwfpoly : ContainsBvarsUpTo pc polyTy.body := hwf polyTy hmem
  -- STEP 1: fresh block start `W`.
  obtain ⟨W, hd, hWfresh⟩ := exists_fresh_block
    (S₀.map Prod.fst ++ S₀.flatMap (fun p => p.2.freeVars) ++ τ₀.freeVars) Φ pc
  have hτ₀W : ∀ v ∈ τ₀.freeVars, ¬ (W ≤ v ∧ v < W + pc) := by
    intro v hv hc
    have := hWfresh v (List.mem_append_right _ hv)
    omega
  have hSrange_lt : ∀ p ∈ S₀, ∀ v ∈ p.2.freeVars, v < W := by
    intro p hp v hv
    exact hWfresh v (List.mem_append_left _
      (List.mem_append_right _ (List.mem_flatMap.mpr ⟨p, hp, hv⟩)))
  have hSkey_lt : ∀ p ∈ S₀, p.1 < W := by
    intro p hp
    exact hWfresh p.1 (List.mem_append_left _
      (List.mem_append_left _ (List.mem_map.mpr ⟨p, hp, rfl⟩)))
  have hS₀belowW : ∀ p ∈ S₀, Ty.BelowFvars W p.2 :=
    fun p hp => Ty.BelowFvars.of_freeVars_lt (fun v hv => hSrange_lt p hp v hv)
  have hWblock_of_belowW : ∀ {t : Ty}, Ty.BelowFvars W t →
      ∀ v ∈ t.freeVars, ¬ (W ≤ v ∧ v < W + pc) :=
    fun {t} ht v hv => by have := ht.mem_lt v hv; omega
  have finj : Function.Injective (blockSwap Φ W pc) := blockSwap_injective hd
  have hffix : ∀ v, v < Φ → blockSwap Φ W pc v = v := fun v hv => blockSwap_lt (by omega) hv
  -- STEP 2: rename `hty` by the block-swap, reinterpret as a `conj`.
  have hren := TypeOfHM.onSubst (blockList Φ W pc) (blockList_lc Φ W pc) hty
  have hctxeq : (blockList Φ W pc).onCtx (S₀.onCtx ctx)
      = (Subst.conj (blockSwap Φ W pc) S₀).onCtx ctx := by
    simp only [Subst.onCtx, Subst.onEnv, List.map_map]
    congr 1
    apply List.map_congr_left
    intro M hM
    simp only [Function.comp_apply, Subst.onPolyTy]
    congr 1
    rw [blockList_onTy hd
        (hWblock_of_belowW (Subst.onTy_belowFvars hS₀belowW ((hbelow M hM).mono (by omega))))]
    conv_rhs => rw [← Ty.rename_eq_self (f := blockSwap Φ W pc) (τ := M.body)
      (fun v hv => hffix v ((hbelow M hM).mem_lt v hv))]
    rw [Subst.onTy_conj finj]
  have htyeq : (blockList Φ W pc).onTy τ₀ = Ty.rename (blockSwap Φ W pc) τ₀ :=
    blockList_onTy hd hτ₀W
  have hren2 : TypeOfHM ((Subst.conj (blockSwap Φ W pc) S₀).onCtx ctx) (.var i)
      (Ty.rename (blockSwap Φ W pc) τ₀) := by
    rw [hctxeq, htyeq] at hren
    exact hren
  -- STEP 3: invert renamed derivation.
  cases hren2 with
  | var hlook2 htyargs2 hinst2 =>
    rename_i polyTy2 tyArgs2
    have hlook2' : ((Subst.conj (blockSwap Φ W pc) S₀).onCtx ctx).env[i]?
        = some ((Subst.conj (blockSwap Φ W pc) S₀).onPolyTy polyTy) := by
      show (ctx.env.map (Subst.conj (blockSwap Φ W pc) S₀).onPolyTy)[i]? = _
      simp only [List.getElem?_map, hlook_orig, Option.map_some]
    have hpolyTy2 : polyTy2 = (Subst.conj (blockSwap Φ W pc) S₀).onPolyTy polyTy :=
      Option.some.inj (hlook2.symm.trans hlook2')
    subst hpolyTy2
    simp only [Subst.onPolyTy] at hinst2
    -- STEP 4: assemble.
    have hdomfresh : ∀ p ∈ Subst.conj (blockSwap Φ W pc) S₀, p.1 ∉ freshVars Φ pc := by
      intro p hp hmemf
      simp only [Subst.conj, List.mem_map] at hp
      obtain ⟨q, hq, rfl⟩ := hp
      have hq1 : q.1 < W := hSkey_lt q hq
      have hge := freshVars_ge _ hmemf
      have hlt := freshVars_lt _ hmemf
      simp only [blockSwap] at hge hlt
      split_ifs at hge hlt <;> omega
    have hbv2 : ContainsBvarsUpTo (freshVars Φ pc).length
        ((Subst.conj (blockSwap Φ W pc) S₀).onTy polyTy.body) := by
      rw [freshVars_length]
      exact Subst.onTy_containsBvars (Subst.conj_lc hS₀) hwfpoly
    have hXfresh2 : ∀ x ∈ freshVars Φ pc, x ∉ (Ty.rename (blockSwap Φ W pc) τ₀).freeVars :=
      fun x hx => blockSwap_rename_not_mem hd hτ₀W x (freshVars_ge x hx) (freshVars_lt x hx)
    have hR'eq : Subst.onTy (Subst.conj (blockSwap Φ W pc) S₀ ++ (freshVars Φ pc).zip tyArgs2)
        (polyTy.openVars (freshVars Φ pc)) = Ty.rename (blockSwap Φ W pc) τ₀ := by
      rw [Subst.onTy_append]
      simp only [PolyTy.openVars]
      rw [Subst.onTy_openVars (Subst.conj_lc hS₀) hdomfresh]
      exact InstantiatesBy.onTy_openVars_zip hinst2 hbv2 freshVars_nodup hXfresh2
    refine ⟨Φ + pc, [], polyTy.openVars (freshVars Φ pc),
      (Subst.conj (blockSwap Φ W pc) S₀ ++ (freshVars Φ pc).zip tyArgs2) ++ blockListBack Φ W pc,
      Infer.var hlook_orig, ?_, ?_, ?_⟩
    · -- agreement below the frontier
      intro v hv
      have hbelowfv : Ty.BelowFvars W (S₀.onTy (.fvar v)) :=
        Subst.onTy_belowFvars hS₀belowW (Ty.BelowFvars.fvar (show v < W by omega))
      have hconjv : Subst.onTy (Subst.conj (blockSwap Φ W pc) S₀) (.fvar v)
          = Ty.rename (blockSwap Φ W pc) (S₀.onTy (.fvar v)) := by
        conv_lhs => rw [show (Ty.fvar v) = Ty.rename (blockSwap Φ W pc) (Ty.fvar v) by
          rw [Ty.rename_fvar, hffix v hv]]
        rw [Subst.onTy_conj finj]
      have hzipnoop : Subst.onTy ((freshVars Φ pc).zip tyArgs2)
          (Ty.rename (blockSwap Φ W pc) (S₀.onTy (.fvar v)))
          = Ty.rename (blockSwap Φ W pc) (S₀.onTy (.fvar v)) :=
        Ty.substFvars_eq_self_of_no_key (fun p hp =>
          blockSwap_rename_not_mem hd (hWblock_of_belowW hbelowfv) p.1
            (freshVars_ge p.1 (List.of_mem_zip hp).1) (freshVars_lt p.1 (List.of_mem_zip hp).1))
      have hback : Subst.onTy (blockListBack Φ W pc)
          (Ty.rename (blockSwap Φ W pc) (S₀.onTy (.fvar v))) = S₀.onTy (.fvar v) :=
        blockListBack_onTy_rename hd (hWblock_of_belowW hbelowfv)
      rw [List.nil_append, Subst.onTy_append, Subst.onTy_append, hconjv, hzipnoop, hback]
    · -- declarative type factors through the residual
      rw [Subst.onTy_append, hR'eq, blockListBack_onTy_rename hd hτ₀W]
    · -- residual is locally closed
      intro p hp
      rw [List.mem_append] at hp
      rcases hp with hp | hp
      · rw [List.mem_append] at hp
        rcases hp with hp | hp
        · exact Subst.conj_lc hS₀ p hp
        · exact htyargs2 p.2 (List.of_mem_zip hp).2
      · exact blockListBack_lc Φ W pc p hp


/-! ### Unification: MGU residual is LC, and unification completeness

For the `app` completeness case we need: (1) the residual `R` factoring a unifier
`S'` through the MGU `S` is locally-closed when `S'` is (so it can serve as the
next `S₀`); (2) unifiability implies a `UnifyRel` derivation exists. -/

mutual
/-- Like `UnifyRel.greatest`, but the residual `R` is also LC when `S'` is. -/
theorem UnifyRel.greatest_lc : {τ₁ τ₂ : Ty} → {S : Subst} → UnifyRel τ₁ τ₂ S →
    ∀ S' : Subst, (∀ p ∈ S', p.2.IsLC) → Unifies S' τ₁ τ₂ →
    ∃ R : Subst, (∀ τ, S'.onTy τ = R.onTy (S.onTy τ)) ∧ (∀ p ∈ R, p.2.IsLC)
  | _, _, _, .prim, S', hlc, _ => ⟨S', fun τ => by simp only [Subst.onTy_nil], hlc⟩
  | _, _, _, .fvarRefl, S', hlc, _ => ⟨S', fun τ => by simp only [Subst.onTy_nil], hlc⟩
  | _, _, _, .fvarL _ _, S', hlc, hS' => ⟨S', fun τ => (Subst.onTy_substFvar hS' τ).symm, hlc⟩
  | _, _, _, .fvarR _ _, S', hlc, hS' => ⟨S', fun τ => (Subst.onTy_substFvar (Eq.symm hS') τ).symm, hlc⟩
  | _, _, _, @UnifyRel.arrow a b c d S₁ S₂ h₁ h₂, S', hlc, hS' => by
    simp only [Unifies, Subst.onTy_arrow, Ty.arrow.injEq] at hS'
    obtain ⟨hac, hbd⟩ := hS'
    obtain ⟨R₁, hR₁, hR₁lc⟩ := UnifyRel.greatest_lc h₁ S' hlc hac
    have hR₁bd : Unifies R₁ (S₁.onTy b) (S₁.onTy d) := by
      show R₁.onTy (S₁.onTy b) = R₁.onTy (S₁.onTy d)
      rw [← hR₁ b, ← hR₁ d]; exact hbd
    obtain ⟨R₂, hR₂, hR₂lc⟩ := UnifyRel.greatest_lc h₂ R₁ hR₁lc hR₁bd
    exact ⟨R₂, fun τ => by rw [Subst.onTy_append, ← hR₂ (S₁.onTy τ), hR₁ τ], hR₂lc⟩
  | _, _, _, @UnifyRel.pair a b c d S₁ S₂ h₁ h₂, S', hlc, hS' => by
    simp only [Unifies, Subst.onTy_pair, Ty.pair.injEq] at hS'
    obtain ⟨hac, hbd⟩ := hS'
    obtain ⟨R₁, hR₁, hR₁lc⟩ := UnifyRel.greatest_lc h₁ S' hlc hac
    have hR₁bd : Unifies R₁ (S₁.onTy b) (S₁.onTy d) := by
      show R₁.onTy (S₁.onTy b) = R₁.onTy (S₁.onTy d)
      rw [← hR₁ b, ← hR₁ d]; exact hbd
    obtain ⟨R₂, hR₂, hR₂lc⟩ := UnifyRel.greatest_lc h₂ R₁ hR₁lc hR₁bd
    exact ⟨R₂, fun τ => by rw [Subst.onTy_append, ← hR₂ (S₁.onTy τ), hR₁ τ], hR₂lc⟩
  | _, _, _, .customTy hl, S', hlc, hS' => by
    simp only [Unifies, Subst.onTy_customTy, Ty.customTy.injEq, true_and] at hS'
    exact UnifyRelList.greatest_lc hl S' hlc hS'

theorem UnifyRelList.greatest_lc : {ts₁ ts₂ : List Ty} → {S : Subst} →
    UnifyRelList ts₁ ts₂ S → ∀ S' : Subst, (∀ p ∈ S', p.2.IsLC) →
      ts₁.map S'.onTy = ts₂.map S'.onTy →
      ∃ R : Subst, (∀ τ, S'.onTy τ = R.onTy (S.onTy τ)) ∧ (∀ p ∈ R, p.2.IsLC)
  | _, _, _, .nil, S', hlc, _ => ⟨S', fun τ => by simp only [Subst.onTy_nil], hlc⟩
  | _, _, _, @UnifyRelList.cons t₁ t₂ ts₁ ts₂ S₁ S₂ h₁ ht, S', hlc, hS' => by
    simp only [List.map_cons, List.cons.injEq] at hS'
    obtain ⟨ht1t2, htail⟩ := hS'
    obtain ⟨R₁, hR₁, hR₁lc⟩ := UnifyRel.greatest_lc h₁ S' hlc ht1t2
    have key : ∀ (l : List Ty), l.map (R₁.onTy ∘ S₁.onTy) = l.map S'.onTy := by
      intro l; apply List.map_congr_left; intro t _; exact (hR₁ t).symm
    have hlist : (ts₁.map S₁.onTy).map R₁.onTy = (ts₂.map S₁.onTy).map R₁.onTy := by
      rw [List.map_map, List.map_map, key, key]; exact htail
    obtain ⟨R₂, hR₂, hR₂lc⟩ := UnifyRelList.greatest_lc ht R₁ hR₁lc hlist
    exact ⟨R₂, fun τ => by rw [Subst.onTy_append, ← hR₂ (S₁.onTy τ), hR₁ τ], hR₂lc⟩
end

/-! A structural size on types (own measure; cleaner than `sizeOf` for the
    unification termination argument). -/
mutual
def Ty.size : Ty → Nat
  | .prim _ => 1
  | .bvar _ => 1
  | .fvar _ => 1
  | .pair a b => 1 + a.size + b.size
  | .arrow a b => 1 + a.size + b.size
  | .customTy _ tys => 1 + TyList.size tys
def TyList.size : List Ty → Nat
  | [] => 0
  | hd :: tl => hd.size + TyList.size tl
end

theorem TyList.size_mem_le {t : Ty} {tys : List Ty} (h : t ∈ tys) :
    t.size ≤ TyList.size tys := by
  induction tys with
  | nil => exact absurd h List.not_mem_nil
  | cons hd tl ih =>
    rcases List.mem_cons.mp h with rfl | h
    · simp only [TyList.size]; omega
    · have := ih h; simp only [TyList.size]; omega

@[simp] theorem Ty.size_pos : ∀ {τ : Ty}, 0 < τ.size
  | .prim _ => by simp only [Ty.size]; omega
  | .bvar _ => by simp only [Ty.size]; omega
  | .fvar _ => by simp only [Ty.size]; omega
  | .pair _ _ => by simp only [Ty.size]; omega
  | .arrow _ _ => by simp only [Ty.size]; omega
  | .customTy _ _ => by simp only [Ty.size]; omega

/-- Occurs-check via size: applying any substitution, a variable's image is no
    bigger than the image of any type containing it. -/
theorem Ty.size_onTy_fvar_le {S : Subst} {n : Nat} :
    ∀ {b : Ty}, n ∈ b.freeVars → (S.onTy (.fvar n)).size ≤ (S.onTy b).size := by
  intro b
  induction b using Ty.rec_strong with
  | prim p => simp [Ty.freeVars]
  | bvar i => simp [Ty.freeVars]
  | fvar m => intro h; simp only [Ty.freeVars, List.mem_singleton] at h; subst h; exact le_refl _
  | pair a b iha ihb =>
    intro h
    simp only [Ty.freeVars, List.mem_dedup, List.mem_append] at h
    simp only [Subst.onTy_pair, Ty.size]
    rcases h with h | h
    · have := iha h; omega
    · have := ihb h; omega
  | arrow a b iha ihb =>
    intro h
    simp only [Ty.freeVars, List.mem_dedup, List.mem_append] at h
    simp only [Subst.onTy_arrow, Ty.size]
    rcases h with h | h
    · have := iha h; omega
    · have := ihb h; omega
  | customTy nm tys ih =>
    intro h
    simp only [Ty.freeVars] at h
    simp only [Subst.onTy_customTy, Ty.size]
    obtain ⟨t, ht, hnt⟩ : ∃ t ∈ tys, n ∈ t.freeVars := by
      by_contra hc; push_neg at hc
      exact (TyList.not_mem_freeVars_iff.mpr hc) h
    have h1 := ih t ht hnt
    have h2 : (S.onTy t).size ≤ TyList.size (tys.map S.onTy) :=
      TyList.size_mem_le (List.mem_map.mpr ⟨t, ht, rfl⟩)
    omega

/-- The strict occurs-check: a variable's image is strictly smaller than the
    image of a *compound* type containing it. -/
theorem Ty.size_onTy_fvar_lt {S : Subst} {n : Nat} {b : Ty}
    (hmem : n ∈ b.freeVars) (hne : b ≠ .fvar n) :
    (S.onTy (.fvar n)).size < (S.onTy b).size := by
  cases b with
  | prim p => simp [Ty.freeVars] at hmem
  | bvar i => simp [Ty.freeVars] at hmem
  | fvar m => simp only [Ty.freeVars, List.mem_singleton] at hmem; subst hmem; exact absurd rfl hne
  | pair a b =>
    simp only [Ty.freeVars, List.mem_dedup, List.mem_append] at hmem
    simp only [Subst.onTy_pair, Ty.size]
    rcases hmem with h | h
    · have := Ty.size_onTy_fvar_le (S := S) (n := n) h; have := @Ty.size_pos (S.onTy b); omega
    · have := Ty.size_onTy_fvar_le (S := S) (n := n) h; have := @Ty.size_pos (S.onTy a); omega
  | arrow a b =>
    simp only [Ty.freeVars, List.mem_dedup, List.mem_append] at hmem
    simp only [Subst.onTy_arrow, Ty.size]
    rcases hmem with h | h
    · have := Ty.size_onTy_fvar_le (S := S) (n := n) h; have := @Ty.size_pos (S.onTy b); omega
    · have := Ty.size_onTy_fvar_le (S := S) (n := n) h; have := @Ty.size_pos (S.onTy a); omega
  | customTy nm tys =>
    simp only [Ty.freeVars] at hmem
    simp only [Subst.onTy_customTy, Ty.size]
    obtain ⟨t, ht, hnt⟩ : ∃ t ∈ tys, n ∈ t.freeVars := by
      by_contra hc; push_neg at hc
      exact (TyList.not_mem_freeVars_iff.mpr hc) hmem
    have h1 := Ty.size_onTy_fvar_le (S := S) (n := n) hnt
    have h2 : (S.onTy t).size ≤ TyList.size (tys.map S.onTy) :=
      TyList.size_mem_le (List.mem_map.mpr ⟨t, ht, rfl⟩)
    omega

/-- Unification completeness (+ the list version), bounded by the measure
    `2 * (size of the unified result) + flag` so a single strong induction on the
    bound `N` covers all recursive calls (`flag = 0` for `UnifyRel`, `1` for the
    list — the offset makes the singleton-list ↔ element step strictly decrease). -/
theorem UnifyRel.complete_aux : ∀ (N : Nat),
    (∀ {a b : Ty} {U : Subst}, 2 * (U.onTy a).size < N → a.IsLC → b.IsLC →
        Unifies U a b → ∃ S, UnifyRel a b S) ∧
    (∀ {as bs : List Ty} {U : Subst}, 2 * TyList.size (as.map U.onTy) + 1 < N →
        (∀ t ∈ as, t.IsLC) → (∀ t ∈ bs, t.IsLC) → as.length = bs.length →
        as.map U.onTy = bs.map U.onTy → ∃ S, UnifyRelList as bs S) := by
  intro N
  induction N with
  | zero => exact ⟨fun h => absurd h (by omega), fun h => absurd h (by omega)⟩
  | succ N ih =>
    obtain ⟨ihU, ihL⟩ := ih
    refine ⟨?_, ?_⟩
    · -- UnifyRel
      intro a b U hsz ha hb hU
      cases a with
      | bvar i => cases ha with | bvar h => omega
      | prim p =>
        cases b with
        | bvar i => cases hb with | bvar h => omega
        | prim q =>
          simp only [Unifies, Subst.onTy_prim, Ty.prim.injEq] at hU
          subst hU; exact ⟨[], .prim⟩
        | fvar m => exact ⟨[(m, .prim p)], .fvarR (by simp) (by simp [Ty.freeVars])⟩
        | pair b₁ b₂ => simp [Unifies] at hU
        | arrow b₁ b₂ => simp [Unifies] at hU
        | customTy nm bs => simp [Unifies] at hU
      | fvar n =>
        cases b with
        | bvar i => cases hb with | bvar h => omega
        | fvar m =>
          by_cases hnm : n = m
          · subst hnm; exact ⟨[], .fvarRefl⟩
          · exact ⟨[(n, .fvar m)], .fvarL (by simp only [ne_eq, Ty.fvar.injEq]; omega)
              (by simp only [Ty.freeVars, List.mem_singleton]; omega)⟩
        | prim q =>
          by_cases hocc : n ∈ (Ty.prim q).freeVars
          · have hlt := Ty.size_onTy_fvar_lt (S := U) hocc (by simp)
            simp only [Unifies] at hU; rw [hU] at hlt; omega
          · exact ⟨[(n, .prim q)], .fvarL (by simp) hocc⟩
        | pair b₁ b₂ =>
          by_cases hocc : n ∈ (Ty.pair b₁ b₂).freeVars
          · have hlt := Ty.size_onTy_fvar_lt (S := U) hocc (by simp)
            simp only [Unifies] at hU; rw [hU] at hlt; omega
          · exact ⟨[(n, .pair b₁ b₂)], .fvarL (by simp) hocc⟩
        | arrow b₁ b₂ =>
          by_cases hocc : n ∈ (Ty.arrow b₁ b₂).freeVars
          · have hlt := Ty.size_onTy_fvar_lt (S := U) hocc (by simp)
            simp only [Unifies] at hU; rw [hU] at hlt; omega
          · exact ⟨[(n, .arrow b₁ b₂)], .fvarL (by simp) hocc⟩
        | customTy nm bs =>
          by_cases hocc : n ∈ (Ty.customTy nm bs).freeVars
          · have hlt := Ty.size_onTy_fvar_lt (S := U) hocc (by simp)
            simp only [Unifies] at hU; rw [hU] at hlt; omega
          · exact ⟨[(n, .customTy nm bs)], .fvarL (by simp) hocc⟩
      | pair a₁ a₂ =>
        cases ha with
        | pair ha₁ ha₂ =>
        cases b with
        | bvar i => cases hb with | bvar h => omega
        | fvar m =>
          by_cases hocc : m ∈ (Ty.pair a₁ a₂).freeVars
          · have hlt := Ty.size_onTy_fvar_lt (S := U) hocc (by simp)
            simp only [Unifies] at hU; rw [hU] at hlt; omega
          · exact ⟨[(m, .pair a₁ a₂)], .fvarR (by simp) hocc⟩
        | prim q => simp [Unifies] at hU
        | arrow b₁ b₂ => simp [Unifies] at hU
        | customTy nm bs => simp [Unifies] at hU
        | pair b₁ b₂ =>
          cases hb with
          | pair hb₁ hb₂ =>
          have hpsz : (U.onTy (.pair a₁ a₂)).size
              = 1 + (U.onTy a₁).size + (U.onTy a₂).size := by simp [Subst.onTy_pair, Ty.size]
          simp only [Unifies, Subst.onTy_pair, Ty.pair.injEq] at hU
          obtain ⟨S₁, h₁⟩ := ihU (a := a₁) (b := b₁) (U := U)
            (by rw [hpsz] at hsz; omega) ha₁ hb₁ hU.1
          obtain ⟨R, hR⟩ := UnifyRel.greatest h₁ U hU.1
          have hS₁lc := UnifyRel.lc h₁ ha₁ hb₁
          obtain ⟨S₂, h₂⟩ := ihU (a := S₁.onTy a₂) (b := S₁.onTy b₂) (U := R)
            (by rw [← hR a₂]; rw [hpsz] at hsz; omega)
            (Subst.onTy_lc hS₁lc ha₂) (Subst.onTy_lc hS₁lc hb₂)
            (by show R.onTy (S₁.onTy a₂) = R.onTy (S₁.onTy b₂); rw [← hR a₂, ← hR b₂]; exact hU.2)
          exact ⟨S₁ ++ S₂, .pair h₁ h₂⟩
      | arrow a₁ a₂ =>
        cases ha with
        | arrow ha₁ ha₂ =>
        cases b with
        | bvar i => cases hb with | bvar h => omega
        | fvar m =>
          by_cases hocc : m ∈ (Ty.arrow a₁ a₂).freeVars
          · have hlt := Ty.size_onTy_fvar_lt (S := U) hocc (by simp)
            simp only [Unifies] at hU; rw [hU] at hlt; omega
          · exact ⟨[(m, .arrow a₁ a₂)], .fvarR (by simp) hocc⟩
        | prim q => simp [Unifies] at hU
        | pair b₁ b₂ => simp [Unifies] at hU
        | customTy nm bs => simp [Unifies] at hU
        | arrow b₁ b₂ =>
          cases hb with
          | arrow hb₁ hb₂ =>
          have hpsz : (U.onTy (.arrow a₁ a₂)).size
              = 1 + (U.onTy a₁).size + (U.onTy a₂).size := by simp [Subst.onTy_arrow, Ty.size]
          simp only [Unifies, Subst.onTy_arrow, Ty.arrow.injEq] at hU
          obtain ⟨S₁, h₁⟩ := ihU (a := a₁) (b := b₁) (U := U)
            (by rw [hpsz] at hsz; omega) ha₁ hb₁ hU.1
          obtain ⟨R, hR⟩ := UnifyRel.greatest h₁ U hU.1
          have hS₁lc := UnifyRel.lc h₁ ha₁ hb₁
          obtain ⟨S₂, h₂⟩ := ihU (a := S₁.onTy a₂) (b := S₁.onTy b₂) (U := R)
            (by rw [← hR a₂]; rw [hpsz] at hsz; omega)
            (Subst.onTy_lc hS₁lc ha₂) (Subst.onTy_lc hS₁lc hb₂)
            (by show R.onTy (S₁.onTy a₂) = R.onTy (S₁.onTy b₂); rw [← hR a₂, ← hR b₂]; exact hU.2)
          exact ⟨S₁ ++ S₂, .arrow h₁ h₂⟩
      | customTy nm tys₁ =>
        cases b with
        | bvar i => cases hb with | bvar h => omega
        | fvar m =>
          by_cases hocc : m ∈ (Ty.customTy nm tys₁).freeVars
          · have hlt := Ty.size_onTy_fvar_lt (S := U) hocc (by simp)
            simp only [Unifies] at hU; rw [hU] at hlt; omega
          · exact ⟨[(m, .customTy nm tys₁)], .fvarR (by simp) hocc⟩
        | prim q => simp [Unifies] at hU
        | pair b₁ b₂ => simp [Unifies] at hU
        | arrow b₁ b₂ => simp [Unifies] at hU
        | customTy nm' tys₂ =>
          have hcsz : (U.onTy (.customTy nm tys₁)).size
              = 1 + TyList.size (tys₁.map U.onTy) := by simp [Subst.onTy_customTy, Ty.size]
          simp only [Unifies, Subst.onTy_customTy, Ty.customTy.injEq] at hU
          obtain ⟨rfl, hmapeq⟩ := hU
          have hlen : tys₁.length = tys₂.length := by
            have := congrArg List.length hmapeq; simpa using this
          obtain ⟨S, hS⟩ := ihL (as := tys₁) (bs := tys₂) (U := U)
            (by rw [hcsz] at hsz; omega)
            (fun t ht => by cases ha with | customTy h => exact h t ht)
            (fun t ht => by cases hb with | customTy h => exact h t ht)
            hlen hmapeq
          exact ⟨S, .customTy hS⟩
    · -- UnifyRelList
      intro as bs U hsz has hbs hlen hmap
      cases as with
      | nil =>
        cases bs with
        | nil => exact ⟨[], .nil⟩
        | cons t₂ ts₂ => simp at hlen
      | cons t₁ ts₁ =>
        cases bs with
        | nil => simp at hlen
        | cons t₂ ts₂ =>
          simp only [List.map_cons, List.cons.injEq] at hmap
          have htsz : TyList.size ((t₁ :: ts₁).map U.onTy)
              = (U.onTy t₁).size + TyList.size (ts₁.map U.onTy) := by
            simp [List.map_cons, TyList.size]
          have ht1pos := @Ty.size_pos (U.onTy t₁)
          obtain ⟨S₁, h₁⟩ := ihU (a := t₁) (b := t₂) (U := U)
            (by rw [htsz] at hsz; omega) (has t₁ List.mem_cons_self)
            (hbs t₂ List.mem_cons_self) hmap.1
          obtain ⟨R, hR⟩ := UnifyRel.greatest h₁ U hmap.1
          have hS₁lc := UnifyRel.lc h₁ (has t₁ List.mem_cons_self) (hbs t₂ List.mem_cons_self)
          have key : ∀ l : List Ty, l.map (R.onTy ∘ S₁.onTy) = l.map U.onTy := by
            intro l; apply List.map_congr_left; intro t _; exact (hR t).symm
          have hkey1 : (ts₁.map S₁.onTy).map R.onTy = ts₁.map U.onTy := by
            rw [List.map_map]; exact key ts₁
          have hmaptail : (ts₁.map S₁.onTy).map R.onTy = (ts₂.map S₁.onTy).map R.onTy := by
            rw [List.map_map, List.map_map, key, key]; exact hmap.2
          obtain ⟨S₂, h₂⟩ := ihL (as := ts₁.map S₁.onTy) (bs := ts₂.map S₁.onTy) (U := R)
            (by rw [hkey1]; rw [htsz] at hsz; omega)
            (by
              intro t ht; obtain ⟨t0, ht0, rfl⟩ := List.mem_map.mp ht
              exact Subst.onTy_lc hS₁lc (has t0 (List.mem_cons_of_mem _ ht0)))
            (by
              intro t ht; obtain ⟨t0, ht0, rfl⟩ := List.mem_map.mp ht
              exact Subst.onTy_lc hS₁lc (hbs t0 (List.mem_cons_of_mem _ ht0)))
            (by simp only [List.length_map]; have := hlen; simpa using this)
            hmaptail
          exact ⟨S₁ ++ S₂, .cons h₁ h₂⟩

/-- Unification completeness: if `a` and `b` (both LC) have a unifier `U`, then a
    `UnifyRel` derivation exists. -/
theorem UnifyRel.complete {a b : Ty} {U : Subst}
    (ha : a.IsLC) (hb : b.IsLC) (hU : Unifies U a b) : ∃ S, UnifyRel a b S :=
  (UnifyRel.complete_aux (2 * (U.onTy a).size + 1)).1 (by omega) ha hb hU

/-- Principality, application case (factored with named binders). Recurse on `f`
    then `arg`; the declarative typing yields a unifier of `S₂.onTy τf` and
    `arrow τa (.fvar Φ₂)` — exhibited explicitly as `[(Φ₂,.fvar W)] ++ R₂ ++ [(W,τ₀)]`
    (`W` fresh) so no derivation renaming is needed — which `UnifyRel.complete`
    realises as a derivation `S₃`, and `greatest_lc` factors through to the
    residual. -/
theorem Infer.complete_app_aux {f arg : Expr} {Φ : Nat} {ctx : Ctx} {S₀ : Subst}
    {argTy τ₀ : Ty}
    (ihf : Infer.CompleteAt f) (iharg : Infer.CompleteAt arg)
    (hwf : CtxWF ctx) (hbelow : CtxBelow Φ ctx) (hS₀ : ∀ p ∈ S₀, p.2.IsLC)
    (hf : TypeOfHM (S₀.onCtx ctx) f (.arrow argTy τ₀))
    (harg : TypeOfHM (S₀.onCtx ctx) arg argTy) :
    ∃ Φ' S τ R,
      Infer Φ ctx (.app f arg) Φ' S τ ∧
      (∀ v, v < Φ → S₀.onTy (.fvar v) = (S ++ R).onTy (.fvar v)) ∧
      τ₀ = R.onTy τ ∧
      (∀ p ∈ R, p.2.IsLC) := by
  -- STEP 1: recurse on `f`.
  obtain ⟨Φ₁, S₁, τf, R₁, hinff, hagf, htyf, hR₁⟩ := ihf hwf hbelow hS₀ hf
  have hS₁ := (Infer.lc hinff hwf).2
  have hbf := Infer.belowFvars hinff hbelow
  have hle1 := Infer.frontier_le hinff
  have hwf₁ := Subst.onCtx_wf hS₁ hwf
  have hbelow₁ := Subst.onCtx_below hbf.2 hle1 hbelow
  -- STEP 2: recurse on `arg`.
  have hctxeq : R₁.onCtx (S₁.onCtx ctx) = S₀.onCtx ctx := by
    rw [← Subst.onCtx_append]
    exact Subst.onCtx_congr (fun v hv => (hagf v hv).symm) hbelow
  have harg' : TypeOfHM (R₁.onCtx (S₁.onCtx ctx)) arg argTy := by
    rw [hctxeq]; exact harg
  obtain ⟨Φ₂, S₂, τa, R₂, hinfa, haga, htya, hR₂⟩ := iharg hwf₁ hbelow₁ hR₁ harg'
  have hS₂ := (Infer.lc hinfa hwf₁).2
  have hba := Infer.belowFvars hinfa hbelow₁
  have hle2 := Infer.frontier_le hinfa
  have hτfLC := (Infer.lc hinff hwf).1
  have hτaLC := (Infer.lc hinfa hwf₁).1
  -- STEP 3: key equalities.
  have hcongr_f : R₁.onTy τf = (S₂ ++ R₂).onTy τf := Subst.onTy_congr haga hbf.1
  have hP : R₂.onTy (S₂.onTy τf) = Ty.arrow argTy τ₀ := by
    rw [← Subst.onTy_append, ← hcongr_f]; exact htyf.symm
  have hΦ₂τf : Φ₂ ∉ (S₂.onTy τf).freeVars := fun hm => by
    have := (Subst.onTy_belowFvars hba.2 (hbf.1.mono hle2)).mem_lt _ hm
    omega
  have hΦ₂τa : Φ₂ ∉ τa.freeVars := fun hm => by
    have := hba.1.mem_lt _ hm
    omega
  have hτ₀LC : τ₀.IsLC := by
    have hreg := TypeOfHM.regular hf
    cases hreg with
    | arrow _ hT => exact hT
  -- STEP 4: a fresh variable `W`.
  obtain ⟨W, hWge, hWfresh⟩ := exists_fresh_block
    (R₂.map Prod.fst ++ R₂.flatMap (fun p => p.2.freeVars) ++ argTy.freeVars ++ τ₀.freeVars) Φ₂ 1
  have hWdom : ∀ p ∈ R₂, p.1 ≠ W := by
    intro p hp he
    have := hWfresh p.1 (List.mem_append_left _ (List.mem_append_left _
      (List.mem_append_left _ (List.mem_map.mpr ⟨p, hp, rfl⟩))))
    omega
  have hWrange : ∀ p ∈ R₂, W ∉ p.2.freeVars := by
    intro p hp hc
    have := hWfresh W (List.mem_append_left _ (List.mem_append_left _
      (List.mem_append_right _ (List.mem_flatMap.mpr ⟨p, hp, hc⟩))))
    omega
  have hWargTy : W ∉ argTy.freeVars := fun hc => by
    have := hWfresh W (List.mem_append_left _ (List.mem_append_right _ hc)); omega
  have hWτ₀ : W ∉ τ₀.freeVars := fun hc => by
    have := hWfresh W (List.mem_append_right _ hc); omega
  have hR₂Wfvar : R₂.onTy (Ty.fvar W) = Ty.fvar W := by
    apply Ty.substFvars_eq_self_of_no_key
    intro p hp hc
    simp only [Ty.freeVars, List.mem_singleton] at hc
    exact hWdom p hp hc
  -- STEP 5: the explicit unifier `U`.
  obtain ⟨U, hUdef⟩ : ∃ U : Subst, U = [(Φ₂, Ty.fvar W)] ++ R₂ ++ [(W, τ₀)] := ⟨_, rfl⟩
  have hsingle : ∀ (Z : Nat) (V y : Ty), Subst.onTy [(Z, V)] y = Ty.substFvar Z V y :=
    fun _ _ _ => rfl
  have hsubArrow : ∀ (Z : Nat) (V a b : Ty),
      Ty.substFvar Z V (Ty.arrow a b) = Ty.arrow (Ty.substFvar Z V a) (Ty.substFvar Z V b) :=
    fun _ _ _ _ => rfl
  have hUonTy : ∀ x, U.onTy x = Ty.substFvar W τ₀ (R₂.onTy (Ty.substFvar Φ₂ (Ty.fvar W) x)) := by
    intro x
    rw [hUdef, Subst.onTy_append, Subst.onTy_append, hsingle, hsingle]
  have e1 : Ty.substFvar Φ₂ (Ty.fvar W) (Ty.fvar Φ₂) = Ty.fvar W := by simp [Ty.substFvar]
  have e2 : Ty.substFvar W τ₀ (Ty.fvar W) = τ₀ := by simp [Ty.substFvar]
  have hUniL : U.onTy (S₂.onTy τf) = Ty.arrow argTy τ₀ := by
    rw [hUonTy, Ty.substFvar_fresh hΦ₂τf, hP, hsubArrow,
        Ty.substFvar_fresh hWargTy, Ty.substFvar_fresh hWτ₀]
  have hUniR : U.onTy (Ty.arrow τa (Ty.fvar Φ₂)) = Ty.arrow argTy τ₀ := by
    rw [hUonTy, hsubArrow, Ty.substFvar_fresh hΦ₂τa, e1, Subst.onTy_arrow,
        hR₂Wfvar, ← htya, hsubArrow, Ty.substFvar_fresh hWargTy, e2]
  have hUni : Unifies U (S₂.onTy τf) (Ty.arrow τa (Ty.fvar Φ₂)) := by
    show U.onTy (S₂.onTy τf) = U.onTy (Ty.arrow τa (Ty.fvar Φ₂))
    rw [hUniL, hUniR]
  -- STEP 6: realise the unifier as a derivation `S₃`.
  obtain ⟨S₃, h₃⟩ := UnifyRel.complete (Subst.onTy_lc hS₂ hτfLC)
    (.arrow hτaLC ContainsBvarsUpTo.fvar) hUni
  -- STEP 7: factor `U` through `S₃`.
  have hUlc : ∀ p ∈ U, p.2.IsLC := by
    rw [hUdef]
    intro p hp
    rcases List.mem_append.mp hp with hp' | hp'
    · rcases List.mem_append.mp hp' with hp'' | hp''
      · obtain rfl := List.mem_singleton.mp hp''
        exact ContainsBvarsUpTo.fvar
      · exact hR₂ p hp''
    · obtain rfl := List.mem_singleton.mp hp'
      exact hτ₀LC
  obtain ⟨R₃, hR₃, hR₃lc⟩ := UnifyRel.greatest_lc h₃ U hUlc hUni
  -- STEP 8: assemble.
  refine ⟨Φ₂ + 1, S₁ ++ S₂ ++ S₃, S₃.onTy (Ty.fvar Φ₂), R₃,
    Infer.app hinff hinfa h₃, ?_, ?_, hR₃lc⟩
  · intro v hv
    have ht1 : Ty.BelowFvars Φ₁ (S₁.onTy (Ty.fvar v)) :=
      Subst.onTy_belowFvars hbf.2 (Ty.BelowFvars.fvar (by omega))
    have ht : Ty.BelowFvars Φ₂ (S₂.onTy (S₁.onTy (Ty.fvar v))) :=
      Subst.onTy_belowFvars hba.2 (ht1.mono hle2)
    have hΦ₂t : Φ₂ ∉ (S₂.onTy (S₁.onTy (Ty.fvar v))).freeVars := fun hm => by
      have := ht.mem_lt _ hm; omega
    have hWt : W ∉ (S₂.onTy (S₁.onTy (Ty.fvar v))).freeVars := fun hm => by
      have := ht.mem_lt _ hm; omega
    have hWR₂t : W ∉ (R₂.onTy (S₂.onTy (S₁.onTy (Ty.fvar v)))).freeVars :=
      Subst.not_mem_onTy_freeVars hWrange hWt
    simp only [Subst.onTy_append]
    rw [← hR₃ (S₂.onTy (S₁.onTy (Ty.fvar v))), hUonTy,
        Ty.substFvar_fresh hΦ₂t, Ty.substFvar_fresh hWR₂t,
        hagf v hv, Subst.onTy_append, Subst.onTy_congr haga ht1, Subst.onTy_append]
  · rw [← hR₃ (Ty.fvar Φ₂), hUonTy, e1, hR₂Wfvar, e2]

/-- Principality, application case. -/
theorem Infer.complete_app {f arg : Expr}
    (ihf : Infer.CompleteAt f) (iharg : Infer.CompleteAt arg) :
    Infer.CompleteAt (.app f arg) := by
  intro Φ ctx S₀ τ₀ hwf hbelow hS₀ hty
  cases hty with
  | app hf harg => exact Infer.complete_app_aux ihf iharg hwf hbelow hS₀ hf harg


/-! ### Scheme weakening (for the `letIn` principality case)

The algorithm generalises the rhs's principal type with `genScheme`, the
*maximal* generalisation; the declarative scheme `M` is less general. Giving the
let-bound variable a more general scheme preserves typing: every instance the
body used is still available. -/

/-- `M'` is at least as general as `M`: every instantiation of `M` is also an
    instantiation of `M'`. -/
def PolyTy.Generalizes (M' M : PolyTy) : Prop :=
  ∀ tyArgs ty, (∀ t ∈ tyArgs, t.IsLC) → InstantiatesBy tyArgs M.body ty →
    ∃ tyArgs', (∀ t ∈ tyArgs', t.IsLC) ∧ InstantiatesBy tyArgs' M'.body ty

/-- Replacing a context scheme `M` by a more general `M'` preserves typing. -/
theorem TypeOfHM.weaken_scheme {ctors : CtorEnv} {env_post env : Env} {M M' : PolyTy}
    {e : Expr} {τ : Ty}
    (hgen : M'.Generalizes M)
    (h : TypeOfHM ⟨env_post ++ [M] ++ env, ctors⟩ e τ) :
    TypeOfHM ⟨env_post ++ [M'] ++ env, ctors⟩ e τ := by
  induction e using Expr.rec_strong generalizing env_post τ with
  | primLit p =>
    cases h <;> constructor
  | pair a b ih_a ih_b =>
    cases h with
    | pair ha hb => exact .pair (ih_a ha) (ih_b hb)
  | app f inp ih_f ih_i =>
    cases h with
    | app hf hi => exact .app (ih_f hf) (ih_i hi)
  | lambda body ih =>
    cases h with
    | lambda hpc heq hbody =>
      subst heq
      refine TypeOfHM.lambda hpc rfl ?_
      exact ih (env_post := PolyTy.mkTrivial _ :: env_post) hbody
  | letIn be body ih_be ih_body =>
    cases h with
    | letIn hsch hcofin heq hbody =>
      subst heq
      refine TypeOfHM.letIn hsch (fun Xs hfresh => ih_be (hcofin Xs hfresh)) rfl ?_
      exact ih_body (env_post := _ :: env_post) hbody
  | letPairIn pe body ih_pe ih_body =>
    cases h with
    | letPairIn hschf hschs harity hcofin heq hbody =>
      subst heq
      refine TypeOfHM.letPairIn hschf hschs harity
        (fun Xs hfresh => ih_pe (hcofin Xs hfresh)) rfl ?_
      exact ih_body (env_post := _ :: _ :: env_post) hbody
  | ctor name =>
    cases h with
    | ctor hlook htyargs hinst => exact .ctor hlook htyargs hinst
  | var i =>
    cases h with
    | var hlook htyargs hinst =>
      rcases lt_trichotomy i env_post.length with hlt | heq | hgt
      · -- i < env_post.length: lookup falls in env_post (unchanged)
        refine TypeOfHM.var ?_ htyargs hinst
        show (env_post ++ [M'] ++ env)[i]? = _
        rw [List.append_assoc, List.getElem?_append_left hlt]
        rw [List.append_assoc, List.getElem?_append_left hlt] at hlook
        exact hlook
      · -- i = env_post.length: the M slot, use hgen
        subst heq
        rw [List.append_assoc, List.getElem?_append_right (Nat.le_refl _),
            Nat.sub_self] at hlook
        simp only [List.singleton_append, List.getElem?_cons_zero,
          Option.some.injEq] at hlook
        subst hlook
        obtain ⟨tyArgs', htyargs', hinst'⟩ := hgen _ _ htyargs hinst
        refine TypeOfHM.var ?_ htyargs' hinst'
        show (env_post ++ [M'] ++ env)[env_post.length]? = _
        rw [List.append_assoc, List.getElem?_append_right (Nat.le_refl _),
            Nat.sub_self]
        simp only [List.singleton_append, List.getElem?_cons_zero]
      · -- i > env_post.length: lookup falls in env (unchanged); slot length is 1
        refine TypeOfHM.var ?_ htyargs hinst
        show (env_post ++ [M'] ++ env)[i]? = _
        have hle : env_post.length ≤ i := by omega
        rw [List.append_assoc, List.getElem?_append_right hle] at hlook
        rw [List.append_assoc, List.getElem?_append_right hle]
        rw [show ([M] ++ env) = M :: env from rfl] at hlook
        rw [show ([M'] ++ env) = M' :: env from rfl]
        rw [show (i - env_post.length) = (i - env_post.length - 1) + 1 from by omega]
            at hlook ⊢
        simp only [List.getElem?_cons_succ] at hlook ⊢
        exact hlook
  | match_ scrut branches ih_scrut ih_branches =>
    cases h with
    | match_ h_scrut h_ne h_brs =>
      refine TypeOfHM.match_ (ih_scrut h_scrut) h_ne ?_
      intro branch h_mem
      obtain ⟨pat, body⟩ := branch
      have h_branch := h_brs (pat, body) h_mem
      cases h_branch with
      | mk h_lookup h_tyName h_paramCount h_contents h_inst h_pb h_ctx h_body =>
        subst h_ctx
        subst h_pb
        expose_names
        rw [show (instContents.map PolyTy.mkTrivial ++ (env_post ++ [M] ++ env))
              = (instContents.map PolyTy.mkTrivial ++ env_post) ++ [M] ++ env
              by rw [List.append_assoc, List.append_assoc, List.append_assoc]]
          at h_body
        have ih_body :=
          ih_branches pat body h_mem
            (env_post := instContents.map PolyTy.mkTrivial ++ env_post)
            h_body
        rw [show (instContents.map PolyTy.mkTrivial ++ env_post) ++ [M'] ++ env
              = instContents.map PolyTy.mkTrivial ++ (env_post ++ [M'] ++ env)
              by rw [List.append_assoc, List.append_assoc, List.append_assoc]]
          at ih_body
        exact TypeOfMatchBranch.mk h_lookup h_tyName h_paramCount h_contents
          h_inst rfl rfl ih_body


/-! ### Generalisation/substitution commutation lemmas (for `letIn` principality) -/

/-! Structural simp lemmas for `openWith` (the analogues for `openVars` already
    exist above, but `openWith` lacks them). -/
@[simp] private theorem Ty.openWith_prim {Vs : List Ty} {p : PrimTy} :
    Ty.openWith Vs (.prim p) = .prim p := rfl
@[simp] private theorem Ty.openWith_fvar {Vs : List Ty} {n : Nat} :
    Ty.openWith Vs (.fvar n) = .fvar n := rfl
@[simp] private theorem Ty.openWith_pair {Vs : List Ty} {a b : Ty} :
    Ty.openWith Vs (.pair a b) = .pair (Ty.openWith Vs a) (Ty.openWith Vs b) := rfl
@[simp] private theorem Ty.openWith_arrow {Vs : List Ty} {a b : Ty} :
    Ty.openWith Vs (.arrow a b) = .arrow (Ty.openWith Vs a) (Ty.openWith Vs b) := rfl
@[simp] private theorem Ty.openWith_customTy {Vs : List Ty} {nm : TyName} {tys : List Ty} :
    Ty.openWith Vs (.customTy nm tys) = .customTy nm (tys.map (Ty.openWith Vs)) := by
  unfold Ty.openWith
  simp only [Ty.instantiate, TyList.instantiate_eq_map]

/-- For a nodup list, `idxOf?` of the element at index `i` is `some i`. -/
private theorem List.idxOf?_getElem_self {α : Type*} [BEq α] [LawfulBEq α]
    {l : List α} (hnd : l.Nodup) {i : Nat} (hi : i < l.length) :
    l.idxOf? l[i] = some i := by
  induction l generalizing i with
  | nil => simp at hi
  | cons x xs ih =>
    rw [List.nodup_cons] at hnd
    cases i with
    | zero => simp [List.idxOf?_cons]
    | succ j =>
      have hj : j < xs.length := by simpa using hi
      have hmem : xs[j] ∈ xs := List.getElem_mem hj
      have hxne : (x == xs[j]) = false := by
        simp only [beq_eq_false_iff_ne, ne_eq]
        intro h; exact hnd.1 (h ▸ hmem)
      rw [List.getElem_cons_succ, List.idxOf?_cons, hxne]
      simp [ih hnd.2 hj]

/-- Applying an LC substitution commutes with bvar-instantiation. -/
theorem Subst.onTy_instantiate {S : Subst} (hS : ∀ p ∈ S, p.2.IsLC) (σ : Nat → Ty) (X : Ty) :
    S.onTy (Ty.instantiate σ X) = Ty.instantiate (fun i => S.onTy (σ i)) (S.onTy X) := by
  induction X using Ty.rec_strong with
  | prim p => simp only [Ty.instantiate, Subst.onTy_prim]
  | bvar i => simp only [Ty.instantiate, Subst.onTy_bvar]
  | fvar n =>
    simp only [Ty.instantiate]
    rw [Ty.instantiate_eq_self_of_lc (Subst.onTy_lc hS ContainsBvarsUpTo.fvar)]
  | pair a b iha ihb => simp only [Ty.instantiate, Subst.onTy_pair, iha, ihb]
  | arrow a b iha ihb => simp only [Ty.instantiate, Subst.onTy_arrow, iha, ihb]
  | customTy nm tys ih =>
    simp only [Ty.instantiate, TyList.instantiate_eq_map, Subst.onTy_customTy, List.map_map]
    apply congrArg (Ty.customTy nm)
    apply List.map_congr_left
    intro t ht
    simp only [Function.comp_apply]
    exact ih t ht

/-- `onTy` (LC) commutes with `openWith`. -/
theorem Subst.onTy_openWith {S : Subst} (hS : ∀ p ∈ S, p.2.IsLC) (Vs : List Ty) (X : Ty) :
    S.onTy (Ty.openWith Vs X) = Ty.openWith (Vs.map S.onTy) (S.onTy X) := by
  unfold Ty.openWith
  rw [Subst.onTy_instantiate hS]
  have hfun : (fun i => S.onTy ((Vs[i]?).getD (.bvar i)))
      = (fun i => ((Vs.map S.onTy)[i]?).getD (.bvar i)) := by
    funext i
    rw [List.getElem?_map]
    cases Vs[i]? with
    | none => simp
    | some t => simp
  rw [hfun]

/-- Open-then-close round-trip: closing the just-opened fresh names recovers the
    scheme body. (Converse of `Ty.openVars_closeOver_self`.) -/
theorem Ty.closeOver_openVars_self {Xs : List Nat} {ty : Ty}
    (hnodup : Xs.Nodup) (hbv : ContainsBvarsUpTo Xs.length ty)
    (hfresh : ∀ x ∈ Xs, x ∉ ty.freeVars) :
    Ty.closeOver Xs (Ty.openVars Xs ty) = ty := by
  induction ty using Ty.rec_strong with
  | prim p => rfl
  | bvar i =>
    cases hbv with
    | bvar hlt =>
      simp only [Ty.openVars, Ty.instantiate, List.getElem?_eq_getElem hlt, Option.elim_some]
      rw [Ty.closeOver.eq_6, List.idxOf?_getElem_self hnodup hlt]
  | fvar n =>
    have hn : n ∉ Xs := fun h => hfresh n h (by simp [Ty.freeVars])
    simp only [Ty.openVars, Ty.instantiate]
    rw [Ty.closeOver.eq_6, List.idxOf?_eq_none_iff.mpr hn]
  | pair a b iha ihb =>
    cases hbv with
    | pair hba hbb =>
      have hfa : ∀ x ∈ Xs, x ∉ a.freeVars := fun x hx hc =>
        hfresh x hx (List.mem_dedup.mpr (List.mem_append.mpr (Or.inl hc)))
      have hfb : ∀ x ∈ Xs, x ∉ b.freeVars := fun x hx hc =>
        hfresh x hx (List.mem_dedup.mpr (List.mem_append.mpr (Or.inr hc)))
      simp only [Ty.openVars_pair, Ty.closeOver, iha hba hfa, ihb hbb hfb]
  | arrow a b iha ihb =>
    cases hbv with
    | arrow hba hbb =>
      have hfa : ∀ x ∈ Xs, x ∉ a.freeVars := fun x hx hc =>
        hfresh x hx (List.mem_dedup.mpr (List.mem_append.mpr (Or.inl hc)))
      have hfb : ∀ x ∈ Xs, x ∉ b.freeVars := fun x hx hc =>
        hfresh x hx (List.mem_dedup.mpr (List.mem_append.mpr (Or.inr hc)))
      simp only [Ty.openVars_arrow, Ty.closeOver, iha hba hfa, ihb hbb hfb]
  | customTy nm tys ih =>
    cases hbv with
    | customTy hball =>
      simp only [Ty.openVars_customTy, Ty.closeOver, TyList.closeOver_eq_map, List.map_map]
      apply congrArg (Ty.customTy nm)
      conv_rhs => rw [← List.map_id tys]
      apply List.map_congr_left
      intro t ht
      exact ih t ht (hball t ht)
        (fun x hx hc => hfresh x hx (TyList.mem_freeVars_of_mem ht hc))

/-- Closing names fresh for `X` commutes into an `openWith`. -/
theorem Ty.closeOver_openWith_comm {Xs : List Nat} {Vs : List Ty} {X : Ty}
    (hfresh : ∀ x ∈ Xs, x ∉ X.freeVars) :
    Ty.closeOver Xs (Ty.openWith Vs X) = Ty.openWith (Vs.map (Ty.closeOver Xs)) X := by
  induction X using Ty.rec_strong with
  | prim p => rfl
  | bvar i =>
    simp only [Ty.openWith, Ty.instantiate]
    rw [List.getElem?_map]
    cases Vs[i]? with
    | none => simp [Ty.closeOver]
    | some t => simp
  | fvar n =>
    have hn : n ∉ Xs := fun h => hfresh n h (by simp [Ty.freeVars])
    simp only [Ty.openWith_fvar]
    rw [Ty.closeOver.eq_6, List.idxOf?_eq_none_iff.mpr hn]
  | pair a b iha ihb =>
    have hfa : ∀ x ∈ Xs, x ∉ a.freeVars := fun x hx hc =>
      hfresh x hx (List.mem_dedup.mpr (List.mem_append.mpr (Or.inl hc)))
    have hfb : ∀ x ∈ Xs, x ∉ b.freeVars := fun x hx hc =>
      hfresh x hx (List.mem_dedup.mpr (List.mem_append.mpr (Or.inr hc)))
    simp only [Ty.openWith_pair, Ty.closeOver, iha hfa, ihb hfb]
  | arrow a b iha ihb =>
    have hfa : ∀ x ∈ Xs, x ∉ a.freeVars := fun x hx hc =>
      hfresh x hx (List.mem_dedup.mpr (List.mem_append.mpr (Or.inl hc)))
    have hfb : ∀ x ∈ Xs, x ∉ b.freeVars := fun x hx hc =>
      hfresh x hx (List.mem_dedup.mpr (List.mem_append.mpr (Or.inr hc)))
    simp only [Ty.openWith_arrow, Ty.closeOver, iha hfa, ihb hfb]
  | customTy nm tys ih =>
    simp only [Ty.openWith_customTy, Ty.closeOver, TyList.closeOver_eq_map, List.map_map]
    apply congrArg (Ty.customTy nm)
    apply List.map_congr_left
    intro t ht
    simp only [Function.comp_apply]
    exact ih t ht (fun x hx hc => hfresh x hx (TyList.mem_freeVars_of_mem ht hc))

/-- Composition of openings (when `X`'s bvars are covered by the inner args). -/
theorem Ty.openWith_openWith {Vs Ws : List Ty} {X : Ty}
    (hbv : ContainsBvarsUpTo Ws.length X) :
    Ty.openWith Vs (Ty.openWith Ws X) = Ty.openWith (Ws.map (Ty.openWith Vs)) X := by
  induction X using Ty.rec_strong with
  | prim p => rfl
  | fvar n => rfl
  | bvar i =>
    cases hbv with
    | bvar hlt =>
      have hi : Ws[i]? = some Ws[i] := List.getElem?_eq_getElem hlt
      have e1 : Ty.openWith Ws (.bvar i) = Ws[i] := by
        simp only [Ty.openWith, Ty.instantiate, hi, Option.getD_some]
      have e2 : Ty.openWith (Ws.map (Ty.openWith Vs)) (.bvar i) = Ty.openWith Vs (Ws[i]) := by
        simp only [Ty.openWith, Ty.instantiate, List.getElem?_map, hi, Option.map_some,
          Option.getD_some]
      rw [e1, e2]
  | pair a b iha ihb =>
    cases hbv with
    | pair hba hbb =>
      simp only [Ty.openWith_pair, iha hba, ihb hbb]
  | arrow a b iha ihb =>
    cases hbv with
    | arrow hba hbb =>
      simp only [Ty.openWith_arrow, iha hba, ihb hbb]
  | customTy nm tys ih =>
    cases hbv with
    | customTy hball =>
      simp only [Ty.openWith_customTy, List.map_map]
      apply congrArg (Ty.customTy nm)
      apply List.map_congr_left
      intro t ht
      simp only [Function.comp_apply]
      exact ih t ht (hball t ht)

/-- Opening a scheme body with LC args is an instantiation by those args. -/
theorem InstantiatesBy.openWith {Vs : List Ty} {n : Nat} {ty : Ty}
    (hbv : ContainsBvarsUpTo n ty) (hn : n ≤ Vs.length) :
    InstantiatesBy Vs ty (Ty.openWith Vs ty) := by
  induction ty using Ty.rec_strong with
  | prim p => exact .prim
  | fvar m => exact .fvar
  | bvar i =>
    cases hbv with
    | bvar hlt =>
      have hi : i < Vs.length := by omega
      simp only [Ty.openWith, Ty.instantiate, List.getElem?_eq_getElem hi, Option.getD_some]
      exact .bvar (List.getElem?_eq_getElem hi)
  | pair a b iha ihb => cases hbv with | pair ha hb => exact .pair (iha ha) (ihb hb)
  | arrow a b iha ihb => cases hbv with | arrow ha hb => exact .arrow (iha ha) (ihb hb)
  | customTy nm tys ih =>
    cases hbv with
    | customTy hball =>
      simp only [Ty.openWith_customTy]
      exact .customTy (List.forall₂_self_map (fun t ht => ih t ht (hball t ht)))


/-! ### Free-var bounds (for the `letIn` principality freshness obligation) -/

/-- Membership in a type-list's free vars iff in some element's. -/
theorem TyList.mem_freeVars_iff {x : Nat} {tys : List Ty} :
    x ∈ TyList.freeVars tys ↔ ∃ t ∈ tys, x ∈ t.freeVars := by
  induction tys with
  | nil => simp [TyList.freeVars]
  | cons hd tl ih =>
    simp only [TyList.freeVars, List.mem_dedup, List.mem_append, List.mem_cons]
    rw [ih]
    constructor
    · rintro (h | ⟨t, ht, hx⟩)
      · exact ⟨hd, .inl rfl, h⟩
      · exact ⟨t, .inr ht, hx⟩
    · rintro ⟨t, (rfl | ht), hx⟩
      · exact .inl hx
      · exact .inr ⟨t, ht, hx⟩

/-- Every free var of `S.onTy Z` traces back to a free var of `Z`. -/
theorem Ty.mem_freeVars_onTy_iff {S : Subst} {x : Nat} {Z : Ty} :
    x ∈ (S.onTy Z).freeVars ↔ ∃ v ∈ Z.freeVars, x ∈ (S.onTy (.fvar v)).freeVars := by
  induction Z using Ty.rec_strong with
  | prim p => simp [Subst.onTy_prim, Ty.freeVars]
  | bvar i => simp [Subst.onTy_bvar, Ty.freeVars]
  | fvar n => simp only [Ty.freeVars, List.mem_singleton, exists_eq_left]
  | pair a b iha ihb =>
    simp only [Subst.onTy_pair, Ty.freeVars, List.mem_dedup, List.mem_append]
    rw [iha, ihb]
    constructor
    · rintro (⟨v, hv, hx⟩ | ⟨v, hv, hx⟩)
      · exact ⟨v, .inl hv, hx⟩
      · exact ⟨v, .inr hv, hx⟩
    · rintro ⟨v, (hv | hv), hx⟩
      · exact .inl ⟨v, hv, hx⟩
      · exact .inr ⟨v, hv, hx⟩
  | arrow a b iha ihb =>
    simp only [Subst.onTy_arrow, Ty.freeVars, List.mem_dedup, List.mem_append]
    rw [iha, ihb]
    constructor
    · rintro (⟨v, hv, hx⟩ | ⟨v, hv, hx⟩)
      · exact ⟨v, .inl hv, hx⟩
      · exact ⟨v, .inr hv, hx⟩
    · rintro ⟨v, (hv | hv), hx⟩
      · exact .inl ⟨v, hv, hx⟩
      · exact .inr ⟨v, hv, hx⟩
  | customTy nm tys ih =>
    simp only [Subst.onTy_customTy, Ty.freeVars]
    rw [TyList.mem_freeVars_iff]
    constructor
    · rintro ⟨t', ht', hx⟩
      obtain ⟨t, ht, rfl⟩ := List.mem_map.mp ht'
      obtain ⟨v, hv, hxv⟩ := (ih t ht).mp hx
      exact ⟨v, TyList.mem_freeVars_iff.mpr ⟨t, ht, hv⟩, hxv⟩
    · rintro ⟨v, hv, hx⟩
      obtain ⟨t, ht, hvt⟩ := TyList.mem_freeVars_iff.mp hv
      exact ⟨S.onTy t, List.mem_map.mpr ⟨t, ht, rfl⟩, (ih t ht).mpr ⟨v, hvt, hx⟩⟩

/-- Closing over vars only removes free vars. -/
theorem Ty.closeOver_freeVars_subset {gs : List Nat} {τ : Ty} :
    (Ty.closeOver gs τ).freeVars ⊆ τ.freeVars := by
  induction τ using Ty.rec_strong with
  | prim p => simp [Ty.closeOver, Ty.freeVars]
  | bvar i => simp [Ty.closeOver, Ty.freeVars]
  | fvar n =>
    rw [Ty.closeOver.eq_6]
    cases gs.idxOf? n with
    | none => exact fun x hx => hx
    | some i => simp [Ty.freeVars]
  | pair a b iha ihb =>
    intro x hx
    simp only [Ty.closeOver, Ty.freeVars, List.mem_dedup, List.mem_append] at hx ⊢
    rcases hx with h | h
    · exact .inl (iha h)
    · exact .inr (ihb h)
  | arrow a b iha ihb =>
    intro x hx
    simp only [Ty.closeOver, Ty.freeVars, List.mem_dedup, List.mem_append] at hx ⊢
    rcases hx with h | h
    · exact .inl (iha h)
    · exact .inr (ihb h)
  | customTy nm tys ih =>
    intro x hx
    simp only [Ty.closeOver, Ty.freeVars, TyList.closeOver_eq_map] at hx ⊢
    obtain ⟨t', ht', hxt⟩ := TyList.mem_freeVars_iff.mp hx
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp ht'
    exact TyList.mem_freeVars_iff.mpr ⟨t, ht, ih t ht hxt⟩


/-! ### Principal generalization generalizes the declarative scheme -/

/-- Opening a type whose bvars are `< n ≤ |Vs|` with LC args is LC. -/
theorem Ty.openWith_isLC {Vs : List Ty} {n : Nat} {X : Ty}
    (hVs : ∀ v ∈ Vs, v.IsLC) (hX : ContainsBvarsUpTo n X) (hn : n ≤ Vs.length) :
    (Ty.openWith Vs X).IsLC := by
  simp only [Ty.openWith]
  refine Ty.instantiate_isLC (fun i hi => ?_) hX
  simp only [List.getElem?_eq_getElem (show i < Vs.length by omega), Option.getD_some]
  exact hVs _ (List.getElem_mem _)

/-- The algorithm's principal generalization `genScheme env τ₁` (transported by
    the residual `R`) is at least as general as any declarative scheme `M` whose
    fresh opening factors as `R.onTy τ₁`. This is the crux of `letIn`
    principality: the body, declaratively typed under `M`, can be retyped under
    the more general scheme the algorithm produces. -/
theorem genScheme_generalizes {env : Env} {τ₁ : Ty} {R : Subst} {M : PolyTy} {Xs : List Nat}
    (hτ₁ : τ₁.IsLC) (hR : ∀ p ∈ R, p.2.IsLC) (hMwf : M.WF)
    (hXnodup : Xs.Nodup) (hXlen : Xs.length = M.paramCount)
    (hXMbody : ∀ x ∈ Xs, x ∉ M.body.freeVars)
    (htyr : Ty.openVars Xs M.body = R.onTy τ₁)
    (hXM'' : ∀ x ∈ Xs, x ∉ (R.onPolyTy (genScheme env τ₁)).body.freeVars) :
    (R.onPolyTy (genScheme env τ₁)).Generalizes M := by
  intro tyArgs ty htyargs_lc hinst
  -- `ty = openWith Vs M.body` for the length-`paramCount` prefix `Vs` of `tyArgs`.
  have hty_eq : ty = Ty.openWith
      ((List.range M.paramCount).map (fun i => (tyArgs[i]?).getD (.prim .unit))) M.body :=
    hinst.eq_openWith_range hMwf
  set Vs := (List.range M.paramCount).map (fun i => (tyArgs[i]?).getD (.prim .unit)) with hVsdef
  have hVs_len : Vs.length = M.paramCount := by rw [hVsdef]; simp
  have hVs_lc : ∀ v ∈ Vs, v.IsLC := by
    intro v hv
    rw [hVsdef] at hv
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hv
    cases hh : tyArgs[i]? with
    | none => simp only [hh, Option.getD_none]; exact ContainsBvarsUpTo.prim
    | some t => simp only [hh, Option.getD_some]; exact htyargs_lc t (List.mem_of_getElem? hh)
  -- `M.body = closeOver Xs (R.onTy τ₁)` (close the just-opened fresh names).
  have hMbody : M.body = Ty.closeOver Xs (R.onTy τ₁) := by
    have hbv : ContainsBvarsUpTo Xs.length M.body := by rw [hXlen]; exact hMwf
    have hrt := Ty.closeOver_openVars_self hXnodup hbv hXMbody
    rw [htyr] at hrt
    exact hrt.symm
  -- `R.onTy τ₁ = openWith Wg M'.body` where `Wg = R` applied to each gen var.
  have hRτ₁ : R.onTy τ₁ = Ty.openWith
      ((genVars env τ₁).map (fun gj => R.onTy (Ty.fvar gj)))
      ((R.onPolyTy (genScheme env τ₁)).body) := by
    show R.onTy τ₁ = Ty.openWith ((genVars env τ₁).map (fun gj => R.onTy (Ty.fvar gj)))
      (R.onTy (Ty.closeOver (genVars env τ₁) τ₁))
    conv_lhs => rw [← Ty.openVars_closeOver_self (gs := genVars env τ₁) hτ₁]
    rw [Ty.openVars_eq_openWith, Subst.onTy_openWith hR, List.map_map]
    simp only [Function.comp_def]
  -- Round-trip to `M'.body`, then re-open with the composed args.
  have hbv1 : ContainsBvarsUpTo
      (((genVars env τ₁).map (fun gj => R.onTy (Ty.fvar gj))).map (Ty.closeOver Xs)).length
      ((R.onPolyTy (genScheme env τ₁)).body) := by
    have hwf := Subst.onPolyTy_wf hR (genScheme_wf (env := env) hτ₁)
    have hlen : (((genVars env τ₁).map (fun gj => R.onTy (Ty.fvar gj))).map (Ty.closeOver Xs)).length
        = (R.onPolyTy (genScheme env τ₁)).paramCount := by
      simp only [List.length_map]; rfl
    rw [hlen]; exact hwf
  have hty_final : ty = Ty.openWith
      ((((genVars env τ₁).map (fun gj => R.onTy (Ty.fvar gj))).map (Ty.closeOver Xs)).map
        (Ty.openWith Vs))
      ((R.onPolyTy (genScheme env τ₁)).body) :=
    calc ty
        = Ty.openWith Vs M.body := hty_eq
      _ = Ty.openWith Vs (Ty.closeOver Xs (R.onTy τ₁)) := by rw [hMbody]
      _ = Ty.openWith Vs (Ty.closeOver Xs (Ty.openWith
            ((genVars env τ₁).map (fun gj => R.onTy (Ty.fvar gj)))
            ((R.onPolyTy (genScheme env τ₁)).body))) := by rw [hRτ₁]
      _ = Ty.openWith Vs (Ty.openWith
            (((genVars env τ₁).map (fun gj => R.onTy (Ty.fvar gj))).map (Ty.closeOver Xs))
            ((R.onPolyTy (genScheme env τ₁)).body)) := by
              rw [Ty.closeOver_openWith_comm hXM'']
      _ = Ty.openWith
            ((((genVars env τ₁).map (fun gj => R.onTy (Ty.fvar gj))).map (Ty.closeOver Xs)).map
              (Ty.openWith Vs))
            ((R.onPolyTy (genScheme env τ₁)).body) := by rw [Ty.openWith_openWith hbv1]
  -- The composed args are LC and witness the instantiation.
  refine ⟨(((genVars env τ₁).map (fun gj => R.onTy (Ty.fvar gj))).map (Ty.closeOver Xs)).map
      (Ty.openWith Vs), ?_, ?_⟩
  · intro v hv
    obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hv
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hz
    obtain ⟨gj, _, rfl⟩ := List.mem_map.mp hw
    have hwlc : (R.onTy (Ty.fvar gj)).IsLC := Subst.onTy_lc hR ContainsBvarsUpTo.fvar
    have hzbv : ContainsBvarsUpTo Xs.length (Ty.closeOver Xs (R.onTy (Ty.fvar gj))) :=
      Ty.closeOver_preserves_bvars hwlc
    exact Ty.openWith_isLC hVs_lc hzbv (by rw [hVs_len]; exact hXlen.le)
  · have hwf := Subst.onPolyTy_wf hR (genScheme_wf (env := env) hτ₁)
    have hVs'len : ((((genVars env τ₁).map (fun gj => R.onTy (Ty.fvar gj))).map
        (Ty.closeOver Xs)).map (Ty.openWith Vs)).length
        = (R.onPolyTy (genScheme env τ₁)).paramCount := by
      simp only [List.length_map]; rfl
    have hinstW := InstantiatesBy.openWith hwf (le_of_eq hVs'len.symm)
    rw [hty_final]
    exact hinstW


/-! ### Principality, `letIn` case -/

/-- The `letIn` principality core (inverted form, with the declarative scheme `M`
    and cofinite-fresh-set `L` named). Mirrors `Infer.sound_letIn`'s factoring to
    sidestep inaccessible binders. The algorithm infers the rhs to `(S₁, τ₁)` and
    generalizes with the principal `genScheme`; `genScheme_generalizes` shows that
    scheme weakens the declarative `M`, so the body — declaratively typed under
    `M` — retypes (`weaken_scheme`) under the algorithm's scheme, ready for the
    body IH. Assembly then mirrors `complete_pair`. -/
theorem Infer.complete_letIn_aux {Φ : Nat} {ctx : Ctx} {S₀ : Subst} {rhs body : Expr}
    {M : PolyTy} {L : List Nat} {τ₀ : Ty}
    (iha : Infer.CompleteAt rhs) (ihb : Infer.CompleteAt body)
    (hwf : CtxWF ctx) (hbelow : CtxBelow Φ ctx) (hS₀ : ∀ p ∈ S₀, p.2.IsLC)
    (hMwf : M.WF)
    (hcofin : ∀ Xs : List Nat, FreshNames L M.paramCount Xs →
      TypeOfHM (S₀.onCtx ctx) rhs (M.openVars Xs))
    (hbody : TypeOfHM { (S₀.onCtx ctx) with env := M :: (S₀.onCtx ctx).env } body τ₀) :
    ∃ Φ' S τ R,
      Infer Φ ctx (.letIn rhs body) Φ' S τ ∧
      (∀ v, v < Φ → S₀.onTy (.fvar v) = (S ++ R).onTy (.fvar v)) ∧
      τ₀ = R.onTy τ ∧
      (∀ p ∈ R, p.2.IsLC) := by
  -- A fresh opening avoiding `L`, `M.body`, and the (substituted) env.
  obtain ⟨Xs, hXlen, hXnodup, hXavoid⟩ :=
    exists_fresh_names (L ++ M.body.freeVars ++ (S₀.onCtx ctx).env.freeVars) M.paramCount
  have hXfreshL : FreshNames L M.paramCount Xs :=
    ⟨hXlen, hXnodup,
      fun x hx hc => hXavoid x hx (List.mem_append_left _ (List.mem_append_left _ hc))⟩
  have hXMbody : ∀ x ∈ Xs, x ∉ M.body.freeVars :=
    fun x hx hc => hXavoid x hx (List.mem_append_left _ (List.mem_append_right _ hc))
  have hXenv : ∀ x ∈ Xs, x ∉ (S₀.onCtx ctx).env.freeVars :=
    fun x hx hc => hXavoid x hx (List.mem_append_right _ hc)
  -- Apply the rhs IH at the fresh opening.
  obtain ⟨Φ₁, S₁, τ₁, R₁, hinfa, haga, htya, hR₁⟩ :=
    iha hwf hbelow hS₀ (hcofin Xs hXfreshL)
  have hS₁ : ∀ p ∈ S₁, p.2.IsLC := (Infer.lc hinfa hwf).2
  have hτ₁lc : τ₁.IsLC := (Infer.lc hinfa hwf).1
  have hle : Φ ≤ Φ₁ := Infer.frontier_le hinfa
  have hbelowτ₁ : Ty.BelowFvars Φ₁ τ₁ := (Infer.belowFvars hinfa hbelow).1
  have hbelowS₁ : ∀ p ∈ S₁, Ty.BelowFvars Φ₁ p.2 := (Infer.belowFvars hinfa hbelow).2
  have hwf₁ : CtxWF (S₁.onCtx ctx) := Subst.onCtx_wf hS₁ hwf
  have hbelow₁ : CtxBelow Φ₁ (S₁.onCtx ctx) := Subst.onCtx_below hbelowS₁ hle hbelow
  have hctxeq : R₁.onCtx (S₁.onCtx ctx) = S₀.onCtx ctx := by
    rw [← Subst.onCtx_append]
    exact Subst.onCtx_congr (fun v hv => (haga v hv).symm) hbelow
  -- Well-formedness / below-frontier for the algorithm's body context.
  have hwfBody : CtxWF { (S₁.onCtx ctx) with
      env := genScheme (S₁.onCtx ctx).env τ₁ :: (S₁.onCtx ctx).env } := by
    intro N hN
    rcases List.mem_cons.mp hN with rfl | hN
    · exact genScheme_wf hτ₁lc
    · exact hwf₁ N hN
  have hbelowBody : CtxBelow Φ₁ { (S₁.onCtx ctx) with
      env := genScheme (S₁.onCtx ctx).env τ₁ :: (S₁.onCtx ctx).env } := by
    intro N hN
    rcases List.mem_cons.mp hN with rfl | hN
    · show Ty.BelowFvars Φ₁ (Ty.closeOver (genVars (S₁.onCtx ctx).env τ₁) τ₁)
      exact hbelowτ₁.closeOver
    · exact hbelow₁ N hN
  -- The freshness obligation for `genScheme_generalizes`: the fresh `Xs` don't
  -- occur free in the (substituted) principal scheme body.
  have hXM'' : ∀ x ∈ Xs,
      x ∉ (R₁.onPolyTy (genScheme (S₁.onCtx ctx).env τ₁)).body.freeVars := by
    intro x hx hmem
    change x ∈ (R₁.onTy (Ty.closeOver (genVars (S₁.onCtx ctx).env τ₁) τ₁)).freeVars at hmem
    obtain ⟨v, hv, hxv⟩ := Ty.mem_freeVars_onTy_iff.mp hmem
    have hvτ₁ : v ∈ τ₁.freeVars := Ty.closeOver_freeVars_subset hv
    have hvg : v ∉ genVars (S₁.onCtx ctx).env τ₁ := fun hg => Ty.not_mem_closeOver_freeVars hg hv
    have hvenv : v ∈ (S₁.onCtx ctx).env.freeVars := by
      by_contra hc
      exact hvg (by
        simp only [genVars, List.mem_filter]
        exact ⟨hvτ₁, by simpa using hc⟩)
    obtain ⟨pt, hpt, hvpt⟩ := Env.mem_freeVars_iff.mp hvenv
    have hx_onTy : x ∈ (R₁.onTy pt.body).freeVars :=
      Ty.mem_freeVars_onTy_iff.mpr ⟨v, hvpt, hxv⟩
    have hpt_mem : R₁.onPolyTy pt ∈ (S₀.onCtx ctx).env := by
      have hmem2 : R₁.onPolyTy pt ∈ (R₁.onCtx (S₁.onCtx ctx)).env := by
        simp only [Subst.onCtx, Subst.onEnv]
        exact List.mem_map.mpr ⟨pt, hpt, rfl⟩
      rw [hctxeq] at hmem2; exact hmem2
    exact hXenv x hx (Env.mem_freeVars_iff.mpr ⟨R₁.onPolyTy pt, hpt_mem, hx_onTy⟩)
  -- Weaken the declarative body typing to the algorithm's (more general) scheme.
  have hgen : (R₁.onPolyTy (genScheme (S₁.onCtx ctx).env τ₁)).Generalizes M :=
    genScheme_generalizes hτ₁lc hR₁ hMwf hXnodup hXlen hXMbody htya hXM''
  have hbody' : TypeOfHM
      ⟨R₁.onPolyTy (genScheme (S₁.onCtx ctx).env τ₁) :: (S₀.onCtx ctx).env,
        (S₀.onCtx ctx).ctors⟩ body τ₀ :=
    TypeOfHM.weaken_scheme (env_post := []) (env := (S₀.onCtx ctx).env) (M := M) hgen hbody
  have hbody'' : TypeOfHM (R₁.onCtx { (S₁.onCtx ctx) with
      env := genScheme (S₁.onCtx ctx).env τ₁ :: (S₁.onCtx ctx).env }) body τ₀ := by
    show TypeOfHM ⟨R₁.onPolyTy (genScheme (S₁.onCtx ctx).env τ₁) :: R₁.onEnv (S₁.onCtx ctx).env,
        (S₁.onCtx ctx).ctors⟩ body τ₀
    rw [show R₁.onEnv (S₁.onCtx ctx).env = (S₀.onCtx ctx).env from congrArg Ctx.env hctxeq]
    exact hbody'
  -- Apply the body IH (specialization is `R₁`).
  obtain ⟨Φ₂, S₂, τ₂, R₂, hinfb, hagb, htyb, hR₂⟩ :=
    ihb hwfBody hbelowBody hR₁ hbody''
  refine ⟨Φ₂, S₁ ++ S₂, τ₂, R₂, .letIn hinfa hinfb, ?_, htyb, hR₂⟩
  intro v hv
  have hbv : Ty.BelowFvars Φ₁ (S₁.onTy (.fvar v)) :=
    Subst.onTy_belowFvars hbelowS₁ (.fvar (by omega))
  calc S₀.onTy (.fvar v)
      = (S₁ ++ R₁).onTy (.fvar v) := haga v hv
    _ = R₁.onTy (S₁.onTy (.fvar v)) := by rw [Subst.onTy_append]
    _ = (S₂ ++ R₂).onTy (S₁.onTy (.fvar v)) := Subst.onTy_congr hagb hbv
    _ = ((S₁ ++ S₂) ++ R₂).onTy (.fvar v) := by
          rw [List.append_assoc, Subst.onTy_append S₁ (S₂ ++ R₂)]

/-- Principality, `letIn` case. -/
theorem Infer.complete_letIn {rhs body : Expr}
    (iha : Infer.CompleteAt rhs) (ihb : Infer.CompleteAt body) :
    Infer.CompleteAt (.letIn rhs body) := by
  intro Φ ctx S₀ τ₀ hwf hbelow hS₀ hty
  cases hty with
  | letIn hMwf hcofin heq hbody =>
    subst heq
    exact Infer.complete_letIn_aux iha ihb hwf hbelow hS₀ hMwf hcofin hbody


/-! ### Principality, assembled -/

/-- Every core expression satisfies the principality property `CompleteAt`,
    assembled from the per-form case lemmas by induction on `Expr.Core`. -/
theorem Infer.completeAt_of_core {e : Expr} (hcore : e.Core) : Infer.CompleteAt e := by
  induction hcore with
  | primLit => exact Infer.complete_prim
  | pair _ _ iha ihb => exact Infer.complete_pair iha ihb
  | lambda _ ih => exact Infer.complete_lambda ih
  | app _ _ ihf iharg => exact Infer.complete_app ihf iharg
  | var => exact Infer.complete_var
  | letIn _ _ iha ihb => exact Infer.complete_letIn iha ihb

/-- **Principality of `Infer`** (Damas–Milner completeness, core fragment): for
    any declarative typing of a core expression `e` under an LC specialization
    `S₀` of a WF, frontier-bounded context, `Infer` succeeds with `(S, τ)` and the
    declarative typing factors through it via an LC residual `R` (`S₀ = R ∘ S`
    below the frontier, `τ₀ = R.onTy τ`). Combined with `Infer.sound`, this is
    full principality: `Infer` computes a most general typing. -/
theorem Infer.complete {Φ : Nat} {ctx : Ctx} {e : Expr} {S₀ : Subst} {τ₀ : Ty}
    (hcore : e.Core) (hwf : CtxWF ctx) (hbelow : CtxBelow Φ ctx)
    (hS₀ : ∀ p ∈ S₀, p.2.IsLC) (hty : TypeOfHM (S₀.onCtx ctx) e τ₀) :
    ∃ Φ' S τ R,
      Infer Φ ctx e Φ' S τ ∧
      (∀ v, v < Φ → S₀.onTy (.fvar v) = (S ++ R).onTy (.fvar v)) ∧
      τ₀ = R.onTy τ ∧
      (∀ p ∈ R, p.2.IsLC) :=
  Infer.completeAt_of_core hcore hwf hbelow hS₀ hty
