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



-- inductive List.Rel
-- def asdfa := List.Forall₂







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




-- @TODO: make a prop here about a Ty being closed, no fvars!
-- and i think then maybe we can insert a thing about how when a new binding's type contains/inserts a new fvar that it always gets generalised away, so nothing can ever stick an fvar in and keep it around for even after it has generalised itself away!
-- so maybe actually the thing that the initial version of the cursor agent wanted is indeed true: that newer additions to the thing are always fvar-closed – relative to the new binding's thing... so that maybe we can indeed avail ourselves of that starting premise? because we can prove that the TypeOfHM relation doesn't add new fvars into the environment? cuz like, there's not even a modified context it returns. so maybe... this was self-farshtendlich? but then you still need a starting premise on the initial thing saying that all the vars in the lower (prepended) env are closed – with relation to the var's binding? and that if you have that starting premise, you can also transport it quite easily through the things. maybe with the caveat that a) tyArgs you create don't also contain... uh wait. don't also contain new fvars? or existing fvars? bc neither of those are true, rite? ok so maybe that... a.1) yes they indeed may contain either existing *or* new fvars, but that any new fvars *will* be guaranteed to be generalised out. nothing new-fvar-shaped makes it out of the current scope! and then a.2) that therefore tyArgs cannot add... ungeneralisable things in? and thus tyArgs won't cause Generalisation discrepancies compared to with or without the binding? and b) lambda params indeed also either create new fvars, but if they do, they will always be generalised out when we close out the lambda typing!
-- ok so with the above in mind, and vaguely understood, i think maybe it makes sense to a) define a locally closed prop – indeed as our erstwhile agent proposed RIP – b) prove that it is maintained for all things, as in that no fvars stick around after closing off? c) in which case, we can easily use that as a starting premise for the subst_lemma about... the pre_env i think? and d) we can easily feed that through to each inductive hypothesis. ok. yes. yes! (i think).



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



-- /-- Replace a type var with some other a type -/
-- abbrev Subst := Nat × Ty


-- mutual

-- def Ty.subst : Subst → Ty → Ty
-- | _, .prim p => .prim p
-- | sub, .pair a b => .pair (a.subst sub) (b.subst sub)
-- | sub, .arrow a b => .arrow (a.subst sub) (b.subst sub)
-- | ⟨n, new⟩, .typeVar dbi => if dbi = n then new else .typeVar dbi
-- | sub, .customTy name tys => .customTy name (TyList.subst sub tys)


-- def TyList.subst (sub : Subst) (list : List Ty) : List Ty :=
--   list.map (Ty.subst sub)

-- end







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

  /-- Beta. -/
  | beta {body v} :
      IsValue v →
      Step (.app (.lambda body) v) (body.subst1 0 v)

  /-- Let reduction (after rhs has been reduced to a value). -/
  | letReduce {v body} :
      IsValue v →
      Step (.letIn v body) (body.subst1 0 v)

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
        | .lambda body => some (body.subst1 0 arg)
        | _ => none
      else do let arg' ← step arg; return .app f arg'
    else do let f' ← step f; return .app f' arg

  | .letIn rhs body =>
    if isValue rhs then some (body.subst1 0 rhs)
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

/-! ### Evaluation -/

-- theorem evaluate_isValue {fuel e v} (h : evaluate fuel e = some v) :
--     isValue v = true := by
--   sorry

/-! ### Soundness & completeness of `step` w.r.t. well-typedness (`TypeOfHM`) -/

-- /-- Preservation: one step of evaluation preserves types. -/
-- theorem step_preserves_typing {ctx : Ctx} {e e' : Expr} {τ : Ty}
--     (h_ty : TypeOfHM ctx e τ)
--     (h_step : step e = some e') :
--     TypeOfHM ctx e' τ := by
--   have h_step_rel := step_sound h_step; clear h_step
--   induction h_step_rel generalizing τ with
--   | beta hval =>
--     cases h_ty with
--     | app h_f h_arg =>
--       cases h_f with
--       | lambda h_closed h_eq h_body =>
--         subst h_eq
--         -- Have:
--         --   h_body : TypeOfHM {ctx with env := mkTrivial argTy :: ctx.env} body τ
--         --   h_arg  : TypeOfHM ctx v argTy
--         -- Need: TypeOfHM ctx (body.subst1 0 v) τ
--         -- This is the substitution lemma at env_post = [].
--         sorry
--   | letReduce hval =>
--     cases h_ty with
--     | letIn h_rhs h_gen h_eq h_body =>
--       subst h_eq
--       -- Have:
--       --   h_body : TypeOfHM {ctx with env := generalisedExprTy :: ctx.env} body τ
--       --   h_rhs  : TypeOfHM ctx v boundExprTy
--       --   h_gen  : Generalise ctx.env boundExprTy generalisedExprTy
--       -- Need: TypeOfHM ctx (body.subst1 0 v) τ
--       -- This is trickier: the binding is polymorphic (generalised), but we
--       -- substitute a monomorphic value. Each use site instantiates the
--       -- polytype, and the value must re-type at each instantiation.
--       sorry
--   | letPairReduce hv1 hv2 =>
--     cases h_ty with
--     | letPairIn h_rhs h_gf h_gs h_eq h_body =>
--       subst h_eq
--       cases h_rhs with
--       | pair h_fst h_snd =>
--         -- Have:
--         --   h_body : TypeOfHM {ctx with env := genSndTy :: genFstTy :: ctx.env} body τ
--         --   h_fst  : TypeOfHM ctx v₁ fstTy
--         --   h_snd  : TypeOfHM ctx v₂ sndTy
--         --   h_gf   : Generalise ctx.env fstTy genFstTy
--         --   h_gs   : Generalise ctx.env sndTy genSndTy
--         -- Need: TypeOfHM ctx (body.substN 0 [v₂, v₁]) τ
--         -- Same challenge as letReduce but with two generalised bindings.
--         sorry
--   | matchReduce hval hctor hfirst =>
--     cases h_ty with
--     | match_ h_scrut h_ne h_brs =>
--       -- Have:
--       --   h_scrut : TypeOfHM ctx scrut (.customTy tyName tyArgs)
--       --   h_brs   : ∀ branch ∈ branches, TypeOfMatchBranch ctx branch tyName tyArgs τ
--       --   hfirst  : FirstMatchingBranch name args.length branches pat body
--       --   hctor   : CtorAppliedTo scrut name args
--       --   hval    : IsValue scrut
--       -- Need: TypeOfHM ctx (body.substN 0 args) τ
--       -- Must extract the matching branch's typing, get types for args from
--       -- the ctor chain + scrutinee typing, then substitute.
--       sorry
--   | pairFst _ ih =>
--     cases h_ty with
--     | pair h_a h_b => exact .pair (ih h_a) h_b
--   | pairSnd hval _ ih =>
--     cases h_ty with
--     | pair h_a h_b => exact .pair h_a (ih h_b)
--   | appFn _ ih =>
--     cases h_ty with
--     | app h_f h_arg => exact .app (ih h_f) h_arg
--   | appArg hval _ ih =>
--     cases h_ty with
--     | app h_f h_arg => exact .app h_f (ih h_arg)
--   | letInRhs _ ih =>
--     cases h_ty with
--     | letIn h_rhs h_gen h_eq h_body => exact .letIn (ih h_rhs) h_gen h_eq h_body
--   | letPairRhs _ ih =>
--     cases h_ty with
--     | letPairIn h_rhs h_gf h_gs h_eq h_body =>
--       exact .letPairIn (ih h_rhs) h_gf h_gs h_eq h_body
--   | matchScrut _ ih =>
--     cases h_ty with
--     | match_ h_scrut h_ne h_brs => exact .match_ (ih h_scrut) h_ne h_brs

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












-- /-- If env doesn't already contain fvars, it won't have any after typing an expr

-- NOTE: alright well this is of course nor true because for lambda params we can insert fvars -/
-- theorem TypeOfHM.preserves_fvars : ctx.env.freeVars = [] → TypeOfHM ctx expr τ → τ.freeVars = [] := by
--   intro hnofv htm
--   induction expr using Expr.rec_strong generalizing τ with
--   | primLit =>
--     cases htm
--     all_goals (simp [Ty.freeVars])
--   | pair a b aih bih =>
--     cases htm
--     simp [Ty.freeVars]
--     tauto
--   | lambda body ih =>
--     cases htm
--     simp [Ty.freeVars]
--     expose_names

--   sorry



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
      quantified — the caller picks it (typically from the typing derivation). -/
  | match_ {tyName : TyName} :
    AllMatchesExhaustive ctors scrut →
    AllBranchBodiesExhaustive ctors branches →
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

-- /-- If a ctor chain is well-typed at `customTy tyName tyArgs`, extract its
--     name, args, ctor entry, and the fact that it's a constructor for `tyName`. -/
-- theorem ctor_chain_info {ctx e tyName tyArgs}
--     (h_chain : IsCtorChain e)
--     (h_ty : TypeOfHM ctx e (.customTy tyName tyArgs)) :
--     ∃ name args, ∃ ctor : Ctor,
--       CtorAppliedTo e name args ∧
--       LookupList.get? ctx.ctors name = some ctor ∧
--       ctor.tyName = tyName ∧
--       args.length = ctor.contents.length := by
--   sorry  -- requires ctor-chain typing inversion

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

-- /-- Progress: a well-typed closed term (with exhaustive matches) is either
--     a value or can take a step. -/
-- theorem progress {ctx : Ctx} {e : Expr} {τ : Ty}
--     (h_ty : TypeOfHM ctx e τ)
--     (h_closed : ctx.env = [])
--     (h_exh : AllMatchesExhaustive ctx.ctors e) :
--     IsValue e ∨ ∃ e', Step e e' := by
--   induction e using Expr.rec_strong generalizing ctx τ with
--   | primLit p => exact .inl (.primLit p)
--   | lambda _ _ => exact .inl (.lambda _)
--   | ctor name => exact .inl (.ctor name)
--   | var n =>
--     cases h_ty with
--     | var h_lookup _ _ => rw [h_closed] at h_lookup; simp at h_lookup
--   | pair a b iha ihb =>
--     cases h_exh with | pair h_exh_a h_exh_b =>
--     cases h_ty with
--     | pair h_a h_b =>
--       rcases iha h_a h_closed h_exh_a with hva | ⟨a', ha⟩
--       · rcases ihb h_b h_closed h_exh_b with hvb | ⟨b', hb⟩
--         · exact .inl (.pair hva hvb)
--         · exact .inr ⟨_, .pairSnd hva hb⟩
--       · exact .inr ⟨_, .pairFst ha⟩
--   | app f arg ihf iharg =>
--     cases h_exh with | app h_exh_f h_exh_arg =>
--     cases h_ty with
--     | app h_f h_arg =>
--       rcases ihf h_f h_closed h_exh_f with hvf | ⟨f', hf⟩
--       · rcases iharg h_arg h_closed h_exh_arg with hva | ⟨arg', harg⟩
--         · rcases TypeOfHM.canonical_arrow h_f hvf with ⟨body, rfl⟩ | hchain
--           · exact .inr ⟨_, .beta hva⟩
--           · exact .inl (.ctorApp hchain hva)
--         · exact .inr ⟨_, .appArg hvf harg⟩
--       · exact .inr ⟨_, .appFn hf⟩
--   | letIn rhs body ihrhs _ =>
--     cases h_exh with | letIn h_exh_rhs _ =>
--     cases h_ty with
--     | letIn h_rhs _ _ _ =>
--       rcases ihrhs h_rhs h_closed h_exh_rhs with hvr | ⟨rhs', hrhs⟩
--       · exact .inr ⟨_, .letReduce hvr⟩
--       · exact .inr ⟨_, .letInRhs hrhs⟩
--   | letPairIn rhs body ihrhs _ =>
--     cases h_exh with | letPairIn h_exh_rhs _ =>
--     cases h_ty with
--     | letPairIn h_rhs _ _ _ _ =>
--       rcases ihrhs h_rhs h_closed h_exh_rhs with hvr | ⟨rhs', hrhs⟩
--       · obtain ⟨v₁, v₂, rfl, hv₁, hv₂⟩ := TypeOfHM.canonical_pair h_rhs hvr
--         exact .inr ⟨_, .letPairReduce hv₁ hv₂⟩
--       · exact .inr ⟨_, .letPairRhs hrhs⟩
--   | match_ scrut branches ihscrut _ =>
--     cases h_exh with | match_ h_exh_scrut _ h_match_exh =>
--     cases h_ty with
--     | match_ h_scrut _ _ =>
--       rcases ihscrut h_scrut h_closed h_exh_scrut with hvs | ⟨scrut', hscrut⟩
--       · have hchain := TypeOfHM.canonical_customTy h_scrut hvs
--         obtain ⟨name, args, ctor, hctor_app, hctor_lookup, _, hlen⟩ :=
--           ctor_chain_info hchain h_scrut
--         -- sorry: ctor.tyName = tyName from exhaustiveness. Holds when
--         -- AllMatchesExhaustive was built with the same tyName as the typing.
--         obtain ⟨pat, body, hmem, hpctor, hparity⟩ := by
--           refine h_match_exh name ctor hctor_lookup ?_
--           expose_names
--           suffices tyName = tyName_1 by
--             subst this
--             exact left
--           subst left

--           sorry

--         obtain ⟨e', hfmb⟩ := findMatchingBranch_of_exists
--           ⟨pat, body, hmem, hpctor, hparity.trans hlen.symm⟩
--         obtain ⟨pat', body', hfirst, _⟩ := findMatchingBranch_to_FirstMatch hfmb
--         exact .inr ⟨_, .matchReduce hvs hctor_app hfirst⟩
--       · exact .inr ⟨_, .matchScrut hscrut⟩

-- /-- Progress for the step function. -/
-- theorem step_progress {ctx : Ctx} {e : Expr} {τ : Ty}
--     (h_ty : TypeOfHM ctx e τ)
--     (h_closed : ctx.env = [])
--     (h_exh : AllMatchesExhaustive ctx.ctors e)
--     (h_not_val : isValue e = false) :
--     ∃ e', step e = some e' := by
--   rcases progress h_ty h_closed h_exh with hv | ⟨e', he⟩
--   · exact absurd (isValue_iff_IsValue.mpr hv) (by simp [h_not_val])
--   · exact ⟨e', step_complete he⟩

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


/-! ### Translation: how this consumes/produces vs. the original `subst_lemma`.

When this is used in `preservation`:

- **Beta** (`(.app (.lambda body) v) → body.subst1 0 v`):
  Apply with `M := PolyTy.mkTrivial paramTy` (paramTy from the lambda rule).
  Discharge `h_v` via `HasScheme.ofTypeOfHM (h_v_typing : TypeOfHM env v paramTy)`.
  Discharge `h_v_value` from the operational hypothesis (red_beta requires
  the argument to be a value).

- **Let-reduce** (`(.letIn t1 t2) → t2.subst1 0 t1`):
  Apply with `M` = the scheme from the `letIn` rule.
  Discharge `h_v` via `HasScheme.fromHasSchemeVars` applied to the cofinite
  premise of the `letIn` rule.
  Discharge `h_v_value` from the `Expr.IsValue boundExpr` premise of the
  `letIn` rule (which we added per Chargueraud's value restriction). -/


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








-- theorem TypeOfHM.subst_lemma {env ctors env_post e τ paramTy v}
--     (h_body : TypeOfHM
--                 { ctors, env := env_post ++ [PolyTy.mkTrivial paramTy] ++ env }
--                 e τ)
--     (h_v : TypeOfHM {ctors,env} v paramTy)
--     (h_paramTy_closed : OnlyContainsBvars [] paramTy)
--     (h_env_post_sub : env_post.freeVars ⊆ env.freeVars) :
--     TypeOfHM { ctors, env := env_post ++ env }
--       (e.substN env_post.length [v]) τ := by
--   induction e using Expr.rec_strong generalizing env env_post τ with
--   | primLit _ =>
--     cases h_body with
--     | primLitUnit => exact .primLitUnit
--     | primLitInt  => exact .primLitInt
--     | primLitNat  => exact .primLitNat
--     | primLitBool => exact .primLitBool
--     | primLitStr  => exact .primLitStr
--   | ctor _ =>
--     cases h_body with
--     | ctor h_lookup h_tyArgs_closed h_inst =>
--       exact .ctor h_lookup h_tyArgs_closed h_inst
--   | pair _ _ ih_a ih_b =>
--     cases h_body with
--     | pair h_a h_b =>
--       exact .pair (ih_a h_a h_v h_env_post_sub) (ih_b h_b h_v h_env_post_sub)
--   | app _ _ ih_f ih_in =>
--     cases h_body with
--     | app h_f h_in =>
--       exact .app (ih_f h_f h_v h_env_post_sub) (ih_in h_in h_v h_env_post_sub)
--   | lambda body ih =>
--     cases h_body with
--     | lambda h_paramTy_lam_closed h_eq h_body_lam =>
--       subst h_eq
--       -- bodyCtx.env was set to `paramTy_lam :: (env_post ++ [paramTy] ++ ctx.env)`,
--       -- which is definitionally `(paramTy_lam :: env_post) ++ [paramTy] ++ ctx.env`.
--       -- We recurse with env_post' := paramTy_lam :: env_post; substitution position
--       -- becomes (env_post.length + 1), which is exactly what `Expr.substN` produces
--       -- for `.lambda body`.
--       exact .lambda h_paramTy_lam_closed rfl
--         (ih (env_post := PolyTy.mkTrivial _ :: env_post) h_body_lam h_v
--           (sorry /- need: (PolyTy.mkTrivial paramTy_lam :: env_post).freeVars ⊆ env.freeVars -/))
--   | letPairIn _ body ih_pe ih_body =>
--     cases h_body with
--     | letPairIn h_pe h_genFst h_genSnd h_eq h_body_inner =>
--       expose_names
--       subst h_eq
--       -- IH on body with env_post' := genSndTy :: genFstTy :: env_post (matching
--       -- the typing rule's ordering).
--       have h_body_subst :=
--         ih_body (env_post := genSndTy :: genFstTy :: env_post)
--           h_body_inner h_v
--           (sorry /- need: (genSndTy :: genFstTy :: env_post).freeVars ⊆ env.freeVars -/)
--       -- With the relaxed Generalise (`→` instead of `↔`), the same generalisation
--       -- transfers from the bigger env to the smaller env: ftvs need only be
--       -- eligible (i.e. ⊆ ¬env.freeVars), and removing paramTy can only ADD
--       -- eligibility, so the same h_gen still works.
--       have h_subset : (env_post ++ env).freeVars ⊆
--           (env_post ++ [PolyTy.mkTrivial paramTy] ++ env).freeVars :=
--         Env.freeVars_subset_insert_middle env_post env _
--       have h_genFst_new : Generalise (env_post ++ env) fstTy genFstTy := by
--         cases h_genFst with
--         | mk h_nodup h_eligible h_pt =>
--           refine .mk h_nodup ?_ h_pt
--           exact fun tv h_mem =>
--             ⟨(h_eligible tv h_mem).1,
--              fun h_in => (h_eligible tv h_mem).2 (h_subset h_in)⟩
--       have h_genSnd_new : Generalise (env_post ++ env) sndTy genSndTy := by
--         cases h_genSnd with
--         | mk h_nodup h_eligible h_pt =>
--           refine .mk h_nodup ?_ h_pt
--           exact fun tv h_mem =>
--             ⟨(h_eligible tv h_mem).1,
--              fun h_in => (h_eligible tv h_mem).2 (h_subset h_in)⟩
--       exact .letPairIn (ih_pe h_pe h_v h_env_post_sub)
--         h_genFst_new h_genSnd_new rfl h_body_subst
--   | match_ scrutinee branches ih_scrut ih_branches =>
--     cases h_body with
--     | match_ h_scrut h_branches_nonempty h_brs =>
--       have h_subst_nonempty :
--           (BranchList.substN env_post.length [v] branches) ≠ [] := by
--         intro h_eq
--         cases branches with
--         | nil => exact h_branches_nonempty rfl
--         | cons _ _ => simp [BranchList.substN] at h_eq
--       refine .match_ (ih_scrut h_scrut h_v h_env_post_sub) h_subst_nonempty ?_
--       clear ih_scrut h_scrut h_branches_nonempty h_subst_nonempty
--       -- Goal: ∀ branch ∈ BranchList.substN env_post.length [v] branches,
--       --   TypeOfMatchBranch { env := env_post ++ ctx.env, ... } branch ...
--       revert h_brs ih_branches
--       induction branches with
--       | nil =>
--         intros _ _ branch h_mem
--         simp only [BranchList.substN] at h_mem
--         exact absurd h_mem (List.not_mem_nil)
--       | cons hd tl ih_tl =>
--         intro ihbs h_brs
--         obtain ⟨pat, body⟩ := hd
--         intro branch h_mem
--         simp only [BranchList.substN, List.mem_cons] at h_mem
--         cases h_mem with
--         | inl h_eq =>
--           subst h_eq
--           -- branch = (pat, body.substN (env_post.length + pat.contents) [v])
--           have h_branch_orig := h_brs (pat, body) List.mem_cons_self
--           cases h_branch_orig with
--           | mk h_lookup h_tyName h_paramCount h_contents h_inst h_pb h_ctx h_body_orig =>
--             subst h_ctx
--             subst h_pb
--             expose_names
--             -- Apply ih_branches to body with env_post' := patternBindings ++ env_post.
--             have h_body_subst :=
--               ihbs pat body List.mem_cons_self
--                 (env_post := List.map PolyTy.mkTrivial instContents ++ env_post)
--                 (by simpa [List.append_assoc] using h_body_orig)
--                 h_v
--                 (sorry /- need: (instContents.map PolyTy.mkTrivial ++ env_post).freeVars ⊆ env.freeVars -/)
--             refine .mk h_lookup h_tyName h_paramCount h_contents h_inst rfl rfl ?_
--             -- Goal: TypeOfHM { env := List.map ... instContents ++ (env_post ++ ctx.env), ... }
--             --         (body.substN (env_post.length + pat.contents) [v]) τ
--             have h_len :
--                 (List.map PolyTy.mkTrivial instContents ++ env_post).length
--                   = env_post.length + pat.contents := by
--               simp only [List.length_append, List.length_map,
--                          ← h_inst.length_eq, ← h_contents]
--               omega
--             simpa [List.append_assoc, h_len] using h_body_subst
--         | inr h_mem' =>
--           exact ih_tl
--             (fun pat' e' hmem => ihbs pat' e' (List.mem_cons_of_mem _ hmem))
--             (fun b hmem => h_brs b (List.mem_cons_of_mem _ hmem))
--             _ h_mem'
--   | letIn _ body ih_be ih_body =>
--     cases h_body with
--     | letIn h_be h_gen h_eq h_body_inner =>
--       expose_names
--       subst h_eq
--       have h_body_subst :=
--         ih_body (env_post := generalisedExprTy :: env_post)
--           h_body_inner h_v
--           (sorry /- need: (generalisedExprTy :: env_post).freeVars ⊆ env.freeVars -/)
--       -- Reuse h_gen on the smaller env (relaxed Generalise: ftvs only need
--       -- to be a subset of eligibles, and eligibility only grows when env shrinks).
--       have h_subset : (env_post ++ env).freeVars ⊆
--           (env_post ++ [PolyTy.mkTrivial paramTy] ++ env).freeVars :=
--         Env.freeVars_subset_insert_middle env_post env _
--       have h_gen_new : Generalise (env_post ++ env) boundExprTy generalisedExprTy := by
--         cases h_gen with
--         | mk h_nodup h_eligible h_pt =>
--           refine .mk h_nodup ?_ h_pt
--           exact fun tv h_mem =>
--             ⟨(h_eligible tv h_mem).1,
--              fun h_in => (h_eligible tv h_mem).2 (h_subset h_in)⟩
--       exact .letIn (ih_be h_be h_v h_env_post_sub) h_gen_new rfl h_body_subst
--   | var i =>
--     cases h_body with
--     | var h_lookup h_tyArgs_closed h_inst =>
--       rcases lt_trichotomy i env_post.length with h_lt | h_eq | h_gt
--       · -- Sub-case (1): i < env_post.length. substN keeps `.var i`.
--         have h_subst : (Expr.var i).substN env_post.length [v] = .var i := by
--           simp [Expr.substN, h_lt]
--         rw [h_subst]
--         refine .var ?_ h_tyArgs_closed h_inst
--         -- Lookup at i is in env_post in both envs since i < env_post.length.
--         rw [List.getElem?_append_left h_lt]
--         rw [List.append_assoc, List.getElem?_append_left h_lt] at h_lookup
--         exact h_lookup
--       · -- Sub-case (2): i = env_post.length. substN returns `v.shiftFrom 0 k`.
--         subst h_eq
--         -- substN (.var env_post.length) env_post.length [v] = v.shiftFrom 0 env_post.length
--         have h_subst :
--             (Expr.var env_post.length).substN env_post.length [v]
--               = v.shiftFrom 0 env_post.length := by
--           simp [Expr.substN]
--         rw [h_subst]
--         -- Extract polyTy = PolyTy.mkTrivial paramTy from h_lookup.
--         rw [List.append_assoc, List.getElem?_append_right (Nat.le_refl _),
--             Nat.sub_self] at h_lookup
--         simp at h_lookup
--         -- h_lookup : polyTy = PolyTy.mkTrivial paramTy (after simp)
--         subst h_lookup
--         -- h_inst : InstantiatesBy tyArgs (PolyTy.mkTrivial paramTy).body τ
--         --        = InstantiatesBy tyArgs paramTy τ (definitionally, since
--         --        (PolyTy.mkTrivial paramTy).body = paramTy by `rfl`).
--         -- By closedness, τ = paramTy.
--         have h_τ_eq := InstantiatesBy.eq_of_closed h_paramTy_closed h_inst
--         subst h_τ_eq
--         exact weaken_env' h_v h_env_post_sub
--       · -- Sub-case (3): i > env_post.length. substN returns `.var (i - 1)`.
--         have h_not_lt : ¬ (i < env_post.length) := by omega
--         have h_not_lt' : ¬ (i - env_post.length < (1 : Nat)) := by omega
--         have h_subst : (Expr.var i).substN env_post.length [v] = .var (i - 1) := by
--           simp [Expr.substN, h_not_lt, h_not_lt']
--         rw [h_subst]
--         refine .var ?_ h_tyArgs_closed h_inst
--         -- Lookup at i in (env_post ++ [paramTy] ++ ctx.env) falls in ctx.env at
--         -- offset (i - env_post.length - 1). Lookup at (i - 1) in (env_post ++ ctx.env)
--         -- falls in ctx.env at offset (i - 1 - env_post.length). Equal by arith.
--         have h_le_i : env_post.length ≤ i := by omega
--         rw [List.getElem?_append_right (by omega : env_post.length ≤ i - 1)]
--         rw [List.append_assoc, List.getElem?_append_right h_le_i] at h_lookup
--         rw [show ([PolyTy.mkTrivial paramTy] ++ env) = (PolyTy.mkTrivial paramTy
--             :: env) from rfl] at h_lookup
--         rw [show (i - env_post.length) = (i - env_post.length - 1) + 1 from by omega]
--             at h_lookup
--         simp only [List.getElem?_cons_succ] at h_lookup
--         rw [show (i - 1 - env_post.length) = (i - env_post.length - 1) from by omega]
--         exact h_lookup

-- theorem TypeOfHM.preservation {ctx e τ e'}
--     (h_ty : TypeOfHM ctx e τ)
--     (h_step : SmallStep.Step e e') :
--     TypeOfHM ctx e' τ := by
--   sorry




/-- Either a conc or unspec. Either the fvar is constrained or not. -/
inductive TyMaybe where
  | unspec
  | conc (ty : Ty)


/-- The unification var context. Each fvar references an item in this context -/
abbrev FvarCtx := List TyMaybe


-- /-- Whether the type-ness is imposed by the value itself or the environment pushes a type onto the value -/
-- inductive TypeDir where
--   /-- The surrounding area pushes a certain type onto the value. This is the check direction. -/
--   | check
--   /-- The value itself imposes its own type. This is the infer direction. -/
--   | infer

-- inductive BiTyping : Ctx → TypeDir → Expr → Ty → Prop
--   | primUnit : BiTyping ctx .infer (.primLit .unit) (.prim .unit)
--   | primInt : BiTyping ctx .infer (.primLit (.int _)) (.prim .int)
--   | primNat : BiTyping ctx .infer (.primLit (.nat _)) (.prim .nat)
--   | primBool : BiTyping ctx .infer (.primLit (.bool _)) (.prim .bool)
--   | primStr : BiTyping ctx .infer (.primLit (.str _)) (.prim .str)

--   | pair :
--     BiTyping ctx .infer fst fstTy →
--     BiTyping ctx .infer snd sndTy →
--     BiTyping ctx .infer (.pair fst snd) (.pair fstTy sndTy)

--   | lambda :
--     bodyCtx = { ctx with env := PolyTy.mkTrivial argTy :: ctx.env } →
--     BiTyping bodyCtx .infer body bodyTy →
--     BiTyping ctx .infer (.lambda body) (.arrow argTy bodyTy)

--   | app :
--     BiTyping ctx .infer f (.arrow argTy returnTy) →
--     BiTyping ctx .check arg argTy →
--     BiTyping ctx .infer (.app f arg) returnTy

--   | var {ctx : Ctx} {polyTy : PolyTy} :
--     ctx.env[dbi]? = some polyTy →
--     InstantiatesBy tyArgs polyTy.body ty →
--     BiTyping ctx .infer (.var dbi) ty

--   | ctor :
--     ctx.ctors.get? ctorName = some polyTy →
--     InstantiatesBy tyArgs polyTy.toTy.body ty →
--     BiTyping ctx .infer (.ctor ctorName) ty

--   | letIn :
--     BiTyping ctx .infer binding bindingTy →
--     Generalise ctx.env bindingTy generalisedTy →
--     bodyCtx = { ctx with env := generalisedTy :: ctx.env } →
--     BiTyping ctx .infer body bodyTy →
--     BiTyping ctx .infer (.letIn binding body) bodyTy
