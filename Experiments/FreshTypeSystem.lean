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
  closed : ∀ ty ∈ contents, ContainsBvarsUpTo paramCount ty

/-- Which type constructors exist -/
abbrev CtorEnv := LookupList CtorName Ctor





/-- Which value bindings exist. Uses de Bruijn levels – i.e. new bindings appended to the end -/
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
  contents : Nat -- this is basically just a binding range. i.e. if 2 this means we've bound 2 new "names" to the context


-- inductive Expr
--   | primLit (prim : PrimLitExpr)
--   | pair (a b : Expr)
--   -- | lambda (param : ValName) (paramTy : Ty) (body : Expr)
--   | lambda (param : ValName) (body : Expr)
--   | app (f input : Expr)
--   | letIn (name : ValName) (bindingExpr body : Expr)
--   /-- Destructuring a pair `let (a,b) = pairExpr in body` -/
--   | letPairIn (fstName sndName : ValName) (pairExpr body : Expr)
--   | var (deBruijnLevel : Nat)
--   /-- A type constructor -/
--   | ctor (name : CtorName)
--   | match_ (scrutinee : Expr) (branches : List (MatchPattern × Expr))


inductive Expr
  | primLit (prim : PrimLitExpr)
  | pair (a b : Expr)
  | lambda (body : Expr)
  | app (f input : Expr)
  | letIn (bindingExpr body : Expr)
  /-- Destructuring a pair `let (a,b) = pairExpr in body` -/
  | letPairIn (pairExpr body : Expr)
  | var (deBruijnLevel : Nat)
  /-- A type constructor -/
  | ctor (name : CtorName)
  | match_ (scrutinee : Expr) (branches : List (MatchPattern × Expr))






-- def Ctor.toTy (ctorEnv : CtorEnv) (ctor : CtorName) : Option PolyTy :=
--   match ctorEnv.get? ctor with
--   | none => none
--   | some thing =>
--     .customTy thing.tyName thing.contents
--     |> some


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
    .customTy ctor.tyName (Ty.bvarRange ctor.paramCount)

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




/-- Under env, ty generalises to this polyty -/
inductive Generalise : Env → Ty → PolyTy → Prop
  | mk {env : Env} {ty : Ty} {ftvs : List Nat} :
    ftvs.Nodup →
    (∀ tv, tv ∈ ftvs → tv ∈ ty.freeVars ∧ tv ∉ env.freeVars) →
    polyTy = ⟨ftvs.length, ty.closeOver ftvs⟩ →
    Generalise env ty polyTy


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

Cannot be produced for a `bvar` whose index is out of range of `tyArgs`. Thus if tyArgs doesn't contain any `bvar`s, neither does the output. -/
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



mutual

/-- Syntax-directed declarative typing relation -/
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

  /-- Under de Bruijn *indices*, new binders are prepended to env: the lambda's
      param sits at index 0 (innermost). -/
  | lambda :
    ContainsBvarsUpTo 0 paramTy →
    bodyCtx = { ctx with env := PolyTy.mkTrivial paramTy :: ctx.env } →
    TypeOfHM bodyCtx body bodyTy →
    TypeOfHM ctx (.lambda body) (.arrow paramTy bodyTy)

  | app :
    TypeOfHM ctx f (.arrow argTy retTy) →
    TypeOfHM ctx input argTy →
    TypeOfHM ctx (.app f input) retTy

  | letIn :
    TypeOfHM ctx boundExpr boundExprTy →
    Generalise ctx.env boundExprTy generalisedExprTy →
    bodyCtx = { ctx with env := generalisedExprTy :: ctx.env } →
    TypeOfHM bodyCtx body bodyTy →
    TypeOfHM ctx (.letIn boundExpr body) bodyTy

  | letPairIn :
    TypeOfHM ctx boundExpr (.pair fstTy sndTy) →
    Generalise ctx.env fstTy genFstTy →
    Generalise ctx.env sndTy genSndTy →
    bodyCtx =
      { ctx with
        env := genSndTy :: genFstTy :: ctx.env } →
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
    -- We need branches to be non-empty so that we can ensure `resultTy` doesn't contain arbitrary `.bvar`s. For that to be the case, `τ` must be a real type coming from a real branch, not an arbitrary one
    branches ≠ [] →
    (∀ branch ∈ branches, TypeOfMatchBranch ctx branch tyName tyArgs resultTy) →
    TypeOfHM ctx (.match_ scrutinee branches) resultTy


/-- The match pattern under ctx has type ty and returns an expr of type ty -/
inductive TypeOfMatchBranch :
  (ctx : Ctx) → (MatchPattern × Expr) → (tyName : TyName) → (tyArgs : List Ty) → (resultTy : Ty) → Prop
  | mk {ctor : Ctor} {ctx : Ctx} {pattern : MatchPattern} :
    LookupList.get? ctx.ctors pattern.ctor = some ctor →
    ctor.tyName = tyName →
    ctor.paramCount = tyArgs.length →
    pattern.contents = ctor.contents.length →

    -- instantiates the ctor polytype (assigns fvars to its bvars)
    List.Forall₂ (InstantiatesBy tyArgs) ctor.contents instContents →

    -- zips together the names of the pattern match vars to their corresponding (instantiated) types in the constructor's content slots
    -- btw we convert them to polytypes but only because that's what the env contains. none of them actually have any type vars. because that would require separate slots to be individually polymorphic, which is not allowed under rank-1 polymorphism.
    patternBindings = instContents.map PolyTy.mkTrivial →

    -- Prepend (indices semantics): the first pattern var sits at index 0,
    -- matching `body.substN 0 args` in `matchReduce`.
    bodyCtx = {ctx with env := patternBindings ++ ctx.env } →

    TypeOfHM bodyCtx bodyExpr resultTy →
    TypeOfMatchBranch ctx (pattern, bodyExpr) tyName tyArgs resultTy

end




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

  /-- Match reduction. The scrutinee must be a saturated ctor chain whose
      ctor name matches some branch's pattern, with the right arity. -/
  | matchReduce {scrut branches name args pat body} :
      CtorAppliedTo scrut name args →
      (pat, body) ∈ branches →
      pat.ctor = name →
      pat.contents = args.length →
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


/-- Every well-typed expression is well-scoped under its context's env length.
    This is the structural invariant: the lambda/let/letPair/match rules
    correctly extend the env by 1, 1, 2, or `pat.contents` entries respectively.

    Proof strategy: induct on the syntactic structure of `e` via `Expr.rec_strong`,
    generalising over both `ctx` and `τ` (binding-extending constructors type
    their bodies under an extended context, so the IH must work for any `ctx`).
    For each case, invert the typing derivation and apply the IH(s). The
    `match_` case requires an inner induction over the branches list. -/
theorem TypeOfHM.well_scoped {ctx e τ} :
    TypeOfHM ctx e τ → Expr.WellScopedUnder ctx.env.length e := by
  induction e using Expr.rec_strong generalizing ctx τ with
  | primLit p =>
    intro _
    exact .primLit
  | pair a b aih bih =>
    intro h
    cases h with
    | pair ha hb => exact .pair (aih ha) (bih hb)
  | lambda body ih =>
    intro h
    cases h with
    | lambda _ h_eq h_body =>
      subst h_eq
      exact .lambda (by simpa using ih h_body)
  | app f input ihf ihi =>
    intro h
    cases h with
    | app hf hi => exact .app (ihf hf) (ihi hi)
  | letIn be body ihbe ihb =>
    intro h
    cases h with
    | letIn h_be _ h_eq h_body =>
      subst h_eq
      exact .letIn (ihbe h_be) (by simpa using ihb h_body)
  | letPairIn pe body ihpe ihb =>
    intro h
    cases h with
    | letPairIn h_pe _ _ h_eq h_body =>
      subst h_eq
      exact .letPairIn (ihpe h_pe) (by simpa using ihb h_body)
  | var n =>
    intro h
    cases h with
    | var h_get _ =>
      exact .var (List.getElem?_eq_some_iff.mp h_get).fst
  | ctor nm =>
    intro _
    exact .ctor
  | match_ scrutinee branches ihs ihbs =>
    intro h
    cases h with
    | match_ h_scrut hnil h_brs =>
      refine .match_ (ihs h_scrut) ?_
      clear ihs h_scrut
      revert h_brs ihbs
      induction branches with
      | nil => contradiction
      | cons hd tl ih_tl =>
        intro ihbs h_brs
        obtain ⟨pat, body⟩ := hd
        have h_branch := h_brs (pat, body) List.mem_cons_self
        cases h_branch with
        | mk h_lookup h_tyName h_paramCount h_contents h_inst h_pb h_ctx h_body =>
          subst h_ctx
          subst h_pb
          have h_body_ws := ihbs pat body List.mem_cons_self h_body
          simp only [List.length_append, List.length_map,
                     ← h_inst.length_eq, ← h_contents] at h_body_ws
          refine .cons (by rw [Nat.add_comm]; exact h_body_ws) ?_
          rcases eq_or_ne tl [] with rfl | htl_ne
          · exact .nil
          · exact ih_tl htl_ne
              (fun pat' e' hmem => ihbs pat' e' (List.mem_cons_of_mem _ hmem))
              (fun branch hmem => h_brs branch (List.mem_cons_of_mem _ hmem))





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



/-- Generalisation doesn't add more bvars than were in the type to begin with -/
theorem Generalise.preserves_bvars : ContainsBvarsUpTo 0 boundExprTy → Generalise env boundExprTy generalisedExprTy → ContainsBvarsUpTo generalisedExprTy.paramCount generalisedExprTy.body := by
  intro prem hgen
  cases hgen
  expose_names
  rw [h_2]
  simp
  clear h_2
  exact Ty.closeOver_preserves_bvars prem (vars:=ftvs)



/-- The typing output doesn't contain any bvars! Assuming that the env polytypes are all appropriately bound -/
theorem TypeOfHM.preserves_bvars {ctx : Ctx} : (∀ pt ∈ ctx.env, ContainsBvarsUpTo pt.paramCount pt.body) → TypeOfHM ctx expr τ → ContainsBvarsUpTo 0 τ := by
  induction expr using Expr.rec_strong generalizing τ ctx with
  | primLit =>
    intro _ htm
    cases htm
    all_goals constructor
  | pair a b aih bih =>
    intro _ htm
    cases htm
    expose_names
    refine .pair ?_ ?_
    tauto
    tauto
  | lambda body ih =>
    intro prem htm
    cases htm
    refine .arrow ?_ ?_
    · tauto
    · expose_names
      apply ih (ctx := {ctx with env := PolyTy.mkTrivial paramTy :: ctx.env})
      · simp
        tauto
      · rw [← h_1]
        exact h_2
  | app f input fih inputih =>
    intro prem htm
    cases htm
    expose_names
    cases fih prem h_1
    trivial
  | letIn expr body eih bodyih =>
    intro prem htm
    cases htm
    expose_names
    have := eih prem h_2
    have := h.preserves_bvars this
    rw [h_1] at h_3
    have : ∀ pt ∈ generalisedExprTy :: ctx.env, ContainsBvarsUpTo pt.paramCount pt.body := by
        grind
    exact bodyih this h_3
  | letPairIn pairExpr body pairexprih bodyih =>
    intro prem htm
    cases htm
    expose_names
    have := pairexprih prem h_3
    cases this
    expose_names
    have hgenfst := h.preserves_bvars h_5
    have hgensnd := h_1.preserves_bvars h_6
    rw [h_2] at h_4
    have : ∀ pt ∈ genSndTy :: genFstTy :: ctx.env, ContainsBvarsUpTo pt.paramCount pt.body := by
      grind
    have := bodyih this h_4
    exact this
  | var i =>
    intro prem htm
    cases htm
    expose_names
    exact h_2.preserves_bvars h
  | ctor nm =>
    intro prem htm
    cases htm
    expose_names
    exact h_2.preserves_bvars h
  | match_ scrut branches ihscrut branchih =>
    intro prem htm
    cases htm
    expose_names
    replace ihscrut := ihscrut prem h
    cases ihscrut
    cases branches with
    | nil => contradiction
    | cons branch branches =>
      have := h_2 branch (by simp)
      cases this
      expose_names
      refine branchih pattern bodyExpr (by simp) ?_ h_11
      rw [h_7]
      simp
      intro pt ptin
      rcases ptin with ptin|ptin
      · rw [h_5] at ptin
        obtain ⟨ty, hty_mem, hpt_eq⟩ := List.mem_map.mp ptin
        subst hpt_eq
        simp [PolyTy.mkTrivial]
        obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hty_mem
        have hlen := h_10.length_eq
        have := List.Forall₂.get h_10 (by omega : i < ctor.contents.length) hi
        exact InstantiatesBy.preserves_bvars h_3 this
      · exact prem pt ptin














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
private theorem Env.freeVars_subset_insert_closed_middle
    {l₁ l₂ l₃ : Env} (h_l₂ : l₂.freeVars = []) :
    (l₁ ++ l₂ ++ l₃).freeVars ⊆ (l₁ ++ l₃).freeVars := by
  intro x hx
  rw [Env.mem_freeVars_iff] at hx ⊢
  obtain ⟨pt, hpt_mem, hpt_x⟩ := hx
  simp only [List.mem_append] at hpt_mem
  rcases hpt_mem with (hpre | hmid) | hpost
  · exact ⟨pt, by simp only [List.mem_append]; tauto, hpt_x⟩
  · exfalso
    have h_in_l₂ : x ∈ l₂.freeVars := by
      rw [Env.mem_freeVars_iff]; exact ⟨pt, hmid, hpt_x⟩
    rw [h_l₂] at h_in_l₂
    exact absurd h_in_l₂ List.not_mem_nil
  · exact ⟨pt, by simp only [List.mem_append]; tauto, hpt_x⟩


/-- Weakening in the middle: inserting `env_extra` between `env_pre` and
    `env_post` (and shifting the expression's free vars to skip over the
    inserted bindings) preserves typing.

    Requires `env_extra.freeVars = []` (env_extra introduces no free type
    variables): otherwise the `letIn`/`letPairIn` cases would face a
    `Generalise`-direction problem (the inserted bindings could intersect
    with the let-bound polytype's eligible vars, requiring a less polymorphic
    polytype that body might not type under).

    Proof strategy: induct on the syntactic structure of `e` via `Expr.rec_strong`,
    generalising over `env_pre`, `env_post`, `env_extra`, and `τ`. The
    `env_pre ++ env_post` split is what makes the induction go through: binders
    extend `env_pre` when descending into bodies (e.g. lambda extends `env_pre`
    by `[paramTy_lam]`). The threshold of `shiftFrom` tracks `env_pre.length`. -/
theorem TypeOfHM.weaken_env
    {ctors} {env_pre env_post env_extra : Env} {e : Expr} {τ : Ty}
    (h : TypeOfHM { ctors, env := env_pre ++ env_post } e τ)
    (h_env_extra_closed : env_extra.freeVars = []) :
    TypeOfHM { ctors, env := env_pre ++ env_extra ++ env_post }
      (e.shiftFrom env_pre.length env_extra.length) τ := by
  induction e using Expr.rec_strong generalizing env_pre env_post env_extra τ with
  | primLit _ =>
    cases h with
    | primLitUnit => exact .primLitUnit
    | primLitInt  => exact .primLitInt
    | primLitNat  => exact .primLitNat
    | primLitBool => exact .primLitBool
    | primLitStr  => exact .primLitStr
  | ctor _ =>
    cases h with
    | ctor h_lookup h_inst => exact .ctor h_lookup h_inst
  | pair _ _ ih_a ih_b =>
    cases h with
    | pair h_a h_b =>
      exact .pair (ih_a h_a h_env_extra_closed) (ih_b h_b h_env_extra_closed)
  | app _ _ ih_f ih_in =>
    cases h with
    | app h_f h_in =>
      exact .app (ih_f h_f h_env_extra_closed) (ih_in h_in h_env_extra_closed)
  | var i =>
    cases h with
    | var h_lookup h_inst =>
      simp only [Expr.shiftFrom]
      by_cases h_lt : i < env_pre.length
      · rw [if_pos h_lt]
        refine .var ?_ h_inst
        show (env_pre ++ env_extra ++ env_post)[i]? = _
        rw [List.getElem?_append_left
              (by simp only [List.length_append]; omega :
                  i < (env_pre ++ env_extra).length)]
        rw [List.getElem?_append_left h_lt]
        have h_lookup' : (env_pre ++ env_post)[i]? = _ := h_lookup
        rw [List.getElem?_append_left h_lt] at h_lookup'
        exact h_lookup'
      · push_neg at h_lt
        rw [if_neg (Nat.not_lt.mpr h_lt)]
        refine .var ?_ h_inst
        show (env_pre ++ env_extra ++ env_post)[i + env_extra.length]? = _
        have h_left : (env_pre ++ env_extra).length ≤ i + env_extra.length := by
          simp only [List.length_append]; omega
        rw [List.getElem?_append_right h_left]
        have h_eq_idx :
            i + env_extra.length - (env_pre ++ env_extra).length
            = i - env_pre.length := by
          simp only [List.length_append]; omega
        rw [h_eq_idx]
        have h_lookup' : (env_pre ++ env_post)[i]? = _ := h_lookup
        rw [List.getElem?_append_right h_lt] at h_lookup'
        exact h_lookup'
  | lambda body ih =>
    cases h with
    | lambda h_eq h_body_lam =>
      subst h_eq
      simp only [Expr.shiftFrom]
      refine .lambda rfl ?_
      exact ih (env_pre := PolyTy.mkTrivial _ :: env_pre)
        (env_extra := env_extra) h_body_lam h_env_extra_closed
  | letIn _ body ih_be ih_body =>
    cases h with
    | letIn h_be h_gen h_eq h_body_inner =>
      expose_names
      subst h_eq
      simp only [Expr.shiftFrom]
      -- Reuse h_gen on the bigger env: with env_extra.freeVars = [], inserting
      -- env_extra adds no freevars, so the original ftvs are still eligible.
      have h_subset :
          (env_pre ++ env_extra ++ env_post).freeVars ⊆
          (env_pre ++ env_post).freeVars :=
        Env.freeVars_subset_insert_closed_middle h_env_extra_closed
      have h_gen_new :
          Generalise (env_pre ++ env_extra ++ env_post) boundExprTy
            generalisedExprTy := by
        cases h_gen with
        | mk h_nodup h_eligible h_pt =>
          refine .mk h_nodup ?_ h_pt
          exact fun tv h_mem =>
            ⟨(h_eligible tv h_mem).1,
             fun h_in => (h_eligible tv h_mem).2 (h_subset h_in)⟩
      refine .letIn (ih_be h_be h_env_extra_closed) h_gen_new rfl ?_
      exact ih_body (env_pre := generalisedExprTy :: env_pre)
        h_body_inner h_env_extra_closed
  | letPairIn _ body ih_pe ih_body =>
    cases h with
    | letPairIn h_pe h_genFst h_genSnd h_eq h_body_inner =>
      expose_names
      subst h_eq
      simp only [Expr.shiftFrom]
      have h_subset :
          (env_pre ++ env_extra ++ env_post).freeVars ⊆
          (env_pre ++ env_post).freeVars :=
        Env.freeVars_subset_insert_closed_middle h_env_extra_closed
      have h_genFst_new :
          Generalise (env_pre ++ env_extra ++ env_post) fstTy genFstTy := by
        cases h_genFst with
        | mk h_nodup h_eligible h_pt =>
          refine .mk h_nodup ?_ h_pt
          exact fun tv h_mem =>
            ⟨(h_eligible tv h_mem).1,
             fun h_in => (h_eligible tv h_mem).2 (h_subset h_in)⟩
      have h_genSnd_new :
          Generalise (env_pre ++ env_extra ++ env_post) sndTy genSndTy := by
        cases h_genSnd with
        | mk h_nodup h_eligible h_pt =>
          refine .mk h_nodup ?_ h_pt
          exact fun tv h_mem =>
            ⟨(h_eligible tv h_mem).1,
             fun h_in => (h_eligible tv h_mem).2 (h_subset h_in)⟩
      refine .letPairIn (ih_pe h_pe h_env_extra_closed) h_genFst_new h_genSnd_new rfl ?_
      exact ih_body (env_pre := genSndTy :: genFstTy :: env_pre)
        h_body_inner h_env_extra_closed
  | match_ scrutinee branches ihs ihbs =>
    cases h with
    | match_ h_scrut h_brs =>
      simp only [Expr.shiftFrom]
      refine .match_ (ihs h_scrut h_env_extra_closed) ?_
      clear ihs h_scrut
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
            -- Reassociate h_body's env so we can apply IH with
            -- env_pre' := instContents.map PolyTy.mkTrivial ++ env_pre.
            rw [show (instContents.map PolyTy.mkTrivial ++ (env_pre ++ env_post))
                  = (instContents.map PolyTy.mkTrivial ++ env_pre) ++ env_post
                  from (List.append_assoc _ _ _).symm] at h_body
            have ih_body :=
              ihbs pat body List.mem_cons_self
                (env_pre := instContents.map PolyTy.mkTrivial ++ env_pre)
                (env_extra := env_extra)
                h_body h_env_extra_closed
            -- Normalise ih_body's threshold: it has length of
            -- `instContents.map ... ++ env_pre`, we want `env_pre.length + pat.contents`.
            simp only [List.length_append, List.length_map] at ih_body
            rw [← h_inst.length_eq, ← h_contents] at ih_body
            rw [show pat.contents + env_pre.length = env_pre.length + pat.contents
                  from Nat.add_comm _ _] at ih_body
            refine TypeOfMatchBranch.mk h_lookup h_tyName h_paramCount h_contents
              h_inst rfl rfl ?_
            -- Reassociate ih_body's env to match goal's bodyCtx.
            rw [List.append_assoc, List.append_assoc] at ih_body
            rw [show env_pre ++ env_extra ++ env_post = env_pre ++ (env_extra ++ env_post)
                  from List.append_assoc _ _ _]
            exact ih_body
        | inr h_mem' =>
          exact ih_tl
            (fun pat' e' hmem => ihbs pat' e' (List.mem_cons_of_mem _ hmem))
            (fun branch hmem => h_brs branch (List.mem_cons_of_mem _ hmem))
            branch h_mem'




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
    {tyArgs : List Ty} {name : TyName} {args tys : List Ty} {τ : Ty}
    (h : InstantiatesBy tyArgs (Ty.wrapArrows (.customTy name args) tys) τ) :
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

/-- Every ctor chain has a type of the form `wrapArrows (customTy n args) tys`,
    i.e. some prefix of arrows ending in a `customTy`.

    Inducts syntactically on `e` (rather than on `h_chain`) because `IsCtorChain`
    is mutually defined with `IsValue`, so the `induction` tactic refuses it. -/
private lemma TypeOfHM.ctor_chain_has_customTy_form
    {ctx e τ}
    (h_chain : SmallStep.IsCtorChain e) (h_ty : TypeOfHM ctx e τ) :
    ∃ name args tys, τ = Ty.wrapArrows (.customTy name args) tys := by
  induction e using Expr.rec_strong generalizing ctx τ with
  | ctor _ =>
    cases h_ty with
    | ctor _ h_inst =>
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




/-! ## Substitution lemma & preservation

The substitution lemma is the gateway: it says that replacing a free variable
with a well-typed value of the right type preserves typing. Preservation then
follows by case analysis on the Step rule, using the substitution lemma in the
binder-eliminating cases (beta, let-reduce, letPair-reduce, match-reduce).

Note: the general version below "substitutes anywhere in env" — this is
necessary to push the induction through binders. Under levels, the level being
substituted is `env_pre.length`, with `env_pre` the env-prefix before the
binding being eliminated. -/

/-- If `ty` is closed (no `bvar`s), then `InstantiatesBy` on it is the identity:
    no `bvar` ever gets matched, so the structural recursion just reproduces `ty`. -/
private theorem InstantiatesBy.eq_of_closed
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

theorem TypeOfHM.subst_lemma {env ctors env_post e τ paramTy v}
    (h_body : TypeOfHM
                { ctors, env := env_post ++ [PolyTy.mkTrivial paramTy] ++ env }
                e τ)
    (h_v : TypeOfHM {ctors,env} v paramTy)
    (h_paramTy_closed : OnlyContainsBvars [] paramTy)
    (h_env_post_closed : env_post.freeVars = []) :
    TypeOfHM { ctors, env := env_post ++ env }
      (e.substN env_post.length [v]) τ := by
  induction e using Expr.rec_strong generalizing env env_post τ with
  | primLit _ =>
    cases h_body with
    | primLitUnit => exact .primLitUnit
    | primLitInt  => exact .primLitInt
    | primLitNat  => exact .primLitNat
    | primLitBool => exact .primLitBool
    | primLitStr  => exact .primLitStr
  | ctor _ =>
    cases h_body with
    | ctor h_lookup h_inst => exact .ctor h_lookup h_inst
  | pair _ _ ih_a ih_b =>
    cases h_body with
    | pair h_a h_b =>
      exact .pair (ih_a h_a h_v h_env_post_closed) (ih_b h_b h_v h_env_post_closed)
  | app _ _ ih_f ih_in =>
    cases h_body with
    | app h_f h_in =>
      exact .app (ih_f h_f h_v h_env_post_closed) (ih_in h_in h_v h_env_post_closed)
  | lambda body ih =>
    cases h_body with
    | lambda h_eq h_body_lam =>
      rename_i bodyCtx_inner sndTy paramTy_lam
      subst h_eq
      -- bodyCtx_inner.env was set to `paramTy_lam :: (env_post ++ [paramTy] ++ ctx.env)`,
      -- which is definitionally `(paramTy_lam :: env_post) ++ [paramTy] ++ ctx.env`.
      -- We recurse with env_post' := paramTy_lam :: env_post; substitution position
      -- becomes (env_post.length + 1), which is exactly what `Expr.substN` produces
      -- for `.lambda body`.
      exact .lambda rfl
        (ih (env_post := PolyTy.mkTrivial paramTy_lam :: env_post) h_body_lam h_v
          (by
            -- Need (paramTy_lam :: env_post).freeVars = [].
            -- = paramTy_lam.freeVars ∪ env_post.freeVars (after dedup).
            -- We have env_post.freeVars = [] but not paramTy_lam.freeVars = [].
            -- Would need a closed-paramTy invariant on the typing of `e`.
            sorry))
  | letPairIn _ body ih_pe ih_body =>
    cases h_body with
    | letPairIn h_pe h_genFst h_genSnd h_eq h_body_inner =>
      expose_names
      subst h_eq
      -- IH on body with env_post' := genSndTy :: genFstTy :: env_post (matching
      -- the typing rule's ordering).
      have h_body_subst :=
        ih_body (env_post := genSndTy :: genFstTy :: env_post)
          h_body_inner h_v
          (by
            -- Need (genSndTy :: genFstTy :: env_post).freeVars = [].
            -- Requires both genSndTy.body.freeVars = [] and
            -- genFstTy.body.freeVars = []. With relaxed Generalise, ftvs may
            -- not be max, so body.freeVars = ty.freeVars \ ftvs may be nonempty.
            -- Would need a max-generalisation invariant on h_genFst, h_genSnd.
            sorry)
      -- With the relaxed Generalise (`→` instead of `↔`), the same generalisation
      -- transfers from the bigger env to the smaller env: ftvs need only be
      -- eligible (i.e. ⊆ ¬env.freeVars), and removing paramTy can only ADD
      -- eligibility, so the same h_gen still works.
      have h_subset : (env_post ++ env).freeVars ⊆
          (env_post ++ [PolyTy.mkTrivial paramTy] ++ env).freeVars :=
        Env.freeVars_subset_insert_middle env_post env _
      have h_genFst_new : Generalise (env_post ++ env) fstTy genFstTy := by
        cases h_genFst with
        | mk h_nodup h_eligible h_pt =>
          refine .mk h_nodup ?_ h_pt
          exact fun tv h_mem =>
            ⟨(h_eligible tv h_mem).1,
             fun h_in => (h_eligible tv h_mem).2 (h_subset h_in)⟩
      have h_genSnd_new : Generalise (env_post ++ env) sndTy genSndTy := by
        cases h_genSnd with
        | mk h_nodup h_eligible h_pt =>
          refine .mk h_nodup ?_ h_pt
          exact fun tv h_mem =>
            ⟨(h_eligible tv h_mem).1,
             fun h_in => (h_eligible tv h_mem).2 (h_subset h_in)⟩
      exact .letPairIn (ih_pe h_pe h_v h_env_post_closed)
        h_genFst_new h_genSnd_new rfl h_body_subst
  | match_ scrutinee branches ih_scrut ih_branches =>
    cases h_body with
    | match_ h_scrut h_brs =>
      refine .match_ (ih_scrut h_scrut h_v h_env_post_closed) ?_
      clear ih_scrut h_scrut
      -- Goal: ∀ branch ∈ BranchList.substN env_post.length [v] branches,
      --   TypeOfMatchBranch { env := env_post ++ ctx.env, ... } branch ...
      revert h_brs ih_branches
      induction branches with
      | nil =>
        intros _ _ branch h_mem
        simp only [BranchList.substN] at h_mem
        exact absurd h_mem (List.not_mem_nil)
      | cons hd tl ih_tl =>
        intro ihbs h_brs
        obtain ⟨pat, body⟩ := hd
        intro branch h_mem
        simp only [BranchList.substN] at h_mem
        cases h_mem with
        | head _ =>
          -- branch = (pat, body.substN (env_post.length + pat.contents) [v])
          have h_branch_orig := h_brs (pat, body) List.mem_cons_self
          cases h_branch_orig with
          | mk h_lookup h_tyName h_paramCount h_contents h_inst h_pb h_ctx h_body_orig =>
            subst h_ctx
            subst h_pb
            expose_names
            -- Apply ih_branches to body with env_post' := patternBindings ++ env_post.
            have h_body_subst :=
              ihbs pat body List.mem_cons_self
                (env_post := List.map PolyTy.mkTrivial instContents ++ env_post)
                (by simpa [List.append_assoc] using h_body_orig)
                h_v
                (by
                  -- Need (instContents.map mkTrivial ++ env_post).freeVars = [].
                  -- Requires each instContents element to be closed. With non-
                  -- closed tyArgs at the match, instContents may have freevars.
                  sorry)
            refine .mk h_lookup h_tyName h_paramCount h_contents h_inst rfl rfl ?_
            -- Goal: TypeOfHM { env := List.map ... instContents ++ (env_post ++ ctx.env), ... }
            --         (body.substN (env_post.length + pat.contents) [v]) τ
            have h_len :
                (List.map PolyTy.mkTrivial instContents ++ env_post).length
                  = env_post.length + pat.contents := by
              simp only [List.length_append, List.length_map,
                         ← h_inst.length_eq, ← h_contents]
              omega
            simpa [List.append_assoc, h_len] using h_body_subst
        | tail _ h_mem' =>
          exact ih_tl
            (fun pat' e' hmem => ihbs pat' e' (List.mem_cons_of_mem _ hmem))
            (fun b hmem => h_brs b (List.mem_cons_of_mem _ hmem))
            _ h_mem'
  | letIn _ body ih_be ih_body =>
    cases h_body with
    | letIn h_be h_gen h_eq h_body_inner =>
      expose_names
      subst h_eq
      have h_body_subst :=
        ih_body (env_post := generalisedExprTy :: env_post)
          h_body_inner h_v
          (by
            -- Need (generalisedExprTy :: env_post).freeVars = [].
            -- Requires generalisedExprTy.body.freeVars = [] = be_ty.freeVars \ ftvs.
            -- With relaxed Generalise, ftvs may not equal be_ty.freeVars, so
            -- generalisedExprTy.body may have freevars. Would need a
            -- max-generalisation invariant on h_gen.
            sorry)
      -- Reuse h_gen on the smaller env (relaxed Generalise: ftvs only need
      -- to be a subset of eligibles, and eligibility only grows when env shrinks).
      have h_subset : (env_post ++ env).freeVars ⊆
          (env_post ++ [PolyTy.mkTrivial paramTy] ++ env).freeVars :=
        Env.freeVars_subset_insert_middle env_post env _
      have h_gen_new : Generalise (env_post ++ env) boundExprTy generalisedExprTy := by
        cases h_gen with
        | mk h_nodup h_eligible h_pt =>
          refine .mk h_nodup ?_ h_pt
          exact fun tv h_mem =>
            ⟨(h_eligible tv h_mem).1,
             fun h_in => (h_eligible tv h_mem).2 (h_subset h_in)⟩
      exact .letIn (ih_be h_be h_v h_env_post_closed) h_gen_new rfl h_body_subst
  | var i =>
    cases h_body with
    | var h_lookup h_inst =>
      rcases lt_trichotomy i env_post.length with h_lt | h_eq | h_gt
      · -- Sub-case (1): i < env_post.length. substN keeps `.var i`.
        have h_subst : (Expr.var i).substN env_post.length [v] = .var i := by
          simp [Expr.substN, h_lt]
        rw [h_subst]
        refine .var ?_ h_inst
        -- Lookup at i is in env_post in both envs since i < env_post.length.
        rw [List.getElem?_append_left h_lt]
        rw [List.append_assoc, List.getElem?_append_left h_lt] at h_lookup
        exact h_lookup
      · -- Sub-case (2): i = env_post.length. substN returns `v.shiftFrom 0 k`.
        subst h_eq
        -- substN (.var env_post.length) env_post.length [v] = v.shiftFrom 0 env_post.length
        have h_subst :
            (Expr.var env_post.length).substN env_post.length [v]
              = v.shiftFrom 0 env_post.length := by
          simp [Expr.substN]
        rw [h_subst]
        -- Extract polyTy = PolyTy.mkTrivial paramTy from h_lookup.
        rw [List.append_assoc, List.getElem?_append_right (Nat.le_refl _),
            Nat.sub_self] at h_lookup
        simp at h_lookup
        -- h_lookup : polyTy = PolyTy.mkTrivial paramTy (after simp)
        subst h_lookup
        -- h_inst : InstantiatesBy tyArgs (PolyTy.mkTrivial paramTy).body τ
        --        = InstantiatesBy tyArgs paramTy τ (after unfolding mkTrivial)
        simp [PolyTy.mkTrivial] at h_inst
        -- By closedness, τ = paramTy.
        have h_τ_eq := InstantiatesBy.eq_of_closed h_paramTy_closed h_inst
        subst h_τ_eq
        -- Goal: TypeOfHM { ctx with env := env_post ++ ctx.env }
        --         (v.shiftFrom 0 env_post.length) paramTy
        -- Apply weaken_env to h_v with env_pre := [], env_post := ctx.env,
        -- env_extra := (our outer) env_post.
        exact TypeOfHM.weaken_env (env_pre := []) (env_post := env)
          (env_extra := env_post) h_v h_env_post_closed
      · -- Sub-case (3): i > env_post.length. substN returns `.var (i - 1)`.
        have h_not_lt : ¬ (i < env_post.length) := by omega
        have h_not_lt' : ¬ (i - env_post.length < (1 : Nat)) := by omega
        have h_subst : (Expr.var i).substN env_post.length [v] = .var (i - 1) := by
          simp [Expr.substN, h_not_lt, h_not_lt']
        rw [h_subst]
        refine .var ?_ h_inst
        -- Lookup at i in (env_post ++ [paramTy] ++ ctx.env) falls in ctx.env at
        -- offset (i - env_post.length - 1). Lookup at (i - 1) in (env_post ++ ctx.env)
        -- falls in ctx.env at offset (i - 1 - env_post.length). Equal by arith.
        have h_le_i : env_post.length ≤ i := by omega
        rw [List.getElem?_append_right (by omega : env_post.length ≤ i - 1)]
        rw [List.append_assoc, List.getElem?_append_right h_le_i] at h_lookup
        rw [show ([PolyTy.mkTrivial paramTy] ++ env) = (PolyTy.mkTrivial paramTy
            :: env) from rfl] at h_lookup
        rw [show (i - env_post.length) = (i - env_post.length - 1) + 1 from by omega]
            at h_lookup
        simp only [List.getElem?_cons_succ] at h_lookup
        rw [show (i - 1 - env_post.length) = (i - env_post.length - 1) from by omega]
        exact h_lookup

theorem TypeOfHM.preservation {ctx e τ e'}
    (h_ty : TypeOfHM ctx e τ)
    (h_step : SmallStep.Step e e') :
    TypeOfHM ctx e' τ := by
  sorry
