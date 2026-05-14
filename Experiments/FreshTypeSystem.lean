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


/-- A constructor for a type. E.g. `Result.Ok`, `Maybe.Some`, `Maybe.None` -/
structure Ctor where
  /-- How many type params the type has -/
  paramCount : Nat
  /-- The name of the type this is a constructor for -/
  tyName : TyName
  /-- What this constructor actually contains.
      Can reference `.bvar`s in range of `paramCount` -/
  contents : List Ty

/-- Which type constructors exist -/
abbrev CtorEnv := LookupList CtorName Ctor


structure PolyTy where
  paramCount : Nat
  /-- May reference params by `.bvar`s in range of `paramCount`  -/
  body : Ty

/-- Make a polytype with no type vars -/
def PolyTy.mkTrivial (bodyTy : Ty) : PolyTy :=
  { paramCount := 0, body := bodyTy }



/-- Which value bindings exist -/
abbrev Env := LookupList ValName PolyTy



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
  contents : List ValName


inductive Expr
  | primLit (prim : PrimLitExpr)
  | pair (a b : Expr)
  -- | lambda (param : ValName) (paramTy : Ty) (body : Expr)
  | lambda (param : ValName) (body : Expr)
  | app (f input : Expr)
  | letIn (name : ValName) (bindingExpr body : Expr)
  /-- Destructuring a pair `let (a,b) = pairExpr in body` -/
  | letPairIn (fstName sndName : ValName) (pairExpr body : Expr)
  | var (name : ValName)
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
  | (_, polyTy) :: tail =>
    (polyTy.body.freeVars ++ freeVars tail).dedup


mutual

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




/-- Under env, ty generalises to this polyty -/
inductive Generalise : Env → Ty → PolyTy → Prop
  | mk {env : Env} {ty : Ty} {ftvs : List Nat} :
    ftvs.Nodup →
    (∀ tv, tv ∈ ftvs ↔ tv ∈ ty.freeVars ∧ tv ∉ env.freeVars) →
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


/-- Can only contain `bvar`s that are in `vars`. If `vars` is empty, ty contains no `bvar`s at all. -/
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



-- theorem InstantiatesBy.no_bvars_if_nin_tyArgs : (∀ ty' ∈ tyArgs, OnlyContainsBvars [] ty') → InstantiatesBy tyArgs ty instTy → OnlyContainsBvars [] instTy := by
  -- -- intro nobvargs prem
  -- -- cases prem with
  -- -- | prim => exact .prim
  -- -- | pair a b
  -- -- | arrow a b =>
  -- --   expose_names
  -- --   constructor
  -- --   · exact no_bvars_if_nin_tyArgs nobvargs a
  -- --   · exact no_bvars_if_nin_tyArgs nobvargs b
  -- -- | fvar => constructor
  -- -- | bvar h =>
  -- --   have : instTy ∈ tyArgs := List.mem_of_getElem? h
  -- --   exact nobvargs _ this
  -- -- | customTy h =>
  -- --   expose_names
  -- --   refine OnlyContainsBvars.customTy ?_
  -- --   induction h
  -- --   · simp
  -- --   · expose_names
  -- --     simp
  -- --     constructor
  -- --     ·
  -- --       -- exact no_bvars_if_nin_tyArgs nobvargs h
  -- --     · grind
  -- sorry



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




/-- The match pattern under ctx has type ty and returns an expr of type ty -/
inductive TypeOfMatchBranch :
  (ctx : Ctx) → (MatchPattern × Expr) → (tyName : TyName) → (tyArgs : List Ty) → (resultTy : Ty) → Prop
  | mk {ctor : Ctor} {ctx : Ctx} {pattern : MatchPattern} :
    LookupList.get? ctx.ctors pattern.ctor = some ctor →
    ctor.tyName = tyName →
    ctor.paramCount = tyArgs.length →
    pattern.contents.length = ctor.contents.length →

    -- instantiates the ctor polytype (assigns fvars to its bvars)
    -- instContents =
    --   ctor.contents.map
    --     (λ binding ↦ (Ty.instantiate (Ty.instSubst tyArgs) binding)) →
    List.Forall₂ (InstantiatesBy tyArgs) ctor.contents instContents →

    -- zips together the names of the pattern match vars to their corresponding (instantiated) types in the constructor's content slots
    -- btw we convert them to polytypes but only because that's what the env contains. none of them actually have any type vars. because that would require separate slots to be individually polymorphic, which is not allowed under rank-1 polymorphism.
    -- patternBindings = (pattern.contents.zip instContents |>.map λ (name,ty) ↦ (name, PolyTy.mkTrivial ty)) →
    Zipped pattern.contents (instContents.map PolyTy.mkTrivial) patternBindings →

    -- just sticks the new patterns and their
    bodyCtx = {ctx with env := patternBindings ++ ctx.env } →

    TypeOfHM bodyCtx bodyExpr resultTy →
    TypeOfMatchBranch ctx (pattern, bodyExpr) tyName tyArgs resultTy





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

  /-- We just posit the existence of a paramTy -/
  | lambda :
    bodyCtx = { ctx with env := (paramName, .mkTrivial paramTy) :: ctx.env } →
    TypeOfHM bodyCtx body sndTy →
    TypeOfHM ctx (.lambda paramName body) (.arrow paramTy sndTy)

  | app :
    TypeOfHM ctx f (.arrow argTy retTy) →
    TypeOfHM ctx input argTy →
    TypeOfHM ctx (.app f input) retTy

  | letIn :
    TypeOfHM ctx boundExpr boundExprTy →
    Generalise ctx.env boundExprTy generalisedExprTy →
    bodyCtx = {ctx with env := (name, generalisedExprTy) :: ctx.env} →
    TypeOfHM bodyCtx body bodyTy →
    TypeOfHM ctx (.letIn name boundExpr body) bodyTy

  | letPairIn :
    TypeOfHM ctx boundExpr (.pair fstTy sndTy) →
    Generalise ctx.env fstTy genFstTy →
    Generalise ctx.env sndTy genSndTy →
    bodyCtx =
      {ctx with
        env := (fstName, genFstTy) :: (sndName, genSndTy) :: ctx.env} →
    TypeOfHM bodyCtx body bodyTy →
    TypeOfHM ctx (.letPairIn fstName sndName boundExpr body) bodyTy

  | var :
    LookupList.get? ctx.env name = some polyTy →
    -- Ty.instantiate subst polyTy.body = ty →
    InstantiatesBy tyArgs polyTy.body ty →
    TypeOfHM ctx (.var name) ty

  | ctor {subst : Nat → Ty} :
    LookupList.get? ctx.ctors name = some ctor →
    -- Ty.instantiate subst ctor.toTy.body = ty →
    InstantiatesBy tyArgs ctor.toTy.body ty →
    TypeOfHM ctx (.ctor name) ty

  | match_ :
    TypeOfHM ctx scrutinee (.customTy tyName tyArgs) →
    ∀ branch ∈ branches, TypeOfMatchBranch ctx branch tyName tyArgs resultTy →
    TypeOfHM ctx (.match_ scrutinee branches) resultTy

end
