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

def get? [DecidableEq k] (l : LookupList k v) (key : k) :=
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



-- /-- Type constructor – is either simple or arrow to another one -/
-- inductive Ctor (t : Type)
--   | done
--   | param : (ty : t) → Ctor t → Ctor t







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
  -- | typeVar : (debruijnIndex : Nat) → Ty
  | bvar : Nat → Ty
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
  /-- What this constructor actually contains. Can reference `.typeVar`s in range of `paramCount` -/
  contents : List Ty

/-- Which type constructors exist -/
abbrev CtorEnv := LookupList CtorName Ctor


structure PolyTy where
  paramCount : Nat
  /-- May reference params by `.typeVar`s in range of `paramCount`  -/
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
def Ty.bvarRange (start : Nat) : Nat → List Ty
  | 0     => []
  | n + 1 => .bvar start :: bvarRange (start + 1) n

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
    .customTy ctor.tyName (Ty.bvarRange 0 ctor.paramCount)

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



def TyList.freeVars : List Ty → List Nat
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
  | .fvar n          =>
      match vars.idxOf? n with
      | some i => .bvar i
      | none   => .fvar n
  | .customTy nm tys => .customTy nm (TyList.closeOver vars tys)

def TyList.closeOver (vars : List Nat) : List Ty → List Ty
  | []        => []
  | hd :: tl  => hd.closeOver vars :: TyList.closeOver vars tl

end

-- def generalise (env : Env) (ty : Ty) : PolyTy :=

/-- Under env, ty generalises to this polyty -/
inductive Generalise : Env → Ty → PolyTy → Prop
  | mk {env : Env} {ty : Ty} :
    ftvs = ty.freeVars \ env.freeVars →
    Generalise env ty ⟨ftvs.length, ty.closeOver ftvs⟩


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

  | var {subst : Nat → Ty} :
    LookupList.get? ctx.env name = some polyTy →
    Ty.instantiate subst polyTy.body = ty →
    TypeOfHM ctx (.var name) ty

  | ctor {subst : Nat → Ty} :
    LookupList.get? ctx.ctors name = some ctor →
    Ty.instantiate subst ctor.toTy.body = ty →
    TypeOfHM ctx (.ctor name) ty
