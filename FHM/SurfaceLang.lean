import FHM.Core

namespace Surface





inductive PrimTy
  | unit
  | int
  | nat
  | bool
  | char
  deriving DecidableEq, Repr


inductive Ty
  | prim : PrimTy → Ty
  | pair : (fst snd : Ty) → Ty
  | arrow : (from_ to_ : Ty) → Ty
  /-- A type variable -/
  | tvar : ValName → Ty
  /-- A custom type with its type params -/
  | customTy : TyName → List Ty → Ty
  deriving Repr




structure PolyTy where
  foralls : List ValName
  body : Ty


/-- Surface algebraic data declaration: named type params, named ctors,
    positional field types (no field names in this slice). -/
structure DataDecl where
  name   : TyName
  params : List ValName
  ctors  : List (CtorName × List Ty)
  deriving Repr


/-- Primitive literals -/
inductive PrimLitExpr
  | unit : PrimLitExpr
  | int : Int → PrimLitExpr
  | nat : Nat → PrimLitExpr
  | bool : Bool → PrimLitExpr
  | char : Char → PrimLitExpr




inductive Pattern
  | pair (fst snd : Pattern)
  | ctor (name : CtorName) (patterns : List Pattern)
  | cons (head tail : Pattern)
  | list (items : List Pattern)
  | name (name : ValName)
  | wildcard





/-- An expression in our language -/
inductive Expr
  | primLit (prim : PrimLitExpr)
  | pair (a b : Expr)
  | cons (head tail : Expr)
  | list (items : List Expr)
  | lambda (param : Pattern) (paramAnn : Option Ty) (body : Expr)
  | app (f input : Expr)
  | letIn (binding : ValName) (ann : Option PolyTy) (bindingExpr body : Expr)
  | letRecIn (bindingsAnns : List (ValName × Option PolyTy × Expr)) (body : Expr)
  | var (binding : ValName)
  | ctor (name : CtorName)
  | ife (cond t f : Expr)
  | match_ (scrutinee : Expr) (branches : List (Pattern × Expr))
