/-! # Quantitative experiments

Minimal `Ty` / `Expr` scaffold copied from `FHM.Core` for standalone experiments. -/

namespace QuantitativeExperiments

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

inductive PrimTy
  | unit
  | int
  | nat
  | char
  deriving DecidableEq, Repr

/-- Prelude List ADT name (Nil/Cons). Bare `List t` is `customTy listTyName [t]`. -/
def listTyName : TyName := ⟨"List"⟩

inductive Ty
  | prim : PrimTy → Ty
  | arrow : (from_ to_ : Ty) → Ty
  /-- Bound var – only makes sense within the context of a polytype -/
  | bvar : Nat → Ty
  /-- Free var – unbound var. In spec-land this signifies an unconstrained variable.
  In algorithm-land this is a unification variable. -/
  | fvar : Nat → Ty
  /-- A custom type with its type params -/
  | customTy : TyName → List Ty → Ty
  deriving Repr

/-- Bare HM list: user `List t` or Infer-filled list shape. -/
def bareListTy (α : Ty) : Ty :=
  .customTy listTyName [α]

structure PolyTy where
  paramCount : Nat
  /-- May reference params by `.bvar`s in range of `paramCount`  -/
  body : Ty

/-- Make a polytype with no type vars -/
def PolyTy.mkTrivial (bodyTy : Ty) : PolyTy :=
  { paramCount := 0, body := bodyTy }

/-- Primitive literals -/
inductive PrimLitExpr
  | unit : PrimLitExpr
  | int : Int → PrimLitExpr
  | nat : Nat → PrimLitExpr
  | char : Char → PrimLitExpr

/-- Primitive binary operators: built-in, monomorphic, curried 2-argument functions. -/
inductive PrimBinOp
  | intAdd
  | intSub
  | intLt
  | charLt
  deriving DecidableEq, Repr

inductive MatchPattern
  /-- `contents` is basically just a binding range. i.e. if 2 this means we've bound 2 new "names" to the context -/
  | named (ctor : CtorName) (contents : Nat)
  | wildcard
  deriving DecidableEq, Repr

/-- An expression in our language -/
inductive Expr
  | primLit (prim : PrimLitExpr)
  /-- A primitive binary operator (e.g. `intAdd`). Applied via ordinary `app`. -/
  | primBinOp (op : PrimBinOp)
  /-- A lambda. `paramAnn` is an optional type ascription on the parameter
      (surface `λ(x : T). body`); `none` means the param type is inferred. -/
  | lambda (paramAnn : Option Ty) (body : Expr)
  | app (f input : Expr)
  /-- A let binding. `ann` is an optional scheme ascription on the bound
      expression (surface `let x : σ = e in body`); `none` means the scheme is
      generalised by inference. -/
  | letIn (ann : Option PolyTy) (bindingExpr body : Expr)
  /-- A variable use, carrying the explicit type arguments at which its scheme is
      instantiated (type-passing). `tyArgs = []` for a monomorphic use. -/
  | var (deBruijnIndex : Nat) (tyArgs : List Ty)
  /-- A type constructor -/
  | ctor (name : CtorName)
  | match_ (scrutinee : Expr) (branches : List (MatchPattern × Expr))
  /-- A (mutually) recursive binding group with per-binding optional scheme
      annotations (mirroring `letIn`'s `ann`). -/
  | letRec (anns : List (Option PolyTy)) (bindings : List Expr) (body : Expr)

end QuantitativeExperiments
