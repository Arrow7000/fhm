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





/-- A value binding as written: optional `{tyParams}`, value `params`, optional
    `: ann`, and `rhs`. Sugar is erased in lowering (→ Core `λ`). -/
structure Binding' (expr : Type) where
  name : ValName
  tyParams : List ValName := []
  params : List (ValName × Option Ty) := []
  ann  : Option PolyTy
  rhs  : expr


/-- An expression in our language -/
inductive Expr
  | primLit (prim : PrimLitExpr)
  | primBinOp (op : PrimBinOp)
  | pair (a b : Expr)
  | cons (head tail : Expr)
  | list (items : List Expr)
  | lambda (param : Pattern) (paramAnn : Option Ty) (body : Expr)
  | app (f input : Expr)
  | letIn (binding : ValName) (tyParams : List ValName)
      (params : List (ValName × Option Ty)) (ann : Option PolyTy)
      (bindingExpr body : Expr)
  | letRecIn (bindings : List (Binding' Expr)) (body : Expr)
  | var (binding : ValName)
  | ctor (name : CtorName)
  | ife (cond t f : Expr)
  | match_ (scrutinee : Expr) (branches : List (Pattern × Expr))


abbrev Binding := Binding' Expr

/-- A surface program: user data declarations, mutual-binding groups
    (author-supplied, or from `SurfaceBridge.Program.ofFlat` / `sccGroups`),
    and a body. Each nonempty group desugars to `letRecIn` (including size 1 —
    self-recursion works). -/
structure Program where
  decls  : List DataDecl
  groups : List (List Binding)
  body   : Expr

/-- Nest groups outermost-first as `letRecIn`, then `body`.
    Empty groups are skipped; nonempty → always `letRecIn` (incl. size 1). -/
def desugarGroups (groups : List (List Binding)) (body : Expr) : Expr :=
  groups.foldr (fun g acc =>
    if g.isEmpty then acc
    else .letRecIn g acc) body

/-- The expression a program lowers: group nesting around `body`. -/
def Program.term (p : Program) : Expr :=
  desugarGroups p.groups p.body
