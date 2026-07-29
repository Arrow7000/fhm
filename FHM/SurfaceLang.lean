import FHM.Core

namespace Surface





inductive PrimTy
  | unit
  | int
  | nat
  | bool
  | char
  deriving DecidableEq, Repr

/-! ## P4a — bound counts in surface types (shapes for sign-off / integration)

Surface counts are **syntax**, not the Bounds kernel `Count` (no rigid/inferable
indices here). Erase (P4b) maps these into `FHM.Bounds` + `BoundAnn`.

`hole` is surface `_` in a bound slot only (e.g. `BL _ 5 a`).
-/

/-- Surface syntax for list length bounds.

v1 parse: `lit` / `var` / `hole` only. Kernel-shaped ops (`add`/`mul`/`pred`/
`min`/`max`) are deferred — see design memo **P4a-count-ops** (before any
surface demo that needs `n+1` / `pred`, and no later than P5 scheme demos).
Erase (P4b) maps these into `FHM.Bounds.Count` + `BoundAnn`. -/
inductive Count where
  | lit (n : Nat)
  | var (name : ValName)
  | hole
  deriving DecidableEq, Repr

inductive Ty
  | prim : PrimTy → Ty
  | pair : (fst snd : Ty) → Ty
  | arrow : (from_ to_ : Ty) → Ty
  /-- A type variable -/
  | tvar : ValName → Ty
  /-- A custom type with its type params -/
  | customTy : TyName → List Ty → Ty
  /-- Bounded list type `BL lo hi elem` (refines `List elem` after erase). -/
  | bl (lo hi : Count) (elem : Ty)
  deriving Repr

/--
Strong induction for `Ty` with a useful IH on `customTy` / `bl`:
`(∀ t ∈ tys, motive t)` instead of a bare motive on the list.
-/
@[elab_as_elim]
def Ty.rec_strong.{u} {motive : Ty → Sort u}
    (prim     : ∀ p, motive (.prim p))
    (pair     : ∀ a b, motive a → motive b → motive (.pair a b))
    (arrow    : ∀ a b, motive a → motive b → motive (.arrow a b))
    (tvar     : ∀ n, motive (.tvar n))
    (customTy : ∀ nm tys, (∀ t ∈ tys, motive t) → motive (.customTy nm tys))
    (bl       : ∀ lo hi e, motive e → motive (.bl lo hi e)) :
    (ty : Ty) → motive ty
  | .prim p          => prim p
  | .pair a b        =>
      pair a b
        (Ty.rec_strong prim pair arrow tvar customTy bl a)
        (Ty.rec_strong prim pair arrow tvar customTy bl b)
  | .arrow a b       =>
      arrow a b
        (Ty.rec_strong prim pair arrow tvar customTy bl a)
        (Ty.rec_strong prim pair arrow tvar customTy bl b)
  | .tvar n          => tvar n
  | .customTy nm tys =>
      customTy nm tys
        (fun t _ht => Ty.rec_strong prim pair arrow tvar customTy bl t)
  | .bl lo hi e      =>
      bl lo hi e (Ty.rec_strong prim pair arrow tvar customTy bl e)
termination_by ty => sizeOf ty
decreasing_by
  all_goals simp_wf
  all_goals first
    | omega
    | (have := List.sizeOf_lt_of_mem _ht; omega)

/-- No `bl` constructors (post-erase invariant for the HM lower stack). -/
inductive Ty.DoesntContainBounds : Ty → Prop where
  | prim {p} : DoesntContainBounds (.prim p)
  | tvar {n} : DoesntContainBounds (.tvar n)
  | pair {a b} :
      DoesntContainBounds a → DoesntContainBounds b → DoesntContainBounds (.pair a b)
  | arrow {a b} :
      DoesntContainBounds a → DoesntContainBounds b → DoesntContainBounds (.arrow a b)
  | customTy {nm tys} :
      (∀ t ∈ tys, DoesntContainBounds t) → DoesntContainBounds (.customTy nm tys)

/-- Scheme as today: `{a b} body`. Nat binders `{n : Nat, a}` deferred to P5
(adding a field breaks every positional `⟨foralls, body⟩` in the tree). -/
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

/--
Strong induction for `Expr` with useful IHs on nested lists:
- `list`: `(∀ e ∈ items, motive e)`
- `letRecIn`: `(∀ b ∈ bindings, motive b.rhs)`
- `match_`: `(∀ pat e, (pat, e) ∈ branches → motive e)`

rather than bare motives on the lists from the auto-generated recursor.

Usage:
```
theorem some_property : ∀ e : Expr, P e := by
  intro e
  induction e using Expr.rec_strong
  case primLit p                            => ...
  case pair a b iha ihb                     => ...
  case list items ih                        => ...
  case lambda param paramAnn body ih        => ...
  case app f input ihf ihi                  => ...
  case letIn ... ihbe ihbo                  => ...
  case letRecIn bindings body ihbs ihbo     => ...
    -- ihbs : ∀ b ∈ bindings, P b.rhs
  case match_ scrutinee branches ihs ihbs   => ...
    -- ihbs : ∀ pat e, (pat, e) ∈ branches → P e
```
-/
@[elab_as_elim]
def Expr.rec_strong.{u} {motive : Expr → Sort u}
    (primLit   : ∀ p, motive (.primLit p))
    (primBinOp : ∀ op, motive (.primBinOp op))
    (pair      : ∀ a b, motive a → motive b → motive (.pair a b))
    (cons      : ∀ head tail, motive head → motive tail → motive (.cons head tail))
    (list      : ∀ items, (∀ e ∈ items, motive e) → motive (.list items))
    (lambda    : ∀ param paramAnn body, motive body → motive (.lambda param paramAnn body))
    (app       : ∀ f input, motive f → motive input → motive (.app f input))
    (letIn     : ∀ binding tyParams params ann bindingExpr body,
                   motive bindingExpr → motive body →
                   motive (.letIn binding tyParams params ann bindingExpr body))
    (letRecIn  : ∀ bindings body,
                   (∀ b ∈ bindings, motive b.rhs) → motive body →
                   motive (.letRecIn bindings body))
    (var       : ∀ binding, motive (.var binding))
    (ctor      : ∀ name, motive (.ctor name))
    (ife       : ∀ cond t f, motive cond → motive t → motive f → motive (.ife cond t f))
    (match_    : ∀ scrutinee branches,
                   motive scrutinee →
                   (∀ pat e, (pat, e) ∈ branches → motive e) →
                   motive (.match_ scrutinee branches)) :
    (e : Expr) → motive e
  | .primLit p    => primLit p
  | .primBinOp op => primBinOp op
  | .pair a b =>
      pair a b
        (Expr.rec_strong primLit primBinOp pair cons list lambda app letIn letRecIn
          var ctor ife match_ a)
        (Expr.rec_strong primLit primBinOp pair cons list lambda app letIn letRecIn
          var ctor ife match_ b)
  | .cons head tail =>
      cons head tail
        (Expr.rec_strong primLit primBinOp pair cons list lambda app letIn letRecIn
          var ctor ife match_ head)
        (Expr.rec_strong primLit primBinOp pair cons list lambda app letIn letRecIn
          var ctor ife match_ tail)
  | .list items =>
      list items
        (fun e _he =>
          Expr.rec_strong primLit primBinOp pair cons list lambda app letIn letRecIn
            var ctor ife match_ e)
  | .lambda param paramAnn body =>
      lambda param paramAnn body
        (Expr.rec_strong primLit primBinOp pair cons list lambda app letIn letRecIn
          var ctor ife match_ body)
  | .app f input =>
      app f input
        (Expr.rec_strong primLit primBinOp pair cons list lambda app letIn letRecIn
          var ctor ife match_ f)
        (Expr.rec_strong primLit primBinOp pair cons list lambda app letIn letRecIn
          var ctor ife match_ input)
  | .letIn binding tyParams params ann bindingExpr body =>
      letIn binding tyParams params ann bindingExpr body
        (Expr.rec_strong primLit primBinOp pair cons list lambda app letIn letRecIn
          var ctor ife match_ bindingExpr)
        (Expr.rec_strong primLit primBinOp pair cons list lambda app letIn letRecIn
          var ctor ife match_ body)
  | .letRecIn bindings body =>
      letRecIn bindings body
        (fun b _hb =>
          Expr.rec_strong primLit primBinOp pair cons list lambda app letIn letRecIn
            var ctor ife match_ b.rhs)
        (Expr.rec_strong primLit primBinOp pair cons list lambda app letIn letRecIn
          var ctor ife match_ body)
  | .var binding => var binding
  | .ctor name   => ctor name
  | .ife cond t f =>
      ife cond t f
        (Expr.rec_strong primLit primBinOp pair cons list lambda app letIn letRecIn
          var ctor ife match_ cond)
        (Expr.rec_strong primLit primBinOp pair cons list lambda app letIn letRecIn
          var ctor ife match_ t)
        (Expr.rec_strong primLit primBinOp pair cons list lambda app letIn letRecIn
          var ctor ife match_ f)
  | .match_ scrutinee branches =>
      match_ scrutinee branches
        (Expr.rec_strong primLit primBinOp pair cons list lambda app letIn letRecIn
          var ctor ife match_ scrutinee)
        (fun _pat e _hb =>
          Expr.rec_strong primLit primBinOp pair cons list lambda app letIn letRecIn
            var ctor ife match_ e)
termination_by e => sizeOf e
decreasing_by
  all_goals simp_wf
  all_goals first
    | omega
    | (have h := List.sizeOf_lt_of_mem _he
       omega)
    | (have h := List.sizeOf_lt_of_mem _hb
       simp only [Prod.mk.sizeOf_spec] at h
       omega)
    | (have h := List.sizeOf_lt_of_mem _hb
       cases b
       simp only [Binding'.mk.sizeOf_spec] at h ⊢
       omega)

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
