import Mathlib.Data.List.Dedup

/-!
# EPL syntax

One type syntax `Ty V`, parametric in what its flexible variables are:

* `SemTy := Ty Empty` — declarative types. Metavariable-free by construction.
* `InfTy := Ty Nat` — inference types; `var id` is metavariable `?id`.
* `Template := Ty String` — partial annotations; `var name` is a named hole.
  The surface `_` is sugar for a hole with a fresh name.

Type variables come in two further kinds, both natural numbers:

* `bvar i` — bound by the enclosing `Scheme` (de Bruijn index). Occurs only in
  scheme bodies: in contexts and in data declarations.
* `rigid l` — a skolem/type variable in scope, by *level*: the binders of the
  written schemes enclosing a source position are levels `0, 1, ...`, outermost
  first. Source annotations always refer to type variables by level, so no
  source term is ever re-indexed.

Every operation on types that replaces variables is an instance of the one
traversal `Ty.subst`, whose laws (`Ty.subst_subst`, `Ty.subst_congr`,
`Ty.scoped_subst` in `EPL.Spec.Syntax`) are the whole type-level library.
-/

namespace EPL

inductive PrimTy where
  | unit
  | int
  | char
  deriving DecidableEq, Repr

inductive Ty (V : Type) where
  | prim (name : PrimTy)
  | arrow (domain codomain : Ty V)
  /-- Declared data type number `id` of the program's signature. -/
  | con (id : Nat)
  /-- Type application. Kinds are not checked: an ill-kinded application is a
  type without values. -/
  | app (function argument : Ty V)
  | bvar (index : Nat)
  | rigid (level : Nat)
  | var (v : V)
  deriving DecidableEq, Repr

abbrev SemTy := Ty Empty
abbrev InfTy := Ty Nat
abbrev Template := Ty String

/-! ## The one substitution -/

/-- What to put in place of each kind of variable. -/
structure Ty.Subst (V W : Type) where
  bvar : Nat → Ty W
  rigid : Nat → Ty W
  var : V → Ty W

def Ty.subst (σ : Ty.Subst V W) : Ty V → Ty W
  | .prim name => .prim name
  | .arrow domain codomain => .arrow (domain.subst σ) (codomain.subst σ)
  | .con id => .con id
  | .app function argument => .app (function.subst σ) (argument.subst σ)
  | .bvar index => σ.bvar index
  | .rigid level => σ.rigid level
  | .var v => σ.var v

def Ty.Subst.id : Ty.Subst V V := ⟨.bvar, .rigid, .var⟩

/-- First `σ`, then `τ`. -/
def Ty.Subst.comp (σ : Ty.Subst U V) (τ : Ty.Subst V W) : Ty.Subst U W :=
  ⟨fun i => (σ.bvar i).subst τ, fun l => (σ.rigid l).subst τ, fun v => (σ.var v).subst τ⟩

/-- Replace flexible variables (monadic bind). -/
def Ty.bind (ty : Ty V) (f : V → Ty W) : Ty W :=
  ty.subst ⟨.bvar, .rigid, f⟩

/-- A semantic type, seen at any variable type. -/
def Ty.lift (ty : SemTy) : Ty V :=
  ty.bind Empty.elim

/-- Replace scheme-bound variables `bvar i` by `args[i]`. -/
def Ty.instantiate (args : List (Ty V)) (ty : Ty V) : Ty V :=
  ty.subst ⟨fun i => args.getD i (.bvar i), .rigid, .var⟩

/-- Replace rigid variables (type substitution). -/
def Ty.substRigids (f : Nat → Ty V) (ty : Ty V) : Ty V :=
  ty.subst ⟨.bvar, f, .var⟩

/-- Turn rigid levels `k, ..., k+n-1` into `bvar 0, ..., bvar (n-1)`. -/
def Ty.closeRigids (k n : Nat) (ty : Ty V) : Ty V :=
  ty.substRigids fun l => if k ≤ l ∧ l < k + n then .bvar (l - k) else .rigid l

/-- The rigid levels `k, ..., k+n-1`. -/
def rigidBlock (k n : Nat) : List (Ty V) :=
  (List.range n).map fun i => .rigid (k + i)

/-- The flexible variables of a type, in order, with repetition. -/
def Ty.vars : Ty V → List V
  | .prim _ | .con _ | .bvar _ | .rigid _ => []
  | .arrow domain codomain => domain.vars ++ codomain.vars
  | .app function argument => function.vars ++ argument.vars
  | .var v => [v]

def Ty.size : Ty V → Nat
  | .prim _ | .con _ | .bvar _ | .rigid _ | .var _ => 1
  | .arrow domain codomain => domain.size + codomain.size + 1
  | .app function argument => function.size + argument.size + 1

/-- The type, if it has no flexible variables. -/
def Ty.ground : Ty V → Option SemTy
  | .prim name => some (.prim name)
  | .arrow domain codomain => do some (.arrow (← domain.ground) (← codomain.ground))
  | .con id => some (.con id)
  | .app function argument => do some (.app (← function.ground) (← argument.ground))
  | .bvar index => some (.bvar index)
  | .rigid level => some (.rigid level)
  | .var _ => none

/-! ## Scope -/

/-- Rigid levels are below `rigids`, bound indices below `binders`. Flexible
variables are unconstrained. -/
def Ty.Scoped (rigids binders : Nat) : Ty V → Prop
  | .prim _ | .con _ | .var _ => True
  | .arrow domain codomain => domain.Scoped rigids binders ∧ codomain.Scoped rigids binders
  | .app function argument => function.Scoped rigids binders ∧ argument.Scoped rigids binders
  | .bvar index => index < binders
  | .rigid level => level < rigids

instance Ty.decScoped (rigids binders : Nat) : (ty : Ty V) → Decidable (ty.Scoped rigids binders)
  | .prim _ | .con _ | .var _ => isTrue trivial
  | .arrow domain codomain =>
      have := Ty.decScoped rigids binders domain
      have := Ty.decScoped rigids binders codomain
      inferInstanceAs (Decidable (_ ∧ _))
  | .app function argument =>
      have := Ty.decScoped rigids binders function
      have := Ty.decScoped rigids binders argument
      inferInstanceAs (Decidable (_ ∧ _))
  | .bvar index => inferInstanceAs (Decidable (index < binders))
  | .rigid level => inferInstanceAs (Decidable (level < rigids))

/-- A type at rigid depth `k`: rigid levels below `k`, no bound variables. -/
abbrev Ty.WF (k : Nat) (ty : Ty V) : Prop := ty.Scoped k 0

/-! ## Schemes -/

/-- `forall (arity binders). body`; the body names its binders `bvar 0 ...
bvar (arity - 1)`. -/
structure Scheme (V : Type) where
  arity : Nat
  body : Ty V
  deriving DecidableEq, Repr

def Scheme.mono (ty : Ty V) : Scheme V := ⟨0, ty⟩

def Scheme.inst (scheme : Scheme V) (args : List (Ty V)) : Ty V :=
  scheme.body.instantiate args

/-- The generic instance at rigid depth `k`: binders become levels
`k, ..., k + arity - 1`. -/
def Scheme.skolemize (scheme : Scheme V) (k : Nat) : Ty V :=
  scheme.inst (rigidBlock k scheme.arity)

def Scheme.bind (scheme : Scheme V) (f : V → Ty W) : Scheme W :=
  ⟨scheme.arity, scheme.body.bind f⟩

def Scheme.lift (scheme : Scheme Empty) : Scheme V :=
  ⟨scheme.arity, scheme.body.lift⟩

def Scheme.substRigids (f : Nat → Ty V) (scheme : Scheme V) : Scheme V :=
  ⟨scheme.arity, scheme.body.substRigids f⟩

abbrev Scheme.WF (k : Nat) (scheme : Scheme V) : Prop := scheme.body.Scoped k scheme.arity

/-- `ty` is an instance of `scheme` by arguments well-formed at depth `k`. -/
def Scheme.Instance (k : Nat) (scheme : Scheme V) (ty : Ty V) : Prop :=
  ∃ args : List (Ty V), args.length = scheme.arity ∧ (∀ arg ∈ args, arg.WF k) ∧
    scheme.inst args = ty

abbrev Ctx (V : Type) := List (Scheme V)

def Ctx.WF (k : Nat) (ctx : Ctx V) : Prop := ∀ scheme ∈ ctx, scheme.WF k

/-! ## Templates -/

/-- Some assignment of types to the holes completes the template to `ty`.
Holes with the same name get the same type. -/
def Template.Matches (template : Template) (ty : SemTy) : Prop :=
  ∃ holes : String → SemTy, template.bind holes = ty

/-- An optional annotation; `none` matches every type. -/
def Template.MatchesOpt : Option Template → SemTy → Prop
  | none, _ => True
  | some template, ty => template.Matches ty

/-! ## Data declarations -/

/-- A data type with `params` type parameters (`bvar 0 ... bvar (params - 1)`
in field types) and one list of field types per constructor. Field types may
name any declared type, so recursion and mutual recursion are allowed. -/
structure DataDecl where
  params : Nat
  ctors : List (List SemTy)
  deriving DecidableEq, Repr

/-- A program's data declarations: type `con i` is declaration `i`. -/
abbrev Signature := List DataDecl

/-- The constants a signature introduces. Arities live in the signature, which
evaluation consults. -/
inductive DataConst where
  /-- Constructor number `index` of declared type `type`. -/
  | ctor (type index : Nat)
  /-- The eliminator of declared type `type`. Surface `match` and `if` are
  applications of an eliminator. -/
  | elim (type : Nat)
  deriving DecidableEq, Repr

/-! ## Expressions -/

inductive PrimLit where
  | unit
  | int (value : Int)
  | char (value : Char)
  deriving DecidableEq, Repr

inductive PrimOp where
  | intAdd
  | intSub
  | intLt
  | charLt
  deriving DecidableEq, Repr

/-- A polymorphic let's annotation `forall (arity binders). body`. Unlike a
`Scheme`, the body names its binders by rigid level: at depth `k` they are
`rigid k, ..., rigid (k + arity - 1)`. -/
structure PolyAnn (A : Type) where
  arity : Nat
  body : A
  deriving DecidableEq, Repr

def PolyAnn.map (f : A → B) (ann : PolyAnn A) : PolyAnn B := ⟨ann.arity, f ann.body⟩

/-- Expressions, parametric in the annotation type `A`:
* `Source := Expr Template` — what the programmer wrote;
* `Elab := Expr SemTy` — the same program with every implicit type filled in
  (every annotation is `some`);
* `RuntimeExpr := Expr Empty` — after erasure (every annotation is `none`). -/
inductive Expr (A : Type) where
  | lit (literal : PrimLit)
  | primOp (op : PrimOp)
  | const (c : DataConst)
  | var (index : Nat)
  | lambda (param : Option A) (body : Expr A)
  | app (function argument : Expr A)
  /-- `none`: a monomorphic let. `some ann`: a let with an explicit scheme;
  its right-hand side is one rigid depth level per binder deeper. -/
  | letIn (ann : Option (PolyAnn A)) (rhs body : Expr A)
  /-- Monomorphic recursion; `self` annotates the recursive binder, as `param`
  does a lambda's. -/
  | fix (self : Option A) (body : Expr A)
  deriving DecidableEq, Repr

abbrev Source := Expr Template
abbrev Elab := Expr SemTy
abbrev RuntimeExpr := Expr Empty

def Expr.mapAnn (f : A → B) : Expr A → Expr B
  | .lit literal => .lit literal
  | .primOp op => .primOp op
  | .const c => .const c
  | .var index => .var index
  | .lambda param body => .lambda (param.map f) (body.mapAnn f)
  | .app function argument => .app (function.mapAnn f) (argument.mapAnn f)
  | .letIn ann rhs body => .letIn (ann.map (PolyAnn.map f)) (rhs.mapAnn f) (body.mapAnn f)
  | .fix self body => .fix (self.map f) (body.mapAnn f)

/-- Map every annotation, failing if any annotation fails. -/
def Expr.traverseAnn (f : A → Option B) : Expr A → Option (Expr B)
  | .lit literal => some (.lit literal)
  | .primOp op => some (.primOp op)
  | .const c => some (.const c)
  | .var index => some (.var index)
  | .lambda none body => do some (.lambda none (← body.traverseAnn f))
  | .lambda (some param) body => do some (.lambda (some (← f param)) (← body.traverseAnn f))
  | .app function argument => do
      some (.app (← function.traverseAnn f) (← argument.traverseAnn f))
  | .letIn none rhs body => do
      some (.letIn none (← rhs.traverseAnn f) (← body.traverseAnn f))
  | .letIn (some ann) rhs body => do
      some (.letIn (some ⟨ann.arity, ← f ann.body⟩) (← rhs.traverseAnn f) (← body.traverseAnn f))
  | .fix none body => do some (.fix none (← body.traverseAnn f))
  | .fix (some self) body => do some (.fix (some (← f self)) (← body.traverseAnn f))

/-- Every annotation of an expression, in order. -/
def Expr.anns : Expr A → List A
  | .lit _ | .primOp _ | .const _ | .var _ => []
  | .lambda none body => body.anns
  | .lambda (some param) body => param :: body.anns
  | .app function argument => function.anns ++ argument.anns
  | .letIn none rhs body => rhs.anns ++ body.anns
  | .letIn (some ann) rhs body => ann.body :: (rhs.anns ++ body.anns)
  | .fix none body => body.anns
  | .fix (some self) body => self :: body.anns

/-- Forget every annotation. A source program and its elaboration erase to the
same runtime expression. -/
def Expr.erase : Expr A → RuntimeExpr
  | .lit literal => .lit literal
  | .primOp op => .primOp op
  | .const c => .const c
  | .var index => .var index
  | .lambda _ body => .lambda none body.erase
  | .app function argument => .app function.erase argument.erase
  | .letIn _ rhs body => .letIn none rhs.erase body.erase
  | .fix _ body => .fix none body.erase

/-- Add `amount` to every term variable at or above `cutoff`. -/
def Expr.shift (cutoff amount : Nat) : Expr A → Expr A
  | .lit literal => .lit literal
  | .primOp op => .primOp op
  | .const c => .const c
  | .var index => .var (if cutoff ≤ index then index + amount else index)
  | .lambda param body => .lambda param (body.shift (cutoff + 1) amount)
  | .app function argument => .app (function.shift cutoff amount) (argument.shift cutoff amount)
  | .letIn ann rhs body => .letIn ann (rhs.shift cutoff amount) (body.shift (cutoff + 1) amount)
  | .fix self body => .fix self (body.shift (cutoff + 1) amount)

/-- Replace term variable `depth` by `value` (whose free variables are relative
to the outside of `depth` binders) and close the gap. -/
def Expr.substAt : Expr A → Nat → Expr A → Expr A
  | .lit literal, _, _ => .lit literal
  | .primOp op, _, _ => .primOp op
  | .const c, _, _ => .const c
  | .var index, depth, value =>
      if index < depth then .var index
      else if index = depth then value.shift 0 depth
      else .var (index - 1)
  | .lambda param body, depth, value => .lambda param (body.substAt (depth + 1) value)
  | .app function argument, depth, value =>
      .app (function.substAt depth value) (argument.substAt depth value)
  | .letIn ann rhs body, depth, value =>
      .letIn ann (rhs.substAt depth value) (body.substAt (depth + 1) value)
  | .fix self body, depth, value => .fix self (body.substAt (depth + 1) value)

def Expr.subst1 (body value : Expr A) : Expr A := body.substAt 0 value

/-- The head of an application spine and its arguments, in order. -/
def Expr.spine : Expr A → Expr A × List (Expr A)
  | .app function argument =>
      let headArgs := function.spine
      (headArgs.1, headArgs.2 ++ [argument])
  | expr => (expr, [])

def Expr.apps (head : Expr A) (args : List (Expr A)) : Expr A :=
  args.foldl .app head

end EPL
