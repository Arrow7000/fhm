import Mathlib.Data.List.Dedup

namespace EPL

inductive PrimTy where
  | unit
  | int
  | nat
  | char
  deriving DecidableEq, Repr

/-- Semantic type variables and inference metavariables are different
constructors. Declarative well-formedness excludes `meta`. -/
inductive Ty where
  | prim (name : PrimTy)
  | arrow (domain codomain : Ty)
  | bvar (index : Nat)
  | rigid (level : Nat)
  | mvar (id : Nat)
  /-- A declared data type, by its index in the program's signature. -/
  | con (id : Nat)
  /-- Type application. Kinds are not checked: an ill-kinded application such
  as `Bool Int` is simply a type without values. -/
  | app (function argument : Ty)
  deriving DecidableEq, Repr

/-- A scheme body uses `bvar 0 ... bvar (paramCount - 1)`. -/
structure Scheme (T : Type) where
  paramCount : Nat
  body : T
  deriving DecidableEq, Repr

abbrev PolyTy := Scheme Ty

def Scheme.map (f : T → U) (scheme : Scheme T) : Scheme U :=
  ⟨scheme.paramCount, f scheme.body⟩

def PolyTy.mono (ty : Ty) : PolyTy := ⟨0, ty⟩

/-- Algorithmic scoping: bound and rigid variables are in range; metavariables
may occur. -/
inductive Ty.Scoped (rigidCount binderCount : Nat) : Ty → Prop
  | prim : Ty.Scoped rigidCount binderCount (.prim p)
  | arrow :
      Ty.Scoped rigidCount binderCount domain →
      Ty.Scoped rigidCount binderCount codomain →
      Ty.Scoped rigidCount binderCount (.arrow domain codomain)
  | bvar : index < binderCount → Ty.Scoped rigidCount binderCount (.bvar index)
  | rigid : level < rigidCount → Ty.Scoped rigidCount binderCount (.rigid level)
  | mvar (id : Nat) : Ty.Scoped rigidCount binderCount (.mvar id)
  | con (id : Nat) : Ty.Scoped rigidCount binderCount (.con id)
  | app :
      Ty.Scoped rigidCount binderCount function →
      Ty.Scoped rigidCount binderCount argument →
      Ty.Scoped rigidCount binderCount (.app function argument)

/-- A semantic type contains no flexible inference metavariables. -/
inductive Ty.MetaFree : Ty → Prop
  | prim : Ty.MetaFree (.prim p)
  | arrow :
      Ty.MetaFree domain → Ty.MetaFree codomain →
      Ty.MetaFree (.arrow domain codomain)
  | bvar : Ty.MetaFree (.bvar index)
  | rigid : Ty.MetaFree (.rigid level)
  | con : Ty.MetaFree (.con name)
  | app :
      Ty.MetaFree function → Ty.MetaFree argument →
      Ty.MetaFree (.app function argument)

/-- Declarative well-formedness. -/
def Ty.WF (rigidCount binderCount : Nat) (ty : Ty) : Prop :=
  ty.Scoped rigidCount binderCount ∧ ty.MetaFree

def PolyTy.WF (rigidCount : Nat) (scheme : PolyTy) : Prop :=
  scheme.body.WF rigidCount scheme.paramCount

/-- Replace scheme-bound variables. Out-of-range indices are retained so the
operation is total; well-formed schemes never exercise that case. -/
def Ty.openWith (args : List Ty) : Ty → Ty
  | .prim p => .prim p
  | .arrow a b => .arrow (a.openWith args) (b.openWith args)
  | .bvar i => (args[i]?).getD (.bvar i)
  | .rigid i => .rigid i
  | .mvar i => .mvar i
  | .con i => .con i
  | .app f a => .app (f.openWith args) (a.openWith args)

def PolyTy.openWith (scheme : PolyTy) (args : List Ty) : Ty :=
  scheme.body.openWith args

def rigidBlock (base count : Nat) : List Ty :=
  (List.range count).map fun offset => .rigid (base + offset)

def PolyTy.openRigids (scheme : PolyTy) (base : Nat) : Ty :=
  scheme.openWith (rigidBlock base scheme.paramCount)

/-- Open `count` binders starting beneath `depth` inner binders, replacing
them by rigid levels beginning at `base`. Indices beyond the removed block are
shifted down. -/
def Ty.openRigidsFrom (depth base count : Nat) : Ty → Ty
  | .prim p => .prim p
  | .arrow a b =>
      .arrow (a.openRigidsFrom depth base count)
        (b.openRigidsFrom depth base count)
  | .bvar i =>
      if i < depth then .bvar i
      else if i - depth < count then .rigid (base + (i - depth))
      else .bvar (i - count)
  | .rigid i => .rigid i
  | .mvar i => .mvar i
  | .con i => .con i
  | .app f a =>
      .app (f.openRigidsFrom depth base count)
        (a.openRigidsFrom depth base count)

/-- Partial annotations. Named-hole scope is one `Template.Matches` witness. -/
inductive Template where
  | fixed (ty : Ty)
  | hole
  | named (name : String)
  | arrow (domain codomain : Template)
  | app (function argument : Template)
  deriving DecidableEq, Repr
abbrev HoleAssignment := List (String × Ty)

def HoleAssignment.Unique (holes : HoleAssignment) : Prop :=
  (holes.map Prod.fst).Nodup

inductive Template.Fits (holes : HoleAssignment) : Template → Ty → Prop
  | fixed : Template.Fits holes (.fixed ty) ty
  | hole : Template.Fits holes .hole ty
  | named : holes.lookup name = some ty → Template.Fits holes (.named name) ty
  | arrow :
      Template.Fits holes domain domainTy →
      Template.Fits holes codomain codomainTy →
      Template.Fits holes (.arrow domain codomain) (.arrow domainTy codomainTy)
  | app :
      Template.Fits holes function functionTy →
      Template.Fits holes argument argumentTy →
      Template.Fits holes (.app function argument) (.app functionTy argumentTy)

def Template.Matches (template : Template) (ty : Ty) : Prop :=
  ∃ holes, holes.Unique ∧ template.Fits holes ty

abbrev ParamAnn := Option Template

def ParamAnn.Matches (ann : ParamAnn) (ty : Ty) : Prop :=
  ∀ template, ann = some template → template.Matches ty

def Template.openRigidsFrom (depth base count : Nat) : Template → Template
  | .fixed ty => .fixed (ty.openRigidsFrom depth base count)
  | .hole => .hole
  | .named name => .named name
  | .arrow a b =>
      .arrow (a.openRigidsFrom depth base count)
        (b.openRigidsFrom depth base count)
  | .app f a =>
      .app (f.openRigidsFrom depth base count)
        (a.openRigidsFrom depth base count)

/-- Source-annotation scope before a written scheme is opened. -/
inductive Template.Scoped (rigidCount binderCount : Nat) : Template → Prop
  | fixed : ty.WF rigidCount binderCount →
      Template.Scoped rigidCount binderCount (.fixed ty)
  | hole : Template.Scoped rigidCount binderCount .hole
  | named : Template.Scoped rigidCount binderCount (.named name)
  | arrow :
      Template.Scoped rigidCount binderCount domain →
      Template.Scoped rigidCount binderCount codomain →
      Template.Scoped rigidCount binderCount (.arrow domain codomain)
  | app :
      Template.Scoped rigidCount binderCount function →
      Template.Scoped rigidCount binderCount argument →
      Template.Scoped rigidCount binderCount (.app function argument)

/-- A written scheme matches exactly the completed scheme's binder count. -/
structure SchemeTemplateMatches (written : Scheme Template)
    (completed : PolyTy) : Prop where
  paramCount_eq : completed.paramCount = written.paramCount
  body_matches : written.body.Matches completed.body

inductive PrimLit where
  | unit
  | int (value : Int)
  | nat (value : Nat)
  | char (value : Char)
  deriving DecidableEq, Repr

/-- Built-in binary operators on primitive literals. Comparisons return the
declared type `Bool` (see `PrimOp.ty`). -/
inductive PrimOp where
  | intAdd
  | intSub
  | intLt
  | charLt
  deriving DecidableEq, Repr

/-- A data type declaration with `paramCount` type parameters and one list of
field types per constructor. Field types refer to the parameters as
`bvar 0 ... bvar (paramCount - 1)` and to declared types (including this one
and later ones, so recursion and mutual recursion are allowed) as `con`. -/
structure DataDecl where
  paramCount : Nat
  ctors : List (List Ty)
  deriving DecidableEq, Repr

/-- A program's data declarations: type `con i` is declaration `i`. -/
abbrev Signature := List DataDecl

/-- The constants a signature introduces. Arities are recorded so that the
erased runtime can evaluate without consulting the signature; typing checks
them against it.

@TODO Two simplifications to consider (deferred while data types land):
* Parameterise `Eval.Step`/`step?`/`Value` by the signature and drop the
  recorded arities (`arity`, `ctorCount`), which are then looked up.
* Number constructors globally across the signature (`ctor id`), so a
  constructor no longer names its type; typing looks up the owner. `elim`
  keeps its type, which nothing else determines.
* Comparison primitives currently find `Bool` by convention: declaration 0
  must be `True | False` (`Signature.HasBool`). The alternative is a
  signature that records Bool's index explicitly; the runtime would then
  need that index to produce `True`/`False`. -/
inductive DataConst where
  /-- Constructor number `ctor` of type `type`, which has `arity` fields. -/
  | ctor (type ctor arity : Nat)
  /-- The eliminator of type `type`, which has `ctorCount` constructors.
  Surface `match` and `if` are applications of an eliminator. -/
  | elim (type ctorCount : Nat)
  deriving DecidableEq, Repr

/-- One expression family for annotated source and erased runtime syntax. -/
inductive Expr (T : Type) where
  | primLit (literal : PrimLit)
  | primOp (op : PrimOp)
  | var (index : Nat)
  | lambda (paramAnn : Option T) (body : Expr T)
  | app (function argument : Expr T)
  | letIn (ann : Option (Scheme T)) (rhs body : Expr T)
  | fix (selfAnn : T) (body : Expr T)
  | const (c : DataConst)
  deriving DecidableEq, Repr

abbrev Source := Expr Template
abbrev RuntimeExpr := Expr Unit
abbrev Ctx := List PolyTy

/-- Map every type annotation of an elaborated expression. -/
def Expr.mapAnn (f : Ty → Ty) : Expr Ty → Expr Ty
  | .primLit lit => .primLit lit
  | .primOp op => .primOp op
  | .var index => .var index
  | .lambda paramTy body => .lambda (paramTy.map f) (body.mapAnn f)
  | .app function argument => .app (function.mapAnn f) (argument.mapAnn f)
  | .letIn scheme rhs body =>
      .letIn (scheme.map (Scheme.map f)) (rhs.mapAnn f) (body.mapAnn f)
  | .fix selfTy body => .fix (f selfTy) (body.mapAnn f)
  | .const c => .const c

/-- Every type annotation of an elaborated expression, in source order. -/
def Expr.annotations : Expr Ty → List Ty
  | .primLit _ | .primOp _ | .var _ | .const _ => []
  | .lambda paramTy body => paramTy.toList ++ body.annotations
  | .app function argument => function.annotations ++ argument.annotations
  | .letIn scheme rhs body =>
      (scheme.map Scheme.body).toList ++ rhs.annotations ++ body.annotations
  | .fix selfTy body => selfTy :: body.annotations

def Ctx.WF (rigidCount : Nat) (ctx : Ctx) : Prop :=
  ∀ scheme ∈ ctx, scheme.WF rigidCount

def Scheme.openTemplateRigidsFrom (depth base count : Nat)
    (scheme : Scheme Template) : Scheme Template :=
  ⟨scheme.paramCount,
    scheme.body.openRigidsFrom (depth + scheme.paramCount) base count⟩

/-- Open an enclosing written scheme inside all source annotations. A nested
written scheme protects its own binders in both its body and its RHS. -/
def Expr.openRigidsFrom (depth base count : Nat) : Source → Source
  | .primLit lit => .primLit lit
  | .primOp op => .primOp op
  | .var index => .var index
  | .lambda ann body =>
      .lambda (ann.map (Template.openRigidsFrom depth base count))
        (body.openRigidsFrom depth base count)
  | .app function argument =>
      .app (function.openRigidsFrom depth base count)
        (argument.openRigidsFrom depth base count)
  | .letIn ann rhs body =>
      let openedAnn := ann.map (Scheme.openTemplateRigidsFrom depth base count)
      let rhsDepth := depth + (ann.map Scheme.paramCount).getD 0
      .letIn openedAnn (rhs.openRigidsFrom rhsDepth base count)
        (body.openRigidsFrom depth base count)
  | .fix ann body =>
      .fix (ann.openRigidsFrom depth base count)
        (body.openRigidsFrom depth base count)
  | .const c => .const c

def Expr.openRigids (base count : Nat) (expr : Source) : Source :=
  expr.openRigidsFrom 0 base count

/-- Scope of authored types inside source annotations. `binderCount` counts
written scheme binders surrounding the current source position. Term-variable
scope is enforced separately by typing. -/
inductive Expr.TypeScoped (rigidCount : Nat) : Nat → Source → Prop
  | primLit : Expr.TypeScoped rigidCount binderCount (.primLit literal)
  | primOp : Expr.TypeScoped rigidCount binderCount (.primOp op)
  | var : Expr.TypeScoped rigidCount binderCount (.var index)
  | lambda :
      (∀ template, ann = some template → template.Scoped rigidCount binderCount) →
      body.TypeScoped rigidCount binderCount →
      Expr.TypeScoped rigidCount binderCount (.lambda ann body)
  | app :
      function.TypeScoped rigidCount binderCount →
      argument.TypeScoped rigidCount binderCount →
      Expr.TypeScoped rigidCount binderCount (.app function argument)
  | letMono :
      rhs.TypeScoped rigidCount binderCount →
      body.TypeScoped rigidCount binderCount →
      Expr.TypeScoped rigidCount binderCount (.letIn none rhs body)
  | letPoly :
      written.body.Scoped rigidCount (binderCount + written.paramCount) →
      rhs.TypeScoped rigidCount (binderCount + written.paramCount) →
      body.TypeScoped rigidCount binderCount →
      Expr.TypeScoped rigidCount binderCount (.letIn (some written) rhs body)
  | fix :
      ann.Scoped rigidCount binderCount →
      body.TypeScoped rigidCount binderCount →
      Expr.TypeScoped rigidCount binderCount (.fix ann body)
  | const : Expr.TypeScoped rigidCount binderCount (.const c)

def Expr.erase : Source → RuntimeExpr
  | .primLit lit => .primLit lit
  | .primOp op => .primOp op
  | .var index => .var index
  | .lambda _ body => .lambda none body.erase
  | .app function argument => .app function.erase argument.erase
  | .letIn _ rhs body => .letIn none rhs.erase body.erase
  | .fix _ body => .fix () body.erase
  | .const c => .const c

/-- Shift free term-variable indices at or above `threshold`. -/
def Expr.shiftFrom (threshold amount : Nat) : Expr T → Expr T
  | .primLit literal => .primLit literal
  | .primOp op => .primOp op
  | .var index => if threshold ≤ index then .var (index + amount) else .var index
  | .lambda ann body => .lambda ann (body.shiftFrom (threshold + 1) amount)
  | .app function argument =>
      .app (function.shiftFrom threshold amount) (argument.shiftFrom threshold amount)
  | .letIn ann rhs body =>
      .letIn ann (rhs.shiftFrom threshold amount)
        (body.shiftFrom (threshold + 1) amount)
  | .fix ann body => .fix ann (body.shiftFrom (threshold + 1) amount)
  | .const c => .const c

/-- Capture-avoiding simultaneous substitution of consecutive de Bruijn term
variables beginning at `depth`. -/
def Expr.substN (depth : Nat) (values : List (Expr T)) : Expr T → Expr T
  | .primLit literal => .primLit literal
  | .primOp op => .primOp op
  | .var index =>
      if index < depth then .var index
      else if h : index - depth < values.length then
        (values[index - depth]).shiftFrom 0 depth
      else .var (index - values.length)
  | .lambda ann body => .lambda ann (body.substN (depth + 1) values)
  | .app function argument =>
      .app (function.substN depth values) (argument.substN depth values)
  | .letIn ann rhs body =>
      .letIn ann (rhs.substN depth values) (body.substN (depth + 1) values)
  | .fix ann body => .fix ann (body.substN (depth + 1) values)
  | .const c => .const c

def Expr.subst1 (expr : Expr T) (value : Expr T) : Expr T :=
  expr.substN 0 [value]

end EPL
