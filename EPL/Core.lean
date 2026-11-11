import Mathlib.Data.List.Dedup

namespace EPL

inductive PrimTy where
  | unit
  | int
  | bool
  deriving DecidableEq, Repr

/-- Semantic type variables and inference metavariables are different
constructors. Declarative well-formedness excludes `meta`. -/
inductive Ty where
  | prim (name : PrimTy)
  | arrow (domain codomain : Ty)
  | bvar (index : Nat)
  | rigid (level : Nat)
  | mvar (id : Nat)
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

/-- A semantic type contains no flexible inference metavariables. -/
inductive Ty.MetaFree : Ty → Prop
  | prim : Ty.MetaFree (.prim p)
  | arrow :
      Ty.MetaFree domain → Ty.MetaFree codomain →
      Ty.MetaFree (.arrow domain codomain)
  | bvar : Ty.MetaFree (.bvar index)
  | rigid : Ty.MetaFree (.rigid level)

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

/-- Partial annotations. Named-hole scope is one `Template.Matches` witness. -/
inductive Template where
  | fixed (ty : Ty)
  | hole
  | named (name : String)
  | arrow (domain codomain : Template)
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

/-- A written scheme matches exactly the completed scheme's binder count. -/
structure SchemeTemplateMatches (written : Scheme Template)
    (completed : PolyTy) : Prop where
  paramCount_eq : completed.paramCount = written.paramCount
  body_matches : written.body.Matches completed.body

inductive PrimLit where
  | unit
  | int (value : Int)
  | bool (value : Bool)
  deriving DecidableEq, Repr

inductive PrimOp where
  | intAdd
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
  deriving DecidableEq, Repr

abbrev Source := Expr Template
abbrev RuntimeExpr := Expr Unit
abbrev Ctx := List PolyTy

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

def Expr.erase : Source → RuntimeExpr
  | .primLit lit => .primLit lit
  | .primOp op => .primOp op
  | .var index => .var index
  | .lambda _ body => .lambda none body.erase
  | .app function argument => .app function.erase argument.erase
  | .letIn _ rhs body => .letIn none rhs.erase body.erase
  | .fix _ body => .fix () body.erase

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

def Expr.subst1 (expr : Expr T) (value : Expr T) : Expr T :=
  expr.substN 0 [value]

end EPL
