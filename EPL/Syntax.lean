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

/-- The built-in types: `Unit`, `Int`, `Char`. (`Bool` is not built in; it is
declaration 0 of the signature, see `boolDecl`.) -/
inductive PrimTy where
  | unit
  | int
  | char
  deriving DecidableEq, Repr

/-- Types, parametric in the flexible variables `V` (see `SemTy`, `InfTy`,
`Template`). For how declared types like `List Int` are written, see
`DataConst`. -/
inductive Ty (V : Type) where
  /-- A built-in type: `Unit`, `Int` or `Char`. -/
  | prim (name : PrimTy)
  /-- The function type `domain -> codomain`. -/
  | arrow (domain codomain : Ty V)
  /-- Declared data type number `id` of the program's signature, unapplied: if
  `List` is declaration 1, then `List` is `.con 1` and `List Int` is
  `.app (.con 1) (.prim .int)`. -/
  | con (id : Nat)
  /-- Type application: `T a b` is `.app (.app T a) b`. Kinds are not checked:
  an ill-kinded application is a type without values. -/
  | app (function argument : Ty V)
  /-- Binder `index` of the enclosing `Scheme`, or parameter `index` of the
  enclosing `DataDecl`. Occurs only in scheme bodies and field types. -/
  | bvar (index : Nat)
  /-- A type variable in scope (a skolem), by level: the outermost enclosing
  written binder is `rigid 0`. -/
  | rigid (level : Nat)
  /-- A flexible variable: none in `SemTy`, a metavariable `?v` in `InfTy`, a
  named hole in `Template`. -/
  | var (v : V)
  deriving DecidableEq, Repr

/-- Declarative types: no flexible variables, by construction. -/
abbrev SemTy := Ty Empty
/-- Types during inference: `var id` is metavariable `?id`. -/
abbrev InfTy := Ty Nat
/-- Partial type annotations, as written: `var name` is a named hole (the
surface `_` is a hole with a fresh name). -/
abbrev Template := Ty String

/-! ## The one substitution -/

/-- What to put in place of each kind of variable. -/
structure Ty.Subst (V W : Type) where
  bvar : Nat → Ty W
  rigid : Nat → Ty W
  var : V → Ty W

/-- Replace every variable as `σ` says. Every other variable-replacing
operation on types is an instance of this one. -/
def Ty.subst (σ : Ty.Subst V W) : Ty V → Ty W
  | .prim name => .prim name
  | .arrow domain codomain => .arrow (domain.subst σ) (codomain.subst σ)
  | .con id => .con id
  | .app function argument => .app (function.subst σ) (argument.subst σ)
  | .bvar index => σ.bvar index
  | .rigid level => σ.rigid level
  | .var v => σ.var v

/-- The substitution that leaves every variable as it is. -/
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

/-- The number of nodes. A termination measure for unification. -/
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

/-- `Ty.Scoped` is decidable, by recursion on the type. -/
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

/-- A type as a scheme with no binders. -/
def Scheme.mono (ty : Ty V) : Scheme V := ⟨0, ty⟩

/-- The instance at `args`: binder `i` becomes `args[i]`. -/
def Scheme.inst (scheme : Scheme V) (args : List (Ty V)) : Ty V :=
  scheme.body.instantiate args

/-- The generic instance at rigid depth `k`: binders become levels
`k, ..., k + arity - 1`. -/
def Scheme.skolemize (scheme : Scheme V) (k : Nat) : Ty V :=
  scheme.inst (rigidBlock k scheme.arity)

/-- `Ty.bind` on the body: replace flexible variables. -/
def Scheme.bind (scheme : Scheme V) (f : V → Ty W) : Scheme W :=
  ⟨scheme.arity, scheme.body.bind f⟩

/-- `Ty.lift` on the body: a semantic scheme, seen at any variable type. -/
def Scheme.lift (scheme : Scheme Empty) : Scheme V :=
  ⟨scheme.arity, scheme.body.lift⟩

/-- `Ty.substRigids` on the body: replace rigid variables. -/
def Scheme.substRigids (f : Nat → Ty V) (scheme : Scheme V) : Scheme V :=
  ⟨scheme.arity, scheme.body.substRigids f⟩

/-- A scheme at rigid depth `k`: rigid levels below `k`, bound indices below
the arity. -/
abbrev Scheme.WF (k : Nat) (scheme : Scheme V) : Prop := scheme.body.Scoped k scheme.arity

/-- `ty` is an instance of `scheme` by arguments well-formed at depth `k`. -/
def Scheme.Instance (k : Nat) (scheme : Scheme V) (ty : Ty V) : Prop :=
  ∃ args : List (Ty V), args.length = scheme.arity ∧ (∀ arg ∈ args, arg.WF k) ∧
    scheme.inst args = ty

/-- A typing context: entry `i` is the scheme of term variable `var i`, so the
innermost binder comes first. -/
abbrev Ctx (V : Type) := List (Scheme V)

/-- Every scheme in the context is well formed at depth `k`. -/
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

/-- A constructor declaration: `existentials` type variables of its own, and
its field types. In a field type, `bvar 0 ... bvar (params - 1)` are the data
type's parameters and `bvar params ... bvar (params + existentials - 1)` are
the constructor's own variables.

The constructor's own variables do not occur in the type it constructs, so
they are *existential*: building a value may pick any types for them, and a
match that takes the value apart learns only that there are some such types
(see the `match` rule of `TypingWith`). In
`type AnyDb = {w} MkAnyDb (Db w)`, with `Db` declaration `d`, `MkAnyDb` is
`⟨1, [.app (.con d) (.bvar 0)]⟩` and has the scheme `forall w. Db w -> AnyDb`. -/
structure CtorDecl where
  existentials : Nat
  fields : List SemTy
  deriving DecidableEq, Repr

/-- A constructor without variables of its own. -/
def CtorDecl.plain (fields : List SemTy) : CtorDecl := ⟨0, fields⟩

/-- A data type with `params` type parameters and its constructors. Field
types may name any declared type, so recursion and mutual recursion are
allowed.

If `List` is declaration 1, `data List a = Nil | Cons a (List a)` is
`⟨1, [.plain [], .plain [.bvar 0, .app (.con 1) (.bvar 0)]]⟩`. See `CtorRef`
for more. -/
structure DataDecl where
  params : Nat
  ctors : List CtorDecl
  deriving DecidableEq, Repr

/-- A program's data declarations: type `con i` is declaration `i`. -/
abbrev Signature := List DataDecl

/-- A resolved constructor name: constructor number `index` of declared type
`type`. Used both to build values (`Expr.ctor`) and as a match pattern
(`Expr.match`). Names are resolved before the core, so a constructor always
says which type it belongs to.

A constructor names a *value*. A *type* is named by its declaration's number,
`Ty.con`, applied to arguments with `Ty.app`. A worked example: the signature

```
[ ⟨0, [.plain [], .plain []]⟩,                  -- 0: data Bool     = True | False
  ⟨1, [.plain [],
       .plain [.bvar 0, .app (.con 1) (.bvar 0)]]⟩, -- 1: data List a = Nil | Cons a (List a)
  ⟨1, [.plain [], .plain [.bvar 0]]⟩,           -- 2: data Maybe a  = Nothing | Just a
  ⟨2, [.plain [.bvar 0, .bvar 1]]⟩,             -- 3: data Pair a b = MkPair a b
  ⟨1, [⟨1, [.bvar 1, .arrow (.bvar 1) (.bvar 0)]⟩]⟩ ] -- 4: data Pack a = {s} MkPack s (s -> a)
```

declares these types:

| written            | `Ty`                                              |
|--------------------|---------------------------------------------------|
| `Bool`             | `.con 0`                                          |
| `List Int`         | `.app (.con 1) (.prim .int)`                      |
| `List (List Bool)` | `.app (.con 1) (.app (.con 1) (.con 0))`          |
| `Maybe a`          | `.app (.con 2) (.rigid 0)` (`a` at level 0)       |
| `Pair Int Char`    | `.app (.app (.con 3) (.prim .int)) (.prim .char)` |

and these constructors (numbered from 0 in declaration order;
`Signature.ctorScheme` gives the schemes):

| written  | `CtorRef` | scheme                            |
|----------|-----------|-----------------------------------|
| `True`   | `⟨0, 0⟩`  | `Bool`                            |
| `False`  | `⟨0, 1⟩`  | `Bool`                            |
| `Nil`    | `⟨1, 0⟩`  | `forall a. List a`                |
| `Cons`   | `⟨1, 1⟩`  | `forall a. a -> List a -> List a` |
| `Just`   | `⟨2, 1⟩`  | `forall a. a -> Maybe a`          |
| `MkPair` | `⟨3, 0⟩`  | `forall a b. a -> b -> Pair a b`  |
| `MkPack` | `⟨4, 0⟩`  | `forall a s. s -> (s -> a) -> Pack a` |

So `Cons 3 Nil : List Int` is
`.app (.app (.ctor ⟨1, 1⟩) (.lit (.int 3))) (.ctor ⟨1, 0⟩)`, and
`match xs with | Nil => a | Cons h t => b` is
`.match xs [(⟨1, 0⟩, a), (⟨1, 1⟩, .lambda none (.lambda none b))]`.

By convention declaration 0 is always `Bool` (`boolDecl`); the comparison
operators rely on it. -/
structure CtorRef where
  type : Nat
  index : Nat
  deriving DecidableEq, Repr

/-! ## Expressions -/

/-- Literals of the built-in types: `()`, integers, characters. -/
inductive PrimLit where
  | unit
  | int (value : Int)
  | char (value : Char)
  deriving DecidableEq, Repr

/-- Built-in operators, all curried and binary. The comparisons return `Bool`
(declaration 0). -/
inductive PrimOp where
  /-- E.g. `1 + 2`. -/
  | intAdd
  /-- E.g. `1 - 2`. -/
  | intSub
  /-- E.g. `1 < 2`. -/
  | intLt
  /-- E.g. `'a' < 'b'`. -/
  | charLt
  deriving DecidableEq, Repr

/-- A polymorphic let's annotation `forall (arity binders). body`. Unlike a
`Scheme`, the body names its binders by rigid level: at depth `k` they are
`rigid k, ..., rigid (k + arity - 1)`. -/
structure PolyAnn (A : Type) where
  arity : Nat
  body : A
  deriving DecidableEq, Repr

/-- Map the body, keeping the arity. -/
def PolyAnn.map (f : A → B) (ann : PolyAnn A) : PolyAnn B := ⟨ann.arity, f ann.body⟩

/-- Expressions, parametric in the annotation type `A`:
* `Source := Expr Template` — what the programmer wrote;
* `Elab := Expr SemTy` — the same program with every implicit type filled in
  (every annotation is `some`);
* `RuntimeExpr := Expr Empty` — after erasure (every annotation is `none`).

`Expr` is a nested inductive (a match holds a `List` of branches), so every
recursive function on it comes with a companion on branch lists, defined in
the same `mutual` block. -/
inductive Expr (A : Type) where
  /-- A literal: `()`, an integer or a character. -/
  | lit (literal : PrimLit)
  /-- A built-in operator, unapplied: `x + y` is
  `.app (.app (.primOp .intAdd) x) y`. -/
  | primOp (op : PrimOp)
  /-- A data constructor, unapplied: it takes its fields by `.app`, like
  `Ty.con` takes its arguments by `Ty.app`. See `CtorRef`. -/
  | ctor (ref : CtorRef)
  /-- A term variable, by de Bruijn index: `var 0` is the innermost binder. -/
  | var (index : Nat)
  /-- `fun x => body`, with `param` the optional type annotation on `x`. In
  `body`, `x` is `var 0`. -/
  | lambda (param : Option A) (body : Expr A)
  /-- Application `function argument`. -/
  | app (function argument : Expr A)
  /-- `let x = rhs in body` (not recursive: `x` is `var 0` in `body` only).
  `none`: a monomorphic let. `some ann`: a let with an explicit scheme; its
  right-hand side is one rigid depth level per binder deeper. -/
  | letIn (ann : Option (PolyAnn A)) (rhs body : Expr A)
  /-- `fix self => body`, monomorphic recursion: in `body`, `self` is `var 0`
  and stands for the whole `fix`. `self` annotates the recursive binder, as
  `param` does a lambda's. -/
  | fix (self : Option A) (body : Expr A)
  /-- `match scrutinee with | pattern => body | ...`. Each branch names the
  constructor it matches; the first branch whose pattern is the scrutinee's
  constructor is taken. A branch body is a function of the constructor's
  fields (`fun h t => b` for `Cons h t => b`; just `b` for a constructor
  without fields), so patterns bind nothing themselves. Matches may be
  partial (see `Exhaustive`). -/
  | «match» (scrutinee : Expr A) (branches : List (CtorRef × Expr A))
  deriving Repr

/-- Structural induction on `Expr`, with a hypothesis for every branch body of
a `match` (the generated `Expr.rec` splits branches into separate list and
pair motives). It is the default eliminator, so a plain `induction expr`
uses it; `@[elab_as_elim]` lets it be applied directly as a term. -/
@[elab_as_elim, induction_eliminator]
theorem Expr.induction {A : Type} {motive : Expr A → Prop}
    (lit : ∀ literal, motive (.lit literal))
    (primOp : ∀ op, motive (.primOp op))
    (ctor : ∀ ref, motive (.ctor ref))
    (var : ∀ index, motive (.var index))
    (lambda : ∀ param body, motive body → motive (.lambda param body))
    (app : ∀ function argument, motive function → motive argument →
      motive (.app function argument))
    (letIn : ∀ ann rhs body, motive rhs → motive body → motive (.letIn ann rhs body))
    (fix : ∀ self body, motive body → motive (.fix self body))
    («match» : ∀ scrutinee branches, motive scrutinee →
      (∀ branch ∈ branches, motive branch.2) → motive (.match scrutinee branches))
    (expr : Expr A) : motive expr :=
  Expr.rec (motive_1 := motive)
    (motive_2 := fun branches => ∀ branch ∈ branches, motive branch.2)
    (motive_3 := fun branch => motive branch.2)
    lit primOp ctor var lambda app letIn fix «match»
    (fun _ mem => nomatch mem)
    (fun _ _ head tail branch mem => by
      cases mem with
      | head => exact head
      | tail _ mem => exact tail branch mem)
    (fun _ _ body => body)
    expr

/-- Programs as written: annotations are partial (`Template`s). -/
abbrev Source := Expr Template
/-- Elaborated programs: every annotation present and complete. -/
abbrev Elab := Expr SemTy
/-- Erased programs, what evaluation runs: no annotations at all. -/
abbrev RuntimeExpr := Expr Empty

mutual
/-- Decidable equality (`deriving` does not handle nested inductives). -/
def Expr.decEq [DecidableEq A] : (x y : Expr A) → Decidable (x = y)
  | .lit l, .lit l' =>
      if h : l = l' then isTrue (h ▸ rfl) else isFalse (by intro e; cases e; exact h rfl)
  | .primOp o, .primOp o' =>
      if h : o = o' then isTrue (h ▸ rfl) else isFalse (by intro e; cases e; exact h rfl)
  | .ctor r, .ctor r' =>
      if h : r = r' then isTrue (h ▸ rfl) else isFalse (by intro e; cases e; exact h rfl)
  | .var i, .var i' =>
      if h : i = i' then isTrue (h ▸ rfl) else isFalse (by intro e; cases e; exact h rfl)
  | .lambda p b, .lambda p' b' =>
      if hp : p = p' then
        match Expr.decEq b b' with
        | isTrue hb => isTrue (hp ▸ hb ▸ rfl)
        | isFalse hb => isFalse (by intro e; cases e; exact hb rfl)
      else isFalse (by intro e; cases e; exact hp rfl)
  | .app f a, .app f' a' =>
      match Expr.decEq f f', Expr.decEq a a' with
      | isTrue hf, isTrue ha => isTrue (hf ▸ ha ▸ rfl)
      | isFalse hf, _ => isFalse (by intro e; cases e; exact hf rfl)
      | _, isFalse ha => isFalse (by intro e; cases e; exact ha rfl)
  | .letIn n r b, .letIn n' r' b' =>
      if hn : n = n' then
        match Expr.decEq r r', Expr.decEq b b' with
        | isTrue hr, isTrue hb => isTrue (hn ▸ hr ▸ hb ▸ rfl)
        | isFalse hr, _ => isFalse (by intro e; cases e; exact hr rfl)
        | _, isFalse hb => isFalse (by intro e; cases e; exact hb rfl)
      else isFalse (by intro e; cases e; exact hn rfl)
  | .fix s b, .fix s' b' =>
      if hs : s = s' then
        match Expr.decEq b b' with
        | isTrue hb => isTrue (hs ▸ hb ▸ rfl)
        | isFalse hb => isFalse (by intro e; cases e; exact hb rfl)
      else isFalse (by intro e; cases e; exact hs rfl)
  | .match s bs, .match s' bs' =>
      match Expr.decEq s s', Expr.decEqBranches bs bs' with
      | isTrue hs, isTrue hb => isTrue (hs ▸ hb ▸ rfl)
      | isFalse hs, _ => isFalse (by intro e; cases e; exact hs rfl)
      | _, isFalse hb => isFalse (by intro e; cases e; exact hb rfl)
  | .lit .., .primOp .. | .lit .., .ctor .. | .lit .., .var .. | .lit .., .lambda ..
  | .lit .., .app .. | .lit .., .letIn .. | .lit .., .fix .. | .lit .., .match ..
  | .primOp .., .lit .. | .primOp .., .ctor .. | .primOp .., .var .. | .primOp .., .lambda ..
  | .primOp .., .app .. | .primOp .., .letIn .. | .primOp .., .fix .. | .primOp .., .match ..
  | .ctor .., .lit .. | .ctor .., .primOp .. | .ctor .., .var .. | .ctor .., .lambda ..
  | .ctor .., .app .. | .ctor .., .letIn .. | .ctor .., .fix .. | .ctor .., .match ..
  | .var .., .lit .. | .var .., .primOp .. | .var .., .ctor .. | .var .., .lambda ..
  | .var .., .app .. | .var .., .letIn .. | .var .., .fix .. | .var .., .match ..
  | .lambda .., .lit .. | .lambda .., .primOp .. | .lambda .., .ctor .. | .lambda .., .var ..
  | .lambda .., .app .. | .lambda .., .letIn .. | .lambda .., .fix .. | .lambda .., .match ..
  | .app .., .lit .. | .app .., .primOp .. | .app .., .ctor .. | .app .., .var ..
  | .app .., .lambda .. | .app .., .letIn .. | .app .., .fix .. | .app .., .match ..
  | .letIn .., .lit .. | .letIn .., .primOp .. | .letIn .., .ctor .. | .letIn .., .var ..
  | .letIn .., .lambda .. | .letIn .., .app .. | .letIn .., .fix .. | .letIn .., .match ..
  | .fix .., .lit .. | .fix .., .primOp .. | .fix .., .ctor .. | .fix .., .var ..
  | .fix .., .lambda .. | .fix .., .app .. | .fix .., .letIn .. | .fix .., .match ..
  | .match .., .lit .. | .match .., .primOp .. | .match .., .ctor .. | .match .., .var ..
  | .match .., .lambda .. | .match .., .app .. | .match .., .letIn .. | .match .., .fix .. =>
      isFalse (by intro e; cases e)

/-- Decidable equality of branch lists. -/
def Expr.decEqBranches [DecidableEq A] :
    (x y : List (CtorRef × Expr A)) → Decidable (x = y)
  | [], [] => isTrue rfl
  | (p, b) :: bs, (p', b') :: bs' =>
      if hp : p = p' then
        match Expr.decEq b b', Expr.decEqBranches bs bs' with
        | isTrue hb, isTrue hbs => isTrue (hp ▸ hb ▸ hbs ▸ rfl)
        | isFalse hb, _ => isFalse (by intro e; cases e; exact hb rfl)
        | _, isFalse hbs => isFalse (by intro e; cases e; exact hbs rfl)
      else isFalse (by intro e; cases e; exact hp rfl)
  | [], _ :: _ | _ :: _, [] => isFalse (by intro e; cases e)
end

instance [DecidableEq A] : DecidableEq (Expr A) := Expr.decEq

mutual
/-- Map every annotation. -/
def Expr.mapAnn (f : A → B) : Expr A → Expr B
  | .lit literal => .lit literal
  | .primOp op => .primOp op
  | .ctor ref => .ctor ref
  | .var index => .var index
  | .lambda param body => .lambda (param.map f) (body.mapAnn f)
  | .app function argument => .app (function.mapAnn f) (argument.mapAnn f)
  | .letIn ann rhs body => .letIn (ann.map (PolyAnn.map f)) (rhs.mapAnn f) (body.mapAnn f)
  | .fix self body => .fix (self.map f) (body.mapAnn f)
  | .match scrutinee branches => .match (scrutinee.mapAnn f) (Expr.mapAnnBranches f branches)

/-- `Expr.mapAnn` on every branch body. -/
def Expr.mapAnnBranches (f : A → B) : List (CtorRef × Expr A) → List (CtorRef × Expr B)
  | [] => []
  | (pattern, body) :: rest => (pattern, body.mapAnn f) :: Expr.mapAnnBranches f rest
end

mutual
/-- Map every annotation, failing if any annotation fails. -/
def Expr.traverseAnn (f : A → Option B) : Expr A → Option (Expr B)
  | .lit literal => some (.lit literal)
  | .primOp op => some (.primOp op)
  | .ctor ref => some (.ctor ref)
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
  | .match scrutinee branches => do
      some (.match (← scrutinee.traverseAnn f) (← Expr.traverseAnnBranches f branches))

/-- `Expr.traverseAnn` on every branch body. -/
def Expr.traverseAnnBranches (f : A → Option B) :
    List (CtorRef × Expr A) → Option (List (CtorRef × Expr B))
  | [] => some []
  | (pattern, body) :: rest => do
      some ((pattern, ← body.traverseAnn f) :: (← Expr.traverseAnnBranches f rest))
end

mutual
/-- Every annotation of an expression, in order. -/
def Expr.anns : Expr A → List A
  | .lit _ | .primOp _ | .ctor _ | .var _ => []
  | .lambda none body => body.anns
  | .lambda (some param) body => param :: body.anns
  | .app function argument => function.anns ++ argument.anns
  | .letIn none rhs body => rhs.anns ++ body.anns
  | .letIn (some ann) rhs body => ann.body :: (rhs.anns ++ body.anns)
  | .fix none body => body.anns
  | .fix (some self) body => self :: body.anns
  | .match scrutinee branches => scrutinee.anns ++ Expr.annsBranches branches

/-- Every annotation of the branch bodies, in order. -/
def Expr.annsBranches : List (CtorRef × Expr A) → List A
  | [] => []
  | (_, body) :: rest => body.anns ++ Expr.annsBranches rest
end

mutual
/-- Forget every annotation. A source program and its elaboration erase to the
same runtime expression. -/
def Expr.erase : Expr A → RuntimeExpr
  | .lit literal => .lit literal
  | .primOp op => .primOp op
  | .ctor ref => .ctor ref
  | .var index => .var index
  | .lambda _ body => .lambda none body.erase
  | .app function argument => .app function.erase argument.erase
  | .letIn _ rhs body => .letIn none rhs.erase body.erase
  | .fix _ body => .fix none body.erase
  | .match scrutinee branches => .match scrutinee.erase (Expr.eraseBranches branches)

/-- `Expr.erase` on every branch body. -/
def Expr.eraseBranches : List (CtorRef × Expr A) → List (CtorRef × RuntimeExpr)
  | [] => []
  | (pattern, body) :: rest => (pattern, body.erase) :: Expr.eraseBranches rest
end

mutual
/-- Add `amount` to every term variable at or above `cutoff`. -/
def Expr.shift (cutoff amount : Nat) : Expr A → Expr A
  | .lit literal => .lit literal
  | .primOp op => .primOp op
  | .ctor ref => .ctor ref
  | .var index => .var (if cutoff ≤ index then index + amount else index)
  | .lambda param body => .lambda param (body.shift (cutoff + 1) amount)
  | .app function argument => .app (function.shift cutoff amount) (argument.shift cutoff amount)
  | .letIn ann rhs body => .letIn ann (rhs.shift cutoff amount) (body.shift (cutoff + 1) amount)
  | .fix self body => .fix self (body.shift (cutoff + 1) amount)
  | .match scrutinee branches =>
      .match (scrutinee.shift cutoff amount) (Expr.shiftBranches cutoff amount branches)

/-- `Expr.shift` on every branch body. Patterns bind nothing, so the cutoff is
unchanged. -/
def Expr.shiftBranches (cutoff amount : Nat) :
    List (CtorRef × Expr A) → List (CtorRef × Expr A)
  | [] => []
  | (pattern, body) :: rest =>
      (pattern, body.shift cutoff amount) :: Expr.shiftBranches cutoff amount rest
end

mutual
/-- Replace term variable `depth` by `value` (whose free variables are relative
to the outside of `depth` binders) and close the gap. -/
def Expr.substAt : Expr A → Nat → Expr A → Expr A
  | .lit literal, _, _ => .lit literal
  | .primOp op, _, _ => .primOp op
  | .ctor ref, _, _ => .ctor ref
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
  | .match scrutinee branches, depth, value =>
      .match (scrutinee.substAt depth value) (Expr.substAtBranches branches depth value)

/-- `Expr.substAt` on every branch body. -/
def Expr.substAtBranches :
    List (CtorRef × Expr A) → Nat → Expr A → List (CtorRef × Expr A)
  | [], _, _ => []
  | (pattern, body) :: rest, depth, value =>
      (pattern, body.substAt depth value) :: Expr.substAtBranches rest depth value
end

/-- Replace the innermost bound variable `var 0` by `value`: `body[value/x]`
for the body of a binder `x`, as in beta reduction. -/
def Expr.subst1 (body value : Expr A) : Expr A := body.substAt 0 value

/-- The head of an application spine and its arguments, in order. -/
def Expr.spine : Expr A → Expr A × List (Expr A)
  | .app function argument =>
      let headArgs := function.spine
      (headArgs.1, headArgs.2 ++ [argument])
  | expr => (expr, [])

/-- Apply `head` to `args` in order: `head a b c`. Inverse of `Expr.spine`. -/
def Expr.apps (head : Expr A) (args : List (Expr A)) : Expr A :=
  args.foldl .app head

/-- The first branch whose pattern is `ref`. -/
def Expr.findBranch (ref : CtorRef) (branches : List (CtorRef × Expr A)) : Option (Expr A) :=
  (branches.find? (·.1 == ref)).map (·.2)

end EPL
