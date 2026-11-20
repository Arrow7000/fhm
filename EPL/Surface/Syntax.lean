/-!
# EPL surface syntax

The language as written, in FHM's syntax: named variables, constructors and
types, function heads with `{a b}` type parameters, nested patterns, and sugar
for `if`, operators, pairs, lists and strings. Every node carries its source
span. `EPL.Surface.Lower` translates a `Program` into a core `Source` term and
its `Signature`.

Lowercase names are term or type variables; uppercase names are constructors
or types. The prelude declares `Bool`, `List` and `Pair` (see
`EPL.Surface.Lower`).
-/

namespace EPL.Surface

/-- A source position: 1-based line and column (counted in characters). -/
structure Pos where
  line : Nat
  col : Nat
  deriving DecidableEq, Repr, Inhabited

/-- The source text from `start` up to (not including) `stop`. -/
structure Span where
  start : Pos
  stop : Pos
  deriving DecidableEq, Repr, Inhabited

/-- From the start of `first` to the end of `last`. -/
def Span.union (first last : Span) : Span := ⟨first.start, last.stop⟩

/-- Types as written. -/
inductive Ty where
  /-- `_`: a type to infer, independent of every other `_`. -/
  | hole (span : Span)
  /-- `?a`: a type to infer, shared by every `?a` of the same signature. -/
  | namedHole (span : Span) (name : String)
  /-- A type variable, bound by an enclosing `{a ...}` or by a data
  declaration's parameters. -/
  | var (span : Span) (name : String)
  /-- A built-in (`Int`, `Char`, `Unit`) or declared type, applied to
  arguments. -/
  | con (span : Span) (name : String) (args : List Ty)
  /-- `()`, the unit type. -/
  | unit (span : Span)
  /-- `(a, b)`, the prelude's `Pair a b`. -/
  | pair (span : Span) (fst snd : Ty)
  | arrow (span : Span) (domain codomain : Ty)
  deriving Repr, Inhabited

def Ty.span : Ty → Span
  | .hole span | .namedHole span _ | .var span _ | .con span _ _ | .unit span
  | .pair span _ _ | .arrow span _ _ => span

/-- A signature as written: `{a b} ty`, or just `ty`. -/
structure PolyTy where
  binders : List String
  body : Ty
  /-- Where each binder is written. -/
  binderSpans : List Span := []
  deriving Repr, Inhabited

/-- Patterns, possibly nested. -/
inductive Pattern where
  /-- `_` -/
  | wildcard (span : Span)
  /-- A lowercase name: matches anything and binds it. -/
  | var (span : Span) (name : String)
  /-- A constructor and one pattern per field, e.g. `Just x` or `True`. -/
  | ctor (span : Span) (name : String) (args : List Pattern)
  /-- `(p, q)` -/
  | pair (span : Span) (fst snd : Pattern)
  /-- `p :: q`; `opSpan` is the `::`'s. -/
  | cons (span : Span) (opSpan : Span) (head tail : Pattern)
  /-- `[p, q, ...]` -/
  | list (span : Span) (items : List Pattern)
  deriving Repr, Inhabited

def Pattern.span : Pattern → Span
  | .wildcard span | .var span _ | .ctor span _ _ | .pair span _ _ | .cons span ..
  | .list span _ => span

mutual
/-- The names a pattern binds, left to right. -/
def Pattern.vars : Pattern → List String
  | .wildcard _ => []
  | .var _ name => [name]
  | .ctor _ _ args => Pattern.varsList args
  | .pair _ fst snd => fst.vars ++ snd.vars
  | .cons _ _ head tail => head.vars ++ tail.vars
  | .list _ items => Pattern.varsList items

def Pattern.varsList : List Pattern → List String
  | [] => []
  | pattern :: rest => pattern.vars ++ Pattern.varsList rest
end

/-- The infix operators. -/
inductive BinOp where
  /-- `+` on `Int` -/
  | add
  /-- `-` on `Int` -/
  | sub
  /-- `<` on `Int` -/
  | lt
  /-- `::`, the prelude's `Cons` -/
  | cons
  deriving DecidableEq, Repr, Inhabited

def BinOp.describe : BinOp → String
  | .add => "+" | .sub => "-" | .lt => "<" | .cons => "::"

/-- A lambda parameter: a pattern, optionally annotated: `x`, `(x : Int)`,
`(a, b)`, `((a, b) : (Int, Int))`. -/
structure Param where
  span : Span
  pattern : Pattern
  ann : Option Ty
  deriving Repr, Inhabited

/-- A parameter of a function head: `x`, `_`, `(x : ty)` or `(_ : ty)`. -/
structure ValueParam where
  span : Span
  /-- `none` for `_`. -/
  name : Option String
  ann : Option Ty
  /-- The span of the name (or `_`). -/
  nameSpan : Span
  deriving Repr, Inhabited

/-- What a `let` binds. -/
inductive Target where
  /-- A function head `f {a b} x (y : ty)`; with no parameters, just `f`. -/
  | named (name : String) (tyParams : List String) (params : List ValueParam)
      (nameSpan : Span)
  /-- A pattern, e.g. `(a, b)`. -/
  | pattern (pattern : Pattern)
  deriving Repr, Inhabited

/-- A `let` binding without its right-hand side. With a function head, `ann`
is the result type (`let f (x : Int) : Int = ...`); otherwise the type of the
whole right-hand side. -/
structure Binding where
  /-- From `let` (or the binding's first token) to `=`. -/
  span : Span
  target : Target
  ann : Option PolyTy
  /-- Where each of a function head's type parameters is written. -/
  tyParamSpans : List Span := []
  deriving Repr, Inhabited

/-- The names a binding defines. -/
def Binding.names (binding : Binding) : List String :=
  match binding.target with
  | .named name .. => [name]
  | .pattern pattern => pattern.vars

/-- Expressions as written. -/
inductive Expr where
  | int (span : Span) (value : Int)
  | char (span : Span) (value : Char)
  /-- A string literal: a `List Char`. -/
  | string (span : Span) (value : String)
  /-- `()` -/
  | unit (span : Span)
  | var (span : Span) (name : String)
  /-- A constructor, unapplied (`True`, `Just`, ...). -/
  | ctor (span : Span) (name : String)
  /-- `left op right`; `opSpan` is the operator's. -/
  | binOp (span : Span) (op : BinOp) (opSpan : Span) (left right : Expr)
  /-- `(a, b)` -/
  | pair (span : Span) (fst snd : Expr)
  /-- `[a, b, ...]` -/
  | list (span : Span) (items : List Expr)
  /-- `\p -> body`, one parameter (`\x y -> e` is two nested lambdas). -/
  | lambda (span : Span) (param : Param) (body : Expr)
  | app (span : Span) (function argument : Expr)
  /-- `let b1 = e1  b2 = e2 ... in body`. The bindings of one block may refer
  to each other in any order, and each to itself. -/
  | letIn (span : Span) (bindings : List (Binding × Expr)) (body : Expr)
  | ite (span : Span) (cond thenBranch elseBranch : Expr)
  | «match» (span : Span) (scrutinee : Expr) (arms : List (Pattern × Expr))
  deriving Repr, Inhabited

def Expr.span : Expr → Span
  | .int span _ | .char span _ | .string span _ | .unit span | .var span _ | .ctor span _
  | .binOp span .. | .pair span _ _ | .list span _ | .lambda span _ _ | .app span _ _
  | .letIn span _ _ | .ite span _ _ _ | .match span _ _ => span

/-- A constructor declaration `C field ...`. Its span starts at its name. -/
structure CtorDecl where
  span : Span
  name : String
  fields : List Ty
  deriving Repr, Inhabited

/-- `type T a b = C1 fields | C2 fields | ...` -/
structure DataDecl where
  span : Span
  name : String
  params : List String
  ctors : List CtorDecl
  nameSpan : Span := default
  /-- Where each parameter is written. -/
  paramSpans : List Span := []
  deriving Repr, Inhabited

/-- A program: data declarations, top-level `let`s (in any order; they may
refer to each other), and the expression it evaluates (`()` if omitted). -/
structure Program where
  decls : List DataDecl
  bindings : List (Binding × Expr)
  body : Expr
  deriving Repr, Inhabited

/-! ## Free variables and size -/

/-- A right-hand side's free variables `free`, minus the binding's parameters. -/
def Binding.rhsFreeVars (binding : Binding) (free : List String) : List String :=
  match binding.target with
  | .named _ _ params _ =>
      let bound := params.filterMap (·.name)
      free.filter (· ∉ bound)
  | .pattern _ => free

mutual
/-- The free term variables, with repetition. -/
def Expr.freeVars : Expr → List String
  | .int .. | .char .. | .string .. | .unit _ | .ctor .. => []
  | .var _ name => [name]
  | .binOp _ _ _ left right => left.freeVars ++ right.freeVars
  | .pair _ fst snd => fst.freeVars ++ snd.freeVars
  | .list _ items => Expr.freeVarsList items
  | .lambda _ param body =>
      let bound := param.pattern.vars
      body.freeVars.filter (· ∉ bound)
  | .app _ function argument => function.freeVars ++ argument.freeVars
  | .letIn _ bindings body =>
      let bound := bindings.flatMap (·.1.names)
      (Expr.freeVarsBindings bindings ++ body.freeVars).filter (· ∉ bound)
  | .ite _ cond thenBranch elseBranch =>
      cond.freeVars ++ thenBranch.freeVars ++ elseBranch.freeVars
  | .match _ scrutinee arms => scrutinee.freeVars ++ Expr.freeVarsArms arms

def Expr.freeVarsList : List Expr → List String
  | [] => []
  | expr :: rest => expr.freeVars ++ Expr.freeVarsList rest

/-- The free variables of each right-hand side, minus its own parameters (but
not minus the block's names). -/
def Expr.freeVarsBindings : List (Binding × Expr) → List String
  | [] => []
  | (binding, rhs) :: rest => Binding.rhsFreeVars binding rhs.freeVars ++
      Expr.freeVarsBindings rest

def Expr.freeVarsArms : List (Pattern × Expr) → List String
  | [] => []
  | (pattern, body) :: rest =>
      let bound := pattern.vars
      body.freeVars.filter (· ∉ bound) ++ Expr.freeVarsArms rest
end

mutual
def Pattern.size : Pattern → Nat
  | .wildcard _ | .var .. => 1
  | .ctor _ _ args => Pattern.sizeList args + 1
  | .pair _ fst snd | .cons _ _ fst snd => fst.size + snd.size + 1
  | .list _ items => Pattern.sizeList items + 1

def Pattern.sizeList : List Pattern → Nat
  | [] => 0
  | pattern :: rest => pattern.size + Pattern.sizeList rest
end

mutual
/-- The number of nodes, counting patterns and parameters. Bounds the depth of
lowering. -/
def Expr.size : Expr → Nat
  | .int .. | .char .. | .string .. | .unit _ | .var .. | .ctor .. => 1
  | .binOp _ _ _ left right => left.size + right.size + 1
  | .pair _ fst snd => fst.size + snd.size + 1
  | .list _ items => Expr.sizeList items + 1
  | .lambda _ param body => param.pattern.size + body.size + 1
  | .app _ function argument => function.size + argument.size + 1
  | .letIn _ bindings body => Expr.sizeBindings bindings + body.size + 1
  | .ite _ cond thenBranch elseBranch => cond.size + thenBranch.size + elseBranch.size + 1
  | .match _ scrutinee arms => scrutinee.size + Expr.sizeArms arms + 1

def Expr.sizeList : List Expr → Nat
  | [] => 0
  | expr :: rest => expr.size + Expr.sizeList rest

def Expr.sizeBindings : List (Binding × Expr) → Nat
  | [] => 0
  | (binding, rhs) :: rest =>
      let head := match binding.target with
        | .named _ _ params _ => params.length
        | .pattern pattern => pattern.size
      head + rhs.size + 1 + Expr.sizeBindings rest

def Expr.sizeArms : List (Pattern × Expr) → Nat
  | [] => 0
  | (pattern, body) :: rest => pattern.size + body.size + 1 + Expr.sizeArms rest
end

end EPL.Surface
