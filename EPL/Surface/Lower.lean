import EPL.Infer
import EPL.Surface.Syntax

/-!
# Lowering

`lowerProgram` translates a surface `Program` to a core signature and a core
`Source` term, or reports the first problem with a typed `LowerError`.

* **Data.** The prelude declares `Bool` (declaration 0, as the core requires),
  `List` and `Pair`; user declarations follow, in order. Pairs, lists, strings,
  `::` and `if` are sugar for the prelude's constructors.
* **Names.** Term variables become de Bruijn indices, constructors `CtorRef`s,
  type names `Ty.con`s (checked against their arity), type variables rigid
  levels, and each `_` in an annotation a hole with a fresh name.
* **Bindings.** The bindings of a block (and the top level) may refer to each
  other in any order; they are sorted so that each comes after those it uses.
  Mutual recursion is rejected. A binding that mentions itself becomes a `fix`.
  A binding with any annotation (`{a}` binders, an annotated parameter, or a
  result type) becomes an explicit `let` whose signature is its head:
  `let f {a} (x : a) y : R = e` has signature `forall a. a -> _ -> R`. A
  binding without one is a monomorphic `let`.
* **Patterns.** Matches with nested patterns, wildcards and variables are
  compiled to nested core matches on one constructor at a time (a decision
  tree), splitting on the leftmost column whose first row is a constructor.
  An arm that no input reaches is rejected. A constructor no row covers is left
  out, so the core match is partial (and `evaluate` rejects the program); the
  lowering records where, for the error message.
* **Origins.** Alongside the term, lowering builds an `Origin` tree of the same
  shape that records each core node's source span, so an `InferError`'s path
  leads to a span.
-/

namespace EPL.Surface

/-! ## Origins -/

/-- Where the type of a core binder's variable is, given the binder node's
inferred type and its children's. -/
inductive BinderTy where
  /-- A lambda: the domain of the node's (function) type. -/
  | domain
  /-- A let: the type of its right-hand side, child 0. -/
  | rhs
  /-- A `fix`: the node's own type. -/
  | self
  deriving Repr, DecidableEq, Inhabited

/-- What a core node is in the source, for tools such as hover. -/
structure OriginInfo where
  /-- The node is the value of the surface expression at this span. -/
  expr : Option Span := none
  /-- The node is a use of this name, a value (`"val"`), a constructor
  (`"ctor"`) or an infix operator (`"op"`), written at the node's span. -/
  use : Option (String × String) := none
  /-- The binder id of the value a `"val"` use refers to. -/
  useBinder : Option Nat := none
  /-- The node binds the variable with this id (see `Scope.ids`). -/
  binder : Option (Nat × BinderTy) := none
  deriving Repr, Inhabited

/-- A core term's source spans: one node per core node, with a child per core
child (see `ExprStep.child`), the type variables in scope by name, and what
the node is in the source. -/
inductive Origin where
  | node (span : Span) (tyVars : List (String × Nat)) (children : List Origin)
      (info : OriginInfo := {})
  deriving Repr, Inhabited

def Origin.span : Origin → Span
  | .node span .. => span

def Origin.tyVars : Origin → List (String × Nat)
  | .node _ tyVars .. => tyVars

def Origin.children : Origin → List Origin
  | .node _ _ children _ => children

def Origin.info : Origin → OriginInfo
  | .node _ _ _ info => info

def Origin.mapInfo (f : OriginInfo → OriginInfo) : Origin → Origin
  | .node span tyVars children info => .node span tyVars children (f info)

/-- The child a step goes to, in `Origin.node`'s list: a match's scrutinee is
child 0 and branch `i` is child `i + 1`. -/
def _root_.EPL.ExprStep.child : ExprStep → Nat
  | .lambdaBody | .appFunction | .letRhs | .fixBody | .matchScrutinee => 0
  | .appArgument | .letBody => 1
  | .matchBranch index => index + 1

/-- The origin of the node at `path`. -/
def Origin.locate : Origin → List ExprStep → Origin
  | origin, [] => origin
  | origin@(.node _ _ children _), step :: path =>
      match children[step.child]? with
      | some child => child.locate path
      | none => origin

/-! ## Errors -/

inductive LowerErrorReason where
  | unboundVariable (name : String)
  | unknownConstructor (name : String)
  | unknownType (name : String)
  | unboundTypeVariable (name : String)
  /-- A type applied to the wrong number of arguments. -/
  | typeArity (name : String) (expected actual : Nat)
  /-- A constructor pattern with the wrong number of fields. -/
  | patternArity (name : String) (expected actual : Nat)
  /-- Constructor `ctor` where the other patterns are of type `type`. -/
  | foreignPattern (ctor type : String)
  /-- `_` or `?a` in a data declaration. -/
  | holeInDeclaration
  | duplicateType (name : String)
  | duplicateConstructor (name : String)
  | duplicateTypeParameter (name : String)
  | duplicatePatternVariable (name : String)
  /-- Two top-level bindings of the same name. -/
  | duplicateBinding (name : String)
  /-- These bindings refer to each other in a cycle. -/
  | mutualRecursion (names : List String)
  /-- A pattern binding whose right-hand side mentions these of its names. -/
  | recursivePattern (names : List String)
  /-- No input reaches this match arm: earlier arms cover it. -/
  | redundantArm
  /-- Unreachable: lowering always has enough fuel. -/
  | tooDeep
  deriving DecidableEq, Repr

structure LowerError where
  span : Span
  reason : LowerErrorReason
  deriving DecidableEq, Repr

/-! ## Declarations -/

/-- A declared type: its name, parameter count, and constructors' names and
field counts. -/
structure TypeInfo where
  name : String
  params : Nat
  ctors : List (String × Nat)
  deriving Repr, Inhabited

/-- The declared types; type `con i` is entry `i`. -/
structure Globals where
  types : List TypeInfo
  deriving Repr, Inhabited

def Globals.findType (globals : Globals) (name : String) : Option (Nat × TypeInfo) :=
  (globals.types.zipIdx.find? (·.1.name == name)).map fun (info, id) => (id, info)

/-- A constructor's reference and field count. -/
def Globals.findCtor (globals : Globals) (name : String) : Option (CtorRef × Nat) :=
  globals.types.zipIdx.findSome? fun (info, type) =>
    (info.ctors.zipIdx.find? (·.1.1 == name)).map fun ((_, arity), index) => (⟨type, index⟩, arity)

def Globals.typeName (globals : Globals) (type : Nat) : String :=
  ((globals.types[type]?).map (·.name)).getD s!"#{type}"

def Globals.ctorName (globals : Globals) (ref : CtorRef) : String :=
  ((globals.types[ref.type]?).bind (·.ctors[ref.index]?) |>.map (·.1)).getD s!"#{ref.type}.{ref.index}"

private def noSpan : Span := default

/-- `type Bool = True | False`, `type List a = Nil | Cons a (List a)`,
`type Pair a b = Pair a b`. -/
def preludeDecls : List DataDecl :=
  [{ span := noSpan, name := "Bool", params := [],
     ctors := [⟨noSpan, "True", []⟩, ⟨noSpan, "False", []⟩] },
   { span := noSpan, name := "List", params := ["a"],
     ctors := [⟨noSpan, "Nil", []⟩,
      ⟨noSpan, "Cons", [.var noSpan "a", .con noSpan "List" [.var noSpan "a"]]⟩] },
   { span := noSpan, name := "Pair", params := ["a", "b"],
     ctors := [⟨noSpan, "Pair", [.var noSpan "a", .var noSpan "b"]⟩] }]

def trueRef : CtorRef := ⟨0, 0⟩
def falseRef : CtorRef := ⟨0, 1⟩
def nilRef : CtorRef := ⟨1, 0⟩
def consRef : CtorRef := ⟨1, 1⟩
def pairRef : CtorRef := ⟨2, 0⟩
def pairType : Nat := 2

def primOf : String → Option PrimTy
  | "Int" => some .int
  | "Char" => some .char
  | "Unit" => some .unit
  | _ => none

/-! ## Types -/

section
variable {m : Type → Type} [Monad m] [MonadExcept LowerError m] {V : Type}
  (globals : Globals) (var : Span → String → m (EPL.Ty V))
  (hole : Span → Option String → m (EPL.Ty V))

mutual
/-- Lower a type, resolving type variables with `var` and holes (`_` is
`none`) with `hole`. -/
def lowerTyWith : Ty → m (EPL.Ty V)
  | .hole span => hole span none
  | .namedHole span name => hole span (some name)
  | .var span name => var span name
  | .unit _ => pure (.prim .unit)
  | .pair _ fst snd => do
      pure (.app (.app (.con pairType) (← lowerTyWith fst)) (← lowerTyWith snd))
  | .arrow _ domain codomain => do
      pure (.arrow (← lowerTyWith domain) (← lowerTyWith codomain))
  | .con span name args => do
      let lowered ← lowerTysWith args
      match primOf name with
      | some prim =>
          if args.isEmpty then pure (.prim prim)
          else throw ⟨span, .typeArity name 0 args.length⟩
      | none =>
          match globals.findType name with
          | some (id, info) =>
              if info.params = args.length then pure (EPL.Ty.apps (.con id) lowered)
              else throw ⟨span, .typeArity name info.params args.length⟩
          | none => throw ⟨span, .unknownType name⟩

def lowerTysWith : List Ty → m (List (EPL.Ty V))
  | [] => pure []
  | ty :: rest => do pure ((← lowerTyWith ty) :: (← lowerTysWith rest))
end
end

/-- The first name that occurs twice. -/
def firstDuplicate : List String → Option String
  | [] => none
  | name :: rest => if name ∈ rest then some name else firstDuplicate rest

/-- Check the declarations and build their signature. -/
def lowerDecls (decls : List DataDecl) : Except LowerError (Globals × Signature) := do
  for decl in decls, index in [0:decls.length] do
    if (primOf decl.name).isSome || (decls.take index).any (·.name == decl.name) then
      throw ⟨decl.span, .duplicateType decl.name⟩
  let ctors := decls.flatMap (·.ctors)
  for ctor in ctors, index in [0:ctors.length] do
    if (ctors.take index).any (·.name == ctor.name) then
      throw ⟨ctor.span, .duplicateConstructor ctor.name⟩
  let globals : Globals :=
    ⟨decls.map fun decl => ⟨decl.name, decl.params.length,
      decl.ctors.map fun ctor => (ctor.name, ctor.fields.length)⟩⟩
  let sig ← decls.mapM fun decl => do
    if let some name := firstDuplicate decl.params then
      throw ⟨decl.span, .duplicateTypeParameter name⟩
    let param (span : Span) (name : String) : Except LowerError SemTy :=
      match decl.params.idxOf? name with
      | some index => pure (.bvar index)
      | none => throw ⟨span, .unboundTypeVariable name⟩
    let noHole (span : Span) (_ : Option String) : Except LowerError SemTy :=
      throw ⟨span, .holeInDeclaration⟩
    let ctors ← decl.ctors.mapM fun ctor =>
      ctor.fields.mapM (lowerTyWith globals param noHole)
    pure (⟨decl.params.length, ctors⟩ : EPL.DataDecl)
  pure (globals, sig)

/-! ## Scopes -/

/-- What is in scope at a point of the source. Term variables are recorded by
de Bruijn *level* (`depth` binders are in scope), so names can alias a value
bound elsewhere (a pattern variable is the matched subterm). -/
structure Scope where
  depth : Nat := 0
  vars : List (String × Nat) := []
  /-- The rigid depth. -/
  k : Nat := 0
  /-- Type variables in scope, by rigid level, innermost first. -/
  tyVars : List (String × Nat) := []
  /-- The id of the binder at each level (see `OriginInfo.binder`). -/
  ids : Array Nat := #[]
  /-- Where each type variable in scope is bound, and by what. -/
  tyVarDefs : List (String × Span × String) := []
  deriving Inhabited

/-- Enter the term binder with id `id`, naming it `name` (`none` for an
anonymous one). -/
def Scope.bind (scope : Scope) (name : Option String) (id : Nat) : Scope :=
  { scope with
    depth := scope.depth + 1
    vars := match name with
      | some name => (name, scope.depth) :: scope.vars
      | none => scope.vars
    ids := scope.ids.push id }

/-- The binder id of the variable at `level`. -/
def Scope.idAt (scope : Scope) (level : Nat) : Nat := scope.ids.getD level 0

/-- Make `name` refer to the variable at `level`. -/
def Scope.alias (scope : Scope) (name : String) (level : Nat) : Scope :=
  { scope with vars := (name, level) :: scope.vars }

/-- The variable at `level`, as a term. -/
def Scope.varAt (scope : Scope) (level : Nat) : Source := .var (scope.depth - 1 - level)

/-- Enter `names` as type variables at the next rigid levels. -/
def Scope.enterTyVars (scope : Scope) (names : List String) : Scope :=
  { scope with
    k := scope.k + names.length
    tyVars := (names.zipIdx.map fun (name, i) => (name, scope.k + i)).reverse ++ scope.tyVars }

/-- Record that `owner` binds the type variables `names` at `spans`. -/
def Scope.defineTyVars (scope : Scope) (names : List String) (spans : List Span)
    (owner : String) : Scope :=
  { scope with tyVarDefs := (names.zip spans).reverse.map (fun (name, span) => (name, span, owner)) ++
      scope.tyVarDefs }

def Scope.origin (scope : Scope) (span : Span) (children : List Origin)
    (info : OriginInfo := {}) : Origin :=
  .node span scope.tyVars children info

/-- A core term and its origins. -/
abbrev Lowered := Source × Origin

def Scope.leaf (scope : Scope) (span : Span) (expr : Source) : Lowered :=
  (expr, scope.origin span [])

def Scope.app (scope : Scope) (span : Span) (function argument : Lowered) : Lowered :=
  (.app function.1 argument.1, scope.origin span [function.2, argument.2])

def Scope.apps (scope : Scope) (span : Span) (head : Lowered) (args : List Lowered) : Lowered :=
  args.foldl (scope.app span) head

/-- A lambda binding the variable with id `id`. -/
def Scope.lambda (scope : Scope) (span : Span) (ann : Option Template) (id : Nat)
    (body : Lowered) : Lowered :=
  (.lambda ann body.1, scope.origin span [body.2] { binder := some (id, .domain) })

/-- `[a, b, ...]` as `Cons a (Cons b ... Nil)`. -/
def Scope.list (scope : Scope) (span : Span) (items : List Lowered) : Lowered :=
  items.foldr (init := scope.leaf span (.ctor nilRef)) fun item rest =>
    scope.apps span (scope.leaf span (.ctor consRef)) [item, rest]

/-! ## The lowering monad -/

/-- A value name the source defines: where, where it can be used, and the
core binder it stands for. -/
structure NameInfo where
  name : String
  span : Span
  /-- Where the name can be used. -/
  scope : Span
  /-- The id of its core binder (see `Scope.ids`). -/
  binder : Nat
  /-- The type variables of a polymorphic `let`, and those in scope at its
  right-hand side, by rigid level. -/
  tyParams : List String := []
  tyVars : List (String × Nat) := []
  /-- A top-level `let`. -/
  topLevel : Bool := false
  /-- Defined by a `let` (not a parameter or a match's pattern). -/
  binding : Bool := false
  deriving Repr, Inhabited

/-- What a name that is not a value refers to. -/
inductive OccurrenceKind where
  | type
  | ctor
  /-- A type variable that `owner` binds. -/
  | tyVar (owner : String)
  /-- An infix operator in a pattern, standing for constructor `ctor`. -/
  | op (ctor : String)
  deriving Repr, Inhabited

/-- A type, type variable, constructor name or operator in the source, other than in a
data declaration and other than a constructor in an expression (whose node
records it). -/
structure Occurrence where
  name : String
  span : Span
  kind : OccurrenceKind
  isDef : Bool := false
  /-- Where a definition can be used. -/
  scope : Span := span
  deriving Repr, Inhabited

/-- The span of `name` written at the start of `span`. -/
def nameSpanAt (span : Span) (name : String) : Span :=
  ⟨span.start, ⟨span.start.line, span.start.col + name.length⟩⟩

/-- Lowering reads the declarations, counts the fresh hole names and binder
ids it has made, and collects the uncovered cases and the names the source
defines. -/
structure LowerState where
  /-- The number of fresh holes made so far. -/
  holes : Nat := 0
  /-- Each constructor a match leaves out, with where the value it misses is
  matched: the scrutinee, or the pattern whose field it is. -/
  uncovered : Array (Span × String) := #[]
  /-- The number of binder ids handed out (see `Scope.ids`). -/
  binders : Nat := 0
  /-- The value names the source defines. -/
  names : Array NameInfo := #[]
  /-- The other names the source mentions (see `Occurrence`). -/
  occurrences : Array Occurrence := #[]

abbrev M := ReaderT Globals (StateT LowerState (Except LowerError))

def freshBinder : M Nat :=
  modifyGet fun state => (state.binders, { state with binders := state.binders + 1 })

def recordName (info : NameInfo) : M Unit :=
  modify fun state => { state with names := state.names.push info }

def recordOccurrence (occurrence : Occurrence) : M Unit :=
  modify fun state => { state with occurrences := state.occurrences.push occurrence }

mutual
/-- Record the type names and type variables of an annotation. -/
def recordTyNames (scope : Scope) : Ty → M Unit
  | .hole _ | .namedHole _ _ | .unit _ => pure ()
  | .var span name => do
      if let some (_, owner) := scope.tyVarDefs.lookup name then
        recordOccurrence { name, span, kind := .tyVar owner }
  | .con span name args => do
      recordOccurrence { name, span := nameSpanAt span name, kind := .type }
      recordTyNamesList scope args
  | .pair _ fst snd | .arrow _ fst snd => do
      recordTyNames scope fst
      recordTyNames scope snd

def recordTyNamesList (scope : Scope) : List Ty → M Unit
  | [] => pure ()
  | ty :: rest => do
      recordTyNames scope ty
      recordTyNamesList scope rest
end

def findCtor (span : Span) (name : String) : M (CtorRef × Nat) := do
  match (← read).findCtor name with
  | some found => pure found
  | none => throw ⟨span, .unknownConstructor name⟩

/-- A hole no source annotation can name (source names start with a letter). -/
def freshHole : M Template := do
  let index ← modifyGet fun state => (state.holes, { state with holes := state.holes + 1 })
  pure (.var s!"_{index}")

/-- Lower an annotation in `scope`: its type variables must be in scope. -/
def lowerTemplate (scope : Scope) (ty : Ty) : M Template := do
  recordTyNames scope ty
  let var (span : Span) (name : String) : M Template :=
    match scope.tyVars.lookup name with
    | some level => pure (.rigid level)
    | none => throw ⟨span, .unboundTypeVariable name⟩
  let hole (_ : Span) : Option String → M Template
    | some name => pure (.var name)
    | none => freshHole
  lowerTyWith (← read) var hole ty

/-- A function head's signature: `param_1 -> ... -> result`, with a fresh hole
for each missing annotation. -/
def headTemplate (scope : Scope) (params : List ValueParam) (result : Option Ty) :
    M Template := do
  let domains ← params.mapM fun param => match param.ann with
    | some ann => lowerTemplate scope ann
    | none => freshHole
  let codomain ← match result with
    | some ann => lowerTemplate scope ann
    | none => freshHole
  pure (EPL.Ty.arrows domains codomain)

/-! ## Pattern matching -/

/-- A pattern with its constructors resolved and its sugar removed. -/
inductive RPat where
  /-- Matches anything, binding it to `name` if given. -/
  | any (name : Option (String × Span))
  | ctor (span : Span) (name : String) (ref : CtorRef) (args : List RPat)
  deriving Repr, Inhabited

mutual
def RPat.ctorCount : RPat → Nat
  | .any _ => 0
  | .ctor _ _ _ args => RPat.ctorCountList args + 1

def RPat.ctorCountList : List RPat → Nat
  | [] => 0
  | pattern :: rest => pattern.ctorCount + RPat.ctorCountList rest
end

mutual
def resolvePattern : Pattern → M RPat
  | .wildcard _ => pure (.any none)
  | .var span name => pure (.any (some (name, span)))
  | .ctor span name args => do
      let (ref, arity) ← findCtor span name
      if args.length ≠ arity then throw ⟨span, .patternArity name arity args.length⟩
      recordOccurrence { name, span := nameSpanAt span name, kind := .ctor }
      pure (.ctor span name ref (← resolvePatterns args))
  | .pair span fst snd => do
      pure (.ctor span "Pair" pairRef [← resolvePattern fst, ← resolvePattern snd])
  | .cons span opSpan head tail => do
      recordOccurrence { name := BinOp.cons.describe, span := opSpan, kind := .op "Cons" }
      pure (.ctor span "Cons" consRef [← resolvePattern head, ← resolvePattern tail])
  | .list span items => do
      let items ← resolvePatterns items
      pure (items.foldr (init := .ctor span "Nil" nilRef []) fun item rest =>
        .ctor span "Cons" consRef [item, rest])

def resolvePatterns : List Pattern → M (List RPat)
  | [] => pure []
  | pattern :: rest => do pure ((← resolvePattern pattern) :: (← resolvePatterns rest))
end

/-- A row of the pattern matrix: one pattern per column, the names already
bound (to levels), and the arm it leads to. -/
structure Row where
  pats : List RPat
  aliases : List ((String × Span) × Nat)
  arm : Nat
  deriving Inhabited

/-- The first column holding a constructor pattern, its span and constructor. -/
def firstCtor : List RPat → Nat → Option (Nat × Span × CtorRef)
  | [], _ => none
  | .any _ :: rest, column => firstCtor rest (column + 1)
  | .ctor span _ ref _ :: _, column => some (column, span, ref)

/-- The span of the first pattern for constructor `ref` in `column` of `rows`. -/
def ctorSpan (column : Nat) (ref : CtorRef) (rows : List Row) : Option Span :=
  rows.findSome? fun row => match row.pats[column]? with
    | some (RPat.ctor span _ other _) => if other = ref then some span else none
    | _ => none

/-- The rows that match constructor `index` (with `arity` fields) of `type` in
`column`, whose value is the variable at `level`: its fields replace the
column. -/
def specialize (column type index arity level : Nat) : List Row → M (List Row)
  | [] => pure []
  | row :: rows => do
      let rest ← specialize column type index arity level rows
      let others := row.pats.eraseIdx column
      match row.pats[column]? with
      | some (.any name) =>
          let aliases := match name with
            | some name => (name, level) :: row.aliases
            | none => row.aliases
          pure (⟨List.replicate arity (.any none) ++ others, aliases, row.arm⟩ :: rest)
      | some (.ctor span name ref args) =>
          if ref.type ≠ type then
            throw ⟨span, .foreignPattern name ((← read).typeName type)⟩
          else if ref.index = index then pure (⟨args ++ others, row.aliases, row.arm⟩ :: rest)
          else pure rest
      | none => pure rest

/-- Compile the rows, whose columns are the variables at the levels `columns`
(with spans to blame), to a decision tree. `leaf arm scope` lowers an arm's
body once its pattern variables are in `scope`. Returns `none` if no row
matches, and the arms reached. The fuel (constructor patterns plus one)
suffices: every split removes a constructor pattern of the first row. -/
def compile (leaf : Nat → Scope → M Lowered) (armScope : Nat → Span) (span : Span) :
    Nat → Scope → List (Nat × Span) → List Row → M (Option Lowered × List Nat)
  | 0, _, _, _ => throw ⟨span, .tooDeep⟩
  | _ + 1, _, _, [] => pure (none, [])
  | fuel + 1, scope, columns, row :: rows =>
      match firstCtor row.pats 0 with
      | none => do
          let bound := (row.pats.zip columns).filterMap fun
            | (.any (some name), (level, _)) => some (name, level)
            | _ => none
          let names := row.aliases ++ bound
          for ((name, nameSpan), level) in names do
            recordName { name := name, span := nameSpan, scope := armScope row.arm,
                         binder := scope.idAt level }
          let scope := names.foldl (fun scope ((name, _), level) =>
            scope.alias name level) scope
          pure (some (← leaf row.arm scope), [row.arm])
      | some (column, patSpan, ref) => do
          let some info := (← read).types[ref.type]? | throw ⟨span, .tooDeep⟩
          let (level, levelSpan) := columns.getD column (0, span)
          let others := columns.eraseIdx column
          let results ← info.ctors.zipIdx.mapM fun ((name, arity), index) => do
            let specialized ← specialize column ref.type index arity level (row :: rows)
            if specialized.isEmpty then
              modify fun state => { state with uncovered := state.uncovered.push (levelSpan, name) }
            -- A field's value is located at its constructor's pattern.
            let fieldSpan := (ctorSpan column ⟨ref.type, index⟩ (row :: rows)).getD patSpan
            let fields := (List.range arity).map fun i => (scope.depth + i, fieldSpan)
            let fieldIds ← (List.range arity).mapM fun _ => freshBinder
            let inner := fieldIds.foldl (fun scope id => scope.bind none id) scope
            let (tree, reached) ←
              compile leaf armScope span fuel inner (fields ++ others) specialized
            let branch := tree.map fun body =>
              ((⟨ref.type, index⟩ : CtorRef),
                fieldIds.foldr (init := body) fun id body =>
                  scope.lambda body.2.span none id body)
            pure (branch, reached)
          let branches := results.filterMap (·.1)
          pure (some (.match (scope.varAt level) (branches.map fun (ref, body) => (ref, body.1)),
              scope.origin patSpan (scope.origin levelSpan [] :: branches.map (·.2.2))),
            results.flatMap (·.2))

/-- Match the variables at the levels `columns` against `rows` (one per arm,
one pattern per column), checking that every arm is reachable. An arm's
pattern variables can be used in `armScope arm`. -/
def compileMatch (scope : Scope) (span : Span) (columns : List (Nat × Span))
    (rows : List (List Pattern)) (armScope : Nat → Span) (leaf : Nat → Scope → M Lowered) :
    M Lowered := do
  for row in rows do
    if let some name := firstDuplicate (Pattern.varsList row) then
      throw ⟨((row.head?.map (·.span)).getD span), .duplicatePatternVariable name⟩
  let resolved ← rows.mapM resolvePatterns
  let fuel := (resolved.map RPat.ctorCountList).sum + 1
  let (tree, reached) ← compile leaf armScope span fuel scope columns
    (resolved.zipIdx.map fun (pats, arm) => ⟨pats, [], arm⟩)
  for row in rows, arm in [0:rows.length] do
    unless reached.contains arm do
      throw ⟨((row.head?.map (·.span)).getD span), .redundantArm⟩
  match tree with
  | some tree => pure tree
  | none => throw ⟨span, .tooDeep⟩

/-! ## Bindings -/

/-- A cycle among `pending` bindings (each paired with the block names it
uses), starting from the first. -/
def findCycle (pending : List (Binding × List String)) : Nat → List String → String →
    List String
  | 0, path, _ => path
  | fuel + 1, path, current =>
      if current ∈ path then (path.dropWhile (· ≠ current)) else
      let next := (pending.find? (current ∈ ·.1.names)).bind fun (_, uses) =>
        uses.find? fun name => pending.any (name ∈ ·.1.names)
      match next with
      | some next => findCycle pending fuel (path ++ [current]) next
      | none => path ++ [current]

/-- Order a block's bindings so that each comes after the bindings it uses
(keeping the source order where it is free). With repeated names (allowed
except at top level) bindings are taken in source order, each seeing the
earlier ones. -/
def sortBindings (topLevel : Bool) (bindings : List (Binding × Expr)) :
    Except LowerError (List (Binding × Expr)) := do
  let names := bindings.flatMap (·.1.names)
  if let some name := firstDuplicate names then
    if topLevel then
      let span := ((bindings.find? (name ∈ ·.1.names |> decide)).map (·.1.span)).getD default
      let span := ((bindings.reverse.find? (name ∈ ·.1.names |> decide)).map (·.1.span)).getD span
      throw ⟨span, .duplicateBinding name⟩
    else return bindings
  let entries := bindings.map fun (binding, rhs) =>
    ((binding, rhs), ((binding.rhsFreeVars rhs.freeVars).filter fun name =>
      name ∈ names && name ∉ binding.names).eraseDups)
  let rec go : Nat → List String → List ((Binding × Expr) × List String) →
      Except LowerError (List (Binding × Expr))
    | _, _, [] => pure []
    | 0, _, _ => pure [] -- unreachable: each step emits one binding
    | fuel + 1, done, pending =>
        match pending.find? (fun (_, uses) => uses.all (· ∈ done)) with
        | some entry@((binding, _), _) => do
            let rest ← go fuel (done ++ binding.names)
              (pending.filter fun other => other.1.1.span != entry.1.1.span ||
                other.1.1.names != entry.1.1.names)
            pure (entry.1 :: rest)
        | none =>
            let blocked := pending.map fun ((binding, _), uses) =>
              (binding, uses.filter (· ∉ done))
            let span := (blocked.head?.map (·.1.span)).getD default
            let start := ((blocked.head?.bind (·.1.names.head?))).getD ""
            throw ⟨span, .mutualRecursion (findCycle blocked (blocked.length + 1) [] start)⟩
  go (entries.length + 1) [] entries

/-! ## Expressions -/

mutual
/-- Lower an expression in `scope`. The fuel bounds the depth of the
recursion; `Expr.size` is enough. -/
def lowerExpr : Nat → Scope → Expr → M Lowered
  | 0, _, expr => throw ⟨expr.span, .tooDeep⟩
  | fuel + 1, scope, expr => do
    let lowered ← (match expr with
    | .int span value => pure (scope.leaf span (.lit (.int value)))
    | .char span value => pure (scope.leaf span (.lit (.char value)))
    | .unit span => pure (scope.leaf span (.lit .unit))
    | .string span value =>
        pure (scope.list span (value.toList.map fun char => scope.leaf span (.lit (.char char))))
    | .var span name =>
        match scope.vars.lookup name with
        | some level => pure (scope.varAt level,
            scope.origin span [] { use := some (name, "val"), useBinder := some (scope.idAt level) })
        | none => throw ⟨span, .unboundVariable name⟩
    | .ctor span name => do
        let (ref, _) ← findCtor span name
        pure (.ctor ref, scope.origin span [] { use := some (name, "ctor") })
    | .binOp span op opSpan left right => do
        let left ← lowerExpr fuel scope left
        let right ← lowerExpr fuel scope right
        let head : Source := match op with
          | .add => .primOp .intAdd
          | .sub => .primOp .intSub
          | .lt => .primOp .intLt
          | .cons => .ctor consRef
        let head := (head, scope.origin opSpan [] { use := some (op.describe, "op") })
        pure (scope.apps span head [left, right])
    | .pair span fst snd => do
        let fst ← lowerExpr fuel scope fst
        let snd ← lowerExpr fuel scope snd
        pure (scope.apps span (scope.leaf span (.ctor pairRef)) [fst, snd])
    | .list span items => do
        pure (scope.list span (← items.mapM (lowerExpr fuel scope)))
    | .app span function argument => do
        let function ← lowerExpr fuel scope function
        let argument ← lowerExpr fuel scope argument
        pure (scope.app span function argument)
    | .lambda span param body => do
        let ann ← param.ann.mapM (lowerTemplate scope)
        let id ← freshBinder
        match param.pattern with
        | .var nameSpan name =>
            recordName { name := name, span := nameSpan, scope := span, binder := id }
            pure (scope.lambda span ann id (← lowerExpr fuel (scope.bind name id) body))
        | .wildcard _ => pure (scope.lambda span ann id (← lowerExpr fuel (scope.bind none id) body))
        | pattern => do
            let body ← compileMatch (scope.bind none id) span [(scope.depth, param.span)]
              [[pattern]] (fun _ => span) fun _ scope => lowerExpr fuel scope body
            pure (scope.lambda span ann id body)
    | .ite span cond thenBranch elseBranch => do
        let cond ← lowerExpr fuel scope cond
        let thenBranch ← lowerExpr fuel scope thenBranch
        let elseBranch ← lowerExpr fuel scope elseBranch
        pure (.match cond.1 [(trueRef, thenBranch.1), (falseRef, elseBranch.1)],
          scope.origin span [cond.2, thenBranch.2, elseBranch.2])
    | .match span scrutinee arms => do
        let rows := arms.map fun (pattern, _) => [pattern]
        let leaf (arm : Nat) (scope : Scope) : M Lowered :=
          lowerExpr fuel scope (arms[arm]!).2
        let armScope (arm : Nat) : Span :=
          ((arms[arm]?).map fun (pattern, body) => pattern.span.union body.span).getD span
        match scrutinee with
        | .var varSpan name =>
            match scope.vars.lookup name with
            | some level => compileMatch scope span [(level, varSpan)] rows armScope leaf
            | none => throw ⟨varSpan, .unboundVariable name⟩
        | _ =>
            let lowered ← lowerExpr fuel scope scrutinee
            let id ← freshBinder
            let tree ← compileMatch (scope.bind none id) span [(scope.depth, scrutinee.span)] rows
              armScope leaf
            pure (.letIn none lowered.1 tree.1,
              scope.origin span [lowered.2, tree.2] { binder := some (id, .rhs) })
    | .letIn span bindings body => do
        let sorted ← liftExcept (sortBindings false bindings)
        lowerChain fuel scope span false sorted body : M Lowered)
    pure (lowered.1, lowered.2.mapInfo ({ · with expr := some expr.span }))

/-- Lower `let b1 = e1 in ... let bn = en in body`, in this order: the
bindings of a block that spans `block` (at top level if `topLevel`). -/
def lowerChain : Nat → Scope → Span → Bool → List (Binding × Expr) → Expr → M Lowered
  | 0, _, _, _, _, body => throw ⟨body.span, .tooDeep⟩
  | fuel + 1, scope, _, _, [], body => lowerExpr fuel scope body
  | fuel + 1, scope, block, topLevel, (binding, rhs) :: rest, body =>
    match binding.target with
    | .named name tyParams params nameSpan => do
        let binders := tyParams ++ ((binding.ann.map (·.binders)).getD [])
        if let some name := firstDuplicate binders then
          throw ⟨binding.span, .duplicateTypeParameter name⟩
        let inner := (scope.enterTyVars binders).defineTyVars binders
          (binding.tyParamSpans ++ ((binding.ann.map (·.binderSpans)).getD [])) name
        let annotated := !binders.isEmpty || params.any (·.ann.isSome) || binding.ann.isSome
        let template ← if annotated then
            some <$> headTemplate inner params (binding.ann.map (·.body))
          else pure none
        let recursive := name ∈ binding.rhsFreeVars rhs.freeVars
        let letId ← freshBinder
        let selfId ← freshBinder
        recordName { name := name, span := nameSpan, scope := block, binder := letId,
                     tyParams := binders, tyVars := inner.tyVars, topLevel := topLevel,
                     binding := true }
        for (tyVar, span) in binders.zip
            (binding.tyParamSpans ++ ((binding.ann.map (·.binderSpans)).getD [])) do
          recordOccurrence { name := tyVar, span, kind := .tyVar name, isDef := true,
                             scope := binding.span.union rhs.span }
        let selfScope := if recursive then inner.bind name selfId else inner
        let params ← params.mapM fun param => do
          let id ← freshBinder
          if let some paramName := param.name then
            recordName { name := paramName, span := param.nameSpan,
                         scope := binding.span.union rhs.span, binder := id }
          pure (param, id)
        let paramScope := params.foldl (fun scope (param, id) => scope.bind param.name id)
          selfScope
        let body' ← lowerExpr fuel paramScope rhs
        let lambdas := params.foldr (init := body') fun (param, id) body =>
          inner.lambda param.span none id body
        let rhs' : Lowered := if recursive then
            (.fix none lambdas.1, inner.origin binding.span [lambdas.2]
              { binder := some (selfId, .self) })
          else lambdas
        let rest' ← lowerChain fuel (scope.bind name letId) block topLevel rest body
        -- An error at the let itself concerns its signature: name its binders.
        pure (.letIn (template.map (⟨binders.length, ·⟩)) rhs'.1 rest'.1,
          inner.origin binding.span [rhs'.2, rest'.2] { binder := some (letId, .rhs) })
    | .pattern pattern => do
        let free := rhs.freeVars
        let recursive := pattern.vars.filter (· ∈ free)
        unless recursive.isEmpty do
          throw ⟨binding.span, .recursivePattern recursive⟩
        let binders := (binding.ann.map (·.binders)).getD []
        if let some name := firstDuplicate binders then
          throw ⟨binding.span, .duplicateTypeParameter name⟩
        let binderSpans := (binding.ann.map (·.binderSpans)).getD []
        let inner := (scope.enterTyVars binders).defineTyVars binders binderSpans "this let"
        for (tyVar, span) in binders.zip binderSpans do
          recordOccurrence { name := tyVar, span, kind := .tyVar "this let", isDef := true,
                             scope := binding.span.union rhs.span }
        let template ← binding.ann.mapM fun ann => lowerTemplate inner ann.body
        let rhs' ← lowerExpr fuel inner rhs
        let id ← freshBinder
        let named := (← get).names.size
        let tree ← compileMatch (scope.bind none id) binding.span [(scope.depth, binding.span)]
          [[pattern]] (fun _ => block) fun _ scope => lowerChain fuel scope block topLevel rest body
        -- The pattern's variables are the first names recorded, before the body's.
        let vars := pattern.vars.length
        modify fun state => { state with names := state.names.mapIdx fun index info =>
          if named ≤ index ∧ index < named + vars then { info with binding := true } else info }
        pure (.letIn (template.map (⟨binders.length, ·⟩)) rhs'.1 tree.1,
          inner.origin binding.span [rhs'.2, tree.2] { binder := some (id, .rhs) })
end

/-! ## Programs -/

/-- A lowered program. -/
structure Lowering where
  globals : Globals
  sig : Signature
  term : Source
  origin : Origin
  /-- The span of the program's final expression. -/
  body : Span
  /-- The constructors that matches leave out, in the order found (see
  `LowerState.uncovered`). The program is exhaustive exactly when this is
  empty. -/
  uncovered : List (Span × String)
  /-- The value names the program defines. -/
  names : List NameInfo
  /-- The other names it mentions outside data declarations. -/
  occurrences : List Occurrence
  /-- The data declarations, the prelude's first: type `con i` is entry `i`. -/
  decls : List DataDecl
  /-- Doc comments, by the position of the name they document (filled in from
  the comments, which lowering does not see). -/
  docs : List (Pos × String) := []

def lowerProgram (program : Program) : Except LowerError Lowering := do
  let (globals, sig) ← lowerDecls (preludeDecls ++ program.decls)
  let sorted ← sortBindings true program.bindings
  let fuel := 2 * (Expr.sizeBindings program.bindings + program.body.size) + 8
  -- Top-level names can be used anywhere.
  let everywhere : Span := ⟨⟨1, 1⟩, ⟨1000000000, 1⟩⟩
  let ((term, origin), state) ←
    (lowerChain fuel {} everywhere true sorted program.body).run globals |>.run {}
  pure ⟨globals, sig, term, origin, program.body.span, state.uncovered.toList,
    state.names.toList, state.occurrences.toList, preludeDecls ++ program.decls, []⟩

end EPL.Surface
