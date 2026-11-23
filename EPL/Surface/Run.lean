import EPL.Theorems
import EPL.Surface.Parse
import EPL.Surface.Lower

/-!
# Running surface programs

`check` lexes, parses, lowers and infers a program; `run` also evaluates it
with the core's proof-carrying `evaluate`. Both stop at the first error, which
`Error.render` prints with its source position. Inference errors are located
by following their path through the lowering's `Origin` tree.
-/

namespace EPL.Surface

inductive Error where
  | lex (error : LexError)
  | parse (error : ParseError)
  | lower (error : LowerError)
  /-- Inference rejected the program at `span`, with type variables `tyVars` in
  scope there. -/
  | infer (globals : Globals) (span : Span) (tyVars : List (String × Nat)) (error : InferError)
  /-- The expression at `span`, of type `ty`, is applied to an argument but is
  not a function. -/
  | notAFunction (globals : Globals) (span : Span) (tyVars : List (String × Nat)) (ty : InfTy)
  /-- The program is well typed but a match at `span` does not cover the
  constructor `ctor`. -/
  | notExhaustive (span : Span) (ctor : String)
  /-- The core rejects a match that the lowering did not record as partial.
  Not expected to happen. -/
  | notExhaustiveUnlocated
  /-- A doc comment at `span` documents nothing. -/
  | misplacedDoc (span : Span)
  deriving Repr

/-! ## Doc comments

A run of doc comments documents the name it comes before (ordinary comments
may come in between), as in FHM: the names a `let` defines, the type after
`type`, the constructor after `|`, or the constructor it is directly before
(a type's first). A doc comment before anything else is an error, so it
cannot silently document nothing. -/

/-- A token or a comment, in source order. -/
inductive Lexeme where
  | tok (t : Tok)
  | comment (c : Comment)

def Lexeme.start : Lexeme → Pos
  | .tok t => t.span.start
  | .comment c => c.span.start

/-- Where each doc comment is, its text, and where the names it may document
start. -/
def docCandidates (tokens : Array Tok) (comments : Array Comment) :
    List (Span × String × List Pos) :=
  let before (a b : Lexeme) : Bool :=
    a.start.line < b.start.line || (a.start.line == b.start.line && a.start.col < b.start.col)
  let lexemes := ((tokens.map Lexeme.tok) ++ (comments.map Lexeme.comment)).qsort before
  let isDoc : Lexeme → Bool
    | .comment c => c.doc.isSome
    | _ => false
  let isComment : Lexeme → Bool
    | .comment _ => true
    | _ => false
  let rec go (fuel : Nat) (rest : List Lexeme) : List (Span × String × List Pos) :=
    match fuel, rest with
    | 0, _ | _, [] => []
    | fuel + 1, .comment { span, doc := some text } :: rest =>
        let more := rest.takeWhile isDoc
        let text := "\n".intercalate (text :: more.filterMap fun
          | .comment c => c.doc
          | _ => none)
        let after := (rest.drop more.length).dropWhile isComment
        let targets := match after with
          | .tok { token := .keyword .let, .. } :: header =>
              (header.takeWhile fun
                | .tok { token := .punct .eq, .. } => false
                | _ => true).filterMap fun
                | .tok { token := .ident .., span } => some span.start
                | _ => none
          | .tok { token := .keyword .type, .. } :: next :: _
          | .tok { token := .punct .pipe, .. } :: next :: _ => [next.start]
          | next :: _ => [next.start]
          | [] => []
        (span, text, targets) :: go fuel (rest.drop more.length)
    | fuel + 1, _ :: rest => go fuel rest
  go (lexemes.size + 1) lexemes.toList

/-- Attach the doc comments to the names they document. -/
def Lowering.attachDocs (lowering : Lowering) (tokens : Array Tok) (comments : Array Comment) :
    Except Error Lowering := do
  let user := lowering.decls.drop preludeDecls.length
  let defined : List Pos :=
    (lowering.names.filter (·.binding)).map (·.span.start) ++
      user.map (·.nameSpan.start) ++ user.flatMap fun decl => decl.ctors.map (·.span.start)
  let mut docs := []
  for (span, text, targets) in docCandidates tokens comments do
    let documented := targets.filter (· ∈ defined)
    if documented.isEmpty then throw (.misplacedDoc span)
    docs := docs ++ documented.map (·, text)
  pure { lowering with docs }

def frontEnd (source : String) : Except Error Lowering := do
  let (tokens, comments) ← (lexWithComments source).mapError .lex
  let program ← (parseProgram tokens).mapError .parse
  let lowering ← (lowerProgram program).mapError .lower
  lowering.attachDocs tokens comments

/-- The subterm at `path`, if it is there. -/
def _root_.EPL.Expr.at? {A : Type} : EPL.Expr A → List ExprStep → Option (EPL.Expr A)
  | expr, [] => some expr
  | .lambda _ body, .lambdaBody :: path
  | .app body _, .appFunction :: path
  | .app _ body, .appArgument :: path
  | .letIn _ body _, .letRhs :: path
  | .letIn _ _ body, .letBody :: path
  | .fix _ body, .fixBody :: path
  | .match body _, .matchScrutinee :: path => body.at? path
  | .match _ branches, .matchBranch index :: path =>
      (branches[index]?).bind fun (_, body) => body.at? path
  | _, _ => none

/-- Locate an inference error. The program's undetermined type is reported at
its final expression. An application's mismatch is reported at its argument,
as one between the argument's type and the parameter's, or at its function if
that is not a function at all. -/
def Lowering.inferError (lowering : Lowering) (error : InferError) : Error :=
  let origin := lowering.origin.locate error.path
  let at_ (index : Nat) := (origin.children[index]?).getD origin
  match error.reason, lowering.term.at? error.path with
  | .undeterminedType _, _ => .infer lowering.globals lowering.body [] error
  -- Inference unified the function's type `actual` with `argument -> ?result`.
  | .mismatch (.arrow argument (.var _)) (.arrow parameter _) cause, some (.app ..) =>
      let cause := match cause with
        | .clash left right => .clash right left
        | cause => cause
      let arg := at_ 1
      .infer lowering.globals arg.span arg.tyVars
        ⟨error.path ++ [.appArgument], .mismatch parameter argument cause⟩
  | .mismatch (.arrow _ (.var _)) (.var _) _, some (.app ..) =>
      .infer lowering.globals origin.span origin.tyVars error
  | .mismatch (.arrow _ (.var _)) actual _, some (.app ..) =>
      let function := at_ 0
      .notAFunction lowering.globals function.span function.tyVars actual
  | _, _ => .infer lowering.globals origin.span origin.tyVars error

/-- The error for a well-typed program whose matches are not all exhaustive. -/
def Lowering.notExhaustive (lowering : Lowering) : Error :=
  match lowering.uncovered with
  | (span, ctor) :: _ => .notExhaustive span ctor
  | [] => .notExhaustiveUnlocated

/-- Infer the type of a program and check that its matches are exhaustive. -/
def check (source : String) : Except Error (Lowering × InferenceResult) := do
  let lowering ← frontEnd source
  let result ← (infer lowering.sig lowering.term).mapError lowering.inferError
  unless lowering.uncovered.isEmpty do throw lowering.notExhaustive
  pure (lowering, result)

/-- `check`, also returning the type of every core node (see `TypeTree`). -/
def checkWithTypes (source : String) : Except Error (Lowering × InferenceResult × TypeTree) := do
  let lowering ← frontEnd source
  let (result, types) ← (inferWithTypes lowering.sig lowering.term).mapError lowering.inferError
  unless lowering.uncovered.isEmpty do throw lowering.notExhaustive
  pure (lowering, result, types)

/-- Infer the type of a program and run it for at most `fuel` steps: its value
(`none` if fuel ran out) and type. -/
def run (source : String) (fuel : Nat := 100000) :
    Except Error (Lowering × Option RuntimeExpr × SemTy) := do
  let lowering ← frontEnd source
  match evaluate lowering.sig lowering.term fuel with
  | .error (.rejected error) => throw (lowering.inferError error)
  | .error .notExhaustive => throw lowering.notExhaustive
  | .ok ⟨result, outcome⟩ => pure (lowering, outcome.value?, result.ty)

/-! ## Printing -/

def parens (cond : Bool) (text : String) : String := if cond then s!"({text})" else text

/-- A type, at precedence `prec` (0: anywhere, 1: function position or arrow
domain, 2: argument). -/
def showTy (globals : Globals) (var : V → String) (rigid : Nat → String) :
    Nat → EPL.Ty V → String
  | _, .prim .int => "Int"
  | _, .prim .char => "Char"
  | _, .prim .unit => "Unit"
  | prec, .arrow domain codomain =>
      parens (prec ≥ 1) s!"{showTy globals var rigid 1 domain} -> {showTy globals var rigid 0 codomain}"
  | _, .app (.app (.con 2) fst) snd =>
      s!"({showTy globals var rigid 0 fst}, {showTy globals var rigid 0 snd})"
  | prec, .app function argument =>
      parens (prec ≥ 2)
        s!"{showTy globals var rigid 1 function} {showTy globals var rigid 2 argument}"
  | _, .con id => globals.typeName id
  | _, .bvar index => s!"#{index}"
  | _, .rigid level => rigid level
  | _, .var v => var v

/-- The name of rigid level `level` among `tyVars`. -/
def rigidName (tyVars : List (String × Nat)) (level : Nat) : String :=
  ((tyVars.find? (·.2 == level)).map (·.1)).getD s!"'{level}"

def showSemTy (globals : Globals) (ty : SemTy) : String :=
  showTy globals Empty.elim (rigidName []) 0 ty

def showInfTy (globals : Globals) (tyVars : List (String × Nat)) (ty : InfTy) : String :=
  showTy globals (fun id => s!"?{id}") (rigidName tyVars) 0 ty

/-- A printed value, with what printing it inside another value needs. -/
inductive Shown where
  | atom (text : String)
  /-- An application, parenthesized as an argument. -/
  | compound (text : String)
  | char (value : Char)
  /-- A complete list. -/
  | list (items : List String)
  /-- A complete nonempty list of characters. -/
  | string (value : String)

def Shown.text : Shown → String
  | .atom text | .compound text => text
  | .char value => toString (repr value)
  | .list items => "[" ++ ", ".intercalate items ++ "]"
  | .string value => toString (repr value)

def Shown.arg : Shown → String
  | .compound text => s!"({text})"
  | shown => shown.text

/-- Print the head of an application spine applied to `args`. Partial
applications and functions print as `<function>`. -/
def showValueAux (globals : Globals) : RuntimeExpr → List Shown → Shown
  | .app function argument, args =>
      showValueAux globals function (showValueAux globals argument [] :: args)
  | .ctor ref, args =>
      let arity := ((globals.types[ref.type]?).bind (·.ctors[ref.index]?) |>.map (·.2)).getD 0
      if args.length ≠ arity then .atom "<function>"
      else if ref = nilRef then .list []
      else if ref = consRef then
        match args with
        | [.char char, .list []] => .string (String.singleton char)
        | [.char char, .string rest] => .string (String.singleton char ++ rest)
        | [head, .list items] => .list (head.text :: items)
        | [head, .string rest] => .list (head.text :: rest.toList.map fun char => toString (repr char))
        | _ => .compound (" :: ".intercalate (args.map Shown.arg))
      else if ref = pairRef then .atom ("(" ++ ", ".intercalate (args.map Shown.text) ++ ")")
      else if args.isEmpty then .atom (globals.ctorName ref)
      else .compound (" ".intercalate (globals.ctorName ref :: args.map Shown.arg))
  | .lit (.int value), [] => .atom (toString value)
  | .lit (.char value), [] => .char value
  | .lit .unit, [] => .atom "()"
  | _, _ => .atom "<function>"

def showValue (globals : Globals) (value : RuntimeExpr) : String :=
  (showValueAux globals value []).text

/-! ## Symbols

Editor tools learn types from the lowering's `Origin` tree and inference's
`TypeTree`, which both have a node per core node: a node's type is the one at
the same path. A binder's type comes from its node's (see `BinderTy`), and a
name the source defines has its binder's type. -/

/-- A span of the source with its type, for hover and go-to-definition. -/
structure Symbol where
  name : String
  /-- `"val"` for a value, `"ctor"` for a constructor, `"op"` for an infix
  operator, `"type"` for a type, `"param"` for a type variable, `"expr"` for an
  expression. -/
  kind : String
  /-- The type; a type's declaration; for a type variable, what binds it. -/
  ty : String
  span : Span
  /-- Where a definition can be used; a use's own span. -/
  scope : Span
  /-- A definition, rather than a use or an expression. -/
  isDef : Bool
  doc : Option String := none
  /-- A constructor's type declaration. -/
  declaration : Option String := none
  /-- The binder id a value use refers to (see `OriginInfo.useBinder`). -/
  binder : Option Nat := none
  deriving Repr, Inhabited

def _root_.EPL.TypeTree.ty : TypeTree → InfTy
  | .node ty _ => ty

def _root_.EPL.TypeTree.children : TypeTree → List TypeTree
  | .node _ children => children

/-- What a node says about the program: a binder's type, or a symbol. -/
inductive NodeFact where
  | binder (id : Nat) (ty : InfTy) (tyVars : List (String × Nat))
  | symbol (symbol : Symbol)

/-- The type of the variable a binder node binds, given the node's type and
its children's. -/
def BinderTy.of (types : TypeTree) : BinderTy → Option InfTy
  | .domain => match types.ty with
      | .arrow param _ => some param
      | _ => none
  | .rhs => types.children.head?.map TypeTree.ty
  | .self => some types.ty

mutual
/-- The facts of the nodes of `origin`, whose types are `types`, added to
`facts`; `none` if the two trees differ in shape. -/
def nodeFacts (globals : Globals) (facts : Array NodeFact) :
    Origin → TypeTree → Option (Array NodeFact)
  | .node span tyVars children info, types => do
      let shown := showInfTy globals tyVars types.ty
      let facts := match info.binder.bind fun (id, how) => (how.of types).map (id, ·) with
        | some (id, ty) => facts.push (.binder id ty tyVars)
        | none => facts
      let facts := match info.use with
        | some (name, kind) =>
            facts.push (.symbol { name, kind, ty := shown, span, scope := span, isDef := false,
                                  binder := info.useBinder })
        | none => facts
      let facts := match info.expr with
        | some span => facts.push (.symbol { name := "expression", kind := "expr", ty := shown,
                                             span, scope := span, isDef := false })
        | none => facts
      nodeFactsList globals facts children types.children

def nodeFactsList (globals : Globals) (facts : Array NodeFact) :
    List Origin → List TypeTree → Option (Array NodeFact)
  | [], [] => some facts
  | origin :: origins, types :: rest => do
      nodeFactsList globals (← nodeFacts globals facts origin types) origins rest
  | _, _ => none
end

/-- `{a b} ` for a polymorphic let's type variables. -/
def tyParamsPrefix : List String → String
  | [] => ""
  | names => "{" ++ " ".intercalate names ++ "} "

mutual
/-- A type as written, at precedence `prec` (as for `showTy`). -/
def Ty.render : Nat → Ty → String
  | _, .hole _ => "_"
  | _, .namedHole _ name => s!"?{name}"
  | _, .var _ name => name
  | _, .unit _ => "Unit"
  | _, .pair _ fst snd => s!"({fst.render 0}, {snd.render 0})"
  | prec, .arrow _ domain codomain =>
      parens (prec ≥ 1) s!"{domain.render 1} -> {codomain.render 0}"
  | _, .con _ name [] => name
  | prec, .con _ name args => parens (prec ≥ 2) (" ".intercalate (name :: Ty.renderArgs args))

def Ty.renderArgs : List Ty → List String
  | [] => []
  | ty :: rest => ty.render 2 :: Ty.renderArgs rest
end

/-- `{s t}`, if the constructor has type variables of its own. -/
def CtorDecl.existentialsText (ctor : CtorDecl) : List String :=
  if ctor.existentials.isEmpty then [] else ["{" ++ " ".intercalate ctor.existentials ++ "}"]

/-- `type Maybe a =` and a line `  | C fields` per constructor. -/
def DataDecl.declaration (decl : DataDecl) : String :=
  "\n".intercalate (s!"type {" ".intercalate (decl.name :: decl.params)} =" ::
    decl.ctors.map fun ctor =>
      "  | " ++ " ".intercalate (ctor.name :: ctor.existentialsText ++ ctor.fields.map (·.render 2)))

/-- A constructor's type: `{a} a -> Maybe a`; its own type variables come after
the data type's parameters, as in `{a s} s -> (s -> a) -> Pack a`. -/
def DataDecl.ctorTy (decl : DataDecl) (ctor : CtorDecl) : String :=
  let result := " ".intercalate (decl.name :: decl.params)
  tyParamsPrefix (decl.params ++ ctor.existentials) ++
    " -> ".intercalate (ctor.fields.map (·.render 1) ++ [result])

/-- What hover shows for a type: its declaration. -/
def Lowering.typeInfo (lowering : Lowering) (name : String) : String × Option String :=
  if (primOf name).isSome then (s!"type {name}  -- built in", none)
  else match lowering.decls.find? (·.name == name) with
    | some decl => (decl.declaration, lowering.docs.lookup decl.nameSpan.start)
    | none => (name, none)

/-- A constructor's declaring type and declaration. -/
def Lowering.ctorDecl? (lowering : Lowering) (name : String) : Option (DataDecl × CtorDecl) :=
  lowering.decls.findSome? fun decl => (decl.ctors.find? (·.name == name)).map (decl, ·)

/-- Top-level names can be used anywhere. -/
def everywhere : Span := ⟨⟨1, 1⟩, ⟨1000000000, 1⟩⟩

mutual
/-- The type names and type variables in a declared field type. -/
def tyUses (lowering : Lowering) (decl : DataDecl) : Ty → List Symbol
  | .hole _ | .namedHole _ _ | .unit _ => []
  | .var span name =>
      [{ name, kind := "param", ty := s!"type variable (of {decl.name})", span, scope := span,
         isDef := false }]
  | .con span name args =>
      let (ty, doc) := lowering.typeInfo name
      let span := nameSpanAt span name
      { name, kind := "type", ty, span, scope := span, isDef := false, doc } ::
        tyUsesList lowering decl args
  | .pair _ fst snd | .arrow _ fst snd => tyUses lowering decl fst ++ tyUses lowering decl snd

def tyUsesList (lowering : Lowering) (decl : DataDecl) : List Ty → List Symbol
  | [] => []
  | ty :: rest => tyUses lowering decl ty ++ tyUsesList lowering decl rest
end

/-- The symbols of the program's data declarations. -/
def Lowering.declSymbols (lowering : Lowering) : List Symbol :=
  (lowering.decls.drop preludeDecls.length).flatMap fun decl =>
    let (declaration, doc) := lowering.typeInfo decl.name
    { name := decl.name, kind := "type", ty := declaration, span := decl.nameSpan,
      scope := everywhere, isDef := true, doc } ::
    (decl.params.zip decl.paramSpans).map (fun (name, span) =>
      { name, kind := "param", ty := s!"type variable (of {decl.name})", span,
        scope := decl.span, isDef := true }) ++
    decl.ctors.flatMap fun ctor =>
      let span := nameSpanAt ctor.span ctor.name
      { name := ctor.name, kind := "ctor", ty := decl.ctorTy ctor, span, scope := everywhere,
        isDef := true, doc := lowering.docs.lookup span.start, declaration } ::
      (ctor.existentials.zip ctor.existentialSpans).map (fun (name, span) =>
        { name, kind := "param", ty := s!"type variable (of {ctor.name})", span,
          scope := ctor.span, isDef := true }) ++
      tyUsesList lowering decl ctor.fields

/-- The symbol of a type, type variable or constructor in a pattern. -/
def Lowering.occurrenceSymbol (lowering : Lowering) (occurrence : Occurrence) : Symbol :=
  let base : Symbol :=
    { name := occurrence.name, kind := "type", ty := "", span := occurrence.span,
      scope := occurrence.scope, isDef := occurrence.isDef }
  match occurrence.kind with
  | .type =>
      let (ty, doc) := lowering.typeInfo occurrence.name
      { base with ty, doc }
  | .ctor => { base with kind := "ctor" }
  | .tyVar owner => { base with kind := "param", ty := s!"type variable (of {owner})" }
  | .op ctor =>
      { base with kind := "op", ty := ((lowering.ctorDecl? ctor).map fun (decl, ctor) =>
                                        decl.ctorTy ctor).getD "" }

/-- Fill in a constructor's declaration and doc, and its type if missing. -/
def Lowering.withCtorInfo (lowering : Lowering) (symbol : Symbol) : Symbol :=
  match lowering.ctorDecl? symbol.name with
  | some (decl, ctor) =>
      { symbol with
        ty := if symbol.ty.isEmpty then decl.ctorTy ctor else symbol.ty
        declaration := some decl.declaration
        doc := lowering.docs.lookup (nameSpanAt ctor.span ctor.name).start }
  | none => symbol

/-- The symbols of a checked program: each name it defines or uses, with its
type and doc, and each expression. Arm bodies that the match compiler copies
yield the same symbol more than once; only the first is kept. Without values
or expressions if the trees differ in shape, which is not expected. -/
def Lowering.symbols (lowering : Lowering) (types : TypeTree) : Array Symbol := Id.run do
  let facts := (nodeFacts lowering.globals #[] lowering.origin types).getD #[]
  let binders : Std.HashMap Nat (InfTy × List (String × Nat)) :=
    facts.foldl (init := {}) fun binders fact => match fact with
      | .binder id ty tyVars => binders.insert id (ty, tyVars)
      | .symbol _ => binders
  let docOf (binder : Nat) : Option String :=
    (lowering.names.find? (·.binder == binder)).bind fun name =>
      lowering.docs.lookup name.span.start
  let defs := lowering.names.filterMap fun name =>
    (binders.get? name.binder).map fun (ty, tyVars) => ({
      name := name.name, kind := "val",
      ty := tyParamsPrefix name.tyParams ++ showInfTy lowering.globals (name.tyVars ++ tyVars) ty,
      span := name.span, scope := name.scope, isDef := true,
      doc := lowering.docs.lookup name.span.start } : Symbol)
  let uses := facts.filterMap fun
    | .symbol symbol => some { symbol with doc := symbol.binder.bind docOf }
    | .binder .. => none
  let others := lowering.declSymbols ++ lowering.occurrences.map lowering.occurrenceSymbol
  let all := (defs.toArray ++ uses ++ others.toArray).map fun symbol =>
    if symbol.kind == "ctor" then lowering.withCtorInfo symbol else symbol
  let mut seen : Std.HashSet (String × String × Nat × Nat × Nat × Nat × Bool) := {}
  let mut symbols := #[]
  for symbol in all do
    let key := (symbol.kind, symbol.name, symbol.span.start.line, symbol.span.start.col,
      symbol.span.stop.line, symbol.span.stop.col, symbol.isDef)
    unless seen.contains key do
      seen := seen.insert key
      symbols := symbols.push symbol
  return symbols

/-- The top-level bindings and their types, in source order. -/
def Lowering.bindingTypes (lowering : Lowering) (symbols : Array Symbol) :
    List (String × String) :=
  let before (a b : NameInfo) : Bool :=
    a.span.start.line < b.span.start.line ||
      (a.span.start.line == b.span.start.line && a.span.start.col < b.span.start.col)
  let topLevel := (lowering.names.filter (·.topLevel)).mergeSort before
  topLevel.filterMap fun name =>
    (symbols.find? fun symbol => symbol.isDef && symbol.span == name.span).map fun symbol =>
      (name.name, symbol.ty)

/-! ## Error messages -/

def Keyword.describe : Keyword → String
  | .let => "let" | .in => "in" | .match => "match" | .with => "with"
  | .if => "if" | .then => "then" | .else => "else" | .type => "type"

def Punct.describe : Punct → String
  | .lparen => "(" | .rparen => ")" | .lbrace => "{" | .rbrace => "}"
  | .lbrack => "[" | .rbrack => "]" | .comma => "," | .colon => ":"
  | .eq => "=" | .pipe => "|" | .arrow => "->" | .backslash => "\\"
  | .underscore => "_"

def quote [Repr α] (value : α) : String := toString (repr value)

def Token.describe : Token → String
  | .ident name _ => s!"`{name}`"
  | .namedHole name => s!"`?{name}`"
  | .keyword kw => s!"`{kw.describe}`"
  | .int value => s!"`{value}`"
  | .char value => s!"`{quote value}`"
  | .string value => s!"`{quote value}`"
  | .op o => s!"`{o.describe}`"
  | .punct p => s!"`{p.describe}`"

def Expected.describe : Expected → String
  | .token tok => tok.describe
  | .expression => "an expression"
  | .pattern => "a pattern"
  | .type => "a type"
  | .parameter => "a parameter"
  | .typeName => "a type name"
  | .constructorName => "a constructor name"
  | .typeParameter => "a type parameter"
  | .endOfInput => "the end of the input"

def LexErrorReason.describe : LexErrorReason → String
  | .tab => "tabs are not allowed"
  | .unexpectedChar char => s!"unexpected character {quote char}"
  | .unterminatedComment => "unterminated block comment"
  | .unterminatedChar => "unterminated character literal"
  | .unterminatedString => "unterminated string literal"
  | .badEscape => "unknown escape sequence"

def ParseErrorReason.describe : ParseErrorReason → String
  | .expected what (some found) => s!"expected {what.describe}, found {found.describe}"
  | .expected what none => s!"expected {what.describe}, found the end of the input"
  | .infixChain => "operators do not chain: add parentheses"
  | .offside col => s!"this must be indented past column {col}"
  | .tooDeep => "the program is nested too deeply"

def LowerErrorReason.describe : LowerErrorReason → String
  | .unboundVariable name => s!"unbound variable `{name}`"
  | .unknownConstructor name => s!"unknown constructor `{name}`"
  | .unknownType name => s!"unknown type `{name}`"
  | .unboundTypeVariable name => s!"type variable `{name}` is not in scope"
  | .typeArity name expected actual =>
      s!"`{name}` takes {expected} type argument(s), but is given {actual}"
  | .patternArity name expected actual =>
      s!"`{name}` has {expected} field(s), but the pattern has {actual}"
  | .foreignPattern ctor type => s!"`{ctor}` is not a constructor of `{type}`"
  | .holeInDeclaration => "data declarations cannot have type holes"
  | .duplicateType name => s!"type `{name}` is already declared"
  | .duplicateConstructor name => s!"constructor `{name}` is already declared"
  | .duplicateTypeParameter name => s!"type parameter `{name}` is bound twice"
  | .duplicatePatternVariable name => s!"`{name}` is bound twice in this pattern"
  | .ctorTyVarArity name 0 _ => s!"`{name}` has no type variables of its own to name"
  | .ctorTyVarArity name expected actual =>
      s!"`{name}` has {expected} type variable(s) of its own, but the pattern names {actual}"
  | .duplicatePatternTypeVariable name => s!"type variable `{name}` is bound twice in this pattern"
  | .duplicateBinding name => s!"`{name}` is defined twice"
  | .mutualRecursion names =>
      s!"mutual recursion is not supported: {", ".intercalate names}"
  | .recursivePattern names =>
      s!"a pattern binding cannot be recursive: {", ".intercalate names}"
  | .redundantArm => "this arm is unreachable"
  | .tooDeep => "the program is nested too deeply"

/-- A hole's name as written: fresh names stand for `_`. -/
def holeName (name : String) : String :=
  if name.startsWith "_" then "_" else s!"?{name}"

def _root_.EPL.UnifyError.describe (showTy : InfTy → String) : UnifyError → String
  | .clash left right => s!"`{showTy left}` is not `{showTy right}`"
  | .occurs id ty => s!"`?{id}` would be the infinite type `{showTy ty}`"
  | .escape id ty => s!"`?{id}` cannot be `{showTy ty}`: a type variable would escape its scope"
  | .outOfFuel => "unification ran out of fuel"

def _root_.EPL.InferErrorReason.describe (showTy : InfTy → String) : InferErrorReason → String
  | .unboundVar => "unbound variable"
  | .unknownCtor => "unknown constructor"
  | .noBool => "comparisons need `Bool`"
  | .illScopedAnnotation => "this annotation mentions a type variable that is not in scope"
  | .emptyMatch => "a match needs an arm"
  | .unknownType => "unknown type in a pattern"
  | .foreignPattern => "this pattern's type differs from the others'"
  | .patternArity => "this pattern binds a different number of variables than its constructor has fields"
  | .mismatch expected actual (.clash left right) =>
      -- The cause only adds something if it is about parts of the types.
      if left = actual ∧ right = expected then
        s!"type mismatch: expected `{showTy expected}`, found `{showTy actual}`"
      else
        s!"type mismatch: expected `{showTy expected}`, found `{showTy actual}` \
          ({(UnifyError.clash left right).describe showTy})"
  | .mismatch expected actual cause =>
      s!"type mismatch: expected `{showTy expected}`, found `{showTy actual}` \
        ({cause.describe showTy})"
  | .ambiguousSignature holes =>
      s!"the definition does not determine {", ".intercalate (holes.map holeName)} in its signature"
  | .undeterminedType ty => s!"the program's type `{showTy ty}` is not determined"
  | .undeterminedAnnotation ty => s!"this binder's type `{showTy ty}` is not determined"

def Error.span : Error → Option Span
  | .lex error => some ⟨error.pos, error.pos⟩
  | .parse error => some error.span
  | .lower error => some error.span
  | .infer _ span .. | .notAFunction _ span .. => some span
  | .notExhaustive span _ => some span
  | .notExhaustiveUnlocated => none
  | .misplacedDoc span => some span

def Error.message : Error → String
  | .lex error => error.reason.describe
  | .parse error => error.reason.describe
  | .lower error => error.reason.describe
  | .infer globals _ tyVars error => error.reason.describe (showInfTy globals tyVars)
  | .notAFunction globals _ tyVars ty =>
      s!"this is applied to an argument, but its type `{showInfTy globals tyVars ty}` \
        is not a function type"
  | .notExhaustive _ ctor => s!"this match does not cover the case `{ctor}`"
  | .notExhaustiveUnlocated => "a match does not cover every case"
  | .misplacedDoc _ => "a doc comment must come before a `let`, a `type` or a constructor"

/-- `line:col: message` -/
def Error.render (error : Error) : String :=
  match error.span with
  | some span => s!"{span.start.line}:{span.start.col}: {error.message}"
  | none => error.message

/-- `value : type`, `<running> : type` if fuel ran out, or the error. -/
def runToString (source : String) (fuel : Nat := 100000) : String :=
  match run source fuel with
  | .ok (lowering, value, ty) =>
      let value := (value.map (showValue lowering.globals)).getD "<running>"
      s!"{value} : {showSemTy lowering.globals ty}"
  | .error error => error.render

/-- The program's type, or the error. -/
def checkToString (source : String) : String :=
  match check source with
  | .ok (lowering, result) => showSemTy lowering.globals result.ty
  | .error error => error.render

end EPL.Surface
