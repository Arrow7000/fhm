import EPL.Surface.Lex

/-!
# Parser

Predictive recursive descent over the tokens, in FHM's grammar. It stops at
the first error. Every function takes fuel; each call either consumes a token
or descends a bounded number of grammar levels first, so `8 * tokens + 16` is
always enough (running out is reported as `tooDeep`, which does not happen).

Layout, as in FHM:
* an application's arguments are on its head's line or indented past its head;
* the bindings of one `let` block start in the same column;
* a right-hand side that starts on a later line than its `=` is indented past
  the binding's `let` (or, in a block, past the block's column);
* a `match` arm on a later line starts its `|` in the column of the first arm;
* a constructor's fields are indented past its declaration's `type`.

Infix operators do not chain: `a + b + c` needs parentheses.
-/

namespace EPL.Surface

/-- What the parser was looking for. -/
inductive Expected where
  | token (token : Token)
  | expression
  | pattern
  | type
  | parameter
  | typeName
  | constructorName
  | typeParameter
  | endOfInput
  deriving DecidableEq, Repr

inductive ParseErrorReason where
  /-- `found` is `none` at the end of the input. -/
  | expected (what : Expected) (found : Option Token)
  /-- A second infix operator without parentheses: `a + b + c`. -/
  | infixChain
  /-- A right-hand side on a later line must be indented past column `col`. -/
  | offside (col : Nat)
  /-- Unreachable: the parser always has enough fuel. -/
  | tooDeep
  deriving DecidableEq, Repr

structure ParseError where
  span : Span
  reason : ParseErrorReason
  deriving DecidableEq, Repr

abbrev P := ReaderT (Array Tok) (StateT Nat (Except ParseError))

namespace Parse

def peek : P (Option Tok) := do return (← read)[← get]?

def peekToken : P (Option Token) := do return (← peek).map (·.token)

def peekAt (offset : Nat) : P (Option Tok) := do return (← read)[(← get) + offset]?

def bump : P Unit := modify (· + 1)

/-- An empty span just after the last token. -/
def endSpan : P Span := do
  match (← read).back? with
  | some tok => return ⟨tok.span.stop, tok.span.stop⟩
  | none => return ⟨⟨1, 1⟩, ⟨1, 1⟩⟩

/-- The span of the next token, or `endSpan`. -/
def nextSpan : P Span := do
  match ← peek with
  | some tok => return tok.span
  | none => endSpan

def startPos : P Pos := return (← nextSpan).start

/-- The end of the last consumed token. -/
def prevStop : P Pos := do
  let i ← get
  match (← read)[i - 1]? with
  | some tok => if i = 0 then return tok.span.start else return tok.span.stop
  | none => return ⟨1, 1⟩

def spanFrom (start : Pos) : P Span := return ⟨start, ← prevStop⟩

def fail (reason : ParseErrorReason) : P α := do throw ⟨← nextSpan, reason⟩

def expected (what : Expected) : P α := do
  match ← peek with
  | some tok => throw ⟨tok.span, .expected what (some tok.token)⟩
  | none => throw ⟨← endSpan, .expected what none⟩

def tooDeep : P α := fail .tooDeep

def nextIs (token : Token) : P Bool := do
  return (← peek).any (·.token == token)

def accept (token : Token) : P (Option Tok) := do
  match ← peek with
  | some tok => if tok.token = token then bump; return some tok else return none
  | none => return none

def expect (token : Token) : P Tok := do
  match ← accept token with
  | some tok => return tok
  | none => expected (.token token)

def upperName (what : Expected) : P (Tok × String) := do
  match ← peek with
  | some tok@{ token := .ident name true, .. } => bump; return (tok, name)
  | _ => expected what

def lowerName (what : Expected) : P (Tok × String) := do
  match ← peek with
  | some tok@{ token := .ident name false, .. } => bump; return (tok, name)
  | _ => expected what

/-- Identifiers up to `}` (at least one), after `{`, with their spans. -/
def binderNames : Nat → P (List (String × Span))
  | 0 => tooDeep
  | n + 1 => do
    match ← peek with
    | some { token := .ident name _, span } =>
        bump
        if ← nextIs (.punct .rbrace) then bump; return [(name, span)]
        return (name, span) :: (← binderNames n)
    | _ => expected .typeParameter

/-! ## Types -/

def startsTyAtom : Token → Bool
  | .punct .underscore | .namedHole _ | .punct .lparen | .ident _ _ => true
  | _ => false

mutual
def tyAtom : Nat → P Ty
  | 0 => tooDeep
  | n + 1 => do
    let some tok ← peek | expected .type
    match tok.token with
    | .punct .underscore => bump; return .hole tok.span
    | .namedHole name => bump; return .namedHole tok.span name
    | .ident name true => bump; return .con tok.span name []
    | .ident name false => bump; return .var tok.span name
    | .punct .lparen =>
        bump
        if let some close ← accept (.punct .rparen) then
          return .unit (tok.span.union close.span)
        let fst ← ty n
        if (← accept (.punct .comma)).isSome then
          let snd ← ty n
          let close ← expect (.punct .rparen)
          return .pair (tok.span.union close.span) fst snd
        let _ ← expect (.punct .rparen)
        return fst
    | _ => expected .type

/-- Type atoms, as long as the next token starts one. -/
def tyArgs : Nat → P (List Ty)
  | 0 => tooDeep
  | n + 1 => do
    match ← peek with
    | some tok =>
        if startsTyAtom tok.token then
          let arg ← tyAtom n
          return arg :: (← tyArgs n)
        else return []
    | none => return []

/-- An atom; a bare type name takes the following atoms as arguments. -/
def tyApp : Nat → P Ty
  | 0 => tooDeep
  | n + 1 => do
    let head ← tyAtom n
    match head with
    | .con span name [] =>
        let args ← tyArgs n
        return .con ⟨span.start, (args.getLast?.map (·.span.stop)).getD span.stop⟩ name args
    | _ => return head

/-- Right-associative arrows. -/
def ty : Nat → P Ty
  | 0 => tooDeep
  | n + 1 => do
    let domain ← tyApp n
    if (← accept (.punct .arrow)).isSome then
      let codomain ← ty n
      return .arrow (domain.span.union codomain.span) domain codomain
    return domain
end

/-- `{a b} ty` or `ty`. -/
def polyTy (n : Nat) : P PolyTy := do
  if (← accept (.punct .lbrace)).isSome then
    let binders ← binderNames n
    return ⟨binders.map (·.1), ← ty n, binders.map (·.2)⟩
  return ⟨[], ← ty n, []⟩

/-! ## Patterns -/

def startsPatAtom : Token → Bool
  | .punct .underscore | .ident _ _ | .punct .lparen | .punct .lbrack => true
  | _ => false

mutual
/-- `_`, a name, a bare constructor, `(p)`, `(p, q)` or `[p, ...]`. -/
def patAtom : Nat → P Pattern
  | 0 => tooDeep
  | n + 1 => do
    let some tok ← peek | expected .pattern
    match tok.token with
    | .punct .underscore => bump; return .wildcard tok.span
    | .ident name false => bump; return .var tok.span name
    | .ident name true => bump; return .ctor tok.span name []
    | .punct .lparen =>
        bump
        let fst ← pattern n
        if (← accept (.punct .comma)).isSome then
          let snd ← pattern n
          let close ← expect (.punct .rparen)
          return .pair (tok.span.union close.span) fst snd
        let _ ← expect (.punct .rparen)
        return fst
    | .punct .lbrack =>
        bump
        if let some close ← accept (.punct .rbrack) then
          return .list (tok.span.union close.span) []
        let first ← pattern n
        let rest ← patItems n
        let close ← expect (.punct .rbrack)
        return .list (tok.span.union close.span) (first :: rest)
    | _ => expected .pattern

/-- `, p` repeated. -/
def patItems : Nat → P (List Pattern)
  | 0 => tooDeep
  | n + 1 => do
    if (← accept (.punct .comma)).isSome then
      let item ← pattern n
      return item :: (← patItems n)
    return []

def patArgs : Nat → P (List Pattern)
  | 0 => tooDeep
  | n + 1 => do
    match ← peek with
    | some tok =>
        if startsPatAtom tok.token then
          let arg ← patAtom n
          return arg :: (← patArgs n)
        else return []
    | none => return []

/-- A constructor applied to atoms, or an atom. -/
def patApp : Nat → P Pattern
  | 0 => tooDeep
  | n + 1 => do
    match ← peek with
    | some tok@{ token := .ident name true, .. } =>
        bump
        let args ← patArgs n
        return .ctor ⟨tok.span.start, (args.getLast?.map (·.span.stop)).getD tok.span.stop⟩
          name args
    | _ => patAtom n

/-- Right-associative `::`. -/
def pattern : Nat → P Pattern
  | 0 => tooDeep
  | n + 1 => do
    let head ← patApp n
    if (← accept (.op .cons)).isSome then
      let tail ← pattern n
      return .cons (head.span.union tail.span) head tail
    return head
end

/-! ## Expressions -/

def startsAtom : Token → Bool
  | .int _ | .char _ | .string _ | .ident _ _ | .punct .lparen | .punct .lbrack
  | .punct .backslash => true
  | _ => false

/-- Can start a `let` binding. -/
def startsBinding : Token → Bool
  | .ident _ _ | .punct .lparen | .punct .lbrack | .punct .underscore => true
  | _ => false

def binOpOf : Token → Option BinOp
  | .op op => some op
  | _ => none

/-- `x`, `_`, `(x : ty)` or `(_ : ty)`. -/
def valueParam (n : Nat) : P ValueParam := do
  let some tok ← peek | expected .parameter
  match tok.token with
  | .punct .underscore => bump; return ⟨tok.span, none, none, tok.span⟩
  | .ident name false => bump; return ⟨tok.span, some name, none, tok.span⟩
  | .punct .lparen =>
      bump
      let (name, nameSpan) ← match ← peek with
        | some { token := .punct .underscore, span } => bump; pure (none, span)
        | some { token := .ident name false, span } => bump; pure (some name, span)
        | _ => expected .parameter
      let _ ← expect (.punct .colon)
      let ann ← ty n
      let close ← expect (.punct .rparen)
      return ⟨tok.span.union close.span, name, some ann, nameSpan⟩
  | _ => expected .parameter

/-- Function-head parameters, up to `:` or `=`. -/
def valueParams : Nat → P (List ValueParam)
  | 0 => tooDeep
  | n + 1 => do
    if (← nextIs (.punct .colon)) || (← nextIs (.punct .eq)) then return []
    let param ← valueParam n
    return param :: (← valueParams n)

/-- A lambda parameter: a pattern atom, or `(p : ty)`. -/
def lambdaParam (n : Nat) : P Param := do
  let some tok ← peek | expected .parameter
  match tok.token with
  | .punct .lparen =>
      bump
      let fst ← pattern n
      if (← accept (.punct .colon)).isSome then
        let ann ← ty n
        let close ← expect (.punct .rparen)
        return ⟨tok.span.union close.span, fst, some ann⟩
      if (← accept (.punct .comma)).isSome then
        let snd ← pattern n
        let close ← expect (.punct .rparen)
        let span := tok.span.union close.span
        return ⟨span, .pair span fst snd, none⟩
      let close ← expect (.punct .rparen)
      return ⟨tok.span.union close.span, fst, none⟩
  | _ =>
      let pattern ← patAtom n
      return ⟨pattern.span, pattern, none⟩

def lambdaParams : Nat → P (List Param)
  | 0 => tooDeep
  | n + 1 => do
    let param ← lambdaParam n
    if ← nextIs (.punct .arrow) then return [param]
    return param :: (← lambdaParams n)

/-- A binding's target and annotation, up to and including `=`. -/
def bindingHead (n : Nat) : P (Binding × Tok) := do
  let start ← startPos
  let (target, tyParams) ← match ← peek with
    | some { token := .ident name false, span } =>
        bump
        let tyParams ← if (← accept (.punct .lbrace)).isSome then binderNames n else pure []
        pure (.named name (tyParams.map (·.1)) (← valueParams n) span, tyParams)
    | _ => do pure (.pattern (← pattern n), [])
  let ann ← if (← accept (.punct .colon)).isSome then some <$> polyTy n else pure none
  let eq ← expect (.punct .eq)
  return ({ span := ⟨start, eq.span.stop⟩, target, ann, tyParamSpans := tyParams.map (·.2) }, eq)

/-- A right-hand side on a later line than `eq` must start past `col`. -/
def checkIndent (eq : Tok) (col : Nat) : P Unit := do
  if let some tok ← peek then
    if tok.span.start.line > eq.span.start.line && tok.span.start.col ≤ col then
      fail (.offside col)

mutual
def expr : Nat → P Expr
  | 0 => tooDeep
  | n + 1 => do
    match ← peekToken with
    | some (.keyword .let) => letExpr n
    | some (.keyword .if) => ifExpr n
    | some (.keyword .match) => matchExpr n
    | _ => infixExpr n

/-- An application, optionally followed by one operator and its right operand. -/
def infixExpr : Nat → P Expr
  | 0 => tooDeep
  | n + 1 => do
    let left ← appExpr n
    let some opTok ← peek | return left
    let some op := binOpOf opTok.token | return left
    bump
    let right ← match ← peekToken with
      | some (.keyword .let) => letExpr n
      | some (.keyword .if) => ifExpr n
      | some (.keyword .match) => matchExpr n
      | _ => appExpr n
    if let some next ← peek then
      if (binOpOf next.token).isSome then throw ⟨next.span, .infixChain⟩
    return .binOp (left.span.union right.span) op left right

def appExpr : Nat → P Expr
  | 0 => tooDeep
  | n + 1 => do
    let head ← atom n
    appArgs head.span.start head n

/-- Arguments on the head's line, or indented past it. -/
def appArgs (headStart : Pos) (function : Expr) : Nat → P Expr
  | 0 => tooDeep
  | n + 1 => do
    let some tok ← peek | return function
    if startsAtom tok.token &&
        (tok.span.start.line == headStart.line || tok.span.start.col > headStart.col) then
      let argument ← atom n
      appArgs headStart (.app (function.span.union argument.span) function argument) n
    else return function

def atom : Nat → P Expr
  | 0 => tooDeep
  | n + 1 => do
    let some tok ← peek | expected .expression
    match tok.token with
    | .int value => bump; return .int tok.span value
    | .char value => bump; return .char tok.span value
    | .string value => bump; return .string tok.span value
    | .ident name false => bump; return .var tok.span name
    | .ident name true => bump; return .ctor tok.span name
    | .punct .lparen =>
        bump
        if let some close ← accept (.punct .rparen) then
          return .unit (tok.span.union close.span)
        let fst ← expr n
        if (← accept (.punct .comma)).isSome then
          let snd ← expr n
          let close ← expect (.punct .rparen)
          return .pair (tok.span.union close.span) fst snd
        let _ ← expect (.punct .rparen)
        return fst
    | .punct .lbrack =>
        bump
        if let some close ← accept (.punct .rbrack) then
          return .list (tok.span.union close.span) []
        let first ← expr n
        let rest ← exprItems n
        let close ← expect (.punct .rbrack)
        return .list (tok.span.union close.span) (first :: rest)
    | .punct .backslash =>
        bump
        let params ← lambdaParams n
        let _ ← expect (.punct .arrow)
        let body ← expr n
        let inner := params.foldr (init := body) fun param body =>
          .lambda (param.span.union body.span) param body
        return match inner with
          | .lambda _ param body => .lambda (tok.span.union body.span) param body
          | other => other
    | _ => expected .expression

/-- `, e` repeated. -/
def exprItems : Nat → P (List Expr)
  | 0 => tooDeep
  | n + 1 => do
    if (← accept (.punct .comma)).isSome then
      let item ← expr n
      return item :: (← exprItems n)
    return []

/-- One binding: its head, `=`, and its right-hand side, which must be indented
past `col` if it starts on a later line. -/
def binding (col : Nat) : Nat → P (Binding × Expr)
  | 0 => tooDeep
  | n + 1 => do
    let (binding, eq) ← bindingHead n
    checkIndent eq col
    return (binding, ← expr n)

/-- Further bindings of a block, each starting in column `col`. -/
def moreBindings (col : Nat) : Nat → P (List (Binding × Expr))
  | 0 => tooDeep
  | n + 1 => do
    let some tok ← peek | return []
    if tok.span.start.col == col && startsBinding tok.token then
      let first ← binding col n
      return first :: (← moreBindings col n)
    return []

def letExpr : Nat → P Expr
  | 0 => tooDeep
  | n + 1 => do
    let letTok ← expect (.keyword .let)
    let col := (← startPos).col
    let first ← binding letTok.span.start.col n
    let rest ← moreBindings col n
    let _ ← expect (.keyword .in)
    let body ← expr n
    return .letIn (letTok.span.union body.span) (first :: rest) body

def ifExpr : Nat → P Expr
  | 0 => tooDeep
  | n + 1 => do
    let ifTok ← expect (.keyword .if)
    let cond ← expr n
    let _ ← expect (.keyword .then)
    let thenBranch ← expr n
    let _ ← expect (.keyword .else)
    let elseBranch ← expr n
    return .ite (ifTok.span.union elseBranch.span) cond thenBranch elseBranch

def arm : Nat → P (Pattern × Expr)
  | 0 => tooDeep
  | n + 1 => do
    let pat ← pattern n
    let _ ← expect (.punct .arrow)
    return (pat, ← expr n)

/-- Further arms: a `|` on the first arm's line, or in its column. -/
def moreArms (blockStart : Pos) : Nat → P (List (Pattern × Expr))
  | 0 => tooDeep
  | n + 1 => do
    let some tok ← peek | return []
    if tok.token == .punct .pipe &&
        (tok.span.start.line ≤ blockStart.line || tok.span.start.col == blockStart.col) then
      bump
      let first ← arm n
      return first :: (← moreArms blockStart n)
    return []

def matchExpr : Nat → P Expr
  | 0 => tooDeep
  | n + 1 => do
    let matchTok ← expect (.keyword .match)
    let scrutinee ← expr n
    let _ ← expect (.keyword .with)
    let blockStart ← startPos
    let _ ← accept (.punct .pipe)
    let first ← arm n
    let rest ← moreArms blockStart n
    let arms := first :: rest
    let stop := (arms.getLast?.map (·.2.span)).getD first.2.span
    return .match (matchTok.span.union stop) scrutinee arms
end

/-! ## Programs -/

/-- A constructor field: an atom, or `(name : ty)` (the name is ignored). Fields
on later lines must be indented past `declCol`. -/
def ctorFields (declCol : Nat) : Nat → P (List Ty)
  | 0 => tooDeep
  | n + 1 => do
    let some tok ← peek | return []
    if !(startsTyAtom tok.token && tok.span.start.col > declCol) then return []
    let named := tok.token == .punct .lparen &&
      ((← peekAt 1).any fun t => match t.token with | .ident .. => true | _ => false) &&
      ((← peekAt 2).any (·.token == .punct .colon))
    let field ← if named then do
        bump; bump; bump
        let field ← ty n
        let _ ← expect (.punct .rparen)
        pure field
      else tyAtom n
    return field :: (← ctorFields declCol n)

def ctorDecl (declCol : Nat) (n : Nat) : P CtorDecl := do
  let (tok, name) ← upperName .constructorName
  let fields ← ctorFields declCol n
  return ⟨← spanFrom tok.span.start, name, fields⟩

def moreCtors (declCol : Nat) : Nat → P (List CtorDecl)
  | 0 => tooDeep
  | n + 1 => do
    if (← accept (.punct .pipe)).isSome then
      let ctor ← ctorDecl declCol n
      return ctor :: (← moreCtors declCol n)
    return []

def lowerNames : Nat → P (List (String × Span))
  | 0 => tooDeep
  | n + 1 => do
    match ← peek with
    | some { token := .ident name false, span } => bump; return (name, span) :: (← lowerNames n)
    | _ => return []

/-- `type T a b = C fields | ...` -/
def typeDecl (n : Nat) : P DataDecl := do
  let typeTok ← expect (.keyword .type)
  let (nameTok, name) ← upperName .typeName
  let params ← lowerNames n
  let _ ← expect (.punct .eq)
  let _ ← accept (.punct .pipe)
  let first ← ctorDecl typeTok.span.start.col n
  let rest ← moreCtors typeTok.span.start.col n
  return { span := ← spanFrom typeTok.span.start, name, params := params.map (·.1),
           ctors := first :: rest, nameSpan := nameTok.span, paramSpans := params.map (·.2) }

/-- Top-level `type` declarations and `let` bindings, in any order. -/
def items : Nat → P (List DataDecl × List (Binding × Expr))
  | 0 => tooDeep
  | n + 1 => do
    match ← peekToken with
    | some (.keyword .type) =>
        let decl ← typeDecl n
        let (decls, bindings) ← items n
        return (decl :: decls, bindings)
    | some (.keyword .let) =>
        let letTok ← expect (.keyword .let)
        let first ← binding letTok.span.start.col n
        let (decls, bindings) ← items n
        return (decls, first :: bindings)
    | _ => return ([], [])

def program (n : Nat) : P Program := do
  let (decls, bindings) ← items n
  let body ← if (← peek).isNone then pure (.unit (← endSpan)) else expr n
  if (← peek).isSome then expected .endOfInput
  return ⟨decls, bindings, body⟩

end Parse

def runParser (parser : Nat → P α) (tokens : Array Tok) : Except ParseError α :=
  (parser (8 * tokens.size + 16) |>.run tokens |>.run' 0)

def parseProgram (tokens : Array Tok) : Except ParseError Program :=
  runParser Parse.program tokens

end EPL.Surface
