import Parser
import FHM.Surface.Lex
import FHM.SurfaceLang

namespace Surface.Parse

open Parser
open Surface.Lex (Token TokenWithSource LexError Keyword Punct BinOpToken)

/-! ## Errors -/

structure ParseError where
  msg : String
  line : Nat
  col : Nat
  deriving Repr

def lexToParse : LexError → ParseError
  | .tab line col => { msg := "tab character", line, col }
  | .unexpectedChar c line col => { msg := s!"unexpected character {repr c}", line, col }
  | .unfinishedBlockComment line col => { msg := "unfinished block comment", line, col }
  | .badEscape line col => { msg := "bad escape sequence", line, col }

/-! ## Token stream plumbing

Lex skips whitespace but still emits comment tokens. The parser skips those
so comments may carry spans later without affecting the grammar.
-/

abbrev Tok := TokenWithSource
abbrev TokStream := Subarray Tok
abbrev P := SimpleParser TokStream Tok

def isComment : Token → Bool
  | .lineComment _ | .blockComment _ => true
  | _ => false

def skipComments : P Unit :=
  dropMany <| tokenFilter (isComment ·.token)

/-- Map a stream index to source line/col (1-based). -/
def posOf (toks : Array Tok) (idx : Nat) : Nat × Nat :=
  if h : idx < toks.size then
    let t := toks[idx]
    (t.startLine, t.startCol)
  else
    match toks.back? with
    | some t => (t.endLine, t.endCol)
    | none => (1, 1)

def simpleErrToParse (toks : Array Tok) (e : Parser.Error.Simple TokStream Tok) : ParseError :=
  let rec go : Parser.Error.Simple TokStream Tok → ParseError
    | .unexpected idx _ =>
      let (line, col) := posOf toks idx
      { msg := "unexpected token", line, col }
    | .addMessage _ idx msg =>
      let (line, col) := posOf toks idx
      { msg := msg, line, col }
  go e

/-! ## Builtin type names (must match SurfaceBridge lowering) -/

/-- Map a surface type name to a primitive; `none` means customTy. Never emits `.nat`. -/
def primTyOf (name : String) : Option PrimTy :=
  match name with
  | "Int" => some .int
  | "Bool" => some .bool
  | "Char" => some .char
  | "Unit" => some .unit
  | _ => none

theorem primTyOf_Int : primTyOf "Int" = some .int := rfl
theorem primTyOf_Bool : primTyOf "Bool" = some .bool := rfl
theorem primTyOf_Char : primTyOf "Char" = some .char := rfl
theorem primTyOf_Unit : primTyOf "Unit" = some .unit := rfl
theorem primTyOf_Nat : primTyOf "Nat" = none := rfl
theorem primTyOf_Maybe : primTyOf "Maybe" = none := rfl

def tyOfUpperName (name : String) : Ty :=
  match primTyOf name with
  | some p => .prim p
  | none => .customTy (.mk name) []

theorem tyOfUpperName_Int : tyOfUpperName "Int" = .prim .int := rfl
theorem tyOfUpperName_Maybe : tyOfUpperName "Maybe" = .customTy (.mk "Maybe") [] := rfl

/-! ## Apply type arguments (juxtaposition) -/

/-- Attach args to a custom type head; reject prim / tvar / arrow / pair heads. -/
def applyTyArgs (head : Ty) (args : List Ty) : Except String Ty :=
  if args.isEmpty then .ok head
  else
    match head with
    | .customTy name existing => .ok (.customTy name (existing ++ args))
    | .prim _ => .error "primitive type cannot take arguments"
    | .tvar _ => .error "type variable cannot take arguments"
    | .arrow _ _ => .error "function type cannot take arguments"
    | .pair _ _ => .error "pair type cannot take arguments"

theorem applyTyArgs_empty (t : Ty) : applyTyArgs t [] = .ok t := by
  simp [applyTyArgs]

#guard (match applyTyArgs (.customTy (.mk "Maybe") []) [.prim .int] with
  | .ok (.customTy (.mk "Maybe") [.prim .int]) => true | _ => false)
#guard (match applyTyArgs (.prim .int) [.prim .bool] with
  | .error _ => true | _ => false)

/-! ## Low-level token matchers -/

def tokFilter (p : Token → Bool) : P Tok :=
  tokenFilter (p ·.token)

def punct (p : Punct) : P Tok :=
  tokFilter (· == .punct p)

def upperIdent : P String :=
  tokenMap fun t =>
    match t.token with
    | .ident raw true => some raw
    | _ => none

def lowerIdent : P String :=
  tokenMap fun t =>
    match t.token with
    | .ident raw false => some raw
    | _ => none

def anyIdent : P String :=
  tokenMap fun t =>
    match t.token with
    | .ident raw _ => some raw
    | _ => none

def intLitTok : P Int :=
  tokenMap fun t =>
    match t.token with
    | .intLit n => some n
    | _ => none

def boolLitTok : P Bool :=
  tokenMap fun t =>
    match t.token with
    | .boolLit b => some b
    | _ => none

def charLitTok : P Char :=
  tokenMap fun t =>
    match t.token with
    | .charLit c => some c
    | _ => none

def stringLitTok : P String :=
  tokenMap fun t =>
    match t.token with
    | .stringLit s => some s
    | _ => none

def binOpTok : P BinOpToken :=
  tokenMap fun t =>
    match t.token with
    | .op o => some o
    | _ => none

def keyword (kw : Keyword) : P Tok :=
  tokFilter (· == .keyword kw)

def consOp : P Tok :=
  tokFilter (· == .op .cons)

/-- Lower ident, also returning the source token (for column layout). -/
def lowerIdentTok : P (Tok × String) :=
  tokenMap fun t =>
    match t.token with
    | .ident raw false => some (t, raw)
    | _ => none

/-! ## Layout helpers (Tigris-style column guards) -/

/-- Peek the next non-comment token without consuming it. -/
def nextTok : P Tok := do
  skipComments
  peek

/-- Require the next token to start at exactly `col`. -/
def colEq (col : Nat) : P Unit := do
  let t ← nextTok
  if t.startCol != col then
    throwUnexpectedWithMessage none s!"expected column {col}"

/-- Require the next token to start strictly right of `col`. -/
def colGt (col : Nat) : P Unit := do
  let t ← nextTok
  if t.startCol ≤ col then
    throwUnexpectedWithMessage none s!"expected column > {col}"

/-! ## Type grammar

ASCII only:
* `tyAtom` — `()`, names, `(ty)`, `(ty, ty)`
* `tyApp`  — juxtaposition (`Maybe Int`); only `customTy` may take args
* `ty`     — right-assoc `tyApp -> ty`
* `polyTy` — `{ binders } ty` or bare `ty`
-/

instance : Inhabited Ty := ⟨.prim .unit⟩
instance : Inhabited PolyTy := ⟨⟨[], .prim .unit⟩⟩

mutual

partial def tyAtom : P Ty :=
  withErrorMessage "expected type atom" do
    skipComments
    first [
      -- `()` unit
      do
        let _ ← punct .lparen
        skipComments
        let _ ← punct .rparen
        return .prim .unit,
      -- `( ty )` or `( ty , ty )`
      do
        let _ ← punct .lparen
        skipComments
        let a ← ty
        skipComments
        match ← option? (punct .comma) with
        | some _ =>
          skipComments
          let b ← ty
          skipComments
          let _ ← punct .rparen
          return .pair a b
        | none =>
          let _ ← punct .rparen
          return a,
      -- upper name → prim or customTy
      do
        let name ← upperIdent
        return tyOfUpperName name,
      -- lower name → tvar
      do
        let name ← lowerIdent
        return .tvar (.mk name)
    ]

/-- One or more atoms; fold juxtaposition onto a customTy head. -/
partial def tyApp : P Ty :=
  withErrorMessage "expected type" do
    let head ← tyAtom
    let args ← takeMany (withBacktracking tyAtom)
    match applyTyArgs head args.toList with
    | .ok t => return t
    | .error msg => throwUnexpectedWithMessage none msg

/-- Right-associative arrows: `A -> B -> C` ≡ `A -> (B -> C)`. -/
partial def ty : P Ty :=
  withErrorMessage "expected type" do
    let left ← tyApp
    skipComments
    match ← option? (punct .arrow) with
    | some _ =>
      skipComments
      let right ← ty
      return .arrow left right
    | none => return left

end

/-- Scheme: `{a b} body` or bare `ty` (empty foralls). -/
partial def polyTy : P PolyTy :=
  withErrorMessage "expected type scheme" do
    skipComments
    match ← option? (punct .lbrace) with
    | some _ =>
      skipComments
      let binders ← takeMany1 (withBacktracking do
        skipComments
        anyIdent)
      skipComments
      let _ ← punct .rbrace
      skipComments
      let body ← ty
      return { foralls := binders.toList.map ValName.mk, body }
    | none =>
      let body ← ty
      return { foralls := [], body }

/-! ## Expression helpers -/

instance : Inhabited Expr := ⟨.primLit .unit⟩
instance : Inhabited Pattern := ⟨.wildcard⟩
instance : Inhabited ValName := ⟨.mk ""⟩
instance : Inhabited (Nat × ValName × Option PolyTy × Expr) :=
  ⟨(0, default, none, default)⟩
instance : Inhabited (Pattern × Expr) := ⟨(default, default)⟩

def applyBinOp (op : BinOpToken) (a b : Expr) : Expr :=
  match op with
  | .plus => .app (.app (.primBinOp .intAdd) a) b
  | .minus => .app (.app (.primBinOp .intSub) a) b
  | .lt => .app (.app (.primBinOp .intLt) a) b
  | .cons => .cons a b

/-- Simple λ/let binder: name or `_`. No type annotation (avoids `->` ambiguity). -/
def simpleBinder : P Pattern :=
  withErrorMessage "expected binder" do
    skipComments
    first [
      do
        let _ ← punct .underscore
        return .wildcard,
      do
        let name ← lowerIdent
        return .name (.mk name)
    ]

/-- `True`/`False` bool tokens as ctor patterns (Surface has no lit patterns). -/
def boolLitPattern : P Pattern :=
  tokenMap fun t =>
    match t.token with
    | .boolLit true => some (.ctor (.mk "True") [])
    | .boolLit false => some (.ctor (.mk "False") [])
    | _ => none

/-! ## Patterns (match only; right-assoc `::`)

* `patAtom` — `_`, name, bool ctor, `(p)`, `(p, p)`, `[ps]`, bare upper ctor
* `patApp`  — upper ctor with argument atoms
* `pattern` — right-assoc `::` chains
-/

mutual

partial def patAtom : P Pattern :=
  withErrorMessage "expected pattern atom" do
    skipComments
    first [
      do
        let _ ← punct .underscore
        return .wildcard,
      do
        boolLitPattern,
      do
        let name ← lowerIdent
        return .name (.mk name),
      -- `( p )` or `( p , p )`
      do
        let _ ← punct .lparen
        skipComments
        let a ← pattern
        skipComments
        match ← option? (punct .comma) with
        | some _ =>
          skipComments
          let b ← pattern
          skipComments
          let _ ← punct .rparen
          return .pair a b
        | none =>
          let _ ← punct .rparen
          return a,
      -- `[ p, … ]`
      do
        let _ ← punct .lbrack
        skipComments
        match ← option? (punct .rbrack) with
        | some _ => return .list []
        | none =>
          let hd ← pattern
          let tl ← takeMany (withBacktracking do
            skipComments
            let _ ← punct .comma
            skipComments
            pattern)
          skipComments
          let _ ← punct .rbrack
          return .list (hd :: tl.toList),
      -- bare upper ctor (no args); apps handled in `patApp`
      do
        let name ← upperIdent
        return .ctor (.mk name) []
    ]

/-- Ctor application: `Just x` / `Cons a b`, or a non-ctor atom. -/
partial def patApp : P Pattern :=
  withErrorMessage "expected pattern" do
    skipComments
    match ← option? (withBacktracking upperIdent) with
    | some name =>
      let args ← takeMany (withBacktracking patAtom)
      return .ctor (.mk name) args.toList
    | none => patAtom

/-- Right-associative cons: `a :: b :: rest` ≡ `cons a (cons b rest)`. -/
partial def pattern : P Pattern :=
  withErrorMessage "expected pattern" do
    let left ← patApp
    skipComments
    match ← option? (withBacktracking consOp) with
    | some _ =>
      skipComments
      let right ← pattern
      return .cons left right
    | none => return left

end

/-! ## Expression grammar

* `atom` — lit, var/ctor, `()`, `(e)`, `(e, e)`, `[es]`, `\ binders -> e`
* `appExpr` — left-assoc juxtaposition
* `infixExpr` — `appExpr` with optional single infix (`+`/`-`/`<`/`::`)
* `let` / `if` / `match` — soft-keyword forms at `expr` (not juxtaposition args)
* `expr` — let | if | match | infixExpr
-/

mutual

partial def atom : P Expr :=
  withErrorMessage "expected expression atom" do
    skipComments
    first [
      -- string lit: reject (no Surface string PrimLitExpr)
      do
        let _ ← stringLitTok
        throwUnexpectedWithMessage none "string literals are not supported in expressions",
      -- int / bool / char
      do
        let n ← intLitTok
        return .primLit (.int n),
      do
        let b ← boolLitTok
        return .primLit (.bool b),
      do
        let c ← charLitTok
        return .primLit (.char c),
      -- `()` unit
      do
        let _ ← punct .lparen
        skipComments
        let _ ← punct .rparen
        return .primLit .unit,
      -- `( e )` or `( e , e )`
      do
        let _ ← punct .lparen
        skipComments
        let a ← expr
        skipComments
        match ← option? (punct .comma) with
        | some _ =>
          skipComments
          let b ← expr
          skipComments
          let _ ← punct .rparen
          return .pair a b
        | none =>
          let _ ← punct .rparen
          return a,
      -- `[ e, … ]`
      do
        let _ ← punct .lbrack
        skipComments
        match ← option? (punct .rbrack) with
        | some _ => return .list []
        | none =>
          let hd ← expr
          let tl ← takeMany (withBacktracking do
            skipComments
            let _ ← punct .comma
            skipComments
            expr)
          skipComments
          let _ ← punct .rbrack
          return .list (hd :: tl.toList),
      -- `\ binder+ -> expr`
      do
        let _ ← punct .backslash
        skipComments
        let binders ← takeMany1 (withBacktracking simpleBinder)
        skipComments
        let _ ← punct .arrow
        skipComments
        let body ← expr
        return binders.toList.foldr (fun b acc => .lambda b none acc) body,
      -- lower → var
      do
        let name ← lowerIdent
        return .var (.mk name),
      -- upper → ctor
      do
        let name ← upperIdent
        return .ctor (.mk name)
    ]

/-- Left-associative juxtaposition: `f a b` ≡ `(f a) b`.
    Layout: args must share the head's line or start at a greater column
    (so a same-column sibling after a let RHS is not consumed as an app arg). -/
partial def appExpr : P Expr :=
  withErrorMessage "expected expression" do
    skipComments
    let headTok ← nextTok
    let head ← atom
    let args ← takeMany (withBacktracking do
      let t ← nextTok
      if t.startLine != headTok.startLine && t.startCol ≤ headTok.startCol then
        throwUnexpectedWithMessage none "app argument must be same line or indented"
      atom)
    return args.foldl (fun f a => .app f a) head

/-- Infix RHS: layout forms or an app — not another infix (keeps single-infix). -/
partial def infixRhs : P Expr :=
  first [letExpr, ifExpr, matchExpr, appExpr]

/-- Single optional infix; a second infix at this layer is an error. -/
partial def infixExpr : P Expr :=
  withErrorMessage "expected expression" do
    let left ← appExpr
    skipComments
    match ← option? (withBacktracking binOpTok) with
    | none => return left
    | some op =>
      skipComments
      let right ← infixRhs
      skipComments
      match ← option? (withBacktracking binOpTok) with
      | some _ =>
        throwUnexpectedWithMessage none "infix chaining requires parentheses"
      | none =>
        return applyBinOp op left right

/-- One `let` binding: `name [: polyTy] = expr`. Returns binder column. -/
partial def letBinding : P (Nat × ValName × Option PolyTy × Expr) :=
  withErrorMessage "expected let binding" do
    skipComments
    let (tok, name) ← lowerIdentTok
    let blockCol := tok.startCol
    skipComments
    let ann ← option? (withBacktracking do
      let _ ← punct .colon
      skipComments
      polyTy)
    skipComments
    let eqTok ← punct .eq
    skipComments
    -- RHS: same line as `=`, or indented past the binder column
    let t ← nextTok
    if t.startLine > eqTok.startLine then
      colGt blockCol
    let rhs ← expr
    return (blockCol, .mk name, ann, rhs)

/-- `let` bindings `in` body → nested `.letIn` (first binder outermost). -/
partial def letExpr : P Expr :=
  withErrorMessage "expected let expression" do
    skipComments
    let _ ← keyword .«let»
    let (blockCol, n0, ann0, rhs0) ← letBinding
    let rest ← takeMany (withBacktracking do
      colEq blockCol
      let (_, n, ann, rhs) ← letBinding
      return (n, ann, rhs))
    skipComments
    let _ ← keyword .«in»
    skipComments
    let body ← expr
    let binds := (n0, ann0, rhs0) :: rest.toList
    return binds.foldr (fun (n, ann, rhs) acc => .letIn n ann rhs acc) body

/-- `if e then e else e` → `.ife`. -/
partial def ifExpr : P Expr :=
  withErrorMessage "expected if expression" do
    skipComments
    let _ ← keyword .«if»
    skipComments
    let c ← expr
    skipComments
    let _ ← keyword .«then»
    skipComments
    let t ← expr
    skipComments
    let _ ← keyword .«else»
    skipComments
    let f ← expr
    return .ife c t f

/-- One match arm: `pattern -> expr`. -/
partial def matchArm : P (Pattern × Expr) := do
  skipComments
  let pat ← pattern
  skipComments
  let _ ← punct .arrow
  skipComments
  let body ← expr
  return (pat, body)

/-- F#-style `match e with [|] P -> e | Q -> e`.
    Leading `|` optional; later branches use `|`.
    Newline-aligned `|` must share the first branch column. -/
partial def matchExpr : P Expr :=
  withErrorMessage "expected match expression" do
    skipComments
    let _ ← keyword .«match»
    skipComments
    let scrut ← expr
    skipComments
    let _ ← keyword .«with»
    skipComments
    let leadPipe? ← option? (withBacktracking (punct .pipe))
    skipComments
    let t ← nextTok
    let blockCol :=
      match leadPipe? with
      | some p => p.startCol
      | none => t.startCol
    let blockLine :=
      match leadPipe? with
      | some p => p.startLine
      | none => t.startLine
    let arm0 ← matchArm
    let rest ← takeMany (withBacktracking do
      skipComments
      let pipe ← nextTok
      if pipe.token != .punct .pipe then
        throwUnexpected
      if pipe.startLine > blockLine && pipe.startCol != blockCol then
        throwUnexpectedWithMessage none "match branch misaligned"
      let _ ← punct .pipe
      matchArm)
    return .match_ scrut (arm0 :: rest.toList)

/-- Top expression: layout forms or infix/app. -/
partial def expr : P Expr :=
  withErrorMessage "expected expression" do
    skipComments
    first [
      letExpr,
      ifExpr,
      matchExpr,
      infixExpr
    ]

end

/-! ## Public API -/

def runTokP (p : P α) (toks : Array Tok) : Except ParseError α :=
  match Parser.run (skipComments *> p <* skipComments <* endOfInput) toks.toSubarray with
  | .ok _ v => .ok v
  | .error _ e => .error (simpleErrToParse toks e)

def runLexParse (p : P α) (src : String) : Except ParseError α :=
  match Lex.lex src with
  | .error e => .error (lexToParse e)
  | .ok toks => runTokP p toks

def parseTy (src : String) : Except ParseError Ty :=
  runLexParse ty src

def parsePolyTy (src : String) : Except ParseError PolyTy :=
  runLexParse polyTy src

def parseExpr (src : String) : Except ParseError Expr :=
  runLexParse expr src

/-! ## Inline checks -/

#guard (parseTy "Int").isOk
#guard (parseTy "Int -> Bool").isOk
#guard (parseTy "(Int, Bool)").isOk

#guard (match parseTy "Int" with
  | .ok (.prim .int) => true | _ => false)
#guard (match parseTy "Bool" with
  | .ok (.prim .bool) => true | _ => false)
#guard (match parseTy "Char" with
  | .ok (.prim .char) => true | _ => false)
#guard (match parseTy "Unit" with
  | .ok (.prim .unit) => true | _ => false)
#guard (match parseTy "()" with
  | .ok (.prim .unit) => true | _ => false)
#guard (match parseTy "a" with
  | .ok (.tvar (.mk "a")) => true | _ => false)
#guard (match parseTy "Maybe" with
  | .ok (.customTy (.mk "Maybe") []) => true | _ => false)
#guard (match parseTy "Maybe Int" with
  | .ok (.customTy (.mk "Maybe") [.prim .int]) => true | _ => false)
#guard (match parseTy "Either Int Bool" with
  | .ok (.customTy (.mk "Either") [.prim .int, .prim .bool]) => true | _ => false)
#guard (match parseTy "Int -> Bool -> Char" with
  | .ok (.arrow (.prim .int) (.arrow (.prim .bool) (.prim .char))) => true | _ => false)
#guard (match parseTy "(Int, Bool) -> Unit" with
  | .ok (.arrow (.pair (.prim .int) (.prim .bool)) (.prim .unit)) => true | _ => false)
#guard (match parseTy "(Int -> Bool)" with
  | .ok (.arrow (.prim .int) (.prim .bool)) => true | _ => false)

-- prims / tvars must not take args
#guard (match parseTy "Int Bool" with | .error _ => true | _ => false)
#guard (match parseTy "a Int" with | .error _ => true | _ => false)

-- Nat is custom (never prim .nat)
#guard (match parseTy "Nat" with
  | .ok (.customTy (.mk "Nat") []) => true | _ => false)

-- comments skipped
#guard (match parseTy "Int {- x -} -> Bool" with
  | .ok (.arrow (.prim .int) (.prim .bool)) => true | _ => false)
#guard (match parseTy "-- c\nInt" with
  | .ok (.prim .int) => true | _ => false)

#guard (match parsePolyTy "{a} a -> a" with
  | .ok ⟨[.mk "a"], .arrow (.tvar (.mk "a")) (.tvar (.mk "a"))⟩ => true
  | _ => false)
#guard (match parsePolyTy "{a b} a -> b" with
  | .ok ⟨[.mk "a", .mk "b"], .arrow (.tvar (.mk "a")) (.tvar (.mk "b"))⟩ => true
  | _ => false)
#guard (match parsePolyTy "Int -> Bool" with
  | .ok ⟨[], .arrow (.prim .int) (.prim .bool)⟩ => true
  | _ => false)
#guard (match parsePolyTy "{}" with | .error _ => true | _ => false)

-- lex errors surface as ParseError
#guard (match parseTy "\t" with
  | .error ⟨"tab character", 1, 1⟩ => true | _ => false)

/-! ### Expression checks -/

#guard (parseExpr "1").isOk
#guard (parseExpr "-3").isOk
#guard (parseExpr "True").isOk
#guard (parseExpr "\\x y -> x").isOk
#guard (parseExpr "f a b").isOk
#guard (match parseExpr "1 + 2" with
  | .ok (.app (.app (.primBinOp .intAdd) (.primLit (.int 1))) (.primLit (.int 2))) => true
  | _ => false)
#guard (parseExpr "a :: (b :: c)").isOk
#guard (match parseExpr "a + b + c" with | .error _ => true | _ => false)
#guard (parseExpr "(a + b) + c").isOk

-- exact shapes
#guard (match parseExpr "1" with
  | .ok (.primLit (.int 1)) => true | _ => false)
#guard (match parseExpr "-3" with
  | .ok (.primLit (.int (-3))) => true | _ => false)
#guard (match parseExpr "True" with
  | .ok (.primLit (.bool true)) => true | _ => false)
#guard (match parseExpr "False" with
  | .ok (.primLit (.bool false)) => true | _ => false)
#guard (match parseExpr "()" with
  | .ok (.primLit .unit) => true | _ => false)
#guard (match parseExpr "'a'" with
  | .ok (.primLit (.char 'a')) => true | _ => false)
#guard (match parseExpr "x" with
  | .ok (.var (.mk "x")) => true | _ => false)
#guard (match parseExpr "Just" with
  | .ok (.ctor (.mk "Just")) => true | _ => false)
#guard (match parseExpr "f a b" with
  | .ok (.app (.app (.var (.mk "f")) (.var (.mk "a"))) (.var (.mk "b"))) => true
  | _ => false)
#guard (match parseExpr "\\x y -> x" with
  | .ok (.lambda (.name (.mk "x")) none
      (.lambda (.name (.mk "y")) none (.var (.mk "x")))) => true
  | _ => false)
#guard (match parseExpr "\\_ -> ()" with
  | .ok (.lambda .wildcard none (.primLit .unit)) => true
  | _ => false)
#guard (match parseExpr "[1, 2]" with
  | .ok (.list [.primLit (.int 1), .primLit (.int 2)]) => true
  | _ => false)
#guard (match parseExpr "[]" with
  | .ok (.list []) => true | _ => false)
#guard (match parseExpr "(1, True)" with
  | .ok (.pair (.primLit (.int 1)) (.primLit (.bool true))) => true
  | _ => false)
#guard (match parseExpr "a :: (b :: c)" with
  | .ok (.cons (.var (.mk "a"))
      (.cons (.var (.mk "b")) (.var (.mk "c")))) => true
  | _ => false)
#guard (match parseExpr "1 - 2" with
  | .ok (.app (.app (.primBinOp .intSub) (.primLit (.int 1))) (.primLit (.int 2))) => true
  | _ => false)
#guard (match parseExpr "1 < 2" with
  | .ok (.app (.app (.primBinOp .intLt) (.primLit (.int 1))) (.primLit (.int 2))) => true
  | _ => false)
#guard (match parseExpr "(a + b) + c" with
  | .ok (.app (.app (.primBinOp .intAdd)
      (.app (.app (.primBinOp .intAdd) (.var (.mk "a"))) (.var (.mk "b"))))
      (.var (.mk "c"))) => true
  | _ => false)

-- rejects
#guard (match parseExpr "\"hi\"" with | .error _ => true | _ => false)
#guard (match parseExpr "a :: b :: c" with | .error _ => true | _ => false)

-- comments skipped
#guard (match parseExpr "1 {- x -} + 2" with
  | .ok (.app (.app (.primBinOp .intAdd) (.primLit (.int 1))) (.primLit (.int 2))) => true
  | _ => false)

/-! ### Layout: let / if / match -/

#guard (parseExpr "let x = 1 in x").isOk
#guard (parseExpr "if True then 1 else 0").isOk
#guard (parseExpr "match True with | True -> 1 | False -> 0").isOk
#guard (parseExpr "match True with True -> 1 | False -> 0").isOk
#guard (match parseExpr "match xs with | a :: b :: rest -> a" with | .ok _ => true | _ => false)

#guard (match parseExpr "let x = 1 in x" with
  | .ok (.letIn (.mk "x") none (.primLit (.int 1)) (.var (.mk "x"))) => true
  | _ => false)
#guard (match parseExpr "if True then 1 else 0" with
  | .ok (.ife (.primLit (.bool true)) (.primLit (.int 1)) (.primLit (.int 0))) => true
  | _ => false)
#guard (match parseExpr "match True with | True -> 1 | False -> 0" with
  | .ok (.match_ (.primLit (.bool true))
      [(.ctor (.mk "True") [], .primLit (.int 1)),
       (.ctor (.mk "False") [], .primLit (.int 0))]) => true
  | _ => false)
#guard (match parseExpr "match True with True -> 1 | False -> 0" with
  | .ok (.match_ (.primLit (.bool true))
      [(.ctor (.mk "True") [], .primLit (.int 1)),
       (.ctor (.mk "False") [], .primLit (.int 0))]) => true
  | _ => false)
#guard (match parseExpr "match xs with | a :: b :: rest -> a" with
  | .ok (.match_ (.var (.mk "xs"))
      [(.cons (.name (.mk "a")) (.cons (.name (.mk "b")) (.name (.mk "rest"))),
        .var (.mk "a"))]) => true
  | _ => false)

-- multi-line let: same-column sibling bindings → nested letIn
#guard (match parseExpr "let x = 1\n    y = 2\nin x" with
  | .ok (.letIn (.mk "x") none (.primLit (.int 1))
      (.letIn (.mk "y") none (.primLit (.int 2)) (.var (.mk "x")))) => true
  | _ => false)

-- optional `: polyTy` on let binder
#guard (match parseExpr "let x : Int = 1 in x" with
  | .ok (.letIn (.mk "x") (some ⟨[], .prim .int⟩) (.primLit (.int 1)) (.var (.mk "x"))) => true
  | _ => false)

-- ctor pattern with args
#guard (match parseExpr "match v with | Just x -> x | Nothing -> 0" with
  | .ok (.match_ (.var (.mk "v"))
      [(.ctor (.mk "Just") [.name (.mk "x")], .var (.mk "x")),
       (.ctor (.mk "Nothing") [], .primLit (.int 0))]) => true
  | _ => false)

end Surface.Parse
