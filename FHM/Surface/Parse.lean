import Parser
import FHM.Surface.Lex
import FHM.Surface.Span
import FHM.SurfaceLang
import FHM.SurfaceBridge

namespace Surface.Parse

open Parser
open Surface.Lex (Token TokenWithSource LexError Keyword Punct BinOpToken)
open Surface.Span (Span BinderKind BinderSpan)

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

/-- Attach args to a bare custom type head (`Maybe` + `[Int]`); reject prim /
    tvar / arrow / pair, and also already-applied heads (`(Maybe Int) Bool`). -/
def applyTyArgs (head : Ty) (args : List Ty) : Except String Ty :=
  if args.isEmpty then .ok head
  else
    match head with
    | .customTy name [] => .ok (.customTy name args)
    | .customTy _ (_ :: _) => .error "type application is already saturated"
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
#guard (match applyTyArgs (.customTy (.mk "Maybe") [.prim .int]) [.prim .bool] with
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

/-- Upper ident with source token. -/
def upperIdentTok : P (Tok × String) :=
  tokenMap fun t =>
    match t.token with
    | .ident raw true => some (t, raw)
    | _ => none

/-- Any ident with source token. -/
def anyIdentTok : P (Tok × String) :=
  tokenMap fun t =>
    match t.token with
    | .ident raw _ => some (t, raw)
    | _ => none

/-! ## Binder-span sidecar (Writer-style)

Same parse walk records binder locations without changing the Surface AST.
`PB α` is `P (α × List BinderSpan)`; failed/`withBacktracking` branches discard
their lists (unlike StateT, which would leak across backtracks).
-/

abbrev PB (α : Type) := P (α × List BinderSpan)

def mkBinder (kind : BinderKind) (tok : Tok) (name : String) : BinderSpan :=
  { name, kind, span := Span.ofTok tok }

/-- Note: return types use `P (α × _)` (not `PB α`) so do-notation binds `P`, not a phantom `PB` monad. -/
def pbPure (a : α) : P (α × List BinderSpan) :=
  pure (a, [])

def liftP (p : P α) : P (α × List BinderSpan) := do
  let a ← p
  pure (a, [])

def pbMap (f : α → β) (m : P (α × List BinderSpan)) : P (β × List BinderSpan) := do
  let (a, bs) ← m
  pure (f a, bs)

/-- Flatten binder lists from an array of Writer results. -/
def concatBinders {α} (xs : Array (α × List BinderSpan)) : List BinderSpan :=
  xs.toList.flatMap (·.2)

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

/-- One or more atoms; fold juxtaposition onto a *bare* customTy head only.
    Already-applied heads (`(Tree a)`), tvars, and prims do not absorb trailing
    atoms — so ctor fields like `Node (Tree a) a` stay two fields. -/
partial def tyApp : P Ty :=
  withErrorMessage "expected type" do
    let head ← tyAtom
    match head with
    | .customTy name [] =>
        let args ← takeMany (withBacktracking tyAtom)
        return .customTy name args.toList
    | _ =>
        return head

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
def simpleBinder : P (Pattern × List BinderSpan) :=
  withErrorMessage "expected binder" do
    skipComments
    first [
      do
        let _ ← punct .underscore
        return (.wildcard, []),
      do
        let (tok, name) ← lowerIdentTok
        return (.name (.mk name), [mkBinder .param tok name])
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

partial def patAtom : P (Pattern × List BinderSpan) :=
  withErrorMessage "expected pattern atom" do
    skipComments
    first [
      do
        let _ ← punct .underscore
        return (.wildcard, []),
      do
        let p ← boolLitPattern
        return (p, []),
      do
        let (tok, name) ← lowerIdentTok
        return (.name (.mk name), [mkBinder .pat tok name]),
      -- `( p )` or `( p , p )`
      do
        let _ ← punct .lparen
        skipComments
        let (a, bsA) ← pattern
        skipComments
        match ← option? (punct .comma) with
        | some _ =>
          skipComments
          let (b, bsB) ← pattern
          skipComments
          let _ ← punct .rparen
          return (.pair a b, bsA ++ bsB)
        | none =>
          let _ ← punct .rparen
          return (a, bsA),
      -- `[ p, … ]`
      do
        let _ ← punct .lbrack
        skipComments
        match ← option? (punct .rbrack) with
        | some _ => return (.list [], [])
        | none =>
          let (hd, bsHd) ← pattern
          let tl ← takeMany (withBacktracking do
            skipComments
            let _ ← punct .comma
            skipComments
            pattern)
          skipComments
          let _ ← punct .rbrack
          return (.list (hd :: tl.toList.map (·.1)), bsHd ++ concatBinders tl),
      -- bare upper ctor (no args); apps handled in `patApp`
      do
        let name ← upperIdent
        return (.ctor (.mk name) [], [])
    ]

/-- Ctor application: `Just x` / `Cons a b`, or a non-ctor atom. -/
partial def patApp : P (Pattern × List BinderSpan) :=
  withErrorMessage "expected pattern" do
    skipComments
    match ← option? (withBacktracking upperIdent) with
    | some name =>
      let args ← takeMany (withBacktracking patAtom)
      return (.ctor (.mk name) (args.toList.map (·.1)), concatBinders args)
    | none => patAtom

/-- Right-associative cons: `a :: b :: rest` ≡ `cons a (cons b rest)`. -/
partial def pattern : P (Pattern × List BinderSpan) :=
  withErrorMessage "expected pattern" do
    let (left, bsL) ← patApp
    skipComments
    match ← option? (withBacktracking consOp) with
    | some _ =>
      skipComments
      let (right, bsR) ← pattern
      return (.cons left right, bsL ++ bsR)
    | none => return (left, bsL)

end

/-! ## Expression grammar

* `atom` — lit, var/ctor, `()`, `(e)`, `(e, e)`, `[es]`, `\ binders -> e`
* `appExpr` — left-assoc juxtaposition
* `infixExpr` — `appExpr` with optional single infix (`+`/`-`/`<`/`::`)
* `let` / `if` / `match` — soft-keyword forms at `expr` (not juxtaposition args)
* `expr` — let | if | match | infixExpr
-/

mutual

partial def atom : P (Expr × List BinderSpan) :=
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
        return (.primLit (.int n), []),
      do
        let b ← boolLitTok
        return (.primLit (.bool b), []),
      do
        let c ← charLitTok
        return (.primLit (.char c), []),
      -- `()` unit
      do
        let _ ← punct .lparen
        skipComments
        let _ ← punct .rparen
        return (.primLit .unit, []),
      -- `( e )` or `( e , e )`
      do
        let _ ← punct .lparen
        skipComments
        let (a, bsA) ← expr
        skipComments
        match ← option? (punct .comma) with
        | some _ =>
          skipComments
          let (b, bsB) ← expr
          skipComments
          let _ ← punct .rparen
          return (.pair a b, bsA ++ bsB)
        | none =>
          let _ ← punct .rparen
          return (a, bsA),
      -- `[ e, … ]`
      do
        let _ ← punct .lbrack
        skipComments
        match ← option? (punct .rbrack) with
        | some _ => return (.list [], [])
        | none =>
          let (hd, bsHd) ← expr
          let tl ← takeMany (withBacktracking do
            skipComments
            let _ ← punct .comma
            skipComments
            expr)
          skipComments
          let _ ← punct .rbrack
          return (.list (hd :: tl.toList.map (·.1)), bsHd ++ concatBinders tl),
      -- `\ binder+ -> expr`
      do
        let _ ← punct .backslash
        skipComments
        let binders ← takeMany1 (withBacktracking simpleBinder)
        skipComments
        let _ ← punct .arrow
        skipComments
        let (body, bsBody) ← expr
        let pats := binders.toList.map (·.1)
        let bsBind := concatBinders binders
        return (pats.foldr (fun b acc => .lambda b none acc) body, bsBind ++ bsBody),
      -- lower → var
      do
        let name ← lowerIdent
        return (.var (.mk name), []),
      -- upper → ctor
      do
        let name ← upperIdent
        return (.ctor (.mk name), [])
    ]

/-- Left-associative juxtaposition: `f a b` ≡ `(f a) b`.
    Layout: args must share the head's line or start at a greater column
    (so a same-column sibling after a let RHS is not consumed as an app arg). -/
partial def appExpr : P (Expr × List BinderSpan) :=
  withErrorMessage "expected expression" do
    skipComments
    let headTok ← nextTok
    let (head, bsHead) ← atom
    let args ← takeMany (withBacktracking do
      let t ← nextTok
      if t.startLine != headTok.startLine && t.startCol ≤ headTok.startCol then
        throwUnexpectedWithMessage none "app argument must be same line or indented"
      atom)
    return (args.foldl (fun f (a, _) => .app f a) head, bsHead ++ concatBinders args)

/-- Infix RHS: layout forms or an app — not another infix (keeps single-infix). -/
partial def infixRhs : P (Expr × List BinderSpan) :=
  first [letExpr, ifExpr, matchExpr, appExpr]

/-- Single optional infix; a second infix at this layer is an error. -/
partial def infixExpr : P (Expr × List BinderSpan) :=
  withErrorMessage "expected expression" do
    let (left, bsL) ← appExpr
    skipComments
    match ← option? (withBacktracking binOpTok) with
    | none => return (left, bsL)
    | some op =>
      skipComments
      let (right, bsR) ← infixRhs
      skipComments
      match ← option? (withBacktracking binOpTok) with
      | some _ =>
        throwUnexpectedWithMessage none "infix chaining requires parentheses"
      | none =>
        return (applyBinOp op left right, bsL ++ bsR)

/-- One `let` binding: `name [: polyTy] = expr`. Returns binder column.
    `indentCol` is the column of the introducing `let` (or of the first
    binder, for sibling bindings): a newline RHS must start strictly right of
    it, so `let map =\n  e` works with a 2-space indent even when `map` itself
    sits further right than that indent. -/
partial def letBinding (indentCol : Nat) : P ((Nat × ValName × Option PolyTy × Expr) × List BinderSpan) :=
  withErrorMessage "expected let binding" do
    skipComments
    let (tok, name) ← lowerIdentTok
    let blockCol := tok.startCol
    let bsName := [mkBinder .val tok name]
    skipComments
    let ann ← option? (withBacktracking do
      let _ ← punct .colon
      skipComments
      polyTy)
    skipComments
    let eqTok ← punct .eq
    skipComments
    -- RHS: same line as `=`, or indented past `indentCol`
    let t ← nextTok
    if t.startLine > eqTok.startLine then
      colGt indentCol
    let (rhs, bsRhs) ← expr
    return ((blockCol, .mk name, ann, rhs), bsName ++ bsRhs)

/-- `let` bindings `in` body → nested `.letIn` (first binder outermost). -/
partial def letExpr : P (Expr × List BinderSpan) :=
  withErrorMessage "expected let expression" do
    skipComments
    let letTok ← keyword .«let»
    let ((blockCol, n0, ann0, rhs0), bs0) ← letBinding letTok.startCol
    let rest ← takeMany (withBacktracking do
      colEq blockCol
      pbMap (fun (_, n, ann, rhs) => (n, ann, rhs)) (letBinding blockCol))
    skipComments
    let _ ← keyword .«in»
    skipComments
    let (body, bsBody) ← expr
    let binds := (n0, ann0, rhs0) :: rest.toList.map (·.1)
    let bsRest := concatBinders rest
    return (binds.foldr (fun (n, ann, rhs) acc => .letIn n ann rhs acc) body,
      bs0 ++ bsRest ++ bsBody)

/-- `if e then e else e` → `.ife`. -/
partial def ifExpr : P (Expr × List BinderSpan) :=
  withErrorMessage "expected if expression" do
    skipComments
    let _ ← keyword .«if»
    skipComments
    let (c, bsC) ← expr
    skipComments
    let _ ← keyword .«then»
    skipComments
    let (t, bsT) ← expr
    skipComments
    let _ ← keyword .«else»
    skipComments
    let (f, bsF) ← expr
    return (.ife c t f, bsC ++ bsT ++ bsF)

/-- One match arm: `pattern -> expr`. -/
partial def matchArm : P ((Pattern × Expr) × List BinderSpan) := do
  skipComments
  let (pat, bsPat) ← pattern
  skipComments
  let _ ← punct .arrow
  skipComments
  let (body, bsBody) ← expr
  return ((pat, body), bsPat ++ bsBody)

/-- F#-style `match e with [|] P -> e | Q -> e`.
    Leading `|` optional; later branches use `|`.
    Newline-aligned `|` must share the first branch column. -/
partial def matchExpr : P (Expr × List BinderSpan) :=
  withErrorMessage "expected match expression" do
    skipComments
    let _ ← keyword .«match»
    skipComments
    let (scrut, bsScrut) ← expr
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
    let (arm0, bs0) ← matchArm
    let rest ← takeMany (withBacktracking do
      skipComments
      let pipe ← nextTok
      if pipe.token != .punct .pipe then
        throwUnexpected
      if pipe.startLine > blockLine && pipe.startCol != blockCol then
        throwUnexpectedWithMessage none "match branch misaligned"
      let _ ← punct .pipe
      matchArm)
    return (.match_ scrut (arm0 :: rest.toList.map (·.1)),
      bsScrut ++ bs0 ++ concatBinders rest)

/-- Top expression: layout forms or infix/app. -/
partial def expr : P (Expr × List BinderSpan) :=
  withErrorMessage "expected expression" do
    skipComments
    first [
      letExpr,
      ifExpr,
      matchExpr,
      infixExpr
    ]

end

/-! ## Program grammar (F# style)

* `ctorField` — `(name : ty)` (name discarded) or bare `tyApp`
* `typeDecl` — `type T a = C ty | D (n : ty) ty`
* `topLet` — `let name [: scheme] = expr` (no `in`; required `let` at root)
* `program` — interleaved type/let decls, optional body (default `()`)
-/

/-- Ctor field: `(name : ty)` discards `name`; bare fields are `tyApp`
    (arrows need parens, so `C Int -> T` is not one field). -/
def ctorField : P Ty :=
  withErrorMessage "expected constructor field" do
    skipComments
    first [
      withBacktracking do
        let _ ← punct .lparen
        skipComments
        let _ ← anyIdent
        skipComments
        let _ ← punct .colon
        skipComments
        let t ← ty
        skipComments
        let _ ← punct .rparen
        return t,
      tyApp
    ]

def dataCtor : P ((CtorName × List Ty) × List BinderSpan) :=
  withErrorMessage "expected constructor" do
    skipComments
    let (tok, name) ← upperIdentTok
    let fields ← takeMany (withBacktracking ctorField)
    return ((.mk name, fields.toList), [mkBinder .ctor tok name])

def typeDecl : P (DataDecl × List BinderSpan) :=
  withErrorMessage "expected type declaration" do
    skipComments
    let _ ← keyword .«type»
    skipComments
    let (tok, name) ← upperIdentTok
    let bsType := [mkBinder .type tok name]
    let params ← takeMany (withBacktracking do
      skipComments
      lowerIdentTok)
    let bsParams := params.toList.map fun (t, n) => mkBinder .param t n
    skipComments
    let _ ← punct .eq
    skipComments
    let _ ← option? (withBacktracking (punct .pipe))
    skipComments
    let (c0, bsC0) ← dataCtor
    let rest ← takeMany (withBacktracking do
      skipComments
      let _ ← punct .pipe
      skipComments
      dataCtor)
    return ({
      name := .mk name
      params := params.toList.map fun (_, n) => ValName.mk n
      ctors := c0 :: rest.toList.map (·.1)
    }, bsType ++ bsParams ++ bsC0 ++ concatBinders rest)

/-- Top-level `let` binding (F# style — `let` required; no `in`). -/
def topLet : P (Binding × List BinderSpan) :=
  withErrorMessage "expected top-level let" do
    skipComments
    let letTok ← keyword .«let»
    let ((_, name, ann, rhs), bs) ← letBinding letTok.startCol
    return (⟨name, ann, rhs⟩, bs)

/-- Interleaved `type` / `let`, then optional body expr (default unit).
    Groups via `SurfaceBridge.Program.ofFlat` (SCC); fails on duplicate names. -/
def program : P (Program × List BinderSpan) :=
  withErrorMessage "expected program" do
    skipComments
    let items ← takeMany (withBacktracking do
      skipComments
      first [
        do
          let (d, bs) ← typeDecl
          return (Sum.inl (α := DataDecl) (β := Binding) d, bs),
        do
          let (b, bs) ← topLet
          return (Sum.inr (α := DataDecl) (β := Binding) b, bs)
      ])
    skipComments
    let body? ← option? (withBacktracking expr)
    let (body, bsBody) :=
      match body? with
      | some (e, bs) => (e, bs)
      | none => (.primLit .unit, [])
    let decls := items.toList.filterMap fun
      | (.inl d, _) => some d
      | (.inr _, _) => none
    let binds := items.toList.filterMap fun
      | (.inl _, _) => none
      | (.inr b, _) => some b
    let bsItems := concatBinders items
    match SurfaceBridge.Program.ofFlat decls binds body with
    | some p => return (p, bsItems ++ bsBody)
    | none =>
      throwUnexpectedWithMessage none "duplicate binding names"

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
  (runLexParse expr src).map Prod.fst

def parseExprWithBinders (src : String) : Except ParseError (Expr × List BinderSpan) :=
  runLexParse expr src

def parseProgramWithBinders (src : String) : Except ParseError (Program × List BinderSpan) :=
  runLexParse program src

def parseProgram (src : String) : Except ParseError Program :=
  parseProgramWithBinders src |>.map Prod.fst

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
-- already-applied customTy must not absorb trailing atoms
#guard (match parseTy "(Maybe Int) Bool" with | .error _ => true | _ => false)

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

/-! ### Program: type decls + top-level lets + optional body -/

#guard (parseProgram "let x = 1\n").isOk
#guard (parseProgram "let x = 1").isOk
#guard (match parseProgram "let x = 1" with
  | .ok p =>
    match p.body with
    | .primLit .unit => true
    | _ => false
  | _ => false)

#guard (parseProgram "type Maybe a = Just a | Nothing\nlet x = Nothing\nx").isOk

#guard (match parseProgram "type T = C (contents : Int)" with
  | .ok p =>
    match p.decls with
    | [⟨.mk "T", [], [(.mk "C", [.prim .int])]⟩] =>
      match p.body with | .primLit .unit => true | _ => false
    | _ => false
  | _ => false)

#guard (match parseProgram "type Maybe a = Just a | Nothing" with
  | .ok p =>
    match p.decls with
    | [⟨.mk "Maybe", [.mk "a"],
        [(.mk "Just", [.tvar (.mk "a")]), (.mk "Nothing", [])]⟩] => true
    | _ => false
  | _ => false)

-- multi-field recursive ADT: trailing atoms are separate fields, not args
#guard (match parseProgram "type Tree a = Leaf | Node (Tree a) a (Tree a)" with
  | .ok p =>
    match p.decls with
    | [⟨.mk "Tree", [.mk "a"],
        [(.mk "Leaf", []),
         (.mk "Node",
           [.customTy (.mk "Tree") [.tvar (.mk "a")],
            .tvar (.mk "a"),
            .customTy (.mk "Tree") [.tvar (.mk "a")]])]⟩] => true
    | _ => false
  | _ => false)
#guard (match parseProgram "type Tree a = Leaf | Node a (Tree a) (Tree a)" with
  | .ok p =>
    match p.decls with
    | [⟨.mk "Tree", [.mk "a"],
        [(.mk "Leaf", []),
         (.mk "Node",
           [.tvar (.mk "a"),
            .customTy (.mk "Tree") [.tvar (.mk "a")],
            .customTy (.mk "Tree") [.tvar (.mk "a")]])]⟩] => true
    | _ => false
  | _ => false)
#guard (match parseProgram
    "type Tree a = Leaf | Node a (Tree a) (Tree a)\nlet t = Leaf\nt" with
  | .ok p => (SurfaceBridge.lowerProgram p).isSome
  | _ => false)

#guard (match parseProgram "let x = 1\nlet y = 2\nx" with
  | .ok p =>
    match p.body with
    | .var (.mk "x") =>
      let flat := p.groups.flatten
      (flat.length == 2) &&
        flat.any (fun b => match b with
          | ⟨.mk "x", none, .primLit (.int 1)⟩ => true | _ => false) &&
        flat.any (fun b => match b with
          | ⟨.mk "y", none, .primLit (.int 2)⟩ => true | _ => false)
    | _ => false
  | _ => false)

#guard (match parseProgram "let f : Int -> Int = \\x -> x" with
  | .ok p =>
    match p.groups, p.body with
    | [[⟨.mk "f", some ⟨[], .arrow (.prim .int) (.prim .int)⟩,
        .lambda (.name (.mk "x")) none (.var (.mk "x"))⟩]],
      .primLit .unit => true
    | _, _ => false
  | _ => false)

-- newline RHS indented past `let` (not past the binder name)
#guard (parseProgram "let map : {a} a -> a =\n  \\x -> x\nmap").isOk
#guard (match parseExpr "let x =\n  1\nin x" with
  | .ok (.letIn (.mk "x") none (.primLit (.int 1)) (.var (.mk "x"))) => true
  | _ => false)

-- duplicate top-level names → error
#guard (match parseProgram "let x = 1\nlet x = 2" with | .error _ => true | _ => false)

-- end-to-end: parse → lowerProgram
#guard (match parseProgram "let x = 1\nx" with
  | .ok p => (SurfaceBridge.lowerProgram p).isSome
  | _ => false)

#guard (match parseProgram "type Maybe a = Just a | Nothing\nlet x = Nothing\nx" with
  | .ok p => (SurfaceBridge.lowerProgram p).isSome
  | _ => false)

end Surface.Parse
