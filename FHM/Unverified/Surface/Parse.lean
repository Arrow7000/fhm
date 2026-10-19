import Parser.Basic
import FHM.Unverified.Surface.Lex
import FHM.Surface.Span
import FHM.SurfaceBridge

namespace Surface.Parse

open Parser
open Surface.Lex (Token TokenWithSource LexError Keyword Punct BinOpToken)
open Surface.Span (Span BinderKind BinderSpan SpannedExpr SpannedProgram)

/-! ## Errors -/

structure ParseError where
  msg : String
  line : Nat
  col : Nat
  endLine : Nat := line
  endCol : Nat := col + 1
  deriving DecidableEq, Repr

def lexToParse : LexError → ParseError
  | .tab line col =>
      { msg := "tab character", line, col, endLine := line, endCol := col + 1 }
  | .unexpectedChar c line col =>
      { msg := s!"unexpected character {repr c}", line, col, endLine := line, endCol := col + 1 }
  | .unfinishedBlockComment line col =>
      -- Point at the opening `/-`; half-open end covers two columns when possible.
      { msg := "unfinished block comment", line, col, endLine := line, endCol := col + 2 }
  | .badEscape line col =>
      { msg := "bad escape sequence", line, col, endLine := line, endCol := col + 1 }

/-! ## Token stream plumbing

Lex skips whitespace but still emits comment tokens. The parser skips those
so comments may carry spans later without affecting the grammar.
-/

abbrev Tok := TokenWithSource
abbrev TokStream := Subarray Tok
abbrev P := SimpleParser TokStream Tok

def isComment : Token → Bool
  | .lineComment _ | .blockComment _ | .docComment _ => true
  | _ => false

def skipComments : P Unit :=
  dropMany <| tokenFilter (isComment ·.token)

/-- Map a stream index to a full source span (1-based half-open).
    In-range: the token's span. Past EOF: last token's end, width 1. Empty: (1,1)–(1,2). -/
def spanOfIdx (toks : Array Tok) (idx : Nat) : Span :=
  if h : idx < toks.size then
    Span.ofTok toks[idx]
  else
    match toks.back? with
    | some t =>
        { startLine := t.endLine, startCol := t.endCol
          endLine := t.endLine, endCol := t.endCol + 1 }
    | none => { startLine := 1, startCol := 1, endLine := 1, endCol := 2 }

/-- Specificity for choosing among `first` alternatives: real reject messages win
over bare `unexpected` and over generic `expected …` wrappers. -/
def errSpecificity : Parser.Error.Simple TokStream Tok → Nat
  | .unexpected _ (some _) => 2
  | .unexpected _ none => 1
  | .addMessage inner _ msg =>
      if msg.startsWith "expected " then errSpecificity inner
      else 100 + msg.length

/-- Prefer the more specific of two errors (`first` default keeps only the last). -/
def preferErr (e f : Parser.Error.Simple TokStream Tok) :
    Parser.Error.Simple TokStream Tok :=
  if errSpecificity f > errSpecificity e then f else e

/-- Prefer the **innermost** unexpected site and the innermost non-generic
`addMessage` text. When `unexpected` carries the rejected token, use **that
token's span** (stream position is often already past a consume-and-fail). -/
def simpleErrToParse (toks : Array Tok) (e : Parser.Error.Simple TokStream Tok) : ParseError :=
  let rec dig : Parser.Error.Simple TokStream Tok →
      Nat × Option Tok × Option String
    | .unexpected idx t? => (idx, t?, none)
    | .addMessage inner _idx msg =>
        let (i, t?, m?) := dig inner
        let m?' :=
          match m? with
          | some m => some m
          | none =>
              if msg.startsWith "expected " then none else some msg
        (i, t?, m?')
  let (idx, t?, msg?) := dig e
  let s :=
    match t? with
    | some t => Span.ofTok t
    | none => spanOfIdx toks idx
  { msg := msg?.getD "unexpected token"
    line := s.startLine, col := s.startCol
    endLine := s.endLine, endCol := s.endCol }

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
    | .hole => .error "type hole cannot take arguments"
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

def intLitTokFull : P (Tok × Int) :=
  tokenMap fun t =>
    match t.token with
    | .intLit n => some (t, n)
    | _ => none

def boolLitTok : P Bool :=
  tokenMap fun t =>
    match t.token with
    | .boolLit b => some b
    | _ => none

def boolLitTokFull : P (Tok × Bool) :=
  tokenMap fun t =>
    match t.token with
    | .boolLit b => some (t, b)
    | _ => none

def charLitTok : P Char :=
  tokenMap fun t =>
    match t.token with
    | .charLit c => some c
    | _ => none

def charLitTokFull : P (Tok × Char) :=
  tokenMap fun t =>
    match t.token with
    | .charLit c => some (t, c)
    | _ => none

def stringLitTok : P String :=
  tokenMap fun t =>
    match t.token with
    | .stringLit s => some s
    | _ => none

def stringLitTokFull : P (Tok × String) :=
  tokenMap fun t =>
    match t.token with
    | .stringLit s => some (t, s)
    | _ => none

def binOpTok : P BinOpToken :=
  tokenMap fun t =>
    match t.token with
    | .op o => some o
    | _ => none

def binOpTokFull : P (Tok × BinOpToken) :=
  tokenMap fun t =>
    match t.token with
    | .op o => some (t, o)
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

/-! ## Binder-span + expr-hull sidecar (Writer-style)

Same parse walk records binder locations and a `SpannedExpr` mirror without
changing the Surface AST. Failed/`withBacktracking` branches discard their
lists (unlike StateT, which would leak across backtracks).

Expression parsers return `Expr × List ParsedNameSpan × SpannedExpr`.
-/

/-- Internal writer entry: definitions and references travel together so
    backtracking discards both. Public APIs keep returning definition spans. -/
structure ParsedNameSpan extends BinderSpan where
  isDef : Bool := true
  deriving Repr, BEq

abbrev PB (α : Type) := P (α × List ParsedNameSpan)
abbrev PE := P (Expr × List ParsedNameSpan × SpannedExpr)

def mkBinder (kind : BinderKind) (tok : Tok) (name : String) : ParsedNameSpan :=
  { name, kind, span := Span.ofTok tok }

/-- Note: return types use `P (α × _)` (not `PB α`) so do-notation binds `P`, not a phantom `PB` monad. -/
def pbPure (a : α) : P (α × List ParsedNameSpan) :=
  pure (a, [])

def liftP (p : P α) : P (α × List ParsedNameSpan) := do
  let a ← p
  pure (a, [])

def pbMap (f : α → β) (m : P (α × List ParsedNameSpan)) : P (β × List ParsedNameSpan) := do
  let (a, bs) ← m
  pure (f a, bs)

/-- Flatten binder lists from an array of Writer results. -/
def concatBinders {α} (xs : Array (α × List ParsedNameSpan)) : List ParsedNameSpan :=
  xs.toList.flatMap (·.2)

def concatBinders3 {α} (xs : Array (α × List ParsedNameSpan × SpannedExpr)) : List ParsedNameSpan :=
  xs.toList.flatMap (·.2.1)

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

/-- Hull of tokens consumed in `[startPos, stopPos)` on the current stream. -/
def spanOfConsumed (startPos stopPos : Nat) : P Span := do
  let s ← getStream
  if stopPos ≤ startPos then
    return Span.empty
  else
    match s.array[startPos]?, s.array[stopPos - 1]? with
    | some t0, some t1 => return Span.union (Span.ofTok t0) (Span.ofTok t1)
    | _, _ => return Span.empty

/-! ## Type grammar

* `tyAtom` — `()`, names, `(ty)`, `(ty, ty)`
* `tyApp`  — juxtaposition (`Maybe Int`); only `customTy` may take args
* `ty`     — right-assoc `tyApp -> ty`
* `polyTy` — `{a b} ty` / bare `ty`
-/

instance : Inhabited Ty := ⟨.prim .unit⟩
instance : Inhabited PolyTy := ⟨⟨[], .prim .unit⟩⟩

mutual

partial def tyAtom : P Ty :=
  withErrorMessage "expected type atom" do
    skipComments
    first (combine := preferErr) [
      do
        let _ ← punct .underscore
        return .hole,
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
      -- Primitive / nominal type. `BL` is reserved as a retired bounds spelling
      -- so old programs fail explicitly instead of becoming a nominal type.
      do
        let name ← upperIdent
        if name == "BL" then
          throwUnexpectedWithMessage none
            "bounded-list types are not part of the Hindley--Milner language"
        else
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

/-- Name references from a successfully parsed type fragment. -/
def typeWithReferences (p : P Ty) : P (Ty × List ParsedNameSpan) := do
  let (t, start, stop) ← withCapture p
  let stream ← getStream
  let refs := (stream.array.extract start stop).toList.filterMap fun tok =>
    match tok.token with
    | .ident name upper => some ({
        name := name
        kind := if upper then .type else .param
        span := Span.ofTok tok
        isDef := false } : ParsedNameSpan)
    | .punct .underscore => some ({
        name := "_"
        kind := .param
        span := Span.ofTok tok
        isDef := false } : ParsedNameSpan)
    | _ => none
  return (t, refs)

/-- Scheme: `{a b} body` or bare `ty`. Type foralls emit `.param` binders
scoped over the complete scheme. -/
partial def polyTy : P (PolyTy × List ParsedNameSpan) :=
  withErrorMessage "expected type scheme" do
    skipComments
    match ← option? (withBacktracking (punct .lbrace)) with
    | some lb =>
      skipComments
      -- First binder group (required if `{` present).
      let firstToks ← takeMany1 (withBacktracking do
        skipComments
        anyIdentTok)
      skipComments
      -- A colon here was the retired `{n : Nat, ...}` count-binder syntax.
      match ← option? (withBacktracking (punct .colon)) with
      | some _ =>
          throwUnexpectedWithMessage none
            "Nat/count binders are not part of the Hindley--Milner language"
      | none => pure ()
      let tyToks := firstToks.toList
      skipComments
      let _ ← punct .rbrace
      skipComments
      let tyNames := tyToks.map (·.2)
      let startBody ← getPosition
      let (body, refs) ← typeWithReferences ty
      let stopBody ← getPosition
      let bodySpan ← spanOfConsumed startBody stopBody
      let polySpan := Span.union (Span.ofTok lb) bodySpan
      let bsTys := tyToks.map fun (t, n) =>
        ({ name := n, kind := .param, span := Span.ofTok t, scope? := some polySpan } :
          ParsedNameSpan)
      return ({ foralls := tyNames.map ValName.mk, body }, bsTys ++ refs)
    | none =>
      let (body, refs) ← typeWithReferences ty
      return ({ foralls := [], body }, refs)

/-! ## Expression helpers -/

instance : Inhabited Expr := ⟨.primLit .unit⟩
instance : Inhabited Pattern := ⟨.wildcard⟩
instance : Inhabited ValName := ⟨.mk ""⟩
instance : Inhabited (Nat × ValName × List ValName × List (ValName × Option Ty) ×
    Option PolyTy × Expr) :=
  ⟨(0, default, [], [], none, default)⟩
instance : Inhabited (Nat × ValName × List ValName × List (ValName × Option Ty) ×
    Option PolyTy × Expr × SpannedExpr) :=
  ⟨(0, default, [], [], none, default, default)⟩
instance : Inhabited (Pattern × Expr) := ⟨(default, default)⟩
instance : Inhabited (Pattern × Expr × SpannedExpr) := ⟨(default, default, default)⟩
instance : Inhabited (Expr × List ParsedNameSpan × SpannedExpr) :=
  ⟨(default, [], default)⟩

def applyBinOp (op : BinOpToken) (a b : Expr) : Expr :=
  match op with
  | .plus => .app (.app (.primBinOp .intAdd) a) b
  | .minus => .app (.app (.primBinOp .intSub) a) b
  | .lt => .app (.app (.primBinOp .intLt) a) b
  | .cons => .cons a b

/-- Apply infix, mirroring Core/Surface shape in `SpannedExpr`. -/
def applyBinOpSpanned (opTok : Tok) (op : BinOpToken)
    (a : Expr) (sa : SpannedExpr) (b : Expr) (sb : SpannedExpr) :
    Expr × SpannedExpr :=
  let spanAll := Span.union sa.span sb.span
  match op with
  | .cons => (.cons a b, .cons spanAll sa sb)
  | .plus | .minus | .lt =>
      let e := applyBinOp op a b
      let opS : SpannedExpr := .leaf (Span.ofTok opTok)
      let spanInner := Span.union opS.span sa.span
      (e, .app spanAll (.app spanInner opS sa) sb)

/-- Simple λ/let binder: name or `_`. No type annotation (avoids `->` ambiguity).
    Also returns the binder token span (for λ hulls). -/
def simpleBinder : P (Pattern × List ParsedNameSpan × Span) :=
  withErrorMessage "expected binder" do
    skipComments
    first [
      do
        let tok ← punct .underscore
        return (.wildcard, [], Span.ofTok tok),
      do
        let (tok, name) ← lowerIdentTok
        return (.name (.mk name), [mkBinder .param tok name], Span.ofTok tok)
    ]

/-- Optional `{ tyParam+ }` after a binding name (nonempty if `{` present). -/
def tyParamBinders : P (List ValName × List ParsedNameSpan) :=
  withErrorMessage "expected type parameters" do
    skipComments
    match ← option? (withBacktracking (punct .lbrace)) with
    | none => return ([], [])
    | some _ =>
      skipComments
      let binderToks ← takeMany1 (withBacktracking do
        skipComments
        anyIdentTok)
      skipComments
      let _ ← punct .rbrace
      let bs := binderToks.toList.map fun (t, n) => mkBinder .param t n
      let tps := binderToks.toList.map fun (_, n) => ValName.mk n
      return (tps, bs)

/-- One value parameter: bare `lowerIdent` or `( lowerIdent : ty )`. -/
def valueParam : P ((ValName × Option Ty) × List ParsedNameSpan) :=
  withErrorMessage "expected value parameter" do
    skipComments
    first [
      withBacktracking do
        let _ ← punct .lparen
        skipComments
        first [
          do
            let _ ← punct .underscore
            skipComments
            let _ ← punct .colon
            skipComments
            let (t, refs) ← typeWithReferences ty
            skipComments
            let _ ← punct .rparen
            return ((.mk "_", some t), refs),
          do
            let (tok, name) ← lowerIdentTok
            skipComments
            let _ ← punct .colon
            skipComments
            let (t, refs) ← typeWithReferences ty
            skipComments
            let _ ← punct .rparen
            return ((.mk name, some t), mkBinder .param tok name :: refs)
        ],
      do
        let (tok, name) ← lowerIdentTok
        return ((.mk name, none), [mkBinder .param tok name])
    ]

/-- Zero or more value params; peek stops at `:` / `=` (ann or RHS). -/
def valueParams : P (List (ValName × Option Ty) × List ParsedNameSpan) := do
  let ps ← takeMany (withBacktracking do
    skipComments
    let t ← nextTok
    match t.token with
    | .punct .colon | .punct .eq => throwUnexpected
    | _ => pure ()
    valueParam)
  return (ps.toList.map (·.1), ps.toList.flatMap (·.2))

/-- `True`/`False` bool tokens as ctor patterns (Surface has no lit patterns). -/
def boolLitPattern : P Pattern :=
  tokenMap fun t =>
    match t.token with
    | .boolLit true => some (.ctor (.mk "True") [])
    | .boolLit false => some (.ctor (.mk "False") [])
    | _ => none

/-! ## Patterns (match arms and lambda parameters; right-assoc `::`)

* `patAtom` — `_`, name, bool ctor, `(p)`, `(p, p)`, `[ps]`, bare upper ctor
* `patApp`  — upper ctor with argument atoms
* `pattern` — right-assoc `::` chains
-/

mutual

partial def patAtom : P (Pattern × List ParsedNameSpan) :=
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
        let (tok, name) ← upperIdentTok
        return (.ctor (.mk name) [],
          [{ name, kind := .ctor, span := Span.ofTok tok, isDef := false }])
    ]

/-- Ctor application: `Just x` / `Cons a b`, or a non-ctor atom. -/
partial def patApp : P (Pattern × List ParsedNameSpan) :=
  withErrorMessage "expected pattern" do
    skipComments
    match ← option? (withBacktracking upperIdentTok) with
    | some (tok, name) =>
      let args ← takeMany (withBacktracking patAtom)
      return (.ctor (.mk name) (args.toList.map (·.1)),
        { name, kind := .ctor, span := Span.ofTok tok, isDef := false } :: concatBinders args)
    | none => patAtom

/-- Right-associative cons: `a :: b :: rest` ≡ `cons a (cons b rest)`. -/
partial def pattern : P (Pattern × List ParsedNameSpan) :=
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

/-- A lambda parameter is one pattern atom; applied constructors and cons
    patterns require parentheses, keeping `\x y` as two parameters. A whole
    pattern can have a monotype annotation, e.g. `((x, y) : (Int, Bool))`. -/
def lambdaBinder : P (Pattern × Option Ty × List ParsedNameSpan × Span) :=
  withErrorMessage "expected lambda binder" do
    skipComments
    let ((pat, ann, bs), start, stop) ← withCapture <| first (combine := preferErr) [
      withBacktracking do
        let _ ← punct .lparen
        let (pat, bs) ← pattern
        skipComments
        let _ ← punct .colon
        let (τ, refs) ← typeWithReferences ty
        skipComments
        let _ ← punct .rparen
        return (pat, some τ, bs ++ refs),
      do
        let (pat, bs) ← patAtom
        return (pat, none, bs)
    ]
    let span ← spanOfConsumed start stop
    let bs := match pat with
      | .name _ => bs.map fun b => if b.isDef && b.kind == .pat then { b with kind := .param } else b
      | _ => bs
    return (pat, ann, bs, span)

/-- One authored binding can expand into storage plus independent projections. -/
structure ParsedLetBinding where
  column : Nat := 0
  header : Span := Span.empty
  entries : List (Binding × SpannedExpr) := []
  patternToken? : Option Tok := none

instance : Inhabited ParsedLetBinding := ⟨{}⟩

/-- Pattern bindings cannot participate in any syntactic dependency cycle,
    including one cut by an annotation for ordinary inference SCCs. -/
def checkPatternBindingCycles (entries : List (Binding × SpannedExpr))
    (tokens : List Tok) (lexicalDuplicates : Bool := false) : P Unit := do
  if tokens.isEmpty then return ()
  let binds := entries.map (·.1)
  let names := binds.map (·.name)
  if names.eraseDups.length != names.length then
    if lexicalDuplicates then return ()
    throwUnexpectedWithMessage tokens.head?
      "duplicate binding names in a pattern let block"
  let groups := (SurfaceBridge.sccGroups (binds.map fun b => { b with ann := none })).getD []
  for group in groups do
    if group.any (fun b => Surface.internalBindingName b.name) &&
        (group.length > 1 || group.any (fun b => b.refersTo b.name)) then
      let names := (group.filter fun b => !Surface.internalBindingName b.name).map
        fun b => match b.name with | .mk name => name
      let site := (tokens.find? fun t => group.any fun b =>
        b.name == ValName.mk s!"$pattern/{t.startLine}/{t.startCol}").or tokens.head?
      throwUnexpectedWithMessage site
        ("recursive pattern binding involving: " ++ String.intercalate ", " names)

/-! ## Expression grammar

* `atom` — lit, var/ctor, `()`, `(e)`, `(e, e)`, `[es]`, `\ binders -> e`
* `appExpr` — left-assoc juxtaposition
* `infixExpr` — `appExpr` with optional single infix (`+`/`-`/`<`/`::`)
* `let` / `if` / `match` — soft-keyword forms at `expr` (not juxtaposition args)
* `expr` — let | if | match | infixExpr
-/

mutual

partial def atom : PE := do
  skipComments
  -- Reject strings *before* `first`: later branches consume-and-fail past the
  -- lit and `first`'s default combine would keep that worse error.
  let t0 ← nextTok
  match t0.token with
  | .stringLit _ =>
      throwUnexpectedWithMessage (some t0)
        "string literals are not supported in expressions"
  | _ => pure ()
  withErrorMessage "expected expression atom" do
    -- Prefer specific reject messages (e.g. value-level `*`) over later bare fails.
    first (combine := preferErr) [
      -- int / bool / char
      do
        let (tok, n) ← intLitTokFull
        return (.primLit (.int n), [], .leaf (Span.ofTok tok)),
      do
        let (tok, b) ← boolLitTokFull
        return (.primLit (.bool b), [], .leaf (Span.ofTok tok)),
      do
        let (tok, c) ← charLitTokFull
        return (.primLit (.char c), [], .leaf (Span.ofTok tok)),
      -- `()` unit
      do
        let t0 ← punct .lparen
        skipComments
        let t1 ← punct .rparen
        return (.primLit .unit, [], .leaf (Span.union (Span.ofTok t0) (Span.ofTok t1))),
      -- `( e )` or `( e , e )`
      do
        let t0 ← punct .lparen
        skipComments
        let (a, bsA, sa) ← expr
        skipComments
        match ← option? (punct .comma) with
        | some _ =>
          skipComments
          let (b, bsB, sb) ← expr
          skipComments
          let t1 ← punct .rparen
          let span := Span.union (Span.ofTok t0) (Span.ofTok t1)
          return (.pair a b, bsA ++ bsB, .pair span sa sb)
        | none =>
          let t1 ← punct .rparen
          let span := Span.union (Span.ofTok t0) (Span.ofTok t1)
          let sa' :=
            match sa with
            | .generated e => .generated e
            | .leaf _ => SpannedExpr.leaf span
            | .pair _ x y => .pair span x y
            | .cons _ x y => .cons span x y
            | .list _ xs => .list span xs
            | .lambda _ b => .lambda span b
            | .app _ f x => .app span f x
            | .letIn _ r b => .letIn span r b
            | .letRecIn _ rs b => .letRecIn span rs b
            | .ife _ c t f => .ife span c t f
            | .match_ _ s arms => .match_ span s arms
          return (a, bsA, sa'),
      -- `[ e, … ]`
      do
        let t0 ← punct .lbrack
        skipComments
        match ← option? (punct .rbrack) with
        | some t1 =>
          return (.list [], [], .list (Span.union (Span.ofTok t0) (Span.ofTok t1)) [])
        | none =>
          let (hd, bsHd, sh) ← expr
          let tl ← takeMany (withBacktracking do
            skipComments
            let _ ← punct .comma
            skipComments
            expr)
          skipComments
          let t1 ← punct .rbrack
          let items := hd :: tl.toList.map (·.1)
          let spans := sh :: tl.toList.map (·.2.2)
          let bs := bsHd ++ concatBinders3 tl
          let span := Span.union (Span.ofTok t0) (Span.ofTok t1)
          return (.list items, bs, .list span spans),
      -- `\ binder+ -> expr`
      do
        let bsTok ← punct .backslash
        skipComments
        let binders ← takeMany1 (withBacktracking lambdaBinder)
        skipComments
        let _ ← punct .arrow
        skipComments
        let (body, bsBody, sBody) ← expr
        let bsBind := binders.toList.flatMap (·.2.2.1)
        let (e, s) :=
          binders.toList.foldr
            (fun (pat, paramAnn, _, bspan) (acc, accS) =>
              let sp := Span.union bspan accS.span
              (Expr.lambda pat paramAnn acc, SpannedExpr.lambda sp accS))
            (body, sBody)
        let spanAll := Span.union (Span.ofTok bsTok) sBody.span
        let s' :=
          match s with
          | .lambda _ b => SpannedExpr.lambda spanAll b
          | other => other
        return (e, bsBind ++ bsBody, s'),
      -- lower → var
      do
        let (tok, name) ← lowerIdentTok
        return (.var (.mk name), [], .leaf (Span.ofTok tok)),
      -- upper → ctor
      do
        let (tok, name) ← upperIdentTok
        return (.ctor (.mk name), [], .leaf (Span.ofTok tok))
    ]

/-- Left-associative juxtaposition: `f a b` ≡ `(f a) b`.
    Layout: args must share the head's line or start at a greater column
    (so a same-column sibling after a let RHS is not consumed as an app arg). -/
partial def appExpr : PE :=
  withErrorMessage "expected expression" do
    skipComments
    let headTok ← nextTok
    let (head, bsHead, sHead) ← atom
    let args ← takeMany (withBacktracking do
      let t ← nextTok
      if t.startLine != headTok.startLine && t.startCol ≤ headTok.startCol then
        throwUnexpectedWithMessage none "app argument must be same line or indented"
      atom)
    -- Soft `takeMany` swallows a failed arg; re-surface common rejects so
    -- `f "bla"` points at the string instead of a generic leftover error.
    skipComments
    match ← option? (withBacktracking do
        let t ← nextTok
        match t.token with
        | .stringLit _ => pure t
        | _ => throwUnexpected) with
    | some t =>
        throwUnexpectedWithMessage (some t)
          "string literals are not supported in expressions"
    | none => pure ()
    let (e, s) :=
      args.foldl
        (fun (f, sf) (a, _, sa) =>
          let sp := Span.union sf.span sa.span
          (Expr.app f a, SpannedExpr.app sp sf sa))
        (head, sHead)
    return (e, bsHead ++ concatBinders3 args, s)

/-- Infix RHS: layout forms or an app — not another infix (keeps single-infix). -/
partial def infixRhs : PE :=
  first [letExpr, ifExpr, matchExpr, appExpr]

/-- Single optional infix; a second infix at this layer is an error. -/
partial def infixExpr : PE :=
  withErrorMessage "expected expression" do
    let (left, bsL, sL) ← appExpr
    skipComments
    match ← option? (withBacktracking binOpTokFull) with
    | none => return (left, bsL, sL)
    | some (opTok, op) =>
      skipComments
      let (right, bsR, sR) ← infixRhs
      skipComments
      match ← option? (withBacktracking binOpTok) with
      | some _ =>
        throwUnexpectedWithMessage none "infix chaining requires parentheses"
      | none =>
        let (e, s) := applyBinOpSpanned opTok op left sL right sR
        return (e, bsL ++ bsR, s)

/-- Named lets retain ordinary recursive/SCC semantics. A pattern head
    expands to ordinary call-by-name storage and independently generalised projections. -/
partial def letBinding (indentCol : Nat) : P (ParsedLetBinding × List ParsedNameSpan) :=
  withErrorMessage "expected let binding" do
    skipComments
    let headTok ← nextTok
    let name? ← option? (withBacktracking lowerIdentTok)
    let (pat, bsHead, tyParams, params) ← match name? with
      | some (tok, name) => do
          skipComments
          let (tyParams, bsTyParams) ← tyParamBinders
          skipComments
          let (params, bsParams) ← valueParams
          if !tyParams.isEmpty || !params.isEmpty then
            throwUnexpectedWithMessage (some tok)
              "let head binders are not supported; write an explicit lambda in the RHS"
          pure (.name (.mk name), [mkBinder .val tok name] ++ bsTyParams ++ bsParams,
            tyParams, params)
      | none => do
          let (pat, bs) ← pattern
          let names := patVars pat
          if names.eraseDups.length != names.length then
            throwUnexpectedWithMessage (some headTok) "duplicate names in let pattern"
          let bs := bs.map fun b =>
            if b.isDef && b.kind == .pat then { b with kind := .val } else b
          pure (pat, bs, [], [])
    skipComments
    let annRaw ← match ← option? (withBacktracking (punct .colon)) with
      | none => pure none
      | some _ => do
          skipComments
          some <$> polyTy
    skipComments
    let eqTok ← punct .eq
    skipComments
    let t ← nextTok
    if t.startLine > eqTok.startLine then colGt indentCol
    let (rhs, bsRhs, sRhs) ← expr
    let recursiveNames := (patVars pat).filter fun name => (freeNames [] rhs).contains name
    if name?.isNone && !recursiveNames.isEmpty then
      let names := recursiveNames.map fun | .mk name => name
      throwUnexpectedWithMessage (some headTok)
        ("recursive pattern binding involving: " ++ String.intercalate ", " names)
    let (ann, bsAnn) := match annRaw with
      | some (σ, bs) => (some σ, bs)
      | none => (none, [])
    let entries := match name? with
      | some (_, name) => [(({ name := .mk name, tyParams, params, ann, rhs } : Binding), sRhs)]
      | none =>
          let storage := ValName.mk s!"$pattern/{headTok.startLine}/{headTok.startCol}"
          (Surface.patternBindings storage pat rhs).mapIdx fun i binding =>
            if i == 0 then ({ binding with ann := ann }, sRhs)
            else (binding, .generated (.match_ sRhs.span (.leaf sRhs.span) [.leaf sRhs.span]))
    let parsed : ParsedLetBinding := {
      column := headTok.startCol
      header := (Span.ofTok headTok).union (Span.ofTok eqTok)
      entries := entries
      patternToken? := if name?.isSome then none else some headTok }
    pure (parsed, bsHead ++ bsAnn ++ bsRhs)

/-- A unique-name local `let` block is SCC-sorted in dependency order.
Acyclic singleton components become ordinary `.letIn`s; recursive singleton
and mutual components become `.letRecIn`s. Thus acyclic forward references and
local mutual recursion have the same SCC meaning as their top-level
counterparts, while ordinary HM let-generalization keeps using the
non-recursive node.

Duplicate names retain the old lexical nesting semantics: SCC construction is
ambiguous in their presence, but ordinary shadowing is not. -/
partial def letExpr : PE :=
  withErrorMessage "expected let expression" do
    skipComments
    let letTok ← keyword .«let»
    let (first, bs0) ← letBinding letTok.startCol
    let rest ← takeMany (withBacktracking do
      colEq first.column
      letBinding first.column)
    let parsed := first :: rest.toList.map (·.1)
    let bindsWithSpans := parsed.flatMap (·.entries)
    checkPatternBindingCycles bindsWithSpans (parsed.filterMap (·.patternToken?)) true
    skipComments
    let _ ← keyword .«in»
    skipComments
    let (body, bsBody, sBody) ← expr
    let binds : List Binding := bindsWithSpans.map (·.1)
    let bsRest := concatBinders rest
    let bindingBinders := bs0 ++ bsRest
    let lexical : Expr × SpannedExpr :=
      bindsWithSpans.foldr
        (fun (entry : Binding × SpannedExpr) (accPair : Expr × SpannedExpr) =>
          let b := entry.1
          let sRhs := entry.2
          let acc := accPair.1
          let accS := accPair.2
          let sp := Span.union sRhs.span accS.span
          (Expr.letIn b.name b.tyParams b.params b.ann b.rhs acc,
            SpannedExpr.letIn sp sRhs accS))
        (body, sBody)
    let (e, s) :=
      match SurfaceBridge.sccGroups binds with
      | none => lexical
      | some groups =>
        let rhsSpan (b : Binding) : SpannedExpr :=
          ((bindsWithSpans.find? fun (p : Binding × SpannedExpr) => p.1.name == b.name).map
            (fun (p : Binding × SpannedExpr) => p.2)).getD
            (.leaf Span.empty)
        let binderSpan (b : Binding) (sRhs : SpannedExpr) : Option Span :=
          let name := match b.name with | .mk s => s
          (bindingBinders.filter fun (bs : ParsedNameSpan) =>
            let beforeRhs :=
              bs.span.endLine < sRhs.span.startLine ||
                (bs.span.endLine == sRhs.span.startLine &&
                  bs.span.endCol ≤ sRhs.span.startCol)
            bs.name == name && bs.kind == BinderKind.val && bs.scope?.isNone && beforeRhs).getLast?.map
              (fun (bs : ParsedNameSpan) => bs.span)
        groups.foldr (fun (group : List Binding) ((acc, accS) : Expr × SpannedExpr) =>
          let rhss : List SpannedExpr := group.map rhsSpan
          let headers := group.zip rhss |>.filterMap fun (b, sRhs) => binderSpan b sRhs
          let sp := (Span.hull (headers ++ rhss.map (fun (s : SpannedExpr) => s.span))).map
              (Span.union · accS.span)
            |>.getD accS.span
          match group with
          | [] => (acc, accS)
          | [b] =>
            let sRhs := rhsSpan b
            if !(SurfaceBridge.Binding.refersTo b b.name) then
              (Expr.letIn b.name b.tyParams b.params b.ann b.rhs acc,
                SpannedExpr.letIn sp sRhs accS)
            else
              (Expr.letRecIn [b] acc, SpannedExpr.letRecIn sp [sRhs] accS)
          | _ => (Expr.letRecIn group acc, SpannedExpr.letRecIn sp rhss accS))
          (body, sBody)
    let spanAll := Span.union (Span.ofTok letTok) sBody.span
    let s' :=
      match s with
      | .letIn _ r b => SpannedExpr.letIn spanAll r b
      | .letRecIn _ rs b => SpannedExpr.letRecIn spanAll rs b
      | other => other
    return (e, bs0 ++ bsRest ++ bsBody, s')

/-- `if e then e else e` → `.ife`. -/
partial def ifExpr : PE :=
  withErrorMessage "expected if expression" do
    skipComments
    let ifTok ← keyword .«if»
    skipComments
    let (c, bsC, sC) ← expr
    skipComments
    let _ ← keyword .«then»
    skipComments
    let (t, bsT, sT) ← expr
    skipComments
    let _ ← keyword .«else»
    skipComments
    let (f, bsF, sF) ← expr
    let span := Span.union (Span.ofTok ifTok) sF.span
    return (.ife c t f, bsC ++ bsT ++ bsF, .ife span sC sT sF)

/-- One match arm: `pattern -> expr`. -/
partial def matchArm : P ((Pattern × Expr × SpannedExpr) × List ParsedNameSpan) := do
  skipComments
  let (pat, bsPat) ← pattern
  skipComments
  let _ ← punct .arrow
  skipComments
  let (body, bsBody, sBody) ← expr
  return ((pat, body, sBody), bsPat ++ bsBody)

/-- F#-style `match e with [|] P -> e | Q -> e`.
    Leading `|` optional; later branches use `|`.
    Newline-aligned `|` must share the first branch column. -/
partial def matchExpr : PE :=
  withErrorMessage "expected match expression" do
    skipComments
    let matchTok ← keyword .«match»
    skipComments
    let (scrut, bsScrut, sScrut) ← expr
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
    let arms := arm0 :: rest.toList.map (·.1)
    let armExprs := arms.map fun ⟨p, e, _⟩ => (p, e)
    let armSpans := arms.map fun ⟨_, _, s⟩ => s
    let lastArmSpan :=
      match armSpans.getLast? with
      | some s => s.span
      | none => sScrut.span
    let span := Span.union (Span.ofTok matchTok) lastArmSpan
    return (.match_ scrut armExprs,
      bsScrut ++ bs0 ++ concatBinders rest,
      .match_ span sScrut armSpans)

/-- Top expression: layout forms or infix/app. -/
partial def expr : PE :=
  withErrorMessage "expected expression" do
    skipComments
    -- Commit on the leading keyword rather than trying each form in turn:
    -- `first` keeps only the last alternative's error, so an error inside a
    -- `match` (say) would be reported as `infixExpr` rejecting the keyword.
    let next : Option Token := (← option? nextTok).map (·.token)
    match next with
    | some (.keyword .«let») => letExpr
    | some (.keyword .«if») => ifExpr
    | some (.keyword .«match») => matchExpr
    | _ => infixExpr

end

/-! ## Program grammar (F# style)

* `ctorField` — `(name : ty)` (name discarded) or bare `tyApp`
* `typeDecl` — `type T a = C ty | D (n : ty) ty`
* `topLet` — `let name/pattern [: scheme] = expr` (no `in`); function heads remain rejected
* `program` — interleaved type/let decls, optional body (default `()`)
-/

/-- Ctor field: `(name : ty)` discards `name`; bare fields are atoms, as in
    Haskell and Elm, so `Node T Int T` has three fields even when `T` takes no
    parameters. Applied types and arrows need parens: `C (List a) (Int -> T)`. -/
def ctorField : P (Ty × List ParsedNameSpan) :=
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
        let (t, refs) ← typeWithReferences ty
        skipComments
        let _ ← punct .rparen
        return (t, refs),
      typeWithReferences tyAtom
    ]

/-- A constructor and its fields. A field on a later line must be indented past
    `declCol`, the declaration's `type` keyword, so the declaration ends at the
    next unindented line (e.g. the program's body). -/
def dataCtor (declCol : Nat) : P ((CtorName × List Ty) × List ParsedNameSpan) :=
  withErrorMessage "expected constructor" do
    skipComments
    let (tok, name) ← upperIdentTok
    let fields ← takeMany (withBacktracking do
      colGt declCol
      ctorField)
    return ((.mk name, fields.toList.map (·.1)),
      mkBinder .ctor tok name :: fields.toList.flatMap (·.2))

/-- `type T a = …` plus binder spans and the full decl source span (tyvar scope). -/
def typeDecl : P (DataDecl × List ParsedNameSpan × Span) :=
  withErrorMessage "expected type declaration" do
    skipComments
    let ((d, bs), seg) ← withCapture do
      let typeTok ← keyword .«type»
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
      let (c0, bsC0) ← dataCtor typeTok.startCol
      let rest ← takeMany (withBacktracking do
        skipComments
        let _ ← punct .pipe
        skipComments
        dataCtor typeTok.startCol)
      return ({
        name := .mk name
        params := params.toList.map fun (_, n) => ValName.mk n
        ctors := c0 :: rest.toList.map (·.1)
      }, bsType ++ bsParams ++ bsC0 ++ concatBinders rest)
    let declSpan ← spanOfConsumed seg.1 seg.2
    return (d, bs, declSpan)

/-- Top-level named or pattern let (no `in`). -/
def topLet : P (ParsedLetBinding × List ParsedNameSpan) :=
  withErrorMessage "expected top-level let" do
    skipComments
    let letTok ← keyword .«let»
    letBinding letTok.startCol

/-- One top-level `type` / `let` item. Soft-fails only when the next token is
**not** `type`/`let` (so `takeMany` can stop). Once the keyword is seen, the
item parse is **committed** — RHS errors keep their real site/message instead of
being swallowed by `foldl`/`takeMany` and re-reported as `unexpected` on `let`. -/
def programItem : P (Sum (DataDecl × Span) ParsedLetBinding × List ParsedNameSpan) := do
  skipComments
  let t ← nextTok
  match t.token with
  | .keyword .«type» =>
      let (d, bs, dSpan) ← typeDecl
      return (Sum.inl (d, dSpan), bs)
  | .keyword .«let» =>
      let (b, bs) ← topLet
      return (Sum.inr b, bs)
  | _ => throwUnexpected

/-- Zero or more committed top-level items. Stops at the first non-`type`/`let`
token (or EOF) without discarding a real item error. -/
partial def programItems : P (Array (Sum (DataDecl × Span) ParsedLetBinding × List ParsedNameSpan)) :=
  go #[]
where
  go (acc : Array (Sum (DataDecl × Span) ParsedLetBinding × List ParsedNameSpan)) := do
    skipComments
    -- EOF → done (peek/nextTok fails only if stream empty after skipComments).
    match ← option? (withBacktracking do
      let t ← nextTok
      match t.token with
      | .keyword .«type» | .keyword .«let» => pure t
      | _ => throwUnexpected) with
    | none => return acc
    | some _ =>
        -- Keyword present: parse committed (errors propagate with true site).
        let item ← programItem
        go (acc.push item)

/-- Interleaved `type` / `let`, then optional body expr (default unit).
    Groups via `SurfaceBridge.Program.ofFlat` (SCC); fails on duplicate names.
    Also returns a `SpannedProgram` aligned with group/body structure. -/
def program : P (Program × List ParsedNameSpan × SpannedProgram) :=
  withErrorMessage "expected program" do
    skipComments
    let items ← programItems
    skipComments
    -- If anything remains, parse body **committed** so body errors aren't soft-
    -- failed into a generic endOfInput at the wrong token. EOF → unit body.
    let (body, bsBody, sBody) ←
      match ← option? (withBacktracking (endOfInput *> pure ())) with
      | some _ => pure (.primLit .unit, [], .leaf Span.empty)
      | none => expr
    let decls := items.toList.filterMap fun
      | (.inl (d, _), _) => some d
      | (.inr _, _) => none
    let declSpans := items.toList.filterMap fun
      | (.inl (_, sp), _) => some sp
      | (.inr _, _) => none
    let bindsWithSpans := items.toList.flatMap fun
      | (.inl _, _) => []
      | (.inr b, _) => b.entries
    let patternTokens := items.toList.filterMap fun
      | (.inl _, _) => none
      | (.inr b, _) => b.patternToken?
    checkPatternBindingCycles bindsWithSpans patternTokens
    let binds := bindsWithSpans.map (·.1)
    let bsItems := concatBinders items
    match SurfaceBridge.Program.ofFlat decls binds body with
    | some p =>
      -- SCC may reorder groups; look up RHS spans by unique binding name.
      let spanByName := bindsWithSpans.map fun (b, s) => (b.name, s)
      let groupSpans := p.groups.map fun g =>
        g.filterMap fun b => (spanByName.find? fun p => p.1 == b.name).map (·.2)
      -- Source order (pre-SCC) for hover: binder spans were emitted in this order.
      let sourceNames := binds.map fun b =>
        match b.name with | .mk s => s
      let bindingHeaders := items.toList.flatMap fun
        | (.inl _, _) => []
        | (.inr parsed, _) => parsed.entries.map fun (binding, _) =>
            (match binding.name with | .mk name => name, parsed.header)
      let sp : SpannedProgram := {
        groups := groupSpans, body := sBody, declSpans, sourceNames, bindingHeaders
      }
      return (p, bsItems ++ bsBody, sp)
    | none =>
      throwUnexpectedWithMessage none "duplicate binding names"

/-! ## Doc comments

The grammar skips doc comments like any comment. After parsing, each run of
consecutive doc comments is attached to the binder it precedes: the name after
`let` or `type`, the constructor after `|`, or a binder token directly (a
type's first constructor). Ordinary comments in between are allowed. A doc
comment that precedes anything else is an error, so it can't silently
document nothing. -/

private def docText? : Token → Option String
  | .docComment t => some t
  | _ => none

private def isPlainComment (t : Tok) : Bool :=
  match t.token with
  | .lineComment _ | .blockComment _ => true
  | _ => false

/-- The `val`, `type` or `ctor` binder that starts at the first non-comment
    token of `toks`. -/
private def binderStartingAt (bs : List BinderSpan) (toks : List Tok) : Option BinderSpan :=
  (toks.dropWhile isPlainComment).head?.bind fun t =>
    bs.find? fun b =>
      (b.kind == .val || b.kind == .type || b.kind == .ctor) &&
        b.span.startLine == t.startLine && b.span.startCol == t.startCol

/-- A pattern-let doc comment documents each captured value. Generated storage
    and projection expressions have no independently authored documentation. -/
private def documentedBinders (bs : List BinderSpan) (toks : List Tok) : List BinderSpan :=
  match toks.dropWhile isPlainComment with
  | t :: rest =>
    match t.token with
    | .keyword .«let» =>
        let header := rest.takeWhile fun t => t.token != .punct .eq
        bs.filter fun b => b.kind == .val && header.any fun t => b.span == Span.ofTok t
    | .keyword .«type» | .punct .pipe => (binderStartingAt bs rest).toList
    | _ => (binderStartingAt bs (t :: rest)).toList
  | [] => []

/-- Attach doc comments to binders (see above). -/
partial def attachDocs (bs : List BinderSpan) : List Tok → Except ParseError (List BinderSpan)
  | [] => .ok bs
  | t :: rest =>
    match t.token with
    | .docComment text =>
      let more := rest.takeWhile (docText? ·.token |>.isSome)
      let after := rest.drop more.length
      let doc := String.intercalate "\n" (text :: more.filterMap (docText? ·.token))
      match documentedBinders bs after with
      | [] => .error {
          msg := "a doc comment must come before a `let`, a `type` or a constructor"
          line := t.startLine, col := t.startCol, endLine := t.endLine, endCol := t.endCol }
      | documented => attachDocs (bs.map fun b =>
          if documented.any (· == b) then { b with doc? := some doc } else b) after
    | _ => attachDocs bs rest

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
  (runLexParse polyTy src).map (·.1)

def parseExpr (src : String) : Except ParseError Expr :=
  (runLexParse expr src).map (·.1)

def parseExprWithBinders (src : String) : Except ParseError (Expr × List BinderSpan) :=
  (runLexParse expr src).map fun (e, bs, _) =>
    (e, bs.filterMap fun b => if b.isDef then some b.toBinderSpan else none)

def parseExprWithSpans (src : String) :
    Except ParseError (Expr × List BinderSpan × SpannedExpr) :=
  (runLexParse expr src).map fun (e, bs, sp) =>
    (e, bs.filterMap (fun b => if b.isDef then some b.toBinderSpan else none), sp)

/-- Parse with binder spans (carrying doc comments) + spanned program (expr
    hulls for scopes). -/
def parseProgramWithSpans (src : String) :
    Except ParseError (Program × List BinderSpan × SpannedProgram) :=
  match Lex.lex src with
  | .error e => .error (lexToParse e)
  | .ok toks => do
    let (p, bs, sp) ← runTokP program toks
    let refs := bs.filterMap fun b =>
      if b.isDef then none else
        some ({
          name := b.name
          span := b.span
          kind := match b.kind with
            | .type => .type
            | .ctor => .ctor
            | _ => if b.name == "_" then .typeHole else .typeVar } : Surface.Span.NameReference)
    let defs := bs.filterMap fun b => if b.isDef then some b.toBinderSpan else none
    let defs ← attachDocs defs toks.toList
    pure (p, defs, { sp with references := refs })

def parseProgramWithBinders (src : String) : Except ParseError (Program × List BinderSpan) :=
  parseProgramWithSpans src |>.map fun (p, bs, _) => (p, bs)

def parseProgram (src : String) : Except ParseError Program :=
  parseProgramWithBinders src |>.map Prod.fst

/-! ## Inline checks -/

#guard (parseTy "Int").isOk
#guard (parseTy "Int -> Bool").isOk
#guard (parseTy "(Int, Bool)").isOk
#guard match parseTy "_" with
  | .ok .hole => true
  | _ => false
#guard match parseTy "Int -> _" with
  | .ok (.arrow (.prim .int) .hole) => true
  | _ => false
#guard match parseTy "List _" with
  | .ok (.customTy (.mk "List") [.hole]) => true
  | _ => false
#guard match applyTyArgs .hole [.prim .int] with
  | .error _ => true
  | _ => false

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
#guard (match parseTy "Int /- x -/ -> Bool" with
  | .ok (.arrow (.prim .int) (.prim .bool)) => true | _ => false)
#guard (match parseTy "-- c\nInt" with
  | .ok (.prim .int) => true | _ => false)

/-- `true` iff `parseTy src` is `.ok expected` (compare via `repr`; `Ty` has no `DecidableEq`). -/
def parseTyEq (src : String) (expected : Ty) : Bool :=
  reprStr (parseTy src) == reprStr (Except.ok (ε := ParseError) expected)

-- Bounds syntax is retired rather than reinterpreted as a nominal `BL` type.
#guard !(parseTy "BL").isOk
#guard !(parseTy "BL 0").isOk
#guard !(parseTy "BL 0 5").isOk
#guard !(parseTy "BL 0 5 Int").isOk

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

#guard !(parsePolyTy "{n : Nat, a} a -> a").isOk

-- lex errors surface as ParseError
#guard (match parseTy "\t" with
  | .error { msg := "tab character", line := 1, col := 1, endLine := 1, endCol := 2 } => true
  | _ => false)

-- Parse diagnostics: string / unsupported `*` must not soft-fail to parent `let`.
#guard (match parseProgramWithSpans "let y = \"bla\"\ny\n" with
  | .error e =>
      (e.msg.splitOn "string").length > 1 && e.line == 1 && e.col == 9 && e.endCol == 14
  | .ok _ => false)
#guard (match parseProgramWithSpans "let y = 3 * 4\ny\n" with
  | .error e =>
      e.line == 1 && e.col == 11 && e.endCol == 12
  | .ok _ => false)
#guard (match parseProgramWithSpans "let xs = [3 * 4]\nxs\n" with
  | .error e =>
      e.col == 13
  | .ok _ => false)
-- Retired bounds/count syntax is rejected at the parser boundary.
#guard !(parseProgramWithSpans
  "let f : BL 0 1 Int = []\nf\n").isOk
#guard !(parseExpr "\\(xs : BL 0 1 Int) -> xs").isOk

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
#guard (match parseExpr "1 /- x -/ + 2" with
  | .ok (.app (.app (.primBinOp .intAdd) (.primLit (.int 1))) (.primLit (.int 2))) => true
  | _ => false)

/-! ### Layout: let / if / match -/

#guard (parseExpr "let x = 1 in x").isOk
#guard (parseExpr "if True then 1 else 0").isOk
#guard (parseExpr "match True with | True -> 1 | False -> 0").isOk
#guard (parseExpr "match True with True -> 1 | False -> 0").isOk
#guard (match parseExpr "match xs with | a :: b :: rest -> a" with | .ok _ => true | _ => false)

#guard (match parseExpr "let x = 1 in x" with
  | .ok (.letIn (.mk "x") [] [] none (.primLit (.int 1)) (.var (.mk "x"))) => true
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

-- Multi-line independent bindings remain nested letIns; their order is free.
#guard (match parseExpr "let x = 1\n    y = 2\nin x" with
  | .ok (.letIn (.mk "x") [] [] none (.primLit (.int 1))
      (.letIn (.mk "y") [] [] none (.primLit (.int 2)) (.var (.mk "x")))) => true
  | .ok (.letIn (.mk "y") [] [] none (.primLit (.int 2))
      (.letIn (.mk "x") [] [] none (.primLit (.int 1)) (.var (.mk "x")))) => true
  | _ => false)

-- Acyclic forward references are dependency-sorted, but remain ordinary letIns.
#guard (match parseExpr "let x = y\n    y = 1\nin x" with
  | .ok (.letIn (.mk "y") [] [] none (.primLit (.int 1))
      (.letIn (.mk "x") [] [] none (.var (.mk "y")) (.var (.mk "x")))) => true
  | _ => false)

-- mutually recursive siblings become one local SCC (member order is immaterial)
#guard (match parseExpr "let f : Int -> Int = \\x -> g x\n    g : Int -> Int = \\x -> f x\nin f" with
  | .ok (.letRecIn bs (.var (.mk "f"))) =>
      bs.length = 2 && (bs.map (·.name)).contains (.mk "f") &&
        (bs.map (·.name)).contains (.mk "g")
  | _ => false)

-- optional `: polyTy` on let binder
#guard (match parseExpr "let x : Int = 1 in x" with
  | .ok (.letIn (.mk "x") [] [] (some ⟨[], .prim .int⟩) (.primLit (.int 1)) (.var (.mk "x"))) => true
  | _ => false)

-- Let head-binder sugar remains deliberately unsupported until annotations
-- have real type holes; explicit RHS lambdas are the supported spelling.
#guard !(parseExpr "let f (x : Int) = x in f").isOk
#guard !(parseExpr "let f a b = a in f").isOk
#guard !(parseExpr "let f (x : Int) : Int = x in f").isOk
#guard !(parseExpr "let f {a} (x : a) : a = x in f").isOk

-- typed lambda binder `(n : ty)`
#guard (parseExpr "\\(n : Int) -> n").isOk
#guard (match parseExpr "\\(n : Int) -> n" with
  | .ok (.lambda (.name (.mk "n")) (some (.prim .int)) (.var (.mk "n"))) => true
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

-- a bare nullary type name in a field does not absorb the following fields
#guard (match parseProgram "type T = Leaf | Node T Int T" with
  | .ok p =>
    match p.decls with
    | [⟨.mk "T", [],
        [(.mk "Leaf", []),
         (.mk "Node", [.customTy (.mk "T") [], .prim .int, .customTy (.mk "T") []])]⟩] => true
    | _ => false
  | _ => false)
-- applied field types are parenthesised
#guard (match parseProgram "type Box = Box (List Int) Bool" with
  | .ok p =>
    match p.decls with
    | [⟨.mk "Box", [], [(.mk "Box", [.customTy (.mk "List") [.prim .int], .prim .bool])]⟩] => true
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
          | { name := .mk "x", tyParams := [], params := [], ann := none,
              rhs := .primLit (.int 1) } => true | _ => false) &&
        flat.any (fun b => match b with
          | { name := .mk "y", tyParams := [], params := [], ann := none,
              rhs := .primLit (.int 2) } => true | _ => false)
    | _ => false
  | _ => false)

#guard (match parseProgram "let f : Int -> Int = \\x -> x" with
  | .ok p =>
    match p.groups, p.body with
    | [[{ name := .mk "f", tyParams := [], params := [],
          ann := some ⟨[], .arrow (.prim .int) (.prim .int)⟩,
          rhs := .lambda (.name (.mk "x")) none (.var (.mk "x")) }]],
      .primLit .unit => true
    | _, _ => false
  | _ => false)

#guard !(parseProgram "let f {a} (x : a) : a = x\nf").isOk

#guard !(parseProgram "let id : {n : Nat, a} a -> a = \\x -> x\nid").isOk

-- newline RHS indented past `let` (not past the binder name)
#guard (parseProgram "let map : {a} a -> a =\n  \\x -> x\nmap").isOk
#guard (match parseExpr "let x =\n  1\nin x" with
  | .ok (.letIn (.mk "x") [] [] none (.primLit (.int 1)) (.var (.mk "x"))) => true
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

-- A type declaration ends at the next unindented line, so the program's body
-- isn't read as another constructor field.
private def ctorArities (src : String) : Option (List (List Nat)) :=
  (parseProgram src).toOption.map (·.decls.map (·.ctors.map (·.2.length)))

#guard ctorArities "type Color = Red | Green | Blue\n\nBlue\n" = some [[0, 0, 0]]
#guard ctorArities "type T = A Int\n\nx\n" = some [[1]]
#guard ctorArities "type T a = Leaf | Node a\n  (T a)\nx\n" = some [[0, 2]]

-- An error inside a `let`, `if` or `match` keeps its message and position.
private def programErrorAt (src : String) : Option (String × Nat × Nat) :=
  match parseProgramWithSpans src with
  | .error e => some (e.msg, e.line, e.col)
  | .ok _ => none

#guard programErrorAt "let f = \\p ->\n  match p with\n  | x -> x + x + x\nf 1\n" =
  some ("infix chaining requires parentheses", 3, 18)
#guard programErrorAt "let f = if True then 1 + 1 + 1 else 0\nf\n" =
  some ("infix chaining requires parentheses", 1, 30)
#guard programErrorAt "let f = let y = 1 + 1 + 1 in y\nf\n" =
  some ("infix chaining requires parentheses", 1, 25)

-- Doc comments attach to the binder they precede.
private def docsOf (src : String) : List (String × String) :=
  match parseProgramWithSpans src with
  | .ok (_, bs, _) => bs.filterMap fun b => b.doc?.map (b.name, ·)
  | .error _ => []

private def docErrorAt (src : String) : Option (Nat × Nat) :=
  match parseProgramWithSpans src with
  | .error e => some (e.line, e.col)
  | .ok _ => none

#guard docsOf "/-- The answer. -/\nlet answer = 42\nanswer\n" = [("answer", "The answer.")]
#guard docsOf "--- Shapes.\ntype Shape =\n  --- A circle.\n  | Circle Int\n  /-- A square. -/\n  | Square Int\n1\n" =
  [("Shape", "Shapes."), ("Circle", "A circle."), ("Square", "A square.")]
#guard docsOf "type T = /-- First. -/ A | B\n1\n" = [("A", "First.")]
#guard docsOf "--- One.\n--- Two.\n-- An ordinary comment in between.\nlet x = 1\nx\n" =
  [("x", "One.\nTwo.")]
#guard docsOf "let f = \\y ->\n  --- Local.\n  let z = y in z\nf 1\n" = [("z", "Local.")]
#guard docErrorAt "let x = 1\n/-- Dangling. -/\nx\n" = some (2, 1)
#guard docErrorAt "let f = \\x -> match x with\n  --- An arm.\n  | y -> y\nf 1\n" = some (2, 3)
#guard docErrorAt "-------\nlet x = 1\nx\n" = none

end Surface.Parse
