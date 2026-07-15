import Parser
import FHM.Surface.Lex
import FHM.SurfaceLang

namespace Surface.Parse

open Parser
open Surface.Lex (Token TokenWithSource LexError Punct)

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

end Surface.Parse
