import FHM.SurfaceLang
import UnicodeBasic

namespace Surface.Lex

/-- Keywords reserved by the surface language. -/
inductive Keyword
  | «let»
  | «in»
  | «match»
  | «with»
  | «if»
  | «then»
  | «else»
  | «type»
  deriving Repr, DecidableEq, BEq, Inhabited

/-- Builtin binary / cons operator tokens (not punctuation). -/
inductive BinOpToken
  | plus
  | minus
  | lt
  | cons
  deriving Repr, DecidableEq, BEq, Inhabited

/-- Punctuation and structural tokens. -/
inductive Punct
  | lparen
  | rparen
  | lbrace
  | rbrace
  | lbrack
  | rbrack
  | comma
  | colon
  | eq
  | pipe
  | arrow
  | backslash
  | underscore
  deriving Repr, DecidableEq, BEq, Inhabited

/-- Lexical tokens. Whitespace is skipped (positions still tracked). -/
inductive Token
  | lineComment (text : String)
  | blockComment (text : String)
  | ident (raw : String) (isUpper : Bool)
  | keyword (kw : Keyword)
  | intLit (n : Int)
  | charLit (c : Char)
  | stringLit (s : String)
  | boolLit (b : Bool)
  | op (o : BinOpToken)
  | punct (p : Punct)
  deriving Repr, DecidableEq, BEq

structure TokenWithSource where
  token : Token
  startLine : Nat
  startCol : Nat
  endLine : Nat
  endCol : Nat
  deriving Repr

inductive LexError
  | tab (line col : Nat)
  | unexpectedChar (c : Char) (line col : Nat)
  | unfinishedBlockComment (line col : Nat)
  | badEscape (line col : Nat)
  deriving Repr, DecidableEq, BEq

/-! ### Character classes

`isUpper` on idents: first character is a Unicode uppercase letter
(`Unicode.isUppercase`, which includes ASCII `A`–`Z` and Lu such as `É`).
Emoji / pictograph starts are never upper.
-/

/-- Common emoji / pictograph blocks (not full Extended_Pictographic). -/
def isEmoji (c : Char) : Bool :=
  let v := c.val
  (0x1F300 ≤ v && v ≤ 0x1FAFF) ||
  (0x2600 ≤ v && v ≤ 0x27BF) ||
  (0x1F1E6 ≤ v && v ≤ 0x1F1FF)

def isIdentStart (c : Char) : Bool :=
  Unicode.isAlphabetic c || isEmoji c

def isIdentCont (c : Char) : Bool :=
  isIdentStart c || Unicode.GeneralCategory.isMark c || Unicode.isNumeric c || c == '_'

def keywordOf (s : String) : Option Keyword :=
  match s with
  | "let" => some .«let»
  | "in" => some .«in»
  | "match" => some .«match»
  | "with" => some .«with»
  | "if" => some .«if»
  | "then" => some .«then»
  | "else" => some .«else»
  | "type" => some .«type»
  | _ => none

def mkTok (tok : Token) (sl sc el ec : Nat) : TokenWithSource :=
  { token := tok, startLine := sl, startCol := sc, endLine := el, endCol := ec }

/-- Advance one character: newline bumps line; other chars bump column. -/
def bump (line col : Nat) (c : Char) : Nat × Nat :=
  if c == '\n' then (line + 1, 1) else (line, col + 1)

/-- Digits → `Nat`, remaining chars. -/
def takeDigits (cs : List Char) (acc : Nat) : Nat × List Char :=
  match cs with
  | c :: rest =>
    if c.isDigit then
      takeDigits rest (acc * 10 + (c.toNat - '0'.toNat))
    else
      (acc, cs)
  | [] => (acc, [])

/-- Line comment body after `--`; leaves the newline (if any) in the stream. -/
partial def takeLineComment (cs : List Char) (line col : Nat) (acc : String) :
    Except LexError (String × List Char × Nat × Nat) :=
  match cs with
  | [] => .ok (acc, [], line, col)
  | '\t' :: _ => .error (.tab line col)
  | '\n' :: _ => .ok (acc, cs, line, col)
  | c :: rest =>
    let (line', col') := bump line col c
    takeLineComment rest line' col' (acc.push c)

/-- Nested `{- … -}`; `depth` starts at 1 after the opening `{-`. -/
partial def takeBlockComment (cs : List Char) (line col : Nat) (depth : Nat) (acc : String)
    (startLine startCol : Nat) :
    Except LexError (String × List Char × Nat × Nat) :=
  match cs with
  | [] => .error (.unfinishedBlockComment startLine startCol)
  | '\t' :: _ => .error (.tab line col)
  | '{' :: '-' :: rest =>
    takeBlockComment rest line (col + 2) (depth + 1) (acc.push '{' |>.push '-')
      startLine startCol
  | '-' :: '}' :: rest =>
    if depth == 1 then
      .ok (acc, rest, line, col + 2)
    else
      takeBlockComment rest line (col + 2) (depth - 1) (acc.push '-' |>.push '}')
        startLine startCol
  | c :: rest =>
    let (line', col') := bump line col c
    takeBlockComment rest line' col' depth (acc.push c) startLine startCol

/-- Escape after `\`; returns decoded char and advanced position.
    Supported: `\\`, `\"`, `\n`, `\r`, `\'`. -/
def takeEscape (cs : List Char) (line col : Nat) :
    Except LexError (Char × List Char × Nat × Nat) :=
  match cs with
  | [] => .error (.badEscape line col)
  | 'n' :: rest => .ok ('\n', rest, line, col + 1)
  | 'r' :: rest => .ok ('\r', rest, line, col + 1)
  | '\\' :: rest => .ok ('\\', rest, line, col + 1)
  | '"' :: rest => .ok ('"', rest, line, col + 1)
  | '\'' :: rest => .ok ('\'', rest, line, col + 1)
  | _ :: _ => .error (.badEscape line col)

/-- Char literal after opening `'`. -/
def takeCharLit (cs : List Char) (line col : Nat) (startLine startCol : Nat) :
    Except LexError (Char × List Char × Nat × Nat) :=
  match cs with
  | [] => .error (.unexpectedChar '\'' startLine startCol)
  | '\t' :: _ => .error (.tab line col)
  | '\\' :: rest =>
    match takeEscape rest line (col + 1) with
    | .error e => .error e
    | .ok (ch, rest', line', col') =>
      match rest' with
      | '\'' :: rest'' => .ok (ch, rest'', line', col' + 1)
      | _ => .error (.unexpectedChar '\'' startLine startCol)
  | '\'' :: _ => .error (.unexpectedChar '\'' line col)
  | c :: '\'' :: rest =>
    let (line', col') := bump line col c
    .ok (c, rest, line', col' + 1)
  | c :: _ => .error (.unexpectedChar c line col)

/-- String literal after opening `"`. -/
partial def takeStringLit (cs : List Char) (line col : Nat) (acc : String)
    (startLine startCol : Nat) :
    Except LexError (String × List Char × Nat × Nat) :=
  match cs with
  | [] => .error (.unexpectedChar '"' startLine startCol)
  | '\t' :: _ => .error (.tab line col)
  | '"' :: rest => .ok (acc, rest, line, col + 1)
  | '\\' :: rest =>
    match takeEscape rest line (col + 1) with
    | .error e => .error e
    | .ok (ch, rest', line', col') =>
      takeStringLit rest' line' col' (acc.push ch) startLine startCol
  | c :: rest =>
    let (line', col') := bump line col c
    takeStringLit rest line' col' (acc.push c) startLine startCol

/-- Identifier body after the first character. -/
partial def takeIdentCont (cs : List Char) (line col : Nat) (acc : String) :
    String × List Char × Nat × Nat :=
  match cs with
  | c :: rest =>
    if isIdentCont c then
      let (line', col') := bump line col c
      takeIdentCont rest line' col' (acc.push c)
    else
      (acc, cs, line, col)
  | [] => (acc, [], line, col)

/-- Classify a raw ident string as keyword, bool lit, or ident. -/
def classifyIdent (raw : String) (isUpper : Bool) : Token :=
  match keywordOf raw with
  | some kw => .keyword kw
  | none =>
    match raw with
    | "True" => .boolLit true
    | "False" => .boolLit false
    | _ => .ident raw isUpper

/-- Full lexer. Positions are 1-based. Skips spaces/newlines/CR; rejects tabs. -/
partial def lex (input : String) : Except LexError (Array TokenWithSource) :=
  let rec go (cs : List Char) (line col : Nat) (acc : Array TokenWithSource) :
      Except LexError (Array TokenWithSource) :=
    match cs with
    | [] => .ok acc
    | '\t' :: _ => .error (.tab line col)
    | ' ' :: rest => go rest line (col + 1) acc
    | '\n' :: rest => go rest (line + 1) 1 acc
    | '\r' :: rest => go rest line col acc
    | '-' :: '-' :: rest =>
      match takeLineComment rest line (col + 2) "" with
      | .error e => .error e
      | .ok (text, rest', line', col') =>
        go rest' line' col'
          (acc.push (mkTok (.lineComment text) line col line' col'))
    | '{' :: '-' :: rest =>
      match takeBlockComment rest line (col + 2) 1 "" line col with
      | .error e => .error e
      | .ok (text, rest', line', col') =>
        go rest' line' col'
          (acc.push (mkTok (.blockComment text) line col line' col'))
    | '-' :: '>' :: rest =>
      go rest line (col + 2)
        (acc.push (mkTok (.punct .arrow) line col line (col + 2)))
    | '-' :: d :: rest =>
      if d.isDigit then
        let (n, rest') := takeDigits (d :: rest) 0
        let consumed := (d :: rest).length - rest'.length
        go rest' line (col + 1 + consumed)
          (acc.push (mkTok (.intLit (Int.negOfNat n)) line col line (col + 1 + consumed)))
      else
        go (d :: rest) line (col + 1)
          (acc.push (mkTok (.op .minus) line col line (col + 1)))
    | '-' :: [] =>
      go [] line (col + 1)
        (acc.push (mkTok (.op .minus) line col line (col + 1)))
    | ':' :: ':' :: rest =>
      go rest line (col + 2)
        (acc.push (mkTok (.op .cons) line col line (col + 2)))
    | c :: rest =>
      if c.isDigit then
        let (n, rest') := takeDigits (c :: rest) 0
        let consumed := (c :: rest).length - rest'.length
        go rest' line (col + consumed)
          (acc.push (mkTok (.intLit (Int.ofNat n)) line col line (col + consumed)))
      else if isIdentStart c then
        let isUpper := Unicode.isUppercase c
        let (line1, col1) := bump line col c
        let (raw, rest', line', col') := takeIdentCont rest line1 col1 (String.ofList [c])
        go rest' line' col'
          (acc.push (mkTok (classifyIdent raw isUpper) line col line' col'))
      else
        match c with
        | '+' =>
          go rest line (col + 1)
            (acc.push (mkTok (.op .plus) line col line (col + 1)))
        | '<' =>
          go rest line (col + 1)
            (acc.push (mkTok (.op .lt) line col line (col + 1)))
        | '(' =>
          go rest line (col + 1)
            (acc.push (mkTok (.punct .lparen) line col line (col + 1)))
        | ')' =>
          go rest line (col + 1)
            (acc.push (mkTok (.punct .rparen) line col line (col + 1)))
        | '{' =>
          go rest line (col + 1)
            (acc.push (mkTok (.punct .lbrace) line col line (col + 1)))
        | '}' =>
          go rest line (col + 1)
            (acc.push (mkTok (.punct .rbrace) line col line (col + 1)))
        | '[' =>
          go rest line (col + 1)
            (acc.push (mkTok (.punct .lbrack) line col line (col + 1)))
        | ']' =>
          go rest line (col + 1)
            (acc.push (mkTok (.punct .rbrack) line col line (col + 1)))
        | ',' =>
          go rest line (col + 1)
            (acc.push (mkTok (.punct .comma) line col line (col + 1)))
        | '=' =>
          go rest line (col + 1)
            (acc.push (mkTok (.punct .eq) line col line (col + 1)))
        | '|' =>
          go rest line (col + 1)
            (acc.push (mkTok (.punct .pipe) line col line (col + 1)))
        | ':' =>
          go rest line (col + 1)
            (acc.push (mkTok (.punct .colon) line col line (col + 1)))
        | '\\' =>
          go rest line (col + 1)
            (acc.push (mkTok (.punct .backslash) line col line (col + 1)))
        | '_' =>
          go rest line (col + 1)
            (acc.push (mkTok (.punct .underscore) line col line (col + 1)))
        | '\'' =>
          match takeCharLit rest line (col + 1) line col with
          | .error e => .error e
          | .ok (ch, rest', line', col') =>
            go rest' line' col'
              (acc.push (mkTok (.charLit ch) line col line' col'))
        | '"' =>
          match takeStringLit rest line (col + 1) "" line col with
          | .error e => .error e
          | .ok (s, rest', line', col') =>
            go rest' line' col'
              (acc.push (mkTok (.stringLit s) line col line' col'))
        | _ => .error (.unexpectedChar c line col)
  go input.toList 1 1 #[]

/-- Token payload only (for `#guard`s). -/
def lexTokens (input : String) : Except LexError (Array Token) :=
  match lex input with
  | .ok a => .ok (a.map (·.token))
  | .error e => .error e

theorem keywordOf_let : keywordOf "let" = some .«let» := rfl
theorem keywordOf_foo : keywordOf "foo" = none := rfl
theorem classifyIdent_True : classifyIdent "True" false = .boolLit true := rfl
theorem classifyIdent_let : classifyIdent "let" false = .keyword .«let» := rfl

private def expectToks (input : String) (expected : Array Token) : Bool :=
  match lexTokens input with
  | .ok ts => decide (ts = expected)
  | .error _ => false

#guard (lex "").isOk
#guard (match lex "\t" with | .error (.tab 1 1) => true | _ => false)

#guard expectToks "-- hi\nlet" #[.lineComment " hi", .keyword .«let»]
#guard expectToks "{- a {- b -} c -}" #[.blockComment " a {- b -} c "]

#guard expectToks "foo" #[.ident "foo" false]
#guard expectToks "Foo" #[.ident "Foo" true]
#guard expectToks "🎉name" #[.ident "🎉name" false]

#guard expectToks "True" #[.boolLit true]
#guard expectToks "False" #[.boolLit false]

#guard expectToks "42" #[.intLit 42]
#guard expectToks "-3" #[.intLit (-3)]

#guard expectToks "->" #[.punct .arrow]
#guard expectToks "::" #[.op .cons]
#guard expectToks "+" #[.op .plus]
#guard expectToks "-" #[.op .minus]
#guard expectToks "<" #[.op .lt]

#guard expectToks "= | : \\ _ ( ) [ ] { } ," #[
  .punct .eq, .punct .pipe, .punct .colon, .punct .backslash, .punct .underscore,
  .punct .lparen, .punct .rparen, .punct .lbrack, .punct .rbrack,
  .punct .lbrace, .punct .rbrace, .punct .comma
]

#guard expectToks "'a'" #[.charLit 'a']
#guard expectToks "\"hi\\n\"" #[.stringLit "hi\n"]
#guard (match lex "\"\\x\"" with | .error (.badEscape ..) => true | _ => false)

#guard expectToks ": :" #[.punct .colon, .punct .colon]
#guard (match lex "- >" with | .error (.unexpectedChar '>' 1 3) => true | _ => false)
#guard (match lex "{- unclosed" with
  | .error (.unfinishedBlockComment 1 1) => true | _ => false)

end Surface.Lex
