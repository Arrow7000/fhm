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
  | «inf»
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
  | star
  /-- `∞` — count infinity (same meaning as keyword `inf`). -/
  | infty
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

/-- Surface spellings ↔ keywords. Single source of truth for the lexer and the
    TextMate grammar exporter (`fhm_grammar`). -/
def keywordEntries : List (String × Keyword) := [
  ("let", .«let»),
  ("in", .«in»),
  ("match", .«match»),
  ("with", .«with»),
  ("if", .«if»),
  ("then", .«then»),
  ("else", .«else»),
  ("type", .«type»),
  ("inf", .«inf»)
]

def keywordOf (s : String) : Option Keyword :=
  (keywordEntries.find? fun ⟨spelling, _⟩ => spelling == s).map (·.2)

def keywordSurfaces : List String := keywordEntries.map (·.1)

/-- Bool literals recognized by `classifyIdent` (not keywords). -/
def boolLitSurfaces : List String := ["True", "False"]

/-- Surface spelling of a builtin operator token. -/
def BinOpToken.surface : BinOpToken → String
  | .plus => "+"
  | .minus => "-"
  | .lt => "<"
  | .cons => "::"

/-- All builtin operator surface spellings (longest first for TextMate). -/
def binOpSurfaces : List String :=
  [BinOpToken.cons, .plus, .minus, .lt].map (·.surface)

/-- Surface spelling of a punctuation token. -/
def Punct.surface : Punct → String
  | .lparen => "("
  | .rparen => ")"
  | .lbrace => "{"
  | .rbrace => "}"
  | .lbrack => "["
  | .rbrack => "]"
  | .comma => ","
  | .colon => ":"
  | .eq => "="
  | .pipe => "|"
  | .arrow => "->"
  | .backslash => "\\"
  | .underscore => "_"
  | .star => "*"
  | .infty => "∞"

/-- All punctuation surface spellings (longest first for TextMate). -/
def punctSurfaces : List String :=
  [Punct.arrow, .lparen, .rparen, .lbrace, .rbrace, .lbrack, .rbrack,
   .comma, .colon, .eq, .pipe, .backslash, .underscore, .star, .infty].map (·.surface)

def mkTok (tok : Token) (sl sc el ec : Nat) : TokenWithSource :=
  { token := tok, startLine := sl, startCol := sc, endLine := el, endCol := ec }

/-- Source columns count UTF-16 code units, as in VS Code and Monaco.
    Newlines start a new line; non-BMP characters occupy two columns. -/
def bump (line col : Nat) (c : Char) : Nat × Nat :=
  if c == '\n' then (line + 1, 1) else (line, col + if c.toNat > 0xFFFF then 2 else 1)

/-- Digits → `Nat`, remaining chars. -/
def takeDigits (cs : List Char) (acc : Nat) : Nat × List Char :=
  match cs with
  | c :: rest =>
    if c.isDigit then
      takeDigits rest (acc * 10 + (c.toNat - '0'.toNat))
    else
      (acc, cs)
  | [] => (acc, [])

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

/-- Classify a raw ident string as keyword, bool lit, or ident. -/
def classifyIdent (raw : String) (isUpper : Bool) : Token :=
  match keywordOf raw with
  | some kw => .keyword kw
  | none =>
    match raw with
    | "True" => .boolLit true
    | "False" => .boolLit false
    | _ => .ident raw isUpper

/-- Half-open source span: contains `(line, col)` iff the position is in
    `[start, end)` in row-major order (1-based line/col, matching the lexer). -/
def TokenWithSource.contains (t : TokenWithSource) (line col : Nat) : Bool :=
  let afterStart :=
    line > t.startLine || (line == t.startLine && col ≥ t.startCol)
  let beforeEnd :=
    line < t.endLine || (line == t.endLine && col < t.endCol)
  afterStart && beforeEnd

/-- Token whose half-open span covers `(line, col)`, if any. -/
def tokenAt (tokens : Array TokenWithSource) (line col : Nat) : Option TokenWithSource :=
  tokens.find? (·.contains line col)

/-- Ident text at `(line, col)`, if the covering token is an ident. -/
def identAt (tokens : Array TokenWithSource) (line col : Nat) : Option String :=
  match tokenAt tokens line col with
  | some { token := .ident raw _, .. } => some raw
  | _ => none

theorem keywordOf_let : keywordOf "let" = some .«let» := rfl
theorem keywordOf_foo : keywordOf "foo" = none := rfl
theorem classifyIdent_True : classifyIdent "True" false = .boolLit true := rfl
theorem classifyIdent_let : classifyIdent "let" false = .keyword .«let» := rfl

end Surface.Lex
