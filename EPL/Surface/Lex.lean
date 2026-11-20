import UnicodeBasic
import EPL.Surface.Syntax

/-!
# Lexer

FHM's token set: `--` line comments and (nested) block comments are
skipped, tabs are rejected, `-` directly followed by a digit is a negative
literal (so `n -1` is `n` applied to `-1`; write `n - 1`).
-/

namespace EPL.Surface

inductive Keyword where
  | «let» | «in» | «match» | «with» | «if» | «then» | «else» | «type»
  deriving DecidableEq, Repr, Inhabited

inductive Punct where
  | lparen | rparen | lbrace | rbrace | lbrack | rbrack
  | comma | colon | eq | pipe | arrow | backslash | underscore
  deriving DecidableEq, Repr, Inhabited

inductive Token where
  /-- An identifier; `upper` if it starts with an uppercase letter. -/
  | ident (name : String) (upper : Bool)
  /-- `?name` -/
  | namedHole (name : String)
  | keyword (keyword : Keyword)
  | int (value : Int)
  | char (value : Char)
  | string (value : String)
  | op (op : BinOp)
  | punct (punct : Punct)
  deriving DecidableEq, Repr, Inhabited

structure Tok where
  token : Token
  span : Span
  deriving Repr, Inhabited

inductive LexErrorReason where
  | tab
  | unexpectedChar (char : Char)
  | unterminatedComment
  | unterminatedChar
  | unterminatedString
  | badEscape
  deriving DecidableEq, Repr

structure LexError where
  pos : Pos
  reason : LexErrorReason
  deriving DecidableEq, Repr

def keywordOf : String → Option Keyword
  | "let" => some .let | "in" => some .in | "match" => some .match | "with" => some .with
  | "if" => some .if | "then" => some .then | "else" => some .else | "type" => some .type
  | _ => none

/-- Common emoji / pictograph blocks, which FHM allows in identifiers. -/
def isEmoji (c : Char) : Bool :=
  let v := c.val
  (0x1F300 ≤ v && v ≤ 0x1FAFF) || (0x2600 ≤ v && v ≤ 0x27BF) || (0x1F1E6 ≤ v && v ≤ 0x1F1FF)

def isIdentStart (c : Char) : Bool := Unicode.isAlphabetic c || isEmoji c

def isIdentCont (c : Char) : Bool :=
  isIdentStart c || Unicode.GeneralCategory.isMark c || Unicode.isNumeric c || c == '_'

def Pos.right (pos : Pos) (n : Nat := 1) : Pos := ⟨pos.line, pos.col + n⟩

def Pos.next (pos : Pos) : Char → Pos
  | '\n' => ⟨pos.line + 1, 1⟩
  | _ => pos.right

/-- Skip a block comment's body after its opening delimiter, at nesting `depth`. -/
def skipBlockComment (start : Pos) : List Char → Pos → Nat → Except LexError (List Char × Pos)
  | [], _, _ => .error ⟨start, .unterminatedComment⟩
  | '\t' :: _, pos, _ => .error ⟨pos, .tab⟩
  | '-' :: '/' :: rest, pos, depth =>
      if depth ≤ 1 then .ok (rest, pos.right 2)
      else skipBlockComment start rest (pos.right 2) (depth - 1)
  | '/' :: '-' :: rest, pos, depth => skipBlockComment start rest (pos.right 2) (depth + 1)
  | c :: rest, pos, depth => skipBlockComment start rest (pos.next c) depth

/-- Skip a line comment, up to (not including) the newline. -/
def skipLineComment : List Char → Pos → Except LexError (List Char × Pos)
  | [], pos => .ok ([], pos)
  | '\n' :: rest, pos => .ok ('\n' :: rest, pos)
  | '\t' :: _, pos => .error ⟨pos, .tab⟩
  | _ :: rest, pos => skipLineComment rest pos.right

/-- The character after a backslash. -/
def escape : Char → Option Char
  | 'n' => some '\n' | 't' => some '\t' | 'r' => some '\r' | '0' => some (Char.ofNat 0)
  | '\\' => some '\\' | '\'' => some '\'' | '"' => some '"'
  | _ => none

/-- One character of a character or string literal. -/
def takeLitChar (pos : Pos) : List Char → Option (Except LexError (Char × List Char × Pos))
  | '\\' :: c :: rest => some <| match escape c with
      | some e => .ok (e, rest, pos.right 2)
      | none => .error ⟨pos, .badEscape⟩
  | '\n' :: _ | [] => none
  | '\t' :: _ => some (.error ⟨pos, .tab⟩)
  | c :: rest => some (.ok (c, rest, pos.right))

/-- A string literal's body after the opening quote, up to and including the
closing quote. -/
def takeString (start : Pos) (acc : String) : List Char → Pos → Except LexError (String × List Char × Pos)
  | '"' :: rest, pos => .ok (acc, rest, pos.right)
  | '\\' :: c :: rest, pos =>
      match escape c with
      | some e => takeString start (acc.push e) rest (pos.right 2)
      | none => .error ⟨pos, .badEscape⟩
  | '\n' :: _, _ | [], _ => .error ⟨start, .unterminatedString⟩
  | '\t' :: _, pos => .error ⟨pos, .tab⟩
  | c :: rest, pos => takeString start (acc.push c) rest pos.right

def digitsValue (digits : List Char) : Nat :=
  digits.foldl (fun n d => 10 * n + (d.toNat - '0'.toNat)) 0

/-- The token for a punctuation or operator character. -/
def symbolToken : Char → Option Token
  | '+' => some (.op .add) | '<' => some (.op .lt)
  | '(' => some (.punct .lparen) | ')' => some (.punct .rparen)
  | '{' => some (.punct .lbrace) | '}' => some (.punct .rbrace)
  | '[' => some (.punct .lbrack) | ']' => some (.punct .rbrack)
  | ',' => some (.punct .comma) | '=' => some (.punct .eq) | '|' => some (.punct .pipe)
  | ':' => some (.punct .colon) | '\\' => some (.punct .backslash)
  | '_' => some (.punct .underscore)
  | _ => none

/-- Lex `cs` from `pos`. Each step consumes at least one character, so
`cs.length + 1` is enough fuel. -/
def lexChars : Nat → List Char → Pos → Array Tok → Except LexError (Array Tok)
  | 0, _, pos, _ => .error ⟨pos, .unexpectedChar ' '⟩ -- unreachable
  | _ + 1, [], _, acc => .ok acc
  | fuel + 1, c :: rest, pos, acc =>
      let emit (token : Token) (rest : List Char) (stop : Pos) :=
        lexChars fuel rest stop (acc.push ⟨token, ⟨pos, stop⟩⟩)
      match c, rest with
      | '\t', _ => .error ⟨pos, .tab⟩
      | ' ', _ | '\r', _ => lexChars fuel rest pos.right acc
      | '\n', _ => lexChars fuel rest (pos.next '\n') acc
      | '-', '-' :: rest => do
          let (rest, stop) ← skipLineComment rest (pos.right 2)
          lexChars fuel rest stop acc
      | '/', '-' :: rest => do
          let (rest, stop) ← skipBlockComment pos rest (pos.right 2) 1
          lexChars fuel rest stop acc
      | '-', '>' :: rest => emit (.punct .arrow) rest (pos.right 2)
      | ':', ':' :: rest => emit (.op .cons) rest (pos.right 2)
      | '-', d :: more =>
          if d.isDigit then
            let (digits, rest) := (d :: more).span Char.isDigit
            emit (.int (-(digitsValue digits : Int))) rest (pos.right (digits.length + 1))
          else emit (.op .sub) rest pos.right
      | '-', [] => emit (.op .sub) rest pos.right
      | '?', d :: more =>
          if isIdentStart d then
            let (name, rest) := (d :: more).span isIdentCont
            emit (.namedHole (String.ofList name)) rest (pos.right (name.length + 1))
          else .error ⟨pos, .unexpectedChar '?'⟩
      | '\'', _ =>
          match takeLitChar pos.right rest with
          | some (.ok (char, '\'' :: rest, stop)) => emit (.char char) rest stop.right
          | some (.error error) => .error error
          | _ => .error ⟨pos, .unterminatedChar⟩
      | '"', _ => do
          let (value, rest, stop) ← takeString pos "" rest pos.right
          emit (.string value) rest stop
      | _, _ =>
          if c.isDigit then
            let (digits, rest) := (c :: rest).span Char.isDigit
            emit (.int (digitsValue digits)) rest (pos.right digits.length)
          else if isIdentStart c then
            let (name, rest) := (c :: rest).span isIdentCont
            let name := String.ofList name
            let token := match keywordOf name with
              | some keyword => .keyword keyword
              | none => .ident name (Unicode.isUppercase c)
            emit token rest (pos.right name.length)
          else match symbolToken c with
            | some token => emit token rest pos.right
            | none => .error ⟨pos, .unexpectedChar c⟩

def lex (source : String) : Except LexError (Array Tok) :=
  let cs := source.toList
  lexChars (cs.length + 1) cs ⟨1, 1⟩ #[]

end EPL.Surface
