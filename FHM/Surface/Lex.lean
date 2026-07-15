import FHM.SurfaceLang

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
  deriving Repr, DecidableEq, Inhabited

/-- Builtin binary / cons operator tokens (not punctuation). -/
inductive BinOpToken
  | plus
  | minus
  | lt
  | cons
  deriving Repr, DecidableEq, Inhabited

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
  deriving Repr, DecidableEq, Inhabited

/-- Lexical tokens. No whitespace tokens: Task 4 will skip WS while tracking positions. -/
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
  deriving Repr, DecidableEq

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
  deriving Repr, DecidableEq

/-- Skeleton lexer: empty succeeds; tab is rejected; anything else is `unexpectedChar`
    until Task 4 fills in real scanners. Positions are 1-based. -/
def lex (input : String) : Except LexError (Array TokenWithSource) :=
  let rec go (cs : List Char) (line col : Nat) : Except LexError (Array TokenWithSource) :=
    match cs with
    | [] => .ok #[]
    | '\t' :: _ => .error (.tab line col)
    | c :: _ => .error (.unexpectedChar c line col)
  go input.toList 1 1

theorem lex_empty : (lex "").isOk = true := rfl

#guard (lex "").isOk
#guard (match lex "\t" with | .error (.tab 1 1) => true | _ => false)
#guard (match lex "a" with | .error (.unexpectedChar 'a' 1 1) => true | _ => false)

end Surface.Lex
