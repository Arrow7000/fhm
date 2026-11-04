import FHM.Unverified.Surface.Lex
import FHM.Surface.Span

/-! Editor token recovery from native lexer checkpoints. Closed malformed
literals are withheld as complete tokens; unfinished strings/comments keep the
accepted prefix and consume the tail. Apparent keywords inside them stay text. -/
namespace FHM.Unverified.LexRecovery
open Surface.Lex Surface.Span

structure Gap where
  error : LexError
  span : Span
  commentOnly : Bool

structure Result where
  tokens : Array TokenWithSource := #[]
  gaps : List Gap := []
  markers : Array TokenWithSource := #[]

private structure Rest where
  chars : List Char
  line : Nat
  col : Nat

private def advance (line col : Nat) (chars : List Char) : Nat × Nat :=
  chars.foldl (fun position char => bump position.1 position.2 char) (line, col)

private def quoted (quote : Char) : List Char → Nat → Nat → Rest
  | [], line, col => ⟨[], line, col⟩
  | '\\' :: char :: rest, line, col =>
      let (line, col) := advance line col ['\\', char]
      quoted quote rest line col
  | char :: rest, line, col =>
      if char == quote then
        let (line, col) := bump line col char
        ⟨rest, line, col⟩
      else if quote == '\'' && char == '\n' then
        ⟨char :: rest, line, col⟩
      else
        let (line, col) := bump line col char
        quoted quote rest line col

private def blockComment : Nat → List Char → Nat → Nat → Rest
  | _, [], line, col => ⟨[], line, col⟩
  | depth, '/' :: '-' :: rest, line, col => blockComment (depth + 1) rest line (col + 2)
  | depth, '-' :: '/' :: rest, line, col =>
      if depth ≤ 1 then ⟨rest, line, col + 2⟩ else blockComment (depth - 1) rest line (col + 2)
  | depth, char :: rest, line, col =>
      let (line, col) := bump line col char
      blockComment depth rest line col
termination_by _ chars _ _ => chars.length

private def skip (failure : Failure) : Rest × Bool :=
  match failure.remaining with
  | '"' :: rest => (quoted '"' rest failure.line (failure.col + 1), false)
  | '\'' :: rest => (quoted '\'' rest failure.line (failure.col + 1), false)
  | '/' :: '-' :: rest => (blockComment 1 rest failure.line (failure.col + 2), true)
  | '-' :: '-' :: rest =>
      let contents := rest.takeWhile (· != '\n')
      let (line, col) := advance failure.line (failure.col + 2) contents
      (⟨rest.drop contents.length, line, col⟩, true)
  | char :: rest =>
      let (line, col) := bump failure.line failure.col char
      (⟨rest, line, col⟩, false)
  | [] => (⟨[], failure.line, failure.col⟩, false)

/-- Preserve native tokens and exact UTF-16 coordinates around rejected lexical
regions. Consumers must quarantine code owning a non-comment gap, rather than
accepting a program obtained by silently deleting its malformed token. -/
def check (source : String) : Result :=
  let rec go (fuel : Nat) (chars : List Char) (line col : Nat) (result : Result) : Result :=
    match lexWithCheckpoint chars line col with
    | .ok tokens => { result with tokens := result.tokens ++ tokens }
    | .error failure =>
        let (rest, commentOnly) := skip failure
        let gap : Gap := ⟨failure.error, ⟨failure.line, failure.col, rest.line, rest.col⟩, commentOnly⟩
        let marker : Token := if commentOnly then .blockComment "" else
          match failure.remaining with
          | '"' :: _ | '\'' :: _ => .stringLit ""
          | _ => .punct .underscore
        let marker := mkTok marker failure.line failure.col rest.line rest.col
        let result : Result := {
          tokens := result.tokens ++ failure.tokens
          gaps := result.gaps ++ [gap]
          markers := result.markers.push marker }
        match fuel with
        | 0 => result
        | fuel + 1 =>
            if rest.chars.length ≥ chars.length then result
            else go fuel rest.chars rest.line rest.col result
  go (source.toList.length + 1) source.toList 1 1 {}

/-- Opaque gap markers are only editor tokens; they never enter the parser. -/
def Result.editorTokens (result : Result) : Array TokenWithSource :=
  if result.markers.isEmpty then result.tokens else
    ((result.tokens ++ result.markers).toList.mergeSort (fun a b =>
      a.startLine < b.startLine || (a.startLine == b.startLine && a.startCol ≤ b.startCol))).toArray

end FHM.Unverified.LexRecovery
