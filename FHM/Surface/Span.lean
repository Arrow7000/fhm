import FHM.Surface.Lex

namespace Surface.Span

open Surface.Lex (TokenWithSource)

/-! ## Source spans for editor hover

Half-open spans matching `TokenWithSource.contains` / the lexer’s 1-based
line/col convention.
-/

structure Span where
  startLine : Nat
  startCol : Nat
  endLine : Nat
  endCol : Nat
  deriving Repr, DecidableEq, BEq

def Span.ofTok (t : TokenWithSource) : Span :=
  { startLine := t.startLine, startCol := t.startCol
    endLine := t.endLine, endCol := t.endCol }

/-- Half-open: contains `(line, col)` iff the position is in `[start, end)` in
    row-major order (1-based), matching `TokenWithSource.contains`. -/
def Span.contains (s : Span) (line col : Nat) : Bool :=
  let afterStart :=
    line > s.startLine || (line == s.startLine && col ≥ s.startCol)
  let beforeEnd :=
    line < s.endLine || (line == s.endLine && col < s.endCol)
  afterStart && beforeEnd

/-- Area proxy for smallest-span hover (same-line width, else line span). -/
def Span.area (s : Span) : Nat :=
  if s.startLine == s.endLine then
    s.endCol - s.startCol
  else
    (s.endLine - s.startLine) * 10000 + (s.endCol + (10000 - s.startCol))

inductive BinderKind
  | val
  | type
  | ctor
  | param
  | pat
  deriving Repr, DecidableEq, BEq, Inhabited

structure BinderSpan where
  name : String
  kind : BinderKind
  span : Span
  deriving Repr, BEq

def BinderKind.toString : BinderKind → String
  | .val => "val"
  | .type => "type"
  | .ctor => "ctor"
  | .param => "param"
  | .pat => "pat"

instance : ToString BinderKind := ⟨BinderKind.toString⟩

#guard (Span.contains ⟨1, 5, 1, 7⟩ 1 5) = true
#guard (Span.contains ⟨1, 5, 1, 7⟩ 1 6) = true
#guard (Span.contains ⟨1, 5, 1, 7⟩ 1 7) = false
#guard (Span.contains ⟨1, 5, 1, 7⟩ 1 4) = false

end Surface.Span
