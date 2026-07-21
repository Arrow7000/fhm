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

/-- Axis-aligned hull of two spans (row-major min start / max end). -/
def Span.union (a b : Span) : Span :=
  let startLe :=
    a.startLine < b.startLine ||
      (a.startLine == b.startLine && a.startCol ≤ b.startCol)
  let endLe :=
    a.endLine < b.endLine ||
      (a.endLine == b.endLine && a.endCol ≤ b.endCol)
  { startLine := if startLe then a.startLine else b.startLine
    startCol := if startLe then a.startCol else b.startCol
    endLine := if endLe then b.endLine else a.endLine
    endCol := if endLe then b.endCol else a.endCol }

/-- Fold `union` over a nonempty list. -/
def Span.hull : List Span → Option Span
  | [] => none
  | s :: ss => some (ss.foldl Span.union s)

/-- Empty / missing span placeholder (contains nothing useful). -/
def Span.empty : Span := ⟨1, 1, 1, 1⟩

/-! ## Spanned expression mirror (parse sidecar; not SurfaceLang) -/

/-- Parallel tree of expression hull spans. Constructors mirror `Surface.Expr`
    enough for scope collection; no binder names (those live in `BinderSpan`). -/
inductive SpannedExpr where
  | leaf (span : Span)
  | pair (span : Span) (a b : SpannedExpr)
  | cons (span : Span) (head tail : SpannedExpr)
  | list (span : Span) (items : List SpannedExpr)
  | lambda (span : Span) (body : SpannedExpr)
  | app (span : Span) (f input : SpannedExpr)
  | letIn (span : Span) (rhs body : SpannedExpr)
  | letRecIn (span : Span) (rhss : List SpannedExpr) (body : SpannedExpr)
  | ife (span : Span) (c t f : SpannedExpr)
  | match_ (span : Span) (scrut : SpannedExpr) (armBodies : List SpannedExpr)
  deriving Repr

instance : Inhabited SpannedExpr := ⟨.leaf Span.empty⟩

def SpannedExpr.span : SpannedExpr → Span
  | .leaf s => s
  | .pair s .. => s
  | .cons s .. => s
  | .list s .. => s
  | .lambda s .. => s
  | .app s .. => s
  | .letIn s .. => s
  | .letRecIn s .. => s
  | .ife s .. => s
  | .match_ s .. => s

/-- Spanned top-level program: RHS hulls per binding in group order + body. -/
structure SpannedProgram where
  groups : List (List SpannedExpr)
  body : SpannedExpr
  deriving Repr

instance : Inhabited SpannedProgram := ⟨⟨[], default⟩⟩

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
#guard (Span.union ⟨1, 1, 1, 3⟩ ⟨1, 5, 2, 4⟩ == ⟨1, 1, 2, 4⟩) = true
#guard (Span.hull [⟨1, 2, 1, 4⟩, ⟨1, 1, 1, 3⟩] == some ⟨1, 1, 1, 4⟩) = true
#guard (Span.hull ([] : List Span)).isNone = true

end Surface.Span
