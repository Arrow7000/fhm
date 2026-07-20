import FHM.BLSketch

/-!
# Pretty-printers for `BLSketch`

Readable `String` renderings of counts, types, expressions, and constraint
problems — same spirit as `FHM/Pretty.lean`. Debugging / demo IO only; no
proofs depend on these.

Conventions:
* Rigid count vars print as `a`, `b`, `c`, …; inferables as `?a`, `?b`, ….
* Term de Bruijn indices resolve against a binder name context (`x`, `y`, …);
  dangling indices print as `#n`.
* Scheme rigid binders print as `∀ a b. body` (same letter pool as rigid counts;
  separate from term names).
* Scheme *instantiation* at a var prints as `f @2 @6` (Haskell-style type
  application; not `f[2, 6]`, which looks like an array slice).
* Annotation holes print as `_`.
* Lists: a proper `nil`/`cons` spine prints as `[a, b, c]`; improper as `h :: t`.
* `matchNil` / `matchCons` print as ordinary `match` with only the `[]` or
  `h :: t` arm respectively.
* Self-delimiting count forms (`min`/`max`/`pred`) never take outer parens;
  `+`/`*` do when nested under `BL` or tighter ops.
* Judgement displays (`e : τ`) use `Expr.prettyJudgement`, which wraps only
  forms that clash with an outer ` : ` (anno / match / if / let) — not bare
  lambdas or atoms.
* `let` / scheme-lets print as a vertical telescope:
  ```
  let x : σ =
    binding
  in
  body
  ```
  Plain `let` omits `: σ`. Binding bodies are indented two spaces.
* Parentheses are otherwise inserted only where precedence requires them.
-/

namespace BLSketch

@[inline] def prettyParenIf (b : Bool) (s : String) : String :=
  if b then "(" ++ s ++ ")" else s

/-- Indent every line of `s` by `n` spaces (for let-binding bodies). -/
def prettyIndentBlock (s : String) (n : Nat := 2) : String :=
  let pad := String.ofList (List.replicate n ' ')
  String.intercalate "\n" ((s.splitOn "\n").map (fun line => pad ++ line))

def prettyTermVarName (n : Nat) : String :=
  let letters := ["x", "y", "z", "u", "v", "w", "p", "q", "r", "s", "t"]
  letters.getD n ("v" ++ toString n)

/-- Letters for bound-count indices (rigid `a` / inferable `?a`). -/
def prettyCountVarLetter (n : Nat) : String :=
  let letters := ["a", "b", "c", "d", "e", "f", "g", "h", "i", "j", "k",
    "l", "m", "n", "o", "p", "q", "r", "s", "t"]
  letters.getD n ("t" ++ toString n)

/-! ## Counts -/

/-- Precedence: `0` top, `1` add/min/max, `2` mul, `3` pred/atomic. -/
def Count.prettyAux (prec : Nat) : Count → String
  | .lit n => toString n
  | .var ⟨.rigid, i⟩ => prettyCountVarLetter i
  | .var ⟨.inferable, i⟩ => "?" ++ prettyCountVarLetter i
  | .add a b =>
      prettyParenIf (prec > 1)
        (Count.prettyAux 1 a ++ " + " ++ Count.prettyAux 1 b)
  | .mul a b =>
      prettyParenIf (prec > 2)
        (Count.prettyAux 2 a ++ " * " ++ Count.prettyAux 2 b)
  | .min a b =>
      "min(" ++ Count.prettyAux 0 a ++ ", " ++ Count.prettyAux 0 b ++ ")"
  | .max a b =>
      "max(" ++ Count.prettyAux 0 a ++ ", " ++ Count.prettyAux 0 b ++ ")"
  | .pred a =>
      "pred(" ++ Count.prettyAux 0 a ++ ")"

def Count.pretty (c : Count) : String := Count.prettyAux 0 c

instance : ToString Count := ⟨Count.pretty⟩

/-! ## Types / annotations / schemes -/

/-- Precedence: `0` top, `1` left of arrow, `2` atomic. -/
def Ty.prettyAux (prec : Nat) : Ty → String
  | .unit => "Unit"
  | .arrow a b =>
      prettyParenIf (prec ≥ 1)
        (Ty.prettyAux 1 a ++ " → " ++ Ty.prettyAux 0 b)
  | .bl lo hi =>
      prettyParenIf (prec ≥ 2)
        ("BL " ++ Count.prettyAux 3 lo ++ " " ++ Count.prettyAux 3 hi)

def Ty.pretty (t : Ty) : String := Ty.prettyAux 0 t

instance : ToString Ty := ⟨Ty.pretty⟩

def AnnoTy.prettyBound : Option Count → String
  | none => "_"
  | some c => Count.prettyAux 3 c

def AnnoTy.prettyAux (prec : Nat) : AnnoTy → String
  | .unit => "Unit"
  | .arrow a b =>
      prettyParenIf (prec ≥ 1)
        (AnnoTy.prettyAux 1 a ++ " → " ++ AnnoTy.prettyAux 0 b)
  | .bl lo hi =>
      prettyParenIf (prec ≥ 2)
        ("BL " ++ AnnoTy.prettyBound lo ++ " " ++ AnnoTy.prettyBound hi)

def AnnoTy.pretty (t : AnnoTy) : String := AnnoTy.prettyAux 0 t

instance : ToString AnnoTy := ⟨AnnoTy.pretty⟩

def BScheme.pretty (s : BScheme) : String :=
  if s.binders = 0 then s.body.pretty
  else
    let binders :=
      String.intercalate " " ((List.range s.binders).map prettyCountVarLetter)
    "∀ " ++ binders ++ ". " ++ s.body.pretty

instance : ToString BScheme := ⟨BScheme.pretty⟩

def Binding.pretty : Binding → String
  | .mono ty => ty.pretty
  | .scheme s => s.pretty

instance : ToString Binding := ⟨Binding.pretty⟩

/-- De Bruijn name context for `ctx` (nearest binder first: `x`, then `y`, …). -/
def Ctx.termNames (ctx : Ctx) : List String :=
  (List.range ctx.length).map prettyTermVarName |>.reverse

/-- Typing context as `x : τ` lines, outermost binder first. -/
def Ctx.prettyEnv (ctx : Ctx) : String :=
  let names := Ctx.termNames ctx
  let lines :=
    (List.zip names ctx).reverse.map fun (n, b) => n ++ " : " ++ b.pretty
  String.intercalate "\n" lines

def Ctx.pretty (ctx : Ctx) : String :=
  "[" ++ String.intercalate ", " (ctx.map Binding.pretty) ++ "]"

instance : ToString Ctx := ⟨Ctx.pretty⟩

/-! ## Constraints / problems -/

def Constraint.pretty (c : Constraint) : String :=
  c.lhs.pretty ++ " ≤ " ++ c.rhs.pretty

instance : ToString Constraint := ⟨Constraint.pretty⟩

def prettyConstraintList (cs : List Constraint) : String :=
  if cs.isEmpty then "⊤"
  else String.intercalate " ∧ " (cs.map Constraint.pretty)

def ForallProblem.pretty (φ : ForallProblem) : String :=
  if φ.prem.isEmpty then
    "∀σ. " ++ prettyConstraintList φ.goals
  else
    "∀σ. (" ++ prettyConstraintList φ.prem ++ ") ⇒ (" ++
      prettyConstraintList φ.goals ++ ")"

instance : ToString ForallProblem := ⟨ForallProblem.pretty⟩

def ExistsProblem.pretty (ψ : ExistsProblem) : String :=
  let slots :=
    String.intercalate ", " (ψ.inferables.map fun v =>
      match v.kind with
      | .rigid => prettyCountVarLetter v.idx
      | .inferable => "?" ++ prettyCountVarLetter v.idx)
  let head := if ψ.inferables.isEmpty then "∃." else "∃ " ++ slots ++ "."
  let body :=
    if ψ.prem.isEmpty then prettyConstraintList ψ.cons
    else "(" ++ prettyConstraintList ψ.prem ++ ") ⇒ (" ++
      prettyConstraintList ψ.cons ++ ")"
  head ++ " " ++ body

instance : ToString ExistsProblem := ⟨ExistsProblem.pretty⟩

/-! ## Expressions

Precedence: `0` top, `1` lam/let/match/if, `2` app / `::`.
-/

mutual

partial def Expr.prettyListElems (ctx : List String) : Expr → Option (List String)
  | .nil => some []
  | .cons h t =>
      match Expr.prettyListElems ctx t with
      | some ts => some (Expr.prettyAux ctx 0 h :: ts)
      | none => none
  | _ => none

partial def Expr.prettyAux (ctx : List String) (prec : Nat) : Expr → String
  | .unit => "()"
  | .nil => "[]"
  | .cons h t =>
      match Expr.prettyListElems ctx t with
      | some ts =>
          "[" ++ String.intercalate ", " (Expr.prettyAux ctx 0 h :: ts) ++ "]"
      | none =>
          prettyParenIf (prec ≥ 2)
            (Expr.prettyAux ctx 2 h ++ " :: " ++ Expr.prettyAux ctx 0 t)
  | .var i args =>
      let name := (ctx[i]?).getD ("#" ++ toString i)
      if args.isEmpty then name
      else
        -- Haskell-style type application for scheme bound-instantiation.
        name ++ String.join (args.map fun a => " @" ++ Count.pretty a)
  | .lam paramAnn body =>
      let x := prettyTermVarName ctx.length
      prettyParenIf (prec ≥ 1)
        ("λ(" ++ x ++ " : " ++ paramAnn.pretty ++ "). " ++
          Expr.prettyAux (x :: ctx) 0 body)
  | .app f a =>
      prettyParenIf (prec ≥ 2)
        (Expr.prettyAux ctx 1 f ++ " " ++ Expr.prettyAux ctx 2 a)
  | .if_ c t e =>
      prettyParenIf (prec ≥ 1)
        ("if " ++ Expr.prettyAux ctx 0 c ++ " then " ++
          Expr.prettyAux ctx 0 t ++ " else " ++ Expr.prettyAux ctx 0 e)
  | .anno e ty =>
      prettyParenIf (prec ≥ 1)
        (Expr.prettyAux ctx 1 e ++ " : " ++ ty.pretty)
  | .let_ b e =>
      let x := prettyTermVarName ctx.length
      prettyParenIf (prec ≥ 1)
        ("let " ++ x ++ " =\n" ++
          prettyIndentBlock (Expr.prettyAux ctx 0 b) ++ "\nin\n" ++
          Expr.prettyAux (x :: ctx) 0 e)
  | .letScheme s b e =>
      let x := prettyTermVarName ctx.length
      prettyParenIf (prec ≥ 1)
        ("let " ++ x ++ " : " ++ s.pretty ++ " =\n" ++
          prettyIndentBlock (Expr.prettyAux ctx 0 b) ++ "\nin\n" ++
          Expr.prettyAux (x :: ctx) 0 e)
  | .matchBL s n c =>
      let h := prettyTermVarName ctx.length
      let t := prettyTermVarName (ctx.length + 1)
      prettyParenIf (prec ≥ 1)
        ("match " ++ Expr.prettyAux ctx 0 s ++ " with" ++
          " | [] => " ++ Expr.prettyAux ctx 0 n ++
          " | " ++ h ++ " :: " ++ t ++ " => " ++
            Expr.prettyAux (h :: t :: ctx) 0 c)
  | .matchNil s n =>
      prettyParenIf (prec ≥ 1)
        ("match " ++ Expr.prettyAux ctx 0 s ++ " with" ++
          " | [] => " ++ Expr.prettyAux ctx 0 n)
  | .matchCons s c =>
      let h := prettyTermVarName ctx.length
      let t := prettyTermVarName (ctx.length + 1)
      prettyParenIf (prec ≥ 1)
        ("match " ++ Expr.prettyAux ctx 0 s ++ " with" ++
          " | " ++ h ++ " :: " ++ t ++ " => " ++
          Expr.prettyAux (h :: t :: ctx) 0 c)

end

def Expr.pretty (e : Expr) (ctx : List String := []) (prec : Nat := 0) : String :=
  Expr.prettyAux ctx prec e

/-- Forms whose top constructor should be parenthesized in an `e : τ` judgement
(so the judgement colon is not read as part of the expression). -/
def Expr.needsJudgementParens : Expr → Bool
  | .anno .. | .matchBL .. | .matchNil .. | .matchCons ..
  | .if_ .. | .let_ .. | .letScheme .. => true
  | _ => false

/-- Pretty for `e : τ` / check judgements: wraps anno/match/if/let only. -/
def Expr.prettyJudgement (e : Expr) (ctx : List String := []) : String :=
  prettyParenIf e.needsJudgementParens (Expr.prettyAux ctx 0 e)

instance : ToString Expr := ⟨fun e => Expr.pretty e⟩

/-- Pretty a *top-level* `BL` with ground bounds folded (`BL (0+1) (0+1)  ↦  BL 1 1`).
Does not fold when `BL` is nested inside arrows (or other structure) — that obscures
the surrounding judgement (e.g. subtype comparisons). -/
def Ty.prettyFolded (t : Ty) : String :=
  match t with
  | .bl lo hi =>
      if hlo : lo.Ground then
        if hhi : hi.Ground then
          let t' : Ty := .bl (.lit (lo.fold hlo)) (.lit (hi.fold hhi))
          if t' = t then t.pretty else t.pretty ++ "  ↦  " ++ t'.pretty
        else t.pretty
      else t.pretty
  | _ => t.pretty

/-- Print an assignment on a fixed list of vars (full `Assign` is a function). -/
def Assign.prettyOn (σ : Assign) (vs : List Var) : String :=
  "{" ++ String.intercalate ", " (vs.map fun v =>
    match v.kind with
    | .rigid => prettyCountVarLetter v.idx ++ "↦" ++ toString (σ v)
    | .inferable => "?" ++ prettyCountVarLetter v.idx ++ "↦" ++ toString (σ v)) ++ "}"

end BLSketch
