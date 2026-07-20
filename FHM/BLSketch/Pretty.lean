import FHM.BLSketch

/-!
# Pretty-printers for `BLSketch`

Readable `String` renderings of counts, types, expressions, and constraint
problems — same spirit as `FHM/Pretty.lean`. Debugging / demo IO only; no
proofs depend on these.

Conventions:
* Rigid count vars print as `r0`, `r1`, …; inferables as `?i0`, `?i1`, ….
* Term de Bruijn indices resolve against a binder name context (`x`, `y`, …);
  dangling indices print as `#n`.
* Scheme rigid binders print as `∀ r0 … rn-1. body` (separate from term names).
* Annotation holes print as `_`.
* Lists: a proper `nil`/`cons` spine prints as `[a, b, c]`; improper as `h :: t`.
-/

namespace BLSketch

@[inline] def prettyParenIf (b : Bool) (s : String) : String :=
  if b then "(" ++ s ++ ")" else s

def prettyTermVarName (n : Nat) : String :=
  let letters := ["x", "y", "z", "u", "v", "w", "p", "q", "r", "s", "t"]
  letters.getD n ("v" ++ toString n)

/-! ## Counts -/

/-- Precedence: `0` top, `1` add/min/max, `2` mul, `3` pred/atomic. -/
def Count.prettyAux (prec : Nat) : Count → String
  | .lit n => toString n
  | .var ⟨.rigid, i⟩ => "r" ++ toString i
  | .var ⟨.inferable, i⟩ => "?i" ++ toString i
  | .add a b =>
      prettyParenIf (prec > 1)
        (Count.prettyAux 1 a ++ " + " ++ Count.prettyAux 1 b)
  | .mul a b =>
      prettyParenIf (prec > 2)
        (Count.prettyAux 2 a ++ " * " ++ Count.prettyAux 2 b)
  | .min a b =>
      prettyParenIf (prec > 1)
        ("min(" ++ Count.prettyAux 0 a ++ ", " ++ Count.prettyAux 0 b ++ ")")
  | .max a b =>
      prettyParenIf (prec > 1)
        ("max(" ++ Count.prettyAux 0 a ++ ", " ++ Count.prettyAux 0 b ++ ")")
  | .pred a =>
      prettyParenIf (prec > 3) ("pred(" ++ Count.prettyAux 0 a ++ ")")

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
      String.intercalate " " ((List.range s.binders).map fun i => "r" ++ toString i)
    "∀ " ++ binders ++ ". " ++ s.body.pretty

instance : ToString BScheme := ⟨BScheme.pretty⟩

def Binding.pretty : Binding → String
  | .mono ty => ty.pretty
  | .scheme s => s.pretty

instance : ToString Binding := ⟨Binding.pretty⟩

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
      | .rigid => "r" ++ toString v.idx
      | .inferable => "?i" ++ toString v.idx)
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
      else name ++ "[" ++ String.intercalate ", " (args.map Count.pretty) ++ "]"
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
        ("let " ++ x ++ " = " ++ Expr.prettyAux ctx 0 b ++ " in " ++
          Expr.prettyAux (x :: ctx) 0 e)
  | .letScheme s b e =>
      let x := prettyTermVarName ctx.length
      prettyParenIf (prec ≥ 1)
        ("letScheme " ++ x ++ " : " ++ s.pretty ++ " = " ++
          Expr.prettyAux ctx 0 b ++ " in " ++ Expr.prettyAux (x :: ctx) 0 e)
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
        ("matchNil " ++ Expr.prettyAux ctx 0 s ++ " => " ++
          Expr.prettyAux ctx 0 n)
  | .matchCons s c =>
      let h := prettyTermVarName ctx.length
      let t := prettyTermVarName (ctx.length + 1)
      prettyParenIf (prec ≥ 1)
        ("matchCons " ++ Expr.prettyAux ctx 0 s ++ " | " ++
          h ++ " :: " ++ t ++ " => " ++
          Expr.prettyAux (h :: t :: ctx) 0 c)

end

def Expr.pretty (e : Expr) (ctx : List String := []) : String :=
  Expr.prettyAux ctx 0 e

instance : ToString Expr := ⟨fun e => Expr.pretty e⟩

/-- Print an assignment on a fixed list of vars (full `Assign` is a function). -/
def Assign.prettyOn (σ : Assign) (vs : List Var) : String :=
  "{" ++ String.intercalate ", " (vs.map fun v =>
    match v.kind with
    | .rigid => "r" ++ toString v.idx ++ "↦" ++ toString (σ v)
    | .inferable => "?i" ++ toString v.idx ++ "↦" ++ toString (σ v)) ++ "}"

end BLSketch
