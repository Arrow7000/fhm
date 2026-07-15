import FHM.Core
import FHM.SurfaceLang

/-! # Pretty-printers for the Core language

Readable `String` renderings of `Ty`, `PolyTy`, and `Expr`, ending the
`[1, .arrow (.fvar 0) (.fvar 0)]` `Repr` misery. These are debugging/IO helpers
only — no proofs depend on them. They are defined in the root `Ty.`/`PolyTy.`/
`Expr.` namespaces so that dot-notation (`t.pretty`) and the `ToString`
instances both resolve.

Conventions:
* Type bound vars (`bvar`) print as `a, b, c, …`; free/unification vars (`fvar`)
  as `?a, ?b, …`. A `PolyTy` binds its params with a leading `∀`.
* Term vars use de Bruijn indices resolved against the binder context to names
  `x, y, z, …` (a binder at depth `d` is named by `prettyTermVarName d`); a
  dangling index prints as `#n`.
* Application is left-associative, `→` is right-associative, and parentheses are
  inserted only where precedence requires them.
-/

/-- Pick a short, stable name for the `n`-th term binder (by depth). -/
def prettyTermVarName (n : Nat) : String :=
  let letters := ["x", "y", "z", "u", "v", "w", "p", "q", "r", "s", "t"]
  letters.getD n ("v" ++ toString n)

/-- Pick a short, stable name for the `n`-th type variable. -/
def prettyTyVarName (n : Nat) : String :=
  let letters := ["a", "b", "c", "d", "e", "f", "g", "h", "i", "j", "k"]
  letters.getD n ("t" ++ toString n)

def prettyPrimTy : PrimTy → String
  | .unit => "Unit"
  | .int  => "Int"
  | .nat  => "Nat"
  | .char => "Char"

def prettyPrimLit : PrimLitExpr → String
  | .unit  => "()"
  | .int n => toString n
  | .nat n => toString n
  | .char c => "'" ++ String.singleton c ++ "'"

@[inline] def prettyParenIf (b : Bool) (s : String) : String := if b then "(" ++ s ++ ")" else s

/-! ## Types -/

mutual

/-- `prec` controls parenthesization: `0` = top, `1` = left of an arrow (wrap
    arrows, since `→` is right-associative), `2` = constructor-argument position
    (wrap arrows *and* applied `customTy`s, since application binds tightest). -/
def Ty.prettyAux (prec : Nat) : Ty → String
  | .prim p        => prettyPrimTy p
  | .bvar n        => prettyTyVarName n
  | .fvar n        => "?" ++ prettyTyVarName n
  | .arrow a b     => prettyParenIf (prec ≥ 1) (Ty.prettyAux 1 a ++ " → " ++ Ty.prettyAux 0 b)
  | .customTy (.mk s) []   => s
  | .customTy (.mk s) args => prettyParenIf (prec ≥ 2) (s ++ " " ++ String.intercalate " " (Ty.prettyArgs args))

/-- Each argument is printed in atomic (parenthesized-if-compound) position. -/
def Ty.prettyArgs : List Ty → List String
  | []      => []
  | t :: ts => Ty.prettyAux 2 t :: Ty.prettyArgs ts

end

def Ty.pretty (t : Ty) : String := Ty.prettyAux 0 t

/-- `∀ a b. body`, or just `body` when there are no params. -/
def PolyTy.pretty (σ : PolyTy) : String :=
  if σ.paramCount = 0 then σ.body.pretty
  else "∀ " ++ String.intercalate " " ((List.range σ.paramCount).map prettyTyVarName)
        ++ ". " ++ σ.body.pretty

instance : ToString Ty := ⟨Ty.pretty⟩
instance : ToString PolyTy := ⟨PolyTy.pretty⟩

/-! ## Expressions

`prec` controls parenthesization: `0` = top, `1` = function position of an
application (wrap lambdas/lets/matches) *or* left of `::`, `2` = argument/atomic
position (wrap applications and `::` too).

List/pair sugar (matching Surface): a proper `Nil`/`Cons` spine prints as
`[a, b, c]`; an improper `Cons` prints as `h :: t`; `Pair a b` prints as
`(a, b)`. Uses the same ctor name strings as `SurfaceBridge` (`"Nil"`/`"Cons"`/
`"Pair"`). -/

def MatchPattern.pretty (names : List String) : MatchPattern → String
  | .named (.mk c) 0 => c
  | .named (.mk c) _ => c ++ " " ++ String.intercalate " " names
  | .wildcard        => "_"

mutual

def Expr.prettyAux (ctx : List String) (prec : Nat) : Expr → String
  | .primLit p => prettyPrimLit p
  | .primBinOp .intAdd => "intAdd"
  | .primBinOp .intSub => "intSub"
  | .primBinOp .intLt => "intLt"
  | .primBinOp .charLt => "charLt"
  | .var n _   => (ctx[n]?).getD ("#" ++ toString n)
  | .ctor (.mk "Nil") => "[]"
  | .ctor (.mk s) => s
  | .app (.app (.ctor (.mk "Pair")) a) b =>
      "(" ++ Expr.prettyAux ctx 0 a ++ ", " ++ Expr.prettyAux ctx 0 b ++ ")"
  | .app (.app (.ctor (.mk "Cons")) h) t =>
      match Expr.prettyListElems ctx t with
      | some ts =>
          "[" ++ String.intercalate ", " (Expr.prettyAux ctx 0 h :: ts) ++ "]"
      | none =>
          prettyParenIf (prec ≥ 1)
            (Expr.prettyAux ctx 2 h ++ " :: " ++ Expr.prettyAux ctx 0 t)
  | .app f x =>
      prettyParenIf (prec ≥ 2)
        (Expr.prettyAux ctx 1 f ++ " " ++ Expr.prettyAux ctx 2 x)
  | .lambda ann body =>
      let name := prettyTermVarName ctx.length
      let annStr := match ann with | none => "" | some t => " : " ++ t.pretty
      prettyParenIf (prec ≥ 1) ("λ" ++ name ++ annStr ++ ". " ++ Expr.prettyAux (name :: ctx) 0 body)
  | .letIn ann be body =>
      let name := prettyTermVarName ctx.length
      let annStr := match ann with | none => "" | some σ => " : " ++ σ.pretty
      prettyParenIf (prec ≥ 1) ("let " ++ name ++ annStr ++ " = " ++ Expr.prettyAux ctx 0 be
        ++ " in " ++ Expr.prettyAux (name :: ctx) 0 body)
  | .match_ scrut branches =>
      prettyParenIf (prec ≥ 1) ("match " ++ Expr.prettyAux ctx 0 scrut ++ " with"
        ++ Expr.prettyBranches ctx branches)
  | .letRec anns bindings body =>
      -- The `n = bindings.length` group binders are in scope (de Bruijn `0..n-1`)
      -- in every binding *and* the body, named by depth like the other cases.
      -- Annotated members print their declared (load-bearing) recursion scheme
      -- inline: `let rec (f : σ) = e and g = e' in body`.
      let names := (List.range bindings.length).map (fun j => prettyTermVarName (ctx.length + j))
      let ctx' := names ++ ctx
      prettyParenIf (prec ≥ 1) ("let rec " ++ Expr.prettyRecGroup ctx' names anns bindings
        ++ " in " ++ Expr.prettyAux ctx' 0 body)

/-- If `e` is a proper `Nil`/`Cons` spine, return pretty-printed elements; else `none`. -/
def Expr.prettyListElems (ctx : List String) : Expr → Option (List String)
  | .ctor (.mk "Nil") => some []
  | .app (.app (.ctor (.mk "Cons")) h) t =>
      match Expr.prettyListElems ctx t with
      | some ts => some (Expr.prettyAux ctx 0 h :: ts)
      | none => none
  | _ => none

def Expr.prettyBranches (ctx : List String) : List (MatchPattern × Expr) → String
  | [] => ""
  | (pat, body) :: rest =>
      let names := (List.range pat.bindCount).map (fun j => prettyTermVarName (ctx.length + j))
      " | " ++ pat.pretty names ++ " => " ++ Expr.prettyAux (names ++ ctx) 0 body
        ++ Expr.prettyBranches ctx rest

/-- Render a `letRec` group `x₀ = e₀ and (x₁ : σ₁) = e₁ and …`, each binding
    printed in the (already group-extended) context `ctx'`; annotated members
    show their declared scheme. -/
def Expr.prettyRecGroup (ctx' : List String) (names : List String)
    (anns : List (Option PolyTy)) : List Expr → String
  | [] => ""
  | e :: rest =>
      (match anns.headD none with
        | none => names.headD "?"
        | some σ => "(" ++ names.headD "?" ++ " : " ++ σ.pretty ++ ")")
        ++ " = " ++ Expr.prettyAux ctx' 0 e
        ++ (match rest with | [] => "" | _ :: _ => " and ")
        ++ Expr.prettyRecGroup ctx' names.tail anns.tail rest

end

def Expr.pretty (e : Expr) : String := Expr.prettyAux [] 0 e

instance : ToString Expr := ⟨Expr.pretty⟩

/-! ## Smoke tests -/

section Examples

-- `∀ a. a → a`
#eval toString (⟨1, .arrow (.bvar 0) (.bvar 0)⟩ : PolyTy)
-- `?a → ?a`
#eval toString (Ty.arrow (.fvar 0) (.fvar 0))
-- `List (?a → Int)`
#eval toString (Ty.customTy (.mk "List") [.arrow (.fvar 0) (.prim .int)])
-- `(Int → Int) → Int`
#eval toString (Ty.arrow (.arrow (.prim .int) (.prim .int)) (.prim .int))

-- `λx. x`
#eval toString (Expr.lambda none (.var 0 []))
-- `λx. λy. x`
#eval toString (Expr.lambda none (.lambda none (.var 1 [])))
-- `(λx. x) 5`
#eval toString (Expr.app (.lambda none (.var 0 [])) (.primLit (.int 5)))
-- `let x : ∀ a. a → a = λy. y in x x`
#eval toString (Expr.letIn (some ⟨1, .arrow (.bvar 0) (.bvar 0)⟩)
  (.lambda none (.var 0 [])) (.app (.var 0 []) (.var 0 [])))
-- `λx. match x with | Cons y z => y | Nil => x | _ => x`
#eval toString (Expr.lambda none (.match_ (.var 0 [])
  [(.named (.mk "Cons") 2, .var 1 []), (.named (.mk "Nil") 0, .var 0 []), (.wildcard, .var 0 [])]))

-- List/pair sugar: `[1, 2]`, `1 :: x`, `(1, 2)`
#guard toString (Expr.app (.app (.ctor (.mk "Cons")) (.primLit (.int 1)))
  (.app (.app (.ctor (.mk "Cons")) (.primLit (.int 2))) (.ctor (.mk "Nil")))) = "[1, 2]"
#guard toString (Expr.ctor (.mk "Nil")) = "[]"
#guard toString (Expr.app (.app (.ctor (.mk "Cons")) (.primLit (.int 1))) (.var 0 [])) = "1 :: #0"
#guard toString (Expr.app (.app (.ctor (.mk "Pair")) (.primLit (.int 1))) (.primLit (.int 2))) = "(1, 2)"

end Examples

/-! # Pretty-printers for the Surface language

The surface language uses *named* binders (`ValName`), so printing needs no de
Bruijn context — values, patterns, and types render directly. -/

def prettyValName : ValName → String
  | .mk s => s

def Surface.prettyPrimTy : Surface.PrimTy → String
  | .unit => "Unit"
  | .int  => "Int"
  | .nat  => "Nat"
  | .bool => "Bool"
  | .char => "Char"

def Surface.prettyPrimLit : Surface.PrimLitExpr → String
  | .unit   => "()"
  | .int n  => toString n
  | .nat n  => toString n
  | .bool b => toString b
  | .char c => "'" ++ toString c ++ "'"

/-! ## Surface types -/

mutual

def Surface.Ty.prettyAux (prec : Nat) : Surface.Ty → String
  | .prim p        => Surface.prettyPrimTy p
  | .tvar v        => prettyValName v
  | .pair a b      => "(" ++ Surface.Ty.prettyAux 0 a ++ ", " ++ Surface.Ty.prettyAux 0 b ++ ")"
  | .arrow a b     => prettyParenIf (prec ≥ 1) (Surface.Ty.prettyAux 1 a ++ " → " ++ Surface.Ty.prettyAux 0 b)
  | .customTy (.mk s) []   => s
  | .customTy (.mk s) args => prettyParenIf (prec ≥ 2) (s ++ " " ++ String.intercalate " " (Surface.Ty.prettyArgs args))

def Surface.Ty.prettyArgs : List Surface.Ty → List String
  | []      => []
  | t :: ts => Surface.Ty.prettyAux 2 t :: Surface.Ty.prettyArgs ts

end

def Surface.Ty.pretty (t : Surface.Ty) : String := Surface.Ty.prettyAux 0 t

def Surface.PolyTy.pretty (σ : Surface.PolyTy) : String :=
  match σ.foralls with
  | [] => σ.body.pretty
  | fs => "∀ " ++ String.intercalate " " (fs.map prettyValName) ++ ". " ++ σ.body.pretty

instance : ToString Surface.Ty := ⟨Surface.Ty.pretty⟩
instance : ToString Surface.PolyTy := ⟨Surface.PolyTy.pretty⟩

/-! ## Surface patterns -/

mutual

/-- `prec`: `0` = top, `1` = left of `::` (wrap nested `::`), `2` =
    constructor-argument position (wrap `::` and applied constructors). -/
def Surface.Pattern.pretty (prec : Nat) : Surface.Pattern → String
  | .name v          => prettyValName v
  | .wildcard        => "_"
  | .pair a b        => "(" ++ Surface.Pattern.pretty 0 a ++ ", " ++ Surface.Pattern.pretty 0 b ++ ")"
  | .cons h t        => prettyParenIf (prec ≥ 1) (Surface.Pattern.pretty 1 h ++ " :: " ++ Surface.Pattern.pretty 0 t)
  | .list items      => "[" ++ String.intercalate ", " (Surface.Pattern.prettyList items) ++ "]"
  | .ctor (.mk c) [] => c
  | .ctor (.mk c) ps => prettyParenIf (prec ≥ 2) (c ++ " " ++ String.intercalate " " (Surface.Pattern.prettyArgs ps))

def Surface.Pattern.prettyArgs : List Surface.Pattern → List String
  | []      => []
  | p :: ps => Surface.Pattern.pretty 2 p :: Surface.Pattern.prettyArgs ps

def Surface.Pattern.prettyList : List Surface.Pattern → List String
  | []      => []
  | p :: ps => Surface.Pattern.pretty 0 p :: Surface.Pattern.prettyList ps

end

instance : ToString Surface.Pattern := ⟨Surface.Pattern.pretty 0⟩

/-! ## Surface expressions -/

mutual

def Surface.Expr.prettyAux (prec : Nat) : Surface.Expr → String
  | .primLit p => Surface.prettyPrimLit p
  | .primBinOp .intAdd => "intAdd"
  | .primBinOp .intSub => "intSub"
  | .primBinOp .intLt => "intLt"
  | .primBinOp .charLt => "charLt"
  | .var v     => prettyValName v
  | .ctor (.mk s) => s
  | .pair a b  => "(" ++ Surface.Expr.prettyAux 0 a ++ ", " ++ Surface.Expr.prettyAux 0 b ++ ")"
  | .cons h t  => prettyParenIf (prec ≥ 1) (Surface.Expr.prettyAux 2 h ++ " :: " ++ Surface.Expr.prettyAux 0 t)
  | .list items => "[" ++ String.intercalate ", " (Surface.Expr.prettyList items) ++ "]"
  | .app f x   => prettyParenIf (prec ≥ 2) (Surface.Expr.prettyAux 1 f ++ " " ++ Surface.Expr.prettyAux 2 x)
  | .lambda param ann body =>
      let annStr := match ann with | none => "" | some t => " : " ++ t.pretty
      prettyParenIf (prec ≥ 1) ("\\" ++ Surface.Pattern.pretty 2 param ++ annStr ++ " -> "
        ++ Surface.Expr.prettyAux 0 body)
  | .letIn v ann be body =>
      let annStr := match ann with | none => "" | some σ => " : " ++ σ.pretty
      prettyParenIf (prec ≥ 1) ("let " ++ prettyValName v ++ annStr ++ " = " ++ Surface.Expr.prettyAux 0 be
        ++ " in " ++ Surface.Expr.prettyAux 0 body)
  | .letRecIn bindingsAnns body =>
      prettyParenIf (prec ≥ 1) ("let rec " ++ Surface.Expr.prettyRecGroup bindingsAnns
        ++ " in " ++ Surface.Expr.prettyAux 0 body)
  | .ife c t f =>
      prettyParenIf (prec ≥ 1) ("if " ++ Surface.Expr.prettyAux 0 c ++ " then " ++ Surface.Expr.prettyAux 0 t
        ++ " else " ++ Surface.Expr.prettyAux 0 f)
  | .match_ scrut branches =>
      prettyParenIf (prec ≥ 1) ("match " ++ Surface.Expr.prettyAux 0 scrut ++ " with"
        ++ Surface.Expr.prettyBranches branches)

def Surface.Expr.prettyList : List Surface.Expr → List String
  | []      => []
  | e :: es => Surface.Expr.prettyAux 0 e :: Surface.Expr.prettyList es

def Surface.Expr.prettyBranches : List (Surface.Pattern × Surface.Expr) → String
  | [] => ""
  | (pat, body) :: rest =>
      " | " ++ Surface.Pattern.pretty 0 pat ++ " => " ++ Surface.Expr.prettyAux 0 body
        ++ Surface.Expr.prettyBranches rest

/-- Render a surface `letRecIn` group `x₀ = e₀ and (x₁ : σ₁) = e₁ and …`,
    each binding printed with its optional scheme annotation. Mirrors
    `prettyList`/`prettyBranches`' single-list-arg recursion shape. -/
def Surface.Expr.prettyRecGroup : List (ValName × Option Surface.PolyTy × Surface.Expr) → String
  | [] => ""
  | (v, ann, e) :: rest =>
      (match ann with
        | none => prettyValName v
        | some σ => "(" ++ prettyValName v ++ " : " ++ σ.pretty ++ ")")
        ++ " = " ++ Surface.Expr.prettyAux 0 e
        ++ (match rest with | [] => "" | _ :: _ => " and ")
        ++ Surface.Expr.prettyRecGroup rest

end

def Surface.Expr.pretty (e : Surface.Expr) : String := Surface.Expr.prettyAux 0 e

instance : ToString Surface.Expr := ⟨Surface.Expr.pretty⟩

/-! ## Surface smoke tests -/

section SurfaceExamples

-- `\(x, y) -> if x then [1, 2] else y :: ys`
#eval IO.println (Surface.Expr.lambda (.pair (.name (.mk "x")) (.name (.mk "y"))) none
  (.ife (.var (.mk "x"))
    (.list [.primLit (.int 1), .primLit (.int 2)])
    (.cons (.var (.mk "y")) (.var (.mk "ys")))))
-- `match xs with | Cons h t => h | [] => 0`
#eval IO.println (Surface.Expr.match_ (.var (.mk "xs"))
  [(.ctor (.mk "Cons") [.name (.mk "h"), .name (.mk "t")], .var (.mk "h")),
   (.list [], .primLit (.int 0))])
-- `match xs with | h :: t => h | [] => 0`
#eval IO.println (Surface.Expr.match_ (.var ⟨"xs"⟩)
  [(.cons (.name (.mk "h")) (.name (.mk "t")), .var (.mk "h")),
   (.list [], .primLit (.int 0))])
-- `∀ a. List a → a`
#eval IO.println (⟨[.mk "a"], .arrow (.customTy (.mk "List") [.tvar (.mk "a")]) (.tvar (.mk "a"))⟩ : Surface.PolyTy)

end SurfaceExamples
