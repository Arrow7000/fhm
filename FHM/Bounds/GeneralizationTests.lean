import FHM.Bounds.Generalization

namespace FHM.Bounds.GeneralizationTests

open Generalization

private def n : Count := .var ⟨.rigid, 7⟩
private def caller : BoundsTy := .list n n (.prim .char)
private def identity : Expr := .lambda none (.var 0)
private def identityBounds : BoundsTy := .arrow (.fvar 7) (.fvar 7)

private theorem identityDerives : Typed.Derives [] [] identity identityBounds :=
  .lambda True.intro (.var rfl)

-- The replacement is full bounds, including caller counts and nested shapes.
example : Typed.Derives [] [] identity (.arrow caller caller) := by
  exact universal (z := 7) identityDerives (by simp [identity, Expr.tyFreeVars])
    (by simp) caller

example : GeneralizedRHS [7] [] [] identity identityBounds := by
  apply generalize identityDerives
  · simp [identity, Expr.tyFreeVars]
  · simp

example (a : BinderBridge.Abstraction ⟨1, .arrow (.bvar 0) (.bvar 0)⟩
    identityBounds ([] ++ identity.tyFreeVars.map Ty.fvar)) :
    GeneralizedRHS a.ids [] [] identity identityBounds := fromBinder a identityDerives

-- A captured variable is not polymorphic just because its shape is a fvar.
example : ¬ Typed.Derives [] [.fvar 7] (.var 0) (.prim .int) := by
  intro h
  cases h with
  | var hv => simp at hv

-- A source annotation mentioning the identity blocks this generalization gate.
example : 7 ∈ (Expr.lambda (some (.fvar 7)) (.var 0)).tyFreeVars := by
  simp [Expr.tyFreeVars, Ty.freeVars]

-- Fresh carried demands stay fixed, including nested lists and arrows.
example {β} (h : Typed.annotation (.arrow (.fvar 99)
    (.bl (.solid (.lit 1)) (.solid (.lit 3)) (.fvar 99))) = .ok β) :
    replace 7 caller β = β := by
  apply annotation_fresh h
  simp [Ty.freeVars]

example : SemanticSub []
    (replace 7 caller (.arrow (.fvar 7) (.list n n (.fvar 7))))
    (replace 7 caller (.arrow (.fvar 7) (.list n n (.fvar 7)))) :=
  subtype 7 caller (SemanticSub.refl [] _)

-- Sequential rows are explicitly not simultaneous scheme-slot substitution.
example : replaceMany [(7, .fvar 8), (8, .prim .int)] (.fvar 7) = .prim .int := rfl
example : replace 7 (.fvar 7) (.fvar 7) = .fvar 7 := rfl
example : replace 7 caller (.bvar 7) = .bvar 7 := rfl
example : replace 7 caller (.list n n (.fvar 99)) = .list n n (.fvar 99) := rfl

private def cases : List (String × Bool) := [
  ("generalized identity receives full caller bounds", match replace 7 caller (.fvar 7) with
    | .list lo hi (.prim .char) => lo == n && hi == n | _ => false),
  ("unrelated captured HM identity remains fixed", match replace 7 caller (.fvar 99) with
    | .fvar 99 => true | _ => false),
  ("bound slots remain separate from free identities", match replace 7 caller (.bvar 7) with
    | .bvar 7 => true | _ => false),
  ("same numeric count identity remains untouched", match replace 7 caller (.list n n (.prim .int)) with
    | .list lo hi (.prim .int) => lo == n && hi == n | _ => false),
  ("structured replacement is inserted nonrecursively", match replace 7 (.fvar 7) (.fvar 7) with
    | .fvar 7 => true | _ => false),
  ("both sides of an arrow specialize", match replace 7 caller identityBounds with
    | .arrow (.list _ _ (.prim .char)) (.list _ _ (.prim .char)) => true | _ => false),
  ("nested custom arguments specialize", match replace 7 caller (.custom ⟨"Box"⟩ [.fvar 7]) with
    | .custom _ [.list _ _ (.prim .char)] => true | _ => false),
  ("sequential rows follow Core substitution convention", match
      replaceMany [(7, .fvar 8), (8, .prim .int)] (.fvar 7) with
    | .prim .int => true | _ => false),
  ("empty substitution leaves identity fixed", match replaceMany [] (.fvar 7) with
    | .fvar 7 => true | _ => false),
  ("unannotated RHS permits fresh generalization", !(identity.tyFreeVars.contains 7)),
  ("source annotation blocks generalization", (Expr.lambda (some (.fvar 7)) (.var 0)).tyFreeVars.contains 7),
  ("captured environment blocks generalization", (Synth.BoundsTy.toTy (.fvar 7)).freeVars.contains 7)]

def main : IO Unit := do
  for (name, ok) in cases do
    IO.println s!"{if ok then "PASS" else "FAIL"}: {name}"
    unless ok do throw (IO.userError s!"bounds generalization regression: {name}")

#eval main

end FHM.Bounds.GeneralizationTests
