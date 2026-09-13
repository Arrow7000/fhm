import FHM.Bounds.TypeSubstitution

namespace FHM.Bounds.TypeSubstitutionTests

open TypeSubstitution

private def n : Count := .var ⟨.rigid, 7⟩
private def capture : Count := .var ⟨.rigid, 99⟩
private def caller : BoundsTy := .list n capture (.prim .char)
private def args : Nat → BoundsTy := fun _ => caller
private def rows : CountSubstitution.Bindings := [(7, .lit 3)]

-- The free HM identity is a capture even if it numerically equals a slot.
example : substitute args (.fvar 0) = .fvar 0 := rfl

-- Replacements are simultaneous, not recursively specialized themselves.
example : substitute (fun i => if i = 0 then .bvar 1 else .prim .int) (.bvar 0) = .bvar 1 := rfl

-- Scheme count substitution must not rewrite counts inside caller arguments.
example : combined rows args (.bvar 0) = caller := rfl

-- The opposite order really has different meaning when identities overlap.
example : CountSubstitution.bounds rows (substitute args (.bvar 0)) =
    .list (.lit 3) capture (.prim .char) := rfl

private def wider : BoundsTy := .list (.lit 0) (.lit 5) (.bvar 0)
private def narrower : BoundsTy := .list (.lit 2) (.lit 2) (.bvar 0)

private theorem inclusion : SemanticSub [] narrower wider := by
  apply SemanticSub.list
  · simp [ForallProblem.Valid, Interval.subGoals, Constraint.Holds, Count.eval, ExtNat.le]
  · exact .bvar

example : SemanticSub [] (substitute args narrower) (substitute args wider) :=
  subtype args inclusion

-- Domain contravariance survives replacement by arbitrary structured bounds.
example : SemanticSub [] (substitute args (.arrow wider (.bvar 0)))
    (substitute args (.arrow narrower (.bvar 0))) :=
  subtype args (.arrow inclusion .bvar)

private def template : BoundsTy := .arrow (.fvar 65) (.list n n (.bvar 0))
private def hmScheme : PolyTy := ⟨1, Synth.BoundsTy.toTy template⟩
private def found : Ty := .arrow (.fvar 65) (listTy (Synth.BoundsTy.toTy caller))

private theorem hmWitness : hmScheme.InstantiatesTo [Synth.BoundsTy.toTy caller] found := by
  simp only [PolyTy.InstantiatesTo, hmScheme, template, found, Synth.BoundsTy.toTy, listTy]
  exact .arrow .fvar (.customTy (.cons (.bvar rfl) .nil))

-- Bounds specialization agrees exactly with an authoritative HM instance,
-- retaining fvar65 while specializing slot0 and the scheme's count binder.
example : Synth.BoundsTy.toTy (combined rows args template) = found := by
  apply found_shape rows args (σ := hmScheme) (tyArgs := [Synth.BoundsTy.toTy caller])
  · rfl
  · exact hmWitness
  · intro i t hi
    cases i with
    | zero => simp only [List.getElem?_cons_zero] at hi; cases hi; rfl
    | succ i => simp at hi

private def countAndTypeSeparated : Bool :=
  match substitute (fun _ => .prim .int) (.list n n (.bvar 7)) with
  | .list lo hi (.prim .int) => lo == n && hi == n
  | _ => false

private def capturedHM : Bool :=
  match substitute args (.arrow (.fvar 0) (.bvar 0)) with
  | .arrow (.fvar 0) (.list lo hi (.prim .char)) => lo == n && hi == capture
  | _ => false

private def cases : List (String × Bool) := [
  ("bound slot replaced by full caller bounds", (substitute args (.bvar 0)).pretty == "BL t n99 Char"),
  ("free HM identity retained rather than indexed", capturedHM),
  ("count and HM bound-slot namespaces are separate", countAndTypeSeparated),
  ("counts in caller replacement are not scheme binders", (combined rows args (.bvar 0)).pretty == "BL t n99 Char"),
  ("scheme counts replaced before inserting caller bounds", (combined rows args
    (.list n n (.bvar 0))).pretty == "BL 3 3 (BL t n99 Char)"),
  ("wrong substitution order changes the result", (CountSubstitution.bounds rows
    (substitute args (.bvar 0))).pretty == "BL 3 n99 Char"),
  ("nested data arguments specialized", (substitute args (.custom ⟨"Box"⟩ [.bvar 0])).pretty ==
    "Box (BL t n99 Char)"),
  ("arrow slots specialized", (substitute (fun _ => .prim .int)
    (.arrow (.bvar 0) (.bvar 0))).pretty == "Int → Int"),
  ("unrelated free HM identity retained", match substitute args (.fvar 65) with
    | .fvar 65 => true | _ => false),
  ("replacement is simultaneous", match substitute
      (fun i => if i = 0 then .bvar 1 else .prim .int) (.bvar 0) with
    | .bvar 1 => true | _ => false)]

def main : IO Unit := do
  for (name, ok) in cases do
    IO.println s!"{if ok then "PASS" else "FAIL"}: {name}"
    unless ok do throw (IO.userError s!"HM bounds specialization regression: {name}")

#eval main

end FHM.Bounds.TypeSubstitutionTests
