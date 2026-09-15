import FHM.Bounds.ScopedHMAnnotation

namespace FHM.Bounds.ScopedHMAnnotationTests

open ScopedHMAnnotation ScopedHMInterpretation

private def n : Count := .var ⟨.rigid, 7⟩
private def callerType : BoundsTy := .list n n (.prim .int)
private def free (i : Nat) : BoundsTy := if i = 90 then .prim .char else .fvar i
private def slots : Nat → BoundsTy := vector [callerType]
private def source : Ty := .bl (.solid n) (.solid n) (.bvar 0)
private def rows : CountSubstitution.Bindings := [(7, .lit 3)]

private def decoded (τ : Ty := source) (caller : List Nat := [7])
    (substitution : CountSubstitution.Bindings := rows) : Except String BoundsTy := do
  pure (← decode free slots [7] substitution caller τ).bounds

private def exactCounts : Bool := match decoded with
  | .ok (.list lo hi (.list innerLo innerHi (.prim .int))) =>
      lo == .lit 3 && hi == .lit 3 && innerLo == n && innerHi == n
  | _ => false

private def checked (actual : BoundsTy) : Except String Unit := do
  let _ ← check free slots [7] rows [7] [] source actual
  pure ()

private def pinned (τ : Ty) (actual : BoundsTy) : Except String BoundsTy := do
  pure (← pin BoundsTy.fvar BoundsTy.bvar [] [] [] [] τ actual).demand

private def pinnedInterface : Bool :=
  match pin BoundsTy.fvar BoundsTy.bvar [] [] [] []
      (.bl .hole (.solid (.lit 5)) (.prim .int))
      (.list (.lit 2) (.lit 2) (.prim .int)) with
  | .ok result =>
      match result.demand with
      | .list lo hi (.prim .int) => lo == .lit 2 && hi == .lit 5
      | _ => false
  | .error _ => false

private def succeeds (r : Except String α) : Bool := match r with | .ok _ => true | _ => false
private def fails (r : Except String α) (needle : String) : Bool :=
  match r with | .error m => (m.splitOn needle).length > 1 | _ => false

example {free slots ids rows Δ τ actual}
    (h : AnnotationOK free slots ids rows Δ τ actual) (outer : Nat → BoundsTy) :
    AnnotationOK (fun i => SchemeSpecialization.mapFree outer (free i))
      (fun i => SchemeSpecialization.mapFree outer (slots i)) ids rows Δ τ
      (SchemeSpecialization.mapFree outer actual) := h.types outer

example {free slots ids rows Δ τ actual}
    (h : AnnotationOK free slots ids rows Δ τ actual)
    (outer : CountSubstitution.Bindings) (finite : CountSubstitution.Finite outer) :
    AnnotationOK (fun i => CountSubstitution.bounds outer (free i))
      (fun i => CountSubstitution.bounds outer (slots i)) ids (CountAlgebra.compose outer rows)
      (Δ.map (CountSubstitution.constraint outer)) τ (CountSubstitution.bounds outer actual) := h.counts outer finite

private def cases : List (String × Bool) := [
  ("lexical source counts specialize before full bound-slot types are inserted", exactCounts),
  ("named bound slot denotes its full caller bounds type", match decoded (.bvar 0) with
    | .ok (.list lo hi (.prim .int)) => lo == n && hi == n | _ => false),
  ("named free identities keep their separate interpretation", match decoded (.fvar 90) [] with
    | .ok (.prim .char) => true | _ => false),
  ("full bound-slot argument counts cannot escape caller scope", fails (decoded source []) "outside caller scope"),
  ("source lexical count scope cannot be repaired by substituting an undeclared count", fails
    (decoded (.bl (.solid (.var ⟨.rigid, 8⟩)) (.solid (.lit 3)) (.bvar 0)) [7] [(8, .lit 3)]) "scope"),
  ("lexical annotation replacement counts must be finite", fails (decoded source [7] [(7, .inf)]) "infinite Nat replacement"),
  ("actual bound-slot-aware annotation inclusion is independently checked", succeeds
    (checked (.list (.lit 3) (.lit 3) callerType))),
  ("a hole is pinned to its derived endpoint while a solid endpoint stays written",
    pinnedInterface),
  ("pinning cannot rescue a false solid endpoint", fails
    (pinned (.bl .hole (.solid (.lit 0)) (.prim .int))
      (.list (.lit 2) (.lit 2) (.prim .int))) "interval inclusion"),
  ("holes nested inside nominal arguments retain their exact origin", match pinned
    (.customTy ⟨"Box"⟩ [.bl .hole .hole (.prim .int)])
    (.custom ⟨"Box"⟩ [.list (.lit 3) (.lit 4) (.prim .int)]) with
      | .ok (.custom _ [.list lo hi _]) => lo == .lit 3 && hi == .lit 4
      | _ => false),
  ("lexical annotation cannot assert a false outer interval", fails
    (checked (.list (.lit 2) (.lit 2) callerType)) "interval inclusion"),
  ("lexical annotation cannot assert false bounds inside its supplied type argument", fails
    (checked (.list (.lit 3) (.lit 3) (.list (.lit 4) (.lit 4) (.prim .int)))) "interval inclusion"),
  ("unsupplied lexical slot is preserved, never replaced with Unit", match decoded (.bvar 1) [] with
    | .ok (.bvar 1) => true | _ => false)]

def main : IO Unit := do
  for (name, ok) in cases do
    IO.println s!"{if ok then "PASS" else "FAIL"}: {name}"
    unless ok do throw (IO.userError s!"lexical HM annotation regression failed: {name}")

#eval main

end FHM.Bounds.ScopedHMAnnotationTests
