import FHM.Bounds.ScopedAnnotation

namespace FHM.Bounds.ScopedAnnotationTests

open Scope ScopedScheme ScopedAnnotation

private def n : Count := .var ⟨.rigid, 7⟩
private def capture : Count := .var ⟨.rigid, 99⟩
private def exact (c : Count) : Ty := .bl (.solid c) (.solid c) (.prim .int)

private def accepted (ids : List Nat) (τ : Ty) : Bool :=
  match decode ids τ with
  | .ok _ => true
  | .error _ => false

private def hasBounds (ids : List Nat) (τ : Ty) (expected : String) : Bool :=
  match decode ids τ with
  | .ok ann => ann.bounds.pretty == expected
  | .error _ => false

private def declared (qs caps : List Nat) (prem : List Constraint) (τ : Ty) : Bool :=
  match contract qs caps prem τ with
  | .ok _ => true
  | .error _ => false

private def countAndTypeNamespaces : Bool :=
  match decode [7] (.bl (.solid n) (.solid n) (.fvar 7)) with
  | .ok ann => match ann.bounds with
      | .list _ _ (.fvar 7) => true
      | _ => false
  | .error _ => false

private def instantiatedDeclaration : Bool :=
  match contract [7] [99] [] (.arrow (exact n) (exact capture)) with
  | .error _ => false
  | .ok c => match c.scheme.instantiate [.lit 3] [99] with
      | .ok inst => inst.bounds.pretty == "BL 3 3 Int → BL n99 n99 Int"
      | .error _ => false

example {ids τ} (ann : Decoded ids τ) :
    Synth.BoundsTy.toTy ann.bounds = τ.eraseBounds := ann.shape

example {qs caps prem τ} (c : Contract qs caps prem τ) :
    c.scheme.WF := c.wf

private def cases : List (String × Bool) := [
  ("scoped symbolic arrow demand", hasBounds [7, 99] (.arrow (exact n) (exact capture))
    "BL t t Int → BL n99 n99 Int"),
  ("bare List gives top interval", hasBounds [] (bareListTy (.prim .int)) "BL 0 ∞ Int"),
  ("bounds nested inside bare List are retained", hasBounds [7] (bareListTy (exact n))
    "BL 0 ∞ (BL t t Int)"),
  ("bounds nested inside data arguments are retained", hasBounds [7]
    (.customTy ⟨"Box"⟩ [exact n]) "Box (BL t t Int)"),
  ("literal infinity endpoint is legal", accepted [7] (.bl (.solid n) (.solid .inf) (.prim .int))),
  ("missing lower identity rejected", !accepted [] (exact n)),
  ("missing upper identity rejected", !accepted [7] (.bl (.solid n) (.solid capture) (.prim .int))),
  ("missing identity nested in arrow rejected", !accepted [] (.arrow (.prim .int) (exact n))),
  ("missing identity nested in data argument rejected", !accepted [] (.customTy ⟨"Box"⟩ [exact n])),
  ("inferable count is not a lexical binder", !accepted [7] (exact (.var ⟨.inferable, 7⟩))),
  ("holes explicitly rejected", !accepted [] (.bl .hole (.solid .inf) (.prim .int))),
  ("malformed zero-argument List rejected", !accepted [] (.customTy _root_.listTyName [])),
  ("malformed two-argument List rejected", !accepted []
    (.customTy _root_.listTyName [.prim .int, .prim .char])),
  ("type fvars are not count identities", countAndTypeNamespaces),
  ("decoded declaration instantiates own count but not capture", instantiatedDeclaration),
  ("declaration quantifiers must be unique even without counts", !declared [7, 7] [] [] (.prim .int)),
  ("declaration capture must not be quantified", !declared [7] [7] [] (exact n)),
  ("declaration premises must be scoped", !declared [7] [] [⟨n, capture⟩] (exact n))]

def main : IO Unit := do
  for (name, ok) in cases do
    IO.println s!"{if ok then "PASS" else "FAIL"}: {name}"
    unless ok do throw (IO.userError s!"scoped annotation regression: {name}")

#eval main

end FHM.Bounds.ScopedAnnotationTests
