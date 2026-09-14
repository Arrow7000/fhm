import FHM.Bounds.SchemeApplication

namespace FHM.Bounds.SchemeApplicationTests

open SchemeTyping

private def idScheme : Scheme :=
  ⟨⟨1, .arrow (.bvar 0) (.bvar 0)⟩, .arrow (.bvar 0) (.bvar 0),
    by
      change ContainsBvarsUpTo 1 (.arrow (.bvar 0) (.bvar 0))
      exact .arrow (.bvar (by omega)) (.bvar (by omega)),
    by simp [Synth.BoundsTy.toTy, Ty.eraseBounds]⟩

private def intCall (functionHM resultHM : Ty) :=
  SchemeApplication.check [] [.poly idScheme] 0 (.primLit (.int 1)) (.prim .int)
    .literal functionHM resultHM []

private def nilCall :=
  SchemeApplication.check [] [.poly idScheme] 0 (.ctor nilCtorName)
    (.list (.lit 0) (.lit 0) (.prim .char)) .nil
    (.arrow (listTy (.prim .char)) (listTy (.prim .char))) (listTy (.prim .char)) []

private def singleton : Expr := .app (.app (.ctor consCtorName) (.primLit (.char 'a'))) (.ctor nilCtorName)
private def singletonBounds : BoundsTy :=
  .list (.add (.lit 0) (.lit 1)) (.add (.lit 0) (.lit 1)) (.prim .char)
private theorem singletonTyping : Derives [] [.poly idScheme] singleton singletonBounds :=
  .cons .literal .nil .prim

private def singletonCall :=
  SchemeApplication.check [] [.poly idScheme] 0 singleton singletonBounds singletonTyping
    (.arrow (listTy (.prim .char)) (listTy (.prim .char))) (listTy (.prim .char)) []

private def n : Count := .var ⟨.rigid, 7⟩
private def captured : BoundsTy := .list n n (.prim .char)
private def capturedCall (scope : List Nat) :=
  SchemeApplication.check [] [.mono captured, .poly idScheme] 1 (.var 0) captured
    (.varMono rfl) (.arrow (listTy (.prim .char)) (listTy (.prim .char)))
    (listTy (.prim .char)) scope

private def structural : Scheme :=
  ⟨⟨1, .arrow (listTy (.bvar 0)) (listTy (.bvar 0))⟩,
    .arrow (.list (.lit 0) .inf (.bvar 0)) (.list (.lit 0) .inf (.bvar 0)),
    by
      change ContainsBvarsUpTo 1 (.arrow (listTy (.bvar 0)) (listTy (.bvar 0)))
      have h : ContainsBvarsUpTo 1 (listTy (.bvar 0)) := .customTy (by
        intro t ht
        simp only [List.mem_singleton] at ht
        subst t
        exact .bvar (by omega))
      exact .arrow h h,
    by simp [Synth.BoundsTy.toTy, Ty.eraseBounds, listTy, TyList.eraseBounds]⟩

private def succeeds (result : Except String α) : Bool :=
  match result with | .ok _ => true | .error _ => false
private def failsWith (result : Except String α) (needle : String) : Bool :=
  match result with | .ok _ => false | .error message => (message.splitOn needle).length > 1

example {Δ env i arg found scope} (r : SchemeApplication.Result Δ env i arg found scope) :
    Derives Δ env (.app (.var i) arg) r.bounds ∧
    Synth.BoundsTy.toTy r.bounds = found.eraseBounds ∧
    ScopedScheme.BoundsScoped scope r.bounds := ⟨r.derivation, r.shape, r.countScope⟩

private def cases : List (String × Bool) := [
  ("identity application at Int", succeeds (intCall (.arrow (.prim .int) (.prim .int)) (.prim .int))),
  ("identity application at Char", succeeds (SchemeApplication.check [] [.poly idScheme] 0
      (.primLit (.char 'a')) (.prim .char) .literal (.arrow (.prim .char) (.prim .char)) (.prim .char) [])),
  ("Nil origin stays exactly zero", match nilCall with
    | .ok r => match r.bounds with | .list (.lit 0) (.lit 0) (.prim .char) => true | _ => false
    | .error _ => false),
  ("Cons origin stays exactly one", match singletonCall with
    | .ok r => match r.bounds with
      | .list (.add (.lit 0) (.lit 1)) (.add (.lit 0) (.lit 1)) (.prim .char) => true
      | _ => false
    | .error _ => false),
  ("captured argument bounds stay symbolic", match capturedCall [7] with
    | .ok r => match r.bounds with | .list lo hi (.prim .char) => lo == n && hi == n | _ => false
    | .error _ => false),
  ("captured argument counts require caller scope", failsWith (capturedCall []) "counts"),
  ("wrong callee found payload rejected", failsWith
      (intCall (.arrow (.prim .char) (.prim .char)) (.prim .char)) "disagree"),
  ("wrong result found payload rejected", failsWith
      (intCall (.arrow (.prim .int) (.prim .int)) (.prim .char)) "result disagrees"),
  ("missing callee rejected", failsWith (SchemeApplication.check [] [] 0 (.primLit (.int 1))
      (.prim .int) .literal (.arrow (.prim .int) (.prim .int)) (.prim .int) []) "outside"),
  ("monomorphic callee not mistaken for scheme", failsWith (SchemeApplication.check []
      [.mono (.arrow (.prim .int) (.prim .int))] 0 (.primLit (.int 1)) (.prim .int) .literal
      (.arrow (.prim .int) (.prim .int)) (.prim .int) []) "polymorphic binding"),
  ("structural slot inference fails explicitly", failsWith (SchemeApplication.check [] [.poly structural]
      0 (.ctor nilCtorName) (.list (.lit 0) (.lit 0) (.prim .char)) .nil
      (.arrow (listTy (.prim .char)) (listTy (.prim .char))) (listTy (.prim .char)) []) "structural"),
  ("enclosing argument HM slot rejected", failsWith (SchemeApplication.check []
      [.mono (.bvar 0), .poly idScheme] 1 (.var 0) (.bvar 0) (.varMono rfl)
      (.arrow (.bvar 0) (.bvar 0)) (.bvar 0) []) "enclosing bound slot")]

def main : IO Unit := do
  for (name, ok) in cases do
    IO.println s!"{if ok then "PASS" else "FAIL"}: {name}"
    unless ok do throw (IO.userError s!"origin-backed scheme application regression: {name}")

#eval main

end FHM.Bounds.SchemeApplicationTests
