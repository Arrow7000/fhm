import FHM.Bounds.RecursiveHMAnnotation

namespace FHM.Bounds.RecursiveHMAnnotationTests

open RecursiveHMAnnotation

private def n : Count := .var ⟨.rigid, 7⟩
private def list (a : Ty := .fvar 90) : Ty := .bl (.solid n) (.solid n) a
private def callerType : BoundsTy := .list n n (.prim .int)
private def types (i : Nat) : BoundsTy := if i = 90 then callerType else .fvar i
private def rows : CountSubstitution.Bindings := [(7, .lit 3)]

private def decoded (τ : Ty := list) (caller : List Nat := [7])
    (replacement : Nat → BoundsTy := types) (substitution : CountSubstitution.Bindings := rows)
    (ids : List Nat := [7]) : Except String BoundsTy := do
  pure (← decode replacement ids substitution caller τ).bounds

private def nestedCounts : Bool :=
  match decoded with
  | .ok (.list lo hi (.list innerLo innerHi (.prim .int))) =>
      lo == .lit 3 && hi == .lit 3 && innerLo == n && innerHi == n
  | _ => false

private def parameter (ann : Option Ty := some (.fvar 90)) (hm : Ty := .fvar 90)
    (expected : Option BoundsTy := none) (caller : List Nat := [7]) : Except String BoundsTy := do
  pure (← chooseParam types [7] rows caller [] ann hm expected).bounds

private def namedIdentity : Bool := match parameter with
  | .ok (.list lo hi (.prim .int)) => lo == n && hi == n
  | _ => false

private def binding (ann : Option PolyTy) (actual : BoundsTy) : Except String Unit := do
  let _ ← checkBinding types [7] rows [7] [] ann actual
  pure ()

private def succeeds (r : Except String α) : Bool := match r with | .ok _ => true | _ => false
private def fails (r : Except String α) (needle : String) : Bool :=
  match r with | .error m => (m.splitOn needle).length > 1 | _ => false

private def cases : List (String × Bool) := [
  ("source endpoints specialize before complete caller types are inserted", nestedCounts),
  ("named source HM identity becomes its full caller parameter type", namedIdentity),
  ("caller counts inside inserted HM types cannot escape", fails (decoded list []) "outside caller scope"),
  ("source lexical count scope is checked before substitution", fails
    (decoded (.bl (.solid (.var ⟨.rigid, 8⟩)) (.solid (.lit 3)) (.prim .int)) [] types [(8, .lit 3)])
    "scope"),
  ("an infinite Nat replacement rejects even if unused by the annotation", fails
    (decoded (.fvar 90) [7] types [(7, .inf)]) "infinite Nat replacement"),
  ("simultaneous HM interpretation leaves identities inside inserted types unchanged", succeeds
    (decoded (.fvar 90) [] (fun i => if i = 90 then .fvar 91 else .prim .int) [] [])),
  ("parameter annotation must agree with the interpreted discovered HM payload", fails
    (parameter (some (.fvar 90)) (.prim .char)) "found payload"),
  ("unannotated parameter can use an explicit exact caller domain", succeeds
    (parameter none (.fvar 90) (some callerType))),
  ("unannotated parameter cannot use a wrong HM domain", fails
    (parameter none (.fvar 90) (some (.prim .int))) "found payload"),
  ("explicit domain counts still require caller scope", fails
    (parameter none (.fvar 90) (some callerType) []) "outside caller scope"),
  ("unguided List parameter does not invent a bounds assumption", !succeeds
    (parameter none (.fvar 90) none [])),
  ("carried mono binding checks actual exact counts under the same HM interpretation", succeeds
    (binding (some ⟨0, list⟩) (.list (.lit 3) (.lit 3) callerType))),
  ("carried mono binding cannot claim a false interval", fails
    (binding (some ⟨0, list⟩) (.list (.lit 2) (.lit 2) callerType)) "interval inclusion"),
  ("internal polymorphic annotation is explicitly rejected by the current RHS slice", fails
    (binding (some ⟨1, list (.bvar 0)⟩) (.list (.lit 3) (.lit 3) callerType)) "polymorphic HM internal"),
  ("unannotated mono binding has no fabricated source obligation", succeeds
    (binding none callerType)),
  ("binding hint retains count-first/full-HM interpreted source demand", succeeds
    (bindingHint types [7] rows [7] (some ⟨0, list⟩)))]

def main : IO Unit := do
  for (name, ok) in cases do
    IO.println s!"{if ok then "PASS" else "FAIL"}: {name}"
    unless ok do throw (IO.userError s!"interpreted annotation regression failed: {name}")

#eval main

end FHM.Bounds.RecursiveHMAnnotationTests
