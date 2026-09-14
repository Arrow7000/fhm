import FHM.Bounds.SchemeSpecialization

namespace FHM.Bounds.SchemeSpecializationTests

open SchemeSpecialization

private def n : Count := .var ⟨.rigid, 7⟩
private def caller : BoundsTy := .list n n (.fvar 8)
private def args : Nat → BoundsTy := fun i => if i = 0 then caller else .prim .int
private def actual : BoundsTy := .arrow (.fvar 7) (.fvar 8)

-- Caller fvar8 must not be rewritten by the argument for generalized slot1.
example : mapFree (argument [7, 8] args) actual = .arrow caller (.prim .int) := rfl
example : TypeSubstitution.substitute args (BinderBridge.close [7, 8] actual) =
    .arrow caller (.prim .int) := rfl
example : Generalization.replaceMany [(7, caller), (8, .prim .int)] actual =
    .arrow (.list n n (.prim .int)) (.prim .int) := rfl

example {β} (h : (Synth.BoundsTy.toTy β).IsLC) :
    TypeSubstitution.substitute args (BinderBridge.close [7, 8] β) =
      mapFree (argument [7, 8] args) β := close_open [7, 8] args h

private def identity : Expr := .lambda none (.var 0)
private def identityBounds : BoundsTy := .arrow (.fvar 7) (.fvar 7)
private def scheme : PolyTy := ⟨1, .arrow (.bvar 0) (.bvar 0)⟩

private theorem identityDerives : Typed.Derives [] [] identity identityBounds :=
  .lambda True.intro (.var rfl)

-- The identity implementation supports complete caller list bounds, not just
-- the bare List spine, even with generalized/caller identity collisions.
example (a : BinderBridge.Abstraction scheme identityBounds
    ([] ++ identity.tyFreeVars.map Ty.fvar)) :
    Typed.Derives [] [] identity
      (TypeSubstitution.substitute args (BinderBridge.close a.ids identityBounds)) :=
  fromBinder a identityDerives args

example (a : BinderBridge.Abstraction scheme identityBounds
    ([] ++ identity.tyFreeVars.map Ty.fvar)) {found}
    (use : BinderBridge.Instance scheme found)
    (ha : ∀ i t, use.args[i]? = some t → Synth.BoundsTy.toTy (args i) = t) :
    Typed.Derives [] [] identity
      (TypeSubstitution.substitute args (BinderBridge.close a.ids identityBounds)) ∧
    Synth.BoundsTy.toTy (TypeSubstitution.substitute args
      (BinderBridge.close a.ids identityBounds)) = found.eraseBounds :=
  checked_use a identityDerives use args ha

example : ScopedScheme.BoundsScoped [7]
    (TypeSubstitution.substitute args (BinderBridge.close [7, 8] actual)) := by
  apply caller_scope [7, 8] args
  · trivial
  · intro i
    simp only [args]
    split
    · exact ⟨by simp [n, Scope.CountScoped], by simp [n, Scope.CountScoped], True.intro⟩
    · trivial

private def cases : List (String × Bool) := [
  ("caller identities are not respecialized", match mapFree (argument [7, 8] args) actual with
    | .arrow (.list _ _ (.fvar 8)) (.prim .int) => true | _ => false),
  ("closed scheme has the same exact specialization", match
      TypeSubstitution.substitute args (BinderBridge.close [7, 8] actual) with
    | .arrow (.list _ _ (.fvar 8)) (.prim .int) => true | _ => false),
  ("sequential substitution exposes the collision", match
      Generalization.replaceMany [(7, caller), (8, .prim .int)] actual with
    | .arrow (.list _ _ (.prim .int)) (.prim .int) => true | _ => false),
  ("captured free identity stays fixed", match mapFree (argument [7, 8] args) (.fvar 99) with
    | .fvar 99 => true | _ => false),
  ("mapping leaves original bound slots fixed", match mapFree (argument [7, 8] args) (.bvar 7) with
    | .bvar 7 => true | _ => false),
  ("counts in original bounds are untouched", match mapFree (argument [7, 8] args) (.list n n (.fvar 7)) with
    | .list lo hi _ => lo == n && hi == n | _ => false),
  ("counts in inserted bounds are untouched", match mapFree (argument [7, 8] args) (.fvar 7) with
    | .list lo hi _ => lo == n && hi == n | _ => false),
  ("slot order comes from the actual identity pool", match argument [8, 7] args 8 with
    | .list _ _ (.fvar 8) => true | _ => false),
  ("second slot receives its own argument", match argument [7, 8] args 8 with
    | .prim .int => true | _ => false),
  ("empty pool preserves free identities", match argument [] args 7 with
    | .fvar 7 => true | _ => false),
  ("nested constructor fields specialize", match mapFree (argument [7, 8] args)
      (.custom ⟨"Box"⟩ [.fvar 7, .fvar 99]) with
    | .custom _ [.list _ _ (.fvar 8), .fvar 99] => true | _ => false),
  ("self replacement terminates without recursion", match mapFree
      (argument [7] (fun _ => .fvar 7)) (.fvar 7) with
    | .fvar 7 => true | _ => false)]

def main : IO Unit := do
  for (name, ok) in cases do
    IO.println s!"{if ok then "PASS" else "FAIL"}: {name}"
    unless ok do throw (IO.userError s!"scheme specialization regression: {name}")

#eval main

end FHM.Bounds.SchemeSpecializationTests
