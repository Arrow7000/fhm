import FHM.Bounds.SchemeSpecialization

/-! # Executable specialization of a certified generalized RHS

The caller supplies actual bounds arguments. Matching HM shapes is a necessary
interface check, not evidence that those arguments describe any expression's
runtime value. Argument-origin typing remains the consuming rule's obligation.
This API proves the specialized RHS judgement, exact final HM shape and count
scope; it does not yet enable polymorphic variables in `Typed.walk`.
-/

namespace FHM.Bounds.SchemeUse

def vector (args : List BoundsTy) (i : Nat) : BoundsTy :=
  args[i]?.getD (.prim .unit)

theorem vector_shape {args : List BoundsTy} {expected : List Ty}
    (h : args.map Synth.BoundsTy.toTy = expected) {i t}
    (hi : expected[i]? = some t) : Synth.BoundsTy.toTy (vector args i) = t := by
  rw [← h] at hi
  cases ha : args[i]? with
  | none => simp [List.getElem?_map, ha] at hi
  | some a =>
      simp only [List.getElem?_map, ha, Option.map_some, Option.some.injEq] at hi
      simpa only [vector, ha, Option.getD_some] using hi

theorem vector_scope {args : List BoundsTy} {scope}
    (h : args.all (ScopedScheme.boundsScopedBool scope) = true) :
    ∀ i, ScopedScheme.BoundsScoped scope (vector args i) := by
  intro i
  cases ha : args[i]? with
  | none => simp [vector, ha, ScopedScheme.BoundsScoped]
  | some a =>
      have hm : a ∈ args := List.mem_of_getElem? ha
      simpa only [vector, ha, Option.getD_some] using
        ScopedScheme.boundsScopedBool_sound (List.all_eq_true.mp h a hm)

structure Result (Δ : List Constraint) (env : List BoundsTy) (rhs : Expr)
    (found : Ty) (scope : List Nat) where
  bounds : BoundsTy
  derivation : Typed.Derives Δ env rhs bounds
  shape : Synth.BoundsTy.toTy bounds = found.eraseBounds
  countScope : ScopedScheme.BoundsScoped scope bounds

/-- Complete checked use, with no shape-only argument reconstruction. The Unit
    value in `vector` serves only unused total-function slots: matching the full
    argument list prevents a used HM slot from falling outside that list. -/
def check {σ Δ env rhs β}
    (binding : BinderBridge.Abstraction σ β
      (env.map Synth.BoundsTy.toTy ++ rhs.tyFreeVars.map Ty.fvar))
    (typing : Typed.Derives Δ env rhs β)
    (found : Ty) (args : List BoundsTy) (scope : List Nat) :
    Except String (Result Δ env rhs found scope) := do
  let use ← BinderBridge.instantiate σ found
  let shapes ← match BinderBridge.equalTys (args.map Synth.BoundsTy.toTy) use.args with
    | none => throw "bounds: supplied argument bounds disagree with HM scheme instance"
    | some evidence => pure evidence
  if ha : args.all (ScopedScheme.boundsScopedBool scope) = true then
    if hb : ScopedScheme.boundsScopedBool scope β = true then
      if args.all (fun a => (Synth.BoundsTy.toTy a).bvarsBelow 0) then
        let specialized := TypeSubstitution.substitute (vector args) (BinderBridge.close binding.ids β)
        let proof := SchemeSpecialization.checked_use binding typing use (vector args)
          (fun _ _ hi => vector_shape shapes.down hi)
        pure ⟨specialized, proof.1, proof.2,
          SchemeSpecialization.caller_scope binding.ids (vector args)
            (ScopedScheme.boundsScopedBool_sound hb) (vector_scope ha)⟩
      else throw "bounds: supplied HM argument contains an enclosing bound slot"
    else throw "bounds: generalized RHS counts are outside caller scope"
  else throw "bounds: supplied argument counts are outside caller scope"

#print axioms check

end FHM.Bounds.SchemeUse
