import FHM.Bounds.SchemeTyping

/-! # Checked scheme-aware variable rule

Consumes the exact de Bruijn environment entry and the final HM payload.
Supplied bounds arguments are checked, never reconstructed from HM shapes.
Environment introduction must establish `SchemeTyping.Derives.letPoly`'s RHS
premise; this component does not certify arbitrary externally invented entries.
-/

namespace FHM.Bounds.SchemeVariable

open SchemeTyping

structure Result (Δ : List Constraint) (env : List Binding) (i : Nat)
    (found : Ty) (scope : List Nat) (args : List BoundsTy) where
  bounds : BoundsTy
  derivation : Derives Δ env (.var i) bounds
  shape : Synth.BoundsTy.toTy bounds = found.eraseBounds
  countScope : ScopedScheme.BoundsScoped scope bounds
  selected : env[i]? = some (.mono bounds) ∨
    ∃ s, env[i]? = some (.poly s) ∧ bounds = s.instantiate args ∧ s.Arguments args

def check (Δ : List Constraint) (env : List Binding) (i : Nat)
    (found : Ty) (args : List BoundsTy) (scope : List Nat) :
    Except String (Result Δ env i found scope args) := do
  match lookup : env[i]? with
  | none => throw "bounds: variable outside scheme-aware bounds environment"
  | some (.mono β) =>
      unless args.isEmpty do throw "bounds: monomorphic variable does not take scheme arguments"
      let shape ← match BinderBridge.equalTy (Synth.BoundsTy.toTy β) found.eraseBounds with
        | none => throw "bounds: monomorphic variable disagrees with found payload"
        | some shape => pure shape
      if hc : ScopedScheme.boundsScopedBool scope β = true then
        pure ⟨β, .varMono lookup, shape.down, ScopedScheme.boundsScopedBool_sound hc, .inl lookup⟩
      else throw "bounds: monomorphic variable counts are outside caller scope"
  | some (.poly s) =>
      let use ← BinderBridge.instantiate s.hm found
      let shapes ← match BinderBridge.equalTys (args.map Synth.BoundsTy.toTy) use.args with
        | none => throw "bounds: supplied argument bounds disagree with HM scheme instance"
        | some shapes => pure shapes
      if hlc : args.all (fun a => (Synth.BoundsTy.toTy a).bvarsBelow 0) = true then
        if ha : args.all (ScopedScheme.boundsScopedBool scope) = true then
          if hb : ScopedScheme.boundsScopedBool scope s.body = true then
            have arguments : s.Arguments args := ⟨by rw [shapes.down]; exact use.arity, by
              intro t ht
              obtain ⟨a, ha, rfl⟩ := List.mem_map.mp ht
              exact (Ty.bvarsBelow_iff (Synth.BoundsTy.toTy a)).mp
                (List.all_eq_true.mp hlc a ha)⟩
            have shape : Synth.BoundsTy.toTy (s.instantiate args) = found.eraseBounds := by
              rw [Scheme.instantiate, TypeSubstitution.shape, s.erasedShape]
              exact TypeSubstitution.hm_instance use.witness _
                (fun _ _ h => SchemeUse.vector_shape shapes.down h)
            pure ⟨s.instantiate args, .varPoly lookup arguments, shape,
              TypeSubstitution.inScope (SchemeUse.vector args)
                (ScopedScheme.boundsScopedBool_sound hb) (SchemeUse.vector_scope ha),
              .inr ⟨s, lookup, rfl, arguments⟩⟩
          else throw "bounds: captured scheme counts are outside caller scope"
        else throw "bounds: supplied argument counts are outside caller scope"
      else throw "bounds: supplied HM argument contains an enclosing bound slot"

#print axioms check

end FHM.Bounds.SchemeVariable
