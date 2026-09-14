import FHM.Bounds.SchemeVariable

/-! # Origin-backed single-slot polymorphic application

The domain must be the scheme's sole HM slot. The argument's existing bounds
derivation then supplies the full slot bounds, not an HM-shape approximation.
More general structural slot inference, quantified count contracts and residual
goals remain explicitly outside this slice.
-/

namespace FHM.Bounds.SchemeApplication

open SchemeTyping

structure Result (Δ : List Constraint) (env : List Binding) (i : Nat) (arg : Expr)
    (found : Ty) (scope : List Nat) where
  bounds : BoundsTy
  derivation : Derives Δ env (.app (.var i) arg) bounds
  shape : Synth.BoundsTy.toTy bounds = found.eraseBounds
  countScope : ScopedScheme.BoundsScoped scope bounds

def check (Δ : List Constraint) (env : List Binding) (i : Nat) (arg : Expr)
    (actual : BoundsTy) (typing : Derives Δ env arg actual)
    (functionHM resultHM : Ty) (scope : List Nat) :
    Except String (Result Δ env i arg resultHM scope) := do
  match lookup : env[i]? with
  | none => throw "bounds: polymorphic application variable outside environment"
  | some (.mono _) => throw "bounds: origin-backed scheme application requires a polymorphic binding"
  | some (.poly s) =>
      if s.hm.paramCount = 1 then
        match body : s.body with
        | .arrow (.bvar 0) result =>
            let callee ← SchemeVariable.check Δ env i functionHM [actual] scope
            have vb : callee.bounds = s.instantiate [actual] := by
              rcases callee.selected with mono | ⟨selected, selectedAt, vb, _⟩
              · rw [lookup] at mono
                cases mono
              · rw [lookup] at selectedAt
                cases selectedAt
                exact vb
            have fn : callee.bounds = .arrow actual
                (TypeSubstitution.substitute (SchemeUse.vector [actual]) result) := by
              rw [vb, Scheme.instantiate, body]
              simp only [TypeSubstitution.substitute, SchemeUse.vector,
                List.getElem?_cons_zero, Option.getD_some]
            let bounds := TypeSubstitution.substitute (SchemeUse.vector [actual]) result
            let shape ← match BinderBridge.equalTy (Synth.BoundsTy.toTy bounds) resultHM.eraseBounds with
              | none => throw "bounds: polymorphic application result disagrees with found payload"
              | some shape => pure shape
            have fnTyping : Derives Δ env (.var i) (.arrow actual bounds) := by
              simpa only [fn] using callee.derivation
            have countScope : ScopedScheme.BoundsScoped scope bounds := by
              have hc := callee.countScope
              rw [fn] at hc
              exact hc.2
            pure ⟨bounds, .app fnTyping typing (SemanticSub.refl Δ actual), shape.down, countScope⟩
        | _ => throw "bounds: structural polymorphic application argument inference unsupported"
      else throw "bounds: origin-backed application supports exactly one HM slot"

#print axioms check

end FHM.Bounds.SchemeApplication
