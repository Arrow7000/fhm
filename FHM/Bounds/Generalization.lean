import FHM.Bounds.Typed

/-! # Fresh HM generalization of bounds derivations

Free HM identities are substituted with complete caller bounds, not HM-shape
approximations. Source annotations and the captured environment must be fresh
for each generalized identity. This transports the existing fragment judgement;
it does not yet add scheme-aware executable variable or let rules.
-/

namespace FHM.Bounds.Generalization

mutual
def replace (z : Nat) (arg : BoundsTy) : BoundsTy → BoundsTy
  | .prim p => .prim p
  | .fvar i => if i = z then arg else .fvar i
  | .bvar i => .bvar i
  | .arrow a b => .arrow (replace z arg a) (replace z arg b)
  | .list lo hi a => .list lo hi (replace z arg a)
  | .custom n as => .custom n (replaceList z arg as)

def replaceList (z : Nat) (arg : BoundsTy) : List BoundsTy → List BoundsTy
  | [] => []
  | a :: as => replace z arg a :: replaceList z arg as
end

mutual
theorem fresh {z arg β} (h : z ∉ (Synth.BoundsTy.toTy β).freeVars) :
    replace z arg β = β := by
  cases β with
  | prim | bvar => rfl
  | fvar i =>
      have hi : i ≠ z := by simpa [Synth.BoundsTy.toTy, Ty.freeVars, eq_comm] using h
      simp [replace, hi]
  | arrow a b =>
      simp only [Synth.BoundsTy.toTy, Ty.freeVars, List.mem_dedup, List.mem_append, not_or] at h
      simp only [replace, fresh h.1, fresh h.2]
  | list lo hi a =>
      have ha : z ∉ (Synth.BoundsTy.toTy a).freeVars := by
        simpa [Synth.BoundsTy.toTy, listTy, Ty.freeVars, TyList.freeVars] using h
      simp only [replace, fresh ha]
  | custom n as =>
      exact congrArg (BoundsTy.custom n) (list_fresh (by simpa only [Synth.BoundsTy.toTy, Ty.freeVars] using h))
termination_by sizeOf β

private theorem list_fresh {z arg as}
    (h : z ∉ TyList.freeVars (as.map Synth.BoundsTy.toTy)) : replaceList z arg as = as := by
  cases as with
  | nil => rfl
  | cons a as =>
      simp only [List.map_cons, TyList.freeVars, List.mem_dedup, List.mem_append, not_or] at h
      simp only [replaceList, fresh h.1, list_fresh h.2]
termination_by sizeOf as
end

mutual
theorem subtype (z : Nat) (arg : BoundsTy) {Δ a b} (h : SemanticSub Δ a b) :
    SemanticSub Δ (replace z arg a) (replace z arg b) := by
  cases h with
  | prim => exact .prim
  | bvar => exact .bvar
  | fvar =>
      simp only [replace]
      split <;> exact SemanticSub.refl Δ _
  | arrow ha hb => exact .arrow (subtype z arg ha) (subtype z arg hb)
  | list hv he => exact .list hv (subtype z arg he)
  | custom hs => exact .custom (list_subtype z arg hs)
termination_by sizeOf a + sizeOf b

private theorem list_subtype (z : Nat) (arg : BoundsTy) {Δ as bs}
    (h : List.Forall₂ (SemanticSub Δ) as bs) :
    List.Forall₂ (SemanticSub Δ) (replaceList z arg as) (replaceList z arg bs) := by
  cases h with
  | nil => exact .nil
  | cons hh ht => exact .cons (subtype z arg hh) (list_subtype z arg ht)
termination_by sizeOf as + sizeOf bs
end

/-- Successful annotation decoding cannot invent a free HM identity absent
    from its carried source type. -/
theorem annotation_fresh {z arg τ β} (h : Typed.annotation τ = .ok β)
    (hf : z ∉ τ.freeVars) : replace z arg β = β := by
  induction τ using Ty.rec_strong generalizing β with
  | prim p => simp [Typed.annotation, pure, Except.pure] at h; subst β; rfl
  | fvar i =>
      simp [Typed.annotation, pure, Except.pure] at h; subst β
      apply fresh
      simpa only [Synth.BoundsTy.toTy] using hf
  | bvar i => simp [Typed.annotation, pure, Except.pure] at h; subst β; rfl
  | arrow a b iha ihb =>
      simp only [Ty.freeVars, List.mem_dedup, List.mem_append, not_or] at hf
      cases ha : Typed.annotation a <;> cases hb : Typed.annotation b <;>
        simp [Typed.annotation, ha, hb, bind, pure, Except.bind, Except.pure] at h
      subst β
      simp only [replace, iha ha hf.1, ihb hb hf.2]
  | bl lo hi a ih =>
      cases lo <;> cases hi <;>
        simp only [Typed.annotation, throw, reduceCtorEq] at h
      split at h
      · cases ha : Typed.annotation a <;> simp [ha, bind, pure, Except.bind, Except.pure] at h
        subst β
        simp only [replace, ih ha hf]
      · simp [bind, Except.bind] at h
  | customTy n as ih =>
      cases as with
      | nil => simp [Typed.annotation, throw] at h
      | cons a as =>
          cases as with
          | cons b bs => simp [Typed.annotation, throw] at h
          | nil =>
              have haFresh : z ∉ a.freeVars := by
                simpa [Ty.freeVars, TyList.freeVars] using hf
              simp only [Typed.annotation] at h
              split at h
              · cases ha : Typed.annotation a <;> simp [ha, bind, pure, Except.bind, Except.pure] at h
                subst β
                simp only [replace, ih a (by simp) ha haFresh]
              · simp [throw] at h

private theorem param {z arg Δ ann β} (h : Typed.ParamOK Δ ann β)
    (hf : z ∉ ann.elim [] Ty.freeVars) : Typed.ParamOK Δ ann (replace z arg β) := by
  cases ann with
  | none => trivial
  | some τ =>
      obtain ⟨demand, hd, hs⟩ := h
      exact ⟨demand, hd, by simpa only [annotation_fresh hd hf] using subtype z arg hs⟩

private theorem binding {z arg Δ ann β} (h : Typed.BindingOK Δ ann β)
    (hf : z ∉ ann.elim [] (fun σ => σ.body.freeVars)) :
    Typed.BindingOK Δ ann (replace z arg β) := by
  cases ann with
  | none => trivial
  | some σ => exact ⟨h.1, param (ann := some σ.body) h.2 hf⟩

/-- Arbitrary structured bounds can replace a fresh free HM identity throughout
    a derivation. The term itself and every source annotation stay unchanged. -/
theorem transport (z : Nat) (arg : BoundsTy) {Δ env e β}
    (h : Typed.Derives Δ env e β) (hf : z ∉ e.tyFreeVars) :
    Typed.Derives Δ (env.map (replace z arg)) e (replace z arg β) := by
  induction h with
  | literal => cases ‹PrimLitExpr› <;> exact .literal
  | primBinOp => cases ‹PrimBinOp› <;> exact .primBinOp
  | nil => exact .nil
  | cons hh ht hs ihh iht =>
      simp only [Expr.tyFreeVars, List.mem_append, List.not_mem_nil, false_or, not_or] at hf
      exact .cons (ihh hf.1) (iht hf.2) (subtype z arg hs)
  | var hv => exact .var (by simpa using congrArg (Option.map (replace z arg)) hv)
  | app hh ht hs ihh iht =>
      simp only [Expr.tyFreeVars, List.mem_append, not_or] at hf
      exact .app (ihh hf.1) (iht hf.2) (subtype z arg hs)
  | lambda hp hb ih =>
      simp only [Expr.tyFreeVars, List.mem_append, not_or] at hf
      exact .lambda (param hp hf.1) (ih hf.2)
  | letIn hp hr hb ihr ihb =>
      simp only [Expr.tyFreeVars, List.mem_append, not_or] at hf
      exact .letIn (binding hp hf.1.1) (ihr hf.1.2) (ihb hf.2)

/-- Generalizing an identity outside both source annotations and the captured
    environment gives a universal RHS typing fact, not just a shape equality. -/
theorem universal {z Δ env e β} (h : Typed.Derives Δ env e β)
    (he : z ∉ e.tyFreeVars)
    (henv : ∀ a ∈ env, z ∉ (Synth.BoundsTy.toTy a).freeVars) :
    ∀ arg, Typed.Derives Δ env e (replace z arg β) := by
  intro arg
  have hm : env.map (replace z arg) = env := by
    conv_rhs => rw [← List.map_id env]
    apply List.map_congr_left
    intro a ha
    exact fresh (henv a ha)
  simpa only [hm] using transport z arg h he

/-- Sequential substitutions, with the same left-to-right convention as
    Core's `Ty.substFvars`. No simultaneous-specialization claim is hidden here. -/
def replaceMany : List (Nat × BoundsTy) → BoundsTy → BoundsTy
  | [], β => β
  | (z, arg) :: rows, β => replaceMany rows (replace z arg β)

/-- A universal RHS contract for the generalized identity pool. Captured counts
    remain untouched. Caller-scope and HM-instance checks remain separate gates. -/
def GeneralizedRHS (ids : List Nat) (Δ : List Constraint) (env : List BoundsTy)
    (e : Expr) (β : BoundsTy) : Prop :=
  ∀ rows : List (Nat × BoundsTy), (∀ row ∈ rows, row.1 ∈ ids) →
    Typed.Derives Δ env e (replaceMany rows β)

theorem generalize {ids Δ env e β} (h : Typed.Derives Δ env e β)
    (he : ∀ z ∈ ids, z ∉ e.tyFreeVars)
    (henv : ∀ z ∈ ids, ∀ a ∈ env, z ∉ (Synth.BoundsTy.toTy a).freeVars) :
    GeneralizedRHS ids Δ env e β := by
  intro rows hr
  induction rows generalizing β with
  | nil => exact h
  | cons row rows ih =>
      obtain ⟨z, arg⟩ := row
      have hz := hr (z, arg) List.mem_cons_self
      exact ih (universal h (he z hz) (henv z hz) arg)
        (fun row hm => hr row (List.mem_cons_of_mem _ hm))

/-- The artifact's checked abstraction supplies precisely the required
    environment/source freshness interface. This proves RHS universality;
    scheme-aware uses must still supply specialization and scope evidence. -/
theorem fromBinder {σ Δ env e β}
    (a : BinderBridge.Abstraction σ β
      (env.map Synth.BoundsTy.toTy ++ e.tyFreeVars.map Ty.fvar))
    (h : Typed.Derives Δ env e β) : GeneralizedRHS a.ids Δ env e β := by
  apply generalize h
  · intro z hz he
    have hf := a.fresh z hz (.fvar z)
      (List.mem_append_right _ (List.mem_map.mpr ⟨z, he, rfl⟩))
    exact hf (by simp [Ty.freeVars])
  · intro z hz b hb
    exact a.fresh z hz (Synth.BoundsTy.toTy b)
      (List.mem_append_left _ (List.mem_map.mpr ⟨b, hb, rfl⟩))

#print axioms transport
#print axioms annotation_fresh
#print axioms subtype
#print axioms universal
#print axioms generalize
#print axioms fromBinder

end FHM.Bounds.Generalization
