import FHM.Bounds.Generalization

/-! # Simultaneous specialization of generalized RHS bounds

Unlike sequential free substitution, caller arguments are never rewritten by
other slots. This is essential when a caller type identity happens to equal a
generalized identity. The exact close/open theorem connects RHS typing to the
existing certified HM scheme-instantiation bridge.
-/

namespace FHM.Bounds.SchemeSpecialization

mutual
def mapFree (f : Nat → BoundsTy) : BoundsTy → BoundsTy
  | .prim p => .prim p
  | .fvar i => f i
  | .bvar i => .bvar i
  | .arrow a b => .arrow (mapFree f a) (mapFree f b)
  | .list lo hi a => .list lo hi (mapFree f a)
  | .custom n as => .custom n (mapFreeList f as)

def mapFreeList (f : Nat → BoundsTy) : List BoundsTy → List BoundsTy
  | [] => []
  | a :: as => mapFree f a :: mapFreeList f as
end

mutual
theorem fixed {f β} (h : ∀ i ∈ (Synth.BoundsTy.toTy β).freeVars, f i = .fvar i) :
    mapFree f β = β := by
  cases β with
  | prim | bvar => rfl
  | fvar i => exact h i (by simp [Synth.BoundsTy.toTy, Ty.freeVars])
  | arrow a b =>
      simp only [mapFree]
      congr 1
      · exact fixed (fun i hi => h i (by simp [Synth.BoundsTy.toTy, Ty.freeVars, hi]))
      · exact fixed (fun i hi => h i (by simp [Synth.BoundsTy.toTy, Ty.freeVars, hi]))
  | list lo hi a =>
      exact congrArg (BoundsTy.list lo hi) (fixed (fun i hi => h i
        (by simpa [Synth.BoundsTy.toTy, listTy, Ty.freeVars, TyList.freeVars] using hi)))
  | custom n as => exact congrArg (BoundsTy.custom n) (list_fixed
      (by simpa only [Synth.BoundsTy.toTy, Ty.freeVars] using h))
termination_by sizeOf β

private theorem list_fixed {f as}
    (h : ∀ i ∈ TyList.freeVars (as.map Synth.BoundsTy.toTy), f i = .fvar i) :
    mapFreeList f as = as := by
  cases as with
  | nil => rfl
  | cons a as =>
      simp only [mapFreeList]
      congr 1
      · exact fixed (fun i hi => h i (by simp [TyList.freeVars, hi]))
      · exact list_fixed (fun i hi => h i (by simp [TyList.freeVars, hi]))
termination_by sizeOf as
end

mutual
theorem subtype (f : Nat → BoundsTy) {Δ a b} (h : SemanticSub Δ a b) :
    SemanticSub Δ (mapFree f a) (mapFree f b) := by
  cases h with
  | prim => exact .prim
  | bvar => exact .bvar
  | fvar => exact SemanticSub.refl Δ _
  | arrow ha hb => exact .arrow (subtype f ha) (subtype f hb)
  | list hv he => exact .list hv (subtype f he)
  | custom hs => exact .custom (list_subtype f hs)
termination_by sizeOf a + sizeOf b

private theorem list_subtype (f : Nat → BoundsTy) {Δ as bs}
    (h : List.Forall₂ (SemanticSub Δ) as bs) :
    List.Forall₂ (SemanticSub Δ) (mapFreeList f as) (mapFreeList f bs) := by
  cases h with
  | nil => exact .nil
  | cons hh ht => exact .cons (subtype f hh) (list_subtype f ht)
termination_by sizeOf as + sizeOf bs
end

mutual
theorem annotation_fixed {f τ β} (h : Typed.annotation τ = .ok β)
    (hf : ∀ i ∈ τ.freeVars, f i = .fvar i) : mapFree f β = β := by
  cases τ with
  | prim p => simp [Typed.annotation, pure, Except.pure] at h; subst β; rfl
  | fvar i =>
      simp [Typed.annotation, pure, Except.pure] at h; subst β
      exact hf i (by simp [Ty.freeVars])
  | bvar i => simp [Typed.annotation, pure, Except.pure] at h; subst β; rfl
  | arrow a b =>
      cases ha : Typed.annotation a <;> cases hb : Typed.annotation b <;>
        simp [Typed.annotation, ha, hb, bind, pure, Except.bind, Except.pure] at h
      subst β
      simp only [mapFree]
      congr 1
      · exact annotation_fixed ha (fun i hi => hf i (by simp [Ty.freeVars, hi]))
      · exact annotation_fixed hb (fun i hi => hf i (by simp [Ty.freeVars, hi]))
  | bl lo hi a =>
      cases lo <;> cases hi <;> simp only [Typed.annotation, throw, reduceCtorEq] at h
      split at h
      · cases ha : Typed.annotation a <;> simp [ha, bind, pure, Except.bind, Except.pure] at h
        subst β
        exact congrArg (BoundsTy.list _ _) (annotation_fixed ha hf)
      · simp [bind, Except.bind] at h
  | customTy name args =>
      by_cases hn : name = listTyName
      · subst name
        cases args with
        | nil => rw [Typed.annotation.eq_def] at h; simp [throw] at h
        | cons a rest =>
            cases rest with
            | cons b bs => rw [Typed.annotation.eq_def] at h; simp [throw] at h
            | nil =>
                rw [Typed.annotation.eq_def] at h
                cases ha : Typed.annotation a <;>
                  simp [ha, bind, pure, Except.bind, Except.pure] at h
                subst β
                exact congrArg (BoundsTy.list _ _)
                  (annotation_fixed ha (fun i hi => hf i
                    (by simpa [Ty.freeVars, TyList.freeVars] using hi)))
      · cases hs : Typed.annotationList args with
        | error message =>
            rw [Typed.annotation.eq_def] at h
            simp [hn, hs, bind, Except.bind] at h
        | ok decoded =>
            rw [Typed.annotation.eq_def] at h
            simp [hn, hs, bind, pure, Except.bind, Except.pure] at h
            subst β
            exact congrArg (BoundsTy.custom name)
              (annotationList_fixed hs (by simpa only [Ty.freeVars] using hf))
termination_by sizeOf τ

private theorem annotationList_fixed {f types decoded}
    (h : Typed.annotationList types = .ok decoded)
    (hf : ∀ i ∈ TyList.freeVars types, f i = .fvar i) :
    mapFreeList f decoded = decoded := by
  cases types with
  | nil => simp [Typed.annotationList, pure, Except.pure] at h; subst decoded; rfl
  | cons ty rest =>
      cases ht : Typed.annotation ty <;> cases hr : Typed.annotationList rest <;>
        simp [Typed.annotationList, ht, hr, bind, pure, Except.bind, Except.pure] at h
      subst decoded
      simp only [mapFreeList,
        annotation_fixed ht (fun i hi => hf i (TyList.mem_freeVars_of_mem (by simp) hi)),
        annotationList_fixed hr (fun i hi => hf i (by simp [TyList.freeVars, hi]))]
termination_by sizeOf types
end

theorem param {f Δ ann β} (h : Typed.ParamOK Δ ann β)
    (hf : ∀ i ∈ ann.elim [] Ty.freeVars, f i = .fvar i) :
    Typed.ParamOK Δ ann (mapFree f β) := by
  cases ann with
  | none => trivial
  | some τ =>
      obtain ⟨demand, hd, hs⟩ := h
      exact ⟨demand, hd, by simpa only [annotation_fixed hd hf] using subtype f hs⟩

theorem binding {f Δ ann β} (h : Typed.BindingOK Δ ann β)
    (hf : ∀ i ∈ ann.elim [] (fun σ => σ.body.freeVars), f i = .fvar i) :
    Typed.BindingOK Δ ann (mapFree f β) := by
  cases ann with
  | none => trivial
  | some σ => exact ⟨h.1, param (ann := some σ.body) h.2 hf⟩

theorem transport (f : Nat → BoundsTy) {Δ env e β} (h : Typed.Derives Δ env e β)
    (hf : ∀ i ∈ e.tyFreeVars, f i = .fvar i) :
    Typed.Derives Δ (env.map (mapFree f)) e (mapFree f β) := by
  induction h with
  | literal => cases ‹PrimLitExpr› <;> exact .literal
  | primBinOp => cases ‹PrimBinOp› <;> exact .primBinOp
  | nil => exact .nil
  | cons hh ht hs ihh iht =>
      exact .cons (ihh (fun i hi => hf i (by simp [Expr.tyFreeVars, hi])))
        (iht (fun i hi => hf i (by simp [Expr.tyFreeVars, hi]))) (subtype f hs)
  | var hv => exact .var (by simpa using congrArg (Option.map (mapFree f)) hv)
  | app hh ht hs ihh iht =>
      exact .app (ihh (fun i hi => hf i (by simp [Expr.tyFreeVars, hi])))
        (iht (fun i hi => hf i (by simp [Expr.tyFreeVars, hi]))) (subtype f hs)
  | lambda hp hb ih =>
      exact .lambda (param hp (fun i hi => hf i (List.mem_append_left _ hi)))
        (ih (fun i hi => hf i (List.mem_append_right _ hi)))
  | letIn hp hr hb ihr ihb =>
      exact .letIn (binding hp (fun i hi => hf i (List.mem_append_left _ (List.mem_append_left _ hi))))
        (ihr (fun i hi => hf i (List.mem_append_left _ (List.mem_append_right _ hi))))
        (ihb (fun i hi => hf i (List.mem_append_right _ hi)))

def argument (ids : List Nat) (args : Nat → BoundsTy) (i : Nat) : BoundsTy :=
  match ids.idxOf? i with
  | none => .fvar i
  | some slot => args slot

private theorem opaque_slot {ids : List Nat} (distinct : ids.Nodup) {i : Nat}
    (inside : i < ids.length) : ids.idxOf? ids[i] = some i := by
  induction ids generalizing i with
  | nil => simp at inside
  | cons head rest ih =>
      obtain ⟨absent, tailDistinct⟩ := List.nodup_cons.mp distinct
      cases i with
      | zero => simp [List.idxOf?_cons]
      | succ i =>
          have tailInside : i < rest.length := by simp only [List.length_cons] at inside; omega
          have different : head ≠ rest[i] := fun same => absent (same ▸ List.getElem_mem tailInside)
          simpa only [List.getElem_cons_succ, List.idxOf?_cons,
            show (head == rest[i]) = false from by simpa using different,
            Bool.false_eq_true, if_false, ih tailDistinct tailInside, Option.map_some] using
              (rfl : some (i + 1) = some (i + 1))

/-- Opaque scheme identities read exactly their assigned simultaneous slots. -/
theorem argument_slot (ids : List Nat) (args : Nat → BoundsTy) (distinct : ids.Nodup)
    (i : Nat) (inside : i < ids.length) : argument ids args ids[i] = args i := by
  simp only [argument, opaque_slot distinct inside]

#print axioms argument_slot

mutual
theorem close_open (ids : List Nat) (args : Nat → BoundsTy) {β}
    (hlc : (Synth.BoundsTy.toTy β).IsLC) :
    TypeSubstitution.substitute args (BinderBridge.close ids β) = mapFree (argument ids args) β := by
  cases β with
  | prim => rfl
  | fvar i => simp only [BinderBridge.close, mapFree, argument]; cases ids.idxOf? i <;> rfl
  | bvar i =>
      simp only [Synth.BoundsTy.toTy] at hlc
      cases hlc with | bvar h => omega
  | arrow a b =>
      simp only [Synth.BoundsTy.toTy] at hlc
      cases hlc with
      | arrow ha hb => simp only [BinderBridge.close, TypeSubstitution.substitute, mapFree,
          close_open ids args ha, close_open ids args hb]
  | list lo hi a =>
      simp only [Synth.BoundsTy.toTy, listTy] at hlc
      cases hlc with
      | customTy hall =>
          exact congrArg (BoundsTy.list lo hi) (close_open ids args (hall _ (by simp)))
  | custom n as =>
      simp only [Synth.BoundsTy.toTy] at hlc
      cases hlc with
      | customTy hall => exact congrArg (BoundsTy.custom n) (list_close_open ids args hall)
termination_by sizeOf β

private theorem list_close_open (ids : List Nat) (args : Nat → BoundsTy) {as}
    (hlc : ∀ t ∈ as.map Synth.BoundsTy.toTy, t.IsLC) :
    TypeSubstitution.substituteList args (BinderBridge.closeList ids as) =
      mapFreeList (argument ids args) as := by
  cases as with
  | nil => rfl
  | cons a as =>
      simp only [BinderBridge.closeList, TypeSubstitution.substituteList, mapFreeList]
      congr 1
      · exact close_open ids args (hlc _ (by simp))
      · exact list_close_open ids args (fun t ht => hlc t (List.mem_cons_of_mem _ ht))
termination_by sizeOf as
end

/-- Universality at the exact closed scheme, even when caller identities overlap
    the generalized pool. HM instance and caller count scope remain separate. -/
theorem fromBinder {σ Δ env e β}
    (a : BinderBridge.Abstraction σ β
      (env.map Synth.BoundsTy.toTy ++ e.tyFreeVars.map Ty.fvar))
    (h : Typed.Derives Δ env e β) (args : Nat → BoundsTy) :
    Typed.Derives Δ env e (TypeSubstitution.substitute args (BinderBridge.close a.ids β)) := by
  have keep : ∀ i ∉ a.ids, argument a.ids args i = .fvar i := by
    intro i hi
    simp only [argument, List.idxOf?_eq_none_iff.mpr hi]
  have source : ∀ i ∈ e.tyFreeVars, argument a.ids args i = .fvar i := by
    intro i hi
    apply keep i
    intro hc
    exact a.fresh i hc (.fvar i)
      (List.mem_append_right _ (List.mem_map.mpr ⟨i, hi, rfl⟩)) (by simp [Ty.freeVars])
  have envFixed : env.map (mapFree (argument a.ids args)) = env := by
    conv_rhs => rw [← List.map_id env]
    apply List.map_congr_left
    intro b hb
    apply fixed
    intro i hi
    apply keep i
    intro hc
    exact a.fresh i hc (Synth.BoundsTy.toTy b)
      (List.mem_append_left _ (List.mem_map.mpr ⟨b, hb, rfl⟩)) hi
  rw [close_open a.ids args a.originalLC]
  simpa only [envFixed] using transport (argument a.ids args) h source

/-- Join RHS universality and the actual final HM use witness. Neither an
    invented scheme nor mere shape similarity supplies the typing premise. -/
theorem checked_use {σ Δ env e β found}
    (a : BinderBridge.Abstraction σ β
      (env.map Synth.BoundsTy.toTy ++ e.tyFreeVars.map Ty.fvar))
    (h : Typed.Derives Δ env e β) (use : BinderBridge.Instance σ found)
    (args : Nat → BoundsTy)
    (ha : ∀ i t, use.args[i]? = some t → Synth.BoundsTy.toTy (args i) = t) :
    Typed.Derives Δ env e (TypeSubstitution.substitute args (BinderBridge.close a.ids β)) ∧
    Synth.BoundsTy.toTy (TypeSubstitution.substitute args (BinderBridge.close a.ids β)) =
      found.eraseBounds := by
  refine ⟨fromBinder a h args, ?_⟩
  rw [TypeSubstitution.shape, a.shape]
  exact TypeSubstitution.hm_instance use.witness _ ha

theorem caller_scope {scope β} (ids : List Nat) (args : Nat → BoundsTy)
    (hb : ScopedScheme.BoundsScoped scope β)
    (ha : ∀ i, ScopedScheme.BoundsScoped scope (args i)) :
    ScopedScheme.BoundsScoped scope
      (TypeSubstitution.substitute args (BinderBridge.close ids β)) :=
  TypeSubstitution.inScope args (BinderBridge.close_inScope ids hb) ha

#print axioms transport
#print axioms close_open
#print axioms fromBinder
#print axioms checked_use
#print axioms caller_scope

end FHM.Bounds.SchemeSpecialization
