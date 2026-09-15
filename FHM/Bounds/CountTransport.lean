import FHM.Bounds.SchemeTransport

/-! # Count substitution of mixed-scheme bounds derivations

Finite selected count substitution transports path conditions, environment and
result together. Universal RHSs are opened at fresh HM placeholders first, then
specialized to arbitrary caller bounds, so caller counts are not rewritten as
scheme counts. Existing annotation premises remain the ground-only fragment.
This does not yet introduce quantified declarations or generalize unknowns.
-/

namespace FHM.Bounds.CountTransport

open SchemeTyping CountSubstitution

def mapScheme (rows : Bindings) (s : SchemeTyping.Scheme) : SchemeTyping.Scheme :=
  ⟨s.hm, bounds rows s.body, s.wf, (bounds_shape rows s.body).trans s.shape⟩

def mapBinding (rows : Bindings) : Binding → Binding
  | .mono β => .mono (bounds rows β)
  | .poly s => .poly (mapScheme rows s)

theorem arguments_mapped (rows : Bindings) {s : SchemeTyping.Scheme} {args}
    (ha : s.Arguments args) : (mapScheme rows s).Arguments (args.map (bounds rows)) := by
  simpa only [Scheme.Arguments, mapScheme, List.map_map, Function.comp_def, bounds_shape] using ha

theorem vector_mapped (rows : Bindings) (args : List BoundsTy) (i : Nat) :
    SchemeUse.vector (args.map (bounds rows)) i = bounds rows (SchemeUse.vector args i) := by
  cases h : args[i]? <;> simp [SchemeUse.vector, List.getElem?_map, h, bounds]

mutual
theorem instantiate_commute (rows : Bindings) (args : Nat → BoundsTy) (β : BoundsTy) :
    bounds rows (TypeSubstitution.substitute args β) =
      TypeSubstitution.substitute (fun i => bounds rows (args i)) (bounds rows β) := by
  cases β with
  | prim | fvar | bvar => rfl
  | arrow a b => simp only [bounds, TypeSubstitution.substitute, instantiate_commute rows args a,
      instantiate_commute rows args b]
  | list lo hi elem =>
      exact congrArg (BoundsTy.list (count rows lo) (count rows hi))
        (instantiate_commute rows args elem)
  | custom name as => exact congrArg (BoundsTy.custom name) (list_instantiate_commute rows args as)
termination_by sizeOf β

private theorem list_instantiate_commute (rows : Bindings) (args : Nat → BoundsTy)
    (as : List BoundsTy) :
    boundsList rows (TypeSubstitution.substituteList args as) =
      TypeSubstitution.substituteList (fun i => bounds rows (args i)) (boundsList rows as) := by
  cases as with
  | nil => rfl
  | cons a as => simp only [boundsList, TypeSubstitution.substituteList,
      instantiate_commute rows args a, list_instantiate_commute rows args as]
termination_by sizeOf as
end

theorem instance_mapped (rows : Bindings) (s : SchemeTyping.Scheme) (args : List BoundsTy) :
    bounds rows (s.instantiate args) = (mapScheme rows s).instantiate (args.map (bounds rows)) := by
  simp only [Scheme.instantiate, instantiate_commute, mapScheme]
  congr 1
  funext i
  exact (vector_mapped rows args i).symm

theorem ground_fixed (rows : Bindings) {c : Count} (h : c.Ground) : count rows c = c := by
  induction h <;> simp_all [count]

theorem annotation_fixed (rows : Bindings) {τ β} (h : Typed.annotation τ = .ok β) :
    bounds rows β = β := by
  induction τ using Ty.rec_strong generalizing β with
  | prim p => simp [Typed.annotation, pure, Except.pure] at h; subst β; rfl
  | fvar i => simp [Typed.annotation, pure, Except.pure] at h; subst β; rfl
  | bvar i => simp [Typed.annotation, pure, Except.pure] at h; subst β; rfl
  | arrow a b iha ihb =>
      cases ha : Typed.annotation a <;> cases hb : Typed.annotation b <;>
        simp [Typed.annotation, ha, hb, bind, pure, Except.bind, Except.pure] at h
      subst β
      simp only [bounds, iha ha, ihb hb]
  | bl lo hi a ih =>
      cases lo <;> cases hi <;> simp only [Typed.annotation, throw, reduceCtorEq] at h
      split at h
      · rename_i hg
        have hg' := (Bool.and_eq_true _ _).mp hg
        cases ha : Typed.annotation a <;> simp [ha, bind, pure, Except.bind, Except.pure] at h
        subst β
        simp only [bounds, ih ha, ground_fixed rows (Count.ground_of_isGround hg'.1),
          ground_fixed rows (Count.ground_of_isGround hg'.2)]
      · simp [bind, Except.bind] at h
  | customTy n as ih =>
      cases as with
      | nil => simp [Typed.annotation, pure, Except.pure] at h; subst β; rfl
      | cons a as =>
          cases as with
          | cons b bs => simp [Typed.annotation, throw] at h
          | nil =>
              simp only [Typed.annotation] at h
              split at h
              · cases ha : Typed.annotation a <;> simp [ha, bind, pure, Except.bind, Except.pure] at h
                subst β
                exact congrArg (BoundsTy.list (.lit 0) .inf) (ih a (by simp) ha)
              · simp [throw] at h

theorem param (rows : Bindings) (hf : Finite rows) {Δ ann β} (h : Typed.ParamOK Δ ann β) :
    Typed.ParamOK (Δ.map (constraint rows)) ann (bounds rows β) := by
  cases ann with
  | none => trivial
  | some τ =>
      obtain ⟨demand, hd, hs⟩ := h
      exact ⟨demand, hd, by simpa only [annotation_fixed rows hd] using subtype rows hf hs⟩

theorem binding (rows : Bindings) (hf : Finite rows) {Δ ann β} (h : Typed.BindingOK Δ ann β) :
    Typed.BindingOK (Δ.map (constraint rows)) ann (bounds rows β) := by
  cases ann with
  | none => trivial
  | some σ => exact ⟨h.1, param rows hf (ann := some σ.body) h.2⟩

private def frontier (ids : List Nat) : Nat := ids.foldr max 0 + 1

private theorem below_frontier {i ids} (hi : i ∈ ids) : i < frontier ids := by
  have le : i ≤ ids.foldr max 0 := by
    induction ids with
    | nil => simp at hi
    | cons j ids ih =>
        rcases List.mem_cons.mp hi with rfl | hi
        · exact le_max_left _ _
        · exact le_trans (ih hi) (le_max_right _ _)
  simp only [frontier]
  omega

def At (e : Expr) : Prop :=
  ∀ (rows : Bindings), Finite rows → ∀ Δ env β, Derives Δ env e β →
    Derives (Δ.map (constraint rows)) (env.map (mapBinding rows)) e (bounds rows β)

theorem universal_from {Δ env rhs s} (ih : At rhs) (rows : Bindings) (hf : Finite rows)
    (hall : ∀ args, s.Arguments args → Derives Δ env rhs (s.instantiate args)) :
    ∀ args, (mapScheme rows s).Arguments args →
      Derives (Δ.map (constraint rows)) (env.map (mapBinding rows)) rhs
        ((mapScheme rows s).instantiate args) := by
  intro args ha
  let changed := env.map (mapBinding rows)
  let target := mapScheme rows s
  let support := SchemeTransport.captures changed ++
    (Synth.BoundsTy.toTy target.body).freeVars ++ rhs.tyFreeVars
  let n := frontier support
  have newEnv : ∀ i ∈ SchemeTransport.captures changed, i < n :=
    fun i hi => below_frontier (by simp [support, hi])
  have newBody : ∀ i ∈ (Synth.BoundsTy.toTy target.body).freeVars, i < n :=
    fun i hi => below_frontier (by simp [support, hi])
  have source : ∀ i ∈ rhs.tyFreeVars, i < n :=
    fun i hi => below_frontier (by simp [support, hi])
  let fresh := (freshVars n s.hm.paramCount).map BoundsTy.fvar
  have freshFixed : fresh.map (bounds rows) = fresh := by simp [fresh, List.map_map, bounds]
  have first := ih rows hf Δ env (s.instantiate fresh) (hall fresh (SchemeTransport.fresh_arguments s n))
  rw [instance_mapped, freshFixed] at first
  let g := SchemeTransport.replaceBlock args n s.hm.paramCount
  have hg := SchemeTransport.block_lc ha n s.hm.paramCount
  have gEnv : changed.map (SchemeTransport.mapBinding g hg) = changed := by
    apply SchemeTransport.env_fixed
    intro i hi
    exact SchemeTransport.block_below (newEnv i hi)
  have gScheme : SchemeTransport.mapScheme g hg target = target := by
    apply SchemeTransport.scheme_fixed
    intro i hi
    exact SchemeTransport.block_below (newBody i hi)
  have gSource : ∀ i ∈ rhs.tyFreeVars, g i = .fvar i := by
    intro i hi
    exact SchemeTransport.block_below (source i hi)
  have gArgs : fresh.map (SchemeSpecialization.mapFree g) = args :=
    SchemeTransport.recovered_arguments ha n
  have second := SchemeTransport.transport g hg first gSource
  rw [SchemeTransport.instance_mapped g hg, gScheme, gArgs, gEnv] at second
  exact second

theorem transport (rows : Bindings) (hf : Finite rows) {Δ env e β} (h : Derives Δ env e β) :
    Derives (Δ.map (constraint rows)) (env.map (mapBinding rows)) e (bounds rows β) := by
  cases h with
  | literal => cases ‹PrimLitExpr› <;> exact .literal
  | primBinOp => cases ‹PrimBinOp› <;> exact .primBinOp
  | nil => exact .nil
  | cons hh ht hs => exact .cons (transport rows hf hh) (transport rows hf ht) (subtype rows hf hs)
  | varMono hv => exact .varMono (by simpa using congrArg (Option.map (mapBinding rows)) hv)
  | @varPoly env i s args hv ha =>
      rw [instance_mapped]
      exact .varPoly (by simpa using congrArg (Option.map (mapBinding rows)) hv) (arguments_mapped rows ha)
  | app hh ht hs => exact .app (transport rows hf hh) (transport rows hf ht) (subtype rows hf hs)
  | lambda hp hb => exact .lambda (param rows hf hp) (transport rows hf hb)
  | letMono hp hr hb => exact .letMono (binding rows hf hp) (transport rows hf hr) (transport rows hf hb)
  | letPoly hall hb =>
      exact .letPoly (universal_from (fun rows hf Δ env β h => transport rows hf h) rows hf hall)
        (transport rows hf hb)
termination_by sizeOf e
decreasing_by
  all_goals subst_vars
  all_goals simp_wf
  all_goals omega

#print axioms universal_from
#print axioms transport

theorem param_assuming {Δ Δ' ann β} (h : Typed.ParamOK Δ ann β)
    (hp : (⟨Δ', Δ⟩ : ForallProblem).Valid) : Typed.ParamOK Δ' ann β := by
  cases ann with
  | none => trivial
  | some τ =>
      obtain ⟨demand, hd, hs⟩ := h
      exact ⟨demand, hd, hs.assuming hp⟩

theorem binding_assuming {Δ Δ' ann β} (h : Typed.BindingOK Δ ann β)
    (hp : (⟨Δ', Δ⟩ : ForallProblem).Valid) : Typed.BindingOK Δ' ann β := by
  cases ann with
  | none => trivial
  | some σ => exact ⟨h.1, param_assuming (ann := some σ.body) h.2 hp⟩

/-- Instantiated premises must follow from caller assumptions. They are not
    silently appended as new facts, including inside universal nested RHSs. -/
theorem assuming {Δ Δ' env e β} (h : Derives Δ env e β)
    (hp : (⟨Δ', Δ⟩ : ForallProblem).Valid) : Derives Δ' env e β := by
  induction h with
  | literal => exact .literal
  | primBinOp => exact .primBinOp
  | nil => exact .nil
  | cons _ _ hs ihh iht => exact .cons ihh iht (hs.assuming hp)
  | varMono hv => exact .varMono hv
  | varPoly hv ha => exact .varPoly hv ha
  | app _ _ hs ihh iht => exact .app ihh iht (hs.assuming hp)
  | lambda ha _ ih => exact .lambda (param_assuming ha hp) ih
  | letMono ha _ _ ihr ihb => exact .letMono (binding_assuming ha hp) ihr ihb
  | letPoly _ _ ihr ihb => exact .letPoly ihr ihb

theorem count_fixed (rows : Bindings) {ids c} (h : Scope.CountScoped ids c)
    (hk : ∀ i ∈ ids, lookup rows i = none) : count rows c = c := by
  induction c with
  | lit | inf => rfl
  | var v =>
      cases v with | mk kind i =>
        cases kind with
        | rigid => exact captured_count (hk i h)
        | inferable => rfl
  | add a b ha hb | mul a b ha hb | min a b ha hb | max a b ha hb =>
      simp only [count, ha h.1, hb h.2]
  | pred a ha => simp only [count, ha h]

mutual
theorem bounds_fixed (rows : Bindings) {ids β} (h : ScopedScheme.BoundsScoped ids β)
    (hk : ∀ i ∈ ids, lookup rows i = none) : bounds rows β = β := by
  cases β with
  | prim | fvar | bvar => rfl
  | arrow a b => simp only [bounds, bounds_fixed rows h.1 hk, bounds_fixed rows h.2 hk]
  | list lo hi elem => simp only [bounds, count_fixed rows h.1 hk, count_fixed rows h.2.1 hk,
      bounds_fixed rows h.2.2 hk]
  | custom name as => exact congrArg (BoundsTy.custom name) (list_fixed rows h hk)
termination_by sizeOf β

private theorem list_fixed (rows : Bindings) {ids as}
    (h : ScopedScheme.BoundsListScoped ids as) (hk : ∀ i ∈ ids, lookup rows i = none) :
    boundsList rows as = as := by
  cases as with
  | nil => rfl
  | cons a as => simp only [boundsList, bounds_fixed rows h.1 hk, list_fixed rows h.2 hk]
termination_by sizeOf as
end

def BindingScoped (ids : List Nat) : Binding → Prop
  | .mono β => ScopedScheme.BoundsScoped ids β
  | .poly s => ScopedScheme.BoundsScoped ids s.body

theorem env_fixed (rows : Bindings) {ids : List Nat} {env : List Binding}
    (h : ∀ b ∈ env, BindingScoped ids b) (hk : ∀ i ∈ ids, lookup rows i = none) :
    env.map (mapBinding rows) = env := by
  conv_rhs => rw [← List.map_id env]
  apply List.map_congr_left
  intro b hb
  cases b with
  | mono β => exact congrArg Binding.mono (bounds_fixed rows (h _ hb) hk)
  | poly s =>
      have hs : mapScheme rows s = s := by
        cases s
        simp only [mapScheme, bounds_fixed rows (h _ hb) hk]
      exact congrArg Binding.poly hs

#print axioms assuming
#print axioms env_fixed

end FHM.Bounds.CountTransport
