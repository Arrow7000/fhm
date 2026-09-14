import FHM.Bounds.SchemeTyping

/-! # Capture-safe transport in mixed bounds scheme environments

Nested polymorphic RHSs are reparameterized through a fresh finite HM identity
block. Free identities inserted by the caller are not confused with captured
identities being transported. This module changes no executable HM inference.
-/

namespace FHM.Bounds.SchemeTransport

open SchemeTyping SchemeSpecialization

def mapScheme (f : Nat → BoundsTy) (hf : ∀ i, (Synth.BoundsTy.toTy (f i)).IsLC)
    (s : Scheme) : Scheme :=
  ⟨⟨s.hm.paramCount, Synth.BoundsTy.toTy (mapFree f s.body)⟩, mapFree f s.body,
    by
      change ContainsBvarsUpTo s.hm.paramCount (Synth.BoundsTy.toTy (mapFree f s.body)).eraseBounds
      apply ContainsBvarsUpTo.eraseBounds
      apply FreeAlgebra.bvars f hf
      rw [s.erasedShape]
      exact s.wf,
    rfl⟩

def mapBinding (f : Nat → BoundsTy) (hf : ∀ i, (Synth.BoundsTy.toTy (f i)).IsLC) : Binding → Binding
  | .mono β => .mono (mapFree f β)
  | .poly s => .poly (mapScheme f hf s)

def captured : Binding → List Nat
  | .mono β => (Synth.BoundsTy.toTy β).freeVars
  | .poly s => (Synth.BoundsTy.toTy s.body).freeVars

def captures (env : List Binding) : List Nat := env.flatMap captured

private theorem scheme_ext {s t : Scheme} (hh : s.hm = t.hm) (hb : s.body = t.body) : s = t := by
  cases s
  cases t
  cases hh
  cases hb
  rfl

theorem scheme_congr {f g : Nat → BoundsTy} {hf hg} {s : Scheme}
    (h : ∀ i ∈ (Synth.BoundsTy.toTy s.body).freeVars, f i = g i) :
    mapScheme f hf s = mapScheme g hg s := by
  have hb := FreeAlgebra.congrFree h
  apply scheme_ext
  · exact congrArg (fun b => PolyTy.mk s.hm.paramCount (Synth.BoundsTy.toTy b)) hb
  · exact hb

theorem scheme_fixed {f : Nat → BoundsTy} {hf} {s : Scheme}
    (h : ∀ i ∈ (Synth.BoundsTy.toTy s.body).freeVars, f i = .fvar i) : mapScheme f hf s = s := by
  have hb := SchemeSpecialization.fixed h
  apply scheme_ext
  · change PolyTy.mk s.hm.paramCount (Synth.BoundsTy.toTy (mapFree f s.body)) = s.hm
    rw [hb, s.shape]
  · exact hb

theorem env_congr {f g : Nat → BoundsTy} {hf hg} {env}
    (h : ∀ i ∈ captures env, f i = g i) : env.map (mapBinding f hf) = env.map (mapBinding g hg) := by
  apply List.map_congr_left
  intro b hb
  have hc : ∀ i ∈ captured b, f i = g i := fun i hi =>
    h i (List.mem_flatMap.mpr ⟨b, hb, hi⟩)
  cases b with
  | mono β => exact congrArg Binding.mono (FreeAlgebra.congrFree hc)
  | poly s => exact congrArg Binding.poly (scheme_congr hc)

theorem env_fixed {f : Nat → BoundsTy} {hf} {env}
    (h : ∀ i ∈ captures env, f i = .fvar i) : env.map (mapBinding f hf) = env := by
  conv_rhs => rw [← List.map_id env]
  apply List.map_congr_left
  intro b hb
  have hc : ∀ i ∈ captured b, f i = .fvar i := fun i hi =>
    h i (List.mem_flatMap.mpr ⟨b, hb, hi⟩)
  cases b with
  | mono β => exact congrArg Binding.mono (SchemeSpecialization.fixed hc)
  | poly s => exact congrArg Binding.poly (scheme_fixed hc)

theorem arguments_mapped (f : Nat → BoundsTy) (hf : ∀ i, (Synth.BoundsTy.toTy (f i)).IsLC)
    {s args} (ha : s.Arguments args) : (mapScheme f hf s).Arguments (args.map (mapFree f)) := by
  refine ⟨by simpa only [List.length_map] using ha.1, ?_⟩
  intro t ht
  obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ht
  obtain ⟨a, ha', rfl⟩ := List.mem_map.mp hb
  exact FreeAlgebra.bvars f hf (ha.2 _ (List.mem_map.mpr ⟨a, ha', rfl⟩))

theorem vector_mapped (f : Nat → BoundsTy) (args : List BoundsTy) (i : Nat) :
    SchemeUse.vector (args.map (mapFree f)) i = mapFree f (SchemeUse.vector args i) := by
  cases h : args[i]? <;> simp [SchemeUse.vector, List.getElem?_map, h, mapFree]

theorem instance_mapped (f : Nat → BoundsTy) (hf : ∀ i, (Synth.BoundsTy.toTy (f i)).IsLC)
    (s : Scheme) (args : List BoundsTy) :
    mapFree f (s.instantiate args) = (mapScheme f hf s).instantiate (args.map (mapFree f)) := by
  simp only [Scheme.instantiate, FreeAlgebra.instantiate_commute f hf, mapScheme]
  congr 1
  funext i
  exact (vector_mapped f args i).symm

private def frontier (ids : List Nat) : Nat := ids.foldr max 0 + 1

private theorem below_frontier {i ids} (hi : i ∈ ids) : i < frontier ids := by
  have le : i ≤ ids.foldr max 0 := by
    induction ids with
    | nil => simp at hi
    | cons j ids ih =>
        simp only [List.mem_cons] at hi
        rcases hi with rfl | hi
        · exact le_max_left _ _
        · exact le_trans (ih hi) (le_max_right _ _)
  simp only [frontier]
  omega

def protect (f : Nat → BoundsTy) (n k i : Nat) : BoundsTy :=
  if n ≤ i ∧ i < n + k then .fvar i else f i

def replaceBlock (args : List BoundsTy) (n k i : Nat) : BoundsTy :=
  if n ≤ i ∧ i < n + k then SchemeUse.vector args (i - n) else .fvar i

theorem protect_below {f n k i} (hi : i < n) : protect f n k i = f i := by
  simp [protect, show ¬ (n ≤ i ∧ i < n + k) from by omega]

theorem block_below {args n k i} (hi : i < n) : replaceBlock args n k i = .fvar i := by
  simp [replaceBlock, show ¬ (n ≤ i ∧ i < n + k) from by omega]

theorem protect_lc {f : Nat → BoundsTy} (hf : ∀ i, (Synth.BoundsTy.toTy (f i)).IsLC) (n k) :
    ∀ i, (Synth.BoundsTy.toTy (protect f n k i)).IsLC := by
  intro i
  simp only [protect]
  split
  · simp only [Synth.BoundsTy.toTy]; exact .fvar
  · exact hf i

theorem block_lc {s : Scheme} {args : List BoundsTy} (ha : s.Arguments args) (n k) :
    ∀ i, (Synth.BoundsTy.toTy (replaceBlock args n k i)).IsLC := by
  intro i
  simp only [replaceBlock]
  split
  · cases h : args[i - n]? with
    | none => simp only [SchemeUse.vector, h, Option.getD_none, Synth.BoundsTy.toTy]; exact .prim
    | some a =>
        simp only [SchemeUse.vector, h, Option.getD_some]
        exact ha.2 _ (List.mem_map.mpr ⟨a, List.mem_of_getElem? h, rfl⟩)
  · simp only [Synth.BoundsTy.toTy]; exact .fvar

theorem fresh_arguments (s : Scheme) (n : Nat) : s.Arguments ((freshVars n s.hm.paramCount).map BoundsTy.fvar) := by
  refine ⟨by simp, ?_⟩
  intro t ht
  obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ht
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp hb
  simp only [Synth.BoundsTy.toTy]
  exact .fvar

theorem protected_arguments (f : Nat → BoundsTy) (n k : Nat) :
    ((freshVars n k).map BoundsTy.fvar).map (mapFree (protect f n k)) =
      (freshVars n k).map BoundsTy.fvar := by
  simp only [List.map_map]
  apply List.map_congr_left
  intro i hi
  simp only [Function.comp_apply, mapFree, protect]
  exact if_pos ⟨freshVars_ge i hi, freshVars_lt i hi⟩

theorem recovered_arguments {s : Scheme} {args : List BoundsTy} (ha : s.Arguments args) (n : Nat) :
    ((freshVars n s.hm.paramCount).map BoundsTy.fvar).map (mapFree (replaceBlock args n s.hm.paramCount)) = args := by
  have hlen : args.length = s.hm.paramCount := by simpa only [List.length_map] using ha.1
  apply List.ext_getElem?
  intro i
  by_cases hi : i < s.hm.paramCount
  · have harg : i < args.length := by omega
    have hblock : (freshVars n s.hm.paramCount)[i]? = some (n + i) := by
      simp [freshVars, List.getElem?_map, List.getElem?_range hi]
    simp only [List.getElem?_map, hblock, Option.map_some, mapFree, replaceBlock]
    rw [if_pos (by omega)]
    simp [SchemeUse.vector, List.getElem?_eq_getElem harg]
  · have harg : args.length ≤ i := by omega
    have hblock : (freshVars n s.hm.paramCount)[i]? = none := by
      exact List.getElem?_eq_none (by simp only [freshVars_length]; omega)
    simp only [List.getElem?_map, hblock, Option.map_none, List.getElem?_eq_none harg]

/-- Transport at a fixed source term. Term-size recursion permits two freshening
    transports of one RHS without circular induction on a universal derivation. -/
def At (Δ : List Constraint) (e : Expr) : Prop :=
  ∀ (f : Nat → BoundsTy) (hf : ∀ i, (Synth.BoundsTy.toTy (f i)).IsLC)
    (env : List Binding) (β : BoundsTy), Derives Δ env e β →
    (∀ i ∈ e.tyFreeVars, f i = .fvar i) →
    Derives Δ (env.map (mapBinding f hf)) e (mapFree f β)

theorem universal_from {Δ env rhs s} (ih : At Δ rhs)
    (f : Nat → BoundsTy) (hf : ∀ i, (Synth.BoundsTy.toTy (f i)).IsLC)
    (hall : ∀ args, s.Arguments args → Derives Δ env rhs (s.instantiate args))
    (hs : ∀ i ∈ rhs.tyFreeVars, f i = .fvar i) :
    ∀ args, (mapScheme f hf s).Arguments args →
      Derives Δ (env.map (mapBinding f hf)) rhs ((mapScheme f hf s).instantiate args) := by
  intro args ha
  let changed := env.map (mapBinding f hf)
  let target := mapScheme f hf s
  let support := captures env ++ (Synth.BoundsTy.toTy s.body).freeVars ++ rhs.tyFreeVars ++
    captures changed ++ (Synth.BoundsTy.toTy target.body).freeVars
  let n := frontier support
  have oldEnv : ∀ i ∈ captures env, i < n := fun i hi => below_frontier (by simp [support, hi])
  have oldBody : ∀ i ∈ (Synth.BoundsTy.toTy s.body).freeVars, i < n :=
    fun i hi => below_frontier (by simp [support, hi])
  have source : ∀ i ∈ rhs.tyFreeVars, i < n := fun i hi => below_frontier (by simp [support, hi])
  have newEnv : ∀ i ∈ captures changed, i < n := fun i hi => below_frontier (by simp [support, hi])
  have newBody : ∀ i ∈ (Synth.BoundsTy.toTy target.body).freeVars, i < n :=
    fun i hi => below_frontier (by simp [support, hi])
  let fresh := (freshVars n s.hm.paramCount).map BoundsTy.fvar
  let p := protect f n s.hm.paramCount
  have hp := protect_lc hf n s.hm.paramCount
  have pEnv : env.map (mapBinding p hp) = changed := by
    apply env_congr
    intro i hi
    exact protect_below (oldEnv i hi)
  have pScheme : mapScheme p hp s = target := by
    apply scheme_congr
    intro i hi
    exact protect_below (oldBody i hi)
  have pSource : ∀ i ∈ rhs.tyFreeVars, p i = .fvar i := by
    intro i hi
    exact (protect_below (source i hi)).trans (hs i hi)
  have pArgs : fresh.map (mapFree p) = fresh := protected_arguments f n s.hm.paramCount
  have first := ih p hp env (s.instantiate fresh) (hall fresh (fresh_arguments s n)) pSource
  rw [instance_mapped p hp, pScheme, pArgs, pEnv] at first
  let g := replaceBlock args n s.hm.paramCount
  have hg := block_lc ha n s.hm.paramCount
  have gEnv : changed.map (mapBinding g hg) = changed := by
    apply env_fixed
    intro i hi
    exact block_below (newEnv i hi)
  have gScheme : mapScheme g hg target = target := by
    apply scheme_fixed
    intro i hi
    exact block_below (newBody i hi)
  have gSource : ∀ i ∈ rhs.tyFreeVars, g i = .fvar i := by
    intro i hi
    exact block_below (source i hi)
  have gArgs : fresh.map (mapFree g) = args := recovered_arguments ha n
  have second := ih g hg changed (target.instantiate fresh) first gSource
  rw [instance_mapped g hg, gScheme, gArgs, gEnv] at second
  exact second

/-- Full free-HM substitution transport, including nested polymorphic lets and
    polymorphic uses in RHSs. Inserted caller arguments are capture-safe. -/
theorem transport (f : Nat → BoundsTy) (hf : ∀ i, (Synth.BoundsTy.toTy (f i)).IsLC)
    {Δ env e β} (h : Derives Δ env e β) (hs : ∀ i ∈ e.tyFreeVars, f i = .fvar i) :
    Derives Δ (env.map (mapBinding f hf)) e (mapFree f β) := by
  cases h with
  | literal => cases ‹PrimLitExpr› <;> exact .literal
  | primBinOp => cases ‹PrimBinOp› <;> exact .primBinOp
  | nil => exact .nil
  | cons hh ht sub =>
      exact .cons (transport f hf hh (fun i hi => hs i (by simp [Expr.tyFreeVars, hi])))
        (transport f hf ht (fun i hi => hs i (by simp [Expr.tyFreeVars, hi]))) (subtype f sub)
  | varMono hv => exact .varMono (by simpa using congrArg (Option.map (mapBinding f hf)) hv)
  | @varPoly env i s args hv ha =>
      rw [instance_mapped f hf]
      exact .varPoly (by simpa using congrArg (Option.map (mapBinding f hf)) hv) (arguments_mapped f hf ha)
  | app hh ht sub =>
      exact .app (transport f hf hh (fun i hi => hs i (by simp [Expr.tyFreeVars, hi])))
        (transport f hf ht (fun i hi => hs i (by simp [Expr.tyFreeVars, hi]))) (subtype f sub)
  | lambda hp hb =>
      exact .lambda (param hp (fun i hi => hs i (List.mem_append_left _ hi)))
        (transport f hf hb (fun i hi => hs i (List.mem_append_right _ hi)))
  | letMono hp hr hb =>
      exact .letMono (binding hp (fun i hi => hs i (List.mem_append_left _ (List.mem_append_left _ hi))))
        (transport f hf hr (fun i hi => hs i (List.mem_append_left _ (List.mem_append_right _ hi))))
        (transport f hf hb (fun i hi => hs i (List.mem_append_right _ hi)))
  | letPoly hall hb =>
      apply Derives.letPoly
      · apply universal_from (fun f hf env β h hs => transport f hf h hs) f hf hall
        intro i hi
        exact hs i (by simp [Expr.tyFreeVars, hi])
      · exact transport f hf hb (fun i hi => hs i (by simp [Expr.tyFreeVars, hi]))
termination_by sizeOf e
decreasing_by
  all_goals subst_vars
  all_goals simp_wf
  all_goals omega

#print axioms universal_from
#print axioms transport

/-- Only free captured identities matter for generalization. HM scheme slots
    stay bound inside their own entries and must not be mistaken for captures. -/
def interface : Binding → Ty
  | .mono β => Synth.BoundsTy.toTy β
  | .poly s => s.hm.body

theorem interface_captured (b : Binding) : (interface b).freeVars = captured b := by
  cases b with
  | mono => rfl
  | poly s => simp only [interface, captured, ← s.shape]

theorem vector_lc {s : Scheme} {args : List BoundsTy} (ha : s.Arguments args) :
    ∀ i, (Synth.BoundsTy.toTy (SchemeUse.vector args i)).IsLC := by
  intro i
  cases h : args[i]? with
  | none => simp only [SchemeUse.vector, h, Option.getD_none, Synth.BoundsTy.toTy]; exact .prim
  | some a =>
      simp only [SchemeUse.vector, h, Option.getD_some]
      exact ha.2 _ (List.mem_map.mpr ⟨a, List.mem_of_getElem? h, rfl⟩)

/-- Artifact-certified RHS generalization in an arbitrary mixed environment,
    including RHSs that use polymorphic bindings or contain polymorphic lets. -/
theorem binder_instances {σ Δ env rhs β}
    (a : BinderBridge.Abstraction σ β
      (env.map interface ++ rhs.tyFreeVars.map Ty.fvar))
    (h : Derives Δ env rhs β) :
    ∀ args, (SchemeTyping.fromBinder a).Arguments args →
      Derives Δ env rhs ((SchemeTyping.fromBinder a).instantiate args) := by
  intro args ha
  let f := argument a.ids (SchemeUse.vector args)
  have hf : ∀ i, (Synth.BoundsTy.toTy (f i)).IsLC := by
    intro i
    simp only [f, argument]
    cases a.ids.idxOf? i with
    | none => simp only [Synth.BoundsTy.toTy]; exact .fvar
    | some k => exact vector_lc ha k
  have keep : ∀ i ∉ a.ids, f i = .fvar i := by
    intro i hi
    simp only [f, argument, List.idxOf?_eq_none_iff.mpr hi]
  have source : ∀ i ∈ rhs.tyFreeVars, f i = .fvar i := by
    intro i hi
    apply keep i
    intro hm
    exact a.fresh i hm (.fvar i)
      (List.mem_append_right _ (List.mem_map.mpr ⟨i, hi, rfl⟩)) (by simp [Ty.freeVars])
  have fixedEnv : env.map (mapBinding f hf) = env := by
    apply env_fixed
    intro i hi
    apply keep i
    intro hm
    obtain ⟨b, hb, hi⟩ := List.mem_flatMap.mp hi
    exact a.fresh i hm (interface b)
      (List.mem_append_left _ (List.mem_map.mpr ⟨b, hb, rfl⟩))
      (by simpa only [interface_captured] using hi)
  have ht := transport f hf h source
  rw [fixedEnv] at ht
  change Derives Δ env rhs
    (TypeSubstitution.substitute (SchemeUse.vector args) (BinderBridge.close a.ids β))
  rw [close_open a.ids _ a.originalLC]
  exact ht

theorem let_fromBinder {σ Δ env rhs body β result}
    (a : BinderBridge.Abstraction σ β
      (env.map interface ++ rhs.tyFreeVars.map Ty.fvar))
    (h : Derives Δ env rhs β)
    (hb : Derives Δ (.poly (SchemeTyping.fromBinder a) :: env) body result) :
    Derives Δ env (.letIn none rhs body) result := .letPoly (binder_instances a h) hb

#print axioms binder_instances
#print axioms let_fromBinder

end FHM.Bounds.SchemeTransport
