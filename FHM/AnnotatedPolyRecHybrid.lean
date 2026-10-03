import FHM.AnnotatedPolyRecErasure

/-!
# Mixed annotated/unannotated recursion over an erased runtime

This module is the second formal spike for annotated in-block polymorphism.  The
first spike, `FHM.AnnotatedPolyRecErasure`, proves erasure and recursive-unfolding
preservation when every member has a complete scheme.  Here the proof-only
runtime judgment records a `RecSpec` per member:

* `.poly σ` is available at `σ` while the group is checked and in its body;
* `.mono τ` is available at one shared opening of `τ` inside the group, then at
  `PolyTy.genGroup G τ` in the body; and
* neither the specs nor `G` occur in `RunExpr`.

The initial checkpoint fixes the mixed declarative rule and a concrete witness.
Its next obligation is the mixed recursive-rewrapping/preservation theorem.
-/

namespace AnnotatedPolyRecHybrid

open AnnotatedPolyRecErasure

/-- The proof-only recursive environment at one shared opening of the
unannotated members' generalisation pool. -/
def rhsEnv (env : Env) (specs : List RecSpec) (G Xs : List Nat) : Env :=
  specs.map (RecSpec.rhsEntry G Xs) ++ env

/-- The environment outside the recursive block.  Only here are unannotated
members generalized. -/
def bodyEnv (env : Env) (specs : List RecSpec) (G : List Nat) : Env :=
  specs.map (RecSpec.bodyScheme G) ++ env

/-- Runtime well-formedness deliberately contains no source-annotation
alignment premise: annotations have already erased. -/
structure SpecsWF (bindings : List RunExpr) (specs : List RecSpec)
    (G : List Nat) : Prop where
  length : bindings.length = specs.length
  nodup : G.Nodup
  mono_lc : ∀ τ, .mono τ ∈ specs → τ.IsLC
  poly_wf : ∀ σ, .poly σ ∈ specs → σ.WF

/-- The Damas--Milner half of a mixed group.  All unannotated members share the
same pool opening `G ↦ Xs`, hence remain monomorphic inside the SCC. -/
def MonoChecks (TypeOf : Env → RunExpr → Ty → Prop) (env : Env)
    (bindings : List RunExpr) (specs : List RecSpec) (G avoid : List Nat) : Prop :=
  ∀ Xs, FreshNames avoid G.length Xs →
    ∀ pair ∈ bindings.zip specs, ∀ τ, pair.2 = .mono τ →
      TypeOf (rhsEnv env specs G Xs) pair.1 (Ty.renameG G Xs τ)

/-- The annotation-directed half.  Pool names are chosen first; each annotated
member is then checked at its own rigid opening, whose names must also avoid the
pool opening. -/
def PolyChecks (TypeOf : Env → RunExpr → Ty → Prop) (env : Env)
    (bindings : List RunExpr) (specs : List RecSpec) (G avoid : List Nat) : Prop :=
  ∀ Xs, FreshNames avoid G.length Xs →
    ∀ pair ∈ bindings.zip specs, ∀ σ, pair.2 = .poly σ →
      ∀ Ys, FreshNames (avoid ++ Xs) σ.paramCount Ys →
        TypeOf (rhsEnv env specs G Xs) pair.1 (σ.openVars Ys)

def GeneralisesTo (TypeOf : Env → RunExpr → Ty → Prop) (env : Env)
    (scheme : PolyTy) (rhs : RunExpr) (avoid : List Nat) : Prop :=
  ∀ Xs, FreshNames avoid scheme.paramCount Xs →
    TypeOf env rhs (scheme.openVars Xs)

/-- Typing for erased runtime terms with a mixed proof-only recursive witness. -/
inductive HybridWT : Env → RunExpr → Ty → Prop
  | int : HybridWT env (.int n) (.prim .int)
  | var :
      env[index]? = some scheme →
      InstArgs scheme args →
      HybridWT env (.var index) (scheme.openWith args)
  | lam :
      HybridWT (PolyTy.mkTrivial paramTy :: env) body resultTy →
      HybridWT env (.lam body) (.arrow paramTy resultTy)
  | app :
      HybridWT env fn (.arrow argTy resultTy) →
      HybridWT env arg argTy →
      HybridWT env (.app fn arg) resultTy
  | letIn {scheme : PolyTy} {avoid : List Nat} :
      scheme.WF →
      GeneralisesTo HybridWT env scheme rhs avoid →
      HybridWT (scheme :: env) body resultTy →
      HybridWT env (.letIn rhs body) resultTy
  | letRec {specs : List RecSpec} {G avoid : List Nat} :
      SpecsWF bindings specs G →
      MonoChecks HybridWT env bindings specs G avoid →
      PolyChecks HybridWT env bindings specs G avoid →
      HybridWT (bodyEnv env specs G) body resultTy →
      HybridWT env (.letRec bindings body) resultTy

/-! ## Rewrapping at a fixed shared-pool opening

The first mixed preservation ingredient is the same transport used by the
production metatheory: freeze `G ↦ Xs` into every `.mono` spec, set the new pool
to empty, and re-derive the same runtime group.  At the empty pool its body
environment is definitionally the original RHS environment, while `.poly`
schemes are unchanged. -/

private theorem Ty.IsLC.substFvars_local {pairs : List (Nat × Ty)} {ty : Ty}
    (hpairs : ∀ pair ∈ pairs, pair.2.IsLC) (hty : ty.IsLC) :
    (Ty.substFvars pairs ty).IsLC := by
  induction pairs generalizing ty with
  | nil => exact hty
  | cons pair rest ih =>
      obtain ⟨name, replacement⟩ := pair
      simp only [Ty.substFvars]
      exact ih
        (fun pair hpair => hpairs pair (List.mem_cons_of_mem _ hpair))
        (Ty.IsLC.substFvar (hpairs (name, replacement) List.mem_cons_self) hty)

private theorem Ty.renameG_isLC_local {G Xs : List Nat} {ty : Ty}
    (hty : ty.IsLC) : (Ty.renameG G Xs ty).IsLC := by
  unfold Ty.renameG
  apply Ty.IsLC.substFvars_local
  · intro pair hpair
    obtain ⟨name, _, heq⟩ := List.mem_map.mp (List.of_mem_zip hpair).2
    rw [← heq]
    exact ContainsBvarsUpTo.fvar
  · exact hty

private theorem PolyTy.genGroup_nil_local {ty : Ty} :
    PolyTy.genGroup [] ty = PolyTy.mkTrivial ty := by
  have hclose : Ty.closeOver [] ty = ty :=
    Ty.closeOver_eq_self_of_fresh (by simp)
  simp [PolyTy.genGroup, Ty.genFilter, hclose, PolyTy.mkTrivial]

private theorem map_rhsEntry_openAt (G Xs Zs : List Nat)
    (specs : List RecSpec) :
    (specs.map (RecSpec.openAt G Xs)).map (RecSpec.rhsEntry [] Zs) =
      specs.map (RecSpec.rhsEntry G Xs) := by
  rw [List.map_map]
  apply List.map_congr_left
  intro spec _
  cases spec with
  | mono ty => rfl
  | poly scheme => rfl

private theorem map_bodyScheme_openAt (G Xs : List Nat)
    (specs : List RecSpec) :
    (specs.map (RecSpec.openAt G Xs)).map (RecSpec.bodyScheme []) =
      specs.map (RecSpec.rhsEntry G Xs) := by
  rw [List.map_map]
  apply List.map_congr_left
  intro spec _
  cases spec with
  | mono ty => exact PolyTy.genGroup_nil_local
  | poly scheme => rfl

private theorem mem_zip_map_right {α β γ : Type _} {f : β → γ} :
    ∀ {left : List α} {right : List β} {pair : α × γ},
      pair ∈ left.zip (right.map f) →
      ∃ a b, (a, b) ∈ left.zip right ∧ pair = (a, f b) := by
  intro left
  induction left with
  | nil => intro right pair hpair; simp at hpair
  | cons head tail ih =>
      intro right pair hpair
      cases right with
      | nil => simp at hpair
      | cons rhead rtail =>
          simp only [List.map_cons, List.zip_cons_cons, List.mem_cons] at hpair
          rcases hpair with hpair | hpair
          · exact ⟨head, rhead, by simp, hpair⟩
          · obtain ⟨a, b, hab, heq⟩ := ih hpair
            exact ⟨a, b, by simp [hab], heq⟩

private theorem specs_wf_openAt {bindings : List RunExpr}
    {specs : List RecSpec} {G Xs : List Nat}
    (hwf : SpecsWF bindings specs G) :
    SpecsWF bindings (specs.map (RecSpec.openAt G Xs)) [] := by
  refine ⟨by simpa using hwf.length, by simp, ?_, ?_⟩
  · intro ty hty
    obtain ⟨spec, hspec, heq⟩ := List.mem_map.mp hty
    cases spec with
    | mono original =>
        simp only [RecSpec.openAt, RecSpec.mono.injEq] at heq
        subst ty
        exact Ty.renameG_isLC_local (hwf.mono_lc original hspec)
    | poly scheme => exact RecSpec.noConfusion heq
  · intro scheme hscheme
    obtain ⟨spec, hspec, heq⟩ := List.mem_map.mp hscheme
    cases spec with
    | mono ty => exact RecSpec.noConfusion heq
    | poly original =>
        simp only [RecSpec.openAt, RecSpec.poly.injEq] at heq
        subst scheme
        exact hwf.poly_wf original hspec

/-- Re-wrap a member at one fixed shared-pool opening.  The resulting runtime
term is unchanged; only its derivation carries the transported specs. -/
theorem HybridWT.rec_rewrap_at {env : Env} {bindings : List RunExpr}
    {specs : List RecSpec} {G avoid Xs : List Nat}
    (hwf : SpecsWF bindings specs G)
    (hmono : MonoChecks HybridWT env bindings specs G avoid)
    (hpoly : PolyChecks HybridWT env bindings specs G avoid)
    (hXs : FreshNames avoid G.length Xs)
    {rhs : RunExpr} {ty : Ty}
    (hrhs : HybridWT (rhsEnv env specs G Xs) rhs ty) :
    HybridWT env (.letRec bindings rhs) ty := by
  let openedSpecs := specs.map (RecSpec.openAt G Xs)
  apply HybridWT.letRec (specs := openedSpecs) (G := [])
    (avoid := avoid ++ Xs)
  · exact specs_wf_openAt hwf
  · intro Zs hZs pair hpair openedTy hopened
    have hZsNil : Zs = [] := List.length_eq_zero_iff.mp hZs.length
    subst Zs
    obtain ⟨rhs0, spec0, hold, rfl⟩ := mem_zip_map_right hpair
    cases spec0 with
    | mono original =>
        simp only [RecSpec.openAt, RecSpec.mono.injEq] at hopened
        subst openedTy
        have ht := hmono Xs hXs (rhs0, .mono original) hold original rfl
        have hctx : rhsEnv env openedSpecs [] [] = rhsEnv env specs G Xs := by
          unfold rhsEnv openedSpecs
          rw [map_rhsEntry_openAt]
        rw [hctx]
        simpa [Ty.renameG] using ht
    | poly scheme => exact RecSpec.noConfusion hopened
  · intro Zs hZs pair hpair scheme hopened Ys hYs
    have hZsNil : Zs = [] := List.length_eq_zero_iff.mp hZs.length
    subst Zs
    obtain ⟨rhs0, spec0, hold, rfl⟩ := mem_zip_map_right hpair
    cases spec0 with
    | mono original => exact RecSpec.noConfusion hopened
    | poly original =>
        simp only [RecSpec.openAt, RecSpec.poly.injEq] at hopened
        subst scheme
        have hYs' : FreshNames (avoid ++ Xs) original.paramCount Ys := by
          simpa using hYs
        have ht := hpoly Xs hXs (rhs0, .poly original) hold original rfl Ys hYs'
        have hctx : rhsEnv env openedSpecs [] [] = rhsEnv env specs G Xs := by
          unfold rhsEnv openedSpecs
          rw [map_rhsEntry_openAt]
        rw [hctx]
        exact ht
  · rw [show bodyEnv env openedSpecs [] = rhsEnv env specs G Xs by
      unfold bodyEnv rhsEnv openedSpecs
      rw [map_bodyScheme_openAt]]
    exact hrhs

/-! ## Operational substitution infrastructure

These lemmas are independent of how the mixed group eventually proves that its
wrapped members inhabit their body schemes.  Once such a `HybridHasScheme`
list is available, ordinary de Bruijn substitution is sufficient for unfolding.
-/

def HybridHasScheme (env : Env) (value : RunExpr) (scheme : PolyTy) : Prop :=
  ∀ args, InstArgs scheme args → HybridWT env value (scheme.openWith args)

@[simp] private theorem shiftGroup_eq_map (threshold amount : Nat)
    (bindings : List RunExpr) :
    shiftGroup threshold amount bindings =
      bindings.map (RunExpr.shiftFrom threshold amount) := by
  induction bindings with
  | nil => rfl
  | cons rhs rest ih => simp [shiftGroup]

/-- Inserting an environment segment and shifting free term indices preserves
mixed runtime typing. -/
theorem HybridWT.weakenEnv {envPre envExtra env : Env} {e : RunExpr} {ty : Ty}
    (h : HybridWT (envPre ++ env) e ty) :
    HybridWT (envPre ++ envExtra ++ env)
      (e.shiftFrom envPre.length envExtra.length) ty := by
  suffices H : ∀ {env0 : Env} {e0 : RunExpr} {ty0 : Ty}, HybridWT env0 e0 ty0 →
      ∀ pre : Env, env0 = pre ++ env →
        HybridWT (pre ++ envExtra ++ env)
          (e0.shiftFrom pre.length envExtra.length) ty0 by
    exact H h envPre rfl
  intro env0 e0 ty0 hd
  induction hd with
  | int => intro pre _; exact .int
  | @var env0 index scheme args hlookup hargs =>
      intro pre henv
      rw [henv] at hlookup
      simp only [RunExpr.shiftFrom]
      by_cases hlt : index < pre.length
      · rw [if_pos hlt]
        refine .var ?_ hargs
        rw [List.getElem?_append_left
          (by simp only [List.length_append]; omega : index < (pre ++ envExtra).length),
          List.getElem?_append_left hlt]
        rwa [List.getElem?_append_left hlt] at hlookup
      · rw [if_neg hlt]
        refine .var ?_ hargs
        rw [List.getElem?_append_right
          (by simp only [List.length_append]; omega :
            (pre ++ envExtra).length ≤ index + envExtra.length)]
        rw [show index + envExtra.length - (pre ++ envExtra).length =
              index - pre.length by simp only [List.length_append]; omega]
        rwa [List.getElem?_append_right (by omega)] at hlookup
  | @lam paramTy env0 body resultTy _ ih =>
      intro pre henv
      simp only [RunExpr.shiftFrom]
      have hb := ih (PolyTy.mkTrivial paramTy :: pre) (by rw [henv, List.cons_append])
      simpa only [List.cons_append, List.length_cons] using HybridWT.lam hb
  | app _ _ ihfn iharg =>
      intro pre henv
      exact .app (ihfn pre henv) (iharg pre henv)
  | @letIn env0 rhs body resultTy scheme avoid hwf hgen _ ihgen ihbody =>
      intro pre henv
      simp only [RunExpr.shiftFrom]
      apply HybridWT.letIn (scheme := scheme) (avoid := avoid) hwf
      · intro names hfresh
        exact ihgen names hfresh pre henv
      · have hb := ihbody (scheme :: pre) (by rw [henv, List.cons_append])
        simpa only [List.cons_append, List.length_cons] using hb
  | @letRec recBindings ambient body resultTy specs G avoid hwf hmono hpoly _
      ihmono ihpoly ihbody =>
      intro pre henv
      simp only [RunExpr.shiftFrom, shiftGroup_eq_map]
      have hwf' : SpecsWF
          (recBindings.map
            (RunExpr.shiftFrom (pre.length + recBindings.length) envExtra.length))
          specs G :=
        { hwf with length := by simpa using hwf.length }
      apply HybridWT.letRec (specs := specs) (G := G) (avoid := avoid) hwf'
      · intro Xs hXs pair hpair τ hτ
        rw [List.zip_map_left] at hpair
        obtain ⟨oldPair, holdPair, rfl⟩ := List.mem_map.mp hpair
        have ht := ihmono Xs hXs oldPair holdPair τ hτ
          (specs.map (RecSpec.rhsEntry G Xs) ++ pre) (by
            rw [henv]
            simp only [rhsEnv, List.append_assoc])
        simp only [List.length_append, List.length_map] at ht
        rw [← hwf.length, Nat.add_comm recBindings.length pre.length] at ht
        simpa only [rhsEnv, List.append_assoc] using ht
      · intro Xs hXs pair hpair scheme hscheme Ys hYs
        rw [List.zip_map_left] at hpair
        obtain ⟨oldPair, holdPair, rfl⟩ := List.mem_map.mp hpair
        have ht := ihpoly Xs hXs oldPair holdPair scheme hscheme Ys hYs
          (specs.map (RecSpec.rhsEntry G Xs) ++ pre) (by
            rw [henv]
            simp only [rhsEnv, List.append_assoc])
        simp only [List.length_append, List.length_map] at ht
        rw [← hwf.length, Nat.add_comm recBindings.length pre.length] at ht
        simpa only [rhsEnv, List.append_assoc] using ht
      · have hb := ihbody (specs.map (RecSpec.bodyScheme G) ++ pre) (by
          rw [henv]
          simp only [bodyEnv, List.append_assoc])
        simp only [List.length_append, List.length_map] at hb
        rw [← hwf.length, Nat.add_comm recBindings.length pre.length] at hb
        simpa only [bodyEnv, List.append_assoc] using hb

@[simp] private theorem substGroup_eq_map (depth : Nat) (values : List RunExpr)
    (bindings : List RunExpr) :
    substGroup depth values bindings =
      bindings.map (RunExpr.substN depth values) := by
  induction bindings with
  | nil => rfl
  | cons rhs rest ih => simp [substGroup]

/-- Simultaneous substitution only needs each replacement to inhabit every
instance of the corresponding body scheme. -/
theorem HybridWT.substMany {envPre env : Env} {schemes : List PolyTy}
    {values : List RunExpr} {e : RunExpr} {ty : Ty}
    (hvalues : List.Forall₂ (HybridHasScheme env) values schemes)
    (h : HybridWT (envPre ++ schemes ++ env) e ty) :
    HybridWT (envPre ++ env) (e.substN envPre.length values) ty := by
  have hvaluesLen : values.length = schemes.length := hvalues.length_eq
  suffices H : ∀ {env0 : Env} {e0 : RunExpr} {ty0 : Ty}, HybridWT env0 e0 ty0 →
      ∀ pre : Env, env0 = pre ++ schemes ++ env →
        HybridWT (pre ++ env) (e0.substN pre.length values) ty0 by
    exact H h envPre rfl
  intro env0 e0 ty0 hd
  induction hd with
  | int => intro pre _; exact .int
  | @var env0 index scheme args hlookup hargs =>
      intro pre henv
      rw [henv] at hlookup
      rw [List.append_assoc] at hlookup
      simp only [RunExpr.substN]
      by_cases hlt : index < pre.length
      · rw [if_pos hlt]
        refine .var ?_ hargs
        rw [List.getElem?_append_left hlt]
        rwa [List.getElem?_append_left hlt] at hlookup
      · rw [if_neg hlt]
        by_cases hin : index - pre.length < values.length
        · rw [dif_pos hin]
          have hschemeLt : index - pre.length < schemes.length := by omega
          rw [List.getElem?_append_right (by omega),
            List.getElem?_append_left hschemeLt,
            List.getElem?_eq_getElem hschemeLt, Option.some.injEq] at hlookup
          subst scheme
          have hs : HybridHasScheme env values[index - pre.length]
              schemes[index - pre.length] :=
            (List.forall₂_iff_get.mp hvalues).2 _ hin hschemeLt
          have hv := hs args hargs
          simpa only [List.nil_append] using
            (HybridWT.weakenEnv (envPre := []) (envExtra := pre) hv)
        · rw [dif_neg hin]
          refine .var ?_ hargs
          rw [List.getElem?_append_right (by omega : pre.length ≤ index - values.length)]
          rw [List.getElem?_append_right (by omega),
            List.getElem?_append_right (by omega : schemes.length ≤ index - pre.length)]
            at hlookup
          rw [show index - values.length - pre.length =
              index - pre.length - schemes.length by omega]
          exact hlookup
  | @lam paramTy env0 body resultTy _ ih =>
      intro pre henv
      simp only [RunExpr.substN]
      have hb := ih (PolyTy.mkTrivial paramTy :: pre) (by
        rw [henv]
        simp only [List.cons_append, List.append_assoc])
      simpa only [List.cons_append, List.length_cons] using HybridWT.lam hb
  | app _ _ ihfn iharg =>
      intro pre henv
      exact .app (ihfn pre henv) (iharg pre henv)
  | @letIn env0 rhs body resultTy scheme avoid hwf hgen _ ihgen ihbody =>
      intro pre henv
      simp only [RunExpr.substN]
      apply HybridWT.letIn (scheme := scheme) (avoid := avoid) hwf
      · intro names hfresh
        exact ihgen names hfresh pre henv
      · have hb := ihbody (scheme :: pre) (by
          rw [henv]
          simp only [List.cons_append, List.append_assoc])
        simpa only [List.cons_append, List.length_cons] using hb
  | @letRec recBindings ambient body resultTy specs G avoid hwf hmono hpoly _
      ihmono ihpoly ihbody =>
      intro pre henv
      simp only [RunExpr.substN, substGroup_eq_map]
      have hwf' : SpecsWF
          (recBindings.map
            (RunExpr.substN (pre.length + recBindings.length) values))
          specs G :=
        { hwf with length := by simpa using hwf.length }
      apply HybridWT.letRec (specs := specs) (G := G) (avoid := avoid) hwf'
      · intro Xs hXs pair hpair τ hτ
        rw [List.zip_map_left] at hpair
        obtain ⟨oldPair, holdPair, rfl⟩ := List.mem_map.mp hpair
        have ht := ihmono Xs hXs oldPair holdPair τ hτ
          (specs.map (RecSpec.rhsEntry G Xs) ++ pre) (by
            rw [henv]
            simp only [rhsEnv, List.append_assoc])
        simp only [List.length_append, List.length_map] at ht
        rw [← hwf.length, Nat.add_comm recBindings.length pre.length] at ht
        simpa only [rhsEnv, List.append_assoc] using ht
      · intro Xs hXs pair hpair scheme hscheme Ys hYs
        rw [List.zip_map_left] at hpair
        obtain ⟨oldPair, holdPair, rfl⟩ := List.mem_map.mp hpair
        have ht := ihpoly Xs hXs oldPair holdPair scheme hscheme Ys hYs
          (specs.map (RecSpec.rhsEntry G Xs) ++ pre) (by
            rw [henv]
            simp only [rhsEnv, List.append_assoc])
        simp only [List.length_append, List.length_map] at ht
        rw [← hwf.length, Nat.add_comm recBindings.length pre.length] at ht
        simpa only [rhsEnv, List.append_assoc] using ht
      · have hb := ihbody (specs.map (RecSpec.bodyScheme G) ++ pre) (by
          rw [henv]
          simp only [bodyEnv, List.append_assoc])
        simp only [List.length_append, List.length_map] at hb
        rw [← hwf.length, Nat.add_comm recBindings.length pre.length] at hb
        simpa only [bodyEnv, List.append_assoc] using hb

/-! ## A concrete mixed-group witness -/

/-- The unannotated member's shared monotype, before opening/generalisation. -/
def mixedIdTy : Ty := .arrow (.fvar 0) (.fvar 0)

def mixedSpecs : List RecSpec :=
  [.poly polyConstInt, .mono mixedIdTy]

/-- The annotated member: `forall a. a -> Int`. -/
def mixedPolyRhs : RunExpr := .lam (.int 0)

/-- The unannotated member: ordinary identity, monomorphic inside the group. -/
def mixedMonoRhs : RunExpr := .lam (.var 0)

def mixedBindings : List RunExpr := [mixedPolyRhs, mixedMonoRhs]

/-- Outside the group, the unannotated identity is used at `Int`. -/
def mixedBody : RunExpr := .app (.var 1) (.int 0)

def polyId : PolyTy := ⟨1, .arrow (.bvar 0) (.bvar 0)⟩

theorem mixedId_bodyScheme :
    PolyTy.genGroup [0] mixedIdTy = polyId := by
  simp [PolyTy.genGroup, Ty.genFilter, mixedIdTy, polyId,
    Ty.freeVars, Ty.closeOver]

theorem mixed_specs_wf : SpecsWF mixedBindings mixedSpecs [0] := by
  refine ⟨by simp [mixedBindings, mixedSpecs], by simp, ?_, ?_⟩
  · intro τ hτ
    simp [mixedSpecs] at hτ
    subst τ
    exact .arrow .fvar .fvar
  · intro σ hσ
    simp [mixedSpecs] at hσ
    subst σ
    exact polyConstInt_wf

private theorem singleton_of_fresh_one {avoid names : List Nat}
    (h : FreshNames avoid 1 names) : ∃ x, names = [x] := by
  exact List.length_eq_one_iff.mp h.length

theorem mixed_mono_checks :
    MonoChecks HybridWT [] mixedBindings mixedSpecs [0] [] := by
  intro Xs hXs pair hpair τ hmono
  obtain ⟨X, rfl⟩ := singleton_of_fresh_one hXs
  simp [mixedBindings, mixedSpecs] at hpair
  rcases hpair with hfirst | hsecond
  · subst pair
    simp at hmono
  · subst pair
    simp only [RecSpec.mono.injEq] at hmono
    subst τ
    change HybridWT
      [polyConstInt, PolyTy.mkTrivial (.arrow (.fvar X) (.fvar X))]
      mixedMonoRhs (.arrow (.fvar X) (.fvar X))
    apply HybridWT.lam
    have hx := HybridWT.var
      (env := [PolyTy.mkTrivial (.fvar X), polyConstInt,
        PolyTy.mkTrivial (.arrow (.fvar X) (.fvar X))])
      (index := 0) (scheme := PolyTy.mkTrivial (.fvar X)) (args := [])
      rfl ⟨rfl, by simp⟩
    simpa [PolyTy.openWith, PolyTy.mkTrivial, Ty.openWith,
      Ty.instantiate] using hx

theorem mixed_poly_checks :
    PolyChecks HybridWT [] mixedBindings mixedSpecs [0] [] := by
  intro Xs hXs pair hpair σ hpoly Ys hYs
  obtain ⟨X, rfl⟩ := singleton_of_fresh_one hXs
  simp [mixedBindings, mixedSpecs] at hpair
  rcases hpair with hfirst | hsecond
  · subst pair
    simp only [RecSpec.poly.injEq] at hpoly
    subst σ
    obtain ⟨Y, rfl⟩ := singleton_of_fresh_one hYs
    change HybridWT
      [polyConstInt, PolyTy.mkTrivial (.arrow (.fvar X) (.fvar X))]
      mixedPolyRhs (.arrow (.fvar Y) (.prim .int))
    exact .lam .int
  · subst pair
    simp at hpoly

theorem mixed_body_typed :
    HybridWT (bodyEnv [] mixedSpecs [0]) mixedBody (.prim .int) := by
  rw [show bodyEnv [] mixedSpecs [0] = [polyConstInt, polyId] by
    simp [bodyEnv, mixedSpecs, RecSpec.bodyScheme, mixedId_bodyScheme]]
  apply HybridWT.app (argTy := .prim .int)
  · exact .var (index := 1) (scheme := polyId) (args := [.prim .int]) rfl
      ⟨by simp [polyId], by simp; exact ContainsBvarsUpTo.prim⟩
  · exact .int

/-- The same proof-only recursive group presents its unannotated member as one
monotype inside the SCC and as a generalized scheme in the body. -/
theorem mixed_runtime_typed :
    HybridWT [] (.letRec mixedBindings mixedBody) (.prim .int) := by
  exact .letRec mixed_specs_wf mixed_mono_checks mixed_poly_checks mixed_body_typed

#print axioms mixed_runtime_typed

end AnnotatedPolyRecHybrid
