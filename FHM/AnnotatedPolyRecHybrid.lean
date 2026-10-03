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

/-! ## Runtime type substitution

This is metatheoretic substitution only: `RunExpr` contains no types.  The
recursive case freshens the shared HM pool before applying the substitution,
while complete schemes are substituted pointwise. -/

private theorem Ty.substFvar_openWith_hybrid {Z : Nat} {U : Ty}
    (hU : U.IsLC) (args : List Ty) (ty : Ty) :
    Ty.substFvar Z U (Ty.openWith args ty) =
      Ty.openWith (args.map (Ty.substFvar Z U)) (Ty.substFvar Z U ty) := by
  induction ty using Ty.rec_strong with
  | prim p => rfl
  | bvar i =>
      simp only [Ty.openWith, Ty.instantiate, Ty.substFvar, List.getElem?_map]
      cases args[i]? <;> rfl
  | fvar n =>
      simp only [Ty.openWith, Ty.instantiate]
      by_cases h : n = Z
      · subst n
        simp only [Ty.substFvar]
        exact (Ty.instantiate_eq_self_of_lc hU).symm
      · simp only [Ty.substFvar, if_neg h, Ty.instantiate]
  | arrow a b iha ihb =>
      simp only [Ty.openWith, Ty.instantiate, Ty.substFvar, Ty.arrow.injEq]
      exact ⟨iha, ihb⟩
  | customTy name tys ih =>
      simp only [Ty.openWith, Ty.instantiate, Ty.substFvar,
        TyList.instantiate_eq_map, TyList.substFvar_eq_map, List.map_map,
        Ty.customTy.injEq, true_and]
      apply List.map_congr_left
      intro t ht
      simpa only [Ty.openWith, Function.comp_apply] using ih t ht

private theorem InstArgs.substFvar_hybrid {scheme : PolyTy} {args : List Ty}
    {Z : Nat} {U : Ty} (hU : U.IsLC) (h : InstArgs scheme args) :
    InstArgs (scheme.substFvar Z U) (args.map (Ty.substFvar Z U)) := by
  constructor
  · simpa [PolyTy.substFvar] using h.1
  · intro arg harg
    obtain ⟨arg0, harg0, rfl⟩ := List.mem_map.mp harg
    exact Ty.IsLC.substFvar hU (h.2 arg0 harg0)

private def substSpecs (Z : Nat) (U : Ty) (G W : List Nat)
    (specs : List RecSpec) : List RecSpec :=
  specs.map (RecSpec.substFreshened Z U G W)

theorem HybridWT.substFvar {env : Env} {e : RunExpr} {ty U : Ty} {Z : Nat}
    (hU : U.IsLC) (h : HybridWT env e ty) :
    HybridWT (env.substFvar Z U) e (Ty.substFvar Z U ty) := by
  induction h with
  | int => exact .int
  | @var env index scheme args hlookup hargs =>
      have hlookup' : (env.substFvar Z U)[index]? =
          some (scheme.substFvar Z U) := by
        simp only [Env.substFvar, List.getElem?_map, hlookup, Option.map_some]
      have hv := HybridWT.var hlookup' (InstArgs.substFvar_hybrid hU hargs)
      simpa [PolyTy.substFvar, PolyTy.openWith,
        Ty.substFvar_openWith_hybrid hU] using hv
  | @lam paramTy env body resultTy _ ih =>
      simpa [Env.substFvar, PolyTy.mkTrivial] using
        (HybridWT.lam (paramTy := Ty.substFvar Z U paramTy) ih)
  | app _ _ ihfn iharg => exact .app ihfn iharg
  | @letIn env rhs body resultTy scheme avoid hwf hgen _ ihgen ihbody =>
      let avoid' := [Z] ++ avoid
      apply HybridWT.letIn (scheme := scheme.substFvar Z U) (avoid := avoid')
      · exact hwf.substFvar hU
      · intro names hfresh
        have hfresh0 : FreshNames avoid scheme.paramCount names := by
          simpa [avoid', PolyTy.substFvar] using FreshNames.of_append_left hfresh
        have hZ : Z ∉ names :=
          FreshNames.not_mem_of_mem_avoid hfresh (by simp [avoid'])
        have hrhs := ihgen names hfresh0
        rw [PolyTy.substFvar_openVars hU hZ]
        exact hrhs
      · simpa [Env.substFvar] using ihbody
  | @letRec bindings env body resultTy specs G avoid hwf hmono hpoly _
      ihmono ihpoly ihbody =>
      obtain ⟨W, hWlen, hWnodup, hWavoid⟩ :=
        exists_fresh_names
          (G ++ [Z] ++ U.freeVars ++ specs.flatMap RecSpec.monoFreeVars)
          G.length
      have hGW : ∀ g ∈ G, g ∉ W := fun g hg hc =>
        hWavoid g hc (by simp [List.mem_append, hg])
      have hZW : Z ∉ W := fun hc =>
        hWavoid Z hc (by simp [List.mem_append])
      have hUW : ∀ u ∈ U.freeVars, u ∉ W := fun u hu hc =>
        hWavoid u hc (by simp [List.mem_append, hu])
      have hWfree : ∀ τ, RecSpec.mono τ ∈ specs →
          ∀ w ∈ W, w ∉ τ.freeVars := by
        intro τ hτ w hw hc
        have hflat : w ∈ specs.flatMap RecSpec.monoFreeVars :=
          List.mem_flatMap.mpr ⟨.mono τ, hτ, hc⟩
        exact hWavoid w hw (by simp [List.mem_append, hflat])
      let specs' := substSpecs Z U G W specs
      let avoid' := [Z] ++ G ++ W ++ avoid
      have hwf' : SpecsWF bindings specs' W := by
        refine ⟨by simpa [specs', substSpecs] using hwf.length, hWnodup, ?_, ?_⟩
        · intro τ' hτ'
          obtain ⟨spec, hspec, heq⟩ := List.mem_map.mp hτ'
          cases spec with
          | mono τ =>
              simp only [RecSpec.substFreshened, RecSpec.mono.injEq] at heq
              subst τ'
              exact Ty.IsLC.substFvar hU
                (Ty.renameG_isLC_local (hwf.mono_lc τ hspec))
          | poly scheme => exact RecSpec.noConfusion heq
        · intro scheme' hscheme'
          obtain ⟨spec, hspec, heq⟩ := List.mem_map.mp hscheme'
          cases spec with
          | mono τ => exact RecSpec.noConfusion heq
          | poly scheme =>
              simp only [RecSpec.substFreshened, RecSpec.poly.injEq] at heq
              subst scheme'
              exact (hwf.poly_wf scheme hspec).substFvar hU
      apply HybridWT.letRec (specs := specs') (G := W) (avoid := avoid') hwf'
      · intro Xs hXs pair hpair τ' hτ'
        have hXlen : Xs.length = G.length := hXs.length.trans hWlen
        have hZXs : Z ∉ Xs :=
          FreshNames.not_mem_of_mem_avoid hXs (by simp [avoid'])
        have hGXs : ∀ g ∈ G, g ∉ Xs := fun g hg hc =>
          hXs.avoid g hc (by simp [avoid', List.mem_append, hg])
        have hWXs : ∀ w ∈ W, w ∉ Xs := fun w hw hc =>
          hXs.avoid w hc (by simp [avoid', List.mem_append, hw])
        have hXs0 : FreshNames avoid G.length Xs := by
          refine ⟨hXlen, hXs.nodup, ?_⟩
          intro x hx ha
          exact hXs.avoid x hx (by simp [avoid', List.mem_append, ha])
        obtain ⟨rhs0, spec0, hold, rfl⟩ := mem_zip_map_right hpair
        cases spec0 with
        | poly scheme => exact RecSpec.noConfusion hτ'
        | mono τ =>
            simp only [RecSpec.substFreshened, RecSpec.mono.injEq] at hτ'
            subst τ'
            have hτmem : RecSpec.mono τ ∈ specs := (List.of_mem_zip hold).2
            have hkey :
                Ty.renameG W Xs (Ty.substFvar Z U (Ty.renameG G W τ)) =
                  Ty.substFvar Z U (Ty.renameG G Xs τ) := by
              rw [Ty.renameG_substFvar_comm hU hZW hUW hZXs
                    (Ty.renameG_isLC_local (hwf.mono_lc τ hτmem))
                    hWnodup hXs.length hWXs,
                Ty.renameG_renameG (hwf.mono_lc τ hτmem) hwf.nodup hWnodup
                  hWlen hXlen hGW (hWfree τ hτmem) hWXs hGXs]
            have henv : rhsEnv (env.substFvar Z U) specs' W Xs =
                (rhsEnv env specs G Xs).substFvar Z U := by
              unfold rhsEnv specs' substSpecs
              rw [Env.substFvar_append]
              simp only [Env.substFvar, List.map_map]
              congr 1
              apply List.map_congr_left
              intro spec hspec
              cases spec with
              | poly scheme => rfl
              | mono original =>
                  have horig : RecSpec.mono original ∈ specs := hspec
                  have horigKey :
                      Ty.renameG W Xs
                          (Ty.substFvar Z U (Ty.renameG G W original)) =
                        Ty.substFvar Z U (Ty.renameG G Xs original) := by
                    rw [Ty.renameG_substFvar_comm hU hZW hUW hZXs
                          (Ty.renameG_isLC_local (hwf.mono_lc original horig))
                          hWnodup hXs.length hWXs,
                      Ty.renameG_renameG (hwf.mono_lc original horig)
                        hwf.nodup hWnodup hWlen hXlen hGW
                        (hWfree original horig) hWXs hGXs]
                  simp only [Function.comp_apply, RecSpec.substFreshened,
                    RecSpec.rhsEntry, PolyTy.substFvar,
                    PolyTy.mkTrivial]
                  rw [horigKey]
            rw [hkey, henv]
            exact ihmono Xs hXs0 (rhs0, .mono τ) hold τ rfl
      · intro Xs hXs pair hpair scheme' hscheme' Ys hYs
        have hXlen : Xs.length = G.length := hXs.length.trans hWlen
        have hZXs : Z ∉ Xs :=
          FreshNames.not_mem_of_mem_avoid hXs (by simp [avoid'])
        have hGXs : ∀ g ∈ G, g ∉ Xs := fun g hg hc =>
          hXs.avoid g hc (by simp [avoid', List.mem_append, hg])
        have hWXs : ∀ w ∈ W, w ∉ Xs := fun w hw hc =>
          hXs.avoid w hc (by simp [avoid', List.mem_append, hw])
        have hXs0 : FreshNames avoid G.length Xs := by
          refine ⟨hXlen, hXs.nodup, ?_⟩
          intro x hx ha
          exact hXs.avoid x hx (by simp [avoid', List.mem_append, ha])
        obtain ⟨rhs0, spec0, hold, rfl⟩ := mem_zip_map_right hpair
        cases spec0 with
        | mono τ => exact RecSpec.noConfusion hscheme'
        | poly scheme =>
            simp only [RecSpec.substFreshened, RecSpec.poly.injEq] at hscheme'
            subst scheme'
            have hYs0 : FreshNames (avoid ++ Xs) scheme.paramCount Ys := by
              refine ⟨by simpa [PolyTy.substFvar] using hYs.length,
                hYs.nodup, ?_⟩
              intro y hy hmem
              exact hYs.avoid y hy (by
                simp only [avoid', List.append_assoc, List.mem_append,
                  List.mem_cons]
                exact Or.inr (Or.inr (Or.inr (by
                  simpa only [List.mem_append] using hmem))))
            have hZYs : Z ∉ Ys :=
              FreshNames.not_mem_of_mem_avoid hYs (by
                simp [avoid', List.mem_append])
            have henv : rhsEnv (env.substFvar Z U) specs' W Xs =
                (rhsEnv env specs G Xs).substFvar Z U := by
              unfold rhsEnv specs' substSpecs
              rw [Env.substFvar_append]
              simp only [Env.substFvar, List.map_map]
              congr 1
              apply List.map_congr_left
              intro spec hspec
              cases spec with
              | poly original => rfl
              | mono original =>
                  have horig : RecSpec.mono original ∈ specs := hspec
                  have horigKey :
                      Ty.renameG W Xs
                          (Ty.substFvar Z U (Ty.renameG G W original)) =
                        Ty.substFvar Z U (Ty.renameG G Xs original) := by
                    rw [Ty.renameG_substFvar_comm hU hZW hUW hZXs
                          (Ty.renameG_isLC_local (hwf.mono_lc original horig))
                          hWnodup hXs.length hWXs,
                      Ty.renameG_renameG (hwf.mono_lc original horig)
                        hwf.nodup hWnodup hWlen hXlen hGW
                        (hWfree original horig) hWXs hGXs]
                  simp only [Function.comp_apply, RecSpec.substFreshened,
                    RecSpec.rhsEntry, PolyTy.substFvar,
                    PolyTy.mkTrivial]
                  rw [horigKey]
            rw [show (scheme.substFvar Z U).openVars Ys =
                Ty.substFvar Z U (scheme.openVars Ys) by
                  unfold PolyTy.openVars PolyTy.substFvar
                  exact (Ty.substFvar_openVars hU hZYs).symm,
              henv]
            exact ihpoly Xs hXs0 (rhs0, .poly scheme) hold scheme rfl Ys hYs0
      · have henvBody : bodyEnv (env.substFvar Z U) specs' W =
            (bodyEnv env specs G).substFvar Z U := by
          unfold bodyEnv specs' substSpecs
          rw [Env.substFvar_append]
          simp only [Env.substFvar, List.map_map]
          congr 1
          apply List.map_congr_left
          intro spec hspec
          cases spec with
          | poly scheme => rfl
          | mono τ =>
              have hτ : RecSpec.mono τ ∈ specs := hspec
              have hrename := PolyTy.genGroup_renameG
                (hwf.mono_lc τ hτ) hWlen hwf.nodup hWnodup hGW (hWfree τ hτ)
              have hsubst := PolyTy.genGroup_substFvar
                (Z := Z) (U := U) (G := W) (τ := Ty.renameG G W τ) hZW hUW
              simp only [Function.comp_apply, RecSpec.substFreshened,
                RecSpec.bodyScheme]
              rw [← hsubst, ← hrename]
        rw [henvBody]
        exact ihbody

private def substFvarsEnvHybrid : List (Nat × Ty) → Env → Env
  | [], env => env
  | (name, replacement) :: rest, env =>
      substFvarsEnvHybrid rest (env.substFvar name replacement)

private theorem HybridWT.substFvars {env : Env} {e : RunExpr} {ty : Ty}
    {pairs : List (Nat × Ty)}
    (hlc : ∀ pair ∈ pairs, pair.2.IsLC) (h : HybridWT env e ty) :
    HybridWT (substFvarsEnvHybrid pairs env) e (Ty.substFvars pairs ty) := by
  induction pairs generalizing env ty with
  | nil => simpa [substFvarsEnvHybrid, Ty.substFvars] using h
  | cons pair rest ih =>
      obtain ⟨name, replacement⟩ := pair
      simp only [substFvarsEnvHybrid, Ty.substFvars]
      exact ih (fun pair hpair => hlc pair (List.mem_cons_of_mem _ hpair))
        (h.substFvar (hlc (name, replacement) List.mem_cons_self))

private theorem substFvarsEnvHybrid_eq_self_of_fresh
    {pairs : List (Nat × Ty)} {env : Env}
    (hfresh : ∀ pair ∈ pairs, pair.1 ∉ env.freeVars) :
    substFvarsEnvHybrid pairs env = env := by
  induction pairs generalizing env with
  | nil => rfl
  | cons pair rest ih =>
      obtain ⟨name, replacement⟩ := pair
      simp only [substFvarsEnvHybrid]
      rw [Env.substFvar_fresh (hfresh (name, replacement) List.mem_cons_self)]
      exact ih (fun pair hpair => hfresh pair (List.mem_cons_of_mem _ hpair))

private theorem pairs_zip_values_lc_hybrid {names : List Nat} {args : List Ty}
    (hlc : ∀ arg ∈ args, arg.IsLC) :
    ∀ pair ∈ names.zip args, pair.2.IsLC := by
  intro pair hpair
  exact hlc pair.2 (List.of_mem_zip hpair).2

private theorem pairs_zip_names_fresh_hybrid {names : List Nat} {args : List Ty}
    {env : Env} (hfresh : ∀ name ∈ names, name ∉ env.freeVars) :
    ∀ pair ∈ names.zip args, pair.1 ∉ env.freeVars := by
  intro pair hpair
  exact hfresh pair.1 (List.of_mem_zip hpair).1

/-- Replace one fresh rigid opening by an arbitrary concrete scheme instance.
The runtime term is unchanged because types never occur in `RunExpr`. -/
private theorem HybridWT.instantiate_opening {env : Env} {e : RunExpr}
    {scheme : PolyTy} {names : List Nat} {args : List Ty}
    (hargs : InstArgs scheme args)
    (hnamesLen : names.length = scheme.paramCount)
    (hnamesNodup : names.Nodup)
    (hnamesEnv : ∀ x ∈ names, x ∉ env.freeVars)
    (hnamesBody : ∀ x ∈ names, x ∉ scheme.body.freeVars)
    (hnamesArgs : ∀ x ∈ names, x ∉ Ty.freeVarsList args)
    (htyped : HybridWT env e (scheme.openVars names)) :
    HybridWT env e (scheme.openWith args) := by
  have hsub := HybridWT.substFvars (pairs := names.zip args)
    (pairs_zip_values_lc_hybrid (names := names) hargs.2) htyped
  rw [substFvarsEnvHybrid_eq_self_of_fresh
    (pairs_zip_names_fresh_hybrid hnamesEnv)] at hsub
  have hopen := Ty.openWith_eq_substFvars_openVars
    (ty := scheme.body) (Vs := args) (Xs := names)
    (⟨hargs.1.trans hnamesLen.symm, hargs.2⟩ : Ty.AreLC names.length args)
    hnamesNodup hnamesBody hnamesArgs
  simpa [PolyTy.openVars, PolyTy.openWith, hopen] using hsub

/-! ## Operational substitution infrastructure

These lemmas are independent of how the mixed group eventually proves that its
wrapped members inhabit their body schemes.  Once such a `HybridHasScheme`
list is available, ordinary de Bruijn substitution is sufficient for unfolding.
-/

def HybridHasScheme (env : Env) (value : RunExpr) (scheme : PolyTy) : Prop :=
  ∀ args, InstArgs scheme args → HybridWT env value (scheme.openWith args)

/-- A completely annotated recursive member remains polymorphic when the
erased group is wrapped around it. -/
theorem HybridHasScheme.ofPolyRecMember {env : Env}
    {bindings : List RunExpr} {specs : List RecSpec} {G avoid : List Nat}
    (hwf : SpecsWF bindings specs G)
    (hmono : MonoChecks HybridWT env bindings specs G avoid)
    (hpoly : PolyChecks HybridWT env bindings specs G avoid)
    {rhs : RunExpr} {scheme : PolyTy}
    (hmember : (rhs, .poly scheme) ∈ bindings.zip specs) :
    HybridHasScheme env (.letRec bindings rhs) scheme := by
  intro args hargs
  obtain ⟨Xs, hXsLen, hXsNodup, hXsAvoid⟩ :=
    exists_fresh_names avoid G.length
  have hXs : FreshNames avoid G.length Xs :=
    ⟨hXsLen, hXsNodup, hXsAvoid⟩
  obtain ⟨Ys, hYsLen, hYsNodup, hYsAvoid⟩ :=
    exists_fresh_names
      (avoid ++ Xs ++ env.freeVars ++ scheme.body.freeVars ++
        Ty.freeVarsList args)
      scheme.paramCount
  have hYs : FreshNames (avoid ++ Xs) scheme.paramCount Ys :=
    ⟨hYsLen, hYsNodup, fun y hy hmem => hYsAvoid y hy (by
      simp only [List.mem_append]
      rcases List.mem_append.mp hmem with ha | hx
      · exact Or.inl (Or.inl (Or.inl (Or.inl ha)))
      · exact Or.inl (Or.inl (Or.inl (Or.inr hx))))⟩
  have htyped := hpoly Xs hXs (rhs, .poly scheme) hmember scheme rfl Ys hYs
  have hwrapped := HybridWT.rec_rewrap_at hwf hmono hpoly hXs htyped
  apply HybridWT.instantiate_opening hargs hYsLen hYsNodup
    (htyped := hwrapped)
  · intro y hy hmem
    exact hYsAvoid y hy (by simp [List.mem_append, hmem])
  · intro y hy hmem
    exact hYsAvoid y hy (by simp [List.mem_append, hmem])
  · intro y hy hmem
    exact hYsAvoid y hy (by simp [List.mem_append, hmem])

/-- An ordinary HM recursive member is polymorphic only after leaving the
group, at the scheme obtained by generalising its shared monotype. -/
theorem HybridHasScheme.ofMonoRecMember {env : Env}
    {bindings : List RunExpr} {specs : List RecSpec} {G avoid : List Nat}
    (hwf : SpecsWF bindings specs G)
    (hmono : MonoChecks HybridWT env bindings specs G avoid)
    (hpoly : PolyChecks HybridWT env bindings specs G avoid)
    {rhs : RunExpr} {ty : Ty}
    (hmember : (rhs, .mono ty) ∈ bindings.zip specs) :
    HybridHasScheme env (.letRec bindings rhs) (PolyTy.genGroup G ty) := by
  intro args hargs
  have htyLC : ty.IsLC :=
    hwf.mono_lc ty (List.of_mem_zip hmember).2
  obtain ⟨Xs, hXsLen, hXsNodup, hXsAvoid⟩ :=
    exists_fresh_names
      (avoid ++ G ++ ty.freeVars ++ env.freeVars ++ Ty.freeVarsList args ++
        (PolyTy.genGroup G ty).body.freeVars)
      G.length
  have hXs : FreshNames avoid G.length Xs :=
    ⟨hXsLen, hXsNodup, fun x hx hmem =>
      hXsAvoid x hx (by simp [List.mem_append, hmem])⟩
  have hdisj : ∀ g ∈ G, g ∉ Xs := fun g hg hc =>
    hXsAvoid g hc (by simp [List.mem_append, hg])
  have hXsTy : ∀ x ∈ Xs, x ∉ ty.freeVars := fun x hx hc =>
    hXsAvoid x hx (by simp [List.mem_append, hc])
  have hXsEnv : ∀ x ∈ Xs, x ∉ env.freeVars := fun x hx hc =>
    hXsAvoid x hx (by simp [List.mem_append, hc])
  have hXsArgs : ∀ x ∈ Xs, x ∉ Ty.freeVarsList args := fun x hx hc =>
    hXsAvoid x hx (by simp [List.mem_append, hc])
  have hXsBody : ∀ x ∈ Xs,
      x ∉ (PolyTy.genGroup G ty).body.freeVars := fun x hx hc =>
    hXsAvoid x hx (by simp [List.mem_append, hc])
  have htyped := hmono Xs hXs (rhs, .mono ty) hmember ty rfl
  have hwrapped : HybridWT env (.letRec bindings rhs) (Ty.renameG G Xs ty) :=
    HybridWT.rec_rewrap_at hwf hmono hpoly hXs htyped
  set Xs' := Ty.genFilter Xs (Ty.renameG G Xs ty) with hXsDef
  have hXsLen' : Xs'.length = (Ty.genFilter G ty).length := by
    have h := congrArg PolyTy.paramCount
      (PolyTy.genGroup_renameG htyLC hXsLen hwf.nodup hXsNodup
        hdisj hXsTy)
    simp only [PolyTy.genGroup] at h
    rw [hXsDef]
    exact h.symm
  have hXsNodup' : Xs'.Nodup := by
    rw [hXsDef]
    unfold Ty.genFilter
    exact hXsNodup.filter _
  have hGNodup : (Ty.genFilter G ty).Nodup := by
    unfold Ty.genFilter
    exact hwf.nodup.filter _
  have hGDisj : ∀ g ∈ Ty.genFilter G ty, g ∉ Xs' := by
    intro g hg hc
    exact hdisj g (Ty.mem_of_mem_genFilter hg) (by
      rw [hXsDef] at hc
      exact Ty.mem_of_mem_genFilter hc)
  have hrewrite : Ty.renameG G Xs ty =
      Ty.openVars Xs' (Ty.closeOver (Ty.genFilter G ty) ty) := by
    rw [Ty.renameG_eq_genFilter hXsLen hwf.nodup hXsNodup hdisj hXsTy]
    exact (Ty.openVars_closeOver_rename htyLC hGNodup hXsLen' hGDisj).symm
  rw [hrewrite] at hwrapped
  apply HybridWT.instantiate_opening hargs
    (scheme := PolyTy.genGroup G ty) (names := Xs')
    (by simpa [PolyTy.genGroup] using hXsLen') hXsNodup'
    (htyped := by simpa [PolyTy.genGroup, PolyTy.openVars] using hwrapped)
  · intro x hx
    apply hXsEnv x
    rw [hXsDef] at hx
    exact Ty.mem_of_mem_genFilter hx
  · intro x hx
    apply hXsBody x
    rw [hXsDef] at hx
    exact Ty.mem_of_mem_genFilter hx
  · intro x hx
    apply hXsArgs x
    rw [hXsDef] at hx
    exact Ty.mem_of_mem_genFilter hx

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

private theorem HybridHasScheme.ofRecMember {env : Env}
    {bindings : List RunExpr} {specs : List RecSpec} {G avoid : List Nat}
    (hwf : SpecsWF bindings specs G)
    (hmono : MonoChecks HybridWT env bindings specs G avoid)
    (hpoly : PolyChecks HybridWT env bindings specs G avoid)
    {rhs : RunExpr} {spec : RecSpec}
    (hmember : (rhs, spec) ∈ bindings.zip specs) :
    HybridHasScheme env (.letRec bindings rhs) (spec.bodyScheme G) := by
  cases spec with
  | mono ty =>
      exact HybridHasScheme.ofMonoRecMember hwf hmono hpoly hmember
  | poly scheme =>
      exact HybridHasScheme.ofPolyRecMember hwf hmono hpoly hmember

/-- Every recursive RHS, wrapped with its own group, inhabits its exported
scheme.  This is exactly the replacement list used by runtime unfolding. -/
private theorem recursiveValuesHaveSchemes {env : Env}
    {bindings : List RunExpr} {specs : List RecSpec} {G avoid : List Nat}
    (hwf : SpecsWF bindings specs G)
    (hmono : MonoChecks HybridWT env bindings specs G avoid)
    (hpoly : PolyChecks HybridWT env bindings specs G avoid) :
    List.Forall₂ (HybridHasScheme env)
      (bindings.map (fun rhs => .letRec bindings rhs))
      (specs.map (RecSpec.bodyScheme G)) := by
  have hall : ∀ pair ∈ bindings.zip specs,
      HybridHasScheme env (.letRec bindings pair.1)
        (pair.2.bodyScheme G) := by
    intro pair hpair
    exact HybridHasScheme.ofRecMember hwf hmono hpoly hpair
  have go : ∀ (bs : List RunExpr) (ss : List RecSpec),
      bs.length = ss.length →
      (∀ pair ∈ bs.zip ss,
        HybridHasScheme env (.letRec bindings pair.1)
          (pair.2.bodyScheme G)) →
      List.Forall₂ (HybridHasScheme env)
        (bs.map (fun rhs => .letRec bindings rhs))
        (ss.map (RecSpec.bodyScheme G)) := by
    intro bs
    induction bs with
    | nil =>
        intro ss hlen _
        cases ss with
        | nil => exact .nil
        | cons _ _ => simp at hlen
    | cons rhs rest ih =>
        intro ss hlen hmembers
        cases ss with
        | nil => simp at hlen
        | cons spec specs =>
            refine .cons
              (hmembers (rhs, spec) (by simp))
              (ih specs (by simpa using hlen) ?_)
            intro pair hpair
            exact hmembers pair (by simp [hpair])
  exact go bindings specs hwf.length hall

/-- Subject reduction for mixed annotated/unannotated recursive unfolding.
The operational semantics remains wholly type-erased; all schemes and the
shared HM pool are recovered from the typing derivation. -/
theorem HybridWT.preservation {env : Env} {e e' : RunExpr} {ty : Ty}
    (htyped : HybridWT env e ty) (hstep : RunStep e e') :
    HybridWT env e' ty := by
  cases hstep with
  | letRecUnfold =>
      cases htyped with
      | letRec hwf hmono hpoly hbody =>
          have hvalues := recursiveValuesHaveSchemes hwf hmono hpoly
          simpa only [bodyEnv, List.nil_append] using
            (HybridWT.substMany (envPre := []) hvalues hbody)

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

/-- The concrete mixed group survives its actual type-free unfolding step. -/
theorem mixed_unfolded_typed :
    HybridWT []
      (mixedBody.substN 0
        (mixedBindings.map (fun rhs => .letRec mixedBindings rhs)))
      (.prim .int) := by
  exact HybridWT.preservation mixed_runtime_typed RunStep.letRecUnfold

#print axioms HybridWT.substFvar
#print axioms HybridHasScheme.ofPolyRecMember
#print axioms HybridHasScheme.ofMonoRecMember
#print axioms HybridWT.substMany
#print axioms HybridWT.preservation
#print axioms mixed_runtime_typed
#print axioms mixed_unfolded_typed

end AnnotatedPolyRecHybrid
