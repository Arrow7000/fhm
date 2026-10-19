import FHM.Elaboration.Worker
import FHM.Elaboration.Properties
import FHM.Elaboration.Close

namespace Elaboration

/-- More-general environment schemes preserve an annotated cofinite RHS check. -/
theorem GeneralisesTo.weaken_annotated {ctx : Ctx} {rhs : Expr} {scheme : PolyTy}
    {avoid : List Nat} {env' : Env} (hwf : scheme.WF)
    (h : GeneralisesTo TypeOfHM ctx (some scheme) rhs scheme avoid)
    (henv : List.Forall₂ PolyTy.Generalizes env' ctx.env) :
    ∃ avoid', GeneralisesTo TypeOfHM { ctx with env := env' } (some scheme) rhs scheme avoid' := by
  have hlet : TypeOfHM ctx (.letIn (some scheme) rhs (.primLit .unit)) (.prim .unit) :=
    .letIn hwf (fun _ heq => Option.some.inj heq) h rfl .primLitUnit
  have hweaken : TypeOfHM { ctx with env := env' } (.letIn (some scheme) rhs (.primLit .unit)) (.prim .unit) := by
    have old : TypeOfHM ⟨ctx.env ++ [], ctx.ctors⟩ (.letIn (some scheme) rhs (.primLit .unit)) (.prim .unit) := by
      simpa only [List.append_nil] using hlet
    simpa only [List.append_nil] using TypeOfHM.weaken_schemes (env := []) henv old
  cases hweaken with
  | letIn _ hpins hgen _ _ =>
    have heq := hpins _ rfl
    subst heq
    exact ⟨_, hgen⟩

/-- Closing a selected monotype can only increase the available instances.
The written prefix and pool need no freshness assumptions for this direction. -/
theorem RecState.exportComponent_entries_generalize {state : RecState}
    {outputs : List (Option Expr)} {facts : List RecFacts} {pool : List Nat}
    (hlen : state.exports.length = state.specs.length)
    (hlc : ∀ spec ∈ state.specs, spec.LC)
    (hclosed : ∀ i ∈ members, state.exports[i]? = some none)
    (hmono : ∀ i ∈ members, ∃ ty, state.specs[i]? = some (.mono ty)) :
    List.Forall₂ PolyTy.Generalizes
      (state.exportComponent members written pool outputs facts).entries state.entries := by
  apply List.forall₂_iff_zip.mpr
  constructor
  · rw [RecState.entries_length _ (by simpa only [RecState.exportComponent, List.length_mapIdx] using hlen),
      RecState.entries_length _ hlen]
    rfl
  · intro newer older hpair
    obtain ⟨i, hget⟩ := List.mem_iff_getElem?.mp hpair
    obtain ⟨hnew, hold⟩ := List.getElem?_zip_eq_some.mp hget
    rw [RecState.entries, List.getElem?_map] at hold
    obtain ⟨⟨spec, exported⟩, hzip, heqOld⟩ := Option.map_eq_some_iff.mp hold
    obtain ⟨hspec, hexport⟩ := List.getElem?_zip_eq_some.mp hzip
    by_cases hi : i ∈ members
    · obtain ⟨ty, hty⟩ := hmono i hi
      have hspecEq : spec = .mono ty := Option.some.inj (hspec.symm.trans hty)
      subst spec
      have he : exported = none := Option.some.inj (hexport.symm.trans (hclosed i hi))
      subst exported
      have hnewExport : (state.exportComponent members written pool outputs facts).exports[i]? =
          some (some (recScheme (written[i]?.getD []) pool ty)) := by
        simp only [RecState.exportComponent, List.getElem?_mapIdx, hclosed i hi, Option.map_some,
          if_pos hi, hty]
        rfl
      have hnewEntry : (state.exportComponent members written pool outputs facts).entries[i]? =
          some (recScheme (written[i]?.getD []) pool ty) := by
        have hz : ((state.exportComponent members written pool outputs facts).specs.zip
            (state.exportComponent members written pool outputs facts).exports)[i]? =
            some (.mono ty, some (recScheme (written[i]?.getD []) pool ty)) :=
          List.getElem?_zip_eq_some.mpr ⟨hspec, hnewExport⟩
        rw [RecState.entries, List.getElem?_map, hz]
        rfl
      have heqNew : newer = recScheme (written[i]?.getD []) pool ty := Option.some.inj (hnew.symm.trans hnewEntry)
      change PolyTy.mkTrivial ty = older at heqOld
      rw [heqNew, ← heqOld]
      exact recScheme_generalizes_mono (hlc _ (List.mem_of_getElem? hspec))
    · have hnewExport : (state.exportComponent members written pool outputs facts).exports[i]? = some exported := by
        simp only [RecState.exportComponent, List.getElem?_mapIdx, hexport, Option.map_some, if_neg hi]
      have hnewEntry : (state.exportComponent members written pool outputs facts).entries[i]? = some older := by
        have hz : ((state.exportComponent members written pool outputs facts).specs.zip
            (state.exportComponent members written pool outputs facts).exports)[i]? = some (spec, exported) :=
          List.getElem?_zip_eq_some.mpr ⟨hspec, hnewExport⟩
        rw [RecState.entries, List.getElem?_map, hz]
        exact congrArg some heqOld
      have heqNew : newer = older := Option.some.inj (hnew.symm.trans hnewEntry)
      rw [heqNew]
      exact PolyTy.Generalizes.refl older


/-- Completed RHSs are stored under their exact exported scheme and the
current full recursive environment. Metadata is intentionally absent. -/
def RecState.SourceTyped (ctx : Ctx) (state : RecState) : Prop :=
  ∀ (i : Nat) (scheme : PolyTy) (output : Expr),
    state.exports[i]? = some (some scheme) → state.outputs[i]? = some (some output) →
    scheme.WF ∧ ∃ L, GeneralisesTo TypeOfHM (state.rhsCtx ctx) (some scheme) output scheme L

 theorem RecState.SourceTyped.init : (RecState.init base anns).SourceTyped ctx := by
  intro i scheme output _ ho
  simp only [RecState.init, List.getElem?_map] at ho
  cases h : anns[i]? <;> simp [h] at ho

 theorem RecState.SourceTyped.onSubst {state : RecState} {ctx : Ctx}
    (h : state.SourceTyped ctx) (S : Subst) (hlc : ∀ p ∈ S, p.2.IsLC) :
    (state.onSubst S).SourceTyped (S.onCtx ctx) := by
  intro i scheme output hs ho
  simp only [RecState.onSubst, List.getElem?_map] at hs ho
  obtain ⟨oldScheme, hscheme, heqScheme⟩ := Option.map_eq_some_iff.mp hs
  obtain ⟨sigma, hsigma, heq⟩ := Option.map_eq_some_iff.mp heqScheme
  cases heq
  obtain ⟨oldOutput, houtput, heqOutput⟩ := Option.map_eq_some_iff.mp ho
  obtain ⟨rhs, hrhs, heq⟩ := Option.map_eq_some_iff.mp heqOutput
  cases heq
  obtain ⟨hwf, L, hgen⟩ := h i sigma rhs (hsigma ▸ hscheme) (hrhs ▸ houtput)
  refine ⟨Subst.onPolyTy_wf hlc hwf, ?_⟩
  simpa only [RecState.rhsCtx_onSubst] using hgen.onSubst_annotated hwf S hlc

 theorem RecState.mem_entries_of_export {state : RecState} {i : Nat} {scheme : PolyTy}
    (hlen : state.exports.length = state.specs.length)
    (hs : state.exports[i]? = some (some scheme)) : scheme ∈ state.entries := by
  have hi : i < state.specs.length := by rw [← hlen]; exact (List.getElem?_eq_some_iff.mp hs).1
  have hz : (state.specs.zip state.exports)[i]? = some (state.specs[i]'hi, some scheme) :=
    List.getElem?_zip_eq_some.mpr ⟨List.getElem?_eq_getElem hi, hs⟩
  apply List.mem_of_getElem? (i := i)
  rw [RecState.entries, List.getElem?_map, hz]
  rfl

 theorem RecState.SourceTyped.setSigned {state : RecState} {ctx : Ctx}
    {member : Nat} {names : List Nat} {scheme : PolyTy} {output : Expr} {facts : RecFacts}
    (h : state.SourceTyped ctx) (hexport : state.exports[member]? = some (some scheme))
    (houtput : member < state.outputs.length) (hwf : scheme.WF)
    (hlen : names.length = scheme.paramCount) (hnd : names.Nodup)
    (hctx : ∀ v ∈ names, v ∉ (state.rhsCtx ctx).env.freeVars)
    (hscheme : ∀ v ∈ names, v ∉ scheme.body.freeVars)
    (htyped : TypeOfHM (state.rhsCtx ctx) output (scheme.openVars names)) :
    (state.setSigned member names output facts).SourceTyped ctx := by
  have hgen := htyped.generaliseAnnotated hnd hctx
  have heq : (⟨names.length, Ty.closeOver names (scheme.openVars names)⟩ : PolyTy) = scheme := by
    cases scheme with
    | mk n body =>
      simp only [PolyTy.openVars] at *
      rw [Ty.closeOver_openVars_self hnd (by simpa only [hlen] using hwf) hscheme]
      simp only [PolyTy.mk.injEq]
      exact ⟨hlen, True.intro⟩
  rw [heq] at hgen
  intro i sigma rhs hs ho
  by_cases hi : member = i
  · subst i
    have he : sigma = scheme := Option.some.inj (Option.some.inj (hs.symm.trans hexport))
    subst sigma
    rw [RecState.setSigned, List.getElem?_set_self houtput] at ho
    cases Option.some.inj (Option.some.inj ho)
    exact ⟨hwf, names, hgen⟩
  · exact h i sigma rhs hs (by simpa only [RecState.setSigned, List.getElem?_set_ne hi] using ho)

 theorem RecState.entries_eq_of_exports {state : RecState} {schemes : List PolyTy}
    (hspecs : state.specs.length = state.exports.length)
    (hexports : state.exports = schemes.map some) : state.entries = schemes := by
  have hlen : state.entries.length = schemes.length := by
    rw [state.entries_length hspecs.symm, hspecs, hexports, List.length_map]
  apply List.ext_getElem?
  intro i
  cases hs : schemes[i]? with
  | none =>
      have hi : schemes.length ≤ i := List.getElem?_eq_none_iff.mp hs
      exact List.getElem?_eq_none_iff.mpr (hlen ▸ hi)
  | some scheme =>
      have hi : i < state.specs.length := by
        have := (List.getElem?_eq_some_iff.mp hs).1
        simpa only [hspecs, hexports, List.length_map] using this
      have hspec := List.getElem?_eq_getElem hi
      have he : state.exports[i]? = some (some scheme) := by
        rw [hexports, List.getElem?_map, hs]; rfl
      have hz : (state.specs.zip state.exports)[i]? = some (state.specs[i]'hi, some scheme) :=
        List.getElem?_zip_eq_some.mpr ⟨hspec, he⟩
      rw [RecState.entries, List.getElem?_map, hz]
      rfl

private theorem collect_annotated_avoids {ctx : Ctx} (pairs : List (Expr × PolyTy))
    (h : ∀ pair ∈ pairs, ∃ L,
      GeneralisesTo TypeOfHM ctx (some pair.2) pair.1 pair.2 L) :
    ∃ L, ∀ pair ∈ pairs, GeneralisesTo TypeOfHM ctx (some pair.2) pair.1 pair.2 L := by
  induction pairs with
  | nil => exact ⟨[], fun _ hm => by cases hm⟩
  | cons pair rest ih =>
    obtain ⟨Lhead, hh⟩ := h pair List.mem_cons_self
    obtain ⟨Ltail, ht⟩ := ih (fun p hp => h p (List.mem_cons_of_mem _ hp))
    refine ⟨Lhead ++ Ltail, ?_⟩
    intro p hp Xs hXs
    rcases List.mem_cons.mp hp with rfl | hp
    · exact hh Xs ⟨hXs.length, hXs.nodup,
        fun x hx hc => hXs.avoid x hx (List.mem_append_left _ hc)⟩
    · exact ht p hp Xs ⟨hXs.length, hXs.nodup,
        fun x hx hc => hXs.avoid x hx (List.mem_append_right _ hc)⟩

/-- Rebuild a completed group using its independently checked exported schemes. -/
 theorem RecState.SourceTyped.letRec {state : RecState} {schemes : List PolyTy} {outputs : List Expr}
    (h : state.SourceTyped ctx) (hexports : state.exports = schemes.map some)
    (houtputs : state.outputs = outputs.map some)
    (hspecs : state.specs.length = state.exports.length)
    (hlength : state.outputs.length = state.exports.length)
    (hbody : TypeOfHM (state.rhsCtx ctx) body ty) :
    TypeOfHM ctx (.letRec (schemes.map some) outputs body) ty := by
  have hlen : outputs.length = schemes.length := by
    simpa only [hexports, houtputs, List.length_map] using hlength
  have hpairs : ∀ p ∈ outputs.zip schemes, p.2.WF ∧ ∃ L,
      GeneralisesTo TypeOfHM (state.rhsCtx ctx) (some p.2) p.1 p.2 L := by
    intro p hp
    obtain ⟨i, hget⟩ := List.mem_iff_getElem?.mp hp
    obtain ⟨ho, hs⟩ := List.getElem?_zip_eq_some.mp hget
    apply h i p.2 p.1
    · rw [hexports, List.getElem?_map, hs]; rfl
    · rw [houtputs, List.getElem?_map, ho]; rfl
  have hwf : ∀ scheme ∈ schemes, scheme.WF := by
    intro scheme hm
    obtain ⟨i, hs⟩ := List.mem_iff_getElem?.mp hm
    have hi : i < outputs.length := by rw [hlen]; exact (List.getElem?_eq_some_iff.mp hs).1
    have ho := List.getElem?_eq_getElem hi
    exact (hpairs (outputs[i]'hi, scheme)
      (List.mem_iff_getElem?.mpr ⟨i, List.getElem?_zip_eq_some.mpr ⟨ho, hs⟩⟩)).1
  obtain ⟨L, hcofinite⟩ := collect_annotated_avoids (outputs.zip schemes) (fun p hp => (hpairs p hp).2)
  have hvalid : RecGroups.ValidResidualGroups (schemes.map some) outputs [] := by
    refine ⟨by simpa only [List.length_map] using hlen.symm, by simp, by simp, by simp, ?_, ?_⟩
    · intro i _
      simp only [List.flatten_nil, List.not_mem_nil, RecGroups.UnsignedAt, List.getElem?_map]
      cases schemes[i]? <;> simp
    · intro stage dependencyStage component dependencyComponent source target rhs hget
      simp at hget
  have hspecwf : RecSpecs.WF (schemes.map some) outputs (schemes.map RecSpec.poly) [] := by
    refine ⟨?_, by simpa only [List.length_map] using hlen, List.nodup_nil, ?_, ?_⟩
    · simp only [List.map_map, Function.comp_def, RecSpec.ann]
    · intro t ht
      obtain ⟨scheme, _, heq⟩ := List.mem_map.mp ht
      cases heq
    · intro scheme hm
      obtain ⟨original, ho, heq⟩ := List.mem_map.mp hm
      have he : original = scheme := RecSpec.poly.inj heq
      subst scheme
      exact hwf original ho
  have hid : schemes.map (fun x => x) = schemes := List.map_id schemes
  refine TypeOfHM.letRec (specs := schemes.map RecSpec.poly) (G := []) (groups := []) (L := L)
    hvalid hspecwf ?_ ?_ ?_ hbody
  · intro stage component hget
    simp at hget
  · intro pair hp scheme heq Ys hYs
    rcases pair with ⟨rhs, spec⟩
    change spec = .poly scheme at heq
    subst spec
    obtain ⟨i, hget⟩ := List.mem_iff_getElem?.mp hp
    obtain ⟨ho, hs⟩ := List.getElem?_zip_eq_some.mp hget
    rw [List.getElem?_map] at hs
    obtain ⟨original, horiginal, heq⟩ := Option.map_eq_some_iff.mp hs
    have he : original = scheme := RecSpec.poly.inj heq
    subst scheme
    have hgen := hcofinite (rhs, original)
      (List.mem_iff_getElem?.mpr ⟨i, List.getElem?_zip_eq_some.mpr ⟨ho, horiginal⟩⟩) Ys hYs
    simpa only [GeneralisesTo, Expr.openBoundTyVars, RecSpecs.bodyCtx, List.map_map,
      Function.comp_def, RecSpec.bodyScheme, hid, RecState.rhsCtx,
      RecState.entries_eq_of_exports hspecs hexports] using hgen
  · simp only [RecSpecs.bodyCtx, List.map_map, Function.comp_def, RecSpec.bodyScheme, hid,
      RecState.rhsCtx, RecState.entries_eq_of_exports hspecs hexports]


 theorem RecState.SourceTyped.exportComponent {state : RecState}
    {outputs : List (Option Expr)} {facts : List RecFacts} {pool : List Nat}
    (h : state.SourceTyped ctx)
    (hexports : state.exports.length = state.outputs.length)
    (hspecs : state.outputs.length = state.specs.length)
    (hlc : ∀ spec ∈ state.specs, spec.LC)
    (hclosed : ∀ i ∈ members, state.exports[i]? = some none)
    (hmono : ∀ i ∈ members, ∃ ty, state.specs[i]? = some (.mono ty))
    (hnd : ∀ i ∈ members, (written[i]?.getD []).Nodup)
    (hsub : ∀ i ∈ members, ∀ v ∈ written[i]?.getD [], v ∈ pool)
    (hpool : pool.Nodup)
    (hfresh : ∀ v ∈ pool, v ∉ ((state.exportComponent members written pool outputs facts).rhsCtx ctx).env.freeVars)
    (htyped : ∀ (i : Nat) (ty : Ty) (output : Expr), state.specs[i]? = some (.mono ty) →
      outputs[i]? = some (some output) → TypeOfHM (state.rhsCtx ctx) output ty) :
    (state.exportComponent members written pool outputs facts).SourceTyped ctx := by
  have hgeneral := RecState.exportComponent_entries_generalize
    (written := written) (outputs := outputs) (facts := facts) (pool := pool)
    (hexports.trans hspecs) hlc hclosed hmono
  intro i scheme output hscheme houtput
  rw [RecState.exportComponent, List.getElem?_mapIdx] at hscheme houtput
  obtain ⟨oldScheme, hOldScheme, hNewScheme⟩ := Option.map_eq_some_iff.mp hscheme
  obtain ⟨oldOutput, hOldOutput, hNewOutput⟩ := Option.map_eq_some_iff.mp houtput
  by_cases hi : i ∈ members
  · obtain ⟨ty, hty⟩ := hmono i hi
    simp only [if_pos hi] at hNewScheme hNewOutput
    have heq : recScheme (written[i]?.getD []) pool ty = scheme := by
      simpa [hty] using hNewScheme
    subst scheme
    rw [hty] at hNewOutput
    obtain ⟨spec, hspec, hbind⟩ := Option.bind_eq_some_iff.mp hNewOutput
    cases Option.some.inj hspec
    obtain ⟨target, htarget, hbind⟩ := Option.bind_eq_some_iff.mp hbind
    cases Option.some.inj htarget
    obtain ⟨rhs, hrhs, hclose⟩ := Option.bind_eq_some_iff.mp hbind
    obtain ⟨inner, hinner, hinnerEq⟩ := Option.bind_eq_some_iff.mp hrhs
    cases hinnerEq
    cases Option.some.inj hclose
    have hchecked := htyped i ty rhs hty hinner
    have hweaken : TypeOfHM ((state.exportComponent members written pool outputs facts).rhsCtx ctx) rhs ty :=
      TypeOfHM.weaken_schemes hgeneral hchecked
    have hnames : (recNames (written[i]?.getD []) pool ty).Nodup := recNames_nodup (hnd i hi) hpool
    have havoid : ∀ v ∈ recNames (written[i]?.getD []) pool ty,
        v ∉ ((state.exportComponent members written pool outputs facts).rhsCtx ctx).env.freeVars := by
      intro v hv
      apply hfresh v
      rcases mem_recNames.mp hv with hv | ⟨hv, _, _⟩
      · exact hsub i hi v hv
      · exact hv
    exact ⟨recScheme_wf (hlc _ (List.mem_of_getElem? hty)), _, hweaken.generaliseAnnotated hnames havoid⟩
  · simp only [if_neg hi] at hNewScheme hNewOutput
    obtain ⟨hwf, L, hgen⟩ := h i scheme output (hNewScheme ▸ hOldScheme) (hNewOutput ▸ hOldOutput)
    refine ⟨hwf, ?_⟩
    have houter : List.Forall₂ PolyTy.Generalizes ctx.env ctx.env := by
      induction ctx.env with
      | nil => exact .nil
      | cons scheme rest ih => exact .cons (PolyTy.Generalizes.refl scheme) ih
    have happend : ∀ {new old : List PolyTy}, List.Forall₂ PolyTy.Generalizes new old →
        List.Forall₂ PolyTy.Generalizes (new ++ ctx.env) (old ++ ctx.env) := by
      intro new old hrel
      induction hrel with
      | nil => exact houter
      | cons head tail ih => exact .cons head ih
    have henv := happend hgeneral
    exact GeneralisesTo.weaken_annotated (ctx := state.rhsCtx ctx) hwf hgen henv


 theorem _root_.InferRecComponent.sourceSound_of_infer
    (h : InferRecComponent K F members index frontier ctx bindings specs next S outputs facts)
    (hInfer : ∀ {κ F' Ψ c e Ψ' T output ty}, e.size ≤ sizeBindings bindings →
      Infer κ F' Ψ c e Ψ' T output ty → CtxWF c → TypeOfHM (T.onCtx c) output ty)
    (hLC : ∀ {κ F' Ψ c e Ψ' T output ty}, e.size ≤ sizeBindings bindings →
      Infer κ F' Ψ c e Ψ' T output ty → CtxWF c → ty.IsLC ∧ ∀ p ∈ T, p.2.IsLC)
    (hctx : CtxWF ctx) (hspec : ∀ spec ∈ specs, spec.LC) :
    ∀ (j : Nat) (target : Ty) (output : Expr), specs[j]? = some (RecSpec.mono target) → outputs[j]? = some (some output) →
      TypeOfHM (S.onCtx ctx) output (S.onTy target) := by
  match h with
  | .nil => intro j target output ht; simp at ht
  | .skipMono _ hr | .skipPoly hr =>
      intro j target output ht ho
      cases j with
      | zero => cases ho
      | succ j =>
          exact hr.sourceSound_of_infer
            (fun he h => hInfer (by simp only [sizeBindings]; omega) h)
            (fun he h => hLC (by simp only [sizeBindings]; omega) h)
            hctx (fun spec hm => hspec spec (List.mem_cons_of_mem _ hm)) j target output ht ho
  | .consSelected _ hi hu hr =>
      expose_names
      obtain ⟨hiTy, hiS⟩ := hLC (by simp only [sizeBindings]; omega) hi hctx
      have huS := hu.unifies.lc hiTy (Subst.onTy_lc hiS (hspec _ List.mem_cons_self))
      have hS12 : ∀ p ∈ s1 ++ s2, p.2.IsLC := fun p hp => (List.mem_append.mp hp).elim (hiS p) (huS p)
      have hrCtx := Subst.onCtx_wf huS (Subst.onCtx_wf hiS hctx)
      have hrSpec : ∀ spec ∈ specs_1.map (RecSpec.onSubstSource (s1 ++ s2)), spec.LC := by
        intro spec hm
        obtain ⟨old, hold, rfl⟩ := List.mem_map.mp hm
        exact RecSpec.lc_onSubstSource hS12 (hspec old (List.mem_cons_of_mem _ hold))
      have hrLC := hr.lc_of_infer
        (fun he h => hLC (by simp only [sizeBindings_map_substTyFvars] at he; simp only [sizeBindings]; omega) h)
        hrCtx hrSpec
      intro j target output ht ho
      cases j with
      | zero =>
        cases Option.some.inj ht
        cases Option.some.inj (Option.some.inj ho)
        have htyped := TypeOfHM.onSubst (s2 ++ s3)
          (fun p hp => (List.mem_append.mp hp).elim (huS p) (hrLC p))
          (hInfer (by simp only [sizeBindings]; omega) hi hctx)
        have heq := hu.unifies.unifies
        change s2.onTy ty = s2.onTy (s1.onTy expected) at heq
        simpa only [Subst.onCtx_append, Subst.onTy_append, heq] using htyped
      | succ j =>
        simp only [List.getElem?_cons_succ] at ht ho
        have htail := hr.sourceSound_of_infer
          (fun he h => hInfer (by simp only [sizeBindings_map_substTyFvars] at he; simp only [sizeBindings]; omega) h)
          (fun he h => hLC (by simp only [sizeBindings_map_substTyFvars] at he; simp only [sizeBindings]; omega) h)
          hrCtx hrSpec j ((s1 ++ s2).onTy target) output
          (by simp only [List.getElem?_map, ht, Option.map_some, RecSpec.onSubstSource]) ho
        simpa only [Subst.onCtx_append, Subst.onTy_append] using htail
 termination_by structural h

 theorem _root_.InferRecSigned.sourceSound_of_infer
    (h : InferRecSigned K F index frontier ctx anns bindings state next S final)
    (hInfer : ∀ {κ F' Ψ c e Ψ' T output ty}, e.size ≤ sizeBindings bindings →
      Infer κ F' Ψ c e Ψ' T output ty → CtxWF c → TypeOfHM (T.onCtx c) output ty)
    (hctx : CtxWF ctx) (hstate : state.LC) (htyped : state.SourceTyped ctx)
    (hlen : state.exports.length = state.specs.length)
    (hout : state.outputs.length = state.exports.length)
    (hcontracts : ∀ (j : Nat) (scheme : PolyTy), anns[j]? = some (.complete scheme) →
      state.exports[index + j]? = some (some scheme)) :
    final.SourceTyped (S.onCtx ctx) := by
  match h with
  | .nil => simpa only [Subst.onCtx_nil] using htyped
  | .skip _ hr =>
    apply hr.sourceSound_of_infer (fun he hi => hInfer (by simp only [sizeBindings]; omega) hi)
      hctx hstate htyped hlen hout
    intro j scheme hs
    have hh := hcontracts (j + 1) scheme (by simpa only [List.getElem?_cons_succ] using hs)
    simpa only [Nat.add_assoc, Nat.add_comm 1 j] using hh
  | .cons hwf _ hi hu hescape hr =>
    expose_names
    have hiCtx := hstate.rhsCtx hctx
    obtain ⟨htLC, hS1⟩ := hi.lc hiCtx
    have hσLC := Subst.onPolyTy_wf hS1 hwf
    have hS2 := hu.unifies.lc htLC (PolyTy.openVars_isLC hσLC (by simp [Subst.onPolyTy]))
    have hS : ∀ p ∈ s1 ++ s2, p.2.IsLC := fun p hp => (List.mem_append.mp hp).elim (hS1 p) (hS2 p)
    have hready := (htyped.onSubst (s1 ++ s2) hS)
    have hex := hcontracts 0 scheme rfl
    simp only [Nat.add_zero] at hex
    have hex' : (state.onSubst (s1 ++ s2)).exports[index]? = some (some ((s1 ++ s2).onPolyTy scheme)) := by
      simp only [RecState.onSubst, List.getElem?_map, hex, Option.map_some]
    have hlen' : (state.onSubst (s1 ++ s2)).exports.length = (state.onSubst (s1 ++ s2)).specs.length := by
      simpa only [RecState.onSubst, List.length_map] using hlen
    have hmember := (state.onSubst (s1 ++ s2)).mem_entries_of_export hlen' hex'
    have hrhs := TypeOfHM.onSubst s2 hS2
      (hInfer (by simp only [Input.size_openTyVars, sizeBindings]; omega) hi hiCtx)
    have heq := hu.unifies.unifies
    have hdom : ∀ p ∈ s2, p.1 ∉ freshVars frontier scheme.paramCount :=
      fun p hp hm => hu.dom_avoids p hp (List.mem_append_right _ hm)
    change s2.onTy ty = s2.onTy (Ty.openVars (freshVars frontier scheme.paramCount) (s1.onPolyTy scheme).body) at heq
    rw [Subst.onTy_openVars hS2 hdom] at heq
    rw [heq] at hrhs
    have hctxFresh : ∀ v ∈ freshVars frontier scheme.paramCount,
        v ∉ ((state.onSubst (s1 ++ s2)).rhsCtx ((s1 ++ s2).onCtx ctx)).env.freeVars :=
      fun v hv hm => hescape v hv (List.mem_append_left _ hm)
    have hschemeFresh : ∀ v ∈ freshVars frontier scheme.paramCount,
        v ∉ ((s1 ++ s2).onPolyTy scheme).body.freeVars := by
      intro v hv hm
      exact hctxFresh v hv (Env.mem_freeVars_iff.mpr ⟨_, List.mem_append_left _ hmember, hm⟩)
    have houtput : index < (state.onSubst (s1 ++ s2)).outputs.length := by
      have hi := (List.getElem?_eq_some_iff.mp hex').1
      simpa only [RecState.onSubst, List.length_map, hout] using hi
    have hclosed := hready.setSigned (facts := bodyFacts.onSubst s2) hex' houtput (Subst.onPolyTy_wf hS hwf)
      (by simp [Subst.onPolyTy]) (freshVars_nodup) hctxFresh hschemeFresh
      (by
        rw [RecState.rhsCtx_onSubst]
        change TypeOfHM ((s1 ++ s2).onCtx (state.rhsCtx ctx)) (output.substTyFvars s2)
          (((s1 ++ s2).onPolyTy scheme).openVars (freshVars frontier scheme.paramCount))
        simpa only [Subst.onCtx_append, Subst.onPolyTy_append, PolyTy.openVars, Subst.onPolyTy, Subst.onTy_append] using hrhs)
    have hfinal := hr.sourceSound_of_infer
      (fun he hj => hInfer (by simp only [sizeBindings_map_substTyFvars] at he; simp only [sizeBindings]; omega) hj)
      (Subst.onCtx_wf hS hctx) ((hstate.onSubst hS).setSigned) hclosed
      (by simpa only [RecState.setSigned, RecState.onSubst, List.length_map] using hlen)
      (by simpa only [RecState.setSigned, RecState.onSubst, List.length_map, List.length_set] using hout)
      (by
        intro j sigma hs
        obtain ⟨ann, ha, heq⟩ := Option.map_eq_some_iff.mp (by simpa only [List.getElem?_map] using hs)
        cases ann with
        | absent | template | partialForall => cases heq
        | complete original =>
          cases LetAnn.complete.inj heq
          have hh := hcontracts (j + 1) original (by simpa only [List.getElem?_cons_succ] using ha)
          simp only [RecState.setSigned, RecState.onSubst, List.getElem?_map, Nat.add_assoc,
            Nat.add_comm 1 j, hh, Option.map_some, Subst.onPolyTy, Subst.onTy])
    simpa only [Subst.onCtx_append] using hfinal
 termination_by structural h


 theorem RecState.Frame.complete_export {state : RecState} {i : Nat} {scheme : PolyTy}
    (h : state.Frame base K F ctx anns done) (ha : anns[i]? = some (.complete scheme)) :
    state.exports[i]? = some (some scheme) := by
  have hi : i < state.specs.length := by rw [h.specs_length]; exact (List.getElem?_eq_some_iff.mp ha).1
  have hs := List.getElem?_eq_getElem hi
  have hm := congrArg (fun xs : List (Option PolyTy) => xs[i]?) h.modes
  dsimp only at hm
  rw [List.getElem?_map, hs, Option.map_some, List.getElem?_map, ha, Option.map_some] at hm
  cases he : state.specs[i]'hi with
  | mono ty => simp only [he, RecSpec.ann, LetAnn.recModeAnn] at hm; cases hm
  | poly sigma =>
    simp only [he, RecSpec.ann, LetAnn.recModeAnn] at hm
    have heq : sigma = scheme := Option.some.inj (Option.some.inj hm)
    subst sigma
    exact h.poly i scheme (he ▸ hs)

 theorem RecState.Frame.mono_at_unsigned {state : RecState} {i : Nat}
    (h : state.Frame base K F ctx anns done)
    (ha : (anns.map LetAnn.recModeAnn)[i]? = some none) :
    ∃ ty, state.specs[i]? = some (.mono ty) := by
  have hi : i < state.specs.length := by
    rw [h.specs_length]
    simpa only [List.length_map] using (List.getElem?_eq_some_iff.mp ha).1
  have hs := List.getElem?_eq_getElem hi
  have hm := congrArg (fun xs : List (Option PolyTy) => xs[i]?) h.modes
  dsimp only at hm
  rw [List.getElem?_map, hs, Option.map_some, ha] at hm
  cases he : state.specs[i]'hi with
  | mono ty => exact ⟨ty, he ▸ hs⟩
  | poly scheme => simp only [he, RecSpec.ann] at hm; cases hm


private theorem RecState.Frame.entry_freeVars_subset {state : RecState} {spec : RecSpec} {scheme : PolyTy} {i : Nat}
    (h : state.Frame base K F ctx anns done) (hs : state.specs[i]? = some spec)
    (he : state.entries[i]? = some scheme) :
    ∀ v ∈ scheme.body.freeVars, v ∈ spec.freeVars := by
  rw [RecState.entries, List.getElem?_map] at he
  obtain ⟨⟨old, exported⟩, hz, hentry⟩ := Option.map_eq_some_iff.mp he
  obtain ⟨hsp, hex⟩ := List.getElem?_zip_eq_some.mp hz
  dsimp only at hsp hex
  have hsame := Option.some.inj (hsp.symm.trans hs)
  change old = spec at hsame
  subst old
  cases spec with
  | poly sigma =>
    have hh := h.poly i sigma hs
    have hh' := Option.some.inj (hex.symm.trans hh)
    subst exported
    cases hentry
    exact fun _ hv => hv
  | mono ty =>
    by_cases hd : i ∈ done
    · obtain ⟨written, _, _, _, _, hx⟩ := if_pos hd ▸ h.mono i ty hs
      have hh := Option.some.inj (hex.symm.trans hx)
      subst exported
      cases hentry
      exact fun _ hv => Ty.freeVars_closeOver_subset hv
    · have hx := if_neg hd ▸ h.mono i ty hs
      have hh := Option.some.inj (hex.symm.trans hx)
      subst exported
      cases hentry
      exact fun _ hv => hv

private theorem RecState.Frame.pending_lookup_other {state : RecState}
    (h : state.Frame base K F ctx anns done)
    (ht : state.specs[member]? = some (.mono ty)) (hm : member ∉ done)
    (hne : i ≠ member) :
    ∀ scheme, (state.rhsCtx ctx).env[i]? = some scheme → base + member ∉ scheme.body.freeVars := by
  intro scheme hlook
  by_cases hi : i < state.entries.length
  · rw [RecState.rhsCtx, List.getElem?_append_left hi] at hlook
    have hispec : i < state.specs.length := by rw [h.specs_length, ← h.entries_length]; exact hi
    have hs := List.getElem?_eq_getElem hispec
    exact fun hv => h.pending.other member ty ht hm i _ hs hne
      (h.entry_freeVars_subset hs hlook _ hv)
  · rw [RecState.rhsCtx, List.getElem?_append_right (by omega)] at hlook
    exact h.pending.env member ty ht hm scheme (List.mem_of_getElem? hlook)

private theorem RecState.Frame.pending_refs {state : RecState} {rhs : Expr}
    (h : state.Frame base K F ctx anns done)
    (ht : state.specs[member]? = some (.mono ty)) (hm : member ∉ done)
    (href : member ∉ rhs.recGroupRefs state.specs.length 0) :
    rhs.ForallOuter (fun i => ∀ M, (state.rhsCtx ctx).env[i]? = some M →
      base + member ∉ M.body.freeVars) 0 := by
  apply Expr.ForallOuter.of_recGroupRefs_with_outer (n := state.specs.length)
  · intro i hi
    exact h.pending_lookup_other ht hm (fun heq => href (heq ▸ hi))
  · intro i hi
    apply h.pending_lookup_other ht hm
    have := (List.getElem?_eq_some_iff.mp ht).1
    omega

private theorem recShapes_selected_avoid {state : RecState}
    (ha : ∀ i ty, i ∈ members → state.specs[i]? = some (.mono ty) → w ∉ ty.freeVars)
    (ho : ∀ opening ∈ openings, ∀ ty, opening.expected = some ty → w ∉ ty.freeVars) :
    ∀ shape ∈ state.shapes members openings, w ∉ shape.1.freeVars ∧
      ∀ ty, shape.2 = some ty → w ∉ ty.freeVars := by
  intro shape hs
  obtain ⟨i, him, heq⟩ := List.mem_filterMap.mp hs
  cases hspec : state.specs[i]? with
  | none => simp [hspec] at heq
  | some spec =>
    cases spec with
    | poly scheme => simp [hspec, RecSpec.monoTy?] at heq
    | mono ty =>
      cases hopen : openings[i]? with
      | none => simp [hspec, RecSpec.monoTy?, hopen] at heq
      | some opening =>
        simp [hspec, RecSpec.monoTy?, hopen] at heq
        subst shape
        exact ⟨ha i ty him hspec, ho opening (List.mem_of_getElem? hopen)⟩

private theorem openRecSources_getElem? {openings : List RecOpening} {bindings : List Input} {i : Nat} {rhs : Input}
    (hlen : openings.length = bindings.length)
    (h : (openRecSources openings bindings)[i]? = some rhs) :
    ∃ old : Input, bindings[i]? = some old ∧ rhs = old.openTyVars ((openings[i]?).getD .empty).written := by
  induction bindings generalizing openings i with
  | nil => cases openings <;> simp_all [openRecSources]
  | cons head rest ih =>
    cases openings with
    | nil => simp at hlen
    | cons opening openings =>
      cases i with
      | zero => exact ⟨head, rfl, (Option.some.inj h).symm⟩
      | succ i =>
        obtain ⟨old, ho, heq⟩ := ih (Nat.succ.inj hlen) h
        exact ⟨old, ho, heq⟩

 theorem recStep_sourceAvoid
    {state : RecState}
    (ho : OpenRecAnns component 0 frontier anns opened openings)
    (hp : CheckRecShapes K ((state.installOpenings component openings).shapes component openings) pre)
    (hc : InferRecComponent K (substSoft pre (F ++ (openings.flatMap RecOpening.written).map Ty.fvar))
      component 0 opened (((state.installOpenings component openings).onSubst pre).rhsCtx (pre.onCtx ctx))
      ((openRecSources openings bindings).map (Input.substTyFvars pre))
      ((state.installOpenings component openings).onSubst pre).specs first current outputs facts)
    (hInfer : ∀ {κ F' Ψ c e Ψ' T output ty}, e.size ≤ sizeBindings bindings →
      Infer κ F' Ψ c e Ψ' T output ty →
      ∀ {w}, w < Ψ →
      e.erase.ForallOuter (fun i => ∀ M, c.env[i]? = some M → w ∉ M.body.freeVars) 0 →
      w ∉ e.rigidVars →
      (∀ p ∈ T, w ∉ p.2.freeVars) ∧ w ∉ ty.freeVars ∧ w ∉ T.map Prod.fst)
    (hw : w < frontier) (hlen : anns.length = bindings.length)
    (hanns : ∀ ann ∈ anns, w ∉ ann.rigidVars)
    (hrhs : ∀ i rhs, i ∈ component → bindings[i]? = some rhs →
      rhs.erase.ForallOuter (fun j => ∀ M, (state.rhsCtx ctx).env[j]? = some M →
        w ∉ M.body.freeVars) 0 ∧ w ∉ rhs.rigidVars)
    (htarget : ∀ i ty, i ∈ component → state.specs[i]? = some (.mono ty) → w ∉ ty.freeVars) :
    (∀ p ∈ pre ++ current, w ∉ p.2.freeVars) ∧ w ∉ (pre ++ current).map Prod.fst := by
  have hpre := hp.sourceAvoid (recShapes_selected_avoid htarget (ho.expected_avoid hw hanns))
  have hn : ∀ opening ∈ openings, w ∉ opening.written := by
    intro opening hm hw'
    have hh := ho.written_range w (List.mem_flatMap.mpr ⟨opening, hm, hw'⟩)
    omega
  have hcomponent := hc.sourceLocality_of_infer
    (fun he hi => hInfer (by simpa only [sizeBindings_map_substTyFvars, sizeBindings_openRecSources] using he) hi)
    (Nat.lt_of_lt_of_le hw ho.frontier_le)
    (by
      intro i rhs hi hget
      obtain ⟨openedRhs, hopen, rfl⟩ := Option.map_eq_some_iff.mp (by simpa only [List.getElem?_map] using hget)
      obtain ⟨old, hold, rfl⟩ := openRecSources_getElem? (ho.length.trans hlen) hopen
      have hhead := hrhs i old (by simpa using hi) hold
      have hnv : w ∉ ((openings[i]?).getD .empty).written := by
        cases hx : openings[i]? with
        | none => simp [RecOpening.empty]
        | some opening => exact hn opening (List.mem_of_getElem? hx)
      refine ⟨?_, Input.avoid_subst hpre.1 (fun hv => (Input.rigidVars_openTyVarsFrom hv).elim hhead.2 hnv)⟩
      have hctxeq : ((state.installOpenings component openings).onSubst pre).rhsCtx (pre.onCtx ctx) =
          pre.onCtx (state.rhsCtx ctx) := by
        rw [RecState.rhsCtx_onSubst]
        rfl
      rw [hctxeq]
      simpa only [Input.erase_substTyFvars, Input.erase_openTyVars] using
        Expr.ForallOuter.lookupAvoid_onSubst (S := pre) hhead.1 hpre.1)
    (by
      intro i ty hi hget
      obtain ⟨old, hold, rfl⟩ := RecSpec.mono_getElem?_map_onSubstSource hget
      exact Subst.notMemOnTy hpre.1 (htarget i old (by simpa using hi) hold))
  exact ⟨fun p hp => (List.mem_append.mp hp).elim (hpre.1 p) (hcomponent.1 p),
    by simpa only [List.map_append, List.mem_append, not_or] using And.intro hpre.2 hcomponent.2⟩

 theorem recStep_oldpool_pending_avoid
    {state : RecState}
    (ho : OpenRecAnns component 0 frontier anns opened openings)
    (hp : CheckRecShapes K ((state.installOpenings component openings).shapes component openings) pre)
    (hc : InferRecComponent K (substSoft pre (F ++ (openings.flatMap RecOpening.written).map Ty.fvar))
      component 0 opened (((state.installOpenings component openings).onSubst pre).rhsCtx (pre.onCtx ctx))
      ((openRecSources openings bindings).map (Input.substTyFvars pre))
      ((state.installOpenings component openings).onSubst pre).specs first current outputs facts)
    (hInfer : ∀ {κ F' Ψ c e Ψ' T output ty}, e.size ≤ sizeBindings bindings →
      Infer κ F' Ψ c e Ψ' T output ty →
      ∀ {w}, w < Ψ →
      e.erase.ForallOuter (fun i => ∀ M, c.env[i]? = some M → w ∉ M.body.freeVars) 0 →
      w ∉ e.rigidVars →
      (∀ p ∈ T, w ∉ p.2.freeVars) ∧ w ∉ ty.freeVars ∧ w ∉ T.map Prod.fst)
    (hvalid : RecGroups.ValidResidualGroups (anns.map LetAnn.recModeAnn) (bindings.map Input.erase)
      (past ++ component :: rest))
    (hframe : state.Frame base K F ctx anns past.flatten)
    (hbelow : state.Below frontier) (hbase : base + bindings.length ≤ frontier)
    (hanns : ∀ ann ∈ anns, ∀ v ∈ ann.rigidVars, v ∈ K ++ softVars F)
    (hrhs : ∀ rhs ∈ bindings, ∀ v ∈ rhs.rigidVars, v ∈ K ++ softVars F) :
    (∀ g ∈ state.pool, (∀ p ∈ pre ++ current, g ∉ p.2.freeVars) ∧ g ∉ (pre ++ current).map Prod.fst) ∧
    (∀ member ty, state.specs[member]? = some (.mono ty) → member ∉ past.flatten ++ component →
      (∀ p ∈ pre ++ current, base + member ∉ p.2.freeVars) ∧ base + member ∉ (pre ++ current).map Prod.fst) := by
  have hlen : anns.length = bindings.length := by simpa only [List.length_map] using hvalid.length
  have hnot : ∀ i ∈ component, i ∉ past.flatten := by
    intro i hi hd
    have hnd : (past.flatten ++ (component ++ rest.flatten)).Nodup := by
      simpa only [List.flatten_append, List.flatten_cons] using hvalid.flatten_nodup
    exact (List.nodup_append.mp hnd).2.2 i hd i (List.mem_append_left _ hi) rfl
  constructor
  · intro g hg
    apply recStep_sourceAvoid ho hp hc hInfer (hbelow.2.2.2 g hg) hlen
    · intro ann ha hv
      exact (List.mem_append.mp (hanns ann ha g hv)).elim (hframe.pool_rigid g hg) (hframe.pool_soft g hg)
    · intro i rhs hi hget
      refine ⟨?_, ?_⟩
      · apply Expr.ForallOuter.of_recGroupRefs_with_outer (n := 0)
        · intro j hj M hm hv
          exact hframe.pool_rhsCtx g hg (Env.mem_freeVars_iff.mpr ⟨M, List.mem_of_getElem? hm, hv⟩)
        · intro j _ M hm hv
          exact hframe.pool_rhsCtx g hg (Env.mem_freeVars_iff.mpr ⟨M, List.mem_of_getElem? hm, hv⟩)
      · intro hv
        exact (List.mem_append.mp (hrhs rhs (List.mem_of_getElem? hget) g hv)).elim
          (hframe.pool_rigid g hg) (hframe.pool_soft g hg)
    · intro i ty hi hget
      rw [hframe.pending.mono i ty hget (hnot i hi)]
      simp only [Ty.freeVars, List.mem_singleton]
      exact fun heq => hframe.pool_pending i ty hget (hnot i hi) (heq ▸ hg)
  · intro member ty ht hm
    have hdone : member ∉ past.flatten := fun hd => hm (List.mem_append_left _ hd)
    have hcomp : member ∉ component := fun hc => hm (List.mem_append_right _ hc)
    have hw : base + member < frontier := by
      have hlt := (List.getElem?_eq_some_iff.mp ht).1
      rw [hframe.specs_length, hlen] at hlt
      omega
    have hrigid : base + member ∉ K := fun hh => by have := hframe.rigid_below _ hh; omega
    have hsoft := hframe.pending_soft member ty ht hdone
    apply recStep_sourceAvoid ho hp hc hInfer hw hlen
    · intro ann ha hv
      exact (List.mem_append.mp (hanns ann ha _ hv)).elim hrigid hsoft
    · intro i rhs hi hget
      refine ⟨?_, fun hv => (List.mem_append.mp (hrhs rhs (List.mem_of_getElem? hget) _ hv)).elim hrigid hsoft⟩
      apply hframe.pending_refs ht hdone
      apply hvalid.pending_no_ref hframe.modes
        (by simpa only [List.length_map] using (hframe.specs_length.trans hlen).symm) hi
        (by simp only [List.getElem?_map, hget, Option.map_some]) ht hm
    · intro i target hi hget
      exact hframe.pending.other member ty ht hdone i (.mono target) hget (fun heq => hcomp (heq ▸ hi))

theorem ResolveRecSlots.lookup
    (h : ResolveRecSlots members forbidden index slots names) :
    ∀ (j : Nat) images, slots[j]? = some images → ∃ ns, names[j]? = some ns ∧
      if index + j ∈ members then ns.map Ty.fvar = images ∧ ns.Nodup ∧
        (∀ v ∈ ns, v ∉ forbidden) else ns = [] := by
  induction h with
  | nil => intro j images hj; simp at hj
  | skip hn hr ih =>
    intro j images hj
    cases j with
    | zero =>
      cases hj
      exact ⟨[], rfl, by simp [hn]⟩
    | succ j =>
      obtain ⟨ns, hget, hh⟩ := ih j images hj
      exact ⟨ns, hget, by simpa only [Nat.succ_add, Nat.add_succ] using hh⟩
  | cons hm hb hnd hav hr ih =>
    intro j images hj
    cases j with
    | zero =>
      cases hj
      exact ⟨_, rfl, by simpa only [Nat.add_zero, hm, ↓reduceIte] using And.intro hb (And.intro hnd hav)⟩
    | succ j =>
      obtain ⟨ns, hget, hh⟩ := ih j images hj
      exact ⟨ns, hget, by simpa only [Nat.succ_add, Nat.add_succ] using hh⟩

theorem ResolveRecSlots.length (h : ResolveRecSlots members forbidden index slots names) :
    names.length = slots.length := by induction h <;> simp_all

private theorem ResolveRecSlots.all_avoid (h : ResolveRecSlots members forbidden index slots names) :
    ∀ v ∈ names.flatten, v ∉ forbidden := by
  induction h with
  | nil => simp
  | skip _ _ ih => exact ih
  | cons _ _ _ ha _ ih =>
    intro v hv
    exact (List.mem_append.mp hv).elim (ha v) (ih v)

private theorem RecState.componentPool_nodup {state : RecState}
    (h : state.pool.Nodup) : (state.componentPool K soft members ctx written).Nodup := by
  apply h.append ((List.nodup_dedup _).filter _)
  intro v hv hother
  exact (of_decide_eq_true (List.mem_filter.mp hother).2) hv

private theorem RecState.componentPool_old {state : RecState} (hv : v ∈ state.pool) :
    v ∈ state.componentPool K soft members ctx written := List.mem_append_left _ hv

private theorem RecState.componentPool_new_avoid {state : RecState}
    (hw : ∀ v ∈ written.flatten, v ∉ (state.fixedCtx ctx).env.freeVars ++ K ++ soft)
    (hv : v ∈ state.componentPool K soft members ctx written) (hold : v ∉ state.pool) :
    v ∉ (state.fixedCtx ctx).env.freeVars ++ K ++ soft := by
  rcases List.mem_append.mp hv with hv | hv
  · exact False.elim (hold hv)
  · have hm := List.mem_dedup.mp (List.mem_filter.mp hv).1
    rcases List.mem_append.mp hm with hm | hm
    · exact hw v hm
    · have hg : v ∈ Ty.freeVarsList (RecSpecs.monoTysAt state.specs members) ∧
          v ∉ (state.fixedCtx ctx).env.freeVars ∧ v ∉ K ++ soft ++ state.pool := by
        simp only [genGroupVars, List.mem_filter, Bool.and_eq_true] at hm
        exact ⟨hm.1, by simpa using hm.2.1, by simpa using hm.2.2⟩
      intro hb
      rcases List.mem_append.mp hb with hb | hb
      · rcases List.mem_append.mp hb with hb | hb
        · exact hg.2.1 hb
        · exact hg.2.2 (List.mem_append_left _ (List.mem_append_left _ hb))
      · exact hg.2.2 (List.mem_append_left _ (List.mem_append_right _ hb))

private theorem Ty.mem_freeVarsList_exists_local {types : List Ty} {g : Nat}
    (h : g ∈ Ty.freeVarsList types) : ∃ t ∈ types, g ∈ t.freeVars := by
  induction types with
  | nil => simp [Ty.freeVarsList] at h
  | cons hd tl ih =>
    simp only [Ty.freeVarsList, List.mem_dedup, List.mem_append] at h
    rcases h with h | h
    · exact ⟨hd, List.mem_cons_self, h⟩
    · obtain ⟨t, ht, hg⟩ := ih h
      exact ⟨t, List.mem_cons_of_mem _ ht, hg⟩

private theorem recScheme_pool_append_eq {writtenPrefix old extra : List Nat} {ty : Ty}
    (ha : ∀ v ∈ extra, v ∉ ty.freeVars) : recScheme writtenPrefix (old ++ extra) ty = recScheme writtenPrefix old ty := by
  have hf : extra.filter (fun v => decide (v ∈ ty.freeVars) && decide (v ∉ writtenPrefix)) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro v hv
    simp [ha v hv]
  simp only [recScheme, recNames, List.filter_append, hf, List.append_nil]

theorem RecState.componentPool_written {state : RecState}
    (hv : v ∈ written.flatten) : v ∈ state.componentPool K soft members ctx written := by
  by_cases hold : v ∈ state.pool
  · exact state.componentPool_old hold
  · exact List.mem_append_right _ (List.mem_filter.mpr
      ⟨List.mem_dedup.mpr (List.mem_append_left _ hv), decide_eq_true hold⟩)

private theorem RecState.recScheme_componentPool_eq {state : RecState} {writtenPrefix : List Nat} {ty : Ty}
    (hlc : ty.IsLC) (hsub : ∀ v ∈ writtenPrefix, v ∈ state.pool)
    (hexport : some (recScheme writtenPrefix state.pool ty) ∈ state.exports)
    (hw : ∀ v ∈ written.flatten, v ∉ (state.fixedCtx ctx).env.freeVars ++ K ++ soft) :
    recScheme writtenPrefix (state.componentPool K soft members ctx written) ty =
      recScheme writtenPrefix state.pool ty := by
  apply recScheme_pool_append_eq
  intro v hv hvty
  have hn : v ∉ state.pool := of_decide_eq_true (List.mem_filter.mp hv).2
  have hnew : v ∈ state.componentPool K soft members ctx written := List.mem_append_right _ hv
  have hav := state.componentPool_new_avoid hw hnew hn
  apply hav
  apply List.mem_append_left
  apply List.mem_append_left
  apply Env.mem_freeVars_iff.mpr
  refine ⟨recScheme writtenPrefix state.pool ty, List.mem_append_left _ ?_, ?_⟩
  · exact List.mem_filterMap.mpr ⟨some _, hexport, rfl⟩
  · apply Ty.mem_closeOver_freeVars_of_notMem_pool hlc hvty
    intro hh
    rcases List.mem_append.mp hh with hh | hh
    · exact hn (hsub v hh)
    · exact hn (List.mem_filter.mp hh).1

private theorem ResolveRecSlots.names_avoid_of_slots
    (h : ResolveRecSlots members forbidden index slots names)
    (hs : ∀ (i : Nat) images, index + i ∈ members → slots[i]? = some images →
      ∀ ty ∈ images, w ∉ ty.freeVars) : w ∉ names.flatten := by
  induction h with
  | nil => simp
  | skip _ _ ih =>
    apply ih
    intro i images hi hget
    exact hs (i + 1) images (by simpa [Nat.add_assoc, Nat.add_comm 1 i] using hi) hget
  | cons hm hb _ _ _ ih =>
    intro hv
    rcases List.mem_append.mp hv with hv | hv
    · apply hs 0 _ (by simpa using hm) rfl (.fvar w)
        (hb ▸ List.mem_map.mpr ⟨w, hv, rfl⟩)
      simp [Ty.freeVars]
    · exact ih (fun i images hi hget => hs (i + 1) images
        (by simpa [Nat.add_assoc, Nat.add_comm 1 i] using hi) hget) hv

 theorem RecState.Frame.exportComponent_onSubst {state : RecState} {S : Subst}
    {written : List (List Nat)} {outputs : List (Option Expr)} {facts : List RecFacts}
    (h : state.Frame base K F ctx anns done) (hlc : state.LC) (hS : ∀ p ∈ S, p.2.IsLC)
    (hpool : ∀ g ∈ state.pool, (∀ p ∈ S, g ∉ p.2.freeVars) ∧ g ∉ S.map Prod.fst)
    (hpending : ∀ i ty, state.specs[i]? = some (.mono ty) → i ∉ done ++ members →
      (∀ p ∈ S, base + i ∉ p.2.freeVars) ∧ base + i ∉ S.map Prod.fst)
    (hresolve : ResolveRecSlots members
      (((state.onSubst S).fixedCtx (S.onCtx ctx)).env.freeVars ++ K ++ softVars (substSoft S F))
      0 (state.onSubst S).slots written)
    (hcounts : ∀ (i : Nat) images, i ∈ members → (state.onSubst S).slots[i]? = some images →
      images.length = (anns[i]?.getD .absent).recPrefixCount)
    (hslots : ∀ member ty, state.specs[member]? = some (.mono ty) → member ∉ done ++ members →
      ∀ (i : Nat) images, i ∈ members → (state.onSubst S).slots[i]? = some images →
        ∀ t ∈ images, base + member ∉ t.freeVars) :
    ((state.onSubst S).exportComponent members written
      ((state.onSubst S).componentPool K (softVars (substSoft S F)) members (S.onCtx ctx) written) outputs facts).Frame
      base K (substSoft S F) (S.onCtx ctx) (anns.map (LetAnn.substTyFvars S)) (done ++ members) := by
  let st := state.onSubst S
  let pool := st.componentPool K (softVars (substSoft S F)) members (S.onCtx ctx) written
  have hdom : ∀ p ∈ S, p.1 ∉ state.pool := fun p hp hg =>
    (hpool p.1 hg).2 (List.mem_map.mpr ⟨p, hp, rfl⟩)
  have hran : ∀ p ∈ S, ∀ g ∈ p.2.freeVars, g ∉ state.pool :=
    fun p hp g hg hgp => (hpool g hgp).1 p hp hg
  have hfix : ∀ g ∈ state.pool, S.onTy (.fvar g) = .fvar g := Subst.fixes_of_dom_avoids hdom
  have hp := h.pending.onSubst_source (fun i hi => List.mem_append_left _ hi) hpending
  have hLC := hlc.onSubst hS
  have hwritten := hresolve.all_avoid
  have hnew : ∀ v ∈ pool, v ∉ state.pool →
      v ∉ (st.fixedCtx (S.onCtx ctx)).env.freeVars ++ K ++ softVars (substSoft S F) :=
    fun v hv hn => st.componentPool_new_avoid hwritten hv hn
  have hpoly : ∀ (i : Nat) (sigma : PolyTy), st.specs[i]? = some (.poly sigma) → st.exports[i]? = some (some sigma) := by
    intro i sigma hs
    rw [show st.specs = state.specs.map (RecSpec.onSubstSource S) from rfl, List.getElem?_map] at hs
    obtain ⟨old, hold, heq⟩ := Option.map_eq_some_iff.mp hs
    cases old with
    | mono ty => cases heq
    | poly original =>
      cases RecSpec.poly.inj heq
      simp only [st, RecState.onSubst, List.getElem?_map, h.poly i original hold, Option.map_some]
  change (st.exportComponent members written pool outputs facts).Frame base K (substSoft S F) (S.onCtx ctx)
    (anns.map (LetAnn.substTyFvars S)) (done ++ members)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hp, st.componentPool_nodup h.pool_nodup,
    ?_, ?_, ?_, ?_, ?_, h.rigid_below, ?_⟩
  · simpa only [RecState.exportComponent, st, RecState.onSubst, List.length_map] using h.specs_length
  · simpa only [RecState.exportComponent, st, RecState.onSubst, List.length_map] using h.slots_length
  · simpa only [RecState.exportComponent, st, RecState.onSubst, List.length_mapIdx, List.length_map] using h.exports_length
  · simpa only [RecState.exportComponent, st, RecState.onSubst, List.length_mapIdx, List.length_map] using h.outputs_length
  · simpa only [RecState.exportComponent, st, RecState.onSubst, List.length_mapIdx, List.length_map] using h.facts_length
  · have hm : st.specs.map RecSpec.ann = (state.specs.map RecSpec.ann).map (Option.map S.onPolyTy) := by
      simp only [st, RecState.onSubst, List.map_map]
      apply List.map_congr_left
      intro spec _
      cases spec <;> rfl
    rw [show (st.exportComponent members written pool outputs facts).specs = st.specs from rfl, hm, h.modes]
    simp only [List.map_map, Function.comp_def, LetAnn.recModeAnn_subst_source]
  · intro i sigma hs
    change st.specs[i]? = some (.poly sigma) at hs
    have hex := hpoly i sigma hs
    simp only [RecState.exportComponent, List.getElem?_mapIdx, hex, Option.map_some]
    by_cases hi : i ∈ members <;> simp [hi, hs, RecSpec.completedScheme]
  · intro i ty hs
    change st.specs[i]? = some (.mono ty) at hs
    obtain ⟨original, hold, heqty⟩ := RecSpec.mono_getElem?_map_onSubstSource hs
    subst ty
    by_cases hi : i ∈ members
    · have hislot : i < st.slots.length := by
        simpa only [st, RecState.onSubst, List.length_map, h.slots_length] using
          (show i < anns.length by simpa only [h.specs_length] using (List.getElem?_eq_some_iff.mp hold).1)
      have hslotget := List.getElem?_eq_getElem hislot
      obtain ⟨names, hnames, hbare⟩ := hresolve.lookup i _ hslotget
      rw [Nat.zero_add, if_pos hi] at hbare
      rw [if_pos (List.mem_append_right _ hi)]
      refine ⟨names, ?_, ?_, hbare.2.1, ?_, ?_⟩
      · change st.slots[i]? = some (names.map Ty.fvar)
        rw [hbare.1]; exact hslotget
      · have hh := hcounts i _ hi hslotget
        rw [← hbare.1, List.length_map] at hh
        cases ha : anns[i]? with
        | none => simpa only [List.getElem?_map, ha, Option.map_none] using hh
        | some ann => simpa only [List.getElem?_map, ha, Option.map_some, Option.getD_some,
            LetAnn.recPrefixCount_subst_source] using hh
      · intro v hv
        exact st.componentPool_written (List.mem_flatten.mpr ⟨names, List.mem_of_getElem? hnames, hv⟩)
      · have hiEx : i < st.exports.length := by
          simpa only [st, RecState.onSubst, List.length_map, h.exports_length] using
            (show i < anns.length by simpa only [h.specs_length] using (List.getElem?_eq_some_iff.mp hold).1)
        simp only [RecState.exportComponent, List.getElem?_mapIdx,
          List.getElem?_eq_getElem hiEx, Option.map_some, if_pos hi, hs,
          Option.getD_some, hnames, RecSpec.completedScheme]
        rfl
    · have hm := h.mono i original hold
      by_cases hd : i ∈ done
      · obtain ⟨names, hslot, hcount, hnd, hsub, hex⟩ := if_pos hd ▸ hm
        rw [if_pos (List.mem_append_left _ hd)]
        have hnormalized : st.exports[i]? = some (some (recScheme names state.pool (S.onTy original))) := by
          simp only [st, RecState.onSubst, List.getElem?_map, hex, Option.map_some]
          rw [recScheme_subst_pool_avoid hdom hran hsub]
        have hstable := st.recScheme_componentPool_eq (members := members)
          (Subst.onTy_lc hS (hlc.1 _ (List.mem_of_getElem? hold))) hsub
          (List.mem_of_getElem? hnormalized) hwritten
        refine ⟨names, ?_, ?_, hnd, fun v hv => st.componentPool_old (hsub v hv), ?_⟩
        · simp only [RecState.exportComponent, st, RecState.onSubst, List.getElem?_map,
            hslot, Option.map_some, List.map_map]
          congr 1
          exact List.map_congr_left (fun v hv => hfix v (hsub v hv))
        · cases ha : anns[i]? with
          | none => simpa only [List.getElem?_map, ha, Option.map_none] using hcount
          | some ann => simpa only [List.getElem?_map, ha, Option.map_some, Option.getD_some,
              LetAnn.recPrefixCount_subst_source] using hcount
        · have hstable' : recScheme names pool (S.onTy original) = recScheme names state.pool (S.onTy original) := hstable
          change (st.exportComponent members written pool outputs facts).exports[i]? = some (some (recScheme names pool (S.onTy original)))
          rw [hstable']
          simp only [RecState.exportComponent, List.getElem?_mapIdx, hnormalized, Option.map_some, if_neg hi]
      · rw [if_neg (by simpa only [List.mem_append, not_or] using And.intro hd hi)]
        have hex := if_neg hd ▸ hm
        simp only [RecState.exportComponent, st, RecState.onSubst, List.getElem?_mapIdx,
          List.getElem?_map, hex, Option.map_some, Option.map_none, if_neg hi]
  · intro v hv hctxv
    by_cases hold : v ∈ state.pool
    · obtain ⟨sigma, hs, hv⟩ := Env.mem_freeVars_iff.mp hctxv
      obtain ⟨original, ho, rfl⟩ := List.mem_map.mp hs
      exact Subst.notMemOnTy (hpool v hold).1
        (fun hh => h.pool_ctx v hold (Env.mem_freeVars_iff.mpr ⟨original, ho, hh⟩)) hv
    · exact hnew v hv hold (List.mem_append_left _ (List.mem_append_left _
        (Env.mem_freeVars_iff.mpr (by
          obtain ⟨sigma, hs, ht⟩ := Env.mem_freeVars_iff.mp hctxv
          exact ⟨sigma, List.mem_append_right _ hs, ht⟩))))
  · intro v hv hKv
    by_cases hold : v ∈ state.pool
    · exact h.pool_rigid v hold hKv
    · exact hnew v hv hold (List.mem_append_left _ (List.mem_append_right _ hKv))
  · intro v hv hFv
    by_cases hold : v ∈ state.pool
    · obtain ⟨ty, ht, hvty⟩ := TyList.mem_freeVars_iff.mp hFv
      obtain ⟨old, ho, rfl⟩ := List.mem_map.mp ht
      exact Subst.notMemOnTy (hpool v hold).1
        (fun hh => h.pool_soft v hold (TyList.mem_freeVars_iff.mpr ⟨old, ho, hh⟩)) hvty
    · exact hnew v hv hold (List.mem_append_right _ hFv)
  · intro sigma ⟨i, hs⟩ v hv hsig
    change st.specs[i]? = some (.poly sigma) at hs
    by_cases hold : v ∈ state.pool
    · rw [show st.specs = state.specs.map (RecSpec.onSubstSource S) from rfl, List.getElem?_map] at hs
      obtain ⟨old, ho, heq⟩ := Option.map_eq_some_iff.mp hs
      cases old with
      | mono ty => cases heq
      | poly original =>
        cases RecSpec.poly.inj heq
        exact Subst.notMemOnTy (hpool v hold).1 (h.pool_poly original ⟨i, ho⟩ v hold) hsig
    · exact hnew v hv hold (List.mem_append_left _ (List.mem_append_left _
        (Env.mem_freeVars_iff.mpr ⟨sigma, List.mem_append_left _
          (List.mem_filterMap.mpr ⟨some sigma, List.mem_of_getElem? (hpoly i sigma hs), rfl⟩), hsig⟩)))
  · intro member ty hs hm hv
    obtain ⟨old, ho, _⟩ := RecSpec.mono_getElem?_map_onSubstSource hs
    rcases List.mem_append.mp hv with hv | hv
    · exact h.pool_pending member old ho (fun hd => hm (List.mem_append_left _ hd)) hv
    · rcases List.mem_append.mp (List.mem_dedup.mp (List.mem_filter.mp hv).1) with hv | hv
      · exact hresolve.names_avoid_of_slots
          (fun i images hi hget => hslots member old ho hm i images (by simpa using hi) hget) hv
      · have hfree : base + member ∈ Ty.freeVarsList (RecSpecs.monoTysAt st.specs members) :=
          (List.mem_filter.mp hv).1
        obtain ⟨tau, htau, hmem⟩ := Ty.mem_freeVarsList_exists_local hfree
        obtain ⟨j, hj, hlook⟩ := List.mem_filterMap.mp htau
        cases hspec : st.specs[j]? with
        | none => simp [hspec] at hlook
        | some spec =>
          cases spec with
          | poly sigma => simp [hspec, RecSpec.monoTy?] at hlook
          | mono tau0 =>
            simp only [hspec, Option.bind_some, RecSpec.monoTy?, Option.some.injEq] at hlook
            subst tau
            exact hp.other member ty hs hm j (.mono tau0) hspec
              (fun heq => hm (List.mem_append_right _ (heq ▸ hj))) hmem
  · intro member ty hs hm hfv
    obtain ⟨old, ho, _⟩ := RecSpec.mono_getElem?_map_onSubstSource hs
    obtain ⟨t, ht, hf⟩ := TyList.mem_freeVars_iff.mp hfv
    obtain ⟨original, horig, rfl⟩ := List.mem_map.mp ht
    exact Subst.notMemOnTy (hpending member old ho hm).1
      (fun hh => h.pending_soft member old ho (fun hd => hm (List.mem_append_left _ hd))
        (TyList.mem_freeVars_iff.mpr ⟨original, horig, hh⟩)) hf

private theorem OpenRecAnns.written_count
    (h : OpenRecAnns members index frontier anns next openings) :
    ∀ j : Nat, index + j ∈ members → ((openings[j]?).getD .empty).written.length =
      (anns[j]?.getD .absent).recPrefixCount := by
  induction h with
  | nil => intro j _; simp [RecOpening.empty, LetAnn.recPrefixCount]
  | skip hn hr ih =>
    intro j hj
    cases j with
    | zero => exact False.elim (hn (by simpa using hj))
    | succ j => exact ih j (by simpa only [Nat.succ_add, Nat.add_succ] using hj)
  | cons hm hh hr ih =>
    intro j hj
    cases j with
    | zero => cases hh <;> simp [LetAnn.recPrefixCount, RecOpening.empty, freshVars_length]
    | succ j => exact ih j (by simpa only [Nat.succ_add, Nat.add_succ] using hj)

private theorem installed_subst_slot {state : RecState} {S : Subst} {i : Nat} {images : List Ty}
    (hi : i ∈ members) (hx : ((state.installOpenings members openings).onSubst S).slots[i]? = some images) :
    images = (((openings[i]?).getD .empty).written.map Ty.fvar).map S.onTy := by
  have hlt : i < state.slots.length := by
    simpa only [RecState.onSubst, RecState.installOpenings, List.length_map, List.length_mapIdx] using
      (List.getElem?_eq_some_iff.mp hx).1
  have hget := List.getElem?_eq_getElem hlt
  simp only [RecState.onSubst, RecState.installOpenings, List.getElem?_map, List.getElem?_mapIdx,
    hget, Option.map_some, if_pos hi] at hx
  exact (Option.some.inj hx).symm

 theorem recStep_frame
    {state : RecState}
    (ho : OpenRecAnns component 0 frontier anns opened openings)
    (hp : CheckRecShapes K ((state.installOpenings component openings).shapes component openings) pre)
    (hc : InferRecComponent K (substSoft pre (F ++ (openings.flatMap RecOpening.written).map Ty.fvar))
      component 0 opened (((state.installOpenings component openings).onSubst pre).rhsCtx (pre.onCtx ctx))
      ((openRecSources openings bindings).map (Input.substTyFvars pre))
      ((state.installOpenings component openings).onSubst pre).specs first current outputs facts)
    (hf : FinishRecComponent K (softVars (substSoft (pre ++ current) F)) component
      ((pre ++ current).onCtx ctx) ((state.installOpenings component openings).onSubst (pre ++ current))
      outputs facts exported)
    (hInfer : ∀ {κ F' Ψ c e Ψ' T output ty}, e.size ≤ sizeBindings bindings →
      Infer κ F' Ψ c e Ψ' T output ty →
      ∀ {w}, w < Ψ →
      e.erase.ForallOuter (fun i => ∀ M, c.env[i]? = some M → w ∉ M.body.freeVars) 0 →
      w ∉ e.rigidVars →
      (∀ p ∈ T, w ∉ p.2.freeVars) ∧ w ∉ ty.freeVars ∧ w ∉ T.map Prod.fst)
    (hvalid : RecGroups.ValidResidualGroups (anns.map LetAnn.recModeAnn) (bindings.map Input.erase)
      (past ++ component :: rest))
    (hframe : state.Frame base K F ctx anns past.flatten)
    (hlc : state.LC) (hctx : CtxWF ctx)
    (hbelow : state.Below frontier) (hbase : base + bindings.length ≤ frontier)
    (hanns : ∀ ann ∈ anns, ∀ v ∈ ann.rigidVars, v ∈ K ++ softVars F)
    (hrhs : ∀ rhs ∈ bindings, ∀ v ∈ rhs.rigidVars, v ∈ K ++ softVars F) :
    exported.Frame base K (substSoft (pre ++ current) F) ((pre ++ current).onCtx ctx)
      (anns.map (LetAnn.substTyFvars (pre ++ current))) (past.flatten ++ component) ∧
    (∀ g ∈ state.pool, (∀ p ∈ pre ++ current, g ∉ p.2.freeVars) ∧ g ∉ (pre ++ current).map Prod.fst) ∧
    (∀ member ty, state.specs[member]? = some (.mono ty) → member ∉ past.flatten ++ component →
      (∀ p ∈ pre ++ current, base + member ∉ p.2.freeVars) ∧ base + member ∉ (pre ++ current).map Prod.fst) := by
  have havoid := recStep_oldpool_pending_avoid ho hp hc hInfer hvalid hframe hbelow hbase hanns hrhs
  have hnot : ∀ i ∈ component, i ∉ past.flatten := by
    intro i hi hd
    have hnd : (past.flatten ++ (component ++ rest.flatten)).Nodup := by
      simpa only [List.flatten_append, List.flatten_cons] using hvalid.flatten_nodup
    exact (List.nodup_append.mp hnd).2.2 i hd i (List.mem_append_left _ hi) rfl
  have hins : (state.installOpenings component openings).Frame base K F ctx anns past.flatten :=
    hframe.installOpenings hnot
  have hinitLC := hlc.installOpenings (members := component) (openings := openings)
  have hpreLC := hp.lc (RecState.shapes_lc hinitLC ho.expected_lc)
  have hcurrentLC := hc.lc_of_infer (fun _ hi => hi.lc)
    ((hinitLC.onSubst hpreLC).rhsCtx (Subst.onCtx_wf hpreLC hctx))
    (hinitLC.onSubst hpreLC).1
  have hSLC : ∀ p ∈ pre ++ current, p.2.IsLC :=
    fun p hm => (List.mem_append.mp hm).elim (hpreLC p) (hcurrentLC p)
  refine ⟨?_, havoid⟩
  cases hf with
  | mk hresolve =>
    apply hins.exportComponent_onSubst hlc.installOpenings hSLC havoid.1 havoid.2 hresolve
    · intro i images hi hx
      rw [installed_subst_slot hi hx, List.length_map, List.length_map]
      exact ho.written_count i (by simpa using hi)
    · intro member ty ht hm i images hi hx t htmem
      have hw : base + member < frontier := by
        have hlt := (List.getElem?_eq_some_iff.mp ht).1
        have hlen : anns.length = bindings.length := by simpa only [List.length_map] using hvalid.length
        change member < state.specs.length at hlt
        rw [hframe.specs_length, hlen] at hlt
        omega
      rw [installed_subst_slot hi hx] at htmem
      obtain ⟨old, hold, rfl⟩ := List.mem_map.mp htmem
      obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hold
      apply Subst.notMemOnTy (havoid.2 member ty ht hm).1
      simp only [Ty.freeVars, List.mem_singleton]
      intro heq
      subst v
      cases hxopen : openings[i]? with
      | none => simp [hxopen, RecOpening.empty] at hv
      | some opening =>
        have hrange := ho.written_range (base + member)
          (List.mem_flatMap.mpr ⟨opening, List.mem_of_getElem? hxopen, by simpa only [hxopen, Option.getD_some] using hv⟩)
        omega

theorem recValid_subst {anns : List LetAnn} {bindings : List Input}
    (h : RecGroups.ValidResidualGroups (anns.map LetAnn.recModeAnn) (bindings.map Input.erase) groups)
    (S : Subst) :
    RecGroups.ValidResidualGroups ((anns.map (LetAnn.substTyFvars S)).map LetAnn.recModeAnn)
      ((bindings.map (Input.substTyFvars S)).map Input.erase) groups := by
  have hg := h.map_bindings (anns' := (anns.map (LetAnn.substTyFvars S)).map LetAnn.recModeAnn) id
    (by simp) (fun i => by
      simp only [RecGroups.UnsignedAt, List.getElem?_map, Option.map_map, Function.comp_def]
      cases anns[i]? with
      | none => simp
      | some ann => cases ann <;> simp [LetAnn.recModeAnn, LetAnn.substTyFvars])
    (fun _ _ => rfl)
  simpa only [List.map_id, List.map_map, Function.comp_def, Input.erase_substTyFvars] using hg

private theorem FinishRecComponent.pool_extends
    (h : FinishRecComponent K soft members ctx state outputs facts final) (hv : v ∈ state.pool) :
    v ∈ final.pool := by
  cases h
  exact state.componentPool_old hv

 theorem _root_.InferRecStrata.frame_of_infer
    (h : InferRecStrata K F frontier ctx anns bindings state groups next S final)
    (hInfer : ∀ {κ F' Ψ c e Ψ' T output ty}, e.size ≤ sizeBindings bindings →
      Infer κ F' Ψ c e Ψ' T output ty →
      ∀ {w}, w < Ψ →
      e.erase.ForallOuter (fun i => ∀ M, c.env[i]? = some M → w ∉ M.body.freeVars) 0 →
      w ∉ e.rigidVars →
      (∀ p ∈ T, w ∉ p.2.freeVars) ∧ w ∉ ty.freeVars ∧ w ∉ T.map Prod.fst)
    (hvalid : RecGroups.ValidResidualGroups (anns.map LetAnn.recModeAnn) (bindings.map Input.erase) (past ++ groups))
    (hframe : state.Frame base K F ctx anns past.flatten)
    (hlc : state.LC) (hctxWF : CtxWF ctx)
    (hbelow : state.Below frontier) (hctx : CtxBelow frontier ctx)
    (hF : ∀ t ∈ F, Ty.BelowFvars frontier t)
    (hbase : base + bindings.length ≤ frontier)
    (hanns : ∀ ann ∈ anns, ∀ v ∈ ann.rigidVars, v ∈ K ++ softVars F)
    (hrhs : ∀ rhs ∈ bindings, ∀ v ∈ rhs.rigidVars, v ∈ K ++ softVars F) :
    final.Frame base K (substSoft S F) (S.onCtx ctx) (anns.map (LetAnn.substTyFvars S)) (past ++ groups).flatten ∧
    (∀ g ∈ state.pool, (∀ p ∈ S, g ∉ p.2.freeVars) ∧ g ∉ S.map Prod.fst) := by
  match h with
  | .nil =>
    have hannNil : anns.map (LetAnn.substTyFvars []) = anns := by
      calc
        anns.map (LetAnn.substTyFvars []) = anns.map id := List.map_congr_left
          (fun ann _ => ann.substTyFvars_eq_self_of_fixes (fun _ _ => rfl))
        _ = anns := List.map_id anns
    exact ⟨by simpa only [substSoft_nil, Subst.onCtx_nil, hannNil, List.append_nil] using hframe,
      by intro g hg; exact ⟨by simp, by simp⟩⟩
  | .cons ho hp hc hf hr =>
    expose_names
    obtain ⟨hstepFrame, hstepPool, _⟩ := recStep_frame ho hp hc hf hInfer hvalid hframe
      hlc hctxWF hbelow hbase hanns hrhs
    have hstep : InferRecStrata K F frontier ctx anns bindings state [component]
        first (pre ++ current ++ []) exported := .cons ho hp hc hf .nil
    have hK : ∀ k ∈ K, k < frontier := fun k hk => by have := hframe.rigid_below k hk; omega
    have hAnnBelow : ∀ ann ∈ anns, ∀ v ∈ ann.rigidVars, v < frontier := by
      intro ann ha v hv
      exact (List.mem_append.mp (hanns ann ha v hv)).elim (hK v) (softVars_lt hF v)
    have hstepBelow := hstep.belowFvars_of_infer (fun _ hi => hi.belowFvars) hctx hK hF hbelow hAnnBelow
    simp only [List.append_nil] at hstepBelow
    have hstepLC := hstep.lc_of_infer (fun _ hi => hi.lc) hctxWF hlc
    simp only [List.append_nil] at hstepLC
    have hfix : ∀ k ∈ K, (pre ++ current).onTy (.fvar k) = .fvar k := by
      apply Subst.fixes_of_dom_avoids
      simpa only [List.append_nil] using hstep.dom_avoids
    have htailValid := recValid_subst (S := pre ++ current)
      (by simpa only [List.append_assoc, List.singleton_append] using hvalid :
        RecGroups.ValidResidualGroups (anns.map LetAnn.recModeAnn) (bindings.map Input.erase)
          ((past ++ [component]) ++ rest))
    have htailFrame : exported.Frame base K (substSoft (pre ++ current) F) ((pre ++ current).onCtx ctx)
        (anns.map (LetAnn.substTyFvars (pre ++ current))) (past ++ [component]).flatten := by
      simpa only [List.flatten_append, List.flatten_cons, List.flatten_nil, List.append_nil] using hstepFrame
    obtain ⟨hfinal, htailPool⟩ := hr.frame_of_infer
      (fun he hi => hInfer (by simpa only [sizeBindings_map_substTyFvars] using he) hi)
      htailValid htailFrame hstepLC.2 (Subst.onCtx_wf hstepLC.1 hctxWF)
      hstepBelow.2 (Subst.onCtx_below hstepBelow.1 (ho.frontier_le.trans hc.frontier_le) hctx)
      (substSoft_below hstepBelow.1 (ho.frontier_le.trans hc.frontier_le) hF)
      (by simp only [List.length_map]; have := ho.frontier_le; have := hc.frontier_le; omega)
      (by
        intro ann hm v hv
        obtain ⟨original, ho, rfl⟩ := List.mem_map.mp hm
        obtain ⟨k, hk, himage⟩ := LetAnn.rigidVars_substTyFvars hv
        exact scope_image hfix (hanns original ho k hk) himage)
      (by
        intro rhs hm
        obtain ⟨original, ho, rfl⟩ := List.mem_map.mp hm
        exact (show SourceScope K F original from hrhs original ho).subst (pre ++ current) hfix)
    refine ⟨?_, ?_⟩
    · simpa only [substSoft_append, Subst.onCtx_append, List.map_map, Function.comp_def,
        ← LetAnn.substTyFvars_append, List.append_assoc, List.singleton_append] using hfinal
    · intro g hg
      have ht := htailPool g (hf.pool_extends hg)
      exact ⟨fun p hp => (List.mem_append.mp hp).elim ((hstepPool g hg).1 p) (ht.1 p),
        by simpa only [List.map_append, List.mem_append, not_or] using And.intro (hstepPool g hg).2 ht.2⟩
 termination_by structural h


theorem RecState.Frame.setSigned {state : RecState} {member : Nat} {names : List Nat}
    {output : Expr} {facts : RecFacts} (h : state.Frame base K F ctx anns done) :
    (state.setSigned member names output facts).Frame base K F ctx anns done := by
  refine ⟨h.specs_length, h.slots_length, h.exports_length, ?_, ?_, h.modes, h.poly, h.mono,
    h.pending, h.pool_nodup, h.pool_ctx, h.pool_rigid, h.pool_soft, h.pool_poly,
    h.pool_pending, h.rigid_below, h.pending_soft⟩
  · simpa only [RecState.setSigned, List.length_set] using h.outputs_length
  · simpa only [RecState.setSigned, List.length_set] using h.facts_length

private theorem RecState.Frame.poly_of_complete {state : RecState} {i : Nat} {scheme : PolyTy}
    (h : state.Frame base K F ctx anns done) (ha : anns[i]? = some (.complete scheme)) :
    state.specs[i]? = some (.poly scheme) := by
  have hm := congrArg (fun xs : List (Option PolyTy) => xs[i]?) h.modes
  simp only [List.getElem?_map, ha, Option.map_some, LetAnn.recModeAnn] at hm
  cases hs : state.specs[i]? with
  | none => simp [hs] at hm
  | some spec =>
    cases spec with
    | mono ty => simp [hs, RecSpec.ann] at hm
    | poly original =>
      simp only [hs, Option.map_some, RecSpec.ann, Option.some.injEq] at hm
      cases hm
      rfl

 theorem _root_.InferRecSigned.frame_of_infer
    (h : InferRecSigned K F index frontier ctx anns bindings state next S final)
    (hInfer : ∀ {κ F' Ψ c e Ψ' T output ty}, e.size ≤ sizeBindings bindings →
      Infer κ F' Ψ c e Ψ' T output ty →
      ∀ {w}, w < Ψ →
      e.erase.ForallOuter (fun i => ∀ M, c.env[i]? = some M → w ∉ M.body.freeVars) 0 →
      w ∉ e.rigidVars →
      (∀ p ∈ T, w ∉ p.2.freeVars) ∧ w ∉ ty.freeVars ∧ w ∉ T.map Prod.fst)
    (hframe : state.Frame base K F ctx fullAnns done)
    (hremaining : fullAnns.drop index = anns)
    (hmono : ∀ i ty, state.specs[i]? = some (.mono ty) → i ∈ done)
    (hpoolBelow : ∀ g ∈ state.pool, g < frontier) :
    final.Frame base K (substSoft S F) (S.onCtx ctx) (fullAnns.map (LetAnn.substTyFvars S)) done ∧
    (∀ g ∈ state.pool, (∀ p ∈ S, g ∉ p.2.freeVars) ∧ g ∉ S.map Prod.fst) := by
  match h with
  | .nil =>
    have hannNil : fullAnns.map (LetAnn.substTyFvars []) = fullAnns := by
      calc
        fullAnns.map (LetAnn.substTyFvars []) = fullAnns.map id := List.map_congr_left
          (fun ann _ => ann.substTyFvars_eq_self_of_fixes (fun _ _ => rfl))
        _ = fullAnns := List.map_id fullAnns
    exact ⟨by simpa only [substSoft_nil, Subst.onCtx_nil, hannNil] using hframe,
      by intro g hg; exact ⟨by simp, by simp⟩⟩
  | .skip _ hr =>
    apply hr.frame_of_infer
      (fun he hi => hInfer (by simp only [sizeBindings]; omega) hi) hframe
      (by simp only [List.drop_add_one_eq_tail_drop, hremaining, List.tail_cons]) hmono hpoolBelow
  | .cons _ hscope hi hu _ hr =>
    expose_names
    have hAnn : fullAnns[index]? = some (.complete scheme) := by
      have hh := congrArg (fun xs : List LetAnn => xs[0]?) hremaining
      simpa only [List.getElem?_drop, Nat.zero_add, List.getElem?_cons_zero] using hh
    have hspec := hframe.poly_of_complete hAnn
    have havoid : ∀ g ∈ state.pool,
        (∀ p ∈ s1 ++ s2, g ∉ p.2.freeVars) ∧ g ∉ (s1 ++ s2).map Prod.fst := by
      intro g hg
      have hgy : g ∉ freshVars frontier scheme.paramCount := fun hmem => by
        have := freshVars_ge g hmem
        have := hpoolBelow g hg
        omega
      obtain ⟨hfirstS, hfirstTy, hfirstD⟩ := hInfer
        (by simp only [Input.size_openTyVars, sizeBindings]; omega) hi
        (show g < frontier + scheme.paramCount by have := hpoolBelow g hg; omega)
        (by
          apply Expr.ForallOuter.of_recGroupRefs_with_outer (n := 0)
          · intro j hj M hget hv
            exact hframe.pool_rhsCtx g hg (Env.mem_freeVars_iff.mpr ⟨M, List.mem_of_getElem? hget, hv⟩)
          · intro j hj M hget hv
            exact hframe.pool_rhsCtx g hg (Env.mem_freeVars_iff.mpr ⟨M, List.mem_of_getElem? hget, hv⟩))
        (by
          intro hv
          rcases Input.rigidVars_openTyVarsFrom hv with hv | hv
          · exact (List.mem_append.mp (hscope g hv)).elim (hframe.pool_rigid g hg) (hframe.pool_soft g hg)
          · exact hgy hv)
      have hexpected : g ∉ ((s1.onPolyTy scheme).openVars (freshVars frontier scheme.paramCount)).freeVars := by
        intro hv
        exact (Ty.freeVars_openVars_subset g hv).elim
          (Subst.notMemOnTy hfirstS (hframe.pool_poly scheme ⟨index, hspec⟩ g hg)) hgy
      have hsecondS : ∀ p ∈ s2, g ∉ p.2.freeVars := by
        intro p hp hv
        exact (hu.unifies.range_mem p hp g hv).elim hfirstTy hexpected
      have hsecondD : g ∉ s2.map Prod.fst := by
        intro hm
        obtain ⟨p, hp, hpw⟩ := List.mem_map.mp hm
        have hh := hu.unifies.dom_mem p hp
        rw [hpw] at hh
        exact hh.elim hfirstTy hexpected
      exact ⟨fun p hp => (List.mem_append.mp hp).elim (hfirstS p) (hsecondS p),
        by simpa only [List.map_append, List.mem_append, not_or] using And.intro hfirstD hsecondD⟩
    have hnextFrame := (hframe.onSubst havoid
      (fun i ty hs hn => False.elim (hn (hmono i ty hs)))).setSigned
      (member := index) (names := freshVars frontier scheme.paramCount)
      (output := output.substTyFvars s2) (facts := bodyFacts.onSubst s2)
    have hnextMono : ∀ i ty,
        ((state.onSubst (s1 ++ s2)).setSigned index (freshVars frontier scheme.paramCount)
          (output.substTyFvars s2) (bodyFacts.onSubst s2)).specs[i]? = some (.mono ty) → i ∈ done := by
      intro i ty hs
      obtain ⟨old, ho, _⟩ := RecSpec.mono_getElem?_map_onSubstSource hs
      exact hmono i old ho
    obtain ⟨hfinal, htailAvoid⟩ := hr.frame_of_infer
      (fun he hh => hInfer (by
        simp only [sizeBindings_map_substTyFvars] at he
        simp only [sizeBindings]
        omega) hh)
      hnextFrame
      (by simp only [← List.map_drop, List.drop_add_one_eq_tail_drop, hremaining, List.map_cons, List.tail_cons]) hnextMono
      (by intro g hg; have hlt := hpoolBelow g hg; have := hi.frontier_le; omega)
    refine ⟨?_, ?_⟩
    · simpa only [substSoft_append, Subst.onCtx_append, List.map_map, Function.comp_def,
        ← LetAnn.substTyFvars_append] using hfinal
    · intro g hg
      have ht := htailAvoid g hg
      exact ⟨fun p hp => (List.mem_append.mp hp).elim ((havoid g hg).1 p) (ht.1 p),
        by simpa only [List.map_append, List.mem_append, not_or] using And.intro (havoid g hg).2 ht.2⟩
 termination_by structural h


 theorem recStep_sourceSound
    {state : RecState} {past : List (List Nat)}
    (ho : OpenRecAnns component 0 frontier anns opened openings)
    (hp : CheckRecShapes K ((state.installOpenings component openings).shapes component openings) pre)
    (hc : InferRecComponent K (substSoft pre (F ++ (openings.flatMap RecOpening.written).map Ty.fvar))
      component 0 opened (((state.installOpenings component openings).onSubst pre).rhsCtx (pre.onCtx ctx))
      ((openRecSources openings bindings).map (Input.substTyFvars pre))
      ((state.installOpenings component openings).onSubst pre).specs first current outputs facts)
    (hf : FinishRecComponent K (softVars (substSoft (pre ++ current) F)) component
      ((pre ++ current).onCtx ctx) ((state.installOpenings component openings).onSubst (pre ++ current))
      outputs facts exported)
    (hInfer : ∀ {κ F' Ψ c e Ψ' T output ty}, e.size ≤ sizeBindings bindings →
      Infer κ F' Ψ c e Ψ' T output ty → CtxWF c → TypeOfHM (T.onCtx c) output ty)
    (hframe : state.Frame base K F ctx anns past.flatten)
    (heframe : exported.Frame base K (substSoft (pre ++ current) F) ((pre ++ current).onCtx ctx)
      (anns.map (LetAnn.substTyFvars (pre ++ current))) (past.flatten ++ component))
    (hlc : state.LC) (hctx : CtxWF ctx) (htyped : state.SourceTyped ctx)
    (hnot : ∀ i ∈ component, i ∉ past.flatten)
    (hmono : ∀ i ∈ component, ∃ ty, state.specs[i]? = some (.mono ty)) :
    exported.SourceTyped ((pre ++ current).onCtx ctx) := by
  have hinitLC := hlc.installOpenings (members := component) (openings := openings)
  have hpreLC := hp.lc (RecState.shapes_lc hinitLC ho.expected_lc)
  have hpreCtx := (hinitLC.onSubst hpreLC).rhsCtx (Subst.onCtx_wf hpreLC hctx)
  have hcurrentLC := hc.lc_of_infer (fun _ hi => hi.lc) hpreCtx (hinitLC.onSubst hpreLC).1
  have hSLC : ∀ p ∈ pre ++ current, p.2.IsLC :=
    fun p hm => (List.mem_append.mp hm).elim (hpreLC p) (hcurrentLC p)
  have hsound := hc.sourceSound_of_infer
    (fun he hi => hInfer (by simpa only [sizeBindings_map_substTyFvars, sizeBindings_openRecSources] using he) hi)
    (fun _ hi => hi.lc) hpreCtx (hinitLC.onSubst hpreLC).1
  have hsource : (state.installOpenings component openings).SourceTyped ctx := htyped
  have hsourceS := hsource.onSubst (pre ++ current) hSLC
  cases hf with
  | mk hresolve =>
    expose_names
    let st := (state.installOpenings component openings).onSubst (pre ++ current)
    have hstmono : ∀ i ∈ component, ∃ ty, st.specs[i]? = some (.mono ty) := by
      intro i hi
      obtain ⟨ty, ht⟩ := hmono i hi
      exact ⟨(pre ++ current).onTy ty, by simp only [st, RecState.onSubst, RecState.installOpenings,
        List.getElem?_map, ht, Option.map_some, RecSpec.onSubstSource]⟩
    apply hsourceS.exportComponent
      (by simp only [RecState.onSubst, RecState.installOpenings, List.length_map]; exact hframe.exports_length.trans hframe.outputs_length.symm)
      (by simp only [RecState.onSubst, RecState.installOpenings, List.length_map]; exact hframe.outputs_length.trans hframe.specs_length.symm)
      (hinitLC.onSubst hSLC).1
    · intro i hi
      obtain ⟨ty, ht⟩ := hmono i hi
      have hh := if_neg (hnot i hi) ▸ hframe.mono i ty ht
      simp only [RecState.onSubst, RecState.installOpenings, List.getElem?_map, hh, Option.map_some, Option.map_none]
    · exact hstmono
    · intro i hi
      have hil : i < st.slots.length := by
        rw [show st.slots.length = anns.length from by simp only [st, RecState.onSubst, RecState.installOpenings, List.length_map, List.length_mapIdx, hframe.slots_length]]
        obtain ⟨ty, ht⟩ := hmono i hi
        simpa only [hframe.specs_length] using (List.getElem?_eq_some_iff.mp ht).1
      obtain ⟨ns, hns, hh⟩ := hresolve.lookup i _ (List.getElem?_eq_getElem hil)
      rw [Nat.zero_add, if_pos hi] at hh
      simpa only [hns, Option.getD_some] using hh.2.1
    · intro i hi v hv
      apply st.componentPool_written
      cases hh : written[i]? with
      | none => simp only [hh, Option.getD_none, List.not_mem_nil] at hv
      | some ns => exact List.mem_flatten.mpr ⟨ns, List.mem_of_getElem? hh,
          by simpa only [hh, Option.getD_some] using hv⟩
    · exact heframe.pool_nodup
    · exact heframe.pool_rhsCtx
    · intro i ty output ht hout
      obtain ⟨old, hold, rfl⟩ := RecSpec.mono_getElem?_map_onSubstSource ht
      have htyPre : ((state.installOpenings component openings).onSubst pre).specs[i]? = some (.mono (pre.onTy old)) := by
        simp only [RecState.onSubst, List.getElem?_map, hold, Option.map_some, RecSpec.onSubstSource]
      have hh := hsound i (pre.onTy old) output htyPre hout
      rw [RecState.rhsCtx_onSubst] at hh ⊢
      simpa only [Subst.onCtx_append, Subst.onTy_append] using hh
 theorem _root_.InferRecStrata.sourceSound_of_infer
    (h : InferRecStrata K F frontier ctx anns bindings state groups next S final)
    (hInfer : ∀ {κ F' Ψ c e Ψ' T output ty}, e.size ≤ sizeBindings bindings →
      Infer κ F' Ψ c e Ψ' T output ty →
      ∀ {w}, w < Ψ →
      e.erase.ForallOuter (fun i => ∀ M, c.env[i]? = some M → w ∉ M.body.freeVars) 0 →
      w ∉ e.rigidVars →
      (∀ p ∈ T, w ∉ p.2.freeVars) ∧ w ∉ ty.freeVars ∧ w ∉ T.map Prod.fst)
    (hvalid : RecGroups.ValidResidualGroups (anns.map LetAnn.recModeAnn) (bindings.map Input.erase) (past ++ groups))
    (hframe : state.Frame base K F ctx anns past.flatten)
    (hlc : state.LC) (hctxWF : CtxWF ctx)
    (hbelow : state.Below frontier) (hctx : CtxBelow frontier ctx)
    (hF : ∀ t ∈ F, Ty.BelowFvars frontier t)
    (hbase : base + bindings.length ≤ frontier)
    (hanns : ∀ ann ∈ anns, ∀ v ∈ ann.rigidVars, v ∈ K ++ softVars F)
    (hrhs : ∀ rhs ∈ bindings, ∀ v ∈ rhs.rigidVars, v ∈ K ++ softVars F)
    (hSound : ∀ {κ F' Ψ c e Ψ' T output ty}, e.size ≤ sizeBindings bindings →
      Infer κ F' Ψ c e Ψ' T output ty → CtxWF c → TypeOfHM (T.onCtx c) output ty)
    (htyped : state.SourceTyped ctx) : final.SourceTyped (S.onCtx ctx) := by
  match h with
  | .nil => simpa only [Subst.onCtx_nil] using htyped
  | .cons ho hp hc hf hr =>
    expose_names
    obtain ⟨hstepFrame, hstepPool, _⟩ := recStep_frame ho hp hc hf hInfer hvalid hframe
      hlc hctxWF hbelow hbase hanns hrhs
    have hnot : ∀ i ∈ component, i ∉ past.flatten := by
      intro i hi hd
      have hnd : (past.flatten ++ (component ++ rest.flatten)).Nodup := by
        simpa only [List.flatten_append, List.flatten_cons] using hvalid.flatten_nodup
      exact (List.nodup_append.mp hnd).2.2 i hd i (List.mem_append_left _ hi) rfl
    have hmono : ∀ i ∈ component, ∃ ty, state.specs[i]? = some (.mono ty) := by
      intro i hi
      have hm : i ∈ (past ++ component :: rest).flatten := by
        simp only [List.flatten_append, List.flatten_cons, List.mem_append]
        tauto
      exact hframe.mono_at_unsigned ((hvalid.covers_unsigned i (hvalid.bounded i hm)).mp hm)
    have hstepSound := recStep_sourceSound ho hp hc hf hSound hframe hstepFrame hlc hctxWF htyped hnot hmono
    have hstep : InferRecStrata K F frontier ctx anns bindings state [component]
        first (pre ++ current ++ []) exported := .cons ho hp hc hf .nil
    have hK : ∀ k ∈ K, k < frontier := fun k hk => by have := hframe.rigid_below k hk; omega
    have hAnnBelow : ∀ ann ∈ anns, ∀ v ∈ ann.rigidVars, v < frontier := by
      intro ann ha v hv
      exact (List.mem_append.mp (hanns ann ha v hv)).elim (hK v) (softVars_lt hF v)
    have hstepBelow := hstep.belowFvars_of_infer (fun _ hi => hi.belowFvars) hctx hK hF hbelow hAnnBelow
    simp only [List.append_nil] at hstepBelow
    have hstepLC := hstep.lc_of_infer (fun _ hi => hi.lc) hctxWF hlc
    simp only [List.append_nil] at hstepLC
    have hfix : ∀ k ∈ K, (pre ++ current).onTy (.fvar k) = .fvar k := by
      apply Subst.fixes_of_dom_avoids
      simpa only [List.append_nil] using hstep.dom_avoids
    have htailValid := recValid_subst (S := pre ++ current)
      (by simpa only [List.append_assoc, List.singleton_append] using hvalid :
        RecGroups.ValidResidualGroups (anns.map LetAnn.recModeAnn) (bindings.map Input.erase)
          ((past ++ [component]) ++ rest))
    have htailFrame : exported.Frame base K (substSoft (pre ++ current) F) ((pre ++ current).onCtx ctx)
        (anns.map (LetAnn.substTyFvars (pre ++ current))) (past ++ [component]).flatten := by
      simpa only [List.flatten_append, List.flatten_cons, List.flatten_nil, List.append_nil] using hstepFrame
    have hfinal := hr.sourceSound_of_infer
      (fun he hi => hInfer (by simpa only [sizeBindings_map_substTyFvars] using he) hi)
      htailValid htailFrame hstepLC.2 (Subst.onCtx_wf hstepLC.1 hctxWF)
      hstepBelow.2 (Subst.onCtx_below hstepBelow.1 (ho.frontier_le.trans hc.frontier_le) hctx)
      (substSoft_below hstepBelow.1 (ho.frontier_le.trans hc.frontier_le) hF)
      (by simp only [List.length_map]; have := ho.frontier_le; have := hc.frontier_le; omega)
      (by
        intro ann hm v hv
        obtain ⟨original, ho, rfl⟩ := List.mem_map.mp hm
        obtain ⟨k, hk, himage⟩ := LetAnn.rigidVars_substTyFvars hv
        exact scope_image hfix (hanns original ho k hk) himage)
      (by
        intro rhs hm
        obtain ⟨original, ho, rfl⟩ := List.mem_map.mp hm
        exact (show SourceScope K F original from hrhs original ho).subst (pre ++ current) hfix)
      (fun he hi => hSound (by simpa only [sizeBindings_map_substTyFvars] using he) hi)
      hstepSound
    simpa only [Subst.onCtx_append] using hfinal
 termination_by structural h



 theorem RecState.Frame.all_mono_done {state : RecState} {bindings : List Input}
    (h : state.Frame base K F ctx anns groups.flatten)
    (hv : RecGroups.ValidResidualGroups (anns.map LetAnn.recModeAnn) (bindings.map Input.erase) groups) :
    ∀ (i : Nat) (ty : Ty), state.specs[i]? = some (.mono ty) → i ∈ groups.flatten := by
  intro i ty hs
  have hm := congrArg (fun xs : List (Option PolyTy) => xs[i]?) h.modes
  dsimp only at hm
  simp only [List.getElem?_map, hs, Option.map_some, RecSpec.ann] at hm
  have hi : i < bindings.length := by
    have hb := (List.getElem?_eq_some_iff.mp hs).1
    have hl : anns.length = bindings.length := by simpa only [List.length_map] using hv.length
    simpa only [h.specs_length, hl] using hb
  exact (hv.covers_unsigned i (by simpa only [List.length_map] using hi)).mpr
    (by simpa only [RecGroups.UnsignedAt, List.getElem?_map] using hm.symm)

private theorem RecState.Frame.prefixes_mono {state : RecState} {i : Nat}
    (h : state.Frame base K F ctx anns done)
    (hs : state.specs[i]? = some (.mono ty)) (hd : i ∈ done) :
    ∃ names, state.prefixes[i]? = some names ∧
      names.length = (anns[i]?.getD .absent).recPrefixCount ∧ names.Nodup ∧
      (∀ v ∈ names, v ∈ state.pool) := by
  obtain ⟨names, hslots, hlen, hnd, hsub, _⟩ := if_pos hd ▸ h.mono i ty hs
  refine ⟨names, ?_, hlen, hnd, hsub⟩
  simp only [RecState.prefixes, List.getElem?_mapIdx, hs, Option.map_some, hslots, Option.getD_some]
  congr 1
  rw [List.filterMap_map]
  change (names.filterMap some) = names
  simp

private theorem RecState.Frame.prefixes_wf {state : RecState} {bindings : List Input}
    (h : state.Frame base K F ctx anns groups.flatten)
    (hg : RecGroups.ValidResidualGroups (anns.map LetAnn.recModeAnn) (bindings.map Input.erase) groups) :
    RecPrefixesWF anns state.specs state.prefixes state.pool := by
  refine ⟨by simp only [RecState.prefixes, List.length_mapIdx], ?_⟩
  intro i ann names ha hn
  have hi : i < state.specs.length := by
    simpa only [h.specs_length] using (List.getElem?_eq_some_iff.mp ha).1
  have hs := List.getElem?_eq_getElem hi
  cases hspec : state.specs[i] with
  | mono ty =>
    have hget : state.specs[i]? = some (.mono ty) := hspec ▸ hs
    obtain ⟨written, hp, hcount, hnd, hsub⟩ := h.prefixes_mono hget (h.all_mono_done hg _ _ hget)
    cases Option.some.inj (hp.symm.trans hn)
    exact ⟨by simpa only [ha, Option.getD_some] using hcount, hnd, hsub⟩
  | poly scheme =>
    have hget : state.specs[i]? = some (.poly scheme) := hspec ▸ hs
    have hp : state.prefixes[i]? = some [] := by
      simp only [RecState.prefixes, List.getElem?_mapIdx, hget, Option.map_some]
    cases Option.some.inj (hp.symm.trans hn)
    have hm := congrArg (fun xs : List (Option PolyTy) => xs[i]?) h.modes
    simp only [List.getElem?_map, hget, ha, Option.map_some, RecSpec.ann] at hm
    cases ann <;> simp_all [LetAnn.recModeAnn, LetAnn.recPrefixCount]

private theorem RecState.Frame.export_mono_prefixes {state : RecState} {i : Nat}
    (h : state.Frame base K F ctx anns done)
    (hs : state.specs[i]? = some (.mono ty)) (hd : i ∈ done) :
    state.exports[i]? = some (some (recScheme (state.prefixes[i]?.getD []) state.pool ty)) := by
  obtain ⟨names, hslots, _, _, _, hex⟩ := if_pos hd ▸ h.mono i ty hs
  have hp : state.prefixes[i]? = some names := by
    simp only [RecState.prefixes, List.getElem?_mapIdx, hs, Option.map_some, hslots, Option.getD_some]
    congr 1
    rw [List.filterMap_map]
    change names.filterMap some = names
    simp
  simpa only [hp, Option.getD_some] using hex

private theorem pool_renaming_lc {G Xs : List Nat} :
    ∀ p ∈ G.zip (Xs.map Ty.fvar), p.2.IsLC := by
  intro p hp
  obtain ⟨v, _, heq⟩ := List.mem_map.mp (List.of_mem_zip hp).2
  rw [← heq]
  exact .fvar

private theorem pool_renaming_image {G Xs : List Nat} (hG : G.Nodup) (hlen : Xs.length = G.length)
    (hGX : ∀ g ∈ G, g ∉ Xs) (hg : g ∈ G) :
    Subst.onTy (G.zip (Xs.map Ty.fvar)) (.fvar g) = .fvar ((Xs[G.idxOf g]?).getD g) := by
  have hi : G.idxOf g < Xs.length := by rw [hlen]; exact List.idxOf_lt_length_iff.mpr hg
  simpa only [List.getElem?_eq_getElem hi, Option.getD_some] using
    Ty.substFvars_zip_fvar_renameG hlen hG hGX (List.getElem?_idxOf hg) (List.getElem?_eq_getElem hi)

private theorem pool_renaming_images {G Xs names : List Nat} (hG : G.Nodup) (hlen : Xs.length = G.length)
    (hGX : ∀ g ∈ G, g ∉ Xs) (hn : ∀ g ∈ names, g ∈ G) :
    names.map (fun v => Subst.onTy (G.zip (Xs.map Ty.fvar)) (.fvar v)) =
      (recRenameNames G Xs names).map Ty.fvar := by
  simp only [recRenameNames, List.map_map]
  exact List.map_congr_left (fun v hv => pool_renaming_image hG hlen hGX (hn v hv))

private theorem recScheme_pool_fixed {G Xs names : List Nat} {ty : Ty} :
    Subst.onPolyTy (G.zip (Xs.map Ty.fvar)) (recScheme names G ty) = recScheme names G ty := by
  apply Subst.onPolyTy_eq_self_of_dom_avoids
  intro p hp hv
  exact Ty.not_mem_closeOver_freeVars
    (mem_recNames_of_mem_pool (List.of_mem_zip hp).1 (Ty.freeVars_closeOver_subset hv)) hv

private theorem RecState.Frame.stageCtx_rename {state : RecState} {earlier Xs : List Nat}
    (h : state.Frame base K F ctx anns done) (hdone : ∀ i ∈ earlier, i ∈ done) :
    Subst.onCtx (state.pool.zip (Xs.map Ty.fvar)) (state.stageCtx ctx earlier) =
      recStageCtx ctx state.specs state.prefixes earlier state.pool Xs := by
  have henv : Subst.onEnv (state.pool.zip (Xs.map Ty.fvar)) ctx.env = ctx.env :=
    Subst.onEnv_eq_self_of_fresh (fun p hp => h.pool_ctx p.1 (List.of_mem_zip hp).1)
  simp only [Subst.onCtx, RecState.stageCtx, recStageCtx, Subst.onEnv, List.map_append]
  congr 1
  congr 1
  · apply List.ext_getElem?
    intro i
    simp only [RecState.stageEntries, List.getElem?_map, List.getElem?_mapIdx, Option.map_map]
    cases hs : state.specs[i]? with
    | none => rfl
    | some spec =>
      simp only [Option.map_some, Option.some.injEq]
      cases spec with
      | poly scheme =>
        have hex := h.poly i scheme hs
        simp only [RecSpec.monoEntry, recStageEntry, hex, Option.join_some, Option.getD_some]
        have hfixed : Subst.onPolyTy (state.pool.zip (Xs.map Ty.fvar)) scheme = scheme :=
          Subst.onPolyTy_eq_self_of_dom_avoids (fun p hp => h.pool_poly scheme ⟨i, hs⟩ p.1 (List.of_mem_zip hp).1)
        split <;> exact hfixed
      | mono ty =>
        by_cases hi : i ∈ earlier
        · have hex := h.export_mono_prefixes hs (hdone i hi)
          simp only [hi, if_pos, hex, Option.join_some, Option.getD_some, recStageEntry]
          exact recScheme_pool_fixed
        · simp only [hi, RecSpec.monoEntry, recStageEntry]
          rfl

private theorem recFits_of_images {ann : LetAnn} {names fresh : List Nat} {ty : Ty} {R : Subst}
    (h : ann.RecFits names ty) (hR : ∀ p ∈ R, p.2.IsLC)
    (hfix : ∀ v ∈ ann.rigidVars, R.onTy (.fvar v) = .fvar v)
    (him : names.map (fun v => R.onTy (.fvar v)) = fresh.map Ty.fvar)
    (hlen : fresh.length = names.length) : ann.RecFits fresh (R.onTy ty) := by
  cases ann with
  | absent => trivial
  | complete sigma => exact False.elim h
  | template tpl =>
    have ht := h.substTyFvars R
    rw [tpl.substTyFvars_eq_self_of_fixes hfix] at ht
    exact ht
  | partialForall count tpl =>
    refine ⟨hlen.trans h.1, ?_⟩
    have ht := h.2.substTyFvars R
    rw [Template.substTyFvars_openTyVarsFrom_of_images tpl hR him 0,
      tpl.substTyFvars_eq_self_of_fixes hfix] at ht
    exact ht

private theorem RecState.InputTrace.cofinite {state : RecState} {bindings : List Input}
    (h : state.InputTrace (K ++ softVars F) ctx anns bindings groups)
    (hf : state.Frame base K F ctx anns groups.flatten)
    (hvalid : RecGroups.ValidResidualGroups (anns.map LetAnn.recModeAnn) (bindings.map Input.erase) groups)
    (hAnn : ∀ ann ∈ anns, ∀ v ∈ ann.rigidVars, v ∈ K ++ softVars F)
    (hRhs : ∀ rhs ∈ bindings, ∀ v ∈ rhs.rigidVars, v ∈ K ++ softVars F)
    {stage : Nat} {component : List Nat} (hc : groups[stage]? = some component)
    (Xs : List Nat) (hXs : FreshNames (state.pool ++ L) state.pool.length Xs)
    {i : Nat} {rhs : Input} {ann : LetAnn} {names : List Nat} {ty : Ty}
    (hi : i ∈ component) (hr : bindings[i]? = some rhs) (ha : anns[i]? = some ann)
    (hn : state.prefixes[i]? = some names) (ht : state.specs[i]? = some (.mono ty)) :
    ann.RecFits (recRenameNames state.pool Xs names) (Ty.renameG state.pool Xs ty) ∧
    Typing ((K ++ softVars F) ++ Xs)
      (recStageCtx ctx state.specs state.prefixes (groups.take stage).flatten state.pool Xs)
      (rhs.openTyVars (recRenameNames state.pool Xs names)) (Ty.renameG state.pool Xs ty) := by
  let R : Subst := state.pool.zip (Xs.map Ty.fvar)
  have hRlc : ∀ p ∈ R, p.2.IsLC := pool_renaming_lc
  have hGX : ∀ g ∈ state.pool, g ∉ Xs := fun g hg hx =>
    hXs.avoid g hx (List.mem_append_left _ hg)
  have hQavoid : ∀ g ∈ state.pool, g ∉ K ++ softVars F := by
    intro g hg hm
    exact (List.mem_append.mp hm).elim (hf.pool_rigid g hg) (hf.pool_soft g hg)
  have hQfix : ∀ q ∈ K ++ softVars F, R.onTy (.fvar q) = .fvar q :=
    Subst.fixes_of_dom_avoids (fun p hp => hQavoid p.1 (List.of_mem_zip hp).1)
  obtain ⟨hfit, htyped⟩ := h stage component hc i ann rhs ty hi ha hr ht
  simp only [hn, Option.getD_some] at hfit htyped
  have hprefix := (hf.prefixes_wf hvalid).member i ann names ha hn
  have himages := pool_renaming_images hf.pool_nodup hXs.length hGX hprefix.2.2
  have hfixAnn : ∀ v ∈ ann.rigidVars, R.onTy (.fvar v) = .fvar v :=
    fun v hv => hQfix v (hAnn ann (List.mem_of_getElem? ha) v hv)
  refine ⟨recFits_of_images hfit hRlc hfixAnn himages (recRenameNames_length _ _ _), ?_⟩
  have hsource := htyped.onSubst_source R hRlc (K' := (K ++ softVars F) ++ Xs) (by
    intro k hk v hv
    rcases List.mem_append.mp hk with hk | hk
    · rw [hQfix k hk] at hv
      exact List.mem_append_left _ ((List.mem_singleton.mp hv) ▸ hk)
    · have hkG := hprefix.2.2 k hk
      have hindex : state.pool.idxOf k < Xs.length := by
        rw [hXs.length]; exact List.idxOf_lt_length_iff.mpr hkG
      rw [pool_renaming_image hf.pool_nodup hXs.length hGX hkG,
        List.getElem?_eq_getElem hindex, Option.getD_some] at hv
      exact List.mem_append_right _ ((List.mem_singleton.mp hv) ▸ List.getElem_mem hindex))
  have hstage := hf.stageCtx_rename (Xs := Xs) (earlier := (groups.take stage).flatten) (by
    intro j hj
    obtain ⟨component, hm, hj⟩ := List.mem_flatten.mp hj
    exact List.mem_flatten.mpr ⟨component, List.mem_of_mem_take hm, hj⟩)
  rw [hstage, rhs.substTyFvars_openTyVars_of_images hRlc himages,
    rhs.substTyFvars_eq_self_of_fixes (fun v hv => hQfix v (hRhs rhs (List.mem_of_getElem? hr) v hv))] at hsource
  exact hsource

 theorem RecState.InputTrace.toTyping {state : RecState} {bindings : List Input} {L : List Nat}
    (hf : state.Frame base K F ctx anns groups.flatten) (hlc : state.LC)
    (hvalid : RecGroups.ValidResidualGroups (anns.map LetAnn.recModeAnn) (bindings.map Input.erase) groups)
    (hAnn : ∀ ann ∈ anns, ∀ v ∈ ann.rigidVars, v ∈ K ++ softVars F)
    (hRhs : ∀ rhs ∈ bindings, ∀ v ∈ rhs.rigidVars, v ∈ K ++ softVars F)
    (htrace : state.InputTrace (K ++ softVars F) ctx anns bindings groups)
    (hpoly : ∀ (i : Nat) (rhs : Input) (scheme : PolyTy), bindings[i]? = some rhs →
      state.specs[i]? = some (.poly scheme) → ∀ Ys, FreshNames L scheme.paramCount Ys →
        Typing ((K ++ softVars F) ++ Ys) (recBodyCtx ctx state.specs state.prefixes state.pool)
          (rhs.openTyVars Ys) (scheme.openVars Ys))
    (hbody : Typing (K ++ softVars F) (recBodyCtx ctx state.specs state.prefixes state.pool) body ty) :
    Typing (K ++ softVars F) ctx (.letRec anns bindings body) ty := by
  have hwf : RecSpecs.WF (anns.map LetAnn.recModeAnn) (bindings.map Input.erase) state.specs state.pool := by
    refine ⟨hf.modes, ?_, hf.pool_nodup, fun ty ht => hlc.1 _ ht, fun scheme hs => hlc.1 _ hs⟩
    rw [List.length_map, hf.specs_length]
    exact (show anns.length = bindings.length by simpa only [List.length_map] using hvalid.length).symm
  refine Typing.letRec (specs := state.specs) (prefixes := state.prefixes) (groups := groups)
    (G := state.pool) (L := L) hvalid hwf (hf.prefixes_wf hvalid) ?_ hAnn hRhs ?_ ?_ hpoly hbody
  · intro g hg hm
    rcases List.mem_append.mp hm with hm | hm
    · exact hf.pool_ctx g hg hm
    · exact (List.mem_append.mp hm).elim (hf.pool_rigid g hg) (hf.pool_soft g hg)
  · intro stage component hc Xs hXs i hi rhs ann names ty hr ha hn ht
    exact (htrace.cofinite hf hvalid hAnn hRhs hc Xs hXs hi hr ha hn ht).1
  · intro stage component hc Xs hXs i hi rhs ann names ty hr ha hn ht
    exact (htrace.cofinite hf hvalid hAnn hRhs hc Xs hXs hi hr ha hn ht).2


private theorem trace_prefix_lookup {state : RecState} {i : Nat} {ty : Ty} {names : List Nat}
    (hs : state.specs[i]? = some (.mono ty))
    (hn : state.slots[i]? = some (names.map Ty.fvar)) :
    state.prefixes[i]? = some names := by
  simp only [RecState.prefixes, List.getElem?_mapIdx, hs, Option.map_some, hn, Option.getD_some]
  congr 1
  clear hs hn
  induction names with
  | nil => rfl
  | cons n ns ih => change n :: _ = n :: _; exact congrArg (n :: ·) ih

 theorem RecState.InputTrace.onSubst {state : RecState} {past : List (List Nat)}
    (hframe : state.Frame base K F ctx anns past.flatten)
    (h : state.InputTrace (K ++ softVars F) ctx anns bindings past)
    (S : Subst) (hlc : ∀ p ∈ S, p.2.IsLC)
    (hK : ∀ k ∈ K, S.onTy (.fvar k) = .fvar k)
    (hpool : ∀ g ∈ state.pool, (∀ p ∈ S, g ∉ p.2.freeVars) ∧ g ∉ S.map Prod.fst) :
    (state.onSubst S).InputTrace (K ++ softVars (substSoft S F)) (S.onCtx ctx)
      (anns.map (LetAnn.substTyFvars S)) (bindings.map (Input.substTyFvars S)) past := by
  intro stage component hc i ann rhs ty hi ha hr ht
  obtain ⟨ann0, ha0, rfl⟩ := Option.map_eq_some_iff.mp (by simpa only [List.getElem?_map] using ha)
  obtain ⟨rhs0, hr0, rfl⟩ := Option.map_eq_some_iff.mp (by simpa only [List.getElem?_map] using hr)
  obtain ⟨ty0, ht0, rfl⟩ := RecSpec.mono_getElem?_map_onSubstSource ht
  have hidone : i ∈ past.flatten := List.mem_flatten.mpr ⟨component, List.mem_of_getElem? hc, hi⟩
  obtain ⟨names, hnames, _, _, hsub, _⟩ := if_pos hidone ▸ hframe.mono i ty0 ht0
  have hfix : ∀ v ∈ names, S.onTy (.fvar v) = .fvar v := by
    intro v hv
    apply Ty.substFvars_eq_self_of_no_key
    intro pair hp hk
    have heq : pair.1 = v := List.mem_singleton.mp hk
    exact (hpool v (hsub v hv)).2 (List.mem_map.mpr ⟨pair, hp, heq⟩)
  have hnewnames : (state.onSubst S).slots[i]? = some (names.map Ty.fvar) := by
    simp only [RecState.onSubst, List.getElem?_map, hnames, Option.map_some, List.map_map]
    congr 1
    exact List.map_congr_left (fun v hv => hfix v hv)
  have hprefix := trace_prefix_lookup ht0 hnames
  have hnewprefix := trace_prefix_lookup ht hnewnames
  obtain ⟨hfits, htyping⟩ := h stage component hc i ann0 rhs0 ty0 hi ha0 hr0 ht0
  simp only [hprefix, Option.getD_some] at hfits htyping
  simp only [hnewprefix, Option.getD_some]
  refine ⟨hfits.onSubst_source S hlc hfix, ?_⟩
  have htypingS := htyping.onSubst_source S hlc (K' := (K ++ softVars (substSoft S F)) ++ names)
    (fun k hk v hv => by
      rcases List.mem_append.mp hk with hk | hk
      · exact List.mem_append_left _ (scope_image hK hk hv)
      · rw [hfix k hk] at hv
        exact List.mem_append_right _ ((List.mem_singleton.mp hv) ▸ hk))
  rw [RecState.stageCtx_onSubst]
  simpa only [Input.substTyFvars_openTyVars_of_fixes _ hlc hfix] using htypingS


 theorem _root_.InferRecComponent.inputSound_of_infer
    (h : InferRecComponent K F members index frontier ctx bindings specs next S outputs facts)
    (hInfer : ∀ {κ F' Ψ c e Ψ' T output ty}, e.size ≤ sizeBindings bindings →
      Infer κ F' Ψ c e Ψ' T output ty → CtxWF c →
      Typing (κ ++ softVars (substSoft T F')) (T.onCtx c) (e.substTyFvars T) ty)
    (hctx : CtxWF ctx) (hspec : ∀ spec ∈ specs, spec.LC) :
    ∀ (j : Nat) (rhs : Input) (target : Ty), index + j ∈ members →
      bindings[j]? = some rhs → specs[j]? = some (.mono target) →
      Typing (K ++ softVars (substSoft S F)) (S.onCtx ctx)
        (rhs.substTyFvars S) (S.onTy target) := by
  match h with
  | .nil => intro j rhs target _ hr; simp at hr
  | .skipMono hn hr =>
    intro j rhs target hj hb ht
    cases j with
    | zero => exact False.elim (hn (by simpa only [Nat.add_zero] using hj))
    | succ j =>
      exact hr.inputSound_of_infer
        (fun he hi => hInfer (by simp only [sizeBindings]; omega) hi)
        hctx (fun spec hm => hspec spec (List.mem_cons_of_mem _ hm)) j rhs target
        (by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hj) hb ht
  | .skipPoly hr =>
    intro j rhs target hj hb ht
    cases j with
    | zero => cases ht
    | succ j =>
      exact hr.inputSound_of_infer
        (fun he hi => hInfer (by simp only [sizeBindings]; omega) hi)
        hctx (fun spec hm => hspec spec (List.mem_cons_of_mem _ hm)) j rhs target
        (by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hj) hb ht
  | .consSelected hm hi hu hr =>
    expose_names
    obtain ⟨hiTy, hiS⟩ := hi.lc hctx
    have huS := hu.unifies.lc hiTy (Subst.onTy_lc hiS (hspec _ List.mem_cons_self))
    have hS12 : ∀ p ∈ s1 ++ s2, p.2.IsLC := fun p hp => (List.mem_append.mp hp).elim (hiS p) (huS p)
    have hrCtx := Subst.onCtx_wf huS (Subst.onCtx_wf hiS hctx)
    have hrSpec : ∀ spec ∈ specs_1.map (RecSpec.onSubstSource (s1 ++ s2)), spec.LC := by
      intro spec hm
      obtain ⟨old, hold, rfl⟩ := List.mem_map.mp hm
      exact RecSpec.lc_onSubstSource hS12 (hspec old (List.mem_cons_of_mem _ hold))
    have hrLC := hr.lc_of_infer (fun _ hi => hi.lc) hrCtx hrSpec
    intro j rhs target hj hb ht
    cases j with
    | zero =>
      cases Option.some.inj hb
      cases Option.some.inj ht
      have hrestLC : ∀ p ∈ s2 ++ s3, p.2.IsLC := fun p hp => (List.mem_append.mp hp).elim (huS p) (hrLC p)
      have hrestFix : ∀ k ∈ K, (s2 ++ s3).onTy (.fvar k) = .fvar k :=
        Subst.fixes_of_dom_avoids (fun p hp => (List.mem_append.mp hp).elim (hu.dom_avoids p) (hr.dom_avoids p))
      have htyping := (hInfer (by simp only [sizeBindings]; omega) hi hctx).onSubst_source (s2 ++ s3) hrestLC
        (fun k hk v hv => scope_image hrestFix hk hv)
      have heq := congrArg s3.onTy hu.unifies.unifies
      rw [Subst.onTy_append] at htyping
      rw [heq] at htyping
      simpa only [Subst.onCtx_append, Subst.onTy_append, List.append_assoc,
        ← substSoft_append, ← Input.substTyFvars_append] using htyping
    | succ j =>
      simp only [List.getElem?_cons_succ] at hb ht
      have htail := hr.inputSound_of_infer
        (fun he hi => hInfer (by simp only [sizeBindings_map_substTyFvars] at he; simp only [sizeBindings]; omega) hi)
        hrCtx hrSpec j (rhs.substTyFvars (s1 ++ s2)) ((s1 ++ s2).onTy target)
        (by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hj)
        (by simp only [List.getElem?_map, hb, Option.map_some])
        (by simp only [List.getElem?_map, ht, Option.map_some, RecSpec.onSubstSource])
      simpa only [← substSoft_append, Subst.onCtx_append, Subst.onTy_append, ← Input.substTyFvars_append] using htail
 termination_by structural h


end Elaboration
