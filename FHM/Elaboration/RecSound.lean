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


end Elaboration
