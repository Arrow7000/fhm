import FHM.Elaboration.Properties
import FHM.Elaboration.RecSound

theorem RecGroup.inferenceSccs_congr_mask
    {anns anns' : List (Option PolyTy)} (bindings : List Expr)
    (hmask : ∀ i, RecGroup.isUnsignedAt anns i = RecGroup.isUnsignedAt anns' i) :
    RecGroup.inferenceSccs anns bindings = RecGroup.inferenceSccs anns' bindings := by
  have hm : (fun i => RecGroup.isUnsignedAt anns i) =
      (fun i => RecGroup.isUnsignedAt anns' i) := funext hmask
  have hs : ∀ i, RecGroup.inferenceSucc anns bindings i =
      RecGroup.inferenceSucc anns' bindings i := by
    intro i
    simp only [RecGroup.inferenceSucc, hmask i]
    split
    · cases bindings[i]? <;> simp only [hm]
    · rfl
  have hg : RecGroup.inferenceDigraph anns bindings =
      RecGroup.inferenceDigraph anns' bindings := by
    unfold RecGroup.inferenceDigraph
    congr 1
    funext i
    rw [hs]
  change ((Scc.rankedSccs (RecGroup.inferenceDigraph anns bindings)).map
      (fun component => (component.map Fin.val).filter (fun i => RecGroup.isUnsignedAt anns i))).filter
      (!·.isEmpty) = _
  rw [hg]
  change _ = ((Scc.rankedSccs (RecGroup.inferenceDigraph anns' bindings)).map
      (fun component => (component.map Fin.val).filter (fun i => RecGroup.isUnsignedAt anns' i))).filter
      (!·.isEmpty)
  rw [hm]

namespace Elaboration
theorem LetAnn.recModeAnn_isUnsignedAt_subst (anns : List LetAnn) (S : Subst) (i : Nat) :
    RecGroup.isUnsignedAt (anns.map LetAnn.recModeAnn) i =
      RecGroup.isUnsignedAt ((anns.map (LetAnn.substTyFvars S)).map LetAnn.recModeAnn) i := by
  simp only [RecGroup.isUnsignedAt, List.getElem?_map]
  cases anns[i]? with
  | none => rfl
  | some ann => cases ann <;> rfl

theorem Input.inferenceSccs_substTyFvars (anns : List LetAnn) (bindings : List Input) (S : Subst) :
    RecGroup.inferenceSccs (anns.map LetAnn.recModeAnn) (bindings.map Input.erase) =
      RecGroup.inferenceSccs ((anns.map (LetAnn.substTyFvars S)).map LetAnn.recModeAnn)
        ((bindings.map (Input.substTyFvars S)).map Input.erase) := by
  have hb : (bindings.map (Input.substTyFvars S)).map Input.erase = bindings.map Input.erase := by
    simp only [List.map_map, Function.comp_def, Input.erase_substTyFvars]
  rw [hb]
  exact RecGroup.inferenceSccs_congr_mask _ (LetAnn.recModeAnn_isUnsignedAt_subst anns S)

theorem Input.inferenceSccs_substInputBindings (anns : List LetAnn) (bindings : List Input) (S : Subst) :
    RecGroup.inferenceSccs (anns.map LetAnn.recModeAnn) (bindings.map Input.erase) =
      RecGroup.inferenceSccs ((anns.map (LetAnn.substTyFvars S)).map LetAnn.recModeAnn)
        ((substInputBindings S bindings).map Input.erase) := by
  have hb : substInputBindings S bindings = bindings.map (Input.substTyFvars S) := by
    induction bindings with
    | nil => rfl
    | cons rhs rest ih => simp only [substInputBindings, List.map_cons, ih]
  rw [hb]
  exact Input.inferenceSccs_substTyFvars anns bindings S
end Elaboration

namespace Elaboration


mutual
theorem Template.toCore_fits {template : Template} {ty : Ty}
    (h : template.toCore = some ty) : template.Fits ty := by
  cases template with
  | fixed => cases h; exact .fixed
  | hole => cases h
  | arrow a b =>
    simp only [Template.toCore, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨ta, ha, tb, hb, rfl⟩ := h
    exact .arrow (Template.toCore_fits ha) (Template.toCore_fits hb)
  | custom name args =>
    simp only [Template.toCore, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨tys, ht, rfl⟩ := h
    exact .custom (completeTypes_fits ht)
theorem completeTypes_fits {templates : List Template} {tys : List Ty}
    (h : completeTypes templates = some tys) : List.Forall₂ Template.Fits templates tys := by
  cases templates with
  | nil => cases h; exact .nil
  | cons t ts =>
    simp only [completeTypes, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨ty, ht, tys, hts, rfl⟩ := h
    exact .cons (Template.toCore_fits ht) (completeTypes_fits hts)
end

mutual
theorem Template.Fits.toCore_eq {template : Template} {ty complete : Ty}
    (h : template.Fits ty) (hc : template.toCore = some complete) : ty = complete := by
  cases h with
  | fixed => cases hc; rfl
  | hole => cases hc
  | arrow ha hb =>
    simp only [Template.toCore, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at hc
    obtain ⟨ta, hta, tb, htb, rfl⟩ := hc
    rw [ha.toCore_eq hta, hb.toCore_eq htb]
  | custom h =>
    simp only [Template.toCore, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at hc
    obtain ⟨tys, htys, rfl⟩ := hc
    rw [fitsList_toCore_eq h htys]
theorem fitsList_toCore_eq {templates : List Template} {tys complete : List Ty}
    (h : List.Forall₂ Template.Fits templates tys)
    (hc : completeTypes templates = some complete) : tys = complete := by
  cases h with
  | nil => cases hc; rfl
  | cons hh ht =>
    simp only [completeTypes, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at hc
    obtain ⟨ty, hty, tys, htys, rfl⟩ := hc
    rw [hh.toCore_eq hty, fitsList_toCore_eq ht htys]
end

private theorem completeBranches_length {inputs : List (MatchPattern × Input)}
    {cores : List (MatchPattern × Expr)} (h : completeBranches inputs = some cores) :
    inputs.length = cores.length := by
  induction inputs generalizing cores with
  | nil => cases h; rfl
  | cons head rest ih =>
    rcases head with ⟨pat, body⟩
    simp only [completeBranches, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨body', _, rest', hr, rfl⟩ := h
    simp only [List.length_cons, ih hr]

private theorem completeBranches_forward {inputs : List (MatchPattern × Input)}
    {cores : List (MatchPattern × Expr)} (h : completeBranches inputs = some cores)
    {branch : MatchPattern × Input} (hb : branch ∈ inputs) :
    ∃ core, (branch.1, core) ∈ cores ∧ branch.2.toCore = some core := by
  induction inputs generalizing cores with
  | nil => cases hb
  | cons head rest ih =>
    rcases head with ⟨pat, body⟩
    simp only [completeBranches, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨body', hh, rest', hr, rfl⟩ := h
    rcases List.mem_cons.mp hb with rfl | hb
    · exact ⟨body', List.mem_cons_self, hh⟩
    · obtain ⟨core, hc, heq⟩ := ih hr hb
      exact ⟨core, List.mem_cons_of_mem _ hc, heq⟩

private theorem completeBranches_backward {inputs : List (MatchPattern × Input)}
    {cores : List (MatchPattern × Expr)} (h : completeBranches inputs = some cores)
    {branch : MatchPattern × Expr} (hb : branch ∈ cores) :
    ∃ body, (branch.1, body) ∈ inputs ∧ body.toCore = some branch.2 := by
  induction inputs generalizing cores with
  | nil => cases h; cases hb
  | cons head rest ih =>
    rcases head with ⟨pat, body⟩
    simp only [completeBranches, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨body', hh, rest', hr, rfl⟩ := h
    rcases List.mem_cons.mp hb with rfl | hb
    · exact ⟨body, List.mem_cons_self, hh⟩
    · obtain ⟨source, hs, heq⟩ := ih hr hb
      exact ⟨source, List.mem_cons_of_mem _ hs, heq⟩

private theorem branchFreeVars_iff {branches : List (MatchPattern × Expr)} {v : Nat} :
    v ∈ Expr.tyFreeVars.BranchList.tyFreeVars branches ↔
      ∃ branch ∈ branches, v ∈ branch.2.tyFreeVars := by
  induction branches with
  | nil => simp [Expr.tyFreeVars.BranchList.tyFreeVars]
  | cons head rest ih =>
    rcases head with ⟨pat, body⟩
    simp only [Expr.tyFreeVars.BranchList.tyFreeVars, List.mem_append, ih, List.mem_cons]
    constructor
    · rintro (hv | ⟨b, hb, hv⟩)
      · exact ⟨_, Or.inl rfl, hv⟩
      · exact ⟨b, Or.inr hb, hv⟩
    · rintro ⟨b, rfl | hb, hv⟩
      · exact Or.inl hv
      · exact Or.inr ⟨b, hb, hv⟩

private theorem recGroupRefs_erase (e : Expr) (n depth : Nat) :
    e.erase.recGroupRefs n depth = e.recGroupRefs n depth := by
  induction e using Expr.rec_strong generalizing depth with
  | primLit | primBinOp | ctor | var => simp only [Expr.erase]
  | lambda ann body ih => simpa only [Expr.erase, Expr.recGroupRefs] using ih _
  | app f a ihf iha => simp only [Expr.erase, Expr.recGroupRefs, ihf, iha]
  | letIn ann rhs body ihr ihb => simp only [Expr.erase, Expr.recGroupRefs, ihr, ihb]
  | match_ scrut branches ihs ihbr =>
    simp only [Expr.erase_match, Expr.recGroupRefs, ihs]
    congr 2
    induction branches with
    | nil => rfl
    | cons pb rest ih =>
      simp only [List.map_cons, RecGroupRefs.branches]
      rw [ihbr pb.1 pb.2 List.mem_cons_self, ih (fun p b h => ihbr p b (List.mem_cons_of_mem _ h))]
  | letRec anns bindings body ihbs ihb =>
    simp only [Expr.erase_letRec, Expr.recGroupRefs, List.length_map, ihb]
    congr 2
    generalize depth + bindings.length = innerDepth
    induction bindings generalizing innerDepth with
    | nil => rfl
    | cons rhs rest ih =>
      simp only [List.map_cons, RecGroupRefs.bindings]
      rw [ihbs rhs List.mem_cons_self, ih (fun e h => ihbs e (List.mem_cons_of_mem _ h)) innerDepth]

private theorem validResidualGroups_erase_iff {anns : List (Option PolyTy)} {bindings : List Expr} :
    RecGroups.ValidResidualGroups anns (bindings.map Expr.erase) groups ↔
      RecGroups.ValidResidualGroups anns bindings groups := by
  constructor
  · intro h
    refine ⟨by simpa using h.length, h.nonempty, h.flatten_nodup,
      by simpa using h.bounded, ?_, ?_⟩
    · intro member hm
      exact h.covers_unsigned member (by simpa using hm)
    · intro stage depStage component depComponent source target rhs hc hd hs ht hr href
      apply h.dependencies_first hc hd hs ht
        (by rw [List.getElem?_map, hr]; rfl)
      simpa only [List.length_map, recGroupRefs_erase] using href
  · intro h
    exact h.map_bindings Expr.erase rfl (fun _ => Iff.rfl) (fun e _ => recGroupRefs_erase e _ _)

private theorem completeBindings_length {inputs : List Input} {cores : List Expr}
    (h : completeBindings inputs = some cores) : inputs.length = cores.length := by
  have hh := congrArg List.length (completeBindings_erase inputs h)
  simpa only [List.length_map, eraseBindings_length] using hh.symm

private theorem completeBindings_lookup {inputs : List Input} {cores : List Expr}
    (h : completeBindings inputs = some cores) {i : Nat} {rhs : Input}
    (hr : inputs[i]? = some rhs) : ∃ core, cores[i]? = some core ∧ rhs.toCore = some core := by
  induction inputs generalizing cores i with
  | nil => cases hr
  | cons head rest ih =>
    simp only [completeBindings, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨core, hh, cores, ht, rfl⟩ := h
    cases i with
    | zero => cases hr; exact ⟨core, rfl, hh⟩
    | succ i => exact ih ht hr

private theorem completeBindings_lookup_back {inputs : List Input} {cores : List Expr}
    (h : completeBindings inputs = some cores) {i : Nat} {core : Expr}
    (hr : cores[i]? = some core) : ∃ rhs, inputs[i]? = some rhs ∧ rhs.toCore = some core := by
  induction inputs generalizing cores i with
  | nil => cases h; cases hr
  | cons head rest ih =>
    simp only [completeBindings, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨core0, hh, cores, ht, rfl⟩ := h
    cases i with
    | zero => cases hr; exact ⟨head, rfl, hh⟩
    | succ i => exact ih ht hr

private theorem completeAnns_data {anns : List LetAnn} {cores : List (Option PolyTy)}
    (h : completeAnns anns = some cores) : cores = anns.map LetAnn.recModeAnn ∧
      ∀ ann ∈ anns, ann.toCore = some ann.recModeAnn ∧ ann.recPrefixCount = 0 := by
  induction anns generalizing cores with
  | nil => cases h; exact ⟨rfl, by simp⟩
  | cons ann rest ih =>
    simp only [completeAnns, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨core, ha, cores, ht, rfl⟩ := h
    obtain ⟨heq, hall⟩ := ih ht
    cases ann with
    | template | partialForall => cases ha
    | absent | complete =>
      cases ha
      refine ⟨by rw [heq]; rfl, ?_⟩
      intro ann hm
      rcases List.mem_cons.mp hm with rfl | hm
      · exact ⟨rfl, rfl⟩
      · exact hall ann hm

private theorem eraseBindings_eq_map_rec (bindings : List Input) :
    eraseBindings bindings = bindings.map Input.erase := by
  induction bindings with
  | nil => rfl
  | cons rhs rest ih => simp only [eraseBindings, List.map_cons, ih]

private theorem recScheme_empty (G : List Nat) (ty : Ty) : recScheme [] G ty = PolyTy.genGroup G ty := by
  simp [recScheme, recNames, PolyTy.genGroup, Ty.genFilter]

private theorem recCompleted_empty_prefixes (specs : List RecSpec) (prefixes : List (List Nat)) (G : List Nat)
    (hp : ∀ i : Nat, prefixes[i]?.getD [] = []) :
    recCompletedSchemes specs prefixes G = specs.map (RecSpec.bodyScheme G) := by
  apply List.ext_get (by simp [recCompletedSchemes])
  intro i hi hj
  simp only [recCompletedSchemes, List.get_eq_getElem, List.getElem_mapIdx, List.getElem_map, hp]
  cases specs[i]'(by simpa using hj) <;> simp only [RecSpec.completedScheme, RecSpec.bodyScheme, recScheme_empty]

private theorem recStage_empty_prefixes (ctx : Ctx) (specs : List RecSpec) (prefixes : List (List Nat)) (done G Xs : List Nat)
    (hp : ∀ i : Nat, prefixes[i]?.getD [] = []) :
    recStageCtx ctx specs prefixes done G Xs = RecSpecs.stageCtx ctx specs done G Xs := by
  unfold recStageCtx RecSpecs.stageCtx
  congr 2
  apply List.ext_get (by simp)
  intro i hi hj
  simp only [List.get_eq_getElem, List.getElem_mapIdx]
  cases specs[i]'(by simpa using hj) <;>
    simp only [recStageEntry, RecSpec.stageEntry, hp, recScheme_empty]

private theorem complete_prefixes_empty {anns : List LetAnn} {specs : List RecSpec}
    (hp : RecPrefixesWF anns specs prefixes G) (hlen : anns.length = specs.length)
    (hz : ∀ ann ∈ anns, ann.recPrefixCount = 0) : ∀ i : Nat, prefixes[i]?.getD [] = [] := by
  intro i
  cases hn : prefixes[i]? with
  | none => rfl
  | some names =>
    have hi : i < anns.length := by
      have := (List.getElem?_eq_some_iff.mp hn).1
      rw [hp.length] at this
      omega
    have hh := (hp.member i anns[i] names (List.getElem?_eq_getElem hi) hn).1
    rw [hz anns[i] (List.getElem_mem hi)] at hh
    exact List.length_eq_zero_iff.mp hh

private theorem core_openTyVars_nil (e : Expr) : e.openTyVars [] = e := by
  rw [← Expr.instTy_fvar_eq_openTyVars]
  exact Expr.instTy_nil e

/-- The independent rules conservatively recover ordinary typing whenever the
input is already complete. This retains complete annotations and recursion. -/
theorem Typing.toCore (h : Typing K ctx input ty) {core : Expr}
    (hc : input.toCore = some core) :
    TypeOfHM ctx core ty ∧ (∀ v ∈ core.tyFreeVars, v ∈ K) := by
  induction h using Typing.rec
      (motive_2 := fun K ctx branch scrutTy resultTy _ =>
        ∀ {body : Expr}, branch.2.toCore = some body →
          TypeOfMatchBranch ctx (branch.1, body) scrutTy resultTy ∧
            (∀ v ∈ body.tyFreeVars, v ∈ K)) generalizing core with
  | complete hemb hscope ht => cases hemb.symm.trans hc; exact ⟨ht, hscope⟩
  | primLit ht => cases hc; exact ⟨ht, by simp [Expr.tyFreeVars]⟩
  | primBinOp ht => cases hc; exact ⟨ht, by simp [Expr.tyFreeVars]⟩
  | @lambda ann _ _ body _ param hlc hfits hrigid _ ih =>
    simp only [Input.toCore, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at hc
    obtain ⟨ann', ha, body', hb, rfl⟩ := hc
    obtain ⟨ht, hs⟩ := ih hb
    have hpin : ann'.Pins param := by
      cases ann with
      | none => cases ha; intro a h; cases h
      | some template =>
        simp only [completeLambdaAnn, bind, pure, Option.bind_eq_some_iff,
          Option.some.injEq] at ha
        obtain ⟨t, ht, rfl⟩ := ha
        intro a ha
        cases ha
        exact (hfits template rfl).toCore_eq ht
    refine ⟨.lambda hlc hpin rfl ht, ?_⟩
    intro v hv
    rcases List.mem_append.mp hv with hv | hv
    · cases ann with
      | none => cases ha; cases hv
      | some template =>
        simp only [completeLambdaAnn, bind, pure, Option.bind_eq_some_iff,
          Option.some.injEq] at ha
        obtain ⟨t, ht, rfl⟩ := ha
        exact hrigid template rfl v ((Template.toCore_rigidVars ht v).mpr hv)
    · exact hs v hv
  | app _ _ ihf ihx =>
    simp only [Input.toCore, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at hc
    obtain ⟨f, hf, x, hx, rfl⟩ := hc
    obtain ⟨htf, hsf⟩ := ihf hf
    obtain ⟨htx, hsx⟩ := ihx hx
    exact ⟨.app htf htx, fun v hv => (List.mem_append.mp hv).elim (hsf v) (hsx v)⟩
  | @letIn ann _ _ rhs body _ M L hwf _ hfits _ _ ihr ihb =>
    simp only [Input.toCore, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at hc
    obtain ⟨ann', ha, rhs', hr, body', hb, rfl⟩ := hc
    obtain ⟨Xs, hlen, hnd, hav⟩ := exists_fresh_names L M.paramCount
    have hXs : FreshNames L M.paramCount Xs := ⟨hlen, hnd, hav⟩
    have hfit := hfits Xs hXs
    cases ann with
    | complete => contradiction
    | partialForall => contradiction
    | template => cases ha
    | absent =>
      cases ha
      obtain ⟨htb, hsb⟩ := ihb hb
      refine ⟨.letIn hwf (by intro a h; cases h) (fun Ys hYs => (ihr Ys hYs hr).1) rfl htb, ?_⟩
      intro v hv
      rcases List.mem_append.mp hv with hv | hv
      · exact (ihr Xs hXs hr).2 v hv
      · exact hsb v hv
  | @letSignature K ctx body bodyTy ann rhs M L hwf hann hrhs hfits _ _ ihr ihb =>
    simp only [Input.toCore, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at hc
    obtain ⟨ann', ha, rhs', hr, body', hb, rfl⟩ := hc
    obtain ⟨Xs, hlen, hnd, hav⟩ := exists_fresh_names L M.paramCount
    have hXs : FreshNames L M.paramCount Xs := ⟨hlen, hnd, hav⟩
    have hfit := hfits Xs hXs
    cases ann with
    | absent => cases hfit
    | template => cases hfit
    | partialForall => cases ha
    | complete scheme =>
      cases ha
      cases hfit
      obtain ⟨htb, hsb⟩ := ihb hb
      refine ⟨.letIn (L := L) hwf (fun _ heq => Option.some.inj heq) ?_ rfl htb, ?_⟩
      · intro fresh hf
        have htake : fresh.take M.paramCount = fresh := by
          exact List.take_of_length_le hf.length.le
        have hemb := rhs.toCore_openTyVars hr (fresh.take M.paramCount)
        have ht := (ihr fresh hf hemb).1
        simpa only [htake, Expr.openBoundTyVars] using ht
      · intro v hv
        rcases List.mem_append.mp hv with hprefix | hv
        · rcases List.mem_append.mp hprefix with hv | hv
          · exact hann v hv
          · exact hrhs v ((Input.toCore_rigidVars rhs hr v).mpr hv)
        · exact hsb v hv
  | var hlook hlc hinst => cases hc; exact ⟨.var hlook hlc hinst, by simp [Expr.tyFreeVars]⟩
  | ctor hlook hlc hinst => cases hc; exact ⟨.ctor hlook hlc hinst, by simp [Expr.tyFreeVars]⟩

  | match_ _ hne _ ihs ihbranches =>
    simp only [Input.toCore, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at hc
    obtain ⟨scrut', hs, branches', hbs, rfl⟩ := hc
    obtain ⟨hts, hscopes⟩ := ihs hs
    refine ⟨.match_ hts ?_ ?_, ?_⟩
    · intro hempty
      have hlen := completeBranches_length hbs
      rw [hempty, List.length_nil] at hlen
      exact hne (List.length_eq_zero_iff.mp hlen)
    · intro branch hb
      obtain ⟨body, hbody, heq⟩ := completeBranches_backward hbs hb
      exact (ihbranches (branch.1, body) hbody heq).1
    · intro v hv
      rcases List.mem_append.mp hv with hv | hv
      · exact hscopes v hv
      · obtain ⟨branch, hb, hv⟩ := branchFreeVars_iff.mp hv
        obtain ⟨body, hbody, heq⟩ := completeBranches_backward hbs hb
        exact (ihbranches (branch.1, body) hbody heq).2 v hv
  | letRec hgroups hwf hp hG hAnn hRhs hFits hMono hPoly hBody ihMono ihPoly ihBody =>
    expose_names
    have hRaw := (Typing.letRec hgroups hwf hp hG hAnn hRhs hFits hMono hPoly hBody).rigidVars
    have hWhole := hc
    simp only [Input.toCore, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at hc
    obtain ⟨coreAnns, ha, coreBindings, hr, coreBody, hb, rfl⟩ := hc
    obtain ⟨hAnnsEq, hAnnData⟩ := completeAnns_data ha
    subst coreAnns
    have hannsLen : anns.length = specs.length := by
      have hh := congrArg List.length hwf.anns_eq
      simpa using hh.symm
    have hpNil := complete_prefixes_empty hp hannsLen (fun ann hm => (hAnnData ann hm).2)
    have hlen := completeBindings_length hr
    have hErased : coreBindings.map Expr.erase = bindings.map Input.erase := by
      rw [completeBindings_erase bindings hr, eraseBindings_eq_map_rec]
    have hbodyCtx : recBodyCtx ctx_1 specs prefixes G = RecSpecs.bodyCtx ctx_1 specs G := by
      unfold recBodyCtx RecSpecs.bodyCtx
      rw [recCompleted_empty_prefixes specs prefixes G hpNil]
    refine ⟨TypeOfHM.letRec (groups := groups) (G := G) (L := G ++ L)
      (validResidualGroups_erase_iff.mp (hErased ▸ hgroups))
      ⟨hwf.anns_eq, hlen.symm.trans (by simpa using hwf.length), hwf.nodup, hwf.mono_lc, hwf.poly_wf⟩
      ?_ ?_ rfl ?_, ?_⟩
    · intro stage component hs Xs hf member hm rhs ty hcore ht
      obtain ⟨rhs0, hr0, hemb⟩ := completeBindings_lookup_back hr hcore
      have hi : member < specs.length := (List.getElem?_eq_some_iff.mp ht).1
      have hia : member < anns.length := by omega
      have hip : member < prefixes.length := by rw [hp.length]; exact hi
      have hn : prefixes[member]? = some [] := by
        have hh := hpNil member
        rw [List.getElem?_eq_getElem hip] at hh
        rw [List.getElem?_eq_getElem hip]
        simpa only [Option.getD_some] using congrArg some hh
      have ho := rhs0.toCore_openTyVars hemb []
      rw [core_openTyVars_nil] at ho
      have hh := (ihMono stage component hs Xs hf member hm rhs0 anns[member] [] ty
        hr0 (List.getElem?_eq_getElem hia) hn ht ho).1
      simpa only [recRenameNames, List.map_nil, recStage_empty_prefixes _ _ _ _ _ _ hpNil] using hh
    · intro pair hpair scheme heq Ys hy
      obtain ⟨member, hzip⟩ := List.mem_iff_getElem?.mp hpair
      obtain ⟨hcore, ht⟩ := List.getElem?_zip_eq_some.mp hzip
      rw [heq] at ht
      obtain ⟨rhs0, hr0, hemb⟩ := completeBindings_lookup_back hr hcore
      have hy0 : FreshNames L scheme.paramCount Ys :=
        ⟨hy.length, hy.nodup, fun y hy' hl => hy.avoid y hy' (List.mem_append_right _ hl)⟩
      have hh := (ihPoly member rhs0 scheme hr0 ht Ys hy0 (rhs0.toCore_openTyVars hemb Ys)).1
      simpa only [hbodyCtx] using hh
    · simpa only [hbodyCtx] using (ihBody hb).1
    · intro v hv
      exact hRaw v ((Input.toCore_rigidVars _ hWhole v).mpr hv)
  | named hspec _ ih =>
    rename_i body heq
    obtain ⟨ht, hs⟩ := ih heq
    exact ⟨.mk hspec rfl ht, hs⟩
  | wildcard _ ih =>
    rename_i body heq
    obtain ⟨ht, hs⟩ := ih heq
    exact ⟨.wildcard ht, hs⟩

/-- Lambda inversion covers both partial syntax and the complete-subtree rule. -/
theorem Typing.lambda_inv (h : Typing K ctx (.lambda ann body) ty) :
    ∃ param result, ty = .arrow param result ∧ param.IsLC ∧
      (∀ template, ann = some template → template.Fits param) ∧
      (∀ template, ann = some template → ∀ v ∈ template.rigidVars, v ∈ K) ∧
      Typing K { ctx with env := PolyTy.mkTrivial param :: ctx.env } body result := by
  cases h with
  | lambda hlc hfits hr hb => exact ⟨_, _, rfl, hlc, hfits, hr, hb⟩
  | complete hemb hscope ht =>
    simp only [Input.toCore, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at hemb
    obtain ⟨ann', ha, body', hb, rfl⟩ := hemb
    cases ht with
    | lambda hlc hp hctx ht =>
      subst hctx
      refine ⟨_, _, rfl, hlc, ?_, ?_, .complete hb ?_ ht⟩
      · intro t heq
        subst ann
        simp only [completeLambdaAnn, bind, pure, Option.bind_eq_some_iff,
          Option.some.injEq] at ha
        obtain ⟨a, hta, rfl⟩ := ha
        rw [hp a rfl]
        exact Template.toCore_fits hta
      · intro t heq v hv
        subst ann
        simp only [completeLambdaAnn, bind, pure, Option.bind_eq_some_iff,
          Option.some.injEq] at ha
        obtain ⟨a, hta, rfl⟩ := ha
        exact hscope v (List.mem_append_left _ ((Template.toCore_rigidVars hta v).mp hv))
      · intro v hv; exact hscope v (List.mem_append_right _ hv)

theorem Typing.app_inv (h : Typing K ctx (.app f arg) ty) :
    ∃ param, Typing K ctx f (.arrow param ty) ∧ Typing K ctx arg param := by
  cases h with
  | app hf hx => exact ⟨_, hf, hx⟩
  | complete hemb hscope ht =>
    simp only [Input.toCore, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at hemb
    obtain ⟨f', hf, arg', hx, rfl⟩ := hemb
    cases ht with
    | app htf htx =>
      exact ⟨_, .complete hf (fun v hv => hscope v (List.mem_append_left _ hv)) htf,
        .complete hx (fun v hv => hscope v (List.mem_append_right _ hv)) htx⟩

theorem Typing.letMono_inv (h : Typing K ctx (.letIn ann rhs body) ty)
    (hmode : ann.isSignature = false) :
    ∃ (M : PolyTy) (L : List Nat), M.WF ∧
      (∀ template, ann = .template template → ∀ v ∈ template.rigidVars, v ∈ K) ∧
      (∀ Xs, FreshNames L M.paramCount Xs → ann.FitsMono (M.openVars Xs)) ∧
      (∀ Xs, FreshNames L M.paramCount Xs → Typing K ctx rhs (M.openVars Xs)) ∧
      Typing K { ctx with env := M :: ctx.env } body ty := by
  cases h with
  | letIn hwf hr hf htr htb => exact ⟨_, _, hwf, hr, hf, htr, htb⟩
  | @letSignature _ _ _ _ _ _ M L _ _ _ hfit _ _ =>
    obtain ⟨Xs, hlen, hnd, hav⟩ := exists_fresh_names L M.paramCount
    have hs := hfit Xs ⟨hlen, hnd, hav⟩
    have := hs.isSignature
    rw [hmode] at this
    cases this
  | complete hemb hscope ht =>
    simp only [Input.toCore, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at hemb
    obtain ⟨ann', ha, rhs', hr, body', hb, rfl⟩ := hemb
    cases ann with
    | complete => cases hmode
    | partialForall => cases hmode
    | template => cases ha
    | absent =>
      cases ha
      cases ht with
      | @letIn _ _ _ _ _ _ M L hwf _ hcofin heq hbody =>
        subst heq
        refine ⟨M, L, hwf, ?_, ?_, ?_, .complete hb ?_ hbody⟩
        · intro template heq; cases heq
        · intro Xs hXs; trivial
        · intro Xs hXs
          exact .complete hr (fun v hv => hscope v (List.mem_append_left _ hv)) (hcofin Xs hXs)
        · intro v hv; exact hscope v (List.mem_append_right _ hv)

/-- Match inversion preserves each constructor's existential arguments and
field context, including when the input used the complete-subtree rule. -/
theorem Typing.match_inv (h : Typing K ctx (.match_ scrut branches) resultTy) :
    ∃ scrutTy, Typing K ctx scrut scrutTy ∧ branches ≠ [] ∧
      ∀ branch ∈ branches, BranchTyping Typing K ctx branch scrutTy resultTy := by
  cases h with
  | match_ hs hne hb => exact ⟨_, hs, hne, hb⟩
  | complete hemb hscope ht =>
    simp only [Input.toCore, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at hemb
    obtain ⟨scrut', hs, branches', hbs, rfl⟩ := hemb
    cases ht with
    | match_ hscrut hne hbranches =>
      refine ⟨_, .complete hs (fun v hv => hscope v (List.mem_append_left _ hv)) hscrut, ?_, ?_⟩
      · intro hempty
        subst branches
        cases hbs
        exact hne rfl
      · intro branch hb
        obtain ⟨core, hc, heq⟩ := completeBranches_forward hbs hb
        have hcoreScope : ∀ v ∈ core.tyFreeVars, v ∈ K := fun v hv =>
          hscope v (List.mem_append_right _ (branchFreeVars_iff.mpr ⟨_, hc, hv⟩))
        have hbranch := hbranches (branch.1, core) hc
        rcases branch with ⟨pat, body⟩
        cases hbranch with
        | mk hspec hctx hbody =>
          subst hctx
          exact .named hspec (.complete heq hcoreScope hbody)
        | wildcard hbody => exact .wildcard (.complete heq hcoreScope hbody)

/-- A whole lambda-parameter hole has exactly omission's independent meaning. -/
theorem Typing.lambda_hole_iff :
    Typing K ctx (.lambda (some .hole) body) ty ↔ Typing K ctx (.lambda none body) ty := by
  constructor
  · intro h
    obtain ⟨param, result, rfl, hlc, _, _, hb⟩ := h.lambda_inv
    exact .lambda hlc (fun _ heq => by cases heq) (fun _ heq => by cases heq) hb
  · intro h
    obtain ⟨param, result, rfl, hlc, _, _, hb⟩ := h.lambda_inv
    refine .lambda hlc ?_ ?_ hb
    · intro template heq; cases heq; exact .hole
    · intro template heq; cases heq; simp only [Template.rigidVars, List.not_mem_nil, false_implies, implies_true]

/-- A whole ordinary-let signature hole has exactly omission's independent
meaning, including cofinite generalization of its RHS. -/
theorem Typing.let_hole_iff :
    Typing K ctx (.letIn (.template .hole) rhs body) ty ↔
      Typing K ctx (.letIn .absent rhs body) ty := by
  constructor
  · intro h
    obtain ⟨M, L, hwf, _, _, hr, hb⟩ := h.letMono_inv rfl
    exact .letIn hwf (fun _ heq => by cases heq) (fun _ _ => True.intro) hr hb
  · intro h
    obtain ⟨M, L, hwf, _, _, hr, hb⟩ := h.letMono_inv rfl
    refine .letIn hwf ?_ (fun _ _ => .hole) hr hb
    intro template heq; cases heq
    simp only [Template.rigidVars, List.not_mem_nil, false_implies, implies_true]


/-- Signed-let inversion retains the full candidate scheme, including any
additional declarative quantifiers after the authored prefix. -/
theorem Typing.signature_inv (h : Typing K ctx (.letIn ann rhs body) ty)
    (hmode : ann.isSignature = true) :
    ∃ (M : PolyTy) (L : List Nat), M.WF ∧
      (∀ v ∈ ann.rigidVars, v ∈ K) ∧ (∀ v ∈ rhs.rigidVars, v ∈ K) ∧
      (∀ Xs, FreshNames L M.paramCount Xs → ann.SignatureFits M Xs) ∧
      (∀ Xs, FreshNames L M.paramCount Xs →
        Typing (K ++ Xs.take ann.paramCount) ctx (rhs.openTyVars (Xs.take ann.paramCount)) (M.openVars Xs)) ∧
      Typing K { ctx with env := M :: ctx.env } body ty := by
  cases h with
  | letSignature hwf hann hrhs hfit htr htb => exact ⟨_, _, hwf, hann, hrhs, hfit, htr, htb⟩
  | @letIn _ _ _ _ _ _ M L _ _ hfit _ _ =>
      obtain ⟨Xs, hlen, hnd, hav⟩ := exists_fresh_names L M.paramCount
      have hmono := hfit Xs ⟨hlen, hnd, hav⟩
      cases ann with
      | absent => cases hmode
      | template => cases hmode
      | complete => cases hmono
      | partialForall => cases hmono
  | complete hemb hscope ht =>
      simp only [Input.toCore, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at hemb
      obtain ⟨ann', ha, rhs', hr, body', hb, rfl⟩ := hemb
      cases ann with
      | absent => cases hmode
      | template => cases hmode
      | partialForall => cases ha
      | complete scheme =>
          cases ha
          cases ht with
          | @letIn _ _ _ _ _ _ M L hwf hpin hgen hctx hbody =>
              subst hctx
              have hM : M = scheme := hpin scheme rfl
              subst M
              have hrhsScope : ∀ v ∈ rhs'.tyFreeVars, v ∈ K := fun v hv =>
                hscope v (List.mem_append_left _ (List.mem_append_right _ hv))
              refine ⟨scheme, L, hwf, ?_, ?_, ?_, ?_, .complete hb ?_ hbody⟩
              · intro v hv
                exact hscope v (List.mem_append_left _ (List.mem_append_left _ hv))
              · intro v hv
                exact hrhsScope v ((Input.toCore_rigidVars rhs hr v).mp hv)
              · intro Xs hXs; exact .complete
              · intro Xs hXs
                have htake : Xs.take scheme.paramCount = Xs := List.take_of_length_le hXs.length.le
                refine .complete (rhs.toCore_openTyVars hr (Xs.take scheme.paramCount)) ?_ ?_
                · intro v hv
                  rcases Expr.tyFreeVars_openTyVars hv with hv | hv
                  · exact List.mem_append_left _ (hrhsScope v hv)
                  · exact List.mem_append_right _ hv
                · simpa only [htake, Expr.openBoundTyVars] using hgen Xs hXs
              · intro v hv; exact hscope v (List.mem_append_right _ hv)


/-- Recursive inversion exposes the exact independent staged premises, even
when the derivation used the conservative complete-Core embedding. -/
theorem Typing.rec_inv (h : Typing K ctx (.letRec anns bindings body) resultTy) :
    ∃ (specs : List RecSpec) (groups prefixes : List (List Nat)) (G L : List Nat),
    RecGroups.ValidResidualGroups (anns.map LetAnn.recModeAnn) (bindings.map Input.erase) groups ∧
    RecSpecs.WF (anns.map LetAnn.recModeAnn) (bindings.map Input.erase) specs G ∧
    RecPrefixesWF anns specs prefixes G ∧
    (∀ name ∈ G, name ∉ ctx.env.freeVars ++ K) ∧
    (∀ ann ∈ anns, ∀ v ∈ ann.rigidVars, v ∈ K) ∧
    (∀ rhs ∈ bindings, ∀ v ∈ rhs.rigidVars, v ∈ K) ∧
    (∀ (stage : Nat) (component : List Nat), groups[stage]? = some component →
      ∀ Xs, FreshNames (G ++ L) G.length Xs →
      ∀ (member : Nat), member ∈ component → ∀ (rhs : Input) (ann : LetAnn) (names : List Nat) (ty : Ty),
        bindings[member]? = some rhs → anns[member]? = some ann →
        prefixes[member]? = some names → specs[member]? = some (.mono ty) →
        ann.RecFits (recRenameNames G Xs names) (Ty.renameG G Xs ty)) ∧
    (∀ (stage : Nat) (component : List Nat), groups[stage]? = some component →
      ∀ Xs, FreshNames (G ++ L) G.length Xs →
      ∀ (member : Nat), member ∈ component → ∀ (rhs : Input) (ann : LetAnn) (names : List Nat) (ty : Ty),
        bindings[member]? = some rhs → anns[member]? = some ann →
        prefixes[member]? = some names → specs[member]? = some (.mono ty) →
        Typing (K ++ Xs) (recStageCtx ctx specs prefixes (groups.take stage).flatten G Xs)
          (rhs.openTyVars (recRenameNames G Xs names)) (Ty.renameG G Xs ty)) ∧
    (∀ (member : Nat) (rhs : Input) (scheme : PolyTy), bindings[member]? = some rhs →
      specs[member]? = some (.poly scheme) → ∀ Ys, FreshNames L scheme.paramCount Ys →
        Typing (K ++ Ys) (recBodyCtx ctx specs prefixes G) (rhs.openTyVars Ys) (scheme.openVars Ys)) ∧
    Typing K (recBodyCtx ctx specs prefixes G) body resultTy := by
  cases h with
  | letRec hg hw hp hG hAnn hRhs hf hm hpoly hb =>
    exact ⟨_, _, _, _, _, hg, hw, hp, hG, hAnn, hRhs, hf, hm, hpoly, hb⟩
  | complete hemb hscope ht =>
    have rawScope : ∀ v ∈ (Input.letRec anns bindings body).rigidVars, v ∈ K :=
      fun v hv => hscope v ((Input.toCore_rigidVars _ hemb v).mp hv)
    have hAnn : ∀ ann ∈ anns, ∀ v ∈ ann.rigidVars, v ∈ K := by
      intro ann ha v hv
      exact rawScope v (List.mem_append_left _ (List.mem_append_left _ (List.mem_flatMap.mpr ⟨ann, ha, hv⟩)))
    have hRhs : ∀ rhs ∈ bindings, ∀ v ∈ rhs.rigidVars, v ∈ K := by
      have hB : ∀ bs : List Input, rigidBindingVars bs = bs.flatMap Input.rigidVars := by
        intro bs
        induction bs with
        | nil => rfl
        | cons rhs rest ih => simp only [rigidBindingVars, List.flatMap_cons, ih]
      intro rhs hr v hv
      apply rawScope v
      apply List.mem_append_left
      apply List.mem_append_right
      rw [hB bindings]
      exact List.mem_flatMap.mpr ⟨rhs, hr, hv⟩
    simp only [Input.toCore, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at hemb
    obtain ⟨coreAnns, ha, coreBindings, hr, coreBody, hb, rfl⟩ := hemb
    obtain ⟨hAnnsEq, hAnnData⟩ := completeAnns_data ha
    subst coreAnns
    cases ht with
    | letRec hg hw hMonoCore hPolyCore hctx hbody =>
      expose_names
      subst hctx
      have hlen := completeBindings_length hr
      have hannsLen : anns.length = specs.length := by
        have hh := congrArg List.length hw.anns_eq
        simpa using hh.symm
      have hErased : coreBindings.map Expr.erase = bindings.map Input.erase := by
        rw [completeBindings_erase bindings hr, eraseBindings_eq_map_rec]
      have hw0 : RecSpecs.WF (anns.map LetAnn.recModeAnn) (bindings.map Input.erase) specs G :=
        ⟨hw.anns_eq, by simpa only [List.length_map, hlen] using hw.length, hw.nodup, hw.mono_lc, hw.poly_wf⟩
      let prefixes0 : List (List Nat) := List.replicate specs.length []
      have hp0Nil : ∀ i : Nat, prefixes0[i]?.getD [] = [] := by
        intro i
        simp only [prefixes0, List.getElem?_replicate]
        split <;> rfl
      have hp0 : RecPrefixesWF anns specs prefixes0 G := by
        refine ⟨List.length_replicate, ?_⟩
        intro i ann names hai hni
        have hh := hp0Nil i
        rw [hni] at hh
        simp only [Option.getD_some] at hh
        subst names
        exact ⟨(hAnnData ann (List.mem_of_getElem? hai)).2.symm, .nil, by simp⟩
      let avoid := K ++ ctx.env.freeVars ++ G ++ specs.flatMap RecSpec.freeVars
      obtain ⟨W, hWlen, hWnd, hWavoid⟩ := exists_fresh_names avoid G.length
      have hGW : ∀ g ∈ G, g ∉ W := by
        intro g hg hw
        exact hWavoid g hw (by simp only [avoid, List.mem_append]; tauto)
      have hWmono : ∀ ty, .mono ty ∈ specs → ∀ w ∈ W, w ∉ ty.freeVars := by
        intro ty ht w hw hv
        exact hWavoid w hw (by
          simp only [avoid, List.mem_append]
          right
          exact List.mem_flatMap.mpr ⟨.mono ty, ht, hv⟩)
      let specs' := specs.map (fun spec => RecSpec.onSubstSource [] (RecSpec.onSubst (G.zip (W.map Ty.fvar)) spec))
      let prefixes' := prefixes0.map (recRenameNames G W)
      let L' := G ++ W ++ L
      have annNil : anns.map (LetAnn.substTyFvars []) = anns := by
        conv_rhs => rw [← List.map_id anns]
        apply List.map_congr_left
        intro ann _
        exact ann.substTyFvars_eq_self_of_fixes (fun _ _ => rfl)
      have hw' : RecSpecs.WF (anns.map LetAnn.recModeAnn) (bindings.map Input.erase) specs' W := by
        simpa only [annNil] using Elaboration.RecSpecs.WF.subst_fresh_pool (S := []) hw0 (by simp) hWnd
      have hp' : RecPrefixesWF anns specs' prefixes' W := by
        simpa only [annNil] using hp0.subst_fresh_pool (S := []) hWlen hWnd
      have hp'Nil : ∀ i : Nat, prefixes'[i]?.getD [] = [] := by
        intro i
        simp only [prefixes', List.getElem?_map]
        cases hpi : prefixes0[i]? with
        | none => rfl
        | some names =>
          have hn := hp0Nil i
          rw [hpi] at hn
          simp only [Option.getD_some] at hn
          rw [hn]
          rfl
      have hpData := fun i hi => hp0.get hannsLen (i := i) hi
      have hcompleted := recCompletedSchemes_subst_fresh_pool (S := []) (by simp) hWlen hw.nodup hWnd hGW hWmono
        (by simp) (by simp) hw.mono_lc hpData
      have mapNil : ∀ xs : List PolyTy, xs.map (Subst.onPolyTy []) = xs := by
        intro xs
        rw [show Subst.onPolyTy [] = id from funext Subst.onPolyTy_nil, List.map_id]
      have hbodyCtx : recBodyCtx ctx specs' prefixes' W = RecSpecs.bodyCtx ctx specs G := by
        unfold recBodyCtx RecSpecs.bodyCtx
        rw [hcompleted, mapNil, recCompleted_empty_prefixes specs prefixes0 G hp0Nil]
      have oldFresh : ∀ Xs, FreshNames (W ++ L') W.length Xs → FreshNames L G.length Xs := by
        intro Xs hf
        refine ⟨hf.length.trans hWlen, hf.nodup, ?_⟩
        intro x hx hl
        exact hf.avoid x hx (by simp only [L', List.mem_append]; tauto)
      have hGXs : ∀ Xs, FreshNames (W ++ L') W.length Xs → ∀ g ∈ G, g ∉ Xs := by
        intro Xs hf g hg hx
        exact hf.avoid g hx (by simp only [L', List.mem_append]; tauto)
      have hWXs : ∀ Xs, FreshNames (W ++ L') W.length Xs → ∀ w ∈ W, w ∉ Xs := by
        intro Xs hf w hw hx
        exact hf.avoid w hx (List.mem_append_left _ hw)
      have hstageCtx : ∀ Xs, FreshNames (W ++ L') W.length Xs → ∀ done,
          recStageCtx ctx specs' prefixes' done W Xs = RecSpecs.stageCtx ctx specs done G Xs := by
        intro Xs hf done
        unfold recStageCtx
        rw [recStageSchemes_subst_fresh_pool (S := []) (by simp) hWlen hw.nodup hWnd hGW hWmono
          (by simp) (by simp) hw.mono_lc hpData (hf.length.trans hWlen) (hGXs Xs hf) (hWXs Xs hf) (by simp), mapNil]
        exact recStage_empty_prefixes ctx specs prefixes0 done G Xs hp0Nil
      have annMonoAbsent : ∀ (member : Nat) (ann : LetAnn) (ty : Ty), anns[member]? = some ann → specs[member]? = some (.mono ty) → ann = .absent := by
        intro member ann ty hai hti
        have heq := congrArg (fun xs => xs[member]?) hw.anns_eq
        simp only [List.getElem?_map, hti, hai, Option.map_some, RecSpec.ann, Option.some.injEq] at heq
        have hvalid := (hAnnData ann (List.mem_of_getElem? hai)).1
        cases ann with
        | absent => rfl
        | complete scheme => cases heq
        | template template => cases hvalid
        | partialForall n template => cases hvalid
      refine ⟨specs', groups, prefixes', W, L', hErased ▸ validResidualGroups_erase_iff.mpr hg,
        hw', hp', ?_, hAnn, hRhs, ?_, ?_, ?_, ?_⟩
      · intro w hw hm
        exact hWavoid w hw (by simp only [avoid, List.mem_append] at hm ⊢; tauto)
      · intro stage component hs Xs hf member hm rhs ann names ty hri hai hni hti
        have hn := hp'Nil member
        rw [hni] at hn
        simp only [Option.getD_some] at hn
        subst names
        rw [List.getElem?_map] at hti
        obtain ⟨spec, ht0, heq⟩ := Option.map_eq_some_iff.mp hti
        cases spec with
        | poly scheme => cases heq
        | mono ty0 =>
          rw [annMonoAbsent member ann ty0 hai ht0]
          trivial
      · intro stage component hs Xs hf member hm rhs ann names ty hri hai hni hti
        have hn := hp'Nil member
        rw [hni] at hn
        simp only [Option.getD_some] at hn
        subst names
        rw [List.getElem?_map] at hti
        obtain ⟨spec, ht0, heq⟩ := Option.map_eq_some_iff.mp hti
        cases spec with
        | poly scheme => cases heq
        | mono ty0 =>
          cases heq
          obtain ⟨coreRhs, hc, hemb⟩ := completeBindings_lookup hr hri
          have hcTyping := hMonoCore stage component hs Xs (oldFresh Xs hf) member hm coreRhs ty0 hc ht0
          have ho := rhs.toCore_openTyVars hemb []
          rw [core_openTyVars_nil] at ho
          change Typing (K ++ Xs) (recStageCtx ctx specs' prefixes' (groups.take stage).flatten W Xs)
            (rhs.openTyVars []) (Ty.renameG W Xs (Ty.renameG G W ty0))
          have hsquare := Ty.renameG_subst_fresh_pool (S := []) (hw.mono_lc ty0 (List.mem_of_getElem? ht0)) (by simp)
            hWlen hw.nodup hWnd hGW (hWmono ty0 (List.mem_of_getElem? ht0)) (by simp) (by simp)
            (hf.length.trans hWlen) (hGXs Xs hf) (hWXs Xs hf) (by simp)
          simp only [Subst.onTy_nil] at hsquare
          rw [hstageCtx Xs hf, hsquare]
          refine .complete ho ?_ hcTyping
          intro v hv
          exact List.mem_append_left _ (hRhs rhs (List.mem_of_getElem? hri) v ((Input.toCore_rigidVars _ hemb v).mpr hv))
      · intro member rhs scheme hri hsi Ys hy
        rw [List.getElem?_map] at hsi
        obtain ⟨spec, hs0, heq⟩ := Option.map_eq_some_iff.mp hsi
        cases spec with
        | mono ty => cases heq
        | poly scheme0 =>
          cases heq
          obtain ⟨coreRhs, hc, hemb⟩ := completeBindings_lookup hr hri
          have hy0 : FreshNames L scheme0.paramCount Ys :=
            ⟨hy.length, hy.nodup, fun y hy' hl => hy.avoid y hy' (by simp only [L', List.mem_append]; tauto)⟩
          have hcTyping := hPolyCore (coreRhs, .poly scheme0)
            (List.mem_iff_getElem?.mpr ⟨member, List.getElem?_zip_eq_some.mpr ⟨hc, hs0⟩⟩) scheme0 rfl Ys hy0
          rw [hbodyCtx]
          refine .complete (rhs.toCore_openTyVars hemb Ys) ?_ hcTyping
          intro v hv
          rcases Expr.tyFreeVars_openTyVars hv with hv | hv
          · exact List.mem_append_left _ (hRhs rhs (List.mem_of_getElem? hri) v ((Input.toCore_rigidVars _ hemb v).mpr hv))
          · exact List.mem_append_right _ hv
      · rw [hbodyCtx]
        refine .complete hb ?_ hbody
        intro v hv
        exact rawScope v (List.mem_append_right _ ((Input.toCore_rigidVars _ hb v).mpr hv))


/-- Move candidate occurrences of an algorithmic skolem block out to fresh
scratch space. The conjugated ambient fixes the algorithmic skolems, agrees
with forward-renaming the old ambient below the block, and maps back exactly.
Only scratch freshness is required; candidate types may contain the whole
algorithmic block. `avoid` can include an algorithm's final allocated range. -/
theorem signed_candidate_dodge (S : Subst) (hS : ∀ p ∈ S, p.2.IsLC)
    (N count : Nat) (targets : List Ty) (avoid : List Nat) :
    ∃ W, N + count ≤ W ∧ (∀ v ∈ avoid, v < W) ∧
      (∀ p ∈ Subst.conj (blockSwap N W count) S, p.2.IsLC) ∧
      (∀ y ∈ freshVars N count,
        (Subst.conj (blockSwap N W count) S).onTy (.fvar y) = .fvar y) ∧
      (∀ v, v < N →
        (blockList N W count).onTy (.fvar v) = .fvar v ∧
        (blockListBack N W count).onTy (.fvar v) = .fvar v) ∧
      (∀ τ, Ty.BelowFvars N τ →
        (Subst.conj (blockSwap N W count) S).onTy τ =
          (blockList N W count).onTy (S.onTy τ)) ∧
      (∀ τ, Ty.BelowFvars N τ →
        (blockListBack N W count).onTy
          ((Subst.conj (blockSwap N W count) S).onTy τ) = S.onTy τ) ∧
      (∀ τ ∈ targets,
        (blockListBack N W count).onTy ((blockList N W count).onTy τ) = τ ∧
        ∀ y ∈ freshVars N count, y ∉ ((blockList N W count).onTy τ).freeVars) := by
  obtain ⟨W, hd, hfresh⟩ := exists_fresh_block
    (S.map Prod.fst ++ S.flatMap (fun p => p.2.freeVars) ++ targets.flatMap Ty.freeVars ++ avoid) N count
  have hkeys : ∀ p ∈ S, p.1 < W := fun p hp =>
    hfresh p.1 (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
      (List.mem_map.mpr ⟨p, hp, rfl⟩))))
  have hranges : ∀ p ∈ S, Ty.BelowFvars W p.2 := by
    intro p hp
    apply Ty.BelowFvars.of_freeVars_lt
    intro v hv
    exact hfresh v (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _
      (List.mem_flatMap.mpr ⟨p, hp, hv⟩))))
  have hSscratch : ∀ τ, Ty.BelowFvars N τ →
      ∀ v ∈ (S.onTy τ).freeVars, ¬ (W ≤ v ∧ v < W + count) := by
    intro τ hτ v hv
    have hlt := (Subst.onTy_belowFvars hranges (hτ.mono (by omega))).mem_lt v hv
    omega
  have hforward : ∀ τ, Ty.BelowFvars N τ →
      (Subst.conj (blockSwap N W count) S).onTy τ = (blockList N W count).onTy (S.onTy τ) := by
    intro τ hτ
    have hrename : Ty.rename (blockSwap N W count) τ = τ :=
      Ty.rename_eq_self (fun v hv => blockSwap_lt (by omega) (hτ.mem_lt v hv))
    have hconj := Subst.onTy_conj (blockSwap_injective hd) S τ
    rw [hrename] at hconj
    exact hconj.trans (blockList_onTy hd (hSscratch τ hτ)).symm
  refine ⟨W, hd, fun v hv => hfresh v (List.mem_append_right _ hv), Subst.conj_lc hS, ?_, ?_, hforward, ?_, ?_⟩
  · intro y hy
    apply Ty.substFvars_eq_self_of_no_key
    intro p hp hc
    simp only [Subst.conj, List.mem_map] at hp
    obtain ⟨q, hq, rfl⟩ := hp
    have hqlt := hkeys q hq
    have hyge := freshVars_ge y hy
    have hylt := freshVars_lt y hy
    simp only [Ty.freeVars, List.mem_singleton, blockSwap] at hc
    split_ifs at hc <;> omega
  · intro v hv
    constructor
    · apply Ty.substFvars_eq_self_of_no_key
      intro p hp hc
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hp
      simp only [Ty.freeVars, List.mem_singleton] at hc
      omega
    · apply Ty.substFvars_eq_self_of_no_key
      intro p hp hc
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hp
      simp only [Ty.freeVars, List.mem_singleton] at hc
      omega
  · intro τ hτ
    rw [hforward τ hτ, blockList_onTy hd (hSscratch τ hτ)]
    exact blockListBack_onTy_rename hd (hSscratch τ hτ)
  · intro τ hτ
    have hτscratch : ∀ v ∈ τ.freeVars, ¬ (W ≤ v ∧ v < W + count) := by
      intro v hv
      have hlt := hfresh v (List.mem_append_left _ (List.mem_append_right _
        (List.mem_flatMap.mpr ⟨τ, hτ, hv⟩)))
      omega
    rw [blockList_onTy hd hτscratch]
    exact ⟨blockListBack_onTy_rename hd hτscratch, fun y hy =>
      blockSwap_rename_not_mem hd hτscratch y (freshVars_ge y hy) (freshVars_lt y hy)⟩

/-- Internal source-transforming residual theorem. The local freeze premise
concerns authored frozen leaves only; unrelated K/context variables may vary. -/
def _root_.Infer.SourcePrincipal (_h : Infer K F frontier ctx input next subst output ty) : Prop :=
  CtxWF ctx → CtxBelow frontier ctx → (∀ k ∈ K, k < frontier) →
  (∀ soft ∈ F, Ty.BelowFvars frontier soft) →
  ∀ (ambient : Subst) (target : Ty) (P : List Nat),
    (∀ pair ∈ ambient, pair.2.IsLC) → (∀ p ∈ P, p < frontier) →
    (∀ p ∈ P, ambient.onTy (.fvar p) = .fvar p) →
    (∀ v ∈ input.rigidVars, v ∈ K → v ∉ softVars F → ambient.onTy (.fvar v) = .fvar v) →
    Typing P (ambient.onCtx ctx) (input.substTyFvars ambient) target →
    ∃ residual : Subst, (∀ pair ∈ residual, pair.2.IsLC) ∧
      target = residual.onTy ty ∧
      (∀ p ∈ P, residual.onTy (.fvar p) = .fvar p) ∧
      Subst.AgreesBelow frontier ambient (subst ++ residual)

/-- Residual principality retains an independently quantified protected set.
`Typing P` scopes authored fixed types in precisely that protected set. It does
not claim most-general fillings for every unused annotation hole. -/
def _root_.Infer.Principal (_h : Infer K F frontier ctx input next subst output ty) : Prop :=
  CtxWF ctx → CtxBelow frontier ctx → (∀ k ∈ K, k < frontier) →
  (∀ soft ∈ F, Ty.BelowFvars frontier soft) →
  ∀ (ambient : Subst) (target : Ty) (P : List Nat),
    (∀ pair ∈ ambient, pair.2.IsLC) → (∀ p ∈ P, p < frontier) →
    (∀ p ∈ P, ambient.onTy (.fvar p) = .fvar p) →
    Typing P (ambient.onCtx ctx) input target →
    ∃ residual : Subst, (∀ pair ∈ residual, pair.2.IsLC) ∧
      target = residual.onTy ty ∧
      (∀ p ∈ P, residual.onTy (.fvar p) = .fvar p) ∧
      Subst.AgreesBelow frontier ambient (subst ++ residual)

theorem _root_.Infer.SourcePrincipal.principal {h : Infer K F frontier ctx input next subst output ty}
    (ih : Infer.SourcePrincipal h) : Infer.Principal h := by
  intro hwf hctx hK hF ambient target P hS hP hfix ht
  have heq := input.substTyFvars_eq_self_of_fixes (fun v hv => hfix v (ht.rigidVars v hv))
  exact ih hwf hctx hK hF ambient target P hS hP hfix
    (fun v hv _ _ => hfix v (ht.rigidVars v hv)) (heq.symm ▸ ht)

theorem Seed.override (h : Seed K frontier ann param initial)
    (hK : ∀ k ∈ K, k < frontier) {target : Ty} (htarget : target.IsLC)
    {ambient : Subst} (hlc : ∀ pair ∈ ambient, pair.2.IsLC)
    (hfit : ∀ template, ann = some template → (template.substTyFvars ambient).Fits target) :
    ∃ U : Subst, (∀ pair ∈ U, pair.2.IsLC) ∧
      Subst.AgreesBelow frontier ambient U ∧ U.onTy param = target := by
  cases h with
  | absent =>
    obtain ⟨U, hU, hag, hb⟩ := Subst.override_block hlc frontier [target] (by simpa using htarget)
    exact ⟨U, hU, hag, by simpa using hb 0 (by simp)⟩
  | @annotated next ty template heq _ hr =>
    obtain ⟨U, hU, hag, ht⟩ := (hfit template rfl).allocate_override_source htarget hlc frontier
      (fun v hv => hK v (hr v hv))
    rw [heq] at ht
    exact ⟨U, hU, hag, ht⟩

/-- The local source freeze is stable under solving and factoring. A source
leaf that originated in F remains marked by the full substituted F image. -/
theorem SourceScope.residual_freeze {K : List Nat} {F : List Ty} {input : Input} {frontier : Nat}
    {ambient solved residual : Subst}
    (hscope : SourceScope K F input)
    (hbelow : ∀ v ∈ input.rigidVars, v < frontier)
    (hsolved : ∀ k ∈ K, solved.onTy (.fvar k) = .fvar k)
    (hfreeze : ∀ v ∈ input.rigidVars, v ∈ K → v ∉ softVars F → ambient.onTy (.fvar v) = .fvar v)
    (hagree : Subst.AgreesBelow frontier ambient (solved ++ residual)) :
    ∀ v ∈ (input.substTyFvars solved).rigidVars,
      v ∈ K → v ∉ softVars (substSoft solved F) → residual.onTy (.fvar v) = .fvar v := by
  intro v hv _ hnot
  obtain ⟨original, horiginal, himage⟩ := input.rigidVars_substTyFvars hv
  have horiginalNotF : original ∉ softVars F := by
    intro hin
    exact hnot (mem_softVars_substSoft.mpr ⟨original, hin, himage⟩)
  have horiginalK : original ∈ K := (List.mem_append.mp (hscope original horiginal)).resolve_right horiginalNotF
  have hfixed := hsolved original horiginalK
  rw [hfixed] at himage
  have heq : v = original := List.mem_singleton.mp himage
  subst v
  have hag := hagree original (hbelow original horiginal)
  rw [Subst.onTy_append, hfixed, hfreeze original horiginal horiginalK horiginalNotF] at hag
  exact hag.symm

 theorem _root_.InferRecComponent.sourcePrincipal_of_infer
    (h : InferRecComponent K F members index frontier ctx bindings specs next S outputs facts)
    (hInfer : ∀ {κ F' Ψ c e Ψ' T output ty}, e.size ≤ sizeBindings bindings →
      (hi : Infer κ F' Ψ c e Ψ' T output ty) → Infer.SourcePrincipal hi)
    (hctxWF : CtxWF ctx) (hctx : CtxBelow frontier ctx)
    (hK : ∀ k ∈ K,k < frontier) (hF : ∀ t ∈ F,Ty.BelowFvars frontier t)
    (hspecLC : ∀ spec ∈ specs,spec.LC) (hspecB : ∀ spec ∈ specs,spec.BelowFvars frontier)
    (hscope : ∀ rhs ∈ bindings,SourceScope K F rhs)
    (ambient : Subst) (P : List Nat) (hambient : ∀ p ∈ ambient,p.2.IsLC)
    (hP : ∀ p ∈ P,p < frontier) (hfixP : ∀ p ∈ P,ambient.onTy (.fvar p) = .fvar p)
    (hfreeze : ∀ (j : Nat) (rhs : Input),index + j ∈ members → bindings[j]? = some rhs →
      ∀ v ∈ rhs.rigidVars,v ∈ K → v ∉ softVars F → ambient.onTy (.fvar v) = .fvar v)
    (hcandidate : ∀ (j : Nat) (rhs : Input) (target : Ty),index + j ∈ members →
      bindings[j]? = some rhs → specs[j]? = some (.mono target) →
      Typing P (ambient.onCtx ctx) (rhs.substTyFvars ambient) (ambient.onTy target)) :
    ∃ R : Subst,(∀ p ∈ R,p.2.IsLC) ∧ (∀ p ∈ P,R.onTy (.fvar p) = .fvar p) ∧
      Subst.AgreesBelow frontier ambient (S ++ R) := by
  match h with
  | .nil => exact ⟨ambient,hambient,hfixP,fun _ _ => rfl⟩
  | .skipMono hn hr | .skipPoly hr =>
    exact hr.sourcePrincipal_of_infer
      (fun he hi => hInfer (by simp only [sizeBindings];omega) hi)
      hctxWF hctx hK hF
      (fun spec hm => hspecLC spec (List.mem_cons_of_mem _ hm))
      (fun spec hm => hspecB spec (List.mem_cons_of_mem _ hm))
      (fun rhs hm => hscope rhs (List.mem_cons_of_mem _ hm)) ambient P hambient hP hfixP
      (fun j rhs hm hb => hfreeze (j+1) rhs (by simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hm) hb)
      (fun j rhs target hm hb ht => hcandidate (j+1) rhs target (by simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hm) hb ht)
  | .consSelected hm hi hu hr =>
    expose_names
    have hle := hi.frontier_le
    have hheadB : Ty.BelowFvars frontier expected := hspecB _ List.mem_cons_self
    have hheadSource := hscope _ List.mem_cons_self
    have hrawBelow : ∀ rhs, SourceScope K F rhs → ∀ v ∈ rhs.rigidVars,v < frontier := by
      intro rhs hh v hv
      exact (List.mem_append.mp (hh v hv)).elim (hK v) (softVars_lt hF v)
    obtain ⟨R1,hR1,hty,hR1P,hag1⟩ := hInfer (by simp only [sizeBindings];omega) hi
      hctxWF hctx hK hF ambient (ambient.onTy expected) P hambient hP hfixP
      (hfreeze 0 _ (by simpa using hm) rfl)
      (hcandidate 0 _ _ (by simpa using hm) rfl rfl)
    have hExpected : ambient.onTy expected = R1.onTy (s1.onTy expected) := by
      simpa only [Subst.onTy_append] using Subst.onTy_congr hag1 hheadB
    obtain ⟨R2,hfac,hR2,hR2P⟩ := hu.unifies.greatest_K R1 hR1 (hty.symm.trans hExpected) hR1P
    have hag12 : Subst.AgreesBelow frontier ambient ((s1 ++ s2) ++ R2) := by
      intro v hv
      rw [hag1 v hv,Subst.onTy_append,hfac,Subst.onTy_append,Subst.onTy_append]
    obtain ⟨hiLC,hs1LC⟩ := hi.lc hctxWF
    have hs2LC := hu.unifies.lc hiLC (Subst.onTy_lc hs1LC (hspecLC _ List.mem_cons_self))
    have hbothLC : ∀ p ∈ s1 ++ s2,p.2.IsLC := fun p hp => (List.mem_append.mp hp).elim (hs1LC p) (hs2LC p)
    obtain ⟨hiB,hs1B⟩ := hi.belowFvars hctx hK hF
    have hs2B := hu.unifies.belowFvars hiB (Subst.onTy_belowFvars hs1B (hheadB.mono hle))
    have hbothB : ∀ p ∈ s1 ++ s2,Ty.BelowFvars first p.2 := fun p hp => (List.mem_append.mp hp).elim (hs1B p) (hs2B p)
    have hbothFix : ∀ k ∈ K,(s1 ++ s2).onTy (.fvar k) = .fvar k :=
      Subst.fixes_of_dom_avoids (fun p hp => (List.mem_append.mp hp).elim (hi.dom_avoids p) (hu.dom_avoids p))
    have hctxEq : R2.onCtx (s2.onCtx (s1.onCtx ctx)) = ambient.onCtx ctx := by
      simpa only [Subst.onCtx_append] using (Subst.onCtx_congr hag12 hctx).symm
    have htailWF := Subst.onCtx_wf hs2LC (Subst.onCtx_wf hs1LC hctxWF)
    have htailB : CtxBelow first (s2.onCtx (s1.onCtx ctx)) := by
      simpa only [Subst.onCtx_append] using Subst.onCtx_below hbothB hle hctx
    obtain ⟨R3,hR3,hR3P,hag3⟩ := hr.sourcePrincipal_of_infer
      (fun he hi => hInfer (by simp only [sizeBindings_map_substTyFvars] at he;simp only [sizeBindings];omega) hi)
      htailWF htailB (fun k hk => (hK k hk).trans_le hle) (substSoft_below hbothB hle hF)
      (by intro spec hs;obtain ⟨old,ho,rfl⟩ := List.mem_map.mp hs;exact RecSpec.lc_onSubstSource hbothLC (hspecLC old (List.mem_cons_of_mem _ ho)))
      (by
        intro spec hs
        obtain ⟨old,ho,rfl⟩ := List.mem_map.mp hs
        cases old with
        | mono t => exact Subst.onTy_belowFvars hbothB ((hspecB _ (List.mem_cons_of_mem _ ho)).mono hle)
        | poly M => exact Subst.onTy_belowFvars hbothB ((hspecB _ (List.mem_cons_of_mem _ ho)).mono hle))
      (by intro rhs hs;obtain ⟨old,ho,rfl⟩ := List.mem_map.mp hs;exact (hscope old (List.mem_cons_of_mem _ ho)).subst _ hbothFix)
      R2 P hR2 (fun p hp => (hP p hp).trans_le hle) hR2P
      (by
        intro j rhs hj hb v hv hk hn
        obtain ⟨old,ho,rfl⟩ := Option.map_eq_some_iff.mp (by simpa only [List.getElem?_map] using hb)
        exact (hscope old (List.mem_cons_of_mem _ (List.mem_of_getElem? ho))).residual_freeze
          (hrawBelow old (hscope old (List.mem_cons_of_mem _ (List.mem_of_getElem? ho)))) hbothFix
          (hfreeze (j+1) old (by simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hj) ho)
          hag12 v hv hk hn)
      (by
        intro j rhs target hj hb ht
        obtain ⟨old,ho,rfl⟩ := Option.map_eq_some_iff.mp (by simpa only [List.getElem?_map] using hb)
        obtain ⟨oldTarget,hot,rfl⟩ := RecSpec.mono_getElem?_map_onSubstSource ht
        have hsourceEq : (old.substTyFvars (s1 ++ s2)).substTyFvars R2 = old.substTyFvars ambient := by
          rw [←Input.substTyFvars_append]
          exact old.substTyFvars_congr (fun v hv => (hag12 v (hrawBelow old (hscope old (List.mem_cons_of_mem _ (List.mem_of_getElem? ho))) v hv)).symm)
        have htargetEq : R2.onTy ((s1 ++ s2).onTy oldTarget) = ambient.onTy oldTarget := by
          simpa only [Subst.onTy_append] using (Subst.onTy_congr hag12 (hspecB _ (List.mem_cons_of_mem _ (List.mem_of_getElem? hot)))).symm
        rw [hctxEq,hsourceEq,htargetEq]
        exact hcandidate (j+1) old oldTarget (by simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hj) ho hot)
    exact ⟨R3,hR3,hR3P,by simpa only [List.append_assoc] using hag12.trans_append hle hbothB hag3⟩
 termination_by structural h


/-- Candidate roots are class labels; a representative is the actual slot at
that label's first occurrence. Labels may themselves collide with actual IDs. -/
def prefixRepresentative (actual candidate : List Nat) (root : Nat) : Nat :=
  (actual[candidate.idxOf root]?).getD 0

def prefixRepresentativeImages (actual candidate : List Nat) : List Nat :=
  candidate.map (prefixRepresentative actual candidate)

def prefixRepresentatives (actual candidate : List Nat) : List Nat :=
  candidate.dedup.map (prefixRepresentative actual candidate)

 theorem prefixRepresentative_lookup {actual candidate : List Nat}
    (hlen : actual.length = candidate.length) (hroot : root ∈ candidate) :
    actual[candidate.idxOf root]? = some (prefixRepresentative actual candidate root) := by
  have hi : candidate.idxOf root < actual.length := by
    rw [hlen]
    exact List.idxOf_lt_length_iff.mpr hroot
  unfold prefixRepresentative
  rw [List.getElem?_eq_getElem hi]
  rfl

 theorem prefixRepresentative_mem {actual candidate : List Nat}
    (hlen : actual.length = candidate.length) (hroot : root ∈ candidate) :
    prefixRepresentative actual candidate root ∈ actual :=
  List.mem_of_getElem? (prefixRepresentative_lookup hlen hroot)

 theorem prefixRepresentative_injective {actual candidate : List Nat}
    (hlen : actual.length = candidate.length) (hnd : actual.Nodup)
    (hc : c ∈ candidate) (hd : d ∈ candidate)
    (heq : prefixRepresentative actual candidate c = prefixRepresentative actual candidate d) : c = d := by
  have hcidx := List.idxOf_lt_length_iff.mpr hc
  have hdidx := List.idxOf_lt_length_iff.mpr hd
  have hci : candidate.idxOf c < actual.length := by omega
  have hdi : candidate.idxOf d < actual.length := by omega
  have ha := (prefixRepresentative_lookup hlen hc).trans
    ((congrArg some heq).trans (prefixRepresentative_lookup hlen hd).symm)
  rw [List.getElem?_eq_getElem hci,List.getElem?_eq_getElem hdi] at ha
  have hij := hnd.getElem_inj_iff.mp (Option.some.inj ha)
  have hh := congrArg (fun i => candidate[i]?) hij
  dsimp only at hh
  rw [List.getElem?_eq_getElem hcidx,List.getElem_idxOf hcidx,
    List.getElem?_eq_getElem hdidx,List.getElem_idxOf hdidx] at hh
  exact Option.some.inj hh

 theorem prefixRepresentative_first {actual candidate : List Nat}
    (hlen : actual.length = candidate.length) (hi : i < candidate.length)
    (hfirst : candidate.idxOf candidate[i] = i) :
    prefixRepresentative actual candidate candidate[i] = actual[i]'(by omega) := by
  unfold prefixRepresentative
  rw [hfirst,List.getElem?_eq_getElem (show i < actual.length by omega)]
  rfl

 theorem prefixRepresentative_fix_image {actual candidate : List Nat} {S : Subst}
    (hlen : actual.length = candidate.length)
    (hassign : ∀ i (hi : i < candidate.length),
      S.onTy (.fvar (actual[i]'(by omega))) = .fvar (prefixRepresentative actual candidate candidate[i]))
    (hc : c ∈ candidate) :
    S.onTy (.fvar (prefixRepresentative actual candidate c)) = .fvar (prefixRepresentative actual candidate c) := by
  have hi := List.idxOf_lt_length_iff.mpr hc
  have hget : candidate[candidate.idxOf c] = c := List.getElem_idxOf hi
  have hactual : actual[candidate.idxOf c]'(by omega) = prefixRepresentative actual candidate c :=
    (Option.some.inj ((List.getElem?_eq_getElem (by omega)).symm.trans (prefixRepresentative_lookup hlen hc)))
  simpa only [hactual,hget] using hassign (candidate.idxOf c) hi


 theorem prefixRepresentative_below {actual candidate : List Nat}
    (hlen : actual.length = candidate.length) (hbound : ∀ a ∈ actual, a < frontier)
    (hc : c ∈ candidate) : prefixRepresentative actual candidate c < frontier :=
  hbound _ (prefixRepresentative_mem hlen hc)

 theorem prefixRepresentative_disjoint {actual candidate P : List Nat}
    (hlen : actual.length = candidate.length) (hstart : ∀ a ∈ actual, base ≤ a)
    (hP : ∀ p ∈ P, p < base) (hc : c ∈ candidate) :
    prefixRepresentative actual candidate c ∉ P := by
  intro hp
  have := hstart _ (prefixRepresentative_mem hlen hc)
  have := hP _ hp
  omega

 theorem prefixRepresentative_prefix_nodup {actual candidate names : List Nat}
    (hlen : actual.length = candidate.length) (hA : actual.Nodup)
    (hnd : names.Nodup) (hsub : ∀ c ∈ names, c ∈ candidate) :
    (names.map (prefixRepresentative actual candidate)).Nodup :=
  hnd.map_on (fun c hc d hd heq => prefixRepresentative_injective hlen hA (hsub c hc) (hsub d hd) heq)

 theorem prefixRepresentatives_nodup {actual candidate : List Nat}
    (hlen : actual.length = candidate.length) (hA : actual.Nodup) :
    (prefixRepresentatives actual candidate).Nodup :=
  prefixRepresentative_prefix_nodup hlen hA (List.nodup_dedup _) (fun _ h => List.mem_dedup.mp h)

 theorem prefixRepresentatives_mem_actual {actual candidate : List Nat}
    (hlen : actual.length = candidate.length) (hv : v ∈ prefixRepresentatives actual candidate) : v ∈ actual := by
  obtain ⟨root,hroot,rfl⟩ := List.mem_map.mp hv
  exact prefixRepresentative_mem hlen (List.mem_dedup.mp hroot)

 theorem prefixRepresentatives_capacity {actual candidate : List Nat}
    (hlen : actual.length = candidate.length) :
    (prefixRepresentatives actual candidate).length ≤ actual.length := by
  rw [prefixRepresentatives,List.length_map,hlen]
  exact (List.dedup_sublist candidate).length_le

 theorem prefixRepresentativeImages_length (actual candidate : List Nat) :
    (prefixRepresentativeImages actual candidate).length = candidate.length := List.length_map _

 theorem prefixRepresentativeImages_lookup {actual candidate : List Nat} {root i : Nat}
    (hc : candidate[i]? = some root) :
    (prefixRepresentativeImages actual candidate)[i]? = some (prefixRepresentative actual candidate root) := by
  simp only [prefixRepresentativeImages,List.getElem?_map,hc,Option.map_some]

 theorem prefixRepresentativeImages_fixed {actual candidate : List Nat} {S : Subst}
    (hlen : actual.length = candidate.length)
    (hassign : ∀ i (hi : i < candidate.length),
      S.onTy (.fvar (actual[i]'(by omega))) = .fvar (prefixRepresentative actual candidate candidate[i])) :
    (prefixRepresentativeImages actual candidate).map (fun v => S.onTy (.fvar v)) =
      (prefixRepresentativeImages actual candidate).map Ty.fvar := by
  apply List.map_congr_left
  intro rep hr
  obtain ⟨c,hc,rfl⟩ := List.mem_map.mp hr
  exact prefixRepresentative_fix_image hlen hassign hc

 theorem prefixRepresentatives_fixed {actual candidate : List Nat} {S : Subst}
    (hlen : actual.length = candidate.length)
    (hassign : ∀ i (hi : i < candidate.length),
      S.onTy (.fvar (actual[i]'(by omega))) = .fvar (prefixRepresentative actual candidate candidate[i])) :
    ∀ v ∈ prefixRepresentatives actual candidate, S.onTy (.fvar v) = .fvar v := by
  intro v hv
  obtain ⟨c,hc,rfl⟩ := List.mem_map.mp hv
  exact prefixRepresentative_fix_image hlen hassign (List.mem_dedup.mp hc)


/-- Realize the class assignment on any distinct selected slots in an allocation
interval. Gaps are permitted; targets may mention any selected slot. -/
 theorem _root_.Subst.override_prefixRepresentatives {S0 : Subst} {actual candidate : List Nat}
    (hS0 : ∀ p ∈ S0, p.2.IsLC) (base frontier : Nat)
    (hlen : actual.length = candidate.length) (hnd : actual.Nodup)
    (hstart : ∀ a ∈ actual, base ≤ a) (hend : ∀ a ∈ actual, a < frontier) :
    ∃ U : Subst, (∀ p ∈ U, p.2.IsLC) ∧ Subst.AgreesBelow base S0 U ∧
      (∀ i (hi : i < candidate.length),
        U.onTy (.fvar (actual[i]'(by omega))) = .fvar (prefixRepresentative actual candidate candidate[i])) ∧
      (∀ v ∈ prefixRepresentatives actual candidate, U.onTy (.fvar v) = .fvar v) := by
  let target := fun a => if a ∈ actual then
    Ty.fvar (prefixRepresentative actual candidate (candidate[actual.idxOf a]?.getD 0))
    else S0.onTy (.fvar a)
  let targets := (freshVars base (frontier - base)).map target
  have htargets : ∀ t ∈ targets, t.IsLC := by
    intro t ht
    obtain ⟨a,_,rfl⟩ := List.mem_map.mp ht
    dsimp only [target]
    split
    · exact .fvar
    · exact Subst.onTy_lc hS0 .fvar
  obtain ⟨U,hU,hagree,hblock⟩ := Subst.override_block hS0 base targets htargets
  have hassign : ∀ i (hi : i < candidate.length),
      U.onTy (.fvar (actual[i]'(by omega))) = .fvar (prefixRepresentative actual candidate candidate[i]) := by
    intro i hi
    have hia : i < actual.length := by omega
    have ha : actual[i] ∈ actual := List.getElem_mem hia
    have haStart := hstart _ ha
    have haEnd := hend _ ha
    have hj : actual[i] - base < frontier - base := by omega
    have hh := hblock (actual[i] - base) (by simpa only [targets,List.length_map,freshVars_length] using hj)
    have hidx : actual.idxOf actual[i] = i := hnd.idxOf_getElem i hia
    simpa only [targets,List.getElem_map,freshVars,List.getElem_range,show base + (actual[i] - base) = actual[i] from by omega,
      target,if_pos ha,hidx,List.getElem?_eq_getElem hi,Option.getD_some] using hh
  exact ⟨U,hU,hagree,hassign,prefixRepresentatives_fixed hlen hassign⟩

 theorem _root_.Subst.AgreesBelow.fixes_prefixProtection {S0 U : Subst} {actual candidate P : List Nat}
    (hlen : actual.length = candidate.length) (hagree : Subst.AgreesBelow base S0 U)
    (hP : ∀ p ∈ P, p < base) (hfix : ∀ p ∈ P, S0.onTy (.fvar p) = .fvar p)
    (hassign : ∀ i (hi : i < candidate.length),
      U.onTy (.fvar (actual[i]'(by omega))) = .fvar (prefixRepresentative actual candidate candidate[i])) :
    ∀ v ∈ P ++ prefixRepresentatives actual candidate, U.onTy (.fvar v) = .fvar v := by
  intro v hv
  rcases List.mem_append.mp hv with hp | hr
  · exact (hagree v (hP v hp)).symm.trans (hfix v hp)
  · exact prefixRepresentatives_fixed hlen hassign v hr



 theorem OpenRecAnn.factor_source {S0 : Subst} {names : List Nat} {target : Ty}
    (h : OpenRecAnn frontier ann next opening)
    (hS0 : ∀ p ∈ S0,p.2.IsLC) (hraw : ∀ v ∈ ann.rigidVars,v < frontier)
    (hfit : (ann.substTyFvars S0).RecFits names target)
    (hcount : names.length = ann.recPrefixCount) (htarget : target.IsLC) :
    ∃ U : Subst,(∀ p ∈ U,p.2.IsLC) ∧ Subst.AgreesBelow frontier S0 U ∧
      opening.written.map (fun v => U.onTy (.fvar v)) = names.map Ty.fvar ∧
      ∀ expected,opening.expected = some expected → U.onTy expected = target := by
  cases h with
  | absent =>
    have hn : names = [] := List.eq_nil_of_length_eq_zero hcount
    subst names
    exact ⟨S0,hS0,fun _ _ => rfl,rfl,fun _ he => by cases he⟩
  | complete => exact False.elim hfit
  | @template next ty frontier template heq hlc =>
    have hn : names = [] := List.eq_nil_of_length_eq_zero hcount
    subst names
    obtain ⟨U,hU,hag,hallocated⟩ := Template.Fits.allocate_override_source hfit htarget hS0 frontier hraw
    refine ⟨U,hU,hag,rfl,?_⟩
    intro expected hex
    cases Option.some.inj hex
    simpa only [heq] using hallocated
  | @partialForall next ty frontier count template heq hlc =>
    have hlen : names.length = count := hcount
    obtain ⟨U0,hU0,hag0,hblock⟩ := Subst.override_block hS0 frontier (names.map Ty.fvar)
      (by intro t ht;obtain ⟨_,_,rfl⟩ := List.mem_map.mp ht;exact .fvar)
    have himages : (freshVars frontier count).map (fun v => U0.onTy (.fvar v)) = names.map Ty.fvar := by
      apply List.ext_getElem
      · simp only [List.length_map,freshVars_length];exact hlen.symm
      · intro i hi hj
        have hin : i < names.length := by simpa only [List.length_map] using hj
        have hh := hblock i (by simpa only [List.length_map] using hin)
        simpa only [List.getElem_map,freshVars,List.getElem_range] using hh
    have hnewFit : ((template.openTyVarsFrom 0 (freshVars frontier count)).substTyFvars U0).Fits target := by
      rw [Template.substTyFvars_openTyVarsFrom_of_images _ hU0 himages 0]
      have heqSource : template.substTyFvars U0 = template.substTyFvars S0 :=
        template.substTyFvars_congr (fun v hv => (hag0 v (hraw v hv)).symm)
      rw [heqSource]
      exact hfit.2
    have hopenedRaw : ∀ v ∈ (template.openTyVarsFrom 0 (freshVars frontier count)).rigidVars,v < frontier+count := by
      intro v hv
      rcases List.mem_append.mp (template.openTyVarsFrom_scope (K := template.rigidVars) (fun _ h => h) 0 _ v hv) with hv | hv
      · have := hraw v hv;omega
      · exact freshVars_lt v hv
    obtain ⟨U,hU,hag,hallocated⟩ := hnewFit.allocate_override_source htarget hU0 (frontier+count) hopenedRaw
    refine ⟨U,hU,fun v hv => (hag0 v hv).trans (hag v (by omega)),?_,?_⟩
    · change (freshVars frontier count).map (fun v => U.onTy (.fvar v)) = _
      calc
        _ = (freshVars frontier count).map (fun v => U0.onTy (.fvar v)) :=
          List.map_congr_left (fun v hv => (hag v (freshVars_lt v hv)).symm)
        _ = names.map Ty.fvar := himages
    · intro expected hex
      cases Option.some.inj hex
      simpa only [heq] using hallocated

 theorem OpenRecAnns.factor_source {S0 : Subst}
    (h : OpenRecAnns members index frontier anns next openings)
    (hS0 : ∀ p ∈ S0,p.2.IsLC) (hraw : ∀ ann ∈ anns,∀ v ∈ ann.rigidVars,v < frontier)
    (targetNames : List (List Nat)) (targetTypes : List Ty)
    (hNames : targetNames.length = anns.length) (hTypes : targetTypes.length = anns.length)
    (hfit : ∀ (j : Nat) (ann : LetAnn) (names : List Nat) (target : Ty),index+j ∈ members →
      anns[j]? = some ann → targetNames[j]? = some names → targetTypes[j]? = some target →
      (ann.substTyFvars S0).RecFits names target ∧ names.length = ann.recPrefixCount ∧ target.IsLC) :
    ∃ U : Subst,(∀ p ∈ U,p.2.IsLC) ∧ Subst.AgreesBelow frontier S0 U ∧
      ∀ (j : Nat) (opening : RecOpening) (names : List Nat) (target : Ty),index+j ∈ members →
        openings[j]? = some opening → targetNames[j]? = some names → targetTypes[j]? = some target →
        opening.written.map (fun v => U.onTy (.fvar v)) = names.map Ty.fvar ∧
        ∀ expected,opening.expected = some expected → U.onTy expected = target := by
  induction h generalizing S0 targetNames targetTypes with
  | nil =>
    refine ⟨S0,hS0,fun _ _ => rfl,?_⟩
    intro j opening names target _ ho
    simp at ho
  | @skip index frontier rest next openings ann hn hr ih =>
    cases targetNames with
    | nil => simp at hNames
    | cons names targetNames =>
      cases targetTypes with
      | nil => simp at hTypes
      | cons target targetTypes =>
        obtain ⟨U,hU,hag,htail⟩ := ih hS0
          (fun ann ha => hraw ann (List.mem_cons_of_mem _ ha)) targetNames targetTypes
          (Nat.succ.inj hNames) (Nat.succ.inj hTypes)
          (fun j ann names target hm ha hn ht => hfit (j+1) ann names target
            (by simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hm) ha hn ht)
        refine ⟨U,hU,hag,?_⟩
        intro j opening names target hm ho hn' ht
        cases j with
        | zero => exact False.elim (hn (by simpa using hm))
        | succ j =>
          exact htail j opening names target
            (by simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hm) ho hn' ht
  | @cons index frontier ann middle opening rest next openings hm hh hr ih =>
    cases targetNames with
    | nil => simp at hNames
    | cons names targetNames =>
      cases targetTypes with
      | nil => simp at hTypes
      | cons target targetTypes =>
        obtain ⟨hfitHead,hcountHead,hLCHead⟩ := hfit 0 ann names target (by simpa using hm) rfl rfl rfl
        obtain ⟨U1,hU1,hag1,himHead,hexHead⟩ := hh.factor_source hS0 (hraw ann List.mem_cons_self)
          hfitHead hcountHead hLCHead
        have hle := hh.frontier_le
        obtain ⟨U,hU,hag,htail⟩ := ih hU1
          (fun ann ha v hv => (hraw ann (List.mem_cons_of_mem _ ha) v hv).trans_le hle)
          targetNames targetTypes (Nat.succ.inj hNames) (Nat.succ.inj hTypes)
          (by
            intro j ann names target hm ha hn ht
            have hfitOld := hfit (j+1) ann names target
              (by simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hm) ha hn ht
            have heq : ann.substTyFvars U1 = ann.substTyFvars S0 :=
              ann.substTyFvars_congr (fun v hv => (hag1 v (hraw ann (List.mem_cons_of_mem _ (List.mem_of_getElem? ha)) v hv)).symm)
            rw [heq]
            exact hfitOld)
        refine ⟨U,hU,fun v hv => (hag1 v hv).trans (hag v (hv.trans_le hle)),?_⟩
        intro j opening' names' target' hm' ho hn ht
        cases j with
        | zero =>
          cases Option.some.inj ho
          cases Option.some.inj hn
          cases Option.some.inj ht
          refine ⟨?_,?_⟩
          · calc
              opening.written.map (fun v => U.onTy (.fvar v)) = opening.written.map (fun v => U1.onTy (.fvar v)) :=
                List.map_congr_left (fun v hv => (hag v (hh.written_range v hv).2).symm)
              _ = names.map Ty.fvar := himHead
          · intro expected he
            exact (Subst.onTy_congr hag (hh.expected_below (hraw ann List.mem_cons_self) he)).symm.trans (hexHead expected he)
        | succ j =>
          exact htail j opening' names' target'
            (by simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hm') ho hn ht

theorem _root_.Infer.sourcePrincipal_backend {input : Input} {core : Expr}
    (hemb : input.toCore = some core)
    (h : CoreBackend.Infer K frontier ctx core next subst ty)
    (hctx : CtxBelow frontier ctx) (hK : ∀ k ∈ K, k < frontier)
    (hr : ∀ v ∈ core.tyFreeVars, v ∈ K)
    (hdisj : ∀ v ∈ core.tyFreeVars, v ∉ softVars F) :
    Infer.SourcePrincipal (.backend hemb h hctx hK hr hdisj) := by
  intro hwf hb _ _ ambient target P hlc hP hfix hfreeze ht
  have heq : input.substTyFvars ambient = input := input.substTyFvars_eq_self_of_fixes (by
    intro v hv
    have hcore := (input.toCore_rigidVars hemb v).mp hv
    exact hfreeze v hv (hr v hcore) (hdisj v hcore))
  rw [heq] at ht
  obtain ⟨ht, hscope⟩ := ht.toCore hemb
  exact h.principal hwf hb ambient target P hlc hP hscope hfix ht

theorem _root_.Infer.sourcePrincipal_lambda {ctx : Ctx}
    (hscope : SourceScope K F (.lambda ann body))
    (hs : Seed (K ++ softVars F) frontier ann param initial)
    (hb : Infer K F initial { ctx with env := PolyTy.mkTrivial param :: ctx.env }
      body next subst completed bodyTy)
    (ih : Infer.SourcePrincipal hb) : Infer.SourcePrincipal (.lambda hscope hs hb) := by
  intro hwf hbelow hK hF ambient target P hS hP hfix hfreeze htyping
  obtain ⟨paramD, resultD, rfl, hparamD, hfit, _, hbodyD⟩ := htyping.lambda_inv
  have hscopeBound : ∀ v ∈ K ++ softVars F, v < frontier :=
    fun v hv => (List.mem_append.mp hv).elim (hK v) (softVars_lt hF v)
  have hbodyBound : ∀ v ∈ body.rigidVars, v < frontier :=
    fun v hv => hscopeBound v (hscope v (List.mem_append_right _ hv))
  obtain ⟨U, hU, hUagree, hUparam⟩ := hs.override hscopeBound hparamD hS (by
    intro t ht
    subst ann
    exact hfit (t.substTyFvars ambient) rfl)
  have hle := hs.frontier_le
  have hbodywf : CtxWF { ctx with env := PolyTy.mkTrivial param :: ctx.env } := by
    intro M hM
    rcases List.mem_cons.mp hM with rfl | hM
    · exact hs.lc
    · exact hwf M hM
  have hbodybelow : CtxBelow initial { ctx with env := PolyTy.mkTrivial param :: ctx.env } := by
    intro M hM
    rcases List.mem_cons.mp hM with rfl | hM
    · exact hs.belowFvars hscopeBound
    · exact (hbelow M hM).mono hle
  have hctxeq : U.onCtx { ctx with env := PolyTy.mkTrivial param :: ctx.env } =
      { ambient.onCtx ctx with env := PolyTy.mkTrivial paramD :: (ambient.onCtx ctx).env } := by
    have heq := Subst.onCtx_congr hUagree hbelow
    simpa only [Subst.onCtx, Subst.onEnv, List.map_cons, Subst.onPolyTy, PolyTy.mkTrivial,
      hUparam] using congrArg (fun c : Ctx => { c with env := PolyTy.mkTrivial paramD :: c.env }) heq.symm
  have hsourceeq : body.substTyFvars U = body.substTyFvars ambient :=
    body.substTyFvars_congr (fun v hv => (hUagree v (hbodyBound v hv)).symm)
  have hUfix : ∀ p ∈ P, U.onTy (.fvar p) = .fvar p :=
    fun p hp => (hUagree p (hP p hp)).symm.trans (hfix p hp)
  obtain ⟨R, hR, hresult, hRP, hag⟩ := ih hbodywf hbodybelow
    (fun k hk => Nat.lt_of_lt_of_le (hK k hk) hle)
    (fun t ht => (hF t ht).mono hle) U resultD P hU
    (fun p hp => Nat.lt_of_lt_of_le (hP p hp) hle) hUfix
    (fun v hv hk hnot => (hUagree v (hbodyBound v hv)).symm.trans
      (hfreeze v (List.mem_append_right _ hv) hk hnot)) (by rwa [hctxeq, hsourceeq])
  refine ⟨R, hR, ?_, hRP, fun v hv => (hUagree v hv).trans (hag v (Nat.lt_of_lt_of_le hv hle))⟩
  rw [Subst.onTy_arrow, ← hresult]
  congr 1
  have hp := Subst.onTy_congr hag (hs.belowFvars hscopeBound)
  rw [Subst.onTy_append, hUparam] at hp
  exact hp

theorem _root_.Infer.sourcePrincipal_app
    (hscope : SourceScope K F (.app f arg))
    (hf : Infer K F frontier ctx f first s1 fOut fTy)
    (ha : Infer K (substSoft s1 F) first (s1.onCtx ctx) (arg.substTyFvars s1) second s2 argOut argTy)
    (hu : RigidUnify K (s2.onTy fTy) (.arrow argTy (.fvar second)) s3)
    (ihf : Infer.SourcePrincipal hf) (iha : Infer.SourcePrincipal ha) :
    Infer.SourcePrincipal (.app hscope hf ha hu) := by
  intro hwf hbelow hK hF ambient target P hS hP hfix hfreeze htyping
  obtain ⟨paramD, hfD, haD⟩ := htyping.app_inv
  obtain ⟨Rf, hRf, hfTy, hRfP, hagf⟩ := ihf hwf hbelow hK hF ambient
    (.arrow paramD target) P hS hP hfix
    (fun v hv => hfreeze v (List.mem_append_left _ hv)) hfD
  have hfle := hf.frontier_le
  have hale := ha.frontier_le
  obtain ⟨hfB, hs1B⟩ := hf.belowFvars hbelow hK hF
  obtain ⟨_, hs1lc⟩ := hf.lc hwf
  have hctx1 := Subst.onCtx_below hs1B hfle hbelow
  have hK1 : ∀ k ∈ K, k < first := fun k hk => Nat.lt_of_lt_of_le (hK k hk) hfle
  have hP1 : ∀ p ∈ P, p < first := fun p hp => Nat.lt_of_lt_of_le (hP p hp) hfle
  have hctxeq : ambient.onCtx ctx = Rf.onCtx (s1.onCtx ctx) := by
    rw [← Subst.onCtx_append]
    exact Subst.onCtx_congr hagf hbelow
  have hargScope : SourceScope K F arg := fun v hv => hscope v (List.mem_append_right _ hv)
  have hargBelow : ∀ v ∈ arg.rigidVars, v < frontier := fun v hv =>
    (List.mem_append.mp (hargScope v hv)).elim (hK v) (softVars_lt hF v)
  have hF1 := substSoft_below hs1B hfle hF
  have hsourceeq : arg.substTyFvars ambient = (arg.substTyFvars s1).substTyFvars Rf := by
    rw [← Input.substTyFvars_append]
    exact arg.substTyFvars_congr (fun v hv => hagf v (hargBelow v hv))
  have hfreeze1 := hargScope.residual_freeze hargBelow (Subst.fixes_of_dom_avoids hf.dom_avoids)
    (fun v hv => hfreeze v (List.mem_append_right _ hv)) hagf
  obtain ⟨Ra, hRa, haTy, hRaP, haga⟩ := iha (Subst.onCtx_wf hs1lc hwf) hctx1 hK1 hF1
    Rf paramD P hRf hP1 hRfP hfreeze1 (by rwa [← hctxeq, ← hsourceeq])
  obtain ⟨haB, hs2B⟩ := ha.belowFvars hctx1 hK1 hF1
  have hleftB := Subst.onTy_belowFvars hs2B (hfB.mono hale)
  have hleft : Ra.onTy (s2.onTy fTy) = .arrow paramD target := by
    have heq := Subst.onTy_congr haga hfB
    rw [Subst.onTy_append, ← hfTy] at heq
    exact heq.symm
  have htargetlc := htyping.regular
  obtain ⟨U, hU, hUagree, hUblock⟩ := Subst.override_block hRa second [target]
    (by simpa using htargetlc)
  have hUret : U.onTy (.fvar second) = target := by simpa using hUblock 0 (by simp)
  have hUP : ∀ p ∈ P, U.onTy (.fvar p) = .fvar p := fun p hp =>
    (hUagree p (Nat.lt_of_lt_of_le (hP1 p hp) hale)).symm.trans (hRaP p hp)
  have hUni : Unifies U (s2.onTy fTy) (.arrow argTy (.fvar second)) := by
    change U.onTy (s2.onTy fTy) = U.onTy (.arrow argTy (.fvar second))
    rw [← Subst.onTy_congr hUagree hleftB, hleft, Subst.onTy_arrow,
      ← Subst.onTy_congr hUagree haB, ← haTy, hUret]
  obtain ⟨R, hfac, hR, hRP⟩ := hu.unifies.greatest_K U hU hUni hUP
  have hag3 : Subst.AgreesBelow second Ra (s3 ++ R) := by
    intro v hv
    rw [Subst.onTy_append]
    exact (hUagree v hv).trans (hfac (.fvar v))
  have hag2 := Subst.AgreesBelow.trans_append hale haga hs2B hag3
  have hag1 := Subst.AgreesBelow.trans_append hfle hagf hs1B hag2
  refine ⟨R, hR, ?_, hRP, ?_⟩
  · exact hUret.symm.trans (hfac (.fvar second))
  · simpa only [List.append_assoc] using hag1





theorem LetCheck.factor_source {P : List Nat} (hc : LetCheck K F first rhsTy ann checked sCheck)
    (hrigid : ∀ v ∈ ann.rigidVars, v < first) (hP : ∀ p ∈ P, p < first)
    (hty : Ty.BelowFvars first rhsTy)
    {R : Subst} (hR : ∀ pair ∈ R, pair.2.IsLC)
    (hRP : ∀ p ∈ P, R.onTy (.fvar p) = .fvar p)
    {target : Ty} (htarget : target.IsLC) (hfit : (ann.substTyFvars R).FitsMono target)
    (heq : target = R.onTy rhsTy) :
    ∃ V : Subst, (∀ pair ∈ V, pair.2.IsLC) ∧
      target = V.onTy (sCheck.onTy rhsTy) ∧
      (∀ p ∈ P, V.onTy (.fvar p) = .fvar p) ∧
      Subst.AgreesBelow first R (sCheck ++ V) := by
  cases hc with
  | absent => exact ⟨R, hR, heq, hRP, fun _ _ => rfl⟩
  | hole => exact ⟨R, hR, heq, hRP, fun _ _ => rfl⟩
  | @template checked expected sCheck template halloc _ _ hu =>
    change (template.substTyFvars R).Fits target at hfit
    obtain ⟨U, hU, hag, hUexpected⟩ := hfit.allocate_override_source htarget hR first hrigid
    rw [halloc] at hUexpected
    have hUty : U.onTy rhsTy = target := (Subst.onTy_congr hag hty).symm.trans heq.symm
    have hUP : ∀ p ∈ P, U.onTy (.fvar p) = .fvar p :=
      fun p hp => (hag p (hP p hp)).symm.trans (hRP p hp)
    obtain ⟨V, hfac, hV, hVP⟩ := hu.unifies.greatest_K U hU
      (hUty.trans hUexpected.symm) hUP
    refine ⟨V, hV, hUty.symm.trans (hfac rhsTy), hVP, ?_⟩
    intro v hv
    simpa only [Subst.onTy_append] using (hag v hv).trans (hfac (.fvar v))

/-- The signed version protects the candidate set and the written names
pointwise, while allowing authored provisional leaves to specialize. -/
theorem SignatureCheck.factor_source {P : List Nat}
    (hc : SignatureCheck K F written first rhsTy ann checked sCheck)
    (_hprefix : written.length = ann.paramCount)
    (hrigid : ∀ v ∈ ann.rigidVars, v < first)
    (hP : ∀ p ∈ P ++ written, p < first) (hty : Ty.BelowFvars first rhsTy)
    {R : Subst} (hR : ∀ pair ∈ R, pair.2.IsLC)
    (hRP : ∀ p ∈ P ++ written, R.onTy (.fvar p) = .fvar p)
    {target : Ty} (htarget : target.IsLC) (heq : target = R.onTy rhsTy)
    (hcomplete : ∀ scheme, ann = .complete scheme → target = (R.onPolyTy scheme).openVars written)
    (hpartial : ∀ count template, ann = .partialForall count template →
      ((template.substTyFvars R).openTyVarsFrom 0 written).Fits target) :
    ∃ V : Subst, (∀ pair ∈ V, pair.2.IsLC) ∧
      target = V.onTy (sCheck.onTy rhsTy) ∧
      (∀ p ∈ P ++ written, V.onTy (.fvar p) = .fvar p) ∧
      Subst.AgreesBelow first R (sCheck ++ V) := by
  have hW : ∀ w ∈ written, R.onTy (.fvar w) = .fvar w :=
    fun w hw => hRP w (List.mem_append_right _ hw)
  cases hc with
  | @complete sCheck scheme _ _ hu =>
    have hExpected : R.onTy (scheme.openVars written) = (R.onPolyTy scheme).openVars written :=
      Subst.onTy_openVars_of_fixes hR hW
    have hUni : Unifies R rhsTy (scheme.openVars written) :=
      heq.symm.trans ((hcomplete scheme rfl).trans hExpected.symm)
    obtain ⟨V, hfac, hV, hVP⟩ := hu.unifies.greatest_K R hR hUni hRP
    refine ⟨V, hV, heq.trans (hfac rhsTy), hVP, ?_⟩
    intro v hv
    simpa only [Subst.onTy_append] using hfac (.fvar v)
  | @partialSignature checked expected sCheck count template halloc _ _ hu =>
    have hfit := hpartial count template rfl
    rw [← Template.substTyFvars_openTyVarsFrom_of_fixes template hR hW 0] at hfit
    obtain ⟨U, hU, hag, hUexpected⟩ := hfit.allocate_override_source htarget hR first (by
      intro v hv
      exact (List.mem_append.mp (Template.open_scope (K := template.rigidVars) (fun _ h => h) v hv)).elim
        (hrigid v) (fun hv => hP v (List.mem_append_right _ hv)))
    rw [halloc] at hUexpected
    have hUty : U.onTy rhsTy = target := (Subst.onTy_congr hag hty).symm.trans heq.symm
    have hUP : ∀ p ∈ P ++ written, U.onTy (.fvar p) = .fvar p :=
      fun p hp => (hag p (hP p hp)).symm.trans (hRP p hp)
    obtain ⟨V, hfac, hV, hVP⟩ := hu.unifies.greatest_K U hU
      (hUty.trans hUexpected.symm) hUP
    refine ⟨V, hV, hUty.symm.trans (hfac rhsTy), hVP, ?_⟩
    intro v hv
    simpa only [Subst.onTy_append] using (hag v hv).trans (hfac (.fvar v))

theorem closeScheme_generalizes {K names : List Nat} {ctx : Ctx} {ty : Ty}
    {V : Subst} {M : PolyTy} {Xs : List Nat}
    (hty : ty.IsLC) (hV : ∀ pair ∈ V, pair.2.IsLC) (hM : M.WF)
    (hXnodup : Xs.Nodup) (hXlen : Xs.length = M.paramCount)
    (hXM : ∀ x ∈ Xs, x ∉ M.body.freeVars)
    (htarget : M.openVars Xs = V.onTy ty)
    (hXctx : ∀ x ∈ Xs, x ∉ (V.onCtx ctx).env.freeVars)
    (hXK : ∀ x ∈ Xs, ∀ k ∈ K, x ∉ (V.onTy (.fvar k)).freeVars)
    (hcover : ∀ v ∈ ty.freeVars, v ∉ names → v ∈ ctx.env.freeVars ∨ v ∈ K) :
    (V.onPolyTy ⟨names.length, Ty.closeOver names ty⟩).Generalizes M := by
  apply closeOver_generalizes hty hV hM hXnodup hXlen hXM htarget
  intro x hx hcx
  rw [Subst.onPolyTy, Ty.mem_freeVars_onTy_iff] at hcx
  obtain ⟨v, hv, hxv⟩ := hcx
  have hvty := Ty.closeOver_freeVars_subset hv
  have hvnot : v ∉ names := fun hg => Ty.not_mem_closeOver_freeVars hg hv
  have hor := hcover v hvty hvnot
  rcases hor with henv | hk
  · obtain ⟨scheme, hs, hv⟩ := Env.mem_freeVars_iff.mp henv
    apply hXctx x hx
    apply Env.mem_freeVars_iff.mpr
    refine ⟨V.onPolyTy scheme, List.mem_map.mpr ⟨scheme, hs, rfl⟩, ?_⟩
    exact Ty.mem_freeVars_onTy_iff.mpr ⟨v, hv, hxv⟩
  · exact hXK x hx v hk hxv


theorem genScheme_generalizes {K : List Nat} {ctx : Ctx} {ty : Ty}
    {V : Subst} {M : PolyTy} {Xs : List Nat}
    (hty : ty.IsLC) (hV : ∀ pair ∈ V, pair.2.IsLC) (hM : M.WF)
    (hXnodup : Xs.Nodup) (hXlen : Xs.length = M.paramCount)
    (hXM : ∀ x ∈ Xs, x ∉ M.body.freeVars)
    (htarget : M.openVars Xs = V.onTy ty)
    (hXctx : ∀ x ∈ Xs, x ∉ (V.onCtx ctx).env.freeVars)
    (hXK : ∀ x ∈ Xs, ∀ k ∈ K, x ∉ (V.onTy (.fvar k)).freeVars) :
    (V.onPolyTy (genScheme K ctx.env ty)).Generalizes M := by
  apply closeScheme_generalizes hty hV hM hXnodup hXlen hXM htarget hXctx hXK
  intro v hv hnot
  by_cases he : v ∈ ctx.env.freeVars
  · exact .inl he
  · by_cases hk : v ∈ K
    · exact .inr hk
    · exfalso
      apply hnot
      simp only [genVars, List.mem_filter, Bool.and_eq_true]
      exact ⟨hv, by simpa using he, by simpa using hk⟩

theorem SignatureCheck.cover (h : SignatureCheck K F written frontier ty ann next subst)
    (hlen : written.length = ann.paramCount) (hlc : ty.IsLC)
    (hsource : ∀ v ∈ (ann.substTyFvars subst).rigidVars, v ∈ Q) :
    ∀ v ∈ (subst.onTy ty).freeVars,
      v ∉ signatureNames (ann.substTyFvars subst) Q written ctx (subst.onTy ty) →
        v ∈ ctx.env.freeVars ∨ v ∈ Q := by
  have hcomp := h.completion (Q := Q) (ctx := ctx) hlen hlc
  cases h with
  | complete _ _ _ =>
    cases hcomp with
    | complete _ heq =>
      intro v hv hnot
      rw [heq] at hv
      rcases Ty.freeVars_openVars_subset v hv with hv | hv
      · exact .inr (hsource v hv)
      · exact False.elim (hnot hv)
  | partialSignature _ _ _ _ =>
    intro v hv hnot
    change v ∉ written ++ genVars (Q ++ written) ctx.env (subst.onTy ty) at hnot
    by_cases he : v ∈ ctx.env.freeVars
    · exact .inl he
    · by_cases hk : v ∈ Q
      · exact .inr hk
      · have hw : v ∉ written := fun hc => hnot (List.mem_append_left _ hc)
        exfalso
        apply hnot
        apply List.mem_append_right
        simp only [genVars, List.mem_filter, Bool.and_eq_true]
        have hkw : v ∉ Q ++ written := by simpa only [List.mem_append, not_or] using And.intro hk hw
        exact ⟨hv, by simpa using he, by simpa using hkw⟩

theorem SignatureCheck.scheme_generalizes
    (h : SignatureCheck K F written frontier ty ann next subst)
    (hlen : written.length = ann.paramCount) (hnd : written.Nodup) (hlc : ty.IsLC)
    (hsource : ∀ v ∈ (ann.substTyFvars subst).rigidVars, v ∈ Q)
    (havoid : ∀ name ∈ written, name ∉ Q)
    {V : Subst} {M : PolyTy} {Xs : List Nat}
    (hV : ∀ pair ∈ V, pair.2.IsLC) (hM : M.WF)
    (hXnodup : Xs.Nodup) (hXlen : Xs.length = M.paramCount)
    (hXM : ∀ x ∈ Xs, x ∉ M.body.freeVars)
    (htarget : M.openVars Xs = V.onTy (subst.onTy ty))
    (hXctx : ∀ x ∈ Xs, x ∉ (V.onCtx ctx).env.freeVars)
    (hXK : ∀ x ∈ Xs, ∀ k ∈ Q, x ∉ (V.onTy (.fvar k)).freeVars) :
    (V.onPolyTy (signatureScheme (ann.substTyFvars subst) Q written ctx (subst.onTy ty))).Generalizes M := by
  rw [h.scheme_eq_close hlen hlc hnd hsource havoid]
  exact closeScheme_generalizes (Subst.onTy_lc (h.lc hlen hlc) hlc)
    hV hM hXnodup hXlen hXM htarget hXctx hXK (h.cover hlen hlc hsource)

theorem _root_.Infer.source_signature_frame_aligned {rhs body : Input} {ann : LetAnn}
    (hscope : SourceScope K F (.letIn ann rhs body))
    (hr : Infer (K ++ Ys) F (frontier + ann.paramCount) ctx (rhs.openTyVars Ys) first s1 rhsOut rhsTy)
    (hc : SignatureCheck K (substSoft s1 F) Ys first rhsTy (ann.substTyFvars s1) checked sCheck)
    (ihr : Infer.SourcePrincipal hr)
    (hprefix : Ys = freshVars frontier ann.paramCount)
    (hwf : CtxWF ctx) (hbelow : CtxBelow frontier ctx) (hK : ∀ k ∈ K, k < frontier)
    (hF : ∀ t ∈ F, Ty.BelowFvars frontier t)
    {ambient : Subst} {P : List Nat} {M : PolyTy} {Xs : List Nat} {target : Ty}
    (hS : ∀ pair ∈ ambient, pair.2.IsLC) (hP : ∀ p ∈ P, p < frontier)
    (hfix : ∀ p ∈ P ++ Ys, ambient.onTy (.fvar p) = .fvar p)
    (hfreeze : ∀ v ∈ (Input.letIn ann rhs body).rigidVars,
      v ∈ K → v ∉ softVars F → ambient.onTy (.fvar v) = .fvar v)
    (hM : M.WF) (_hannRigid : ∀ v ∈ (ann.substTyFvars ambient).rigidVars, v ∈ P)
    (hXlen : Xs.length = M.paramCount) (hXnd : Xs.Nodup) (hXtake : Xs.take ann.paramCount = Ys)
    (hannFits : (ann.substTyFvars ambient).SignatureFits M Xs)
    (hrD : Typing (P ++ Ys) (ambient.onCtx ctx)
      ((rhs.substTyFvars ambient).openTyVars Ys) (M.openVars Xs))
    (hbD : Typing P { ambient.onCtx ctx with env := M :: (ambient.onCtx ctx).env }
      (body.substTyFvars ambient) target)
    (hXM : ∀ x ∈ Xs, x ∉ M.body.freeVars)
    (hXctx : ∀ x ∈ Xs, x ∉ (ambient.onCtx ctx).env.freeVars)
    (hXimages : ∀ x ∈ Xs, ∀ k ∈ K, x ∉ (ambient.onTy (.fvar k)).freeVars)
    (hXsoft : ∀ x ∈ Xs, x ∉ softVars (substSoft ambient F)) :
    let checkedCtx := sCheck.onCtx (s1.onCtx ctx)
    let soft := substSoft (s1 ++ sCheck) F
    let scheme := signatureScheme (ann.substTyFvars (s1 ++ sCheck)) (K ++ softVars soft) Ys checkedCtx (sCheck.onTy rhsTy)
    ∃ V : Subst, (∀ pair ∈ V, pair.2.IsLC) ∧
      (∀ p ∈ P ++ Ys, V.onTy (.fvar p) = .fvar p) ∧
      Subst.AgreesBelow (frontier + ann.paramCount) ambient ((s1 ++ sCheck) ++ V) ∧
      Typing P (V.onCtx { checkedCtx with env := scheme :: checkedCtx.env })
        ((body.substTyFvars (s1 ++ sCheck)).substTyFvars V) target ∧
      CtxWF { checkedCtx with env := scheme :: checkedCtx.env } ∧
      CtxBelow checked { checkedCtx with env := scheme :: checkedCtx.env } ∧
      (∀ pair ∈ s1 ++ sCheck, Ty.BelowFvars checked pair.2) ∧
      (∀ y ∈ Ys, y ∉ checkedCtx.env.freeVars ++ softVars soft) := by

  dsimp only
  have hscopeBound : ∀ v ∈ K ++ softVars F, v < frontier :=
    fun v hv => (List.mem_append.mp hv).elim (hK v) (softVars_lt hF v)
  have hYlen : Ys.length = ann.paramCount := by rw [hprefix, freshVars_length]
  have hYnd : Ys.Nodup := hprefix ▸ freshVars_nodup
  have hYavoid : ∀ y ∈ Ys, y ∉ K := by
    intro y hy hk
    have := freshVars_ge y (hprefix ▸ hy)
    have := hK y hk
    omega
  have hKopen : ∀ k ∈ K ++ Ys, k < frontier + ann.paramCount := by
    intro k hk
    rcases List.mem_append.mp hk with hk | hk
    · have := hK k hk; omega
    · exact freshVars_lt k (hprefix ▸ hk)
  have hPopen : ∀ p ∈ P ++ Ys, p < frontier + ann.paramCount := by
    intro p hp
    rcases List.mem_append.mp hp with hp | hp
    · have := hP p hp; omega
    · exact freshVars_lt p (hprefix ▸ hp)
  have hbelowOpen : CtxBelow (frontier + ann.paramCount) ctx :=
    fun scheme hs => (hbelow scheme hs).mono (by omega)
  have hFopen : ∀ t ∈ F, Ty.BelowFvars (frontier + ann.paramCount) t :=
    fun t ht => (hF t ht).mono (by omega)
  have hfreezeOpen : ∀ v ∈ (rhs.openTyVars Ys).rigidVars,
      v ∈ K ++ Ys → v ∉ softVars F → ambient.onTy (.fvar v) = .fvar v := by
    intro v hv hk hn
    rcases Input.rigidVars_openTyVarsFrom hv with hv | hy
    · by_cases hy : v ∈ Ys
      · exact hfix v (List.mem_append_right _ hy)
      · have hvK : v ∈ K := (List.mem_append.mp hk).resolve_right hy
        exact hfreeze v (List.mem_append_left _ (List.mem_append_right _ hv)) hvK hn
    · exact hfix v (List.mem_append_right _ hy)
  have hrD' : Typing (P ++ Ys) (ambient.onCtx ctx)
      ((rhs.openTyVars Ys).substTyFvars ambient) (M.openVars Xs) := by
    rw [rhs.substTyFvars_openTyVars_of_fixes hS (fun y hy => hfix y (List.mem_append_right _ hy))]
    exact hrD
  obtain ⟨R, hR, hrTy, hRP, hagR⟩ := ihr hwf hbelowOpen hKopen hFopen ambient
    (M.openVars Xs) (P ++ Ys) hS hPopen hfix hfreezeOpen hrD'
  have hrle := hr.frontier_le
  have hcle := hc.frontier_le
  have hK1 : ∀ k ∈ K ++ Ys, k < first := fun k hk => Nat.lt_of_lt_of_le (hKopen k hk) hrle
  have hP1 : ∀ p ∈ P ++ Ys, p < first := fun p hp => Nat.lt_of_lt_of_le (hPopen p hp) hrle
  obtain ⟨hrB, hs1B⟩ := hr.belowFvars hbelowOpen hKopen hFopen
  obtain ⟨hrLC, hs1LC⟩ := hr.lc hwf
  have hF1 := substSoft_below hs1B hrle hFopen
  have hs1Fix : ∀ k ∈ K, s1.onTy (.fvar k) = .fvar k :=
    Subst.fixes_of_dom_avoids (fun p hp hk => hr.dom_avoids p hp (List.mem_append_left _ hk))
  have hannEq : (ann.substTyFvars s1).substTyFvars R = ann.substTyFvars ambient := by
    rw [← LetAnn.substTyFvars_append]
    exact ann.substTyFvars_congr (fun v hv => (hagR v (by
      have := hscopeBound v (hscope v (List.mem_append_left _ (List.mem_append_left _ hv)))
      omega)).symm)
  have hannBound : ∀ v ∈ (ann.substTyFvars s1).rigidVars, v < first := by
    intro v hv
    have hs := hscope.subst s1 hs1Fix
    exact (List.mem_append.mp (hs v (List.mem_append_left _ (List.mem_append_left _ hv)))).elim
      (fun hk => hK1 v (List.mem_append_left _ hk)) (softVars_lt hF1 v)
  have hYlen' : Ys.length = (ann.substTyFvars s1).paramCount := by simpa using hYlen
  have hannFits' : ((ann.substTyFvars s1).substTyFvars R).SignatureFits M Xs := hannEq.symm ▸ hannFits
  obtain ⟨V, hV, hcheckedTy, hVP, hagV⟩ := hc.factor_source hYlen' hannBound hP1 hrB hR hRP
    hrD.regular hrTy
    (by
      intro scheme heq
      rw [heq] at hannFits'
      cases hannFits'
      have htake : Xs.take (R.onPolyTy scheme).paramCount = Xs := List.take_of_length_le hXlen.le
      have hcounts : ann.paramCount = (R.onPolyTy scheme).paramCount := by
        have := congrArg LetAnn.paramCount heq
        simpa using this
      rw [hcounts, htake] at hXtake
      exact congrArg (R.onPolyTy scheme).openVars hXtake)
    (by
      intro count template heq
      rw [heq] at hannFits'
      cases hannFits' with
      | partialSignature _ hfits =>
        have hcounts : ann.paramCount = count := by
          have := congrArg LetAnn.paramCount heq
          simpa using this
        simpa only [← hcounts, hXtake] using hfits)
  have hsCheckLC := hc.lc hYlen' hrLC
  have hsCheckB := hc.belowFvars hrB
    (fun k hk => hK1 k (List.mem_append_left _ hk))
    (fun y hy => hK1 y (List.mem_append_right _ hy)) hF1
  have hprefixB : ∀ pair ∈ s1 ++ sCheck, Ty.BelowFvars checked pair.2 := by
    intro pair hp
    exact (List.mem_append.mp hp).elim (fun hp => (hs1B pair hp).mono hcle) (hsCheckB pair)
  have hagPrefix := Subst.AgreesBelow.trans_append hrle hagR hs1B hagV
  have hctxBridge : V.onCtx (sCheck.onCtx (s1.onCtx ctx)) = ambient.onCtx ctx := by
    rw [← Subst.onCtx_append, ← Subst.onCtx_append]
    simpa only [List.append_assoc] using (Subst.onCtx_congr hagPrefix hbelowOpen).symm
  have hprefixFix : ∀ k ∈ K, (s1 ++ sCheck).onTy (.fvar k) = .fvar k := by
    apply Subst.fixes_of_dom_avoids
    intro pair hp
    exact (List.mem_append.mp hp).elim
      (fun hp => fun hk => hr.dom_avoids pair hp (List.mem_append_left _ hk))
      (fun hp => fun hk => hc.dom_avoids pair hp (List.mem_append_left _ hk))
  have hVimages : ∀ x ∈ Xs, ∀ k ∈ K ++ softVars (substSoft (s1 ++ sCheck) F),
      x ∉ (V.onTy (.fvar k)).freeVars := by
    intro x hx k hk hv
    rcases List.mem_append.mp hk with hk | hk
    · have heq := hagPrefix k (hKopen k (List.mem_append_left _ hk))
      rw [Subst.onTy_append, hprefixFix k hk] at heq
      rw [← heq] at hv
      exact hXimages x hx k hk hv
    · obtain ⟨ty, hty, hk⟩ := TyList.mem_freeVars_iff.mp hk
      obtain ⟨original, ho, rfl⟩ := List.mem_map.mp hty
      have himage : x ∈ (V.onTy ((s1 ++ sCheck).onTy original)).freeVars :=
        Ty.mem_freeVars_substFvars_image.mpr ⟨k, hk, hv⟩
      have heq := Subst.onTy_congr hagPrefix (hFopen original ho)
      rw [Subst.onTy_append] at heq
      rw [← heq] at himage
      exact hXsoft x hx (TyList.mem_freeVars_iff.mpr ⟨ambient.onTy original,
        List.mem_map.mpr ⟨original, ho, rfl⟩, himage⟩)
  have hYX : ∀ y ∈ Ys, y ∈ Xs := by
    intro y hy
    rw [← hXtake] at hy
    exact List.mem_of_mem_take hy
  have hescape : ∀ y ∈ Ys, y ∉ (sCheck.onCtx (s1.onCtx ctx)).env.freeVars ++
      softVars (substSoft (s1 ++ sCheck) F) := by
    intro y hy hc
    have hfixy := hVP y (List.mem_append_right _ hy)
    rcases List.mem_append.mp hc with hc | hc
    · obtain ⟨scheme, hm, hyM⟩ := Env.mem_freeVars_iff.mp hc
      have himage : y ∈ (V.onPolyTy scheme).body.freeVars :=
        Ty.mem_freeVars_substFvars_image.mpr ⟨y, hyM, by change y ∈ (V.onTy (.fvar y)).freeVars; rw [hfixy]; exact List.mem_cons_self⟩
      apply hXctx y (hYX y hy)
      rw [← hctxBridge]
      exact Env.mem_freeVars_iff.mpr ⟨V.onPolyTy scheme, List.mem_map.mpr ⟨scheme, hm, rfl⟩, himage⟩
    · exact hVimages y (hYX y hy) y (List.mem_append_right _ hc) (by rw [hfixy]; exact List.mem_cons_self)

  have hpostScope := hscope.subst (s1 ++ sCheck) hprefixFix
  have hannSource : ∀ v ∈ ((ann.substTyFvars s1).substTyFvars sCheck).rigidVars,
      v ∈ K ++ softVars (substSoft (s1 ++ sCheck) F) := by
    intro v hv
    rw [← LetAnn.substTyFvars_append] at hv
    exact hpostScope v (List.mem_append_left _ (List.mem_append_left _ hv))
  have havoidQ : ∀ y ∈ Ys, y ∉ K ++ softVars (substSoft (s1 ++ sCheck) F) := by
    intro y hy hc
    exact (List.mem_append.mp hc).elim (hYavoid y hy)
      (fun hc => hescape y hy (List.mem_append_right _ hc))
  have hcheckedLC := Subst.onTy_lc hsCheckLC hrLC
  have hgen := hc.scheme_generalizes (ctx := sCheck.onCtx (s1.onCtx ctx)) hYlen' hYnd hrLC
    hannSource havoidQ hV hM hXnd hXlen hXM hcheckedTy
    (by simpa only [hctxBridge] using hXctx) hVimages
  rw [← LetAnn.substTyFvars_append] at hgen
  have hbodyWeak := Typing.weaken_schemes (env := (ambient.onCtx ctx).env) (.cons hgen .nil) hbD
  have hbodySource : body.substTyFvars ambient =
      (body.substTyFvars (s1 ++ sCheck)).substTyFvars V := by
    rw [← Input.substTyFvars_append]
    exact body.substTyFvars_congr (fun v hv => hagPrefix v (by
      have := hscopeBound v (hscope v (List.mem_append_right _ hv)); omega))
  rw [hbodySource] at hbodyWeak
  have hbodyD : Typing P (V.onCtx
      { (sCheck.onCtx (s1.onCtx ctx)) with
        env := signatureScheme (ann.substTyFvars (s1 ++ sCheck))
          (K ++ softVars (substSoft (s1 ++ sCheck) F)) Ys
          (sCheck.onCtx (s1.onCtx ctx)) (sCheck.onTy rhsTy) ::
          (sCheck.onCtx (s1.onCtx ctx)).env }) ((body.substTyFvars (s1 ++ sCheck)).substTyFvars V) target := by
    rw [← hctxBridge] at hbodyWeak
    exact hbodyWeak
  have hcheckedWF := Subst.onCtx_wf hsCheckLC (Subst.onCtx_wf hs1LC hwf)
  have hcheckedB := Subst.onCtx_below hsCheckB hcle
    (Subst.onCtx_below hs1B (by omega) hbelow)
  have hcheckedTyB := Subst.onTy_belowFvars hsCheckB (hrB.mono hcle)
  have hpostAnnBound : ∀ v ∈ ((ann.substTyFvars s1).substTyFvars sCheck).rigidVars, v < checked := by
    intro v hv
    obtain ⟨k, hk, himage⟩ := (ann.substTyFvars s1).rigidVars_substTyFvars hv
    exact (Subst.onTy_belowFvars hsCheckB (Ty.BelowFvars.fvar (Nat.lt_of_lt_of_le (hannBound k hk) hcle))).mem_lt v himage
  have hbodyWF : CtxWF { (sCheck.onCtx (s1.onCtx ctx)) with
      env := signatureScheme (ann.substTyFvars (s1 ++ sCheck))
        (K ++ softVars (substSoft (s1 ++ sCheck) F)) Ys
        (sCheck.onCtx (s1.onCtx ctx)) (sCheck.onTy rhsTy) ::
        (sCheck.onCtx (s1.onCtx ctx)).env } := by
    intro scheme hs
    rcases List.mem_cons.mp hs with rfl | hs
    · simpa only [← LetAnn.substTyFvars_append] using hc.scheme_wf (Q := K ++ softVars (substSoft (s1 ++ sCheck) F))
        (ctx := sCheck.onCtx (s1.onCtx ctx)) hYlen' hrLC
    · exact hcheckedWF scheme hs
  have hbodyB : CtxBelow checked { (sCheck.onCtx (s1.onCtx ctx)) with
      env := signatureScheme (ann.substTyFvars (s1 ++ sCheck))
        (K ++ softVars (substSoft (s1 ++ sCheck) F)) Ys
        (sCheck.onCtx (s1.onCtx ctx)) (sCheck.onTy rhsTy) ::
        (sCheck.onCtx (s1.onCtx ctx)).env } := by
    intro scheme hs
    rcases List.mem_cons.mp hs with rfl | hs
    · simpa only [← LetAnn.substTyFvars_append] using hc.scheme_belowFvars
        (Q := K ++ softVars (substSoft (s1 ++ sCheck) F)) (ctx := sCheck.onCtx (s1.onCtx ctx)) hcheckedTyB hpostAnnBound
    · exact hcheckedB scheme hs
  exact ⟨V, hV, hVP, hagPrefix, hbodyD, hbodyWF, hbodyB, hprefixB, hescape⟩

theorem Typing.align_partial_prefix_with_fits {P : List Nat} {ctx : Ctx} {rhs : Input}
    {scheme : PolyTy} {ann : LetAnn} {count : Nat} {L Ys : List Nat}
    (hcount : count = ann.paramCount)
    (hFits : ∀ Xs, FreshNames L scheme.paramCount Xs → ann.SignatureFits scheme Xs)
    (hAnn : ∀ v ∈ ann.rigidVars, v ∈ P)
    (hcofinite : ∀ Xs, FreshNames L scheme.paramCount Xs →
      Typing (P ++ Xs.take count) ctx (rhs.openTyVars (Xs.take count)) (scheme.openVars Xs))
    (hle : count ≤ scheme.paramCount) (hsource : ∀ v ∈ rhs.rigidVars, v ∈ P)
    (hYsLen : Ys.length = count) (hYsNodup : Ys.Nodup)
    (hYsP : ∀ y ∈ Ys, y ∉ P) (hYsCtx : ∀ y ∈ Ys, y ∉ ctx.env.freeVars)
    (hYsScheme : ∀ y ∈ Ys, y ∉ scheme.body.freeVars) (avoid : List Nat) :
    ∃ extras : List Nat,
      extras.length = scheme.paramCount - count ∧ (Ys ++ extras).Nodup ∧
      (∀ z ∈ extras, z ∉ avoid ++ P ++ Ys ++ ctx.env.freeVars ++ scheme.body.freeVars ++ rhs.rigidVars) ∧
      (∀ z ∈ Ys ++ extras, z ∉ P ∧ z ∉ ctx.env.freeVars ∧ z ∉ scheme.body.freeVars) ∧
      Typing (P ++ Ys) ctx (rhs.openTyVars Ys) (scheme.openVars (Ys ++ extras)) ∧
      ann.SignatureFits scheme (Ys ++ extras) := by
  obtain ⟨extras, hELen, hENodup, hEAvoid⟩ := exists_fresh_names
    (avoid ++ P ++ Ys ++ ctx.env.freeVars ++ scheme.body.freeVars ++ rhs.rigidVars)
    (scheme.paramCount - count)
  have hVsLen : (Ys ++ extras).length = scheme.paramCount := by
    simp only [List.length_append, hYsLen, hELen]; omega
  have hVsNodup : (Ys ++ extras).Nodup := by
    refine List.nodup_append.mpr ⟨hYsNodup, hENodup, ?_⟩
    intro y hy z hz heq
    subst z
    apply hEAvoid y hz
    simp only [List.mem_append]
    tauto
  obtain ⟨Ns, hNLen, hNNodup, hNAvoid⟩ := exists_fresh_names
    (L ++ P ++ (Ys ++ extras) ++ ctx.env.freeVars ++ scheme.body.freeVars ++ rhs.rigidVars)
    scheme.paramCount
  have hNfresh : FreshNames L scheme.paramCount Ns :=
    ⟨hNLen, hNNodup, fun x hx hl => hNAvoid x hx (by simp only [List.mem_append]; tauto)⟩
  have hNP : ∀ x ∈ Ns, x ∉ P := fun x hx hp => hNAvoid x hx (by simp only [List.mem_append]; tauto)
  have hNCtx : ∀ x ∈ Ns, x ∉ ctx.env.freeVars := fun x hx hc => hNAvoid x hx (by simp only [List.mem_append]; tauto)
  have hNScheme : ∀ x ∈ Ns, x ∉ scheme.body.freeVars := fun x hx hm => hNAvoid x hx (by simp only [List.mem_append]; tauto)
  have hNVs : ∀ x ∈ Ns, x ∉ Ys ++ extras := fun x hx hv => hNAvoid x hx (by simp only [List.mem_append] at hv ⊢; tauto)
  have hNtake : (Ns.take count).length = Ys.length := by
    rw [List.length_take, hNLen, hYsLen]; omega
  have hNSplit : (Ns.take count ++ Ns.drop count).Nodup := by simpa only [List.take_append_drop] using hNNodup
  have hNtakeY : ∀ name ∈ Ns.take count, name ∉ Ys := fun name hn hy =>
    hNVs name (List.mem_of_mem_take hn) (List.mem_append_left _ hy)
  let RY : Subst := (Ns.take count).zip (Ys.map Ty.fvar)
  let RG : Subst := (Ns.drop count).zip (extras.map Ty.fvar)
  have hRYlc : ∀ p ∈ RY, p.2.IsLC := by
    intro p hp
    obtain ⟨_, _, heq⟩ := List.mem_map.mp (List.of_mem_zip hp).2
    rw [← heq]; exact .fvar
  have hRGlc : ∀ p ∈ RG, p.2.IsLC := by
    intro p hp
    obtain ⟨_, _, heq⟩ := List.mem_map.mp (List.of_mem_zip hp).2
    rw [← heq]; exact .fvar
  have hRYK : ∀ k ∈ P, RY.onTy (.fvar k) = .fvar k := by
    intro k hk
    apply Ty.substFvars_eq_self_of_no_key
    intro p hp hc
    have heq : p.1 = k := List.mem_singleton.mp hc
    exact hNP p.1 (List.mem_of_mem_take (List.of_mem_zip hp).1) (heq ▸ hk)
  have hRYscope : ∀ k ∈ P ++ Ns.take count, ∀ v ∈ (RY.onTy (.fvar k)).freeVars, v ∈ P ++ Ys := by
    intro k hk v hv
    rcases List.mem_append.mp hk with hk | hk
    · rw [hRYK k hk] at hv
      exact List.mem_append_left _ ((List.mem_singleton.mp hv) ▸ hk)
    · obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hk
      have hilt : i < (Ns.take count).length := (List.getElem?_eq_some_iff.mp hi).choose
      have hit : i < Ys.length := by omega
      have himg : RY.onTy (.fvar k) = .fvar Ys[i] := by
        apply Ty.substFvars_zip_fvar_eq' hNSplit.of_append_left hi
        · simp only [List.getElem?_map, List.getElem?_eq_getElem hit, Option.map_some]
        · intro y hy hc
          simp only [Ty.freeVars, List.mem_singleton] at hc
          apply hNtakeY y hy
          rw [hc]
          exact List.getElem_mem hit
      rw [himg] at hv
      exact List.mem_append_right _ ((List.mem_singleton.mp hv) ▸ List.getElem_mem hit)
  have ctxFixed : ∀ S : Subst, (∀ p ∈ S, p.1 ∈ Ns) → S.onCtx ctx = ctx := by
    intro S hS
    have henv := Subst.onEnv_eq_self_of_fresh (fun p hp => hNCtx p.1 (hS p hp))
    cases ctx
    simp only [Subst.onCtx, henv]
  have hRYctx : RY.onCtx ctx = ctx := ctxFixed RY
    (fun p hp => List.mem_of_mem_take (List.of_mem_zip hp).1)
  have hRGctx : RG.onCtx ctx = ctx := ctxFixed RG
    (fun p hp => List.mem_of_mem_drop (List.of_mem_zip hp).1)
  have hRYsource : (rhs.openTyVars (Ns.take count)).substTyFvars RY = rhs.openTyVars Ys := by
    exact rhs.substTyFvars_zip_openTyVars hNtake hNSplit.of_append_left
      (fun y hy hv => hNP y (List.mem_of_mem_take hy) (hsource y hv)) hNtakeY
  have hfirst := (hcofinite Ns hNfresh).onSubst_source RY hRYlc hRYscope
  rw [hRYctx, hRYsource] at hfirst
  have hRGavoid : ∀ p ∈ RG, p.1 ∉ P ++ Ys := by
    intro p hp hc
    have hpN := List.mem_of_mem_drop (List.of_mem_zip hp).1
    rcases List.mem_append.mp hc with hk | hy
    · exact hNP p.1 hpN hk
    · exact hNVs p.1 hpN (List.mem_append_left _ hy)
  have hsecond := hfirst.onSubst RG hRGlc hRGavoid
  rw [hRGctx] at hsecond
  have hzip : Ns.zip ((Ys ++ extras).map Ty.fvar) = RY ++ RG := by
    conv_lhs => rw [← List.take_append_drop count Ns, List.map_append]
    exact List.zip_append (by simpa only [List.length_map] using hNtake)
  have htype : (RY ++ RG).onTy (scheme.openVars Ns) = scheme.openVars (Ys ++ extras) := by
    rw [← hzip]
    have h := Ty.substFvars_zip_openVarsFrom (d := 0) (t := scheme.body)
      (hNLen.trans hVsLen.symm) hNNodup hNScheme hNVs
    simpa only [Subst.onTy, PolyTy.openVars, Ty.openVarsFrom, Ty.openVars,
      Nat.not_lt_zero, ↓reduceIte, Nat.sub_zero] using h
  have hpaired : ann.SignatureFits scheme (Ys ++ extras) := by
    have hfit := hFits Ns hNfresh
    cases hfit with
    | complete => exact .complete
    | @partialSignature scheme template declaredCount names hdeclLe hfitNs =>
      have hsame : count = declaredCount := hcount
      subst declaredCount
      change ∀ v ∈ template.rigidVars, v ∈ P at hAnn
      have hRYTemplate : (template.openTyVarsFrom 0 (Ns.take count)).substTyFvars RY =
          template.openTyVarsFrom 0 Ys :=
        template.substTyFvars_zip_openTyVarsFrom hNtake hNSplit.of_append_left
          (fun y hy hv => hNP y (List.mem_of_mem_take hy) (hAnn y hv)) hNtakeY 0
      have hfirstFit := hfitNs.substTyFvars RY
      rw [hRYTemplate] at hfirstFit
      have hRGTemplate : (template.openTyVarsFrom 0 Ys).substTyFvars RG =
          template.openTyVarsFrom 0 Ys := by
        rw [template.substTyFvars_openTyVarsFrom hRGlc
          (fun p hp hy => hRGavoid p hp (List.mem_append_right _ hy)) 0]
        rw [template.substTyFvars_eq_self_of_fixes (fun v hv =>
          Subst.fixes_of_dom_avoids hRGavoid v (List.mem_append_left _ (hAnn v hv)))]
      have hsecondFit := hfirstFit.substTyFvars RG
      rw [hRGTemplate] at hsecondFit
      refine .partialSignature hdeclLe ?_
      have htakeVs : (Ys ++ extras).take count = Ys := by
        rw [← hYsLen]
        simp
      rw [htakeVs, ← htype, Subst.onTy_append]
      exact hsecondFit
  refine ⟨extras, hELen, hVsNodup, hEAvoid, ?_, ?_, hpaired⟩
  · intro z hz
    rcases List.mem_append.mp hz with hz | hz
    · exact ⟨hYsP z hz, hYsCtx z hz, hYsScheme z hz⟩
    · refine ⟨?_, ?_, ?_⟩ <;> intro hc <;> apply hEAvoid z hz <;>
        simp only [List.mem_append] <;> tauto
  · rw [← htype, Subst.onTy_append]
    exact hsecond

/-- Shared signed continuation frame for an internally dodged candidate. The
cofinite template and RHS premises use one aligned opening and one extra block. -/
theorem _root_.Infer.source_signature_frame {rhs body : Input} {ann : LetAnn}
    (hscope : SourceScope K F (.letIn ann rhs body))
    (hr : Infer (K ++ Ys) F (frontier + ann.paramCount) ctx (rhs.openTyVars Ys) first s1 rhsOut rhsTy)
    (hc : SignatureCheck K (substSoft s1 F) Ys first rhsTy (ann.substTyFvars s1) checked sCheck)
    (ihr : Infer.SourcePrincipal hr)
    (hprefix : Ys = freshVars frontier ann.paramCount)
    (hwf : CtxWF ctx) (hbelow : CtxBelow frontier ctx) (hK : ∀ k ∈ K, k < frontier)
    (hF : ∀ t ∈ F, Ty.BelowFvars frontier t)
    {ambient : Subst} {P : List Nat} {M : PolyTy} {L : List Nat} {target : Ty}
    (hS : ∀ pair ∈ ambient, pair.2.IsLC) (hP : ∀ p ∈ P, p < frontier)
    (hfix : ∀ p ∈ P ++ Ys, ambient.onTy (.fvar p) = .fvar p)
    (hfreeze : ∀ v ∈ (Input.letIn ann rhs body).rigidVars,
      v ∈ K → v ∉ softVars F → ambient.onTy (.fvar v) = .fvar v)
    (hM : M.WF) (hannRigid : ∀ v ∈ (ann.substTyFvars ambient).rigidVars, v ∈ P)
    (hrhsRigid : ∀ v ∈ (rhs.substTyFvars ambient).rigidVars, v ∈ P)
    (hannFits : ∀ Xs, FreshNames L M.paramCount Xs → (ann.substTyFvars ambient).SignatureFits M Xs)
    (hrD : ∀ Xs, FreshNames L M.paramCount Xs →
      Typing (P ++ Xs.take ann.paramCount) (ambient.onCtx ctx)
        ((rhs.substTyFvars ambient).openTyVars (Xs.take ann.paramCount)) (M.openVars Xs))
    (hbD : Typing P { ambient.onCtx ctx with env := M :: (ambient.onCtx ctx).env }
      (body.substTyFvars ambient) target)
    (hYsM : ∀ y ∈ Ys, y ∉ M.body.freeVars)
    (hYsCtx : ∀ y ∈ Ys, y ∉ (ambient.onCtx ctx).env.freeVars)
    (hYsImages : ∀ y ∈ Ys, ∀ k ∈ K, y ∉ (ambient.onTy (.fvar k)).freeVars)
    (hYsSoft : ∀ y ∈ Ys, y ∉ softVars (substSoft ambient F)) :
    let checkedCtx := sCheck.onCtx (s1.onCtx ctx)
    let soft := substSoft (s1 ++ sCheck) F
    let scheme := signatureScheme (ann.substTyFvars (s1 ++ sCheck)) (K ++ softVars soft) Ys checkedCtx (sCheck.onTy rhsTy)
    ∃ V : Subst, (∀ pair ∈ V, pair.2.IsLC) ∧
      (∀ p ∈ P ++ Ys, V.onTy (.fvar p) = .fvar p) ∧
      Subst.AgreesBelow (frontier + ann.paramCount) ambient ((s1 ++ sCheck) ++ V) ∧
      Typing P (V.onCtx { checkedCtx with env := scheme :: checkedCtx.env })
        ((body.substTyFvars (s1 ++ sCheck)).substTyFvars V) target ∧
      CtxWF { checkedCtx with env := scheme :: checkedCtx.env } ∧
      CtxBelow checked { checkedCtx with env := scheme :: checkedCtx.env } ∧
      (∀ pair ∈ s1 ++ sCheck, Ty.BelowFvars checked pair.2) ∧
      (∀ y ∈ Ys, y ∉ checkedCtx.env.freeVars ++ softVars soft) := by
  have hYlen : Ys.length = ann.paramCount := by rw [hprefix, freshVars_length]
  have hYnd : Ys.Nodup := hprefix ▸ freshVars_nodup
  have hYsP : ∀ y ∈ Ys, y ∉ P := by
    intro y hy hp
    have hge := freshVars_ge y (hprefix ▸ hy)
    have hlt := hP y hp
    omega
  obtain ⟨Ns, hNlen, hNnd, hNavoid⟩ := exists_fresh_names L M.paramCount
  have hle := (hannFits Ns ⟨hNlen, hNnd, hNavoid⟩).prefix_le
  simp only [LetAnn.paramCount_substTyFvars] at hle
  let images := K.flatMap (fun k => (ambient.onTy (.fvar k)).freeVars) ++ softVars (substSoft ambient F)
  obtain ⟨extras, hElen, hXsNd, hExtra, hAll, hAligned, hAlignedFits⟩ :=
    Typing.align_partial_prefix_with_fits (by simp) hannFits hannRigid hrD hle hrhsRigid
      hYlen hYnd hYsP hYsCtx hYsM images
  have hXsLen : (Ys ++ extras).length = M.paramCount := by
    simp only [List.length_append, hYlen, hElen]; omega
  have hXsTake : (Ys ++ extras).take ann.paramCount = Ys := by rw [← hYlen]; simp
  have hXImages : ∀ x ∈ Ys ++ extras, ∀ k ∈ K, x ∉ (ambient.onTy (.fvar k)).freeVars := by
    intro x hx k hk hv
    rcases List.mem_append.mp hx with hy | he
    · exact hYsImages x hy k hk hv
    · apply hExtra x he
      have himages : x ∈ images := List.mem_append_left _ (List.mem_flatMap.mpr ⟨k, hk, hv⟩)
      simp only [List.mem_append]
      tauto
  have hXSoft : ∀ x ∈ Ys ++ extras, x ∉ softVars (substSoft ambient F) := by
    intro x hx hv
    rcases List.mem_append.mp hx with hy | he
    · exact hYsSoft x hy hv
    · apply hExtra x he
      have himages : x ∈ images := List.mem_append_right _ hv
      simp only [List.mem_append]
      tauto
  exact Infer.source_signature_frame_aligned hscope hr hc ihr hprefix hwf hbelow hK hF hS hP hfix hfreeze hM hannRigid
    hXsLen hXsNd hXsTake hAlignedFits hAligned hbD
    (fun x hx => (hAll x hx).2.2) (fun x hx => (hAll x hx).2.1) hXImages hXSoft

/-- Dodge candidate collisions while retaining the source-transformed signed
contract. Authored candidate leaves lie in P and hence are fixed by the move. -/
theorem Typing.signature_dodge_source
    {K P : List Nat} {F : List Ty} {ambient : Subst} {ctx : Ctx} {ann : LetAnn}
    {rhs body : Input} {target : Ty} {frontier : Nat}
    (ht : Typing P (ambient.onCtx ctx) ((Input.letIn ann rhs body).substTyFvars ambient) target)
    (hmode : ann.isSignature = true) (hscope : SourceScope K F (.letIn ann rhs body))
    (hbelow : CtxBelow frontier ctx) (hP : ∀ p ∈ P, p < frontier)
    (hK : ∀ k ∈ K, k < frontier) (hF : ∀ t ∈ F, Ty.BelowFvars frontier t)
    (hS : ∀ pair ∈ ambient, pair.2.IsLC)
    (hfix : ∀ p ∈ P, ambient.onTy (.fvar p) = .fvar p)
    (hfreeze : ∀ v ∈ (.letIn ann rhs body : Input).rigidVars,
      v ∈ K → v ∉ softVars F → ambient.onTy (.fvar v) = .fvar v) :
    ∃ (W : Nat) (M : PolyTy) (L : List Nat),
      let written := freshVars frontier ann.paramCount
      let forward := blockList frontier W ann.paramCount
      let backward := blockListBack frontier W ann.paramCount
      let moved := Subst.conj (blockSwap frontier W ann.paramCount) ambient
      (∀ pair ∈ moved, pair.2.IsLC) ∧
      (∀ p ∈ P ++ written, moved.onTy (.fvar p) = .fvar p) ∧
      (∀ v, v < frontier → backward.onTy (moved.onTy (.fvar v)) = ambient.onTy (.fvar v)) ∧
      (∀ pair ∈ backward, pair.2.IsLC) ∧
      (∀ p ∈ P, backward.onTy (.fvar p) = .fvar p) ∧
      backward.onTy (forward.onTy target) = target ∧
      (∀ v ∈ (.letIn ann rhs body : Input).rigidVars,
        v ∈ K → v ∉ softVars F → moved.onTy (.fvar v) = .fvar v) ∧
      M.WF ∧ (∀ v ∈ (ann.substTyFvars moved).rigidVars, v ∈ P) ∧
      (∀ v ∈ (rhs.substTyFvars moved).rigidVars, v ∈ P) ∧
      (∀ Xs, FreshNames L M.paramCount Xs → (ann.substTyFvars moved).SignatureFits M Xs) ∧
      (∀ Xs, FreshNames L M.paramCount Xs →
        Typing (P ++ Xs.take ann.paramCount) (moved.onCtx ctx)
          ((rhs.substTyFvars moved).openTyVars (Xs.take ann.paramCount)) (M.openVars Xs)) ∧
      Typing P { moved.onCtx ctx with env := M :: (moved.onCtx ctx).env }
        (body.substTyFvars moved) (forward.onTy target) ∧
      (∀ y ∈ written, y ∉ M.body.freeVars) ∧
      (∀ y ∈ written, y ∉ (moved.onCtx ctx).env.freeVars) ∧
      (∀ y ∈ written, y ∉ softVars (substSoft moved F)) ∧
      (∀ y ∈ written, ∀ k ∈ K, y ∉ (moved.onTy (.fvar k)).freeVars) := by
  have hmode' : (ann.substTyFvars ambient).isSignature = true := by
    cases ann <;> exact hmode
  obtain ⟨M, L, hM, hann, hrhs, hfit, htyped, hbody⟩ := ht.signature_inv hmode'
  let scopeVars := K ++ softVars F
  let images := scopeVars.map (fun k => ambient.onTy (.fvar k))
  let contextTypes := (ambient.onCtx ctx).env.map PolyTy.body
  let targets := M.body :: target :: (contextTypes ++ images)
  obtain ⟨W, hW, _, hMoved, hWritten, hBelow, hForward, hBackward, hTargets⟩ :=
    signed_candidate_dodge ambient hS frontier ann.paramCount targets []
  let forward := blockList frontier W ann.paramCount
  let backward := blockListBack frontier W ann.paramCount
  let moved := Subst.conj (blockSwap frontier W ann.paramCount) ambient
  have hforwardLC := blockList_lc frontier W ann.paramCount
  have hForwardP : ∀ p ∈ P, forward.onTy (.fvar p) = .fvar p :=
    fun p hp => (hBelow p (hP p hp)).1
  have hMovedP : ∀ p ∈ P, moved.onTy (.fvar p) = .fvar p := by
    intro p hp
    rw [hForward (.fvar _) (.fvar (hP p hp)), hfix p hp]
    exact hForwardP p hp
  have hdomP : ∀ pair ∈ forward, pair.1 ∉ P := by
    intro pair hp hmem
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hp
    have := hP _ hmem
    omega
  have hag : Subst.AgreesBelow frontier (ambient ++ forward) moved := by
    intro v hv
    simpa only [Subst.onTy_append] using (hForward (.fvar v) (.fvar hv)).symm
  have hctxeq : forward.onCtx (ambient.onCtx ctx) = moved.onCtx ctx := by
    rw [← Subst.onCtx_append]
    exact Subst.onCtx_congr hag hbelow
  have hsourceeq : (.letIn ann rhs body : Input).substTyFvars moved =
      (.letIn ann rhs body : Input).substTyFvars ambient := by
    trans ((.letIn ann rhs body : Input).substTyFvars ambient).substTyFvars forward
    · rw [← Input.substTyFvars_append]
      apply Input.substTyFvars_congr
      intro v hv
      change moved.onTy (.fvar v) = (ambient ++ forward).onTy (.fvar v)
      rw [Subst.onTy_append]
      exact hForward (.fvar v) (.fvar ((List.mem_append.mp (hscope v hv)).elim (hK v) (softVars_lt hF v)))
    · exact Input.substTyFvars_eq_self_of_fixes _ (fun v hv => hForwardP v (ht.rigidVars v hv))
  change Input.letIn (ann.substTyFvars moved) (rhs.substTyFvars moved) (body.substTyFvars moved) =
    Input.letIn (ann.substTyFvars ambient) (rhs.substTyFvars ambient) (body.substTyFvars ambient) at hsourceeq
  obtain ⟨hannEq, hrhsEq, hbodyEq⟩ := Input.letIn.inj hsourceeq
  obtain ⟨L', hfits', htypes'⟩ := Typing.signatureBinding_onSubst hfit htyped hann
    forward hforwardLC hdomP
  have hbody' := hbody.onSubst_fixes forward hforwardLC hForwardP
  have hbodyctx : forward.onCtx { ambient.onCtx ctx with env := M :: (ambient.onCtx ctx).env } =
      { moved.onCtx ctx with env := forward.onPolyTy M :: (moved.onCtx ctx).env } := by
    change { forward.onCtx (ambient.onCtx ctx) with
      env := forward.onPolyTy M :: (forward.onCtx (ambient.onCtx ctx)).env } = _
    rw [hctxeq]
  rw [hbodyctx, ← hbodyEq] at hbody'
  have htargetM := hTargets M.body (by simp only [targets, List.mem_cons]; tauto)
  have htargetResult := hTargets target (by simp only [targets, List.mem_cons]; tauto)
  have hprotected : ∀ k ∈ scopeVars, k < frontier :=
    fun k hk => (List.mem_append.mp hk).elim (hK k) (softVars_lt hF k)
  have hImages : ∀ y ∈ freshVars frontier ann.paramCount, ∀ k ∈ scopeVars,
      y ∉ (moved.onTy (.fvar k)).freeVars := by
    intro y hy k hk hv
    rw [hForward (.fvar _) (.fvar (hprotected k hk))] at hv
    exact (hTargets (ambient.onTy (.fvar k)) (by
      simp only [targets, List.mem_cons, List.mem_append]
      right; right; right
      exact List.mem_map.mpr ⟨k, hk, rfl⟩)).2 y hy hv
  refine ⟨W, forward.onPolyTy M, L', hMoved, ?_, (fun v hv => hBackward (.fvar v) (.fvar hv)),
    blockListBack_lc _ _ _, ?_, htargetResult.1, ?_, Subst.onPolyTy_wf hforwardLC hM,
    ?_, ?_, ?_, ?_, hbody', htargetM.2, ?_, ?_, ?_⟩
  · intro p hp
    exact (List.mem_append.mp hp).elim (hMovedP p) (hWritten p)
  · intro p hp
    exact (hBelow p (hP p hp)).2
  · intro v hv hk hnot
    rw [hForward (.fvar v) (.fvar (hK v hk)), hfreeze v hv hk hnot]
    exact (hBelow v (hK v hk)).1
  · rwa [hannEq]
  · rwa [hrhsEq]
  · intro Xs hf
    have h := hfits' Xs hf
    rw [← hannEq] at h
    exact h
  · intro Xs hf
    rw [hrhsEq]
    simpa only [LetAnn.paramCount_substTyFvars, hctxeq] using htypes' Xs hf
  · intro y hy hmem
    rw [← hctxeq] at hmem
    obtain ⟨scheme, hs, hv⟩ := Env.mem_freeVars_iff.mp hmem
    obtain ⟨old, ho, rfl⟩ := List.mem_map.mp hs
    exact (hTargets old.body (by
      simp only [targets, List.mem_cons, List.mem_append]
      right; right; left
      exact List.mem_map.mpr ⟨old, ho, rfl⟩)).2 y hy hv
  · intro y hy hv
    obtain ⟨k, hk, hv⟩ := mem_softVars_substSoft.mp hv
    exact hImages y hy k (List.mem_append_right _ hk) hv
  · intro y hy k hk
    exact hImages y hy k (List.mem_append_left _ hk)

/-- Reconcile a checked ordinary RHS with a declarative let scheme, then
transport its continuation. Shared by both completeness directions. -/
theorem _root_.Infer.source_let_frame
    (hscope : SourceScope K F (.letIn ann rhs body))
    (hr : Infer K F frontier ctx rhs first s1 rhsOut rhsTy)
    (hc : LetCheck K (substSoft s1 F) first rhsTy (ann.substTyFvars s1) checked sCheck)
    (ihr : Infer.SourcePrincipal hr) :
    CtxWF ctx → CtxBelow frontier ctx → (∀ k ∈ K, k < frontier) →
    (∀ t ∈ F, Ty.BelowFvars frontier t) →
    ∀ (ambient : Subst) (target : Ty) (P : List Nat),
      (∀ pair ∈ ambient, pair.2.IsLC) → (∀ p ∈ P, p < frontier) →
      (∀ p ∈ P, ambient.onTy (.fvar p) = .fvar p) →
      (∀ v ∈ (Input.letIn ann rhs body).rigidVars, v ∈ K → v ∉ softVars F → ambient.onTy (.fvar v) = .fvar v) →
      Typing P (ambient.onCtx ctx) ((Input.letIn ann rhs body).substTyFvars ambient) target →
      ∃ V : Subst, (∀ pair ∈ V, pair.2.IsLC) ∧
        (∀ p ∈ P, V.onTy (.fvar p) = .fvar p) ∧
        Subst.AgreesBelow frontier ambient (s1 ++ sCheck ++ V) ∧
        Typing P (V.onCtx { (sCheck.onCtx (s1.onCtx ctx)) with
        env := genScheme (K ++ softVars (substSoft (s1 ++ sCheck) F)) (sCheck.onCtx (s1.onCtx ctx)).env (sCheck.onTy rhsTy) ::
          (sCheck.onCtx (s1.onCtx ctx)).env }) ((body.substTyFvars (s1 ++ sCheck)).substTyFvars V) target ∧
        CtxWF { (sCheck.onCtx (s1.onCtx ctx)) with
        env := genScheme (K ++ softVars (substSoft (s1 ++ sCheck) F)) (sCheck.onCtx (s1.onCtx ctx)).env (sCheck.onTy rhsTy) ::
          (sCheck.onCtx (s1.onCtx ctx)).env } ∧ CtxBelow checked { (sCheck.onCtx (s1.onCtx ctx)) with
        env := genScheme (K ++ softVars (substSoft (s1 ++ sCheck) F)) (sCheck.onCtx (s1.onCtx ctx)).env (sCheck.onTy rhsTy) ::
          (sCheck.onCtx (s1.onCtx ctx)).env } ∧
        (∀ pair ∈ s1 ++ sCheck, Ty.BelowFvars checked pair.2) := by
  intro hwf hbelow hK hF ambient target P hS hP hfix hfreeze htyping
  have hscopeBound : ∀ v ∈ K ++ softVars F, v < frontier :=
    fun v hv => (List.mem_append.mp hv).elim (hK v) (softVars_lt hF v)
  have hmode : ann.isSignature = false := by simpa only [LetAnn.isSignature_substTyFvars] using hc.not_signature
  obtain ⟨M, L, hM, hannRigid, hannFits, hrD, hbD⟩ := htyping.letMono_inv (by simpa using hmode)
  let images := K.flatMap (fun k => (ambient.onTy (.fvar k)).freeVars) ++ softVars (substSoft ambient F)
  obtain ⟨Xs, hXlen, hXnd, hXavoid⟩ := exists_fresh_names
    (L ++ M.body.freeVars ++ (ambient.onCtx ctx).env.freeVars ++ images) M.paramCount
  have hXfresh : FreshNames L M.paramCount Xs := ⟨hXlen, hXnd, by
    intro x hx hc; exact hXavoid x hx (by simp only [List.mem_append]; tauto)⟩
  have hXM : ∀ x ∈ Xs, x ∉ M.body.freeVars := by
    intro x hx hc; exact hXavoid x hx (by simp only [List.mem_append]; tauto)
  have hXctx : ∀ x ∈ Xs, x ∉ (ambient.onCtx ctx).env.freeVars := by
    intro x hx hc; exact hXavoid x hx (by simp only [List.mem_append]; tauto)
  have hXimages : ∀ x ∈ Xs, ∀ k ∈ K, x ∉ (ambient.onTy (.fvar k)).freeVars := by
    intro x hx k hk hc
    exact hXavoid x hx (by
      simp only [List.mem_append]; right
      exact List.mem_append_left _ (List.mem_flatMap.mpr ⟨k, hk, hc⟩))
  obtain ⟨R, hR, hrTy, hRP, hagR⟩ := ihr hwf hbelow hK hF ambient
    (M.openVars Xs) P hS hP hfix
    (fun v hv => hfreeze v (List.mem_append_left _ (List.mem_append_right _ hv))) (hrD Xs hXfresh)
  have hrle := hr.frontier_le
  have hcle := hc.frontier_le
  have hK1 : ∀ k ∈ K, k < first := fun k hk => Nat.lt_of_lt_of_le (hK k hk) hrle
  have hP1 : ∀ p ∈ P, p < first := fun p hp => Nat.lt_of_lt_of_le (hP p hp) hrle
  obtain ⟨hrB, hs1B⟩ := hr.belowFvars hbelow hK hF
  obtain ⟨hrLC, hs1LC⟩ := hr.lc hwf
  have hF1 := substSoft_below hs1B hrle hF
  have hannEq : (ann.substTyFvars s1).substTyFvars R = ann.substTyFvars ambient := by
    rw [← LetAnn.substTyFvars_append]
    exact ann.substTyFvars_congr (fun v hv => (hagR v
      (hscopeBound v (hscope v (List.mem_append_left _ (List.mem_append_left _ hv))))).symm)
  obtain ⟨V, hV, hcheckedTy, hVP, hagV⟩ := hc.factor_source
    (fun v hv => by
      have hs := hscope.subst s1 (Subst.fixes_of_dom_avoids hr.dom_avoids)
      have hvscope := hs v (List.mem_append_left _ (List.mem_append_left _ hv))
      exact (List.mem_append.mp hvscope).elim (hK1 v) (softVars_lt hF1 v))
    hP1 hrB hR hRP ((hrD Xs hXfresh).regular) (hannEq.symm ▸ hannFits Xs hXfresh) hrTy
  have hsCheckLC := hc.lc hrLC
  have hsCheckB := hc.belowFvars hrB hK1 hF1
  have hprefixB : ∀ pair ∈ s1 ++ sCheck, Ty.BelowFvars checked pair.2 := by
    intro pair hp
    exact (List.mem_append.mp hp).elim (fun hp => (hs1B pair hp).mono hcle) (hsCheckB pair)
  have hagPrefix := Subst.AgreesBelow.trans_append hrle hagR hs1B hagV
  have hctxBridge : V.onCtx (sCheck.onCtx (s1.onCtx ctx)) = ambient.onCtx ctx := by
    rw [← Subst.onCtx_append, ← Subst.onCtx_append]
    simpa only [List.append_assoc] using (Subst.onCtx_congr hagPrefix hbelow).symm
  have hprefixFix : ∀ k ∈ K, (s1 ++ sCheck).onTy (.fvar k) = .fvar k := by
    apply Subst.fixes_of_dom_avoids
    intro pair hp
    exact (List.mem_append.mp hp).elim (hr.dom_avoids pair) (hc.dom_avoids pair)
  have hVimages : ∀ x ∈ Xs, ∀ k ∈ K ++ softVars (substSoft (s1 ++ sCheck) F),
      x ∉ (V.onTy (.fvar k)).freeVars := by
    intro x hx k hk hv
    rcases List.mem_append.mp hk with hk | hk
    · have heq := hagPrefix k (hK k hk)
      rw [Subst.onTy_append, hprefixFix k hk] at heq
      rw [← heq] at hv
      exact hXimages x hx k hk hv
    · obtain ⟨ty, hty, hk⟩ := TyList.mem_freeVars_iff.mp hk
      obtain ⟨original, ho, rfl⟩ := List.mem_map.mp hty
      have himage : x ∈ (V.onTy ((s1 ++ sCheck).onTy original)).freeVars :=
        Ty.mem_freeVars_substFvars_image.mpr ⟨k, hk, hv⟩
      have heq := Subst.onTy_congr hagPrefix (hF original ho)
      rw [Subst.onTy_append] at heq
      rw [← heq] at himage
      exact hXavoid x hx (by
        simp only [List.mem_append, images]
        right; right
        exact TyList.mem_freeVars_iff.mpr ⟨ambient.onTy original,
          List.mem_map.mpr ⟨original, ho, rfl⟩, himage⟩)
  have hcheckedLC := Subst.onTy_lc hsCheckLC hrLC
  have hgen := genScheme_generalizes (ctx := sCheck.onCtx (s1.onCtx ctx)) hcheckedLC hV hM hXnd hXlen hXM hcheckedTy
    (by simpa only [hctxBridge] using hXctx) hVimages
  have hbodyWeak := Typing.weaken_schemes (env := (ambient.onCtx ctx).env)
    (.cons hgen .nil) hbD
  have hbodySource : body.substTyFvars ambient =
      (body.substTyFvars (s1 ++ sCheck)).substTyFvars V := by
    rw [← Input.substTyFvars_append]
    exact body.substTyFvars_congr (fun v hv => hagPrefix v
      (hscopeBound v (hscope v (List.mem_append_right _ hv))))
  rw [hbodySource] at hbodyWeak
  have hbodyD : Typing P (V.onCtx
      { (sCheck.onCtx (s1.onCtx ctx)) with
        env := genScheme (K ++ softVars (substSoft (s1 ++ sCheck) F)) (sCheck.onCtx (s1.onCtx ctx)).env (sCheck.onTy rhsTy) ::
          (sCheck.onCtx (s1.onCtx ctx)).env }) ((body.substTyFvars (s1 ++ sCheck)).substTyFvars V) target := by
    rw [← hctxBridge] at hbodyWeak
    exact hbodyWeak
  have hcheckedWF := Subst.onCtx_wf hsCheckLC (Subst.onCtx_wf hs1LC hwf)
  have hcheckedB := Subst.onCtx_below hsCheckB hcle
    (Subst.onCtx_below hs1B hrle hbelow)
  have hcheckedTyB := Subst.onTy_belowFvars hsCheckB (hrB.mono hcle)
  have hbodyWF : CtxWF { (sCheck.onCtx (s1.onCtx ctx)) with
      env := genScheme (K ++ softVars (substSoft (s1 ++ sCheck) F)) (sCheck.onCtx (s1.onCtx ctx)).env (sCheck.onTy rhsTy) ::
        (sCheck.onCtx (s1.onCtx ctx)).env } := by
    intro scheme hs
    rcases List.mem_cons.mp hs with rfl | hs
    · exact genScheme_wf hcheckedLC
    · exact hcheckedWF scheme hs
  have hbodyB : CtxBelow checked { (sCheck.onCtx (s1.onCtx ctx)) with
      env := genScheme (K ++ softVars (substSoft (s1 ++ sCheck) F)) (sCheck.onCtx (s1.onCtx ctx)).env (sCheck.onTy rhsTy) ::
        (sCheck.onCtx (s1.onCtx ctx)).env } := by
    intro scheme hs
    rcases List.mem_cons.mp hs with rfl | hs
    · exact hcheckedTyB.closeOver
    · exact hcheckedB scheme hs
  exact ⟨V, hV, hVP, hagPrefix, hbodyD, hbodyWF, hbodyB, hprefixB⟩

theorem _root_.Infer.sourcePrincipal_letIn
    (hscope : SourceScope K F (.letIn ann rhs body))
    (hr : Infer K F frontier ctx rhs first s1 rhsOut rhsTy)
    (hc : LetCheck K (substSoft s1 F) first rhsTy (ann.substTyFvars s1) checked sCheck)
    (hb : Infer K (substSoft (s1 ++ sCheck) F) checked
      { (sCheck.onCtx (s1.onCtx ctx)) with
        env := genScheme (K ++ softVars (substSoft (s1 ++ sCheck) F)) (sCheck.onCtx (s1.onCtx ctx)).env (sCheck.onTy rhsTy) ::
          (sCheck.onCtx (s1.onCtx ctx)).env }
      (body.substTyFvars (s1 ++ sCheck)) next s2 bodyOut bodyTy)
    (ihr : Infer.SourcePrincipal hr) (ihb : Infer.SourcePrincipal hb) :
    Infer.SourcePrincipal (.letIn hscope hr hc hb) := by
  intro hwf hbelow hK hF ambient target P hS hP hfix hfreeze htyping
  obtain ⟨V, hV, hVP, hagPrefix, hbodyD, hbodyWF, hbodyB, hprefixB⟩ :=
    hr.source_let_frame hscope hc ihr hwf hbelow hK hF ambient target P hS hP hfix hfreeze htyping
  have hle := hr.frontier_le.trans hc.frontier_le
  obtain ⟨R2, hR2, hresult, hR2P, hag2⟩ := ihb hbodyWF hbodyB
    (fun k hk => Nat.lt_of_lt_of_le (hK k hk) hle)
    (substSoft_below hprefixB hle hF) V target P hV
    (fun p hp => Nat.lt_of_lt_of_le (hP p hp) hle) hVP
    ((show SourceScope K F body from fun v hv => hscope v (List.mem_append_right _ hv)).residual_freeze
      (fun v hv => (List.mem_append.mp (hscope v (List.mem_append_right _ hv))).elim
        (hK v) (softVars_lt hF v))
      (Subst.fixes_of_dom_avoids (fun p hp => (List.mem_append.mp hp).elim (hr.dom_avoids p) (hc.dom_avoids p)))
      (fun v hv => hfreeze v (List.mem_append_right _ hv)) hagPrefix) hbodyD
  exact ⟨R2, hR2, hresult, hR2P,
    Subst.AgreesBelow.trans_append hle hagPrefix hprefixB hag2⟩

/-- Residual factorization for a nonempty branch thread. The independent
protected set scopes authored annotations; both common type images are explicit. -/
def _root_.InferBranches.SourcePrincipal
    (_h : InferBranches K F frontier ctx scrutTy resultTy branches next subst completed)
    (_hne : branches ≠ []) : Prop :=
  CtxWF ctx → CtxBelow frontier ctx → (∀ k ∈ K, k < frontier) →
  (∀ soft ∈ F, Ty.BelowFvars frontier soft) →
  ∀ (ambient : Subst) (scrutD resultD : Ty) (P : List Nat),
    (∀ pair ∈ ambient, pair.2.IsLC) → scrutD.IsLC → scrutTy.IsLC → resultTy.IsLC →
    Ty.BelowFvars frontier scrutTy → Ty.BelowFvars frontier resultTy →
    (∀ p ∈ P, p < frontier) →
    (∀ p ∈ P, ambient.onTy (.fvar p) = .fvar p) →
    (∀ v ∈ rigidBranchVars branches, v ∈ K → v ∉ softVars F → ambient.onTy (.fvar v) = .fvar v) →
    resultD = ambient.onTy resultTy → scrutD = ambient.onTy scrutTy →
    (∀ b ∈ branches, BranchTyping Typing P (ambient.onCtx ctx) (b.1, b.2.substTyFvars ambient) scrutD resultD) →
    ∃ residual : Subst, (∀ pair ∈ residual, pair.2.IsLC) ∧
      Subst.AgreesBelow frontier ambient (subst ++ residual) ∧
      (∀ p ∈ P, residual.onTy (.fvar p) = .fvar p) ∧
      resultD = residual.onTy (subst.onTy resultTy)

theorem BranchTyping.factor_named
    {Φ : Nat} {ctx : Ctx} {c : CtorName} {nbr : Nat} {ctor : Ctor}
    {scrutTy scruT₀ ρe : Ty} {S₀ S₀amb : Subst} {K : List Nat} {body : Input}
    (hlook : LookupList.get? ctx.ctors c = some ctor)
    (h₀ : UnifyRel scrutTy
      (.customTy ctor.tyName ((freshVars Φ ctor.paramCount).map Ty.fvar)) S₀)
    (hbelow : CtxBelow Φ ctx) (hbscrut : Ty.BelowFvars Φ scrutTy)
    (hS₀amb : ∀ pair ∈ S₀amb, pair.2.IsLC) (hscruLC : scruT₀.IsLC)
    (hKΦ : ∀ k ∈ K, k < Φ) (hKfix : ∀ k ∈ K, S₀amb.onTy (.fvar k) = .fvar k)
    (hIMGscru : scruT₀ = S₀amb.onTy scrutTy)
    (hdhead : BranchTyping Typing K (S₀amb.onCtx ctx) (.named c nbr, body) scruT₀ ρe) :
    ∃ R₀ : Subst, (∀ pair ∈ R₀, pair.2.IsLC) ∧
      (∀ k ∈ K, R₀.onTy (.fvar k) = .fvar k) ∧
      Subst.AgreesBelow Φ S₀amb (S₀ ++ R₀) ∧
      Typing K (R₀.onCtx { S₀.onCtx ctx with
        env := (ctor.contents.map (Ty.openWith
          (((freshVars Φ ctor.paramCount).map Ty.fvar).map S₀.onTy))).map PolyTy.mkTrivial ++
            (S₀.onCtx ctx).env }) body ρe := by
  cases hdhead with
  | named hspec hbodyty =>
    rename_i ctorE tyArgsE instContentsE
    let bodyCtx : Ctx := { S₀amb.onCtx ctx with
      env := instContentsE.map PolyTy.mkTrivial ++ (S₀amb.onCtx ctx).env }
    have hctxdef : bodyCtx = { S₀amb.onCtx ctx with
      env := instContentsE.map PolyTy.mkTrivial ++ (S₀amb.onCtx ctx).env } := rfl
    have hctorE : ctorE =  ctor := by
      have hl : LookupList.get? (S₀amb.onCtx ctx).ctors c = some ( ctor) := by
        simpa [Subst.onCtx] using hlook
      exact Option.some.inj (hspec.lookup.symm.trans hl)
    have htyArgs_lc : ∀ t ∈ tyArgsE, t.IsLC := by
      have hlc : (Ty.customTy ctor.tyName tyArgsE).IsLC := by
        simpa [hctorE, hspec.scrut_eq] using hscruLC
      cases hlc with | customTy h => exact h
    have hpc' : ctor.paramCount = tyArgsE.length := by
      simpa [hctorE] using hspec.arity
    have hscrutImg' : Eq (.customTy ctor.tyName tyArgsE) (S₀amb.onTy scrutTy) := by
      simpa [hctorE, hspec.scrut_eq] using hIMGscru
    have hinstsE : instContentsE = ctorE.contents.map (Ty.openWith tyArgsE) := by
      refine List.ext_getElem ?_ ?_
      · rw [List.length_map]
        exact hspec.fields.length_eq.symm
      · intro i hi _
        have hlen₂ : i < ctorE.contents.length := hspec.fields.length_eq.symm ▸ hi
        have hinst := hspec.fields.get hlen₂ hi
        rw [List.get_eq_getElem, List.get_eq_getElem] at hinst
        rw [List.getElem_map]
        have hpc'' : tyArgsE.length = ctorE.paramCount := hspec.arity.symm
        exact InstantiatesBy.eq_openWith hinst (ctorE.bound _ (List.getElem_mem hlen₂)) hpc''
    obtain ⟨R₀, hR₀, hR₀K, hAgree₀, hmap₀⟩ :=
      customTy_factor_dodge (R := S₀amb) (S₀ := S₀) (ctor := ctor) (tyArgs := tyArgsE)
        h₀ hbscrut hS₀amb hKΦ hKfix hpc' htyArgs_lc hscrutImg'
    have hAgreeBelow₀ : Subst.AgreesBelow Φ S₀amb (S₀ ++ R₀) :=
      fun v hv => by rw [Subst.onTy_append]; exact hAgree₀ v hv
    let bodyCtxAlg : Ctx := { (S₀.onCtx ctx) with
        env := (ctor.contents.map (Ty.openWith
            (((freshVars Φ ctor.paramCount).map (Ty.fvar ·)).map S₀.onTy))).map PolyTy.mkTrivial
          ++ (S₀.onCtx ctx).env }
    have hctx0 : (R₀.onCtx (S₀.onCtx ctx)) = (S₀amb.onCtx ctx) := by
      rw [← Subst.onCtx_append]
      exact (Subst.onCtx_congr hAgreeBelow₀ hbelow).symm
    have hinstsE_direct :
        instContentsE =
          ctor.contents.map (fun c => Ty.openWith tyArgsE c) := by
      simpa [hctorE] using hinstsE
    have hbodyCtxEq : (R₀.onCtx bodyCtxAlg) = bodyCtx := by
      calc
        (R₀.onCtx bodyCtxAlg)
            = { (R₀.onCtx (S₀.onCtx ctx)) with
                env := (( ctor).contents.map
                  (fun c => Ty.openWith tyArgsE c)).map PolyTy.mkTrivial
                    ++ (R₀.onCtx (S₀.onCtx ctx)).env } := by
          rw [Subst.onCtx_branchBindings hR₀]
          rw [hmap₀]
        _ = { (S₀amb.onCtx ctx) with
                env := (( ctor).contents.map
                  (fun c => Ty.openWith tyArgsE c)).map PolyTy.mkTrivial
                    ++ (S₀amb.onCtx ctx).env } := by
          rw [hctx0]
        _ = bodyCtx := by
          rw [hctxdef]
          simp [hinstsE_direct]
    have hbE : Typing K bodyCtx body ( ρe) := by
      exact hbodyty
    have hbE' : Typing K (R₀.onCtx bodyCtxAlg) body ( ρe) := by
      rwa [← hbodyCtxEq] at hbE
    exact ⟨R₀, hR₀, hR₀K, hAgreeBelow₀, hbE'⟩

theorem _root_.InferBranches.nil_det
    (h : InferBranches κ F Φ ctx st rt [] Φ' S out) : Φ' = Φ ∧ S = [] := by
  cases h
  exact ⟨rfl, rfl⟩

private theorem branch_rigid_mem {bs : List (MatchPattern × Input)} {b : MatchPattern × Input}
    (hb : b ∈ bs) {v : Nat} (hv : v ∈ b.2.rigidVars) : v ∈ rigidBranchVars bs := by
  induction bs with
  | nil => cases hb
  | cons head tail ih =>
    exact (List.mem_cons.mp hb).elim (fun heq => List.mem_append_left _ (heq ▸ hv))
      (fun hb => List.mem_append_right _ (ih hb))

private theorem branch_candidates_frame {bs : List (MatchPattern × Input)}
    {ambient solved residual : Subst} {Φ : Nat} {ctx ctx' : Ctx} {P : List Nat} {st rt : Ty}
    (hbelow : ∀ v ∈ rigidBranchVars bs, v < Φ)
    (hag : Subst.AgreesBelow Φ ambient (solved ++ residual))
    (hctx : residual.onCtx ctx' = ambient.onCtx ctx)
    (hbr : ∀ b ∈ bs, BranchTyping Typing P (ambient.onCtx ctx)
      (b.1, b.2.substTyFvars ambient) st rt) :
    ∀ b ∈ substInputBranches solved bs,
      BranchTyping Typing P (residual.onCtx ctx') (b.1, b.2.substTyFvars residual) st rt := by
  intro b hb
  rw [substInputBranches_eq_map] at hb
  obtain ⟨original, horiginal, rfl⟩ := List.mem_map.mp hb
  have hsource : original.2.substTyFvars ambient =
      (original.2.substTyFvars solved).substTyFvars residual := by
    rw [← Input.substTyFvars_append]
    exact original.2.substTyFvars_congr (fun v hv => hag v (hbelow v (branch_rigid_mem horiginal hv)))
  rw [hctx, ← hsource]
  exact hbr original horiginal

private theorem branch_freeze_frame {κ : List Nat} {F : List Ty} {bs : List (MatchPattern × Input)}
    {ambient solved residual : Subst} {Φ : Nat}
    (hscope : ∀ v ∈ rigidBranchVars bs, v ∈ κ ++ softVars F)
    (hbelow : ∀ v ∈ rigidBranchVars bs, v < Φ)
    (hprefix : ∀ k ∈ κ, solved.onTy (.fvar k) = .fvar k)
    (hfreeze : ∀ v ∈ rigidBranchVars bs, v ∈ κ → v ∉ softVars F → ambient.onTy (.fvar v) = .fvar v)
    (hag : Subst.AgreesBelow Φ ambient (solved ++ residual)) :
    ∀ v ∈ rigidBranchVars (substInputBranches solved bs),
      v ∈ κ → v ∉ softVars (substSoft solved F) → residual.onTy (.fvar v) = .fvar v := by
  exact SourceScope.residual_freeze (input := .match_ (.var 0) bs) hscope hbelow hprefix hfreeze hag
set_option maxRecDepth 4096 in
theorem _root_.InferBranches.sourcePrincipal_of_body
    (h : InferBranches κ F Φ ctx scrutTy ρ brs Φ' S out) (hne : brs ≠ [])
    (bodyIH : ∀ body : Input, body.size < sizeBranches brs →
      ∀ {κ F' f c n s o t} (hb : Infer κ F' f c body n s o t), Infer.SourcePrincipal hb) :
    InferBranches.SourcePrincipal h hne := by
  cases h with
      | nil => exact False.elim (hne rfl)
      | @cons c nbr body rest κ F ctor scrutTy Φ S₀ ctx Φ₁ S₁ bodyOut τb ρ S₂ Φ' S₃ restOut hscope hlook hn h₀Rigid hinfbody h₂Rigid hrest =>
        have h₀ := h₀Rigid.unifies
        have h₂ := h₂Rigid.unifies
        exact fun hwf hbelow hκ hF S₀amb scruT₀ ρe K hS₀amb hscruLC hscrutLC hρLC hbscrut hbρ hKΦ hKfix hfreeze hIMGρ hIMGscru hbrs => by
          have hrawBelow : ∀ v ∈ rigidBranchVars ((.named c nbr, body) :: rest), v < Φ := by
            intro v hv
            exact (List.mem_append.mp (hscope v hv)).elim (hκ v) (softVars_lt hF v)
          have hbodyScope : SourceScope κ F body := fun v hv => hscope v (List.mem_append_left _ hv)
          have hbodyBelow : ∀ v ∈ body.rigidVars, v < Φ := fun v hv => hrawBelow v (List.mem_append_left _ hv)
          have hrestScope : ∀ v ∈ rigidBranchVars rest, v ∈ κ ++ softVars F :=
            fun v hv => hscope v (List.mem_append_right _ hv)
          have hrestBelow : ∀ v ∈ rigidBranchVars rest, v < Φ :=
            fun v hv => hrawBelow v (List.mem_append_right _ hv)
          obtain ⟨R₀, hR₀, hR₀K, hAgreeBelow₀, hbE'⟩ :=
            BranchTyping.factor_named hlook h₀ hbelow hbscrut hS₀amb hscruLC hKΦ hKfix hIMGscru
              (hbrs (.named c nbr, body) (List.mem_cons_self ..))
          have hS₀lc : ∀ p ∈ S₀, p.2.IsLC :=
            UnifyRel.lc h₀ hscrutLC (by
              apply ContainsBvarsUpTo.customTy
              intro t ht
              obtain ⟨x, _, rfl⟩ := List.mem_map.mp ht
              exact ContainsBvarsUpTo.fvar)
          have hS₀_bel : ∀ p ∈ S₀, Ty.BelowFvars (Φ + ctor.paramCount) p.2 :=
            UnifyRel.belowFvars h₀ (hbscrut.mono (by omega)) (by
              apply Ty.BelowFvars.customTy
              intro t ht
              obtain ⟨x, hx, rfl⟩ := List.mem_map.mp ht
              exact Ty.BelowFvars.fvar (by have := freshVars_lt x hx; omega))
          have hfle₀ : Φ ≤ Φ + ctor.paramCount := by omega
          let bodyCtxAlg : Ctx := { (S₀.onCtx ctx) with
              env := (ctor.contents.map (Ty.openWith
                  (((freshVars Φ ctor.paramCount).map (Ty.fvar ·)).map S₀.onTy))).map PolyTy.mkTrivial
                ++ (S₀.onCtx ctx).env }
          have hwf_body : CtxWF bodyCtxAlg := by
            dsimp [bodyCtxAlg]
            refine branchBindings_wf (ctorr := ctor)
              (ta := ((freshVars Φ ctor.paramCount).map (Ty.fvar ·)).map S₀.onTy)
              (Subst.onCtx_wf hS₀lc hwf) ?_ (by simp)
            intro t ht
            obtain ⟨v, hv, rfl⟩ := List.mem_map.mp ht
            obtain ⟨x, _, rfl⟩ := List.mem_map.mp hv
            exact Subst.onTy_lc hS₀lc ContainsBvarsUpTo.fvar
          have hbelow_body : CtxBelow (Φ + ctor.paramCount) bodyCtxAlg := by
            dsimp [bodyCtxAlg]
            refine branchBindings_below (ctorr := ctor)
              (ta := ((freshVars Φ ctor.paramCount).map (Ty.fvar ·)).map S₀.onTy)
              (Subst.onCtx_below hS₀_bel hfle₀ hbelow) ?_
            intro t ht
            obtain ⟨v, hv, rfl⟩ := List.mem_map.mp ht
            obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hv
            exact Subst.onTy_belowFvars hS₀_bel (.fvar (by have := freshVars_lt x hx; omega))
          have hKΦ₀ : ∀ k ∈ K, k < Φ + ctor.paramCount := fun k hk => lt_of_lt_of_le (hKΦ k hk) hfle₀
          have hsource0 : body.substTyFvars S₀amb = (body.substTyFvars S₀).substTyFvars R₀ := by
            rw [← Input.substTyFvars_append]
            exact body.substTyFvars_congr (fun v hv => hAgreeBelow₀ v (hbodyBelow v hv))
          have hF0 := substSoft_below hS₀_bel hfle₀ hF
          have hfreeze0 := hbodyScope.residual_freeze hbodyBelow
            (Subst.fixes_of_dom_avoids h₀Rigid.dom_avoids)
            (fun v hv => hfreeze v (List.mem_append_left _ hv)) hAgreeBelow₀
          obtain ⟨R_b, hR_b, htyb, hR_bK, hagb⟩ :=
            (bodyIH (body.substTyFvars S₀) (by simp only [Input.size_substTyFvars, sizeBranches]; omega) hinfbody)
              hwf_body hbelow_body (fun k hk => Nat.lt_of_lt_of_le (hκ k hk) hfle₀) hF0
              R₀ ρe K hR₀ hKΦ₀ hR₀K hfreeze0 (hsource0 ▸ hbE')
          have hle_b : Φ + ctor.paramCount ≤ Φ₁ := Infer.frontier_le hinfbody
          have hKΦ₁ : ∀ k ∈ K, k < Φ₁ := fun k hk => lt_of_lt_of_le (hKΦ₀ k hk) hle_b
          have hbodyLC := Infer.lc hinfbody hwf_body
          have hτb_lc : τb.IsLC := hbodyLC.1
          have hS₁lc : ∀ p ∈ S₁, p.2.IsLC := hbodyLC.2
          have hbb := Infer.belowFvars hinfbody hbelow_body (fun k hk => Nat.lt_of_lt_of_le (hκ k hk) hfle₀) hF0
          have hτb_bel : Ty.BelowFvars Φ₁ τb := hbb.1
          have hS₁_bel : ∀ p ∈ S₁, Ty.BelowFvars Φ₁ p.2 := hbb.2
          have htyb' : Eq ρe (R_b.onTy τb) :=
            htyb
          have hρbel₁ : Ty.BelowFvars (Φ + ctor.paramCount) (S₀.onTy ρ) :=
            Subst.onTy_belowFvars hS₀_bel (hbρ.mono hfle₀)
          have hρImg₀ : Eq ρe (R₀.onTy (S₀.onTy ρ)) := by
            rw [← Subst.onTy_append]
            exact Eq.trans hIMGρ (Subst.onTy_congr hAgreeBelow₀ hbρ)
          have hρImg_b : Eq ρe (R_b.onTy (S₁.onTy (S₀.onTy ρ))) := by
            rw [← Subst.onTy_append]
            exact Eq.trans hρImg₀ (Subst.onTy_congr hagb hρbel₁)
          have hUni : Unifies R_b τb (S₁.onTy (S₀.onTy ρ)) := by
            show Eq (R_b.onTy τb) (R_b.onTy (S₁.onTy (S₀.onTy ρ)))
            exact Eq.trans (Eq.symm htyb') hρImg_b
          obtain ⟨R_u, hR_u_fac, hR_u, hR_uK⟩ :=
            UnifyRel.greatest_K h₂ R_b hR_b hUni hR_bK
          have hS₂lc : ∀ p ∈ S₂, p.2.IsLC :=
            UnifyRel.lc h₂ hτb_lc (Subst.onTy_lc hS₁lc (Subst.onTy_lc hS₀lc hρLC))
          have hS₂_bel : ∀ p ∈ S₂, Ty.BelowFvars Φ₁ p.2 :=
            UnifyRel.belowFvars h₂ hτb_bel
              (Subst.onTy_belowFvars hS₁_bel
                ((Subst.onTy_belowFvars hS₀_bel (hbρ.mono hfle₀)).mono hle_b))
          have hAgreeUni : Subst.AgreesBelow Φ₁ R_b (S₂ ++ R_u) :=
            fun v hv => by rw [Subst.onTy_append]; exact hR_u_fac (Ty.fvar v)
          have hρImg_u : Eq ρe (R_u.onTy (S₂.onTy (S₁.onTy (S₀.onTy ρ)))) :=
            Eq.trans hρImg_b (hR_u_fac (S₁.onTy (S₀.onTy ρ)))
          have hwf' : CtxWF (S₂.onCtx (S₁.onCtx (S₀.onCtx ctx))) :=
            Subst.onCtx_wf hS₂lc (Subst.onCtx_wf hS₁lc (Subst.onCtx_wf hS₀lc hwf))
          have hbelow' : CtxBelow Φ₁ (S₂.onCtx (S₁.onCtx (S₀.onCtx ctx))) :=
            Subst.onCtx_below hS₂_bel (le_refl _)
              (Subst.onCtx_below hS₁_bel hle_b
                (Subst.onCtx_below hS₀_bel hfle₀ hbelow))
          have hbscrut' : Ty.BelowFvars Φ₁ (S₂.onTy (S₁.onTy (S₀.onTy scrutTy))) :=
            Subst.onTy_belowFvars hS₂_bel
              (Subst.onTy_belowFvars hS₁_bel
                ((Subst.onTy_belowFvars hS₀_bel (hbscrut.mono hfle₀)).mono hle_b))
          have hbρ' : Ty.BelowFvars Φ₁ (S₂.onTy (S₁.onTy (S₀.onTy ρ))) :=
            Subst.onTy_belowFvars hS₂_bel
              (Subst.onTy_belowFvars hS₁_bel
                ((Subst.onTy_belowFvars hS₀_bel (hbρ.mono hfle₀)).mono hle_b))
          have hscrutTy'lc : (S₂.onTy (S₁.onTy (S₀.onTy scrutTy))).IsLC :=
            Subst.onTy_lc hS₂lc (Subst.onTy_lc hS₁lc (Subst.onTy_lc hS₀lc hscrutLC))
          have hρ'lc : (S₂.onTy (S₁.onTy (S₀.onTy ρ))).IsLC :=
            Subst.onTy_lc hS₂lc (Subst.onTy_lc hS₁lc (Subst.onTy_lc hS₀lc hρLC))
          have hScrutStep1 : Eq (S₀amb.onTy scrutTy) (R₀.onTy (S₀.onTy scrutTy)) := by
            rw [← Subst.onTy_append]
            exact Subst.onTy_congr hAgreeBelow₀ hbscrut
          have hScrutStep2 : Eq (R₀.onTy (S₀.onTy scrutTy))
              (R_b.onTy (S₁.onTy (S₀.onTy scrutTy))) := by
            simpa [Subst.onTy_append] using
              (Subst.onTy_congr hagb (Subst.onTy_belowFvars hS₀_bel (hbscrut.mono hfle₀)))
          have hScrutStep3 : Eq (R_b.onTy (S₁.onTy (S₀.onTy scrutTy)))
              (R_u.onTy (S₂.onTy (S₁.onTy (S₀.onTy scrutTy)))) := by
            simpa [Subst.onTy_append] using (hR_u_fac (S₁.onTy (S₀.onTy scrutTy)))
          have hscrutImg' : Eq scruT₀ (R_u.onTy (S₂.onTy (S₁.onTy (S₀.onTy scrutTy)))) :=
            Eq.trans hIMGscru (Eq.trans hScrutStep1 (Eq.trans hScrutStep2 hScrutStep3))
          have hctxeq' : (R_u.onCtx (S₂.onCtx (S₁.onCtx (S₀.onCtx ctx))))
              = (S₀amb.onCtx ctx) := by
            have h1 : (R_u.onCtx (S₂.onCtx (S₁.onCtx (S₀.onCtx ctx))))
                = (R_b.onCtx (S₁.onCtx (S₀.onCtx ctx))) := by
              rw [← Subst.onCtx_append]
              exact (Subst.onCtx_congr hAgreeUni
                (Subst.onCtx_below hS₁_bel hle_b
                  (Subst.onCtx_below hS₀_bel hfle₀ hbelow))).symm
            have hAgree01 : Subst.AgreesBelow Φ S₀amb ((S₀ ++ S₁) ++ R_b) :=
              @Subst.AgreesBelow.trans_append Φ (Φ + ctor.paramCount) S₀amb S₀ R₀ S₁ R_b
                hfle₀ hAgreeBelow₀ hS₀_bel hagb
            have h2 : (R_b.onCtx (S₁.onCtx (S₀.onCtx ctx)))
                = (S₀amb.onCtx ctx) := by
              simpa [Subst.onCtx_append, List.append_assoc] using
                (Subst.onCtx_congr hAgree01 hbelow).symm
            exact h1.trans h2
          have hAgreePrefix : Subst.AgreesBelow Φ S₀amb ((S₀ ++ S₁ ++ S₂) ++ R_u) := by
            have hA : Subst.AgreesBelow Φ S₀amb ((S₀ ++ (S₁ ++ S₂)) ++ R_u) :=
              @Subst.AgreesBelow.trans_append Φ (Φ + ctor.paramCount) S₀amb S₀ R₀ (S₁ ++ S₂) R_u
                hfle₀ hAgreeBelow₀ hS₀_bel
                (@Subst.AgreesBelow.trans_append (Φ + ctor.paramCount) Φ₁ R₀ S₁ R_b S₂ R_u
                  hle_b hagb hS₁_bel hAgreeUni)
            simpa [List.append_assoc] using hA
          have hF' : ∀ t ∈ substSoft (S₀ ++ S₁ ++ S₂) F, Ty.BelowFvars Φ₁ t := by
            simpa only [substSoft_append] using substSoft_below hS₂_bel (le_refl _)
              (substSoft_below hS₁_bel hle_b hF0)
          have hprefixFix : ∀ k ∈ κ, (S₀ ++ S₁ ++ S₂).onTy (.fvar k) = .fvar k := by
            intro k hk
            simp only [Subst.onTy_append, Subst.fixes_of_dom_avoids h₀Rigid.dom_avoids k hk,
              Subst.fixes_of_dom_avoids hinfbody.dom_avoids k hk,
              Subst.fixes_of_dom_avoids h₂Rigid.dom_avoids k hk]
          have hfreeze' := branch_freeze_frame hrestScope hrestBelow hprefixFix
            (fun v hv => hfreeze v (List.mem_append_right _ hv)) hAgreePrefix
          have hbr' := branch_candidates_frame hrestBelow hAgreePrefix hctxeq'
            (fun b hb => hbrs b (List.mem_cons_of_mem _ hb))
          by_cases hrestNe : rest = []
          · -- rest = []: the rest derivation is `nil`, so S₃ = [] and Φ₂ = Φ₁.
            subst hrestNe
            have hnil := InferBranches.nil_det hrest
            have hAgree1 : Subst.AgreesBelow Φ S₀amb ((S₀ ++ S₁ ++ S₂) ++ R_u) := by
              have hA : Subst.AgreesBelow Φ S₀amb ((S₀ ++ (S₁ ++ S₂)) ++ R_u) :=
                @Subst.AgreesBelow.trans_append Φ (Φ + ctor.paramCount) S₀amb S₀ R₀ (S₁ ++ S₂) R_u
                  hfle₀ hAgreeBelow₀ hS₀_bel
                  (@Subst.AgreesBelow.trans_append (Φ + ctor.paramCount) Φ₁ R₀ S₁ R_b S₂ R_u
                    hle_b hagb hS₁_bel hAgreeUni)
              simpa [List.append_assoc] using hA
            rw [hnil.2]
            refine ⟨R_u, hR_u, by simpa [List.append_assoc, List.append_nil] using hAgree1, hR_uK, ?_⟩
            · simpa [Subst.onTy_append, List.append_assoc, List.append_nil] using hρImg_u
          · -- rest ≠ []: recurse with the tier IH.
            have hrestNe' : rest ≠ [] := hrestNe
            obtain ⟨R_r, hR_r, hAgreeRest, hR_rK, htyRest⟩ :=
              InferBranches.sourcePrincipal_of_body hrest (by
                intro heq
                cases rest with
                | nil => exact hrestNe rfl
                | cons b bs => cases heq)
                (fun b hb {_ _ _ _ _ _ _ _} hi => bodyIH b (by
                  rw [sizeBranches_substInputBranches] at hb
                  simp only [sizeBranches]; omega) hi)
                hwf' hbelow' (fun k hk => Nat.lt_of_lt_of_le (hκ k hk) (by omega)) hF' R_u scruT₀ ρe K
                hR_u hscruLC hscrutTy'lc hρ'lc hbscrut' hbρ' hKΦ₁ hR_uK hfreeze' hρImg_u hscrutImg' hbr'
            have hAgree1 : Subst.AgreesBelow Φ₁ R_u (S₃ ++ R_r) := hAgreeRest
            have hAgree01 : Subst.AgreesBelow Φ S₀amb ((S₀ ++ S₁ ++ S₂) ++ R_u) := by
              have hA : Subst.AgreesBelow Φ S₀amb ((S₀ ++ (S₁ ++ S₂)) ++ R_u) :=
                @Subst.AgreesBelow.trans_append Φ (Φ + ctor.paramCount) S₀amb S₀ R₀ (S₁ ++ S₂) R_u
                  hfle₀ hAgreeBelow₀ hS₀_bel
                  (@Subst.AgreesBelow.trans_append (Φ + ctor.paramCount) Φ₁ R₀ S₁ R_b S₂ R_u
                    hle_b hagb hS₁_bel hAgreeUni)
              simpa [List.append_assoc] using hA
            have hAgree : Subst.AgreesBelow Φ S₀amb ((S₀ ++ S₁ ++ S₂ ++ S₃) ++ R_r) := by
              have hA : Subst.AgreesBelow Φ S₀amb (((S₀ ++ S₁ ++ S₂) ++ S₃) ++ R_r) :=
                @Subst.AgreesBelow.trans_append Φ Φ₁ S₀amb (S₀ ++ S₁ ++ S₂) R_u S₃ R_r (by omega)
                  hAgree01
                  (fun p hp => by
                    rcases List.mem_append.mp hp with hp | hp
                    · rcases List.mem_append.mp hp with hp | hp
                      · exact (hS₀_bel p hp).mono hle_b
                      · exact hS₁_bel p hp
                    · exact hS₂_bel p hp)
                  hAgreeRest
              simpa [List.append_assoc] using hA
            refine ⟨R_r, hR_r, hAgree, hR_rK, ?_⟩
            · simpa [Subst.onTy_append] using htyRest
      | @consWild body rest κ F Φ ctx Φ₁ S₁ bodyOut τb ρ S₂ scrutTy Φ' S₃ restOut hscope hinfbody h₂Rigid hrest =>
        have h₂ := h₂Rigid.unifies
        exact fun hwf hbelow hκ hF S₀amb scruT₀ ρe K hS₀amb hscruLC hscrutLC hρLC hbscrut hbρ hKΦ hKfix hfreeze hIMGρ hIMGscru hbrs => by
          have hrawBelow : ∀ v ∈ rigidBranchVars ((.wildcard, body) :: rest), v < Φ := by
            intro v hv
            exact (List.mem_append.mp (hscope v hv)).elim (hκ v) (softVars_lt hF v)
          have hbodyScope : SourceScope κ F body := fun v hv => hscope v (List.mem_append_left _ hv)
          have hbodyBelow : ∀ v ∈ body.rigidVars, v < Φ := fun v hv => hrawBelow v (List.mem_append_left _ hv)
          have hrestScope : ∀ v ∈ rigidBranchVars rest, v ∈ κ ++ softVars F :=
            fun v hv => hscope v (List.mem_append_right _ hv)
          have hrestBelow : ∀ v ∈ rigidBranchVars rest, v < Φ :=
            fun v hv => hrawBelow v (List.mem_append_right _ hv)
          have hdhead := hbrs (.wildcard, body) (List.mem_cons_self ..)
          have hbodyD : Typing K (S₀amb.onCtx ctx) (body.substTyFvars S₀amb) ρe := by
            cases hdhead with
            | wildcard hbodyty => exact hbodyty
          obtain ⟨R_b, hR_b, htyb, hR_bK, hagb⟩ :=
            (bodyIH body (by simp only [sizeBranches]; omega) hinfbody)
              hwf hbelow hκ hF S₀amb ρe K hS₀amb hKΦ hKfix
                (fun v hv => hfreeze v (List.mem_append_left _ hv)) hbodyD
          have hle_b : Φ ≤ Φ₁ := Infer.frontier_le hinfbody
          have hKΦ₁ : ∀ k ∈ K, k < Φ₁ := fun k hk => lt_of_lt_of_le (hKΦ k hk) hle_b
          have hbodyLC := Infer.lc hinfbody hwf
          have hτb_lc : τb.IsLC := hbodyLC.1
          have hS₁lc : ∀ p ∈ S₁, p.2.IsLC := hbodyLC.2
          have hbb := Infer.belowFvars hinfbody hbelow hκ hF
          have hτb_bel : Ty.BelowFvars Φ₁ τb := hbb.1
          have hS₁_bel : ∀ p ∈ S₁, Ty.BelowFvars Φ₁ p.2 := hbb.2
          have hρImg_b : Eq ρe (R_b.onTy (S₁.onTy ρ)) := by
            rw [← Subst.onTy_append]
            exact Eq.trans hIMGρ (Subst.onTy_congr hagb hbρ)
          have hUni : Unifies R_b τb (S₁.onTy ρ) := by
            show Eq (R_b.onTy τb) (R_b.onTy (S₁.onTy ρ))
            exact Eq.trans (Eq.symm htyb) hρImg_b
          obtain ⟨R_u, hR_u_fac, hR_u, hR_uK⟩ :=
            UnifyRel.greatest_K h₂ R_b hR_b hUni hR_bK
          have hS₂lc : ∀ p ∈ S₂, p.2.IsLC :=
            UnifyRel.lc h₂ hτb_lc (Subst.onTy_lc hS₁lc hρLC)
          have hS₂_bel : ∀ p ∈ S₂, Ty.BelowFvars Φ₁ p.2 :=
            UnifyRel.belowFvars h₂ hτb_bel (Subst.onTy_belowFvars hS₁_bel (hbρ.mono hle_b))
          have hAgreeUni : Subst.AgreesBelow Φ₁ R_b (S₂ ++ R_u) :=
            fun v hv => by rw [Subst.onTy_append]; exact hR_u_fac (Ty.fvar v)
          have hρImg_u : Eq ρe (R_u.onTy (S₂.onTy (S₁.onTy ρ))) :=
            Eq.trans hρImg_b (hR_u_fac (S₁.onTy ρ))
          have hwf' : CtxWF (S₂.onCtx (S₁.onCtx ctx)) :=
            Subst.onCtx_wf hS₂lc (Subst.onCtx_wf hS₁lc hwf)
          have hbelow' : CtxBelow Φ₁ (S₂.onCtx (S₁.onCtx ctx)) :=
            Subst.onCtx_below hS₂_bel (le_refl _) (Subst.onCtx_below hS₁_bel hle_b hbelow)
          have hbscrut' : Ty.BelowFvars Φ₁ (S₂.onTy (S₁.onTy scrutTy)) :=
            Subst.onTy_belowFvars hS₂_bel (Subst.onTy_belowFvars hS₁_bel (hbscrut.mono hle_b))
          have hbρ' : Ty.BelowFvars Φ₁ (S₂.onTy (S₁.onTy ρ)) :=
            Subst.onTy_belowFvars hS₂_bel (Subst.onTy_belowFvars hS₁_bel (hbρ.mono hle_b))
          have hscrutTy'lc : (S₂.onTy (S₁.onTy scrutTy)).IsLC :=
            Subst.onTy_lc hS₂lc (Subst.onTy_lc hS₁lc hscrutLC)
          have hρ'lc : (S₂.onTy (S₁.onTy ρ)).IsLC :=
            Subst.onTy_lc hS₂lc (Subst.onTy_lc hS₁lc hρLC)
          have hScrutStep1 : Eq (S₀amb.onTy scrutTy) (R_b.onTy (S₁.onTy scrutTy)) := by
            simpa [Subst.onTy_append] using (Subst.onTy_congr hagb hbscrut)
          have hScrutStep2 : Eq (R_b.onTy (S₁.onTy scrutTy))
              (R_u.onTy (S₂.onTy (S₁.onTy scrutTy))) := by
            simpa [Subst.onTy_append] using (hR_u_fac (S₁.onTy scrutTy))
          have hscrutImg' : Eq scruT₀ (R_u.onTy (S₂.onTy (S₁.onTy scrutTy))) :=
            Eq.trans hIMGscru (Eq.trans hScrutStep1 hScrutStep2)
          have hctxeq' : (R_u.onCtx (S₂.onCtx (S₁.onCtx ctx)))
              = (S₀amb.onCtx ctx) := by
            have h1 : (R_u.onCtx (S₂.onCtx (S₁.onCtx ctx)))
                = (R_b.onCtx (S₁.onCtx ctx)) := by
              rw [← Subst.onCtx_append]
              exact (Subst.onCtx_congr hAgreeUni (Subst.onCtx_below hS₁_bel hle_b hbelow)).symm
            have h2 : (R_b.onCtx (S₁.onCtx ctx)) = (S₀amb.onCtx ctx) := by
              rw [← Subst.onCtx_append]
              exact (Subst.onCtx_congr hagb hbelow).symm
            exact h1.trans h2
          have hAgreePrefix : Subst.AgreesBelow Φ S₀amb ((S₁ ++ S₂) ++ R_u) :=
            Subst.AgreesBelow.trans_append hle_b hagb hS₁_bel hAgreeUni
          have hF' : ∀ t ∈ substSoft (S₁ ++ S₂) F, Ty.BelowFvars Φ₁ t := by
            simpa only [substSoft_append] using substSoft_below hS₂_bel (le_refl _)
              (substSoft_below hS₁_bel hle_b hF)
          have hprefixFix : ∀ k ∈ κ, (S₁ ++ S₂).onTy (.fvar k) = .fvar k := by
            intro k hk
            simp only [Subst.onTy_append, Subst.fixes_of_dom_avoids hinfbody.dom_avoids k hk,
              Subst.fixes_of_dom_avoids h₂Rigid.dom_avoids k hk]
          have hfreeze' := branch_freeze_frame hrestScope hrestBelow hprefixFix
            (fun v hv => hfreeze v (List.mem_append_right _ hv)) hAgreePrefix
          have hbr' := branch_candidates_frame hrestBelow hAgreePrefix hctxeq'
            (fun b hb => hbrs b (List.mem_cons_of_mem _ hb))
          by_cases hrestNe : rest = []
          · subst hrestNe
            have hnil := InferBranches.nil_det hrest
            have hAgree : Subst.AgreesBelow Φ S₀amb ((S₁ ++ S₂) ++ R_u) :=
              @Subst.AgreesBelow.trans_append Φ Φ₁ S₀amb S₁ R_b S₂ R_u hle_b hagb hS₁_bel hAgreeUni
            rw [hnil.2]
            refine ⟨R_u, hR_u, by simpa [List.append_assoc, List.append_nil] using hAgree, hR_uK, ?_⟩
            · simpa [Subst.onTy_append, List.append_assoc, List.append_nil] using hρImg_u
          · have hrestNe' : rest ≠ [] := hrestNe
            obtain ⟨R_r, hR_r, hAgreeRest, hR_rK, htyRest⟩ :=
              InferBranches.sourcePrincipal_of_body hrest (by
                intro heq
                cases rest with
                | nil => exact hrestNe rfl
                | cons b bs => cases heq)
                (fun b hb {_ _ _ _ _ _ _ _} hi => bodyIH b (by
                  rw [sizeBranches_substInputBranches] at hb
                  simp only [sizeBranches]; omega) hi)
                hwf' hbelow' (fun k hk => Nat.lt_of_lt_of_le (hκ k hk) hle_b) hF' R_u scruT₀ ρe K
                hR_u hscruLC hscrutTy'lc hρ'lc hbscrut' hbρ' hKΦ₁ hR_uK hfreeze' hρImg_u hscrutImg' hbr'
            have hAgree : Subst.AgreesBelow Φ S₀amb ((S₁ ++ S₂ ++ S₃) ++ R_r) := by
              have hA : Subst.AgreesBelow Φ S₀amb (((S₁ ++ S₂) ++ S₃) ++ R_r) :=
                @Subst.AgreesBelow.trans_append Φ Φ₁ S₀amb (S₁ ++ S₂) R_u S₃ R_r hle_b
                  (@Subst.AgreesBelow.trans_append Φ Φ₁ S₀amb S₁ R_b S₂ R_u hle_b hagb hS₁_bel hAgreeUni)
                  (fun p hp => by
                    rcases List.mem_append.mp hp with hp | hp
                    · exact hS₁_bel p hp
                    · exact hS₂_bel p hp)
                  hAgreeRest
              simpa [List.append_assoc] using hA
            refine ⟨R_r, hR_r, hAgree, hR_rK, ?_⟩
            · simpa [Subst.onTy_append] using htyRest

termination_by sizeBranches brs
decreasing_by all_goals (subst_vars; simp only [sizeBranches_substInputBranches, sizeBranches]; omega)


theorem _root_.Infer.sourcePrincipal_match
    (hscope : SourceScope K F (.match_ scrut branches))
    (hs : Infer K F frontier ctx scrut first s1 scrutOut scrutTy)
    (hne : branches ≠ [])
    (hb : InferBranches K (substSoft s1 F) (first + 1) (s1.onCtx ctx) scrutTy (.fvar first)
      (substInputBranches s1 branches) next s2 branchesOut)
    (ihs : Infer.SourcePrincipal hs)
    (bodyIH : ∀ body : Input, body.size < sizeBranches branches →
      ∀ {κ F' f c n s o t} (hi : Infer κ F' f c body n s o t), Infer.SourcePrincipal hi) :
    Infer.SourcePrincipal (.match_ hscope hs hne hb) := by
  intro hwf hbelow hK hF ambient target P hS hP hfix hfreeze htyping
  obtain ⟨scrutD, hsD, _, hbD⟩ := htyping.match_inv
  obtain ⟨R1, hR1, hscrut, hR1P, hag1⟩ := ihs hwf hbelow hK hF ambient
    scrutD P hS hP hfix (fun v hv => hfreeze v (List.mem_append_left _ hv)) hsD
  have hle := hs.frontier_le
  obtain ⟨hsB, hs1B⟩ := hs.belowFvars hbelow hK hF
  obtain ⟨hsLC, hs1LC⟩ := hs.lc hwf
  have hctxWF := Subst.onCtx_wf hs1LC hwf
  have hctxB := Subst.onCtx_below hs1B hle hbelow
  obtain ⟨U, hU, hagU, hblock⟩ := Subst.override_block hR1 first [target]
    (by simpa using htyping.regular)
  have hUtarget : U.onTy (.fvar first) = target := by simpa using hblock 0 (by simp)
  have hctxeq : U.onCtx (s1.onCtx ctx) = ambient.onCtx ctx := by
    trans R1.onCtx (s1.onCtx ctx)
    · exact (Subst.onCtx_congr hagU hctxB).symm
    · rw [← Subst.onCtx_append]
      exact (Subst.onCtx_congr hag1 hbelow).symm
  have hUP : ∀ p ∈ P, U.onTy (.fvar p) = .fvar p := fun p hp =>
    (hagU p (Nat.lt_of_lt_of_le (hP p hp) hle)).symm.trans (hR1P p hp)
  have hUst : scrutD = U.onTy scrutTy :=
    hscrut.trans (Subst.onTy_congr hagU hsB)
  have hagSU : Subst.AgreesBelow frontier ambient (s1 ++ U) := by
    intro v hv
    exact (hag1 v hv).trans (by
      rw [Subst.onTy_append, Subst.onTy_append]
      exact Subst.onTy_congr hagU (Subst.onTy_belowFvars hs1B (.fvar (Nat.lt_of_lt_of_le hv hle))))
  have hbranchScope : ∀ v ∈ rigidBranchVars branches, v ∈ K ++ softVars F :=
    fun v hv => hscope v (List.mem_append_right _ hv)
  have hbranchBelow : ∀ v ∈ rigidBranchVars branches, v < frontier := fun v hv =>
    (List.mem_append.mp (hbranchScope v hv)).elim (hK v) (softVars_lt hF v)
  have hfreezeB := branch_freeze_frame hbranchScope hbranchBelow
    (Subst.fixes_of_dom_avoids hs.dom_avoids)
    (fun v hv => hfreeze v (List.mem_append_right _ hv)) hagSU
  have hbrU := branch_candidates_frame hbranchBelow hagSU hctxeq (by
    intro b hb
    exact hbD (b.1, b.2.substTyFvars ambient) (by
      rw [substInputBranches_eq_map]
      exact List.mem_map.mpr ⟨b, hb, rfl⟩))
  have hne' : substInputBranches s1 branches ≠ [] := by
    cases branches with
    | nil => exact False.elim (hne rfl)
    | cons b bs => intro heq; cases heq
  have ihb := hb.sourcePrincipal_of_body hne' (fun body hbody {_ _ _ _ _ _ _ _} hi =>
    bodyIH body (by rwa [sizeBranches_substInputBranches] at hbody) hi)
  obtain ⟨R2, hR2, hag2, hR2P, htarget⟩ := ihb hctxWF
    (fun M hM => (hctxB M hM).mono (by omega))
    (fun k hk => by have := hK k hk; omega)
    (substSoft_below (fun p hp => (hs1B p hp).mono (Nat.le_succ _))
      (hle.trans (Nat.le_succ _)) hF)
    U scrutD target P hU hsD.regular hsLC .fvar
    (hsB.mono (by omega)) (.fvar (by omega))
    (fun p hp => by have := hP p hp; omega) hUP hfreezeB hUtarget.symm hUst hbrU
  have hag2' : Subst.AgreesBelow first R1 (s2 ++ R2) := fun v hv =>
    (hagU v hv).trans (hag2 v (by omega))
  exact ⟨R2, hR2, htarget, hR2P, Subst.AgreesBelow.trans_append hle hag1 hs1B hag2'⟩

private theorem branch_size_lt {branch : MatchPattern × Input}
    (h : branch ∈ branches) : branch.2.size < sizeBranches branches := by
  induction branches with
  | nil => cases h
  | cons head rest ih =>
    rcases List.mem_cons.mp h with rfl | h
    · simp only [sizeBranches]; omega
    · have := ih h; simp only [sizeBranches]; omega

theorem _root_.Infer.sourcePrincipal_letSignature {rhs body : Input} {ann : LetAnn}
    (hscope : SourceScope K F (.letIn ann rhs body))
    (hprefix : written = freshVars frontier ann.paramCount)
    (havoid : ∀ name ∈ written, name ∉ K ++ softVars F)
    (hraw : ∀ v ∈ rhs.rigidVars, v ∈ K ++ softVars F)
    (hr : Infer (K ++ written) F (frontier + ann.paramCount) ctx (rhs.openTyVars written) first s1 rhsOut rhsTy)
    (hc : SignatureCheck K (substSoft s1 F) written first rhsTy (ann.substTyFvars s1) checked sCheck)
    (hescape : ∀ name ∈ written, name ∉ (sCheck.onCtx (s1.onCtx ctx)).env.freeVars ++ softVars (substSoft (s1 ++ sCheck) F))
    (hb : Infer K (substSoft (s1 ++ sCheck) F) checked
      { sCheck.onCtx (s1.onCtx ctx) with
        env := signatureScheme (ann.substTyFvars (s1 ++ sCheck)) (K ++ softVars (substSoft (s1 ++ sCheck) F))
          written (sCheck.onCtx (s1.onCtx ctx)) (sCheck.onTy rhsTy) ::
          (sCheck.onCtx (s1.onCtx ctx)).env }
      (body.substTyFvars (s1 ++ sCheck)) next s2 bodyOut bodyTy)
    (ihr : Infer.SourcePrincipal hr) (ihb : Infer.SourcePrincipal hb) :
    Infer.SourcePrincipal (.letSignature hscope hprefix havoid hraw hr hc hescape hb) := by
  intro hwf hbelow hK hF ambient target P hS hP hfix hfreeze ht
  subst written
  have hmode : ann.isSignature = true := by
    have hm : (ann.substTyFvars s1).isSignature = true := by cases ann <;> cases hc <;> rfl
    simpa only [LetAnn.isSignature_substTyFvars] using hm
  obtain ⟨W, M, L, hMoved, hMovedFix, hBackAmbient, hBackLC, hBackP, hRestore,
      hMovedFreeze, hM, hann, hrhs, hfits, htypes, hbodyD, hYsM, hYsCtx, hYsSoft, hYsImages⟩ :=
    ht.signature_dodge_source hmode hscope hbelow hP hK hF hS hfix hfreeze
  obtain ⟨V, hV, hVP, hagPrefix, hbodyV, hbodyWF, hbodyB, hprefixB, _⟩ :=
    Infer.source_signature_frame hscope hr hc ihr rfl hwf hbelow hK hF hMoved hP hMovedFix hMovedFreeze
      hM hann hrhs hfits htypes hbodyD hYsM hYsCtx hYsImages hYsSoft
  have hleOpen := hr.frontier_le.trans hc.frontier_le
  have hle : frontier ≤ checked := (Nat.le_add_right frontier ann.paramCount).trans hleOpen
  have hprefixFix : ∀ k ∈ K, (s1 ++ sCheck).onTy (.fvar k) = .fvar k := by
    apply Subst.fixes_of_dom_avoids
    intro p hp hk
    exact (List.mem_append.mp hp).elim
      (fun hp => hr.dom_avoids p hp (List.mem_append_left _ hk))
      (fun hp => hc.dom_avoids p hp (List.mem_append_left _ hk))
  have hbodyFreeze :=
    (show SourceScope K F body from fun v hv => hscope v (List.mem_append_right _ hv)).residual_freeze
      (fun v hv => (List.mem_append.mp (hscope v (List.mem_append_right _ hv))).elim
        (hK v) (softVars_lt hF v)) hprefixFix
      (fun v hv => hMovedFreeze v (List.mem_append_right _ hv))
      (fun v hv => hagPrefix v (by omega))
  obtain ⟨R, hR, hresult, hRP, hagBody⟩ := ihb hbodyWF hbodyB
    (fun k hk => Nat.lt_of_lt_of_le (hK k hk) hle)
    (substSoft_below hprefixB hle hF) V _ P hV
    (fun p hp => Nat.lt_of_lt_of_le (hP p hp) hle)
    (fun p hp => hVP p (List.mem_append_left _ hp)) hbodyFreeze hbodyV
  have hag := Subst.AgreesBelow.trans_append hleOpen hagPrefix hprefixB hagBody
  refine ⟨R ++ blockListBack frontier W ann.paramCount,
    (fun p hp => (List.mem_append.mp hp).elim (hR p) (hBackLC p)), ?_, ?_, ?_⟩
  · simpa only [Subst.onTy_append, ← hresult] using hRestore.symm
  · intro p hp
    rw [Subst.onTy_append, hRP p hp]
    exact hBackP p hp
  · intro v hv
    have heq := congrArg (blockListBack frontier W ann.paramCount).onTy (hag v (by omega))
    rw [hBackAmbient v hv] at heq
    simpa only [Subst.onTy_append, List.append_assoc] using heq


/-- A residual compares live pending monotypes exactly and completed exports
by scheme generality. No equation is retained for a completed raw monotype.
`Xs` is an internal opening of the independent candidate pool and may be
re-chosen between components; it is never a public candidate bound. -/
structure RecResidual (P : List Nat) (declCtx : Ctx) (declSpecs : List RecSpec)
    (declPrefixes : List (List Nat)) (declPool Xs : List Nat)
    (ctx : Ctx) (state : RecState) (done : List Nat) (R : Subst) : Prop where
  lc : ∀ pair ∈ R, pair.2.IsLC
  fixes : ∀ p ∈ P, R.onTy (.fvar p) = .fvar p
  ctx_eq : R.onCtx ctx = declCtx
  length : state.specs.length = declSpecs.length
  mono : ∀ (i : Nat) (algTy : Ty), state.specs[i]? = some (.mono algTy) →
    ∃ (declTy : Ty), declSpecs[i]? = some (.mono declTy)
  poly : ∀ (i : Nat) (algScheme : PolyTy), state.specs[i]? = some (.poly algScheme) →
    ∃ (declScheme : PolyTy), declSpecs[i]? = some (.poly declScheme) ∧
      R.onPolyTy algScheme = declScheme
  pending : ∀ (i : Nat) (algTy declTy : Ty), state.specs[i]? = some (.mono algTy) →
    declSpecs[i]? = some (.mono declTy) → i ∉ done →
      R.onTy algTy = Ty.renameG declPool Xs declTy
  completed : ∀ (i : Nat) (algTy declTy : Ty), state.specs[i]? = some (.mono algTy) →
    declSpecs[i]? = some (.mono declTy) → i ∈ done →
      ∃ exported, state.exports[i]? = some (some exported) ∧
        (R.onPolyTy exported).Generalizes
          (recScheme (declPrefixes[i]?.getD []) declPool declTy)


private theorem residual_entries_at {state : RecState} {i : Nat} {spec : RecSpec}
    {exported : Option PolyTy} (hs : state.specs[i]? = some spec)
    (he : state.exports[i]? = some exported) :
    state.entries[i]? = some (exported.getD spec.monoEntry) := by
  have hz : (state.specs.zip state.exports)[i]? = some (spec, exported) :=
    List.getElem?_zip_eq_some.mpr ⟨hs, he⟩
  simp only [RecState.entries, List.getElem?_map, hz, Option.map_some]

private theorem residual_not_mem_take {anns : List (Option PolyTy)} {bindings : List Expr}
    {groups : List (List Nat)} (h : RecGroups.ValidResidualGroups anns bindings groups)
    {stage member : Nat} {component : List Nat}
    (hc : groups[stage]? = some component) (hm : member ∈ component) :
    member ∉ (groups.take stage).flatten := by
  intro hp
  obtain ⟨prior, hprior, hmp⟩ := List.mem_flatten.mp hp
  obtain ⟨priorStage, hps⟩ := List.mem_iff_getElem?.mp hprior
  have hpbound := (List.getElem?_eq_some_iff.mp hps).1
  have hbound := (List.getElem?_eq_some_iff.mp hc).1
  simp only [List.length_take] at hpbound
  have hlt : priorStage < stage := by omega
  rw [List.getElem?_take, if_pos hlt] at hps
  have hdisjoint := (List.pairwise_iff_getElem.mp (List.nodup_flatten.mp h.flatten_nodup).2)
    priorStage stage (List.getElem?_eq_some_iff.mp hps).1 hbound hlt
  rw [(List.getElem?_eq_some_iff.mp hps).2, (List.getElem?_eq_some_iff.mp hc).2] at hdisjoint
  exact List.disjoint_left.mp hdisjoint hmp hm

theorem RecResidual.componentMonoTyped
    {P declPool Xs K done : List Nat} {F : List Ty} {base algorithmStage : Nat}
    {declCtx ctx : Ctx} {declSpecs : List RecSpec} {declPrefixes : List (List Nat)}
    {state : RecState} {R : Subst} {anns declAnns : List LetAnn}
    {bindings declBindings : List Input} {declGroups : List (List Nat)} {component : List Nat}
    (h : RecResidual P declCtx declSpecs declPrefixes declPool Xs ctx state done R)
    (hframe : state.Frame base K F ctx anns done)
    (hbindings : bindings.map Input.erase = declBindings.map Input.erase)
    (hmask : ∀ i, RecGroup.isUnsignedAt (anns.map LetAnn.recModeAnn) i =
      RecGroup.isUnsignedAt (declAnns.map LetAnn.recModeAnn) i)
    (halgorithm : (RecGroup.inferenceSccs (anns.map LetAnn.recModeAnn)
      (bindings.map Input.erase))[algorithmStage]? = some component)
    (hdone : done = ((RecGroup.inferenceSccs (anns.map LetAnn.recModeAnn)
      (bindings.map Input.erase)).take algorithmStage).flatten)
    (hvalidDecl : RecGroups.ValidResidualGroups (declAnns.map LetAnn.recModeAnn)
      (declBindings.map Input.erase) declGroups)
    (hdeclWF : RecSpecs.WF (declAnns.map LetAnn.recModeAnn)
      (declBindings.map Input.erase) declSpecs declPool)
    (hprefix : RecPrefixesWF declAnns declSpecs declPrefixes declPool)
    (hmonoDecl : ∀ stage declComponent, declGroups[stage]? = some declComponent →
      ∀ member ∈ declComponent, ∀ rhs declTy,
      declBindings[member]? = some rhs → declSpecs[member]? = some (.mono declTy) →
      Typing (P ++ Xs) (recStageCtx declCtx declSpecs declPrefixes
        (declGroups.take stage).flatten declPool Xs)
        (rhs.openTyVars (recRenameNames declPool Xs (declPrefixes[member]?.getD [])))
        (Ty.renameG declPool Xs declTy))
    {member : Nat} {rawRhs : Input} {algTy : Ty}
    (hrhs : declBindings[member]? = some rawRhs)
    (halgTy : state.specs[member]? = some (.mono algTy)) (hmember : member ∈ component)
    (hscope : ∀ v ∈ rawRhs.rigidVars, v ∈ P) :
    Typing (P ++ recRenameNames declPool Xs (declPrefixes[member]?.getD []))
      (R.onCtx (state.rhsCtx ctx))
      (rawRhs.openTyVars (recRenameNames declPool Xs (declPrefixes[member]?.getD [])))
      (R.onTy algTy) := by
  have hschedule : RecGroup.inferenceSccs (anns.map LetAnn.recModeAnn) (bindings.map Input.erase) =
      RecGroup.inferenceSccs (declAnns.map LetAnn.recModeAnn) (declBindings.map Input.erase) := by
    rw [hbindings]
    exact RecGroup.inferenceSccs_congr_mask _ hmask
  have halgorithm' := halgorithm
  rw [hschedule] at halgorithm'
  have hdone' := hdone
  rw [hschedule] at hdone'
  have hvalidAlgorithm := RecGroup.inferenceSccs_valid hvalidDecl.length
  obtain ⟨declTy, hdeclTy⟩ := h.mono member algTy halgTy
  obtain ⟨declStage, declComponent, hdeclComponent, hcontained⟩ :=
    hvalidDecl.canonical_component_contained halgorithm'
  have hmemberDecl : member ∈ declComponent := hcontained member hmember
  have htypedDecl := hmonoDecl declStage declComponent hdeclComponent member hmemberDecl
    rawRhs declTy hrhs hdeclTy
  let declDone := (declGroups.take declStage).flatten
  let oldEntries := declSpecs.mapIdx (recStageEntry declPrefixes declDone declPool Xs)
  let newEntries := state.entries.map R.onPolyTy
  have hlenEntries : oldEntries.length = newEntries.length := by
    simp only [oldEntries, newEntries, List.length_mapIdx, List.length_map]
    rw [hframe.entries_length, ← hframe.specs_length, h.length]
  have htypedDecl' : Typing (P ++ Xs) ⟨oldEntries ++ declCtx.env, declCtx.ctors⟩
      (rawRhs.openTyVars (recRenameNames declPool Xs (declPrefixes[member]?.getD [])))
      (Ty.renameG declPool Xs declTy) := htypedDecl
  have htypedNew : Typing (P ++ Xs) ⟨newEntries ++ declCtx.env, declCtx.ctors⟩
      (rawRhs.openTyVars (recRenameNames declPool Xs (declPrefixes[member]?.getD [])))
      (Ty.renameG declPool Xs declTy) := by
    apply Typing.weaken_recGroupRefs hlenEntries ?_ htypedDecl'
    intro target hold hnew href
    have htargetBound : target < state.specs.length := by
      have : target < declSpecs.length := by simpa only [oldEntries, List.length_mapIdx] using hold
      rw [h.length]
      exact this
    have htarget : state.specs[target]? = some state.specs[target] :=
      List.getElem?_eq_getElem htargetBound
    cases hs : state.specs[target] with
    | poly scheme =>
      have htargetPoly : state.specs[target]? = some (.poly scheme) := by simpa only [hs] using htarget
      obtain ⟨declScheme, hdeclPoly, hpoly⟩ := h.poly target scheme htargetPoly
      have he := residual_entries_at htargetPoly (hframe.poly target scheme htargetPoly)
      have hne : newEntries[target]? = some declScheme := by
        simp only [newEntries, List.getElem?_map, he, Option.map_some, Option.getD_some, hpoly]
      have hoe : oldEntries[target]? = some declScheme := by
        simp only [oldEntries, List.getElem?_mapIdx, hdeclPoly, Option.map_some, recStageEntry]
      rw [(List.getElem?_eq_some_iff.mp hne).2, (List.getElem?_eq_some_iff.mp hoe).2]
      exact PolyTy.Generalizes.refl _
    | mono targetTy =>
      have htargetMono : state.specs[target]? = some (.mono targetTy) := by simpa only [hs] using htarget
      obtain ⟨declTargetTy, hdeclTarget⟩ := h.mono target targetTy htargetMono
      have href' : target ∈ rawRhs.erase.recGroupRefs (declBindings.map Input.erase).length 0 := by
        simpa only [Input.erase_openTyVars, oldEntries, List.length_mapIdx, hdeclWF.length] using href
      have hrhs' : (declBindings.map Input.erase)[member]? = some rawRhs.erase := by
        simp only [List.getElem?_map, hrhs, Option.map_some]
      have havailable := hvalidAlgorithm.refs_available hdeclWF.anns_eq hdeclWF.length
        halgorithm' hmember hrhs' hdeclTarget href'
      rcases havailable with htargetDone | htargetCurrent
      · have htargetDone' : target ∈ done := hdone'.symm ▸ htargetDone
        obtain ⟨exported, hexported, hgen⟩ := h.completed target targetTy declTargetTy
          htargetMono hdeclTarget htargetDone'
        have he := residual_entries_at htargetMono hexported
        have hne : newEntries[target]? = some (R.onPolyTy exported) := by
          simp only [newEntries, List.getElem?_map, he, Option.map_some, Option.getD_some]
        rw [(List.getElem?_eq_some_iff.mp hne).2]
        have hoe : oldEntries[target]? = some (recStageEntry declPrefixes declDone declPool Xs
            target (.mono declTargetTy)) := by
          simp only [oldEntries, List.getElem?_mapIdx, hdeclTarget, Option.map_some]
        rw [(List.getElem?_eq_some_iff.mp hoe).2]
        simp only [recStageEntry]
        split
        · exact hgen
        · have htLC := hdeclWF.mono_lc declTargetTy (List.mem_of_getElem? hdeclTarget)
          have hannsLen : declAnns.length = declSpecs.length := by
            have heq := congrArg List.length hdeclWF.anns_eq
            simpa only [List.length_map] using heq.symm
          obtain ⟨_, hsub⟩ := hprefix.get hannsLen (List.getElem?_eq_some_iff.mp hdeclTarget).1
          exact hgen.trans ((recScheme_generalizes_genGroup htLC hdeclWF.nodup hsub).trans
            (genGroup_generalizes_rename_mono htLC))
      · have htargetNotDone : target ∉ done := by
          rw [hdone']
          exact residual_not_mem_take hvalidAlgorithm halgorithm' htargetCurrent
        have htargetNotDeclDone : target ∉ declDone :=
          residual_not_mem_take hvalidDecl hdeclComponent (hcontained target htargetCurrent)
        have hex := if_neg htargetNotDone ▸ hframe.mono target targetTy htargetMono
        have he := residual_entries_at htargetMono hex
        have hconnection := h.pending target targetTy declTargetTy htargetMono hdeclTarget htargetNotDone
        have hne : newEntries[target]? = some (PolyTy.mkTrivial (Ty.renameG declPool Xs declTargetTy)) := by
          simp only [newEntries, List.getElem?_map, he, Option.map_some, Option.getD_none,
            RecSpec.monoEntry, Subst.onPolyTy, PolyTy.mkTrivial, hconnection]
        have hoe : oldEntries[target]? = some (PolyTy.mkTrivial (Ty.renameG declPool Xs declTargetTy)) := by
          simp only [oldEntries, List.getElem?_mapIdx, hdeclTarget, Option.map_some, recStageEntry,
            htargetNotDeclDone, if_false]
        rw [(List.getElem?_eq_some_iff.mp hne).2, (List.getElem?_eq_some_iff.mp hoe).2]
        exact PolyTy.Generalizes.refl _
  have hctxEq : R.onCtx (state.rhsCtx ctx) = ⟨newEntries ++ declCtx.env, declCtx.ctors⟩ := by
    have he := congrArg Ctx.env h.ctx_eq
    have hc := congrArg Ctx.ctors h.ctx_eq
    apply congrArg₂ Ctx.mk
    · simpa only [RecState.rhsCtx, Subst.onCtx, Subst.onEnv, List.map_append, newEntries] using
        congrArg (newEntries ++ ·) he
    · simpa only [RecState.rhsCtx, Subst.onCtx] using hc
  rw [hctxEq]
  rw [h.pending member algTy declTy halgTy hdeclTy (by
    rw [hdone']
    exact residual_not_mem_take hvalidAlgorithm halgorithm' hmember)]
  exact htypedNew.scope_restrict (fun v hv => by
    rcases Input.rigidVars_openTyVarsFrom hv with hv | hv
    · exact List.mem_append_left _ (hscope v hv)
    · exact List.mem_append_right _ hv)



/-- Expose a selected pending binding before normalizing its authored prefix. -/
theorem RecResidual.selected_view
    {P G Xs K done : List Nat} {F : List Ty} {base algorithmStage : Nat}
    {declCtx ctx : Ctx} {declSpecs : List RecSpec} {declPrefixes : List (List Nat)}
    {state : RecState} {R : Subst} {anns declAnns : List LetAnn}
    {bindings declBindings : List Input} {declGroups : List (List Nat)} {component : List Nat}
    (h : RecResidual P declCtx declSpecs declPrefixes G Xs ctx state done R)
    (hframe : state.Frame base K F ctx anns done)
    (hbindings : bindings.map Input.erase = declBindings.map Input.erase)
    (hmask : ∀ i,RecGroup.isUnsignedAt (anns.map LetAnn.recModeAnn) i =
      RecGroup.isUnsignedAt (declAnns.map LetAnn.recModeAnn) i)
    (halgorithm : (RecGroup.inferenceSccs (anns.map LetAnn.recModeAnn)
      (bindings.map Input.erase))[algorithmStage]? = some component)
    (hdone : done = ((RecGroup.inferenceSccs (anns.map LetAnn.recModeAnn)
      (bindings.map Input.erase)).take algorithmStage).flatten)
    (hvalidDecl : RecGroups.ValidResidualGroups (declAnns.map LetAnn.recModeAnn)
      (declBindings.map Input.erase) declGroups)
    (hdeclWF : RecSpecs.WF (declAnns.map LetAnn.recModeAnn)
      (declBindings.map Input.erase) declSpecs G)
    (hprefix : RecPrefixesWF declAnns declSpecs declPrefixes G)
    (hfitsDecl : ∀ (stage : Nat) (declComponent : List Nat),declGroups[stage]? = some declComponent →
      ∀ (member : Nat),member ∈ declComponent → ∀ (rhs : Input) (ann : LetAnn) (names : List Nat) (ty : Ty),
      declBindings[member]? = some rhs → declAnns[member]? = some ann →
      declPrefixes[member]? = some names → declSpecs[member]? = some (RecSpec.mono ty) →
      ann.RecFits (recRenameNames G Xs names) (Ty.renameG G Xs ty))
    (hmonoDecl : ∀ (stage : Nat) (declComponent : List Nat),declGroups[stage]? = some declComponent →
      ∀ (member : Nat),member ∈ declComponent → ∀ (rhs : Input) (declTy : Ty),
      declBindings[member]? = some rhs → declSpecs[member]? = some (.mono declTy) →
      Typing (P ++ Xs) (recStageCtx declCtx declSpecs declPrefixes
        (declGroups.take stage).flatten G Xs)
        (rhs.openTyVars (recRenameNames G Xs (declPrefixes[member]?.getD [])))
        (Ty.renameG G Xs declTy))
    (hscope : ∀ rhs ∈ declBindings,∀ v ∈ rhs.rigidVars,v ∈ P)
    (hannEq : anns.map (LetAnn.substTyFvars R) = declAnns)
    (hrhsEq : bindings.map (Input.substTyFvars R) = declBindings)
    {member : Nat} {ann : LetAnn} {rhs : Input} {algTy : Ty}
    (hann : anns[member]? = some ann) (hrhs : bindings[member]? = some rhs)
    (halgTy : state.specs[member]? = some (.mono algTy)) (hmember : member ∈ component) :
    let ownNames := recRenameNames G Xs (declPrefixes[member]?.getD [])
    (ann.substTyFvars R).RecFits ownNames (R.onTy algTy) ∧
      ownNames.length = ann.recPrefixCount ∧
      Typing (P ++ ownNames) (R.onCtx (state.rhsCtx ctx))
        ((rhs.substTyFvars R).openTyVars ownNames) (R.onTy algTy) := by
  have hdeclAnn : declAnns[member]? = some (ann.substTyFvars R) := by
    rw [← hannEq,List.getElem?_map,hann,Option.map_some]
  have hdeclRhs : declBindings[member]? = some (rhs.substTyFvars R) := by
    rw [← hrhsEq,List.getElem?_map,hrhs,Option.map_some]
  have hTyped := h.componentMonoTyped hframe hbindings hmask halgorithm hdone hvalidDecl hdeclWF hprefix
    hmonoDecl hdeclRhs halgTy hmember (hscope _ (List.mem_of_getElem? hdeclRhs))
  refine ⟨?_,?_,hTyped⟩
  · have hschedule : RecGroup.inferenceSccs (anns.map LetAnn.recModeAnn) (bindings.map Input.erase) =
        RecGroup.inferenceSccs (declAnns.map LetAnn.recModeAnn) (declBindings.map Input.erase) := by
      rw [hbindings]
      exact RecGroup.inferenceSccs_congr_mask _ hmask
    have halgorithm' := halgorithm
    rw [hschedule] at halgorithm'
    obtain ⟨declStage,declComponent,hdeclComponent,hcontained⟩ :=
      hvalidDecl.canonical_component_contained halgorithm'
    obtain ⟨declTy,hdeclTy⟩ := h.mono member algTy halgTy
    have hiNames : member < declPrefixes.length := by
      rw [hprefix.length]
      exact (List.getElem?_eq_some_iff.mp hdeclTy).1
    have hNames := List.getElem?_eq_getElem hiNames
    have hFits := hfitsDecl declStage declComponent hdeclComponent member (hcontained member hmember)
      (rhs.substTyFvars R) (ann.substTyFvars R) _ declTy hdeclRhs hdeclAnn hNames hdeclTy
    have hPending := h.pending member algTy declTy halgTy hdeclTy (by
      rw [hdone,hschedule]
      exact residual_not_mem_take (RecGroup.inferenceSccs_valid hvalidDecl.length) halgorithm' hmember)
    simpa only [hPending,hNames,Option.getD_some] using hFits
  · obtain ⟨declTy,hdeclTy⟩ := h.mono member algTy halgTy
    have hiNames : member < declPrefixes.length := by
      rw [hprefix.length]
      exact (List.getElem?_eq_some_iff.mp hdeclTy).1
    have hNames := List.getElem?_eq_getElem hiNames
    simpa only [recRenameNames_length,hNames,Option.getD_some,LetAnn.recPrefixCount_subst_source] using
      (hprefix.member member (ann.substTyFvars R) _ hdeclAnn hNames).1

private theorem RecResidual.onSubst_fields
    {P declPool Xs done : List Nat} {declCtx ctx : Ctx} {declSpecs : List RecSpec}
    {declPrefixes : List (List Nat)} {state : RecState} {R S U : Subst}
    (h : RecResidual P declCtx declSpecs declPrefixes declPool Xs ctx state done R)
    (hU : ∀ pair ∈ U, pair.2.IsLC)
    (hUfix : ∀ p ∈ P, U.onTy (.fvar p) = .fvar p)
    (hctx : R.onCtx ctx = U.onCtx (S.onCtx ctx))
    (hmono : ∀ ty, .mono ty ∈ state.specs → R.onTy ty = U.onTy (S.onTy ty))
    (hpoly : ∀ scheme, .poly scheme ∈ state.specs →
      R.onPolyTy scheme = U.onPolyTy (S.onPolyTy scheme))
    (hexport : ∀ scheme, some scheme ∈ state.exports →
      R.onPolyTy scheme = U.onPolyTy (S.onPolyTy scheme)) :
    RecResidual P declCtx declSpecs declPrefixes declPool Xs (S.onCtx ctx)
      (state.onSubst S) done U := by
  refine ⟨hU, hUfix, hctx.symm.trans h.ctx_eq, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [RecState.onSubst, List.length_map] using h.length
  · intro i algTy hi
    obtain ⟨old, hold, rfl⟩ := RecSpec.mono_getElem?_map_onSubstSource hi
    exact h.mono i old hold
  · intro i algScheme hi
    change (state.specs.map (RecSpec.onSubstSource S))[i]? = some (.poly algScheme) at hi
    rw [List.getElem?_map] at hi
    obtain ⟨spec, hold, heq⟩ := Option.map_eq_some_iff.mp hi
    cases spec with
    | mono ty => cases heq
    | poly scheme =>
      change RecSpec.poly (S.onPolyTy scheme) = RecSpec.poly algScheme at heq
      cases heq
      obtain ⟨declScheme, hdecl, heq⟩ := h.poly i scheme hold
      exact ⟨declScheme, hdecl, (hpoly scheme (List.mem_of_getElem? hold)).symm.trans heq⟩
  · intro i algTy declTy hi hd hnot
    obtain ⟨old, hold, rfl⟩ := RecSpec.mono_getElem?_map_onSubstSource hi
    rw [← hmono old (List.mem_of_getElem? hold)]
    exact h.pending i old declTy hold hd hnot
  · intro i algTy declTy hi hd hdone
    obtain ⟨old, hold, rfl⟩ := RecSpec.mono_getElem?_map_onSubstSource hi
    obtain ⟨exported, he, hgen⟩ := h.completed i old declTy hold hd hdone
    refine ⟨S.onPolyTy exported, ?_, ?_⟩
    · simp only [RecState.onSubst, List.getElem?_map, he, Option.map_some]
    · rw [← hexport exported (List.mem_of_getElem? he)]
      exact hgen

theorem RecResidual.onSubst
    {P declPool Xs done : List Nat} {declCtx ctx : Ctx} {declSpecs : List RecSpec}
    {declPrefixes : List (List Nat)} {state : RecState} {R S U : Subst}
    (h : RecResidual P declCtx declSpecs declPrefixes declPool Xs ctx state done R)
    (hfactor : ∀ ty, R.onTy ty = U.onTy (S.onTy ty))
    (hU : ∀ pair ∈ U, pair.2.IsLC)
    (hUfix : ∀ p ∈ P, U.onTy (.fvar p) = .fvar p) :
    RecResidual P declCtx declSpecs declPrefixes declPool Xs (S.onCtx ctx)
      (state.onSubst S) done U := by
  have hpoly : ∀ scheme : PolyTy, R.onPolyTy scheme = U.onPolyTy (S.onPolyTy scheme) := by
    intro scheme
    exact congrArg (PolyTy.mk scheme.paramCount) (hfactor scheme.body)
  apply h.onSubst_fields hU hUfix ?_ (fun ty _ => hfactor ty)
    (fun scheme _ => hpoly scheme) (fun scheme _ => hpoly scheme)
  apply congrArg₂ Ctx.mk
  · simp only [Subst.onCtx, Subst.onEnv, List.map_map]
    exact List.map_congr_left (fun scheme _ => hpoly scheme)
  · rfl

theorem RecResidual.onSubst_of_agreesBelow
    {P declPool Xs done : List Nat} {declCtx ctx : Ctx} {declSpecs : List RecSpec}
    {declPrefixes : List (List Nat)} {state : RecState} {R S U : Subst} {frontier : Nat}
    (h : RecResidual P declCtx declSpecs declPrefixes declPool Xs ctx state done R)
    (hbelow : state.Below frontier) (hctxBelow : CtxBelow frontier ctx)
    (hfactor : Subst.AgreesBelow frontier R (S ++ U))
    (hU : ∀ pair ∈ U, pair.2.IsLC)
    (hUfix : ∀ p ∈ P, U.onTy (.fvar p) = .fvar p) :
    RecResidual P declCtx declSpecs declPrefixes declPool Xs (S.onCtx ctx)
      (state.onSubst S) done U := by
  have hty : ∀ ty, Ty.BelowFvars frontier ty → R.onTy ty = U.onTy (S.onTy ty) := by
    intro ty hb
    simpa only [Subst.onTy_append] using Subst.onTy_congr hfactor hb
  have hpoly : ∀ scheme : PolyTy, Ty.BelowFvars frontier scheme.body →
      R.onPolyTy scheme = U.onPolyTy (S.onPolyTy scheme) := by
    intro scheme hb
    exact congrArg (PolyTy.mk scheme.paramCount) (hty scheme.body hb)
  apply h.onSubst_fields hU hUfix ?_ (fun ty hm => hty ty (hbelow.1 (.mono ty) hm))
    (fun scheme hm => hpoly scheme (hbelow.1 (.poly scheme) hm))
    (fun scheme hm => hpoly scheme (hbelow.2.2.1 scheme hm))
  simpa only [Subst.onCtx_append] using Subst.onCtx_congr hfactor hctxBelow



/-- Alpha-renaming the independent bound pool leaves the actual residual and
its fixed opening unchanged, including previously exported schemes. -/
theorem RecResidual.rename_decl_pool
    {P G W Xs done : List Nat} {declCtx ctx : Ctx} {declSpecs : List RecSpec}
    {declPrefixes : List (List Nat)} {state : RecState} {R : Subst}
    (h : RecResidual P declCtx declSpecs declPrefixes G Xs ctx state done R)
    (hLC : ∀ spec ∈ declSpecs,spec.LC) (hG : G.Nodup)
    (hprefix : ∀ i,i < declSpecs.length → (declPrefixes[i]?.getD []).Nodup ∧
      ∀ v ∈ declPrefixes[i]?.getD [],v ∈ G)
    (hWlen : W.length = G.length) (hW : W.Nodup) (hXlen : Xs.length = G.length)
    (hGW : ∀ g ∈ G,g ∉ W)
    (hWmono : ∀ ty,.mono ty ∈ declSpecs → ∀ w ∈ W,w ∉ ty.freeVars)
    (hWX : ∀ w ∈ W,w ∉ Xs) (hGX : ∀ g ∈ G,g ∉ Xs)
    (hPoly : ∀ scheme,.poly scheme ∈ declSpecs → ∀ g ∈ G,g ∉ scheme.body.freeVars) :
    RecResidual P declCtx
      (declSpecs.map (RecSpec.onSubstSource (G.zip (W.map Ty.fvar))))
      (declPrefixes.map (recRenameNames G W)) W Xs ctx state done R := by
  have hpolyFix : ∀ scheme,.poly scheme ∈ declSpecs →
      Subst.onPolyTy (G.zip (W.map Ty.fvar)) scheme = scheme := by
    intro scheme hs
    cases scheme with
    | mk count body =>
      apply congrArg (PolyTy.mk count)
      apply Ty.substFvars_eq_self_of_no_key
      intro pair hp hv
      exact hPoly _ hs pair.1 (List.of_mem_zip hp).1 hv
  refine ⟨h.lc,h.fixes,h.ctx_eq,?_,?_,?_,?_,?_⟩
  · simpa only [List.length_map] using h.length
  · intro i algTy hs
    obtain ⟨declTy,hd⟩ := h.mono i algTy hs
    exact ⟨Ty.renameG G W declTy,by simp only [List.getElem?_map,hd,Option.map_some,RecSpec.onSubstSource];rfl⟩
  · intro i algScheme hs
    obtain ⟨declScheme,hd,heq⟩ := h.poly i algScheme hs
    refine ⟨declScheme,?_,heq⟩
    simp only [List.getElem?_map,hd,Option.map_some,RecSpec.onSubstSource,hpolyFix declScheme (List.mem_of_getElem? hd)]
  · intro i algTy declTy hs hd hn
    obtain ⟨oldTy,hold,rfl⟩ := RecSpec.mono_getElem?_map_onSubstSource hd
    change R.onTy algTy = Ty.renameG W Xs (Ty.renameG G W oldTy)
    rw [Ty.renameG_renameG (hLC _ (List.mem_of_getElem? hold)) hG hW hWlen hXlen hGW
      (hWmono oldTy (List.mem_of_getElem? hold)) hWX hGX]
    exact h.pending i algTy oldTy hs hold hn
  · intro i algTy declTy hs hd hi
    obtain ⟨oldTy,hold,rfl⟩ := RecSpec.mono_getElem?_map_onSubstSource hd
    obtain ⟨exported,hex,hgen⟩ := h.completed i algTy oldTy hs hold hi
    refine ⟨exported,hex,?_⟩
    have hprefixEq : (declPrefixes.map (recRenameNames G W))[i]?.getD [] = recRenameNames G W (declPrefixes[i]?.getD []) := by
      rw [List.getElem?_map]
      cases declPrefixes[i]? <;> rfl
    rw [hprefixEq]
    change (R.onPolyTy exported).Generalizes
      (recScheme (recRenameNames G W (declPrefixes[i]?.getD [])) W (Ty.renameG G W oldTy))
    have hp := hprefix i (List.getElem?_eq_some_iff.mp hold).1
    rw [recScheme_rename_pool (hLC _ (List.mem_of_getElem? hold)) hWlen hG hW hGW
      (hWmono oldTy (List.mem_of_getElem? hold)) hp.1 hp.2]
    exact hgen



/-- Changing an internal candidate opening preserves the pending-only residual.
All agreement bounds concern actual state/context types. Candidate assumptions
state only the chosen renaming's exact action and completed-scheme validity. -/
theorem RecResidual.change_opening
    {P P' declPool Xs Ys done : List Nat} {declCtx ctx : Ctx} {declSpecs : List RecSpec}
    {declPrefixes : List (List Nat)} {state : RecState} {R B U : Subst} {frontier : Nat}
    (h : RecResidual P declCtx declSpecs declPrefixes declPool Xs ctx state done R)
    (hbelow : state.Below frontier) (hctxBelow : CtxBelow frontier ctx)
    (hB : ∀ pair ∈ B, pair.2.IsLC)
    (hBctx : B.onCtx declCtx = declCtx)
    (hBpoly : ∀ scheme, .poly scheme ∈ declSpecs → B.onPolyTy scheme = scheme)
    (hCompletedWF : ∀ i ty, declSpecs[i]? = some (.mono ty) → i ∈ done →
      (recScheme (declPrefixes[i]?.getD []) declPool ty).WF)
    (hBcompleted : ∀ i ty, declSpecs[i]? = some (.mono ty) → i ∈ done →
      B.onPolyTy (recScheme (declPrefixes[i]?.getD []) declPool ty) =
        recScheme (declPrefixes[i]?.getD []) declPool ty)
    (hBmono : ∀ ty, .mono ty ∈ declSpecs →
      B.onTy (Ty.renameG declPool Xs ty) = Ty.renameG declPool Ys ty)
    (hU : ∀ pair ∈ U, pair.2.IsLC)
    (hUfix : ∀ p ∈ P', U.onTy (.fvar p) = .fvar p)
    (hagrees : Subst.AgreesBelow frontier (R ++ B) U) :
    RecResidual P' declCtx declSpecs declPrefixes declPool Ys ctx state done U := by
  have hty : ∀ ty, Ty.BelowFvars frontier ty → U.onTy ty = B.onTy (R.onTy ty) := by
    intro ty hb
    simpa only [Subst.onTy_append] using (Subst.onTy_congr hagrees hb).symm
  have hpoly : ∀ scheme : PolyTy, Ty.BelowFvars frontier scheme.body →
      U.onPolyTy scheme = B.onPolyTy (R.onPolyTy scheme) := by
    intro scheme hb
    exact congrArg (PolyTy.mk scheme.paramCount) (hty scheme.body hb)
  refine ⟨hU, hUfix, ?_, h.length, h.mono, ?_, ?_, ?_⟩
  · have he := (Subst.onCtx_congr hagrees hctxBelow).symm
    simpa only [Subst.onCtx_append, h.ctx_eq, hBctx] using he
  · intro i algScheme hi
    obtain ⟨declScheme, hd, he⟩ := h.poly i algScheme hi
    refine ⟨declScheme, hd, ?_⟩
    rw [hpoly algScheme (hbelow.1 (.poly algScheme) (List.mem_of_getElem? hi)), he]
    exact hBpoly declScheme (List.mem_of_getElem? hd)
  · intro i algTy declTy hi hd hnot
    rw [hty algTy (hbelow.1 (.mono algTy) (List.mem_of_getElem? hi)),
      h.pending i algTy declTy hi hd hnot]
    exact hBmono declTy (List.mem_of_getElem? hd)
  · intro i algTy declTy hi hd hdone
    obtain ⟨exported, he, hgen⟩ := h.completed i algTy declTy hi hd hdone
    refine ⟨exported, he, ?_⟩
    rw [hpoly exported (hbelow.2.2.1 exported (List.mem_of_getElem? he))]
    have hg := hgen.onSubst (hCompletedWF i declTy hd hdone) hB
    rwa [hBcompleted i declTy hd hdone] at hg




private theorem residual_export_selected {state : RecState} {members pool : List Nat}
    {written : List (List Nat)} {outputs : List (Option Expr)} {facts : List RecFacts}
    {i : Nat} {ty : Ty} (hbound : i < state.exports.length) (hi : i ∈ members)
    (hs : state.specs[i]? = some (.mono ty)) :
    (state.exportComponent members written pool outputs facts).exports[i]? =
      some (some (recScheme (written[i]?.getD []) pool ty)) := by
  have he := List.getElem?_eq_getElem hbound
  simp only [RecState.exportComponent, List.getElem?_mapIdx, he, Option.map_some,
    if_pos hi, hs, bind, pure, Option.bind_some, RecSpec.completedScheme]

private theorem residual_export_untouched {state : RecState} {members pool : List Nat}
    {written : List (List Nat)} {outputs : List (Option Expr)} {facts : List RecFacts}
    {i : Nat} (hi : i ∉ members) :
    (state.exportComponent members written pool outputs facts).exports[i]? = state.exports[i]? := by
  simp only [RecState.exportComponent, List.getElem?_mapIdx]
  cases state.exports[i]? <;> simp only [Option.map_none, Option.map_some, if_neg hi]

theorem RecResidual.exportComponent
    {P declPool Xs done members pool : List Nat} {declCtx ctx : Ctx} {declSpecs : List RecSpec}
    {declPrefixes written : List (List Nat)} {state : RecState} {R : Subst}
    {outputs : List (Option Expr)} {facts : List RecFacts}
    (h : RecResidual P declCtx declSpecs declPrefixes declPool Xs ctx state done R)
    (hdisjoint : ∀ i ∈ members, i ∉ done)
    (hwrite : ∀ i ty, state.specs[i]? = some (.mono ty) → i ∈ members → i < state.exports.length)
    (hgeneralizes : ∀ i algTy declTy, state.specs[i]? = some (.mono algTy) →
      declSpecs[i]? = some (.mono declTy) → i ∈ members →
      (R.onPolyTy (recScheme (written[i]?.getD []) pool algTy)).Generalizes
        (recScheme (declPrefixes[i]?.getD []) declPool declTy)) :
    RecResidual P declCtx declSpecs declPrefixes declPool Xs ctx
      (state.exportComponent members written pool outputs facts) (done ++ members) R := by
  refine ⟨h.lc, h.fixes, h.ctx_eq, h.length, h.mono, h.poly, ?_, ?_⟩
  · intro i algTy declTy hi hd hnot
    exact h.pending i algTy declTy hi hd (fun hc => hnot (List.mem_append_left _ hc))
  · intro i algTy declTy hi hd hdone
    rcases List.mem_append.mp hdone with hold | hnew
    · obtain ⟨exported, he, hg⟩ := h.completed i algTy declTy hi hd hold
      exact ⟨exported, (residual_export_untouched (fun hm => hdisjoint i hm hold)).trans he, hg⟩
    · exact ⟨recScheme (written[i]?.getD []) pool algTy,
        residual_export_selected (hwrite i algTy hi hnew) hnew hi,
        hgeneralizes i algTy declTy hi hd hnew⟩

theorem RecResidual.afterFinish
    {P declPool Xs done members K soft : List Nat} {declCtx ctx : Ctx} {declSpecs : List RecSpec}
    {declPrefixes : List (List Nat)} {state final : RecState} {R : Subst}
    {outputs : List (Option Expr)} {facts : List RecFacts}
    (h : RecResidual P declCtx declSpecs declPrefixes declPool Xs ctx state done R)
    (hfinish : FinishRecComponent K soft members ctx state outputs facts final)
    (hdisjoint : ∀ i ∈ members, i ∉ done)
    (hexports : state.exports.length = state.specs.length)
    (hAlgLC : ∀ i ty, state.specs[i]? = some (.mono ty) → i ∈ members → ty.IsLC)
    (hDeclLC : ∀ i ty, declSpecs[i]? = some (.mono ty) → i ∈ members → ty.IsLC)
    (hPool : declPool.Nodup)
    (hWritten : ∀ i ty, declSpecs[i]? = some (.mono ty) → i ∈ members →
      (declPrefixes[i]?.getD []).Nodup ∧ ∀ v ∈ declPrefixes[i]?.getD [], v ∈ declPool)
    (hLen : Xs.length = declPool.length) (hXs : Xs.Nodup)
    (hDisjoint : ∀ g ∈ declPool, g ∉ Xs)
    (hFreshTy : ∀ i ty, declSpecs[i]? = some (.mono ty) → i ∈ members →
      ∀ x ∈ Xs, x ∉ ty.freeVars)
    (hFreshExport : ∀ i scheme, i ∈ members → final.exports[i]? = some (some scheme) →
      ∀ x ∈ Xs, x ∉ (R.onPolyTy scheme).body.freeVars) :
    RecResidual P declCtx declSpecs declPrefixes declPool Xs ctx final (done ++ members) R := by
  cases hfinish with
  | @mk written hresolve =>
    apply h.exportComponent hdisjoint
      (fun i ty hi _ => hexports.symm ▸ (List.getElem?_eq_some_iff.mp hi).1)
    intro i algTy declTy hi hd hm
    obtain ⟨hwnd, hwsub⟩ := hWritten i declTy hd hm
    apply recScheme_generalizes_of_renameG (hAlgLC i algTy hi hm) (hDeclLC i declTy hd hm)
      h.lc hPool hwnd hwsub hLen hXs hDisjoint (hFreshTy i declTy hd hm)
      (h.pending i algTy declTy hi hd (hdisjoint i hm))
    exact hFreshExport i _ hm (residual_export_selected
      (hexports.symm ▸ (List.getElem?_eq_some_iff.mp hi).1) hm hi)



 theorem Ty.renameG_onSubst_pool_safe {G Xs : List Nat} {S : Subst} {ty : Ty}
    (hLC : ty.IsLC) (hS : ∀ p ∈ S,p.2.IsLC) (hG : G.Nodup)
    (hLen : Xs.length = G.length) (hGX : ∀ g ∈ G,g ∉ Xs)
    (hDomG : ∀ p ∈ S,p.1 ∉ G) (hRanG : ∀ p ∈ S,∀ v ∈ p.2.freeVars,v ∉ G)
    (hDomX : ∀ p ∈ S,p.1 ∉ Xs) :
    S.onTy (Ty.renameG G Xs ty) = Ty.renameG G Xs (S.onTy ty) := by
  induction S generalizing ty with
  | nil => rfl
  | cons p rest ih =>
    obtain ⟨key,value⟩ := p
    have hval := hS (key,value) List.mem_cons_self
    change Subst.onTy rest (Ty.substFvar key value (Ty.renameG G Xs ty)) =
      Ty.renameG G Xs (Subst.onTy rest (Ty.substFvar key value ty))
    rw [←Ty.renameG_substFvar_comm hval (hDomG _ List.mem_cons_self)
      (hRanG _ List.mem_cons_self) (hDomX _ List.mem_cons_self) hLC hG hLen hGX]
    exact ih (Ty.IsLC.substFvar hval hLC)
      (fun p hp => hS p (List.mem_cons_of_mem _ hp))
      (fun p hp => hDomG p (List.mem_cons_of_mem _ hp))
      (fun p hp => hRanG p (List.mem_cons_of_mem _ hp))
      (fun p hp => hDomX p (List.mem_cons_of_mem _ hp))

/-- Move only independent candidate data through a pool-safe substitution.
The actual state and the chosen candidate pool opening stay literal. -/
theorem RecResidual.onSubst_decl
    {P G Xs done : List Nat} {declCtx ctx : Ctx} {declSpecs : List RecSpec}
    {declPrefixes : List (List Nat)} {state : RecState} {R moved D : Subst} {N : Nat}
    (h : RecResidual P declCtx declSpecs declPrefixes G Xs ctx state done R)
    (hctx : CtxBelow N ctx) (hstate : state.Below N)
    (hLC : ∀ spec ∈ declSpecs,spec.LC)
    (hG : G.Nodup) (hLen : Xs.length = G.length) (hGX : ∀ g ∈ G,g ∉ Xs)
    (hprefix : ∀ i,i < declSpecs.length → ∀ v ∈ declPrefixes[i]?.getD [],v ∈ G)
    (hD : ∀ p ∈ D,p.2.IsLC)
    (hDomG : ∀ p ∈ D,p.1 ∉ G) (hRanG : ∀ p ∈ D,∀ v ∈ p.2.freeVars,v ∉ G)
    (hDomX : ∀ p ∈ D,p.1 ∉ Xs)
    (hMoved : ∀ p ∈ moved,p.2.IsLC) (hP : ∀ p ∈ P,p < N)
    (hDP : ∀ p ∈ P,D.onTy (.fvar p) = .fvar p)
    (hAgree : Subst.AgreesBelow N moved (R ++ D)) :
    RecResidual P (D.onCtx declCtx) (declSpecs.map (RecSpec.onSubstSource D))
      declPrefixes G Xs ctx state done moved := by
  have hty : ∀ ty,Ty.BelowFvars N ty → moved.onTy ty = D.onTy (R.onTy ty) := by
    intro ty hb
    simpa only [Subst.onTy_append] using Subst.onTy_congr hAgree hb
  have hpoly : ∀ M,Ty.BelowFvars N M.body → moved.onPolyTy M = D.onPolyTy (R.onPolyTy M) := by
    intro M hb
    exact congrArg (PolyTy.mk M.paramCount) (hty M.body hb)
  refine ⟨hMoved,?_,?_,?_,?_,?_,?_,?_⟩
  · intro p hp
    rw [hty (.fvar p) (.fvar (hP p hp)),h.fixes p hp,hDP p hp]
  · have hh := Subst.onCtx_congr hAgree hctx
    rw [Subst.onCtx_append,h.ctx_eq] at hh
    exact hh
  · simpa only [List.length_map] using h.length
  · intro i algTy hs
    obtain ⟨declTy,hd⟩ := h.mono i algTy hs
    exact ⟨D.onTy declTy,by simp only [List.getElem?_map,hd,Option.map_some,RecSpec.onSubstSource]⟩
  · intro i algScheme hs
    obtain ⟨declScheme,hd,heq⟩ := h.poly i algScheme hs
    refine ⟨D.onPolyTy declScheme,?_,?_⟩
    · simp only [List.getElem?_map,hd,Option.map_some,RecSpec.onSubstSource]
    · rw [hpoly algScheme (hstate.1 _ (List.mem_of_getElem? hs)),heq]
  · intro i algTy declTy hs hd hn
    obtain ⟨oldTy,hold,rfl⟩ := RecSpec.mono_getElem?_map_onSubstSource hd
    rw [hty algTy (hstate.1 _ (List.mem_of_getElem? hs)),h.pending i algTy oldTy hs hold hn,
      Ty.renameG_onSubst_pool_safe (hLC _ (List.mem_of_getElem? hold)) hD hG hLen hGX hDomG hRanG hDomX]
  · intro i algTy declTy hs hd hi
    obtain ⟨oldTy,hold,rfl⟩ := RecSpec.mono_getElem?_map_onSubstSource hd
    obtain ⟨exported,hex,hgen⟩ := h.completed i algTy oldTy hs hold hi
    refine ⟨exported,hex,?_⟩
    rw [hpoly exported (hstate.2.2.1 exported (List.mem_of_getElem? hex))]
    rw [recScheme_subst_pool_avoid hDomG hRanG (hprefix i (List.getElem?_eq_some_iff.mp hold).1)]
    exact hgen.onSubst (recScheme_wf (hLC _ (List.mem_of_getElem? hold))) hD

/-- Restore a later residual after candidate-only movement. No bounds on the
later actual state are required: the inverse acts after its residual. -/
theorem RecResidual.restore_decl
    {P G Xs done : List Nat} {declCtx ctx : Ctx} {declSpecs : List RecSpec}
    {declPrefixes : List (List Nat)} {state : RecState} {R D back : Subst}
    (h : RecResidual P (D.onCtx declCtx) (declSpecs.map (RecSpec.onSubstSource D))
      declPrefixes G Xs ctx state done R)
    (hLC : ∀ spec ∈ declSpecs,spec.LC)
    (hG : G.Nodup) (hLen : Xs.length = G.length) (hGX : ∀ g ∈ G,g ∉ Xs)
    (hprefix : ∀ i,i < declSpecs.length → ∀ v ∈ declPrefixes[i]?.getD [],v ∈ G)
    (hD : ∀ p ∈ D,p.2.IsLC) (hBack : ∀ p ∈ back,p.2.IsLC)
    (hDomG : ∀ p ∈ back,p.1 ∉ G) (hRanG : ∀ p ∈ back,∀ v ∈ p.2.freeVars,v ∉ G)
    (hDomX : ∀ p ∈ back,p.1 ∉ Xs)
    (hBackP : ∀ p ∈ P,back.onTy (.fvar p) = .fvar p)
    (hCtxRestore : back.onCtx (D.onCtx declCtx) = declCtx)
    (hMonoRestore : ∀ ty,.mono ty ∈ declSpecs → back.onTy (D.onTy ty) = ty)
    (hPolyRestore : ∀ M,.poly M ∈ declSpecs → back.onPolyTy (D.onPolyTy M) = M) :
    RecResidual P declCtx declSpecs declPrefixes G Xs ctx state done (R ++ back) := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_⟩
  · intro p hp
    exact (List.mem_append.mp hp).elim (h.lc p) (hBack p)
  · intro p hp
    rw [Subst.onTy_append,h.fixes p hp,hBackP p hp]
  · rw [Subst.onCtx_append,h.ctx_eq,hCtxRestore]
  · simpa only [List.length_map] using h.length
  · intro i algTy hs
    obtain ⟨declTy,hd⟩ := h.mono i algTy hs
    obtain ⟨oldTy,hold,_⟩ := RecSpec.mono_getElem?_map_onSubstSource hd
    exact ⟨oldTy,hold⟩
  · intro i algScheme hs
    obtain ⟨declScheme,hd,heq⟩ := h.poly i algScheme hs
    rw [List.getElem?_map] at hd
    obtain ⟨spec,hold,he⟩ := Option.map_eq_some_iff.mp hd
    cases spec with
    | mono ty => cases he
    | poly M =>
      cases RecSpec.poly.inj he
      refine ⟨M,hold,?_⟩
      rw [Subst.onPolyTy_append,heq,hPolyRestore M (List.mem_of_getElem? hold)]
  · intro i algTy declTy hs hd hn
    have hnew : (declSpecs.map (RecSpec.onSubstSource D))[i]? = some (.mono (D.onTy declTy)) := by
      simp only [List.getElem?_map,hd,Option.map_some,RecSpec.onSubstSource]
    have hh := h.pending i algTy (D.onTy declTy) hs hnew hn
    rw [Subst.onTy_append,hh,
      Ty.renameG_onSubst_pool_safe (Subst.onTy_lc hD (hLC _ (List.mem_of_getElem? hd))) hBack hG hLen hGX hDomG hRanG hDomX,
      hMonoRestore declTy (List.mem_of_getElem? hd)]
  · intro i algTy declTy hs hd hi
    have hnew : (declSpecs.map (RecSpec.onSubstSource D))[i]? = some (.mono (D.onTy declTy)) := by
      simp only [List.getElem?_map,hd,Option.map_some,RecSpec.onSubstSource]
    obtain ⟨exported,hex,hgen⟩ := h.completed i algTy (D.onTy declTy) hs hnew hi
    refine ⟨exported,hex,?_⟩
    have hrestored := hgen.onSubst
      (recScheme_wf (Subst.onTy_lc hD (hLC _ (List.mem_of_getElem? hd)))) hBack
    rw [←recScheme_subst_pool_avoid hDomG hRanG (hprefix i (List.getElem?_eq_some_iff.mp hd).1),
      hMonoRestore declTy (List.mem_of_getElem? hd)] at hrestored
    simpa only [Subst.onPolyTy_append] using hrestored

/-- Dodge a finite allocation block in the independent candidate. The only
block-avoidance premise concerns internally chosen pool names and openings. -/
theorem RecResidual.dodge
    {P G Xs done : List Nat} {declCtx ctx : Ctx} {declSpecs : List RecSpec}
    {declPrefixes : List (List Nat)} {state : RecState} {R : Subst}
    (h : RecResidual P declCtx declSpecs declPrefixes G Xs ctx state done R)
    (N count : Nat) (targets : List Ty) (avoid : List Nat)
    (hctx : CtxBelow N ctx) (hstate : state.Below N) (hP : ∀ p ∈ P,p < N)
    (hLC : ∀ spec ∈ declSpecs,spec.LC)
    (hG : G.Nodup) (hLen : Xs.length = G.length) (hGX : ∀ g ∈ G,g ∉ Xs)
    (hprefix : ∀ i,i < declSpecs.length → ∀ v ∈ declPrefixes[i]?.getD [],v ∈ G)
    (hPoolBlock : ∀ v ∈ G ++ Xs,v ∉ freshVars N count) :
    ∃ W,N+count ≤ W ∧ (∀ v ∈ G ++ Xs ++ avoid,v < W) ∧
      let forward := blockList N W count
      let backward := blockListBack N W count
      let moved := Subst.conj (blockSwap N W count) R
      let allTargets := declCtx.env.map PolyTy.body ++
        declSpecs.map (fun spec => spec.monoEntry.body) ++
        (recCompletedSchemes declSpecs declPrefixes G).map PolyTy.body ++ targets
      RecResidual P (forward.onCtx declCtx) (declSpecs.map (RecSpec.onSubstSource forward))
        declPrefixes G Xs ctx state done moved ∧
      (∀ p ∈ P ++ freshVars N count,moved.onTy (.fvar p) = .fvar p) ∧
      (∀ pair ∈ forward,pair.2.IsLC) ∧ (∀ pair ∈ backward,pair.2.IsLC) ∧
      (∀ v ∈ G ++ Xs,forward.onTy (.fvar v) = .fvar v ∧ backward.onTy (.fvar v) = .fvar v) ∧
      (∀ ty,Ty.BelowFvars N ty → moved.onTy ty = forward.onTy (R.onTy ty)) ∧
      (∀ ty,Ty.BelowFvars N ty → backward.onTy (moved.onTy ty) = R.onTy ty) ∧
      (∀ ty ∈ allTargets,backward.onTy (forward.onTy ty) = ty ∧
        ∀ y ∈ freshVars N count,y ∉ (forward.onTy ty).freeVars) ∧
      (∀ (laterCtx : Ctx) (laterState : RecState) (laterDone : List Nat) (laterR : Subst),
        RecResidual P (forward.onCtx declCtx) (declSpecs.map (RecSpec.onSubstSource forward))
          declPrefixes G Xs laterCtx laterState laterDone laterR →
        RecResidual P declCtx declSpecs declPrefixes G Xs laterCtx laterState laterDone (laterR ++ backward)) := by
  let allTargets := declCtx.env.map PolyTy.body ++ declSpecs.map (fun spec => spec.monoEntry.body) ++
    (recCompletedSchemes declSpecs declPrefixes G).map PolyTy.body ++ targets
  obtain ⟨W,hW,hAvoid,hMoved,hBlock,hBelow,hForward,hBackward,hTargets⟩ :=
    signed_candidate_dodge R h.lc N count allTargets (G ++ Xs ++ avoid)
  let forward := blockList N W count
  let backward := blockListBack N W count
  let moved := Subst.conj (blockSwap N W count) R
  have hFLC := blockList_lc N W count
  have hBLC := blockListBack_lc N W count
  have hScratch : ∀ v ∈ G ++ Xs,v ∉ freshVars W count := by
    intro v hv hw
    have hh := hAvoid v (List.mem_append_left _ hv)
    have := freshVars_ge v hw
    omega
  have hFDom : ∀ pair ∈ forward,pair.1 ∉ G ++ Xs := by
    intro pair hp hv
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hp
    exact hPoolBlock _ hv (List.mem_map.mpr ⟨i,hi,rfl⟩)
  have hBDom : ∀ pair ∈ backward,pair.1 ∉ G ++ Xs := by
    intro pair hp hv
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hp
    exact hScratch _ hv (List.mem_map.mpr ⟨i,hi,rfl⟩)
  have hFRan : ∀ pair ∈ forward,∀ v ∈ pair.2.freeVars,v ∉ G := by
    intro pair hp v hv hg
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hp
    have heq : v = W+i := List.mem_singleton.mp hv
    subst v
    exact hScratch _ (List.mem_append_left _ hg) (List.mem_map.mpr ⟨i,hi,rfl⟩)
  have hBRan : ∀ pair ∈ backward,∀ v ∈ pair.2.freeVars,v ∉ G := by
    intro pair hp v hv hg
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hp
    have heq : v = N+i := List.mem_singleton.mp hv
    subst v
    exact hPoolBlock _ (List.mem_append_left _ hg) (List.mem_map.mpr ⟨i,hi,rfl⟩)
  have hFP : ∀ p ∈ P,forward.onTy (.fvar p) = .fvar p := fun p hp => (hBelow p (hP p hp)).1
  have hBP : ∀ p ∈ P,backward.onTy (.fvar p) = .fvar p := fun p hp => (hBelow p (hP p hp)).2
  have hAgree : Subst.AgreesBelow N moved (R ++ forward) := by
    intro v hv
    simpa only [Subst.onTy_append] using hForward (.fvar v) (.fvar hv)
  have hMovedRec := h.onSubst_decl hctx hstate hLC hG hLen hGX hprefix hFLC
    (fun pair hp hg => hFDom pair hp (List.mem_append_left _ hg)) hFRan
    (fun pair hp hx => hFDom pair hp (List.mem_append_right _ hx)) hMoved hP hFP hAgree
  have hCtxRound : backward.onCtx (forward.onCtx declCtx) = declCtx := by
    apply congrArg₂ Ctx.mk
    · change List.map _ (List.map _ declCtx.env) = declCtx.env
      rw [List.map_map]
      calc
        _ = declCtx.env.map id := List.map_congr_left (by
          intro M hm
          apply congrArg (PolyTy.mk M.paramCount)
          exact (hTargets M.body (by
            dsimp only [allTargets]
            exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
              (List.mem_map.mpr ⟨M,hm,rfl⟩))))).1)
        _ = _ := List.map_id _
    · rfl
  have hMonoRound : ∀ ty,.mono ty ∈ declSpecs → backward.onTy (forward.onTy ty) = ty := by
    intro ty ht
    exact (hTargets ty (by
      dsimp only [allTargets]
      exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _
        (List.mem_map.mpr ⟨.mono ty,ht,rfl⟩))))).1
  have hPolyRound : ∀ M,.poly M ∈ declSpecs → backward.onPolyTy (forward.onPolyTy M) = M := by
    intro M ht
    apply congrArg (PolyTy.mk M.paramCount)
    exact (hTargets M.body (by
      dsimp only [allTargets]
      exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _
        (List.mem_map.mpr ⟨.poly M,ht,rfl⟩))))).1
  refine ⟨W,hW,hAvoid,hMovedRec,?_,hFLC,hBLC,?_,hForward,hBackward,hTargets,?_⟩
  · intro p hp
    rcases List.mem_append.mp hp with hp | hp
    · rw [hForward (.fvar p) (.fvar (hP p hp)),h.fixes p hp,hFP p hp]
    · exact hBlock p hp
  · intro v hv
    exact ⟨Subst.fixes_of_dom_avoids hFDom v hv,Subst.fixes_of_dom_avoids hBDom v hv⟩
  · intro laterCtx laterState laterDone laterR hr
    exact hr.restore_decl hLC hG hLen hGX hprefix hFLC hBLC
      (fun pair hp hg => hBDom pair hp (List.mem_append_left _ hg)) hBRan
      (fun pair hp hx => hBDom pair hp (List.mem_append_right _ hx)) hBP hCtxRound hMonoRound hPolyRound

/-- Restoring a moved candidate acts after the algorithm's solved substitution. -/
theorem _root_.Subst.AgreesBelow.restore_after {N : Nat} {ambient moved solved residual back : Subst}
    (h : Subst.AgreesBelow N moved (solved ++ residual))
    (hBack : ∀ v,v < N → back.onTy (moved.onTy (.fvar v)) = ambient.onTy (.fvar v)) :
    Subst.AgreesBelow N ambient (solved ++ (residual ++ back)) := by
  intro v hv
  rw [←hBack v hv,h v hv]
  simp only [Subst.onTy_append]


 theorem zip_fvars_fixes {names targets : List Nat} (hv : v ∉ names) :
    Subst.onTy (names.zip (targets.map Ty.fvar)) (.fvar v) = .fvar v := by
  apply Ty.substFvars_eq_self_of_no_key
  intro pair hp hk
  exact hv ((List.mem_singleton.mp hk) ▸ (List.of_mem_zip hp).1)

 theorem zip_fvars_roundtrip {names targets : List Nat} {ty : Ty}
    (hlen : targets.length = names.length) (hnd : names.Nodup) (htnd : targets.Nodup)
    (hdisj : ∀ n ∈ names, n ∉ targets) (havoid : ∀ t ∈ targets, t ∉ ty.freeVars) :
    Subst.onTy (targets.zip (names.map Ty.fvar))
      (Subst.onTy (names.zip (targets.map Ty.fvar)) ty) = ty := by
  rw [← Subst.onTy_append]
  apply Subst.onTy_eq_self_of_fixes
  intro v hv
  rw [Subst.onTy_append]
  by_cases hn : v ∈ names
  · have hi : names.idxOf v < names.length := List.idxOf_lt_length_iff.mpr hn
    have ht : names.idxOf v < targets.length := by omega
    have hnget : names[names.idxOf v]? = some v := List.getElem?_idxOf hn
    have htget := List.getElem?_eq_getElem ht
    rw [show Subst.onTy (names.zip (targets.map Ty.fvar)) (.fvar v) =
        .fvar targets[names.idxOf v] from Ty.substFvars_zip_fvar_renameG hlen hnd hdisj hnget htget]
    exact Ty.substFvars_zip_fvar_renameG hlen.symm htnd
      (fun t ht hn => hdisj t hn ht) htget hnget
  · rw [zip_fvars_fixes hn]
    exact zip_fvars_fixes (fun ht => havoid v ht hv)
 theorem zip_fvars_lc {names targets : List Nat} :
    ∀ pair ∈ names.zip (targets.map Ty.fvar), pair.2.IsLC := by
  intro pair hp
  obtain ⟨v, _, heq⟩ := List.mem_map.mp (List.of_mem_zip hp).2
  rw [← heq]
  exact .fvar

 theorem Typing.rename_prefixes {P names targets : List Nat}
    (h : Typing (P ++ names) ctx input ty)
    (hlen : targets.length = names.length) (hnd : names.Nodup)
    (hdisj : ∀ n ∈ names, n ∉ targets) (hP : ∀ p ∈ P, p ∉ names) :
    Typing (P ++ targets) (Subst.onCtx (names.zip (targets.map Ty.fvar)) ctx)
      (input.substTyFvars (names.zip (targets.map Ty.fvar)))
      (Subst.onTy (names.zip (targets.map Ty.fvar)) ty) := by
  apply h.onSubst_source _ zip_fvars_lc
  intro k hk v hv
  rcases List.mem_append.mp hk with hk | hk
  · rw [zip_fvars_fixes (hP k hk)] at hv
    exact List.mem_append_left _ ((List.mem_singleton.mp hv) ▸ hk)
  · have hi : names.idxOf k < names.length := List.idxOf_lt_length_iff.mpr hk
    have ht : names.idxOf k < targets.length := by omega
    have he := Ty.substFvars_zip_fvar_renameG hlen hnd hdisj
      (List.getElem?_idxOf hk) (List.getElem?_eq_getElem ht)
    change v ∈ (Ty.substFvars (names.zip (targets.map Ty.fvar)) (.fvar k)).freeVars at hv
    rw [he] at hv
    exact List.mem_append_right _ ((List.mem_singleton.mp hv) ▸ List.getElem_mem ht)

 theorem Input.rename_prefixes_roundtrip {input : Input} {names targets : List Nat}
    (hlen : targets.length = names.length) (hnd : names.Nodup) (htnd : targets.Nodup)
    (hdisj : ∀ n ∈ names, n ∉ targets) (havoid : ∀ t ∈ targets, t ∉ input.rigidVars) :
    (input.substTyFvars (names.zip (targets.map Ty.fvar))).substTyFvars
      (targets.zip (names.map Ty.fvar)) = input := by
  rw [← input.substTyFvars_append]
  apply input.substTyFvars_eq_self_of_fixes
  intro v hv
  change Subst.onTy (names.zip (targets.map Ty.fvar) ++ targets.zip (names.map Ty.fvar)) (.fvar v) = .fvar v
  rw [Subst.onTy_append]
  exact zip_fvars_roundtrip hlen hnd htnd hdisj (by
    intro t ht hm
    exact havoid t ht ((List.mem_singleton.mp hm) ▸ hv))

 theorem Ctx.rename_prefixes_roundtrip {ctx : Ctx} {names targets : List Nat}
    (hlen : targets.length = names.length) (hnd : names.Nodup) (htnd : targets.Nodup)
    (hdisj : ∀ n ∈ names, n ∉ targets) (havoid : ∀ t ∈ targets, t ∉ ctx.env.freeVars) :
    Subst.onCtx (targets.zip (names.map Ty.fvar)) (Subst.onCtx (names.zip (targets.map Ty.fvar)) ctx) = ctx := by
  apply congrArg₂ Ctx.mk
  · change List.map _ (List.map _ ctx.env) = ctx.env
    rw [List.map_map]
    have hh : ∀ M ∈ ctx.env,
        Subst.onPolyTy (targets.zip (names.map Ty.fvar)) (Subst.onPolyTy (names.zip (targets.map Ty.fvar)) M) = M := by
      intro M hm
      apply congrArg (PolyTy.mk M.paramCount)
      exact zip_fvars_roundtrip hlen hnd htnd hdisj (fun t ht hv =>
        havoid t ht (Env.mem_freeVars_iff.mpr ⟨M, hm, hv⟩))
    calc
      _ = ctx.env.map id := List.map_congr_left hh
      _ = _ := List.map_id _
  · rfl
 theorem zip_fvars_on_rename {names targets : List Nat}
    (hlen : targets.length = names.length) (hnd : names.Nodup)
    (hdisj : ∀ n ∈ names, n ∉ targets) (v : Nat) :
    Subst.onTy (names.zip (targets.map Ty.fvar)) (.fvar v) =
      .fvar ((targets[names.idxOf v]?).getD v) := by
  by_cases hv : v ∈ names
  · have hi : names.idxOf v < targets.length := by
      have := List.idxOf_lt_length_iff.mpr hv
      omega
    rw [List.getElem?_eq_getElem hi, Option.getD_some]
    exact Ty.substFvars_zip_fvar_renameG hlen hnd hdisj (List.getElem?_idxOf hv) (List.getElem?_eq_getElem hi)
  · have hi : targets.length ≤ names.idxOf v := by
      have hn : ¬ names.idxOf v < names.length := fun h => hv (List.idxOf_lt_length_iff.mp h)
      omega
    rw [List.getElem?_eq_none_iff.mpr hi, Option.getD_none]
    exact zip_fvars_fixes hv

 theorem zip_fvars_images {names targets Xs : List Nat}
    (hlen : targets.length = names.length) (hnd : names.Nodup)
    (hdisj : ∀ n ∈ names, n ∉ targets) :
    Xs.map (fun x => Subst.onTy (names.zip (targets.map Ty.fvar)) (.fvar x)) =
      (recRenameNames names targets Xs).map Ty.fvar := by
  simp only [recRenameNames, List.map_map, Function.comp_def]
  exact List.map_congr_left (fun x _ => zip_fvars_on_rename hlen hnd hdisj x)

 theorem recRenameNames_mem_source_or_target {names targets Xs : List Nat}
    (hv : v ∈ recRenameNames names targets Xs) : v ∈ Xs ∨ v ∈ targets := by
  obtain ⟨x, hx, heq⟩ := List.mem_map.mp hv
  cases ht : targets[names.idxOf x]? with
  | none => simp only [ht, Option.getD_none] at heq; exact .inl (heq ▸ hx)
  | some target =>
      simp only [ht, Option.getD_some] at heq
      exact .inr (heq ▸ List.mem_of_getElem? ht)

 theorem zip_fvars_renameG {names targets G Xs : List Nat} {ty : Ty}
    (hlen : targets.length = names.length) (hnd : names.Nodup)
    (hdisj : ∀ n ∈ names, n ∉ targets)
    (hlc : ty.IsLC) (hG : G.Nodup) (hXs : Xs.length = G.length)
    (hGX : ∀ g ∈ G, g ∉ Xs) (hGT : ∀ g ∈ G, g ∉ targets)
    (hnTy : ∀ n ∈ names, n ∉ ty.freeVars) :
    Subst.onTy (names.zip (targets.map Ty.fvar)) (Ty.renameG G Xs ty) =
      Ty.renameG G (recRenameNames names targets Xs) ty := by
  have hfix : Subst.onTy (names.zip (targets.map Ty.fvar)) (Ty.closeOver G ty) = Ty.closeOver G ty := by
    apply Subst.onTy_eq_self_of_fixes
    intro v hv
    exact zip_fvars_fixes (fun hn => hnTy v hn (Ty.freeVars_closeOver_subset hv))
  have hopen : Ty.renameG G Xs ty = Ty.openVars Xs (Ty.closeOver G ty) :=
    (Ty.openVars_closeOver_rename hlc hG hXs hGX).symm
  rw [hopen,
    Subst.onTy_openVars_of_images zip_fvars_lc (zip_fvars_images hlen hnd hdisj), hfix]
  exact (Ty.openVars_closeOver_rename hlc hG
    (by simp only [recRenameNames, List.length_map, hXs])
    (fun g hg hm => (recRenameNames_mem_source_or_target hm).elim (hGX g hg) (hGT g hg)))


theorem recRenameNames_images {S : Subst} {G Xs Ys names : List Nat}
    (hLen : Xs.length = G.length) (hSub : ∀ n ∈ names, n ∈ G)
    (himages : Xs.map (fun x => S.onTy (.fvar x)) = Ys.map Ty.fvar) :
    (recRenameNames G Xs names).map (fun x => S.onTy (.fvar x)) =
      (recRenameNames G Ys names).map Ty.fvar := by
  have hYs : Ys.length = G.length := by
    have := congrArg List.length himages
    simp only [List.length_map] at this
    omega
  simp only [recRenameNames, List.map_map, Function.comp_def]
  apply List.map_congr_left
  intro n hn
  have hi : G.idxOf n < Xs.length := by have := List.idxOf_lt_length_iff.mpr (hSub n hn); omega
  have hj : G.idxOf n < Ys.length := by omega
  have hh := congrArg (fun ts : List Ty => ts[G.idxOf n]?) himages
  simpa only [List.getElem?_map, List.getElem?_eq_getElem hi, List.getElem?_eq_getElem hj,
    Option.map_some, Option.getD_some, Option.some.injEq] using hh

 theorem Typing.opened_source_onSubst {S : Subst} {P Xs Ys names newNames : List Nat}
    {ctx : Ctx} {rhs : Input} {ty : Ty}
    (h : Typing (P ++ Xs) ctx (rhs.openTyVars names) ty)
    (hS : ∀ pair ∈ S, pair.2.IsLC)
    (hP : ∀ p ∈ P, S.onTy (.fvar p) = .fvar p)
    (himages : Xs.map (fun x => S.onTy (.fvar x)) = Ys.map Ty.fvar)
    (hNames : names.map (fun x => S.onTy (.fvar x)) = newNames.map Ty.fvar)
    (hRaw : ∀ v ∈ rhs.rigidVars, v ∈ P) :
    Typing (P ++ Ys) (S.onCtx ctx) (rhs.openTyVars newNames) (S.onTy ty) := by
  have htrans := h.onSubst_source S hS (K' := P ++ Ys) (by
    intro k hk v hv
    rcases List.mem_append.mp hk with hk | hk
    · rw [hP k hk] at hv
      exact List.mem_append_left _ ((List.mem_singleton.mp hv) ▸ hk)
    · obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hk
      have hh := congrArg (fun ts : List Ty => ts[i]?) himages
      dsimp only at hh
      rw [List.getElem?_map, hi, Option.map_some, List.getElem?_map] at hh
      obtain ⟨y, hy, heq⟩ := Option.map_eq_some_iff.mp hh.symm
      rw [← heq] at hv
      exact List.mem_append_right _ ((List.mem_singleton.mp hv) ▸ List.mem_of_getElem? hy))
  rw [rhs.substTyFvars_openTyVars_of_images hS hNames,
    rhs.substTyFvars_eq_self_of_fixes (fun v hv => hP v (hRaw v hv))] at htrans
  exact htrans

theorem LetAnn.RecFits.onSubst_images {ann : LetAnn} {names resolved : List Nat} {ty : Ty} {S : Subst}
    (h : ann.RecFits names ty) (hS : ∀ pair ∈ S, pair.2.IsLC)
    (himages : names.map (fun x => S.onTy (.fvar x)) = resolved.map Ty.fvar) :
    (ann.substTyFvars S).RecFits resolved (S.onTy ty) := by
  cases ann with
  | absent => trivial
  | complete => exact False.elim h
  | template template => exact h.substTyFvars S
  | partialForall count template =>
    obtain ⟨hlen, hfit⟩ := h
    have heq := congrArg List.length himages
    simp only [List.length_map] at heq
    refine ⟨heq.symm.trans hlen, ?_⟩
    have hs := hfit.substTyFvars S
    simpa only [Template.substTyFvars_openTyVarsFrom_of_images _ hS himages 0] using hs

theorem Ty.prefix_normalize_fresh
    {ty movedTy : Ty} {back : Subst} {Xs actual reps C : List Nat}
    (hBack : back.onTy movedTy = ty)
    (hFix : ∀ x ∈ Xs,back.onTy (.fvar x) = .fvar x)
    (hOld : ∀ x ∈ Xs,x ∉ ty.freeVars)
    (hActual : ∀ a ∈ actual,a ∉ movedTy.freeVars)
    (hReps : ∀ r ∈ reps,r ∈ actual) (hC : ∀ c ∈ C,c ∈ Xs) :
    let B : Subst := C.dedup.zip (reps.map Ty.fvar)
    let Ys := recRenameNames C.dedup reps Xs
    B.onTy movedTy = movedTy ∧ ∀ y ∈ Ys,y ∉ movedTy.freeVars := by
  have hMoved : ∀ x ∈ Xs,x ∉ movedTy.freeVars := by
    intro x hx hv
    have hi : x ∈ (back.onTy movedTy).freeVars := Ty.mem_freeVars_substFvars_image.mpr
      ⟨x,hv,by change x ∈ (back.onTy (.fvar x)).freeVars;rw [hFix x hx];exact List.mem_singleton_self _⟩
    rw [hBack] at hi
    exact hOld x hx hi
  constructor
  · apply Ty.substFvars_eq_self_of_no_key
    intro pair hp hv
    exact hMoved pair.1 (hC pair.1 (List.mem_dedup.mp (List.of_mem_zip hp).1)) hv
  · intro y hy
    rcases recRenameNames_mem_source_or_target hy with hy | hy
    · exact hMoved y hy
    · exact hActual y (hReps y hy)

 theorem RecResidual.align_prefixes
    {P declPool Xs done actual candidate : List Nat} {declCtx ctx : Ctx}
    {declSpecs : List RecSpec} {declPrefixes : List (List Nat)} {state : RecState}
    {R : Subst} {frontier opened : Nat}
    (h : RecResidual P declCtx declSpecs declPrefixes declPool Xs ctx state done R)
    (hbelow : state.Below frontier) (hctx : CtxBelow frontier ctx)
    (hP : ∀ p ∈ P, p < frontier)
    (hactual : actual.Nodup) (hlen : actual.length = candidate.length)
    (hstart : ∀ a ∈ actual, frontier ≤ a) (hend : ∀ a ∈ actual, a < opened)
    (hCX : ∀ c ∈ candidate, c ∈ Xs)
    (hXA : ∀ x ∈ Xs, x ∉ actual) (hXP : ∀ x ∈ Xs, x ∉ P)
    (hG : declPool.Nodup) (hXlen : Xs.length = declPool.length)
    (hGX : ∀ g ∈ declPool, g ∉ Xs) (hGA : ∀ g ∈ declPool, g ∉ actual)
    (hdeclLC : ∀ ty, .mono ty ∈ declSpecs → ty.IsLC)
    (hXM : ∀ ty, .mono ty ∈ declSpecs → ∀ x ∈ Xs, x ∉ ty.freeVars)
    (hXPoly : ∀ sigma, .poly sigma ∈ declSpecs → ∀ x ∈ Xs, x ∉ sigma.body.freeVars)
    (hXCtx : ∀ x ∈ Xs, x ∉ declCtx.env.freeVars) :
    let reps := prefixRepresentatives actual candidate
    let B : Subst := candidate.dedup.zip (reps.map Ty.fvar)
    let Ys := recRenameNames candidate.dedup reps Xs
    ∃ U : Subst, (∀ pair ∈ U, pair.2.IsLC) ∧ Subst.AgreesBelow frontier (R ++ B) U ∧
      (∀ p ∈ P ++ reps, U.onTy (.fvar p) = .fvar p) ∧
      (∀ i (hi : i < candidate.length),
        U.onTy (.fvar (actual[i]'(by omega))) = .fvar (prefixRepresentative actual candidate candidate[i])) ∧
      RecResidual (P ++ reps) declCtx declSpecs declPrefixes declPool Ys ctx state done U := by
  dsimp only
  let reps := prefixRepresentatives actual candidate
  let B : Subst := candidate.dedup.zip (reps.map Ty.fvar)
  have hrepA : ∀ r ∈ reps, r ∈ actual := fun _ hr => prefixRepresentatives_mem_actual hlen hr
  have hrepLen : reps.length = candidate.dedup.length := by simp only [reps, prefixRepresentatives, List.length_map]
  have hdisj : ∀ c ∈ candidate.dedup, c ∉ reps := by
    intro c hc hr
    exact hXA c (hCX c (List.mem_dedup.mp hc)) (hrepA c hr)
  have hBLC : ∀ pair ∈ B, pair.2.IsLC := zip_fvars_lc
  have hRB : ∀ pair ∈ R ++ B, pair.2.IsLC :=
    fun pair hp => (List.mem_append.mp hp).elim (h.lc pair) (hBLC pair)
  obtain ⟨U, hU, hag, hassign, hfixReps⟩ := Subst.override_prefixRepresentatives hRB frontier opened
    hlen hactual hstart hend
  have hPfix : ∀ p ∈ P, (R ++ B).onTy (.fvar p) = .fvar p := by
    intro p hp
    rw [Subst.onTy_append, h.fixes p hp]
    exact zip_fvars_fixes (fun hc => hXP p (hCX p (List.mem_dedup.mp hc)) hp)
  have hUfix := hag.fixes_prefixProtection hlen hP hPfix hassign
  refine ⟨U, hU, hag, hUfix, hassign, ?_⟩
  apply h.change_opening hbelow hctx hBLC ?_ ?_ ?_ ?_ ?_ hU hUfix hag
  · apply congrArg₂ Ctx.mk
    · apply Subst.onEnv_eq_self_of_fresh
      intro pair hp hv
      exact hXCtx pair.1 (hCX pair.1 (List.mem_dedup.mp (List.of_mem_zip hp).1)) hv
    · rfl
  · intro scheme hs
    apply congrArg (PolyTy.mk scheme.paramCount)
    apply Subst.onTy_eq_self_of_fixes
    intro v hv
    exact zip_fvars_fixes (fun hc => hXPoly scheme hs v (hCX v (List.mem_dedup.mp hc)) hv)
  · intro i ty hi _
    exact recScheme_wf (hdeclLC ty (List.mem_of_getElem? hi))
  · intro i ty hi _
    apply congrArg (PolyTy.mk _)
    apply Subst.onTy_eq_self_of_fixes
    intro v hv
    exact zip_fvars_fixes (fun hc => hXM ty (List.mem_of_getElem? hi) v
      (hCX v (List.mem_dedup.mp hc)) (Ty.freeVars_closeOver_subset hv))
  · intro ty ht
    exact zip_fvars_renameG hrepLen (List.nodup_dedup _) hdisj (hdeclLC ty ht) hG hXlen hGX
      (fun g hg hr => hGA g hg (hrepA g hr))
      (fun c hc => hXM ty ht c (hCX c (List.mem_dedup.mp hc)))


theorem recRenameNames_nodup_partial {names targets Xs : List Nat}
    (hlen : targets.length = names.length) (hnd : names.Nodup) (htnd : targets.Nodup)
    (hdisj : ∀ n ∈ names, n ∉ targets) (hXs : Xs.Nodup)
    (havoid : ∀ t ∈ targets, t ∉ Xs) :
    (recRenameNames names targets Xs).Nodup := by
  apply List.Nodup.map_on ?_ hXs
  intro x hx y hy heq
  have hbackx := zip_fvars_roundtrip (ty := .fvar x) hlen hnd htnd hdisj
    (fun t ht hv => havoid t ht ((List.mem_singleton.mp hv) ▸ hx))
  have hbacky := zip_fvars_roundtrip (ty := .fvar y) hlen hnd htnd hdisj
    (fun t ht hv => havoid t ht ((List.mem_singleton.mp hv) ▸ hy))
  rw [zip_fvars_on_rename hlen hnd hdisj] at hbackx hbacky
  rw [heq] at hbackx
  exact Ty.fvar.inj (hbackx.symm.trans hbacky)

theorem OpenRecAnns.written_alignment
    (h : OpenRecAnns selected index frontier anns next openings)
    {names : List (List Nat)} (hlen : names.length = anns.length)
    (hcounts : ∀ j ann ns, anns[j]? = some ann → names[j]? = some ns →
      if index + j ∈ selected then ns.length = ann.recPrefixCount else ns = []) :
    List.Forall₂ (fun opening ns => opening.written.length = ns.length) openings names := by
  induction h generalizing names with
  | nil => have hn : names = [] := List.eq_nil_of_length_eq_zero hlen; subst names; exact .nil
  | skip hn hr ih =>
    cases names with
    | nil => simp at hlen
    | cons ns rest =>
      have hz := hcounts 0 _ ns rfl rfl
      simp only [Nat.add_zero, if_neg hn] at hz
      subst ns
      refine List.Forall₂.cons (R := fun (opening : RecOpening) (ns : List Nat) => opening.written.length = ns.length) rfl ?_
      apply ih (by simpa only [List.length_cons, Nat.add_right_cancel_iff] using hlen)
      intro j ann ns ha hn
      simpa only [List.getElem?_cons_succ, Nat.add_assoc, Nat.add_comm 1 j] using
        hcounts (j+1) ann ns ha hn
  | cons hs ho hr ih =>
    cases names with
    | nil => simp at hlen
    | cons ns rest =>
      have hz := hcounts 0 _ ns rfl rfl
      simp only [Nat.add_zero, if_pos hs] at hz
      apply List.Forall₂.cons
      · exact ho.written_length.trans (by cases ho <;> simpa only [LetAnn.recPrefixCount] using hz.symm)
      · apply ih (by simpa only [List.length_cons, Nat.add_right_cancel_iff] using hlen)
        intro j ann ns ha hn
        simpa only [List.getElem?_cons_succ, Nat.add_assoc, Nat.add_comm 1 j] using
          hcounts (j+1) ann ns ha hn

 theorem OpenRecAnns.written_images
    (h : OpenRecAnns selected index frontier anns next openings)
    {names : List (List Nat)} {U : Subst} {f : Nat → Nat}
    (hlen : names.length = anns.length)
    (hzero : ∀ j ann ns, anns[j]? = some ann → names[j]? = some ns →
      index + j ∉ selected → ns = [])
    (himages : ∀ j opening ns, openings[j]? = some opening → names[j]? = some ns →
      index + j ∈ selected →
        opening.written.map (fun x => U.onTy (.fvar x)) = ns.map (fun x => Ty.fvar (f x))) :
    (openings.flatMap RecOpening.written).map (fun x => U.onTy (.fvar x)) =
      names.flatten.map (fun x => Ty.fvar (f x)) := by
  induction h generalizing names with
  | nil => have hn : names = [] := List.eq_nil_of_length_eq_zero hlen; subst names; rfl
  | skip hn hr ih =>
    cases names with
    | nil => simp at hlen
    | cons ns rest =>
      have hz := hzero 0 _ ns rfl rfl (by simpa only [Nat.add_zero] using hn)
      subst ns
      simp only [List.flatMap_cons, RecOpening.empty, List.nil_append, List.flatten_cons]
      apply ih (by simpa only [List.length_cons, Nat.add_right_cancel_iff] using hlen)
      · intro j ann ns ha hn hj
        exact hzero (j+1) ann ns ha hn (by simpa [Nat.add_assoc, Nat.add_comm 1 j] using hj)
      · intro j opening ns ho hn hj
        exact himages (j+1) opening ns ho hn (by simpa [Nat.add_assoc, Nat.add_comm 1 j] using hj)
  | cons hs ho hr ih =>
    cases names with
    | nil => simp at hlen
    | cons ns rest =>
      simp only [List.flatMap_cons, List.flatten_cons, List.map_append]
      rw [himages 0 _ ns rfl rfl (by simpa only [Nat.add_zero] using hs)]
      congr 1
      apply ih (by simpa only [List.length_cons, Nat.add_right_cancel_iff] using hlen)
      · intro j ann ns ha hn hj
        exact hzero (j+1) ann ns ha hn (by simpa [Nat.add_assoc, Nat.add_comm 1 j] using hj)
      · intro j opening ns ho hn hj
        exact himages (j+1) opening ns ho hn (by simpa [Nat.add_assoc, Nat.add_comm 1 j] using hj)

/-- Renaming the pool's image vector composes with renaming any pool prefix. -/
theorem recRenameNames_map_images {G Xs names labels images : List Nat}
    (hXs : Xs.length = G.length) (hsub : ∀ v ∈ names,v ∈ G) :
    recRenameNames G (recRenameNames labels images Xs) names =
      recRenameNames labels images (recRenameNames G Xs names) := by
  simp only [recRenameNames,List.map_map]
  apply List.map_congr_left
  intro v hv
  have hi : G.idxOf v < Xs.length := by
    have := List.idxOf_lt_length_iff.mpr (hsub v hv)
    omega
  simp only [Function.comp_def,List.getElem?_map,List.getElem?_eq_getElem hi,Option.map_some,Option.getD_some]

 theorem recRenameNames_prefixRepresentatives {A C G Xs names : List Nat}
    (hXs : Xs.length = G.length) (hsub : ∀ v ∈ names,v ∈ G)
    (hclasses : ∀ v ∈ recRenameNames G Xs names,v ∈ C) :
    recRenameNames G (recRenameNames C.dedup (prefixRepresentatives A C) Xs) names =
      (recRenameNames G Xs names).map (prefixRepresentative A C) := by
  rw [recRenameNames_map_images hXs hsub]
  apply List.map_congr_left
  intro v hv
  simp only [prefixRepresentatives,List.getElem?_map,
    List.getElem?_idxOf (List.mem_dedup.mpr (hclasses v hv)),Option.map_some,Option.getD_some]

 theorem OpenRecAnns.selected_prefix_collection
    (h : OpenRecAnns members 0 frontier anns next openings)
    {declPrefixes : List (List Nat)} {G Xs : List Nat}
    (hlen : declPrefixes.length = anns.length) (hXs : Xs.length = G.length)
    (hprefix : ∀ (i : Nat) (ann : LetAnn) (names : List Nat),anns[i]? = some ann →
      declPrefixes[i]? = some names → names.length = ann.recPrefixCount ∧ ∀ v ∈ names,v ∈ G) :
    let targets := declPrefixes.mapIdx (fun i names => if i ∈ members then recRenameNames G Xs names else [])
    (openings.flatMap RecOpening.written).length = targets.flatten.length ∧
      ∀ c ∈ targets.flatten,c ∈ Xs := by
  dsimp only
  let targets := declPrefixes.mapIdx (fun i names => if i ∈ members then recRenameNames G Xs names else [])
  have hTargetLen : targets.length = anns.length := by simp only [targets,List.length_mapIdx,hlen]
  have hAlign := h.written_alignment hTargetLen (by
    intro j ann ns ha hn
    change (declPrefixes.mapIdx _)[j]? = some ns at hn
    rw [List.getElem?_mapIdx] at hn
    obtain ⟨writtenNames,hp,heq⟩ := Option.map_eq_some_iff.mp hn
    by_cases hm : j ∈ members
    · rw [if_pos hm] at heq
      subst ns
      simpa only [Nat.zero_add,if_pos hm,recRenameNames_length] using (hprefix j ann writtenNames ha hp).1
    · rw [if_neg hm] at heq
      subst ns
      simp only [Nat.zero_add,if_neg hm])
  refine ⟨?_,?_⟩
  · change (openings.flatMap RecOpening.written).length = targets.flatten.length
    have aux : ∀ (os : List RecOpening) (ns : List (List Nat)),
        List.Forall₂ (fun opening names => opening.written.length = names.length) os ns →
        (os.flatMap RecOpening.written).length = ns.flatten.length := by
      intro os ns hh
      induction hh with
      | nil => rfl
      | cons heq htail ih =>
        simp only [List.flatMap_cons,List.flatten_cons,List.length_append,heq,ih]
    exact aux _ _ hAlign
  · intro c hc
    change c ∈ targets.flatten at hc
    obtain ⟨names,hn,hc⟩ := List.mem_flatten.mp hc
    obtain ⟨j,hj,heq⟩ := List.mem_mapIdx.mp hn
    have ha : j < anns.length := by omega
    have hAnn := List.getElem?_eq_getElem ha
    have hNames := List.getElem?_eq_getElem hj
    by_cases hm : j ∈ members
    · rw [if_pos hm] at heq
      subst names
      exact recRenameNames_mem hXs (hprefix j _ _ hAnn hNames).2 c hc
    · rw [if_neg hm] at heq
      subst names
      cases hc

 theorem OpenRecAnns.prefixRepresentatives_fixed_of_images
    (h : OpenRecAnns members 0 frontier anns next openings)
    {declPrefixes : List (List Nat)} {G Xs : List Nat} {U : Subst}
    (hlen : declPrefixes.length = anns.length) (hXs : Xs.length = G.length)
    (hprefix : ∀ (i : Nat) (ann : LetAnn) (names : List Nat),anns[i]? = some ann →
      declPrefixes[i]? = some names → names.length = ann.recPrefixCount ∧ ∀ v ∈ names,v ∈ G)
    (himages :
      let targets := declPrefixes.mapIdx (fun i names => if i ∈ members then recRenameNames G Xs names else [])
      let A := openings.flatMap RecOpening.written
      let C := targets.flatten
      let Ys := recRenameNames C.dedup (prefixRepresentatives A C) Xs
      ∀ (i : Nat) (opening : RecOpening) (names : List Nat),i ∈ members →
        openings[i]? = some opening → declPrefixes[i]? = some names →
        opening.written.map (fun v => U.onTy (.fvar v)) = (recRenameNames G Ys names).map Ty.fvar) :
    let targets := declPrefixes.mapIdx (fun i names => if i ∈ members then recRenameNames G Xs names else [])
    let A := openings.flatMap RecOpening.written
    let C := targets.flatten
    ∀ r ∈ prefixRepresentatives A C,U.onTy (.fvar r) = .fvar r := by
  dsimp only at himages ⊢
  let targets := declPrefixes.mapIdx (fun i names => if i ∈ members then recRenameNames G Xs names else [])
  let A := openings.flatMap RecOpening.written
  let C := targets.flatten
  have hAC : A.length = C.length := (h.selected_prefix_collection hlen hXs hprefix).1
  have hglobal : A.map (fun v => U.onTy (.fvar v)) = C.map (fun v => Ty.fvar (prefixRepresentative A C v)) := by
    apply h.written_images (f := prefixRepresentative A C) (names := targets)
      (by simp only [targets,List.length_mapIdx,hlen])
    · intro j ann names ha hn hj
      change (declPrefixes.mapIdx _)[j]? = some names at hn
      rw [List.getElem?_mapIdx] at hn
      obtain ⟨writtenNames,hp,heq⟩ := Option.map_eq_some_iff.mp hn
      have hm : j ∉ members := by simpa only [Nat.zero_add] using hj
      simpa only [if_neg hm] using heq.symm
    · intro j opening names ho hn hj
      have hm : j ∈ members := by simpa only [Nat.zero_add] using hj
      have hTarget := hn
      change (declPrefixes.mapIdx _)[j]? = some names at hn
      rw [List.getElem?_mapIdx] at hn
      obtain ⟨writtenNames,hp,heq⟩ := Option.map_eq_some_iff.mp hn
      rw [if_pos hm] at heq
      subst names
      have hjA : j < anns.length := by
        have := (List.getElem?_eq_some_iff.mp hp).1
        omega
      have hsub := (hprefix j _ writtenNames (List.getElem?_eq_getElem hjA) hp).2
      have hNorm := recRenameNames_prefixRepresentatives (A := A) (C := C) hXs hsub (by
        intro v hv
        exact List.mem_flatten.mpr ⟨_,List.mem_of_getElem? hTarget,hv⟩)
      rw [himages j opening writtenNames hm ho hp,hNorm,List.map_map]
      rfl
  apply prefixRepresentatives_fixed hAC
  intro i hi
  have hEq := congrArg (fun ts : List Ty => ts[i]?) hglobal
  have hiA : i < A.length := by omega
  simpa only [List.getElem?_map,List.getElem?_eq_getElem hiA,List.getElem?_eq_getElem hi,
    Option.map_some,Option.some.injEq] using hEq

theorem recStageCtx_change_opening {B : Subst} {specs : List RecSpec}
    {ctx : Ctx} {prefixes : List (List Nat)} {done G Xs Ys : List Nat}
    (hctx : B.onCtx ctx = ctx)
    (hpoly : ∀ sigma, .poly sigma ∈ specs → B.onPolyTy sigma = sigma)
    (hcomplete : ∀ (i : Nat) (ty : Ty), specs[i]? = some (.mono ty) →
      B.onPolyTy (recScheme (prefixes[i]?.getD []) G ty) = recScheme (prefixes[i]?.getD []) G ty)
    (hmono : ∀ ty, .mono ty ∈ specs → B.onTy (Ty.renameG G Xs ty) = Ty.renameG G Ys ty) :
    B.onCtx (recStageCtx ctx specs prefixes done G Xs) = recStageCtx ctx specs prefixes done G Ys := by
  have heq : List.map B.onPolyTy (specs.mapIdx (recStageEntry prefixes done G Xs)) =
      specs.mapIdx (recStageEntry prefixes done G Ys) := by
    apply List.ext_getElem?
    intro i
    simp only [List.getElem?_map, List.getElem?_mapIdx]
    cases hs : specs[i]? with
    | none => rfl
    | some spec =>
      simp only [Option.map_some]
      congr 1
      cases spec with
      | poly sigma => exact hpoly sigma (List.mem_of_getElem? hs)
      | mono ty =>
        simp only [recStageEntry]
        split
        · exact hcomplete i ty hs
        · exact congrArg PolyTy.mkTrivial (hmono ty (List.mem_of_getElem? hs))
  apply congrArg₂ Ctx.mk
  · have henv := congrArg Ctx.env hctx
    simpa only [Subst.onCtx, Subst.onEnv, recStageCtx, List.map_append, heq] using
      congrArg (fun tail => specs.mapIdx (recStageEntry prefixes done G Ys) ++ tail) henv
  · rfl

 theorem recStageCtx_onSubst_pool_safe {S : Subst} {specs : List RecSpec} {ctx : Ctx}
    {prefixes : List (List Nat)} {done G Xs : List Nat}
    (hLC : ∀ spec ∈ specs, spec.LC) (hS : ∀ pair ∈ S, pair.2.IsLC)
    (hG : G.Nodup) (hLen : Xs.length = G.length) (hGX : ∀ g ∈ G, g ∉ Xs)
    (hPrefix : ∀ i, i < specs.length → ∀ v ∈ prefixes[i]?.getD [], v ∈ G)
    (hDomG : ∀ pair ∈ S, pair.1 ∉ G)
    (hRanG : ∀ pair ∈ S, ∀ v ∈ pair.2.freeVars, v ∉ G)
    (hDomX : ∀ pair ∈ S, pair.1 ∉ Xs) :
    S.onCtx (recStageCtx ctx specs prefixes done G Xs) =
      recStageCtx (S.onCtx ctx) (specs.map (RecSpec.onSubstSource S)) prefixes done G Xs := by
  have heq : List.map S.onPolyTy (specs.mapIdx (recStageEntry prefixes done G Xs)) =
      (specs.map (RecSpec.onSubstSource S)).mapIdx (recStageEntry prefixes done G Xs) := by
    apply List.ext_getElem?
    intro i
    simp only [List.getElem?_map, List.getElem?_mapIdx]
    cases hs : specs[i]? with
    | none => rfl
    | some spec =>
      simp only [Option.map_some]
      congr 1
      cases spec with
      | poly sigma => rfl
      | mono ty =>
        simp only [recStageEntry, RecSpec.onSubstSource]
        split
        · exact (recScheme_subst_pool_avoid hDomG hRanG (hPrefix i (List.getElem?_eq_some_iff.mp hs).1)).symm
        · exact congrArg PolyTy.mkTrivial
            (Ty.renameG_onSubst_pool_safe (hLC _ (List.mem_of_getElem? hs)) hS hG hLen hGX hDomG hRanG hDomX)
  apply congrArg₂ Ctx.mk
  · simp only [Subst.onCtx, Subst.onEnv, recStageCtx, List.map_append, heq]
  · rfl

 theorem OpenRecAnns.realize_prefixes
    {S : Subst} (h : OpenRecAnns members 0 frontier anns next openings)
    (hS : ∀ pair ∈ S, pair.2.IsLC)
    (hraw : ∀ ann ∈ anns, ∀ v ∈ ann.rigidVars, v < frontier)
    (names : List (List Nat)) (targets : List Ty)
    (hNames : names.length = anns.length) (hTargets : targets.length = anns.length)
    (hzero : ∀ i ann ns, anns[i]? = some ann → names[i]? = some ns → i ∉ members → ns = [])
    (hfit : ∀ i ann ns target, i ∈ members → anns[i]? = some ann →
      names[i]? = some ns → targets[i]? = some target →
      (ann.substTyFvars S).RecFits ns target ∧ ns.length = ann.recPrefixCount ∧ target.IsLC)
    (hdisjoint : ∀ c ∈ names.flatten, c ∉ openings.flatMap RecOpening.written) :
    let A := openings.flatMap RecOpening.written
    let C := names.flatten
    let reps := prefixRepresentatives A C
    let B : Subst := C.dedup.zip (reps.map Ty.fvar)
    ∃ U : Subst, (∀ pair ∈ U, pair.2.IsLC) ∧ Subst.AgreesBelow frontier (S ++ B) U ∧
      (∀ r ∈ reps, U.onTy (.fvar r) = .fvar r) ∧
      (∀ i opening ns target, i ∈ members → openings[i]? = some opening →
        names[i]? = some ns → targets[i]? = some target →
        opening.written.map (fun v => U.onTy (.fvar v)) =
          (recRenameNames C.dedup reps ns).map Ty.fvar ∧
        ∀ expected, opening.expected = some expected → U.onTy expected = B.onTy target) := by
  dsimp only
  let A := openings.flatMap RecOpening.written
  let C := names.flatten
  let reps := prefixRepresentatives A C
  let B : Subst := C.dedup.zip (reps.map Ty.fvar)
  have hAC : A.length = C.length := by
    have ha := h.written_alignment hNames (by
      intro i ann ns hann hns
      by_cases hm : i ∈ members
      · rw [if_pos (by simpa only [Nat.zero_add] using hm)]
        have hib : i < targets.length := by
          have := (List.getElem?_eq_some_iff.mp hann).1
          omega
        exact (hfit i ann ns targets[i] hm hann hns (List.getElem?_eq_getElem hib)).2.1
      · rw [if_neg (by simpa only [Nat.zero_add] using hm)]
        exact hzero i ann ns hann hns hm)
    have aux : ∀ os nss, List.Forall₂ (fun (o : RecOpening) (ns : List Nat) => o.written.length = ns.length) os nss →
        (os.flatMap RecOpening.written).length = nss.flatten.length := by
      intro os nss hh
      induction hh with
      | nil => rfl
      | cons heq ht ih => simp only [List.flatMap_cons, List.flatten_cons, List.length_append, heq, ih]
    exact aux _ _ ha
  have hrepA : ∀ r ∈ reps, r ∈ A := fun _ hr => prefixRepresentatives_mem_actual hAC hr
  have hrepLen : reps.length = C.dedup.length := by simp only [reps, prefixRepresentatives, List.length_map]
  have hCD : ∀ c ∈ C.dedup, c ∉ reps := fun c hc hr =>
    hdisjoint c (List.mem_dedup.mp hc) (hrepA c hr)
  have hBLC : ∀ pair ∈ B, pair.2.IsLC := zip_fvars_lc
  have hSBLC : ∀ pair ∈ S ++ B, pair.2.IsLC :=
    fun pair hp => (List.mem_append.mp hp).elim (hS pair) (hBLC pair)
  obtain ⟨U, hU, hag, himages⟩ := h.factor_source hSBLC hraw
    (names.map (recRenameNames C.dedup reps)) (targets.map B.onTy)
    (by simpa only [List.length_map] using hNames)
    (by simpa only [List.length_map] using hTargets) (by
      intro i ann ns target hm hann hns ht
      rw [List.getElem?_map] at hns ht
      obtain ⟨oldNames, hn, rfl⟩ := Option.map_eq_some_iff.mp hns
      obtain ⟨oldTarget, htarget, rfl⟩ := Option.map_eq_some_iff.mp ht
      obtain ⟨hf, hc, hlc⟩ := hfit i ann oldNames oldTarget (by simpa only [Nat.zero_add] using hm) hann hn htarget
      refine ⟨?_, by simpa only [recRenameNames_length] using hc, Subst.onTy_lc hBLC hlc⟩
      rw [LetAnn.substTyFvars_append]
      exact hf.onSubst_images hBLC (zip_fvars_images hrepLen (List.nodup_dedup _) hCD))
  have him : ∀ i opening ns target, i ∈ members → openings[i]? = some opening →
      names[i]? = some ns → targets[i]? = some target →
      opening.written.map (fun v => U.onTy (.fvar v)) =
        (recRenameNames C.dedup reps ns).map Ty.fvar ∧
      ∀ expected, opening.expected = some expected → U.onTy expected = B.onTy target := by
    intro i opening ns target hm ho hn ht
    exact himages i opening _ _ (by simpa only [Nat.zero_add] using hm) ho
      (by simp only [List.getElem?_map, hn, Option.map_some])
      (by simp only [List.getElem?_map, ht, Option.map_some])
  refine ⟨U, hU, hag, ?_, him⟩
  apply prefixRepresentatives_fixed hAC
  intro i hi
  have hglobal : A.map (fun v => U.onTy (.fvar v)) = C.map (fun c => Ty.fvar (prefixRepresentative A C c)) := by
    apply h.written_images hNames
    · intro j ann ns ha hn hj
      exact hzero j ann ns ha hn (by simpa only [Nat.zero_add] using hj)
    · intro j opening ns ho hn hj
      have hjt : j < targets.length := by
        have hjo := (List.getElem?_eq_some_iff.mp ho).1
        have hol := h.length
        omega
      rw [(him j opening ns targets[j] (by simpa only [Nat.zero_add] using hj) ho hn
        (List.getElem?_eq_getElem hjt)).1]
      simp only [recRenameNames, List.map_map, Function.comp_def]
      apply List.map_congr_left
      intro c hc
      have hcC : c ∈ C := List.mem_flatten.mpr ⟨ns, List.mem_of_getElem? hn, hc⟩
      simp only [reps, prefixRepresentatives, List.getElem?_map,
        List.getElem?_idxOf (List.mem_dedup.mpr hcC), Option.map_some, Option.getD_some]
  have he := congrArg (fun ts : List Ty => ts[i]?) hglobal
  have hiA : i < A.length := by omega
  simpa only [List.getElem?_map, List.getElem?_eq_getElem hiA, List.getElem?_eq_getElem hi,
    Option.map_some, Option.some.injEq] using he

theorem RecResidual.fixedCtx_avoids
    {P G Xs K done : List Nat} {F : List Ty} {base : Nat}
    {declCtx ctx : Ctx} {declSpecs : List RecSpec} {declPrefixes : List (List Nat)}
    {anns : List LetAnn} {state : RecState} {R : Subst}
    (h : RecResidual P declCtx declSpecs declPrefixes G Xs ctx state done R)
    (hframe : state.Frame base K F ctx anns done)
    (hCtx : ∀ x ∈ Xs,x ∉ declCtx.env.freeVars)
    (hSpecs : ∀ x ∈ Xs,∀ spec ∈ declSpecs,x ∉ spec.freeVars) :
    ∀ x ∈ Xs,x ∉ (R.onCtx (state.fixedCtx ctx)).env.freeVars := by
  intro x hx hv
  obtain ⟨scheme,hScheme,hxScheme⟩ := Env.mem_freeVars_iff.mp hv
  simp only [Subst.onCtx,Subst.onEnv,RecState.fixedCtx,List.map_append] at hScheme
  change scheme ∈ (state.exports.filterMap id).map R.onPolyTy ++ (R.onCtx ctx).env at hScheme
  rcases List.mem_append.mp hScheme with hExport | hOuter
  · obtain ⟨exported,hExported,hSchemeEq⟩ := List.mem_map.mp hExport
    subst scheme
    obtain ⟨entry,hEntry,hValue⟩ := List.mem_filterMap.mp hExported
    change entry = some exported at hValue
    subst entry
    obtain ⟨i,he⟩ := List.mem_iff_getElem?.mp hEntry
    have hi : i < state.specs.length := by
      have hb := (List.getElem?_eq_some_iff.mp he).1
      rw [hframe.exports_length,← hframe.specs_length] at hb
      exact hb
    have hs := List.getElem?_eq_getElem hi
    cases hSpec : state.specs[i] with
    | mono ty =>
      have hm : state.specs[i]? = some (.mono ty) := by simpa only [hSpec] using hs
      by_cases hd : i ∈ done
      · obtain ⟨declTy,hDecl⟩ := h.mono i ty hm
        obtain ⟨actualExport,hActual,hGeneral⟩ := h.completed i ty declTy hm hDecl hd
        have hSame : actualExport = exported := Option.some.inj (Option.some.inj (hActual.symm.trans he))
        subst actualExport
        exact hSpecs x hx (.mono declTy) (List.mem_of_getElem? hDecl)
          (Ty.freeVars_closeOver_subset (hGeneral.freeVars_subset hxScheme))
      · have hNone := if_neg hd ▸ hframe.mono i ty hm
        rw [he] at hNone
        cases hNone
    | poly actualScheme =>
      have hp : state.specs[i]? = some (.poly actualScheme) := by simpa only [hSpec] using hs
      have hSame : actualScheme = exported :=
        Option.some.inj (Option.some.inj ((hframe.poly i actualScheme hp).symm.trans he))
      subst exported
      obtain ⟨declScheme,hDecl,hEq⟩ := h.poly i actualScheme hp
      rw [hEq] at hxScheme
      exact hSpecs x hx (.poly declScheme) (List.mem_of_getElem? hDecl) hxScheme
  · have hOuterEq := congrArg Ctx.env h.ctx_eq
    rw [hOuterEq] at hOuter
    exact hCtx x hx (Env.mem_freeVars_iff.mpr ⟨scheme,hOuter,hxScheme⟩)

 theorem RecResidual.normalize_openings
    {P G Xs Ys done members : List Nat} {declCtx ctx : Ctx} {declSpecs : List RecSpec}
    {declPrefixes : List (List Nat)} {state : RecState} {R : Subst}
    {anns : List LetAnn} {bindings candidates : List Input} {frontier next : Nat} {openings : List RecOpening}
    (hres : RecResidual P declCtx declSpecs declPrefixes G Xs ctx state done R)
    (ho : OpenRecAnns members 0 frontier anns next openings)
    (hstate : state.Below frontier) (hctx : CtxBelow frontier ctx)
    (hP : ∀ p ∈ P, p < frontier)
    (hrawAnn : ∀ ann ∈ anns, ∀ v ∈ ann.rigidVars, v < frontier)
    (hrawRhs : ∀ rhs ∈ bindings, ∀ v ∈ rhs.rigidVars, v < frontier)
    (hlenBindings : anns.length = bindings.length)
    (names : List (List Nat)) (targets : List Ty)
    (hNames : names.length = anns.length) (hTargets : targets.length = anns.length)
    (hzero : ∀ i ann ns, anns[i]? = some ann → names[i]? = some ns → i ∉ members → ns = [])
    (hfit : ∀ i ann ns target, i ∈ members → anns[i]? = some ann →
      names[i]? = some ns → targets[i]? = some target →
      (ann.substTyFvars R).RecFits ns target ∧ ns.length = ann.recPrefixCount ∧ target.IsLC)
    (hdisjoint : ∀ c ∈ names.flatten, c ∉ openings.flatMap RecOpening.written)
    (hPnames : ∀ p ∈ P, p ∉ names.flatten)
    (hBctx : let reps := prefixRepresentatives (openings.flatMap RecOpening.written) names.flatten
      let B : Subst := names.flatten.dedup.zip (reps.map Ty.fvar)
      B.onCtx declCtx = declCtx)
    (hBpoly : let reps := prefixRepresentatives (openings.flatMap RecOpening.written) names.flatten
      let B : Subst := names.flatten.dedup.zip (reps.map Ty.fvar)
      ∀ scheme, .poly scheme ∈ declSpecs → B.onPolyTy scheme = scheme)
    (hCompletedWF : ∀ i ty, declSpecs[i]? = some (.mono ty) → i ∈ done →
      (recScheme (declPrefixes[i]?.getD []) G ty).WF)
    (hBcompleted : let reps := prefixRepresentatives (openings.flatMap RecOpening.written) names.flatten
      let B : Subst := names.flatten.dedup.zip (reps.map Ty.fvar)
      ∀ i ty, declSpecs[i]? = some (.mono ty) → i ∈ done →
        B.onPolyTy (recScheme (declPrefixes[i]?.getD []) G ty) = recScheme (declPrefixes[i]?.getD []) G ty)
    (hBmono : let reps := prefixRepresentatives (openings.flatMap RecOpening.written) names.flatten
      let B : Subst := names.flatten.dedup.zip (reps.map Ty.fvar)
      ∀ ty, .mono ty ∈ declSpecs → B.onTy (Ty.renameG G Xs ty) = Ty.renameG G Ys ty)
    (htarget : ∀ i ty, i ∈ members → state.specs[i]? = some (.mono ty) → targets[i]? = some (R.onTy ty))
    (hcandidate : ∀ i raw candidate ty ns, i ∈ members → bindings[i]? = some raw →
      candidates[i]? = some candidate → state.specs[i]? = some (.mono ty) → names[i]? = some ns →
      Typing (P ++ ns) (R.onCtx (state.rhsCtx ctx)) (candidate.openTyVars ns) (R.onTy ty))
    (hsource : ∀ i raw, i ∈ members → bindings[i]? = some raw →
      ∃ candidate, candidates[i]? = some candidate ∧ raw.substTyFvars R = candidate ∧
        ∀ v ∈ candidate.rigidVars, v ∈ P) :
    let A := openings.flatMap RecOpening.written
    let C := names.flatten
    let reps := prefixRepresentatives A C
    let B : Subst := C.dedup.zip (reps.map Ty.fvar)
    ∃ U : Subst, (∀ pair ∈ U, pair.2.IsLC) ∧ Subst.AgreesBelow frontier (R ++ B) U ∧
      (∀ p ∈ P ++ reps, U.onTy (.fvar p) = .fvar p) ∧
      RecResidual (P ++ reps) declCtx declSpecs declPrefixes G Ys ctx state done U ∧
      (∀ i opening ns target, i ∈ members → openings[i]? = some opening →
        names[i]? = some ns → targets[i]? = some target →
        opening.written.map (fun v => U.onTy (.fvar v)) = (recRenameNames C.dedup reps ns).map Ty.fvar ∧
        ∀ expected, opening.expected = some expected → U.onTy expected = B.onTy target) ∧
      (∀ i rhs ty, i ∈ members → (openRecSources openings bindings)[i]? = some rhs →
        state.specs[i]? = some (.mono ty) →
        Typing (P ++ reps) (U.onCtx (state.rhsCtx ctx)) (rhs.substTyFvars U) (U.onTy ty)) := by
  dsimp only at hBctx hBpoly hBcompleted hBmono ⊢
  let A := openings.flatMap RecOpening.written
  let C := names.flatten
  let reps := prefixRepresentatives A C
  let B : Subst := C.dedup.zip (reps.map Ty.fvar)
  have hrepLen : reps.length = C.dedup.length := by simp only [reps, prefixRepresentatives, List.length_map]
  have hAC : A.length = C.length := by
    have hh := ho.written_alignment hNames (by
      intro i ann ns ha hn
      by_cases hm : i ∈ members
      · rw [if_pos (by simpa only [Nat.zero_add] using hm)]
        have hi : i < targets.length := by have := (List.getElem?_eq_some_iff.mp ha).1; omega
        exact (hfit i ann ns targets[i] hm ha hn (List.getElem?_eq_getElem hi)).2.1
      · rw [if_neg (by simpa only [Nat.zero_add] using hm)]
        exact hzero i ann ns ha hn hm)
    have aux : ∀ os nss, List.Forall₂ (fun (o : RecOpening) (ns : List Nat) => o.written.length = ns.length) os nss →
        (os.flatMap RecOpening.written).length = nss.flatten.length := by
      intro os nss hh
      induction hh with
      | nil => rfl
      | cons he ht ih => simp only [List.flatMap_cons, List.flatten_cons, List.length_append, he, ih]
    exact aux _ _ hh
  have hrepA : ∀ r ∈ reps, r ∈ A := fun _ hr => prefixRepresentatives_mem_actual hAC hr
  have hCD : ∀ c ∈ C.dedup, c ∉ reps := fun c hc hr => hdisjoint c (List.mem_dedup.mp hc) (hrepA c hr)
  have hBLC : ∀ pair ∈ B, pair.2.IsLC := zip_fvars_lc
  have hBP : ∀ p ∈ P, B.onTy (.fvar p) = .fvar p :=
    fun p hp => zip_fvars_fixes (fun hc => hPnames p hp (List.mem_dedup.mp hc))
  obtain ⟨U, hU, hag, hfix, him⟩ := ho.realize_prefixes hres.lc hrawAnn names targets hNames hTargets hzero hfit hdisjoint
  have hUP : ∀ p ∈ P ++ reps, U.onTy (.fvar p) = .fvar p := by
    intro p hp
    rcases List.mem_append.mp hp with hp | hp
    · have hpb : p < frontier := by
        exact hP p hp
      rw [← hag p hpb, Subst.onTy_append, hres.fixes p hp, hBP p hp]
    · exact hfix p hp
  refine ⟨U, hU, hag, hUP, hres.change_opening hstate hctx hBLC hBctx hBpoly hCompletedWF
    hBcompleted hBmono hU hUP hag, him, ?_⟩
  intro i rhs ty hi hr hs
  obtain ⟨raw, hrRaw, rfl⟩ := openRecSources_getElem? (ho.length.trans hlenBindings) hr
  have hiNames : i < names.length := by have := (List.getElem?_eq_some_iff.mp hrRaw).1; omega
  let ns := names[i]
  have hns : names[i]? = some ns := List.getElem?_eq_getElem hiNames
  have hiOpen : i < openings.length := by
    have := (List.getElem?_eq_some_iff.mp hrRaw).1
    have := ho.length
    omega
  let opening := openings[i]
  have hop : openings[i]? = some opening := List.getElem?_eq_getElem hiOpen
  obtain ⟨candidate, hcand, hsrc, hscope⟩ := hsource i raw hi hrRaw
  have htyped := hcandidate i raw candidate ty ns hi hrRaw hcand hs hns
  have hroots := (him i opening ns (R.onTy ty) hi hop hns (htarget i ty hi hs)).1
  have hBimages : ns.map (fun x => B.onTy (.fvar x)) = (recRenameNames C.dedup reps ns).map Ty.fvar :=
    zip_fvars_images hrepLen (List.nodup_dedup _) hCD
  have ht := htyped.opened_source_onSubst hBLC hBP hBimages hBimages hscope
  have hctxEq : U.onCtx (state.rhsCtx ctx) = B.onCtx (R.onCtx (state.rhsCtx ctx)) := by
    simpa only [Subst.onCtx_append] using (Subst.onCtx_congr hag (hstate.rhsCtx hctx)).symm
  have htyEq : U.onTy ty = B.onTy (R.onTy ty) := by
    simpa only [Subst.onTy_append] using (Subst.onTy_congr hag (hstate.1 _ (List.mem_of_getElem? hs))).symm
  have hrawEq : raw.substTyFvars U = candidate := by
    rw [show raw.substTyFvars U = (raw.substTyFvars R).substTyFvars B from by
      rw [← Input.substTyFvars_append]
      exact raw.substTyFvars_congr (fun v hv => (hag v (hrawRhs raw (List.mem_of_getElem? hrRaw) v hv)).symm), hsrc]
    exact candidate.substTyFvars_eq_self_of_fixes (fun v hv => hBP v (hscope v hv))
  have hOpened : (raw.openTyVars opening.written).substTyFvars U =
      candidate.openTyVars (recRenameNames C.dedup reps ns) := by
    rw [raw.substTyFvars_openTyVars_of_images hU hroots, hrawEq]
  rw [hop, Option.getD_some, hOpened, hctxEq, htyEq]
  exact ht.scope_restrict (fun v hv => by
    rcases Input.rigidVars_openTyVarsFrom hv with hv | hv
    · exact List.mem_append_left _ (hscope v hv)
    · apply List.mem_append_right _
      have hclass : ∀ c ∈ ns, c ∈ C := fun c hc => List.mem_flatten.mpr ⟨ns, List.mem_of_getElem? hns, hc⟩
      obtain ⟨c, hc, heq⟩ := List.mem_map.mp hv
      have hidx : C.dedup.idxOf c < reps.length := by
        have := List.idxOf_lt_length_iff.mpr (List.mem_dedup.mpr (hclass c hc)); omega
      rw [← heq]
      change (reps[C.dedup.idxOf c]?).getD c ∈ reps
      rw [List.getElem?_eq_getElem hidx, Option.getD_some]
      exact List.getElem_mem hidx)

/-- Restore only candidate opening labels after an arbitrary later solve. -/
theorem RecResidual.restore_opening
    {P reps G Xs Ys done : List Nat} {declCtx ctx : Ctx} {declSpecs : List RecSpec}
    {declPrefixes : List (List Nat)} {state : RecState} {T back : Subst}
    (h : RecResidual (P ++ reps) declCtx declSpecs declPrefixes G Ys ctx state done T)
    (hBack : ∀ pair ∈ back,pair.2.IsLC)
    (hBackP : ∀ p ∈ P,back.onTy (.fvar p) = .fvar p)
    (hBackCtx : back.onCtx declCtx = declCtx)
    (hBackPoly : ∀ scheme,.poly scheme ∈ declSpecs → back.onPolyTy scheme = scheme)
    (hCompletedWF : ∀ i ty,declSpecs[i]? = some (.mono ty) → i ∈ done →
      (recScheme (declPrefixes[i]?.getD []) G ty).WF)
    (hBackCompleted : ∀ i ty,declSpecs[i]? = some (.mono ty) → i ∈ done →
      back.onPolyTy (recScheme (declPrefixes[i]?.getD []) G ty) =
        recScheme (declPrefixes[i]?.getD []) G ty)
    (hBackOpen : ∀ ty,.mono ty ∈ declSpecs → back.onTy (Ty.renameG G Ys ty) = Ty.renameG G Xs ty) :
    RecResidual P declCtx declSpecs declPrefixes G Xs ctx state done (T ++ back) := by
  refine ⟨?_,?_,?_,h.length,h.mono,?_,?_,?_⟩
  · intro pair hp
    exact (List.mem_append.mp hp).elim (h.lc pair) (hBack pair)
  · intro p hp
    rw [Subst.onTy_append,h.fixes p (List.mem_append_left _ hp),hBackP p hp]
  · rw [Subst.onCtx_append,h.ctx_eq,hBackCtx]
  · intro i algScheme hi
    obtain ⟨declScheme,hd,heq⟩ := h.poly i algScheme hi
    refine ⟨declScheme,hd,?_⟩
    rw [Subst.onPolyTy_append,heq,hBackPoly declScheme (List.mem_of_getElem? hd)]
  · intro i algTy declTy hi hd hn
    rw [Subst.onTy_append,h.pending i algTy declTy hi hd hn,hBackOpen declTy (List.mem_of_getElem? hd)]
  · intro i algTy declTy hi hd hm
    obtain ⟨exported,he,hg⟩ := h.completed i algTy declTy hi hd hm
    refine ⟨exported,he,?_⟩
    have hRestored := hg.onSubst (hCompletedWF i declTy hd hm) hBack
    rw [hBackCompleted i declTy hd hm] at hRestored
    simpa only [Subst.onPolyTy_append] using hRestored

/-- Pop the finite class renaming; later algorithm state remains literal. -/
theorem RecResidual.restore_prefixRepresentatives
    {P C reps G Xs done : List Nat} {declCtx ctx : Ctx} {declSpecs : List RecSpec}
    {declPrefixes : List (List Nat)} {state : RecState} {T : Subst}
    (h : RecResidual (P ++ reps) declCtx declSpecs declPrefixes G
      (recRenameNames C.dedup reps Xs) ctx state done T)
    (hRepLen : reps.length = C.dedup.length) (hReps : reps.Nodup)
    (hCX : ∀ c ∈ C,c ∈ Xs) (hXR : ∀ x ∈ Xs,x ∉ reps)
    (hG : G.Nodup) (hXlen : Xs.length = G.length)
    (hGX : ∀ g ∈ G,g ∉ Xs) (hGR : ∀ g ∈ G,g ∉ reps)
    (hMonoLC : ∀ ty,.mono ty ∈ declSpecs → ty.IsLC)
    (hXMono : ∀ ty,.mono ty ∈ declSpecs → ∀ x ∈ Xs,x ∉ ty.freeVars)
    (hRepMono : ∀ ty,.mono ty ∈ declSpecs → ∀ r ∈ reps,r ∉ ty.freeVars)
    (hRepPoly : ∀ scheme,.poly scheme ∈ declSpecs → ∀ r ∈ reps,r ∉ scheme.body.freeVars)
    (hRepCtx : ∀ r ∈ reps,r ∉ declCtx.env.freeVars)
    (hRepP : ∀ p ∈ P,p ∉ reps) :
    RecResidual P declCtx declSpecs declPrefixes G Xs ctx state done
      (T ++ reps.zip (C.dedup.map Ty.fvar)) := by
  let B : Subst := C.dedup.zip (reps.map Ty.fvar)
  let back : Subst := reps.zip (C.dedup.map Ty.fvar)
  have hdisj : ∀ c ∈ C.dedup,c ∉ reps := fun c hc => hXR c (hCX c (List.mem_dedup.mp hc))
  apply h.restore_opening (back := back) zip_fvars_lc (fun p hp => zip_fvars_fixes (hRepP p hp))
  · apply congrArg₂ Ctx.mk
    · apply Subst.onEnv_eq_self_of_fresh
      intro pair hp hv
      exact hRepCtx pair.1 (List.of_mem_zip hp).1 hv
    · rfl
  · intro scheme hs
    apply congrArg (PolyTy.mk scheme.paramCount)
    apply Subst.onTy_eq_self_of_fixes
    intro v hv
    exact zip_fvars_fixes (fun hr => hRepPoly scheme hs v hr hv)
  · intro i ty hd _
    exact recScheme_wf (hMonoLC ty (List.mem_of_getElem? hd))
  · intro i ty hd _
    apply congrArg (PolyTy.mk _)
    apply Subst.onTy_eq_self_of_fixes
    intro v hv
    exact zip_fvars_fixes (fun hr => hRepMono ty (List.mem_of_getElem? hd) v hr (Ty.freeVars_closeOver_subset hv))
  · intro ty ht
    have hForward : B.onTy (Ty.renameG G Xs ty) = Ty.renameG G (recRenameNames C.dedup reps Xs) ty :=
      zip_fvars_renameG hRepLen (List.nodup_dedup _) hdisj (hMonoLC ty ht) hG hXlen hGX hGR
        (fun c hc => hXMono ty ht c (hCX c (List.mem_dedup.mp hc)))
    rw [← hForward]
    apply zip_fvars_roundtrip hRepLen (List.nodup_dedup _) hReps hdisj
    intro r hr
    apply Subst.notMemOnTy (S := G.zip (Xs.map Ty.fvar)) ?_ (hRepMono ty ht r hr)
    intro pair hp hv
    obtain ⟨x,hx,heq⟩ := List.mem_map.mp (List.of_mem_zip hp).2
    rw [← heq] at hv
    exact hXR x hx ((List.mem_singleton.mp hv) ▸ hr)

/-- Restore agreement on every old variable, using its actual ambient image. -/
theorem _root_.Subst.AgreesBelow.restore_prefixRepresentatives
    {N : Nat} {R solved residual : Subst} {C reps : List Nat}
    (h : Subst.AgreesBelow N (R ++ C.dedup.zip (reps.map Ty.fvar)) (solved ++ residual))
    (hRepLen : reps.length = C.dedup.length) (hReps : reps.Nodup)
    (hdisj : ∀ c ∈ C.dedup,c ∉ reps)
    (hAvoid : ∀ v,v < N → ∀ r ∈ reps,r ∉ (R.onTy (.fvar v)).freeVars) :
    Subst.AgreesBelow N R (solved ++ (residual ++ reps.zip (C.dedup.map Ty.fvar))) := by
  intro v hv
  calc
    R.onTy (.fvar v) =
        Subst.onTy (reps.zip (C.dedup.map Ty.fvar))
          ((R ++ C.dedup.zip (reps.map Ty.fvar)).onTy (.fvar v)) := by
      simpa only [Subst.onTy_append] using
        (zip_fvars_roundtrip hRepLen (List.nodup_dedup _) hReps hdisj (hAvoid v hv)).symm
    _ = Subst.onTy (reps.zip (C.dedup.map Ty.fvar)) ((solved ++ residual).onTy (.fvar v)) :=
      congrArg (Subst.onTy (reps.zip (C.dedup.map Ty.fvar))) (h v hv)
    _ = _ := by simp only [Subst.onTy_append]

/-- Finalization and a residual factor preserve a fresh candidate pool at the
export boundary, without any bound on candidate images or later allocations. -/
theorem FinishRecComponent.export_fresh_of_agrees
    {S U V : Subst} {Xs K members : List Nat} {F : List Ty}
    {originalFixedCtx currentCtx : Ctx} {state final : RecState}
    (h : FinishRecComponent K (softVars (substSoft S F)) members currentCtx state outputs facts final)
    (hFixed : state.fixedCtx currentCtx = S.onCtx originalFixedCtx)
    (hCtx : CtxBelow N originalFixedCtx) (hK : ∀ k ∈ K,k < N)
    (hF : ∀ t ∈ F,Ty.BelowFvars N t)
    (hSfix : ∀ k ∈ K,S.onTy (.fvar k) = .fvar k)
    (hAgree : Subst.AgreesBelow N U (S ++ V))
    (hXsCtx : ∀ x ∈ Xs,x ∉ (U.onCtx originalFixedCtx).env.freeVars)
    (hXsK : ∀ x ∈ Xs,∀ k ∈ K,x ∉ (U.onTy (.fvar k)).freeVars)
    (hXsF : ∀ x ∈ Xs,x ∉ softVars (substSoft U F))
    (hi : i ∈ members) (ht : state.specs[i]? = some (.mono ty))
    (hex : final.exports[i]? = some (some scheme)) :
    ∀ x ∈ Xs,x ∉ (V.onPolyTy scheme).body.freeVars := by
  have hCtxEq : V.onCtx (state.fixedCtx currentCtx) = U.onCtx originalFixedCtx := by
    rw [hFixed,←Subst.onCtx_append]
    exact (Subst.onCtx_congr hAgree hCtx).symm
  intro x hx hfree
  obtain ⟨v,hv,himage⟩ := Ty.mem_freeVars_substFvars_image.mp hfree
  rcases h.export_freeVars_boundary hi ht hex v hv with hfixed | hrigid | hsoft
  · have hxCtx : x ∈ (V.onCtx (state.fixedCtx currentCtx)).env.freeVars := by
      obtain ⟨M,hM,hvM⟩ := Env.mem_freeVars_iff.mp hfixed
      apply Env.mem_freeVars_iff.mpr
      refine ⟨V.onPolyTy M,List.mem_map.mpr ⟨M,hM,rfl⟩,?_⟩
      exact Ty.mem_freeVars_substFvars_image.mpr ⟨v,hvM,himage⟩
    exact hXsCtx x hx (hCtxEq ▸ hxCtx)
  · have hh := hAgree v (hK v hrigid)
    rw [Subst.onTy_append,hSfix v hrigid] at hh
    exact hXsK x hx v hrigid (hh ▸ himage)
  · obtain ⟨original,horiginal,hvOriginal⟩ := mem_softVars_substSoft.mp hsoft
    have hxOriginal : x ∈ (V.onTy (S.onTy (.fvar original))).freeVars :=
      Ty.mem_freeVars_substFvars_image.mpr ⟨v,hvOriginal,himage⟩
    have hh := hAgree original (softVars_lt hF original horiginal)
    rw [Subst.onTy_append] at hh
    exact hXsF x hx (mem_softVars_substSoft.mpr ⟨original,horiginal,hh ▸ hxOriginal⟩)

 theorem _root_.InferRecComponent.sourcePrincipal_after_shapes
    {specs : List RecSpec} {bindings : List Input}
    (hshape : CheckRecShapes K shapes pre)
    (hcomponent : InferRecComponent K (substSoft pre F) members index frontier (pre.onCtx ctx)
      (bindings.map (Input.substTyFvars pre)) (specs.map (RecSpec.onSubstSource pre)) next current outputs facts)
    (hInfer : ∀ {κ F' Ψ c e Ψ' T output ty}, e.size ≤ sizeBindings bindings →
      (hi : Infer κ F' Ψ c e Ψ' T output ty) → Infer.SourcePrincipal hi)
    (hctxWF : CtxWF ctx) (hctx : CtxBelow frontier ctx)
    (hK : ∀ k ∈ K, k < frontier) (hF : ∀ t ∈ F, Ty.BelowFvars frontier t)
    (hSpecLC : ∀ spec ∈ specs, spec.LC)
    (hSpecB : ∀ spec ∈ specs, spec.BelowFvars frontier)
    (hSource : ∀ rhs ∈ bindings, SourceScope K F rhs)
    (hPreLC : ∀ pair ∈ pre, pair.2.IsLC)
    (hPreB : ∀ pair ∈ pre, Ty.BelowFvars frontier pair.2)
    (ambient : Subst) (P : List Nat) (hAmbient : ∀ pair ∈ ambient, pair.2.IsLC)
    (hP : ∀ p ∈ P, p < frontier) (hFix : ∀ p ∈ P, ambient.onTy (.fvar p) = .fvar p)
    (hSolve : ∀ ty expected, (ty, some expected) ∈ shapes → ambient.onTy ty = ambient.onTy expected)
    (hFreeze : ∀ (j : Nat) (rhs : Input), index + j ∈ members → bindings[j]? = some rhs →
      ∀ v ∈ rhs.rigidVars, v ∈ K → v ∉ softVars F → ambient.onTy (.fvar v) = .fvar v)
    (hCandidate : ∀ (j : Nat) (rhs : Input) (target : Ty), index + j ∈ members →
      bindings[j]? = some rhs → specs[j]? = some (.mono target) →
      Typing P (ambient.onCtx ctx) (rhs.substTyFvars ambient) (ambient.onTy target)) :
    ∃ residual : Subst, (∀ pair ∈ residual, pair.2.IsLC) ∧
      (∀ p ∈ P, residual.onTy (.fvar p) = .fvar p) ∧
      Subst.AgreesBelow frontier ambient (pre ++ current ++ residual) := by
  obtain ⟨V, hV, hVP, hFactor⟩ := hshape.factor hAmbient hSolve hFix
  have hPreFix := Subst.fixes_of_dom_avoids hshape.dom_avoids
  have hAgreement : Subst.AgreesBelow frontier ambient (pre ++ V) := by
    intro v _
    simpa only [Subst.onTy_append] using hFactor (.fvar v)
  have hCtxEq : V.onCtx (pre.onCtx ctx) = ambient.onCtx ctx := by
    apply congrArg₂ Ctx.mk
    · simp only [Subst.onCtx, Subst.onEnv, List.map_map]
      apply List.map_congr_left
      intro M _
      exact congrArg (PolyTy.mk M.paramCount) (hFactor M.body).symm
    · rfl
  have hRawBelow : ∀ rhs ∈ bindings, ∀ v ∈ rhs.rigidVars, v < frontier := by
    intro rhs hr v hv
    exact (List.mem_append.mp (hSource rhs hr v hv)).elim (hK v) (softVars_lt hF v)
  obtain ⟨residual, hResidual, hResidualP, hResidualAgree⟩ := hcomponent.sourcePrincipal_of_infer
    (fun he hi => hInfer (by simpa only [sizeBindings_map_substTyFvars] using he) hi)
    (Subst.onCtx_wf hPreLC hctxWF) (Subst.onCtx_below hPreB (Nat.le_refl _) hctx)
    hK (substSoft_below hPreB (Nat.le_refl _) hF)
    (by
      intro spec hs
      obtain ⟨old, ho, rfl⟩ := List.mem_map.mp hs
      exact RecSpec.lc_onSubstSource hPreLC (hSpecLC old ho))
    (by
      intro spec hs
      obtain ⟨old, ho, rfl⟩ := List.mem_map.mp hs
      cases old <;> exact Subst.onTy_belowFvars hPreB (hSpecB _ ho))
    (by
      intro rhs hr
      obtain ⟨old, ho, rfl⟩ := List.mem_map.mp hr
      exact (hSource old ho).subst pre hPreFix)
    V P hV hP hVP
    (by
      intro j rhs hj hr v hv hk hn
      obtain ⟨old, ho, rfl⟩ := Option.map_eq_some_iff.mp (by simpa only [List.getElem?_map] using hr)
      exact (hSource old (List.mem_of_getElem? ho)).residual_freeze
        (hRawBelow old (List.mem_of_getElem? ho)) hPreFix (hFreeze j old hj ho) hAgreement v hv hk hn)
    (by
      intro j rhs target hj hr ht
      obtain ⟨old, ho, rfl⟩ := Option.map_eq_some_iff.mp (by simpa only [List.getElem?_map] using hr)
      obtain ⟨oldTarget, hot, rfl⟩ := RecSpec.mono_getElem?_map_onSubstSource ht
      have hSourceEq : (old.substTyFvars pre).substTyFvars V = old.substTyFvars ambient := by
        rw [← old.substTyFvars_append]
        apply old.substTyFvars_congr
        intro v _
        change (pre ++ V).onTy (.fvar v) = ambient.onTy (.fvar v)
        rw [Subst.onTy_append]
        exact (hFactor (.fvar v)).symm
      rw [hCtxEq, hSourceEq, ← hFactor oldTarget]
      exact hCandidate j old oldTarget hj ho hot)
  refine ⟨residual, hResidual, hResidualP, ?_⟩
  intro v hv
  calc
    ambient.onTy (.fvar v) = V.onTy (pre.onTy (.fvar v)) := hFactor _
    _ = (current ++ residual).onTy (pre.onTy (.fvar v)) :=
      Subst.onTy_congr hResidualAgree (Subst.onTy_belowFvars hPreB (.fvar hv))
    _ = _ := by simp only [Subst.onTy_append]


theorem RecResidual.completed_entries_generalize
    {P declPool Xs done : List Nat} {declCtx ctx : Ctx} {declSpecs : List RecSpec}
    {declPrefixes : List (List Nat)} {state : RecState} {R : Subst}
    (h : RecResidual P declCtx declSpecs declPrefixes declPool Xs ctx state done R)
    (hlen : state.exports.length = state.specs.length)
    (hpoly : ∀ (i : Nat) (scheme : PolyTy), state.specs[i]? = some (.poly scheme) → state.exports[i]? = some (some scheme))
    (hdone : ∀ i ty, state.specs[i]? = some (.mono ty) → i ∈ done) :
    List.Forall₂ PolyTy.Generalizes (state.entries.map R.onPolyTy)
      (recCompletedSchemes declSpecs declPrefixes declPool) := by
  apply List.forall₂_of_length_eq_of_get
  · simp only [List.length_map, recCompletedSchemes, List.length_mapIdx, state.entries_length hlen, h.length]
  · intro i hnew hold
    have hib : i < state.specs.length := by
      simpa only [List.length_map, state.entries_length hlen] using hnew
    have hi := List.getElem?_eq_getElem hib
    change (state.entries.map R.onPolyTy)[i].Generalizes
      (recCompletedSchemes declSpecs declPrefixes declPool)[i]
    cases hs : state.specs[i] with
    | mono ty =>
      have hmono : state.specs[i]? = some (.mono ty) := by simpa only [hs] using hi
      obtain ⟨declTy, hd⟩ := h.mono i ty hmono
      obtain ⟨exported, he, hg⟩ := h.completed i ty declTy hmono hd (hdone i ty hmono)
      have hent := residual_entries_at hmono he
      simp only [List.getElem_map, (List.getElem?_eq_some_iff.mp hent).2, Option.getD_some,
        recCompletedSchemes, List.getElem_mapIdx, (List.getElem?_eq_some_iff.mp hd).2,
        RecSpec.completedScheme]
      exact hg
    | poly scheme =>
      have hpolySpec : state.specs[i]? = some (.poly scheme) := by simpa only [hs] using hi
      obtain ⟨declScheme, hd, heq⟩ := h.poly i scheme hpolySpec
      have hent := residual_entries_at hpolySpec (hpoly i scheme hpolySpec)
      simp only [List.getElem_map, (List.getElem?_eq_some_iff.mp hent).2, Option.getD_some, heq,
        recCompletedSchemes, List.getElem_mapIdx, (List.getElem?_eq_some_iff.mp hd).2,
        RecSpec.completedScheme]
      exact PolyTy.Generalizes.refl _

theorem RecResidual.weaken_from_body
    {P declPool Xs done Q : List Nat} {declCtx ctx : Ctx} {declSpecs : List RecSpec}
    {declPrefixes : List (List Nat)} {state : RecState} {R : Subst} {input : Input} {ty : Ty}
    (h : RecResidual P declCtx declSpecs declPrefixes declPool Xs ctx state done R)
    (hlen : state.exports.length = state.specs.length)
    (hpoly : ∀ (i : Nat) (scheme : PolyTy), state.specs[i]? = some (.poly scheme) → state.exports[i]? = some (some scheme))
    (hdone : ∀ i monoTy, state.specs[i]? = some (.mono monoTy) → i ∈ done)
    (ht : Typing Q (recBodyCtx declCtx declSpecs declPrefixes declPool) input ty) :
    Typing Q (R.onCtx (state.rhsCtx ctx)) input ty := by
  have hg := h.completed_entries_generalize hlen hpoly hdone
  have ht' := Typing.weaken_schemes hg ht
  have hctx : R.onCtx (state.rhsCtx ctx) =
      ⟨state.entries.map R.onPolyTy ++ declCtx.env, declCtx.ctors⟩ := by
    have he := congrArg Ctx.env h.ctx_eq
    have hc := congrArg Ctx.ctors h.ctx_eq
    apply congrArg₂ Ctx.mk
    · simpa only [RecState.rhsCtx, Subst.onCtx, Subst.onEnv, List.map_append] using
        congrArg (state.entries.map R.onPolyTy ++ ·) he
    · simpa only [RecState.rhsCtx, Subst.onCtx] using hc
  rw [hctx]
  exact ht'

theorem _root_.Infer.signed_check_factor
    {K P : List Nat} {F : List Ty} {frontier first : Nat} {ctx : Ctx}
    {rhs : Input} {scheme : PolyTy} {s1 s2 R : Subst} {output : Expr} {ty : Ty}
    (hwf : scheme.WF)
    (hann : ∀ v ∈ scheme.body.freeVars, v ∈ K ++ softVars F)
    (hraw : SourceScope K F rhs)
    (hi : Infer (K ++ freshVars frontier scheme.paramCount) F (frontier + scheme.paramCount)
      ctx (rhs.openTyVars (freshVars frontier scheme.paramCount)) first s1 output ty)
    (hu : RigidUnify (K ++ freshVars frontier scheme.paramCount) ty
      ((s1.onPolyTy scheme).openVars (freshVars frontier scheme.paramCount)) s2)
    (hescape : ∀ y ∈ freshVars frontier scheme.paramCount,
      y ∉ (s2.onCtx (s1.onCtx ctx)).env.freeVars ++ softVars (substSoft (s1 ++ s2) F))
    (ih : Infer.SourcePrincipal hi)
    (hctxWF : CtxWF ctx) (hctx : CtxBelow frontier ctx)
    (hK : ∀ k ∈ K, k < frontier) (hF : ∀ soft ∈ F, Ty.BelowFvars frontier soft)
    (hR : ∀ pair ∈ R, pair.2.IsLC) (hP : ∀ p ∈ P, p < frontier)
    (hRP : ∀ p ∈ P, R.onTy (.fvar p) = .fvar p)
    (hfreeze : ∀ v ∈ (Input.letIn (.complete scheme) rhs (.primLit .unit)).rigidVars,
      v ∈ K → v ∉ softVars F → R.onTy (.fvar v) = .fvar v)
    (hcandAnn : ∀ v ∈ (R.onPolyTy scheme).body.freeVars, v ∈ P)
    (hcandRhs : ∀ v ∈ (rhs.substTyFvars R).rigidVars, v ∈ P)
    (hcandidate : ∃ L, ∀ Ys, FreshNames L scheme.paramCount Ys →
      Typing (P ++ Ys) (R.onCtx ctx) ((rhs.substTyFvars R).openTyVars Ys)
        ((R.onPolyTy scheme).openVars Ys)) :
    ∃ U : Subst, (∀ pair ∈ U, pair.2.IsLC) ∧
      (∀ p ∈ P, U.onTy (.fvar p) = .fvar p) ∧
      Subst.AgreesBelow frontier R ((s1 ++ s2) ++ U) := by
  have hscope : SourceScope K F (.letIn (.complete scheme) rhs (.primLit .unit)) := by
    intro v hv
    simp only [Input.rigidVars, LetAnn.rigidVars, List.mem_append, List.not_mem_nil, or_false] at hv
    exact hv.elim (hann v) (hraw v)
  have havoid : ∀ name ∈ freshVars frontier scheme.paramCount, name ∉ K ++ softVars F := by
    intro name hn hc
    have hlow := freshVars_ge name hn
    have hhigh := (List.mem_append.mp hc).elim (hK name) (softVars_lt hF name)
    omega
  have hfirst := hi.frontier_le
  have hle : frontier ≤ first := by omega
  obtain ⟨htLC, hs1LC⟩ := hi.lc hctxWF
  have hs2LC := hu.unifies.lc htLC (PolyTy.openVars_isLC (Subst.onPolyTy_wf hs1LC hwf) (by
    simp only [freshVars_length, Subst.onPolyTy]; omega))
  have hs1Fix : ∀ k ∈ K, s1.onTy (.fvar k) = .fvar k :=
    Subst.fixes_of_dom_avoids (fun p hp hk => hi.dom_avoids p hp (List.mem_append_left _ hk))
  have hcheck : SignatureCheck K (substSoft s1 F) (freshVars frontier scheme.paramCount) first ty
      ((LetAnn.complete scheme).substTyFvars s1) first s2 := by
    apply SignatureCheck.complete (Subst.onPolyTy_wf hs1LC hwf) ?_ hu
    intro v hv
    obtain ⟨original, ho, hv⟩ := Ty.mem_freeVars_substFvars_image.mp hv
    exact scope_image hs1Fix (hann original ho) hv
  obtain ⟨htB, hs1B⟩ := hi.belowFvars (fun M hM => (hctx M hM).mono (by omega))
    (fun k hk => (List.mem_append.mp hk).elim (fun hk => by have := hK k hk; omega)
      (fun hk => by have := freshVars_lt k hk; simpa only [freshVars_length] using this))
    (fun t ht => (hF t ht).mono (by omega))
  have hs2B := hcheck.belowFvars htB (fun k hk => (hK k hk).trans_le hle)
    (fun y hy => (freshVars_lt y hy).trans_le hfirst) (substSoft_below hs1B (by omega) hF)
  have hbothB : ∀ p ∈ s1 ++ s2, Ty.BelowFvars first p.2 :=
    fun p hp => (List.mem_append.mp hp).elim (hs1B p) (hs2B p)
  let bodyCtx : Ctx :=
    { s2.onCtx (s1.onCtx ctx) with
      env := signatureScheme ((LetAnn.complete scheme).substTyFvars (s1 ++ s2))
        (K ++ softVars (substSoft (s1 ++ s2) F)) (freshVars frontier scheme.paramCount)
        (s2.onCtx (s1.onCtx ctx)) (s2.onTy ty) :: (s2.onCtx (s1.onCtx ctx)).env }
  have hbodyB : CtxBelow first bodyCtx := by
    intro M hm
    rcases List.mem_cons.mp hm with rfl | hm
    · change Ty.BelowFvars first ((s1 ++ s2).onPolyTy scheme).body
      exact Subst.onTy_belowFvars hbothB
        ((Ty.BelowFvars.of_freeVars_lt (fun v hv => (List.mem_append.mp (hann v hv)).elim (hK v) (softVars_lt hF v))).mono hle)
    · have hb : CtxBelow first (s2.onCtx (s1.onCtx ctx)) := by
        simpa only [Subst.onCtx_append] using Subst.onCtx_below hbothB hle hctx
      exact hb M hm
  have hKfirst : ∀ k ∈ K, k < first := fun k hk => (hK k hk).trans_le hle
  let hb : Infer K (substSoft (s1 ++ s2) F) first bodyCtx (.primLit .unit) first []
      (.primLit .unit) (.prim .unit) :=
    .backend rfl .primLitUnit hbodyB hKfirst (by simp [Expr.tyFreeVars]) (by simp [Expr.tyFreeVars])
  have ihb : Infer.SourcePrincipal hb :=
    Infer.sourcePrincipal_backend rfl .primLitUnit hbodyB hKfirst
      (by simp [Expr.tyFreeVars]) (by simp [Expr.tyFreeVars])
  have hprincipal := Infer.sourcePrincipal_letSignature hscope rfl havoid hraw hi hcheck hescape hb ih ihb
  obtain ⟨L, htypes⟩ := hcandidate
  have ht : Typing P (R.onCtx ctx)
      ((Input.letIn (.complete scheme) rhs (.primLit .unit)).substTyFvars R) (.prim .unit) := by
    refine Typing.letSignature (M := R.onPolyTy scheme) (L := L)
      (Subst.onPolyTy_wf hR hwf) hcandAnn hcandRhs (fun _ _ => .complete) ?_
      (.primLit .primLitUnit)
    intro Ys hy
    have hlen : Ys.length = scheme.paramCount := hy.length
    have htake : Ys.take scheme.paramCount = Ys := List.take_of_length_le (by omega)
    simpa only [LetAnn.paramCount, LetAnn.substTyFvars, Subst.onPolyTy, htake] using htypes Ys
      ⟨hlen, hy.nodup, hy.avoid⟩
  obtain ⟨U, hU, _, hUP, hag⟩ := hprincipal hctxWF hctx hK hF R (.prim .unit) P hR hP hRP hfreeze ht
  exact ⟨U, hU, hUP, by simpa only [List.append_nil] using hag⟩

private theorem residual_congr_types {P declPool Xs done : List Nat} {declCtx ctx : Ctx}
    {declSpecs : List RecSpec} {declPrefixes : List (List Nat)} {state final : RecState} {R : Subst}
    (h : RecResidual P declCtx declSpecs declPrefixes declPool Xs ctx state done R)
    (hs : final.specs = state.specs) (he : final.exports = state.exports) :
    RecResidual P declCtx declSpecs declPrefixes declPool Xs ctx final done R := by
  refine ⟨h.lc, h.fixes, h.ctx_eq, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [hs] using h.length
  · simpa only [hs] using h.mono
  · simpa only [hs] using h.poly
  · simpa only [hs] using h.pending
  · simpa only [hs, he] using h.completed

private theorem signed_ann_freeze {ann : LetAnn} {K : List Nat} {F : List Ty} {frontier : Nat}
    {R solved U : Subst}
    (hscope : ∀ v ∈ ann.rigidVars, v ∈ K ++ softVars F)
    (hbelow : ∀ v ∈ ann.rigidVars, v < frontier)
    (hsolved : ∀ k ∈ K, solved.onTy (.fvar k) = .fvar k)
    (hfreeze : ∀ v ∈ ann.rigidVars, v ∈ K → v ∉ softVars F → R.onTy (.fvar v) = .fvar v)
    (hag : Subst.AgreesBelow frontier R (solved ++ U)) :
    ∀ v ∈ (ann.substTyFvars solved).rigidVars, v ∈ K → v ∉ softVars (substSoft solved F) →
      U.onTy (.fvar v) = .fvar v := by
  have hs : SourceScope K F (.letIn ann (.primLit .unit) (.primLit .unit)) := by
    simpa only [SourceScope, Input.rigidVars, List.append_nil] using hscope
  have hb : ∀ v ∈ (Input.letIn ann (.primLit .unit) (.primLit .unit)).rigidVars, v < frontier := by
    simpa only [Input.rigidVars, List.append_nil] using hbelow
  have hf : ∀ v ∈ (Input.letIn ann (.primLit .unit) (.primLit .unit)).rigidVars,
      v ∈ K → v ∉ softVars F → R.onTy (.fvar v) = .fvar v := by
    simpa only [Input.rigidVars, List.append_nil] using hfreeze
  simpa only [Input.substTyFvars, Input.rigidVars, List.append_nil] using
    hs.residual_freeze hb hsolved hf hag

 theorem _root_.InferRecSigned.sourcePrincipal_residual
    (h : InferRecSigned K F index frontier ctx anns bindings state next S final)
    (hInfer : ∀ {κ F' Ψ c e Ψ' T output ty}, e.size ≤ sizeBindings bindings →
      (hi : Infer κ F' Ψ c e Ψ' T output ty) → Infer.SourcePrincipal hi)
    {P declPool Xs done : List Nat} {declCtx : Ctx} {declSpecs : List RecSpec}
    {declPrefixes : List (List Nat)} {R : Subst}
    (hres : RecResidual P declCtx declSpecs declPrefixes declPool Xs ctx state done R)
    (hctxWF : CtxWF ctx) (hctx : CtxBelow frontier ctx)
    (hstateLC : state.LC) (hstateB : state.Below frontier)
    (hK : ∀ k ∈ K, k < frontier) (hF : ∀ t ∈ F, Ty.BelowFvars frontier t)
    (hP : ∀ p ∈ P, p < frontier)
    (hlen : state.exports.length = state.specs.length)
    (hpoly : ∀ (i : Nat) (scheme : PolyTy), state.specs[i]? = some (.poly scheme) →
      state.exports[i]? = some (some scheme))
    (hdone : ∀ i ty, state.specs[i]? = some (.mono ty) → i ∈ done)
    (hannScope : ∀ ann ∈ anns, ∀ v ∈ ann.rigidVars, v ∈ K ++ softVars F)
    (hrhsScope : ∀ rhs ∈ bindings, SourceScope K F rhs)
    (hannFreeze : ∀ ann ∈ anns, ∀ v ∈ ann.rigidVars,
      v ∈ K → v ∉ softVars F → R.onTy (.fvar v) = .fvar v)
    (hrhsFreeze : ∀ rhs ∈ bindings, ∀ v ∈ rhs.rigidVars,
      v ∈ K → v ∉ softVars F → R.onTy (.fvar v) = .fvar v)
    (hcandAnn : ∀ ann ∈ anns, ∀ v ∈ (ann.substTyFvars R).rigidVars, v ∈ P)
    (hcandRhs : ∀ rhs ∈ bindings, ∀ v ∈ (rhs.substTyFvars R).rigidVars, v ∈ P)
    (hcandidate : ∀ (j : Nat) (scheme : PolyTy) (rhs : Input),
      anns[j]? = some (.complete scheme) → bindings[j]? = some rhs →
      ∃ L, ∀ Ys, FreshNames L scheme.paramCount Ys →
        Typing (P ++ Ys) (recBodyCtx declCtx declSpecs declPrefixes declPool)
          ((rhs.substTyFvars R).openTyVars Ys) ((R.onPolyTy scheme).openVars Ys)) :
    ∃ U : Subst, (∀ pair ∈ U, pair.2.IsLC) ∧
      (∀ p ∈ P, U.onTy (.fvar p) = .fvar p) ∧
      Subst.AgreesBelow frontier R (S ++ U) ∧
      RecResidual P declCtx declSpecs declPrefixes declPool Xs (S.onCtx ctx) final done U := by
  match h with
  | .nil =>
    exact ⟨R, hres.lc, hres.fixes, (by intro v hv; simp only [Subst.onTy_append, Subst.onTy_nil]),
      by simpa only [Subst.onCtx_nil] using hres⟩
  | .skip hmode hr =>
    apply hr.sourcePrincipal_residual (fun he hi => hInfer (by simp only [sizeBindings]; omega) hi)
      hres hctxWF hctx hstateLC hstateB hK hF hP hlen hpoly hdone
    · exact fun ann hm => hannScope ann (List.mem_cons_of_mem _ hm)
    · exact fun rhs hm => hrhsScope rhs (List.mem_cons_of_mem _ hm)
    · exact fun ann hm => hannFreeze ann (List.mem_cons_of_mem _ hm)
    · exact fun rhs hm => hrhsFreeze rhs (List.mem_cons_of_mem _ hm)
    · exact fun ann hm => hcandAnn ann (List.mem_cons_of_mem _ hm)
    · exact fun rhs hm => hcandRhs rhs (List.mem_cons_of_mem _ hm)
    · intro j scheme rhs ha hb
      exact hcandidate (j + 1) scheme rhs (by simpa only [List.getElem?_cons_succ] using ha)
        (by simpa only [List.getElem?_cons_succ] using hb)
  | .cons hwf hraw hi hu hescape hr =>
    expose_names
    have hiCtxWF := hstateLC.rhsCtx hctxWF
    have hiCtxB := hstateB.rhsCtx hctx
    have hheadAnn : ∀ v ∈ scheme.body.freeVars, v ∈ K ++ softVars F :=
      hannScope _ List.mem_cons_self
    obtain ⟨L, htypes⟩ := hcandidate 0 scheme rhs rfl rfl
    have htypes' : ∃ L, ∀ Ys, FreshNames L scheme.paramCount Ys →
        Typing (P ++ Ys) (R.onCtx (state.rhsCtx ctx)) ((rhs.substTyFvars R).openTyVars Ys)
          ((R.onPolyTy scheme).openVars Ys) :=
      ⟨L, fun Ys hy => hres.weaken_from_body hlen hpoly hdone (htypes Ys hy)⟩
    obtain ⟨U, hU, hUP, hag⟩ := Infer.signed_check_factor hwf hheadAnn hraw hi hu
      (by
        have he := hescape
        rw [RecState.rhsCtx_onSubst] at he
        simpa only [Subst.onCtx_append] using he)
      (hInfer (by simp only [Input.size_openTyVars, sizeBindings]; omega) hi)
      hiCtxWF hiCtxB hK hF hres.lc hP hres.fixes
      (by
        intro v hv hk hn
        simp only [Input.rigidVars, LetAnn.rigidVars, List.mem_append, List.not_mem_nil, or_false] at hv
        exact hv.elim (fun hv => hannFreeze _ List.mem_cons_self v hv hk hn)
          (fun hv => hrhsFreeze _ List.mem_cons_self v hv hk hn))
      (hcandAnn _ List.mem_cons_self) (hcandRhs _ List.mem_cons_self) htypes'
    let checked := (state.onSubst (s1 ++ s2)).setSigned index (freshVars frontier scheme.paramCount)
      (output.substTyFvars s2) (bodyFacts.onSubst s2)
    have hstep : InferRecSigned K F index frontier ctx [.complete scheme] [rhs] state first
        ((s1 ++ s2) ++ []) checked := .cons hwf hraw hi hu hescape .nil
    have hstep' : InferRecSigned K F index frontier ctx [.complete scheme] [rhs] state first
        (s1 ++ s2) checked := by simpa only [List.append_nil] using hstep
    have hle := hstep'.frontier_le
    obtain ⟨hbothLC, hcheckedLC⟩ := hstep'.lc_of_infer (fun _ hi hc => hi.lc hc) hctxWF hstateLC
    obtain ⟨hbothB, hcheckedB⟩ := hstep'.belowFvars_of_infer
      (fun _ hi hc hk hf => hi.belowFvars hc hk hf) hctx hK hF hstateB
      (by
        intro ann ha v hv
        rcases List.mem_singleton.mp ha with rfl
        exact (List.mem_append.mp (hheadAnn v hv)).elim (hK v) (softVars_lt hF v))
    have hbothFix : ∀ k ∈ K, (s1 ++ s2).onTy (.fvar k) = .fvar k :=
      Subst.fixes_of_dom_avoids hstep'.dom_avoids
    have hctxChecked := Subst.onCtx_below hbothB hle hctx
    have hresChecked : RecResidual P declCtx declSpecs declPrefixes declPool Xs
        ((s1 ++ s2).onCtx ctx) checked done U :=
      residual_congr_types (hres.onSubst_of_agreesBelow hstateB hctx hag hU hUP) rfl rfl
    have hannBelow : ∀ ann ∈ (.complete scheme :: anns_1), ∀ v ∈ ann.rigidVars, v < frontier :=
      fun ann ha v hv => (List.mem_append.mp (hannScope ann ha v hv)).elim (hK v) (softVars_lt hF v)
    have hrhsBelow : ∀ term ∈ (rhs :: bindings_1), ∀ v ∈ term.rigidVars, v < frontier :=
      fun term hm v hv => (List.mem_append.mp (hrhsScope term hm v hv)).elim (hK v) (softVars_lt hF v)
    have annEq : ∀ ann ∈ (.complete scheme :: anns_1),
        (ann.substTyFvars (s1 ++ s2)).substTyFvars U = ann.substTyFvars R := by
      intro ann hm
      rw [← LetAnn.substTyFvars_append]
      exact ann.substTyFvars_congr (fun v hv => (hag v (hannBelow ann hm v hv)).symm)
    have rhsEq : ∀ term ∈ (rhs :: bindings_1),
        (term.substTyFvars (s1 ++ s2)).substTyFvars U = term.substTyFvars R := by
      intro term hm
      rw [← Input.substTyFvars_append]
      exact term.substTyFvars_congr (fun v hv => (hag v (hrhsBelow term hm v hv)).symm)
    have hpolyChecked : ∀ (i : Nat) (scheme : PolyTy), checked.specs[i]? = some (.poly scheme) →
        checked.exports[i]? = some (some scheme) := by
      intro i sigma hs
      change (state.specs.map (RecSpec.onSubstSource (s1 ++ s2)))[i]? = some (.poly sigma) at hs
      rw [List.getElem?_map] at hs
      obtain ⟨spec, hold, heq⟩ := Option.map_eq_some_iff.mp hs
      cases spec with
      | mono ty => cases heq
      | poly old =>
        change RecSpec.poly ((s1 ++ s2).onPolyTy old) = RecSpec.poly sigma at heq
        cases heq
        simp only [checked, RecState.setSigned, RecState.onSubst, List.getElem?_map,
          hpoly i old hold, Option.map_some]
    obtain ⟨V, hV, hVP, hagTail, hresFinal⟩ := hr.sourcePrincipal_residual
      (fun he hi => hInfer (by simp only [sizeBindings_map_substTyFvars] at he; simp only [sizeBindings]; omega) hi)
      hresChecked (Subst.onCtx_wf hbothLC hctxWF) hctxChecked hcheckedLC hcheckedB
      (fun k hk => (hK k hk).trans_le hle) (substSoft_below hbothB hle hF)
      (fun p hp => (hP p hp).trans_le hle)
      (by simpa only [checked, RecState.setSigned, RecState.onSubst, List.length_map] using hlen)
      hpolyChecked
      (by
        intro i ty hs
        obtain ⟨old, hold, _⟩ := RecSpec.mono_getElem?_map_onSubstSource hs
        exact hdone i old hold)
      (by
        intro ann hm v hv
        obtain ⟨old, ho, rfl⟩ := List.mem_map.mp hm
        obtain ⟨original, horiginal, himage⟩ := LetAnn.rigidVars_substTyFvars hv
        exact scope_image hbothFix (hannScope old (List.mem_cons_of_mem _ ho) original horiginal) himage)
      (by
        intro rhs hm
        obtain ⟨old, ho, rfl⟩ := List.mem_map.mp hm
        exact (hrhsScope old (List.mem_cons_of_mem _ ho)).subst _ hbothFix)
      (by
        intro ann hm
        obtain ⟨old, ho, rfl⟩ := List.mem_map.mp hm
        exact signed_ann_freeze (hannScope old (List.mem_cons_of_mem _ ho))
          (hannBelow old (List.mem_cons_of_mem _ ho)) hbothFix
          (hannFreeze old (List.mem_cons_of_mem _ ho)) hag)
      (by
        intro rhs hm
        obtain ⟨old, ho, rfl⟩ := List.mem_map.mp hm
        exact (hrhsScope old (List.mem_cons_of_mem _ ho)).residual_freeze
          (hrhsBelow old (List.mem_cons_of_mem _ ho)) hbothFix
          (hrhsFreeze old (List.mem_cons_of_mem _ ho)) hag)
      (by
        intro ann hm v hv
        obtain ⟨old, ho, rfl⟩ := List.mem_map.mp hm
        rw [annEq old (List.mem_cons_of_mem _ ho)] at hv
        exact hcandAnn old (List.mem_cons_of_mem _ ho) v hv)
      (by
        intro rhs hm v hv
        obtain ⟨old, ho, rfl⟩ := List.mem_map.mp hm
        rw [rhsEq old (List.mem_cons_of_mem _ ho)] at hv
        exact hcandRhs old (List.mem_cons_of_mem _ ho) v hv)
      (by
        intro j sigma rhs' ha hb
        rw [List.getElem?_map] at ha hb
        obtain ⟨ann, ho, heq⟩ := Option.map_eq_some_iff.mp ha
        obtain ⟨oldRhs, hro, rfl⟩ := Option.map_eq_some_iff.mp hb
        cases ann with
        | absent | template _ | partialForall _ _ => cases heq
        | complete old =>
          cases heq
          obtain ⟨L, htypes⟩ := hcandidate (j + 1) old oldRhs
            (by simpa only [List.getElem?_cons_succ] using ho)
            (by simpa only [List.getElem?_cons_succ] using hro)
          refine ⟨L, ?_⟩
          intro Ys hy
          have hσ : U.onPolyTy ((s1 ++ s2).onPolyTy old) = R.onPolyTy old := by
            apply congrArg (PolyTy.mk old.paramCount)
            change U.onTy ((s1 ++ s2).onTy old.body) = R.onTy old.body
            simpa only [Subst.onTy_append] using (Subst.onTy_congr hag
              (Ty.BelowFvars.of_freeVars_lt (hannBelow _ (List.mem_cons_of_mem _ (List.mem_of_getElem? ho))))).symm
          rw [rhsEq oldRhs (List.mem_cons_of_mem _ (List.mem_of_getElem? hro))]
          change Typing (P ++ Ys) (recBodyCtx declCtx declSpecs declPrefixes declPool)
            ((oldRhs.substTyFvars R).openTyVars Ys)
            ((U.onPolyTy ((s1 ++ s2).onPolyTy old)).openVars Ys)
          rw [hσ]
          exact htypes Ys hy)
    refine ⟨V, hV, hVP, ?_, ?_⟩
    · simpa only [List.append_assoc] using Subst.AgreesBelow.trans_append hle hag hbothB hagTail
    · simpa only [Subst.onCtx_append, List.append_assoc] using hresFinal
termination_by structural h


/-- Allocate the actual recursion seeds against unrestricted candidate pool
openings while retaining ambient behavior on every pre-existing variable. -/
theorem RecResidual.init
    {P G Xs : List Nat} {declPrefixes : List (List Nat)} {frontier : Nat} {ctx : Ctx}
    {anns : List LetAnn} {bindings : List Expr} {declSpecs : List RecSpec} {ambient : Subst}
    (hwf : RecSpecs.WF ((anns.map (LetAnn.substTyFvars ambient)).map LetAnn.recModeAnn)
      bindings declSpecs G)
    (hambient : ∀ pair ∈ ambient, pair.2.IsLC)
    (hP : ∀ p ∈ P, p < frontier)
    (hfixP : ∀ p ∈ P, ambient.onTy (.fvar p) = .fvar p)
    (hanns : ∀ ann ∈ anns, ∀ v ∈ ann.rigidVars, v < frontier)
    (hctx : CtxBelow frontier ctx) :
    ∃ U : Subst, (∀ pair ∈ U, pair.2.IsLC) ∧ Subst.AgreesBelow frontier ambient U ∧
      (∀ p ∈ P, U.onTy (.fvar p) = .fvar p) ∧
      RecResidual P (ambient.onCtx ctx) declSpecs declPrefixes G Xs ctx
        (RecState.init frontier anns) [] U := by
  let target : RecSpec → Ty := fun spec => match spec with
    | .mono ty => Ty.renameG G Xs ty
    | .poly _ => .prim .unit
  have htarget : ∀ ty ∈ declSpecs.map target, ty.IsLC := by
    intro ty hm
    obtain ⟨spec, hs, rfl⟩ := List.mem_map.mp hm
    cases spec with
    | poly scheme => exact .prim
    | mono ty =>
      change Subst.onTy (G.zip (Xs.map Ty.fvar)) ty |>.IsLC
      apply Subst.onTy_lc ?_ (hwf.mono_lc ty hs)
      intro pair hp
      obtain ⟨v, _, heq⟩ := List.mem_map.mp (List.of_mem_zip hp).2
      rw [← heq]
      exact .fvar
  obtain ⟨U, hU, hag, hblock⟩ := Subst.override_block hambient frontier (declSpecs.map target) htarget
  have hUP : ∀ p ∈ P, U.onTy (.fvar p) = .fvar p :=
    fun p hp => (hag p (hP p hp)).symm.trans (hfixP p hp)
  have hmodes : declSpecs.map RecSpec.ann =
      (anns.map LetAnn.recModeAnn).map (Option.map ambient.onPolyTy) := by
    rw [hwf.anns_eq]
    simp only [List.map_map, Function.comp_def, LetAnn.recModeAnn_subst_source]
  have hlen : declSpecs.length = anns.length := by
    have he := congrArg List.length hmodes
    simpa only [List.length_map] using he
  have hInitModes : (RecState.init frontier anns).specs.map RecSpec.ann =
      anns.map LetAnn.recModeAnn := RecSpec.map_ann_init frontier _
  have modeOf : ∀ (i : Nat) (spec : RecSpec),
      (RecState.init frontier anns).specs[i]? = some spec →
      (anns.map LetAnn.recModeAnn)[i]? = some spec.ann := by
    intro i spec hi
    rw [← hInitModes, List.getElem?_map, hi, Option.map_some]
  have declMono : ∀ (i : Nat), (anns.map LetAnn.recModeAnn)[i]? = some none →
      ∃ ty, declSpecs[i]? = some (.mono ty) := by
    intro i hi
    have hib : i < declSpecs.length := by
      have hb := (List.getElem?_eq_some_iff.mp hi).1
      simp only [List.length_map] at hb
      omega
    have hd := List.getElem?_eq_getElem hib
    have hm := congrArg (fun l : List (Option PolyTy) => l[i]?) hmodes
    simp only [List.getElem?_map, hd, hi, Option.map_some, Option.map_none] at hm
    cases hs : declSpecs[i] with
    | mono ty => exact ⟨ty, hs ▸ hd⟩
    | poly scheme => simp only [hs, RecSpec.ann] at hm; cases hm
  have declPoly : ∀ (i : Nat) (scheme : PolyTy),
      (anns.map LetAnn.recModeAnn)[i]? = some (some scheme) →
      declSpecs[i]? = some (.poly (ambient.onPolyTy scheme)) := by
    intro i scheme hi
    have hib : i < declSpecs.length := by
      have hb := (List.getElem?_eq_some_iff.mp hi).1
      simp only [List.length_map] at hb
      omega
    have hd := List.getElem?_eq_getElem hib
    have hm := congrArg (fun l : List (Option PolyTy) => l[i]?) hmodes
    simp only [List.getElem?_map, hd, hi, Option.map_some] at hm
    cases hs : declSpecs[i] with
    | mono ty => simp only [hs, RecSpec.ann] at hm; cases hm
    | poly old =>
      simp only [hs, RecSpec.ann, Option.some.injEq] at hm
      rw [hs, hm] at hd
      exact hd
  have rawPolyBelow : ∀ scheme, some scheme ∈ anns.map LetAnn.recModeAnn →
      Ty.BelowFvars frontier scheme.body := by
    intro scheme hm
    obtain ⟨ann, ha, heq⟩ := List.mem_map.mp hm
    cases ann with
    | absent | template _ | partialForall _ _ => cases heq
    | complete old =>
      cases heq
      exact Ty.BelowFvars.of_freeVars_lt (hanns _ ha)
  refine ⟨U, hU, hag, hUP, ?_⟩
  refine ⟨hU, hUP, (Subst.onCtx_congr hag hctx).symm, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [RecState.init, RecSpec.init_length, List.length_map] using hlen.symm
  · intro i algTy hi
    exact declMono i (modeOf i _ hi)
  · intro i algScheme hi
    have hm := modeOf i _ hi
    have hd := declPoly i algScheme hm
    refine ⟨ambient.onPolyTy algScheme, hd, ?_⟩
    apply congrArg (PolyTy.mk algScheme.paramCount)
    exact (Subst.onTy_congr hag (rawPolyBelow algScheme (List.mem_of_getElem? hm))).symm
  · intro i algTy declTy hi hd hnot
    have hm := modeOf i _ hi
    have hseed : algTy = .fvar (frontier + i) := by
      change (RecSpec.init frontier (anns.map LetAnn.recModeAnn))[i]? = some (.mono algTy) at hi
      rw [RecSpec.init_getElem?, hm] at hi
      cases hi
      rfl
    rw [hseed]
    have hib := (List.getElem?_eq_some_iff.mp hd).1
    have hh := hblock i (by simpa only [List.length_map] using hib)
    simpa only [List.getElem_map, (List.getElem?_eq_some_iff.mp hd).2, target] using hh
  · intro i algTy declTy hi hd hdone
    cases hdone


theorem RecResidual.close_aligned_component
    {K P G Xs done members : List Nat} {F localF : List Ty} {frontier next : Nat}
    {ctx declCtx : Ctx} {state exported : RecState} {bindings : List Input}
    {shapes : List RecShape} {pre current R : Subst}
    {outputs : List (Option Expr)} {facts : List RecFacts}
    {declSpecs : List RecSpec} {declPrefixes : List (List Nat)}
    (hshape : CheckRecShapes K shapes pre)
    (hcomponent : InferRecComponent K (substSoft pre (F ++ localF)) members 0 frontier
      (pre.onCtx (state.rhsCtx ctx)) (bindings.map (Input.substTyFvars pre))
      (state.specs.map (RecSpec.onSubstSource pre)) next current outputs facts)
    (hfinish : FinishRecComponent K (softVars (substSoft (pre ++ current) F)) members
      ((pre ++ current).onCtx ctx) (state.onSubst (pre ++ current)) outputs facts exported)
    (hInfer : ∀ {κ F' Ψ c e Ψ' T output ty}, e.size ≤ sizeBindings bindings →
      (hi : Infer κ F' Ψ c e Ψ' T output ty) → Infer.SourcePrincipal hi)
    (hres : RecResidual P declCtx declSpecs declPrefixes G Xs ctx state done R)
    (hstateLC : state.LC) (hstateB : state.Below frontier)
    (hctxWF : CtxWF ctx) (hctx : CtxBelow frontier ctx)
    (hK : ∀ k ∈ K, k < frontier) (hF : ∀ t ∈ F ++ localF, Ty.BelowFvars frontier t)
    (hP : ∀ p ∈ P, p < frontier)
    (hpreLC : ∀ pair ∈ pre, pair.2.IsLC)
    (hpreB : ∀ pair ∈ pre, Ty.BelowFvars frontier pair.2)
    (hsource : ∀ rhs ∈ bindings, SourceScope K (F ++ localF) rhs)
    (hsolve : ∀ ty expected, (ty, some expected) ∈ shapes → R.onTy ty = R.onTy expected)
    (hfreeze : ∀ (i : Nat) (rhs : Input), i ∈ members → bindings[i]? = some rhs →
      ∀ v ∈ rhs.rigidVars, v ∈ K → v ∉ softVars (F ++ localF) → R.onTy (.fvar v) = .fvar v)
    (hcandidate : ∀ (i : Nat) (rhs : Input) (ty : Ty), i ∈ members →
      bindings[i]? = some rhs → state.specs[i]? = some (.mono ty) →
      Typing P (R.onCtx (state.rhsCtx ctx)) (rhs.substTyFvars R) (R.onTy ty))
    (hexports : state.exports.length = state.specs.length)
    (hdisjoint : ∀ i ∈ members, i ∉ done)
    (hdeclLC : ∀ ty, .mono ty ∈ declSpecs → ty.IsLC)
    (hG : G.Nodup)
    (hprefix : ∀ (i : Nat) (ty : Ty), declSpecs[i]? = some (.mono ty) →
      (declPrefixes[i]?.getD []).Nodup ∧ ∀ v ∈ declPrefixes[i]?.getD [], v ∈ G)
    (hXsLen : Xs.length = G.length) (hXsND : Xs.Nodup)
    (hGXs : ∀ g ∈ G, g ∉ Xs)
    (hXsTypes : ∀ x ∈ Xs, ∀ ty, .mono ty ∈ declSpecs → x ∉ ty.freeVars)
    (hXsCtx : ∀ x ∈ Xs, x ∉ (R.onCtx (state.fixedCtx ctx)).env.freeVars)
    (hXsK : ∀ x ∈ Xs, ∀ k ∈ K, x ∉ (R.onTy (.fvar k)).freeVars)
    (hXsF : ∀ x ∈ Xs, x ∉ softVars (substSoft R F)) :
    ∃ V : Subst, (∀ pair ∈ V, pair.2.IsLC) ∧
      (∀ p ∈ P, V.onTy (.fvar p) = .fvar p) ∧
      Subst.AgreesBelow frontier R ((pre ++ current) ++ V) ∧
      RecResidual P declCtx declSpecs declPrefixes G Xs ((pre ++ current).onCtx ctx)
        exported (done ++ members) V := by
  obtain ⟨V, hV, hVP, hag⟩ := InferRecComponent.sourcePrincipal_after_shapes hshape hcomponent hInfer
    (hstateLC.rhsCtx hctxWF) (hstateB.rhsCtx hctx) hK hF hstateLC.1 hstateB.1
    hsource hpreLC hpreB R P hres.lc hP hres.fixes hsolve
    (by simpa only [Nat.zero_add] using hfreeze)
    (by simpa only [Nat.zero_add] using hcandidate)
  have hag' : Subst.AgreesBelow frontier R ((pre ++ current) ++ V) := by
    simpa only [List.append_assoc] using hag
  have hcurrentLC := hcomponent.lc_of_infer (fun _ hi => hi.lc)
    (Subst.onCtx_wf hpreLC (hstateLC.rhsCtx hctxWF)) (hstateLC.onSubst hpreLC).1
  have hbothLC : ∀ pair ∈ pre ++ current, pair.2.IsLC :=
    fun pair hp => (List.mem_append.mp hp).elim (hpreLC pair) (hcurrentLC pair)
  have hsolvedStateLC := hstateLC.onSubst hbothLC
  have hpostRes := hres.onSubst_of_agreesBelow hstateB hctx hag' hV hVP
  have hsolvedFix : ∀ k ∈ K, (pre ++ current).onTy (.fvar k) = .fvar k :=
    Subst.fixes_of_dom_avoids (fun pair hp hk => (List.mem_append.mp hp).elim
      (fun hp => hshape.dom_avoids pair hp hk) (fun hp => hcomponent.dom_avoids pair hp hk))
  have hFreshMono : ∀ (i : Nat) (ty : Ty) (scheme : PolyTy), i ∈ members →
      (state.onSubst (pre ++ current)).specs[i]? = some (.mono ty) →
      exported.exports[i]? = some (some scheme) →
      ∀ x ∈ Xs, x ∉ (V.onPolyTy scheme).body.freeVars := by
    intro i ty scheme hi ht he
    exact hfinish.export_fresh_of_agrees (RecState.fixedCtx_onSubst state (pre ++ current) ctx)
      (hstateB.fixedCtx hctx) hK (fun t ht => hF t (List.mem_append_left _ ht)) hsolvedFix hag'
      hXsCtx hXsK hXsF hi ht he
  refine ⟨V, hV, hVP, hag', ?_⟩
  cases hfinish with
  | @mk written hresolve =>
    have hwrite : ∀ (i : Nat) (ty : Ty), (state.onSubst (pre ++ current)).specs[i]? = some (.mono ty) →
        i ∈ members → i < (state.onSubst (pre ++ current)).exports.length := by
      intro i ty hi _
      have hib := (List.getElem?_eq_some_iff.mp hi).1
      simpa only [RecState.onSubst, List.length_map, hexports] using hib
    apply hpostRes.exportComponent hdisjoint hwrite
    intro i algTy declTy hi hd hm
    have hAlgLC : algTy.IsLC := hsolvedStateLC.1 _ (List.mem_of_getElem? hi)
    have hDeclLC := hdeclLC declTy (List.mem_of_getElem? hd)
    obtain ⟨hwND, hwG⟩ := hprefix i declTy hd
    apply recScheme_generalizes_of_renameG hAlgLC hDeclLC hV hG hwND hwG
      hXsLen hXsND hGXs (fun x hx => hXsTypes x hx declTy (List.mem_of_getElem? hd))
      (hpostRes.pending i algTy declTy hi hd (hdisjoint i hm))
    exact hFreshMono i algTy _ hm hi (residual_export_selected (hwrite i algTy hi hm) hm hi)


set_option maxHeartbeats 2000000 in
theorem RecResidual.close_opened_component
    {K P G Xs done members : List Nat} {F : List Ty} {frontier opened next : Nat}
    {ctx declCtx : Ctx} {state exported : RecState} {anns : List LetAnn} {bindings : List Input}
    {openings : List RecOpening} {pre current R : Subst}
    {outputs : List (Option Expr)} {facts : List RecFacts}
    {declSpecs : List RecSpec} {declPrefixes : List (List Nat)}
    (ho : OpenRecAnns members 0 frontier anns opened openings)
    (hp : CheckRecShapes K ((state.installOpenings members openings).shapes members openings) pre)
    (hc : InferRecComponent K
      (substSoft pre (F ++ (openings.flatMap RecOpening.written).map Ty.fvar)) members 0 opened
      (((state.installOpenings members openings).onSubst pre).rhsCtx (pre.onCtx ctx))
      ((openRecSources openings bindings).map (Input.substTyFvars pre))
      ((state.installOpenings members openings).onSubst pre).specs next current outputs facts)
    (hf : FinishRecComponent K (softVars (substSoft (pre ++ current) F)) members
      ((pre ++ current).onCtx ctx) ((state.installOpenings members openings).onSubst (pre ++ current))
      outputs facts exported)
    (hInfer : ∀ {κ F' Ψ c e Ψ' T output ty}, e.size ≤ sizeBindings bindings →
      (hi : Infer κ F' Ψ c e Ψ' T output ty) → Infer.SourcePrincipal hi)
    (hres : RecResidual P declCtx declSpecs declPrefixes G Xs ctx state done R)
    (hstateLC : state.LC) (hstateB : state.Below frontier)
    (hctxWF : CtxWF ctx) (hctx : CtxBelow frontier ctx)
    (hK : ∀ k ∈ K, k < frontier) (hF : ∀ t ∈ F, Ty.BelowFvars frontier t)
    (hP : ∀ p ∈ P, p < opened)
    (hlen : anns.length = bindings.length)
    (hanns : ∀ ann ∈ anns, ∀ v ∈ ann.rigidVars, v ∈ K ++ softVars F)
    (hrhs : ∀ rhs ∈ bindings, SourceScope K F rhs)
    (hfreeze : ∀ (i : Nat) (rhs : Input), i ∈ members → bindings[i]? = some rhs →
      ∀ v ∈ rhs.rigidVars, v ∈ K → v ∉ softVars F → R.onTy (.fvar v) = .fvar v)
    (hsolve : ∀ (i : Nat) (opening : RecOpening) (ty expected : Ty), i ∈ members →
      openings[i]? = some opening → state.specs[i]? = some (.mono ty) →
      opening.expected = some expected → R.onTy expected = R.onTy ty)
    (hcandidate : ∀ (i : Nat) (rhs : Input) (ty : Ty), i ∈ members →
      (openRecSources openings bindings)[i]? = some rhs → state.specs[i]? = some (.mono ty) →
      Typing P (R.onCtx (state.rhsCtx ctx)) (rhs.substTyFvars R) (R.onTy ty))
    (hexports : state.exports.length = state.specs.length)
    (hdisjoint : ∀ i ∈ members, i ∉ done)
    (hdeclLC : ∀ ty, .mono ty ∈ declSpecs → ty.IsLC)
    (hG : G.Nodup)
    (hprefix : ∀ (i : Nat) (ty : Ty), declSpecs[i]? = some (.mono ty) →
      (declPrefixes[i]?.getD []).Nodup ∧ ∀ v ∈ declPrefixes[i]?.getD [], v ∈ G)
    (hXsLen : Xs.length = G.length) (hXsND : Xs.Nodup)
    (hGXs : ∀ g ∈ G, g ∉ Xs)
    (hXsTypes : ∀ x ∈ Xs, ∀ ty, .mono ty ∈ declSpecs → x ∉ ty.freeVars)
    (hXsCtx : ∀ x ∈ Xs, x ∉ (R.onCtx (state.fixedCtx ctx)).env.freeVars)
    (hXsK : ∀ x ∈ Xs, ∀ k ∈ K, x ∉ (R.onTy (.fvar k)).freeVars)
    (hXsF : ∀ x ∈ Xs, x ∉ softVars (substSoft R F)) :
    ∃ V : Subst, (∀ pair ∈ V, pair.2.IsLC) ∧
      (∀ p ∈ P, V.onTy (.fvar p) = .fvar p) ∧
      Subst.AgreesBelow opened R ((pre ++ current) ++ V) ∧
      RecResidual P declCtx declSpecs declPrefixes G Xs ((pre ++ current).onCtx ctx)
        exported (done ++ members) V := by
  let localF := (openings.flatMap RecOpening.written).map Ty.fvar
  have hle := ho.frontier_le
  have hinstLC := hstateLC.installOpenings (members := members) (openings := openings)
  have hinstB := hstateB.installOpenings ho
  have hinstRes : RecResidual P declCtx declSpecs declPrefixes G Xs ctx
      (state.installOpenings members openings) done R := residual_congr_types hres rfl rfl
  have hannBelow : ∀ ann ∈ anns, ∀ v ∈ ann.rigidVars, v < frontier := by
    intro ann ha v hv
    exact (List.mem_append.mp (hanns ann ha v hv)).elim (hK v) (softVars_lt hF v)
  have hpreLC := hp.lc (RecState.shapes_lc hinstLC ho.expected_lc)
  have hpreB := hp.belowFvars (RecState.shapes_below hinstB (ho.expected_below hannBelow))
  have hactiveB : ∀ t ∈ F ++ localF, Ty.BelowFvars opened t := by
    intro t ht
    rcases List.mem_append.mp ht with ht | ht
    · exact (hF t ht).mono hle
    · obtain ⟨v, hv, rfl⟩ := List.mem_map.mp ht
      exact .fvar (ho.written_range v hv).2
  have hwritten : ∀ (i v : Nat), v ∈ ((openings[i]?).getD RecOpening.empty).written →
      v ∈ openings.flatMap RecOpening.written := by
    intro i v hv
    cases he : openings[i]? with
    | none => simp only [he, Option.getD_none, RecOpening.empty, List.not_mem_nil] at hv
    | some opening =>
      simp only [he, Option.getD_some] at hv
      exact List.mem_flatMap.mpr ⟨opening, List.mem_of_getElem? he, hv⟩
  have hsoftIncl : ∀ v ∈ softVars F, v ∈ softVars (F ++ localF) := by
    intro v hv
    obtain ⟨t, ht, hv⟩ := TyList.mem_freeVars_iff.mp hv
    exact TyList.mem_freeVars_iff.mpr ⟨t, List.mem_append_left _ ht, hv⟩
  have hrootSoft : ∀ v ∈ openings.flatMap RecOpening.written, v ∈ softVars (F ++ localF) := by
    intro v hv
    exact TyList.mem_freeVars_iff.mpr ⟨.fvar v, List.mem_append_right _ (List.mem_map.mpr ⟨v, hv, rfl⟩), by simp [Ty.freeVars]⟩
  have hsource : ∀ rhs ∈ openRecSources openings bindings, SourceScope K (F ++ localF) rhs := by
    intro rhs hm v hv
    obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hm
    obtain ⟨raw, hraw, rfl⟩ := openRecSources_getElem? (ho.length.trans hlen) hi
    rcases Input.rigidVars_openTyVarsFrom hv with hv | hv
    · rcases List.mem_append.mp (hrhs raw (List.mem_of_getElem? hraw) v hv) with hk | hs
      · exact List.mem_append_left _ hk
      · exact List.mem_append_right _ (hsoftIncl v hs)
    · exact List.mem_append_right _ (hrootSoft v (hwritten i v hv))
  have hfreezeOpened : ∀ (i : Nat) (rhs : Input), i ∈ members →
      (openRecSources openings bindings)[i]? = some rhs →
      ∀ v ∈ rhs.rigidVars, v ∈ K → v ∉ softVars (F ++ localF) → R.onTy (.fvar v) = .fvar v := by
    intro i rhs hi hr v hv hk hn
    obtain ⟨raw, hraw, rfl⟩ := openRecSources_getElem? (ho.length.trans hlen) hr
    rcases Input.rigidVars_openTyVarsFrom hv with hv | hv
    · exact hfreeze i raw hi hraw v hv hk (fun hs => hn (hsoftIncl v hs))
    · exact False.elim (hn (hrootSoft v (hwritten i v hv)))
  have hsolveShapes : ∀ ty expected,
      (ty, some expected) ∈ (state.installOpenings members openings).shapes members openings →
      R.onTy ty = R.onTy expected := by
    intro ty expected hm
    change (ty, some expected) ∈ state.shapes members openings at hm
    obtain ⟨i, hi, he⟩ := List.mem_filterMap.mp hm
    cases hs : state.specs[i]? with
    | none => simp [hs] at he
    | some spec =>
      cases spec with
      | poly scheme => simp [RecSpec.monoTy?, hs] at he
      | mono actual =>
        cases hop : openings[i]? with
        | none => simp [hs, RecSpec.monoTy?, hop] at he
        | some opening =>
          simp [hs, RecSpec.monoTy?, hop] at he
          obtain ⟨rfl, hexpected⟩ := he
          exact (hsolve i opening actual expected hi hop hs hexpected).symm
  apply RecResidual.close_aligned_component hp
    (by simpa only [RecState.rhsCtx_onSubst] using hc) hf
    (fun he hi => hInfer (by simpa only [sizeBindings_openRecSources] using he) hi)
    hinstRes hinstLC hinstB hctxWF
    (fun M hm => (hctx M hm).mono hle)
    (fun k hk => (hK k hk).trans_le hle) hactiveB hP hpreLC hpreB hsource hsolveShapes
    hfreezeOpened hcandidate hexports hdisjoint hdeclLC hG hprefix hXsLen hXsND hGXs hXsTypes
    hXsCtx hXsK hXsF

private theorem _root_.InferRecStrata.sourcePrincipal_residual_of_step
    {P G Xs : List Nat} {declCtx : Ctx} {declAnns : List LetAnn}
    {declBindings : List Input} {declSpecs : List RecSpec}
    {declPrefixes : List (List Nat)} {cutoff base : Nat}
    {K : List Nat} {F : List Ty} {frontier next : Nat} {ctx : Ctx}
    {anns : List LetAnn} {bindings : List Input} {state final : RecState}
    {past groups : List (List Nat)} {S R : Subst}
    (hStep : ∀ {K : List Nat} {F : List Ty} {frontier opened first : Nat}
      {ctx : Ctx} {anns : List LetAnn} {bindings : List Input}
      {state exported : RecState} {past rest : List (List Nat)} {component : List Nat}
      {openings : List RecOpening} {pre current R : Subst}
      {outputs : List (Option Expr)} {facts : List RecFacts},
      OpenRecAnns component 0 frontier anns opened openings →
      CheckRecShapes K ((state.installOpenings component openings).shapes component openings) pre →
      InferRecComponent K
        (substSoft pre (F ++ (openings.flatMap RecOpening.written).map Ty.fvar)) component 0 opened
        (((state.installOpenings component openings).onSubst pre).rhsCtx (pre.onCtx ctx))
        ((openRecSources openings bindings).map (Input.substTyFvars pre))
        ((state.installOpenings component openings).onSubst pre).specs first current outputs facts →
      FinishRecComponent K (softVars (substSoft (pre ++ current) F)) component
        ((pre ++ current).onCtx ctx) ((state.installOpenings component openings).onSubst (pre ++ current))
        outputs facts exported →
      (∀ {κ F' Ψ c e Ψ' T output ty}, e.size ≤ sizeBindings bindings →
        (hi : Infer κ F' Ψ c e Ψ' T output ty) → Infer.SourcePrincipal hi) →
      first ≤ cutoff →
      RecGroups.ValidResidualGroups (anns.map LetAnn.recModeAnn) (bindings.map Input.erase)
        (past ++ component :: rest) →
      past ++ component :: rest = RecGroup.inferenceSccs
        (anns.map LetAnn.recModeAnn) (bindings.map Input.erase) →
      state.Frame base K F ctx anns past.flatten →
      state.LC → state.Below frontier → CtxWF ctx → CtxBelow frontier ctx →
      base + bindings.length ≤ frontier →
      (∀ k ∈ K, k < frontier) → (∀ t ∈ F, Ty.BelowFvars frontier t) →
      (∀ p ∈ P, p < frontier) →
      RecResidual P declCtx declSpecs declPrefixes G Xs ctx state past.flatten R →
      (∀ x ∈ Xs, ∀ k ∈ K, x ∉ (R.onTy (.fvar k)).freeVars) →
      (∀ x ∈ Xs, x ∉ softVars (substSoft R F)) →
      (∀ ann ∈ anns, ∀ v ∈ ann.rigidVars, v ∈ K ++ softVars F) →
      (∀ rhs ∈ bindings, SourceScope K F rhs) →
      anns.map (LetAnn.substTyFvars R) = declAnns →
      bindings.map (Input.substTyFvars R) = declBindings →
      (∀ ann ∈ anns, ∀ v ∈ ann.rigidVars,
        v ∈ K → v ∉ softVars F → R.onTy (.fvar v) = .fvar v) →
      (∀ rhs ∈ bindings, ∀ v ∈ rhs.rigidVars,
        v ∈ K → v ∉ softVars F → R.onTy (.fvar v) = .fvar v) →
      ∃ U : Subst, (∀ pair ∈ U, pair.2.IsLC) ∧
        (∀ p ∈ P, U.onTy (.fvar p) = .fvar p) ∧
        Subst.AgreesBelow frontier R ((pre ++ current) ++ U) ∧
        RecResidual P declCtx declSpecs declPrefixes G Xs ((pre ++ current).onCtx ctx)
          exported (past.flatten ++ component) U)
    (h : InferRecStrata K F frontier ctx anns bindings state groups next S final)
    (hInfer : ∀ {κ F' Ψ c e Ψ' T output ty}, e.size ≤ sizeBindings bindings →
      (hi : Infer κ F' Ψ c e Ψ' T output ty) → Infer.SourcePrincipal hi)
    (hcutoff : next ≤ cutoff)
    (hvalid : RecGroups.ValidResidualGroups (anns.map LetAnn.recModeAnn) (bindings.map Input.erase)
      (past ++ groups))
    (hcanonical : past ++ groups = RecGroup.inferenceSccs
      (anns.map LetAnn.recModeAnn) (bindings.map Input.erase))
    (hframe : state.Frame base K F ctx anns past.flatten)
    (hstateLC : state.LC) (hstateB : state.Below frontier)
    (hctxWF : CtxWF ctx) (hctx : CtxBelow frontier ctx)
    (hbase : base + bindings.length ≤ frontier)
    (hK : ∀ k ∈ K, k < frontier) (hF : ∀ t ∈ F, Ty.BelowFvars frontier t)
    (hP : ∀ p ∈ P, p < frontier)
    (hres : RecResidual P declCtx declSpecs declPrefixes G Xs ctx state past.flatten R)
    (hXsK : ∀ x ∈ Xs, ∀ k ∈ K, x ∉ (R.onTy (.fvar k)).freeVars)
    (hXsF : ∀ x ∈ Xs, x ∉ softVars (substSoft R F))
    (hannScope : ∀ ann ∈ anns, ∀ v ∈ ann.rigidVars, v ∈ K ++ softVars F)
    (hrhsScope : ∀ rhs ∈ bindings, SourceScope K F rhs)
    (hannEq : anns.map (LetAnn.substTyFvars R) = declAnns)
    (hrhsEq : bindings.map (Input.substTyFvars R) = declBindings)
    (hannFreeze : ∀ ann ∈ anns, ∀ v ∈ ann.rigidVars,
      v ∈ K → v ∉ softVars F → R.onTy (.fvar v) = .fvar v)
    (hrhsFreeze : ∀ rhs ∈ bindings, ∀ v ∈ rhs.rigidVars,
      v ∈ K → v ∉ softVars F → R.onTy (.fvar v) = .fvar v) :
    ∃ V : Subst, (∀ pair ∈ V, pair.2.IsLC) ∧
      (∀ p ∈ P, V.onTy (.fvar p) = .fvar p) ∧
      Subst.AgreesBelow frontier R (S ++ V) ∧
      RecResidual P declCtx declSpecs declPrefixes G Xs (S.onCtx ctx) final (past ++ groups).flatten V ∧
      (anns.map (LetAnn.substTyFvars S)).map (LetAnn.substTyFvars V) = declAnns ∧
      (bindings.map (Input.substTyFvars S)).map (Input.substTyFvars V) = declBindings ∧
      (∀ ann ∈ anns.map (LetAnn.substTyFvars S), ∀ v ∈ ann.rigidVars,
        v ∈ K → v ∉ softVars (substSoft S F) → V.onTy (.fvar v) = .fvar v) ∧
      (∀ rhs ∈ bindings.map (Input.substTyFvars S), ∀ v ∈ rhs.rigidVars,
        v ∈ K → v ∉ softVars (substSoft S F) → V.onTy (.fvar v) = .fvar v) ∧
      (∀ x ∈ Xs, ∀ k ∈ K, x ∉ (V.onTy (.fvar k)).freeVars) ∧
      (∀ x ∈ Xs, x ∉ softVars (substSoft V (substSoft S F))) := by
  match h with
  | .nil =>
    have hannNil : anns.map (LetAnn.substTyFvars []) = anns := by
      calc
        _ = anns.map id := List.map_congr_left (fun ann _ => ann.substTyFvars_eq_self_of_fixes (fun _ _ => rfl))
        _ = anns := List.map_id anns
    have hrhsNil : bindings.map (Input.substTyFvars []) = bindings := by
      calc
        _ = bindings.map id := List.map_congr_left (fun rhs _ => rhs.substTyFvars_eq_self_of_fixes (fun _ _ => rfl))
        _ = bindings := List.map_id bindings
    refine ⟨R, hres.lc, hres.fixes, (fun _ _ => rfl), ?_, ?_, ?_, ?_, ?_, hXsK, ?_⟩
    · simpa only [Subst.onCtx_nil, List.append_nil] using hres
    · simpa only [hannNil] using hannEq
    · simpa only [hrhsNil] using hrhsEq
    · simpa only [hannNil, substSoft_nil] using hannFreeze
    · simpa only [hrhsNil, substSoft_nil] using hrhsFreeze
    · simpa only [substSoft_nil] using hXsF
  | .cons ho hp hc hf hr =>
    expose_names
    have hfirst : first ≤ cutoff := hr.frontier_le.trans hcutoff
    obtain ⟨U, hU, hUP, hag, hresStep⟩ := hStep ho hp hc hf hInfer hfirst hvalid hcanonical
      hframe hstateLC hstateB hctxWF hctx hbase hK hF hP hres hXsK hXsF
      hannScope hrhsScope hannEq hrhsEq hannFreeze hrhsFreeze
    obtain ⟨hstepFrame, _, _⟩ := recStep_frame ho hp hc hf
      (fun _ hi => hi.sourceLocality) hvalid hframe hstateLC hctxWF hstateB hbase hannScope hrhsScope
    have hstep : InferRecStrata K F frontier ctx anns bindings state [component]
        first (pre ++ current ++ []) exported := .cons ho hp hc hf .nil
    have hstep' : InferRecStrata K F frontier ctx anns bindings state [component]
        first (pre ++ current) exported := by simpa only [List.append_nil] using hstep
    have hle := hstep'.frontier_le
    have hannBelow : ∀ ann ∈ anns, ∀ v ∈ ann.rigidVars, v < frontier :=
      fun ann ha v hv => (List.mem_append.mp (hannScope ann ha v hv)).elim (hK v) (softVars_lt hF v)
    have hrhsBelow : ∀ rhs ∈ bindings, ∀ v ∈ rhs.rigidVars, v < frontier :=
      fun rhs hm v hv => (List.mem_append.mp (hrhsScope rhs hm v hv)).elim (hK v) (softVars_lt hF v)
    obtain ⟨hbothLC, hstepLC⟩ := hstep'.lc_of_infer (fun _ hi => hi.lc) hctxWF hstateLC
    obtain ⟨hbothB, hstepB⟩ := hstep'.belowFvars_of_infer (fun _ hi => hi.belowFvars)
      hctx hK hF hstateB hannBelow
    have hbothFix : ∀ k ∈ K, (pre ++ current).onTy (.fvar k) = .fvar k :=
      Subst.fixes_of_dom_avoids hstep'.dom_avoids
    have hannEqStep : (anns.map (LetAnn.substTyFvars (pre ++ current))).map
        (LetAnn.substTyFvars U) = declAnns := by
      calc
        _ = anns.map (LetAnn.substTyFvars R) := by
          simp only [List.map_map, Function.comp_def]
          apply List.map_congr_left
          intro ann ha
          rw [← LetAnn.substTyFvars_append]
          exact ann.substTyFvars_congr (fun v hv => (hag v (hannBelow ann ha v hv)).symm)
        _ = declAnns := hannEq
    have hrhsEqStep : (bindings.map (Input.substTyFvars (pre ++ current))).map
        (Input.substTyFvars U) = declBindings := by
      calc
        _ = bindings.map (Input.substTyFvars R) := by
          simp only [List.map_map, Function.comp_def]
          apply List.map_congr_left
          intro rhs hm
          rw [← Input.substTyFvars_append]
          exact rhs.substTyFvars_congr (fun v hv => (hag v (hrhsBelow rhs hm v hv)).symm)
        _ = declBindings := hrhsEq
    have hUonK : ∀ k ∈ K, U.onTy (.fvar k) = R.onTy (.fvar k) := by
      intro k hk
      have he := hag k (hK k hk)
      rw [Subst.onTy_append, hbothFix k hk] at he
      exact he.symm
    have hUF : substSoft U (substSoft (pre ++ current) F) = substSoft R F := by
      simp only [substSoft, List.map_map, Function.comp_def]
      apply List.map_congr_left
      intro ty ht
      simpa only [Subst.onTy_append] using (Subst.onTy_congr hag (hF ty ht)).symm
    have htailValid := recValid_subst (S := pre ++ current)
      (by simpa only [List.append_assoc, List.singleton_append] using hvalid :
        RecGroups.ValidResidualGroups (anns.map LetAnn.recModeAnn) (bindings.map Input.erase)
          ((past ++ [component]) ++ rest))
    have htailCanonical : (past ++ [component]) ++ rest = RecGroup.inferenceSccs
        ((anns.map (LetAnn.substTyFvars (pre ++ current))).map LetAnn.recModeAnn)
        ((bindings.map (Input.substTyFvars (pre ++ current))).map Input.erase) := by
      rw [← Input.inferenceSccs_substTyFvars anns bindings (pre ++ current)]
      simpa only [List.append_assoc, List.singleton_append] using hcanonical
    have htailFrame : exported.Frame base K (substSoft (pre ++ current) F) ((pre ++ current).onCtx ctx)
        (anns.map (LetAnn.substTyFvars (pre ++ current))) (past ++ [component]).flatten := by
      simpa only [List.flatten_append, List.flatten_cons, List.flatten_nil, List.append_nil] using hstepFrame
    have htailRes : RecResidual P declCtx declSpecs declPrefixes G Xs ((pre ++ current).onCtx ctx)
        exported (past ++ [component]).flatten U := by
      simpa only [List.flatten_append, List.flatten_cons, List.flatten_nil, List.append_nil] using hresStep
    obtain ⟨V, hV, hVP, hagTail, hresFinal, hAnnFinal, hRhsFinal, hAFinal, hRFinal, hXKFinal, hXFFinal⟩ :=
      InferRecStrata.sourcePrincipal_residual_of_step hStep hr
        (fun he hi => hInfer (by simpa only [sizeBindings_map_substTyFvars] using he) hi)
        hcutoff htailValid htailCanonical htailFrame hstepLC hstepB
        (Subst.onCtx_wf hbothLC hctxWF) (Subst.onCtx_below hbothB hle hctx)
        (by simp only [List.length_map]; omega)
        (fun k hk => (hK k hk).trans_le hle) (substSoft_below hbothB hle hF)
        (fun p hp => (hP p hp).trans_le hle) htailRes
        (by intro x hx k hk; rw [hUonK k hk]; exact hXsK x hx k hk)
        (by intro x hx; rw [hUF]; exact hXsF x hx)
        (by
          intro ann ha v hv
          obtain ⟨old, ho, rfl⟩ := List.mem_map.mp ha
          obtain ⟨original, horiginal, himage⟩ := LetAnn.rigidVars_substTyFvars hv
          exact scope_image hbothFix (hannScope old ho original horiginal) himage)
        (by
          intro rhs hm
          obtain ⟨old, ho, rfl⟩ := List.mem_map.mp hm
          exact (hrhsScope old ho).subst _ hbothFix)
        hannEqStep hrhsEqStep
        (by
          intro ann ha
          obtain ⟨old, ho, rfl⟩ := List.mem_map.mp ha
          exact signed_ann_freeze (hannScope old ho) (hannBelow old ho) hbothFix (hannFreeze old ho) hag)
        (by
          intro rhs hm
          obtain ⟨old, ho, rfl⟩ := List.mem_map.mp hm
          exact (hrhsScope old ho).residual_freeze (hrhsBelow old ho) hbothFix (hrhsFreeze old ho) hag)
    refine ⟨V, hV, hVP, ?_, ?_, ?_, ?_, ?_, ?_, hXKFinal, ?_⟩
    · simpa only [List.append_assoc] using Subst.AgreesBelow.trans_append hle hag hbothB hagTail
    · simpa only [Subst.onCtx_append, List.append_assoc, List.singleton_append] using hresFinal
    · simpa only [List.map_map, Function.comp_def, ← LetAnn.substTyFvars_append, List.append_assoc] using hAnnFinal
    · simpa only [List.map_map, Function.comp_def, ← Input.substTyFvars_append, List.append_assoc] using hRhsFinal
    · simpa only [List.map_map, Function.comp_def, ← LetAnn.substTyFvars_append, substSoft_append,
        List.append_assoc] using hAFinal
    · simpa only [List.map_map, Function.comp_def, ← Input.substTyFvars_append, substSoft_append,
        List.append_assoc] using hRFinal
    · simpa only [substSoft_append, List.append_assoc] using hXFFinal
termination_by structural h


theorem Typing.rec_inv_high (floor : Nat) (h : Typing K ctx (.letRec anns bindings body) resultTy) :
    ∃ (specs : List RecSpec) (groups prefixes : List (List Nat)) (G L : List Nat),
    (∀ g ∈ G, floor ≤ g) ∧
    RecGroups.ValidResidualGroups (anns.map LetAnn.recModeAnn) (bindings.map Input.erase) groups ∧
    RecSpecs.WF (anns.map LetAnn.recModeAnn) (bindings.map Input.erase) specs G ∧
    RecPrefixesWF anns specs prefixes G ∧
    (∀ name ∈ G, name ∉ ctx.env.freeVars ++ K) ∧
    (∀ ann ∈ anns, ∀ v ∈ ann.rigidVars, v ∈ K) ∧
    (∀ rhs ∈ bindings, ∀ v ∈ rhs.rigidVars, v ∈ K) ∧
    (∀ (stage : Nat) (component : List Nat), groups[stage]? = some component →
      ∀ Xs, FreshNames (G ++ L) G.length Xs →
      ∀ (member : Nat), member ∈ component → ∀ (rhs : Input) (ann : LetAnn) (names : List Nat) (ty : Ty),
        bindings[member]? = some rhs → anns[member]? = some ann →
        prefixes[member]? = some names → specs[member]? = some (.mono ty) →
        ann.RecFits (recRenameNames G Xs names) (Ty.renameG G Xs ty)) ∧
    (∀ (stage : Nat) (component : List Nat), groups[stage]? = some component →
      ∀ Xs, FreshNames (G ++ L) G.length Xs →
      ∀ (member : Nat), member ∈ component → ∀ (rhs : Input) (ann : LetAnn) (names : List Nat) (ty : Ty),
        bindings[member]? = some rhs → anns[member]? = some ann →
        prefixes[member]? = some names → specs[member]? = some (.mono ty) →
        Typing (K ++ Xs) (recStageCtx ctx specs prefixes (groups.take stage).flatten G Xs)
          (rhs.openTyVars (recRenameNames G Xs names)) (Ty.renameG G Xs ty)) ∧
    (∀ (member : Nat) (rhs : Input) (scheme : PolyTy), bindings[member]? = some rhs →
      specs[member]? = some (.poly scheme) → ∀ Ys, FreshNames L scheme.paramCount Ys →
        Typing (K ++ Ys) (recBodyCtx ctx specs prefixes G) (rhs.openTyVars Ys) (scheme.openVars Ys)) ∧
    Typing K (recBodyCtx ctx specs prefixes G) body resultTy := by
  obtain ⟨specs, groups, prefixes, G, L, hg, hw, hp, hG, ha, hr, hf, hm, hpoly, hb⟩ := h.rec_inv
  let avoid := K ++ ctx.env.freeVars ++ G ++ specs.flatMap RecSpec.freeVars ++ List.range floor
  obtain ⟨W, hWlen, hWnd, hWavoid⟩ := exists_fresh_names avoid G.length
  have hGW : ∀ g ∈ G, g ∉ W := by
    intro g hg hw
    exact hWavoid g hw (by simp only [avoid, List.mem_append]; tauto)
  have hWmono : ∀ ty, .mono ty ∈ specs → ∀ w ∈ W, w ∉ ty.freeVars := by
    intro ty ht w hw hv
    apply hWavoid w hw
    simp only [avoid, List.mem_append]
    exact Or.inl (Or.inr (List.mem_flatMap.mpr ⟨.mono ty, ht, hv⟩))
  let specs' := specs.map (fun spec => RecSpec.onSubstSource [] (RecSpec.onSubst (G.zip (W.map Ty.fvar)) spec))
  let prefixes' := prefixes.map (recRenameNames G W)
  let L' := G ++ W ++ L
  have annNil : anns.map (LetAnn.substTyFvars []) = anns := by
    conv_rhs => rw [← List.map_id anns]
    apply List.map_congr_left
    intro ann _
    exact ann.substTyFvars_eq_self_of_fixes (fun _ _ => rfl)
  have hw' : RecSpecs.WF (anns.map LetAnn.recModeAnn) (bindings.map Input.erase) specs' W := by
    simpa only [annNil] using Elaboration.RecSpecs.WF.subst_fresh_pool (S := []) hw (by simp) hWnd
  have hp' : RecPrefixesWF anns specs' prefixes' W := by
    simpa only [annNil] using hp.subst_fresh_pool (S := []) hWlen hWnd
  have hannsLen : anns.length = specs.length := by
    have hh := congrArg List.length hw.anns_eq
    simpa using hh.symm
  have hpData := fun i hi => hp.get hannsLen (i := i) hi
  have hcompleted := recCompletedSchemes_subst_fresh_pool (S := []) (by simp) hWlen hw.nodup hWnd hGW hWmono
    (by simp) (by simp) hw.mono_lc hpData
  have mapNil : ∀ xs : List PolyTy, xs.map (Subst.onPolyTy []) = xs := by
    intro xs
    rw [show Subst.onPolyTy [] = id from funext Subst.onPolyTy_nil, List.map_id]
  have hbodyCtx : recBodyCtx ctx specs' prefixes' W = recBodyCtx ctx specs prefixes G := by
    unfold recBodyCtx
    rw [hcompleted, mapNil]
  have oldFresh : ∀ Xs, FreshNames (W ++ L') W.length Xs → FreshNames (G ++ L) G.length Xs := by
    intro Xs hX
    refine ⟨hX.length.trans hWlen, hX.nodup, ?_⟩
    intro x hx hl
    exact hX.avoid x hx (by simp only [L', List.mem_append] at hl ⊢; tauto)
  have hGXs : ∀ Xs, FreshNames (W ++ L') W.length Xs → ∀ g ∈ G, g ∉ Xs := by
    intro Xs hX g hg hx
    exact hX.avoid g hx (by simp only [L', List.mem_append]; tauto)
  have hWXs : ∀ Xs, FreshNames (W ++ L') W.length Xs → ∀ w ∈ W, w ∉ Xs := by
    intro Xs hX w hw hx
    exact hX.avoid w hx (List.mem_append_left _ hw)
  have hstageCtx : ∀ Xs, FreshNames (W ++ L') W.length Xs → ∀ done,
      recStageCtx ctx specs' prefixes' done W Xs = recStageCtx ctx specs prefixes done G Xs := by
    intro Xs hX done
    unfold recStageCtx
    rw [recStageSchemes_subst_fresh_pool (S := []) (by simp) hWlen hw.nodup hWnd hGW hWmono
      (by simp) (by simp) hw.mono_lc hpData (hX.length.trans hWlen) (hGXs Xs hX) (hWXs Xs hX) (by simp), mapNil]
  have getOld : ∀ (i : Nat) (names : List Nat) (ty : Ty),
      prefixes'[i]? = some names → specs'[i]? = some (.mono ty) →
      ∃ names0 ty0, prefixes[i]? = some names0 ∧ specs[i]? = some (.mono ty0) ∧
        names = recRenameNames G W names0 ∧ ty = Ty.renameG G W ty0 := by
    intro i names ty hn ht
    rw [List.getElem?_map] at hn ht
    obtain ⟨names0, hn0, rfl⟩ := Option.map_eq_some_iff.mp hn
    obtain ⟨spec0, ht0, heq⟩ := Option.map_eq_some_iff.mp ht
    cases spec0 with
    | poly scheme => cases heq
    | mono ty0 =>
      cases heq
      exact ⟨names0, ty0, hn0, ht0, rfl, rfl⟩
  have square : ∀ Xs, FreshNames (W ++ L') W.length Xs → ∀ ty0,
      .mono ty0 ∈ specs → Ty.renameG W Xs (Ty.renameG G W ty0) = Ty.renameG G Xs ty0 := by
    intro Xs hX ty0 ht0
    simpa only [Subst.onTy_nil] using Ty.renameG_subst_fresh_pool (S := []) (hw.mono_lc ty0 ht0) (by simp)
      hWlen hw.nodup hWnd hGW (hWmono ty0 ht0) (by simp) (by simp)
      (hX.length.trans hWlen) (hGXs Xs hX) (hWXs Xs hX) (by simp)
  refine ⟨specs', groups, prefixes', W, L', ?_, hg, hw', hp', ?_, ha, hr, ?_, ?_, ?_, ?_⟩
  · intro w hw
    by_contra hh
    exact hWavoid w hw (by simp only [avoid, List.mem_append]; exact Or.inr (List.mem_range.mpr (by omega)))
  · intro w hw hv
    exact hWavoid w hw (by simp only [avoid, List.mem_append] at hv ⊢; tauto)
  · intro stage component hs Xs hX member hmember rhs ann names ty hri hai hni hti
    obtain ⟨names0, ty0, hn0, ht0, rfl, rfl⟩ := getOld member names ty hni hti
    have hsub := (hp.member member ann names0 hai hn0).2.2
    rw [recRenameNames_composition hWlen (hX.length.trans hWlen) hWnd hsub, square Xs hX ty0 (List.mem_of_getElem? ht0)]
    exact hf stage component hs Xs (oldFresh Xs hX) member hmember rhs ann names0 ty0 hri hai hn0 ht0
  · intro stage component hs Xs hX member hmember rhs ann names ty hri hai hni hti
    obtain ⟨names0, ty0, hn0, ht0, rfl, rfl⟩ := getOld member names ty hni hti
    have hsub := (hp.member member ann names0 hai hn0).2.2
    rw [hstageCtx Xs hX, recRenameNames_composition hWlen (hX.length.trans hWlen) hWnd hsub,
      square Xs hX ty0 (List.mem_of_getElem? ht0)]
    exact hm stage component hs Xs (oldFresh Xs hX) member hmember rhs ann names0 ty0 hri hai hn0 ht0
  · intro member rhs scheme hri hsi Ys hy
    rw [List.getElem?_map] at hsi
    obtain ⟨spec, hs0, heq⟩ := Option.map_eq_some_iff.mp hsi
    cases spec with
    | mono ty => cases heq
    | poly scheme0 =>
      cases heq
      rw [hbodyCtx]
      apply hpoly member rhs scheme0 hri hs0 Ys
      exact ⟨hy.length, hy.nodup, fun y hy' hl => hy.avoid y hy' (by simp only [L', List.mem_append]; tauto)⟩
  · rw [hbodyCtx]
    exact hb

set_option maxHeartbeats 2000000 in
theorem _root_.Infer.sourcePrincipal_letRec_of_unsigned
    {K : List Nat} {F : List Ty} {frontier first second next : Nat} {ctx : Ctx}
    {anns : List LetAnn} {bindings : List Input} {body : Input}
    {s1 s2 s3 : Subst} {state1 state2 : RecState} {groups : List (List Nat)}
    {schemes : List PolyTy} {outputs : List Expr} {bodyOut : Expr} {bodyTy : Ty}
    (hscope : SourceScope K F (.letRec anns bindings body) ∧ CtxBelow frontier ctx ∧
      (∀ k ∈ K, k < frontier) ∧ (∀ v ∈ softVars F, v < frontier))
    (hann : ∀ scheme, .complete scheme ∈ anns → scheme.WF)
    (hvalid : RecGroups.ValidResidualGroups (anns.map LetAnn.recModeAnn) (bindings.map Input.erase) groups ∧
      groups = RecGroup.inferenceSccs (anns.map LetAnn.recModeAnn) (bindings.map Input.erase))
    (hstrata : InferRecStrata K F (frontier + bindings.length) ctx anns bindings
      (RecState.init frontier anns) groups first s1 state1)
    (hsigned : InferRecSigned K (substSoft s1 F) 0 first (s1.onCtx ctx)
      (anns.map (LetAnn.substTyFvars s1)) (bindings.map (Input.substTyFvars s1)) state1 second s2 state2)
    (hexports : state2.exports = schemes.map some) (houtputs : state2.outputs = outputs.map some)
    (hbody : Infer K (substSoft (s1 ++ s2) F) second (state2.rhsCtx ((s1 ++ s2).onCtx ctx))
      (body.substTyFvars (s1 ++ s2)) next s3 bodyOut bodyTy)
    (hInfer : ∀ {κ F' Ψ c e Ψ' T output ty}, e.size ≤ sizeBindings bindings →
      (hi : Infer κ F' Ψ c e Ψ' T output ty) → Infer.SourcePrincipal hi)
    (ihbody : Infer.SourcePrincipal hbody)
(hUnsigned : ∀ (P : List Nat) (declCtx : Ctx) (declAnns : List LetAnn)
    (declBindings : List Input) (declSpecs : List RecSpec)
    (declGroups declPrefixes : List (List Nat)) (G Xs : List Nat) (R : Subst),
  RecGroups.ValidResidualGroups (declAnns.map LetAnn.recModeAnn) (declBindings.map Input.erase) declGroups →
  RecSpecs.WF (declAnns.map LetAnn.recModeAnn) (declBindings.map Input.erase) declSpecs G →
  RecPrefixesWF declAnns declSpecs declPrefixes G →
  (∀ g ∈ G, g ∉ declCtx.env.freeVars ++ P) →
  (∀ ann ∈ declAnns, ∀ v ∈ ann.rigidVars, v ∈ P) →
  (∀ rhs ∈ declBindings, ∀ v ∈ rhs.rigidVars, v ∈ P) →
  (∀ (stage : Nat) (component : List Nat), declGroups[stage]? = some component →
    ∀ (member : Nat), member ∈ component → ∀ (rhs : Input) (ann : LetAnn) (names : List Nat) (ty : Ty),
      declBindings[member]? = some rhs → declAnns[member]? = some ann →
      declPrefixes[member]? = some names → declSpecs[member]? = some (.mono ty) →
      ann.RecFits (recRenameNames G Xs names) (Ty.renameG G Xs ty)) →
  (∀ (stage : Nat) (component : List Nat), declGroups[stage]? = some component →
    ∀ (member : Nat), member ∈ component → ∀ (rhs : Input) (ann : LetAnn) (names : List Nat) (ty : Ty),
      declBindings[member]? = some rhs → declAnns[member]? = some ann →
      declPrefixes[member]? = some names → declSpecs[member]? = some (.mono ty) →
      Typing (P ++ Xs) (recStageCtx declCtx declSpecs declPrefixes (declGroups.take stage).flatten G Xs)
        (rhs.openTyVars (recRenameNames G Xs names)) (Ty.renameG G Xs ty)) →
  (∀ g ∈ G, next ≤ g) → (∀ x ∈ Xs, next ≤ x) →
  Xs.length = G.length → Xs.Nodup →
  (∀ g ∈ G, g ∉ Xs) →
  (∀ x ∈ Xs, ∀ (ty : Ty), .mono ty ∈ declSpecs → x ∉ ty.freeVars) →
  (∀ x ∈ Xs, x ∉ declCtx.env.freeVars ++ P) →
  CtxWF ctx → CtxBelow (frontier + bindings.length) ctx →
  (RecState.init frontier anns).LC → (RecState.init frontier anns).Below (frontier + bindings.length) →
  (RecState.init frontier anns).Frame frontier K F ctx anns [] →
  (∀ k ∈ K, k < frontier + bindings.length) →
  (∀ t ∈ F, Ty.BelowFvars (frontier + bindings.length) t) →
  (∀ p ∈ P, p < frontier + bindings.length) →
  RecResidual P declCtx declSpecs declPrefixes G Xs ctx (RecState.init frontier anns) [] R →
  (∀ x ∈ Xs, ∀ k ∈ K, x ∉ (R.onTy (.fvar k)).freeVars) →
  (∀ x ∈ Xs, x ∉ softVars (substSoft R F)) →
  (∀ ann ∈ anns, ∀ v ∈ ann.rigidVars, v ∈ K ++ softVars F) →
  (∀ rhs ∈ bindings, SourceScope K F rhs) →
  anns.map (LetAnn.substTyFvars R) = declAnns →
  bindings.map (Input.substTyFvars R) = declBindings →
  (∀ ann ∈ anns, ∀ v ∈ ann.rigidVars,
    v ∈ K → v ∉ softVars F → R.onTy (.fvar v) = .fvar v) →
  (∀ rhs ∈ bindings, ∀ v ∈ rhs.rigidVars,
    v ∈ K → v ∉ softVars F → R.onTy (.fvar v) = .fvar v) →
  ∃ V : Subst, (∀ pair ∈ V, pair.2.IsLC) ∧
    (∀ p ∈ P, V.onTy (.fvar p) = .fvar p) ∧
    Subst.AgreesBelow (frontier + bindings.length) R (s1 ++ V) ∧
    RecResidual P declCtx declSpecs declPrefixes G Xs (s1.onCtx ctx) state1 groups.flatten V ∧
    (anns.map (LetAnn.substTyFvars s1)).map (LetAnn.substTyFvars V) = declAnns ∧
    (bindings.map (Input.substTyFvars s1)).map (Input.substTyFvars V) = declBindings ∧
    (∀ ann ∈ anns.map (LetAnn.substTyFvars s1), ∀ v ∈ ann.rigidVars,
      v ∈ K → v ∉ softVars (substSoft s1 F) → V.onTy (.fvar v) = .fvar v) ∧
    (∀ rhs ∈ bindings.map (Input.substTyFvars s1), ∀ v ∈ rhs.rigidVars,
      v ∈ K → v ∉ softVars (substSoft s1 F) → V.onTy (.fvar v) = .fvar v) ∧
    (∀ x ∈ Xs, ∀ k ∈ K, x ∉ (V.onTy (.fvar k)).freeVars) ∧
    (∀ x ∈ Xs, x ∉ softVars (substSoft V (substSoft s1 F))))
 :
    Infer.SourcePrincipal (.letRec hscope hann hvalid hstrata hsigned hexports houtputs hbody) := by
  intro hctxWF hctx hK hF ambient target P hambient hP hfix hfreeze ht
  have bindingsMap : ∀ (S : Subst) (bs : List Input), substInputBindings S bs = bs.map (Input.substTyFvars S) := by
    intro S bs
    induction bs with
    | nil => rfl
    | cons rhs rest ih => simp only [substInputBindings, List.map_cons, ih]
  change Typing P (ambient.onCtx ctx)
    (.letRec (anns.map (LetAnn.substTyFvars ambient)) (substInputBindings ambient bindings)
      (body.substTyFvars ambient)) target at ht
  rw [bindingsMap] at ht
  obtain ⟨declSpecs, declGroups, declPrefixes, G, L, hGhigh, hdeclValid, hdeclWF, hdeclPrefixes,
    hGfresh, hdeclAnn, hdeclRhs, hdeclFits, hdeclTypes, hdeclPoly, hdeclBody⟩ := ht.rec_inv_high next
  have hraw := hscope.1
  have hannscope : ∀ ann ∈ anns, ∀ v ∈ ann.rigidVars, v ∈ K ++ softVars F := by
    intro ann ha v hv
    exact hraw v (List.mem_append_left _ (List.mem_append_left _ (List.mem_flatMap.mpr ⟨ann, ha, hv⟩)))
  have hrhsscope : ∀ rhs ∈ bindings, SourceScope K F rhs := by
    intro rhs hr v hv
    apply hraw v
    apply List.mem_append_left
    apply List.mem_append_right
    have hmap : ∀ bs : List Input, rigidBindingVars bs = bs.flatMap Input.rigidVars := by
      intro bs
      induction bs with
      | nil => rfl
      | cons rhs rest ih => simp only [rigidBindingVars, List.flatMap_cons, ih]
    rw [hmap]
    exact List.mem_flatMap.mpr ⟨rhs, hr, hv⟩
  have hannbelow : ∀ ann ∈ anns, ∀ v ∈ ann.rigidVars, v < frontier := by
    intro ann ha v hv
    exact (List.mem_append.mp (hannscope ann ha v hv)).elim (hK v) (softVars_lt hF v)
  have hrhsbelow : ∀ rhs ∈ bindings, ∀ v ∈ rhs.rigidVars, v < frontier := by
    intro rhs hr v hv
    exact (List.mem_append.mp (hrhsscope rhs hr v hv)).elim (hK v) (softVars_lt hF v)
  have hbodybelow : ∀ v ∈ body.rigidVars, v < frontier := by
    intro v hv
    exact (List.mem_append.mp (hraw v (List.mem_append_right _ hv))).elim (hK v) (softVars_lt hF v)
  have hlen : anns.length = bindings.length := by simpa only [List.length_map] using hvalid.1.length
  have hinitFrame := RecState.Frame.init hctx
    (fun v hv => by obtain ⟨ann, ha, hv⟩ := List.mem_flatMap.mp hv; exact hannbelow ann ha v hv) hK (softVars_lt hF)
  have hinitLC := RecState.LC.init (base := frontier) hann
  have hinitBelow : (RecState.init frontier anns).Below (frontier + bindings.length) := by
    simpa only [hlen] using RecState.Below.init hannbelow
  have hctxSeed : CtxBelow (frontier + bindings.length) ctx :=
    fun M hm => (hctx M hm).mono (by omega)
  have hFSeed : ∀ t ∈ F, Ty.BelowFvars (frontier + bindings.length) t :=
    fun t ht => (hF t ht).mono (by omega)
  have hKSeed : ∀ k ∈ K, k < frontier + bindings.length := fun k hk => by have := hK k hk; omega
  have hPSeed : ∀ p ∈ P, p < frontier + bindings.length := fun p hp => by have := hP p hp; omega
  have hvalid0 : RecGroups.ValidResidualGroups (anns.map LetAnn.recModeAnn) (bindings.map Input.erase) ([] ++ groups) := hvalid.1
  obtain ⟨hframe1, _⟩ := hstrata.frame_of_infer
    (fun _ hi => hi.sourceLocality) hvalid0 hinitFrame hinitLC hctxWF hinitBelow hctxSeed hFSeed
    (by omega) hannscope hrhsscope
  obtain ⟨hS1, hLC1⟩ := hstrata.lc_of_infer (fun _ hi => hi.lc) hctxWF hinitLC
  obtain ⟨hB1, hBelow1⟩ := hstrata.belowFvars_of_infer (fun _ hi => hi.belowFvars)
    hctxSeed hKSeed hFSeed hinitBelow
    (fun ann ha v hv => Nat.lt_of_lt_of_le (hannbelow ann ha v hv) (by omega))
  have hvalid1 := recValid_subst hvalid.1 s1
  have hdone1 := hframe1.all_mono_done hvalid1
  obtain ⟨hframe2, _⟩ := hsigned.frame_of_infer
    (fun _ hi => hi.sourceLocality) hframe1 (by simp) hdone1 hBelow1.2.2.2
  obtain ⟨hS2, hLC2⟩ := hsigned.lc_of_infer (fun _ hi => hi.lc) (Subst.onCtx_wf hS1 hctxWF) hLC1
  have hle1 := hstrata.frontier_le
  have hle2 := hsigned.frontier_le
  have hle3 := hbody.frontier_le
  let avoid := G ++ L ++ (ambient.onCtx ctx).env.freeVars ++ P ++ declSpecs.flatMap RecSpec.freeVars ++
    K.flatMap (fun k => (ambient.onTy (.fvar k)).freeVars) ++ softVars (substSoft ambient F) ++ List.range next
  obtain ⟨Xs, hXslen, hXsnd, hXsavoid⟩ := exists_fresh_names avoid G.length
  have hXs : FreshNames (G ++ L) G.length Xs := by
    refine ⟨hXslen, hXsnd, ?_⟩
    intro x hx hv
    exact hXsavoid x hx (by simp only [avoid, List.mem_append] at hv ⊢; tauto)
  obtain ⟨R, hR, hag0, hRP, hres0⟩ := RecResidual.init (declPrefixes := declPrefixes) (Xs := Xs)
    hdeclWF hambient hP hfix hannbelow hctx
  have hAnnEq : anns.map (LetAnn.substTyFvars R) = anns.map (LetAnn.substTyFvars ambient) := by
    apply List.map_congr_left
    intro ann ha
    exact ann.substTyFvars_congr (fun v hv => (hag0 v (hannbelow ann ha v hv)).symm)
  have hRhsEq : bindings.map (Input.substTyFvars R) = bindings.map (Input.substTyFvars ambient) := by
    apply List.map_congr_left
    intro rhs hr
    exact rhs.substTyFvars_congr (fun v hv => (hag0 v (hrhsbelow rhs hr v hv)).symm)
  have hAnnFreeze : ∀ ann ∈ anns, ∀ v ∈ ann.rigidVars,
      v ∈ K → v ∉ softVars F → R.onTy (.fvar v) = .fvar v := by
    intro ann ha v hv hk hn
    exact (hag0 v (hK v hk)).symm.trans (hfreeze v
      (List.mem_append_left _ (List.mem_append_left _ (List.mem_flatMap.mpr ⟨ann, ha, hv⟩))) hk hn)
  have hRhsFreeze : ∀ rhs ∈ bindings, ∀ v ∈ rhs.rigidVars,
      v ∈ K → v ∉ softVars F → R.onTy (.fvar v) = .fvar v := by
    intro rhs hr v hv hk hn
    exact (hag0 v (hK v hk)).symm.trans (hfreeze v (by
      apply List.mem_append_left
      apply List.mem_append_right
      have := hrhsscope rhs hr
      have hmap : ∀ bs : List Input, rigidBindingVars bs = bs.flatMap Input.rigidVars := by
        intro bs
        induction bs with
        | nil => rfl
        | cons r rest ih => simp only [rigidBindingVars, List.flatMap_cons, ih]
      rw [hmap]
      exact List.mem_flatMap.mpr ⟨rhs, hr, hv⟩) hk hn)
  have hXsK : ∀ x ∈ Xs, ∀ k ∈ K, x ∉ (R.onTy (.fvar k)).freeVars := by
    intro x hx k hk hv
    rw [← hag0 k (hK k hk)] at hv
    have hm : x ∈ K.flatMap (fun k => (ambient.onTy (.fvar k)).freeVars) := List.mem_flatMap.mpr ⟨k, hk, hv⟩
    exact hXsavoid x hx (by simp only [avoid, List.mem_append]; tauto)
  have hXsF : ∀ x ∈ Xs, x ∉ softVars (substSoft R F) := by
    intro x hx hv
    have he : substSoft R F = substSoft ambient F := by
      apply List.map_congr_left
      intro t ht
      exact (Subst.onTy_congr hag0 (hF t ht)).symm
    rw [he] at hv
    exact hXsavoid x hx (by simp only [avoid, List.mem_append]; tauto)
  obtain ⟨R1, hR1, hR1P, hag1, hres1, hAnnEq1, hRhsEq1, hAnnFreeze1, hRhsFreeze1, hXsK1, hXsF1⟩ :=
    hUnsigned P (ambient.onCtx ctx) _ _ declSpecs declGroups declPrefixes G Xs R
      hdeclValid hdeclWF hdeclPrefixes hGfresh hdeclAnn hdeclRhs
      (fun st co hs => hdeclFits st co hs Xs hXs)
      (fun st co hs => hdeclTypes st co hs Xs hXs)
      hGhigh (by
        intro x hx
        by_contra hh
        exact hXsavoid x hx (by simp only [avoid, List.mem_append]; exact Or.inr (List.mem_range.mpr (by omega))))
      hXslen hXsnd (by intro g hg hx; exact hXs.avoid g hx (List.mem_append_left _ hg))
      (by intro x hx ty ht hv; exact hXsavoid x hx (by
        simp only [avoid, List.mem_append]
        have hm : x ∈ declSpecs.flatMap RecSpec.freeVars := List.mem_flatMap.mpr ⟨.mono ty, ht, hv⟩
        tauto))
      (by intro x hx hv; exact hXsavoid x hx (by simp only [avoid, List.mem_append] at hv ⊢; tauto))
      hctxWF hctxSeed hinitLC hinitBelow hinitFrame hKSeed hFSeed hPSeed hres0 hXsK hXsF
      hannscope hrhsscope hAnnEq hRhsEq hAnnFreeze hRhsFreeze
  have hbase1 : frontier ≤ first := (Nat.le_add_right frontier bindings.length).trans hle1
  have hbase2 : frontier ≤ second := hbase1.trans hle2
  have hctx1 := Subst.onCtx_below hB1 hbase1 hctx
  have hF1 := substSoft_below hB1 hbase1 hF
  have hfix1 := Subst.fixes_of_dom_avoids hstrata.dom_avoids
  have hannscope1 : ∀ ann ∈ anns.map (LetAnn.substTyFvars s1), ∀ v ∈ ann.rigidVars,
      v ∈ K ++ softVars (substSoft s1 F) := by
    intro ann ha v hv
    obtain ⟨old, ho, rfl⟩ := List.mem_map.mp ha
    obtain ⟨k, hk, hv⟩ := LetAnn.rigidVars_substTyFvars hv
    exact scope_image hfix1 (hannscope old ho k hk) hv
  have hrhsscope1 : ∀ rhs ∈ bindings.map (Input.substTyFvars s1), SourceScope K (substSoft s1 F) rhs := by
    intro rhs hr
    obtain ⟨old, ho, rfl⟩ := List.mem_map.mp hr
    exact (hrhsscope old ho).subst s1 hfix1
  obtain ⟨R2, hR2, hR2P, hag2, hres2⟩ := hsigned.sourcePrincipal_residual
    (fun he hi => hInfer (by simpa only [sizeBindings_map_substTyFvars] using he) hi)
    hres1 (Subst.onCtx_wf hS1 hctxWF) hctx1 hLC1 hBelow1
    (fun k hk => (hK k hk).trans_le hbase1) hF1
    (fun p hp => (hP p hp).trans_le hbase1)
    (hframe1.exports_length.trans hframe1.specs_length.symm)
    hframe1.poly hdone1 hannscope1 hrhsscope1 hAnnFreeze1 hRhsFreeze1
    (by
      intro ann ha v hv
      apply hdeclAnn (ann.substTyFvars R1)
      · rw [← hAnnEq1]
        exact List.mem_map.mpr ⟨ann, ha, rfl⟩
      · exact hv)
    (by
      intro rhs hr v hv
      apply hdeclRhs (rhs.substTyFvars R1)
      · rw [← hRhsEq1]
        exact List.mem_map.mpr ⟨rhs, hr, rfl⟩
      · exact hv)
    (by
      intro j scheme rhs ha hr
      have hj : j < state1.specs.length := by
        rw [hframe1.specs_length]
        exact (List.getElem?_eq_some_iff.mp ha).1
      have hs0 := List.getElem?_eq_getElem hj
      have hmode := congrArg (fun xs : List (Option PolyTy) => xs[j]?) hframe1.modes
      dsimp only at hmode
      rw [List.getElem?_map, hs0, List.getElem?_map, ha] at hmode
      have hs : state1.specs[j]? = some (.poly scheme) := by
        cases heq : state1.specs[j]'hj with
        | mono ty => simp only [heq, Option.map_some, RecSpec.ann, LetAnn.recModeAnn] at hmode; cases hmode
        | poly other =>
          simp only [heq, Option.map_some, RecSpec.ann, LetAnn.recModeAnn, Option.some.injEq] at hmode
          exact hmode ▸ (heq ▸ hs0)
      obtain ⟨declScheme, hds, he⟩ := hres1.poly j scheme hs
      refine ⟨L, ?_⟩
      intro Ys hY
      have hr' := congrArg (fun bs : List Input => bs[j]?) hRhsEq1
      simp only [List.getElem?_map, hr, Option.map_some] at hr'
      have hd := hdeclPoly j (rhs.substTyFvars R1) declScheme (by simpa only [List.getElem?_map] using hr'.symm) hds Ys
      rw [← he] at hd
      exact hd hY)
  obtain ⟨hB2, hBelow2⟩ := hsigned.belowFvars_of_infer (fun _ hi => hi.belowFvars)
    hctx1 (fun k hk => (hK k hk).trans_le hbase1) hF1 hBelow1
    (by
      intro ann hm v hv
      obtain ⟨old, ho, rfl⟩ := List.mem_map.mp hm
      obtain ⟨k, hk, hv⟩ := LetAnn.rigidVars_substTyFvars hv
      exact (Subst.onTy_belowFvars hB1 ((Ty.BelowFvars.fvar (hannbelow old ho k hk)).mono hbase1)).mem_lt v hv)
  have hag12 : Subst.AgreesBelow (frontier + bindings.length) R ((s1 ++ s2) ++ R2) := by
    simpa only [List.append_assoc] using Subst.AgreesBelow.trans_append hle1 hag1 hB1 hag2
  have hagOriginal : Subst.AgreesBelow frontier ambient ((s1 ++ s2) ++ R2) := by
    intro v hv
    exact (hag0 v hv).trans (hag12 v (by omega))
  have hvalid2 := recValid_subst hvalid1 s2
  have hdone2 := hframe2.all_mono_done hvalid2
  have hcandidateBody := hres2.weaken_from_body
    (hframe2.exports_length.trans hframe2.specs_length.symm) hframe2.poly hdone2 hdeclBody
  have hctxbody : CtxWF (state2.rhsCtx ((s1 ++ s2).onCtx ctx)) := by
    apply hLC2.rhsCtx
    simpa only [Subst.onCtx_append] using Subst.onCtx_wf hS2 (Subst.onCtx_wf hS1 hctxWF)
  have hctxbodyB : CtxBelow second (state2.rhsCtx ((s1 ++ s2).onCtx ctx)) := by
    apply hBelow2.rhsCtx
    simpa only [Subst.onCtx_append] using Subst.onCtx_below hB2 hle2 hctx1
  have hbothB : ∀ p ∈ s1 ++ s2, Ty.BelowFvars second p.2 :=
    fun p hp => (List.mem_append.mp hp).elim (fun hp => (hB1 p hp).mono hle2) (hB2 p)
  have hbothFix : ∀ k ∈ K, (s1 ++ s2).onTy (.fvar k) = .fvar k :=
    Subst.fixes_of_dom_avoids (fun p hp => (List.mem_append.mp hp).elim (hstrata.dom_avoids p) (hsigned.dom_avoids p))
  have hbodySource : (body.substTyFvars (s1 ++ s2)).substTyFvars R2 = body.substTyFvars ambient := by
    rw [← body.substTyFvars_append]
    exact body.substTyFvars_congr (fun v hv => (hagOriginal v (hbodybelow v hv)).symm)
  have hbodyFreeze : ∀ v ∈ (body.substTyFvars (s1 ++ s2)).rigidVars,
      v ∈ K → v ∉ softVars (substSoft (s1 ++ s2) F) → R2.onTy (.fvar v) = .fvar v := by
    apply (show SourceScope K F body from fun v hv => hraw v (List.mem_append_right _ hv)).residual_freeze
      hbodybelow hbothFix (fun v hv => hfreeze v (List.mem_append_right _ hv)) hagOriginal
  have hcand : Typing P (R2.onCtx (state2.rhsCtx ((s1 ++ s2).onCtx ctx)))
      ((body.substTyFvars (s1 ++ s2)).substTyFvars R2) target := by
    rw [hbodySource]
    simpa only [Subst.onCtx_append] using hcandidateBody
  obtain ⟨R3, hR3, htarget, hR3P, hag3⟩ := ihbody hctxbody hctxbodyB
    (fun k hk => (hK k hk).trans_le hbase2) (substSoft_below hbothB hbase2 hF)
    R2 target P hR2 (fun p hp => (hP p hp).trans_le hbase2) hR2P hbodyFreeze hcand
  refine ⟨R3, hR3, htarget, hR3P, ?_⟩
  simpa only [List.append_assoc] using
    Subst.AgreesBelow.trans_append hbase2 hagOriginal hbothB hag3

/-- Reparameterize a private candidate pool without moving any actual state.
The inverse is valid after every later solve/export. -/
theorem RecResidual.repool
    {P G W Xs done : List Nat} {declCtx ctx : Ctx} {specs : List RecSpec}
    {prefixes : List (List Nat)} {state : RecState} {R : Subst}
    (h : RecResidual P declCtx specs prefixes G Xs ctx state done R)
    (hLC : ∀ spec ∈ specs, spec.LC) (hG : G.Nodup)
    (hprefix : ∀ i, i < specs.length → (prefixes[i]?.getD []).Nodup ∧
      ∀ v ∈ prefixes[i]?.getD [], v ∈ G)
    (hLen : W.length = G.length) (hW : W.Nodup)
    (hGW : ∀ g ∈ G, g ∉ W)
    (hWmono : ∀ ty, .mono ty ∈ specs → ∀ w ∈ W, w ∉ ty.freeVars)
    (hPoly : ∀ scheme, .poly scheme ∈ specs → ∀ g ∈ G, g ∉ scheme.body.freeVars)
    (hXsLen : Xs.length = G.length) (hGXs : ∀ g ∈ G, g ∉ Xs) (hWXs : ∀ w ∈ W, w ∉ Xs) :
    let specs' := specs.map (RecSpec.onSubstSource (G.zip (W.map Ty.fvar)))
    let prefixes' := prefixes.map (recRenameNames G W)
    RecResidual P declCtx specs' prefixes' W Xs ctx state done R ∧
      recBodyCtx declCtx specs' prefixes' W = recBodyCtx declCtx specs prefixes G ∧
      (∀ Z, Z.length = G.length → (∀ g ∈ G, g ∉ Z) → (∀ w ∈ W, w ∉ Z) →
        ∀ prior, recStageCtx declCtx specs' prefixes' prior W Z =
          recStageCtx declCtx specs prefixes prior G Z) ∧
      (∀ Z, Z.length = G.length → (∀ g ∈ G, g ∉ Z) → (∀ w ∈ W, w ∉ Z) →
        ∀ ty, .mono ty ∈ specs →
          Ty.renameG W Z (Ty.renameG G W ty) = Ty.renameG G Z ty) ∧
      (∀ laterCtx laterState laterDone T,
        RecResidual P declCtx specs' prefixes' W Xs laterCtx laterState laterDone T →
        RecResidual P declCtx specs prefixes G Xs laterCtx laterState laterDone T) := by
  dsimp only
  let A : Subst := G.zip (W.map Ty.fvar)
  let specs' := specs.map (RecSpec.onSubstSource A)
  let prefixes' := prefixes.map (recRenameNames G W)
  have hmonoLC : ∀ ty, .mono ty ∈ specs → ty.IsLC := fun ty ht => hLC _ ht
  have hPolyFix : ∀ scheme, .poly scheme ∈ specs → A.onPolyTy scheme = scheme := by
    intro scheme hs
    apply congrArg (PolyTy.mk scheme.paramCount)
    apply Subst.onTy_eq_self_of_fixes
    intro v hv
    exact zip_fvars_fixes (fun hg => hPoly scheme hs v hg hv)
  have hMap : specs' = specs.map (fun spec => RecSpec.onSubstSource [] (RecSpec.onSubst A spec)) := by
    apply List.map_congr_left
    intro spec hs
    cases spec with
    | mono ty => simp only [RecSpec.onSubstSource, RecSpec.onSubst, Subst.onTy_nil]
    | poly scheme => simp only [RecSpec.onSubstSource, RecSpec.onSubst, hPolyFix scheme hs, Subst.onPolyTy_nil]
  have hNil : ∀ Ms : List PolyTy, Ms.map (Subst.onPolyTy []) = Ms := by
    intro Ms
    rw [show Subst.onPolyTy [] = id from funext Subst.onPolyTy_nil, List.map_id]
  have hBody : recBodyCtx declCtx specs' prefixes' W = recBodyCtx declCtx specs prefixes G := by
    unfold recBodyCtx
    rw [hMap, recCompletedSchemes_subst_fresh_pool (S := []) (by simp) hLen hG hW hGW hWmono
      (by simp) (by simp) hmonoLC hprefix, hNil]
  have hStage : ∀ Z, Z.length = G.length → (∀ g ∈ G, g ∉ Z) → (∀ w ∈ W, w ∉ Z) →
      ∀ prior, recStageCtx declCtx specs' prefixes' prior W Z = recStageCtx declCtx specs prefixes prior G Z := by
    intro Z hZ hGZ hWZ prior
    unfold recStageCtx
    rw [hMap, recStageSchemes_subst_fresh_pool (S := []) (by simp) hLen hG hW hGW hWmono
      (by simp) (by simp) hmonoLC hprefix hZ hGZ hWZ (by simp), hNil]
  have hSquare : ∀ Z, Z.length = G.length → (∀ g ∈ G, g ∉ Z) → (∀ w ∈ W, w ∉ Z) →
      ∀ ty, .mono ty ∈ specs → Ty.renameG W Z (Ty.renameG G W ty) = Ty.renameG G Z ty := by
    intro Z hZ hGZ hWZ ty ht
    exact Ty.renameG_renameG (hmonoLC ty ht) hG hW hLen hZ hGW (hWmono ty ht) hWZ hGZ
  refine ⟨h.rename_decl_pool hLC hG hprefix hLen hW hXsLen hGW hWmono hWXs hGXs hPoly,
    hBody, hStage, hSquare, ?_⟩
  intro laterCtx laterState laterDone T ht
  refine ⟨ht.lc, ht.fixes, ht.ctx_eq, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [List.length_map] using ht.length
  · intro i algTy hi
    obtain ⟨declTy, hd⟩ := ht.mono i algTy hi
    obtain ⟨old, ho, _⟩ := RecSpec.mono_getElem?_map_onSubstSource hd
    exact ⟨old, ho⟩
  · intro i algScheme hi
    obtain ⟨declScheme, hd, heq⟩ := ht.poly i algScheme hi
    rw [List.getElem?_map] at hd
    obtain ⟨spec, ho, hspec⟩ := Option.map_eq_some_iff.mp hd
    cases spec with
    | mono ty => cases hspec
    | poly scheme =>
      simp only [RecSpec.onSubstSource] at hspec
      cases RecSpec.poly.inj hspec
      rw [hPolyFix scheme (List.mem_of_getElem? ho)] at heq
      exact ⟨scheme, ho, heq⟩
  · intro i algTy declTy hi hd hn
    have hnew : specs'[i]? = some (.mono (Ty.renameG G W declTy)) := by
      simp only [specs', List.getElem?_map, hd, Option.map_some, RecSpec.onSubstSource]
      rfl
    rw [ht.pending i algTy _ hi hnew hn, hSquare Xs hXsLen hGXs hWXs declTy (List.mem_of_getElem? hd)]
  · intro i algTy declTy hi hd hm
    have hnew : specs'[i]? = some (.mono (Ty.renameG G W declTy)) := by
      simp only [specs', List.getElem?_map, hd, Option.map_some, RecSpec.onSubstSource]
      rfl
    obtain ⟨exported, he, hg⟩ := ht.completed i algTy _ hi hnew hm
    refine ⟨exported, he, ?_⟩
    have hpref : prefixes'[i]?.getD [] = recRenameNames G W (prefixes[i]?.getD []) := by
      rw [List.getElem?_map]
      cases prefixes[i]? <;> rfl
    rw [hpref, recScheme_rename_pool (hmonoLC declTy (List.mem_of_getElem? hd)) hLen hG hW hGW
      (hWmono declTy (List.mem_of_getElem? hd)) (hprefix i (List.getElem?_eq_some_iff.mp hd).1).1
      (hprefix i (List.getElem?_eq_some_iff.mp hd).1).2] at hg
    exact hg

theorem recRenameNames_pool {names targets : List Nat}
    (hlen : targets.length = names.length) (hnd : names.Nodup) :
    recRenameNames names targets names = targets := by
  apply List.ext_get (by simp [recRenameNames, hlen])
  intro i hi hj
  simp only [recRenameNames, List.get_eq_getElem, List.getElem_map]
  simp only [hnd.idxOf_getElem i (by simpa only [recRenameNames, List.length_map] using hi),
    List.getElem?_eq_getElem hj, Option.getD_some]

/-- Refresh one candidate opening after the next actual allocation is known.
The inverse is appended after later solving and needs no bound on that solve. -/
theorem RecResidual.refresh_opening
    {P G Xs Zs done : List Nat} {declCtx ctx : Ctx} {specs : List RecSpec}
    {prefixes : List (List Nat)} {state : RecState} {R : Subst} {frontier : Nat}
    (h : RecResidual P declCtx specs prefixes G Xs ctx state done R)
    (hstate : state.Below frontier) (hctx : CtxBelow frontier ctx)
    (hMonoLC : ∀ ty, .mono ty ∈ specs → ty.IsLC) (hG : G.Nodup)
    (hXsLen : Xs.length = G.length) (hXsND : Xs.Nodup) (hGXs : ∀ g ∈ G, g ∉ Xs)
    (hZLen : Zs.length = Xs.length) (hZND : Zs.Nodup) (hGZ : ∀ g ∈ G, g ∉ Zs)
    (hXZ : ∀ x ∈ Xs, x ∉ Zs)
    (hXsP : ∀ p ∈ P, p ∉ Xs) (hZP : ∀ p ∈ P, p ∉ Zs)
    (hXsCtx : ∀ x ∈ Xs, x ∉ declCtx.env.freeVars)
    (hZCtx : ∀ z ∈ Zs, z ∉ declCtx.env.freeVars)
    (hXsSpec : ∀ x ∈ Xs, ∀ spec ∈ specs, x ∉ spec.freeVars)
    (hZSpec : ∀ z ∈ Zs, ∀ spec ∈ specs, z ∉ spec.freeVars)
    (hZOld : ∀ v, v < frontier → ∀ z ∈ Zs, z ∉ (R.onTy (.fvar v)).freeVars) :
    let B : Subst := Xs.zip (Zs.map Ty.fvar)
    let back : Subst := Zs.zip (Xs.map Ty.fvar)
    RecResidual P declCtx specs prefixes G Zs ctx state done (R ++ B) ∧
      (∀ prior, B.onCtx (recStageCtx declCtx specs prefixes prior G Xs) =
        recStageCtx declCtx specs prefixes prior G Zs) ∧
      (∀ ty, .mono ty ∈ specs → B.onTy (Ty.renameG G Xs ty) = Ty.renameG G Zs ty) ∧
      (∀ (raw : Input), (∀ v ∈ raw.rigidVars, v ∈ P) → ∀ (prior : List Nat) (ty : Ty) (names : List Nat),
        Typing (P ++ Xs) (recStageCtx declCtx specs prefixes prior G Xs) (raw.openTyVars names) ty →
        Typing (P ++ Zs) (recStageCtx declCtx specs prefixes prior G Zs)
          (raw.openTyVars (recRenameNames Xs Zs names)) (B.onTy ty)) ∧
      (∀ laterCtx laterState laterDone T,
        RecResidual P declCtx specs prefixes G Zs laterCtx laterState laterDone T →
        RecResidual P declCtx specs prefixes G Xs laterCtx laterState laterDone (T ++ back)) ∧
      (∀ solved T, Subst.AgreesBelow frontier (R ++ B) (solved ++ T) →
        Subst.AgreesBelow frontier R (solved ++ (T ++ back))) := by
  dsimp only
  let B : Subst := Xs.zip (Zs.map Ty.fvar)
  let back : Subst := Zs.zip (Xs.map Ty.fvar)
  have hBLC : ∀ pair ∈ B, pair.2.IsLC := zip_fvars_lc
  have hBackLC : ∀ pair ∈ back, pair.2.IsLC := zip_fvars_lc
  have hBP : ∀ p ∈ P, B.onTy (.fvar p) = .fvar p := fun p hp => zip_fvars_fixes (hXsP p hp)
  have hBackP : ∀ p ∈ P, back.onTy (.fvar p) = .fvar p := fun p hp => zip_fvars_fixes (hZP p hp)
  have hBCtx : B.onCtx declCtx = declCtx := by
    apply congrArg₂ Ctx.mk
    · apply Subst.onEnv_eq_self_of_fresh
      intro pair hp hv
      exact hXsCtx pair.1 (List.of_mem_zip hp).1 hv
    · rfl
  have hBackCtx : back.onCtx declCtx = declCtx := by
    apply congrArg₂ Ctx.mk
    · apply Subst.onEnv_eq_self_of_fresh
      intro pair hp hv
      exact hZCtx pair.1 (List.of_mem_zip hp).1 hv
    · rfl
  have hBSpec : ∀ scheme, .poly scheme ∈ specs → B.onPolyTy scheme = scheme := by
    intro scheme hs
    apply congrArg (PolyTy.mk scheme.paramCount)
    apply Subst.onTy_eq_self_of_fixes
    intro v hv
    exact zip_fvars_fixes (fun hx => hXsSpec v hx (.poly scheme) hs hv)
  have hBackSpec : ∀ scheme, .poly scheme ∈ specs → back.onPolyTy scheme = scheme := by
    intro scheme hs
    apply congrArg (PolyTy.mk scheme.paramCount)
    apply Subst.onTy_eq_self_of_fixes
    intro v hv
    exact zip_fvars_fixes (fun hz => hZSpec v hz (.poly scheme) hs hv)
  have hBClose : ∀ (i : Nat) (ty : Ty), specs[i]? = some (.mono ty) →
      B.onPolyTy (recScheme (prefixes[i]?.getD []) G ty) = recScheme (prefixes[i]?.getD []) G ty := by
    intro i ty hs
    apply congrArg (PolyTy.mk _)
    apply Subst.onTy_eq_self_of_fixes
    intro v hv
    exact zip_fvars_fixes (fun hx => hXsSpec v hx (.mono ty) (List.mem_of_getElem? hs)
      (Ty.freeVars_closeOver_subset hv))
  have hBackClose : ∀ (i : Nat) (ty : Ty), specs[i]? = some (.mono ty) →
      back.onPolyTy (recScheme (prefixes[i]?.getD []) G ty) = recScheme (prefixes[i]?.getD []) G ty := by
    intro i ty hs
    apply congrArg (PolyTy.mk _)
    apply Subst.onTy_eq_self_of_fixes
    intro v hv
    exact zip_fvars_fixes (fun hz => hZSpec v hz (.mono ty) (List.mem_of_getElem? hs)
      (Ty.freeVars_closeOver_subset hv))
  have hBMono : ∀ ty, .mono ty ∈ specs → B.onTy (Ty.renameG G Xs ty) = Ty.renameG G Zs ty := by
    intro ty ht
    simpa only [recRenameNames_pool hZLen hXsND] using
      (zip_fvars_renameG hZLen hXsND hXZ (hMonoLC ty ht) hG hXsLen hGXs hGZ
        (fun x hx => hXsSpec x hx (.mono ty) ht))
  have hBackMono : ∀ ty, .mono ty ∈ specs → back.onTy (Ty.renameG G Zs ty) = Ty.renameG G Xs ty := by
    intro ty ht
    simpa only [recRenameNames_pool hZLen.symm hZND] using
      (zip_fvars_renameG hZLen.symm hZND (fun z hz hx => hXZ z hx hz)
        (hMonoLC ty ht) hG (hZLen.trans hXsLen) hGZ hGXs
        (fun z hz => hZSpec z hz (.mono ty) ht))
  have hRBLc : ∀ pair ∈ R ++ B, pair.2.IsLC :=
    fun pair hp => (List.mem_append.mp hp).elim (h.lc pair) (hBLC pair)
  have hRBP : ∀ p ∈ P, (R ++ B).onTy (.fvar p) = .fvar p := by
    intro p hp
    rw [Subst.onTy_append, h.fixes p hp, hBP p hp]
  refine ⟨h.change_opening hstate hctx hBLC hBCtx hBSpec
    (fun i ty hs _ => recScheme_wf (hMonoLC ty (List.mem_of_getElem? hs)))
    (fun i ty hs _ => hBClose i ty hs) hBMono hRBLc hRBP (fun _ _ => rfl), ?_, hBMono, ?_, ?_, ?_⟩
  · intro prior
    exact recStageCtx_change_opening hBCtx hBSpec hBClose hBMono
  · intro raw hraw prior ty names ht
    have himages : Xs.map (fun x => B.onTy (.fvar x)) = Zs.map Ty.fvar := by
      apply List.ext_getElem
      · simpa only [List.length_map] using hZLen.symm
      · intro i hi hj
        have hiX : i < Xs.length := by simpa only [List.length_map] using hi
        have hiZ : i < Zs.length := by omega
        simp only [List.getElem_map]
        exact Ty.substFvars_zip_fvar_renameG hZLen hXsND hXZ
          (List.getElem?_eq_getElem hiX) (List.getElem?_eq_getElem hiZ)
    have hnames : names.map (fun x => B.onTy (.fvar x)) = (recRenameNames Xs Zs names).map Ty.fvar :=
      zip_fvars_images hZLen hXsND hXZ
    have hs := ht.opened_source_onSubst hBLC hBP himages hnames hraw
    rw [recStageCtx_change_opening hBCtx hBSpec hBClose hBMono] at hs
    exact hs
  · intro laterCtx laterState laterDone T ht
    have ht' : RecResidual (P ++ []) declCtx specs prefixes G Zs laterCtx laterState laterDone T := by
      simpa only [List.append_nil] using ht
    exact ht'.restore_opening hBackLC hBackP hBackCtx hBackSpec
      (fun i ty hs _ => recScheme_wf (hMonoLC ty (List.mem_of_getElem? hs)))
      (fun i ty hs _ => hBackClose i ty hs) hBackMono
  · intro solved T hag
    apply hag.restore_after
    intro v hv
    rw [Subst.onTy_append]
    exact zip_fvars_roundtrip hZLen hXsND hZND hXZ (hZOld v hv)

/-- Internal proof data shared by recursive factorization and production.
Creation requires only the authoritative opening allocation, not a solve/run. -/
structure RecResidual.Prepared
    (P G Xs K : List Nat) (F : List Ty) (frontier opened : Nat)
    (ctx declCtx : Ctx) (state : RecState) (bindings : List Input)
    (openings : List RecOpening) (done members : List Nat)
    (declSpecs : List RecSpec) (prefixes : List (List Nat)) (R : Subst) where
  protectedVars : List Nat
  candidateCtx : Ctx
  candidateSpecs : List RecSpec
  opening : List Nat
  subst : Subst
  lc : ∀ pair ∈ subst, pair.2.IsLC
  fixes : ∀ p ∈ protectedVars, subst.onTy (.fvar p) = .fvar p
  record : RecResidual protectedVars candidateCtx candidateSpecs prefixes G opening ctx state done subst
  below : ∀ p ∈ protectedVars, p < opened
  freeze : ∀ (i : Nat) (rhs : Input), i ∈ members → bindings[i]? = some rhs →
    ∀ v ∈ rhs.rigidVars, v ∈ K → v ∉ softVars F → subst.onTy (.fvar v) = .fvar v
  solves : ∀ (i : Nat) (slot : RecOpening) (ty expected : Ty), i ∈ members →
    openings[i]? = some slot → state.specs[i]? = some (.mono ty) →
    slot.expected = some expected → subst.onTy expected = subst.onTy ty
  typed : ∀ (i : Nat) (rhs : Input) (ty : Ty), i ∈ members →
    (openRecSources openings bindings)[i]? = some rhs → state.specs[i]? = some (.mono ty) →
    Typing protectedVars (subst.onCtx (state.rhsCtx ctx)) (rhs.substTyFvars subst) (subst.onTy ty)
  written : ∀ (i : Nat) (slot : RecOpening), i ∈ members → openings[i]? = some slot →
    slot.written.map (fun v => subst.onTy (.fvar v)) =
      (recRenameNames G opening (prefixes[i]?.getD [])).map Ty.fvar
  monoLC : ∀ ty, .mono ty ∈ candidateSpecs → ty.IsLC
  poolND : G.Nodup
  prefixData : ∀ (i : Nat) (ty : Ty), candidateSpecs[i]? = some (.mono ty) →
    (prefixes[i]?.getD []).Nodup ∧ ∀ v ∈ prefixes[i]?.getD [], v ∈ G
  length : opening.length = G.length
  nodup : opening.Nodup
  disjoint : ∀ g ∈ G, g ∉ opening
  typesFresh : ∀ x ∈ opening, ∀ ty, .mono ty ∈ candidateSpecs → x ∉ ty.freeVars
  ctxFresh : ∀ x ∈ opening, x ∉ (subst.onCtx (state.fixedCtx ctx)).env.freeVars
  rigidFresh : ∀ x ∈ opening, ∀ k ∈ K, x ∉ (subst.onTy (.fvar k)).freeVars
  softFresh : ∀ x ∈ opening, x ∉ softVars (substSoft subst F)
  preservesRigid : (∀ k ∈ K, R.onTy (.fvar k) = .fvar k) →
    ∀ k ∈ K, subst.onTy (.fvar k) = .fvar k
  restore : ∀ (solved : Subst) (final : RecState) (V : Subst),
    Subst.AgreesBelow opened subst (solved ++ V) →
    RecResidual protectedVars candidateCtx candidateSpecs prefixes G opening
      (solved.onCtx ctx) final (done ++ members) V →
    ∃ T : Subst, (∀ pair ∈ T, pair.2.IsLC) ∧ (∀ p ∈ P, T.onTy (.fvar p) = .fvar p) ∧
      Subst.AgreesBelow frontier R (solved ++ T) ∧
      RecResidual P declCtx declSpecs prefixes G Xs (solved.onCtx ctx) final (done ++ members) T

set_option maxHeartbeats 3000000 in
theorem RecResidual.prepare_component
    {P G Xs : List Nat} {declCtx : Ctx} {declAnns : List LetAnn}
    {declBindings : List Input} {declSpecs : List RecSpec}
    {declGroups declPrefixes : List (List Nat)} {cutoff base : Nat} :
  RecGroups.ValidResidualGroups (declAnns.map LetAnn.recModeAnn) (declBindings.map Input.erase) declGroups →
  RecSpecs.WF (declAnns.map LetAnn.recModeAnn) (declBindings.map Input.erase) declSpecs G →
  RecPrefixesWF declAnns declSpecs declPrefixes G →
  (∀ g ∈ G, g ∉ declCtx.env.freeVars ++ P) →
  (∀ ann ∈ declAnns, ∀ v ∈ ann.rigidVars, v ∈ P) →
  (∀ rhs ∈ declBindings, ∀ v ∈ rhs.rigidVars, v ∈ P) →
  (∀ (stage : Nat) (component : List Nat), declGroups[stage]? = some component →
    ∀ (member : Nat), member ∈ component → ∀ (rhs : Input) (ann : LetAnn) (names : List Nat) (ty : Ty),
      declBindings[member]? = some rhs → declAnns[member]? = some ann →
      declPrefixes[member]? = some names → declSpecs[member]? = some (.mono ty) →
      ann.RecFits (recRenameNames G Xs names) (Ty.renameG G Xs ty)) →
  (∀ (stage : Nat) (component : List Nat), declGroups[stage]? = some component →
    ∀ (member : Nat), member ∈ component → ∀ (rhs : Input) (ann : LetAnn) (names : List Nat) (ty : Ty),
      declBindings[member]? = some rhs → declAnns[member]? = some ann →
      declPrefixes[member]? = some names → declSpecs[member]? = some (.mono ty) →
      Typing (P ++ Xs) (recStageCtx declCtx declSpecs declPrefixes (declGroups.take stage).flatten G Xs)
        (rhs.openTyVars (recRenameNames G Xs names)) (Ty.renameG G Xs ty)) →
  (∀ g ∈ G, cutoff ≤ g) → (∀ x ∈ Xs, cutoff ≤ x) →
  Xs.length = G.length → Xs.Nodup →
  (∀ g ∈ G, g ∉ Xs) →
  (∀ x ∈ Xs, ∀ (ty : Ty), .mono ty ∈ declSpecs → x ∉ ty.freeVars) →
  (∀ x ∈ Xs, x ∉ declCtx.env.freeVars ++ P) →
∀ {K : List Nat} {F : List Ty} {frontier opened : Nat}
      {ctx : Ctx} {anns : List LetAnn} {bindings : List Input}
      {state : RecState} {past rest : List (List Nat)} {component : List Nat}
      {openings : List RecOpening} {R : Subst}
      ,
      OpenRecAnns component 0 frontier anns opened openings →
      opened ≤ cutoff →
      RecGroups.ValidResidualGroups (anns.map LetAnn.recModeAnn) (bindings.map Input.erase)
        (past ++ component :: rest) →
      past ++ component :: rest = RecGroup.inferenceSccs
        (anns.map LetAnn.recModeAnn) (bindings.map Input.erase) →
      state.Frame base K F ctx anns past.flatten →
      state.LC → state.Below frontier → CtxWF ctx → CtxBelow frontier ctx →
      base + bindings.length ≤ frontier →
      (∀ k ∈ K, k < frontier) → (∀ t ∈ F, Ty.BelowFvars frontier t) →
      (∀ p ∈ P, p < frontier) →
      RecResidual P declCtx declSpecs declPrefixes G Xs ctx state past.flatten R →
      (∀ x ∈ Xs, ∀ k ∈ K, x ∉ (R.onTy (.fvar k)).freeVars) →
      (∀ x ∈ Xs, x ∉ softVars (substSoft R F)) →
      (∀ ann ∈ anns, ∀ v ∈ ann.rigidVars, v ∈ K ++ softVars F) →
      (∀ rhs ∈ bindings, SourceScope K F rhs) →
      anns.map (LetAnn.substTyFvars R) = declAnns →
      bindings.map (Input.substTyFvars R) = declBindings →
      (∀ ann ∈ anns, ∀ v ∈ ann.rigidVars,
        v ∈ K → v ∉ softVars F → R.onTy (.fvar v) = .fvar v) →
      (∀ rhs ∈ bindings, ∀ v ∈ rhs.rigidVars,
        v ∈ K → v ∉ softVars F → R.onTy (.fvar v) = .fvar v) →
      Nonempty (RecResidual.Prepared P G Xs K F frontier opened ctx declCtx state bindings
        openings past.flatten component declSpecs declPrefixes R) := by
  intro hdeclValid hdeclWF hprefix hGfresh hdeclAnn hdeclRhs hdeclFits hdeclTypes
    hGhigh hXhigh hXlen hXnd hGX hXmono hXctxP K F frontier opened ctx anns bindings state past rest component openings R
    ho hcutoff hvalid hcanonical hframe hstateLC hstateB hctxWF hctx hbase hK hF hP hres
    hXsK hXsF hannScope hrhsScope hannEq hrhsEq hannFreeze hrhsFreeze
  have hopen := ho.frontier_le
  have hopenCut : opened ≤ cutoff := hcutoff
  have hfrontCut : frontier ≤ cutoff := hopen.trans hopenCut
  have hlen : anns.length = bindings.length := by simpa only [List.length_map] using hvalid.length
  have hAnnLen : declAnns.length = declSpecs.length := by
    have h := congrArg List.length hdeclWF.anns_eq
    simpa only [List.length_map] using h.symm
  have hAnnLen0 : anns.length = declAnns.length := by
    have h := congrArg List.length hannEq
    simpa only [List.length_map] using h
  have hprefLen : declPrefixes.length = anns.length := hprefix.length.trans (hAnnLen.symm.trans hAnnLen0.symm)
  have hprefixData := fun i hi => hprefix.get hAnnLen (i := i) hi
  have hdeclLC : ∀ spec ∈ declSpecs, spec.LC := by
    intro spec hs
    cases spec with
    | mono ty => exact hdeclWF.mono_lc ty hs
    | poly scheme => exact hdeclWF.poly_wf scheme hs
  have hRawAnn : ∀ ann ∈ anns, ∀ v ∈ ann.rigidVars, v < frontier :=
    fun ann ha v hv => (List.mem_append.mp (hannScope ann ha v hv)).elim (hK v) (softVars_lt hF v)
  have hRawRhs : ∀ rhs ∈ bindings, ∀ v ∈ rhs.rigidVars, v < frontier :=
    fun rhs hr v hv => (List.mem_append.mp (hrhsScope rhs hr v hv)).elim (hK v) (softVars_lt hF v)
  have hbindings : bindings.map Input.erase = declBindings.map Input.erase := by
    rw [← hrhsEq, List.map_map]
    exact List.map_congr_left (fun rhs _ => rhs.erase_substTyFvars R |>.symm)
  have hmask : ∀ i, RecGroup.isUnsignedAt (anns.map LetAnn.recModeAnn) i =
      RecGroup.isUnsignedAt (declAnns.map LetAnn.recModeAnn) i := by
    intro i
    rw [← hannEq]
    exact LetAnn.recModeAnn_isUnsignedAt_subst anns R i
  have halgorithm : (RecGroup.inferenceSccs (anns.map LetAnn.recModeAnn)
      (bindings.map Input.erase))[past.length]? = some component := by
    rw [← hcanonical, List.getElem?_append_right (by omega)]
    simp
  have hdone : past.flatten = ((RecGroup.inferenceSccs (anns.map LetAnn.recModeAnn)
      (bindings.map Input.erase)).take past.length).flatten := by
    rw [← hcanonical, List.take_append, List.take_length, Nat.sub_self, List.take_zero, List.append_nil]
  have hTypes : ∀ stage co, declGroups[stage]? = some co →
      ∀ member ∈ co, ∀ rhs ty, declBindings[member]? = some rhs → declSpecs[member]? = some (.mono ty) →
      Typing (P ++ Xs) (recStageCtx declCtx declSpecs declPrefixes (declGroups.take stage).flatten G Xs)
        (rhs.openTyVars (recRenameNames G Xs (declPrefixes[member]?.getD []))) (Ty.renameG G Xs ty) := by
    intro stage co hs member hm rhs ty hr ht
    have hi : member < declPrefixes.length := by rw [hprefix.length]; exact (List.getElem?_eq_some_iff.mp ht).1
    have hiann : member < declAnns.length := by rw [hAnnLen]; exact (List.getElem?_eq_some_iff.mp ht).1
    have hp := List.getElem?_eq_getElem hi
    have ha := List.getElem?_eq_getElem hiann
    simpa only [hp, Option.getD_some] using hdeclTypes stage co hs member hm rhs declAnns[member]
      declPrefixes[member] ty hr ha hp ht
  have hview : ∀ (i : Nat) (ann : LetAnn) (rhs : Input) (ty : Ty), i ∈ component →
      anns[i]? = some ann → bindings[i]? = some rhs → state.specs[i]? = some (.mono ty) →
      (ann.substTyFvars R).RecFits (recRenameNames G Xs (declPrefixes[i]?.getD [])) (R.onTy ty) ∧
      (recRenameNames G Xs (declPrefixes[i]?.getD [])).length = ann.recPrefixCount ∧
      Typing (P ++ recRenameNames G Xs (declPrefixes[i]?.getD [])) (R.onCtx (state.rhsCtx ctx))
        ((rhs.substTyFvars R).openTyVars (recRenameNames G Xs (declPrefixes[i]?.getD []))) (R.onTy ty) := by
    intro i ann rhs ty hi ha hr ht
    exact hres.selected_view hframe hbindings hmask halgorithm hdone hdeclValid hdeclWF hprefix
      hdeclFits hTypes hdeclRhs hannEq hrhsEq ha hr ht hi
  let names := declPrefixes.mapIdx (fun i ns => if i ∈ component then recRenameNames G Xs ns else [])
  have hNames : names.length = anns.length := by simp only [names, List.length_mapIdx, hprefLen]
  have hprefixCount : ∀ (i : Nat) (ann : LetAnn) (ns : List Nat), anns[i]? = some ann →
      declPrefixes[i]? = some ns → ns.length = ann.recPrefixCount ∧ ∀ v ∈ ns, v ∈ G := by
    intro i ann ns ha hn
    have hca : declAnns[i]? = some (ann.substTyFvars R) := by rw [← hannEq, List.getElem?_map, ha, Option.map_some]
    obtain ⟨hc, _, hs⟩ := hprefix.member i _ ns hca hn
    exact ⟨by simpa only [LetAnn.recPrefixCount_subst_source] using hc, hs⟩
  have hcollection := ho.selected_prefix_collection hprefLen hXlen hprefixCount
  change (openings.flatMap RecOpening.written).length = names.flatten.length ∧
    ∀ c ∈ names.flatten, c ∈ Xs at hcollection
  let A := openings.flatMap RecOpening.written
  let C := names.flatten
  let reps := prefixRepresentatives A C
  let B : Subst := C.dedup.zip (reps.map Ty.fvar)
  let Ys := recRenameNames C.dedup reps Xs
  have hAC : A.length = C.length := hcollection.1
  have hCX : ∀ c ∈ C, c ∈ Xs := hcollection.2
  have hrepA : ∀ r ∈ reps, r ∈ A := fun r hr => prefixRepresentatives_mem_actual hAC hr
  have hRepLen : reps.length = C.dedup.length := by simp only [reps, prefixRepresentatives, List.length_map]
  have hReps : reps.Nodup := prefixRepresentatives_nodup hAC ho.written_nodup
  have hXA : ∀ x ∈ Xs, x ∉ A := by
    intro x hx ha
    have h1 := hXhigh x hx
    have h2 := (ho.written_range x ha).2
    omega
  have hGA : ∀ g ∈ G, g ∉ A := by
    intro g hg ha
    have h1 := hGhigh g hg
    have h2 := (ho.written_range g ha).2
    omega
  have hXR : ∀ x ∈ Xs, x ∉ reps := fun x hx hr => hXA x hx (hrepA x hr)
  have hGR : ∀ g ∈ G, g ∉ reps := fun g hg hr => hGA g hg (hrepA g hr)
  have hCD : ∀ c ∈ C.dedup, c ∉ reps := fun c hc => hXR c (hCX c (List.mem_dedup.mp hc))
  have hXP : ∀ x ∈ Xs, x ∉ P := fun x hx hp => hXctxP x hx (List.mem_append_right _ hp)
  have hPC : ∀ p ∈ P, p ∉ C := fun p hp hc => hXP p (hCX p hc) hp
  have hPR : ∀ p ∈ P, p ∉ reps := by
    intro p hp hr
    have h1 := hP p hp
    have h2 := (ho.written_range p (hrepA p hr)).1
    omega
  let extras := (List.range frontier).map (fun v => R.onTy (.fvar v)) ++
    K.map (fun k => R.onTy (.fvar k)) ++ F.map R.onTy
  obtain ⟨W, hW, hWavoid, hmove, hblock, hDLC, hBackLC, hPoolFix, hForward, hBackward, hTargets, hRestore⟩ :=
    hres.dodge frontier (opened - frontier) extras [] hctx hstateB hP hdeclLC hdeclWF.nodup hXlen hGX
      (fun i hi => (hprefixData i hi).2)
      (by
        intro v hv hb
        have hhigh := (List.mem_append.mp hv).elim (hGhigh v) (hXhigh v)
        have hlt := freshVars_lt v hb
        omega)
  let D := blockList frontier W (opened - frontier)
  let backD := blockListBack frontier W (opened - frontier)
  let moved := Subst.conj (blockSwap frontier W (opened - frontier)) R
  change RecResidual P (D.onCtx declCtx) (declSpecs.map (RecSpec.onSubstSource D)) declPrefixes G Xs ctx state past.flatten moved at hmove
  have hAblock : ∀ a ∈ A, a ∈ freshVars frontier (opened - frontier) := by
    intro a ha
    obtain ⟨hlo, hhi⟩ := ho.written_range a ha
    unfold freshVars
    exact List.mem_map.mpr ⟨a - frontier, List.mem_range.mpr (by omega), by omega⟩
  let allTargets := declCtx.env.map PolyTy.body ++ declSpecs.map (fun spec => spec.monoEntry.body) ++
    (recCompletedSchemes declSpecs declPrefixes G).map PolyTy.body ++ extras
  have hTarget : ∀ ty ∈ allTargets, backD.onTy (D.onTy ty) = ty ∧ ∀ a ∈ A, a ∉ (D.onTy ty).freeVars := by
    intro ty ht
    exact ⟨(hTargets ty ht).1, fun a ha => (hTargets ty ht).2 a (hAblock a ha)⟩
  have hCtxT : ∀ M ∈ declCtx.env, M.body ∈ allTargets := by
    intro M hm
    have hh : M.body ∈ declCtx.env.map PolyTy.body := List.mem_map.mpr ⟨M, hm, rfl⟩
    simp only [allTargets, List.mem_append]
    tauto
  have hSpecT : ∀ spec ∈ declSpecs, spec.monoEntry.body ∈ allTargets := by
    intro spec hs
    have hh : spec.monoEntry.body ∈ declSpecs.map (fun spec => spec.monoEntry.body) := List.mem_map.mpr ⟨spec, hs, rfl⟩
    simp only [allTargets, List.mem_append]
    tauto
  have hCompleteT : ∀ M ∈ recCompletedSchemes declSpecs declPrefixes G, M.body ∈ allTargets := by
    intro M hm
    have hh : M.body ∈ (recCompletedSchemes declSpecs declPrefixes G).map PolyTy.body := List.mem_map.mpr ⟨M, hm, rfl⟩
    simp only [allTargets, List.mem_append]
    tauto
  have hExtraT : ∀ ty ∈ extras, ty ∈ allTargets := by
    intro ty ht
    simp only [allTargets, List.mem_append]
    tauto
  have hBackX : ∀ x ∈ Xs, backD.onTy (.fvar x) = .fvar x :=
    fun x hx => (hPoolFix x (List.mem_append_right _ hx)).2
  have hForwardX : ∀ x ∈ Xs, D.onTy (.fvar x) = .fvar x :=
    fun x hx => (hPoolFix x (List.mem_append_right _ hx)).1
  have hFinite : ∀ ty ∈ allTargets, (∀ x ∈ Xs, x ∉ ty.freeVars) →
      B.onTy (D.onTy ty) = D.onTy ty ∧ ∀ y ∈ Ys, y ∉ (D.onTy ty).freeVars := by
    intro ty ht hx
    exact Ty.prefix_normalize_fresh (hTarget ty ht).1 hBackX hx (hTarget ty ht).2 hrepA hCX
  have hDlow : ∀ v, v < frontier → D.onTy (.fvar v) = .fvar v := by
    intro v hv
    apply Ty.substFvars_eq_self_of_no_key
    intro pair hp hc
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hp
    simp only [Ty.freeVars, List.mem_singleton] at hc
    omega
  have hDP : ∀ p ∈ P, D.onTy (.fvar p) = .fvar p := fun p hp => hDlow p (hP p hp)
  have hagD : Subst.AgreesBelow frontier (R ++ D) moved := by
    intro v hv
    simpa only [Subst.onTy_append] using (hForward (.fvar v) (.fvar hv)).symm
  have hCtxMove : D.onCtx (R.onCtx (state.rhsCtx ctx)) = moved.onCtx (state.rhsCtx ctx) := by
    simpa only [Subst.onCtx_append] using Subst.onCtx_congr hagD (hstateB.rhsCtx hctx)
  have hMovedSource : ∀ (raw : Input) (candidate : Input),
      (∀ v ∈ raw.rigidVars, v < frontier) → raw.substTyFvars R = candidate →
      (∀ v ∈ candidate.rigidVars, v ∈ P) → raw.substTyFvars moved = candidate := by
    intro raw candidate hb he hs
    calc
      _ = (raw.substTyFvars R).substTyFvars D := by
        rw [← raw.substTyFvars_append]
        exact raw.substTyFvars_congr (fun v hv => (hagD v (hb v hv)).symm)
      _ = candidate := by rw [he]; exact candidate.substTyFvars_eq_self_of_fixes (fun v hv => hDP v (hs v hv))
  have hMovedAnn : ∀ ann ∈ anns, ann.substTyFvars moved = ann.substTyFvars R := by
    intro ann ha
    have hca : ann.substTyFvars R ∈ declAnns := by rw [← hannEq]; exact List.mem_map.mpr ⟨ann, ha, rfl⟩
    calc
      _ = (ann.substTyFvars R).substTyFvars D := by
        rw [← ann.substTyFvars_append]
        exact ann.substTyFvars_congr (fun v hv => (hagD v (hRawAnn ann ha v hv)).symm)
      _ = ann.substTyFvars R := (ann.substTyFvars R).substTyFvars_eq_self_of_fixes
        (fun v hv => hDP v (hdeclAnn _ hca v hv))
  have hGetNames : ∀ i ns, i ∈ component → names[i]? = some ns →
      ns = recRenameNames G Xs (declPrefixes[i]?.getD []) := by
    intro i ns hi hn
    rw [List.getElem?_mapIdx] at hn
    obtain ⟨old, ho, he⟩ := Option.map_eq_some_iff.mp hn
    simpa only [if_pos hi, ho, Option.getD_some] using he.symm
  have hzero : ∀ i ann ns, anns[i]? = some ann → names[i]? = some ns → i ∉ component → ns = [] := by
    intro i ann ns ha hn hi
    rw [List.getElem?_mapIdx] at hn
    obtain ⟨old, ho, he⟩ := Option.map_eq_some_iff.mp hn
    simpa only [if_neg hi] using he.symm
  have hselectedMono : ∀ i ∈ component, ∃ ty, state.specs[i]? = some (.mono ty) := by
    intro i hi
    have hm : i ∈ (past ++ component :: rest).flatten := by
      simp only [List.flatten_append, List.flatten_cons, List.mem_append]
      tauto
    exact hframe.mono_at_unsigned ((hvalid.covers_unsigned i (hvalid.bounded i hm)).mp hm)
  let targets := state.specs.map (fun spec => moved.onTy spec.monoEntry.body)
  have hTargetsLen : targets.length = anns.length := by simp only [targets, List.length_map, hframe.specs_length]
  have htarget : ∀ i ty, i ∈ component → state.specs[i]? = some (.mono ty) → targets[i]? = some (moved.onTy ty) := by
    intro i ty hi ht
    simp only [targets, List.getElem?_map, ht, Option.map_some, RecSpec.monoEntry, PolyTy.mkTrivial]
  have hfit : ∀ i ann ns target, i ∈ component → anns[i]? = some ann →
      names[i]? = some ns → targets[i]? = some target →
      (ann.substTyFvars moved).RecFits ns target ∧ ns.length = ann.recPrefixCount ∧ target.IsLC := by
    intro i ann ns target hi ha hn ht
    obtain ⟨ty, hty⟩ := hselectedMono i hi
    have hiRhs : i < bindings.length := by
      have := (List.getElem?_eq_some_iff.mp ha).1
      omega
    have hr := List.getElem?_eq_getElem hiRhs
    have ht' := htarget i ty hi hty
    have he : target = moved.onTy ty := Option.some.inj (ht.symm.trans ht')
    subst target
    have hns := hGetNames i ns hi hn
    rw [hns]
    obtain ⟨hf0, hcount, htyped⟩ := hview i ann bindings[i] ty hi ha hr hty
    have hnSub : ∀ v ∈ recRenameNames G Xs (declPrefixes[i]?.getD []), v ∈ Xs :=
      recRenameNames_mem hXlen (hprefixData i (List.getElem?_eq_some_iff.mp (hres.mono i ty hty).choose_spec).1).2
    have him : (recRenameNames G Xs (declPrefixes[i]?.getD [])).map (fun x => D.onTy (.fvar x)) =
        (recRenameNames G Xs (declPrefixes[i]?.getD [])).map Ty.fvar :=
      List.map_congr_left (fun x hx => hForwardX x (hnSub x hx))
    refine ⟨?_, hcount, Subst.onTy_lc hmove.lc (hstateLC.1 _ (List.mem_of_getElem? hty))⟩
    rw [hMovedAnn ann (List.mem_of_getElem? ha), hForward ty (hstateB.1 _ (List.mem_of_getElem? hty))]
    have hh := hf0.onSubst_images hDLC him
    rw [(ann.substTyFvars R).substTyFvars_eq_self_of_fixes (fun v hv => hDP v (hdeclAnn _
      (by rw [← hannEq]; exact List.mem_map.mpr ⟨ann, List.mem_of_getElem? ha, rfl⟩) v hv))] at hh
    exact hh
  have hsource : ∀ i raw, i ∈ component → bindings[i]? = some raw →
      ∃ candidate, declBindings[i]? = some candidate ∧ raw.substTyFvars moved = candidate ∧
        ∀ v ∈ candidate.rigidVars, v ∈ P := by
    intro i raw hi hr
    have he : declBindings[i]? = some (raw.substTyFvars R) := by rw [← hrhsEq, List.getElem?_map, hr, Option.map_some]
    exact ⟨raw.substTyFvars R, he,
      hMovedSource raw _ (hRawRhs raw (List.mem_of_getElem? hr)) rfl
        (hdeclRhs _ (List.mem_of_getElem? he)), hdeclRhs _ (List.mem_of_getElem? he)⟩
  have htypedMoved : ∀ i raw candidate ty ns, i ∈ component → bindings[i]? = some raw →
      declBindings[i]? = some candidate → state.specs[i]? = some (.mono ty) → names[i]? = some ns →
      Typing (P ++ ns) (moved.onCtx (state.rhsCtx ctx)) (candidate.openTyVars ns) (moved.onTy ty) := by
    intro i raw candidate ty ns hi hr hc ht hn
    have hiAnn : i < anns.length := by have := (List.getElem?_eq_some_iff.mp hr).1; omega
    have ha := List.getElem?_eq_getElem hiAnn
    have he : raw.substTyFvars R = candidate := by
      have hh := congrArg (fun bs : List Input => bs[i]?) hrhsEq
      simpa only [List.getElem?_map, hr, Option.map_some, hc, Option.some.injEq] using hh
    have hns := hGetNames i ns hi hn
    obtain ⟨_, _, ht0⟩ := hview i anns[i] raw ty hi ha hr ht
    rw [← hns, he] at ht0
    have hnSub : ∀ v ∈ ns, v ∈ Xs := by
      intro v hv
      exact hCX v (List.mem_flatten.mpr ⟨ns, List.mem_of_getElem? hn, hv⟩)
    have him : ns.map (fun x => D.onTy (.fvar x)) = ns.map Ty.fvar :=
      List.map_congr_left (fun x hx => hForwardX x (hnSub x hx))
    have htrans := ht0.opened_source_onSubst hDLC hDP him him (hdeclRhs candidate (List.mem_of_getElem? hc))
    rw [hCtxMove, ← hForward ty (hstateB.1 _ (List.mem_of_getElem? ht))] at htrans
    exact htrans
  have hXpoly : ∀ scheme, .poly scheme ∈ declSpecs → ∀ x ∈ Xs, x ∉ scheme.body.freeVars := by
    intro scheme hs x hx hv
    have hm : some scheme ∈ declAnns.map LetAnn.recModeAnn := by
      rw [← hdeclWF.anns_eq]
      exact List.mem_map.mpr ⟨.poly scheme, hs, rfl⟩
    obtain ⟨ann, ha, he⟩ := List.mem_map.mp hm
    cases ann with
    | absent | template _ | partialForall _ _ => cases he
    | complete sigma =>
      cases Option.some.inj he
      exact hXP x hx (hdeclAnn (.complete scheme) ha x hv)
  have hXspec : ∀ x ∈ Xs, ∀ spec ∈ declSpecs, x ∉ spec.freeVars := by
    intro x hx spec hs
    cases spec with
    | mono ty => exact hXmono x hx ty hs
    | poly scheme => exact hXpoly scheme hs x hx
  have hDXfresh : ∀ ty ∈ allTargets, (∀ x ∈ Xs, x ∉ ty.freeVars) →
      ∀ x ∈ Xs, x ∉ (D.onTy ty).freeVars := by
    intro ty ht hold x hx hv
    have hh : x ∈ (backD.onTy (D.onTy ty)).freeVars := Ty.mem_freeVars_substFvars_image.mpr
      ⟨x, hv, by change x ∈ (backD.onTy (.fvar x)).freeVars; rw [hBackX x hx]; exact List.mem_singleton_self x⟩
    rw [(hTarget ty ht).1] at hh
    exact hold x hx hh
  have hMonoMovedLC : ∀ ty, .mono ty ∈ declSpecs.map (RecSpec.onSubstSource D) → ty.IsLC := by
    intro ty ht
    obtain ⟨old, ho, he⟩ := List.mem_map.mp ht
    cases old with
    | poly scheme => cases he
    | mono original => cases he; exact Subst.onTy_lc hDLC (hdeclWF.mono_lc original ho)
  have hBctx : B.onCtx (D.onCtx declCtx) = D.onCtx declCtx := by
    apply congrArg₂ Ctx.mk
    · change ((declCtx.env.map D.onPolyTy).map B.onPolyTy) = declCtx.env.map D.onPolyTy
      rw [List.map_map]
      apply List.map_congr_left
      intro M hm
      exact congrArg (PolyTy.mk M.paramCount) (hFinite M.body (hCtxT M hm)
        (fun x hx hv => hXctxP x hx (List.mem_append_left _ (Env.mem_freeVars_iff.mpr ⟨M, hm, hv⟩)))).1
    · rfl
  have hBpoly : ∀ scheme, .poly scheme ∈ declSpecs.map (RecSpec.onSubstSource D) → B.onPolyTy scheme = scheme := by
    intro scheme hs
    obtain ⟨old, ho, he⟩ := List.mem_map.mp hs
    cases old with
    | mono ty => cases he
    | poly original =>
      cases he
      exact congrArg (PolyTy.mk original.paramCount) (hFinite original.body (hSpecT _ ho) (hXpoly original ho)).1
  have hCompletedWF : ∀ i ty, (declSpecs.map (RecSpec.onSubstSource D))[i]? = some (.mono ty) → i ∈ past.flatten →
      (recScheme (declPrefixes[i]?.getD []) G ty).WF := by
    intro i ty hi _
    exact recScheme_wf (hMonoMovedLC ty (List.mem_of_getElem? hi))
  have hBcompleted : ∀ i ty, (declSpecs.map (RecSpec.onSubstSource D))[i]? = some (.mono ty) → i ∈ past.flatten →
      B.onPolyTy (recScheme (declPrefixes[i]?.getD []) G ty) = recScheme (declPrefixes[i]?.getD []) G ty := by
    intro i ty hi _
    obtain ⟨original, ho, rfl⟩ := RecSpec.mono_getElem?_map_onSubstSource hi
    apply congrArg (PolyTy.mk _)
    apply Subst.onTy_eq_self_of_fixes
    intro v hv
    apply zip_fvars_fixes
    intro hc
    exact hDXfresh original (hSpecT _ (List.mem_of_getElem? ho))
      (fun x hx => hXmono x hx original (List.mem_of_getElem? ho))
      v (hCX v (List.mem_dedup.mp hc)) (Ty.freeVars_closeOver_subset hv)
  have hBmono : ∀ ty, .mono ty ∈ declSpecs.map (RecSpec.onSubstSource D) →
      B.onTy (Ty.renameG G Xs ty) = Ty.renameG G Ys ty := by
    intro ty ht
    obtain ⟨old, ho, he⟩ := List.mem_map.mp ht
    cases old with
    | poly scheme => cases he
    | mono original =>
      cases he
      apply zip_fvars_renameG hRepLen (List.nodup_dedup _) hCD
        (Subst.onTy_lc hDLC (hdeclWF.mono_lc original ho)) hdeclWF.nodup hXlen hGX hGR
      intro c hc
      exact hDXfresh original (hSpecT _ ho) (fun x hx => hXmono x hx original ho) c (hCX c (List.mem_dedup.mp hc))
  obtain ⟨U, hU, hUag, hUP, hures, himages, huTyped⟩ := hmove.normalize_openings ho hstateB hctx hP
    hRawAnn hRawRhs hlen names targets hNames hTargetsLen hzero hfit
    (fun c hc => hXA c (hCX c hc)) hPC hBctx hBpoly hCompletedWF hBcompleted hBmono htarget htypedMoved hsource
  change Subst.AgreesBelow frontier (moved ++ B) U at hUag
  change RecResidual (P ++ reps) (D.onCtx declCtx) (declSpecs.map (RecSpec.onSubstSource D))
    declPrefixes G Ys ctx state past.flatten U at hures
  have hUFacts : ∀ ty, Ty.BelowFvars frontier ty → U.onTy ty = B.onTy (moved.onTy ty) := by
    intro ty hb
    simpa only [Subst.onTy_append] using (Subst.onTy_congr hUag hb).symm
  have hOldImageT : ∀ v, v < frontier → R.onTy (.fvar v) ∈ allTargets := by
    intro v hv
    apply hExtraT
    exact List.mem_append_left _ (List.mem_append_left _ (List.mem_map.mpr ⟨v, List.mem_range.mpr hv, rfl⟩))
  have hMovedAvoid : ∀ ty, Ty.BelowFvars frontier ty → ∀ a ∈ A, a ∉ (moved.onTy ty).freeVars := by
    intro ty hb a ha hv
    obtain ⟨v, hv, him⟩ := Ty.mem_freeVars_substFvars_image.mp hv
    change a ∈ (moved.onTy (.fvar v)).freeVars at him
    rw [hForward (.fvar v) (.fvar (hb.mem_lt v hv))] at him
    exact (hTarget _ (hOldImageT v (hb.mem_lt v hv))).2 a ha him
  have hFiniteActual : ∀ ty, Ty.BelowFvars frontier ty → (∀ x ∈ Xs, x ∉ (R.onTy ty).freeVars) →
      B.onTy (moved.onTy ty) = moved.onTy ty ∧ ∀ y ∈ Ys, y ∉ (moved.onTy ty).freeVars := by
    intro ty hb hx
    exact Ty.prefix_normalize_fresh (hBackward ty hb) hBackX hx (hMovedAvoid ty hb) hrepA hCX
  have hFixedOld := hres.fixedCtx_avoids hframe
    (fun x hx hv => hXctxP x hx (List.mem_append_left _ hv)) hXspec
  have hFixedFinite : ∀ M ∈ (state.fixedCtx ctx).env,
      B.onTy (moved.onTy M.body) = moved.onTy M.body ∧ ∀ y ∈ Ys, y ∉ (moved.onTy M.body).freeVars := by
    intro M hm
    apply hFiniteActual M.body (hstateB.fixedCtx hctx M hm)
    intro x hx hv
    exact hFixedOld x hx (Env.mem_freeVars_iff.mpr ⟨R.onPolyTy M,
      List.mem_map.mpr ⟨M, hm, rfl⟩, hv⟩)
  have hYsCtx : ∀ y ∈ Ys, y ∉ (U.onCtx (state.fixedCtx ctx)).env.freeVars := by
    intro y hy hv
    obtain ⟨scheme, hs, hv⟩ := Env.mem_freeVars_iff.mp hv
    obtain ⟨M, hm, rfl⟩ := List.mem_map.mp hs
    change y ∈ (U.onTy M.body).freeVars at hv
    rw [hUFacts M.body (hstateB.fixedCtx hctx M hm), (hFixedFinite M hm).1] at hv
    exact (hFixedFinite M hm).2 y hy hv
  have hYsK : ∀ y ∈ Ys, ∀ k ∈ K, y ∉ (U.onTy (.fvar k)).freeVars := by
    intro y hy k hk hv
    have hh := hFiniteActual (.fvar k) (.fvar (hK k hk)) (fun x hx => hXsK x hx k hk)
    rw [hUFacts (.fvar k) (.fvar (hK k hk)), hh.1] at hv
    exact hh.2 y hy hv
  have hYsF : ∀ y ∈ Ys, y ∉ softVars (substSoft U F) := by
    intro y hy hv
    obtain ⟨ty, ht, hv⟩ := TyList.mem_freeVars_iff.mp hv
    obtain ⟨old, ho, rfl⟩ := List.mem_map.mp ht
    have hh := hFiniteActual old (hF old ho) (fun x hx hv => hXsF x hx
      (TyList.mem_freeVars_iff.mpr ⟨R.onTy old, List.mem_map.mpr ⟨old, ho, rfl⟩, hv⟩))
    rw [hUFacts old (hF old ho), hh.1] at hv
    exact hh.2 y hy hv
  have hUPbelow : ∀ p ∈ P ++ reps, p < opened := by
    intro p hp
    exact (List.mem_append.mp hp).elim (fun hp => (hP p hp).trans_le hopen) (fun hp => (ho.written_range p (hrepA p hp)).2)
  have hLocalFreeze : ∀ (i : Nat) (rhs : Input), i ∈ component → bindings[i]? = some rhs →
      ∀ v ∈ rhs.rigidVars, v ∈ K → v ∉ softVars F → U.onTy (.fvar v) = .fvar v := by
    intro i rhs hi hr v hv hk hn
    rw [hUFacts (.fvar v) (.fvar (hK v hk)), hForward (.fvar v) (.fvar (hK v hk)),
      hrhsFreeze rhs (List.mem_of_getElem? hr) v hv hk hn, hDlow v (hK v hk)]
    apply zip_fvars_fixes
    intro hc
    have hhi := hXhigh v (hCX v (List.mem_dedup.mp hc))
    have hlo := hK v hk
    omega
  have hSolveU : ∀ (i : Nat) (opening : RecOpening) (ty expected : Ty), i ∈ component →
      openings[i]? = some opening → state.specs[i]? = some (.mono ty) → opening.expected = some expected →
      U.onTy expected = U.onTy ty := by
    intro i opening ty expected hi hop hty he
    have hib : i < names.length := by
      have hs := (List.getElem?_eq_some_iff.mp hty).1
      rw [hframe.specs_length] at hs
      omega
    have hn := List.getElem?_eq_getElem hib
    exact (himages i opening names[i] (moved.onTy ty) hi hop hn (htarget i ty hi hty)).2 expected he |>.trans
      (hUFacts ty (hstateB.1 _ (List.mem_of_getElem? hty))).symm
  have hMovedPrefix : ∀ (i : Nat) (ty : Ty), (declSpecs.map (RecSpec.onSubstSource D))[i]? = some (.mono ty) →
      (declPrefixes[i]?.getD []).Nodup ∧ ∀ v ∈ declPrefixes[i]?.getD [], v ∈ G := by
    intro i ty ht
    obtain ⟨old, ho, rfl⟩ := RecSpec.mono_getElem?_map_onSubstSource ht
    exact hprefixData i (List.getElem?_eq_some_iff.mp ho).1
  have hYsTypes : ∀ y ∈ Ys, ∀ ty, .mono ty ∈ declSpecs.map (RecSpec.onSubstSource D) → y ∉ ty.freeVars := by
    intro y hy ty ht
    obtain ⟨old, ho, he⟩ := List.mem_map.mp ht
    cases old with
    | poly scheme => cases he
    | mono original =>
      cases he
      exact (hFinite original (hSpecT _ ho) (fun x hx => hXmono x hx original ho)).2 y hy
  have hYsND : Ys.Nodup := recRenameNames_nodup_partial hRepLen (List.nodup_dedup _) hReps hCD hXnd
    (fun r hr hx => hXR r hx hr)
  have hGYs : ∀ g ∈ G, g ∉ Ys := by
    intro g hg hy
    exact (recRenameNames_mem_source_or_target hy).elim (hGX g hg) (hGR g hg)
  refine ⟨{
    protectedVars := P ++ reps
    candidateCtx := D.onCtx declCtx
    candidateSpecs := declSpecs.map (RecSpec.onSubstSource D)
    opening := Ys
    subst := U
    lc := hU
    fixes := hUP
    record := hures
    below := hUPbelow
    freeze := hLocalFreeze
    solves := hSolveU
    typed := huTyped
    written := ?_
    monoLC := hMonoMovedLC
    poolND := hdeclWF.nodup
    prefixData := hMovedPrefix
    length := ?_
    nodup := hYsND
    disjoint := hGYs
    typesFresh := hYsTypes
    ctxFresh := hYsCtx
    rigidFresh := hYsK
    softFresh := hYsF
    preservesRigid := ?_
    restore := ?_ }⟩
  · intro i opening hi hop
    have hib : i < names.length := by
      have := (List.getElem?_eq_some_iff.mp hop).1
      have := ho.length
      omega
    have hn := List.getElem?_eq_getElem hib
    obtain ⟨ty, hty⟩ := hselectedMono i hi
    have hm := (himages i opening names[i] (moved.onTy ty) hi hop hn (htarget i ty hi hty)).1
    rw [hm, hGetNames i names[i] hi hn, ← recRenameNames_map_images hXlen
      (hprefixData i (List.getElem?_eq_some_iff.mp (hres.mono i ty hty).choose_spec).1).2]
  · simpa only [Ys, recRenameNames_length] using hXlen
  · intro hRK k hk
    rw [hUFacts (.fvar k) (.fvar (hK k hk)), hForward (.fvar k) (.fvar (hK k hk)),
      hRK k hk, hDlow k (hK k hk)]
    apply zip_fvars_fixes
    intro hc
    have hhi := hXhigh k (hCX k (List.mem_dedup.mp hc))
    have hlo := hK k hk
    omega
  · intro solved final T hagClose hTRes
    have hBRestored := hTRes.restore_prefixRepresentatives hRepLen hReps hCX hXR hdeclWF.nodup hXlen hGX hGR
      hMonoMovedLC
      (by
        intro ty ht
        obtain ⟨old, ho, he⟩ := List.mem_map.mp ht
        cases old with
        | poly scheme => cases he
        | mono original => cases he; exact hDXfresh original (hSpecT _ ho) (fun x hx => hXmono x hx original ho))
      (by
        intro ty ht r hr
        obtain ⟨old, ho, he⟩ := List.mem_map.mp ht
        cases old with
        | poly scheme => cases he
        | mono original => cases he; exact (hTarget original (hSpecT _ ho)).2 r (hrepA r hr))
      (by
        intro scheme hs r hr
        obtain ⟨old, ho, he⟩ := List.mem_map.mp hs
        cases old with
        | mono ty => cases he
        | poly original => cases he; exact (hTarget original.body (hSpecT _ ho)).2 r (hrepA r hr))
      (by
        intro r hr hv
        obtain ⟨M, hm, hv⟩ := Env.mem_freeVars_iff.mp hv
        obtain ⟨old, ho, rfl⟩ := List.mem_map.mp hm
        exact (hTarget old.body (hCtxT old ho)).2 r (hrepA r hr) hv)
      hPR
    have hFinal := hRestore _ _ _ _ hBRestored
    have hagB : Subst.AgreesBelow frontier (moved ++ B) (solved ++ T) := by
      intro v hv
      exact (hUag v hv).trans (hagClose v (hv.trans_le hopen))
    have hagPopB := hagB.restore_prefixRepresentatives hRepLen hReps hCD
      (fun v hv r hr => hMovedAvoid (.fvar v) (.fvar hv) r (hrepA r hr))
    have hagFinal := hagPopB.restore_after (fun v hv => hBackward (.fvar v) (.fvar hv))
    exact ⟨_, hFinal.lc, hFinal.fixes, hagFinal, hFinal⟩


set_option maxHeartbeats 3000000 in
theorem RecResidual.successful_step
    {P G Xs : List Nat} {declCtx : Ctx} {declAnns : List LetAnn}
    {declBindings : List Input} {declSpecs : List RecSpec}
    {declGroups declPrefixes : List (List Nat)} {cutoff base : Nat} :
  RecGroups.ValidResidualGroups (declAnns.map LetAnn.recModeAnn) (declBindings.map Input.erase) declGroups →
  RecSpecs.WF (declAnns.map LetAnn.recModeAnn) (declBindings.map Input.erase) declSpecs G →
  RecPrefixesWF declAnns declSpecs declPrefixes G →
  (∀ g ∈ G, g ∉ declCtx.env.freeVars ++ P) →
  (∀ ann ∈ declAnns, ∀ v ∈ ann.rigidVars, v ∈ P) →
  (∀ rhs ∈ declBindings, ∀ v ∈ rhs.rigidVars, v ∈ P) →
  (∀ (stage : Nat) (component : List Nat), declGroups[stage]? = some component →
    ∀ (member : Nat), member ∈ component → ∀ (rhs : Input) (ann : LetAnn) (names : List Nat) (ty : Ty),
      declBindings[member]? = some rhs → declAnns[member]? = some ann →
      declPrefixes[member]? = some names → declSpecs[member]? = some (.mono ty) →
      ann.RecFits (recRenameNames G Xs names) (Ty.renameG G Xs ty)) →
  (∀ (stage : Nat) (component : List Nat), declGroups[stage]? = some component →
    ∀ (member : Nat), member ∈ component → ∀ (rhs : Input) (ann : LetAnn) (names : List Nat) (ty : Ty),
      declBindings[member]? = some rhs → declAnns[member]? = some ann →
      declPrefixes[member]? = some names → declSpecs[member]? = some (.mono ty) →
      Typing (P ++ Xs) (recStageCtx declCtx declSpecs declPrefixes (declGroups.take stage).flatten G Xs)
        (rhs.openTyVars (recRenameNames G Xs names)) (Ty.renameG G Xs ty)) →
  (∀ g ∈ G, cutoff ≤ g) → (∀ x ∈ Xs, cutoff ≤ x) →
  Xs.length = G.length → Xs.Nodup →
  (∀ g ∈ G, g ∉ Xs) →
  (∀ x ∈ Xs, ∀ (ty : Ty), .mono ty ∈ declSpecs → x ∉ ty.freeVars) →
  (∀ x ∈ Xs, x ∉ declCtx.env.freeVars ++ P) →
∀ {K : List Nat} {F : List Ty} {frontier opened first : Nat}
      {ctx : Ctx} {anns : List LetAnn} {bindings : List Input}
      {state exported : RecState} {past rest : List (List Nat)} {component : List Nat}
      {openings : List RecOpening} {pre current R : Subst}
      {outputs : List (Option Expr)} {facts : List RecFacts},
      OpenRecAnns component 0 frontier anns opened openings →
      CheckRecShapes K ((state.installOpenings component openings).shapes component openings) pre →
      InferRecComponent K
        (substSoft pre (F ++ (openings.flatMap RecOpening.written).map Ty.fvar)) component 0 opened
        (((state.installOpenings component openings).onSubst pre).rhsCtx (pre.onCtx ctx))
        ((openRecSources openings bindings).map (Input.substTyFvars pre))
        ((state.installOpenings component openings).onSubst pre).specs first current outputs facts →
      FinishRecComponent K (softVars (substSoft (pre ++ current) F)) component
        ((pre ++ current).onCtx ctx) ((state.installOpenings component openings).onSubst (pre ++ current))
        outputs facts exported →
      (∀ {κ F' Ψ c e Ψ' T output ty}, e.size ≤ sizeBindings bindings →
        (hi : Infer κ F' Ψ c e Ψ' T output ty) → Infer.SourcePrincipal hi) →
      first ≤ cutoff →
      RecGroups.ValidResidualGroups (anns.map LetAnn.recModeAnn) (bindings.map Input.erase)
        (past ++ component :: rest) →
      past ++ component :: rest = RecGroup.inferenceSccs
        (anns.map LetAnn.recModeAnn) (bindings.map Input.erase) →
      state.Frame base K F ctx anns past.flatten →
      state.LC → state.Below frontier → CtxWF ctx → CtxBelow frontier ctx →
      base + bindings.length ≤ frontier →
      (∀ k ∈ K, k < frontier) → (∀ t ∈ F, Ty.BelowFvars frontier t) →
      (∀ p ∈ P, p < frontier) →
      RecResidual P declCtx declSpecs declPrefixes G Xs ctx state past.flatten R →
      (∀ x ∈ Xs, ∀ k ∈ K, x ∉ (R.onTy (.fvar k)).freeVars) →
      (∀ x ∈ Xs, x ∉ softVars (substSoft R F)) →
      (∀ ann ∈ anns, ∀ v ∈ ann.rigidVars, v ∈ K ++ softVars F) →
      (∀ rhs ∈ bindings, SourceScope K F rhs) →
      anns.map (LetAnn.substTyFvars R) = declAnns →
      bindings.map (Input.substTyFvars R) = declBindings →
      (∀ ann ∈ anns, ∀ v ∈ ann.rigidVars,
        v ∈ K → v ∉ softVars F → R.onTy (.fvar v) = .fvar v) →
      (∀ rhs ∈ bindings, ∀ v ∈ rhs.rigidVars,
        v ∈ K → v ∉ softVars F → R.onTy (.fvar v) = .fvar v) →
      ∃ U : Subst, (∀ pair ∈ U, pair.2.IsLC) ∧
        (∀ p ∈ P, U.onTy (.fvar p) = .fvar p) ∧
        Subst.AgreesBelow frontier R ((pre ++ current) ++ U) ∧
        RecResidual P declCtx declSpecs declPrefixes G Xs ((pre ++ current).onCtx ctx)
          exported (past.flatten ++ component) U := by
  intro hdeclValid hdeclWF hprefix hGfresh hdeclAnn hdeclRhs hdeclFits hdeclTypes
    hGhigh hXhigh hXlen hXnd hGX hXmono hXctxP K F frontier opened first ctx anns bindings state exported past rest component openings pre current R outputs facts
    ho hp hc hf hInfer hcutoff hvalid hcanonical hframe hstateLC hstateB hctxWF hctx hbase hK hF hP hres
    hXsK hXsF hannScope hrhsScope hannEq hrhsEq hannFreeze hrhsFreeze
  obtain ⟨prepared⟩ := RecResidual.prepare_component hdeclValid hdeclWF hprefix hGfresh hdeclAnn hdeclRhs
    hdeclFits hdeclTypes hGhigh hXhigh hXlen hXnd hGX hXmono hXctxP
    ho (hc.frontier_le.trans hcutoff) hvalid hcanonical hframe hstateLC hstateB hctxWF hctx hbase hK hF hP hres
    hXsK hXsF hannScope hrhsScope hannEq hrhsEq hannFreeze hrhsFreeze
  obtain ⟨T, hT, hTP, hag, hresT⟩ := prepared.record.close_opened_component ho hp hc hf hInfer
    hstateLC hstateB hctxWF hctx hK hF prepared.below (by simpa only [List.length_map] using hvalid.length)
    hannScope hrhsScope prepared.freeze prepared.solves prepared.typed
    (hframe.exports_length.trans hframe.specs_length.symm)
    (by
      intro i hi hd
      have hh : (past.flatten ++ (component ++ rest.flatten)).Nodup := by
        simpa only [List.flatten_append, List.flatten_cons] using hvalid.flatten_nodup
      exact (List.nodup_append.mp hh).2.2 i hd i (List.mem_append_left _ hi) rfl)
    prepared.monoLC prepared.poolND prepared.prefixData prepared.length prepared.nodup prepared.disjoint
    prepared.typesFresh prepared.ctxFresh prepared.rigidFresh prepared.softFresh
  exact prepared.restore (pre ++ current) exported T hag hresT

theorem _root_.Infer.sourcePrincipal (h : Infer K F frontier ctx input next subst output ty) :
    Infer.SourcePrincipal h := by
  match h with
  | .backend hemb hi hctx hK hr hd => exact Infer.sourcePrincipal_backend hemb hi hctx hK hr hd
  | .lambda hs seed hb => exact Infer.sourcePrincipal_lambda hs seed hb hb.sourcePrincipal
  | .app hs hf ha hu => exact Infer.sourcePrincipal_app hs hf ha hu hf.sourcePrincipal ha.sourcePrincipal
  | .letIn hs hr hc hb => exact Infer.sourcePrincipal_letIn hs hr hc hb hr.sourcePrincipal hb.sourcePrincipal
  | .letSignature hs hp ha hs' hr hc he hb =>
    exact Infer.sourcePrincipal_letSignature hs hp ha hs' hr hc he hb hr.sourcePrincipal hb.sourcePrincipal
  | .match_ hscope hs hne hb =>
    exact Infer.sourcePrincipal_match hscope hs hne hb hs.sourcePrincipal
      (fun body hbody {_ _ _ _ _ _ _ _} hi => hi.sourcePrincipal)
  | .letRec hscope hann hvalid hstrata hsigned hexports houtputs hbody =>
    apply Infer.sourcePrincipal_letRec_of_unsigned hscope hann hvalid hstrata hsigned hexports houtputs hbody
      (fun he hi => hi.sourcePrincipal) hbody.sourcePrincipal
    intro P declCtx declAnns declBindings declSpecs declGroups declPrefixes G Xs R
      hdeclValid hdeclWF hprefix hGfresh hdeclAnn hdeclRhs hdeclFits hdeclTypes
      hGhigh hXhigh hXlen hXnd hGX hXmono hXctxP
      hctxWF hctx hstateLC hstateB hframe hK hF hP hres hXsK hXsF hannScope hrhsScope
      hannEq hrhsEq hannFreeze hrhsFreeze
    simpa only [List.nil_append] using InferRecStrata.sourcePrincipal_residual_of_step (past := []) (base := frontier)
      (RecResidual.successful_step hdeclValid hdeclWF hprefix hGfresh hdeclAnn hdeclRhs hdeclFits hdeclTypes
        hGhigh hXhigh hXlen hXnd hGX hXmono hXctxP)
      hstrata (fun he hi => hi.sourcePrincipal) (hsigned.frontier_le.trans hbody.frontier_le)
      hvalid.1 hvalid.2 hframe hstateLC hstateB hctxWF hctx (by omega) hK hF hP hres
      hXsK hXsF hannScope hrhsScope hannEq hrhsEq hannFreeze hrhsFreeze
termination_by input.size
decreasing_by
  all_goals (simp only [Input.size, Input.size_openTyVars, Input.size_substTyFvars]; omega)

/-- The public residual contract retains independent P and its protection. -/
theorem _root_.Infer.principal (h : Infer K F frontier ctx input next subst output ty) :
    Infer.Principal h := h.sourcePrincipal.principal

end Elaboration
