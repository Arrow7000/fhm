import FHM.Elaboration.Properties

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

/-- Every scoped elaboration admits source-transforming residual factorization. -/
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
termination_by input.size
decreasing_by
  all_goals (simp only [Input.size, Input.size_openTyVars, Input.size_substTyFvars]; omega)

/-- The public residual contract retains independent P and its protection. -/
theorem _root_.Infer.principal (h : Infer K F frontier ctx input next subst output ty) :
    Infer.Principal h := h.sourcePrincipal.principal

end Elaboration
