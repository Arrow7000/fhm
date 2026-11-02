import FHM.SourceTyping
import FHM.Compatibility.Metatheory

/-! Derived complete-Core compatibility. The source typing relation has only
structural rules; this optional conversion is not a source typing constructor
or an inference soundness premise. -/

private theorem complete_ctor_of_runtime (h : RuntimeTyping.RunWT ctx (.ctor name) ty) :
    TypeOfHM ctx (.ctor name) ty := by
  cases h with
  | ctor hl ha hi => exact .ctor hl ha hi

private theorem complete_primLit_of_runtime (h : RuntimeTyping.RunWT ctx (.primLit p) ty) :
    TypeOfHM ctx (.primLit p) ty := by
  cases h <;> constructor

private theorem complete_primBinOp_of_runtime (h : RuntimeTyping.RunWT ctx (.primBinOp op) ty) :
    TypeOfHM ctx (.primBinOp op) ty := by
  cases h with
  | primBinOpIntAdd => exact .primBinOpIntAdd
  | primBinOpIntSub => exact .primBinOpIntSub
  | primBinOpIntLt ht hf => exact .primBinOpIntLt (complete_ctor_of_runtime ht) (complete_ctor_of_runtime hf)
  | primBinOpCharLt ht hf => exact .primBinOpCharLt (complete_ctor_of_runtime ht) (complete_ctor_of_runtime hf)

mutual
theorem PartialCore.Template.toCore_fits_any {template : TyTemplate} {ty : Ty}
    (h : template.toCore = some ty) (holes : PartialCore.HoleAssignment) :
    PartialCore.Template.Fits holes template ty := by
  cases template with
  | fixed => cases h; exact .fixed
  | hole | named => cases h
  | arrow a b =>
    simp only [PartialCore.Template.toCore, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨ta, ha, tb, hb, rfl⟩ := h
    exact .arrow (PartialCore.Template.toCore_fits_any ha holes) (PartialCore.Template.toCore_fits_any hb holes)
  | custom name args =>
    simp only [PartialCore.Template.toCore, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨tys, ht, rfl⟩ := h
    exact .custom (completeTypes_fits_any ht holes)
theorem completeTypes_fits_any {templates : List TyTemplate} {tys : List Ty}
    (h : completeTypes templates = some tys) (holes : PartialCore.HoleAssignment) :
    List.Forall₂ (PartialCore.Template.Fits holes) templates tys := by
  cases templates with
  | nil => cases h; exact .nil
  | cons t ts =>
    simp only [completeTypes, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨ty, ht, tys, hts, rfl⟩ := h
    exact .cons (PartialCore.Template.toCore_fits_any ht holes) (completeTypes_fits_any hts holes)
end

theorem PartialCore.Template.toCore_fits {template : TyTemplate} {ty : Ty}
    (h : template.toCore = some ty) : template.Matches ty :=
  ⟨[], by simp [PartialCore.HoleAssignment.Unique], PartialCore.Template.toCore_fits_any h []⟩

theorem completeTypes_fits {templates : List TyTemplate} {tys : List Ty}
    (h : completeTypes templates = some tys) : List.Forall₂ PartialCore.Template.Matches templates tys := by
  cases templates with
  | nil => cases h; exact .nil
  | cons t ts =>
    simp only [completeTypes, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨ty, ht, tys, hts, rfl⟩ := h
    exact .cons (PartialCore.Template.toCore_fits ht) (completeTypes_fits hts)

mutual
theorem PartialCore.Template.Fits.toCore_eq {template : TyTemplate} {ty complete : Ty}
    (h : PartialCore.Template.Fits holes template ty) (hc : template.toCore = some complete) : ty = complete := by
  cases h with
  | fixed => cases hc; rfl
  | hole | named => cases hc
  | arrow ha hb =>
    simp only [PartialCore.Template.toCore, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at hc
    obtain ⟨ta, hta, tb, htb, rfl⟩ := hc
    rw [ha.toCore_eq hta, hb.toCore_eq htb]
  | custom h =>
    simp only [PartialCore.Template.toCore, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at hc
    obtain ⟨tys, htys, rfl⟩ := hc
    rw [fitsList_toCore_eq_any h htys]
theorem fitsList_toCore_eq_any {templates : List TyTemplate} {tys complete : List Ty}
    (h : List.Forall₂ (PartialCore.Template.Fits holes) templates tys)
    (hc : completeTypes templates = some complete) : tys = complete := by
  cases h with
  | nil => cases hc; rfl
  | cons hh ht =>
    simp only [completeTypes, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at hc
    obtain ⟨ty, hty, tys, htys, rfl⟩ := hc
    rw [hh.toCore_eq hty, fitsList_toCore_eq_any ht htys]
end

theorem PartialCore.Template.Matches.toCore_eq {template : TyTemplate} {ty complete : Ty}
    (h : template.Matches ty) (hc : template.toCore = some complete) : ty = complete := by
  obtain ⟨_, _, hf⟩ := h
  exact hf.toCore_eq hc

theorem fitsList_toCore_eq {templates : List TyTemplate} {tys complete : List Ty}
    (h : List.Forall₂ PartialCore.Template.Matches templates tys)
    (hc : completeTypes templates = some complete) : tys = complete := by
  cases h with
  | nil => cases hc; rfl
  | cons hh ht =>
    simp only [completeTypes, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at hc
    obtain ⟨ty, hty, tys, htys, rfl⟩ := hc
    rw [hh.toCore_eq hty, fitsList_toCore_eq ht htys]

theorem completeBranches_length {inputs : List (MatchPattern × InferInput)}
    {cores : List (MatchPattern × Expr)} (h : completeBranches inputs = some cores) :
    inputs.length = cores.length := by
  induction inputs generalizing cores with
  | nil => cases h; rfl
  | cons head rest ih =>
    rcases head with ⟨pat, body⟩
    simp only [completeBranches, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨body', _, rest', hr, rfl⟩ := h
    simp only [List.length_cons, ih hr]

theorem completeBranches_forward {inputs : List (MatchPattern × InferInput)}
    {cores : List (MatchPattern × Expr)} (h : completeBranches inputs = some cores)
    {branch : MatchPattern × InferInput} (hb : branch ∈ inputs) :
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

theorem completeBranches_backward {inputs : List (MatchPattern × InferInput)}
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

theorem branchFreeVars_iff {branches : List (MatchPattern × Expr)} {v : Nat} :
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

theorem recGroupRefs_erase (e : Expr) (n depth : Nat) :
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
  | letRec bindings body ihbs ihb =>
    simp only [Expr.erase_letRec, Expr.recGroupRefs, List.length_map, ihb]
    congr 2
    generalize depth + bindings.length = innerDepth
    induction bindings generalizing innerDepth with
    | nil => rfl
    | cons binding rest ih =>
      rcases binding with ⟨ann, rhs⟩
      simp only [List.map_cons, RecGroupRefs.bindings]
      rw [ihbs ⟨ann, rhs⟩ List.mem_cons_self,
        ih (fun binding h => ihbs binding (List.mem_cons_of_mem _ h)) innerDepth]

def eraseRecRhs (binding : CoreRecBinding) : CoreRecBinding :=
  { binding with rhs := binding.rhs.erase }

theorem validResidualGroups_erase_iff {bindings : List CoreRecBinding} :
    RecGroups.ValidResidualGroups (bindings.map eraseRecRhs) groups ↔
      RecGroups.ValidResidualGroups bindings groups := by
  constructor
  · intro h
    refine ⟨h.nonempty, h.flatten_nodup, by simpa using h.bounded, ?_, ?_⟩
    · intro member hm
      have hc := h.covers_unsigned member (by simpa only [List.length_map] using hm)
      simp only [RecGroups.UnsignedAt, List.getElem?_map] at hc ⊢
      cases hb : bindings[member]? <;> simp only [hb, Option.map_none, Option.map_some,
        eraseRecRhs] at hc ⊢
      all_goals exact hc
    · intro stage depStage component depComponent source target binding hc hd hs ht hr href
      apply h.dependencies_first hc hd hs ht
        (by rw [List.getElem?_map, hr]; rfl)
      simpa only [List.length_map, eraseRecRhs, recGroupRefs_erase] using href
  · intro h
    exact h.map_bindings eraseRecRhs
      (by
        intro i
        simp only [RecGroups.UnsignedAt, List.getElem?_map]
        cases bindings[i]? <;> rfl)
      (fun binding _ => recGroupRefs_erase binding.rhs _ _)

theorem completeBindings_lookup {inputs : List InputRecBinding} {cores : List CoreRecBinding}
    (h : completeBindings inputs = some cores) {i : Nat} {binding : InputRecBinding}
    (hr : inputs[i]? = some binding) : ∃ core, cores[i]? = some core ∧
      binding.ann.toCore = some core.ann ∧ binding.rhs.toCore = some core.rhs := by
  induction inputs generalizing cores i with
  | nil => cases hr
  | cons head rest ih =>
    simp only [completeBindings, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨ann, ha, rhs, hh, cores, ht, rfl⟩ := h
    cases i with
    | zero => cases hr; exact ⟨_, rfl, ha, hh⟩
    | succ i => exact ih ht hr

theorem completeBindings_lookup_back {inputs : List InputRecBinding} {cores : List CoreRecBinding}
    (h : completeBindings inputs = some cores) {i : Nat} {core : CoreRecBinding}
    (hr : cores[i]? = some core) : ∃ binding, inputs[i]? = some binding ∧
      binding.ann.toCore = some core.ann ∧ binding.rhs.toCore = some core.rhs := by
  induction inputs generalizing cores i with
  | nil => cases h; cases hr
  | cons head rest ih =>
    simp only [completeBindings, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨ann, ha, rhs, hh, cores, ht, rfl⟩ := h
    cases i with
    | zero => cases hr; exact ⟨head, rfl, ha, hh⟩
    | succ i => exact ih ht hr

theorem completeBindings_data {inputs : List InputRecBinding}
    {cores : List CoreRecBinding} (h : completeBindings inputs = some cores) :
    cores.map eraseRecRhs = inputs.map InputRecBinding.recMode ∧
      ∀ binding ∈ inputs,
        binding.ann.toCore = some binding.ann.recModeAnn ∧
        binding.ann.recPrefixCount = 0 := by
  induction inputs generalizing cores with
  | nil => cases h; exact ⟨rfl, by simp⟩
  | cons binding rest ih =>
    rcases binding with ⟨ann, rhs⟩
    simp only [completeBindings, bind, pure, Option.bind_eq_some_iff,
      Option.some.injEq] at h
    obtain ⟨coreAnn, ha, coreRhs, hr, cores, ht, rfl⟩ := h
    obtain ⟨heq, hall⟩ := ih ht
    have hview := ann.annotationView_toCore ha
    have hmode : ann.recModeAnn = coreAnn := by
      simp only [Option.recModeAnn, hview]
      cases coreAnn <;> rfl
    have hprefix : ann.recPrefixCount = 0 := by
      simp only [Option.recPrefixCount, hview]
      cases coreAnn <;> rfl
    refine ⟨by simp only [List.map_cons, eraseRecRhs, InputRecBinding.recMode,
      hmode, rhs.source_toCore_erase hr, heq], ?_⟩
    intro binding hm
    rcases List.mem_cons.mp hm with rfl | hm
    · exact ⟨by simpa only [hmode] using ha, hprefix⟩
    · exact hall binding hm

theorem recScheme_empty (G : List Nat) (ty : Ty) : recScheme [] G ty = PolyTy.genGroup G ty := by
  simp [recScheme, recNames, PolyTy.genGroup, Ty.genFilter]

theorem recCompleted_empty_prefixes (specs : List RecSpec) (prefixes : List (List Nat)) (G : List Nat)
    (hp : ∀ i : Nat, prefixes[i]?.getD [] = []) :
    recCompletedSchemes specs prefixes G = specs.map (RecSpec.bodyScheme G) := by
  apply List.ext_get (by simp [recCompletedSchemes])
  intro i hi hj
  simp only [recCompletedSchemes, List.get_eq_getElem, List.getElem_mapIdx, List.getElem_map, hp]
  cases specs[i]'(by simpa using hj) <;> simp only [RecSpec.completedScheme, RecSpec.bodyScheme, recScheme_empty]

theorem recStage_empty_prefixes (ctx : Ctx) (specs : List RecSpec) (prefixes : List (List Nat)) (done G Xs : List Nat)
    (hp : ∀ i : Nat, prefixes[i]?.getD [] = []) :
    recStageCtx ctx specs prefixes done G Xs = RecSpecs.stageCtx ctx specs done G Xs := by
  unfold recStageCtx RecSpecs.stageCtx
  congr 2
  apply List.ext_get (by simp)
  intro i hi hj
  simp only [List.get_eq_getElem, List.getElem_mapIdx]
  cases specs[i]'(by simpa using hj) <;>
    simp only [recStageEntry, RecSpec.stageEntry, hp, recScheme_empty]

theorem complete_prefixes_empty {bindings : List InputRecBinding} {specs : List RecSpec}
    (hp : RecPrefixesWF bindings specs prefixes G)
    (hlen : bindings.length = specs.length)
    (hz : ∀ binding ∈ bindings, binding.ann.recPrefixCount = 0) :
    ∀ i : Nat, prefixes[i]?.getD [] = [] := by
  intro i
  cases hn : prefixes[i]? with
  | none => rfl
  | some names =>
    have hi : i < bindings.length := by
      have := (List.getElem?_eq_some_iff.mp hn).1
      rw [hp.length] at this
      rwa [hlen]
    have hh := (hp.member i bindings[i] names (List.getElem?_eq_getElem hi) hn).1
    rw [hz bindings[i] (List.getElem_mem hi)] at hh
    exact List.length_eq_zero_iff.mp hh

theorem core_openTyVars_nil (e : Expr) : e.openTyVars [] = e := by
  rw [← Expr.instTy_fvar_eq_openTyVars]
  exact Expr.instTy_nil e

private theorem rigidBindingVars_mem_iff {bindings : List InputRecBinding} :
    v ∈ rigidBindingVars bindings ↔ ∃ binding ∈ bindings,
      v ∈ binding.ann.rigidVars ∨ v ∈ binding.rhs.rigidVars := by
  induction bindings with
  | nil => simp only [rigidBindingVars, List.not_mem_nil, false_iff, not_exists,
      not_and, false_implies, implies_true]
  | cons head rest ih =>
      simp only [rigidBindingVars, List.mem_append, List.mem_cons, ih]
      constructor
      · rintro (h | ⟨binding, hr, hv⟩)
        · exact ⟨head, .inl rfl, h⟩
        · exact ⟨binding, .inr hr, hv⟩
      · rintro ⟨binding, rfl | hr, hv⟩
        · exact .inl hv
        · exact .inr ⟨binding, hr, hv⟩

private theorem input_branch_size {branches : List (MatchPattern × InferInput)}
    (h : (pat, body) ∈ branches) : body.sourceSize < sizeBranches branches := by
  induction branches with
  | nil => cases h
  | cons head rest ih =>
    rcases head with ⟨p, b⟩
    rcases List.mem_cons.mp h with heq | hm
    · cases heq
      simp only [sizeBranches]
      omega
    · have := ih hm
      simp only [sizeBranches]
      omega

private theorem input_binding_size {bindings : List InputRecBinding}
    (h : binding ∈ bindings) : binding.rhs.sourceSize < sizeBindings bindings := by
  induction bindings with
  | nil => cases h
  | cons head rest ih =>
    rcases List.mem_cons.mp h with rfl | hm
    · simp only [sizeBindings]
      omega
    · have := ih hm
      simp only [sizeBindings]
      omega

/-- Conservative completed syntax is derivable using structural source rules.
This proof never uses the completed-subtree source constructor. -/
theorem ScopedTyping.ofComplete {input : InferInput} {K : List Nat} {ctx : Ctx}
    {core : Expr} {ty : Ty} (hemb : input.toCore = some core)
    (hscope : ∀ v ∈ core.tyFreeVars, v ∈ K) (ht : TypeOfHM ctx core ty) :
    ScopedTyping K ctx input ty := by
  cases hinput : input <;> simp only [hinput] at hemb
  case primLit p =>
    cases hemb
    exact .primLit (by simpa only [Expr.erase] using ht.erase_preserves_typing)
  case primBinOp op =>
    cases hemb
    exact .primBinOp (by simpa only [Expr.erase] using ht.erase_preserves_typing)
  case var i =>
    cases hemb
    cases ht with
    | var hlook hlc hinst => exact .var hlook hlc hinst
  case ctor name =>
    cases hemb
    cases ht with
    | ctor hlook hlc hinst => exact .ctor hlook hlc hinst
  case lambda ann body =>
    simp only [Expr.toCore, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at hemb
    obtain ⟨ann', ha, body', hb, rfl⟩ := hemb
    cases ht with
    | lambda hlc hp hctx ht =>
      subst hctx
      refine .lambda hlc ?_ ?_ (ScopedTyping.ofComplete hb ?_ ht)
      · intro t heq
        subst ann
        simp only [completeLambdaAnn, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at ha
        obtain ⟨a, hta, rfl⟩ := ha
        rw [hp a rfl]
        exact PartialCore.Template.toCore_fits hta
      · intro t heq v hv
        subst ann
        simp only [completeLambdaAnn, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at ha
        obtain ⟨a, hta, rfl⟩ := ha
        exact hscope v (List.mem_append_left _ ((PartialCore.Template.source_toCore_rigidVars hta v).mp hv))
      · intro v hv; exact hscope v (List.mem_append_right _ hv)
  case app f arg =>
    simp only [Expr.toCore, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at hemb
    obtain ⟨f', hf, arg', hx, rfl⟩ := hemb
    cases ht with
    | app htf htx =>
      exact .app (ScopedTyping.ofComplete hf (fun v hv => hscope v (List.mem_append_left _ hv)) htf)
        (ScopedTyping.ofComplete hx (fun v hv => hscope v (List.mem_append_right _ hv)) htx)
  case letIn ann rhs body =>
    simp only [Expr.toCore, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at hemb
    obtain ⟨ann', ha, rhs', hr, body', hb, rfl⟩ := hemb
    have hview := ann.annotationView_toCore ha
    cases ann' with
    | none =>
      cases ht with
      | @letIn _ _ _ _ _ _ M L hwf _ hcofin heq hbody =>
        subst heq
        refine .letIn (M := M) (L := L) hwf (by intro t ht; simp [hview, PartialCore.Ann.ofCore] at ht)
          (by simpa only [Option.MonoMatches, hview, PartialCore.Ann.ofCore] using PartialCore.Ann.MonoMatches.absent hwf) ?_ (ScopedTyping.ofComplete hb ?_ hbody)
        · intro Xs hf
          exact ScopedTyping.ofComplete hr
            (fun v hv => hscope v (List.mem_append_left _ hv)) (hcofin Xs hf)
        · intro v hv; exact hscope v (List.mem_append_right _ hv)
    | some scheme =>
      cases ht with
      | @letIn _ _ _ _ _ _ M L hwf hpin hgen hctx hbody =>
        subst hctx
        have hM : M = scheme := hpin scheme rfl
        subst M
        have hrhsScope : ∀ v ∈ rhs'.tyFreeVars, v ∈ K := fun v hv =>
          hscope v (List.mem_append_left _ (List.mem_append_right _ hv))
        refine .letSignature (M := scheme) (L := L) hwf ?_ ?_
          (by simpa only [Option.SignatureMatches, hview, PartialCore.Ann.ofCore] using PartialCore.Ann.SignatureMatches.complete hwf) ?_ (ScopedTyping.ofComplete hb ?_ hbody)
        · intro v hv
          have hv' : v ∈ scheme.body.freeVars := by
            simpa only [← Option.mem_annotationView_rigidVars, hview,
              PartialCore.Ann.ofCore, PartialCore.Ann.rigidVars] using hv
          exact hscope v (List.mem_append_left _ (List.mem_append_left _ hv'))
        · intro v hv
          exact hrhsScope v ((Expr.source_toCore_rigidVars rhs hr v).mp hv)
        · intro Xs hf
          have hcount : ann.paramCount = scheme.paramCount := ann.paramCount_toCore ha
          simp only [hcount]
          have htake : Xs.take scheme.paramCount = Xs := List.take_of_length_le hf.length.le
          refine ScopedTyping.ofComplete (rhs.source_toCore_openTyVars hr (Xs.take scheme.paramCount)) ?_ ?_
          · intro v hv
            rcases Expr.tyFreeVars_openTyVars hv with hv | hv
            · exact List.mem_append_left _ (hrhsScope v hv)
            · exact List.mem_append_right _ hv
          · simpa only [htake, Expr.openBoundTyVars] using hgen Xs hf
        · intro v hv; exact hscope v (List.mem_append_right _ hv)
  case match_ scrut branches =>
    simp only [Expr.toCore, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at hemb
    obtain ⟨scrut', hs, branches', hbs, rfl⟩ := hemb
    cases ht with
    | match_ hscrut hne hbranches =>
      refine .match_ (ScopedTyping.ofComplete hs
        (fun v hv => hscope v (List.mem_append_left _ hv)) hscrut) ?_ ?_
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
        have hsz := input_branch_size hb
        cases hbranch with
        | mk hspec hctx hbody =>
          subst hctx
          exact .named hspec (ScopedTyping.ofComplete heq hcoreScope hbody)
        | wildcard hbody => exact .wildcard (ScopedTyping.ofComplete heq hcoreScope hbody)

  case letRec bindings body =>
    have rawScope : ∀ v ∈ (Expr.letRec bindings body).rigidVars, v ∈ K :=
      fun v hv => hscope v ((Expr.source_toCore_rigidVars _ hemb v).mp hv)
    have hRows : ∀ binding ∈ bindings,
        ∀ v ∈ binding.ann.rigidVars ++ binding.rhs.rigidVars, v ∈ K := by
      intro binding hb v hv
      exact rawScope v (List.mem_append_left _
        (rigidBindingVars_mem_iff.mpr ⟨binding, hb, (List.mem_append.mp hv)⟩))
    simp only [Expr.toCore, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at hemb
    obtain ⟨coreBindings, hr, coreBody, hb, rfl⟩ := hemb
    obtain ⟨hErased, hBindingData⟩ := completeBindings_data hr
    cases ht with
    | letRec hg hw hMonoCore hPolyCore hctx hbody =>
      expose_names
      subst hctx
      have hCoreAnns : coreBindings.map RecBinding.ann =
          (bindings.map InputRecBinding.recMode).map RecBinding.ann := by
        have hh := congrArg (List.map RecBinding.ann) hErased
        simpa only [List.map_map, Function.comp_def, eraseRecRhs,
          InputRecBinding.recMode] using hh
      have hw0 : RecSpecs.WF (bindings.map InputRecBinding.recMode) specs G :=
        ⟨hw.anns_eq.trans hCoreAnns, hw.nodup, hw.mono_lc, hw.poly_wf⟩
      let prefixes0 : List (List Nat) := List.replicate specs.length []
      have hp0Nil : ∀ i : Nat, prefixes0[i]?.getD [] = [] := by
        intro i
        simp only [prefixes0, List.getElem?_replicate]
        split <;> rfl
      have hp0 : RecPrefixesWF bindings specs prefixes0 G := by
        refine ⟨List.length_replicate, ?_⟩
        intro i binding names hbi hni
        have hh := hp0Nil i
        rw [hni] at hh
        simp only [Option.getD_some] at hh
        subst names
        exact ⟨(hBindingData binding (List.mem_of_getElem? hbi)).2.symm, .nil, by simp⟩
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
      have bindingsNil : substInputBindings [] bindings = bindings :=
        substInputBindings_eq_self_of_fixes bindings (fun _ _ => rfl)
      have hw' : RecSpecs.WF (bindings.map InputRecBinding.recMode) specs' W := by
        simpa only [bindingsNil] using RecSpecs.WF.subst_fresh_pool (S := []) hw0 (by simp) hWnd
      have hp' : RecPrefixesWF bindings specs' prefixes' W := by
        simpa only [bindingsNil] using hp0.subst_fresh_pool (S := []) hWlen hWnd
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
      have hpData := fun i hi => hp0.get (by simpa only [List.length_map] using hw0.length)
        (i := i) hi
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
      have annMonoAbsent : ∀ (member : Nat) (binding : InputRecBinding) (ty : Ty),
          bindings[member]? = some binding → specs[member]? = some (.mono ty) →
          binding.ann.annotationView = .absent := by
        intro member binding ty hbi hti
        have heq := congrArg (fun xs => xs[member]?) hw0.anns_eq
        simp only [List.getElem?_map, hti, hbi, Option.map_some, RecSpec.ann,
          InputRecBinding.recMode, Option.some.injEq] at heq
        have hvalid := (hBindingData binding (List.mem_of_getElem? hbi)).1
        have hview := binding.ann.annotationView_toCore hvalid
        have hnone : binding.ann.recModeAnn = none := heq.symm
        simpa only [hnone, PartialCore.Ann.ofCore] using hview
      refine ScopedTyping.letRec (specs := specs') (groups := groups) (prefixes := prefixes')
        (G := W) (L := L') (hErased ▸ validResidualGroups_erase_iff.mpr hg)
        hw' hp' ?_ hRows ?_ ?_ ?_ ?_
      · intro w hw hm
        exact hWavoid w hw (by simp only [avoid, List.mem_append] at hm ⊢; tauto)
      · intro member binding names ty hbi hni hti
        have hlc := hw'.mono_lc ty (List.mem_of_getElem? hti)
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
          simp only [Option.RecMatches, annMonoAbsent member binding ty0 hbi ht0]
          exact ⟨rfl, rfl, ⟨.absent (Ty.closeOver_preserves_bvars hlc)⟩⟩
      · intro stage component hs Xs hf member hm binding names ty hbi hni hti
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
          obtain ⟨coreBinding, hc, _, hemb⟩ := completeBindings_lookup hr hbi
          have hcTyping := hMonoCore stage component hs Xs (oldFresh Xs hf)
            member hm coreBinding ty0 hc ht0
          have ho := binding.rhs.source_toCore_openTyVars hemb []
          rw [core_openTyVars_nil] at ho
          change ScopedTyping (K ++ Xs) (recStageCtx ctx specs' prefixes' (groups.take stage).flatten W Xs)
            (binding.rhs.openSourceTyVars []) (Ty.renameG W Xs (Ty.renameG G W ty0))
          have hsquare := Ty.renameG_subst_fresh_pool (S := []) (hw.mono_lc ty0 (List.mem_of_getElem? ht0)) (by simp)
            hWlen hw.nodup hWnd hGW (hWmono ty0 (List.mem_of_getElem? ht0)) (by simp) (by simp)
            (hf.length.trans hWlen) (hGXs Xs hf) (hWXs Xs hf) (by simp)
          simp only [Subst.onTy_nil] at hsquare
          rw [hstageCtx Xs hf, hsquare]
          have hsz := input_binding_size (List.mem_of_getElem? hbi)
          refine ScopedTyping.ofComplete ho ?_ hcTyping
          intro v hv
          exact List.mem_append_left _ (hRows binding (List.mem_of_getElem? hbi) v
            (List.mem_append_right _ ((Expr.source_toCore_rigidVars _ hemb v).mpr hv)))
      · intro member binding scheme hbi hsi Ys hy
        rw [List.getElem?_map] at hsi
        obtain ⟨spec, hs0, heq⟩ := Option.map_eq_some_iff.mp hsi
        cases spec with
        | mono ty => cases heq
        | poly scheme0 =>
          cases heq
          obtain ⟨coreBinding, hc, _, hemb⟩ := completeBindings_lookup hr hbi
          have hy0 : FreshNames L scheme0.paramCount Ys :=
            ⟨hy.length, hy.nodup, fun y hy' hl => hy.avoid y hy' (by simp only [L', List.mem_append]; tauto)⟩
          have hcTyping := hPolyCore (coreBinding, .poly scheme0)
            (List.mem_iff_getElem?.mpr ⟨member, List.getElem?_zip_eq_some.mpr ⟨hc, hs0⟩⟩) scheme0 rfl Ys hy0
          rw [hbodyCtx]
          have hsz := input_binding_size (List.mem_of_getElem? hbi)
          refine ScopedTyping.ofComplete (binding.rhs.source_toCore_openTyVars hemb Ys) ?_ hcTyping
          intro v hv
          rcases Expr.tyFreeVars_openTyVars hv with hv | hv
          · exact List.mem_append_left _ (hRows binding (List.mem_of_getElem? hbi) v
              (List.mem_append_right _ ((Expr.source_toCore_rigidVars _ hemb v).mpr hv)))
          · exact List.mem_append_right _ hv
      · rw [hbodyCtx]
        refine ScopedTyping.ofComplete hb ?_ hbody
        intro v hv
        exact rawScope v (List.mem_append_right _ ((Expr.source_toCore_rigidVars _ hb v).mpr hv))
termination_by input.sourceSize
decreasing_by
  all_goals simp only [hinput, Expr.sourceSize, Expr.openSourceTyVars, Expr.source_size_openTyVarsFrom] at *
  all_goals omega

#print axioms ScopedTyping.ofComplete

/-- The independent rules conservatively recover ordinary typing whenever the
input is already complete. This retains complete annotations and recursion. -/
theorem ScopedTyping.toCore (h : ScopedTyping K ctx input ty) {core : Expr}
    (hc : input.toCore = some core) :
    TypeOfHM ctx core ty ∧ (∀ v ∈ core.tyFreeVars, v ∈ K) := by
  induction h using ScopedTyping.rec
      (motive_2 := fun K ctx branch scrutTy resultTy _ =>
        ∀ {body : Expr}, branch.2.toCore = some body →
          TypeOfMatchBranch ctx (branch.1, body) scrutTy resultTy ∧
            (∀ v ∈ body.tyFreeVars, v ∈ K)) generalizing core with

  | primLit ht => cases hc; exact ⟨complete_primLit_of_runtime ht, by simp [Expr.tyFreeVars]⟩
  | primBinOp ht => cases hc; exact ⟨complete_primBinOp_of_runtime ht, by simp [Expr.tyFreeVars]⟩
  | @lambda ann _ _ body _ param hlc hfits hrigid _ ih =>
    simp only [Expr.toCore, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at hc
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
        exact hrigid template rfl v ((PartialCore.Template.source_toCore_rigidVars ht v).mpr hv)
    · exact hs v hv
  | app _ _ ihf ihx =>
    simp only [Expr.toCore, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at hc
    obtain ⟨f, hf, x, hx, rfl⟩ := hc
    obtain ⟨htf, hsf⟩ := ihf hf
    obtain ⟨htx, hsx⟩ := ihx hx
    exact ⟨.app htf htx, fun v hv => (List.mem_append.mp hv).elim (hsf v) (hsx v)⟩
  | @letIn ann _ _ rhs body _ M L hwf _ hfits _ _ ihr ihb =>
    simp only [Expr.toCore, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at hc
    obtain ⟨ann', ha, rhs', hr, body', hb, rfl⟩ := hc
    obtain ⟨Xs, hlen, hnd, hav⟩ := exists_fresh_names L M.paramCount
    have hXs : FreshNames L M.paramCount Xs := ⟨hlen, hnd, hav⟩
    have hfit := hfits.open Xs hXs.length.ge
    have hview := ann.annotationView_toCore ha
    cases ann' with
    | some scheme =>
      have hmode := hfits.isSignature
      simp [hview, PartialCore.Ann.ofCore, PartialCore.Ann.isSignature] at hmode
    | none =>
      obtain ⟨htb, hsb⟩ := ihb hb
      refine ⟨.letIn hwf (by intro a h; cases h) (fun Ys hYs => (ihr Ys hYs hr).1) rfl htb, ?_⟩
      intro v hv
      rcases List.mem_append.mp hv with hv | hv
      · exact (ihr Xs hXs hr).2 v hv
      · exact hsb v hv
  | @letSignature K ctx body bodyTy ann rhs M L hwf hann hrhs hfits _ _ ihr ihb =>
    simp only [Expr.toCore, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at hc
    obtain ⟨ann', ha, rhs', hr, body', hb, rfl⟩ := hc
    obtain ⟨Xs, hlen, hnd, hav⟩ := exists_fresh_names L M.paramCount
    have hXs : FreshNames L M.paramCount Xs := ⟨hlen, hnd, hav⟩
    have hfit := hfits.open Xs hXs.length.ge
    have hview := ann.annotationView_toCore ha
    cases ann' with
    | none =>
      have hmode := hfits.isSignature
      simp [hview, PartialCore.Ann.ofCore, PartialCore.Ann.isSignature] at hmode
    | some scheme =>
      have hcount : ann.paramCount = scheme.paramCount := ann.paramCount_toCore ha
      simp only [Option.SignatureFits, hview, PartialCore.Ann.ofCore] at hfit
      cases hfit
      obtain ⟨htb, hsb⟩ := ihb hb
      refine ⟨.letIn (L := L) hwf (fun _ heq => Option.some.inj heq) ?_ rfl htb, ?_⟩
      · intro fresh hf
        have htake : fresh.take M.paramCount = fresh := by
          exact List.take_of_length_le hf.length.le
        have hemb := rhs.source_toCore_openTyVars hr (fresh.take M.paramCount)
        have ht := (ihr fresh hf (by simpa only [hcount] using hemb)).1
        simpa only [hcount, htake, Expr.openBoundTyVars] using ht
      · intro v hv
        rcases List.mem_append.mp hv with hprefix | hv
        · rcases List.mem_append.mp hprefix with hv | hv
          · exact hann v ((Option.mem_annotationView_rigidVars ann v).mp
              (by simpa only [hview, PartialCore.Ann.ofCore, PartialCore.Ann.rigidVars] using hv))
          · exact hrhs v ((Expr.source_toCore_rigidVars rhs hr v).mpr hv)
        · exact hsb v hv
  | var hlook hlc hinst => cases hc; exact ⟨.var hlook hlc hinst, by simp [Expr.tyFreeVars]⟩
  | ctor hlook hlc hinst => cases hc; exact ⟨.ctor hlook hlc hinst, by simp [Expr.tyFreeVars]⟩

  | match_ _ hne _ ihs ihbranches =>
    simp only [Expr.toCore, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at hc
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
  | letRec hgroups hwf hp hG hRows hMatches hMono hPoly hBody ihMono ihPoly ihBody =>
    expose_names
    have hRaw := (ScopedTyping.letRec hgroups hwf hp hG hRows hMatches hMono hPoly hBody).rigidVars
    have hWhole := hc
    simp only [Expr.toCore, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at hc
    obtain ⟨coreBindings, hr, coreBody, hb, rfl⟩ := hc
    obtain ⟨hErased, hBindingData⟩ := completeBindings_data hr
    have hpNil := complete_prefixes_empty hp
      (by simpa only [List.length_map] using hwf.length)
      (fun binding hm => (hBindingData binding hm).2)
    have hCoreAnns : coreBindings.map RecBinding.ann =
        (bindings.map InputRecBinding.recMode).map RecBinding.ann := by
      have := congrArg (List.map RecBinding.ann) hErased
      simpa only [List.map_map, Function.comp_def, eraseRecRhs,
        InputRecBinding.recMode] using this
    have hbodyCtx : recBodyCtx ctx_1 specs prefixes G = RecSpecs.bodyCtx ctx_1 specs G := by
      unfold recBodyCtx RecSpecs.bodyCtx
      rw [recCompleted_empty_prefixes specs prefixes G hpNil]
    refine ⟨TypeOfHM.letRec (groups := groups) (G := G) (L := G ++ L)
      (validResidualGroups_erase_iff.mp (hErased ▸ hgroups))
      ⟨hwf.anns_eq.trans hCoreAnns.symm, hwf.nodup, hwf.mono_lc, hwf.poly_wf⟩
      ?_ ?_ rfl ?_, ?_⟩
    · intro stage component hs Xs hf member hm coreBinding ty hcore ht
      obtain ⟨binding, hr0, _, hemb⟩ := completeBindings_lookup_back hr hcore
      have hi : member < specs.length := (List.getElem?_eq_some_iff.mp ht).1
      have hip : member < prefixes.length := by rw [hp.length]; exact hi
      have hn : prefixes[member]? = some [] := by
        have hh := hpNil member
        rw [List.getElem?_eq_getElem hip] at hh
        rw [List.getElem?_eq_getElem hip]
        simpa only [Option.getD_some] using congrArg some hh
      have ho := binding.rhs.source_toCore_openTyVars hemb []
      rw [core_openTyVars_nil] at ho
      have hh := (ihMono stage component hs Xs hf member hm binding [] ty
        hr0 hn ht ho).1
      simpa only [recRenameNames, List.map_nil, recStage_empty_prefixes _ _ _ _ _ _ hpNil] using hh
    · intro pair hpair scheme heq Ys hy
      obtain ⟨member, hzip⟩ := List.mem_iff_getElem?.mp hpair
      obtain ⟨hcore, ht⟩ := List.getElem?_zip_eq_some.mp hzip
      rw [heq] at ht
      obtain ⟨binding, hr0, _, hemb⟩ := completeBindings_lookup_back hr hcore
      have hy0 : FreshNames L scheme.paramCount Ys :=
        ⟨hy.length, hy.nodup, fun y hy' hl => hy.avoid y hy' (List.mem_append_right _ hl)⟩
      have hh := (ihPoly member binding scheme hr0 ht Ys hy0
        (binding.rhs.source_toCore_openTyVars hemb Ys)).1
      simpa only [hbodyCtx] using hh
    · simpa only [hbodyCtx] using (ihBody hb).1
    · intro v hv
      exact hRaw v ((Expr.source_toCore_rigidVars _ hWhole v).mpr hv)
  | named hspec _ ih =>
    rename_i body heq
    obtain ⟨ht, hs⟩ := ih heq
    exact ⟨.mk hspec rfl ht, hs⟩
  | wildcard _ ih =>
    rename_i body heq
    obtain ⟨ht, hs⟩ := ih heq
    exact ⟨.wildcard ht, hs⟩
