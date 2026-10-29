import FHM.InferInput

/-! Declarative typing for partial Core source. Scope bookkeeping for the
inference implementation lives in `ScopedTyping`, a conservative refinement
of this judgment. Neither type holes nor fresh scheme openings require an
algorithmic protection set in the source judgment. -/

namespace SourceRec

/-- Check each residual component monomorphically, with earlier components
already generalized. Annotation matching is deliberately a separate premise. -/
def MonoTyped (J : Ctx → InferInput → Ty → Prop) (ctx : Ctx)
    (bindings : List InputRecBinding) (specs : List RecSpec)
    (groups prefixes : List (List Nat)) (G L : List Nat) : Prop :=
  ∀ (stage : Nat) (component : List Nat), groups[stage]? = some component →
    ∀ Xs, FreshNames (G ++ L) G.length Xs →
    ∀ member ∈ component,
      ∀ (binding : InputRecBinding) (names : List Nat) (ty : Ty),
      bindings[member]? = some binding →
      prefixes[member]? = some names →
      specs[member]? = some (.mono ty) →
      J (recStageCtx ctx specs prefixes (groups.take stage).flatten G Xs)
        (binding.rhs.openSourceTyVars (recRenameNames G Xs names)) (Ty.renameG G Xs ty)

/-- Signed recursive RHSs are checked under the final scheme environment. -/
def PolyTyped (J : Ctx → InferInput → Ty → Prop) (ctx : Ctx)
    (bindings : List InputRecBinding) (specs : List RecSpec)
    (prefixes : List (List Nat)) (G L : List Nat) : Prop :=
  ∀ (member : Nat) (binding : InputRecBinding) (scheme : PolyTy),
    bindings[member]? = some binding →
    specs[member]? = some (.poly scheme) →
    ∀ Ys, FreshNames L scheme.paramCount Ys →
      J (recBodyCtx ctx specs prefixes G)
        (binding.rhs.openSourceTyVars Ys) (scheme.openVars Ys)

end SourceRec

inductive BranchTyping (J : Ctx → InferInput → Ty → Prop) :
    Ctx → (MatchPattern × InferInput) → Ty → Ty → Prop
  | named :
    BranchCtorSpec ctx.ctors name count scrutTy ctor args fields →
    J { ctx with env := fields.map PolyTy.mkTrivial ++ ctx.env } body resultTy →
    BranchTyping J ctx (.named name count, body) scrutTy resultTy

  | wildcard :
    J ctx body resultTy →
    BranchTyping J ctx (.wildcard, body) scrutTy resultTy

/-- The main source judgment. One closed annotation completion is selected
before the cofinite RHS premises, including for partial written signatures.
Fresh names in those premises are ordinary abstract type parameters. -/
inductive InputTyping : Ctx → InferInput → Ty → Prop
  | primLitUnit :
    InputTyping ctx (.primLit .unit) (.prim .unit)

  | primLitInt :
    InputTyping ctx (.primLit (.int n)) (.prim .int)

  | primLitNat :
    InputTyping ctx (.primLit (.nat n)) (.prim .nat)

  | primLitChar :
    InputTyping ctx (.primLit (.char c)) (.prim .char)

  | primBinOpIntAdd :
    InputTyping ctx (.primBinOp .intAdd)
      (.arrow (.prim .int) (.arrow (.prim .int) (.prim .int)))

  | primBinOpIntSub :
    InputTyping ctx (.primBinOp .intSub)
      (.arrow (.prim .int) (.arrow (.prim .int) (.prim .int)))

  | primBinOpIntLt :
    InputTyping ctx (.ctor ⟨"True"⟩) (.customTy ⟨"Bool"⟩ []) →
    InputTyping ctx (.ctor ⟨"False"⟩) (.customTy ⟨"Bool"⟩ []) →
    InputTyping ctx (.primBinOp .intLt)
      (.arrow (.prim .int) (.arrow (.prim .int) (.customTy ⟨"Bool"⟩ [])))

  | primBinOpCharLt :
    InputTyping ctx (.ctor ⟨"True"⟩) (.customTy ⟨"Bool"⟩ []) →
    InputTyping ctx (.ctor ⟨"False"⟩) (.customTy ⟨"Bool"⟩ []) →
    InputTyping ctx (.primBinOp .charLt)
      (.arrow (.prim .char) (.arrow (.prim .char) (.customTy ⟨"Bool"⟩ [])))

  | lambda :
    paramTy.IsLC →
    (∀ template, ann = some template → template.Matches paramTy) →
    InputTyping { ctx with env := PolyTy.mkTrivial paramTy :: ctx.env } body bodyTy →
    InputTyping ctx (.lambda ann body) (.arrow paramTy bodyTy)

  | app :
    InputTyping ctx f (.arrow argTy retTy) →
    InputTyping ctx arg argTy →
    InputTyping ctx (.app f arg) retTy

  | letIn {ctx : Ctx} {rhs body : InferInput} {bodyTy : Ty}
      {ann : BindingAnn} {M : PolyTy} {L : List Nat} :
    M.WF →
    ann.MonoMatches M →
    (∀ Xs, FreshNames L M.paramCount Xs → InputTyping ctx rhs (M.openVars Xs)) →
    InputTyping { ctx with env := M :: ctx.env } body bodyTy →
    InputTyping ctx (.letIn ann rhs body) bodyTy

  | letSignature {ctx : Ctx} {body : InferInput} {bodyTy : Ty}
      {ann : BindingAnn} {rhs : InferInput} {M : PolyTy} {L : List Nat} :
    M.WF →
    ann.SignatureMatches M →
    (∀ Xs, FreshNames L M.paramCount Xs →
      InputTyping ctx (rhs.openSourceTyVars (Xs.take ann.paramCount)) (M.openVars Xs)) →
    InputTyping { ctx with env := M :: ctx.env } body bodyTy →
    InputTyping ctx (.letIn ann rhs body) bodyTy

  | var :
    ctx.env[index]? = some scheme →
    (∀ arg ∈ args, arg.IsLC) →
    scheme.InstantiatesTo args ty →
    InputTyping ctx (.var index) ty

  | ctor :
    LookupList.get? ctx.ctors name = some ctor →
    (∀ arg ∈ args, arg.IsLC) →
    ctor.toTy.InstantiatesTo args ty →
    InputTyping ctx (.ctor name) ty

  | match_ :
    InputTyping ctx scrut scrutTy →
    branches ≠ [] →
    (∀ branch ∈ branches, BranchTyping InputTyping ctx branch scrutTy resultTy) →
    InputTyping ctx (.match_ scrut branches) resultTy

  | letRec {specs : List RecSpec} {groups : List (List Nat)}
      {prefixes : List (List Nat)} {G L : List Nat} :
    RecGroups.ValidResidualGroups (bindings.map InputRecBinding.recMode) groups →
    RecSpecs.WF (bindings.map InputRecBinding.recMode) specs G →
    RecPrefixesWF bindings specs prefixes G →
    (∀ name ∈ G, name ∉ ctx.env.freeVars ++ (Expr.letRec bindings body).rigidVars) →
    RecAnnotationsMatch bindings specs prefixes G →
    SourceRec.MonoTyped InputTyping ctx bindings specs groups prefixes G L →
    SourceRec.PolyTyped InputTyping ctx bindings specs prefixes G L →
    InputTyping (recBodyCtx ctx specs prefixes G) body resultTy →
    InputTyping ctx (.letRec bindings body) resultTy

private theorem source_ctor (h : TypeOfHM ctx (.ctor name) ty) :
    InputTyping ctx (.ctor name) ty := by
  cases h with
  | ctor hl ha hi => exact .ctor hl ha hi

/-- Forget the inference scope refinement. This proof follows the source
derivation; no completed annotated expression is involved. -/
theorem ScopedTyping.source (h : ScopedTyping K ctx input ty) : InputTyping ctx input ty := by
  induction h using ScopedTyping.rec
      (motive_2 := fun _ ctx branch st rt _ => BranchTyping InputTyping ctx branch st rt) with
  | primLit h => cases h <;> constructor
  | primBinOp h =>
    cases h with
    | primBinOpIntAdd => exact .primBinOpIntAdd
    | primBinOpIntSub => exact .primBinOpIntSub
    | primBinOpIntLt ht hf => exact .primBinOpIntLt (source_ctor ht) (source_ctor hf)
    | primBinOpCharLt ht hf => exact .primBinOpCharLt (source_ctor ht) (source_ctor hf)
  | lambda hl hf _ _ ih => exact .lambda hl hf ih
  | app _ _ ihf ihx => exact .app ihf ihx
  | letIn hw _ hm _ _ ihr ihb => exact .letIn hw hm ihr ihb
  | letSignature hw _ _ hm _ _ ihr ihb => exact .letSignature hw hm ihr ihb
  | var hl ha hi => exact .var hl ha hi
  | ctor hl ha hi => exact .ctor hl ha hi
  | match_ _ hn _ ihs ihb => exact .match_ ihs hn ihb
  | letRec hg hw hp hf hr hm hmono hpoly hb ihm ihp ihb =>
    refine .letRec hg hw hp ?_ hm ihm ihp ihb
    intro n hn hv
    apply hf n hn
    rcases List.mem_append.mp hv with hv | hv
    · exact List.mem_append_left _ hv
    · exact List.mem_append_right _ ((ScopedTyping.letRec hg hw hp hf hr hm hmono hpoly hb).rigidVars n hv)
  | named hs _ ih => exact .named hs ih
  | wildcard _ ih => exact .wildcard ih

private theorem binding_scope {bindings : List InputRecBinding} {binding : InputRecBinding}
    (hb : binding ∈ bindings) :
    ∀ v ∈ binding.ann.rigidVars ++ binding.rhs.rigidVars, v ∈ rigidBindingVars bindings := by
  induction bindings with
  | nil => cases hb
  | cons b bs ih =>
    rcases List.mem_cons.mp hb with rfl | hb
    · intro v hv
      exact List.mem_append_left _ hv
    · intro v hv
      exact List.mem_append_right _ (ih hb v hv)

/-- A source derivation can be refined with precisely its authored free
variables. Extra protected names are irrelevant to declarative acceptance. -/
theorem InputTyping.scoped (h : InputTyping ctx input ty) :
    ScopedTyping input.rigidVars ctx input ty := by
  induction h using InputTyping.rec
      (motive_2 := fun ctx branch st rt _ =>
        ScopedBranchTyping ScopedTyping branch.2.rigidVars ctx branch st rt) with
  | primLitUnit => exact .primLit .primLitUnit
  | primLitInt => exact .primLit .primLitInt
  | primLitNat => exact .primLit .primLitNat
  | primLitChar => exact .primLit .primLitChar
  | primBinOpIntAdd => exact .primBinOp .primBinOpIntAdd
  | primBinOpIntSub => exact .primBinOp .primBinOpIntSub
  | primBinOpIntLt _ _ iht ihf =>
    cases iht with | ctor ht hat it =>
      cases ihf with | ctor hf af iff =>
        exact .primBinOp (.primBinOpIntLt (.ctor ht hat it) (.ctor hf af iff))
  | primBinOpCharLt _ _ iht ihf =>
    cases iht with | ctor ht hat it =>
      cases ihf with | ctor hf af iff =>
        exact .primBinOp (.primBinOpCharLt (.ctor ht hat it) (.ctor hf af iff))
  | @lambda ann ctx body bt param hl hf _ ih =>
    refine .lambda hl hf ?_ (ih.scope_restrict (fun v hv => List.mem_append_right _ hv))
    intro t he v hv
    subst ann
    exact List.mem_append_left _ hv
  | app _ _ ihf ihx =>
    exact .app (ihf.scope_restrict (fun v hv => List.mem_append_left _ hv))
      (ihx.scope_restrict (fun v hv => List.mem_append_right _ hv))
  | @letIn ctx rhs body bt ann M L hw hm _ _ ihr ihb =>
    refine .letIn (L := L) hw ?_ hm ?_ (ihb.scope_restrict (fun v hv => List.mem_append_right _ hv))
    · intro t he v hv
      have hv' : v ∈ ann.rigidVars := (Option.mem_annotationView_rigidVars ann v).mp
        (by simpa [he, PartialCore.Ann.rigidVars] using hv)
      exact List.mem_append_left _ (List.mem_append_left _ hv')
    · intro Xs hf
      exact (ihr Xs hf).scope_restrict (fun v hv => List.mem_append_left _ (List.mem_append_right _ hv))
  | @letSignature ctx body bt ann rhs M L hw hm _ _ ihr ihb =>
    have ha : ∀ v ∈ ann.rigidVars, v ∈ (Expr.letIn ann rhs body).rigidVars :=
      fun v hv => List.mem_append_left _ (List.mem_append_left _ hv)
    have hr : ∀ v ∈ rhs.rigidVars, v ∈ (Expr.letIn ann rhs body).rigidVars :=
      fun v hv => List.mem_append_left _ (List.mem_append_right _ hv)
    refine .letSignature (L := L) hw ha hr hm ?_
      (ihb.scope_restrict (fun v hv => List.mem_append_right _ hv))
    intro Xs hf
    exact (ihr Xs hf).scope_restrict (rhs.source_openTyVars_scope hr (Xs.take ann.paramCount))
  | var hl ha hi => exact .var hl ha hi
  | ctor hl ha hi => exact .ctor hl ha hi
  | match_ _ hn _ ihs ihb =>
    refine .match_ (ihs.scope_restrict (fun v hv => List.mem_append_left _ hv)) hn ?_
    intro b hb
    cases hi : ihb b hb with
    | named hs ht =>
      refine .named hs (ht.scope_restrict ?_)
      intro v hv
      exact List.mem_append_right _ (source_branch_mem hb hv)
    | wildcard ht =>
      refine .wildcard (ht.scope_restrict ?_)
      intro v hv
      exact List.mem_append_right _ (source_branch_mem hb hv)
  | @letRec bindings body ctx rt specs groups prefixes G L hg hw hp hf hm _ _ _ ihm ihp ihb =>
    have hr : ∀ b ∈ bindings, ∀ v ∈ b.ann.rigidVars ++ b.rhs.rigidVars,
        v ∈ (Expr.letRec bindings body).rigidVars :=
      fun b hb v hv => List.mem_append_left _ (binding_scope hb v hv)
    refine .letRec (L := L) hg hw hp hf hr hm ?_ ?_
      (ihb.scope_restrict (fun v hv => List.mem_append_right _ hv))
    · intro stage component hc Xs hx member hmem b names t hb hn ht
      exact (ihm stage component hc Xs hx member hmem b names t hb hn ht).scope_restrict
        (by
          intro v hv
          rcases List.mem_append.mp (b.rhs.source_openTyVars_scope
            (fun v hv => hr b (List.mem_of_getElem? hb) v (List.mem_append_right _ hv))
            (recRenameNames G Xs names) v hv) with hv | hv
          · exact List.mem_append_left _ hv
          · exact List.mem_append_right _ (recRenameNames_mem hx.length
              (by
                exact (hp.member member b names hb hn).2.2) v hv))
    · intro member b scheme hb hs Ys hy
      exact (ihp member b scheme hb hs Ys hy).scope_restrict
        (b.rhs.source_openTyVars_scope
          (fun v hv => hr b (List.mem_of_getElem? hb) v (List.mem_append_right _ hv)) Ys)
  | named hs _ ih => exact .named hs ih
  | wildcard _ ih => exact .wildcard ih
where
  source_branch_mem {branches : List (MatchPattern × InferInput)} {branch : MatchPattern × InferInput}
      (hb : branch ∈ branches) {v : Nat} (hv : v ∈ branch.2.rigidVars) : v ∈ rigidBranchVars branches := by
    induction branches with
    | nil => cases hb
    | cons b bs ih =>
      rcases List.mem_cons.mp hb with rfl | hb
      · exact List.mem_append_left _ hv
      · exact List.mem_append_right _ (ih hb)

theorem scopedTyping_iff (hscope : ∀ v ∈ input.rigidVars, v ∈ K) :
    ScopedTyping K ctx input ty ↔ InputTyping ctx input ty :=
  ⟨ScopedTyping.source, fun h => h.scoped.scope_restrict hscope⟩

/-- Runtime typing follows directly from partial source typing. -/
theorem InputTyping.erase (h : InputTyping ctx input ty) :
    RuntimeTyping.RunWT ctx input.erase ty := h.scoped.erase

theorem InputTyping.regular (h : InputTyping ctx input ty) : ty.IsLC := h.erase.regular

theorem InputTyping.lambda_inv (h : InputTyping ctx (.lambda ann body) ty) :
    ∃ param result, ty = .arrow param result ∧ param.IsLC ∧
      (∀ template, ann = some template → template.Matches param) ∧
      InputTyping { ctx with env := PolyTy.mkTrivial param :: ctx.env } body result := by
  cases h with
  | lambda hl hf hb => exact ⟨_, _, rfl, hl, hf, hb⟩

theorem InputTyping.rec_inv (h : InputTyping ctx (.letRec bindings body) resultTy) :
    ∃ (specs : List RecSpec) (groups prefixes : List (List Nat)) (G L : List Nat),
      RecGroups.ValidResidualGroups (bindings.map InputRecBinding.recMode) groups ∧
      RecSpecs.WF (bindings.map InputRecBinding.recMode) specs G ∧
      RecPrefixesWF bindings specs prefixes G ∧
      (∀ name ∈ G, name ∉ ctx.env.freeVars ++ (Expr.letRec bindings body).rigidVars) ∧
      RecAnnotationsMatch bindings specs prefixes G ∧
      SourceRec.MonoTyped InputTyping ctx bindings specs groups prefixes G L ∧
      SourceRec.PolyTyped InputTyping ctx bindings specs prefixes G L ∧
      InputTyping (recBodyCtx ctx specs prefixes G) body resultTy := by
  cases h with
  | letRec hg hw hp hf hm hmono hpoly hb => exact ⟨_, _, _, _, _, hg, hw, hp, hf, hm, hmono, hpoly, hb⟩

theorem InputTyping.template_completion
    (h : InputTyping ctx (.letIn ann rhs body) result)
    (hann : ann.annotationView = .template template) :
    ∃ (scheme : PolyTy) (avoid : List Nat)
      (completion : PartialCore.Completion scheme.paramCount template scheme.body),
      template.WellScoped 0 ∧
      (∀ Xs, FreshNames avoid scheme.paramCount Xs →
        PartialCore.Template.Fits (PartialCore.HoleAssignment.map (Ty.openVars Xs) completion.holes)
          template (scheme.openVars Xs)) ∧
      (∀ Xs, FreshNames avoid scheme.paramCount Xs → InputTyping ctx rhs (scheme.openVars Xs)) ∧
      InputTyping { ctx with env := scheme :: ctx.env } body result := by
  cases h with
  | @letIn _ _ _ _ _ M L hw hm hr hb =>
    obtain ⟨hc⟩ := hm.completion
    rw [hann] at hc
    cases hc with
    | template hs hc =>
      refine ⟨M, L, hc, hs, ?_, hr, hb⟩
      intro Xs hf
      simpa only [hs.open_lc Xs] using (hc.open Xs hf.length.ge).fits
  | letSignature _ hm _ _ =>
    have hs := hm.isSignature
    simp [hann, PartialCore.Ann.isSignature] at hs

/-- A closed completion is chosen once, outside every fresh scheme opening. -/
theorem InputTyping.partialSignature_completion
    (h : InputTyping ctx (.letIn ann rhs body) result)
    (hann : ann.annotationView = .partialForall count template) :
    ∃ (scheme : PolyTy) (avoid : List Nat)
      (completion : PartialCore.Completion scheme.paramCount template scheme.body),
      count ≤ scheme.paramCount ∧ template.WellScoped count ∧
      (∀ Xs, FreshNames avoid scheme.paramCount Xs →
        PartialCore.Template.Fits (PartialCore.HoleAssignment.map (Ty.openVars Xs) completion.holes)
          (template.map (Ty.openVars (Xs.take count))) (scheme.openVars Xs)) ∧
      (∀ Xs, FreshNames avoid scheme.paramCount Xs →
        InputTyping ctx (rhs.openSourceTyVars (Xs.take count)) (scheme.openVars Xs)) ∧
      InputTyping { ctx with env := scheme :: ctx.env } body result := by
  cases h with
  | letIn _ hm _ _ =>
    have hs := hm.isSignature
    simp [hann, PartialCore.Ann.isSignature] at hs
  | @letSignature _ _ _ _ _ M L hw hm hr hb =>
    obtain ⟨hc⟩ := hm.completion
    rw [hann] at hc
    cases hc with
    | partialForall hle hs hc =>
      refine ⟨M, L, hc, hle, hs, ?_, ?_, hb⟩
      · intro Xs hf
        rw [hs.open_prefix]
        exact (hc.open Xs hf.length.ge).fits
      · intro Xs hf
        simpa only [← Option.annotationView_paramCount ann, hann, PartialCore.Ann.paramCount] using hr Xs hf

/-- Source substitution transports the annotation-local hole witnesses too. -/
theorem InputTyping.onSubst_source (h : InputTyping ctx input ty) (subst : Subst)
    (hlc : ∀ p ∈ subst, p.2.IsLC) :
    InputTyping (subst.onCtx ctx) (input.substSourceTyFvars subst) (subst.onTy ty) :=
  (h.scoped.onSubst_source (K' := input.rigidVars.flatMap
    (fun v => (subst.onTy (.fvar v)).freeVars)) subst hlc
    (fun k hk _ hv => List.mem_flatMap.mpr ⟨k, hk, hv⟩)).source

theorem InputTyping.onSubst_fixes (h : InputTyping ctx input ty) (subst : Subst)
    (hlc : ∀ p ∈ subst, p.2.IsLC)
    (hfix : ∀ v ∈ input.rigidVars, subst.onTy (.fvar v) = .fvar v) :
    InputTyping (subst.onCtx ctx) input (subst.onTy ty) := by
  simpa only [input.source_substTyFvars_eq_self_of_fixes hfix] using h.onSubst_source subst hlc
