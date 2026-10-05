import FHM.Core

/-!
# Typing for fully erased runtime terms

`TypeOfHM` specifies which annotated source programs the checker accepts.
`RunWT` instead types machine terms after every annotation has disappeared.
Its recursive schemes are proof-only witnesses: they are not recoverable from,
and do not occur in, the `Expr` being evaluated.

The source rule first solves `.mono τ` members in the mixed initial context,
then generalizes them and checks signed members under the final schemes.  The
runtime rule records the resulting, simpler fact: every RHS and the body are
typed under those final schemes.  The runtime node itself stores only `none`
annotations.

Source typing erases into this judgment. Its substitution and preservation
theorems then show that evaluation keeps the source program's type, including
when annotated recursive members instantiate their own schemes differently.
-/

namespace RuntimeTyping

/-- Runtime group evidence has no source-annotation alignment premise: those
annotations have already erased. -/
structure RecSpecsWF (bindings : List Expr) (specs : List RecSpec)
    (G : List Nat) : Prop where
  length : bindings.length = specs.length
  nodup : G.Nodup
  mono_lc : ∀ τ, .mono τ ∈ specs → τ.IsLC
  poly_wf : ∀ σ, .poly σ ∈ specs → σ.WF

/-- Ordinary HM members share one opening of the group's generalisation pool,
but erased runtime evidence records their RHSs under the group's final scheme
environment.  This is the runtime form needed by unfolding: every recursively
wrapped member may subsequently be substituted at its exported scheme. -/
def MonoTyped (TypeOf : Ctx → Expr → Ty → Prop) (ctx : Ctx)
    (bindings : List Expr) (specs : List RecSpec) (G avoid : List Nat) : Prop :=
  ∀ Xs, FreshNames avoid G.length Xs →
    ∀ pair ∈ bindings.zip specs, ∀ τ, pair.2 = .mono τ →
      TypeOf (RecSpecs.bodyCtx ctx specs G) pair.1 (Ty.renameG G Xs τ)

/-- Complete annotations enable scheme-polymorphic recursive use.  Signed RHSs
are checked under the same final schemes as ordinary RHSs and the group body.
Runtime terms contain no type syntax, so only the expected type is opened at
the member's fresh rigid names. -/
def PolyTyped (TypeOf : Ctx → Expr → Ty → Prop) (ctx : Ctx)
    (bindings : List Expr) (specs : List RecSpec) (G avoid : List Nat) : Prop :=
  ∀ pair ∈ bindings.zip specs, ∀ σ, pair.2 = .poly σ →
    ∀ Ys, FreshNames avoid σ.paramCount Ys →
      TypeOf (RecSpecs.bodyCtx ctx specs G) pair.1 (σ.openVars Ys)

def GeneralisesTo (TypeOf : Ctx → Expr → Ty → Prop) (ctx : Ctx)
    (rhs : Expr) (scheme : PolyTy) (avoid : List Nat) : Prop :=
  ∀ Xs, FreshNames avoid scheme.paramCount Xs →
    TypeOf ctx rhs (scheme.openVars Xs)

mutual

/-- Typing for annotation-free machine terms. -/
inductive RunWT : Ctx → Expr → Ty → Prop
  | primLitUnit : RunWT ctx (.primLit .unit) (.prim .unit)
  | primLitInt : RunWT ctx (.primLit (.int n)) (.prim .int)
  | primLitNat : RunWT ctx (.primLit (.nat n)) (.prim .nat)
  | primLitChar : RunWT ctx (.primLit (.char c)) (.prim .char)
  | primBinOpIntAdd :
      RunWT ctx (.primBinOp .intAdd)
        (.arrow (.prim .int) (.arrow (.prim .int) (.prim .int)))
  | primBinOpIntSub :
      RunWT ctx (.primBinOp .intSub)
        (.arrow (.prim .int) (.arrow (.prim .int) (.prim .int)))
  | primBinOpIntLt :
      RunWT ctx (.ctor ⟨"True"⟩) (.customTy ⟨"Bool"⟩ []) →
      RunWT ctx (.ctor ⟨"False"⟩) (.customTy ⟨"Bool"⟩ []) →
      RunWT ctx (.primBinOp .intLt)
        (.arrow (.prim .int) (.arrow (.prim .int) (.customTy ⟨"Bool"⟩ [])))
  | primBinOpCharLt :
      RunWT ctx (.ctor ⟨"True"⟩) (.customTy ⟨"Bool"⟩ []) →
      RunWT ctx (.ctor ⟨"False"⟩) (.customTy ⟨"Bool"⟩ []) →
      RunWT ctx (.primBinOp .charLt)
        (.arrow (.prim .char) (.arrow (.prim .char) (.customTy ⟨"Bool"⟩ [])))
  | lambda :
      paramTy.IsLC →
      RunWT { ctx with env := PolyTy.mkTrivial paramTy :: ctx.env }
        body bodyTy →
      RunWT ctx (.lambda none body) (.arrow paramTy bodyTy)
  | app :
      RunWT ctx fn (.arrow argTy resultTy) →
      RunWT ctx arg argTy →
      RunWT ctx (.app fn arg) resultTy
  | letIn {scheme : PolyTy} {avoid : List Nat} :
      scheme.WF →
      GeneralisesTo RunWT ctx rhs scheme avoid →
      RunWT { ctx with env := scheme :: ctx.env } body resultTy →
      RunWT ctx (.letIn none rhs body) resultTy
  | var :
      ctx.env[index]? = some scheme →
      (∀ arg ∈ args, arg.IsLC) →
      scheme.InstantiatesTo args ty →
      RunWT ctx (.var index) ty
  | ctor :
      LookupList.get? ctx.ctors name = some ctor →
      (∀ arg ∈ args, arg.IsLC) →
      ctor.toTy.InstantiatesTo args ty →
      RunWT ctx (.ctor name) ty
  | match_ :
      RunWT ctx scrutinee scrutTy →
      branches ≠ [] →
      (∀ branch ∈ branches,
        RunWTMatchBranch ctx branch scrutTy resultTy) →
      RunWT ctx (.match_ scrutinee branches) resultTy
  | letRec {specs : List RecSpec} {G avoid : List Nat} :
      RecSpecsWF bindings specs G →
      MonoTyped RunWT ctx bindings specs G avoid →
      PolyTyped RunWT ctx bindings specs G avoid →
      RunWT (RecSpecs.bodyCtx ctx specs G) body resultTy →
      RunWT ctx (.letRec (bindings.map (fun _ => none)) bindings body) resultTy

/-- Match-branch typing for erased terms. -/
inductive RunWTMatchBranch :
    Ctx → (MatchPattern × Expr) → Ty → Ty → Prop
  | mk {ctor : Ctor} {ctx : Ctx} {c : CtorName} {n : Nat}
      {tyArgs instContents : List Ty} :
      BranchCtorSpec ctx.ctors c n scrutTy ctor tyArgs instContents →
      RunWT { ctx with env := instContents.map PolyTy.mkTrivial ++ ctx.env }
        body resultTy →
      RunWTMatchBranch ctx (.named c n, body) scrutTy resultTy
  | wildcard :
      RunWT ctx body resultTy →
      RunWTMatchBranch ctx (.wildcard, body) scrutTy resultTy

end

/-- Replacing one environment scheme by a more general scheme preserves erased
runtime typing.  Schemes are proof-only, so this changes no runtime term. -/
theorem RunWT.weaken_scheme {ctors : CtorEnv} {envPost env : Env}
    {scheme scheme' : PolyTy} {e : Expr} {ty : Ty}
    (hgen : scheme'.Generalizes scheme)
    (h : RunWT ⟨envPost ++ [scheme] ++ env, ctors⟩ e ty) :
    RunWT ⟨envPost ++ [scheme'] ++ env, ctors⟩ e ty := by
  have H : ∀ {ctx : Ctx} {e₀ : Expr} {ty₀ : Ty}, RunWT ctx e₀ ty₀ →
      ∀ ep : Env, ctx.env = ep ++ [scheme] ++ env →
        RunWT ⟨ep ++ [scheme'] ++ env, ctx.ctors⟩ e₀ ty₀ := by
    intro ctx e₀ ty₀ hd
    induction hd using RunWT.rec
      (motive_2 := fun ctx branch scrutTy resultTy _ =>
        ∀ ep : Env, ctx.env = ep ++ [scheme] ++ env →
          RunWTMatchBranch ⟨ep ++ [scheme'] ++ env, ctx.ctors⟩
            branch scrutTy resultTy) with
    | primLitUnit => intro _ _; exact .primLitUnit
    | primLitInt => intro _ _; exact .primLitInt
    | primLitNat => intro _ _; exact .primLitNat
    | primLitChar => intro _ _; exact .primLitChar
    | primBinOpIntAdd => intro _ _; exact .primBinOpIntAdd
    | primBinOpIntSub => intro _ _; exact .primBinOpIntSub
    | primBinOpIntLt _ _ ihtrue ihfalse =>
        intro ep heq
        exact .primBinOpIntLt (ihtrue ep heq) (ihfalse ep heq)
    | primBinOpCharLt _ _ ihtrue ihfalse =>
        intro ep heq
        exact .primBinOpCharLt (ihtrue ep heq) (ihfalse ep heq)
    | lambda hparam _ ihbody =>
        intro ep heq
        expose_names
        refine RunWT.lambda (paramTy := paramTy) hparam ?_
        have hb := ihbody (PolyTy.mkTrivial paramTy :: ep)
          (by simp only [heq, List.cons_append])
        simpa only [List.cons_append] using hb
    | app _ _ ihfn iharg =>
        intro ep heq
        exact .app (ihfn ep heq) (iharg ep heq)
    | letIn hwf _ _ ihgen ihbody =>
        intro ep heq
        expose_names
        refine .letIn hwf (fun Xs hXs => ihgen Xs hXs ep heq) ?_
        have hb := ihbody (scheme_1 :: ep)
          (by simp only [heq, List.cons_append])
        simpa only [List.cons_append] using hb
    | var hlook hlc hinst =>
        intro ep heq
        expose_names
        rw [heq] at hlook
        rcases lt_trichotomy index ep.length with hlt | heqi | hgt
        · refine .var ?_ hlc hinst
          rw [List.append_assoc, List.getElem?_append_left hlt]
          rwa [List.append_assoc, List.getElem?_append_left hlt] at hlook
        · subst heqi
          have hscheme : scheme_1 = scheme := by
            rw [List.append_assoc,
              List.getElem?_append_right (le_refl ep.length)] at hlook
            simpa only [Nat.sub_self, List.singleton_append,
              List.getElem?_cons_zero, Option.some.injEq] using hlook.symm
          subst hscheme
          obtain ⟨args', hlc', hinst'⟩ := hgen args ty_1 hlc hinst
          refine .var ?_ hlc' hinst'
          rw [List.append_assoc,
            List.getElem?_append_right (le_refl ep.length)]
          simp only [Nat.sub_self, List.singleton_append,
            List.getElem?_cons_zero]
        · refine .var ?_ hlc hinst
          have hle : ep.length ≤ index := by omega
          rw [List.append_assoc, List.getElem?_append_right hle] at hlook ⊢
          rw [show ([scheme] ++ env) = scheme :: env from rfl] at hlook
          rw [show ([scheme'] ++ env) = scheme' :: env from rfl]
          rw [show index - ep.length = (index - ep.length - 1) + 1 by omega]
            at hlook ⊢
          simpa only [List.getElem?_cons_succ] using hlook
    | ctor hlook hlc hinst => intro _ _; exact .ctor hlook hlc hinst
    | match_ _ hne _ ihscrut ihbranches =>
        intro ep heq
        refine .match_ (ihscrut ep heq) hne ?_
        intro branch hmem
        exact ihbranches branch hmem ep heq
    | letRec hwf hmono hpoly _ ihmono ihpoly ihbody =>
        intro ep heq
        expose_names
        refine .letRec (specs := specs) (G := G) (avoid := avoid) hwf ?_ ?_ ?_
        · intro Xs hXs pair hpair monoTy hmonoEq
          have ht := ihmono Xs hXs pair hpair monoTy hmonoEq
            (specs.map (RecSpec.bodyScheme G) ++ ep)
            (by simp only [RecSpecs.bodyCtx, heq, List.append_assoc])
          simpa only [RecSpecs.bodyCtx, List.append_assoc] using ht
        · intro pair hpair polyScheme hpolyEq Ys hYs
          have ht := ihpoly pair hpair polyScheme hpolyEq Ys hYs
            (specs.map (RecSpec.bodyScheme G) ++ ep)
            (by simp only [RecSpecs.bodyCtx, heq, List.append_assoc])
          simpa only [RecSpecs.bodyCtx, List.append_assoc] using ht
        · have hb := ihbody (specs.map (RecSpec.bodyScheme G) ++ ep)
            (by simp only [RecSpecs.bodyCtx, heq, List.append_assoc])
          simpa only [RecSpecs.bodyCtx, List.append_assoc] using hb
    | mk hspec _ ihbody =>
        expose_names
        refine RunWTMatchBranch.mk hspec ?_
        have hb := ihbody (instContents.map PolyTy.mkTrivial ++ ep)
          (by simp only [h_2, List.append_assoc])
        simpa only [List.append_assoc] using hb
    | wildcard _ ihbody =>
        expose_names
        exact .wildcard (ihbody ep h_2)
  exact H h envPost rfl

/-- Pointwise scheme generalisation preserves erased runtime typing. -/
theorem RunWT.weaken_schemes {ctors : CtorEnv} {env : Env}
    {schemes schemes' : List PolyTy} {e : Expr} {ty : Ty}
    (hgen : List.Forall₂ PolyTy.Generalizes schemes' schemes)
    (h : RunWT ⟨schemes ++ env, ctors⟩ e ty) :
    RunWT ⟨schemes' ++ env, ctors⟩ e ty := by
  have H : ∀ {old new : List PolyTy},
      List.Forall₂ PolyTy.Generalizes new old →
      ∀ pre : Env, RunWT ⟨pre ++ old ++ env, ctors⟩ e ty →
        RunWT ⟨pre ++ new ++ env, ctors⟩ e ty := by
    intro old new hs
    induction hs with
    | nil => intro pre ht; simpa using ht
    | @cons newHead oldHead newTail oldTail hhead _ ih =>
        intro pre ht
        have ht₁ : RunWT ⟨(pre ++ [oldHead]) ++ oldTail ++ env, ctors⟩ e ty := by
          simpa only [List.append_assoc, List.cons_append, List.nil_append,
            List.singleton_append] using ht
        have ht₂ := ih (pre ++ [oldHead]) ht₁
        have ht₃ := RunWT.weaken_scheme
          (envPost := pre) (env := newTail ++ env) hhead
          (by simpa only [List.append_assoc, List.singleton_append] using ht₂)
        simpa only [List.append_assoc, List.cons_append, List.nil_append,
          List.singleton_append] using ht₃
  have result := H hgen [] (by simpa using h)
  simpa using result

private theorem Ty.IsLC.substFvars_runtime {pairs : List (Nat × Ty)} {ty : Ty}
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

private theorem Ty.renameG_isLC_runtime {G Xs : List Nat} {ty : Ty}
    (hty : ty.IsLC) : (Ty.renameG G Xs ty).IsLC := by
  unfold Ty.renameG
  apply Ty.IsLC.substFvars_runtime
  · intro pair hpair
    obtain ⟨name, _, heq⟩ := List.mem_map.mp (List.of_mem_zip hpair).2
    rw [← heq]
    exact ContainsBvarsUpTo.fvar
  · exact hty

/-- Opening a type with enough arguments supplies an `InstantiatesBy`
derivation for the resulting type. -/
private theorem InstantiatesBy.openWith_runtime {args : List Ty} {body : Ty}
    (hbody : ContainsBvarsUpTo args.length body) :
    InstantiatesBy args body (Ty.openWith args body) := by
  induction body using Ty.rec_strong with
  | prim p => exact .prim
  | fvar n => exact .fvar
  | bvar i =>
      cases hbody with
      | bvar hi =>
          simp only [Ty.openWith, Ty.instantiate,
            List.getElem?_eq_getElem hi, Option.getD_some]
          exact .bvar (List.getElem?_eq_getElem hi)
  | arrow a b iha ihb =>
      cases hbody with
      | arrow ha hb => exact .arrow (iha ha) (ihb hb)
  | customTy name tys ih =>
      cases hbody with
      | customTy hall =>
          simp only [Ty.openWith, Ty.instantiate,
            TyList.instantiate_eq_map]
          apply InstantiatesBy.customTy
          induction tys with
          | nil => exact .nil
          | cons head tail ihtail =>
              exact .cons
                (ih head List.mem_cons_self (hall head List.mem_cons_self))
                (ihtail
                  (fun ty hty => ih ty (List.mem_cons_of_mem _ hty))
                  (fun ty hty => hall ty (List.mem_cons_of_mem _ hty)))

/-- Generalising a monotype over `G` is at least as general as its monomorphic
fresh opening `G ↦ Xs`. -/
private theorem PolyTy.genGroup_generalizes_renameG_runtime {G Xs : List Nat}
    {ty : Ty} (hty : ty.IsLC) (hG : G.Nodup)
    (hXsLen : Xs.length = G.length) (hXsNodup : Xs.Nodup)
    (hGXs : ∀ g ∈ G, g ∉ Xs) (hXsTy : ∀ x ∈ Xs, x ∉ ty.freeVars) :
    (PolyTy.genGroup G ty).Generalizes
      (PolyTy.mkTrivial (Ty.renameG G Xs ty)) := by
  rw [PolyTy.genGroup_renameG hty hXsLen hG hXsNodup hGXs hXsTy]
  intro args result hlc hinst
  have hopenedLC : (Ty.renameG G Xs ty).IsLC :=
    Ty.renameG_isLC_runtime hty
  have hresult : result = Ty.renameG G Xs ty := by
    have heq := InstantiatesBy.eq_openWith_range hinst hopenedLC
    simpa [PolyTy.mkTrivial, Ty.openWith_nil] using heq
  subst result
  let relevant := Ty.genFilter Xs (Ty.renameG G Xs ty)
  let witnesses := relevant.map (Ty.fvar ·)
  refine ⟨witnesses, ?_, ?_⟩
  · intro arg harg
    obtain ⟨name, _, rfl⟩ := List.mem_map.mp harg
    exact .fvar
  · have hbound : ContainsBvarsUpTo witnesses.length
        (Ty.closeOver relevant (Ty.renameG G Xs ty)) := by
      simpa [witnesses, relevant] using
        (Ty.closeOver_preserves_bvars hopenedLC (vars := relevant))
    have hopen := InstantiatesBy.openWith_runtime hbound
    have hroundtrip :
        Ty.openWith witnesses
            (Ty.closeOver relevant (Ty.renameG G Xs ty)) =
          Ty.renameG G Xs ty := by
      simpa [witnesses, relevant, Ty.openVars_eq_openWith] using
        (Ty.openVars_closeOver_self
          (gs := relevant) hopenedLC)
    simpa [PolyTy.genGroup, relevant, witnesses, hroundtrip] using hopen

/-- Final recursive schemes pointwise generalise the monomorphic RHS entries
at a suitably fresh shared opening. -/
private theorem bodySchemes_generalize_rhsEntries_runtime
    {specs : List RecSpec} {G Xs : List Nat}
    (hG : G.Nodup) (hXsLen : Xs.length = G.length)
    (hXsNodup : Xs.Nodup)
    (hmonoLC : ∀ ty, RecSpec.mono ty ∈ specs → ty.IsLC)
    (hGXs : ∀ g ∈ G, g ∉ Xs)
    (hXsMono : ∀ ty, RecSpec.mono ty ∈ specs →
      ∀ x ∈ Xs, x ∉ ty.freeVars) :
    List.Forall₂ PolyTy.Generalizes
      (specs.map (RecSpec.bodyScheme G))
      (specs.map (RecSpec.rhsEntry G Xs)) := by
  induction specs with
  | nil => exact .nil
  | cons spec rest ih =>
      apply List.Forall₂.cons
      · cases spec with
        | mono ty =>
            exact PolyTy.genGroup_generalizes_renameG_runtime
              (hmonoLC ty List.mem_cons_self) hG hXsLen hXsNodup hGXs
              (hXsMono ty List.mem_cons_self)
        | poly scheme => exact PolyTy.Generalizes.refl scheme
      · exact ih
          (fun ty hty => hmonoLC ty (List.mem_cons_of_mem _ hty))
          (fun ty hty => hXsMono ty (List.mem_cons_of_mem _ hty))

/-- Every intermediate residual environment can be widened to the final
schemes. Completed members already have their final scheme; pending members
use the same fresh-opening generalization as the original mixed rule. -/
private theorem bodySchemes_generalize_stageEntries_runtime
    {specs : List RecSpec} {G Xs done : List Nat}
    (hG : G.Nodup) (hXsLen : Xs.length = G.length)
    (hXsNodup : Xs.Nodup)
    (hmonoLC : ∀ ty, RecSpec.mono ty ∈ specs → ty.IsLC)
    (hGXs : ∀ g ∈ G, g ∉ Xs)
    (hXsMono : ∀ ty, RecSpec.mono ty ∈ specs →
      ∀ x ∈ Xs, x ∉ ty.freeVars) :
    List.Forall₂ PolyTy.Generalizes
      (specs.map (RecSpec.bodyScheme G))
      (specs.mapIdx (RecSpec.stageEntry done G Xs)) := by
  apply List.forall₂_of_length_eq_of_get (by simp)
  intro i hfinal hstage
  have hi : i < specs.length := by simpa using hfinal
  simp only [List.get_eq_getElem, List.getElem_map, List.getElem_mapIdx]
  cases hspec : specs[i]'hi with
  | mono ty =>
      simp only [RecSpec.bodyScheme, RecSpec.stageEntry]
      split
      · exact PolyTy.Generalizes.refl _
      · apply PolyTy.genGroup_generalizes_renameG_runtime
          (hmonoLC ty (by rw [← hspec]; exact List.getElem_mem hi))
          hG hXsLen hXsNodup hGXs
          (hXsMono ty (by rw [← hspec]; exact List.getElem_mem hi))
  | poly scheme =>
      exact PolyTy.Generalizes.refl _

end RuntimeTyping

/-- Checking the annotated source first justifies its completely erased runtime
term. Recursive schemes survive only as witnesses in the runtime derivation. -/
theorem TypeOfHM.erase_preserves_typing {ctx : Ctx} {e : Expr} {τ : Ty}
    (h : TypeOfHM ctx e τ) : RuntimeTyping.RunWT ctx e.erase τ := by
  induction h using TypeOfHM.rec
    (motive_2 := fun ctx branch scrutTy resultTy _ =>
      RuntimeTyping.RunWTMatchBranch ctx (branch.1, branch.2.erase)
        scrutTy resultTy) with
  | primLitUnit => simpa only [Expr.erase] using RuntimeTyping.RunWT.primLitUnit
  | primLitInt => simpa only [Expr.erase] using RuntimeTyping.RunWT.primLitInt
  | primLitNat => simpa only [Expr.erase] using RuntimeTyping.RunWT.primLitNat
  | primLitChar => simpa only [Expr.erase] using RuntimeTyping.RunWT.primLitChar
  | primBinOpIntAdd =>
      simpa only [Expr.erase] using RuntimeTyping.RunWT.primBinOpIntAdd
  | primBinOpIntSub =>
      simpa only [Expr.erase] using RuntimeTyping.RunWT.primBinOpIntSub
  | primBinOpIntLt _ _ ihtrue ihfalse =>
      simp only [Expr.erase] at ihtrue ihfalse ⊢
      exact RuntimeTyping.RunWT.primBinOpIntLt ihtrue ihfalse
  | primBinOpCharLt _ _ ihtrue ihfalse =>
      simp only [Expr.erase] at ihtrue ihfalse ⊢
      exact RuntimeTyping.RunWT.primBinOpCharLt ihtrue ihfalse
  | lambda hpc _ _ _ ihbody =>
      expose_names
      subst bodyCtx
      simp only [Expr.erase]
      exact RuntimeTyping.RunWT.lambda hpc ihbody
  | app _ _ ihfn iharg =>
      simpa only [Expr.erase] using RuntimeTyping.RunWT.app ihfn iharg
  | letIn hwf _ _ _ _ ihcofin ihbody =>
      expose_names
      subst bodyCtx
      simp only [Expr.erase]
      refine RuntimeTyping.RunWT.letIn (scheme := M) (avoid := L) hwf ?_ ihbody
      intro Xs hfresh
      have hrhs := ihcofin Xs hfresh
      rwa [Expr.erase_openBoundTyVars] at hrhs
  | var hlook hargs hinst =>
      simpa only [Expr.erase] using RuntimeTyping.RunWT.var hlook hargs hinst
  | ctor hlook hargs hinst =>
      simpa only [Expr.erase] using RuntimeTyping.RunWT.ctor hlook hargs hinst
  | match_ _ hne _ ihscrut ihbranches =>
      expose_names
      simp only [Expr.erase_match]
      refine RuntimeTyping.RunWT.match_ ihscrut ?_ ?_
      · intro hempty
        obtain ⟨head, tail, rfl⟩ := List.exists_cons_of_ne_nil hne
        simp at hempty
      · intro branch' hmem'
        obtain ⟨⟨pat, branchBody⟩, hmem, rfl⟩ := List.mem_map.mp hmem'
        exact ihbranches (pat, branchBody) hmem
  | letRec hgroups hwf _ _ heq _ ihstrat ihpoly ihbody =>
      expose_names
      subst heq
      let runtimeAvoid := L ++ G ++ specs.flatMap RecSpec.monoFreeVars
      simp only [Expr.erase_letRec]
      rw [show bindings.map (fun _ => none) =
        (bindings.map Expr.erase).map (fun _ => none) by
          simp only [List.map_map, Function.comp_def]]
      refine RuntimeTyping.RunWT.letRec (specs := specs) (G := G)
        (avoid := runtimeAvoid)
        ⟨by simpa using hwf.length, hwf.nodup, hwf.mono_lc, hwf.poly_wf⟩
        ?_ ?_ ihbody
      · intro Xs hfresh pair hpair ty heq
        obtain ⟨binding, spec, _, hpair', rfl⟩ := List.mem_zip_map_left hpair
        have hmono : spec = .mono ty := heq
        obtain ⟨member, hzip⟩ := List.mem_iff_getElem?.mp hpair'
        obtain ⟨hbinding, hspec⟩ := List.getElem?_zip_eq_some.mp hzip
        rw [hmono] at hspec
        have hbound : member < bindings.length := by
          exact (List.getElem?_eq_some_iff.mp hbinding).1
        have hunsigned : RecGroups.UnsignedAt anns member := by
          simp only [RecGroups.UnsignedAt, ← hwf.anns_eq,
            List.getElem?_map, hspec, Option.map_some, RecSpec.ann]
        have hcovered := (hgroups.covers_unsigned member hbound).2 hunsigned
        obtain ⟨component, hcomponent, hmember⟩ := List.mem_flatten.mp hcovered
        obtain ⟨stage, hstage⟩ := List.mem_iff_getElem?.mp hcomponent
        have hfreshSource : FreshNames L G.length Xs := by
          refine ⟨hfresh.length, hfresh.nodup, ?_⟩
          intro x hx hL
          exact hfresh.avoid x hx (by
            simp only [runtimeAvoid, List.mem_append]
            exact .inl (.inl hL))
        have hrhs := ihstrat stage component hstage Xs hfreshSource
          member hmember binding ty hbinding hspec
        have hGXs : ∀ g ∈ G, g ∉ Xs := by
          intro g hg hmem
          exact hfresh.avoid g hmem (by
            simp only [runtimeAvoid, List.mem_append]
            exact .inl (.inr hg))
        have hXsMono : ∀ monoTy, RecSpec.mono monoTy ∈ specs →
            ∀ x ∈ Xs, x ∉ monoTy.freeVars := by
          intro monoTy hmember x hx hfree
          exact hfresh.avoid x hx (by
            simp only [runtimeAvoid, List.mem_append]
            exact .inr (List.mem_flatMap.mpr
              ⟨.mono monoTy, hmember, hfree⟩))
        have hgens :=
          RuntimeTyping.bodySchemes_generalize_stageEntries_runtime
            (done := (groups.take stage).flatten)
            hwf.nodup hfresh.length hfresh.nodup hwf.mono_lc hGXs hXsMono
        have hfinal := RuntimeTyping.RunWT.weaken_schemes hgens hrhs
        simpa only [RecSpecs.stageCtx, RecSpecs.bodyCtx] using hfinal
      · intro pair hpair scheme heq Ys hfreshY
        obtain ⟨binding, spec, _, hpair', rfl⟩ := List.mem_zip_map_left hpair
        have hfreshSource : FreshNames L scheme.paramCount Ys := by
          refine ⟨hfreshY.length, hfreshY.nodup, ?_⟩
          intro x hx hL
          exact hfreshY.avoid x hx (by
            simp only [runtimeAvoid, List.mem_append]
            exact .inl (.inl hL))
        have hrhs := ihpoly (binding, spec) hpair' scheme heq Ys hfreshSource
        rwa [Expr.erase_openTyVars] at hrhs
  | mk hspec _ _ ihbody =>
      expose_names
      subst bodyCtx
      exact RuntimeTyping.RunWTMatchBranch.mk hspec ihbody
  | wildcard _ ihbody => exact RuntimeTyping.RunWTMatchBranch.wildcard ihbody

namespace RuntimeTyping


/-! ## Runtime type substitution

This is proof-only substitution.  Runtime expressions contain no type
annotations, so substituting a free type variable changes the context and the
derived type but leaves the expression itself untouched.  The recursive case
freshens the shared HM pool before applying the substitution.
-/

private theorem mem_zip_map_right_runtime {α β γ : Type _} {f : β → γ} :
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

private def substSpecs (Z : Nat) (U : Ty) (G W : List Nat)
    (specs : List RecSpec) : List RecSpec :=
  specs.map (RecSpec.substFreshened Z U G W)

theorem RunWT.substFvar {ctx : Ctx} {e : Expr} {ty U : Ty} {Z : Nat}
    (hU : U.IsLC) (h : RunWT ctx e ty) :
    RunWT { ctx with env := ctx.env.substFvar Z U } e
      (Ty.substFvar Z U ty) := by
  induction h using RunWT.rec
    (motive_2 := fun ctx branch scrutTy resultTy _ =>
      RunWTMatchBranch { ctx with env := ctx.env.substFvar Z U }
        branch (Ty.substFvar Z U scrutTy) (Ty.substFvar Z U resultTy)) with
  | primLitUnit => exact .primLitUnit
  | primLitInt => exact .primLitInt
  | primLitNat => exact .primLitNat
  | primLitChar => exact .primLitChar
  | primBinOpIntAdd => exact .primBinOpIntAdd
  | primBinOpIntSub => exact .primBinOpIntSub
  | primBinOpIntLt _ _ ihtrue ihfalse =>
      exact .primBinOpIntLt ihtrue ihfalse
  | primBinOpCharLt _ _ ihtrue ihfalse =>
      exact .primBinOpCharLt ihtrue ihfalse
  | lambda hparam _ ihbody =>
      expose_names
      simpa only [Env.substFvar, List.map_cons, PolyTy.substFvar,
        PolyTy.mkTrivial] using
        (RunWT.lambda (ctx := { ctx_1 with env := ctx_1.env.substFvar Z U })
          (Ty.IsLC.substFvar hU hparam) ihbody)
  | app _ _ ihfn iharg => exact .app ihfn iharg
  | letIn hwf hgen _ ihgen ihbody =>
      expose_names
      let avoid' := Z :: avoid
      apply RunWT.letIn (scheme := scheme.substFvar Z U) (avoid := avoid')
      · exact hwf.substFvar hU
      · intro names hfresh
        have hfresh0 : FreshNames avoid scheme.paramCount names := by
          refine ⟨by simpa [PolyTy.substFvar] using hfresh.length,
            hfresh.nodup, ?_⟩
          intro x hx hmem
          exact hfresh.avoid x hx (List.mem_cons_of_mem _ hmem)
        have hZ : Z ∉ names := fun hmem =>
          hfresh.avoid Z hmem List.mem_cons_self
        have hrhs := ihgen names hfresh0
        rw [PolyTy.substFvar_openVars hU hZ]
        exact hrhs
      · simpa only [Env.substFvar, List.map_cons] using ihbody
  | var hlookup hlc hinst =>
      expose_names
      have hlookup' : (ctx_1.env.substFvar Z U)[index]? =
          some (scheme.substFvar Z U) := by
        simp only [Env.substFvar, List.getElem?_map, hlookup, Option.map_some]
      apply RunWT.var (ctx := { ctx_1 with env := ctx_1.env.substFvar Z U })
        (args := args.map (Ty.substFvar Z U))
        hlookup'
      · intro arg harg
        obtain ⟨arg0, harg0, rfl⟩ := List.mem_map.mp harg
        exact Ty.IsLC.substFvar hU (hlc arg0 harg0)
      · exact InstantiatesBy.substFvar hU hinst
  | ctor hlookup hlc hinst =>
      expose_names
      have hinst' := InstantiatesBy.substFvar (Z := Z) (U := U) hU hinst
      rw [Ty.substFvar_fresh
        (NoFreeVars.not_mem_freeVars (Ctor.toTy_body_noFreeVars _) Z)] at hinst'
      apply RunWT.ctor (ctx := { ctx_1 with env := ctx_1.env.substFvar Z U })
        (args := args.map (Ty.substFvar Z U))
        hlookup
      · intro arg harg
        obtain ⟨arg0, harg0, rfl⟩ := List.mem_map.mp harg
        exact Ty.IsLC.substFvar hU (hlc arg0 harg0)
      · exact hinst'
  | match_ _ hne _ ihscrut ihbranches =>
      exact .match_ ihscrut hne ihbranches
  | @letRec bindings ctx body resultTy specs G avoid hwf hmono hpoly _
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
      let avoid' := Z :: G ++ W ++ avoid
      have hwf' : RecSpecsWF bindings specs' W := by
        refine ⟨by simpa [specs', substSpecs] using hwf.length,
          hWnodup, ?_, ?_⟩
        · intro τ' hτ'
          obtain ⟨spec, hspec, heq⟩ := List.mem_map.mp hτ'
          cases spec with
          | mono τ =>
              simp only [RecSpec.substFreshened, RecSpec.mono.injEq] at heq
              subst τ'
              exact Ty.IsLC.substFvar hU
                (Ty.renameG_isLC_runtime (hwf.mono_lc τ hspec))
          | poly scheme => exact RecSpec.noConfusion heq
        · intro scheme' hscheme'
          obtain ⟨spec, hspec, heq⟩ := List.mem_map.mp hscheme'
          cases spec with
          | mono τ => exact RecSpec.noConfusion heq
          | poly scheme =>
              simp only [RecSpec.substFreshened, RecSpec.poly.injEq] at heq
              subst scheme'
              exact (hwf.poly_wf scheme hspec).substFvar hU
      have henvBody :
          (RecSpecs.bodyCtx { ctx with env := ctx.env.substFvar Z U }
              specs' W).env =
            (RecSpecs.bodyCtx ctx specs G).env.substFvar Z U := by
        unfold RecSpecs.bodyCtx specs' substSpecs
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
              (hwf.mono_lc τ hτ) hWlen hwf.nodup hWnodup hGW
              (hWfree τ hτ)
            have hsubst := PolyTy.genGroup_substFvar
              (Z := Z) (U := U) (G := W) (τ := Ty.renameG G W τ) hZW hUW
            simp only [Function.comp_apply, RecSpec.substFreshened,
              RecSpec.bodyScheme]
            rw [← hsubst, ← hrename]
      have hctxBody :
          RecSpecs.bodyCtx { ctx with env := ctx.env.substFvar Z U }
              specs' W =
            { RecSpecs.bodyCtx ctx specs G with
              env := (RecSpecs.bodyCtx ctx specs G).env.substFvar Z U } := by
        cases ctx
        simp only [RecSpecs.bodyCtx] at henvBody ⊢
        rw [henvBody]
      apply RunWT.letRec (specs := specs') (G := W) (avoid := avoid') hwf'
      · intro Xs hXs pair hpair τ' hτ'
        have hXlen : Xs.length = G.length := hXs.length.trans hWlen
        have hZXs : Z ∉ Xs := fun hc =>
          hXs.avoid Z hc (by simp [avoid'])
        have hGXs : ∀ g ∈ G, g ∉ Xs := fun g hg hc =>
          hXs.avoid g hc (by simp [avoid', List.mem_append, hg])
        have hWXs : ∀ w ∈ W, w ∉ Xs := fun w hw hc =>
          hXs.avoid w hc (by simp [avoid', List.mem_append, hw])
        have hXs0 : FreshNames avoid G.length Xs := by
          refine ⟨hXlen, hXs.nodup, ?_⟩
          intro x hx ha
          exact hXs.avoid x hx (by simp [avoid', List.mem_append, ha])
        obtain ⟨rhs0, spec0, hold, rfl⟩ := mem_zip_map_right_runtime hpair
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
                    (Ty.renameG_isLC_runtime (hwf.mono_lc τ hτmem))
                    hWnodup hXs.length hWXs,
                Ty.renameG_renameG (hwf.mono_lc τ hτmem) hwf.nodup
                  hWnodup hWlen hXlen hGW (hWfree τ hτmem) hWXs hGXs]
            rw [hkey]
            have ht := ihmono Xs hXs0 (rhs0, .mono τ) hold τ rfl
            rw [hctxBody]
            exact ht
      · intro pair hpair scheme' hscheme' Ys hYs
        obtain ⟨rhs0, spec0, hold, rfl⟩ := mem_zip_map_right_runtime hpair
        cases spec0 with
        | mono τ => exact RecSpec.noConfusion hscheme'
        | poly scheme =>
            simp only [RecSpec.substFreshened, RecSpec.poly.injEq] at hscheme'
            subst scheme'
            have hYs0 : FreshNames avoid scheme.paramCount Ys := by
              refine ⟨by simpa [PolyTy.substFvar] using hYs.length,
                hYs.nodup, ?_⟩
              intro y hy hmem
              apply hYs.avoid y hy
              simp only [avoid', List.mem_cons, List.mem_append]
              tauto
            have hZYs : Z ∉ Ys := fun hc =>
              hYs.avoid Z hc (by simp [avoid'])
            rw [show (scheme.substFvar Z U).openVars Ys =
                Ty.substFvar Z U (scheme.openVars Ys) by
                  unfold PolyTy.openVars PolyTy.substFvar
                  exact (Ty.substFvar_openVars hU hZYs).symm]
            have ht := ihpoly (rhs0, .poly scheme) hold scheme rfl Ys hYs0
            rw [hctxBody]
            exact ht
      · rw [hctxBody]
        exact ihbody
  | mk hspec _ ihbody =>
      expose_names
      have hcontents : ctor.contents.map (Ty.substFvar Z U) = ctor.contents := by
        calc
          ctor.contents.map (Ty.substFvar Z U) = ctor.contents.map id := by
            apply List.map_congr_left
            intro field hfield
            exact Ty.substFvar_fresh
              ((ctor.closed field hfield).not_mem_freeVars Z)
          _ = ctor.contents := by simp only [List.map_id]
      have hfields := InstantiatesBy.forall2_substFvar
        (Z := Z) (U := U) hU hspec.fields
      rw [hcontents] at hfields
      rw [Env.substFvar_append, Env.substFvar_map_mkTrivial] at ihbody
      have hspec' : BranchCtorSpec ctx_1.ctors c n
          (Ty.substFvar Z U scrutTy) ctor
          (tyArgs.map (Ty.substFvar Z U))
          (instContents.map (Ty.substFvar Z U)) :=
        ⟨hspec.lookup, by
          rw [hspec.scrut_eq]
          simp [Ty.substFvar, TyList.substFvar_eq_map],
          by simpa using hspec.arity,
          hspec.bind_count, hfields⟩
      exact RunWTMatchBranch.mk
        (ctx := { ctx_1 with env := ctx_1.env.substFvar Z U })
        hspec' (by simpa only using ihbody)
  | wildcard _ ihbody => exact .wildcard ihbody


/-! ## Recursive rewrapping and scheme inhabitants

The operational `letRecUnfold` step substitutes each recursively wrapped
member for the corresponding body variable.  The wrapper is an ordinary
erased `letRec`: its typing derivation remembers the mixed recursive specs,
but its `Expr` contains only `none` annotations.  Because runtime group
evidence types every RHS under the final exported schemes, re-wrapping a member
is now a direct use of the runtime `letRec` rule.
-/

/-- Re-wrap one recursive member.  Runtime group evidence already types every
RHS under the final exported schemes, exactly the context used for the wrapper
body. -/
theorem RunWT.rec_rewrap_at {ctx : Ctx} {bindings : List Expr}
    {specs : List RecSpec} {G avoid : List Nat}
    (hwf : RecSpecsWF bindings specs G)
    (hmono : MonoTyped RunWT ctx bindings specs G avoid)
    (hpoly : PolyTyped RunWT ctx bindings specs G avoid)
    {rhs : Expr} {ty : Ty}
    (hrhs : RunWT (RecSpecs.bodyCtx ctx specs G) rhs ty) :
    RunWT ctx (.letRec (bindings.map (fun _ => none)) bindings rhs) ty := by
  exact RunWT.letRec hwf hmono hpoly hrhs

/-- An erased value inhabits a scheme when it has every locally-closed
`InstantiatesBy` instance accepted by the production variable rule. -/
def RunHasScheme (ctx : Ctx) (value : Expr) (scheme : PolyTy) : Prop :=
  ∀ args ty, (∀ arg ∈ args, arg.IsLC) →
    scheme.InstantiatesTo args ty → RunWT ctx value ty


/-! ### From cofinite openings to production scheme instances

The production variable rule intentionally does not require its witness list
to have exactly the scheme arity: unused quantifiers may be omitted and extra
arguments are harmless.  For the cofinite proof we canonicalize that witness
to exactly `paramCount` entries, padding omitted unused entries with `Unit`.
-/

private def exactInstArgs (n : Nat) (args : List Ty) : List Ty :=
  (List.range n).map (fun i => (args[i]?).getD (.prim .unit))

private theorem exactInstArgs_areLC {n : Nat} {args : List Ty}
    (hlc : ∀ arg ∈ args, arg.IsLC) : Ty.AreLC n (exactInstArgs n args) := by
  constructor
  · simp [exactInstArgs]
  · intro arg harg
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp harg
    cases hget : args[i]? with
    | none => exact ContainsBvarsUpTo.prim
    | some actual =>
        simp only [Option.getD_some]
        exact hlc actual (List.mem_of_getElem? hget)

private theorem exactInstArgs_realise {scheme : PolyTy} {args : List Ty}
    {ty : Ty} (hwf : scheme.WF)
    (hinst : scheme.InstantiatesTo args ty) :
    ty = scheme.openWith (exactInstArgs scheme.paramCount args) := by
  unfold PolyTy.InstantiatesTo at hinst
  have h := InstantiatesBy.eq_openWith_range hinst hwf
  simpa [exactInstArgs, PolyTy.openWith] using h

private def substFvarsEnvRuntime : List (Nat × Ty) → Env → Env
  | [], env => env
  | (name, replacement) :: rest, env =>
      substFvarsEnvRuntime rest (env.substFvar name replacement)

private theorem RunWT.substFvars {ctx : Ctx} {e : Expr} {ty : Ty}
    {pairs : List (Nat × Ty)}
    (hlc : ∀ pair ∈ pairs, pair.2.IsLC) (h : RunWT ctx e ty) :
    RunWT { ctx with env := substFvarsEnvRuntime pairs ctx.env }
      e (Ty.substFvars pairs ty) := by
  induction pairs generalizing ctx ty with
  | nil => simpa [substFvarsEnvRuntime, Ty.substFvars] using h
  | cons pair rest ih =>
      obtain ⟨name, replacement⟩ := pair
      simp only [substFvarsEnvRuntime, Ty.substFvars]
      exact ih (fun pair hpair => hlc pair (List.mem_cons_of_mem _ hpair))
        (h.substFvar (hlc (name, replacement) List.mem_cons_self))

private theorem substFvarsEnvRuntime_eq_self_of_fresh
    {pairs : List (Nat × Ty)} {env : Env}
    (hfresh : ∀ pair ∈ pairs, pair.1 ∉ env.freeVars) :
    substFvarsEnvRuntime pairs env = env := by
  induction pairs generalizing env with
  | nil => rfl
  | cons pair rest ih =>
      obtain ⟨name, replacement⟩ := pair
      simp only [substFvarsEnvRuntime]
      rw [Env.substFvar_fresh (hfresh (name, replacement) List.mem_cons_self)]
      exact ih (fun pair hpair => hfresh pair (List.mem_cons_of_mem _ hpair))

private theorem pairs_zip_values_lc_runtime {names : List Nat} {args : List Ty}
    (hlc : ∀ arg ∈ args, arg.IsLC) :
    ∀ pair ∈ names.zip args, pair.2.IsLC := by
  intro pair hpair
  exact hlc pair.2 (List.of_mem_zip hpair).2

private theorem pairs_zip_names_fresh_runtime {names : List Nat}
    {args : List Ty} {env : Env}
    (hfresh : ∀ name ∈ names, name ∉ env.freeVars) :
    ∀ pair ∈ names.zip args, pair.1 ∉ env.freeVars := by
  intro pair hpair
  exact hfresh pair.1 (List.of_mem_zip hpair).1

/-- Replace one fresh rigid opening by an exact concrete scheme instance.
The erased runtime expression itself is unchanged. -/
private theorem RunWT.instantiate_opening {ctx : Ctx} {e : Expr}
    {scheme : PolyTy} {names : List Nat} {args : List Ty}
    (hargs : Ty.AreLC scheme.paramCount args)
    (hnamesLen : names.length = scheme.paramCount)
    (hnamesNodup : names.Nodup)
    (hnamesEnv : ∀ x ∈ names, x ∉ ctx.env.freeVars)
    (hnamesBody : ∀ x ∈ names, x ∉ scheme.body.freeVars)
    (hnamesArgs : ∀ x ∈ names, x ∉ Ty.freeVarsList args)
    (htyped : RunWT ctx e (scheme.openVars names)) :
    RunWT ctx e (scheme.openWith args) := by
  have hsub := RunWT.substFvars (pairs := names.zip args)
    (pairs_zip_values_lc_runtime (names := names) hargs.2) htyped
  rw [substFvarsEnvRuntime_eq_self_of_fresh
    (pairs_zip_names_fresh_runtime hnamesEnv)] at hsub
  have hopen := Ty.openWith_eq_substFvars_openVars
    (ty := scheme.body) (Vs := args) (Xs := names)
    ⟨hargs.1.trans hnamesLen.symm, hargs.2⟩
    hnamesNodup hnamesBody hnamesArgs
  simpa [PolyTy.openVars, PolyTy.openWith, hopen] using hsub

/-- A completely annotated recursive member retains its declared scheme when
the erased group is wrapped around it. -/
theorem RunHasScheme.ofPolyRecMember {ctx : Ctx}
    {bindings : List Expr} {specs : List RecSpec} {G avoid : List Nat}
    (hwf : RecSpecsWF bindings specs G)
    (hmono : MonoTyped RunWT ctx bindings specs G avoid)
    (hpoly : PolyTyped RunWT ctx bindings specs G avoid)
    {rhs : Expr} {scheme : PolyTy}
    (hmember : (rhs, .poly scheme) ∈ bindings.zip specs) :
    RunHasScheme ctx
      (.letRec (bindings.map (fun _ => none)) bindings rhs) scheme := by
  intro args ty hlc hinst
  let exactArgs := exactInstArgs scheme.paramCount args
  have hargs : Ty.AreLC scheme.paramCount exactArgs :=
    exactInstArgs_areLC hlc
  have hschemeWf : scheme.WF := hwf.poly_wf scheme (List.of_mem_zip hmember).2
  have hrealise := exactInstArgs_realise hschemeWf hinst
  rw [hrealise]
  obtain ⟨Ys, hYsLen, hYsNodup, hYsAvoid⟩ :=
    exists_fresh_names
      (avoid ++ ctx.env.freeVars ++ scheme.body.freeVars ++
        Ty.freeVarsList exactArgs)
      scheme.paramCount
  have hYs : FreshNames avoid scheme.paramCount Ys :=
    ⟨hYsLen, hYsNodup, fun y hy hmem => hYsAvoid y hy (by
      simp only [List.mem_append]
      exact Or.inl (Or.inl (Or.inl hmem)))⟩
  have htyped := hpoly (rhs, .poly scheme) hmember scheme rfl Ys hYs
  have hwrapped := RunWT.rec_rewrap_at hwf hmono hpoly htyped
  apply RunWT.instantiate_opening hargs hYsLen hYsNodup
    (htyped := hwrapped)
  · intro y hy hmem
    exact hYsAvoid y hy (by simp [List.mem_append, hmem])
  · intro y hy hmem
    exact hYsAvoid y hy (by simp [List.mem_append, hmem])
  · intro y hy hmem
    exact hYsAvoid y hy (by simp [List.mem_append, hmem])

/-- An ordinary recursive member is available at the HM scheme obtained by
generalising its shared inference-phase monotype. Source checking performs that
generalisation before signed RHSs; erased runtime typing records only the final
scheme environment. -/
theorem RunHasScheme.ofMonoRecMember {ctx : Ctx}
    {bindings : List Expr} {specs : List RecSpec} {G avoid : List Nat}
    (hwf : RecSpecsWF bindings specs G)
    (hmono : MonoTyped RunWT ctx bindings specs G avoid)
    (hpoly : PolyTyped RunWT ctx bindings specs G avoid)
    {rhs : Expr} {ty : Ty}
    (hmember : (rhs, .mono ty) ∈ bindings.zip specs) :
    RunHasScheme ctx
      (.letRec (bindings.map (fun _ => none)) bindings rhs)
      (PolyTy.genGroup G ty) := by
  intro args result hlc hinst
  let scheme := PolyTy.genGroup G ty
  let exactArgs := exactInstArgs scheme.paramCount args
  have hargs : Ty.AreLC scheme.paramCount exactArgs :=
    exactInstArgs_areLC hlc
  have htyLC : ty.IsLC := hwf.mono_lc ty (List.of_mem_zip hmember).2
  have hschemeWf : scheme.WF := PolyTy.genGroup_wf htyLC
  have hrealise := exactInstArgs_realise hschemeWf hinst
  rw [hrealise]
  obtain ⟨Xs, hXsLen, hXsNodup, hXsAvoid⟩ :=
    exists_fresh_names
      (avoid ++ G ++ ty.freeVars ++ ctx.env.freeVars ++ Ty.freeVarsList exactArgs ++
        scheme.body.freeVars)
      G.length
  have hXs : FreshNames avoid G.length Xs :=
    ⟨hXsLen, hXsNodup, fun x hx hmem =>
      hXsAvoid x hx (by simp [List.mem_append, hmem])⟩
  have hdisj : ∀ g ∈ G, g ∉ Xs := fun g hg hc =>
    hXsAvoid g hc (by simp [List.mem_append, hg])
  have hXsTy : ∀ x ∈ Xs, x ∉ ty.freeVars := fun x hx hc =>
    hXsAvoid x hx (by simp [List.mem_append, hc])
  have hXsEnv : ∀ x ∈ Xs, x ∉ ctx.env.freeVars := fun x hx hc =>
    hXsAvoid x hx (by simp [List.mem_append, hc])
  have hXsArgs : ∀ x ∈ Xs, x ∉ Ty.freeVarsList exactArgs := fun x hx hc =>
    hXsAvoid x hx (by simp [List.mem_append, hc])
  have hXsBody : ∀ x ∈ Xs, x ∉ scheme.body.freeVars := fun x hx hc =>
    hXsAvoid x hx (by simp [List.mem_append, hc])
  have htyped := hmono Xs hXs (rhs, .mono ty) hmember ty rfl
  have hwrapped : RunWT ctx
      (.letRec (bindings.map (fun _ => none)) bindings rhs)
      (Ty.renameG G Xs ty) :=
    RunWT.rec_rewrap_at hwf hmono hpoly htyped
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
  apply RunWT.instantiate_opening hargs
    (scheme := scheme) (names := Xs')
    (by simpa [scheme, PolyTy.genGroup] using hXsLen') hXsNodup'
    (htyped := by simpa [scheme, PolyTy.genGroup, PolyTy.openVars] using hwrapped)
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

/-- Runtime typing produces a locally closed result type. -/
theorem RunWT.regular {ctx : Ctx} {e : Expr} {ty : Ty}
    (h : RunWT ctx e ty) : ty.IsLC := by
  induction h using RunWT.rec
    (motive_2 := fun _ _ _ resultTy _ => resultTy.IsLC) with
  | primLitUnit => exact .prim
  | primLitInt => exact .prim
  | primLitNat => exact .prim
  | primLitChar => exact .prim
  | primBinOpIntAdd => exact .arrow .prim (.arrow .prim .prim)
  | primBinOpIntSub => exact .arrow .prim (.arrow .prim .prim)
  | primBinOpIntLt _ _ _ _ => exact .arrow .prim (.arrow .prim (.customTy (by simp)))
  | primBinOpCharLt _ _ _ _ => exact .arrow .prim (.arrow .prim (.customTy (by simp)))
  | lambda hparam _ ihbody => exact .arrow hparam ihbody
  | app _ _ ihfn _ =>
      cases ihfn with
      | arrow _ hresult => exact hresult
  | letIn _ _ _ _ ihbody => exact ihbody
  | var _ hlc hinst => exact InstantiatesBy.preserves_bvars hlc hinst
  | ctor _ hlc hinst => exact InstantiatesBy.preserves_bvars hlc hinst
  | match_ _ hne _ _ ihbranches =>
      obtain ⟨hd, tl, rfl⟩ := List.exists_cons_of_ne_nil hne
      exact ihbranches hd (List.mem_cons_self ..)
  | letRec _ _ _ _ _ _ ihbody => exact ihbody
  | mk _ _ ihbody => exact ihbody
  | wildcard _ ihbody => exact ihbody

/-- A term typed at a monotype inhabits its trivial scheme. -/
theorem RunHasScheme.ofTrivial {ctx : Ctx} {value : Expr} {ty : Ty}
    (h : RunWT ctx value ty) :
    RunHasScheme ctx value (PolyTy.mkTrivial ty) := by
  intro args result _ hinst
  have heq := InstantiatesBy.eq_openWith_range hinst h.regular
  have hresult : result = ty := by
    simpa [PolyTy.mkTrivial, Ty.openWith_nil] using heq
  rw [hresult]
  exact h

/-- A cofinally checked let-bound expression inhabits every production
`InstantiatesBy` instance of its generalized scheme. -/
theorem RunHasScheme.ofGeneralisesTo {ctx : Ctx} {rhs : Expr}
    {scheme : PolyTy} {avoid : List Nat}
    (hwf : scheme.WF)
    (hgen : GeneralisesTo RunWT ctx rhs scheme avoid) :
    RunHasScheme ctx rhs scheme := by
  intro args ty hlc hinst
  let exactArgs := exactInstArgs scheme.paramCount args
  have hargs : Ty.AreLC scheme.paramCount exactArgs :=
    exactInstArgs_areLC hlc
  have hrealise := exactInstArgs_realise hwf hinst
  rw [hrealise]
  obtain ⟨Xs, hXsLen, hXsNodup, hXsAvoid⟩ :=
    exists_fresh_names
      (avoid ++ ctx.env.freeVars ++ scheme.body.freeVars ++
        Ty.freeVarsList exactArgs)
      scheme.paramCount
  have hXs : FreshNames avoid scheme.paramCount Xs :=
    ⟨hXsLen, hXsNodup, fun x hx hmem =>
      hXsAvoid x hx (by simp [List.mem_append, hmem])⟩
  apply RunWT.instantiate_opening hargs hXsLen hXsNodup
    (htyped := hgen Xs hXs)
  · intro x hx hmem
    exact hXsAvoid x hx (by simp [List.mem_append, hmem])
  · intro x hx hmem
    exact hXsAvoid x hx (by simp [List.mem_append, hmem])
  · intro x hx hmem
    exact hXsAvoid x hx (by simp [List.mem_append, hmem])

/-! ### Constructor-spine inversion for match reduction -/

private theorem List.Forall₂.snoc_runtime {α β : Type _} {R : α → β → Prop}
    {left : List α} {right : List β} {a : α} {b : β}
    (h : List.Forall₂ R left right) (hab : R a b) :
    List.Forall₂ R (left ++ [a]) (right ++ [b]) := by
  induction h with
  | nil => exact .cons hab .nil
  | cons hhd _ ih => exact .cons hhd ih

/-- Invert typing directly along the constructor spine supplied by the
operational match rule. No separate canonical-forms detour is required. -/
theorem RunWT.ctor_applied_inversion {ctx : Ctx} {e : Expr}
    {name : CtorName} {args : List Expr} {ty : Ty}
    (hcat : SmallStep.CtorAppliedTo e name args)
    (htyped : RunWT ctx e ty) :
    ∃ (ctor : Ctor) (tyArgs consumed remaining : List Ty),
      LookupList.get? ctx.ctors name = some ctor ∧
      (∀ arg ∈ tyArgs, arg.IsLC) ∧
      ctor.contents = consumed ++ remaining ∧
      List.Forall₂
        (fun value field =>
          ∃ fieldTy, InstantiatesBy tyArgs field fieldTy ∧
            RunWT ctx value fieldTy)
        args consumed ∧
      InstantiatesBy tyArgs
        (Ty.wrapArrows
          (.customTy ctor.tyName (Ty.bvarRange ctor.paramCount)) remaining)
        ty := by
  induction hcat generalizing ty with
  | base name =>
      cases htyped with
      | ctor hlook htyargs hinst =>
          exact ⟨_, _, [], _, hlook, htyargs, rfl, .nil,
            by simpa [Ctor.toTy] using hinst⟩
  | step hcat ih =>
      cases htyped with
      | app hf harg =>
          obtain ⟨ctor, tyArgs, consumed, remaining, hlook, htyargs,
            hcontents, hforall, hinst_f⟩ := ih hf
          cases remaining with
          | nil =>
              simp only [Ty.wrapArrows] at hinst_f
              cases hinst_f
          | cons field rest =>
              simp only [Ty.wrapArrows] at hinst_f
              cases hinst_f with
              | arrow hfield hrest =>
                  refine ⟨ctor, tyArgs, consumed ++ [field], rest,
                    hlook, htyargs, ?_, List.Forall₂.snoc_runtime hforall
                      ⟨_, hfield, harg⟩,
                    hrest⟩
                  rw [hcontents]
                  exact (List.append_assoc consumed [field] rest).symm

/-- Align constructor-field instances from the branch typing and the runtime
constructor spine, producing the scheme inhabitants consumed by `substMany`. -/
private theorem InstantiatesBy.build_run_match_values
    {ctx : Ctx} {n : Nat} {tyArgs tyArgsSpine : List Ty}
    (hagree : ∀ k, k < n → tyArgs[k]? = tyArgsSpine[k]?) :
    ∀ {contents instContents : List Ty} {args : List Expr},
      (∀ field ∈ contents, ContainsBvarsUpTo n field) →
      List.Forall₂ (InstantiatesBy tyArgs) contents instContents →
      List.Forall₂
        (fun value field =>
          ∃ fieldTy, InstantiatesBy tyArgsSpine field fieldTy ∧
            RunWT ctx value fieldTy)
        args contents →
      List.Forall₂ (RunHasScheme ctx)
        args (instContents.map PolyTy.mkTrivial) := by
  intro contents
  induction contents with
  | nil =>
      intro instContents args _ hinst hfor
      cases hinst
      cases hfor
      exact .nil
  | cons field rest ih =>
      intro instContents args hbound hinst hfor
      cases hinst with
      | cons hinstField hinstRest =>
          cases hfor with
          | cons hforField hforRest =>
              obtain ⟨fieldTy, hspine, hvalue⟩ := hforField
              have heq := InstantiatesBy.det_agree hagree
                (hbound field List.mem_cons_self) hinstField hspine
              refine List.Forall₂.cons ?_
                (ih (fun ty hty => hbound ty (List.mem_cons_of_mem _ hty))
                  hinstRest hforRest)
              rw [heq]
              exact RunHasScheme.ofTrivial hvalue

private theorem RunHasScheme.ofRecMember {ctx : Ctx}
    {bindings : List Expr} {specs : List RecSpec} {G avoid : List Nat}
    (hwf : RecSpecsWF bindings specs G)
    (hmono : MonoTyped RunWT ctx bindings specs G avoid)
    (hpoly : PolyTyped RunWT ctx bindings specs G avoid)
    {rhs : Expr} {spec : RecSpec}
    (hmember : (rhs, spec) ∈ bindings.zip specs) :
    RunHasScheme ctx
      (.letRec (bindings.map (fun _ => none)) bindings rhs)
      (spec.bodyScheme G) := by
  cases spec with
  | mono ty =>
      simpa [RecSpec.bodyScheme] using
        RunHasScheme.ofMonoRecMember hwf hmono hpoly hmember
  | poly scheme =>
      simpa [RecSpec.bodyScheme] using
        RunHasScheme.ofPolyRecMember hwf hmono hpoly hmember

/-- Every recursively wrapped RHS inhabits the scheme exported for its slot.
This is exactly the replacement list used by `Step.letRecUnfold`. -/
private theorem recursiveValuesHaveSchemes {ctx : Ctx}
    {bindings : List Expr} {specs : List RecSpec} {G avoid : List Nat}
    (hwf : RecSpecsWF bindings specs G)
    (hmono : MonoTyped RunWT ctx bindings specs G avoid)
    (hpoly : PolyTyped RunWT ctx bindings specs G avoid) :
    List.Forall₂ (RunHasScheme ctx)
      (bindings.map (fun rhs =>
        .letRec (bindings.map (fun _ => none)) bindings rhs))
      (specs.map (RecSpec.bodyScheme G)) := by
  have hall : ∀ pair ∈ bindings.zip specs,
      RunHasScheme ctx
        (.letRec (bindings.map (fun _ => none)) bindings pair.1)
        (pair.2.bodyScheme G) := by
    intro pair hpair
    exact RunHasScheme.ofRecMember hwf hmono hpoly hpair
  have go : ∀ (bs : List Expr) (ss : List RecSpec),
      bs.length = ss.length →
      (∀ pair ∈ bs.zip ss,
        RunHasScheme ctx
          (.letRec (bindings.map (fun _ => none)) bindings pair.1)
          (pair.2.bodyScheme G)) →
      List.Forall₂ (RunHasScheme ctx)
        (bs.map (fun rhs =>
          .letRec (bindings.map (fun _ => none)) bindings rhs))
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
            refine .cons ?_ ?_
            · exact hmembers (rhs, spec) (by simp)
            · apply ih specs (by simpa using hlen)
              intro pair hpair
              exact hmembers pair (by simp [hpair])
  exact go bindings specs hwf.length hall

/-! ### Term-environment transport

Operational substitution inserts erased values under binders.  The following
weakening theorem accounts for that insertion by shifting free de Bruijn
indices; types, schemes, and constructor declarations are unchanged.
-/

theorem RunWT.weakenEnv {ctors : CtorEnv} {envPre envExtra env : Env}
    {e : Expr} {ty : Ty}
    (h : RunWT ⟨envPre ++ env, ctors⟩ e ty) :
    RunWT ⟨envPre ++ envExtra ++ env, ctors⟩
      (e.shiftFrom envPre.length envExtra.length) ty := by
  suffices H : ∀ {ctx' : Ctx} {e' : Expr} {ty' : Ty}, RunWT ctx' e' ty' →
      ∀ pre : Env, ctx'.env = pre ++ env →
        RunWT ⟨pre ++ envExtra ++ env, ctx'.ctors⟩
          (e'.shiftFrom pre.length envExtra.length) ty' by
    exact H h envPre rfl
  intro ctx' e' ty' hd
  induction hd using RunWT.rec
    (motive_2 := fun ctx branch scrutTy resultTy _ =>
      ∀ pre : Env, ctx.env = pre ++ env →
        RunWTMatchBranch ⟨pre ++ envExtra ++ env, ctx.ctors⟩
          (branch.1, branch.2.shiftFrom (pre.length + branch.1.bindCount)
            envExtra.length) scrutTy resultTy) with
  | primLitUnit => intro _ _; exact .primLitUnit
  | primLitInt => intro _ _; exact .primLitInt
  | primLitNat => intro _ _; exact .primLitNat
  | primLitChar => intro _ _; exact .primLitChar
  | primBinOpIntAdd => intro _ _; exact .primBinOpIntAdd
  | primBinOpIntSub => intro _ _; exact .primBinOpIntSub
  | primBinOpIntLt _ _ ihtrue ihfalse =>
      intro pre hctx
      exact .primBinOpIntLt (ihtrue pre hctx) (ihfalse pre hctx)
  | primBinOpCharLt _ _ ihtrue ihfalse =>
      intro pre hctx
      exact .primBinOpCharLt (ihtrue pre hctx) (ihfalse pre hctx)
  | lambda hparam _ ihbody =>
      intro pre hctx
      expose_names
      simp only [Expr.shiftFrom]
      have hb := ihbody (PolyTy.mkTrivial paramTy :: pre) (by rw [hctx, List.cons_append])
      exact RunWT.lambda hparam (by
        simpa only [List.cons_append, List.length_cons] using hb)
  | app _ _ ihfn iharg =>
      intro pre hctx
      simp only [Expr.shiftFrom]
      exact .app (ihfn pre hctx) (iharg pre hctx)
  | letIn hwf hgen _ ihgen ihbody =>
      intro pre hctx
      expose_names
      simp only [Expr.shiftFrom]
      apply RunWT.letIn (scheme := scheme) (avoid := avoid) hwf
      · intro names hfresh
        exact ihgen names hfresh pre hctx
      · have hb := ihbody (scheme :: pre) (by rw [hctx, List.cons_append])
        simpa only [List.cons_append, List.length_cons] using hb
  | var hlookup hlc hinst =>
      intro pre hctx
      expose_names
      rw [hctx] at hlookup
      simp only [Expr.shiftFrom]
      by_cases hlt : index < pre.length
      · rw [if_pos hlt]
        refine .var ?_ hlc hinst
        rw [List.getElem?_append_left
          (by simp only [List.length_append]; omega : index < (pre ++ envExtra).length),
          List.getElem?_append_left hlt]
        rwa [List.getElem?_append_left hlt] at hlookup
      · rw [if_neg hlt]
        refine .var ?_ hlc hinst
        rw [List.getElem?_append_right
          (by simp only [List.length_append]; omega :
            (pre ++ envExtra).length ≤ index + envExtra.length)]
        rw [show index + envExtra.length - (pre ++ envExtra).length =
          index - pre.length by simp only [List.length_append]; omega]
        rwa [List.getElem?_append_right (by omega)] at hlookup
  | ctor hlookup hlc hinst =>
      intro _ _
      exact .ctor hlookup hlc hinst
  | match_ _ hne _ ihscrut ihbranches =>
      intro pre hctx
      simp only [Expr.shiftFrom]
      refine .match_ (ihscrut pre hctx) ?_ ?_
      · intro hnil
        obtain ⟨⟨p, b⟩, rest, hb⟩ := List.exists_cons_of_ne_nil hne
        have hm := BranchList.mem_shiftFrom_of_mem
          (threshold := pre.length) (n := envExtra.length)
          (hb ▸ List.mem_cons_self (a := (p, b)))
        rw [hnil] at hm
        exact List.not_mem_nil hm
      · intro branch' hm'
        obtain ⟨pat, body, hm, rfl⟩ := BranchList.mem_shiftFrom hm'
        exact ihbranches (pat, body) hm pre hctx
  | @letRec bindings ctx body resultTy specs G avoid hwf hmono hpoly _
      ihmono ihpoly ihbody =>
      intro pre hctx
      simp only [Expr.shiftFrom, RecGroup.shiftFrom_eq_map]
      have hwf' : RecSpecsWF
          (bindings.map
            (Expr.shiftFrom (pre.length + bindings.length) envExtra.length))
          specs G :=
        { hwf with length := by simpa using hwf.length }
      have hann :
          (bindings.map
            (Expr.shiftFrom (pre.length + bindings.length) envExtra.length)).map
              (fun _ => (none : Option PolyTy)) =
            bindings.map (fun _ => (none : Option PolyTy)) := by
        simp only [List.map_map, Function.comp_def]
      rw [← hann]
      apply RunWT.letRec (specs := specs) (G := G) (avoid := avoid) hwf'
      · intro Xs hXs pair hpair τ hτ
        rw [List.zip_map_left] at hpair
        obtain ⟨oldPair, holdPair, rfl⟩ := List.mem_map.mp hpair
        have ht := ihmono Xs hXs oldPair holdPair τ hτ
          (specs.map (RecSpec.bodyScheme G) ++ pre) (by
            simp only [RecSpecs.bodyCtx, hctx, List.append_assoc])
        simp only [RecSpecs.bodyCtx, List.length_append, List.length_map] at ht
        rw [← hwf.length, Nat.add_comm bindings.length pre.length] at ht
        simpa only [RecSpecs.bodyCtx, List.append_assoc] using ht
      · intro pair hpair scheme hscheme Ys hYs
        rw [List.zip_map_left] at hpair
        obtain ⟨oldPair, holdPair, rfl⟩ := List.mem_map.mp hpair
        have ht := ihpoly oldPair holdPair scheme hscheme Ys hYs
          (specs.map (RecSpec.bodyScheme G) ++ pre) (by
            simp only [RecSpecs.bodyCtx, hctx, List.append_assoc])
        simp only [RecSpecs.bodyCtx, List.length_append, List.length_map] at ht
        rw [← hwf.length, Nat.add_comm bindings.length pre.length] at ht
        simpa only [RecSpecs.bodyCtx, List.append_assoc] using ht
      · have hb := ihbody (specs.map (RecSpec.bodyScheme G) ++ pre) (by
          simp only [RecSpecs.bodyCtx, hctx, List.append_assoc])
        simp only [RecSpecs.bodyCtx, List.length_append, List.length_map] at hb
        rw [← hwf.length, Nat.add_comm bindings.length pre.length] at hb
        simpa only [RecSpecs.bodyCtx, List.append_assoc] using hb
  | mk hspec _ ihbody =>
      expose_names
      have hb := ihbody (instContents.map PolyTy.mkTrivial ++ pre) (by
        rw [h_2, List.append_assoc])
      simp only [List.length_append, List.length_map] at hb
      have hlen : instContents.length = n := by
        have := List.Forall₂.length_eq hspec.fields
        simpa [hspec.bind_count] using this.symm
      rw [hlen, Nat.add_comm n pre.length] at hb
      exact RunWTMatchBranch.mk hspec (by
        simpa only [List.append_assoc] using hb)
  | wildcard _ ihbody =>
      expose_names
      simpa only [MatchPattern.bindCount, Nat.add_zero] using
        (RunWTMatchBranch.wildcard (ihbody pre h_2))

/-- Simultaneous de Bruijn substitution preserves runtime typing when every
replacement inhabits the scheme stored in the environment segment it removes.
The replacement expressions remain entirely type-erased. -/
theorem RunWT.substMany {ctors : CtorEnv} {envPre env : Env}
    {schemes : List PolyTy} {values : List Expr} {e : Expr} {ty : Ty}
    (hvalues : List.Forall₂ (RunHasScheme ⟨env, ctors⟩) values schemes)
    (h : RunWT ⟨envPre ++ schemes ++ env, ctors⟩ e ty) :
    RunWT ⟨envPre ++ env, ctors⟩
      (e.substN envPre.length values) ty := by
  have hvaluesLen : values.length = schemes.length := hvalues.length_eq
  suffices H : ∀ {ctx' : Ctx} {e' : Expr} {ty' : Ty}, RunWT ctx' e' ty' →
      ∀ pre : Env, ctx'.env = pre ++ schemes ++ env → ctx'.ctors = ctors →
        RunWT ⟨pre ++ env, ctx'.ctors⟩ (e'.substN pre.length values) ty' by
    exact H h envPre rfl rfl
  intro ctx' e' ty' hd
  induction hd using RunWT.rec
    (motive_2 := fun ctx branch scrutTy resultTy _ =>
      ∀ pre : Env, ctx.env = pre ++ schemes ++ env → ctx.ctors = ctors →
        RunWTMatchBranch ⟨pre ++ env, ctx.ctors⟩
          (branch.1, branch.2.substN (pre.length + branch.1.bindCount) values)
          scrutTy resultTy) with
  | primLitUnit => intro _ _ _; exact .primLitUnit
  | primLitInt => intro _ _ _; exact .primLitInt
  | primLitNat => intro _ _ _; exact .primLitNat
  | primLitChar => intro _ _ _; exact .primLitChar
  | primBinOpIntAdd => intro _ _ _; exact .primBinOpIntAdd
  | primBinOpIntSub => intro _ _ _; exact .primBinOpIntSub
  | primBinOpIntLt _ _ ihtrue ihfalse =>
      intro pre hctx hctors
      exact .primBinOpIntLt (ihtrue pre hctx hctors) (ihfalse pre hctx hctors)
  | primBinOpCharLt _ _ ihtrue ihfalse =>
      intro pre hctx hctors
      exact .primBinOpCharLt (ihtrue pre hctx hctors) (ihfalse pre hctx hctors)
  | lambda hparam _ ihbody =>
      intro pre hctx hctors
      expose_names
      simp only [Expr.substN]
      have hb := ihbody (PolyTy.mkTrivial paramTy :: pre)
        (by simp only [hctx, List.cons_append, List.append_assoc]) hctors
      exact RunWT.lambda hparam (by
        simpa only [List.cons_append, List.length_cons] using hb)
  | app _ _ ihfn iharg =>
      intro pre hctx hctors
      simp only [Expr.substN]
      exact .app (ihfn pre hctx hctors) (iharg pre hctx hctors)
  | letIn hwf hgen _ ihgen ihbody =>
      intro pre hctx hctors
      expose_names
      simp only [Expr.substN]
      apply RunWT.letIn (scheme := scheme) (avoid := avoid) hwf
      · intro names hfresh
        exact ihgen names hfresh pre hctx hctors
      · have hb := ihbody (scheme :: pre)
          (by simp only [hctx, List.cons_append, List.append_assoc]) hctors
        simpa only [List.cons_append, List.length_cons] using hb
  | var hlookup hlc hinst =>
      intro pre hctx hctors
      expose_names
      rw [hctx] at hlookup
      rw [List.append_assoc] at hlookup
      simp only [Expr.substN]
      by_cases hlt : index < pre.length
      · rw [if_pos hlt]
        refine .var ?_ hlc hinst
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
          have hs : RunHasScheme ⟨env, ctors⟩ values[index - pre.length]
              schemes[index - pre.length] :=
            (List.forall₂_iff_get.mp hvalues).2 _ hin hschemeLt
          have hv := hs args _ hlc hinst
          rw [← hctors] at hv
          simpa only [List.nil_append] using
            (RunWT.weakenEnv (envPre := []) (envExtra := pre) hv)
        · rw [dif_neg hin]
          refine .var ?_ hlc hinst
          rw [List.getElem?_append_right (by omega : pre.length ≤ index - values.length)]
          rw [List.getElem?_append_right (by omega),
            List.getElem?_append_right (by omega : schemes.length ≤ index - pre.length)]
            at hlookup
          rw [show index - values.length - pre.length =
              index - pre.length - schemes.length by omega]
          exact hlookup
  | ctor hlookup hlc hinst =>
      intro _ _ _
      exact .ctor hlookup hlc hinst
  | match_ _ hne _ ihscrut ihbranches =>
      intro pre hctx hctors
      simp only [Expr.substN]
      refine .match_ (ihscrut pre hctx hctors) ?_ ?_
      · intro hnil
        obtain ⟨⟨p, b⟩, rest, hb⟩ := List.exists_cons_of_ne_nil hne
        have hm := BranchList.mem_substN_of_mem
          (k := pre.length) (vs := values)
          (hb ▸ List.mem_cons_self (a := (p, b)))
        rw [hnil] at hm
        exact List.not_mem_nil hm
      · intro branch' hm'
        obtain ⟨pat, body, hm, rfl⟩ := BranchList.mem_substN hm'
        exact ihbranches (pat, body) hm pre hctx hctors
  | @letRec bindings ctx body resultTy specs G avoid hwf hmono hpoly _
      ihmono ihpoly ihbody =>
      intro pre hctx hctors
      simp only [Expr.substN, RecGroup.substN_eq_map]
      have hwf' : RecSpecsWF
          (bindings.map
            (Expr.substN (pre.length + bindings.length) values))
          specs G :=
        { hwf with length := by simpa using hwf.length }
      have hann :
          (bindings.map
            (Expr.substN (pre.length + bindings.length) values)).map
              (fun _ => (none : Option PolyTy)) =
            bindings.map (fun _ => (none : Option PolyTy)) := by
        simp only [List.map_map, Function.comp_def]
      rw [← hann]
      apply RunWT.letRec (specs := specs) (G := G) (avoid := avoid) hwf'
      · intro Xs hXs pair hpair τ hτ
        rw [List.zip_map_left] at hpair
        obtain ⟨oldPair, holdPair, rfl⟩ := List.mem_map.mp hpair
        have ht := ihmono Xs hXs oldPair holdPair τ hτ
          (specs.map (RecSpec.bodyScheme G) ++ pre) (by
            simp only [RecSpecs.bodyCtx, hctx, List.append_assoc]) hctors
        simp only [RecSpecs.bodyCtx, List.length_append, List.length_map] at ht
        rw [← hwf.length, Nat.add_comm bindings.length pre.length] at ht
        simpa only [RecSpecs.bodyCtx, List.append_assoc] using ht
      · intro pair hpair scheme hscheme Ys hYs
        rw [List.zip_map_left] at hpair
        obtain ⟨oldPair, holdPair, rfl⟩ := List.mem_map.mp hpair
        have ht := ihpoly oldPair holdPair scheme hscheme Ys hYs
          (specs.map (RecSpec.bodyScheme G) ++ pre) (by
            simp only [RecSpecs.bodyCtx, hctx, List.append_assoc]) hctors
        simp only [RecSpecs.bodyCtx, List.length_append, List.length_map] at ht
        rw [← hwf.length, Nat.add_comm bindings.length pre.length] at ht
        simpa only [RecSpecs.bodyCtx, List.append_assoc] using ht
      · have hb := ihbody (specs.map (RecSpec.bodyScheme G) ++ pre) (by
          simp only [RecSpecs.bodyCtx, hctx, List.append_assoc]) hctors
        simp only [RecSpecs.bodyCtx, List.length_append, List.length_map] at hb
        rw [← hwf.length, Nat.add_comm bindings.length pre.length] at hb
        simpa only [RecSpecs.bodyCtx, List.append_assoc] using hb
  | mk hspec _ ihbody =>
      expose_names
      have hb := ihbody (instContents.map PolyTy.mkTrivial ++ pre) (by
        simp only [h_2, List.append_assoc]) h_3
      simp only [List.length_append, List.length_map] at hb
      have hlen : instContents.length = n := by
        have := List.Forall₂.length_eq hspec.fields
        simpa [hspec.bind_count] using this.symm
      rw [hlen, Nat.add_comm n pre.length] at hb
      exact RunWTMatchBranch.mk hspec (by
        simpa only [List.append_assoc] using hb)
  | wildcard _ ihbody =>
      expose_names
      simpa only [MatchPattern.bindCount, Nat.add_zero] using
        (RunWTMatchBranch.wildcard (ihbody pre h_2 h_3))


/-- Subject reduction for the recursive-group unfolding rule. Each RHS is
substituted as an erased self-wrapped value at its exported scheme. -/
theorem RunWT.letRecUnfold_preservation {ctx : Ctx}
    {anns : List (Option PolyTy)} {bindings : List Expr} {body : Expr}
    {ty : Ty}
    (h : RunWT ctx (.letRec anns bindings body) ty) :
    RunWT ctx
      (body.substN 0
        (bindings.map (fun rhs => .letRec anns bindings rhs))) ty := by
  cases h with
  | letRec hwf hmono hpoly hbody =>
      have hvalues := recursiveValuesHaveSchemes hwf hmono hpoly
      have hsubst := RunWT.substMany (envPre := []) hvalues hbody
      simpa [RecSpecs.bodyCtx, List.nil_append, RecSpec.bodyScheme] using hsubst

/-- One-step subject reduction for fully erased runtime terms. -/
theorem RunWT.preservation {ctx : Ctx} {e e' : Expr} {ty : Ty}
    (hstep : SmallStep.Step e e') (htyped : RunWT ctx e ty) :
    RunWT ctx e' ty := by
  induction hstep generalizing ty with
  | beta hval =>
      rename_i ann body v
      cases htyped with
      | app hfn harg =>
          cases hfn with
          | lambda hparam hbody =>
              have hvalues : List.Forall₂ (RunHasScheme ctx)
                  [v] [PolyTy.mkTrivial _] :=
                .cons (RunHasScheme.ofTrivial harg) .nil
              have hsubst := RunWT.substMany
                (envPre := []) (schemes := [PolyTy.mkTrivial _])
                (values := [v]) hvalues hbody
              simpa using hsubst
  | letReduce =>
      rename_i ann rhs body
      cases htyped with
      | letIn hwf hgen hbody =>
          expose_names
          have hvalues : List.Forall₂ (RunHasScheme ctx)
              [rhs] [scheme] :=
            .cons (RunHasScheme.ofGeneralisesTo hwf hgen) .nil
          have hsubst := RunWT.substMany
            (envPre := []) (schemes := [scheme]) (values := [rhs])
            hvalues hbody
          simpa using hsubst
  | deltaIntAdd =>
      cases htyped with
      | app hfn _ => cases hfn with
        | app hop _ => cases hop; exact .primLitInt
  | deltaIntSub =>
      cases htyped with
      | app hfn _ => cases hfn with
        | app hop _ => cases hop; exact .primLitInt
  | deltaIntLt =>
      cases htyped with
      | app hfn _ => cases hfn with
        | app hop _ => cases hop with
          | primBinOpIntLt htrue hfalse => split <;> assumption
  | deltaCharLt =>
      cases htyped with
      | app hfn _ => cases hfn with
        | app hop _ => cases hop with
          | primBinOpCharLt htrue hfalse => split <;> assumption
  | matchReduce hval hctor hfirst =>
      rename_i scrut branches name args pat body
      cases htyped with
      | match_ hscrut _ hbranches =>
          have hmem := hfirst.mem
          have hpeq := hfirst.ctor_eq
          cases pat with
          | wildcard =>
              cases hbranches (.wildcard, body) hmem with
              | wildcard hbody =>
                  have hsubst := RunWT.substMany
                    (envPre := []) (schemes := []) (values := [])
                    List.Forall₂.nil hbody
                  simpa [MatchPattern.bindCount] using hsubst
          | named c n =>
              simp only [MatchPattern.matchesCtor, Bool.and_eq_true,
                beq_iff_eq] at hpeq
              obtain ⟨hcname, hnlen⟩ := hpeq
              simp only [MatchPattern.bindCount]
              rw [hnlen, List.take_length]
              cases hbranches (.named c n, body) hmem with
              | @mk _ _ _ _ ctorB _ _ tyArgsB instContents hspecB hbodyB =>
                  have hlookB := hspecB.lookup
                  have hScrutB := hspecB.scrut_eq
                  have hpcB := hspecB.arity
                  have hinstB := hspecB.fields
                  rw [hScrutB] at hscrut
                  obtain ⟨ctorS, tyArgsS, consumedS, remainingS,
                    hlookS, htyargsS, hcontentsS, hforallS, hinstS⟩ :=
                    RunWT.ctor_applied_inversion hctor hscrut
                  rw [hcname] at hlookB
                  have hcc := Option.some.inj (hlookS.symm.trans hlookB)
                  cases hcc
                  rename_i ctorB
                  cases remainingS with
                  | cons field rest =>
                      simp only [Ty.wrapArrows] at hinstS
                      cases hinstS
                  | nil =>
                      rw [List.append_nil] at hcontentsS
                      subst hcontentsS
                      simp only [Ty.wrapArrows] at hinstS
                      cases hinstS with
                      | customTy hbvr =>
                          have hpc_len : tyArgsB.length = ctorB.paramCount := hpcB.symm
                          have hagree : ∀ k, k < ctorB.paramCount →
                              tyArgsB[k]? = tyArgsS[k]? := by
                            intro k hk
                            have hkt : k < tyArgsB.length := by omega
                            have hkr : k < (Ty.bvarRange ctorB.paramCount).length := by
                              rw [hbvr.length_eq]
                              exact hkt
                            have hrel := List.Forall₂.get hbvr hkr hkt
                            simp only [List.get_eq_getElem] at hrel
                            have helem : (Ty.bvarRange ctorB.paramCount)[k] =
                                Ty.bvar k := by
                              have h1 := Ty.bvarRange_getElem?
                                (n := ctorB.paramCount) (k := k) hk
                              rw [List.getElem?_eq_getElem hkr] at h1
                              exact Option.some.inj h1
                            rw [helem] at hrel
                            cases hrel with
                            | bvar hsome =>
                                rw [hsome]
                                exact List.getElem?_eq_getElem hkt
                          have hvalues := InstantiatesBy.build_run_match_values
                            hagree ctorB.bound hinstB hforallS
                          have hsubst := RunWT.substMany
                            (envPre := []) hvalues hbodyB
                          simpa using hsubst
  | matchWildReduce hval hnc =>
      rename_i scrut body rest
      cases htyped with
      | match_ _ _ hbranches =>
          cases hbranches (.wildcard, body) (List.mem_cons_self ..) with
          | wildcard hbody => exact hbody
  | appFn _ ih =>
      cases htyped with
      | app hfn harg => exact .app (ih hfn) harg
  | appArg hval _ ih =>
      cases htyped with
      | app hfn harg => exact .app hfn (ih harg)
  | matchScrut _ ih =>
      cases htyped with
      | match_ hscrut hne hbranches =>
          exact .match_ (ih hscrut) hne hbranches
  | letRecUnfold =>
      exact RunWT.letRecUnfold_preservation htyped


/-! ## Runtime progress -/

private lemma RunWT.ctor_chain_has_customTy_form
    {ctx e τ}
    (h_chain : SmallStep.IsCtorChain e) (h_ty : RunWT ctx e τ) :
    ∃ name args tys, τ = Ty.wrapArrows (.customTy name args) tys := by
  induction e using Expr.rec_strong generalizing ctx τ with
  | ctor _ =>
    cases h_ty with
    | ctor _ _ hinst =>
      have hform : ∀ {name : TyName} {tyArgs : List Ty} {args tys : List Ty} {τ' : Ty},
          InstantiatesBy tyArgs (Ty.wrapArrows (.customTy name args) tys) τ' →
          ∃ instArgs instTys, τ' = Ty.wrapArrows (.customTy name instArgs) instTys := by
        intro name tyArgs args tys τ'
        induction tys generalizing τ' with
        | nil => intro h; cases h with | customTy _ => exact ⟨_, [], rfl⟩
        | cons _ rest ih =>
          intro h
          cases h with
          | arrow _ h_rest =>
            expose_names
            obtain ⟨instArgs, instRest, h_eq⟩ := ih h_rest
            refine ⟨instArgs, instFst :: instRest, ?_⟩
            simp [Ty.wrapArrows, h_eq]
      obtain ⟨instArgs, instTys, h_eq⟩ := hform hinst
      exact ⟨_, instArgs, instTys, h_eq⟩
  | app _ _ ihf _ =>
    cases h_chain with
    | app h_chain' _ =>
      cases h_ty with
      | app h_f_ty _ =>
        obtain ⟨name, args, tys, h_eq⟩ := ihf h_chain' h_f_ty
        cases tys with
        | nil => simp [Ty.wrapArrows] at h_eq
        | cons _ rest =>
          simp only [Ty.wrapArrows] at h_eq
          injection h_eq with _ h_ret
          exact ⟨name, args, rest, h_ret⟩
  | primLit _      => cases h_chain
  | primBinOp _    => cases h_chain
  | lambda _ _ _   => cases h_chain
  | letIn _ _ _ _ _ => cases h_chain
  | var _          => cases h_chain
  | match_ _ _ _ _ => cases h_chain
  | letRec _ _ _ _ _ => cases h_chain

/-- A value of arrow type is a λ, a ctor chain, a bare primop, or a one-argument-
    short primop application. -/
theorem RunWT.canonical_arrow {ctx e argTy retTy}
    (h_ty : RunWT ctx e (.arrow argTy retTy))
    (h_val : SmallStep.IsValue e) :
    (∃ ann body, e = .lambda ann body) ∨ SmallStep.IsCtorChain e
    ∨ (∃ op, e = .primBinOp op) ∨ (∃ op v, e = .app (.primBinOp op) v) := by
  cases h_val with
  | primLit _ => cases h_ty
  | lambda ann body => exact .inl ⟨ann, body, rfl⟩
  | ctor name => exact .inr (.inl (.ctor name))
  | ctorApp h_chain h_v => exact .inr (.inl (.app h_chain h_v))
  -- a bare primop and a one-argument-short application are both arrow-typed values
  | primBinOp op => exact .inr (.inr (.inl ⟨op, rfl⟩))
  | primBinOpPartial hv => exact .inr (.inr (.inr ⟨_, _, rfl⟩))

/-- A value of a data type is a constructor chain. -/
theorem RunWT.canonical_customTy {ctx e tyName tyArgs}
    (h_ty : RunWT ctx e (.customTy tyName tyArgs))
    (h_val : SmallStep.IsValue e) :
    SmallStep.IsCtorChain e := by
  cases h_val with
  | primLit _ => cases h_ty
  | lambda _ _ => cases h_ty
  | ctor name => exact .ctor name
  | ctorApp h_chain h_v => exact .app h_chain h_v
  -- `primBinOp`/`primBinOpPartial` are arrow-typed, never `customTy` — the typing
  -- rule for `.primBinOp _` forces an arrow, contradicting `customTy`.
  | primBinOp op => cases h_ty
  | primBinOpPartial hv => cases h_ty with | app h_pbo _ => cases h_pbo

/-- A value of type `int` is an integer literal. -/
theorem RunWT.canonical_int {ctx e}
    (h_ty : RunWT ctx e (.prim .int))
    (h_val : SmallStep.IsValue e) :
    ∃ m : Int, e = .primLit (.int m) := by
  cases h_val with
  | primLit p => cases h_ty; exact ⟨_, rfl⟩
  | lambda _ _ => cases h_ty
  | ctor name =>
    obtain ⟨_, _, tys, h_eq⟩ :=
      RunWT.ctor_chain_has_customTy_form (.ctor name) h_ty
    cases tys <;> simp [Ty.wrapArrows] at h_eq
  | ctorApp h_chain h_v =>
    obtain ⟨_, _, tys, h_eq⟩ :=
      RunWT.ctor_chain_has_customTy_form (.app h_chain h_v) h_ty
    cases tys <;> simp [Ty.wrapArrows] at h_eq
  | primBinOp op => cases h_ty
  | primBinOpPartial hv => cases h_ty with | app h_pbo _ => cases h_pbo

/-- A value of type `char` is a character literal. -/
theorem RunWT.canonical_char {ctx e}
    (h_ty : RunWT ctx e (.prim .char))
    (h_val : SmallStep.IsValue e) :
    ∃ c : Char, e = .primLit (.char c) := by
  cases h_val with
  | primLit p => cases h_ty; exact ⟨_, rfl⟩
  | lambda _ _ => cases h_ty
  | ctor name =>
    obtain ⟨_, _, tys, h_eq⟩ :=
      RunWT.ctor_chain_has_customTy_form (.ctor name) h_ty
    cases tys <;> simp [Ty.wrapArrows] at h_eq
  | ctorApp h_chain h_v =>
    obtain ⟨_, _, tys, h_eq⟩ :=
      RunWT.ctor_chain_has_customTy_form (.app h_chain h_v) h_ty
    cases tys <;> simp [Ty.wrapArrows] at h_eq
  | primBinOp op => cases h_ty
  | primBinOpPartial hv => cases h_ty with | app h_pbo _ => cases h_pbo

/-- (helper) `Forall₂` distributes over appending one element to both sides. -/
private theorem forall₂_snoc_runtime {α β : Type _} {R : α → β → Prop}
    {l1 : List α} {l2 : List β} {a : α} {b : β}
    (h : List.Forall₂ R l1 l2) (hab : R a b) :
    List.Forall₂ R (l1 ++ [a]) (l2 ++ [b]) := by
  induction h with
  | nil => exact .cons hab .nil
  | cons hhd _ ih => exact .cons hhd ih

/-- A well-typed constructor chain decomposes into a head constructor applied to
    args, where the consumed fields are well-typed at their instantiations and
    the result type is the remaining fields wrapped over the (instantiated)
    `customTy`. -/
theorem RunWT.ctor_chain_inversion {ctx : Ctx} {e : Expr} {τ : Ty}
    (h_chain : SmallStep.IsCtorChain e) (h_ty : RunWT ctx e τ) :
    ∃ (name : CtorName) (args : List Expr) (ctor : Ctor)
      (tyArgs consumed remaining : List Ty),
      SmallStep.CtorAppliedTo e name args ∧
      LookupList.get? ctx.ctors name = some ctor ∧
      (∀ t ∈ tyArgs, ContainsBvarsUpTo 0 t) ∧
      ctor.contents = consumed ++ remaining ∧
      List.Forall₂ (fun a c => ∃ ct, InstantiatesBy tyArgs c ct ∧ RunWT ctx a ct)
        args consumed ∧
      InstantiatesBy tyArgs
        (Ty.wrapArrows (.customTy ctor.tyName (Ty.bvarRange ctor.paramCount)) remaining) τ := by
  induction e using Expr.rec_strong generalizing τ with
  | ctor name =>
    cases h_ty with
    | ctor hlook htyargs hinst =>
      exact ⟨name, [], _, _, [], _, .base name, hlook, htyargs, rfl, .nil,
        by simpa [Ctor.toTy] using hinst⟩
  | app f arg ihf _ =>
    cases h_chain with
    | app hchainf hvarg =>
      cases h_ty with
      | app hf harg =>
        obtain ⟨name, args, ctor, tyArgs, consumed, remaining, hcat, hlook, htyargs,
          hcontents, hforall, hinst_f⟩ := ihf hchainf hf
        cases remaining with
        | nil =>
          simp only [Ty.wrapArrows] at hinst_f
          cases hinst_f
        | cons c rest =>
          simp only [Ty.wrapArrows] at hinst_f
          cases hinst_f with
          | arrow hc hrest =>
            refine ⟨name, args ++ [arg], ctor, tyArgs, consumed ++ [c], rest,
              .step hcat, hlook, htyargs, ?_,
              forall₂_snoc_runtime hforall ⟨_, hc, harg⟩, hrest⟩
            rw [hcontents]
            exact (List.append_assoc consumed [c] rest).symm
  | primLit _ => cases h_chain
  | primBinOp _ => cases h_chain
  | lambda _ _ _ => cases h_chain
  | letIn _ _ _ _ _ => cases h_chain
  | var _ => cases h_chain
  | match_ _ _ _ _ => cases h_chain
  | letRec _ _ _ _ _ => cases h_chain

/-- Progress: a closed, well-typed term is a value or takes a step. -/
theorem RunWT.progress {ctx : Ctx} {e : Expr} {τ : Ty}
    (h_ty : RunWT ctx e τ) (h_closed : ctx.env = [])
    (h_exh : SmallStep.AllMatchesExhaustive ctx.ctors e) (h_erased : e.erase = e) :
    SmallStep.IsValue e ∨ ∃ e', SmallStep.Step e e' := by
  open SmallStep in
  suffices H : ∀ (n : Nat) (e : Expr), e.size ≤ n → ∀ (ctx : Ctx) (τ : Ty),
      RunWT ctx e τ → ctx.env = [] → AllMatchesExhaustive ctx.ctors e →
      e.erase = e → IsValue e ∨ ∃ e', Step e e' by
    exact H e.size e (Nat.le_refl _) ctx τ h_ty h_closed h_exh h_erased
  intro n
  induction n with
  | zero => intro e he; exact absurd he (Nat.not_le.mpr (Expr.size_pos e))
  | succ n ih =>
    intro e hsize ctx τ h_ty h_closed h_exh h_erased
    cases h_ty with
    | primLitUnit => exact .inl (.primLit _)
    | primLitInt => exact .inl (.primLit _)
    | primLitNat => exact .inl (.primLit _)
    | primLitChar => exact .inl (.primLit _)
    | primBinOpIntAdd => exact .inl (.primBinOp _)
    | primBinOpIntSub => exact .inl (.primBinOp _)
    | primBinOpIntLt _ _ => exact .inl (.primBinOp _)
    | primBinOpCharLt _ _ => exact .inl (.primBinOp _)
    | ctor _ _ _ => exact .inl (.ctor _)
    | lambda _ _ => exact .inl (.lambda _ _)
    | var h_lookup _ _ => rw [h_closed] at h_lookup; simp at h_lookup
    | @app _ f _ _ arg h_f h_arg =>
      cases h_exh with
      | app h_exh_f h_exh_arg =>
        simp only [Expr.size] at hsize
        have herased : f.erase = f ∧ arg.erase = arg := by
          simpa [Expr.erase_app] using h_erased
        rcases ih f (by omega) ctx _ h_f h_closed h_exh_f herased.1 with hvf | ⟨f', hf⟩
        · rcases ih arg (by omega) ctx _ h_arg h_closed h_exh_arg herased.2 with hva | ⟨arg', harg⟩
          · rcases RunWT.canonical_arrow h_f hvf with
                ⟨ann, body, rfl⟩ | hchain | ⟨op, rfl⟩ | ⟨op, v, rfl⟩
            · exact .inr ⟨_, .beta hva⟩
            · exact .inl (.ctorApp hchain hva)
            · -- `f` is a bare primop; applying one value leaves it one arg short → a value
              exact .inl (.primBinOpPartial hva)
            · -- `f` is a partial primop; this application saturates it → δ-step.
              -- Both operands are values of type `int`, hence literals (canonical_int).
              cases hvf with
              | ctorApp hchain _ => nomatch hchain
              | primBinOpPartial hv =>
                cases h_f with
                | app h_pbo h_v =>
                  cases h_pbo with
                  | primBinOpIntAdd =>
                    obtain ⟨m, rfl⟩ := RunWT.canonical_int h_v hv
                    obtain ⟨n, rfl⟩ := RunWT.canonical_int h_arg hva
                    exact .inr ⟨_, .deltaIntAdd⟩
                  | primBinOpIntSub =>
                    obtain ⟨m, rfl⟩ := RunWT.canonical_int h_v hv
                    obtain ⟨n, rfl⟩ := RunWT.canonical_int h_arg hva
                    exact .inr ⟨_, .deltaIntSub⟩
                  | primBinOpIntLt _ _ =>
                    obtain ⟨m, rfl⟩ := RunWT.canonical_int h_v hv
                    obtain ⟨n, rfl⟩ := RunWT.canonical_int h_arg hva
                    exact .inr ⟨_, .deltaIntLt⟩
                  | primBinOpCharLt _ _ =>
                    obtain ⟨a, rfl⟩ := RunWT.canonical_char h_v hv
                    obtain ⟨b, rfl⟩ := RunWT.canonical_char h_arg hva
                    exact .inr ⟨_, .deltaCharLt⟩
          · exact .inr ⟨_, .appArg hvf harg⟩
        · exact .inr ⟨_, .appFn hf⟩
    | letIn _ _ _ =>
      -- call-by-name: a `let` always steps via `letReduce` (no rhs reduction).
      exact .inr ⟨_, .letReduce⟩
    | @match_ _ scrut scrutTy branches resultTy h_scrut h_ne h_brs =>
      cases h_exh with
      | match_ h_exh_scrut _ h_branch_ty h_match_exh =>
        simp only [Expr.size] at hsize
        have herased : scrut.erase = scrut := by
          have hboth : scrut.erase = scrut ∧
              (branches.map fun pe => (pe.1, pe.2.erase)) = branches := by
            simpa [Expr.erase_match] using h_erased
          exact hboth.1
        rcases ih scrut (by omega) ctx _ h_scrut h_closed h_exh_scrut herased with hvs | ⟨scrut', hscrut⟩
        · obtain ⟨⟨pat0, body0⟩, rest0, hbeq⟩ := List.exists_cons_of_ne_nil h_ne
          have hb0 : (pat0, body0) ∈ branches := by rw [hbeq]; exact List.mem_cons_self
          by_cases hchain : IsCtorChain scrut
          · rcases (Expr.rec_strong
                (motive := fun e => IsCtorChain e → ∃ name args, CtorAppliedTo e name args)
                (fun _ h => by cases h)
                (fun _ h => by cases h)
                (fun _ _ _ => by intro h; cases h)
                (fun f v ihf _ => by
                  intro h
                  cases h with
                  | app hf _ =>
                    obtain ⟨name, args, hca⟩ := ihf hf
                    exact ⟨name, args ++ [v], .step hca⟩)
                (fun _ _ _ _ _ => by intro h; cases h)
                (fun _ => by intro h; cases h)
                (fun nm => by
                  intro h
                  cases h
                  exact ⟨nm, [], .base nm⟩)
                (fun _ _ _ _ => by intro h; cases h)
                (fun _ _ _ _ _ => by intro h; cases h)
                scrut hchain) with ⟨name, args, hcat⟩
            have hcover : ∃ pat body, (pat, body) ∈ branches ∧
                pat.matchesCtor name args.length = true := by
              cases pat0 with
              | wildcard => exact ⟨.wildcard, body0, hb0, rfl⟩
              | named c0 n0 =>
                cases h_brs (.named c0 n0, body0) hb0 with
                | mk hspec0 _ =>
                  obtain ⟨name', args', ctor, tyArgs', consumed, remaining,
                    hcat', hlook, _, hcontents, hforall, hinst⟩ :=
                    RunWT.ctor_chain_inversion hchain h_scrut
                  obtain ⟨rfl, rfl⟩ : name = name' ∧ args = args' := by
                    exact CtorAppliedTo.det hcat hcat'
                  cases remaining with
                  | cons d rest =>
                    simp only [Ty.wrapArrows] at hinst
                    rw [hspec0.scrut_eq] at hinst; cases hinst
                  | nil =>
                    simp only [Ty.wrapArrows] at hinst
                    rw [List.append_nil] at hcontents
                    have hlen : args.length = ctor.contents.length := by
                      rw [hcontents]; exact hforall.length_eq
                    obtain ⟨ctorB, hlookB, htyB⟩ := h_branch_ty c0 n0 body0 hb0
                    cases hinst with
                    | customTy _ =>
                      obtain ⟨pat, body, hmem, hcov⟩ := h_match_exh name ctor hlook (by
                        injection hspec0.scrut_eq with hn _
                        rw [hn, Option.some.inj (hspec0.lookup.symm.trans hlookB)]; exact htyB)
                      exact ⟨pat, body, hmem, by rw [hlen]; exact hcov⟩
            obtain ⟨pat, body, hmem, hcov⟩ := hcover
            obtain ⟨e', hfmb⟩ := findMatchingBranch_of_exists ⟨pat, body, hmem, hcov⟩
            rcases (List.rec
              (motive := fun l => findMatchingBranch name args l = some e' →
                  ∃ pat body, FirstMatchingBranch name args.length l pat body ∧
                    e' = body.substN 0 (args.take pat.bindCount))
              (fun h => by simp [findMatchingBranch] at h)
              (fun hd tl ih => by
                obtain ⟨pat, body⟩ := hd
                intro h
                simp only [findMatchingBranch] at h
                split at h
                · rename_i hm
                  simp at h
                  exact ⟨pat, body, .here hm, h.symm⟩
                · rename_i hnm
                  obtain ⟨p, b, hfirst, heq⟩ := ih h
                  exact ⟨p, b, .there ((Bool.not_eq_true _).mp hnm) hfirst, heq⟩)
              branches hfmb) with ⟨pat', body', hfirst, _⟩
            exact .inr ⟨_, .matchReduce hvs hcat hfirst⟩
          · have hwild : pat0 = .wildcard := by
              cases pat0 with
              | wildcard => rfl
              | named c0 n0 =>
                cases h_brs (.named c0 n0, body0) hb0 with
                | mk hspecA _ =>
                  exact absurd (RunWT.canonical_customTy (hspecA.scrut_eq ▸ h_scrut) hvs) hchain
            subst hwild
            rw [hbeq]
            exact .inr ⟨body0, .matchWildReduce hvs hchain⟩
        · exact .inr ⟨_, .matchScrut hscrut⟩
    | letRec _ _ _ _ => exact .inr ⟨_, .letRecUnfold⟩

/-! ## A real-Core erased polymorphic-recursion witness -/

def polyId : PolyTy := ⟨1, .arrow (.bvar 0) (.bvar 0)⟩

/-- `fun x => (fun _ => x) (self 0)`: the current call is at a rigid `a`,
while the recursive occurrence is independently instantiated at `Int`. -/
def polySelfRhs : Expr :=
  .lambda none
    (.app (.lambda none (.var 1)) (.app (.var 1) (.primLit (.int 0))))

def polySelfBindings : List Expr := [polySelfRhs]

theorem polyId_wf : polyId.WF := by
  show ContainsBvarsUpTo 1 (.arrow (.bvar 0) (.bvar 0))
  exact .arrow (.bvar (by omega)) (.bvar (by omega))

theorem polySelf_specs_wf :
    RecSpecsWF polySelfBindings [.poly polyId] [] := by
  refine ⟨by simp [polySelfBindings], by simp, ?_, ?_⟩
  · intro ty hty
    simp at hty
  · intro scheme hscheme
    simp only [List.mem_singleton, RecSpec.poly.injEq] at hscheme
    subst scheme
    exact polyId_wf

theorem polySelf_mono :
    MonoTyped RunWT ⟨[], []⟩ polySelfBindings [.poly polyId] [] [] := by
  intro Xs hXs pair hpair ty hmono
  have hXsNil : Xs = [] := List.length_eq_zero_iff.mp hXs.length
  subst Xs
  simp [polySelfBindings] at hpair
  subst pair
  simp at hmono

private theorem singleton_of_fresh_one {avoid names : List Nat}
    (h : FreshNames avoid 1 names) : ∃ name, names = [name] := by
  exact List.length_eq_one_iff.mp h.length

theorem polySelf_poly :
    PolyTyped RunWT ⟨[], []⟩ polySelfBindings [.poly polyId] [] [] := by
  intro pair hpair scheme hscheme Ys hYs
  simp [polySelfBindings] at hpair
  subst pair
  simp only [RecSpec.poly.injEq] at hscheme
  subst scheme
  obtain ⟨Y, rfl⟩ := singleton_of_fresh_one hYs
  change RunWT ⟨[polyId], []⟩ polySelfRhs
    (.arrow (.fvar Y) (.fvar Y))
  apply RunWT.lambda .fvar
  apply RunWT.app (argTy := .prim .int)
  · apply RunWT.lambda .prim
    exact RunWT.var (index := 1) (scheme := PolyTy.mkTrivial (.fvar Y))
      (args := []) rfl (by simp) .fvar
  · apply RunWT.app (argTy := .prim .int)
    · exact RunWT.var (index := 1) (scheme := polyId)
        (args := [.prim .int]) rfl (by simp; exact .prim)
        (.arrow (.bvar rfl) (.bvar rfl))
    · exact .primLitInt

theorem polySelf_body :
    RunWT (RecSpecs.bodyCtx ⟨[], []⟩ [.poly polyId] [])
      (.var 0) (.arrow (.prim .unit) (.prim .unit)) := by
  exact RunWT.var (index := 0) (scheme := polyId)
    (args := [.prim .unit]) rfl (by simp; exact .prim)
    (.arrow (.bvar rfl) (.bvar rfl))

/-- The annotated source accepts the same independently instantiated recursive
call. Its complete annotation is checked before the machine sees the term. -/
theorem annotated_polySelf_typed :
    TypeOfHM ⟨[], []⟩ (.letRec [some polyId] polySelfBindings (.var 0))
      (.arrow (.prim .unit) (.prim .unit)) := by
  refine TypeOfHM.letRec (specs := [.poly polyId]) (groups := [])
    (G := []) (L := []) ?_ ⟨rfl, rfl, by simp, ?_, ?_⟩ ?_ ?_ rfl ?_
  · refine ⟨by simp [polySelfBindings], ?_, ?_, ?_, ?_, ?_⟩
    · intro component hcomponent
      simp at hcomponent
    · simp
    · intro member hmember
      simp at hmember
    · intro member hbound
      have hzero : member = 0 := by
        simp [polySelfBindings] at hbound
        omega
      subst member
      simp [RecGroups.UnsignedAt]
    · intro stage dependencyStage component dependencyComponent source target rhs
        hstage _ _ _ _ _
      simp at hstage
  · intro ty hty
    simp at hty
  · intro scheme hscheme
    simp only [List.mem_singleton, RecSpec.poly.injEq] at hscheme
    subst scheme
    exact polyId_wf
  · intro stage component hstage
    simp at hstage
  · intro pair hpair scheme hscheme Ys hYs
    simp [polySelfBindings] at hpair
    subst pair
    simp only [RecSpec.poly.injEq] at hscheme
    subst scheme
    obtain ⟨Y, rfl⟩ := singleton_of_fresh_one hYs
    change TypeOfHM ⟨[polyId], []⟩ polySelfRhs
      (.arrow (.fvar Y) (.fvar Y))
    apply TypeOfHM.lambda .fvar (by simp [Option.Pins]) rfl
    apply TypeOfHM.app (argTy := .prim .int)
    · apply TypeOfHM.lambda .prim (by simp [Option.Pins]) rfl
      exact TypeOfHM.var (dbl := 1) (polyTy := PolyTy.mkTrivial (.fvar Y))
        (instArgs := []) rfl (by simp) .fvar
    · apply TypeOfHM.app (argTy := .prim .int)
      · exact TypeOfHM.var (dbl := 1) (polyTy := polyId)
          (instArgs := [.prim .int]) rfl (by simp; exact .prim)
          (.arrow (.bvar rfl) (.bvar rfl))
      · exact .primLitInt
  · exact TypeOfHM.var (dbl := 0) (polyTy := polyId)
      (instArgs := [.prim .unit]) rfl (by simp; exact .prim)
      (.arrow (.bvar rfl) (.bvar rfl))

/-- No scheme or type application occurs anywhere in this runtime expression. -/
theorem erased_polySelf_typed :
    RunWT ⟨[], []⟩
      (.letRec (polySelfBindings.map (fun _ => none))
        polySelfBindings (.var 0))
      (.arrow (.prim .unit) (.prim .unit)) := by
  simpa [Expr.erase, polySelfBindings, polySelfRhs] using
    TypeOfHM.erase_preserves_typing annotated_polySelf_typed

theorem erased_polySelf_steps :
    SmallStep.Step
      (.letRec (polySelfBindings.map (fun _ => none))
        polySelfBindings (.var 0))
      ((Expr.var 0).substN 0
        (polySelfBindings.map (fun rhs =>
          .letRec (polySelfBindings.map (fun _ => none))
            polySelfBindings rhs))) := by
  exact .letRecUnfold

theorem erased_polySelf_unfolded_typed :
    RunWT ⟨[], []⟩
      ((Expr.var 0).substN 0
        (polySelfBindings.map (fun rhs =>
          .letRec (polySelfBindings.map (fun _ => none))
            polySelfBindings rhs)))
      (.arrow (.prim .unit) (.prim .unit)) := by
  exact RunWT.letRecUnfold_preservation erased_polySelf_typed

#print axioms RunWT.substFvar
#print axioms TypeOfHM.erase_preserves_typing
#print axioms RunWT.substMany
#print axioms RunWT.letRecUnfold_preservation
#print axioms RunWT.preservation
#print axioms RunWT.progress
#print axioms annotated_polySelf_typed
#print axioms erased_polySelf_typed
#print axioms erased_polySelf_unfolded_typed

end RuntimeTyping
