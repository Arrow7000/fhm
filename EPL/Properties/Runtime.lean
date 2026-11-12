import EPL.Runtime

namespace EPL

private theorem erase_openRigidsFrom (expr : Source) :
    (expr.openRigidsFrom depth base count).erase = expr.erase := by
  induction expr generalizing depth with
  | primLit => rfl
  | primOp => rfl
  | var => rfl
  | lambda ann body ih =>
      simp only [Expr.openRigidsFrom, Expr.erase, ih]
  | app function argument functionIH argumentIH =>
      simp only [Expr.openRigidsFrom, Expr.erase, functionIH, argumentIH]
  | letIn ann rhs body rhsIH bodyIH =>
      simp only [Expr.openRigidsFrom, Expr.erase, rhsIH, bodyIH]
  | fix ann body ih =>
      simp only [Expr.openRigidsFrom, Expr.erase, ih]

/-- Opening source type annotations has no runtime effect. -/
theorem erase_openRigids (expr : Source) :
    (expr.openRigids base count).erase = expr.erase := by
  exact erase_openRigidsFrom expr

namespace Typing

/-- Erasing Core-native partial annotations preserves the assigned type. -/
theorem erase (typing : Typing rigidCount ctx expr ty) :
    RuntimeTyping rigidCount ctx expr.erase ty := by
  induction typing with
  | primLit => exact .primLit
  | primOp => exact .primOp
  | var hlookup hwf hlen hargs =>
      exact .var hlookup hwf hlen hargs
  | lambda paramWF _ _ bodyErased =>
      exact .lambda paramWF bodyErased
  | app _ _ functionErased argumentErased =>
      exact .app functionErased argumentErased
  | letMono rhsWF _ _ rhsErased bodyErased =>
      exact .letMono rhsWF rhsErased bodyErased
  | letPoly _ schemeWF ctxWF _ _ _ rhsErased bodyErased =>
      apply RuntimeTyping.letPoly schemeWF ctxWF
      · simpa only [erase_openRigids] using rhsErased
      · exact bodyErased
  | fix selfWF _ _ bodyErased =>
      exact .fix selfWF bodyErased

end Typing
end EPL

namespace EPL
namespace RuntimeTyping

private theorem scoped_openWith
    {ty : Ty} {rigidCount binderCount : Nat} {args : List Ty}
    (hscoped : ty.Scoped rigidCount binderCount)
    (hlen : args.length = binderCount)
    (hargs : ∀ arg ∈ args, arg.Scoped rigidCount 0) :
    (ty.openWith args).Scoped rigidCount 0 := by
  induction ty generalizing binderCount with
  | prim p => exact .prim
  | arrow domain codomain ihDomain ihCodomain =>
      cases hscoped with
      | arrow domainScoped codomainScoped =>
          exact .arrow (ihDomain domainScoped hlen)
            (ihCodomain codomainScoped hlen)
  | bvar index =>
      cases hscoped with
      | bvar hindex =>
          have hindex' : index < args.length := by simpa [hlen] using hindex
          have hget : args[index]? = some args[index] :=
            List.getElem?_eq_getElem hindex'
          simp only [Ty.openWith, hget, Option.getD_some]
          exact hargs args[index] (List.getElem_mem hindex')
  | rigid level =>
      cases hscoped with
      | rigid hlevel => exact .rigid hlevel
  | mvar id => exact .mvar id

private theorem metaFree_openWith
    {ty : Ty} {args : List Ty}
    (free : ty.MetaFree)
    (hargs : ∀ arg ∈ args, arg.MetaFree) :
    (ty.openWith args).MetaFree := by
  induction ty with
  | prim p => exact .prim
  | arrow domain codomain ihDomain ihCodomain =>
      cases free with
      | arrow domainFree codomainFree =>
          exact .arrow (ihDomain domainFree) (ihCodomain codomainFree)
  | bvar index =>
      simp only [Ty.openWith]
      cases hget : args[index]? with
      | none => exact .bvar
      | some arg => exact hargs arg (List.mem_of_getElem? hget)
  | rigid level => exact .rigid
  | mvar id => cases free

private theorem wf_openWith
    {ty : Ty} {rigidCount binderCount : Nat} {args : List Ty}
    (wf : ty.WF rigidCount binderCount)
    (hlen : args.length = binderCount)
    (hargs : ∀ arg ∈ args, arg.WF rigidCount 0) :
    (ty.openWith args).WF rigidCount 0 := by
  exact ⟨scoped_openWith wf.1 hlen (fun arg harg => (hargs arg harg).1),
    metaFree_openWith wf.2 (fun arg harg => (hargs arg harg).2)⟩

/-- Runtime typing also assigns only scoped, meta-free semantic types. -/
theorem regular (typing : RuntimeTyping rigidCount ctx expr ty) :
    ty.WF rigidCount 0 := by
  induction typing with
  | primLit => cases_type PrimLit <;> exact ⟨.prim, .prim⟩
  | primOp =>
      cases_type PrimOp
      exact ⟨.arrow .prim (.arrow .prim .prim),
        .arrow .prim (.arrow .prim .prim)⟩
  | var _ wf hlen hargs => exact wf_openWith wf hlen hargs
  | lambda paramWF _ bodyRegular =>
      exact ⟨.arrow paramWF.1 bodyRegular.1,
        .arrow paramWF.2 bodyRegular.2⟩
  | app _ _ functionRegular _ =>
      rcases functionRegular with ⟨functionScoped, functionFree⟩
      cases functionScoped with
      | arrow _ resultScoped =>
          cases functionFree with
          | arrow _ resultFree => exact ⟨resultScoped, resultFree⟩
  | letMono => assumption
  | letPoly => assumption
  | fix => assumption

end RuntimeTyping
end EPL

namespace EPL
namespace RuntimeTyping

private def shiftLevel (cutoff delta level : Nat) : Nat :=
  if cutoff ≤ level then level + delta else level

private def shiftTy (cutoff delta : Nat) : Ty → Ty
  | .prim p => .prim p
  | .arrow a b => .arrow (shiftTy cutoff delta a) (shiftTy cutoff delta b)
  | .bvar i => .bvar i
  | .rigid i => .rigid (shiftLevel cutoff delta i)
  | .mvar i => .mvar i

private def shiftScheme (cutoff delta : Nat) (scheme : PolyTy) : PolyTy :=
  ⟨scheme.paramCount, shiftTy cutoff delta scheme.body⟩

private def shiftCtx (cutoff delta : Nat) (ctx : Ctx) : Ctx :=
  ctx.map (shiftScheme cutoff delta)

private theorem scoped_monoRigids {ty : Ty}
    (h : Ty.Scoped rigidCount binderCount ty) (hle : rigidCount ≤ larger) :
    Ty.Scoped larger binderCount ty := by
  induction h with
  | prim => exact .prim
  | arrow _ _ iha ihb => exact .arrow iha ihb
  | bvar hi => exact .bvar hi
  | rigid hi => exact .rigid (Nat.lt_of_lt_of_le hi hle)
  | mvar id => exact .mvar id

private theorem wf_monoRigids {ty : Ty}
    (h : Ty.WF rigidCount binderCount ty) (hle : rigidCount ≤ larger) :
    Ty.WF larger binderCount ty :=
  ⟨scoped_monoRigids h.1 hle, h.2⟩

private theorem schemeWF_monoRigids {scheme : PolyTy}
    (h : PolyTy.WF rigidCount scheme) (hle : rigidCount ≤ larger) :
    PolyTy.WF larger scheme :=
  wf_monoRigids h hle

private theorem ctxWF_monoRigids {ctx : Ctx}
    (h : Ctx.WF rigidCount ctx) (hle : rigidCount ≤ larger) :
    Ctx.WF larger ctx := by
  intro scheme hs
  exact schemeWF_monoRigids (h scheme hs) hle

private theorem shiftTy_eq_self {ty : Ty} (h : Ty.Scoped cutoff binderCount ty) :
    shiftTy cutoff delta ty = ty := by
  induction h with
  | prim => rfl
  | arrow _ _ iha ihb => simp [shiftTy, iha, ihb]
  | bvar => rfl
  | rigid hi => simp [shiftTy, shiftLevel, Nat.not_le.mpr hi]
  | mvar => rfl

private theorem shiftScheme_eq_self {scheme : PolyTy} (h : PolyTy.WF cutoff scheme) :
    shiftScheme cutoff delta scheme = scheme := by
  cases scheme with
  | mk count body =>
      simp only [shiftScheme, Scheme.mk.injEq, true_and]
      exact shiftTy_eq_self h.1

private theorem shiftCtx_eq_self {ctx : Ctx} (h : Ctx.WF cutoff ctx) :
    shiftCtx cutoff delta ctx = ctx := by
  induction ctx with
  | nil => rfl
  | cons scheme tail ih =>
      have hs : scheme.WF cutoff := h scheme (by simp)
      have ht : Ctx.WF cutoff tail := by
        intro item hi
        exact h item (by simp [hi])
      change shiftScheme cutoff delta scheme :: shiftCtx cutoff delta tail = scheme :: tail
      rw [shiftScheme_eq_self hs, ih ht]

private theorem shiftTy_scoped {ty : Ty}
    (h : Ty.Scoped rigidCount binderCount ty) :
    Ty.Scoped (rigidCount + delta) binderCount (shiftTy cutoff delta ty) := by
  induction h with
  | prim => exact .prim
  | arrow _ _ iha ihb => exact .arrow iha ihb
  | bvar hi => exact .bvar hi
  | rigid hi =>
      simp only [shiftTy]
      unfold shiftLevel
      split
      · exact .rigid (by omega)
      · exact .rigid (by omega)
  | mvar id => exact .mvar id

private theorem shiftTy_metaFree (h : Ty.MetaFree ty) :
    Ty.MetaFree (shiftTy cutoff delta ty) := by
  induction h with
  | prim => exact .prim
  | arrow _ _ iha ihb => exact .arrow iha ihb
  | bvar => exact .bvar
  | rigid => exact .rigid

private theorem shiftTy_wf {ty : Ty}
    (h : Ty.WF rigidCount binderCount ty) :
    Ty.WF (rigidCount + delta) binderCount (shiftTy cutoff delta ty) :=
  ⟨shiftTy_scoped h.1, shiftTy_metaFree h.2⟩

private theorem shiftScheme_wf {scheme : PolyTy}
    (h : PolyTy.WF rigidCount scheme) :
    PolyTy.WF (rigidCount + delta) (shiftScheme cutoff delta scheme) :=
  shiftTy_wf h

private theorem shiftCtx_wf {ctx : Ctx} (h : Ctx.WF rigidCount ctx) :
    Ctx.WF (rigidCount + delta) (shiftCtx cutoff delta ctx) := by
  intro scheme hmem
  rcases List.mem_map.mp hmem with ⟨original, horiginal, rfl⟩
  exact shiftScheme_wf (h original horiginal)

private theorem shiftTy_openWith (ty : Ty) (args : List Ty) :
    shiftTy cutoff delta (ty.openWith args) =
      (shiftTy cutoff delta ty).openWith (args.map (shiftTy cutoff delta)) := by
  induction ty with
  | prim => rfl
  | arrow a b iha ihb => simp [Ty.openWith, shiftTy, iha, ihb]
  | bvar index =>
      simp only [Ty.openWith, shiftTy, List.getElem?_map]
      cases args[index]? <;> simp [shiftTy]
  | rigid => rfl
  | mvar => rfl

private theorem shiftRigidBlock (hcut : cutoff ≤ base) :
    (rigidBlock base count).map (shiftTy cutoff delta) =
      rigidBlock (base + delta) count := by
  unfold rigidBlock
  rw [List.map_map]
  apply List.map_congr_left
  intro offset _
  simp only [Function.comp_apply, shiftTy]
  unfold shiftLevel
  rw [if_pos (by omega)]
  congr 1
  omega

private theorem shiftScheme_openRigids (scheme : PolyTy)
    (hcut : cutoff ≤ base) :
    shiftTy cutoff delta (scheme.openRigids base) =
      (shiftScheme cutoff delta scheme).openRigids (base + delta) := by
  simp only [PolyTy.openRigids, PolyTy.openWith, shiftScheme]
  rw [shiftTy_openWith, shiftRigidBlock hcut]

private theorem shiftTyping (typing : RuntimeTyping rigidCount ctx expr ty)
    (hcut : cutoff ≤ rigidCount) :
    RuntimeTyping (rigidCount + delta) (shiftCtx cutoff delta ctx)
      expr (shiftTy cutoff delta ty) := by
  induction typing with
  | primLit =>
      rename_i literal
      cases literal <;> exact .primLit
  | primOp =>
      rename_i op
      cases op
      exact .primOp
  | var hlookup hwf hlen hargs =>
      clear rigidCount ctx expr ty
      rename_i localCtx index scheme args localRigid
      let shiftedArgs := args.map (shiftTy cutoff delta)
      have hlookup' :
          (shiftCtx cutoff delta localCtx)[index]? =
            some (shiftScheme cutoff delta scheme) := by
        simpa [shiftCtx] using congrArg (Option.map (shiftScheme cutoff delta)) hlookup
      have hargs' : ∀ arg ∈ shiftedArgs,
          arg.WF (localRigid + delta) 0 := by
        intro arg harg
        rcases List.mem_map.mp harg with ⟨original, horiginal, rfl⟩
        exact shiftTy_wf (hargs original horiginal)
      have hopen := shiftTy_openWith (cutoff := cutoff) (delta := delta)
        scheme.body args
      simpa [shiftScheme, PolyTy.openWith, shiftedArgs, hopen] using
        (RuntimeTyping.var hlookup' (shiftScheme_wf hwf)
          (by simpa [shiftedArgs] using hlen) hargs')
  | lambda hwf _ ih =>
      simpa [shiftCtx, shiftScheme, PolyTy.mono, shiftTy] using
        (RuntimeTyping.lambda (shiftTy_wf hwf) (ih hcut))
  | app _ _ ihf iha =>
      simpa [shiftTy] using RuntimeTyping.app (ihf hcut) (iha hcut)
  | letMono hwf _ _ ihr ihb =>
      simpa [shiftCtx, shiftScheme, PolyTy.mono] using
        (RuntimeTyping.letMono (shiftTy_wf hwf) (ihr hcut) (ihb hcut))
  | letPoly hwf hctx _ _ ihr ihb =>
      clear rigidCount ctx expr ty
      have hRhs := ihr (by omega)
      rw [shiftScheme_openRigids _ hcut] at hRhs
      simpa [shiftCtx, shiftScheme] using
        (RuntimeTyping.letPoly (shiftScheme_wf hwf)
          (shiftCtx_wf hctx)
          (by simpa [shiftScheme, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hRhs)
          (ihb hcut))
  | fix hwf _ ih =>
      simpa [shiftCtx, shiftScheme, PolyTy.mono] using
        (RuntimeTyping.fix (shiftTy_wf hwf) (ih hcut))

private theorem rebaseExplicit
    (hctx : Ctx.WF rigidCount ctx)
    (hscheme : PolyTy.WF rigidCount scheme)
    (htyping : RuntimeTyping (rigidCount + scheme.paramCount) ctx rhs
      (scheme.openRigids rigidCount))
    (hle : rigidCount ≤ larger) :
    RuntimeTyping (larger + scheme.paramCount) ctx rhs
      (scheme.openRigids larger) := by
  let delta := larger - rigidCount
  have hshift := shiftTyping (cutoff := rigidCount) (delta := delta)
    htyping (by omega)
  have hctxId : shiftCtx rigidCount delta ctx = ctx := shiftCtx_eq_self hctx
  have hschemeId : shiftScheme rigidCount delta scheme = scheme :=
    shiftScheme_eq_self hscheme
  rw [hctxId, shiftScheme_openRigids _ (by omega), hschemeId] at hshift
  have hbase : rigidCount + delta = larger := by
    dsimp [delta]
    omega
  have hboundary : rigidCount + scheme.paramCount + delta =
      larger + scheme.paramCount := by
    dsimp [delta]
    omega
  rw [hboundary, hbase] at hshift
  exact hshift

/-- Runtime typing is stable when unrelated rigid levels are added to scope.
Explicit-polymorphic lets rebase their deterministic generic block. -/
theorem weakenRigids
    (typing : RuntimeTyping rigidCount ctx expr ty)
    (hscope : rigidCount ≤ larger) :
    RuntimeTyping larger ctx expr ty := by
  induction typing generalizing larger with
  | primLit => exact .primLit
  | primOp => exact .primOp
  | var hlookup hwf hlen hargs =>
      exact .var hlookup (schemeWF_monoRigids hwf hscope) hlen
        (fun arg harg => wf_monoRigids (hargs arg harg) hscope)
  | lambda hwf _ ih =>
      exact .lambda (wf_monoRigids hwf hscope) (ih hscope)
  | app _ _ ihf iha => exact .app (ihf hscope) (iha hscope)
  | letMono hwf _ _ ihr ihb =>
      exact .letMono (wf_monoRigids hwf hscope) (ihr hscope) (ihb hscope)
  | letPoly hwf hctx hrhs _ _ ihb =>
      exact .letPoly (schemeWF_monoRigids hwf hscope)
        (ctxWF_monoRigids hctx hscope)
        (rebaseExplicit hctx hwf hrhs hscope) (ihb hscope)
  | fix hwf _ ih =>
      exact .fix (wf_monoRigids hwf hscope) (ih hscope)

end RuntimeTyping
end EPL

namespace EPL
namespace RuntimeTyping

private theorem scoped_weakenRigids
    {ty : Ty}
    (hScoped : ty.Scoped rigidCount binderCount)
    (hscope : rigidCount ≤ larger) :
    ty.Scoped larger binderCount := by
  induction hScoped with
  | prim => exact .prim
  | arrow _ _ domainIH codomainIH => exact .arrow domainIH codomainIH
  | bvar hindex => exact .bvar hindex
  | rigid hlevel => exact .rigid (hlevel.trans_le hscope)
  | mvar id => exact .mvar id

private theorem schemeWF_weakenRigids
    {scheme : PolyTy}
    (wf : scheme.WF rigidCount)
    (hscope : rigidCount ≤ larger) :
    scheme.WF larger :=
  ⟨scoped_weakenRigids wf.1 hscope, wf.2⟩

private theorem ctxWF_insert
    {pre post : Ctx} {inserted : PolyTy}
    (wf : (pre ++ post : Ctx).WF rigidCount)
    (insertedWF : inserted.WF rigidCount) :
    (pre ++ inserted :: post : Ctx).WF rigidCount := by
  intro scheme hmem
  rcases List.mem_append.mp hmem with hpre | htail
  · exact wf scheme (List.mem_append_left post hpre)
  · rcases List.mem_cons.mp htail with rfl | hsuffix
    · exact insertedWF
    · exact wf scheme (List.mem_append_right pre hsuffix)

private theorem weakenAt
    (typing : RuntimeTyping rigidCount env expr ty) :
    ∀ (pre post : Ctx), env = pre ++ post →
      inserted.WF rigidCount →
      RuntimeTyping rigidCount (pre ++ inserted :: post)
        (expr.shiftFrom pre.length 1) ty := by
  induction typing with
  | primLit =>
      intro pre post _ _
      exact .primLit
  | primOp =>
      intro pre post _ _
      exact .primOp
  | var lookup schemeWF lengthEq argsWF =>
      expose_names
      intro pre post envEq insertedWF
      rw [envEq] at lookup
      by_cases hindex : index < pre.length
      · simp only [Expr.shiftFrom, if_neg (Nat.not_le.mpr hindex)]
        apply RuntimeTyping.var (scheme := scheme) (args := args)
        · rw [List.getElem?_append_left hindex]
          rwa [List.getElem?_append_left hindex] at lookup
        · exact schemeWF
        · exact lengthEq
        · exact argsWF
      · have hle : pre.length ≤ index := Nat.le_of_not_gt hindex
        simp only [Expr.shiftFrom, if_pos hle]
        apply RuntimeTyping.var (scheme := scheme) (args := args)
        · rw [List.getElem?_append_right hle] at lookup
          rw [List.getElem?_append_right (by omega : pre.length ≤ index + 1)]
          have hsub : index + 1 - pre.length = (index - pre.length) + 1 := by omega
          rw [hsub, List.getElem?_cons_succ]
          exact lookup
        · exact schemeWF
        · exact lengthEq
        · exact argsWF
  | lambda paramWF _ bodyIH =>
      expose_names
      intro pre post envEq insertedWF
      simp only [Expr.shiftFrom]
      apply RuntimeTyping.lambda paramWF
      have shifted := bodyIH (PolyTy.mono paramTy :: pre) post
        (by simp [envEq]) insertedWF
      simpa only [List.cons_append, List.length_cons] using shifted
  | app _ _ functionIH argumentIH =>
      intro pre post envEq insertedWF
      exact .app (functionIH pre post envEq insertedWF)
        (argumentIH pre post envEq insertedWF)
  | letMono rhsWF _ _ rhsIH bodyIH =>
      expose_names
      intro pre post envEq insertedWF
      simp only [Expr.shiftFrom]
      apply RuntimeTyping.letMono rhsWF
      · exact rhsIH pre post envEq insertedWF
      · have shifted := bodyIH (PolyTy.mono rhsTy :: pre) post
          (by simp [envEq]) insertedWF
        simpa only [List.cons_append, List.length_cons] using shifted
  | letPoly schemeWF ctxWF _ _ rhsIH bodyIH =>
      expose_names
      intro pre post envEq insertedWF
      simp only [Expr.shiftFrom]
      apply RuntimeTyping.letPoly (scheme := scheme) schemeWF
      · rw [envEq] at ctxWF
        exact ctxWF_insert ctxWF insertedWF
      · exact rhsIH pre post envEq
          (schemeWF_weakenRigids insertedWF (Nat.le_add_right _ _))
      · have shifted := bodyIH (scheme :: pre) post
          (by simp [envEq]) insertedWF
        simpa only [List.cons_append, List.length_cons] using shifted
  | fix selfWF _ bodyIH =>
      expose_names
      intro pre post envEq insertedWF
      simp only [Expr.shiftFrom]
      apply RuntimeTyping.fix selfWF
      have shifted := bodyIH (PolyTy.mono selfTy :: pre) post
        (by simp [envEq]) insertedWF
      simpa only [List.cons_append, List.length_cons] using shifted

/-- Inserting a well-formed scheme at the head of the term context preserves
typing after shifting all free term indices by one. -/
theorem weakenHead
    (typing : RuntimeTyping rigidCount ctx expr ty)
    (insertedWF : inserted.WF rigidCount) :
    RuntimeTyping rigidCount (inserted :: ctx) (expr.shiftFrom 0 1) ty := by
  simpa using weakenAt typing [] ctx rfl insertedWF

end RuntimeTyping
end EPL

namespace EPL

private theorem openWith_nil_of_scoped_zero
    {ty : Ty} {rigidCount : Nat}
    (hscoped : ty.Scoped rigidCount 0) :
    ty.openWith [] = ty := by
  induction hscoped with
  | prim => rfl
  | arrow _ _ ihDomain ihCodomain =>
      simp only [Ty.openWith, ihDomain, ihCodomain]
  | bvar h => omega
  | rigid => rfl
  | mvar => rfl

private theorem openWith_eq_self_of_scoped_zero
    {ty : Ty} {rigidCount : Nat}
    (hscoped : ty.Scoped rigidCount 0) (replacements : List Ty) :
    ty.openWith replacements = ty := by
  induction hscoped with
  | prim => rfl
  | arrow _ _ ihDomain ihCodomain =>
      simp only [Ty.openWith, ihDomain, ihCodomain]
  | bvar h => omega
  | rigid => rfl
  | mvar => rfl

/-- A monomorphic runtime typing derivation is the unique instance of its
zero-binder scheme. -/
theorem RuntimeHasScheme.mono
    (typeWF : ty.WF rigidCount 0)
    (typing : RuntimeTyping rigidCount ctx expr ty) :
    RuntimeHasScheme rigidCount ctx expr (PolyTy.mono ty) := by
  refine ⟨typeWF, ?_⟩
  intro larger hscope args hlen _
  have : args = [] := List.length_eq_zero_iff.mp (by simpa [PolyTy.mono] using hlen)
  subst args
  simpa only [PolyTy.openWith, PolyTy.mono,
    openWith_nil_of_scoped_zero typeWF.1] using typing.weakenRigids hscope

/-- Replace one contiguous block of rigid levels, removing that block from all
higher levels. The `extra` levels used in the proofs below are the fresh blocks
introduced by nested explicit schemes. -/
private def instantiateRigids (base count : Nat) (args : List Ty) : Ty → Ty
  | .prim p => .prim p
  | .arrow domain codomain =>
      .arrow (instantiateRigids base count args domain)
        (instantiateRigids base count args codomain)
  | .bvar index => .bvar index
  | .rigid level =>
      if level < base then .rigid level
      else if level - base < count then
        (args[level - base]?).getD (.rigid level)
      else .rigid (level - count)
  | .mvar id => .mvar id

private def instantiateSchemeRigids (base count : Nat) (args : List Ty)
    (scheme : PolyTy) : PolyTy :=
  ⟨scheme.paramCount, instantiateRigids base count args scheme.body⟩

private def instantiateCtxRigids (base count : Nat) (args : List Ty)
    (ctx : Ctx) : Ctx :=
  ctx.map (instantiateSchemeRigids base count args)

private theorem scoped_mono
    {ty : Ty} {rigidCount binderCount larger largerBinders : Nat}
    (hscoped : ty.Scoped rigidCount binderCount)
    (hrigid : rigidCount ≤ larger)
    (hbinders : binderCount ≤ largerBinders) :
    ty.Scoped larger largerBinders := by
  induction hscoped with
  | prim => exact .prim
  | arrow _ _ ihDomain ihCodomain => exact .arrow ihDomain ihCodomain
  | bvar h => exact .bvar (Nat.lt_of_lt_of_le h hbinders)
  | rigid h => exact .rigid (Nat.lt_of_lt_of_le h hrigid)
  | mvar id => exact .mvar id

private theorem instantiateRigids_scoped
    (hscoped : ty.Scoped (base + count + extra) binderCount)
    (hlen : args.length = count)
    (argsWF : ∀ arg ∈ args, arg.WF base 0) :
    (instantiateRigids base count args ty).Scoped (base + extra) binderCount := by
  induction ty with
  | prim => exact .prim
  | arrow domain codomain domainIH codomainIH =>
      cases hscoped with
      | arrow domainScoped codomainScoped =>
          exact .arrow (domainIH domainScoped) (codomainIH codomainScoped)
  | bvar index =>
      cases hscoped with
      | bvar h => exact .bvar h
  | rigid level =>
      cases hscoped with
      | rigid hlevel =>
          simp only [instantiateRigids]
          split <;> rename_i hbelow
          · exact .rigid (by omega)
          · split <;> rename_i hblock
            · have hindex : level - base < args.length := by simpa [hlen] using hblock
              have hget : args[level - base]? = some args[level - base] :=
                List.getElem?_eq_getElem hindex
              simp only [hget, Option.getD_some]
              exact scoped_mono (argsWF args[level - base] (List.getElem_mem hindex)).1
                (by omega) (by omega)
            · exact .rigid (by omega)
  | mvar id => exact .mvar id

private theorem instantiateRigids_metaFree
    (free : ty.MetaFree)
    (argsFree : ∀ arg ∈ args, arg.MetaFree) :
    (instantiateRigids base count args ty).MetaFree := by
  induction ty with
  | prim => exact .prim
  | arrow domain codomain domainIH codomainIH =>
      cases free with
      | arrow domainFree codomainFree =>
          exact .arrow (domainIH domainFree) (codomainIH codomainFree)
  | bvar => exact .bvar
  | rigid level =>
      simp only [instantiateRigids]
      split
      · exact .rigid
      · split
        · cases hget : args[level - base]? with
          | none => exact .rigid
          | some arg => exact argsFree arg (List.mem_of_getElem? hget)
        · exact .rigid
  | mvar => cases free

private theorem instantiateRigids_wf
    (wf : ty.WF (base + count + extra) binderCount)
    (hlen : args.length = count)
    (argsWF : ∀ arg ∈ args, arg.WF base 0) :
    (instantiateRigids base count args ty).WF (base + extra) binderCount :=
  ⟨instantiateRigids_scoped wf.1 hlen argsWF,
    instantiateRigids_metaFree wf.2 (fun arg harg => (argsWF arg harg).2)⟩

private theorem instantiateSchemeRigids_wf
    (wf : scheme.WF (base + count + extra))
    (hlen : args.length = count)
    (argsWF : ∀ arg ∈ args, arg.WF base 0) :
    (instantiateSchemeRigids base count args scheme).WF (base + extra) :=
  instantiateRigids_wf wf hlen argsWF

private theorem instantiateCtxRigids_wf
    (wf : ctx.WF (base + count + extra))
    (hlen : args.length = count)
    (argsWF : ∀ arg ∈ args, arg.WF base 0) :
    (instantiateCtxRigids base count args ctx).WF (base + extra) := by
  intro scheme hscheme
  rw [instantiateCtxRigids] at hscheme
  obtain ⟨original, horiginal, rfl⟩ := List.mem_map.mp hscheme
  exact instantiateSchemeRigids_wf (wf original horiginal) hlen argsWF

private theorem instantiateRigids_openWith (ty : Ty)
    (argsScoped : ∀ arg ∈ args, arg.Scoped base 0) :
    instantiateRigids base count args (ty.openWith replacements) =
      (instantiateRigids base count args ty).openWith
        (replacements.map (instantiateRigids base count args)) := by
  induction ty with
  | prim => rfl
  | arrow domain codomain domainIH codomainIH =>
      simp only [Ty.openWith, instantiateRigids, domainIH, codomainIH]
  | bvar index =>
      simp only [Ty.openWith, instantiateRigids, List.getElem?_map]
      cases replacements[index]? <;> rfl
  | rigid level =>
      simp only [Ty.openWith, instantiateRigids]
      split
      · rfl
      · split
        · cases hget : args[level - base]? with
          | none => rfl
          | some arg =>
              exact (openWith_eq_self_of_scoped_zero
                (argsScoped arg (List.mem_of_getElem? hget)) _).symm
        · rfl
  | mvar id => rfl

private theorem instantiateRigids_rigidBlock :
    (rigidBlock (base + count + extra) amount).map
        (instantiateRigids base count args) =
      rigidBlock (base + extra) amount := by
  simp only [rigidBlock, List.map_map]
  apply List.map_congr_left
  intro offset hoffset
  have hoffset' : offset < amount := List.mem_range.mp hoffset
  simp only [Function.comp_apply, instantiateRigids]
  split <;> rename_i hbelow
  · omega
  · split <;> rename_i hblock
    · omega
    · congr 1
      omega

private theorem instantiateRigids_openRigids (scheme : PolyTy)
    (argsScoped : ∀ arg ∈ args, arg.Scoped base 0) :
    instantiateRigids base count args
        (scheme.openRigids (base + count + extra)) =
      (instantiateSchemeRigids base count args scheme).openRigids (base + extra) := by
  simp only [PolyTy.openRigids, PolyTy.openWith, instantiateSchemeRigids,
    instantiateRigids_openWith _ argsScoped, instantiateRigids_rigidBlock]

private theorem instantiateRigids_eq_self
    (hscoped : ty.Scoped base binderCount) :
    instantiateRigids base count args ty = ty := by
  induction hscoped with
  | prim => rfl
  | arrow _ _ domainIH codomainIH =>
      simp only [instantiateRigids, domainIH, codomainIH]
  | bvar => rfl
  | rigid hlevel => simp [instantiateRigids, hlevel]
  | mvar => rfl

private theorem instantiateSchemeRigids_eq_self
    (wf : scheme.WF base) :
    instantiateSchemeRigids base count args scheme = scheme := by
  cases scheme
  simp only [instantiateSchemeRigids]
  rw [instantiateRigids_eq_self wf.1]

private theorem instantiateCtxRigids_eq_self
    (wf : ctx.WF base) :
    instantiateCtxRigids base count args ctx = ctx := by
  induction ctx with
  | nil => rfl
  | cons scheme tail ih =>
      simp only [instantiateCtxRigids, List.map_cons, List.cons.injEq]
      constructor
      · exact instantiateSchemeRigids_eq_self (wf scheme (by simp))
      · exact ih (fun candidate hcandidate => wf candidate (by simp [hcandidate]))

private def instantiateRigidsTo (source target count : Nat) (args : List Ty) : Ty → Ty
  | .prim p => .prim p
  | .arrow domain codomain =>
      .arrow (instantiateRigidsTo source target count args domain)
        (instantiateRigidsTo source target count args codomain)
  | .bvar index => .bvar index
  | .rigid level =>
      if level < source then .rigid level
      else if level - source < count then
        (args[level - source]?).getD (.rigid level)
      else .rigid (target + (level - (source + count)))
  | .mvar id => .mvar id

private def instantiateSchemeRigidsTo (source target count : Nat) (args : List Ty)
    (scheme : PolyTy) : PolyTy :=
  ⟨scheme.paramCount, instantiateRigidsTo source target count args scheme.body⟩

private def instantiateCtxRigidsTo (source target count : Nat) (args : List Ty)
    (ctx : Ctx) : Ctx :=
  ctx.map (instantiateSchemeRigidsTo source target count args)

private theorem instantiateRigidsTo_scoped
    (hscoped : ty.Scoped (source + count + extra) binderCount)
    (hsource : source ≤ target)
    (hlen : args.length = count)
    (argsWF : ∀ arg ∈ args, arg.WF target 0) :
    (instantiateRigidsTo source target count args ty).Scoped
      (target + extra) binderCount := by
  induction ty with
  | prim => exact .prim
  | arrow domain codomain domainIH codomainIH =>
      cases hscoped with
      | arrow domainScoped codomainScoped =>
          exact .arrow (domainIH domainScoped) (codomainIH codomainScoped)
  | bvar index =>
      cases hscoped with
      | bvar h => exact .bvar h
  | rigid level =>
      cases hscoped with
      | rigid hlevel =>
          simp only [instantiateRigidsTo]
          split <;> rename_i hbelow
          · exact .rigid (by omega)
          · split <;> rename_i hblock
            · have hindex : level - source < args.length := by simpa [hlen] using hblock
              have hget : args[level - source]? = some args[level - source] :=
                List.getElem?_eq_getElem hindex
              simp only [hget, Option.getD_some]
              exact scoped_mono (argsWF args[level - source] (List.getElem_mem hindex)).1
                (by omega) (by omega)
            · exact .rigid (by omega)
  | mvar id => exact .mvar id

private theorem instantiateRigidsTo_metaFree
    (free : ty.MetaFree)
    (argsFree : ∀ arg ∈ args, arg.MetaFree) :
    (instantiateRigidsTo source target count args ty).MetaFree := by
  induction ty with
  | prim => exact .prim
  | arrow domain codomain domainIH codomainIH =>
      cases free with
      | arrow domainFree codomainFree =>
          exact .arrow (domainIH domainFree) (codomainIH codomainFree)
  | bvar => exact .bvar
  | rigid level =>
      simp only [instantiateRigidsTo]
      split
      · exact .rigid
      · split
        · cases hget : args[level - source]? with
          | none => exact .rigid
          | some arg => exact argsFree arg (List.mem_of_getElem? hget)
        · exact .rigid
  | mvar => cases free

private theorem instantiateRigidsTo_wf
    (wf : ty.WF (source + count + extra) binderCount)
    (hsource : source ≤ target)
    (hlen : args.length = count)
    (argsWF : ∀ arg ∈ args, arg.WF target 0) :
    (instantiateRigidsTo source target count args ty).WF
      (target + extra) binderCount :=
  ⟨instantiateRigidsTo_scoped wf.1 hsource hlen argsWF,
    instantiateRigidsTo_metaFree wf.2 (fun arg harg => (argsWF arg harg).2)⟩

private theorem instantiateSchemeRigidsTo_wf
    (wf : scheme.WF (source + count + extra))
    (hsource : source ≤ target)
    (hlen : args.length = count)
    (argsWF : ∀ arg ∈ args, arg.WF target 0) :
    (instantiateSchemeRigidsTo source target count args scheme).WF
      (target + extra) :=
  instantiateRigidsTo_wf wf hsource hlen argsWF

private theorem instantiateCtxRigidsTo_wf
    (wf : ctx.WF (source + count + extra))
    (hsource : source ≤ target)
    (hlen : args.length = count)
    (argsWF : ∀ arg ∈ args, arg.WF target 0) :
    (instantiateCtxRigidsTo source target count args ctx).WF (target + extra) := by
  intro scheme hscheme
  rw [instantiateCtxRigidsTo] at hscheme
  obtain ⟨original, horiginal, rfl⟩ := List.mem_map.mp hscheme
  exact instantiateSchemeRigidsTo_wf (wf original horiginal) hsource hlen argsWF

private theorem instantiateRigidsTo_openWith (ty : Ty)
    (argsScoped : ∀ arg ∈ args, arg.Scoped target 0) :
    instantiateRigidsTo source target count args (ty.openWith replacements) =
      (instantiateRigidsTo source target count args ty).openWith
        (replacements.map (instantiateRigidsTo source target count args)) := by
  induction ty with
  | prim => rfl
  | arrow domain codomain domainIH codomainIH =>
      simp only [Ty.openWith, instantiateRigidsTo, domainIH, codomainIH]
  | bvar index =>
      simp only [Ty.openWith, instantiateRigidsTo, List.getElem?_map]
      cases replacements[index]? <;> rfl
  | rigid level =>
      simp only [Ty.openWith, instantiateRigidsTo]
      split
      · rfl
      · split
        · cases hget : args[level - source]? with
          | none => rfl
          | some arg =>
              exact (openWith_eq_self_of_scoped_zero
                (argsScoped arg (List.mem_of_getElem? hget)) _).symm
        · rfl
  | mvar => rfl

private theorem instantiateRigidsTo_nestedBlock :
    (rigidBlock (source + count + extra) amount).map
        (instantiateRigidsTo source target count args) =
      rigidBlock (target + extra) amount := by
  simp only [rigidBlock, List.map_map]
  apply List.map_congr_left
  intro offset hoffset
  have hoffset' : offset < amount := List.mem_range.mp hoffset
  simp only [Function.comp_apply, instantiateRigidsTo]
  split <;> rename_i hbelow
  · omega
  · split <;> rename_i hblock
    · omega
    · congr 1
      omega

private theorem instantiateRigidsTo_openRigids (scheme : PolyTy)
    (argsScoped : ∀ arg ∈ args, arg.Scoped target 0) :
    instantiateRigidsTo source target count args
        (scheme.openRigids (source + count + extra)) =
      (instantiateSchemeRigidsTo source target count args scheme).openRigids
        (target + extra) := by
  simp only [PolyTy.openRigids, PolyTy.openWith, instantiateSchemeRigidsTo,
    instantiateRigidsTo_openWith _ argsScoped, instantiateRigidsTo_nestedBlock]

private theorem instantiateRigidsTo_genericBlock
    (hlen : args.length = count) :
    (rigidBlock source count).map
        (instantiateRigidsTo source target count args) = args := by
  apply List.ext_getElem
  · simp [rigidBlock, hlen]
  · intro index hleft hright
    have hindex : index < count := by simpa [rigidBlock] using hleft
    simp only [rigidBlock, List.getElem_map, List.getElem_range,
      instantiateRigidsTo]
    split <;> rename_i hbelow
    · omega
    · split <;> rename_i hblock
      · have hget : args[index]? = some args[index] :=
          List.getElem?_eq_getElem (by simpa [hlen] using hindex)
        simp [hget]
      · omega

private theorem instantiateRigidsTo_generic (scheme : PolyTy)
    (hcount : scheme.paramCount = count)
    (hlen : args.length = count)
    (argsScoped : ∀ arg ∈ args, arg.Scoped target 0) :
    instantiateRigidsTo source target count args (scheme.openRigids source) =
      (instantiateSchemeRigidsTo source target count args scheme).openWith args := by
  subst count
  simp only [PolyTy.openRigids, PolyTy.openWith, instantiateSchemeRigidsTo,
    instantiateRigidsTo_openWith _ argsScoped,
    instantiateRigidsTo_genericBlock hlen]

private theorem instantiateRigidsTo_eq_self
    (hscoped : ty.Scoped source binderCount) :
    instantiateRigidsTo source target count args ty = ty := by
  induction hscoped with
  | prim => rfl
  | arrow _ _ domainIH codomainIH =>
      simp only [instantiateRigidsTo, domainIH, codomainIH]
  | bvar => rfl
  | rigid hlevel => simp [instantiateRigidsTo, hlevel]
  | mvar => rfl

private theorem instantiateSchemeRigidsTo_eq_self
    (wf : scheme.WF source) :
    instantiateSchemeRigidsTo source target count args scheme = scheme := by
  cases scheme
  simp only [instantiateSchemeRigidsTo]
  rw [instantiateRigidsTo_eq_self wf.1]

private theorem instantiateCtxRigidsTo_eq_self
    (wf : ctx.WF source) :
    instantiateCtxRigidsTo source target count args ctx = ctx := by
  induction ctx with
  | nil => rfl
  | cons scheme tail ih =>
      simp only [instantiateCtxRigidsTo, List.map_cons, List.cons.injEq]
      constructor
      · exact instantiateSchemeRigidsTo_eq_self (wf scheme (by simp))
      · exact ih (fun candidate hcandidate => wf candidate (by simp [hcandidate]))

private theorem instantiateTypingTo
    (typing : RuntimeTyping old ctx expr ty)
    (hold : old = source + count + extra)
    (hsource : source ≤ target)
    (hlen : args.length = count)
    (argsWF : ∀ arg ∈ args, arg.WF target 0) :
    RuntimeTyping (target + extra)
      (instantiateCtxRigidsTo source target count args ctx) expr
      (instantiateRigidsTo source target count args ty) := by
  induction typing generalizing extra with
  | primLit =>
      cases_type PrimLit <;> exact .primLit
  | primOp =>
      cases_type PrimOp
      exact .primOp
  | @var ctx index scheme instArgs rigidCount hlookup schemeWF instLength instWF =>
      have schemeWF' : scheme.WF (source + count + extra) := by
        simpa [hold] using schemeWF
      have hlookup' :
          (instantiateCtxRigidsTo source target count args ctx)[index]? =
            some (instantiateSchemeRigidsTo source target count args scheme) := by
        simp [instantiateCtxRigidsTo, List.getElem?_map, hlookup]
      have opened := RuntimeTyping.var
        (args := instArgs.map (instantiateRigidsTo source target count args)) hlookup'
        (instantiateSchemeRigidsTo_wf schemeWF' hsource hlen argsWF)
        (by simpa using instLength)
        (fun transformed htransformed => by
          obtain ⟨original, horiginal, rfl⟩ := List.mem_map.mp htransformed
          have originalWF : original.WF (source + count + extra) 0 := by
            simpa [hold] using instWF original horiginal
          exact instantiateRigidsTo_wf originalWF hsource hlen argsWF)
      have hopen :
          instantiateRigidsTo source target count args
              (scheme.openWith instArgs) =
            (instantiateSchemeRigidsTo source target count args scheme).openWith
              (instArgs.map (instantiateRigidsTo source target count args)) := by
        exact instantiateRigidsTo_openWith
          (source := source) (target := target) (count := count) (args := args)
          scheme.body (replacements := instArgs)
          (fun arg harg => (argsWF arg harg).1)
      rw [hopen]
      exact opened
  | @lambda rigidCount paramTy ctx body bodyTy ann paramWF bodyTyping bodyIH =>
      have paramWF' : paramTy.WF (source + count + extra) 0 := by
        simpa [hold] using paramWF
      apply RuntimeTyping.lambda
        (instantiateRigidsTo_wf paramWF' hsource hlen argsWF)
      simpa [instantiateCtxRigidsTo, instantiateSchemeRigidsTo, PolyTy.mono] using
        bodyIH hold
  | @app rigidCount ctx function argumentTy resultTy argument
      functionTyping argumentTyping functionIH argumentIH =>
      exact RuntimeTyping.app (functionIH hold) (argumentIH hold)
  | @letMono rigidCount ctx rhs rhsTy body bodyTy ann rhsWF rhsTyping bodyTyping
      rhsIH bodyIH =>
      have rhsWF' : rhsTy.WF (source + count + extra) 0 := by
        simpa [hold] using rhsWF
      apply RuntimeTyping.letMono
        (instantiateRigidsTo_wf rhsWF' hsource hlen argsWF)
      · exact rhsIH hold
      · simpa [instantiateCtxRigidsTo, instantiateSchemeRigidsTo, PolyTy.mono] using
          bodyIH hold
  | @letPoly rigidCount ctx rhs scheme body bodyTy ann schemeWF ctxWF rhsTyping
      bodyTyping rhsIH bodyIH =>
      have schemeWF' : scheme.WF (source + count + extra) := by
        simpa [hold] using schemeWF
      have ctxWF' : ctx.WF (source + count + extra) := by
        simpa [hold] using ctxWF
      let transformed := instantiateSchemeRigidsTo source target count args scheme
      apply RuntimeTyping.letPoly
        (scheme := transformed)
        (instantiateSchemeRigidsTo_wf schemeWF' hsource hlen argsWF)
        (instantiateCtxRigidsTo_wf ctxWF' hsource hlen argsWF)
      · have rhsInstantiated := rhsIH (extra := extra + scheme.paramCount) (by omega)
        rw [hold] at rhsInstantiated
        have hopen :
            instantiateRigidsTo source target count args
                (scheme.openRigids (source + count + extra)) =
              transformed.openRigids (target + extra) := by
          exact instantiateRigidsTo_openRigids
            (source := source) (target := target) (count := count) (args := args)
            (extra := extra) scheme (fun arg harg => (argsWF arg harg).1)
        rw [hopen] at rhsInstantiated
        simpa only [Nat.add_assoc] using rhsInstantiated
      · simpa [transformed, instantiateCtxRigidsTo] using bodyIH hold
  | @fix rigidCount selfTy ctx body selfWF bodyTyping bodyIH =>
      have selfWF' : selfTy.WF (source + count + extra) 0 := by
        simpa [hold] using selfWF
      apply RuntimeTyping.fix
        (instantiateRigidsTo_wf selfWF' hsource hlen argsWF)
      simpa [instantiateCtxRigidsTo, instantiateSchemeRigidsTo, PolyTy.mono] using
        bodyIH hold

namespace RuntimeTyping

/-- Checking a runtime expression once at a fresh rigid block establishes all
well-formed semantic instances of that exact written scheme. -/
theorem genericHasScheme
    (schemeWF : scheme.WF rigidCount)
    (ctxWF : ctx.WF rigidCount)
    (generic : RuntimeTyping (rigidCount + scheme.paramCount) ctx expr
      (scheme.openRigids rigidCount)) :
    RuntimeHasScheme rigidCount ctx expr scheme := by
  refine ⟨schemeWF, ?_⟩
  intro larger hscope args hlen argsWF
  have instantiated := instantiateTypingTo
    (source := rigidCount) (target := larger) (count := scheme.paramCount)
    (args := args) (extra := 0) generic rfl hscope hlen argsWF
  have hctx :
      instantiateCtxRigidsTo rigidCount larger scheme.paramCount args ctx = ctx :=
    instantiateCtxRigidsTo_eq_self ctxWF
  have hscheme :
      instantiateSchemeRigidsTo rigidCount larger scheme.paramCount args scheme =
        scheme :=
    instantiateSchemeRigidsTo_eq_self schemeWF
  have hty :
      instantiateRigidsTo rigidCount larger scheme.paramCount args
          (scheme.openRigids rigidCount) =
        scheme.openWith args := by
    rw [instantiateRigidsTo_generic scheme rfl hlen
      (fun arg harg => (argsWF arg harg).1), hscheme]
  simpa only [Nat.add_zero, hctx, hty] using instantiated

end RuntimeTyping
end EPL

namespace EPL
namespace RuntimeTyping

private theorem scoped_monoRigids_2
    {ty : Ty} {rigidCount binderCount larger : Nat}
    (hScoped : ty.Scoped rigidCount binderCount)
    (hscope : rigidCount ≤ larger) :
    ty.Scoped larger binderCount := by
  induction hScoped with
  | prim => exact .prim
  | arrow _ _ domainIH codomainIH => exact .arrow domainIH codomainIH
  | bvar hindex => exact .bvar hindex
  | rigid hlevel => exact .rigid (hlevel.trans_le hscope)
  | mvar id => exact .mvar id

private theorem wf_monoRigids_2
    {ty : Ty} {rigidCount binderCount larger : Nat}
    (wf : ty.WF rigidCount binderCount)
    (hscope : rigidCount ≤ larger) :
    ty.WF larger binderCount :=
  ⟨scoped_monoRigids_2 wf.1 hscope, wf.2⟩

private theorem schemeWF_monoRigids_2
    {scheme : PolyTy} {rigidCount larger : Nat}
    (wf : scheme.WF rigidCount)
    (hscope : rigidCount ≤ larger) :
    scheme.WF larger :=
  wf_monoRigids_2 wf hscope

private theorem ctxWF_monoRigids_2
    {ctx : Ctx} {rigidCount larger : Nat}
    (wf : ctx.WF rigidCount)
    (hscope : rigidCount ≤ larger) :
    ctx.WF larger := by
  intro scheme hmem
  exact schemeWF_monoRigids_2 (wf scheme hmem) hscope

private theorem ctxWF_cons
    {head : PolyTy} {tail : Ctx} {rigidCount : Nat}
    (headWF : head.WF rigidCount)
    (tailWF : Ctx.WF rigidCount tail) :
    Ctx.WF rigidCount (head :: tail) := by
  intro scheme hmem
  rcases List.mem_cons.mp hmem with rfl | htail
  · exact headWF
  · exact tailWF scheme htail

private theorem ctxWF_remove_middle
    {pre post : Ctx} {removed : PolyTy} {rigidCount : Nat}
    (wf : (pre ++ [removed] ++ post : Ctx).WF rigidCount) :
    (pre ++ post : Ctx).WF rigidCount := by
  intro scheme hmem
  apply wf scheme
  simp only [List.mem_append, List.mem_singleton] at hmem ⊢
  tauto

private theorem shiftFrom_zero (expr : Expr T) :
    expr.shiftFrom threshold 0 = expr := by
  induction expr generalizing threshold with
  | primLit => rfl
  | primOp => rfl
  | var index => simp [Expr.shiftFrom]
  | lambda ann body ih => simp [Expr.shiftFrom, ih]
  | app function argument ihFunction ihArgument =>
      simp [Expr.shiftFrom, ihFunction, ihArgument]
  | letIn ann rhs body ihRhs ihBody =>
      simp [Expr.shiftFrom, ihRhs, ihBody]
  | fix ann body ih => simp [Expr.shiftFrom, ih]

private theorem shiftFrom_add_zero (expr : Expr T) :
    (expr.shiftFrom threshold first).shiftFrom threshold second =
      expr.shiftFrom threshold (first + second) := by
  induction expr generalizing threshold with
  | primLit => rfl
  | primOp => rfl
  | var index =>
      by_cases h : threshold ≤ index
      · simp [Expr.shiftFrom, h, h.trans (Nat.le_add_right _ _), Nat.add_assoc]
      · simp [Expr.shiftFrom, h]
  | lambda ann body ih => simp [Expr.shiftFrom, ih]
  | app function argument ihFunction ihArgument =>
      simp [Expr.shiftFrom, ihFunction, ihArgument]
  | letIn ann rhs body ihRhs ihBody =>
      simp [Expr.shiftFrom, ihRhs, ihBody]
  | fix ann body ih => simp [Expr.shiftFrom, ih]

private theorem hasScheme_weakenPrefix
    {rigidCount : Nat} {ctx pre : Ctx} {replacement : RuntimeExpr}
    {scheme : PolyTy}
    (typing : RuntimeHasScheme rigidCount ctx replacement scheme)
    (preWF : pre.WF rigidCount) :
    RuntimeHasScheme rigidCount (pre ++ ctx)
      (replacement.shiftFrom 0 pre.length) scheme := by
  refine ⟨typing.schemeWF, ?_⟩
  intro larger hscope args hlen hargs
  have baseTyping := typing.typed larger hscope args hlen hargs
  induction pre with
  | nil =>
      simpa only [List.nil_append, List.length_nil,
        shiftFrom_zero] using baseTyping
  | cons head tail tailIH =>
      have headWF : head.WF rigidCount := preWF head (by simp)
      have tailWF : Ctx.WF rigidCount tail := by
        intro item hitem
        exact preWF item (by simp [hitem])
      have weakenedTail := tailIH tailWF
      have weakened := RuntimeTyping.weakenHead weakenedTail
        (schemeWF_monoRigids_2 headWF hscope)
      simpa only [List.cons_append, List.length_cons,
        shiftFrom_add_zero, Nat.add_comm] using weakened

private theorem substAt
    (bodyTyping : RuntimeTyping rigidCount env body ty) :
    ∀ (pre ctx : Ctx) (target : PolyTy) (replacement : RuntimeExpr),
      env = pre ++ [target] ++ ctx →
      pre.WF rigidCount →
      RuntimeHasScheme rigidCount ctx replacement target →
      RuntimeTyping rigidCount (pre ++ ctx)
        (body.substN pre.length [replacement]) ty := by
  induction bodyTyping with
  | primLit =>
      intro pre ctx target replacement _ _ _
      exact .primLit
  | primOp =>
      intro pre ctx target replacement _ _ _
      exact .primOp
  | var lookup schemeWF lengthEq argsWF =>
      expose_names
      intro pre ctx target replacement envEq preWF replacementTyping
      rw [envEq, List.append_assoc] at lookup
      simp only [Expr.substN]
      by_cases hlt : index < pre.length
      · rw [if_pos hlt]
        apply RuntimeTyping.var (scheme := scheme) (args := args)
        · rw [List.getElem?_append_left hlt]
          rwa [List.getElem?_append_left hlt] at lookup
        · exact schemeWF
        · exact lengthEq
        · exact argsWF
      · rw [if_neg hlt]
        by_cases hselected : index - pre.length < [replacement].length
        · rw [dif_pos hselected]
          simp only [List.length_cons, List.length_nil, Nat.zero_add] at hselected
          have hzero : index - pre.length = 0 := by omega
          have lookup' := lookup
          rw [List.getElem?_append_right (by omega)] at lookup'
          simp only [hzero] at lookup'
          have schemeEq : scheme = target := (Option.some.inj lookup').symm
          subst scheme
          have replacementAtPrefix := hasScheme_weakenPrefix replacementTyping preWF
          have typed : RuntimeTyping rigidCount_1 (pre ++ ctx)
              (replacement.shiftFrom 0 pre.length) (target.openWith args) :=
            replacementAtPrefix.typed rigidCount_1 (le_refl rigidCount_1)
              args lengthEq argsWF
          simpa using typed
        · rw [dif_neg hselected]
          have hpre : pre.length ≤ index := Nat.le_of_not_gt hlt
          have hone : [target].length ≤ index - pre.length := by
            simpa using (Nat.le_of_not_gt hselected)
          have hindices :
              index - [replacement].length - pre.length =
                index - pre.length - [target].length := by
            simp only [List.length_cons, List.length_nil, Nat.zero_add]
            omega
          apply RuntimeTyping.var (scheme := scheme) (args := args)
          · rw [List.getElem?_append_right
              (by omega : pre.length ≤ index - [replacement].length)]
            rw [List.getElem?_append_right hpre,
              List.getElem?_append_right hone] at lookup
            rw [hindices]
            exact lookup
          · exact schemeWF
          · exact lengthEq
          · exact argsWF
  | lambda paramWF _ bodyIH =>
      expose_names
      intro pre ctx target replacement envEq preWF replacementTyping
      simp only [Expr.substN]
      apply RuntimeTyping.lambda paramWF
      have substituted := bodyIH (PolyTy.mono paramTy :: pre) ctx target replacement
        (by simp [envEq, List.append_assoc])
        (ctxWF_cons ⟨paramWF.1, paramWF.2⟩ preWF) replacementTyping
      simpa only [List.cons_append, List.length_cons] using substituted
  | app _ _ functionIH argumentIH =>
      intro pre ctx target replacement envEq preWF replacementTyping
      exact .app (functionIH pre ctx target replacement envEq preWF replacementTyping)
        (argumentIH pre ctx target replacement envEq preWF replacementTyping)
  | letMono rhsWF _ _ rhsIH bodyIH =>
      expose_names
      intro pre ctx target replacement envEq preWF replacementTyping
      simp only [Expr.substN]
      apply RuntimeTyping.letMono rhsWF
      · exact rhsIH pre ctx target replacement envEq preWF replacementTyping
      · have substituted := bodyIH (PolyTy.mono rhsTy :: pre) ctx target replacement
          (by simp [envEq, List.append_assoc])
          (ctxWF_cons ⟨rhsWF.1, rhsWF.2⟩ preWF) replacementTyping
        simpa only [List.cons_append, List.length_cons] using substituted
  | letPoly schemeWF localCtxWF _ _ rhsIH bodyIH =>
      expose_names
      intro pre ctx target replacement envEq preWF replacementTyping
      simp only [Expr.substN]
      rw [envEq] at localCtxWF
      apply RuntimeTyping.letPoly (scheme := scheme) schemeWF
      · exact ctxWF_remove_middle localCtxWF
      · exact rhsIH pre ctx target replacement envEq
          (ctxWF_monoRigids_2 preWF (Nat.le_add_right _ _))
          ⟨schemeWF_monoRigids_2 replacementTyping.schemeWF (Nat.le_add_right _ _),
            fun larger hscope => replacementTyping.typed larger
              ((Nat.le_add_right _ _).trans hscope)⟩
      · have substituted := bodyIH (scheme :: pre) ctx target replacement
          (by simp [envEq, List.append_assoc])
          (ctxWF_cons schemeWF preWF) replacementTyping
        simpa only [List.cons_append, List.length_cons] using substituted
  | fix selfWF _ bodyIH =>
      expose_names
      intro pre ctx target replacement envEq preWF replacementTyping
      simp only [Expr.substN]
      apply RuntimeTyping.fix selfWF
      have substituted := bodyIH (PolyTy.mono selfTy :: pre) ctx target replacement
        (by simp [envEq, List.append_assoc])
        (ctxWF_cons ⟨selfWF.1, selfWF.2⟩ preWF) replacementTyping
      simpa only [List.cons_append, List.length_cons] using substituted

/-- Replacing the head variable by an expression inhabiting its whole scheme
preserves runtime typing. This is the common substitution principle for beta,
monomorphic lets, explicit-polymorphic lets, and fixed-point unfolding. -/
theorem substScheme
    (replacementTyping : RuntimeHasScheme rigidCount ctx replacement scheme)
    (bodyTyping : RuntimeTyping rigidCount (scheme :: ctx) body ty) :
    RuntimeTyping rigidCount ctx (body.subst1 replacement) ty := by
  simpa [Expr.subst1] using
    substAt bodyTyping [] ctx scheme replacement (by simp) (by simp [Ctx.WF])
      replacementTyping

end RuntimeTyping
end EPL

namespace EPL
namespace RuntimeTyping

private theorem int_value
    (value : Eval.Value expr)
    (typing : RuntimeTyping rigidCount [] expr (.prim .int)) :
    ∃ number, expr = .primLit (.int number) := by
  cases value with
  | primLit =>
      cases_type PrimLit <;> cases typing
      exact ⟨_, rfl⟩
  | primOp => cases typing
  | lambda => cases typing
  | intAddPartial =>
      cases typing with
      | app functionTyping _ => cases functionTyping

private theorem progress_empty (typing : RuntimeTyping rigidCount ctx expr ty)
    (empty : ctx = []) :
    Eval.Value expr ∨ ∃ next, Eval.Step expr next := by
  induction typing with
  | primLit => exact .inl .primLit
  | primOp => exact .inl .primOp
  | var hlookup => simp [empty] at hlookup
  | lambda => exact .inl .lambda
  | app functionTyping argumentTyping functionIH argumentIH =>
      rcases functionIH empty with functionValue | ⟨function', functionStep⟩
      · rcases argumentIH empty with argumentValue | ⟨argument', argumentStep⟩
        · cases functionValue with
          | primLit =>
              cases_type PrimLit <;> cases functionTyping
          | primOp =>
              cases_type PrimOp
              cases functionTyping
              obtain ⟨number, rfl⟩ := int_value argumentValue (empty ▸ argumentTyping)
              exact .inl .intAddPartial
          | lambda =>
              exact .inr ⟨_, .beta argumentValue⟩
          | intAddPartial =>
              cases functionTyping with
              | app operatorTyping _ =>
                  cases operatorTyping
                  obtain ⟨number, rfl⟩ := int_value argumentValue (empty ▸ argumentTyping)
                  exact .inr ⟨_, .intAdd⟩
        · exact .inr ⟨_, .appArgument functionValue argumentStep⟩
      · exact .inr ⟨_, .appFunction functionStep⟩
  | letMono _ _ _ rhsIH _ =>
      rcases rhsIH empty with rhsValue | ⟨rhs', rhsStep⟩
      · exact .inr ⟨_, .letValue rhsValue⟩
      · exact .inr ⟨_, .letRhs rhsStep⟩
  | letPoly _ _ _ _ rhsIH _ =>
      rcases rhsIH empty with rhsValue | ⟨rhs', rhsStep⟩
      · exact .inr ⟨_, .letValue rhsValue⟩
      · exact .inr ⟨_, .letRhs rhsStep⟩
  | fix => exact .inr ⟨_, .fixUnfold⟩

/-- Closed, well-typed runtime terms are values or can take a step. -/
theorem progress (typing : RuntimeTyping 0 [] expr ty) :
    Eval.Value expr ∨ ∃ next, Eval.Step expr next := by
  exact progress_empty typing rfl

/-- A runtime step preserves the exact assigned type. -/
theorem preservation
    (typing : RuntimeTyping rigidCount ctx expr ty)
    (step : Eval.Step expr next) :
    RuntimeTyping rigidCount ctx next ty := by
  induction step generalizing rigidCount ctx ty with
  | beta argumentValue =>
      cases typing with
      | app functionTyping argumentTyping =>
          cases functionTyping with
          | lambda paramWF bodyTyping =>
              exact substScheme (RuntimeHasScheme.mono paramWF argumentTyping)
                bodyTyping
  | appFunction functionStep functionIH =>
      cases typing with
      | app functionTyping argumentTyping =>
          exact .app (functionIH functionTyping) argumentTyping
  | appArgument functionValue argumentStep argumentIH =>
      cases typing with
      | app functionTyping argumentTyping =>
          exact .app functionTyping (argumentIH argumentTyping)
  | intAdd =>
      cases typing with
      | app functionTyping argumentTyping =>
          cases functionTyping with
          | app operatorTyping leftTyping =>
              cases operatorTyping
              cases leftTyping
              cases argumentTyping
              exact .primLit
  | letRhs rhsStep rhsIH =>
      cases typing with
      | letMono rhsWF rhsTyping bodyTyping =>
          exact .letMono rhsWF (rhsIH rhsTyping) bodyTyping
      | letPoly schemeWF ctxWF rhsTyping bodyTyping =>
          exact .letPoly schemeWF ctxWF (rhsIH rhsTyping) bodyTyping
  | letValue rhsValue =>
      cases typing with
      | letMono rhsWF rhsTyping bodyTyping =>
          exact substScheme (RuntimeHasScheme.mono rhsWF rhsTyping) bodyTyping
      | letPoly schemeWF ctxWF rhsTyping bodyTyping =>
          exact substScheme (genericHasScheme schemeWF ctxWF rhsTyping) bodyTyping
  | fixUnfold =>
      cases typing with
      | fix selfWF bodyTyping =>
          expose_names
          have fixed := RuntimeTyping.fix selfWF bodyTyping
          exact substScheme (RuntimeHasScheme.mono selfWF fixed) bodyTyping

end RuntimeTyping
end EPL

/-!
# The executable evaluator computes `Eval.Step`

`step?` is sound and complete for the step relation, so the relation is
deterministic and `step? = none` characterises normal forms. `run` follows
the relation, and it is complete: any execution that reaches a value is found
by `run` given enough fuel.
-/

namespace EPL
namespace Eval

theorem isValue_iff {expr : RuntimeExpr} :
    isValue expr = true ↔ Value expr := by
  constructor
  · intro h
    cases expr with
    | primLit literal => exact .primLit
    | primOp op => exact .primOp
    | var index => simp [isValue] at h
    | lambda ann body => exact .lambda
    | app function argument =>
        cases function with
        | primOp op =>
            cases op
            cases argument with
            | primLit literal =>
                cases literal with
                | int value => exact .intAddPartial
                | unit => simp [isValue] at h
                | bool value => simp [isValue] at h
            | primOp op => simp [isValue] at h
            | var index => simp [isValue] at h
            | lambda ann body => simp [isValue] at h
            | app f a => simp [isValue] at h
            | letIn ann rhs body => simp [isValue] at h
            | fix ann body => simp [isValue] at h
        | primLit literal => simp [isValue] at h
        | var index => simp [isValue] at h
        | lambda ann body => simp [isValue] at h
        | app f a => simp [isValue] at h
        | letIn ann rhs body => simp [isValue] at h
        | fix ann body => simp [isValue] at h
    | letIn ann rhs body => simp [isValue] at h
    | fix ann body => simp [isValue] at h
  · intro value
    cases value <;> simp [isValue]

/-- `step?` is the identity (returns `none`) on values. -/
private theorem step?_of_value {expr : RuntimeExpr} (value : Value expr) :
    step? expr = none := by
  cases value <;> rfl

private theorem isValue_lambda (ann : Option Unit) (body : RuntimeExpr) :
    isValue (.lambda ann body) = true := rfl

/-- Values are normal forms. -/
theorem Value.irreducible {expr next : RuntimeExpr}
    (value : Value expr) : ¬ Step expr next := by
  intro step
  cases value with
  | primLit => cases step
  | primOp => cases step
  | lambda => cases step
  | intAddPartial =>
      cases step with
      | appFunction h => cases h
      | appArgument _ h => cases h

theorem step?_sound {expr next : RuntimeExpr}
    (h : step? expr = some next) : Step expr next := by
  induction expr generalizing next with
  | primLit literal => simp [step?] at h
  | primOp op => simp [step?] at h
  | var index => simp [step?] at h
  | lambda ann body => simp [step?] at h
  | fix ann body =>
      cases ann
      simp only [step?] at h
      cases h
      exact Step.fixUnfold
  | letIn ann rhs body ihRhs ihBody =>
      simp only [step?] at h
      cases hr : step? rhs with
      | some rhs' =>
          rw [hr] at h
          simp only [Option.some.injEq] at h
          cases h
          exact Step.letRhs (ihRhs hr)
      | none =>
          rw [hr] at h
          by_cases hval : isValue rhs = true
          · simp only [hval, if_true] at h
            cases h
            exact Step.letValue (isValue_iff.mp hval)
          · simp only [hval] at h
            simp at h
  | app function argument ihFunction ihArgument =>
      simp only [step?] at h
      cases hf : step? function with
      | some function' =>
          rw [hf] at h
          simp only [Option.some.injEq] at h
          cases h
          exact Step.appFunction (ihFunction hf)
      | none =>
          rw [hf] at h
          by_cases hval : isValue function = true
          · simp only [hval, if_true] at h
            cases ha : step? argument with
            | some argument' =>
                rw [ha] at h
                simp only [Option.some.injEq] at h
                cases h
                exact Step.appArgument (isValue_iff.mp hval) (ihArgument ha)
            | none =>
                rw [ha] at h
                by_cases harg : isValue argument = true
                · simp only [harg, if_true] at h
                  have vf := isValue_iff.mp hval
                  have va := isValue_iff.mp harg
                  cases vf with
                  | primLit => simp [reduceApp] at h
                  | primOp => simp [reduceApp] at h
                  | lambda =>
                      simp only [reduceApp] at h
                      simp only [Option.some.injEq] at h
                      cases h
                      exact Step.beta va
                  | intAddPartial =>
                      cases va with
                      | primLit =>
                          rename_i literal
                          cases literal with
                          | int right =>
                              simp only [reduceApp] at h
                              simp only [Option.some.injEq] at h
                              cases h
                              exact Step.intAdd
                          | unit => simp [reduceApp] at h
                          | bool b => simp [reduceApp] at h
                      | primOp => simp [reduceApp] at h
                      | lambda => simp [reduceApp] at h
                      | intAddPartial => simp [reduceApp] at h
                · simp only [harg] at h
                  simp at h
          · simp only [hval] at h
            simp at h

theorem step?_complete {expr next : RuntimeExpr}
    (step : Step expr next) : step? expr = some next := by
  induction step with
  | beta value =>
      simp [step?, reduceApp, step?_of_value value, isValue_iff.mpr value, isValue_lambda]
  | appFunction h ih =>
      simp [step?, ih]
  | appArgument value h ih =>
      simp [step?, step?_of_value value, isValue_iff.mpr value, ih]
  | intAdd =>
      simp [step?, reduceApp, isValue]
  | letRhs h ih =>
      simp [step?, ih]
  | letValue value =>
      simp [step?, step?_of_value value, isValue_iff.mpr value]
  | fixUnfold =>
      simp [step?]

theorem Step.deterministic {expr first second : RuntimeExpr}
    (stepFirst : Step expr first) (stepSecond : Step expr second) :
    first = second := by
  have hFirst := step?_complete stepFirst
  have hSecond := step?_complete stepSecond
  rw [hFirst] at hSecond
  exact Option.some.inj hSecond

/-- `step?` returns `none` exactly on normal forms of `Step`. -/
theorem step?_eq_none_iff {expr : RuntimeExpr} :
    step? expr = none ↔ ∀ next, ¬ Step expr next := by
  constructor
  · intro h next step
    have hsome := step?_complete step
    rw [h] at hsome
    exact nomatch hsome
  · intro h
    cases hstep : step? expr with
    | none => rfl
    | some next => exact absurd (step?_sound hstep) (h next)

/-- `run` is stationary when `step?` has no successor. -/
private theorem run_none {expr : RuntimeExpr} (h : step? expr = none) (fuel : Nat) :
    run fuel expr = expr := by
  induction fuel with
  | zero => rfl
  | succ fuel ih => simp [run, h]

private theorem run_add (first second : Nat) (expr : RuntimeExpr) :
    run (first + second) expr = run second (run first expr) := by
  induction first generalizing expr with
  | zero => simp [run]
  | succ first ih =>
      rw [Nat.succ_add]
      cases h : step? expr with
      | none =>
          rw [run_none h (first + second + 1)]
          rw [run_none h (first + 1)]
          rw [run_none h second]
      | some next =>
          have hlhs : run (first + second + 1) expr = run (first + second) next := by
            simp [run, h]
          have hrhs : run (first + 1) expr = run first next := by
            simp [run, h]
          rw [hlhs, hrhs]
          exact ih next

/-- The evaluator only ever follows the step relation. -/
theorem run_steps (fuel : Nat) (expr : RuntimeExpr) :
    Steps expr (run fuel expr) := by
  induction fuel generalizing expr with
  | zero => exact Relation.ReflTransGen.refl
  | succ fuel ih =>
      simp only [run]
      cases h : step? expr with
      | none =>
          exact Relation.ReflTransGen.refl
      | some next =>
          exact Relation.ReflTransGen.head (step?_sound h) (ih next)

/-- The evaluator leaves values unchanged. -/
theorem run_value {fuel : Nat} {expr : RuntimeExpr}
    (value : Value expr) : run fuel expr = expr := by
  exact run_none (step?_of_value value) fuel

/-- Any finite execution is realised by `run` at exactly the corresponding
fuel. -/
private theorem run_reaches {expr result : RuntimeExpr} (steps : Steps expr result) :
    ∃ fuel, run fuel expr = result := by
  induction steps with
  | refl => exact ⟨0, rfl⟩
  | tail hsteps hstep ih =>
      obtain ⟨fuel, hfuel⟩ := ih
      refine ⟨fuel + 1, ?_⟩
      rw [run_add fuel 1 expr, hfuel]
      simp [run, step?_complete hstep]

/-- Evaluator completeness: an execution reaching a value is found by `run`
with enough fuel (and with any larger fuel). -/
theorem run_complete {expr result : RuntimeExpr}
    (steps : Steps expr result) (value : Value result) :
    ∃ fuel, ∀ extra, run (fuel + extra) expr = result := by
  obtain ⟨fuel, hfuel⟩ := run_reaches steps
  refine ⟨fuel, fun extra => ?_⟩
  rw [run_add fuel extra expr, hfuel]
  exact run_value (fuel := extra) value

end Eval
end EPL
