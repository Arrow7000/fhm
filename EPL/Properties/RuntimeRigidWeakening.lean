import EPL.RuntimeTyping

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
