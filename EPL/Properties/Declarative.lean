import EPL.Core
import EPL.Typing

namespace EPL
namespace Template.Fits

/-- Two occurrences of the same local named hole in one assignment have the
same type. -/
theorem named_eq
    (first : Template.Fits holes (.named name) firstTy)
    (second : Template.Fits holes (.named name) secondTy) :
    firstTy = secondTy := by
  cases first with
  | named firstLookup =>
      cases second with
      | named secondLookup =>
          exact Option.some.inj (firstLookup.symm.trans secondLookup)

end Template.Fits
end EPL

namespace EPL
namespace Typing

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
      | some arg =>
          exact hargs arg (List.mem_of_getElem? hget)
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

/-- Every declaratively assigned type is semantic and scoped. -/
theorem regular (typing : Typing rigidCount ctx expr ty) :
    ty.WF rigidCount 0 := by
  induction typing with
  | primLit => cases_type PrimLit <;> exact ⟨.prim, .prim⟩
  | primOp =>
      cases_type PrimOp
      exact ⟨.arrow .prim (.arrow .prim .prim),
        .arrow .prim (.arrow .prim .prim)⟩
  | var _ wf hlen hargs => exact wf_openWith wf hlen hargs
  | lambda paramWF _ _ bodyRegular =>
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

end Typing
end EPL

namespace EPL
namespace Typing

private theorem fits_scoped
    (fits : Template.Fits holes template ty)
    (wf : ty.WF rigidCount binderCount) :
    template.Scoped rigidCount binderCount := by
  induction fits with
  | fixed => exact .fixed wf
  | hole => exact .hole
  | named => exact .named
  | arrow domainFit codomainFit domainIH codomainIH =>
      rcases wf with ⟨hScoped, hFree⟩
      cases hScoped with
      | arrow domainScoped codomainScoped =>
          cases hFree with
          | arrow domainFree codomainFree =>
              exact .arrow (domainIH ⟨domainScoped, domainFree⟩)
                (codomainIH ⟨codomainScoped, codomainFree⟩)

private theorem matches_scoped
    {template : Template} {ty : Ty}
    (hMatches : template.Matches ty)
    (wf : ty.WF rigidCount binderCount) :
    template.Scoped rigidCount binderCount := by
  rcases hMatches with ⟨holes, _, fits⟩
  exact fits_scoped fits wf

private theorem param_scoped
    {ann : ParamAnn} {ty : Ty}
    (hMatches : ParamAnn.Matches ann ty)
    (wf : ty.WF rigidCount binderCount) :
    ∀ template, ann = some template → template.Scoped rigidCount binderCount := by
  intro template hann
  exact matches_scoped (hMatches template hann) wf

/-- A derivable source expression cannot contain an out-of-scope authored
rigid, bound type variable, or inference metavariable in its annotations. -/
theorem sourceScoped (typing : Typing rigidCount ctx expr ty) :
    expr.TypeScoped rigidCount 0 := by
  induction typing with
  | primLit => exact .primLit
  | primOp => exact .primOp
  | var => exact .var
  | lambda paramWF hMatches _ bodyScoped =>
      exact .lambda (param_scoped hMatches paramWF) bodyScoped
  | app _ _ functionScoped argumentScoped =>
      exact .app functionScoped argumentScoped
  | letMono _ _ _ rhsScoped bodyScoped =>
      exact .letMono rhsScoped bodyScoped
  | letPoly hMatches schemeWF _ rhsScoped _ _ _ bodyScoped =>
      rcases hMatches with ⟨paramCountEq, bodyMatches⟩
      exact .letPoly
        (by
          rw [← paramCountEq]
          simpa [PolyTy.WF] using matches_scoped bodyMatches schemeWF)
        (by simpa [paramCountEq] using rhsScoped)
        bodyScoped
  | fix selfWF hMatches _ bodyScoped =>
      exact .fix (matches_scoped hMatches selfWF) bodyScoped

end Typing
end EPL

namespace EPL
namespace Typing

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

private def shiftTemplate (cutoff delta : Nat) : Template → Template
  | .fixed ty => .fixed (shiftTy cutoff delta ty)
  | .hole => .hole
  | .named name => .named name
  | .arrow a b => .arrow (shiftTemplate cutoff delta a) (shiftTemplate cutoff delta b)

private def shiftWritten (cutoff delta : Nat)
    (scheme : Scheme Template) : Scheme Template :=
  ⟨scheme.paramCount, shiftTemplate cutoff delta scheme.body⟩

@[simp] private theorem shiftWritten_paramCount (written : Scheme Template) :
    (shiftWritten cutoff delta written).paramCount = written.paramCount := rfl

private def shiftSource (cutoff delta : Nat) : Source → Source
  | .primLit lit => .primLit lit
  | .primOp op => .primOp op
  | .var index => .var index
  | .lambda ann body =>
      .lambda (ann.map (shiftTemplate cutoff delta))
        (shiftSource cutoff delta body)
  | .app function argument =>
      .app (shiftSource cutoff delta function) (shiftSource cutoff delta argument)
  | .letIn ann rhs body =>
      .letIn (ann.map (shiftWritten cutoff delta))
        (shiftSource cutoff delta rhs) (shiftSource cutoff delta body)
  | .fix ann body =>
      .fix (shiftTemplate cutoff delta ann) (shiftSource cutoff delta body)

private def shiftCtx (cutoff delta : Nat) (ctx : Ctx) : Ctx :=
  ctx.map (shiftScheme cutoff delta)

private def shiftHoles (cutoff delta : Nat)
    (holes : HoleAssignment) : HoleAssignment :=
  holes.map fun entry => (entry.1, shiftTy cutoff delta entry.2)

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

private theorem templateScoped_monoRigids {template : Template}
    (h : Template.Scoped rigidCount binderCount template) (hle : rigidCount ≤ larger) :
    Template.Scoped larger binderCount template := by
  induction h with
  | fixed hty => exact .fixed (wf_monoRigids hty hle)
  | hole => exact .hole
  | named => exact .named
  | arrow _ _ iha ihb => exact .arrow iha ihb

private theorem typeScoped_monoRigids {expr : Source}
    (h : Expr.TypeScoped rigidCount binderCount expr) (hle : rigidCount ≤ larger) :
    Expr.TypeScoped larger binderCount expr := by
  induction h with
  | primLit => exact .primLit
  | primOp => exact .primOp
  | var => exact .var
  | lambda hann _ ih =>
      exact .lambda (fun template heq => templateScoped_monoRigids (hann template heq) hle) ih
  | app _ _ ihf iha => exact .app ihf iha
  | letMono _ _ ihr ihb => exact .letMono ihr ihb
  | letPoly hw _ _ ihr ihb =>
      exact .letPoly (templateScoped_monoRigids hw hle) ihr ihb
  | fix ha _ ihb => exact .fix (templateScoped_monoRigids ha hle) ihb

private theorem shiftTy_eq_self {ty : Ty} (h : Ty.Scoped cutoff binderCount ty) :
    shiftTy cutoff delta ty = ty := by
  induction h with
  | prim => rfl
  | arrow _ _ iha ihb => simp [shiftTy, iha, ihb]
  | bvar hi => rfl
  | rigid hi => simp [shiftTy, shiftLevel, Nat.not_le.mpr hi]
  | mvar id => rfl

private theorem shiftScheme_eq_self {scheme : PolyTy} (h : PolyTy.WF cutoff scheme) :
    shiftScheme cutoff delta scheme = scheme := by
  cases scheme with
  | mk count body =>
      simp only [shiftScheme, Scheme.mk.injEq, true_and]
      exact shiftTy_eq_self h.1

private theorem shiftTemplate_eq_self {template : Template}
    (h : Template.Scoped cutoff binderCount template) :
    shiftTemplate cutoff delta template = template := by
  induction h with
  | fixed hty => simp [shiftTemplate, shiftTy_eq_self hty.1]
  | hole => rfl
  | named => rfl
  | arrow _ _ iha ihb => simp [shiftTemplate, iha, ihb]

private theorem shiftSource_eq_self {expr : Source}
    (h : Expr.TypeScoped cutoff binderCount expr) :
    shiftSource cutoff delta expr = expr := by
  induction expr generalizing binderCount with
  | primLit => rfl
  | primOp => rfl
  | var => rfl
  | lambda ann body ih =>
      cases h with
      | lambda hann hbody =>
          have hb := ih hbody
          cases ann with
          | none => simp [shiftSource, hb]
          | some template =>
              have ht := shiftTemplate_eq_self (delta := delta) (hann template rfl)
              simp [shiftSource, hb, ht]
  | app function argument ihf iha =>
      cases h with
      | app hf ha => simp [shiftSource, ihf hf, iha ha]
  | letIn ann rhs body ihr ihb =>
      cases ann with
      | none =>
          cases h with
          | letMono hr hb => simp [shiftSource, ihr hr, ihb hb]
      | some written =>
          cases h with
          | letPoly hw hr hb =>
              have hs := shiftTemplate_eq_self (delta := delta) hw
              have hrr := ihr hr
              have hbb := ihb hb
              cases written
              simp [shiftSource, shiftWritten, hs, hrr, hbb]
  | fix ann body ih =>
      cases h with
      | fix ha hb => simp [shiftSource, shiftTemplate_eq_self ha, ih hb]

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
    (h : Ty.Scoped rigidCount binderCount ty) (_hcut : cutoff ≤ rigidCount) :
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
    (h : Ty.WF rigidCount binderCount ty) (hcut : cutoff ≤ rigidCount) :
    Ty.WF (rigidCount + delta) binderCount (shiftTy cutoff delta ty) :=
  ⟨shiftTy_scoped h.1 hcut, shiftTy_metaFree h.2⟩

private theorem shiftScheme_wf {scheme : PolyTy}
    (h : PolyTy.WF rigidCount scheme) (hcut : cutoff ≤ rigidCount) :
    PolyTy.WF (rigidCount + delta) (shiftScheme cutoff delta scheme) :=
  shiftTy_wf h hcut

private theorem shiftTemplate_scoped {template : Template}
    (h : Template.Scoped rigidCount binderCount template)
    (hcut : cutoff ≤ rigidCount) :
    Template.Scoped (rigidCount + delta) binderCount
      (shiftTemplate cutoff delta template) := by
  induction h with
  | fixed hty => exact .fixed (shiftTy_wf hty hcut)
  | hole => exact .hole
  | named => exact .named
  | arrow _ _ iha ihb => exact .arrow iha ihb

private theorem shiftTypeScoped {expr : Source}
    (h : Expr.TypeScoped rigidCount binderCount expr)
    (hcut : cutoff ≤ rigidCount) :
    Expr.TypeScoped (rigidCount + delta) binderCount
      (shiftSource cutoff delta expr) := by
  induction expr generalizing binderCount with
  | primLit => exact .primLit
  | primOp => exact .primOp
  | var => exact .var
  | lambda ann body ih =>
      cases h with
      | lambda hann hbody =>
          apply Expr.TypeScoped.lambda
          · intro template heq
            cases ann with
            | none => simp at heq
            | some original =>
                simp only [Option.map_some, Option.some.injEq] at heq
                subst template
                exact shiftTemplate_scoped (hann original rfl) hcut
          · exact ih hbody
  | app function argument ihf iha =>
      cases h with
      | app hf ha => exact .app (ihf hf) (iha ha)
  | letIn ann rhs body ihr ihb =>
      cases ann with
      | none =>
          cases h with
          | letMono hr hb => exact .letMono (ihr hr) (ihb hb)
      | some written =>
          cases h with
          | letPoly hw hr hb =>
              exact .letPoly (shiftTemplate_scoped hw hcut) (ihr hr) (ihb hb)
  | fix ann body ih =>
      cases h with
      | fix ha hb => exact .fix (shiftTemplate_scoped ha hcut) (ih hb)

private theorem shiftCtx_wf {ctx : Ctx} (h : Ctx.WF rigidCount ctx)
    (hcut : cutoff ≤ rigidCount) :
    Ctx.WF (rigidCount + delta) (shiftCtx cutoff delta ctx) := by
  intro scheme hmem
  rcases List.mem_map.mp hmem with ⟨original, horiginal, rfl⟩
  exact shiftScheme_wf (h original horiginal) hcut

private theorem shiftHoles_unique (h : holes.Unique) :
    (shiftHoles cutoff delta holes).Unique := by
  simpa [HoleAssignment.Unique, shiftHoles, List.map_map, Function.comp_def] using h

private theorem shiftHoles_lookup (holes : HoleAssignment) (name : String) :
    (shiftHoles cutoff delta holes).lookup name =
      (holes.lookup name).map (shiftTy cutoff delta) := by
  induction holes with
  | nil => rfl
  | cons entry tail ih =>
      rcases entry with ⟨key, ty⟩
      simp only [shiftHoles, List.map_cons, List.lookup]
      split
      · simp_all
      · simpa [shiftHoles] using ih

private theorem shiftFits (h : Template.Fits holes template ty) :
    Template.Fits (shiftHoles cutoff delta holes)
      (shiftTemplate cutoff delta template) (shiftTy cutoff delta ty) := by
  induction h with
  | fixed => exact .fixed
  | hole => exact .hole
  | named hlookup =>
      apply Template.Fits.named
      rw [shiftHoles_lookup, hlookup]
      rfl
  | arrow _ _ iha ihb => exact .arrow iha ihb

private theorem shiftMatches (h : Template.Matches template ty) :
    Template.Matches (shiftTemplate cutoff delta template)
      (shiftTy cutoff delta ty) := by
  rcases h with ⟨holes, hu, hf⟩
  exact ⟨shiftHoles cutoff delta holes, shiftHoles_unique hu, shiftFits hf⟩

private theorem shiftParamMatches (h : ParamAnn.Matches ann ty) :
    ParamAnn.Matches (ann.map (shiftTemplate cutoff delta))
      (shiftTy cutoff delta ty) := by
  intro template heq
  cases ann with
  | none => simp at heq
  | some original =>
      simp only [Option.map_some, Option.some.injEq] at heq
      subst template
      exact shiftMatches (h original rfl)

private theorem shiftSchemeMatches
    (h : SchemeTemplateMatches written scheme) :
    SchemeTemplateMatches (shiftWritten cutoff delta written)
      (shiftScheme cutoff delta scheme) := by
  constructor
  · exact h.paramCount_eq
  · exact shiftMatches h.body_matches

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
  intro offset hoffset
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

private theorem shiftTy_openRigidsFrom (ty : Ty) (hcut : cutoff ≤ base) :
    shiftTy cutoff delta (ty.openRigidsFrom depth base count) =
      (shiftTy cutoff delta ty).openRigidsFrom depth (base + delta) count := by
  induction ty with
  | prim => rfl
  | arrow a b iha ihb =>
      simp [Ty.openRigidsFrom, shiftTy, iha, ihb]
  | bvar index =>
      simp only [Ty.openRigidsFrom, shiftTy]
      split
      · rfl
      · split
        · simp only [shiftTy]
          unfold shiftLevel
          rw [if_pos (by omega)]
          congr 1
          omega
        · rfl
  | rigid => rfl
  | mvar => rfl

private theorem shiftTemplate_openRigidsFrom (template : Template)
    (hcut : cutoff ≤ base) :
    shiftTemplate cutoff delta
        (template.openRigidsFrom depth base count) =
      (shiftTemplate cutoff delta template).openRigidsFrom
        depth (base + delta) count := by
  induction template with
  | fixed ty =>
      simp [Template.openRigidsFrom, shiftTemplate,
        shiftTy_openRigidsFrom ty hcut]
  | hole => rfl
  | named => rfl
  | arrow a b iha ihb =>
      simp [Template.openRigidsFrom, shiftTemplate, iha, ihb]

private theorem shiftWritten_openRigidsFrom (written : Scheme Template)
    (hcut : cutoff ≤ base) :
    shiftWritten cutoff delta
        (written.openTemplateRigidsFrom depth base count) =
      (shiftWritten cutoff delta written).openTemplateRigidsFrom
        depth (base + delta) count := by
  cases written with
  | mk params body =>
      simp [Scheme.openTemplateRigidsFrom, shiftWritten,
        shiftTemplate_openRigidsFrom body hcut]

private theorem shiftSource_openRigidsFrom (expr : Source)
    (hcut : cutoff ≤ base) :
    shiftSource cutoff delta
        (expr.openRigidsFrom depth base count) =
      (shiftSource cutoff delta expr).openRigidsFrom
        depth (base + delta) count := by
  induction expr generalizing depth with
  | primLit => rfl
  | primOp => rfl
  | var => rfl
  | lambda ann body ih =>
      cases ann with
      | none => simp [Expr.openRigidsFrom, shiftSource, ih]
      | some template =>
          simp [Expr.openRigidsFrom, shiftSource, ih,
            shiftTemplate_openRigidsFrom template hcut]
  | app function argument ihf iha =>
      simp [Expr.openRigidsFrom, shiftSource, ihf, iha]
  | letIn ann rhs body ihr ihb =>
      cases ann with
      | none =>
          simp [Expr.openRigidsFrom, shiftSource, ihr, ihb]
      | some written =>
          simp [Expr.openRigidsFrom, shiftSource, ihr, ihb,
            shiftWritten_openRigidsFrom written hcut]
  | fix ann body ih =>
      simp [Expr.openRigidsFrom, shiftSource, ih,
        shiftTemplate_openRigidsFrom ann hcut]

private theorem shiftSource_openRigids (expr : Source)
    (hcut : cutoff ≤ base) :
    shiftSource cutoff delta (expr.openRigids base count) =
      (shiftSource cutoff delta expr).openRigids (base + delta) count :=
  shiftSource_openRigidsFrom expr hcut

private theorem shiftTyping (typing : Typing rigidCount ctx expr ty)
    (hcut : cutoff ≤ rigidCount) :
    Typing (rigidCount + delta) (shiftCtx cutoff delta ctx)
      (shiftSource cutoff delta expr) (shiftTy cutoff delta ty) := by
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
        exact shiftTy_wf (hargs original horiginal) hcut
      have hopen := shiftTy_openWith (cutoff := cutoff) (delta := delta)
        scheme.body args
      simpa [shiftSource, shiftScheme, PolyTy.openWith, shiftedArgs, hopen] using
        (Typing.var hlookup' (shiftScheme_wf hwf hcut)
          (by simpa [shiftedArgs] using hlen) hargs')
  | lambda hwf hmatch _ ih =>
      simpa [shiftSource, shiftTy, shiftCtx, shiftScheme, PolyTy.mono] using
        (Typing.lambda (shiftTy_wf hwf hcut) (shiftParamMatches hmatch)
          (ih hcut))
  | app _ _ ihf iha =>
      simpa [shiftSource, shiftTy] using Typing.app (ihf hcut) (iha hcut)
  | letMono hwf _ _ ihr ihb =>
      simpa [shiftSource, shiftCtx, shiftScheme, PolyTy.mono] using
        (Typing.letMono (shiftTy_wf hwf hcut) (ihr hcut) (ihb hcut))
  | letPoly hmatch hwf hctx hsource _ _ ihr ihb =>
      clear rigidCount ctx expr ty
      have hRhs := ihr (by omega)
      rw [shiftSource_openRigids _ hcut, shiftScheme_openRigids _ hcut] at hRhs
      simpa [shiftSource, shiftScheme, shiftWritten] using
        (Typing.letPoly (shiftSchemeMatches hmatch)
          (shiftScheme_wf hwf hcut) (shiftCtx_wf hctx hcut)
          (shiftTypeScoped hsource hcut)
          (by simpa [shiftScheme, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hRhs)
          (ihb hcut))
  | fix hwf hmatch _ ih =>
      simpa [shiftSource, shiftCtx, shiftScheme, PolyTy.mono] using
        (Typing.fix (shiftTy_wf hwf hcut) (shiftMatches hmatch) (ih hcut))

private theorem rebaseExplicit
    (hctx : Ctx.WF rigidCount ctx)
    (hsource : Expr.TypeScoped rigidCount scheme.paramCount rhs)
    (hscheme : PolyTy.WF rigidCount scheme)
    (htyping : Typing (rigidCount + scheme.paramCount) ctx
      (rhs.openRigids rigidCount scheme.paramCount)
      (scheme.openRigids rigidCount))
    (hle : rigidCount ≤ larger) :
    Typing (larger + scheme.paramCount) ctx
      (rhs.openRigids larger scheme.paramCount)
      (scheme.openRigids larger) := by
  let delta := larger - rigidCount
  have hshift := shiftTyping (cutoff := rigidCount) (delta := delta)
    htyping (by omega)
  have hctxId : shiftCtx rigidCount delta ctx = ctx := shiftCtx_eq_self hctx
  have hrhsId : shiftSource rigidCount delta rhs = rhs :=
    shiftSource_eq_self hsource
  have hschemeId : shiftScheme rigidCount delta scheme = scheme :=
    shiftScheme_eq_self hscheme
  rw [hctxId, shiftSource_openRigids _ (by omega), hrhsId,
    shiftScheme_openRigids _ (by omega), hschemeId] at hshift
  have hbase : rigidCount + delta = larger := by
    dsimp [delta]
    omega
  have hboundary : rigidCount + scheme.paramCount + delta =
      larger + scheme.paramCount := by
    dsimp [delta]
    omega
  rw [hboundary, hbase] at hshift
  exact hshift

/-- Increasing the rigid-level boundary preserves an existing derivation.
Explicit-scheme premises require alpha-renaming their deterministic fresh
rigid block from the old boundary to the new one. -/
theorem weakenRigids (typing : Typing rigidCount ctx expr ty)
    (hscope : rigidCount ≤ larger) :
    Typing larger ctx expr ty := by
  induction typing generalizing larger with
  | primLit => exact .primLit
  | primOp => exact .primOp
  | var hlookup hwf hlen hargs =>
      exact .var hlookup (schemeWF_monoRigids hwf hscope) hlen
        (fun arg harg => wf_monoRigids (hargs arg harg) hscope)
  | lambda hwf hmatch _ ih =>
      exact .lambda (wf_monoRigids hwf hscope) hmatch (ih hscope)
  | app _ _ ihf iha => exact .app (ihf hscope) (iha hscope)
  | letMono hwf _ _ ihr ihb =>
      exact .letMono (wf_monoRigids hwf hscope) (ihr hscope) (ihb hscope)
  | letPoly hmatch hwf hctx hsource hrhs _ _ ihb =>
      exact .letPoly hmatch (schemeWF_monoRigids hwf hscope)
        (ctxWF_monoRigids hctx hscope) (typeScoped_monoRigids hsource hscope)
        (rebaseExplicit hctx hsource hwf hrhs hscope) (ihb hscope)
  | fix hwf hmatch _ ih =>
      exact .fix (wf_monoRigids hwf hscope) hmatch (ih hscope)

end Typing
end EPL
