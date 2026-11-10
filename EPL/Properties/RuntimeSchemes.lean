import EPL.Properties.RuntimeRigidWeakening
import EPL.Properties.RuntimeWeakening

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
