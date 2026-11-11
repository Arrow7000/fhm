import EPL.Properties.InferenceClosing
import EPL.Properties.Regular

namespace EPL

/-- Strong semantic soundness of the internal engine. A successful run both
refines its input state and yields a declarative typing derivation under every
semantic model of the result state. -/
theorem inferFuel_sound_model
    {fuel rigidCount : Nat} {ctx : Ctx} {input : Source}
    {state : InferState} {result : InferResult}
    (stateSafe : state.Safe rigidCount)
    (ctxWF : ctx.InferWF rigidCount state.next)
    (inputScoped : input.TypeScoped rigidCount 0)
    (run : inferFuel fuel rigidCount ctx input state = some result) :
    state.Refines result.state rigidCount ∧
      ∀ valuation, result.state.Models rigidCount valuation →
        Typing rigidCount (ctx.realize valuation) input
          (result.ty.realize valuation) := by
  have modelWF : ∀ {candidate : InferState} {valuation : MValuation}
      {rigid : Nat}, candidate.Safe rigid → candidate.Models rigid valuation →
        valuation.WF rigid candidate.next := by
    intro candidate valuation rigid safe models
    simpa [safe.solutions_length] using models.valuationWF
  have ctx_mono : ∀ {context : Ctx} {rigid smaller larger : Nat},
      context.InferWF rigid smaller → smaller ≤ larger →
        context.InferWF rigid larger := by
    intro context rigid smaller larger h le scheme member
    exact ⟨(h scheme member).1,
      fun id idMem => lt_of_lt_of_le ((h scheme member).2 id idMem) le⟩
  have inferWF_mono : ∀ {ty : Ty} {rigid binder smaller larger : Nat},
      ty.InferWF rigid binder smaller → smaller ≤ larger →
        ty.InferWF rigid binder larger := by
    intro ty rigid binder smaller larger h le
    exact ⟨h.1, fun id idMem => lt_of_lt_of_le (h.2 id idMem) le⟩
  have scoped_mono_rigid : ∀ {ty : Ty} {binder smaller larger : Nat},
      ty.Scoped smaller binder → smaller ≤ larger → ty.Scoped larger binder := by
    intro ty binder smaller larger h le
    induction h with
    | prim => exact .prim
    | arrow _ _ ihDomain ihCodomain => exact .arrow ihDomain ihCodomain
    | bvar hlt => exact .bvar hlt
    | rigid hlt => exact .rigid (lt_of_lt_of_le hlt le)
    | mvar id => exact .mvar id
  have ctx_mono_rigid : ∀ {context : Ctx} {frontier smaller larger : Nat},
      context.InferWF smaller frontier → smaller ≤ larger →
        context.InferWF larger frontier := by
    intro context frontier smaller larger h le scheme member
    exact ⟨scoped_mono_rigid (h scheme member).1 le, (h scheme member).2⟩
  have state_mono_rigid : ∀ {candidate : InferState} {smaller larger : Nat},
      candidate.Safe smaller → smaller ≤ larger → candidate.Safe larger := by
    intro candidate smaller larger h le
    exact ⟨h.solutions_length,
      (fun ty member => scoped_mono_rigid (h.solutionsScoped ty member) le),
      h.solutionsBounded, h.solutionsNormalized, h.requiredBounded⟩
  have metaFree_bounded : ∀ {ty : Ty} {frontier : Nat},
      ty.MetaFree → ty.MVarBounded frontier := by
    intro ty frontier h
    induction h with
    | prim => simp [Ty.MVarBounded, Ty.mvars]
    | arrow _ _ ihDomain ihCodomain =>
        intro id member
        simp only [Ty.mvars, List.mem_dedup, List.mem_append] at member
        exact member.elim (ihDomain id) (ihCodomain id)
    | bvar => simp [Ty.MVarBounded, Ty.mvars]
    | rigid => simp [Ty.MVarBounded, Ty.mvars]
  have wf_inferWF : ∀ {ty : Ty} {rigid binder frontier : Nat},
      ty.WF rigid binder → ty.InferWF rigid binder frontier := by
    intro ty rigid binder frontier h
    exact ⟨h.1, metaFree_bounded h.2⟩
  induction fuel generalizing rigidCount ctx input state result with
  | zero => simp [inferFuel] at run
  | succ fuel ih =>
      cases input with
      | primLit literal =>
          simp only [inferFuel, Option.some.injEq] at run
          subst result
          refine ⟨MStore.Refines.refl _ _, ?_⟩
          intro valuation models
          cases literal <;> exact Typing.primLit
      | primOp op =>
          simp only [inferFuel, Option.some.injEq] at run
          subst result
          refine ⟨MStore.Refines.refl _ _, ?_⟩
          intro valuation models
          cases op
          exact Typing.primOp
      | var index =>
          simp only [inferFuel] at run
          cases lookup : ctx[index]? with
          | none => simp [lookup] at run
          | some scheme =>
              simp only [lookup] at run
              let fresh := state.freshMany scheme.paramCount
              have resultEq : result =
                  ⟨fresh.1, (state.solutions.applyScheme scheme).openWith fresh.2⟩ :=
                Option.some.inj run.symm
              subst result
              have freshSafe := InferState.freshMany_safe
                (count := scheme.paramCount) stateSafe
              refine ⟨InferState.freshMany_refines, ?_⟩
              intro valuation models
              have stateModels : state.Models rigidCount valuation :=
                InferState.freshMany_refines valuation models
              have valuationWF : valuation.WF rigidCount fresh.1.next :=
                modelWF freshSafe.1 models
              have schemeMember : scheme ∈ ctx := List.mem_of_getElem? lookup
              have schemeWF := ctxWF scheme schemeMember
              have appliedWF : (state.solutions.applyScheme scheme).InferWF
                  rigidCount state.next :=
                MStore.apply_inferWF stateSafe.solutionsScoped
                  stateSafe.solutionsBounded schemeWF
              have argsWF : ∀ arg ∈ fresh.2,
                  (arg.realize valuation).WF rigidCount 0 := by
                intro arg member
                exact Ty.realize_inferWF
                  (freshSafe.2.1 arg member) valuationWF
              have resultTyEq :
                  ((state.solutions.applyScheme scheme).openWith fresh.2).realize
                      valuation =
                    (scheme.realize valuation).openWith
                      (fresh.2.map (·.realize valuation)) := by
                have opened := Ty.realize_openWith (args := fresh.2) appliedWF
                  (modelWF stateSafe stateModels)
                have appliedEq := stateModels.realize_apply scheme.body
                simpa [PolyTy.openWith, PolyTy.realize, MStore.applyScheme,
                  appliedEq] using opened
              rw [resultTyEq]
              apply Typing.var (scheme := scheme.realize valuation)
                  (args := fresh.2.map (·.realize valuation))
              · simp [Ctx.realize, lookup]
              · exact PolyTy.realize_wf schemeWF
                  (modelWF stateSafe stateModels)
              · simpa using freshSafe.2.2.1
              · intro arg member
                rcases List.mem_map.mp member with ⟨original, originalMem, rfl⟩
                exact argsWF original originalMem
      | lambda ann body =>
          cases inputScoped with
          | lambda annScoped bodyScoped =>
            cases ann with
            | none =>
                simp only [inferFuel] at run
                let seeded := state.freshRequired
                cases bodyRun : inferFuel fuel rigidCount
                    (PolyTy.mono seeded.2 :: ctx) body seeded.1 with
                | none => simp [seeded, bodyRun] at run
                | some bodyResult =>
                    have seededSafe := InferState.freshRequired_safe stateSafe
                    have bodyCtxWF : Ctx.InferWF
                        (PolyTy.mono seeded.2 :: ctx) rigidCount seeded.1.next := by
                      intro scheme member
                      simp only [List.mem_cons] at member
                      rcases member with rfl | member
                      · exact seededSafe.2.1
                      · exact ctx_mono ctxWF seededSafe.2.2 scheme member
                    have bodySound := ih seededSafe.1 bodyCtxWF bodyScoped bodyRun
                    dsimp [seeded] at bodyRun
                    rw [bodyRun] at run
                    have run := Option.some.inj run
                    subst result
                    refine ⟨InferState.freshRequired_refines.trans bodySound.1, ?_⟩
                    intro valuation models
                    have seededModels : seeded.1.Models rigidCount valuation :=
                      bodySound.1 valuation models
                    have paramWF := Ty.realize_inferWF seededSafe.2.1
                      (modelWF seededSafe.1 seededModels)
                    have bodyTyping := bodySound.2 valuation models
                    have annMatches : ParamAnn.Matches none
                        (seeded.2.realize valuation) := by
                      intro template impossible
                      cases impossible
                    have realizedBody : Typing rigidCount
                        (PolyTy.mono (seeded.2.realize valuation) ::
                          ctx.realize valuation) body
                        (bodyResult.ty.realize valuation) := by
                      simpa [Ctx.realize, PolyTy.realize, PolyTy.mono] using
                        bodyTyping
                    have lambdaTyping := Typing.lambda
                      (ann := none) (body := body) (ctx := ctx.realize valuation)
                      (bodyTy := bodyResult.ty.realize valuation)
                      paramWF annMatches realizedBody
                    simp only [Ty.realize]
                    rw [models.realize_apply seeded.2]
                    exact lambdaTyping
            | some template =>
                have templateScoped := annScoped template rfl
                simp only [inferFuel] at run
                let seeded := state.allocate template
                cases bodyRun : inferFuel fuel rigidCount
                    (PolyTy.mono seeded.2 :: ctx) body seeded.1 with
                | none => simp [seeded, bodyRun] at run
                | some bodyResult =>
                    have seededSafe := InferState.allocate_safe stateSafe templateScoped
                    have bodyCtxWF : Ctx.InferWF
                        (PolyTy.mono seeded.2 :: ctx) rigidCount seeded.1.next := by
                      intro scheme member
                      simp only [List.mem_cons] at member
                      rcases member with rfl | member
                      · exact seededSafe.2.1
                      · exact ctx_mono ctxWF seededSafe.2.2 scheme member
                    have bodySound := ih seededSafe.1 bodyCtxWF bodyScoped bodyRun
                    dsimp [seeded] at bodyRun
                    rw [bodyRun] at run
                    have run := Option.some.inj run
                    subst result
                    refine ⟨InferState.allocate_refines.trans bodySound.1, ?_⟩
                    intro valuation models
                    have seededModels : seeded.1.Models rigidCount valuation :=
                      bodySound.1 valuation models
                    have paramWF := Ty.realize_inferWF seededSafe.2.1
                      (modelWF seededSafe.1 seededModels)
                    have bodyTyping := bodySound.2 valuation models
                    have annMatches : ParamAnn.Matches (some template)
                        (seeded.2.realize valuation) := by
                      intro candidate annEq
                      cases annEq
                      exact Template.allocate_matches_realize templateScoped
                    have realizedBody : Typing rigidCount
                        (PolyTy.mono (seeded.2.realize valuation) ::
                          ctx.realize valuation) body
                        (bodyResult.ty.realize valuation) := by
                      simpa [Ctx.realize, PolyTy.realize, PolyTy.mono] using
                        bodyTyping
                    have lambdaTyping := Typing.lambda
                      (ann := some template) (body := body)
                      (bodyTy := bodyResult.ty.realize valuation)
                      (ctx := ctx.realize valuation) paramWF annMatches realizedBody
                    simp only [Ty.realize]
                    rw [models.realize_apply seeded.2]
                    exact lambdaTyping
      | app function argument =>
          cases inputScoped with
          | app functionScoped argumentScoped =>
            simp only [inferFuel] at run
            cases functionRun : inferFuel fuel rigidCount ctx function state with
            | none => simp [functionRun] at run
            | some functionResult =>
              have functionSafe := inferFuel_safe stateSafe ctxWF
                functionScoped functionRun
              have functionSound := ih stateSafe ctxWF functionScoped functionRun
              have argumentCtxWF := ctx_mono ctxWF functionSafe.2.2
              cases argumentRun : inferFuel fuel rigidCount ctx argument
                  functionResult.state with
              | none => simp [functionRun, argumentRun] at run
              | some argumentResult =>
                have argumentSafe := inferFuel_safe functionSafe.1 argumentCtxWF
                  argumentScoped argumentRun
                have argumentSound := ih functionSafe.1 argumentCtxWF
                  argumentScoped argumentRun
                let fresh := argumentResult.state.fresh
                have freshSafe := InferState.fresh_safe argumentSafe.1
                have functionTyWF : functionResult.ty.InferWF rigidCount 0
                    fresh.1.next := inferWF_mono functionSafe.2.1
                      (le_trans argumentSafe.2.2 freshSafe.2.2)
                have argumentTyWF : argumentResult.ty.InferWF rigidCount 0
                    fresh.1.next := inferWF_mono argumentSafe.2.1 freshSafe.2.2
                have arrowWF : (Ty.arrow argumentResult.ty fresh.2).InferWF
                    rigidCount 0 fresh.1.next := by
                  exact ⟨.arrow argumentTyWF.1 freshSafe.2.1.1,
                    by
                      intro id member
                      simp only [Ty.mvars, List.mem_dedup, List.mem_append] at member
                      exact member.elim (argumentTyWF.2 id) (freshSafe.2.1.2 id)⟩
                cases checkedRun : fresh.1.constrain functionResult.ty
                    (.arrow argumentResult.ty fresh.2) with
                | none =>
                    dsimp [fresh] at checkedRun
                    simp [functionRun, argumentRun, checkedRun] at run
                | some checked =>
                    dsimp [fresh] at checkedRun
                    have checkedSafe := InferState.constrain_safe freshSafe.1
                      functionTyWF arrowWF checkedRun
                    have resultEq : result =
                        ⟨checked, checked.solutions.apply fresh.2⟩ := by
                      simpa [functionRun, argumentRun, checkedRun] using run.symm
                    subst result
                    have checkedRefines : fresh.1.Refines checked rigidCount :=
                      InferState.constrain_refines freshSafe.1 checkedRun
                    refine ⟨functionSound.1.trans <| argumentSound.1.trans <|
                      InferState.fresh_refines.trans checkedRefines, ?_⟩
                    intro valuation models
                    have argumentModels : argumentResult.state.Models
                        rigidCount valuation :=
                      (InferState.fresh_refines.trans checkedRefines) valuation models
                    have functionModels : functionResult.state.Models
                        rigidCount valuation := argumentSound.1 valuation argumentModels
                    have functionTyping := functionSound.2 valuation functionModels
                    have argumentTyping := argumentSound.2 valuation argumentModels
                    have checkedEq := checkedSafe.2.2.2
                    have semanticEq := congrArg (Ty.realize valuation) checkedEq
                    rw [models.realize_apply functionResult.ty,
                      models.realize_apply (.arrow argumentResult.ty fresh.2)] at semanticEq
                    simp only [Ty.realize] at semanticEq
                    rw [semanticEq] at functionTyping
                    have applied := Typing.app functionTyping argumentTyping
                    rw [models.realize_apply fresh.2]
                    exact applied
      | letIn ann rhs body =>
          cases ann with
          | none =>
            cases inputScoped with
            | letMono rhsScoped bodyScoped =>
              simp only [inferFuel] at run
              cases rhsRun : inferFuel fuel rigidCount ctx rhs state with
              | none => simp [rhsRun] at run
              | some rhsResult =>
                have rhsSafe := inferFuel_safe stateSafe ctxWF rhsScoped rhsRun
                have rhsSound := ih stateSafe ctxWF rhsScoped rhsRun
                let rhsTy := rhsResult.state.solutions.apply rhsResult.ty
                have rhsTyWF : rhsTy.InferWF rigidCount 0 rhsResult.state.next :=
                  MStore.apply_inferWF rhsSafe.1.solutionsScoped
                    rhsSafe.1.solutionsBounded rhsSafe.2.1
                have bodyCtxWF : Ctx.InferWF (PolyTy.mono rhsTy :: ctx)
                    rigidCount rhsResult.state.next := by
                  intro scheme member
                  simp only [List.mem_cons] at member
                  rcases member with rfl | member
                  · exact rhsTyWF
                  · exact ctx_mono ctxWF rhsSafe.2.2 scheme member
                have bodyRun : inferFuel fuel rigidCount
                    (PolyTy.mono rhsTy :: ctx) body rhsResult.state = some result := by
                  simpa [rhsTy, rhsRun] using run
                have bodySound := ih rhsSafe.1 bodyCtxWF bodyScoped bodyRun
                refine ⟨rhsSound.1.trans bodySound.1, ?_⟩
                intro valuation models
                have rhsModels := bodySound.1 valuation models
                have rhsTyping := rhsSound.2 valuation rhsModels
                have bodyTyping := bodySound.2 valuation models
                have rhsSemanticWF := Ty.realize_inferWF rhsSafe.2.1
                  (modelWF rhsSafe.1 rhsModels)
                apply Typing.letMono rhsSemanticWF rhsTyping
                have rhsEq := rhsModels.realize_apply rhsResult.ty
                simpa [rhsTy, Ctx.realize, PolyTy.realize, PolyTy.mono,
                  rhsEq] using bodyTyping
          | some written =>
            cases inputScoped with
            | letPoly writtenScoped rhsScoped bodyScoped =>
              simp only [inferFuel] at run
              let localStart := state.next
              let count := written.paramCount
              let openedTemplate :=
                written.body.openRigidsFrom 0 rigidCount count
              have openedTemplateScoped :
                  openedTemplate.Scoped (rigidCount + count) 0 := by
                simpa [openedTemplate, Nat.zero_add] using
                  (Template.openRigidsFrom_scoped
                    (rigidCount := rigidCount) (depth := 0)
                    (count := count) writtenScoped)
              have localStateSafe : state.Safe (rigidCount + count) :=
                state_mono_rigid stateSafe (by omega)
              let seeded := state.allocate openedTemplate
              have seededSafe := InferState.allocate_safe localStateSafe
                openedTemplateScoped
              have openedRhsScoped :
                  (rhs.openRigids rigidCount count).TypeScoped
                    (rigidCount + count) 0 := by
                simpa [Expr.openRigids, count, Nat.zero_add] using
                  (Expr.openRigidsFrom_typeScoped
                    (rigidCount := rigidCount) (depth := 0)
                    (count := count) rhsScoped)
              have rhsCtxWF : ctx.InferWF (rigidCount + count) seeded.1.next :=
                ctx_mono (ctx_mono_rigid ctxWF (by omega)) seededSafe.2.2
              cases rhsRun : inferFuel fuel (rigidCount + count) ctx
                  (rhs.openRigids rigidCount count) seeded.1 with
              | none =>
                  dsimp [seeded, openedTemplate, count] at rhsRun
                  simp [rhsRun] at run
              | some rhsResult =>
                  dsimp [seeded, openedTemplate, count] at rhsRun
                  have rhsSafe := inferFuel_safe seededSafe.1 rhsCtxWF
                    openedRhsScoped rhsRun
                  have rhsSound := ih seededSafe.1 rhsCtxWF openedRhsScoped rhsRun
                  have seededTyAtRhs : seeded.2.InferWF
                      (rigidCount + count) 0 rhsResult.state.next :=
                    inferWF_mono seededSafe.2.1 rhsSafe.2.2
                  cases checkedRun : rhsResult.state.constrain
                      rhsResult.ty seeded.2 with
                  | none =>
                      dsimp [seeded, openedTemplate, count] at checkedRun
                      simp [rhsRun, checkedRun] at run
                  | some checked =>
                      dsimp [seeded, openedTemplate, count] at checkedRun
                      have checkedSafe := InferState.constrain_safe rhsSafe.1
                        rhsSafe.2.1 seededTyAtRhs checkedRun
                      have checkedRefines : rhsResult.state.Refines checked
                          (rigidCount + count) :=
                        InferState.constrain_refines rhsSafe.1 checkedRun
                      simp [rhsRun, checkedRun] at run
                      rcases run with ⟨completionProof, obligationsProof,
                        schemeWFB, escapeRaw, bodyRunRaw⟩
                      let completedOpen := checked.solutions.apply seeded.2
                      let completed : PolyTy :=
                        ⟨count, completedOpen.closeRigids rigidCount count⟩
                      let projected := checked.solutions.take localStart
                      have escape : MStore.safeToLeave rigidCount
                          localStart projected = true := by
                        simpa [projected, localStart] using escapeRaw
                      have localStartLe : localStart ≤ checked.solutions.length := by
                        rw [checkedSafe.1.solutions_length, checkedSafe.2.1]
                        exact le_trans seededSafe.2.2 rhsSafe.2.2
                      have projectedSafe := MStore.take_safe localStartLe
                        checkedSafe.1.solutionsNormalized escape
                      let outerState : InferState :=
                        { next := localStart
                          solutions := projected
                          required := checked.required.filter (· < localStart) }
                      have outerSafe : outerState.Safe rigidCount := by
                        refine ⟨?_, ?_, ?_, ?_, ?_⟩
                        · simpa [outerState, projected] using projectedSafe.1
                        · simpa [outerState, projected] using projectedSafe.2.1
                        · simpa [outerState, projected] using projectedSafe.2.2.1
                        · simpa [outerState, projected] using projectedSafe.2.2.2
                        · intro id member
                          have filtered := List.mem_filter.mp member
                          simpa [outerState] using filtered.2
                      have completedWFB : completed.wfB rigidCount = true := by
                        simpa [completed, completedOpen, count] using schemeWFB
                      have completedParts :
                          completed.body.scopedB rigidCount
                              completed.paramCount = true ∧
                            completed.body.metaFreeB = true := by
                        simpa [PolyTy.wfB, Bool.and_eq_true] using completedWFB
                      have completedScoped :
                          completed.body.Scoped rigidCount completed.paramCount :=
                        Ty.scopedB_eq_true_iff.mp completedParts.1
                      have completedFree : completed.body.MetaFree :=
                        Ty.metaFreeB_eq_true_iff.mp completedParts.2
                      have completedWF : completed.WF rigidCount :=
                        ⟨completedScoped, completedFree⟩
                      have bodyCtxWF : Ctx.InferWF (completed :: ctx)
                          rigidCount outerState.next := by
                        intro scheme member
                        simp only [List.mem_cons] at member
                        rcases member with rfl | member
                        · exact wf_inferWF completedWF
                        · simpa [outerState, localStart] using ctxWF scheme member
                      have bodyRun : inferFuel fuel rigidCount
                          (completed :: ctx) body outerState = some result := by
                        simpa [completed, completedOpen, count, outerState,
                          projected, localStart] using bodyRunRaw
                      have bodySound := ih outerSafe bodyCtxWF bodyScoped bodyRun
                      have outerRefines : state.Refines outerState rigidCount := by
                        intro outerVal outerModels
                        obtain ⟨localVal, localModels, agree⟩ :=
                          MStore.Models.extend_checkedPrefix localStartLe
                            checkedSafe.1.solutionsScoped
                            (by simpa [checkedSafe.1.solutions_length] using
                              checkedSafe.1.solutionsBounded)
                            checkedSafe.1.solutionsNormalized escape outerModels
                        have checkedToState : state.Refines checked
                            (rigidCount + count) :=
                          InferState.allocate_refines.trans <|
                            rhsSound.1.trans checkedRefines
                        have localStateModels := checkedToState localVal localModels
                        have outerWF : outerVal.WF rigidCount state.next := by
                          simpa [outerState, projected, localStart,
                            projectedSafe.1] using outerModels.valuationWF
                        constructor
                        · simpa [stateSafe.solutions_length] using outerWF
                        · intro id idLt
                          have idOuter : id < localStart := by
                            simpa [localStart, stateSafe.solutions_length] using idLt
                          have localEq := localStateModels.equation id (by
                            simpa [stateSafe.solutions_length] using idLt)
                          have entryBounded := stateSafe.solutionsBounded
                            state.solutions[id] (List.getElem_mem ..)
                          calc
                            outerVal id = localVal id := (agree id idOuter).symm
                            _ = state.solutions[id].realize localVal := localEq
                            _ = state.solutions[id].realize outerVal :=
                              Ty.realize_eq_of_agree entryBounded agree
                      refine ⟨outerRefines.trans bodySound.1, ?_⟩
                      intro outerVal finalModels
                      have outerModels := bodySound.1 outerVal finalModels
                      obtain ⟨localVal, localModels, agree⟩ :=
                        MStore.Models.extend_checkedPrefix localStartLe
                          checkedSafe.1.solutionsScoped
                          (by simpa [checkedSafe.1.solutions_length] using
                            checkedSafe.1.solutionsBounded)
                          checkedSafe.1.solutionsNormalized escape outerModels
                      have rhsModels := checkedRefines localVal localModels
                      have rhsTyping := rhsSound.2 localVal rhsModels
                      have ctxEq : ctx.realize localVal = ctx.realize outerVal :=
                        Ctx.realize_eq_of_agree
                          (fun scheme member => (ctxWF scheme member).2) agree
                      rw [ctxEq] at rhsTyping
                      have checkedEq := checkedSafe.2.2.2
                      have semanticEq := congrArg (Ty.realize localVal) checkedEq
                      rw [localModels.realize_apply rhsResult.ty,
                        localModels.realize_apply seeded.2] at semanticEq
                      rw [semanticEq] at rhsTyping
                      have completedOpenScoped : completedOpen.Scoped
                          (rigidCount + count) 0 := by
                        apply Ty.scopedB_eq_true_iff.mp
                        simpa [completedOpen, count] using completionProof.2
                      have completedOpenFree : completedOpen.MetaFree := by
                        apply Ty.metaFreeB_eq_true_iff.mp
                        simpa [completedOpen] using completionProof.1
                      have seedEqOpen : seeded.2.realize localVal = completedOpen := by
                        calc
                          seeded.2.realize localVal =
                              completedOpen.realize localVal :=
                            (localModels.realize_apply seeded.2).symm
                          _ = completedOpen := Ty.realize_eq_self
                            completedOpenFree localVal
                      have rhsExpected : Typing (rigidCount + count)
                          (ctx.realize outerVal) (rhs.openRigids rigidCount count)
                          (completed.openRigids rigidCount) := by
                        rw [PolyTy.openRigids_closeRigids completedOpenScoped]
                        simpa [seedEqOpen] using rhsTyping
                      have openedMatches : openedTemplate.Matches
                          (seeded.2.realize localVal) :=
                        Template.allocate_matches_realize
                          (valuation := localVal) (frontier := localStart)
                            openedTemplateScoped
                      rw [seedEqOpen] at openedMatches
                      have writtenBodyScoped : written.body.Scoped
                          rigidCount count := by
                        simpa [count] using writtenScoped
                      have closedMatches := Template.matches_closeRigids
                        writtenBodyScoped completedOpenScoped openedMatches
                      have schemeMatches : SchemeTemplateMatches written completed :=
                        ⟨rfl, by simpa [completed, completedOpen, count] using
                          closedMatches⟩
                      have bodyTyping := bodySound.2 outerVal finalModels
                      apply Typing.letPoly schemeMatches completedWF
                      · apply Ctx.realize_wf ctxWF
                        have outerValWF : outerVal.WF rigidCount outerState.next :=
                          modelWF (candidate := outerState) outerSafe outerModels
                        simpa [outerState, localStart] using outerValWF
                      · simpa [completed, count] using rhsScoped
                      · exact rhsExpected
                      · simpa [Ctx.realize, PolyTy.realize,
                          Ty.realize_eq_self completedWF.2 outerVal] using bodyTyping
      | fix ann body =>
          cases inputScoped with
          | fix annScoped bodyScoped =>
            simp only [inferFuel] at run
            let seeded := state.allocate ann
            have seededSafe := InferState.allocate_safe stateSafe annScoped
            have bodyCtxWF : Ctx.InferWF (PolyTy.mono seeded.2 :: ctx)
                rigidCount seeded.1.next := by
              intro scheme member
              simp only [List.mem_cons] at member
              rcases member with rfl | member
              · exact seededSafe.2.1
              · exact ctx_mono ctxWF seededSafe.2.2 scheme member
            cases bodyRun : inferFuel fuel rigidCount
                (PolyTy.mono seeded.2 :: ctx) body seeded.1 with
            | none =>
                dsimp [seeded] at bodyRun
                simp [bodyRun] at run
            | some bodyResult =>
                dsimp [seeded] at bodyRun
                rw [bodyRun] at run
                change (bodyResult.state.constrain bodyResult.ty
                  (state.allocate ann).2).bind (fun checked =>
                    some ⟨checked, checked.solutions.apply (state.allocate ann).2⟩) =
                      some result at run
                have bodySafe := inferFuel_safe seededSafe.1 bodyCtxWF
                  bodyScoped bodyRun
                have bodySound := ih seededSafe.1 bodyCtxWF bodyScoped bodyRun
                have selfWF : seeded.2.InferWF rigidCount 0 bodyResult.state.next :=
                  inferWF_mono seededSafe.2.1 bodySafe.2.2
                cases checkedRun : bodyResult.state.constrain
                    bodyResult.ty (state.allocate ann).2 with
                | none =>
                    rw [checkedRun] at run
                    simp at run
                | some checked =>
                    have checkedSafe := InferState.constrain_safe bodySafe.1
                      bodySafe.2.1 selfWF (by simpa [seeded] using checkedRun)
                    rw [checkedRun] at run
                    simp only [Option.bind_some, Option.some.injEq] at run
                    subst result
                    have checkedRefines : bodyResult.state.Refines checked rigidCount :=
                      InferState.constrain_refines bodySafe.1 (by
                        simpa [seeded] using checkedRun)
                    refine ⟨InferState.allocate_refines.trans <|
                      bodySound.1.trans checkedRefines, ?_⟩
                    intro valuation models
                    have bodyModels := checkedRefines valuation models
                    have bodyTyping := bodySound.2 valuation bodyModels
                    have checkedEq := checkedSafe.2.2.2
                    have semanticEq := congrArg (Ty.realize valuation) checkedEq
                    rw [models.realize_apply bodyResult.ty,
                      models.realize_apply seeded.2] at semanticEq
                    rw [semanticEq] at bodyTyping
                    have selfAtChecked : seeded.2.InferWF rigidCount 0 checked.next := by
                      rw [checkedSafe.2.1]
                      exact selfWF
                    have selfSemanticWF := Ty.realize_inferWF selfAtChecked
                      (modelWF checkedSafe.1 models)
                    have annMatches : ann.Matches
                        (seeded.2.realize valuation) := by
                      exact Template.allocate_matches_realize
                        (valuation := valuation) (frontier := state.next) annScoped
                    have realizedBody : Typing rigidCount
                        (PolyTy.mono (seeded.2.realize valuation) ::
                          ctx.realize valuation) body
                        (seeded.2.realize valuation) := by
                      simpa [Ctx.realize, PolyTy.realize, PolyTy.mono] using
                        bodyTyping
                    have fixTyping := Typing.fix selfSemanticWF annMatches realizedBody
                    change Typing rigidCount (ctx.realize valuation)
                      (.fix ann body)
                      ((checked.solutions.apply seeded.2).realize valuation)
                    rw [models.realize_apply seeded.2]
                    exact fixTyping

/-- Every successful public inference result belongs to the declarative source
typing relation. -/
theorem infer_sound
    {input : Source} {result : InferenceResult}
    (run : infer input = some result) :
    Typing 0 [] input result.ty := by
  unfold infer at run
  by_cases sourceBad : (!input.typeScopedB 0 0) = true
  · rw [if_pos sourceBad] at run
    simp at run
  · rw [if_neg sourceBad] at run
    cases internalRun : inferFuel (input.inferSize + 1) 0 [] input
        ⟨0, [], []⟩ with
    | none => simp [internalRun] at run
    | some internal =>
        rw [internalRun] at run
        by_cases finalGood : (internal.state.solvedB 0 &&
            (internal.state.solutions.apply internal.ty).wfB 0 0) = true
        · simp at run
          rcases run with ⟨guardParts, resultEq⟩
          cases resultEq
          have sourceScopedB : input.typeScopedB 0 0 = true := by
            cases sourceEq : input.typeScopedB 0 0 <;> simp_all
          have inputScoped : input.TypeScoped 0 0 :=
            Expr.typeScopedB_eq_true_iff.mp sourceScopedB
          have initialSafe : (⟨0, [], []⟩ : InferState).Safe 0 :=
            InferState.initial_safe
          have emptyCtxWF : Ctx.InferWF [] 0 0 := by
            simp [Ctx.InferWF]
          have internalSafe := inferFuel_safe initialSafe emptyCtxWF
            inputScoped internalRun
          obtain ⟨valuation, models⟩ :=
            InferState.has_model internalSafe.1
          have typing := (inferFuel_sound_model initialSafe emptyCtxWF
            inputScoped internalRun).2 valuation models
          have publicWF :
              (internal.state.solutions.apply internal.ty).WF 0 0 :=
            Ty.wfB_eq_true_iff.mp guardParts.2
          have resultEq : internal.ty.realize valuation =
              internal.state.solutions.apply internal.ty := by
            calc
              internal.ty.realize valuation =
                  (internal.state.solutions.apply internal.ty).realize valuation :=
                (models.realize_apply internal.ty).symm
              _ = internal.state.solutions.apply internal.ty :=
                Ty.realize_eq_self publicWF.2 valuation
          simpa [Ctx.realize, resultEq] using typing
        · simp at run
          apply False.elim
          apply finalGood
          simpa only [Bool.and_eq_true] using run.1

/-- The public result contains a closed semantic type; in particular it has no
remaining inference metavariables. -/
theorem infer_result_wf
    {input : Source} {result : InferenceResult}
    (run : infer input = some result) :
    result.ty.WF 0 0 := by
  exact Typing.regular (infer_sound run)

end EPL
