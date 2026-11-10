import EPL.Properties.InferenceOpening

namespace EPL

/-- Successful internal inference preserves the dense-state invariant, returns
an allocated/scoped algorithmic type, and never moves the caller's outer
frontier backwards. This is the structural precursor to semantic soundness. -/
theorem inferFuel_safe
    {fuel rigidCount : Nat} {ctx : Ctx} {input : Source}
    {state : InferState} {result : InferResult}
    (stateSafe : state.Safe rigidCount)
    (ctxWF : ctx.InferWF rigidCount state.next)
    (inputScoped : input.TypeScoped rigidCount 0)
    (run : inferFuel fuel rigidCount ctx input state = some result) :
    result.state.Safe rigidCount ∧
      result.ty.InferWF rigidCount 0 result.state.next ∧
      state.next ≤ result.state.next := by
  have scoped_mono_rigid :
      ∀ {ty : Ty} {rigid smaller larger : Nat},
        ty.Scoped smaller rigid → smaller ≤ larger → ty.Scoped larger rigid := by
    intro ty rigid smaller larger h le
    induction h with
    | prim => exact .prim
    | arrow _ _ ihDomain ihCodomain => exact .arrow ihDomain ihCodomain
    | bvar hlt => exact .bvar hlt
    | rigid hlt => exact .rigid (lt_of_lt_of_le hlt le)
    | mvar id => exact .mvar id
  have inferWF_mono :
      ∀ {ty : Ty} {rigid binder smaller larger : Nat},
        ty.InferWF rigid binder smaller → smaller ≤ larger →
          ty.InferWF rigid binder larger := by
    intro ty rigid binder smaller larger h le
    exact ⟨h.1, fun id member => lt_of_lt_of_le (h.2 id member) le⟩
  have inferWF_mono_rigid :
      ∀ {ty : Ty} {binder frontier smaller larger : Nat},
        ty.InferWF smaller binder frontier → smaller ≤ larger →
          ty.InferWF larger binder frontier := by
    intro ty binder frontier smaller larger h le
    exact ⟨scoped_mono_rigid h.1 le, h.2⟩
  have ctx_mono :
      ∀ {context : Ctx} {rigid smaller larger : Nat},
        context.InferWF rigid smaller → smaller ≤ larger →
          context.InferWF rigid larger := by
    intro context rigid smaller larger h le scheme member
    exact inferWF_mono (h scheme member) le
  have ctx_mono_rigid :
      ∀ {context : Ctx} {frontier smaller larger : Nat},
        context.InferWF smaller frontier → smaller ≤ larger →
          context.InferWF larger frontier := by
    intro context frontier smaller larger h le scheme member
    exact inferWF_mono_rigid (h scheme member) le
  have state_mono_rigid :
      ∀ {candidate : InferState} {smaller larger : Nat},
        candidate.Safe smaller → smaller ≤ larger → candidate.Safe larger := by
    intro candidate smaller larger h le
    exact ⟨h.solutions_length,
      (fun ty member => scoped_mono_rigid (h.solutionsScoped ty member) le),
      h.solutionsBounded, h.solutionsNormalized, h.requiredBounded⟩
  have metaFree_bounded :
      ∀ {ty : Ty} {frontier : Nat}, ty.MetaFree → ty.MVarBounded frontier := by
    intro ty frontier h
    induction h with
    | prim => simp [Ty.MVarBounded, Ty.mvars]
    | arrow _ _ ihDomain ihCodomain =>
        intro id member
        simp only [Ty.mvars, List.mem_dedup, List.mem_append] at member
        exact member.elim (ihDomain id) (ihCodomain id)
    | bvar => simp [Ty.MVarBounded, Ty.mvars]
    | rigid => simp [Ty.MVarBounded, Ty.mvars]
  have wf_inferWF :
      ∀ {ty : Ty} {rigid binder frontier : Nat},
        ty.WF rigid binder → ty.InferWF rigid binder frontier := by
    intro ty rigid binder frontier h
    exact ⟨h.1, metaFree_bounded h.2⟩
  have openWith_inferWF :
      ∀ {ty : Ty} {args : List Ty} {rigid count frontier : Nat},
        ty.InferWF rigid count frontier →
        args.length = count →
        (∀ arg ∈ args, arg.InferWF rigid 0 frontier) →
        (ty.openWith args).InferWF rigid 0 frontier := by
    intro ty args rigid count frontier typeWF length argsWF
    induction ty with
    | prim name => exact ⟨.prim, by simp [Ty.openWith, Ty.MVarBounded, Ty.mvars]⟩
    | arrow domain codomain ihDomain ihCodomain =>
        cases typeWF.1 with
        | arrow domainScoped codomainScoped =>
          have domainWF : domain.InferWF rigid count frontier :=
            ⟨domainScoped, fun id member => typeWF.2 id (by
              simp [Ty.mvars, member])⟩
          have codomainWF : codomain.InferWF rigid count frontier :=
            ⟨codomainScoped, fun id member => typeWF.2 id (by
              simp [Ty.mvars, member])⟩
          have domainResult := ihDomain domainWF
          have codomainResult := ihCodomain codomainWF
          exact ⟨Ty.Scoped.arrow domainResult.1 codomainResult.1,
            by
              intro id member
              simp only [Ty.openWith, Ty.mvars, List.mem_dedup,
                List.mem_append] at member
              rcases member with member | member
              · exact domainResult.2 id member
              · exact codomainResult.2 id member⟩
    | bvar index =>
        cases typeWF.1 with
        | bvar hlt =>
          have inArgs : index < args.length := by omega
          rw [Ty.openWith, List.getElem?_eq_getElem inArgs, Option.getD_some]
          exact argsWF args[index] (List.getElem_mem ..)
    | rigid level =>
        cases typeWF.1 with
        | rigid hlt =>
          exact ⟨.rigid hlt,
            by simp [Ty.openWith, Ty.MVarBounded, Ty.mvars]⟩
    | mvar id =>
        exact ⟨.mvar id, typeWF.2⟩
  induction fuel generalizing rigidCount ctx input state result with
  | zero => simp [inferFuel] at run
  | succ fuel ih =>
      cases input with
      | primLit literal =>
          simp only [inferFuel, Option.some.injEq] at run
          subst result
          refine ⟨stateSafe, ?_, le_rfl⟩
          cases literal <;> exact wf_inferWF ⟨.prim, .prim⟩
      | primOp op =>
          simp only [inferFuel, Option.some.injEq] at run
          subst result
          refine ⟨stateSafe, ?_, le_rfl⟩
          cases op
          exact wf_inferWF
            ⟨.arrow .prim (.arrow .prim .prim),
              .arrow .prim (.arrow .prim .prim)⟩
      | var index =>
          simp only [inferFuel] at run
          cases lookup : ctx[index]? with
          | none => simp [lookup] at run
          | some scheme =>
              simp only [lookup] at run
              have schemeMember : scheme ∈ ctx := List.mem_of_getElem? lookup
              have schemeWF := ctxWF scheme schemeMember
              have appliedWF :
                  (state.solutions.applyScheme scheme).InferWF
                    rigidCount state.next := by
                exact MStore.apply_inferWF stateSafe.solutionsScoped
                  stateSafe.solutionsBounded schemeWF
              let fresh := state.freshMany scheme.paramCount
              have freshSafe := InferState.freshMany_safe
                (count := scheme.paramCount) stateSafe
              have appliedMono :
                  (state.solutions.applyScheme scheme).InferWF
                    rigidCount fresh.1.next :=
                inferWF_mono appliedWF freshSafe.2.2.2
              have openedWF :
                  ((state.solutions.applyScheme scheme).openWith fresh.2).InferWF
                    rigidCount 0 fresh.1.next :=
                openWith_inferWF appliedMono freshSafe.2.2.1 freshSafe.2.1
              have resultEq : result =
                  ⟨fresh.1, (state.solutions.applyScheme scheme).openWith fresh.2⟩ := by
                exact Option.some.inj run.symm
              subst result
              exact ⟨freshSafe.1, openedWF, freshSafe.2.2.2⟩
      | lambda ann body =>
          cases inputScoped with
          | lambda annScoped bodyScoped =>
            cases ann with
            | none =>
                simp only [inferFuel] at run
                let seeded := state.freshRequired
                have seededSafe := InferState.freshRequired_safe stateSafe
                have bodyCtxWF :
                    Ctx.InferWF (PolyTy.mono seeded.2 :: ctx)
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
                    simp [bodyRun] at run
                    have bodySafe := ih seededSafe.1 bodyCtxWF bodyScoped bodyRun
                    have paramBefore : seeded.2.InferWF rigidCount 0
                        bodyResult.state.next :=
                      inferWF_mono seededSafe.2.1 bodySafe.2.2
                    have paramAfter := MStore.apply_inferWF
                      bodySafe.1.solutionsScoped bodySafe.1.solutionsBounded
                      paramBefore
                    have resultEq : result =
                        ⟨bodyResult.state,
                          .arrow (bodyResult.state.solutions.apply seeded.2)
                            bodyResult.ty⟩ := by
                      simpa [seeded] using run.symm
                    subst result
                    exact ⟨bodySafe.1,
                      ⟨.arrow paramAfter.1 bodySafe.2.1.1,
                        by
                          intro id member
                          simp only [Ty.mvars, List.mem_dedup,
                            List.mem_append] at member
                          rcases member with member | member
                          · exact paramAfter.2 id member
                          · exact bodySafe.2.1.2 id member⟩,
                      le_trans seededSafe.2.2 bodySafe.2.2⟩
            | some template =>
                have templateScoped := annScoped template rfl
                simp only [inferFuel] at run
                let seeded := state.allocate template
                have seededSafe := InferState.allocate_safe stateSafe templateScoped
                have bodyCtxWF :
                    Ctx.InferWF (PolyTy.mono seeded.2 :: ctx)
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
                    simp [bodyRun] at run
                    have bodySafe := ih seededSafe.1 bodyCtxWF bodyScoped bodyRun
                    have paramBefore : seeded.2.InferWF rigidCount 0
                        bodyResult.state.next :=
                      inferWF_mono seededSafe.2.1 bodySafe.2.2
                    have paramAfter := MStore.apply_inferWF
                      bodySafe.1.solutionsScoped bodySafe.1.solutionsBounded
                      paramBefore
                    have resultEq : result =
                        ⟨bodyResult.state,
                          .arrow (bodyResult.state.solutions.apply seeded.2)
                            bodyResult.ty⟩ := by
                      simpa [seeded] using run.symm
                    subst result
                    exact ⟨bodySafe.1,
                      ⟨.arrow paramAfter.1 bodySafe.2.1.1,
                        by
                          intro id member
                          simp only [Ty.mvars, List.mem_dedup,
                            List.mem_append] at member
                          rcases member with member | member
                          · exact paramAfter.2 id member
                          · exact bodySafe.2.1.2 id member⟩,
                      le_trans seededSafe.2.2 bodySafe.2.2⟩
      | app function argument =>
          cases inputScoped with
          | app functionScoped argumentScoped =>
            simp only [inferFuel] at run
            cases functionRun : inferFuel fuel rigidCount ctx function state with
            | none => simp [functionRun] at run
            | some functionResult =>
                have functionSafe := ih stateSafe ctxWF functionScoped functionRun
                have argumentCtxWF := ctx_mono ctxWF functionSafe.2.2
                cases argumentRun : inferFuel fuel rigidCount ctx argument
                    functionResult.state with
                | none => simp [functionRun, argumentRun] at run
                | some argumentResult =>
                    have argumentSafe := ih functionSafe.1 argumentCtxWF
                      argumentScoped argumentRun
                    let fresh := argumentResult.state.fresh
                    have freshSafe := InferState.fresh_safe argumentSafe.1
                    have functionTyWF : functionResult.ty.InferWF rigidCount 0
                        fresh.1.next :=
                      inferWF_mono functionSafe.2.1
                        (le_trans argumentSafe.2.2 freshSafe.2.2)
                    have argumentTyWF : argumentResult.ty.InferWF rigidCount 0
                        fresh.1.next :=
                      inferWF_mono argumentSafe.2.1 freshSafe.2.2
                    have arrowWF :
                        (Ty.arrow argumentResult.ty fresh.2).InferWF
                          rigidCount 0 fresh.1.next := by
                      exact ⟨.arrow argumentTyWF.1 freshSafe.2.1.1,
                        by
                          intro id member
                          simp only [Ty.mvars, List.mem_dedup,
                            List.mem_append] at member
                          rcases member with member | member
                          · exact argumentTyWF.2 id member
                          · exact freshSafe.2.1.2 id member⟩
                    cases checkedRun : fresh.1.constrain functionResult.ty
                        (.arrow argumentResult.ty fresh.2) with
                    | none =>
                        dsimp [fresh] at checkedRun
                        simp [functionRun, argumentRun, checkedRun] at run
                    | some checked =>
                        dsimp [fresh] at checkedRun
                        simp [functionRun, argumentRun, checkedRun] at run
                        have checkedSafe := InferState.constrain_safe
                          freshSafe.1 functionTyWF arrowWF checkedRun
                        have freshTyAtChecked : fresh.2.InferWF rigidCount 0
                            checked.next := by
                          rw [checkedSafe.2.1]
                          exact freshSafe.2.1
                        have resultTyWF := MStore.apply_inferWF
                          checkedSafe.1.solutionsScoped
                          checkedSafe.1.solutionsBounded freshTyAtChecked
                        have resultEq : result =
                            ⟨checked, checked.solutions.apply fresh.2⟩ := by
                          simpa [fresh] using run.symm
                        subst result
                        refine ⟨checkedSafe.1, resultTyWF, ?_⟩
                        rw [checkedSafe.2.1]
                        exact le_trans functionSafe.2.2
                          (le_trans argumentSafe.2.2 freshSafe.2.2)
      | letIn ann rhs body =>
          cases ann with
          | none =>
              cases inputScoped with
              | letMono rhsScoped bodyScoped =>
                simp only [inferFuel] at run
                cases rhsRun : inferFuel fuel rigidCount ctx rhs state with
                | none => simp [rhsRun] at run
                | some rhsResult =>
                    have rhsSafe := ih stateSafe ctxWF rhsScoped rhsRun
                    let rhsTy := rhsResult.state.solutions.apply rhsResult.ty
                    have rhsTyWF : rhsTy.InferWF rigidCount 0
                        rhsResult.state.next :=
                      MStore.apply_inferWF rhsSafe.1.solutionsScoped
                        rhsSafe.1.solutionsBounded rhsSafe.2.1
                    have bodyCtxWF :
                        Ctx.InferWF (PolyTy.mono rhsTy :: ctx)
                          rigidCount rhsResult.state.next := by
                      intro scheme member
                      simp only [List.mem_cons] at member
                      rcases member with rfl | member
                      · exact rhsTyWF
                      · exact ctx_mono ctxWF rhsSafe.2.2 scheme member
                    have bodyRun : inferFuel fuel rigidCount
                        (PolyTy.mono rhsTy :: ctx) body rhsResult.state =
                          some result := by
                      simpa [rhsTy, rhsRun] using run
                    have bodySafe := ih rhsSafe.1 bodyCtxWF bodyScoped bodyRun
                    exact ⟨bodySafe.1, bodySafe.2.1,
                      le_trans rhsSafe.2.2 bodySafe.2.2⟩
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
                have rhsCtxWF : ctx.InferWF (rigidCount + count)
                    seeded.1.next :=
                  ctx_mono (ctx_mono_rigid ctxWF (by omega)) seededSafe.2.2
                cases rhsRun : inferFuel fuel (rigidCount + count) ctx
                    (rhs.openRigids rigidCount count) seeded.1 with
                | none =>
                    dsimp [seeded, openedTemplate, count] at rhsRun
                    simp [rhsRun] at run
                | some rhsResult =>
                    dsimp [seeded, openedTemplate, count] at rhsRun
                    have rhsSafe := ih seededSafe.1 rhsCtxWF openedRhsScoped rhsRun
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
                        have localStartLe :
                            localStart ≤ checked.solutions.length := by
                          rw [checkedSafe.1.solutions_length,
                            checkedSafe.2.1]
                          exact le_trans seededSafe.2.2 rhsSafe.2.2
                        have projectedSafe := MStore.take_safe
                          localStartLe checkedSafe.1.solutionsNormalized escape
                        let outerState : InferState :=
                          { next := localStart
                            solutions := projected
                            required := checked.required.filter
                              (· < localStart) }
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
                        have bodySafe := ih outerSafe bodyCtxWF bodyScoped bodyRun
                        refine ⟨bodySafe.1, bodySafe.2.1, ?_⟩
                        simpa [outerState, localStart] using bodySafe.2.2
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
                have bodySafe := ih seededSafe.1 bodyCtxWF bodyScoped bodyRun
                have selfAtBody : seeded.2.InferWF rigidCount 0
                    bodyResult.state.next :=
                  inferWF_mono seededSafe.2.1 bodySafe.2.2
                cases checkedRun : bodyResult.state.constrain
                    bodyResult.ty seeded.2 with
                | none =>
                    dsimp [seeded] at checkedRun
                    simp [bodyRun, checkedRun] at run
                | some checked =>
                    dsimp [seeded] at checkedRun
                    simp [bodyRun, checkedRun] at run
                    have checkedSafe := InferState.constrain_safe bodySafe.1
                      bodySafe.2.1 selfAtBody checkedRun
                    have selfAtChecked : seeded.2.InferWF rigidCount 0
                        checked.next := by
                      rw [checkedSafe.2.1]
                      exact selfAtBody
                    have resultTyWF := MStore.apply_inferWF
                      checkedSafe.1.solutionsScoped
                      checkedSafe.1.solutionsBounded selfAtChecked
                    have resultEq : result =
                        ⟨checked, checked.solutions.apply seeded.2⟩ := by
                      simpa [seeded] using run.symm
                    subst result
                    refine ⟨checkedSafe.1, resultTyWF, ?_⟩
                    rw [checkedSafe.2.1]
                    exact le_trans seededSafe.2.2 bodySafe.2.2

end EPL
