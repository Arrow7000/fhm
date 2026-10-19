import FHM.Elaboration.Judgment

namespace Elaboration

def seed (K : List Nat) (frontier : Nat) (ann : Option Template) :
    Option { result : Nat × Ty // Seed K frontier ann result.2 result.1 } :=
  match ann with
  | none => some ⟨(frontier + 1, .fvar frontier), .absent⟩
  | some template =>
      let result := template.allocate frontier
      if hlc : result.2.bvarsBelow 0 = true then
        if hrigid : template.rigidVars.all (fun v => decide (v ∈ K)) = true then
          some ⟨result, .annotated rfl ((Ty.bvarsBelow_iff _).mp hlc)
            (fun v hv => of_decide_eq_true (List.all_eq_true.mp hrigid v hv))⟩
        else none
      else none

def checkLet (K : List Nat) (F : List Ty) (frontier : Nat) (ann : LetAnn) (ty : Ty) :
    Option { result : Nat × Subst // LetCheck K F frontier ty ann result.1 result.2 } :=
  match ann with
  | .absent => some ⟨(frontier, []), .absent⟩
  | .template .hole => some ⟨(frontier, []), .hole⟩
  | .template template =>
      let result := template.allocate frontier
      if hlc : result.2.bvarsBelow 0 = true then
        if hrigid : template.rigidVars.all (fun v => decide (v ∈ K ++ softVars F)) = true then
          match unifyCoreK K ty result.2 with
          | none => none
          | some ⟨subst, hunifies, havoids⟩ =>
              some ⟨(result.1, subst), .template rfl ((Ty.bvarsBelow_iff _).mp hlc)
                (fun v hv => of_decide_eq_true (List.all_eq_true.mp hrigid v hv))
                ⟨hunifies, havoids⟩⟩
        else none
      else none
  | .complete _ | .partialForall _ _ => none

def checkSignature (K : List Nat) (F : List Ty) (written : List Nat) (frontier : Nat) (ann : LetAnn) (ty : Ty) :
    Option { result : Nat × Subst // SignatureCheck K F written frontier ty ann result.1 result.2 } :=
  match ann with
  | .complete scheme =>
    if hwf : scheme.body.bvarsBelow scheme.paramCount = true then
      if hr : scheme.body.freeVars.all (fun v => decide (v ∈ K ++ softVars F)) = true then
        match unifyCoreK (K ++ written) ty (scheme.openVars written) with
        | none => none
        | some ⟨subst, hu, hd⟩ => some ⟨(frontier, subst), .complete
            (PolyTy.wf_iff_bvarsBelow.mp hwf)
            (fun v hv => of_decide_eq_true (List.all_eq_true.mp hr v hv)) ⟨hu, hd⟩⟩
      else none
    else none
  | .partialForall _ template =>
    let expected := (template.openTyVarsFrom 0 written).allocate frontier
    if hlc : expected.2.bvarsBelow 0 = true then
      if hr : template.rigidVars.all (fun v => decide (v ∈ K ++ softVars F)) = true then
        match unifyCoreK (K ++ written) ty expected.2 with
        | none => none
        | some ⟨subst, hu, hd⟩ => some ⟨(expected.1, subst), .partialSignature rfl
            ((Ty.bvarsBelow_iff _).mp hlc)
            (fun v hv => of_decide_eq_true (List.all_eq_true.mp hr v hv)) ⟨hu, hd⟩⟩
      else none
    else none
  | .absent | .template _ => none

private theorem ctxBelow_of_all {ctx : Ctx} {frontier : Nat}
    (h : ctx.env.freeVars.all (fun v => decide (v < frontier)) = true) : CtxBelow frontier ctx := by
  intro scheme hscheme
  apply Ty.BelowFvars.of_freeVars_lt
  intro v hv
  exact of_decide_eq_true (List.all_eq_true.mp h v (Env.mem_freeVars_iff.mpr ⟨scheme, hscheme, hv⟩))

/-- Completed syntax mentioning a live soft slot is inferred structurally;
it must not be sent to the backend, whose annotations are all rigid. -/
def backendInput (K : List Nat) (F : List Ty) (input : Input) :
    Option { core : Expr // input.toCore = some core ∧
      (∀ v ∈ core.tyFreeVars, v ∈ K) ∧ (∀ v ∈ core.tyFreeVars, v ∉ softVars F) } :=
  match _h : input.toCore with
  | none => none
  | some core =>
      if hs : core.tyFreeVars.all (fun v => decide (v ∈ K)) = true then
        if hd : core.tyFreeVars.all (fun v => decide (v ∉ softVars F)) = true then
          some ⟨core, rfl,
            fun v hv => of_decide_eq_true (List.all_eq_true.mp hs v hv),
            fun v hv => of_decide_eq_true (List.all_eq_true.mp hd v hv)⟩
        else none
      else none

structure RecComponentResult where
  frontier : Nat
  subst : Subst
  outputs : List (Option Expr)
  facts : List RecFacts

structure RecRunResult where
  frontier : Nat
  subst : Subst
  state : RecState

mutual
/-- One dispatch path: completed subtrees use the existing verified worker;
partial spines elaborate while inferring. Recursive partial signatures remain
monomorphic until their component is solved and its ordered prefix is validated. -/
def _root_.inferWithTypesCore (K : List Nat) (frontier : Nat) (ctx : Ctx) (input : Input) (F : List Ty := []) :
    Option { result : Nat × Subst × Expr × Ty × InferredNodeTypes × InferredBinderSchemes //
      Infer K F frontier ctx input result.1 result.2.1 result.2.2.1 result.2.2.2.1 } :=
  if hK : K.all (fun v => decide (v < frontier)) = true then
    if hctx : ctx.env.freeVars.all (fun v => decide (v < frontier)) = true then
      if hF : (softVars F).all (fun v => decide (v < frontier)) = true then
        if hsource : input.rigidVars.all (fun v => decide (v ∈ K ++ softVars F)) = true then
          have hrawScope : SourceScope K F input := fun v hv =>
            of_decide_eq_true (List.all_eq_true.mp hsource v hv)
          match hemb : backendInput K F input with
          | some ⟨core, hc, hscope, hdisjoint⟩ =>
              match CoreBackend.inferWithTypesCore K frontier ctx core with
              | none => none
              | some ⟨(next, subst, ty, nodeTypes, schemes), h⟩ =>
                  some ⟨(next, subst, core, ty, nodeTypes, schemes), .backend hc h (ctxBelow_of_all hctx)
                    (fun v hv => of_decide_eq_true (List.all_eq_true.mp hK v hv)) hscope hdisjoint⟩
          | none =>
              match input with
              | .lambda ann body =>
                  match seed (K ++ softVars F) frontier ann with
                  | none => none
                  | some ⟨(initial, param), hs⟩ =>
                      match inferWithTypesCore K initial { ctx with env := PolyTy.mkTrivial param :: ctx.env } body F with
                      | none => none
                      | some ⟨(next, subst, completed, bodyTy, bodyTypes, bodySchemes), hb⟩ =>
                          let ty := .arrow (subst.onTy param) bodyTy
                          some ⟨(next, subst, lambdaOutput ann param subst completed, ty,
                            .root ty ++ bodyTypes.below .lambdaBody, bodySchemes.below .lambdaBody), .lambda hrawScope hs hb⟩
              | .app f arg =>
                  match inferWithTypesCore K frontier ctx f F with
                  | none => none
                  | some ⟨(first, s1, fOut, fTy, fTypes, fSchemes), hf⟩ =>
                      match inferWithTypesCore K first (s1.onCtx ctx) (arg.substTyFvars s1) (substSoft s1 F) with
                      | none => none
                      | some ⟨(second, s2, argOut, argTy, argTypes, argSchemes), ha⟩ =>
                          match unifyCoreK K (s2.onTy fTy) (.arrow argTy (.fvar second)) with
                          | none => none
                          | some ⟨s3, hu, hd⟩ =>
                              let ty := s3.onTy (.fvar second)
                              some ⟨(second + 1, s1 ++ s2 ++ s3,
                                .app (fOut.substTyFvars (s2 ++ s3)) (argOut.substTyFvars s3), ty,
                                .root ty ++ (fTypes.onSubst (s2 ++ s3)).below .appFun ++
                                  (argTypes.onSubst s3).below .appArg,
                                (fSchemes.onSubst (s2 ++ s3)).below .appFun ++
                                  (argSchemes.onSubst s3).below .appArg), .app hrawScope hf ha ⟨hu, hd⟩⟩
              | .letIn ann rhs body =>
                if ann.isSignature then
                  let written := freshVars frontier ann.paramCount
                  if hraw : rhs.rigidVars.all (fun v => decide (v ∈ K ++ softVars F)) = true then
                    match inferWithTypesCore (K ++ written) (frontier + ann.paramCount) ctx (rhs.openTyVars written) F with
                    | none => none
                    | some ⟨(first, s1, rhsOut, rhsTy, rhsTypes, rhsSchemes), hr⟩ =>
                      match checkSignature K (substSoft s1 F) written first (ann.substTyFvars s1) rhsTy with
                      | none => none
                      | some ⟨(checked, sCheck), hc⟩ =>
                        let checkedCtx := sCheck.onCtx (s1.onCtx ctx)
                        let checkedTy := sCheck.onTy rhsTy
                        let checkedOut := rhsOut.substTyFvars sCheck
                        let scheme := signatureScheme (ann.substTyFvars (s1 ++ sCheck)) (K ++ softVars (substSoft (s1 ++ sCheck) F)) written checkedCtx checkedTy
                        let names := signatureNames (ann.substTyFvars (s1 ++ sCheck)) (K ++ softVars (substSoft (s1 ++ sCheck) F)) written checkedCtx checkedTy
                        if hescape : ∀ name ∈ written, name ∉ checkedCtx.env.freeVars ++ softVars (substSoft (s1 ++ sCheck) F) then
                          match inferWithTypesCore K checked { checkedCtx with env := scheme :: checkedCtx.env } (body.substTyFvars (s1 ++ sCheck)) (substSoft (s1 ++ sCheck) F) with
                          | none => none
                          | some ⟨(next, s2, bodyOut, bodyTy, bodyTypes, bodySchemes), hb⟩ =>
                            let rhsFinalTypes := (((rhsTypes.onSubst sCheck).closeTyVars written).onSubst s2)
                              |>.underTyBinders ann.paramCount |>.below .letRhs
                            let rhsFinalSchemes := (((rhsSchemes.onSubst sCheck).closeTyVars written).onSubst s2)
                              |>.underTyBinders ann.paramCount |>.below .letRhs
                            let inferred : InferredBinderSchemes := match ann with
                              | .partialForall _ _ => [{ site := .letIn [], scheme := s2.onPolyTy scheme, tyDepth := 0 }]
                              | _ => []
                            some ⟨(next, s1 ++ sCheck ++ s2, letOutput scheme names checkedOut bodyOut s2, bodyTy,
                              .root bodyTy ++ rhsFinalTypes ++ bodyTypes.below .letBody,
                              inferred ++ rhsFinalSchemes ++ bodySchemes.below .letBody),
                              .letSignature hrawScope rfl (fun name hn hk => by
                                have hlt : name < frontier := by
                                  rcases List.mem_append.mp hk with hk | hk
                                  · exact of_decide_eq_true (List.all_eq_true.mp hK name hk)
                                  · exact of_decide_eq_true (List.all_eq_true.mp hF name hk)
                                have hge := freshVars_ge name hn
                                omega)
                                (fun v hv => of_decide_eq_true (List.all_eq_true.mp hraw v hv)) hr hc hescape hb⟩
                        else none
                  else none
                else
                      match inferWithTypesCore K frontier ctx rhs F with
                      | none => none
                      | some ⟨(first, s1, rhsOut, rhsTy, rhsTypes, rhsSchemes), hr⟩ =>
                          match checkLet K (substSoft s1 F) first (ann.substTyFvars s1) rhsTy with
                          | none => none
                          | some ⟨(checked, sCheck), hc⟩ =>
                              let checkedCtx := sCheck.onCtx (s1.onCtx ctx)
                              let checkedTy := sCheck.onTy rhsTy
                              let checkedOut := rhsOut.substTyFvars sCheck
                              let scheme := genScheme (K ++ softVars (substSoft (s1 ++ sCheck) F)) checkedCtx.env checkedTy
                              let names := genVars (K ++ softVars (substSoft (s1 ++ sCheck) F)) checkedCtx.env checkedTy
                              match inferWithTypesCore K checked { checkedCtx with env := scheme :: checkedCtx.env } (body.substTyFvars (s1 ++ sCheck)) (substSoft (s1 ++ sCheck) F) with
                              | none => none
                              | some ⟨(next, s2, bodyOut, bodyTy, bodyTypes, bodySchemes), hb⟩ =>
                                  let binder : InferredBinderScheme :=
                                    { site := .letIn [], scheme := s2.onPolyTy scheme, tyDepth := 0 }
                                  some ⟨(next, s1 ++ sCheck ++ s2,
                                    letOutput scheme names checkedOut bodyOut s2, bodyTy,
                                    .root bodyTy ++ (rhsTypes.onSubst (sCheck ++ s2)).below .letRhs ++
                                      bodyTypes.below .letBody,
                                    binder :: (rhsSchemes.onSubst (sCheck ++ s2)).below .letRhs ++
                                      bodySchemes.below .letBody), .letIn hrawScope hr hc hb⟩
              | .match_ scrut branches =>
                  match inferWithTypesCore K frontier ctx scrut F with
                  | none => none
                  | some ⟨(first, s1, scrutOut, scrutTy, scrutTypes, scrutSchemes), hs⟩ =>
                    match hh : branches.head? with
                    | none => none
                    | some _ =>
                      match inferBranchesWithTypesCore K (first + 1) (s1.onCtx ctx)
                          scrutTy (.fvar first) 0 (substInputBranches s1 branches) (substSoft s1 F) with
                      | none => none
                      | some ⟨(next, s2, branchOut, branchTypes, branchSchemes), hb⟩ =>
                        let ty := s2.onTy (.fvar first)
                        some ⟨(next, s1 ++ s2, .match_ (scrutOut.substTyFvars s2) branchOut, ty,
                          .root ty ++ (scrutTypes.onSubst s2).below .matchScrut ++ branchTypes,
                          (scrutSchemes.onSubst s2).below .matchScrut ++ branchSchemes),
                          .match_ hrawScope hs (by intro heq; rw [heq] at hh; simp at hh) hb⟩
              | .letRec anns bindings body =>
                  if hwf : anns.all (fun ann => match ann with
                      | .complete scheme => scheme.body.bvarsBelow scheme.paramCount
                      | _ => true) = true then
                    if hg : RecGroups.validResidualGroupsB (anns.map LetAnn.recModeAnn) (bindings.map Input.erase)
                        (RecGroup.inferenceSccs (anns.map LetAnn.recModeAnn) (bindings.map Input.erase)) = true then
                      match inferRecStrataWithTypesCore K F (frontier + bindings.length) ctx anns bindings
                          (RecState.init frontier anns)
                          (RecGroup.inferenceSccs (anns.map LetAnn.recModeAnn) (bindings.map Input.erase)) with
                      | none => none
                      | some ⟨strata, hs⟩ =>
                        match inferRecSignedWithTypesCore K (substSoft strata.subst F) 0 strata.frontier
                            (strata.subst.onCtx ctx) (anns.map (LetAnn.substTyFvars strata.subst))
                            (bindings.map (Input.substTyFvars strata.subst)) strata.state with
                        | none => none
                        | some ⟨signed, hp⟩ =>
                          match collectRecValues signed.state.exports, collectRecValues signed.state.outputs with
                          | some ⟨schemes, hschemes⟩, some ⟨outputs, houtputs⟩ =>
                            let solved := strata.subst ++ signed.subst
                            match inferWithTypesCore K signed.frontier (signed.state.rhsCtx (solved.onCtx ctx))
                                (body.substTyFvars solved) (substSoft solved F) with
                            | none => none
                            | some ⟨(next, s3, bodyOut, bodyTy, bodyTypes, bodySchemes), hb⟩ =>
                              let final := signed.state.onSubst s3
                              let finalSchemes := schemes.map s3.onPolyTy
                              some ⟨(next, strata.subst ++ signed.subst ++ s3,
                                .letRec (finalSchemes.map some) (outputs.map (Expr.substTyFvars s3)) bodyOut,
                                bodyTy, .root bodyTy ++ finalRecNodeTypes anns final ++ bodyTypes.below .letRecBody,
                                inferredRecSchemes anns finalSchemes ++ finalRecBinderSchemes anns final ++
                                  bodySchemes.below .letRecBody),
                                .letRec ⟨hrawScope, ctxBelow_of_all hctx,
                                  (fun v hv => of_decide_eq_true (List.all_eq_true.mp hK v hv)),
                                  (fun v hv => of_decide_eq_true (List.all_eq_true.mp hF v hv))⟩ (fun scheme hmem => PolyTy.wf_iff_bvarsBelow.mp (List.all_eq_true.mp hwf (.complete scheme) hmem))
                                  ⟨RecGroups.validResidualGroupsB_sound hg, rfl⟩ hs hp hschemes houtputs hb⟩
                          | _, _ => none
                    else none
                  else none
              | _ => none
        else none
      else none
    else none
  else none
termination_by (input.size, 0)
decreasing_by all_goals (simp only [Input.size, Input.size_openTyVars, Input.size_substTyFvars, sizeBranches_substInputBranches, sizeBindings_map_substTyFvars]; omega)

def _root_.inferBranchesWithTypesCore (K : List Nat) (Φ : Nat) (ctx : Ctx) (scrutTy : Ty) (ρ : Ty)
    (branchIndex : Nat) (branches : List (MatchPattern × Input)) (F : List Ty := []) :
    Option { r : Nat × Subst × List (MatchPattern × Expr) × InferredNodeTypes × InferredBinderSchemes //
      InferBranches K F Φ ctx scrutTy ρ branches r.1 r.2.1 r.2.2.1 } :=
  if hsource : (rigidBranchVars branches).all (fun v => decide (v ∈ K ++ softVars F)) = true then
    have hrawScope : ∀ v ∈ rigidBranchVars branches, v ∈ K ++ softVars F := fun v hv =>
      of_decide_eq_true (List.all_eq_true.mp hsource v hv)
    match branches with
    | [] => some ⟨(Φ, [], [], [], []), .nil⟩
    | (.wildcard, body) :: rest =>
        match inferWithTypesCore K Φ ctx body F with
        | none => none
        | some ⟨(Φ₁, S₁, bodyOut, τb, bodyTypes, bodySchemes), hbody⟩ =>
          match unifyCoreK K τb (S₁.onTy ρ) with
          | none => none
          | some ⟨S₂, huni, hav₂⟩ =>
            match inferBranchesWithTypesCore K Φ₁ (S₂.onCtx (S₁.onCtx ctx))
                (S₂.onTy (S₁.onTy scrutTy)) (S₂.onTy (S₁.onTy ρ)) (branchIndex + 1) (substInputBranches (S₁ ++ S₂) rest) (substSoft (S₁ ++ S₂) F) with
            | none => none
            | some ⟨(Φ₂, S₃, restOut, restTypes, restSchemes), hrest⟩ =>
              let schemes := (bodySchemes.onSubst (S₂ ++ S₃)).below
                (.matchBranch branchIndex) ++ restSchemes
              let nodeTypes := (bodyTypes.onSubst (S₂ ++ S₃)).below
                (.matchBranch branchIndex) ++ restTypes
              some ⟨(Φ₂, S₁ ++ S₂ ++ S₃,
                  (.wildcard, bodyOut.substTyFvars (S₂ ++ S₃)) :: restOut, nodeTypes, schemes),
                  .consWild hrawScope hbody ⟨huni, hav₂⟩ hrest⟩
    | (.named c n, body) :: rest =>
        match hget : LookupList.get? ctx.ctors c with
        | none => none
        | some ctorr =>
          if hcont : n = ctorr.contents.length then
            match unifyCoreK K scrutTy
                (.customTy ctorr.tyName ((freshVars Φ ctorr.paramCount).map (Ty.fvar ·))) with
            | none => none
            | some ⟨S₀, huni0, hav0⟩ =>
              match inferWithTypesCore K (Φ + ctorr.paramCount)
                  { (S₀.onCtx ctx) with
                    env := (ctorr.contents.map (Ty.openWith
                        (((freshVars Φ ctorr.paramCount).map (Ty.fvar ·)).map S₀.onTy))).map PolyTy.mkTrivial
                      ++ (S₀.onCtx ctx).env }
                  (body.substTyFvars S₀) (substSoft S₀ F) with
              | none => none
              | some ⟨(Φ₁, S₁, bodyOut, τb, bodyTypes, bodySchemes), hbody⟩ =>
                match unifyCoreK K τb (S₁.onTy (S₀.onTy ρ)) with
                | none => none
                | some ⟨S₂, huni, hav₂⟩ =>
                  match inferBranchesWithTypesCore K Φ₁ (S₂.onCtx (S₁.onCtx (S₀.onCtx ctx)))
                      (S₂.onTy (S₁.onTy (S₀.onTy scrutTy))) (S₂.onTy (S₁.onTy (S₀.onTy ρ)))
                      (branchIndex + 1) (substInputBranches (S₀ ++ S₁ ++ S₂) rest) (substSoft (S₀ ++ S₁ ++ S₂) F) with
                  | none => none
                  | some ⟨(Φ₂, S₃, restOut, restTypes, restSchemes), hrest⟩ =>
                    let schemes := (bodySchemes.onSubst (S₂ ++ S₃)).below
                      (.matchBranch branchIndex) ++ restSchemes
                    let nodeTypes := (bodyTypes.onSubst (S₂ ++ S₃)).below
                      (.matchBranch branchIndex) ++ restTypes
                    some ⟨(Φ₂, S₀ ++ S₁ ++ S₂ ++ S₃,
                        (.named c n, bodyOut.substTyFvars (S₂ ++ S₃)) :: restOut, nodeTypes, schemes),
                        .cons hrawScope hget hcont ⟨huni0, hav0⟩ hbody ⟨huni, hav₂⟩ hrest⟩
          else none
  else none
termination_by (sizeBranches branches, 0)
decreasing_by
  all_goals (try simp only [sizeBranches, Input.size_substTyFvars, sizeBranches_substInputBranches]; omega)

/-- One monomorphic component visit, with artifacts in original member order. -/
def _root_.inferRecComponentWithTypesCore (K : List Nat) (F : List Ty) (members : List Nat)
    (index frontier : Nat) (ctx : Ctx) (bindings : List Input) (specs : List RecSpec) :
    Option { result : RecComponentResult // InferRecComponent K F members index frontier ctx bindings specs
      result.frontier result.subst result.outputs result.facts } :=
  match bindings, specs with
  | [], [] => some ⟨⟨frontier, [], [], []⟩, .nil⟩
  | rhs :: rest, .mono expected :: specs =>
      if hm : index ∈ members then
        match inferWithTypesCore K frontier ctx rhs F with
        | none => none
        | some ⟨(first, s1, output, ty, types, schemes), hi⟩ =>
          match unifyCoreK K ty (s1.onTy expected) with
          | none => none
          | some ⟨s2, hu, hav⟩ =>
            match inferRecComponentWithTypesCore K (substSoft (s1 ++ s2) F) members (index + 1) first
                (s2.onCtx (s1.onCtx ctx)) (rest.map (Input.substTyFvars (s1 ++ s2)))
                (specs.map (RecSpec.onSubstSource (s1 ++ s2))) with
            | none => none
            | some ⟨tail, ht⟩ =>
              some ⟨⟨tail.frontier, s1 ++ s2 ++ tail.subst,
                some (output.substTyFvars (s2 ++ tail.subst)) :: tail.outputs,
                (RecFacts.mk types schemes).onSubst (s2 ++ tail.subst) :: tail.facts⟩,
                .consSelected hm hi ⟨hu, hav⟩ ht⟩
      else
        match inferRecComponentWithTypesCore K F members (index + 1) frontier ctx rest specs with
        | none => none
        | some ⟨tail, ht⟩ =>
          some ⟨⟨tail.frontier, tail.subst, none :: tail.outputs, .empty :: tail.facts⟩, .skipMono hm ht⟩
  | _ :: rest, .poly _ :: specs =>
      match inferRecComponentWithTypesCore K F members (index + 1) frontier ctx rest specs with
      | none => none
      | some ⟨tail, ht⟩ =>
        some ⟨⟨tail.frontier, tail.subst, none :: tail.outputs, .empty :: tail.facts⟩, .skipPoly ht⟩
  | _, _ => none
termination_by (sizeBindings bindings, 0)
decreasing_by all_goals (simp only [sizeBindings, sizeBindings_map_substTyFvars]; omega)

/-- Solve shapes and bodies before exporting each SCC. K remains unchanged;
written slots stay flexible until the component's checked solved resolution. -/
def _root_.inferRecStrataWithTypesCore (K : List Nat) (F : List Ty) (frontier : Nat)
    (ctx : Ctx) (anns : List LetAnn) (bindings : List Input) (state : RecState)
    (groups : List (List Nat)) :
    Option { result : RecRunResult // InferRecStrata K F frontier ctx anns bindings state groups
      result.frontier result.subst result.state } :=
  match groups with
  | [] => some ⟨⟨frontier, [], state⟩, .nil⟩
  | component :: rest =>
      match openRecAnns component 0 frontier anns with
      | none => none
      | some ⟨(opened, openings), ho⟩ =>
        let installed := state.installOpenings component openings
        match checkRecShapes K (installed.shapes component openings) with
        | none => none
        | some ⟨pre, hp⟩ =>
          match inferRecComponentWithTypesCore K
              (substSoft pre (F ++ (openings.flatMap RecOpening.written).map Ty.fvar)) component 0 opened
              ((installed.onSubst pre).rhsCtx (pre.onCtx ctx))
              ((openRecSources openings bindings).map (Input.substTyFvars pre))
              (installed.onSubst pre).specs with
          | none => none
          | some ⟨current, hc⟩ =>
            let solved := pre ++ current.subst
            match finishRecComponent K (softVars (substSoft solved F)) component (solved.onCtx ctx)
                (installed.onSubst solved) current.outputs current.facts with
            | none => none
            | some ⟨exported, he⟩ =>
              match inferRecStrataWithTypesCore K (substSoft solved F) current.frontier (solved.onCtx ctx)
                  (anns.map (LetAnn.substTyFvars solved)) (bindings.map (Input.substTyFvars solved))
                  exported rest with
              | none => none
              | some ⟨tail, ht⟩ =>
                some ⟨⟨tail.frontier, pre ++ current.subst ++ tail.subst, tail.state⟩, .cons ho hp hc he ht⟩
termination_by (sizeBindings bindings, groups.length + 1)
decreasing_by
  all_goals (simp only [sizeBindings_map_substTyFvars, sizeBindings_openRecSources, List.length_cons])
  all_goals apply Prod.Lex.right
  all_goals omega

/-- Complete contracts retain polymorphic recursive use and rigid openings. -/
def _root_.inferRecSignedWithTypesCore (K : List Nat) (F : List Ty) (index frontier : Nat)
    (ctx : Ctx) (anns : List LetAnn) (bindings : List Input) (state : RecState) :
    Option { result : RecRunResult // InferRecSigned K F index frontier ctx anns bindings state
      result.frontier result.subst result.state } :=
  match anns, bindings with
  | [], [] => some ⟨⟨frontier, [], state⟩, .nil⟩
  | ann :: anns, rhs :: rest =>
    match ann with
    | .complete scheme =>
      if hwf : scheme.body.bvarsBelow scheme.paramCount = true then
        if hraw : rhs.rigidVars.all (fun v => decide (v ∈ K ++ softVars F)) = true then
          let written := freshVars frontier scheme.paramCount
          match inferWithTypesCore (K ++ written) (frontier + scheme.paramCount)
              (state.rhsCtx ctx) (rhs.openTyVars written) F with
          | none => none
          | some ⟨(first, s1, output, ty, types, schemes), hi⟩ =>
            match unifyCoreK (K ++ written) ty ((s1.onPolyTy scheme).openVars written) with
            | none => none
            | some ⟨s2, hu, hav⟩ =>
              let solved := s1 ++ s2
              let checked := state.onSubst solved
              if he : ∀ y ∈ written,
                  y ∉ (checked.rhsCtx (solved.onCtx ctx)).env.freeVars ++ softVars (substSoft solved F) then
                match inferRecSignedWithTypesCore K (substSoft solved F) (index + 1) first (solved.onCtx ctx)
                    (anns.map (LetAnn.substTyFvars solved)) (rest.map (Input.substTyFvars solved))
                    (checked.setSigned index written (output.substTyFvars s2)
                      ((RecFacts.mk types schemes).onSubst s2)) with
                | none => none
                | some ⟨tail, ht⟩ =>
                  some ⟨⟨tail.frontier, s1 ++ s2 ++ tail.subst, tail.state⟩,
                    .cons (PolyTy.wf_iff_bvarsBelow.mp hwf)
                      (fun v hv => of_decide_eq_true (List.all_eq_true.mp hraw v hv)) hi ⟨hu, hav⟩ he ht⟩
              else none
        else none
      else none
    | .absent | .template _ | .partialForall _ _ =>
      match inferRecSignedWithTypesCore K F (index + 1) frontier ctx anns rest state with
      | none => none
      | some ⟨tail, ht⟩ => some ⟨tail, .skip rfl ht⟩
  | _, _ => none
termination_by (sizeBindings bindings, 0)
decreasing_by all_goals (simp only [sizeBindings, Input.size_openTyVars, sizeBindings_map_substTyFvars]; omega)

end

/-- The plain certificate API projects the one metadata-producing run. -/
def _root_.inferCore (K : List Nat) (frontier : Nat) (ctx : Ctx) (input : Input) :
    Option { result : Nat × Subst × Expr × Ty //
      Infer K [] frontier ctx input result.1 result.2.1 result.2.2.1 result.2.2.2 } :=
  match inferWithTypesCore K frontier ctx input with
  | none => none
  | some ⟨(next, subst, output, ty, _, _), h⟩ => some ⟨(next, subst, output, ty), h⟩

@[simp] theorem _root_.inferCore_isSome (K : List Nat) (frontier : Nat) (ctx : Ctx) (input : Input) :
    (inferCore K frontier ctx input).isSome = (inferWithTypesCore K frontier ctx input).isSome := by
  unfold inferCore
  cases inferWithTypesCore K frontier ctx input with
  | none => rfl
  | some result => rcases result with ⟨⟨next, subst, output, ty, nodes, schemes⟩, h⟩; rfl

/-- Public artifacts and completed ordinary Core come from the same inference. -/
structure _root_.InferenceResult where
  frontier : Nat
  subst : Subst
  completedExpr : Expr
  ty : Ty
  nodeTypes : NodeTypeMap
  binderSchemes : BinderSchemeMap

def Input.freshFloor (input : Input) : Nat := tyVarCeil input.rigidVars

theorem Input.lt_freshFloor {input : Input} {v : Nat} (h : v ∈ input.rigidVars) :
    v < input.freshFloor := lt_tyVarCeil h

def _root_.inferWithTypes (ctors : CtorEnv) (input : Input) : Option InferenceResult :=
  (inferWithTypesCore input.rigidVars input.freshFloor ⟨[], ctors⟩ input).map fun result =>
    { frontier := result.val.1
      subst := result.val.2.1
      completedExpr := result.val.2.2.1
      ty := result.val.2.2.2.1
      nodeTypes := result.val.2.2.2.2.1.toMap
      binderSchemes := result.val.2.2.2.2.2.toMap }

def _root_.principalType (ctors : CtorEnv) (input : Input) : Option Ty :=
  (inferCore input.rigidVars input.freshFloor ⟨[], ctors⟩ input).map (·.val.2.2.2)

def _root_.typecheck (ctors : CtorEnv) (input : Input) : Option PolyTy :=
  (principalType ctors input).map (genScheme [] [])

/-- A public artifact result carries the canonical elaboration derivation. -/
theorem _root_.inferWithTypes_infer {ctors : CtorEnv} {input : Input} {result : InferenceResult}
    (h : inferWithTypes ctors input = some result) :
    Infer input.rigidVars [] input.freshFloor ⟨[], ctors⟩ input result.frontier result.subst
      result.completedExpr result.ty := by
  unfold inferWithTypes at h
  cases hcore : inferWithTypesCore input.rigidVars input.freshFloor ⟨[], ctors⟩ input with
  | none => simp only [hcore, Option.map_none, reduceCtorEq] at h
  | some r =>
    rcases r with ⟨⟨next, subst, output, ty, nodes, schemes⟩, hi⟩
    simp only [hcore, Option.map_some, Option.some.injEq] at h
    subst result
    exact hi


end Elaboration
