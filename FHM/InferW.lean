import FHM.InferInput

/-! The canonical inference judgment, its sole certified worker, and soundness. -/

/-! ## Judgment -/

section

/-! Canonical inference elaborates partial annotations while returning completed
Core. Every input form follows the same recursive inference judgment, including
literals, complete annotations, and partial annotations.
-/

/-- Images of live provisional written-forall slots. They are scoped and
excluded from nested generalization, but are not frozen by unification. -/
def softVars (soft : List Ty) : List Nat := TyList.freeVars soft

def substSoft (subst : Subst) (soft : List Ty) : List Ty := soft.map subst.onTy

@[simp] theorem substSoft_nil (soft : List Ty) : substSoft [] soft = soft := by
  simp [substSoft, Subst.onTy, Ty.substFvars]

@[simp] theorem substSoft_append (first second : Subst) (soft : List Ty) :
    substSoft (first ++ second) soft = substSoft second (substSoft first soft) := by
  simp [substSoft, List.map_map, Function.comp_def, Subst.onTy_append]

theorem mem_softVars_substSoft {subst : Subst} {soft : List Ty} {v : Nat} :
    v ∈ softVars (substSoft subst soft) ↔
      ∃ original ∈ softVars soft, v ∈ (subst.onTy (.fvar original)).freeVars := by
  constructor
  · intro hv
    obtain ⟨ty, hty, hv⟩ := TyList.mem_freeVars_iff.mp hv
    obtain ⟨originalTy, horiginalTy, rfl⟩ := List.mem_map.mp hty
    obtain ⟨original, horiginal, hv⟩ := Ty.mem_freeVars_substFvars_image.mp hv
    exact ⟨original, TyList.mem_freeVars_iff.mpr ⟨originalTy, horiginalTy, horiginal⟩, hv⟩
  · rintro ⟨original, horiginal, hv⟩
    obtain ⟨ty, hty, horiginal⟩ := TyList.mem_freeVars_iff.mp horiginal
    exact TyList.mem_freeVars_iff.mpr ⟨subst.onTy ty, List.mem_map.mpr ⟨ty, hty, rfl⟩,
      Ty.mem_freeVars_substFvars_image.mpr ⟨original, horiginal, hv⟩⟩

theorem scope_image {K : List Nat} {F : List Ty} {subst : Subst} {original v : Nat}
    (hfix : ∀ k ∈ K, subst.onTy (.fvar k) = .fvar k)
    (hscope : original ∈ K ++ softVars F) (hv : v ∈ (subst.onTy (.fvar original)).freeVars) :
    v ∈ K ++ softVars (substSoft subst F) := by
  rcases List.mem_append.mp hscope with hK | hF
  · rw [hfix original hK] at hv
    exact List.mem_append_left _ ((List.mem_singleton.mp hv) ▸ hK)
  · exact List.mem_append_right _ (mem_softVars_substSoft.mpr ⟨original, hF, hv⟩)

def SourceScope (K : List Nat) (F : List Ty) (input : InferInput) : Prop :=
  ∀ v ∈ input.rigidVars, v ∈ K ++ softVars F

theorem SourceScope.subst (h : SourceScope K F input) (subst : Subst)
    (hfix : ∀ k ∈ K, subst.onTy (.fvar k) = .fvar k) :
    SourceScope K (substSoft subst F) (input.substTyFvars subst) := by
  intro v hv
  obtain ⟨original, ho, hv⟩ := InferInput.rigidVars_substTyFvars hv
  exact scope_image hfix (h original ho) hv

inductive Seed (K : List Nat) (frontier : Nat) : Option TyTemplate → Ty → Nat → Prop
  | absent : Seed K frontier none (.fvar frontier) (frontier + 1)
  | annotated :
      template.allocate frontier = (next, ty) → ty.IsLC →
      (∀ v ∈ template.rigidVars, v ∈ K) →
      Seed K frontier (some template) ty next

inductive LetCheck (K : List Nat) (F : List Ty) (frontier : Nat) (ty : Ty) : BindingAnn → Nat → Subst → Prop
  | absent : LetCheck K F frontier ty .absent frontier []
  /-- A whole-signature `_` imposes no constraint on the RHS monotype. This
  eliminates an immediately solved, otherwise unused fresh metavariable. -/
  | hole : LetCheck K F frontier ty (.template .hole) frontier []
  | template :
      template.allocate frontier = (next, expected) → expected.IsLC →
      (∀ v ∈ template.rigidVars, v ∈ K ++ softVars F) →
      RigidUnify K ty expected subst →
      LetCheck K F frontier ty (.template template) next subst

/-- A signed RHS is checked under its written forall prefix. Only those
written skolems and ambient K are protected; anonymous holes stay flexible. -/
inductive SignatureCheck (K : List Nat) (F : List Ty) (written : List Nat) (frontier : Nat) (ty : Ty) :
    BindingAnn → Nat → Subst → Prop
  | complete {scheme : PolyTy} : scheme.WF → (∀ v ∈ scheme.body.freeVars, v ∈ K ++ softVars F) →
      RigidUnify (K ++ written) ty (scheme.openVars written) subst →
      SignatureCheck K F written frontier ty (.complete scheme) frontier subst
  | partialSignature {template : TyTemplate} :
      (template.openTyVarsFrom 0 written).allocate frontier = (next, expected) →
      expected.IsLC → (∀ v ∈ template.rigidVars, v ∈ K ++ softVars F) →
      RigidUnify (K ++ written) ty expected subst →
      SignatureCheck K F written frontier ty (.partialForall count template) next subst

/-- Written binders keep their authored order; inferred binders follow them. -/
def signatureNames (ann : BindingAnn) (K written : List Nat) (ctx : Ctx) (ty : Ty) : List Nat :=
  match ann with
  | .complete _ => written
  | _ => written ++ genVars (K ++ written) ctx.env ty

def signatureScheme (ann : BindingAnn) (K written : List Nat) (ctx : Ctx) (ty : Ty) : PolyTy :=
  match ann with
  | .complete scheme => scheme
  | _ => let names := signatureNames ann K written ctx ty
         ⟨names.length, Ty.closeOver names ty⟩

def lambdaOutput (ann : Option TyTemplate) (param : Ty) (subst : Subst) (body : Expr) : Expr :=
  .lambda (ann.map fun _ => subst.onTy param) body

def letOutput (scheme : PolyTy) (names : List Nat) (rhs body : Expr) (subst : Subst) : Expr :=
  .letIn (some (subst.onPolyTy scheme)) ((rhs.closeTyVars names).substTyFvars subst) body

mutual
/-- Canonical inference carries frozen K and the current images F of live
provisional forall slots. Sequential calls transform both F and source syntax. -/
inductive _root_.Infer : List Nat → List Ty → Nat → Ctx → InferInput → Nat → Subst → Expr → Ty → Prop
  | primLitUnit : Infer K F frontier ctx (.primLit .unit) frontier [] (.primLit .unit) (.prim .unit)
  | primLitInt : Infer K F frontier ctx (.primLit (.int n)) frontier [] (.primLit (.int n)) (.prim .int)
  | primLitNat : Infer K F frontier ctx (.primLit (.nat n)) frontier [] (.primLit (.nat n)) (.prim .nat)
  | primLitChar : Infer K F frontier ctx (.primLit (.char c)) frontier [] (.primLit (.char c)) (.prim .char)
  | primBinOpIntAdd : Infer K F frontier ctx (.primBinOp .intAdd) frontier [] (.primBinOp .intAdd) (.arrow (.prim .int) (.arrow (.prim .int) (.prim .int)))
  | primBinOpIntSub : Infer K F frontier ctx (.primBinOp .intSub) frontier [] (.primBinOp .intSub) (.arrow (.prim .int) (.arrow (.prim .int) (.prim .int)))
  | primBinOpIntLt :
      LookupList.get? ctx.ctors ⟨"True"⟩ = some trueC → trueC.IsBoolCtor →
      LookupList.get? ctx.ctors ⟨"False"⟩ = some falseC → falseC.IsBoolCtor →
      Infer K F frontier ctx (.primBinOp .intLt) frontier [] (.primBinOp .intLt)
        (.arrow (.prim .int) (.arrow (.prim .int) (.customTy ⟨"Bool"⟩ [])))
  | primBinOpCharLt :
      LookupList.get? ctx.ctors ⟨"True"⟩ = some trueC → trueC.IsBoolCtor →
      LookupList.get? ctx.ctors ⟨"False"⟩ = some falseC → falseC.IsBoolCtor →
      Infer K F frontier ctx (.primBinOp .charLt) frontier [] (.primBinOp .charLt)
        (.arrow (.prim .char) (.arrow (.prim .char) (.customTy ⟨"Bool"⟩ [])))
  | var : ctx.env[index]? = some scheme →
      Infer K F frontier ctx (.var index) (frontier + scheme.paramCount) [] (.var index)
        (scheme.openVars (freshVars frontier scheme.paramCount))
  | ctor : LookupList.get? ctx.ctors name = some ctor →
      Infer K F frontier ctx (.ctor name) (frontier + ctor.paramCount) [] (.ctor name)
        (ctor.toTy.openVars (freshVars frontier ctor.paramCount))
  | lambda :
      SourceScope K F (.lambda ann body) →
      Seed (K ++ softVars F) frontier ann param initial →
      Infer K F initial { ctx with env := PolyTy.mkTrivial param :: ctx.env }
        body next subst completed bodyTy →
      Infer K F frontier ctx (.lambda ann body) next subst
        (lambdaOutput ann param subst completed) (.arrow (subst.onTy param) bodyTy)
  | app :
      SourceScope K F (.app f arg) →
      Infer K F frontier ctx f first s1 fOut fTy →
      Infer K (substSoft s1 F) first (s1.onCtx ctx) (arg.substTyFvars s1) second s2 argOut argTy →
      RigidUnify K (s2.onTy fTy) (.arrow argTy (.fvar second)) s3 →
      Infer K F frontier ctx (.app f arg) (second + 1) (s1 ++ s2 ++ s3)
        (.app (fOut.substTyFvars (s2 ++ s3)) (argOut.substTyFvars s3)) (s3.onTy (.fvar second))
  | letIn :
      SourceScope K F (.letIn ann rhs body) →
      Infer K F frontier ctx rhs first s1 rhsOut rhsTy →
      LetCheck K (substSoft s1 F) first rhsTy (ann.substTyFvars s1) checked sCheck →
      Infer K (substSoft (s1 ++ sCheck) F) checked
        { (sCheck.onCtx (s1.onCtx ctx)) with
          env := genScheme (K ++ softVars (substSoft (s1 ++ sCheck) F))
            (sCheck.onCtx (s1.onCtx ctx)).env (sCheck.onTy rhsTy) ::
            (sCheck.onCtx (s1.onCtx ctx)).env }
        (body.substTyFvars (s1 ++ sCheck)) next s2 bodyOut bodyTy →
      Infer K F frontier ctx (.letIn ann rhs body) next (s1 ++ sCheck ++ s2)
        (letOutput (genScheme (K ++ softVars (substSoft (s1 ++ sCheck) F))
            (sCheck.onCtx (s1.onCtx ctx)).env (sCheck.onTy rhsTy))
          (genVars (K ++ softVars (substSoft (s1 ++ sCheck) F))
            (sCheck.onCtx (s1.onCtx ctx)).env (sCheck.onTy rhsTy))
          (rhsOut.substTyFvars sCheck) bodyOut s2) bodyTy
  | letSignature :
      SourceScope K F (.letIn ann rhs body) →
      written = freshVars frontier ann.paramCount →
      (∀ name ∈ written, name ∉ K ++ softVars F) →
      (∀ v ∈ rhs.rigidVars, v ∈ K ++ softVars F) →
      Infer (K ++ written) F (frontier + ann.paramCount) ctx (rhs.openTyVars written)
        first s1 rhsOut rhsTy →
      SignatureCheck K (substSoft s1 F) written first rhsTy (ann.substTyFvars s1) checked sCheck →
      (∀ name ∈ written, name ∉ (sCheck.onCtx (s1.onCtx ctx)).env.freeVars ++
        softVars (substSoft (s1 ++ sCheck) F)) →
      Infer K (substSoft (s1 ++ sCheck) F) checked
        { (sCheck.onCtx (s1.onCtx ctx)) with
          env := signatureScheme (ann.substTyFvars (s1 ++ sCheck))
            (K ++ softVars (substSoft (s1 ++ sCheck) F)) written
            (sCheck.onCtx (s1.onCtx ctx)) (sCheck.onTy rhsTy) ::
            (sCheck.onCtx (s1.onCtx ctx)).env }
        (body.substTyFvars (s1 ++ sCheck)) next s2 bodyOut bodyTy →
      Infer K F frontier ctx (.letIn ann rhs body) next (s1 ++ sCheck ++ s2)
        (letOutput (signatureScheme (ann.substTyFvars (s1 ++ sCheck))
            (K ++ softVars (substSoft (s1 ++ sCheck) F)) written
            (sCheck.onCtx (s1.onCtx ctx)) (sCheck.onTy rhsTy))
          (signatureNames (ann.substTyFvars (s1 ++ sCheck))
            (K ++ softVars (substSoft (s1 ++ sCheck) F)) written
            (sCheck.onCtx (s1.onCtx ctx)) (sCheck.onTy rhsTy))
          (rhsOut.substTyFvars sCheck) bodyOut s2) bodyTy
  | match_ :
      SourceScope K F (.match_ scrut branches) →
      Infer K F frontier ctx scrut first s1 scrutOut scrutTy →
      branches ≠ [] →
      InferBranches K (substSoft s1 F) (first + 1) (s1.onCtx ctx) scrutTy (.fvar first)
        (substInputBranches s1 branches) next s2 branchesOut →
      Infer K F frontier ctx (.match_ scrut branches) next (s1 ++ s2)
        (.match_ (scrutOut.substTyFvars s2) branchesOut) (s2.onTy (.fvar first))

  | letRec {schemes : List PolyTy} {outputs : List Expr} :
      (SourceScope K F (.letRec anns bindings body) ∧ CtxBelow frontier ctx ∧
        (∀ v ∈ K, v < frontier) ∧ (∀ v ∈ softVars F, v < frontier)) →
      (∀ scheme, .complete scheme ∈ anns → scheme.WF) →
      (RecGroups.ValidResidualGroups (anns.map BindingAnn.recModeAnn) (bindings.map InferInput.erase) groups ∧
        groups = RecGroup.inferenceSccs (anns.map BindingAnn.recModeAnn) (bindings.map InferInput.erase)) →
      InferRecStrata K F (frontier + bindings.length) ctx anns bindings (RecState.init frontier anns)
        groups first s1 state1 →
      InferRecSigned K (substSoft s1 F) 0 first (s1.onCtx ctx)
        (anns.map (BindingAnn.substTyFvars s1)) (bindings.map (InferInput.substTyFvars s1)) state1
        second s2 state2 →
      state2.exports = schemes.map some → state2.outputs = outputs.map some →
      Infer K (substSoft (s1 ++ s2) F) second (state2.rhsCtx ((s1 ++ s2).onCtx ctx))
        (body.substTyFvars (s1 ++ s2)) next s3 bodyOut bodyTy →
      Infer K F frontier ctx (.letRec anns bindings body) next (s1 ++ s2 ++ s3)
        (.letRec ((schemes.map s3.onPolyTy).map some) (outputs.map (Expr.substTyFvars s3)) bodyOut) bodyTy

inductive _root_.InferBranches : List Nat → List Ty → Nat → Ctx → Ty → Ty →
    List (MatchPattern × InferInput) → Nat → Subst → List (MatchPattern × Expr) → Prop
  | nil : InferBranches K F frontier ctx scrutTy resultTy [] frontier [] []
  | consWild :
      (∀ v ∈ rigidBranchVars ((.wildcard, body) :: rest), v ∈ K ++ softVars F) →
      Infer K F frontier ctx body first s1 bodyOut bodyTy →
      RigidUnify K bodyTy (s1.onTy resultTy) s2 →
      InferBranches K (substSoft (s1 ++ s2) F) first (s2.onCtx (s1.onCtx ctx))
        (s2.onTy (s1.onTy scrutTy)) (s2.onTy (s1.onTy resultTy))
        (substInputBranches (s1 ++ s2) rest) next s3 restOut →
      InferBranches K F frontier ctx scrutTy resultTy ((.wildcard, body) :: rest) next (s1 ++ s2 ++ s3)
        ((.wildcard, bodyOut.substTyFvars (s2 ++ s3)) :: restOut)
  | cons :
      (∀ v ∈ rigidBranchVars ((.named name count, body) :: rest), v ∈ K ++ softVars F) →
      LookupList.get? ctx.ctors name = some ctor →
      count = ctor.contents.length →
      RigidUnify K scrutTy (.customTy ctor.tyName ((freshVars frontier ctor.paramCount).map Ty.fvar)) s0 →
      Infer K (substSoft s0 F) (frontier + ctor.paramCount)
        { (s0.onCtx ctx) with
          env := (ctor.contents.map (Ty.openWith (((freshVars frontier ctor.paramCount).map Ty.fvar).map s0.onTy))).map PolyTy.mkTrivial ++
              (s0.onCtx ctx).env }
        (body.substTyFvars s0) first s1 bodyOut bodyTy →
      RigidUnify K bodyTy (s1.onTy (s0.onTy resultTy)) s2 →
      InferBranches K (substSoft (s0 ++ s1 ++ s2) F) first (s2.onCtx (s1.onCtx (s0.onCtx ctx)))
        (s2.onTy (s1.onTy (s0.onTy scrutTy))) (s2.onTy (s1.onTy (s0.onTy resultTy)))
        (substInputBranches (s0 ++ s1 ++ s2) rest) next s3 restOut →
      InferBranches K F frontier ctx scrutTy resultTy ((.named name count, body) :: rest) next
        (s0 ++ s1 ++ s2 ++ s3) ((.named name count, bodyOut.substTyFvars (s2 ++ s3)) :: restOut)
/-- Infer one selected SCC in the original full group coordinates. Sources have
already been opened at flexible written roots and transformed by shape solving. -/
inductive _root_.InferRecComponent : List Nat → List Ty → List Nat → Nat → Nat → Ctx →
    List InferInput → List RecSpec → Nat → Subst → List (Option Expr) → List RecFacts → Prop
  | nil : InferRecComponent K F members index frontier ctx [] [] frontier [] [] []
  | skipMono :
      index ∉ members →
      InferRecComponent K F members (index + 1) frontier ctx rest specs next subst outputs facts →
      InferRecComponent K F members index frontier ctx (rhs :: rest) (.mono ty :: specs)
        next subst (none :: outputs) (.empty :: facts)
  | skipPoly :
      InferRecComponent K F members (index + 1) frontier ctx rest specs next subst outputs facts →
      InferRecComponent K F members index frontier ctx (rhs :: rest) (.poly scheme :: specs)
        next subst (none :: outputs) (.empty :: facts)
  | consSelected {bodyFacts : RecFacts} :
      index ∈ members →
      Infer K F frontier ctx rhs first s1 output ty →
      RigidUnify K ty (s1.onTy expected) s2 →
      InferRecComponent K (substSoft (s1 ++ s2) F) members (index + 1) first
        (s2.onCtx (s1.onCtx ctx)) (rest.map (InferInput.substTyFvars (s1 ++ s2)))
        (specs.map (RecSpec.onSubstSource (s1 ++ s2))) next s3 outputs facts →
      InferRecComponent K F members index frontier ctx (rhs :: rest) (.mono expected :: specs)
        next (s1 ++ s2 ++ s3) (some (output.substTyFvars (s2 ++ s3)) :: outputs)
        (bodyFacts.onSubst (s2 ++ s3) :: facts)

/-- Component scheduling is shared with complete Core. Only completed contracts
cut dependencies; each partial signature is solved in its monomorphic SCC. -/
inductive _root_.InferRecStrata : List Nat → List Ty → Nat → Ctx → List BindingAnn → List InferInput →
    RecState → List (List Nat) → Nat → Subst → RecState → Prop
  | nil : InferRecStrata K F frontier ctx anns bindings state [] frontier [] state
  | cons {state : RecState} :
      OpenRecAnns component 0 frontier anns opened openings →
      CheckRecShapes K ((state.installOpenings component openings).shapes component openings) pre →
      InferRecComponent K
        (substSoft pre (F ++ (openings.flatMap RecOpening.written).map Ty.fvar)) component 0 opened
        (((state.installOpenings component openings).onSubst pre).rhsCtx (pre.onCtx ctx))
        ((openRecSources openings bindings).map (InferInput.substTyFvars pre))
        ((state.installOpenings component openings).onSubst pre).specs
        first current outputs facts →
      FinishRecComponent K (softVars (substSoft (pre ++ current) F)) component
        ((pre ++ current).onCtx ctx) ((state.installOpenings component openings).onSubst (pre ++ current))
        outputs facts exported →
      InferRecStrata K (substSoft (pre ++ current) F) first ((pre ++ current).onCtx ctx)
        (anns.map (BindingAnn.substTyFvars (pre ++ current)))
        (bindings.map (InferInput.substTyFvars (pre ++ current))) exported rest next tail final →
      InferRecStrata K F frontier ctx anns bindings state (component :: rest)
        next (pre ++ current ++ tail) final

/-- Completely written recursive contracts are checked after inferred SCCs,
under their completed final exports, with fresh rigid openings. -/
inductive _root_.InferRecSigned : List Nat → List Ty → Nat → Nat → Ctx → List BindingAnn → List InferInput →
    RecState → Nat → Subst → RecState → Prop
  | nil : InferRecSigned K F index frontier ctx [] [] state frontier [] state
  | skip :
      ann.recModeAnn = none →
      InferRecSigned K F (index + 1) frontier ctx anns bindings state next subst final →
      InferRecSigned K F index frontier ctx (ann :: anns) (rhs :: bindings) state next subst final
  | cons {scheme : PolyTy} {rhs : InferInput} {state : RecState} {bodyFacts : RecFacts} :
      scheme.WF →
      (∀ v ∈ rhs.rigidVars, v ∈ K ++ softVars F) →
      Infer (K ++ freshVars frontier scheme.paramCount) F (frontier + scheme.paramCount)
        (state.rhsCtx ctx) (rhs.openTyVars (freshVars frontier scheme.paramCount))
        first s1 output ty →
      RigidUnify (K ++ freshVars frontier scheme.paramCount) ty
        ((s1.onPolyTy scheme).openVars (freshVars frontier scheme.paramCount)) s2 →
      (∀ y ∈ freshVars frontier scheme.paramCount,
        y ∉ (((state.onSubst (s1 ++ s2)).rhsCtx ((s1 ++ s2).onCtx ctx)).env.freeVars ++
          softVars (substSoft (s1 ++ s2) F))) →
      InferRecSigned K (substSoft (s1 ++ s2) F) (index + 1) first ((s1 ++ s2).onCtx ctx)
        (anns.map (BindingAnn.substTyFvars (s1 ++ s2))) (bindings.map (InferInput.substTyFvars (s1 ++ s2)))
        ((state.onSubst (s1 ++ s2)).setSigned index (freshVars frontier scheme.paramCount)
          (output.substTyFvars s2) (bodyFacts.onSubst s2)) next tail final →
      InferRecSigned K F index frontier ctx (.complete scheme :: anns) (rhs :: bindings) state
        next (s1 ++ s2 ++ tail) final

end

theorem Seed.lc (h : Seed K frontier ann param initial) : param.IsLC := by
  cases h with
  | absent => exact .fvar
  | annotated _ hlc _ => exact hlc

theorem Seed.fits (h : Seed K frontier ann param initial) :
    ∀ template, ann = some template → template.Fits param := by
  cases h with
  | absent => intro _ heq; cases heq
  | @annotated next param sourceTemplate heq _ _ =>
      intro t ht
      have hfit := TyTemplate.allocate_fits sourceTemplate frontier
      have hequal := Option.some.inj ht
      subst t
      rwa [heq] at hfit

theorem Seed.rigid (h : Seed K frontier ann param initial) :
    ∀ template, ann = some template → ∀ v ∈ template.rigidVars, v ∈ K := by
  cases h with
  | absent => intro _ heq; cases heq
  | annotated _ _ hrigid => intro _ heq; cases heq; exact hrigid

theorem LetCheck.not_signature (h : LetCheck K F frontier ty ann next subst) :
    ann.isSignature = false := by cases h <;> rfl

theorem LetCheck.dom_avoids (h : LetCheck K F frontier ty ann next subst) :
    ∀ pair ∈ subst, pair.1 ∉ K := by
  cases h with
  | absent => simp
  | hole => simp
  | template _ _ _ huni => exact huni.dom_avoids

theorem LetCheck.lc (h : LetCheck K F frontier ty ann next subst) (hlc : ty.IsLC) :
    ∀ pair ∈ subst, pair.2.IsLC := by
  cases h with
  | absent => simp
  | hole => simp
  | template _ he _ huni => exact huni.unifies.lc hlc he

theorem LetCheck.fits (h : LetCheck K F frontier ty ann next subst) :
    (ann.substTyFvars subst).FitsMono (subst.onTy ty) := by
  cases h with
  | absent => trivial
  | hole => exact .hole
  | @template next expected subst t heq _ _ huni =>
      have hfit := TyTemplate.allocate_fits t frontier
      rw [heq] at hfit
      change (t.substTyFvars subst).Fits (subst.onTy ty)
      rw [huni.unifies.unifies]
      exact hfit.substTyFvars subst

theorem LetCheck.rigid (h : LetCheck K F frontier ty ann next subst) :
    ∀ template, ann = .template template → ∀ v ∈ template.rigidVars, v ∈ K ++ softVars F := by
  cases h with
  | absent => intro _ heq; cases heq
  | hole => intro _ heq; cases heq; simp [TyTemplate.rigidVars]
  | template _ _ hrigid _ => intro _ heq; cases heq; exact hrigid

theorem TyTemplate.open_scope {template : TyTemplate} {K written : List Nat}
    (h : ∀ v ∈ template.rigidVars, v ∈ K) :
    ∀ v ∈ (template.openTyVarsFrom 0 written).rigidVars, v ∈ K ++ written :=
  template.openTyVarsFrom_scope h 0 written

theorem SignatureCheck.dom_avoids (h : SignatureCheck K F written frontier ty ann next subst) :
    ∀ pair ∈ subst, pair.1 ∉ K ++ written := by
  cases h with
  | complete _ _ hu => exact hu.dom_avoids
  | partialSignature _ _ _ hu => exact hu.dom_avoids

theorem SignatureCheck.rigid (h : SignatureCheck K F written frontier ty ann next subst) :
    ∀ v ∈ ann.rigidVars, v ∈ K ++ softVars F := by
  cases h with
  | complete _ hr _ => exact hr
  | partialSignature _ _ hr _ => exact hr

theorem SignatureCheck.lc (h : SignatureCheck K F written frontier ty ann next subst)
    (hprefix : written.length = ann.paramCount) (hlc : ty.IsLC) :
    ∀ pair ∈ subst, pair.2.IsLC := by
  cases h with
  | complete hwf _ hu => exact hu.unifies.lc hlc (PolyTy.openVars_isLC hwf hprefix.ge)
  | partialSignature _ he _ hu => exact hu.unifies.lc hlc he

theorem SignatureCheck.completion (h : SignatureCheck K F written frontier ty ann next subst)
    (hprefix : written.length = ann.paramCount) (hlc : ty.IsLC) :
    (ann.substTyFvars subst).SignatureCompletion written (subst.onTy ty)
      (signatureScheme (ann.substTyFvars subst) Q written ctx (subst.onTy ty))
      (signatureNames (ann.substTyFvars subst) Q written ctx (subst.onTy ty)) := by
  have hS := h.lc hprefix hlc
  have hdom : ∀ pair ∈ subst, pair.1 ∉ written :=
    fun p hp hw => h.dom_avoids p hp (List.mem_append_right _ hw)
  cases h with
  | @complete subst scheme _ _ hu =>
    refine .complete hprefix ?_
    exact hu.unifies.unifies.trans (Subst.onTy_openVars hS hdom)
  | @partialSignature next expected subst count template heq _ _ hu =>
    refine .partialSignature hprefix ?_
    have hfit := TyTemplate.allocate_fits (template.openTyVarsFrom 0 written) frontier
    rw [heq] at hfit
    have ht := hfit.substTyFvars subst
    rw [hu.unifies.unifies]
    simpa only [TyTemplate.substTyFvars_openTyVarsFrom _ hS hdom 0] using ht

theorem SignatureCheck.scheme_wf (h : SignatureCheck K F written frontier ty ann next subst)
    (hprefix : written.length = ann.paramCount) (hlc : ty.IsLC) :
    (signatureScheme (ann.substTyFvars subst) Q written ctx (subst.onTy ty)).WF := by
  have hS := h.lc hprefix hlc
  cases h with
  | complete hwf _ _ => exact Subst.onPolyTy_wf hS hwf
  | partialSignature _ _ _ _ => exact Ty.closeOver_preserves_bvars (Subst.onTy_lc hS hlc)

theorem SignatureCheck.names_avoid (h : SignatureCheck K F written frontier ty ann next subst)
    (havoid : ∀ name ∈ written, name ∉ Q) :
    ∀ name ∈ signatureNames (ann.substTyFvars subst) Q written ctx (subst.onTy ty), name ∉ Q := by
  cases h with
  | complete _ _ _ => exact havoid
  | partialSignature _ _ _ _ =>
    intro name hn hk
    rcases List.mem_append.mp hn with hn | hn
    · exact havoid name hn hk
    · exact genVars_not_mem_rigid hn (List.mem_append_left _ hk)

theorem SignatureCheck.names_nodup (h : SignatureCheck K F written frontier ty ann next subst)
    (hnd : written.Nodup) :
    (signatureNames (ann.substTyFvars subst) Q written ctx (subst.onTy ty)).Nodup := by
  cases h with
  | complete _ _ _ => exact hnd
  | partialSignature _ _ _ _ =>
    apply List.nodup_append.mpr
    refine ⟨hnd, genVars_nodup, ?_⟩
    intro name hw other hg heq
    subst other
    exact genVars_not_mem_rigid hg (List.mem_append_right _ hw)

theorem SignatureCheck.names_fresh (h : SignatureCheck K F written frontier ty ann next subst)
    (havoid : ∀ name ∈ written, name ∉ ctx.env.freeVars) :
    ∀ name ∈ signatureNames (ann.substTyFvars subst) Q written ctx (subst.onTy ty), name ∉ ctx.env.freeVars := by
  cases h with
  | complete _ _ _ => exact havoid
  | partialSignature _ _ _ _ =>
    intro name hn
    rcases List.mem_append.mp hn with hn | hn
    · exact havoid name hn
    · exact genVars_not_mem hn

theorem SignatureCheck.scheme_eq_close (h : SignatureCheck K F written frontier ty ann next subst)
    (hlen : written.length = ann.paramCount) (hlc : ty.IsLC) (hnd : written.Nodup)
    (hrigid : ∀ v ∈ (ann.substTyFvars subst).rigidVars, v ∈ Q)
    (havoid : ∀ name ∈ written, name ∉ Q) :
    signatureScheme (ann.substTyFvars subst) Q written ctx (subst.onTy ty) =
      ⟨(signatureNames (ann.substTyFvars subst) Q written ctx (subst.onTy ty)).length,
        Ty.closeOver (signatureNames (ann.substTyFvars subst) Q written ctx (subst.onTy ty))
          (subst.onTy ty)⟩ := by
  have hcomp := h.completion (Q := Q) (ctx := ctx) hlen hlc
  have hwf := h.scheme_wf (Q := Q) (ctx := ctx) hlen hlc
  cases h with
  | @complete subst scheme _ _ _ =>
    cases hcomp with
    | complete hl heq =>
      simp only [BindingAnn.substTyFvars, signatureScheme, signatureNames] at *
      rw [heq, PolyTy.openVars, Ty.closeOver_openVars_self hnd
        (by simpa only [hl] using hwf)
        (fun name hn hv => havoid name hn (hrigid name hv))]
      cases scheme
      simp only [PolyTy.mk.injEq]
      exact ⟨hl.symm, True.intro⟩
  | partialSignature _ _ _ _ => rfl

theorem _root_.Infer.sourceScope (h : Infer K F frontier ctx input next subst output ty) :
    SourceScope K F input := by
  cases h with
  | primLitUnit | primLitInt | primLitNat | primLitChar | primBinOpIntAdd | primBinOpIntSub | primBinOpIntLt _ _ _ _ | primBinOpCharLt _ _ _ _ | var _ | ctor _ =>
      simp [SourceScope, InferInput.rigidVars]
  | lambda hs _ _ => exact hs
  | app hs _ _ _ => exact hs
  | letIn hs _ _ _ => exact hs
  | letSignature hs _ _ _ _ _ _ _ => exact hs
  | match_ hs _ _ _ => exact hs
  | letRec hs _ _ _ _ _ _ _ => exact hs.1

private theorem avoids_append {K : List Nat} {S T : Subst}
    (hS : ∀ p ∈ S, p.1 ∉ K) (hT : ∀ p ∈ T, p.1 ∉ K) :
    ∀ p ∈ S ++ T, p.1 ∉ K :=
  fun p hp => (List.mem_append.mp hp).elim (hS p) (hT p)

mutual
theorem _root_.Infer.dom_avoids (h : Infer K F frontier ctx input next subst output ty) :
    ∀ pair ∈ subst, pair.1 ∉ K := by
  match h with
  | .primLitUnit | .primLitInt | .primLitNat | .primLitChar | .primBinOpIntAdd | .primBinOpIntSub | .primBinOpIntLt _ _ _ _ | .primBinOpCharLt _ _ _ _ | .var _ | .ctor _ => simp
  | .lambda _ _ hb => exact hb.dom_avoids
  | .app _ hf ha hu => exact avoids_append (avoids_append hf.dom_avoids ha.dom_avoids) hu.dom_avoids
  | .letIn _ hr hc hb => exact avoids_append (avoids_append hr.dom_avoids hc.dom_avoids) hb.dom_avoids
  | .letSignature _ _ _ _ hr hc _ hb =>
    exact avoids_append (avoids_append
      (fun p hp hk => hr.dom_avoids p hp (List.mem_append_left _ hk))
      (fun p hp hk => hc.dom_avoids p hp (List.mem_append_left _ hk))) hb.dom_avoids
  | .match_ _ hs _ hb => exact avoids_append hs.dom_avoids hb.dom_avoids
  | .letRec _ _ _ hstrata hsigned _ _ hbody =>
      exact avoids_append (avoids_append hstrata.dom_avoids hsigned.dom_avoids) hbody.dom_avoids
termination_by (input.size, 0)
decreasing_by all_goals (simp only [InferInput.size, InferInput.size_openTyVars, InferInput.size_substTyFvars, sizeBranches_substInputBranches, sizeBindings_map_substTyFvars]; omega)

theorem _root_.InferBranches.dom_avoids
    (h : InferBranches K F frontier ctx scrutTy resultTy branches next subst completed) :
    ∀ pair ∈ subst, pair.1 ∉ K := by
  match h with
  | .nil => simp
  | .consWild _ hb hu hr => exact avoids_append (avoids_append hb.dom_avoids hu.dom_avoids) hr.dom_avoids
  | .cons _ _ _ hu0 hb hu hr =>
    exact avoids_append (avoids_append (avoids_append hu0.dom_avoids hb.dom_avoids) hu.dom_avoids) hr.dom_avoids
termination_by (sizeBranches branches, 0)
decreasing_by all_goals (simp only [sizeBranches, InferInput.size_substTyFvars, sizeBranches_substInputBranches]; omega)

theorem _root_.InferRecComponent.dom_avoids
    (h : InferRecComponent K F members index frontier ctx bindings specs next S outputs facts) :
    ∀ pair ∈ S, pair.1 ∉ K := by
  match h with
  | .nil => simp
  | .skipMono _ hr | .skipPoly hr => exact hr.dom_avoids
  | .consSelected _ hi hu hr =>
      exact avoids_append (avoids_append hi.dom_avoids hu.dom_avoids) hr.dom_avoids
termination_by (sizeBindings bindings, 0)
decreasing_by all_goals (simp only [sizeBindings, sizeBindings_map_substTyFvars]; omega)

theorem _root_.InferRecStrata.dom_avoids
    (h : InferRecStrata K F frontier ctx anns bindings state groups next S final) :
    ∀ pair ∈ S, pair.1 ∉ K := by
  match h with
  | .nil => simp
  | .cons _ hpre hcurrent _ htail =>
      exact avoids_append (avoids_append hpre.dom_avoids hcurrent.dom_avoids) htail.dom_avoids
termination_by (sizeBindings bindings, groups.length + 1)
decreasing_by
  all_goals (simp only [sizeBindings_map_substTyFvars, sizeBindings_openRecSources, List.length_cons])
  all_goals omega

theorem _root_.InferRecSigned.dom_avoids
    (h : InferRecSigned K F index frontier ctx anns bindings state next S final) :
    ∀ pair ∈ S, pair.1 ∉ K := by
  match h with
  | .nil => simp
  | .skip _ hr => exact hr.dom_avoids
  | .cons _ _ hi hu _ hr =>
      exact avoids_append (avoids_append
        (fun p hp hk => hi.dom_avoids p hp (List.mem_append_left _ hk))
        (fun p hp hk => hu.dom_avoids p hp (List.mem_append_left _ hk))) hr.dom_avoids
termination_by (sizeBindings bindings, 0)
decreasing_by all_goals (simp only [sizeBindings, InferInput.size_openTyVars, sizeBindings_map_substTyFvars]; omega)
end

 theorem _root_.InferRecComponent.lengths
    (h : InferRecComponent K F members index frontier ctx bindings specs next S outputs facts) :
    outputs.length = bindings.length ∧ specs.length = bindings.length ∧ facts.length = bindings.length := by
  match h with
  | .nil => exact ⟨rfl,rfl,rfl⟩
  | .skipMono _ hr | .skipPoly hr =>
      simpa only [List.length_cons, Nat.add_right_cancel_iff] using hr.lengths
  | .consSelected _ _ _ hr =>
      simpa only [List.length_cons, List.length_map, Nat.add_right_cancel_iff] using hr.lengths

 termination_by structural h

 theorem _root_.InferRecComponent.output_inv
    (h : InferRecComponent K F members index frontier ctx bindings specs next S outputs facts) :
    ∀ j output, outputs[j]? = some (some output) →
      index + j ∈ members ∧ ∃ ty, specs[j]? = some (.mono ty) := by
  match h with
  | .nil => intro j output hget; simp at hget
  | .skipMono hskip hr =>
      intro j output hget
      cases j with
      | zero => cases hget
      | succ j =>
        obtain ⟨hmem, target, htarget⟩ := hr.output_inv j output hget
        exact ⟨by simpa only [Nat.add_assoc, Nat.add_comm 1 j] using hmem, target, htarget⟩
  | .skipPoly hr =>
      intro j output hget
      cases j with
      | zero => cases hget
      | succ j =>
        obtain ⟨hmem, target, htarget⟩ := hr.output_inv j output hget
        exact ⟨by simpa only [Nat.add_assoc, Nat.add_comm 1 j] using hmem, target, htarget⟩
  | .consSelected hsel hi hu hr =>
      intro j output hget
      cases j with
      | zero => exact ⟨by simpa using hsel, _, rfl⟩
      | succ j =>
        obtain ⟨hmem, target, htarget⟩ := hr.output_inv j output hget
        rw [List.getElem?_map] at htarget
        obtain ⟨old, hold, heq⟩ := Option.map_eq_some_iff.mp htarget
        cases old with
        | poly scheme => cases heq
        | mono ty =>
            exact ⟨by simpa only [Nat.add_assoc, Nat.add_comm 1 j] using hmem, ty, hold⟩

 termination_by structural h

 theorem _root_.InferRecComponent.lc_of_infer
    (h : InferRecComponent K F members index frontier ctx bindings specs next S outputs facts)
    (hInfer : ∀ {κ F' Ψ c e Ψ' T output ty}, e.size ≤ sizeBindings bindings →
      Infer κ F' Ψ c e Ψ' T output ty → CtxWF c → ty.IsLC ∧ ∀ p ∈ T, p.2.IsLC)
    (hctx : CtxWF ctx) (hspec : ∀ spec ∈ specs, spec.LC) : ∀ p ∈ S, p.2.IsLC := by
  match h with
  | .nil => simp
  | .skipMono _ hr | .skipPoly hr =>
      exact hr.lc_of_infer (fun he h => hInfer (by simp only [sizeBindings]; omega) h)
        hctx (fun spec hm => hspec spec (List.mem_cons_of_mem _ hm))
  | .consSelected _ hi hu hr =>
      expose_names
      obtain ⟨hiTy, hiS⟩ := hInfer (by simp only [sizeBindings]; omega) hi hctx
      have huS := hu.unifies.lc hiTy (Subst.onTy_lc hiS (hspec _ List.mem_cons_self))
      have hS12 : ∀ p ∈ s1 ++ s2, p.2.IsLC := fun p hp => (List.mem_append.mp hp).elim (hiS p) (huS p)
      have hrS := hr.lc_of_infer
        (fun he h => hInfer (by simp only [sizeBindings_map_substTyFvars] at he; simp only [sizeBindings]; omega) h)
        (Subst.onCtx_wf huS (Subst.onCtx_wf hiS hctx)) (by
          intro spec hm
          obtain ⟨old, hold, rfl⟩ := List.mem_map.mp hm
          exact RecSpec.lc_onSubstSource hS12 (hspec old (List.mem_cons_of_mem _ hold)))
      intro p hp
      exact (List.mem_append.mp hp).elim (hS12 p) (hrS p)
 termination_by structural h


 theorem RecState.shapes_lc {state : RecState} {openings : List RecOpening} (hstate : state.LC)
    (hopen : ∀ opening ∈ openings, ∀ ty, opening.expected = some ty → ty.IsLC) :
    ∀ shape ∈ state.shapes members openings, RecShape.LC shape := by
  intro shape hm
  obtain ⟨i, _, heq⟩ := List.mem_filterMap.mp hm
  cases hs : state.specs[i]? with
  | none => simp [hs] at heq
  | some spec =>
    cases spec with
    | poly σ => simp [hs, RecSpec.monoTy?] at heq
    | mono ty =>
      cases ho : openings[i]? with
      | none => simp [hs, RecSpec.monoTy?, ho] at heq
      | some opening =>
        simp [hs, RecSpec.monoTy?, ho] at heq
        subst shape
        exact ⟨hstate.1 _ (List.mem_of_getElem? hs), hopen opening (List.mem_of_getElem? ho)⟩

 theorem _root_.InferRecStrata.lc_of_infer
    (h : InferRecStrata K F frontier ctx anns bindings state groups next S final)
    (hInfer : ∀ {κ F' Ψ c e Ψ' T output ty}, e.size ≤ sizeBindings bindings →
      Infer κ F' Ψ c e Ψ' T output ty → CtxWF c → ty.IsLC ∧ ∀ p ∈ T, p.2.IsLC)
    (hctx : CtxWF ctx) (hstate : state.LC) :
    (∀ p ∈ S, p.2.IsLC) ∧ final.LC := by
  match h with
  | .nil => exact ⟨by simp, hstate⟩
  | .cons hopen hshape hcomponent hfinish hrest =>
    expose_names
    have hinit := hstate.installOpenings (members := component) (openings := openings)
    have hpre := hshape.lc (RecState.shapes_lc hinit hopen.expected_lc)
    have hcurrent := hcomponent.lc_of_infer
      (fun he h => hInfer (by simpa only [sizeBindings_map_substTyFvars, sizeBindings_openRecSources] using he) h)
      ((hinit.onSubst hpre).rhsCtx (Subst.onCtx_wf hpre hctx)) (hinit.onSubst hpre).1
    have hboth : ∀ p ∈ pre ++ current, p.2.IsLC :=
      fun p hp => (List.mem_append.mp hp).elim (hpre p) (hcurrent p)
    have hexport := hfinish.lc (hinit.onSubst hboth)
    obtain ⟨htail, hfinal⟩ := hrest.lc_of_infer
      (fun he h => hInfer (by simpa only [sizeBindings_map_substTyFvars] using he) h)
      (Subst.onCtx_wf hboth hctx) hexport
    exact ⟨fun p hp => (List.mem_append.mp hp).elim (hboth p) (htail p), hfinal⟩
 termination_by structural h

 theorem _root_.InferRecSigned.lc_of_infer
    (h : InferRecSigned K F index frontier ctx anns bindings state next S final)
    (hInfer : ∀ {κ F' Ψ c e Ψ' T output ty}, e.size ≤ sizeBindings bindings →
      Infer κ F' Ψ c e Ψ' T output ty → CtxWF c → ty.IsLC ∧ ∀ p ∈ T, p.2.IsLC)
    (hctx : CtxWF ctx) (hstate : state.LC) :
    (∀ p ∈ S, p.2.IsLC) ∧ final.LC := by
  match h with
  | .nil => exact ⟨by simp, hstate⟩
  | .skip _ hr =>
      exact hr.lc_of_infer (fun he h => hInfer (by simp only [sizeBindings]; omega) h) hctx hstate
  | .cons hscheme _ hi hu _ hr =>
      expose_names
      obtain ⟨hiTy, hiS⟩ := hInfer (by simp only [InferInput.size_openTyVars, sizeBindings]; omega) hi
        (hstate.rhsCtx hctx)
      have hexpected : ((s1.onPolyTy scheme).openVars (freshVars frontier scheme.paramCount)).IsLC :=
        PolyTy.openVars_isLC (Subst.onPolyTy_wf hiS hscheme)
        (by simp only [Subst.onPolyTy, freshVars_length]; exact Nat.le_refl _)
      have huS := hu.unifies.lc hiTy hexpected
      have hboth : ∀ p ∈ s1 ++ s2, p.2.IsLC :=
        fun p hp => (List.mem_append.mp hp).elim (hiS p) (huS p)
      obtain ⟨htail, hfinal⟩ := hr.lc_of_infer
        (fun he h => hInfer (by simp only [sizeBindings_map_substTyFvars] at he; simp only [sizeBindings]; omega) h)
        (Subst.onCtx_wf hboth hctx) ((hstate.onSubst hboth).setSigned)
      exact ⟨fun p hp => (List.mem_append.mp hp).elim (hboth p) (htail p), hfinal⟩
 termination_by structural h


mutual
theorem _root_.Infer.lc (h : Infer K F frontier ctx input next subst output ty) :
    CtxWF ctx → ty.IsLC ∧ ∀ pair ∈ subst, pair.2.IsLC := by
  match h with
  | .primLitUnit => intro _; exact ⟨.prim, by simp⟩
  | .primLitInt => intro _; exact ⟨.prim, by simp⟩
  | .primLitNat => intro _; exact ⟨.prim, by simp⟩
  | .primLitChar => intro _; exact ⟨.prim, by simp⟩
  | .primBinOpIntAdd => intro _; exact ⟨.arrow .prim (.arrow .prim .prim), by simp⟩
  | .primBinOpIntSub => intro _; exact ⟨.arrow .prim (.arrow .prim .prim), by simp⟩
  | .primBinOpIntLt _ _ _ _ => intro _; exact ⟨.arrow .prim (.arrow .prim (.customTy (by simp))), by simp⟩
  | .primBinOpCharLt _ _ _ _ => intro _; exact ⟨.arrow .prim (.arrow .prim (.customTy (by simp))), by simp⟩
  | .var hlook =>
      intro hctx
      exact ⟨PolyTy.openVars_isLC (hctx _ (List.mem_of_getElem? hlook)) (by simp), by simp⟩
  | .ctor hlook =>
      intro _
      exact ⟨PolyTy.openVars_isLC (Ctor.toTy_wf _) (by simp [Ctor.toTy]), by simp⟩
  | @Infer.lambda K F ann body frontier param initial ctx next subst completed bodyTy _ hs hb =>
      intro hctx
      have hbodyCtx : CtxWF { ctx with env := PolyTy.mkTrivial param :: ctx.env } := by
        intro scheme hscheme
        rcases List.mem_cons.mp hscheme with rfl | hscheme
        · exact hs.lc
        · exact hctx scheme hscheme
      obtain ⟨ht, hsubst⟩ := hb.lc hbodyCtx
      exact ⟨.arrow (Subst.onTy_lc hsubst hs.lc) ht, hsubst⟩
  | .app _ hf hx hu =>
      intro hctx
      obtain ⟨hfTy, hs1⟩ := hf.lc hctx
      obtain ⟨hxTy, hs2⟩ := hx.lc (Subst.onCtx_wf hs1 hctx)
      have hs3 := hu.unifies.lc (Subst.onTy_lc hs2 hfTy) (.arrow hxTy .fvar)
      refine ⟨Subst.onTy_lc hs3 .fvar, ?_⟩
      intro pair hp
      rcases List.mem_append.mp hp with hp | hp
      · exact (List.mem_append.mp hp).elim (hs1 pair) (hs2 pair)
      · exact hs3 pair hp
  | .letIn _ hr hc hb =>
      intro hctx
      obtain ⟨hrTy, hs1⟩ := hr.lc hctx
      have hcheck := hc.lc hrTy
      obtain ⟨hbTy, hs2⟩ := hb.lc (by
        intro scheme hscheme
        rcases List.mem_cons.mp hscheme with rfl | hscheme
        · exact genScheme_wf (Subst.onTy_lc hcheck hrTy)
        · exact Subst.onCtx_wf hcheck (Subst.onCtx_wf hs1 hctx) scheme hscheme)
      refine ⟨hbTy, ?_⟩
      intro pair hp
      rcases List.mem_append.mp hp with hp | hp
      · exact (List.mem_append.mp hp).elim (hs1 pair) (hcheck pair)
      · exact hs2 pair hp

  | .letSignature _ hprefix _ _ hr hc _ hb =>
    intro hctx
    have hlen : _ := congrArg List.length hprefix
    simp only [freshVars_length] at hlen
    obtain ⟨hrTy, hs1⟩ := hr.lc hctx
    have hcheck := hc.lc (by simpa using hlen) hrTy
    obtain ⟨hbTy, hs2⟩ := hb.lc (by
      intro scheme hscheme
      rcases List.mem_cons.mp hscheme with rfl | hscheme
      · simpa only [BindingAnn.substTyFvars_append] using hc.scheme_wf (Q := K ++ softVars (substSoft (_ ++ _) F)) (by simpa using hlen) hrTy
      · exact Subst.onCtx_wf hcheck (Subst.onCtx_wf hs1 hctx) scheme hscheme)
    exact ⟨hbTy, fun p hp => (List.mem_append.mp hp).elim
      (fun hp => (List.mem_append.mp hp).elim (hs1 p) (hcheck p)) (hs2 p)⟩
  | .match_ _ hs _ hb =>
    intro hctx
    obtain ⟨ht, hS1⟩ := hs.lc hctx
    obtain ⟨hresult, hS2⟩ := hb.lc (Subst.onCtx_wf hS1 hctx) ht .fvar
    exact ⟨hresult, fun p hp => (List.mem_append.mp hp).elim (hS1 p) (hS2 p)⟩
  | .letRec _ hann _ hs hp _ _ hb =>
    intro hctx
    obtain ⟨hs1, hstate1⟩ := hs.lc_of_infer
      (fun he hi => hi.lc) hctx (RecState.LC.init hann)
    obtain ⟨hs2, hstate2⟩ := hp.lc_of_infer
      (fun he hi => hi.lc) (Subst.onCtx_wf hs1 hctx) hstate1
    have hbodyCtx := hstate2.rhsCtx (Subst.onCtx_wf hs2 (Subst.onCtx_wf hs1 hctx))
    rw [← Subst.onCtx_append] at hbodyCtx
    obtain ⟨ht, hs3⟩ := hb.lc hbodyCtx
    exact ⟨ht, fun p hp => (List.mem_append.mp hp).elim
      (fun hp => (List.mem_append.mp hp).elim (hs1 p) (hs2 p)) (hs3 p)⟩
termination_by (input.size, 0)
decreasing_by
  all_goals simp only [sizeBindings_map_substTyFvars] at *
  all_goals (simp only [InferInput.size, InferInput.size_openTyVars, InferInput.size_substTyFvars, sizeBranches_substInputBranches]; omega)

theorem _root_.InferBranches.lc {Φ ctx scrutTy ρ brs Φ' S}
    (h : InferBranches κ F Φ ctx scrutTy ρ brs Φ' S out)
    (hctx : CtxWF ctx) (hscrutTy : scrutTy.IsLC) (hρ : ρ.IsLC) :
    (S.onTy ρ).IsLC ∧ (∀ p ∈ S, p.2.IsLC) := by
  match h with
  | .nil => exact ⟨by simpa using hρ, by simp⟩
  | .cons _ hlook hn huni0Rigid hbody huniRigid hrest =>
    have huni0 := huni0Rigid.unifies
    have huni := huniRigid.unifies
    have hS₀ := huni0.lc hscrutTy
      (.customTy (fun t ht => by obtain ⟨x, _, rfl⟩ := List.mem_map.mp ht; exact ContainsBvarsUpTo.fvar))
    obtain ⟨hτb_lc, hS₁⟩ := Infer.lc hbody
      (branchBindings_wf (Subst.onCtx_wf hS₀ hctx)
        (fun t ht => by
          obtain ⟨v, hv, rfl⟩ := List.mem_map.mp ht
          obtain ⟨x, _, rfl⟩ := List.mem_map.mp hv
          exact Subst.onTy_lc hS₀ ContainsBvarsUpTo.fvar)
        (by simp))
    have hS₂ := huni.lc hτb_lc (Subst.onTy_lc hS₁ (Subst.onTy_lc hS₀ hρ))
    obtain ⟨hres, hS₃⟩ := InferBranches.lc hrest
      (Subst.onCtx_wf hS₂ (Subst.onCtx_wf hS₁ (Subst.onCtx_wf hS₀ hctx)))
      (Subst.onTy_lc hS₂ (Subst.onTy_lc hS₁ (Subst.onTy_lc hS₀ hscrutTy)))
      (Subst.onTy_lc hS₂ (Subst.onTy_lc hS₁ (Subst.onTy_lc hS₀ hρ)))
    refine ⟨?_, ?_⟩
    · rw [Subst.onTy_append, Subst.onTy_append, Subst.onTy_append]; exact hres
    · intro p hp; rw [List.mem_append, List.mem_append, List.mem_append] at hp
      rcases hp with ((hp | hp) | hp) | hp
      · exact hS₀ p hp
      · exact hS₁ p hp
      · exact hS₂ p hp
      · exact hS₃ p hp
  | .consWild _ hbody huniRigid hrest =>
    have huni := huniRigid.unifies
    obtain ⟨hτb_lc, hS₁⟩ := Infer.lc hbody hctx
    have hS₂ := huni.lc hτb_lc (Subst.onTy_lc hS₁ hρ)
    obtain ⟨hres, hS₃⟩ := InferBranches.lc hrest
      (Subst.onCtx_wf hS₂ (Subst.onCtx_wf hS₁ hctx))
      (Subst.onTy_lc hS₂ (Subst.onTy_lc hS₁ hscrutTy))
      (Subst.onTy_lc hS₂ (Subst.onTy_lc hS₁ hρ))
    refine ⟨?_, ?_⟩
    · rw [Subst.onTy_append, Subst.onTy_append]; exact hres
    · intro p hp; rw [List.mem_append, List.mem_append] at hp
      rcases hp with (hp | hp) | hp
      · exact hS₁ p hp
      · exact hS₂ p hp
      · exact hS₃ p hp
termination_by (sizeBranches brs, 0)
decreasing_by
  all_goals (simp only [sizeBranches, InferInput.size_substTyFvars, sizeBranches_substInputBranches]; omega)
end

end

/-! ## Worker -/

section

def seed (K : List Nat) (frontier : Nat) (ann : Option TyTemplate) :
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

def checkLet (K : List Nat) (F : List Ty) (frontier : Nat) (ann : BindingAnn) (ty : Ty) :
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

def checkSignature (K : List Nat) (F : List Ty) (written : List Nat) (frontier : Nat) (ann : BindingAnn) (ty : Ty) :
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
/-- One metadata-producing inference path for all input syntax. Recursive partial signatures remain
monomorphic until their component is solved and its ordered prefix is validated. -/
def _root_.inferWithTypesCore (K : List Nat) (frontier : Nat) (ctx : Ctx) (input : InferInput) (F : List Ty := []) :
    Option { result : Nat × Subst × Expr × Ty × InferredNodeTypes × InferredBinderSchemes //
      Infer K F frontier ctx input result.1 result.2.1 result.2.2.1 result.2.2.2.1 } :=
  if hK : K.all (fun v => decide (v < frontier)) = true then
    if hctx : ctx.env.freeVars.all (fun v => decide (v < frontier)) = true then
      if hF : (softVars F).all (fun v => decide (v < frontier)) = true then
        if hsource : input.rigidVars.all (fun v => decide (v ∈ K ++ softVars F)) = true then
          have hrawScope : SourceScope K F input := fun v hv =>
            of_decide_eq_true (List.all_eq_true.mp hsource v hv)
          match input with
          | .primLit .unit => some ⟨(frontier, [], .primLit .unit, .prim .unit, .root (.prim .unit), []), .primLitUnit⟩
          | .primLit (.int n) => some ⟨(frontier, [], .primLit (.int n), .prim .int, .root (.prim .int), []), .primLitInt⟩
          | .primLit (.nat n) => some ⟨(frontier, [], .primLit (.nat n), .prim .nat, .root (.prim .nat), []), .primLitNat⟩
          | .primLit (.char c) => some ⟨(frontier, [], .primLit (.char c), .prim .char, .root (.prim .char), []), .primLitChar⟩
          | .primBinOp .intAdd =>
              let ty := .arrow (.prim .int) (.arrow (.prim .int) (.prim .int))
              some ⟨(frontier, [], .primBinOp .intAdd, ty, .root ty, []), .primBinOpIntAdd⟩
          | .primBinOp .intSub =>
              let ty := .arrow (.prim .int) (.arrow (.prim .int) (.prim .int))
              some ⟨(frontier, [], .primBinOp .intSub, ty, .root ty, []), .primBinOpIntSub⟩
          | .primBinOp .intLt =>
              match hT : LookupList.get? ctx.ctors ⟨"True"⟩ with
              | none => none
              | some tc =>
                match hF : LookupList.get? ctx.ctors ⟨"False"⟩ with
                | none => none
                | some fc =>
                  if htc : tc.isBoolCtor = true then
                    if hfc : fc.isBoolCtor = true then
                      let ty := .arrow (.prim .int) (.arrow (.prim .int) (.customTy ⟨"Bool"⟩ []))
                      some ⟨(frontier, [], .primBinOp .intLt, ty, .root ty, []),
                            .primBinOpIntLt hT (Ctor.isBoolCtor_iff.mp htc) hF (Ctor.isBoolCtor_iff.mp hfc)⟩
                    else none
                  else none
          | .primBinOp .charLt =>
              match hT : LookupList.get? ctx.ctors ⟨"True"⟩ with
              | none => none
              | some tc =>
                match hF : LookupList.get? ctx.ctors ⟨"False"⟩ with
                | none => none
                | some fc =>
                  if htc : tc.isBoolCtor = true then
                    if hfc : fc.isBoolCtor = true then
                      let ty := .arrow (.prim .char) (.arrow (.prim .char) (.customTy ⟨"Bool"⟩ []))
                      some ⟨(frontier, [], .primBinOp .charLt, ty, .root ty, []),
                            .primBinOpCharLt hT (Ctor.isBoolCtor_iff.mp htc) hF (Ctor.isBoolCtor_iff.mp hfc)⟩
                    else none
                  else none
          | .var index =>
              match hlook : ctx.env[index]? with
              | none => none
              | some scheme =>
                  let ty := scheme.openVars (freshVars frontier scheme.paramCount)
                  some ⟨(frontier + scheme.paramCount, [], .var index, ty, .root ty, []), .var hlook⟩
          | .ctor name =>
              match hlook : LookupList.get? ctx.ctors name with
              | none => none
              | some ctor =>
                  let ty := ctor.toTy.openVars (freshVars frontier ctor.paramCount)
                  some ⟨(frontier + ctor.paramCount, [], .ctor name, ty, .root ty, []), .ctor hlook⟩
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
                if hg : RecGroups.validResidualGroupsB (anns.map BindingAnn.recModeAnn) (bindings.map InferInput.erase)
                    (RecGroup.inferenceSccs (anns.map BindingAnn.recModeAnn) (bindings.map InferInput.erase)) = true then
                  match inferRecStrataWithTypesCore K F (frontier + bindings.length) ctx anns bindings
                      (RecState.init frontier anns)
                      (RecGroup.inferenceSccs (anns.map BindingAnn.recModeAnn) (bindings.map InferInput.erase)) with
                  | none => none
                  | some ⟨strata, hs⟩ =>
                    match inferRecSignedWithTypesCore K (substSoft strata.subst F) 0 strata.frontier
                        (strata.subst.onCtx ctx) (anns.map (BindingAnn.substTyFvars strata.subst))
                        (bindings.map (InferInput.substTyFvars strata.subst)) strata.state with
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
        else none
      else none
    else none
  else none
termination_by (input.size, 0)
decreasing_by all_goals (simp only [InferInput.size, InferInput.size_openTyVars, InferInput.size_substTyFvars, sizeBranches_substInputBranches, sizeBindings_map_substTyFvars]; omega)

def _root_.inferBranchesWithTypesCore (K : List Nat) (Φ : Nat) (ctx : Ctx) (scrutTy : Ty) (ρ : Ty)
    (branchIndex : Nat) (branches : List (MatchPattern × InferInput)) (F : List Ty := []) :
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
  all_goals (try simp only [sizeBranches, InferInput.size_substTyFvars, sizeBranches_substInputBranches]; omega)

/-- One monomorphic component visit, with artifacts in original member order. -/
def _root_.inferRecComponentWithTypesCore (K : List Nat) (F : List Ty) (members : List Nat)
    (index frontier : Nat) (ctx : Ctx) (bindings : List InferInput) (specs : List RecSpec) :
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
                (s2.onCtx (s1.onCtx ctx)) (rest.map (InferInput.substTyFvars (s1 ++ s2)))
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
    (ctx : Ctx) (anns : List BindingAnn) (bindings : List InferInput) (state : RecState)
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
              ((openRecSources openings bindings).map (InferInput.substTyFvars pre))
              (installed.onSubst pre).specs with
          | none => none
          | some ⟨current, hc⟩ =>
            let solved := pre ++ current.subst
            match finishRecComponent K (softVars (substSoft solved F)) component (solved.onCtx ctx)
                (installed.onSubst solved) current.outputs current.facts with
            | none => none
            | some ⟨exported, he⟩ =>
              match inferRecStrataWithTypesCore K (substSoft solved F) current.frontier (solved.onCtx ctx)
                  (anns.map (BindingAnn.substTyFvars solved)) (bindings.map (InferInput.substTyFvars solved))
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
    (ctx : Ctx) (anns : List BindingAnn) (bindings : List InferInput) (state : RecState) :
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
                    (anns.map (BindingAnn.substTyFvars solved)) (rest.map (InferInput.substTyFvars solved))
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
decreasing_by all_goals (simp only [sizeBindings, InferInput.size_openTyVars, sizeBindings_map_substTyFvars]; omega)

end

/-- The plain certificate API projects the one metadata-producing run. -/
def _root_.inferCore (K : List Nat) (frontier : Nat) (ctx : Ctx) (input : InferInput) :
    Option { result : Nat × Subst × Expr × Ty //
      Infer K [] frontier ctx input result.1 result.2.1 result.2.2.1 result.2.2.2 } :=
  match inferWithTypesCore K frontier ctx input with
  | none => none
  | some ⟨(next, subst, output, ty, _, _), h⟩ => some ⟨(next, subst, output, ty), h⟩

@[simp] theorem _root_.inferCore_isSome (K : List Nat) (frontier : Nat) (ctx : Ctx) (input : InferInput) :
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

def InferInput.freshFloor (input : InferInput) : Nat := tyVarCeil input.rigidVars

theorem InferInput.lt_freshFloor {input : InferInput} {v : Nat} (h : v ∈ input.rigidVars) :
    v < input.freshFloor := lt_tyVarCeil h

def _root_.inferWithTypes (ctors : CtorEnv) (input : InferInput) : Option InferenceResult :=
  (inferWithTypesCore input.rigidVars input.freshFloor ⟨[], ctors⟩ input).map fun result =>
    { frontier := result.val.1
      subst := result.val.2.1
      completedExpr := result.val.2.2.1
      ty := result.val.2.2.2.1
      nodeTypes := result.val.2.2.2.2.1.toMap
      binderSchemes := result.val.2.2.2.2.2.toMap }

def _root_.principalType (ctors : CtorEnv) (input : InferInput) : Option Ty :=
  (inferCore input.rigidVars input.freshFloor ⟨[], ctors⟩ input).map (·.val.2.2.2)

def _root_.typecheck (ctors : CtorEnv) (input : InferInput) : Option PolyTy :=
  (principalType ctors input).map (genScheme [] [])

/-- A public artifact result carries the canonical elaboration derivation. -/
theorem _root_.inferWithTypes_infer {ctors : CtorEnv} {input : InferInput} {result : InferenceResult}
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

end

/-! ## Properties -/

section

private theorem override_freshVars_getElem? {Φ n i : Nat} (hi : i < n) :
    (freshVars Φ n)[i]? = some (Φ + i) := by
  simp only [freshVars, List.getElem?_map, List.getElem?_range hi, Option.map_some]

/-- Assign a freshly allocated block arbitrary LC targets while preserving an
existing substitution on every earlier variable. Targets may mention the block. -/
theorem Subst.override_block {S0 : Subst} (hS0 : ∀ p ∈ S0, p.2.IsLC)
    (Φ : Nat) (ts : List Ty) (hts : ∀ t ∈ ts, t.IsLC) :
    ∃ U : Subst, (∀ p ∈ U, p.2.IsLC) ∧ Subst.AgreesBelow Φ S0 U ∧
      ∀ i (hi : i < ts.length), U.onTy (.fvar (Φ + i)) = ts[i] := by
  obtain ⟨W, hWge, hWfresh⟩ := exists_fresh_block
    (S0.map Prod.fst ++ S0.flatMap (fun p => p.2.freeVars) ++ ts.flatMap Ty.freeVars)
    Φ ts.length
  let A : Subst := (freshVars Φ ts.length).zip ((freshVars W ts.length).map Ty.fvar)
  let C : Subst := (freshVars W ts.length).zip ts
  let U : Subst := A ++ S0 ++ C
  have hUonTy : ∀ x, U.onTy x = C.onTy (S0.onTy (A.onTy x)) := by
    intro x; exact (Subst.onTy_append _ _ _).trans (congrArg C.onTy (Subst.onTy_append _ _ _))
  have hkeys : ∀ w ∈ freshVars W ts.length, w ∉ S0.map Prod.fst := by
    intro w hw hc
    have := freshVars_ge w hw
    have := hWfresh w (List.mem_append_left _ (List.mem_append_left _ hc))
    omega
  have hranges : ∀ w ∈ freshVars W ts.length, ∀ p ∈ S0, w ∉ p.2.freeVars := by
    intro w hw p hp hc
    have := freshVars_ge w hw
    have := hWfresh w (List.mem_append_left _ (List.mem_append_right _
      (List.mem_flatMap.mpr ⟨p, hp, hc⟩)))
    omega
  have htargets : ∀ t ∈ ts, Ty.BelowFvars W t := by
    intro t ht
    apply Ty.BelowFvars.of_freeVars_lt
    intro v hv
    exact hWfresh v (List.mem_append_right _ (List.mem_flatMap.mpr ⟨t, ht, hv⟩))
  refine ⟨U, ?_, ?_, ?_⟩
  · intro p hp
    rcases List.mem_append.mp hp with hp | hp
    · rcases List.mem_append.mp hp with hp | hp
      · obtain ⟨x, _, heq⟩ := List.mem_map.mp (List.of_mem_zip hp).2
        rw [← heq]; exact .fvar
      · exact hS0 p hp
    · exact hts p.2 (List.of_mem_zip hp).2
  · intro v hv
    symm
    rw [hUonTy]
    have hA : A.onTy (.fvar v) = .fvar v := by
      apply Ty.substFvars_eq_self_of_no_key
      intro p hp hc
      simp only [Ty.freeVars, List.mem_singleton] at hc
      have := freshVars_ge p.1 (List.of_mem_zip hp).1
      omega
    rw [hA]
    apply Ty.substFvars_eq_self_of_no_key
    intro p hp hc
    have hw := (List.of_mem_zip hp).1
    exact Subst.not_mem_onTy_freeVars (hranges p.1 hw)
      (by simp only [Ty.freeVars, List.mem_singleton]; have := freshVars_ge p.1 hw; omega) hc
  · intro i hi
    rw [hUonTy]
    have hA : A.onTy (.fvar (Φ + i)) = .fvar (W + i) := by
      apply Ty.substFvars_zip_fvar_eq' freshVars_nodup (override_freshVars_getElem? hi)
      · rw [List.getElem?_map, override_freshVars_getElem? hi]; rfl
      · intro x hx hc
        simp only [Ty.freeVars, List.mem_singleton] at hc
        have := freshVars_lt x hx
        omega
    rw [hA]
    have hS : S0.onTy (.fvar (W + i)) = .fvar (W + i) := by
      apply Ty.substFvars_eq_self_of_no_key
      intro p hp hc
      simp only [Ty.freeVars, List.mem_singleton] at hc
      apply hkeys (W + i)
      · simp only [freshVars, List.mem_map, List.mem_range]
        exact ⟨i, hi, rfl⟩
      · rw [← hc]; exact List.mem_map.mpr ⟨p, hp, rfl⟩
    rw [hS]
    apply Ty.substFvars_zip_fvar_eq' freshVars_nodup (override_freshVars_getElem? hi)
      (List.getElem?_eq_getElem hi)
    intro w hw hc
    have := freshVars_ge w hw
    have := (htargets ts[i] (List.getElem_mem hi)).mem_lt w hc
    omega

mutual
private theorem transformed_hole_targets (template : TyTemplate) {S0 : Subst} {target : Ty}
    (h : (template.substTyFvars S0).Fits target) (hlc : target.IsLC) (Φ : Nat) :
    ∃ ts : List Ty, (template.allocate Φ).1 = Φ + ts.length ∧
      (∀ t ∈ ts, t.IsLC) ∧ ∀ U : Subst,
      (∀ v ∈ template.rigidVars, U.onTy (.fvar v) = S0.onTy (.fvar v)) →
      (∀ i (hi : i < ts.length), U.onTy (.fvar (Φ + i)) = ts[i]) →
      U.onTy (template.allocate Φ).2 = target := by
  cases template with
  | fixed ty =>
    cases h
    exact ⟨[], rfl, by simp, fun _ hr _ => TyTemplate.fixed.inj ((TyTemplate.fixed ty).substTyFvars_congr hr)⟩
  | hole =>
    refine ⟨[target], rfl, ?_, ?_⟩
    · simpa using hlc
    · intro U _ hb
      simpa only [Nat.add_zero] using hb 0 (by simp)
  | arrow a b =>
    cases h with
    | arrow ha hb =>
       cases hlc with
        | arrow hlca hlcb =>
          obtain ⟨as, halen, halc, haeq⟩ := transformed_hole_targets a ha hlca Φ
          obtain ⟨bs, hblen, hblc, hbeq⟩ := transformed_hole_targets b hb hlcb (a.allocate Φ).1
          refine ⟨as ++ bs, ?_, ?_, ?_⟩
          · change (b.allocate (a.allocate Φ).1).1 = Φ + (as ++ bs).length
            rw [hblen, halen, List.length_append, Nat.add_assoc]
          · intro t ht; exact (List.mem_append.mp ht).elim (halc t) (hblc t)
          · intro U hr hblock
            simp only [TyTemplate.allocate, Subst.onTy_arrow]
            congr 1
            · apply haeq U (fun v hv => hr v (List.mem_append_left _ hv))
              intro i hi
              have heq := hblock i (by simp only [List.length_append]; omega)
              rwa [List.getElem_append_left hi] at heq
            · apply hbeq U (fun v hv => hr v (List.mem_append_right _ hv))
              intro i hi
              have heq := hblock (as.length + i) (by simp only [List.length_append]; omega)
              rw [List.getElem_append_right (by omega)] at heq
              simpa only [halen, Nat.add_assoc, Nat.add_sub_cancel_left] using heq
  | custom name templates =>
    cases h with
    | custom h =>
      cases hlc with
      | customTy hlcs =>
        obtain ⟨ts, hlen, hlc, heq⟩ := transformed_hole_targets_list templates h hlcs Φ
        refine ⟨ts, hlen, hlc, ?_⟩
        intro U hr hb
        simp only [TyTemplate.allocate, Subst.onTy_customTy, heq U hr hb]
private theorem transformed_hole_targets_list (templates : List TyTemplate) {S0 : Subst} {targets : List Ty}
    (h : List.Forall₂ TyTemplate.Fits (substTemplateList S0 templates) targets)
    (hlc : ∀ t ∈ targets, t.IsLC) (Φ : Nat) :
    ∃ ts : List Ty, (allocateList Φ templates).1 = Φ + ts.length ∧
      (∀ t ∈ ts, t.IsLC) ∧ ∀ U : Subst,
      (∀ v ∈ rigidVarsList templates, U.onTy (.fvar v) = S0.onTy (.fvar v)) →
      (∀ i (hi : i < ts.length), U.onTy (.fvar (Φ + i)) = ts[i]) →
      (allocateList Φ templates).2.map U.onTy = targets := by
  cases templates with
  | nil => cases h; exact ⟨[], rfl, by simp, by simp [allocateList]⟩
  | cons template templates =>
    cases h with
    | cons hh ht =>
      obtain ⟨as, halen, halc, haeq⟩ := transformed_hole_targets template hh (hlc _ List.mem_cons_self) Φ
      obtain ⟨bs, hblen, hblc, hbeq⟩ := transformed_hole_targets_list templates ht
        (fun t ht => hlc t (List.mem_cons_of_mem _ ht)) (template.allocate Φ).1
      refine ⟨as ++ bs, ?_, ?_, ?_⟩
      · change (allocateList (template.allocate Φ).1 templates).1 = Φ + (as ++ bs).length
        rw [hblen, halen, List.length_append, Nat.add_assoc]
      · intro t ht; exact (List.mem_append.mp ht).elim (halc t) (hblc t)
      · intro U hr hblock
        simp only [allocateList, List.map_cons]
        congr 1
        · apply haeq U (fun v hv => hr v (List.mem_append_left _ hv))
          intro i hi
          have heq := hblock i (by simp only [List.length_append]; omega)
          rwa [List.getElem_append_left hi] at heq
        · apply hbeq U (fun v hv => hr v (List.mem_append_right _ hv))
          intro i hi
          have heq := hblock (as.length + i) (by simp only [List.length_append]; omega)
          rw [List.getElem_append_right (by omega)] at heq
          simpa only [halen, Nat.add_assoc, Nat.add_sub_cancel_left] using heq
end

/-- A target fitting the ambient-substituted source is realizable from the
original allocation while preserving ambient behavior below its frontier.
Neither frozen raw leaves nor fresh target names are required. -/
theorem TyTemplate.Fits.allocate_override_source {template : TyTemplate} {target : Ty} {S0 : Subst}
    (h : (template.substTyFvars S0).Fits target) (hlc : target.IsLC)
    (hS0 : ∀ p ∈ S0, p.2.IsLC) (Φ : Nat)
    (hrigid : ∀ v ∈ template.rigidVars, v < Φ) :
    ∃ U : Subst, (∀ p ∈ U, p.2.IsLC) ∧ Subst.AgreesBelow Φ S0 U ∧
      U.onTy (template.allocate Φ).2 = target := by
  obtain ⟨ts, _, hts, htemplate⟩ := transformed_hole_targets template h hlc Φ
  obtain ⟨U, hUlc, hUagree, hUblock⟩ := Subst.override_block hS0 Φ ts hts
  exact ⟨U, hUlc, hUagree, htemplate U
    (fun v hv => (hUagree v (hrigid v hv)).symm) hUblock⟩

/-- Fixed-source compatibility follows from the source-transforming allocator. -/
theorem TyTemplate.Fits.allocate_override {template : TyTemplate} {target : Ty}
    (h : template.Fits target) (hlc : target.IsLC) {S0 : Subst}
    (hS0 : ∀ p ∈ S0, p.2.IsLC) (Φ : Nat)
    (hrigid : ∀ v ∈ template.rigidVars, v < Φ)
    (hfix : ∀ v ∈ template.rigidVars, S0.onTy (.fvar v) = .fvar v) :
    ∃ U : Subst, (∀ p ∈ U, p.2.IsLC) ∧ Subst.AgreesBelow Φ S0 U ∧
      U.onTy (template.allocate Φ).2 = target := by
  have hsource : template.substTyFvars S0 = template := template.substTyFvars_eq_self_of_fixes hfix
  exact (hsource.symm ▸ h).allocate_override_source hlc hS0 Φ hrigid

theorem softVars_lt {F : List Ty} (hF : ∀ t ∈ F, Ty.BelowFvars frontier t) :
    ∀ v ∈ softVars F, v < frontier := by
  intro v hv
  obtain ⟨t, ht, hv⟩ := TyList.mem_freeVars_iff.mp hv
  exact (hF t ht).mem_lt v hv

theorem substSoft_below {S : Subst} {F : List Ty}
    (hS : ∀ p ∈ S, Ty.BelowFvars next p.2) (hle : frontier ≤ next)
    (hF : ∀ t ∈ F, Ty.BelowFvars frontier t) :
    ∀ t ∈ substSoft S F, Ty.BelowFvars next t := by
  intro t ht
  obtain ⟨u, hu, rfl⟩ := List.mem_map.mp ht
  exact Subst.onTy_belowFvars hS ((hF u hu).mono hle)

private theorem rigid_soft_lt {K F frontier}
    (hK : ∀ k ∈ K, k < frontier) (hF : ∀ t ∈ F, Ty.BelowFvars frontier t) :
    ∀ v ∈ K ++ softVars F, v < frontier :=
  fun v hv => (List.mem_append.mp hv).elim (hK v) (softVars_lt hF v)

theorem Seed.frontier_le (h : Seed K frontier ann param initial) : frontier ≤ initial := by
  cases h with
  | absent => omega
  | @annotated next ty template heq _ _ =>
    have hle := (template.allocate_bounds frontier).1
    rwa [heq] at hle

theorem Seed.belowFvars (h : Seed K frontier ann param initial)
    (hK : ∀ k ∈ K, k < frontier) : Ty.BelowFvars initial param := by
  cases h with
  | absent => exact .fvar (by omega)
  | @annotated next ty template heq _ hr =>
    have hb := (template.allocate_bounds frontier).2 (fun v hv => hK v (hr v hv))
    rwa [heq] at hb

theorem LetCheck.frontier_le (h : LetCheck K F frontier ty ann next subst) : frontier ≤ next := by
  cases h with
  | absent => omega
  | hole => omega
  | @template next expected subst sourceTemplate heq _ _ _ =>
    have hle := (sourceTemplate.allocate_bounds frontier).1
    rwa [heq] at hle

theorem LetCheck.belowFvars (h : LetCheck K F frontier ty ann next subst)
    (hty : Ty.BelowFvars frontier ty) (hK : ∀ k ∈ K, k < frontier)
    (hF : ∀ t ∈ F, Ty.BelowFvars frontier t) :
    ∀ p ∈ subst, Ty.BelowFvars next p.2 := by
  cases h with
  | absent => simp
  | hole => simp
  | @template next expected subst sourceTemplate heq _ hr hu =>
    have hb := (sourceTemplate.allocate_bounds frontier).2 (fun v hv => rigid_soft_lt hK hF v (hr v hv))
    rw [heq] at hb
    have hle := (sourceTemplate.allocate_bounds frontier).1
    rw [heq] at hle
    exact hu.unifies.belowFvars (hty.mono hle) hb

theorem SignatureCheck.frontier_le (h : SignatureCheck K F written frontier ty ann next subst) :
    frontier ≤ next := by
  cases h with
  | complete => exact Nat.le_refl _
  | @partialSignature next expected subst count template heq _ _ _ =>
      have hle := ((template.openTyVarsFrom 0 written).allocate_bounds frontier).1
      rwa [heq] at hle

theorem SignatureCheck.belowFvars (h : SignatureCheck K F written frontier ty ann next subst)
    (hty : Ty.BelowFvars frontier ty) (hK : ∀ k ∈ K, k < frontier)
    (hwritten : ∀ name ∈ written, name < frontier)
    (hF : ∀ t ∈ F, Ty.BelowFvars frontier t) :
    ∀ p ∈ subst, Ty.BelowFvars next p.2 := by
  cases h with
  | complete _ hr hu =>
      exact hu.unifies.belowFvars hty
        (Ty.openVars_belowFvars (Ty.BelowFvars.of_freeVars_lt (fun v hv => rigid_soft_lt hK hF v (hr v hv))) hwritten)
  | @partialSignature next expected subst count template heq _ hr hu =>
      have hb := ((template.openTyVarsFrom 0 written).allocate_bounds frontier).2
        (fun v hv => (List.mem_append.mp (TyTemplate.open_scope hr v hv)).elim (rigid_soft_lt hK hF v) (hwritten v))
      rw [heq] at hb
      have hle := ((template.openTyVarsFrom 0 written).allocate_bounds frontier).1
      rw [heq] at hle
      exact hu.unifies.belowFvars (hty.mono hle) hb

theorem SignatureCheck.scheme_belowFvars (h : SignatureCheck K F written frontier ty ann next subst)
    (hty : Ty.BelowFvars next (subst.onTy ty))
    (hrigid : ∀ v ∈ (ann.substTyFvars subst).rigidVars, v < next) :
    Ty.BelowFvars next (signatureScheme (ann.substTyFvars subst) Q written ctx (subst.onTy ty)).body := by
  cases h with
  | complete _ _ _ => exact Ty.BelowFvars.of_freeVars_lt hrigid
  | partialSignature => exact hty.closeOver

set_option maxHeartbeats 400000 in
mutual
theorem _root_.Infer.frontier_le (h : Infer K F frontier ctx input next subst output ty) : frontier ≤ next := by
  match h with
  | .primLitUnit | .primLitInt | .primLitNat | .primLitChar | .primBinOpIntAdd | .primBinOpIntSub | .primBinOpIntLt _ _ _ _ | .primBinOpCharLt _ _ _ _ => exact Nat.le_refl _
  | .var _ | .ctor _ => exact Nat.le_add_right _ _
  | .lambda _ hs hb => exact hs.frontier_le.trans hb.frontier_le
  | .app _ hf ha _ => have := hf.frontier_le; have := ha.frontier_le; omega
  | .letIn _ hr hc hb => exact hr.frontier_le.trans (hc.frontier_le.trans hb.frontier_le)
  | .letSignature _ _ _ _ hr hc _ hb =>
      have := hr.frontier_le
      have := hc.frontier_le
      have := hb.frontier_le
      omega
  | .match_ _ hs _ hb => have := hs.frontier_le; have := hb.frontier_le; omega
  | .letRec _ _ _ hstrata hsigned _ _ hbody =>
      have := hstrata.frontier_le; have := hsigned.frontier_le; have := hbody.frontier_le; omega
termination_by (input.size, 0)
decreasing_by all_goals (simp only [InferInput.size, InferInput.size_openTyVars, InferInput.size_substTyFvars, sizeBranches_substInputBranches, sizeBindings_map_substTyFvars] at *; omega)

theorem _root_.InferBranches.frontier_le
    (h : InferBranches K F frontier ctx scrutTy resultTy branches next subst output) : frontier ≤ next := by
  match h with
  | .nil => omega
  | .cons _ _ _ _ hb _ hr => have := hb.frontier_le; have := hr.frontier_le; omega
  | .consWild _ hb _ hr => have := hb.frontier_le; have := hr.frontier_le; omega
termination_by (sizeBranches branches, 0)
decreasing_by all_goals (simp only [sizeBranches, InferInput.size_substTyFvars, sizeBranches_substInputBranches]; omega)

theorem _root_.InferRecComponent.frontier_le
    (h : InferRecComponent K F members index frontier ctx bindings specs next S outputs facts) :
    frontier ≤ next := by
  match h with
  | .nil => exact Nat.le_refl _
  | .skipMono _ hr | .skipPoly hr => exact hr.frontier_le
  | .consSelected _ hi _ hr => exact hi.frontier_le.trans hr.frontier_le
termination_by (sizeBindings bindings, 0)
decreasing_by all_goals (simp only [sizeBindings, sizeBindings_map_substTyFvars]; omega)

theorem _root_.InferRecStrata.frontier_le
    (h : InferRecStrata K F frontier ctx anns bindings state groups next S final) : frontier ≤ next := by
  match h with
  | .nil => exact Nat.le_refl _
  | .cons ho _ hc _ hr => exact ho.frontier_le.trans (hc.frontier_le.trans hr.frontier_le)
termination_by (sizeBindings bindings, groups.length + 1)
decreasing_by all_goals (simp only [sizeBindings_map_substTyFvars, sizeBindings_openRecSources, List.length_cons]; omega)

theorem _root_.InferRecSigned.frontier_le
    (h : InferRecSigned K F index frontier ctx anns bindings state next S final) : frontier ≤ next := by
  match h with
  | .nil => exact Nat.le_refl _
  | .skip _ hr => exact hr.frontier_le
  | .cons _ _ hi _ _ hr => have := hi.frontier_le; have := hr.frontier_le; omega
termination_by (sizeBindings bindings, 0)
decreasing_by all_goals (simp only [sizeBindings, InferInput.size_openTyVars, sizeBindings_map_substTyFvars]; omega)
end


private theorem anns_below_subst {anns : List BindingAnn}
    (h : ∀ ann ∈ anns, ∀ v ∈ ann.rigidVars, v < frontier)
    (hS : ∀ p ∈ S, Ty.BelowFvars next p.2) (hle : frontier ≤ next) :
    ∀ ann ∈ anns.map (BindingAnn.substTyFvars S), ∀ v ∈ ann.rigidVars, v < next := by
  intro ann hm v hv
  obtain ⟨old, hold, rfl⟩ := List.mem_map.mp hm
  obtain ⟨k, hk, hv⟩ := BindingAnn.rigidVars_substTyFvars hv
  exact (Subst.onTy_belowFvars hS (.fvar (Nat.lt_of_lt_of_le (h old hold k hk) hle))).mem_lt v hv

private theorem specs_below_subst {specs : List RecSpec}
    (h : ∀ spec ∈ specs, spec.BelowFvars frontier)
    (hS : ∀ p ∈ S, Ty.BelowFvars next p.2) (hle : frontier ≤ next) :
    ∀ spec ∈ specs.map (RecSpec.onSubstSource S), spec.BelowFvars next := by
  intro spec hm
  obtain ⟨old, hold, rfl⟩ := List.mem_map.mp hm
  cases old with
  | mono ty => exact Subst.onTy_belowFvars hS ((h _ hold).mono hle)
  | poly scheme => exact Subst.onTy_belowFvars hS ((h _ hold).mono hle)

 theorem RecState.shapes_below {state : RecState} {openings : List RecOpening}
    (hstate : state.Below frontier)
    (hopen : ∀ opening ∈ openings, ∀ ty, opening.expected = some ty → Ty.BelowFvars frontier ty) :
    ∀ shape ∈ state.shapes members openings, RecShape.BelowFvars frontier shape := by
  intro shape hm
  obtain ⟨i, _, heq⟩ := List.mem_filterMap.mp hm
  cases hs : state.specs[i]? with
  | none => simp [hs] at heq
  | some spec =>
    cases spec with
    | poly σ => simp [hs, RecSpec.monoTy?] at heq
    | mono ty =>
      cases ho : openings[i]? with
      | none => simp [hs, RecSpec.monoTy?, ho] at heq
      | some opening =>
        simp [hs, RecSpec.monoTy?, ho] at heq
        subst shape
        exact ⟨hstate.1 _ (List.mem_of_getElem? hs), hopen opening (List.mem_of_getElem? ho)⟩

 theorem _root_.InferRecComponent.belowFvars_of_infer
    (h : InferRecComponent K F members index frontier ctx bindings specs next S outputs facts)
    (hInfer : ∀ {κ F' Ψ c e Ψ' T output ty}, e.size ≤ sizeBindings bindings →
      Infer κ F' Ψ c e Ψ' T output ty → CtxBelow Ψ c → (∀ k ∈ κ, k < Ψ) →
      (∀ t ∈ F', Ty.BelowFvars Ψ t) → Ty.BelowFvars Ψ' ty ∧ ∀ p ∈ T, Ty.BelowFvars Ψ' p.2)
    (hctx : CtxBelow frontier ctx) (hK : ∀ k ∈ K, k < frontier)
    (hF : ∀ t ∈ F, Ty.BelowFvars frontier t) (hspec : ∀ spec ∈ specs, spec.BelowFvars frontier) :
    ∀ p ∈ S, Ty.BelowFvars next p.2 := by
  match h with
  | .nil => simp
  | .skipMono _ hr | .skipPoly hr =>
      exact hr.belowFvars_of_infer (fun he h => hInfer (by simp only [sizeBindings]; omega) h)
        hctx hK hF (fun spec hm => hspec spec (List.mem_cons_of_mem _ hm))
  | .consSelected _ hi hu hr =>
      expose_names
      have hle := hi.frontier_le
      have hrle := hr.frontier_le
      obtain ⟨hiTy, hiS⟩ := hInfer (by simp only [sizeBindings]; omega) hi hctx hK hF
      have huS := hu.unifies.belowFvars hiTy (Subst.onTy_belowFvars hiS ((hspec _ List.mem_cons_self).mono hle))
      have hboth : ∀ p ∈ s1 ++ s2, Ty.BelowFvars first p.2 :=
        fun p hp => (List.mem_append.mp hp).elim (hiS p) (huS p)
      have hrS := hr.belowFvars_of_infer
        (fun he h => hInfer (by simp only [sizeBindings_map_substTyFvars] at he; simp only [sizeBindings]; omega) h)
        (by simpa only [Subst.onCtx_append] using Subst.onCtx_below hboth hle hctx)
        (fun k hk => Nat.lt_of_lt_of_le (hK k hk) hle)
        (substSoft_below hboth hle hF)
        (specs_below_subst (fun spec hm => hspec spec (List.mem_cons_of_mem _ hm)) hboth hle)
      intro p hp
      exact (List.mem_append.mp hp).elim (fun hp => (hboth p hp).mono hrle) (hrS p)
 termination_by structural h

 theorem _root_.InferRecStrata.belowFvars_of_infer
    (h : InferRecStrata K F frontier ctx anns bindings state groups next S final)
    (hInfer : ∀ {κ F' Ψ c e Ψ' T output ty}, e.size ≤ sizeBindings bindings →
      Infer κ F' Ψ c e Ψ' T output ty → CtxBelow Ψ c → (∀ k ∈ κ, k < Ψ) →
      (∀ t ∈ F', Ty.BelowFvars Ψ t) → Ty.BelowFvars Ψ' ty ∧ ∀ p ∈ T, Ty.BelowFvars Ψ' p.2)
    (hctx : CtxBelow frontier ctx) (hK : ∀ k ∈ K, k < frontier)
    (hF : ∀ t ∈ F, Ty.BelowFvars frontier t) (hstate : state.Below frontier)
    (hanns : ∀ ann ∈ anns, ∀ v ∈ ann.rigidVars, v < frontier) :
    (∀ p ∈ S, Ty.BelowFvars next p.2) ∧ final.Below next := by
  match h with
  | .nil => exact ⟨by simp, hstate⟩
  | .cons hopen hshape hcomponent hfinish hrest =>
    expose_names
    have hle := hopen.frontier_le
    have hcle := hcomponent.frontier_le
    have hrle := hrest.frontier_le
    have hinit := hstate.installOpenings hopen
    have hpre := hshape.belowFvars (RecState.shapes_below hinit (hopen.expected_below hanns))
    have hFopened : ∀ t ∈ F ++ (openings.flatMap RecOpening.written).map Ty.fvar, Ty.BelowFvars opened t := by
      intro t ht
      rcases List.mem_append.mp ht with ht | ht
      · exact (hF t ht).mono hle
      · obtain ⟨v, hv, rfl⟩ := List.mem_map.mp ht
        exact .fvar (hopen.written_range v hv).2
    have hcurrent := hcomponent.belowFvars_of_infer
      (fun he h => hInfer (by simpa only [sizeBindings_map_substTyFvars, sizeBindings_openRecSources] using he) h)
      ((hinit.onSubst hpre (Nat.le_refl _)).rhsCtx (Subst.onCtx_below hpre hle hctx))
      (fun k hk => Nat.lt_of_lt_of_le (hK k hk) hle)
      (substSoft_below hpre (Nat.le_refl _) hFopened) (hinit.onSubst hpre (Nat.le_refl _)).1
    have hboth : ∀ p ∈ pre ++ current, Ty.BelowFvars first p.2 :=
      fun p hp => (List.mem_append.mp hp).elim (fun hp => (hpre p hp).mono hcle) (hcurrent p)
    have hfullle := hle.trans hcle
    obtain ⟨htail, hfinal⟩ := hrest.belowFvars_of_infer
      (fun he h => hInfer (by simpa only [sizeBindings_map_substTyFvars] using he) h)
      (Subst.onCtx_below hboth hfullle hctx)
      (fun k hk => Nat.lt_of_lt_of_le (hK k hk) hfullle)
      (substSoft_below hboth hfullle hF)
      (hfinish.below (hinit.onSubst hboth hcle))
      (anns_below_subst hanns hboth hfullle)
    exact ⟨fun p hp => (List.mem_append.mp hp).elim (fun hp => (hboth p hp).mono hrle) (htail p), hfinal⟩
 termination_by structural h

 theorem _root_.InferRecSigned.belowFvars_of_infer
    (h : InferRecSigned K F index frontier ctx anns bindings state next S final)
    (hInfer : ∀ {κ F' Ψ c e Ψ' T output ty}, e.size ≤ sizeBindings bindings →
      Infer κ F' Ψ c e Ψ' T output ty → CtxBelow Ψ c → (∀ k ∈ κ, k < Ψ) →
      (∀ t ∈ F', Ty.BelowFvars Ψ t) → Ty.BelowFvars Ψ' ty ∧ ∀ p ∈ T, Ty.BelowFvars Ψ' p.2)
    (hctx : CtxBelow frontier ctx) (hK : ∀ k ∈ K, k < frontier)
    (hF : ∀ t ∈ F, Ty.BelowFvars frontier t) (hstate : state.Below frontier)
    (hanns : ∀ ann ∈ anns, ∀ v ∈ ann.rigidVars, v < frontier) :
    (∀ p ∈ S, Ty.BelowFvars next p.2) ∧ final.Below next := by
  match h with
  | .nil => exact ⟨by simp, hstate⟩
  | .skip _ hr =>
      exact hr.belowFvars_of_infer (fun he h => hInfer (by simp only [sizeBindings]; omega) h)
        hctx hK hF hstate (fun ann ha => hanns ann (List.mem_cons_of_mem _ ha))
  | .cons _ _ hi hu _ hr =>
      expose_names
      have hle := hi.frontier_le
      have hrle := hr.frontier_le
      have hbase : frontier ≤ first := by omega
      obtain ⟨hiTy, hiS⟩ := hInfer (by simp only [InferInput.size_openTyVars, sizeBindings]; omega) hi
        (fun M hm => ((hstate.rhsCtx hctx) M hm).mono (by omega))
        (by
          intro k hk
          rcases List.mem_append.mp hk with hk | hk
          · have := hK k hk; omega
          · exact freshVars_lt k hk)
        (fun t ht => (hF t ht).mono (by omega))
      have hexpected : Ty.BelowFvars first ((s1.onPolyTy scheme).openVars (freshVars frontier scheme.paramCount)) :=
        Ty.openVars_belowFvars (Subst.onTy_belowFvars hiS
          ((Ty.BelowFvars.of_freeVars_lt (hanns _ List.mem_cons_self)).mono hbase))
          (fun v hv => Nat.lt_of_lt_of_le (freshVars_lt v hv) hle)
      have huS := hu.unifies.belowFvars hiTy hexpected
      have hboth : ∀ p ∈ s1 ++ s2, Ty.BelowFvars first p.2 :=
        fun p hp => (List.mem_append.mp hp).elim (hiS p) (huS p)
      obtain ⟨htail, hfinal⟩ := hr.belowFvars_of_infer
        (fun he h => hInfer (by simp only [sizeBindings_map_substTyFvars] at he; simp only [sizeBindings]; omega) h)
        (Subst.onCtx_below hboth hbase hctx)
        (fun k hk => Nat.lt_of_lt_of_le (hK k hk) hbase)
        (substSoft_below hboth hbase hF) ((hstate.onSubst hboth hbase).setSigned)
        (anns_below_subst (fun ann ha => hanns ann (List.mem_cons_of_mem _ ha)) hboth hbase)
      exact ⟨fun p hp => (List.mem_append.mp hp).elim (fun hp => (hboth p hp).mono hrle) (htail p), hfinal⟩
 termination_by structural h

mutual
theorem _root_.Infer.belowFvars (h : Infer K F frontier ctx input next subst output ty) :
    CtxBelow frontier ctx → (∀ k ∈ K, k < frontier) →
      (∀ t ∈ F, Ty.BelowFvars frontier t) →
      Ty.BelowFvars next ty ∧ ∀ p ∈ subst, Ty.BelowFvars next p.2 := by
  match h with
  | .primLitUnit => intro _ _ _; exact ⟨.prim, by simp⟩
  | .primLitInt => intro _ _ _; exact ⟨.prim, by simp⟩
  | .primLitNat => intro _ _ _; exact ⟨.prim, by simp⟩
  | .primLitChar => intro _ _ _; exact ⟨.prim, by simp⟩
  | .primBinOpIntAdd => intro _ _ _; exact ⟨.arrow .prim (.arrow .prim .prim), by simp⟩
  | .primBinOpIntSub => intro _ _ _; exact ⟨.arrow .prim (.arrow .prim .prim), by simp⟩
  | .primBinOpIntLt _ _ _ _ => intro _ _ _; exact ⟨.arrow .prim (.arrow .prim (.customTy (by simp))), by simp⟩
  | .primBinOpCharLt _ _ _ _ => intro _ _ _; exact ⟨.arrow .prim (.arrow .prim (.customTy (by simp))), by simp⟩
  | .var hlook =>
      intro hctx _ _
      refine ⟨?_, by simp⟩
      exact Ty.openVars_belowFvars ((hctx _ (List.mem_of_getElem? hlook)).mono (by omega))
        (fun x hx => by have := freshVars_lt x hx; omega)
  | .ctor hlook =>
      intro _ _ _
      refine ⟨?_, by simp⟩
      exact Ty.openVars_belowFvars (Ty.BelowFvars.of_noFreeVars (Ctor.toTy_body_noFreeVars _))
        (fun x hx => by have := freshVars_lt x hx; omega)
  | .lambda _ hs hb =>
    intro hctx hK hF
    have hle := hs.frontier_le
    have hparam := hs.belowFvars (rigid_soft_lt hK hF)
    obtain ⟨hbTy, hbSubst⟩ := hb.belowFvars (by
      intro M hM
      rcases List.mem_cons.mp hM with rfl | hM
      · exact hparam
      · exact (hctx M hM).mono hle)
      (fun k hk => Nat.lt_of_lt_of_le (hK k hk) hle)
      (fun t ht => (hF t ht).mono hle)
    exact ⟨.arrow (Subst.onTy_belowFvars hbSubst (hparam.mono hb.frontier_le)) hbTy, hbSubst⟩
  | .app _ hf ha hu =>
    intro hctx hK hF
    have hfLe := hf.frontier_le
    have haLe := ha.frontier_le
    obtain ⟨hfTy, hfSubst⟩ := hf.belowFvars hctx hK hF
    obtain ⟨haTy, haSubst⟩ := ha.belowFvars (Subst.onCtx_below hfSubst hfLe hctx)
      (fun k hk => Nat.lt_of_lt_of_le (hK k hk) hfLe)
      (substSoft_below hfSubst hfLe hF)
    have huni := hu.unifies.belowFvars
      (Subst.onTy_belowFvars (fun p hp => (haSubst p hp).mono (Nat.le_succ _))
        (hfTy.mono (haLe.trans (Nat.le_succ _))))
      (.arrow (haTy.mono (Nat.le_succ _)) (.fvar (Nat.lt_succ_self _)))
    refine ⟨Subst.onTy_belowFvars huni (.fvar (Nat.lt_succ_self _)), ?_⟩
    intro p hp
    rcases List.mem_append.mp hp with hp | hp
    · rcases List.mem_append.mp hp with hp | hp
      · exact (hfSubst p hp).mono (haLe.trans (Nat.le_succ _))
      · exact (haSubst p hp).mono (Nat.le_succ _)
    · exact huni p hp
  | .letIn _ hr hc hb =>
    intro hctx hK hF
    have hrLe := hr.frontier_le
    have hcLe := hc.frontier_le
    have hbLe := hb.frontier_le
    obtain ⟨hrTy, hrSubst⟩ := hr.belowFvars hctx hK hF
    have hFfirst := substSoft_below hrSubst hrLe hF
    have hcSubst := hc.belowFvars hrTy (fun k hk => Nat.lt_of_lt_of_le (hK k hk) hrLe) hFfirst
    have hcTy := Subst.onTy_belowFvars hcSubst (hrTy.mono hcLe)
    have hcheckedCtx := Subst.onCtx_below hcSubst hcLe
      (Subst.onCtx_below hrSubst hrLe hctx)
    obtain ⟨hbTy, hbSubst⟩ := hb.belowFvars (by
      intro M hM
      rcases List.mem_cons.mp hM with rfl | hM
      · exact hcTy.closeOver
      · exact hcheckedCtx M hM)
      (fun k hk => Nat.lt_of_lt_of_le (hK k hk) (hrLe.trans hcLe))
      (by simpa only [substSoft_append] using substSoft_below hcSubst hcLe hFfirst)
    refine ⟨hbTy, ?_⟩
    intro p hp
    rcases List.mem_append.mp hp with hp | hp
    · rcases List.mem_append.mp hp with hp | hp
      · exact (hrSubst p hp).mono (hcLe.trans hbLe)
      · exact (hcSubst p hp).mono hbLe
    · exact hbSubst p hp

  | @Infer.letSignature K F ann rhs body written frontier ctx first s1 rhsOut rhsTy checked sCheck
      next s2 bodyOut bodyTy _ hprefix _ _ hr hc _ hb =>
    intro hctx hK hF
    have hrLe := hr.frontier_le
    have hcLe := hc.frontier_le
    have hbLe := hb.frontier_le
    obtain ⟨hrTy, hrSubst⟩ := hr.belowFvars
      (fun M hM => (hctx M hM).mono (by omega)) (by
        intro k hk
        rcases List.mem_append.mp hk with hk | hk
        · exact Nat.lt_of_lt_of_le (hK k hk) (by omega)
        · exact freshVars_lt k (by rwa [← hprefix]))
      (fun t ht => (hF t ht).mono (by omega))
    have hKfirst : ∀ k ∈ K, k < first := fun k hk => Nat.lt_of_lt_of_le (hK k hk) (by omega)
    have hWfirst : ∀ name ∈ written, name < first := fun name hn =>
      Nat.lt_of_lt_of_le (freshVars_lt name (by rwa [← hprefix])) hrLe
    have hFfirst := substSoft_below hrSubst (by omega) hF
    have hcSubst := hc.belowFvars hrTy hKfirst hWfirst hFfirst
    have hcTy := Subst.onTy_belowFvars hcSubst (hrTy.mono hcLe)
    have hcheckedCtx := Subst.onCtx_below hcSubst hcLe
      (Subst.onCtx_below hrSubst (by omega) hctx)
    have hpostrigid : ∀ v ∈ ((ann.substTyFvars s1).substTyFvars sCheck).rigidVars, v < checked := by
      intro v hv
      obtain ⟨k, hk, hv⟩ := BindingAnn.rigidVars_substTyFvars hv
      exact (Subst.onTy_belowFvars hcSubst (.fvar
        (Nat.lt_of_lt_of_le (rigid_soft_lt hKfirst hFfirst k (hc.rigid k hk)) hcLe))).mem_lt v hv
    obtain ⟨hbTy, hbSubst⟩ := hb.belowFvars (by
      intro M hM
      rcases List.mem_cons.mp hM with rfl | hM
      · rw [BindingAnn.substTyFvars_append]
        exact hc.scheme_belowFvars hcTy hpostrigid
      · exact hcheckedCtx M hM)
      (fun k hk => Nat.lt_of_lt_of_le (hK k hk) (by omega))
      (by simpa only [substSoft_append] using substSoft_below hcSubst hcLe hFfirst)
    refine ⟨hbTy, ?_⟩
    intro p hp
    rcases List.mem_append.mp hp with hp | hp
    · rcases List.mem_append.mp hp with hp | hp
      · exact (hrSubst p hp).mono (hcLe.trans hbLe)
      · exact (hcSubst p hp).mono hbLe
    · exact hbSubst p hp

  | .match_ _ hs _ hb =>
    intro hctx hK hF
    obtain ⟨ht, hS1⟩ := hs.belowFvars hctx hK hF
    have hle := hs.frontier_le
    obtain ⟨hresult, hS2⟩ := hb.belowFvars
      (Subst.onCtx_below (fun p hp => (hS1 p hp).mono (Nat.le_succ _)) (hle.trans (Nat.le_succ _)) hctx)
      (ht.mono (Nat.le_succ _)) (.fvar (Nat.lt_succ_self _))
      (fun k hk => Nat.lt_of_lt_of_le (hK k hk) (hle.trans (Nat.le_succ _)))
      (substSoft_below (fun p hp => (hS1 p hp).mono (Nat.le_succ _))
        (hle.trans (Nat.le_succ _)) hF)
    refine ⟨hresult, fun p hp => ?_⟩
    rcases List.mem_append.mp hp with hp | hp
    · exact (hS1 p hp).mono ((Nat.le_succ _).trans hb.frontier_le)
    · exact hS2 p hp
  | .letRec hscope _ hvalid hstrata hsigned _ _ hbody =>
    intro hctx hK hF
    expose_names
    have hvalid := hvalid.1
    have hanns : ∀ ann ∈ anns, ∀ v ∈ ann.rigidVars, v < frontier := by
      intro ann ha v hv
      exact rigid_soft_lt hK hF v (hscope.1 v (by
        simp only [InferInput.rigidVars, List.mem_append]
        exact Or.inl (Or.inl (List.mem_flatMap.mpr ⟨ann, ha, hv⟩))))
    have hlen : anns.length = bindings.length := by simpa only [List.length_map] using hvalid.length
    have hseed : frontier ≤ frontier + bindings.length := by omega
    obtain ⟨hs1, hstate1⟩ := hstrata.belowFvars_of_infer
      (fun he hi => hi.belowFvars)
      (fun M hm => (hctx M hm).mono hseed)
      (fun k hk => Nat.lt_of_lt_of_le (hK k hk) hseed)
      (fun t ht => (hF t ht).mono hseed)
      (by simpa only [hlen] using RecState.Below.init hanns)
      (fun ann ha v hv => Nat.lt_of_lt_of_le (hanns ann ha v hv) hseed)
    have hle1 := hstrata.frontier_le
    have hle2 := hsigned.frontier_le
    have hle3 := hbody.frontier_le
    have hbase1 : frontier ≤ first := by omega
    have hbase2 : frontier ≤ second := by omega
    obtain ⟨hs2, hstate2⟩ := hsigned.belowFvars_of_infer
      (fun he hi => hi.belowFvars)
      (Subst.onCtx_below hs1 hbase1 hctx)
      (fun k hk => Nat.lt_of_lt_of_le (hK k hk) hbase1)
      (substSoft_below hs1 hbase1 hF) hstate1 (anns_below_subst hanns hs1 hbase1)
    have hs12 : ∀ p ∈ s1 ++ s2, Ty.BelowFvars second p.2 :=
      fun p hp => (List.mem_append.mp hp).elim (fun hp => (hs1 p hp).mono hle2) (hs2 p)
    obtain ⟨hbodyTy, hs3⟩ := hbody.belowFvars
      (hstate2.rhsCtx (Subst.onCtx_below hs12 hbase2 hctx))
      (fun k hk => Nat.lt_of_lt_of_le (hK k hk) hbase2)
      (substSoft_below hs12 hbase2 hF)
    exact ⟨hbodyTy, fun p hp => (List.mem_append.mp hp).elim (fun hp => (hs12 p hp).mono hle3) (hs3 p)⟩
termination_by (input.size, 0)
decreasing_by all_goals (simp only [InferInput.size, InferInput.size_openTyVars, InferInput.size_substTyFvars, sizeBranches_substInputBranches, sizeBindings_map_substTyFvars] at *; omega)

theorem _root_.InferBranches.belowFvars {Φ ctx scrutTy ρ brs Φ' S}
    (h : InferBranches κ F Φ ctx scrutTy ρ brs Φ' S out)
    (hctx : CtxBelow Φ ctx) (hscrutTy : Ty.BelowFvars Φ scrutTy) (hρ : Ty.BelowFvars Φ ρ)
    (hK : ∀ k ∈ κ, k < Φ) (hF : ∀ t ∈ F, Ty.BelowFvars Φ t) :
    Ty.BelowFvars Φ' (S.onTy ρ) ∧ (∀ p ∈ S, Ty.BelowFvars Φ' p.2) := by
  match h with
  | .nil => exact ⟨by simpa using hρ, by simp⟩
  | @InferBranches.cons name count body rest κ F ctor scrutTy Φ S₀ ctx Φ₁ S₁ bodyOut bodyTy ρ S₂ Φ' S₃ restOut _ hlook hn huni0Rigid hbody huniRigid hrest =>
    have huni0 := huni0Rigid.unifies
    have huni := huniRigid.unifies
    have hS₀ : ∀ p ∈ S₀, Ty.BelowFvars (Φ + ctor.paramCount) p.2 :=
      UnifyRel.belowFvars huni0 (hscrutTy.mono (by omega))
        (.customTy (fun t ht => by
          obtain ⟨x, hx, rfl⟩ := List.mem_map.mp ht
          exact .fvar (by have := freshVars_lt x hx; omega)))
    obtain ⟨hτb, hS₁⟩ := Infer.belowFvars hbody
      (branchBindings_below (ctorr := ctor)
        (ta := ((freshVars Φ ctor.paramCount).map (Ty.fvar ·)).map S₀.onTy)
        (Subst.onCtx_below hS₀ (by omega) hctx)
        (fun t ht => by
          obtain ⟨v, hv, rfl⟩ := List.mem_map.mp ht
          obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hv
          exact Subst.onTy_belowFvars hS₀ (.fvar (by have := freshVars_lt x hx; omega))))
      (fun k hk => Nat.lt_of_lt_of_le (hK k hk) (by omega))
      (substSoft_below hS₀ (by omega) hF)
    have hle0 : Φ + ctor.paramCount ≤ Φ₁ := Infer.frontier_le hbody
    have hS₀ρ : Ty.BelowFvars Φ₁ (S₀.onTy ρ) :=
      (Subst.onTy_belowFvars hS₀ (hρ.mono (by omega))).mono hle0
    have hS₀scrut : Ty.BelowFvars Φ₁ (S₀.onTy scrutTy) :=
      (Subst.onTy_belowFvars hS₀ (hscrutTy.mono (by omega))).mono hle0
    have hS₁ρ := Subst.onTy_belowFvars hS₁ hS₀ρ
    have hS₂ := UnifyRel.belowFvars huni hτb hS₁ρ
    have hctx1 : CtxBelow Φ₁ (S₂.onCtx (S₁.onCtx (S₀.onCtx ctx))) :=
      Subst.onCtx_below hS₂ (le_refl _)
        (Subst.onCtx_below hS₁ (le_refl _)
          (Subst.onCtx_below (fun p hp => (hS₀ p hp).mono hle0) (by omega) hctx))
    obtain ⟨hres, hS₃⟩ := InferBranches.belowFvars hrest hctx1
      (Subst.onTy_belowFvars hS₂ (Subst.onTy_belowFvars hS₁ hS₀scrut))
      (Subst.onTy_belowFvars hS₂ (Subst.onTy_belowFvars hS₁ hS₀ρ))
      (fun k hk => Nat.lt_of_lt_of_le (hK k hk) (by omega))
      (by simpa only [substSoft_append] using
        substSoft_below hS₂ (le_refl _) (substSoft_below hS₁ (le_refl _)
          (substSoft_below (fun p hp => (hS₀ p hp).mono hle0) (by omega) hF)))
    have hbrle := InferBranches.frontier_le hrest
    refine ⟨?_, ?_⟩
    · rw [Subst.onTy_append, Subst.onTy_append, Subst.onTy_append]; exact hres
    · intro p hp; rw [List.mem_append, List.mem_append, List.mem_append] at hp
      rcases hp with ((hp | hp) | hp) | hp
      · exact (hS₀ p hp).mono (by omega)
      · exact (hS₁ p hp).mono (by omega)
      · exact (hS₂ p hp).mono (by omega)
      · exact hS₃ p hp
  | .consWild _ hbody huniRigid hrest =>
    have huni := huniRigid.unifies
    obtain ⟨hτb, hS₁⟩ := Infer.belowFvars hbody hctx
      hK hF
    have hle1 := Infer.frontier_le hbody
    have hS₁ρ := Subst.onTy_belowFvars hS₁ (hρ.mono hle1)
    have hS₂ := UnifyRel.belowFvars huni hτb hS₁ρ
    have hctx1 := Subst.onCtx_below hS₂ (le_refl _) (Subst.onCtx_below hS₁ hle1 hctx)
    obtain ⟨hres, hS₃⟩ := InferBranches.belowFvars hrest hctx1
      (Subst.onTy_belowFvars hS₂ (Subst.onTy_belowFvars hS₁ (hscrutTy.mono hle1)))
      (Subst.onTy_belowFvars hS₂ (Subst.onTy_belowFvars hS₁ (hρ.mono hle1)))
      (fun k hk => Nat.lt_of_lt_of_le (hK k hk) hle1)
      (by simpa only [substSoft_append] using
        substSoft_below hS₂ (le_refl _) (substSoft_below hS₁ hle1 hF))
    have hbrle := InferBranches.frontier_le hrest
    refine ⟨?_, ?_⟩
    · rw [Subst.onTy_append, Subst.onTy_append]; exact hres
    · intro p hp; rw [List.mem_append, List.mem_append] at hp
      rcases hp with (hp | hp) | hp
      · exact (hS₁ p hp).mono (by omega)
      · exact (hS₂ p hp).mono (by omega)
      · exact hS₃ p hp
termination_by (sizeBranches brs, 0)
decreasing_by
  all_goals (try subst_vars; try simp only [sizeBranches, InferInput.size_substTyFvars, sizeBranches_substInputBranches]; omega)
end


private theorem generalizes_lookup {new old : Env}
    (h : List.Forall₂ PolyTy.Generalizes new old) {index : Nat} {scheme : PolyTy}
    (hlook : old[index]? = some scheme) :
    ∃ scheme', new[index]? = some scheme' ∧ scheme'.Generalizes scheme := by
  induction h generalizing index with
  | nil => simp at hlook
  | @cons headNew headOld tailNew tailOld hhead htail ih =>
    cases index with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hlook
      subst scheme
      exact ⟨headNew, rfl, hhead⟩
    | succ index => exact ih hlook

/-- Replacing each environment entry by a more general scheme preserves
independent anonymous input typing, with its protected variables unchanged. -/
theorem InputTyping.weaken {K : List Nat} {ctx : Ctx} {input : InferInput} {ty : Ty}
    (h : InputTyping K ctx input ty) :
    ∀ {env' : Env}, List.Forall₂ PolyTy.Generalizes env' ctx.env →
      InputTyping K { ctx with env := env' } input ty := by
  induction h using InputTyping.rec
      (motive_2 := fun K ctx branch scrutTy resultTy _ =>
        ∀ {env' : Env}, List.Forall₂ PolyTy.Generalizes env' ctx.env →
          BranchTyping InputTyping K { ctx with env := env' } branch scrutTy resultTy) with
  | complete hemb hprotected hcore =>
    intro env' hgen
    refine .complete hemb hprotected ?_
    simpa only [List.append_nil] using
      TypeOfHM.weaken_schemes (env := []) hgen (by simpa only [List.append_nil] using hcore)
  | primLit hcore =>
    intro env' hgen
    apply InputTyping.primLit
    simpa only [List.append_nil] using
      TypeOfHM.weaken_schemes (env := []) hgen (by simpa only [List.append_nil] using hcore)
  | primBinOp hcore =>
    intro env' hgen
    apply InputTyping.primBinOp
    simpa only [List.append_nil] using
      TypeOfHM.weaken_schemes (env := []) hgen (by simpa only [List.append_nil] using hcore)
  | lambda hlc hfit hprotected _ ih =>
    intro env' hgen
    refine .lambda hlc hfit hprotected ?_
    exact ih (.cons (PolyTy.Generalizes.refl _) hgen)
  | app _ _ ihf iha =>
    intro env' hgen
    exact .app (ihf hgen) (iha hgen)
  | letIn hwf hprotected hfit _ _ ihr ihb =>
    intro env' hgen
    refine .letIn hwf hprotected hfit (fun Xs hf => ihr Xs hf hgen) ?_
    exact ihb (.cons (PolyTy.Generalizes.refl _) hgen)
  | letSignature hwf hann hrhs hfit _ _ ihr ihb =>
    intro env' hgen
    refine .letSignature hwf hann hrhs hfit (fun Xs hf => ihr Xs hf hgen) ?_
    exact ihb (.cons (PolyTy.Generalizes.refl _) hgen)
  | var hlook hargs hinst =>
    intro env' hgen
    obtain ⟨scheme', hlook', hscheme⟩ := generalizes_lookup hgen hlook
    obtain ⟨args', hargs', hinst'⟩ := hscheme _ _ hargs hinst
    exact .var hlook' hargs' hinst'
  | ctor hlook hargs hinst =>
    intro env' _
    exact .ctor hlook hargs hinst

  | match_ _ hne _ ihscrut ihbranches =>
    intro env' hgen
    exact .match_ (ihscrut hgen) hne (fun branch hb => ihbranches branch hb hgen)
  | @letRec anns K bindings ctx body resultTy specs groups prefixes G L hg hw hp hG hAnn hRhs hFits _ _ _ ihMono ihPoly ihBody =>
    intro env' hgen
    have hextra : ∀ extra : Env, List.Forall₂ PolyTy.Generalizes (extra ++ env') (extra ++ ctx.env) := by
      intro extra
      induction extra with
      | nil => exact hgen
      | cons head tail ih => exact .cons (PolyTy.Generalizes.refl head) ih
    let avoid := K ++ env'.freeVars ++ G ++ specs.flatMap RecSpec.freeVars
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
    let prefixes' := prefixes.map (recRenameNames G W)
    let L' := G ++ W ++ L
    have annNil : anns.map (BindingAnn.substTyFvars []) = anns := by
      conv_rhs => rw [← List.map_id anns]
      apply List.map_congr_left
      intro ann _
      exact ann.substTyFvars_eq_self_of_fixes (fun _ _ => rfl)
    have hw' : RecSpecs.WF (anns.map BindingAnn.recModeAnn) (bindings.map InferInput.erase) specs' W := by
      simpa only [annNil] using RecSpecs.WF.subst_fresh_pool (S := []) hw (by simp) hWnd
    have hp' : RecPrefixesWF anns specs' prefixes' W := by
      simpa only [annNil] using hp.subst_fresh_pool (S := []) hWlen hWnd
    have hannsLen : anns.length = specs.length := by
      have hh := congrArg List.length hw.anns_eq
      simpa using hh.symm
    have hpData := fun i hi => hp.get hannsLen (i := i) hi
    have mapNil : ∀ xs : List PolyTy, xs.map (Subst.onPolyTy []) = xs := by
      intro xs
      rw [show Subst.onPolyTy [] = id from funext Subst.onPolyTy_nil, List.map_id]
    have hcompleted : recCompletedSchemes specs' prefixes' W = recCompletedSchemes specs prefixes G := by
      simpa only [mapNil] using recCompletedSchemes_subst_fresh_pool (S := []) (by simp) hWlen hw.nodup hWnd
        hGW hWmono (by simp) (by simp) hw.mono_lc hpData
    have oldFresh : ∀ Xs, FreshNames (W ++ L') W.length Xs → FreshNames (G ++ L) G.length Xs := by
      intro Xs hf
      refine ⟨hf.length.trans hWlen, hf.nodup, ?_⟩
      intro x hx hl
      exact hf.avoid x hx (by simp only [L', List.mem_append] at hl ⊢; tauto)
    have hGXs : ∀ Xs, FreshNames (W ++ L') W.length Xs → ∀ g ∈ G, g ∉ Xs := by
      intro Xs hf g hg hx
      exact hf.avoid g hx (by simp only [L', List.mem_append]; tauto)
    have hWXs : ∀ Xs, FreshNames (W ++ L') W.length Xs → ∀ w ∈ W, w ∉ Xs := by
      intro Xs hf w hw hx
      exact hf.avoid w hx (List.mem_append_left _ hw)
    have hstage : ∀ Xs, FreshNames (W ++ L') W.length Xs → ∀ done,
        specs'.mapIdx (recStageEntry prefixes' done W Xs) = specs.mapIdx (recStageEntry prefixes done G Xs) := by
      intro Xs hf done
      simpa only [mapNil] using recStageSchemes_subst_fresh_pool (S := []) (done := done) (by simp)
        hWlen hw.nodup hWnd hGW hWmono (by simp) (by simp) hw.mono_lc hpData
        (hf.length.trans hWlen) (hGXs Xs hf) (hWXs Xs hf) (by simp)
    have hsquare : ∀ ty, .mono ty ∈ specs → ∀ Xs, FreshNames (W ++ L') W.length Xs →
        Ty.renameG W Xs (Ty.renameG G W ty) = Ty.renameG G Xs ty := by
      intro ty ht Xs hf
      simpa only [Subst.onTy_nil] using Ty.renameG_subst_fresh_pool (S := []) (hw.mono_lc ty ht) (by simp)
        hWlen hw.nodup hWnd hGW (hWmono ty ht) (by simp) (by simp)
        (hf.length.trans hWlen) (hGXs Xs hf) (hWXs Xs hf) (by simp)
    refine InputTyping.letRec (specs := specs') (groups := groups) (prefixes := prefixes') (G := W) (L := L')
      hg hw' hp' ?_ hAnn hRhs ?_ ?_ ?_ ?_
    · intro w hw hm
      exact hWavoid w hw (by simp only [avoid, List.mem_append] at hm ⊢; tauto)
    · intro stage component hs Xs hf member hm rhs ann names ty hri hai hni hti
      rw [List.getElem?_map] at hni hti
      obtain ⟨names0, hn0, rfl⟩ := Option.map_eq_some_iff.mp hni
      obtain ⟨spec, ht0, heq⟩ := Option.map_eq_some_iff.mp hti
      cases spec with
      | poly scheme => cases heq
      | mono ty0 =>
        cases heq
        obtain ⟨_, _, hsub⟩ := hp.member member ann names0 hai hn0
        change ann.RecFits (recRenameNames W Xs (recRenameNames G W names0))
          (Ty.renameG W Xs (Ty.renameG G W ty0))
        rw [recRenameNames_composition hWlen (hf.length.trans hWlen) hWnd hsub,
          hsquare ty0 (List.mem_of_getElem? ht0) Xs hf]
        exact hFits stage component hs Xs (oldFresh Xs hf) member hm rhs ann names0 ty0 hri hai hn0 ht0
    · intro stage component hs Xs hf member hm rhs ann names ty hri hai hni hti
      rw [List.getElem?_map] at hni hti
      obtain ⟨names0, hn0, rfl⟩ := Option.map_eq_some_iff.mp hni
      obtain ⟨spec, ht0, heq⟩ := Option.map_eq_some_iff.mp hti
      cases spec with
      | poly scheme => cases heq
      | mono ty0 =>
        cases heq
        obtain ⟨_, _, hsub⟩ := hp.member member ann names0 hai hn0
        change InputTyping (K ++ Xs)
          (recStageCtx { ctx with env := env' } specs' prefixes' (groups.take stage).flatten W Xs)
          (rhs.openTyVars (recRenameNames W Xs (recRenameNames G W names0)))
          (Ty.renameG W Xs (Ty.renameG G W ty0))
        rw [recRenameNames_composition hWlen (hf.length.trans hWlen) hWnd hsub,
          hsquare ty0 (List.mem_of_getElem? ht0) Xs hf]
        have hc := ihMono stage component hs Xs (oldFresh Xs hf) member hm rhs ann names0 ty0 hri hai hn0 ht0
          (hextra (specs.mapIdx (recStageEntry prefixes (groups.take stage).flatten G Xs)))
        simpa only [recStageCtx, hstage Xs hf] using hc
    · intro member rhs scheme hri hsi Ys hy
      rw [List.getElem?_map] at hsi
      obtain ⟨spec, hs0, heq⟩ := Option.map_eq_some_iff.mp hsi
      cases spec with
      | mono ty => cases heq
      | poly scheme0 =>
        cases heq
        have hy0 : FreshNames L scheme0.paramCount Ys :=
          ⟨hy.length, hy.nodup, fun y hy' hl => hy.avoid y hy' (by simp only [L', List.mem_append]; tauto)⟩
        have hc := ihPoly member rhs scheme0 hri hs0 Ys hy0 (hextra (recCompletedSchemes specs prefixes G))
        simpa only [recBodyCtx, hcompleted] using hc
    · have hc := ihBody (hextra (recCompletedSchemes specs prefixes G))
      simpa only [recBodyCtx, hcompleted] using hc
  | @named name count scrutTy ctor args fields K ctx body resultTy hspec _ ih =>
    rename_i env' hgen
    refine .named hspec (ih ?_)
    have hextra : ∀ extra : Env,
        List.Forall₂ PolyTy.Generalizes (extra ++ env') (extra ++ ctx.env) := by
      intro extra
      induction extra with
      | nil => exact hgen
      | cons head tail ih => exact .cons (PolyTy.Generalizes.refl head) ih
    exact hextra (fields.map PolyTy.mkTrivial)
  | wildcard _ ih =>
    rename_i env' hgen
    exact .wildcard (ih hgen)

/-- Segment form matching the existing `TypeOfHM.weaken_schemes` contract. -/
theorem InputTyping.weaken_schemes {K : List Nat} {ctors : CtorEnv} {env : Env}
    {Ms Ms' : List PolyTy} {input : InferInput} {ty : Ty}
    (hgen : List.Forall₂ PolyTy.Generalizes Ms' Ms)
    (h : InputTyping K ⟨Ms ++ env, ctors⟩ input ty) :
    InputTyping K ⟨Ms' ++ env, ctors⟩ input ty := by
  apply h.weaken
  clear h
  have hrefl : List.Forall₂ PolyTy.Generalizes env env := by
    induction env with
    | nil => exact .nil
    | cons head tail ih => exact .cons (PolyTy.Generalizes.refl head) ih
  induction hgen with
  | nil => exact hrefl
  | cons hh _ ih => exact .cons hh ih

mutual
/-- Allocating flexible holes preserves local closure of any matching target. -/
theorem TyTemplate.Fits.allocate_lc {template : TyTemplate} {target : Ty}
    (h : template.Fits target) (hlc : target.IsLC) (frontier : Nat) :
    (template.allocate frontier).2.IsLC := by
  cases h with
  | fixed => exact hlc
  | hole => exact .fvar
  | arrow ha hb =>
    cases hlc with
    | arrow hla hlb =>
      exact .arrow (ha.allocate_lc hla frontier) (hb.allocate_lc hlb _)
  | custom hall =>
    cases hlc with
    | customTy hl => exact .customTy (allocateList_lc hall hl frontier)
theorem allocateList_lc {templates : List TyTemplate} {targets : List Ty}
    (h : List.Forall₂ TyTemplate.Fits templates targets)
    (hlc : ∀ t ∈ targets, t.IsLC) (frontier : Nat) :
    ∀ t ∈ (allocateList frontier templates).2, t.IsLC := by
  cases h with
  | nil => simp [allocateList]
  | @cons template target templates targets hh ht =>
    intro t hmem
    rcases List.mem_cons.mp hmem with rfl | hmem
    · exact hh.allocate_lc (hlc target List.mem_cons_self) frontier
    · exact allocateList_lc ht (fun t ht => hlc t (List.mem_cons_of_mem _ ht)) _ t hmem
end


mutual
/-- A locally closed filling of the transformed source reflects local closure
of the original allocation. No rigidity or closure of the substitution needed. -/
theorem TyTemplate.Fits.allocate_lc_source {template : TyTemplate} {target : Ty} {S : Subst}
    (h : (template.substTyFvars S).Fits target) (hlc : target.IsLC) (frontier : Nat) :
    (template.allocate frontier).2.IsLC := by
  cases template with
  | fixed ty => cases h; exact ContainsBvarsUpTo.of_substFvars hlc
  | hole => exact .fvar
  | arrow a b =>
    cases h with
    | arrow ha hb =>
      cases hlc with
      | arrow hla hlb => exact .arrow (ha.allocate_lc_source hla frontier) (hb.allocate_lc_source hlb _)
  | custom name args =>
    cases h with
    | custom hall =>
      cases hlc with
      | customTy hl => exact .customTy (allocateList_lc_source hall hl frontier)
private theorem allocateList_lc_source {templates : List TyTemplate} {targets : List Ty} {S : Subst}
    (h : List.Forall₂ TyTemplate.Fits (substTemplateList S templates) targets)
    (hlc : ∀ t ∈ targets, t.IsLC) (frontier : Nat) :
    ∀ t ∈ (allocateList frontier templates).2, t.IsLC := by
  cases templates with
  | nil => intro t ht; cases ht
  | cons template templates =>
    cases h with
    | cons hh ht =>
      intro t hmem
      rcases List.mem_cons.mp hmem with rfl | hmem
      · exact hh.allocate_lc_source (hlc _ List.mem_cons_self) frontier
      · exact allocateList_lc_source ht (fun t ht => hlc t (List.mem_cons_of_mem _ ht)) _ t hmem
end


private theorem UnifyRel.sourceAvoid_local {t u : Ty} {S : Subst} {w : Nat}
    (h : UnifyRel t u S) (ht : w ∉ t.freeVars) (hu : w ∉ u.freeVars) :
    (∀ p ∈ S, w ∉ p.2.freeVars) ∧ w ∉ S.map Prod.fst := by
  constructor
  · intro p hp hw
    exact (h.range_mem p hp w hw).elim ht hu
  · intro hw
    obtain ⟨p, hp, heq⟩ := List.mem_map.mp hw
    have hm := h.dom_mem p hp
    rw [heq] at hm
    exact hm.elim ht hu

private theorem Subst.sourceAvoid_append_local {S T : Subst} {w : Nat}
    (hS : (∀ p ∈ S, w ∉ p.2.freeVars) ∧ w ∉ S.map Prod.fst)
    (hT : (∀ p ∈ T, w ∉ p.2.freeVars) ∧ w ∉ T.map Prod.fst) :
    (∀ p ∈ S ++ T, w ∉ p.2.freeVars) ∧ w ∉ (S ++ T).map Prod.fst := by
  exact ⟨fun p hp => (List.mem_append.mp hp).elim (hS.1 p) (hT.1 p),
    by simpa only [List.map_append, List.mem_append, not_or] using And.intro hS.2 hT.2⟩

mutual
 theorem TyTemplate.allocate_avoid {template : TyTemplate} {frontier w : Nat}
    (hw : w < frontier) (h : w ∉ template.rigidVars) :
    w ∉ (template.allocate frontier).2.freeVars := by
  cases template with
  | fixed ty => exact h
  | hole => simp only [TyTemplate.allocate, Ty.freeVars, List.mem_singleton]; omega
  | arrow a b =>
    simp only [TyTemplate.rigidVars, List.mem_append, not_or] at h
    have ha := a.allocate_avoid hw h.1
    have hb := b.allocate_avoid (Nat.lt_of_lt_of_le hw (a.allocate_bounds frontier).1) h.2
    simpa only [TyTemplate.allocate, Ty.freeVars, List.mem_dedup, List.mem_append, not_or] using And.intro ha hb
  | custom name args =>
    exact allocateList_avoid hw h
 theorem allocateList_avoid {templates : List TyTemplate} {frontier w : Nat}
    (hw : w < frontier) (h : w ∉ rigidVarsList templates) :
    w ∉ TyList.freeVars (allocateList frontier templates).2 := by
  cases templates with
  | nil => simp [allocateList, TyList.freeVars]
  | cons a rest =>
    simp only [rigidVarsList, List.mem_append, not_or] at h
    have ha := a.allocate_avoid hw h.1
    have hb := allocateList_avoid (Nat.lt_of_lt_of_le hw (a.allocate_bounds frontier).1) h.2
    simpa only [allocateList, TyList.freeVars, List.mem_dedup, List.mem_append, not_or] using And.intro ha hb
end

 theorem Seed.sourceAvoid (h : Seed K frontier ann param initial) (hw : w < frontier)
    (hann : ∀ t, ann = some t → w ∉ t.rigidVars) : w ∉ param.freeVars := by
  cases h with
  | absent => simp only [Ty.freeVars, List.mem_singleton]; omega
  | annotated heq _ _ => simpa only [heq] using TyTemplate.allocate_avoid hw (hann _ rfl)

 theorem LetCheck.sourceAvoid (h : LetCheck K F frontier ty ann next subst)
    (hw : w < frontier) (hty : w ∉ ty.freeVars) (hann : w ∉ ann.rigidVars) :
    (∀ p ∈ subst, w ∉ p.2.freeVars) ∧ w ∉ subst.map Prod.fst := by
  cases h with
  | absent => simp
  | hole => simp
  | template heq _ _ hu =>
    exact UnifyRel.sourceAvoid_local hu.unifies hty (by simpa only [heq] using TyTemplate.allocate_avoid hw hann)

 theorem SignatureCheck.sourceAvoid (h : SignatureCheck K F written frontier ty ann next subst)
    (hw : w < frontier) (hty : w ∉ ty.freeVars) (hann : w ∉ ann.rigidVars)
    (hwr : w ∉ written) :
    (∀ p ∈ subst, w ∉ p.2.freeVars) ∧ w ∉ subst.map Prod.fst := by
  cases h with
  | complete _ _ hu =>
    refine UnifyRel.sourceAvoid_local hu.unifies hty ?_
    intro hc
    exact (Ty.freeVars_openVars_subset w hc).elim hann hwr
  | partialSignature heq _ _ hu =>
    refine UnifyRel.sourceAvoid_local hu.unifies hty ?_
    simpa only [heq] using TyTemplate.allocate_avoid hw
      (fun hc => (List.mem_append.mp (TyTemplate.openTyVarsFrom_scope _ (K := _) (fun _ h => h) 0 written w hc)).elim hann hwr)

theorem InferInput.avoid_subst {input : InferInput} {S : Subst} {w : Nat}
    (hS : ∀ p ∈ S, w ∉ p.2.freeVars) (h : w ∉ input.rigidVars) :
    w ∉ (input.substTyFvars S).rigidVars := by
  intro hw
  obtain ⟨v, hv, him⟩ := InferInput.rigidVars_substTyFvars hw
  exact Subst.notMemOnTy hS (by simpa only [Ty.freeVars, List.mem_singleton] using (show w ≠ v from fun heq => h (heq.symm ▸ hv))) him

private theorem BindingAnn.avoid_subst {ann : BindingAnn} {S : Subst} {w : Nat}
    (hS : ∀ p ∈ S, w ∉ p.2.freeVars) (h : w ∉ ann.rigidVars) :
    w ∉ (ann.substTyFvars S).rigidVars := by
  intro hw
  obtain ⟨v, hv, him⟩ := BindingAnn.rigidVars_substTyFvars hw
  exact Subst.notMemOnTy hS (by simpa only [Ty.freeVars, List.mem_singleton] using (show w ≠ v from fun heq => h (heq.symm ▸ hv))) him

private theorem branches_avoid_subst {brs : List (MatchPattern × InferInput)} {S : Subst} {w : Nat}
    (hS : ∀ p ∈ S, w ∉ p.2.freeVars) (h : w ∉ rigidBranchVars brs) :
    w ∉ rigidBranchVars (substInputBranches S brs) := by
  induction brs with
  | nil => simp [substInputBranches, rigidBranchVars]
  | cons pair rest ih =>
    simp only [rigidBranchVars, List.mem_append, not_or] at h
    exact fun hm => (List.mem_append.mp hm).elim (InferInput.avoid_subst hS h.1) (ih h.2)

private theorem mem_eraseBranches {brs : List (MatchPattern × InferInput)} {p : MatchPattern} {b : InferInput}
    (h : (p,b) ∈ brs) : (p,b.erase) ∈ eraseBranches brs := by
  induction brs with
  | nil => cases h
  | cons pair rest ih =>
    rcases List.mem_cons.mp h with heq | hm
    · cases heq; exact List.mem_cons_self ..
    · exact List.mem_cons_of_mem _ (ih hm)

private theorem branches_refs_subst {brs : List (MatchPattern × InferInput)} {ctx : Ctx} {S : Subst} {w : Nat}
    (hrefs : ∀ p b, (p,b) ∈ brs → b.erase.ForallOuter
      (fun i => ∀ M, ctx.env[i]? = some M → w ∉ M.body.freeVars) p.bindCount)
    (hS : ∀ p ∈ S, w ∉ p.2.freeVars) :
    ∀ p b, (p,b) ∈ substInputBranches S brs → b.erase.ForallOuter
      (fun i => ∀ M, (S.onCtx ctx).env[i]? = some M → w ∉ M.body.freeVars) p.bindCount := by
  intro p b hm
  rw [substInputBranches_eq_map] at hm
  obtain ⟨⟨oldpat,oldbody⟩, hold, heq⟩ := List.mem_map.mp hm
  cases heq
  simpa only [InferInput.erase_substTyFvars] using Expr.ForallOuter.lookupAvoid_onSubst
    (hrefs oldpat oldbody hold) hS

 theorem _root_.InferRecComponent.sourceLocality_of_infer
    (h : InferRecComponent K F members index frontier ctx bindings specs next S outputs facts)
    (hInfer : ∀ {κ F' Ψ c e Ψ' T output ty}, e.size ≤ sizeBindings bindings →
      Infer κ F' Ψ c e Ψ' T output ty →
      ∀ {w}, w < Ψ →
      e.erase.ForallOuter (fun i => ∀ M, c.env[i]? = some M → w ∉ M.body.freeVars) 0 →
      w ∉ e.rigidVars →
      (∀ p ∈ T, w ∉ p.2.freeVars) ∧ w ∉ ty.freeVars ∧ w ∉ T.map Prod.fst) :
    ∀ {w}, w < frontier →
    (∀ j rhs, index + j ∈ members → bindings[j]? = some rhs →
      rhs.erase.ForallOuter
        (fun i => ∀ M, ctx.env[i]? = some M → w ∉ M.body.freeVars) 0 ∧ w ∉ rhs.rigidVars) →
    (∀ j ty, index + j ∈ members → specs[j]? = some (.mono ty) → w ∉ ty.freeVars) →
    (∀ p ∈ S, w ∉ p.2.freeVars) ∧ w ∉ S.map Prod.fst := by
  match h with
  | .nil => intro w _ _ _; exact ⟨by simp, by simp⟩
  | .consSelected hsel hi hu hrest =>
    intro w hw hrefs htargets
    expose_names
    have hrhs := hrefs 0 rhs (by simpa using hsel) rfl
    obtain ⟨hiS, hiTy, hiD⟩ := hInfer (by simp only [sizeBindings]; omega) hi hw hrhs.1 hrhs.2
    have ht : w ∉ expected.freeVars := htargets 0 expected (by simpa using hsel) rfl
    have huS : ∀ p ∈ s2, w ∉ p.2.freeVars := by
      intro p hp hwp
      exact (hu.unifies.range_mem p hp w hwp).elim hiTy (Subst.notMemOnTy hiS ht)
    have huD : w ∉ s2.map Prod.fst := by
      intro hm
      obtain ⟨p, hp, hpw⟩ := List.mem_map.mp hm
      have hmem := hu.unifies.dom_mem p hp
      rw [hpw] at hmem
      exact hmem.elim hiTy (Subst.notMemOnTy hiS ht)
    have hS12 : ∀ p ∈ s1 ++ s2, w ∉ p.2.freeVars :=
      fun p hp => (List.mem_append.mp hp).elim (hiS p) (huS p)
    have hrestRefs : ∀ j rhs', index + 1 + j ∈ members →
        (rest.map (InferInput.substTyFvars (s1 ++ s2)))[j]? = some rhs' →
        rhs'.erase.ForallOuter
          (fun i => ∀ M, (s2.onCtx (s1.onCtx ctx)).env[i]? = some M → w ∉ M.body.freeVars) 0 ∧
          w ∉ rhs'.rigidVars := by
      intro j rhs' hj hget
      rw [List.getElem?_map] at hget
      obtain ⟨old, hold, rfl⟩ := Option.map_eq_some_iff.mp hget
      have horig := hrefs (j + 1) old
        (by simpa only [Nat.add_assoc, Nat.add_comm 1 j] using hj)
        (by simpa only [List.getElem?_cons_succ] using hold)
      refine ⟨?_, InferInput.avoid_subst hS12 horig.2⟩
      simpa only [InferInput.erase_substTyFvars, Subst.onCtx_append] using
        Expr.ForallOuter.lookupAvoid_onSubst (S := s1 ++ s2) horig.1 hS12
    have hrestTargets : ∀ j ty, index + 1 + j ∈ members →
        (specs_1.map (RecSpec.onSubstSource (s1 ++ s2)))[j]? = some (.mono ty) →
        w ∉ ty.freeVars := by
      intro j ty hj hget
      rw [List.getElem?_map] at hget
      obtain ⟨old, hold, heq⟩ := Option.map_eq_some_iff.mp hget
      cases old with
      | poly σ => cases heq
      | mono τ =>
          cases RecSpec.mono.inj heq
          exact Subst.notMemOnTy hS12 (htargets (j + 1) τ
            (by simpa only [Nat.add_assoc, Nat.add_comm 1 j] using hj)
            (by simpa only [List.getElem?_cons_succ] using hold))
    obtain ⟨hrS, hrD⟩ := hrest.sourceLocality_of_infer
      (fun he h => hInfer (by
        simp only [sizeBindings_map_substTyFvars] at he
        simp only [sizeBindings]; omega) h)
      (Nat.lt_of_lt_of_le hw hi.frontier_le) hrestRefs hrestTargets
    refine ⟨?_, ?_⟩
    · intro p hp
      rw [List.mem_append, List.mem_append] at hp
      rcases hp with (hp | hp) | hp
      · exact hiS p hp
      · exact huS p hp
      · exact hrS p hp
    · simpa only [List.map_append, List.mem_append, not_or] using
        And.intro (And.intro hiD huD) hrD
  | .skipMono _ hrest | .skipPoly hrest =>
    intro w hw hrefs htargets
    apply hrest.sourceLocality_of_infer
      (fun he h => hInfer (by simp only [sizeBindings]; omega) h) hw
    · intro j rhs hj hget
      exact hrefs (j + 1) rhs
        (by simpa only [Nat.add_assoc, Nat.add_comm 1 j] using hj)
        (by simpa only [List.getElem?_cons_succ] using hget)
    · intro j ty hj hget
      exact htargets (j + 1) ty
        (by simpa only [Nat.add_assoc, Nat.add_comm 1 j] using hj)
        (by simpa only [List.getElem?_cons_succ] using hget)
 termination_by structural h

/-- Only live type specs and exports affect the recursive term environment. -/
def RecState.Avoids (w : Nat) (state : RecState) : Prop :=
  (∀ spec ∈ state.specs, w ∉ spec.freeVars) ∧
  ∀ scheme ∈ state.exports.filterMap id, w ∉ scheme.body.freeVars

theorem RecState.Avoids.exported {state : RecState} (h : state.Avoids w)
    (hs : some scheme ∈ state.exports) : w ∉ scheme.body.freeVars :=
  h.2 scheme (List.mem_filterMap.mpr ⟨some scheme, hs, rfl⟩)

theorem RecState.Avoids.init {anns : List BindingAnn} (hw : w < base)
    (hanns : ∀ ann ∈ anns, w ∉ ann.rigidVars) : (RecState.init base anns).Avoids w := by
  have hmode : ∀ scheme, some scheme ∈ anns.map BindingAnn.recModeAnn → w ∉ scheme.body.freeVars := by
    intro scheme hs
    obtain ⟨ann, ha, heq⟩ := List.mem_map.mp hs
    cases ann with
    | absent | template | partialForall => cases heq
    | complete original =>
      cases heq
      exact hanns _ ha
  constructor
  · intro spec hs
    rcases RecSpec.mem_init hs with ⟨m, hlo, _, rfl⟩ | ⟨scheme, hsigma, rfl⟩
    · simp only [RecSpec.freeVars, Ty.freeVars, List.mem_singleton]
      omega
    · exact hmode scheme hsigma
  · intro scheme hs
    obtain ⟨old, ho, heq⟩ := List.mem_filterMap.mp hs
    exact hmode scheme (heq ▸ ho)

theorem RecState.Avoids.onSubst {state : RecState} (h : state.Avoids w)
    (hS : ∀ p ∈ S, w ∉ p.2.freeVars) : (state.onSubst S).Avoids w := by
  constructor
  · intro spec hs
    obtain ⟨old, ho, rfl⟩ := List.mem_map.mp hs
    cases old with
    | mono ty => exact Subst.notMemOnTy hS (h.1 _ ho)
    | poly scheme => exact Subst.notMemOnTy hS (h.1 _ ho)
  · intro scheme hs
    obtain ⟨old, ho, heq⟩ := List.mem_filterMap.mp hs
    obtain ⟨original, horiginal, rfl⟩ := List.mem_map.mp ho
    obtain ⟨sigma, hsigma, heq'⟩ := Option.map_eq_some_iff.mp heq
    subst scheme
    exact Subst.notMemOnTy hS (h.exported (hsigma ▸ horiginal))

theorem RecState.Avoids.installOpenings {state : RecState} (h : state.Avoids w) :
    (state.installOpenings members openings).Avoids w := h

theorem RecState.Avoids.setSigned {state : RecState} {member : Nat} {names : List Nat}
    {output : Expr} {facts : RecFacts} (h : state.Avoids w) :
    (state.setSigned member names output facts).Avoids w := h

theorem RecState.Avoids.entries {state : RecState} (h : state.Avoids w) :
    ∀ scheme ∈ state.entries, w ∉ scheme.body.freeVars := by
  intro scheme hs
  obtain ⟨⟨spec, exported⟩, hp, heq⟩ := List.mem_map.mp hs
  have hmem := List.of_mem_zip hp
  cases exported with
  | none =>
    subst scheme
    cases spec with
    | mono ty => exact h.1 _ hmem.1
    | poly sigma => exact h.1 _ hmem.1
  | some sigma =>
    cases heq
    exact h.exported hmem.2

theorem RecState.Avoids.rhsCtx {state : RecState} {e : Expr} {groupSize : Nat} {ctx : Ctx} (h : state.Avoids w)
    (hlen : state.entries.length = groupSize)
    (href : e.ForallOuter (fun i => ∀ M, ctx.env[i]? = some M → w ∉ M.body.freeVars) groupSize) :
    e.ForallOuter (fun i => ∀ M, (state.rhsCtx ctx).env[i]? = some M → w ∉ M.body.freeVars) 0 := by
  exact Expr.ForallOuter.lookupAvoid_prepend (pre := state.entries)
    (by simpa only [Nat.zero_add, hlen] using href) h.entries

theorem RecState.Avoids.exportComponent {state : RecState} {members pool : List Nat}
    {written : List (List Nat)} {outputs : List (Option Expr)} {facts : List RecFacts} (h : state.Avoids w) :
    (state.exportComponent members written pool outputs facts).Avoids w := by
  refine ⟨h.1, ?_⟩
  intro scheme hs
  obtain ⟨old, ho, heq⟩ := List.mem_filterMap.mp hs
  obtain ⟨i, hi, heq'⟩ := List.mem_mapIdx.mp ho
  subst old
  split at heq
  · cases hlookup : state.specs[i]? with
    | none => simp [hlookup] at heq
    | some spec =>
      simp only [hlookup, bind, pure, Option.bind_some] at heq
      cases heq
      cases spec with
      | mono ty => exact fun hv => h.1 _ (List.mem_of_getElem? hlookup) (Ty.freeVars_closeOver_subset hv)
      | poly sigma => exact h.1 _ (List.mem_of_getElem? hlookup)
  · exact h.exported (heq ▸ List.getElem_mem hi)

theorem FinishRecComponent.avoids (h : FinishRecComponent K soft members ctx state outputs facts final)
    (ha : state.Avoids w) : final.Avoids w := by
  cases h
  exact ha.exportComponent

private theorem opening_template_avoid {template : TyTemplate} {names : List Nat}
    (ht : w ∉ template.rigidVars) (hn : w ∉ names) :
    w ∉ (template.openTyVarsFrom 0 names).rigidVars := by
  intro hv
  have hh := template.openTyVarsFrom_scope (K := template.rigidVars) (fun _ h => h) 0 names w hv
  exact (List.mem_append.mp hh).elim ht hn

theorem OpenRecAnn.expected_avoid (h : OpenRecAnn frontier ann next opening) (hw : w < frontier)
    (ha : w ∉ ann.rigidVars) (he : opening.expected = some ty) : w ∉ ty.freeVars := by
  cases h with
  | absent | complete => cases he
  | template halloc _ =>
    cases he
    simpa only [halloc] using TyTemplate.allocate_avoid hw ha
  | @partialForall next ty frontier count template halloc _ =>
    cases he
    have hn : w ∉ freshVars frontier count := fun hm => by have := freshVars_ge w hm; omega
    have hh := TyTemplate.allocate_avoid (frontier := frontier + count) (by omega : w < frontier + count)
      (opening_template_avoid ha hn)
    simpa only [halloc] using hh

theorem OpenRecAnns.expected_avoid (h : OpenRecAnns members index frontier anns next openings)
    (hw : w < frontier) (ha : ∀ ann ∈ anns, w ∉ ann.rigidVars) :
    ∀ opening ∈ openings, ∀ ty, opening.expected = some ty → w ∉ ty.freeVars := by
  induction h with
  | nil => intro opening hm; cases hm
  | skip _ _ ih =>
    intro opening hm ty he
    rcases List.mem_cons.mp hm with rfl | hm
    · cases he
    · exact ih hw (fun ann hm => ha ann (List.mem_cons_of_mem _ hm)) opening hm ty he
  | cons _ hh ht ih =>
    intro opening hm ty he
    rcases List.mem_cons.mp hm with rfl | hm
    · exact hh.expected_avoid hw (ha _ List.mem_cons_self) he
    · exact ih (Nat.lt_of_lt_of_le hw hh.frontier_le)
        (fun ann hm => ha ann (List.mem_cons_of_mem _ hm)) opening hm ty he

private theorem openRecSources_locality {openings : List RecOpening} {bindings : List InferInput}
    (ho : ∀ opening ∈ openings, w ∉ opening.written)
    (hr : ∀ rhs ∈ bindings, rhs.erase.ForallOuter P depth ∧ w ∉ rhs.rigidVars) :
    ∀ rhs ∈ openRecSources openings bindings, rhs.erase.ForallOuter P depth ∧ w ∉ rhs.rigidVars := by
  induction bindings generalizing openings with
  | nil => cases openings <;> intro rhs hm <;> cases hm
  | cons rhs rest ih =>
    cases openings with
    | nil => exact hr
    | cons opening openings =>
      intro source hs
      rcases List.mem_cons.mp hs with rfl | hs
      · refine ⟨by simpa only [InferInput.erase_openTyVars] using (hr rhs List.mem_cons_self).1, ?_⟩
        intro hv
        exact (InferInput.rigidVars_openTyVarsFrom hv).elim (hr rhs List.mem_cons_self).2 (ho opening List.mem_cons_self)
      · exact ih (fun opening ho' => ho opening (List.mem_cons_of_mem _ ho'))
          (fun rhs hr' => hr rhs (List.mem_cons_of_mem _ hr')) source hs

private theorem recShapes_avoid {state : RecState} (ha : state.Avoids w)
    (ho : ∀ opening ∈ openings, ∀ ty, opening.expected = some ty → w ∉ ty.freeVars) :
    ∀ shape ∈ state.shapes members openings, w ∉ shape.1.freeVars ∧
      ∀ ty, shape.2 = some ty → w ∉ ty.freeVars := by
  intro shape hs
  obtain ⟨i, _, heq⟩ := List.mem_filterMap.mp hs
  cases hspec : state.specs[i]? with
  | none => simp [hspec] at heq
  | some spec =>
    cases spec with
    | poly scheme => simp [hspec, RecSpec.monoTy?] at heq
    | mono ty =>
      cases hopen : openings[i]? with
      | none => simp [hspec, RecSpec.monoTy?, hopen] at heq
      | some opening =>
        simp [hspec, RecSpec.monoTy?, hopen] at heq
        subst shape
        exact ⟨ha.1 _ (List.mem_of_getElem? hspec), ho opening (List.mem_of_getElem? hopen)⟩

private theorem FinishRecComponent.avoid_lengths
    (h : FinishRecComponent K soft members ctx state outputs facts final) :
    final.specs.length = state.specs.length ∧ final.exports.length = state.exports.length := by
  cases h
  exact ⟨rfl, List.length_mapIdx⟩


 theorem _root_.InferRecStrata.sourceLocality_of_infer
    (h : InferRecStrata K F frontier ctx anns bindings state groups next S final)
    (hInfer : ∀ {κ F' Ψ c e Ψ' T output ty}, e.size ≤ sizeBindings bindings →
      Infer κ F' Ψ c e Ψ' T output ty →
      ∀ {w}, w < Ψ →
      e.erase.ForallOuter (fun i => ∀ M, c.env[i]? = some M → w ∉ M.body.freeVars) 0 →
      w ∉ e.rigidVars →
      (∀ p ∈ T, w ∉ p.2.freeVars) ∧ w ∉ ty.freeVars ∧ w ∉ T.map Prod.fst)
    (hw : w < frontier) (ha : state.Avoids w)
    (hlenS : state.specs.length = bindings.length)
    (hlenE : state.exports.length = bindings.length)
    (hanns : ∀ ann ∈ anns, w ∉ ann.rigidVars)
    (hrhs : ∀ rhs ∈ bindings, rhs.erase.ForallOuter
      (fun i => ∀ M, ctx.env[i]? = some M → w ∉ M.body.freeVars) bindings.length ∧ w ∉ rhs.rigidVars) :
    (∀ p ∈ S, w ∉ p.2.freeVars) ∧ w ∉ S.map Prod.fst ∧ final.Avoids w := by
  match h with
  | .nil => exact ⟨by simp, by simp, ha⟩
  | .cons ho hp hc hf hr =>
    expose_names
    have hpre := hp.sourceAvoid (recShapes_avoid ha.installOpenings (ho.expected_avoid hw hanns))
    have hapre : ((state.installOpenings component openings).onSubst pre).Avoids w :=
      ha.installOpenings.onSubst hpre.1
    have hentry : (((state.installOpenings component openings).onSubst pre).entries).length = bindings.length := by
      rw [RecState.entries_length]
      · simpa [RecState.onSubst, RecState.installOpenings] using hlenS
      · simpa [RecState.onSubst, RecState.installOpenings] using hlenE.trans hlenS.symm
    have hopen : ∀ rhs ∈ openRecSources openings bindings, rhs.erase.ForallOuter
        (fun i => ∀ M, ctx.env[i]? = some M → w ∉ M.body.freeVars) bindings.length ∧ w ∉ rhs.rigidVars :=
      openRecSources_locality (fun opening hm hv => by
        have hh := ho.written_range w (List.mem_flatMap.mpr ⟨opening, hm, hv⟩)
        omega) hrhs
    have hcomponent := hc.sourceLocality_of_infer
      (fun he hi => hInfer (by simpa only [sizeBindings_map_substTyFvars, sizeBindings_openRecSources] using he) hi)
      (Nat.lt_of_lt_of_le hw ho.frontier_le)
      (by
        intro j rhs _ hget
        obtain ⟨old, hold, rfl⟩ := Option.map_eq_some_iff.mp (by simpa only [List.getElem?_map] using hget)
        have hh := hopen old (List.mem_of_getElem? hold)
        refine ⟨?_, InferInput.avoid_subst hpre.1 hh.2⟩
        exact hapre.rhsCtx hentry (by simpa only [InferInput.erase_substTyFvars] using
          Expr.ForallOuter.lookupAvoid_onSubst hh.1 hpre.1))
      (by intro j ty _ hget; exact hapre.1 _ (List.mem_of_getElem? hget))
    have hboth : ∀ p ∈ pre ++ current, w ∉ p.2.freeVars :=
      fun p hm => (List.mem_append.mp hm).elim (hpre.1 p) (hcomponent.1 p)
    have hafinal := hf.avoids (ha.installOpenings.onSubst hboth)
    have hlength := hf.avoid_lengths
    have htailS : exported.specs.length = (bindings.map (InferInput.substTyFvars (pre ++ current))).length := by
      simpa [RecState.onSubst, RecState.installOpenings] using hlength.1.trans (by simpa [RecState.onSubst, RecState.installOpenings] using hlenS)
    have htailE : exported.exports.length = (bindings.map (InferInput.substTyFvars (pre ++ current))).length := by
      simpa [RecState.onSubst, RecState.installOpenings] using hlength.2.trans (by simpa [RecState.onSubst, RecState.installOpenings] using hlenE)
    obtain ⟨htS, htD, htA⟩ := hr.sourceLocality_of_infer
      (fun he hi => hInfer (by simpa only [sizeBindings_map_substTyFvars] using he) hi)
      (Nat.lt_of_lt_of_le hw (ho.frontier_le.trans hc.frontier_le)) hafinal htailS htailE
      (by intro ann hm; obtain ⟨old, hold, rfl⟩ := List.mem_map.mp hm
          exact BindingAnn.avoid_subst hboth (hanns old hold))
      (by intro rhs hm; obtain ⟨old, hold, rfl⟩ := List.mem_map.mp hm
          have hh := hrhs old hold
          exact ⟨by simpa only [InferInput.erase_substTyFvars, List.length_map] using
            Expr.ForallOuter.lookupAvoid_onSubst hh.1 hboth, InferInput.avoid_subst hboth hh.2⟩)
    refine ⟨fun p hp => (List.mem_append.mp hp).elim (hboth p) (htS p), ?_, htA⟩
    simpa only [List.map_append, List.mem_append, not_or] using And.intro (And.intro hpre.2 hcomponent.2) htD
 termination_by structural h

 theorem _root_.InferRecSigned.sourceLocality_of_infer
    (h : InferRecSigned K F index frontier ctx anns bindings state next S final)
    (hInfer : ∀ {κ F' Ψ c e Ψ' T output ty}, e.size ≤ sizeBindings bindings →
      Infer κ F' Ψ c e Ψ' T output ty →
      ∀ {w}, w < Ψ →
      e.erase.ForallOuter (fun i => ∀ M, c.env[i]? = some M → w ∉ M.body.freeVars) 0 →
      w ∉ e.rigidVars →
      (∀ p ∈ T, w ∉ p.2.freeVars) ∧ w ∉ ty.freeVars ∧ w ∉ T.map Prod.fst)
    (hw : w < frontier) (ha : state.Avoids w)
    (groupSize : Nat) (hlenS : state.specs.length = groupSize)
    (hlenE : state.exports.length = groupSize)
    (hanns : ∀ ann ∈ anns, w ∉ ann.rigidVars)
    (hrhs : ∀ rhs ∈ bindings, rhs.erase.ForallOuter
      (fun i => ∀ M, ctx.env[i]? = some M → w ∉ M.body.freeVars) groupSize ∧ w ∉ rhs.rigidVars) :
    (∀ p ∈ S, w ∉ p.2.freeVars) ∧ w ∉ S.map Prod.fst ∧ final.Avoids w := by
  match h with
  | .nil => exact ⟨by simp, by simp, ha⟩
  | .skip _ hr =>
    exact hr.sourceLocality_of_infer
      (fun he hi => hInfer (by simp only [sizeBindings]; omega) hi) hw ha groupSize hlenS hlenE
      (fun ann hm => hanns ann (List.mem_cons_of_mem _ hm))
      (fun rhs hm => hrhs rhs (List.mem_cons_of_mem _ hm))
  | .cons _ _ hi hu _ hr =>
    expose_names
    have hy : w ∉ freshVars frontier scheme.paramCount := fun hm => by
      have := freshVars_ge w hm; omega
    have hhead := hrhs rhs List.mem_cons_self
    have hentry : state.entries.length = groupSize := by
      rw [state.entries_length (hlenE.trans hlenS.symm)]; exact hlenS
    obtain ⟨hfirstS, hfirstTy, hfirstD⟩ := hInfer
      (by simp only [InferInput.size_openTyVars, sizeBindings]; omega) hi (by omega)
      (by simpa only [InferInput.erase_openTyVars] using ha.rhsCtx hentry hhead.1)
      (fun hv => (InferInput.rigidVars_openTyVarsFrom hv).elim hhead.2 hy)
    have hexpected : w ∉ ((s1.onPolyTy scheme).openVars (freshVars frontier scheme.paramCount)).freeVars := by
      intro hv
      exact (Ty.freeVars_openVars_subset w hv).elim
        (Subst.notMemOnTy hfirstS (hanns (.complete scheme) List.mem_cons_self)) hy
    have hsecondS : ∀ p ∈ s2, w ∉ p.2.freeVars := by
      intro p hp hv
      exact (hu.unifies.range_mem p hp w hv).elim hfirstTy hexpected
    have hsecondD : w ∉ s2.map Prod.fst := by
      intro hm
      obtain ⟨p, hp, hpw⟩ := List.mem_map.mp hm
      have hh := hu.unifies.dom_mem p hp
      rw [hpw] at hh
      exact hh.elim hfirstTy hexpected
    have hboth : ∀ p ∈ s1 ++ s2, w ∉ p.2.freeVars :=
      fun p hm => (List.mem_append.mp hm).elim (hfirstS p) (hsecondS p)
    have hanext : ((state.onSubst (s1 ++ s2)).setSigned index (freshVars frontier scheme.paramCount)
        (output.substTyFvars s2) (bodyFacts.onSubst s2)).Avoids w :=
      (ha.onSubst hboth).setSigned
    obtain ⟨htS, htD, htA⟩ := hr.sourceLocality_of_infer
      (fun he hh => hInfer (by
        simp only [sizeBindings_map_substTyFvars] at he
        simp only [sizeBindings]
        omega) hh)
      (by have := hi.frontier_le; omega) hanext groupSize
      (by simpa [RecState.setSigned, RecState.onSubst] using hlenS)
      (by simpa [RecState.setSigned, RecState.onSubst] using hlenE)
      (by intro ann hm; obtain ⟨old, hold, rfl⟩ := List.mem_map.mp hm
          exact BindingAnn.avoid_subst hboth (hanns old (List.mem_cons_of_mem _ hold)))
      (by intro source hm; obtain ⟨old, hold, rfl⟩ := List.mem_map.mp hm
          have hh := hrhs old (List.mem_cons_of_mem _ hold)
          exact ⟨by simpa only [InferInput.erase_substTyFvars] using
            Expr.ForallOuter.lookupAvoid_onSubst hh.1 hboth, InferInput.avoid_subst hboth hh.2⟩)
    refine ⟨fun p hp => (List.mem_append.mp hp).elim (hboth p) (htS p), ?_, htA⟩
    simpa only [List.map_append, List.mem_append, not_or] using And.intro (And.intro hfirstD hsecondD) htD
 termination_by structural h


private theorem mem_eraseBindings {bindings : List InferInput} {rhs : InferInput}
    (hr : rhs ∈ bindings) : rhs.erase ∈ eraseBindings bindings := by
  induction bindings with
  | nil => cases hr
  | cons head rest ih =>
    rcases List.mem_cons.mp hr with rfl | hr
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (ih hr)

private theorem rigidBindingVars_mem {bindings : List InferInput} {rhs : InferInput} {v : Nat}
    (hr : rhs ∈ bindings) (hv : v ∈ rhs.rigidVars) : v ∈ rigidBindingVars bindings := by
  induction bindings with
  | nil => cases hr
  | cons head rest ih =>
    rcases List.mem_cons.mp hr with rfl | hr
    · exact List.mem_append_left _ hv
    · exact List.mem_append_right _ (ih hr)

 theorem _root_.InferRecStrata.env_lengths
    (h : InferRecStrata K F frontier ctx anns bindings state groups next S final) :
    final.specs.length = state.specs.length ∧ final.exports.length = state.exports.length := by
  match h with
  | .nil => exact ⟨rfl, rfl⟩
  | .cons _ _ _ hf hr =>
    have he := hf.avoid_lengths
    have ht := hr.env_lengths
    exact ⟨ht.1.trans (he.1.trans (by simp [RecState.onSubst, RecState.installOpenings])),
      ht.2.trans (he.2.trans (by simp [RecState.onSubst, RecState.installOpenings]))⟩
 termination_by structural h

 theorem _root_.InferRecSigned.env_lengths
    (h : InferRecSigned K F index frontier ctx anns bindings state next S final) :
    final.specs.length = state.specs.length ∧ final.exports.length = state.exports.length := by
  match h with
  | .nil => exact ⟨rfl, rfl⟩
  | .skip _ hr => exact hr.env_lengths
  | .cons _ _ _ _ _ hr =>
    have ht := hr.env_lengths
    exact ⟨ht.1.trans (by simp [RecState.onSubst, RecState.setSigned]),
      ht.2.trans (by simp [RecState.onSubst, RecState.setSigned])⟩
 termination_by structural h

mutual
 theorem _root_.Infer.sourceLocality (h : Infer K F frontier ctx input next subst output ty) :
    ∀ {w}, w < frontier →
    input.erase.ForallOuter (fun i => ∀ M, ctx.env[i]? = some M → w ∉ M.body.freeVars) 0 →
    w ∉ input.rigidVars →
    (∀ p ∈ subst, w ∉ p.2.freeVars) ∧ w ∉ ty.freeVars ∧ w ∉ subst.map Prod.fst := by
  match h with
  | .primLitUnit | .primLitInt | .primLitNat | .primLitChar
  | .primBinOpIntAdd | .primBinOpIntSub | .primBinOpIntLt _ _ _ _
  | .primBinOpCharLt _ _ _ _ =>
    intro w _ _ _; simp [Ty.freeVars, TyList.freeVars]
  | .var hlook =>
    intro w hw hrefs _
    refine ⟨by simp, ?_, by simp⟩
    intro hc
    rcases Ty.freeVars_openVars_subset w hc with h | h
    · simp only [InferInput.erase, Expr.ForallOuter, Expr.rec_strong, Nat.zero_le, Nat.sub_zero] at hrefs
      exact hrefs (by trivial) _ hlook h
    · have := freshVars_ge w h; omega
  | .ctor hlook =>
    intro w hw _ _
    refine ⟨by simp, ?_, by simp⟩
    intro hc
    rcases Ty.freeVars_openVars_subset w hc with h | h
    · exact (Ctor.toTy_body_noFreeVars _).not_mem_freeVars w h
    · have := freshVars_ge w h; omega
  | .lambda _ hs hb =>
    intro w hw hrefs hwe
    simp only [InferInput.erase, Expr.ForallOuter, Expr.rec_strong, Nat.zero_add] at hrefs
    simp only [InferInput.rigidVars, List.mem_append, not_or] at hwe
    have hp := hs.sourceAvoid hw (by intro t ht; cases ht; exact hwe.1)
    have hbrefs := Expr.ForallOuter.lookupAvoid_prepend (pre := [PolyTy.mkTrivial _]) hrefs
      (by intro M hM; rcases List.mem_singleton.mp hM with rfl; exact hp)
    obtain ⟨hS, hty, hD⟩ := hb.sourceLocality (Nat.lt_of_lt_of_le hw hs.frontier_le) hbrefs hwe.2
    exact ⟨hS, by simpa only [Ty.freeVars, List.mem_dedup, List.mem_append, not_or]
      using And.intro (Subst.notMemOnTy hS hp) hty, hD⟩
  | .app _ hf ha hu =>
    intro w hw hrefs hwe
    expose_names
    simp only [InferInput.erase, Expr.ForallOuter, Expr.rec_strong] at hrefs
    simp only [InferInput.rigidVars, List.mem_append, not_or] at hwe
    obtain ⟨hfS, hfTy, hfD⟩ := hf.sourceLocality hw hrefs.1 hwe.1
    obtain ⟨haS, haTy, haD⟩ := ha.sourceLocality (Nat.lt_of_lt_of_le hw hf.frontier_le)
      (by simpa only [InferInput.erase_substTyFvars] using Expr.ForallOuter.lookupAvoid_onSubst hrefs.2 hfS)
      (InferInput.avoid_subst hfS hwe.2)
    have hnew : w ∉ (Ty.fvar second).freeVars := by
      simp only [Ty.freeVars, List.mem_singleton]; have := hf.frontier_le; have := ha.frontier_le; omega
    have huA := UnifyRel.sourceAvoid_local hu.unifies (Subst.notMemOnTy haS hfTy)
      (by simpa only [Ty.freeVars, List.mem_dedup, List.mem_append, not_or] using And.intro haTy hnew)
    have hA := Subst.sourceAvoid_append_local (Subst.sourceAvoid_append_local ⟨hfS, hfD⟩ ⟨haS, haD⟩) huA
    exact ⟨hA.1, Subst.notMemOnTy huA.1 hnew, hA.2⟩
  | .letIn _ hr hc hb =>
    intro w hw hrefs hwe
    expose_names
    simp only [InferInput.erase, Expr.ForallOuter, Expr.rec_strong, Nat.zero_add] at hrefs
    simp only [InferInput.rigidVars, List.mem_append, not_or] at hwe
    obtain ⟨hrS, hrTy, hrD⟩ := hr.sourceLocality hw hrefs.1 hwe.1.2
    have hcA := hc.sourceAvoid (Nat.lt_of_lt_of_le hw hr.frontier_le) hrTy
      (BindingAnn.avoid_subst hrS hwe.1.1)
    have hA := Subst.sourceAvoid_append_local ⟨hrS, hrD⟩ hcA
    have hfinalTy := Subst.notMemOnTy hcA.1 hrTy
    have hp : w ∉ (genScheme (K ++ softVars (substSoft (s1 ++ sCheck) F))
      (sCheck.onCtx (s1.onCtx ctx)).env (sCheck.onTy rhsTy)).body.freeVars :=
      fun hm => hfinalTy (Ty.freeVars_closeOver_subset hm)
    have hbrefs := Expr.ForallOuter.lookupAvoid_prepend (pre := [genScheme _ _ _])
      (Expr.ForallOuter.lookupAvoid_onSubst (Expr.ForallOuter.lookupAvoid_onSubst hrefs.2 hrS) hcA.1)
      (by intro M hM; rcases List.mem_singleton.mp hM with rfl; exact hp)
    obtain ⟨hbS, hbTy, hbD⟩ := hb.sourceLocality
      (Nat.lt_of_lt_of_le hw (hr.frontier_le.trans hc.frontier_le))
      (by simpa only [InferInput.erase_substTyFvars] using hbrefs) (InferInput.avoid_subst hA.1 hwe.2)
    have hAll := Subst.sourceAvoid_append_local hA ⟨hbS, hbD⟩
    exact ⟨hAll.1, hbTy, hAll.2⟩
  | .letSignature _ heq _ _ hr hc _ hb =>
    intro w hw hrefs hwe
    expose_names
    subst written
    simp only [InferInput.erase, Expr.ForallOuter, Expr.rec_strong, Nat.zero_add] at hrefs
    simp only [InferInput.rigidVars, List.mem_append, not_or] at hwe
    have hwr : w ∉ freshVars frontier ann.paramCount := fun hm => by have := freshVars_ge w hm; omega
    obtain ⟨hrS, hrTy, hrD⟩ := hr.sourceLocality (by omega)
      (by simpa only [InferInput.erase_openTyVars] using hrefs.1)
      (fun hm => (InferInput.rigidVars_openTyVarsFrom hm).elim hwe.1.2 hwr)
    have hcA := hc.sourceAvoid (Nat.lt_of_lt_of_le hw (by have := hr.frontier_le; omega)) hrTy
      (BindingAnn.avoid_subst hrS hwe.1.1) hwr
    have hA := Subst.sourceAvoid_append_local ⟨hrS, hrD⟩ hcA
    have hp : w ∉ (signatureScheme (ann.substTyFvars (s1 ++ sCheck))
      (K ++ softVars (substSoft (s1 ++ sCheck) F)) (freshVars frontier ann.paramCount)
      (sCheck.onCtx (s1.onCtx ctx)) (sCheck.onTy rhsTy)).body.freeVars := by
      cases ann with
      | complete σ => exact BindingAnn.avoid_subst hA.1 hwe.1.1
      | absent | template t | partialForall n t =>
        exact fun hm => Subst.notMemOnTy hcA.1 hrTy (Ty.freeVars_closeOver_subset hm)
    have hbrefs := Expr.ForallOuter.lookupAvoid_prepend (pre := [signatureScheme _ _ _ _ _])
      (Expr.ForallOuter.lookupAvoid_onSubst (Expr.ForallOuter.lookupAvoid_onSubst hrefs.2 hrS) hcA.1)
      (by intro M hM; rcases List.mem_singleton.mp hM with rfl; exact hp)
    obtain ⟨hbS, hbTy, hbD⟩ := hb.sourceLocality
      (Nat.lt_of_lt_of_le hw (by have := hr.frontier_le; have := hc.frontier_le; omega))
      (by simpa only [InferInput.erase_substTyFvars] using hbrefs) (InferInput.avoid_subst hA.1 hwe.2)
    have hAll := Subst.sourceAvoid_append_local hA ⟨hbS, hbD⟩
    exact ⟨hAll.1, hbTy, hAll.2⟩
  | .letRec _ _ hv hs hp _ _ hb =>
    intro w hw hrefs hwe
    expose_names
    have hv := hv.1
    simp only [InferInput.erase, Expr.ForallOuter, Expr.rec_strong, eraseBindings_length, Nat.zero_add] at hrefs
    simp only [InferInput.rigidVars, List.mem_append, not_or] at hwe
    have hanns : ∀ ann ∈ anns, w ∉ ann.rigidVars :=
      fun ann ha hv => hwe.1.1 (List.mem_flatMap.mpr ⟨ann, ha, hv⟩)
    have hrhs : ∀ rhs ∈ bindings, rhs.erase.ForallOuter
        (fun i => ∀ M, ctx.env[i]? = some M → w ∉ M.body.freeVars) bindings.length ∧ w ∉ rhs.rigidVars := by
      intro rhs hr
      exact ⟨hrefs.1 rhs.erase (mem_eraseBindings hr), fun hv => hwe.1.2 (rigidBindingVars_mem hr hv)⟩
    have hlen : anns.length = bindings.length := by simpa only [List.length_map] using hv.length
    obtain ⟨hsS, hsD, hstate1⟩ := hs.sourceLocality_of_infer (fun _ hi => hi.sourceLocality)
      (by omega) (RecState.Avoids.init hw hanns)
      (by simpa only [RecState.init, RecSpec.init_length, List.length_map] using hlen)
      (by simpa only [RecState.init, List.length_map] using hlen) hanns hrhs
    have hsl := hs.env_lengths
    have hs1len : state1.specs.length = bindings.length := by
      simpa only [RecState.init, RecSpec.init_length, List.length_map] using hsl.1.trans (by simpa [RecState.init, RecSpec.init_length] using hlen)
    have he1len : state1.exports.length = bindings.length := by
      simpa only [RecState.init, List.length_map] using hsl.2.trans (by simpa [RecState.init] using hlen)
    obtain ⟨hpS, hpD, hstate2⟩ := hp.sourceLocality_of_infer (fun _ hi => hi.sourceLocality)
      (by have := hs.frontier_le; omega) hstate1 bindings.length hs1len he1len
      (by intro ann ha; obtain ⟨old, ho, rfl⟩ := List.mem_map.mp ha; exact BindingAnn.avoid_subst hsS (hanns old ho))
      (by
        intro rhs hr
        obtain ⟨old, ho, rfl⟩ := List.mem_map.mp hr
        exact ⟨by simpa only [InferInput.erase_substTyFvars] using Expr.ForallOuter.lookupAvoid_onSubst (hrhs old ho).1 hsS,
          InferInput.avoid_subst hsS (hrhs old ho).2⟩)
    have hpre := Subst.sourceAvoid_append_local ⟨hsS, hsD⟩ ⟨hpS, hpD⟩
    have hpl := hp.env_lengths
    have hentries : state2.entries.length = bindings.length := by
      rw [state2.entries_length ((hpl.2.trans he1len).trans (hpl.1.trans hs1len).symm)]
      exact hpl.1.trans hs1len
    obtain ⟨hbS, hbTy, hbD⟩ := hb.sourceLocality (show w < second from by have := hs.frontier_le; have := hp.frontier_le; omega)
      (by
        have hh := hstate2.rhsCtx hentries (Expr.ForallOuter.lookupAvoid_onSubst hrefs.2 hpre.1)
        simpa only [InferInput.erase_substTyFvars] using hh)
      (InferInput.avoid_subst hpre.1 hwe.2)
    have hAll := Subst.sourceAvoid_append_local hpre ⟨hbS, hbD⟩
    exact ⟨hAll.1, hbTy, hAll.2⟩
  | .match_ _ hs _ hb =>
    intro w hw hrefs hwe
    expose_names
    simp only [InferInput.erase, Expr.ForallOuter, Expr.rec_strong, Nat.zero_add] at hrefs
    simp only [InferInput.rigidVars, List.mem_append, not_or] at hwe
    obtain ⟨hsS, hsTy, hsD⟩ := hs.sourceLocality hw hrefs.1 hwe.1
    have hnew : w ∉ (Ty.fvar first).freeVars := by
      simp only [Ty.freeVars, List.mem_singleton]; have := hs.frontier_le; omega
    obtain ⟨hbS, hbTy, hbD⟩ := hb.sourceLocality (by have := hs.frontier_le; omega)
      (branches_refs_subst (fun p b hm => hrefs.2 p b.erase (mem_eraseBranches hm)) hsS)
      hsTy hnew (branches_avoid_subst hsS hwe.2)
    have hA := Subst.sourceAvoid_append_local ⟨hsS, hsD⟩ ⟨hbS, hbD⟩
    exact ⟨hA.1, hbTy, hA.2⟩
 termination_by (input.size, 1)
 decreasing_by
  all_goals simp only [sizeBindings_map_substTyFvars] at *
  all_goals (simp only [InferInput.size, InferInput.size_substTyFvars, InferInput.size_openTyVars, sizeBranches_substInputBranches]; omega)

 theorem _root_.InferBranches.sourceLocality
    (h : InferBranches K F frontier ctx scrutTy resultTy brs next subst completed) :
    ∀ {w}, w < frontier →
    (∀ p b, (p,b) ∈ brs → b.erase.ForallOuter
      (fun i => ∀ M, ctx.env[i]? = some M → w ∉ M.body.freeVars) p.bindCount) →
    w ∉ scrutTy.freeVars → w ∉ resultTy.freeVars → w ∉ rigidBranchVars brs →
    (∀ p ∈ subst, w ∉ p.2.freeVars) ∧ w ∉ (subst.onTy resultTy).freeVars ∧ w ∉ subst.map Prod.fst := by
  match h with
  | .nil => intro w _ _ _ hρ _; exact ⟨by simp, by simpa using hρ, by simp⟩
  | .cons _ hlook hn hu₀ hb hu hr =>
    intro w hw hrefs hscrut hρ hbrs
    expose_names
    simp only [rigidBranchVars, List.mem_append, not_or] at hbrs
    have hcustom : w ∉ (Ty.customTy ctor.tyName ((freshVars frontier ctor.paramCount).map Ty.fvar)).freeVars := by
      intro hc; simp only [Ty.freeVars] at hc; rw [mem_TyList_freeVars] at hc
      obtain ⟨t, ht, hwt⟩ := hc; obtain ⟨x, hx, rfl⟩ := List.mem_map.mp ht
      simp only [Ty.freeVars, List.mem_singleton] at hwt
      have := freshVars_ge x hx; omega
    have hA₀ := UnifyRel.sourceAvoid_local hu₀.unifies hscrut hcustom
    have hta : ∀ t ∈ ((freshVars frontier ctor.paramCount).map Ty.fvar).map s0.onTy, w ∉ t.freeVars := by
      intro t ht; obtain ⟨t₀, ht₀, rfl⟩ := List.mem_map.mp ht
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp ht₀
      apply Subst.notMemOnTy hA₀.1
      simp only [Ty.freeVars, List.mem_singleton]; have := freshVars_ge x hx; omega
    have hbrefs : body.erase.ForallOuter
        (fun i => ∀ M,
          ((ctor.contents.map (Ty.openWith (((freshVars frontier ctor.paramCount).map Ty.fvar).map s0.onTy))).map PolyTy.mkTrivial
            ++ (s0.onCtx ctx).env)[i]? = some M → w ∉ M.body.freeVars) 0 := by
      apply Expr.ForallOuter.lookupAvoid_prepend
        (by simpa only [List.length_map, Nat.zero_add, MatchPattern.bindCount, hn] using
          Expr.ForallOuter.lookupAvoid_onSubst (hrefs (.named name count) body List.mem_cons_self) hA₀.1)
      intro M hM; obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hM
      obtain ⟨t₀, ht₀, rfl⟩ := List.mem_map.mp ht
      exact Ty.not_mem_freeVars_openWith hta ((ctor.closed t₀ ht₀).not_mem_freeVars w)
    obtain ⟨hbS, hbTy, hbD⟩ := hb.sourceLocality (by omega)
      (by simpa only [InferInput.erase_substTyFvars] using hbrefs) (InferInput.avoid_subst hA₀.1 hbrs.1)
    have hA₂ := UnifyRel.sourceAvoid_local hu.unifies hbTy
      (Subst.notMemOnTy hbS (Subst.notMemOnTy hA₀.1 hρ))
    have hApre := Subst.sourceAvoid_append_local (Subst.sourceAvoid_append_local hA₀ ⟨hbS,hbD⟩) hA₂
    obtain ⟨hrS, hrTy, hrD⟩ := hr.sourceLocality (by have := hb.frontier_le; omega)
      (by
        have hf := branches_refs_subst
          (fun p b hm => hrefs p b (List.mem_cons_of_mem _ hm)) hApre.1
        simpa only [Subst.onCtx_append] using hf)
      (Subst.notMemOnTy hA₂.1 (Subst.notMemOnTy hbS (Subst.notMemOnTy hA₀.1 hscrut)))
      (Subst.notMemOnTy hA₂.1 (Subst.notMemOnTy hbS (Subst.notMemOnTy hA₀.1 hρ)))
      (branches_avoid_subst hApre.1 hbrs.2)
    have hA := Subst.sourceAvoid_append_local hApre ⟨hrS,hrD⟩
    exact ⟨hA.1, by simpa only [Subst.onTy_append] using hrTy, hA.2⟩
  | .consWild _ hb hu hr =>
    intro w hw hrefs hscrut hρ hbrs
    expose_names
    simp only [rigidBranchVars, List.mem_append, not_or] at hbrs
    obtain ⟨hbS, hbTy, hbD⟩ := hb.sourceLocality hw
      (hrefs .wildcard body List.mem_cons_self) hbrs.1
    have hA₂ := UnifyRel.sourceAvoid_local hu.unifies hbTy (Subst.notMemOnTy hbS hρ)
    have hApre := Subst.sourceAvoid_append_local ⟨hbS,hbD⟩ hA₂
    obtain ⟨hrS, hrTy, hrD⟩ := hr.sourceLocality (Nat.lt_of_lt_of_le hw hb.frontier_le)
      (by
        have hf := branches_refs_subst
          (fun p b hm => hrefs p b (List.mem_cons_of_mem _ hm)) hApre.1
        simpa only [Subst.onCtx_append] using hf)
      (Subst.notMemOnTy hA₂.1 (Subst.notMemOnTy hbS hscrut))
      (Subst.notMemOnTy hA₂.1 (Subst.notMemOnTy hbS hρ))
      (branches_avoid_subst hApre.1 hbrs.2)
    have hA := Subst.sourceAvoid_append_local hApre ⟨hrS,hrD⟩
    exact ⟨hA.1, by simpa only [Subst.onTy_append] using hrTy, hA.2⟩
 termination_by (sizeBranches brs, 0)
 decreasing_by all_goals (simp only [sizeBranches, InferInput.size_substTyFvars, sizeBranches_substInputBranches]; omega)
end

theorem RecSpec.notMem_freeVars_onSubstSource {S : Subst} {spec : RecSpec} {w : Nat}
    (hS : ∀ p ∈ S, w ∉ p.2.freeVars) (h : w ∉ spec.freeVars) :
    w ∉ (spec.onSubstSource S).freeVars := by
  cases spec with
  | mono ty => exact Subst.notMemOnTy hS h
  | poly scheme => exact Subst.notMemOnTy hS h

theorem RecSpec.mono_getElem?_map_onSubstSource {S : Subst} {specs : List RecSpec}
    {member : Nat} {ty : Ty}
    (h : (specs.map (RecSpec.onSubstSource S))[member]? = some (.mono ty)) :
    ∃ old, specs[member]? = some (.mono old) ∧ ty = S.onTy old := by
  rw [List.getElem?_map] at h
  obtain ⟨s, hs, heq⟩ := Option.map_eq_some_iff.mp h
  cases s with
  | mono old => exact ⟨old, hs, (RecSpec.mono.inj heq).symm⟩
  | poly scheme => cases heq

theorem RecSpecs.PendingSeeds.onSubst_source {base : Nat} {ctx : Ctx} {specs : List RecSpec}
    {done done' : List Nat} {S : Subst} (h : RecSpecs.PendingSeeds base ctx specs done)
    (hdone : ∀ member ∈ done, member ∈ done')
    (havoid : ∀ member ty, specs[member]? = some (.mono ty) → member ∉ done' →
      (∀ p ∈ S, base + member ∉ p.2.freeVars) ∧ base + member ∉ S.map Prod.fst) :
    RecSpecs.PendingSeeds base (S.onCtx ctx) (specs.map (RecSpec.onSubstSource S)) done' := by
  constructor
  · intro member ty hty hm
    obtain ⟨old, hold, rfl⟩ := RecSpec.mono_getElem?_map_onSubstSource hty
    rw [h.mono member old hold (fun hc => hm (hdone member hc))]
    apply Ty.substFvars_eq_self_of_no_key
    intro p hp hc
    apply (havoid member old hold hm).2
    apply List.mem_map.mpr
    refine ⟨p, hp, ?_⟩
    simpa only [Ty.freeVars, List.mem_singleton] using hc
  · intro member ty hty hm j spec hs hj
    obtain ⟨old, hold, _⟩ := RecSpec.mono_getElem?_map_onSubstSource hty
    rw [List.getElem?_map] at hs
    obtain ⟨oldSpec, holdSpec, rfl⟩ := Option.map_eq_some_iff.mp hs
    exact RecSpec.notMem_freeVars_onSubstSource (havoid member old hold hm).1
      (h.other member old hold (fun hc => hm (hdone member hc)) j oldSpec holdSpec hj)
  · intro member ty hty hm
    obtain ⟨old, hold, _⟩ := RecSpec.mono_getElem?_map_onSubstSource hty
    exact Subst.onCtx_avoid (h.env member old hold (fun hc => hm (hdone member hc)))
      (havoid member old hold hm).1

private theorem soft_avoids_subst {F : List Ty} {S : Subst} {v : Nat}
    (hF : v ∉ TyList.freeVars F) (hS : ∀ p ∈ S, v ∉ p.2.freeVars) :
    v ∉ TyList.freeVars (F.map S.onTy) := by
  intro hm
  obtain ⟨ty, ht, hv⟩ := TyList.mem_freeVars_iff.mp hm
  obtain ⟨old, ho, rfl⟩ := List.mem_map.mp ht
  exact Subst.notMemOnTy hS (fun hv => hF (TyList.mem_freeVars_iff.mpr ⟨old, ho, hv⟩)) hv

 theorem RecState.Frame.onSubst {state : RecState} {S : Subst}
    (h : state.Frame base K F ctx anns done)
    (hpool : ∀ g ∈ state.pool, (∀ p ∈ S, g ∉ p.2.freeVars) ∧ g ∉ S.map Prod.fst)
    (hpending : ∀ i ty, state.specs[i]? = some (.mono ty) → i ∉ done →
      (∀ p ∈ S, base + i ∉ p.2.freeVars) ∧ base + i ∉ S.map Prod.fst) :
    (state.onSubst S).Frame base K (F.map S.onTy) (S.onCtx ctx)
      (anns.map (BindingAnn.substTyFvars S)) done := by
  have hdom : ∀ p ∈ S, p.1 ∉ state.pool := by
    intro p hp hg
    exact (hpool p.1 hg).2 (List.mem_map.mpr ⟨p, hp, rfl⟩)
  have hran : ∀ p ∈ S, ∀ g ∈ p.2.freeVars, g ∉ state.pool :=
    fun p hp g hg hgp => (hpool g hgp).1 p hp hg
  have hfix : ∀ g ∈ state.pool, S.onTy (.fvar g) = .fvar g := Subst.fixes_of_dom_avoids hdom
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, h.pool_nodup, ?_, h.pool_rigid, ?_, ?_, ?_, h.rigid_below, ?_⟩
  · simpa only [RecState.onSubst, List.length_map] using h.specs_length
  · simpa only [RecState.onSubst, List.length_map] using h.slots_length
  · simpa only [RecState.onSubst, List.length_map] using h.exports_length
  · simpa only [RecState.onSubst, List.length_map] using h.outputs_length
  · simpa only [RecState.onSubst, List.length_map] using h.facts_length
  · have hm : ((state.onSubst S).specs).map RecSpec.ann =
        (state.specs.map RecSpec.ann).map (Option.map S.onPolyTy) := by
      simp only [RecState.onSubst, List.map_map]
      apply List.map_congr_left
      intro spec _
      cases spec <;> rfl
    rw [hm, h.modes]
    simp only [List.map_map, Function.comp_def, BindingAnn.recModeAnn_subst_source]
  · intro i scheme hget
    rw [RecState.onSubst, List.getElem?_map] at hget
    obtain ⟨old, hold, heq⟩ := Option.map_eq_some_iff.mp hget
    cases old with
    | mono ty => cases heq
    | poly σ =>
      cases RecSpec.poly.inj heq
      simp only [RecState.onSubst, List.getElem?_map, h.poly i σ hold, Option.map_some]
  · intro i ty hget
    rw [RecState.onSubst, List.getElem?_map] at hget
    obtain ⟨old, hold, heq⟩ := Option.map_eq_some_iff.mp hget
    cases old with
    | poly scheme => cases heq
    | mono original =>
      cases RecSpec.mono.inj heq
      by_cases hi : i ∈ done
      · obtain ⟨written, hslots, hcount, hnd, hsub, hexport⟩ := if_pos hi ▸ h.mono i original hold
        rw [if_pos hi]
        refine ⟨written, ?_, ?_, hnd, hsub, ?_⟩
        · simp only [RecState.onSubst, List.getElem?_map, hslots, Option.map_some, List.map_map]
          congr 1
          apply List.map_congr_left
          intro name hn
          exact hfix name (hsub name hn)
        · cases ha : anns[i]? with
          | none => simpa only [List.getElem?_map, ha, Option.map_none] using hcount
          | some ann => simpa only [List.getElem?_map, ha, Option.map_some, Option.getD_some,
              BindingAnn.recPrefixCount_subst_source] using hcount
        · simp only [RecState.onSubst, List.getElem?_map, hexport, Option.map_some]
          rw [recScheme_subst_pool_avoid hdom hran hsub]
      · rw [if_neg hi]
        have he := if_neg hi ▸ h.mono i original hold
        simp only [RecState.onSubst, List.getElem?_map, he, Option.map_some, Option.map_none]
  · exact h.pending.onSubst_source (fun _ hm => hm) hpending
  · intro g hg hm
    obtain ⟨scheme, hs, hv⟩ := Env.mem_freeVars_iff.mp hm
    obtain ⟨old, ho, rfl⟩ := List.mem_map.mp hs
    exact Subst.notMemOnTy (hpool g hg).1
      (fun hv => h.pool_ctx g hg (Env.mem_freeVars_iff.mpr ⟨old, ho, hv⟩)) hv
  · intro g hg
    exact soft_avoids_subst (h.pool_soft g hg) (hpool g hg).1
  · intro scheme ⟨i, hget⟩ g hg
    rw [RecState.onSubst, List.getElem?_map] at hget
    obtain ⟨old, hold, heq⟩ := Option.map_eq_some_iff.mp hget
    cases old with
    | mono ty => cases heq
    | poly σ =>
      cases RecSpec.poly.inj heq
      exact Subst.notMemOnTy (hpool g hg).1 (h.pool_poly σ ⟨i, hold⟩ g hg)
  · intro i ty hget hi
    obtain ⟨old, hold, _⟩ := RecSpec.mono_getElem?_map_onSubstSource hget
    exact h.pool_pending i old hold hi
  · intro i ty hget hi
    obtain ⟨old, hold, _⟩ := RecSpec.mono_getElem?_map_onSubstSource hget
    exact soft_avoids_subst (h.pending_soft i old hold hi) (hpending i old hold hi).1


private theorem mem_eraseBranches_local {branches : List (MatchPattern × InferInput)}
    (h : (pat, body) ∈ branches) : (pat, body.erase) ∈ eraseBranches branches := by
  induction branches with
  | nil => cases h
  | cons head rest ih =>
    rcases List.mem_cons.mp h with hh | hh
    · cases hh; exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (ih hh)
private theorem mem_eraseBindings_local {bindings : List InferInput} (h : rhs ∈ bindings) :
    rhs.erase ∈ eraseBindings bindings := by
  induction bindings with
  | nil => cases h
  | cons head rest ih =>
    rcases List.mem_cons.mp h with hh | hh
    · cases hh; exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (ih hh)

 theorem InputTyping.env_agreement {Q : List Nat} {ctx : Ctx} {input : InferInput} {ty : Ty}
    (h : InputTyping Q ctx input ty) : ∀ env',
    input.erase.ForallOuter (fun i => env'[i]? = ctx.env[i]?) 0 →
    InputTyping Q ⟨env', ctx.ctors⟩ input ty := by
  induction h using InputTyping.rec
      (motive_2 := fun Q ctx branch scrutTy resultTy _ => ∀ env',
        branch.2.erase.ForallOuter (fun i => env'[i]? = ctx.env[i]?) branch.1.bindCount →
        BranchTyping InputTyping Q ⟨env', ctx.ctors⟩ branch scrutTy resultTy) with
  | complete hemb hprotected hcore =>
    intro env' hag
    refine .complete hemb hprotected (hcore.env_agreement env' ?_)
    apply (Expr.ForallOuter.erase_iff _).mp
    rwa [InferInput.toCore_erase _ hemb]
  | primLit hcore =>
    intro env' hag
    exact .primLit (hcore.env_agreement env' hag)
  | primBinOp hcore =>
    intro env' hag
    exact .primBinOp (hcore.env_agreement env' hag)
  | lambda hlc hfit hprotected _ ih =>
    intro env' hag
    simp only [InferInput.erase, Expr.ForallOuter, Expr.rec_strong, Nat.zero_add] at hag
    refine .lambda hlc hfit hprotected (ih _ ?_)
    exact Expr.ForallOuter.prepend_env (pre := [PolyTy.mkTrivial _]) hag
  | app _ _ ihf iha =>
    intro env' hag
    simp only [InferInput.erase, Expr.ForallOuter, Expr.rec_strong] at hag
    exact .app (ihf env' hag.1) (iha env' hag.2)
  | letIn hwf hprotected hfit _ _ ihr ihb =>
    intro env' hag
    simp only [InferInput.erase, Expr.ForallOuter, Expr.rec_strong, Nat.zero_add] at hag
    refine .letIn hwf hprotected hfit (fun Xs hf => ihr Xs hf env' hag.1) (ihb _ ?_)
    exact Expr.ForallOuter.prepend_env (pre := [_]) hag.2
  | letSignature hwf hann hrhs hfit _ _ ihr ihb =>
    intro env' hag
    simp only [InferInput.erase, Expr.ForallOuter, Expr.rec_strong, Nat.zero_add] at hag
    refine .letSignature hwf hann hrhs hfit (fun Xs hf => ihr Xs hf env' ?_) (ihb _ ?_)
    · simpa only [InferInput.erase_openTyVars] using hag.1
    · exact Expr.ForallOuter.prepend_env (pre := [_]) hag.2
  | var hlook hargs hinst =>
    intro env' hag
    simp only [InferInput.erase, Expr.ForallOuter, Expr.rec_strong, Nat.zero_le, Nat.sub_zero] at hag
    exact .var (by rw [hag trivial]; exact hlook) hargs hinst
  | ctor hlook hargs hinst => intro _ _; exact .ctor hlook hargs hinst
  | match_ _ hne _ ihs ihbr =>
    intro env' hag
    simp only [InferInput.erase, Expr.ForallOuter, Expr.rec_strong, Nat.zero_add] at hag
    refine .match_ (ihs env' hag.1) hne ?_
    intro ⟨pat, body⟩ hb
    exact ihbr (pat, body) hb env' (hag.2 pat body.erase (mem_eraseBranches_local hb))
  | @letRec anns K bindings ctx body resultTy specs groups prefixes G L hg hw hp hG hAnn hRhs hFits _ _ _ ihMono ihPoly ihBody =>
    intro env' hag
    simp only [InferInput.erase, Expr.ForallOuter, Expr.rec_strong, eraseBindings_length, Nat.zero_add] at hag
    let avoid := K ++ env'.freeVars ++ G ++ specs.flatMap RecSpec.freeVars
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
    let prefixes' := prefixes.map (recRenameNames G W)
    let L' := G ++ W ++ L
    have annNil : anns.map (BindingAnn.substTyFvars []) = anns := by
      conv_rhs => rw [← List.map_id anns]
      apply List.map_congr_left
      intro ann _
      exact ann.substTyFvars_eq_self_of_fixes (fun _ _ => rfl)
    have hw' : RecSpecs.WF (anns.map BindingAnn.recModeAnn) (bindings.map InferInput.erase) specs' W := by
      simpa only [annNil] using RecSpecs.WF.subst_fresh_pool (S := []) hw (by simp) hWnd
    have hp' : RecPrefixesWF anns specs' prefixes' W := by
      simpa only [annNil] using hp.subst_fresh_pool (S := []) hWlen hWnd
    have hannsLen : anns.length = specs.length := by
      have hh := congrArg List.length hw.anns_eq
      simpa using hh.symm
    have hpData := fun i hi => hp.get hannsLen (i := i) hi
    have mapNil : ∀ xs : List PolyTy, xs.map (Subst.onPolyTy []) = xs := by
      intro xs
      rw [show Subst.onPolyTy [] = id from funext Subst.onPolyTy_nil, List.map_id]
    have hcompleted : recCompletedSchemes specs' prefixes' W = recCompletedSchemes specs prefixes G := by
      simpa only [mapNil] using recCompletedSchemes_subst_fresh_pool (S := []) (by simp) hWlen hw.nodup hWnd
        hGW hWmono (by simp) (by simp) hw.mono_lc hpData
    have oldFresh : ∀ Xs, FreshNames (W ++ L') W.length Xs → FreshNames (G ++ L) G.length Xs := by
      intro Xs hf
      refine ⟨hf.length.trans hWlen, hf.nodup, ?_⟩
      intro x hx hl
      exact hf.avoid x hx (by simp only [L', List.mem_append] at hl ⊢; tauto)
    have hGXs : ∀ Xs, FreshNames (W ++ L') W.length Xs → ∀ g ∈ G, g ∉ Xs := by
      intro Xs hf g hg hx
      exact hf.avoid g hx (by simp only [L', List.mem_append]; tauto)
    have hWXs : ∀ Xs, FreshNames (W ++ L') W.length Xs → ∀ w ∈ W, w ∉ Xs := by
      intro Xs hf w hw hx
      exact hf.avoid w hx (List.mem_append_left _ hw)
    have hstage : ∀ Xs, FreshNames (W ++ L') W.length Xs → ∀ done,
        specs'.mapIdx (recStageEntry prefixes' done W Xs) = specs.mapIdx (recStageEntry prefixes done G Xs) := by
      intro Xs hf done
      simpa only [mapNil] using recStageSchemes_subst_fresh_pool (S := []) (done := done) (by simp)
        hWlen hw.nodup hWnd hGW hWmono (by simp) (by simp) hw.mono_lc hpData
        (hf.length.trans hWlen) (hGXs Xs hf) (hWXs Xs hf) (by simp)
    have hsquare : ∀ ty, .mono ty ∈ specs → ∀ Xs, FreshNames (W ++ L') W.length Xs →
        Ty.renameG W Xs (Ty.renameG G W ty) = Ty.renameG G Xs ty := by
      intro ty ht Xs hf
      simpa only [Subst.onTy_nil] using Ty.renameG_subst_fresh_pool (S := []) (hw.mono_lc ty ht) (by simp)
        hWlen hw.nodup hWnd hGW (hWmono ty ht) (by simp) (by simp)
        (hf.length.trans hWlen) (hGXs Xs hf) (hWXs Xs hf) (by simp)
    refine InputTyping.letRec (specs := specs') (groups := groups) (prefixes := prefixes') (G := W) (L := L')
      hg hw' hp' ?_ hAnn hRhs ?_ ?_ ?_ ?_
    · intro w hw hm
      exact hWavoid w hw (by simp only [avoid, List.mem_append] at hm ⊢; tauto)
    · intro stage component hs Xs hf member hm rhs ann names ty hri hai hni hti
      rw [List.getElem?_map] at hni hti
      obtain ⟨names0, hn0, rfl⟩ := Option.map_eq_some_iff.mp hni
      obtain ⟨spec, ht0, heq⟩ := Option.map_eq_some_iff.mp hti
      cases spec with
      | poly scheme => cases heq
      | mono ty0 =>
        cases heq
        obtain ⟨_, _, hsub⟩ := hp.member member ann names0 hai hn0
        change ann.RecFits (recRenameNames W Xs (recRenameNames G W names0))
          (Ty.renameG W Xs (Ty.renameG G W ty0))
        rw [recRenameNames_composition hWlen (hf.length.trans hWlen) hWnd hsub,
          hsquare ty0 (List.mem_of_getElem? ht0) Xs hf]
        exact hFits stage component hs Xs (oldFresh Xs hf) member hm rhs ann names0 ty0 hri hai hn0 ht0
    · intro stage component hs Xs hf member hm rhs ann names ty hri hai hni hti
      rw [List.getElem?_map] at hni hti
      obtain ⟨names0, hn0, rfl⟩ := Option.map_eq_some_iff.mp hni
      obtain ⟨spec, ht0, heq⟩ := Option.map_eq_some_iff.mp hti
      cases spec with
      | poly scheme => cases heq
      | mono ty0 =>
        cases heq
        obtain ⟨_, _, hsub⟩ := hp.member member ann names0 hai hn0
        change InputTyping (K ++ Xs)
          (recStageCtx { ctx with env := env' } specs' prefixes' (groups.take stage).flatten W Xs)
          (rhs.openTyVars (recRenameNames W Xs (recRenameNames G W names0)))
          (Ty.renameG W Xs (Ty.renameG G W ty0))
        rw [recRenameNames_composition hWlen (hf.length.trans hWlen) hWnd hsub,
          hsquare ty0 (List.mem_of_getElem? ht0) Xs hf]
        have hc := ihMono stage component hs Xs (oldFresh Xs hf) member hm rhs ann names0 ty0 hri hai hn0 ht0
          ((specs.mapIdx (recStageEntry prefixes (groups.take stage).flatten G Xs)) ++ env') (by
            apply Expr.ForallOuter.prepend_env
            simpa only [InferInput.erase_openTyVars, List.length_mapIdx, Nat.zero_add, ← hw.length, List.length_map] using
              hag.1 rhs.erase (mem_eraseBindings_local (List.mem_of_getElem? hri)))
        simpa only [recStageCtx, hstage Xs hf] using hc
    · intro member rhs scheme hri hsi Ys hy
      rw [List.getElem?_map] at hsi
      obtain ⟨spec, hs0, heq⟩ := Option.map_eq_some_iff.mp hsi
      cases spec with
      | mono ty => cases heq
      | poly scheme0 =>
        cases heq
        have hy0 : FreshNames L scheme0.paramCount Ys :=
          ⟨hy.length, hy.nodup, fun y hy' hl => hy.avoid y hy' (by simp only [L', List.mem_append]; tauto)⟩
        have hc := ihPoly member rhs scheme0 hri hs0 Ys hy0 ((recCompletedSchemes specs prefixes G) ++ env') (by
          apply Expr.ForallOuter.prepend_env
          simpa only [InferInput.erase_openTyVars, recCompletedSchemes, List.length_mapIdx, Nat.zero_add, ← hw.length, List.length_map] using
            hag.1 rhs.erase (mem_eraseBindings_local (List.mem_of_getElem? hri)))
        simpa only [recBodyCtx, hcompleted] using hc
    · have hc := ihBody ((recCompletedSchemes specs prefixes G) ++ env') (by
        apply Expr.ForallOuter.prepend_env
        simpa only [recCompletedSchemes, List.length_mapIdx, Nat.zero_add, ← hw.length, List.length_map] using hag.2)
      simpa only [recBodyCtx, hcompleted] using hc
  | @named name count scrutTy ctor args fields K ctx body resultTy hspec _ ih =>
    rename_i env' hag
    refine .named hspec (ih _ ?_)
    apply Expr.ForallOuter.prepend_env
    have hlen : fields.length = count := hspec.fields.length_eq.symm.trans hspec.bind_count.symm
    simpa only [List.length_map, Nat.zero_add, MatchPattern.bindCount, hlen] using hag
  | wildcard _ ih =>
    rename_i env' hag
    exact .wildcard (ih env' hag)

private def inputSchemeHybrid (input : InferInput) (old new : List PolyTy) : List PolyTy :=
  old.mapIdx fun member oldScheme =>
    if member ∈ input.erase.recGroupRefs old.length 0 then oldScheme else new[member]?.getD oldScheme

private theorem inputSchemeHybrid_getElem {input : InferInput} {old new : List PolyTy}
    (member : Nat) (hold : member < old.length) (hnew : member < new.length) :
    (inputSchemeHybrid input old new)[member]'(by simpa [inputSchemeHybrid] using hold) =
      if member ∈ input.erase.recGroupRefs old.length 0 then old[member]'hold else new[member]'hnew := by
  simp only [inputSchemeHybrid, List.getElem_mapIdx]
  split
  · rfl
  · rw [List.getElem?_eq_getElem hnew, Option.getD_some]

 theorem InputTyping.weaken_recGroupRefs {Q : List Nat} {ctx : Ctx} {input : InferInput} {ty : Ty}
    {old new : List PolyTy} (hlen : old.length = new.length)
    (hgen : ∀ member (hold : member < old.length) (hnew : member < new.length),
      member ∈ input.erase.recGroupRefs old.length 0 →
      (new[member]'hnew).Generalizes (old[member]'hold))
    (hty : InputTyping Q ⟨old ++ ctx.env, ctx.ctors⟩ input ty) :
    InputTyping Q ⟨new ++ ctx.env, ctx.ctors⟩ input ty := by
  let hybrid := inputSchemeHybrid input old new
  have hlenHybrid : hybrid.length = old.length := by simp [hybrid, inputSchemeHybrid]
  have htyHybrid : InputTyping Q ⟨hybrid ++ ctx.env, ctx.ctors⟩ input ty := by
    apply hty.env_agreement
    apply Expr.ForallOuter.of_recGroupRefs_with_outer (n := old.length)
    · intro member href
      by_cases hmember : member < old.length
      · rw [List.getElem?_append_left (by simpa [hlenHybrid] using hmember),
          List.getElem?_append_left hmember]
        have hnew : member < new.length := by omega
        rw [List.getElem?_eq_getElem (by simpa [hlenHybrid] using hmember),
          inputSchemeHybrid_getElem member hmember hnew, if_pos href,
          List.getElem?_eq_getElem hmember]
      · have hmember' : old.length ≤ member := by omega
        rw [List.getElem?_append_right (by simpa [hlenHybrid] using hmember'),
          List.getElem?_append_right hmember']
        simp only [hlenHybrid]
    · intro member hmember
      rw [List.getElem?_append_right (by simpa [hlenHybrid] using hmember),
        List.getElem?_append_right hmember]
      simp only [hlenHybrid]
  apply InputTyping.weaken_schemes (Ms := hybrid) (Ms' := new) ?_ htyHybrid
  apply (List.forall₂_iff_get).mpr
  refine ⟨by omega, ?_⟩
  intro member hnew hhybrid
  change new[member].Generalizes (inputSchemeHybrid input old new)[member]
  rw [inputSchemeHybrid_getElem member (by omega) hnew]
  split
  · exact hgen member (by omega) hnew (by assumption)
  · exact PolyTy.Generalizes.refl new[member]

end

/-! ## RecSound -/

section

/-- More-general environment schemes preserve an annotated cofinite RHS check. -/
theorem GeneralisesTo.weaken_annotated {ctx : Ctx} {rhs : Expr} {scheme : PolyTy}
    {avoid : List Nat} {env' : Env} (hwf : scheme.WF)
    (h : GeneralisesTo TypeOfHM ctx (some scheme) rhs scheme avoid)
    (henv : List.Forall₂ PolyTy.Generalizes env' ctx.env) :
    ∃ avoid', GeneralisesTo TypeOfHM { ctx with env := env' } (some scheme) rhs scheme avoid' := by
  have hlet : TypeOfHM ctx (.letIn (some scheme) rhs (.primLit .unit)) (.prim .unit) :=
    .letIn hwf (fun _ heq => Option.some.inj heq) h rfl .primLitUnit
  have hweaken : TypeOfHM { ctx with env := env' } (.letIn (some scheme) rhs (.primLit .unit)) (.prim .unit) := by
    have old : TypeOfHM ⟨ctx.env ++ [], ctx.ctors⟩ (.letIn (some scheme) rhs (.primLit .unit)) (.prim .unit) := by
      simpa only [List.append_nil] using hlet
    simpa only [List.append_nil] using TypeOfHM.weaken_schemes (env := []) henv old
  cases hweaken with
  | letIn _ hpins hgen _ _ =>
    have heq := hpins _ rfl
    subst heq
    exact ⟨_, hgen⟩

/-- Closing a selected monotype can only increase the available instances.
The written prefix and pool need no freshness assumptions for this direction. -/
theorem RecState.exportComponent_entries_generalize {state : RecState}
    {outputs : List (Option Expr)} {facts : List RecFacts} {pool : List Nat}
    (hlen : state.exports.length = state.specs.length)
    (hlc : ∀ spec ∈ state.specs, spec.LC)
    (hclosed : ∀ i ∈ members, state.exports[i]? = some none)
    (hmono : ∀ i ∈ members, ∃ ty, state.specs[i]? = some (.mono ty)) :
    List.Forall₂ PolyTy.Generalizes
      (state.exportComponent members written pool outputs facts).entries state.entries := by
  apply List.forall₂_iff_zip.mpr
  constructor
  · rw [RecState.entries_length _ (by simpa only [RecState.exportComponent, List.length_mapIdx] using hlen),
      RecState.entries_length _ hlen]
    rfl
  · intro newer older hpair
    obtain ⟨i, hget⟩ := List.mem_iff_getElem?.mp hpair
    obtain ⟨hnew, hold⟩ := List.getElem?_zip_eq_some.mp hget
    rw [RecState.entries, List.getElem?_map] at hold
    obtain ⟨⟨spec, exported⟩, hzip, heqOld⟩ := Option.map_eq_some_iff.mp hold
    obtain ⟨hspec, hexport⟩ := List.getElem?_zip_eq_some.mp hzip
    by_cases hi : i ∈ members
    · obtain ⟨ty, hty⟩ := hmono i hi
      have hspecEq : spec = .mono ty := Option.some.inj (hspec.symm.trans hty)
      subst spec
      have he : exported = none := Option.some.inj (hexport.symm.trans (hclosed i hi))
      subst exported
      have hnewExport : (state.exportComponent members written pool outputs facts).exports[i]? =
          some (some (recScheme (written[i]?.getD []) pool ty)) := by
        simp only [RecState.exportComponent, List.getElem?_mapIdx, hclosed i hi, Option.map_some,
          if_pos hi, hty]
        rfl
      have hnewEntry : (state.exportComponent members written pool outputs facts).entries[i]? =
          some (recScheme (written[i]?.getD []) pool ty) := by
        have hz : ((state.exportComponent members written pool outputs facts).specs.zip
            (state.exportComponent members written pool outputs facts).exports)[i]? =
            some (.mono ty, some (recScheme (written[i]?.getD []) pool ty)) :=
          List.getElem?_zip_eq_some.mpr ⟨hspec, hnewExport⟩
        rw [RecState.entries, List.getElem?_map, hz]
        rfl
      have heqNew : newer = recScheme (written[i]?.getD []) pool ty := Option.some.inj (hnew.symm.trans hnewEntry)
      change PolyTy.mkTrivial ty = older at heqOld
      rw [heqNew, ← heqOld]
      exact recScheme_generalizes_mono (hlc _ (List.mem_of_getElem? hspec))
    · have hnewExport : (state.exportComponent members written pool outputs facts).exports[i]? = some exported := by
        simp only [RecState.exportComponent, List.getElem?_mapIdx, hexport, Option.map_some, if_neg hi]
      have hnewEntry : (state.exportComponent members written pool outputs facts).entries[i]? = some older := by
        have hz : ((state.exportComponent members written pool outputs facts).specs.zip
            (state.exportComponent members written pool outputs facts).exports)[i]? = some (spec, exported) :=
          List.getElem?_zip_eq_some.mpr ⟨hspec, hnewExport⟩
        rw [RecState.entries, List.getElem?_map, hz]
        exact congrArg some heqOld
      have heqNew : newer = older := Option.some.inj (hnew.symm.trans hnewEntry)
      rw [heqNew]
      exact PolyTy.Generalizes.refl older


/-- Completed RHSs are stored under their exact exported scheme and the
current full recursive environment. Metadata is intentionally absent. -/
def RecState.SourceTyped (ctx : Ctx) (state : RecState) : Prop :=
  ∀ (i : Nat) (scheme : PolyTy) (output : Expr),
    state.exports[i]? = some (some scheme) → state.outputs[i]? = some (some output) →
    scheme.WF ∧ ∃ L, GeneralisesTo TypeOfHM (state.rhsCtx ctx) (some scheme) output scheme L

 theorem RecState.SourceTyped.init : (RecState.init base anns).SourceTyped ctx := by
  intro i scheme output _ ho
  simp only [RecState.init, List.getElem?_map] at ho
  cases h : anns[i]? <;> simp [h] at ho

 theorem RecState.SourceTyped.onSubst {state : RecState} {ctx : Ctx}
    (h : state.SourceTyped ctx) (S : Subst) (hlc : ∀ p ∈ S, p.2.IsLC) :
    (state.onSubst S).SourceTyped (S.onCtx ctx) := by
  intro i scheme output hs ho
  simp only [RecState.onSubst, List.getElem?_map] at hs ho
  obtain ⟨oldScheme, hscheme, heqScheme⟩ := Option.map_eq_some_iff.mp hs
  obtain ⟨sigma, hsigma, heq⟩ := Option.map_eq_some_iff.mp heqScheme
  cases heq
  obtain ⟨oldOutput, houtput, heqOutput⟩ := Option.map_eq_some_iff.mp ho
  obtain ⟨rhs, hrhs, heq⟩ := Option.map_eq_some_iff.mp heqOutput
  cases heq
  obtain ⟨hwf, L, hgen⟩ := h i sigma rhs (hsigma ▸ hscheme) (hrhs ▸ houtput)
  refine ⟨Subst.onPolyTy_wf hlc hwf, ?_⟩
  simpa only [RecState.rhsCtx_onSubst] using hgen.onSubst_annotated hwf S hlc

 theorem RecState.mem_entries_of_export {state : RecState} {i : Nat} {scheme : PolyTy}
    (hlen : state.exports.length = state.specs.length)
    (hs : state.exports[i]? = some (some scheme)) : scheme ∈ state.entries := by
  have hi : i < state.specs.length := by rw [← hlen]; exact (List.getElem?_eq_some_iff.mp hs).1
  have hz : (state.specs.zip state.exports)[i]? = some (state.specs[i]'hi, some scheme) :=
    List.getElem?_zip_eq_some.mpr ⟨List.getElem?_eq_getElem hi, hs⟩
  apply List.mem_of_getElem? (i := i)
  rw [RecState.entries, List.getElem?_map, hz]
  rfl

 theorem RecState.SourceTyped.setSigned {state : RecState} {ctx : Ctx}
    {member : Nat} {names : List Nat} {scheme : PolyTy} {output : Expr} {facts : RecFacts}
    (h : state.SourceTyped ctx) (hexport : state.exports[member]? = some (some scheme))
    (houtput : member < state.outputs.length) (hwf : scheme.WF)
    (hlen : names.length = scheme.paramCount) (hnd : names.Nodup)
    (hctx : ∀ v ∈ names, v ∉ (state.rhsCtx ctx).env.freeVars)
    (hscheme : ∀ v ∈ names, v ∉ scheme.body.freeVars)
    (htyped : TypeOfHM (state.rhsCtx ctx) output (scheme.openVars names)) :
    (state.setSigned member names output facts).SourceTyped ctx := by
  have hgen := htyped.generaliseAnnotated hnd hctx
  have heq : (⟨names.length, Ty.closeOver names (scheme.openVars names)⟩ : PolyTy) = scheme := by
    cases scheme with
    | mk n body =>
      simp only [PolyTy.openVars] at *
      rw [Ty.closeOver_openVars_self hnd (by simpa only [hlen] using hwf) hscheme]
      simp only [PolyTy.mk.injEq]
      exact ⟨hlen, True.intro⟩
  rw [heq] at hgen
  intro i sigma rhs hs ho
  by_cases hi : member = i
  · subst i
    have he : sigma = scheme := Option.some.inj (Option.some.inj (hs.symm.trans hexport))
    subst sigma
    rw [RecState.setSigned, List.getElem?_set_self houtput] at ho
    cases Option.some.inj (Option.some.inj ho)
    exact ⟨hwf, names, hgen⟩
  · exact h i sigma rhs hs (by simpa only [RecState.setSigned, List.getElem?_set_ne hi] using ho)

 theorem RecState.entries_eq_of_exports {state : RecState} {schemes : List PolyTy}
    (hspecs : state.specs.length = state.exports.length)
    (hexports : state.exports = schemes.map some) : state.entries = schemes := by
  have hlen : state.entries.length = schemes.length := by
    rw [state.entries_length hspecs.symm, hspecs, hexports, List.length_map]
  apply List.ext_getElem?
  intro i
  cases hs : schemes[i]? with
  | none =>
      have hi : schemes.length ≤ i := List.getElem?_eq_none_iff.mp hs
      exact List.getElem?_eq_none_iff.mpr (hlen ▸ hi)
  | some scheme =>
      have hi : i < state.specs.length := by
        have := (List.getElem?_eq_some_iff.mp hs).1
        simpa only [hspecs, hexports, List.length_map] using this
      have hspec := List.getElem?_eq_getElem hi
      have he : state.exports[i]? = some (some scheme) := by
        rw [hexports, List.getElem?_map, hs]; rfl
      have hz : (state.specs.zip state.exports)[i]? = some (state.specs[i]'hi, some scheme) :=
        List.getElem?_zip_eq_some.mpr ⟨hspec, he⟩
      rw [RecState.entries, List.getElem?_map, hz]
      rfl

private theorem collect_annotated_avoids {ctx : Ctx} (pairs : List (Expr × PolyTy))
    (h : ∀ pair ∈ pairs, ∃ L,
      GeneralisesTo TypeOfHM ctx (some pair.2) pair.1 pair.2 L) :
    ∃ L, ∀ pair ∈ pairs, GeneralisesTo TypeOfHM ctx (some pair.2) pair.1 pair.2 L := by
  induction pairs with
  | nil => exact ⟨[], fun _ hm => by cases hm⟩
  | cons pair rest ih =>
    obtain ⟨Lhead, hh⟩ := h pair List.mem_cons_self
    obtain ⟨Ltail, ht⟩ := ih (fun p hp => h p (List.mem_cons_of_mem _ hp))
    refine ⟨Lhead ++ Ltail, ?_⟩
    intro p hp Xs hXs
    rcases List.mem_cons.mp hp with rfl | hp
    · exact hh Xs ⟨hXs.length, hXs.nodup,
        fun x hx hc => hXs.avoid x hx (List.mem_append_left _ hc)⟩
    · exact ht p hp Xs ⟨hXs.length, hXs.nodup,
        fun x hx hc => hXs.avoid x hx (List.mem_append_right _ hc)⟩

/-- Rebuild a completed group using its independently checked exported schemes. -/
 theorem RecState.SourceTyped.letRec {state : RecState} {schemes : List PolyTy} {outputs : List Expr}
    (h : state.SourceTyped ctx) (hexports : state.exports = schemes.map some)
    (houtputs : state.outputs = outputs.map some)
    (hspecs : state.specs.length = state.exports.length)
    (hlength : state.outputs.length = state.exports.length)
    (hbody : TypeOfHM (state.rhsCtx ctx) body ty) :
    TypeOfHM ctx (.letRec (schemes.map some) outputs body) ty := by
  have hlen : outputs.length = schemes.length := by
    simpa only [hexports, houtputs, List.length_map] using hlength
  have hpairs : ∀ p ∈ outputs.zip schemes, p.2.WF ∧ ∃ L,
      GeneralisesTo TypeOfHM (state.rhsCtx ctx) (some p.2) p.1 p.2 L := by
    intro p hp
    obtain ⟨i, hget⟩ := List.mem_iff_getElem?.mp hp
    obtain ⟨ho, hs⟩ := List.getElem?_zip_eq_some.mp hget
    apply h i p.2 p.1
    · rw [hexports, List.getElem?_map, hs]; rfl
    · rw [houtputs, List.getElem?_map, ho]; rfl
  have hwf : ∀ scheme ∈ schemes, scheme.WF := by
    intro scheme hm
    obtain ⟨i, hs⟩ := List.mem_iff_getElem?.mp hm
    have hi : i < outputs.length := by rw [hlen]; exact (List.getElem?_eq_some_iff.mp hs).1
    have ho := List.getElem?_eq_getElem hi
    exact (hpairs (outputs[i]'hi, scheme)
      (List.mem_iff_getElem?.mpr ⟨i, List.getElem?_zip_eq_some.mpr ⟨ho, hs⟩⟩)).1
  obtain ⟨L, hcofinite⟩ := collect_annotated_avoids (outputs.zip schemes) (fun p hp => (hpairs p hp).2)
  have hvalid : RecGroups.ValidResidualGroups (schemes.map some) outputs [] := by
    refine ⟨by simpa only [List.length_map] using hlen.symm, by simp, by simp, by simp, ?_, ?_⟩
    · intro i _
      simp only [List.flatten_nil, List.not_mem_nil, RecGroups.UnsignedAt, List.getElem?_map]
      cases schemes[i]? <;> simp
    · intro stage dependencyStage component dependencyComponent source target rhs hget
      simp at hget
  have hspecwf : RecSpecs.WF (schemes.map some) outputs (schemes.map RecSpec.poly) [] := by
    refine ⟨?_, by simpa only [List.length_map] using hlen, List.nodup_nil, ?_, ?_⟩
    · simp only [List.map_map, Function.comp_def, RecSpec.ann]
    · intro t ht
      obtain ⟨scheme, _, heq⟩ := List.mem_map.mp ht
      cases heq
    · intro scheme hm
      obtain ⟨original, ho, heq⟩ := List.mem_map.mp hm
      have he : original = scheme := RecSpec.poly.inj heq
      subst scheme
      exact hwf original ho
  have hid : schemes.map (fun x => x) = schemes := List.map_id schemes
  refine TypeOfHM.letRec (specs := schemes.map RecSpec.poly) (G := []) (groups := []) (L := L)
    hvalid hspecwf ?_ ?_ ?_ hbody
  · intro stage component hget
    simp at hget
  · intro pair hp scheme heq Ys hYs
    rcases pair with ⟨rhs, spec⟩
    change spec = .poly scheme at heq
    subst spec
    obtain ⟨i, hget⟩ := List.mem_iff_getElem?.mp hp
    obtain ⟨ho, hs⟩ := List.getElem?_zip_eq_some.mp hget
    rw [List.getElem?_map] at hs
    obtain ⟨original, horiginal, heq⟩ := Option.map_eq_some_iff.mp hs
    have he : original = scheme := RecSpec.poly.inj heq
    subst scheme
    have hgen := hcofinite (rhs, original)
      (List.mem_iff_getElem?.mpr ⟨i, List.getElem?_zip_eq_some.mpr ⟨ho, horiginal⟩⟩) Ys hYs
    simpa only [GeneralisesTo, Expr.openBoundTyVars, RecSpecs.bodyCtx, List.map_map,
      Function.comp_def, RecSpec.bodyScheme, hid, RecState.rhsCtx,
      RecState.entries_eq_of_exports hspecs hexports] using hgen
  · simp only [RecSpecs.bodyCtx, List.map_map, Function.comp_def, RecSpec.bodyScheme, hid,
      RecState.rhsCtx, RecState.entries_eq_of_exports hspecs hexports]


 theorem RecState.SourceTyped.exportComponent {state : RecState}
    {outputs : List (Option Expr)} {facts : List RecFacts} {pool : List Nat}
    (h : state.SourceTyped ctx)
    (hexports : state.exports.length = state.outputs.length)
    (hspecs : state.outputs.length = state.specs.length)
    (hlc : ∀ spec ∈ state.specs, spec.LC)
    (hclosed : ∀ i ∈ members, state.exports[i]? = some none)
    (hmono : ∀ i ∈ members, ∃ ty, state.specs[i]? = some (.mono ty))
    (hnd : ∀ i ∈ members, (written[i]?.getD []).Nodup)
    (hsub : ∀ i ∈ members, ∀ v ∈ written[i]?.getD [], v ∈ pool)
    (hpool : pool.Nodup)
    (hfresh : ∀ v ∈ pool, v ∉ ((state.exportComponent members written pool outputs facts).rhsCtx ctx).env.freeVars)
    (htyped : ∀ (i : Nat) (ty : Ty) (output : Expr), state.specs[i]? = some (.mono ty) →
      outputs[i]? = some (some output) → TypeOfHM (state.rhsCtx ctx) output ty) :
    (state.exportComponent members written pool outputs facts).SourceTyped ctx := by
  have hgeneral := RecState.exportComponent_entries_generalize
    (written := written) (outputs := outputs) (facts := facts) (pool := pool)
    (hexports.trans hspecs) hlc hclosed hmono
  intro i scheme output hscheme houtput
  rw [RecState.exportComponent, List.getElem?_mapIdx] at hscheme houtput
  obtain ⟨oldScheme, hOldScheme, hNewScheme⟩ := Option.map_eq_some_iff.mp hscheme
  obtain ⟨oldOutput, hOldOutput, hNewOutput⟩ := Option.map_eq_some_iff.mp houtput
  by_cases hi : i ∈ members
  · obtain ⟨ty, hty⟩ := hmono i hi
    simp only [if_pos hi] at hNewScheme hNewOutput
    have heq : recScheme (written[i]?.getD []) pool ty = scheme := by
      simpa [hty] using hNewScheme
    subst scheme
    rw [hty] at hNewOutput
    obtain ⟨spec, hspec, hbind⟩ := Option.bind_eq_some_iff.mp hNewOutput
    cases Option.some.inj hspec
    obtain ⟨target, htarget, hbind⟩ := Option.bind_eq_some_iff.mp hbind
    cases Option.some.inj htarget
    obtain ⟨rhs, hrhs, hclose⟩ := Option.bind_eq_some_iff.mp hbind
    obtain ⟨inner, hinner, hinnerEq⟩ := Option.bind_eq_some_iff.mp hrhs
    cases hinnerEq
    cases Option.some.inj hclose
    have hchecked := htyped i ty rhs hty hinner
    have hweaken : TypeOfHM ((state.exportComponent members written pool outputs facts).rhsCtx ctx) rhs ty :=
      TypeOfHM.weaken_schemes hgeneral hchecked
    have hnames : (recNames (written[i]?.getD []) pool ty).Nodup := recNames_nodup (hnd i hi) hpool
    have havoid : ∀ v ∈ recNames (written[i]?.getD []) pool ty,
        v ∉ ((state.exportComponent members written pool outputs facts).rhsCtx ctx).env.freeVars := by
      intro v hv
      apply hfresh v
      rcases mem_recNames.mp hv with hv | ⟨hv, _, _⟩
      · exact hsub i hi v hv
      · exact hv
    exact ⟨recScheme_wf (hlc _ (List.mem_of_getElem? hty)), _, hweaken.generaliseAnnotated hnames havoid⟩
  · simp only [if_neg hi] at hNewScheme hNewOutput
    obtain ⟨hwf, L, hgen⟩ := h i scheme output (hNewScheme ▸ hOldScheme) (hNewOutput ▸ hOldOutput)
    refine ⟨hwf, ?_⟩
    have houter : List.Forall₂ PolyTy.Generalizes ctx.env ctx.env := by
      induction ctx.env with
      | nil => exact .nil
      | cons scheme rest ih => exact .cons (PolyTy.Generalizes.refl scheme) ih
    have happend : ∀ {new old : List PolyTy}, List.Forall₂ PolyTy.Generalizes new old →
        List.Forall₂ PolyTy.Generalizes (new ++ ctx.env) (old ++ ctx.env) := by
      intro new old hrel
      induction hrel with
      | nil => exact houter
      | cons head tail ih => exact .cons head ih
    have henv := happend hgeneral
    exact GeneralisesTo.weaken_annotated (ctx := state.rhsCtx ctx) hwf hgen henv


 theorem _root_.InferRecComponent.sourceSound_of_infer
    (h : InferRecComponent K F members index frontier ctx bindings specs next S outputs facts)
    (hInfer : ∀ {κ F' Ψ c e Ψ' T output ty}, e.size ≤ sizeBindings bindings →
      Infer κ F' Ψ c e Ψ' T output ty → CtxWF c → TypeOfHM (T.onCtx c) output ty)
    (hLC : ∀ {κ F' Ψ c e Ψ' T output ty}, e.size ≤ sizeBindings bindings →
      Infer κ F' Ψ c e Ψ' T output ty → CtxWF c → ty.IsLC ∧ ∀ p ∈ T, p.2.IsLC)
    (hctx : CtxWF ctx) (hspec : ∀ spec ∈ specs, spec.LC) :
    ∀ (j : Nat) (target : Ty) (output : Expr), specs[j]? = some (RecSpec.mono target) → outputs[j]? = some (some output) →
      TypeOfHM (S.onCtx ctx) output (S.onTy target) := by
  match h with
  | .nil => intro j target output ht; simp at ht
  | .skipMono _ hr | .skipPoly hr =>
      intro j target output ht ho
      cases j with
      | zero => cases ho
      | succ j =>
          exact hr.sourceSound_of_infer
            (fun he h => hInfer (by simp only [sizeBindings]; omega) h)
            (fun he h => hLC (by simp only [sizeBindings]; omega) h)
            hctx (fun spec hm => hspec spec (List.mem_cons_of_mem _ hm)) j target output ht ho
  | .consSelected _ hi hu hr =>
      expose_names
      obtain ⟨hiTy, hiS⟩ := hLC (by simp only [sizeBindings]; omega) hi hctx
      have huS := hu.unifies.lc hiTy (Subst.onTy_lc hiS (hspec _ List.mem_cons_self))
      have hS12 : ∀ p ∈ s1 ++ s2, p.2.IsLC := fun p hp => (List.mem_append.mp hp).elim (hiS p) (huS p)
      have hrCtx := Subst.onCtx_wf huS (Subst.onCtx_wf hiS hctx)
      have hrSpec : ∀ spec ∈ specs_1.map (RecSpec.onSubstSource (s1 ++ s2)), spec.LC := by
        intro spec hm
        obtain ⟨old, hold, rfl⟩ := List.mem_map.mp hm
        exact RecSpec.lc_onSubstSource hS12 (hspec old (List.mem_cons_of_mem _ hold))
      have hrLC := hr.lc_of_infer
        (fun he h => hLC (by simp only [sizeBindings_map_substTyFvars] at he; simp only [sizeBindings]; omega) h)
        hrCtx hrSpec
      intro j target output ht ho
      cases j with
      | zero =>
        cases Option.some.inj ht
        cases Option.some.inj (Option.some.inj ho)
        have htyped := TypeOfHM.onSubst (s2 ++ s3)
          (fun p hp => (List.mem_append.mp hp).elim (huS p) (hrLC p))
          (hInfer (by simp only [sizeBindings]; omega) hi hctx)
        have heq := hu.unifies.unifies
        change s2.onTy ty = s2.onTy (s1.onTy expected) at heq
        simpa only [Subst.onCtx_append, Subst.onTy_append, heq] using htyped
      | succ j =>
        simp only [List.getElem?_cons_succ] at ht ho
        have htail := hr.sourceSound_of_infer
          (fun he h => hInfer (by simp only [sizeBindings_map_substTyFvars] at he; simp only [sizeBindings]; omega) h)
          (fun he h => hLC (by simp only [sizeBindings_map_substTyFvars] at he; simp only [sizeBindings]; omega) h)
          hrCtx hrSpec j ((s1 ++ s2).onTy target) output
          (by simp only [List.getElem?_map, ht, Option.map_some, RecSpec.onSubstSource]) ho
        simpa only [Subst.onCtx_append, Subst.onTy_append] using htail
 termination_by structural h

 theorem _root_.InferRecSigned.sourceSound_of_infer
    (h : InferRecSigned K F index frontier ctx anns bindings state next S final)
    (hInfer : ∀ {κ F' Ψ c e Ψ' T output ty}, e.size ≤ sizeBindings bindings →
      Infer κ F' Ψ c e Ψ' T output ty → CtxWF c → TypeOfHM (T.onCtx c) output ty)
    (hctx : CtxWF ctx) (hstate : state.LC) (htyped : state.SourceTyped ctx)
    (hlen : state.exports.length = state.specs.length)
    (hout : state.outputs.length = state.exports.length)
    (hcontracts : ∀ (j : Nat) (scheme : PolyTy), anns[j]? = some (.complete scheme) →
      state.exports[index + j]? = some (some scheme)) :
    final.SourceTyped (S.onCtx ctx) := by
  match h with
  | .nil => simpa only [Subst.onCtx_nil] using htyped
  | .skip _ hr =>
    apply hr.sourceSound_of_infer (fun he hi => hInfer (by simp only [sizeBindings]; omega) hi)
      hctx hstate htyped hlen hout
    intro j scheme hs
    have hh := hcontracts (j + 1) scheme (by simpa only [List.getElem?_cons_succ] using hs)
    simpa only [Nat.add_assoc, Nat.add_comm 1 j] using hh
  | .cons hwf _ hi hu hescape hr =>
    expose_names
    have hiCtx := hstate.rhsCtx hctx
    obtain ⟨htLC, hS1⟩ := hi.lc hiCtx
    have hσLC := Subst.onPolyTy_wf hS1 hwf
    have hS2 := hu.unifies.lc htLC (PolyTy.openVars_isLC hσLC (by simp [Subst.onPolyTy]))
    have hS : ∀ p ∈ s1 ++ s2, p.2.IsLC := fun p hp => (List.mem_append.mp hp).elim (hS1 p) (hS2 p)
    have hready := (htyped.onSubst (s1 ++ s2) hS)
    have hex := hcontracts 0 scheme rfl
    simp only [Nat.add_zero] at hex
    have hex' : (state.onSubst (s1 ++ s2)).exports[index]? = some (some ((s1 ++ s2).onPolyTy scheme)) := by
      simp only [RecState.onSubst, List.getElem?_map, hex, Option.map_some]
    have hlen' : (state.onSubst (s1 ++ s2)).exports.length = (state.onSubst (s1 ++ s2)).specs.length := by
      simpa only [RecState.onSubst, List.length_map] using hlen
    have hmember := (state.onSubst (s1 ++ s2)).mem_entries_of_export hlen' hex'
    have hrhs := TypeOfHM.onSubst s2 hS2
      (hInfer (by simp only [InferInput.size_openTyVars, sizeBindings]; omega) hi hiCtx)
    have heq := hu.unifies.unifies
    have hdom : ∀ p ∈ s2, p.1 ∉ freshVars frontier scheme.paramCount :=
      fun p hp hm => hu.dom_avoids p hp (List.mem_append_right _ hm)
    change s2.onTy ty = s2.onTy (Ty.openVars (freshVars frontier scheme.paramCount) (s1.onPolyTy scheme).body) at heq
    rw [Subst.onTy_openVars hS2 hdom] at heq
    rw [heq] at hrhs
    have hctxFresh : ∀ v ∈ freshVars frontier scheme.paramCount,
        v ∉ ((state.onSubst (s1 ++ s2)).rhsCtx ((s1 ++ s2).onCtx ctx)).env.freeVars :=
      fun v hv hm => hescape v hv (List.mem_append_left _ hm)
    have hschemeFresh : ∀ v ∈ freshVars frontier scheme.paramCount,
        v ∉ ((s1 ++ s2).onPolyTy scheme).body.freeVars := by
      intro v hv hm
      exact hctxFresh v hv (Env.mem_freeVars_iff.mpr ⟨_, List.mem_append_left _ hmember, hm⟩)
    have houtput : index < (state.onSubst (s1 ++ s2)).outputs.length := by
      have hi := (List.getElem?_eq_some_iff.mp hex').1
      simpa only [RecState.onSubst, List.length_map, hout] using hi
    have hclosed := hready.setSigned (facts := bodyFacts.onSubst s2) hex' houtput (Subst.onPolyTy_wf hS hwf)
      (by simp [Subst.onPolyTy]) (freshVars_nodup) hctxFresh hschemeFresh
      (by
        rw [RecState.rhsCtx_onSubst]
        change TypeOfHM ((s1 ++ s2).onCtx (state.rhsCtx ctx)) (output.substTyFvars s2)
          (((s1 ++ s2).onPolyTy scheme).openVars (freshVars frontier scheme.paramCount))
        simpa only [Subst.onCtx_append, Subst.onPolyTy_append, PolyTy.openVars, Subst.onPolyTy, Subst.onTy_append] using hrhs)
    have hfinal := hr.sourceSound_of_infer
      (fun he hj => hInfer (by simp only [sizeBindings_map_substTyFvars] at he; simp only [sizeBindings]; omega) hj)
      (Subst.onCtx_wf hS hctx) ((hstate.onSubst hS).setSigned) hclosed
      (by simpa only [RecState.setSigned, RecState.onSubst, List.length_map] using hlen)
      (by simpa only [RecState.setSigned, RecState.onSubst, List.length_map, List.length_set] using hout)
      (by
        intro j sigma hs
        obtain ⟨ann, ha, heq⟩ := Option.map_eq_some_iff.mp (by simpa only [List.getElem?_map] using hs)
        cases ann with
        | absent | template | partialForall => cases heq
        | complete original =>
          cases BindingAnn.complete.inj heq
          have hh := hcontracts (j + 1) original (by simpa only [List.getElem?_cons_succ] using ha)
          simp only [RecState.setSigned, RecState.onSubst, List.getElem?_map, Nat.add_assoc,
            Nat.add_comm 1 j, hh, Option.map_some, Subst.onPolyTy, Subst.onTy])
    simpa only [Subst.onCtx_append] using hfinal
 termination_by structural h


 theorem RecState.Frame.complete_export {state : RecState} {i : Nat} {scheme : PolyTy}
    (h : state.Frame base K F ctx anns done) (ha : anns[i]? = some (.complete scheme)) :
    state.exports[i]? = some (some scheme) := by
  have hi : i < state.specs.length := by rw [h.specs_length]; exact (List.getElem?_eq_some_iff.mp ha).1
  have hs := List.getElem?_eq_getElem hi
  have hm := congrArg (fun xs : List (Option PolyTy) => xs[i]?) h.modes
  dsimp only at hm
  rw [List.getElem?_map, hs, Option.map_some, List.getElem?_map, ha, Option.map_some] at hm
  cases he : state.specs[i]'hi with
  | mono ty => simp only [he, RecSpec.ann, BindingAnn.recModeAnn] at hm; cases hm
  | poly sigma =>
    simp only [he, RecSpec.ann, BindingAnn.recModeAnn] at hm
    have heq : sigma = scheme := Option.some.inj (Option.some.inj hm)
    subst sigma
    exact h.poly i scheme (he ▸ hs)

 theorem RecState.Frame.mono_at_unsigned {state : RecState} {i : Nat}
    (h : state.Frame base K F ctx anns done)
    (ha : (anns.map BindingAnn.recModeAnn)[i]? = some none) :
    ∃ ty, state.specs[i]? = some (.mono ty) := by
  have hi : i < state.specs.length := by
    rw [h.specs_length]
    simpa only [List.length_map] using (List.getElem?_eq_some_iff.mp ha).1
  have hs := List.getElem?_eq_getElem hi
  have hm := congrArg (fun xs : List (Option PolyTy) => xs[i]?) h.modes
  dsimp only at hm
  rw [List.getElem?_map, hs, Option.map_some, ha] at hm
  cases he : state.specs[i]'hi with
  | mono ty => exact ⟨ty, he ▸ hs⟩
  | poly scheme => simp only [he, RecSpec.ann] at hm; cases hm


private theorem RecState.Frame.entry_freeVars_subset {state : RecState} {spec : RecSpec} {scheme : PolyTy} {i : Nat}
    (h : state.Frame base K F ctx anns done) (hs : state.specs[i]? = some spec)
    (he : state.entries[i]? = some scheme) :
    ∀ v ∈ scheme.body.freeVars, v ∈ spec.freeVars := by
  rw [RecState.entries, List.getElem?_map] at he
  obtain ⟨⟨old, exported⟩, hz, hentry⟩ := Option.map_eq_some_iff.mp he
  obtain ⟨hsp, hex⟩ := List.getElem?_zip_eq_some.mp hz
  dsimp only at hsp hex
  have hsame := Option.some.inj (hsp.symm.trans hs)
  change old = spec at hsame
  subst old
  cases spec with
  | poly sigma =>
    have hh := h.poly i sigma hs
    have hh' := Option.some.inj (hex.symm.trans hh)
    subst exported
    cases hentry
    exact fun _ hv => hv
  | mono ty =>
    by_cases hd : i ∈ done
    · obtain ⟨written, _, _, _, _, hx⟩ := if_pos hd ▸ h.mono i ty hs
      have hh := Option.some.inj (hex.symm.trans hx)
      subst exported
      cases hentry
      exact fun _ hv => Ty.freeVars_closeOver_subset hv
    · have hx := if_neg hd ▸ h.mono i ty hs
      have hh := Option.some.inj (hex.symm.trans hx)
      subst exported
      cases hentry
      exact fun _ hv => hv

private theorem RecState.Frame.pending_lookup_other {state : RecState}
    (h : state.Frame base K F ctx anns done)
    (ht : state.specs[member]? = some (.mono ty)) (hm : member ∉ done)
    (hne : i ≠ member) :
    ∀ scheme, (state.rhsCtx ctx).env[i]? = some scheme → base + member ∉ scheme.body.freeVars := by
  intro scheme hlook
  by_cases hi : i < state.entries.length
  · rw [RecState.rhsCtx, List.getElem?_append_left hi] at hlook
    have hispec : i < state.specs.length := by rw [h.specs_length, ← h.entries_length]; exact hi
    have hs := List.getElem?_eq_getElem hispec
    exact fun hv => h.pending.other member ty ht hm i _ hs hne
      (h.entry_freeVars_subset hs hlook _ hv)
  · rw [RecState.rhsCtx, List.getElem?_append_right (by omega)] at hlook
    exact h.pending.env member ty ht hm scheme (List.mem_of_getElem? hlook)

private theorem RecState.Frame.pending_refs {state : RecState} {rhs : Expr}
    (h : state.Frame base K F ctx anns done)
    (ht : state.specs[member]? = some (.mono ty)) (hm : member ∉ done)
    (href : member ∉ rhs.recGroupRefs state.specs.length 0) :
    rhs.ForallOuter (fun i => ∀ M, (state.rhsCtx ctx).env[i]? = some M →
      base + member ∉ M.body.freeVars) 0 := by
  apply Expr.ForallOuter.of_recGroupRefs_with_outer (n := state.specs.length)
  · intro i hi
    exact h.pending_lookup_other ht hm (fun heq => href (heq ▸ hi))
  · intro i hi
    apply h.pending_lookup_other ht hm
    have := (List.getElem?_eq_some_iff.mp ht).1
    omega

private theorem recShapes_selected_avoid {state : RecState}
    (ha : ∀ i ty, i ∈ members → state.specs[i]? = some (.mono ty) → w ∉ ty.freeVars)
    (ho : ∀ opening ∈ openings, ∀ ty, opening.expected = some ty → w ∉ ty.freeVars) :
    ∀ shape ∈ state.shapes members openings, w ∉ shape.1.freeVars ∧
      ∀ ty, shape.2 = some ty → w ∉ ty.freeVars := by
  intro shape hs
  obtain ⟨i, him, heq⟩ := List.mem_filterMap.mp hs
  cases hspec : state.specs[i]? with
  | none => simp [hspec] at heq
  | some spec =>
    cases spec with
    | poly scheme => simp [hspec, RecSpec.monoTy?] at heq
    | mono ty =>
      cases hopen : openings[i]? with
      | none => simp [hspec, RecSpec.monoTy?, hopen] at heq
      | some opening =>
        simp [hspec, RecSpec.monoTy?, hopen] at heq
        subst shape
        exact ⟨ha i ty him hspec, ho opening (List.mem_of_getElem? hopen)⟩

theorem openRecSources_getElem? {openings : List RecOpening} {bindings : List InferInput} {i : Nat} {rhs : InferInput}
    (hlen : openings.length = bindings.length)
    (h : (openRecSources openings bindings)[i]? = some rhs) :
    ∃ old : InferInput, bindings[i]? = some old ∧ rhs = old.openTyVars ((openings[i]?).getD .empty).written := by
  induction bindings generalizing openings i with
  | nil => cases openings <;> simp_all [openRecSources]
  | cons head rest ih =>
    cases openings with
    | nil => simp at hlen
    | cons opening openings =>
      cases i with
      | zero => exact ⟨head, rfl, (Option.some.inj h).symm⟩
      | succ i =>
        obtain ⟨old, ho, heq⟩ := ih (Nat.succ.inj hlen) h
        exact ⟨old, ho, heq⟩

 theorem recStep_sourceAvoid
    {state : RecState}
    (ho : OpenRecAnns component 0 frontier anns opened openings)
    (hp : CheckRecShapes K ((state.installOpenings component openings).shapes component openings) pre)
    (hc : InferRecComponent K (substSoft pre (F ++ (openings.flatMap RecOpening.written).map Ty.fvar))
      component 0 opened (((state.installOpenings component openings).onSubst pre).rhsCtx (pre.onCtx ctx))
      ((openRecSources openings bindings).map (InferInput.substTyFvars pre))
      ((state.installOpenings component openings).onSubst pre).specs first current outputs facts)
    (hInfer : ∀ {κ F' Ψ c e Ψ' T output ty}, e.size ≤ sizeBindings bindings →
      Infer κ F' Ψ c e Ψ' T output ty →
      ∀ {w}, w < Ψ →
      e.erase.ForallOuter (fun i => ∀ M, c.env[i]? = some M → w ∉ M.body.freeVars) 0 →
      w ∉ e.rigidVars →
      (∀ p ∈ T, w ∉ p.2.freeVars) ∧ w ∉ ty.freeVars ∧ w ∉ T.map Prod.fst)
    (hw : w < frontier) (hlen : anns.length = bindings.length)
    (hanns : ∀ ann ∈ anns, w ∉ ann.rigidVars)
    (hrhs : ∀ i rhs, i ∈ component → bindings[i]? = some rhs →
      rhs.erase.ForallOuter (fun j => ∀ M, (state.rhsCtx ctx).env[j]? = some M →
        w ∉ M.body.freeVars) 0 ∧ w ∉ rhs.rigidVars)
    (htarget : ∀ i ty, i ∈ component → state.specs[i]? = some (.mono ty) → w ∉ ty.freeVars) :
    (∀ p ∈ pre ++ current, w ∉ p.2.freeVars) ∧ w ∉ (pre ++ current).map Prod.fst := by
  have hpre := hp.sourceAvoid (recShapes_selected_avoid htarget (ho.expected_avoid hw hanns))
  have hn : ∀ opening ∈ openings, w ∉ opening.written := by
    intro opening hm hw'
    have hh := ho.written_range w (List.mem_flatMap.mpr ⟨opening, hm, hw'⟩)
    omega
  have hcomponent := hc.sourceLocality_of_infer
    (fun he hi => hInfer (by simpa only [sizeBindings_map_substTyFvars, sizeBindings_openRecSources] using he) hi)
    (Nat.lt_of_lt_of_le hw ho.frontier_le)
    (by
      intro i rhs hi hget
      obtain ⟨openedRhs, hopen, rfl⟩ := Option.map_eq_some_iff.mp (by simpa only [List.getElem?_map] using hget)
      obtain ⟨old, hold, rfl⟩ := openRecSources_getElem? (ho.length.trans hlen) hopen
      have hhead := hrhs i old (by simpa using hi) hold
      have hnv : w ∉ ((openings[i]?).getD .empty).written := by
        cases hx : openings[i]? with
        | none => simp [RecOpening.empty]
        | some opening => exact hn opening (List.mem_of_getElem? hx)
      refine ⟨?_, InferInput.avoid_subst hpre.1 (fun hv => (InferInput.rigidVars_openTyVarsFrom hv).elim hhead.2 hnv)⟩
      have hctxeq : ((state.installOpenings component openings).onSubst pre).rhsCtx (pre.onCtx ctx) =
          pre.onCtx (state.rhsCtx ctx) := by
        rw [RecState.rhsCtx_onSubst]
        rfl
      rw [hctxeq]
      simpa only [InferInput.erase_substTyFvars, InferInput.erase_openTyVars] using
        Expr.ForallOuter.lookupAvoid_onSubst (S := pre) hhead.1 hpre.1)
    (by
      intro i ty hi hget
      obtain ⟨old, hold, rfl⟩ := RecSpec.mono_getElem?_map_onSubstSource hget
      exact Subst.notMemOnTy hpre.1 (htarget i old (by simpa using hi) hold))
  exact ⟨fun p hp => (List.mem_append.mp hp).elim (hpre.1 p) (hcomponent.1 p),
    by simpa only [List.map_append, List.mem_append, not_or] using And.intro hpre.2 hcomponent.2⟩

 theorem recStep_oldpool_pending_avoid
    {state : RecState}
    (ho : OpenRecAnns component 0 frontier anns opened openings)
    (hp : CheckRecShapes K ((state.installOpenings component openings).shapes component openings) pre)
    (hc : InferRecComponent K (substSoft pre (F ++ (openings.flatMap RecOpening.written).map Ty.fvar))
      component 0 opened (((state.installOpenings component openings).onSubst pre).rhsCtx (pre.onCtx ctx))
      ((openRecSources openings bindings).map (InferInput.substTyFvars pre))
      ((state.installOpenings component openings).onSubst pre).specs first current outputs facts)
    (hInfer : ∀ {κ F' Ψ c e Ψ' T output ty}, e.size ≤ sizeBindings bindings →
      Infer κ F' Ψ c e Ψ' T output ty →
      ∀ {w}, w < Ψ →
      e.erase.ForallOuter (fun i => ∀ M, c.env[i]? = some M → w ∉ M.body.freeVars) 0 →
      w ∉ e.rigidVars →
      (∀ p ∈ T, w ∉ p.2.freeVars) ∧ w ∉ ty.freeVars ∧ w ∉ T.map Prod.fst)
    (hvalid : RecGroups.ValidResidualGroups (anns.map BindingAnn.recModeAnn) (bindings.map InferInput.erase)
      (past ++ component :: rest))
    (hframe : state.Frame base K F ctx anns past.flatten)
    (hbelow : state.Below frontier) (hbase : base + bindings.length ≤ frontier)
    (hanns : ∀ ann ∈ anns, ∀ v ∈ ann.rigidVars, v ∈ K ++ softVars F)
    (hrhs : ∀ rhs ∈ bindings, ∀ v ∈ rhs.rigidVars, v ∈ K ++ softVars F) :
    (∀ g ∈ state.pool, (∀ p ∈ pre ++ current, g ∉ p.2.freeVars) ∧ g ∉ (pre ++ current).map Prod.fst) ∧
    (∀ member ty, state.specs[member]? = some (.mono ty) → member ∉ past.flatten ++ component →
      (∀ p ∈ pre ++ current, base + member ∉ p.2.freeVars) ∧ base + member ∉ (pre ++ current).map Prod.fst) := by
  have hlen : anns.length = bindings.length := by simpa only [List.length_map] using hvalid.length
  have hnot : ∀ i ∈ component, i ∉ past.flatten := by
    intro i hi hd
    have hnd : (past.flatten ++ (component ++ rest.flatten)).Nodup := by
      simpa only [List.flatten_append, List.flatten_cons] using hvalid.flatten_nodup
    exact (List.nodup_append.mp hnd).2.2 i hd i (List.mem_append_left _ hi) rfl
  constructor
  · intro g hg
    apply recStep_sourceAvoid ho hp hc hInfer (hbelow.2.2.2 g hg) hlen
    · intro ann ha hv
      exact (List.mem_append.mp (hanns ann ha g hv)).elim (hframe.pool_rigid g hg) (hframe.pool_soft g hg)
    · intro i rhs hi hget
      refine ⟨?_, ?_⟩
      · apply Expr.ForallOuter.of_recGroupRefs_with_outer (n := 0)
        · intro j hj M hm hv
          exact hframe.pool_rhsCtx g hg (Env.mem_freeVars_iff.mpr ⟨M, List.mem_of_getElem? hm, hv⟩)
        · intro j _ M hm hv
          exact hframe.pool_rhsCtx g hg (Env.mem_freeVars_iff.mpr ⟨M, List.mem_of_getElem? hm, hv⟩)
      · intro hv
        exact (List.mem_append.mp (hrhs rhs (List.mem_of_getElem? hget) g hv)).elim
          (hframe.pool_rigid g hg) (hframe.pool_soft g hg)
    · intro i ty hi hget
      rw [hframe.pending.mono i ty hget (hnot i hi)]
      simp only [Ty.freeVars, List.mem_singleton]
      exact fun heq => hframe.pool_pending i ty hget (hnot i hi) (heq ▸ hg)
  · intro member ty ht hm
    have hdone : member ∉ past.flatten := fun hd => hm (List.mem_append_left _ hd)
    have hcomp : member ∉ component := fun hc => hm (List.mem_append_right _ hc)
    have hw : base + member < frontier := by
      have hlt := (List.getElem?_eq_some_iff.mp ht).1
      rw [hframe.specs_length, hlen] at hlt
      omega
    have hrigid : base + member ∉ K := fun hh => by have := hframe.rigid_below _ hh; omega
    have hsoft := hframe.pending_soft member ty ht hdone
    apply recStep_sourceAvoid ho hp hc hInfer hw hlen
    · intro ann ha hv
      exact (List.mem_append.mp (hanns ann ha _ hv)).elim hrigid hsoft
    · intro i rhs hi hget
      refine ⟨?_, fun hv => (List.mem_append.mp (hrhs rhs (List.mem_of_getElem? hget) _ hv)).elim hrigid hsoft⟩
      apply hframe.pending_refs ht hdone
      apply hvalid.pending_no_ref hframe.modes
        (by simpa only [List.length_map] using (hframe.specs_length.trans hlen).symm) hi
        (by simp only [List.getElem?_map, hget, Option.map_some]) ht hm
    · intro i target hi hget
      exact hframe.pending.other member ty ht hdone i (.mono target) hget (fun heq => hcomp (heq ▸ hi))

theorem ResolveRecSlots.lookup
    (h : ResolveRecSlots members forbidden index slots names) :
    ∀ (j : Nat) images, slots[j]? = some images → ∃ ns, names[j]? = some ns ∧
      if index + j ∈ members then ns.map Ty.fvar = images ∧ ns.Nodup ∧
        (∀ v ∈ ns, v ∉ forbidden) else ns = [] := by
  induction h with
  | nil => intro j images hj; simp at hj
  | skip hn hr ih =>
    intro j images hj
    cases j with
    | zero =>
      cases hj
      exact ⟨[], rfl, by simp [hn]⟩
    | succ j =>
      obtain ⟨ns, hget, hh⟩ := ih j images hj
      exact ⟨ns, hget, by simpa only [Nat.succ_add, Nat.add_succ] using hh⟩
  | cons hm hb hnd hav hr ih =>
    intro j images hj
    cases j with
    | zero =>
      cases hj
      exact ⟨_, rfl, by simpa only [Nat.add_zero, hm, ↓reduceIte] using And.intro hb (And.intro hnd hav)⟩
    | succ j =>
      obtain ⟨ns, hget, hh⟩ := ih j images hj
      exact ⟨ns, hget, by simpa only [Nat.succ_add, Nat.add_succ] using hh⟩

theorem ResolveRecSlots.length (h : ResolveRecSlots members forbidden index slots names) :
    names.length = slots.length := by induction h <;> simp_all

private theorem ResolveRecSlots.all_avoid (h : ResolveRecSlots members forbidden index slots names) :
    ∀ v ∈ names.flatten, v ∉ forbidden := by
  induction h with
  | nil => simp
  | skip _ _ ih => exact ih
  | cons _ _ _ ha _ ih =>
    intro v hv
    exact (List.mem_append.mp hv).elim (ha v) (ih v)

private theorem RecState.componentPool_nodup {state : RecState}
    (h : state.pool.Nodup) : (state.componentPool K soft members ctx written).Nodup := by
  apply h.append ((List.nodup_dedup _).filter _)
  intro v hv hother
  exact (of_decide_eq_true (List.mem_filter.mp hother).2) hv

private theorem RecState.componentPool_old {state : RecState} (hv : v ∈ state.pool) :
    v ∈ state.componentPool K soft members ctx written := List.mem_append_left _ hv

private theorem RecState.componentPool_new_avoid {state : RecState}
    (hw : ∀ v ∈ written.flatten, v ∉ (state.fixedCtx ctx).env.freeVars ++ K ++ soft)
    (hv : v ∈ state.componentPool K soft members ctx written) (hold : v ∉ state.pool) :
    v ∉ (state.fixedCtx ctx).env.freeVars ++ K ++ soft := by
  rcases List.mem_append.mp hv with hv | hv
  · exact False.elim (hold hv)
  · have hm := List.mem_dedup.mp (List.mem_filter.mp hv).1
    rcases List.mem_append.mp hm with hm | hm
    · exact hw v hm
    · have hg : v ∈ Ty.freeVarsList (RecSpecs.monoTysAt state.specs members) ∧
          v ∉ (state.fixedCtx ctx).env.freeVars ∧ v ∉ K ++ soft ++ state.pool := by
        simp only [genGroupVars, List.mem_filter, Bool.and_eq_true] at hm
        exact ⟨hm.1, by simpa using hm.2.1, by simpa using hm.2.2⟩
      intro hb
      rcases List.mem_append.mp hb with hb | hb
      · rcases List.mem_append.mp hb with hb | hb
        · exact hg.2.1 hb
        · exact hg.2.2 (List.mem_append_left _ (List.mem_append_left _ hb))
      · exact hg.2.2 (List.mem_append_left _ (List.mem_append_right _ hb))

private theorem Ty.mem_freeVarsList_exists_local {types : List Ty} {g : Nat}
    (h : g ∈ Ty.freeVarsList types) : ∃ t ∈ types, g ∈ t.freeVars := by
  induction types with
  | nil => simp [Ty.freeVarsList] at h
  | cons hd tl ih =>
    simp only [Ty.freeVarsList, List.mem_dedup, List.mem_append] at h
    rcases h with h | h
    · exact ⟨hd, List.mem_cons_self, h⟩
    · obtain ⟨t, ht, hg⟩ := ih h
      exact ⟨t, List.mem_cons_of_mem _ ht, hg⟩

private theorem recScheme_pool_append_eq {writtenPrefix old extra : List Nat} {ty : Ty}
    (ha : ∀ v ∈ extra, v ∉ ty.freeVars) : recScheme writtenPrefix (old ++ extra) ty = recScheme writtenPrefix old ty := by
  have hf : extra.filter (fun v => decide (v ∈ ty.freeVars) && decide (v ∉ writtenPrefix)) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro v hv
    simp [ha v hv]
  simp only [recScheme, recNames, List.filter_append, hf, List.append_nil]

theorem RecState.componentPool_written {state : RecState}
    (hv : v ∈ written.flatten) : v ∈ state.componentPool K soft members ctx written := by
  by_cases hold : v ∈ state.pool
  · exact state.componentPool_old hold
  · exact List.mem_append_right _ (List.mem_filter.mpr
      ⟨List.mem_dedup.mpr (List.mem_append_left _ hv), decide_eq_true hold⟩)

private theorem RecState.recScheme_componentPool_eq {state : RecState} {writtenPrefix : List Nat} {ty : Ty}
    (hlc : ty.IsLC) (hsub : ∀ v ∈ writtenPrefix, v ∈ state.pool)
    (hexport : some (recScheme writtenPrefix state.pool ty) ∈ state.exports)
    (hw : ∀ v ∈ written.flatten, v ∉ (state.fixedCtx ctx).env.freeVars ++ K ++ soft) :
    recScheme writtenPrefix (state.componentPool K soft members ctx written) ty =
      recScheme writtenPrefix state.pool ty := by
  apply recScheme_pool_append_eq
  intro v hv hvty
  have hn : v ∉ state.pool := of_decide_eq_true (List.mem_filter.mp hv).2
  have hnew : v ∈ state.componentPool K soft members ctx written := List.mem_append_right _ hv
  have hav := state.componentPool_new_avoid hw hnew hn
  apply hav
  apply List.mem_append_left
  apply List.mem_append_left
  apply Env.mem_freeVars_iff.mpr
  refine ⟨recScheme writtenPrefix state.pool ty, List.mem_append_left _ ?_, ?_⟩
  · exact List.mem_filterMap.mpr ⟨some _, hexport, rfl⟩
  · apply Ty.mem_closeOver_freeVars_of_notMem_pool hlc hvty
    intro hh
    rcases List.mem_append.mp hh with hh | hh
    · exact hn (hsub v hh)
    · exact hn (List.mem_filter.mp hh).1

private theorem ResolveRecSlots.names_avoid_of_slots
    (h : ResolveRecSlots members forbidden index slots names)
    (hs : ∀ (i : Nat) images, index + i ∈ members → slots[i]? = some images →
      ∀ ty ∈ images, w ∉ ty.freeVars) : w ∉ names.flatten := by
  induction h with
  | nil => simp
  | skip _ _ ih =>
    apply ih
    intro i images hi hget
    exact hs (i + 1) images (by simpa [Nat.add_assoc, Nat.add_comm 1 i] using hi) hget
  | cons hm hb _ _ _ ih =>
    intro hv
    rcases List.mem_append.mp hv with hv | hv
    · apply hs 0 _ (by simpa using hm) rfl (.fvar w)
        (hb ▸ List.mem_map.mpr ⟨w, hv, rfl⟩)
      simp [Ty.freeVars]
    · exact ih (fun i images hi hget => hs (i + 1) images
        (by simpa [Nat.add_assoc, Nat.add_comm 1 i] using hi) hget) hv

 theorem RecState.Frame.exportComponent_onSubst {state : RecState} {S : Subst}
    {written : List (List Nat)} {outputs : List (Option Expr)} {facts : List RecFacts}
    (h : state.Frame base K F ctx anns done) (hlc : state.LC) (hS : ∀ p ∈ S, p.2.IsLC)
    (hpool : ∀ g ∈ state.pool, (∀ p ∈ S, g ∉ p.2.freeVars) ∧ g ∉ S.map Prod.fst)
    (hpending : ∀ i ty, state.specs[i]? = some (.mono ty) → i ∉ done ++ members →
      (∀ p ∈ S, base + i ∉ p.2.freeVars) ∧ base + i ∉ S.map Prod.fst)
    (hresolve : ResolveRecSlots members
      (((state.onSubst S).fixedCtx (S.onCtx ctx)).env.freeVars ++ K ++ softVars (substSoft S F))
      0 (state.onSubst S).slots written)
    (hcounts : ∀ (i : Nat) images, i ∈ members → (state.onSubst S).slots[i]? = some images →
      images.length = (anns[i]?.getD .absent).recPrefixCount)
    (hslots : ∀ member ty, state.specs[member]? = some (.mono ty) → member ∉ done ++ members →
      ∀ (i : Nat) images, i ∈ members → (state.onSubst S).slots[i]? = some images →
        ∀ t ∈ images, base + member ∉ t.freeVars) :
    ((state.onSubst S).exportComponent members written
      ((state.onSubst S).componentPool K (softVars (substSoft S F)) members (S.onCtx ctx) written) outputs facts).Frame
      base K (substSoft S F) (S.onCtx ctx) (anns.map (BindingAnn.substTyFvars S)) (done ++ members) := by
  let st := state.onSubst S
  let pool := st.componentPool K (softVars (substSoft S F)) members (S.onCtx ctx) written
  have hdom : ∀ p ∈ S, p.1 ∉ state.pool := fun p hp hg =>
    (hpool p.1 hg).2 (List.mem_map.mpr ⟨p, hp, rfl⟩)
  have hran : ∀ p ∈ S, ∀ g ∈ p.2.freeVars, g ∉ state.pool :=
    fun p hp g hg hgp => (hpool g hgp).1 p hp hg
  have hfix : ∀ g ∈ state.pool, S.onTy (.fvar g) = .fvar g := Subst.fixes_of_dom_avoids hdom
  have hp := h.pending.onSubst_source (fun i hi => List.mem_append_left _ hi) hpending
  have hLC := hlc.onSubst hS
  have hwritten := hresolve.all_avoid
  have hnew : ∀ v ∈ pool, v ∉ state.pool →
      v ∉ (st.fixedCtx (S.onCtx ctx)).env.freeVars ++ K ++ softVars (substSoft S F) :=
    fun v hv hn => st.componentPool_new_avoid hwritten hv hn
  have hpoly : ∀ (i : Nat) (sigma : PolyTy), st.specs[i]? = some (.poly sigma) → st.exports[i]? = some (some sigma) := by
    intro i sigma hs
    rw [show st.specs = state.specs.map (RecSpec.onSubstSource S) from rfl, List.getElem?_map] at hs
    obtain ⟨old, hold, heq⟩ := Option.map_eq_some_iff.mp hs
    cases old with
    | mono ty => cases heq
    | poly original =>
      cases RecSpec.poly.inj heq
      simp only [st, RecState.onSubst, List.getElem?_map, h.poly i original hold, Option.map_some]
  change (st.exportComponent members written pool outputs facts).Frame base K (substSoft S F) (S.onCtx ctx)
    (anns.map (BindingAnn.substTyFvars S)) (done ++ members)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hp, st.componentPool_nodup h.pool_nodup,
    ?_, ?_, ?_, ?_, ?_, h.rigid_below, ?_⟩
  · simpa only [RecState.exportComponent, st, RecState.onSubst, List.length_map] using h.specs_length
  · simpa only [RecState.exportComponent, st, RecState.onSubst, List.length_map] using h.slots_length
  · simpa only [RecState.exportComponent, st, RecState.onSubst, List.length_mapIdx, List.length_map] using h.exports_length
  · simpa only [RecState.exportComponent, st, RecState.onSubst, List.length_mapIdx, List.length_map] using h.outputs_length
  · simpa only [RecState.exportComponent, st, RecState.onSubst, List.length_mapIdx, List.length_map] using h.facts_length
  · have hm : st.specs.map RecSpec.ann = (state.specs.map RecSpec.ann).map (Option.map S.onPolyTy) := by
      simp only [st, RecState.onSubst, List.map_map]
      apply List.map_congr_left
      intro spec _
      cases spec <;> rfl
    rw [show (st.exportComponent members written pool outputs facts).specs = st.specs from rfl, hm, h.modes]
    simp only [List.map_map, Function.comp_def, BindingAnn.recModeAnn_subst_source]
  · intro i sigma hs
    change st.specs[i]? = some (.poly sigma) at hs
    have hex := hpoly i sigma hs
    simp only [RecState.exportComponent, List.getElem?_mapIdx, hex, Option.map_some]
    by_cases hi : i ∈ members <;> simp [hi, hs, RecSpec.completedScheme]
  · intro i ty hs
    change st.specs[i]? = some (.mono ty) at hs
    obtain ⟨original, hold, heqty⟩ := RecSpec.mono_getElem?_map_onSubstSource hs
    subst ty
    by_cases hi : i ∈ members
    · have hislot : i < st.slots.length := by
        simpa only [st, RecState.onSubst, List.length_map, h.slots_length] using
          (show i < anns.length by simpa only [h.specs_length] using (List.getElem?_eq_some_iff.mp hold).1)
      have hslotget := List.getElem?_eq_getElem hislot
      obtain ⟨names, hnames, hbare⟩ := hresolve.lookup i _ hslotget
      rw [Nat.zero_add, if_pos hi] at hbare
      rw [if_pos (List.mem_append_right _ hi)]
      refine ⟨names, ?_, ?_, hbare.2.1, ?_, ?_⟩
      · change st.slots[i]? = some (names.map Ty.fvar)
        rw [hbare.1]; exact hslotget
      · have hh := hcounts i _ hi hslotget
        rw [← hbare.1, List.length_map] at hh
        cases ha : anns[i]? with
        | none => simpa only [List.getElem?_map, ha, Option.map_none] using hh
        | some ann => simpa only [List.getElem?_map, ha, Option.map_some, Option.getD_some,
            BindingAnn.recPrefixCount_subst_source] using hh
      · intro v hv
        exact st.componentPool_written (List.mem_flatten.mpr ⟨names, List.mem_of_getElem? hnames, hv⟩)
      · have hiEx : i < st.exports.length := by
          simpa only [st, RecState.onSubst, List.length_map, h.exports_length] using
            (show i < anns.length by simpa only [h.specs_length] using (List.getElem?_eq_some_iff.mp hold).1)
        simp only [RecState.exportComponent, List.getElem?_mapIdx,
          List.getElem?_eq_getElem hiEx, Option.map_some, if_pos hi, hs,
          Option.getD_some, hnames, RecSpec.completedScheme]
        rfl
    · have hm := h.mono i original hold
      by_cases hd : i ∈ done
      · obtain ⟨names, hslot, hcount, hnd, hsub, hex⟩ := if_pos hd ▸ hm
        rw [if_pos (List.mem_append_left _ hd)]
        have hnormalized : st.exports[i]? = some (some (recScheme names state.pool (S.onTy original))) := by
          simp only [st, RecState.onSubst, List.getElem?_map, hex, Option.map_some]
          rw [recScheme_subst_pool_avoid hdom hran hsub]
        have hstable := st.recScheme_componentPool_eq (members := members)
          (Subst.onTy_lc hS (hlc.1 _ (List.mem_of_getElem? hold))) hsub
          (List.mem_of_getElem? hnormalized) hwritten
        refine ⟨names, ?_, ?_, hnd, fun v hv => st.componentPool_old (hsub v hv), ?_⟩
        · simp only [RecState.exportComponent, st, RecState.onSubst, List.getElem?_map,
            hslot, Option.map_some, List.map_map]
          congr 1
          exact List.map_congr_left (fun v hv => hfix v (hsub v hv))
        · cases ha : anns[i]? with
          | none => simpa only [List.getElem?_map, ha, Option.map_none] using hcount
          | some ann => simpa only [List.getElem?_map, ha, Option.map_some, Option.getD_some,
              BindingAnn.recPrefixCount_subst_source] using hcount
        · have hstable' : recScheme names pool (S.onTy original) = recScheme names state.pool (S.onTy original) := hstable
          change (st.exportComponent members written pool outputs facts).exports[i]? = some (some (recScheme names pool (S.onTy original)))
          rw [hstable']
          simp only [RecState.exportComponent, List.getElem?_mapIdx, hnormalized, Option.map_some, if_neg hi]
      · rw [if_neg (by simpa only [List.mem_append, not_or] using And.intro hd hi)]
        have hex := if_neg hd ▸ hm
        simp only [RecState.exportComponent, st, RecState.onSubst, List.getElem?_mapIdx,
          List.getElem?_map, hex, Option.map_some, Option.map_none, if_neg hi]
  · intro v hv hctxv
    by_cases hold : v ∈ state.pool
    · obtain ⟨sigma, hs, hv⟩ := Env.mem_freeVars_iff.mp hctxv
      obtain ⟨original, ho, rfl⟩ := List.mem_map.mp hs
      exact Subst.notMemOnTy (hpool v hold).1
        (fun hh => h.pool_ctx v hold (Env.mem_freeVars_iff.mpr ⟨original, ho, hh⟩)) hv
    · exact hnew v hv hold (List.mem_append_left _ (List.mem_append_left _
        (Env.mem_freeVars_iff.mpr (by
          obtain ⟨sigma, hs, ht⟩ := Env.mem_freeVars_iff.mp hctxv
          exact ⟨sigma, List.mem_append_right _ hs, ht⟩))))
  · intro v hv hKv
    by_cases hold : v ∈ state.pool
    · exact h.pool_rigid v hold hKv
    · exact hnew v hv hold (List.mem_append_left _ (List.mem_append_right _ hKv))
  · intro v hv hFv
    by_cases hold : v ∈ state.pool
    · obtain ⟨ty, ht, hvty⟩ := TyList.mem_freeVars_iff.mp hFv
      obtain ⟨old, ho, rfl⟩ := List.mem_map.mp ht
      exact Subst.notMemOnTy (hpool v hold).1
        (fun hh => h.pool_soft v hold (TyList.mem_freeVars_iff.mpr ⟨old, ho, hh⟩)) hvty
    · exact hnew v hv hold (List.mem_append_right _ hFv)
  · intro sigma ⟨i, hs⟩ v hv hsig
    change st.specs[i]? = some (.poly sigma) at hs
    by_cases hold : v ∈ state.pool
    · rw [show st.specs = state.specs.map (RecSpec.onSubstSource S) from rfl, List.getElem?_map] at hs
      obtain ⟨old, ho, heq⟩ := Option.map_eq_some_iff.mp hs
      cases old with
      | mono ty => cases heq
      | poly original =>
        cases RecSpec.poly.inj heq
        exact Subst.notMemOnTy (hpool v hold).1 (h.pool_poly original ⟨i, ho⟩ v hold) hsig
    · exact hnew v hv hold (List.mem_append_left _ (List.mem_append_left _
        (Env.mem_freeVars_iff.mpr ⟨sigma, List.mem_append_left _
          (List.mem_filterMap.mpr ⟨some sigma, List.mem_of_getElem? (hpoly i sigma hs), rfl⟩), hsig⟩)))
  · intro member ty hs hm hv
    obtain ⟨old, ho, _⟩ := RecSpec.mono_getElem?_map_onSubstSource hs
    rcases List.mem_append.mp hv with hv | hv
    · exact h.pool_pending member old ho (fun hd => hm (List.mem_append_left _ hd)) hv
    · rcases List.mem_append.mp (List.mem_dedup.mp (List.mem_filter.mp hv).1) with hv | hv
      · exact hresolve.names_avoid_of_slots
          (fun i images hi hget => hslots member old ho hm i images (by simpa using hi) hget) hv
      · have hfree : base + member ∈ Ty.freeVarsList (RecSpecs.monoTysAt st.specs members) :=
          (List.mem_filter.mp hv).1
        obtain ⟨tau, htau, hmem⟩ := Ty.mem_freeVarsList_exists_local hfree
        obtain ⟨j, hj, hlook⟩ := List.mem_filterMap.mp htau
        cases hspec : st.specs[j]? with
        | none => simp [hspec] at hlook
        | some spec =>
          cases spec with
          | poly sigma => simp [hspec, RecSpec.monoTy?] at hlook
          | mono tau0 =>
            simp only [hspec, Option.bind_some, RecSpec.monoTy?, Option.some.injEq] at hlook
            subst tau
            exact hp.other member ty hs hm j (.mono tau0) hspec
              (fun heq => hm (List.mem_append_right _ (heq ▸ hj))) hmem
  · intro member ty hs hm hfv
    obtain ⟨old, ho, _⟩ := RecSpec.mono_getElem?_map_onSubstSource hs
    obtain ⟨t, ht, hf⟩ := TyList.mem_freeVars_iff.mp hfv
    obtain ⟨original, horig, rfl⟩ := List.mem_map.mp ht
    exact Subst.notMemOnTy (hpending member old ho hm).1
      (fun hh => h.pending_soft member old ho (fun hd => hm (List.mem_append_left _ hd))
        (TyList.mem_freeVars_iff.mpr ⟨original, horig, hh⟩)) hf

private theorem OpenRecAnns.written_count
    (h : OpenRecAnns members index frontier anns next openings) :
    ∀ j : Nat, index + j ∈ members → ((openings[j]?).getD .empty).written.length =
      (anns[j]?.getD .absent).recPrefixCount := by
  induction h with
  | nil => intro j _; simp [RecOpening.empty, BindingAnn.recPrefixCount]
  | skip hn hr ih =>
    intro j hj
    cases j with
    | zero => exact False.elim (hn (by simpa using hj))
    | succ j => exact ih j (by simpa only [Nat.succ_add, Nat.add_succ] using hj)
  | cons hm hh hr ih =>
    intro j hj
    cases j with
    | zero => cases hh <;> simp [BindingAnn.recPrefixCount, RecOpening.empty, freshVars_length]
    | succ j => exact ih j (by simpa only [Nat.succ_add, Nat.add_succ] using hj)

private theorem installed_subst_slot {state : RecState} {S : Subst} {i : Nat} {images : List Ty}
    (hi : i ∈ members) (hx : ((state.installOpenings members openings).onSubst S).slots[i]? = some images) :
    images = (((openings[i]?).getD .empty).written.map Ty.fvar).map S.onTy := by
  have hlt : i < state.slots.length := by
    simpa only [RecState.onSubst, RecState.installOpenings, List.length_map, List.length_mapIdx] using
      (List.getElem?_eq_some_iff.mp hx).1
  have hget := List.getElem?_eq_getElem hlt
  simp only [RecState.onSubst, RecState.installOpenings, List.getElem?_map, List.getElem?_mapIdx,
    hget, Option.map_some, if_pos hi] at hx
  exact (Option.some.inj hx).symm

 theorem recStep_frame
    {state : RecState}
    (ho : OpenRecAnns component 0 frontier anns opened openings)
    (hp : CheckRecShapes K ((state.installOpenings component openings).shapes component openings) pre)
    (hc : InferRecComponent K (substSoft pre (F ++ (openings.flatMap RecOpening.written).map Ty.fvar))
      component 0 opened (((state.installOpenings component openings).onSubst pre).rhsCtx (pre.onCtx ctx))
      ((openRecSources openings bindings).map (InferInput.substTyFvars pre))
      ((state.installOpenings component openings).onSubst pre).specs first current outputs facts)
    (hf : FinishRecComponent K (softVars (substSoft (pre ++ current) F)) component
      ((pre ++ current).onCtx ctx) ((state.installOpenings component openings).onSubst (pre ++ current))
      outputs facts exported)
    (hInfer : ∀ {κ F' Ψ c e Ψ' T output ty}, e.size ≤ sizeBindings bindings →
      Infer κ F' Ψ c e Ψ' T output ty →
      ∀ {w}, w < Ψ →
      e.erase.ForallOuter (fun i => ∀ M, c.env[i]? = some M → w ∉ M.body.freeVars) 0 →
      w ∉ e.rigidVars →
      (∀ p ∈ T, w ∉ p.2.freeVars) ∧ w ∉ ty.freeVars ∧ w ∉ T.map Prod.fst)
    (hvalid : RecGroups.ValidResidualGroups (anns.map BindingAnn.recModeAnn) (bindings.map InferInput.erase)
      (past ++ component :: rest))
    (hframe : state.Frame base K F ctx anns past.flatten)
    (hlc : state.LC) (hctx : CtxWF ctx)
    (hbelow : state.Below frontier) (hbase : base + bindings.length ≤ frontier)
    (hanns : ∀ ann ∈ anns, ∀ v ∈ ann.rigidVars, v ∈ K ++ softVars F)
    (hrhs : ∀ rhs ∈ bindings, ∀ v ∈ rhs.rigidVars, v ∈ K ++ softVars F) :
    exported.Frame base K (substSoft (pre ++ current) F) ((pre ++ current).onCtx ctx)
      (anns.map (BindingAnn.substTyFvars (pre ++ current))) (past.flatten ++ component) ∧
    (∀ g ∈ state.pool, (∀ p ∈ pre ++ current, g ∉ p.2.freeVars) ∧ g ∉ (pre ++ current).map Prod.fst) ∧
    (∀ member ty, state.specs[member]? = some (.mono ty) → member ∉ past.flatten ++ component →
      (∀ p ∈ pre ++ current, base + member ∉ p.2.freeVars) ∧ base + member ∉ (pre ++ current).map Prod.fst) := by
  have havoid := recStep_oldpool_pending_avoid ho hp hc hInfer hvalid hframe hbelow hbase hanns hrhs
  have hnot : ∀ i ∈ component, i ∉ past.flatten := by
    intro i hi hd
    have hnd : (past.flatten ++ (component ++ rest.flatten)).Nodup := by
      simpa only [List.flatten_append, List.flatten_cons] using hvalid.flatten_nodup
    exact (List.nodup_append.mp hnd).2.2 i hd i (List.mem_append_left _ hi) rfl
  have hins : (state.installOpenings component openings).Frame base K F ctx anns past.flatten :=
    hframe.installOpenings hnot
  have hinitLC := hlc.installOpenings (members := component) (openings := openings)
  have hpreLC := hp.lc (RecState.shapes_lc hinitLC ho.expected_lc)
  have hcurrentLC := hc.lc_of_infer (fun _ hi => hi.lc)
    ((hinitLC.onSubst hpreLC).rhsCtx (Subst.onCtx_wf hpreLC hctx))
    (hinitLC.onSubst hpreLC).1
  have hSLC : ∀ p ∈ pre ++ current, p.2.IsLC :=
    fun p hm => (List.mem_append.mp hm).elim (hpreLC p) (hcurrentLC p)
  refine ⟨?_, havoid⟩
  cases hf with
  | mk hresolve =>
    apply hins.exportComponent_onSubst hlc.installOpenings hSLC havoid.1 havoid.2 hresolve
    · intro i images hi hx
      rw [installed_subst_slot hi hx, List.length_map, List.length_map]
      exact ho.written_count i (by simpa using hi)
    · intro member ty ht hm i images hi hx t htmem
      have hw : base + member < frontier := by
        have hlt := (List.getElem?_eq_some_iff.mp ht).1
        have hlen : anns.length = bindings.length := by simpa only [List.length_map] using hvalid.length
        change member < state.specs.length at hlt
        rw [hframe.specs_length, hlen] at hlt
        omega
      rw [installed_subst_slot hi hx] at htmem
      obtain ⟨old, hold, rfl⟩ := List.mem_map.mp htmem
      obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hold
      apply Subst.notMemOnTy (havoid.2 member ty ht hm).1
      simp only [Ty.freeVars, List.mem_singleton]
      intro heq
      subst v
      cases hxopen : openings[i]? with
      | none => simp [hxopen, RecOpening.empty] at hv
      | some opening =>
        have hrange := ho.written_range (base + member)
          (List.mem_flatMap.mpr ⟨opening, List.mem_of_getElem? hxopen, by simpa only [hxopen, Option.getD_some] using hv⟩)
        omega

theorem recValid_subst {anns : List BindingAnn} {bindings : List InferInput}
    (h : RecGroups.ValidResidualGroups (anns.map BindingAnn.recModeAnn) (bindings.map InferInput.erase) groups)
    (S : Subst) :
    RecGroups.ValidResidualGroups ((anns.map (BindingAnn.substTyFvars S)).map BindingAnn.recModeAnn)
      ((bindings.map (InferInput.substTyFvars S)).map InferInput.erase) groups := by
  have hg := h.map_bindings (anns' := (anns.map (BindingAnn.substTyFvars S)).map BindingAnn.recModeAnn) id
    (by simp) (fun i => by
      simp only [RecGroups.UnsignedAt, List.getElem?_map, Option.map_map, Function.comp_def]
      cases anns[i]? with
      | none => simp
      | some ann => cases ann <;> simp [BindingAnn.recModeAnn, BindingAnn.substTyFvars])
    (fun _ _ => rfl)
  simpa only [List.map_id, List.map_map, Function.comp_def, InferInput.erase_substTyFvars] using hg

private theorem FinishRecComponent.pool_extends
    (h : FinishRecComponent K soft members ctx state outputs facts final) (hv : v ∈ state.pool) :
    v ∈ final.pool := by
  cases h
  exact state.componentPool_old hv

 theorem _root_.InferRecStrata.frame_of_infer
    (h : InferRecStrata K F frontier ctx anns bindings state groups next S final)
    (hInfer : ∀ {κ F' Ψ c e Ψ' T output ty}, e.size ≤ sizeBindings bindings →
      Infer κ F' Ψ c e Ψ' T output ty →
      ∀ {w}, w < Ψ →
      e.erase.ForallOuter (fun i => ∀ M, c.env[i]? = some M → w ∉ M.body.freeVars) 0 →
      w ∉ e.rigidVars →
      (∀ p ∈ T, w ∉ p.2.freeVars) ∧ w ∉ ty.freeVars ∧ w ∉ T.map Prod.fst)
    (hvalid : RecGroups.ValidResidualGroups (anns.map BindingAnn.recModeAnn) (bindings.map InferInput.erase) (past ++ groups))
    (hframe : state.Frame base K F ctx anns past.flatten)
    (hlc : state.LC) (hctxWF : CtxWF ctx)
    (hbelow : state.Below frontier) (hctx : CtxBelow frontier ctx)
    (hF : ∀ t ∈ F, Ty.BelowFvars frontier t)
    (hbase : base + bindings.length ≤ frontier)
    (hanns : ∀ ann ∈ anns, ∀ v ∈ ann.rigidVars, v ∈ K ++ softVars F)
    (hrhs : ∀ rhs ∈ bindings, ∀ v ∈ rhs.rigidVars, v ∈ K ++ softVars F) :
    final.Frame base K (substSoft S F) (S.onCtx ctx) (anns.map (BindingAnn.substTyFvars S)) (past ++ groups).flatten ∧
    (∀ g ∈ state.pool, (∀ p ∈ S, g ∉ p.2.freeVars) ∧ g ∉ S.map Prod.fst) := by
  match h with
  | .nil =>
    have hannNil : anns.map (BindingAnn.substTyFvars []) = anns := by
      calc
        anns.map (BindingAnn.substTyFvars []) = anns.map id := List.map_congr_left
          (fun ann _ => ann.substTyFvars_eq_self_of_fixes (fun _ _ => rfl))
        _ = anns := List.map_id anns
    exact ⟨by simpa only [substSoft_nil, Subst.onCtx_nil, hannNil, List.append_nil] using hframe,
      by intro g hg; exact ⟨by simp, by simp⟩⟩
  | .cons ho hp hc hf hr =>
    expose_names
    obtain ⟨hstepFrame, hstepPool, _⟩ := recStep_frame ho hp hc hf hInfer hvalid hframe
      hlc hctxWF hbelow hbase hanns hrhs
    have hstep : InferRecStrata K F frontier ctx anns bindings state [component]
        first (pre ++ current ++ []) exported := .cons ho hp hc hf .nil
    have hK : ∀ k ∈ K, k < frontier := fun k hk => by have := hframe.rigid_below k hk; omega
    have hAnnBelow : ∀ ann ∈ anns, ∀ v ∈ ann.rigidVars, v < frontier := by
      intro ann ha v hv
      exact (List.mem_append.mp (hanns ann ha v hv)).elim (hK v) (softVars_lt hF v)
    have hstepBelow := hstep.belowFvars_of_infer (fun _ hi => hi.belowFvars) hctx hK hF hbelow hAnnBelow
    simp only [List.append_nil] at hstepBelow
    have hstepLC := hstep.lc_of_infer (fun _ hi => hi.lc) hctxWF hlc
    simp only [List.append_nil] at hstepLC
    have hfix : ∀ k ∈ K, (pre ++ current).onTy (.fvar k) = .fvar k := by
      apply Subst.fixes_of_dom_avoids
      simpa only [List.append_nil] using hstep.dom_avoids
    have htailValid := recValid_subst (S := pre ++ current)
      (by simpa only [List.append_assoc, List.singleton_append] using hvalid :
        RecGroups.ValidResidualGroups (anns.map BindingAnn.recModeAnn) (bindings.map InferInput.erase)
          ((past ++ [component]) ++ rest))
    have htailFrame : exported.Frame base K (substSoft (pre ++ current) F) ((pre ++ current).onCtx ctx)
        (anns.map (BindingAnn.substTyFvars (pre ++ current))) (past ++ [component]).flatten := by
      simpa only [List.flatten_append, List.flatten_cons, List.flatten_nil, List.append_nil] using hstepFrame
    obtain ⟨hfinal, htailPool⟩ := hr.frame_of_infer
      (fun he hi => hInfer (by simpa only [sizeBindings_map_substTyFvars] using he) hi)
      htailValid htailFrame hstepLC.2 (Subst.onCtx_wf hstepLC.1 hctxWF)
      hstepBelow.2 (Subst.onCtx_below hstepBelow.1 (ho.frontier_le.trans hc.frontier_le) hctx)
      (substSoft_below hstepBelow.1 (ho.frontier_le.trans hc.frontier_le) hF)
      (by simp only [List.length_map]; have := ho.frontier_le; have := hc.frontier_le; omega)
      (by
        intro ann hm v hv
        obtain ⟨original, ho, rfl⟩ := List.mem_map.mp hm
        obtain ⟨k, hk, himage⟩ := BindingAnn.rigidVars_substTyFvars hv
        exact scope_image hfix (hanns original ho k hk) himage)
      (by
        intro rhs hm
        obtain ⟨original, ho, rfl⟩ := List.mem_map.mp hm
        exact (show SourceScope K F original from hrhs original ho).subst (pre ++ current) hfix)
    refine ⟨?_, ?_⟩
    · simpa only [substSoft_append, Subst.onCtx_append, List.map_map, Function.comp_def,
        ← BindingAnn.substTyFvars_append, List.append_assoc, List.singleton_append] using hfinal
    · intro g hg
      have ht := htailPool g (hf.pool_extends hg)
      exact ⟨fun p hp => (List.mem_append.mp hp).elim ((hstepPool g hg).1 p) (ht.1 p),
        by simpa only [List.map_append, List.mem_append, not_or] using And.intro (hstepPool g hg).2 ht.2⟩
 termination_by structural h


theorem RecState.Frame.setSigned {state : RecState} {member : Nat} {names : List Nat}
    {output : Expr} {facts : RecFacts} (h : state.Frame base K F ctx anns done) :
    (state.setSigned member names output facts).Frame base K F ctx anns done := by
  refine ⟨h.specs_length, h.slots_length, h.exports_length, ?_, ?_, h.modes, h.poly, h.mono,
    h.pending, h.pool_nodup, h.pool_ctx, h.pool_rigid, h.pool_soft, h.pool_poly,
    h.pool_pending, h.rigid_below, h.pending_soft⟩
  · simpa only [RecState.setSigned, List.length_set] using h.outputs_length
  · simpa only [RecState.setSigned, List.length_set] using h.facts_length

private theorem RecState.Frame.poly_of_complete {state : RecState} {i : Nat} {scheme : PolyTy}
    (h : state.Frame base K F ctx anns done) (ha : anns[i]? = some (.complete scheme)) :
    state.specs[i]? = some (.poly scheme) := by
  have hm := congrArg (fun xs : List (Option PolyTy) => xs[i]?) h.modes
  simp only [List.getElem?_map, ha, Option.map_some, BindingAnn.recModeAnn] at hm
  cases hs : state.specs[i]? with
  | none => simp [hs] at hm
  | some spec =>
    cases spec with
    | mono ty => simp [hs, RecSpec.ann] at hm
    | poly original =>
      simp only [hs, Option.map_some, RecSpec.ann, Option.some.injEq] at hm
      cases hm
      rfl

 theorem _root_.InferRecSigned.frame_of_infer
    (h : InferRecSigned K F index frontier ctx anns bindings state next S final)
    (hInfer : ∀ {κ F' Ψ c e Ψ' T output ty}, e.size ≤ sizeBindings bindings →
      Infer κ F' Ψ c e Ψ' T output ty →
      ∀ {w}, w < Ψ →
      e.erase.ForallOuter (fun i => ∀ M, c.env[i]? = some M → w ∉ M.body.freeVars) 0 →
      w ∉ e.rigidVars →
      (∀ p ∈ T, w ∉ p.2.freeVars) ∧ w ∉ ty.freeVars ∧ w ∉ T.map Prod.fst)
    (hframe : state.Frame base K F ctx fullAnns done)
    (hremaining : fullAnns.drop index = anns)
    (hmono : ∀ i ty, state.specs[i]? = some (.mono ty) → i ∈ done)
    (hpoolBelow : ∀ g ∈ state.pool, g < frontier) :
    final.Frame base K (substSoft S F) (S.onCtx ctx) (fullAnns.map (BindingAnn.substTyFvars S)) done ∧
    (∀ g ∈ state.pool, (∀ p ∈ S, g ∉ p.2.freeVars) ∧ g ∉ S.map Prod.fst) := by
  match h with
  | .nil =>
    have hannNil : fullAnns.map (BindingAnn.substTyFvars []) = fullAnns := by
      calc
        fullAnns.map (BindingAnn.substTyFvars []) = fullAnns.map id := List.map_congr_left
          (fun ann _ => ann.substTyFvars_eq_self_of_fixes (fun _ _ => rfl))
        _ = fullAnns := List.map_id fullAnns
    exact ⟨by simpa only [substSoft_nil, Subst.onCtx_nil, hannNil] using hframe,
      by intro g hg; exact ⟨by simp, by simp⟩⟩
  | .skip _ hr =>
    apply hr.frame_of_infer
      (fun he hi => hInfer (by simp only [sizeBindings]; omega) hi) hframe
      (by simp only [List.drop_add_one_eq_tail_drop, hremaining, List.tail_cons]) hmono hpoolBelow
  | .cons _ hscope hi hu _ hr =>
    expose_names
    have hAnn : fullAnns[index]? = some (.complete scheme) := by
      have hh := congrArg (fun xs : List BindingAnn => xs[0]?) hremaining
      simpa only [List.getElem?_drop, Nat.zero_add, List.getElem?_cons_zero] using hh
    have hspec := hframe.poly_of_complete hAnn
    have havoid : ∀ g ∈ state.pool,
        (∀ p ∈ s1 ++ s2, g ∉ p.2.freeVars) ∧ g ∉ (s1 ++ s2).map Prod.fst := by
      intro g hg
      have hgy : g ∉ freshVars frontier scheme.paramCount := fun hmem => by
        have := freshVars_ge g hmem
        have := hpoolBelow g hg
        omega
      obtain ⟨hfirstS, hfirstTy, hfirstD⟩ := hInfer
        (by simp only [InferInput.size_openTyVars, sizeBindings]; omega) hi
        (show g < frontier + scheme.paramCount by have := hpoolBelow g hg; omega)
        (by
          apply Expr.ForallOuter.of_recGroupRefs_with_outer (n := 0)
          · intro j hj M hget hv
            exact hframe.pool_rhsCtx g hg (Env.mem_freeVars_iff.mpr ⟨M, List.mem_of_getElem? hget, hv⟩)
          · intro j hj M hget hv
            exact hframe.pool_rhsCtx g hg (Env.mem_freeVars_iff.mpr ⟨M, List.mem_of_getElem? hget, hv⟩))
        (by
          intro hv
          rcases InferInput.rigidVars_openTyVarsFrom hv with hv | hv
          · exact (List.mem_append.mp (hscope g hv)).elim (hframe.pool_rigid g hg) (hframe.pool_soft g hg)
          · exact hgy hv)
      have hexpected : g ∉ ((s1.onPolyTy scheme).openVars (freshVars frontier scheme.paramCount)).freeVars := by
        intro hv
        exact (Ty.freeVars_openVars_subset g hv).elim
          (Subst.notMemOnTy hfirstS (hframe.pool_poly scheme ⟨index, hspec⟩ g hg)) hgy
      have hsecondS : ∀ p ∈ s2, g ∉ p.2.freeVars := by
        intro p hp hv
        exact (hu.unifies.range_mem p hp g hv).elim hfirstTy hexpected
      have hsecondD : g ∉ s2.map Prod.fst := by
        intro hm
        obtain ⟨p, hp, hpw⟩ := List.mem_map.mp hm
        have hh := hu.unifies.dom_mem p hp
        rw [hpw] at hh
        exact hh.elim hfirstTy hexpected
      exact ⟨fun p hp => (List.mem_append.mp hp).elim (hfirstS p) (hsecondS p),
        by simpa only [List.map_append, List.mem_append, not_or] using And.intro hfirstD hsecondD⟩
    have hnextFrame := (hframe.onSubst havoid
      (fun i ty hs hn => False.elim (hn (hmono i ty hs)))).setSigned
      (member := index) (names := freshVars frontier scheme.paramCount)
      (output := output.substTyFvars s2) (facts := bodyFacts.onSubst s2)
    have hnextMono : ∀ i ty,
        ((state.onSubst (s1 ++ s2)).setSigned index (freshVars frontier scheme.paramCount)
          (output.substTyFvars s2) (bodyFacts.onSubst s2)).specs[i]? = some (.mono ty) → i ∈ done := by
      intro i ty hs
      obtain ⟨old, ho, _⟩ := RecSpec.mono_getElem?_map_onSubstSource hs
      exact hmono i old ho
    obtain ⟨hfinal, htailAvoid⟩ := hr.frame_of_infer
      (fun he hh => hInfer (by
        simp only [sizeBindings_map_substTyFvars] at he
        simp only [sizeBindings]
        omega) hh)
      hnextFrame
      (by simp only [← List.map_drop, List.drop_add_one_eq_tail_drop, hremaining, List.map_cons, List.tail_cons]) hnextMono
      (by intro g hg; have hlt := hpoolBelow g hg; have := hi.frontier_le; omega)
    refine ⟨?_, ?_⟩
    · simpa only [substSoft_append, Subst.onCtx_append, List.map_map, Function.comp_def,
        ← BindingAnn.substTyFvars_append] using hfinal
    · intro g hg
      have ht := htailAvoid g hg
      exact ⟨fun p hp => (List.mem_append.mp hp).elim ((havoid g hg).1 p) (ht.1 p),
        by simpa only [List.map_append, List.mem_append, not_or] using And.intro (havoid g hg).2 ht.2⟩
 termination_by structural h


 theorem recStep_sourceSound
    {state : RecState} {past : List (List Nat)}
    (ho : OpenRecAnns component 0 frontier anns opened openings)
    (hp : CheckRecShapes K ((state.installOpenings component openings).shapes component openings) pre)
    (hc : InferRecComponent K (substSoft pre (F ++ (openings.flatMap RecOpening.written).map Ty.fvar))
      component 0 opened (((state.installOpenings component openings).onSubst pre).rhsCtx (pre.onCtx ctx))
      ((openRecSources openings bindings).map (InferInput.substTyFvars pre))
      ((state.installOpenings component openings).onSubst pre).specs first current outputs facts)
    (hf : FinishRecComponent K (softVars (substSoft (pre ++ current) F)) component
      ((pre ++ current).onCtx ctx) ((state.installOpenings component openings).onSubst (pre ++ current))
      outputs facts exported)
    (hInfer : ∀ {κ F' Ψ c e Ψ' T output ty}, e.size ≤ sizeBindings bindings →
      Infer κ F' Ψ c e Ψ' T output ty → CtxWF c → TypeOfHM (T.onCtx c) output ty)
    (hframe : state.Frame base K F ctx anns past.flatten)
    (heframe : exported.Frame base K (substSoft (pre ++ current) F) ((pre ++ current).onCtx ctx)
      (anns.map (BindingAnn.substTyFvars (pre ++ current))) (past.flatten ++ component))
    (hlc : state.LC) (hctx : CtxWF ctx) (htyped : state.SourceTyped ctx)
    (hnot : ∀ i ∈ component, i ∉ past.flatten)
    (hmono : ∀ i ∈ component, ∃ ty, state.specs[i]? = some (.mono ty)) :
    exported.SourceTyped ((pre ++ current).onCtx ctx) := by
  have hinitLC := hlc.installOpenings (members := component) (openings := openings)
  have hpreLC := hp.lc (RecState.shapes_lc hinitLC ho.expected_lc)
  have hpreCtx := (hinitLC.onSubst hpreLC).rhsCtx (Subst.onCtx_wf hpreLC hctx)
  have hcurrentLC := hc.lc_of_infer (fun _ hi => hi.lc) hpreCtx (hinitLC.onSubst hpreLC).1
  have hSLC : ∀ p ∈ pre ++ current, p.2.IsLC :=
    fun p hm => (List.mem_append.mp hm).elim (hpreLC p) (hcurrentLC p)
  have hsound := hc.sourceSound_of_infer
    (fun he hi => hInfer (by simpa only [sizeBindings_map_substTyFvars, sizeBindings_openRecSources] using he) hi)
    (fun _ hi => hi.lc) hpreCtx (hinitLC.onSubst hpreLC).1
  have hsource : (state.installOpenings component openings).SourceTyped ctx := htyped
  have hsourceS := hsource.onSubst (pre ++ current) hSLC
  cases hf with
  | mk hresolve =>
    expose_names
    let st := (state.installOpenings component openings).onSubst (pre ++ current)
    have hstmono : ∀ i ∈ component, ∃ ty, st.specs[i]? = some (.mono ty) := by
      intro i hi
      obtain ⟨ty, ht⟩ := hmono i hi
      exact ⟨(pre ++ current).onTy ty, by simp only [st, RecState.onSubst, RecState.installOpenings,
        List.getElem?_map, ht, Option.map_some, RecSpec.onSubstSource]⟩
    apply hsourceS.exportComponent
      (by simp only [RecState.onSubst, RecState.installOpenings, List.length_map]; exact hframe.exports_length.trans hframe.outputs_length.symm)
      (by simp only [RecState.onSubst, RecState.installOpenings, List.length_map]; exact hframe.outputs_length.trans hframe.specs_length.symm)
      (hinitLC.onSubst hSLC).1
    · intro i hi
      obtain ⟨ty, ht⟩ := hmono i hi
      have hh := if_neg (hnot i hi) ▸ hframe.mono i ty ht
      simp only [RecState.onSubst, RecState.installOpenings, List.getElem?_map, hh, Option.map_some, Option.map_none]
    · exact hstmono
    · intro i hi
      have hil : i < st.slots.length := by
        rw [show st.slots.length = anns.length from by simp only [st, RecState.onSubst, RecState.installOpenings, List.length_map, List.length_mapIdx, hframe.slots_length]]
        obtain ⟨ty, ht⟩ := hmono i hi
        simpa only [hframe.specs_length] using (List.getElem?_eq_some_iff.mp ht).1
      obtain ⟨ns, hns, hh⟩ := hresolve.lookup i _ (List.getElem?_eq_getElem hil)
      rw [Nat.zero_add, if_pos hi] at hh
      simpa only [hns, Option.getD_some] using hh.2.1
    · intro i hi v hv
      apply st.componentPool_written
      cases hh : written[i]? with
      | none => simp only [hh, Option.getD_none, List.not_mem_nil] at hv
      | some ns => exact List.mem_flatten.mpr ⟨ns, List.mem_of_getElem? hh,
          by simpa only [hh, Option.getD_some] using hv⟩
    · exact heframe.pool_nodup
    · exact heframe.pool_rhsCtx
    · intro i ty output ht hout
      obtain ⟨old, hold, rfl⟩ := RecSpec.mono_getElem?_map_onSubstSource ht
      have htyPre : ((state.installOpenings component openings).onSubst pre).specs[i]? = some (.mono (pre.onTy old)) := by
        simp only [RecState.onSubst, List.getElem?_map, hold, Option.map_some, RecSpec.onSubstSource]
      have hh := hsound i (pre.onTy old) output htyPre hout
      rw [RecState.rhsCtx_onSubst] at hh ⊢
      simpa only [Subst.onCtx_append, Subst.onTy_append] using hh
 theorem _root_.InferRecStrata.sourceSound_of_infer
    (h : InferRecStrata K F frontier ctx anns bindings state groups next S final)
    (hInfer : ∀ {κ F' Ψ c e Ψ' T output ty}, e.size ≤ sizeBindings bindings →
      Infer κ F' Ψ c e Ψ' T output ty →
      ∀ {w}, w < Ψ →
      e.erase.ForallOuter (fun i => ∀ M, c.env[i]? = some M → w ∉ M.body.freeVars) 0 →
      w ∉ e.rigidVars →
      (∀ p ∈ T, w ∉ p.2.freeVars) ∧ w ∉ ty.freeVars ∧ w ∉ T.map Prod.fst)
    (hvalid : RecGroups.ValidResidualGroups (anns.map BindingAnn.recModeAnn) (bindings.map InferInput.erase) (past ++ groups))
    (hframe : state.Frame base K F ctx anns past.flatten)
    (hlc : state.LC) (hctxWF : CtxWF ctx)
    (hbelow : state.Below frontier) (hctx : CtxBelow frontier ctx)
    (hF : ∀ t ∈ F, Ty.BelowFvars frontier t)
    (hbase : base + bindings.length ≤ frontier)
    (hanns : ∀ ann ∈ anns, ∀ v ∈ ann.rigidVars, v ∈ K ++ softVars F)
    (hrhs : ∀ rhs ∈ bindings, ∀ v ∈ rhs.rigidVars, v ∈ K ++ softVars F)
    (hSound : ∀ {κ F' Ψ c e Ψ' T output ty}, e.size ≤ sizeBindings bindings →
      Infer κ F' Ψ c e Ψ' T output ty → CtxWF c → TypeOfHM (T.onCtx c) output ty)
    (htyped : state.SourceTyped ctx) : final.SourceTyped (S.onCtx ctx) := by
  match h with
  | .nil => simpa only [Subst.onCtx_nil] using htyped
  | .cons ho hp hc hf hr =>
    expose_names
    obtain ⟨hstepFrame, hstepPool, _⟩ := recStep_frame ho hp hc hf hInfer hvalid hframe
      hlc hctxWF hbelow hbase hanns hrhs
    have hnot : ∀ i ∈ component, i ∉ past.flatten := by
      intro i hi hd
      have hnd : (past.flatten ++ (component ++ rest.flatten)).Nodup := by
        simpa only [List.flatten_append, List.flatten_cons] using hvalid.flatten_nodup
      exact (List.nodup_append.mp hnd).2.2 i hd i (List.mem_append_left _ hi) rfl
    have hmono : ∀ i ∈ component, ∃ ty, state.specs[i]? = some (.mono ty) := by
      intro i hi
      have hm : i ∈ (past ++ component :: rest).flatten := by
        simp only [List.flatten_append, List.flatten_cons, List.mem_append]
        tauto
      exact hframe.mono_at_unsigned ((hvalid.covers_unsigned i (hvalid.bounded i hm)).mp hm)
    have hstepSound := recStep_sourceSound ho hp hc hf hSound hframe hstepFrame hlc hctxWF htyped hnot hmono
    have hstep : InferRecStrata K F frontier ctx anns bindings state [component]
        first (pre ++ current ++ []) exported := .cons ho hp hc hf .nil
    have hK : ∀ k ∈ K, k < frontier := fun k hk => by have := hframe.rigid_below k hk; omega
    have hAnnBelow : ∀ ann ∈ anns, ∀ v ∈ ann.rigidVars, v < frontier := by
      intro ann ha v hv
      exact (List.mem_append.mp (hanns ann ha v hv)).elim (hK v) (softVars_lt hF v)
    have hstepBelow := hstep.belowFvars_of_infer (fun _ hi => hi.belowFvars) hctx hK hF hbelow hAnnBelow
    simp only [List.append_nil] at hstepBelow
    have hstepLC := hstep.lc_of_infer (fun _ hi => hi.lc) hctxWF hlc
    simp only [List.append_nil] at hstepLC
    have hfix : ∀ k ∈ K, (pre ++ current).onTy (.fvar k) = .fvar k := by
      apply Subst.fixes_of_dom_avoids
      simpa only [List.append_nil] using hstep.dom_avoids
    have htailValid := recValid_subst (S := pre ++ current)
      (by simpa only [List.append_assoc, List.singleton_append] using hvalid :
        RecGroups.ValidResidualGroups (anns.map BindingAnn.recModeAnn) (bindings.map InferInput.erase)
          ((past ++ [component]) ++ rest))
    have htailFrame : exported.Frame base K (substSoft (pre ++ current) F) ((pre ++ current).onCtx ctx)
        (anns.map (BindingAnn.substTyFvars (pre ++ current))) (past ++ [component]).flatten := by
      simpa only [List.flatten_append, List.flatten_cons, List.flatten_nil, List.append_nil] using hstepFrame
    have hfinal := hr.sourceSound_of_infer
      (fun he hi => hInfer (by simpa only [sizeBindings_map_substTyFvars] using he) hi)
      htailValid htailFrame hstepLC.2 (Subst.onCtx_wf hstepLC.1 hctxWF)
      hstepBelow.2 (Subst.onCtx_below hstepBelow.1 (ho.frontier_le.trans hc.frontier_le) hctx)
      (substSoft_below hstepBelow.1 (ho.frontier_le.trans hc.frontier_le) hF)
      (by simp only [List.length_map]; have := ho.frontier_le; have := hc.frontier_le; omega)
      (by
        intro ann hm v hv
        obtain ⟨original, ho, rfl⟩ := List.mem_map.mp hm
        obtain ⟨k, hk, himage⟩ := BindingAnn.rigidVars_substTyFvars hv
        exact scope_image hfix (hanns original ho k hk) himage)
      (by
        intro rhs hm
        obtain ⟨original, ho, rfl⟩ := List.mem_map.mp hm
        exact (show SourceScope K F original from hrhs original ho).subst (pre ++ current) hfix)
      (fun he hi => hSound (by simpa only [sizeBindings_map_substTyFvars] using he) hi)
      hstepSound
    simpa only [Subst.onCtx_append] using hfinal
 termination_by structural h



 theorem RecState.Frame.all_mono_done {state : RecState} {bindings : List InferInput}
    (h : state.Frame base K F ctx anns groups.flatten)
    (hv : RecGroups.ValidResidualGroups (anns.map BindingAnn.recModeAnn) (bindings.map InferInput.erase) groups) :
    ∀ (i : Nat) (ty : Ty), state.specs[i]? = some (.mono ty) → i ∈ groups.flatten := by
  intro i ty hs
  have hm := congrArg (fun xs : List (Option PolyTy) => xs[i]?) h.modes
  dsimp only at hm
  simp only [List.getElem?_map, hs, Option.map_some, RecSpec.ann] at hm
  have hi : i < bindings.length := by
    have hb := (List.getElem?_eq_some_iff.mp hs).1
    have hl : anns.length = bindings.length := by simpa only [List.length_map] using hv.length
    simpa only [h.specs_length, hl] using hb
  exact (hv.covers_unsigned i (by simpa only [List.length_map] using hi)).mpr
    (by simpa only [RecGroups.UnsignedAt, List.getElem?_map] using hm.symm)

theorem RecState.Frame.prefixes_mono {state : RecState} {i : Nat}
    (h : state.Frame base K F ctx anns done)
    (hs : state.specs[i]? = some (.mono ty)) (hd : i ∈ done) :
    ∃ names, state.prefixes[i]? = some names ∧
      names.length = (anns[i]?.getD .absent).recPrefixCount ∧ names.Nodup ∧
      (∀ v ∈ names, v ∈ state.pool) := by
  obtain ⟨names, hslots, hlen, hnd, hsub, _⟩ := if_pos hd ▸ h.mono i ty hs
  refine ⟨names, ?_, hlen, hnd, hsub⟩
  simp only [RecState.prefixes, List.getElem?_mapIdx, hs, Option.map_some, hslots, Option.getD_some]
  congr 1
  rw [List.filterMap_map]
  change (names.filterMap some) = names
  simp

theorem RecState.Frame.prefixes_wf {state : RecState} {bindings : List InferInput}
    (h : state.Frame base K F ctx anns groups.flatten)
    (hg : RecGroups.ValidResidualGroups (anns.map BindingAnn.recModeAnn) (bindings.map InferInput.erase) groups) :
    RecPrefixesWF anns state.specs state.prefixes state.pool := by
  refine ⟨by simp only [RecState.prefixes, List.length_mapIdx], ?_⟩
  intro i ann names ha hn
  have hi : i < state.specs.length := by
    simpa only [h.specs_length] using (List.getElem?_eq_some_iff.mp ha).1
  have hs := List.getElem?_eq_getElem hi
  cases hspec : state.specs[i] with
  | mono ty =>
    have hget : state.specs[i]? = some (.mono ty) := hspec ▸ hs
    obtain ⟨written, hp, hcount, hnd, hsub⟩ := h.prefixes_mono hget (h.all_mono_done hg _ _ hget)
    cases Option.some.inj (hp.symm.trans hn)
    exact ⟨by simpa only [ha, Option.getD_some] using hcount, hnd, hsub⟩
  | poly scheme =>
    have hget : state.specs[i]? = some (.poly scheme) := hspec ▸ hs
    have hp : state.prefixes[i]? = some [] := by
      simp only [RecState.prefixes, List.getElem?_mapIdx, hget, Option.map_some]
    cases Option.some.inj (hp.symm.trans hn)
    have hm := congrArg (fun xs : List (Option PolyTy) => xs[i]?) h.modes
    simp only [List.getElem?_map, hget, ha, Option.map_some, RecSpec.ann] at hm
    cases ann <;> simp_all [BindingAnn.recModeAnn, BindingAnn.recPrefixCount]

private theorem RecState.Frame.export_mono_prefixes {state : RecState} {i : Nat}
    (h : state.Frame base K F ctx anns done)
    (hs : state.specs[i]? = some (.mono ty)) (hd : i ∈ done) :
    state.exports[i]? = some (some (recScheme (state.prefixes[i]?.getD []) state.pool ty)) := by
  obtain ⟨names, hslots, _, _, _, hex⟩ := if_pos hd ▸ h.mono i ty hs
  have hp : state.prefixes[i]? = some names := by
    simp only [RecState.prefixes, List.getElem?_mapIdx, hs, Option.map_some, hslots, Option.getD_some]
    congr 1
    rw [List.filterMap_map]
    change names.filterMap some = names
    simp
  simpa only [hp, Option.getD_some] using hex

private theorem pool_renaming_lc {G Xs : List Nat} :
    ∀ p ∈ G.zip (Xs.map Ty.fvar), p.2.IsLC := by
  intro p hp
  obtain ⟨v, _, heq⟩ := List.mem_map.mp (List.of_mem_zip hp).2
  rw [← heq]
  exact .fvar

private theorem pool_renaming_image {G Xs : List Nat} (hG : G.Nodup) (hlen : Xs.length = G.length)
    (hGX : ∀ g ∈ G, g ∉ Xs) (hg : g ∈ G) :
    Subst.onTy (G.zip (Xs.map Ty.fvar)) (.fvar g) = .fvar ((Xs[G.idxOf g]?).getD g) := by
  have hi : G.idxOf g < Xs.length := by rw [hlen]; exact List.idxOf_lt_length_iff.mpr hg
  simpa only [List.getElem?_eq_getElem hi, Option.getD_some] using
    Ty.substFvars_zip_fvar_renameG hlen hG hGX (List.getElem?_idxOf hg) (List.getElem?_eq_getElem hi)

private theorem pool_renaming_images {G Xs names : List Nat} (hG : G.Nodup) (hlen : Xs.length = G.length)
    (hGX : ∀ g ∈ G, g ∉ Xs) (hn : ∀ g ∈ names, g ∈ G) :
    names.map (fun v => Subst.onTy (G.zip (Xs.map Ty.fvar)) (.fvar v)) =
      (recRenameNames G Xs names).map Ty.fvar := by
  simp only [recRenameNames, List.map_map]
  exact List.map_congr_left (fun v hv => pool_renaming_image hG hlen hGX (hn v hv))

private theorem recScheme_pool_fixed {G Xs names : List Nat} {ty : Ty} :
    Subst.onPolyTy (G.zip (Xs.map Ty.fvar)) (recScheme names G ty) = recScheme names G ty := by
  apply Subst.onPolyTy_eq_self_of_dom_avoids
  intro p hp hv
  exact Ty.not_mem_closeOver_freeVars
    (mem_recNames_of_mem_pool (List.of_mem_zip hp).1 (Ty.freeVars_closeOver_subset hv)) hv

private theorem RecState.Frame.stageCtx_rename {state : RecState} {earlier Xs : List Nat}
    (h : state.Frame base K F ctx anns done) (hdone : ∀ i ∈ earlier, i ∈ done) :
    Subst.onCtx (state.pool.zip (Xs.map Ty.fvar)) (state.stageCtx ctx earlier) =
      recStageCtx ctx state.specs state.prefixes earlier state.pool Xs := by
  have henv : Subst.onEnv (state.pool.zip (Xs.map Ty.fvar)) ctx.env = ctx.env :=
    Subst.onEnv_eq_self_of_fresh (fun p hp => h.pool_ctx p.1 (List.of_mem_zip hp).1)
  simp only [Subst.onCtx, RecState.stageCtx, recStageCtx, Subst.onEnv, List.map_append]
  congr 1
  congr 1
  · apply List.ext_getElem?
    intro i
    simp only [RecState.stageEntries, List.getElem?_map, List.getElem?_mapIdx, Option.map_map]
    cases hs : state.specs[i]? with
    | none => rfl
    | some spec =>
      simp only [Option.map_some, Option.some.injEq]
      cases spec with
      | poly scheme =>
        have hex := h.poly i scheme hs
        simp only [RecSpec.monoEntry, recStageEntry, hex, Option.join_some, Option.getD_some]
        have hfixed : Subst.onPolyTy (state.pool.zip (Xs.map Ty.fvar)) scheme = scheme :=
          Subst.onPolyTy_eq_self_of_dom_avoids (fun p hp => h.pool_poly scheme ⟨i, hs⟩ p.1 (List.of_mem_zip hp).1)
        split <;> exact hfixed
      | mono ty =>
        by_cases hi : i ∈ earlier
        · have hex := h.export_mono_prefixes hs (hdone i hi)
          simp only [hi, if_pos, hex, Option.join_some, Option.getD_some, recStageEntry]
          exact recScheme_pool_fixed
        · simp only [hi, RecSpec.monoEntry, recStageEntry]
          rfl

private theorem recFits_of_images {ann : BindingAnn} {names fresh : List Nat} {ty : Ty} {R : Subst}
    (h : ann.RecFits names ty) (hR : ∀ p ∈ R, p.2.IsLC)
    (hfix : ∀ v ∈ ann.rigidVars, R.onTy (.fvar v) = .fvar v)
    (him : names.map (fun v => R.onTy (.fvar v)) = fresh.map Ty.fvar)
    (hlen : fresh.length = names.length) : ann.RecFits fresh (R.onTy ty) := by
  cases ann with
  | absent => trivial
  | complete sigma => exact False.elim h
  | template tpl =>
    have ht := h.substTyFvars R
    rw [tpl.substTyFvars_eq_self_of_fixes hfix] at ht
    exact ht
  | partialForall count tpl =>
    refine ⟨hlen.trans h.1, ?_⟩
    have ht := h.2.substTyFvars R
    rw [TyTemplate.substTyFvars_openTyVarsFrom_of_images tpl hR him 0,
      tpl.substTyFvars_eq_self_of_fixes hfix] at ht
    exact ht

private theorem RecState.InputTrace.cofinite {state : RecState} {bindings : List InferInput}
    (h : state.InputTrace (K ++ softVars F) ctx anns bindings groups)
    (hf : state.Frame base K F ctx anns groups.flatten)
    (hvalid : RecGroups.ValidResidualGroups (anns.map BindingAnn.recModeAnn) (bindings.map InferInput.erase) groups)
    (hAnn : ∀ ann ∈ anns, ∀ v ∈ ann.rigidVars, v ∈ K ++ softVars F)
    (hRhs : ∀ rhs ∈ bindings, ∀ v ∈ rhs.rigidVars, v ∈ K ++ softVars F)
    {stage : Nat} {component : List Nat} (hc : groups[stage]? = some component)
    (Xs : List Nat) (hXs : FreshNames (state.pool ++ L) state.pool.length Xs)
    {i : Nat} {rhs : InferInput} {ann : BindingAnn} {names : List Nat} {ty : Ty}
    (hi : i ∈ component) (hr : bindings[i]? = some rhs) (ha : anns[i]? = some ann)
    (hn : state.prefixes[i]? = some names) (ht : state.specs[i]? = some (.mono ty)) :
    ann.RecFits (recRenameNames state.pool Xs names) (Ty.renameG state.pool Xs ty) ∧
    InputTyping ((K ++ softVars F) ++ Xs)
      (recStageCtx ctx state.specs state.prefixes (groups.take stage).flatten state.pool Xs)
      (rhs.openTyVars (recRenameNames state.pool Xs names)) (Ty.renameG state.pool Xs ty) := by
  let R : Subst := state.pool.zip (Xs.map Ty.fvar)
  have hRlc : ∀ p ∈ R, p.2.IsLC := pool_renaming_lc
  have hGX : ∀ g ∈ state.pool, g ∉ Xs := fun g hg hx =>
    hXs.avoid g hx (List.mem_append_left _ hg)
  have hQavoid : ∀ g ∈ state.pool, g ∉ K ++ softVars F := by
    intro g hg hm
    exact (List.mem_append.mp hm).elim (hf.pool_rigid g hg) (hf.pool_soft g hg)
  have hQfix : ∀ q ∈ K ++ softVars F, R.onTy (.fvar q) = .fvar q :=
    Subst.fixes_of_dom_avoids (fun p hp => hQavoid p.1 (List.of_mem_zip hp).1)
  obtain ⟨hfit, htyped⟩ := h stage component hc i ann rhs ty hi ha hr ht
  simp only [hn, Option.getD_some] at hfit htyped
  have hprefix := (hf.prefixes_wf hvalid).member i ann names ha hn
  have himages := pool_renaming_images hf.pool_nodup hXs.length hGX hprefix.2.2
  have hfixAnn : ∀ v ∈ ann.rigidVars, R.onTy (.fvar v) = .fvar v :=
    fun v hv => hQfix v (hAnn ann (List.mem_of_getElem? ha) v hv)
  refine ⟨recFits_of_images hfit hRlc hfixAnn himages (recRenameNames_length _ _ _), ?_⟩
  have hsource := htyped.onSubst_source R hRlc (K' := (K ++ softVars F) ++ Xs) (by
    intro k hk v hv
    rcases List.mem_append.mp hk with hk | hk
    · rw [hQfix k hk] at hv
      exact List.mem_append_left _ ((List.mem_singleton.mp hv) ▸ hk)
    · have hkG := hprefix.2.2 k hk
      have hindex : state.pool.idxOf k < Xs.length := by
        rw [hXs.length]; exact List.idxOf_lt_length_iff.mpr hkG
      rw [pool_renaming_image hf.pool_nodup hXs.length hGX hkG,
        List.getElem?_eq_getElem hindex, Option.getD_some] at hv
      exact List.mem_append_right _ ((List.mem_singleton.mp hv) ▸ List.getElem_mem hindex))
  have hstage := hf.stageCtx_rename (Xs := Xs) (earlier := (groups.take stage).flatten) (by
    intro j hj
    obtain ⟨component, hm, hj⟩ := List.mem_flatten.mp hj
    exact List.mem_flatten.mpr ⟨component, List.mem_of_mem_take hm, hj⟩)
  rw [hstage, rhs.substTyFvars_openTyVars_of_images hRlc himages,
    rhs.substTyFvars_eq_self_of_fixes (fun v hv => hQfix v (hRhs rhs (List.mem_of_getElem? hr) v hv))] at hsource
  exact hsource

 theorem RecState.InputTrace.toTyping {state : RecState} {bindings : List InferInput} {L : List Nat}
    (hf : state.Frame base K F ctx anns groups.flatten) (hlc : state.LC)
    (hvalid : RecGroups.ValidResidualGroups (anns.map BindingAnn.recModeAnn) (bindings.map InferInput.erase) groups)
    (hAnn : ∀ ann ∈ anns, ∀ v ∈ ann.rigidVars, v ∈ K ++ softVars F)
    (hRhs : ∀ rhs ∈ bindings, ∀ v ∈ rhs.rigidVars, v ∈ K ++ softVars F)
    (htrace : state.InputTrace (K ++ softVars F) ctx anns bindings groups)
    (hpoly : ∀ (i : Nat) (rhs : InferInput) (scheme : PolyTy), bindings[i]? = some rhs →
      state.specs[i]? = some (.poly scheme) → ∀ Ys, FreshNames L scheme.paramCount Ys →
        InputTyping ((K ++ softVars F) ++ Ys) (recBodyCtx ctx state.specs state.prefixes state.pool)
          (rhs.openTyVars Ys) (scheme.openVars Ys))
    (hbody : InputTyping (K ++ softVars F) (recBodyCtx ctx state.specs state.prefixes state.pool) body ty) :
    InputTyping (K ++ softVars F) ctx (.letRec anns bindings body) ty := by
  have hwf : RecSpecs.WF (anns.map BindingAnn.recModeAnn) (bindings.map InferInput.erase) state.specs state.pool := by
    refine ⟨hf.modes, ?_, hf.pool_nodup, fun ty ht => hlc.1 _ ht, fun scheme hs => hlc.1 _ hs⟩
    rw [List.length_map, hf.specs_length]
    exact (show anns.length = bindings.length by simpa only [List.length_map] using hvalid.length).symm
  refine InputTyping.letRec (specs := state.specs) (prefixes := state.prefixes) (groups := groups)
    (G := state.pool) (L := L) hvalid hwf (hf.prefixes_wf hvalid) ?_ hAnn hRhs ?_ ?_ hpoly hbody
  · intro g hg hm
    rcases List.mem_append.mp hm with hm | hm
    · exact hf.pool_ctx g hg hm
    · exact (List.mem_append.mp hm).elim (hf.pool_rigid g hg) (hf.pool_soft g hg)
  · intro stage component hc Xs hXs i hi rhs ann names ty hr ha hn ht
    exact (htrace.cofinite hf hvalid hAnn hRhs hc Xs hXs hi hr ha hn ht).1
  · intro stage component hc Xs hXs i hi rhs ann names ty hr ha hn ht
    exact (htrace.cofinite hf hvalid hAnn hRhs hc Xs hXs hi hr ha hn ht).2


private theorem trace_prefix_lookup {state : RecState} {i : Nat} {ty : Ty} {names : List Nat}
    (hs : state.specs[i]? = some (.mono ty))
    (hn : state.slots[i]? = some (names.map Ty.fvar)) :
    state.prefixes[i]? = some names := by
  simp only [RecState.prefixes, List.getElem?_mapIdx, hs, Option.map_some, hn, Option.getD_some]
  congr 1
  clear hs hn
  induction names with
  | nil => rfl
  | cons n ns ih => change n :: _ = n :: _; exact congrArg (n :: ·) ih

 theorem RecState.InputTrace.onSubst {state : RecState} {past : List (List Nat)}
    (hframe : state.Frame base K F ctx anns past.flatten)
    (h : state.InputTrace (K ++ softVars F) ctx anns bindings past)
    (S : Subst) (hlc : ∀ p ∈ S, p.2.IsLC)
    (hK : ∀ k ∈ K, S.onTy (.fvar k) = .fvar k)
    (hpool : ∀ g ∈ state.pool, (∀ p ∈ S, g ∉ p.2.freeVars) ∧ g ∉ S.map Prod.fst) :
    (state.onSubst S).InputTrace (K ++ softVars (substSoft S F)) (S.onCtx ctx)
      (anns.map (BindingAnn.substTyFvars S)) (bindings.map (InferInput.substTyFvars S)) past := by
  intro stage component hc i ann rhs ty hi ha hr ht
  obtain ⟨ann0, ha0, rfl⟩ := Option.map_eq_some_iff.mp (by simpa only [List.getElem?_map] using ha)
  obtain ⟨rhs0, hr0, rfl⟩ := Option.map_eq_some_iff.mp (by simpa only [List.getElem?_map] using hr)
  obtain ⟨ty0, ht0, rfl⟩ := RecSpec.mono_getElem?_map_onSubstSource ht
  have hidone : i ∈ past.flatten := List.mem_flatten.mpr ⟨component, List.mem_of_getElem? hc, hi⟩
  obtain ⟨names, hnames, _, _, hsub, _⟩ := if_pos hidone ▸ hframe.mono i ty0 ht0
  have hfix : ∀ v ∈ names, S.onTy (.fvar v) = .fvar v := by
    intro v hv
    apply Ty.substFvars_eq_self_of_no_key
    intro pair hp hk
    have heq : pair.1 = v := List.mem_singleton.mp hk
    exact (hpool v (hsub v hv)).2 (List.mem_map.mpr ⟨pair, hp, heq⟩)
  have hnewnames : (state.onSubst S).slots[i]? = some (names.map Ty.fvar) := by
    simp only [RecState.onSubst, List.getElem?_map, hnames, Option.map_some, List.map_map]
    congr 1
    exact List.map_congr_left (fun v hv => hfix v hv)
  have hprefix := trace_prefix_lookup ht0 hnames
  have hnewprefix := trace_prefix_lookup ht hnewnames
  obtain ⟨hfits, htyping⟩ := h stage component hc i ann0 rhs0 ty0 hi ha0 hr0 ht0
  simp only [hprefix, Option.getD_some] at hfits htyping
  simp only [hnewprefix, Option.getD_some]
  refine ⟨hfits.onSubst_source S hlc hfix, ?_⟩
  have htypingS := htyping.onSubst_source S hlc (K' := (K ++ softVars (substSoft S F)) ++ names)
    (fun k hk v hv => by
      rcases List.mem_append.mp hk with hk | hk
      · exact List.mem_append_left _ (scope_image hK hk hv)
      · rw [hfix k hk] at hv
        exact List.mem_append_right _ ((List.mem_singleton.mp hv) ▸ hk))
  rw [RecState.stageCtx_onSubst]
  simpa only [InferInput.substTyFvars_openTyVars_of_fixes _ hlc hfix] using htypingS


 theorem _root_.InferRecComponent.inputSound_of_infer
    (h : InferRecComponent K F members index frontier ctx bindings specs next S outputs facts)
    (hInfer : ∀ {κ F' Ψ c e Ψ' T output ty}, e.size ≤ sizeBindings bindings →
      Infer κ F' Ψ c e Ψ' T output ty → CtxWF c →
      InputTyping (κ ++ softVars (substSoft T F')) (T.onCtx c) (e.substTyFvars T) ty)
    (hctx : CtxWF ctx) (hspec : ∀ spec ∈ specs, spec.LC) :
    ∀ (j : Nat) (rhs : InferInput) (target : Ty), index + j ∈ members →
      bindings[j]? = some rhs → specs[j]? = some (.mono target) →
      InputTyping (K ++ softVars (substSoft S F)) (S.onCtx ctx)
        (rhs.substTyFvars S) (S.onTy target) := by
  match h with
  | .nil => intro j rhs target _ hr; simp at hr
  | .skipMono hn hr =>
    intro j rhs target hj hb ht
    cases j with
    | zero => exact False.elim (hn (by simpa only [Nat.add_zero] using hj))
    | succ j =>
      exact hr.inputSound_of_infer
        (fun he hi => hInfer (by simp only [sizeBindings]; omega) hi)
        hctx (fun spec hm => hspec spec (List.mem_cons_of_mem _ hm)) j rhs target
        (by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hj) hb ht
  | .skipPoly hr =>
    intro j rhs target hj hb ht
    cases j with
    | zero => cases ht
    | succ j =>
      exact hr.inputSound_of_infer
        (fun he hi => hInfer (by simp only [sizeBindings]; omega) hi)
        hctx (fun spec hm => hspec spec (List.mem_cons_of_mem _ hm)) j rhs target
        (by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hj) hb ht
  | .consSelected hm hi hu hr =>
    expose_names
    obtain ⟨hiTy, hiS⟩ := hi.lc hctx
    have huS := hu.unifies.lc hiTy (Subst.onTy_lc hiS (hspec _ List.mem_cons_self))
    have hS12 : ∀ p ∈ s1 ++ s2, p.2.IsLC := fun p hp => (List.mem_append.mp hp).elim (hiS p) (huS p)
    have hrCtx := Subst.onCtx_wf huS (Subst.onCtx_wf hiS hctx)
    have hrSpec : ∀ spec ∈ specs_1.map (RecSpec.onSubstSource (s1 ++ s2)), spec.LC := by
      intro spec hm
      obtain ⟨old, hold, rfl⟩ := List.mem_map.mp hm
      exact RecSpec.lc_onSubstSource hS12 (hspec old (List.mem_cons_of_mem _ hold))
    have hrLC := hr.lc_of_infer (fun _ hi => hi.lc) hrCtx hrSpec
    intro j rhs target hj hb ht
    cases j with
    | zero =>
      cases Option.some.inj hb
      cases Option.some.inj ht
      have hrestLC : ∀ p ∈ s2 ++ s3, p.2.IsLC := fun p hp => (List.mem_append.mp hp).elim (huS p) (hrLC p)
      have hrestFix : ∀ k ∈ K, (s2 ++ s3).onTy (.fvar k) = .fvar k :=
        Subst.fixes_of_dom_avoids (fun p hp => (List.mem_append.mp hp).elim (hu.dom_avoids p) (hr.dom_avoids p))
      have htyping := (hInfer (by simp only [sizeBindings]; omega) hi hctx).onSubst_source (s2 ++ s3) hrestLC
        (fun k hk v hv => scope_image hrestFix hk hv)
      have heq := congrArg s3.onTy hu.unifies.unifies
      rw [Subst.onTy_append] at htyping
      rw [heq] at htyping
      simpa only [Subst.onCtx_append, Subst.onTy_append, List.append_assoc,
        ← substSoft_append, ← InferInput.substTyFvars_append] using htyping
    | succ j =>
      simp only [List.getElem?_cons_succ] at hb ht
      have htail := hr.inputSound_of_infer
        (fun he hi => hInfer (by simp only [sizeBindings_map_substTyFvars] at he; simp only [sizeBindings]; omega) hi)
        hrCtx hrSpec j (rhs.substTyFvars (s1 ++ s2)) ((s1 ++ s2).onTy target)
        (by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hj)
        (by simp only [List.getElem?_map, hb, Option.map_some])
        (by simp only [List.getElem?_map, ht, Option.map_some, RecSpec.onSubstSource])
      simpa only [← substSoft_append, Subst.onCtx_append, Subst.onTy_append, ← InferInput.substTyFvars_append] using htail
 termination_by structural h


/-- Signed recursive RHS checks already completed during the positional scan.
One cofinite avoidance list covers the finite checked prefix. -/
def RecState.CompleteInput (Q : List Nat) (ctx : Ctx) (anns : List BindingAnn)
    (bindings : List InferInput) (checked : Nat) (state : RecState) : Prop :=
  ∃ L, ∀ (i : Nat) (scheme : PolyTy) (rhs : InferInput), i < checked →
    anns[i]? = some (.complete scheme) → bindings[i]? = some rhs →
    ∀ Xs, FreshNames L scheme.paramCount Xs →
      InputTyping (Q ++ Xs) (state.rhsCtx ctx) (rhs.openTyVars Xs) (scheme.openVars Xs)

 theorem RecState.CompleteInput.init {state : RecState} {Q : List Nat} {ctx : Ctx}
    {anns : List BindingAnn} {bindings : List InferInput} : state.CompleteInput Q ctx anns bindings 0 :=
  ⟨[], fun _ _ _ hi => False.elim (by omega)⟩

 theorem RecState.CompleteInput.onSubst {state : RecState} {Q Q' : List Nat}
    (h : state.CompleteInput Q ctx anns bindings checked) (S : Subst)
    (hS : ∀ p ∈ S, p.2.IsLC)
    (hscope : ∀ k ∈ Q, ∀ v ∈ (S.onTy (.fvar k)).freeVars, v ∈ Q') :
    (state.onSubst S).CompleteInput Q' (S.onCtx ctx)
      (anns.map (BindingAnn.substTyFvars S)) (bindings.map (InferInput.substTyFvars S)) checked := by
  obtain ⟨L, hh⟩ := h
  refine ⟨L ++ S.map Prod.fst, ?_⟩
  intro i scheme rhs hi hann hrhs Xs hXs
  obtain ⟨oldAnn, ha, heq⟩ := Option.map_eq_some_iff.mp (by simpa only [List.getElem?_map] using hann)
  cases oldAnn with
  | absent | template | partialForall => cases heq
  | complete sigma =>
    cases BindingAnn.complete.inj heq
    obtain ⟨oldRhs, hr, heq⟩ := Option.map_eq_some_iff.mp (by simpa only [List.getElem?_map] using hrhs)
    cases heq
    have hf : FreshNames L sigma.paramCount Xs :=
      ⟨hXs.length, hXs.nodup, fun v hv hm => hXs.avoid v hv (List.mem_append_left _ hm)⟩
    have hdom : ∀ p ∈ S, p.1 ∉ Xs := fun p hp hx =>
      hXs.avoid p.1 hx (List.mem_append_right _ (List.mem_map.mpr ⟨p, hp, rfl⟩))
    have hfix := Subst.fixes_of_dom_avoids hdom
    have ht := (hh i sigma oldRhs hi ha hr Xs hf).onSubst_source S hS
      (K' := Q' ++ Xs) (by
        intro k hk v hv
        rcases List.mem_append.mp hk with hk | hk
        · exact List.mem_append_left _ (hscope k hk v hv)
        · rw [hfix k hk] at hv
          exact List.mem_append_right _ ((List.mem_singleton.mp hv) ▸ hk))
    simpa only [RecState.rhsCtx_onSubst, InferInput.substTyFvars_openTyVars_of_fixes _ hS hfix,
      PolyTy.openVars, Subst.onPolyTy, Subst.onTy_openVars hS hdom] using ht


/-- Aligned completed members retain exact authored-prefix/full-output openings. -/
def RecState.Fidelity (Q : List Nat) (anns : List BindingAnn) (bindings : List InferInput) (state : RecState) : Prop :=
  ∀ (i : Nat) (ann : BindingAnn) (rhs : InferInput) (scheme : PolyTy) (output : Expr),
    anns[i]? = some ann → bindings[i]? = some rhs →
    state.exports[i]? = some (some scheme) → state.outputs[i]? = some (some output) →
    ∃ L, ∀ Xs, FreshNames L scheme.paramCount Xs →
      ann.BindingFits scheme Xs ∧
      AnnotationCompletion (Q ++ Xs.take ann.paramCount) (rhs.openTyVars (Xs.take ann.paramCount))
        (output.openTyVars Xs)

theorem RecState.Fidelity.init {anns : List BindingAnn} {bindings : List InferInput} :
    (RecState.init base anns).Fidelity Q anns bindings := by
  intro i ann rhs scheme output ha hb he ho
  simp only [RecState.init, List.getElem?_map] at ho
  obtain ⟨old, _, heq⟩ := Option.map_eq_some_iff.mp ho
  cases heq

theorem RecState.Fidelity.onSubst_source {state : RecState} {S : Subst}
    (h : state.Fidelity Q anns bindings) (hS : ∀ p ∈ S, p.2.IsLC)
    (hscope : ∀ q ∈ Q, ∀ v ∈ (S.onTy (.fvar q)).freeVars, v ∈ Q') :
    (state.onSubst S).Fidelity Q' (anns.map (BindingAnn.substTyFvars S))
      (bindings.map (InferInput.substTyFvars S)) := by
  intro i ann rhs scheme output ha hb he ho
  rw [List.getElem?_map] at ha hb
  obtain ⟨oldAnn, hAnn, rfl⟩ := Option.map_eq_some_iff.mp ha
  obtain ⟨oldRhs, hRhs, rfl⟩ := Option.map_eq_some_iff.mp hb
  rw [RecState.onSubst, List.getElem?_map] at he ho
  obtain ⟨oldExport, hExport, hScheme⟩ := Option.map_eq_some_iff.mp he
  obtain ⟨oldOutput, hOutput, hOut⟩ := Option.map_eq_some_iff.mp ho
  cases oldExport with
  | none => cases hScheme
  | some oldScheme =>
    cases Option.some.inj hScheme
    cases oldOutput with
    | none => cases hOut
    | some oldOutput =>
      cases Option.some.inj hOut
      obtain ⟨L, hL⟩ := h i oldAnn oldRhs oldScheme oldOutput hAnn hRhs hExport hOutput
      obtain ⟨Lc, hLc⟩ := AnnotationCompletion.signatureBinding_onSubst_source
        (ann := oldAnn) (M := oldScheme) (fun Xs hf => (hL Xs hf).2) S hS hscope
      refine ⟨(L ++ S.map Prod.fst) ++ Lc, ?_⟩
      intro Xs hf
      have hfOld : FreshNames L oldScheme.paramCount Xs :=
        ⟨hf.length, hf.nodup, fun v hv hm => hf.avoid v hv
          (List.mem_append_left _ (List.mem_append_left _ hm))⟩
      have hdom : ∀ p ∈ S, p.1 ∉ Xs := fun p hp hv =>
        hf.avoid p.1 hv (List.mem_append_left _
          (List.mem_append_right _ (List.mem_map.mpr ⟨p, hp, rfl⟩)))
      refine ⟨(hL Xs hfOld).1.onSubst_source S hS hdom, ?_⟩
      simpa only [BindingAnn.paramCount_substTyFvars] using hLc Xs
        ⟨hf.length, hf.nodup, fun v hv hm => hf.avoid v hv (List.mem_append_right _ hm)⟩

 theorem RecState.Fidelity.toCompletes {state : RecState} {schemes : List PolyTy} {outputs : List Expr}
    (h : state.Fidelity Q anns bindings)
    (hAnnLen : anns.length = schemes.length) (hRhsLen : bindings.length = schemes.length)
    (hOutLen : outputs.length = schemes.length)
    (hExports : state.exports = schemes.map some) (hOutputs : state.outputs = outputs.map some)
    (hAnn : ∀ ann ∈ anns, ∀ v ∈ ann.rigidVars, v ∈ Q)
    (hRhs : ∀ rhs ∈ bindings, ∀ v ∈ rhs.rigidVars, v ∈ Q)
    (hbody : AnnotationCompletion Q body bodyOut) :
    AnnotationCompletion Q (.letRec anns bindings body) (.letRec (schemes.map some) outputs bodyOut) := by
  classical
  have hper : ∀ i : Fin schemes.length, ∃ L, ∀ Xs, FreshNames L (schemes[i.val]).paramCount Xs →
      (anns[i.val]'(by have := i.isLt; omega)).BindingFits schemes[i.val] Xs ∧
      AnnotationCompletion (Q ++ Xs.take (anns[i.val]'(by have := i.isLt; omega)).paramCount)
        ((bindings[i.val]'(by have := i.isLt; omega)).openTyVars
          (Xs.take (anns[i.val]'(by have := i.isLt; omega)).paramCount))
        ((outputs[i.val]'(by have := i.isLt; omega)).openTyVars Xs) := by
    intro i
    exact h i.val _ _ _ _ (List.getElem?_eq_getElem _) (List.getElem?_eq_getElem _)
      (by simp only [hExports, List.getElem?_map, List.getElem?_eq_getElem i.isLt, Option.map_some])
      (by simp only [hOutputs, List.getElem?_map, List.getElem?_eq_getElem (show i.val < outputs.length by omega), Option.map_some])
  choose avoid hav using hper
  let L := (List.finRange schemes.length).flatMap avoid
  have hall : ∀ (i : Nat) (ann : BindingAnn) (rhs : InferInput) (output : Expr) (scheme : PolyTy),
      anns[i]? = some ann → bindings[i]? = some rhs → outputs[i]? = some output → schemes[i]? = some scheme →
      ∀ Xs, FreshNames L scheme.paramCount Xs →
        ann.BindingFits scheme Xs ∧ AnnotationCompletion (Q ++ Xs.take ann.paramCount)
          (rhs.openTyVars (Xs.take ann.paramCount)) (output.openTyVars Xs) := by
    intro i ann rhs output scheme ha hb ho hs Xs hXs
    have hi : i < schemes.length := (List.getElem?_eq_some_iff.mp hs).1
    let j : Fin schemes.length := ⟨i, hi⟩
    have ha' := List.getElem?_eq_getElem (show i < anns.length by omega)
    have hb' := List.getElem?_eq_getElem (show i < bindings.length by omega)
    have ho' := List.getElem?_eq_getElem (show i < outputs.length by omega)
    have hs' := List.getElem?_eq_getElem hi
    have heqa := Option.some.inj (ha'.symm.trans ha)
    have heqb := Option.some.inj (hb'.symm.trans hb)
    have heqo := Option.some.inj (ho'.symm.trans ho)
    have heqs := Option.some.inj (hs'.symm.trans hs)
    subst ann rhs output scheme
    exact hav j Xs ⟨hXs.length, hXs.nodup, fun v hv hm => hXs.avoid v hv
      (List.mem_flatMap.mpr ⟨j, by simp, hm⟩)⟩
  exact AnnotationCompletion.letRec (L := L) hAnnLen hRhsLen hOutLen hAnn hRhs
    (fun i ann rhs output scheme ha hb ho hs Xs hXs => (hall i ann rhs output scheme ha hb ho hs Xs hXs).1)
    (fun i ann rhs output scheme ha hb ho hs Xs hXs => (hall i ann rhs output scheme ha hb ho hs Xs hXs).2) hbody

 theorem BindingAnn.RecFits.cofinite_fidelity
    {ann : BindingAnn} {written pool Q : List Nat} {ty : Ty} {rhs : InferInput} {output : Expr}
    (hfit : ann.RecFits written ty) (hcount : written.length = ann.recPrefixCount)
    (hnd : written.Nodup) (hsub : ∀ v ∈ written, v ∈ pool) (hpool : pool.Nodup)
    (hlc : ty.IsLC) (hAnn : ∀ v ∈ ann.rigidVars, v ∈ Q)
    (hRhs : ∀ v ∈ rhs.rigidVars, v ∈ Q) (havoid : ∀ v ∈ pool, v ∉ Q)
    (hcomplete : AnnotationCompletion (Q ++ written) (rhs.openTyVars written) output)
    (hbound : output.TyBvarBounded 0) :
    ∃ L, ∀ Xs, FreshNames L (recScheme written pool ty).paramCount Xs →
      ann.BindingFits (recScheme written pool ty) Xs ∧
      AnnotationCompletion (Q ++ Xs.take ann.paramCount) (rhs.openTyVars (Xs.take ann.paramCount))
        ((output.closeTyVars (recNames written pool ty)).openTyVars Xs) := by
  have hparam : written.length = ann.paramCount := by
    cases ann with
    | absent | template | partialForall => exact hcount
    | complete => cases hfit
  have hnames := recNames_nodup (ty := ty) hnd hpool
  have hnamesQ : ∀ v ∈ recNames written pool ty, v ∉ Q := by
    intro v hv
    rcases mem_recNames.mp hv with hv | ⟨hv, _, _⟩
    · exact havoid v (hsub v hv)
    · exact havoid v hv
  obtain ⟨Lf, hf⟩ := hfit.cofinite_bindingFits hcount hnd hsub hpool hlc hAnn havoid
  obtain ⟨Lc, hc⟩ := hcomplete.generalise_opened (G := pool.filter
    (fun v => decide (v ∈ ty.freeVars) && decide (v ∉ written))) hnames hnamesQ hRhs hbound
  refine ⟨Lf ++ Lc, ?_⟩
  intro Xs hXs
  refine ⟨hf Xs ⟨hXs.length, hXs.nodup, fun v hv hm => hXs.avoid v hv (List.mem_append_left _ hm)⟩, ?_⟩
  have hXsC : FreshNames Lc
      (written.length + (pool.filter (fun v => decide (v ∈ ty.freeVars) && decide (v ∉ written))).length) Xs :=
    ⟨by simpa only [recScheme, recNames, List.length_append] using hXs.length,
      hXs.nodup, fun v hv hm => hXs.avoid v hv (List.mem_append_right _ hm)⟩
  simpa only [hparam] using hc Xs hXsC

 theorem RecState.Fidelity.exportComponent {state : RecState} {members pool : List Nat}
    {written : List (List Nat)} {outputs : List (Option Expr)} {facts : List RecFacts}
    (h : state.Fidelity Q anns bindings) (hlc : state.LC)
    (hpool : pool.Nodup) (havoid : ∀ v ∈ pool, v ∉ Q)
    (hAnn : ∀ ann ∈ anns, ∀ v ∈ ann.rigidVars, v ∈ Q)
    (hRhs : ∀ rhs ∈ bindings, ∀ v ∈ rhs.rigidVars, v ∈ Q)
    (hprefix : ∀ i ∈ members,
      (written[i]?.getD []).length = (anns[i]?.getD .absent).recPrefixCount ∧
      (written[i]?.getD []).Nodup ∧ ∀ v ∈ written[i]?.getD [], v ∈ pool)
    (hcheck : ∀ (i : Nat) (ann : BindingAnn) (rhs : InferInput) (ty : Ty) (output : Expr),
      i ∈ members → anns[i]? = some ann → bindings[i]? = some rhs →
      state.specs[i]? = some (.mono ty) → (outputs[i]?).join = some output →
      ann.RecFits (written[i]?.getD []) ty ∧
      AnnotationCompletion (Q ++ written[i]?.getD []) (rhs.openTyVars (written[i]?.getD [])) output ∧
      output.TyBvarBounded 0) :
    (state.exportComponent members written pool outputs facts).Fidelity Q anns bindings := by
  intro i ann rhs scheme output ha hb he ho
  simp only [RecState.exportComponent, List.getElem?_mapIdx] at he ho
  obtain ⟨oldExport, hExport, heq⟩ := Option.map_eq_some_iff.mp he
  obtain ⟨oldOutput, hOutput, hout⟩ := Option.map_eq_some_iff.mp ho
  by_cases hi : i ∈ members
  · simp only [if_pos hi] at heq hout
    cases hspec : state.specs[i]? with
    | none => simp [hspec] at heq
    | some spec =>
      cases spec with
      | poly sigma => simp [hspec, RecSpec.monoTy?] at hout
      | mono ty =>
        rw [hspec] at heq
        have hscheme : recScheme (written[i]?.getD []) pool ty = scheme := Option.some.inj heq
        subst scheme
        rw [hspec] at hout
        change ((outputs[i]?).join.bind (fun raw => some (raw.closeTyVars (recNames (written[i]?.getD []) pool ty)))) = some output at hout
        obtain ⟨raw, hraw, hclose⟩ := Option.bind_eq_some_iff.mp hout
        cases Option.some.inj hclose
        obtain ⟨hfit, hcomplete, hbound⟩ := hcheck i ann rhs ty raw hi ha hb hspec hraw
        have hp := hprefix i hi
        have hcount : (written[i]?.getD []).length = ann.recPrefixCount := by
          simpa only [ha, Option.getD_some] using hp.1
        exact hfit.cofinite_fidelity hcount hp.2.1 hp.2.2 hpool
          (hlc.1 _ (List.mem_of_getElem? hspec)) (hAnn ann (List.mem_of_getElem? ha))
          (hRhs rhs (List.mem_of_getElem? hb)) havoid hcomplete hbound
  · simp only [if_neg hi] at heq hout
    subst oldExport oldOutput
    exact h i ann rhs scheme output ha hb hExport hOutput


 theorem _root_.InferRecComponent.completes_of_infer
    (h : InferRecComponent K F members index frontier ctx bindings specs next S outputs facts)
    (hInfer : ∀ {κ F' Ψ c e Ψ' T output ty}, e.size ≤ sizeBindings bindings →
      Infer κ F' Ψ c e Ψ' T output ty → CtxWF c →
      AnnotationCompletion (κ ++ softVars (substSoft T F')) (e.substTyFvars T) output)
    (hctx : CtxWF ctx) (hspec : ∀ spec ∈ specs, spec.LC) :
    ∀ (j : Nat) (rhs : InferInput) (output : Expr), bindings[j]? = some rhs → outputs[j]? = some (some output) →
      AnnotationCompletion (K ++ softVars (substSoft S F)) (rhs.substTyFvars S) output := by
  match h with
  | .nil => intro j rhs output hb; simp at hb
  | .skipMono _ hr | .skipPoly hr =>
      intro j rhs output hb ho
      cases j with
      | zero => cases ho
      | succ j =>
        exact hr.completes_of_infer (fun he hi => hInfer (by simp only [sizeBindings]; omega) hi)
          hctx (fun spec hm => hspec spec (List.mem_cons_of_mem _ hm)) j rhs output hb ho
  | .consSelected _ hi hu hr =>
    expose_names
    obtain ⟨hiTy, hiS⟩ := hi.lc hctx
    have huS := hu.unifies.lc hiTy (Subst.onTy_lc hiS (hspec _ List.mem_cons_self))
    have hS12 : ∀ p ∈ s1 ++ s2, p.2.IsLC := fun p hp => (List.mem_append.mp hp).elim (hiS p) (huS p)
    have hrCtx := Subst.onCtx_wf huS (Subst.onCtx_wf hiS hctx)
    have hrSpec : ∀ spec ∈ specs_1.map (RecSpec.onSubstSource (s1 ++ s2)), spec.LC := by
      intro spec hm
      obtain ⟨old, hold, rfl⟩ := List.mem_map.mp hm
      exact RecSpec.lc_onSubstSource hS12 (hspec old (List.mem_cons_of_mem _ hold))
    have hrLC := hr.lc_of_infer (fun _ hi => hi.lc) hrCtx hrSpec
    intro j rhs output hb ho
    cases j with
    | zero =>
      cases Option.some.inj hb
      cases Option.some.inj (Option.some.inj ho)
      have hrestLC : ∀ p ∈ s2 ++ s3, p.2.IsLC := fun p hp => (List.mem_append.mp hp).elim (huS p) (hrLC p)
      have hrestFix : ∀ k ∈ K, (s2 ++ s3).onTy (.fvar k) = .fvar k :=
        Subst.fixes_of_dom_avoids (fun p hp => (List.mem_append.mp hp).elim (hu.dom_avoids p) (hr.dom_avoids p))
      have hcomplete := (hInfer (by simp only [sizeBindings]; omega) hi hctx).onSubst_source
        (s2 ++ s3) hrestLC (fun k hk v hv => scope_image hrestFix hk hv)
      simpa only [← substSoft_append, ← InferInput.substTyFvars_append, List.append_assoc] using hcomplete
    | succ j =>
      simp only [List.getElem?_cons_succ] at hb ho
      have htail := hr.completes_of_infer
        (fun he hi => hInfer (by simp only [sizeBindings_map_substTyFvars] at he; simp only [sizeBindings]; omega) hi)
        hrCtx hrSpec j (rhs.substTyFvars (s1 ++ s2)) output
        (by simp only [List.getElem?_map, hb, Option.map_some]) ho
      simpa only [← substSoft_append, ← InferInput.substTyFvars_append] using htail
 termination_by structural h


private theorem trace_stage_export {state : RecState}
    (hdisj : ∀ i ∈ earlier, i ∉ members) :
    (state.exportComponent members written pool outputs facts).stageCtx ctx earlier = state.stageCtx ctx earlier := by
  unfold RecState.stageCtx RecState.stageEntries
  congr 2
  apply List.ext_getElem?
  intro i
  simp only [List.getElem?_mapIdx]
  simp only [show (state.exportComponent members written pool outputs facts).specs = state.specs from rfl]
  cases hs : state.specs[i]? with
  | none => rfl
  | some spec =>
    simp only [Option.map_some]
    by_cases hm : i ∈ earlier
    · have hn := hdisj i hm
      have hh : (state.exportComponent members written pool outputs facts).exports[i]? = state.exports[i]? := by
        simp only [RecState.exportComponent, List.getElem?_mapIdx]
        cases hx : state.exports[i]? <;> simp only [Option.map_none,Option.map_some]
        simp only [if_neg hn]
      simp only [if_pos hm, hh]
    · simp only [if_neg hm]

private theorem trace_stage_all {state : RecState}
    (h : state.Frame base K F ctx anns done) : state.stageCtx ctx done = state.rhsCtx ctx := by
  unfold RecState.stageCtx RecState.rhsCtx
  congr 2
  apply List.ext_getElem
  · simp only [RecState.stageEntries, RecState.entries, List.length_mapIdx, List.length_map, List.length_zip]
    rw [h.exports_length, h.specs_length]
    omega
  · intro i hi hj
    have his : i < state.specs.length := by simpa only [RecState.stageEntries,List.length_mapIdx] using hi
    have hie : i < state.exports.length := by rw [h.exports_length,←h.specs_length];exact his
    have hs := List.getElem?_eq_getElem his
    have he := List.getElem?_eq_getElem hie
    simp only [RecState.stageEntries,RecState.entries,List.getElem_mapIdx,List.getElem_map,List.getElem_zip]
    cases hx : state.specs[i]'his with
    | poly M =>
      have hm := h.poly i M (hx ▸ hs)
      have heq : state.exports[i]'hie = some M := Option.some.inj (he.symm.trans hm)
      simp [hm,heq,RecSpec.monoEntry]
    | mono ty =>
      by_cases hd : i ∈ done
      · obtain ⟨ns, _, _, _, _, hm⟩ := if_pos hd ▸ h.mono i ty (hx ▸ hs)
        have heq : state.exports[i]'hie = some (recScheme ns state.pool ty) := Option.some.inj (he.symm.trans hm)
        simp [hd,hm,heq,RecSpec.monoEntry]
      · have hm := if_neg hd ▸ h.mono i ty (hx ▸ hs)
        have heq : state.exports[i]'hie = none := Option.some.inj (he.symm.trans hm)
        simp [hd,heq,RecSpec.monoEntry]

private theorem trace_install {state : RecState} {past : List (List Nat)}
    (hframe : state.Frame base K F ctx anns past.flatten)
    (h : state.InputTrace Q ctx anns bindings past)
    (hnot : ∀ i ∈ members, i ∉ past.flatten) :
    (state.installOpenings members openings).InputTrace Q ctx anns bindings past := by
  intro stage comp hc i ann rhs ty hi ha hr ht
  have hid : i ∈ past.flatten := List.mem_flatten.mpr ⟨comp,List.mem_of_getElem? hc,hi⟩
  obtain ⟨ns,hslot,_,_,_,_⟩ := if_pos hid ▸ hframe.mono i ty ht
  have hold := trace_prefix_lookup (state := state) ht hslot
  have hslotnew : (state.installOpenings members openings).slots[i]? = some (ns.map Ty.fvar) := by
    simp only [RecState.installOpenings,List.getElem?_mapIdx,hslot,Option.map_some,
      if_neg (show i ∉ members from fun hm => hnot i hm hid)]
  have hnew := trace_prefix_lookup (state := state.installOpenings members openings) ht hslotnew
  have hh := h stage comp hc i ann rhs ty hi ha hr ht
  simpa only [hnew,hold,Option.getD_some] using hh

private theorem trace_export {state : RecState} {past : List (List Nat)}
    (h : state.InputTrace Q ctx anns bindings past)
    (hnot : ∀ i ∈ members, i ∉ past.flatten) :
    (state.exportComponent members written pool outputs facts).InputTrace Q ctx anns bindings past := by
  intro stage comp hc i ann rhs ty hi ha hr ht
  have hh := h stage comp hc i ann rhs ty hi ha hr ht
  rw [trace_stage_export (fun j hj hm => hnot j hm (by
    obtain ⟨group,hgroup,hj⟩ := List.mem_flatten.mp hj
    exact List.mem_flatten.mpr ⟨group,List.mem_of_mem_take hgroup,hj⟩))]
  exact hh
theorem openRecSources_lookup {i : Nat} {rhs : InferInput} {opening : RecOpening} {openings : List RecOpening} {bindings : List InferInput}
    (hlen : openings.length = bindings.length)
    (hr : bindings[i]? = some rhs) (ho : openings[i]? = some opening) :
    (openRecSources openings bindings)[i]? = some (rhs.openTyVars opening.written) := by
  induction bindings generalizing openings i with
  | nil => simp at hr
  | cons b bs ih =>
    cases openings with
    | nil => simp at hlen
    | cons op ops =>
      cases i with
      | zero => cases Option.some.inj hr; cases Option.some.inj ho; rfl
      | succ i => exact ih (Nat.succ.inj hlen) hr ho

 theorem recStep_inputTrace
    {state : RecState}
    (ho : OpenRecAnns component 0 frontier anns opened openings)
    (hp : CheckRecShapes K ((state.installOpenings component openings).shapes component openings) pre)
    (hc : InferRecComponent K (substSoft pre (F ++ (openings.flatMap RecOpening.written).map Ty.fvar))
      component 0 opened (((state.installOpenings component openings).onSubst pre).rhsCtx (pre.onCtx ctx))
      ((openRecSources openings bindings).map (InferInput.substTyFvars pre))
      ((state.installOpenings component openings).onSubst pre).specs first current outputs facts)
    (hf : FinishRecComponent K (softVars (substSoft (pre ++ current) F)) component
      ((pre ++ current).onCtx ctx) ((state.installOpenings component openings).onSubst (pre ++ current))
      outputs facts exported)
    (hInfer : ∀ {κ F' Ψ c e Ψ' T output ty}, e.size ≤ sizeBindings bindings →
      Infer κ F' Ψ c e Ψ' T output ty →
      ∀ {w}, w < Ψ →
      e.erase.ForallOuter (fun i => ∀ M, c.env[i]? = some M → w ∉ M.body.freeVars) 0 →
      w ∉ e.rigidVars →
      (∀ p ∈ T, w ∉ p.2.freeVars) ∧ w ∉ ty.freeVars ∧ w ∉ T.map Prod.fst)
    (hvalid : RecGroups.ValidResidualGroups (anns.map BindingAnn.recModeAnn) (bindings.map InferInput.erase)
      (past ++ component :: rest))
    (hframe : state.Frame base K F ctx anns past.flatten)
    (hlc : state.LC) (hctx : CtxWF ctx)
    (hbelow : state.Below frontier) (hbase : base + bindings.length ≤ frontier)
    (hanns : ∀ ann ∈ anns, ∀ v ∈ ann.rigidVars, v ∈ K ++ softVars F)
    (hrhs : ∀ rhs ∈ bindings, ∀ v ∈ rhs.rigidVars, v ∈ K ++ softVars F)
    (hInput : ∀ {κ F' Ψ c e Ψ' T output ty}, e.size ≤ sizeBindings bindings →
      Infer κ F' Ψ c e Ψ' T output ty → CtxWF c →
      InputTyping (κ ++ softVars (substSoft T F')) (T.onCtx c) (e.substTyFvars T) ty)
    (hTrace : state.InputTrace (K ++ softVars F) ctx anns bindings past) :
    exported.InputTrace (K ++ softVars (substSoft (pre ++ current) F)) ((pre ++ current).onCtx ctx)
      (anns.map (BindingAnn.substTyFvars (pre ++ current)))
      (bindings.map (InferInput.substTyFvars (pre ++ current))) (past ++ [component]) := by
  obtain ⟨heframe,hpool,_⟩ := recStep_frame ho hp hc hf hInfer hvalid hframe hlc hctx hbelow hbase hanns hrhs
  have hnot : ∀ i ∈ component, i ∉ past.flatten := by
    intro i hi hd
    have hnd : (past.flatten ++ (component ++ rest.flatten)).Nodup := by
      simpa only [List.flatten_append,List.flatten_cons] using hvalid.flatten_nodup
    exact (List.nodup_append.mp hnd).2.2 i hd i (List.mem_append_left _ hi) rfl
  have hins := hframe.installOpenings (openings := openings) hnot
  have hinitLC := hlc.installOpenings (members := component) (openings := openings)
  have hpreLC := hp.lc (RecState.shapes_lc hinitLC ho.expected_lc)
  have hpreCtx := (hinitLC.onSubst hpreLC).rhsCtx (Subst.onCtx_wf hpreLC hctx)
  have hcurrentLC := hc.lc_of_infer (fun _ hi => hi.lc) hpreCtx (hinitLC.onSubst hpreLC).1
  have hSLC : ∀ p ∈ pre ++ current, p.2.IsLC :=
    fun p hm => (List.mem_append.mp hm).elim (hpreLC p) (hcurrentLC p)
  have hfixK : ∀ k ∈ K, (pre ++ current).onTy (.fvar k) = .fvar k :=
    Subst.fixes_of_dom_avoids (fun p hp' => (List.mem_append.mp hp').elim (hp.dom_avoids p) (hc.dom_avoids p))
  have hlength : anns.length = bindings.length := by simpa only [List.length_map] using hvalid.length
  have hcompInput := hc.inputSound_of_infer
    (fun he hi => hInput (by simpa only [sizeBindings_map_substTyFvars,sizeBindings_openRecSources] using he) hi)
    hpreCtx (hinitLC.onSubst hpreLC).1
  have hOld := (trace_install hframe hTrace hnot).onSubst hins (pre ++ current) hSLC hfixK hpool
  cases hf with
  | mk hresolve =>
    expose_names
    let st := (state.installOpenings component openings).onSubst (pre ++ current)
    have hOldEx := trace_export (members := component) (written := written)
      (pool := st.componentPool K (softVars (substSoft (pre ++ current) F)) component ((pre ++ current).onCtx ctx) written)
      (outputs := outputs) (facts := facts) hOld hnot
    have hStage : (st.exportComponent component written
        (st.componentPool K (softVars (substSoft (pre ++ current) F)) component ((pre ++ current).onCtx ctx) written)
        outputs facts).stageCtx ((pre ++ current).onCtx ctx) past.flatten = st.rhsCtx ((pre ++ current).onCtx ctx) := by
      rw [trace_stage_export (fun i hi hm => hnot i hm hi),RecState.stageCtx_onSubst,
        trace_stage_all hins,RecState.rhsCtx_onSubst]
    have hcurrent : ∀ i ann rhs ty, i ∈ component →
        anns[i]? = some ann → bindings[i]? = some rhs →
        st.specs[i]? = some (.mono ty) →
        (ann.substTyFvars (pre ++ current)).RecFits
          ((st.exportComponent component written
            (st.componentPool K (softVars (substSoft (pre ++ current) F)) component ((pre ++ current).onCtx ctx) written)
            outputs facts).prefixes[i]?.getD []) ty ∧
        InputTyping ((K ++ softVars (substSoft (pre ++ current) F)) ++
          (st.exportComponent component written
            (st.componentPool K (softVars (substSoft (pre ++ current) F)) component ((pre ++ current).onCtx ctx) written)
            outputs facts).prefixes[i]?.getD [])
          (st.rhsCtx ((pre ++ current).onCtx ctx))
          ((rhs.substTyFvars (pre ++ current)).openTyVars
            ((st.exportComponent component written
              (st.componentPool K (softVars (substSoft (pre ++ current) F)) component ((pre ++ current).onCtx ctx) written)
              outputs facts).prefixes[i]?.getD [])) ty := by
      intro i ann rhs ty hi ha hr ht
      obtain ⟨oldTy,ht0,rfl⟩ := RecSpec.mono_getElem?_map_onSubstSource ht
      have ht0' : state.specs[i]? = some (.mono oldTy) := ht0
      obtain ⟨ns,hslot,_,_,_,_⟩ := if_pos (List.mem_append_right _ hi) ▸ heframe.mono i _ ht
      have hprefix := trace_prefix_lookup (state := st) ht hslot
      change (ann.substTyFvars (pre ++ current)).RecFits (st.prefixes[i]?.getD []) ((pre ++ current).onTy oldTy) ∧
        InputTyping ((K ++ softVars (substSoft (pre ++ current) F)) ++ st.prefixes[i]?.getD [])
          (st.rhsCtx ((pre ++ current).onCtx ctx))
          ((rhs.substTyFvars (pre ++ current)).openTyVars (st.prefixes[i]?.getD [])) ((pre ++ current).onTy oldTy)
      simp only [hprefix,Option.getD_some]
      obtain ⟨a,b,opening,hop,hopen⟩ := OpenRecAnns.selected_lookup ho (by simpa using hi) ha
      have hislot : i < state.slots.length := by
        rw [hframe.slots_length,←hframe.specs_length]
        exact (List.getElem?_eq_some_iff.mp ht0').1
      have hslots : st.slots[i]? = some (opening.written.map (fun v => (pre ++ current).onTy (.fvar v))) := by
        simp only [st,RecState.onSubst,RecState.installOpenings,List.getElem?_map,List.getElem?_mapIdx,
          List.getElem?_eq_getElem hislot,Option.map_some,if_pos hi,hop,Option.getD_some,List.map_map,Function.comp_def]
      have himages : opening.written.map (fun v => (pre ++ current).onTy (.fvar v)) = ns.map Ty.fvar :=
        Option.some.inj (hslots.symm.trans hslot)
      have hmode : ann.recModeAnn = none := by
        have hh := congrArg (fun xs : List (Option PolyTy) => xs[i]?) hframe.modes
        simpa only [List.getElem?_map,ht0',ha,Option.map_some,RecSpec.ann,Option.some.injEq] using hh.symm
      refine ⟨hopen.recFits_of_images hmode hSLC himages ?_, ?_⟩
      · intro expected hex
        have hshape : (oldTy,some expected) ∈ (state.installOpenings component openings).shapes component openings := by
          apply List.mem_filterMap.mpr
          exact ⟨i,hi,by simp [RecState.installOpenings,ht0',RecSpec.monoTy?,hop,hex]⟩
        have hsolved := CheckRecShapes.solves hp hshape
        simpa only [Subst.onTy_append] using congrArg current.onTy hsolved
      · have hrOpened := openRecSources_lookup (ho.length.trans hlength) hr hop
        have hh := hcompInput i ((rhs.openTyVars opening.written).substTyFvars pre) (pre.onTy oldTy)
          (by simpa only [Nat.zero_add] using hi)
          (by simp only [List.getElem?_map,hrOpened,Option.map_some])
          (by simp only [RecState.onSubst,List.getElem?_map,ht0,Option.map_some,RecSpec.onSubstSource])
        have htyping : InputTyping (K ++ softVars (substSoft (pre ++ current) (F ++ (openings.flatMap RecOpening.written).map Ty.fvar))) (st.rhsCtx ((pre ++ current).onCtx ctx))
            ((rhs.substTyFvars (pre ++ current)).openTyVars ns) ((pre ++ current).onTy oldTy) := by
          dsimp only [st]
          rw [RecState.rhsCtx_onSubst]
          rw [RecState.rhsCtx_onSubst] at hh
          simpa only [← substSoft_append,Subst.onCtx_append,Subst.onTy_append,
            ← InferInput.substTyFvars_append,InferInput.substTyFvars_openTyVars_of_images _ hSLC himages] using hh
        exact htyping.scope_restrict
          ((rhs.substTyFvars (pre ++ current)).openTyVars_scope
            ((show SourceScope K F rhs from hrhs rhs (List.mem_of_getElem? hr)).subst (pre ++ current) hfixK) ns)
    intro stage comp hget i ann rhs ty hi ha hr ht
    by_cases hstage : stage < past.length
    · have hget0 : past[stage]? = some comp := by simpa only [List.getElem?_append_left hstage] using hget
      have hh := hOldEx stage comp hget0 i ann rhs ty hi ha hr ht
      simpa only [List.take_append_of_le_length (Nat.le_of_lt hstage)] using hh
    · have hstageEq : stage = past.length := by
        have hlt := (List.getElem?_eq_some_iff.mp hget).1
        simp only [List.length_append,List.length_singleton] at hlt
        omega
      subst stage
      have hcomp : comp = component := Option.some.inj (by simpa using hget.symm)
      subst comp
      obtain ⟨ann0,ha0,rfl⟩ := Option.map_eq_some_iff.mp (by simpa only [List.getElem?_map] using ha)
      obtain ⟨rhs0,hr0,rfl⟩ := Option.map_eq_some_iff.mp (by simpa only [List.getElem?_map] using hr)
      have hh := hcurrent i ann0 rhs0 ty hi ha0 hr0 ht
      rw [← hStage] at hh
      simpa only [List.take_left] using hh
 theorem _root_.InferRecStrata.inputTrace_of_infer
    (h : InferRecStrata K F frontier ctx anns bindings state groups next S final)
    (hInfer : ∀ {κ F' Ψ c e Ψ' T output ty}, e.size ≤ sizeBindings bindings →
      Infer κ F' Ψ c e Ψ' T output ty →
      ∀ {w}, w < Ψ →
      e.erase.ForallOuter (fun i => ∀ M, c.env[i]? = some M → w ∉ M.body.freeVars) 0 →
      w ∉ e.rigidVars →
      (∀ p ∈ T, w ∉ p.2.freeVars) ∧ w ∉ ty.freeVars ∧ w ∉ T.map Prod.fst)
    (hvalid : RecGroups.ValidResidualGroups (anns.map BindingAnn.recModeAnn) (bindings.map InferInput.erase) (past ++ groups))
    (hframe : state.Frame base K F ctx anns past.flatten)
    (hlc : state.LC) (hctxWF : CtxWF ctx)
    (hbelow : state.Below frontier) (hctx : CtxBelow frontier ctx)
    (hF : ∀ t ∈ F, Ty.BelowFvars frontier t)
    (hbase : base + bindings.length ≤ frontier)
    (hanns : ∀ ann ∈ anns, ∀ v ∈ ann.rigidVars, v ∈ K ++ softVars F)
    (hrhs : ∀ rhs ∈ bindings, ∀ v ∈ rhs.rigidVars, v ∈ K ++ softVars F)
    (hInput : ∀ {κ F' Ψ c e Ψ' T output ty}, e.size ≤ sizeBindings bindings →
      Infer κ F' Ψ c e Ψ' T output ty → CtxWF c →
      InputTyping (κ ++ softVars (substSoft T F')) (T.onCtx c) (e.substTyFvars T) ty)
    (hTrace : state.InputTrace (K ++ softVars F) ctx anns bindings past) :
    final.InputTrace (K ++ softVars (substSoft S F)) (S.onCtx ctx)
      (anns.map (BindingAnn.substTyFvars S)) (bindings.map (InferInput.substTyFvars S)) (past ++ groups) := by
  match h with
  | .nil =>
    have hannNil : anns.map (BindingAnn.substTyFvars []) = anns := by
      calc
        anns.map (BindingAnn.substTyFvars []) = anns.map id := List.map_congr_left
          (fun ann _ => ann.substTyFvars_eq_self_of_fixes (fun _ _ => rfl))
        _ = anns := List.map_id anns
    have hrhsNil : bindings.map (InferInput.substTyFvars []) = bindings := by
      calc
        bindings.map (InferInput.substTyFvars []) = bindings.map id := List.map_congr_left
          (fun rhs _ => rhs.substTyFvars_eq_self_of_fixes (fun _ _ => rfl))
        _ = bindings := List.map_id bindings
    simpa only [substSoft_nil,Subst.onCtx_nil,hannNil,hrhsNil,List.append_nil] using hTrace
  | .cons ho hp hc hf hr =>
    expose_names
    obtain ⟨hstepFrame, hstepPool, _⟩ := recStep_frame ho hp hc hf hInfer hvalid hframe
      hlc hctxWF hbelow hbase hanns hrhs
    have hstepTrace := recStep_inputTrace ho hp hc hf hInfer hvalid hframe
      hlc hctxWF hbelow hbase hanns hrhs hInput hTrace
    have hstep : InferRecStrata K F frontier ctx anns bindings state [component]
        first (pre ++ current ++ []) exported := .cons ho hp hc hf .nil
    have hK : ∀ k ∈ K, k < frontier := fun k hk => by have := hframe.rigid_below k hk; omega
    have hAnnBelow : ∀ ann ∈ anns, ∀ v ∈ ann.rigidVars, v < frontier := by
      intro ann ha v hv
      exact (List.mem_append.mp (hanns ann ha v hv)).elim (hK v) (softVars_lt hF v)
    have hstepBelow := hstep.belowFvars_of_infer (fun _ hi => hi.belowFvars) hctx hK hF hbelow hAnnBelow
    simp only [List.append_nil] at hstepBelow
    have hstepLC := hstep.lc_of_infer (fun _ hi => hi.lc) hctxWF hlc
    simp only [List.append_nil] at hstepLC
    have hfix : ∀ k ∈ K, (pre ++ current).onTy (.fvar k) = .fvar k := by
      apply Subst.fixes_of_dom_avoids
      simpa only [List.append_nil] using hstep.dom_avoids
    have htailValid := recValid_subst (S := pre ++ current)
      (by simpa only [List.append_assoc, List.singleton_append] using hvalid :
        RecGroups.ValidResidualGroups (anns.map BindingAnn.recModeAnn) (bindings.map InferInput.erase)
          ((past ++ [component]) ++ rest))
    have htailFrame : exported.Frame base K (substSoft (pre ++ current) F) ((pre ++ current).onCtx ctx)
        (anns.map (BindingAnn.substTyFvars (pre ++ current))) (past ++ [component]).flatten := by
      simpa only [List.flatten_append, List.flatten_cons, List.flatten_nil, List.append_nil] using hstepFrame
    have hfinal := hr.inputTrace_of_infer
      (fun he hi => hInfer (by simpa only [sizeBindings_map_substTyFvars] using he) hi)
      htailValid htailFrame hstepLC.2 (Subst.onCtx_wf hstepLC.1 hctxWF)
      hstepBelow.2 (Subst.onCtx_below hstepBelow.1 (ho.frontier_le.trans hc.frontier_le) hctx)
      (substSoft_below hstepBelow.1 (ho.frontier_le.trans hc.frontier_le) hF)
      (by simp only [List.length_map]; have := ho.frontier_le; have := hc.frontier_le; omega)
      (by
        intro ann hm v hv
        obtain ⟨original, ho, rfl⟩ := List.mem_map.mp hm
        obtain ⟨k, hk, himage⟩ := BindingAnn.rigidVars_substTyFvars hv
        exact scope_image hfix (hanns original ho k hk) himage)
      (by
        intro rhs hm
        obtain ⟨original, ho, rfl⟩ := List.mem_map.mp hm
        exact (show SourceScope K F original from hrhs original ho).subst (pre ++ current) hfix)
      (fun he hi => hInput (by simpa only [sizeBindings_map_substTyFvars] using he) hi)
      hstepTrace
    simpa only [substSoft_append,Subst.onCtx_append,List.map_map,Function.comp_def,
      ← BindingAnn.substTyFvars_append,← InferInput.substTyFvars_append,List.append_assoc,List.singleton_append] using hfinal
 termination_by structural h



private theorem RecState.CompleteInput.advance_skip {state : RecState}
    (h : state.CompleteInput Q ctx anns bindings index)
    (ha : anns[index]? = some ann) (hm : ann.recModeAnn = none) :
    state.CompleteInput Q ctx anns bindings (index + 1) := by
  obtain ⟨L, hh⟩ := h
  refine ⟨L, ?_⟩
  intro i scheme rhs hi hann hrhs Xs hXs
  by_cases hlt : i < index
  · exact hh i scheme rhs hlt hann hrhs Xs hXs
  · have heq : i = index := by omega
    subst i
    have hsame := Option.some.inj (ha.symm.trans hann)
    subst ann
    cases hm

private theorem RecState.CompleteInput.advance_complete {state : RecState}
    (h : state.CompleteInput Q ctx anns bindings index)
    (ha : anns[index]? = some (.complete scheme)) (hb : bindings[index]? = some rhs)
    (hhead : ∃ L, ∀ Xs, FreshNames L scheme.paramCount Xs →
      InputTyping (Q ++ Xs) (state.rhsCtx ctx) (rhs.openTyVars Xs) (scheme.openVars Xs)) :
    state.CompleteInput Q ctx anns bindings (index + 1) := by
  obtain ⟨Lold, hold⟩ := h
  obtain ⟨Lhead, hhead⟩ := hhead
  refine ⟨Lold ++ Lhead, ?_⟩
  intro i sigma source hi hann hrhs Xs hXs
  by_cases hlt : i < index
  · exact hold i sigma source hlt hann hrhs Xs
      ⟨hXs.length, hXs.nodup, fun v hv hm => hXs.avoid v hv (List.mem_append_left _ hm)⟩
  · have heq : i = index := by omega
    subst i
    cases BindingAnn.complete.inj (Option.some.inj (ha.symm.trans hann))
    cases Option.some.inj (hb.symm.trans hrhs)
    exact hhead Xs ⟨hXs.length, hXs.nodup, fun v hv hm => hXs.avoid v hv (List.mem_append_right _ hm)⟩

private theorem RecState.CompleteInput.setSigned {state : RecState} {member : Nat} {names : List Nat}
    {output : Expr} {facts : RecFacts} (h : state.CompleteInput Q ctx anns bindings checked) :
    (state.setSigned member names output facts).CompleteInput Q ctx anns bindings checked := h

 theorem _root_.InferRecSigned.inputSound_of_infer
    (h : InferRecSigned K F index frontier ctx anns bindings state next S final)
    (hInfer : ∀ {κ F' Ψ c e Ψ' T output ty}, e.size ≤ sizeBindings bindings →
      Infer κ F' Ψ c e Ψ' T output ty → CtxWF c →
      InputTyping (κ ++ softVars (substSoft T F')) (T.onCtx c) (e.substTyFvars T) ty)
    (hctx : CtxWF ctx) (hstate : state.LC) (hK : ∀ k ∈ K, k < frontier)
    (hAnns : fullAnns.drop index = anns) (hBindings : fullBindings.drop index = bindings)
    (hscope : ∀ ann ∈ fullAnns, ∀ v ∈ ann.rigidVars, v ∈ K ++ softVars F)
    (hchecked : state.CompleteInput (K ++ softVars F) ctx fullAnns fullBindings index) :
    final.CompleteInput (K ++ softVars (substSoft S F)) (S.onCtx ctx)
      (fullAnns.map (BindingAnn.substTyFvars S)) (fullBindings.map (InferInput.substTyFvars S)) fullAnns.length := by
  match h with
  | .nil =>
    have hlen : fullAnns.length ≤ index := by
      have hh := congrArg List.length hAnns
      simp only [List.length_drop, List.length_nil] at hh
      omega
    obtain ⟨L, hh⟩ := hchecked
    have heq : fullAnns.map (BindingAnn.substTyFvars []) = fullAnns := by
      calc
        _ = fullAnns.map id := List.map_congr_left
          (fun ann _ => ann.substTyFvars_eq_self_of_fixes (fun _ _ => rfl))
        _ = fullAnns := List.map_id _
    have heqb : fullBindings.map (InferInput.substTyFvars []) = fullBindings := by
      calc
        _ = fullBindings.map id := List.map_congr_left
          (fun rhs _ => rhs.substTyFvars_eq_self_of_fixes (fun _ _ => rfl))
        _ = fullBindings := List.map_id _
    simp only [substSoft_nil, Subst.onCtx_nil, heq, heqb]
    exact ⟨L, fun i scheme rhs hi => hh i scheme rhs (by omega)⟩
  | .skip hnone hr =>
    expose_names
    have ha : fullAnns[index]? = some ann := by
      have hh := congrArg (fun xs : List BindingAnn => xs[0]?) hAnns
      simpa only [List.getElem?_drop, Nat.zero_add, List.getElem?_cons_zero] using hh
    exact hr.inputSound_of_infer
      (fun he hi => hInfer (by simp only [sizeBindings]; omega) hi) hctx hstate hK
      (by simp only [List.drop_add_one_eq_tail_drop, hAnns, List.tail_cons])
      (by simp only [List.drop_add_one_eq_tail_drop, hBindings, List.tail_cons]) hscope
      (hchecked.advance_skip ha hnone)
  | .cons hWF hraw hi hu hescape hr =>
    expose_names
    have hCtxRhs := hstate.rhsCtx hctx
    obtain ⟨hTyLC, hs1⟩ := hi.lc hCtxRhs
    have hexpected : ((s1.onPolyTy scheme).openVars (freshVars frontier scheme.paramCount)).IsLC :=
      PolyTy.openVars_isLC (Subst.onPolyTy_wf hs1 hWF)
        (by simp only [Subst.onPolyTy, freshVars_length]; exact Nat.le_refl _)
    have hs2 := hu.unifies.lc hTyLC hexpected
    have hSLC : ∀ p ∈ s1 ++ s2, p.2.IsLC := fun p hp => (List.mem_append.mp hp).elim (hs1 p) (hs2 p)
    have hdom : ∀ p ∈ s1 ++ s2, p.1 ∉ K ++ freshVars frontier scheme.paramCount :=
      fun p hp => (List.mem_append.mp hp).elim (hi.dom_avoids p) (hu.dom_avoids p)
    have hfix := Subst.fixes_of_dom_avoids hdom
    have hfixK : ∀ k ∈ K, (s1 ++ s2).onTy (.fvar k) = .fvar k :=
      fun k hk => hfix k (List.mem_append_left _ hk)
    have hfixY : ∀ y ∈ freshVars frontier scheme.paramCount, (s1 ++ s2).onTy (.fvar y) = .fvar y :=
      fun y hy => hfix y (List.mem_append_right _ hy)
    have hAnn : fullAnns[index]? = some (.complete scheme) := by
      have hh := congrArg (fun xs : List BindingAnn => xs[0]?) hAnns
      simpa only [List.getElem?_drop, Nat.zero_add, List.getElem?_cons_zero] using hh
    have hBinding : fullBindings[index]? = some rhs := by
      have hh := congrArg (fun xs : List InferInput => xs[0]?) hBindings
      simpa only [List.getElem?_drop, Nat.zero_add, List.getElem?_cons_zero] using hh
    have hpostRhs : SourceScope K (substSoft (s1 ++ s2) F) (rhs.substTyFvars (s1 ++ s2)) :=
      (show SourceScope K F rhs from hraw).subst (s1 ++ s2) hfixK
    have hpostAnn : ∀ v ∈ ((s1 ++ s2).onPolyTy scheme).body.freeVars,
        v ∈ K ++ softVars (substSoft (s1 ++ s2) F) := by
      intro v hv
      obtain ⟨old, ho, himage⟩ := Ty.mem_freeVars_substFvars_image.mp hv
      exact scope_image hfixK (hscope (.complete scheme) (List.mem_of_getElem? hAnn) old ho) himage
    have htyped := (hInfer (by simp only [InferInput.size_openTyVars, sizeBindings]; omega) hi hCtxRhs).onSubst_source s2 hs2
      (fun k hk v hv => scope_image (Subst.fixes_of_dom_avoids hu.dom_avoids) hk hv)
    have hSctx := RecState.rhsCtx_onSubst state (s1 ++ s2) ctx
    have hEq : s2.onTy ty = ((s1 ++ s2).onPolyTy scheme).openVars (freshVars frontier scheme.paramCount) := by
      simpa only [Unifies, PolyTy.openVars, Subst.onPolyTy, Subst.onTy_append,
        Subst.onTy_openVars_of_fixes hs2 (fun y hy => Subst.fixes_of_dom_avoids hu.dom_avoids y (List.mem_append_right _ hy))] using hu.unifies.unifies
    rw [hEq] at htyped
    simp only [← substSoft_append, ← Subst.onCtx_append, ← InferInput.substTyFvars_append,
      InferInput.substTyFvars_openTyVars_of_fixes _ hSLC hfixY] at htyped
    rw [← hSctx] at htyped
    have hrestricted := htyped.scope_restrict
      ((rhs.substTyFvars (s1 ++ s2)).openTyVarsFrom_scope hpostRhs 0 (freshVars frontier scheme.paramCount))
    have hcompletion : (BindingAnn.complete ((s1 ++ s2).onPolyTy scheme)).SignatureCompletion
        (freshVars frontier scheme.paramCount)
        (((s1 ++ s2).onPolyTy scheme).openVars (freshVars frontier scheme.paramCount))
        ((s1 ++ s2).onPolyTy scheme) (freshVars frontier scheme.paramCount) :=
      .complete (freshVars_length _ _) rfl
    obtain ⟨Lhead, hhead⟩ := hcompletion.cofinite_typing hrestricted (Subst.onPolyTy_wf hSLC hWF)
      freshVars_nodup
      (fun y hy hv => hescape y hy (List.mem_append_left _ hv))
      (by intro y hy hm; rcases List.mem_append.mp hm with hm | hm
          · have := freshVars_ge y hy; have := hK y hm; omega
          · exact hescape y hy (List.mem_append_right _ hm)) hpostAnn hpostRhs
    have hprevious := (hchecked.onSubst (s1 ++ s2) hSLC
      (fun k hk v hv => scope_image hfixK hk hv)).setSigned
      (member := index) (names := freshVars frontier scheme.paramCount)
      (output := output.substTyFvars s2) (facts := bodyFacts.onSubst s2)
    have hcheckNext := hprevious.advance_complete (scheme := (s1 ++ s2).onPolyTy scheme)
      (rhs := rhs.substTyFvars (s1 ++ s2))
      (by simp only [List.getElem?_map, hAnn, Option.map_some, BindingAnn.substTyFvars]; rfl)
      (by simp only [List.getElem?_map, hBinding, Option.map_some])
      ⟨Lhead, fun Xs hXs => by
        have htake : Xs.take ((s1 ++ s2).onPolyTy scheme).paramCount = Xs := by
          rw [← hXs.length, List.take_length]
        simpa only [BindingAnn.paramCount, htake] using hhead Xs hXs⟩
    have hnextScope : ∀ ann ∈ fullAnns.map (BindingAnn.substTyFvars (s1 ++ s2)),
        ∀ v ∈ ann.rigidVars, v ∈ K ++ softVars (substSoft (s1 ++ s2) F) := by
      intro ann hm v hv
      obtain ⟨old, ho, rfl⟩ := List.mem_map.mp hm
      obtain ⟨k, hk, himage⟩ := BindingAnn.rigidVars_substTyFvars hv
      exact scope_image hfixK (hscope old ho k hk) himage
    have htail := hr.inputSound_of_infer
      (fun he hh => hInfer (by
        simp only [sizeBindings_map_substTyFvars] at he
        simp only [sizeBindings]
        omega) hh)
      (Subst.onCtx_wf hSLC hctx) ((hstate.onSubst hSLC).setSigned)
      (fun k hk => by have := hK k hk; have := hi.frontier_le; omega)
      (by simp only [← List.map_drop, List.drop_add_one_eq_tail_drop, hAnns, List.map_cons, List.tail_cons])
      (by simp only [← List.map_drop, List.drop_add_one_eq_tail_drop, hBindings, List.map_cons, List.tail_cons])
      hnextScope hcheckNext
    simpa only [substSoft_append, Subst.onCtx_append, List.map_map, Function.comp_def,
      ← BindingAnn.substTyFvars_append, ← InferInput.substTyFvars_append, List.length_map] using htail
 termination_by structural h

private theorem fidelity_fvar_map_inj {a b : List Nat}
    (h : a.map Ty.fvar = b.map Ty.fvar) : a = b := by
  induction a generalizing b with
  | nil => cases b <;> simp_all
  | cons x xs ih =>
    cases b with
    | nil => simp at h
    | cons y ys =>
      have hh : x = y ∧ xs.map Ty.fvar = ys.map Ty.fvar := by simpa using h
      obtain ⟨rfl,ht⟩ := hh
      exact congrArg (x :: ·) (ih ht)

private theorem fidelity_some_join {xs : List (Option Expr)} {i : Nat} {output : Expr}
    (h : xs[i]?.join = some output) : xs[i]? = some (some output) := by
  cases hx : xs[i]? with
  | none => simp [hx] at h
  | some o => cases o <;> simp_all

 theorem recStep_fidelity
    {state : RecState}
    (ho : OpenRecAnns component 0 frontier anns opened openings)
    (hp : CheckRecShapes K ((state.installOpenings component openings).shapes component openings) pre)
    (hc : InferRecComponent K (substSoft pre (F ++ (openings.flatMap RecOpening.written).map Ty.fvar))
      component 0 opened (((state.installOpenings component openings).onSubst pre).rhsCtx (pre.onCtx ctx))
      ((openRecSources openings bindings).map (InferInput.substTyFvars pre))
      ((state.installOpenings component openings).onSubst pre).specs first current outputs facts)
    (hf : FinishRecComponent K (softVars (substSoft (pre ++ current) F)) component
      ((pre ++ current).onCtx ctx) ((state.installOpenings component openings).onSubst (pre ++ current))
      outputs facts exported)
    (hInfer : ∀ {κ F' Ψ c e Ψ' T output ty}, e.size ≤ sizeBindings bindings →
      Infer κ F' Ψ c e Ψ' T output ty →
      ∀ {w}, w < Ψ →
      e.erase.ForallOuter (fun i => ∀ M, c.env[i]? = some M → w ∉ M.body.freeVars) 0 →
      w ∉ e.rigidVars →
      (∀ p ∈ T, w ∉ p.2.freeVars) ∧ w ∉ ty.freeVars ∧ w ∉ T.map Prod.fst)
    (hvalid : RecGroups.ValidResidualGroups (anns.map BindingAnn.recModeAnn) (bindings.map InferInput.erase)
      (past ++ component :: rest))
    (hframe : state.Frame base K F ctx anns past.flatten)
    (hlc : state.LC) (hctx : CtxWF ctx)
    (hbelow : state.Below frontier) (hbase : base + bindings.length ≤ frontier)
    (hanns : ∀ ann ∈ anns, ∀ v ∈ ann.rigidVars, v ∈ K ++ softVars F)
    (hrhs : ∀ rhs ∈ bindings, ∀ v ∈ rhs.rigidVars, v ∈ K ++ softVars F)
    (hComplete : ∀ {κ F' Ψ c e Ψ' T output ty}, e.size ≤ sizeBindings bindings →
      Infer κ F' Ψ c e Ψ' T output ty → CtxWF c →
      AnnotationCompletion (κ ++ softVars (substSoft T F')) (e.substTyFvars T) output)
    (hSound : ∀ {κ F' Ψ c e Ψ' T output ty}, e.size ≤ sizeBindings bindings →
      Infer κ F' Ψ c e Ψ' T output ty → CtxWF c → TypeOfHM (T.onCtx c) output ty)
    (hFidelity : state.Fidelity (K ++ softVars F) anns bindings) :
    exported.Fidelity (K ++ softVars (substSoft (pre ++ current) F))
      (anns.map (BindingAnn.substTyFvars (pre ++ current)))
      (bindings.map (InferInput.substTyFvars (pre ++ current))) := by
  obtain ⟨heframe,hpool,_⟩ := recStep_frame ho hp hc hf hInfer hvalid hframe hlc hctx hbelow hbase hanns hrhs
  have hinitLC := hlc.installOpenings (members := component) (openings := openings)
  have hpreLC := hp.lc (RecState.shapes_lc hinitLC ho.expected_lc)
  have hpreCtx := (hinitLC.onSubst hpreLC).rhsCtx (Subst.onCtx_wf hpreLC hctx)
  have hcurrentLC := hc.lc_of_infer (fun _ hi => hi.lc) hpreCtx (hinitLC.onSubst hpreLC).1
  have hSLC : ∀ p ∈ pre ++ current, p.2.IsLC :=
    fun p hm => (List.mem_append.mp hm).elim (hpreLC p) (hcurrentLC p)
  have hfixK : ∀ k ∈ K, (pre ++ current).onTy (.fvar k) = .fvar k :=
    Subst.fixes_of_dom_avoids (fun p hp' => (List.mem_append.mp hp').elim (hp.dom_avoids p) (hc.dom_avoids p))
  have hlength : anns.length = bindings.length := by simpa only [List.length_map] using hvalid.length
  have hcompComplete := hc.completes_of_infer
    (fun he hi => hComplete (by simpa only [sizeBindings_map_substTyFvars,sizeBindings_openRecSources] using he) hi)
    hpreCtx (hinitLC.onSubst hpreLC).1
  have hcompSound := hc.sourceSound_of_infer
    (fun he hi => hSound (by simpa only [sizeBindings_map_substTyFvars,sizeBindings_openRecSources] using he) hi)
    (fun _ hi => hi.lc) hpreCtx (hinitLC.onSubst hpreLC).1
  have hfidInstall : (state.installOpenings component openings).Fidelity (K ++ softVars F) anns bindings := hFidelity
  have hfidS := hfidInstall.onSubst_source hSLC (fun k hk v hv => scope_image hfixK hk hv)
  have hAnnS : ∀ ann ∈ anns.map (BindingAnn.substTyFvars (pre ++ current)),
      ∀ v ∈ ann.rigidVars, v ∈ K ++ softVars (substSoft (pre ++ current) F) := by
    intro ann ha v hv
    obtain ⟨old,hold,rfl⟩ := List.mem_map.mp ha
    obtain ⟨k,hk,hv⟩ := BindingAnn.rigidVars_substTyFvars hv
    exact scope_image hfixK (hanns old hold k hk) hv
  have hRhsS : ∀ rhs ∈ bindings.map (InferInput.substTyFvars (pre ++ current)),
      ∀ v ∈ rhs.rigidVars, v ∈ K ++ softVars (substSoft (pre ++ current) F) := by
    intro rhs hr
    obtain ⟨old,hold,rfl⟩ := List.mem_map.mp hr
    exact (show SourceScope K F old from hrhs old hold).subst (pre ++ current) hfixK
  cases hf with
  | mk hresolve =>
    expose_names
    let st := (state.installOpenings component openings).onSubst (pre ++ current)
    have hprefixData : ∀ i ∈ component,
        ∃ ns, written[i]? = some ns ∧ st.slots[i]? = some (ns.map Ty.fvar) ∧
          ns.length = ((anns.map (BindingAnn.substTyFvars (pre ++ current)))[i]?.getD .absent).recPrefixCount ∧
          ns.Nodup ∧ ∀ v ∈ ns, v ∈ st.componentPool K (softVars (substSoft (pre ++ current) F)) component ((pre ++ current).onCtx ctx) written := by
      intro i hi
      have hm : i ∈ (past ++ component :: rest).flatten := by
        simp only [List.flatten_append,List.flatten_cons,List.mem_append];tauto
      obtain ⟨ty,ht⟩ := hframe.mono_at_unsigned ((hvalid.covers_unsigned i (hvalid.bounded i hm)).mp hm)
      have htS : st.specs[i]? = some (.mono ((pre ++ current).onTy ty)) := by
        simp only [st,RecState.onSubst,RecState.installOpenings,List.getElem?_map,ht,Option.map_some,RecSpec.onSubstSource]
      obtain ⟨ns,hslot,hcount,hnd,hsub,_⟩ := if_pos (List.mem_append_right _ hi) ▸ heframe.mono i _ htS
      obtain ⟨resolved,hr,hh⟩ := hresolve.lookup i (ns.map Ty.fvar) hslot
      rw [Nat.zero_add,if_pos hi] at hh
      have heq := fidelity_fvar_map_inj hh.1
      subst resolved
      exact ⟨ns,hr,hslot,hcount,hnd,hsub⟩
    apply hfidS.exportComponent (hinitLC.onSubst hSLC) heframe.pool_nodup
      (fun v hv hq => (List.mem_append.mp hq).elim (heframe.pool_rigid v hv) (heframe.pool_soft v hv))
      hAnnS hRhsS
    · intro i hi
      obtain ⟨ns,hn,_,hcount,hnd,hsub⟩ := hprefixData i hi
      simpa only [hn,Option.getD_some] using And.intro hcount (And.intro hnd hsub)
    · intro i ann rhs ty output hi ha hr ht hout
      obtain ⟨ann0,ha0,rfl⟩ := Option.map_eq_some_iff.mp (by simpa only [List.getElem?_map] using ha)
      obtain ⟨rhs0,hr0,rfl⟩ := Option.map_eq_some_iff.mp (by simpa only [List.getElem?_map] using hr)
      obtain ⟨oldTy,ht0,rfl⟩ := RecSpec.mono_getElem?_map_onSubstSource ht
      have ht0' : state.specs[i]? = some (.mono oldTy) := ht0
      obtain ⟨ns,hn,hslot,_,_,_⟩ := hprefixData i hi
      simp only [hn,Option.getD_some]
      obtain ⟨a,b,opening,hop,hopen⟩ := ho.selected_lookup (by simpa using hi) ha0
      have hislot : i < state.slots.length := by
        rw [hframe.slots_length,←hframe.specs_length]
        exact (List.getElem?_eq_some_iff.mp ht0').1
      have hslots : st.slots[i]? = some (opening.written.map (fun v => (pre ++ current).onTy (.fvar v))) := by
        simp only [st,RecState.onSubst,RecState.installOpenings,List.getElem?_map,List.getElem?_mapIdx,
          List.getElem?_eq_getElem hislot,Option.map_some,if_pos hi,hop,Option.getD_some,List.map_map,Function.comp_def]
      have himages : opening.written.map (fun v => (pre ++ current).onTy (.fvar v)) = ns.map Ty.fvar :=
        Option.some.inj (hslots.symm.trans hslot)
      have hmode : ann0.recModeAnn = none := by
        have hh := congrArg (fun xs : List (Option PolyTy) => xs[i]?) hframe.modes
        simpa only [List.getElem?_map,ht0',ha0,Option.map_some,RecSpec.ann,Option.some.injEq] using hh.symm
      refine ⟨hopen.recFits_of_images hmode hSLC himages ?_, ?_, ?_⟩
      · intro expected hex
        have hshape : (oldTy,some expected) ∈ (state.installOpenings component openings).shapes component openings := by
          apply List.mem_filterMap.mpr
          exact ⟨i,hi,by simp [RecState.installOpenings,ht0',RecSpec.monoTy?,hop,hex]⟩
        have hsolved := hp.solves hshape
        simpa only [Subst.onTy_append] using congrArg current.onTy hsolved
      · have hrOpened := openRecSources_lookup (ho.length.trans hlength) hr0 hop
        have hh := hcompComplete i ((rhs0.openTyVars opening.written).substTyFvars pre) output
          (by simp only [List.getElem?_map,hrOpened,Option.map_some]) (fidelity_some_join hout)
        have hcomplete : AnnotationCompletion (K ++ softVars (substSoft (pre ++ current) (F ++ (openings.flatMap RecOpening.written).map Ty.fvar)))
            ((rhs0.substTyFvars (pre ++ current)).openTyVars ns) output := by
          simpa only [← substSoft_append,← InferInput.substTyFvars_append,
            InferInput.substTyFvars_openTyVars_of_images _ hSLC himages] using hh
        exact hcomplete.scope_restrict ((rhs0.substTyFvars (pre ++ current)).openTyVars_scope
          ((show SourceScope K F rhs0 from hrhs rhs0 (List.mem_of_getElem? hr0)).subst (pre ++ current) hfixK) ns)
      · have hh := hcompSound i (pre.onTy oldTy) output
          (by simp only [RecState.onSubst,List.getElem?_map,ht0,Option.map_some,RecSpec.onSubstSource])
          (fidelity_some_join hout)
        exact hh.tyBvarBounded

 theorem _root_.InferRecStrata.fidelity_of_infer
    (h : InferRecStrata K F frontier ctx anns bindings state groups next S final)
    (hInfer : ∀ {κ F' Ψ c e Ψ' T output ty}, e.size ≤ sizeBindings bindings →
      Infer κ F' Ψ c e Ψ' T output ty →
      ∀ {w}, w < Ψ →
      e.erase.ForallOuter (fun i => ∀ M, c.env[i]? = some M → w ∉ M.body.freeVars) 0 →
      w ∉ e.rigidVars →
      (∀ p ∈ T, w ∉ p.2.freeVars) ∧ w ∉ ty.freeVars ∧ w ∉ T.map Prod.fst)
    (hvalid : RecGroups.ValidResidualGroups (anns.map BindingAnn.recModeAnn) (bindings.map InferInput.erase) (past ++ groups))
    (hframe : state.Frame base K F ctx anns past.flatten)
    (hlc : state.LC) (hctxWF : CtxWF ctx)
    (hbelow : state.Below frontier) (hctx : CtxBelow frontier ctx)
    (hF : ∀ t ∈ F, Ty.BelowFvars frontier t)
    (hbase : base + bindings.length ≤ frontier)
    (hanns : ∀ ann ∈ anns, ∀ v ∈ ann.rigidVars, v ∈ K ++ softVars F)
    (hrhs : ∀ rhs ∈ bindings, ∀ v ∈ rhs.rigidVars, v ∈ K ++ softVars F)
    (hComplete : ∀ {κ F' Ψ c e Ψ' T output ty}, e.size ≤ sizeBindings bindings →
      Infer κ F' Ψ c e Ψ' T output ty → CtxWF c →
      AnnotationCompletion (κ ++ softVars (substSoft T F')) (e.substTyFvars T) output)
    (hSound : ∀ {κ F' Ψ c e Ψ' T output ty}, e.size ≤ sizeBindings bindings →
      Infer κ F' Ψ c e Ψ' T output ty → CtxWF c → TypeOfHM (T.onCtx c) output ty)
    (hFidelity : state.Fidelity (K ++ softVars F) anns bindings) :
    final.Fidelity (K ++ softVars (substSoft S F))
      (anns.map (BindingAnn.substTyFvars S)) (bindings.map (InferInput.substTyFvars S)) := by
  match h with
  | .nil =>
    have hannNil : anns.map (BindingAnn.substTyFvars []) = anns := by
      calc
        anns.map (BindingAnn.substTyFvars []) = anns.map id := List.map_congr_left
          (fun ann _ => ann.substTyFvars_eq_self_of_fixes (fun _ _ => rfl))
        _ = anns := List.map_id anns
    have hrhsNil : bindings.map (InferInput.substTyFvars []) = bindings := by
      calc
        bindings.map (InferInput.substTyFvars []) = bindings.map id := List.map_congr_left
          (fun rhs _ => rhs.substTyFvars_eq_self_of_fixes (fun _ _ => rfl))
        _ = bindings := List.map_id bindings
    simpa only [substSoft_nil,Subst.onCtx_nil,hannNil,hrhsNil,List.append_nil] using hFidelity
  | .cons ho hp hc hf hr =>
    expose_names
    obtain ⟨hstepFrame, hstepPool, _⟩ := recStep_frame ho hp hc hf hInfer hvalid hframe
      hlc hctxWF hbelow hbase hanns hrhs
    have hstepFidelity := recStep_fidelity ho hp hc hf hInfer hvalid hframe
      hlc hctxWF hbelow hbase hanns hrhs hComplete hSound hFidelity
    have hstep : InferRecStrata K F frontier ctx anns bindings state [component]
        first (pre ++ current ++ []) exported := .cons ho hp hc hf .nil
    have hK : ∀ k ∈ K, k < frontier := fun k hk => by have := hframe.rigid_below k hk; omega
    have hAnnBelow : ∀ ann ∈ anns, ∀ v ∈ ann.rigidVars, v < frontier := by
      intro ann ha v hv
      exact (List.mem_append.mp (hanns ann ha v hv)).elim (hK v) (softVars_lt hF v)
    have hstepBelow := hstep.belowFvars_of_infer (fun _ hi => hi.belowFvars) hctx hK hF hbelow hAnnBelow
    simp only [List.append_nil] at hstepBelow
    have hstepLC := hstep.lc_of_infer (fun _ hi => hi.lc) hctxWF hlc
    simp only [List.append_nil] at hstepLC
    have hfix : ∀ k ∈ K, (pre ++ current).onTy (.fvar k) = .fvar k := by
      apply Subst.fixes_of_dom_avoids
      simpa only [List.append_nil] using hstep.dom_avoids
    have htailValid := recValid_subst (S := pre ++ current)
      (by simpa only [List.append_assoc, List.singleton_append] using hvalid :
        RecGroups.ValidResidualGroups (anns.map BindingAnn.recModeAnn) (bindings.map InferInput.erase)
          ((past ++ [component]) ++ rest))
    have htailFrame : exported.Frame base K (substSoft (pre ++ current) F) ((pre ++ current).onCtx ctx)
        (anns.map (BindingAnn.substTyFvars (pre ++ current))) (past ++ [component]).flatten := by
      simpa only [List.flatten_append, List.flatten_cons, List.flatten_nil, List.append_nil] using hstepFrame
    have hfinal := hr.fidelity_of_infer
      (fun he hi => hInfer (by simpa only [sizeBindings_map_substTyFvars] using he) hi)
      htailValid htailFrame hstepLC.2 (Subst.onCtx_wf hstepLC.1 hctxWF)
      hstepBelow.2 (Subst.onCtx_below hstepBelow.1 (ho.frontier_le.trans hc.frontier_le) hctx)
      (substSoft_below hstepBelow.1 (ho.frontier_le.trans hc.frontier_le) hF)
      (by simp only [List.length_map]; have := ho.frontier_le; have := hc.frontier_le; omega)
      (by
        intro ann hm v hv
        obtain ⟨original, ho, rfl⟩ := List.mem_map.mp hm
        obtain ⟨k, hk, himage⟩ := BindingAnn.rigidVars_substTyFvars hv
        exact scope_image hfix (hanns original ho k hk) himage)
      (by
        intro rhs hm
        obtain ⟨original, ho, rfl⟩ := List.mem_map.mp hm
        exact (show SourceScope K F original from hrhs original ho).subst (pre ++ current) hfix)
      (fun he hi => hComplete (by simpa only [sizeBindings_map_substTyFvars] using he) hi)
      (fun he hi => hSound (by simpa only [sizeBindings_map_substTyFvars] using he) hi)
      hstepFidelity
    simpa only [substSoft_append,Subst.onCtx_append,List.map_map,Function.comp_def,
      ← BindingAnn.substTyFvars_append,← InferInput.substTyFvars_append,List.append_assoc,List.singleton_append] using hfinal
 termination_by structural h





 theorem _root_.InferRecSigned.type_fields
    (h : InferRecSigned K F index frontier ctx anns bindings state next S final) :
    final.specs = (state.onSubst S).specs ∧ final.slots = (state.onSubst S).slots ∧
    final.exports = (state.onSubst S).exports ∧ final.pool = state.pool := by
  match h with
  | .nil =>
    have hs : RecSpec.onSubstSource [] = id := funext RecSpec.onSubstSource_nil
    have ht : Subst.onTy [] = id := funext (fun _ => Subst.onTy_nil)
    have hp : Subst.onPolyTy [] = id := funext (fun _ => Subst.onPolyTy_nil _)
    simp [RecState.onSubst, hs, ht, hp]
  | .skip _ hr => exact hr.type_fields
  | .cons _ _ _ _ _ hr =>
    obtain ⟨hspec, hslots, hexports, hpool⟩ := hr.type_fields
    refine ⟨?_, ?_, ?_, hpool⟩
    · exact hspec.trans (by
        simp only [RecState.setSigned, RecState.onSubst, List.map_map]
        apply List.map_congr_left
        intro spec _
        simp only [Function.comp_apply, RecSpec.onSubstSource_append, List.append_assoc])
    · exact hslots.trans (by
        simp only [RecState.setSigned, RecState.onSubst, List.map_map]
        apply List.map_congr_left
        intro names _
        simp only [Function.comp_apply, List.map_map]
        apply List.map_congr_left
        intro ty _
        simp only [Function.comp_apply, Subst.onTy_append, List.append_assoc])
    · exact hexports.trans (by
        simp only [RecState.setSigned, RecState.onSubst, List.map_map]
        apply List.map_congr_left
        intro entry _
        cases entry <;> simp only [Function.comp_apply, Option.map_none, Option.map_some,
          Subst.onPolyTy_append, List.append_assoc])
 termination_by structural h

 theorem RecState.InputTrace.congr_types {state other : RecState}
    (h : state.InputTrace Q ctx anns bindings past)
    (hspec : other.specs = state.specs) (hslots : other.slots = state.slots)
    (hexports : other.exports = state.exports) : other.InputTrace Q ctx anns bindings past := by
  simpa only [RecState.InputTrace, RecState.prefixes, RecState.stageCtx, RecState.stageEntries,
    hspec, hslots, hexports] using h

private theorem RecState.Fidelity.setSigned_complete {state : RecState} {member : Nat} {names : List Nat}
    {output : Expr} {facts : RecFacts} {scheme : PolyTy} {rhs : InferInput}
    (h : state.Fidelity Q anns bindings)
    (ha : anns[member]? = some (.complete scheme)) (hb : bindings[member]? = some rhs)
    (he : state.exports[member]? = some (some scheme)) (hm : member < state.outputs.length)
    (hnew : ∃ L, ∀ Xs, FreshNames L scheme.paramCount Xs →
      AnnotationCompletion (Q ++ Xs) (rhs.openTyVars Xs) ((output.closeTyVars names).openTyVars Xs)) :
    (state.setSigned member names output facts).Fidelity Q anns bindings := by
  intro i ann source sigma completed hann hrhs hex hout
  change state.exports[i]? = some (some sigma) at hex
  change (state.outputs.set member (some (output.closeTyVars names)))[i]? = some (some completed) at hout
  rw [List.getElem?_set] at hout
  by_cases hi : member = i
  · subst i
    cases Option.some.inj (ha.symm.trans hann)
    cases Option.some.inj (hb.symm.trans hrhs)
    cases Option.some.inj (Option.some.inj (he.symm.trans hex))
    simp only [ite_true, if_pos hm, Option.some.injEq] at hout
    subst completed
    obtain ⟨L, hh⟩ := hnew
    refine ⟨L, ?_⟩
    intro Xs hXs
    have htake : Xs.take scheme.paramCount = Xs := by rw [← hXs.length, List.take_length]
    refine ⟨BindingAnn.SignatureFits.complete, ?_⟩
    simpa only [BindingAnn.paramCount, htake] using hh Xs hXs
  · simp only [if_neg hi] at hout
    exact h i ann source sigma completed hann hrhs hex hout

 theorem _root_.InferRecSigned.completes_of_infer
    (h : InferRecSigned K F index frontier ctx anns bindings state next S final)
    (hInfer : ∀ {κ F' Ψ c e Ψ' T output ty}, e.size ≤ sizeBindings bindings →
      Infer κ F' Ψ c e Ψ' T output ty → CtxWF c →
      AnnotationCompletion (κ ++ softVars (substSoft T F')) (e.substTyFvars T) output)
    (hSource : ∀ {κ F' Ψ c e Ψ' T output ty}, e.size ≤ sizeBindings bindings →
      Infer κ F' Ψ c e Ψ' T output ty → CtxWF c → TypeOfHM (T.onCtx c) output ty)
    (hctx : CtxWF ctx) (hstate : state.LC) (hK : ∀ k ∈ K, k < frontier)
    (hAnns : fullAnns.drop index = anns) (hBindings : fullBindings.drop index = bindings)
    (hOutLen : state.outputs.length = fullAnns.length)
    (hExports : ∀ (j : Nat) (scheme : PolyTy), anns[j]? = some (.complete scheme) →
      state.exports[index + j]? = some (some scheme))
    (hfid : state.Fidelity (K ++ softVars F) fullAnns fullBindings) :
    final.Fidelity (K ++ softVars (substSoft S F))
      (fullAnns.map (BindingAnn.substTyFvars S)) (fullBindings.map (InferInput.substTyFvars S)) := by
  match h with
  | .nil =>
    have heq : fullAnns.map (BindingAnn.substTyFvars []) = fullAnns := by
      calc
        _ = fullAnns.map id := List.map_congr_left
          (fun ann _ => ann.substTyFvars_eq_self_of_fixes (fun _ _ => rfl))
        _ = fullAnns := List.map_id _
    have heqb : fullBindings.map (InferInput.substTyFvars []) = fullBindings := by
      calc
        _ = fullBindings.map id := List.map_congr_left
          (fun rhs _ => rhs.substTyFvars_eq_self_of_fixes (fun _ _ => rfl))
        _ = fullBindings := List.map_id _
    simpa only [substSoft_nil, heq, heqb] using hfid
  | .skip _ hr =>
    exact hr.completes_of_infer
      (fun he hi => hInfer (by simp only [sizeBindings]; omega) hi)
      (fun he hi => hSource (by simp only [sizeBindings]; omega) hi)
      hctx hstate hK
      (by simp only [List.drop_add_one_eq_tail_drop, hAnns, List.tail_cons])
      (by simp only [List.drop_add_one_eq_tail_drop, hBindings, List.tail_cons]) hOutLen
      (by intro j scheme hj; simpa only [Nat.add_assoc, Nat.add_comm 1 j] using
            hExports (j + 1) scheme hj) hfid
  | .cons hWF hraw hi hu hescape hr =>
    expose_names
    have hCtxRhs := hstate.rhsCtx hctx
    obtain ⟨hTyLC, hs1⟩ := hi.lc hCtxRhs
    have hexpected : ((s1.onPolyTy scheme).openVars (freshVars frontier scheme.paramCount)).IsLC :=
      PolyTy.openVars_isLC (Subst.onPolyTy_wf hs1 hWF)
        (by simp only [Subst.onPolyTy, freshVars_length]; exact Nat.le_refl _)
    have hs2 := hu.unifies.lc hTyLC hexpected
    have hSLC : ∀ p ∈ s1 ++ s2, p.2.IsLC := fun p hp => (List.mem_append.mp hp).elim (hs1 p) (hs2 p)
    have hdom : ∀ p ∈ s1 ++ s2, p.1 ∉ K ++ freshVars frontier scheme.paramCount :=
      fun p hp => (List.mem_append.mp hp).elim (hi.dom_avoids p) (hu.dom_avoids p)
    have hfix := Subst.fixes_of_dom_avoids hdom
    have hfixK : ∀ k ∈ K, (s1 ++ s2).onTy (.fvar k) = .fvar k :=
      fun k hk => hfix k (List.mem_append_left _ hk)
    have hfixY : ∀ y ∈ freshVars frontier scheme.paramCount, (s1 ++ s2).onTy (.fvar y) = .fvar y :=
      fun y hy => hfix y (List.mem_append_right _ hy)
    have hAnn : fullAnns[index]? = some (.complete scheme) := by
      have hh := congrArg (fun xs : List BindingAnn => xs[0]?) hAnns
      simpa only [List.getElem?_drop, Nat.zero_add, List.getElem?_cons_zero] using hh
    have hBinding : fullBindings[index]? = some rhs := by
      have hh := congrArg (fun xs : List InferInput => xs[0]?) hBindings
      simpa only [List.getElem?_drop, Nat.zero_add, List.getElem?_cons_zero] using hh
    have hpostRhs : SourceScope K (substSoft (s1 ++ s2) F) (rhs.substTyFvars (s1 ++ s2)) :=
      (show SourceScope K F rhs from hraw).subst (s1 ++ s2) hfixK
    have hcomplete := (hInfer (by simp only [InferInput.size_openTyVars, sizeBindings]; omega) hi hCtxRhs).onSubst_source s2 hs2
      (fun k hk v hv => scope_image (Subst.fixes_of_dom_avoids hu.dom_avoids) hk hv)
    simp only [← substSoft_append, ← InferInput.substTyFvars_append,
      InferInput.substTyFvars_openTyVars_of_fixes _ hSLC hfixY] at hcomplete
    have hrestricted := hcomplete.scope_restrict
      ((rhs.substTyFvars (s1 ++ s2)).openTyVarsFrom_scope hpostRhs 0 (freshVars frontier scheme.paramCount))
    have hbound : (output.substTyFvars s2).TyBvarBounded 0 :=
      (TypeOfHM.onSubst s2 hs2 (hSource
        (by simp only [InferInput.size_openTyVars, sizeBindings]; omega) hi hCtxRhs)).tyBvarBounded
    have hcompletion : (BindingAnn.complete ((s1 ++ s2).onPolyTy scheme)).SignatureCompletion
        (freshVars frontier scheme.paramCount)
        (((s1 ++ s2).onPolyTy scheme).openVars (freshVars frontier scheme.paramCount))
        ((s1 ++ s2).onPolyTy scheme) (freshVars frontier scheme.paramCount) :=
      .complete (freshVars_length _ _) rfl
    obtain ⟨Lhead, hhead⟩ := hcompletion.cofinite_completes hrestricted freshVars_nodup
      (by intro y hy hm; rcases List.mem_append.mp hm with hm | hm
          · have := freshVars_ge y hy; have := hK y hm; omega
          · exact hescape y hy (List.mem_append_right _ hm)) hpostRhs hbound
    have hprevious := hfid.onSubst_source hSLC (fun k hk v hv => scope_image hfixK hk hv)
    have hnew := hprevious.setSigned_complete (member := index) (names := freshVars frontier scheme.paramCount)
      (output := output.substTyFvars s2) (facts := bodyFacts.onSubst s2)
      (scheme := (s1 ++ s2).onPolyTy scheme) (rhs := rhs.substTyFvars (s1 ++ s2))
      (by simp only [List.getElem?_map, hAnn, Option.map_some, BindingAnn.substTyFvars]; rfl)
      (by simp only [List.getElem?_map, hBinding, Option.map_some])
      (by
        have hh : state.exports[index]? = some (some scheme) := by simpa only [Nat.add_zero] using hExports 0 scheme rfl
        simp only [RecState.onSubst, List.getElem?_map, hh, Option.map_some])
      (by simpa only [RecState.onSubst, List.length_map, hOutLen] using (List.getElem?_eq_some_iff.mp hAnn).1)
      ⟨Lhead, fun Xs hXs => by
        have htake : Xs.take ((s1 ++ s2).onPolyTy scheme).paramCount = Xs := by
          rw [← hXs.length, List.take_length]
        simpa only [BindingAnn.paramCount, htake] using hhead Xs hXs⟩
    have htail := hr.completes_of_infer
      (fun he hh => hInfer (by
        simp only [sizeBindings_map_substTyFvars] at he
        simp only [sizeBindings]
        omega) hh)
      (fun he hh => hSource (by
        simp only [sizeBindings_map_substTyFvars] at he
        simp only [sizeBindings]
        omega) hh)
      (Subst.onCtx_wf hSLC hctx) ((hstate.onSubst hSLC).setSigned)
      (fun k hk => by have := hK k hk; have := hi.frontier_le; omega)
      (by simp only [← List.map_drop, List.drop_add_one_eq_tail_drop, hAnns, List.map_cons, List.tail_cons])
      (by simp only [← List.map_drop, List.drop_add_one_eq_tail_drop, hBindings, List.map_cons, List.tail_cons])
      (by simpa only [RecState.setSigned, RecState.onSubst, List.length_set, List.length_map] using hOutLen)
      (by
        intro j sigma hj
        obtain ⟨ann, ha, heq⟩ := Option.map_eq_some_iff.mp (by simpa only [List.getElem?_map] using hj)
        cases ann with
        | absent | template | partialForall => cases heq
        | complete original =>
          cases BindingAnn.complete.inj heq
          have hh := hExports (j + 1) original ha
          simp only [RecState.setSigned, RecState.onSubst, List.getElem?_map, Nat.add_assoc,
            Nat.add_comm 1 j, hh, Option.map_some]
          rfl) hnew
    simpa only [substSoft_append, List.map_map, Function.comp_def,
      ← BindingAnn.substTyFvars_append, ← InferInput.substTyFvars_append] using htail
 termination_by structural h

end

/-! ## Infer -/

section

private theorem substInputBindings_eq_map_global (S : Subst) (bindings : List InferInput) :
    substInputBindings S bindings = bindings.map (InferInput.substTyFvars S) := by
  induction bindings with
  | nil => rfl
  | cons rhs rest ih => simp only [substInputBindings, List.map_cons, ih]

 theorem RecState.Frame.rhsCtx_eq_recBodyCtx {state : RecState}
    (h : state.Frame base K F ctx anns done)
    (hdone : ∀ i ty, state.specs[i]? = some (.mono ty) → i ∈ done) :
    state.rhsCtx ctx = recBodyCtx ctx state.specs state.prefixes state.pool := by
  have heq : state.entries = recCompletedSchemes state.specs state.prefixes state.pool := by
    apply List.ext_getElem?
    intro i
    cases hs : state.specs[i]? with
    | none =>
      have hi : state.specs.length ≤ i := List.getElem?_eq_none_iff.mp hs
      simp only [recCompletedSchemes, List.getElem?_mapIdx, hs, Option.map_none]
      exact List.getElem?_eq_none_iff.mpr (by
        simp only [RecState.entries, List.length_map, List.length_zip]
        omega)
    | some spec =>
      have he : state.exports[i]? = some (some (spec.completedScheme (state.prefixes[i]?.getD []) state.pool)) := by
        cases spec with
        | poly sigma => simpa only [RecSpec.completedScheme_poly] using h.poly i sigma hs
        | mono ty =>
          obtain ⟨names, hslots, _, _, _, hex⟩ := if_pos (hdone i ty hs) ▸ h.mono i ty hs
          have hp : state.prefixes[i]? = some names := by
            simp only [RecState.prefixes, List.getElem?_mapIdx, hs, Option.map_some, hslots, Option.getD_some]
            congr 1
            rw [List.filterMap_map]
            change names.filterMap some = names
            simp
          simpa only [RecSpec.completedScheme_mono, hp, Option.getD_some] using hex
      have hz : (state.specs.zip state.exports)[i]? = some (spec, some (spec.completedScheme (state.prefixes[i]?.getD []) state.pool)) := List.getElem?_zip_eq_some.mpr ⟨hs, he⟩
      simp only [RecState.entries, List.getElem?_map, hz, Option.map_some, Option.getD_some,
        recCompletedSchemes, List.getElem?_mapIdx, hs]
  simp only [RecState.rhsCtx, recBodyCtx, heq]

private theorem forall₂_self_map {α β} {R : α → β → Prop} {f : α → β} :
    ∀ {xs : List α}, (∀ x ∈ xs, R x (f x)) → List.Forall₂ R xs (xs.map f)
  | [], _ => .nil
  | _ :: _, h => .cons (h _ (List.mem_cons_self ..))
      (forall₂_self_map (fun x hx => h x (List.mem_cons_of_mem _ hx)))

/-- Whole substitutions transport a completed branch and its constructor witness. -/
theorem _root_.TypeOfMatchBranch.onSubst
    (h : TypeOfMatchBranch ctx (pat, body) scrutTy resultTy)
    (subst : Subst) (hlc : ∀ pair ∈ subst, pair.2.IsLC) :
    TypeOfMatchBranch (subst.onCtx ctx) (pat, body.substTyFvars subst)
      (subst.onTy scrutTy) (subst.onTy resultTy) := by
  cases h with
  | wildcard hb => exact .wildcard (TypeOfHM.onSubst subst hlc hb)
  | mk hspec heq hb =>
    subst heq
    refine .mk (hspec.onSubst subst hlc) ?_ (TypeOfHM.onSubst subst hlc hb)
    simp only [Subst.onCtx, Subst.onEnv, List.map_append, List.map_map,
      Function.comp_def, Subst.onPolyTy, PolyTy.mkTrivial]

theorem _root_.InferBranches.nil_iff
    (h : InferBranches K F frontier ctx scrutTy resultTy branches next subst completed) :
    completed = [] ↔ branches = [] := by cases h <;> simp




private theorem rec_rhs_rigid_mem {bindings : List InferInput} {rhs : InferInput} {v : Nat}
    (hr : rhs ∈ bindings) (hv : v ∈ rhs.rigidVars) : v ∈ rigidBindingVars bindings := by
  induction bindings with
  | nil => cases hr
  | cons head rest ih =>
    rcases List.mem_cons.mp hr with rfl | hr
    · exact List.mem_append_left _ hv
    · exact List.mem_append_right _ (ih hr)

mutual
/-- Successful elaboration produces ordinary annotated Core typing. The proof
constructs the typing from the inference derivation; it does not recheck output
with the Core inferer. -/
theorem _root_.Infer.sourceSound (h : Infer K F frontier ctx input next subst output ty) :
    CtxWF ctx → TypeOfHM (subst.onCtx ctx) output ty := by
  match h with
  | .primLitUnit => intro _; simpa only [Subst.onCtx_nil] using (TypeOfHM.primLitUnit (ctx := _))
  | .primLitInt => intro _; simpa only [Subst.onCtx_nil] using (TypeOfHM.primLitInt (ctx := _))
  | .primLitNat => intro _; simpa only [Subst.onCtx_nil] using (TypeOfHM.primLitNat (ctx := _))
  | .primLitChar => intro _; simpa only [Subst.onCtx_nil] using (TypeOfHM.primLitChar (ctx := _))
  | .primBinOpIntAdd => intro _; simpa only [Subst.onCtx_nil] using (TypeOfHM.primBinOpIntAdd (ctx := _))
  | .primBinOpIntSub => intro _; simpa only [Subst.onCtx_nil] using (TypeOfHM.primBinOpIntSub (ctx := _))
  | .primBinOpIntLt hT ht hF hf =>
      intro _
      simpa only [Subst.onCtx_nil] using (TypeOfHM.primBinOpIntLt
        (Ctor.IsBoolCtor.typeOfHM hT ht) (Ctor.IsBoolCtor.typeOfHM hF hf))
  | .primBinOpCharLt hT ht hF hf =>
      intro _
      simpa only [Subst.onCtx_nil] using (TypeOfHM.primBinOpCharLt
        (Ctor.IsBoolCtor.typeOfHM hT ht) (Ctor.IsBoolCtor.typeOfHM hF hf))
  | .var (scheme := scheme) (frontier := frontier) hlook =>
      intro hctx
      simp only [Subst.onCtx_nil]
      refine TypeOfHM.var (polyTy := scheme)
        (instArgs := (freshVars frontier scheme.paramCount).map Ty.fvar) hlook ?_ ?_
      · intro ty ht
        obtain ⟨_, _, rfl⟩ := List.mem_map.mp ht
        exact .fvar
      · exact InstantiatesBy.openVars (hctx _ (List.mem_of_getElem? hlook)) (by simp)
  | .ctor (ctor := ctor) (frontier := frontier) hlook =>
      intro _
      simp only [Subst.onCtx_nil]
      refine TypeOfHM.ctor (ctor := ctor)
        (tyArgs := (freshVars frontier ctor.paramCount).map Ty.fvar) hlook ?_ ?_
      · intro ty ht
        obtain ⟨_, _, rfl⟩ := List.mem_map.mp ht
        exact .fvar
      · exact InstantiatesBy.openVars (Ctor.toTy_wf ctor) (by simp [Ctor.toTy])
  | @Infer.lambda K F ann body frontier param initial ctx next subst completed bodyTy _ hs hb =>
      intro hctx
      have hbodyCtx : CtxWF { ctx with env := PolyTy.mkTrivial param :: ctx.env } := by
        intro scheme hscheme
        rcases List.mem_cons.mp hscheme with rfl | hscheme
        · exact hs.lc
        · exact hctx scheme hscheme
      have hsubst := (hb.lc hbodyCtx).2
      refine TypeOfHM.lambda (Subst.onTy_lc hsubst hs.lc) ?_ rfl ?_
      · intro expected heq
        cases ann with
        | none => cases heq
        | some template => exact Option.some.inj heq
      · simpa only [lambdaOutput, Subst.onCtx, Subst.onEnv, List.map_cons,
          Subst.onPolyTy, PolyTy.mkTrivial] using hb.sourceSound hbodyCtx
  | @Infer.app K F f arg frontier ctx first s1 fOut fTy second s2 argOut argTy s3 _ hf ha hu =>
      intro hctx
      have hs1 := (hf.lc hctx).2
      have haCtx := Subst.onCtx_wf hs1 hctx
      have hs2 := (ha.lc haCtx).2
      have hs3 := hu.unifies.lc (Subst.onTy_lc hs2 (hf.lc hctx).1)
        (.arrow (ha.lc haCtx).1 .fvar)
      have hfTyped := TypeOfHM.onSubst (s2 ++ s3)
        (fun pair hp => (List.mem_append.mp hp).elim (hs2 pair) (hs3 pair)) (hf.sourceSound hctx)
      have haTyped := TypeOfHM.onSubst s3 hs3 (ha.sourceSound haCtx)
      have heq : (s2 ++ s3).onTy fTy =
          .arrow (s3.onTy argTy) (s3.onTy (.fvar second)) := by
        simpa only [Unifies, Subst.onTy_append, Subst.onTy_arrow] using hu.unifies.unifies
      rw [heq] at hfTyped
      simp only [Subst.onCtx_append] at hfTyped
      simpa only [Subst.onCtx_append] using TypeOfHM.app hfTyped haTyped
  | @Infer.letIn K F ann rhs body frontier ctx first s1 rhsOut rhsTy checked sCheck next s2 bodyOut bodyTy
      _ hr hc hb =>
      intro hctx
      have hs1 := (hr.lc hctx).2
      have hrTy := (hr.lc hctx).1
      have hsCheck := hc.lc hrTy
      have checkedCtxWF := Subst.onCtx_wf hsCheck (Subst.onCtx_wf hs1 hctx)
      have checkedTyLC := Subst.onTy_lc hsCheck hrTy
      have bodyCtxWF : CtxWF
          { sCheck.onCtx (s1.onCtx ctx) with
            env := genScheme (K ++ softVars (substSoft (s1 ++ sCheck) F)) (sCheck.onCtx (s1.onCtx ctx)).env (sCheck.onTy rhsTy) ::
              (sCheck.onCtx (s1.onCtx ctx)).env } := by
        intro scheme hscheme
        rcases List.mem_cons.mp hscheme with rfl | hscheme
        · exact genScheme_wf checkedTyLC
        · exact checkedCtxWF scheme hscheme
      have hs2 := (hb.lc bodyCtxWF).2
      have rhsTyped := TypeOfHM.onSubst sCheck hsCheck (hr.sourceSound hctx)
      have rhsGeneral := TypeOfHM.generaliseAnnotated
        (names := genVars (K ++ softVars (substSoft (s1 ++ sCheck) F)) (sCheck.onCtx (s1.onCtx ctx)).env (sCheck.onTy rhsTy))
        rhsTyped genVars_nodup
        (fun name hn => genVars_not_mem hn)
      obtain ⟨avoid, rhsFinal⟩ := GeneralisesTo.onSubst_annotated
        (genScheme_wf checkedTyLC) rhsGeneral s2 hs2
      have bodyTyped := hb.sourceSound bodyCtxWF
      have hctxeq :
          s2.onCtx
            { sCheck.onCtx (s1.onCtx ctx) with
              env := genScheme (K ++ softVars (substSoft (s1 ++ sCheck) F)) (sCheck.onCtx (s1.onCtx ctx)).env (sCheck.onTy rhsTy) ::
                (sCheck.onCtx (s1.onCtx ctx)).env } =
          { (s1 ++ sCheck ++ s2).onCtx ctx with
            env := s2.onPolyTy (genScheme (K ++ softVars (substSoft (s1 ++ sCheck) F)) (sCheck.onCtx (s1.onCtx ctx)).env (sCheck.onTy rhsTy)) ::
              ((s1 ++ sCheck ++ s2).onCtx ctx).env } := by
        rw [Subst.onCtx_append, Subst.onCtx_append]
        rfl
      rw [hctxeq] at bodyTyped
      refine TypeOfHM.letIn (L := avoid) (Subst.onPolyTy_wf hs2 (genScheme_wf checkedTyLC))
        (fun _ heq => Option.some.inj heq) ?_ rfl bodyTyped
      simpa only [letOutput, genScheme, ← Subst.onCtx_append] using rhsFinal

  | @Infer.letSignature K F ann rhs body written frontier ctx first s1 rhsOut rhsTy checked sCheck next s2 bodyOut bodyTy
      hraw hprefix havoid _ hr hc hescape hb =>
    intro hctx
    have hlen : written.length = ann.paramCount := by simpa only [freshVars_length] using congrArg List.length hprefix
    have hnd : written.Nodup := hprefix ▸ freshVars_nodup
    obtain ⟨hrTy, hs1⟩ := hr.lc hctx
    have hsCheck := hc.lc (by simpa using hlen) hrTy
    have checkedCtxWF := Subst.onCtx_wf hsCheck (Subst.onCtx_wf hs1 hctx)
    have checkedTyLC := Subst.onTy_lc hsCheck hrTy
    have hscheme : (signatureScheme (ann.substTyFvars (s1 ++ sCheck))
        (K ++ softVars (substSoft (s1 ++ sCheck) F)) written
        (sCheck.onCtx (s1.onCtx ctx)) (sCheck.onTy rhsTy)).WF := by
      simpa only [BindingAnn.substTyFvars_append] using
        hc.scheme_wf (Q := K ++ softVars (substSoft (s1 ++ sCheck) F))
          (ctx := sCheck.onCtx (s1.onCtx ctx)) (by simpa using hlen) hrTy
    have hscopePost : ∀ v ∈ (ann.substTyFvars (s1 ++ sCheck)).rigidVars,
        v ∈ K ++ softVars (substSoft (s1 ++ sCheck) F) := by
      intro v hv
      obtain ⟨original, ho, hv⟩ := BindingAnn.rigidVars_substTyFvars hv
      exact scope_image (Subst.fixes_of_dom_avoids (fun p hp hk =>
        (List.mem_append.mp hp).elim
          (fun hp => hr.dom_avoids p hp (List.mem_append_left _ hk))
          (fun hp => hc.dom_avoids p hp (List.mem_append_left _ hk))))
        (hraw original (List.mem_append_left _ (List.mem_append_left _ ho))) hv
    have havoidPost : ∀ name ∈ written, name ∉ K ++ softVars (substSoft (s1 ++ sCheck) F) := by
      intro name hn hm
      rcases List.mem_append.mp hm with hK | hF
      · exact havoid name hn (List.mem_append_left _ hK)
      · exact hescape name hn (List.mem_append_right _ hF)
    have hnamesFresh : ∀ name ∈ written, name ∉ (sCheck.onCtx (s1.onCtx ctx)).env.freeVars :=
      fun name hn hm => hescape name hn (List.mem_append_left _ hm)
    have bodyCtxWF : CtxWF
        { sCheck.onCtx (s1.onCtx ctx) with
          env := signatureScheme (ann.substTyFvars (s1 ++ sCheck)) (K ++ softVars (substSoft (s1 ++ sCheck) F)) written (sCheck.onCtx (s1.onCtx ctx)) (sCheck.onTy rhsTy) ::
            (sCheck.onCtx (s1.onCtx ctx)).env } := by
      intro scheme hschemeMem
      rcases List.mem_cons.mp hschemeMem with rfl | hschemeMem
      · exact hscheme
      · exact checkedCtxWF scheme hschemeMem
    have hs2 := (hb.lc bodyCtxWF).2
    have rhsTyped := TypeOfHM.onSubst sCheck hsCheck (hr.sourceSound hctx)
    have rhsGeneral := TypeOfHM.generaliseAnnotated
      (names := signatureNames (ann.substTyFvars (s1 ++ sCheck)) (K ++ softVars (substSoft (s1 ++ sCheck) F)) written (sCheck.onCtx (s1.onCtx ctx)) (sCheck.onTy rhsTy))
      rhsTyped (by simpa only [BindingAnn.substTyFvars_append] using hc.names_nodup (Q := K ++ softVars (substSoft (s1 ++ sCheck) F)) hnd)
        (by simpa only [BindingAnn.substTyFvars_append] using hc.names_fresh (Q := K ++ softVars (substSoft (s1 ++ sCheck) F)) hnamesFresh)
    have hclose := hc.scheme_eq_close (Q := K ++ softVars (substSoft (s1 ++ sCheck) F))
      (ctx := sCheck.onCtx (s1.onCtx ctx)) (by simpa using hlen) hrTy hnd
      (by simpa only [BindingAnn.substTyFvars_append] using hscopePost) havoidPost
    simp only [← BindingAnn.substTyFvars_append] at hclose
    rw [← hclose] at rhsGeneral
    obtain ⟨avoid, rhsFinal⟩ := GeneralisesTo.onSubst_annotated hscheme rhsGeneral s2 hs2
    have bodyTyped := hb.sourceSound bodyCtxWF
    have hctxeq :
        s2.onCtx { sCheck.onCtx (s1.onCtx ctx) with
          env := signatureScheme (ann.substTyFvars (s1 ++ sCheck)) (K ++ softVars (substSoft (s1 ++ sCheck) F)) written (sCheck.onCtx (s1.onCtx ctx)) (sCheck.onTy rhsTy) ::
            (sCheck.onCtx (s1.onCtx ctx)).env } =
        { (s1 ++ sCheck ++ s2).onCtx ctx with
          env := s2.onPolyTy (signatureScheme (ann.substTyFvars (s1 ++ sCheck)) (K ++ softVars (substSoft (s1 ++ sCheck) F)) written (sCheck.onCtx (s1.onCtx ctx)) (sCheck.onTy rhsTy)) ::
            ((s1 ++ sCheck ++ s2).onCtx ctx).env } := by
      rw [Subst.onCtx_append, Subst.onCtx_append]
      rfl
    rw [hctxeq] at bodyTyped
    refine TypeOfHM.letIn (L := avoid) (Subst.onPolyTy_wf hs2 hscheme)
      (fun _ heq => Option.some.inj heq) ?_ rfl bodyTyped
    simpa only [letOutput, ← Subst.onCtx_append] using rhsFinal
  | .letRec hscope hann hvalid hstrata hsigned hexports houtputs hbody =>
    intro hctxWF
    expose_names
    have hvalid := hvalid.1
    obtain ⟨hraw, hctx, hK, hFvars⟩ := hscope
    have hF : ∀ t ∈ F, Ty.BelowFvars frontier t := by
      intro t ht
      apply Ty.BelowFvars.of_freeVars_lt
      intro v hv
      exact hFvars v (TyList.mem_freeVars_iff.mpr ⟨t, ht, hv⟩)
    have hannscope : ∀ ann ∈ anns, ∀ v ∈ ann.rigidVars, v ∈ K ++ softVars F := by
      intro ann ha v hv
      exact hraw v (List.mem_append_left _ (List.mem_append_left _ (List.mem_flatMap.mpr ⟨ann, ha, hv⟩)))
    have hrhsscope : ∀ rhs ∈ bindings, SourceScope K F rhs := by
      intro rhs hr v hv
      exact hraw v (List.mem_append_left _ (List.mem_append_right _ (rec_rhs_rigid_mem hr hv)))
    have hannbelow : ∀ ann ∈ anns, ∀ v ∈ ann.rigidVars, v < frontier := by
      intro ann ha v hv
      exact (List.mem_append.mp (hannscope ann ha v hv)).elim (hK v) (hFvars v)
    have hlen : anns.length = bindings.length := by simpa only [List.length_map] using hvalid.length
    have hinitFrame := RecState.Frame.init hctx
      (fun v hv => by obtain ⟨ann, ha, hv⟩ := List.mem_flatMap.mp hv; exact hannbelow ann ha v hv) hK hFvars
    have hinitLC := RecState.LC.init (base := frontier) hann
    have hinitBelow : (RecState.init frontier anns).Below (frontier + bindings.length) := by
      simpa only [hlen] using RecState.Below.init hannbelow
    have hctxSeed : CtxBelow (frontier + bindings.length) ctx :=
      fun M hm => (hctx M hm).mono (by omega)
    have hFSeed : ∀ t ∈ F, Ty.BelowFvars (frontier + bindings.length) t :=
      fun t ht => (hF t ht).mono (by omega)
    have hvalid0 : RecGroups.ValidResidualGroups (anns.map BindingAnn.recModeAnn) (bindings.map InferInput.erase) ([] ++ groups) := hvalid
    obtain ⟨hframe1, _⟩ := hstrata.frame_of_infer
      (fun _ hi => hi.sourceLocality) hvalid0 hinitFrame hinitLC hctxWF hinitBelow hctxSeed hFSeed
      (by omega) hannscope hrhsscope
    have htyped1 := hstrata.sourceSound_of_infer
      (fun _ hi => hi.sourceLocality) hvalid0 hinitFrame hinitLC hctxWF hinitBelow hctxSeed hFSeed
      (by omega) hannscope hrhsscope (fun _ hi => hi.sourceSound) RecState.SourceTyped.init
    obtain ⟨hS1, hLC1⟩ := hstrata.lc_of_infer (fun _ hi => hi.lc) hctxWF hinitLC
    obtain ⟨hB1, hBelow1⟩ := hstrata.belowFvars_of_infer (fun _ hi => hi.belowFvars)
      hctxSeed (fun k hk => Nat.lt_of_lt_of_le (hK k hk) (by omega)) hFSeed hinitBelow
      (fun ann ha v hv => Nat.lt_of_lt_of_le (hannbelow ann ha v hv) (by omega))
    have hvalid1 := recValid_subst hvalid s1
    have hdone1 := hframe1.all_mono_done hvalid1
    obtain ⟨hframe2, _⟩ := hsigned.frame_of_infer
      (fun _ hi => hi.sourceLocality) hframe1 (by simp) hdone1 hBelow1.2.2.2
    have htyped2 := hsigned.sourceSound_of_infer
      (fun he hi => hi.sourceSound) (Subst.onCtx_wf hS1 hctxWF) hLC1 htyped1
      (hframe1.exports_length.trans hframe1.specs_length.symm)
      (hframe1.outputs_length.trans hframe1.exports_length.symm)
      (fun j scheme ha => by simpa only [Nat.zero_add] using hframe1.complete_export ha)
    obtain ⟨hS2, hLC2⟩ := hsigned.lc_of_infer (fun _ hi => hi.lc) (Subst.onCtx_wf hS1 hctxWF) hLC1
    have hbodyCtx := hLC2.rhsCtx (Subst.onCtx_wf hS2 (Subst.onCtx_wf hS1 hctxWF))
    rw [← Subst.onCtx_append] at hbodyCtx
    obtain ⟨_, hS3⟩ := hbody.lc hbodyCtx
    have hbodyTyped := hbody.sourceSound hbodyCtx
    have htypedFinal := htyped2.onSubst s3 hS3
    have hfinalExports : (state2.onSubst s3).exports = (schemes.map s3.onPolyTy).map some := by
      simp only [RecState.onSubst, hexports, List.map_map]
      rfl
    have hfinalOutputs : (state2.onSubst s3).outputs = (outputs.map (Expr.substTyFvars s3)).map some := by
      simp only [RecState.onSubst, houtputs, List.map_map]
      rfl
    have hresult := htypedFinal.letRec hfinalExports hfinalOutputs
      (by simpa only [RecState.onSubst, List.length_map] using hframe2.specs_length.trans hframe2.exports_length.symm)
      (by simpa only [RecState.onSubst, List.length_map] using hframe2.outputs_length.trans hframe2.exports_length.symm)
      (by simpa only [RecState.rhsCtx_onSubst, Subst.onCtx_append] using hbodyTyped)
    simpa only [Subst.onCtx_append] using hresult
  | .match_ _ hs hne hb =>
    intro hctx
    have hs1 := (hs.lc hctx).2
    have hbr := hb.lc (Subst.onCtx_wf hs1 hctx) (hs.lc hctx).1 .fvar
    have hscrut := TypeOfHM.onSubst _ hbr.2 (hs.sourceSound hctx)
    have hbranches := hb.sourceSound (Subst.onCtx_wf hs1 hctx) (hs.lc hctx).1 .fvar
    simpa only [Subst.onCtx_append] using
      TypeOfHM.match_ hscrut (fun hnil => hne (substInputBranches_eq_nil _ _ |>.mp (hb.nil_iff.mp hnil))) hbranches
termination_by (input.size, 0)
decreasing_by
  all_goals simp only [sizeBindings_map_substTyFvars] at *
  all_goals (simp only [InferInput.size, InferInput.size_openTyVars, InferInput.size_substTyFvars, sizeBranches_substInputBranches]; omega)

theorem _root_.InferBranches.sourceSound
    (h : InferBranches K F frontier ctx scrutTy resultTy branches next subst completed)
    (hctx : CtxWF ctx) (hscrut : scrutTy.IsLC) (hresult : resultTy.IsLC) :
    ∀ branch ∈ completed, TypeOfMatchBranch (subst.onCtx ctx) branch
      (subst.onTy scrutTy) (subst.onTy resultTy) := by
  match h with
  | .nil => intro branch hb; cases hb
  | @InferBranches.consWild body rest K F frontier ctx first s1 bodyOut bodyTy resultTy s2 scrutTy next s3 restOut
      _ hb hu hr =>
    obtain ⟨hbTy, hs1⟩ := hb.lc hctx
    have hs2 := hu.unifies.lc hbTy (Subst.onTy_lc hs1 hresult)
    have hctxRest := Subst.onCtx_wf hs2 (Subst.onCtx_wf hs1 hctx)
    have hscrutRest := Subst.onTy_lc hs2 (Subst.onTy_lc hs1 hscrut)
    have hresultRest := Subst.onTy_lc hs2 (Subst.onTy_lc hs1 hresult)
    have hs3 := (hr.lc hctxRest hscrutRest hresultRest).2
    have htail := hr.sourceSound hctxRest hscrutRest hresultRest
    intro branch hbranch
    rcases List.mem_cons.mp hbranch with rfl | hbranch
    · have head := TypeOfHM.onSubst (s2 ++ s3)
        (fun p hp => (List.mem_append.mp hp).elim (hs2 p) (hs3 p)) (hb.sourceSound hctx)
      have heq := congrArg s3.onTy hu.unifies.unifies
      rw [Subst.onTy_append] at head
      rw [heq] at head
      simpa only [Subst.onCtx_append, Subst.onTy_append, List.append_assoc] using
        (TypeOfMatchBranch.wildcard (scrutTy := (s1 ++ s2 ++ s3).onTy scrutTy) head)
    · simpa only [Subst.onCtx_append, Subst.onTy_append] using htail branch hbranch
  | @InferBranches.cons name count body rest K F ctor scrutTy frontier s0 ctx first s1 bodyOut bodyTy resultTy s2 next s3 restOut
      _ hlookup hcount hu0 hb hu hr =>
    have hs0 := hu0.unifies.lc hscrut
      (.customTy (fun t ht => by obtain ⟨v, _, rfl⟩ := List.mem_map.mp ht; exact .fvar))
    have hbodyWF := branchBindings_wf (ctorr := ctor)
      (ta := ((freshVars frontier ctor.paramCount).map Ty.fvar).map s0.onTy)
      (Subst.onCtx_wf hs0 hctx)
      (fun t ht => by
        obtain ⟨v, hv, rfl⟩ := List.mem_map.mp ht
        obtain ⟨x, _, rfl⟩ := List.mem_map.mp hv
        exact Subst.onTy_lc hs0 .fvar) (by simp)
    obtain ⟨hbTy, hs1⟩ := hb.lc hbodyWF
    have hs2 := hu.unifies.lc hbTy (Subst.onTy_lc hs1 (Subst.onTy_lc hs0 hresult))
    have hctxRest := Subst.onCtx_wf hs2 (Subst.onCtx_wf hs1 (Subst.onCtx_wf hs0 hctx))
    have hscrutRest := Subst.onTy_lc hs2 (Subst.onTy_lc hs1 (Subst.onTy_lc hs0 hscrut))
    have hresultRest := Subst.onTy_lc hs2 (Subst.onTy_lc hs1 (Subst.onTy_lc hs0 hresult))
    have hs3 := (hr.lc hctxRest hscrutRest hresultRest).2
    have htail := hr.sourceSound hctxRest hscrutRest hresultRest
    intro branch hbranch
    rcases List.mem_cons.mp hbranch with rfl | hbranch
    · let args := (((freshVars frontier ctor.paramCount).map Ty.fvar).map s0.onTy).map s1.onTy
      have hspec : BranchCtorSpec (s1.onCtx (s0.onCtx ctx)).ctors name count
          (s1.onTy (s0.onTy scrutTy)) ctor args (ctor.contents.map (Ty.openWith args)) := by
        refine ⟨hlookup, ?_, ?_, hcount, ?_⟩
        · simpa only [Subst.onTy_customTy, args] using congrArg s1.onTy hu0.unifies.unifies
        · simp only [args, List.length_map, freshVars_length]
        · exact forall₂_self_map (fun t ht => InstantiatesBy.openWith (ctor.bound t ht)
            (by simp only [args, List.length_map, freshVars_length]; omega))
      have head0 := TypeOfMatchBranch.mk hspec (Subst.onCtx_branchBindings hs1) (hb.sourceSound hbodyWF)
      have head := head0.onSubst (s2 ++ s3)
        (fun p hp => (List.mem_append.mp hp).elim (hs2 p) (hs3 p))
      have heq := congrArg s3.onTy hu.unifies.unifies
      simp only [Subst.onTy_append] at head
      rw [heq] at head
      simpa only [Subst.onCtx_append, Subst.onTy_append] using head
    · simpa only [Subst.onCtx_append, Subst.onTy_append] using htail branch hbranch
termination_by (sizeBranches branches, 0)
decreasing_by all_goals (simp only [sizeBranches, InferInput.size_substTyFvars, sizeBranches_substInputBranches]; omega)
end


private theorem eraseBindings_eq_map (bindings : List InferInput) :
    bindings.map InferInput.erase = eraseBindings bindings := by
  induction bindings with
  | nil => rfl
  | cons rhs rest ih => simp only [List.map_cons, eraseBindings, ih]

/-- Every stored completed RHS retains the erased source at its original slot. -/
def RecState.Erases (erased : List Expr) (state : RecState) : Prop :=
  state.outputs.length = erased.length ∧
  ∀ (i : Nat) (output : Expr), state.outputs[i]? = some (some output) → erased[i]? = some output.erase

 theorem RecState.Erases.init {base : Nat} {anns : List BindingAnn}
    (hlen : anns.length = erased.length) : (RecState.init base anns).Erases erased := by
  constructor
  · simpa only [RecState.init, List.length_map] using hlen
  · intro i output hget
    simp only [RecState.init, List.getElem?_map] at hget
    cases ha : anns[i]? <;> simp [ha] at hget

 theorem RecState.Erases.onSubst {state : RecState} (h : state.Erases erased) (S : Subst) :
    (state.onSubst S).Erases erased := by
  refine ⟨by simpa only [RecState.onSubst, List.length_map] using h.1, ?_⟩
  intro i output hget
  rw [RecState.onSubst, List.getElem?_map] at hget
  obtain ⟨old, ho, heq⟩ := Option.map_eq_some_iff.mp hget
  obtain ⟨rhs, hrhs, rfl⟩ := Option.map_eq_some_iff.mp heq
  simpa only [Expr.erase_substTyFvars] using h.2 i rhs (hrhs ▸ ho)

 theorem RecState.Erases.installOpenings {state : RecState} (h : state.Erases erased) :
    (state.installOpenings members openings).Erases erased := h

 theorem RecState.Erases.exportComponent {state : RecState} (h : state.Erases erased)
    {outputs : List (Option Expr)} {facts : List RecFacts} {pool : List Nat}
    (hout : ∀ (i : Nat) (output : Expr), outputs[i]? = some (some output) → erased[i]? = some output.erase) :
    (state.exportComponent members written pool outputs facts).Erases erased := by
  refine ⟨by simpa only [RecState.exportComponent, List.length_mapIdx] using h.1, ?_⟩
  intro i output hget
  rw [RecState.exportComponent, List.getElem?_mapIdx] at hget
  obtain ⟨old, hold, heq⟩ := Option.map_eq_some_iff.mp hget
  split at heq
  · obtain ⟨spec, _, hbind⟩ := Option.bind_eq_some_iff.mp heq
    obtain ⟨ty, _, hbind⟩ := Option.bind_eq_some_iff.mp hbind
    obtain ⟨rhs, hrhs, hclose⟩ := Option.bind_eq_some_iff.mp hbind
    obtain ⟨inner, hinner, hinnerEq⟩ := Option.bind_eq_some_iff.mp hrhs
    cases hinnerEq
    cases Option.some.inj hclose
    simpa only [Expr.erase_closeTyVars] using hout i rhs hinner
  · exact h.2 i output (heq ▸ hold)

 theorem FinishRecComponent.erases
    (h : FinishRecComponent K soft members ctx state outputs facts final)
    (hstate : state.Erases erased)
    (hout : ∀ (i : Nat) (output : Expr), outputs[i]? = some (some output) → erased[i]? = some output.erase) :
    final.Erases erased := by
  cases h
  exact hstate.exportComponent hout

 theorem RecState.Erases.setSigned {state : RecState} (h : state.Erases erased)
    {facts : RecFacts} (hout : erased[member]? = some output.erase) :
    (state.setSigned member names output facts).Erases erased := by
  refine ⟨by simpa only [RecState.setSigned, List.length_set] using h.1, ?_⟩
  intro i rhs hget
  by_cases hi : member = i
  · subst i
    have hlt : member < state.outputs.length := by
      rw [h.1]
      exact List.getElem?_eq_some_iff.mp hout |>.1
    rw [RecState.setSigned, List.getElem?_set_self hlt] at hget
    cases Option.some.inj (Option.some.inj hget)
    simpa only [Expr.erase_closeTyVars] using hout
  · exact h.2 i rhs (by simpa only [RecState.setSigned, List.getElem?_set_ne hi] using hget)

 theorem RecState.Erases.outputs_eq {state : RecState} {outputs : List Expr} (h : state.Erases erased)
    (hout : state.outputs = outputs.map some) : outputs.map Expr.erase = erased := by
  have hlen : outputs.length = erased.length := by simpa only [hout, List.length_map] using h.1
  apply List.ext_getElem?
  intro i
  cases ho : outputs[i]? with
  | none =>
      have hi : outputs.length ≤ i := List.getElem?_eq_none_iff.mp ho
      simp only [List.getElem?_map, ho, Option.map_none]
      exact (List.getElem?_eq_none_iff.mpr (hlen ▸ hi)).symm
  | some output =>
      exact (by simpa only [List.getElem?_map, ho, Option.map_some] using
        (h.2 i output (by rw [hout, List.getElem?_map, ho]; rfl)).symm)

@[simp] theorem erase_openRecSources (openings : List RecOpening) (bindings : List InferInput) :
    (openRecSources openings bindings).map InferInput.erase = bindings.map InferInput.erase := by
  induction bindings generalizing openings with
  | nil => cases openings <;> rfl
  | cons rhs rest ih =>
    cases openings with
    | nil => rfl
    | cons opening openings => simp only [openRecSources, List.map_cons, InferInput.erase_openTyVars, ih]

@[simp] theorem erase_map_subst_inputs (bindings : List InferInput) (S : Subst) :
    (bindings.map (InferInput.substTyFvars S)).map InferInput.erase = bindings.map InferInput.erase := by
  simp only [List.map_map, Function.comp_def, InferInput.erase_substTyFvars]

 theorem _root_.InferRecComponent.erase_of_infer
    (h : InferRecComponent K F members index frontier ctx bindings specs next S outputs facts)
    (hInfer : ∀ {κ F' Ψ c e Ψ' T output ty}, e.size ≤ sizeBindings bindings →
      Infer κ F' Ψ c e Ψ' T output ty → output.erase = e.erase) :
    ∀ (i : Nat) (output : Expr), outputs[i]? = some (some output) → (bindings.map InferInput.erase)[i]? = some output.erase := by
  match h with
  | .nil => intro i output hget; simp at hget
  | .skipMono _ hr | .skipPoly hr =>
      intro i output hget
      cases i with
      | zero => cases hget
      | succ i =>
          exact hr.erase_of_infer
            (fun he h => hInfer (by simp only [sizeBindings]; omega) h) i output hget
  | .consSelected _ hi _ hr =>
      intro i output hget
      cases i with
      | zero =>
        cases Option.some.inj (Option.some.inj hget)
        simp only [List.map_cons, List.getElem?_cons_zero, Expr.erase_substTyFvars,
          hInfer (by simp only [sizeBindings]; omega) hi]
      | succ i =>
        have hh := hr.erase_of_infer
          (fun he h => hInfer (by simp only [sizeBindings_map_substTyFvars] at he; simp only [sizeBindings]; omega) h)
          i output hget
        simpa only [erase_map_subst_inputs] using hh
 termination_by structural h

 theorem _root_.InferRecStrata.erase_of_infer
    (h : InferRecStrata K F frontier ctx anns bindings state groups next S final)
    (hInfer : ∀ {κ F' Ψ c e Ψ' T output ty}, e.size ≤ sizeBindings bindings →
      Infer κ F' Ψ c e Ψ' T output ty → output.erase = e.erase)
    (hstate : state.Erases (bindings.map InferInput.erase)) : final.Erases (bindings.map InferInput.erase) := by
  match h with
  | .nil => exact hstate
  | .cons _ _ hc he hr =>
      have hcomponent := hc.erase_of_infer
        (fun hsize h => hInfer (by simpa only [sizeBindings_map_substTyFvars, sizeBindings_openRecSources] using hsize) h)
      have hready := he.erases ((hstate.installOpenings).onSubst _) (by
        simpa only [erase_map_subst_inputs, erase_openRecSources] using hcomponent)
      have htail := hr.erase_of_infer
        (fun hsize h => hInfer (by simpa only [sizeBindings_map_substTyFvars] using hsize) h)
        (by simpa only [erase_map_subst_inputs] using hready)
      simpa only [erase_map_subst_inputs] using htail
 termination_by structural h

private theorem erased_remaining_tail {erased : List Expr} {rhs : InferInput} {bindings : List InferInput}
    (h : (rhs :: bindings).map InferInput.erase = erased.drop index) :
    bindings.map InferInput.erase = erased.drop (index + 1) := by
  have ht := congrArg (List.drop 1) h
  simpa only [List.map_cons, List.drop_succ_cons, List.drop_zero, List.drop_drop] using ht

 theorem _root_.InferRecSigned.erase_of_infer
    (h : InferRecSigned K F index frontier ctx anns bindings state next S final)
    (hInfer : ∀ {κ F' Ψ c e Ψ' T output ty}, e.size ≤ sizeBindings bindings →
      Infer κ F' Ψ c e Ψ' T output ty → output.erase = e.erase)
    (hstate : state.Erases erased) (hremaining : bindings.map InferInput.erase = erased.drop index) :
    final.Erases erased := by
  match h with
  | .nil => exact hstate
  | .skip _ hr =>
      exact hr.erase_of_infer (fun he h => hInfer (by simp only [sizeBindings]; omega) h)
        hstate (erased_remaining_tail hremaining)
  | .cons _ _ hi _ _ hr =>
      expose_names
      have he := hInfer (by simp only [InferInput.size_openTyVars, sizeBindings]; omega) hi
      have hhead := congrArg (fun xs => xs[0]?) hremaining
      simp only [List.map_cons, List.getElem?_cons_zero, List.getElem?_drop, Nat.add_zero] at hhead
      have hready : ((state.onSubst (s1 ++ s2)).setSigned index (freshVars frontier scheme.paramCount)
          (output.substTyFvars s2) (bodyFacts.onSubst s2)).Erases erased :=
        (hstate.onSubst _).setSigned (by
        simpa only [Expr.erase_substTyFvars, InferInput.erase_openTyVars, he] using hhead.symm)
      exact hr.erase_of_infer
        (fun he h => hInfer (by simp only [sizeBindings_map_substTyFvars] at he; simp only [sizeBindings]; omega) h)
        hready (by simpa only [erase_map_subst_inputs] using erased_remaining_tail hremaining)
 termination_by structural h


mutual
/-- Inference completes annotations and binders while preserving runtime syntax. -/
theorem _root_.Infer.erase (h : Infer K F frontier ctx input next subst output ty) :
    output.erase = input.erase := by
  match h with
  | .primLitUnit | .primLitInt | .primLitNat | .primLitChar | .primBinOpIntAdd | .primBinOpIntSub | .primBinOpIntLt _ _ _ _ | .primBinOpCharLt _ _ _ _ | .var _ | .ctor _ => simp only [Expr.erase, InferInput.erase]
  | .lambda _ _ hb =>
      simpa only [lambdaOutput, Expr.erase, InferInput.erase] using
        congrArg (Expr.lambda none) hb.erase
  | .app _ hf ha _ =>
      simp only [Expr.erase, Expr.erase_substTyFvars, InferInput.erase, hf.erase, ha.erase, InferInput.erase_substTyFvars]
  | .letIn _ hr _ hb =>
      simp only [letOutput, Expr.erase, Expr.erase_substTyFvars,
        Expr.erase_closeTyVars, InferInput.erase, hr.erase, hb.erase, InferInput.erase_substTyFvars]
  | .letSignature _ _ _ _ hr _ _ hb =>
      simp only [letOutput, Expr.erase, Expr.erase_substTyFvars,
        Expr.erase_closeTyVars, InferInput.erase, hr.erase, hb.erase, InferInput.erase_openTyVars, InferInput.erase_substTyFvars]
  | .match_ _ hs _ hb =>
      simp only [Expr.erase, Expr.erase_substTyFvars, InferInput.erase, hs.erase, hb.erase, eraseBranches_substInputBranches]
  | .letRec _ _ hv hs hp _ hout hb =>
      expose_names
      have hv := hv.1
      have hstate1 := hs.erase_of_infer (fun _ hi => hi.erase)
        (RecState.Erases.init (by simpa only [List.length_map] using hv.length))
      have hstate2 := hp.erase_of_infer (fun _ hi => hi.erase)
        (by simpa only [erase_map_subst_inputs] using hstate1)
        (by simp only [erase_map_subst_inputs, List.drop_zero])
      have houtputs := hstate2.outputs_eq hout
      have hlen := congrArg List.length houtputs
      simp only [List.length_map] at hlen
      simp only [Expr.erase_letRec, InferInput.erase, List.map_map, Function.comp_def,
        Expr.erase_substTyFvars, houtputs, hb.erase, InferInput.erase_substTyFvars,
        eraseBindings_eq_map]
      congr 1
      simpa only [List.map_const'] using congrArg (fun n => List.replicate n (none : Option PolyTy)) hlen
termination_by (input.size, 0)
decreasing_by
  all_goals simp only [sizeBindings_map_substTyFvars] at *
  all_goals (simp only [InferInput.size, InferInput.size_openTyVars, InferInput.size_substTyFvars, sizeBranches_substInputBranches]; omega)

theorem _root_.InferBranches.erase
    (h : InferBranches K F frontier ctx scrutTy resultTy branches next subst completed) :
    completed.map (fun pe => (pe.1, pe.2.erase)) = eraseBranches branches := by
  match h with
  | .nil => rfl
  | .consWild _ hb _ hr =>
      simp only [List.map_cons, eraseBranches, Expr.erase_substTyFvars, hb.erase, hr.erase, eraseBranches_substInputBranches]
  | .cons _ _ _ _ hb _ hr =>
      simp only [List.map_cons, eraseBranches, Expr.erase_substTyFvars, hb.erase, hr.erase, InferInput.erase_substTyFvars, eraseBranches_substInputBranches]
termination_by (sizeBranches branches, 0)
decreasing_by all_goals (simp only [sizeBranches, InferInput.size_substTyFvars, sizeBranches_substInputBranches]; omega)
end

theorem _root_.Infer.sound (h : Infer K F frontier ctx input next subst output ty) (hctx : CtxWF ctx) :
    RuntimeTyping.RunWT (subst.onCtx ctx) input.erase ty := by
  rw [← h.erase]
  exact (h.sourceSound hctx).erase_preserves_typing

theorem InputTyping.onSubst_soft {K : List Nat} {F : List Ty}
    (h : InputTyping (K ++ softVars F) ctx input ty) (subst : Subst)
    (hlc : ∀ p ∈ subst, p.2.IsLC) (havoid : ∀ p ∈ subst, p.1 ∉ K) :
    InputTyping (K ++ softVars (substSoft subst F)) (subst.onCtx ctx)
      (input.substTyFvars subst) (subst.onTy ty) :=
  h.onSubst_source subst hlc (fun _ hk _ hv => scope_image (Subst.fixes_of_dom_avoids havoid) hk hv)

theorem BranchTyping.onSubst_soft {K : List Nat} {F : List Ty}
    (h : BranchTyping InputTyping (K ++ softVars F) ctx branch scrutTy resultTy) (subst : Subst)
    (hlc : ∀ p ∈ subst, p.2.IsLC) (havoid : ∀ p ∈ subst, p.1 ∉ K) :
    BranchTyping InputTyping (K ++ softVars (substSoft subst F)) (subst.onCtx ctx)
      (branch.1, branch.2.substTyFvars subst) (subst.onTy scrutTy) (subst.onTy resultTy) :=
  h.onSubst_source subst hlc (fun _ hk _ hv => scope_image (Subst.fixes_of_dom_avoids havoid) hk hv)

mutual
/-- Successful inference also satisfies the independent partial-input rules.
This connects input admissibility and completed-output typing at the same type. -/
theorem _root_.Infer.inputSound_source (h : Infer K F frontier ctx input next subst output ty) :
    CtxWF ctx → InputTyping (K ++ softVars (substSoft subst F)) (subst.onCtx ctx) (input.substTyFvars subst) ty := by
  match h with
  | leaf@(.primLitUnit) =>
      intro hctx
      exact .complete rfl (by simp [Expr.tyFreeVars]) (leaf.sourceSound hctx)
  | leaf@(.primLitInt) =>
      intro hctx
      exact .complete rfl (by simp [Expr.tyFreeVars]) (leaf.sourceSound hctx)
  | leaf@(.primLitNat) =>
      intro hctx
      exact .complete rfl (by simp [Expr.tyFreeVars]) (leaf.sourceSound hctx)
  | leaf@(.primLitChar) =>
      intro hctx
      exact .complete rfl (by simp [Expr.tyFreeVars]) (leaf.sourceSound hctx)
  | leaf@(.primBinOpIntAdd) =>
      intro hctx
      exact .complete rfl (by simp [Expr.tyFreeVars]) (leaf.sourceSound hctx)
  | leaf@(.primBinOpIntSub) =>
      intro hctx
      exact .complete rfl (by simp [Expr.tyFreeVars]) (leaf.sourceSound hctx)
  | leaf@(.primBinOpIntLt _ _ _ _) =>
      intro hctx
      exact .complete rfl (by simp [Expr.tyFreeVars]) (leaf.sourceSound hctx)
  | leaf@(.primBinOpCharLt _ _ _ _) =>
      intro hctx
      exact .complete rfl (by simp [Expr.tyFreeVars]) (leaf.sourceSound hctx)
  | leaf@(.var _) =>
      intro hctx
      exact .complete rfl (by simp [Expr.tyFreeVars]) (leaf.sourceSound hctx)
  | leaf@(.ctor _) =>
      intro hctx
      exact .complete rfl (by simp [Expr.tyFreeVars]) (leaf.sourceSound hctx)
  | @Infer.lambda K F ann body frontier param initial ctx next subst completed bodyTy _ hs hb =>
      intro hctx
      have hbodyCtx : CtxWF { ctx with env := PolyTy.mkTrivial param :: ctx.env } := by
        intro scheme hscheme
        rcases List.mem_cons.mp hscheme with rfl | hscheme
        · exact hs.lc
        · exact hctx scheme hscheme
      have hsubst := (hb.lc hbodyCtx).2
      simp only [InferInput.substTyFvars]
      refine InputTyping.lambda (Subst.onTy_lc hsubst hs.lc) ?_ ?_ ?_
      · intro template heq
        cases ann with
        | none => cases heq
        | some original =>
          cases heq
          exact (hs.fits original rfl).substTyFvars subst
      · intro template heq v hv
        cases ann with
        | none => cases heq
        | some original =>
          cases heq
          obtain ⟨old, hold, hv⟩ := TyTemplate.rigidVars_substTyFvars hv
          exact scope_image (Subst.fixes_of_dom_avoids hb.dom_avoids) (hs.rigid original rfl old hold) hv
      · simpa only [Subst.onCtx, Subst.onEnv, List.map_cons, Subst.onPolyTy,
          PolyTy.mkTrivial] using hb.inputSound_source hbodyCtx
  | @Infer.app K F f arg frontier ctx first s1 fOut fTy second s2 argOut argTy s3 _ hf ha hu =>
      intro hctx
      have hs1 := (hf.lc hctx).2
      have haCtx := Subst.onCtx_wf hs1 hctx
      have hs2 := (ha.lc haCtx).2
      have hs3 := hu.unifies.lc (Subst.onTy_lc hs2 (hf.lc hctx).1)
        (.arrow (ha.lc haCtx).1 .fvar)
      have hfTyped := (hf.inputSound_source hctx).onSubst_soft (s2 ++ s3)
        (fun pair hp => (List.mem_append.mp hp).elim (hs2 pair) (hs3 pair))
        (fun pair hp => (List.mem_append.mp hp).elim (ha.dom_avoids pair) (hu.dom_avoids pair))
      have haTyped := (ha.inputSound_source haCtx).onSubst_soft s3 hs3 hu.dom_avoids
      have heq : (s2 ++ s3).onTy fTy =
          .arrow (s3.onTy argTy) (s3.onTy (.fvar second)) := by
        simpa only [Unifies, Subst.onTy_append, Subst.onTy_arrow] using hu.unifies.unifies
      rw [heq] at hfTyped
      simp only [Subst.onCtx_append] at hfTyped
      simp only [← substSoft_append, ← InferInput.substTyFvars_append, List.append_assoc] at hfTyped haTyped
      simpa only [Subst.onCtx_append, InferInput.substTyFvars, List.append_assoc] using InputTyping.app hfTyped haTyped
  | @Infer.letIn K F ann rhs body frontier ctx first s1 rhsOut rhsTy checked sCheck next s2 bodyOut bodyTy
      hraw hr hc hb =>
      intro hctx
      have hs1 := (hr.lc hctx).2
      have hrTy := (hr.lc hctx).1
      have hsCheck := hc.lc hrTy
      have hprefixAvoid : ∀ p ∈ s1 ++ sCheck, p.1 ∉ K := fun p hp =>
        (List.mem_append.mp hp).elim (hr.dom_avoids p) (hc.dom_avoids p)
      have hpost := hraw.subst (s1 ++ sCheck) (Subst.fixes_of_dom_avoids hprefixAvoid)
      have hann : ∀ template, (ann.substTyFvars (s1 ++ sCheck)) = .template template →
          ∀ v ∈ template.rigidVars, v ∈ K ++ softVars (substSoft (s1 ++ sCheck) F) := by
        intro template heq v hv
        exact hpost v (List.mem_append_left _ (List.mem_append_left _ (by
          simpa only [BindingAnn.rigidVars, heq] using hv)))
      have hfit : (ann.substTyFvars (s1 ++ sCheck)).FitsMono (sCheck.onTy rhsTy) := by
        simpa only [BindingAnn.substTyFvars_append] using hc.fits
      have checkedCtxWF := Subst.onCtx_wf hsCheck (Subst.onCtx_wf hs1 hctx)
      have checkedTyLC := Subst.onTy_lc hsCheck hrTy
      have bodyCtxWF : CtxWF
          { sCheck.onCtx (s1.onCtx ctx) with
            env := genScheme (K ++ softVars (substSoft (s1 ++ sCheck) F))
              (sCheck.onCtx (s1.onCtx ctx)).env (sCheck.onTy rhsTy) ::
              (sCheck.onCtx (s1.onCtx ctx)).env } := by
        intro scheme hscheme
        rcases List.mem_cons.mp hscheme with rfl | hscheme
        · exact genScheme_wf checkedTyLC
        · exact checkedCtxWF scheme hscheme
      have hs2 := (hb.lc bodyCtxWF).2
      have rhsTyped := (hr.inputSound_source hctx).onSubst_soft sCheck hsCheck hc.dom_avoids
      simp only [← substSoft_append, ← InferInput.substTyFvars_append] at rhsTyped
      have rhsGeneral := rhsTyped.generalise
        (names := genVars (K ++ softVars (substSoft (s1 ++ sCheck) F))
          (sCheck.onCtx (s1.onCtx ctx)).env (sCheck.onTy rhsTy))
        hfit hann genVars_nodup (fun _ hn => genVars_not_mem hn)
        (fun _ hn => genVars_not_mem_rigid hn)
      obtain ⟨avoid, hfits, hgeneral⟩ := InputTyping.binding_onSubst_source
        (scheme := genScheme (K ++ softVars (substSoft (s1 ++ sCheck) F))
          (sCheck.onCtx (s1.onCtx ctx)).env (sCheck.onTy rhsTy))
        (fun fresh hf => (rhsGeneral fresh hf).1)
        (fun fresh hf => (rhsGeneral fresh hf).2) s2 hs2
        (fun _ hk _ hv => scope_image (Subst.fixes_of_dom_avoids hb.dom_avoids) hk hv)
      have hannFinal : ∀ template, (ann.substTyFvars (s1 ++ sCheck ++ s2)) = .template template →
          ∀ v ∈ template.rigidVars, v ∈ K ++ softVars (substSoft (s1 ++ sCheck ++ s2) F) := by
        have hp := hraw.subst (s1 ++ sCheck ++ s2) (Subst.fixes_of_dom_avoids
          (fun p hp => (List.mem_append.mp hp).elim (hprefixAvoid p) (hb.dom_avoids p)))
        intro template heq v hv
        exact hp v (List.mem_append_left _ (List.mem_append_left _ (by
          simpa only [BindingAnn.rigidVars, heq] using hv)))
      have bodyTyped := hb.inputSound_source bodyCtxWF
      have hctxeq :
          s2.onCtx
            { sCheck.onCtx (s1.onCtx ctx) with
              env := genScheme (K ++ softVars (substSoft (s1 ++ sCheck) F))
                (sCheck.onCtx (s1.onCtx ctx)).env (sCheck.onTy rhsTy) ::
                (sCheck.onCtx (s1.onCtx ctx)).env } =
          { (s1 ++ sCheck ++ s2).onCtx ctx with
            env := s2.onPolyTy (genScheme (K ++ softVars (substSoft (s1 ++ sCheck) F))
              (sCheck.onCtx (s1.onCtx ctx)).env (sCheck.onTy rhsTy)) ::
              ((s1 ++ sCheck ++ s2).onCtx ctx).env } := by
        rw [Subst.onCtx_append, Subst.onCtx_append]
        rfl
      rw [hctxeq] at bodyTyped
      simp only [← substSoft_append, ← InferInput.substTyFvars_append, ← BindingAnn.substTyFvars_append,
        List.append_assoc] at hfits hgeneral bodyTyped hannFinal ⊢
      refine InputTyping.letIn (L := avoid) (Subst.onPolyTy_wf hs2 (genScheme_wf checkedTyLC))
        hannFinal hfits ?_ bodyTyped
      intro fresh hfresh
      simpa only [← Subst.onCtx_append, List.append_assoc] using hgeneral fresh hfresh

  | @Infer.letSignature K F ann rhs body written frontier ctx first s1 rhsOut rhsTy checked sCheck next s2 bodyOut bodyTy
      hscope hprefix havoid hraw hr hc hescape hb =>
    intro hctx
    have hlen : written.length = ann.paramCount := by simpa only [freshVars_length] using congrArg List.length hprefix
    have hnd : written.Nodup := hprefix ▸ freshVars_nodup
    obtain ⟨hrTy, hs1⟩ := hr.lc hctx
    have hsCheck := hc.lc (by simpa using hlen) hrTy
    have checkedCtxWF := Subst.onCtx_wf hsCheck (Subst.onCtx_wf hs1 hctx)
    have checkedTyLC := Subst.onTy_lc hsCheck hrTy
    have hscheme : (signatureScheme (ann.substTyFvars (s1 ++ sCheck))
        (K ++ softVars (substSoft (s1 ++ sCheck) F)) written
        (sCheck.onCtx (s1.onCtx ctx)) (sCheck.onTy rhsTy)).WF := by
      simpa only [BindingAnn.substTyFvars_append] using
        hc.scheme_wf (Q := K ++ softVars (substSoft (s1 ++ sCheck) F))
          (ctx := sCheck.onCtx (s1.onCtx ctx)) (by simpa using hlen) hrTy
    have hscopePost : ∀ v ∈ (ann.substTyFvars (s1 ++ sCheck)).rigidVars,
        v ∈ K ++ softVars (substSoft (s1 ++ sCheck) F) := by
      intro v hv
      obtain ⟨original, ho, hv⟩ := BindingAnn.rigidVars_substTyFvars hv
      exact scope_image (Subst.fixes_of_dom_avoids (fun p hp hk =>
        (List.mem_append.mp hp).elim
          (fun hp => hr.dom_avoids p hp (List.mem_append_left _ hk))
          (fun hp => hc.dom_avoids p hp (List.mem_append_left _ hk))))
        (hscope original (List.mem_append_left _ (List.mem_append_left _ ho))) hv
    have havoidPost : ∀ name ∈ written, name ∉ K ++ softVars (substSoft (s1 ++ sCheck) F) := by
      intro name hn hm
      rcases List.mem_append.mp hm with hK | hF
      · exact havoid name hn (List.mem_append_left _ hK)
      · exact hescape name hn (List.mem_append_right _ hF)
    have hnamesFresh : ∀ name ∈ written, name ∉ (sCheck.onCtx (s1.onCtx ctx)).env.freeVars :=
      fun name hn hm => hescape name hn (List.mem_append_left _ hm)
    have bodyCtxWF : CtxWF
        { sCheck.onCtx (s1.onCtx ctx) with
          env := signatureScheme (ann.substTyFvars (s1 ++ sCheck)) (K ++ softVars (substSoft (s1 ++ sCheck) F)) written (sCheck.onCtx (s1.onCtx ctx)) (sCheck.onTy rhsTy) ::
            (sCheck.onCtx (s1.onCtx ctx)).env } := by
      intro scheme hschemeMem
      rcases List.mem_cons.mp hschemeMem with rfl | hschemeMem
      · exact hscheme
      · exact checkedCtxWF scheme hschemeMem
    have hs2 := (hb.lc bodyCtxWF).2
    have hprefixLC : ∀ p ∈ s1 ++ sCheck, p.2.IsLC := fun p hp =>
      (List.mem_append.mp hp).elim (hs1 p) (hsCheck p)
    have hprefixAvoid : ∀ p ∈ s1 ++ sCheck, p.1 ∉ K ++ written := fun p hp =>
      (List.mem_append.mp hp).elim (hr.dom_avoids p) (hc.dom_avoids p)
    have rhsTyped0 := (hr.inputSound_source hctx).onSubst_soft sCheck hsCheck hc.dom_avoids
    simp only [← substSoft_append, ← InferInput.substTyFvars_append] at rhsTyped0
    rw [InferInput.substTyFvars_openTyVars rhs hprefixLC
      (fun p hp hw => hprefixAvoid p hp (List.mem_append_right _ hw))] at rhsTyped0
    have rhsTyped : InputTyping ((K ++ softVars (substSoft (s1 ++ sCheck) F)) ++ written)
        (sCheck.onCtx (s1.onCtx ctx)) ((rhs.substTyFvars (s1 ++ sCheck)).openTyVars written)
        (sCheck.onTy rhsTy) := rhsTyped0.scope_mono (by
      intro k hk
      simp only [List.mem_append] at hk ⊢
      tauto)
    have hpost := hscope.subst (s1 ++ sCheck) (Subst.fixes_of_dom_avoids
      (fun p hp hk => hprefixAvoid p hp (List.mem_append_left _ hk)))
    have hrawPost : ∀ v ∈ (rhs.substTyFvars (s1 ++ sCheck)).rigidVars,
        v ∈ K ++ softVars (substSoft (s1 ++ sCheck) F) := fun v hv =>
      hpost v (List.mem_append_left _ (List.mem_append_right _ hv))
    have hcomp := hc.completion (Q := K ++ softVars (substSoft (s1 ++ sCheck) F))
      (ctx := sCheck.onCtx (s1.onCtx ctx)) (by simpa using hlen) hrTy
    simp only [← BindingAnn.substTyFvars_append] at hcomp
    have hnamesND := hc.names_nodup (Q := K ++ softVars (substSoft (s1 ++ sCheck) F))
      (ctx := sCheck.onCtx (s1.onCtx ctx)) hnd
    have hnamesAvoid := hc.names_avoid (ctx := sCheck.onCtx (s1.onCtx ctx)) havoidPost
    have hnamesFresh := hc.names_fresh (Q := K ++ softVars (substSoft (s1 ++ sCheck) F)) hnamesFresh
    simp only [← BindingAnn.substTyFvars_append] at hnamesND hnamesAvoid hnamesFresh
    obtain ⟨fitAvoid, hfits⟩ := hcomp.cofinite_fits hnamesND hnamesAvoid hscopePost checkedTyLC
    obtain ⟨typeAvoid, htypes⟩ := hcomp.cofinite_typing rhsTyped hscheme
      hnamesND hnamesFresh hnamesAvoid hscopePost hrawPost
    have hfitBoth := fun fresh (hf : FreshNames (fitAvoid ++ typeAvoid)
        (signatureScheme (ann.substTyFvars (s1 ++ sCheck))
          (K ++ softVars (substSoft (s1 ++ sCheck) F)) written
          (sCheck.onCtx (s1.onCtx ctx)) (sCheck.onTy rhsTy)).paramCount fresh) =>
      hfits fresh ⟨hf.length, hf.nodup, fun v hv ha => hf.avoid v hv (List.mem_append_left _ ha)⟩
    have htypeBoth := fun fresh (hf : FreshNames (fitAvoid ++ typeAvoid)
        (signatureScheme (ann.substTyFvars (s1 ++ sCheck))
          (K ++ softVars (substSoft (s1 ++ sCheck) F)) written
          (sCheck.onCtx (s1.onCtx ctx)) (sCheck.onTy rhsTy)).paramCount fresh) =>
      htypes fresh ⟨hf.length, hf.nodup, fun v hv ha => hf.avoid v hv (List.mem_append_right _ ha)⟩
    obtain ⟨avoid, hfitsFinal, htypesFinal⟩ := InputTyping.signatureBinding_onSubst_source
      hfitBoth htypeBoth s2 hs2
      (fun _ hk _ hv => scope_image (Subst.fixes_of_dom_avoids hb.dom_avoids) hk hv)
    have bodyTyped := hb.inputSound_source bodyCtxWF
    have hctxeq :
        s2.onCtx { sCheck.onCtx (s1.onCtx ctx) with
          env := signatureScheme (ann.substTyFvars (s1 ++ sCheck)) (K ++ softVars (substSoft (s1 ++ sCheck) F)) written (sCheck.onCtx (s1.onCtx ctx)) (sCheck.onTy rhsTy) ::
            (sCheck.onCtx (s1.onCtx ctx)).env } =
        { (s1 ++ sCheck ++ s2).onCtx ctx with
          env := s2.onPolyTy (signatureScheme (ann.substTyFvars (s1 ++ sCheck)) (K ++ softVars (substSoft (s1 ++ sCheck) F)) written (sCheck.onCtx (s1.onCtx ctx)) (sCheck.onTy rhsTy)) ::
            ((s1 ++ sCheck ++ s2).onCtx ctx).env } := by
      rw [Subst.onCtx_append, Subst.onCtx_append]
      rfl
    rw [hctxeq] at bodyTyped
    have hpostFinal := hscope.subst (s1 ++ sCheck ++ s2) (Subst.fixes_of_dom_avoids
      (fun p hp hk => (List.mem_append.mp hp).elim
        (fun hp => hprefixAvoid p hp (List.mem_append_left _ hk))
        (fun hp => hb.dom_avoids p hp hk)))
    have hannFinal : ∀ v ∈ (ann.substTyFvars (s1 ++ sCheck ++ s2)).rigidVars,
        v ∈ K ++ softVars (substSoft (s1 ++ sCheck ++ s2) F) := fun v hv =>
      hpostFinal v (List.mem_append_left _ (List.mem_append_left _ hv))
    have hrhsFinal : ∀ v ∈ (rhs.substTyFvars (s1 ++ sCheck ++ s2)).rigidVars,
        v ∈ K ++ softVars (substSoft (s1 ++ sCheck ++ s2) F) := fun v hv =>
      hpostFinal v (List.mem_append_left _ (List.mem_append_right _ hv))
    simp only [← substSoft_append, ← InferInput.substTyFvars_append, ← BindingAnn.substTyFvars_append,
      List.append_assoc] at hfitsFinal htypesFinal bodyTyped hannFinal hrhsFinal ⊢
    refine InputTyping.letSignature (L := avoid) (Subst.onPolyTy_wf hs2 hscheme)
      hannFinal hrhsFinal hfitsFinal ?_ bodyTyped
    intro fresh hfresh
    simpa only [← Subst.onCtx_append, List.append_assoc] using htypesFinal fresh hfresh

  | .letRec hscope hann hvalid hstrata hsigned hexports houtputs hbody =>
    intro hctxWF
    expose_names
    have hvalid := hvalid.1
    obtain ⟨hraw, hctx, hK, hFvars⟩ := hscope
    have hF : ∀ t ∈ F, Ty.BelowFvars frontier t := by
      intro t ht
      apply Ty.BelowFvars.of_freeVars_lt
      intro v hv
      exact hFvars v (TyList.mem_freeVars_iff.mpr ⟨t, ht, hv⟩)
    have hannscope : ∀ ann ∈ anns, ∀ v ∈ ann.rigidVars, v ∈ K ++ softVars F := by
      intro ann ha v hv
      exact hraw v (List.mem_append_left _ (List.mem_append_left _ (List.mem_flatMap.mpr ⟨ann, ha, hv⟩)))
    have hrhsscope : ∀ rhs ∈ bindings, SourceScope K F rhs := by
      intro rhs hr v hv
      exact hraw v (List.mem_append_left _ (List.mem_append_right _ (rec_rhs_rigid_mem hr hv)))
    have hannbelow : ∀ ann ∈ anns, ∀ v ∈ ann.rigidVars, v < frontier := by
      intro ann ha v hv
      exact (List.mem_append.mp (hannscope ann ha v hv)).elim (hK v) (hFvars v)
    have hlen : anns.length = bindings.length := by simpa only [List.length_map] using hvalid.length
    have hinitFrame := RecState.Frame.init hctx
      (fun v hv => by obtain ⟨ann, ha, hv⟩ := List.mem_flatMap.mp hv; exact hannbelow ann ha v hv) hK hFvars
    have hinitLC := RecState.LC.init (base := frontier) hann
    have hinitBelow : (RecState.init frontier anns).Below (frontier + bindings.length) := by
      simpa only [hlen] using RecState.Below.init hannbelow
    have hctxSeed : CtxBelow (frontier + bindings.length) ctx :=
      fun M hm => (hctx M hm).mono (by omega)
    have hFSeed : ∀ t ∈ F, Ty.BelowFvars (frontier + bindings.length) t :=
      fun t ht => (hF t ht).mono (by omega)
    have hvalid0 : RecGroups.ValidResidualGroups (anns.map BindingAnn.recModeAnn) (bindings.map InferInput.erase) ([] ++ groups) := hvalid
    obtain ⟨hframe1, _⟩ := hstrata.frame_of_infer
      (fun _ hi => hi.sourceLocality) hvalid0 hinitFrame hinitLC hctxWF hinitBelow hctxSeed hFSeed
      (by omega) hannscope hrhsscope
    have htrace1 := hstrata.inputTrace_of_infer
      (fun _ hi => hi.sourceLocality) hvalid0 hinitFrame hinitLC hctxWF hinitBelow hctxSeed hFSeed
      (by omega) hannscope hrhsscope (fun _ hi => hi.inputSound_source) (by
        intro stage component hc
        cases hc)
    obtain ⟨hS1, hLC1⟩ := hstrata.lc_of_infer (fun _ hi => hi.lc) hctxWF hinitLC
    obtain ⟨hB1, hBelow1⟩ := hstrata.belowFvars_of_infer (fun _ hi => hi.belowFvars)
      hctxSeed (fun k hk => Nat.lt_of_lt_of_le (hK k hk) (by omega)) hFSeed hinitBelow
      (fun ann ha v hv => Nat.lt_of_lt_of_le (hannbelow ann ha v hv) (by omega))
    have hvalid1 := recValid_subst hvalid s1
    have hdone1 := hframe1.all_mono_done hvalid1
    obtain ⟨hframe2, hpool2⟩ := hsigned.frame_of_infer
      (fun _ hi => hi.sourceLocality) hframe1 (by simp) hdone1 hBelow1.2.2.2
    obtain ⟨hS2, hLC2⟩ := hsigned.lc_of_infer (fun _ hi => hi.lc) (Subst.onCtx_wf hS1 hctxWF) hLC1
    have hbase1 : frontier ≤ first := (Nat.le_add_right frontier bindings.length).trans hstrata.frontier_le
    have hbase2 : frontier ≤ second := hbase1.trans hsigned.frontier_le
    have hctx1 := Subst.onCtx_below hB1 hbase1 hctx
    have hF1 := substSoft_below hB1 hbase1 hF
    obtain ⟨hB2, hBelow2⟩ := hsigned.belowFvars_of_infer (fun _ hi => hi.belowFvars)
      hctx1 (fun k hk => Nat.lt_of_lt_of_le (hK k hk) hbase1) hF1 hBelow1
      (by
        intro ann hm v hv
        obtain ⟨original, ho, rfl⟩ := List.mem_map.mp hm
        obtain ⟨k, hk, hv⟩ := BindingAnn.rigidVars_substTyFvars hv
        exact (Subst.onTy_belowFvars (hB1) ((Ty.BelowFvars.fvar (hannbelow original ho k hk)).mono hbase1)).mem_lt v hv)
    have hfix2 := Subst.fixes_of_dom_avoids hsigned.dom_avoids
    have htrace2' := htrace1.onSubst hframe1 s2 hS2 hfix2 hpool2
    have hfields := hsigned.type_fields
    have htrace2 := htrace2'.congr_types hfields.1 hfields.2.1 hfields.2.2.1
    have hscope1 : ∀ ann ∈ anns.map (BindingAnn.substTyFvars s1), ∀ v ∈ ann.rigidVars,
        v ∈ K ++ softVars (substSoft s1 F) := by
      intro ann hm v hv
      obtain ⟨original, ho, rfl⟩ := List.mem_map.mp hm
      obtain ⟨k, hk, hv⟩ := BindingAnn.rigidVars_substTyFvars hv
      exact scope_image (Subst.fixes_of_dom_avoids hstrata.dom_avoids) (hannscope original ho k hk) hv
    have hcomplete2 := hsigned.inputSound_of_infer (fullAnns := anns.map (BindingAnn.substTyFvars s1))
      (fullBindings := bindings.map (InferInput.substTyFvars s1)) (fun _ hi => hi.inputSound_source)
      (Subst.onCtx_wf hS1 hctxWF) hLC1
      (fun k hk => Nat.lt_of_lt_of_le (hK k hk) hbase1) (by simp) (by simp) hscope1 RecState.CompleteInput.init
    have hbodyCtx := hLC2.rhsCtx (Subst.onCtx_wf hS2 (Subst.onCtx_wf hS1 hctxWF))
    rw [← Subst.onCtx_append] at hbodyCtx
    have hbodyTyped := hbody.inputSound_source hbodyCtx
    have hS3 := (hbody.lc hbodyCtx).2
    have hvalid2 := recValid_subst hvalid1 s2
    have hdone2 := hframe2.all_mono_done hvalid2
    have hpool3 : ∀ g ∈ state2.pool,
        (∀ p ∈ s3, g ∉ p.2.freeVars) ∧ g ∉ s3.map Prod.fst := by
      intro g hg
      have henv := hframe2.pool_rhsCtx g hg
      have href : (body.substTyFvars (s1 ++ s2)).erase.ForallOuter
          (fun i => ∀ M, (state2.rhsCtx ((s1 ++ s2).onCtx ctx)).env[i]? = some M → g ∉ M.body.freeVars) 0 := by
        apply Expr.ForallOuter.of_recGroupRefs_with_outer (n := 0)
        · intro i _ scheme hs hv
          apply henv
          simpa only [Subst.onCtx_append] using Env.mem_freeVars_iff.mpr ⟨scheme, List.mem_of_getElem? hs, hv⟩
        · intro i _ scheme hs hv
          apply henv
          simpa only [Subst.onCtx_append] using Env.mem_freeVars_iff.mpr ⟨scheme, List.mem_of_getElem? hs, hv⟩
      have hsource : g ∉ (body.substTyFvars (s1 ++ s2)).rigidVars := by
        intro hm
        exact (List.mem_append.mp (hbody.sourceScope g hm)).elim
          (hframe2.pool_rigid g hg) (by simpa only [← substSoft_append] using hframe2.pool_soft g hg)
      have hl := hbody.sourceLocality (hBelow2.2.2.2 g hg) href hsource
      exact ⟨hl.1, hl.2.2⟩
    have hframe3 := hframe2.onSubst hpool3 (fun i target hs hn => False.elim (hn (hdone2 i target hs)))
    have htrace3 := htrace2.onSubst hframe2 s3 hS3 (Subst.fixes_of_dom_avoids hbody.dom_avoids) hpool3
    have hcomplete3 := hcomplete2.onSubst s3 hS3
      (fun k hk v hv => scope_image (Subst.fixes_of_dom_avoids hbody.dom_avoids) hk hv)
    have hLC3 := hLC2.onSubst hS3
    have hvalid3 := recValid_subst hvalid2 s3
    have hdone3 := hframe3.all_mono_done hvalid3
    have hctxeq := hframe3.rhsCtx_eq_recBodyCtx hdone3
    have hfix123 : ∀ k ∈ K, (s1 ++ s2 ++ s3).onTy (.fvar k) = .fvar k :=
      Subst.fixes_of_dom_avoids (fun p hp => (List.mem_append.mp hp).elim
        (fun hp => (List.mem_append.mp hp).elim (hstrata.dom_avoids p) (hsigned.dom_avoids p))
        (hbody.dom_avoids p))
    have hannFinal : ∀ ann ∈ anns.map (BindingAnn.substTyFvars (s1 ++ s2 ++ s3)), ∀ v ∈ ann.rigidVars,
        v ∈ K ++ softVars (substSoft (s1 ++ s2 ++ s3) F) := by
      intro ann hm v hv
      obtain ⟨original, ho, rfl⟩ := List.mem_map.mp hm
      obtain ⟨k, hk, hv⟩ := BindingAnn.rigidVars_substTyFvars hv
      exact scope_image hfix123 (hannscope original ho k hk) hv
    have hrhsFinal : ∀ rhs ∈ bindings.map (InferInput.substTyFvars (s1 ++ s2 ++ s3)), ∀ v ∈ rhs.rigidVars,
        v ∈ K ++ softVars (substSoft (s1 ++ s2 ++ s3) F) := by
      intro rhs hm
      obtain ⟨original, ho, rfl⟩ := List.mem_map.mp hm
      exact (hrhsscope original ho).subst _ hfix123
    simp only [List.map_map, Function.comp_def, ← BindingAnn.substTyFvars_append,
      ← InferInput.substTyFvars_append, ← substSoft_append, ← Subst.onCtx_append] at hframe3 htrace3 hcomplete3 hctxeq
    change (state2.onSubst s3).Frame frontier K (substSoft s3 (substSoft (s1 ++ s2) F))
      ((s1 ++ s2 ++ s3).onCtx ctx) (anns.map (BindingAnn.substTyFvars (s1 ++ s2 ++ s3)))
      groups.flatten at hframe3
    simp only [← substSoft_append] at hframe3
    simp only [List.map_map, Function.comp_def, ← BindingAnn.substTyFvars_append,
      ← InferInput.substTyFvars_append, List.nil_append] at hvalid3 htrace3 hframe3
    obtain ⟨L, hcomplete3⟩ := hcomplete3
    have hresult := RecState.InputTrace.toTyping
      (bindings := bindings.map (InferInput.substTyFvars (s1 ++ s2 ++ s3))) hframe3 hLC3
      (by simpa only [List.map_map, Function.comp_def] using hvalid3) hannFinal hrhsFinal htrace3
      (L := L) (by
        intro i rhs scheme hr hs Xs hXs
        have hm := congrArg (fun ss : List (Option PolyTy) => ss[i]?) hframe3.modes
        change (List.map RecSpec.ann (state2.onSubst s3).specs)[i]? =
          (List.map BindingAnn.recModeAnn (anns.map (BindingAnn.substTyFvars (s1 ++ s2 ++ s3))))[i]? at hm
        rw [List.getElem?_map, hs] at hm
        change some (some scheme) = _ at hm
        cases ha : (anns.map (BindingAnn.substTyFvars (s1 ++ s2 ++ s3)))[i]? with
        | none => rw [List.getElem?_map, ha] at hm; cases hm
        | some ann =>
          have hmode : ann.recModeAnn = some scheme := by rw [List.getElem?_map, ha] at hm; exact Option.some.inj hm.symm
          have haComplete : (anns.map (BindingAnn.substTyFvars (s1 ++ s2 ++ s3)))[i]? = some (.complete scheme) := by
            cases ann <;> simp_all only [BindingAnn.recModeAnn, Option.some.injEq, reduceCtorEq]
          have hi : i < (anns.map (BindingAnn.substTyFvars s1)).length := by
            have := (List.getElem?_eq_some_iff.mp hr).1
            simpa only [List.length_map, hlen] using this
          rw [← hctxeq]
          exact hcomplete3 i _ rhs hi haComplete hr Xs hXs)
      (by
        rw [← hctxeq]
        simpa only [RecState.rhsCtx_onSubst, Subst.onCtx_append, ← substSoft_append,
          ← InferInput.substTyFvars_append] using hbodyTyped)
    simpa only [InferInput.substTyFvars, Subst.onCtx_append, substInputBindings_eq_map_global] using hresult
  | .match_ _ hs hne hb =>
    intro hctx
    have hs1 := (hs.lc hctx).2
    have hbr := hb.lc (Subst.onCtx_wf hs1 hctx) (hs.lc hctx).1 .fvar
    have hscrut := (hs.inputSound_source hctx).onSubst_soft _ hbr.2 hb.dom_avoids
    have hbranches := hb.inputSound_source (Subst.onCtx_wf hs1 hctx) (hs.lc hctx).1 .fvar
    simp only [← substSoft_append, ← InferInput.substTyFvars_append] at hscrut
    simp only [InferInput.substTyFvars, Subst.onCtx_append]
    refine InputTyping.match_ hscrut (fun hn => hne (substInputBranches_eq_nil _ _ |>.mp hn)) ?_
    intro branch hbranch
    rw [substInputBranches_eq_map] at hbranch
    obtain ⟨original, ho, rfl⟩ := List.mem_map.mp hbranch
    have ht := hbranches (original.1, original.2.substTyFvars _) (by
      rw [substInputBranches_eq_map]
      exact List.mem_map.mpr ⟨original, ho, rfl⟩)
    simpa only [← substSoft_append, ← InferInput.substTyFvars_append, Subst.onCtx_append] using ht

termination_by (input.size, 0)
decreasing_by
  all_goals simp only [sizeBindings_map_substTyFvars] at *
  all_goals (simp only [InferInput.size, InferInput.size_openTyVars, InferInput.size_substTyFvars, sizeBranches_substInputBranches]; omega)

theorem _root_.InferBranches.inputSound_source
    (h : InferBranches K F frontier ctx scrutTy resultTy branches next subst completed)
    (hctx : CtxWF ctx) (hscrut : scrutTy.IsLC) (hresult : resultTy.IsLC) :
    ∀ branch ∈ branches, BranchTyping InputTyping (K ++ softVars (substSoft subst F))
      (subst.onCtx ctx) (branch.1, branch.2.substTyFvars subst)
      (subst.onTy scrutTy) (subst.onTy resultTy) := by
  match h with
  | .nil => intro branch hb; cases hb
  | @InferBranches.consWild body rest K F frontier ctx first s1 bodyOut bodyTy resultTy s2 scrutTy next s3 restOut
      _ hb hu hr =>
    obtain ⟨hbTy, hs1⟩ := hb.lc hctx
    have hs2 := hu.unifies.lc hbTy (Subst.onTy_lc hs1 hresult)
    have hctxRest := Subst.onCtx_wf hs2 (Subst.onCtx_wf hs1 hctx)
    have hscrutRest := Subst.onTy_lc hs2 (Subst.onTy_lc hs1 hscrut)
    have hresultRest := Subst.onTy_lc hs2 (Subst.onTy_lc hs1 hresult)
    have hs3 := (hr.lc hctxRest hscrutRest hresultRest).2
    have htail := hr.inputSound_source hctxRest hscrutRest hresultRest
    intro branch hbranch
    rcases List.mem_cons.mp hbranch with rfl | hbranch
    · have head := (hb.inputSound_source hctx).onSubst_soft (s2 ++ s3)
        (fun p hp => (List.mem_append.mp hp).elim (hs2 p) (hs3 p))
        (fun p hp => (List.mem_append.mp hp).elim (hu.dom_avoids p) (hr.dom_avoids p))
      have heq := congrArg s3.onTy hu.unifies.unifies
      rw [Subst.onTy_append] at head
      rw [heq] at head
      simpa only [Subst.onCtx_append, Subst.onTy_append, List.append_assoc,
        ← substSoft_append, ← InferInput.substTyFvars_append] using
        (BranchTyping.wildcard (scrutTy := (s1 ++ s2 ++ s3).onTy scrutTy) head)
    · have ht := htail (branch.1, branch.2.substTyFvars (s1 ++ s2)) (by
        rw [substInputBranches_eq_map]
        exact List.mem_map.mpr ⟨branch, hbranch, rfl⟩)
      simpa only [Subst.onCtx_append, Subst.onTy_append, ← substSoft_append,
        ← InferInput.substTyFvars_append] using ht
  | @InferBranches.cons name count body rest K F ctor scrutTy frontier s0 ctx first s1 bodyOut bodyTy resultTy s2 next s3 restOut
      _ hlookup hcount hu0 hb hu hr =>
    have hs0 := hu0.unifies.lc hscrut
      (.customTy (fun t ht => by obtain ⟨v, _, rfl⟩ := List.mem_map.mp ht; exact .fvar))
    have hbodyWF := branchBindings_wf (ctorr := ctor)
      (ta := ((freshVars frontier ctor.paramCount).map Ty.fvar).map s0.onTy)
      (Subst.onCtx_wf hs0 hctx)
      (fun t ht => by
        obtain ⟨v, hv, rfl⟩ := List.mem_map.mp ht
        obtain ⟨x, _, rfl⟩ := List.mem_map.mp hv
        exact Subst.onTy_lc hs0 .fvar) (by simp)
    obtain ⟨hbTy, hs1⟩ := hb.lc hbodyWF
    have hs2 := hu.unifies.lc hbTy (Subst.onTy_lc hs1 (Subst.onTy_lc hs0 hresult))
    have hctxRest := Subst.onCtx_wf hs2 (Subst.onCtx_wf hs1 (Subst.onCtx_wf hs0 hctx))
    have hscrutRest := Subst.onTy_lc hs2 (Subst.onTy_lc hs1 (Subst.onTy_lc hs0 hscrut))
    have hresultRest := Subst.onTy_lc hs2 (Subst.onTy_lc hs1 (Subst.onTy_lc hs0 hresult))
    have hs3 := (hr.lc hctxRest hscrutRest hresultRest).2
    have htail := hr.inputSound_source hctxRest hscrutRest hresultRest
    intro branch hbranch
    rcases List.mem_cons.mp hbranch with rfl | hbranch
    · let args := (((freshVars frontier ctor.paramCount).map Ty.fvar).map s0.onTy).map s1.onTy
      have hspec : BranchCtorSpec (s1.onCtx (s0.onCtx ctx)).ctors name count
          (s1.onTy (s0.onTy scrutTy)) ctor args (ctor.contents.map (Ty.openWith args)) := by
        refine ⟨hlookup, ?_, ?_, hcount, ?_⟩
        · simpa only [Subst.onTy_customTy, args] using congrArg s1.onTy hu0.unifies.unifies
        · simp only [args, List.length_map, freshVars_length]
        · exact forall₂_self_map (fun t ht => InstantiatesBy.openWith (ctor.bound t ht)
            (by simp only [args, List.length_map, freshVars_length]; omega))
      have head0 : BranchTyping InputTyping (K ++ softVars (substSoft (s0 ++ s1) F))
          (s1.onCtx (s0.onCtx ctx)) (.named name count, body.substTyFvars (s0 ++ s1)) (s1.onTy (s0.onTy scrutTy)) bodyTy := by
        refine .named hspec ?_
        rw [← Subst.onCtx_branchBindings hs1]
        simpa only [← substSoft_append, ← InferInput.substTyFvars_append] using hb.inputSound_source hbodyWF
      have head := head0.onSubst_soft (s2 ++ s3)
        (fun p hp => (List.mem_append.mp hp).elim (hs2 p) (hs3 p))
        (fun p hp => (List.mem_append.mp hp).elim (hu.dom_avoids p) (hr.dom_avoids p))
      have heq := congrArg s3.onTy hu.unifies.unifies
      simp only [Subst.onTy_append] at head
      rw [heq] at head
      simpa only [Subst.onCtx_append, Subst.onTy_append, ← substSoft_append,
        ← InferInput.substTyFvars_append, List.append_assoc] using head
    · have ht := htail (branch.1, branch.2.substTyFvars (s0 ++ s1 ++ s2)) (by
        rw [substInputBranches_eq_map]
        exact List.mem_map.mpr ⟨branch, hbranch, rfl⟩)
      simpa only [Subst.onCtx_append, Subst.onTy_append, ← substSoft_append,
        ← InferInput.substTyFvars_append] using ht
termination_by (sizeBranches branches, 0)
decreasing_by all_goals (simp only [sizeBranches, InferInput.size_substTyFvars, sizeBranches_substInputBranches]; omega)
end

/-- With no provisional slots, actual inference preserves authored annotations. -/
theorem _root_.Infer.inputSound (h : Infer K [] frontier ctx input next subst output ty)
    (hctx : CtxWF ctx) : InputTyping K (subst.onCtx ctx) input ty := by
  have hscope : ∀ v ∈ input.rigidVars, v ∈ K := by
    simpa only [SourceScope, softVars, TyList.freeVars, List.append_nil] using h.sourceScope
  have hinput := input.substTyFvars_eq_self_of_fixes
    (fun v hv => Subst.fixes_of_dom_avoids h.dom_avoids v (hscope v hv))
  simpa only [substSoft, List.map_nil, softVars, TyList.freeVars, List.append_nil, hinput] using
    h.inputSound_source hctx

theorem AnnotationCompletion.onSubst_soft {K : List Nat} {F : List Ty}
    (h : AnnotationCompletion (K ++ softVars F) input output) (S : Subst)
    (hlc : ∀ p ∈ S, p.2.IsLC) (havoid : ∀ p ∈ S, p.1 ∉ K) :
    AnnotationCompletion (K ++ softVars (substSoft S F)) (input.substTyFvars S) (output.substTyFvars S) :=
  h.onSubst_source S hlc (fun _ hk _ hv => scope_image (Subst.fixes_of_dom_avoids havoid) hk hv)

mutual
/-- Exact annotation fidelity follows the same scoped source transformation as
input typing. Completed let binders are compared by cofinite openings. -/
theorem _root_.Infer.completes_source (h : Infer K F frontier ctx input next subst output ty) :
    CtxWF ctx → AnnotationCompletion (K ++ softVars (substSoft subst F)) (input.substTyFvars subst) output := by
  match h with
  | .primLitUnit | .primLitInt | .primLitNat | .primLitChar | .primBinOpIntAdd | .primBinOpIntSub | .primBinOpIntLt _ _ _ _ | .primBinOpCharLt _ _ _ _ | .var _ | .ctor _ =>
      intro _
      exact .complete rfl (by simp [Expr.tyFreeVars])
  | @Infer.lambda K F ann body frontier param initial ctx next subst completed bodyTy _ hs hb =>
      intro hctx
      have hbodyCtx : CtxWF { ctx with env := PolyTy.mkTrivial param :: ctx.env } := by
        intro scheme hscheme
        rcases List.mem_cons.mp hscheme with rfl | hscheme
        · exact hs.lc
        · exact hctx scheme hscheme
      have hsubst := (hb.lc hbodyCtx).2
      simp only [InferInput.substTyFvars]
      have hout : ann.map (fun _ => subst.onTy param) =
          (ann.map (TyTemplate.substTyFvars subst)).map (fun _ => subst.onTy param) := by
        cases ann <;> rfl
      simp only [lambdaOutput, hout]
      refine AnnotationCompletion.lambda ?_ ?_ ?_
      · intro template heq
        cases ann with
        | none => cases heq
        | some original =>
          cases heq
          exact (hs.fits original rfl).substTyFvars subst
      · intro template heq v hv
        cases ann with
        | none => cases heq
        | some original =>
          cases heq
          obtain ⟨old, hold, hv⟩ := TyTemplate.rigidVars_substTyFvars hv
          exact scope_image (Subst.fixes_of_dom_avoids hb.dom_avoids) (hs.rigid original rfl old hold) hv
      · simpa only [Subst.onCtx, Subst.onEnv, List.map_cons, Subst.onPolyTy,
          PolyTy.mkTrivial] using hb.completes_source hbodyCtx
  | @Infer.app K F f arg frontier ctx first s1 fOut fTy second s2 argOut argTy s3 _ hf ha hu =>
      intro hctx
      have hs1 := (hf.lc hctx).2
      have haCtx := Subst.onCtx_wf hs1 hctx
      have hs2 := (ha.lc haCtx).2
      have hs3 := hu.unifies.lc (Subst.onTy_lc hs2 (hf.lc hctx).1)
        (.arrow (ha.lc haCtx).1 .fvar)
      have hfComp := (hf.completes_source hctx).onSubst_soft (s2 ++ s3)
        (fun pair hp => (List.mem_append.mp hp).elim (hs2 pair) (hs3 pair))
        (fun pair hp => (List.mem_append.mp hp).elim (ha.dom_avoids pair) (hu.dom_avoids pair))
      have haComp := (ha.completes_source haCtx).onSubst_soft s3 hs3 hu.dom_avoids
      simp only [← substSoft_append, ← InferInput.substTyFvars_append, List.append_assoc] at hfComp haComp
      simpa only [List.append_assoc] using AnnotationCompletion.app hfComp haComp
  | @Infer.letIn K F ann rhs body frontier ctx first s1 rhsOut rhsTy checked sCheck next s2 bodyOut bodyTy
      hraw hr hc hb =>
      intro hctx
      have hs1 := (hr.lc hctx).2
      have hrTy := (hr.lc hctx).1
      have hsCheck := hc.lc hrTy
      have hprefixAvoid : ∀ p ∈ s1 ++ sCheck, p.1 ∉ K := fun p hp =>
        (List.mem_append.mp hp).elim (hr.dom_avoids p) (hc.dom_avoids p)
      have hpost := hraw.subst (s1 ++ sCheck) (Subst.fixes_of_dom_avoids hprefixAvoid)
      have hann : ∀ template, (ann.substTyFvars (s1 ++ sCheck)) = .template template →
          ∀ v ∈ template.rigidVars, v ∈ K ++ softVars (substSoft (s1 ++ sCheck) F) := by
        intro template heq v hv
        exact hpost v (List.mem_append_left _ (List.mem_append_left _ (by
          simpa only [BindingAnn.rigidVars, heq] using hv)))
      have hfit : (ann.substTyFvars (s1 ++ sCheck)).FitsMono (sCheck.onTy rhsTy) := by
        simpa only [BindingAnn.substTyFvars_append] using hc.fits
      have checkedCtxWF := Subst.onCtx_wf hsCheck (Subst.onCtx_wf hs1 hctx)
      have checkedTyLC := Subst.onTy_lc hsCheck hrTy
      have bodyCtxWF : CtxWF
          { sCheck.onCtx (s1.onCtx ctx) with
            env := genScheme (K ++ softVars (substSoft (s1 ++ sCheck) F))
              (sCheck.onCtx (s1.onCtx ctx)).env (sCheck.onTy rhsTy) ::
              (sCheck.onCtx (s1.onCtx ctx)).env } := by
        intro scheme hscheme
        rcases List.mem_cons.mp hscheme with rfl | hscheme
        · exact genScheme_wf checkedTyLC
        · exact checkedCtxWF scheme hscheme
      have hs2 := (hb.lc bodyCtxWF).2
      have rhsTyped := (hr.inputSound_source hctx).onSubst_soft sCheck hsCheck hc.dom_avoids
      simp only [← substSoft_append, ← InferInput.substTyFvars_append] at rhsTyped
      have rhsGeneral := rhsTyped.generalise
        (names := genVars (K ++ softVars (substSoft (s1 ++ sCheck) F))
          (sCheck.onCtx (s1.onCtx ctx)).env (sCheck.onTy rhsTy))
        hfit hann genVars_nodup (fun _ hn => genVars_not_mem hn)
        (fun _ hn => genVars_not_mem_rigid hn)
      obtain ⟨avoid, hfits, hgeneral⟩ := InputTyping.binding_onSubst_source
        (scheme := genScheme (K ++ softVars (substSoft (s1 ++ sCheck) F))
          (sCheck.onCtx (s1.onCtx ctx)).env (sCheck.onTy rhsTy))
        (fun fresh hf => (rhsGeneral fresh hf).1)
        (fun fresh hf => (rhsGeneral fresh hf).2) s2 hs2
        (fun _ hk _ hv => scope_image (Subst.fixes_of_dom_avoids hb.dom_avoids) hk hv)
      have hannFinal : ∀ template, (ann.substTyFvars (s1 ++ sCheck ++ s2)) = .template template →
          ∀ v ∈ template.rigidVars, v ∈ K ++ softVars (substSoft (s1 ++ sCheck ++ s2) F) := by
        have hp := hraw.subst (s1 ++ sCheck ++ s2) (Subst.fixes_of_dom_avoids
          (fun p hp => (List.mem_append.mp hp).elim (hprefixAvoid p) (hb.dom_avoids p)))
        intro template heq v hv
        exact hp v (List.mem_append_left _ (List.mem_append_left _ (by
          simpa only [BindingAnn.rigidVars, heq] using hv)))
      have rhsComp := (hr.completes_source hctx).onSubst_soft sCheck hsCheck hc.dom_avoids
      simp only [← substSoft_append, ← InferInput.substTyFvars_append] at rhsComp
      have rhsBound := (TypeOfHM.onSubst sCheck hsCheck (hr.sourceSound hctx)).tyBvarBounded
      obtain ⟨compAvoid, hcomplete⟩ := rhsComp.generalise_closed_after_source
        (names := genVars (K ++ softVars (substSoft (s1 ++ sCheck) F))
          (sCheck.onCtx (s1.onCtx ctx)).env (sCheck.onTy rhsTy))
        genVars_nodup (fun _ hn => genVars_not_mem_rigid hn) rhsBound s2 hs2
        (fun _ hk _ hv => scope_image (Subst.fixes_of_dom_avoids hb.dom_avoids) hk hv)
      have bodyComp := hb.completes_source bodyCtxWF
      simp only [← substSoft_append, ← InferInput.substTyFvars_append, ← BindingAnn.substTyFvars_append,
        List.append_assoc] at hfits hcomplete bodyComp hannFinal ⊢
      simp only [letOutput]
      refine AnnotationCompletion.letIn (L := avoid ++ compAvoid) hannFinal ?_ ?_ bodyComp
      · intro fresh hf
        exact hfits fresh ⟨hf.length, hf.nodup, fun v hv hm => hf.avoid v hv (List.mem_append_left _ hm)⟩
      · intro fresh hf
        exact hcomplete fresh ⟨hf.length, hf.nodup, fun v hv hm => hf.avoid v hv (List.mem_append_right _ hm)⟩

  | @Infer.letSignature K F ann rhs body written frontier ctx first s1 rhsOut rhsTy checked sCheck next s2 bodyOut bodyTy
      hscope hprefix havoid hraw hr hc hescape hb =>
    intro hctx
    have hlen : written.length = ann.paramCount := by simpa only [freshVars_length] using congrArg List.length hprefix
    have hnd : written.Nodup := hprefix ▸ freshVars_nodup
    obtain ⟨hrTy, hs1⟩ := hr.lc hctx
    have hsCheck := hc.lc (by simpa using hlen) hrTy
    have checkedCtxWF := Subst.onCtx_wf hsCheck (Subst.onCtx_wf hs1 hctx)
    have checkedTyLC := Subst.onTy_lc hsCheck hrTy
    have hscheme : (signatureScheme (ann.substTyFvars (s1 ++ sCheck))
        (K ++ softVars (substSoft (s1 ++ sCheck) F)) written
        (sCheck.onCtx (s1.onCtx ctx)) (sCheck.onTy rhsTy)).WF := by
      simpa only [BindingAnn.substTyFvars_append] using
        hc.scheme_wf (Q := K ++ softVars (substSoft (s1 ++ sCheck) F))
          (ctx := sCheck.onCtx (s1.onCtx ctx)) (by simpa using hlen) hrTy
    have hscopePost : ∀ v ∈ (ann.substTyFvars (s1 ++ sCheck)).rigidVars,
        v ∈ K ++ softVars (substSoft (s1 ++ sCheck) F) := by
      intro v hv
      obtain ⟨original, ho, hv⟩ := BindingAnn.rigidVars_substTyFvars hv
      exact scope_image (Subst.fixes_of_dom_avoids (fun p hp hk =>
        (List.mem_append.mp hp).elim
          (fun hp => hr.dom_avoids p hp (List.mem_append_left _ hk))
          (fun hp => hc.dom_avoids p hp (List.mem_append_left _ hk))))
        (hscope original (List.mem_append_left _ (List.mem_append_left _ ho))) hv
    have havoidPost : ∀ name ∈ written, name ∉ K ++ softVars (substSoft (s1 ++ sCheck) F) := by
      intro name hn hm
      rcases List.mem_append.mp hm with hK | hF
      · exact havoid name hn (List.mem_append_left _ hK)
      · exact hescape name hn (List.mem_append_right _ hF)
    have hnamesFresh : ∀ name ∈ written, name ∉ (sCheck.onCtx (s1.onCtx ctx)).env.freeVars :=
      fun name hn hm => hescape name hn (List.mem_append_left _ hm)
    have bodyCtxWF : CtxWF
        { sCheck.onCtx (s1.onCtx ctx) with
          env := signatureScheme (ann.substTyFvars (s1 ++ sCheck)) (K ++ softVars (substSoft (s1 ++ sCheck) F)) written (sCheck.onCtx (s1.onCtx ctx)) (sCheck.onTy rhsTy) ::
            (sCheck.onCtx (s1.onCtx ctx)).env } := by
      intro scheme hschemeMem
      rcases List.mem_cons.mp hschemeMem with rfl | hschemeMem
      · exact hscheme
      · exact checkedCtxWF scheme hschemeMem
    have hs2 := (hb.lc bodyCtxWF).2
    have hprefixLC : ∀ p ∈ s1 ++ sCheck, p.2.IsLC := fun p hp =>
      (List.mem_append.mp hp).elim (hs1 p) (hsCheck p)
    have hprefixAvoid : ∀ p ∈ s1 ++ sCheck, p.1 ∉ K ++ written := fun p hp =>
      (List.mem_append.mp hp).elim (hr.dom_avoids p) (hc.dom_avoids p)
    have rhsTyped0 := (hr.inputSound_source hctx).onSubst_soft sCheck hsCheck hc.dom_avoids
    simp only [← substSoft_append, ← InferInput.substTyFvars_append] at rhsTyped0
    rw [InferInput.substTyFvars_openTyVars rhs hprefixLC
      (fun p hp hw => hprefixAvoid p hp (List.mem_append_right _ hw))] at rhsTyped0
    have rhsTyped : InputTyping ((K ++ softVars (substSoft (s1 ++ sCheck) F)) ++ written)
        (sCheck.onCtx (s1.onCtx ctx)) ((rhs.substTyFvars (s1 ++ sCheck)).openTyVars written)
        (sCheck.onTy rhsTy) := rhsTyped0.scope_mono (by
      intro k hk
      simp only [List.mem_append] at hk ⊢
      tauto)
    have hpost := hscope.subst (s1 ++ sCheck) (Subst.fixes_of_dom_avoids
      (fun p hp hk => hprefixAvoid p hp (List.mem_append_left _ hk)))
    have hrawPost : ∀ v ∈ (rhs.substTyFvars (s1 ++ sCheck)).rigidVars,
        v ∈ K ++ softVars (substSoft (s1 ++ sCheck) F) := fun v hv =>
      hpost v (List.mem_append_left _ (List.mem_append_right _ hv))
    have hcomp := hc.completion (Q := K ++ softVars (substSoft (s1 ++ sCheck) F))
      (ctx := sCheck.onCtx (s1.onCtx ctx)) (by simpa using hlen) hrTy
    simp only [← BindingAnn.substTyFvars_append] at hcomp
    have hnamesND := hc.names_nodup (Q := K ++ softVars (substSoft (s1 ++ sCheck) F))
      (ctx := sCheck.onCtx (s1.onCtx ctx)) hnd
    have hnamesAvoid := hc.names_avoid (ctx := sCheck.onCtx (s1.onCtx ctx)) havoidPost
    have hnamesFresh := hc.names_fresh (Q := K ++ softVars (substSoft (s1 ++ sCheck) F)) hnamesFresh
    simp only [← BindingAnn.substTyFvars_append] at hnamesND hnamesAvoid hnamesFresh
    obtain ⟨fitAvoid, hfits⟩ := hcomp.cofinite_fits hnamesND hnamesAvoid hscopePost checkedTyLC
    obtain ⟨typeAvoid, htypes⟩ := hcomp.cofinite_typing rhsTyped hscheme
      hnamesND hnamesFresh hnamesAvoid hscopePost hrawPost
    have hfitBoth := fun fresh (hf : FreshNames (fitAvoid ++ typeAvoid)
        (signatureScheme (ann.substTyFvars (s1 ++ sCheck))
          (K ++ softVars (substSoft (s1 ++ sCheck) F)) written
          (sCheck.onCtx (s1.onCtx ctx)) (sCheck.onTy rhsTy)).paramCount fresh) =>
      hfits fresh ⟨hf.length, hf.nodup, fun v hv ha => hf.avoid v hv (List.mem_append_left _ ha)⟩
    have htypeBoth := fun fresh (hf : FreshNames (fitAvoid ++ typeAvoid)
        (signatureScheme (ann.substTyFvars (s1 ++ sCheck))
          (K ++ softVars (substSoft (s1 ++ sCheck) F)) written
          (sCheck.onCtx (s1.onCtx ctx)) (sCheck.onTy rhsTy)).paramCount fresh) =>
      htypes fresh ⟨hf.length, hf.nodup, fun v hv ha => hf.avoid v hv (List.mem_append_right _ ha)⟩
    obtain ⟨avoid, hfitsFinal, htypesFinal⟩ := InputTyping.signatureBinding_onSubst_source
      hfitBoth htypeBoth s2 hs2
      (fun _ hk _ hv => scope_image (Subst.fixes_of_dom_avoids hb.dom_avoids) hk hv)
    have rhsComp0 := (hr.completes_source hctx).onSubst_soft sCheck hsCheck hc.dom_avoids
    simp only [← substSoft_append, ← InferInput.substTyFvars_append] at rhsComp0
    rw [InferInput.substTyFvars_openTyVars rhs hprefixLC
      (fun p hp hw => hprefixAvoid p hp (List.mem_append_right _ hw))] at rhsComp0
    have rhsComp : AnnotationCompletion ((K ++ softVars (substSoft (s1 ++ sCheck) F)) ++ written)
        ((rhs.substTyFvars (s1 ++ sCheck)).openTyVars written) (rhsOut.substTyFvars sCheck) :=
      rhsComp0.scope_mono (by intro k hk; simp only [List.mem_append] at hk ⊢; tauto)
    have rhsBound := (TypeOfHM.onSubst sCheck hsCheck (hr.sourceSound hctx)).tyBvarBounded
    obtain ⟨completeAvoid, hcomplete⟩ := hcomp.cofinite_completes rhsComp hnamesND hnamesAvoid hrawPost rhsBound
    obtain ⟨finalCompAvoid, hcompleteFinal⟩ := AnnotationCompletion.signatureBinding_onSubst_source hcomplete s2 hs2
      (fun _ hk _ hv => scope_image (Subst.fixes_of_dom_avoids hb.dom_avoids) hk hv)
    have bodyComp := hb.completes_source bodyCtxWF
    have hpostFinal := hscope.subst (s1 ++ sCheck ++ s2) (Subst.fixes_of_dom_avoids
      (fun p hp hk => (List.mem_append.mp hp).elim
        (fun hp => hprefixAvoid p hp (List.mem_append_left _ hk))
        (fun hp => hb.dom_avoids p hp hk)))
    have hannFinal : ∀ v ∈ (ann.substTyFvars (s1 ++ sCheck ++ s2)).rigidVars,
        v ∈ K ++ softVars (substSoft (s1 ++ sCheck ++ s2) F) := fun v hv =>
      hpostFinal v (List.mem_append_left _ (List.mem_append_left _ hv))
    have hrhsFinal : ∀ v ∈ (rhs.substTyFvars (s1 ++ sCheck ++ s2)).rigidVars,
        v ∈ K ++ softVars (substSoft (s1 ++ sCheck ++ s2) F) := fun v hv =>
      hpostFinal v (List.mem_append_left _ (List.mem_append_right _ hv))
    simp only [← substSoft_append, ← InferInput.substTyFvars_append, ← BindingAnn.substTyFvars_append,
      List.append_assoc] at hfitsFinal hcompleteFinal bodyComp hannFinal hrhsFinal ⊢
    simp only [letOutput]
    refine AnnotationCompletion.letSignature (L := avoid ++ finalCompAvoid) hannFinal hrhsFinal ?_ ?_ bodyComp
    · intro fresh hf
      exact hfitsFinal fresh ⟨hf.length, hf.nodup, fun v hv hm => hf.avoid v hv (List.mem_append_left _ hm)⟩
    · intro fresh hf
      simpa only [List.append_assoc, BindingAnn.paramCount_substTyFvars] using
        hcompleteFinal fresh ⟨hf.length, hf.nodup, fun v hv hm => hf.avoid v hv (List.mem_append_right _ hm)⟩

  | .letRec hscope hann hvalid hstrata hsigned hexports houtputs hbody =>
    intro hctxWF
    expose_names
    have hvalid := hvalid.1
    obtain ⟨hraw, hctx, hK, hFvars⟩ := hscope
    have hF : ∀ t ∈ F, Ty.BelowFvars frontier t := by
      intro t ht
      apply Ty.BelowFvars.of_freeVars_lt
      intro v hv
      exact hFvars v (TyList.mem_freeVars_iff.mpr ⟨t, ht, hv⟩)
    have hannscope : ∀ ann ∈ anns, ∀ v ∈ ann.rigidVars, v ∈ K ++ softVars F := by
      intro ann ha v hv
      exact hraw v (List.mem_append_left _ (List.mem_append_left _ (List.mem_flatMap.mpr ⟨ann, ha, hv⟩)))
    have hrhsscope : ∀ rhs ∈ bindings, SourceScope K F rhs := by
      intro rhs hr v hv
      exact hraw v (List.mem_append_left _ (List.mem_append_right _ (rec_rhs_rigid_mem hr hv)))
    have hannbelow : ∀ ann ∈ anns, ∀ v ∈ ann.rigidVars, v < frontier := by
      intro ann ha v hv
      exact (List.mem_append.mp (hannscope ann ha v hv)).elim (hK v) (hFvars v)
    have hlen : anns.length = bindings.length := by simpa only [List.length_map] using hvalid.length
    have hinitFrame := RecState.Frame.init hctx
      (fun v hv => by obtain ⟨ann, ha, hv⟩ := List.mem_flatMap.mp hv; exact hannbelow ann ha v hv) hK hFvars
    have hinitLC := RecState.LC.init (base := frontier) hann
    have hinitBelow : (RecState.init frontier anns).Below (frontier + bindings.length) := by
      simpa only [hlen] using RecState.Below.init hannbelow
    have hctxSeed : CtxBelow (frontier + bindings.length) ctx :=
      fun M hm => (hctx M hm).mono (by omega)
    have hFSeed : ∀ t ∈ F, Ty.BelowFvars (frontier + bindings.length) t :=
      fun t ht => (hF t ht).mono (by omega)
    have hvalid0 : RecGroups.ValidResidualGroups (anns.map BindingAnn.recModeAnn) (bindings.map InferInput.erase) ([] ++ groups) := hvalid
    obtain ⟨hframe1, _⟩ := hstrata.frame_of_infer
      (fun _ hi => hi.sourceLocality) hvalid0 hinitFrame hinitLC hctxWF hinitBelow hctxSeed hFSeed
      (by omega) hannscope hrhsscope
    have hfid1 := hstrata.fidelity_of_infer
      (fun _ hi => hi.sourceLocality) hvalid0 hinitFrame hinitLC hctxWF hinitBelow hctxSeed hFSeed
      (by omega) hannscope hrhsscope (fun _ hi => hi.completes_source) (fun _ hi => hi.sourceSound)
      RecState.Fidelity.init
    obtain ⟨hS1, hLC1⟩ := hstrata.lc_of_infer (fun _ hi => hi.lc) hctxWF hinitLC
    obtain ⟨hB1, hBelow1⟩ := hstrata.belowFvars_of_infer (fun _ hi => hi.belowFvars)
      hctxSeed (fun k hk => Nat.lt_of_lt_of_le (hK k hk) (by omega)) hFSeed hinitBelow
      (fun ann ha v hv => Nat.lt_of_lt_of_le (hannbelow ann ha v hv) (by omega))
    have hvalid1 := recValid_subst hvalid s1
    have hdone1 := hframe1.all_mono_done hvalid1
    obtain ⟨hframe2, _⟩ := hsigned.frame_of_infer
      (fun _ hi => hi.sourceLocality) hframe1 (by simp) hdone1 hBelow1.2.2.2
    have hfid2 := hsigned.completes_of_infer
      (fun _ hi => hi.completes_source) (fun _ hi => hi.sourceSound)
      (Subst.onCtx_wf hS1 hctxWF) hLC1
      (fun k hk => by have := hK k hk; have := hstrata.frontier_le; omega)
      (by simp) (by simp) hframe1.outputs_length
      (fun j scheme ha => by simpa only [Nat.zero_add] using hframe1.complete_export ha) hfid1
    simp only [← substSoft_append, List.map_map, Function.comp_def,
      ← BindingAnn.substTyFvars_append, ← InferInput.substTyFvars_append] at hfid2
    obtain ⟨hS2, hLC2⟩ := hsigned.lc_of_infer (fun _ hi => hi.lc) (Subst.onCtx_wf hS1 hctxWF) hLC1
    have hbodyCtx := hLC2.rhsCtx (Subst.onCtx_wf hS2 (Subst.onCtx_wf hS1 hctxWF))
    rw [← Subst.onCtx_append] at hbodyCtx
    obtain ⟨_, hS3⟩ := hbody.lc hbodyCtx
    have hbodyComplete := hbody.completes_source hbodyCtx
    simp only [← substSoft_append, ← InferInput.substTyFvars_append] at hbodyComplete
    have hfidFinal := hfid2.onSubst_source hS3
      (fun k hk v hv => scope_image (Subst.fixes_of_dom_avoids hbody.dom_avoids) hk hv)
    simp only [← substSoft_append, List.map_map, Function.comp_def,
      ← BindingAnn.substTyFvars_append, ← InferInput.substTyFvars_append] at hfidFinal
    have hfinalExports : (state2.onSubst s3).exports = (schemes.map s3.onPolyTy).map some := by
      simp only [RecState.onSubst, hexports, List.map_map]
      rfl
    have hfinalOutputs : (state2.onSubst s3).outputs = (outputs.map (Expr.substTyFvars s3)).map some := by
      simp only [RecState.onSubst, houtputs, List.map_map]
      rfl
    have hschemeLen : schemes.length = anns.length := by
      have hh := congrArg List.length hexports
      simp only [List.length_map] at hh
      exact hh.symm.trans (by simpa only [List.length_map] using hframe2.exports_length)
    have houtputLen : outputs.length = schemes.length := by
      have hh := congrArg List.length houtputs
      simp only [List.length_map] at hh
      exact hh.symm.trans (by simpa only [List.length_map, hschemeLen] using hframe2.outputs_length)
    have hfixAll : ∀ k ∈ K, (s1 ++ s2 ++ s3).onTy (.fvar k) = .fvar k :=
      Subst.fixes_of_dom_avoids (fun p hp => (List.mem_append.mp hp).elim
        (fun hp => (List.mem_append.mp hp).elim (hstrata.dom_avoids p) (hsigned.dom_avoids p)) (hbody.dom_avoids p))
    have hAnnFinal : ∀ ann ∈ anns.map (BindingAnn.substTyFvars (s1 ++ s2 ++ s3)),
        ∀ v ∈ ann.rigidVars, v ∈ K ++ softVars (substSoft (s1 ++ s2 ++ s3) F) := by
      intro ann hm v hv
      obtain ⟨original, ho, rfl⟩ := List.mem_map.mp hm
      obtain ⟨k, hk, himage⟩ := BindingAnn.rigidVars_substTyFvars hv
      exact scope_image hfixAll (hannscope original ho k hk) himage
    have hRhsFinal : ∀ rhs ∈ bindings.map (InferInput.substTyFvars (s1 ++ s2 ++ s3)),
        ∀ v ∈ rhs.rigidVars, v ∈ K ++ softVars (substSoft (s1 ++ s2 ++ s3) F) := by
      intro rhs hm
      obtain ⟨original, ho, rfl⟩ := List.mem_map.mp hm
      exact (hrhsscope original ho).subst (s1 ++ s2 ++ s3) hfixAll
    have hresult := hfidFinal.toCompletes
      (by simpa only [List.length_map] using hschemeLen.symm)
      (by simpa only [List.length_map] using hlen.symm.trans hschemeLen.symm)
      (by simpa only [List.length_map] using houtputLen)
      hfinalExports hfinalOutputs hAnnFinal hRhsFinal hbodyComplete
    simpa only [InferInput.substTyFvars, substInputBindings_eq_map_global] using hresult

  | .match_ _ hs _ hb =>
    intro hctx
    have hs1 := (hs.lc hctx).2
    have hbr := hb.lc (Subst.onCtx_wf hs1 hctx) (hs.lc hctx).1 .fvar
    have hscrut := (hs.completes_source hctx).onSubst_soft _ hbr.2 hb.dom_avoids
    have hbranches := hb.completes_source (Subst.onCtx_wf hs1 hctx) (hs.lc hctx).1 .fvar
    simp only [← substSoft_append, ← InferInput.substTyFvars_append] at hscrut
    simp only [← substSoft_append, ← substInputBranches_append] at hbranches
    simpa only [InferInput.substTyFvars, ← substSoft_append, substInputBranches_append] using
      AnnotationCompletion.match_ hscrut hbranches
termination_by (input.size, 0)
decreasing_by
  all_goals simp only [sizeBindings_map_substTyFvars] at *
  all_goals (simp only [InferInput.size, InferInput.size_openTyVars, InferInput.size_substTyFvars, sizeBranches_substInputBranches]; omega)

theorem _root_.InferBranches.completes_source
    (h : InferBranches K F frontier ctx scrutTy resultTy branches next subst completed)
    (hctx : CtxWF ctx) (hscrut : scrutTy.IsLC) (hresult : resultTy.IsLC) :
    CompletedBranches AnnotationCompletion (K ++ softVars (substSoft subst F))
      (substInputBranches subst branches) completed := by
  match h with
  | .nil => exact .nil
  | @InferBranches.consWild body rest K F frontier ctx first s1 bodyOut bodyTy resultTy s2 scrutTy next s3 restOut
      _ hb hu hr =>
    obtain ⟨hbTy, hs1⟩ := hb.lc hctx
    have hs2 := hu.unifies.lc hbTy (Subst.onTy_lc hs1 hresult)
    have hctxRest := Subst.onCtx_wf hs2 (Subst.onCtx_wf hs1 hctx)
    have hscrutRest := Subst.onTy_lc hs2 (Subst.onTy_lc hs1 hscrut)
    have hresultRest := Subst.onTy_lc hs2 (Subst.onTy_lc hs1 hresult)
    have hs3 := (hr.lc hctxRest hscrutRest hresultRest).2
    have htail := hr.completes_source hctxRest hscrutRest hresultRest
    have head := (hb.completes_source hctx).onSubst_soft (s2 ++ s3)
      (fun p hp => (List.mem_append.mp hp).elim (hs2 p) (hs3 p))
      (fun p hp => (List.mem_append.mp hp).elim (hu.dom_avoids p) (hr.dom_avoids p))
    simp only [← substSoft_append, ← InferInput.substTyFvars_append, ← substInputBranches_append,
      List.append_assoc] at head htail ⊢
    exact CompletedBranches.cons head htail
  | @InferBranches.cons name count body rest K F ctor scrutTy frontier s0 ctx first s1 bodyOut bodyTy resultTy s2 next s3 restOut
      _ hlookup hcount hu0 hb hu hr =>
    have hs0 := hu0.unifies.lc hscrut
      (.customTy (fun t ht => by obtain ⟨v, _, rfl⟩ := List.mem_map.mp ht; exact .fvar))
    have hbodyWF := branchBindings_wf (ctorr := ctor)
      (ta := ((freshVars frontier ctor.paramCount).map Ty.fvar).map s0.onTy)
      (Subst.onCtx_wf hs0 hctx)
      (fun t ht => by
        obtain ⟨v, hv, rfl⟩ := List.mem_map.mp ht
        obtain ⟨x, _, rfl⟩ := List.mem_map.mp hv
        exact Subst.onTy_lc hs0 .fvar) (by simp)
    obtain ⟨hbTy, hs1⟩ := hb.lc hbodyWF
    have hs2 := hu.unifies.lc hbTy (Subst.onTy_lc hs1 (Subst.onTy_lc hs0 hresult))
    have hctxRest := Subst.onCtx_wf hs2 (Subst.onCtx_wf hs1 (Subst.onCtx_wf hs0 hctx))
    have hscrutRest := Subst.onTy_lc hs2 (Subst.onTy_lc hs1 (Subst.onTy_lc hs0 hscrut))
    have hresultRest := Subst.onTy_lc hs2 (Subst.onTy_lc hs1 (Subst.onTy_lc hs0 hresult))
    have hs3 := (hr.lc hctxRest hscrutRest hresultRest).2
    have htail := hr.completes_source hctxRest hscrutRest hresultRest
    have head := (hb.completes_source hbodyWF).onSubst_soft (s2 ++ s3)
      (fun p hp => (List.mem_append.mp hp).elim (hs2 p) (hs3 p))
      (fun p hp => (List.mem_append.mp hp).elim (hu.dom_avoids p) (hr.dom_avoids p))
    simp only [← substSoft_append, ← InferInput.substTyFvars_append, ← substInputBranches_append,
      List.append_assoc] at head htail ⊢
    exact CompletedBranches.cons head htail
termination_by (sizeBranches branches, 0)
decreasing_by all_goals (simp only [sizeBranches, InferInput.size_substTyFvars, sizeBranches_substInputBranches]; omega)
end

/-- The public empty-soft-context judgment preserves all authored annotations. -/
theorem _root_.Infer.completes (h : Infer K [] frontier ctx input next subst output ty)
    (hctx : CtxWF ctx) : AnnotationCompletion K input output := by
  have hscope : ∀ v ∈ input.rigidVars, v ∈ K := by
    simpa only [SourceScope, softVars, TyList.freeVars, List.append_nil] using h.sourceScope
  have hinput := input.substTyFvars_eq_self_of_fixes
    (fun v hv => Subst.fixes_of_dom_avoids h.dom_avoids v (hscope v hv))
  simpa only [substSoft, List.map_nil, softVars, TyList.freeVars, List.append_nil, hinput] using
    h.completes_source hctx

/-- The exact completed Core returned to the runtime is source typed. -/
theorem _root_.inferWithTypes_source_sound {ctors : CtorEnv} {input : InferInput} {result : InferenceResult}
    (h : inferWithTypes ctors input = some result) :
    TypeOfHM ⟨[], ctors⟩ result.completedExpr result.ty := by
  simpa only [Subst.onCtx_empty] using (inferWithTypes_infer h).sourceSound CtxWF.empty

theorem _root_.inferWithTypes_erase {ctors : CtorEnv} {input : InferInput} {result : InferenceResult}
    (h : inferWithTypes ctors input = some result) : result.completedExpr.erase = input.erase :=
  (inferWithTypes_infer h).erase

theorem _root_.inferWithTypes_input_sound {ctors : CtorEnv} {input : InferInput} {result : InferenceResult}
    (h : inferWithTypes ctors input = some result) : InputTyping input.rigidVars ⟨[], ctors⟩ input result.ty := by
  simpa only [Subst.onCtx_empty] using (inferWithTypes_infer h).inputSound CtxWF.empty

end
