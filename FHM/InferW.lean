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

/-- All inputs to one canonical inference call. `protectedVars` is the current
frozen set `K`; `soft` contains the live provisional written-forall images
traditionally named `F`. -/
structure InferRequest where
  protectedVars : List Nat
  soft : List Ty
  frontier : Nat
  ctx : Ctx
  input : InferInput

namespace InferRequest

/-- A request for ordinary core inference, with no live provisional slots. -/
def core (protectedVars : List Nat) (frontier : Nat) (ctx : Ctx)
    (input : InferInput) : InferRequest :=
  { protectedVars, soft := [], frontier, ctx, input }

/-- Freshness bounds required by the inference worker independently of source
scope and semantic well-formedness. -/
structure Bounds (request : InferRequest) : Prop where
  ctxBelow : CtxBelow request.frontier request.ctx
  protectedBelow : ∀ v ∈ request.protectedVars, v < request.frontier
  softBelow : ∀ ty ∈ request.soft, Ty.BelowFvars request.frontier ty

/-- A bounded request whose term environment is semantically well formed. -/
structure WF (request : InferRequest) : Prop extends Bounds request where
  ctxWF : CtxWF request.ctx

/-- The authored rigid leaves of a request are accounted for by its protected
variables or live provisional images. -/
def Scoped (request : InferRequest) : Prop :=
  SourceScope request.protectedVars request.soft request.input

/-- A well-formed request whose source is valid in its current scope. -/
structure Admissible (request : InferRequest) : Prop extends WF request where
  sourceScope : request.Scoped

end InferRequest

/-- The semantic output shared by the certificate and public inference APIs. -/
structure InferResult where
  frontier : Nat
  subst : Subst
  completedExpr : Expr
  ty : Ty

/-- The parameter type and advanced frontier produced while seeding a lambda
parameter from its optional annotation. -/
structure SeedResult where
  param : Ty
  frontier : Nat

/-- The advanced frontier and substitution produced by either form of binding
annotation check. Shared by ordinary and explicitly signed lets. -/
structure CheckResult where
  frontier : Nat
  subst : Subst

/-- The semantic output of inferring all branches of a match. Kept separate
from `InferResult` because a branch traversal completes a list, not one term,
and its result type is fixed by the enclosing match. -/
structure InferBranchesResult where
  frontier : Nat
  subst : Subst
  completedBranches : List (MatchPattern × Expr)

/-- The semantic output shared by the inferred-SCC and signed-contract
recursive phases. Their relations remain distinct despite sharing this shape. -/
structure RecRunResult where
  frontier : Nat
  subst : Subst
  state : RecState

private theorem ann_rigid_mem {bindings : List InputRecBinding}
    {binding : InputRecBinding} (hb : binding ∈ bindings) {v : Nat}
    (hv : v ∈ binding.ann.rigidVars) : v ∈ rigidBindingVars bindings := by
  induction bindings with
  | nil => cases hb
  | cons head rest ih =>
      rcases List.mem_cons.mp hb with rfl | hb
      · exact List.mem_append_left _ (List.mem_append_left _ hv)
      · exact List.mem_append_right _ (ih hb)

private theorem rhs_rigid_mem {bindings : List InputRecBinding}
    {binding : InputRecBinding} (hb : binding ∈ bindings) {v : Nat}
    (hv : v ∈ binding.rhs.rigidVars) : v ∈ rigidBindingVars bindings := by
  induction bindings with
  | nil => cases hb
  | cons head rest ih =>
      rcases List.mem_cons.mp hb with rfl | hb
      · exact List.mem_append_left _ (List.mem_append_right _ hv)
      · exact List.mem_append_right _ (ih hb)

private theorem erase_rhs_mem {bindings : List InputRecBinding}
    {binding : InputRecBinding} (hb : binding ∈ bindings) :
    ({ ann := none, rhs := binding.rhs.erase } : CoreRecBinding) ∈ eraseBindings bindings := by
  induction bindings with
  | nil => cases hb
  | cons head rest ih =>
      rcases List.mem_cons.mp hb with rfl | hb
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (ih hb)

private theorem eraseBindings_length_local (bindings : List InputRecBinding) :
    (eraseBindings bindings).length = bindings.length := by
  induction bindings with
  | nil => rfl
  | cons binding rest ih => simp [eraseBindings, ih]

private theorem eraseBindings_eq_map_local (bindings : List InputRecBinding) :
    eraseBindings bindings = bindings.map (fun binding =>
      ({ ann := none, rhs := binding.rhs.erase } : CoreRecBinding)) := by
  induction bindings with
  | nil => rfl
  | cons binding rest ih => simp [eraseBindings, ih]

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

/-- Assemble a lambda result from its seeded parameter and inferred body. -/
def lambdaResult (ann : Option TyTemplate) (seeded : SeedResult)
    (bodyResult : InferResult) : InferResult :=
  { frontier := bodyResult.frontier
    subst := bodyResult.subst
    completedExpr := lambdaOutput ann seeded.param bodyResult.subst bodyResult.completedExpr
    ty := .arrow (bodyResult.subst.onTy seeded.param) bodyResult.ty }

/-- Assemble the semantic result of sequential function/argument inference and
the final application unifier. -/
def appResult (functionResult argumentResult : InferResult) (unifier : Subst) : InferResult :=
  { frontier := argumentResult.frontier + 1
    subst := functionResult.subst ++ argumentResult.subst ++ unifier
    completedExpr := .app
      (functionResult.completedExpr.substTyFvars (argumentResult.subst ++ unifier))
      (argumentResult.completedExpr.substTyFvars unifier)
    ty := unifier.onTy (.fvar argumentResult.frontier) }

def letOutput (scheme : PolyTy) (names : List Nat) (rhs body : Expr) (subst : Subst) : Expr :=
  .letIn (some (subst.onPolyTy scheme)) ((rhs.closeTyVars names).substTyFvars subst) body

/-- Assemble either form of let result from its chosen scheme and binder names,
RHS inference, annotation check, and body inference. -/
def letResult (scheme : PolyTy) (names : List Nat) (rhsResult : InferResult)
    (checkResult : CheckResult) (bodyResult : InferResult) : InferResult :=
  { frontier := bodyResult.frontier
    subst := rhsResult.subst ++ checkResult.subst ++ bodyResult.subst
    completedExpr := letOutput scheme names
      (rhsResult.completedExpr.substTyFvars checkResult.subst)
      bodyResult.completedExpr bodyResult.subst
    ty := bodyResult.ty }

/-- Assemble a match result from the inferred scrutinee and the positional
branch judgment's semantic output. -/
def matchResult (scrutineeResult : InferResult)
    (branchesResult : InferBranchesResult) : InferResult :=
  { frontier := branchesResult.frontier
    subst := scrutineeResult.subst ++ branchesResult.subst
    completedExpr := .match_
      (scrutineeResult.completedExpr.substTyFvars branchesResult.subst)
      branchesResult.completedBranches
    ty := branchesResult.subst.onTy (.fvar scrutineeResult.frontier) }

/-- Assemble a recursive-let result from the two recursive phases, the
completed member evidence, and body inference. -/
def letRecResult (completed : List CompletedRecMember)
    (strataResult signedResult : RecRunResult) (bodyResult : InferResult) : InferResult :=
  { frontier := bodyResult.frontier
    subst := strataResult.subst ++ signedResult.subst ++ bodyResult.subst
    completedExpr := .letRec (completed.map fun member =>
      { ann := some (bodyResult.subst.onPolyTy member.scheme)
        rhs := member.output.substTyFvars bodyResult.subst }) bodyResult.completedExpr
    ty := bodyResult.ty }

mutual
/-- Canonical inference carries frozen K and the current images F of live
provisional forall slots. Sequential calls transform both F and source syntax. -/
inductive InferCert : InferRequest → InferResult → Prop
  | primLitUnit : InferCert ⟨K, F, frontier, ctx, .primLit .unit⟩
      ⟨frontier, [], .primLit .unit, .prim .unit⟩
  | primLitInt : InferCert ⟨K, F, frontier, ctx, .primLit (.int n)⟩
      ⟨frontier, [], .primLit (.int n), .prim .int⟩
  | primLitNat : InferCert ⟨K, F, frontier, ctx, .primLit (.nat n)⟩
      ⟨frontier, [], .primLit (.nat n), .prim .nat⟩
  | primLitChar : InferCert ⟨K, F, frontier, ctx, .primLit (.char c)⟩
      ⟨frontier, [], .primLit (.char c), .prim .char⟩
  | primBinOpIntAdd : InferCert ⟨K, F, frontier, ctx, .primBinOp .intAdd⟩
      ⟨frontier, [], .primBinOp .intAdd, .arrow (.prim .int) (.arrow (.prim .int) (.prim .int))⟩
  | primBinOpIntSub : InferCert ⟨K, F, frontier, ctx, .primBinOp .intSub⟩
      ⟨frontier, [], .primBinOp .intSub, .arrow (.prim .int) (.arrow (.prim .int) (.prim .int))⟩
  | primBinOpIntLt :
      LookupList.get? ctx.ctors ⟨"True"⟩ = some trueC → trueC.IsBoolCtor →
      LookupList.get? ctx.ctors ⟨"False"⟩ = some falseC → falseC.IsBoolCtor →
      InferCert ⟨K, F, frontier, ctx, .primBinOp .intLt⟩
        ⟨frontier, [], .primBinOp .intLt,
          .arrow (.prim .int) (.arrow (.prim .int) (.customTy ⟨"Bool"⟩ []))⟩
  | primBinOpCharLt :
      LookupList.get? ctx.ctors ⟨"True"⟩ = some trueC → trueC.IsBoolCtor →
      LookupList.get? ctx.ctors ⟨"False"⟩ = some falseC → falseC.IsBoolCtor →
      InferCert ⟨K, F, frontier, ctx, .primBinOp .charLt⟩
        ⟨frontier, [], .primBinOp .charLt,
          .arrow (.prim .char) (.arrow (.prim .char) (.customTy ⟨"Bool"⟩ []))⟩
  | var : ctx.env[index]? = some scheme →
      InferCert ⟨K, F, frontier, ctx, .var index⟩
        ⟨frontier + scheme.paramCount, [], .var index,
          scheme.openVars (freshVars frontier scheme.paramCount)⟩
  | ctor : LookupList.get? ctx.ctors name = some ctor →
      InferCert ⟨K, F, frontier, ctx, .ctor name⟩
        ⟨frontier + ctor.paramCount, [], .ctor name,
          ctor.toTy.openVars (freshVars frontier ctor.paramCount)⟩
  | lambda {K : List Nat} {F : List Ty} {ann : Option TyTemplate} {body : InferInput}
      {frontier : Nat} {ctx : Ctx} {seeded : SeedResult} {bodyResult : InferResult} :
      SourceScope K F (.lambda ann body) →
      Seed (K ++ softVars F) frontier ann seeded.param seeded.frontier →
      InferCert
        ⟨K, F, seeded.frontier,
          { ctx with env := PolyTy.mkTrivial seeded.param :: ctx.env }, body⟩
        bodyResult →
      InferCert ⟨K, F, frontier, ctx, .lambda ann body⟩
        (lambdaResult ann seeded bodyResult)
  | app {K : List Nat} {F : List Ty} {f arg : InferInput} {frontier : Nat} {ctx : Ctx}
      {functionResult argumentResult : InferResult} {unifier : Subst} :
      SourceScope K F (.app f arg) →
      InferCert ⟨K, F, frontier, ctx, f⟩ functionResult →
      InferCert
        ⟨K, substSoft functionResult.subst F, functionResult.frontier,
          functionResult.subst.onCtx ctx, arg.substTyFvars functionResult.subst⟩
        argumentResult →
      RigidUnify K (argumentResult.subst.onTy functionResult.ty)
        (.arrow argumentResult.ty (.fvar argumentResult.frontier)) unifier →
      InferCert ⟨K, F, frontier, ctx, .app f arg⟩
        (appResult functionResult argumentResult unifier)
  | letIn {K : List Nat} {F : List Ty} {ann : BindingAnn} {rhs body : InferInput}
      {frontier : Nat} {ctx : Ctx} {rhsResult : InferResult}
      {checkResult : CheckResult} {bodyResult : InferResult} :
      SourceScope K F (.letIn ann rhs body) →
      InferCert ⟨K, F, frontier, ctx, rhs⟩ rhsResult →
      LetCheck K (substSoft rhsResult.subst F) rhsResult.frontier rhsResult.ty
        (ann.substTyFvars rhsResult.subst) checkResult.frontier checkResult.subst →
      (let checkedSubst := rhsResult.subst ++ checkResult.subst
       let checkedSoft := substSoft checkedSubst F
       let checkedCtx := checkResult.subst.onCtx (rhsResult.subst.onCtx ctx)
       let generalized := genScheme (K ++ softVars checkedSoft) checkedCtx.env
         (checkResult.subst.onTy rhsResult.ty)
       InferCert
         ⟨K, checkedSoft, checkResult.frontier,
           { checkedCtx with env := generalized :: checkedCtx.env },
           body.substTyFvars checkedSubst⟩
         bodyResult) →
      InferCert ⟨K, F, frontier, ctx, .letIn ann rhs body⟩
        (let checkedSubst := rhsResult.subst ++ checkResult.subst
         let checkedSoft := substSoft checkedSubst F
         let checkedCtx := checkResult.subst.onCtx (rhsResult.subst.onCtx ctx)
         let generalized := genScheme (K ++ softVars checkedSoft) checkedCtx.env
           (checkResult.subst.onTy rhsResult.ty)
         let generalizedNames := genVars (K ++ softVars checkedSoft) checkedCtx.env
           (checkResult.subst.onTy rhsResult.ty)
         letResult generalized generalizedNames rhsResult checkResult bodyResult)
  | letSignature {K : List Nat} {F : List Ty} {ann : BindingAnn}
      {rhs body : InferInput} {written : List Nat} {frontier : Nat} {ctx : Ctx}
      {rhsResult : InferResult} {checkResult : CheckResult} {bodyResult : InferResult} :
      SourceScope K F (.letIn ann rhs body) →
      written = freshVars frontier ann.paramCount →
      (∀ name ∈ written, name ∉ K ++ softVars F) →
      InferCert ⟨K ++ written, F, frontier + ann.paramCount, ctx, rhs.openTyVars written⟩
        rhsResult →
      SignatureCheck K (substSoft rhsResult.subst F) written rhsResult.frontier rhsResult.ty
        (ann.substTyFvars rhsResult.subst) checkResult.frontier checkResult.subst →
      (let checkedSubst := rhsResult.subst ++ checkResult.subst
       let checkedSoft := substSoft checkedSubst F
       let checkedCtx := checkResult.subst.onCtx (rhsResult.subst.onCtx ctx)
       ∀ name ∈ written, name ∉ checkedCtx.env.freeVars ++ softVars checkedSoft) →
      (let checkedSubst := rhsResult.subst ++ checkResult.subst
       let checkedSoft := substSoft checkedSubst F
       let checkedCtx := checkResult.subst.onCtx (rhsResult.subst.onCtx ctx)
       let checkedAnn := ann.substTyFvars checkedSubst
       let bodyScheme := signatureScheme checkedAnn (K ++ softVars checkedSoft) written
         checkedCtx (checkResult.subst.onTy rhsResult.ty)
       InferCert
         ⟨K, checkedSoft, checkResult.frontier,
           { checkedCtx with env := bodyScheme :: checkedCtx.env },
           body.substTyFvars checkedSubst⟩
         bodyResult) →
      InferCert ⟨K, F, frontier, ctx, .letIn ann rhs body⟩
        (let checkedSubst := rhsResult.subst ++ checkResult.subst
         let checkedSoft := substSoft checkedSubst F
         let checkedCtx := checkResult.subst.onCtx (rhsResult.subst.onCtx ctx)
         let checkedAnn := ann.substTyFvars checkedSubst
         let bodyScheme := signatureScheme checkedAnn (K ++ softVars checkedSoft) written
           checkedCtx (checkResult.subst.onTy rhsResult.ty)
         let bodyNames := signatureNames checkedAnn (K ++ softVars checkedSoft) written
           checkedCtx (checkResult.subst.onTy rhsResult.ty)
         letResult bodyScheme bodyNames rhsResult checkResult bodyResult)
  | match_ {K : List Nat} {F : List Ty} {scrut : InferInput}
      {branches : List (MatchPattern × InferInput)} {frontier : Nat} {ctx : Ctx}
      {scrutineeResult : InferResult} {branchesResult : InferBranchesResult} :
      SourceScope K F (.match_ scrut branches) →
      InferCert ⟨K, F, frontier, ctx, scrut⟩ scrutineeResult →
      branches ≠ [] →
      (let branchSoft := substSoft scrutineeResult.subst F
       let branchCtx := scrutineeResult.subst.onCtx ctx
       let branchInputs := substInputBranches scrutineeResult.subst branches
       InferBranches K branchSoft (scrutineeResult.frontier + 1) branchCtx
         scrutineeResult.ty (.fvar scrutineeResult.frontier) branchInputs
         branchesResult.frontier branchesResult.subst branchesResult.completedBranches) →
      InferCert ⟨K, F, frontier, ctx, .match_ scrut branches⟩
        (matchResult scrutineeResult branchesResult)

  | letRec {K : List Nat} {F : List Ty} {bindings : List InputRecBinding}
      {body : InferInput} {frontier : Nat} {ctx : Ctx}
      {completed : List CompletedRecMember} {strataResult signedResult : RecRunResult}
      {bodyResult : InferResult} :
      (SourceScope K F (.letRec bindings body) ∧ CtxBelow frontier ctx ∧
        (∀ v ∈ K, v < frontier) ∧ (∀ v ∈ softVars F, v < frontier)) →
      (∀ scheme, .complete scheme ∈ bindings.map (·.ann) → scheme.WF) →
      (let modes := bindings.map InputRecBinding.recMode
       let groups := RecGroup.inferenceSccs modes
       let seededFrontier := frontier + bindings.length
       let initialState := RecState.init frontier bindings
       InferRecStrata K F seededFrontier ctx bindings initialState groups
         strataResult.frontier strataResult.subst strataResult.state) →
      (let signedSoft := substSoft strataResult.subst F
       let signedCtx := strataResult.subst.onCtx ctx
       let signedBindings := substInputBindings strataResult.subst bindings
       InferRecSigned K signedSoft 0 strataResult.frontier signedCtx signedBindings
         strataResult.state signedResult.frontier signedResult.subst signedResult.state) →
      signedResult.state.Completed completed →
      (let recSubst := strataResult.subst ++ signedResult.subst
       InferCert
         ⟨K, substSoft recSubst F, signedResult.frontier,
           signedResult.state.rhsCtx (recSubst.onCtx ctx),
           body.substTyFvars recSubst⟩
         bodyResult) →
      InferCert ⟨K, F, frontier, ctx, .letRec bindings body⟩
        (letRecResult completed strataResult signedResult bodyResult)

inductive InferBranches : List Nat → List Ty → Nat → Ctx → Ty → Ty →
    List (MatchPattern × InferInput) → Nat → Subst → List (MatchPattern × Expr) → Prop
  | nil : InferBranches K F frontier ctx scrutTy resultTy [] frontier [] []
  | consWild :
      (∀ v ∈ rigidBranchVars ((.wildcard, body) :: rest), v ∈ K ++ softVars F) →
      InferCert ⟨K, F, frontier, ctx, body⟩ ⟨first, s1, bodyOut, bodyTy⟩ →
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
      InferCert
        ⟨K, substSoft s0 F, frontier + ctor.paramCount,
          { (s0.onCtx ctx) with
            env := (ctor.contents.map (Ty.openWith (((freshVars frontier ctor.paramCount).map Ty.fvar).map s0.onTy))).map PolyTy.mkTrivial ++
                (s0.onCtx ctx).env },
          body.substTyFvars s0⟩
        ⟨first, s1, bodyOut, bodyTy⟩ →
      RigidUnify K bodyTy (s1.onTy (s0.onTy resultTy)) s2 →
      InferBranches K (substSoft (s0 ++ s1 ++ s2) F) first (s2.onCtx (s1.onCtx (s0.onCtx ctx)))
        (s2.onTy (s1.onTy (s0.onTy scrutTy))) (s2.onTy (s1.onTy (s0.onTy resultTy)))
        (substInputBranches (s0 ++ s1 ++ s2) rest) next s3 restOut →
      InferBranches K F frontier ctx scrutTy resultTy ((.named name count, body) :: rest) next
        (s0 ++ s1 ++ s2 ++ s3) ((.named name count, bodyOut.substTyFvars (s2 ++ s3)) :: restOut)
/-- Infer one selected SCC in the original full group coordinates. Sources have
already been opened at flexible written roots and transformed by shape solving. -/
inductive InferRecComponent : List Nat → List Ty → List Nat → Nat → Nat → Ctx →
    List InputRecBinding → List RecSpec → Nat → Subst → List (Option RecComponentArtifact) → Prop
  | nil : InferRecComponent K F members index frontier ctx [] [] frontier [] []
  | skipMono :
      index ∉ members →
      InferRecComponent K F members (index + 1) frontier ctx rest specs next subst artifacts →
      InferRecComponent K F members index frontier ctx (binding :: rest) (.mono ty :: specs)
        next subst (none :: artifacts)
  | skipPoly :
      InferRecComponent K F members (index + 1) frontier ctx rest specs next subst artifacts →
      InferRecComponent K F members index frontier ctx (binding :: rest) (.poly scheme :: specs)
        next subst (none :: artifacts)
  | consSelected {bodyFacts : RecFacts} :
      index ∈ members →
      InferCert ⟨K, F, frontier, ctx, binding.rhs⟩ ⟨first, s1, output, ty⟩ →
      RigidUnify K ty (s1.onTy expected) s2 →
      InferRecComponent K (substSoft (s1 ++ s2) F) members (index + 1) first
        (s2.onCtx (s1.onCtx ctx)) (substInputBindings (s1 ++ s2) rest)
        (specs.map (RecSpec.onSubstSource (s1 ++ s2))) next s3 artifacts →
      InferRecComponent K F members index frontier ctx (binding :: rest) (.mono expected :: specs)
        next (s1 ++ s2 ++ s3)
        (some ((RecComponentArtifact.mk output bodyFacts).onSubst (s2 ++ s3)) :: artifacts)

/-- Component scheduling is shared with complete Core. Only completed contracts
cut dependencies; each partial signature is solved in its monomorphic SCC. -/
inductive InferRecStrata : List Nat → List Ty → Nat → Ctx → List InputRecBinding →
    RecState → List (List Nat) → Nat → Subst → RecState → Prop
  | nil : InferRecStrata K F frontier ctx bindings state [] frontier [] state
  | cons {state : RecState} :
      OpenRecAnns component 0 frontier bindings opened openings →
      CheckRecShapes K ((state.installOpenings component openings).shapes component openings) pre →
      InferRecComponent K
        (substSoft pre (F ++ (openings.flatMap RecOpening.written).map Ty.fvar)) component 0 opened
        (((state.installOpenings component openings).onSubst pre).rhsCtx (pre.onCtx ctx))
        (substInputBindings pre (openRecSources openings bindings))
        ((state.installOpenings component openings).onSubst pre).specs
        first current artifacts →
      FinishRecComponent K (softVars (substSoft (pre ++ current) F)) component
        ((pre ++ current).onCtx ctx) ((state.installOpenings component openings).onSubst (pre ++ current))
        artifacts exported →
      InferRecStrata K (substSoft (pre ++ current) F) first ((pre ++ current).onCtx ctx)
        (substInputBindings (pre ++ current) bindings) exported rest next tail final →
      InferRecStrata K F frontier ctx bindings state (component :: rest)
        next (pre ++ current ++ tail) final

/-- Completely written recursive contracts are checked after inferred SCCs,
under their completed final exports, with fresh rigid openings. -/
inductive InferRecSigned : List Nat → List Ty → Nat → Nat → Ctx → List InputRecBinding →
    RecState → Nat → Subst → RecState → Prop
  | nil : InferRecSigned K F index frontier ctx [] state frontier [] state
  | skip :
      binding.ann.recModeAnn = none →
      InferRecSigned K F (index + 1) frontier ctx bindings state next subst final →
      InferRecSigned K F index frontier ctx (binding :: bindings) state next subst final
  | cons {scheme : PolyTy} {rhs : InferInput} {state : RecState} {bodyFacts : RecFacts} :
      scheme.WF →
      (∀ v ∈ rhs.rigidVars, v ∈ K ++ softVars F) →
      InferCert
        ⟨K ++ freshVars frontier scheme.paramCount, F, frontier + scheme.paramCount,
          state.rhsCtx ctx, rhs.openTyVars (freshVars frontier scheme.paramCount)⟩
        ⟨first, s1, output, ty⟩ →
      RigidUnify (K ++ freshVars frontier scheme.paramCount) ty
        ((s1.onPolyTy scheme).openVars (freshVars frontier scheme.paramCount)) s2 →
      (∀ y ∈ freshVars frontier scheme.paramCount,
        y ∉ (((state.onSubst (s1 ++ s2)).rhsCtx ((s1 ++ s2).onCtx ctx)).env.freeVars ++
          softVars (substSoft (s1 ++ s2) F))) →
      InferRecSigned K (substSoft (s1 ++ s2) F) (index + 1) first ((s1 ++ s2).onCtx ctx)
        (substInputBindings (s1 ++ s2) bindings)
        ((state.onSubst (s1 ++ s2)).setSigned index (freshVars frontier scheme.paramCount)
          (output.substTyFvars s2) (bodyFacts.onSubst s2)) next tail final →
      InferRecSigned K F index frontier ctx
        ({ ann := .complete scheme, rhs := rhs } :: bindings) state
        next (s1 ++ s2 ++ tail) final

end

/-- Positional compatibility view of the canonical bundled certificate.
New proofs should state their contracts with `InferCert`; this alias keeps the
established internal theorem surface definitionally equal during migration. -/
abbrev Infer (K : List Nat) (F : List Ty) (frontier : Nat) (ctx : Ctx)
    (input : InferInput) (next : Nat) (subst : Subst) (output : Expr) (ty : Ty) : Prop :=
  InferCert (InferRequest.mk K F frontier ctx input) (InferResult.mk next subst output ty)

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

private theorem InferCert.sourceScope_raw (h : Infer K F frontier ctx input next subst output ty) :
    SourceScope K F input := by
  cases h with
  | primLitUnit | primLitInt | primLitNat | primLitChar | primBinOpIntAdd | primBinOpIntSub | primBinOpIntLt _ _ _ _ | primBinOpCharLt _ _ _ _ | var _ | ctor _ =>
      simp [SourceScope, InferInput.rigidVars]
  | lambda hs _ _ => exact hs
  | app hs _ _ _ => exact hs
  | letIn hs _ _ _ => exact hs
  | letSignature hs _ _ _ _ _ _ => exact hs
  | match_ hs _ _ _ => exact hs
  | letRec hs _ _ _ _ _ => exact hs.1

theorem InferCert.sourceScope {request : InferRequest} {result : InferResult}
    (h : InferCert request result) : request.Scoped := by
  cases request
  cases result
  exact InferCert.sourceScope_raw h

theorem Infer.sourceScope (h : Infer K F frontier ctx input next subst output ty) :
    SourceScope K F input :=
  InferCert.sourceScope_raw h

private theorem avoids_append {K : List Nat} {S T : Subst}
    (hS : ∀ p ∈ S, p.1 ∉ K) (hT : ∀ p ∈ T, p.1 ∉ K) :
    ∀ p ∈ S ++ T, p.1 ∉ K :=
  fun p hp => (List.mem_append.mp hp).elim (hS p) (hT p)

mutual
private theorem InferCert.dom_avoids_raw (h : Infer K F frontier ctx input next subst output ty) :
    ∀ pair ∈ subst, pair.1 ∉ K := by
  match h with
  | .primLitUnit | .primLitInt | .primLitNat | .primLitChar | .primBinOpIntAdd | .primBinOpIntSub | .primBinOpIntLt _ _ _ _ | .primBinOpCharLt _ _ _ _ | .var _ | .ctor _ => simp
  | .lambda _ _ hb => exact hb.dom_avoids_raw
  | .app _ hf ha hu => exact avoids_append (avoids_append hf.dom_avoids_raw ha.dom_avoids_raw) hu.dom_avoids
  | .letIn _ hr hc hb => exact avoids_append (avoids_append hr.dom_avoids_raw hc.dom_avoids) hb.dom_avoids_raw
  | .letSignature _ _ _ hr hc _ hb =>
    exact avoids_append (avoids_append
      (fun p hp hk => hr.dom_avoids_raw p hp (List.mem_append_left _ hk))
      (fun p hp hk => hc.dom_avoids p hp (List.mem_append_left _ hk))) hb.dom_avoids_raw
  | .match_ _ hs _ hb => exact avoids_append hs.dom_avoids_raw hb.dom_avoids
  | .letRec _ _ hstrata hsigned _ hbody =>
      exact avoids_append (avoids_append hstrata.dom_avoids hsigned.dom_avoids) hbody.dom_avoids_raw
termination_by (input.size, 0)
decreasing_by all_goals (simp only [InferInput.size, InferInput.size_openTyVars, InferInput.size_substTyFvars, sizeBranches_substInputBranches, sizeBindings_substInputBindings]; omega)

theorem InferBranches.dom_avoids
    (h : InferBranches K F frontier ctx scrutTy resultTy branches next subst completed) :
    ∀ pair ∈ subst, pair.1 ∉ K := by
  match h with
  | .nil => simp
  | .consWild _ hb hu hr => exact avoids_append (avoids_append hb.dom_avoids_raw hu.dom_avoids) hr.dom_avoids
  | .cons _ _ _ hu0 hb hu hr =>
    exact avoids_append (avoids_append (avoids_append hu0.dom_avoids hb.dom_avoids_raw) hu.dom_avoids) hr.dom_avoids
termination_by (sizeBranches branches, 0)
decreasing_by all_goals (simp only [sizeBranches, InferInput.size_substTyFvars, sizeBranches_substInputBranches]; omega)

theorem InferRecComponent.dom_avoids
    (h : InferRecComponent K F members index frontier ctx bindings specs next S artifacts) :
    ∀ pair ∈ S, pair.1 ∉ K := by
  match h with
  | .nil => simp
  | .skipMono _ hr | .skipPoly hr => exact hr.dom_avoids
  | .consSelected _ hi hu hr =>
      exact avoids_append (avoids_append hi.dom_avoids_raw hu.dom_avoids) hr.dom_avoids
termination_by (sizeBindings bindings, 0)
decreasing_by all_goals (simp only [sizeBindings, sizeBindings_substInputBindings]; omega)

theorem InferRecStrata.dom_avoids
    (h : InferRecStrata K F frontier ctx bindings state groups next S final) :
    ∀ pair ∈ S, pair.1 ∉ K := by
  match h with
  | .nil => simp
  | .cons _ hpre hcurrent _ htail =>
      exact avoids_append (avoids_append hpre.dom_avoids hcurrent.dom_avoids) htail.dom_avoids
termination_by (sizeBindings bindings, groups.length + 1)
decreasing_by
  all_goals (simp only [sizeBindings_substInputBindings, sizeBindings_openRecSources, List.length_cons])
  all_goals omega

theorem InferRecSigned.dom_avoids
    (h : InferRecSigned K F index frontier ctx bindings state next S final) :
    ∀ pair ∈ S, pair.1 ∉ K := by
  match h with
  | .nil => simp
  | .skip _ hr => exact hr.dom_avoids
  | .cons _ _ hi hu _ hr =>
      exact avoids_append (avoids_append
        (fun p hp hk => hi.dom_avoids_raw p hp (List.mem_append_left _ hk))
        (fun p hp hk => hu.dom_avoids p hp (List.mem_append_left _ hk))) hr.dom_avoids
termination_by (sizeBindings bindings, 0)
decreasing_by all_goals (simp only [sizeBindings, InferInput.size_openTyVars, sizeBindings_substInputBindings]; omega)
end

theorem InferCert.dom_avoids {request : InferRequest} {result : InferResult}
    (h : InferCert request result) :
    ∀ pair ∈ result.subst, pair.1 ∉ request.protectedVars := by
  cases request
  cases result
  exact InferCert.dom_avoids_raw h

theorem Infer.dom_avoids (h : Infer K F frontier ctx input next subst output ty) :
    ∀ pair ∈ subst, pair.1 ∉ K :=
  InferCert.dom_avoids_raw h

 theorem InferRecComponent.lc_of_infer
    (h : InferRecComponent K F members index frontier ctx bindings specs next S artifacts)
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
        (fun he h => hInfer (by simp only [sizeBindings_substInputBindings] at he; simp only [sizeBindings]; omega) h)
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
  cases hmember : state.memberStates[i]? with
  | none => simp [hmember] at heq
  | some member =>
    have hmember_mem : member ∈ state.memberStates := List.mem_of_getElem? hmember
    cases hs : member.spec with
    | poly σ => simp [hmember, hs, RecSpec.monoTy?] at heq
    | mono ty =>
      cases ho : openings[i]? with
      | none => simp [hmember, RecSpec.monoTy?, ho] at heq
      | some opening =>
        simp [hmember, hs, RecSpec.monoTy?, ho] at heq
        cases heq
        exact ⟨hstate.1 _ (List.mem_map.mpr ⟨member, hmember_mem, hs⟩),
          hopen opening (List.mem_of_getElem? ho)⟩

 theorem InferRecStrata.lc_of_infer
    (h : InferRecStrata K F frontier ctx bindings state groups next S final)
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
      (fun he h => hInfer (by simpa only [sizeBindings_substInputBindings, sizeBindings_openRecSources] using he) h)
      ((hinit.onSubst hpre).rhsCtx (Subst.onCtx_wf hpre hctx)) (hinit.onSubst hpre).1
    have hboth : ∀ p ∈ pre ++ current, p.2.IsLC :=
      fun p hp => (List.mem_append.mp hp).elim (hpre p) (hcurrent p)
    have hexport := hfinish.lc (hinit.onSubst hboth)
    obtain ⟨htail, hfinal⟩ := hrest.lc_of_infer
      (fun he h => hInfer (by simpa only [sizeBindings_substInputBindings] using he) h)
      (Subst.onCtx_wf hboth hctx) hexport
    exact ⟨fun p hp => (List.mem_append.mp hp).elim (hboth p) (htail p), hfinal⟩
 termination_by structural h

 theorem InferRecSigned.lc_of_infer
    (h : InferRecSigned K F index frontier ctx bindings state next S final)
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
        (fun he h => hInfer (by simp only [sizeBindings_substInputBindings] at he; simp only [sizeBindings]; omega) h)
        (Subst.onCtx_wf hboth hctx) ((hstate.onSubst hboth).setSigned)
      exact ⟨fun p hp => (List.mem_append.mp hp).elim (hboth p) (htail p), hfinal⟩
 termination_by structural h


mutual
private theorem InferCert.lc_raw (h : Infer K F frontier ctx input next subst output ty) :
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
  | @InferCert.lambda K F ann body frontier ctx seeded _ _ hs hb =>
      intro hctx
      have hbodyCtx : CtxWF
          { ctx with env := PolyTy.mkTrivial seeded.param :: ctx.env } := by
        intro scheme hscheme
        rcases List.mem_cons.mp hscheme with rfl | hscheme
        · exact hs.lc
        · exact hctx scheme hscheme
      obtain ⟨ht, hsubst⟩ := hb.lc_raw hbodyCtx
      exact ⟨.arrow (Subst.onTy_lc hsubst hs.lc) ht, hsubst⟩
  | .app _ hf hx hu =>
      intro hctx
      obtain ⟨hfTy, hs1⟩ := hf.lc_raw hctx
      obtain ⟨hxTy, hs2⟩ := hx.lc_raw (Subst.onCtx_wf hs1 hctx)
      have hs3 := hu.unifies.lc (Subst.onTy_lc hs2 hfTy) (.arrow hxTy .fvar)
      refine ⟨Subst.onTy_lc hs3 .fvar, ?_⟩
      intro pair hp
      rcases List.mem_append.mp hp with hp | hp
      · exact (List.mem_append.mp hp).elim (hs1 pair) (hs2 pair)
      · exact hs3 pair hp
  | .letIn _ hr hc hb =>
      intro hctx
      obtain ⟨hrTy, hs1⟩ := hr.lc_raw hctx
      have hcheck := hc.lc hrTy
      obtain ⟨hbTy, hs2⟩ := hb.lc_raw (by
        intro scheme hscheme
        rcases List.mem_cons.mp hscheme with rfl | hscheme
        · exact genScheme_wf (Subst.onTy_lc hcheck hrTy)
        · exact Subst.onCtx_wf hcheck (Subst.onCtx_wf hs1 hctx) scheme hscheme)
      refine ⟨hbTy, ?_⟩
      intro pair hp
      rcases List.mem_append.mp hp with hp | hp
      · exact (List.mem_append.mp hp).elim (hs1 pair) (hcheck pair)
      · exact hs2 pair hp

  | .letSignature _ hprefix _ hr hc _ hb =>
    intro hctx
    have hlen : _ := congrArg List.length hprefix
    simp only [freshVars_length] at hlen
    obtain ⟨hrTy, hs1⟩ := hr.lc_raw hctx
    have hcheck := hc.lc (by simpa using hlen) hrTy
    obtain ⟨hbTy, hs2⟩ := hb.lc_raw (by
      intro scheme hscheme
      rcases List.mem_cons.mp hscheme with rfl | hscheme
      · simpa only [BindingAnn.substTyFvars_append] using hc.scheme_wf (Q := K ++ softVars (substSoft (_ ++ _) F)) (by simpa using hlen) hrTy
      · exact Subst.onCtx_wf hcheck (Subst.onCtx_wf hs1 hctx) scheme hscheme)
    exact ⟨hbTy, fun p hp => (List.mem_append.mp hp).elim
      (fun hp => (List.mem_append.mp hp).elim (hs1 p) (hcheck p)) (hs2 p)⟩
  | .match_ _ hs _ hb =>
    intro hctx
    obtain ⟨ht, hS1⟩ := hs.lc_raw hctx
    obtain ⟨hresult, hS2⟩ := hb.lc (Subst.onCtx_wf hS1 hctx) ht .fvar
    exact ⟨hresult, fun p hp => (List.mem_append.mp hp).elim (hS1 p) (hS2 p)⟩
  | .letRec _ hann hs hp _ hb =>
    intro hctx
    obtain ⟨hs1, hstate1⟩ := hs.lc_of_infer
      (fun he hi => hi.lc_raw) hctx (RecState.LC.init (fun binding hbinding scheme heq =>
        hann scheme (List.mem_map.mpr ⟨binding, hbinding, heq⟩)))
    obtain ⟨hs2, hstate2⟩ := hp.lc_of_infer
      (fun he hi => hi.lc_raw) (Subst.onCtx_wf hs1 hctx) hstate1
    have hbodyCtx := hstate2.rhsCtx (Subst.onCtx_wf hs2 (Subst.onCtx_wf hs1 hctx))
    rw [← Subst.onCtx_append] at hbodyCtx
    obtain ⟨ht, hs3⟩ := hb.lc_raw hbodyCtx
    exact ⟨ht, fun p hp => (List.mem_append.mp hp).elim
      (fun hp => (List.mem_append.mp hp).elim (hs1 p) (hs2 p)) (hs3 p)⟩
termination_by (input.size, 0)
decreasing_by
  all_goals simp only [sizeBindings_substInputBindings] at *
  all_goals (simp only [InferInput.size, InferInput.size_openTyVars, InferInput.size_substTyFvars, sizeBranches_substInputBranches]; omega)

theorem InferBranches.lc {Φ ctx scrutTy ρ brs Φ' S}
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
    obtain ⟨hτb_lc, hS₁⟩ := InferCert.lc_raw hbody
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
    obtain ⟨hτb_lc, hS₁⟩ := InferCert.lc_raw hbody hctx
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

theorem InferCert.lc {request : InferRequest} {result : InferResult}
    (h : InferCert request result) (hctx : CtxWF request.ctx) :
    result.ty.IsLC ∧ ∀ pair ∈ result.subst, pair.2.IsLC := by
  cases request
  cases result
  exact InferCert.lc_raw h hctx

theorem Infer.lc (h : Infer K F frontier ctx input next subst output ty) :
    CtxWF ctx → ty.IsLC ∧ ∀ pair ∈ subst, pair.2.IsLC :=
  InferCert.lc_raw h

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

/-- The internal inference result, including source-indexed metadata. -/
structure InferCoreResult extends InferResult where
  nodeTypes : InferredNodeTypes
  binderSchemes : InferredBinderSchemes

structure RecComponentResult where
  frontier : Nat
  subst : Subst
  artifacts : List (Option RecComponentArtifact)

mutual
/-- One metadata-producing inference path for all input syntax. Recursive partial signatures remain
monomorphic until their component is solved and its ordered prefix is validated. -/
def inferWithTypesCore (K : List Nat) (frontier : Nat) (ctx : Ctx) (input : InferInput) (F : List Ty := []) :
    Option { result : InferCoreResult //
      Infer K F frontier ctx input result.frontier result.subst result.completedExpr result.ty } :=
  if hK : K.all (fun v => decide (v < frontier)) = true then
    if hctx : ctx.env.freeVars.all (fun v => decide (v < frontier)) = true then
      if hF : (softVars F).all (fun v => decide (v < frontier)) = true then
        if hsource : input.rigidVars.all (fun v => decide (v ∈ K ++ softVars F)) = true then
          have hrawScope : SourceScope K F input := fun v hv =>
            of_decide_eq_true (List.all_eq_true.mp hsource v hv)
          match input with
          | .primLit .unit => some ⟨{
              frontier := frontier
              subst := []
              completedExpr := .primLit .unit
              ty := .prim .unit
              nodeTypes := .root (.prim .unit)
              binderSchemes := [] }, .primLitUnit⟩
          | .primLit (.int n) => some ⟨{
              frontier := frontier
              subst := []
              completedExpr := .primLit (.int n)
              ty := .prim .int
              nodeTypes := .root (.prim .int)
              binderSchemes := [] }, .primLitInt⟩
          | .primLit (.nat n) => some ⟨{
              frontier := frontier
              subst := []
              completedExpr := .primLit (.nat n)
              ty := .prim .nat
              nodeTypes := .root (.prim .nat)
              binderSchemes := [] }, .primLitNat⟩
          | .primLit (.char c) => some ⟨{
              frontier := frontier
              subst := []
              completedExpr := .primLit (.char c)
              ty := .prim .char
              nodeTypes := .root (.prim .char)
              binderSchemes := [] }, .primLitChar⟩
          | .primBinOp .intAdd =>
              let ty := .arrow (.prim .int) (.arrow (.prim .int) (.prim .int))
              some ⟨{
                frontier := frontier
                subst := []
                completedExpr := .primBinOp .intAdd
                ty := ty
                nodeTypes := .root ty
                binderSchemes := [] }, .primBinOpIntAdd⟩
          | .primBinOp .intSub =>
              let ty := .arrow (.prim .int) (.arrow (.prim .int) (.prim .int))
              some ⟨{
                frontier := frontier
                subst := []
                completedExpr := .primBinOp .intSub
                ty := ty
                nodeTypes := .root ty
                binderSchemes := [] }, .primBinOpIntSub⟩
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
                      some ⟨{
                            frontier := frontier
                            subst := []
                            completedExpr := .primBinOp .intLt
                            ty := ty
                            nodeTypes := .root ty
                            binderSchemes := [] },
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
                      some ⟨{
                            frontier := frontier
                            subst := []
                            completedExpr := .primBinOp .charLt
                            ty := ty
                            nodeTypes := .root ty
                            binderSchemes := [] },
                            .primBinOpCharLt hT (Ctor.isBoolCtor_iff.mp htc) hF (Ctor.isBoolCtor_iff.mp hfc)⟩
                    else none
                  else none
          | .var index =>
              match hlook : ctx.env[index]? with
              | none => none
              | some scheme =>
                  let ty := scheme.openVars (freshVars frontier scheme.paramCount)
                  some ⟨{
                    frontier := frontier + scheme.paramCount
                    subst := []
                    completedExpr := .var index
                    ty := ty
                    nodeTypes := .root ty
                    binderSchemes := [] }, .var hlook⟩
          | .ctor name =>
              match hlook : LookupList.get? ctx.ctors name with
              | none => none
              | some ctor =>
                  let ty := ctor.toTy.openVars (freshVars frontier ctor.paramCount)
                  some ⟨{
                    frontier := frontier + ctor.paramCount
                    subst := []
                    completedExpr := .ctor name
                    ty := ty
                    nodeTypes := .root ty
                    binderSchemes := [] }, .ctor hlook⟩
          | .lambda ann body =>
              match seed (K ++ softVars F) frontier ann with
              | none => none
              | some ⟨(initial, param), hs⟩ =>
                  match inferWithTypesCore K initial { ctx with env := PolyTy.mkTrivial param :: ctx.env } body F with
                  | none => none
                  | some ⟨bodyResult, hb⟩ =>
                      let ty := .arrow (bodyResult.subst.onTy param) bodyResult.ty
                      some ⟨{
                        frontier := bodyResult.frontier
                        subst := bodyResult.subst
                        completedExpr := lambdaOutput ann param bodyResult.subst bodyResult.completedExpr
                        ty := ty
                        nodeTypes := .root ty ++ bodyResult.nodeTypes.below .lambdaBody
                        binderSchemes := bodyResult.binderSchemes.below .lambdaBody }, by
                        simpa only [lambdaResult] using
                          (InferCert.lambda (seeded := ⟨param, initial⟩)
                            (bodyResult := bodyResult.toInferResult) hrawScope hs hb)⟩
          | .app f arg =>
              match inferWithTypesCore K frontier ctx f F with
              | none => none
              | some ⟨fResult, hf⟩ =>
                  match inferWithTypesCore K fResult.frontier (fResult.subst.onCtx ctx)
                      (arg.substTyFvars fResult.subst) (substSoft fResult.subst F) with
                  | none => none
                  | some ⟨argResult, ha⟩ =>
                      match unifyCoreK K (argResult.subst.onTy fResult.ty)
                          (.arrow argResult.ty (.fvar argResult.frontier)) with
                      | none => none
                      | some ⟨s3, hu, hd⟩ =>
                          let ty := s3.onTy (.fvar argResult.frontier)
                          some ⟨{
                            frontier := argResult.frontier + 1
                            subst := fResult.subst ++ argResult.subst ++ s3
                            completedExpr := .app
                              (fResult.completedExpr.substTyFvars (argResult.subst ++ s3))
                              (argResult.completedExpr.substTyFvars s3)
                            ty := ty
                            nodeTypes := .root ty ++
                              (fResult.nodeTypes.onSubst (argResult.subst ++ s3)).below .appFun ++
                              (argResult.nodeTypes.onSubst s3).below .appArg
                            binderSchemes :=
                              (fResult.binderSchemes.onSubst (argResult.subst ++ s3)).below .appFun ++
                              (argResult.binderSchemes.onSubst s3).below .appArg },
                            .app hrawScope hf ha ⟨hu, hd⟩⟩
          | .letIn ann rhs body =>
            if ann.isSignature then
              let written := freshVars frontier ann.paramCount
              match inferWithTypesCore (K ++ written) (frontier + ann.paramCount) ctx (rhs.openTyVars written) F with
                | none => none
                | some ⟨rhsResult, hr⟩ =>
                  match checkSignature K (substSoft rhsResult.subst F) written rhsResult.frontier
                      (ann.substTyFvars rhsResult.subst) rhsResult.ty with
                  | none => none
                  | some ⟨(checked, sCheck), hc⟩ =>
                    let checkedCtx := sCheck.onCtx (rhsResult.subst.onCtx ctx)
                    let checkedTy := sCheck.onTy rhsResult.ty
                    let checkedOut := rhsResult.completedExpr.substTyFvars sCheck
                    let scheme := signatureScheme (ann.substTyFvars (rhsResult.subst ++ sCheck))
                      (K ++ softVars (substSoft (rhsResult.subst ++ sCheck) F)) written checkedCtx checkedTy
                    let names := signatureNames (ann.substTyFvars (rhsResult.subst ++ sCheck))
                      (K ++ softVars (substSoft (rhsResult.subst ++ sCheck) F)) written checkedCtx checkedTy
                    if hescape : ∀ name ∈ written, name ∉ checkedCtx.env.freeVars ++
                        softVars (substSoft (rhsResult.subst ++ sCheck) F) then
                      match inferWithTypesCore K checked { checkedCtx with env := scheme :: checkedCtx.env }
                          (body.substTyFvars (rhsResult.subst ++ sCheck))
                          (substSoft (rhsResult.subst ++ sCheck) F) with
                      | none => none
                      | some ⟨bodyResult, hb⟩ =>
                        let rhsFinalTypes := (((rhsResult.nodeTypes.onSubst sCheck).closeTyVars written)
                            |>.onSubst bodyResult.subst)
                          |>.underTyBinders ann.paramCount |>.below .letRhs
                        let rhsFinalSchemes := (((rhsResult.binderSchemes.onSubst sCheck).closeTyVars written)
                            |>.onSubst bodyResult.subst)
                          |>.underTyBinders ann.paramCount |>.below .letRhs
                        let inferred : InferredBinderSchemes := match ann with
                          | .partialForall _ _ => [{
                              site := .letIn []
                              scheme := bodyResult.subst.onPolyTy scheme
                              tyDepth := 0 }]
                          | _ => []
                        some ⟨{
                          frontier := bodyResult.frontier
                          subst := rhsResult.subst ++ sCheck ++ bodyResult.subst
                          completedExpr := letOutput scheme names checkedOut bodyResult.completedExpr bodyResult.subst
                          ty := bodyResult.ty
                          nodeTypes := .root bodyResult.ty ++ rhsFinalTypes ++
                            bodyResult.nodeTypes.below .letBody
                          binderSchemes := inferred ++ rhsFinalSchemes ++
                            bodyResult.binderSchemes.below .letBody }, by
                          simpa only [letResult] using
                            (InferCert.letSignature
                              (written := written)
                              (rhsResult := rhsResult.toInferResult)
                              (checkResult := ⟨checked, sCheck⟩)
                              (bodyResult := bodyResult.toInferResult)
                              hrawScope rfl (fun name hn hk => by
                                have hlt : name < frontier := by
                                  rcases List.mem_append.mp hk with hk | hk
                                  · exact of_decide_eq_true (List.all_eq_true.mp hK name hk)
                                  · exact of_decide_eq_true (List.all_eq_true.mp hF name hk)
                                have hge := freshVars_ge name hn
                                omega)
                              hr hc hescape hb)⟩
                    else none
            else
                  match inferWithTypesCore K frontier ctx rhs F with
                  | none => none
                  | some ⟨rhsResult, hr⟩ =>
                      match checkLet K (substSoft rhsResult.subst F) rhsResult.frontier
                          (ann.substTyFvars rhsResult.subst) rhsResult.ty with
                      | none => none
                      | some ⟨(checked, sCheck), hc⟩ =>
                          let checkedCtx := sCheck.onCtx (rhsResult.subst.onCtx ctx)
                          let checkedTy := sCheck.onTy rhsResult.ty
                          let checkedOut := rhsResult.completedExpr.substTyFvars sCheck
                          let scheme := genScheme (K ++ softVars (substSoft (rhsResult.subst ++ sCheck) F))
                            checkedCtx.env checkedTy
                          let names := genVars (K ++ softVars (substSoft (rhsResult.subst ++ sCheck) F))
                            checkedCtx.env checkedTy
                          match inferWithTypesCore K checked { checkedCtx with env := scheme :: checkedCtx.env }
                              (body.substTyFvars (rhsResult.subst ++ sCheck))
                              (substSoft (rhsResult.subst ++ sCheck) F) with
                          | none => none
                          | some ⟨bodyResult, hb⟩ =>
                              let binder : InferredBinderScheme :=
                                { site := .letIn [], scheme := bodyResult.subst.onPolyTy scheme, tyDepth := 0 }
                              some ⟨{
                                frontier := bodyResult.frontier
                                subst := rhsResult.subst ++ sCheck ++ bodyResult.subst
                                completedExpr := letOutput scheme names checkedOut bodyResult.completedExpr
                                  bodyResult.subst
                                ty := bodyResult.ty
                                nodeTypes := .root bodyResult.ty ++
                                  (rhsResult.nodeTypes.onSubst (sCheck ++ bodyResult.subst)).below .letRhs ++
                                  bodyResult.nodeTypes.below .letBody
                                binderSchemes := binder ::
                                  (rhsResult.binderSchemes.onSubst (sCheck ++ bodyResult.subst)).below .letRhs ++
                                  bodyResult.binderSchemes.below .letBody }, by
                                simpa only [letResult] using
                                  (InferCert.letIn
                                    (rhsResult := rhsResult.toInferResult)
                                    (checkResult := ⟨checked, sCheck⟩)
                                    (bodyResult := bodyResult.toInferResult)
                                    hrawScope hr hc hb)⟩
          | .match_ scrut branches =>
              match inferWithTypesCore K frontier ctx scrut F with
              | none => none
              | some ⟨scrutResult, hs⟩ =>
                match hh : branches.head? with
                | none => none
                | some _ =>
                  match inferBranchesWithTypesCore K (scrutResult.frontier + 1)
                      (scrutResult.subst.onCtx ctx) scrutResult.ty (.fvar scrutResult.frontier) 0
                      (substInputBranches scrutResult.subst branches) (substSoft scrutResult.subst F) with
                  | none => none
                  | some ⟨(next, s2, branchOut, branchTypes, branchSchemes), hb⟩ =>
                    let ty := s2.onTy (.fvar scrutResult.frontier)
                    some ⟨{
                      frontier := next
                      subst := scrutResult.subst ++ s2
                      completedExpr := .match_ (scrutResult.completedExpr.substTyFvars s2) branchOut
                      ty := ty
                      nodeTypes := .root ty ++ (scrutResult.nodeTypes.onSubst s2).below .matchScrut ++
                        branchTypes
                      binderSchemes := (scrutResult.binderSchemes.onSubst s2).below .matchScrut ++
                        branchSchemes }, by
                      simpa only [matchResult] using
                        (InferCert.match_
                          (scrutineeResult := scrutResult.toInferResult)
                          (branchesResult := ⟨next, s2, branchOut⟩)
                          hrawScope hs (by intro heq; rw [heq] at hh; simp at hh) hb)⟩
          | .letRec bindings body =>
              if hwf : (bindings.map (·.ann)).all (fun ann => match ann with
                  | .complete scheme => scheme.body.bvarsBelow scheme.paramCount
                  | _ => true) = true then
                match inferRecStrataWithTypesCore K F (frontier + bindings.length) ctx bindings
                    (RecState.init frontier bindings)
                    (RecGroup.inferenceSccs (bindings.map InputRecBinding.recMode)) with
                  | none => none
                  | some ⟨strata, hs⟩ =>
                    match inferRecSignedWithTypesCore K (substSoft strata.subst F) 0 strata.frontier
                        (strata.subst.onCtx ctx) (substInputBindings strata.subst bindings)
                        strata.state with
                    | none => none
                    | some ⟨signed, hp⟩ =>
                      match collectCompletedRecMembers signed.state.memberStates with
                      | some ⟨completed, hcompleted⟩ =>
                        let solved := strata.subst ++ signed.subst
                        match inferWithTypesCore K signed.frontier (signed.state.rhsCtx (solved.onCtx ctx))
                            (body.substTyFvars solved) (substSoft solved F) with
                        | none => none
                        | some ⟨bodyResult, hb⟩ =>
                          let final := signed.state.onSubst bodyResult.subst
                          some ⟨{
                            frontier := bodyResult.frontier
                            subst := strata.subst ++ signed.subst ++ bodyResult.subst
                            completedExpr := .letRec (completed.map fun member =>
                              { ann := some (bodyResult.subst.onPolyTy member.scheme),
                                rhs := member.output.substTyFvars bodyResult.subst })
                              bodyResult.completedExpr
                            ty := bodyResult.ty
                            nodeTypes := .root bodyResult.ty ++ finalRecNodeTypes final ++
                              bodyResult.nodeTypes.below .letRecBody
                            binderSchemes := (inferredRecSchemes completed).onSubst bodyResult.subst ++
                              finalRecBinderSchemes final ++
                              bodyResult.binderSchemes.below .letRecBody }, by
                            simpa only [letRecResult] using
                              (InferCert.letRec
                                (completed := completed)
                                (strataResult := strata)
                                (signedResult := signed)
                                (bodyResult := bodyResult.toInferResult)
                                ⟨hrawScope, ctxBelow_of_all hctx,
                                  (fun v hv => of_decide_eq_true (List.all_eq_true.mp hK v hv)),
                                  (fun v hv => of_decide_eq_true (List.all_eq_true.mp hF v hv))⟩
                                (fun scheme hmem => PolyTy.wf_iff_bvarsBelow.mp
                                  (List.all_eq_true.mp hwf (.complete scheme) hmem))
                                hs hp hcompleted hb)⟩
                      | none => none
              else none
        else none
      else none
    else none
  else none
termination_by (input.size, 0)
decreasing_by all_goals (simp only [InferInput.size, InferInput.size_openTyVars,
  InferInput.size_substTyFvars, sizeBranches_substInputBranches,
  sizeBindings_substInputBindings]; omega)

def inferBranchesWithTypesCore (K : List Nat) (Φ : Nat) (ctx : Ctx) (scrutTy : Ty) (ρ : Ty)
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
        | some ⟨bodyResult, hbody⟩ =>
          match unifyCoreK K bodyResult.ty (bodyResult.subst.onTy ρ) with
          | none => none
          | some ⟨S₂, huni, hav₂⟩ =>
            match inferBranchesWithTypesCore K bodyResult.frontier
                (S₂.onCtx (bodyResult.subst.onCtx ctx))
                (S₂.onTy (bodyResult.subst.onTy scrutTy))
                (S₂.onTy (bodyResult.subst.onTy ρ)) (branchIndex + 1)
                (substInputBranches (bodyResult.subst ++ S₂) rest)
                (substSoft (bodyResult.subst ++ S₂) F) with
            | none => none
            | some ⟨(Φ₂, S₃, restOut, restTypes, restSchemes), hrest⟩ =>
              let schemes := (bodyResult.binderSchemes.onSubst (S₂ ++ S₃)).below
                (.matchBranch branchIndex) ++ restSchemes
              let nodeTypes := (bodyResult.nodeTypes.onSubst (S₂ ++ S₃)).below
                (.matchBranch branchIndex) ++ restTypes
              some ⟨(Φ₂, bodyResult.subst ++ S₂ ++ S₃,
                  (.wildcard, bodyResult.completedExpr.substTyFvars (S₂ ++ S₃)) :: restOut,
                  nodeTypes, schemes),
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
              | some ⟨bodyResult, hbody⟩ =>
                match unifyCoreK K bodyResult.ty (bodyResult.subst.onTy (S₀.onTy ρ)) with
                | none => none
                | some ⟨S₂, huni, hav₂⟩ =>
                  match inferBranchesWithTypesCore K bodyResult.frontier
                      (S₂.onCtx (bodyResult.subst.onCtx (S₀.onCtx ctx)))
                      (S₂.onTy (bodyResult.subst.onTy (S₀.onTy scrutTy)))
                      (S₂.onTy (bodyResult.subst.onTy (S₀.onTy ρ)))
                      (branchIndex + 1) (substInputBranches (S₀ ++ bodyResult.subst ++ S₂) rest)
                      (substSoft (S₀ ++ bodyResult.subst ++ S₂) F) with
                  | none => none
                  | some ⟨(Φ₂, S₃, restOut, restTypes, restSchemes), hrest⟩ =>
                    let schemes := (bodyResult.binderSchemes.onSubst (S₂ ++ S₃)).below
                      (.matchBranch branchIndex) ++ restSchemes
                    let nodeTypes := (bodyResult.nodeTypes.onSubst (S₂ ++ S₃)).below
                      (.matchBranch branchIndex) ++ restTypes
                    some ⟨(Φ₂, S₀ ++ bodyResult.subst ++ S₂ ++ S₃,
                        (.named c n, bodyResult.completedExpr.substTyFvars (S₂ ++ S₃)) :: restOut,
                        nodeTypes, schemes),
                        .cons hrawScope hget hcont ⟨huni0, hav0⟩ hbody ⟨huni, hav₂⟩ hrest⟩
          else none
  else none
termination_by (sizeBranches branches, 0)
decreasing_by
  all_goals (try simp only [sizeBranches, InferInput.size_substTyFvars, sizeBranches_substInputBranches]; omega)

/-- One monomorphic component visit, with artifacts in original member order. -/
def inferRecComponentWithTypesCore (K : List Nat) (F : List Ty) (members : List Nat)
    (index frontier : Nat) (ctx : Ctx) (bindings : List InputRecBinding) (specs : List RecSpec) :
    Option { result : RecComponentResult // InferRecComponent K F members index frontier ctx bindings specs
      result.frontier result.subst result.artifacts } :=
  match bindings, specs with
  | [], [] => some ⟨⟨frontier, [], []⟩, .nil⟩
  | binding :: rest, .mono expected :: specs =>
      if hm : index ∈ members then
        match inferWithTypesCore K frontier ctx binding.rhs F with
        | none => none
        | some ⟨rhsResult, hi⟩ =>
          match unifyCoreK K rhsResult.ty (rhsResult.subst.onTy expected) with
          | none => none
          | some ⟨s2, hu, hav⟩ =>
            match inferRecComponentWithTypesCore K (substSoft (rhsResult.subst ++ s2) F) members
                (index + 1) rhsResult.frontier (s2.onCtx (rhsResult.subst.onCtx ctx))
                (substInputBindings (rhsResult.subst ++ s2) rest)
                (specs.map (RecSpec.onSubstSource (rhsResult.subst ++ s2))) with
            | none => none
            | some ⟨tail, ht⟩ =>
              some ⟨⟨tail.frontier, rhsResult.subst ++ s2 ++ tail.subst,
                some ((RecComponentArtifact.mk rhsResult.completedExpr
                  (RecFacts.mk rhsResult.nodeTypes rhsResult.binderSchemes)).onSubst
                    (s2 ++ tail.subst)) :: tail.artifacts⟩,
                .consSelected hm hi ⟨hu, hav⟩ ht⟩
      else
        match inferRecComponentWithTypesCore K F members (index + 1) frontier ctx rest specs with
        | none => none
        | some ⟨tail, ht⟩ =>
          some ⟨⟨tail.frontier, tail.subst, none :: tail.artifacts⟩, .skipMono hm ht⟩
  | _ :: rest, .poly _ :: specs =>
      match inferRecComponentWithTypesCore K F members (index + 1) frontier ctx rest specs with
      | none => none
      | some ⟨tail, ht⟩ =>
        some ⟨⟨tail.frontier, tail.subst, none :: tail.artifacts⟩, .skipPoly ht⟩
  | _, _ => none
termination_by (sizeBindings bindings, 0)
decreasing_by all_goals (simp only [sizeBindings, sizeBindings_substInputBindings]; omega)

/-- Solve shapes and bodies before exporting each SCC. K remains unchanged;
written slots stay flexible until the component's checked solved resolution. -/
def inferRecStrataWithTypesCore (K : List Nat) (F : List Ty) (frontier : Nat)
    (ctx : Ctx) (bindings : List InputRecBinding) (state : RecState)
    (groups : List (List Nat)) :
    Option { result : RecRunResult // InferRecStrata K F frontier ctx bindings state groups
      result.frontier result.subst result.state } :=
  match groups with
  | [] => some ⟨⟨frontier, [], state⟩, .nil⟩
  | component :: rest =>
      match openRecAnns component 0 frontier bindings with
      | none => none
      | some ⟨(opened, openings), ho⟩ =>
        let installed := state.installOpenings component openings
        match checkRecShapes K (installed.shapes component openings) with
        | none => none
        | some ⟨pre, hp⟩ =>
          match inferRecComponentWithTypesCore K
              (substSoft pre (F ++ (openings.flatMap RecOpening.written).map Ty.fvar)) component 0 opened
              ((installed.onSubst pre).rhsCtx (pre.onCtx ctx))
              (substInputBindings pre (openRecSources openings bindings))
              (installed.onSubst pre).specs with
          | none => none
          | some ⟨current, hc⟩ =>
            let solved := pre ++ current.subst
            match finishRecComponent K (softVars (substSoft solved F)) component (solved.onCtx ctx)
                (installed.onSubst solved) current.artifacts with
            | none => none
            | some ⟨exported, he⟩ =>
              match inferRecStrataWithTypesCore K (substSoft solved F) current.frontier (solved.onCtx ctx)
                  (substInputBindings solved bindings)
                  exported rest with
              | none => none
              | some ⟨tail, ht⟩ =>
                some ⟨⟨tail.frontier, pre ++ current.subst ++ tail.subst, tail.state⟩, .cons ho hp hc he ht⟩
termination_by (sizeBindings bindings, groups.length + 1)
decreasing_by
  all_goals (simp only [sizeBindings_substInputBindings, sizeBindings_openRecSources, List.length_cons])
  all_goals apply Prod.Lex.right
  all_goals omega

/-- Complete contracts retain polymorphic recursive use and rigid openings. -/
def inferRecSignedWithTypesCore (K : List Nat) (F : List Ty) (index frontier : Nat)
    (ctx : Ctx) (bindings : List InputRecBinding) (state : RecState) :
    Option { result : RecRunResult // InferRecSigned K F index frontier ctx bindings state
      result.frontier result.subst result.state } :=
  match bindings with
  | [] => some ⟨⟨frontier, [], state⟩, .nil⟩
  | ⟨ann, rhs⟩ :: rest =>
    match ann with
    | .complete scheme =>
      if hwf : scheme.body.bvarsBelow scheme.paramCount = true then
        if hraw : rhs.rigidVars.all (fun v => decide (v ∈ K ++ softVars F)) = true then
          let written := freshVars frontier scheme.paramCount
          match inferWithTypesCore (K ++ written) (frontier + scheme.paramCount)
              (state.rhsCtx ctx) (rhs.openTyVars written) F with
          | none => none
          | some ⟨rhsResult, hi⟩ =>
            match unifyCoreK (K ++ written) rhsResult.ty
                ((rhsResult.subst.onPolyTy scheme).openVars written) with
            | none => none
            | some ⟨s2, hu, hav⟩ =>
              let solved := rhsResult.subst ++ s2
              let checked := state.onSubst solved
              if he : ∀ y ∈ written,
                  y ∉ (checked.rhsCtx (solved.onCtx ctx)).env.freeVars ++ softVars (substSoft solved F) then
                match inferRecSignedWithTypesCore K (substSoft solved F) (index + 1)
                    rhsResult.frontier (solved.onCtx ctx)
                    (substInputBindings solved rest)
                    (checked.setSigned index written (rhsResult.completedExpr.substTyFvars s2)
                      ((RecFacts.mk rhsResult.nodeTypes rhsResult.binderSchemes).onSubst s2)) with
                | none => none
                | some ⟨tail, ht⟩ =>
                  some ⟨⟨tail.frontier, rhsResult.subst ++ s2 ++ tail.subst, tail.state⟩,
                    .cons (PolyTy.wf_iff_bvarsBelow.mp hwf)
                      (fun v hv => of_decide_eq_true (List.all_eq_true.mp hraw v hv)) hi ⟨hu, hav⟩ he ht⟩
              else none
        else none
      else none
    | .absent | .template _ | .partialForall _ _ =>
      match inferRecSignedWithTypesCore K F (index + 1) frontier ctx rest state with
      | none => none
      | some ⟨tail, ht⟩ => some ⟨tail, .skip rfl ht⟩
termination_by (sizeBindings bindings, 0)
decreasing_by all_goals (simp only [sizeBindings, InferInput.size_openTyVars,
  sizeBindings_substInputBindings]; omega)

end

/-- Run the certified worker from one bundled request. -/
def inferRequestCore (request : InferRequest) :
    Option { result : InferCoreResult // InferCert request result.toInferResult } :=
  inferWithTypesCore request.protectedVars request.frontier request.ctx request.input request.soft

/-- Project a certified request run to its semantic result. -/
def inferRequest (request : InferRequest) :
    Option { result : InferResult // InferCert request result } :=
  (inferRequestCore request).map fun result =>
    ⟨result.val.toInferResult, result.property⟩

/-- Forget the dependent certificate while retaining the worker's full result. -/
def InferRequest.run (request : InferRequest) : Option InferCoreResult :=
  (inferRequestCore request).map Subtype.val

/-- Exact graph of the bundled inference worker. -/
def InferRun (request : InferRequest) (result : InferCoreResult) : Prop :=
  request.run = some result

/-- The executable graph returns at most one result for a request. -/
theorem InferRun.result_eq {request : InferRequest} {first second : InferCoreResult}
    (hfirst : InferRun request first) (hsecond : InferRun request second) : first = second := by
  unfold InferRun at hfirst hsecond
  exact Option.some.inj (hfirst.symm.trans hsecond)

/-- Every recorded worker run carries a derivation of the compact certificate. -/
theorem InferRun.cert {request : InferRequest} {result : InferCoreResult}
    (h : InferRun request result) : InferCert request result.toInferResult := by
  unfold InferRun InferRequest.run at h
  cases hrun : inferRequestCore request with
  | none => simp only [hrun, Option.map_none, reduceCtorEq] at h
  | some certified =>
      simp only [hrun, Option.map_some, Option.some.injEq] at h
      rw [← h]
      exact certified.property

@[simp] theorem InferRequest.run_isSome (request : InferRequest) :
    request.run.isSome = (inferRequestCore request).isSome := by
  unfold InferRequest.run
  cases inferRequestCore request <;> rfl

/-- The bundled run and the underlying metadata-producing worker have the same
acceptance behavior. This is the normalization boundary used by proofs that
reason request-first while executing the concrete worker. -/
theorem InferRequest.run_isSome_worker (request : InferRequest) :
    request.run.isSome =
      (inferWithTypesCore request.protectedVars request.frontier request.ctx
        request.input request.soft).isSome := by
  rw [InferRequest.run_isSome]
  rfl

theorem InferRequest.run_isSome_iff_exists (request : InferRequest) :
    request.run.isSome ↔ ∃ result, InferRun request result := by
  cases hrun : request.run with
  | none => simp [InferRun, hrun]
  | some result => simp [InferRun, hrun]

/-- The plain certificate API projects the one metadata-producing run. -/
def inferCore (K : List Nat) (frontier : Nat) (ctx : Ctx) (input : InferInput) :
    Option { result : InferResult //
      Infer K [] frontier ctx input result.frontier result.subst result.completedExpr result.ty } :=
  inferRequest (InferRequest.core K frontier ctx input)

@[simp] theorem inferCore_isSome (K : List Nat) (frontier : Nat) (ctx : Ctx) (input : InferInput) :
    (inferCore K frontier ctx input).isSome = (inferWithTypesCore K frontier ctx input).isSome := by
  unfold inferCore inferRequest inferRequestCore InferRequest.core
  cases inferWithTypesCore K frontier ctx input with
  | none => rfl
  | some result => rfl

/-- Public artifacts and completed ordinary Core come from the same inference. -/
structure InferenceResult extends InferResult where
  nodeTypes : NodeTypeMap
  binderSchemes : BinderSchemeMap

def InferInput.freshFloor (input : InferInput) : Nat := tyVarCeil input.rigidVars

theorem InferInput.lt_freshFloor {input : InferInput} {v : Nat} (h : v ∈ input.rigidVars) :
    v < input.freshFloor := lt_tyVarCeil h

def inferWithTypes (ctors : CtorEnv) (input : InferInput) : Option InferenceResult :=
  (inferWithTypesCore input.rigidVars input.freshFloor ⟨[], ctors⟩ input).map fun result =>
    {
      toInferResult := result.val.toInferResult
      nodeTypes := result.val.nodeTypes.toMap
      binderSchemes := result.val.binderSchemes.toMap }

def principalType (ctors : CtorEnv) (input : InferInput) : Option Ty :=
  (inferCore input.rigidVars input.freshFloor ⟨[], ctors⟩ input).map (·.val.ty)

def typecheck (ctors : CtorEnv) (input : InferInput) : Option PolyTy :=
  (principalType ctors input).map (genScheme [] [])

/-- A public artifact result carries the canonical elaboration derivation. -/
theorem inferWithTypes_infer {ctors : CtorEnv} {input : InferInput} {result : InferenceResult}
    (h : inferWithTypes ctors input = some result) :
    InferCert (InferRequest.core input.rigidVars input.freshFloor ⟨[], ctors⟩ input)
      result.toInferResult := by
  unfold inferWithTypes at h
  cases hcore : inferWithTypesCore input.rigidVars input.freshFloor ⟨[], ctors⟩ input with
  | none => simp only [hcore, Option.map_none, reduceCtorEq] at h
  | some r =>
    rcases r with ⟨coreResult, hi⟩
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
private theorem InferCert.frontier_le_raw
    (h : Infer K F frontier ctx input next subst output ty) : frontier ≤ next := by
  match h with
  | .primLitUnit | .primLitInt | .primLitNat | .primLitChar | .primBinOpIntAdd | .primBinOpIntSub | .primBinOpIntLt _ _ _ _ | .primBinOpCharLt _ _ _ _ => exact Nat.le_refl _
  | .var _ | .ctor _ => exact Nat.le_add_right _ _
  | .lambda _ hs hb => exact hs.frontier_le.trans hb.frontier_le_raw
  | .app _ hf ha _ => have := hf.frontier_le_raw; have := ha.frontier_le_raw; omega
  | .letIn _ hr hc hb => exact hr.frontier_le_raw.trans (hc.frontier_le.trans hb.frontier_le_raw)
  | .letSignature _ _ _ hr hc _ hb =>
      have := hr.frontier_le_raw
      have := hc.frontier_le
      have := hb.frontier_le_raw
      omega
  | .match_ _ hs _ hb => have := hs.frontier_le_raw; have := hb.frontier_le; omega
  | .letRec _ _ hstrata hsigned _ hbody =>
      have := hstrata.frontier_le; have := hsigned.frontier_le; have := hbody.frontier_le_raw; omega
termination_by (input.size, 0)
decreasing_by all_goals (simp only [InferInput.size, InferInput.size_openTyVars, InferInput.size_substTyFvars, sizeBranches_substInputBranches, sizeBindings_substInputBindings] at *; omega)

theorem InferBranches.frontier_le
    (h : InferBranches K F frontier ctx scrutTy resultTy branches next subst output) : frontier ≤ next := by
  match h with
  | .nil => omega
  | .cons _ _ _ _ hb _ hr => have := hb.frontier_le_raw; have := hr.frontier_le; omega
  | .consWild _ hb _ hr => have := hb.frontier_le_raw; have := hr.frontier_le; omega
termination_by (sizeBranches branches, 0)
decreasing_by all_goals (simp only [sizeBranches, InferInput.size_substTyFvars, sizeBranches_substInputBranches]; omega)

theorem InferRecComponent.frontier_le
    (h : InferRecComponent K F members index frontier ctx bindings specs next S artifacts) :
    frontier ≤ next := by
  match h with
  | .nil => exact Nat.le_refl _
  | .skipMono _ hr | .skipPoly hr => exact hr.frontier_le
  | .consSelected _ hi _ hr => exact hi.frontier_le_raw.trans hr.frontier_le
termination_by (sizeBindings bindings, 0)
decreasing_by all_goals (simp only [sizeBindings, sizeBindings_substInputBindings]; omega)

theorem InferRecStrata.frontier_le
    (h : InferRecStrata K F frontier ctx bindings state groups next S final) : frontier ≤ next := by
  match h with
  | .nil => exact Nat.le_refl _
  | .cons ho _ hc _ hr => exact ho.frontier_le.trans (hc.frontier_le.trans hr.frontier_le)
termination_by (sizeBindings bindings, groups.length + 1)
decreasing_by all_goals (simp only [sizeBindings_substInputBindings, sizeBindings_openRecSources, List.length_cons]; omega)

theorem InferRecSigned.frontier_le
    (h : InferRecSigned K F index frontier ctx bindings state next S final) : frontier ≤ next := by
  match h with
  | .nil => exact Nat.le_refl _
  | .skip _ hr => exact hr.frontier_le
  | .cons _ _ hi _ _ hr => have := hi.frontier_le_raw; have := hr.frontier_le; omega
termination_by (sizeBindings bindings, 0)
decreasing_by all_goals (simp only [sizeBindings, InferInput.size_openTyVars, sizeBindings_substInputBindings]; omega)
end

theorem InferCert.frontier_le {request : InferRequest} {result : InferResult}
    (h : InferCert request result) : request.frontier ≤ result.frontier := by
  cases request
  cases result
  exact InferCert.frontier_le_raw h

theorem Infer.frontier_le (h : Infer K F frontier ctx input next subst output ty) : frontier ≤ next :=
  InferCert.frontier_le_raw h


private theorem bindings_below_subst {bindings : List InputRecBinding}
    (h : ∀ binding ∈ bindings, ∀ v ∈ binding.ann.rigidVars, v < frontier)
    (hS : ∀ p ∈ S, Ty.BelowFvars next p.2) (hle : frontier ≤ next) :
    ∀ binding ∈ substInputBindings S bindings,
      ∀ v ∈ binding.ann.rigidVars, v < next := by
  intro binding hm v hv
  rw [substInputBindings_eq_map] at hm
  obtain ⟨old, hold, rfl⟩ := List.mem_map.mp hm
  obtain ⟨k, hk, hv⟩ := BindingAnn.rigidVars_substTyFvars hv
  exact (Subst.onTy_belowFvars hS
    (.fvar (Nat.lt_of_lt_of_le (h old hold k hk) hle))).mem_lt v hv

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
  cases hmember : state.memberStates[i]? with
  | none => simp [hmember] at heq
  | some member =>
    have hmember_mem : member ∈ state.memberStates := List.mem_of_getElem? hmember
    cases hs : member.spec with
    | poly σ => simp [hmember, hs, RecSpec.monoTy?] at heq
    | mono ty =>
      cases ho : openings[i]? with
      | none => simp [hmember, RecSpec.monoTy?, ho] at heq
      | some opening =>
        simp [hmember, hs, RecSpec.monoTy?, ho] at heq
        cases heq
        exact ⟨hstate.1 _ (List.mem_map.mpr ⟨member, hmember_mem, hs⟩),
          hopen opening (List.mem_of_getElem? ho)⟩

 theorem InferRecComponent.belowFvars_of_infer
    (h : InferRecComponent K F members index frontier ctx bindings specs next S artifacts)
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
      have hle := Infer.frontier_le hi
      have hrle := hr.frontier_le
      obtain ⟨hiTy, hiS⟩ := hInfer (by simp only [sizeBindings]; omega) hi hctx hK hF
      have huS := hu.unifies.belowFvars hiTy (Subst.onTy_belowFvars hiS ((hspec _ List.mem_cons_self).mono hle))
      have hboth : ∀ p ∈ s1 ++ s2, Ty.BelowFvars first p.2 :=
        fun p hp => (List.mem_append.mp hp).elim (hiS p) (huS p)
      have hrS := hr.belowFvars_of_infer
        (fun he h => hInfer (by simp only [sizeBindings_substInputBindings] at he; simp only [sizeBindings]; omega) h)
        (by simpa only [Subst.onCtx_append] using Subst.onCtx_below hboth hle hctx)
        (fun k hk => Nat.lt_of_lt_of_le (hK k hk) hle)
        (substSoft_below hboth hle hF)
        (specs_below_subst (fun spec hm => hspec spec (List.mem_cons_of_mem _ hm)) hboth hle)
      intro p hp
      exact (List.mem_append.mp hp).elim (fun hp => (hboth p hp).mono hrle) (hrS p)
 termination_by structural h

 theorem InferRecStrata.belowFvars_of_infer
    (h : InferRecStrata K F frontier ctx bindings state groups next S final)
    (hInfer : ∀ {κ F' Ψ c e Ψ' T output ty}, e.size ≤ sizeBindings bindings →
      Infer κ F' Ψ c e Ψ' T output ty → CtxBelow Ψ c → (∀ k ∈ κ, k < Ψ) →
      (∀ t ∈ F', Ty.BelowFvars Ψ t) → Ty.BelowFvars Ψ' ty ∧ ∀ p ∈ T, Ty.BelowFvars Ψ' p.2)
    (hctx : CtxBelow frontier ctx) (hK : ∀ k ∈ K, k < frontier)
    (hF : ∀ t ∈ F, Ty.BelowFvars frontier t) (hstate : state.Below frontier)
    (hbindings : ∀ binding ∈ bindings, ∀ v ∈ binding.ann.rigidVars, v < frontier) :
    (∀ p ∈ S, Ty.BelowFvars next p.2) ∧ final.Below next := by
  match h with
  | .nil => exact ⟨by simp, hstate⟩
  | .cons hopen hshape hcomponent hfinish hrest =>
    expose_names
    have hle := hopen.frontier_le
    have hcle := hcomponent.frontier_le
    have hrle := hrest.frontier_le
    have hinit := hstate.installOpenings hopen
    have hpre := hshape.belowFvars (RecState.shapes_below hinit (hopen.expected_below hbindings))
    have hFopened : ∀ t ∈ F ++ (openings.flatMap RecOpening.written).map Ty.fvar, Ty.BelowFvars opened t := by
      intro t ht
      rcases List.mem_append.mp ht with ht | ht
      · exact (hF t ht).mono hle
      · obtain ⟨v, hv, rfl⟩ := List.mem_map.mp ht
        exact .fvar (hopen.written_range v hv).2
    have hcurrent := hcomponent.belowFvars_of_infer
      (fun he h => hInfer (by simpa only [sizeBindings_substInputBindings, sizeBindings_openRecSources] using he) h)
      ((hinit.onSubst hpre (Nat.le_refl _)).rhsCtx (Subst.onCtx_below hpre hle hctx))
      (fun k hk => Nat.lt_of_lt_of_le (hK k hk) hle)
      (substSoft_below hpre (Nat.le_refl _) hFopened) (hinit.onSubst hpre (Nat.le_refl _)).1
    have hboth : ∀ p ∈ pre ++ current, Ty.BelowFvars first p.2 :=
      fun p hp => (List.mem_append.mp hp).elim (fun hp => (hpre p hp).mono hcle) (hcurrent p)
    have hfullle := hle.trans hcle
    obtain ⟨htail, hfinal⟩ := hrest.belowFvars_of_infer
      (fun he h => hInfer (by simpa only [sizeBindings_substInputBindings] using he) h)
      (Subst.onCtx_below hboth hfullle hctx)
      (fun k hk => Nat.lt_of_lt_of_le (hK k hk) hfullle)
      (substSoft_below hboth hfullle hF)
      (hfinish.below (hinit.onSubst hboth hcle))
      (bindings_below_subst hbindings hboth hfullle)
    exact ⟨fun p hp => (List.mem_append.mp hp).elim (fun hp => (hboth p hp).mono hrle) (htail p), hfinal⟩
 termination_by structural h

 theorem InferRecSigned.belowFvars_of_infer
    (h : InferRecSigned K F index frontier ctx bindings state next S final)
    (hInfer : ∀ {κ F' Ψ c e Ψ' T output ty}, e.size ≤ sizeBindings bindings →
      Infer κ F' Ψ c e Ψ' T output ty → CtxBelow Ψ c → (∀ k ∈ κ, k < Ψ) →
      (∀ t ∈ F', Ty.BelowFvars Ψ t) → Ty.BelowFvars Ψ' ty ∧ ∀ p ∈ T, Ty.BelowFvars Ψ' p.2)
    (hctx : CtxBelow frontier ctx) (hK : ∀ k ∈ K, k < frontier)
    (hF : ∀ t ∈ F, Ty.BelowFvars frontier t) (hstate : state.Below frontier)
    (hbindings : ∀ binding ∈ bindings, ∀ v ∈ binding.ann.rigidVars, v < frontier) :
    (∀ p ∈ S, Ty.BelowFvars next p.2) ∧ final.Below next := by
  match h with
  | .nil => exact ⟨by simp, hstate⟩
  | .skip _ hr =>
      exact hr.belowFvars_of_infer (fun he h => hInfer (by simp only [sizeBindings]; omega) h)
        hctx hK hF hstate (fun binding hb => hbindings binding (List.mem_cons_of_mem _ hb))
  | .cons _ _ hi hu _ hr =>
      expose_names
      have hle := Infer.frontier_le hi
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
          ((Ty.BelowFvars.of_freeVars_lt
            (hbindings _ List.mem_cons_self)).mono hbase))
          (fun v hv => Nat.lt_of_lt_of_le (freshVars_lt v hv) hle)
      have huS := hu.unifies.belowFvars hiTy hexpected
      have hboth : ∀ p ∈ s1 ++ s2, Ty.BelowFvars first p.2 :=
        fun p hp => (List.mem_append.mp hp).elim (hiS p) (huS p)
      obtain ⟨htail, hfinal⟩ := hr.belowFvars_of_infer
        (fun he h => hInfer (by simp only [sizeBindings_substInputBindings] at he; simp only [sizeBindings]; omega) h)
        (Subst.onCtx_below hboth hbase hctx)
        (fun k hk => Nat.lt_of_lt_of_le (hK k hk) hbase)
        (substSoft_below hboth hbase hF) ((hstate.onSubst hboth hbase).setSigned)
        (bindings_below_subst
          (fun binding hb => hbindings binding (List.mem_cons_of_mem _ hb)) hboth hbase)
      exact ⟨fun p hp => (List.mem_append.mp hp).elim (fun hp => (hboth p hp).mono hrle) (htail p), hfinal⟩
 termination_by structural h

mutual
private theorem InferCert.belowFvars_raw (h : Infer K F frontier ctx input next subst output ty) :
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
    obtain ⟨hbTy, hbSubst⟩ := hb.belowFvars_raw (by
      intro M hM
      rcases List.mem_cons.mp hM with rfl | hM
      · exact hparam
      · exact (hctx M hM).mono hle)
      (fun k hk => Nat.lt_of_lt_of_le (hK k hk) hle)
      (fun t ht => (hF t ht).mono hle)
    exact ⟨.arrow (Subst.onTy_belowFvars hbSubst (hparam.mono (Infer.frontier_le hb))) hbTy, hbSubst⟩
  | .app _ hf ha hu =>
    intro hctx hK hF
    have hfLe := Infer.frontier_le hf
    have haLe := Infer.frontier_le ha
    obtain ⟨hfTy, hfSubst⟩ := hf.belowFvars_raw hctx hK hF
    obtain ⟨haTy, haSubst⟩ := ha.belowFvars_raw (Subst.onCtx_below hfSubst hfLe hctx)
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
  | @InferCert.letIn K F ann rhs body frontier ctx
      ⟨first, s1, rhsOut, rhsTy⟩ ⟨checked, sCheck⟩ ⟨next, s2, bodyOut, bodyTy⟩
      _ hr hc hb =>
    intro hctx hK hF
    have hrLe := Infer.frontier_le hr
    have hcLe := hc.frontier_le
    have hbLe := Infer.frontier_le hb
    obtain ⟨hrTy, hrSubst⟩ := hr.belowFvars_raw hctx hK hF
    have hFfirst := substSoft_below hrSubst hrLe hF
    have hcSubst := hc.belowFvars hrTy (fun k hk => Nat.lt_of_lt_of_le (hK k hk) hrLe) hFfirst
    have hcTy := Subst.onTy_belowFvars hcSubst (hrTy.mono hcLe)
    have hcheckedCtx := Subst.onCtx_below hcSubst hcLe
      (Subst.onCtx_below hrSubst hrLe hctx)
    obtain ⟨hbTy, hbSubst⟩ := hb.belowFvars_raw (by
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

  | @InferCert.letSignature K F ann rhs body written frontier ctx
      ⟨first, s1, rhsOut, rhsTy⟩ ⟨checked, sCheck⟩ ⟨next, s2, bodyOut, bodyTy⟩
      _ hprefix _ hr hc _ hb =>
    intro hctx hK hF
    dsimp only at hr hc hb
    have hrLe : frontier + ann.paramCount ≤ first := by
      simpa using Infer.frontier_le hr
    have hcLe : first ≤ checked := by
      simpa using hc.frontier_le
    have hbLe : checked ≤ next := by
      simpa using Infer.frontier_le hb
    obtain ⟨hrTy, hrSubst⟩ := hr.belowFvars_raw
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
    obtain ⟨hbTy, hbSubst⟩ := hb.belowFvars_raw (by
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
    obtain ⟨ht, hS1⟩ := hs.belowFvars_raw hctx hK hF
    have hle := Infer.frontier_le hs
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
  | @InferCert.letRec K F bindings body frontier ctx completed
      ⟨first, s1, state1⟩ ⟨second, s2, state2⟩ ⟨next, s3, bodyOut, bodyTy⟩
      hscope _ hstrata hsigned _ hbody =>
    intro hctx hK hF
    dsimp only at hstrata hsigned hbody
    have hbindings : ∀ binding ∈ bindings,
        ∀ v ∈ binding.ann.rigidVars, v < frontier := by
      intro binding hb v hv
      exact rigid_soft_lt hK hF v (hscope.1 v (by
        simp only [InferInput.rigidVars, List.mem_append]
        exact Or.inl (ann_rigid_mem hb hv)))
    have hseed : frontier ≤ frontier + bindings.length := by omega
    obtain ⟨hs1, hstate1⟩ := hstrata.belowFvars_of_infer
      (fun he hi => hi.belowFvars_raw)
      (fun M hm => (hctx M hm).mono hseed)
      (fun k hk => Nat.lt_of_lt_of_le (hK k hk) hseed)
      (fun t ht => (hF t ht).mono hseed)
      (RecState.Below.init hbindings)
      (fun binding hb v hv => Nat.lt_of_lt_of_le (hbindings binding hb v hv) hseed)
    have hle1 := hstrata.frontier_le
    have hle2 := hsigned.frontier_le
    have hle3 := Infer.frontier_le hbody
    have hbase1 : frontier ≤ first := by omega
    have hbase2 : frontier ≤ second := by omega
    obtain ⟨hs2, hstate2⟩ := hsigned.belowFvars_of_infer
      (fun he hi => hi.belowFvars_raw)
      (Subst.onCtx_below hs1 hbase1 hctx)
      (fun k hk => Nat.lt_of_lt_of_le (hK k hk) hbase1)
      (substSoft_below hs1 hbase1 hF) hstate1
      (bindings_below_subst hbindings hs1 hbase1)
    have hs12 : ∀ p ∈ s1 ++ s2, Ty.BelowFvars second p.2 :=
      fun p hp => (List.mem_append.mp hp).elim (fun hp => (hs1 p hp).mono hle2) (hs2 p)
    obtain ⟨hbodyTy, hs3⟩ := hbody.belowFvars_raw
      (hstate2.rhsCtx (Subst.onCtx_below hs12 hbase2 hctx))
      (fun k hk => Nat.lt_of_lt_of_le (hK k hk) hbase2)
      (substSoft_below hs12 hbase2 hF)
    exact ⟨hbodyTy, fun p hp => (List.mem_append.mp hp).elim (fun hp => (hs12 p hp).mono hle3) (hs3 p)⟩
termination_by (input.size, 0)
decreasing_by all_goals (simp only [InferInput.size, InferInput.size_openTyVars, InferInput.size_substTyFvars, sizeBranches_substInputBranches, sizeBindings_substInputBindings] at *; omega)

theorem InferBranches.belowFvars {Φ ctx scrutTy ρ brs Φ' S}
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
    obtain ⟨hτb, hS₁⟩ := InferCert.belowFvars_raw hbody
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
    obtain ⟨hτb, hS₁⟩ := InferCert.belowFvars_raw hbody hctx
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

theorem InferCert.belowFvars {request : InferRequest} {result : InferResult}
    (h : InferCert request result) (bounds : request.Bounds) :
    Ty.BelowFvars result.frontier result.ty ∧
      ∀ pair ∈ result.subst, Ty.BelowFvars result.frontier pair.2 := by
  cases request
  cases result
  exact InferCert.belowFvars_raw h bounds.ctxBelow bounds.protectedBelow bounds.softBelow

theorem Infer.belowFvars (h : Infer K F frontier ctx input next subst output ty) :
    CtxBelow frontier ctx → (∀ k ∈ K, k < frontier) →
    (∀ soft ∈ F, Ty.BelowFvars frontier soft) →
    Ty.BelowFvars next ty ∧ ∀ pair ∈ subst, Ty.BelowFvars next pair.2 :=
  InferCert.belowFvars_raw h


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
  | @letRec bindings K ctx body resultTy specs groups prefixes G L hg hw hp hG hscope hFits _ _ _ ihMono ihPoly ihBody =>
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
    have bindingsNil : substInputBindings [] bindings = bindings :=
      substInputBindings_eq_self_of_fixes bindings (fun _ _ => rfl)
    have hw' : RecSpecs.WF (bindings.map InputRecBinding.recMode) specs' W := by
      simpa only [bindingsNil] using RecSpecs.WF.subst_fresh_pool (S := []) hw (by simp) hWnd
    have hp' : RecPrefixesWF bindings specs' prefixes' W := by
      simpa only [bindingsNil] using hp.subst_fresh_pool (S := []) hWlen hWnd
    have hbindingsLen : bindings.length = specs.length := by
      simpa only [List.length_map] using hw.length
    have hpData := fun i hi => hp.get hbindingsLen (i := i) hi
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
      hg hw' hp' ?_ hscope ?_ ?_ ?_ ?_
    · intro w hw hm
      exact hWavoid w hw (by simp only [avoid, List.mem_append] at hm ⊢; tauto)
    · intro stage component hs Xs hf member hm binding names ty hbi hni hti
      rw [List.getElem?_map] at hni hti
      obtain ⟨names0, hn0, rfl⟩ := Option.map_eq_some_iff.mp hni
      obtain ⟨spec, ht0, heq⟩ := Option.map_eq_some_iff.mp hti
      cases spec with
      | poly scheme => cases heq
      | mono ty0 =>
        cases heq
        obtain ⟨_, _, hsub⟩ := hp.member member binding names0 hbi hn0
        change binding.ann.RecFits (recRenameNames W Xs (recRenameNames G W names0))
          (Ty.renameG W Xs (Ty.renameG G W ty0))
        rw [recRenameNames_composition hWlen (hf.length.trans hWlen) hWnd hsub,
          hsquare ty0 (List.mem_of_getElem? ht0) Xs hf]
        exact hFits stage component hs Xs (oldFresh Xs hf) member hm binding names0 ty0 hbi hn0 ht0
    · intro stage component hs Xs hf member hm binding names ty hbi hni hti
      rw [List.getElem?_map] at hni hti
      obtain ⟨names0, hn0, rfl⟩ := Option.map_eq_some_iff.mp hni
      obtain ⟨spec, ht0, heq⟩ := Option.map_eq_some_iff.mp hti
      cases spec with
      | poly scheme => cases heq
      | mono ty0 =>
        cases heq
        obtain ⟨_, _, hsub⟩ := hp.member member binding names0 hbi hn0
        change InputTyping (K ++ Xs)
          (recStageCtx { ctx with env := env' } specs' prefixes' (groups.take stage).flatten W Xs)
          (binding.rhs.openTyVars (recRenameNames W Xs (recRenameNames G W names0)))
          (Ty.renameG W Xs (Ty.renameG G W ty0))
        rw [recRenameNames_composition hWlen (hf.length.trans hWlen) hWnd hsub,
          hsquare ty0 (List.mem_of_getElem? ht0) Xs hf]
        have hc := ihMono stage component hs Xs (oldFresh Xs hf) member hm binding names0 ty0 hbi hn0 ht0
          (hextra (specs.mapIdx (recStageEntry prefixes (groups.take stage).flatten G Xs)))
        simpa only [recStageCtx, hstage Xs hf] using hc
    · intro member binding scheme hbi hsi Ys hy
      rw [List.getElem?_map] at hsi
      obtain ⟨spec, hs0, heq⟩ := Option.map_eq_some_iff.mp hsi
      cases spec with
      | mono ty => cases heq
      | poly scheme0 =>
        cases heq
        have hy0 : FreshNames L scheme0.paramCount Ys :=
          ⟨hy.length, hy.nodup, fun y hy' hl => hy.avoid y hy' (by simp only [L', List.mem_append]; tauto)⟩
        have hc := ihPoly member binding scheme0 hbi hs0 Ys hy0 (hextra (recCompletedSchemes specs prefixes G))
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

 theorem InferRecComponent.sourceLocality_of_infer
    (h : InferRecComponent K F members index frontier ctx bindings specs next S artifacts)
    (hInfer : ∀ {κ F' Ψ c e Ψ' T output ty}, e.size ≤ sizeBindings bindings →
      Infer κ F' Ψ c e Ψ' T output ty →
      ∀ {w}, w < Ψ →
      e.erase.ForallOuter (fun i => ∀ M, c.env[i]? = some M → w ∉ M.body.freeVars) 0 →
      w ∉ e.rigidVars →
      (∀ p ∈ T, w ∉ p.2.freeVars) ∧ w ∉ ty.freeVars ∧ w ∉ T.map Prod.fst) :
    ∀ {w}, w < frontier →
    (∀ j binding, index + j ∈ members → bindings[j]? = some binding →
      binding.rhs.erase.ForallOuter
        (fun i => ∀ M, ctx.env[i]? = some M → w ∉ M.body.freeVars) 0 ∧
        w ∉ binding.rhs.rigidVars) →
    (∀ j ty, index + j ∈ members → specs[j]? = some (.mono ty) → w ∉ ty.freeVars) →
    (∀ p ∈ S, w ∉ p.2.freeVars) ∧ w ∉ S.map Prod.fst := by
  match h with
  | .nil => intro w _ _ _; exact ⟨by simp, by simp⟩
  | .consSelected hsel hi hu hrest =>
    intro w hw hrefs htargets
    expose_names
    have hrhs := hrefs 0 binding (by simpa using hsel) rfl
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
    have hrestRefs : ∀ j binding', index + 1 + j ∈ members →
        (substInputBindings (s1 ++ s2) rest)[j]? = some binding' →
        binding'.rhs.erase.ForallOuter
          (fun i => ∀ M, (s2.onCtx (s1.onCtx ctx)).env[i]? = some M → w ∉ M.body.freeVars) 0 ∧
          w ∉ binding'.rhs.rigidVars := by
      intro j binding' hj hget
      rw [substInputBindings_eq_map, List.getElem?_map] at hget
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
        simp only [sizeBindings_substInputBindings] at he
        simp only [sizeBindings]; omega) h)
      (Nat.lt_of_lt_of_le hw (Infer.frontier_le hi)) hrestRefs hrestTargets
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

private theorem RecSpec.monoEntry_avoids {spec : RecSpec}
    (h : w ∉ spec.freeVars) : w ∉ spec.monoEntry.body.freeVars := by
  cases spec <;> exact h

private theorem RecSpec.completedScheme_avoids {spec : RecSpec}
    (h : w ∉ spec.freeVars) :
    w ∉ (spec.completedScheme written pool).body.freeVars := by
  cases spec with
  | mono ty => exact fun hv => h (Ty.freeVars_closeOver_subset hv)
  | poly scheme => exact h

theorem RecState.Avoids.init {bindings : List InputRecBinding} (hw : w < base)
    (hbindings : ∀ binding ∈ bindings, w ∉ binding.ann.rigidVars) :
    (RecState.init base bindings).Avoids w := by
  have hmode : ∀ scheme,
      some scheme ∈ bindings.map (fun binding => binding.ann.recModeAnn) →
      w ∉ scheme.body.freeVars := by
    intro scheme hs
    obtain ⟨binding, hb, heq⟩ := List.mem_map.mp hs
    cases hann : binding.ann with
    | absent | template | partialForall =>
      simp only [hann, BindingAnn.recModeAnn, reduceCtorEq] at heq
    | complete original =>
      simp only [hann, BindingAnn.recModeAnn, Option.some.injEq] at heq
      subst scheme
      simpa only [hann, BindingAnn.rigidVars] using hbindings binding hb
  rw [RecState.Avoids, RecState.init_specs, RecState.init_exports]
  constructor
  · intro spec hs
    rcases RecSpec.mem_init hs with ⟨m, hlo, _, rfl⟩ | ⟨scheme, hsigma, rfl⟩
    · simp only [RecSpec.freeVars, Ty.freeVars, List.mem_singleton]
      omega
    · exact hmode scheme (by
        simpa only [InputRecBinding.map_recMode_ann] using hsigma)
  · intro scheme hs
    obtain ⟨old, ho, heq⟩ := List.mem_filterMap.mp hs
    exact hmode scheme (heq ▸ ho)

theorem RecState.Avoids.onSubst {state : RecState} (h : state.Avoids w)
    (hS : ∀ p ∈ S, w ∉ p.2.freeVars) : (state.onSubst S).Avoids w := by
  rw [RecState.Avoids, RecState.specs_onSubst, RecState.exports_onSubst]
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
    (state.installOpenings members openings).Avoids w := by
  simpa only [RecState.Avoids, RecState.specs_installOpenings,
    RecState.exports_installOpenings] using h

theorem RecState.Avoids.setSigned {state : RecState} {member : Nat} {names : List Nat}
    {output : Expr} {facts : RecFacts} (h : state.Avoids w) :
    (state.setSigned member names output facts).Avoids w := by
  simpa only [RecState.Avoids, RecState.specs_setSigned,
    RecState.exports_setSigned] using h

theorem RecState.Avoids.entries {state : RecState} (h : state.Avoids w) :
    ∀ scheme ∈ state.entries, w ∉ scheme.body.freeVars := by
  intro scheme hs
  obtain ⟨member, hmember, rfl⟩ := List.mem_map.mp hs
  have hspec : member.spec ∈ state.specs :=
    List.mem_map.mpr ⟨member, hmember, rfl⟩
  cases he : member.exported with
  | none =>
    simp only [Option.getD_none]
    exact RecSpec.monoEntry_avoids (h.1 member.spec hspec)
  | some sigma =>
    simp only [Option.getD_some]
    exact h.exported (List.mem_map.mpr ⟨member, hmember, he⟩)

theorem RecState.Avoids.rhsCtx {state : RecState} {e : Expr} {groupSize : Nat} {ctx : Ctx} (h : state.Avoids w)
    (hlen : state.entries.length = groupSize)
    (href : e.ForallOuter (fun i => ∀ M, ctx.env[i]? = some M → w ∉ M.body.freeVars) groupSize) :
    e.ForallOuter (fun i => ∀ M, (state.rhsCtx ctx).env[i]? = some M → w ∉ M.body.freeVars) 0 := by
  exact Expr.ForallOuter.lookupAvoid_prepend (pre := state.entries)
    (by simpa only [Nat.zero_add, hlen] using href) h.entries

theorem RecState.Avoids.exportComponent {state : RecState} {members pool : List Nat}
    {written : List (List Nat)} {artifacts : List (Option RecComponentArtifact)}
    (h : state.Avoids w) :
    (state.exportComponent members written pool artifacts).Avoids w := by
  refine ⟨?_, ?_⟩
  · simpa only [RecState.specs_exportComponent] using h.1
  intro scheme hs
  obtain ⟨old, hold, heq⟩ := List.mem_filterMap.mp hs
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hold
  rw [RecState.getElem?_exports_exportComponent] at hi
  cases hmember : state.memberStates[i]? with
  | none => simp [hmember] at hi
  | some member =>
      have hmember_mem : member ∈ state.memberStates := List.mem_of_getElem? hmember
      have hspec : member.spec ∈ state.specs :=
        List.mem_map.mpr ⟨member, hmember_mem, rfl⟩
      by_cases hselected : i ∈ members
      · simp only [hmember, Option.map_some, hselected, if_pos] at hi
        have hcompleted : some (member.spec.completedScheme (written[i]?.getD []) pool) =
            some scheme := (Option.some.inj hi).trans heq
        cases Option.some.inj hcompleted
        exact RecSpec.completedScheme_avoids (h.1 member.spec hspec)
      · simp only [hmember, Option.map_some, hselected] at hi
        have hmemberExport : member.exported = some scheme := (Option.some.inj hi).trans heq
        exact h.exported (List.mem_map.mpr ⟨member, hmember_mem, hmemberExport⟩)

theorem FinishRecComponent.avoids (h : FinishRecComponent K soft members ctx state artifacts final)
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
    (hw : w < frontier) (ha : ∀ binding ∈ anns, w ∉ binding.ann.rigidVars) :
    ∀ opening ∈ openings, ∀ ty, opening.expected = some ty → w ∉ ty.freeVars := by
  induction h with
  | nil => intro opening hm; cases hm
  | skip _ _ ih =>
    intro opening hm ty he
    rcases List.mem_cons.mp hm with rfl | hm
    · cases he
    · exact ih hw (fun binding hm => ha binding (List.mem_cons_of_mem _ hm)) opening hm ty he
  | cons _ hh ht ih =>
    intro opening hm ty he
    rcases List.mem_cons.mp hm with rfl | hm
    · exact hh.expected_avoid hw (ha _ List.mem_cons_self) he
    · exact ih (Nat.lt_of_lt_of_le hw hh.frontier_le)
        (fun binding hm => ha binding (List.mem_cons_of_mem _ hm)) opening hm ty he

private theorem openRecSources_locality {openings : List RecOpening} {bindings : List InputRecBinding}
    (ho : ∀ opening ∈ openings, w ∉ opening.written)
    (hr : ∀ binding ∈ bindings,
      binding.rhs.erase.ForallOuter P depth ∧ w ∉ binding.rhs.rigidVars) :
    ∀ binding ∈ openRecSources openings bindings,
      binding.rhs.erase.ForallOuter P depth ∧ w ∉ binding.rhs.rigidVars := by
  induction bindings generalizing openings with
  | nil => cases openings <;> intro binding hm <;> cases hm
  | cons binding rest ih =>
    cases openings with
    | nil => exact hr
    | cons opening openings =>
      intro source hs
      rcases List.mem_cons.mp hs with rfl | hs
      · refine ⟨by simpa only [InferInput.erase_openTyVars] using
          (hr binding List.mem_cons_self).1, ?_⟩
        intro hv
        exact (InferInput.rigidVars_openTyVarsFrom hv).elim
          (hr binding List.mem_cons_self).2 (ho opening List.mem_cons_self)
      · exact ih (fun opening ho' => ho opening (List.mem_cons_of_mem _ ho'))
          (fun binding hr' => hr binding (List.mem_cons_of_mem _ hr')) source hs

private theorem recShapes_avoid {state : RecState} (ha : state.Avoids w)
    (ho : ∀ opening ∈ openings, ∀ ty, opening.expected = some ty → w ∉ ty.freeVars) :
    ∀ shape ∈ state.shapes members openings, w ∉ shape.1.freeVars ∧
      ∀ ty, shape.2 = some ty → w ∉ ty.freeVars := by
  intro shape hs
  obtain ⟨i, _, heq⟩ := List.mem_filterMap.mp hs
  cases hmember : state.memberStates[i]? with
  | none => simp [hmember] at heq
  | some member =>
    have hmember_mem : member ∈ state.memberStates := List.mem_of_getElem? hmember
    cases hspec : member.spec with
    | poly scheme => simp [hmember, hspec, RecSpec.monoTy?] at heq
    | mono ty =>
      cases hopen : openings[i]? with
      | none => simp [hmember, RecSpec.monoTy?, hopen] at heq
      | some opening =>
        simp [hmember, hspec, RecSpec.monoTy?, hopen] at heq
        cases heq
        exact ⟨ha.1 _ (List.mem_map.mpr ⟨member, hmember_mem, hspec⟩),
          ho opening (List.mem_of_getElem? hopen)⟩

private theorem FinishRecComponent.memberStates_length
    (h : FinishRecComponent K soft members ctx state artifacts final) :
    final.memberStates.length = state.memberStates.length := by
  cases h
  simp [RecState.exportComponent]


 theorem InferRecStrata.sourceLocality_of_infer
    (h : InferRecStrata K F frontier ctx bindings state groups next S final)
    (hInfer : ∀ {κ F' Ψ c e Ψ' T output ty}, e.size ≤ sizeBindings bindings →
      Infer κ F' Ψ c e Ψ' T output ty →
      ∀ {w}, w < Ψ →
      e.erase.ForallOuter (fun i => ∀ M, c.env[i]? = some M → w ∉ M.body.freeVars) 0 →
      w ∉ e.rigidVars →
      (∀ p ∈ T, w ∉ p.2.freeVars) ∧ w ∉ ty.freeVars ∧ w ∉ T.map Prod.fst)
    (hw : w < frontier) (ha : state.Avoids w)
    (hlen : state.memberStates.length = bindings.length)
    (hbindings : ∀ binding ∈ bindings, w ∉ binding.ann.rigidVars)
    (hrhs : ∀ binding ∈ bindings, binding.rhs.erase.ForallOuter
      (fun i => ∀ M, ctx.env[i]? = some M → w ∉ M.body.freeVars) bindings.length ∧
      w ∉ binding.rhs.rigidVars) :
    (∀ p ∈ S, w ∉ p.2.freeVars) ∧ w ∉ S.map Prod.fst ∧ final.Avoids w := by
  match h with
  | .nil => exact ⟨by simp, by simp, ha⟩
  | .cons ho hp hc hf hr =>
    expose_names
    have hpre := hp.sourceAvoid
      (recShapes_avoid ha.installOpenings (ho.expected_avoid hw hbindings))
    have hapre : ((state.installOpenings component openings).onSubst pre).Avoids w :=
      ha.installOpenings.onSubst hpre.1
    have hentry : (((state.installOpenings component openings).onSubst pre).entries).length = bindings.length := by
      simpa [RecState.entries, RecState.onSubst, RecState.installOpenings] using hlen
    have hopen : ∀ binding ∈ openRecSources openings bindings,
        binding.rhs.erase.ForallOuter
          (fun i => ∀ M, ctx.env[i]? = some M → w ∉ M.body.freeVars) bindings.length ∧
        w ∉ binding.rhs.rigidVars :=
      openRecSources_locality (fun opening hm hv => by
        have hh := ho.written_range w (List.mem_flatMap.mpr ⟨opening, hm, hv⟩)
        omega) hrhs
    have hcomponent := hc.sourceLocality_of_infer
      (fun he hi => hInfer (by simpa only [sizeBindings_substInputBindings, sizeBindings_openRecSources] using he) hi)
      (Nat.lt_of_lt_of_le hw ho.frontier_le)
      (by
        intro j binding _ hget
        rw [substInputBindings_eq_map, List.getElem?_map] at hget
        obtain ⟨old, hold, rfl⟩ := Option.map_eq_some_iff.mp hget
        have hh := hopen old (List.mem_of_getElem? hold)
        refine ⟨?_, InferInput.avoid_subst hpre.1 hh.2⟩
        exact hapre.rhsCtx hentry (by simpa only [InferInput.erase_substTyFvars] using
          Expr.ForallOuter.lookupAvoid_onSubst hh.1 hpre.1))
      (by intro j ty _ hget; exact hapre.1 _ (List.mem_of_getElem? hget))
    have hboth : ∀ p ∈ pre ++ current, w ∉ p.2.freeVars :=
      fun p hm => (List.mem_append.mp hm).elim (hpre.1 p) (hcomponent.1 p)
    have hafinal := hf.avoids (ha.installOpenings.onSubst hboth)
    have htailLength : exported.memberStates.length =
        (substInputBindings (pre ++ current) bindings).length := by
      simpa [substInputBindings_eq_map, RecState.onSubst, RecState.installOpenings] using
        hf.memberStates_length.trans
          (by simpa [RecState.onSubst, RecState.installOpenings] using hlen)
    obtain ⟨htS, htD, htA⟩ := hr.sourceLocality_of_infer
      (fun he hi => hInfer (by simpa only [sizeBindings_substInputBindings] using he) hi)
      (Nat.lt_of_lt_of_le hw (ho.frontier_le.trans hc.frontier_le)) hafinal htailLength
      (by
        intro binding hm
        rw [substInputBindings_eq_map] at hm
        obtain ⟨old, hold, rfl⟩ := List.mem_map.mp hm
        exact BindingAnn.avoid_subst hboth (hbindings old hold))
      (by
        intro binding hm
        rw [substInputBindings_eq_map] at hm
        obtain ⟨old, hold, rfl⟩ := List.mem_map.mp hm
        have hh := hrhs old hold
        exact ⟨by simpa only [InferInput.erase_substTyFvars,
            substInputBindings_eq_map, List.length_map] using
          Expr.ForallOuter.lookupAvoid_onSubst hh.1 hboth, InferInput.avoid_subst hboth hh.2⟩)
    refine ⟨fun p hp => (List.mem_append.mp hp).elim (hboth p) (htS p), ?_, htA⟩
    simpa only [List.map_append, List.mem_append, not_or] using And.intro (And.intro hpre.2 hcomponent.2) htD
 termination_by structural h

 theorem InferRecSigned.sourceLocality_of_infer
    (h : InferRecSigned K F index frontier ctx bindings state next S final)
    (hInfer : ∀ {κ F' Ψ c e Ψ' T output ty}, e.size ≤ sizeBindings bindings →
      Infer κ F' Ψ c e Ψ' T output ty →
      ∀ {w}, w < Ψ →
      e.erase.ForallOuter (fun i => ∀ M, c.env[i]? = some M → w ∉ M.body.freeVars) 0 →
      w ∉ e.rigidVars →
      (∀ p ∈ T, w ∉ p.2.freeVars) ∧ w ∉ ty.freeVars ∧ w ∉ T.map Prod.fst)
    (hw : w < frontier) (ha : state.Avoids w)
    (groupSize : Nat) (hlen : state.memberStates.length = groupSize)
    (hbindings : ∀ binding ∈ bindings, w ∉ binding.ann.rigidVars)
    (hrhs : ∀ binding ∈ bindings, binding.rhs.erase.ForallOuter
      (fun i => ∀ M, ctx.env[i]? = some M → w ∉ M.body.freeVars) groupSize ∧
      w ∉ binding.rhs.rigidVars) :
    (∀ p ∈ S, w ∉ p.2.freeVars) ∧ w ∉ S.map Prod.fst ∧ final.Avoids w := by
  match h with
  | .nil => exact ⟨by simp, by simp, ha⟩
  | .skip _ hr =>
    exact hr.sourceLocality_of_infer
      (fun he hi => hInfer (by simp only [sizeBindings]; omega) hi) hw ha groupSize hlen
      (fun binding hm => hbindings binding (List.mem_cons_of_mem _ hm))
      (fun binding hm => hrhs binding (List.mem_cons_of_mem _ hm))
  | .cons _ _ hi hu _ hr =>
    expose_names
    have hy : w ∉ freshVars frontier scheme.paramCount := fun hm => by
      have := freshVars_ge w hm; omega
    have hhead := hrhs { ann := .complete scheme, rhs := rhs } List.mem_cons_self
    have hentry : state.entries.length = groupSize := by
      simpa [RecState.entries] using hlen
    obtain ⟨hfirstS, hfirstTy, hfirstD⟩ := hInfer
      (by simp only [InferInput.size_openTyVars, sizeBindings]; omega) hi (by omega)
      (by simpa only [InferInput.erase_openTyVars] using ha.rhsCtx hentry hhead.1)
      (fun hv => (InferInput.rigidVars_openTyVarsFrom hv).elim hhead.2 hy)
    have hexpected : w ∉ ((s1.onPolyTy scheme).openVars (freshVars frontier scheme.paramCount)).freeVars := by
      intro hv
      exact (Ty.freeVars_openVars_subset w hv).elim
        (Subst.notMemOnTy hfirstS
          (hbindings { ann := .complete scheme, rhs := rhs } List.mem_cons_self)) hy
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
        simp only [sizeBindings_substInputBindings] at he
        simp only [sizeBindings]
        omega) hh)
      (by have := Infer.frontier_le hi; omega) hanext groupSize
      (by simpa [RecState.setSigned, RecState.onSubst] using hlen)
      (by
        intro binding hm
        rw [substInputBindings_eq_map] at hm
        obtain ⟨old, hold, rfl⟩ := List.mem_map.mp hm
        exact BindingAnn.avoid_subst hboth
          (hbindings old (List.mem_cons_of_mem _ hold)))
      (by
        intro binding hm
        rw [substInputBindings_eq_map] at hm
        obtain ⟨old, hold, rfl⟩ := List.mem_map.mp hm
        have hh := hrhs old (List.mem_cons_of_mem _ hold)
        exact ⟨by simpa only [InferInput.erase_substTyFvars] using
          Expr.ForallOuter.lookupAvoid_onSubst hh.1 hboth,
          InferInput.avoid_subst hboth hh.2⟩)
    refine ⟨fun p hp => (List.mem_append.mp hp).elim (hboth p) (htS p), ?_, htA⟩
    simpa only [List.map_append, List.mem_append, not_or] using And.intro (And.intro hfirstD hsecondD) htD
 termination_by structural h


private theorem mem_eraseBindings {bindings : List InputRecBinding}
    {binding : InputRecBinding} (hr : binding ∈ bindings) :
    ({ ann := none, rhs := binding.rhs.erase } : CoreRecBinding) ∈ eraseBindings bindings :=
  erase_rhs_mem hr

private theorem rigidBindingVars_mem {bindings : List InputRecBinding}
    {binding : InputRecBinding} {v : Nat}
    (hr : binding ∈ bindings) (hv : v ∈ binding.rhs.rigidVars) :
    v ∈ rigidBindingVars bindings :=
  rhs_rigid_mem hr hv

 theorem InferRecStrata.memberStates_length
    (h : InferRecStrata K F frontier ctx bindings state groups next S final) :
    final.memberStates.length = state.memberStates.length := by
  match h with
  | .nil => rfl
  | .cons _ _ _ hf hr =>
    exact hr.memberStates_length.trans
      (hf.memberStates_length.trans (by simp [RecState.onSubst, RecState.installOpenings]))
 termination_by structural h

 theorem InferRecSigned.memberStates_length
    (h : InferRecSigned K F index frontier ctx bindings state next S final) :
    final.memberStates.length = state.memberStates.length := by
  match h with
  | .nil => rfl
  | .skip _ hr => exact hr.memberStates_length
  | .cons _ _ _ _ _ hr =>
    exact hr.memberStates_length.trans (by simp [RecState.onSubst, RecState.setSigned])
 termination_by structural h

mutual
 private theorem InferCert.sourceLocality_raw (h : Infer K F frontier ctx input next subst output ty) :
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
    obtain ⟨hS, hty, hD⟩ := hb.sourceLocality_raw (Nat.lt_of_lt_of_le hw hs.frontier_le) hbrefs hwe.2
    exact ⟨hS, by simpa only [Ty.freeVars, List.mem_dedup, List.mem_append, not_or]
      using And.intro (Subst.notMemOnTy hS hp) hty, hD⟩
  | @InferCert.app _ _ _ _ _ _ _ argumentResult _ _ hf ha hu =>
    intro w hw hrefs hwe
    expose_names
    simp only [InferInput.erase, Expr.ForallOuter, Expr.rec_strong] at hrefs
    simp only [InferInput.rigidVars, List.mem_append, not_or] at hwe
    obtain ⟨hfS, hfTy, hfD⟩ := hf.sourceLocality_raw hw hrefs.1 hwe.1
    obtain ⟨haS, haTy, haD⟩ := ha.sourceLocality_raw (Nat.lt_of_lt_of_le hw (Infer.frontier_le hf))
      (by simpa only [InferInput.erase_substTyFvars] using Expr.ForallOuter.lookupAvoid_onSubst hrefs.2 hfS)
      (InferInput.avoid_subst hfS hwe.2)
    have hnew : w ∉ (Ty.fvar argumentResult.frontier).freeVars := by
      simp only [Ty.freeVars, List.mem_singleton];
      have := Infer.frontier_le hf; have := Infer.frontier_le ha; omega
    have huA := UnifyRel.sourceAvoid_local hu.unifies (Subst.notMemOnTy haS hfTy)
      (by simpa only [Ty.freeVars, List.mem_dedup, List.mem_append, not_or] using And.intro haTy hnew)
    have hA := Subst.sourceAvoid_append_local (Subst.sourceAvoid_append_local ⟨hfS, hfD⟩ ⟨haS, haD⟩) huA
    exact ⟨hA.1, Subst.notMemOnTy huA.1 hnew, hA.2⟩
  | @InferCert.letIn K F ann rhs body frontier ctx
      ⟨first, s1, rhsOut, rhsTy⟩ ⟨checked, sCheck⟩ ⟨next, s2, bodyOut, bodyTy⟩
      _ hr hc hb =>
    intro w hw hrefs hwe
    expose_names
    simp only [InferInput.erase, Expr.ForallOuter, Expr.rec_strong, Nat.zero_add] at hrefs
    simp only [InferInput.rigidVars, List.mem_append, not_or] at hwe
    obtain ⟨hrS, hrTy, hrD⟩ := hr.sourceLocality_raw hw hrefs.1 hwe.1.2
    have hcA := hc.sourceAvoid (Nat.lt_of_lt_of_le hw (Infer.frontier_le hr)) hrTy
      (BindingAnn.avoid_subst hrS hwe.1.1)
    have hA := Subst.sourceAvoid_append_local ⟨hrS, hrD⟩ hcA
    have hfinalTy := Subst.notMemOnTy hcA.1 hrTy
    have hp : w ∉ (genScheme (K ++ softVars (substSoft (s1 ++ sCheck) F))
      (sCheck.onCtx (s1.onCtx ctx)).env (sCheck.onTy rhsTy)).body.freeVars :=
      fun hm => hfinalTy (Ty.freeVars_closeOver_subset hm)
    have hbrefs := Expr.ForallOuter.lookupAvoid_prepend (pre := [genScheme _ _ _])
      (Expr.ForallOuter.lookupAvoid_onSubst (Expr.ForallOuter.lookupAvoid_onSubst hrefs.2 hrS) hcA.1)
      (by intro M hM; rcases List.mem_singleton.mp hM with rfl; exact hp)
    obtain ⟨hbS, hbTy, hbD⟩ := hb.sourceLocality_raw
      (Nat.lt_of_lt_of_le hw ((Infer.frontier_le hr).trans hc.frontier_le))
      (by simpa only [InferInput.erase_substTyFvars] using hbrefs) (InferInput.avoid_subst hA.1 hwe.2)
    have hAll := Subst.sourceAvoid_append_local hA ⟨hbS, hbD⟩
    exact ⟨hAll.1, hbTy, hAll.2⟩
  | @InferCert.letSignature K F ann rhs body written frontier ctx
      ⟨first, s1, rhsOut, rhsTy⟩ ⟨checked, sCheck⟩ ⟨next, s2, bodyOut, bodyTy⟩
      _ heq _ hr hc _ hb =>
    intro w hw hrefs hwe
    expose_names
    subst written
    dsimp only at hr hc hb
    simp only [InferInput.erase, Expr.ForallOuter, Expr.rec_strong, Nat.zero_add] at hrefs
    simp only [InferInput.rigidVars, List.mem_append, not_or] at hwe
    have hwr : w ∉ freshVars frontier ann.paramCount := fun hm => by have := freshVars_ge w hm; omega
    have hrLe : frontier + ann.paramCount ≤ first := by
      simpa using Infer.frontier_le hr
    have hcLe : first ≤ checked := by
      simpa using hc.frontier_le
    obtain ⟨hrS, hrTy, hrD⟩ := hr.sourceLocality_raw (by omega)
      (by simpa only [InferInput.erase_openTyVars] using hrefs.1)
      (fun hm => (InferInput.rigidVars_openTyVarsFrom hm).elim hwe.1.2 hwr)
    have hcA := hc.sourceAvoid (Nat.lt_of_lt_of_le hw (by omega)) hrTy
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
    obtain ⟨hbS, hbTy, hbD⟩ := hb.sourceLocality_raw
      (Nat.lt_of_lt_of_le hw (by omega))
      (by simpa only [InferInput.erase_substTyFvars] using hbrefs) (InferInput.avoid_subst hA.1 hwe.2)
    have hAll := Subst.sourceAvoid_append_local hA ⟨hbS, hbD⟩
    exact ⟨hAll.1, hbTy, hAll.2⟩
  | @InferCert.letRec K F bindings body frontier ctx completed
      ⟨first, s1, state1⟩ ⟨second, s2, state2⟩ ⟨next, s3, bodyOut, bodyTy⟩
      _ _ hs hp _ hb =>
    intro w hw hrefs hwe
    dsimp only at hs hp hb
    simp only [InferInput.erase, Expr.ForallOuter, Expr.rec_strong,
      eraseBindings_length_local, Nat.zero_add] at hrefs
    simp only [InferInput.rigidVars, List.mem_append, not_or] at hwe
    have hbindings : ∀ binding ∈ bindings, w ∉ binding.ann.rigidVars :=
      fun binding hb hv => hwe.1 (ann_rigid_mem hb hv)
    have hrhs : ∀ binding ∈ bindings, binding.rhs.erase.ForallOuter
        (fun i => ∀ M, ctx.env[i]? = some M → w ∉ M.body.freeVars) bindings.length ∧
        w ∉ binding.rhs.rigidVars := by
      intro binding hb
      exact ⟨hrefs.1 { ann := none, rhs := binding.rhs.erase } (mem_eraseBindings hb),
        fun hv => hwe.1 (rigidBindingVars_mem hb hv)⟩
    obtain ⟨hsS, hsD, hstate1⟩ := hs.sourceLocality_of_infer (fun _ hi => hi.sourceLocality_raw)
      (by omega) (RecState.Avoids.init hw hbindings)
      (by simp [RecState.init]) hbindings hrhs
    have hs1len : state1.memberStates.length = bindings.length :=
      hs.memberStates_length.trans (by simp [RecState.init])
    obtain ⟨hpS, hpD, hstate2⟩ := hp.sourceLocality_of_infer (fun _ hi => hi.sourceLocality_raw)
      (by have := hs.frontier_le; omega) hstate1 bindings.length hs1len
      (by
        intro binding hm
        rw [substInputBindings_eq_map] at hm
        obtain ⟨old, ho, rfl⟩ := List.mem_map.mp hm
        exact BindingAnn.avoid_subst hsS (hbindings old ho))
      (by
        intro binding hm
        rw [substInputBindings_eq_map] at hm
        obtain ⟨old, ho, rfl⟩ := List.mem_map.mp hm
        exact ⟨by simpa only [InferInput.erase_substTyFvars] using
            Expr.ForallOuter.lookupAvoid_onSubst (hrhs old ho).1 hsS,
          InferInput.avoid_subst hsS (hrhs old ho).2⟩)
    have hpre := Subst.sourceAvoid_append_local ⟨hsS, hsD⟩ ⟨hpS, hpD⟩
    have hentries : state2.entries.length = bindings.length := by
      calc
        state2.entries.length = state2.memberStates.length := by simp [RecState.entries]
        _ = state1.memberStates.length := hp.memberStates_length
        _ = bindings.length := hs1len
    obtain ⟨hbS, hbTy, hbD⟩ := hb.sourceLocality_raw (show w < second from by have := hs.frontier_le; have := hp.frontier_le; omega)
      (by
        have hh := hstate2.rhsCtx hentries (Expr.ForallOuter.lookupAvoid_onSubst hrefs.2 hpre.1)
        simpa only [InferInput.erase_substTyFvars] using hh)
      (InferInput.avoid_subst hpre.1 hwe.2)
    have hAll := Subst.sourceAvoid_append_local hpre ⟨hbS, hbD⟩
    exact ⟨hAll.1, hbTy, hAll.2⟩
  | @InferCert.match_ K F scrut branches frontier ctx
      ⟨first, s1, scrutOut, scrutTy⟩ ⟨next, s2, branchesOut⟩ _ hs _ hb =>
    intro w hw hrefs hwe
    dsimp only at hs hb
    expose_names
    simp only [InferInput.erase, Expr.ForallOuter, Expr.rec_strong, Nat.zero_add] at hrefs
    simp only [InferInput.rigidVars, List.mem_append, not_or] at hwe
    obtain ⟨hsS, hsTy, hsD⟩ := hs.sourceLocality_raw hw hrefs.1 hwe.1
    have hnew : w ∉ (Ty.fvar first).freeVars := by
      simp only [Ty.freeVars, List.mem_singleton]; have := Infer.frontier_le hs; omega
    obtain ⟨hbS, hbTy, hbD⟩ := hb.sourceLocality (by have := Infer.frontier_le hs; omega)
      (branches_refs_subst (fun p b hm => hrefs.2 p b.erase (mem_eraseBranches hm)) hsS)
      hsTy hnew (branches_avoid_subst hsS hwe.2)
    have hA := Subst.sourceAvoid_append_local ⟨hsS, hsD⟩ ⟨hbS, hbD⟩
    exact ⟨hA.1, hbTy, hA.2⟩
 termination_by (input.size, 1)
 decreasing_by
  all_goals simp only [sizeBindings_substInputBindings] at *
  all_goals (simp only [InferInput.size, InferInput.size_substTyFvars, InferInput.size_openTyVars, sizeBranches_substInputBranches]; omega)

 theorem InferBranches.sourceLocality
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
    obtain ⟨hbS, hbTy, hbD⟩ := hb.sourceLocality_raw (by omega)
      (by simpa only [InferInput.erase_substTyFvars] using hbrefs) (InferInput.avoid_subst hA₀.1 hbrs.1)
    have hA₂ := UnifyRel.sourceAvoid_local hu.unifies hbTy
      (Subst.notMemOnTy hbS (Subst.notMemOnTy hA₀.1 hρ))
    have hApre := Subst.sourceAvoid_append_local (Subst.sourceAvoid_append_local hA₀ ⟨hbS,hbD⟩) hA₂
    obtain ⟨hrS, hrTy, hrD⟩ := hr.sourceLocality (by have := Infer.frontier_le hb; omega)
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
    obtain ⟨hbS, hbTy, hbD⟩ := hb.sourceLocality_raw hw
      (hrefs .wildcard body List.mem_cons_self) hbrs.1
    have hA₂ := UnifyRel.sourceAvoid_local hu.unifies hbTy (Subst.notMemOnTy hbS hρ)
    have hApre := Subst.sourceAvoid_append_local ⟨hbS,hbD⟩ hA₂
    obtain ⟨hrS, hrTy, hrD⟩ := hr.sourceLocality (Nat.lt_of_lt_of_le hw (Infer.frontier_le hb))
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

theorem InferCert.sourceLocality {request : InferRequest} {result : InferResult}
    (h : InferCert request result) {w : Nat} (hw : w < request.frontier)
    (hrefs : request.input.erase.ForallOuter
      (fun i => ∀ scheme, request.ctx.env[i]? = some scheme → w ∉ scheme.body.freeVars) 0)
    (hrigid : w ∉ request.input.rigidVars) :
    (∀ pair ∈ result.subst, w ∉ pair.2.freeVars) ∧
      w ∉ result.ty.freeVars ∧ w ∉ result.subst.map Prod.fst := by
  cases request
  cases result
  exact InferCert.sourceLocality_raw h hw hrefs hrigid

theorem Infer.sourceLocality (h : Infer K F frontier ctx input next subst output ty) :
    ∀ {w}, w < frontier →
    input.erase.ForallOuter
      (fun i => ∀ M, ctx.env[i]? = some M → w ∉ M.body.freeVars) 0 →
    w ∉ input.rigidVars →
    (∀ pair ∈ subst, w ∉ pair.2.freeVars) ∧ w ∉ ty.freeVars ∧ w ∉ subst.map Prod.fst :=
  InferCert.sourceLocality_raw h

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
    (h : state.Frame base K F ctx bindings done)
    (hpool : ∀ g ∈ state.pool, (∀ p ∈ S, g ∉ p.2.freeVars) ∧ g ∉ S.map Prod.fst)
    (hpending : ∀ i ty, state.specs[i]? = some (.mono ty) → i ∉ done →
      (∀ p ∈ S, base + i ∉ p.2.freeVars) ∧ base + i ∉ S.map Prod.fst) :
    (state.onSubst S).Frame base K (F.map S.onTy) (S.onCtx ctx)
      (substInputBindings S bindings) done := by
  have hdom : ∀ p ∈ S, p.1 ∉ state.pool := by
    intro p hp hg
    exact (hpool p.1 hg).2 (List.mem_map.mpr ⟨p, hp, rfl⟩)
  have hran : ∀ p ∈ S, ∀ g ∈ p.2.freeVars, g ∉ state.pool :=
    fun p hp g hg hgp => (hpool g hgp).1 p hp hg
  have hfix : ∀ g ∈ state.pool, S.onTy (.fvar g) = .fvar g := Subst.fixes_of_dom_avoids hdom
  refine {
    modes := ?_
    annInfo := ?_
    poly := ?_
    mono := ?_
    pending := ?_
    pool_nodup := h.pool_nodup
    pool_ctx := ?_
    pool_rigid := h.pool_rigid
    pool_soft := ?_
    pool_poly := ?_
    pool_pending := ?_
    rigid_below := h.rigid_below
    pending_soft := ?_ }
  · have hm : ((state.onSubst S).specs).map RecSpec.ann =
        (state.specs.map RecSpec.ann).map (Option.map S.onPolyTy) := by
      simp only [RecState.specs_onSubst, List.map_map]
      apply List.map_congr_left
      intro spec _
      cases spec <;> rfl
    rw [hm, h.modes]
    simp only [substInputBindings_eq_map, List.map_map, Function.comp_def,
      BindingAnn.recModeAnn_subst_source]
  · rw [RecState.annInfo_onSubst, h.annInfo]
    simp only [substInputBindings_eq_map, List.map_map, Function.comp_def,
      BindingAnn.recMemberAnnInfo_substTyFvars]
  · intro i scheme hget
    rw [RecState.specs_onSubst, List.getElem?_map] at hget
    obtain ⟨old, hold, heq⟩ := Option.map_eq_some_iff.mp hget
    cases old with
    | mono ty => cases heq
    | poly σ =>
      cases RecSpec.poly.inj heq
      simp only [RecState.exports_onSubst, List.getElem?_map, h.poly i σ hold, Option.map_some]
  · intro i ty hget
    rw [RecState.specs_onSubst, List.getElem?_map] at hget
    obtain ⟨old, hold, heq⟩ := Option.map_eq_some_iff.mp hget
    cases old with
    | poly scheme => cases heq
    | mono original =>
      cases RecSpec.mono.inj heq
      by_cases hi : i ∈ done
      · obtain ⟨written, hslots, hcount, hnd, hsub, hexport⟩ := if_pos hi ▸ h.mono i original hold
        rw [if_pos hi]
        refine ⟨written, ?_, ?_, hnd, hsub, ?_⟩
        · simp only [RecState.slots_onSubst, List.getElem?_map, hslots, Option.map_some, List.map_map]
          congr 1
          apply List.map_congr_left
          intro name hn
          exact hfix name (hsub name hn)
        · simpa only [RecState.recPrefixCountAt_onSubst] using hcount
        · simp only [RecState.exports_onSubst, List.getElem?_map, hexport, Option.map_some]
          exact congrArg (fun scheme => some (some scheme))
            (recScheme_subst_pool_avoid hdom hran hsub).symm
      · rw [if_neg hi]
        have he := if_neg hi ▸ h.mono i original hold
        simp only [RecState.exports_onSubst, List.getElem?_map, he, Option.map_some, Option.map_none]
  · simpa only [RecState.specs_onSubst] using
      h.pending.onSubst_source (fun _ hm => hm) hpending
  · intro g hg hm
    obtain ⟨scheme, hs, hv⟩ := Env.mem_freeVars_iff.mp hm
    obtain ⟨old, ho, rfl⟩ := List.mem_map.mp hs
    exact Subst.notMemOnTy (hpool g hg).1
      (fun hv => h.pool_ctx g hg (Env.mem_freeVars_iff.mpr ⟨old, ho, hv⟩)) hv
  · intro g hg
    exact soft_avoids_subst (h.pool_soft g hg) (hpool g hg).1
  · intro scheme ⟨i, hget⟩ g hg
    rw [RecState.specs_onSubst, List.getElem?_map] at hget
    obtain ⟨old, hold, heq⟩ := Option.map_eq_some_iff.mp hget
    cases old with
    | mono ty => cases heq
    | poly σ =>
      cases RecSpec.poly.inj heq
      exact Subst.notMemOnTy (hpool g hg).1 (h.pool_poly σ ⟨i, hold⟩ g hg)
  · intro i ty hget hi
    have hget' : (state.specs.map (RecSpec.onSubstSource S))[i]? = some (.mono ty) := by
      simpa only [RecState.specs_onSubst] using hget
    obtain ⟨old, hold, _⟩ := RecSpec.mono_getElem?_map_onSubstSource hget'
    exact h.pool_pending i old hold hi
  · intro i ty hget hi
    have hget' : (state.specs.map (RecSpec.onSubstSource S))[i]? = some (.mono ty) := by
      simpa only [RecState.specs_onSubst] using hget
    obtain ⟨old, hold, _⟩ := RecSpec.mono_getElem?_map_onSubstSource hget'
    exact soft_avoids_subst (h.pending_soft i old hold hi) (hpending i old hold hi).1


private theorem mem_eraseBranches_local {branches : List (MatchPattern × InferInput)}
    (h : (pat, body) ∈ branches) : (pat, body.erase) ∈ eraseBranches branches := by
  induction branches with
  | nil => cases h
  | cons head rest ih =>
    rcases List.mem_cons.mp h with hh | hh
    · cases hh; exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (ih hh)
private theorem mem_eraseBindings_local {bindings : List InputRecBinding}
    {binding : InputRecBinding} (h : binding ∈ bindings) :
    ({ ann := none, rhs := binding.rhs.erase } : CoreRecBinding) ∈ eraseBindings bindings :=
  erase_rhs_mem h

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
  | @letRec bindings K ctx body resultTy specs groups prefixes G L hg hw hp hG hscope hFits _ _ _ ihMono ihPoly ihBody =>
    intro env' hag
    simp only [InferInput.erase, Expr.ForallOuter, Expr.rec_strong,
      eraseBindings_length_local, Nat.zero_add] at hag
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
    have bindingsNil : substInputBindings [] bindings = bindings :=
      substInputBindings_eq_self_of_fixes bindings (fun _ _ => rfl)
    have hw' : RecSpecs.WF (bindings.map InputRecBinding.recMode) specs' W := by
      simpa only [bindingsNil] using RecSpecs.WF.subst_fresh_pool (S := []) hw (by simp) hWnd
    have hp' : RecPrefixesWF bindings specs' prefixes' W := by
      simpa only [bindingsNil] using hp.subst_fresh_pool (S := []) hWlen hWnd
    have hbindingsLen : bindings.length = specs.length := by
      simpa only [List.length_map] using hw.length
    have hpData := fun i hi => hp.get hbindingsLen (i := i) hi
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
      hg hw' hp' ?_ hscope ?_ ?_ ?_ ?_
    · intro w hw hm
      exact hWavoid w hw (by simp only [avoid, List.mem_append] at hm ⊢; tauto)
    · intro stage component hs Xs hf member hm binding names ty hbi hni hti
      rw [List.getElem?_map] at hni hti
      obtain ⟨names0, hn0, rfl⟩ := Option.map_eq_some_iff.mp hni
      obtain ⟨spec, ht0, heq⟩ := Option.map_eq_some_iff.mp hti
      cases spec with
      | poly scheme => cases heq
      | mono ty0 =>
        cases heq
        obtain ⟨_, _, hsub⟩ := hp.member member binding names0 hbi hn0
        change binding.ann.RecFits (recRenameNames W Xs (recRenameNames G W names0))
          (Ty.renameG W Xs (Ty.renameG G W ty0))
        rw [recRenameNames_composition hWlen (hf.length.trans hWlen) hWnd hsub,
          hsquare ty0 (List.mem_of_getElem? ht0) Xs hf]
        exact hFits stage component hs Xs (oldFresh Xs hf) member hm binding names0 ty0 hbi hn0 ht0
    · intro stage component hs Xs hf member hm binding names ty hbi hni hti
      rw [List.getElem?_map] at hni hti
      obtain ⟨names0, hn0, rfl⟩ := Option.map_eq_some_iff.mp hni
      obtain ⟨spec, ht0, heq⟩ := Option.map_eq_some_iff.mp hti
      cases spec with
      | poly scheme => cases heq
      | mono ty0 =>
        cases heq
        obtain ⟨_, _, hsub⟩ := hp.member member binding names0 hbi hn0
        change InputTyping (K ++ Xs)
          (recStageCtx { ctx with env := env' } specs' prefixes' (groups.take stage).flatten W Xs)
          (binding.rhs.openTyVars (recRenameNames W Xs (recRenameNames G W names0)))
          (Ty.renameG W Xs (Ty.renameG G W ty0))
        rw [recRenameNames_composition hWlen (hf.length.trans hWlen) hWnd hsub,
          hsquare ty0 (List.mem_of_getElem? ht0) Xs hf]
        have hc := ihMono stage component hs Xs (oldFresh Xs hf) member hm binding names0 ty0 hbi hn0 ht0
          ((specs.mapIdx (recStageEntry prefixes (groups.take stage).flatten G Xs)) ++ env') (by
            apply Expr.ForallOuter.prepend_env
            simpa only [InferInput.erase_openTyVars, List.length_mapIdx, Nat.zero_add, ← hw.length, List.length_map] using
              hag.1 { ann := none, rhs := binding.rhs.erase }
                (mem_eraseBindings_local (List.mem_of_getElem? hbi)))
        simpa only [recStageCtx, hstage Xs hf] using hc
    · intro member binding scheme hbi hsi Ys hy
      rw [List.getElem?_map] at hsi
      obtain ⟨spec, hs0, heq⟩ := Option.map_eq_some_iff.mp hsi
      cases spec with
      | mono ty => cases heq
      | poly scheme0 =>
        cases heq
        have hy0 : FreshNames L scheme0.paramCount Ys :=
          ⟨hy.length, hy.nodup, fun y hy' hl => hy.avoid y hy' (by simp only [L', List.mem_append]; tauto)⟩
        have hc := ihPoly member binding scheme0 hbi hs0 Ys hy0 ((recCompletedSchemes specs prefixes G) ++ env') (by
          apply Expr.ForallOuter.prepend_env
          simpa only [InferInput.erase_openTyVars, recCompletedSchemes, List.length_mapIdx, Nat.zero_add, ← hw.length, List.length_map] using
              hag.1 { ann := none, rhs := binding.rhs.erase }
                (mem_eraseBindings_local (List.mem_of_getElem? hbi)))
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
    {artifacts : List (Option RecComponentArtifact)} {pool : List Nat}
    (hlc : ∀ spec ∈ state.specs, spec.LC)
    (hclosed : ∀ i ∈ members, state.exports[i]? = some none)
    (hmono : ∀ i ∈ members, ∃ ty, state.specs[i]? = some (.mono ty)) :
    List.Forall₂ PolyTy.Generalizes
      (state.exportComponent members written pool artifacts).entries state.entries := by
  apply List.forall₂_iff_zip.mpr
  constructor
  · simp [RecState.entries, RecState.exportComponent]
  · intro newer older hpair
    obtain ⟨i, hget⟩ := List.mem_iff_getElem?.mp hpair
    obtain ⟨hnew, hold⟩ := List.getElem?_zip_eq_some.mp hget
    rw [RecState.entries, List.getElem?_map] at hold
    obtain ⟨member, hmember, heqOld⟩ := Option.map_eq_some_iff.mp hold
    have hmember_mem : member ∈ state.memberStates := List.mem_of_getElem? hmember
    have hspec : state.specs[i]? = some member.spec := by
      simp only [RecState.getElem?_specs, hmember, Option.map_some]
    have hexport : state.exports[i]? = some member.exported := by
      simp only [RecState.getElem?_exports, hmember, Option.map_some]
    rw [RecState.entries, RecState.exportComponent, List.getElem?_map,
      List.getElem?_mapIdx, hmember, Option.map_some] at hnew
    by_cases hi : i ∈ members
    · obtain ⟨ty, hty⟩ := hmono i hi
      have hspecEq : member.spec = .mono ty := Option.some.inj (hspec.symm.trans hty)
      have he : member.exported = none := Option.some.inj (hexport.symm.trans (hclosed i hi))
      simp only [hi, if_pos, hspecEq, RecSpec.completedScheme_mono] at hnew
      have heqNew : newer = recScheme (written[i]?.getD []) pool ty := Option.some.inj hnew.symm
      simp only [he, Option.getD_none, hspecEq, RecSpec.monoEntry] at heqOld
      rw [heqNew, ← heqOld]
      have htyLC : ty.IsLC := by
        simpa only [hspecEq] using
          (hlc member.spec (List.mem_map.mpr ⟨member, hmember_mem, rfl⟩))
      exact recScheme_generalizes_mono htyLC
    · simp only [hi] at hnew
      have heqNew : newer = older := Option.some.inj (hnew.symm.trans (congrArg some heqOld))
      rw [heqNew]
      exact PolyTy.Generalizes.refl older


/-- Completed RHSs are stored under their exact exported scheme and the
current full recursive environment. Metadata is intentionally absent. -/
def RecState.SourceTyped (ctx : Ctx) (state : RecState) : Prop :=
  ∀ (i : Nat) (scheme : PolyTy) (output : Expr),
    state.exports[i]? = some (some scheme) → state.outputs[i]? = some (some output) →
    scheme.WF ∧ ∃ L, GeneralisesTo TypeOfHM (state.rhsCtx ctx) (some scheme) output scheme L

@[simp] theorem RecState.entries_setSigned (state : RecState) (member : Nat)
    (names : List Nat) (output : Expr) (facts : RecFacts) :
    (state.setSigned member names output facts).entries = state.entries := by
  apply List.ext_getElem?
  intro i
  simp only [RecState.entries, RecState.setSigned, List.getElem?_map,
    List.getElem?_mapIdx]
  cases state.memberStates[i]? with
  | none => rfl
  | some old => split <;> rfl

@[simp] theorem RecState.entries_installOpenings (state : RecState) (members : List Nat)
    (openings : List RecOpening) :
    (state.installOpenings members openings).entries = state.entries := by
  apply List.ext_getElem?
  intro i
  simp only [RecState.entries, RecState.installOpenings, List.getElem?_map,
    List.getElem?_mapIdx]
  cases state.memberStates[i]? with
  | none => rfl
  | some old => split <;> rfl

@[simp] theorem RecState.rhsCtx_installOpenings (state : RecState) (members : List Nat)
    (openings : List RecOpening) (ctx : Ctx) :
    (state.installOpenings members openings).rhsCtx ctx = state.rhsCtx ctx := by
  simp [RecState.rhsCtx]

@[simp] theorem RecState.rhsCtx_setSigned (state : RecState) (member : Nat)
    (names : List Nat) (output : Expr) (facts : RecFacts) (ctx : Ctx) :
    (state.setSigned member names output facts).rhsCtx ctx = state.rhsCtx ctx := by
  simp [RecState.rhsCtx]

theorem RecState.getElem?_outputs_setSigned_self (state : RecState) (member : Nat)
    (names : List Nat) (output : Expr) (facts : RecFacts)
    (hmember : member < state.outputs.length) :
    (state.setSigned member names output facts).outputs[member]? =
      some (some (output.closeTyVars names)) := by
  have hi : member < state.memberStates.length := by
    simpa only [RecState.outputs_length] using hmember
  simp only [RecState.outputs, RecState.setSigned, List.getElem?_map,
    List.getElem?_mapIdx]
  rw [List.getElem?_eq_getElem hi]
  simp

theorem RecState.getElem?_outputs_setSigned_of_ne (state : RecState) (member i : Nat)
    (names : List Nat) (output : Expr) (facts : RecFacts) (hi : i ≠ member) :
    (state.setSigned member names output facts).outputs[i]? = state.outputs[i]? := by
  simp only [RecState.outputs, RecState.setSigned, List.getElem?_map,
    List.getElem?_mapIdx]
  cases state.memberStates[i]? <;> simp [hi]

theorem RecState.getElem?_outputs_exportComponent (state : RecState) (members : List Nat)
    (written : List (List Nat)) (pool : List Nat)
    (artifacts : List (Option RecComponentArtifact)) (i : Nat) :
    (state.exportComponent members written pool artifacts).outputs[i]? =
      state.memberStates[i]?.map (fun member =>
        if i ∈ members then do
          let ty ← member.spec.monoTy?
          let rhs ← recComponentOutputAt artifacts i
          pure (rhs.closeTyVars (recNames (written[i]?.getD []) pool ty))
        else member.output) := by
  simp only [RecState.outputs, RecState.exportComponent, List.getElem?_map,
    List.getElem?_mapIdx]
  cases state.memberStates[i]? with
  | none => rfl
  | some member => split <;> rfl

@[simp] theorem RecState.pool_exportComponent (state : RecState) (members : List Nat)
    (written : List (List Nat)) (pool : List Nat)
    (artifacts : List (Option RecComponentArtifact)) :
    (state.exportComponent members written pool artifacts).pool = pool := rfl

@[simp] theorem RecState.pool_onSubst (state : RecState) (S : Subst) :
    (state.onSubst S).pool = state.pool := rfl

@[simp] theorem RecState.prefixes_exportComponent (state : RecState) (members : List Nat)
    (written : List (List Nat)) (pool : List Nat)
    (artifacts : List (Option RecComponentArtifact)) :
    (state.exportComponent members written pool artifacts).prefixes = state.prefixes := by
  apply List.ext_getElem?
  intro i
  simp only [RecState.getElem?_prefixes, RecState.exportComponent, List.getElem?_mapIdx]
  cases state.memberStates[i]? with
  | none => rfl
  | some member =>
    simp only [Option.map_some]
    by_cases hm : i ∈ members
    · simp only [hm, if_pos]
      rcases member with ⟨spec, slots, exported, output, facts, annInfo⟩
      cases spec <;> rfl
    · simp [hm]

@[simp] theorem RecState.prefixes_installOpenings_of_disjoint (state : RecState)
    {members done : List Nat} {openings : List RecOpening}
    (hnot : ∀ i ∈ members, i ∉ done) :
    ∀ i ∈ done, (state.installOpenings members openings).prefixes[i]? = state.prefixes[i]? := by
  intro i hi
  simp only [RecState.getElem?_prefixes, RecState.installOpenings, List.getElem?_mapIdx]
  cases state.memberStates[i]? with
  | none => rfl
  | some member =>
    simp only [Option.map_some]
    rw [if_neg (fun hm => hnot i hm hi)]

@[simp] theorem RecState.stageEntries_installOpenings (state : RecState)
    (members : List Nat) (openings : List RecOpening) (earlier : List Nat) :
    (state.installOpenings members openings).stageEntries earlier = state.stageEntries earlier := by
  apply List.ext_getElem?
  intro i
  simp only [RecState.stageEntries, RecState.installOpenings, List.getElem?_mapIdx]
  cases state.memberStates[i]? with
  | none => rfl
  | some member =>
    simp only [Option.map_some]
    by_cases he : i ∈ earlier <;> by_cases hm : i ∈ members <;> simp [he, hm]

@[simp] theorem RecState.stageCtx_installOpenings (state : RecState) (members : List Nat)
    (openings : List RecOpening) (ctx : Ctx) (earlier : List Nat) :
    (state.installOpenings members openings).stageCtx ctx earlier = state.stageCtx ctx earlier := by
  simp [RecState.stageCtx]

 theorem RecState.SourceTyped.init : (RecState.init base bindings).SourceTyped ctx := by
  intro i scheme output _ ho
  rw [RecState.init_outputs, List.getElem?_map] at ho
  cases bindings[i]? <;> simp_all

 theorem RecState.SourceTyped.onSubst {state : RecState} {ctx : Ctx}
    (h : state.SourceTyped ctx) (S : Subst) (hlc : ∀ p ∈ S, p.2.IsLC) :
    (state.onSubst S).SourceTyped (S.onCtx ctx) := by
  intro i scheme output hs ho
  rw [RecState.exports_onSubst, List.getElem?_map] at hs
  rw [RecState.outputs_onSubst, List.getElem?_map] at ho
  obtain ⟨oldScheme, hscheme, heqScheme⟩ := Option.map_eq_some_iff.mp hs
  obtain ⟨sigma, hsigma, heq⟩ := Option.map_eq_some_iff.mp heqScheme
  cases heq
  obtain ⟨oldOutput, houtput, heqOutput⟩ := Option.map_eq_some_iff.mp ho
  obtain ⟨rhs, hrhs, heq⟩ := Option.map_eq_some_iff.mp heqOutput
  cases heq
  obtain ⟨hwf, L, hgen⟩ := h i sigma rhs (hsigma ▸ hscheme) (hrhs ▸ houtput)
  refine ⟨Subst.onPolyTy_wf hlc hwf, ?_⟩
  simpa only [RecState.rhsCtx_onSubst] using hgen.onSubst_annotated hwf S hlc

 theorem RecState.SourceTyped.installOpenings {state : RecState} {ctx : Ctx}
    (h : state.SourceTyped ctx) :
    (state.installOpenings members openings).SourceTyped ctx := by
  intro i scheme output hs ho
  rw [RecState.exports_installOpenings] at hs
  rw [RecState.outputs_installOpenings] at ho
  simpa only [RecState.rhsCtx_installOpenings] using h i scheme output hs ho

 theorem RecState.mem_entries_of_export {state : RecState} {i : Nat} {scheme : PolyTy}
    (hs : state.exports[i]? = some (some scheme)) : scheme ∈ state.entries := by
  rw [RecState.getElem?_exports] at hs
  obtain ⟨member, hmember, hexport⟩ := Option.map_eq_some_iff.mp hs
  apply List.mem_of_getElem? (i := i)
  rw [RecState.entries, List.getElem?_map, hmember]
  simp only [Option.map_some, hexport, Option.getD_some]

 theorem RecState.SourceTyped.setSigned {state : RecState} {ctx : Ctx}
    {member : Nat} {names : List Nat} {scheme : PolyTy} {output : Expr} {facts : RecFacts}
    (h : state.SourceTyped ctx) (hexport : state.exports[member]? = some (some scheme))
    (hwf : scheme.WF)
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
  rw [RecState.exports_setSigned] at hs
  by_cases hi : member = i
  · subst i
    have he : sigma = scheme := Option.some.inj (Option.some.inj (hs.symm.trans hexport))
    subst sigma
    have houtput : member < state.outputs.length := by
      have hm := (List.getElem?_eq_some_iff.mp hexport).1
      simpa only [RecState.exports_length, RecState.outputs_length] using hm
    rw [RecState.getElem?_outputs_setSigned_self state member names output facts houtput] at ho
    cases Option.some.inj (Option.some.inj ho)
    simpa only [RecState.rhsCtx_setSigned] using And.intro hwf ⟨names, hgen⟩
  · rw [RecState.getElem?_outputs_setSigned_of_ne state member i names output facts (Ne.symm hi)] at ho
    simpa only [RecState.rhsCtx_setSigned] using h i sigma rhs hs ho

 theorem RecState.entries_eq_of_exports {state : RecState} {schemes : List PolyTy}
    (hexports : state.exports = schemes.map some) : state.entries = schemes := by
  have hlen : state.entries.length = schemes.length := by
    rw [state.entries_length, state.specs_length, ← state.exports_length,
      hexports, List.length_map]
  apply List.ext_getElem?
  intro i
  cases hs : schemes[i]? with
  | none =>
      have hi : schemes.length ≤ i := List.getElem?_eq_none_iff.mp hs
      exact List.getElem?_eq_none_iff.mpr (hlen ▸ hi)
  | some scheme =>
      have he : state.exports[i]? = some (some scheme) := by
        rw [hexports, List.getElem?_map, hs]; rfl
      rw [RecState.getElem?_exports] at he
      obtain ⟨member, hmember, hexport⟩ := Option.map_eq_some_iff.mp he
      rw [RecState.entries, List.getElem?_map, hmember]
      simp only [Option.map_some, hexport, Option.getD_some]

private theorem collect_completed_avoids {ctx : Ctx} (completed : List CompletedRecMember)
    (h : ∀ member ∈ completed, ∃ L,
      GeneralisesTo TypeOfHM ctx (some member.scheme) member.output member.scheme L) :
    ∃ L, ∀ member ∈ completed,
      GeneralisesTo TypeOfHM ctx (some member.scheme) member.output member.scheme L := by
  induction completed with
  | nil => exact ⟨[], fun _ hm => by cases hm⟩
  | cons member rest ih =>
    obtain ⟨Lhead, hh⟩ := h member List.mem_cons_self
    obtain ⟨Ltail, ht⟩ := ih (fun m hm => h m (List.mem_cons_of_mem _ hm))
    refine ⟨Lhead ++ Ltail, ?_⟩
    intro current hm Xs hXs
    rcases List.mem_cons.mp hm with rfl | hm
    · exact hh Xs ⟨hXs.length, hXs.nodup,
        fun x hx hc => hXs.avoid x hx (List.mem_append_left _ hc)⟩
    · exact ht current hm Xs ⟨hXs.length, hXs.nodup,
        fun x hx hc => hXs.avoid x hx (List.mem_append_right _ hc)⟩

/-- Rebuild a fully completed recursive group from its row-shaped members. -/
theorem RecState.SourceTyped.letRec {state : RecState}
    {completed : List CompletedRecMember}
    (h : state.SourceTyped ctx)
    (hexports : state.exports = (completed.map CompletedRecMember.scheme).map some)
    (houtputs : state.outputs = (completed.map CompletedRecMember.output).map some)
    (hbody : TypeOfHM (state.rhsCtx ctx) body ty) :
    TypeOfHM ctx (.letRec (completed.map fun member =>
      { ann := some member.scheme, rhs := member.output }) body) ty := by
  let rows : List CoreRecBinding := completed.map fun member =>
    { ann := some member.scheme, rhs := member.output }
  let specs : List RecSpec := completed.map fun member => .poly member.scheme
  have hmember : ∀ member ∈ completed, member.scheme.WF ∧ ∃ L,
      GeneralisesTo TypeOfHM (state.rhsCtx ctx) (some member.scheme)
        member.output member.scheme L := by
    intro member hm
    obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hm
    exact h i member.scheme member.output
      (by simp only [hexports, List.getElem?_map, hi, Option.map_some])
      (by simp only [houtputs, List.getElem?_map, hi, Option.map_some])
  obtain ⟨L, hcofinite⟩ := collect_completed_avoids completed
    (fun member hm => (hmember member hm).2)
  have hvalid : RecGroups.ValidResidualGroups rows [] := by
    refine ⟨by simp, by simp, by simp, ?_, ?_⟩
    · intro i hi
      simp only [List.flatten_nil, List.not_mem_nil, false_iff,
        RecGroups.UnsignedAt, rows, List.getElem?_map]
      cases completed[i]? <;> simp
    · intro stage dependencyStage component dependencyComponent source target binding
        hstage
      simp at hstage
  have hwf : RecSpecs.WF rows specs [] := by
    refine ⟨?_, List.nodup_nil, ?_, ?_⟩
    · simp only [rows, specs, List.map_map, Function.comp_def, RecSpec.ann]
    · intro mono hm
      obtain ⟨member, _, heq⟩ := List.mem_map.mp hm
      cases heq
    · intro scheme hm
      obtain ⟨member, hmem, heq⟩ := List.mem_map.mp hm
      cases RecSpec.poly.inj heq
      exact (hmember member hmem).1
  refine TypeOfHM.letRec (specs := specs) (groups := []) (G := []) (L := L)
    hvalid hwf ?_ ?_ ?_ hbody
  · intro stage component hget
    simp at hget
  · intro pair hp scheme heq Ys hYs
    rcases pair with ⟨binding, spec⟩
    obtain ⟨i, hget⟩ := List.mem_iff_getElem?.mp hp
    obtain ⟨hb, hs⟩ := List.getElem?_zip_eq_some.mp hget
    simp only [List.getElem?_map] at hb
    simp only [specs, List.getElem?_map] at hs
    obtain ⟨left, hleft, hb⟩ := Option.map_eq_some_iff.mp hb
    obtain ⟨right, hright, hs⟩ := Option.map_eq_some_iff.mp hs
    have hlr : left = right := Option.some.inj (hleft.symm.trans hright)
    subst right binding spec
    have hscheme : left.scheme = scheme := RecSpec.poly.inj heq
    subst scheme
    have hgen := hcofinite left (List.mem_of_getElem? hleft) Ys hYs
    simpa only [GeneralisesTo, Expr.openBoundTyVars, RecSpecs.bodyCtx, specs,
      List.map_map, Function.comp_def, RecSpec.bodyScheme, RecState.rhsCtx,
      RecState.entries_eq_of_exports hexports] using hgen
  · simp only [RecSpecs.bodyCtx, specs, List.map_map, Function.comp_def,
      RecSpec.bodyScheme, RecState.rhsCtx, RecState.entries_eq_of_exports hexports]

 theorem RecState.SourceTyped.exportComponent {state : RecState}
    {artifacts : List (Option RecComponentArtifact)} {pool : List Nat}
    (h : state.SourceTyped ctx)
    (hlc : ∀ spec ∈ state.specs, spec.LC)
    (hclosed : ∀ i ∈ members, state.exports[i]? = some none)
    (hmono : ∀ i ∈ members, ∃ ty, state.specs[i]? = some (.mono ty))
    (hnd : ∀ i ∈ members, (written[i]?.getD []).Nodup)
    (hsub : ∀ i ∈ members, ∀ v ∈ written[i]?.getD [], v ∈ pool)
    (hpool : pool.Nodup)
    (hfresh : ∀ v ∈ pool, v ∉ ((state.exportComponent members written pool artifacts).rhsCtx ctx).env.freeVars)
    (htyped : ∀ (i : Nat) (ty : Ty) (output : Expr), state.specs[i]? = some (.mono ty) →
      recComponentOutputAt artifacts i = some output → TypeOfHM (state.rhsCtx ctx) output ty) :
    (state.exportComponent members written pool artifacts).SourceTyped ctx := by
  have hgeneral := RecState.exportComponent_entries_generalize
    (written := written) (artifacts := artifacts) (pool := pool)
    hlc hclosed hmono
  intro i scheme output hscheme houtput
  rw [RecState.getElem?_exports_exportComponent] at hscheme
  rw [RecState.getElem?_outputs_exportComponent] at houtput
  cases hmember : state.memberStates[i]? with
  | none => simp [hmember] at hscheme
  | some member =>
    have hmember_mem : member ∈ state.memberStates := List.mem_of_getElem? hmember
    have hspec : state.specs[i]? = some member.spec := by
      simp only [RecState.getElem?_specs, hmember, Option.map_some]
    by_cases hi : i ∈ members
    · obtain ⟨ty, hty⟩ := hmono i hi
      have hspecEq : member.spec = .mono ty := Option.some.inj (hspec.symm.trans hty)
      simp only [hmember, Option.map_some, hi, if_pos, hspecEq,
        RecSpec.completedScheme_mono] at hscheme houtput
      cases Option.some.inj hscheme
      change some (do
        let rhs ← recComponentOutputAt artifacts i
        pure (rhs.closeTyVars (recNames (written[i]?.getD []) pool ty))) = some (some output) at houtput
      obtain ⟨rhs, hrhs, hclose⟩ := Option.bind_eq_some_iff.mp (Option.some.inj houtput)
      cases Option.some.inj hclose
      have hchecked := htyped i ty rhs hty hrhs
      have hweaken : TypeOfHM
          ((state.exportComponent members written pool artifacts).rhsCtx ctx) rhs ty :=
        TypeOfHM.weaken_schemes hgeneral hchecked
      have hnames : (recNames (written[i]?.getD []) pool ty).Nodup :=
        recNames_nodup (hnd i hi) hpool
      have havoid : ∀ v ∈ recNames (written[i]?.getD []) pool ty,
          v ∉ ((state.exportComponent members written pool artifacts).rhsCtx ctx).env.freeVars := by
        intro v hv
        apply hfresh v
        rcases mem_recNames.mp hv with hv | ⟨hv, _, _⟩
        · exact hsub i hi v hv
        · exact hv
      have htyLC : ty.IsLC := by
        simpa only [hspecEq] using
          (hlc member.spec (List.mem_map.mpr ⟨member, hmember_mem, rfl⟩))
      exact ⟨recScheme_wf htyLC, _, hweaken.generaliseAnnotated hnames havoid⟩
    · simp only [hmember, Option.map_some, hi] at hscheme houtput
      have hscheme' := Option.some.inj hscheme
      have houtput' := Option.some.inj houtput
      simp only [if_false] at hscheme' houtput'
      have hOldScheme : state.exports[i]? = some (some scheme) := by
        simp only [RecState.getElem?_exports, hmember, Option.map_some, hscheme']
      have hOldOutput : state.outputs[i]? = some (some output) := by
        simp only [RecState.getElem?_outputs, hmember, Option.map_some, houtput']
      obtain ⟨hwf, L, hgen⟩ := h i scheme output hOldScheme hOldOutput
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


 theorem InferRecComponent.sourceSound_of_infer
    (h : InferRecComponent K F members index frontier ctx bindings specs next S artifacts)
    (hInfer : ∀ {κ F' Ψ c e Ψ' T output ty}, e.size ≤ sizeBindings bindings →
      Infer κ F' Ψ c e Ψ' T output ty → CtxWF c → TypeOfHM (T.onCtx c) output ty)
    (hLC : ∀ {κ F' Ψ c e Ψ' T output ty}, e.size ≤ sizeBindings bindings →
      Infer κ F' Ψ c e Ψ' T output ty → CtxWF c → ty.IsLC ∧ ∀ p ∈ T, p.2.IsLC)
    (hctx : CtxWF ctx) (hspec : ∀ spec ∈ specs, spec.LC) :
    ∀ (j : Nat) (target : Ty) (output : Expr), specs[j]? = some (RecSpec.mono target) →
      recComponentOutputAt artifacts j = some output →
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
        (fun he h => hLC (by simp only [sizeBindings_substInputBindings] at he; simp only [sizeBindings]; omega) h)
        hrCtx hrSpec
      intro j target output ht ho
      cases j with
      | zero =>
        cases Option.some.inj ht
        cases Option.some.inj ho
        have htyped := TypeOfHM.onSubst (s2 ++ s3)
          (fun p hp => (List.mem_append.mp hp).elim (huS p) (hrLC p))
          (hInfer (by simp only [sizeBindings]; omega) hi hctx)
        have heq := hu.unifies.unifies
        change s2.onTy ty = s2.onTy (s1.onTy expected) at heq
        simpa only [Subst.onCtx_append, Subst.onTy_append, heq] using htyped
      | succ j =>
        simp only [List.getElem?_cons_succ] at ht ho
        have htail := hr.sourceSound_of_infer
          (fun he h => hInfer (by simp only [sizeBindings_substInputBindings] at he; simp only [sizeBindings]; omega) h)
          (fun he h => hLC (by simp only [sizeBindings_substInputBindings] at he; simp only [sizeBindings]; omega) h)
          hrCtx hrSpec j ((s1 ++ s2).onTy target) output
          (by simp only [List.getElem?_map, ht, Option.map_some, RecSpec.onSubstSource]) ho
        simpa only [Subst.onCtx_append, Subst.onTy_append] using htail
 termination_by structural h

 theorem InferRecSigned.sourceSound_of_infer
    (h : InferRecSigned K F index frontier ctx bindings state next S final)
    (hInfer : ∀ {κ F' Ψ c e Ψ' T output ty}, e.size ≤ sizeBindings bindings →
      Infer κ F' Ψ c e Ψ' T output ty → CtxWF c → TypeOfHM (T.onCtx c) output ty)
    (hctx : CtxWF ctx) (hstate : state.LC) (htyped : state.SourceTyped ctx)
    (hcontracts : ∀ (j : Nat) (binding : InputRecBinding) (scheme : PolyTy),
      bindings[j]? = some binding → binding.ann = .complete scheme →
      state.exports[index + j]? = some (some scheme)) :
    final.SourceTyped (S.onCtx ctx) := by
  match h with
  | .nil => simpa only [Subst.onCtx_nil] using htyped
  | .skip _ hr =>
    apply hr.sourceSound_of_infer (fun he hi => hInfer (by simp only [sizeBindings]; omega) hi)
      hctx hstate htyped
    intro j binding scheme hb ha
    have hh := hcontracts (j + 1) binding scheme
      (by simpa only [List.getElem?_cons_succ] using hb) ha
    simpa only [Nat.add_assoc, Nat.add_comm 1 j] using hh
  | .cons hwf _ hi hu hescape hr =>
    expose_names
    have hiCtx := hstate.rhsCtx hctx
    obtain ⟨htLC, hS1⟩ := hi.lc hiCtx
    have hσLC := Subst.onPolyTy_wf hS1 hwf
    have hS2 := hu.unifies.lc htLC (PolyTy.openVars_isLC hσLC (by simp [Subst.onPolyTy]))
    have hS : ∀ p ∈ s1 ++ s2, p.2.IsLC := fun p hp => (List.mem_append.mp hp).elim (hS1 p) (hS2 p)
    have hready := (htyped.onSubst (s1 ++ s2) hS)
    have hex := hcontracts 0 { ann := .complete scheme, rhs := rhs } scheme rfl rfl
    simp only [Nat.add_zero] at hex
    have hex' : (state.onSubst (s1 ++ s2)).exports[index]? = some (some ((s1 ++ s2).onPolyTy scheme)) := by
      simp only [RecState.exports_onSubst, List.getElem?_map, hex, Option.map_some]
    have hmember := (state.onSubst (s1 ++ s2)).mem_entries_of_export hex'
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
    have hclosed := hready.setSigned (facts := bodyFacts.onSubst s2) hex' (Subst.onPolyTy_wf hS hwf)
      (by simp [Subst.onPolyTy]) (freshVars_nodup) hctxFresh hschemeFresh
      (by
        rw [RecState.rhsCtx_onSubst]
        change TypeOfHM ((s1 ++ s2).onCtx (state.rhsCtx ctx)) (output.substTyFvars s2)
          (((s1 ++ s2).onPolyTy scheme).openVars (freshVars frontier scheme.paramCount))
        simpa only [Subst.onCtx_append, Subst.onPolyTy_append, PolyTy.openVars, Subst.onPolyTy, Subst.onTy_append] using hrhs)
    have hfinal := hr.sourceSound_of_infer
      (fun he hj => hInfer (by simp only [sizeBindings_substInputBindings] at he; simp only [sizeBindings]; omega) hj)
      (Subst.onCtx_wf hS hctx) ((hstate.onSubst hS).setSigned) hclosed
      (by
        intro j binding sigma hb ha
        rw [substInputBindings_eq_map, List.getElem?_map] at hb
        obtain ⟨oldBinding, hold, rfl⟩ := Option.map_eq_some_iff.mp hb
        cases hann : oldBinding.ann with
        | absent | template | partialForall =>
          simp only [hann, BindingAnn.substTyFvars, reduceCtorEq] at ha
        | complete original =>
          have hsigma : (s1 ++ s2).onPolyTy original = sigma := by
            simpa only [hann, BindingAnn.substTyFvars, BindingAnn.complete.injEq,
              Subst.onPolyTy] using ha
          subst sigma
          have hh := hcontracts (j + 1) oldBinding original
            (by simpa only [List.getElem?_cons_succ] using hold) hann
          simp only [RecState.exports_setSigned, RecState.exports_onSubst, List.getElem?_map,
            Nat.add_assoc, Nat.add_comm 1 j, hh, Option.map_some, Subst.onPolyTy, Subst.onTy])
    simpa only [Subst.onCtx_append] using hfinal
 termination_by structural h


 theorem RecState.Frame.complete_export {state : RecState} {i : Nat} {scheme : PolyTy}
    (h : state.Frame base K F ctx bindings done) {binding : InputRecBinding}
    (hb : bindings[i]? = some binding) (ha : binding.ann = .complete scheme) :
    state.exports[i]? = some (some scheme) := by
  have hi : i < state.specs.length := by
    rw [h.specs_length]
    exact (List.getElem?_eq_some_iff.mp hb).1
  have hs := List.getElem?_eq_getElem hi
  have hm := congrArg (fun xs : List (Option PolyTy) => xs[i]?) h.modes
  dsimp only at hm
  rw [List.getElem?_map, hs, Option.map_some, List.getElem?_map, hb, Option.map_some, ha] at hm
  cases he : state.specs[i]'hi with
  | mono ty => simp only [he, RecSpec.ann, BindingAnn.recModeAnn] at hm; cases hm
  | poly sigma =>
    simp only [he, RecSpec.ann, BindingAnn.recModeAnn] at hm
    have heq : sigma = scheme := Option.some.inj (Option.some.inj hm)
    subst sigma
    exact h.poly i scheme (he ▸ hs)

 theorem RecState.Frame.mono_at_unsigned {state : RecState} {i : Nat}
    (h : state.Frame base K F ctx bindings done)
    (ha : (bindings.map fun binding => binding.ann.recModeAnn)[i]? = some none) :
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
    (h : state.Frame base K F ctx bindings done) (hs : state.specs[i]? = some spec)
    (he : state.entries[i]? = some scheme) :
    ∀ v ∈ scheme.body.freeVars, v ∈ spec.freeVars := by
  rw [RecState.entries, List.getElem?_map] at he
  obtain ⟨member, hmember, hentry⟩ := Option.map_eq_some_iff.mp he
  have hsp : state.specs[i]? = some member.spec := by
    simp only [RecState.getElem?_specs, hmember, Option.map_some]
  have hex : state.exports[i]? = some member.exported := by
    simp only [RecState.getElem?_exports, hmember, Option.map_some]
  have hsame : member.spec = spec := Option.some.inj (hsp.symm.trans hs)
  rw [hsame] at hentry
  cases spec with
  | poly sigma =>
    have hh := h.poly i sigma hs
    have hh' := Option.some.inj (hex.symm.trans hh)
    rw [hh'] at hentry
    cases hentry
    exact fun _ hv => hv
  | mono ty =>
    by_cases hd : i ∈ done
    · obtain ⟨written, _, _, _, _, hx⟩ := if_pos hd ▸ h.mono i ty hs
      have hh := Option.some.inj (hex.symm.trans hx)
      rw [hh] at hentry
      cases hentry
      exact fun _ hv => Ty.freeVars_closeOver_subset hv
    · have hx := if_neg hd ▸ h.mono i ty hs
      have hh := Option.some.inj (hex.symm.trans hx)
      rw [hh] at hentry
      cases hentry
      exact fun _ hv => hv

private theorem RecState.Frame.pending_lookup_other {state : RecState}
    (h : state.Frame base K F ctx bindings done)
    (ht : state.specs[member]? = some (.mono ty)) (hm : member ∉ done)
    (hne : i ≠ member) :
    ∀ scheme, (state.rhsCtx ctx).env[i]? = some scheme → base + member ∉ scheme.body.freeVars := by
  intro scheme hlook
  by_cases hi : i < state.entries.length
  · rw [RecState.rhsCtx, List.getElem?_append_left hi] at hlook
    have hispec : i < state.specs.length := state.entries_length ▸ hi
    have hs := List.getElem?_eq_getElem hispec
    exact fun hv => h.pending.other member ty ht hm i _ hs hne
      (h.entry_freeVars_subset hs hlook _ hv)
  · rw [RecState.rhsCtx, List.getElem?_append_right (by omega)] at hlook
    exact h.pending.env member ty ht hm scheme (List.mem_of_getElem? hlook)

private theorem RecState.Frame.pending_refs {state : RecState} {rhs : Expr}
    (h : state.Frame base K F ctx bindings done)
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
  cases hmember : state.memberStates[i]? with
  | none => simp [hmember] at heq
  | some member =>
    cases hspec : member.spec with
    | poly scheme => simp [hmember, hspec, RecSpec.monoTy?] at heq
    | mono ty =>
      cases hopen : openings[i]? with
      | none => simp [hmember, RecSpec.monoTy?, hopen] at heq
      | some opening =>
        simp [hmember, hspec, RecSpec.monoTy?, hopen] at heq
        cases heq
        have hsview : state.specs[i]? = some (.mono ty) := by
          simp only [RecState.getElem?_specs, hmember, Option.map_some, hspec]
        exact ⟨ha i ty him hsview, ho opening (List.mem_of_getElem? hopen)⟩

private theorem RecState.shape_mem {state : RecState} {i : Nat} {ty : Ty}
    {opening : RecOpening} (hi : i ∈ members)
    (ht : state.specs[i]? = some (.mono ty)) (ho : openings[i]? = some opening) :
    (ty, opening.expected) ∈ state.shapes members openings := by
  apply List.mem_filterMap.mpr
  refine ⟨i, hi, ?_⟩
  cases hm : state.memberStates[i]? with
  | none =>
    rw [RecState.getElem?_specs, hm] at ht
    simp at ht
  | some member =>
    have hs : member.spec = .mono ty := by
      rw [RecState.getElem?_specs, hm] at ht
      simpa only [Option.map_some, Option.some.injEq] using ht
    simp [hs, ho, RecSpec.monoTy?]

theorem openRecSources_getElem? {openings : List RecOpening} {bindings : List InputRecBinding}
    {i : Nat} {binding : InputRecBinding}
    (hlen : openings.length = bindings.length)
    (h : (openRecSources openings bindings)[i]? = some binding) :
    ∃ old : InputRecBinding, bindings[i]? = some old ∧
      binding = { old with rhs := old.rhs.openTyVars ((openings[i]?).getD .empty).written } := by
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
    (ho : OpenRecAnns component 0 frontier bindings opened openings)
    (hp : CheckRecShapes K ((state.installOpenings component openings).shapes component openings) pre)
    (hc : InferRecComponent K (substSoft pre (F ++ (openings.flatMap RecOpening.written).map Ty.fvar))
      component 0 opened (((state.installOpenings component openings).onSubst pre).rhsCtx (pre.onCtx ctx))
      (substInputBindings pre (openRecSources openings bindings))
      ((state.installOpenings component openings).onSubst pre).specs first current artifacts)
    (hInfer : ∀ {κ F' Ψ c e Ψ' T output ty}, e.size ≤ sizeBindings bindings →
      Infer κ F' Ψ c e Ψ' T output ty →
      ∀ {w}, w < Ψ →
      e.erase.ForallOuter (fun i => ∀ M, c.env[i]? = some M → w ∉ M.body.freeVars) 0 →
      w ∉ e.rigidVars →
      (∀ p ∈ T, w ∉ p.2.freeVars) ∧ w ∉ ty.freeVars ∧ w ∉ T.map Prod.fst)
    (hw : w < frontier)
    (hanns : ∀ binding ∈ bindings, w ∉ binding.ann.rigidVars)
    (hrhs : ∀ i binding, i ∈ component → bindings[i]? = some binding →
      binding.rhs.erase.ForallOuter (fun j => ∀ M, (state.rhsCtx ctx).env[j]? = some M →
        w ∉ M.body.freeVars) 0 ∧ w ∉ binding.rhs.rigidVars)
    (htarget : ∀ i ty, i ∈ component → state.specs[i]? = some (.mono ty) → w ∉ ty.freeVars) :
    (∀ p ∈ pre ++ current, w ∉ p.2.freeVars) ∧ w ∉ (pre ++ current).map Prod.fst := by
  have hpre := hp.sourceAvoid (recShapes_selected_avoid
    (fun i ty hi hs => htarget i ty hi (by
      rw [RecState.specs_installOpenings] at hs
      exact hs))
    (ho.expected_avoid hw hanns))
  have hn : ∀ opening ∈ openings, w ∉ opening.written := by
    intro opening hm hw'
    have hh := ho.written_range w (List.mem_flatMap.mpr ⟨opening, hm, hw'⟩)
    omega
  have hcomponent := hc.sourceLocality_of_infer
    (fun he hi => hInfer (by simpa only [sizeBindings_substInputBindings, sizeBindings_openRecSources] using he) hi)
    (Nat.lt_of_lt_of_le hw ho.frontier_le)
    (by
      intro i rhs hi hget
      rw [substInputBindings_eq_map, List.getElem?_map] at hget
      obtain ⟨openedBinding, hopen, heq⟩ := Option.map_eq_some_iff.mp hget
      subst rhs
      obtain ⟨old, hold, heq⟩ := openRecSources_getElem? ho.length hopen
      subst openedBinding
      have hhead := hrhs i old (by simpa using hi) hold
      have hnv : w ∉ ((openings[i]?).getD .empty).written := by
        cases hx : openings[i]? with
        | none => simp [RecOpening.empty]
        | some opening => exact hn opening (List.mem_of_getElem? hx)
      refine ⟨?_, InferInput.avoid_subst hpre.1 (fun hv => (InferInput.rigidVars_openTyVarsFrom hv).elim hhead.2 hnv)⟩
      have hctxeq : ((state.installOpenings component openings).onSubst pre).rhsCtx (pre.onCtx ctx) =
          pre.onCtx (state.rhsCtx ctx) := by
        rw [RecState.rhsCtx_onSubst]
        rw [RecState.rhsCtx_installOpenings]
      rw [hctxeq]
      simpa only [InferInput.erase_substTyFvars, InferInput.erase_openTyVars] using
        Expr.ForallOuter.lookupAvoid_onSubst (S := pre) hhead.1 hpre.1)
    (by
      intro i ty hi hget
      have hget' : (state.specs.map (RecSpec.onSubstSource pre))[i]? = some (.mono ty) := by
        simpa only [RecState.specs_onSubst, RecState.specs_installOpenings] using hget
      obtain ⟨old, hold, rfl⟩ := RecSpec.mono_getElem?_map_onSubstSource hget'
      exact Subst.notMemOnTy hpre.1 (htarget i old (by simpa using hi) hold))
  exact ⟨fun p hp => (List.mem_append.mp hp).elim (hpre.1 p) (hcomponent.1 p),
    by simpa only [List.map_append, List.mem_append, not_or] using And.intro hpre.2 hcomponent.2⟩

 theorem recStep_oldpool_pending_avoid
    {state : RecState}
    (ho : OpenRecAnns component 0 frontier bindings opened openings)
    (hp : CheckRecShapes K ((state.installOpenings component openings).shapes component openings) pre)
    (hc : InferRecComponent K (substSoft pre (F ++ (openings.flatMap RecOpening.written).map Ty.fvar))
      component 0 opened (((state.installOpenings component openings).onSubst pre).rhsCtx (pre.onCtx ctx))
      (substInputBindings pre (openRecSources openings bindings))
      ((state.installOpenings component openings).onSubst pre).specs first current artifacts)
    (hInfer : ∀ {κ F' Ψ c e Ψ' T output ty}, e.size ≤ sizeBindings bindings →
      Infer κ F' Ψ c e Ψ' T output ty →
      ∀ {w}, w < Ψ →
      e.erase.ForallOuter (fun i => ∀ M, c.env[i]? = some M → w ∉ M.body.freeVars) 0 →
      w ∉ e.rigidVars →
      (∀ p ∈ T, w ∉ p.2.freeVars) ∧ w ∉ ty.freeVars ∧ w ∉ T.map Prod.fst)
    (hvalid : RecGroups.ValidResidualGroups (bindings.map InputRecBinding.recMode)
      (past ++ component :: rest))
    (hframe : state.Frame base K F ctx bindings past.flatten)
    (hbelow : state.Below frontier) (hbase : base + bindings.length ≤ frontier)
    (hbindings : ∀ binding ∈ bindings,
      ∀ v ∈ binding.ann.rigidVars ++ binding.rhs.rigidVars, v ∈ K ++ softVars F) :
    (∀ g ∈ state.pool, (∀ p ∈ pre ++ current, g ∉ p.2.freeVars) ∧ g ∉ (pre ++ current).map Prod.fst) ∧
    (∀ member ty, state.specs[member]? = some (.mono ty) → member ∉ past.flatten ++ component →
      (∀ p ∈ pre ++ current, base + member ∉ p.2.freeVars) ∧ base + member ∉ (pre ++ current).map Prod.fst) := by
  have hnot : ∀ i ∈ component, i ∉ past.flatten := by
    intro i hi hd
    have hnd : (past.flatten ++ (component ++ rest.flatten)).Nodup := by
      simpa only [List.flatten_append, List.flatten_cons] using hvalid.flatten_nodup
    exact (List.nodup_append.mp hnd).2.2 i hd i (List.mem_append_left _ hi) rfl
  constructor
  · intro g hg
    apply recStep_sourceAvoid ho hp hc hInfer (hbelow.2.2.2 g hg)
    · intro binding hb hv
      exact (List.mem_append.mp (hbindings binding hb g (List.mem_append_left _ hv))).elim
        (hframe.pool_rigid g hg) (hframe.pool_soft g hg)
    · intro i binding hi hget
      refine ⟨?_, ?_⟩
      · apply Expr.ForallOuter.of_recGroupRefs_with_outer (n := 0)
        · intro j hj M hm hv
          exact hframe.pool_rhsCtx g hg (Env.mem_freeVars_iff.mpr ⟨M, List.mem_of_getElem? hm, hv⟩)
        · intro j _ M hm hv
          exact hframe.pool_rhsCtx g hg (Env.mem_freeVars_iff.mpr ⟨M, List.mem_of_getElem? hm, hv⟩)
      · intro hv
        exact (List.mem_append.mp (hbindings binding (List.mem_of_getElem? hget) g
          (List.mem_append_right _ hv))).elim
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
      rw [hframe.specs_length] at hlt
      omega
    have hrigid : base + member ∉ K := fun hh => by have := hframe.rigid_below _ hh; omega
    have hsoft := hframe.pending_soft member ty ht hdone
    apply recStep_sourceAvoid ho hp hc hInfer hw
    · intro binding hb hv
      exact (List.mem_append.mp (hbindings binding hb _ (List.mem_append_left _ hv))).elim hrigid hsoft
    · intro i binding hi hget
      refine ⟨?_, fun hv => (List.mem_append.mp (hbindings binding
        (List.mem_of_getElem? hget) _ (List.mem_append_right _ hv))).elim hrigid hsoft⟩
      apply hframe.pending_refs ht hdone
      have hmodes : state.specs.map RecSpec.ann =
          (bindings.map InputRecBinding.recMode).map RecBinding.ann := by
        simpa only [InputRecBinding.map_recMode_ann] using hframe.modes
      have hcore : (bindings.map InputRecBinding.recMode)[i]? = some binding.recMode := by
        simp only [List.getElem?_map, hget, Option.map_some]
      simpa only [InputRecBinding.recMode] using
        hvalid.pending_no_ref hmodes hi hcore ht hm
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
    {written : List (List Nat)} {artifacts : List (Option RecComponentArtifact)}
    (h : state.Frame base K F ctx bindings done) (hlc : state.LC) (hS : ∀ p ∈ S, p.2.IsLC)
    (hpool : ∀ g ∈ state.pool, (∀ p ∈ S, g ∉ p.2.freeVars) ∧ g ∉ S.map Prod.fst)
    (hpending : ∀ i ty, state.specs[i]? = some (.mono ty) → i ∉ done ++ members →
      (∀ p ∈ S, base + i ∉ p.2.freeVars) ∧ base + i ∉ S.map Prod.fst)
    (hresolve : ResolveRecSlots members
      (((state.onSubst S).fixedCtx (S.onCtx ctx)).env.freeVars ++ K ++ softVars (substSoft S F))
      0 (state.onSubst S).slots written)
    (hcounts : ∀ (i : Nat) images, i ∈ members → (state.onSubst S).slots[i]? = some images →
      (state.onSubst S).recPrefixCountAt i = some images.length)
    (hslots : ∀ member ty, state.specs[member]? = some (.mono ty) → member ∉ done ++ members →
      ∀ (i : Nat) images, i ∈ members → (state.onSubst S).slots[i]? = some images →
        ∀ t ∈ images, base + member ∉ t.freeVars) :
    ((state.onSubst S).exportComponent members written
      ((state.onSubst S).componentPool K (softVars (substSoft S F)) members (S.onCtx ctx) written) artifacts).Frame
      base K (substSoft S F) (S.onCtx ctx) (substInputBindings S bindings) (done ++ members) := by
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
    rw [show st.specs = state.specs.map (RecSpec.onSubstSource S) from
      RecState.specs_onSubst state S, List.getElem?_map] at hs
    obtain ⟨old, hold, heq⟩ := Option.map_eq_some_iff.mp hs
    cases old with
    | mono ty => cases heq
    | poly original =>
      cases RecSpec.poly.inj heq
      simp only [st, RecState.exports_onSubst, List.getElem?_map,
        h.poly i original hold, Option.map_some]
  have hp' : RecSpecs.PendingSeeds base (S.onCtx ctx) st.specs (done ++ members) := by
    simpa only [st, RecState.specs_onSubst] using hp
  change (st.exportComponent members written pool artifacts).Frame base K (substSoft S F) (S.onCtx ctx)
    (substInputBindings S bindings) (done ++ members)
  refine {
    modes := ?_
    annInfo := ?_
    poly := ?_
    mono := ?_
    pending := by simpa only [RecState.specs_exportComponent] using hp'
    pool_nodup := st.componentPool_nodup h.pool_nodup
    pool_ctx := ?_
    pool_rigid := ?_
    pool_soft := ?_
    pool_poly := ?_
    pool_pending := ?_
    rigid_below := h.rigid_below
    pending_soft := ?_ }
  · have hm : st.specs.map RecSpec.ann = (state.specs.map RecSpec.ann).map (Option.map S.onPolyTy) := by
      simp only [st, RecState.specs_onSubst, List.map_map]
      apply List.map_congr_left
      intro spec _
      cases spec <;> rfl
    rw [RecState.specs_exportComponent, hm, h.modes]
    simp only [substInputBindings_eq_map, List.map_map, Function.comp_def,
      BindingAnn.recModeAnn_subst_source]
  · rw [RecState.annInfo_exportComponent]
    change (state.onSubst S).memberStates.map RecMemberState.annInfo = _
    rw [RecState.annInfo_onSubst, h.annInfo]
    simp only [substInputBindings_eq_map, List.map_map, Function.comp_def,
      BindingAnn.recMemberAnnInfo_substTyFvars]
  · intro i sigma hs
    rw [RecState.specs_exportComponent] at hs
    have hex := hpoly i sigma hs
    rw [RecState.getElem?_exports_exportComponent]
    cases hmember : st.memberStates[i]? with
    | none =>
      rw [RecState.getElem?_specs, hmember] at hs
      simp at hs
    | some member =>
      have hspec : member.spec = .poly sigma := by
        rw [RecState.getElem?_specs, hmember] at hs
        simpa only [Option.map_some, Option.some.injEq] using hs
      by_cases hi : i ∈ members
      · simp [hi, hspec, RecSpec.completedScheme]
      · rw [RecState.getElem?_exports, hmember] at hex
        simpa [hmember, hi] using hex
  · intro i ty hs
    rw [RecState.specs_exportComponent] at hs
    have hs' : (state.specs.map (RecSpec.onSubstSource S))[i]? = some (.mono ty) := by
      simpa only [st, RecState.specs_onSubst] using hs
    obtain ⟨original, hold, heqty⟩ := RecSpec.mono_getElem?_map_onSubstSource hs'
    subst ty
    by_cases hi : i ∈ members
    · have hislot : i < st.slots.length := by
        simpa only [RecState.slots_length, RecState.specs_length] using
          (List.getElem?_eq_some_iff.mp hs).1
      have hslotget := List.getElem?_eq_getElem hislot
      obtain ⟨names, hnames, hbare⟩ := hresolve.lookup i _ hslotget
      rw [Nat.zero_add, if_pos hi] at hbare
      rw [if_pos (List.mem_append_right _ hi)]
      refine ⟨names, ?_, ?_, hbare.2.1, ?_, ?_⟩
      · rw [RecState.slots_exportComponent]
        rw [hbare.1]; exact hslotget
      · have hh := hcounts i _ hi hslotget
        rw [← hbare.1, List.length_map] at hh
        simpa only [RecState.recPrefixCountAt_exportComponent] using hh
      · intro v hv
        exact st.componentPool_written (List.mem_flatten.mpr ⟨names, List.mem_of_getElem? hnames, hv⟩)
      · rw [RecState.getElem?_exports_exportComponent]
        cases hmember : st.memberStates[i]? with
        | none =>
          rw [RecState.getElem?_specs, hmember] at hs
          simp at hs
        | some member =>
          have hspec : member.spec = .mono (S.onTy original) := by
            rw [RecState.getElem?_specs, hmember] at hs
            simpa only [Option.map_some, Option.some.injEq] using hs
          simp [hi, hspec, hnames, RecSpec.completedScheme,
            RecState.pool_exportComponent]
    · have hm := h.mono i original hold
      by_cases hd : i ∈ done
      · obtain ⟨names, hslot, hcount, hnd, hsub, hex⟩ := if_pos hd ▸ hm
        rw [if_pos (List.mem_append_left _ hd)]
        have hnormalized : st.exports[i]? = some (some (recScheme names state.pool (S.onTy original))) := by
          simp only [st, RecState.exports_onSubst, List.getElem?_map, hex, Option.map_some]
          rw [recScheme_subst_pool_avoid hdom hran hsub]
        have hstable := st.recScheme_componentPool_eq (members := members)
          (Subst.onTy_lc hS (hlc.1 _ (List.mem_of_getElem? hold))) hsub
          (List.mem_of_getElem? hnormalized) hwritten
        refine ⟨names, ?_, ?_, hnd, fun v hv => st.componentPool_old (hsub v hv), ?_⟩
        · simp only [RecState.slots_exportComponent, st, RecState.slots_onSubst,
            List.getElem?_map, hslot, Option.map_some]
          congr 1
          rw [List.map_map]
          exact List.map_congr_left (fun v hv => hfix v (hsub v hv))
        · simpa only [RecState.recPrefixCountAt_exportComponent, st,
            RecState.recPrefixCountAt_onSubst] using hcount
        · have hstable' : recScheme names pool (S.onTy original) = recScheme names state.pool (S.onTy original) := hstable
          rw [RecState.pool_exportComponent]
          rw [hstable']
          rw [RecState.getElem?_exports_exportComponent]
          simpa only [RecState.getElem?_exports, if_neg hi] using hnormalized
      · rw [if_neg (by simpa only [List.mem_append, not_or] using And.intro hd hi)]
        have hex := if_neg hd ▸ hm
        have hex' : st.exports[i]? = some none := by
          simp only [st, RecState.exports_onSubst, List.getElem?_map, hex,
            Option.map_some, Option.map_none]
        rw [RecState.getElem?_exports_exportComponent]
        simpa only [RecState.getElem?_exports, if_neg hi] using hex'
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
    rw [RecState.specs_exportComponent] at hs
    by_cases hold : v ∈ state.pool
    · rw [show st.specs = state.specs.map (RecSpec.onSubstSource S) from
        RecState.specs_onSubst state S, List.getElem?_map] at hs
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
    rw [RecState.specs_exportComponent] at hs
    have hs' : (state.specs.map (RecSpec.onSubstSource S))[member]? = some (.mono ty) := by
      simpa only [st, RecState.specs_onSubst] using hs
    obtain ⟨old, ho, _⟩ := RecSpec.mono_getElem?_map_onSubstSource hs'
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
            have hspec' : (state.specs.map (RecSpec.onSubstSource S))[j]? =
                some (.mono tau0) := by
              simpa only [st, RecState.specs_onSubst] using hspec
            exact hp.other member ty hs' hm j (.mono tau0) hspec'
              (fun heq => hm (List.mem_append_right _ (heq ▸ hj))) hmem
  · intro member ty hs hm hfv
    rw [RecState.specs_exportComponent] at hs
    have hs' : (state.specs.map (RecSpec.onSubstSource S))[member]? = some (.mono ty) := by
      simpa only [st, RecState.specs_onSubst] using hs
    obtain ⟨old, ho, _⟩ := RecSpec.mono_getElem?_map_onSubstSource hs'
    obtain ⟨t, ht, hf⟩ := TyList.mem_freeVars_iff.mp hfv
    obtain ⟨original, horig, rfl⟩ := List.mem_map.mp ht
    exact Subst.notMemOnTy (hpending member old ho hm).1
      (fun hh => h.pending_soft member old ho (fun hd => hm (List.mem_append_left _ hd))
        (TyList.mem_freeVars_iff.mpr ⟨original, horig, hh⟩)) hf

private theorem OpenRecAnn.written_count
    (h : OpenRecAnn frontier ann next opening) :
    opening.written.length = ann.recPrefixCount := by
  cases h <;> simp [BindingAnn.recPrefixCount, RecOpening.empty, freshVars_length]

private theorem OpenRecAnns.written_count
    (h : OpenRecAnns members index frontier bindings next openings) :
    ∀ j : Nat, index + j ∈ members → ((openings[j]?).getD .empty).written.length =
      ((bindings[j]?).map (fun binding : InputRecBinding => binding.ann)
        |>.getD BindingAnn.absent).recPrefixCount := by
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
    | zero => simpa using hh.written_count
    | succ j => exact ih j (by simpa only [Nat.succ_add, Nat.add_succ] using hj)

private theorem installed_subst_slot {state : RecState} {S : Subst} {i : Nat} {images : List Ty}
    (hi : i ∈ members) (hx : ((state.installOpenings members openings).onSubst S).slots[i]? = some images) :
    images = (((openings[i]?).getD .empty).written.map Ty.fvar).map S.onTy := by
  rw [RecState.slots_onSubst, List.getElem?_map] at hx
  obtain ⟨old, hold, heq⟩ := Option.map_eq_some_iff.mp hx
  rw [RecState.getElem?_slots_installOpenings] at hold
  cases hm : state.memberStates[i]? with
  | none => simp [hm] at hold
  | some member =>
    simp only [hm, Option.map_some, if_pos hi, Option.some.injEq] at hold
    subst old
    exact heq.symm

private theorem installed_subst_slot_value {state : RecState} {S : Subst} {i : Nat}
    (hi : i ∈ members) (hlt : i < state.slots.length) :
    ((state.installOpenings members openings).onSubst S).slots[i]? =
      some ((((openings[i]?).getD .empty).written.map Ty.fvar).map S.onTy) := by
  rw [RecState.slots_onSubst, List.getElem?_map,
    RecState.getElem?_slots_installOpenings]
  have hm : i < state.memberStates.length := by
    simpa only [RecState.slots_length] using hlt
  rw [List.getElem?_eq_getElem hm]
  simp [hi]

 theorem recStep_frame
    {state : RecState}
    (ho : OpenRecAnns component 0 frontier bindings opened openings)
    (hp : CheckRecShapes K ((state.installOpenings component openings).shapes component openings) pre)
    (hc : InferRecComponent K (substSoft pre (F ++ (openings.flatMap RecOpening.written).map Ty.fvar))
      component 0 opened (((state.installOpenings component openings).onSubst pre).rhsCtx (pre.onCtx ctx))
      (substInputBindings pre (openRecSources openings bindings))
      ((state.installOpenings component openings).onSubst pre).specs first current artifacts)
    (hf : FinishRecComponent K (softVars (substSoft (pre ++ current) F)) component
      ((pre ++ current).onCtx ctx) ((state.installOpenings component openings).onSubst (pre ++ current))
      artifacts exported)
    (hInfer : ∀ {κ F' Ψ c e Ψ' T output ty}, e.size ≤ sizeBindings bindings →
      Infer κ F' Ψ c e Ψ' T output ty →
      ∀ {w}, w < Ψ →
      e.erase.ForallOuter (fun i => ∀ M, c.env[i]? = some M → w ∉ M.body.freeVars) 0 →
      w ∉ e.rigidVars →
      (∀ p ∈ T, w ∉ p.2.freeVars) ∧ w ∉ ty.freeVars ∧ w ∉ T.map Prod.fst)
    (hvalid : RecGroups.ValidResidualGroups (bindings.map InputRecBinding.recMode)
      (past ++ component :: rest))
    (hframe : state.Frame base K F ctx bindings past.flatten)
    (hlc : state.LC) (hctx : CtxWF ctx)
    (hbelow : state.Below frontier) (hbase : base + bindings.length ≤ frontier)
    (hbindings : ∀ binding ∈ bindings,
      ∀ v ∈ binding.ann.rigidVars ++ binding.rhs.rigidVars, v ∈ K ++ softVars F) :
    exported.Frame base K (substSoft (pre ++ current) F) ((pre ++ current).onCtx ctx)
      (substInputBindings (pre ++ current) bindings) (past.flatten ++ component) ∧
    (∀ g ∈ state.pool, (∀ p ∈ pre ++ current, g ∉ p.2.freeVars) ∧ g ∉ (pre ++ current).map Prod.fst) ∧
    (∀ member ty, state.specs[member]? = some (.mono ty) → member ∉ past.flatten ++ component →
      (∀ p ∈ pre ++ current, base + member ∉ p.2.freeVars) ∧ base + member ∉ (pre ++ current).map Prod.fst) := by
  have havoid := recStep_oldpool_pending_avoid ho hp hc hInfer hvalid hframe hbelow hbase hbindings
  have hnot : ∀ i ∈ component, i ∉ past.flatten := by
    intro i hi hd
    have hnd : (past.flatten ++ (component ++ rest.flatten)).Nodup := by
      simpa only [List.flatten_append, List.flatten_cons] using hvalid.flatten_nodup
    exact (List.nodup_append.mp hnd).2.2 i hd i (List.mem_append_left _ hi) rfl
  have hins : (state.installOpenings component openings).Frame base K F ctx bindings past.flatten :=
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
    apply hins.exportComponent_onSubst hlc.installOpenings hSLC havoid.1
      (by simpa only [RecState.specs_installOpenings] using havoid.2) hresolve
    · intro i images hi hx
      have hindex : i < bindings.length := by
        rw [← hframe.memberStates_length]
        have hs : i < ((state.installOpenings component openings).onSubst
            (pre ++ current)).slots.length := (List.getElem?_eq_some_iff.mp hx).1
        simpa only [RecState.slots_length, RecState.onSubst, RecState.installOpenings,
          List.length_mapIdx, List.length_map] using hs
      let binding := bindings[i]
      have hb : bindings[i]? = some binding := List.getElem?_eq_getElem hindex
      have himages : images.length = binding.ann.recPrefixCount := by
        rw [installed_subst_slot hi hx, List.length_map, List.length_map]
        simpa only [hb, Option.map_some, Option.getD_some] using
          ho.written_count i (by simpa using hi)
      rw [RecState.recPrefixCountAt_onSubst, hins.recPrefixCountAt hb]
      exact congrArg some himages.symm
    · intro member ty ht hm i images hi hx t htmem
      have ht0 : state.specs[member]? = some (.mono ty) := by
        simpa only [RecState.specs_installOpenings] using ht
      have hw : base + member < frontier := by
        have hlt := (List.getElem?_eq_some_iff.mp ht0).1
        rw [hframe.specs_length] at hlt
        omega
      rw [installed_subst_slot hi hx] at htmem
      obtain ⟨old, hold, rfl⟩ := List.mem_map.mp htmem
      obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hold
      apply Subst.notMemOnTy (havoid.2 member ty ht0 hm).1
      simp only [Ty.freeVars, List.mem_singleton]
      intro heq
      subst v
      cases hxopen : openings[i]? with
      | none => simp [hxopen, RecOpening.empty] at hv
      | some opening =>
        have hrange := ho.written_range (base + member)
          (List.mem_flatMap.mpr ⟨opening, List.mem_of_getElem? hxopen, by simpa only [hxopen, Option.getD_some] using hv⟩)
        omega

private theorem recAnn_substFvars_eq_map (S : Subst) (ann : Option PolyTy) :
    RecAnn.substFvars S ann = ann.map S.onPolyTy := by
  cases ann <;> simp [RecAnn.substFvars_none, RecAnn.substFvars_some,
    PolyTy.substFvars_eq, Subst.onPolyTy, Subst.onTy]

theorem recValid_subst {bindings : List InputRecBinding}
    (h : RecGroups.ValidResidualGroups (bindings.map InputRecBinding.recMode) groups)
    (S : Subst) :
    RecGroups.ValidResidualGroups
      ((substInputBindings S bindings).map InputRecBinding.recMode) groups := by
  let f : CoreRecBinding → CoreRecBinding := fun binding =>
    { ann := RecAnn.substFvars S binding.ann, rhs := binding.rhs }
  have hg := h.map_bindings f
    (fun i => by
      simp only [RecGroups.UnsignedAt, List.getElem?_map, Option.map_map, Function.comp_def]
      cases bindings[i]? with
      | none => simp
      | some binding =>
        cases hann : binding.ann <;>
          simp [f, InputRecBinding.recMode, BindingAnn.recModeAnn,
            RecAnn.substFvars_none,
            RecAnn.substFvars_some, hann])
    (fun _ _ => rfl)
  simpa only [substInputBindings_eq_map, List.map_map, Function.comp_def,
    InputRecBinding.recMode, f, BindingAnn.recModeAnn_subst_source,
    InferInput.erase_substTyFvars, RecAnn.substFvars_none,
    RecAnn.substFvars_some, Subst.onPolyTy, recAnn_substFvars_eq_map] using hg

private theorem FinishRecComponent.pool_extends
    (h : FinishRecComponent K soft members ctx state artifacts final) (hv : v ∈ state.pool) :
    v ∈ final.pool := by
  cases h
  exact state.componentPool_old hv

 theorem InferRecStrata.frame_of_infer
    (h : InferRecStrata K F frontier ctx bindings state groups next S final)
    (hInfer : ∀ {κ F' Ψ c e Ψ' T output ty}, e.size ≤ sizeBindings bindings →
      Infer κ F' Ψ c e Ψ' T output ty →
      ∀ {w}, w < Ψ →
      e.erase.ForallOuter (fun i => ∀ M, c.env[i]? = some M → w ∉ M.body.freeVars) 0 →
      w ∉ e.rigidVars →
      (∀ p ∈ T, w ∉ p.2.freeVars) ∧ w ∉ ty.freeVars ∧ w ∉ T.map Prod.fst)
    (hvalid : RecGroups.ValidResidualGroups (bindings.map InputRecBinding.recMode) (past ++ groups))
    (hframe : state.Frame base K F ctx bindings past.flatten)
    (hlc : state.LC) (hctxWF : CtxWF ctx)
    (hbelow : state.Below frontier) (hctx : CtxBelow frontier ctx)
    (hF : ∀ t ∈ F, Ty.BelowFvars frontier t)
    (hbase : base + bindings.length ≤ frontier)
    (hbindings : ∀ binding ∈ bindings,
      ∀ v ∈ binding.ann.rigidVars ++ binding.rhs.rigidVars, v ∈ K ++ softVars F) :
    final.Frame base K (substSoft S F) (S.onCtx ctx)
      (substInputBindings S bindings) (past ++ groups).flatten ∧
    (∀ g ∈ state.pool, (∀ p ∈ S, g ∉ p.2.freeVars) ∧ g ∉ S.map Prod.fst) := by
  match h with
  | .nil =>
    have hbindingsNil : substInputBindings [] bindings = bindings :=
      substInputBindings_eq_self_of_fixes bindings (fun _ _ => rfl)
    exact ⟨by simpa only [substSoft_nil, Subst.onCtx_nil, hbindingsNil, List.append_nil] using hframe,
      by intro g hg; exact ⟨by simp, by simp⟩⟩
  | .cons ho hp hc hf hr =>
    expose_names
    obtain ⟨hstepFrame, hstepPool, _⟩ := recStep_frame ho hp hc hf hInfer hvalid hframe
      hlc hctxWF hbelow hbase hbindings
    have hstep : InferRecStrata K F frontier ctx bindings state [component]
        first (pre ++ current ++ []) exported := .cons ho hp hc hf .nil
    have hK : ∀ k ∈ K, k < frontier := fun k hk => by have := hframe.rigid_below k hk; omega
    have hAnnBelow : ∀ binding ∈ bindings, ∀ v ∈ binding.ann.rigidVars, v < frontier := by
      intro binding hb v hv
      exact (List.mem_append.mp (hbindings binding hb v (List.mem_append_left _ hv))).elim
        (hK v) (softVars_lt hF v)
    have hstepBelow := hstep.belowFvars_of_infer (fun _ hi => hi.belowFvars) hctx hK hF hbelow hAnnBelow
    simp only [List.append_nil] at hstepBelow
    have hstepLC := hstep.lc_of_infer (fun _ hi => hi.lc) hctxWF hlc
    simp only [List.append_nil] at hstepLC
    have hfix : ∀ k ∈ K, (pre ++ current).onTy (.fvar k) = .fvar k := by
      apply Subst.fixes_of_dom_avoids
      simpa only [List.append_nil] using hstep.dom_avoids
    have htailValid := recValid_subst (S := pre ++ current)
      (by simpa only [List.append_assoc, List.singleton_append] using hvalid :
        RecGroups.ValidResidualGroups (bindings.map InputRecBinding.recMode)
          ((past ++ [component]) ++ rest))
    have htailFrame : exported.Frame base K (substSoft (pre ++ current) F) ((pre ++ current).onCtx ctx)
        (substInputBindings (pre ++ current) bindings) (past ++ [component]).flatten := by
      simpa only [List.flatten_append, List.flatten_cons, List.flatten_nil, List.append_nil] using hstepFrame
    obtain ⟨hfinal, htailPool⟩ := hr.frame_of_infer
      (fun he hi => hInfer (by simpa only [sizeBindings_substInputBindings] using he) hi)
      htailValid htailFrame hstepLC.2 (Subst.onCtx_wf hstepLC.1 hctxWF)
      hstepBelow.2 (Subst.onCtx_below hstepBelow.1 (ho.frontier_le.trans hc.frontier_le) hctx)
      (substSoft_below hstepBelow.1 (ho.frontier_le.trans hc.frontier_le) hF)
      (by
        simp only [substInputBindings_eq_map, List.length_map]
        have := ho.frontier_le
        have := hc.frontier_le
        omega)
      (by
        intro binding hm v hv
        rw [substInputBindings_eq_map] at hm
        obtain ⟨original, ho, rfl⟩ := List.mem_map.mp hm
        rcases List.mem_append.mp hv with hv | hv
        · obtain ⟨k, hk, himage⟩ := BindingAnn.rigidVars_substTyFvars hv
          exact scope_image hfix
            (hbindings original ho k (List.mem_append_left _ hk)) himage
        · exact (show SourceScope K F original.rhs from fun v hv =>
            hbindings original ho v (List.mem_append_right _ hv)).subst
              (pre ++ current) hfix v hv)
    refine ⟨?_, ?_⟩
    · simpa only [substSoft_append, Subst.onCtx_append, substInputBindings_append,
        List.append_assoc, List.singleton_append] using hfinal
    · intro g hg
      have ht := htailPool g (hf.pool_extends hg)
      exact ⟨fun p hp => (List.mem_append.mp hp).elim ((hstepPool g hg).1 p) (ht.1 p),
        by simpa only [List.map_append, List.mem_append, not_or] using And.intro (hstepPool g hg).2 ht.2⟩
 termination_by structural h


theorem RecState.Frame.setSigned {state : RecState} {member : Nat} {names : List Nat}
    {output : Expr} {facts : RecFacts} (h : state.Frame base K F ctx bindings done) :
    (state.setSigned member names output facts).Frame base K F ctx bindings done := by
  exact {
    modes := by simpa only [RecState.specs_setSigned] using h.modes
    annInfo := by simpa only [RecState.annInfo_setSigned] using h.annInfo
    poly := by simpa only [RecState.specs_setSigned, RecState.exports_setSigned] using h.poly
    mono := by simpa only [RecState.specs_setSigned, RecState.slots_setSigned,
      RecState.exports_setSigned, RecState.pool_setSigned,
      RecState.recPrefixCountAt_setSigned] using h.mono
    pending := by simpa only [RecState.specs_setSigned] using h.pending
    pool_nodup := by simpa only [RecState.pool_setSigned] using h.pool_nodup
    pool_ctx := by simpa only [RecState.pool_setSigned] using h.pool_ctx
    pool_rigid := by simpa only [RecState.pool_setSigned] using h.pool_rigid
    pool_soft := by simpa only [RecState.pool_setSigned] using h.pool_soft
    pool_poly := by simpa only [RecState.specs_setSigned, RecState.pool_setSigned] using h.pool_poly
    pool_pending := by simpa only [RecState.specs_setSigned, RecState.pool_setSigned] using h.pool_pending
    rigid_below := h.rigid_below
    pending_soft := by simpa only [RecState.specs_setSigned] using h.pending_soft }

private theorem RecState.Frame.poly_of_complete {state : RecState} {i : Nat} {scheme : PolyTy}
    (h : state.Frame base K F ctx bindings done) {binding : InputRecBinding}
    (hb : bindings[i]? = some binding) (ha : binding.ann = .complete scheme) :
    state.specs[i]? = some (.poly scheme) := by
  have hm := congrArg (fun xs : List (Option PolyTy) => xs[i]?) h.modes
  simp only [List.getElem?_map, hb, Option.map_some, ha, BindingAnn.recModeAnn] at hm
  cases hs : state.specs[i]? with
  | none => simp [hs] at hm
  | some spec =>
    cases spec with
    | mono ty => simp [hs, RecSpec.ann] at hm
    | poly original =>
      simp only [hs, Option.map_some, RecSpec.ann, Option.some.injEq] at hm
      cases hm
      rfl

 theorem InferRecSigned.frame_of_infer
    (h : InferRecSigned K F index frontier ctx bindings state next S final)
    (hInfer : ∀ {κ F' Ψ c e Ψ' T output ty}, e.size ≤ sizeBindings bindings →
      Infer κ F' Ψ c e Ψ' T output ty →
      ∀ {w}, w < Ψ →
      e.erase.ForallOuter (fun i => ∀ M, c.env[i]? = some M → w ∉ M.body.freeVars) 0 →
      w ∉ e.rigidVars →
      (∀ p ∈ T, w ∉ p.2.freeVars) ∧ w ∉ ty.freeVars ∧ w ∉ T.map Prod.fst)
    (hframe : state.Frame base K F ctx fullBindings done)
    (hremaining : fullBindings.drop index = bindings)
    (hmono : ∀ i ty, state.specs[i]? = some (.mono ty) → i ∈ done)
    (hpoolBelow : ∀ g ∈ state.pool, g < frontier) :
    final.Frame base K (substSoft S F) (S.onCtx ctx)
      (substInputBindings S fullBindings) done ∧
    (∀ g ∈ state.pool, (∀ p ∈ S, g ∉ p.2.freeVars) ∧ g ∉ S.map Prod.fst) := by
  match h with
  | .nil =>
    have hbindingsNil : substInputBindings [] fullBindings = fullBindings :=
      substInputBindings_eq_self_of_fixes fullBindings (fun _ _ => rfl)
    exact ⟨by simpa only [substSoft_nil, Subst.onCtx_nil, hbindingsNil] using hframe,
      by intro g hg; exact ⟨by simp, by simp⟩⟩
  | .skip _ hr =>
    apply hr.frame_of_infer
      (fun he hi => hInfer (by simp only [sizeBindings]; omega) hi) hframe
      (by simp only [List.drop_add_one_eq_tail_drop, hremaining, List.tail_cons]) hmono hpoolBelow
  | .cons _ hscope hi hu _ hr =>
    expose_names
    have hBinding : fullBindings[index]? = some { ann := .complete scheme, rhs := rhs } := by
      have hh := congrArg (fun xs : List InputRecBinding => xs[0]?) hremaining
      simpa only [List.getElem?_drop, Nat.zero_add, List.getElem?_cons_zero] using hh
    have hspec := hframe.poly_of_complete hBinding rfl
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
      have hs' : (state.specs.map (RecSpec.onSubstSource (s1 ++ s2)))[i]? = some (.mono ty) := by
        simpa only [RecState.specs_setSigned, RecState.specs_onSubst] using hs
      obtain ⟨old, ho, _⟩ := RecSpec.mono_getElem?_map_onSubstSource hs'
      exact hmono i old ho
    obtain ⟨hfinal, htailAvoid⟩ := hr.frame_of_infer
      (fun he hh => hInfer (by
        simp only [sizeBindings_substInputBindings] at he
        simp only [sizeBindings]
        omega) hh)
      hnextFrame
      (by simp only [substInputBindings_eq_map, ← List.map_drop,
        List.drop_add_one_eq_tail_drop, hremaining, List.map_cons, List.tail_cons]) hnextMono
      (by intro g hg; have hlt := hpoolBelow g hg; have := Infer.frontier_le hi; omega)
    refine ⟨?_, ?_⟩
    · simpa only [substSoft_append, Subst.onCtx_append,
        substInputBindings_append] using hfinal
    · intro g hg
      have ht := htailAvoid g hg
      exact ⟨fun p hp => (List.mem_append.mp hp).elim ((havoid g hg).1 p) (ht.1 p),
        by simpa only [List.map_append, List.mem_append, not_or] using And.intro (havoid g hg).2 ht.2⟩
 termination_by structural h


 theorem recStep_sourceSound
    {state : RecState} {past : List (List Nat)}
    (ho : OpenRecAnns component 0 frontier bindings opened openings)
    (hp : CheckRecShapes K ((state.installOpenings component openings).shapes component openings) pre)
    (hc : InferRecComponent K (substSoft pre (F ++ (openings.flatMap RecOpening.written).map Ty.fvar))
      component 0 opened (((state.installOpenings component openings).onSubst pre).rhsCtx (pre.onCtx ctx))
      (substInputBindings pre (openRecSources openings bindings))
      ((state.installOpenings component openings).onSubst pre).specs first current artifacts)
    (hf : FinishRecComponent K (softVars (substSoft (pre ++ current) F)) component
      ((pre ++ current).onCtx ctx) ((state.installOpenings component openings).onSubst (pre ++ current))
      artifacts exported)
    (hInfer : ∀ {κ F' Ψ c e Ψ' T output ty}, e.size ≤ sizeBindings bindings →
      Infer κ F' Ψ c e Ψ' T output ty → CtxWF c → TypeOfHM (T.onCtx c) output ty)
    (hframe : state.Frame base K F ctx bindings past.flatten)
    (heframe : exported.Frame base K (substSoft (pre ++ current) F) ((pre ++ current).onCtx ctx)
      (substInputBindings (pre ++ current) bindings) (past.flatten ++ component))
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
    (fun he hi => hInfer (by simpa only [sizeBindings_substInputBindings, sizeBindings_openRecSources] using he) hi)
    (fun _ hi => hi.lc) hpreCtx (hinitLC.onSubst hpreLC).1
  have hsource : (state.installOpenings component openings).SourceTyped ctx :=
    htyped.installOpenings
  have hsourceS := hsource.onSubst (pre ++ current) hSLC
  cases hf with
  | mk hresolve =>
    expose_names
    let st := (state.installOpenings component openings).onSubst (pre ++ current)
    have hstmono : ∀ i ∈ component, ∃ ty, st.specs[i]? = some (.mono ty) := by
      intro i hi
      obtain ⟨ty, ht⟩ := hmono i hi
      exact ⟨(pre ++ current).onTy ty, by
        simp only [st, RecState.specs_onSubst, RecState.specs_installOpenings,
          List.getElem?_map, ht, Option.map_some, RecSpec.onSubstSource]⟩
    apply hsourceS.exportComponent
      (hinitLC.onSubst hSLC).1
    · intro i hi
      obtain ⟨ty, ht⟩ := hmono i hi
      have hh := if_neg (hnot i hi) ▸ hframe.mono i ty ht
      simp only [RecState.exports_onSubst, RecState.exports_installOpenings,
        List.getElem?_map, hh, Option.map_some, Option.map_none]
    · exact hstmono
    · intro i hi
      have hil : i < st.slots.length := by
        rw [show st.slots.length = bindings.length from by
          calc
            st.slots.length = st.memberStates.length := RecState.slots_length st
            _ = state.memberStates.length := by
              simp only [st, RecState.onSubst, RecState.installOpenings,
                List.length_map, List.length_mapIdx]
            _ = bindings.length := hframe.memberStates_length]
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
      have ht' : ((state.installOpenings component openings).specs.map
          (RecSpec.onSubstSource (pre ++ current)))[i]? = some (.mono ty) := by
        simpa only [st, RecState.specs_onSubst] using ht
      obtain ⟨old, hold, rfl⟩ := RecSpec.mono_getElem?_map_onSubstSource ht'
      have htyPre : ((state.installOpenings component openings).onSubst pre).specs[i]? = some (.mono (pre.onTy old)) := by
        simp only [RecState.specs_onSubst, List.getElem?_map, hold, Option.map_some,
          RecSpec.onSubstSource]
      have hh := hsound i (pre.onTy old) output htyPre hout
      rw [RecState.rhsCtx_onSubst] at hh ⊢
      simpa only [Subst.onCtx_append, Subst.onTy_append] using hh
 theorem InferRecStrata.sourceSound_of_infer
    (h : InferRecStrata K F frontier ctx bindings state groups next S final)
    (hInfer : ∀ {κ F' Ψ c e Ψ' T output ty}, e.size ≤ sizeBindings bindings →
      Infer κ F' Ψ c e Ψ' T output ty →
      ∀ {w}, w < Ψ →
      e.erase.ForallOuter (fun i => ∀ M, c.env[i]? = some M → w ∉ M.body.freeVars) 0 →
      w ∉ e.rigidVars →
      (∀ p ∈ T, w ∉ p.2.freeVars) ∧ w ∉ ty.freeVars ∧ w ∉ T.map Prod.fst)
    (hvalid : RecGroups.ValidResidualGroups (bindings.map InputRecBinding.recMode) (past ++ groups))
    (hframe : state.Frame base K F ctx bindings past.flatten)
    (hlc : state.LC) (hctxWF : CtxWF ctx)
    (hbelow : state.Below frontier) (hctx : CtxBelow frontier ctx)
    (hF : ∀ t ∈ F, Ty.BelowFvars frontier t)
    (hbase : base + bindings.length ≤ frontier)
    (hbindings : ∀ binding ∈ bindings,
      ∀ v ∈ binding.ann.rigidVars ++ binding.rhs.rigidVars, v ∈ K ++ softVars F)
    (hSound : ∀ {κ F' Ψ c e Ψ' T output ty}, e.size ≤ sizeBindings bindings →
      Infer κ F' Ψ c e Ψ' T output ty → CtxWF c → TypeOfHM (T.onCtx c) output ty)
    (htyped : state.SourceTyped ctx) : final.SourceTyped (S.onCtx ctx) := by
  match h with
  | .nil => simpa only [Subst.onCtx_nil] using htyped
  | .cons ho hp hc hf hr =>
    expose_names
    obtain ⟨hstepFrame, hstepPool, _⟩ := recStep_frame ho hp hc hf hInfer hvalid hframe
      hlc hctxWF hbelow hbase hbindings
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
      have hu := (hvalid.covers_unsigned i (hvalid.bounded i hm)).mp hm
      have hu' : (bindings.map (fun binding => binding.ann.recModeAnn))[i]? = some none := by
        simpa only [RecGroups.UnsignedAt, List.getElem?_map, Option.map_map,
          Function.comp_def, InputRecBinding.recMode] using hu
      exact hframe.mono_at_unsigned hu'
    have hstepSound := recStep_sourceSound ho hp hc hf hSound hframe hstepFrame hlc hctxWF htyped hnot hmono
    have hstep : InferRecStrata K F frontier ctx bindings state [component]
        first (pre ++ current ++ []) exported := .cons ho hp hc hf .nil
    have hK : ∀ k ∈ K, k < frontier := fun k hk => by have := hframe.rigid_below k hk; omega
    have hAnnBelow : ∀ binding ∈ bindings, ∀ v ∈ binding.ann.rigidVars, v < frontier := by
      intro binding hb v hv
      exact (List.mem_append.mp (hbindings binding hb v (List.mem_append_left _ hv))).elim
        (hK v) (softVars_lt hF v)
    have hstepBelow := hstep.belowFvars_of_infer (fun _ hi => hi.belowFvars) hctx hK hF hbelow hAnnBelow
    simp only [List.append_nil] at hstepBelow
    have hstepLC := hstep.lc_of_infer (fun _ hi => hi.lc) hctxWF hlc
    simp only [List.append_nil] at hstepLC
    have hfix : ∀ k ∈ K, (pre ++ current).onTy (.fvar k) = .fvar k := by
      apply Subst.fixes_of_dom_avoids
      simpa only [List.append_nil] using hstep.dom_avoids
    have htailValid := recValid_subst (S := pre ++ current)
      (by simpa only [List.append_assoc, List.singleton_append] using hvalid :
        RecGroups.ValidResidualGroups (bindings.map InputRecBinding.recMode)
          ((past ++ [component]) ++ rest))
    have htailFrame : exported.Frame base K (substSoft (pre ++ current) F) ((pre ++ current).onCtx ctx)
        (substInputBindings (pre ++ current) bindings) (past ++ [component]).flatten := by
      simpa only [List.flatten_append, List.flatten_cons, List.flatten_nil, List.append_nil] using hstepFrame
    have hfinal := hr.sourceSound_of_infer
      (fun he hi => hInfer (by simpa only [sizeBindings_substInputBindings] using he) hi)
      htailValid htailFrame hstepLC.2 (Subst.onCtx_wf hstepLC.1 hctxWF)
      hstepBelow.2 (Subst.onCtx_below hstepBelow.1 (ho.frontier_le.trans hc.frontier_le) hctx)
      (substSoft_below hstepBelow.1 (ho.frontier_le.trans hc.frontier_le) hF)
      (by
        simp only [substInputBindings_eq_map, List.length_map]
        have := ho.frontier_le
        have := hc.frontier_le
        omega)
      (by
        intro binding hm v hv
        rw [substInputBindings_eq_map] at hm
        obtain ⟨original, ho, rfl⟩ := List.mem_map.mp hm
        rcases List.mem_append.mp hv with hv | hv
        · obtain ⟨k, hk, himage⟩ := BindingAnn.rigidVars_substTyFvars hv
          exact scope_image hfix
            (hbindings original ho k (List.mem_append_left _ hk)) himage
        · exact (show SourceScope K F original.rhs from fun v hv =>
            hbindings original ho v (List.mem_append_right _ hv)).subst
              (pre ++ current) hfix v hv)
      (fun he hi => hSound (by simpa only [sizeBindings_substInputBindings] using he) hi)
      hstepSound
    simpa only [Subst.onCtx_append] using hfinal
 termination_by structural h



 theorem RecState.Frame.all_mono_done {state : RecState} {bindings : List InputRecBinding}
    (h : state.Frame base K F ctx bindings groups.flatten)
    (hv : RecGroups.ValidResidualGroups (bindings.map InputRecBinding.recMode) groups) :
    ∀ (i : Nat) (ty : Ty), state.specs[i]? = some (.mono ty) → i ∈ groups.flatten := by
  intro i ty hs
  have hm := congrArg (fun xs : List (Option PolyTy) => xs[i]?) h.modes
  dsimp only at hm
  simp only [List.getElem?_map, hs, Option.map_some, RecSpec.ann] at hm
  have hi : i < bindings.length := by
    have hb := (List.getElem?_eq_some_iff.mp hs).1
    simpa only [h.specs_length] using hb
  exact (hv.covers_unsigned i (by simpa only [List.length_map] using hi)).mpr
    (by simpa only [RecGroups.UnsignedAt, List.getElem?_map, Option.map_map,
      Function.comp_def, InputRecBinding.recMode] using hm.symm)

theorem RecState.Frame.prefixes_mono {state : RecState} {i : Nat}
    (h : state.Frame base K F ctx bindings done)
    {binding : InputRecBinding} (hb : bindings[i]? = some binding)
    (hs : state.specs[i]? = some (.mono ty)) (hd : i ∈ done) :
    ∃ names, state.prefixes[i]? = some names ∧
      names.length = binding.ann.recPrefixCount ∧ names.Nodup ∧
      (∀ v ∈ names, v ∈ state.pool) := by
  obtain ⟨names, hslots, hlen, hnd, hsub, _⟩ := if_pos hd ▸ h.mono i ty hs
  have hcount := h.recPrefixCountAt hb
  refine ⟨names, ?_, Option.some.inj (hlen.symm.trans hcount), hnd, hsub⟩
  rw [RecState.getElem?_prefixes_of_mono state hs, hslots]
  simp [recSlotName, Function.comp_def]

theorem RecState.Frame.prefixes_wf {state : RecState} {bindings : List InputRecBinding}
    (h : state.Frame base K F ctx bindings groups.flatten)
    (hg : RecGroups.ValidResidualGroups (bindings.map InputRecBinding.recMode) groups) :
    RecPrefixesWF bindings state.specs state.prefixes state.pool := by
  refine ⟨by simp, ?_⟩
  intro i binding names hb hn
  have hi : i < state.specs.length := by
    simpa only [h.specs_length] using (List.getElem?_eq_some_iff.mp hb).1
  have hs := List.getElem?_eq_getElem hi
  cases hspec : state.specs[i] with
  | mono ty =>
    have hget : state.specs[i]? = some (.mono ty) := hspec ▸ hs
    obtain ⟨written, hp, hcount, hnd, hsub⟩ :=
      h.prefixes_mono hb hget (h.all_mono_done hg _ _ hget)
    cases Option.some.inj (hp.symm.trans hn)
    exact ⟨hcount, hnd, hsub⟩
  | poly scheme =>
    have hget : state.specs[i]? = some (.poly scheme) := hspec ▸ hs
    have hp : state.prefixes[i]? = some [] :=
      RecState.getElem?_prefixes_of_poly state hget
    cases Option.some.inj (hp.symm.trans hn)
    have hm := congrArg (fun xs : List (Option PolyTy) => xs[i]?) h.modes
    simp only [List.getElem?_map, hget, hb, Option.map_some, RecSpec.ann] at hm
    cases hann : binding.ann <;>
      simp_all [BindingAnn.recModeAnn, BindingAnn.recPrefixCount]

private theorem RecState.Frame.export_mono_prefixes {state : RecState} {i : Nat}
    (h : state.Frame base K F ctx bindings done)
    (hs : state.specs[i]? = some (.mono ty)) (hd : i ∈ done) :
    state.exports[i]? = some (some (recScheme (state.prefixes[i]?.getD []) state.pool ty)) := by
  obtain ⟨names, hslots, _, _, _, hex⟩ := if_pos hd ▸ h.mono i ty hs
  have hp : state.prefixes[i]? = some names := by
    rw [RecState.getElem?_prefixes_of_mono state hs, hslots]
    simp [recSlotName, Function.comp_def]
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
    (h : state.Frame base K F ctx bindings done) (hdone : ∀ i ∈ earlier, i ∈ done) :
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
    cases hm : state.memberStates[i]? with
    | none =>
      have hs : state.specs[i]? = none := by
        simp [RecState.getElem?_specs, hm]
      simp [hs]
    | some member =>
      have hs : state.specs[i]? = some member.spec := by
        simp [RecState.getElem?_specs, hm]
      simp only [Option.map_some, Function.comp_apply]
      cases hspec : member.spec with
      | poly scheme =>
        have hspoly : state.specs[i]? = some (.poly scheme) := by simpa [hspec] using hs
        have hex := h.poly i scheme hspoly
        rw [RecState.getElem?_exports, hm] at hex
        simp only [Option.map_some, Option.some.injEq] at hex
        have hfixed : Subst.onPolyTy (state.pool.zip (Xs.map Ty.fvar)) scheme = scheme :=
          Subst.onPolyTy_eq_self_of_dom_avoids
            (fun p hp => h.pool_poly scheme ⟨i, hspoly⟩ p.1 (List.of_mem_zip hp).1)
        by_cases hi : i ∈ earlier <;>
          simp [hi, hspoly, hex, recStageEntry, RecSpec.monoEntry, hfixed]
      | mono ty =>
        have hsmono : state.specs[i]? = some (.mono ty) := by simpa [hspec] using hs
        by_cases hi : i ∈ earlier
        · have hex := h.export_mono_prefixes hsmono (hdone i hi)
          rw [RecState.getElem?_exports, hm] at hex
          simp only [Option.map_some, Option.some.injEq] at hex
          simp [hi, hsmono, hex, recStageEntry, RecSpec.monoEntry,
            recScheme_pool_fixed]
        · simp [hi, hsmono, recStageEntry, RecSpec.monoEntry]
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

private theorem RecState.InputTrace.cofinite {state : RecState} {bindings : List InputRecBinding}
    (h : state.InputTrace (K ++ softVars F) ctx bindings groups)
    (hf : state.Frame base K F ctx bindings groups.flatten)
    (hvalid : RecGroups.ValidResidualGroups (bindings.map InputRecBinding.recMode) groups)
    (hscope : ∀ binding ∈ bindings,
      ∀ v ∈ binding.ann.rigidVars ++ binding.rhs.rigidVars, v ∈ K ++ softVars F)
    {stage : Nat} {component : List Nat} (hc : groups[stage]? = some component)
    (Xs : List Nat) (hXs : FreshNames (state.pool ++ L) state.pool.length Xs)
    {i : Nat} {binding : InputRecBinding} {names : List Nat} {ty : Ty}
    (hi : i ∈ component) (hb : bindings[i]? = some binding)
    (hn : state.prefixes[i]? = some names) (ht : state.specs[i]? = some (.mono ty)) :
    binding.ann.RecFits (recRenameNames state.pool Xs names) (Ty.renameG state.pool Xs ty) ∧
    InputTyping ((K ++ softVars F) ++ Xs)
      (recStageCtx ctx state.specs state.prefixes (groups.take stage).flatten state.pool Xs)
      (binding.rhs.openTyVars (recRenameNames state.pool Xs names)) (Ty.renameG state.pool Xs ty) := by
  let R : Subst := state.pool.zip (Xs.map Ty.fvar)
  have hRlc : ∀ p ∈ R, p.2.IsLC := pool_renaming_lc
  have hGX : ∀ g ∈ state.pool, g ∉ Xs := fun g hg hx =>
    hXs.avoid g hx (List.mem_append_left _ hg)
  have hQavoid : ∀ g ∈ state.pool, g ∉ K ++ softVars F := by
    intro g hg hm
    exact (List.mem_append.mp hm).elim (hf.pool_rigid g hg) (hf.pool_soft g hg)
  have hQfix : ∀ q ∈ K ++ softVars F, R.onTy (.fvar q) = .fvar q :=
    Subst.fixes_of_dom_avoids (fun p hp => hQavoid p.1 (List.of_mem_zip hp).1)
  obtain ⟨hfit, htyped⟩ := h stage component hc i binding ty hi hb ht
  simp only [hn, Option.getD_some] at hfit htyped
  have hprefix := (hf.prefixes_wf hvalid).member i binding names hb hn
  have himages := pool_renaming_images hf.pool_nodup hXs.length hGX hprefix.2.2
  have hfixAnn : ∀ v ∈ binding.ann.rigidVars, R.onTy (.fvar v) = .fvar v :=
    fun v hv => hQfix v (hscope binding (List.mem_of_getElem? hb) v (List.mem_append_left _ hv))
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
  rw [hstage, binding.rhs.substTyFvars_openTyVars_of_images hRlc himages,
    binding.rhs.substTyFvars_eq_self_of_fixes (fun v hv => hQfix v
      (hscope binding (List.mem_of_getElem? hb) v (List.mem_append_right _ hv)))] at hsource
  exact hsource

 theorem RecState.InputTrace.toTyping {state : RecState} {bindings : List InputRecBinding} {L : List Nat}
    (hf : state.Frame base K F ctx bindings groups.flatten) (hlc : state.LC)
    (hvalid : RecGroups.ValidResidualGroups (bindings.map InputRecBinding.recMode) groups)
    (hscope : ∀ binding ∈ bindings,
      ∀ v ∈ binding.ann.rigidVars ++ binding.rhs.rigidVars, v ∈ K ++ softVars F)
    (htrace : state.InputTrace (K ++ softVars F) ctx bindings groups)
    (hpoly : ∀ (i : Nat) (binding : InputRecBinding) (scheme : PolyTy), bindings[i]? = some binding →
      state.specs[i]? = some (.poly scheme) → ∀ Ys, FreshNames L scheme.paramCount Ys →
        InputTyping ((K ++ softVars F) ++ Ys) (recBodyCtx ctx state.specs state.prefixes state.pool)
          (binding.rhs.openTyVars Ys) (scheme.openVars Ys))
    (hbody : InputTyping (K ++ softVars F) (recBodyCtx ctx state.specs state.prefixes state.pool) body ty) :
    InputTyping (K ++ softVars F) ctx (.letRec bindings body) ty := by
  have hwf : RecSpecs.WF (bindings.map InputRecBinding.recMode) state.specs state.pool := by
    exact ⟨by simpa only [InputRecBinding.map_recMode_ann] using hf.modes,
      hf.pool_nodup, fun ty ht => hlc.1 _ ht, fun scheme hs => hlc.1 _ hs⟩
  refine InputTyping.letRec (specs := state.specs) (prefixes := state.prefixes) (groups := groups)
    (G := state.pool) (L := L) hvalid hwf (hf.prefixes_wf hvalid) ?_ hscope ?_ ?_ hpoly hbody
  · intro g hg hm
    rcases List.mem_append.mp hm with hm | hm
    · exact hf.pool_ctx g hg hm
    · exact (List.mem_append.mp hm).elim (hf.pool_rigid g hg) (hf.pool_soft g hg)
  · intro stage component hc Xs hXs i hi binding names ty hb hn ht
    exact (htrace.cofinite hf hvalid hscope hc Xs hXs hi hb hn ht).1
  · intro stage component hc Xs hXs i hi binding names ty hb hn ht
    exact (htrace.cofinite hf hvalid hscope hc Xs hXs hi hb hn ht).2


private theorem trace_prefix_lookup {state : RecState} {i : Nat} {ty : Ty} {names : List Nat}
    (hs : state.specs[i]? = some (.mono ty))
    (hn : state.slots[i]? = some (names.map Ty.fvar)) :
    state.prefixes[i]? = some names := by
  rw [RecState.getElem?_prefixes_of_mono state hs, hn]
  simp [recSlotName, Function.comp_def]

 theorem RecState.InputTrace.onSubst {state : RecState} {past : List (List Nat)}
    (hframe : state.Frame base K F ctx bindings past.flatten)
    (h : state.InputTrace (K ++ softVars F) ctx bindings past)
    (S : Subst) (hlc : ∀ p ∈ S, p.2.IsLC)
    (hK : ∀ k ∈ K, S.onTy (.fvar k) = .fvar k)
    (hpool : ∀ g ∈ state.pool, (∀ p ∈ S, g ∉ p.2.freeVars) ∧ g ∉ S.map Prod.fst) :
    (state.onSubst S).InputTrace (K ++ softVars (substSoft S F)) (S.onCtx ctx)
      (substInputBindings S bindings) past := by
  intro stage component hc i binding ty hi hb ht
  rw [substInputBindings_eq_map, List.getElem?_map] at hb
  obtain ⟨binding0, hb0, rfl⟩ := Option.map_eq_some_iff.mp hb
  have ht' : (state.specs.map (RecSpec.onSubstSource S))[i]? = some (.mono ty) := by
    simpa only [RecState.specs_onSubst] using ht
  obtain ⟨ty0, ht0, rfl⟩ := RecSpec.mono_getElem?_map_onSubstSource ht'
  have hidone : i ∈ past.flatten := List.mem_flatten.mpr ⟨component, List.mem_of_getElem? hc, hi⟩
  obtain ⟨names, hnames, _, _, hsub, _⟩ := if_pos hidone ▸ hframe.mono i ty0 ht0
  have hfix : ∀ v ∈ names, S.onTy (.fvar v) = .fvar v := by
    intro v hv
    apply Ty.substFvars_eq_self_of_no_key
    intro pair hp hk
    have heq : pair.1 = v := List.mem_singleton.mp hk
    exact (hpool v (hsub v hv)).2 (List.mem_map.mpr ⟨pair, hp, heq⟩)
  have hnewnames : (state.onSubst S).slots[i]? = some (names.map Ty.fvar) := by
    simp only [RecState.slots_onSubst, List.getElem?_map, hnames, Option.map_some, List.map_map]
    congr 1
    exact List.map_congr_left (fun v hv => hfix v hv)
  have hprefix := trace_prefix_lookup ht0 hnames
  have hnewprefix := trace_prefix_lookup ht hnewnames
  obtain ⟨hfits, htyping⟩ := h stage component hc i binding0 ty0 hi hb0 ht0
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


 theorem InferRecComponent.inputSound_of_infer
    (h : InferRecComponent K F members index frontier ctx bindings specs next S artifacts)
    (hInfer : ∀ {κ F' Ψ c e Ψ' T output ty}, e.size ≤ sizeBindings bindings →
      Infer κ F' Ψ c e Ψ' T output ty → CtxWF c →
      InputTyping (κ ++ softVars (substSoft T F')) (T.onCtx c) (e.substTyFvars T) ty)
    (hctx : CtxWF ctx) (hspec : ∀ spec ∈ specs, spec.LC) :
    ∀ (j : Nat) (binding : InputRecBinding) (target : Ty), index + j ∈ members →
      bindings[j]? = some binding → specs[j]? = some (.mono target) →
      InputTyping (K ++ softVars (substSoft S F)) (S.onCtx ctx)
        (binding.rhs.substTyFvars S) (S.onTy target) := by
  match h with
  | .nil => intro j binding target _ hb; simp at hb
  | .skipMono hn hr =>
    intro j binding target hj hb ht
    cases j with
    | zero => exact False.elim (hn (by simpa only [Nat.add_zero] using hj))
    | succ j =>
      exact hr.inputSound_of_infer
        (fun he hi => hInfer (by simp only [sizeBindings]; omega) hi)
        hctx (fun spec hm => hspec spec (List.mem_cons_of_mem _ hm)) j binding target
        (by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hj) hb ht
  | .skipPoly hr =>
    intro j binding target hj hb ht
    cases j with
    | zero => cases ht
    | succ j =>
      exact hr.inputSound_of_infer
        (fun he hi => hInfer (by simp only [sizeBindings]; omega) hi)
        hctx (fun spec hm => hspec spec (List.mem_cons_of_mem _ hm)) j binding target
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
    intro j binding target hj hb ht
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
        (fun he hi => hInfer (by simp only [sizeBindings_substInputBindings] at he; simp only [sizeBindings]; omega) hi)
        hrCtx hrSpec j
          { ann := binding.ann.substTyFvars (s1 ++ s2),
            rhs := binding.rhs.substTyFvars (s1 ++ s2) }
          ((s1 ++ s2).onTy target)
        (by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hj)
        (by simp only [substInputBindings_eq_map, List.getElem?_map, hb, Option.map_some])
        (by simp only [List.getElem?_map, ht, Option.map_some, RecSpec.onSubstSource])
      simpa only [← substSoft_append, Subst.onCtx_append, Subst.onTy_append, ← InferInput.substTyFvars_append] using htail
 termination_by structural h


/-- Signed recursive RHS checks already completed during the positional scan.
One cofinite avoidance list covers the finite checked prefix. -/
def RecState.CompleteInput (Q : List Nat) (ctx : Ctx)
    (bindings : List InputRecBinding) (checked : Nat) (state : RecState) : Prop :=
  ∃ L, ∀ (i : Nat) (binding : InputRecBinding) (scheme : PolyTy), i < checked →
    bindings[i]? = some binding → binding.ann = .complete scheme →
    ∀ Xs, FreshNames L scheme.paramCount Xs →
      InputTyping (Q ++ Xs) (state.rhsCtx ctx) (binding.rhs.openTyVars Xs) (scheme.openVars Xs)

 theorem RecState.CompleteInput.init {state : RecState} {Q : List Nat} {ctx : Ctx}
    {bindings : List InputRecBinding} : state.CompleteInput Q ctx bindings 0 :=
  ⟨[], fun _ _ _ hi => False.elim (by omega)⟩

 theorem RecState.CompleteInput.onSubst {state : RecState} {Q Q' : List Nat}
    (h : state.CompleteInput Q ctx bindings checked) (S : Subst)
    (hS : ∀ p ∈ S, p.2.IsLC)
    (hscope : ∀ k ∈ Q, ∀ v ∈ (S.onTy (.fvar k)).freeVars, v ∈ Q') :
    (state.onSubst S).CompleteInput Q' (S.onCtx ctx)
      (substInputBindings S bindings) checked := by
  obtain ⟨L, hh⟩ := h
  refine ⟨L ++ S.map Prod.fst, ?_⟩
  intro i binding scheme hi hbinding hann Xs hXs
  rw [substInputBindings_eq_map, List.getElem?_map] at hbinding
  obtain ⟨oldBinding, hb, rfl⟩ := Option.map_eq_some_iff.mp hbinding
  cases hAnn : oldBinding.ann with
  | absent | template | partialForall =>
    simp only [hAnn, BindingAnn.substTyFvars, reduceCtorEq] at hann
  | complete sigma =>
    have heq : S.onPolyTy sigma = scheme := by
      simpa only [hAnn, BindingAnn.substTyFvars, BindingAnn.complete.injEq,
        Subst.onPolyTy] using hann
    subst scheme
    have hf : FreshNames L sigma.paramCount Xs :=
      ⟨hXs.length, hXs.nodup, fun v hv hm => hXs.avoid v hv (List.mem_append_left _ hm)⟩
    have hdom : ∀ p ∈ S, p.1 ∉ Xs := fun p hp hx =>
      hXs.avoid p.1 hx (List.mem_append_right _ (List.mem_map.mpr ⟨p, hp, rfl⟩))
    have hfix := Subst.fixes_of_dom_avoids hdom
    have ht := (hh i oldBinding sigma hi hb hAnn Xs hf).onSubst_source S hS
      (K' := Q' ++ Xs) (by
        intro k hk v hv
        rcases List.mem_append.mp hk with hk | hk
        · exact List.mem_append_left _ (hscope k hk v hv)
        · rw [hfix k hk] at hv
          exact List.mem_append_right _ ((List.mem_singleton.mp hv) ▸ hk))
    simpa only [RecState.rhsCtx_onSubst, InferInput.substTyFvars_openTyVars_of_fixes _ hS hfix,
      PolyTy.openVars, Subst.onPolyTy, Subst.onTy_openVars hS hdom] using ht


/-- Completed members retain exact authored-prefix/full-output openings. -/
def RecState.Fidelity (Q : List Nat) (bindings : List InputRecBinding) (state : RecState) : Prop :=
  ∀ (i : Nat) (binding : InputRecBinding) (scheme : PolyTy) (output : Expr),
    bindings[i]? = some binding →
    state.exports[i]? = some (some scheme) → state.outputs[i]? = some (some output) →
    ∃ L, ∀ Xs, FreshNames L scheme.paramCount Xs →
      binding.ann.BindingFits scheme Xs ∧
      AnnotationCompletion (Q ++ Xs.take binding.ann.paramCount)
        (binding.rhs.openTyVars (Xs.take binding.ann.paramCount))
        (output.openTyVars Xs)

theorem RecState.Fidelity.init {bindings : List InputRecBinding} :
    (RecState.init base bindings).Fidelity Q bindings := by
  intro i binding scheme output hb he ho
  rw [RecState.init_outputs, List.getElem?_map] at ho
  cases hx : bindings[i]? <;> simp [hx] at ho

theorem RecState.Fidelity.onSubst_source {state : RecState} {S : Subst}
    (h : state.Fidelity Q bindings) (hS : ∀ p ∈ S, p.2.IsLC)
    (hscope : ∀ q ∈ Q, ∀ v ∈ (S.onTy (.fvar q)).freeVars, v ∈ Q') :
    (state.onSubst S).Fidelity Q' (substInputBindings S bindings) := by
  intro i binding scheme output hb he ho
  rw [substInputBindings_eq_map, List.getElem?_map] at hb
  obtain ⟨oldBinding, hBinding, rfl⟩ := Option.map_eq_some_iff.mp hb
  rw [RecState.exports_onSubst, List.getElem?_map] at he
  rw [RecState.outputs_onSubst, List.getElem?_map] at ho
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
      obtain ⟨L, hL⟩ := h i oldBinding oldScheme oldOutput hBinding hExport hOutput
      obtain ⟨Lc, hLc⟩ := AnnotationCompletion.signatureBinding_onSubst_source
        (ann := oldBinding.ann) (M := oldScheme) (fun Xs hf => (hL Xs hf).2) S hS hscope
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

theorem RecState.Fidelity.installOpenings {state : RecState}
    (h : state.Fidelity Q bindings) :
    (state.installOpenings members openings).Fidelity Q bindings := by
  intro i binding scheme output hb he ho
  apply h i binding scheme output hb
  · simpa only [RecState.exports_installOpenings] using he
  · simpa only [RecState.outputs_installOpenings] using ho

 theorem RecState.Fidelity.toCompletes {state : RecState}
    {bindings : List InputRecBinding} {completed : List CompletedRecMember}
    (h : state.Fidelity Q bindings) (hcompleted : state.Completed completed)
    (hlen : bindings.length = completed.length)
    (hscope : ∀ binding ∈ bindings,
      ∀ v ∈ binding.ann.rigidVars ++ binding.rhs.rigidVars, v ∈ Q)
    (hbody : AnnotationCompletion Q body bodyOut) :
    AnnotationCompletion Q (.letRec bindings body)
      (.letRec (completed.map fun member =>
        { ann := some member.scheme, rhs := member.output }) bodyOut) := by
  classical
  have hexports : state.exports = (completed.map (·.scheme)).map some := hcompleted.exports
  have houtputs : state.outputs = (completed.map (·.output)).map some := hcompleted.outputs
  have hper : ∀ i : Fin completed.length, ∃ L, ∀ Xs,
      FreshNames L (completed[i.val]).scheme.paramCount Xs →
      (bindings[i.val]'(by have := i.isLt; omega)).ann.BindingFits
        (completed[i.val]).scheme Xs ∧
      AnnotationCompletion
        (Q ++ Xs.take (bindings[i.val]'(by have := i.isLt; omega)).ann.paramCount)
        ((bindings[i.val]'(by have := i.isLt; omega)).rhs.openTyVars
          (Xs.take (bindings[i.val]'(by have := i.isLt; omega)).ann.paramCount))
        ((completed[i.val]).output.openTyVars Xs) := by
    intro i
    exact h i.val _ _ _ (List.getElem?_eq_getElem (show i.val < bindings.length by omega))
      (by simp only [hexports, List.getElem?_map,
        List.getElem?_eq_getElem i.isLt, Option.map_some])
      (by simp only [houtputs, List.getElem?_map,
        List.getElem?_eq_getElem i.isLt, Option.map_some])
  choose avoid hav using hper
  let L := (List.finRange completed.length).flatMap avoid
  have hall : ∀ (i : Nat) (binding : InputRecBinding) (member : CompletedRecMember),
      bindings[i]? = some binding → completed[i]? = some member →
      ∀ Xs, FreshNames L member.scheme.paramCount Xs →
        binding.ann.BindingFits member.scheme Xs ∧
        AnnotationCompletion (Q ++ Xs.take binding.ann.paramCount)
          (binding.rhs.openTyVars (Xs.take binding.ann.paramCount))
          (member.output.openTyVars Xs) := by
    intro i binding member hb hm Xs hXs
    have hi : i < completed.length := (List.getElem?_eq_some_iff.mp hm).1
    let j : Fin completed.length := ⟨i, hi⟩
    have hb' := List.getElem?_eq_getElem (show i < bindings.length by omega)
    have hm' := List.getElem?_eq_getElem hi
    have heqb := Option.some.inj (hb'.symm.trans hb)
    have heqm := Option.some.inj (hm'.symm.trans hm)
    subst binding member
    exact hav j Xs ⟨hXs.length, hXs.nodup, fun v hv hm => hXs.avoid v hv
      (List.mem_flatMap.mpr ⟨j, by simp, hm⟩)⟩
  have hrows : CompletedRecBindings AnnotationCompletion Q L bindings
      (completed.map fun member => { ann := member.scheme, rhs := member.output }) := by
    have build : ∀ (bs : List InputRecBinding) (cs : List CompletedRecMember),
        bs.length = cs.length →
        (∀ (i : Nat) (binding : InputRecBinding) (member : CompletedRecMember),
          bs[i]? = some binding → cs[i]? = some member →
          ∀ Xs, FreshNames L member.scheme.paramCount Xs →
            binding.ann.BindingFits member.scheme Xs ∧
            AnnotationCompletion (Q ++ Xs.take binding.ann.paramCount)
              (binding.rhs.openTyVars (Xs.take binding.ann.paramCount))
              (member.output.openTyVars Xs)) →
        CompletedRecBindings AnnotationCompletion Q L bs
          (cs.map fun member => { ann := member.scheme, rhs := member.output }) := by
      intro bs
      induction bs with
      | nil =>
          intro cs hlen _
          have hc : cs = [] := List.eq_nil_of_length_eq_zero (by simpa using hlen.symm)
          subst cs
          exact .nil
      | cons binding bs ih =>
          intro cs hlen hall
          cases cs with
          | nil => simp at hlen
          | cons member cs =>
              apply CompletedRecBindings.cons
              · intro Xs hXs
                exact (hall 0 binding member rfl rfl Xs hXs).1
              · intro Xs hXs
                exact (hall 0 binding member rfl rfl Xs hXs).2
              · apply ih cs (by simpa using hlen)
                intro i tailBinding tailMember hb hm Xs hXs
                exact hall (i + 1) tailBinding tailMember
                  (by simpa only [List.getElem?_cons_succ] using hb)
                  (by simpa only [List.getElem?_cons_succ] using hm) Xs hXs
    exact build bindings completed hlen hall
  simpa only [List.map_map, Function.comp_def] using
    AnnotationCompletion.letRec hscope hrows hbody

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
    {written : List (List Nat)} {artifacts : List (Option RecComponentArtifact)}
    (h : state.Fidelity Q bindings) (hlc : state.LC)
    (hpool : pool.Nodup) (havoid : ∀ v ∈ pool, v ∉ Q)
    (hscope : ∀ binding ∈ bindings,
      ∀ v ∈ binding.ann.rigidVars ++ binding.rhs.rigidVars, v ∈ Q)
    (hprefix : ∀ i ∈ members, ∀ binding, bindings[i]? = some binding →
      (written[i]?.getD []).length = binding.ann.recPrefixCount ∧
      (written[i]?.getD []).Nodup ∧ ∀ v ∈ written[i]?.getD [], v ∈ pool)
    (hcheck : ∀ (i : Nat) (binding : InputRecBinding) (ty : Ty) (output : Expr),
      i ∈ members → bindings[i]? = some binding →
      state.specs[i]? = some (.mono ty) → recComponentOutputAt artifacts i = some output →
      binding.ann.RecFits (written[i]?.getD []) ty ∧
      AnnotationCompletion (Q ++ written[i]?.getD [])
        (binding.rhs.openTyVars (written[i]?.getD [])) output ∧
      output.TyBvarBounded 0) :
    (state.exportComponent members written pool artifacts).Fidelity Q bindings := by
  intro i binding scheme output hb he ho
  rw [RecState.getElem?_exports_exportComponent] at he
  rw [RecState.getElem?_outputs_exportComponent] at ho
  cases hm : state.memberStates[i]? with
  | none => simp [hm] at he
  | some member =>
    have hs : state.specs[i]? = some member.spec := by
      simp only [RecState.getElem?_specs, hm, Option.map_some]
    by_cases hi : i ∈ members
    · simp only [hm, Option.map_some, if_pos hi] at he ho
      cases hspec : member.spec with
      | poly sigma => simp [hspec, RecSpec.monoTy?] at ho
      | mono ty =>
        simp only [hspec, RecSpec.completedScheme_mono, Option.some.injEq] at he
        subst scheme
        rw [hspec] at ho
        change some (do
          let raw ← recComponentOutputAt artifacts i
          pure (raw.closeTyVars (recNames (written[i]?.getD []) pool ty))) = some (some output) at ho
        obtain ⟨raw, hraw, hclose⟩ := Option.bind_eq_some_iff.mp (Option.some.inj ho)
        cases Option.some.inj hclose
        have hsmono : state.specs[i]? = some (.mono ty) := by simpa only [hspec] using hs
        obtain ⟨hfit, hcomplete, hbound⟩ := hcheck i binding ty raw hi hb hsmono hraw
        have hp := hprefix i hi binding hb
        exact hfit.cofinite_fidelity hp.1 hp.2.1 hp.2.2 hpool
          (by simpa only [hspec] using
            (hlc.1 member.spec (List.mem_map.mpr ⟨member, List.mem_of_getElem? hm, rfl⟩)))
          (fun v hv => hscope binding (List.mem_of_getElem? hb) v (List.mem_append_left _ hv))
          (fun v hv => hscope binding (List.mem_of_getElem? hb) v (List.mem_append_right _ hv))
          havoid hcomplete hbound
    · simp only [hm, Option.map_some, if_neg hi] at he ho
      have heOld : state.exports[i]? = some (some scheme) := by
        simpa only [RecState.getElem?_exports, hm, Option.map_some] using he
      have hoOld : state.outputs[i]? = some (some output) := by
        simpa only [RecState.getElem?_outputs, hm, Option.map_some] using ho
      exact h i binding scheme output hb heOld hoOld


 theorem InferRecComponent.completes_of_infer
    (h : InferRecComponent K F members index frontier ctx bindings specs next S artifacts)
    (hInfer : ∀ {κ F' Ψ c e Ψ' T output ty}, e.size ≤ sizeBindings bindings →
      Infer κ F' Ψ c e Ψ' T output ty → CtxWF c →
      AnnotationCompletion (κ ++ softVars (substSoft T F')) (e.substTyFvars T) output)
    (hctx : CtxWF ctx) (hspec : ∀ spec ∈ specs, spec.LC) :
    ∀ (j : Nat) (binding : InputRecBinding) (output : Expr), bindings[j]? = some binding →
      recComponentOutputAt artifacts j = some output →
      AnnotationCompletion (K ++ softVars (substSoft S F)) (binding.rhs.substTyFvars S) output := by
  match h with
  | .nil => intro j binding output hb; simp at hb
  | .skipMono _ hr | .skipPoly hr =>
      intro j binding output hb ho
      cases j with
      | zero => cases ho
      | succ j =>
        exact hr.completes_of_infer (fun he hi => hInfer (by simp only [sizeBindings]; omega) hi)
          hctx (fun spec hm => hspec spec (List.mem_cons_of_mem _ hm)) j binding output hb ho
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
    intro j binding output hb ho
    cases j with
    | zero =>
      cases Option.some.inj hb
      cases Option.some.inj ho
      have hrestLC : ∀ p ∈ s2 ++ s3, p.2.IsLC := fun p hp => (List.mem_append.mp hp).elim (huS p) (hrLC p)
      have hrestFix : ∀ k ∈ K, (s2 ++ s3).onTy (.fvar k) = .fvar k :=
        Subst.fixes_of_dom_avoids (fun p hp => (List.mem_append.mp hp).elim (hu.dom_avoids p) (hr.dom_avoids p))
      have hcomplete := (hInfer (by simp only [sizeBindings]; omega) hi hctx).onSubst_source
        (s2 ++ s3) hrestLC (fun k hk v hv => scope_image hrestFix hk hv)
      simpa only [← substSoft_append, ← InferInput.substTyFvars_append, List.append_assoc] using hcomplete
    | succ j =>
      simp only [List.getElem?_cons_succ] at hb ho
      have htail := hr.completes_of_infer
        (fun he hi => hInfer (by simp only [sizeBindings_substInputBindings] at he; simp only [sizeBindings]; omega) hi)
        hrCtx hrSpec j
          { ann := binding.ann.substTyFvars (s1 ++ s2),
            rhs := binding.rhs.substTyFvars (s1 ++ s2) }
          output
        (by simp only [substInputBindings_eq_map, List.getElem?_map, hb, Option.map_some]) ho
      simpa only [← substSoft_append, ← InferInput.substTyFvars_append] using htail
 termination_by structural h


private theorem trace_stage_export {state : RecState}
    (hdisj : ∀ i ∈ earlier, i ∉ members) :
    (state.exportComponent members written pool artifacts).stageCtx ctx earlier = state.stageCtx ctx earlier := by
  unfold RecState.stageCtx RecState.stageEntries
  congr 2
  apply List.ext_getElem?
  intro i
  simp only [List.getElem?_mapIdx, RecState.exportComponent]
  cases state.memberStates[i]? with
  | none => rfl
  | some member =>
    simp only [Option.map_some]
    by_cases he : i ∈ earlier
    · have hn := hdisj i he
      simp [he, hn]
    · by_cases hm : i ∈ members <;> simp [he, hm]

private theorem trace_stage_all {state : RecState}
    (h : state.Frame base K F ctx bindings done) : state.stageCtx ctx done = state.rhsCtx ctx := by
  unfold RecState.stageCtx RecState.rhsCtx
  congr 2
  apply List.ext_getElem?
  intro i
  simp only [RecState.stageEntries, RecState.entries, List.getElem?_mapIdx,
    List.getElem?_map]
  cases hm : state.memberStates[i]? with
  | none => rfl
  | some member =>
    simp only [Option.map_some]
    cases hs : member.spec with
    | poly M =>
      have hp := h.poly i M (by
        simp only [RecState.getElem?_specs, hm, Option.map_some, hs])
      rw [RecState.getElem?_exports, hm] at hp
      simp only [Option.map_some, Option.some.injEq] at hp
      simp [hp, RecSpec.monoEntry]
    | mono ty =>
      have hmono : state.specs[i]? = some (.mono ty) := by
        simp only [RecState.getElem?_specs, hm, Option.map_some, hs]
      by_cases hd : i ∈ done
      · obtain ⟨ns, _, _, _, _, he⟩ := if_pos hd ▸ h.mono i ty hmono
        rw [RecState.getElem?_exports, hm] at he
        simp only [Option.map_some, Option.some.injEq] at he
        simp [hd, he, RecSpec.monoEntry]
      · have he := if_neg hd ▸ h.mono i ty hmono
        rw [RecState.getElem?_exports, hm] at he
        simp only [Option.map_some, Option.some.injEq] at he
        simp [hd, he, RecSpec.monoEntry]

private theorem trace_install {state : RecState} {past : List (List Nat)}
    (hframe : state.Frame base K F ctx bindings past.flatten)
    (h : state.InputTrace Q ctx bindings past)
    (hnot : ∀ i ∈ members, i ∉ past.flatten) :
    (state.installOpenings members openings).InputTrace Q ctx bindings past := by
  intro stage comp hc i binding ty hi hb ht
  have hid : i ∈ past.flatten := List.mem_flatten.mpr ⟨comp,List.mem_of_getElem? hc,hi⟩
  have ht0 : state.specs[i]? = some (.mono ty) := by
    simpa only [RecState.specs_installOpenings] using ht
  obtain ⟨ns,hslot,_,_,_,_⟩ := if_pos hid ▸ hframe.mono i ty ht0
  have hold := trace_prefix_lookup (state := state) ht0 hslot
  have hnew : (state.installOpenings members openings).prefixes[i]? = some ns := by
    rw [RecState.prefixes_installOpenings_of_disjoint state hnot i hid, hold]
  have hh := h stage comp hc i binding ty hi hb ht0
  simpa only [hnew, hold, Option.getD_some, RecState.stageCtx_installOpenings] using hh

private theorem trace_export {state : RecState} {past : List (List Nat)}
    (h : state.InputTrace Q ctx bindings past)
    (hnot : ∀ i ∈ members, i ∉ past.flatten) :
    (state.exportComponent members written pool artifacts).InputTrace Q ctx bindings past := by
  intro stage comp hc i binding ty hi hb ht
  have ht0 : state.specs[i]? = some (.mono ty) := by
    simpa only [RecState.specs_exportComponent] using ht
  have hh := h stage comp hc i binding ty hi hb ht0
  rw [trace_stage_export (fun j hj hm => hnot j hm (by
    obtain ⟨group,hgroup,hj⟩ := List.mem_flatten.mp hj
    exact List.mem_flatten.mpr ⟨group,List.mem_of_mem_take hgroup,hj⟩))]
  simpa only [RecState.prefixes_exportComponent] using hh
theorem openRecSources_lookup {i : Nat} {binding : InputRecBinding}
    {opening : RecOpening} {openings : List RecOpening} {bindings : List InputRecBinding}
    (hlen : openings.length = bindings.length)
    (hb : bindings[i]? = some binding) (ho : openings[i]? = some opening) :
    (openRecSources openings bindings)[i]? =
      some { binding with rhs := binding.rhs.openTyVars opening.written } := by
  induction bindings generalizing openings i with
  | nil => simp at hb
  | cons b bs ih =>
    cases openings with
    | nil => simp at hlen
    | cons op ops =>
      cases i with
      | zero => cases Option.some.inj hb; cases Option.some.inj ho; rfl
      | succ i => exact ih (Nat.succ.inj hlen) hb ho

 theorem recStep_inputTrace
    {state : RecState}
    (ho : OpenRecAnns component 0 frontier bindings opened openings)
    (hp : CheckRecShapes K ((state.installOpenings component openings).shapes component openings) pre)
    (hc : InferRecComponent K (substSoft pre (F ++ (openings.flatMap RecOpening.written).map Ty.fvar))
      component 0 opened (((state.installOpenings component openings).onSubst pre).rhsCtx (pre.onCtx ctx))
      (substInputBindings pre (openRecSources openings bindings))
      ((state.installOpenings component openings).onSubst pre).specs first current artifacts)
    (hf : FinishRecComponent K (softVars (substSoft (pre ++ current) F)) component
      ((pre ++ current).onCtx ctx) ((state.installOpenings component openings).onSubst (pre ++ current))
      artifacts exported)
    (hInfer : ∀ {κ F' Ψ c e Ψ' T output ty}, e.size ≤ sizeBindings bindings →
      Infer κ F' Ψ c e Ψ' T output ty →
      ∀ {w}, w < Ψ →
      e.erase.ForallOuter (fun i => ∀ M, c.env[i]? = some M → w ∉ M.body.freeVars) 0 →
      w ∉ e.rigidVars →
      (∀ p ∈ T, w ∉ p.2.freeVars) ∧ w ∉ ty.freeVars ∧ w ∉ T.map Prod.fst)
    (hvalid : RecGroups.ValidResidualGroups (bindings.map InputRecBinding.recMode)
      (past ++ component :: rest))
    (hframe : state.Frame base K F ctx bindings past.flatten)
    (hlc : state.LC) (hctx : CtxWF ctx)
    (hbelow : state.Below frontier) (hbase : base + bindings.length ≤ frontier)
    (hbindings : ∀ binding ∈ bindings,
      ∀ v ∈ binding.ann.rigidVars ++ binding.rhs.rigidVars, v ∈ K ++ softVars F)
    (hInput : ∀ {κ F' Ψ c e Ψ' T output ty}, e.size ≤ sizeBindings bindings →
      Infer κ F' Ψ c e Ψ' T output ty → CtxWF c →
      InputTyping (κ ++ softVars (substSoft T F')) (T.onCtx c) (e.substTyFvars T) ty)
    (hTrace : state.InputTrace (K ++ softVars F) ctx bindings past) :
    exported.InputTrace (K ++ softVars (substSoft (pre ++ current) F)) ((pre ++ current).onCtx ctx)
      (substInputBindings (pre ++ current) bindings) (past ++ [component]) := by
  obtain ⟨heframe,hpool,_⟩ := recStep_frame ho hp hc hf hInfer hvalid hframe hlc hctx hbelow hbase hbindings
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
  have hcompInput := hc.inputSound_of_infer
    (fun he hi => hInput (by simpa only [sizeBindings_substInputBindings,sizeBindings_openRecSources] using he) hi)
    hpreCtx (hinitLC.onSubst hpreLC).1
  have hOld := (trace_install hframe hTrace hnot).onSubst hins (pre ++ current) hSLC hfixK hpool
  cases hf with
  | mk hresolve =>
    expose_names
    let st := (state.installOpenings component openings).onSubst (pre ++ current)
    have hOldEx := trace_export (members := component) (written := written)
      (pool := st.componentPool K (softVars (substSoft (pre ++ current) F)) component ((pre ++ current).onCtx ctx) written)
      (artifacts := artifacts) hOld hnot
    have hStage : (st.exportComponent component written
        (st.componentPool K (softVars (substSoft (pre ++ current) F)) component ((pre ++ current).onCtx ctx) written)
        artifacts).stageCtx ((pre ++ current).onCtx ctx) past.flatten = st.rhsCtx ((pre ++ current).onCtx ctx) := by
      rw [trace_stage_export (fun i hi hm => hnot i hm hi),RecState.stageCtx_onSubst,
        trace_stage_all hins,RecState.rhsCtx_onSubst]
    have hcurrent : ∀ i binding ty, i ∈ component →
        bindings[i]? = some binding →
        st.specs[i]? = some (.mono ty) →
        (binding.ann.substTyFvars (pre ++ current)).RecFits
          ((st.exportComponent component written
            (st.componentPool K (softVars (substSoft (pre ++ current) F)) component ((pre ++ current).onCtx ctx) written)
            artifacts).prefixes[i]?.getD []) ty ∧
        InputTyping ((K ++ softVars (substSoft (pre ++ current) F)) ++
          (st.exportComponent component written
            (st.componentPool K (softVars (substSoft (pre ++ current) F)) component ((pre ++ current).onCtx ctx) written)
            artifacts).prefixes[i]?.getD [])
          (st.rhsCtx ((pre ++ current).onCtx ctx))
          ((binding.rhs.substTyFvars (pre ++ current)).openTyVars
            ((st.exportComponent component written
              (st.componentPool K (softVars (substSoft (pre ++ current) F)) component ((pre ++ current).onCtx ctx) written)
              artifacts).prefixes[i]?.getD [])) ty := by
      intro i binding ty hi hb ht
      have ht' : ((state.installOpenings component openings).specs.map
          (RecSpec.onSubstSource (pre ++ current)))[i]? = some (.mono ty) := by
        simpa only [st, RecState.specs_onSubst] using ht
      obtain ⟨oldTy,ht0,rfl⟩ := RecSpec.mono_getElem?_map_onSubstSource ht'
      have ht0' : state.specs[i]? = some (.mono oldTy) := by
        simpa only [RecState.specs_installOpenings] using ht0
      have htFinal : (st.exportComponent component written
          (st.componentPool K (softVars (substSoft (pre ++ current) F)) component
            ((pre ++ current).onCtx ctx) written) artifacts).specs[i]? =
          some (.mono ((pre ++ current).onTy oldTy)) := by
        simpa only [RecState.specs_exportComponent] using ht
      obtain ⟨ns,hslot,_,_,_,_⟩ :=
        if_pos (List.mem_append_right _ hi) ▸ heframe.mono i _ htFinal
      have hslot0 : st.slots[i]? = some (ns.map Ty.fvar) := by
        simpa only [RecState.slots_exportComponent] using hslot
      have hprefix := trace_prefix_lookup (state := st) ht hslot0
      rw [RecState.prefixes_exportComponent]
      change (binding.ann.substTyFvars (pre ++ current)).RecFits (st.prefixes[i]?.getD []) ((pre ++ current).onTy oldTy) ∧
        InputTyping ((K ++ softVars (substSoft (pre ++ current) F)) ++ st.prefixes[i]?.getD [])
          (st.rhsCtx ((pre ++ current).onCtx ctx))
          ((binding.rhs.substTyFvars (pre ++ current)).openTyVars (st.prefixes[i]?.getD [])) ((pre ++ current).onTy oldTy)
      simp only [hprefix,Option.getD_some]
      obtain ⟨a,b,opening,hop,hopen⟩ := OpenRecAnns.selected_lookup ho (by simpa using hi) hb
      have hislot : i < state.slots.length := by
        simpa only [RecState.slots_length, RecState.specs_length] using
          (List.getElem?_eq_some_iff.mp ht0').1
      have hslots : st.slots[i]? = some (opening.written.map (fun v => (pre ++ current).onTy (.fvar v))) := by
        simpa only [st, hop, Option.getD_some, List.map_map, Function.comp_def] using
          (installed_subst_slot_value (S := pre ++ current) (openings := openings) hi hislot)
      have himages : opening.written.map (fun v => (pre ++ current).onTy (.fvar v)) = ns.map Ty.fvar :=
        Option.some.inj (hslots.symm.trans hslot0)
      have hmode : binding.ann.recModeAnn = none := by
        have hh := congrArg (fun xs : List (Option PolyTy) => xs[i]?) hframe.modes
        simpa only [List.getElem?_map,ht0',hb,Option.map_some,RecSpec.ann,Option.some.injEq] using hh.symm
      refine ⟨hopen.recFits_of_images hmode hSLC himages ?_, ?_⟩
      · intro expected hex
        have hshape : (oldTy,some expected) ∈ (state.installOpenings component openings).shapes component openings := by
          simpa only [hex] using
            (RecState.shape_mem (state := state.installOpenings component openings) hi ht0 hop)
        have hsolved := CheckRecShapes.solves hp hshape
        simpa only [Subst.onTy_append] using congrArg current.onTy hsolved
      · have hrOpened := openRecSources_lookup ho.length hb hop
        have hh := hcompInput i
          ({ ann := binding.ann.substTyFvars pre,
             rhs := (binding.rhs.openTyVars opening.written).substTyFvars pre } : InputRecBinding)
          (pre.onTy oldTy)
          (by simpa only [Nat.zero_add] using hi)
          (by simp only [substInputBindings_eq_map, List.getElem?_map, hrOpened,
            Option.map_some])
          (by simp only [RecState.specs_onSubst, List.getElem?_map, ht0,
            Option.map_some, RecSpec.onSubstSource])
        have htyping : InputTyping (K ++ softVars (substSoft (pre ++ current) (F ++ (openings.flatMap RecOpening.written).map Ty.fvar))) (st.rhsCtx ((pre ++ current).onCtx ctx))
          ((binding.rhs.substTyFvars (pre ++ current)).openTyVars ns) ((pre ++ current).onTy oldTy) := by
          dsimp only [st]
          rw [RecState.rhsCtx_onSubst]
          rw [RecState.rhsCtx_onSubst] at hh
          simpa only [← substSoft_append,Subst.onCtx_append,Subst.onTy_append,
            ← InferInput.substTyFvars_append,InferInput.substTyFvars_openTyVars_of_images _ hSLC himages] using hh
        exact htyping.scope_restrict
          ((binding.rhs.substTyFvars (pre ++ current)).openTyVars_scope
            ((show SourceScope K F binding.rhs from fun v hv =>
              hbindings binding (List.mem_of_getElem? hb) v (List.mem_append_right _ hv)).subst
                (pre ++ current) hfixK) ns)
    intro stage comp hget i binding ty hi hb ht
    by_cases hstage : stage < past.length
    · have hget0 : past[stage]? = some comp := by simpa only [List.getElem?_append_left hstage] using hget
      have hh := hOldEx stage comp hget0 i binding ty hi hb ht
      simpa only [List.take_append_of_le_length (Nat.le_of_lt hstage)] using hh
    · have hstageEq : stage = past.length := by
        have hlt := (List.getElem?_eq_some_iff.mp hget).1
        simp only [List.length_append,List.length_singleton] at hlt
        omega
      subst stage
      have hcomp : comp = component := Option.some.inj (by simpa using hget.symm)
      subst comp
      rw [substInputBindings_eq_map, List.getElem?_map] at hb
      obtain ⟨binding0,hb0,rfl⟩ := Option.map_eq_some_iff.mp hb
      have ht0 : st.specs[i]? = some (.mono ty) := by
        simpa only [RecState.specs_exportComponent] using ht
      have hh := hcurrent i binding0 ty hi hb0 ht0
      rw [← hStage] at hh
      simpa only [List.take_left] using hh
 theorem InferRecStrata.inputTrace_of_infer
    (h : InferRecStrata K F frontier ctx bindings state groups next S final)
    (hInfer : ∀ {κ F' Ψ c e Ψ' T output ty}, e.size ≤ sizeBindings bindings →
      Infer κ F' Ψ c e Ψ' T output ty →
      ∀ {w}, w < Ψ →
      e.erase.ForallOuter (fun i => ∀ M, c.env[i]? = some M → w ∉ M.body.freeVars) 0 →
      w ∉ e.rigidVars →
      (∀ p ∈ T, w ∉ p.2.freeVars) ∧ w ∉ ty.freeVars ∧ w ∉ T.map Prod.fst)
    (hvalid : RecGroups.ValidResidualGroups (bindings.map InputRecBinding.recMode) (past ++ groups))
    (hframe : state.Frame base K F ctx bindings past.flatten)
    (hlc : state.LC) (hctxWF : CtxWF ctx)
    (hbelow : state.Below frontier) (hctx : CtxBelow frontier ctx)
    (hF : ∀ t ∈ F, Ty.BelowFvars frontier t)
    (hbase : base + bindings.length ≤ frontier)
    (hbindings : ∀ binding ∈ bindings,
      ∀ v ∈ binding.ann.rigidVars ++ binding.rhs.rigidVars, v ∈ K ++ softVars F)
    (hInput : ∀ {κ F' Ψ c e Ψ' T output ty}, e.size ≤ sizeBindings bindings →
      Infer κ F' Ψ c e Ψ' T output ty → CtxWF c →
      InputTyping (κ ++ softVars (substSoft T F')) (T.onCtx c) (e.substTyFvars T) ty)
    (hTrace : state.InputTrace (K ++ softVars F) ctx bindings past) :
    final.InputTrace (K ++ softVars (substSoft S F)) (S.onCtx ctx)
      (substInputBindings S bindings) (past ++ groups) := by
  match h with
  | .nil =>
    have hbindingsNil : substInputBindings [] bindings = bindings :=
      substInputBindings_eq_self_of_fixes bindings (fun _ _ => rfl)
    simpa only [substSoft_nil,Subst.onCtx_nil,hbindingsNil,List.append_nil] using hTrace
  | .cons ho hp hc hf hr =>
    expose_names
    obtain ⟨hstepFrame, hstepPool, _⟩ := recStep_frame ho hp hc hf hInfer hvalid hframe
      hlc hctxWF hbelow hbase hbindings
    have hstepTrace := recStep_inputTrace ho hp hc hf hInfer hvalid hframe
      hlc hctxWF hbelow hbase hbindings hInput hTrace
    have hstep : InferRecStrata K F frontier ctx bindings state [component]
        first (pre ++ current ++ []) exported := .cons ho hp hc hf .nil
    have hK : ∀ k ∈ K, k < frontier := fun k hk => by have := hframe.rigid_below k hk; omega
    have hAnnBelow : ∀ binding ∈ bindings, ∀ v ∈ binding.ann.rigidVars, v < frontier := by
      intro binding hb v hv
      exact (List.mem_append.mp (hbindings binding hb v (List.mem_append_left _ hv))).elim
        (hK v) (softVars_lt hF v)
    have hstepBelow := hstep.belowFvars_of_infer (fun _ hi => hi.belowFvars) hctx hK hF hbelow hAnnBelow
    simp only [List.append_nil] at hstepBelow
    have hstepLC := hstep.lc_of_infer (fun _ hi => hi.lc) hctxWF hlc
    simp only [List.append_nil] at hstepLC
    have hfix : ∀ k ∈ K, (pre ++ current).onTy (.fvar k) = .fvar k := by
      apply Subst.fixes_of_dom_avoids
      simpa only [List.append_nil] using hstep.dom_avoids
    have htailValid := recValid_subst (S := pre ++ current)
      (by simpa only [List.append_assoc, List.singleton_append] using hvalid :
        RecGroups.ValidResidualGroups (bindings.map InputRecBinding.recMode)
          ((past ++ [component]) ++ rest))
    have htailFrame : exported.Frame base K (substSoft (pre ++ current) F) ((pre ++ current).onCtx ctx)
        (substInputBindings (pre ++ current) bindings) (past ++ [component]).flatten := by
      simpa only [List.flatten_append, List.flatten_cons, List.flatten_nil, List.append_nil] using hstepFrame
    have hfinal := hr.inputTrace_of_infer
      (fun he hi => hInfer (by simpa only [sizeBindings_substInputBindings] using he) hi)
      htailValid htailFrame hstepLC.2 (Subst.onCtx_wf hstepLC.1 hctxWF)
      hstepBelow.2 (Subst.onCtx_below hstepBelow.1 (ho.frontier_le.trans hc.frontier_le) hctx)
      (substSoft_below hstepBelow.1 (ho.frontier_le.trans hc.frontier_le) hF)
      (by
        simp only [substInputBindings_eq_map, List.length_map]
        have := ho.frontier_le
        have := hc.frontier_le
        omega)
      (by
        intro binding hm v hv
        rw [substInputBindings_eq_map] at hm
        obtain ⟨original, ho, rfl⟩ := List.mem_map.mp hm
        rcases List.mem_append.mp hv with hv | hv
        · obtain ⟨k, hk, himage⟩ := BindingAnn.rigidVars_substTyFvars hv
          exact scope_image hfix
            (hbindings original ho k (List.mem_append_left _ hk)) himage
        · exact (show SourceScope K F original.rhs from fun v hv =>
            hbindings original ho v (List.mem_append_right _ hv)).subst
              (pre ++ current) hfix v hv)
      (fun he hi => hInput (by simpa only [sizeBindings_substInputBindings] using he) hi)
      hstepTrace
    simpa only [substSoft_append,Subst.onCtx_append,substInputBindings_append,
      List.append_assoc,List.singleton_append] using hfinal
 termination_by structural h



private theorem RecState.CompleteInput.advance_skip {state : RecState}
    (h : state.CompleteInput Q ctx bindings index)
    (hb : bindings[index]? = some binding) (hm : binding.ann.recModeAnn = none) :
    state.CompleteInput Q ctx bindings (index + 1) := by
  obtain ⟨L, hh⟩ := h
  refine ⟨L, ?_⟩
  intro i current scheme hi hcurrent hann Xs hXs
  by_cases hlt : i < index
  · exact hh i current scheme hlt hcurrent hann Xs hXs
  · have heq : i = index := by omega
    subst i
    have hsame := Option.some.inj (hb.symm.trans hcurrent)
    subst current
    rw [hann] at hm
    cases hm

private theorem RecState.CompleteInput.advance_complete {state : RecState}
    (h : state.CompleteInput Q ctx bindings index)
    (hb : bindings[index]? = some binding) (ha : binding.ann = .complete scheme)
    (hhead : ∃ L, ∀ Xs, FreshNames L scheme.paramCount Xs →
      InputTyping (Q ++ Xs) (state.rhsCtx ctx) (binding.rhs.openTyVars Xs)
        (scheme.openVars Xs)) :
    state.CompleteInput Q ctx bindings (index + 1) := by
  obtain ⟨Lold, hold⟩ := h
  obtain ⟨Lhead, hhead⟩ := hhead
  refine ⟨Lold ++ Lhead, ?_⟩
  intro i source sigma hi hsource hann Xs hXs
  by_cases hlt : i < index
  · exact hold i source sigma hlt hsource hann Xs
      ⟨hXs.length, hXs.nodup, fun v hv hm => hXs.avoid v hv (List.mem_append_left _ hm)⟩
  · have heq : i = index := by omega
    subst i
    have heq := Option.some.inj (hb.symm.trans hsource)
    subst source
    cases BindingAnn.complete.inj (ha.symm.trans hann)
    exact hhead Xs ⟨hXs.length, hXs.nodup, fun v hv hm => hXs.avoid v hv (List.mem_append_right _ hm)⟩

private theorem RecState.CompleteInput.setSigned {state : RecState} {member : Nat} {names : List Nat}
    {output : Expr} {facts : RecFacts} (h : state.CompleteInput Q ctx bindings checked) :
    (state.setSigned member names output facts).CompleteInput Q ctx bindings checked := by
  obtain ⟨L, hh⟩ := h
  refine ⟨L, ?_⟩
  intro i binding scheme hi hb ha Xs hXs
  rw [RecState.rhsCtx_setSigned]
  exact hh i binding scheme hi hb ha Xs hXs

 theorem InferRecSigned.inputSound_of_infer
    (h : InferRecSigned K F index frontier ctx bindings state next S final)
    (hInfer : ∀ {κ F' Ψ c e Ψ' T output ty}, e.size ≤ sizeBindings bindings →
      Infer κ F' Ψ c e Ψ' T output ty → CtxWF c →
      InputTyping (κ ++ softVars (substSoft T F')) (T.onCtx c) (e.substTyFvars T) ty)
    (hctx : CtxWF ctx) (hstate : state.LC) (hK : ∀ k ∈ K, k < frontier)
    (hBindings : fullBindings.drop index = bindings)
    (hscope : ∀ binding ∈ fullBindings,
      ∀ v ∈ binding.ann.rigidVars, v ∈ K ++ softVars F)
    (hchecked : state.CompleteInput (K ++ softVars F) ctx fullBindings index) :
    final.CompleteInput (K ++ softVars (substSoft S F)) (S.onCtx ctx)
      (substInputBindings S fullBindings) fullBindings.length := by
  match h with
  | .nil =>
    have hlen : fullBindings.length ≤ index := by
      have hh := congrArg List.length hBindings
      simp only [List.length_drop, List.length_nil] at hh
      omega
    obtain ⟨L, hh⟩ := hchecked
    have heq : substInputBindings [] fullBindings = fullBindings := by
      apply substInputBindings_eq_self_of_fixes
      intro _ _
      rfl
    simp only [substSoft_nil, Subst.onCtx_nil, heq]
    exact ⟨L, fun i binding scheme hi => hh i binding scheme (by omega)⟩
  | .skip hnone hr =>
    expose_names
    have hb : fullBindings[index]? = some binding := by
      have hh := congrArg (fun xs : List InputRecBinding => xs[0]?) hBindings
      simpa only [List.getElem?_drop, Nat.zero_add, List.getElem?_cons_zero] using hh
    exact hr.inputSound_of_infer
      (fun he hi => hInfer (by simp only [sizeBindings]; omega) hi) hctx hstate hK
      (by simp only [List.drop_add_one_eq_tail_drop, hBindings, List.tail_cons]) hscope
      (hchecked.advance_skip hb hnone)
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
    have hBinding : fullBindings[index]? = some
        { ann := .complete scheme, rhs := rhs } := by
      have hh := congrArg (fun xs : List InputRecBinding => xs[0]?) hBindings
      simpa only [List.getElem?_drop, Nat.zero_add, List.getElem?_cons_zero] using hh
    have hpostRhs : SourceScope K (substSoft (s1 ++ s2) F) (rhs.substTyFvars (s1 ++ s2)) :=
      (show SourceScope K F rhs from hraw).subst (s1 ++ s2) hfixK
    have hpostAnn : ∀ v ∈ ((s1 ++ s2).onPolyTy scheme).body.freeVars,
        v ∈ K ++ softVars (substSoft (s1 ++ s2) F) := by
      intro v hv
      obtain ⟨old, ho, himage⟩ := Ty.mem_freeVars_substFvars_image.mp hv
      exact scope_image hfixK
        (hscope { ann := .complete scheme, rhs := rhs } (List.mem_of_getElem? hBinding) old ho)
        himage
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
    let nextBinding : InputRecBinding :=
      ⟨(BindingAnn.complete scheme).substTyFvars (s1 ++ s2),
        rhs.substTyFvars (s1 ++ s2)⟩
    have hcheckNext := hprevious.advance_complete (scheme := (s1 ++ s2).onPolyTy scheme)
      (binding := nextBinding)
      (by simp only [nextBinding, substInputBindings_eq_map, List.getElem?_map,
        hBinding, Option.map_some])
      (by simp only [nextBinding, BindingAnn.substTyFvars, Subst.onPolyTy, Subst.onTy])
      ⟨Lhead, fun Xs hXs => by
        have htake : Xs.take ((s1 ++ s2).onPolyTy scheme).paramCount = Xs := by
          rw [← hXs.length, List.take_length]
        simpa only [BindingAnn.paramCount, htake, RecState.rhsCtx_setSigned] using hhead Xs hXs⟩
    have hnextScope : ∀ binding ∈ substInputBindings (s1 ++ s2) fullBindings,
        ∀ v ∈ binding.ann.rigidVars,
          v ∈ K ++ softVars (substSoft (s1 ++ s2) F) := by
      intro binding hm v hv
      rw [substInputBindings_eq_map] at hm
      obtain ⟨old, ho, rfl⟩ := List.mem_map.mp hm
      obtain ⟨k, hk, himage⟩ := BindingAnn.rigidVars_substTyFvars hv
      exact scope_image hfixK (hscope old ho k hk) himage
    have htail := hr.inputSound_of_infer
      (fun he hh => hInfer (by
        simp only [sizeBindings_substInputBindings] at he
        simp only [sizeBindings]
        omega) hh)
      (Subst.onCtx_wf hSLC hctx) ((hstate.onSubst hSLC).setSigned)
      (fun k hk => by have := hK k hk; have := Infer.frontier_le hi; omega)
      (by simp only [substInputBindings_eq_map, ← List.map_drop,
        List.drop_add_one_eq_tail_drop, hBindings, List.map_cons, List.tail_cons])
      hnextScope hcheckNext
    have hfullLength : (substInputBindings (s1 ++ s2) fullBindings).length =
        fullBindings.length := by
      simp only [substInputBindings_eq_map, List.length_map]
    rw [hfullLength] at htail
    simpa only [substSoft_append, Subst.onCtx_append, ← substInputBindings_append,
      List.length_map] using htail
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

 theorem recStep_fidelity
    {state : RecState}
    (ho : OpenRecAnns component 0 frontier bindings opened openings)
    (hp : CheckRecShapes K ((state.installOpenings component openings).shapes component openings) pre)
    (hc : InferRecComponent K (substSoft pre (F ++ (openings.flatMap RecOpening.written).map Ty.fvar))
      component 0 opened (((state.installOpenings component openings).onSubst pre).rhsCtx (pre.onCtx ctx))
      (substInputBindings pre (openRecSources openings bindings))
      ((state.installOpenings component openings).onSubst pre).specs first current artifacts)
    (hf : FinishRecComponent K (softVars (substSoft (pre ++ current) F)) component
      ((pre ++ current).onCtx ctx) ((state.installOpenings component openings).onSubst (pre ++ current))
      artifacts exported)
    (hInfer : ∀ {κ F' Ψ c e Ψ' T output ty}, e.size ≤ sizeBindings bindings →
      Infer κ F' Ψ c e Ψ' T output ty →
      ∀ {w}, w < Ψ →
      e.erase.ForallOuter (fun i => ∀ M, c.env[i]? = some M → w ∉ M.body.freeVars) 0 →
      w ∉ e.rigidVars →
      (∀ p ∈ T, w ∉ p.2.freeVars) ∧ w ∉ ty.freeVars ∧ w ∉ T.map Prod.fst)
    (hvalid : RecGroups.ValidResidualGroups (bindings.map InputRecBinding.recMode)
      (past ++ component :: rest))
    (hframe : state.Frame base K F ctx bindings past.flatten)
    (hlc : state.LC) (hctx : CtxWF ctx)
    (hbelow : state.Below frontier) (hbase : base + bindings.length ≤ frontier)
    (hbindings : ∀ binding ∈ bindings,
      ∀ v ∈ binding.ann.rigidVars ++ binding.rhs.rigidVars, v ∈ K ++ softVars F)
    (hComplete : ∀ {κ F' Ψ c e Ψ' T output ty}, e.size ≤ sizeBindings bindings →
      Infer κ F' Ψ c e Ψ' T output ty → CtxWF c →
      AnnotationCompletion (κ ++ softVars (substSoft T F')) (e.substTyFvars T) output)
    (hSound : ∀ {κ F' Ψ c e Ψ' T output ty}, e.size ≤ sizeBindings bindings →
      Infer κ F' Ψ c e Ψ' T output ty → CtxWF c → TypeOfHM (T.onCtx c) output ty)
    (hFidelity : state.Fidelity (K ++ softVars F) bindings) :
    exported.Fidelity (K ++ softVars (substSoft (pre ++ current) F))
      (substInputBindings (pre ++ current) bindings) := by
  obtain ⟨heframe,hpool,_⟩ := recStep_frame ho hp hc hf hInfer hvalid hframe hlc hctx hbelow hbase hbindings
  have hinitLC := hlc.installOpenings (members := component) (openings := openings)
  have hpreLC := hp.lc (RecState.shapes_lc hinitLC ho.expected_lc)
  have hpreCtx := (hinitLC.onSubst hpreLC).rhsCtx (Subst.onCtx_wf hpreLC hctx)
  have hcurrentLC := hc.lc_of_infer (fun _ hi => hi.lc) hpreCtx (hinitLC.onSubst hpreLC).1
  have hSLC : ∀ p ∈ pre ++ current, p.2.IsLC :=
    fun p hm => (List.mem_append.mp hm).elim (hpreLC p) (hcurrentLC p)
  have hfixK : ∀ k ∈ K, (pre ++ current).onTy (.fvar k) = .fvar k :=
    Subst.fixes_of_dom_avoids (fun p hp' => (List.mem_append.mp hp').elim (hp.dom_avoids p) (hc.dom_avoids p))
  have hcompComplete := hc.completes_of_infer
    (fun he hi => hComplete (by simpa only [sizeBindings_substInputBindings,sizeBindings_openRecSources] using he) hi)
    hpreCtx (hinitLC.onSubst hpreLC).1
  have hcompSound := hc.sourceSound_of_infer
    (fun he hi => hSound (by simpa only [sizeBindings_substInputBindings,sizeBindings_openRecSources] using he) hi)
    (fun _ hi => hi.lc) hpreCtx (hinitLC.onSubst hpreLC).1
  have hfidInstall : (state.installOpenings component openings).Fidelity (K ++ softVars F) bindings :=
    hFidelity.installOpenings
  have hfidS := hfidInstall.onSubst_source hSLC (fun k hk v hv => scope_image hfixK hk hv)
  have hScopeS : ∀ binding ∈ substInputBindings (pre ++ current) bindings,
      ∀ v ∈ binding.ann.rigidVars ++ binding.rhs.rigidVars,
        v ∈ K ++ softVars (substSoft (pre ++ current) F) := by
    intro binding hb v hv
    rw [substInputBindings_eq_map] at hb
    obtain ⟨old,hold,rfl⟩ := List.mem_map.mp hb
    rcases List.mem_append.mp hv with hv | hv
    · obtain ⟨k,hk,himage⟩ := BindingAnn.rigidVars_substTyFvars hv
      exact scope_image hfixK
        (hbindings old hold k (List.mem_append_left _ hk)) himage
    · exact (show SourceScope K F old.rhs from fun v hv =>
        hbindings old hold v (List.mem_append_right _ hv)).subst
          (pre ++ current) hfixK v hv
  cases hf with
  | mk hresolve =>
    expose_names
    let st := (state.installOpenings component openings).onSubst (pre ++ current)
    have hprefixData : ∀ i ∈ component,
        ∃ ns, written[i]? = some ns ∧ st.slots[i]? = some (ns.map Ty.fvar) ∧
          (st.exportComponent component written
            (st.componentPool K (softVars (substSoft (pre ++ current) F)) component
              ((pre ++ current).onCtx ctx) written) artifacts).recPrefixCountAt i = some ns.length ∧
          ns.Nodup ∧ ∀ v ∈ ns, v ∈ st.componentPool K (softVars (substSoft (pre ++ current) F)) component ((pre ++ current).onCtx ctx) written := by
      intro i hi
      have hm : i ∈ (past ++ component :: rest).flatten := by
        simp only [List.flatten_append,List.flatten_cons,List.mem_append];tauto
      have hu := (hvalid.covers_unsigned i (hvalid.bounded i hm)).mp hm
      have hu' : (bindings.map (fun binding => binding.ann.recModeAnn))[i]? = some none := by
        simpa only [RecGroups.UnsignedAt, List.getElem?_map, Option.map_map,
          Function.comp_def, InputRecBinding.recMode] using hu
      obtain ⟨ty,ht⟩ := hframe.mono_at_unsigned hu'
      have htS : st.specs[i]? = some (.mono ((pre ++ current).onTy ty)) := by
        simp only [st, RecState.specs_onSubst, RecState.specs_installOpenings,
          List.getElem?_map, ht, Option.map_some, RecSpec.onSubstSource]
      have htFinal : (st.exportComponent component written
          (st.componentPool K (softVars (substSoft (pre ++ current) F)) component
            ((pre ++ current).onCtx ctx) written) artifacts).specs[i]? =
          some (.mono ((pre ++ current).onTy ty)) := by
        simpa only [RecState.specs_exportComponent] using htS
      obtain ⟨ns,hslot,hcount,hnd,hsub,_⟩ :=
        if_pos (List.mem_append_right _ hi) ▸ heframe.mono i _ htFinal
      have hslot0 : st.slots[i]? = some (ns.map Ty.fvar) := by
        simpa only [RecState.slots_exportComponent] using hslot
      obtain ⟨resolved,hr,hh⟩ := hresolve.lookup i (ns.map Ty.fvar) hslot0
      rw [Nat.zero_add,if_pos hi] at hh
      have heq := fidelity_fvar_map_inj hh.1
      subst resolved
      exact ⟨ns,hr,hslot0,hcount,hnd,hsub⟩
    apply hfidS.exportComponent (hinitLC.onSubst hSLC) heframe.pool_nodup
      (fun v hv hq => (List.mem_append.mp hq).elim (heframe.pool_rigid v hv) (heframe.pool_soft v hv))
      hScopeS
    · intro i hi binding hb
      obtain ⟨ns,hn,_,hcount,hnd,hsub⟩ := hprefixData i hi
      have hsource := heframe.recPrefixCountAt hb
      have hlen : ns.length = binding.ann.recPrefixCount :=
        Option.some.inj (hcount.symm.trans hsource)
      simpa only [hn, Option.getD_some] using And.intro hlen (And.intro hnd hsub)
    · intro i binding ty output hi hb ht hout
      rw [substInputBindings_eq_map, List.getElem?_map] at hb
      obtain ⟨binding0,hb0,rfl⟩ := Option.map_eq_some_iff.mp hb
      have ht' : ((state.installOpenings component openings).specs.map
          (RecSpec.onSubstSource (pre ++ current)))[i]? = some (.mono ty) := by
        simpa only [st, RecState.specs_onSubst] using ht
      obtain ⟨oldTy,ht0,rfl⟩ := RecSpec.mono_getElem?_map_onSubstSource ht'
      have ht0' : state.specs[i]? = some (.mono oldTy) := by
        simpa only [RecState.specs_installOpenings] using ht0
      obtain ⟨ns,hn,hslot,_,_,_⟩ := hprefixData i hi
      simp only [hn,Option.getD_some]
      obtain ⟨a,b,opening,hop,hopen⟩ := ho.selected_lookup (by simpa using hi) hb0
      have hislot : i < state.slots.length := by
        simpa only [RecState.slots_length, RecState.specs_length] using
          (List.getElem?_eq_some_iff.mp ht0').1
      have hslots : st.slots[i]? = some (opening.written.map (fun v => (pre ++ current).onTy (.fvar v))) := by
        simpa only [st, hop, Option.getD_some, List.map_map, Function.comp_def] using
          (installed_subst_slot_value (S := pre ++ current) (openings := openings) hi hislot)
      have himages : opening.written.map (fun v => (pre ++ current).onTy (.fvar v)) = ns.map Ty.fvar :=
        Option.some.inj (hslots.symm.trans hslot)
      have hmode : binding0.ann.recModeAnn = none := by
        have hh := congrArg (fun xs : List (Option PolyTy) => xs[i]?) hframe.modes
        simpa only [List.getElem?_map,ht0',hb0,Option.map_some,RecSpec.ann,Option.some.injEq] using hh.symm
      refine ⟨hopen.recFits_of_images hmode hSLC himages ?_, ?_, ?_⟩
      · intro expected hex
        have hshape : (oldTy,some expected) ∈ (state.installOpenings component openings).shapes component openings := by
          simpa only [hex] using
            (RecState.shape_mem (state := state.installOpenings component openings) hi ht0 hop)
        have hsolved := hp.solves hshape
        simpa only [Subst.onTy_append] using congrArg current.onTy hsolved
      · have hrOpened := openRecSources_lookup ho.length hb0 hop
        have hh := hcompComplete i
          ({ ann := binding0.ann.substTyFvars pre,
             rhs := (binding0.rhs.openTyVars opening.written).substTyFvars pre } : InputRecBinding)
          output (by simp only [substInputBindings_eq_map, List.getElem?_map,
            hrOpened,Option.map_some]) hout
        have hcomplete : AnnotationCompletion (K ++ softVars (substSoft (pre ++ current) (F ++ (openings.flatMap RecOpening.written).map Ty.fvar)))
            ((binding0.rhs.substTyFvars (pre ++ current)).openTyVars ns) output := by
          simpa only [← substSoft_append,← InferInput.substTyFvars_append,
            InferInput.substTyFvars_openTyVars_of_images _ hSLC himages] using hh
        exact hcomplete.scope_restrict ((binding0.rhs.substTyFvars (pre ++ current)).openTyVars_scope
          ((show SourceScope K F binding0.rhs from fun v hv =>
            hbindings binding0 (List.mem_of_getElem? hb0) v (List.mem_append_right _ hv)).subst
              (pre ++ current) hfixK) ns)
      · have hh := hcompSound i (pre.onTy oldTy) output
          (by simp only [RecState.specs_onSubst, List.getElem?_map, ht0,
            Option.map_some, RecSpec.onSubstSource])
          hout
        exact hh.tyBvarBounded

 theorem InferRecStrata.fidelity_of_infer
    (h : InferRecStrata K F frontier ctx bindings state groups next S final)
    (hInfer : ∀ {κ F' Ψ c e Ψ' T output ty}, e.size ≤ sizeBindings bindings →
      Infer κ F' Ψ c e Ψ' T output ty →
      ∀ {w}, w < Ψ →
      e.erase.ForallOuter (fun i => ∀ M, c.env[i]? = some M → w ∉ M.body.freeVars) 0 →
      w ∉ e.rigidVars →
      (∀ p ∈ T, w ∉ p.2.freeVars) ∧ w ∉ ty.freeVars ∧ w ∉ T.map Prod.fst)
    (hvalid : RecGroups.ValidResidualGroups (bindings.map InputRecBinding.recMode) (past ++ groups))
    (hframe : state.Frame base K F ctx bindings past.flatten)
    (hlc : state.LC) (hctxWF : CtxWF ctx)
    (hbelow : state.Below frontier) (hctx : CtxBelow frontier ctx)
    (hF : ∀ t ∈ F, Ty.BelowFvars frontier t)
    (hbase : base + bindings.length ≤ frontier)
    (hbindings : ∀ binding ∈ bindings,
      ∀ v ∈ binding.ann.rigidVars ++ binding.rhs.rigidVars, v ∈ K ++ softVars F)
    (hComplete : ∀ {κ F' Ψ c e Ψ' T output ty}, e.size ≤ sizeBindings bindings →
      Infer κ F' Ψ c e Ψ' T output ty → CtxWF c →
      AnnotationCompletion (κ ++ softVars (substSoft T F')) (e.substTyFvars T) output)
    (hSound : ∀ {κ F' Ψ c e Ψ' T output ty}, e.size ≤ sizeBindings bindings →
      Infer κ F' Ψ c e Ψ' T output ty → CtxWF c → TypeOfHM (T.onCtx c) output ty)
    (hFidelity : state.Fidelity (K ++ softVars F) bindings) :
    final.Fidelity (K ++ softVars (substSoft S F))
      (substInputBindings S bindings) := by
  match h with
  | .nil =>
    have hbindingsNil : substInputBindings [] bindings = bindings :=
      substInputBindings_eq_self_of_fixes bindings (fun _ _ => rfl)
    simpa only [substSoft_nil,Subst.onCtx_nil,hbindingsNil,List.append_nil] using hFidelity
  | .cons ho hp hc hf hr =>
    expose_names
    obtain ⟨hstepFrame, hstepPool, _⟩ := recStep_frame ho hp hc hf hInfer hvalid hframe
      hlc hctxWF hbelow hbase hbindings
    have hstepFidelity := recStep_fidelity ho hp hc hf hInfer hvalid hframe
      hlc hctxWF hbelow hbase hbindings hComplete hSound hFidelity
    have hstep : InferRecStrata K F frontier ctx bindings state [component]
        first (pre ++ current ++ []) exported := .cons ho hp hc hf .nil
    have hK : ∀ k ∈ K, k < frontier := fun k hk => by have := hframe.rigid_below k hk; omega
    have hAnnBelow : ∀ binding ∈ bindings, ∀ v ∈ binding.ann.rigidVars, v < frontier := by
      intro binding hb v hv
      exact (List.mem_append.mp (hbindings binding hb v (List.mem_append_left _ hv))).elim
        (hK v) (softVars_lt hF v)
    have hstepBelow := hstep.belowFvars_of_infer (fun _ hi => hi.belowFvars) hctx hK hF hbelow hAnnBelow
    simp only [List.append_nil] at hstepBelow
    have hstepLC := hstep.lc_of_infer (fun _ hi => hi.lc) hctxWF hlc
    simp only [List.append_nil] at hstepLC
    have hfix : ∀ k ∈ K, (pre ++ current).onTy (.fvar k) = .fvar k := by
      apply Subst.fixes_of_dom_avoids
      simpa only [List.append_nil] using hstep.dom_avoids
    have htailValid := recValid_subst (S := pre ++ current)
      (by simpa only [List.append_assoc, List.singleton_append] using hvalid :
        RecGroups.ValidResidualGroups (bindings.map InputRecBinding.recMode)
          ((past ++ [component]) ++ rest))
    have htailFrame : exported.Frame base K (substSoft (pre ++ current) F) ((pre ++ current).onCtx ctx)
        (substInputBindings (pre ++ current) bindings) (past ++ [component]).flatten := by
      simpa only [List.flatten_append, List.flatten_cons, List.flatten_nil, List.append_nil] using hstepFrame
    have hfinal := hr.fidelity_of_infer
      (fun he hi => hInfer (by simpa only [sizeBindings_substInputBindings] using he) hi)
      htailValid htailFrame hstepLC.2 (Subst.onCtx_wf hstepLC.1 hctxWF)
      hstepBelow.2 (Subst.onCtx_below hstepBelow.1 (ho.frontier_le.trans hc.frontier_le) hctx)
      (substSoft_below hstepBelow.1 (ho.frontier_le.trans hc.frontier_le) hF)
      (by
        simp only [substInputBindings_eq_map, List.length_map]
        have := ho.frontier_le
        have := hc.frontier_le
        omega)
      (by
        intro binding hm v hv
        rw [substInputBindings_eq_map] at hm
        obtain ⟨original, ho, rfl⟩ := List.mem_map.mp hm
        rcases List.mem_append.mp hv with hv | hv
        · obtain ⟨k, hk, himage⟩ := BindingAnn.rigidVars_substTyFvars hv
          exact scope_image hfix
            (hbindings original ho k (List.mem_append_left _ hk)) himage
        · exact (show SourceScope K F original.rhs from fun v hv =>
            hbindings original ho v (List.mem_append_right _ hv)).subst
              (pre ++ current) hfix v hv)
      (fun he hi => hComplete (by simpa only [sizeBindings_substInputBindings] using he) hi)
      (fun he hi => hSound (by simpa only [sizeBindings_substInputBindings] using he) hi)
      hstepFidelity
    simpa only [substSoft_append,Subst.onCtx_append,substInputBindings_append,
      List.append_assoc,List.singleton_append] using hfinal
 termination_by structural h





 theorem InferRecSigned.type_fields
    (h : InferRecSigned K F index frontier ctx bindings state next S final) :
    final.specs = (state.onSubst S).specs ∧ final.slots = (state.onSubst S).slots ∧
    final.exports = (state.onSubst S).exports ∧ final.pool = state.pool := by
  match h with
  | .nil =>
    have hs : RecSpec.onSubstSource [] = id := funext RecSpec.onSubstSource_nil
    have ht : Subst.onTy [] = id := funext (fun _ => Subst.onTy_nil)
    have hp : Subst.onPolyTy [] = id := funext (fun _ => Subst.onPolyTy_nil _)
    simp [RecState.specs_onSubst, RecState.slots_onSubst,
      RecState.exports_onSubst, hs, ht, hp]
  | .skip _ hr => exact hr.type_fields
  | .cons _ _ _ _ _ hr =>
    obtain ⟨hspec, hslots, hexports, hpool⟩ := hr.type_fields
    refine ⟨?_, ?_, ?_, hpool⟩
    · exact hspec.trans (by
        simp only [RecState.specs_onSubst, RecState.specs_setSigned, List.map_map]
        apply List.map_congr_left
        intro spec _
        simp only [Function.comp_apply, RecSpec.onSubstSource_append, List.append_assoc])
    · exact hslots.trans (by
        simp only [RecState.slots_onSubst, RecState.slots_setSigned, List.map_map]
        apply List.map_congr_left
        intro names _
        simp only [Function.comp_apply, List.map_map]
        apply List.map_congr_left
        intro ty _
        simp only [Function.comp_apply, Subst.onTy_append, List.append_assoc])
    · exact hexports.trans (by
        simp only [RecState.exports_onSubst, RecState.exports_setSigned, List.map_map]
        apply List.map_congr_left
        intro entry _
        cases entry <;> simp only [Function.comp_apply, Option.map_none, Option.map_some,
          Subst.onPolyTy_append, List.append_assoc])
 termination_by structural h

 theorem RecState.InputTrace.congr_types {state other : RecState}
    (h : state.InputTrace Q ctx bindings past)
    (hspec : other.specs = state.specs) (hslots : other.slots = state.slots)
    (hexports : other.exports = state.exports) : other.InputTrace Q ctx bindings past := by
  have hp : other.prefixes = state.prefixes :=
    RecState.prefixes_eq_of_specs_slots_eq hspec hslots
  have he : ∀ earlier, other.stageEntries earlier = state.stageEntries earlier :=
    fun earlier => RecState.stageEntries_eq_of_specs_exports_eq hspec hexports earlier
  simpa only [RecState.InputTrace, hspec, hp, RecState.stageCtx, he] using h

private theorem RecState.Fidelity.setSigned_complete {state : RecState} {member : Nat} {names : List Nat}
    {output : Expr} {facts : RecFacts} {scheme : PolyTy} {binding : InputRecBinding}
    (h : state.Fidelity Q bindings)
    (hb : bindings[member]? = some binding) (ha : binding.ann = .complete scheme)
    (he : state.exports[member]? = some (some scheme)) (hm : member < state.outputs.length)
    (hnew : ∃ L, ∀ Xs, FreshNames L scheme.paramCount Xs →
      AnnotationCompletion (Q ++ Xs) (binding.rhs.openTyVars Xs) ((output.closeTyVars names).openTyVars Xs)) :
    (state.setSigned member names output facts).Fidelity Q bindings := by
  intro i current sigma completed hcurrent hex hout
  rw [RecState.exports_setSigned] at hex
  by_cases hi : member = i
  · subst i
    rw [RecState.getElem?_outputs_setSigned_self state member names output facts hm] at hout
    have hcurrentEq := Option.some.inj (hb.symm.trans hcurrent)
    subst current
    have hsigmaEq := Option.some.inj (Option.some.inj (he.symm.trans hex))
    subst sigma
    simp only [Option.some.injEq] at hout
    subst completed
    obtain ⟨L, hh⟩ := hnew
    refine ⟨L, ?_⟩
    intro Xs hXs
    have hparam : binding.ann.paramCount = scheme.paramCount := by
      rw [ha]
      rfl
    have htake : Xs.take binding.ann.paramCount = Xs := by
      rw [hparam, ← hXs.length, List.take_length]
    refine ⟨?_, ?_⟩
    · rw [ha]
      exact BindingAnn.SignatureFits.complete
    simpa only [htake] using hh Xs hXs
  · rw [RecState.getElem?_outputs_setSigned_of_ne state member i names output facts (Ne.symm hi)] at hout
    exact h i current sigma completed hcurrent hex hout

 theorem InferRecSigned.completes_of_infer
    (h : InferRecSigned K F index frontier ctx bindings state next S final)
    (hInfer : ∀ {κ F' Ψ c e Ψ' T output ty}, e.size ≤ sizeBindings bindings →
      Infer κ F' Ψ c e Ψ' T output ty → CtxWF c →
      AnnotationCompletion (κ ++ softVars (substSoft T F')) (e.substTyFvars T) output)
    (hSource : ∀ {κ F' Ψ c e Ψ' T output ty}, e.size ≤ sizeBindings bindings →
      Infer κ F' Ψ c e Ψ' T output ty → CtxWF c → TypeOfHM (T.onCtx c) output ty)
    (hctx : CtxWF ctx) (hstate : state.LC) (hK : ∀ k ∈ K, k < frontier)
    (hBindings : fullBindings.drop index = bindings)
    (hOutLen : state.outputs.length = fullBindings.length)
    (hExports : ∀ (j : Nat) (binding : InputRecBinding) (scheme : PolyTy),
      bindings[j]? = some binding → binding.ann = .complete scheme →
      state.exports[index + j]? = some (some scheme))
    (hfid : state.Fidelity (K ++ softVars F) fullBindings) :
    final.Fidelity (K ++ softVars (substSoft S F))
      (substInputBindings S fullBindings) := by
  match h with
  | .nil =>
    have heq : substInputBindings [] fullBindings = fullBindings :=
      substInputBindings_eq_self_of_fixes fullBindings (fun _ _ => rfl)
    simpa only [substSoft_nil, heq] using hfid
  | .skip _ hr =>
    exact hr.completes_of_infer
      (fun he hi => hInfer (by simp only [sizeBindings]; omega) hi)
      (fun he hi => hSource (by simp only [sizeBindings]; omega) hi)
      hctx hstate hK
      (by simp only [List.drop_add_one_eq_tail_drop, hBindings, List.tail_cons]) hOutLen
      (by intro j binding scheme hb ha; simpa only [Nat.add_assoc, Nat.add_comm 1 j] using
            hExports (j + 1) binding scheme hb ha) hfid
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
    have hBinding : fullBindings[index]? = some { ann := .complete scheme, rhs := rhs } := by
      have hh := congrArg (fun xs : List InputRecBinding => xs[0]?) hBindings
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
    let nextBinding : InputRecBinding :=
      ⟨(BindingAnn.complete scheme).substTyFvars (s1 ++ s2),
        rhs.substTyFvars (s1 ++ s2)⟩
    have hnew := hprevious.setSigned_complete (member := index) (names := freshVars frontier scheme.paramCount)
      (output := output.substTyFvars s2) (facts := bodyFacts.onSubst s2)
      (scheme := (s1 ++ s2).onPolyTy scheme)
      (binding := nextBinding)
      (by simp only [nextBinding, substInputBindings_eq_map, List.getElem?_map,
        hBinding, Option.map_some])
      (by simp only [nextBinding, BindingAnn.substTyFvars, Subst.onPolyTy, Subst.onTy])
      (by
        have hh : state.exports[index]? = some (some scheme) := by
          simpa only [Nat.add_zero] using hExports 0
            { ann := .complete scheme, rhs := rhs } scheme rfl rfl
        simp only [RecState.exports_onSubst, List.getElem?_map, hh, Option.map_some])
      (by simpa only [RecState.outputs_onSubst, List.length_map, hOutLen] using
        (List.getElem?_eq_some_iff.mp hBinding).1)
      ⟨Lhead, fun Xs hXs => by
        have htake : Xs.take ((s1 ++ s2).onPolyTy scheme).paramCount = Xs := by
          rw [← hXs.length, List.take_length]
        simpa only [BindingAnn.paramCount, htake] using hhead Xs hXs⟩
    have htail := hr.completes_of_infer
      (fun he hh => hInfer (by
        simp only [sizeBindings_substInputBindings] at he
        simp only [sizeBindings]
        omega) hh)
      (fun he hh => hSource (by
        simp only [sizeBindings_substInputBindings] at he
        simp only [sizeBindings]
        omega) hh)
      (Subst.onCtx_wf hSLC hctx) ((hstate.onSubst hSLC).setSigned)
      (fun k hk => by have := hK k hk; have := Infer.frontier_le hi; omega)
      (by simp only [substInputBindings_eq_map, ← List.map_drop,
        List.drop_add_one_eq_tail_drop, hBindings, List.map_cons, List.tail_cons])
      (by
        simp only [RecState.outputs_length, RecState.setSigned, RecState.onSubst,
          substInputBindings_eq_map, List.length_mapIdx, List.length_map]
        simpa only [RecState.outputs_length] using hOutLen)
      (by
        intro j binding sigma hb ha
        rw [substInputBindings_eq_map, List.getElem?_map] at hb
        obtain ⟨oldBinding, hold, rfl⟩ := Option.map_eq_some_iff.mp hb
        cases hAnn : oldBinding.ann with
        | absent | template | partialForall =>
          simp only [hAnn, BindingAnn.substTyFvars, reduceCtorEq] at ha
        | complete original =>
          have hsigma : (s1 ++ s2).onPolyTy original = sigma := by
            simpa only [hAnn, BindingAnn.substTyFvars, BindingAnn.complete.injEq,
              Subst.onPolyTy, Subst.onTy] using ha
          subst sigma
          have hh := hExports (j + 1) oldBinding original hold hAnn
          simp only [RecState.exports_setSigned, RecState.exports_onSubst, List.getElem?_map, Nat.add_assoc,
            Nat.add_comm 1 j, hh, Option.map_some]) hnew
    simpa only [substSoft_append, ← substInputBindings_append,
      List.length_map] using htail
 termination_by structural h

end

/-! ## Infer -/

section

 theorem RecState.Frame.rhsCtx_eq_recBodyCtx {state : RecState}
    (h : state.Frame base K F ctx bindings done)
    (hdone : ∀ i ty, state.specs[i]? = some (.mono ty) → i ∈ done) :
    state.rhsCtx ctx = recBodyCtx ctx state.specs state.prefixes state.pool := by
  have heq : state.entries = recCompletedSchemes state.specs state.prefixes state.pool := by
    apply List.ext_getElem?
    intro i
    cases hm : state.memberStates[i]? with
    | none =>
      simp [RecState.entries, RecState.getElem?_specs, recCompletedSchemes, hm]
    | some member =>
      have hs : state.specs[i]? = some member.spec := by
        simp only [RecState.getElem?_specs, hm, Option.map_some]
      have hex : state.exports[i]? = some member.exported := by
        simp only [RecState.getElem?_exports, hm, Option.map_some]
      cases hspec : member.spec with
      | poly sigma =>
        have hspoly : state.specs[i]? = some (.poly sigma) := by simpa only [hspec] using hs
        have hh := h.poly i sigma hspoly
        have hex' : member.exported = some sigma := Option.some.inj (hex.symm.trans hh)
        simp [RecState.entries, recCompletedSchemes, hm, hspoly, hspec, hex',
          RecSpec.monoEntry, RecSpec.completedScheme]
      | mono ty =>
        have hsmono : state.specs[i]? = some (.mono ty) := by simpa only [hspec] using hs
        obtain ⟨names, hslots, _, _, _, hexported⟩ :=
          if_pos (hdone i ty hsmono) ▸ h.mono i ty hsmono
        have hp : state.prefixes[i]? = some names := by
          rw [RecState.getElem?_prefixes_of_mono state hsmono, hslots]
          simp [recSlotName, Function.comp_def]
        have hprefix : member.prefix = names := by
          rw [RecState.getElem?_prefixes, hm] at hp
          exact Option.some.inj hp
        have hex' : member.exported = some (recScheme names state.pool ty) :=
          Option.some.inj (hex.symm.trans hexported)
        simp [RecState.entries, recCompletedSchemes, hm, hsmono, hspec, hex', hprefix,
          RecSpec.monoEntry, RecSpec.completedScheme]
  simp only [RecState.rhsCtx, recBodyCtx, heq]

private theorem forall₂_self_map {α β} {R : α → β → Prop} {f : α → β} :
    ∀ {xs : List α}, (∀ x ∈ xs, R x (f x)) → List.Forall₂ R xs (xs.map f)
  | [], _ => .nil
  | _ :: _, h => .cons (h _ (List.mem_cons_self ..))
      (forall₂_self_map (fun x hx => h x (List.mem_cons_of_mem _ hx)))

/-- Whole substitutions transport a completed branch and its constructor witness. -/
theorem TypeOfMatchBranch.onSubst
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

theorem InferBranches.nil_iff
    (h : InferBranches K F frontier ctx scrutTy resultTy branches next subst completed) :
    completed = [] ↔ branches = [] := by cases h <;> simp




mutual
/-- Successful elaboration produces ordinary annotated Core typing. The proof
constructs the typing from the inference derivation; it does not recheck output
with the Core inferer. -/
private theorem InferCert.sourceSound_raw (h : Infer K F frontier ctx input next subst output ty) :
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
  | @InferCert.lambda K F ann body frontier ctx seeded _ _ hs hb =>
      intro hctx
      have hbodyCtx : CtxWF
          { ctx with env := PolyTy.mkTrivial seeded.param :: ctx.env } := by
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
          Subst.onPolyTy, PolyTy.mkTrivial] using hb.sourceSound_raw hbodyCtx
  | @InferCert.app K F f arg frontier ctx functionResult argumentResult unifier _ hf ha hu =>
      intro hctx
      have hs1 := (hf.lc hctx).2
      have haCtx := Subst.onCtx_wf hs1 hctx
      have hs2 := (ha.lc haCtx).2
      have hs3 := hu.unifies.lc (Subst.onTy_lc hs2 (hf.lc hctx).1)
        (.arrow (ha.lc haCtx).1 .fvar)
      have hfTyped := TypeOfHM.onSubst (argumentResult.subst ++ unifier)
        (fun pair hp => (List.mem_append.mp hp).elim (hs2 pair) (hs3 pair)) (hf.sourceSound_raw hctx)
      have haTyped := TypeOfHM.onSubst unifier hs3 (ha.sourceSound_raw haCtx)
      have heq : (argumentResult.subst ++ unifier).onTy functionResult.ty =
          .arrow (unifier.onTy argumentResult.ty)
            (unifier.onTy (.fvar argumentResult.frontier)) := by
        simpa only [Unifies, Subst.onTy_append, Subst.onTy_arrow] using hu.unifies.unifies
      rw [heq] at hfTyped
      simp only [Subst.onCtx_append] at hfTyped
      simpa only [Subst.onCtx_append] using TypeOfHM.app hfTyped haTyped
  | @InferCert.letIn K F ann rhs body frontier ctx
      ⟨first, s1, rhsOut, rhsTy⟩ ⟨checked, sCheck⟩ ⟨next, s2, bodyOut, bodyTy⟩
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
      have rhsTyped := TypeOfHM.onSubst sCheck hsCheck (hr.sourceSound_raw hctx)
      have rhsGeneral := TypeOfHM.generaliseAnnotated
        (names := genVars (K ++ softVars (substSoft (s1 ++ sCheck) F)) (sCheck.onCtx (s1.onCtx ctx)).env (sCheck.onTy rhsTy))
        rhsTyped genVars_nodup
        (fun name hn => genVars_not_mem hn)
      obtain ⟨avoid, rhsFinal⟩ := GeneralisesTo.onSubst_annotated
        (genScheme_wf checkedTyLC) rhsGeneral s2 hs2
      have bodyTyped := hb.sourceSound_raw bodyCtxWF
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

  | @InferCert.letSignature K F ann rhs body written frontier ctx
      ⟨first, s1, rhsOut, rhsTy⟩ ⟨checked, sCheck⟩ ⟨next, s2, bodyOut, bodyTy⟩
      hraw hprefix havoid hr hc hescape hb =>
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
    have rhsTyped := TypeOfHM.onSubst sCheck hsCheck (hr.sourceSound_raw hctx)
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
    have bodyTyped := hb.sourceSound_raw bodyCtxWF
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
  | @InferCert.letRec K F bindings body frontier ctx completed
      ⟨first, s1, state1⟩ ⟨second, s2, state2⟩ ⟨next, s3, bodyOut, bodyTy⟩
      hscope hann hstrata hsigned hcompleted hbody =>
    intro hctxWF
    let groups := RecGroup.inferenceSccs (bindings.map InputRecBinding.recMode)
    obtain ⟨hraw, hctx, hK, hFvars⟩ := hscope
    have hF : ∀ t ∈ F, Ty.BelowFvars frontier t := by
      intro t ht
      apply Ty.BelowFvars.of_freeVars_lt
      intro v hv
      exact hFvars v (TyList.mem_freeVars_iff.mpr ⟨t, ht, hv⟩)
    have hbindingscope : ∀ binding ∈ bindings,
        ∀ v ∈ binding.ann.rigidVars ++ binding.rhs.rigidVars, v ∈ K ++ softVars F := by
      intro binding hb v hv
      exact hraw v (List.mem_append_left _ ((List.mem_append.mp hv).elim
        (ann_rigid_mem hb) (rigidBindingVars_mem hb)))
    have hbindingsbelow : ∀ binding ∈ bindings, ∀ v ∈ binding.ann.rigidVars, v < frontier := by
      intro binding hb v hv
      exact (List.mem_append.mp (hbindingscope binding hb v (List.mem_append_left _ hv))).elim
        (hK v) (hFvars v)
    have hvalid := RecGroup.inferenceSccs_valid
      (bindings := bindings.map InputRecBinding.recMode)
    have hinitFrame := RecState.Frame.init hctx
      hbindingsbelow hK hFvars
    have hinitLC := RecState.LC.init (base := frontier)
      (fun binding hb scheme heq =>
        hann scheme (List.mem_map.mpr ⟨binding, hb, heq⟩))
    have hinitBelow : (RecState.init frontier bindings).Below (frontier + bindings.length) := by
      exact RecState.Below.init hbindingsbelow
    have hctxSeed : CtxBelow (frontier + bindings.length) ctx :=
      fun M hm => (hctx M hm).mono (by omega)
    have hFSeed : ∀ t ∈ F, Ty.BelowFvars (frontier + bindings.length) t :=
      fun t ht => (hF t ht).mono (by omega)
    have hvalid0 : RecGroups.ValidResidualGroups (bindings.map InputRecBinding.recMode) ([] ++ groups) := hvalid
    obtain ⟨hframe1, _⟩ := hstrata.frame_of_infer
      (fun _ hi => hi.sourceLocality) hvalid0 hinitFrame hinitLC hctxWF hinitBelow hctxSeed hFSeed
      (by omega) hbindingscope
    have htyped1 := hstrata.sourceSound_of_infer
      (fun _ hi => hi.sourceLocality) hvalid0 hinitFrame hinitLC hctxWF hinitBelow hctxSeed hFSeed
      (by omega) hbindingscope (fun _ hi => hi.sourceSound_raw) RecState.SourceTyped.init
    obtain ⟨hS1, hLC1⟩ := hstrata.lc_of_infer (fun _ hi => hi.lc) hctxWF hinitLC
    obtain ⟨hB1, hBelow1⟩ := hstrata.belowFvars_of_infer (fun _ hi => hi.belowFvars)
      hctxSeed (fun k hk => Nat.lt_of_lt_of_le (hK k hk) (by omega)) hFSeed hinitBelow
      (fun binding hb v hv => Nat.lt_of_lt_of_le (hbindingsbelow binding hb v hv) (by omega))
    have hvalid1 := recValid_subst hvalid s1
    have hdone1 := hframe1.all_mono_done hvalid1
    obtain ⟨hframe2, _⟩ := hsigned.frame_of_infer
      (fun _ hi => hi.sourceLocality) hframe1 (by simp) hdone1 hBelow1.2.2.2
    have htyped2 := hsigned.sourceSound_of_infer
      (fun he hi => hi.sourceSound_raw) (Subst.onCtx_wf hS1 hctxWF) hLC1 htyped1
      (fun j binding scheme hb ha => by
        simpa only [Nat.zero_add] using hframe1.complete_export hb ha)
    obtain ⟨hS2, hLC2⟩ := hsigned.lc_of_infer (fun _ hi => hi.lc) (Subst.onCtx_wf hS1 hctxWF) hLC1
    have hbodyCtx := hLC2.rhsCtx (Subst.onCtx_wf hS2 (Subst.onCtx_wf hS1 hctxWF))
    rw [← Subst.onCtx_append] at hbodyCtx
    obtain ⟨_, hS3⟩ := hbody.lc hbodyCtx
    have hbodyTyped := hbody.sourceSound_raw hbodyCtx
    have htypedFinal := htyped2.onSubst s3 hS3
    have hexports : state2.exports =
        (completed.map CompletedRecMember.scheme).map some := hcompleted.exports
    have houtputs : state2.outputs =
        (completed.map CompletedRecMember.output).map some := hcompleted.outputs
    let completedFinal : List CompletedRecMember := completed.map fun member =>
      { member with
        scheme := s3.onPolyTy member.scheme
        output := member.output.substTyFvars s3 }
    have hfinalExports : (state2.onSubst s3).exports =
        (completedFinal.map CompletedRecMember.scheme).map some := by
      simp only [RecState.exports_onSubst, hexports, completedFinal, List.map_map,
        Function.comp_def]
      apply List.map_congr_left
      intro scheme _
      rfl
    have hfinalOutputs : (state2.onSubst s3).outputs =
        (completedFinal.map CompletedRecMember.output).map some := by
      simp only [RecState.outputs_onSubst, houtputs, completedFinal, List.map_map,
        Function.comp_def]
      apply List.map_congr_left
      intro output _
      rfl
    have hresult := htypedFinal.letRec (completed := completedFinal)
      hfinalExports hfinalOutputs
      (by simpa only [RecState.rhsCtx_onSubst, Subst.onCtx_append] using hbodyTyped)
    simpa only [Subst.onCtx_append, completedFinal, List.map_map,
      Function.comp_def] using hresult
  | .match_ _ hs hne hb =>
    intro hctx
    have hs1 := (hs.lc hctx).2
    have hbr := hb.lc (Subst.onCtx_wf hs1 hctx) (hs.lc hctx).1 .fvar
    have hscrut := TypeOfHM.onSubst _ hbr.2 (hs.sourceSound_raw hctx)
    have hbranches := hb.sourceSound (Subst.onCtx_wf hs1 hctx) (hs.lc hctx).1 .fvar
    simpa only [Subst.onCtx_append] using
      TypeOfHM.match_ hscrut (fun hnil => hne (substInputBranches_eq_nil _ _ |>.mp (hb.nil_iff.mp hnil))) hbranches
termination_by (input.size, 0)
decreasing_by
  all_goals simp only [sizeBindings_substInputBindings] at *
  all_goals (simp only [InferInput.size, InferInput.size_openTyVars, InferInput.size_substTyFvars, sizeBranches_substInputBranches]; omega)

theorem InferBranches.sourceSound
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
        (fun p hp => (List.mem_append.mp hp).elim (hs2 p) (hs3 p)) (hb.sourceSound_raw hctx)
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
      have head0 := TypeOfMatchBranch.mk hspec (Subst.onCtx_branchBindings hs1) (hb.sourceSound_raw hbodyWF)
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

theorem InferCert.sourceSound {request : InferRequest} {result : InferResult}
    (h : InferCert request result) (hctx : CtxWF request.ctx) :
    TypeOfHM (result.subst.onCtx request.ctx) result.completedExpr result.ty := by
  cases request
  cases result
  exact InferCert.sourceSound_raw h hctx

theorem Infer.sourceSound (h : Infer K F frontier ctx input next subst output ty) :
    CtxWF ctx → TypeOfHM (subst.onCtx ctx) output ty :=
  InferCert.sourceSound_raw h


/-- Every stored completed RHS retains the erased source at its original slot. -/
def RecState.Erases (erased : List Expr) (state : RecState) : Prop :=
  state.outputs.length = erased.length ∧
  ∀ (i : Nat) (output : Expr), state.outputs[i]? = some (some output) → erased[i]? = some output.erase

 theorem RecState.Erases.init {base : Nat} {bindings : List InputRecBinding}
    (hlen : bindings.length = erased.length) : (RecState.init base bindings).Erases erased := by
  constructor
  · simpa only [RecState.init_outputs, List.length_map] using hlen
  · intro i output hget
    simp only [RecState.init_outputs, List.getElem?_map] at hget
    cases hb : bindings[i]? <;> simp [hb] at hget

 theorem RecState.Erases.onSubst {state : RecState} (h : state.Erases erased) (S : Subst) :
    (state.onSubst S).Erases erased := by
  refine ⟨by simpa only [RecState.outputs_onSubst, List.length_map] using h.1, ?_⟩
  intro i output hget
  rw [RecState.outputs_onSubst, List.getElem?_map] at hget
  obtain ⟨old, ho, heq⟩ := Option.map_eq_some_iff.mp hget
  obtain ⟨rhs, hrhs, rfl⟩ := Option.map_eq_some_iff.mp heq
  simpa only [Expr.erase_substTyFvars] using h.2 i rhs (hrhs ▸ ho)

 theorem RecState.Erases.installOpenings {state : RecState} (h : state.Erases erased) :
    (state.installOpenings members openings).Erases erased := by
  simpa only [RecState.Erases, RecState.outputs_installOpenings] using h

 theorem RecState.Erases.exportComponent {state : RecState} (h : state.Erases erased)
    {artifacts : List (Option RecComponentArtifact)} {pool : List Nat}
    (hout : ∀ (i : Nat) (output : Expr), recComponentOutputAt artifacts i = some output →
      erased[i]? = some output.erase) :
    (state.exportComponent members written pool artifacts).Erases erased := by
  refine ⟨by simpa only [RecState.outputs_length, RecState.exportComponent,
    List.length_mapIdx] using h.1, ?_⟩
  intro i output hget
  rw [RecState.getElem?_outputs_exportComponent] at hget
  obtain ⟨old, hold, heq⟩ := Option.map_eq_some_iff.mp hget
  by_cases hi : i ∈ members
  · simp only [if_pos hi] at heq
    obtain ⟨ty, _, hbind⟩ := Option.bind_eq_some_iff.mp heq
    obtain ⟨rhs, hrhs, hclose⟩ := Option.bind_eq_some_iff.mp hbind
    change recComponentOutputAt artifacts i = some rhs at hrhs
    cases Option.some.inj hclose
    simpa only [Expr.erase_closeTyVars] using hout i rhs hrhs
  · simp only [if_neg hi] at heq
    apply h.2 i output
    simp only [RecState.getElem?_outputs, hold, Option.map_some, heq]

 theorem FinishRecComponent.erases
    (h : FinishRecComponent K soft members ctx state artifacts final)
    (hstate : state.Erases erased)
    (hout : ∀ (i : Nat) (output : Expr), recComponentOutputAt artifacts i = some output →
      erased[i]? = some output.erase) :
    final.Erases erased := by
  cases h
  exact hstate.exportComponent hout

 theorem RecState.Erases.setSigned {state : RecState} (h : state.Erases erased)
    {facts : RecFacts} (hout : erased[member]? = some output.erase) :
    (state.setSigned member names output facts).Erases erased := by
  refine ⟨by simpa only [RecState.outputs_length, RecState.setSigned,
    List.length_mapIdx] using h.1, ?_⟩
  intro i rhs hget
  by_cases hi : member = i
  · subst i
    have hlt : member < state.outputs.length := by
      rw [h.1]
      exact List.getElem?_eq_some_iff.mp hout |>.1
    rw [RecState.getElem?_outputs_setSigned_self state member names output facts hlt] at hget
    cases Option.some.inj (Option.some.inj hget)
    simpa only [Expr.erase_closeTyVars] using hout
  · rw [RecState.getElem?_outputs_setSigned_of_ne state member i names output facts (Ne.symm hi)] at hget
    exact h.2 i rhs hget

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

@[simp] theorem erase_openRecSources (openings : List RecOpening) (bindings : List InputRecBinding) :
    (openRecSources openings bindings).map (fun binding => binding.rhs.erase) =
      bindings.map (fun binding => binding.rhs.erase) := by
  induction bindings generalizing openings with
  | nil => cases openings <;> rfl
  | cons binding rest ih =>
    cases openings with
    | nil => rfl
    | cons opening openings => simp only [openRecSources, List.map_cons, InferInput.erase_openTyVars, ih]

@[simp] theorem erase_map_subst_inputs (bindings : List InputRecBinding) (S : Subst) :
    (substInputBindings S bindings).map (fun binding => binding.rhs.erase) =
      bindings.map (fun binding => binding.rhs.erase) := by
  simp only [substInputBindings_eq_map, List.map_map, Function.comp_def,
    InferInput.erase_substTyFvars]

 theorem InferRecComponent.erase_of_infer
    (h : InferRecComponent K F members index frontier ctx bindings specs next S artifacts)
    (hInfer : ∀ {κ F' Ψ c e Ψ' T output ty}, e.size ≤ sizeBindings bindings →
      Infer κ F' Ψ c e Ψ' T output ty → output.erase = e.erase) :
    ∀ (i : Nat) (output : Expr), recComponentOutputAt artifacts i = some output →
      (bindings.map (fun binding => binding.rhs.erase))[i]? = some output.erase := by
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
        cases Option.some.inj hget
        simp only [List.map_cons, List.getElem?_cons_zero, RecComponentArtifact.onSubst,
          Expr.erase_substTyFvars,
          hInfer (by simp only [sizeBindings]; omega) hi]
      | succ i =>
        have hh := hr.erase_of_infer
          (fun he h => hInfer (by simp only [sizeBindings_substInputBindings] at he; simp only [sizeBindings]; omega) h)
          i output hget
        simpa only [erase_map_subst_inputs] using hh
 termination_by structural h

 theorem InferRecStrata.erase_of_infer
    (h : InferRecStrata K F frontier ctx bindings state groups next S final)
    (hInfer : ∀ {κ F' Ψ c e Ψ' T output ty}, e.size ≤ sizeBindings bindings →
      Infer κ F' Ψ c e Ψ' T output ty → output.erase = e.erase)
    (hstate : state.Erases (bindings.map (fun binding => binding.rhs.erase))) :
    final.Erases (bindings.map (fun binding => binding.rhs.erase)) := by
  match h with
  | .nil => exact hstate
  | .cons _ _ hc he hr =>
      have hcomponent := hc.erase_of_infer
        (fun hsize h => hInfer (by simpa only [sizeBindings_substInputBindings, sizeBindings_openRecSources] using hsize) h)
      have hready := he.erases ((hstate.installOpenings).onSubst _) (by
        simpa only [erase_map_subst_inputs, erase_openRecSources] using hcomponent)
      have htail := hr.erase_of_infer
        (fun hsize h => hInfer (by simpa only [sizeBindings_substInputBindings] using hsize) h)
        (by simpa only [erase_map_subst_inputs] using hready)
      simpa only [erase_map_subst_inputs] using htail
 termination_by structural h

private theorem erased_remaining_tail {erased : List Expr} {binding : InputRecBinding}
    {bindings : List InputRecBinding}
    (h : (binding :: bindings).map (fun binding => binding.rhs.erase) = erased.drop index) :
    bindings.map (fun binding => binding.rhs.erase) = erased.drop (index + 1) := by
  have ht := congrArg (List.drop 1) h
  simpa only [List.map_cons, List.drop_succ_cons, List.drop_zero, List.drop_drop] using ht

 theorem InferRecSigned.erase_of_infer
    (h : InferRecSigned K F index frontier ctx bindings state next S final)
    (hInfer : ∀ {κ F' Ψ c e Ψ' T output ty}, e.size ≤ sizeBindings bindings →
      Infer κ F' Ψ c e Ψ' T output ty → output.erase = e.erase)
    (hstate : state.Erases erased)
    (hremaining : bindings.map (fun binding => binding.rhs.erase) = erased.drop index) :
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
        (fun he h => hInfer (by simp only [sizeBindings_substInputBindings] at he; simp only [sizeBindings]; omega) h)
        hready (by simpa only [erase_map_subst_inputs] using erased_remaining_tail hremaining)
 termination_by structural h


mutual
/-- Inference completes annotations and binders while preserving runtime syntax. -/
private theorem InferCert.erase_raw (h : Infer K F frontier ctx input next subst output ty) :
    output.erase = input.erase := by
  match h with
  | .primLitUnit | .primLitInt | .primLitNat | .primLitChar | .primBinOpIntAdd | .primBinOpIntSub | .primBinOpIntLt _ _ _ _ | .primBinOpCharLt _ _ _ _ | .var _ | .ctor _ => simp only [Expr.erase, InferInput.erase]
  | .lambda _ _ hb =>
      simpa only [lambdaOutput, Expr.erase, InferInput.erase] using
        congrArg (Expr.lambda none) hb.erase_raw
  | .app _ hf ha _ =>
      simp only [Expr.erase, Expr.erase_substTyFvars, InferInput.erase, hf.erase_raw, ha.erase_raw, InferInput.erase_substTyFvars]
  | .letIn _ hr _ hb =>
      simp only [letOutput, Expr.erase, Expr.erase_substTyFvars,
        Expr.erase_closeTyVars, InferInput.erase, hr.erase_raw, hb.erase_raw, InferInput.erase_substTyFvars]
  | .letSignature _ _ _ hr _ _ hb =>
      simp only [letOutput, Expr.erase, Expr.erase_substTyFvars,
        Expr.erase_closeTyVars, InferInput.erase, hr.erase_raw, hb.erase_raw, InferInput.erase_openTyVars, InferInput.erase_substTyFvars]
  | .match_ _ hs _ hb =>
      simp only [Expr.erase, Expr.erase_substTyFvars, InferInput.erase, hs.erase_raw, hb.erase, eraseBranches_substInputBranches]
  | @InferCert.letRec K F bindings body frontier ctx completed
      ⟨first, s1, state1⟩ ⟨second, s2, state2⟩ ⟨next, s3, bodyOut, bodyTy⟩
      _ _ hs hp hcompleted hb =>
      have hstate1 := hs.erase_of_infer (fun _ hi => hi.erase_raw)
        (RecState.Erases.init (erased := bindings.map (fun binding => binding.rhs.erase))
          (by simp))
      have hstate2 := hp.erase_of_infer (fun _ hi => hi.erase_raw)
        (by simpa only [erase_map_subst_inputs] using hstate1)
        (by simp only [erase_map_subst_inputs, List.drop_zero])
      have houtputs := hstate2.outputs_eq hcompleted.outputs
      have hrows : completed.map (fun member =>
          ({ ann := none, rhs := member.output.erase } : CoreRecBinding)) =
          eraseBindings bindings := by
        rw [eraseBindings_eq_map_local]
        simpa only [List.map_map, Function.comp_def] using congrArg
          (List.map (fun rhs : Expr => ({ ann := none, rhs := rhs } : CoreRecBinding))) houtputs
      simp only [Expr.erase_letRec, InferInput.erase, List.map_map, Function.comp_def,
        Expr.erase_substTyFvars, hb.erase_raw, InferInput.erase_substTyFvars, hrows]
termination_by (input.size, 0)
decreasing_by
  all_goals simp only [sizeBindings_substInputBindings] at *
  all_goals (simp only [InferInput.size, InferInput.size_openTyVars, InferInput.size_substTyFvars, sizeBranches_substInputBranches]; omega)

theorem InferBranches.erase
    (h : InferBranches K F frontier ctx scrutTy resultTy branches next subst completed) :
    completed.map (fun pe => (pe.1, pe.2.erase)) = eraseBranches branches := by
  match h with
  | .nil => rfl
  | .consWild _ hb _ hr =>
      simp only [List.map_cons, eraseBranches, Expr.erase_substTyFvars, hb.erase_raw, hr.erase, eraseBranches_substInputBranches]
  | .cons _ _ _ _ hb _ hr =>
      simp only [List.map_cons, eraseBranches, Expr.erase_substTyFvars, hb.erase_raw, hr.erase, InferInput.erase_substTyFvars, eraseBranches_substInputBranches]
termination_by (sizeBranches branches, 0)
decreasing_by all_goals (simp only [sizeBranches, InferInput.size_substTyFvars, sizeBranches_substInputBranches]; omega)
end

theorem InferCert.erase {request : InferRequest} {result : InferResult}
    (h : InferCert request result) : result.completedExpr.erase = request.input.erase := by
  cases request
  cases result
  exact InferCert.erase_raw h

theorem Infer.erase (h : Infer K F frontier ctx input next subst output ty) :
    output.erase = input.erase :=
  InferCert.erase_raw h

theorem Infer.sound (h : Infer K F frontier ctx input next subst output ty) (hctx : CtxWF ctx) :
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
private theorem InferCert.inputSound_source_raw (h : Infer K F frontier ctx input next subst output ty) :
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
  | @InferCert.lambda K F ann body frontier ctx seeded bodyResult _ hs hb =>
      intro hctx
      have hbodyCtx : CtxWF
          { ctx with env := PolyTy.mkTrivial seeded.param :: ctx.env } := by
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
          exact (hs.fits original rfl).substTyFvars bodyResult.subst
      · intro template heq v hv
        cases ann with
        | none => cases heq
        | some original =>
          cases heq
          obtain ⟨old, hold, hv⟩ := TyTemplate.rigidVars_substTyFvars hv
          exact scope_image (Subst.fixes_of_dom_avoids hb.dom_avoids) (hs.rigid original rfl old hold) hv
      · simpa only [Subst.onCtx, Subst.onEnv, List.map_cons, Subst.onPolyTy,
          PolyTy.mkTrivial] using hb.inputSound_source_raw hbodyCtx
  | @InferCert.app K F f arg frontier ctx functionResult argumentResult unifier _ hf ha hu =>
      intro hctx
      have hs1 := (hf.lc hctx).2
      have haCtx := Subst.onCtx_wf hs1 hctx
      have hs2 := (ha.lc haCtx).2
      have hs3 := hu.unifies.lc (Subst.onTy_lc hs2 (hf.lc hctx).1)
        (.arrow (ha.lc haCtx).1 .fvar)
      have hfTyped := (hf.inputSound_source_raw hctx).onSubst_soft
        (argumentResult.subst ++ unifier)
        (fun pair hp => (List.mem_append.mp hp).elim (hs2 pair) (hs3 pair))
        (fun pair hp => (List.mem_append.mp hp).elim (ha.dom_avoids pair) (hu.dom_avoids pair))
      have haTyped := (ha.inputSound_source_raw haCtx).onSubst_soft
        unifier hs3 hu.dom_avoids
      have heq : (argumentResult.subst ++ unifier).onTy functionResult.ty =
          .arrow (unifier.onTy argumentResult.ty)
            (unifier.onTy (.fvar argumentResult.frontier)) := by
        simpa only [Unifies, Subst.onTy_append, Subst.onTy_arrow] using hu.unifies.unifies
      rw [heq] at hfTyped
      simp only [Subst.onCtx_append] at hfTyped
      simp only [← substSoft_append, ← InferInput.substTyFvars_append, List.append_assoc] at hfTyped haTyped
      simpa only [Subst.onCtx_append, InferInput.substTyFvars, List.append_assoc] using InputTyping.app hfTyped haTyped
  | @InferCert.letIn K F ann rhs body frontier ctx
      ⟨first, s1, rhsOut, rhsTy⟩ ⟨checked, sCheck⟩ ⟨next, s2, bodyOut, bodyTy⟩
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
      have rhsTyped := (hr.inputSound_source_raw hctx).onSubst_soft sCheck hsCheck hc.dom_avoids
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
      have bodyTyped := hb.inputSound_source_raw bodyCtxWF
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

  | @InferCert.letSignature K F ann rhs body written frontier ctx
      ⟨first, s1, rhsOut, rhsTy⟩ ⟨checked, sCheck⟩ ⟨next, s2, bodyOut, bodyTy⟩
      hscope hprefix havoid hr hc hescape hb =>
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
    have rhsTyped0 := (hr.inputSound_source_raw hctx).onSubst_soft sCheck hsCheck hc.dom_avoids
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
    have bodyTyped := hb.inputSound_source_raw bodyCtxWF
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

  | @InferCert.letRec K F bindings body frontier ctx completed
      ⟨first, s1, state1⟩ ⟨second, s2, state2⟩ ⟨next, s3, bodyOut, bodyTy⟩
      hscope hann hstrata hsigned hcompleted hbody =>
    intro hctxWF
    let groups := RecGroup.inferenceSccs (bindings.map InputRecBinding.recMode)
    obtain ⟨hraw, hctx, hK, hFvars⟩ := hscope
    have hF : ∀ t ∈ F, Ty.BelowFvars frontier t := by
      intro t ht
      apply Ty.BelowFvars.of_freeVars_lt
      intro v hv
      exact hFvars v (TyList.mem_freeVars_iff.mpr ⟨t, ht, hv⟩)
    have hbindingscope : ∀ binding ∈ bindings,
        ∀ v ∈ binding.ann.rigidVars ++ binding.rhs.rigidVars, v ∈ K ++ softVars F := by
      intro binding hb v hv
      exact hraw v (List.mem_append_left _ ((List.mem_append.mp hv).elim
        (ann_rigid_mem hb) (rigidBindingVars_mem hb)))
    have hbindingsbelow : ∀ binding ∈ bindings, ∀ v ∈ binding.ann.rigidVars, v < frontier := by
      intro binding hb v hv
      exact (List.mem_append.mp (hbindingscope binding hb v (List.mem_append_left _ hv))).elim
        (hK v) (hFvars v)
    have hvalid := RecGroup.inferenceSccs_valid
      (bindings := bindings.map InputRecBinding.recMode)
    have hinitFrame := RecState.Frame.init hctx
      hbindingsbelow hK hFvars
    have hinitLC := RecState.LC.init (base := frontier)
      (fun binding hb scheme heq =>
        hann scheme (List.mem_map.mpr ⟨binding, hb, heq⟩))
    have hinitBelow : (RecState.init frontier bindings).Below (frontier + bindings.length) := by
      exact RecState.Below.init hbindingsbelow
    have hctxSeed : CtxBelow (frontier + bindings.length) ctx :=
      fun M hm => (hctx M hm).mono (by omega)
    have hFSeed : ∀ t ∈ F, Ty.BelowFvars (frontier + bindings.length) t :=
      fun t ht => (hF t ht).mono (by omega)
    have hvalid0 : RecGroups.ValidResidualGroups (bindings.map InputRecBinding.recMode) ([] ++ groups) := hvalid
    obtain ⟨hframe1, _⟩ := hstrata.frame_of_infer
      (fun _ hi => hi.sourceLocality) hvalid0 hinitFrame hinitLC hctxWF hinitBelow hctxSeed hFSeed
      (by omega) hbindingscope
    have htrace1 := hstrata.inputTrace_of_infer
      (fun _ hi => hi.sourceLocality) hvalid0 hinitFrame hinitLC hctxWF hinitBelow hctxSeed hFSeed
      (by omega) hbindingscope (fun _ hi => hi.inputSound_source_raw) (by
        intro stage component hc
        cases hc)
    obtain ⟨hS1, hLC1⟩ := hstrata.lc_of_infer (fun _ hi => hi.lc) hctxWF hinitLC
    obtain ⟨hB1, hBelow1⟩ := hstrata.belowFvars_of_infer (fun _ hi => hi.belowFvars)
      hctxSeed (fun k hk => Nat.lt_of_lt_of_le (hK k hk) (by omega)) hFSeed hinitBelow
      (fun binding hb v hv => Nat.lt_of_lt_of_le (hbindingsbelow binding hb v hv) (by omega))
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
        intro binding hm v hv
        rw [substInputBindings_eq_map] at hm
        obtain ⟨original, ho, rfl⟩ := List.mem_map.mp hm
        obtain ⟨k, hk, hv⟩ := BindingAnn.rigidVars_substTyFvars hv
        exact (Subst.onTy_belowFvars (hB1)
          ((Ty.BelowFvars.fvar (hbindingsbelow original ho k hk)).mono hbase1)).mem_lt v hv)
    have hfix2 := Subst.fixes_of_dom_avoids hsigned.dom_avoids
    have htrace2' := htrace1.onSubst hframe1 s2 hS2 hfix2 hpool2
    have hfields := hsigned.type_fields
    have htrace2 := htrace2'.congr_types hfields.1 hfields.2.1 hfields.2.2.1
    have hscope1 : ∀ binding ∈ substInputBindings s1 bindings, ∀ v ∈ binding.ann.rigidVars,
        v ∈ K ++ softVars (substSoft s1 F) := by
      intro binding hm v hv
      rw [substInputBindings_eq_map] at hm
      obtain ⟨original, ho, rfl⟩ := List.mem_map.mp hm
      obtain ⟨k, hk, hv⟩ := BindingAnn.rigidVars_substTyFvars hv
      exact scope_image (Subst.fixes_of_dom_avoids hstrata.dom_avoids)
        (hbindingscope original ho k (List.mem_append_left _ hk)) hv
    have hcomplete2 := hsigned.inputSound_of_infer
      (fullBindings := substInputBindings s1 bindings) (fun _ hi => hi.inputSound_source_raw)
      (Subst.onCtx_wf hS1 hctxWF) hLC1
      (fun k hk => Nat.lt_of_lt_of_le (hK k hk) hbase1) (by simp) hscope1
      RecState.CompleteInput.init
    have hbodyCtx := hLC2.rhsCtx (Subst.onCtx_wf hS2 (Subst.onCtx_wf hS1 hctxWF))
    rw [← Subst.onCtx_append] at hbodyCtx
    have hbodyTyped := hbody.inputSound_source_raw hbodyCtx
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
    have hbindingsFinal : ∀ binding ∈ substInputBindings (s1 ++ s2 ++ s3) bindings,
        ∀ v ∈ binding.ann.rigidVars ++ binding.rhs.rigidVars,
          v ∈ K ++ softVars (substSoft (s1 ++ s2 ++ s3) F) := by
      intro binding hm v hv
      rw [substInputBindings_eq_map] at hm
      obtain ⟨original, ho, rfl⟩ := List.mem_map.mp hm
      rcases List.mem_append.mp hv with hv | hv
      · obtain ⟨k, hk, himage⟩ := BindingAnn.rigidVars_substTyFvars hv
        exact scope_image hfix123
          (hbindingscope original ho k (List.mem_append_left _ hk)) himage
      · exact (show SourceScope K F original.rhs from fun v hv =>
          hbindingscope original ho v (List.mem_append_right _ hv)).subst
            (s1 ++ s2 ++ s3) hfix123 v hv
    simp only [← substInputBindings_append, ← substSoft_append,
      ← Subst.onCtx_append, List.nil_append] at hframe3 htrace3 hcomplete3 hctxeq
    simp only [← substInputBindings_append] at hvalid3
    change (state2.onSubst s3).Frame frontier K
      (substSoft s3 (substSoft (s1 ++ s2) F)) ((s1 ++ s2 ++ s3).onCtx ctx)
      (substInputBindings (s1 ++ s2 ++ s3) bindings) groups.flatten at hframe3
    simp only [← substSoft_append] at hframe3
    obtain ⟨L, hcomplete3⟩ := hcomplete3
    have hresult := RecState.InputTrace.toTyping
      (bindings := substInputBindings (s1 ++ s2 ++ s3) bindings) hframe3 hLC3
      hvalid3 hbindingsFinal htrace3
      (L := L) (by
        intro i binding scheme hb hs Xs hXs
        have hm := congrArg (fun ss : List (Option PolyTy) => ss[i]?) hframe3.modes
        change (List.map RecSpec.ann (state2.onSubst s3).specs)[i]? =
          (List.map (fun binding => binding.ann.recModeAnn)
            (substInputBindings (s1 ++ s2 ++ s3) bindings))[i]? at hm
        rw [List.getElem?_map, hs] at hm
        change some (some scheme) = _ at hm
        cases ha : (substInputBindings (s1 ++ s2 ++ s3) bindings)[i]? with
        | none => rw [List.getElem?_map, ha] at hm; cases hm
        | some found =>
          have hsame : found = binding := Option.some.inj (ha.symm.trans hb)
          subst found
          have hmode : binding.ann.recModeAnn = some scheme := by
            rw [List.getElem?_map, hb] at hm
            exact Option.some.inj hm.symm
          have haComplete : binding.ann = .complete scheme := by
            cases hAnn : binding.ann with
            | absent | template | partialForall =>
              simp only [hAnn, BindingAnn.recModeAnn, reduceCtorEq] at hmode
            | complete found =>
              have heq : found = scheme := by
                simpa only [hAnn, BindingAnn.recModeAnn, Option.some.injEq] using hmode
              subst found
              rfl
          have hi : i < (substInputBindings s1 bindings).length := by
            have := (List.getElem?_eq_some_iff.mp hb).1
            simpa only [substInputBindings_eq_map, List.length_map] using this
          rw [← hctxeq]
          exact hcomplete3 i binding scheme hi hb haComplete Xs hXs)
      (by
        rw [← hctxeq]
        simpa only [RecState.rhsCtx_onSubst, Subst.onCtx_append, ← substSoft_append,
          ← InferInput.substTyFvars_append] using hbodyTyped)
    simpa only [InferInput.substTyFvars, Subst.onCtx_append,
      substInputBindings_append] using hresult
  | .match_ _ hs hne hb =>
    intro hctx
    have hs1 := (hs.lc hctx).2
    have hbr := hb.lc (Subst.onCtx_wf hs1 hctx) (hs.lc hctx).1 .fvar
    have hscrut := (hs.inputSound_source_raw hctx).onSubst_soft _ hbr.2 hb.dom_avoids
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
  all_goals simp only [sizeBindings_substInputBindings] at *
  all_goals (simp only [InferInput.size, InferInput.size_openTyVars, InferInput.size_substTyFvars, sizeBranches_substInputBranches]; omega)

theorem InferBranches.inputSound_source
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
    · have head := (hb.inputSound_source_raw hctx).onSubst_soft (s2 ++ s3)
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
        simpa only [← substSoft_append, ← InferInput.substTyFvars_append] using hb.inputSound_source_raw hbodyWF
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

theorem InferCert.inputSound_source {request : InferRequest} {result : InferResult}
    (h : InferCert request result) (hctx : CtxWF request.ctx) :
    InputTyping
      (request.protectedVars ++ softVars (substSoft result.subst request.soft))
      (result.subst.onCtx request.ctx) (request.input.substTyFvars result.subst) result.ty := by
  cases request
  cases result
  exact InferCert.inputSound_source_raw h hctx

theorem Infer.inputSound_source (h : Infer K F frontier ctx input next subst output ty) :
    CtxWF ctx →
      InputTyping (K ++ softVars (substSoft subst F)) (subst.onCtx ctx)
        (input.substTyFvars subst) ty :=
  InferCert.inputSound_source_raw h

/-- With no provisional slots, actual inference preserves authored annotations. -/
theorem Infer.inputSound (h : Infer K [] frontier ctx input next subst output ty)
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
private theorem InferCert.completes_source_raw (h : Infer K F frontier ctx input next subst output ty) :
    CtxWF ctx → AnnotationCompletion (K ++ softVars (substSoft subst F)) (input.substTyFvars subst) output := by
  match h with
  | .primLitUnit | .primLitInt | .primLitNat | .primLitChar | .primBinOpIntAdd | .primBinOpIntSub | .primBinOpIntLt _ _ _ _ | .primBinOpCharLt _ _ _ _ | .var _ | .ctor _ =>
      intro _
      exact .complete rfl (by simp [Expr.tyFreeVars])
  | @InferCert.lambda K F ann body frontier ctx seeded bodyResult _ hs hb =>
      intro hctx
      have hbodyCtx : CtxWF
          { ctx with env := PolyTy.mkTrivial seeded.param :: ctx.env } := by
        intro scheme hscheme
        rcases List.mem_cons.mp hscheme with rfl | hscheme
        · exact hs.lc
        · exact hctx scheme hscheme
      have hsubst := (hb.lc hbodyCtx).2
      simp only [InferInput.substTyFvars]
      have hout : ann.map (fun _ => bodyResult.subst.onTy seeded.param) =
          (ann.map (TyTemplate.substTyFvars bodyResult.subst)).map
            (fun _ => bodyResult.subst.onTy seeded.param) := by
        cases ann <;> rfl
      simp only [lambdaOutput, hout]
      refine AnnotationCompletion.lambda ?_ ?_ ?_
      · intro template heq
        cases ann with
        | none => cases heq
        | some original =>
          cases heq
          exact (hs.fits original rfl).substTyFvars bodyResult.subst
      · intro template heq v hv
        cases ann with
        | none => cases heq
        | some original =>
          cases heq
          obtain ⟨old, hold, hv⟩ := TyTemplate.rigidVars_substTyFvars hv
          exact scope_image (Subst.fixes_of_dom_avoids hb.dom_avoids) (hs.rigid original rfl old hold) hv
      · simpa only [Subst.onCtx, Subst.onEnv, List.map_cons, Subst.onPolyTy,
          PolyTy.mkTrivial] using hb.completes_source_raw hbodyCtx
  | @InferCert.app K F f arg frontier ctx _ argumentResult unifier _ hf ha hu =>
      intro hctx
      have hs1 := (hf.lc hctx).2
      have haCtx := Subst.onCtx_wf hs1 hctx
      have hs2 := (ha.lc haCtx).2
      have hs3 := hu.unifies.lc (Subst.onTy_lc hs2 (hf.lc hctx).1)
        (.arrow (ha.lc haCtx).1 .fvar)
      have hfComp := (hf.completes_source_raw hctx).onSubst_soft
        (argumentResult.subst ++ unifier)
        (fun pair hp => (List.mem_append.mp hp).elim (hs2 pair) (hs3 pair))
        (fun pair hp => (List.mem_append.mp hp).elim (ha.dom_avoids pair) (hu.dom_avoids pair))
      have haComp := (ha.completes_source_raw haCtx).onSubst_soft
        unifier hs3 hu.dom_avoids
      simp only [← substSoft_append, ← InferInput.substTyFvars_append, List.append_assoc] at hfComp haComp
      simpa only [List.append_assoc] using AnnotationCompletion.app hfComp haComp
  | @InferCert.letIn K F ann rhs body frontier ctx
      ⟨first, s1, rhsOut, rhsTy⟩ ⟨checked, sCheck⟩ ⟨next, s2, bodyOut, bodyTy⟩
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
      have rhsComp := (hr.completes_source_raw hctx).onSubst_soft sCheck hsCheck hc.dom_avoids
      simp only [← substSoft_append, ← InferInput.substTyFvars_append] at rhsComp
      have rhsBound := (TypeOfHM.onSubst sCheck hsCheck (hr.sourceSound hctx)).tyBvarBounded
      obtain ⟨compAvoid, hcomplete⟩ := rhsComp.generalise_closed_after_source
        (names := genVars (K ++ softVars (substSoft (s1 ++ sCheck) F))
          (sCheck.onCtx (s1.onCtx ctx)).env (sCheck.onTy rhsTy))
        genVars_nodup (fun _ hn => genVars_not_mem_rigid hn) rhsBound s2 hs2
        (fun _ hk _ hv => scope_image (Subst.fixes_of_dom_avoids hb.dom_avoids) hk hv)
      have bodyComp := hb.completes_source_raw bodyCtxWF
      simp only [← substSoft_append, ← InferInput.substTyFvars_append, ← BindingAnn.substTyFvars_append,
        List.append_assoc] at hfits hcomplete bodyComp hannFinal ⊢
      simp only [letOutput]
      refine AnnotationCompletion.letIn (L := avoid ++ compAvoid) hannFinal ?_ ?_ bodyComp
      · intro fresh hf
        exact hfits fresh ⟨hf.length, hf.nodup, fun v hv hm => hf.avoid v hv (List.mem_append_left _ hm)⟩
      · intro fresh hf
        exact hcomplete fresh ⟨hf.length, hf.nodup, fun v hv hm => hf.avoid v hv (List.mem_append_right _ hm)⟩

  | @InferCert.letSignature K F ann rhs body written frontier ctx
      ⟨first, s1, rhsOut, rhsTy⟩ ⟨checked, sCheck⟩ ⟨next, s2, bodyOut, bodyTy⟩
      hscope hprefix havoid hr hc hescape hb =>
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
    have rhsComp0 := (hr.completes_source_raw hctx).onSubst_soft sCheck hsCheck hc.dom_avoids
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
    have bodyComp := hb.completes_source_raw bodyCtxWF
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

  | @InferCert.letRec K F bindings body frontier ctx completed
      ⟨first, s1, state1⟩ ⟨second, s2, state2⟩ ⟨next, s3, bodyOut, bodyTy⟩
      hscope hann hstrata hsigned hcompleted hbody =>
    intro hctxWF
    let groups := RecGroup.inferenceSccs (bindings.map InputRecBinding.recMode)
    obtain ⟨hraw, hctx, hK, hFvars⟩ := hscope
    have hF : ∀ t ∈ F, Ty.BelowFvars frontier t := by
      intro t ht
      apply Ty.BelowFvars.of_freeVars_lt
      intro v hv
      exact hFvars v (TyList.mem_freeVars_iff.mpr ⟨t, ht, hv⟩)
    have hbindingscope : ∀ binding ∈ bindings,
        ∀ v ∈ binding.ann.rigidVars ++ binding.rhs.rigidVars, v ∈ K ++ softVars F := by
      intro binding hb v hv
      exact hraw v (List.mem_append_left _ ((List.mem_append.mp hv).elim
        (ann_rigid_mem hb) (rigidBindingVars_mem hb)))
    have hbindingsbelow : ∀ binding ∈ bindings, ∀ v ∈ binding.ann.rigidVars, v < frontier := by
      intro binding hb v hv
      exact (List.mem_append.mp (hbindingscope binding hb v (List.mem_append_left _ hv))).elim
        (hK v) (hFvars v)
    have hvalid := RecGroup.inferenceSccs_valid
      (bindings := bindings.map InputRecBinding.recMode)
    have hinitFrame := RecState.Frame.init hctx
      hbindingsbelow hK hFvars
    have hinitLC := RecState.LC.init (base := frontier)
      (fun binding hb scheme heq =>
        hann scheme (List.mem_map.mpr ⟨binding, hb, heq⟩))
    have hinitBelow : (RecState.init frontier bindings).Below (frontier + bindings.length) := by
      exact RecState.Below.init hbindingsbelow
    have hctxSeed : CtxBelow (frontier + bindings.length) ctx :=
      fun M hm => (hctx M hm).mono (by omega)
    have hFSeed : ∀ t ∈ F, Ty.BelowFvars (frontier + bindings.length) t :=
      fun t ht => (hF t ht).mono (by omega)
    have hvalid0 : RecGroups.ValidResidualGroups (bindings.map InputRecBinding.recMode) ([] ++ groups) := hvalid
    obtain ⟨hframe1, _⟩ := hstrata.frame_of_infer
      (fun _ hi => hi.sourceLocality) hvalid0 hinitFrame hinitLC hctxWF hinitBelow hctxSeed hFSeed
      (by omega) hbindingscope
    have hfid1 := hstrata.fidelity_of_infer
      (fun _ hi => hi.sourceLocality) hvalid0 hinitFrame hinitLC hctxWF hinitBelow hctxSeed hFSeed
      (by omega) hbindingscope (fun _ hi => hi.completes_source_raw) (fun _ hi => hi.sourceSound)
      RecState.Fidelity.init
    obtain ⟨hS1, hLC1⟩ := hstrata.lc_of_infer (fun _ hi => hi.lc) hctxWF hinitLC
    obtain ⟨hB1, hBelow1⟩ := hstrata.belowFvars_of_infer (fun _ hi => hi.belowFvars)
      hctxSeed (fun k hk => Nat.lt_of_lt_of_le (hK k hk) (by omega)) hFSeed hinitBelow
      (fun binding hb v hv => Nat.lt_of_lt_of_le (hbindingsbelow binding hb v hv) (by omega))
    have hvalid1 := recValid_subst hvalid s1
    have hdone1 := hframe1.all_mono_done hvalid1
    obtain ⟨hframe2, _⟩ := hsigned.frame_of_infer
      (fun _ hi => hi.sourceLocality) hframe1 (by simp) hdone1 hBelow1.2.2.2
    have hfid2 := hsigned.completes_of_infer
      (fun _ hi => hi.completes_source_raw) (fun _ hi => hi.sourceSound)
      (Subst.onCtx_wf hS1 hctxWF) hLC1
      (fun k hk => by have := hK k hk; have := hstrata.frontier_le; omega)
      (by simp) ((RecState.outputs_length state1).trans hframe1.memberStates_length)
      (fun j binding scheme hb ha => by
        simpa only [Nat.zero_add] using hframe1.complete_export hb ha) hfid1
    simp only [← substSoft_append] at hfid2
    obtain ⟨hS2, hLC2⟩ := hsigned.lc_of_infer (fun _ hi => hi.lc) (Subst.onCtx_wf hS1 hctxWF) hLC1
    have hbodyCtx := hLC2.rhsCtx (Subst.onCtx_wf hS2 (Subst.onCtx_wf hS1 hctxWF))
    rw [← Subst.onCtx_append] at hbodyCtx
    obtain ⟨_, hS3⟩ := hbody.lc hbodyCtx
    have hbodyComplete := hbody.completes_source_raw hbodyCtx
    simp only [← substSoft_append, ← InferInput.substTyFvars_append] at hbodyComplete
    have hfidFinal := hfid2.onSubst_source hS3
      (fun k hk v hv => scope_image (Subst.fixes_of_dom_avoids hbody.dom_avoids) hk hv)
    simp only [← substSoft_append] at hfidFinal
    have hexports : state2.exports =
        (completed.map CompletedRecMember.scheme).map some := hcompleted.exports
    have houtputs : state2.outputs =
        (completed.map CompletedRecMember.output).map some := hcompleted.outputs
    have hfinalExports : (state2.onSubst s3).exports =
        (completed.map (fun member => s3.onPolyTy member.scheme)).map some := by
      simp only [RecState.exports_onSubst, hexports, List.map_map]
      apply List.map_congr_left
      intro scheme _
      rfl
    have hfinalOutputs : (state2.onSubst s3).outputs =
        (completed.map (fun member => member.output.substTyFvars s3)).map some := by
      simp only [RecState.outputs_onSubst, houtputs, List.map_map]
      apply List.map_congr_left
      intro output _
      rfl
    have hstateLen : state2.memberStates.length = bindings.length := by
      simpa only [substInputBindings_eq_map, List.length_map] using hframe2.memberStates_length
    have hcompletedLen : completed.length = bindings.length :=
      hcompleted.length_eq.symm.trans hstateLen
    have hfixAll : ∀ k ∈ K, (s1 ++ s2 ++ s3).onTy (.fvar k) = .fvar k :=
      Subst.fixes_of_dom_avoids (fun p hp => (List.mem_append.mp hp).elim
        (fun hp => (List.mem_append.mp hp).elim (hstrata.dom_avoids p) (hsigned.dom_avoids p)) (hbody.dom_avoids p))
    have hScopeFinal : ∀ binding ∈ substInputBindings (s1 ++ s2 ++ s3) bindings,
        ∀ v ∈ binding.ann.rigidVars ++ binding.rhs.rigidVars,
          v ∈ K ++ softVars (substSoft (s1 ++ s2 ++ s3) F) := by
      intro binding hm v hv
      rw [substInputBindings_eq_map] at hm
      obtain ⟨original, ho, rfl⟩ := List.mem_map.mp hm
      rcases List.mem_append.mp hv with hv | hv
      · obtain ⟨k, hk, himage⟩ := BindingAnn.rigidVars_substTyFvars hv
        exact scope_image hfixAll
          (hbindingscope original ho k (List.mem_append_left _ hk)) himage
      · exact (show SourceScope K F original.rhs from fun v hv =>
          hbindingscope original ho v (List.mem_append_right _ hv)).subst
            (s1 ++ s2 ++ s3) hfixAll v hv
    let completedFinal : List CompletedRecMember := completed.map fun member =>
      { member with
        scheme := s3.onPolyTy member.scheme
        output := member.output.substTyFvars s3 }
    have hcompletedFinal : (state2.onSubst s3).Completed completedFinal :=
      ⟨by simpa only [RecState.exports, completedFinal, List.map_map, Function.comp_def]
          using hfinalExports,
        by simpa only [RecState.outputs, completedFinal, List.map_map, Function.comp_def]
          using hfinalOutputs,
        by simpa only [RecState.onSubst, RecMemberState.onSubst, completedFinal,
            List.map_map, Function.comp_def]
          using hcompleted.annInfo⟩
    have hScopeFinal' : ∀ binding ∈
        substInputBindings s3 (substInputBindings s2 (substInputBindings s1 bindings)),
        ∀ v ∈ binding.ann.rigidVars ++ binding.rhs.rigidVars,
          v ∈ K ++ softVars (substSoft (s1 ++ s2 ++ s3) F) := by
      rw [← substInputBindings_append, ← substInputBindings_append]
      simpa only [List.append_assoc] using hScopeFinal
    have hresult := hfidFinal.toCompletes hcompletedFinal
      (by simp only [completedFinal, substInputBindings_eq_map, List.length_map, hcompletedLen])
      hScopeFinal' hbodyComplete
    simpa only [InferInput.substTyFvars, completedFinal, substInputBindings_append,
      List.map_map, Function.comp_def] using hresult

  | .match_ _ hs _ hb =>
    intro hctx
    have hs1 := (hs.lc hctx).2
    have hbr := hb.lc (Subst.onCtx_wf hs1 hctx) (hs.lc hctx).1 .fvar
    have hscrut := (hs.completes_source_raw hctx).onSubst_soft _ hbr.2 hb.dom_avoids
    have hbranches := hb.completes_source (Subst.onCtx_wf hs1 hctx) (hs.lc hctx).1 .fvar
    simp only [← substSoft_append, ← InferInput.substTyFvars_append] at hscrut
    simp only [← substSoft_append, ← substInputBranches_append] at hbranches
    simpa only [InferInput.substTyFvars, ← substSoft_append, substInputBranches_append] using
      AnnotationCompletion.match_ hscrut hbranches
termination_by (input.size, 0)
decreasing_by
  all_goals simp only [sizeBindings_substInputBindings] at *
  all_goals (simp only [InferInput.size, InferInput.size_openTyVars, InferInput.size_substTyFvars, sizeBranches_substInputBranches]; omega)

theorem InferBranches.completes_source
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
    have head := (hb.completes_source_raw hctx).onSubst_soft (s2 ++ s3)
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
    have head := (hb.completes_source_raw hbodyWF).onSubst_soft (s2 ++ s3)
      (fun p hp => (List.mem_append.mp hp).elim (hs2 p) (hs3 p))
      (fun p hp => (List.mem_append.mp hp).elim (hu.dom_avoids p) (hr.dom_avoids p))
    simp only [← substSoft_append, ← InferInput.substTyFvars_append, ← substInputBranches_append,
      List.append_assoc] at head htail ⊢
    exact CompletedBranches.cons head htail
termination_by (sizeBranches branches, 0)
decreasing_by all_goals (simp only [sizeBranches, InferInput.size_substTyFvars, sizeBranches_substInputBranches]; omega)
end

theorem InferCert.completes_source {request : InferRequest} {result : InferResult}
    (h : InferCert request result) (hctx : CtxWF request.ctx) :
    AnnotationCompletion
      (request.protectedVars ++ softVars (substSoft result.subst request.soft))
      (request.input.substTyFvars result.subst) result.completedExpr := by
  cases request
  cases result
  exact InferCert.completes_source_raw h hctx

theorem Infer.completes_source (h : Infer K F frontier ctx input next subst output ty) :
    CtxWF ctx →
      AnnotationCompletion (K ++ softVars (substSoft subst F))
        (input.substTyFvars subst) output :=
  InferCert.completes_source_raw h

/-- The public empty-soft-context judgment preserves all authored annotations. -/
theorem Infer.completes (h : Infer K [] frontier ctx input next subst output ty)
    (hctx : CtxWF ctx) : AnnotationCompletion K input output := by
  have hscope : ∀ v ∈ input.rigidVars, v ∈ K := by
    simpa only [SourceScope, softVars, TyList.freeVars, List.append_nil] using h.sourceScope
  have hinput := input.substTyFvars_eq_self_of_fixes
    (fun v hv => Subst.fixes_of_dom_avoids h.dom_avoids v (hscope v hv))
  simpa only [substSoft, List.map_nil, softVars, TyList.freeVars, List.append_nil, hinput] using
    h.completes_source hctx

/-! ## Compact certificate interface -/

namespace InferCert

theorem sound {request : InferRequest} {result : InferResult}
    (h : InferCert request result) (hctx : CtxWF request.ctx) :
    RuntimeTyping.RunWT (result.subst.onCtx request.ctx) request.input.erase result.ty :=
  Infer.sound h hctx

/-- Ordinary core inference has no provisional soft slots, so its certificate
directly types the authored input. -/
theorem inputSound {K : List Nat} {frontier : Nat} {ctx : Ctx} {input : InferInput}
    {result : InferResult} (h : InferCert (InferRequest.core K frontier ctx input) result)
    (hctx : CtxWF ctx) : InputTyping K (result.subst.onCtx ctx) input result.ty :=
  Infer.inputSound h hctx

/-- Ordinary core inference completes annotations in the authored input itself. -/
theorem completes {K : List Nat} {frontier : Nat} {ctx : Ctx} {input : InferInput}
    {result : InferResult} (h : InferCert (InferRequest.core K frontier ctx input) result)
    (hctx : CtxWF ctx) : AnnotationCompletion K input result.completedExpr :=
  Infer.completes h hctx

end InferCert

/-- The exact completed Core returned to the runtime is source typed. -/
theorem inferWithTypes_source_sound {ctors : CtorEnv} {input : InferInput} {result : InferenceResult}
    (h : inferWithTypes ctors input = some result) :
    TypeOfHM ⟨[], ctors⟩ result.completedExpr result.ty := by
  simpa only [InferRequest.core, Subst.onCtx_empty] using
    InferCert.sourceSound (inferWithTypes_infer h) CtxWF.empty

theorem inferWithTypes_erase {ctors : CtorEnv} {input : InferInput} {result : InferenceResult}
    (h : inferWithTypes ctors input = some result) : result.completedExpr.erase = input.erase :=
  InferCert.erase (inferWithTypes_infer h)

theorem inferWithTypes_input_sound {ctors : CtorEnv} {input : InferInput} {result : InferenceResult}
    (h : inferWithTypes ctors input = some result) : InputTyping input.rigidVars ⟨[], ctors⟩ input result.ty := by
  simpa only [Subst.onCtx_empty] using
    InferCert.inputSound (inferWithTypes_infer h) CtxWF.empty

end
