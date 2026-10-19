import FHM.Elaboration.Input
import FHM.SurfaceBridge
import FHM.PatComp.Trace

/-! Annotation adapters for the shared surface and pattern-lowering pipeline.
Holes remain syntax until inference visits each generated occurrence. -/

namespace Elaboration

mutual
/-- Lower a template with the same name, kind and arity checks as ordinary
surface type lowering. Named scoped variables remain fixed bound variables. -/
def lowerTemplate (ke : KindEnv) (tvs : List ValName) : Surface.Ty → Option Template
  | .hole => some .hole
  | .prim p => (SurfaceBridge.lowerTy ke tvs (.prim p)).map .fixed
  | .tvar name => (SurfaceBridge.lowerTy ke tvs (.tvar name)).map .fixed
  | .arrow a b => return .arrow (← lowerTemplate ke tvs a) (← lowerTemplate ke tvs b)
  | .pair a b => do
      let a' ← lowerTemplate ke tvs a
      let b' ← lowerTemplate ke tvs b
      if LookupList.get? ke SurfaceBridge.nPair = some 2 then
        some (.custom SurfaceBridge.nPair [a', b'])
      else none
  | .customTy name args => do
      let args' ← lowerTemplateList ke tvs args
      if LookupList.get? ke name = some args'.length then some (.custom name args') else none

def lowerTemplateList (ke : KindEnv) (tvs : List ValName) :
    List Surface.Ty → Option (List Template)
  | [] => some []
  | ty :: rest => return (← lowerTemplate ke tvs ty) :: (← lowerTemplateList ke tvs rest)
end

/-- Lower an optional lambda-parameter annotation without filling its holes. -/
def lowerTemplateAnn (ke : KindEnv) (tvs : List ValName) :
    Option Surface.Ty → Option (Option Template)
  | none => some none
  | some ty => (lowerTemplate ke tvs ty).map some

/-- Normalize binding-head sugar for the canonical input pipeline.
A result annotation describes the RHS after every head parameter. Missing
parameter types become independent holes; a head forall without a result
annotation retains its scope using a partial signature. Parameter-only heads
without a result annotation keep ordinary HM lambda inference. -/
def finalizeInputAnn (tyParams : List ValName)
    (params : List (ValName × Option Surface.Ty)) (ann : Option Surface.PolyTy) :
    Option Surface.PolyTy :=
  if tyParams.isEmpty && params.isEmpty then SurfaceBridge.mergeTyParams [] ann
  else if tyParams.isEmpty && ann.isNone then none
  else
    some {
      foralls := SurfaceBridge.mergeTyParamNames tyParams ((ann.map (·.foralls)).getD [])
      body := params.foldr (fun (_, domain) result => .arrow (domain.getD .hole) result)
        ((ann.map (·.body)).getD .hole) }

@[simp] theorem finalizeInputAnn_noHead (ann : Option Surface.PolyTy) :
    finalizeInputAnn [] [] ann = SurfaceBridge.finalizeAnn [] [] ann := rfl

example : finalizeInputAnn [] [] (some ⟨[], .prim .int⟩) = some ⟨[], .prim .int⟩ := rfl

example : finalizeInputAnn [] [(.mk "x", none), (.mk "y", some (.prim .bool))]
    (some ⟨[], .prim .int⟩) =
  some ⟨[], .arrow .hole (.arrow (.prim .bool) (.prim .int))⟩ := rfl

example : finalizeInputAnn [.mk "a"] [(.mk "x", some (.tvar (.mk "a")))] none =
  some ⟨[.mk "a"], .arrow (.tvar (.mk "a")) .hole⟩ := rfl

example : finalizeInputAnn [.mk "unused"] [] none = some ⟨[.mk "unused"], .hole⟩ := rfl

example : finalizeInputAnn [] [(.mk "x", some (.prim .int)), (.mk "y", none)] none = none := rfl

example : finalizeInputAnn [.mk "a"] [(.mk "x", none)]
    (some ⟨[.mk "b"], .tvar (.mk "b")⟩) =
  some ⟨[.mk "a", .mk "b"], .arrow .hole (.tvar (.mk "b"))⟩ := rfl

/-- Classify a finalized binding signature by whether its lowered template is
complete. The caller applies `finalizeInputAnn` before this adapter. -/
def lowerInputLetAnn (ke : KindEnv) (tvs : List ValName) :
    Option Surface.PolyTy → Option LetAnn
  | none => some .absent
  | some scheme => do
      let names := scheme.foralls.eraseDups
      let template ← lowerTemplate ke (names ++ tvs) scheme.body
      match template.toCore with
      | some body => some (.complete ⟨names.length, body⟩)
      | none =>
          if names.isEmpty then some (.template template)
          else some (.partialForall names.length template)

mutual
/-- Erasure commutes with term shifting, including recursive group binders. -/
theorem Input.erase_shiftFrom (input : Input) (threshold count : Nat) :
    (input.shiftFrom threshold count).erase = input.erase.shiftFrom threshold count := by
  cases input with
  | primLit p => rfl
  | primBinOp op => rfl
  | var i => simp only [Input.shiftFrom, Input.erase, Expr.shiftFrom]; split <;> rfl
  | ctor name => rfl
  | lambda ann body =>
    simp only [Input.shiftFrom, Input.erase, Expr.shiftFrom, body.erase_shiftFrom]
  | app f arg =>
    simp only [Input.shiftFrom, Input.erase, Expr.shiftFrom, f.erase_shiftFrom, arg.erase_shiftFrom]
  | letIn ann rhs body =>
    simp only [Input.shiftFrom, Input.erase, Expr.shiftFrom, rhs.erase_shiftFrom, body.erase_shiftFrom]
  | match_ scrut branches =>
    simp only [Input.shiftFrom, Input.erase, scrut.erase_shiftFrom]
    change Expr.match_ (scrut.erase.shiftFrom threshold count) (eraseBranches (shiftBranches threshold count branches)) =
      Expr.match_ (scrut.erase.shiftFrom threshold count)
        (((Expr.match_ (.primLit .unit) (eraseBranches branches)).shiftFrom threshold count).matchBranchesOf)
    rw [eraseBranches_shiftFrom]
  | letRec anns bindings body =>
    have hlength : ∀ start, (shiftBindings start count bindings).length = bindings.length := by
      induction bindings with
      | nil => intro _; rfl
      | cons head tail ih =>
        intro start
        simp only [shiftBindings, List.length_cons, ih]
    have hbindings := eraseBindings_shiftFrom bindings (threshold + bindings.length) count
    simp only [Input.shiftFrom, Input.erase, Expr.shiftFrom, body.erase_shiftFrom,
      eraseBindings_length, hbindings, List.map_const', hlength]
termination_by sizeOf input
decreasing_by
  all_goals simp_wf
  all_goals omega
private theorem eraseBranches_shiftFrom (branches : List (MatchPattern × Input)) (threshold count : Nat) :
    eraseBranches (shiftBranches threshold count branches) =
      ((Expr.match_ (.primLit .unit) (eraseBranches branches)).shiftFrom threshold count).matchBranchesOf := by
  cases branches with
  | nil => rfl
  | cons head rest =>
    rcases head with ⟨pat, body⟩
    change (pat, (body.shiftFrom (threshold + pat.bindCount) count).erase) ::
      eraseBranches (shiftBranches threshold count rest) =
      (pat, body.erase.shiftFrom (threshold + pat.bindCount) count) ::
        (((Expr.match_ (.primLit .unit) (eraseBranches rest)).shiftFrom threshold count).matchBranchesOf)
    rw [body.erase_shiftFrom, eraseBranches_shiftFrom]
termination_by sizeOf branches
decreasing_by
  all_goals simp_wf
  all_goals omega
private theorem eraseBindings_shiftFrom (bindings : List Input) (threshold count : Nat) :
    eraseBindings (shiftBindings threshold count bindings) =
      RecGroup.shiftFrom threshold count (eraseBindings bindings) := by
  cases bindings with
  | nil => rfl
  | cons body rest =>
    have hrest := eraseBindings_shiftFrom rest threshold count
    simp only [shiftBindings, eraseBindings, RecGroup.shiftFrom, body.erase_shiftFrom, hrest]
termination_by sizeOf bindings
decreasing_by
  all_goals simp_wf
  all_goals omega
end

/-- Preserve input annotations while using the single generic pattern emitter. -/
def inputEmissionOps : PatComp.EmissionOps Input :=
  { var := Input.var
    ctor := Input.ctor
    letIn := Input.letIn .absent
    match_ := Input.match_
    shiftFrom := Input.shiftFrom }

def lowerInputMatch (scrut : Input) (pats : List Surface.Pattern) (bodies : Nat → Input) : Input :=
  PatComp.lowerMatchWith inputEmissionOps scrut pats bodies

def lowerInputMatchTrace (scrut : Input) (pats : List Surface.Pattern)
    (bodies : Nat → Input) : PatComp.TracedLowering Input :=
  PatComp.lowerMatchTraceWith inputEmissionOps scrut pats bodies

@[simp] theorem lowerInputMatchTrace_expr (scrut : Input) (pats : List Surface.Pattern)
    (bodies : Nat → Input) :
    (lowerInputMatchTrace scrut pats bodies).expr = lowerInputMatch scrut pats bodies := rfl

private theorem eraseBranches_append (left right : List (MatchPattern × Input)) :
    eraseBranches (left ++ right) = eraseBranches left ++ eraseBranches right := by
  induction left with
  | nil => rfl
  | cons head rest ih => rcases head with ⟨pat, body⟩; simp only [List.cons_append, eraseBranches, ih]

private theorem erase_emitLetsInput (env binds : List PatComp.Occ) (body : Input) :
    (PatComp.emitLetsWith inputEmissionOps env binds body).erase =
      PatComp.emitLets env binds body.erase := by
  have hgo : ∀ rest depth,
      (PatComp.emitLetsWith.go inputEmissionOps env binds body rest depth).erase =
        PatComp.emitLets.go env binds body.erase rest depth := by
    intro rest
    induction rest with
    | nil => intro depth; exact body.erase_shiftFrom _ _
    | cons head rest ih =>
      intro depth
      change Expr.letIn none (.var _) _ = Expr.letIn none (.var _) _
      rw [ih]
      rfl
  exact hgo binds.reverse 0

mutual
/-- The shared emitter has the same erased runtime structure for Input and Core. -/
theorem erase_emitInput (env : List PatComp.Occ) (bodies : Nat → Input) (tree : PatComp.DTree) :
    (PatComp.emitWith inputEmissionOps env bodies tree).erase =
      PatComp.emit env (fun i => (bodies i).erase) tree := by
  cases tree with
  | fail => rfl
  | leaf act binds => exact erase_emitLetsInput env binds (bodies act)
  | switch occ cases dflt =>
    by_cases hd : dflt = .fail
    · subst dflt
      rw [PatComp.emitWith.eq_3, PatComp.emit, PatComp.emitWith.eq_3]
      change Expr.match_ (.var _) (eraseBranches (_ ++ [])) = Expr.match_ (.var _) (_ ++ [])
      simp only [List.append_nil]
      rw [erase_emitCasesInput env bodies occ cases]
      rfl
    · rw [PatComp.emitWith.eq_4 _ _ _ _ _ _ hd, PatComp.emit,
        PatComp.emitWith.eq_4 _ _ _ _ _ _ hd]
      change Expr.match_ (.var _) (eraseBranches (_ ++ [(.wildcard,
        PatComp.emitWith inputEmissionOps env bodies dflt)])) = Expr.match_ (.var _) (_ ++ _)
      rw [eraseBranches_append, erase_emitCasesInput env bodies occ cases]
      simp only [eraseBranches]
      rw [erase_emitInput env bodies dflt]
      rfl

termination_by sizeOf tree
decreasing_by
  all_goals simp_wf
  all_goals omega
private theorem erase_emitCasesInput (env : List PatComp.Occ) (bodies : Nat → Input)
    (occ : PatComp.Occ) (cases : List (CtorName × Nat × PatComp.DTree)) :
    eraseBranches (PatComp.emitCasesWith inputEmissionOps env bodies occ cases) =
      PatComp.emitCases env (fun i => (bodies i).erase) occ cases := by
  cases cases with
  | nil => rfl
  | cons head rest =>
    rcases head with ⟨name, arity, tree⟩
    change (MatchPattern.named name arity,
      (PatComp.emitWith inputEmissionOps (PatComp.subOccs occ arity ++ env) bodies tree).erase) ::
      eraseBranches (PatComp.emitCasesWith inputEmissionOps env bodies occ rest) = _
    rw [erase_emitInput, erase_emitCasesInput env bodies occ rest]
    rfl
termination_by sizeOf cases
decreasing_by
  all_goals simp_wf
  all_goals omega
end

@[simp] theorem erase_lowerInputMatch (scrut : Input) (pats : List Surface.Pattern)
    (bodies : Nat → Input) :
    (lowerInputMatch scrut pats bodies).erase =
      PatComp.lowerMatch scrut.erase pats (fun i => (bodies i).erase) := by
  change Expr.letIn none scrut.erase _ = Expr.letIn none scrut.erase _
  rw [erase_emitInput]
  rfl

end Elaboration
