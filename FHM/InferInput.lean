import FHM.InferenceSupport

/-! Annotated inference input, independent typing, annotation fidelity and recursive state. -/

/-! ## Input -/

section

/-- The fixed leaves retain authored type syntax; every `hole` occurrence is
independent. `fixed` is also the embedding of a complete monotype. -/
inductive TyTemplate where
  | fixed (ty : Ty)
  | hole
  | arrow (domain codomain : TyTemplate)
  | custom (name : TyName) (args : List TyTemplate)

/-- Declarative matching of an annotation template. This relation neither
allocates metavariables nor mentions inference or an executable substitution. -/
inductive TyTemplate.Fits : TyTemplate → Ty → Prop
  | fixed : Fits (.fixed ty) ty
  | hole : Fits .hole ty
  | arrow : Fits a ta → Fits b tb → Fits (.arrow a b) (.arrow ta tb)
  | custom : List.Forall₂ Fits args tys → Fits (.custom name args) (.customTy name tys)

mutual
def TyTemplate.rigidVars : TyTemplate → List Nat
  | .fixed ty => ty.freeVars
  | .hole => []
  | .arrow a b => a.rigidVars ++ b.rigidVars
  | .custom _ args => rigidVarsList args
def rigidVarsList : List TyTemplate → List Nat
  | [] => []
  | template :: rest => template.rigidVars ++ rigidVarsList rest
end


/-- Complete signatures and partial signatures have different checking modes.
Quantified partial signatures retain their authored binder count for scoped
checking and completion. -/
inductive BindingAnn where
  | absent
  | complete (scheme : PolyTy)
  | template (body : TyTemplate)
  | partialForall (paramCount : Nat) (body : TyTemplate)

/-- A Core-shaped input spine. Type annotations are inputs to elaboration,
whereas the output is always the existing ordinary Core `Expr`. -/
inductive InferInput where
  | primLit (value : PrimLitExpr)
  | primBinOp (op : PrimBinOp)
  | lambda (ann : Option TyTemplate) (body : InferInput)
  | app (fn arg : InferInput)
  | letIn (ann : BindingAnn) (rhs body : InferInput)
  | var (index : Nat)
  | ctor (name : CtorName)
  | match_ (scrutinee : InferInput) (branches : List (MatchPattern × InferInput))
  | letRec (anns : List BindingAnn) (bindings : List InferInput) (body : InferInput)

mutual
/-- Runtime shape, independently of any choices made for anonymous holes. -/
def InferInput.erase : InferInput → Expr
  | .primLit p => .primLit p
  | .primBinOp op => .primBinOp op
  | .lambda _ body => .lambda none body.erase
  | .app f x => .app f.erase x.erase
  | .letIn _ rhs body => .letIn none rhs.erase body.erase
  | .var i => .var i
  | .ctor c => .ctor c
  | .match_ scrut branches => .match_ scrut.erase (eraseBranches branches)
  | .letRec _ bindings body =>
      .letRec (bindings.map fun _ => none) (eraseBindings bindings) body.erase
def eraseBranches : List (MatchPattern × InferInput) → List (MatchPattern × Expr)
  | [] => []
  | (pat, body) :: rest => (pat, body.erase) :: eraseBranches rest
def eraseBindings : List InferInput → List Expr
  | [] => []
  | body :: rest => body.erase :: eraseBindings rest
end

/-- Complete annotation modes only. A partial mode stays partial even if its
template happens not to contain a hole. -/
def BindingAnn.toCore : BindingAnn → Option (Option PolyTy)
  | .absent => some none
  | .complete scheme => some (some scheme)
  | .template _ | .partialForall _ _ => none

mutual
def TyTemplate.toCore : TyTemplate → Option Ty
  | .fixed ty => some ty
  | .hole => none
  | .arrow a b => return .arrow (← a.toCore) (← b.toCore)
  | .custom name args => return .customTy name (← completeTypes args)
def completeTypes : List TyTemplate → Option (List Ty)
  | [] => some []
  | template :: rest => return (← template.toCore) :: (← completeTypes rest)
end

def completeLambdaAnn : Option TyTemplate → Option (Option Ty)
  | none => some none
  | some template => return some (← template.toCore)

mutual
/-- A decidable conservative embedding, preserving complete/partial modes.
Only a whole subtree successfully embedded here may use the old Core backend. -/
def InferInput.toCore : InferInput → Option Expr
  | .primLit p => some (.primLit p)
  | .primBinOp op => some (.primBinOp op)
  | .lambda ann body => return .lambda (← completeLambdaAnn ann) (← body.toCore)
  | .app f x => return .app (← f.toCore) (← x.toCore)
  | .letIn ann rhs body => return .letIn (← ann.toCore) (← rhs.toCore) (← body.toCore)
  | .var i => some (.var i)
  | .ctor name => some (.ctor name)
  | .match_ scrut branches => return .match_ (← scrut.toCore) (← completeBranches branches)
  | .letRec anns bindings body =>
      return .letRec (← completeAnns anns) (← completeBindings bindings) (← body.toCore)
def completeBranches : List (MatchPattern × InferInput) → Option (List (MatchPattern × Expr))
  | [] => some []
  | (pat, body) :: rest => return (pat, ← body.toCore) :: (← completeBranches rest)
def completeBindings : List InferInput → Option (List Expr)
  | [] => some []
  | body :: rest => return (← body.toCore) :: (← completeBindings rest)
def completeAnns : List BindingAnn → Option (List (Option PolyTy))
  | [] => some []
  | ann :: rest => return (← ann.toCore) :: (← completeAnns rest)
end

mutual
theorem InferInput.toCore_erase (input : InferInput) {core : Expr}
    (h : input.toCore = some core) : core.erase = input.erase := by
  cases input with
  | primLit p => cases h; simp only [Expr.erase, InferInput.erase]
  | primBinOp op => cases h; simp only [Expr.erase, InferInput.erase]
  | var i => cases h; simp only [Expr.erase, InferInput.erase]
  | ctor c => cases h; simp only [Expr.erase, InferInput.erase]
  | lambda ann body =>
      simp only [InferInput.toCore, bind, pure, Option.bind_eq_some_iff,
        Option.some.injEq] at h
      obtain ⟨ann', _, body', hb, rfl⟩ := h
      simp only [Expr.erase, InferInput.erase, body.toCore_erase hb]
  | app f x =>
      simp only [InferInput.toCore, bind, pure, Option.bind_eq_some_iff,
        Option.some.injEq] at h
      obtain ⟨f', hf, x', hx, rfl⟩ := h
      simp only [Expr.erase, InferInput.erase, f.toCore_erase hf, x.toCore_erase hx]
  | letIn ann rhs body =>
      simp only [InferInput.toCore, bind, pure, Option.bind_eq_some_iff,
        Option.some.injEq] at h
      obtain ⟨ann', _, rhs', hr, body', hb, rfl⟩ := h
      simp only [Expr.erase, InferInput.erase, rhs.toCore_erase hr, body.toCore_erase hb]
  | match_ scrut branches =>
      simp only [InferInput.toCore, bind, pure, Option.bind_eq_some_iff,
        Option.some.injEq] at h
      obtain ⟨scrut', hs, branches', hb, rfl⟩ := h
      simp only [Expr.erase, InferInput.erase, scrut.toCore_erase hs, completeBranches_erase branches hb]
  | letRec anns bindings body =>
      simp only [InferInput.toCore, bind, pure, Option.bind_eq_some_iff,
        Option.some.injEq] at h
      obtain ⟨anns', _, bindings', hr, body', hb, rfl⟩ := h
      have hbindings := completeBindings_erase bindings hr
      have hlength : bindings'.length = bindings.length := by
        have := congrArg List.length hbindings
        simpa only [List.length_map, eraseBindings_length] using this
      simp only [Expr.erase, InferInput.erase, body.toCore_erase hb, hbindings]
      congr 1
      simp only [List.map_const', hlength]
theorem completeBranches_erase (inputs : List (MatchPattern × InferInput))
    {cores : List (MatchPattern × Expr)} (h : completeBranches inputs = some cores) :
    cores.map (fun pe => (pe.1, pe.2.erase)) = eraseBranches inputs := by
  cases inputs with
  | nil => cases h; rfl
  | cons head rest =>
      rcases head with ⟨pat, body⟩
      simp only [completeBranches, bind, pure, Option.bind_eq_some_iff,
        Option.some.injEq] at h
      obtain ⟨body', hb, rest', hr, rfl⟩ := h
      simp only [List.map_cons, eraseBranches, body.toCore_erase hb, completeBranches_erase rest hr]
theorem completeBindings_erase (inputs : List InferInput) {cores : List Expr}
    (h : completeBindings inputs = some cores) :
    cores.map Expr.erase = eraseBindings inputs := by
  cases inputs with
  | nil => cases h; rfl
  | cons body rest =>
      simp only [completeBindings, bind, pure, Option.bind_eq_some_iff,
        Option.some.injEq] at h
      obtain ⟨body', hb, rest', hr, rfl⟩ := h
      simp only [List.map_cons, eraseBindings, body.toCore_erase hb, completeBindings_erase rest hr]
theorem eraseBindings_length (inputs : List InferInput) : (eraseBindings inputs).length = inputs.length := by
  cases inputs with
  | nil => rfl
  | cons body rest =>
      simpa only [eraseBindings, List.length_cons] using congrArg Nat.succ (eraseBindings_length rest)
end

/-- A partial ordinary signature constrains the inferred monotype before that
monotype is generalised. It is not an existential complete Core signature. -/
def BindingAnn.FitsMono : BindingAnn → Ty → Prop
  | .absent, _ => True
  | .template t, ty => t.Fits ty
  | _, _ => False

mutual
/-- Instantiate a template at a local inference visit. No authored IDs or
cross-copy allocation table participate in this operation. -/
def TyTemplate.allocate (frontier : Nat) : TyTemplate → Nat × Ty
  | .fixed ty => (frontier, ty)
  | .hole => (frontier + 1, .fvar frontier)
  | .arrow a b =>
      let (next, ta) := a.allocate frontier
      let (last, tb) := b.allocate next
      (last, .arrow ta tb)
  | .custom name args =>
      let (next, tys) := allocateList frontier args
      (next, .customTy name tys)
def allocateList (frontier : Nat) : List TyTemplate → Nat × List Ty
  | [] => (frontier, [])
  | template :: rest =>
      let (next, ty) := template.allocate frontier
      let (last, tys) := allocateList next rest
      (last, ty :: tys)
end

mutual
theorem TyTemplate.allocate_fits (template : TyTemplate) (frontier : Nat) :
    template.Fits (template.allocate frontier).2 := by
  cases template with
  | fixed => exact .fixed
  | hole => exact .hole
  | arrow a b =>
      exact .arrow (a.allocate_fits frontier) (b.allocate_fits (a.allocate frontier).1)
  | custom name args => exact .custom (allocateList_fits args frontier)
theorem allocateList_fits (templates : List TyTemplate) (frontier : Nat) :
    List.Forall₂ TyTemplate.Fits templates (allocateList frontier templates).2 := by
  cases templates with
  | nil => exact .nil
  | cons template rest =>
      exact .cons (template.allocate_fits frontier) (allocateList_fits rest (template.allocate frontier).1)
end


mutual
/-- Term size ignores annotations, so opening written type binders preserves it. -/
def InferInput.size : InferInput → Nat
  | .primLit _ | .primBinOp _ | .var _ | .ctor _ => 1
  | .lambda _ body => body.size + 1
  | .app f arg => f.size + arg.size + 1
  | .letIn _ rhs body => rhs.size + body.size + 1
  | .match_ scrut branches => scrut.size + sizeBranches branches + 1
  | .letRec _ bindings body => sizeBindings bindings + body.size + 1
def sizeBranches : List (MatchPattern × InferInput) → Nat
  | [] => 0
  | (_, body) :: rest => 1 + body.size + sizeBranches rest
def sizeBindings : List InferInput → Nat
  | [] => 0
  | body :: rest => 1 + body.size + sizeBindings rest
end

/-- Authored free type variables are rigid; anonymous holes contribute none. -/
def BindingAnn.isSignature : BindingAnn → Bool
  | .complete _ | .partialForall _ _ => true
  | .absent | .template _ => false

def BindingAnn.rigidVars : BindingAnn → List Nat
  | .absent => []
  | .complete scheme => scheme.body.freeVars
  | .template t => t.rigidVars
  | .partialForall _ t => t.rigidVars

mutual
def InferInput.rigidVars : InferInput → List Nat
  | .primLit _ | .primBinOp _ | .var _ | .ctor _ => []
  | .lambda ann body => ann.elim [] TyTemplate.rigidVars ++ body.rigidVars
  | .app f arg => f.rigidVars ++ arg.rigidVars
  | .letIn ann rhs body => ann.rigidVars ++ rhs.rigidVars ++ body.rigidVars
  | .match_ scrut branches => scrut.rigidVars ++ rigidBranchVars branches
  | .letRec anns bindings body => anns.flatMap BindingAnn.rigidVars ++ rigidBindingVars bindings ++ body.rigidVars
def rigidBranchVars : List (MatchPattern × InferInput) → List Nat
  | [] => []
  | (_, body) :: rest => body.rigidVars ++ rigidBranchVars rest
def rigidBindingVars : List InferInput → List Nat
  | [] => []
  | body :: rest => body.rigidVars ++ rigidBindingVars rest
end

/-- Embed complete ordinary Core without changing annotation modes. -/
def BindingAnn.ofCore : Option PolyTy → BindingAnn
  | none => .absent
  | some scheme => .complete scheme

mutual
def InferInput.ofCore : Expr → InferInput
  | .primLit p => .primLit p
  | .primBinOp op => .primBinOp op
  | .lambda ann body => .lambda (ann.map TyTemplate.fixed) (InferInput.ofCore body)
  | .app f arg => .app (InferInput.ofCore f) (InferInput.ofCore arg)
  | .letIn ann rhs body => .letIn (BindingAnn.ofCore ann) (InferInput.ofCore rhs) (InferInput.ofCore body)
  | .var i => .var i
  | .ctor name => .ctor name
  | .match_ scrut branches => .match_ (InferInput.ofCore scrut) (ofCoreBranches branches)
  | .letRec anns bindings body =>
      .letRec (anns.map BindingAnn.ofCore) (ofCoreBindings bindings) (InferInput.ofCore body)
def ofCoreBranches : List (MatchPattern × Expr) → List (MatchPattern × InferInput)
  | [] => []
  | (pat, body) :: rest => (pat, (InferInput.ofCore body)) :: ofCoreBranches rest
def ofCoreBindings : List Expr → List InferInput
  | [] => []
  | body :: rest => (InferInput.ofCore body) :: ofCoreBindings rest
end

@[simp] theorem BindingAnn.toCore_ofCore (ann : Option PolyTy) :
    (BindingAnn.ofCore ann).toCore = some ann := by cases ann <;> rfl

private theorem completeAnns_ofCore (anns : List (Option PolyTy)) :
    completeAnns (anns.map BindingAnn.ofCore) = some anns := by
  induction anns with
  | nil => rfl
  | cons ann anns ih => simp only [List.map_cons, completeAnns, BindingAnn.toCore_ofCore, ih]; rfl

mutual
@[simp] theorem InferInput.toCore_ofCore (expr : Expr) : (InferInput.ofCore expr).toCore = some expr := by
  cases expr with
  | primLit => rfl
  | primBinOp => rfl
  | var => rfl
  | ctor => rfl
  | lambda ann body =>
    have ha : completeLambdaAnn (ann.map TyTemplate.fixed) = some ann := by cases ann <;> rfl
    simp only [InferInput.ofCore, InferInput.toCore, ha, InferInput.toCore_ofCore body]; rfl
  | app f arg => simp only [InferInput.ofCore, InferInput.toCore, InferInput.toCore_ofCore f, InferInput.toCore_ofCore arg]; rfl
  | letIn ann rhs body =>
    simp only [InferInput.ofCore, InferInput.toCore, BindingAnn.toCore_ofCore, InferInput.toCore_ofCore rhs, InferInput.toCore_ofCore body]; rfl
  | match_ scrut branches =>
    simp only [InferInput.ofCore, InferInput.toCore, InferInput.toCore_ofCore scrut, completeBranches_ofCore branches]; rfl
  | letRec anns bindings body =>
    simp only [InferInput.ofCore, InferInput.toCore, completeAnns_ofCore, completeBindings_ofCore bindings,
      InferInput.toCore_ofCore body]; rfl
theorem completeBranches_ofCore (branches : List (MatchPattern × Expr)) :
    completeBranches (ofCoreBranches branches) = some branches := by
  cases branches with
  | nil => rfl
  | cons pair rest =>
    rcases pair with ⟨pat, body⟩
    simp only [ofCoreBranches, completeBranches, InferInput.toCore_ofCore body, completeBranches_ofCore rest]; rfl
theorem completeBindings_ofCore (bindings : List Expr) :
    completeBindings (ofCoreBindings bindings) = some bindings := by
  cases bindings with
  | nil => rfl
  | cons body rest =>
    simp only [ofCoreBindings, completeBindings, InferInput.toCore_ofCore body, completeBindings_ofCore rest]; rfl
end

mutual
/-- Shift term variables while preserving every authored partial annotation. -/
def InferInput.shiftFrom (threshold count : Nat) : InferInput → InferInput
  | .var i => if i < threshold then .var i else .var (i + count)
  | .primLit p => .primLit p
  | .primBinOp op => .primBinOp op
  | .lambda ann body => .lambda ann (body.shiftFrom (threshold + 1) count)
  | .app f arg => .app (f.shiftFrom threshold count) (arg.shiftFrom threshold count)
  | .letIn ann rhs body => .letIn ann (rhs.shiftFrom threshold count) (body.shiftFrom (threshold + 1) count)
  | .ctor name => .ctor name
  | .match_ scrut branches => .match_ (scrut.shiftFrom threshold count) (shiftBranches threshold count branches)
  | .letRec anns bindings body => .letRec anns
      (shiftBindings (threshold + bindings.length) count bindings)
      (body.shiftFrom (threshold + bindings.length) count)
def shiftBranches (threshold count : Nat) : List (MatchPattern × InferInput) → List (MatchPattern × InferInput)
  | [] => []
  | (pat, body) :: rest =>
      (pat, body.shiftFrom (threshold + pat.bindCount) count) :: shiftBranches threshold count rest
def shiftBindings (threshold count : Nat) : List InferInput → List InferInput
  | [] => []
  | body :: rest => body.shiftFrom threshold count :: shiftBindings threshold count rest
end


mutual
/-- Open an enclosing written type-variable block through a template. Anonymous
holes are unchanged and never acquire an authored variable identity. -/
def TyTemplate.openTyVarsFrom (d : Nat) (Xs : List Nat) : TyTemplate → TyTemplate
  | .fixed ty => .fixed (ty.openVarsFrom d Xs)
  | .hole => .hole
  | .arrow a b => .arrow (a.openTyVarsFrom d Xs) (b.openTyVarsFrom d Xs)
  | .custom name args => .custom name (openTemplateList d Xs args)
def openTemplateList (d : Nat) (Xs : List Nat) : List TyTemplate → List TyTemplate
  | [] => []
  | t :: ts => t.openTyVarsFrom d Xs :: openTemplateList d Xs ts
end

/-- A signature's own binders shield its annotation and RHS, but not the let
continuation. This also applies when its body contains anonymous holes. -/
def BindingAnn.paramCount : BindingAnn → Nat
  | .complete scheme => scheme.paramCount
  | .partialForall n _ => n
  | .absent | .template _ => 0

def BindingAnn.openTyVarsFrom (d : Nat) (Xs : List Nat) : BindingAnn → BindingAnn
  | .absent => .absent
  | .complete scheme => .complete { scheme with
      body := scheme.body.openVarsFrom (d + scheme.paramCount) Xs }
  | .template t => .template (t.openTyVarsFrom d Xs)
  | .partialForall n t => .partialForall n (t.openTyVarsFrom (d + n) Xs)

mutual
/-- Open the type binders of an enclosing signature with the same scope rules
as `Expr.openTyVarsAux`, retaining every partial annotation mode. -/
def InferInput.openTyVarsFrom (d : Nat) (Xs : List Nat) : InferInput → InferInput
  | .primLit p => .primLit p
  | .primBinOp op => .primBinOp op
  | .lambda ann body => .lambda (ann.map (TyTemplate.openTyVarsFrom d Xs))
      (body.openTyVarsFrom d Xs)
  | .app f arg => .app (f.openTyVarsFrom d Xs) (arg.openTyVarsFrom d Xs)
  | .letIn ann rhs body => .letIn (ann.openTyVarsFrom d Xs)
      (rhs.openTyVarsFrom (d + ann.paramCount) Xs) (body.openTyVarsFrom d Xs)
  | .var i => .var i
  | .ctor name => .ctor name
  | .match_ scrut branches => .match_ (scrut.openTyVarsFrom d Xs)
      (openInputBranches d Xs branches)
  | .letRec anns bindings body => .letRec (anns.map (BindingAnn.openTyVarsFrom d Xs))
      (openInputBindings d Xs anns bindings) (body.openTyVarsFrom d Xs)
def openInputBranches (d : Nat) (Xs : List Nat) :
    List (MatchPattern × InferInput) → List (MatchPattern × InferInput)
  | [] => []
  | (pat, body) :: rest => (pat, body.openTyVarsFrom d Xs) :: openInputBranches d Xs rest
/-- As in Core, missing recursion annotations are treated as absent; extra
annotations do not introduce binders over another member. -/
def openInputBindings (d : Nat) (Xs : List Nat) : List BindingAnn → List InferInput → List InferInput
  | _, [] => []
  | [], body :: rest => body.openTyVarsFrom d Xs :: openInputBindings d Xs [] rest
  | ann :: anns, body :: rest => body.openTyVarsFrom (d + ann.paramCount) Xs ::
      openInputBindings d Xs anns rest
end

def InferInput.openTyVars (Xs : List Nat) (input : InferInput) : InferInput := input.openTyVarsFrom 0 Xs

@[simp] theorem BindingAnn.paramCount_openTyVarsFrom (ann : BindingAnn) (d : Nat) (Xs : List Nat) :
    (ann.openTyVarsFrom d Xs).paramCount = ann.paramCount := by cases ann <;> rfl

mutual
@[simp] theorem InferInput.size_openTyVarsFrom (input : InferInput) (d : Nat) (Xs : List Nat) :
    (input.openTyVarsFrom d Xs).size = input.size := by
  cases input with
  | primLit | primBinOp | var | ctor => rfl
  | lambda ann body => simp only [InferInput.openTyVarsFrom, InferInput.size, body.size_openTyVarsFrom d Xs]
  | app f a => simp only [InferInput.openTyVarsFrom, InferInput.size, f.size_openTyVarsFrom d Xs, a.size_openTyVarsFrom d Xs]
  | letIn ann rhs body => simp only [InferInput.openTyVarsFrom, InferInput.size,
      rhs.size_openTyVarsFrom (d + ann.paramCount) Xs, body.size_openTyVarsFrom d Xs]
  | match_ scrut branches => simp only [InferInput.openTyVarsFrom, InferInput.size,
      scrut.size_openTyVarsFrom d Xs, sizeBranches_openInputBranches branches d Xs]
  | letRec anns bindings body => simp only [InferInput.openTyVarsFrom, InferInput.size,
      sizeBindings_openInputBindings bindings anns d Xs, body.size_openTyVarsFrom d Xs]
termination_by sizeOf input
theorem sizeBranches_openInputBranches (branches : List (MatchPattern × InferInput)) (d : Nat) (Xs : List Nat) :
    sizeBranches (openInputBranches d Xs branches) = sizeBranches branches := by
  cases branches with
  | nil => rfl
  | cons pair rest =>
      rcases pair with ⟨pat, body⟩
      simp only [openInputBranches, sizeBranches, body.size_openTyVarsFrom d Xs,
        sizeBranches_openInputBranches rest d Xs]
termination_by sizeOf branches
theorem sizeBindings_openInputBindings (bindings : List InferInput) (anns : List BindingAnn) (d : Nat) (Xs : List Nat) :
    sizeBindings (openInputBindings d Xs anns bindings) = sizeBindings bindings := by
  cases bindings with
  | nil => rfl
  | cons body rest =>
      cases anns with
      | nil => simp only [openInputBindings, sizeBindings, body.size_openTyVarsFrom d Xs,
          sizeBindings_openInputBindings rest [] d Xs]
      | cons ann anns => simp only [openInputBindings, sizeBindings,
          body.size_openTyVarsFrom (d + ann.paramCount) Xs,
          sizeBindings_openInputBindings rest anns d Xs]
termination_by sizeOf bindings
end

@[simp] theorem InferInput.size_openTyVars (input : InferInput) (Xs : List Nat) :
    (input.openTyVars Xs).size = input.size := input.size_openTyVarsFrom 0 Xs

theorem openInputBindings_length (bindings : List InferInput) (anns : List BindingAnn) (d : Nat) (Xs : List Nat) :
    (openInputBindings d Xs anns bindings).length = bindings.length := by
  induction bindings generalizing anns with
  | nil => rfl
  | cons body rest ih => cases anns <;> simp only [openInputBindings, List.length_cons, ih]

mutual
@[simp] theorem InferInput.erase_openTyVarsFrom (input : InferInput) (d : Nat) (Xs : List Nat) :
    (input.openTyVarsFrom d Xs).erase = input.erase := by
  cases input with
  | primLit | primBinOp | var | ctor => rfl
  | lambda ann body => simp only [InferInput.openTyVarsFrom, InferInput.erase, body.erase_openTyVarsFrom d Xs]
  | app f a => simp only [InferInput.openTyVarsFrom, InferInput.erase, f.erase_openTyVarsFrom d Xs, a.erase_openTyVarsFrom d Xs]
  | letIn ann rhs body => simp only [InferInput.openTyVarsFrom, InferInput.erase,
      rhs.erase_openTyVarsFrom (d + ann.paramCount) Xs, body.erase_openTyVarsFrom d Xs]
  | match_ scrut branches => simp only [InferInput.openTyVarsFrom, InferInput.erase,
      scrut.erase_openTyVarsFrom d Xs, eraseBranches_openInputBranches branches d Xs]
  | letRec anns bindings body => simp only [InferInput.openTyVarsFrom, InferInput.erase,
      eraseBindings_openInputBindings bindings anns d Xs, body.erase_openTyVarsFrom d Xs,
      List.map_const', openInputBindings_length]
termination_by sizeOf input
theorem eraseBranches_openInputBranches (branches : List (MatchPattern × InferInput)) (d : Nat) (Xs : List Nat) :
    eraseBranches (openInputBranches d Xs branches) = eraseBranches branches := by
  cases branches with
  | nil => rfl
  | cons pair rest =>
      rcases pair with ⟨pat, body⟩
      simp only [openInputBranches, eraseBranches, body.erase_openTyVarsFrom d Xs,
        eraseBranches_openInputBranches rest d Xs]
termination_by sizeOf branches
theorem eraseBindings_openInputBindings (bindings : List InferInput) (anns : List BindingAnn) (d : Nat) (Xs : List Nat) :
    eraseBindings (openInputBindings d Xs anns bindings) = eraseBindings bindings := by
  cases bindings with
  | nil => rfl
  | cons body rest =>
      cases anns with
      | nil => simp only [openInputBindings, eraseBindings, body.erase_openTyVarsFrom d Xs,
          eraseBindings_openInputBindings rest [] d Xs]
      | cons ann anns => simp only [openInputBindings, eraseBindings,
          body.erase_openTyVarsFrom (d + ann.paramCount) Xs,
          eraseBindings_openInputBindings rest anns d Xs]
termination_by sizeOf bindings
end

@[simp] theorem InferInput.erase_openTyVars (input : InferInput) (Xs : List Nat) :
    (input.openTyVars Xs).erase = input.erase := input.erase_openTyVarsFrom 0 Xs


mutual
theorem TyTemplate.toCore_openTyVarsFrom (template : TyTemplate) {ty : Ty}
    (h : template.toCore = some ty) (d : Nat) (Xs : List Nat) :
    (template.openTyVarsFrom d Xs).toCore = some (ty.openVarsFrom d Xs) := by
  cases template with
  | fixed t => cases h; rfl
  | hole => cases h
  | arrow a b =>
      simp only [TyTemplate.toCore, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at h
      obtain ⟨ta, ha, tb, hb, rfl⟩ := h
      simp only [TyTemplate.openTyVarsFrom, TyTemplate.toCore, a.toCore_openTyVarsFrom ha d Xs,
        b.toCore_openTyVarsFrom hb d Xs]
      rfl
  | custom name args =>
      simp only [TyTemplate.toCore, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at h
      obtain ⟨tys, ht, rfl⟩ := h
      simp only [TyTemplate.openTyVarsFrom, TyTemplate.toCore, completeTypes_openTemplateList args ht d Xs,
        Ty.openVarsFrom_customTy]
      rfl
theorem completeTypes_openTemplateList (templates : List TyTemplate) {tys : List Ty}
    (h : completeTypes templates = some tys) (d : Nat) (Xs : List Nat) :
    completeTypes (openTemplateList d Xs templates) = some (tys.map (Ty.openVarsFrom d Xs)) := by
  cases templates with
  | nil => cases h; rfl
  | cons t ts =>
      simp only [completeTypes, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at h
      obtain ⟨ty, ht, tys, hts, rfl⟩ := h
      simp only [openTemplateList, completeTypes, t.toCore_openTyVarsFrom ht d Xs,
        completeTypes_openTemplateList ts hts d Xs]
      rfl
end

theorem completeLambdaAnn_openTyVarsFrom (ann : Option TyTemplate) {core : Option Ty}
    (h : completeLambdaAnn ann = some core) (d : Nat) (Xs : List Nat) :
    completeLambdaAnn (ann.map (TyTemplate.openTyVarsFrom d Xs)) =
      some (core.map (Ty.openVarsFrom d Xs)) := by
  cases ann with
  | none => cases h; rfl
  | some template =>
      simp only [completeLambdaAnn, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at h
      obtain ⟨ty, ht, rfl⟩ := h
      simp only [Option.map_some, completeLambdaAnn, template.toCore_openTyVarsFrom ht d Xs]
      rfl

theorem BindingAnn.toCore_openTyVarsFrom (ann : BindingAnn) {core : Option PolyTy}
    (h : ann.toCore = some core) (d : Nat) (Xs : List Nat) :
    (ann.openTyVarsFrom d Xs).toCore = some (core.map (fun scheme =>
      { scheme with body := scheme.body.openVarsFrom (d + scheme.paramCount) Xs })) := by
  cases ann <;> cases h <;> rfl

theorem BindingAnn.paramCount_toCore (ann : BindingAnn) {core : Option PolyTy}
    (h : ann.toCore = some core) : ann.paramCount = RecAnn.params core := by
  cases ann <;> cases h <;> rfl

theorem completeAnns_openTyVarsFrom (anns : List BindingAnn) {cores : List (Option PolyTy)}
    (h : completeAnns anns = some cores) (d : Nat) (Xs : List Nat) :
    completeAnns (anns.map (BindingAnn.openTyVarsFrom d Xs)) = some (RecGroup.openAnns d Xs cores) := by
  induction anns generalizing cores with
  | nil => cases h; rfl
  | cons ann anns ih =>
      simp only [completeAnns, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at h
      obtain ⟨core, ha, cores, has, rfl⟩ := h
      simp only [List.map_cons, completeAnns, ann.toCore_openTyVarsFrom ha d Xs, ih has]
      rfl

mutual
/-- Successful conservative embedding commutes with opening an outer signature;
all nested complete signatures retain the shielding used by ordinary Core. -/
theorem InferInput.toCore_openTyVarsFrom (input : InferInput) {core : Expr}
    (h : input.toCore = some core) (d : Nat) (Xs : List Nat) :
    (input.openTyVarsFrom d Xs).toCore = some (core.openTyVarsAux d Xs) := by
  cases input with
  | primLit p => cases h; rfl
  | primBinOp op => cases h; rfl
  | var i => cases h; rfl
  | ctor name => cases h; rfl
  | lambda ann body =>
      simp only [InferInput.toCore, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at h
      obtain ⟨ann', ha, body', hb, rfl⟩ := h
      simp only [InferInput.openTyVarsFrom, InferInput.toCore, completeLambdaAnn_openTyVarsFrom ann ha d Xs,
        body.toCore_openTyVarsFrom hb d Xs]
      rfl
  | app f arg =>
      simp only [InferInput.toCore, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at h
      obtain ⟨f', hf, arg', ha, rfl⟩ := h
      simp only [InferInput.openTyVarsFrom, InferInput.toCore, f.toCore_openTyVarsFrom hf d Xs,
        arg.toCore_openTyVarsFrom ha d Xs]
      rfl
  | letIn ann rhs body =>
      simp only [InferInput.toCore, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at h
      obtain ⟨ann', ha, rhs', hr, body', hb, rfl⟩ := h
      simp only [InferInput.openTyVarsFrom, InferInput.toCore, ann.toCore_openTyVarsFrom ha d Xs,
        rhs.toCore_openTyVarsFrom hr (d + ann.paramCount) Xs, body.toCore_openTyVarsFrom hb d Xs]
      rw [ann.paramCount_toCore ha]
      cases ann' <;> rfl
  | match_ scrut branches =>
      simp only [InferInput.toCore, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at h
      obtain ⟨scrut', hs, branches', hbs, rfl⟩ := h
      simp only [InferInput.openTyVarsFrom, InferInput.toCore, scrut.toCore_openTyVarsFrom hs d Xs,
        completeBranches_openTyVarsFrom branches hbs d Xs]
      rfl
  | letRec anns bindings body =>
      simp only [InferInput.toCore, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at h
      obtain ⟨anns', ha, bindings', hbs, body', hb, rfl⟩ := h
      simp only [InferInput.openTyVarsFrom, InferInput.toCore, completeAnns_openTyVarsFrom anns ha d Xs,
        completeBindings_openTyVarsFrom bindings anns ha hbs d Xs,
        body.toCore_openTyVarsFrom hb d Xs]
      rfl
termination_by sizeOf input
decreasing_by all_goals (subst_vars; simp_wf <;> omega)

theorem completeBranches_openTyVarsFrom (branches : List (MatchPattern × InferInput))
    {cores : List (MatchPattern × Expr)} (h : completeBranches branches = some cores)
    (d : Nat) (Xs : List Nat) :
    completeBranches (openInputBranches d Xs branches) = some (BranchList.openTyVarsAux d Xs cores) := by
  cases branches with
  | nil => cases h; rfl
  | cons pair rest =>
      simp only [completeBranches, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at h
      obtain ⟨body', hb, rest', hr, rfl⟩ := h
      simp only [openInputBranches, completeBranches, pair.2.toCore_openTyVarsFrom hb d Xs,
        completeBranches_openTyVarsFrom rest hr d Xs]
      rfl
termination_by sizeOf branches
decreasing_by all_goals (subst_vars; cases pair; simp_wf <;> omega)

theorem completeBindings_openTyVarsFrom (bindings : List InferInput) (anns : List BindingAnn)
    {coreAnns : List (Option PolyTy)} {cores : List Expr}
    (ha : completeAnns anns = some coreAnns) (h : completeBindings bindings = some cores)
    (d : Nat) (Xs : List Nat) :
    completeBindings (openInputBindings d Xs anns bindings) =
      some (RecGroup.openTyVarsAux d Xs coreAnns cores) := by
  cases bindings with
  | nil => cases h; rfl
  | cons body rest =>
      simp only [completeBindings, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at h
      obtain ⟨body', hb, rest', hr, rfl⟩ := h
      cases anns with
      | nil =>
          cases ha
          simp only [openInputBindings, completeBindings, body.toCore_openTyVarsFrom hb d Xs,
            completeBindings_openTyVarsFrom rest [] rfl hr d Xs]
          rfl
      | cons ann anns =>
          simp only [completeAnns, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at ha
          obtain ⟨coreAnn, ha, coreAnns, has, rfl⟩ := ha
          simp only [openInputBindings, completeBindings,
            body.toCore_openTyVarsFrom hb (d + ann.paramCount) Xs,
            completeBindings_openTyVarsFrom rest anns has hr d Xs]
          rw [ann.paramCount_toCore ha]
          rfl
termination_by sizeOf bindings
decreasing_by all_goals (subst_vars; simp_wf <;> omega)
end

theorem InferInput.toCore_openTyVars (input : InferInput) {core : Expr}
    (h : input.toCore = some core) (Xs : List Nat) :
    (input.openTyVars Xs).toCore = some (core.openTyVars Xs) :=
  input.toCore_openTyVarsFrom h 0 Xs

mutual
/-- Substitute only free variables in authored type leaves; anonymous holes
remain unallocated and independent. -/
def TyTemplate.substTyFvars (subst : List (Nat × Ty)) : TyTemplate → TyTemplate
  | .fixed ty => .fixed (ty.substFvars subst)
  | .hole => .hole
  | .arrow a b => .arrow (a.substTyFvars subst) (b.substTyFvars subst)
  | .custom name args => .custom name (substTemplateList subst args)
def substTemplateList (subst : List (Nat × Ty)) : List TyTemplate → List TyTemplate
  | [] => []
  | t :: ts => t.substTyFvars subst :: substTemplateList subst ts
end

/-- Free type substitution preserves annotation modes and written binders. -/
def BindingAnn.substTyFvars (subst : List (Nat × Ty)) : BindingAnn → BindingAnn
  | .absent => .absent
  | .complete scheme => .complete { scheme with body := scheme.body.substFvars subst }
  | .template t => .template (t.substTyFvars subst)
  | .partialForall n t => .partialForall n (t.substTyFvars subst)

mutual
/-- Type substitution does not shift under type or term binders: all replaced
variables are free, just as for `Expr.substTyFvars`. -/
def InferInput.substTyFvars (subst : List (Nat × Ty)) : InferInput → InferInput
  | .primLit p => .primLit p
  | .primBinOp op => .primBinOp op
  | .lambda ann body => .lambda (ann.map (TyTemplate.substTyFvars subst)) (body.substTyFvars subst)
  | .app f arg => .app (f.substTyFvars subst) (arg.substTyFvars subst)
  | .letIn ann rhs body => .letIn (ann.substTyFvars subst) (rhs.substTyFvars subst) (body.substTyFvars subst)
  | .var i => .var i
  | .ctor name => .ctor name
  | .match_ scrut branches => .match_ (scrut.substTyFvars subst) (substInputBranches subst branches)
  | .letRec anns bindings body => .letRec (anns.map (BindingAnn.substTyFvars subst))
      (substInputBindings subst bindings) (body.substTyFvars subst)
def substInputBranches (subst : List (Nat × Ty)) :
    List (MatchPattern × InferInput) → List (MatchPattern × InferInput)
  | [] => []
  | (pat, body) :: rest => (pat, body.substTyFvars subst) :: substInputBranches subst rest
def substInputBindings (subst : List (Nat × Ty)) : List InferInput → List InferInput
  | [] => []
  | body :: rest => body.substTyFvars subst :: substInputBindings subst rest
end

@[simp] theorem BindingAnn.isSignature_substTyFvars (ann : BindingAnn) (subst : List (Nat × Ty)) :
    (ann.substTyFvars subst).isSignature = ann.isSignature := by cases ann <;> rfl

@[simp] theorem BindingAnn.paramCount_substTyFvars (ann : BindingAnn) (subst : List (Nat × Ty)) :
    (ann.substTyFvars subst).paramCount = ann.paramCount := by cases ann <;> rfl

theorem substInputBranches_eq_map (subst : List (Nat × Ty)) (branches : List (MatchPattern × InferInput)) :
    substInputBranches subst branches = branches.map (fun b => (b.1, b.2.substTyFvars subst)) := by
  induction branches with
  | nil => rfl
  | cons head rest ih => cases head; simp only [substInputBranches, List.map_cons, ih]

@[simp] theorem substInputBranches_eq_nil (subst : List (Nat × Ty))
    (branches : List (MatchPattern × InferInput)) :
    substInputBranches subst branches = [] ↔ branches = [] := by
  cases branches <;> simp [substInputBranches]

mutual
@[simp] theorem InferInput.size_substTyFvars (input : InferInput) (subst : List (Nat × Ty)) :
    (input.substTyFvars subst).size = input.size := by
  cases input with
  | primLit | primBinOp | var | ctor => rfl
  | lambda ann body => simp only [InferInput.substTyFvars, InferInput.size, body.size_substTyFvars subst]
  | app f a => simp only [InferInput.substTyFvars, InferInput.size, f.size_substTyFvars subst, a.size_substTyFvars subst]
  | letIn ann rhs body => simp only [InferInput.substTyFvars, InferInput.size,
      rhs.size_substTyFvars subst, body.size_substTyFvars subst]
  | match_ scrut branches => simp only [InferInput.substTyFvars, InferInput.size,
      scrut.size_substTyFvars subst, sizeBranches_substInputBranches branches subst]
  | letRec anns bindings body => simp only [InferInput.substTyFvars, InferInput.size,
      sizeBindings_substInputBindings bindings subst, body.size_substTyFvars subst]
termination_by sizeOf input
theorem sizeBranches_substInputBranches (branches : List (MatchPattern × InferInput)) (subst : List (Nat × Ty)) :
    sizeBranches (substInputBranches subst branches) = sizeBranches branches := by
  cases branches with
  | nil => rfl
  | cons pair rest =>
      rcases pair with ⟨pat, body⟩
      simp only [substInputBranches, sizeBranches, body.size_substTyFvars subst,
        sizeBranches_substInputBranches rest subst]
termination_by sizeOf branches
theorem sizeBindings_substInputBindings (bindings : List InferInput) (subst : List (Nat × Ty)) :
    sizeBindings (substInputBindings subst bindings) = sizeBindings bindings := by
  cases bindings with
  | nil => rfl
  | cons body rest =>
      simp only [substInputBindings, sizeBindings, body.size_substTyFvars subst,
          sizeBindings_substInputBindings rest subst]
termination_by sizeOf bindings
end

theorem substInputBindings_length (bindings : List InferInput) (subst : List (Nat × Ty)) :
    (substInputBindings subst bindings).length = bindings.length := by
  induction bindings with
  | nil => rfl
  | cons body rest ih => simp only [substInputBindings, List.length_cons, ih]

mutual
@[simp] theorem InferInput.erase_substTyFvars (input : InferInput) (subst : List (Nat × Ty)) :
    (input.substTyFvars subst).erase = input.erase := by
  cases input with
  | primLit | primBinOp | var | ctor => rfl
  | lambda ann body => simp only [InferInput.substTyFvars, InferInput.erase, body.erase_substTyFvars subst]
  | app f a => simp only [InferInput.substTyFvars, InferInput.erase, f.erase_substTyFvars subst, a.erase_substTyFvars subst]
  | letIn ann rhs body => simp only [InferInput.substTyFvars, InferInput.erase,
      rhs.erase_substTyFvars subst, body.erase_substTyFvars subst]
  | match_ scrut branches => simp only [InferInput.substTyFvars, InferInput.erase,
      scrut.erase_substTyFvars subst, eraseBranches_substInputBranches branches subst]
  | letRec anns bindings body => simp only [InferInput.substTyFvars, InferInput.erase,
      eraseBindings_substInputBindings bindings subst, body.erase_substTyFvars subst,
      List.map_const', substInputBindings_length]
termination_by sizeOf input
theorem eraseBranches_substInputBranches (branches : List (MatchPattern × InferInput)) (subst : List (Nat × Ty)) :
    eraseBranches (substInputBranches subst branches) = eraseBranches branches := by
  cases branches with
  | nil => rfl
  | cons pair rest =>
      rcases pair with ⟨pat, body⟩
      simp only [substInputBranches, eraseBranches, body.erase_substTyFvars subst,
        eraseBranches_substInputBranches rest subst]
termination_by sizeOf branches
theorem eraseBindings_substInputBindings (bindings : List InferInput) (subst : List (Nat × Ty)) :
    eraseBindings (substInputBindings subst bindings) = eraseBindings bindings := by
  cases bindings with
  | nil => rfl
  | cons body rest =>
      simp only [substInputBindings, eraseBindings, body.erase_substTyFvars subst,
          eraseBindings_substInputBindings rest subst]
termination_by sizeOf bindings
end

mutual
theorem TyTemplate.toCore_substTyFvars (template : TyTemplate) {ty : Ty}
    (h : template.toCore = some ty) (subst : List (Nat × Ty)) :
    (template.substTyFvars subst).toCore = some (ty.substFvars subst) := by
  cases template with
  | fixed t => cases h; rfl
  | hole => cases h
  | arrow a b =>
      simp only [TyTemplate.toCore, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at h
      obtain ⟨ta, ha, tb, hb, rfl⟩ := h
      simp only [TyTemplate.substTyFvars, TyTemplate.toCore, a.toCore_substTyFvars ha subst,
        b.toCore_substTyFvars hb subst, Ty.substFvars_arrow]
      rfl
  | custom name args =>
      simp only [TyTemplate.toCore, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at h
      obtain ⟨tys, ht, rfl⟩ := h
      simp only [TyTemplate.substTyFvars, TyTemplate.toCore, completeTypes_substTemplateList args ht subst,
        Ty.substFvars_customTy]
      rfl
theorem completeTypes_substTemplateList (templates : List TyTemplate) {tys : List Ty}
    (h : completeTypes templates = some tys) (subst : List (Nat × Ty)) :
    completeTypes (substTemplateList subst templates) = some (tys.map (Ty.substFvars subst)) := by
  cases templates with
  | nil => cases h; rfl
  | cons t ts =>
      simp only [completeTypes, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at h
      obtain ⟨ty, ht, tys, hts, rfl⟩ := h
      simp only [substTemplateList, completeTypes, t.toCore_substTyFvars ht subst,
        completeTypes_substTemplateList ts hts subst]
      rfl
end

theorem completeLambdaAnn_substTyFvars (ann : Option TyTemplate) {core : Option Ty}
    (h : completeLambdaAnn ann = some core) (subst : List (Nat × Ty)) :
    completeLambdaAnn (ann.map (TyTemplate.substTyFvars subst)) =
      some (core.map (Ty.substFvars subst)) := by
  cases ann with
  | none => cases h; rfl
  | some template =>
      simp only [completeLambdaAnn, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at h
      obtain ⟨ty, ht, rfl⟩ := h
      simp only [Option.map_some, completeLambdaAnn, template.toCore_substTyFvars ht subst]
      rfl

theorem BindingAnn.toCore_substTyFvars (ann : BindingAnn) {core : Option PolyTy}
    (h : ann.toCore = some core) (subst : List (Nat × Ty)) :
    (ann.substTyFvars subst).toCore = some (core.map (fun scheme =>
      { scheme with body := scheme.body.substFvars subst })) := by
  cases ann <;> cases h <;> rfl

theorem completeAnns_substTyFvars (anns : List BindingAnn) {cores : List (Option PolyTy)}
    (h : completeAnns anns = some cores) (subst : List (Nat × Ty)) :
    completeAnns (anns.map (BindingAnn.substTyFvars subst)) = some (cores.map (Option.map (fun scheme => {scheme with body := scheme.body.substFvars subst}))) := by
  induction anns generalizing cores with
  | nil => cases h; rfl
  | cons ann anns ih =>
      simp only [completeAnns, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at h
      obtain ⟨core, ha, cores, has, rfl⟩ := h
      simp only [List.map_cons, completeAnns, ann.toCore_substTyFvars ha subst, ih has]
      rfl

mutual
/-- Conservative embedding commutes with free type substitution. -/
theorem InferInput.toCore_substTyFvars (input : InferInput) {core : Expr}
    (h : input.toCore = some core) (subst : List (Nat × Ty)) :
    (input.substTyFvars subst).toCore = some (core.substTyFvars subst) := by
  cases input with
  | primLit p =>
      cases h
      induction subst with
      | nil => rfl
      | cons pair rest ih => cases pair; simpa only [InferInput.substTyFvars, InferInput.toCore, Expr.substTyFvars, Expr.substTyFvar] using ih
  | primBinOp op =>
      cases h
      induction subst with
      | nil => rfl
      | cons pair rest ih => cases pair; simpa only [InferInput.substTyFvars, InferInput.toCore, Expr.substTyFvars, Expr.substTyFvar] using ih
  | var i => cases h; simp only [InferInput.substTyFvars, InferInput.toCore, Expr.substTyFvars_var]
  | ctor name =>
      cases h
      induction subst with
      | nil => rfl
      | cons pair rest ih => cases pair; simpa only [InferInput.substTyFvars, InferInput.toCore, Expr.substTyFvars, Expr.substTyFvar] using ih
  | lambda ann body =>
      simp only [InferInput.toCore, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at h
      obtain ⟨ann', ha, body', hb, rfl⟩ := h
      simp only [InferInput.substTyFvars, InferInput.toCore, completeLambdaAnn_substTyFvars ann ha subst,
        body.toCore_substTyFvars hb subst, Expr.substTyFvars_lambda]
      rfl
  | app f arg =>
      simp only [InferInput.toCore, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at h
      obtain ⟨f', hf, arg', ha, rfl⟩ := h
      simp only [InferInput.substTyFvars, InferInput.toCore, f.toCore_substTyFvars hf subst,
        arg.toCore_substTyFvars ha subst, Expr.substTyFvars_app]
      rfl
  | letIn ann rhs body =>
      simp only [InferInput.toCore, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at h
      obtain ⟨ann', ha, rhs', hr, body', hb, rfl⟩ := h
      simp only [InferInput.substTyFvars, InferInput.toCore, ann.toCore_substTyFvars ha subst,
        rhs.toCore_substTyFvars hr subst, body.toCore_substTyFvars hb subst]
      rw [Expr.substTyFvars_letIn]
      rfl
  | match_ scrut branches =>
      simp only [InferInput.toCore, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at h
      obtain ⟨scrut', hs, branches', hbs, rfl⟩ := h
      simp only [InferInput.substTyFvars, InferInput.toCore, scrut.toCore_substTyFvars hs subst,
        completeBranches_substTyFvars branches hbs subst, Expr.substTyFvars_match]
      rfl
  | letRec anns bindings body =>
      simp only [InferInput.toCore, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at h
      obtain ⟨anns', ha, bindings', hbs, body', hb, rfl⟩ := h
      simp only [InferInput.substTyFvars, InferInput.toCore, completeAnns_substTyFvars anns ha subst,
        completeBindings_substTyFvars bindings hbs subst,
        body.toCore_substTyFvars hb subst, Expr.substTyFvars_letRec]
      have hann : RecAnn.substFvars subst = Option.map (fun scheme =>
          { scheme with body := scheme.body.substFvars subst }) := by
        funext ann; cases ann <;> simp only [RecAnn.substFvars_none, RecAnn.substFvars_some,
          PolyTy.substFvars_eq, Option.map_none, Option.map_some]
      rw [hann]
      rfl
termination_by sizeOf input
decreasing_by all_goals (subst_vars; simp_wf <;> omega)

theorem completeBranches_substTyFvars (branches : List (MatchPattern × InferInput))
    {cores : List (MatchPattern × Expr)} (h : completeBranches branches = some cores)
    (subst : List (Nat × Ty)) :
    completeBranches (substInputBranches subst branches) = some (cores.map (fun pair => (pair.1, pair.2.substTyFvars subst))) := by
  cases branches with
  | nil => cases h; rfl
  | cons pair rest =>
      simp only [completeBranches, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at h
      obtain ⟨body', hb, rest', hr, rfl⟩ := h
      simp only [substInputBranches, completeBranches, pair.2.toCore_substTyFvars hb subst,
        completeBranches_substTyFvars rest hr subst]
      rfl
termination_by sizeOf branches
decreasing_by all_goals (subst_vars; cases pair; simp_wf <;> omega)

theorem completeBindings_substTyFvars (bindings : List InferInput) {cores : List Expr}
    (h : completeBindings bindings = some cores) (subst : List (Nat × Ty)) :
    completeBindings (substInputBindings subst bindings) = some (cores.map (Expr.substTyFvars subst)) := by
  cases bindings with
  | nil => cases h; rfl
  | cons body rest =>
      simp only [completeBindings, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at h
      obtain ⟨body', hb, rest', hr, rfl⟩ := h
      simp only [substInputBindings, completeBindings, body.toCore_substTyFvars hb subst,
        completeBindings_substTyFvars rest hr subst]
      rfl
termination_by sizeOf bindings
end

mutual
theorem TyTemplate.substTyFvars_zip_openTyVarsFrom (template : TyTemplate) {Ys Xs : List Nat}
    (hlen : Ys.length = Xs.length) (hnd : Ys.Nodup) (hfresh : ∀ y ∈ Ys, y ∉ template.rigidVars)
    (hdisj : ∀ y ∈ Ys, y ∉ Xs) (d : Nat) :
    (template.openTyVarsFrom d Ys).substTyFvars (Ys.zip (Xs.map Ty.fvar)) =
      template.openTyVarsFrom d Xs := by
  cases template with
  | fixed ty => exact congrArg TyTemplate.fixed (Ty.substFvars_zip_openVarsFrom hlen hnd hfresh hdisj)
  | hole => rfl
  | arrow a b =>
      rw [TyTemplate.openTyVarsFrom, TyTemplate.substTyFvars, TyTemplate.openTyVarsFrom,
        a.substTyFvars_zip_openTyVarsFrom hlen hnd
          (fun y hy hv => hfresh y hy (List.mem_append_left _ hv)) hdisj d,
        b.substTyFvars_zip_openTyVarsFrom hlen hnd
          (fun y hy hv => hfresh y hy (List.mem_append_right _ hv)) hdisj d]
  | custom name args =>
      exact congrArg (TyTemplate.custom name) (substTemplateList_zip_open args hlen hnd hfresh hdisj d)
theorem substTemplateList_zip_open (templates : List TyTemplate) {Ys Xs : List Nat}
    (hlen : Ys.length = Xs.length) (hnd : Ys.Nodup) (hfresh : ∀ y ∈ Ys, y ∉ rigidVarsList templates)
    (hdisj : ∀ y ∈ Ys, y ∉ Xs) (d : Nat) :
    substTemplateList (Ys.zip (Xs.map Ty.fvar)) (openTemplateList d Ys templates) =
      openTemplateList d Xs templates := by
  cases templates with
  | nil => rfl
  | cons t ts =>
      simp only [openTemplateList, substTemplateList,
        t.substTyFvars_zip_openTyVarsFrom hlen hnd
          (fun y hy hv => hfresh y hy (List.mem_append_left _ hv)) hdisj d,
        substTemplateList_zip_open ts hlen hnd
          (fun y hy hv => hfresh y hy (List.mem_append_right _ hv)) hdisj d]
end

theorem BindingAnn.substTyFvars_zip_openTyVarsFrom (ann : BindingAnn) {Ys Xs : List Nat}
    (hlen : Ys.length = Xs.length) (hnd : Ys.Nodup) (hfresh : ∀ y ∈ Ys, y ∉ ann.rigidVars)
    (hdisj : ∀ y ∈ Ys, y ∉ Xs) (d : Nat) :
    (ann.openTyVarsFrom d Ys).substTyFvars (Ys.zip (Xs.map Ty.fvar)) = ann.openTyVarsFrom d Xs := by
  cases ann with
  | absent => rfl
  | complete scheme =>
      simp only [BindingAnn.openTyVarsFrom, BindingAnn.substTyFvars,
        Ty.substFvars_zip_openVarsFrom hlen hnd hfresh hdisj]
  | template t => exact congrArg BindingAnn.template (t.substTyFvars_zip_openTyVarsFrom hlen hnd hfresh hdisj d)
  | partialForall n t =>
      exact congrArg (BindingAnn.partialForall n)
        (t.substTyFvars_zip_openTyVarsFrom hlen hnd hfresh hdisj (d + n))

mutual
/-- Replace an opening's fresh names throughout partial input syntax. As in
Core, the names must be absent from authored leaves and from the replacement
block, because type substitution is sequential. -/
theorem InferInput.substTyFvars_zip_openTyVarsFrom (input : InferInput) {Ys Xs : List Nat}
    (hlen : Ys.length = Xs.length) (hnd : Ys.Nodup) (hfresh : ∀ y ∈ Ys, y ∉ input.rigidVars)
    (hdisj : ∀ y ∈ Ys, y ∉ Xs) (d : Nat) :
    (input.openTyVarsFrom d Ys).substTyFvars (Ys.zip (Xs.map Ty.fvar)) = input.openTyVarsFrom d Xs := by
  cases input with
  | primLit | primBinOp | var | ctor => rfl
  | lambda ann body =>
      simp only [InferInput.openTyVarsFrom, InferInput.substTyFvars,
        body.substTyFvars_zip_openTyVarsFrom hlen hnd
          (fun y hy hv => hfresh y hy (List.mem_append_right _ hv)) hdisj d]
      congr 1
      cases ann with
      | none => rfl
      | some template => exact congrArg some (template.substTyFvars_zip_openTyVarsFrom hlen hnd
          (fun y hy hv => hfresh y hy (List.mem_append_left _ hv)) hdisj d)
  | app f a =>
      simp only [InferInput.openTyVarsFrom, InferInput.substTyFvars,
        f.substTyFvars_zip_openTyVarsFrom hlen hnd
          (fun y hy hv => hfresh y hy (List.mem_append_left _ hv)) hdisj d,
        a.substTyFvars_zip_openTyVarsFrom hlen hnd
          (fun y hy hv => hfresh y hy (List.mem_append_right _ hv)) hdisj d]
  | letIn ann rhs body =>
      simp only [InferInput.openTyVarsFrom, InferInput.substTyFvars,
        ann.substTyFvars_zip_openTyVarsFrom hlen hnd
          (fun y hy hv => hfresh y hy (List.mem_append_left _ (List.mem_append_left _ hv))) hdisj d,
        rhs.substTyFvars_zip_openTyVarsFrom hlen hnd
          (fun y hy hv => hfresh y hy (List.mem_append_left _ (List.mem_append_right _ hv))) hdisj (d + ann.paramCount),
        body.substTyFvars_zip_openTyVarsFrom hlen hnd
          (fun y hy hv => hfresh y hy (List.mem_append_right _ hv)) hdisj d]
  | match_ scrut branches =>
      simp only [InferInput.openTyVarsFrom, InferInput.substTyFvars,
        scrut.substTyFvars_zip_openTyVarsFrom hlen hnd
          (fun y hy hv => hfresh y hy (List.mem_append_left _ hv)) hdisj d,
        substInputBranches_zip_open branches hlen hnd
          (fun y hy hv => hfresh y hy (List.mem_append_right _ hv)) hdisj d]
  | letRec anns bindings body =>
      simp only [InferInput.openTyVarsFrom, InferInput.substTyFvars,
        body.substTyFvars_zip_openTyVarsFrom hlen hnd
          (fun y hy hv => hfresh y hy (List.mem_append_right _ hv)) hdisj d,
        substInputBindings_zip_open bindings anns hlen hnd
          (fun y hy hv => hfresh y hy (List.mem_append_left _ (List.mem_append_right _ hv))) hdisj d,
        List.map_map]
      congr 1
      apply List.map_congr_left
      intro ann hann
      exact ann.substTyFvars_zip_openTyVarsFrom hlen hnd
        (fun y hy hv => hfresh y hy (List.mem_append_left _ (List.mem_append_left _
          (List.mem_flatMap.mpr ⟨ann, hann, hv⟩)))) hdisj d
termination_by sizeOf input

theorem substInputBranches_zip_open (branches : List (MatchPattern × InferInput)) {Ys Xs : List Nat}
    (hlen : Ys.length = Xs.length) (hnd : Ys.Nodup) (hfresh : ∀ y ∈ Ys, y ∉ rigidBranchVars branches)
    (hdisj : ∀ y ∈ Ys, y ∉ Xs) (d : Nat) :
    substInputBranches (Ys.zip (Xs.map Ty.fvar)) (openInputBranches d Ys branches) =
      openInputBranches d Xs branches := by
  cases branches with
  | nil => rfl
  | cons pair rest =>
      simp only [openInputBranches, substInputBranches,
        pair.2.substTyFvars_zip_openTyVarsFrom hlen hnd
          (fun y hy hv => hfresh y hy (List.mem_append_left _ hv)) hdisj d,
        substInputBranches_zip_open rest hlen hnd
          (fun y hy hv => hfresh y hy (List.mem_append_right _ hv)) hdisj d]
termination_by sizeOf branches
decreasing_by all_goals (subst_vars; cases pair; simp_wf <;> omega)

theorem substInputBindings_zip_open (bindings : List InferInput) (anns : List BindingAnn) {Ys Xs : List Nat}
    (hlen : Ys.length = Xs.length) (hnd : Ys.Nodup) (hfresh : ∀ y ∈ Ys, y ∉ rigidBindingVars bindings)
    (hdisj : ∀ y ∈ Ys, y ∉ Xs) (d : Nat) :
    substInputBindings (Ys.zip (Xs.map Ty.fvar)) (openInputBindings d Ys anns bindings) =
      openInputBindings d Xs anns bindings := by
  cases bindings with
  | nil => rfl
  | cons body rest =>
      cases anns with
      | nil => simp only [openInputBindings, substInputBindings,
          body.substTyFvars_zip_openTyVarsFrom hlen hnd
            (fun y hy hv => hfresh y hy (List.mem_append_left _ hv)) hdisj d,
          substInputBindings_zip_open rest [] hlen hnd
            (fun y hy hv => hfresh y hy (List.mem_append_right _ hv)) hdisj d]
      | cons ann anns => simp only [openInputBindings, substInputBindings,
          body.substTyFvars_zip_openTyVarsFrom hlen hnd
            (fun y hy hv => hfresh y hy (List.mem_append_left _ hv)) hdisj (d + ann.paramCount),
          substInputBindings_zip_open rest anns hlen hnd
            (fun y hy hv => hfresh y hy (List.mem_append_right _ hv)) hdisj d]
termination_by sizeOf bindings
end

/-- Top-level fresh-block replacement, with the same assumptions as the Core
opening/renaming law and authored `rigidVars` in place of annotation free vars. -/
theorem InferInput.substTyFvars_zip_openTyVars (input : InferInput) {Ys Xs : List Nat}
    (hlen : Ys.length = Xs.length) (hnd : Ys.Nodup) (hfresh : ∀ y ∈ Ys, y ∉ input.rigidVars)
    (hdisj : ∀ y ∈ Ys, y ∉ Xs) :
    (input.openTyVars Ys).substTyFvars (Ys.zip (Xs.map Ty.fvar)) = input.openTyVars Xs :=
  input.substTyFvars_zip_openTyVarsFrom hlen hnd hfresh hdisj 0

/-- Sequential free substitution commutes with offset opening when its ranges
are locally closed and its domain avoids the opening names. -/
theorem _root_.Ty.substFvars_openVarsFrom {subst : List (Nat × Ty)} {Xs : List Nat}
    (hlc : ∀ pair ∈ subst, pair.2.IsLC) (hfresh : ∀ pair ∈ subst, pair.1 ∉ Xs)
    (ty : Ty) (d : Nat) :
    (ty.openVarsFrom d Xs).substFvars subst = (ty.substFvars subst).openVarsFrom d Xs := by
  induction subst generalizing ty with
  | nil => rfl
  | cons pair rest ih =>
      rcases pair with ⟨name, replacement⟩
      simp only [Ty.substFvars]
      rw [Ty.substFvar_openVarsFrom (hlc _ List.mem_cons_self) (hfresh _ List.mem_cons_self)]
      exact ih (fun p hp => hlc p (List.mem_cons_of_mem _ hp))
        (fun p hp => hfresh p (List.mem_cons_of_mem _ hp)) _

mutual
theorem TyTemplate.substTyFvars_openTyVarsFrom (template : TyTemplate) {subst : List (Nat × Ty)} {Xs : List Nat}
    (hlc : ∀ pair ∈ subst, pair.2.IsLC) (hfresh : ∀ pair ∈ subst, pair.1 ∉ Xs) (d : Nat) :
    (template.openTyVarsFrom d Xs).substTyFvars subst = (template.substTyFvars subst).openTyVarsFrom d Xs := by
  cases template with
  | fixed ty => exact congrArg TyTemplate.fixed (Ty.substFvars_openVarsFrom hlc hfresh ty d)
  | hole => rfl
  | arrow a b => simp only [TyTemplate.openTyVarsFrom, TyTemplate.substTyFvars,
      a.substTyFvars_openTyVarsFrom hlc hfresh d, b.substTyFvars_openTyVarsFrom hlc hfresh d]
  | custom name args =>
      exact congrArg (TyTemplate.custom name) (substTemplateList_openTemplateList args hlc hfresh d)
theorem substTemplateList_openTemplateList (templates : List TyTemplate) {subst : List (Nat × Ty)} {Xs : List Nat}
    (hlc : ∀ pair ∈ subst, pair.2.IsLC) (hfresh : ∀ pair ∈ subst, pair.1 ∉ Xs) (d : Nat) :
    substTemplateList subst (openTemplateList d Xs templates) = openTemplateList d Xs (substTemplateList subst templates) := by
  cases templates with
  | nil => rfl
  | cons t ts => simp only [openTemplateList, substTemplateList,
      t.substTyFvars_openTyVarsFrom hlc hfresh d, substTemplateList_openTemplateList ts hlc hfresh d]
end

theorem BindingAnn.substTyFvars_openTyVarsFrom (ann : BindingAnn) {subst : List (Nat × Ty)} {Xs : List Nat}
    (hlc : ∀ pair ∈ subst, pair.2.IsLC) (hfresh : ∀ pair ∈ subst, pair.1 ∉ Xs) (d : Nat) :
    (ann.openTyVarsFrom d Xs).substTyFvars subst = (ann.substTyFvars subst).openTyVarsFrom d Xs := by
  cases ann with
  | absent => rfl
  | complete scheme => simp only [BindingAnn.openTyVarsFrom, BindingAnn.substTyFvars,
      Ty.substFvars_openVarsFrom hlc hfresh]
  | template t => exact congrArg BindingAnn.template (t.substTyFvars_openTyVarsFrom hlc hfresh d)
  | partialForall n t =>
      exact congrArg (BindingAnn.partialForall n) (t.substTyFvars_openTyVarsFrom hlc hfresh (d + n))

mutual
/-- Source substitution commutes with opening through nested written signature
binders. LC ranges need not avoid the opened names. -/
theorem InferInput.substTyFvars_openTyVarsFrom (input : InferInput) {subst : List (Nat × Ty)} {Xs : List Nat}
    (hlc : ∀ pair ∈ subst, pair.2.IsLC) (hfresh : ∀ pair ∈ subst, pair.1 ∉ Xs) (d : Nat) :
    (input.openTyVarsFrom d Xs).substTyFvars subst = (input.substTyFvars subst).openTyVarsFrom d Xs := by
  cases input with
  | primLit | primBinOp | var | ctor => rfl
  | lambda ann body =>
      simp only [InferInput.openTyVarsFrom, InferInput.substTyFvars,
        body.substTyFvars_openTyVarsFrom hlc hfresh d]
      congr 1
      cases ann with
      | none => rfl
      | some template => exact congrArg some (template.substTyFvars_openTyVarsFrom hlc hfresh d)
  | app f a => simp only [InferInput.openTyVarsFrom, InferInput.substTyFvars,
      f.substTyFvars_openTyVarsFrom hlc hfresh d, a.substTyFvars_openTyVarsFrom hlc hfresh d]
  | letIn ann rhs body => simp only [InferInput.openTyVarsFrom, InferInput.substTyFvars,
      BindingAnn.paramCount_substTyFvars, ann.substTyFvars_openTyVarsFrom hlc hfresh d,
      rhs.substTyFvars_openTyVarsFrom hlc hfresh (d + ann.paramCount),
      body.substTyFvars_openTyVarsFrom hlc hfresh d]
  | match_ scrut branches => simp only [InferInput.openTyVarsFrom, InferInput.substTyFvars,
      scrut.substTyFvars_openTyVarsFrom hlc hfresh d,
      substInputBranches_openInputBranches branches hlc hfresh d]
  | letRec anns bindings body =>
      simp only [InferInput.openTyVarsFrom, InferInput.substTyFvars,
        body.substTyFvars_openTyVarsFrom hlc hfresh d,
        substInputBindings_openInputBindings bindings anns hlc hfresh d, List.map_map]
      congr 1
      apply List.map_congr_left
      intro ann _
      exact ann.substTyFvars_openTyVarsFrom hlc hfresh d
termination_by sizeOf input

theorem substInputBranches_openInputBranches (branches : List (MatchPattern × InferInput)) {subst : List (Nat × Ty)} {Xs : List Nat}
    (hlc : ∀ pair ∈ subst, pair.2.IsLC) (hfresh : ∀ pair ∈ subst, pair.1 ∉ Xs) (d : Nat) :
    substInputBranches subst (openInputBranches d Xs branches) = openInputBranches d Xs (substInputBranches subst branches) := by
  cases branches with
  | nil => rfl
  | cons pair rest =>
      rcases pair with ⟨pat, body⟩
      simp only [openInputBranches, substInputBranches, body.substTyFvars_openTyVarsFrom hlc hfresh d,
        substInputBranches_openInputBranches rest hlc hfresh d]
termination_by sizeOf branches

theorem substInputBindings_openInputBindings (bindings : List InferInput) (anns : List BindingAnn)
    {subst : List (Nat × Ty)} {Xs : List Nat}
    (hlc : ∀ pair ∈ subst, pair.2.IsLC) (hfresh : ∀ pair ∈ subst, pair.1 ∉ Xs) (d : Nat) :
    substInputBindings subst (openInputBindings d Xs anns bindings) =
      openInputBindings d Xs (anns.map (BindingAnn.substTyFvars subst)) (substInputBindings subst bindings) := by
  cases bindings with
  | nil => rfl
  | cons body rest =>
      cases anns with
      | nil => simp only [openInputBindings, substInputBindings, List.map_nil,
          body.substTyFvars_openTyVarsFrom hlc hfresh d,
          substInputBindings_openInputBindings rest [] hlc hfresh d]
      | cons ann anns => simp only [openInputBindings, substInputBindings, List.map_cons,
          BindingAnn.paramCount_substTyFvars, body.substTyFvars_openTyVarsFrom hlc hfresh (d + ann.paramCount),
          substInputBindings_openInputBindings rest anns hlc hfresh d]
termination_by sizeOf bindings
end

theorem InferInput.substTyFvars_openTyVars (input : InferInput) {subst : List (Nat × Ty)} {Xs : List Nat}
    (hlc : ∀ pair ∈ subst, pair.2.IsLC) (hfresh : ∀ pair ∈ subst, pair.1 ∉ Xs) :
    (input.openTyVars Xs).substTyFvars subst = (input.substTyFvars subst).openTyVars Xs :=
  input.substTyFvars_openTyVarsFrom hlc hfresh 0

private theorem ty_substFvars_eq_self_of_fixes {subst : List (Nat × Ty)} {ty : Ty}
    (h : ∀ v ∈ ty.freeVars, (Ty.fvar v).substFvars subst = .fvar v) : ty.substFvars subst = ty := by
  induction ty using Ty.rec_strong with
  | prim p => exact Ty.substFvars_prim
  | bvar i => exact Ty.substFvars_bvar
  | fvar n => exact h n (by simp only [Ty.freeVars, List.mem_singleton])
  | arrow a b iha ihb =>
      rw [Ty.substFvars_arrow,
        iha (fun v hv => h v (by simp only [Ty.freeVars, List.mem_dedup, List.mem_append]; exact .inl hv)),
        ihb (fun v hv => h v (by simp only [Ty.freeVars, List.mem_dedup, List.mem_append]; exact .inr hv))]
  | customTy name args ih =>
      rw [Ty.substFvars_customTy]
      congr 1
      conv_rhs => rw [← List.map_id args]
      apply List.map_congr_left
      intro ty hty
      exact ih ty hty (fun v hv => h v (TyList.mem_freeVars_of_mem hty hv))

mutual
theorem TyTemplate.substTyFvars_eq_self_of_fixes (template : TyTemplate) {subst : List (Nat × Ty)}
    (h : ∀ v ∈ template.rigidVars, (Ty.fvar v).substFvars subst = .fvar v) :
    template.substTyFvars subst = template := by
  cases template with
  | fixed ty => exact congrArg TyTemplate.fixed (ty_substFvars_eq_self_of_fixes h)
  | hole => rfl
  | arrow a b => simp only [TyTemplate.substTyFvars,
      a.substTyFvars_eq_self_of_fixes (fun v hv => h v (List.mem_append_left _ hv)),
      b.substTyFvars_eq_self_of_fixes (fun v hv => h v (List.mem_append_right _ hv))]
  | custom name args =>
      exact congrArg (TyTemplate.custom name) (substTemplateList_eq_self_of_fixes args h)
theorem substTemplateList_eq_self_of_fixes (templates : List TyTemplate) {subst : List (Nat × Ty)}
    (h : ∀ v ∈ rigidVarsList templates, (Ty.fvar v).substFvars subst = .fvar v) :
    substTemplateList subst templates = templates := by
  cases templates with
  | nil => rfl
  | cons t ts => simp only [substTemplateList,
      t.substTyFvars_eq_self_of_fixes (fun v hv => h v (List.mem_append_left _ hv)),
      substTemplateList_eq_self_of_fixes ts (fun v hv => h v (List.mem_append_right _ hv))]
end

theorem BindingAnn.substTyFvars_eq_self_of_fixes (ann : BindingAnn) {subst : List (Nat × Ty)}
    (h : ∀ v ∈ ann.rigidVars, (Ty.fvar v).substFvars subst = .fvar v) : ann.substTyFvars subst = ann := by
  cases ann with
  | absent => rfl
  | complete scheme => simp only [BindingAnn.substTyFvars, ty_substFvars_eq_self_of_fixes h]
  | template t => exact congrArg BindingAnn.template (t.substTyFvars_eq_self_of_fixes h)
  | partialForall n t => exact congrArg (BindingAnn.partialForall n) (t.substTyFvars_eq_self_of_fixes h)

mutual
/-- Fixing every authored free type variable leaves the complete input syntax
unchanged, including anonymous holes and written signature modes. -/
theorem InferInput.substTyFvars_eq_self_of_fixes (input : InferInput) {subst : List (Nat × Ty)}
    (h : ∀ v ∈ input.rigidVars, (Ty.fvar v).substFvars subst = .fvar v) : input.substTyFvars subst = input := by
  cases input with
  | primLit | primBinOp | var | ctor => rfl
  | lambda ann body =>
      simp only [InferInput.substTyFvars,
        body.substTyFvars_eq_self_of_fixes (fun v hv => h v (List.mem_append_right _ hv))]
      congr 1
      cases ann with
      | none => rfl
      | some template =>
          exact congrArg some (template.substTyFvars_eq_self_of_fixes (fun v hv => h v (List.mem_append_left _ hv)))
  | app f a => simp only [InferInput.substTyFvars,
      f.substTyFvars_eq_self_of_fixes (fun v hv => h v (List.mem_append_left _ hv)),
      a.substTyFvars_eq_self_of_fixes (fun v hv => h v (List.mem_append_right _ hv))]
  | letIn ann rhs body => simp only [InferInput.substTyFvars,
      ann.substTyFvars_eq_self_of_fixes (fun v hv => h v (List.mem_append_left _ (List.mem_append_left _ hv))),
      rhs.substTyFvars_eq_self_of_fixes (fun v hv => h v (List.mem_append_left _ (List.mem_append_right _ hv))),
      body.substTyFvars_eq_self_of_fixes (fun v hv => h v (List.mem_append_right _ hv))]
  | match_ scrut branches => simp only [InferInput.substTyFvars,
      scrut.substTyFvars_eq_self_of_fixes (fun v hv => h v (List.mem_append_left _ hv)),
      substInputBranches_eq_self_of_fixes branches (fun v hv => h v (List.mem_append_right _ hv))]
  | letRec anns bindings body =>
      simp only [InferInput.substTyFvars,
        body.substTyFvars_eq_self_of_fixes (fun v hv => h v (List.mem_append_right _ hv)),
        substInputBindings_eq_self_of_fixes bindings (fun v hv => h v (List.mem_append_left _ (List.mem_append_right _ hv)))]
      congr 1
      conv_rhs => rw [← List.map_id anns]
      apply List.map_congr_left
      intro ann hann
      exact ann.substTyFvars_eq_self_of_fixes (fun v hv => h v (List.mem_append_left _
        (List.mem_append_left _ (List.mem_flatMap.mpr ⟨ann, hann, hv⟩))))
termination_by sizeOf input

theorem substInputBranches_eq_self_of_fixes (branches : List (MatchPattern × InferInput)) {subst : List (Nat × Ty)}
    (h : ∀ v ∈ rigidBranchVars branches, (Ty.fvar v).substFvars subst = .fvar v) :
    substInputBranches subst branches = branches := by
  cases branches with
  | nil => rfl
  | cons pair rest =>
      simp only [substInputBranches,
        pair.2.substTyFvars_eq_self_of_fixes (fun v hv => h v (List.mem_append_left _ hv)),
        substInputBranches_eq_self_of_fixes rest (fun v hv => h v (List.mem_append_right _ hv))]
termination_by sizeOf branches
decreasing_by all_goals (subst_vars; cases pair; simp_wf <;> omega)

theorem substInputBindings_eq_self_of_fixes (bindings : List InferInput) {subst : List (Nat × Ty)}
    (h : ∀ v ∈ rigidBindingVars bindings, (Ty.fvar v).substFvars subst = .fvar v) :
    substInputBindings subst bindings = bindings := by
  cases bindings with
  | nil => rfl
  | cons body rest => simp only [substInputBindings,
      body.substTyFvars_eq_self_of_fixes (fun v hv => h v (List.mem_append_left _ hv)),
      substInputBindings_eq_self_of_fixes rest (fun v hv => h v (List.mem_append_right _ hv))]
termination_by sizeOf bindings
end

private theorem ty_substFvars_append (ty : Ty) (first second : List (Nat × Ty)) :
    ty.substFvars (first ++ second) = (ty.substFvars first).substFvars second := by
  induction first generalizing ty with
  | nil => rfl
  | cons pair rest ih => cases pair; exact ih _

mutual
theorem TyTemplate.substTyFvars_append (template : TyTemplate) (first second : List (Nat × Ty)) :
    template.substTyFvars (first ++ second) = (template.substTyFvars first).substTyFvars second := by
  cases template with
  | fixed ty => exact congrArg TyTemplate.fixed (ty_substFvars_append ty first second)
  | hole => rfl
  | arrow a b => simp only [TyTemplate.substTyFvars,
      a.substTyFvars_append first second, b.substTyFvars_append first second]
  | custom name args => exact congrArg (TyTemplate.custom name) (substTemplateList_append args first second)
theorem substTemplateList_append (templates : List TyTemplate) (first second : List (Nat × Ty)) :
    substTemplateList (first ++ second) templates = substTemplateList second (substTemplateList first templates) := by
  cases templates with
  | nil => rfl
  | cons t ts => simp only [substTemplateList, t.substTyFvars_append first second,
      substTemplateList_append ts first second]
end

theorem BindingAnn.substTyFvars_append (ann : BindingAnn) (first second : List (Nat × Ty)) :
    ann.substTyFvars (first ++ second) = (ann.substTyFvars first).substTyFvars second := by
  cases ann with
  | absent => rfl
  | complete scheme => simp only [BindingAnn.substTyFvars, ty_substFvars_append]
  | template t => exact congrArg BindingAnn.template (t.substTyFvars_append first second)
  | partialForall n t => exact congrArg (BindingAnn.partialForall n) (t.substTyFvars_append first second)

mutual
/-- Source type substitutions compose in the same left-to-right order as Core. -/
theorem InferInput.substTyFvars_append (input : InferInput) (first second : List (Nat × Ty)) :
    input.substTyFvars (first ++ second) = (input.substTyFvars first).substTyFvars second := by
  cases input with
  | primLit | primBinOp | var | ctor => rfl
  | lambda ann body =>
      simp only [InferInput.substTyFvars, body.substTyFvars_append first second, Option.map_map]
      congr 1
      cases ann with
      | none => rfl
      | some t => exact congrArg some (t.substTyFvars_append first second)
  | app f a => simp only [InferInput.substTyFvars, f.substTyFvars_append first second, a.substTyFvars_append first second]
  | letIn ann rhs body => simp only [InferInput.substTyFvars, ann.substTyFvars_append first second,
      rhs.substTyFvars_append first second, body.substTyFvars_append first second]
  | match_ scrut branches => simp only [InferInput.substTyFvars, scrut.substTyFvars_append first second,
      substInputBranches_append branches first second]
  | letRec anns bindings body =>
      simp only [InferInput.substTyFvars, body.substTyFvars_append first second,
        substInputBindings_append bindings first second, List.map_map]
      congr 1
      exact List.map_congr_left (fun ann _ => ann.substTyFvars_append first second)
termination_by sizeOf input

theorem substInputBranches_append (branches : List (MatchPattern × InferInput)) (first second : List (Nat × Ty)) :
    substInputBranches (first ++ second) branches = substInputBranches second (substInputBranches first branches) := by
  cases branches with
  | nil => rfl
  | cons pair rest =>
      rcases pair with ⟨pat, body⟩
      simp only [substInputBranches, body.substTyFvars_append first second, substInputBranches_append rest first second]
termination_by sizeOf branches

theorem substInputBindings_append (bindings : List InferInput) (first second : List (Nat × Ty)) :
    substInputBindings (first ++ second) bindings = substInputBindings second (substInputBindings first bindings) := by
  cases bindings with
  | nil => rfl
  | cons body rest => simp only [substInputBindings, body.substTyFvars_append first second,
      substInputBindings_append rest first second]
termination_by sizeOf bindings
end

private theorem input_ty_substFvars_congr {subst other : List (Nat × Ty)} {ty : Ty}
    (h : ∀ v ∈ ty.freeVars, (Ty.fvar v).substFvars subst = (Ty.fvar v).substFvars other) : ty.substFvars subst = ty.substFvars other := by
  induction ty using Ty.rec_strong with
  | prim p => simp only [Ty.substFvars_prim]
  | bvar i => simp only [Ty.substFvars_bvar]
  | fvar n => exact h n (by simp only [Ty.freeVars, List.mem_singleton])
  | arrow a b iha ihb =>
      rw [Ty.substFvars_arrow, Ty.substFvars_arrow,
        iha (fun v hv => h v (by simp only [Ty.freeVars, List.mem_dedup, List.mem_append]; exact .inl hv)),
        ihb (fun v hv => h v (by simp only [Ty.freeVars, List.mem_dedup, List.mem_append]; exact .inr hv))]
  | customTy name args ih =>
      rw [Ty.substFvars_customTy, Ty.substFvars_customTy]
      congr 1
      apply List.map_congr_left
      intro ty hty
      exact ih ty hty (fun v hv => h v (TyList.mem_freeVars_of_mem hty hv))

mutual
theorem TyTemplate.substTyFvars_congr (template : TyTemplate) {subst other : List (Nat × Ty)}
    (h : ∀ v ∈ template.rigidVars, (Ty.fvar v).substFvars subst = (Ty.fvar v).substFvars other) :
    template.substTyFvars subst = template.substTyFvars other := by
  cases template with
  | fixed ty => exact congrArg TyTemplate.fixed (input_ty_substFvars_congr h)
  | hole => rfl
  | arrow a b => simp only [TyTemplate.substTyFvars,
      a.substTyFvars_congr (fun v hv => h v (List.mem_append_left _ hv)),
      b.substTyFvars_congr (fun v hv => h v (List.mem_append_right _ hv))]
  | custom name args =>
      exact congrArg (TyTemplate.custom name) (substTemplateList_congr args h)
theorem substTemplateList_congr (templates : List TyTemplate) {subst other : List (Nat × Ty)}
    (h : ∀ v ∈ rigidVarsList templates, (Ty.fvar v).substFvars subst = (Ty.fvar v).substFvars other) :
    substTemplateList subst templates = substTemplateList other templates := by
  cases templates with
  | nil => rfl
  | cons t ts => simp only [substTemplateList,
      t.substTyFvars_congr (fun v hv => h v (List.mem_append_left _ hv)),
      substTemplateList_congr ts (fun v hv => h v (List.mem_append_right _ hv))]
end

theorem BindingAnn.substTyFvars_congr (ann : BindingAnn) {subst other : List (Nat × Ty)}
    (h : ∀ v ∈ ann.rigidVars, (Ty.fvar v).substFvars subst = (Ty.fvar v).substFvars other) : ann.substTyFvars subst = ann.substTyFvars other := by
  cases ann with
  | absent => rfl
  | complete scheme => simp only [BindingAnn.substTyFvars, input_ty_substFvars_congr h]
  | template t => exact congrArg BindingAnn.template (t.substTyFvars_congr h)
  | partialForall n t => exact congrArg (BindingAnn.partialForall n) (t.substTyFvars_congr h)

mutual
/-- Substitutions agreeing on all authored free type variables produce the
same input syntax, including beneath written signature binders. -/
theorem InferInput.substTyFvars_congr (input : InferInput) {subst other : List (Nat × Ty)}
    (h : ∀ v ∈ input.rigidVars, (Ty.fvar v).substFvars subst = (Ty.fvar v).substFvars other) : input.substTyFvars subst = input.substTyFvars other := by
  cases input with
  | primLit | primBinOp | var | ctor => rfl
  | lambda ann body =>
      simp only [InferInput.substTyFvars,
        body.substTyFvars_congr (fun v hv => h v (List.mem_append_right _ hv))]
      congr 1
      cases ann with
      | none => rfl
      | some template =>
          exact congrArg some (template.substTyFvars_congr (fun v hv => h v (List.mem_append_left _ hv)))
  | app f a => simp only [InferInput.substTyFvars,
      f.substTyFvars_congr (fun v hv => h v (List.mem_append_left _ hv)),
      a.substTyFvars_congr (fun v hv => h v (List.mem_append_right _ hv))]
  | letIn ann rhs body => simp only [InferInput.substTyFvars,
      ann.substTyFvars_congr (fun v hv => h v (List.mem_append_left _ (List.mem_append_left _ hv))),
      rhs.substTyFvars_congr (fun v hv => h v (List.mem_append_left _ (List.mem_append_right _ hv))),
      body.substTyFvars_congr (fun v hv => h v (List.mem_append_right _ hv))]
  | match_ scrut branches => simp only [InferInput.substTyFvars,
      scrut.substTyFvars_congr (fun v hv => h v (List.mem_append_left _ hv)),
      substInputBranches_congr branches (fun v hv => h v (List.mem_append_right _ hv))]
  | letRec anns bindings body =>
      simp only [InferInput.substTyFvars,
        body.substTyFvars_congr (fun v hv => h v (List.mem_append_right _ hv)),
        substInputBindings_congr bindings (fun v hv => h v (List.mem_append_left _ (List.mem_append_right _ hv)))]
      congr 1
      apply List.map_congr_left
      intro ann hann
      exact ann.substTyFvars_congr (fun v hv => h v (List.mem_append_left _
        (List.mem_append_left _ (List.mem_flatMap.mpr ⟨ann, hann, hv⟩))))
termination_by sizeOf input

theorem substInputBranches_congr (branches : List (MatchPattern × InferInput)) {subst other : List (Nat × Ty)}
    (h : ∀ v ∈ rigidBranchVars branches, (Ty.fvar v).substFvars subst = (Ty.fvar v).substFvars other) :
    substInputBranches subst branches = substInputBranches other branches := by
  cases branches with
  | nil => rfl
  | cons pair rest =>
      simp only [substInputBranches,
        pair.2.substTyFvars_congr (fun v hv => h v (List.mem_append_left _ hv)),
        substInputBranches_congr rest (fun v hv => h v (List.mem_append_right _ hv))]
termination_by sizeOf branches
decreasing_by all_goals (subst_vars; cases pair; simp_wf <;> omega)

theorem substInputBindings_congr (bindings : List InferInput) {subst other : List (Nat × Ty)}
    (h : ∀ v ∈ rigidBindingVars bindings, (Ty.fvar v).substFvars subst = (Ty.fvar v).substFvars other) :
    substInputBindings subst bindings = substInputBindings other bindings := by
  cases bindings with
  | nil => rfl
  | cons body rest => simp only [substInputBindings,
      body.substTyFvars_congr (fun v hv => h v (List.mem_append_left _ hv)),
      substInputBindings_congr rest (fun v hv => h v (List.mem_append_right _ hv))]
termination_by sizeOf bindings
end




mutual
theorem TyTemplate.openTyVarsFrom_scope (template : TyTemplate) {K : List Nat}
    (hscope : ∀ v ∈ template.rigidVars, v ∈ K) (depth : Nat) (Xs : List Nat) :
    ∀ v ∈ (template.openTyVarsFrom depth Xs).rigidVars, v ∈ K ++ Xs := by
  cases template with
  | fixed ty =>
    intro v hv
    exact (Ty.freeVars_openVarsFrom_subset v hv).elim
      (fun hv => List.mem_append_left _ (hscope v hv)) (List.mem_append_right _)
  | hole => intro v hv; cases hv
  | arrow a b =>
    intro v hv
    exact (List.mem_append.mp hv).elim
      (a.openTyVarsFrom_scope (fun v hv => hscope v (List.mem_append_left _ hv)) depth Xs v)
      (b.openTyVarsFrom_scope (fun v hv => hscope v (List.mem_append_right _ hv)) depth Xs v)
  | custom name args => exact openTemplateList_scope args hscope depth Xs
private theorem openTemplateList_scope (templates : List TyTemplate) {K : List Nat}
    (hscope : ∀ v ∈ rigidVarsList templates, v ∈ K) (depth : Nat) (Xs : List Nat) :
    ∀ v ∈ rigidVarsList (openTemplateList depth Xs templates), v ∈ K ++ Xs := by
  cases templates with
  | nil => intro v hv; cases hv
  | cons t ts =>
    intro v hv
    exact (List.mem_append.mp hv).elim
      (t.openTyVarsFrom_scope (fun v hv => hscope v (List.mem_append_left _ hv)) depth Xs v)
      (openTemplateList_scope ts (fun v hv => hscope v (List.mem_append_right _ hv)) depth Xs v)
end

theorem BindingAnn.openTyVarsFrom_scope (ann : BindingAnn) {K : List Nat}
    (hscope : ∀ v ∈ ann.rigidVars, v ∈ K) (depth : Nat) (Xs : List Nat) :
    ∀ v ∈ (ann.openTyVarsFrom depth Xs).rigidVars, v ∈ K ++ Xs := by
  cases ann with
  | absent => intro v hv; cases hv
  | complete scheme =>
    intro v hv
    exact (Ty.freeVars_openVarsFrom_subset v hv).elim
      (fun hv => List.mem_append_left _ (hscope v hv)) (List.mem_append_right _)
  | template t => exact t.openTyVarsFrom_scope hscope depth Xs
  | partialForall n t => exact t.openTyVarsFrom_scope hscope (depth + n) Xs

/- Opening adds only the opening names to the authored free-variable scope.
The offset and nested signatures' own binders are respected in every mode. -/
mutual
theorem InferInput.openTyVarsFrom_scope (input : InferInput) {K : List Nat}
    (hscope : ∀ v ∈ input.rigidVars, v ∈ K) (depth : Nat) (Xs : List Nat) :
    ∀ v ∈ (input.openTyVarsFrom depth Xs).rigidVars, v ∈ K ++ Xs := by
  cases input with
  | primLit | primBinOp | var | ctor => intro v hv; cases hv
  | lambda ann body =>
    intro v hv
    rcases List.mem_append.mp hv with hv | hv
    · cases ann with
      | none => cases hv
      | some t =>
        exact t.openTyVarsFrom_scope
          (fun v hv => hscope v (List.mem_append_left _ hv)) depth Xs v hv
    · exact body.openTyVarsFrom_scope
        (fun v hv => hscope v (List.mem_append_right _ hv)) depth Xs v hv
  | app f x =>
    intro v hv
    exact (List.mem_append.mp hv).elim
      (f.openTyVarsFrom_scope (fun v hv => hscope v (List.mem_append_left _ hv)) depth Xs v)
      (x.openTyVarsFrom_scope (fun v hv => hscope v (List.mem_append_right _ hv)) depth Xs v)
  | letIn ann rhs body =>
    intro v hv
    rcases List.mem_append.mp hv with hv | hv
    · rcases List.mem_append.mp hv with hv | hv
      · exact ann.openTyVarsFrom_scope
          (fun v hv => hscope v (List.mem_append_left _ (List.mem_append_left _ hv))) depth Xs v hv
      · exact rhs.openTyVarsFrom_scope
          (fun v hv => hscope v (List.mem_append_left _ (List.mem_append_right _ hv)))
          (depth + ann.paramCount) Xs v hv
    · exact body.openTyVarsFrom_scope
        (fun v hv => hscope v (List.mem_append_right _ hv)) depth Xs v hv
  | match_ scrut branches =>
    intro v hv
    exact (List.mem_append.mp hv).elim
      (scrut.openTyVarsFrom_scope (fun v hv => hscope v (List.mem_append_left _ hv)) depth Xs v)
      (openInputBranches_scope branches (fun v hv => hscope v (List.mem_append_right _ hv)) depth Xs v)
  | letRec anns bindings body =>
    intro v hv
    rcases List.mem_append.mp hv with hv | hv
    · rcases List.mem_append.mp hv with hv | hv
      · obtain ⟨opened, ho, hv⟩ := List.mem_flatMap.mp hv
        obtain ⟨original, horiginal, rfl⟩ := List.mem_map.mp ho
        exact original.openTyVarsFrom_scope (fun v hv => hscope v
          (List.mem_append_left _ (List.mem_append_left _
            (List.mem_flatMap.mpr ⟨original, horiginal, hv⟩)))) depth Xs v hv
      · exact openInputBindings_scope bindings anns
          (fun v hv => hscope v (List.mem_append_left _ (List.mem_append_right _ hv))) depth Xs v hv
    · exact body.openTyVarsFrom_scope
        (fun v hv => hscope v (List.mem_append_right _ hv)) depth Xs v hv
termination_by sizeOf input

theorem openInputBranches_scope (branches : List (MatchPattern × InferInput)) {K : List Nat}
    (hscope : ∀ v ∈ rigidBranchVars branches, v ∈ K) (depth : Nat) (Xs : List Nat) :
    ∀ v ∈ rigidBranchVars (openInputBranches depth Xs branches), v ∈ K ++ Xs := by
  cases branches with
  | nil => intro v hv; cases hv
  | cons branch branches =>
    have hhead := branch.2.openTyVarsFrom_scope
      (fun v hv => hscope v (List.mem_append_left _ hv)) depth Xs
    have htail := openInputBranches_scope branches
      (fun v hv => hscope v (List.mem_append_right _ hv)) depth Xs
    rcases branch with ⟨pat, body⟩
    intro v hv
    exact (List.mem_append.mp hv).elim (hhead v) (htail v)
termination_by sizeOf branches
decreasing_by all_goals (subst_vars; cases branch; simp_wf <;> omega)

theorem openInputBindings_scope (bindings : List InferInput) (anns : List BindingAnn) {K : List Nat}
    (hscope : ∀ v ∈ rigidBindingVars bindings, v ∈ K) (depth : Nat) (Xs : List Nat) :
    ∀ v ∈ rigidBindingVars (openInputBindings depth Xs anns bindings), v ∈ K ++ Xs := by
  cases bindings with
  | nil => intro v hv; cases hv
  | cons body rest =>
    cases anns with
    | nil =>
      intro v hv
      exact (List.mem_append.mp hv).elim
        (body.openTyVarsFrom_scope (fun v hv => hscope v (List.mem_append_left _ hv)) depth Xs v)
        (openInputBindings_scope rest [] (fun v hv => hscope v (List.mem_append_right _ hv)) depth Xs v)
    | cons ann anns =>
      intro v hv
      exact (List.mem_append.mp hv).elim
        (body.openTyVarsFrom_scope (fun v hv => hscope v (List.mem_append_left _ hv)) (depth + ann.paramCount) Xs v)
        (openInputBindings_scope rest anns (fun v hv => hscope v (List.mem_append_right _ hv)) depth Xs v)
termination_by sizeOf bindings
end

theorem InferInput.openTyVars_scope (input : InferInput) {K : List Nat}
    (hscope : ∀ v ∈ input.rigidVars, v ∈ K) (Xs : List Nat) :
    ∀ v ∈ (input.openTyVars Xs).rigidVars, v ∈ K ++ Xs :=
  input.openTyVarsFrom_scope hscope 0 Xs

theorem InferInput.rigidVars_openTyVarsFrom {input : InferInput} {d : Nat} {Xs : List Nat} {v : Nat}
    (hv : v ∈ (input.openTyVarsFrom d Xs).rigidVars) : v ∈ input.rigidVars ∨ v ∈ Xs :=
  List.mem_append.mp (input.openTyVarsFrom_scope (K := input.rigidVars) (fun _ h => h) d Xs v hv)

theorem rigidBranchVars_openInputBranches {branches : List (MatchPattern × InferInput)}
    {d : Nat} {Xs : List Nat} {v : Nat}
    (hv : v ∈ rigidBranchVars (openInputBranches d Xs branches)) :
    v ∈ rigidBranchVars branches ∨ v ∈ Xs :=
  List.mem_append.mp (openInputBranches_scope branches (K := rigidBranchVars branches) (fun _ h => h) d Xs v hv)

theorem rigidBindingVars_openInputBindings {bindings : List InferInput} {anns : List BindingAnn}
    {d : Nat} {Xs : List Nat} {v : Nat}
    (hv : v ∈ rigidBindingVars (openInputBindings d Xs anns bindings)) :
    v ∈ rigidBindingVars bindings ∨ v ∈ Xs :=
  List.mem_append.mp (openInputBindings_scope bindings anns (K := rigidBindingVars bindings) (fun _ h => h) d Xs v hv)

end

/-! ## RecScheme -/

section

/-! Ordered completion schemes for recursive members. Written slots retain
all authored positions; remaining occurring pool variables follow them. -/

/-- Preserve the written prefix, including vacuous slots, then quantify the
remaining pool variables that occur in this member's monotype. -/
def recNames (written pool : List Nat) (ty : Ty) : List Nat :=
  written ++ pool.filter (fun v => decide (v ∈ ty.freeVars) && decide (v ∉ written))

def recScheme (written pool : List Nat) (ty : Ty) : PolyTy :=
  ⟨(recNames written pool ty).length, Ty.closeOver (recNames written pool ty) ty⟩

/-- Complete signatures retain their exact scheme; monotypes use the member's
own ordered written prefix and the shared pool. -/
def _root_.RecSpec.completedScheme (written pool : List Nat) : RecSpec → PolyTy
  | .mono ty => recScheme written pool ty
  | .poly scheme => scheme

@[simp] theorem recNames_take_prefix (written pool : List Nat) (ty : Ty) :
    (recNames written pool ty).take written.length = written := by
  simp [recNames]

theorem recNames_prefix (written pool : List Nat) (ty : Ty) :
    List.IsPrefix written (recNames written pool ty) :=
  ⟨_, rfl⟩

theorem recNames_prefix_length_le (written pool : List Nat) (ty : Ty) :
    written.length ≤ (recNames written pool ty).length := by
  simp only [recNames, List.length_append]
  omega

@[simp] theorem mem_recNames {written pool : List Nat} {ty : Ty} {v : Nat} :
    v ∈ recNames written pool ty ↔
      v ∈ written ∨ (v ∈ pool ∧ v ∈ ty.freeVars ∧ v ∉ written) := by
  simp [recNames, List.mem_filter]

theorem recNames_nodup {written pool : List Nat} {ty : Ty}
    (hprefix : written.Nodup) (hpool : pool.Nodup) :
    (recNames written pool ty).Nodup := by
  refine List.nodup_append.mpr ⟨hprefix, hpool.filter _, ?_⟩
  intro v hv w hw heq
  have hparts : w ∈ ty.freeVars ∧ w ∉ written := by
    simpa only [Bool.and_eq_true, decide_eq_true_eq] using (List.mem_filter.mp hw).2
  exact hparts.2 (heq ▸ hv)

/-- Every pool variable occurring in this member is quantified. -/
theorem mem_recNames_of_mem_pool {written pool : List Nat} {ty : Ty} {v : Nat}
    (hpool : v ∈ pool) (hfree : v ∈ ty.freeVars) :
    v ∈ recNames written pool ty := by
  by_cases hp : v ∈ written
  · exact mem_recNames.mpr (Or.inl hp)
  · exact mem_recNames.mpr (Or.inr ⟨hpool, hfree, hp⟩)

theorem not_mem_pool_of_not_mem_recNames {written pool : List Nat} {ty : Ty} {v : Nat}
    (hfree : v ∈ ty.freeVars) (hnames : v ∉ recNames written pool ty) : v ∉ pool :=
  fun hpool => hnames (mem_recNames_of_mem_pool hpool hfree)

theorem recScheme_wf {written pool : List Nat} {ty : Ty} (hlc : ty.IsLC) :
    (recScheme written pool ty).WF :=
  Ty.closeOver_preserves_bvars hlc

/-- Closing names generalizes the original monotype; uniqueness is needed for
other opening arguments, but not for this direction of scheme generality. -/
theorem recScheme_generalizes_mono {written pool : List Nat} {ty : Ty} (hlc : ty.IsLC) :
    (recScheme written pool ty).Generalizes (PolyTy.mkTrivial ty) := by
  intro args target _ hinst
  have htarget : target = ty := InstantiatesBy.eq_of_closed hlc hinst
  subst target
  refine ⟨(recNames written pool ty).map Ty.fvar, ?_, ?_⟩
  · intro t ht
    obtain ⟨_, _, heq⟩ := List.mem_map.mp ht
    rw [← heq]
    exact .fvar
  · have hopen := InstantiatesBy.openVars (Xs := recNames written pool ty)
      (Ty.closeOver_preserves_bvars hlc) (Nat.le_refl _)
    rwa [Ty.openVars_closeOver_self hlc] at hopen

/-- Closing the occurring pool variables leaves only outer variables free. -/
theorem recScheme_freeVars_outer {written pool outer : List Nat} {ty : Ty}
    (hcover : ∀ v ∈ ty.freeVars, v ∈ pool ++ outer) :
    ∀ v ∈ (recScheme written pool ty).body.freeVars, v ∈ outer := by
  intro v hv
  have hty := Ty.freeVars_closeOver_subset hv
  rcases List.mem_append.mp (hcover v hty) with hpool | houter
  · exact False.elim (Ty.not_mem_closeOver_freeVars
      (mem_recNames_of_mem_pool hpool hty) hv)
  · exact houter

@[simp] theorem _root_.RecSpec.completedScheme_mono (written pool : List Nat) (ty : Ty) :
    RecSpec.completedScheme written pool (.mono ty) = recScheme written pool ty := rfl

@[simp] theorem _root_.RecSpec.completedScheme_poly (written pool : List Nat) (scheme : PolyTy) :
    RecSpec.completedScheme written pool (.poly scheme) = scheme := rfl

theorem _root_.RecSpec.completedScheme_wf {written pool : List Nat} {spec : RecSpec}
    (h : spec.LC) : (spec.completedScheme written pool).WF := by
  cases spec with
  | mono ty => exact recScheme_wf h
  | poly scheme => exact h

/-- Generic source transformation also updates free outer variables of complete
contracts. Their quantified binder count and bound variables stay unchanged. -/
def _root_.RecSpec.onSubstSource (S : Subst) : RecSpec → RecSpec
  | .mono ty => .mono (S.onTy ty)
  | .poly scheme => .poly (S.onPolyTy scheme)

/-- Only a complete written contract cuts recursive dependencies. Partial
annotations retain monomorphic recursive use until their component is solved. -/
def BindingAnn.recModeAnn : BindingAnn → Option PolyTy
  | .complete scheme => some scheme
  | _ => none

def BindingAnn.recPrefixCount : BindingAnn → Nat
  | .partialForall count _ => count
  | _ => 0

def recRenameNames (pool fresh names : List Nat) : List Nat :=
  names.map (fun name => (fresh[pool.idxOf name]?).getD name)

def recCompletedSchemes (specs : List RecSpec) (prefixes : List (List Nat))
    (pool : List Nat) : List PolyTy :=
  specs.mapIdx (fun i spec => spec.completedScheme (prefixes[i]?.getD []) pool)

def recBodyCtx (ctx : Ctx) (specs : List RecSpec) (prefixes : List (List Nat))
    (pool : List Nat) : Ctx :=
  { ctx with env := recCompletedSchemes specs prefixes pool ++ ctx.env }

def recStageEntry (prefixes : List (List Nat)) (done pool fresh : List Nat)
    (member : Nat) (spec : RecSpec) : PolyTy :=
  match spec with
  | .poly scheme => scheme
  | .mono ty =>
      if member ∈ done then recScheme (prefixes[member]?.getD []) pool ty
      else PolyTy.mkTrivial (Ty.renameG pool fresh ty)

def recStageCtx (ctx : Ctx) (specs : List RecSpec) (prefixes : List (List Nat))
    (done pool fresh : List Nat) : Ctx :=
  { ctx with env := specs.mapIdx (recStageEntry prefixes done pool fresh) ++ ctx.env }

structure RecPrefixesWF (anns : List BindingAnn) (specs : List RecSpec)
    (prefixes : List (List Nat)) (pool : List Nat) : Prop where
  length : prefixes.length = specs.length
  member : ∀ (i : Nat) (ann : BindingAnn) (names : List Nat), anns[i]? = some ann → prefixes[i]? = some names →
    names.length = ann.recPrefixCount ∧ names.Nodup ∧ ∀ name ∈ names, name ∈ pool




/-- Reordering quantified names and retaining unused names changes no instances
when the same occurring free variables are closed. -/
theorem closeScheme_generalizes_of_same_bound_vars {ty : Ty} {source target : List Nat}
    (hlc : ty.IsLC) (hnd : target.Nodup)
    (hcover : ∀ v ∈ ty.freeVars, v ∈ source ↔ v ∈ target) :
    PolyTy.Generalizes ⟨source.length, Ty.closeOver source ty⟩
      ⟨target.length, Ty.closeOver target ty⟩ := by
  obtain ⟨Xs, hlen, hXs, hav⟩ := exists_fresh_names (target ++ ty.freeVars) target.length
  let R : Subst := target.zip (Xs.map Ty.fvar)
  have hR : ∀ p ∈ R, p.2.IsLC := by
    intro p hp
    obtain ⟨_, _, heq⟩ := List.mem_map.mp (List.of_mem_zip hp).2
    rw [← heq]; exact .fvar
  have htargetXs : ∀ v ∈ target, v ∉ Xs := by
    intro v hv hx
    exact hav v hx (List.mem_append_left _ hv)
  have hXsTy : ∀ x ∈ Xs, x ∉ ty.freeVars := by
    intro x hx ht
    exact hav x hx (List.mem_append_right _ ht)
  have hfixed : R.onPolyTy ⟨source.length, Ty.closeOver source ty⟩ =
      ⟨source.length, Ty.closeOver source ty⟩ := by
    unfold Subst.onPolyTy
    congr 1
    apply Ty.substFvars_eq_self_of_no_key
    intro p hp hv
    have hty := Ty.freeVars_closeOver_subset hv
    exact Ty.not_mem_closeOver_freeVars ((hcover p.1 hty).mpr (List.of_mem_zip hp).1) hv
  have hh := closeOver_generalizes (g := source) (M := ⟨target.length, Ty.closeOver target ty⟩) hlc hR
    (Ty.closeOver_preserves_bvars (vars := target) hlc) hXs hlen
    (fun x hx hv => hXsTy x hx (Ty.freeVars_closeOver_subset hv))
    (Ty.openVars_closeOver_rename hlc hnd hlen htargetXs)
    (by rw [hfixed]; exact fun x hx hv => hXsTy x hx (Ty.freeVars_closeOver_subset hv))
  rwa [hfixed] at hh

theorem recScheme_generalizes_genGroup {written pool : List Nat} {ty : Ty}
    (hlc : ty.IsLC) (hpool : pool.Nodup) (hprefix : ∀ v ∈ written, v ∈ pool) :
    (recScheme written pool ty).Generalizes (PolyTy.genGroup pool ty) := by
  apply closeScheme_generalizes_of_same_bound_vars hlc (hpool.filter _)
  intro v hv
  simp only [mem_recNames, List.mem_filter, decide_eq_true_eq]
  constructor
  · rintro (hw | ⟨hp, _, _⟩)
    · exact ⟨hprefix v hw, hv⟩
    · exact ⟨hp, hv⟩
  · rintro ⟨hp, _⟩
    by_cases hw : v ∈ written
    · exact .inl hw
    · exact .inr ⟨hp, hv, hw⟩

theorem genGroup_generalizes_recScheme {written pool : List Nat} {ty : Ty}
    (hlc : ty.IsLC) (hpool : pool.Nodup) (hnd : written.Nodup)
    (hprefix : ∀ v ∈ written, v ∈ pool) :
    (PolyTy.genGroup pool ty).Generalizes (recScheme written pool ty) := by
  apply closeScheme_generalizes_of_same_bound_vars hlc (recNames_nodup hnd hpool)
  intro v hv
  simp only [mem_recNames, Ty.genFilter, List.mem_filter, decide_eq_true_eq]
  constructor
  · rintro ⟨hp, _⟩
    by_cases hw : v ∈ written
    · exact .inl hw
    · exact .inr ⟨hp, hv, hw⟩
  · rintro (hw | ⟨hp, _, _⟩)
    · exact ⟨hprefix v hw, hv⟩
    · exact ⟨hp, hv⟩




/-- The filtered pool scheme permits every simultaneous pool renaming. -/
theorem genGroup_generalizes_rename_mono {G Xs : List Nat} {ty : Ty} (hlc : ty.IsLC) :
    (PolyTy.genGroup G ty).Generalizes (PolyTy.mkTrivial (Ty.renameG G Xs ty)) := by
  let R : Subst := G.zip (Xs.map Ty.fvar)
  have hR : ∀ p ∈ R, p.2.IsLC := by
    intro p hp
    obtain ⟨_, _, heq⟩ := List.mem_map.mp (List.of_mem_zip hp).2
    rw [← heq]; exact .fvar
  have hbase : (PolyTy.genGroup G ty).Generalizes (PolyTy.mkTrivial ty) := by
    simpa [recScheme, recNames, PolyTy.genGroup, Ty.genFilter] using
      (recScheme_generalizes_mono (written := []) (pool := G) hlc)
  have hfixed : R.onPolyTy (PolyTy.genGroup G ty) = PolyTy.genGroup G ty := by
    unfold Subst.onPolyTy
    congr 1
    apply Ty.substFvars_eq_self_of_no_key
    intro p hp hv
    apply Ty.not_mem_closeOver_freeVars (gs := Ty.genFilter G ty) _ hv
    exact List.mem_filter.mpr ⟨(List.of_mem_zip hp).1, by
      simpa using Ty.freeVars_closeOver_subset hv⟩
  have hh := hbase.onSubst (S := R) hlc hR
  rw [hfixed] at hh
  exact hh

/-- Read the member's prefix invariant in the total indexing convention used
by completed environments. -/
theorem RecPrefixesWF.get {anns : List BindingAnn} {specs : List RecSpec}
    (h : RecPrefixesWF anns specs prefixes G) (hlen : anns.length = specs.length)
    (hi : i < specs.length) :
    (prefixes[i]?.getD []).Nodup ∧ ∀ v ∈ prefixes[i]?.getD [], v ∈ G := by
  cases hp : prefixes[i]? with
  | none => simp
  | some names =>
      have hia : i < anns.length := by omega
      exact (h.member i anns[i] names (List.getElem?_eq_getElem hia) hp).2

/-- Erased Core's filtered pool exports generalize each ordered completion. -/
theorem bodySchemes_generalize_recCompleted {anns : List BindingAnn} {specs : List RecSpec}
    (hwf : RecSpecs.WF (anns.map BindingAnn.recModeAnn) bindings specs G)
    (hp : RecPrefixesWF anns specs prefixes G) :
    List.Forall₂ PolyTy.Generalizes (specs.map (RecSpec.bodyScheme G))
      (recCompletedSchemes specs prefixes G) := by
  apply List.forall₂_of_length_eq_of_get (by simp [recCompletedSchemes])
  intro i hb hc
  have hi : i < specs.length := by simpa using hb
  have hannsLen : anns.length = specs.length := by
    have := congrArg List.length hwf.anns_eq
    simpa using this.symm
  obtain ⟨hnd, hsub⟩ := hp.get hannsLen hi
  simp only [recCompletedSchemes, List.get_eq_getElem, List.getElem_map, List.getElem_mapIdx]
  cases hs : specs[i]'hi with
  | mono ty =>
      exact genGroup_generalizes_recScheme
        (hwf.mono_lc ty (hs ▸ List.getElem_mem hi)) hwf.nodup hnd hsub
  | poly scheme => exact PolyTy.Generalizes.refl _

/-- Ordered completed schemes and Core's filtered pool exports have precisely
identical instances, including unused authored quantifiers. -/
theorem recCompleted_generalize_bodySchemes {anns : List BindingAnn} {specs : List RecSpec}
    (hwf : RecSpecs.WF (anns.map BindingAnn.recModeAnn) bindings specs G)
    (hp : RecPrefixesWF anns specs prefixes G) :
    List.Forall₂ PolyTy.Generalizes (recCompletedSchemes specs prefixes G)
      (specs.map (RecSpec.bodyScheme G)) := by
  apply List.forall₂_of_length_eq_of_get (by simp [recCompletedSchemes])
  intro i hc hb
  have hi : i < specs.length := by simpa [recCompletedSchemes] using hc
  have hannsLen : anns.length = specs.length := by
    have := congrArg List.length hwf.anns_eq
    simpa using this.symm
  obtain ⟨_, hsub⟩ := hp.get hannsLen hi
  simp only [recCompletedSchemes, List.get_eq_getElem, List.getElem_map, List.getElem_mapIdx]
  cases hs : specs[i]'hi with
  | mono ty =>
      exact recScheme_generalizes_genGroup
        (hwf.mono_lc ty (hs ▸ List.getElem_mem hi)) hwf.nodup hsub
  | poly scheme => exact PolyTy.Generalizes.refl _

/-- The final filtered pool environment generalizes the new stage environment;
current/pending members remain monomorphic at the same shared opening. -/
theorem bodySchemes_generalize_recStage {anns : List BindingAnn} {specs : List RecSpec}
    (hwf : RecSpecs.WF (anns.map BindingAnn.recModeAnn) bindings specs G)
    (hp : RecPrefixesWF anns specs prefixes G) :
    List.Forall₂ PolyTy.Generalizes (specs.map (RecSpec.bodyScheme G))
      (specs.mapIdx (recStageEntry prefixes done G Xs)) := by
  apply List.forall₂_of_length_eq_of_get (by simp)
  intro i hb hs
  have hi : i < specs.length := by simpa using hb
  have hannsLen : anns.length = specs.length := by
    have := congrArg List.length hwf.anns_eq
    simpa using this.symm
  obtain ⟨hnd, hsub⟩ := hp.get hannsLen hi
  simp only [List.get_eq_getElem, List.getElem_map, List.getElem_mapIdx]
  cases he : specs[i]'hi with
  | mono ty =>
      simp only [RecSpec.bodyScheme, recStageEntry]
      split
      · exact genGroup_generalizes_recScheme
          (hwf.mono_lc ty (he ▸ List.getElem_mem hi)) hwf.nodup hnd hsub
      · exact genGroup_generalizes_rename_mono (hwf.mono_lc ty (he ▸ List.getElem_mem hi))
  | poly scheme => exact PolyTy.Generalizes.refl _




private def poolMap (G W : List Nat) (v : Nat) : Nat := (W[G.idxOf v]?).getD v

private theorem poolMap_eq {G W : List Nat} (hlen : W.length = G.length) {v : Nat} (hv : v ∈ G) :
    poolMap G W v = W[G.idxOf v]'(by have := List.idxOf_lt_length_iff.mpr hv; omega) := by
  have hi : G.idxOf v < W.length := by have := List.idxOf_lt_length_iff.mpr hv; omega
  unfold poolMap
  rw [List.getElem?_eq_getElem hi]
  rfl

private theorem poolMap_mem {G W : List Nat} (hlen : W.length = G.length) {v : Nat} (hv : v ∈ G) :
    poolMap G W v ∈ W := by
  rw [poolMap_eq hlen hv]
  exact List.getElem_mem _

private theorem poolMap_inj {G W : List Nat} (hlen : W.length = G.length) (hW : W.Nodup)
    {a b : Nat} (ha : a ∈ G) (hb : b ∈ G) (heq : poolMap G W a = poolMap G W b) : a = b := by
  rw [poolMap_eq hlen ha, poolMap_eq hlen hb] at heq
  have hi := (List.Nodup.getElem_inj_iff hW).mp heq
  have hh := congrArg (fun i => G[i]?) hi
  simpa only [List.getElem?_idxOf ha, List.getElem?_idxOf hb, Option.some.injEq] using hh

private theorem poolMap_pool {G W : List Nat} (hlen : W.length = G.length) (hG : G.Nodup) :
    G.map (poolMap G W) = W := by
  apply List.ext_get (by simp [hlen])
  intro i hi hj
  simp only [List.get_eq_getElem, List.getElem_map]
  simp only [poolMap, hG.idxOf_getElem i (by simpa using hi), List.getElem?_eq_getElem hj, Option.getD_some]

private theorem poolMap_sublist_mem {G W names : List Nat}
    (hlen : W.length = G.length) (hW : W.Nodup) (hnames : ∀ v ∈ names, v ∈ G)
    {v : Nat} (hv : v ∈ G) :
    poolMap G W v ∈ names.map (poolMap G W) ↔ v ∈ names := by
  constructor
  · intro hm
    obtain ⟨a, ha, heq⟩ := List.mem_map.mp hm
    exact poolMap_inj hlen hW (hnames a ha) hv heq ▸ ha
  · intro hm
    exact List.mem_map.mpr ⟨v, hm, rfl⟩

private theorem poolMap_occurs {G W : List Nat} {ty : Ty}
    (hlen : W.length = G.length) (hG : G.Nodup) (hW : W.Nodup)
    (hGW : ∀ g ∈ G, g ∉ W) (hWty : ∀ w ∈ W, w ∉ ty.freeVars)
    {v : Nat} (hv : v ∈ G) :
    poolMap G W v ∈ (Ty.renameG G W ty).freeVars ↔ v ∈ ty.freeVars := by
  exact Ty.mem_freeVars_renameG_iff hlen hG hW hGW hWty (List.getElem?_idxOf hv)
    (by rw [poolMap_eq hlen hv]; exact List.getElem?_eq_getElem _)

private theorem poolMap_nodup {G W names : List Nat}
    (hlen : W.length = G.length) (hW : W.Nodup) (hnd : names.Nodup)
    (hnames : ∀ v ∈ names, v ∈ G) : (names.map (poolMap G W)).Nodup := by
  induction names with
  | nil => exact .nil
  | cons head rest ih =>
    obtain ⟨hn, ht⟩ := List.nodup_cons.mp hnd
    apply List.nodup_cons.mpr
    refine ⟨?_, ih ht (fun v hv => hnames v (List.mem_cons_of_mem _ hv))⟩
    intro hm
    obtain ⟨v, hv, heq⟩ := List.mem_map.mp hm
    exact hn (poolMap_inj hlen hW (hnames v (List.mem_cons_of_mem _ hv))
      (hnames head List.mem_cons_self) heq ▸ hv)

theorem recNames_rename_pool {G W names : List Nat} {ty : Ty}
    (hlen : W.length = G.length) (hG : G.Nodup) (hW : W.Nodup)
    (hGW : ∀ g ∈ G, g ∉ W) (hWty : ∀ w ∈ W, w ∉ ty.freeVars)
    (hnames : ∀ v ∈ names, v ∈ G) :
    recNames (recRenameNames G W names) W (Ty.renameG G W ty) =
      recRenameNames G W (recNames names G ty) := by
  change names.map (poolMap G W) ++ W.filter _ = (names ++ G.filter _).map (poolMap G W)
  rw [List.map_append]
  congr 1
  calc
    W.filter (fun v => decide (v ∈ (Ty.renameG G W ty).freeVars) && decide (v ∉ names.map (poolMap G W))) =
        (G.map (poolMap G W)).filter (fun v => decide (v ∈ (Ty.renameG G W ty).freeVars) && decide (v ∉ names.map (poolMap G W))) :=
      congrArg (fun l => l.filter (fun v => decide (v ∈ (Ty.renameG G W ty).freeVars) && decide (v ∉ names.map (poolMap G W)))) (poolMap_pool hlen hG).symm
    _ = (G.filter (fun v => decide (poolMap G W v ∈ (Ty.renameG G W ty).freeVars) && decide (poolMap G W v ∉ names.map (poolMap G W)))).map (poolMap G W) := by
      rw [List.filter_map]; rfl
    _ = (G.filter (fun v => decide (v ∈ ty.freeVars) && decide (v ∉ names))).map (poolMap G W) := by
      congr 1
      apply List.filter_congr
      intro v hv
      simp only [poolMap_occurs hlen hG hW hGW hWty hv, poolMap_sublist_mem hlen hW hnames hv]

@[simp] theorem recRenameNames_length (G W names : List Nat) :
    (recRenameNames G W names).length = names.length := List.length_map _

theorem recRenameNames_nodup {G W names : List Nat}
    (hlen : W.length = G.length) (hW : W.Nodup) (hnd : names.Nodup)
    (hnames : ∀ v ∈ names, v ∈ G) : (recRenameNames G W names).Nodup :=
  poolMap_nodup hlen hW hnd hnames

theorem recRenameNames_mem {G W names : List Nat}
    (hlen : W.length = G.length) (hnames : ∀ v ∈ names, v ∈ G) :
    ∀ v ∈ recRenameNames G W names, v ∈ W := by
  intro v hv
  obtain ⟨original, ho, rfl⟩ := List.mem_map.mp hv
  exact poolMap_mem hlen (hnames original ho)

theorem recRenameNames_composition {G W Xs names : List Nat}
    (hlen : W.length = G.length) (hXs : Xs.length = G.length) (hW : W.Nodup)
    (hnames : ∀ v ∈ names, v ∈ G) :
    recRenameNames W Xs (recRenameNames G W names) = recRenameNames G Xs names := by
  simp only [recRenameNames, List.map_map]
  apply List.map_congr_left
  intro v hv
  have hi : G.idxOf v < W.length := by have := List.idxOf_lt_length_iff.mpr (hnames v hv); omega
  simp only [Function.comp_def]
  change poolMap W Xs (poolMap G W v) = poolMap G Xs v
  rw [poolMap_eq hlen (hnames v hv)]
  have hiXs : G.idxOf v < Xs.length := by omega
  simp only [poolMap, hW.idxOf_getElem _ hi, List.getElem?_eq_getElem hiXs, Option.getD_some]

theorem Ty.mem_freeVars_onTy_of_pool_avoid {S : Subst} {W : List Nat} {ty : Ty} {v : Nat}
    (hdom : ∀ p ∈ S, p.1 ∉ W)
    (hran : ∀ p ∈ S, ∀ x ∈ p.2.freeVars, x ∉ W) (hv : v ∈ W) :
    v ∈ (S.onTy ty).freeVars ↔ v ∈ ty.freeVars := by
  constructor
  · intro himage
    by_contra hnot
    exact Subst.notMemOnTy (fun p hp hc => hran p hp v hc hv) hnot himage
  · intro hty
    apply Ty.mem_freeVars_substFvars_image.mpr
    refine ⟨v, hty, ?_⟩
    have hfix : S.onTy (.fvar v) = .fvar v := by
      apply Ty.substFvars_eq_self_of_no_key
      intro p hp hc
      have heq := List.mem_singleton.mp hc
      exact hdom p hp (heq ▸ hv)
    change v ∈ (S.onTy (.fvar v)).freeVars
    rw [hfix]
    exact List.mem_cons_self

theorem recNames_subst_pool_avoid {S : Subst} {W names : List Nat} {ty : Ty}
    (hdom : ∀ p ∈ S, p.1 ∉ W)
    (hran : ∀ p ∈ S, ∀ x ∈ p.2.freeVars, x ∉ W) :
    recNames names W (S.onTy ty) = recNames names W ty := by
  unfold recNames
  congr 1
  apply List.filter_congr
  intro v hv
  simp only [Ty.mem_freeVars_onTy_of_pool_avoid hdom hran hv]

private theorem scheme_ty_substFvars_congr {subst other : List (Nat × Ty)} {ty : Ty}
    (h : ∀ v ∈ ty.freeVars, (Ty.fvar v).substFvars subst = (Ty.fvar v).substFvars other) : ty.substFvars subst = ty.substFvars other := by
  induction ty using Ty.rec_strong with
  | prim p => simp only [Ty.substFvars_prim]
  | bvar i => simp only [Ty.substFvars_bvar]
  | fvar n => exact h n (by simp only [Ty.freeVars, List.mem_singleton])
  | arrow a b iha ihb =>
      rw [Ty.substFvars_arrow, Ty.substFvars_arrow,
        iha (fun v hv => h v (by simp only [Ty.freeVars, List.mem_dedup, List.mem_append]; exact .inl hv)),
        ihb (fun v hv => h v (by simp only [Ty.freeVars, List.mem_dedup, List.mem_append]; exact .inr hv))]
  | customTy name args ih =>
      rw [Ty.substFvars_customTy, Ty.substFvars_customTy]
      congr 1
      apply List.map_congr_left
      intro ty hty
      exact ih ty hty (fun v hv => h v (TyList.mem_freeVars_of_mem hty hv))

private theorem renameG_restrict_pool {G W names : List Nat} {ty : Ty}
    (hlen : W.length = G.length) (hG : G.Nodup) (hnd : names.Nodup)
    (hGW : ∀ g ∈ G, g ∉ W) (hnames : ∀ v ∈ names, v ∈ G)
    (hcover : ∀ v ∈ ty.freeVars, v ∈ G → v ∈ names) :
    Ty.renameG G W ty = Ty.renameG names (recRenameNames G W names) ty := by
  apply scheme_ty_substFvars_congr
  intro v hv
  by_cases hg : v ∈ G
  · have hn := hcover v hv hg
    have hfull : Ty.substFvars (G.zip (W.map Ty.fvar)) (.fvar v) = .fvar (poolMap G W v) :=
      Ty.substFvars_zip_fvar_renameG hlen hG hGW (List.getElem?_idxOf hg)
        (by rw [poolMap_eq hlen hg]; exact List.getElem?_eq_getElem _)
    rw [hfull]
    symm
    apply Ty.substFvars_zip_fvar_renameG (by simp [recRenameNames]) hnd
      (fun n hm hc => hGW n (hnames n hm) (recRenameNames_mem hlen hnames n hc))
      (List.getElem?_idxOf hn)
    simp only [recRenameNames, List.getElem?_map, List.getElem?_idxOf hn, Option.map_some]
    rfl
  · have hn : v ∉ names := fun hv => hg (hnames v hv)
    have fix : ∀ (keys : List Nat) (values : List Ty), v ∉ keys →
        Ty.substFvars (keys.zip values) (.fvar v) = .fvar v := by
      intro keys values hn
      apply Ty.substFvars_eq_self_of_no_key
      intro p hp hc
      exact hn ((List.mem_singleton.mp hc) ▸ (List.of_mem_zip hp).1)
    rw [fix _ _ hg, fix _ _ hn]

theorem recScheme_rename_pool {G W names : List Nat} {ty : Ty}
    (hlc : ty.IsLC) (hlen : W.length = G.length) (hG : G.Nodup) (hW : W.Nodup)
    (hGW : ∀ g ∈ G, g ∉ W) (hWty : ∀ w ∈ W, w ∉ ty.freeVars)
    (hnd : names.Nodup) (hnames : ∀ v ∈ names, v ∈ G) :
    recScheme (recRenameNames G W names) W (Ty.renameG G W ty) = recScheme names G ty := by
  unfold recScheme
  rw [recNames_rename_pool hlen hG hW hGW hWty hnames]
  have hsub : ∀ v ∈ recNames names G ty, v ∈ G := by
    intro v hv
    rcases mem_recNames.mp hv with hv | ⟨hv, _, _⟩
    · exact hnames v hv
    · exact hv
  have hclose := Ty.closeOver_rename (gs := recNames names G ty)
    (gs' := recRenameNames G W (recNames names G ty)) hlc
    (recRenameNames_length ..) (recNames_nodup hnd hG)
    (recRenameNames_nodup hlen hW (recNames_nodup hnd hG) hsub)
    (fun g hg hw => hGW g (hsub g hg) (recRenameNames_mem hlen hsub g hw))
    (fun w hw => hWty w (recRenameNames_mem hlen hsub w hw))
  change Ty.closeOver (recRenameNames G W (recNames names G ty))
    (Ty.renameG (recNames names G ty) (recRenameNames G W (recNames names G ty)) ty) = _ at hclose
  rw [← renameG_restrict_pool hlen hG (recNames_nodup hnd hG) hGW hsub
    (fun v hv hg => mem_recNames_of_mem_pool hg hv)] at hclose
  simp only [recRenameNames_length]
  exact congrArg (PolyTy.mk (recNames names G ty).length) hclose

 theorem recScheme_subst_pool_avoid {S : Subst} {W names : List Nat} {ty : Ty}
    (hdom : ∀ p ∈ S, p.1 ∉ W)
    (hran : ∀ p ∈ S, ∀ x ∈ p.2.freeVars, x ∉ W)
    (hnames : ∀ v ∈ names, v ∈ W) :
    recScheme names W (S.onTy ty) = S.onPolyTy (recScheme names W ty) := by
  unfold recScheme Subst.onPolyTy
  rw [recNames_subst_pool_avoid hdom hran]
  congr 1
  symm
  apply Ty.substFvars_closeOver
  · intro p hp hv
    rcases mem_recNames.mp hv with hv | ⟨hv, _, _⟩
    · exact hdom p hp (hnames p.1 hv)
    · exact hdom p hp hv
  · intro p hp v hv hn
    rcases mem_recNames.mp hn with hn | ⟨hn, _, _⟩
    · exact hran p hp v hv (hnames v hn)
    · exact hran p hp v hv hn

/-- Freshen the bound pool before applying an arbitrary LC source substitution.
The freshness assumptions concern the newly chosen pool and cofinite opening. -/
theorem Ty.renameG_subst_fresh_pool {S : Subst} {G W Xs : List Nat} {ty : Ty}
    (hlc : ty.IsLC) (hS : ∀ p ∈ S, p.2.IsLC)
    (hlen : W.length = G.length) (hG : G.Nodup) (hW : W.Nodup)
    (hGW : ∀ g ∈ G, g ∉ W) (hWty : ∀ w ∈ W, w ∉ ty.freeVars)
    (hdomW : ∀ p ∈ S, p.1 ∉ W)
    (hranW : ∀ p ∈ S, ∀ v ∈ p.2.freeVars, v ∉ W)
    (hXs : Xs.length = G.length)
    (hGXs : ∀ g ∈ G, g ∉ Xs) (hWXs : ∀ w ∈ W, w ∉ Xs)
    (hdomXs : ∀ p ∈ S, p.1 ∉ Xs) :
    Ty.renameG W Xs (S.onTy (Ty.renameG G W ty)) = S.onTy (Ty.renameG G Xs ty) := by
  have hGWeq : Ty.renameG G W ty = Ty.openVars W (Ty.closeOver G ty) :=
    (Ty.openVars_closeOver_rename hlc hG hlen hGW).symm
  have hGXeq : Ty.renameG G Xs ty = Ty.openVars Xs (Ty.closeOver G ty) :=
    (Ty.openVars_closeOver_rename hlc hG hXs hGXs).symm
  have hnew : S.onTy (Ty.renameG G W ty) = Ty.openVars W (S.onTy (Ty.closeOver G ty)) := by
    rw [hGWeq, Subst.onTy_openVars hS hdomW]
  have hnewLC : (S.onTy (Ty.renameG G W ty)).IsLC := by
    apply Subst.onTy_lc hS
    apply Subst.onTy_lc (S := G.zip (W.map Ty.fvar)) _ hlc
    intro p hp
    obtain ⟨_, _, heq⟩ := List.mem_map.mp (List.of_mem_zip hp).2
    rw [← heq]; exact .fvar
  have hclose : Ty.closeOver W (S.onTy (Ty.renameG G W ty)) = S.onTy (Ty.closeOver G ty) := by
    rw [hnew]
    apply Ty.closeOver_openVars_self hW
    · rw [hlen]
      exact Subst.onTy_containsBvars hS (Ty.closeOver_preserves_bvars hlc)
    · intro w hw
      exact Subst.notMemOnTy (fun p hp hv => hranW p hp w hv hw)
        (fun hv => hWty w hw (Ty.freeVars_closeOver_subset hv))
  have hh := (Ty.openVars_closeOver_rename hnewLC hW (hXs.trans hlen.symm) hWXs).symm
  change Ty.renameG W Xs (S.onTy (Ty.renameG G W ty)) = _ at hh
  rw [hclose] at hh
  rw [hh, hGXeq, Subst.onTy_openVars hS hdomXs]

private theorem recRenameNames_getD (G W : List Nat) (prefixes : List (List Nat)) (i : Nat) :
    (prefixes.map (recRenameNames G W))[i]?.getD [] = recRenameNames G W (prefixes[i]?.getD []) := by
  rw [List.getElem?_map]
  cases prefixes[i]? <;> rfl

/-- Reparameterizing the bound pool and then substituting free outer leaves
commutes with the literal ordered/vacuous export list. -/
theorem recCompletedSchemes_subst_fresh_pool {S : Subst} {G W : List Nat}
    {specs : List RecSpec} {prefixes : List (List Nat)}
    (_hS : ∀ p ∈ S, p.2.IsLC) (hlen : W.length = G.length) (hG : G.Nodup) (hW : W.Nodup)
    (hGW : ∀ g ∈ G, g ∉ W)
    (hWmono : ∀ ty, .mono ty ∈ specs → ∀ w ∈ W, w ∉ ty.freeVars)
    (hdomW : ∀ p ∈ S, p.1 ∉ W)
    (hranW : ∀ p ∈ S, ∀ v ∈ p.2.freeVars, v ∉ W)
    (hlc : ∀ ty, .mono ty ∈ specs → ty.IsLC)
    (hprefix : ∀ i, i < specs.length →
      (prefixes[i]?.getD []).Nodup ∧ ∀ v ∈ prefixes[i]?.getD [], v ∈ G) :
    recCompletedSchemes
      (specs.map (fun spec => RecSpec.onSubstSource S (RecSpec.onSubst (G.zip (W.map Ty.fvar)) spec)))
      (prefixes.map (recRenameNames G W)) W =
      (recCompletedSchemes specs prefixes G).map S.onPolyTy := by
  apply List.ext_get (by simp [recCompletedSchemes])
  intro i hi hj
  have hit : i < specs.length := by simpa [recCompletedSchemes] using hj
  simp only [recCompletedSchemes, List.get_eq_getElem, List.getElem_map, List.getElem_mapIdx,
    recRenameNames_getD]
  cases hs : specs[i]'hit with
  | poly scheme => rfl
  | mono ty =>
    obtain ⟨hnd, hsub⟩ := hprefix i hit
    have hty : .mono ty ∈ specs := hs ▸ List.getElem_mem hit
    change recScheme (recRenameNames G W (prefixes[i]?.getD [])) W
      (S.onTy (Ty.renameG G W ty)) = S.onPolyTy (recScheme (prefixes[i]?.getD []) G ty)
    rw [recScheme_subst_pool_avoid hdomW hranW (recRenameNames_mem hlen hsub),
      recScheme_rename_pool (hlc ty hty) hlen hG hW hGW (hWmono ty hty) hnd hsub]

 theorem recStageSchemes_subst_fresh_pool {S : Subst} {G W Xs : List Nat}
    {specs : List RecSpec} {prefixes : List (List Nat)}
    (hS : ∀ p ∈ S, p.2.IsLC) (hlen : W.length = G.length) (hG : G.Nodup) (hW : W.Nodup)
    (hGW : ∀ g ∈ G, g ∉ W)
    (hWmono : ∀ ty, .mono ty ∈ specs → ∀ w ∈ W, w ∉ ty.freeVars)
    (hdomW : ∀ p ∈ S, p.1 ∉ W)
    (hranW : ∀ p ∈ S, ∀ v ∈ p.2.freeVars, v ∉ W)
    (hlc : ∀ ty, .mono ty ∈ specs → ty.IsLC)
    (hprefix : ∀ i, i < specs.length →
      (prefixes[i]?.getD []).Nodup ∧ ∀ v ∈ prefixes[i]?.getD [], v ∈ G)
    (hXs : Xs.length = G.length) (hGXs : ∀ g ∈ G, g ∉ Xs)
    (hWXs : ∀ w ∈ W, w ∉ Xs) (hdomXs : ∀ p ∈ S, p.1 ∉ Xs) :
    (specs.map (fun spec => RecSpec.onSubstSource S (RecSpec.onSubst (G.zip (W.map Ty.fvar)) spec))).mapIdx
      (recStageEntry (prefixes.map (recRenameNames G W)) done W Xs) =
      (specs.mapIdx (recStageEntry prefixes done G Xs)).map S.onPolyTy := by
  apply List.ext_get (by simp)
  intro i hi hj
  have hit : i < specs.length := by simpa using hj
  simp only [List.get_eq_getElem, List.getElem_map, List.getElem_mapIdx]
  cases hs : specs[i]'hit with
  | poly scheme => rfl
  | mono ty =>
    have hty : .mono ty ∈ specs := hs ▸ List.getElem_mem hit
    simp only [RecSpec.onSubstSource, RecSpec.onSubst, recStageEntry, recRenameNames_getD]
    split
    · obtain ⟨hnd, hsub⟩ := hprefix i hit
      change recScheme (recRenameNames G W (prefixes[i]?.getD [])) W
        (S.onTy (Ty.renameG G W ty)) = S.onPolyTy (recScheme (prefixes[i]?.getD []) G ty)
      rw [recScheme_subst_pool_avoid hdomW hranW (recRenameNames_mem hlen hsub),
        recScheme_rename_pool (hlc ty hty) hlen hG hW hGW (hWmono ty hty) hnd hsub]
    · change PolyTy.mkTrivial (Ty.renameG W Xs (S.onTy (Ty.renameG G W ty))) =
        PolyTy.mkTrivial (S.onTy (Ty.renameG G Xs ty))
      rw [Ty.renameG_subst_fresh_pool (hlc ty hty) hS hlen hG hW hGW (hWmono ty hty)
        hdomW hranW hXs hGXs hWXs hdomXs]



@[simp] theorem BindingAnn.recModeAnn_subst_source (ann : BindingAnn) (S : Subst) :
    (ann.substTyFvars S).recModeAnn = ann.recModeAnn.map S.onPolyTy := by
  cases ann <;> rfl

@[simp] theorem BindingAnn.recPrefixCount_subst_source (ann : BindingAnn) (S : Subst) :
    (ann.substTyFvars S).recPrefixCount = ann.recPrefixCount := by
  cases ann <;> rfl

theorem RecPrefixesWF.subst_fresh_pool {S : Subst} {G W : List Nat}
    (h : RecPrefixesWF anns specs prefixes G) (hlen : W.length = G.length) (hW : W.Nodup) :
    RecPrefixesWF (anns.map (BindingAnn.substTyFvars S))
      (specs.map (fun spec => RecSpec.onSubstSource S (RecSpec.onSubst (G.zip (W.map Ty.fvar)) spec)))
      (prefixes.map (recRenameNames G W)) W := by
  refine ⟨by simpa only [List.length_map] using h.length, ?_⟩
  intro i ann names ha hn
  rw [List.getElem?_map] at ha hn
  obtain ⟨ann0, ha0, rfl⟩ := Option.map_eq_some_iff.mp ha
  obtain ⟨names0, hn0, rfl⟩ := Option.map_eq_some_iff.mp hn
  obtain ⟨hcount, hnd, hsub⟩ := h.member i ann0 names0 ha0 hn0
  exact ⟨by simpa using hcount, recRenameNames_nodup hlen hW hnd hsub,
    recRenameNames_mem hlen hsub⟩

theorem RecSpecs.WF.subst_fresh_pool {S : Subst} {G W : List Nat}
    {anns : List BindingAnn} {bindings : List Expr} {specs : List RecSpec}
    (h : RecSpecs.WF (anns.map BindingAnn.recModeAnn) bindings specs G)
    (hS : ∀ p ∈ S, p.2.IsLC) (hW : W.Nodup) :
    RecSpecs.WF ((anns.map (BindingAnn.substTyFvars S)).map BindingAnn.recModeAnn) bindings
      (specs.map (fun spec => RecSpec.onSubstSource S (RecSpec.onSubst (G.zip (W.map Ty.fvar)) spec))) W := by
  have hR : ∀ p ∈ G.zip (W.map Ty.fvar), p.2.IsLC := by
    intro p hp
    obtain ⟨_, _, heq⟩ := List.mem_map.mp (List.of_mem_zip hp).2
    rw [← heq]; exact .fvar
  refine ⟨?_, by simpa only [List.length_map] using h.length, hW, ?_, ?_⟩
  · have hmap : (specs.map (fun spec => RecSpec.onSubstSource S
        (RecSpec.onSubst (G.zip (W.map Ty.fvar)) spec))).map RecSpec.ann =
        (specs.map RecSpec.ann).map (Option.map S.onPolyTy) := by
      simp only [List.map_map]
      apply List.map_congr_left
      intro spec _
      cases spec <;> rfl
    rw [hmap, h.anns_eq]
    simp only [List.map_map, Function.comp_def, BindingAnn.recModeAnn_subst_source]
  · intro ty ht
    obtain ⟨spec, hs, heq⟩ := List.mem_map.mp ht
    cases spec with
    | poly scheme => cases heq
    | mono original =>
      cases heq
      exact Subst.onTy_lc hS (Subst.onTy_lc hR (h.mono_lc original hs))
  · intro scheme hs
    obtain ⟨spec, ho, heq⟩ := List.mem_map.mp hs
    cases spec with
    | mono ty => cases heq
    | poly original =>
      cases heq
      exact Subst.onPolyTy_wf hS (h.poly_wf original ho)


theorem _root_.RecSpec.lc_onSubstSource {S : Subst} (hS : ∀ p ∈ S, p.2.IsLC)
    {spec : RecSpec} (hs : spec.LC) : (spec.onSubstSource S).LC := by
  cases spec with
  | mono ty => exact Subst.onTy_lc hS hs
  | poly scheme => exact Subst.onPolyTy_wf hS hs

@[simp] theorem _root_.RecSpec.onSubstSource_nil (spec : RecSpec) : spec.onSubstSource [] = spec := by
  cases spec <;> simp [RecSpec.onSubstSource, Subst.onPolyTy, Subst.onTy, Ty.substFvars]

 theorem _root_.RecSpec.onSubstSource_append (spec : RecSpec) (first second : Subst) :
    spec.onSubstSource (first ++ second) = (spec.onSubstSource first).onSubstSource second := by
  cases spec <;> simp only [RecSpec.onSubstSource, Subst.onTy_append, Subst.onPolyTy_append]

/-- A factor through a fresh declarative pool opening generalizes its group scheme. -/
theorem recScheme_generalizes_genGroup_of_renameG
    {algWritten algPool declPool Xs : List Nat} {algTy declTy : Ty} {R : Subst}
    (hAlg : algTy.IsLC) (hDecl : declTy.IsLC) (hR : ∀ p ∈ R, p.2.IsLC)
    (hPool : declPool.Nodup) (hLen : Xs.length = declPool.length) (hXs : Xs.Nodup)
    (hDisjoint : ∀ g ∈ declPool, g ∉ Xs) (hFreshTy : ∀ x ∈ Xs, x ∉ declTy.freeVars)
    (hConnect : R.onTy algTy = Ty.renameG declPool Xs declTy)
    (hFreshExport : ∀ x ∈ Xs,
      x ∉ (R.onPolyTy (recScheme algWritten algPool algTy)).body.freeVars) :
    (R.onPolyTy (recScheme algWritten algPool algTy)).Generalizes (PolyTy.genGroup declPool declTy) := by
  let selected := Ty.genFilter Xs (Ty.renameG declPool Xs declTy)
  have hscheme : PolyTy.genGroup declPool declTy =
      PolyTy.genGroup Xs (Ty.renameG declPool Xs declTy) :=
    PolyTy.genGroup_renameG hDecl hLen hPool hXs hDisjoint hFreshTy
  have hselectedLen : selected.length = (Ty.genFilter declPool declTy).length := by
    have hh := congrArg PolyTy.paramCount hscheme
    exact hh.symm
  have hselectedND : selected.Nodup := hXs.filter _
  have hselectedSub : ∀ x ∈ selected, x ∈ Xs := fun _ hx => Ty.mem_of_mem_genFilter hx
  have hfilteredND : (Ty.genFilter declPool declTy).Nodup := hPool.filter _
  have hfilteredDisjoint : ∀ g ∈ Ty.genFilter declPool declTy, g ∉ selected :=
    fun g hg hx => hDisjoint g (Ty.mem_of_mem_genFilter hg) (hselectedSub g hx)
  apply closeOver_generalizes (g := recNames algWritten algPool algTy)
    (Xs := selected) hAlg hR (PolyTy.genGroup_wf hDecl) hselectedND hselectedLen
  · intro x hx hv
    exact hFreshTy x (hselectedSub x hx) (Ty.freeVars_closeOver_subset hv)
  · change Ty.openVars selected (Ty.closeOver (Ty.genFilter declPool declTy) declTy) = R.onTy algTy
    rw [Ty.openVars_closeOver_rename hDecl hfilteredND hselectedLen hfilteredDisjoint, hConnect]
    exact (Ty.renameG_eq_genFilter hLen hPool hXs hDisjoint hFreshTy).symm
  · intro x hx
    exact hFreshExport x (hselectedSub x hx)

/-- Ordered and vacuous authored prefixes preserve the candidate's scheme instances. -/
theorem recScheme_generalizes_of_renameG
    {algWritten algPool declWritten declPool Xs : List Nat} {algTy declTy : Ty} {R : Subst}
    (hAlg : algTy.IsLC) (hDecl : declTy.IsLC) (hR : ∀ p ∈ R, p.2.IsLC)
    (hPool : declPool.Nodup) (hWritten : declWritten.Nodup)
    (hWrittenPool : ∀ v ∈ declWritten, v ∈ declPool)
    (hLen : Xs.length = declPool.length) (hXs : Xs.Nodup)
    (hDisjoint : ∀ g ∈ declPool, g ∉ Xs) (hFreshTy : ∀ x ∈ Xs, x ∉ declTy.freeVars)
    (hConnect : R.onTy algTy = Ty.renameG declPool Xs declTy)
    (hFreshExport : ∀ x ∈ Xs,
      x ∉ (R.onPolyTy (recScheme algWritten algPool algTy)).body.freeVars) :
    (R.onPolyTy (recScheme algWritten algPool algTy)).Generalizes
      (recScheme declWritten declPool declTy) :=
  (recScheme_generalizes_genGroup_of_renameG hAlg hDecl hR hPool hLen hXs hDisjoint hFreshTy hConnect hFreshExport).trans
    (genGroup_generalizes_recScheme hDecl hPool hWritten hWrittenPool)

/-- A dependency already exported by the fine schedule can remain mono in a coarser candidate stage. -/
theorem recScheme_generalizes_opened_mono_of_renameG
    {algWritten algPool declPool Xs : List Nat} {algTy declTy : Ty} {R : Subst}
    (hAlg : algTy.IsLC) (hDecl : declTy.IsLC) (hR : ∀ p ∈ R, p.2.IsLC)
    (hPool : declPool.Nodup) (hLen : Xs.length = declPool.length) (hXs : Xs.Nodup)
    (hDisjoint : ∀ g ∈ declPool, g ∉ Xs) (hFreshTy : ∀ x ∈ Xs, x ∉ declTy.freeVars)
    (hConnect : R.onTy algTy = Ty.renameG declPool Xs declTy)
    (hFreshExport : ∀ x ∈ Xs,
      x ∉ (R.onPolyTy (recScheme algWritten algPool algTy)).body.freeVars)
    (opened : List Nat) :
    (R.onPolyTy (recScheme algWritten algPool algTy)).Generalizes
      (PolyTy.mkTrivial (Ty.renameG declPool opened declTy)) :=
  (recScheme_generalizes_genGroup_of_renameG hAlg hDecl hR hPool hLen hXs hDisjoint hFreshTy hConnect hFreshExport).trans
    (genGroup_generalizes_rename_mono hDecl)

end

/-! ## Close -/

section

/-- Every declaratively typed Core expression has correctly scoped type annotations. -/
theorem TypeOfHM.tyBvarBounded {ctx : Ctx} {expr : Expr} {ty : Ty}
    (h : TypeOfHM ctx expr ty) : expr.TyBvarBounded 0 := by
  induction h using TypeOfHM.rec
      (motive_2 := fun _ branch _ _ _ => branch.2.TyBvarBounded 0) with
  | primLitUnit => trivial
  | primLitInt => trivial
  | primLitNat => trivial
  | primLitChar => trivial
  | primBinOpIntAdd => trivial
  | primBinOpIntSub => trivial
  | primBinOpIntLt _ _ _ _ => trivial
  | primBinOpCharLt _ _ _ _ => trivial
  | var _ _ _ => trivial
  | ctor _ _ _ => trivial
  | lambda hpc hann _ _ ihbody =>
    exact ⟨fun t ht => (hann t ht) ▸ hpc, ihbody⟩
  | app _ _ ihf iharg => exact ⟨ihf, iharg⟩
  | letIn hwf hann _ _ _ ihcofin ihbody =>
    expose_names
    obtain ⟨Xs, hlen, hnodup, havoid⟩ := exists_fresh_names L M.paramCount
    have hrhs := ihcofin Xs ⟨hlen, hnodup, havoid⟩
    cases ann with
    | none => exact ⟨hrhs, ihbody⟩
    | some σ =>
      have hM : M = σ := hann σ rfl
      subst M
      refine ⟨by simpa only [Nat.zero_add] using hwf, ?_, ihbody⟩
      have hb := Expr.tyBvarBounded_of_openTyVarsAux Xs boundExpr 0 hrhs
      simpa only [Nat.zero_add, hlen] using hb
  | match_ _ _ _ ihscrut ihbranches =>
    refine ⟨ihscrut, Expr.TyBvarBounded.BranchList_iff.mpr ?_⟩
    intro p b hb
    exact ihbranches (p, b) hb
  | mk _ _ _ ihbody => exact ihbody
  | wildcard _ ihbody => exact ihbody
  | letRec hvalid hwf _ _ _ _ ihmono ihpoly ihbody =>
    expose_names
    have hbound : ∀ pair ∈ bindings.zip specs,
        pair.1.TyBvarBounded (RecAnn.params pair.2.ann) := by
      rintro ⟨rhs, spec⟩ hpair
      cases spec with
      | mono τ =>
        obtain ⟨member, hlookup⟩ := List.mem_iff_getElem?.mp hpair
        rw [List.getElem?_zip_eq_some] at hlookup
        obtain ⟨hrhs, hspec⟩ := hlookup
        have hmember : member < bindings.length :=
          (List.getElem?_eq_some_iff.mp hrhs).choose
        have hunsigned : RecGroups.UnsignedAt anns member := by
          rw [RecGroups.UnsignedAt, ← hwf.anns_eq, List.getElem?_map, hspec]
          rfl
        obtain ⟨component, hc, hm⟩ := List.mem_flatten.mp
          ((hvalid.covers_unsigned member hmember).mpr hunsigned)
        obtain ⟨stage, hstage⟩ := List.mem_iff_getElem?.mp hc
        obtain ⟨Xs, hlen, hnodup, havoid⟩ := exists_fresh_names L G.length
        exact ihmono stage component hstage Xs ⟨hlen, hnodup, havoid⟩
          member hm rhs τ hrhs hspec
      | poly σ =>
        obtain ⟨Ys, hlen, hnodup, havoid⟩ := exists_fresh_names L σ.paramCount
        have hopen := ihpoly (rhs, .poly σ) hpair σ rfl Ys ⟨hlen, hnodup, havoid⟩
        have hb := Expr.tyBvarBounded_of_openTyVarsAux Ys rhs 0 hopen
        simpa only [Nat.zero_add, hlen, RecSpec.ann, RecAnn.params] using hb
    refine ⟨?_, ?_, ihbody⟩
    · intro σ hσ
      rw [← hwf.anns_eq] at hσ
      obtain ⟨spec, hspec, heq⟩ := List.mem_map.mp hσ
      have hpolySpec : spec = .poly σ := RecSpec.ann_eq_some heq
      subst spec
      simpa only [Nat.zero_add] using hwf.poly_wf σ hspec
    · apply Expr.TyBvarBounded.RecGroup_of_zip
        (hwf.length.trans (by rw [← hwf.anns_eq, List.length_map]))
      intro pair hpair
      rw [← hwf.anns_eq, List.zip_map_right] at hpair
      obtain ⟨source, hsource, rfl⟩ := List.mem_map.mp hpair
      simpa only [Prod.map, id_eq, Nat.zero_add] using hbound source hsource

/-! Closing elaborated RHS annotations under a newly synthesized scheme must
reopen the term as well as its type. Existing inner scheme binders are shielded.
The freshness condition below is needed because `substTyFvars` is sequential.
-/

private theorem TyList.closeVarsFrom_map (depth : Nat) (names : List Nat)
    (types : List Ty) :
    TyList.closeVarsFrom depth names types = types.map (Ty.closeVarsFrom depth names) := by
  induction types with
  | nil => rfl
  | cons _ _ ih => simp [TyList.closeVarsFrom, ih]

theorem Ty.open_closeVarsFrom_rename {names fresh : List Nat}
    (hnames : names.Nodup) (hlen : fresh.length = names.length)
    (hdisj : ∀ name ∈ names, name ∉ fresh) (ty : Ty) (depth : Nat)
    (hbound : ContainsBvarsUpTo depth ty) :
    Ty.openVarsFrom depth fresh (Ty.closeVarsFrom depth names ty) =
      Ty.substFvars (names.zip (fresh.map Ty.fvar)) ty := by
  induction ty using Ty.rec_strong with
  | prim p => simp [Ty.closeVarsFrom, Ty.openVarsFrom, Ty.instantiate, Ty.substFvars_prim]
  | bvar i =>
      cases hbound with | bvar hi =>
        simp [Ty.closeVarsFrom, Ty.openVarsFrom, Ty.instantiate, Ty.substFvars_bvar, hi]
  | fvar name =>
      have h := Ty.openVars_closeOver_rename (τ := .fvar name) .fvar hnames hlen hdisj
      convert h using 1
      cases hi : names.idxOf? name with
      | none => simp [Ty.closeVarsFrom, Ty.closeOver, hi, Ty.openVarsFrom,
          Ty.openVars, Ty.instantiate]
      | some i =>
          have hil : i < names.length := by
            rw [List.idxOf?_eq_map_finIdxOf?_val] at hi
            obtain ⟨j, _, heq⟩ := Option.map_eq_some_iff.mp hi
            exact heq ▸ j.isLt
          simp [Ty.closeVarsFrom, Ty.closeOver, hi, Ty.openVarsFrom,
            Ty.openVars, Ty.instantiate, List.getElem?_eq_getElem (by omega : i < fresh.length)]
  | arrow a b iha ihb =>
      cases hbound with | arrow ha hb =>
        simp [Ty.closeVarsFrom, Ty.substFvars_arrow, iha ha, ihb hb]
  | customTy name args ih =>
      cases hbound with | customTy hall =>
        simp only [Ty.closeVarsFrom, TyList.closeVarsFrom_map,
          Ty.openVarsFrom_customTy, Ty.substFvars_customTy, List.map_map]
        congr 1
        exact List.map_congr_left (fun ty hty => ih ty hty (hall ty hty))

/-- Reopening a completed RHS renames its generalized annotation variables,
including beneath already-present scheme binders. -/
theorem Expr.open_closeTyVarsAux_rename {names fresh : List Nat}
    (hnames : names.Nodup) (hlen : fresh.length = names.length)
    (hdisj : ∀ name ∈ names, name ∉ fresh) (expr : Expr) :
    ∀ depth, expr.TyBvarBounded depth →
      (expr.closeTyVarsAux depth names).openTyVarsAux depth fresh =
        expr.substTyFvars (names.zip (fresh.map Ty.fvar)) := by
  induction expr using Expr.rec_strong with
  | primLit p =>
      intro _ _
      exact (Expr.substTyFvars_eq_self_of_tyFreeVars_nil _ rfl).symm
  | primBinOp op =>
      intro _ _
      exact (Expr.substTyFvars_eq_self_of_tyFreeVars_nil _ rfl).symm
  | var i => intro _ _; exact Expr.substTyFvars_var.symm
  | ctor name =>
      intro _ _
      exact (Expr.substTyFvars_eq_self_of_tyFreeVars_nil _ rfl).symm
  | lambda ann body ih =>
      intro depth hbound
      simp only [Expr.TyBvarBounded] at hbound
      simp only [Expr.closeTyVarsAux, Expr.openTyVarsAux, Expr.substTyFvars_lambda]
      rw [ih depth hbound.2]
      congr 1
      cases ann with
      | none => rfl
      | some ty =>
          simp only [Option.map_some, Option.some.injEq]
          exact Ty.open_closeVarsFrom_rename hnames hlen hdisj ty depth (hbound.1 ty rfl)
  | app f x ihf ihx =>
      intro depth hbound
      simp only [Expr.TyBvarBounded] at hbound
      simp only [Expr.closeTyVarsAux, Expr.openTyVarsAux, Expr.substTyFvars_app,
        ihf depth hbound.1, ihx depth hbound.2]
  | letIn ann rhs body ihr ihb =>
      intro depth hbound
      cases ann with
      | none =>
          simp only [Expr.TyBvarBounded] at hbound
          simp only [Expr.closeTyVarsAux, Expr.openTyVarsAux, Expr.substTyFvars_letIn,
            Option.map_none, ihr depth hbound.1, ihb depth hbound.2]
      | some scheme =>
          simp only [Expr.TyBvarBounded] at hbound
          simp only [Expr.closeTyVarsAux, Expr.openTyVarsAux, Expr.substTyFvars_letIn,
            Option.map_some, ihr (depth + scheme.paramCount) hbound.2.1,
            ihb depth hbound.2.2]
          congr 3
          exact Ty.open_closeVarsFrom_rename hnames hlen hdisj scheme.body
            (depth + scheme.paramCount) hbound.1
  | match_ scrut branches ihs ihbs =>
      intro depth hbound
      simp only [Expr.TyBvarBounded] at hbound
      simp only [Expr.closeTyVarsAux, Expr.openTyVarsAux, Expr.substTyFvars_match,
        ihs depth hbound.1]
      congr 1
      have hall := Expr.TyBvarBounded.BranchList_iff.mp hbound.2
      clear hbound ihs
      induction branches with
      | nil => rfl
      | cons head tail ih =>
          rcases head with ⟨pat, body⟩
          simp only [BranchList.closeTyVarsAux, BranchList.openTyVarsAux, List.map_cons,
            List.cons.injEq, Prod.mk.injEq, true_and]
          exact ⟨ihbs pat body List.mem_cons_self depth (hall pat body List.mem_cons_self),
            ih (fun p b h => ihbs p b (List.mem_cons_of_mem _ h))
              (fun p b h => hall p b (List.mem_cons_of_mem _ h))⟩
  | letRec anns bindings body ihbs ihb =>
      intro depth hbound
      simp only [Expr.TyBvarBounded] at hbound
      simp only [Expr.closeTyVarsAux, Expr.openTyVarsAux, Expr.substTyFvars_letRec,
        ihb depth hbound.2.2, Expr.letRec.injEq, and_true]
      constructor
      · simp only [RecGroup.closeAnns, RecGroup.openAnns, List.map_map]
        apply List.map_congr_left
        intro ann hann
        cases ann with
        | none => simp
        | some scheme =>
            simp only [Function.comp_apply, Option.map_some, RecAnn.substFvars_some,
              PolyTy.substFvars_eq, Option.some.injEq, PolyTy.mk.injEq, true_and]
            exact Ty.open_closeVarsFrom_rename hnames hlen hdisj scheme.body
              (depth + scheme.paramCount) (hbound.1 scheme hann)
      · have hbindings := hbound.2.1
        clear hbound ihb
        induction bindings generalizing anns with
        | nil => cases anns <;> rfl
        | cons binding rest ih =>
            cases anns with
            | nil =>
                simp only [RecGroup.closeAnns, List.map_nil, RecGroup.closeTyVarsAux,
                  RecGroup.openTyVarsAux, List.map_cons, Expr.TyBvarBounded.RecGroup,
                  List.cons.injEq] at hbindings ⊢
                exact ⟨ihbs binding List.mem_cons_self depth hbindings.1,
                  ih [] (fun e h => ihbs e (List.mem_cons_of_mem _ h)) hbindings.2⟩
            | cons ann anns =>
                cases ann <;>
                  simp only [RecGroup.closeAnns, List.map_cons, Option.map_none,
                    Option.map_some, RecGroup.closeTyVarsAux, RecGroup.openTyVarsAux,
                    RecAnn.params, Expr.TyBvarBounded.RecGroup, Nat.add_zero,
                    List.cons.injEq] at hbindings ⊢
                all_goals exact ⟨ihbs binding List.mem_cons_self _ hbindings.1,
                  ih anns (fun e h => ihbs e (List.mem_cons_of_mem _ h)) hbindings.2⟩

theorem Expr.open_closeTyVars_rename {names fresh : List Nat}
    (hnames : names.Nodup) (hlen : fresh.length = names.length)
    (hdisj : ∀ name ∈ names, name ∉ fresh) {expr : Expr}
    (hbound : expr.TyBvarBounded 0) :
    (expr.closeTyVars names).openTyVars fresh =
      expr.substTyFvars (names.zip (fresh.map Ty.fvar)) :=
  Expr.open_closeTyVarsAux_rename hnames hlen hdisj expr 0 hbound

/-- Generalising an elaborated RHS closes its annotations under the same ordered
binders as its result type. Unlike the unannotated Core rule, the resulting
cofinite premise opens BOTH the RHS and the scheme. -/
theorem TypeOfHM.generaliseAnnotated {ctx : Ctx} {expr : Expr} {ty : Ty}
    {names : List Nat} (htyping : TypeOfHM ctx expr ty)
    (hnames : names.Nodup)
    (hctx : ∀ name ∈ names, name ∉ ctx.env.freeVars) :
    GeneralisesTo TypeOfHM ctx (some ⟨names.length, Ty.closeOver names ty⟩)
      (expr.closeTyVars names) ⟨names.length, Ty.closeOver names ty⟩ names := by
  intro fresh hfresh
  have hdisj : ∀ name ∈ names, name ∉ fresh :=
    fun name hn hf => hfresh.avoid name hf hn
  rw [Expr.openBoundTyVars,
    Expr.open_closeTyVars_rename hnames hfresh.length hdisj htyping.tyBvarBounded]
  change TypeOfHM ctx (expr.substTyFvars (names.zip (fresh.map Ty.fvar)))
    (Ty.openVars fresh (Ty.closeOver names ty))
  rw [Ty.openVars_closeOver_rename (TypeOfHM.regular htyping) hnames hfresh.length hdisj]
  apply TypeOfHM.typ_substs_preservation _ _ _ htyping
  · intro pair hp
    exact hctx pair.1 (List.of_mem_zip hp).1
  · intro pair hp
    obtain ⟨name, _, heq⟩ := List.mem_map.mp (List.of_mem_zip hp).2
    rw [← heq]
    exact .fvar

/-- Substitution transports a completed RHS's cofinite scheme premise. This
corollary reuses the existing source substitution theorem, including its binder
freshening, rather than maintaining a second transport proof. -/
theorem GeneralisesTo.onSubst_annotated {ctx : Ctx} {rhs : Expr} {scheme : PolyTy}
    {avoid : List Nat} (hwf : scheme.WF)
    (h : GeneralisesTo TypeOfHM ctx (some scheme) rhs scheme avoid)
    (subst : Subst) (hlc : ∀ pair ∈ subst, pair.2.IsLC) :
    ∃ avoid', GeneralisesTo TypeOfHM (subst.onCtx ctx) (some (subst.onPolyTy scheme))
      (rhs.substTyFvars subst) (subst.onPolyTy scheme) avoid' := by
  have hlet : TypeOfHM ctx (.letIn (some scheme) rhs (.primLit .unit)) (.prim .unit) :=
    .letIn hwf (fun _ heq => Option.some.inj heq) h rfl .primLitUnit
  have transported := TypeOfHM.onSubst subst hlc hlet
  simp only [Expr.substTyFvars_letIn, Option.map_some] at transported
  cases transported with
  | letIn _ hpins hgen _ _ =>
      have heq := hpins _ rfl
      subst heq
      exact ⟨_, hgen⟩

/-- Substitution changes annotations only, so it preserves runtime shape. -/
theorem Expr.erase_substTyFvars (expr : Expr) (subst : Subst) :
    (expr.substTyFvars subst).erase = expr.erase := by
  induction expr using Expr.rec_strong with
  | primLit => rw [Expr.substTyFvars_eq_self_of_tyFreeVars_nil subst rfl]
  | primBinOp => rw [Expr.substTyFvars_eq_self_of_tyFreeVars_nil subst rfl]
  | var => rw [Expr.substTyFvars_var]
  | ctor => rw [Expr.substTyFvars_eq_self_of_tyFreeVars_nil subst rfl]
  | lambda ann body ih => simp only [Expr.substTyFvars_lambda, Expr.erase, ih]
  | app f x ihf ihx => simp only [Expr.substTyFvars_app, Expr.erase, ihf, ihx]
  | letIn ann rhs body ihr ihb => simp only [Expr.substTyFvars_letIn, Expr.erase, ihr, ihb]
  | match_ scrut branches ihs ihbs =>
      simp only [Expr.substTyFvars_match, Expr.erase, ihs, List.map_map]
      congr 1
      exact List.map_congr_left (fun pair hp => congrArg (Prod.mk pair.1) (ihbs pair.1 pair.2 hp))
  | letRec anns bindings body ihbs ihb =>
      simp only [Expr.substTyFvars_letRec, Expr.erase, ihb, List.map_map]
      congr 1
      exact List.map_congr_left (fun binding hb => ihbs binding hb)


/-- Closing scoped type variables changes only annotations, which erasure discards. -/
theorem Expr.erase_closeTyVarsAux (expr : Expr) (depth : Nat) (names : List Nat) :
    (expr.closeTyVarsAux depth names).erase = expr.erase := by
  induction expr using Expr.rec_strong generalizing depth with
  | primLit p => rfl
  | primBinOp op => rfl
  | var i => rfl
  | ctor name => rfl
  | lambda ann body ih => simp only [Expr.closeTyVarsAux, Expr.erase, ih]
  | app f arg ihf iha => simp only [Expr.closeTyVarsAux, Expr.erase, ihf, iha]
  | letIn ann rhs body ihr ihb =>
    cases ann <;> simp only [Expr.closeTyVarsAux, Expr.erase, ihr, ihb]
  | match_ scrut branches ihs ihbs =>
    simp only [Expr.closeTyVarsAux, Expr.erase, ihs]
    congr 1
    induction branches with
    | nil => rfl
    | cons head tail ih =>
      rcases head with ⟨pat, body⟩
      simp only [BranchList.closeTyVarsAux, List.map_cons]
      rw [ihbs pat body List.mem_cons_self depth]
      congr 1
      exact ih (fun p b hb => ihbs p b (List.mem_cons_of_mem _ hb))
  | letRec anns bindings body ihbs ihb =>
    have hgroup : ∀ anns depth,
        (RecGroup.closeTyVarsAux depth names anns bindings).map Expr.erase = bindings.map Expr.erase := by
      induction bindings with
      | nil => intro _ _; rfl
      | cons head tail ih =>
        intro anns depth
        cases anns <;> simp only [RecGroup.closeTyVarsAux, List.map_cons]
        all_goals
          rw [ihbs head List.mem_cons_self]
          congr 1
          exact ih (fun b hb => ihbs b (List.mem_cons_of_mem _ hb)) _ _
    have hlen := congrArg List.length (hgroup anns depth)
    simp only [List.length_map] at hlen
    simp only [Expr.closeTyVarsAux, Expr.erase, ihb, hgroup]
    congr 1
    simp only [List.map_const', hlen]

/-- Erasure is invariant under closing any list of names, including duplicates. -/
theorem Expr.erase_closeTyVars (expr : Expr) (names : List Nat) :
    (expr.closeTyVars names).erase = expr.erase :=
  expr.erase_closeTyVarsAux 0 names

end

/-! ## Typing -/

section

/-- Pointwise fixing of the opening names suffices; the substitution's literal
domain may contain those names and its ranges may mention them. -/
theorem Subst.onTy_openVarsFrom_of_fixes {S : Subst} {Xs : List Nat}
    (hlc : ∀ p ∈ S, p.2.IsLC)
    (hfix : ∀ x ∈ Xs, S.onTy (.fvar x) = .fvar x) (ty : Ty) (depth : Nat) :
    S.onTy (Ty.openVarsFrom depth Xs ty) = Ty.openVarsFrom depth Xs (S.onTy ty) := by
  induction ty using Ty.rec_strong with
  | prim p => simp only [Ty.openVarsFrom, Ty.instantiate, Subst.onTy_prim]
  | bvar i =>
    simp only [Subst.onTy_bvar, Ty.openVarsFrom, Ty.instantiate]
    by_cases hi : i < depth
    · simp only [if_pos hi, Subst.onTy_bvar]
    · simp only [if_neg hi]
      cases hx : Xs[i - depth]? with
      | none => exact Subst.onTy_bvar
      | some x => exact hfix x (List.mem_of_getElem? hx)
  | fvar v =>
    change S.onTy (.fvar v) = Ty.openVarsFrom depth Xs (S.onTy (.fvar v))
    exact (Ty.instantiate_eq_self_of_lc (Subst.onTy_lc hlc .fvar)).symm
  | arrow a b iha ihb =>
    simp only [Ty.openVarsFrom, Ty.instantiate, Subst.onTy_arrow] at *
    exact congrArg₂ Ty.arrow iha ihb
  | customTy name args ih =>
    simp only [Ty.openVarsFrom, Ty.instantiate, TyList.instantiate_eq_map,
      Subst.onTy_customTy, List.map_map]
    congr 1
    exact List.map_congr_left (fun t ht => ih t ht)

theorem Subst.onTy_openVars_of_fixes {S : Subst} {Xs : List Nat}
    (hlc : ∀ p ∈ S, p.2.IsLC)
    (hfix : ∀ x ∈ Xs, S.onTy (.fvar x) = .fvar x) {ty : Ty} :
    S.onTy (Ty.openVars Xs ty) = Ty.openVars Xs (S.onTy ty) := by
  simpa only [Ty.openVarsFrom, Nat.not_lt_zero, if_false, Nat.sub_zero, Ty.openVars] using Subst.onTy_openVarsFrom_of_fixes hlc hfix ty 0


/-- Free-variable replacement cannot remove an existing bound variable. -/
theorem ContainsBvarsUpTo.of_substFvar {n Z : Nat} {U ty : Ty}
    (h : ContainsBvarsUpTo n (Ty.substFvar Z U ty)) : ContainsBvarsUpTo n ty := by
  induction ty using Ty.rec_strong with
  | prim p => exact .prim
  | bvar i => exact h
  | fvar v => exact .fvar
  | arrow a b iha ihb => cases h with | arrow ha hb => exact .arrow (iha ha) (ihb hb)
  | customTy name args ih =>
    cases h with
    | customTy hall =>
      exact .customTy (fun t ht => ih t ht (hall _ (by
        rw [TyList.substFvar_eq_map]; exact List.mem_map.mpr ⟨t, ht, rfl⟩)))

theorem ContainsBvarsUpTo.of_substFvars {n : Nat} {S : Subst} {ty : Ty}
    (h : ContainsBvarsUpTo n (Ty.substFvars S ty)) : ContainsBvarsUpTo n ty := by
  induction S generalizing ty with
  | nil => exact h
  | cons pair rest ih => exact ContainsBvarsUpTo.of_substFvar (ih h)

private theorem branch_tyFreeVars_mem {branches : List (MatchPattern × Expr)}
    {p : MatchPattern} {body : Expr} {v : Nat} (hb : (p, body) ∈ branches)
    (hv : v ∈ body.tyFreeVars) :
    v ∈ Expr.tyFreeVars.BranchList.tyFreeVars branches := by
  induction branches with
  | nil => cases hb
  | cons head tail ih =>
    rcases head with ⟨p', body'⟩
    simp only [Expr.tyFreeVars.BranchList.tyFreeVars, List.mem_append]
    rcases List.mem_cons.mp hb with heq | hb
    · cases heq; exact Or.inl hv
    · exact Or.inr (ih hb)

/-- Pointwise identity on annotation free variables fixes an entire Core expression. -/
theorem Expr.substTyFvars_eq_self_of_fixes {S : Subst} {e : Expr}
    (h : ∀ v ∈ e.tyFreeVars, S.onTy (.fvar v) = .fvar v) :
    e.substTyFvars S = e := by
  induction e using Expr.rec_strong with
  | primLit p =>
    exact Expr.substTyFvars_eq_self_of_not_mem_tyFreeVars (by simp [Expr.tyFreeVars])
  | primBinOp op =>
    exact Expr.substTyFvars_eq_self_of_not_mem_tyFreeVars (by simp [Expr.tyFreeVars])
  | var n => exact Expr.substTyFvars_var
  | ctor name =>
    exact Expr.substTyFvars_eq_self_of_not_mem_tyFreeVars (by simp [Expr.tyFreeVars])
  | lambda ann body ih =>
    rw [Expr.substTyFvars_lambda]
    have hb := ih (fun v hv => h v (List.mem_append_right _ hv))
    rw [hb]
    cases ann with
    | none => rfl
    | some t =>
      have ht : Ty.substFvars S t = t := Subst.onTy_eq_self_of_fixes
        (fun v hv => h v (List.mem_append_left _ hv))
      simp only [Option.map_some, ht]
  | app f arg ihf iha =>
    rw [Expr.substTyFvars_app,
      ihf (fun v hv => h v (List.mem_append_left _ hv)),
      iha (fun v hv => h v (List.mem_append_right _ hv))]
  | letIn ann rhs body ihr ihb =>
    rw [Expr.substTyFvars_letIn,
      ihr (fun v hv => h v (List.mem_append_left _ (List.mem_append_right _ hv))),
      ihb (fun v hv => h v (List.mem_append_right _ hv))]
    cases ann with
    | none => rfl
    | some scheme =>
      have hs : Ty.substFvars S scheme.body = scheme.body := Subst.onTy_eq_self_of_fixes
        (fun v hv => h v (List.mem_append_left _ (List.mem_append_left _ hv)))
      simp only [Option.map_some, hs]
  | match_ scrut branches ihs ihbs =>
    rw [Expr.substTyFvars_match, ihs (fun v hv => h v (List.mem_append_left _ hv))]
    congr 1
    apply List.map_eq_self_of_forall_eq_id
    rintro ⟨p, b⟩ hb
    change (p, b.substTyFvars S) = (p, b)
    rw [ihbs p b hb (fun v hv => h v
      (List.mem_append_right _ (branch_tyFreeVars_mem hb hv)))]
  | letRec anns bindings body ihbs ihb =>
    rw [Expr.substTyFvars_letRec,
      ihb (fun v hv => h v (List.mem_append_right _ hv))]
    have hbindings : bindings.map (fun b => b.substTyFvars S) = bindings := by
      apply List.map_eq_self_of_forall_eq_id
      intro b hb
      apply ihbs b hb
      intro v hv
      apply h v
      apply List.mem_append_left
      apply List.mem_append_right
      exact Expr.mem_flatMap_tyFreeVars_iff_recGroup.mp (List.mem_flatMap.mpr ⟨b, hb, hv⟩)
    rw [hbindings]
    congr 1
    apply List.map_eq_self_of_forall_eq_id
    intro ann hann
    cases ann with
    | none => exact RecAnn.substFvars_none S
    | some scheme =>
      have hs : Ty.substFvars S scheme.body = scheme.body := Subst.onTy_eq_self_of_fixes
        (fun v hv => h v (List.mem_append_left _ (List.mem_append_left _
          (Expr.scheme_body_mem_annList_tyFreeVars hann hv))))
      simp only [RecAnn.substFvars_some, PolyTy.substFvars_eq, hs]

/-- Literal domain avoidance implies pointwise rigidity of the composite. -/
theorem Subst.fixes_of_dom_avoids {K : List Nat} {subst : Subst}
    (h : ∀ pair ∈ subst, pair.1 ∉ K) :
    ∀ v ∈ K, subst.onTy (.fvar v) = .fvar v := by
  intro v hv
  apply Ty.substFvars_eq_self_of_no_key
  intro pair hp hc
  have heq : pair.1 = v := by simpa only [Ty.freeVars, List.mem_singleton] using hc
  exact h pair hp (heq ▸ hv)

private theorem annList_subst_image {S : Subst} {w : Nat}
    (anns : List (Option PolyTy))
    (h : w ∈ Expr.tyFreeVars.AnnList.tyFreeVars (anns.map (RecAnn.substFvars S))) :
    ∃ k ∈ Expr.tyFreeVars.AnnList.tyFreeVars anns, w ∈ (S.onTy (.fvar k)).freeVars := by
  induction anns with
  | nil => simp [Expr.tyFreeVars.AnnList.tyFreeVars] at h
  | cons ann rest ih =>
    cases ann with
    | none =>
      simp only [List.map_cons, RecAnn.substFvars_none, Expr.tyFreeVars.AnnList.tyFreeVars,
        Option.elim, List.nil_append] at h ⊢
      exact ih h
    | some scheme =>
      simp only [List.map_cons, RecAnn.substFvars_some, Expr.tyFreeVars.AnnList.tyFreeVars,
        Option.elim, List.mem_append, PolyTy.body_substFvars] at h ⊢
      rcases h with h | h
      · obtain ⟨k, hk, hv⟩ := Ty.mem_freeVars_substFvars_image.mp h
        exact ⟨k, Or.inl hk, hv⟩
      · obtain ⟨k, hk, hv⟩ := ih h
        exact ⟨k, Or.inr hk, hv⟩

/-- Every annotation variable after substitution comes from the substituted
image of an annotation variable of the original expression. -/
theorem Expr.mem_tyFreeVars_substTyFvars_image {S : Subst} {w : Nat} {e : Expr}
    (h : w ∈ (e.substTyFvars S).tyFreeVars) :
    ∃ k ∈ e.tyFreeVars, w ∈ (S.onTy (.fvar k)).freeVars := by
  induction e using Expr.rec_strong with
  | primLit p =>
    rw [Expr.substTyFvars_eq_self_of_not_mem_tyFreeVars (by simp [Expr.tyFreeVars])] at h
    simp [Expr.tyFreeVars] at h
  | primBinOp op =>
    rw [Expr.substTyFvars_eq_self_of_not_mem_tyFreeVars (by simp [Expr.tyFreeVars])] at h
    simp [Expr.tyFreeVars] at h
  | ctor c =>
    rw [Expr.substTyFvars_eq_self_of_not_mem_tyFreeVars (by simp [Expr.tyFreeVars])] at h
    simp [Expr.tyFreeVars] at h
  | var i => simp [Expr.substTyFvars_var, Expr.tyFreeVars] at h
  | lambda ann body ih =>
    rw [Expr.substTyFvars_lambda] at h
    cases ann with
    | none =>
      simp only [Expr.tyFreeVars, Option.map_none, Option.elim_none, List.nil_append] at h ⊢
      exact ih h
    | some t =>
      simp only [Expr.tyFreeVars, Option.map_some, Option.elim_some, List.mem_append] at h ⊢
      rcases h with h | h
      · obtain ⟨k, hk, hv⟩ := Ty.mem_freeVars_substFvars_image.mp h
        exact ⟨k, Or.inl hk, hv⟩
      · obtain ⟨k, hk, hv⟩ := ih h
        exact ⟨k, Or.inr hk, hv⟩
  | app f arg ihf iha =>
    rw [Expr.substTyFvars_app] at h
    simp only [Expr.tyFreeVars, List.mem_append] at h ⊢
    rcases h with h | h
    · obtain ⟨k, hk, hv⟩ := ihf h
      exact ⟨k, Or.inl hk, hv⟩
    · obtain ⟨k, hk, hv⟩ := iha h
      exact ⟨k, Or.inr hk, hv⟩
  | letIn ann rhs body ihr ihb =>
    rw [Expr.substTyFvars_letIn] at h
    cases ann with
    | none =>
      simp only [Expr.tyFreeVars, Option.map_none, Option.elim_none, List.nil_append,
        List.mem_append] at h ⊢
      rcases h with h | h
      · obtain ⟨k, hk, hv⟩ := ihr h
        exact ⟨k, Or.inl hk, hv⟩
      · obtain ⟨k, hk, hv⟩ := ihb h
        exact ⟨k, Or.inr hk, hv⟩
    | some scheme =>
      simp only [Expr.tyFreeVars, Option.map_some, Option.elim_some, List.mem_append] at h ⊢
      rcases h with (h | h) | h
      · obtain ⟨k, hk, hv⟩ := Ty.mem_freeVars_substFvars_image.mp h
        exact ⟨k, Or.inl (Or.inl hk), hv⟩
      · obtain ⟨k, hk, hv⟩ := ihr h
        exact ⟨k, Or.inl (Or.inr hk), hv⟩
      · obtain ⟨k, hk, hv⟩ := ihb h
        exact ⟨k, Or.inr hk, hv⟩
  | match_ scrut branches ihs ihbs =>
    rw [Expr.substTyFvars_match] at h
    simp only [Expr.tyFreeVars, List.mem_append] at h ⊢
    rcases h with h | h
    · obtain ⟨k, hk, hv⟩ := ihs h
      exact ⟨k, Or.inl hk, hv⟩
    · obtain ⟨branch, hb, hv⟩ := Expr.mem_branchListTyFreeVars h
      obtain ⟨⟨p, body⟩, hsource, rfl⟩ := List.mem_map.mp hb
      obtain ⟨k, hk, hv⟩ := ihbs p body hsource hv
      exact ⟨k, Or.inr (Expr.mem_branchListTyFreeVars_of hsource hk), hv⟩
  | letRec anns bindings body ihbs ihb =>
    rw [Expr.substTyFvars_letRec] at h
    simp only [Expr.tyFreeVars, List.mem_append] at h ⊢
    rcases h with (h | h) | h
    · obtain ⟨k, hk, hv⟩ := annList_subst_image anns h
      exact ⟨k, Or.inl (Or.inl hk), hv⟩
    · obtain ⟨output, ho, hv⟩ := Expr.mem_recGroupTyFreeVars h
      obtain ⟨source, hs, rfl⟩ := List.mem_map.mp ho
      obtain ⟨k, hk, hv⟩ := ihbs source hs hv
      exact ⟨k, Or.inl (Or.inr (Expr.mem_recGroupTyFreeVars_of hs hk)), hv⟩
    · obtain ⟨k, hk, hv⟩ := ihb h
      exact ⟨k, Or.inr hk, hv⟩

mutual
theorem TyTemplate.allocate_bounds (template : TyTemplate) (frontier : Nat) :
    frontier ≤ (template.allocate frontier).1 ∧
      ((∀ v ∈ template.rigidVars, v < frontier) →
        Ty.BelowFvars (template.allocate frontier).1 (template.allocate frontier).2) := by
  cases template with
  | fixed ty => exact ⟨Nat.le_refl _, Ty.BelowFvars.of_freeVars_lt⟩
  | hole => exact ⟨Nat.le_succ _, fun _ => .fvar (Nat.lt_succ_self _)⟩
  | arrow a b =>
    obtain ⟨hale, hab⟩ := a.allocate_bounds frontier
    obtain ⟨hble, hbb⟩ := b.allocate_bounds (a.allocate frontier).1
    refine ⟨hale.trans hble, fun hr => .arrow ?_ ?_⟩
    · exact (hab (fun v hv => hr v (List.mem_append_left _ hv))).mono hble
    · exact hbb (fun v hv => Nat.lt_of_lt_of_le (hr v (List.mem_append_right _ hv)) hale)
  | custom name args =>
    obtain ⟨hle, hb⟩ := allocateList_bounds args frontier
    exact ⟨hle, fun hr => .customTy (hb hr)⟩
theorem allocateList_bounds (templates : List TyTemplate) (frontier : Nat) :
    frontier ≤ (allocateList frontier templates).1 ∧
      ((∀ v ∈ rigidVarsList templates, v < frontier) →
        ∀ t ∈ (allocateList frontier templates).2, Ty.BelowFvars (allocateList frontier templates).1 t) := by
  cases templates with
  | nil => exact ⟨Nat.le_refl _, fun _ _ ht => by cases ht⟩
  | cons template rest =>
    obtain ⟨hhle, hhb⟩ := template.allocate_bounds frontier
    obtain ⟨htle, htb⟩ := allocateList_bounds rest (template.allocate frontier).1
    refine ⟨hhle.trans htle, ?_⟩
    intro hr t ht
    rcases List.mem_cons.mp ht with rfl | ht
    · exact (hhb (fun v hv => hr v (List.mem_append_left _ hv))).mono htle
    · exact htb (fun v hv => Nat.lt_of_lt_of_le (hr v (List.mem_append_right _ hv)) hhle) t ht
end



mutual
theorem TyTemplate.substTyFvars_openTyVarsFrom_of_fixes (template : TyTemplate) {S : Subst} {Xs : List Nat}
    (hlc : ∀ p ∈ S, p.2.IsLC)
    (hfix : ∀ x ∈ Xs, S.onTy (.fvar x) = .fvar x) (depth : Nat) :
    (template.openTyVarsFrom depth Xs).substTyFvars S =
      (template.substTyFvars S).openTyVarsFrom depth Xs := by
  cases template with
  | fixed ty => exact congrArg TyTemplate.fixed (Subst.onTy_openVarsFrom_of_fixes hlc hfix ty depth)
  | hole => rfl
  | arrow a b =>
    simp only [TyTemplate.openTyVarsFrom, TyTemplate.substTyFvars,
      a.substTyFvars_openTyVarsFrom_of_fixes hlc hfix depth,
      b.substTyFvars_openTyVarsFrom_of_fixes hlc hfix depth]
  | custom name args =>
    exact congrArg (TyTemplate.custom name) (templateList_open_subst_of_fixes args hlc hfix depth)
private theorem templateList_open_subst_of_fixes (templates : List TyTemplate) {S : Subst} {Xs : List Nat}
    (hlc : ∀ p ∈ S, p.2.IsLC)
    (hfix : ∀ x ∈ Xs, S.onTy (.fvar x) = .fvar x) (depth : Nat) :
    substTemplateList S (openTemplateList depth Xs templates) =
      openTemplateList depth Xs (substTemplateList S templates) := by
  cases templates with
  | nil => rfl
  | cons t ts =>
    simp only [substTemplateList, openTemplateList,
      t.substTyFvars_openTyVarsFrom_of_fixes hlc hfix depth,
      templateList_open_subst_of_fixes ts hlc hfix depth]
end

/-- Factor an ordinary annotation check against the transformed source. Only
raw-source allocation bounds and independent target protection are required. -/

theorem BindingAnn.substTyFvars_openTyVarsFrom_of_fixes (ann : BindingAnn) {subst : Subst} {Xs : List Nat}
    (hlc : ∀ pair ∈ subst, pair.2.IsLC) (hfix : ∀ x ∈ Xs, subst.onTy (.fvar x) = .fvar x) (d : Nat) :
    (ann.openTyVarsFrom d Xs).substTyFvars subst = (ann.substTyFvars subst).openTyVarsFrom d Xs := by
  cases ann with
  | absent => rfl
  | complete scheme =>
      exact congrArg (fun t => BindingAnn.complete ⟨scheme.paramCount, t⟩)
        (Subst.onTy_openVarsFrom_of_fixes hlc hfix scheme.body (d + scheme.paramCount))
  | template t => exact congrArg BindingAnn.template (t.substTyFvars_openTyVarsFrom_of_fixes hlc hfix d)
  | partialForall n t =>
      exact congrArg (BindingAnn.partialForall n) (t.substTyFvars_openTyVarsFrom_of_fixes hlc hfix (d + n))

mutual
/-- Source substitution commutes with opening through nested written signature
binders. LC ranges need not avoid the opened names. -/
theorem InferInput.substTyFvars_openTyVarsFrom_of_fixes (input : InferInput) {subst : Subst} {Xs : List Nat}
    (hlc : ∀ pair ∈ subst, pair.2.IsLC) (hfix : ∀ x ∈ Xs, subst.onTy (.fvar x) = .fvar x) (d : Nat) :
    (input.openTyVarsFrom d Xs).substTyFvars subst = (input.substTyFvars subst).openTyVarsFrom d Xs := by
  cases input with
  | primLit | primBinOp | var | ctor => rfl
  | lambda ann body =>
      simp only [InferInput.openTyVarsFrom, InferInput.substTyFvars,
        body.substTyFvars_openTyVarsFrom_of_fixes hlc hfix d]
      congr 1
      cases ann with
      | none => rfl
      | some template => exact congrArg some (template.substTyFvars_openTyVarsFrom_of_fixes hlc hfix d)
  | app f a => simp only [InferInput.openTyVarsFrom, InferInput.substTyFvars,
      f.substTyFvars_openTyVarsFrom_of_fixes hlc hfix d, a.substTyFvars_openTyVarsFrom_of_fixes hlc hfix d]
  | letIn ann rhs body => simp only [InferInput.openTyVarsFrom, InferInput.substTyFvars,
      BindingAnn.paramCount_substTyFvars, ann.substTyFvars_openTyVarsFrom_of_fixes hlc hfix d,
      rhs.substTyFvars_openTyVarsFrom_of_fixes hlc hfix (d + ann.paramCount),
      body.substTyFvars_openTyVarsFrom_of_fixes hlc hfix d]
  | match_ scrut branches => simp only [InferInput.openTyVarsFrom, InferInput.substTyFvars,
      scrut.substTyFvars_openTyVarsFrom_of_fixes hlc hfix d,
      substInputBranches_openInputBranches_of_fixes branches hlc hfix d]
  | letRec anns bindings body =>
      simp only [InferInput.openTyVarsFrom, InferInput.substTyFvars,
        body.substTyFvars_openTyVarsFrom_of_fixes hlc hfix d,
        substInputBindings_openInputBindings_of_fixes bindings anns hlc hfix d, List.map_map]
      congr 1
      apply List.map_congr_left
      intro ann _
      exact ann.substTyFvars_openTyVarsFrom_of_fixes hlc hfix d
termination_by sizeOf input

theorem substInputBranches_openInputBranches_of_fixes (branches : List (MatchPattern × InferInput)) {subst : Subst} {Xs : List Nat}
    (hlc : ∀ pair ∈ subst, pair.2.IsLC) (hfix : ∀ x ∈ Xs, subst.onTy (.fvar x) = .fvar x) (d : Nat) :
    substInputBranches subst (openInputBranches d Xs branches) = openInputBranches d Xs (substInputBranches subst branches) := by
  cases branches with
  | nil => rfl
  | cons pair rest =>
      rcases pair with ⟨pat, body⟩
      simp only [openInputBranches, substInputBranches, body.substTyFvars_openTyVarsFrom_of_fixes hlc hfix d,
        substInputBranches_openInputBranches_of_fixes rest hlc hfix d]
termination_by sizeOf branches

theorem substInputBindings_openInputBindings_of_fixes (bindings : List InferInput) (anns : List BindingAnn)
    {subst : Subst} {Xs : List Nat}
    (hlc : ∀ pair ∈ subst, pair.2.IsLC) (hfix : ∀ x ∈ Xs, subst.onTy (.fvar x) = .fvar x) (d : Nat) :
    substInputBindings subst (openInputBindings d Xs anns bindings) =
      openInputBindings d Xs (anns.map (BindingAnn.substTyFvars subst)) (substInputBindings subst bindings) := by
  cases bindings with
  | nil => rfl
  | cons body rest =>
      cases anns with
      | nil => simp only [openInputBindings, substInputBindings, List.map_nil,
          body.substTyFvars_openTyVarsFrom_of_fixes hlc hfix d,
          substInputBindings_openInputBindings_of_fixes rest [] hlc hfix d]
      | cons ann anns => simp only [openInputBindings, substInputBindings, List.map_cons,
          BindingAnn.paramCount_substTyFvars, body.substTyFvars_openTyVarsFrom_of_fixes hlc hfix (d + ann.paramCount),
          substInputBindings_openInputBindings_of_fixes rest anns hlc hfix d]
termination_by sizeOf bindings
end

theorem InferInput.substTyFvars_openTyVars_of_fixes (input : InferInput) {subst : Subst} {Xs : List Nat}
    (hlc : ∀ pair ∈ subst, pair.2.IsLC) (hfix : ∀ x ∈ Xs, subst.onTy (.fvar x) = .fvar x) :
    (input.openTyVars Xs).substTyFvars subst = (input.substTyFvars subst).openTyVars Xs :=
  input.substTyFvars_openTyVarsFrom_of_fixes hlc hfix 0





mutual
theorem TyTemplate.toCore_rigidVars {template : TyTemplate} {ty : Ty}
    (h : template.toCore = some ty) (v : Nat) : v ∈ template.rigidVars ↔ v ∈ ty.freeVars := by
  cases template with
  | fixed => cases h; rfl
  | hole => cases h
  | arrow a b =>
    simp only [TyTemplate.toCore, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨ta, ha, tb, hb, rfl⟩ := h
    simp only [TyTemplate.rigidVars, Ty.freeVars, List.mem_append, List.mem_dedup,
      TyTemplate.toCore_rigidVars ha, TyTemplate.toCore_rigidVars hb]
  | custom name args =>
    simp only [TyTemplate.toCore, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨tys, ht, rfl⟩ := h
    simpa only [TyTemplate.rigidVars, Ty.freeVars, TyList.mem_freeVars_iff, List.mem_flatMap] using completeTypes_rigidVars ht v
theorem completeTypes_rigidVars {templates : List TyTemplate} {tys : List Ty}
    (h : completeTypes templates = some tys) (v : Nat) :
    v ∈ rigidVarsList templates ↔ v ∈ tys.flatMap Ty.freeVars := by
  cases templates with
  | nil => cases h; rfl
  | cons t ts =>
    simp only [completeTypes, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨ty, ht, tys, hts, rfl⟩ := h
    simp only [rigidVarsList, List.flatMap_cons, List.mem_append,
      TyTemplate.toCore_rigidVars ht, completeTypes_rigidVars hts]
end


private theorem completeLambdaAnn_rigidVars {ann : Option TyTemplate} {core : Option Ty}
    (h : completeLambdaAnn ann = some core) (v : Nat) :
    v ∈ ann.elim [] TyTemplate.rigidVars ↔ v ∈ core.elim [] Ty.freeVars := by
  cases ann with
  | none => cases h; rfl
  | some template =>
    simp only [completeLambdaAnn, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨ty, ht, rfl⟩ := h
    exact TyTemplate.toCore_rigidVars ht v

private theorem BindingAnn.toCore_rigidVars {ann : BindingAnn} {core : Option PolyTy}
    (h : ann.toCore = some core) (v : Nat) :
    v ∈ ann.rigidVars ↔ v ∈ core.elim [] (fun scheme => scheme.body.freeVars) := by
  cases ann with
  | absent => cases h; rfl
  | complete scheme => cases h; rfl
  | template _ => cases h
  | partialForall _ _ => cases h

private theorem completeAnns_rigidVars (anns : List BindingAnn) {cores : List (Option PolyTy)}
    (h : completeAnns anns = some cores) (v : Nat) :
    v ∈ anns.flatMap BindingAnn.rigidVars ↔ v ∈ Expr.tyFreeVars.AnnList.tyFreeVars cores := by
  cases anns with
  | nil => cases h; rfl
  | cons ann rest =>
    simp only [completeAnns, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨core, ha, cores, hr, rfl⟩ := h
    simp only [List.flatMap_cons, Expr.tyFreeVars.AnnList.tyFreeVars, List.mem_append,
      BindingAnn.toCore_rigidVars ha v, completeAnns_rigidVars rest hr v]

mutual
/-- Conservative embedding preserves exactly the authored free type variables,
including all complete signature binders, branches, and recursive RHSs. -/
theorem InferInput.toCore_rigidVars (input : InferInput) {core : Expr}
    (h : input.toCore = some core) (v : Nat) : v ∈ input.rigidVars ↔ v ∈ core.tyFreeVars := by
  cases input with
  | primLit p => cases h; rfl
  | primBinOp op => cases h; rfl
  | var index => cases h; rfl
  | ctor name => cases h; rfl
  | lambda ann body =>
    simp only [InferInput.toCore, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨ann', ha, body', hb, rfl⟩ := h
    simp only [InferInput.rigidVars, Expr.tyFreeVars, List.mem_append,
      completeLambdaAnn_rigidVars ha v, body.toCore_rigidVars hb v]
  | app f arg =>
    simp only [InferInput.toCore, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨f', hf, arg', ha, rfl⟩ := h
    simp only [InferInput.rigidVars, Expr.tyFreeVars, List.mem_append,
      f.toCore_rigidVars hf v, arg.toCore_rigidVars ha v]
  | letIn ann rhs body =>
    simp only [InferInput.toCore, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨ann', ha, rhs', hr, body', hb, rfl⟩ := h
    simp only [InferInput.rigidVars, Expr.tyFreeVars, List.mem_append,
      BindingAnn.toCore_rigidVars ha v, rhs.toCore_rigidVars hr v, body.toCore_rigidVars hb v]
  | match_ scrut branches =>
    simp only [InferInput.toCore, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨scrut', hs, branches', hb, rfl⟩ := h
    simp only [InferInput.rigidVars, Expr.tyFreeVars, List.mem_append,
      scrut.toCore_rigidVars hs v, completeBranches_rigidVars branches hb v]
  | letRec anns bindings body =>
    simp only [InferInput.toCore, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨anns', ha, bindings', hr, body', hb, rfl⟩ := h
    simp only [InferInput.rigidVars, Expr.tyFreeVars, List.mem_append,
      completeAnns_rigidVars anns ha v, completeBindings_rigidVars bindings hr v,
      body.toCore_rigidVars hb v]

theorem completeBranches_rigidVars (branches : List (MatchPattern × InferInput))
    {cores : List (MatchPattern × Expr)} (h : completeBranches branches = some cores) (v : Nat) :
    v ∈ rigidBranchVars branches ↔ v ∈ Expr.tyFreeVars.BranchList.tyFreeVars cores := by
  cases branches with
  | nil => cases h; rfl
  | cons head rest =>
    rcases head with ⟨pat, body⟩
    simp only [completeBranches, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨body', hb, rest', hr, rfl⟩ := h
    simp only [rigidBranchVars, Expr.tyFreeVars.BranchList.tyFreeVars, List.mem_append,
      body.toCore_rigidVars hb v, completeBranches_rigidVars rest hr v]

theorem completeBindings_rigidVars (bindings : List InferInput) {cores : List Expr}
    (h : completeBindings bindings = some cores) (v : Nat) :
    v ∈ rigidBindingVars bindings ↔ v ∈ Expr.tyFreeVars.RecGroup.tyFreeVars cores := by
  cases bindings with
  | nil => cases h; rfl
  | cons body rest =>
    simp only [completeBindings, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨body', hb, rest', hr, rfl⟩ := h
    simp only [rigidBindingVars, Expr.tyFreeVars.RecGroup.tyFreeVars, List.mem_append,
      body.toCore_rigidVars hb v, completeBindings_rigidVars rest hr v]
end


/-- A signed completion preserves the written forall prefix. Partial signatures
may additionally quantify independent inferred variables after that prefix. -/
inductive BindingAnn.SignatureFits : BindingAnn → PolyTy → List Nat → Prop
  | complete : SignatureFits (.complete scheme) scheme names
  | partialSignature {scheme : PolyTy} {template : TyTemplate} {count : Nat} {names : List Nat} :
      count ≤ scheme.paramCount →
      (template.openTyVarsFrom 0 (names.take count)).Fits (scheme.openVars names) →
      SignatureFits (.partialForall count template) scheme names

theorem BindingAnn.SignatureFits.prefix_le {ann : BindingAnn} {scheme : PolyTy} {names : List Nat}
    (h : ann.SignatureFits scheme names) : ann.paramCount ≤ scheme.paramCount := by
  cases h with
  | complete => exact Nat.le_refl _
  | partialSignature h _ => exact h

theorem BindingAnn.SignatureFits.isSignature {ann : BindingAnn} {scheme : PolyTy} {names : List Nat}
    (h : ann.SignatureFits scheme names) :
    ann.isSignature = true := by cases h <;> rfl

/-- A checked monotype is closed under the written prefix and any inferred
extra binders. Complete signatures retain their exact authored scheme. -/
inductive BindingAnn.SignatureCompletion : BindingAnn → List Nat → Ty → PolyTy → List Nat → Prop
  | complete {scheme : PolyTy} :
      names.length = scheme.paramCount → ty = scheme.openVars names →
      SignatureCompletion (.complete scheme) names ty scheme names
  | partialSignature {template : TyTemplate} {count : Nat} {written extras : List Nat} :
      written.length = count → (template.openTyVarsFrom 0 written).Fits ty →
      SignatureCompletion (.partialForall count template) written ty
        ⟨(written ++ extras).length, Ty.closeOver (written ++ extras) ty⟩ (written ++ extras)

/-- Structural branch completion preserves patterns and completes each body. -/
def BindingAnn.RecFits (ann : BindingAnn) (written : List Nat) (ty : Ty) : Prop :=
  match ann with
  | .absent => True
  | .template t => t.Fits ty
  | .partialForall count t => written.length = count ∧
      (t.openTyVarsFrom 0 written).Fits ty
  | .complete _ => False

def BindingAnn.BindingFits (ann : BindingAnn) (scheme : PolyTy) (fresh : List Nat) : Prop :=
  if ann.isSignature then ann.SignatureFits scheme fresh else ann.FitsMono (scheme.openVars fresh)


inductive CompletedBranches (J : List Nat → InferInput → Expr → Prop) :
    List Nat → List (MatchPattern × InferInput) → List (MatchPattern × Expr) → Prop
  | nil : CompletedBranches J K [] []
  | cons {source : InferInput} {output : Expr} {K : List Nat} :
      J K source output → CompletedBranches J K rest restOut →
      CompletedBranches J K ((pat, source) :: rest) ((pat, output) :: restOut)

/-- Structural annotation completion. This is distinct from input admissibility
(`InputTyping` below): it records fixed syntax, individual hole fillings, and the
type abstraction/specialization performed when an ordinary let is generalized.
Protected fixed variables cannot be substituted or captured by new binders.
Scope correctness of the resulting Core is supplied by output typing. -/
inductive AnnotationCompletion : List Nat → InferInput → Expr → Prop
  | complete : input.toCore = some core → (∀ v ∈ core.tyFreeVars, v ∈ K) → AnnotationCompletion K input core
  | lambda :
      (∀ template, ann = some template → template.Fits param) →
      (∀ template, ann = some template → ∀ v ∈ template.rigidVars, v ∈ K) →
      AnnotationCompletion K body completed →
      AnnotationCompletion K (.lambda ann body) (.lambda (ann.map fun _ => param) completed)
  | app : AnnotationCompletion K f fOut → AnnotationCompletion K arg argOut → AnnotationCompletion K (.app f arg) (.app fOut argOut)
  | letIn {M : PolyTy} {L : List Nat} :
      (∀ template, ann = .template template → ∀ v ∈ template.rigidVars, v ∈ K) →
      (∀ Xs, FreshNames L M.paramCount Xs → ann.FitsMono (M.openVars Xs)) →
      (∀ Xs, FreshNames L M.paramCount Xs → AnnotationCompletion K rhs (rhsOut.openTyVars Xs)) →
      AnnotationCompletion K body bodyOut →
      AnnotationCompletion K (.letIn ann rhs body) (.letIn (some M) rhsOut bodyOut)
  | letSignature {M : PolyTy} {L : List Nat} :
      (∀ v ∈ ann.rigidVars, v ∈ K) → (∀ v ∈ rhs.rigidVars, v ∈ K) →
      (∀ Xs, FreshNames L M.paramCount Xs → ann.SignatureFits M Xs) →
      (∀ Xs, FreshNames L M.paramCount Xs →
        AnnotationCompletion (K ++ Xs.take ann.paramCount) (rhs.openTyVars (Xs.take ann.paramCount))
          (rhsOut.openTyVars Xs)) →
      AnnotationCompletion K body bodyOut →
      AnnotationCompletion K (.letIn ann rhs body) (.letIn (some M) rhsOut bodyOut)
  | match_ : AnnotationCompletion K scrut scrutOut → CompletedBranches AnnotationCompletion K branches branchesOut →
      AnnotationCompletion K (.match_ scrut branches) (.match_ scrutOut branchesOut)

  | letRec {schemes : List PolyTy} {L : List Nat} :
    anns.length = schemes.length → bindings.length = schemes.length →
    completed.length = schemes.length →
    (∀ ann ∈ anns, ∀ v ∈ ann.rigidVars, v ∈ K) →
    (∀ rhs ∈ bindings, ∀ v ∈ rhs.rigidVars, v ∈ K) →
    (∀ (member : Nat) (ann : BindingAnn) (rhs : InferInput) (output : Expr) (scheme : PolyTy),
      anns[member]? = some ann → bindings[member]? = some rhs →
      completed[member]? = some output → schemes[member]? = some scheme →
      (∀ Xs, FreshNames L scheme.paramCount Xs → ann.BindingFits scheme Xs)) →
    (∀ (member : Nat) (ann : BindingAnn) (rhs : InferInput) (output : Expr) (scheme : PolyTy),
      anns[member]? = some ann → bindings[member]? = some rhs →
      completed[member]? = some output → schemes[member]? = some scheme →
      (∀ Xs, FreshNames L scheme.paramCount Xs →
        AnnotationCompletion (K ++ Xs.take ann.paramCount) (rhs.openTyVars (Xs.take ann.paramCount))
          (output.openTyVars Xs))) →
    AnnotationCompletion K body bodyOut →
    AnnotationCompletion K (.letRec anns bindings body) (.letRec (schemes.map some) completed bodyOut)

/-- Independent branch semantics reuse the ordinary constructor specification;
the body relation is a parameter, with no inference state or substitution. -/
inductive BranchTyping (J : List Nat → Ctx → InferInput → Ty → Prop) :
    List Nat → Ctx → (MatchPattern × InferInput) → Ty → Ty → Prop
  | named : BranchCtorSpec ctx.ctors name count scrutTy ctor args fields →
      J K { ctx with env := fields.map PolyTy.mkTrivial ++ ctx.env } body resultTy →
      BranchTyping J K ctx (.named name count, body) scrutTy resultTy
  | wildcard : J K ctx body resultTy → BranchTyping J K ctx (.wildcard, body) scrutTy resultTy

/-- Independent input typing. `K` scopes authored rigid annotation variables;
context monotypes can still contain flexible variables. Ordinary lets generalize
cofinally. Signed lets preserve the written forall prefix and check each fresh
opening, with any additional hole variables quantified after that prefix.

Whole completed subtrees retain the existing rules through conservative Core
embedding. Partial recursive signatures remain monomorphic within their
component; only complete written schemes permit polymorphic recursive use.
-/
inductive InputTyping : List Nat → Ctx → InferInput → Ty → Prop
  /-- Existing complete Core programs retain their existing declarative meaning.
  The checked embedding rejects every partial annotation mode. -/
  | complete : input.toCore = some core →
      (∀ v ∈ core.tyFreeVars, v ∈ K) → TypeOfHM ctx core ty → InputTyping K ctx input ty
  | primLit : TypeOfHM ctx (.primLit p) ty → InputTyping K ctx (.primLit p) ty
  | primBinOp : TypeOfHM ctx (.primBinOp op) ty → InputTyping K ctx (.primBinOp op) ty
  | lambda :
      paramTy.IsLC →
      (∀ template, ann = some template → template.Fits paramTy) →
      (∀ template, ann = some template → ∀ v ∈ template.rigidVars, v ∈ K) →
      InputTyping K { ctx with env := PolyTy.mkTrivial paramTy :: ctx.env } body bodyTy →
      InputTyping K ctx (.lambda ann body) (.arrow paramTy bodyTy)
  | app : InputTyping K ctx f (.arrow argTy retTy) → InputTyping K ctx arg argTy →
      InputTyping K ctx (.app f arg) retTy
  | letIn {M : PolyTy} {L : List Nat} :
      M.WF →
      (∀ template, ann = .template template → ∀ v ∈ template.rigidVars, v ∈ K) →
      (∀ Xs, FreshNames L M.paramCount Xs → ann.FitsMono (M.openVars Xs)) →
      (∀ Xs, FreshNames L M.paramCount Xs → InputTyping K ctx rhs (M.openVars Xs)) →
      InputTyping K { ctx with env := M :: ctx.env } body bodyTy →
      InputTyping K ctx (.letIn ann rhs body) bodyTy
  | letSignature {M : PolyTy} {L : List Nat} :
      M.WF → (∀ v ∈ ann.rigidVars, v ∈ K) → (∀ v ∈ rhs.rigidVars, v ∈ K) →
      (∀ Xs, FreshNames L M.paramCount Xs → ann.SignatureFits M Xs) →
      (∀ Xs, FreshNames L M.paramCount Xs →
        InputTyping (K ++ Xs.take ann.paramCount) ctx (rhs.openTyVars (Xs.take ann.paramCount)) (M.openVars Xs)) →
      InputTyping K { ctx with env := M :: ctx.env } body bodyTy →
      InputTyping K ctx (.letIn ann rhs body) bodyTy
  | var : ctx.env[index]? = some scheme →
      (∀ arg ∈ args, arg.IsLC) → scheme.InstantiatesTo args ty →
      InputTyping K ctx (.var index) ty
  | ctor : LookupList.get? ctx.ctors name = some ctor →
      (∀ arg ∈ args, arg.IsLC) → ctor.toTy.InstantiatesTo args ty →
      InputTyping K ctx (.ctor name) ty
  | match_ : InputTyping K ctx scrut scrutTy → branches ≠ [] →
      (∀ branch ∈ branches, BranchTyping InputTyping K ctx branch scrutTy resultTy) →
      InputTyping K ctx (.match_ scrut branches) resultTy
  | letRec {specs : List RecSpec} {groups : List (List Nat)} {prefixes : List (List Nat)}
      {G L : List Nat} :
    RecGroups.ValidResidualGroups (anns.map BindingAnn.recModeAnn) (bindings.map InferInput.erase) groups →
    RecSpecs.WF (anns.map BindingAnn.recModeAnn) (bindings.map InferInput.erase) specs G →
    RecPrefixesWF anns specs prefixes G →
    (∀ name ∈ G, name ∉ ctx.env.freeVars ++ K) →
    (∀ ann ∈ anns, ∀ v ∈ ann.rigidVars, v ∈ K) →
    (∀ rhs ∈ bindings, ∀ v ∈ rhs.rigidVars, v ∈ K) →
    (∀ (stage : Nat) (component : List Nat), groups[stage]? = some component →
      ∀ Xs, FreshNames (G ++ L) G.length Xs →
      ∀ (member : Nat), member ∈ component → ∀ (rhs : InferInput) (ann : BindingAnn) (names : List Nat) (ty : Ty),
        bindings[member]? = some rhs → anns[member]? = some ann →
        prefixes[member]? = some names → specs[member]? = some (.mono ty) →
        ann.RecFits (recRenameNames G Xs names) (Ty.renameG G Xs ty)) →
    (∀ (stage : Nat) (component : List Nat), groups[stage]? = some component →
      ∀ Xs, FreshNames (G ++ L) G.length Xs →
      ∀ (member : Nat), member ∈ component → ∀ (rhs : InferInput) (ann : BindingAnn) (names : List Nat) (ty : Ty),
        bindings[member]? = some rhs → anns[member]? = some ann →
        prefixes[member]? = some names → specs[member]? = some (.mono ty) →
        InputTyping (K ++ Xs) (recStageCtx ctx specs prefixes (groups.take stage).flatten G Xs)
          (rhs.openTyVars (recRenameNames G Xs names)) (Ty.renameG G Xs ty)) →
    (∀ (member : Nat) (rhs : InferInput) (scheme : PolyTy), bindings[member]? = some rhs →
      specs[member]? = some (.poly scheme) →
      ∀ Ys, FreshNames L scheme.paramCount Ys →
        InputTyping (K ++ Ys) (recBodyCtx ctx specs prefixes G) (rhs.openTyVars Ys) (scheme.openVars Ys)) →
    InputTyping K (recBodyCtx ctx specs prefixes G) body resultTy →
    InputTyping K ctx (.letRec anns bindings body) resultTy



private theorem erasedBranches_eq_map (branches : List (MatchPattern × InferInput)) :
    eraseBranches branches = branches.map (fun branch => (branch.1, branch.2.erase)) := by
  induction branches with
  | nil => rfl
  | cons head rest ih => rcases head with ⟨p, b⟩; simp only [eraseBranches, List.map_cons, ih]

private theorem eraseBindings_eq_map_source (bindings : List InferInput) :
    eraseBindings bindings = bindings.map InferInput.erase := by
  induction bindings with
  | nil => rfl
  | cons rhs rest ih => simp only [eraseBindings, List.map_cons, ih]

/-- The input specification has the ordinary HM runtime meaning independently
of elaboration. Annotation matching restricts this meaning; it never grants a
new runtime typing rule. -/
theorem InputTyping.erase (h : InputTyping K ctx input ty) : RuntimeTyping.RunWT ctx input.erase ty := by
  induction h using InputTyping.rec
      (motive_2 := fun K ctx branch scrutTy resultTy _ =>
        RuntimeTyping.RunWTMatchBranch ctx (branch.1, branch.2.erase) scrutTy resultTy) with
  | complete hemb _ htyping =>
      rw [← InferInput.toCore_erase _ hemb]
      exact htyping.erase_preserves_typing
  | primLit h => simpa only [Expr.erase] using h.erase_preserves_typing
  | primBinOp h => simpa only [Expr.erase] using h.erase_preserves_typing
  | lambda hlc _ _ _ ih =>
      exact .lambda hlc ih
  | app _ _ ihf ihx => exact .app ihf ihx
  | letIn hwf _ _ _ _ ihrhs ihbody =>
      exact .letIn hwf ihrhs ihbody
  | @letSignature K ctx body bodyTy ann rhs scheme avoid hwf _ _ _ _ _ ihrhs ihbody =>
      refine .letIn (avoid := avoid) hwf ?_ ihbody
      intro Xs hf
      simpa only [InferInput.erase_openTyVars] using ihrhs Xs hf
  | var hlook hlc hinst => exact .var hlook hlc hinst
  | ctor hlook hlc hinst => exact .ctor hlook hlc hinst

  | match_ _ hne _ ihscrut ihbranches =>
    expose_names
    simp only [InferInput.erase]
    rw [erasedBranches_eq_map]
    refine .match_ ihscrut ?_ ?_
    · intro hempty
      exact hne (List.map_eq_nil_iff.mp hempty)
    · intro branch hb
      obtain ⟨source, hsource, rfl⟩ := List.mem_map.mp hb
      exact ihbranches source hsource
  | letRec hgroups hwf hp _ _ _ _ _ _ _ ihmono ihpoly ihbody =>
    expose_names
    have hannsLen : anns.length = specs.length := by
      have hh := congrArg List.length hwf.anns_eq
      simpa using hh.symm
    have hbodyGen := bodySchemes_generalize_recCompleted hwf hp
    simp only [InferInput.erase, eraseBindings_eq_map_source]
    rw [show bindings.map (fun _ => none) = (bindings.map InferInput.erase).map (fun _ => none) by
      simp only [List.map_map, Function.comp_def]]
    refine RuntimeTyping.RunWT.letRec (specs := specs) (G := G) (avoid := G ++ L)
      ⟨hwf.length, hwf.nodup, hwf.mono_lc, hwf.poly_wf⟩ ?_ ?_ ?_
    · intro Xs hf pair hpair ty heq
      obtain ⟨rhs, spec, _, hpair0, rfl⟩ := List.mem_zip_map_left hpair
      obtain ⟨member, hzip⟩ := List.mem_iff_getElem?.mp hpair0
      obtain ⟨hrhs, hspec⟩ := List.getElem?_zip_eq_some.mp hzip
      rw [heq] at hspec
      have hi : member < specs.length := (List.getElem?_eq_some_iff.mp hspec).1
      have hia : member < anns.length := by omega
      have hip : member < prefixes.length := by rw [hp.length]; exact hi
      have hunsigned : RecGroups.UnsignedAt (anns.map BindingAnn.recModeAnn) member := by
        simp only [RecGroups.UnsignedAt, ← hwf.anns_eq, List.getElem?_map, hspec,
          Option.map_some, RecSpec.ann]
      have hcovered := (hgroups.covers_unsigned member (by simpa only [List.length_map] using
        (List.getElem?_eq_some_iff.mp hrhs).1)).2 hunsigned
      obtain ⟨component, hc, hm⟩ := List.mem_flatten.mp hcovered
      obtain ⟨stage, hstage⟩ := List.mem_iff_getElem?.mp hc
      have ht := ihmono stage component hstage Xs hf member hm rhs anns[member] prefixes[member] ty
        hrhs (List.getElem?_eq_getElem hia) (List.getElem?_eq_getElem hip) hspec
      simp only [InferInput.erase_openTyVars] at ht
      have hh := RuntimeTyping.RunWT.weaken_schemes
        (bodySchemes_generalize_recStage (done := (groups.take stage).flatten) (Xs := Xs) hwf hp) ht
      exact hh
    · intro pair hpair scheme heq Ys hy
      obtain ⟨rhs, spec, _, hpair0, rfl⟩ := List.mem_zip_map_left hpair
      obtain ⟨member, hzip⟩ := List.mem_iff_getElem?.mp hpair0
      obtain ⟨hrhs, hspec⟩ := List.getElem?_zip_eq_some.mp hzip
      rw [heq] at hspec
      have hf : FreshNames L scheme.paramCount Ys :=
        ⟨hy.length, hy.nodup, fun y hy' hl => hy.avoid y hy' (List.mem_append_right _ hl)⟩
      have ht := ihpoly member rhs scheme hrhs hspec Ys hf
      simp only [InferInput.erase_openTyVars] at ht
      exact RuntimeTyping.RunWT.weaken_schemes hbodyGen ht
    · exact RuntimeTyping.RunWT.weaken_schemes hbodyGen ihbody
  | named hspec _ ihbody => exact .mk hspec ihbody
  | wildcard _ ihbody => exact .wildcard ihbody

/-- Independently typed branch bodies retain ordinary erased branch semantics. -/
theorem BranchTyping.erase (h : BranchTyping InputTyping K ctx branch scrutTy resultTy) :
    RuntimeTyping.RunWTMatchBranch ctx (branch.1, branch.2.erase) scrutTy resultTy := by
  cases h with
  | named hspec hbody => exact .mk hspec hbody.erase
  | wildcard hbody => exact .wildcard hbody.erase

mutual
/-- Simultaneously transform the authored template and its instance. -/
theorem TyTemplate.Fits.substTyFvars {template : TyTemplate} {ty : Ty}
    (h : template.Fits ty) (subst : Subst) :
    (template.substTyFvars subst).Fits (subst.onTy ty) := by
  cases h with
  | fixed => exact .fixed
  | hole => exact .hole
  | arrow ha hb =>
      simpa only [TyTemplate.substTyFvars, Subst.onTy_arrow] using
        (TyTemplate.Fits.arrow (ha.substTyFvars subst) (hb.substTyFvars subst))
  | custom hargs =>
      simpa only [TyTemplate.substTyFvars, Subst.onTy_customTy] using
        (TyTemplate.Fits.custom (fitsList_substTyFvars hargs subst))
theorem fitsList_substTyFvars {templates : List TyTemplate} {tys : List Ty}
    (h : List.Forall₂ TyTemplate.Fits templates tys) (subst : Subst) :
    List.Forall₂ TyTemplate.Fits (substTemplateList subst templates) (tys.map subst.onTy) := by
  cases h with
  | nil => exact .nil
  | cons hh ht => exact .cons (hh.substTyFvars subst) (fitsList_substTyFvars ht subst)
end

theorem TyTemplate.Fits.onSubst_fixes {K : List Nat} {template : TyTemplate} {ty : Ty}
    (h : template.Fits ty) (hfixed : ∀ v ∈ template.rigidVars, v ∈ K)
    {subst : Subst} (hsubst : ∀ v ∈ K, subst.onTy (.fvar v) = .fvar v) :
    template.Fits (subst.onTy ty) := by
  have ht := h.substTyFvars subst
  rwa [template.substTyFvars_eq_self_of_fixes (fun v hv => hsubst v (hfixed v hv))] at ht

theorem BindingAnn.FitsMono.onSubst_fixes {K : List Nat} {ann : BindingAnn} {ty : Ty}
    (h : ann.FitsMono ty)
    (hfixed : ∀ template, ann = .template template → ∀ v ∈ template.rigidVars, v ∈ K)
    {subst : Subst} (hsubst : ∀ v ∈ K, subst.onTy (.fvar v) = .fvar v) :
    ann.FitsMono (subst.onTy ty) := by
  cases ann with
  | absent => trivial
  | template template => exact TyTemplate.Fits.onSubst_fixes h (hfixed template rfl) hsubst
  | complete => exact False.elim h
  | partialForall => exact False.elim h

theorem TyTemplate.Fits.onSubst {K : List Nat} {template : TyTemplate} {ty : Ty}
    (h : template.Fits ty) (hfixed : ∀ v ∈ template.rigidVars, v ∈ K)
    {subst : Subst} (hsubst : ∀ pair ∈ subst, pair.1 ∉ K) :
    template.Fits (subst.onTy ty) :=
  h.onSubst_fixes hfixed (Subst.fixes_of_dom_avoids hsubst)

theorem BindingAnn.FitsMono.onSubst {K : List Nat} {ann : BindingAnn} {ty : Ty}
    (h : ann.FitsMono ty)
    (hfixed : ∀ template, ann = .template template → ∀ v ∈ template.rigidVars, v ∈ K)
    {subst : Subst} (hsubst : ∀ pair ∈ subst, pair.1 ∉ K) :
    ann.FitsMono (subst.onTy ty) :=
  h.onSubst_fixes hfixed (Subst.fixes_of_dom_avoids hsubst)

/-- Constructor branch witnesses transport with LC substitutions; constructor
field declarations themselves are closed and therefore unchanged. -/
theorem _root_.BranchCtorSpec.onSubst {ctors : CtorEnv} {name : CtorName} {count : Nat}
    {scrutTy : Ty} {ctor : Ctor} {args fields : List Ty}
    (h : BranchCtorSpec ctors name count scrutTy ctor args fields)
    (subst : Subst) (hlc : ∀ pair ∈ subst, pair.2.IsLC) :
    BranchCtorSpec ctors name count (subst.onTy scrutTy) ctor
      (args.map subst.onTy) (fields.map subst.onTy) := by
  induction subst generalizing scrutTy args fields with
  | nil =>
    change BranchCtorSpec ctors name count scrutTy ctor (args.map id) (fields.map id)
    simpa only [List.map_id] using h
  | cons pair rest ih =>
    rcases pair with ⟨v, replacement⟩
    have hrepl := hlc (v, replacement) List.mem_cons_self
    have hfields := InstantiatesBy.forall2_substFvar (Z := v) (U := replacement) hrepl h.fields
    have hcontents : ctor.contents.map (Ty.substFvar v replacement) = ctor.contents := by
      apply List.map_eq_self_of_forall_eq_id
      intro field hf
      exact Ty.substFvar_fresh ((ctor.closed field hf).not_mem_freeVars v)
    rw [hcontents] at hfields
    have hstep : BranchCtorSpec ctors name count (Ty.substFvar v replacement scrutTy) ctor
        (args.map (Ty.substFvar v replacement)) (fields.map (Ty.substFvar v replacement)) :=
      ⟨h.lookup, by rw [h.scrut_eq]; simp only [Ty.substFvar, TyList.substFvar_eq_map],
        by simpa only [List.length_map] using h.arity, h.bind_count, hfields⟩
    have ht := ih hstep (fun pair hp => hlc pair (List.mem_cons_of_mem _ hp))
    simpa only [List.map_map, Function.comp_def, Subst.onTy, Ty.substFvars] using ht





mutual
/-- Each authored free variable after substitution comes from one original
fixed leaf variable's image; anonymous holes contribute no variables. -/
theorem TyTemplate.rigidVars_substTyFvars {template : TyTemplate} {subst : Subst} {v : Nat}
    (h : v ∈ (template.substTyFvars subst).rigidVars) :
    ∃ k ∈ template.rigidVars, v ∈ (subst.onTy (.fvar k)).freeVars := by
  cases template with
  | fixed ty => exact Ty.mem_freeVars_substFvars_image.mp h
  | hole => cases h
  | arrow a b =>
      rcases List.mem_append.mp h with ha | hb
      · obtain ⟨k, hk, hv⟩ := a.rigidVars_substTyFvars ha
        exact ⟨k, List.mem_append_left _ hk, hv⟩
      · obtain ⟨k, hk, hv⟩ := b.rigidVars_substTyFvars hb
        exact ⟨k, List.mem_append_right _ hk, hv⟩
  | custom name args => exact rigidVarsList_substTyFvars h
theorem rigidVarsList_substTyFvars {templates : List TyTemplate} {subst : Subst} {v : Nat}
    (h : v ∈ rigidVarsList (substTemplateList subst templates)) :
    ∃ k ∈ rigidVarsList templates, v ∈ (subst.onTy (.fvar k)).freeVars := by
  cases templates with
  | nil => cases h
  | cons t ts =>
      rcases List.mem_append.mp h with ht | hts
      · obtain ⟨k, hk, hv⟩ := t.rigidVars_substTyFvars ht
        exact ⟨k, List.mem_append_left _ hk, hv⟩
      · obtain ⟨k, hk, hv⟩ := rigidVarsList_substTyFvars hts
        exact ⟨k, List.mem_append_right _ hk, hv⟩
end

theorem BindingAnn.rigidVars_substTyFvars {ann : BindingAnn} {subst : Subst} {v : Nat}
    (h : v ∈ (ann.substTyFvars subst).rigidVars) :
    ∃ k ∈ ann.rigidVars, v ∈ (subst.onTy (.fvar k)).freeVars := by
  cases ann with
  | absent => cases h
  | complete scheme => exact Ty.mem_freeVars_substFvars_image.mp h
  | template t => exact t.rigidVars_substTyFvars h
  | partialForall n t => exact t.rigidVars_substTyFvars h


private theorem rigidAnns_substTyFvars {anns : List BindingAnn} {subst : Subst} {v : Nat}
    (h : v ∈ (anns.map (BindingAnn.substTyFvars subst)).flatMap BindingAnn.rigidVars) :
    ∃ k ∈ anns.flatMap BindingAnn.rigidVars, v ∈ (subst.onTy (.fvar k)).freeVars := by
  obtain ⟨ann', hann', hv⟩ := List.mem_flatMap.mp h
  obtain ⟨ann, hann, rfl⟩ := List.mem_map.mp hann'
  obtain ⟨k, hk, hv⟩ := ann.rigidVars_substTyFvars hv
  exact ⟨k, List.mem_flatMap.mpr ⟨ann, hann, hk⟩, hv⟩

mutual
/-- Every authored variable after source substitution originates in the image
of one authored variable before substitution. -/
theorem InferInput.rigidVars_substTyFvars {input : InferInput} {subst : Subst} {v : Nat}
    (h : v ∈ (input.substTyFvars subst).rigidVars) :
    ∃ k ∈ input.rigidVars, v ∈ (subst.onTy (.fvar k)).freeVars := by
  cases input with
  | primLit | primBinOp | var | ctor => cases h
  | lambda ann body =>
      rcases List.mem_append.mp h with ha | hb
      · cases ann with
        | none => cases ha
        | some template =>
            obtain ⟨k, hk, hv⟩ := template.rigidVars_substTyFvars ha
            exact ⟨k, List.mem_append_left _ hk, hv⟩
      · obtain ⟨k, hk, hv⟩ := body.rigidVars_substTyFvars hb
        exact ⟨k, List.mem_append_right _ hk, hv⟩
  | app f a =>
      rcases List.mem_append.mp h with hf | ha
      · obtain ⟨k, hk, hv⟩ := f.rigidVars_substTyFvars hf
        exact ⟨k, List.mem_append_left _ hk, hv⟩
      · obtain ⟨k, hk, hv⟩ := a.rigidVars_substTyFvars ha
        exact ⟨k, List.mem_append_right _ hk, hv⟩
  | letIn ann rhs body =>
      rcases List.mem_append.mp h with hprefix | hb
      · rcases List.mem_append.mp hprefix with ha | hr
        · obtain ⟨k, hk, hv⟩ := ann.rigidVars_substTyFvars ha
          exact ⟨k, List.mem_append_left _ (List.mem_append_left _ hk), hv⟩
        · obtain ⟨k, hk, hv⟩ := rhs.rigidVars_substTyFvars hr
          exact ⟨k, List.mem_append_left _ (List.mem_append_right _ hk), hv⟩
      · obtain ⟨k, hk, hv⟩ := body.rigidVars_substTyFvars hb
        exact ⟨k, List.mem_append_right _ hk, hv⟩
  | match_ scrut branches =>
      rcases List.mem_append.mp h with hs | hbs
      · obtain ⟨k, hk, hv⟩ := scrut.rigidVars_substTyFvars hs
        exact ⟨k, List.mem_append_left _ hk, hv⟩
      · obtain ⟨k, hk, hv⟩ := rigidBranchVars_substTyFvars hbs
        exact ⟨k, List.mem_append_right _ hk, hv⟩
  | letRec anns bindings body =>
      rcases List.mem_append.mp h with hprefix | hb
      · rcases List.mem_append.mp hprefix with ha | hbs
        · obtain ⟨k, hk, hv⟩ := rigidAnns_substTyFvars ha
          exact ⟨k, List.mem_append_left _ (List.mem_append_left _ hk), hv⟩
        · obtain ⟨k, hk, hv⟩ := rigidBindingVars_substTyFvars hbs
          exact ⟨k, List.mem_append_left _ (List.mem_append_right _ hk), hv⟩
      · obtain ⟨k, hk, hv⟩ := body.rigidVars_substTyFvars hb
        exact ⟨k, List.mem_append_right _ hk, hv⟩
termination_by sizeOf input

theorem rigidBranchVars_substTyFvars {branches : List (MatchPattern × InferInput)} {subst : Subst} {v : Nat}
    (h : v ∈ rigidBranchVars (substInputBranches subst branches)) :
    ∃ k ∈ rigidBranchVars branches, v ∈ (subst.onTy (.fvar k)).freeVars := by
  cases branches with
  | nil => cases h
  | cons pair rest =>
      rcases List.mem_append.mp h with hb | hr
      · obtain ⟨k, hk, hv⟩ := pair.2.rigidVars_substTyFvars hb
        exact ⟨k, List.mem_append_left _ hk, hv⟩
      · obtain ⟨k, hk, hv⟩ := rigidBranchVars_substTyFvars hr
        exact ⟨k, List.mem_append_right _ hk, hv⟩
termination_by sizeOf branches
decreasing_by all_goals (subst_vars; cases pair; simp_wf <;> omega)

theorem rigidBindingVars_substTyFvars {bindings : List InferInput} {subst : Subst} {v : Nat}
    (h : v ∈ rigidBindingVars (substInputBindings subst bindings)) :
    ∃ k ∈ rigidBindingVars bindings, v ∈ (subst.onTy (.fvar k)).freeVars := by
  cases bindings with
  | nil => cases h
  | cons body rest =>
      rcases List.mem_append.mp h with hb | hr
      · obtain ⟨k, hk, hv⟩ := body.rigidVars_substTyFvars hb
        exact ⟨k, List.mem_append_left _ hk, hv⟩
      · obtain ⟨k, hk, hv⟩ := rigidBindingVars_substTyFvars hr
        exact ⟨k, List.mem_append_right _ hk, hv⟩
termination_by sizeOf bindings
end


private theorem fitsMono_sourceSubst {ann : BindingAnn} {ty : Ty}
    (h : ann.FitsMono ty) (subst : Subst) :
    (ann.substTyFvars subst).FitsMono (subst.onTy ty) := by
  cases ann with
  | absent => trivial
  | template t => exact h.substTyFvars subst
  | complete _ => cases h
  | partialForall _ _ => cases h

private theorem template_scope_sourceSubst {K K' : List Nat} {template : TyTemplate}
    {subst : Subst} (hrigid : ∀ v ∈ template.rigidVars, v ∈ K)
    (hscope : ∀ k ∈ K, ∀ v ∈ (subst.onTy (.fvar k)).freeVars, v ∈ K') :
    ∀ v ∈ (template.substTyFvars subst).rigidVars, v ∈ K' := by
  intro v hv
  obtain ⟨k, hk, hv⟩ := template.rigidVars_substTyFvars hv
  exact hscope k (hrigid k hk) v hv

theorem BindingAnn.SignatureFits.onSubst_source {ann : BindingAnn} {scheme : PolyTy} {names : List Nat}
    (h : ann.SignatureFits scheme names) (subst : Subst)
    (hlc : ∀ pair ∈ subst, pair.2.IsLC) (hfresh : ∀ pair ∈ subst, pair.1 ∉ names) :
    (ann.substTyFvars subst).SignatureFits (subst.onPolyTy scheme) names := by
  cases h with
  | complete => exact .complete
  | @partialSignature scheme template count names hle hfit =>
      refine .partialSignature hle ?_
      have hsmall : ∀ pair ∈ subst, pair.1 ∉ names.take count :=
        fun pair hp hv => hfresh pair hp (List.mem_of_mem_take hv)
      have ht := hfit.substTyFvars subst
      simpa only [TyTemplate.substTyFvars_openTyVarsFrom _ hlc hsmall 0,
        PolyTy.openVars, Subst.onPolyTy, Subst.onTy_openVars hlc hfresh] using ht

private theorem substInputBindings_eq_map_source (S : Subst) (bindings : List InferInput) :
    substInputBindings S bindings = bindings.map (InferInput.substTyFvars S) := by
  induction bindings with
  | nil => rfl
  | cons rhs rest ih => simp only [substInputBindings, List.map_cons, ih]

private theorem recRenameNames_getD_source (G W : List Nat) (prefixes : List (List Nat)) (i : Nat) :
    (prefixes.map (recRenameNames G W))[i]?.getD [] = recRenameNames G W (prefixes[i]?.getD []) := by
  rw [List.getElem?_map]
  cases prefixes[i]? <;> rfl

theorem BindingAnn.RecFits.onSubst_source {ann : BindingAnn} {names : List Nat} {ty : Ty}
    (h : ann.RecFits names ty) (S : Subst) (hlc : ∀ p ∈ S, p.2.IsLC)
    (hfix : ∀ name ∈ names, S.onTy (.fvar name) = .fvar name) :
    (ann.substTyFvars S).RecFits names (S.onTy ty) := by
  cases ann with
  | absent => trivial
  | complete scheme => exact False.elim h
  | template t => exact h.substTyFvars S
  | partialForall n t =>
    refine ⟨h.1, ?_⟩
    have hh := h.2.substTyFvars S
    rw [TyTemplate.substTyFvars_openTyVarsFrom_of_fixes t hlc hfix] at hh
    exact hh

/-- Source-transforming substitution transports the independent judgment when
its authored variable images are scoped by the destination protected set. -/
theorem InputTyping.onSubst_source {K K' : List Nat} {ctx : Ctx} {input : InferInput} {ty : Ty}
    (h : InputTyping K ctx input ty) (subst : Subst)
    (hlc : ∀ pair ∈ subst, pair.2.IsLC)
    (hscope : ∀ k ∈ K, ∀ v ∈ (subst.onTy (.fvar k)).freeVars, v ∈ K') :
    InputTyping K' (subst.onCtx ctx) (input.substTyFvars subst) (subst.onTy ty) := by
  induction h using InputTyping.rec
      (motive_2 := fun K ctx branch scrutTy resultTy _ => ∀ {K' : List Nat},
        (∀ k ∈ K, ∀ v ∈ (subst.onTy (.fvar k)).freeVars, v ∈ K') →
          BranchTyping InputTyping K' (subst.onCtx ctx) (branch.1, branch.2.substTyFvars subst)
            (subst.onTy scrutTy) (subst.onTy resultTy)) generalizing K' with
  | complete hemb hrigid htyping =>
    refine .complete (InferInput.toCore_substTyFvars _ hemb subst) ?_ (htyping.onSubst subst hlc)
    intro v hv
    obtain ⟨k, hk, hv⟩ := Expr.mem_tyFreeVars_substTyFvars_image hv
    exact hscope k (hrigid k hk) v hv
  | primLit htyping =>
    exact .primLit (TypeOfHM.onSubst_fixed subst hlc
      (Expr.substTyFvars_eq_self_of_tyFreeVars_nil _ rfl) htyping)
  | primBinOp htyping =>
    exact .primBinOp (TypeOfHM.onSubst_fixed subst hlc
      (Expr.substTyFvars_eq_self_of_tyFreeVars_nil _ rfl) htyping)
  | @lambda ann K ctx body bodyTy paramTy hparam hfit hrigid _ ihbody =>
    simp only [InferInput.substTyFvars, Subst.onTy_arrow]
    refine .lambda (Subst.onTy_lc hlc hparam) ?_ ?_ ?_
    · intro template heq
      cases ann with
      | none => cases heq
      | some original =>
        cases heq
        exact (hfit original rfl).substTyFvars subst
    · intro template heq
      cases ann with
      | none => cases heq
      | some original =>
        cases heq
        exact template_scope_sourceSubst (hrigid original rfl) hscope
    · simpa only [Subst.onCtx, Subst.onEnv, List.map_cons, Subst.onPolyTy,
        PolyTy.mkTrivial] using ihbody hscope
  | app _ _ ihf ihx =>
    simp only [InferInput.substTyFvars, Subst.onTy_arrow] at ihf ⊢
    exact .app (ihf hscope) (ihx hscope)
  | @letIn ann K ctx rhs body bodyTy scheme avoid hwf hrigid hfit _ _ ihgeneral ihbody =>
    let avoid' := avoid ++ subst.map Prod.fst
    have oldFresh : ∀ fresh, FreshNames avoid' scheme.paramCount fresh → FreshNames avoid scheme.paramCount fresh :=
      fun fresh hf => ⟨hf.length, hf.nodup, fun v hv ha => hf.avoid v hv (List.mem_append_left _ ha)⟩
    have domFresh : ∀ fresh, FreshNames avoid' scheme.paramCount fresh → ∀ pair ∈ subst, pair.1 ∉ fresh := by
      intro fresh hf pair hp hv
      exact hf.avoid pair.1 hv (List.mem_append_right _ (List.mem_map.mpr ⟨pair, hp, rfl⟩))
    refine InputTyping.letIn (M := subst.onPolyTy scheme) (L := avoid')
      (Subst.onPolyTy_wf hlc hwf) ?_ ?_ ?_ ?_
    · intro template heq
      cases ann with
      | absent => cases heq
      | complete _ => cases heq
      | partialForall _ _ => cases heq
      | template original =>
        cases heq
        exact template_scope_sourceSubst (hrigid original rfl) hscope
    · intro fresh hf
      have hs := fitsMono_sourceSubst (hfit fresh (oldFresh fresh hf)) subst
      simpa only [PolyTy.openVars, Subst.onPolyTy,
        Subst.onTy_openVars hlc (domFresh fresh hf)] using hs
    · intro fresh hf
      simpa only [PolyTy.openVars, Subst.onPolyTy,
        Subst.onTy_openVars hlc (domFresh fresh hf)] using ihgeneral fresh (oldFresh fresh hf) hscope
    · simpa only [Subst.onCtx, Subst.onEnv, List.map_cons] using ihbody hscope
  | @letSignature K ctx body bodyTy ann rhs scheme avoid hwf hann hrhs hfit _ _ ihgeneral ihbody =>
    let avoid' := avoid ++ subst.map Prod.fst
    have oldFresh : ∀ names, FreshNames avoid' scheme.paramCount names → FreshNames avoid scheme.paramCount names :=
      fun names hf => ⟨hf.length, hf.nodup, fun v hv ha => hf.avoid v hv (List.mem_append_left _ ha)⟩
    have domFresh : ∀ names, FreshNames avoid' scheme.paramCount names → ∀ pair ∈ subst, pair.1 ∉ names := by
      intro names hf pair hp hv
      exact hf.avoid pair.1 hv (List.mem_append_right _ (List.mem_map.mpr ⟨pair, hp, rfl⟩))
    refine InputTyping.letSignature (M := subst.onPolyTy scheme) (L := avoid')
      (Subst.onPolyTy_wf hlc hwf) ?_ ?_ ?_ ?_ ?_
    · intro v hv
      obtain ⟨k, hk, hv⟩ := BindingAnn.rigidVars_substTyFvars hv
      exact hscope k (hann k hk) v hv
    · intro v hv
      obtain ⟨k, hk, hv⟩ := InferInput.rigidVars_substTyFvars hv
      exact hscope k (hrhs k hk) v hv
    · intro names hf
      exact (hfit names (oldFresh names hf)).onSubst_source subst hlc (domFresh names hf)
    · intro names hf
      have hsmall : ∀ pair ∈ subst, pair.1 ∉ names.take ann.paramCount :=
        fun pair hp hv => domFresh names hf pair hp (List.mem_of_mem_take hv)
      have hchild := ihgeneral names (oldFresh names hf) (K' := K' ++ names.take ann.paramCount) (fun k hk v hv => by
        rcases List.mem_append.mp hk with hk | hk
        · exact List.mem_append_left _ (hscope k hk v hv)
        · have hfix : subst.onTy (.fvar k) = .fvar k := by
            apply Ty.substFvars_eq_self_of_no_key
            intro pair hp hc
            have heq : pair.1 = k := List.mem_singleton.mp hc
            exact hsmall pair hp (heq ▸ hk)
          rw [hfix] at hv
          exact List.mem_append_right _ ((List.mem_singleton.mp hv) ▸ hk))
      simpa only [BindingAnn.paramCount_substTyFvars,
        InferInput.substTyFvars_openTyVars _ hlc hsmall, PolyTy.openVars, Subst.onPolyTy,
        Subst.onTy_openVars hlc (domFresh names hf)] using hchild
    · simpa only [Subst.onCtx, Subst.onEnv, List.map_cons] using ihbody hscope
  | letRec hgroups hwf hp hG hAnn hRhs hFits _ _ _ ihMono ihPoly ihBody =>
    expose_names
    let avoid := K' ++ (subst.onCtx ctx_1).env.freeVars ++ G ++ subst.map Prod.fst ++
      subst.flatMap (fun p => p.2.freeVars) ++ specs.flatMap RecSpec.freeVars
    obtain ⟨W, hWlen, hWnd, hWavoid⟩ := exists_fresh_names avoid G.length
    have hGW : ∀ g ∈ G, g ∉ W := by
      intro g hg hw
      exact hWavoid g hw (by simp only [avoid, List.mem_append]; tauto)
    have hWmono : ∀ t, .mono t ∈ specs → ∀ w ∈ W, w ∉ t.freeVars := by
      intro t ht w hw hv
      exact hWavoid w hw (by
        simp only [avoid, List.mem_append]
        right
        exact List.mem_flatMap.mpr ⟨.mono t, ht, hv⟩)
    have hdomW : ∀ p ∈ subst, p.1 ∉ W := by
      intro p hp hw
      exact hWavoid p.1 hw (by
        have hm : p.1 ∈ subst.map Prod.fst := List.mem_map.mpr ⟨p, hp, rfl⟩
        simp only [avoid, List.mem_append]
        tauto)
    have hranW : ∀ p ∈ subst, ∀ v ∈ p.2.freeVars, v ∉ W := by
      intro p hp v hv hw
      exact hWavoid v hw (by
        simp only [avoid, List.mem_append]
        left; right
        exact List.mem_flatMap.mpr ⟨p, hp, hv⟩)
    let specs' := specs.map (fun spec => RecSpec.onSubstSource subst (RecSpec.onSubst (G.zip (W.map Ty.fvar)) spec))
    let prefixes' := prefixes.map (recRenameNames G W)
    let L' := G ++ W ++ L ++ subst.map Prod.fst
    have hannsLen : anns.length = specs.length := by
      have hh := congrArg List.length hwf.anns_eq
      simpa using hh.symm
    have hpData := fun i hi => hp.get hannsLen (i := i) hi
    have hcompleted := recCompletedSchemes_subst_fresh_pool hlc hWlen hwf.nodup hWnd hGW hWmono
      hdomW hranW hwf.mono_lc hpData
    have hbodyCtx : recBodyCtx (subst.onCtx ctx_1) specs' prefixes' W = subst.onCtx (recBodyCtx ctx_1 specs prefixes G) := by
      simp only [recBodyCtx, Subst.onCtx, Subst.onEnv, List.map_append]
      rw [hcompleted]
    have oldFresh : ∀ Xs, FreshNames (W ++ L') W.length Xs → FreshNames (G ++ L) G.length Xs := by
      intro Xs hf
      refine ⟨hf.length.trans hWlen, hf.nodup, ?_⟩
      intro v hv hm
      exact hf.avoid v hv (by simp only [L', List.mem_append] at hm ⊢; tauto)
    have hGXs : ∀ Xs, FreshNames (W ++ L') W.length Xs → ∀ g ∈ G, g ∉ Xs := by
      intro Xs hf g hg hx
      exact hf.avoid g hx (by simp only [L', List.mem_append]; tauto)
    have hWXs : ∀ Xs, FreshNames (W ++ L') W.length Xs → ∀ w ∈ W, w ∉ Xs := by
      intro Xs hf w hw hx
      exact hf.avoid w hx (List.mem_append_left _ hw)
    have hdomXs : ∀ Xs, FreshNames (W ++ L') W.length Xs → ∀ p ∈ subst, p.1 ∉ Xs := by
      intro Xs hf p hp hx
      exact hf.avoid p.1 hx (by
        have hm : p.1 ∈ subst.map Prod.fst := List.mem_map.mpr ⟨p, hp, rfl⟩
        simp only [L', List.mem_append]
        tauto)
    have scopeXs : ∀ Xs, FreshNames (W ++ L') W.length Xs →
        ∀ k ∈ K_1 ++ Xs, ∀ v ∈ (subst.onTy (.fvar k)).freeVars, v ∈ K' ++ Xs := by
      intro Xs hf k hk v hv
      rcases List.mem_append.mp hk with hk | hk
      · exact List.mem_append_left _ (hscope k hk v hv)
      · have hfix : subst.onTy (.fvar k) = .fvar k :=
          Subst.fixes_of_dom_avoids (hdomXs Xs hf) k hk
        rw [hfix] at hv
        exact List.mem_append_right _ ((List.mem_singleton.mp hv) ▸ hk)
    simp only [InferInput.substTyFvars, substInputBindings_eq_map_source]
    refine InputTyping.letRec (specs := specs') (groups := groups) (prefixes := prefixes') (G := W) (L := L')
      ?_ ?_ (hp.subst_fresh_pool (S := subst) hWlen hWnd) ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · have hg := hgroups.map_bindings (anns' := (anns.map (BindingAnn.substTyFvars subst)).map BindingAnn.recModeAnn) id
        (by simp) (fun i => by
          simp only [RecGroups.UnsignedAt, List.getElem?_map, Option.map_map, Function.comp_def]
          cases anns[i]? with
          | none => simp
          | some ann => cases ann <;> simp [BindingAnn.recModeAnn, BindingAnn.substTyFvars])
        (fun _ _ => rfl)
      simpa only [List.map_id, List.map_map, Function.comp_def, InferInput.erase_substTyFvars] using hg
    · simpa only [List.map_map, Function.comp_def, InferInput.erase_substTyFvars] using RecSpecs.WF.subst_fresh_pool hwf hlc hWnd
    · intro w hw hm
      exact hWavoid w hw (by simp only [avoid, List.mem_append] at hm ⊢; tauto)
    · intro ann ha v hv
      obtain ⟨ann0, ha0, rfl⟩ := List.mem_map.mp ha
      obtain ⟨k, hk, himage⟩ := BindingAnn.rigidVars_substTyFvars hv
      exact hscope k (hAnn ann0 ha0 k hk) v himage
    · intro rhs hr v hv
      obtain ⟨rhs0, hr0, rfl⟩ := List.mem_map.mp hr
      obtain ⟨k, hk, himage⟩ := InferInput.rigidVars_substTyFvars hv
      exact hscope k (hRhs rhs0 hr0 k hk) v himage
    · intro stage component hs Xs hf member hm rhs ann names ty hr ha hn ht
      rw [List.getElem?_map] at hr ha hn ht
      obtain ⟨rhs0, hr0, rfl⟩ := Option.map_eq_some_iff.mp hr
      obtain ⟨ann0, ha0, rfl⟩ := Option.map_eq_some_iff.mp ha
      obtain ⟨names0, hn0, rfl⟩ := Option.map_eq_some_iff.mp hn
      obtain ⟨spec0, ht0, heq⟩ := Option.map_eq_some_iff.mp ht
      cases spec0 with
      | poly scheme => cases heq
      | mono ty0 =>
        cases heq
        change (ann0.substTyFvars subst).RecFits
          (recRenameNames W Xs (recRenameNames G W names0))
          (Ty.renameG W Xs (subst.onTy (Ty.renameG G W ty0)))
        obtain ⟨_, _, hsub⟩ := hp.member member ann0 names0 ha0 hn0
        have hfit := (hFits stage component hs Xs (oldFresh Xs hf) member hm rhs0 ann0 names0 ty0 hr0 ha0 hn0 ht0).onSubst_source
          subst hlc (Subst.fixes_of_dom_avoids (fun p hp hn => hdomXs Xs hf p hp
            (recRenameNames_mem (hf.length.trans hWlen) hsub p.1 hn)))
        rw [recRenameNames_composition hWlen (hf.length.trans hWlen) hWnd hsub,
          Ty.renameG_subst_fresh_pool (hwf.mono_lc ty0 (List.mem_of_getElem? ht0)) hlc hWlen hwf.nodup hWnd hGW
            (hWmono ty0 (List.mem_of_getElem? ht0)) hdomW hranW (hf.length.trans hWlen) (hGXs Xs hf)
            (hWXs Xs hf) (hdomXs Xs hf)]
        exact hfit
    · intro stage component hs Xs hf member hm rhs ann names ty hr ha hn ht
      rw [List.getElem?_map] at hr ha hn ht
      obtain ⟨rhs0, hr0, rfl⟩ := Option.map_eq_some_iff.mp hr
      obtain ⟨ann0, ha0, rfl⟩ := Option.map_eq_some_iff.mp ha
      obtain ⟨names0, hn0, rfl⟩ := Option.map_eq_some_iff.mp hn
      obtain ⟨spec0, ht0, heq⟩ := Option.map_eq_some_iff.mp ht
      cases spec0 with
      | poly scheme => cases heq
      | mono ty0 =>
        cases heq
        change InputTyping (K' ++ Xs)
          (recStageCtx (subst.onCtx ctx_1) specs' prefixes' (groups.take stage).flatten W Xs)
          ((rhs0.substTyFvars subst).openTyVars (recRenameNames W Xs (recRenameNames G W names0)))
          (Ty.renameG W Xs (subst.onTy (Ty.renameG G W ty0)))
        obtain ⟨_, _, hsub⟩ := hp.member member ann0 names0 ha0 hn0
        have hsmall : ∀ p ∈ subst, p.1 ∉ recRenameNames G Xs names0 :=
          fun p hp hn => hdomXs Xs hf p hp (recRenameNames_mem (hf.length.trans hWlen) hsub p.1 hn)
        have hc := ihMono stage component hs Xs (oldFresh Xs hf) member hm rhs0 ann0 names0 ty0 hr0 ha0 hn0 ht0
          (K' := K' ++ Xs) (scopeXs Xs hf)
        have hstageCtx : recStageCtx (subst.onCtx ctx_1) specs' prefixes' (groups.take stage).flatten W Xs =
            subst.onCtx (recStageCtx ctx_1 specs prefixes (groups.take stage).flatten G Xs) := by
          simp only [recStageCtx, Subst.onCtx, Subst.onEnv, List.map_append]
          rw [recStageSchemes_subst_fresh_pool hlc hWlen hwf.nodup hWnd hGW hWmono hdomW hranW
            hwf.mono_lc hpData (hf.length.trans hWlen) (hGXs Xs hf) (hWXs Xs hf) (hdomXs Xs hf)]
        rw [hstageCtx, recRenameNames_composition hWlen (hf.length.trans hWlen) hWnd hsub,
          Ty.renameG_subst_fresh_pool (hwf.mono_lc ty0 (List.mem_of_getElem? ht0)) hlc hWlen hwf.nodup hWnd hGW
            (hWmono ty0 (List.mem_of_getElem? ht0)) hdomW hranW (hf.length.trans hWlen) (hGXs Xs hf)
            (hWXs Xs hf) (hdomXs Xs hf)]
        simpa only [InferInput.substTyFvars_openTyVars _ hlc hsmall] using hc
    · intro member rhs scheme hr hs Ys hy
      rw [List.getElem?_map] at hr hs
      obtain ⟨rhs0, hr0, rfl⟩ := Option.map_eq_some_iff.mp hr
      obtain ⟨spec0, hs0, heq⟩ := Option.map_eq_some_iff.mp hs
      cases spec0 with
      | mono ty => cases heq
      | poly scheme0 =>
        cases heq
        have hy0 : FreshNames L scheme0.paramCount Ys :=
          ⟨hy.length, hy.nodup, fun y hy' hl => hy.avoid y hy' (by simp only [L', List.mem_append]; tauto)⟩
        have hsmall : ∀ p ∈ subst, p.1 ∉ Ys := by
          intro p hp hy'
          exact hy.avoid p.1 hy' (by
            simp only [L', List.mem_append]
            right
            exact List.mem_map.mpr ⟨p, hp, rfl⟩)
        have hc := ihPoly member rhs0 scheme0 hr0 hs0 Ys hy0 (K' := K' ++ Ys) (fun k hk v hv => by
          rcases List.mem_append.mp hk with hk | hk
          · exact List.mem_append_left _ (hscope k hk v hv)
          · rw [Subst.fixes_of_dom_avoids hsmall k hk] at hv
            exact List.mem_append_right _ ((List.mem_singleton.mp hv) ▸ hk))
        rw [hbodyCtx]
        simpa only [InferInput.substTyFvars_openTyVars _ hlc hsmall, PolyTy.openVars, Subst.onPolyTy,
          Subst.onTy_openVars hlc hsmall] using hc
    · rw [hbodyCtx]
      exact ihBody hscope
  | var hlookup hargs hinst =>
    exact .complete rfl (by simp [Expr.tyFreeVars]) (TypeOfHM.onSubst_fixed subst hlc
      (Expr.substTyFvars_eq_self_of_tyFreeVars_nil _ rfl) (.var hlookup hargs hinst))
  | ctor hlookup hargs hinst =>
    exact .complete rfl (by simp [Expr.tyFreeVars]) (TypeOfHM.onSubst_fixed subst hlc
      (Expr.substTyFvars_eq_self_of_tyFreeVars_nil _ rfl) (.ctor hlookup hargs hinst))
  | match_ _ hne _ ihscrut ihbranches =>
    simp only [InferInput.substTyFvars, substInputBranches_eq_map]
    refine .match_ (ihscrut hscope) (fun h => hne (List.map_eq_nil_iff.mp h)) ?_
    intro b hb
    obtain ⟨source, hs, rfl⟩ := List.mem_map.mp hb
    exact ihbranches source hs hscope
  | named hspec _ ihbody hscope =>
    refine .named (hspec.onSubst subst hlc) ?_
    simpa only [Subst.onCtx, Subst.onEnv, List.map_append, List.map_map,
      Subst.onPolyTy, PolyTy.mkTrivial, Function.comp_def] using ihbody hscope
  | wildcard _ ihbody hscope => exact .wildcard (ihbody hscope)


private theorem rigidBranchVars_mem_iff {branches : List (MatchPattern × InferInput)} :
    v ∈ rigidBranchVars branches ↔ ∃ branch ∈ branches, v ∈ branch.2.rigidVars := by
  induction branches with
  | nil => simp only [rigidBranchVars, List.not_mem_nil, false_iff, not_exists, not_and, false_implies, implies_true]
  | cons head rest ih =>
    simp only [rigidBranchVars, List.mem_append, ih, List.mem_cons]
    constructor
    · rintro (h | ⟨b, hb, hv⟩)
      · exact ⟨head, Or.inl rfl, h⟩
      · exact ⟨b, Or.inr hb, hv⟩
    · rintro ⟨b, rfl | hb, hv⟩
      · exact Or.inl hv
      · exact Or.inr ⟨b, hb, hv⟩

/-- Authored free type variables are scoped intrinsically by independent typing. -/
private theorem rigidBindingVars_mem_iff {bindings : List InferInput} :
    v ∈ rigidBindingVars bindings ↔ ∃ rhs ∈ bindings, v ∈ rhs.rigidVars := by
  induction bindings with
  | nil => simp only [rigidBindingVars, List.not_mem_nil, false_iff, not_exists, not_and, false_implies, implies_true]
  | cons head rest ih =>
      simp only [rigidBindingVars, List.mem_append, List.mem_cons, ih]
      constructor
      · rintro (h | ⟨rhs, hr, hv⟩)
        · exact ⟨head, .inl rfl, h⟩
        · exact ⟨rhs, .inr hr, hv⟩
      · rintro ⟨rhs, rfl | hr, hv⟩
        · exact .inl hv
        · exact .inr ⟨rhs, hr, hv⟩

theorem InputTyping.rigidVars (h : InputTyping K ctx input ty) : ∀ v ∈ input.rigidVars, v ∈ K := by
  induction h using InputTyping.rec
      (motive_2 := fun K _ branch _ _ _ => ∀ v ∈ branch.2.rigidVars, v ∈ K) with
  | complete hemb hr _ => exact fun v hv => hr v ((InferInput.toCore_rigidVars _ hemb v).mp hv)
  | primLit _ => intro v hv; cases hv
  | primBinOp _ => intro v hv; cases hv
  | lambda _ _ hr _ ih =>
    intro v hv
    rcases List.mem_append.mp hv with hv | hv
    · expose_names
      cases ann with
      | none => cases hv
      | some t => exact hr t rfl v hv
    · exact ih v hv
  | app _ _ ihf ihx =>
    exact fun v hv => (List.mem_append.mp hv).elim (ihf v) (ihx v)
  | @letIn ann K ctx rhs body bodyTy M L _ hr hf _ _ ihr ihb =>
    obtain ⟨Xs, hlen, hnd, hav⟩ := exists_fresh_names L M.paramCount
    have hXs : FreshNames L M.paramCount Xs := ⟨hlen, hnd, hav⟩
    intro v hv
    rcases List.mem_append.mp hv with hv | hv
    · rcases List.mem_append.mp hv with hv | hv
      · cases ann with
        | absent => cases hv
        | complete _ => cases hf Xs hXs
        | partialForall _ _ => cases hf Xs hXs
        | template t => exact hr t rfl v hv
      · exact ihr Xs hXs v hv
    · exact ihb v hv
  | letSignature _ hann hrhs _ _ _ _ ihb =>
    intro v hv
    rcases List.mem_append.mp hv with hv | hv
    · exact (List.mem_append.mp hv).elim (hann v) (hrhs v)
    · exact ihb v hv
  | var _ _ _ => intro v hv; cases hv
  | ctor _ _ _ => intro v hv; cases hv
  | match_ _ _ _ ihs ihbranches =>
    intro v hv
    rcases List.mem_append.mp hv with hv | hv
    · exact ihs v hv
    · obtain ⟨branch, hb, hv⟩ := rigidBranchVars_mem_iff.mp hv
      exact ihbranches branch hb v hv
  | letRec _ _ _ _ hAnn hRhs _ _ _ _ _ _ ihBody =>
    intro v hv
    rcases List.mem_append.mp hv with hv | hv
    · rcases List.mem_append.mp hv with hv | hv
      · obtain ⟨ann, ha, hv⟩ := List.mem_flatMap.mp hv
        exact hAnn ann ha v hv
      · obtain ⟨rhs, hr, hv⟩ := rigidBindingVars_mem_iff.mp hv
        exact hRhs rhs hr v hv
    · exact ihBody v hv
  | named _ _ ih v hv => exact ih v hv
  | wildcard _ ih v hv => exact ih v hv

/-- Fixed-source transport is a corollary of source substitution and intrinsic
annotation scope; it needs only pointwise protection of the composite. -/
theorem BranchTyping.onSubst_source
    (h : BranchTyping InputTyping K ctx branch scrutTy resultTy) (subst : Subst)
    (hlc : ∀ p ∈ subst, p.2.IsLC)
    (hscope : ∀ k ∈ K, ∀ v ∈ (subst.onTy (.fvar k)).freeVars, v ∈ K') :
    BranchTyping InputTyping K' (subst.onCtx ctx) (branch.1, branch.2.substTyFvars subst)
      (subst.onTy scrutTy) (subst.onTy resultTy) := by
  cases h with
  | named hspec hb =>
    refine .named (hspec.onSubst subst hlc) ?_
    simpa only [Subst.onCtx, Subst.onEnv, List.map_append, List.map_map,
      Subst.onPolyTy, PolyTy.mkTrivial, Function.comp_def] using hb.onSubst_source subst hlc hscope
  | wildcard hb => exact .wildcard (hb.onSubst_source subst hlc hscope)

theorem InputTyping.scope_mono (h : InputTyping K ctx input ty) (hscope : ∀ k ∈ K, k ∈ K') :
    InputTyping K' ctx input ty := by
  have hinput : input.substTyFvars [] = input := input.substTyFvars_eq_self_of_fixes (fun _ _ => rfl)
  simpa only [Subst.onCtx_nil, Subst.onTy_nil, hinput] using
    h.onSubst_source [] (by simp) (fun k hk v hv => hscope v ((List.mem_singleton.mp hv) ▸ hk))


theorem InputTyping.onSubst_fixes (h : InputTyping K ctx input ty) (subst : Subst)
    (hlc : ∀ pair ∈ subst, pair.2.IsLC)
    (hprotected : ∀ v ∈ K, subst.onTy (.fvar v) = .fvar v) :
    InputTyping K (subst.onCtx ctx) input (subst.onTy ty) := by
  have ht := h.onSubst_source (K' := K) subst hlc (fun k hk v hv => by
    rw [hprotected k hk] at hv
    exact (List.mem_singleton.mp hv) ▸ hk)
  rwa [input.substTyFvars_eq_self_of_fixes (fun v hv => hprotected v (h.rigidVars v hv))] at ht

/-- Pointwise-fixed transport for an independently typed match branch. -/
theorem BranchTyping.onSubst_fixes (h : BranchTyping InputTyping K ctx branch scrutTy resultTy)
    (subst : Subst) (hlc : ∀ pair ∈ subst, pair.2.IsLC)
    (hprotected : ∀ v ∈ K, subst.onTy (.fvar v) = .fvar v) :
    BranchTyping InputTyping K (subst.onCtx ctx) branch (subst.onTy scrutTy) (subst.onTy resultTy) := by
  cases h with
  | named hspec hbody =>
    refine .named (hspec.onSubst subst hlc) ?_
    simpa only [Subst.onCtx, Subst.onEnv, List.map_append, List.map_map,
      Subst.onPolyTy, PolyTy.mkTrivial, Function.comp_def] using hbody.onSubst_fixes subst hlc hprotected
  | wildcard hbody => exact .wildcard (hbody.onSubst_fixes subst hlc hprotected)

theorem InputTyping.onSubst (h : InputTyping K ctx input ty) (subst : Subst)
    (hlc : ∀ pair ∈ subst, pair.2.IsLC) (hprotected : ∀ pair ∈ subst, pair.1 ∉ K) :
    InputTyping K (subst.onCtx ctx) input (subst.onTy ty) :=
  h.onSubst_fixes subst hlc (Subst.fixes_of_dom_avoids hprotected)

theorem InputTyping.regular (h : InputTyping K ctx input ty) : ty.IsLC := h.erase.regular



theorem InputTyping.generalise_opened {K Ys G : List Nat} {ctx : Ctx} {input : InferInput} {ty : Ty}
    (h : InputTyping (K ++ Ys) ctx (input.openTyVars Ys) ty)
    (hnd : (Ys ++ G).Nodup)
    (hctx : ∀ name ∈ Ys ++ G, name ∉ ctx.env.freeVars)
    (hK : ∀ name ∈ Ys ++ G, name ∉ K)
    (hsource : ∀ v ∈ input.rigidVars, v ∈ K) :
    ∃ L, ∀ Xs, FreshNames L (Ys.length + G.length) Xs →
      InputTyping (K ++ Xs.take Ys.length) ctx (input.openTyVars (Xs.take Ys.length))
        (Ty.openVars Xs (Ty.closeOver (Ys ++ G) ty)) := by
  refine ⟨Ys ++ G, ?_⟩
  intro Xs hXs
  have htake : (Xs.take Ys.length).length = Ys.length := by
    rw [List.length_take, hXs.length]; omega
  have hdisj : ∀ name ∈ Ys ++ G, name ∉ Xs := fun name hn hx => hXs.avoid name hx hn
  have hYtake : ∀ name ∈ Ys, name ∉ Xs.take Ys.length :=
    fun name hn hx => hdisj name (List.mem_append_left _ hn) (List.mem_of_mem_take hx)
  let RY : Subst := Ys.zip ((Xs.take Ys.length).map Ty.fvar)
  let RG : Subst := G.zip ((Xs.drop Ys.length).map Ty.fvar)
  have hRYlc : ∀ p ∈ RY, p.2.IsLC := by
    intro p hp
    obtain ⟨_, _, heq⟩ := List.mem_map.mp (List.of_mem_zip hp).2
    rw [← heq]; exact .fvar
  have hRGlc : ∀ p ∈ RG, p.2.IsLC := by
    intro p hp
    obtain ⟨_, _, heq⟩ := List.mem_map.mp (List.of_mem_zip hp).2
    rw [← heq]; exact .fvar
  have hRYK : ∀ k ∈ K, RY.onTy (.fvar k) = .fvar k := by
    intro k hk
    apply Ty.substFvars_eq_self_of_no_key
    intro p hp hc
    simp only [Ty.freeVars, List.mem_singleton] at hc
    exact hK p.1 (List.mem_append_left _ (List.of_mem_zip hp).1) (hc ▸ hk)
  have hRYscope : ∀ k ∈ K ++ Ys, ∀ v ∈ (RY.onTy (.fvar k)).freeVars, v ∈ K ++ Xs.take Ys.length := by
    intro k hk v hv
    rcases List.mem_append.mp hk with hk | hk
    · rw [hRYK k hk] at hv
      simp only [Ty.freeVars, List.mem_singleton] at hv
      exact List.mem_append_left _ (hv ▸ hk)
    · obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hk
      have hilt : i < Ys.length := (List.getElem?_eq_some_iff.mp hi).choose
      have hit : i < (Xs.take Ys.length).length := by omega
      have himg : RY.onTy (.fvar k) = .fvar ((Xs.take Ys.length)[i]) := by
        apply Ty.substFvars_zip_fvar_eq' hnd.of_append_left hi
        · simp only [List.getElem?_map, List.getElem?_eq_getElem hit, Option.map_some]
        · intro y hy hc
          simp only [Ty.freeVars, List.mem_singleton] at hc
          apply hYtake y hy
          rw [hc]
          exact List.getElem_mem hit
      rw [himg] at hv
      simp only [Ty.freeVars, List.mem_singleton] at hv
      exact List.mem_append_right _ (hv ▸ List.getElem_mem hit)
  have ctxFixed : ∀ S : Subst, (∀ p ∈ S, p.1 ∈ Ys ++ G) → S.onCtx ctx = ctx := by
    intro S hS
    have henv := Subst.onEnv_eq_self_of_fresh (fun p hp => hctx p.1 (hS p hp))
    cases ctx
    simp only [Subst.onCtx, henv]
  have hRYctx : RY.onCtx ctx = ctx := ctxFixed RY
    (fun p hp => List.mem_append_left _ (List.of_mem_zip hp).1)
  have hRGctx : RG.onCtx ctx = ctx := ctxFixed RG
    (fun p hp => List.mem_append_right _ (List.of_mem_zip hp).1)
  have hRYsource : (input.openTyVars Ys).substTyFvars RY = input.openTyVars (Xs.take Ys.length) := by
    exact input.substTyFvars_zip_openTyVars htake.symm hnd.of_append_left
      (fun y hy hv => hK y (List.mem_append_left _ hy) (hsource y hv)) hYtake
  have hfirst := h.onSubst_source RY hRYlc hRYscope
  rw [hRYctx, hRYsource] at hfirst
  have hRGavoid : ∀ p ∈ RG, p.1 ∉ K ++ Xs.take Ys.length := by
    intro p hp hc
    have hpG := (List.of_mem_zip hp).1
    rcases List.mem_append.mp hc with hk | hx
    · exact hK p.1 (List.mem_append_right _ hpG) hk
    · exact hdisj p.1 (List.mem_append_right _ hpG) (List.mem_of_mem_take hx)
  have hsecond := hfirst.onSubst RG hRGlc hRGavoid
  rw [hRGctx] at hsecond
  have hzip : (Ys ++ G).zip (Xs.map Ty.fvar) = RY ++ RG := by
    have hmap : Xs.map Ty.fvar = (Xs.take Ys.length).map Ty.fvar ++ (Xs.drop Ys.length).map Ty.fvar := by
      rw [← List.map_append, List.take_append_drop]
    rw [hmap]
    exact List.zip_append (by simp only [List.length_map, htake])
  rw [Ty.openVars_closeOver_rename h.regular hnd (by simpa only [List.length_append] using hXs.length) hdisj,
    hzip]
  change InputTyping (K ++ Xs.take Ys.length) ctx (input.openTyVars (Xs.take Ys.length))
    ((RY ++ RG).onTy ty)
  rw [Subst.onTy_append]
  exact hsecond




/-- Closing a checked partial signature preserves its exact written-prefix
matching at every sufficiently fresh opening of the completed scheme. -/
theorem BindingAnn.SignatureCompletion.cofinite_fits {ann : BindingAnn} {written names : List Nat}
    {ty : Ty} {scheme : PolyTy} {K : List Nat}
    (h : ann.SignatureCompletion written ty scheme names)
    (hnd : names.Nodup) (hK : ∀ name ∈ names, name ∉ K)
    (hsource : ∀ v ∈ ann.rigidVars, v ∈ K) (hlc : ty.IsLC) :
    ∃ L, ∀ Xs, FreshNames L scheme.paramCount Xs → ann.SignatureFits scheme Xs := by
  cases h with
  | complete => exact ⟨[], fun _ _ => .complete⟩
  | @partialSignature ty template count written extras hlen hfit =>
    refine ⟨written ++ extras, ?_⟩
    intro Xs hXs
    have htake : (Xs.take written.length).length = written.length := by
      rw [List.length_take, hXs.length]; simp only [List.length_append]; omega
    have hdisj : ∀ name ∈ written ++ extras, name ∉ Xs := fun name hn hx => hXs.avoid name hx hn
    have hYtake : ∀ name ∈ written, name ∉ Xs.take written.length :=
      fun name hn hx => hdisj name (List.mem_append_left _ hn) (List.mem_of_mem_take hx)
    let RY : Subst := written.zip ((Xs.take written.length).map Ty.fvar)
    let RG : Subst := extras.zip ((Xs.drop written.length).map Ty.fvar)
    have hRGlc : ∀ p ∈ RG, p.2.IsLC := by
      intro p hp
      obtain ⟨_, _, heq⟩ := List.mem_map.mp (List.of_mem_zip hp).2
      rw [← heq]; exact .fvar
    have hRYsource : (template.openTyVarsFrom 0 written).substTyFvars RY =
        template.openTyVarsFrom 0 (Xs.take written.length) := by
      exact template.substTyFvars_zip_openTyVarsFrom htake.symm hnd.of_append_left
        (fun y hy hv => hK y (List.mem_append_left _ hy) (hsource y hv)) hYtake 0
    have hfirst := hfit.substTyFvars RY
    rw [hRYsource] at hfirst
    have hRGfresh : ∀ p ∈ RG, p.1 ∉ Xs.take written.length := by
      intro p hp hc
      exact hdisj p.1 (List.mem_append_right _ (List.of_mem_zip hp).1) (List.mem_of_mem_take hc)
    have hRGsource : (template.openTyVarsFrom 0 (Xs.take written.length)).substTyFvars RG =
        template.openTyVarsFrom 0 (Xs.take written.length) := by
      rw [template.substTyFvars_openTyVarsFrom hRGlc hRGfresh 0]
      rw [template.substTyFvars_eq_self_of_fixes (fun v hv => by
        apply Ty.substFvars_eq_self_of_no_key
        intro p hp hc
        have heq : p.1 = v := List.mem_singleton.mp hc
        exact hK p.1 (List.mem_append_right _ (List.of_mem_zip hp).1) (heq ▸ hsource v hv))]
    have hsecond := hfirst.substTyFvars RG
    rw [hRGsource] at hsecond
    have hzip : (written ++ extras).zip (Xs.map Ty.fvar) = RY ++ RG := by
      have hmap : Xs.map Ty.fvar = (Xs.take written.length).map Ty.fvar ++ (Xs.drop written.length).map Ty.fvar := by
        rw [← List.map_append, List.take_append_drop]
      rw [hmap]
      exact List.zip_append (by simp only [List.length_map, htake])
    refine .partialSignature (by simp only [List.length_append]; omega) ?_
    change (template.openTyVarsFrom 0 (Xs.take count)).Fits
      (Ty.openVars Xs (Ty.closeOver (written ++ extras) ty))
    rw [Ty.openVars_closeOver_rename hlc hnd hXs.length hdisj, hzip]
    change (template.openTyVarsFrom 0 (Xs.take count)).Fits ((RY ++ RG).onTy ty)
    rw [Subst.onTy_append, ← hlen]
    exact hsecond


/-- Opening a completed signed scheme reopens exactly its written source
binders; inferred extra quantifiers specialize only the typing monotype. -/
theorem BindingAnn.SignatureCompletion.cofinite_typing
    {ann : BindingAnn} {written names K : List Nat} {ty : Ty} {scheme : PolyTy} {ctx : Ctx} {input : InferInput}
    (hcomp : ann.SignatureCompletion written ty scheme names)
    (ht : InputTyping (K ++ written) ctx (input.openTyVars written) ty)
    (hwf : scheme.WF) (hnd : names.Nodup)
    (hctx : ∀ name ∈ names, name ∉ ctx.env.freeVars)
    (hK : ∀ name ∈ names, name ∉ K)
    (hann : ∀ v ∈ ann.rigidVars, v ∈ K)
    (hsource : ∀ v ∈ input.rigidVars, v ∈ K) :
    ∃ L, ∀ Xs, FreshNames L scheme.paramCount Xs →
      InputTyping (K ++ Xs.take ann.paramCount) ctx (input.openTyVars (Xs.take ann.paramCount)) (scheme.openVars Xs) := by
  cases hcomp with
  | @complete ty written scheme hlen heq =>
    obtain ⟨L, hgen⟩ := ht.generalise_opened (G := [])
      (by simpa only [List.append_nil] using hnd)
      (by simpa only [List.append_nil] using hctx)
      (by simpa only [List.append_nil] using hK) hsource
    have hclose : Ty.closeOver written ty = scheme.body := by
      rw [heq, PolyTy.openVars]
      exact Ty.closeOver_openVars_self hnd (by simpa only [hlen] using hwf)
        (fun name hn hv => hK name hn (hann name hv))
    refine ⟨L, ?_⟩
    intro Xs hf
    simpa only [List.append_nil, BindingAnn.paramCount, hclose, PolyTy.openVars, hlen] using
      hgen Xs (by simpa only [List.length_nil, Nat.add_zero, hlen] using hf)
  | @partialSignature ty template count written extras hlen _ =>
    obtain ⟨L, hgen⟩ := ht.generalise_opened (G := extras) hnd hctx hK hsource
    refine ⟨L, ?_⟩
    intro Xs hf
    simpa only [BindingAnn.paramCount, hlen, PolyTy.openVars] using
      hgen Xs (by simpa only [List.length_append] using hf)

/-- A signed binding's cofinite contract transports under an ambient
specialization; the newly opened written variables are chosen away from its domain. -/
theorem InputTyping.signatureBinding_onSubst
    {ann : BindingAnn} {scheme : PolyTy} {avoid : List Nat} {K : List Nat} {ctx : Ctx} {input : InferInput}
    (hfit : ∀ fresh, FreshNames avoid scheme.paramCount fresh → ann.SignatureFits scheme fresh)
    (htyping : ∀ fresh, FreshNames avoid scheme.paramCount fresh →
      InputTyping (K ++ fresh.take ann.paramCount) ctx (input.openTyVars (fresh.take ann.paramCount)) (scheme.openVars fresh))
    (hrigid : ∀ v ∈ ann.rigidVars, v ∈ K)
    (subst : Subst) (hlc : ∀ pair ∈ subst, pair.2.IsLC)
    (hprotected : ∀ pair ∈ subst, pair.1 ∉ K) :
    ∃ avoid',
      (∀ fresh, FreshNames avoid' scheme.paramCount fresh → ann.SignatureFits (subst.onPolyTy scheme) fresh) ∧
      (∀ fresh, FreshNames avoid' scheme.paramCount fresh →
        InputTyping (K ++ fresh.take ann.paramCount) (subst.onCtx ctx)
          (input.openTyVars (fresh.take ann.paramCount)) ((subst.onPolyTy scheme).openVars fresh)) := by
  let avoid' := avoid ++ subst.map Prod.fst
  have hold : ∀ fresh, FreshNames avoid' scheme.paramCount fresh → FreshNames avoid scheme.paramCount fresh :=
    fun fresh hf => ⟨hf.length, hf.nodup, fun v hv ha => hf.avoid v hv (List.mem_append_left _ ha)⟩
  have hdom : ∀ fresh, FreshNames avoid' scheme.paramCount fresh → ∀ pair ∈ subst, pair.1 ∉ fresh := by
    intro fresh hf pair hp hv
    exact hf.avoid pair.1 hv (List.mem_append_right _ (List.mem_map.mpr ⟨pair, hp, rfl⟩))
  refine ⟨avoid', ?_, ?_⟩
  · intro fresh hf
    have hfit' := (hfit fresh (hold fresh hf)).onSubst_source subst hlc (hdom fresh hf)
    rwa [ann.substTyFvars_eq_self_of_fixes (fun v hv => Subst.fixes_of_dom_avoids hprotected v (hrigid v hv))] at hfit'
  · intro fresh hf
    have hprotected' : ∀ pair ∈ subst, pair.1 ∉ K ++ fresh.take ann.paramCount := by
      intro pair hp hmem
      rcases List.mem_append.mp hmem with hmem | hmem
      · exact hprotected pair hp hmem
      · exact hdom fresh hf pair hp (List.mem_of_mem_take hmem)
    have ht := (htyping fresh (hold fresh hf)).onSubst subst hlc hprotected'
    simpa only [Subst.onPolyTy, PolyTy.openVars, Subst.onTy_openVars hlc (hdom fresh hf)] using ht

/-- Cofinite binding premises transport together with authored source syntax. -/
theorem InputTyping.binding_onSubst_source {ann : BindingAnn} {scheme : PolyTy} {avoid : List Nat}
    (hfit : ∀ fresh, FreshNames avoid scheme.paramCount fresh → ann.FitsMono (scheme.openVars fresh))
    (htyping : ∀ fresh, FreshNames avoid scheme.paramCount fresh → InputTyping K ctx input (scheme.openVars fresh))
    (subst : Subst) (hlc : ∀ pair ∈ subst, pair.2.IsLC)
    (hscope : ∀ k ∈ K, ∀ v ∈ (subst.onTy (.fvar k)).freeVars, v ∈ K') :
    ∃ avoid',
      (∀ fresh, FreshNames avoid' scheme.paramCount fresh →
        (ann.substTyFvars subst).FitsMono ((subst.onPolyTy scheme).openVars fresh)) ∧
      (∀ fresh, FreshNames avoid' scheme.paramCount fresh →
        InputTyping K' (subst.onCtx ctx) (input.substTyFvars subst) ((subst.onPolyTy scheme).openVars fresh)) := by
  let avoid' := avoid ++ subst.map Prod.fst
  have hold : ∀ fresh, FreshNames avoid' scheme.paramCount fresh → FreshNames avoid scheme.paramCount fresh :=
    fun fresh hf => ⟨hf.length, hf.nodup, fun v hv ha => hf.avoid v hv (List.mem_append_left _ ha)⟩
  have hdom : ∀ fresh, FreshNames avoid' scheme.paramCount fresh → ∀ pair ∈ subst, pair.1 ∉ fresh := by
    intro fresh hf pair hp hv
    exact hf.avoid pair.1 hv (List.mem_append_right _ (List.mem_map.mpr ⟨pair, hp, rfl⟩))
  refine ⟨avoid', ?_, ?_⟩
  · intro fresh hf
    simpa only [PolyTy.openVars, Subst.onPolyTy, Subst.onTy_openVars hlc (hdom fresh hf)] using
      fitsMono_sourceSubst (hfit fresh (hold fresh hf)) subst
  · intro fresh hf
    simpa only [PolyTy.openVars, Subst.onPolyTy, Subst.onTy_openVars hlc (hdom fresh hf)] using
      (htyping fresh (hold fresh hf)).onSubst_source subst hlc hscope

/-- Scoped written openings also transport; fresh binders are protected only
inside the RHS premise. -/
theorem InputTyping.signatureBinding_onSubst_source
    {ann : BindingAnn} {scheme : PolyTy} {avoid : List Nat} {K K' : List Nat} {ctx : Ctx} {input : InferInput}
    (hfit : ∀ fresh, FreshNames avoid scheme.paramCount fresh → ann.SignatureFits scheme fresh)
    (htyping : ∀ fresh, FreshNames avoid scheme.paramCount fresh →
      InputTyping (K ++ fresh.take ann.paramCount) ctx (input.openTyVars (fresh.take ann.paramCount)) (scheme.openVars fresh))
    (subst : Subst) (hlc : ∀ pair ∈ subst, pair.2.IsLC)
    (hscope : ∀ k ∈ K, ∀ v ∈ (subst.onTy (.fvar k)).freeVars, v ∈ K') :
    ∃ avoid',
      (∀ fresh, FreshNames avoid' scheme.paramCount fresh →
        (ann.substTyFvars subst).SignatureFits (subst.onPolyTy scheme) fresh) ∧
      (∀ fresh, FreshNames avoid' scheme.paramCount fresh →
        InputTyping (K' ++ fresh.take (ann.substTyFvars subst).paramCount) (subst.onCtx ctx)
          ((input.substTyFvars subst).openTyVars (fresh.take (ann.substTyFvars subst).paramCount))
          ((subst.onPolyTy scheme).openVars fresh)) := by
  let avoid' := avoid ++ subst.map Prod.fst
  have hold : ∀ fresh, FreshNames avoid' scheme.paramCount fresh → FreshNames avoid scheme.paramCount fresh :=
    fun fresh hf => ⟨hf.length, hf.nodup, fun v hv ha => hf.avoid v hv (List.mem_append_left _ ha)⟩
  have hdom : ∀ fresh, FreshNames avoid' scheme.paramCount fresh → ∀ pair ∈ subst, pair.1 ∉ fresh := by
    intro fresh hf pair hp hv
    exact hf.avoid pair.1 hv (List.mem_append_right _ (List.mem_map.mpr ⟨pair, hp, rfl⟩))
  refine ⟨avoid', ?_, ?_⟩
  · intro fresh hf
    exact (hfit fresh (hold fresh hf)).onSubst_source subst hlc (hdom fresh hf)
  · intro fresh hf
    have hsmall : ∀ pair ∈ subst, pair.1 ∉ fresh.take ann.paramCount :=
      fun pair hp hv => hdom fresh hf pair hp (List.mem_of_mem_take hv)
    have ht := (htyping fresh (hold fresh hf)).onSubst_source subst hlc
      (K' := K' ++ fresh.take ann.paramCount) (fun k hk v hv => by
        rcases List.mem_append.mp hk with hk | hk
        · exact List.mem_append_left _ (hscope k hk v hv)
        · have hfix : subst.onTy (.fvar k) = .fvar k := by
            apply Ty.substFvars_eq_self_of_no_key
            intro pair hp hc
            exact hsmall pair hp ((List.mem_singleton.mp hc) ▸ hk)
          rw [hfix] at hv
          exact List.mem_append_right _ ((List.mem_singleton.mp hv) ▸ hk))
    simpa only [BindingAnn.paramCount_substTyFvars,
      InferInput.substTyFvars_openTyVars _ hlc hsmall, PolyTy.openVars, Subst.onPolyTy,
      Subst.onTy_openVars hlc (hdom fresh hf)] using ht

/-- Simultaneous fresh opening of an ordinary partial binding's monotype. The
input syntax stays unchanged because every fixed annotation variable is in K. -/
theorem InputTyping.generalise {ann : BindingAnn} {names : List Nat} (h : InputTyping K ctx input ty)
    (hfit : ann.FitsMono ty)
    (hrigid : ∀ template, ann = .template template → ∀ v ∈ template.rigidVars, v ∈ K)
    (hnames : names.Nodup) (hctx : ∀ name ∈ names, name ∉ ctx.env.freeVars)
    (hprotected : ∀ name ∈ names, name ∉ K) :
    ∀ fresh, FreshNames names names.length fresh →
      ann.FitsMono (Ty.openVars fresh (Ty.closeOver names ty)) ∧
      InputTyping K ctx input (Ty.openVars fresh (Ty.closeOver names ty)) := by
  intro fresh hfresh
  let rename : Subst := names.zip (fresh.map Ty.fvar)
  have hdom : ∀ pair ∈ rename, pair.1 ∉ K :=
    fun pair hp => hprotected pair.1 (List.of_mem_zip hp).1
  have hlc : ∀ pair ∈ rename, pair.2.IsLC := by
    intro pair hp
    obtain ⟨name, _, heq⟩ := List.mem_map.mp (List.of_mem_zip hp).2
    rw [← heq]
    exact .fvar
  have hctxfix : rename.onCtx ctx = ctx := by
    cases ctx with
    | mk env ctors =>
        exact congrArg (fun env => Ctx.mk env ctors)
          (Subst.onEnv_eq_self_of_fresh (fun pair hp => hctx pair.1 (List.of_mem_zip hp).1))
  rw [Ty.openVars_closeOver_rename h.regular hnames hfresh.length
    (fun name hn hf => hfresh.avoid name hf hn)]
  refine ⟨hfit.onSubst hrigid hdom, ?_⟩
  have hrenamed := h.onSubst rename hlc hdom
  rwa [hctxfix] at hrenamed

/-- Transport both independent ordinary-let premises through a whole ambient
specialization, freshening opening names away from its domain. -/
theorem InputTyping.binding_onSubst_fixes {ann : BindingAnn} {scheme : PolyTy} {avoid : List Nat}
    (hfit : ∀ fresh, FreshNames avoid scheme.paramCount fresh → ann.FitsMono (scheme.openVars fresh))
    (htyping : ∀ fresh, FreshNames avoid scheme.paramCount fresh → InputTyping K ctx input (scheme.openVars fresh))
    (hrigid : ∀ template, ann = .template template → ∀ v ∈ template.rigidVars, v ∈ K)
    (subst : Subst) (hlc : ∀ pair ∈ subst, pair.2.IsLC)
    (hprotected : ∀ v ∈ K, subst.onTy (.fvar v) = .fvar v) :
    ∃ avoid',
      (∀ fresh, FreshNames avoid' scheme.paramCount fresh → ann.FitsMono ((subst.onPolyTy scheme).openVars fresh)) ∧
      (∀ fresh, FreshNames avoid' scheme.paramCount fresh →
        InputTyping K (subst.onCtx ctx) input ((subst.onPolyTy scheme).openVars fresh)) := by
  let avoid' := avoid ++ subst.map Prod.fst
  have hstep : ∀ fresh, FreshNames avoid' scheme.paramCount fresh →
      ann.FitsMono ((subst.onPolyTy scheme).openVars fresh) ∧
      InputTyping K (subst.onCtx ctx) input ((subst.onPolyTy scheme).openVars fresh) := by
    intro fresh hf
    have hold : FreshNames avoid scheme.paramCount fresh :=
      ⟨hf.length, hf.nodup, fun v hv ha => hf.avoid v hv (List.mem_append_left _ ha)⟩
    have hdom : ∀ pair ∈ subst, pair.1 ∉ fresh := by
      intro pair hp hv
      exact hf.avoid pair.1 hv (List.mem_append_right _ (List.mem_map.mpr ⟨pair, hp, rfl⟩))
    have hfit' := (hfit fresh hold).onSubst_fixes hrigid hprotected
    have htyping' := (htyping fresh hold).onSubst_fixes subst hlc hprotected
    simpa only [PolyTy.openVars, Subst.onPolyTy, Subst.onTy_openVars hlc hdom] using And.intro hfit' htyping'
  exact ⟨avoid', fun fresh hf => (hstep fresh hf).1, fun fresh hf => (hstep fresh hf).2⟩

theorem InputTyping.binding_onSubst {ann : BindingAnn} {scheme : PolyTy} {avoid : List Nat}
    (hfit : ∀ fresh, FreshNames avoid scheme.paramCount fresh → ann.FitsMono (scheme.openVars fresh))
    (htyping : ∀ fresh, FreshNames avoid scheme.paramCount fresh → InputTyping K ctx input (scheme.openVars fresh))
    (hrigid : ∀ template, ann = .template template → ∀ v ∈ template.rigidVars, v ∈ K)
    (subst : Subst) (hlc : ∀ pair ∈ subst, pair.2.IsLC)
    (hprotected : ∀ pair ∈ subst, pair.1 ∉ K) :
    ∃ avoid',
      (∀ fresh, FreshNames avoid' scheme.paramCount fresh → ann.FitsMono ((subst.onPolyTy scheme).openVars fresh)) ∧
      (∀ fresh, FreshNames avoid' scheme.paramCount fresh →
        InputTyping K (subst.onCtx ctx) input ((subst.onPolyTy scheme).openVars fresh)) :=
  InputTyping.binding_onSubst_fixes hfit htyping hrigid subst hlc (Subst.fixes_of_dom_avoids hprotected)


private theorem Expr.substTyFvars_openTyVars_lc (expr : Expr) {S : Subst} {Xs : List Nat}
    (hlc : ∀ p ∈ S, p.2.IsLC) (hfresh : ∀ p ∈ S, p.1 ∉ Xs) :
    (expr.openTyVars Xs).substTyFvars S = (expr.substTyFvars S).openTyVars Xs := by
  induction S generalizing expr with
  | nil => rfl
  | cons p rest ih =>
    rcases p with ⟨v, ty⟩
    simp only [Expr.substTyFvars]
    rw [Expr.substTyFvar_openTyVars (hlc _ List.mem_cons_self) (hfresh _ List.mem_cons_self)]
    exact ih _ (fun p hp => hlc p (List.mem_cons_of_mem _ hp))
      (fun p hp => hfresh p (List.mem_cons_of_mem _ hp))


/-- Global LC transport is a paired cofinite induction; no closing algebra or
choice of renamed internal witnesses is needed. -/

theorem BindingAnn.BindingFits.onSubst_source {ann : BindingAnn} {scheme : PolyTy} {Xs : List Nat}
    (h : ann.BindingFits scheme Xs) (S : Subst)
    (hlc : ∀ p ∈ S, p.2.IsLC) (hdom : ∀ p ∈ S, p.1 ∉ Xs) :
    (ann.substTyFvars S).BindingFits (S.onPolyTy scheme) Xs := by
  unfold BindingAnn.BindingFits at h ⊢
  rw [BindingAnn.isSignature_substTyFvars]
  cases hm : ann.isSignature with
  | false =>
    simp only [hm, Bool.false_eq_true, if_false] at h ⊢
    have hh := fitsMono_sourceSubst h S
    simpa only [PolyTy.openVars, Subst.onPolyTy, Subst.onTy_openVars hlc hdom] using hh
  | true =>
    simp only [hm, if_true] at h ⊢
    exact h.onSubst_source S hlc hdom

theorem AnnotationCompletion.onSubst_source (h : AnnotationCompletion K input output) (S : Subst)
    (hlc : ∀ p ∈ S, p.2.IsLC)
    (hscope : ∀ k ∈ K, ∀ v ∈ (S.onTy (.fvar k)).freeVars, v ∈ K') :
    AnnotationCompletion K' (input.substTyFvars S) (output.substTyFvars S) := by
  induction h using AnnotationCompletion.rec
      (motive_2 := fun K branches branchesOut _ => ∀ {K'},
        (∀ k ∈ K, ∀ v ∈ (S.onTy (.fvar k)).freeVars, v ∈ K') →
        CompletedBranches AnnotationCompletion K' (substInputBranches S branches)
          (branchesOut.map fun (pat, body) => (pat, body.substTyFvars S))) generalizing K' with
  | @complete core K input hemb hr =>
    refine .complete (input.toCore_substTyFvars hemb S) ?_
    intro v hv
    obtain ⟨k, hk, hv⟩ := Expr.mem_tyFreeVars_substTyFvars_image hv
    exact hscope k (hr k hk) v hv
  | @lambda ann K body completed param hfit hr _ ih =>
    rw [Expr.substTyFvars_lambda]
    cases ann with
    | none =>
      simpa only [InferInput.substTyFvars, Option.map_none] using
        (AnnotationCompletion.lambda (ann := none) (param := S.onTy param)
          (fun _ h => by cases h) (fun _ h => by cases h) (ih hscope))
    | some original =>
      simp only [InferInput.substTyFvars, Option.map_some]
      refine .lambda ?_ ?_ (ih hscope)
      · intro template heq
        cases heq
        exact (hfit original rfl).substTyFvars S
      · intro template heq
        cases heq
        exact template_scope_sourceSubst (hr original rfl) hscope

  | app _ _ ihf ihx =>
    rw [Expr.substTyFvars_app]
    exact .app (ihf hscope) (ihx hscope)
  | @letIn ann K rhs body bodyOut rhsOut M L hr hfit _ _ ihr ihb =>
    let L' := L ++ S.map Prod.fst
    have oldFresh : ∀ Xs, FreshNames L' M.paramCount Xs → FreshNames L M.paramCount Xs :=
      fun Xs hf => ⟨hf.length, hf.nodup, fun v hv hm => hf.avoid v hv (List.mem_append_left _ hm)⟩
    have domFresh : ∀ Xs, FreshNames L' M.paramCount Xs → ∀ p ∈ S, p.1 ∉ Xs := by
      intro Xs hf p hp hv
      exact hf.avoid p.1 hv (List.mem_append_right _ (List.mem_map.mpr ⟨p, hp, rfl⟩))
    rw [Expr.substTyFvars_letIn]
    refine AnnotationCompletion.letIn (M := S.onPolyTy M) (L := L') ?_ ?_ ?_ (ihb hscope)
    · intro template heq
      cases ann with
      | absent | complete _ | partialForall _ _ => cases heq
      | template original =>
        cases heq
        exact template_scope_sourceSubst (hr original rfl) hscope
    · intro Xs hf
      have hfit' := fitsMono_sourceSubst (hfit Xs (oldFresh Xs hf)) S
      simpa only [PolyTy.openVars, Subst.onPolyTy, Subst.onTy_openVars hlc (domFresh Xs hf)] using hfit'
    · intro Xs hf
      have hc := ihr Xs (oldFresh Xs hf) hscope
      simpa only [Expr.substTyFvars_openTyVars_lc _ hlc (domFresh Xs hf)] using hc
  | @letSignature K body bodyOut ann rhs rhsOut M L hann hrhs hfit _ _ ihr ihb =>
    let L' := L ++ S.map Prod.fst
    have oldFresh : ∀ Xs, FreshNames L' M.paramCount Xs → FreshNames L M.paramCount Xs :=
      fun Xs hf => ⟨hf.length, hf.nodup, fun v hv hm => hf.avoid v hv (List.mem_append_left _ hm)⟩
    have domFresh : ∀ Xs, FreshNames L' M.paramCount Xs → ∀ p ∈ S, p.1 ∉ Xs := by
      intro Xs hf p hp hv
      exact hf.avoid p.1 hv (List.mem_append_right _ (List.mem_map.mpr ⟨p, hp, rfl⟩))
    rw [Expr.substTyFvars_letIn]
    refine AnnotationCompletion.letSignature (M := S.onPolyTy M) (L := L') ?_ ?_ ?_ ?_ (ihb hscope)
    · intro v hv
      obtain ⟨k, hk, hv⟩ := BindingAnn.rigidVars_substTyFvars hv
      exact hscope k (hann k hk) v hv
    · intro v hv
      obtain ⟨k, hk, hv⟩ := InferInput.rigidVars_substTyFvars hv
      exact hscope k (hrhs k hk) v hv
    · intro Xs hf
      exact (hfit Xs (oldFresh Xs hf)).onSubst_source S hlc (domFresh Xs hf)
    · intro Xs hf
      have hsmall : ∀ p ∈ S, p.1 ∉ Xs.take ann.paramCount :=
        fun p hp hv => domFresh Xs hf p hp (List.mem_of_mem_take hv)
      have hc := ihr Xs (oldFresh Xs hf) (K' := K' ++ Xs.take ann.paramCount) (fun k hk v hv => by
        rcases List.mem_append.mp hk with hk | hk
        · exact List.mem_append_left _ (hscope k hk v hv)
        · rw [Subst.fixes_of_dom_avoids hsmall k hk] at hv
          exact List.mem_append_right _ ((List.mem_singleton.mp hv) ▸ hk))
      simpa only [BindingAnn.paramCount_substTyFvars, InferInput.substTyFvars_openTyVars _ hlc hsmall,
        Expr.substTyFvars_openTyVars_lc _ hlc (domFresh Xs hf)] using hc
  | match_ _ _ ihs ihbs =>
    rw [Expr.substTyFvars_match]
    exact .match_ (ihs hscope) (ihbs hscope)
  | letRec hlenA hlenR hlenO hAnn hRhs hFits _ _ ihChildren ihBody =>
    expose_names
    let L' := L ++ S.map Prod.fst
    have oldFresh : ∀ (scheme : PolyTy) (Xs : List Nat), FreshNames L' scheme.paramCount Xs → FreshNames L scheme.paramCount Xs :=
      fun scheme Xs hf => ⟨hf.length, hf.nodup, fun v hv hm => hf.avoid v hv (List.mem_append_left _ hm)⟩
    have domFresh : ∀ (scheme : PolyTy) (Xs : List Nat), FreshNames L' scheme.paramCount Xs → ∀ p ∈ S, p.1 ∉ Xs := by
      intro scheme Xs hf p hp hv
      exact hf.avoid p.1 hv (List.mem_append_right _ (List.mem_map.mpr ⟨p, hp, rfl⟩))
    simp only [InferInput.substTyFvars, substInputBindings_eq_map_source, Expr.substTyFvars_letRec]
    rw [show (schemes.map some).map (RecAnn.substFvars S) = (schemes.map S.onPolyTy).map some by
      simp only [List.map_map, Function.comp_def, RecAnn.substFvars_some, PolyTy.substFvars_eq]; rfl]
    refine AnnotationCompletion.letRec (schemes := schemes.map S.onPolyTy) (L := L')
      (by simpa only [List.length_map] using hlenA)
      (by simpa only [List.length_map] using hlenR)
      (by simpa only [List.length_map] using hlenO) ?_ ?_ ?_ ?_ (ihBody hscope)
    · intro ann ha v hv
      obtain ⟨original, ho, rfl⟩ := List.mem_map.mp ha
      obtain ⟨k, hk, himage⟩ := BindingAnn.rigidVars_substTyFvars hv
      exact hscope k (hAnn original ho k hk) v himage
    · intro rhs hr v hv
      obtain ⟨original, ho, rfl⟩ := List.mem_map.mp hr
      obtain ⟨k, hk, himage⟩ := InferInput.rigidVars_substTyFvars hv
      exact hscope k (hRhs original ho k hk) v himage
    · intro member ann rhs output scheme ha hr ho hs Xs hf
      rw [List.getElem?_map] at ha hr ho hs
      obtain ⟨ann0, ha0, rfl⟩ := Option.map_eq_some_iff.mp ha
      obtain ⟨rhs0, hr0, rfl⟩ := Option.map_eq_some_iff.mp hr
      obtain ⟨output0, ho0, rfl⟩ := Option.map_eq_some_iff.mp ho
      obtain ⟨scheme0, hs0, rfl⟩ := Option.map_eq_some_iff.mp hs
      exact (hFits member ann0 rhs0 output0 scheme0 ha0 hr0 ho0 hs0 Xs (oldFresh scheme0 Xs hf)).onSubst_source
        S hlc (domFresh scheme0 Xs hf)
    · intro member ann rhs output scheme ha hr ho hs Xs hf
      rw [List.getElem?_map] at ha hr ho hs
      obtain ⟨ann0, ha0, rfl⟩ := Option.map_eq_some_iff.mp ha
      obtain ⟨rhs0, hr0, rfl⟩ := Option.map_eq_some_iff.mp hr
      obtain ⟨output0, ho0, rfl⟩ := Option.map_eq_some_iff.mp ho
      obtain ⟨scheme0, hs0, rfl⟩ := Option.map_eq_some_iff.mp hs
      have hsmall : ∀ p ∈ S, p.1 ∉ Xs.take ann0.paramCount :=
        fun p hp hv => domFresh scheme0 Xs hf p hp (List.mem_of_mem_take hv)
      have hc := ihChildren member ann0 rhs0 output0 scheme0 ha0 hr0 ho0 hs0 Xs (oldFresh scheme0 Xs hf)
        (K' := K' ++ Xs.take ann0.paramCount) (fun k hk v hv => by
          rcases List.mem_append.mp hk with hk | hk
          · exact List.mem_append_left _ (hscope k hk v hv)
          · rw [Subst.fixes_of_dom_avoids hsmall k hk] at hv
            exact List.mem_append_right _ ((List.mem_singleton.mp hv) ▸ hk))
      simpa only [BindingAnn.paramCount_substTyFvars, InferInput.substTyFvars_openTyVars _ hlc hsmall,
        Expr.substTyFvars_openTyVars_lc _ hlc (domFresh scheme0 Xs hf)] using hc
  | nil => exact .nil
  | cons _ _ ih ihs hscope => exact .cons (ih hscope) (ihs hscope)

theorem AnnotationCompletion.rigidVars (h : AnnotationCompletion K input output) :
    ∀ v ∈ input.rigidVars, v ∈ K := by
  induction h using AnnotationCompletion.rec
      (motive_2 := fun K branches _ _ => ∀ v ∈ rigidBranchVars branches, v ∈ K) with
  | complete hemb hr => exact fun v hv => hr v ((InferInput.toCore_rigidVars _ hemb v).mp hv)
  | lambda _ hr _ ih =>
    intro v hv
    rcases List.mem_append.mp hv with hv | hv
    · expose_names
      cases ann with
      | none => cases hv
      | some t => exact hr t rfl v hv
    · exact ih v hv
  | app _ _ ihf ihx => exact fun v hv => (List.mem_append.mp hv).elim (ihf v) (ihx v)
  | @letIn ann K rhs body bodyOut rhsOut M L hr hf _ _ ihr ihb =>
    obtain ⟨Xs, hlen, hnd, hav⟩ := exists_fresh_names L M.paramCount
    have hFresh : FreshNames L M.paramCount Xs := ⟨hlen, hnd, hav⟩
    intro v hv
    rcases List.mem_append.mp hv with hv | hv
    · rcases List.mem_append.mp hv with hv | hv
      · cases ann with
        | absent => cases hv
        | template t => exact hr t rfl v hv
        | complete _ => cases hf Xs hFresh
        | partialForall _ _ => cases hf Xs hFresh
      · exact ihr Xs hFresh v hv
    · exact ihb v hv
  | letSignature hann hrhs _ _ _ _ ihb =>
    intro v hv
    rcases List.mem_append.mp hv with hv | hv
    · exact (List.mem_append.mp hv).elim (hann v) (hrhs v)
    · exact ihb v hv
  | match_ _ _ ihs ihbs => exact fun v hv => (List.mem_append.mp hv).elim (ihs v) (ihbs v)
  | letRec _ _ _ hAnn hRhs _ _ _ _ ihBody =>
    intro v hv
    rcases List.mem_append.mp hv with hv | hv
    · rcases List.mem_append.mp hv with hv | hv
      · obtain ⟨ann, ha, hv⟩ := List.mem_flatMap.mp hv
        exact hAnn ann ha v hv
      · obtain ⟨rhs, hr, hv⟩ := rigidBindingVars_mem_iff.mp hv
        exact hRhs rhs hr v hv
    · exact ihBody v hv
  | nil v hv => cases hv
  | cons _ _ ih ihs v hv => exact (List.mem_append.mp hv).elim (ih v) (ihs v)

/-- LC specialization is derived, rather than an unrestricted constructor. -/
theorem AnnotationCompletion.scope_mono (h : AnnotationCompletion K input output) (hscope : ∀ k ∈ K, k ∈ K') :
    AnnotationCompletion K' input output := by
  have hinput : input.substTyFvars [] = input := input.substTyFvars_eq_self_of_fixes (fun _ _ => rfl)
  simpa only [hinput, Expr.substTyFvars] using
    h.onSubst_source [] (by simp) (fun k hk v hv => hscope v ((List.mem_singleton.mp hv) ▸ hk))

theorem AnnotationCompletion.onSubst_fixes (h : AnnotationCompletion K input output) (S : Subst)
    (hlc : ∀ p ∈ S, p.2.IsLC) (hfix : ∀ k ∈ K, S.onTy (.fvar k) = .fvar k) :
    AnnotationCompletion K input (output.substTyFvars S) := by
  have ht := h.onSubst_source S hlc (fun k hk v hv => by
    rw [hfix k hk] at hv
    exact (List.mem_singleton.mp hv) ▸ hk)
  rwa [input.substTyFvars_eq_self_of_fixes (fun v hv => hfix v (h.rigidVars v hv))] at ht

theorem AnnotationCompletion.specialise (h : AnnotationCompletion K input output) (S : Subst)
    (hlc : ∀ p ∈ S, p.2.IsLC) (hdom : ∀ p ∈ S, p.1 ∉ K) :
    AnnotationCompletion K input (output.substTyFvars S) :=
  h.onSubst_fixes S hlc (Subst.fixes_of_dom_avoids hdom)

/-- Generated closing witnesses yield exact cofinite output openings. This uses
only the already established scope of the completed RHS. -/
theorem AnnotationCompletion.generalise_closed (h : AnnotationCompletion K input output) {names : List Nat}
    (hnd : names.Nodup) (hK : ∀ name ∈ names, name ∉ K)
    (hb : output.TyBvarBounded 0) :
    ∀ Xs, FreshNames names names.length Xs →
      AnnotationCompletion K input ((output.closeTyVars names).openTyVars Xs) := by
  intro Xs hf
  rw [Expr.open_closeTyVars_rename hnd hf.length
    (fun name hn hx => hf.avoid name hx hn) hb]
  apply h.specialise
  · intro p hp
    obtain ⟨_, _, heq⟩ := List.mem_map.mp (List.of_mem_zip hp).2
    rw [← heq]
    exact .fvar
  · intro p hp
    exact hK p.1 (List.of_mem_zip hp).1

/-- A generated signed prefix is renamed together with the full output binder
block. Only the authored prefix enters the child's protected source scope. -/
theorem AnnotationCompletion.generalise_opened {K Ys G : List Nat} {input : InferInput} {output : Expr}
    (h : AnnotationCompletion (K ++ Ys) (input.openTyVars Ys) output)
    (hnd : (Ys ++ G).Nodup) (hK : ∀ name ∈ Ys ++ G, name ∉ K)
    (hsource : ∀ v ∈ input.rigidVars, v ∈ K) (hbound : output.TyBvarBounded 0) :
    ∃ L, ∀ Xs, FreshNames L (Ys.length + G.length) Xs →
      AnnotationCompletion (K ++ Xs.take Ys.length) (input.openTyVars (Xs.take Ys.length))
        ((output.closeTyVars (Ys ++ G)).openTyVars Xs) := by
  refine ⟨Ys ++ G, ?_⟩
  intro Xs hXs
  have htake : (Xs.take Ys.length).length = Ys.length := by
    rw [List.length_take, hXs.length]; omega
  have hdisj : ∀ name ∈ Ys ++ G, name ∉ Xs := fun name hn hx => hXs.avoid name hx hn
  have hYtake : ∀ name ∈ Ys, name ∉ Xs.take Ys.length :=
    fun name hn hx => hdisj name (List.mem_append_left _ hn) (List.mem_of_mem_take hx)
  let RY : Subst := Ys.zip ((Xs.take Ys.length).map Ty.fvar)
  let RG : Subst := G.zip ((Xs.drop Ys.length).map Ty.fvar)
  have hRYlc : ∀ p ∈ RY, p.2.IsLC := by
    intro p hp
    obtain ⟨_, _, heq⟩ := List.mem_map.mp (List.of_mem_zip hp).2
    rw [← heq]; exact .fvar
  have hRGlc : ∀ p ∈ RG, p.2.IsLC := by
    intro p hp
    obtain ⟨_, _, heq⟩ := List.mem_map.mp (List.of_mem_zip hp).2
    rw [← heq]; exact .fvar
  have hRYK : ∀ k ∈ K, RY.onTy (.fvar k) = .fvar k := by
    intro k hk
    apply Ty.substFvars_eq_self_of_no_key
    intro p hp hc
    simp only [Ty.freeVars, List.mem_singleton] at hc
    exact hK p.1 (List.mem_append_left _ (List.of_mem_zip hp).1) (hc ▸ hk)
  have hRYscope : ∀ k ∈ K ++ Ys, ∀ v ∈ (RY.onTy (.fvar k)).freeVars, v ∈ K ++ Xs.take Ys.length := by
    intro k hk v hv
    rcases List.mem_append.mp hk with hk | hk
    · rw [hRYK k hk] at hv
      simp only [Ty.freeVars, List.mem_singleton] at hv
      exact List.mem_append_left _ (hv ▸ hk)
    · obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hk
      have hilt : i < Ys.length := (List.getElem?_eq_some_iff.mp hi).choose
      have hit : i < (Xs.take Ys.length).length := by omega
      have himg : RY.onTy (.fvar k) = .fvar ((Xs.take Ys.length)[i]) := by
        apply Ty.substFvars_zip_fvar_eq' hnd.of_append_left hi
        · simp only [List.getElem?_map, List.getElem?_eq_getElem hit, Option.map_some]
        · intro y hy hc
          simp only [Ty.freeVars, List.mem_singleton] at hc
          apply hYtake y hy
          rw [hc]
          exact List.getElem_mem hit
      rw [himg] at hv
      simp only [Ty.freeVars, List.mem_singleton] at hv
      exact List.mem_append_right _ (hv ▸ List.getElem_mem hit)
  have hRYsource : (input.openTyVars Ys).substTyFvars RY = input.openTyVars (Xs.take Ys.length) := by
    exact input.substTyFvars_zip_openTyVars htake.symm hnd.of_append_left
      (fun y hy hv => hK y (List.mem_append_left _ hy) (hsource y hv)) hYtake
  have hfirst := h.onSubst_source RY hRYlc hRYscope
  rw [hRYsource] at hfirst
  have hRGavoid : ∀ p ∈ RG, p.1 ∉ K ++ Xs.take Ys.length := by
    intro p hp hc
    have hpG := (List.of_mem_zip hp).1
    rcases List.mem_append.mp hc with hk | hx
    · exact hK p.1 (List.mem_append_right _ hpG) hk
    · exact hdisj p.1 (List.mem_append_right _ hpG) (List.mem_of_mem_take hx)
  have hsecond := hfirst.specialise RG hRGlc hRGavoid
  have hzip : (Ys ++ G).zip (Xs.map Ty.fvar) = RY ++ RG := by
    have hmap : Xs.map Ty.fvar = (Xs.take Ys.length).map Ty.fvar ++ (Xs.drop Ys.length).map Ty.fvar := by
      rw [← List.map_append, List.take_append_drop]
    rw [hmap]
    exact List.zip_append (by simp only [List.length_map, htake])
  rw [Expr.open_closeTyVars_rename hnd
    (by simpa only [List.length_append] using hXs.length) hdisj hbound, hzip,
    Expr.substTyFvars_append]
  exact hsecond

/-- Closing generated names and then changing the source needs no pointwise
fixing of the old protected set. Only the new opening avoids S's domain. -/
theorem AnnotationCompletion.generalise_closed_after_source (h : AnnotationCompletion Q input output) {names : List Nat}
    (hnd : names.Nodup) (hQ : ∀ name ∈ names, name ∉ Q)
    (hb : output.TyBvarBounded 0) (S : Subst)
    (hlc : ∀ p ∈ S, p.2.IsLC)
    (hscope : ∀ q ∈ Q, ∀ v ∈ (S.onTy (.fvar q)).freeVars, v ∈ Q') :
    ∃ L, ∀ Xs, FreshNames L names.length Xs →
      AnnotationCompletion Q' (input.substTyFvars S)
        (((output.closeTyVars names).substTyFvars S).openTyVars Xs) := by
  refine ⟨names ++ S.map Prod.fst, ?_⟩
  intro Xs hf
  have hXs : FreshNames names names.length Xs :=
    ⟨hf.length, hf.nodup, fun x hx hm => hf.avoid x hx (List.mem_append_left _ hm)⟩
  have hS : ∀ p ∈ S, p.1 ∉ Xs := by
    intro p hp hv
    exact hf.avoid p.1 hv (List.mem_append_right _ (List.mem_map.mpr ⟨p, hp, rfl⟩))
  have ht := (h.generalise_closed hnd hQ hb Xs hXs).onSubst_source S hlc hscope
  simpa only [Expr.substTyFvars_openTyVars_lc _ hlc hS] using ht


/-- A cofinite signed completion transports without fixing the old scope. Only
new opening names, chosen outside S's domain, stay fixed in the child scope. -/
theorem AnnotationCompletion.signatureBinding_onSubst_source
    {Q Q' : List Nat} {input : InferInput} {rhsOut : Expr} {ann : BindingAnn} {M : PolyTy} {avoid : List Nat}
    (h : ∀ Xs, FreshNames avoid M.paramCount Xs →
      AnnotationCompletion (Q ++ Xs.take ann.paramCount) (input.openTyVars (Xs.take ann.paramCount))
        (rhsOut.openTyVars Xs))
    (S : Subst) (hlc : ∀ p ∈ S, p.2.IsLC)
    (hscope : ∀ q ∈ Q, ∀ v ∈ (S.onTy (.fvar q)).freeVars, v ∈ Q') :
    ∃ avoid', ∀ Xs, FreshNames avoid' M.paramCount Xs →
      AnnotationCompletion (Q' ++ Xs.take ann.paramCount)
        ((input.substTyFvars S).openTyVars (Xs.take ann.paramCount))
        ((rhsOut.substTyFvars S).openTyVars Xs) := by
  refine ⟨avoid ++ S.map Prod.fst, ?_⟩
  intro Xs hf
  have hXs : FreshNames avoid M.paramCount Xs :=
    ⟨hf.length, hf.nodup, fun x hx hm => hf.avoid x hx (List.mem_append_left _ hm)⟩
  have hS : ∀ p ∈ S, p.1 ∉ Xs := by
    intro p hp hv
    exact hf.avoid p.1 hv (List.mem_append_right _ (List.mem_map.mpr ⟨p, hp, rfl⟩))
  have hsmall : ∀ p ∈ S, p.1 ∉ Xs.take ann.paramCount :=
    fun p hp hv => hS p hp (List.mem_of_mem_take hv)
  have ht := (h Xs hXs).onSubst_source S hlc
    (K' := Q' ++ Xs.take ann.paramCount) (fun q hq v hv => by
      rcases List.mem_append.mp hq with hq | hq
      · exact List.mem_append_left _ (hscope q hq v hv)
      · rw [Subst.fixes_of_dom_avoids hsmall q hq] at hv
        exact List.mem_append_right _ ((List.mem_singleton.mp hv) ▸ hq))
  simpa only [InferInput.substTyFvars_openTyVars _ hlc hsmall,
    Expr.substTyFvars_openTyVars_lc _ hlc hS] using ht

/-- The generated signature certificate supplies exactly the prefix/full-block
length correspondence needed by the cofinite completion constructor. -/
theorem BindingAnn.SignatureCompletion.cofinite_completes
    {ann : BindingAnn} {written names Q : List Nat} {ty : Ty} {M : PolyTy}
    {input : InferInput} {output : Expr}
    (hcomp : ann.SignatureCompletion written ty M names)
    (h : AnnotationCompletion (Q ++ written) (input.openTyVars written) output)
    (hnd : names.Nodup) (hQ : ∀ name ∈ names, name ∉ Q)
    (hsource : ∀ v ∈ input.rigidVars, v ∈ Q) (hb : output.TyBvarBounded 0) :
    ∃ L, ∀ Xs, FreshNames L M.paramCount Xs →
      AnnotationCompletion (Q ++ Xs.take ann.paramCount) (input.openTyVars (Xs.take ann.paramCount))
        ((output.closeTyVars names).openTyVars Xs) := by
  cases hcomp with
  | complete hlen _ =>
    obtain ⟨L, hgen⟩ := h.generalise_opened (G := []) (by simpa using hnd)
      (by simpa using hQ) hsource hb
    refine ⟨L, ?_⟩
    intro Xs hf
    simpa only [List.append_nil, BindingAnn.paramCount, hlen] using
      hgen Xs (by simpa only [List.length_nil, Nat.add_zero, hlen] using hf)
  | partialSignature hlen _ =>
    obtain ⟨L, hgen⟩ := h.generalise_opened hnd hQ hsource hb
    refine ⟨L, ?_⟩
    intro Xs hf
    simpa only [BindingAnn.paramCount, hlen] using
      hgen Xs (by simpa only [List.length_append] using hf)

/-- Opening follows the pointwise images of its provisional roots. No
freshness, injectivity, or literal domain avoidance is required. -/
theorem Subst.onTy_openVarsFrom_of_images {S : Subst} {roots resolved : List Nat}
    (hlc : ∀ p ∈ S, p.2.IsLC)
    (himages : roots.map (fun x => S.onTy (.fvar x)) = resolved.map Ty.fvar)
    (ty : Ty) (depth : Nat) :
    S.onTy (Ty.openVarsFrom depth roots ty) = Ty.openVarsFrom depth resolved (S.onTy ty) := by
  induction ty using Ty.rec_strong with
  | prim p => simp only [Ty.openVarsFrom, Ty.instantiate, Subst.onTy_prim]
  | bvar i =>
    simp only [Subst.onTy_bvar, Ty.openVarsFrom, Ty.instantiate]
    by_cases hi : i < depth
    · simp only [if_pos hi, Subst.onTy_bvar]
    · simp only [if_neg hi]
      have hg := congrArg (fun ts : List Ty => ts[i - depth]?) himages
      cases hr : roots[i - depth]? <;> cases hd : resolved[i - depth]?
      · exact Subst.onTy_bvar
      · simp only [List.getElem?_map, hr, hd, Option.map_none, Option.map_some] at hg
        cases hg
      · simp only [List.getElem?_map, hr, hd, Option.map_none, Option.map_some] at hg
        cases hg
      · simp only [List.getElem?_map, hr, hd, Option.map_some] at hg
        exact Option.some.inj hg
  | fvar v =>
    change S.onTy (.fvar v) = Ty.openVarsFrom depth resolved (S.onTy (.fvar v))
    exact (Ty.instantiate_eq_self_of_lc (Subst.onTy_lc hlc .fvar)).symm
  | arrow a b iha ihb =>
    simp only [Ty.openVarsFrom, Ty.instantiate, Subst.onTy_arrow] at *
    exact congrArg₂ Ty.arrow iha ihb
  | customTy name args ih =>
    simp only [Ty.openVarsFrom, Ty.instantiate, TyList.instantiate_eq_map,
      Subst.onTy_customTy, List.map_map]
    congr 1
    exact List.map_congr_left (fun t ht => ih t ht)

theorem Subst.onTy_openVars_of_images {S : Subst} {roots resolved : List Nat}
    (hlc : ∀ p ∈ S, p.2.IsLC)
    (himages : roots.map (fun x => S.onTy (.fvar x)) = resolved.map Ty.fvar) {ty : Ty} :
    S.onTy (Ty.openVars roots ty) = Ty.openVars resolved (S.onTy ty) := by
  simpa only [Ty.openVarsFrom, Nat.not_lt_zero, if_false, Nat.sub_zero, Ty.openVars] using
    Subst.onTy_openVarsFrom_of_images hlc himages ty 0

mutual
theorem TyTemplate.substTyFvars_openTyVarsFrom_of_images (template : TyTemplate) {S : Subst} {roots resolved : List Nat}
    (hlc : ∀ p ∈ S, p.2.IsLC)
    (himages : roots.map (fun x => S.onTy (.fvar x)) = resolved.map Ty.fvar) (depth : Nat) :
    (template.openTyVarsFrom depth roots).substTyFvars S =
      (template.substTyFvars S).openTyVarsFrom depth resolved := by
  cases template with
  | fixed ty => exact congrArg TyTemplate.fixed (Subst.onTy_openVarsFrom_of_images hlc himages ty depth)
  | hole => rfl
  | arrow a b =>
    simp only [TyTemplate.openTyVarsFrom, TyTemplate.substTyFvars,
      a.substTyFvars_openTyVarsFrom_of_images hlc himages depth,
      b.substTyFvars_openTyVarsFrom_of_images hlc himages depth]
  | custom name args =>
    exact congrArg (TyTemplate.custom name) (templateList_open_subst_of_images args hlc himages depth)
private theorem templateList_open_subst_of_images (templates : List TyTemplate) {S : Subst} {roots resolved : List Nat}
    (hlc : ∀ p ∈ S, p.2.IsLC)
    (himages : roots.map (fun x => S.onTy (.fvar x)) = resolved.map Ty.fvar) (depth : Nat) :
    substTemplateList S (openTemplateList depth roots templates) =
      openTemplateList depth resolved (substTemplateList S templates) := by
  cases templates with
  | nil => rfl
  | cons t ts =>
    simp only [substTemplateList, openTemplateList,
      t.substTyFvars_openTyVarsFrom_of_images hlc himages depth,
      templateList_open_subst_of_images ts hlc himages depth]
end

/-- Factor an ordinary annotation check against the transformed source. Only
raw-source allocation bounds and independent target protection are required. -/

theorem BindingAnn.substTyFvars_openTyVarsFrom_of_images (ann : BindingAnn) {subst : Subst} {roots resolved : List Nat}
    (hlc : ∀ pair ∈ subst, pair.2.IsLC) (himages : roots.map (fun x => subst.onTy (.fvar x)) = resolved.map Ty.fvar) (d : Nat) :
    (ann.openTyVarsFrom d roots).substTyFvars subst = (ann.substTyFvars subst).openTyVarsFrom d resolved := by
  cases ann with
  | absent => rfl
  | complete scheme =>
      exact congrArg (fun t => BindingAnn.complete ⟨scheme.paramCount, t⟩)
        (Subst.onTy_openVarsFrom_of_images hlc himages scheme.body (d + scheme.paramCount))
  | template t => exact congrArg BindingAnn.template (t.substTyFvars_openTyVarsFrom_of_images hlc himages d)
  | partialForall n t =>
      exact congrArg (BindingAnn.partialForall n) (t.substTyFvars_openTyVarsFrom_of_images hlc himages (d + n))

mutual
/-- Source substitution commutes with opening through nested written signature
binders. LC ranges need not avoid the opened names. -/
theorem InferInput.substTyFvars_openTyVarsFrom_of_images (input : InferInput) {subst : Subst} {roots resolved : List Nat}
    (hlc : ∀ pair ∈ subst, pair.2.IsLC) (himages : roots.map (fun x => subst.onTy (.fvar x)) = resolved.map Ty.fvar) (d : Nat) :
    (input.openTyVarsFrom d roots).substTyFvars subst = (input.substTyFvars subst).openTyVarsFrom d resolved := by
  cases input with
  | primLit | primBinOp | var | ctor => rfl
  | lambda ann body =>
      simp only [InferInput.openTyVarsFrom, InferInput.substTyFvars,
        body.substTyFvars_openTyVarsFrom_of_images hlc himages d]
      congr 1
      cases ann with
      | none => rfl
      | some template => exact congrArg some (template.substTyFvars_openTyVarsFrom_of_images hlc himages d)
  | app f a => simp only [InferInput.openTyVarsFrom, InferInput.substTyFvars,
      f.substTyFvars_openTyVarsFrom_of_images hlc himages d, a.substTyFvars_openTyVarsFrom_of_images hlc himages d]
  | letIn ann rhs body => simp only [InferInput.openTyVarsFrom, InferInput.substTyFvars,
      BindingAnn.paramCount_substTyFvars, ann.substTyFvars_openTyVarsFrom_of_images hlc himages d,
      rhs.substTyFvars_openTyVarsFrom_of_images hlc himages (d + ann.paramCount),
      body.substTyFvars_openTyVarsFrom_of_images hlc himages d]
  | match_ scrut branches => simp only [InferInput.openTyVarsFrom, InferInput.substTyFvars,
      scrut.substTyFvars_openTyVarsFrom_of_images hlc himages d,
      substInputBranches_openInputBranches_of_images branches hlc himages d]
  | letRec anns bindings body =>
      simp only [InferInput.openTyVarsFrom, InferInput.substTyFvars,
        body.substTyFvars_openTyVarsFrom_of_images hlc himages d,
        substInputBindings_openInputBindings_of_images bindings anns hlc himages d, List.map_map]
      congr 1
      apply List.map_congr_left
      intro ann _
      exact ann.substTyFvars_openTyVarsFrom_of_images hlc himages d
termination_by sizeOf input

theorem substInputBranches_openInputBranches_of_images (branches : List (MatchPattern × InferInput)) {subst : Subst} {roots resolved : List Nat}
    (hlc : ∀ pair ∈ subst, pair.2.IsLC) (himages : roots.map (fun x => subst.onTy (.fvar x)) = resolved.map Ty.fvar) (d : Nat) :
    substInputBranches subst (openInputBranches d roots branches) = openInputBranches d resolved (substInputBranches subst branches) := by
  cases branches with
  | nil => rfl
  | cons pair rest =>
      rcases pair with ⟨pat, body⟩
      simp only [openInputBranches, substInputBranches, body.substTyFvars_openTyVarsFrom_of_images hlc himages d,
        substInputBranches_openInputBranches_of_images rest hlc himages d]
termination_by sizeOf branches

theorem substInputBindings_openInputBindings_of_images (bindings : List InferInput) (anns : List BindingAnn)
    {subst : Subst} {roots resolved : List Nat}
    (hlc : ∀ pair ∈ subst, pair.2.IsLC) (himages : roots.map (fun x => subst.onTy (.fvar x)) = resolved.map Ty.fvar) (d : Nat) :
    substInputBindings subst (openInputBindings d roots anns bindings) =
      openInputBindings d resolved (anns.map (BindingAnn.substTyFvars subst)) (substInputBindings subst bindings) := by
  cases bindings with
  | nil => rfl
  | cons body rest =>
      cases anns with
      | nil => simp only [openInputBindings, substInputBindings, List.map_nil,
          body.substTyFvars_openTyVarsFrom_of_images hlc himages d,
          substInputBindings_openInputBindings_of_images rest [] hlc himages d]
      | cons ann anns => simp only [openInputBindings, substInputBindings, List.map_cons,
          BindingAnn.paramCount_substTyFvars, body.substTyFvars_openTyVarsFrom_of_images hlc himages (d + ann.paramCount),
          substInputBindings_openInputBindings_of_images rest anns hlc himages d]
termination_by sizeOf bindings
end

theorem InferInput.substTyFvars_openTyVars_of_images (input : InferInput) {subst : Subst} {roots resolved : List Nat}
    (hlc : ∀ pair ∈ subst, pair.2.IsLC) (himages : roots.map (fun x => subst.onTy (.fvar x)) = resolved.map Ty.fvar) :
    (input.openTyVars roots).substTyFvars subst = (input.substTyFvars subst).openTyVars resolved :=
  input.substTyFvars_openTyVarsFrom_of_images hlc himages 0

private theorem scope_branch_rigid_mem {bs : List (MatchPattern × InferInput)} {b : MatchPattern × InferInput}
    (hb : b ∈ bs) {v : Nat} (hv : v ∈ b.2.rigidVars) : v ∈ rigidBranchVars bs := by
  induction bs with
  | nil => cases hb
  | cons head tail ih =>
    exact (List.mem_cons.mp hb).elim (fun heq => List.mem_append_left _ (heq ▸ hv))
      (fun hb => List.mem_append_right _ (ih hb))

private theorem scope_binding_rigid_mem {bs : List InferInput} {b : InferInput}
    (hb : b ∈ bs) {v : Nat} (hv : v ∈ b.rigidVars) : v ∈ rigidBindingVars bs := by
  induction bs with
  | nil => cases hb
  | cons head tail ih =>
    exact (List.mem_cons.mp hb).elim (fun heq => List.mem_append_left _ (heq ▸ hv))
      (fun hb => List.mem_append_right _ (ih hb))
private theorem scope_ann_nil (ann : BindingAnn) : ann.substTyFvars [] = ann :=
  ann.substTyFvars_eq_self_of_fixes (fun _ _ => rfl)
private theorem scope_ann_nil_fun : BindingAnn.substTyFvars [] = id := funext scope_ann_nil
private theorem scope_poly_nil : Subst.onPolyTy [] = id := funext Subst.onPolyTy_nil
/-- The independent scope index protects authored source variables only.
Unused index entries do not constrain candidate types or the context. -/
theorem InputTyping.scope_restrict {Q P : List Nat} {ctx : Ctx} {input : InferInput} {ty : Ty}
    (h : InputTyping Q ctx input ty) (hscope : ∀ v ∈ input.rigidVars, v ∈ P) : InputTyping P ctx input ty := by
  induction h using InputTyping.rec
      (motive_2 := fun _ ctx branch st rt _ => ∀ {P : List Nat},
        (∀ v ∈ branch.2.rigidVars, v ∈ P) → BranchTyping InputTyping P ctx branch st rt) generalizing P with
  | complete hemb _ ht =>
    exact .complete hemb (fun v hv => hscope v ((InferInput.toCore_rigidVars _ hemb v).mpr hv)) ht
  | primLit ht => exact .primLit ht
  | primBinOp ht => exact .primBinOp ht
  | @lambda ann Q ctx body bodyTy param hlc hfit _ _ ih =>
    refine .lambda hlc hfit ?_ (ih (fun v hv => hscope v (List.mem_append_right _ hv)))
    intro t heq v hv
    subst ann
    exact hscope v (List.mem_append_left _ hv)
  | app _ _ ihf ihx =>
    exact .app (ihf (fun v hv => hscope v (List.mem_append_left _ hv)))
      (ihx (fun v hv => hscope v (List.mem_append_right _ hv)))
  | @letIn ann Q ctx rhs body bodyTy M L hM _ hfit _ _ ihr ihb =>
    refine .letIn (L := L) hM ?_ hfit ?_ (ihb (fun v hv => hscope v (List.mem_append_right _ hv)))
    · intro t heq v hv
      subst ann
      exact hscope v (List.mem_append_left _ (List.mem_append_left _ hv))
    · intro Xs hf
      exact ihr Xs hf (fun v hv => hscope v (List.mem_append_left _ (List.mem_append_right _ hv)))
  | @letSignature Q ctx body bodyTy ann rhs M L hM _ _ hfit _ _ ihr ihb =>
    have ha : ∀ v ∈ ann.rigidVars, v ∈ P :=
      fun v hv => hscope v (List.mem_append_left _ (List.mem_append_left _ hv))
    have hr : ∀ v ∈ rhs.rigidVars, v ∈ P :=
      fun v hv => hscope v (List.mem_append_left _ (List.mem_append_right _ hv))
    refine .letSignature (L := L) hM ha hr hfit ?_
      (ihb (fun v hv => hscope v (List.mem_append_right _ hv)))
    intro Xs hf
    exact ihr Xs hf (rhs.openTyVars_scope hr (Xs.take ann.paramCount))
  | letRec hgroups hwf hp hG hAnn hRhs hFits _ _ _ ihMono ihPoly ihBody =>
    expose_names
    have hAnnP : ∀ ann ∈ anns, ∀ v ∈ ann.rigidVars, v ∈ P := by
      intro ann ha v hv
      exact hscope v (List.mem_append_left _ (List.mem_append_left _
        (List.mem_flatMap.mpr ⟨ann, ha, hv⟩)))
    have hRhsP : ∀ rhs ∈ bindings, ∀ v ∈ rhs.rigidVars, v ∈ P := by
      intro rhs hr v hv
      have hmem := scope_binding_rigid_mem hr hv
      exact hscope v (List.mem_append_left _ (List.mem_append_right _ hmem))
    let avoid := P ++ ctx_1.env.freeVars ++ G ++ specs.flatMap RecSpec.freeVars
    obtain ⟨W, hWlen, hWnd, hWavoid⟩ := exists_fresh_names avoid G.length
    have hGW : ∀ g ∈ G, g ∉ W := by
      intro g hg hw
      exact hWavoid g hw (by simp only [avoid, List.mem_append]; tauto)
    have hWmono : ∀ t, .mono t ∈ specs → ∀ w ∈ W, w ∉ t.freeVars := by
      intro t ht w hw hv
      exact hWavoid w hw (by simp only [avoid, List.mem_append]; right; exact List.mem_flatMap.mpr ⟨.mono t, ht, hv⟩)
    have hS : ∀ p ∈ ([] : Subst), p.2.IsLC := by simp
    have hdom : ∀ p ∈ ([] : Subst), p.1 ∉ W := by simp
    have hran : ∀ p ∈ ([] : Subst), ∀ v ∈ p.2.freeVars, v ∉ W := by simp
    let specs' := specs.map (fun spec => RecSpec.onSubstSource [] (RecSpec.onSubst (G.zip (W.map Ty.fvar)) spec))
    let prefixes' := prefixes.map (recRenameNames G W)
    let L' := G ++ W ++ L
    have hannsLen : anns.length = specs.length := by
      have hh := congrArg List.length hwf.anns_eq
      simpa using hh.symm
    have hpData := fun i hi => hp.get hannsLen (i := i) hi
    have hcompleted := recCompletedSchemes_subst_fresh_pool hS hWlen hwf.nodup hWnd hGW hWmono hdom hran hwf.mono_lc hpData
    have hbodyCtx : recBodyCtx ctx_1 specs' prefixes' W = recBodyCtx ctx_1 specs prefixes G := by
      simp only [recBodyCtx]
      simp only [scope_poly_nil, List.map_id] at hcompleted
      rw [hcompleted]
    have oldFresh : ∀ Xs, FreshNames (W ++ L') W.length Xs → FreshNames (G ++ L) G.length Xs := by
      intro Xs hf
      refine ⟨hf.length.trans hWlen, hf.nodup, ?_⟩
      intro v hv hm
      exact hf.avoid v hv (by simp only [L', List.mem_append] at hm ⊢; tauto)
    have hGXs : ∀ Xs, FreshNames (W ++ L') W.length Xs → ∀ g ∈ G, g ∉ Xs := by
      intro Xs hf g hg hx
      exact hf.avoid g hx (by simp only [L', List.mem_append]; tauto)
    have hWXs : ∀ Xs, FreshNames (W ++ L') W.length Xs → ∀ w ∈ W, w ∉ Xs := by
      intro Xs hf w hw hx
      exact hf.avoid w hx (List.mem_append_left _ hw)
    refine InputTyping.letRec (specs := specs') (groups := groups) (prefixes := prefixes') (G := W) (L := L')
      hgroups ?_ ?_ ?_ hAnnP hRhsP ?_ ?_ ?_ ?_
    · simpa only [scope_ann_nil_fun, List.map_id] using
        RecSpecs.WF.subst_fresh_pool hwf hS hWnd
    · simpa only [scope_ann_nil_fun, List.map_id] using
        hp.subst_fresh_pool (S := []) hWlen hWnd
    · intro w hw hm
      exact hWavoid w hw (by simp only [avoid, List.mem_append] at hm ⊢; tauto)
    · intro stage component hs Xs hf member hm rhs ann names ty hr ha hn ht
      rw [List.getElem?_map] at hn ht
      obtain ⟨names0, hn0, rfl⟩ := Option.map_eq_some_iff.mp hn
      obtain ⟨spec0, ht0, heq⟩ := Option.map_eq_some_iff.mp ht
      cases spec0 with
      | poly scheme => cases heq
      | mono ty0 =>
        cases heq
        obtain ⟨_, _, hsub⟩ := hp.member member ann names0 ha hn0
        have hrename := Ty.renameG_subst_fresh_pool (hwf.mono_lc ty0 (List.mem_of_getElem? ht0)) hS hWlen hwf.nodup hWnd hGW
          (hWmono ty0 (List.mem_of_getElem? ht0)) hdom hran (hf.length.trans hWlen) (hGXs Xs hf)
          (hWXs Xs hf) (by simp)
        simp only [Subst.onTy_nil] at hrename
        change ann.RecFits (recRenameNames W Xs (recRenameNames G W names0)) (Ty.renameG W Xs (Ty.renameG G W ty0))
        rw [recRenameNames_composition hWlen (hf.length.trans hWlen) hWnd hsub, hrename]
        exact hFits stage component hs Xs (oldFresh Xs hf) member hm rhs ann names0 ty0 hr ha hn0 ht0
    · intro stage component hs Xs hf member hm rhs ann names ty hr ha hn ht
      rw [List.getElem?_map] at hn ht
      obtain ⟨names0, hn0, rfl⟩ := Option.map_eq_some_iff.mp hn
      obtain ⟨spec0, ht0, heq⟩ := Option.map_eq_some_iff.mp ht
      cases spec0 with
      | poly scheme => cases heq
      | mono ty0 =>
        cases heq
        obtain ⟨_, _, hsub⟩ := hp.member member ann names0 ha hn0
        have hc := ihMono stage component hs Xs (oldFresh Xs hf) member hm rhs ann names0 ty0 hr ha hn0 ht0
          (P := P ++ Xs) (fun v hv => by
            rcases InferInput.rigidVars_openTyVarsFrom hv with hv | hv
            · exact List.mem_append_left _ (hRhsP rhs (List.mem_of_getElem? hr) v hv)
            · exact List.mem_append_right _ (recRenameNames_mem (hf.length.trans hWlen) hsub v hv))
        have hstage := recStageSchemes_subst_fresh_pool (done := (groups.take stage).flatten) hS hWlen hwf.nodup hWnd hGW hWmono hdom hran
          hwf.mono_lc hpData (hf.length.trans hWlen) (hGXs Xs hf) (hWXs Xs hf) (by simp)
        simp only [scope_poly_nil, List.map_id] at hstage
        have hstageCtx : recStageCtx ctx_1 specs' prefixes' (groups.take stage).flatten W Xs =
            recStageCtx ctx_1 specs prefixes (groups.take stage).flatten G Xs := by
          simp only [recStageCtx]
          rw [hstage]
        have hrename := Ty.renameG_subst_fresh_pool (hwf.mono_lc ty0 (List.mem_of_getElem? ht0)) hS hWlen hwf.nodup hWnd hGW
          (hWmono ty0 (List.mem_of_getElem? ht0)) hdom hran (hf.length.trans hWlen) (hGXs Xs hf)
          (hWXs Xs hf) (by simp)
        simp only [Subst.onTy_nil] at hrename
        change InputTyping (P ++ Xs) (recStageCtx ctx_1 specs' prefixes' (groups.take stage).flatten W Xs)
          (rhs.openTyVars (recRenameNames W Xs (recRenameNames G W names0))) (Ty.renameG W Xs (Ty.renameG G W ty0))
        rw [hstageCtx, recRenameNames_composition hWlen (hf.length.trans hWlen) hWnd hsub, hrename]
        exact hc
    · intro member rhs scheme hr hs Ys hy
      rw [List.getElem?_map] at hs
      obtain ⟨spec0, hs0, heq⟩ := Option.map_eq_some_iff.mp hs
      cases spec0 with
      | mono ty => cases heq
      | poly scheme0 =>
        cases heq
        have hy0 : FreshNames L scheme0.paramCount Ys :=
          ⟨hy.length, hy.nodup, fun y hy' hl => hy.avoid y hy' (by simp only [L', List.mem_append]; tauto)⟩
        rw [hbodyCtx]
        exact ihPoly member rhs scheme0 hr hs0 Ys hy0 (rhs.openTyVars_scope (hRhsP rhs (List.mem_of_getElem? hr)) Ys)
    · rw [hbodyCtx]
      exact ihBody (fun v hv => hscope v (List.mem_append_right _ hv))
  | var hl ha hi => exact .var hl ha hi
  | ctor hl ha hi => exact .ctor hl ha hi
  | match_ _ hne _ ihs ihbs =>
    refine .match_ (ihs (fun v hv => hscope v (List.mem_append_left _ hv))) hne ?_
    intro b hb
    exact ihbs b hb (fun v hv => hscope v
      (List.mem_append_right _ (scope_branch_rigid_mem hb hv)))
  | named hs _ ih =>
    rename_i P hscope
    exact .named hs (ih hscope)
  | wildcard _ ih =>
    rename_i P hscope
    exact .wildcard (ih hscope)

/-- Completion scopes only authored input leaves, independently of output holes. -/
theorem AnnotationCompletion.scope_restrict {Q P : List Nat} {input : InferInput} {output : Expr}
    (h : AnnotationCompletion Q input output) (hscope : ∀ v ∈ input.rigidVars, v ∈ P) :
    AnnotationCompletion P input output := by
  induction h using AnnotationCompletion.rec
      (motive_2 := fun _ branches outputs _ => ∀ {P : List Nat},
        (∀ v ∈ rigidBranchVars branches, v ∈ P) → CompletedBranches AnnotationCompletion P branches outputs)
      generalizing P with
  | complete hemb _ =>
    exact .complete hemb (fun v hv => hscope v ((InferInput.toCore_rigidVars _ hemb v).mpr hv))
  | @lambda ann Q body completed param hfit _ _ ih =>
    refine .lambda hfit ?_ (ih (fun v hv => hscope v (List.mem_append_right _ hv)))
    intro t heq v hv
    subst ann
    exact hscope v (List.mem_append_left _ hv)
  | app _ _ ihf ihx =>
    exact .app (ihf (fun v hv => hscope v (List.mem_append_left _ hv)))
      (ihx (fun v hv => hscope v (List.mem_append_right _ hv)))
  | @letIn ann Q rhs body bodyOut rhsOut M L _ hfit _ _ ihr ihb =>
    refine .letIn (L := L) ?_ hfit ?_ (ihb (fun v hv => hscope v (List.mem_append_right _ hv)))
    · intro t heq v hv
      subst ann
      exact hscope v (List.mem_append_left _ (List.mem_append_left _ hv))
    · intro Xs hf
      exact ihr Xs hf (fun v hv => hscope v (List.mem_append_left _ (List.mem_append_right _ hv)))
  | @letSignature Q body bodyOut ann rhs rhsOut M L _ _ hfit _ _ ihr ihb =>
    have ha : ∀ v ∈ ann.rigidVars, v ∈ P :=
      fun v hv => hscope v (List.mem_append_left _ (List.mem_append_left _ hv))
    have hr : ∀ v ∈ rhs.rigidVars, v ∈ P :=
      fun v hv => hscope v (List.mem_append_left _ (List.mem_append_right _ hv))
    refine .letSignature (L := L) ha hr hfit ?_
      (ihb (fun v hv => hscope v (List.mem_append_right _ hv)))
    intro Xs hf
    exact ihr Xs hf (rhs.openTyVars_scope hr (Xs.take ann.paramCount))
  | match_ _ _ ihs ihbs =>
    exact .match_ (ihs (fun v hv => hscope v (List.mem_append_left _ hv)))
      (ihbs (fun v hv => hscope v (List.mem_append_right _ hv)))
  | letRec ha hb ho _ _ hfit _ _ ihr ihb =>
    expose_names
    have hAnnP : ∀ ann ∈ anns, ∀ v ∈ ann.rigidVars, v ∈ P := by
      intro ann ha v hv
      exact hscope v (List.mem_append_left _ (List.mem_append_left _
        (List.mem_flatMap.mpr ⟨ann, ha, hv⟩)))
    have hRhsP : ∀ rhs ∈ bindings, ∀ v ∈ rhs.rigidVars, v ∈ P := by
      intro rhs hr v hv
      exact hscope v (List.mem_append_left _ (List.mem_append_right _ (scope_binding_rigid_mem hr hv)))
    refine .letRec ha hb ho hAnnP hRhsP hfit ?_
      (ihb (fun v hv => hscope v (List.mem_append_right _ hv)))
    intro member ann rhs output scheme ha hr ho hs Xs hf
    exact ihr member ann rhs output scheme ha hr ho hs Xs hf
      (rhs.openTyVars_scope (hRhsP rhs (List.mem_of_getElem? hr)) (Xs.take ann.paramCount))
  | nil => exact .nil
  | cons _ _ ihb iht =>
    rename_i P hscope
    exact .cons (ihb (fun v hv => hscope v (List.mem_append_left _ hv)))
      (iht (fun v hv => hscope v (List.mem_append_right _ hv)))

end

/-! ## RecOpening -/

section

structure RecOpening where
  written : List Nat
  expected : Option Ty

def RecOpening.empty : RecOpening := ⟨[], none⟩

/-- Allocate flexible written slots and partial expected shapes, without
changing scope or performing inference. Complete contracts are handled later. -/
inductive OpenRecAnn : Nat → BindingAnn → Nat → RecOpening → Prop
  | absent : OpenRecAnn frontier .absent frontier .empty
  | complete : OpenRecAnn frontier (.complete scheme) frontier .empty
  | template :
      template.allocate frontier = (next, ty) → ty.IsLC →
      OpenRecAnn frontier (.template template) next ⟨[], some ty⟩
  | partialForall :
      (template.openTyVarsFrom 0 (freshVars frontier count)).allocate (frontier + count) = (next, ty) →
      ty.IsLC →
      OpenRecAnn frontier (.partialForall count template) next ⟨freshVars frontier count, some ty⟩

/-- Scan the whole aligned annotation list; only selected indices allocate. -/
inductive OpenRecAnns (selected : List Nat) : Nat → Nat → List BindingAnn → Nat → List RecOpening → Prop
  | nil : OpenRecAnns selected index frontier [] frontier []
  | skip :
      index ∉ selected → OpenRecAnns selected (index + 1) frontier rest next openings →
      OpenRecAnns selected index frontier (ann :: rest) next (.empty :: openings)
  | cons :
      index ∈ selected → OpenRecAnn frontier ann middle opening →
      OpenRecAnns selected (index + 1) middle rest next openings →
      OpenRecAnns selected index frontier (ann :: rest) next (opening :: openings)

def openRecAnn (frontier : Nat) (ann : BindingAnn) :
    Option { result : Nat × RecOpening // OpenRecAnn frontier ann result.1 result.2 } :=
  match ann with
  | .absent => some ⟨(frontier, .empty), .absent⟩
  | .complete _ => some ⟨(frontier, .empty), .complete⟩
  | .template template =>
      let result := template.allocate frontier
      if hlc : result.2.bvarsBelow 0 = true then
        some ⟨(result.1, ⟨[], some result.2⟩), .template rfl ((Ty.bvarsBelow_iff _).mp hlc)⟩
      else none
  | .partialForall count template =>
      let written := freshVars frontier count
      let result := (template.openTyVarsFrom 0 written).allocate (frontier + count)
      if hlc : result.2.bvarsBelow 0 = true then
        some ⟨(result.1, ⟨written, some result.2⟩), .partialForall rfl ((Ty.bvarsBelow_iff _).mp hlc)⟩
      else none

def openRecAnns (selected : List Nat) (index frontier : Nat) (anns : List BindingAnn) :
    Option { result : Nat × List RecOpening // OpenRecAnns selected index frontier anns result.1 result.2 } :=
  match anns with
  | [] => some ⟨(frontier, []), .nil⟩
  | ann :: rest =>
      if hs : index ∈ selected then
        match openRecAnn frontier ann with
        | none => none
        | some ⟨(middle, opening), hhead⟩ =>
            match openRecAnns selected (index + 1) middle rest with
            | none => none
            | some ⟨(next, openings), htail⟩ =>
                some ⟨(next, opening :: openings), .cons hs hhead htail⟩
      else
        match openRecAnns selected (index + 1) frontier rest with
        | none => none
        | some ⟨(next, openings), htail⟩ =>
            some ⟨(next, .empty :: openings), .skip hs htail⟩

theorem OpenRecAnns.length (h : OpenRecAnns selected index frontier anns next openings) :
    openings.length = anns.length := by
  induction h with
  | nil => rfl
  | skip _ _ ih => exact congrArg Nat.succ ih
  | cons _ _ _ ih => exact congrArg Nat.succ ih

theorem OpenRecAnn.expected_lc (h : OpenRecAnn frontier ann next opening)
    (he : opening.expected = some ty) : ty.IsLC := by
  cases h with
  | absent | complete => cases he
  | template _ hlc => exact Option.some.inj he ▸ hlc
  | partialForall _ hlc => exact Option.some.inj he ▸ hlc

theorem OpenRecAnns.expected_lc (h : OpenRecAnns selected index frontier anns next openings) :
    ∀ opening ∈ openings, ∀ ty, opening.expected = some ty → ty.IsLC := by
  induction h with
  | nil => intro opening hm; cases hm
  | skip _ _ ih =>
    intro opening hm ty he
    rcases List.mem_cons.mp hm with rfl | hm
    · cases he
    · exact ih opening hm ty he
  | cons _ hhead _ ih =>
    intro opening hm ty he
    rcases List.mem_cons.mp hm with rfl | hm
    · exact hhead.expected_lc he
    · exact ih opening hm ty he


theorem OpenRecAnn.frontier_le (h : OpenRecAnn frontier ann next opening) : frontier ≤ next := by
  cases h with
  | absent | complete => exact Nat.le_refl _
  | @template next ty frontier template heq _ =>
    have hle := (template.allocate_bounds frontier).1
    rwa [heq] at hle
  | @partialForall next ty frontier count template heq _ =>
    have hle := ((template.openTyVarsFrom 0 (freshVars frontier count)).allocate_bounds (frontier + count)).1
    rw [heq] at hle
    exact (Nat.le_add_right _ _).trans hle

theorem OpenRecAnns.frontier_le (h : OpenRecAnns selected index frontier anns next openings) :
    frontier ≤ next := by
  induction h with
  | nil => exact Nat.le_refl _
  | skip _ _ ih => exact ih
  | cons _ hhead _ ih => exact hhead.frontier_le.trans ih

theorem OpenRecAnn.written_nodup (h : OpenRecAnn frontier ann next opening) : opening.written.Nodup := by
  cases h with
  | absent | complete | template => exact List.nodup_nil
  | partialForall => exact freshVars_nodup

theorem OpenRecAnn.written_length (h : OpenRecAnn frontier ann next opening) :
    opening.written.length = (match ann with | .partialForall n _ => n | _ => 0) := by
  cases h <;> simp [RecOpening.empty, freshVars_length]

theorem OpenRecAnn.written_range (h : OpenRecAnn frontier ann next opening) :
    ∀ v ∈ opening.written, frontier ≤ v ∧ v < next := by
  cases h with
  | absent | complete | template => intro v hv; cases hv
  | @partialForall next ty frontier count template heq hlc =>
    have hle := ((template.openTyVarsFrom 0 (freshVars frontier count)).allocate_bounds (frontier + count)).1
    rw [heq] at hle
    intro v hv
    exact ⟨freshVars_ge v hv, Nat.lt_of_lt_of_le (freshVars_lt v hv) hle⟩

theorem OpenRecAnns.written_range (h : OpenRecAnns selected index frontier anns next openings) :
    ∀ v ∈ openings.flatMap RecOpening.written, frontier ≤ v ∧ v < next := by
  induction h with
  | nil => intro v hv; cases hv
  | skip _ _ ih =>
    simpa only [List.flatMap_cons, RecOpening.empty, List.nil_append] using ih
  | cons _ hhead htail ih =>
    intro v hv
    rcases List.mem_append.mp hv with hv | hv
    · have hh := hhead.written_range v hv
      exact ⟨hh.1, Nat.lt_of_lt_of_le hh.2 htail.frontier_le⟩
    · have ht := ih v hv
      exact ⟨hhead.frontier_le.trans ht.1, ht.2⟩

theorem OpenRecAnns.written_nodup (h : OpenRecAnns selected index frontier anns next openings) :
    (openings.flatMap RecOpening.written).Nodup := by
  induction h with
  | nil => exact List.nodup_nil
  | skip _ _ ih =>
    simpa only [List.flatMap_cons, RecOpening.empty, List.nil_append] using ih
  | cons _ hhead htail ih =>
    refine List.nodup_append.mpr ⟨hhead.written_nodup, ih, ?_⟩
    intro v hv w hw heq
    have hh := hhead.written_range v hv
    have ht := htail.written_range w hw
    omega

theorem OpenRecAnn.expected_below (h : OpenRecAnn frontier ann next opening)
    (hraw : ∀ v ∈ ann.rigidVars, v < frontier)
    (he : opening.expected = some ty) : Ty.BelowFvars next ty := by
  cases h with
  | absent | complete => cases he
  | @template next target frontier template heq _ =>
    have hb := (template.allocate_bounds frontier).2 hraw
    rw [heq] at hb
    exact Option.some.inj he ▸ hb
  | @partialForall next target frontier count template heq _ =>
    have hopen : ∀ v ∈ (template.openTyVarsFrom 0 (freshVars frontier count)).rigidVars,
        v < frontier + count := by
      intro v hv
      have hmem := template.openTyVarsFrom_scope (K := template.rigidVars) (fun _ h => h)
        0 (freshVars frontier count) v hv
      rcases List.mem_append.mp hmem with hmem | hmem
      · have hvold := hraw v hmem
        omega
      · exact freshVars_lt v hmem
    have hb := ((template.openTyVarsFrom 0 (freshVars frontier count)).allocate_bounds (frontier + count)).2 hopen
    rw [heq] at hb
    exact Option.some.inj he ▸ hb

theorem OpenRecAnns.expected_below (h : OpenRecAnns selected index frontier anns next openings)
    (hraw : ∀ ann ∈ anns, ∀ v ∈ ann.rigidVars, v < frontier) :
    ∀ opening ∈ openings, ∀ ty, opening.expected = some ty → Ty.BelowFvars next ty := by
  induction h with
  | nil => intro opening hm; cases hm
  | skip _ _ ih =>
    intro opening hm ty he
    rcases List.mem_cons.mp hm with rfl | hm
    · cases he
    · exact ih (fun ann ha => hraw ann (List.mem_cons_of_mem _ ha)) opening hm ty he
  | cons _ hhead htail ih =>
    intro opening hm ty he
    rcases List.mem_cons.mp hm with rfl | hm
    · exact (hhead.expected_below (hraw _ List.mem_cons_self) he).mono htail.frontier_le
    · exact ih (fun ann ha v hv => Nat.lt_of_lt_of_le
        (hraw ann (List.mem_cons_of_mem _ ha) v hv) hhead.frontier_le) opening hm ty he

theorem OpenRecAnns.expectedTypes_lc (h : OpenRecAnns selected index frontier anns next openings) :
    ∀ ty ∈ openings.filterMap RecOpening.expected, ty.IsLC := by
  intro ty hm
  obtain ⟨opening, hopening, he⟩ := List.mem_filterMap.mp hm
  exact h.expected_lc opening hopening ty he

theorem OpenRecAnns.expectedTypes_below (h : OpenRecAnns selected index frontier anns next openings)
    (hraw : ∀ ann ∈ anns, ∀ v ∈ ann.rigidVars, v < frontier) :
    ∀ ty ∈ openings.filterMap RecOpening.expected, Ty.BelowFvars next ty := by
  intro ty hm
  obtain ⟨opening, hopening, he⟩ := List.mem_filterMap.mp hm
  exact h.expected_below hraw opening hopening ty he



/-- Read a list of bare variable images without changing their order. -/
private def recWrittenNames : List Ty → Option (List Nat)
  | [] => some []
  | .fvar name :: rest => (recWrittenNames rest).map (name :: ·)
  | _ :: _ => none

private theorem recWrittenNames_sound {images : List Ty} {names : List Nat}
    (h : recWrittenNames images = some names) : names.map Ty.fvar = images := by
  induction images generalizing names with
  | nil => cases h; rfl
  | cons ty rest ih =>
      cases ty with
      | fvar name =>
          simp only [recWrittenNames, Option.map_eq_some_iff] at h
          obtain ⟨tail, ht, rfl⟩ := h
          simpa only [List.map_cons] using congrArg (Ty.fvar name :: ·) (ih ht)
      | prim | arrow | bvar | customTy => cases h

private theorem recWrittenNames_map (names : List Nat) :
    recWrittenNames (names.map Ty.fvar) = some names := by
  induction names with
  | nil => rfl
  | cons name rest ih => simp only [List.map_cons, recWrittenNames, ih, Option.map_some]

/-- Validate one member's normalized prefix. Sharing roots with another member
is permitted; this call checks distinctness only within the supplied prefix. -/
def resolveRecWritten (images : List Ty) (forbidden : List Nat) :
    Option { names : List Nat // names.map Ty.fvar = images ∧ names.Nodup ∧
      ∀ name ∈ names, name ∉ forbidden } :=
  match hp : recWrittenNames images with
  | none => none
  | some names =>
      if hnd : names.Nodup then
        if havoid : ∀ name ∈ names, name ∉ forbidden then
          some ⟨names, recWrittenNames_sound hp, hnd, havoid⟩
        else none
      else none

theorem resolveRecWritten_isSome_iff : (resolveRecWritten images forbidden).isSome ↔
    ∃ names : List Nat, names.map Ty.fvar = images ∧ names.Nodup ∧
      ∀ name ∈ names, name ∉ forbidden := by
  constructor
  · intro hs
    obtain ⟨⟨names, hnames⟩, _⟩ := Option.isSome_iff_exists.mp hs
    exact ⟨names, hnames⟩
  · rintro ⟨names, rfl, hnd, havoid⟩
    unfold resolveRecWritten
    split
    · rename_i hp
      rw [recWrittenNames_map] at hp
      cases hp
    · rename_i names' hp
      have heq : names' = names := Option.some.inj (hp.symm.trans (recWrittenNames_map names))
      subst names'
      simp only [dif_pos hnd, dif_pos havoid, Option.isSome_some]

theorem resolveRecWritten_length {result}
    (_h : resolveRecWritten images forbidden = some result) : result.val.length = images.length := by
  exact (List.length_map ..).symm.trans (congrArg List.length result.property.1)

/-- Substitution cannot erase a structured/concrete/bound type into a bare
free variable. No LC or freshness hypothesis on the substitution is required. -/
private theorem bare_of_subst_bare {R : Subst} {ty : Ty} {name : Nat}
    (h : R.onTy ty = .fvar name) : ∃ original, ty = .fvar original := by
  cases ty with
  | fvar original => exact ⟨original, rfl⟩
  | prim | arrow | bvar | customTy => simp only [Subst.onTy_prim, Subst.onTy_arrow, Subst.onTy_bvar, Subst.onTy_customTy, reduceCtorEq] at h

private theorem bareList_of_subst_bareList {R : Subst} {images : List Ty} {candidates : List Nat}
    (h : images.map R.onTy = candidates.map Ty.fvar) :
    ∃ names : List Nat, names.map Ty.fvar = images := by
  have hall : ∀ ty ∈ images, ∃ name, ty = .fvar name := by
    intro ty ht
    have hm : R.onTy ty ∈ candidates.map Ty.fvar := h ▸ List.mem_map.mpr ⟨ty, ht, rfl⟩
    obtain ⟨name, _, heq⟩ := List.mem_map.mp hm
    exact bare_of_subst_bare heq.symm
  clear h
  induction images with
  | nil => exact ⟨[], rfl⟩
  | cons ty rest ih =>
      obtain ⟨name, rfl⟩ := hall ty List.mem_cons_self
      obtain ⟨names, heq⟩ := ih (fun ty ht => hall ty (List.mem_cons_of_mem _ ht))
      exact ⟨name :: names, congrArg (Ty.fvar name :: ·) heq⟩

/-- A factor into a distinct bare candidate prefix certifies the concrete
validator, provided the candidate prefix avoids the images of forbidden roots.
These are per-call frame facts; no global candidate freshness is assumed. -/
theorem resolveRecWritten_complete_of_factor {R : Subst} {candidates : List Nat}
    (hfactor : images.map R.onTy = candidates.map Ty.fvar) (hnd : candidates.Nodup)
    (havoid : ∀ name ∈ candidates, ∀ v ∈ forbidden, name ∉ (R.onTy (.fvar v)).freeVars) :
    (resolveRecWritten images forbidden).isSome := by
  obtain ⟨names, hbare⟩ := bareList_of_subst_bareList hfactor
  apply resolveRecWritten_isSome_iff.mpr
  refine ⟨names, hbare, ?_, ?_⟩
  · have hmap := hnd.map (fun _ _ heq => Ty.fvar.inj heq)
    rw [← hfactor, ← hbare] at hmap
    exact hmap.of_map.of_map
  · intro name hn hf
    have hm : R.onTy (.fvar name) ∈ candidates.map Ty.fvar :=
      hfactor ▸ List.mem_map.mpr ⟨.fvar name, hbare ▸ List.mem_map.mpr ⟨name, hn, rfl⟩, rfl⟩
    obtain ⟨candidate, hc, heq⟩ := List.mem_map.mp hm
    apply havoid candidate hc name hf
    rw [← heq]
    exact List.mem_cons_self


theorem OpenRecAnn.recFits_of_images {S : Subst}
    (h : OpenRecAnn frontier ann next opening) (hmode : ann.recModeAnn = none)
    (hS : ∀ p ∈ S, p.2.IsLC)
    (himages : opening.written.map (fun x => S.onTy (.fvar x)) = resolved.map Ty.fvar)
    (htarget : ∀ expected, opening.expected = some expected → target = S.onTy expected) :
    (ann.substTyFvars S).RecFits resolved target := by
  cases h with
  | absent => trivial
  | complete => cases hmode
  | @template next ty frontier template heq _ =>
      have hfit := template.allocate_fits frontier
      rw [heq] at hfit
      rw [htarget ty rfl]
      exact hfit.substTyFvars S
  | @partialForall next ty frontier count template heq _ =>
      have hfit := (template.openTyVarsFrom 0 (freshVars frontier count)).allocate_fits (frontier + count)
      rw [heq] at hfit
      have hcount := congrArg List.length himages
      simp only [List.length_map, freshVars_length] at hcount
      refine ⟨hcount.symm, ?_⟩
      have hfitS := hfit.substTyFvars S
      rw [TyTemplate.substTyFvars_openTyVarsFrom_of_images _ hS himages 0] at hfitS
      rw [htarget ty rfl]
      exact hfitS

/-- Closing a recursively checked annotation retains its cofinite binding fit. -/
theorem BindingAnn.RecFits.cofinite_bindingFits {ann : BindingAnn} {written pool Q : List Nat} {ty : Ty}
    (hfit : ann.RecFits written ty) (hcount : written.length = ann.recPrefixCount)
    (hnd : written.Nodup) (hsub : ∀ v ∈ written, v ∈ pool) (hpool : pool.Nodup)
    (hlc : ty.IsLC) (hsource : ∀ v ∈ ann.rigidVars, v ∈ Q)
    (havoid : ∀ v ∈ pool, v ∉ Q) :
    ∃ L, ∀ Xs, FreshNames L (recScheme written pool ty).paramCount Xs →
      ann.BindingFits (recScheme written pool ty) Xs := by
  have hnames := recNames_nodup (ty := ty) hnd hpool
  have hnamesQ : ∀ v ∈ recNames written pool ty, v ∉ Q := by
    intro v hv
    rcases mem_recNames.mp hv with hv | ⟨hv, _, _⟩
    · exact havoid v (hsub v hv)
    · exact havoid v hv
  cases ann with
  | absent => exact ⟨[], fun _ _ => trivial⟩
  | complete => cases hfit
  | template template =>
      refine ⟨recNames written pool ty, ?_⟩
      intro Xs hXs
      change template.Fits (Ty.openVars Xs (Ty.closeOver (recNames written pool ty) ty))
      rw [Ty.openVars_closeOver_rename hlc hnames hXs.length
        (fun v hv hx => hXs.avoid v hx hv)]
      exact TyTemplate.Fits.onSubst hfit hsource
        (fun pair hp => hnamesQ pair.1 (List.of_mem_zip hp).1)
  | partialForall count template =>
      have hcomp : (BindingAnn.partialForall count template).SignatureCompletion written ty
          (recScheme written pool ty) (recNames written pool ty) :=
        .partialSignature hcount hfit.2
      obtain ⟨L, hL⟩ := hcomp.cofinite_fits hnames hnamesQ hsource hlc
      exact ⟨L, fun Xs hXs => hL Xs hXs⟩


theorem OpenRecAnns.selected_lookup (h : OpenRecAnns members index frontier anns next openings)
    (hi : index + i ∈ members) (ha : anns[i]? = some ann) :
    ∃ a b opening, openings[i]? = some opening ∧ OpenRecAnn a ann b opening := by
  induction h generalizing i with
  | nil => simp at ha
  | skip hn hr ih =>
    cases i with
    | zero => exact False.elim (hn (by simpa using hi))
    | succ i => exact ih (by simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hi) ha
  | cons hm hh hr ih =>
    cases i with
    | zero => cases Option.some.inj ha; exact ⟨_, _, _, rfl, hh⟩
    | succ i => exact ih (by simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hi) ha

end

/-! ## RecShapeCheck -/

section

abbrev RecShape := Ty × Option Ty

def substRecShapes (S : Subst) (shapes : List RecShape) : List RecShape :=
  shapes.map (fun shape => (S.onTy shape.1, shape.2.map S.onTy))

@[simp] theorem substRecShapes_length (S : Subst) (shapes : List RecShape) :
    (substRecShapes S shapes).length = shapes.length := by simp [substRecShapes]

/-- Solve all component shapes before entering any recursive body. -/
inductive CheckRecShapes (K : List Nat) : List RecShape → Subst → Prop
  | nil : CheckRecShapes K [] []
  | skipNone : CheckRecShapes K rest S → CheckRecShapes K ((ty, none) :: rest) S
  | consSome : RigidUnify K ty expected first →
      CheckRecShapes K (substRecShapes first rest) tail →
      CheckRecShapes K ((ty, some expected) :: rest) (first ++ tail)

/-- One rigidity-aware unification for each expected shape; no allocation. -/
def checkRecShapes (K : List Nat) (shapes : List RecShape) :
    Option { S : Subst // CheckRecShapes K shapes S } :=
  match shapes with
  | [] => some ⟨[], .nil⟩
  | (ty, none) :: rest =>
      match checkRecShapes K rest with
      | none => none
      | some ⟨S, hS⟩ => some ⟨S, .skipNone hS⟩
  | (ty, some expected) :: rest =>
      match unifyCoreK K ty expected with
      | none => none
      | some ⟨first, hu, hav⟩ =>
          match checkRecShapes K (substRecShapes first rest) with
          | none => none
          | some ⟨tail, ht⟩ => some ⟨first ++ tail, .consSome ⟨hu, hav⟩ ht⟩
termination_by shapes.length
decreasing_by all_goals simp_wf

/-- Both the shared monotype and optional expected shape are locally closed. -/
def RecShape.LC (shape : RecShape) : Prop :=
  shape.1.IsLC ∧ ∀ ty, shape.2 = some ty → ty.IsLC

def RecShape.BelowFvars (frontier : Nat) (shape : RecShape) : Prop :=
  Ty.BelowFvars frontier shape.1 ∧ ∀ ty, shape.2 = some ty → Ty.BelowFvars frontier ty

theorem substRecShapes_lc {S : Subst} (hS : ∀ pair ∈ S, pair.2.IsLC)
    (h : ∀ shape ∈ shapes, RecShape.LC shape) :
    ∀ shape ∈ substRecShapes S shapes, RecShape.LC shape := by
  intro shape hm
  unfold substRecShapes at hm
  obtain ⟨originalShape, horiginal, heq⟩ := List.mem_map.mp hm
  subst shape
  rcases originalShape with ⟨ty, expected⟩
  obtain ⟨hty, he⟩ := h _ horiginal
  refine ⟨Subst.onTy_lc hS hty, ?_⟩
  intro target ht
  obtain ⟨original, ho, rfl⟩ := Option.map_eq_some_iff.mp ht
  exact Subst.onTy_lc hS (he original ho)

theorem substRecShapes_below {S : Subst} (hS : ∀ pair ∈ S, Ty.BelowFvars frontier pair.2)
    (h : ∀ shape ∈ shapes, RecShape.BelowFvars frontier shape) :
    ∀ shape ∈ substRecShapes S shapes, RecShape.BelowFvars frontier shape := by
  intro shape hm
  unfold substRecShapes at hm
  obtain ⟨originalShape, horiginal, heq⟩ := List.mem_map.mp hm
  subst shape
  rcases originalShape with ⟨ty, expected⟩
  obtain ⟨hty, he⟩ := h _ horiginal
  refine ⟨Subst.onTy_belowFvars hS hty, ?_⟩
  intro target ht
  obtain ⟨original, ho, rfl⟩ := Option.map_eq_some_iff.mp ht
  exact Subst.onTy_belowFvars hS (he original ho)

theorem CheckRecShapes.dom_avoids (h : CheckRecShapes K shapes S) :
    ∀ pair ∈ S, pair.1 ∉ K := by
  induction h with
  | nil => simp
  | skipNone _ ih => exact ih
  | consSome hu _ ih =>
      intro pair hp
      exact (List.mem_append.mp hp).elim (hu.dom_avoids pair) (ih pair)

theorem CheckRecShapes.lc (h : CheckRecShapes K shapes S)
    (hshapes : ∀ shape ∈ shapes, RecShape.LC shape) : ∀ pair ∈ S, pair.2.IsLC := by
  induction h with
  | nil => simp
  | skipNone _ ih => exact ih (fun shape hm => hshapes shape (List.mem_cons_of_mem _ hm))
  | @consSome ty expected first rest tail hu ht ih =>
      have hh := hshapes (ty, some expected) (List.mem_cons_self)
      have hfirst := hu.unifies.lc hh.1 (hh.2 expected rfl)
      have htail := ih (substRecShapes_lc hfirst (fun shape hm => hshapes shape (List.mem_cons_of_mem _ hm)))
      intro pair hp
      exact (List.mem_append.mp hp).elim (hfirst pair) (htail pair)

theorem CheckRecShapes.belowFvars (h : CheckRecShapes K shapes S)
    (hshapes : ∀ shape ∈ shapes, RecShape.BelowFvars frontier shape) :
    ∀ pair ∈ S, Ty.BelowFvars frontier pair.2 := by
  induction h with
  | nil => simp
  | skipNone _ ih => exact ih (fun shape hm => hshapes shape (List.mem_cons_of_mem _ hm))
  | @consSome ty expected first rest tail hu ht ih =>
      have hh := hshapes (ty, some expected) (List.mem_cons_self)
      have hfirst := hu.unifies.belowFvars hh.1 (hh.2 expected rfl)
      have htail := ih (substRecShapes_below hfirst (fun shape hm => hshapes shape (List.mem_cons_of_mem _ hm)))
      intro pair hp
      exact (List.mem_append.mp hp).elim (hfirst pair) (htail pair)



private theorem recShape_unify_sourceAvoid (h : UnifyRel ty expected S)
    (ht : w ∉ ty.freeVars) (he : w ∉ expected.freeVars) :
    (∀ p ∈ S, w ∉ p.2.freeVars) ∧ w ∉ S.map Prod.fst := by
  constructor
  · intro p hp hw
    exact (h.range_mem p hp w hw).elim ht he
  · intro hw
    obtain ⟨p, hp, heq⟩ := List.mem_map.mp hw
    have hm := h.dom_mem p hp
    rw [heq] at hm
    exact hm.elim ht he

theorem CheckRecShapes.sourceAvoid (h : CheckRecShapes K shapes S)
    (hshapes : ∀ shape ∈ shapes, w ∉ shape.1.freeVars ∧
      ∀ expected, shape.2 = some expected → w ∉ expected.freeVars) :
    (∀ p ∈ S, w ∉ p.2.freeVars) ∧ w ∉ S.map Prod.fst := by
  induction h with
  | nil => simp
  | skipNone _ ih => exact ih (fun shape hm => hshapes shape (List.mem_cons_of_mem _ hm))
  | @consSome ty expected first rest tail hu ht ih =>
      have hh := hshapes (ty, some expected) List.mem_cons_self
      have hfirst := recShape_unify_sourceAvoid hu.unifies hh.1 (hh.2 expected rfl)
      have htail := ih (by
        intro shape hm
        obtain ⟨⟨original, expected⟩, ho, heq⟩ := List.mem_map.mp hm
        subst shape
        have hold := hshapes (original, expected) (List.mem_cons_of_mem _ ho)
        refine ⟨Subst.notMemOnTy hfirst.1 hold.1, ?_⟩
        intro target ht
        obtain ⟨old, holdEq, rfl⟩ := Option.map_eq_some_iff.mp ht
        exact Subst.notMemOnTy hfirst.1 (hold.2 old holdEq))
      refine ⟨fun p hp => (List.mem_append.mp hp).elim (hfirst.1 p) (htail.1 p), ?_⟩
      simpa only [List.map_append, List.mem_append, not_or] using And.intro hfirst.2 htail.2


theorem CheckRecShapes.solves (h : CheckRecShapes K shapes S)
    (hm : (ty, some expected) ∈ shapes) : S.onTy ty = S.onTy expected := by
  induction h generalizing ty expected with
  | nil => cases hm
  | skipNone hr ih =>
    rcases List.mem_cons.mp hm with hh | hm
    · cases hh
    · exact ih hm
  | consSome hu hr ih =>
    rcases List.mem_cons.mp hm with hh | hm
    · cases hh
      simpa only [Subst.onTy_append] using congrArg _ hu.unifies.unifies
    · have hh := ih (List.mem_map.mpr ⟨_, hm, rfl⟩)
      simpa only [Subst.onTy_append] using hh


private theorem recShape_solutions_factor {shapes : List RecShape} {S U R : Subst}
    (hsolve : ∀ ty expected, (ty,some expected) ∈ shapes → U.onTy ty = U.onTy expected)
    (hfactor : ∀ ty, U.onTy ty = R.onTy (S.onTy ty)) :
    ∀ ty expected, (ty,some expected) ∈ substRecShapes S shapes → R.onTy ty = R.onTy expected := by
  intro ty expected hm
  obtain ⟨⟨oldTy,oldExpected⟩,hmem,heq⟩ := List.mem_map.mp hm
  cases oldExpected with
  | none => cases heq
  | some oldExpected =>
    cases heq
    rw [←hfactor oldTy,←hfactor oldExpected]
    exact hsolve oldTy oldExpected hmem

/-- A successful shape pass is principal for every LC solution, preserving an
independent protected set. Neither source LC nor a frontier is needed here. -/
theorem CheckRecShapes.factor {K P : List Nat} {shapes : List RecShape} {S U : Subst}
    (h : CheckRecShapes K shapes S) (hU : ∀ p ∈ U, p.2.IsLC)
    (hsolve : ∀ ty expected, (ty,some expected) ∈ shapes → U.onTy ty = U.onTy expected)
    (hP : ∀ p ∈ P, U.onTy (.fvar p) = .fvar p) :
    ∃ R : Subst, (∀ p ∈ R,p.2.IsLC) ∧ (∀ p ∈ P,R.onTy (.fvar p) = .fvar p) ∧
      ∀ ty,U.onTy ty = R.onTy (S.onTy ty) := by
  induction h generalizing U with
  | nil => exact ⟨U,hU,hP,fun _ => rfl⟩
  | skipNone hr ih => exact ih hU (fun ty expected hm => hsolve ty expected (List.mem_cons_of_mem _ hm)) hP
  | consSome hu hr ih =>
    obtain ⟨V,hfac,hV,hVP⟩ := hu.unifies.greatest_K U hU (hsolve _ _ List.mem_cons_self) hP
    obtain ⟨R,hR,hRP,hrest⟩ := ih hV
      (recShape_solutions_factor (fun ty expected hm => hsolve ty expected (List.mem_cons_of_mem _ hm)) hfac) hVP
    exact ⟨R,hR,hRP,fun ty => by rw [hfac ty,hrest,Subst.onTy_append]⟩

/-- Any LC solution fixing the actual rigid set makes the executable shape
checker succeed. Candidate targets may contain arbitrary variable IDs. -/
theorem checkRecShapes_complete {K : List Nat} {shapes : List RecShape} {U : Subst}
    (hLC : ∀ shape ∈ shapes, RecShape.LC shape) (hU : ∀ p ∈ U,p.2.IsLC)
    (hsolve : ∀ ty expected,(ty,some expected) ∈ shapes → U.onTy ty = U.onTy expected)
    (hK : ∀ k ∈ K,U.onTy (.fvar k) = .fvar k) :
    (checkRecShapes K shapes).isSome := by
  match shapes with
  | [] => simp only [checkRecShapes,Option.isSome_some]
  | (ty,none)::rest =>
    have ht := checkRecShapes_complete
      (fun shape hm => hLC shape (List.mem_cons_of_mem _ hm)) hU
      (fun ty expected hm => hsolve ty expected (List.mem_cons_of_mem _ hm)) hK
    cases hc : checkRecShapes K rest with
    | none => simp only [hc,Option.isSome_none] at ht; contradiction
    | some result => simp only [checkRecShapes,hc,Option.isSome_some]
  | (ty,some expected)::rest =>
    have hh := hLC (ty,some expected) List.mem_cons_self
    have hu := unifyCoreK_complete hh.1 (hh.2 expected rfl) hU (hsolve _ _ List.mem_cons_self) hK
    cases hc : unifyCoreK K ty expected with
    | none => simp only [hc,Option.isSome_none] at hu; contradiction
    | some result =>
      obtain ⟨first,hfirst,havoid⟩ := result
      have hfirstLC := hfirst.lc hh.1 (hh.2 expected rfl)
      obtain ⟨V,hfac,hV,hVK⟩ := hfirst.greatest_K U hU (hsolve _ _ List.mem_cons_self) hK
      have ht := checkRecShapes_complete
        (substRecShapes_lc hfirstLC (fun shape hm => hLC shape (List.mem_cons_of_mem _ hm))) hV
        (recShape_solutions_factor (fun ty expected hm => hsolve ty expected (List.mem_cons_of_mem _ hm)) hfac) hVK
      cases ht' : checkRecShapes K (substRecShapes first rest) with
      | none => simp only [ht',Option.isSome_none] at ht; contradiction
      | some tail => simp only [checkRecShapes,hc,ht',Option.isSome_some]
 termination_by shapes.length
 decreasing_by all_goals simp_wf

end

/-! ## RecState -/

section

/-- Artifacts remain in inference-variable coordinates until each member's
written prefix is finalized. Closing an output expression is separate. -/
structure RecFacts where
  nodeTypes : InferredNodeTypes
  binderSchemes : InferredBinderSchemes

def RecFacts.empty : RecFacts := ⟨[], []⟩

def RecFacts.onSubst (S : Subst) (facts : RecFacts) : RecFacts :=
  ⟨facts.nodeTypes.onSubst S, facts.binderSchemes.onSubst S⟩

/-- All lists retain original recursive-group coordinates. `slots` records the
ordered current images of written slots, including unused ones; `exports`
contains complete contracts and already generalized inferred components. -/
structure RecState where
  specs : List RecSpec
  slots : List (List Ty)
  exports : List (Option PolyTy)
  outputs : List (Option Expr)
  facts : List RecFacts
  pool : List Nat

def RecState.init (frontier : Nat) (anns : List BindingAnn) : RecState :=
  { specs := RecSpec.init frontier (anns.map BindingAnn.recModeAnn)
    slots := anns.map (fun _ => [])
    exports := anns.map BindingAnn.recModeAnn
    outputs := anns.map (fun _ => none)
    facts := anns.map (fun _ => .empty)
    pool := [] }

def RecState.onSubst (S : Subst) (state : RecState) : RecState :=
  { specs := state.specs.map (RecSpec.onSubstSource S)
    slots := state.slots.map (fun names => names.map S.onTy)
    exports := state.exports.map (Option.map S.onPolyTy)
    outputs := state.outputs.map (Option.map (Expr.substTyFvars S))
    facts := state.facts.map (RecFacts.onSubst S)
    pool := state.pool }

def _root_.RecSpec.monoEntry : RecSpec → PolyTy
  | .mono ty => PolyTy.mkTrivial ty
  | .poly scheme => scheme

def RecState.entries (state : RecState) : List PolyTy :=
  state.specs.zip state.exports |>.map (fun (spec, exported) => exported.getD spec.monoEntry)

def RecState.rhsCtx (state : RecState) (ctx : Ctx) : Ctx :=
  { ctx with env := state.entries ++ ctx.env }

def RecState.fixedCtx (state : RecState) (ctx : Ctx) : Ctx :=
  { ctx with env := state.exports.filterMap id ++ ctx.env }

/-- Install only this component's newly allocated written roots. Other members
retain their own ordered traces. -/
def RecState.installOpenings (state : RecState) (members : List Nat)
    (openings : List RecOpening) : RecState :=
  { state with slots := state.slots.mapIdx (fun i old =>
      if i ∈ members then ((openings[i]?).getD .empty).written.map Ty.fvar else old) }

/-- Open before applying the component's constraints. Provisional slots may
subsequently become nonvariables, so opening cannot be deferred until after S. -/
def openRecSources : List RecOpening → List InferInput → List InferInput
  | _, [] => []
  | [], bindings => bindings
  | opening :: openings, rhs :: rest => rhs.openTyVars opening.written :: openRecSources openings rest

@[simp] theorem sizeBindings_openRecSources (openings : List RecOpening) (bindings : List InferInput) :
    sizeBindings (openRecSources openings bindings) = sizeBindings bindings := by
  induction bindings generalizing openings with
  | nil => cases openings <;> rfl
  | cons rhs rest ih =>
    cases openings with
    | nil => rfl
    | cons opening openings => simp only [openRecSources, sizeBindings, InferInput.size_openTyVars, ih]


def RecState.shapes (state : RecState) (members : List Nat)
    (openings : List RecOpening) : List RecShape :=
  members.filterMap (fun i => do
    let spec ← state.specs[i]?
    let ty ← spec.monoTy?
    let opening ← openings[i]?
    pure (ty, opening.expected))

/-- Closed unsigned outputs use the member's own prefix order and the shared
pool. Metadata remains open until all later component substitutions are known. -/
def RecState.exportComponent (state : RecState) (members : List Nat)
    (written : List (List Nat)) (pool : List Nat)
    (outputs : List (Option Expr)) (facts : List RecFacts) : RecState :=
  { state with
    exports := state.exports.mapIdx (fun i old =>
      if i ∈ members then do
        let spec ← state.specs[i]?
        pure (spec.completedScheme (written[i]?.getD []) pool)
      else old)
    outputs := state.outputs.mapIdx (fun i old =>
      if i ∈ members then do
        let spec ← state.specs[i]?
        let ty ← spec.monoTy?
        let rhs ← (outputs[i]?).join
        pure (rhs.closeTyVars (recNames (written[i]?.getD []) pool ty))
      else old)
    facts := state.facts.mapIdx (fun i old => if i ∈ members then facts[i]?.getD .empty else old)
    pool := pool }

/-- Validate ordered slot images only for the component being exported. -/
inductive ResolveRecSlots (members : List Nat) (forbidden : List Nat) :
    Nat → List (List Ty) → List (List Nat) → Prop
  | nil : ResolveRecSlots members forbidden index [] []
  | skip : index ∉ members → ResolveRecSlots members forbidden (index + 1) rest names →
      ResolveRecSlots members forbidden index (images :: rest) ([] :: names)
  | cons : index ∈ members → written.map Ty.fvar = images → written.Nodup →
      (∀ name ∈ written, name ∉ forbidden) →
      ResolveRecSlots members forbidden (index + 1) rest names →
      ResolveRecSlots members forbidden index (images :: rest) (written :: names)

def resolveRecSlots (members forbidden : List Nat) (index : Nat) (slots : List (List Ty)) :
    Option { names : List (List Nat) // ResolveRecSlots members forbidden index slots names } :=
  match slots with
  | [] => some ⟨[], .nil⟩
  | images :: rest =>
      if hm : index ∈ members then
        match resolveRecWritten images forbidden, resolveRecSlots members forbidden (index + 1) rest with
        | some ⟨written, hbare, hnd, hav⟩, some ⟨names, hn⟩ =>
            some ⟨written :: names, .cons hm hbare hnd hav hn⟩
        | _, _ => none
      else
        match resolveRecSlots members forbidden (index + 1) rest with
        | some ⟨names, hn⟩ => some ⟨[] :: names, .skip hm hn⟩
        | none => none

def RecState.componentPool (state : RecState) (K soft members : List Nat)
    (ctx : Ctx) (written : List (List Nat)) : List Nat :=
  state.pool ++ ((written.flatten ++
    genGroupVars (K ++ soft ++ state.pool) (state.fixedCtx ctx).env
      (RecSpecs.monoTysAt state.specs members)).dedup.filter (fun v => decide (v ∉ state.pool)))

/-- The only export check on a partial written prefix is ordinary forall
validity: bare, distinct within that member, and fresh in the fixed boundary. -/
inductive FinishRecComponent (K soft members : List Nat) (ctx : Ctx)
    (state : RecState) (outputs : List (Option Expr)) (facts : List RecFacts) :
    RecState → Prop
  | mk {written : List (List Nat)} :
      ResolveRecSlots members ((state.fixedCtx ctx).env.freeVars ++ K ++ soft) 0 state.slots written →
      FinishRecComponent K soft members ctx state outputs facts
        (state.exportComponent members written (state.componentPool K soft members ctx written) outputs facts)

def finishRecComponent (K soft members : List Nat) (ctx : Ctx)
    (state : RecState) (outputs : List (Option Expr)) (facts : List RecFacts) :
    Option { result : RecState // FinishRecComponent K soft members ctx state outputs facts result } :=
  match resolveRecSlots members ((state.fixedCtx ctx).env.freeVars ++ K ++ soft) 0 state.slots with
  | none => none
  | some ⟨written, hw⟩ =>
      some ⟨state.exportComponent members written (state.componentPool K soft members ctx written) outputs facts, .mk hw⟩


def RecFacts.closeWritten (names : List Nat) (facts : RecFacts) : RecFacts :=
  ⟨(facts.nodeTypes.closeTyVars names).underTyBinders names.length,
    (facts.binderSchemes.closeTyVars names).underTyBinders names.length⟩

/-- Complete-signature RHSs close their rigid opening before leaving its scope.
Partial prefixes stay open in the stored metadata until final normalization. -/
def RecState.setSigned (state : RecState) (member : Nat) (names : List Nat)
    (output : Expr) (facts : RecFacts) : RecState :=
  { state with
    outputs := state.outputs.set member (some (output.closeTyVars names))
    facts := state.facts.set member (facts.closeWritten names) }


/-- Extract a completed aligned vector, retaining its exact positional equation. -/
def collectRecValues {α : Type} : (values : List (Option α)) →
    Option { result : List α // values = result.map some }
  | [] => some ⟨[], rfl⟩
  | none :: _ => none
  | some value :: rest =>
      match collectRecValues rest with
      | none => none
      | some ⟨values, hv⟩ => some ⟨value :: values, congrArg (some value :: ·) hv⟩

private def recSlotName : Ty → Option Nat
  | .fvar name => some name
  | _ => none

/-- Close only authored partial-prefix representatives in editor artifacts.
Additional generalized variables keep the ordinary inference-variable convention. -/
def finalizeRecFacts (ann : BindingAnn) (slots : List Ty) (facts : RecFacts) : RecFacts :=
  match ann with
  | .partialForall count _ =>
      let written := slots.filterMap recSlotName
      ⟨(facts.nodeTypes.closeTyVars written).underTyBinders count,
        (facts.binderSchemes.closeTyVars written).underTyBinders count⟩
  | _ => facts

def inferredRecSchemes (anns : List BindingAnn) (schemes : List PolyTy) : InferredBinderSchemes :=
  anns.zip schemes |>.mapIdx (fun i (ann, scheme) => match ann with
    | .complete _ => []
    | _ => [{ site := .letRec [] i, scheme := scheme, tyDepth := 0 }]) |>.flatten

def finalRecNodeTypes (anns : List BindingAnn) (state : RecState) : InferredNodeTypes :=
  state.facts.mapIdx (fun i facts =>
    (finalizeRecFacts (anns[i]?.getD .absent) (state.slots[i]?.getD []) facts).nodeTypes.below (.letRecRhs i)) |>.flatten

def finalRecBinderSchemes (anns : List BindingAnn) (state : RecState) : InferredBinderSchemes :=
  state.facts.mapIdx (fun i facts =>
    (finalizeRecFacts (anns[i]?.getD .absent) (state.slots[i]?.getD []) facts).binderSchemes.below (.letRecRhs i)) |>.flatten

@[simp] theorem sizeBindings_map_substTyFvars (bindings : List InferInput) (S : Subst) :
    sizeBindings (bindings.map (InferInput.substTyFvars S)) = sizeBindings bindings := by
  induction bindings with
  | nil => rfl
  | cons rhs rest ih => simp only [List.map_cons, sizeBindings, InferInput.size_substTyFvars, ih]

@[simp] theorem RecState.entries_onSubst (state : RecState) (S : Subst) :
    (state.onSubst S).entries = S.onEnv state.entries := by
  simp only [RecState.entries, RecState.onSubst, Subst.onEnv, List.zip_map_left,
    List.zip_map_right, List.map_map]
  apply List.map_congr_left
  intro pair _
  rcases pair with ⟨spec, exported⟩
  cases exported with
  | none => cases spec <;> rfl
  | some scheme => rfl

@[simp] theorem RecState.rhsCtx_onSubst (state : RecState) (S : Subst) (ctx : Ctx) :
    (state.onSubst S).rhsCtx (S.onCtx ctx) = S.onCtx (state.rhsCtx ctx) := by
  simp only [RecState.rhsCtx, RecState.entries_onSubst, Subst.onCtx, Subst.onEnv, List.map_append]

@[simp] theorem RecState.fixedCtx_onSubst (state : RecState) (S : Subst) (ctx : Ctx) :
    (state.onSubst S).fixedCtx (S.onCtx ctx) = S.onCtx (state.fixedCtx ctx) := by
  simp only [RecState.fixedCtx, RecState.onSubst, Subst.onCtx, Subst.onEnv,
    List.map_append, List.map_filterMap, List.filterMap_map, Function.comp_def, id_eq]

 theorem RecState.entries_length (state : RecState)
    (hlen : state.exports.length = state.specs.length) : state.entries.length = state.specs.length := by
  simp only [RecState.entries, List.length_map, List.length_zip, hlen, Nat.min_self]

@[simp] theorem RecState.init_lengths (base : Nat) (anns : List BindingAnn) :
    (RecState.init base anns).specs.length = anns.length ∧
    (RecState.init base anns).slots.length = anns.length ∧
    (RecState.init base anns).exports.length = anns.length ∧
    (RecState.init base anns).outputs.length = anns.length ∧
    (RecState.init base anns).facts.length = anns.length := by
  simp only [RecState.init, RecSpec.init_length, List.length_map, and_self]

 theorem RecState.onSubst_lengths (state : RecState) (S : Subst) :
    (state.onSubst S).specs.length = state.specs.length ∧
    (state.onSubst S).slots.length = state.slots.length ∧
    (state.onSubst S).exports.length = state.exports.length ∧
    (state.onSubst S).outputs.length = state.outputs.length ∧
    (state.onSubst S).facts.length = state.facts.length := by
  simp only [RecState.onSubst, List.length_map, and_self]

private theorem initial_entries (base : Nat) (anns : List (Option PolyTy)) :
    ((RecSpec.init base anns).zip anns).map (fun (spec, exported) => exported.getD spec.monoEntry) =
      (RecSpec.init base anns).map RecSpec.monoEntry := by
  induction anns generalizing base with
  | nil => rfl
  | cons ann rest ih =>
      cases ann with
      | none => exact congrArg (List.cons (PolyTy.mkTrivial (.fvar base))) (ih (base + 1))
      | some scheme => exact congrArg (List.cons scheme) (ih (base + 1))

 theorem RecState.init_entries (base : Nat) (anns : List BindingAnn) :
    (RecState.init base anns).entries =
      (RecSpec.init base (anns.map BindingAnn.recModeAnn)).map RecSpec.monoEntry :=
  initial_entries base (anns.map BindingAnn.recModeAnn)

 theorem RecState.init_rhsCtx (base : Nat) (anns : List BindingAnn) (ctx : Ctx) :
    (RecState.init base anns).rhsCtx ctx =
      RecSpecs.algorithmStageCtx ctx (RecSpec.init base (anns.map BindingAnn.recModeAnn)) [] [] := by
  simp only [RecState.rhsCtx, RecState.init_entries, RecSpecs.algorithmStageCtx]
  congr 1
  congr 1
  apply List.ext_getElem?
  intro i
  simp only [List.getElem?_map, List.getElem?_mapIdx]
  cases hs : (RecSpec.init base (anns.map BindingAnn.recModeAnn))[i]? with
  | none => rfl
  | some spec => cases spec <;> simp [RecSpec.monoEntry, RecSpec.algorithmStageEntry]

 theorem RecState.pendingSeeds_init {base : Nat} {ctx : Ctx} {anns : List BindingAnn}
    (hctx : CtxBelow base ctx)
    (hanns : ∀ ann ∈ anns, ∀ v ∈ ann.rigidVars, v < base) :
    RecSpecs.PendingSeeds base ctx (RecState.init base anns).specs [] := by
  apply RecSpecs.PendingSeeds.init hctx
  intro scheme hm
  obtain ⟨ann, hann, heq⟩ := List.mem_map.mp hm
  cases ann with
  | absent | template t | partialForall n t => cases heq
  | complete σ =>
      have hs : σ = scheme := Option.some.inj heq
      subst scheme
      exact Ty.BelowFvars.of_freeVars_lt (hanns (.complete σ) hann)

/-- Only recursive type specs and already exported schemes constrain LC. -/
def RecState.LC (state : RecState) : Prop :=
  (∀ spec ∈ state.specs, spec.LC) ∧ (∀ scheme, some scheme ∈ state.exports → scheme.WF)

 theorem RecState.LC.init {base : Nat} {anns : List BindingAnn}
    (hanns : ∀ scheme, .complete scheme ∈ anns → scheme.WF) : (RecState.init base anns).LC := by
  have hmode : ∀ scheme, some scheme ∈ anns.map BindingAnn.recModeAnn → scheme.WF := by
    intro scheme hm
    obtain ⟨ann, hann, heq⟩ := List.mem_map.mp hm
    cases ann with
    | absent | template t | partialForall n t => cases heq
    | complete σ =>
        have hs : σ = scheme := Option.some.inj heq
        subst scheme
        exact hanns σ hann
  constructor
  · intro spec hm
    rcases RecSpec.mem_init hm with ⟨m, _, _, rfl⟩ | ⟨scheme, hs, rfl⟩
    · exact .fvar
    · exact hmode scheme hs
  · exact hmode

 theorem RecState.LC.onSubst {state : RecState} (h : state.LC)
    (hS : ∀ p ∈ S, p.2.IsLC) : (state.onSubst S).LC := by
  constructor
  · intro spec hm
    obtain ⟨old, hold, rfl⟩ := List.mem_map.mp hm
    cases old with
    | mono ty => exact Subst.onTy_lc hS (h.1 _ hold)
    | poly scheme => exact Subst.onPolyTy_wf hS (h.1 _ hold)
  · intro scheme hm
    obtain ⟨old, hold, heq⟩ := List.mem_map.mp hm
    obtain ⟨original, ho, rfl⟩ := Option.map_eq_some_iff.mp heq
    exact Subst.onPolyTy_wf hS (h.2 original (ho ▸ hold))

 theorem RecState.LC.installOpenings {state : RecState} (h : state.LC) :
    (state.installOpenings members openings).LC := h

 theorem RecState.LC.setSigned {state : RecState} (h : state.LC) {facts : RecFacts} :
    (state.setSigned member names output facts).LC := h

 theorem RecState.LC.rhsCtx {state : RecState} (h : state.LC) (hctx : CtxWF ctx) :
    CtxWF (state.rhsCtx ctx) := by
  intro scheme hm
  rcases List.mem_append.mp hm with hm | hm
  · obtain ⟨⟨spec, exported⟩, hp, heq⟩ := List.mem_map.mp hm
    have hmem := List.of_mem_zip hp
    cases exported with
    | none =>
      subst scheme
      cases spec with
      | mono ty => exact h.1 _ hmem.1
      | poly σ => exact h.1 _ hmem.1
    | some σ =>
      cases heq
      exact h.2 σ hmem.2
  · exact hctx scheme hm

 theorem RecState.LC.fixedCtx {state : RecState} (h : state.LC) (hctx : CtxWF ctx) :
    CtxWF (state.fixedCtx ctx) := by
  intro scheme hm
  rcases List.mem_append.mp hm with hm | hm
  · obtain ⟨old, hold, heq⟩ := List.mem_filterMap.mp hm
    exact h.2 scheme (heq ▸ hold)
  · exact hctx scheme hm

 theorem RecState.LC.exportComponent {state : RecState} (h : state.LC)
    {pool : List Nat} {outputs : List (Option Expr)} {facts : List RecFacts} :
    (state.exportComponent members written pool outputs facts).LC := by
  refine ⟨h.1, ?_⟩
  intro scheme hm
  obtain ⟨i, hi, heq⟩ := List.mem_mapIdx.mp hm
  split at heq
  · cases hs : state.specs[i]? with
    | none => simp [hs] at heq
    | some spec =>
      simp [hs] at heq
      subst scheme
      exact RecSpec.completedScheme_wf (h.1 spec (List.mem_of_getElem? hs))
  · exact h.2 scheme (heq ▸ List.getElem_mem hi)

 theorem FinishRecComponent.lc (h : FinishRecComponent K soft members ctx state outputs facts final)
    (hstate : state.LC) : final.LC := by
  cases h
  exact hstate.exportComponent

/-- Bounds for live recursive types; completed expressions and metadata are separate. -/
def RecState.Below (frontier : Nat) (state : RecState) : Prop :=
  (∀ spec ∈ state.specs, spec.BelowFvars frontier) ∧
  (∀ images ∈ state.slots, ∀ ty ∈ images, Ty.BelowFvars frontier ty) ∧
  (∀ scheme, some scheme ∈ state.exports → Ty.BelowFvars frontier scheme.body) ∧
  (∀ name ∈ state.pool, name < frontier)

 theorem RecState.Below.init {base : Nat} {anns : List BindingAnn}
    (hanns : ∀ ann ∈ anns, ∀ v ∈ ann.rigidVars, v < base) :
    (RecState.init base anns).Below (base + anns.length) := by
  have hmode : ∀ scheme, some scheme ∈ anns.map BindingAnn.recModeAnn → Ty.BelowFvars (base + anns.length) scheme.body := by
    intro scheme hm
    obtain ⟨ann, hann, heq⟩ := List.mem_map.mp hm
    cases ann with
    | absent | template t | partialForall n t => cases heq
    | complete σ =>
      have hs : σ = scheme := Option.some.inj heq
      subst scheme
      exact Ty.BelowFvars.of_freeVars_lt (fun v hv => Nat.lt_of_lt_of_le (hanns _ hann v hv) (by omega))
  refine ⟨?_, ?_, hmode, by simp [RecState.init]⟩
  · intro spec hm
    rcases RecSpec.mem_init hm with ⟨m, _, hupper, rfl⟩ | ⟨scheme, hs, rfl⟩
    · exact .fvar (by simpa only [List.length_map] using hupper)
    · exact hmode scheme hs
  · intro images hm ty ht
    obtain ⟨ann, _, heq⟩ := List.mem_map.mp hm
    cases heq
    cases ht

 theorem RecState.Below.mono {state : RecState} (h : state.Below frontier) (hle : frontier ≤ next) :
    state.Below next :=
  ⟨fun spec hs => (h.1 spec hs).mono hle,
    fun images hi ty ht => (h.2.1 images hi ty ht).mono hle,
    fun scheme hs => (h.2.2.1 scheme hs).mono hle,
    fun name hn => Nat.lt_of_lt_of_le (h.2.2.2 name hn) hle⟩

 theorem RecState.Below.onSubst {state : RecState} (h : state.Below frontier)
    (hS : ∀ p ∈ S, Ty.BelowFvars next p.2) (hle : frontier ≤ next) :
    (state.onSubst S).Below next := by
  refine ⟨?_, ?_, ?_, fun name hn => Nat.lt_of_lt_of_le (h.2.2.2 name hn) hle⟩
  · intro spec hm
    obtain ⟨old, hold, rfl⟩ := List.mem_map.mp hm
    cases old with
    | mono ty => exact Subst.onTy_belowFvars hS ((h.1 _ hold).mono hle)
    | poly scheme => exact Subst.onTy_belowFvars hS ((h.1 _ hold).mono hle)
  · intro images hm ty ht
    obtain ⟨old, hold, rfl⟩ := List.mem_map.mp hm
    obtain ⟨original, ho, rfl⟩ := List.mem_map.mp ht
    exact Subst.onTy_belowFvars hS ((h.2.1 old hold original ho).mono hle)
  · intro scheme hm
    obtain ⟨old, hold, heq⟩ := List.mem_map.mp hm
    obtain ⟨original, ho, rfl⟩ := Option.map_eq_some_iff.mp heq
    exact Subst.onTy_belowFvars hS ((h.2.2.1 original (ho ▸ hold)).mono hle)

 theorem RecState.Below.setSigned {state : RecState} (h : state.Below frontier) {facts : RecFacts} :
    (state.setSigned member names output facts).Below frontier := h

 theorem RecState.Below.rhsCtx {state : RecState} (h : state.Below frontier) (hctx : CtxBelow frontier ctx) :
    CtxBelow frontier (state.rhsCtx ctx) := by
  intro scheme hm
  rcases List.mem_append.mp hm with hm | hm
  · obtain ⟨⟨spec, exported⟩, hp, heq⟩ := List.mem_map.mp hm
    have hmem := List.of_mem_zip hp
    cases exported with
    | none =>
      subst scheme
      cases spec with
      | mono ty => exact h.1 _ hmem.1
      | poly σ => exact h.1 _ hmem.1
    | some σ => cases heq; exact h.2.2.1 σ hmem.2
  · exact hctx scheme hm

 theorem RecState.Below.fixedCtx {state : RecState} (h : state.Below frontier) (hctx : CtxBelow frontier ctx) :
    CtxBelow frontier (state.fixedCtx ctx) := by
  intro scheme hm
  rcases List.mem_append.mp hm with hm | hm
  · obtain ⟨old, hold, heq⟩ := List.mem_filterMap.mp hm
    exact h.2.2.1 scheme (heq ▸ hold)
  · exact hctx scheme hm

 theorem RecState.Below.installOpenings {state : RecState} (h : state.Below frontier)
    (hopen : OpenRecAnns members index frontier anns next openings) :
    (state.installOpenings members openings).Below next := by
  have hb := h.mono hopen.frontier_le
  refine ⟨hb.1, ?_, hb.2.2⟩
  intro images hm ty ht
  obtain ⟨i, hi, heq⟩ := List.mem_mapIdx.mp hm
  split at heq
  · cases ho : openings[i]? with
    | none => simp [ho, RecOpening.empty] at heq; subst images; cases ht
    | some opening =>
      simp only [ho, Option.getD_some] at heq
      subst images
      obtain ⟨name, hn, rfl⟩ := List.mem_map.mp ht
      exact .fvar ((hopen.written_range name (List.mem_flatMap.mpr
        ⟨opening, List.mem_of_getElem? ho, hn⟩)).2)
  · exact hb.2.1 _ (List.getElem_mem hi) ty (heq ▸ ht)

 theorem ResolveRecSlots.names_below
    (h : ResolveRecSlots members forbidden index slots names)
    (hslots : ∀ images ∈ slots, ∀ ty ∈ images, Ty.BelowFvars frontier ty) :
    ∀ name ∈ names.flatten, name < frontier := by
  induction h with
  | nil => intro name hn; cases hn
  | skip _ _ ih =>
    exact ih (fun images hi => hslots images (List.mem_cons_of_mem _ hi))
  | cons _ hbare _ _ _ ih =>
    intro name hn
    rcases List.mem_append.mp hn with hn | hn
    · have hb := hslots _ List.mem_cons_self (.fvar name)
        (hbare ▸ List.mem_map.mpr ⟨name, hn, rfl⟩)
      exact hb.mem_lt name (by simp [Ty.freeVars])
    · exact ih (fun images hi => hslots images (List.mem_cons_of_mem _ hi)) name hn

private theorem monoTysAt_below {specs : List RecSpec}
    (h : ∀ spec ∈ specs, spec.BelowFvars frontier) :
    ∀ ty ∈ RecSpecs.monoTysAt specs members, Ty.BelowFvars frontier ty := by
  intro ty hm
  obtain ⟨i, _, heq⟩ := List.mem_filterMap.mp hm
  cases hs : specs[i]? with
  | none => simp [hs] at heq
  | some spec =>
    cases spec with
    | poly σ => simp [hs, RecSpec.monoTy?] at heq
    | mono original =>
      simp [hs, RecSpec.monoTy?] at heq
      subst ty
      exact h _ (List.mem_of_getElem? hs)

private theorem freeVarsList_below {tys : List Ty}
    (h : ∀ ty ∈ tys, Ty.BelowFvars frontier ty) :
    ∀ v ∈ Ty.freeVarsList tys, v < frontier := by
  induction tys with
  | nil => intro v hv; cases hv
  | cons ty rest ih =>
    intro v hv
    rcases List.mem_append.mp (List.mem_dedup.mp hv) with hv | hv
    · exact (h ty List.mem_cons_self).mem_lt v hv
    · exact ih (fun t ht => h t (List.mem_cons_of_mem _ ht)) v hv

 theorem RecState.Below.componentPool {state : RecState} (h : state.Below frontier)
    (hnames : ∀ v ∈ written.flatten, v < frontier) :
    ∀ v ∈ state.componentPool K soft members ctx written, v < frontier := by
  intro v hv
  rcases List.mem_append.mp hv with hv | hv
  · exact h.2.2.2 v hv
  · have hm := List.mem_dedup.mp (List.mem_filter.mp hv).1
    rcases List.mem_append.mp hm with hm | hm
    · exact hnames v hm
    · have hf := (List.mem_filter.mp hm).1
      exact freeVarsList_below (monoTysAt_below h.1) v hf

 theorem RecState.Below.exportComponent {state : RecState} (h : state.Below frontier)
    {pool : List Nat} {outputs : List (Option Expr)} {facts : List RecFacts}
    (hpool : ∀ v ∈ pool, v < frontier) :
    (state.exportComponent members written pool outputs facts).Below frontier := by
  refine ⟨h.1, h.2.1, ?_, hpool⟩
  intro scheme hm
  obtain ⟨i, hi, heq⟩ := List.mem_mapIdx.mp hm
  split at heq
  · cases hs : state.specs[i]? with
    | none => simp [hs] at heq
    | some spec =>
      simp [hs] at heq
      subst scheme
      cases spec with
      | mono ty => exact (h.1 _ (List.mem_of_getElem? hs)).closeOver
      | poly σ => exact h.1 _ (List.mem_of_getElem? hs)
  · exact h.2.2.1 scheme (heq ▸ List.getElem_mem hi)

 theorem FinishRecComponent.below (h : FinishRecComponent K soft members ctx state outputs facts final)
    (hstate : state.Below frontier) : final.Below frontier := by
  cases h with
  | mk hslots =>
      exact hstate.exportComponent (hstate.componentPool (hslots.names_below hstate.2.1))

/-- The live type state of a dependency-first recursion solve. Completed members
are compared through their exported schemes; exact seed equations are retained
only for members that have not yet been solved. -/
structure RecState.Frame (base : Nat) (K : List Nat) (F : List Ty)
    (ctx : Ctx) (anns : List BindingAnn) (done : List Nat) (state : RecState) : Prop where
  specs_length : state.specs.length = anns.length
  slots_length : state.slots.length = anns.length
  exports_length : state.exports.length = anns.length
  outputs_length : state.outputs.length = anns.length
  facts_length : state.facts.length = anns.length
  modes : state.specs.map RecSpec.ann = anns.map BindingAnn.recModeAnn
  poly : ∀ (i : Nat) (scheme : PolyTy), state.specs[i]? = some (RecSpec.poly scheme) →
    state.exports[i]? = some (some scheme)
  mono : ∀ (i : Nat) (ty : Ty), state.specs[i]? = some (RecSpec.mono ty) →
    if i ∈ done then ∃ written,
      state.slots[i]? = some (written.map Ty.fvar) ∧
      written.length = (anns[i]?.getD .absent).recPrefixCount ∧ written.Nodup ∧
      (∀ v ∈ written, v ∈ state.pool) ∧
      state.exports[i]? = some (some (recScheme written state.pool ty))
    else state.exports[i]? = some none
  pending : RecSpecs.PendingSeeds base ctx state.specs done
  pool_nodup : state.pool.Nodup
  pool_ctx : ∀ v ∈ state.pool, v ∉ ctx.env.freeVars
  pool_rigid : ∀ v ∈ state.pool, v ∉ K
  pool_soft : ∀ v ∈ state.pool, v ∉ TyList.freeVars F
  pool_poly : ∀ (scheme : PolyTy), (∃ i : Nat, state.specs[i]? = some (.poly scheme)) →
    ∀ v ∈ state.pool, v ∉ scheme.body.freeVars
  pool_pending : ∀ (i : Nat) (ty : Ty), state.specs[i]? = some (RecSpec.mono ty) → i ∉ done →
    base + i ∉ state.pool
  rigid_below : ∀ v ∈ K, v < base
  pending_soft : ∀ (i : Nat) (ty : Ty), state.specs[i]? = some (RecSpec.mono ty) → i ∉ done →
    base + i ∉ TyList.freeVars F

 theorem RecState.Frame.entries_length {state : RecState} {base : Nat} {K : List Nat}
    {F : List Ty} {ctx : Ctx} {anns : List BindingAnn} {done : List Nat}
    (h : state.Frame base K F ctx anns done) :
    state.entries.length = anns.length := by
  rw [state.entries_length (h.exports_length.trans h.specs_length.symm), h.specs_length]

 theorem RecState.Frame.init {base : Nat} {K : List Nat} {F : List Ty} {ctx : Ctx}
    {anns : List BindingAnn} (hctx : CtxBelow base ctx)
    (hanns : ∀ v ∈ anns.flatMap BindingAnn.rigidVars, v < base)
    (hK : ∀ v ∈ K, v < base) (hF : ∀ v ∈ TyList.freeVars F, v < base) :
    (RecState.init base anns).Frame base K F ctx anns [] := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := RecState.init_lengths base anns
  refine ⟨h1, h2, h3, h4, h5, ?_, ?_, ?_, ?_, by simp [RecState.init],
    by simp [RecState.init], by simp [RecState.init], by simp [RecState.init],
    by simp [RecState.init], by simp [RecState.init], hK, ?_⟩
  · exact RecSpec.map_ann_init base _
  · intro i scheme hspec
    have heq := congrArg (fun specs : List RecSpec => (specs.map RecSpec.ann)[i]?)
      (show (RecState.init base anns).specs = RecSpec.init base (anns.map BindingAnn.recModeAnn) from rfl)
    have hm := congrArg (fun xs : List (Option PolyTy) => xs[i]?)
      (RecSpec.map_ann_init base (anns.map BindingAnn.recModeAnn))
    simp only [List.getElem?_map, ← heq, hspec, Option.map_some, RecSpec.ann] at hm
    simpa only [RecState.init, List.getElem?_map] using hm.symm
  · intro i ty hspec
    simp only [List.not_mem_nil, ↓reduceIte]
    have hm := congrArg (fun xs : List (Option PolyTy) => xs[i]?)
      (RecSpec.map_ann_init base (anns.map BindingAnn.recModeAnn))
    change (RecState.init base anns).exports[i]? = some none
    simp only [RecState.init, List.getElem?_map] at hspec ⊢
    have heq : (RecSpec.init base (anns.map BindingAnn.recModeAnn))[i]? = some (.mono ty) := hspec
    simpa only [List.getElem?_map, heq, Option.map_some, RecSpec.ann] using hm.symm
  · apply RecSpecs.PendingSeeds.init hctx
    intro scheme hm
    apply Ty.BelowFvars.of_freeVars_lt
    intro v hv
    obtain ⟨ann, ha, heq⟩ := List.mem_map.mp hm
    have hs : scheme.body.freeVars = ann.rigidVars := by
      cases ann <;> simp_all [BindingAnn.recModeAnn, BindingAnn.rigidVars]
    exact hanns v (List.mem_flatMap.mpr ⟨ann, ha, hs ▸ hv⟩)
  · intro i ty _ _ hmem
    have := hF (base + i) hmem
    omega


 theorem RecState.Frame.pool_entries {state : RecState} {base : Nat} {K : List Nat}
    {F : List Ty} {ctx : Ctx} {anns : List BindingAnn} {done : List Nat}
    (h : state.Frame base K F ctx anns done) :
    ∀ v ∈ state.pool, ∀ scheme ∈ state.entries, v ∉ scheme.body.freeVars := by
  intro v hv scheme hm
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hm
  rw [RecState.entries, List.getElem?_map] at hi
  obtain ⟨⟨spec, exported⟩, hz, heq⟩ := Option.map_eq_some_iff.mp hi
  obtain ⟨hs, he⟩ := List.getElem?_zip_eq_some.mp hz
  cases spec with
  | poly sigma =>
    have hex := h.poly i sigma hs
    have heqex := Option.some.inj (he.symm.trans hex)
    change exported = some sigma at heqex
    subst exported
    change sigma = scheme at heq
    subst scheme
    have hother : v ∉ sigma.body.freeVars := by
      have hfixed : sigma ∈ state.exports.filterMap id := by
        apply List.mem_filterMap.mpr
        exact ⟨some sigma, List.mem_of_getElem? hex, rfl⟩
      -- Complete contracts are entries in the fixed boundary. Their free
      -- variables must be excluded from a previously generalized pool.
      exact h.pool_poly sigma ⟨i, hs⟩ v hv
    exact hother
  | mono ty =>
    have hx := h.mono i ty hs
    by_cases hd : i ∈ done
    · simp only [hd, ↓reduceIte] at hx
      obtain ⟨written, _, _, _, _, hex⟩ := hx
      have heqex := Option.some.inj (he.symm.trans hex)
      change exported = some (recScheme written state.pool ty) at heqex
      subst exported
      change recScheme written state.pool ty = scheme at heq
      subst scheme
      exact fun hm => Ty.not_mem_closeOver_freeVars
        (mem_recNames_of_mem_pool hv (Ty.freeVars_closeOver_subset hm)) hm
    · simp only [hd, ↓reduceIte] at hx
      have heqex := Option.some.inj (he.symm.trans hx)
      change exported = none at heqex
      subst exported
      change PolyTy.mkTrivial ty = scheme at heq
      subst scheme
      rw [h.pending.mono i ty hs hd]
      simp only [PolyTy.mkTrivial, Ty.freeVars, List.mem_singleton]
      exact fun heq => h.pool_pending i ty hs hd (heq ▸ hv)

 theorem RecState.Frame.pool_rhsCtx {state : RecState} {base : Nat} {K : List Nat}
    {F : List Ty} {ctx : Ctx} {anns : List BindingAnn} {done : List Nat}
    (h : state.Frame base K F ctx anns done) :
    ∀ v ∈ state.pool, v ∉ (state.rhsCtx ctx).env.freeVars := by
  intro v hv hm
  obtain ⟨scheme, hs, ht⟩ := Env.mem_freeVars_iff.mp hm
  exact (List.mem_append.mp hs).elim
    (fun hentry => h.pool_entries v hv scheme hentry ht)
    (fun houter => h.pool_ctx v hv (Env.mem_freeVars_iff.mpr ⟨scheme, houter, ht⟩))

 theorem RecState.Frame.installOpenings {state : RecState} {base : Nat} {K : List Nat}
    {F : List Ty} {ctx : Ctx} {anns : List BindingAnn} {done members : List Nat}
    {openings : List RecOpening} (h : state.Frame base K F ctx anns done)
    (hnot : ∀ i ∈ members, i ∉ done) :
    (state.installOpenings members openings).Frame base K F ctx anns done := by
  refine ⟨h.specs_length, by simpa only [RecState.installOpenings, List.length_mapIdx] using h.slots_length,
    h.exports_length, h.outputs_length, h.facts_length, h.modes, h.poly, ?_, h.pending,
    h.pool_nodup, h.pool_ctx, h.pool_rigid, h.pool_soft, h.pool_poly, h.pool_pending,
    h.rigid_below, h.pending_soft⟩
  intro i ty hs
  have hm := h.mono i ty hs
  by_cases hd : i ∈ done
  · simp only [hd, ↓reduceIte] at hm ⊢
    obtain ⟨written, hslot, hcount, hnd, hpool, hex⟩ := hm
    refine ⟨written, ?_, hcount, hnd, hpool, hex⟩
    have hi : i ∉ members := fun hc => hnot i hc hd
    simp only [RecState.installOpenings, List.getElem?_mapIdx, hslot, Option.map_some, if_neg hi]
  · simpa only [hd, ↓reduceIte] using hm


/-- Read completed members' ordered written representatives from the retained
slot images. Complete contracts introduce no provisional slots. -/
def RecState.prefixes (state : RecState) : List (List Nat) :=
  state.specs.mapIdx (fun i spec => match spec with
    | .poly _ => []
    | .mono _ => (state.slots[i]?.getD []).filterMap recSlotName)

/-- A historical SCC stage exposes only exports from earlier components.
Later exports cannot change the environment in which an earlier RHS was checked. -/
def RecState.stageEntries (state : RecState) (earlier : List Nat) : List PolyTy :=
  state.specs.mapIdx (fun i spec => if i ∈ earlier then
    ((state.exports[i]?).join).getD spec.monoEntry else spec.monoEntry)

def RecState.stageCtx (state : RecState) (ctx : Ctx) (earlier : List Nat) : Ctx :=
  { ctx with env := state.stageEntries earlier ++ ctx.env }

 theorem RecState.stageEntries_onSubst (state : RecState) (S : Subst) (earlier : List Nat) :
    (state.onSubst S).stageEntries earlier = S.onEnv (state.stageEntries earlier) := by
  apply List.ext_getElem?
  intro i
  simp only [RecState.stageEntries, RecState.onSubst, Subst.onEnv,
    List.getElem?_mapIdx, List.getElem?_map, Option.map_map]
  cases hs : state.specs[i]? with
  | none => rfl
  | some spec =>
    simp only [Option.map_some]
    by_cases hi : i ∈ earlier
    · simp only [hi, if_pos]
      cases he : state.exports[i]? with
      | none => cases spec <;> rfl
      | some exported => cases exported <;> cases spec <;> rfl
    · simp only [hi]
      cases spec <;> rfl

 theorem RecState.stageCtx_onSubst (state : RecState) (S : Subst) (ctx : Ctx) (earlier : List Nat) :
    (state.onSubst S).stageCtx (S.onCtx ctx) earlier = S.onCtx (state.stageCtx ctx earlier) := by
  simp only [RecState.stageCtx, RecState.stageEntries_onSubst, Subst.onCtx, Subst.onEnv, List.map_append]

/-- Historical monomorphic checks retain each component's original stage.
Only the type state changes under later substitutions; earlier checks are not
silently rechecked in an environment where their own SCC is polymorphic. -/
def RecState.InputTrace (Q : List Nat) (ctx : Ctx) (anns : List BindingAnn)
    (bindings : List InferInput) (past : List (List Nat)) (state : RecState) : Prop :=
  ∀ (stage : Nat) (component : List Nat), past[stage]? = some component →
    ∀ (i : Nat) (ann : BindingAnn) (rhs : InferInput) (ty : Ty), i ∈ component →
      anns[i]? = some ann → bindings[i]? = some rhs → state.specs[i]? = some (.mono ty) →
      ann.RecFits (state.prefixes[i]?.getD []) ty ∧
      InputTyping (Q ++ state.prefixes[i]?.getD [])
        (state.stageCtx ctx (past.take stage).flatten)
        (rhs.openTyVars (state.prefixes[i]?.getD [])) ty


private theorem boundary_freeVarsList_mem {tys : List Ty} (ht : ty ∈ tys) (hv : v ∈ ty.freeVars) :
    v ∈ Ty.freeVarsList tys := by
  induction tys with
  | nil => cases ht
  | cons head rest ih =>
    apply List.mem_dedup.mpr
    rcases List.mem_cons.mp ht with rfl | ht
    · exact List.mem_append_left _ hv
    · exact List.mem_append_right _ (ih ht)

/-- Finalization includes every selected monotype variable outside its fixed
boundary, regardless of slot images, graph order, or type-variable bounds. -/
theorem RecState.componentPool_covers {state : RecState}
    (hi : i ∈ members) (ht : state.specs[i]? = some (.mono ty)) (hv : v ∈ ty.freeVars)
    (hctx : v ∉ (state.fixedCtx ctx).env.freeVars) (hK : v ∉ K) (hsoft : v ∉ soft) :
    v ∈ state.componentPool K soft members ctx written := by
  by_cases hp : v ∈ state.pool
  · exact List.mem_append_left _ hp
  · have hty : ty ∈ RecSpecs.monoTysAt state.specs members := by
      apply List.mem_filterMap.mpr
      exact ⟨i,hi,by simp [ht,RecSpec.monoTy?]⟩
    have hgen : v ∈ genGroupVars (K ++ soft ++ state.pool) (state.fixedCtx ctx).env
        (RecSpecs.monoTysAt state.specs members) := by
      apply List.mem_filter.mpr
      exact ⟨boundary_freeVarsList_mem hty hv,by simp [hctx,hK,hsoft,hp]⟩
    exact List.mem_append_right _ (List.mem_filter.mpr
      ⟨List.mem_dedup.mpr (List.mem_append_right _ hgen),decide_eq_true hp⟩)

/-- An exported selected monotype has no free variables outside the fixed
outer/export context, the frozen set, and the live soft-variable boundary. -/
theorem FinishRecComponent.export_freeVars_boundary
    (h : FinishRecComponent K soft members ctx state outputs facts final)
    (hi : i ∈ members) (ht : state.specs[i]? = some (.mono ty))
    (hex : final.exports[i]? = some (some scheme)) :
    ∀ v ∈ scheme.body.freeVars, v ∈ (state.fixedCtx ctx).env.freeVars ∨ v ∈ K ∨ v ∈ soft := by
  cases h with
  | mk hresolve =>
    expose_names
    rw [RecState.exportComponent,List.getElem?_mapIdx] at hex
    obtain ⟨old,_,heq⟩ := Option.map_eq_some_iff.mp hex
    simp only [if_pos hi,ht,RecSpec.completedScheme] at heq
    have hs : recScheme (written[i]?.getD [])
        (state.componentPool K soft members ctx written) ty = scheme := Option.some.inj heq
    subst scheme
    intro v hv
    by_cases hctx : v ∈ (state.fixedCtx ctx).env.freeVars
    · exact Or.inl hctx
    by_cases hK : v ∈ K
    · exact Or.inr (Or.inl hK)
    by_cases hsoft : v ∈ soft
    · exact Or.inr (Or.inr hsoft)
    have hfree := Ty.freeVars_closeOver_subset hv
    have hpool := state.componentPool_covers (written := written) hi ht hfree hctx hK hsoft
    exact False.elim (Ty.not_mem_closeOver_freeVars (mem_recNames_of_mem_pool hpool hfree) hv)

end
