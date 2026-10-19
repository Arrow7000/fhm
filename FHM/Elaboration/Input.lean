import FHM.Core

namespace Elaboration

/-- The fixed leaves retain authored type syntax; every `hole` occurrence is
independent. `fixed` is also the embedding of a complete monotype. -/
inductive Template where
  | fixed (ty : Ty)
  | hole
  | arrow (domain codomain : Template)
  | custom (name : TyName) (args : List Template)

/-- Declarative matching of an annotation template. This relation neither
allocates metavariables nor mentions inference or an executable substitution. -/
inductive Template.Fits : Template → Ty → Prop
  | fixed : Fits (.fixed ty) ty
  | hole : Fits .hole ty
  | arrow : Fits a ta → Fits b tb → Fits (.arrow a b) (.arrow ta tb)
  | custom : List.Forall₂ Fits args tys → Fits (.custom name args) (.customTy name tys)

mutual
def Template.rigidVars : Template → List Nat
  | .fixed ty => ty.freeVars
  | .hole => []
  | .arrow a b => a.rigidVars ++ b.rigidVars
  | .custom _ args => rigidVarsList args
def rigidVarsList : List Template → List Nat
  | [] => []
  | template :: rest => template.rigidVars ++ rigidVarsList rest
end


/-- Complete signatures and partial signatures have different checking modes.
The quantified partial form is recorded separately pending its scoped rule. -/
inductive LetAnn where
  | absent
  | complete (scheme : PolyTy)
  | template (body : Template)
  | partialForall (paramCount : Nat) (body : Template)

/-- A Core-shaped input spine. Type annotations are inputs to elaboration,
whereas the output is always the existing ordinary Core `Expr`. -/
inductive Input where
  | primLit (value : PrimLitExpr)
  | primBinOp (op : PrimBinOp)
  | lambda (ann : Option Template) (body : Input)
  | app (fn arg : Input)
  | letIn (ann : LetAnn) (rhs body : Input)
  | var (index : Nat)
  | ctor (name : CtorName)
  | match_ (scrutinee : Input) (branches : List (MatchPattern × Input))
  | letRec (anns : List LetAnn) (bindings : List Input) (body : Input)

mutual
/-- Runtime shape, independently of any choices made for anonymous holes. -/
def Input.erase : Input → Expr
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
def eraseBranches : List (MatchPattern × Input) → List (MatchPattern × Expr)
  | [] => []
  | (pat, body) :: rest => (pat, body.erase) :: eraseBranches rest
def eraseBindings : List Input → List Expr
  | [] => []
  | body :: rest => body.erase :: eraseBindings rest
end

/-- Complete annotation modes only. A partial mode stays partial even if its
template happens not to contain a hole. -/
def LetAnn.toCore : LetAnn → Option (Option PolyTy)
  | .absent => some none
  | .complete scheme => some (some scheme)
  | .template _ | .partialForall _ _ => none

mutual
def Template.toCore : Template → Option Ty
  | .fixed ty => some ty
  | .hole => none
  | .arrow a b => return .arrow (← a.toCore) (← b.toCore)
  | .custom name args => return .customTy name (← completeTypes args)
def completeTypes : List Template → Option (List Ty)
  | [] => some []
  | template :: rest => return (← template.toCore) :: (← completeTypes rest)
end

def completeLambdaAnn : Option Template → Option (Option Ty)
  | none => some none
  | some template => return some (← template.toCore)

mutual
/-- A decidable conservative embedding, preserving complete/partial modes.
Only a whole subtree successfully embedded here may use the old Core backend. -/
def Input.toCore : Input → Option Expr
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
def completeBranches : List (MatchPattern × Input) → Option (List (MatchPattern × Expr))
  | [] => some []
  | (pat, body) :: rest => return (pat, ← body.toCore) :: (← completeBranches rest)
def completeBindings : List Input → Option (List Expr)
  | [] => some []
  | body :: rest => return (← body.toCore) :: (← completeBindings rest)
def completeAnns : List LetAnn → Option (List (Option PolyTy))
  | [] => some []
  | ann :: rest => return (← ann.toCore) :: (← completeAnns rest)
end

mutual
theorem Input.toCore_erase (input : Input) {core : Expr}
    (h : input.toCore = some core) : core.erase = input.erase := by
  cases input with
  | primLit p => cases h; simp only [Expr.erase, Input.erase]
  | primBinOp op => cases h; simp only [Expr.erase, Input.erase]
  | var i => cases h; simp only [Expr.erase, Input.erase]
  | ctor c => cases h; simp only [Expr.erase, Input.erase]
  | lambda ann body =>
      simp only [Input.toCore, bind, pure, Option.bind_eq_some_iff,
        Option.some.injEq] at h
      obtain ⟨ann', _, body', hb, rfl⟩ := h
      simp only [Expr.erase, Input.erase, body.toCore_erase hb]
  | app f x =>
      simp only [Input.toCore, bind, pure, Option.bind_eq_some_iff,
        Option.some.injEq] at h
      obtain ⟨f', hf, x', hx, rfl⟩ := h
      simp only [Expr.erase, Input.erase, f.toCore_erase hf, x.toCore_erase hx]
  | letIn ann rhs body =>
      simp only [Input.toCore, bind, pure, Option.bind_eq_some_iff,
        Option.some.injEq] at h
      obtain ⟨ann', _, rhs', hr, body', hb, rfl⟩ := h
      simp only [Expr.erase, Input.erase, rhs.toCore_erase hr, body.toCore_erase hb]
  | match_ scrut branches =>
      simp only [Input.toCore, bind, pure, Option.bind_eq_some_iff,
        Option.some.injEq] at h
      obtain ⟨scrut', hs, branches', hb, rfl⟩ := h
      simp only [Expr.erase, Input.erase, scrut.toCore_erase hs, completeBranches_erase branches hb]
  | letRec anns bindings body =>
      simp only [Input.toCore, bind, pure, Option.bind_eq_some_iff,
        Option.some.injEq] at h
      obtain ⟨anns', _, bindings', hr, body', hb, rfl⟩ := h
      have hbindings := completeBindings_erase bindings hr
      have hlength : bindings'.length = bindings.length := by
        have := congrArg List.length hbindings
        simpa only [List.length_map, eraseBindings_length] using this
      simp only [Expr.erase, Input.erase, body.toCore_erase hb, hbindings]
      congr 1
      simp only [List.map_const', hlength]
theorem completeBranches_erase (inputs : List (MatchPattern × Input))
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
theorem completeBindings_erase (inputs : List Input) {cores : List Expr}
    (h : completeBindings inputs = some cores) :
    cores.map Expr.erase = eraseBindings inputs := by
  cases inputs with
  | nil => cases h; rfl
  | cons body rest =>
      simp only [completeBindings, bind, pure, Option.bind_eq_some_iff,
        Option.some.injEq] at h
      obtain ⟨body', hb, rest', hr, rfl⟩ := h
      simp only [List.map_cons, eraseBindings, body.toCore_erase hb, completeBindings_erase rest hr]
theorem eraseBindings_length (inputs : List Input) : (eraseBindings inputs).length = inputs.length := by
  cases inputs with
  | nil => rfl
  | cons body rest =>
      simpa only [eraseBindings, List.length_cons] using congrArg Nat.succ (eraseBindings_length rest)
end

/-- A partial ordinary signature constrains the inferred monotype before that
monotype is generalised. It is not an existential complete Core signature. -/
def LetAnn.FitsMono : LetAnn → Ty → Prop
  | .absent, _ => True
  | .template t, ty => t.Fits ty
  | _, _ => False

mutual
/-- Instantiate a template at a local inference visit. No authored IDs or
cross-copy allocation table participate in this operation. -/
def Template.allocate (frontier : Nat) : Template → Nat × Ty
  | .fixed ty => (frontier, ty)
  | .hole => (frontier + 1, .fvar frontier)
  | .arrow a b =>
      let (next, ta) := a.allocate frontier
      let (last, tb) := b.allocate next
      (last, .arrow ta tb)
  | .custom name args =>
      let (next, tys) := allocateList frontier args
      (next, .customTy name tys)
def allocateList (frontier : Nat) : List Template → Nat × List Ty
  | [] => (frontier, [])
  | template :: rest =>
      let (next, ty) := template.allocate frontier
      let (last, tys) := allocateList next rest
      (last, ty :: tys)
end

mutual
theorem Template.allocate_fits (template : Template) (frontier : Nat) :
    template.Fits (template.allocate frontier).2 := by
  cases template with
  | fixed => exact .fixed
  | hole => exact .hole
  | arrow a b =>
      exact .arrow (a.allocate_fits frontier) (b.allocate_fits (a.allocate frontier).1)
  | custom name args => exact .custom (allocateList_fits args frontier)
theorem allocateList_fits (templates : List Template) (frontier : Nat) :
    List.Forall₂ Template.Fits templates (allocateList frontier templates).2 := by
  cases templates with
  | nil => exact .nil
  | cons template rest =>
      exact .cons (template.allocate_fits frontier) (allocateList_fits rest (template.allocate frontier).1)
end


mutual
/-- Term size ignores annotations, so opening written type binders preserves it. -/
def Input.size : Input → Nat
  | .primLit _ | .primBinOp _ | .var _ | .ctor _ => 1
  | .lambda _ body => body.size + 1
  | .app f arg => f.size + arg.size + 1
  | .letIn _ rhs body => rhs.size + body.size + 1
  | .match_ scrut branches => scrut.size + sizeBranches branches + 1
  | .letRec _ bindings body => sizeBindings bindings + body.size + 1
def sizeBranches : List (MatchPattern × Input) → Nat
  | [] => 0
  | (_, body) :: rest => 1 + body.size + sizeBranches rest
def sizeBindings : List Input → Nat
  | [] => 0
  | body :: rest => 1 + body.size + sizeBindings rest
end

/-- Authored free type variables are rigid; anonymous holes contribute none. -/
def LetAnn.isSignature : LetAnn → Bool
  | .complete _ | .partialForall _ _ => true
  | .absent | .template _ => false

def LetAnn.rigidVars : LetAnn → List Nat
  | .absent => []
  | .complete scheme => scheme.body.freeVars
  | .template t => t.rigidVars
  | .partialForall _ t => t.rigidVars

mutual
def Input.rigidVars : Input → List Nat
  | .primLit _ | .primBinOp _ | .var _ | .ctor _ => []
  | .lambda ann body => ann.elim [] Template.rigidVars ++ body.rigidVars
  | .app f arg => f.rigidVars ++ arg.rigidVars
  | .letIn ann rhs body => ann.rigidVars ++ rhs.rigidVars ++ body.rigidVars
  | .match_ scrut branches => scrut.rigidVars ++ rigidBranchVars branches
  | .letRec anns bindings body => anns.flatMap LetAnn.rigidVars ++ rigidBindingVars bindings ++ body.rigidVars
def rigidBranchVars : List (MatchPattern × Input) → List Nat
  | [] => []
  | (_, body) :: rest => body.rigidVars ++ rigidBranchVars rest
def rigidBindingVars : List Input → List Nat
  | [] => []
  | body :: rest => body.rigidVars ++ rigidBindingVars rest
end

/-- Embed complete ordinary Core without changing annotation modes. -/
def LetAnn.ofCore : Option PolyTy → LetAnn
  | none => .absent
  | some scheme => .complete scheme

mutual
def Input.ofCore : Expr → Input
  | .primLit p => .primLit p
  | .primBinOp op => .primBinOp op
  | .lambda ann body => .lambda (ann.map Template.fixed) (Input.ofCore body)
  | .app f arg => .app (Input.ofCore f) (Input.ofCore arg)
  | .letIn ann rhs body => .letIn (LetAnn.ofCore ann) (Input.ofCore rhs) (Input.ofCore body)
  | .var i => .var i
  | .ctor name => .ctor name
  | .match_ scrut branches => .match_ (Input.ofCore scrut) (ofCoreBranches branches)
  | .letRec anns bindings body =>
      .letRec (anns.map LetAnn.ofCore) (ofCoreBindings bindings) (Input.ofCore body)
def ofCoreBranches : List (MatchPattern × Expr) → List (MatchPattern × Input)
  | [] => []
  | (pat, body) :: rest => (pat, (Input.ofCore body)) :: ofCoreBranches rest
def ofCoreBindings : List Expr → List Input
  | [] => []
  | body :: rest => (Input.ofCore body) :: ofCoreBindings rest
end

@[simp] theorem LetAnn.toCore_ofCore (ann : Option PolyTy) :
    (LetAnn.ofCore ann).toCore = some ann := by cases ann <;> rfl

private theorem completeAnns_ofCore (anns : List (Option PolyTy)) :
    completeAnns (anns.map LetAnn.ofCore) = some anns := by
  induction anns with
  | nil => rfl
  | cons ann anns ih => simp only [List.map_cons, completeAnns, LetAnn.toCore_ofCore, ih]; rfl

mutual
@[simp] theorem Input.toCore_ofCore (expr : Expr) : (Input.ofCore expr).toCore = some expr := by
  cases expr with
  | primLit => rfl
  | primBinOp => rfl
  | var => rfl
  | ctor => rfl
  | lambda ann body =>
    have ha : completeLambdaAnn (ann.map Template.fixed) = some ann := by cases ann <;> rfl
    simp only [Input.ofCore, Input.toCore, ha, Input.toCore_ofCore body]; rfl
  | app f arg => simp only [Input.ofCore, Input.toCore, Input.toCore_ofCore f, Input.toCore_ofCore arg]; rfl
  | letIn ann rhs body =>
    simp only [Input.ofCore, Input.toCore, LetAnn.toCore_ofCore, Input.toCore_ofCore rhs, Input.toCore_ofCore body]; rfl
  | match_ scrut branches =>
    simp only [Input.ofCore, Input.toCore, Input.toCore_ofCore scrut, completeBranches_ofCore branches]; rfl
  | letRec anns bindings body =>
    simp only [Input.ofCore, Input.toCore, completeAnns_ofCore, completeBindings_ofCore bindings,
      Input.toCore_ofCore body]; rfl
theorem completeBranches_ofCore (branches : List (MatchPattern × Expr)) :
    completeBranches (ofCoreBranches branches) = some branches := by
  cases branches with
  | nil => rfl
  | cons pair rest =>
    rcases pair with ⟨pat, body⟩
    simp only [ofCoreBranches, completeBranches, Input.toCore_ofCore body, completeBranches_ofCore rest]; rfl
theorem completeBindings_ofCore (bindings : List Expr) :
    completeBindings (ofCoreBindings bindings) = some bindings := by
  cases bindings with
  | nil => rfl
  | cons body rest =>
    simp only [ofCoreBindings, completeBindings, Input.toCore_ofCore body, completeBindings_ofCore rest]; rfl
end

mutual
/-- Shift term variables while preserving every authored partial annotation. -/
def Input.shiftFrom (threshold count : Nat) : Input → Input
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
def shiftBranches (threshold count : Nat) : List (MatchPattern × Input) → List (MatchPattern × Input)
  | [] => []
  | (pat, body) :: rest =>
      (pat, body.shiftFrom (threshold + pat.bindCount) count) :: shiftBranches threshold count rest
def shiftBindings (threshold count : Nat) : List Input → List Input
  | [] => []
  | body :: rest => body.shiftFrom threshold count :: shiftBindings threshold count rest
end


mutual
/-- Open an enclosing written type-variable block through a template. Anonymous
holes are unchanged and never acquire an authored variable identity. -/
def Template.openTyVarsFrom (d : Nat) (Xs : List Nat) : Template → Template
  | .fixed ty => .fixed (ty.openVarsFrom d Xs)
  | .hole => .hole
  | .arrow a b => .arrow (a.openTyVarsFrom d Xs) (b.openTyVarsFrom d Xs)
  | .custom name args => .custom name (openTemplateList d Xs args)
def openTemplateList (d : Nat) (Xs : List Nat) : List Template → List Template
  | [] => []
  | t :: ts => t.openTyVarsFrom d Xs :: openTemplateList d Xs ts
end

/-- A signature's own binders shield its annotation and RHS, but not the let
continuation. This also applies when its body contains anonymous holes. -/
def LetAnn.paramCount : LetAnn → Nat
  | .complete scheme => scheme.paramCount
  | .partialForall n _ => n
  | .absent | .template _ => 0

def LetAnn.openTyVarsFrom (d : Nat) (Xs : List Nat) : LetAnn → LetAnn
  | .absent => .absent
  | .complete scheme => .complete { scheme with
      body := scheme.body.openVarsFrom (d + scheme.paramCount) Xs }
  | .template t => .template (t.openTyVarsFrom d Xs)
  | .partialForall n t => .partialForall n (t.openTyVarsFrom (d + n) Xs)

mutual
/-- Open the type binders of an enclosing signature with the same scope rules
as `Expr.openTyVarsAux`, retaining every partial annotation mode. -/
def Input.openTyVarsFrom (d : Nat) (Xs : List Nat) : Input → Input
  | .primLit p => .primLit p
  | .primBinOp op => .primBinOp op
  | .lambda ann body => .lambda (ann.map (Template.openTyVarsFrom d Xs))
      (body.openTyVarsFrom d Xs)
  | .app f arg => .app (f.openTyVarsFrom d Xs) (arg.openTyVarsFrom d Xs)
  | .letIn ann rhs body => .letIn (ann.openTyVarsFrom d Xs)
      (rhs.openTyVarsFrom (d + ann.paramCount) Xs) (body.openTyVarsFrom d Xs)
  | .var i => .var i
  | .ctor name => .ctor name
  | .match_ scrut branches => .match_ (scrut.openTyVarsFrom d Xs)
      (openInputBranches d Xs branches)
  | .letRec anns bindings body => .letRec (anns.map (LetAnn.openTyVarsFrom d Xs))
      (openInputBindings d Xs anns bindings) (body.openTyVarsFrom d Xs)
def openInputBranches (d : Nat) (Xs : List Nat) :
    List (MatchPattern × Input) → List (MatchPattern × Input)
  | [] => []
  | (pat, body) :: rest => (pat, body.openTyVarsFrom d Xs) :: openInputBranches d Xs rest
/-- As in Core, missing recursion annotations are treated as absent; extra
annotations do not introduce binders over another member. -/
def openInputBindings (d : Nat) (Xs : List Nat) : List LetAnn → List Input → List Input
  | _, [] => []
  | [], body :: rest => body.openTyVarsFrom d Xs :: openInputBindings d Xs [] rest
  | ann :: anns, body :: rest => body.openTyVarsFrom (d + ann.paramCount) Xs ::
      openInputBindings d Xs anns rest
end

def Input.openTyVars (Xs : List Nat) (input : Input) : Input := input.openTyVarsFrom 0 Xs

@[simp] theorem LetAnn.paramCount_openTyVarsFrom (ann : LetAnn) (d : Nat) (Xs : List Nat) :
    (ann.openTyVarsFrom d Xs).paramCount = ann.paramCount := by cases ann <;> rfl

mutual
@[simp] theorem Input.size_openTyVarsFrom (input : Input) (d : Nat) (Xs : List Nat) :
    (input.openTyVarsFrom d Xs).size = input.size := by
  cases input with
  | primLit | primBinOp | var | ctor => rfl
  | lambda ann body => simp only [Input.openTyVarsFrom, Input.size, body.size_openTyVarsFrom d Xs]
  | app f a => simp only [Input.openTyVarsFrom, Input.size, f.size_openTyVarsFrom d Xs, a.size_openTyVarsFrom d Xs]
  | letIn ann rhs body => simp only [Input.openTyVarsFrom, Input.size,
      rhs.size_openTyVarsFrom (d + ann.paramCount) Xs, body.size_openTyVarsFrom d Xs]
  | match_ scrut branches => simp only [Input.openTyVarsFrom, Input.size,
      scrut.size_openTyVarsFrom d Xs, sizeBranches_openInputBranches branches d Xs]
  | letRec anns bindings body => simp only [Input.openTyVarsFrom, Input.size,
      sizeBindings_openInputBindings bindings anns d Xs, body.size_openTyVarsFrom d Xs]
termination_by sizeOf input
theorem sizeBranches_openInputBranches (branches : List (MatchPattern × Input)) (d : Nat) (Xs : List Nat) :
    sizeBranches (openInputBranches d Xs branches) = sizeBranches branches := by
  cases branches with
  | nil => rfl
  | cons pair rest =>
      rcases pair with ⟨pat, body⟩
      simp only [openInputBranches, sizeBranches, body.size_openTyVarsFrom d Xs,
        sizeBranches_openInputBranches rest d Xs]
termination_by sizeOf branches
theorem sizeBindings_openInputBindings (bindings : List Input) (anns : List LetAnn) (d : Nat) (Xs : List Nat) :
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

@[simp] theorem Input.size_openTyVars (input : Input) (Xs : List Nat) :
    (input.openTyVars Xs).size = input.size := input.size_openTyVarsFrom 0 Xs

theorem openInputBindings_length (bindings : List Input) (anns : List LetAnn) (d : Nat) (Xs : List Nat) :
    (openInputBindings d Xs anns bindings).length = bindings.length := by
  induction bindings generalizing anns with
  | nil => rfl
  | cons body rest ih => cases anns <;> simp only [openInputBindings, List.length_cons, ih]

mutual
@[simp] theorem Input.erase_openTyVarsFrom (input : Input) (d : Nat) (Xs : List Nat) :
    (input.openTyVarsFrom d Xs).erase = input.erase := by
  cases input with
  | primLit | primBinOp | var | ctor => rfl
  | lambda ann body => simp only [Input.openTyVarsFrom, Input.erase, body.erase_openTyVarsFrom d Xs]
  | app f a => simp only [Input.openTyVarsFrom, Input.erase, f.erase_openTyVarsFrom d Xs, a.erase_openTyVarsFrom d Xs]
  | letIn ann rhs body => simp only [Input.openTyVarsFrom, Input.erase,
      rhs.erase_openTyVarsFrom (d + ann.paramCount) Xs, body.erase_openTyVarsFrom d Xs]
  | match_ scrut branches => simp only [Input.openTyVarsFrom, Input.erase,
      scrut.erase_openTyVarsFrom d Xs, eraseBranches_openInputBranches branches d Xs]
  | letRec anns bindings body => simp only [Input.openTyVarsFrom, Input.erase,
      eraseBindings_openInputBindings bindings anns d Xs, body.erase_openTyVarsFrom d Xs,
      List.map_const', openInputBindings_length]
termination_by sizeOf input
theorem eraseBranches_openInputBranches (branches : List (MatchPattern × Input)) (d : Nat) (Xs : List Nat) :
    eraseBranches (openInputBranches d Xs branches) = eraseBranches branches := by
  cases branches with
  | nil => rfl
  | cons pair rest =>
      rcases pair with ⟨pat, body⟩
      simp only [openInputBranches, eraseBranches, body.erase_openTyVarsFrom d Xs,
        eraseBranches_openInputBranches rest d Xs]
termination_by sizeOf branches
theorem eraseBindings_openInputBindings (bindings : List Input) (anns : List LetAnn) (d : Nat) (Xs : List Nat) :
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

@[simp] theorem Input.erase_openTyVars (input : Input) (Xs : List Nat) :
    (input.openTyVars Xs).erase = input.erase := input.erase_openTyVarsFrom 0 Xs


mutual
theorem Template.toCore_openTyVarsFrom (template : Template) {ty : Ty}
    (h : template.toCore = some ty) (d : Nat) (Xs : List Nat) :
    (template.openTyVarsFrom d Xs).toCore = some (ty.openVarsFrom d Xs) := by
  cases template with
  | fixed t => cases h; rfl
  | hole => cases h
  | arrow a b =>
      simp only [Template.toCore, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at h
      obtain ⟨ta, ha, tb, hb, rfl⟩ := h
      simp only [Template.openTyVarsFrom, Template.toCore, a.toCore_openTyVarsFrom ha d Xs,
        b.toCore_openTyVarsFrom hb d Xs]
      rfl
  | custom name args =>
      simp only [Template.toCore, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at h
      obtain ⟨tys, ht, rfl⟩ := h
      simp only [Template.openTyVarsFrom, Template.toCore, completeTypes_openTemplateList args ht d Xs,
        Ty.openVarsFrom_customTy]
      rfl
theorem completeTypes_openTemplateList (templates : List Template) {tys : List Ty}
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

theorem completeLambdaAnn_openTyVarsFrom (ann : Option Template) {core : Option Ty}
    (h : completeLambdaAnn ann = some core) (d : Nat) (Xs : List Nat) :
    completeLambdaAnn (ann.map (Template.openTyVarsFrom d Xs)) =
      some (core.map (Ty.openVarsFrom d Xs)) := by
  cases ann with
  | none => cases h; rfl
  | some template =>
      simp only [completeLambdaAnn, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at h
      obtain ⟨ty, ht, rfl⟩ := h
      simp only [Option.map_some, completeLambdaAnn, template.toCore_openTyVarsFrom ht d Xs]
      rfl

theorem LetAnn.toCore_openTyVarsFrom (ann : LetAnn) {core : Option PolyTy}
    (h : ann.toCore = some core) (d : Nat) (Xs : List Nat) :
    (ann.openTyVarsFrom d Xs).toCore = some (core.map (fun scheme =>
      { scheme with body := scheme.body.openVarsFrom (d + scheme.paramCount) Xs })) := by
  cases ann <;> cases h <;> rfl

theorem LetAnn.paramCount_toCore (ann : LetAnn) {core : Option PolyTy}
    (h : ann.toCore = some core) : ann.paramCount = RecAnn.params core := by
  cases ann <;> cases h <;> rfl

theorem completeAnns_openTyVarsFrom (anns : List LetAnn) {cores : List (Option PolyTy)}
    (h : completeAnns anns = some cores) (d : Nat) (Xs : List Nat) :
    completeAnns (anns.map (LetAnn.openTyVarsFrom d Xs)) = some (RecGroup.openAnns d Xs cores) := by
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
theorem Input.toCore_openTyVarsFrom (input : Input) {core : Expr}
    (h : input.toCore = some core) (d : Nat) (Xs : List Nat) :
    (input.openTyVarsFrom d Xs).toCore = some (core.openTyVarsAux d Xs) := by
  cases input with
  | primLit p => cases h; rfl
  | primBinOp op => cases h; rfl
  | var i => cases h; rfl
  | ctor name => cases h; rfl
  | lambda ann body =>
      simp only [Input.toCore, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at h
      obtain ⟨ann', ha, body', hb, rfl⟩ := h
      simp only [Input.openTyVarsFrom, Input.toCore, completeLambdaAnn_openTyVarsFrom ann ha d Xs,
        body.toCore_openTyVarsFrom hb d Xs]
      rfl
  | app f arg =>
      simp only [Input.toCore, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at h
      obtain ⟨f', hf, arg', ha, rfl⟩ := h
      simp only [Input.openTyVarsFrom, Input.toCore, f.toCore_openTyVarsFrom hf d Xs,
        arg.toCore_openTyVarsFrom ha d Xs]
      rfl
  | letIn ann rhs body =>
      simp only [Input.toCore, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at h
      obtain ⟨ann', ha, rhs', hr, body', hb, rfl⟩ := h
      simp only [Input.openTyVarsFrom, Input.toCore, ann.toCore_openTyVarsFrom ha d Xs,
        rhs.toCore_openTyVarsFrom hr (d + ann.paramCount) Xs, body.toCore_openTyVarsFrom hb d Xs]
      rw [ann.paramCount_toCore ha]
      cases ann' <;> rfl
  | match_ scrut branches =>
      simp only [Input.toCore, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at h
      obtain ⟨scrut', hs, branches', hbs, rfl⟩ := h
      simp only [Input.openTyVarsFrom, Input.toCore, scrut.toCore_openTyVarsFrom hs d Xs,
        completeBranches_openTyVarsFrom branches hbs d Xs]
      rfl
  | letRec anns bindings body =>
      simp only [Input.toCore, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at h
      obtain ⟨anns', ha, bindings', hbs, body', hb, rfl⟩ := h
      simp only [Input.openTyVarsFrom, Input.toCore, completeAnns_openTyVarsFrom anns ha d Xs,
        completeBindings_openTyVarsFrom bindings anns ha hbs d Xs,
        body.toCore_openTyVarsFrom hb d Xs]
      rfl
termination_by sizeOf input
decreasing_by all_goals (subst_vars; simp_wf <;> omega)

theorem completeBranches_openTyVarsFrom (branches : List (MatchPattern × Input))
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

theorem completeBindings_openTyVarsFrom (bindings : List Input) (anns : List LetAnn)
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

theorem Input.toCore_openTyVars (input : Input) {core : Expr}
    (h : input.toCore = some core) (Xs : List Nat) :
    (input.openTyVars Xs).toCore = some (core.openTyVars Xs) :=
  input.toCore_openTyVarsFrom h 0 Xs

mutual
/-- Substitute only free variables in authored type leaves; anonymous holes
remain unallocated and independent. -/
def Template.substTyFvars (subst : List (Nat × Ty)) : Template → Template
  | .fixed ty => .fixed (ty.substFvars subst)
  | .hole => .hole
  | .arrow a b => .arrow (a.substTyFvars subst) (b.substTyFvars subst)
  | .custom name args => .custom name (substTemplateList subst args)
def substTemplateList (subst : List (Nat × Ty)) : List Template → List Template
  | [] => []
  | t :: ts => t.substTyFvars subst :: substTemplateList subst ts
end

/-- Free type substitution preserves annotation modes and written binders. -/
def LetAnn.substTyFvars (subst : List (Nat × Ty)) : LetAnn → LetAnn
  | .absent => .absent
  | .complete scheme => .complete { scheme with body := scheme.body.substFvars subst }
  | .template t => .template (t.substTyFvars subst)
  | .partialForall n t => .partialForall n (t.substTyFvars subst)

mutual
/-- Type substitution does not shift under type or term binders: all replaced
variables are free, just as for `Expr.substTyFvars`. -/
def Input.substTyFvars (subst : List (Nat × Ty)) : Input → Input
  | .primLit p => .primLit p
  | .primBinOp op => .primBinOp op
  | .lambda ann body => .lambda (ann.map (Template.substTyFvars subst)) (body.substTyFvars subst)
  | .app f arg => .app (f.substTyFvars subst) (arg.substTyFvars subst)
  | .letIn ann rhs body => .letIn (ann.substTyFvars subst) (rhs.substTyFvars subst) (body.substTyFvars subst)
  | .var i => .var i
  | .ctor name => .ctor name
  | .match_ scrut branches => .match_ (scrut.substTyFvars subst) (substInputBranches subst branches)
  | .letRec anns bindings body => .letRec (anns.map (LetAnn.substTyFvars subst))
      (substInputBindings subst bindings) (body.substTyFvars subst)
def substInputBranches (subst : List (Nat × Ty)) :
    List (MatchPattern × Input) → List (MatchPattern × Input)
  | [] => []
  | (pat, body) :: rest => (pat, body.substTyFvars subst) :: substInputBranches subst rest
def substInputBindings (subst : List (Nat × Ty)) : List Input → List Input
  | [] => []
  | body :: rest => body.substTyFvars subst :: substInputBindings subst rest
end

@[simp] theorem LetAnn.isSignature_substTyFvars (ann : LetAnn) (subst : List (Nat × Ty)) :
    (ann.substTyFvars subst).isSignature = ann.isSignature := by cases ann <;> rfl

@[simp] theorem LetAnn.paramCount_substTyFvars (ann : LetAnn) (subst : List (Nat × Ty)) :
    (ann.substTyFvars subst).paramCount = ann.paramCount := by cases ann <;> rfl

theorem substInputBranches_eq_map (subst : List (Nat × Ty)) (branches : List (MatchPattern × Input)) :
    substInputBranches subst branches = branches.map (fun b => (b.1, b.2.substTyFvars subst)) := by
  induction branches with
  | nil => rfl
  | cons head rest ih => cases head; simp only [substInputBranches, List.map_cons, ih]

@[simp] theorem substInputBranches_eq_nil (subst : List (Nat × Ty))
    (branches : List (MatchPattern × Input)) :
    substInputBranches subst branches = [] ↔ branches = [] := by
  cases branches <;> simp [substInputBranches]

mutual
@[simp] theorem Input.size_substTyFvars (input : Input) (subst : List (Nat × Ty)) :
    (input.substTyFvars subst).size = input.size := by
  cases input with
  | primLit | primBinOp | var | ctor => rfl
  | lambda ann body => simp only [Input.substTyFvars, Input.size, body.size_substTyFvars subst]
  | app f a => simp only [Input.substTyFvars, Input.size, f.size_substTyFvars subst, a.size_substTyFvars subst]
  | letIn ann rhs body => simp only [Input.substTyFvars, Input.size,
      rhs.size_substTyFvars subst, body.size_substTyFvars subst]
  | match_ scrut branches => simp only [Input.substTyFvars, Input.size,
      scrut.size_substTyFvars subst, sizeBranches_substInputBranches branches subst]
  | letRec anns bindings body => simp only [Input.substTyFvars, Input.size,
      sizeBindings_substInputBindings bindings subst, body.size_substTyFvars subst]
termination_by sizeOf input
theorem sizeBranches_substInputBranches (branches : List (MatchPattern × Input)) (subst : List (Nat × Ty)) :
    sizeBranches (substInputBranches subst branches) = sizeBranches branches := by
  cases branches with
  | nil => rfl
  | cons pair rest =>
      rcases pair with ⟨pat, body⟩
      simp only [substInputBranches, sizeBranches, body.size_substTyFvars subst,
        sizeBranches_substInputBranches rest subst]
termination_by sizeOf branches
theorem sizeBindings_substInputBindings (bindings : List Input) (subst : List (Nat × Ty)) :
    sizeBindings (substInputBindings subst bindings) = sizeBindings bindings := by
  cases bindings with
  | nil => rfl
  | cons body rest =>
      simp only [substInputBindings, sizeBindings, body.size_substTyFvars subst,
          sizeBindings_substInputBindings rest subst]
termination_by sizeOf bindings
end

theorem substInputBindings_length (bindings : List Input) (subst : List (Nat × Ty)) :
    (substInputBindings subst bindings).length = bindings.length := by
  induction bindings with
  | nil => rfl
  | cons body rest ih => simp only [substInputBindings, List.length_cons, ih]

mutual
@[simp] theorem Input.erase_substTyFvars (input : Input) (subst : List (Nat × Ty)) :
    (input.substTyFvars subst).erase = input.erase := by
  cases input with
  | primLit | primBinOp | var | ctor => rfl
  | lambda ann body => simp only [Input.substTyFvars, Input.erase, body.erase_substTyFvars subst]
  | app f a => simp only [Input.substTyFvars, Input.erase, f.erase_substTyFvars subst, a.erase_substTyFvars subst]
  | letIn ann rhs body => simp only [Input.substTyFvars, Input.erase,
      rhs.erase_substTyFvars subst, body.erase_substTyFvars subst]
  | match_ scrut branches => simp only [Input.substTyFvars, Input.erase,
      scrut.erase_substTyFvars subst, eraseBranches_substInputBranches branches subst]
  | letRec anns bindings body => simp only [Input.substTyFvars, Input.erase,
      eraseBindings_substInputBindings bindings subst, body.erase_substTyFvars subst,
      List.map_const', substInputBindings_length]
termination_by sizeOf input
theorem eraseBranches_substInputBranches (branches : List (MatchPattern × Input)) (subst : List (Nat × Ty)) :
    eraseBranches (substInputBranches subst branches) = eraseBranches branches := by
  cases branches with
  | nil => rfl
  | cons pair rest =>
      rcases pair with ⟨pat, body⟩
      simp only [substInputBranches, eraseBranches, body.erase_substTyFvars subst,
        eraseBranches_substInputBranches rest subst]
termination_by sizeOf branches
theorem eraseBindings_substInputBindings (bindings : List Input) (subst : List (Nat × Ty)) :
    eraseBindings (substInputBindings subst bindings) = eraseBindings bindings := by
  cases bindings with
  | nil => rfl
  | cons body rest =>
      simp only [substInputBindings, eraseBindings, body.erase_substTyFvars subst,
          eraseBindings_substInputBindings rest subst]
termination_by sizeOf bindings
end

mutual
theorem Template.toCore_substTyFvars (template : Template) {ty : Ty}
    (h : template.toCore = some ty) (subst : List (Nat × Ty)) :
    (template.substTyFvars subst).toCore = some (ty.substFvars subst) := by
  cases template with
  | fixed t => cases h; rfl
  | hole => cases h
  | arrow a b =>
      simp only [Template.toCore, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at h
      obtain ⟨ta, ha, tb, hb, rfl⟩ := h
      simp only [Template.substTyFvars, Template.toCore, a.toCore_substTyFvars ha subst,
        b.toCore_substTyFvars hb subst, Ty.substFvars_arrow]
      rfl
  | custom name args =>
      simp only [Template.toCore, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at h
      obtain ⟨tys, ht, rfl⟩ := h
      simp only [Template.substTyFvars, Template.toCore, completeTypes_substTemplateList args ht subst,
        Ty.substFvars_customTy]
      rfl
theorem completeTypes_substTemplateList (templates : List Template) {tys : List Ty}
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

theorem completeLambdaAnn_substTyFvars (ann : Option Template) {core : Option Ty}
    (h : completeLambdaAnn ann = some core) (subst : List (Nat × Ty)) :
    completeLambdaAnn (ann.map (Template.substTyFvars subst)) =
      some (core.map (Ty.substFvars subst)) := by
  cases ann with
  | none => cases h; rfl
  | some template =>
      simp only [completeLambdaAnn, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at h
      obtain ⟨ty, ht, rfl⟩ := h
      simp only [Option.map_some, completeLambdaAnn, template.toCore_substTyFvars ht subst]
      rfl

theorem LetAnn.toCore_substTyFvars (ann : LetAnn) {core : Option PolyTy}
    (h : ann.toCore = some core) (subst : List (Nat × Ty)) :
    (ann.substTyFvars subst).toCore = some (core.map (fun scheme =>
      { scheme with body := scheme.body.substFvars subst })) := by
  cases ann <;> cases h <;> rfl

theorem completeAnns_substTyFvars (anns : List LetAnn) {cores : List (Option PolyTy)}
    (h : completeAnns anns = some cores) (subst : List (Nat × Ty)) :
    completeAnns (anns.map (LetAnn.substTyFvars subst)) = some (cores.map (Option.map (fun scheme => {scheme with body := scheme.body.substFvars subst}))) := by
  induction anns generalizing cores with
  | nil => cases h; rfl
  | cons ann anns ih =>
      simp only [completeAnns, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at h
      obtain ⟨core, ha, cores, has, rfl⟩ := h
      simp only [List.map_cons, completeAnns, ann.toCore_substTyFvars ha subst, ih has]
      rfl

mutual
/-- Conservative embedding commutes with free type substitution. -/
theorem Input.toCore_substTyFvars (input : Input) {core : Expr}
    (h : input.toCore = some core) (subst : List (Nat × Ty)) :
    (input.substTyFvars subst).toCore = some (core.substTyFvars subst) := by
  cases input with
  | primLit p =>
      cases h
      induction subst with
      | nil => rfl
      | cons pair rest ih => cases pair; simpa only [Input.substTyFvars, Input.toCore, Expr.substTyFvars, Expr.substTyFvar] using ih
  | primBinOp op =>
      cases h
      induction subst with
      | nil => rfl
      | cons pair rest ih => cases pair; simpa only [Input.substTyFvars, Input.toCore, Expr.substTyFvars, Expr.substTyFvar] using ih
  | var i => cases h; simp only [Input.substTyFvars, Input.toCore, Expr.substTyFvars_var]
  | ctor name =>
      cases h
      induction subst with
      | nil => rfl
      | cons pair rest ih => cases pair; simpa only [Input.substTyFvars, Input.toCore, Expr.substTyFvars, Expr.substTyFvar] using ih
  | lambda ann body =>
      simp only [Input.toCore, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at h
      obtain ⟨ann', ha, body', hb, rfl⟩ := h
      simp only [Input.substTyFvars, Input.toCore, completeLambdaAnn_substTyFvars ann ha subst,
        body.toCore_substTyFvars hb subst, Expr.substTyFvars_lambda]
      rfl
  | app f arg =>
      simp only [Input.toCore, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at h
      obtain ⟨f', hf, arg', ha, rfl⟩ := h
      simp only [Input.substTyFvars, Input.toCore, f.toCore_substTyFvars hf subst,
        arg.toCore_substTyFvars ha subst, Expr.substTyFvars_app]
      rfl
  | letIn ann rhs body =>
      simp only [Input.toCore, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at h
      obtain ⟨ann', ha, rhs', hr, body', hb, rfl⟩ := h
      simp only [Input.substTyFvars, Input.toCore, ann.toCore_substTyFvars ha subst,
        rhs.toCore_substTyFvars hr subst, body.toCore_substTyFvars hb subst]
      rw [Expr.substTyFvars_letIn]
      rfl
  | match_ scrut branches =>
      simp only [Input.toCore, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at h
      obtain ⟨scrut', hs, branches', hbs, rfl⟩ := h
      simp only [Input.substTyFvars, Input.toCore, scrut.toCore_substTyFvars hs subst,
        completeBranches_substTyFvars branches hbs subst, Expr.substTyFvars_match]
      rfl
  | letRec anns bindings body =>
      simp only [Input.toCore, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at h
      obtain ⟨anns', ha, bindings', hbs, body', hb, rfl⟩ := h
      simp only [Input.substTyFvars, Input.toCore, completeAnns_substTyFvars anns ha subst,
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

theorem completeBranches_substTyFvars (branches : List (MatchPattern × Input))
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

theorem completeBindings_substTyFvars (bindings : List Input) {cores : List Expr}
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
theorem Template.substTyFvars_zip_openTyVarsFrom (template : Template) {Ys Xs : List Nat}
    (hlen : Ys.length = Xs.length) (hnd : Ys.Nodup) (hfresh : ∀ y ∈ Ys, y ∉ template.rigidVars)
    (hdisj : ∀ y ∈ Ys, y ∉ Xs) (d : Nat) :
    (template.openTyVarsFrom d Ys).substTyFvars (Ys.zip (Xs.map Ty.fvar)) =
      template.openTyVarsFrom d Xs := by
  cases template with
  | fixed ty => exact congrArg Template.fixed (Ty.substFvars_zip_openVarsFrom hlen hnd hfresh hdisj)
  | hole => rfl
  | arrow a b =>
      rw [Template.openTyVarsFrom, Template.substTyFvars, Template.openTyVarsFrom,
        a.substTyFvars_zip_openTyVarsFrom hlen hnd
          (fun y hy hv => hfresh y hy (List.mem_append_left _ hv)) hdisj d,
        b.substTyFvars_zip_openTyVarsFrom hlen hnd
          (fun y hy hv => hfresh y hy (List.mem_append_right _ hv)) hdisj d]
  | custom name args =>
      exact congrArg (Template.custom name) (substTemplateList_zip_open args hlen hnd hfresh hdisj d)
theorem substTemplateList_zip_open (templates : List Template) {Ys Xs : List Nat}
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

theorem LetAnn.substTyFvars_zip_openTyVarsFrom (ann : LetAnn) {Ys Xs : List Nat}
    (hlen : Ys.length = Xs.length) (hnd : Ys.Nodup) (hfresh : ∀ y ∈ Ys, y ∉ ann.rigidVars)
    (hdisj : ∀ y ∈ Ys, y ∉ Xs) (d : Nat) :
    (ann.openTyVarsFrom d Ys).substTyFvars (Ys.zip (Xs.map Ty.fvar)) = ann.openTyVarsFrom d Xs := by
  cases ann with
  | absent => rfl
  | complete scheme =>
      simp only [LetAnn.openTyVarsFrom, LetAnn.substTyFvars,
        Ty.substFvars_zip_openVarsFrom hlen hnd hfresh hdisj]
  | template t => exact congrArg LetAnn.template (t.substTyFvars_zip_openTyVarsFrom hlen hnd hfresh hdisj d)
  | partialForall n t =>
      exact congrArg (LetAnn.partialForall n)
        (t.substTyFvars_zip_openTyVarsFrom hlen hnd hfresh hdisj (d + n))

mutual
/-- Replace an opening's fresh names throughout partial input syntax. As in
Core, the names must be absent from authored leaves and from the replacement
block, because type substitution is sequential. -/
theorem Input.substTyFvars_zip_openTyVarsFrom (input : Input) {Ys Xs : List Nat}
    (hlen : Ys.length = Xs.length) (hnd : Ys.Nodup) (hfresh : ∀ y ∈ Ys, y ∉ input.rigidVars)
    (hdisj : ∀ y ∈ Ys, y ∉ Xs) (d : Nat) :
    (input.openTyVarsFrom d Ys).substTyFvars (Ys.zip (Xs.map Ty.fvar)) = input.openTyVarsFrom d Xs := by
  cases input with
  | primLit | primBinOp | var | ctor => rfl
  | lambda ann body =>
      simp only [Input.openTyVarsFrom, Input.substTyFvars,
        body.substTyFvars_zip_openTyVarsFrom hlen hnd
          (fun y hy hv => hfresh y hy (List.mem_append_right _ hv)) hdisj d]
      congr 1
      cases ann with
      | none => rfl
      | some template => exact congrArg some (template.substTyFvars_zip_openTyVarsFrom hlen hnd
          (fun y hy hv => hfresh y hy (List.mem_append_left _ hv)) hdisj d)
  | app f a =>
      simp only [Input.openTyVarsFrom, Input.substTyFvars,
        f.substTyFvars_zip_openTyVarsFrom hlen hnd
          (fun y hy hv => hfresh y hy (List.mem_append_left _ hv)) hdisj d,
        a.substTyFvars_zip_openTyVarsFrom hlen hnd
          (fun y hy hv => hfresh y hy (List.mem_append_right _ hv)) hdisj d]
  | letIn ann rhs body =>
      simp only [Input.openTyVarsFrom, Input.substTyFvars,
        ann.substTyFvars_zip_openTyVarsFrom hlen hnd
          (fun y hy hv => hfresh y hy (List.mem_append_left _ (List.mem_append_left _ hv))) hdisj d,
        rhs.substTyFvars_zip_openTyVarsFrom hlen hnd
          (fun y hy hv => hfresh y hy (List.mem_append_left _ (List.mem_append_right _ hv))) hdisj (d + ann.paramCount),
        body.substTyFvars_zip_openTyVarsFrom hlen hnd
          (fun y hy hv => hfresh y hy (List.mem_append_right _ hv)) hdisj d]
  | match_ scrut branches =>
      simp only [Input.openTyVarsFrom, Input.substTyFvars,
        scrut.substTyFvars_zip_openTyVarsFrom hlen hnd
          (fun y hy hv => hfresh y hy (List.mem_append_left _ hv)) hdisj d,
        substInputBranches_zip_open branches hlen hnd
          (fun y hy hv => hfresh y hy (List.mem_append_right _ hv)) hdisj d]
  | letRec anns bindings body =>
      simp only [Input.openTyVarsFrom, Input.substTyFvars,
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

theorem substInputBranches_zip_open (branches : List (MatchPattern × Input)) {Ys Xs : List Nat}
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

theorem substInputBindings_zip_open (bindings : List Input) (anns : List LetAnn) {Ys Xs : List Nat}
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
theorem Input.substTyFvars_zip_openTyVars (input : Input) {Ys Xs : List Nat}
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
theorem Template.substTyFvars_openTyVarsFrom (template : Template) {subst : List (Nat × Ty)} {Xs : List Nat}
    (hlc : ∀ pair ∈ subst, pair.2.IsLC) (hfresh : ∀ pair ∈ subst, pair.1 ∉ Xs) (d : Nat) :
    (template.openTyVarsFrom d Xs).substTyFvars subst = (template.substTyFvars subst).openTyVarsFrom d Xs := by
  cases template with
  | fixed ty => exact congrArg Template.fixed (Ty.substFvars_openVarsFrom hlc hfresh ty d)
  | hole => rfl
  | arrow a b => simp only [Template.openTyVarsFrom, Template.substTyFvars,
      a.substTyFvars_openTyVarsFrom hlc hfresh d, b.substTyFvars_openTyVarsFrom hlc hfresh d]
  | custom name args =>
      exact congrArg (Template.custom name) (substTemplateList_openTemplateList args hlc hfresh d)
theorem substTemplateList_openTemplateList (templates : List Template) {subst : List (Nat × Ty)} {Xs : List Nat}
    (hlc : ∀ pair ∈ subst, pair.2.IsLC) (hfresh : ∀ pair ∈ subst, pair.1 ∉ Xs) (d : Nat) :
    substTemplateList subst (openTemplateList d Xs templates) = openTemplateList d Xs (substTemplateList subst templates) := by
  cases templates with
  | nil => rfl
  | cons t ts => simp only [openTemplateList, substTemplateList,
      t.substTyFvars_openTyVarsFrom hlc hfresh d, substTemplateList_openTemplateList ts hlc hfresh d]
end

theorem LetAnn.substTyFvars_openTyVarsFrom (ann : LetAnn) {subst : List (Nat × Ty)} {Xs : List Nat}
    (hlc : ∀ pair ∈ subst, pair.2.IsLC) (hfresh : ∀ pair ∈ subst, pair.1 ∉ Xs) (d : Nat) :
    (ann.openTyVarsFrom d Xs).substTyFvars subst = (ann.substTyFvars subst).openTyVarsFrom d Xs := by
  cases ann with
  | absent => rfl
  | complete scheme => simp only [LetAnn.openTyVarsFrom, LetAnn.substTyFvars,
      Ty.substFvars_openVarsFrom hlc hfresh]
  | template t => exact congrArg LetAnn.template (t.substTyFvars_openTyVarsFrom hlc hfresh d)
  | partialForall n t =>
      exact congrArg (LetAnn.partialForall n) (t.substTyFvars_openTyVarsFrom hlc hfresh (d + n))

mutual
/-- Source substitution commutes with opening through nested written signature
binders. LC ranges need not avoid the opened names. -/
theorem Input.substTyFvars_openTyVarsFrom (input : Input) {subst : List (Nat × Ty)} {Xs : List Nat}
    (hlc : ∀ pair ∈ subst, pair.2.IsLC) (hfresh : ∀ pair ∈ subst, pair.1 ∉ Xs) (d : Nat) :
    (input.openTyVarsFrom d Xs).substTyFvars subst = (input.substTyFvars subst).openTyVarsFrom d Xs := by
  cases input with
  | primLit | primBinOp | var | ctor => rfl
  | lambda ann body =>
      simp only [Input.openTyVarsFrom, Input.substTyFvars,
        body.substTyFvars_openTyVarsFrom hlc hfresh d]
      congr 1
      cases ann with
      | none => rfl
      | some template => exact congrArg some (template.substTyFvars_openTyVarsFrom hlc hfresh d)
  | app f a => simp only [Input.openTyVarsFrom, Input.substTyFvars,
      f.substTyFvars_openTyVarsFrom hlc hfresh d, a.substTyFvars_openTyVarsFrom hlc hfresh d]
  | letIn ann rhs body => simp only [Input.openTyVarsFrom, Input.substTyFvars,
      LetAnn.paramCount_substTyFvars, ann.substTyFvars_openTyVarsFrom hlc hfresh d,
      rhs.substTyFvars_openTyVarsFrom hlc hfresh (d + ann.paramCount),
      body.substTyFvars_openTyVarsFrom hlc hfresh d]
  | match_ scrut branches => simp only [Input.openTyVarsFrom, Input.substTyFvars,
      scrut.substTyFvars_openTyVarsFrom hlc hfresh d,
      substInputBranches_openInputBranches branches hlc hfresh d]
  | letRec anns bindings body =>
      simp only [Input.openTyVarsFrom, Input.substTyFvars,
        body.substTyFvars_openTyVarsFrom hlc hfresh d,
        substInputBindings_openInputBindings bindings anns hlc hfresh d, List.map_map]
      congr 1
      apply List.map_congr_left
      intro ann _
      exact ann.substTyFvars_openTyVarsFrom hlc hfresh d
termination_by sizeOf input

theorem substInputBranches_openInputBranches (branches : List (MatchPattern × Input)) {subst : List (Nat × Ty)} {Xs : List Nat}
    (hlc : ∀ pair ∈ subst, pair.2.IsLC) (hfresh : ∀ pair ∈ subst, pair.1 ∉ Xs) (d : Nat) :
    substInputBranches subst (openInputBranches d Xs branches) = openInputBranches d Xs (substInputBranches subst branches) := by
  cases branches with
  | nil => rfl
  | cons pair rest =>
      rcases pair with ⟨pat, body⟩
      simp only [openInputBranches, substInputBranches, body.substTyFvars_openTyVarsFrom hlc hfresh d,
        substInputBranches_openInputBranches rest hlc hfresh d]
termination_by sizeOf branches

theorem substInputBindings_openInputBindings (bindings : List Input) (anns : List LetAnn)
    {subst : List (Nat × Ty)} {Xs : List Nat}
    (hlc : ∀ pair ∈ subst, pair.2.IsLC) (hfresh : ∀ pair ∈ subst, pair.1 ∉ Xs) (d : Nat) :
    substInputBindings subst (openInputBindings d Xs anns bindings) =
      openInputBindings d Xs (anns.map (LetAnn.substTyFvars subst)) (substInputBindings subst bindings) := by
  cases bindings with
  | nil => rfl
  | cons body rest =>
      cases anns with
      | nil => simp only [openInputBindings, substInputBindings, List.map_nil,
          body.substTyFvars_openTyVarsFrom hlc hfresh d,
          substInputBindings_openInputBindings rest [] hlc hfresh d]
      | cons ann anns => simp only [openInputBindings, substInputBindings, List.map_cons,
          LetAnn.paramCount_substTyFvars, body.substTyFvars_openTyVarsFrom hlc hfresh (d + ann.paramCount),
          substInputBindings_openInputBindings rest anns hlc hfresh d]
termination_by sizeOf bindings
end

theorem Input.substTyFvars_openTyVars (input : Input) {subst : List (Nat × Ty)} {Xs : List Nat}
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
theorem Template.substTyFvars_eq_self_of_fixes (template : Template) {subst : List (Nat × Ty)}
    (h : ∀ v ∈ template.rigidVars, (Ty.fvar v).substFvars subst = .fvar v) :
    template.substTyFvars subst = template := by
  cases template with
  | fixed ty => exact congrArg Template.fixed (ty_substFvars_eq_self_of_fixes h)
  | hole => rfl
  | arrow a b => simp only [Template.substTyFvars,
      a.substTyFvars_eq_self_of_fixes (fun v hv => h v (List.mem_append_left _ hv)),
      b.substTyFvars_eq_self_of_fixes (fun v hv => h v (List.mem_append_right _ hv))]
  | custom name args =>
      exact congrArg (Template.custom name) (substTemplateList_eq_self_of_fixes args h)
theorem substTemplateList_eq_self_of_fixes (templates : List Template) {subst : List (Nat × Ty)}
    (h : ∀ v ∈ rigidVarsList templates, (Ty.fvar v).substFvars subst = .fvar v) :
    substTemplateList subst templates = templates := by
  cases templates with
  | nil => rfl
  | cons t ts => simp only [substTemplateList,
      t.substTyFvars_eq_self_of_fixes (fun v hv => h v (List.mem_append_left _ hv)),
      substTemplateList_eq_self_of_fixes ts (fun v hv => h v (List.mem_append_right _ hv))]
end

theorem LetAnn.substTyFvars_eq_self_of_fixes (ann : LetAnn) {subst : List (Nat × Ty)}
    (h : ∀ v ∈ ann.rigidVars, (Ty.fvar v).substFvars subst = .fvar v) : ann.substTyFvars subst = ann := by
  cases ann with
  | absent => rfl
  | complete scheme => simp only [LetAnn.substTyFvars, ty_substFvars_eq_self_of_fixes h]
  | template t => exact congrArg LetAnn.template (t.substTyFvars_eq_self_of_fixes h)
  | partialForall n t => exact congrArg (LetAnn.partialForall n) (t.substTyFvars_eq_self_of_fixes h)

mutual
/-- Fixing every authored free type variable leaves the complete input syntax
unchanged, including anonymous holes and written signature modes. -/
theorem Input.substTyFvars_eq_self_of_fixes (input : Input) {subst : List (Nat × Ty)}
    (h : ∀ v ∈ input.rigidVars, (Ty.fvar v).substFvars subst = .fvar v) : input.substTyFvars subst = input := by
  cases input with
  | primLit | primBinOp | var | ctor => rfl
  | lambda ann body =>
      simp only [Input.substTyFvars,
        body.substTyFvars_eq_self_of_fixes (fun v hv => h v (List.mem_append_right _ hv))]
      congr 1
      cases ann with
      | none => rfl
      | some template =>
          exact congrArg some (template.substTyFvars_eq_self_of_fixes (fun v hv => h v (List.mem_append_left _ hv)))
  | app f a => simp only [Input.substTyFvars,
      f.substTyFvars_eq_self_of_fixes (fun v hv => h v (List.mem_append_left _ hv)),
      a.substTyFvars_eq_self_of_fixes (fun v hv => h v (List.mem_append_right _ hv))]
  | letIn ann rhs body => simp only [Input.substTyFvars,
      ann.substTyFvars_eq_self_of_fixes (fun v hv => h v (List.mem_append_left _ (List.mem_append_left _ hv))),
      rhs.substTyFvars_eq_self_of_fixes (fun v hv => h v (List.mem_append_left _ (List.mem_append_right _ hv))),
      body.substTyFvars_eq_self_of_fixes (fun v hv => h v (List.mem_append_right _ hv))]
  | match_ scrut branches => simp only [Input.substTyFvars,
      scrut.substTyFvars_eq_self_of_fixes (fun v hv => h v (List.mem_append_left _ hv)),
      substInputBranches_eq_self_of_fixes branches (fun v hv => h v (List.mem_append_right _ hv))]
  | letRec anns bindings body =>
      simp only [Input.substTyFvars,
        body.substTyFvars_eq_self_of_fixes (fun v hv => h v (List.mem_append_right _ hv)),
        substInputBindings_eq_self_of_fixes bindings (fun v hv => h v (List.mem_append_left _ (List.mem_append_right _ hv)))]
      congr 1
      conv_rhs => rw [← List.map_id anns]
      apply List.map_congr_left
      intro ann hann
      exact ann.substTyFvars_eq_self_of_fixes (fun v hv => h v (List.mem_append_left _
        (List.mem_append_left _ (List.mem_flatMap.mpr ⟨ann, hann, hv⟩))))
termination_by sizeOf input

theorem substInputBranches_eq_self_of_fixes (branches : List (MatchPattern × Input)) {subst : List (Nat × Ty)}
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

theorem substInputBindings_eq_self_of_fixes (bindings : List Input) {subst : List (Nat × Ty)}
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
theorem Template.substTyFvars_append (template : Template) (first second : List (Nat × Ty)) :
    template.substTyFvars (first ++ second) = (template.substTyFvars first).substTyFvars second := by
  cases template with
  | fixed ty => exact congrArg Template.fixed (ty_substFvars_append ty first second)
  | hole => rfl
  | arrow a b => simp only [Template.substTyFvars,
      a.substTyFvars_append first second, b.substTyFvars_append first second]
  | custom name args => exact congrArg (Template.custom name) (substTemplateList_append args first second)
theorem substTemplateList_append (templates : List Template) (first second : List (Nat × Ty)) :
    substTemplateList (first ++ second) templates = substTemplateList second (substTemplateList first templates) := by
  cases templates with
  | nil => rfl
  | cons t ts => simp only [substTemplateList, t.substTyFvars_append first second,
      substTemplateList_append ts first second]
end

theorem LetAnn.substTyFvars_append (ann : LetAnn) (first second : List (Nat × Ty)) :
    ann.substTyFvars (first ++ second) = (ann.substTyFvars first).substTyFvars second := by
  cases ann with
  | absent => rfl
  | complete scheme => simp only [LetAnn.substTyFvars, ty_substFvars_append]
  | template t => exact congrArg LetAnn.template (t.substTyFvars_append first second)
  | partialForall n t => exact congrArg (LetAnn.partialForall n) (t.substTyFvars_append first second)

mutual
/-- Source type substitutions compose in the same left-to-right order as Core. -/
theorem Input.substTyFvars_append (input : Input) (first second : List (Nat × Ty)) :
    input.substTyFvars (first ++ second) = (input.substTyFvars first).substTyFvars second := by
  cases input with
  | primLit | primBinOp | var | ctor => rfl
  | lambda ann body =>
      simp only [Input.substTyFvars, body.substTyFvars_append first second, Option.map_map]
      congr 1
      cases ann with
      | none => rfl
      | some t => exact congrArg some (t.substTyFvars_append first second)
  | app f a => simp only [Input.substTyFvars, f.substTyFvars_append first second, a.substTyFvars_append first second]
  | letIn ann rhs body => simp only [Input.substTyFvars, ann.substTyFvars_append first second,
      rhs.substTyFvars_append first second, body.substTyFvars_append first second]
  | match_ scrut branches => simp only [Input.substTyFvars, scrut.substTyFvars_append first second,
      substInputBranches_append branches first second]
  | letRec anns bindings body =>
      simp only [Input.substTyFvars, body.substTyFvars_append first second,
        substInputBindings_append bindings first second, List.map_map]
      congr 1
      exact List.map_congr_left (fun ann _ => ann.substTyFvars_append first second)
termination_by sizeOf input

theorem substInputBranches_append (branches : List (MatchPattern × Input)) (first second : List (Nat × Ty)) :
    substInputBranches (first ++ second) branches = substInputBranches second (substInputBranches first branches) := by
  cases branches with
  | nil => rfl
  | cons pair rest =>
      rcases pair with ⟨pat, body⟩
      simp only [substInputBranches, body.substTyFvars_append first second, substInputBranches_append rest first second]
termination_by sizeOf branches

theorem substInputBindings_append (bindings : List Input) (first second : List (Nat × Ty)) :
    substInputBindings (first ++ second) bindings = substInputBindings second (substInputBindings first bindings) := by
  cases bindings with
  | nil => rfl
  | cons body rest => simp only [substInputBindings, body.substTyFvars_append first second,
      substInputBindings_append rest first second]
termination_by sizeOf bindings
end

private theorem ty_substFvars_congr {subst other : List (Nat × Ty)} {ty : Ty}
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
theorem Template.substTyFvars_congr (template : Template) {subst other : List (Nat × Ty)}
    (h : ∀ v ∈ template.rigidVars, (Ty.fvar v).substFvars subst = (Ty.fvar v).substFvars other) :
    template.substTyFvars subst = template.substTyFvars other := by
  cases template with
  | fixed ty => exact congrArg Template.fixed (ty_substFvars_congr h)
  | hole => rfl
  | arrow a b => simp only [Template.substTyFvars,
      a.substTyFvars_congr (fun v hv => h v (List.mem_append_left _ hv)),
      b.substTyFvars_congr (fun v hv => h v (List.mem_append_right _ hv))]
  | custom name args =>
      exact congrArg (Template.custom name) (substTemplateList_congr args h)
theorem substTemplateList_congr (templates : List Template) {subst other : List (Nat × Ty)}
    (h : ∀ v ∈ rigidVarsList templates, (Ty.fvar v).substFvars subst = (Ty.fvar v).substFvars other) :
    substTemplateList subst templates = substTemplateList other templates := by
  cases templates with
  | nil => rfl
  | cons t ts => simp only [substTemplateList,
      t.substTyFvars_congr (fun v hv => h v (List.mem_append_left _ hv)),
      substTemplateList_congr ts (fun v hv => h v (List.mem_append_right _ hv))]
end

theorem LetAnn.substTyFvars_congr (ann : LetAnn) {subst other : List (Nat × Ty)}
    (h : ∀ v ∈ ann.rigidVars, (Ty.fvar v).substFvars subst = (Ty.fvar v).substFvars other) : ann.substTyFvars subst = ann.substTyFvars other := by
  cases ann with
  | absent => rfl
  | complete scheme => simp only [LetAnn.substTyFvars, ty_substFvars_congr h]
  | template t => exact congrArg LetAnn.template (t.substTyFvars_congr h)
  | partialForall n t => exact congrArg (LetAnn.partialForall n) (t.substTyFvars_congr h)

mutual
/-- Substitutions agreeing on all authored free type variables produce the
same input syntax, including beneath written signature binders. -/
theorem Input.substTyFvars_congr (input : Input) {subst other : List (Nat × Ty)}
    (h : ∀ v ∈ input.rigidVars, (Ty.fvar v).substFvars subst = (Ty.fvar v).substFvars other) : input.substTyFvars subst = input.substTyFvars other := by
  cases input with
  | primLit | primBinOp | var | ctor => rfl
  | lambda ann body =>
      simp only [Input.substTyFvars,
        body.substTyFvars_congr (fun v hv => h v (List.mem_append_right _ hv))]
      congr 1
      cases ann with
      | none => rfl
      | some template =>
          exact congrArg some (template.substTyFvars_congr (fun v hv => h v (List.mem_append_left _ hv)))
  | app f a => simp only [Input.substTyFvars,
      f.substTyFvars_congr (fun v hv => h v (List.mem_append_left _ hv)),
      a.substTyFvars_congr (fun v hv => h v (List.mem_append_right _ hv))]
  | letIn ann rhs body => simp only [Input.substTyFvars,
      ann.substTyFvars_congr (fun v hv => h v (List.mem_append_left _ (List.mem_append_left _ hv))),
      rhs.substTyFvars_congr (fun v hv => h v (List.mem_append_left _ (List.mem_append_right _ hv))),
      body.substTyFvars_congr (fun v hv => h v (List.mem_append_right _ hv))]
  | match_ scrut branches => simp only [Input.substTyFvars,
      scrut.substTyFvars_congr (fun v hv => h v (List.mem_append_left _ hv)),
      substInputBranches_congr branches (fun v hv => h v (List.mem_append_right _ hv))]
  | letRec anns bindings body =>
      simp only [Input.substTyFvars,
        body.substTyFvars_congr (fun v hv => h v (List.mem_append_right _ hv)),
        substInputBindings_congr bindings (fun v hv => h v (List.mem_append_left _ (List.mem_append_right _ hv)))]
      congr 1
      apply List.map_congr_left
      intro ann hann
      exact ann.substTyFvars_congr (fun v hv => h v (List.mem_append_left _
        (List.mem_append_left _ (List.mem_flatMap.mpr ⟨ann, hann, hv⟩))))
termination_by sizeOf input

theorem substInputBranches_congr (branches : List (MatchPattern × Input)) {subst other : List (Nat × Ty)}
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

theorem substInputBindings_congr (bindings : List Input) {subst other : List (Nat × Ty)}
    (h : ∀ v ∈ rigidBindingVars bindings, (Ty.fvar v).substFvars subst = (Ty.fvar v).substFvars other) :
    substInputBindings subst bindings = substInputBindings other bindings := by
  cases bindings with
  | nil => rfl
  | cons body rest => simp only [substInputBindings,
      body.substTyFvars_congr (fun v hv => h v (List.mem_append_left _ hv)),
      substInputBindings_congr rest (fun v hv => h v (List.mem_append_right _ hv))]
termination_by sizeOf bindings
end


end Elaboration
