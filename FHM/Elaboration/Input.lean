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

end Elaboration
