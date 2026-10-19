import FHM.Completeness

/-! Anonymous annotation input is separate from ordinary Core. A hole is syntax,
not a free type variable: each visit allocates a fresh flexible variable. The
completed output of elaboration remains an ordinary `Expr`.

This module starts with ordinary lambda and let generalisation. Partial explicit
quantifiers and partial recursive contracts are deliberately distinguished in
the syntax so an unsupported case cannot accidentally become a complete Core
signature (and hence a polymorphic-recursion dependency cut).
-/

namespace Anonymous

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

/-- A partial ordinary signature constrains the inferred monotype before that
monotype is generalised. It is not an existential complete Core signature. -/
def LetAnn.FitsMono : LetAnn → Ty → Prop
  | .absent, _ => True
  | .template t, ty => t.Fits ty
  | _, _ => False

/-- Independent input typing for the first fragment. The let rule generalises
the RHS cofinally, and partial annotations constrain that very monotype. There
is no recursive rule: in particular, a partial annotation cannot acquire
polymorphic recursive uses through an arbitrary completed output signature.

Complete scoped signatures will use their existing checking rule when the
conservative Core embedding is connected; this fragment does not reinterpret
complete annotations as partial annotations.
-/
inductive Typing : Ctx → Input → Ty → Prop
  | primLit : TypeOfHM ctx (.primLit p) ty → Typing ctx (.primLit p) ty
  | primBinOp : TypeOfHM ctx (.primBinOp op) ty → Typing ctx (.primBinOp op) ty
  | lambda :
      paramTy.IsLC →
      (∀ template, ann = some template → template.Fits paramTy) →
      Typing { ctx with env := PolyTy.mkTrivial paramTy :: ctx.env } body bodyTy →
      Typing ctx (.lambda ann body) (.arrow paramTy bodyTy)
  | app : Typing ctx f (.arrow argTy retTy) → Typing ctx arg argTy →
      Typing ctx (.app f arg) retTy
  | letIn {M : PolyTy} {L : List Nat} :
      M.WF →
      (∀ Xs, FreshNames L M.paramCount Xs → ann.FitsMono (M.openVars Xs)) →
      (∀ Xs, FreshNames L M.paramCount Xs → Typing ctx rhs (M.openVars Xs)) →
      Typing { ctx with env := M :: ctx.env } body bodyTy →
      Typing ctx (.letIn ann rhs body) bodyTy
  | var : ctx.env[index]? = some scheme →
      (∀ arg ∈ args, arg.IsLC) → scheme.InstantiatesTo args ty →
      Typing ctx (.var index) ty
  | ctor : LookupList.get? ctx.ctors name = some ctor →
      (∀ arg ∈ args, arg.IsLC) → ctor.toTy.InstantiatesTo args ty →
      Typing ctx (.ctor name) ty

/-- The input specification has the ordinary HM runtime meaning independently
of elaboration. Annotation matching restricts this meaning; it never grants a
new runtime typing rule. -/
theorem Typing.erase (h : Typing ctx input ty) : TypeOfHM ctx input.erase ty := by
  induction h with
  | primLit h => exact h
  | primBinOp h => exact h
  | lambda hlc _ _ ih =>
      exact .lambda hlc (fun _ h => by cases h) rfl ih
  | app _ _ ihf ihx => exact .app ihf ihx
  | letIn hwf _ _ _ ihrhs ihbody =>
      exact .letIn hwf (fun _ h => by cases h) ihrhs rfl ihbody
  | var hlook hlc hinst => exact .var hlook hlc hinst
  | ctor hlook hlc hinst => exact .ctor hlook hlc hinst

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

end Anonymous
