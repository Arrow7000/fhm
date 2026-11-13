import EPL.Core

namespace EPL

def PrimLit.ty : PrimLit → Ty
  | .unit => .prim .unit
  | .int _ => .prim .int

def PrimOp.ty : PrimOp → Ty
  | .intAdd => .arrow (.prim .int) (.arrow (.prim .int) (.prim .int))

def Ty.apps (head : Ty) (args : List Ty) : Ty :=
  args.foldl .app head

def Ty.arrows (domains : List Ty) (codomain : Ty) : Ty :=
  domains.foldr .arrow codomain

/-- Declared type `type` applied to its own parameters. -/
def DataDecl.selfTy (decl : DataDecl) (type : Nat) : Ty :=
  Ty.apps (.con type) ((List.range decl.paramCount).map .bvar)

/-- `forall params. field_1 -> ... -> field_n -> T params`. -/
def DataDecl.ctorScheme (decl : DataDecl) (type : Nat) (fields : List Ty) :
    PolyTy :=
  ⟨decl.paramCount, Ty.arrows fields (decl.selfTy type)⟩

/-- A branch first receives `()`, so that call-by-value evaluation does not
run the branches a match does not take, and then the constructor's fields. -/
def branchTy (fields : List Ty) (result : Ty) : Ty :=
  .arrow (.prim .unit) (Ty.arrows fields result)

/-- `forall params r. T params -> branch_1 -> ... -> branch_k -> r`, with the
result type `r` bound last. -/
def DataDecl.elimScheme (decl : DataDecl) (type : Nat) : PolyTy :=
  let result := Ty.bvar decl.paramCount
  ⟨decl.paramCount + 1,
    .arrow (decl.selfTy type)
      (Ty.arrows (decl.ctors.map fun fields => branchTy fields result) result)⟩

/-- The scheme of a constant, if the signature declares it with the recorded
arity. -/
def Signature.schemeOf (sig : Signature) : DataConst → Option PolyTy
  | .ctor type ctor arity => do
      let decl ← sig[type]?
      let fields ← decl.ctors[ctor]?
      if fields.length = arity then some (decl.ctorScheme type fields) else none
  | .elim type ctorCount => do
      let decl ← sig[type]?
      if decl.ctors.length = ctorCount then some (decl.elimScheme type) else none

/-- Declarative typing for the explicitly polymorphic source language.

`rigidCount` is the number of rigid levels currently in scope. It makes an
explicit scheme's generic opening deterministic and prevents rigid variables
from being confused with inference metavariables. -/
inductive Typing (sig : Signature) : Nat → Ctx → Source → Ty → Prop
  | primLit :
      Typing sig rigidCount ctx (.primLit literal) literal.ty

  | primOp :
      Typing sig rigidCount ctx (.primOp op) op.ty

  | var :
      ctx[index]? = some scheme →
      scheme.WF rigidCount →
      args.length = scheme.paramCount →
      (∀ arg ∈ args, arg.WF rigidCount 0) →
      Typing sig rigidCount ctx (.var index) (scheme.openWith args)

  | lambda :
      paramTy.WF rigidCount 0 →
      ParamAnn.Matches ann paramTy →
      Typing sig rigidCount (PolyTy.mono paramTy :: ctx) body bodyTy →
      Typing sig rigidCount ctx (.lambda ann body) (.arrow paramTy bodyTy)

  | app :
      Typing sig rigidCount ctx function (.arrow argumentTy resultTy) →
      Typing sig rigidCount ctx argument argumentTy →
      Typing sig rigidCount ctx (.app function argument) resultTy

  | letMono :
      rhsTy.WF rigidCount 0 →
      Typing sig rigidCount ctx rhs rhsTy →
      Typing sig rigidCount (PolyTy.mono rhsTy :: ctx) body bodyTy →
      Typing sig rigidCount ctx (.letIn none rhs body) bodyTy

  | letPoly :
      SchemeTemplateMatches written scheme →
      scheme.WF rigidCount →
      ctx.WF rigidCount →
      rhs.TypeScoped rigidCount scheme.paramCount →
      Typing sig (rigidCount + scheme.paramCount) ctx
        (rhs.openRigids rigidCount scheme.paramCount)
        (scheme.openRigids rigidCount) →
      Typing sig rigidCount (scheme :: ctx) body bodyTy →
      Typing sig rigidCount ctx (.letIn (some written) rhs body) bodyTy

  | fix :
      selfTy.WF rigidCount 0 →
      ann.Matches selfTy →
      Typing sig rigidCount (PolyTy.mono selfTy :: ctx) body selfTy →
      Typing sig rigidCount ctx (.fix ann body) selfTy

  | const :
      sig.schemeOf c = some scheme →
      scheme.WF 0 →
      args.length = scheme.paramCount →
      (∀ arg ∈ args, arg.WF rigidCount 0) →
      Typing sig rigidCount ctx (.const c) (scheme.openWith args)

/-- Declarative typing that also records the implicit types it chose: every
lambda's parameter type, every `fix`'s self type, and every explicit let's
completed scheme. Together these determine every annotation hole and every
omitted parameter type. Scheme instantiations are deliberately not recorded:
an unknown introduced only to instantiate a scheme need not be determined.

An explicit let's right-hand side is elaborated at the scheme's rigid block,
so its recorded types may mention those rigid levels. A partial signature is
completed from its definition and context, never from later uses: the
completed scheme must be the only one for which the right-hand side checks.
(Later uses could not consider completions mentioning the scheme's own
binders. A signature without binders has no such completions, so its holes
are treated like any other implicit type.)
So, unlike `Typing`, not every typable program elaborates (e.g.
`let f : forall a. _ -> a -> a = fun z y => y in f true true`, where `_` could
be `a` or `Bool`). -/
inductive Elaborates (sig : Signature) : Nat → Ctx → Source → Expr Ty → Ty → Prop
  | primLit :
      Elaborates sig rigidCount ctx (.primLit literal) (.primLit literal) literal.ty

  | primOp :
      Elaborates sig rigidCount ctx (.primOp op) (.primOp op) op.ty

  | var :
      ctx[index]? = some scheme →
      scheme.WF rigidCount →
      args.length = scheme.paramCount →
      (∀ arg ∈ args, arg.WF rigidCount 0) →
      Elaborates sig rigidCount ctx (.var index) (.var index) (scheme.openWith args)

  | lambda :
      paramTy.WF rigidCount 0 →
      ParamAnn.Matches ann paramTy →
      Elaborates sig rigidCount (PolyTy.mono paramTy :: ctx) body bodyElab bodyTy →
      Elaborates sig rigidCount ctx (.lambda ann body)
        (.lambda (some paramTy) bodyElab) (.arrow paramTy bodyTy)

  | app :
      Elaborates sig rigidCount ctx function functionElab
        (.arrow argumentTy resultTy) →
      Elaborates sig rigidCount ctx argument argumentElab argumentTy →
      Elaborates sig rigidCount ctx (.app function argument)
        (.app functionElab argumentElab) resultTy

  | letMono :
      rhsTy.WF rigidCount 0 →
      Elaborates sig rigidCount ctx rhs rhsElab rhsTy →
      Elaborates sig rigidCount (PolyTy.mono rhsTy :: ctx) body bodyElab bodyTy →
      Elaborates sig rigidCount ctx (.letIn none rhs body)
        (.letIn none rhsElab bodyElab) bodyTy

  | letPoly :
      SchemeTemplateMatches written scheme →
      scheme.WF rigidCount →
      ctx.WF rigidCount →
      rhs.TypeScoped rigidCount scheme.paramCount →
      Elaborates sig (rigidCount + scheme.paramCount) ctx
        (rhs.openRigids rigidCount scheme.paramCount) rhsElab
        (scheme.openRigids rigidCount) →
      -- A polymorphic signature's holes are determined by the definition
      -- and its context alone: no other completion also checks. (A
      -- signature without binders is an ordinary partial annotation, whose
      -- holes later uses may determine.)
      (scheme.paramCount = 0 ∨
        ∀ other : PolyTy, SchemeTemplateMatches written other →
          other.WF rigidCount →
          Typing sig (rigidCount + other.paramCount) ctx
            (rhs.openRigids rigidCount other.paramCount)
            (other.openRigids rigidCount) →
          other = scheme) →
      Elaborates sig rigidCount (scheme :: ctx) body bodyElab bodyTy →
      Elaborates sig rigidCount ctx (.letIn (some written) rhs body)
        (.letIn (some scheme) rhsElab bodyElab) bodyTy

  | fix :
      selfTy.WF rigidCount 0 →
      ann.Matches selfTy →
      Elaborates sig rigidCount (PolyTy.mono selfTy :: ctx) body bodyElab selfTy →
      Elaborates sig rigidCount ctx (.fix ann body) (.fix selfTy bodyElab) selfTy

  | const :
      sig.schemeOf c = some scheme →
      scheme.WF 0 →
      args.length = scheme.paramCount →
      (∀ arg ∈ args, arg.WF rigidCount 0) →
      Elaborates sig rigidCount ctx (.const c) (.const c) (scheme.openWith args)

end EPL
