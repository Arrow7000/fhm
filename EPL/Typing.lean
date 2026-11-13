import EPL.Core

namespace EPL

def PrimLit.ty : PrimLit → Ty
  | .unit => .prim .unit
  | .int _ => .prim .int
  | .bool _ => .prim .bool

def PrimOp.ty : PrimOp → Ty
  | .intAdd => .arrow (.prim .int) (.arrow (.prim .int) (.prim .int))

/-- Declarative typing for the explicitly polymorphic source language.

`rigidCount` is the number of rigid levels currently in scope. It makes an
explicit scheme's generic opening deterministic and prevents rigid variables
from being confused with inference metavariables. -/
inductive Typing : Nat → Ctx → Source → Ty → Prop
  | primLit :
      Typing rigidCount ctx (.primLit literal) literal.ty

  | primOp :
      Typing rigidCount ctx (.primOp op) op.ty

  | var :
      ctx[index]? = some scheme →
      scheme.WF rigidCount →
      args.length = scheme.paramCount →
      (∀ arg ∈ args, arg.WF rigidCount 0) →
      Typing rigidCount ctx (.var index) (scheme.openWith args)

  | lambda :
      paramTy.WF rigidCount 0 →
      ParamAnn.Matches ann paramTy →
      Typing rigidCount (PolyTy.mono paramTy :: ctx) body bodyTy →
      Typing rigidCount ctx (.lambda ann body) (.arrow paramTy bodyTy)

  | app :
      Typing rigidCount ctx function (.arrow argumentTy resultTy) →
      Typing rigidCount ctx argument argumentTy →
      Typing rigidCount ctx (.app function argument) resultTy

  | letMono :
      rhsTy.WF rigidCount 0 →
      Typing rigidCount ctx rhs rhsTy →
      Typing rigidCount (PolyTy.mono rhsTy :: ctx) body bodyTy →
      Typing rigidCount ctx (.letIn none rhs body) bodyTy

  | letPoly :
      SchemeTemplateMatches written scheme →
      scheme.WF rigidCount →
      ctx.WF rigidCount →
      rhs.TypeScoped rigidCount scheme.paramCount →
      Typing (rigidCount + scheme.paramCount) ctx
        (rhs.openRigids rigidCount scheme.paramCount)
        (scheme.openRigids rigidCount) →
      Typing rigidCount (scheme :: ctx) body bodyTy →
      Typing rigidCount ctx (.letIn (some written) rhs body) bodyTy

  | fix :
      selfTy.WF rigidCount 0 →
      ann.Matches selfTy →
      Typing rigidCount (PolyTy.mono selfTy :: ctx) body selfTy →
      Typing rigidCount ctx (.fix ann body) selfTy

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
inductive Elaborates : Nat → Ctx → Source → Expr Ty → Ty → Prop
  | primLit :
      Elaborates rigidCount ctx (.primLit literal) (.primLit literal) literal.ty

  | primOp :
      Elaborates rigidCount ctx (.primOp op) (.primOp op) op.ty

  | var :
      ctx[index]? = some scheme →
      scheme.WF rigidCount →
      args.length = scheme.paramCount →
      (∀ arg ∈ args, arg.WF rigidCount 0) →
      Elaborates rigidCount ctx (.var index) (.var index) (scheme.openWith args)

  | lambda :
      paramTy.WF rigidCount 0 →
      ParamAnn.Matches ann paramTy →
      Elaborates rigidCount (PolyTy.mono paramTy :: ctx) body bodyElab bodyTy →
      Elaborates rigidCount ctx (.lambda ann body)
        (.lambda (some paramTy) bodyElab) (.arrow paramTy bodyTy)

  | app :
      Elaborates rigidCount ctx function functionElab
        (.arrow argumentTy resultTy) →
      Elaborates rigidCount ctx argument argumentElab argumentTy →
      Elaborates rigidCount ctx (.app function argument)
        (.app functionElab argumentElab) resultTy

  | letMono :
      rhsTy.WF rigidCount 0 →
      Elaborates rigidCount ctx rhs rhsElab rhsTy →
      Elaborates rigidCount (PolyTy.mono rhsTy :: ctx) body bodyElab bodyTy →
      Elaborates rigidCount ctx (.letIn none rhs body)
        (.letIn none rhsElab bodyElab) bodyTy

  | letPoly :
      SchemeTemplateMatches written scheme →
      scheme.WF rigidCount →
      ctx.WF rigidCount →
      rhs.TypeScoped rigidCount scheme.paramCount →
      Elaborates (rigidCount + scheme.paramCount) ctx
        (rhs.openRigids rigidCount scheme.paramCount) rhsElab
        (scheme.openRigids rigidCount) →
      -- A polymorphic signature's holes are determined by the definition
      -- and its context alone: no other completion also checks. (A
      -- signature without binders is an ordinary partial annotation, whose
      -- holes later uses may determine.)
      (scheme.paramCount = 0 ∨
        ∀ other : PolyTy, SchemeTemplateMatches written other →
          other.WF rigidCount →
          Typing (rigidCount + other.paramCount) ctx
            (rhs.openRigids rigidCount other.paramCount)
            (other.openRigids rigidCount) →
          other = scheme) →
      Elaborates rigidCount (scheme :: ctx) body bodyElab bodyTy →
      Elaborates rigidCount ctx (.letIn (some written) rhs body)
        (.letIn (some scheme) rhsElab bodyElab) bodyTy

  | fix :
      selfTy.WF rigidCount 0 →
      ann.Matches selfTy →
      Elaborates rigidCount (PolyTy.mono selfTy :: ctx) body bodyElab selfTy →
      Elaborates rigidCount ctx (.fix ann body) (.fix selfTy bodyElab) selfTy

end EPL
