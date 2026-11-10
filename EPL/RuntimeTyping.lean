import EPL.Eval
import EPL.Typing

namespace EPL

/-- Typing after annotations have been erased. Runtime syntax does not retain
whether a source let was monomorphic or carried an explicit scheme, so the
relation has separate derivations for the same erased constructor. -/
inductive RuntimeTyping : Nat → Ctx → RuntimeExpr → Ty → Prop
  | primLit :
      RuntimeTyping rigidCount ctx (.primLit literal) literal.ty

  | primOp :
      RuntimeTyping rigidCount ctx (.primOp op) op.ty

  | var :
      ctx[index]? = some scheme →
      scheme.WF rigidCount →
      args.length = scheme.paramCount →
      (∀ arg ∈ args, arg.WF rigidCount 0) →
      RuntimeTyping rigidCount ctx (.var index) (scheme.openWith args)

  | lambda :
      paramTy.WF rigidCount 0 →
      RuntimeTyping rigidCount (PolyTy.mono paramTy :: ctx) body bodyTy →
      RuntimeTyping rigidCount ctx (.lambda ann body) (.arrow paramTy bodyTy)

  | app :
      RuntimeTyping rigidCount ctx function (.arrow argumentTy resultTy) →
      RuntimeTyping rigidCount ctx argument argumentTy →
      RuntimeTyping rigidCount ctx (.app function argument) resultTy

  | letMono :
      rhsTy.WF rigidCount 0 →
      RuntimeTyping rigidCount ctx rhs rhsTy →
      RuntimeTyping rigidCount (PolyTy.mono rhsTy :: ctx) body bodyTy →
      RuntimeTyping rigidCount ctx (.letIn ann rhs body) bodyTy

  | letPoly :
      scheme.WF rigidCount →
      ctx.WF rigidCount →
      RuntimeTyping (rigidCount + scheme.paramCount) ctx rhs
        (scheme.openRigids rigidCount) →
      RuntimeTyping rigidCount (scheme :: ctx) body bodyTy →
      RuntimeTyping rigidCount ctx (.letIn ann rhs body) bodyTy

  | fix :
      selfTy.WF rigidCount 0 →
      RuntimeTyping rigidCount (PolyTy.mono selfTy :: ctx) body selfTy →
      RuntimeTyping rigidCount ctx (.fix () body) selfTy

/-- A runtime expression inhabits every semantic instance of a scheme. -/
structure RuntimeHasScheme (rigidCount : Nat) (ctx : Ctx)
    (expr : RuntimeExpr) (scheme : PolyTy) : Prop where
  schemeWF : scheme.WF rigidCount
  typed : ∀ larger, rigidCount ≤ larger → ∀ args,
    args.length = scheme.paramCount →
    (∀ arg ∈ args, arg.WF larger 0) →
    RuntimeTyping larger ctx expr (scheme.openWith args)

end EPL
