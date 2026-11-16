import EPL2.Spec.Syntax
import EPL2.Spec.Runtime

/-!
# Declarative metatheory

Everything here is proved once for `TypingWith sig Det`, generically in the
let condition `Det`, so it holds for both `Typing` and `Elaborates`.
-/

namespace EPL2

theorem PrimLit.ty_wf (literal : PrimLit) : (literal.ty : Ty V).WF k := by
  sorry

theorem PrimOp.ty_wf {op : PrimOp} {ty : Ty V} (typed : op.ty sig = some ty) : ty.WF k := by
  sorry

theorem PrimOp.ty_lift {op : PrimOp} {ty : SemTy} (typed : op.ty sig = some ty) :
    op.ty sig = some (ty.lift : Ty V) := by
  sorry

/-- Primitive operator types have no variables. -/
theorem PrimOp.ty_bind {op : PrimOp} {ty : Ty V} (typed : op.ty sig = some ty) (f : V → Ty W) :
    op.ty sig = some (ty.bind f) := by
  sorry

theorem PrimLit.ty_bind (literal : PrimLit) (f : V → Ty W) :
    (literal.ty : Ty V).bind f = literal.ty := by
  sorry

theorem Signature.schemeOf_wf {sig : Signature} (found : sig.schemeOf c = some scheme) : scheme.WF 0 := by
  sorry

namespace TypingWith

/-- A weaker let condition admits more derivations. -/
theorem mono {Det Det' : LetCondition}
    (weaker : ∀ k ctx ann rhs scheme, Det k ctx ann rhs scheme → Det' k ctx ann rhs scheme)
    (typing : TypingWith sig Det k ctx src elaboration ty) :
    TypingWith sig Det' k ctx src elaboration ty := by
  sorry

/-- Types are well-formed. Proof: induction on the derivation; the `var`
and `const` cases are `Scheme.inst_wf`. -/
theorem regular (ctxWF : ctx.WF k) (typing : TypingWith sig Det k ctx src elaboration ty) :
    ty.WF k := by
  sorry

/-- A source program and its elaboration erase alike. -/
theorem erase_eq (typing : TypingWith sig Det k ctx src elaboration ty) : elaboration.erase = src.erase := by
  sorry

/-- Erasure preserves typing. Proof: induction on the derivation. In the
`letPoly` case the induction hypothesis types the right-hand side at the
generic instance at depth `k + arity`; `RuntimeTyping.substRigids` with
`blockSubst k args` and `Scheme.skolemize_substRigids` give every other
instance, and `Scheme.substRigids_eq_self` shows the context is unchanged. -/
theorem erase (ctxWF : ctx.WF k) (typing : TypingWith sig Det k ctx src elaboration ty) :
    RuntimeTyping sig k ctx src.erase ty := by
  sorry

end TypingWith

theorem Elaborates.typing (elaborates : Elaborates sig k ctx src elaboration ty) :
    Typing sig k ctx src elaboration ty :=
  TypingWith.mono (fun _ _ _ _ _ _ => trivial) elaborates

end EPL2
