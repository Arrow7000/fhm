import EPL2.Syntax

/-!
# Declarative typing

`TypingWith sig Det k ctx src elab ty`: at rigid depth `k`, in `ctx`, source
`src` has type `ty`, and `elab` is `src` with every implicit type filled in
(lambda parameter types, `fix` types, and explicit lets' completed schemes,
recorded at the let's own rigid depth, i.e. in `PolyAnn` form).

The relation is parametric in a side condition `Det` on explicit lets, which
gives two instances from one set of rules:

* `Typing := TypingWith sig (no condition)`;
* `Elaborates := TypingWith sig (Determined sig)`, where `Determined` says a
  polymorphic signature's holes are fixed by its definition and context alone.

(`Determined` must mention `Typing` negatively, so it cannot be one more
premise of a single inductive definition.)

There are no scoping premises on contexts or source annotations: theorems
assume `ctx.WF k`, and a source annotation with an out-of-scope variable
matches no well-formed type.
-/

namespace EPL2

def PrimLit.ty : PrimLit → Ty V
  | .unit => .prim .unit
  | .int _ => .prim .int
  | .char _ => .prim .char

/-- By convention, declaration 0 of a signature is `Bool`, with constructors
`True | False` in that order. Comparisons are typed only in signatures that
follow the convention. -/
def boolDecl : DataDecl := ⟨0, [[], []]⟩

def Ty.bool : Ty V := .con 0

def Signature.HasBool (sig : Signature) : Prop := sig[0]? = some boolDecl

instance (sig : Signature) : Decidable sig.HasBool :=
  inferInstanceAs (Decidable (sig[0]? = some boolDecl))

def PrimOp.ty (sig : Signature) : PrimOp → Option (Ty V)
  | .intAdd | .intSub => some (.arrow (.prim .int) (.arrow (.prim .int) (.prim .int)))
  | .intLt => if sig.HasBool then some (.arrow (.prim .int) (.arrow (.prim .int) .bool)) else none
  | .charLt => if sig.HasBool then some (.arrow (.prim .char) (.arrow (.prim .char) .bool)) else none

def Ty.apps (head : Ty V) (args : List (Ty V)) : Ty V := args.foldl .app head

def Ty.arrows (domains : List (Ty V)) (codomain : Ty V) : Ty V := domains.foldr .arrow codomain

/-- Declared type `type` applied to its own parameters. -/
def DataDecl.selfTy (decl : DataDecl) (type : Nat) : SemTy :=
  Ty.apps (.con type) ((List.range decl.params).map .bvar)

/-- `forall params. field_1 -> ... -> field_n -> T params`. -/
def DataDecl.ctorScheme (decl : DataDecl) (type : Nat) (fields : List SemTy) : Scheme Empty :=
  ⟨decl.params, Ty.arrows fields (decl.selfTy type)⟩

/-- A branch first receives `()`, so call-by-value evaluation does not run the
branches a match does not take, then the constructor's fields. -/
def branchTy (fields : List SemTy) (result : SemTy) : SemTy :=
  .arrow (.prim .unit) (Ty.arrows fields result)

/-- `forall params r. T params -> branch_1 -> ... -> branch_k -> r`. -/
def DataDecl.elimScheme (decl : DataDecl) (type : Nat) : Scheme Empty :=
  let result : SemTy := .bvar decl.params
  ⟨decl.params + 1,
    .arrow (decl.selfTy type) (Ty.arrows (decl.ctors.map (branchTy · result)) result)⟩

/-- The scheme of a constant; `none` if the signature does not declare it or
its scheme is ill-scoped (a field mentions an undeclared parameter). -/
def Signature.schemeOf (sig : Signature) : DataConst → Option (Scheme Empty)
  | .ctor type index => do
      let decl ← sig[type]?
      let fields ← decl.ctors[index]?
      let scheme := decl.ctorScheme type fields
      if scheme.WF 0 then some scheme else none
  | .elim type => do
      let decl ← sig[type]?
      let scheme := decl.elimScheme type
      if scheme.WF 0 then some scheme else none

/-- `scheme` completes the written annotation `ann` at depth `k`. -/
structure PolyAnn.Completes (k : Nat) (ann : PolyAnn Template) (scheme : Scheme Empty) :
    Prop where
  arity_eq : scheme.arity = ann.arity
  wf : scheme.WF k
  body_matches : ann.body.Matches (scheme.skolemize k)

/-- A side condition on explicit lets: depth, context, annotation, right-hand
side, completed scheme. -/
abbrev LetCondition := Nat → Ctx Empty → PolyAnn Template → Source → Scheme Empty → Prop

inductive TypingWith (sig : Signature) (Det : LetCondition) :
    Nat → Ctx Empty → Source → Elab → SemTy → Prop
  | lit :
      TypingWith sig Det k ctx (.lit literal) (.lit literal) literal.ty
  | primOp :
      op.ty sig = some ty →
      TypingWith sig Det k ctx (.primOp op) (.primOp op) ty
  | const :
      sig.schemeOf c = some scheme →
      scheme.Instance k ty →
      TypingWith sig Det k ctx (.const c) (.const c) ty
  | var :
      ctx[index]? = some scheme →
      scheme.Instance k ty →
      TypingWith sig Det k ctx (.var index) (.var index) ty
  | lambda :
      paramTy.WF k →
      Template.MatchesOpt param paramTy →
      TypingWith sig Det k (.mono paramTy :: ctx) body bodyElab bodyTy →
      TypingWith sig Det k ctx (.lambda param body) (.lambda (some paramTy) bodyElab)
        (.arrow paramTy bodyTy)
  | app :
      TypingWith sig Det k ctx function functionElab (.arrow argumentTy resultTy) →
      TypingWith sig Det k ctx argument argumentElab argumentTy →
      TypingWith sig Det k ctx (.app function argument) (.app functionElab argumentElab) resultTy
  | letMono :
      TypingWith sig Det k ctx rhs rhsElab rhsTy →
      TypingWith sig Det k (.mono rhsTy :: ctx) body bodyElab bodyTy →
      TypingWith sig Det k ctx (.letIn none rhs body) (.letIn none rhsElab bodyElab) bodyTy
  | letPoly :
      ann.Completes k scheme →
      TypingWith sig Det (k + scheme.arity) ctx rhs rhsElab (scheme.skolemize k) →
      Det k ctx ann rhs scheme →
      TypingWith sig Det k (scheme :: ctx) body bodyElab bodyTy →
      TypingWith sig Det k ctx (.letIn (some ann) rhs body)
        (.letIn (some ⟨scheme.arity, scheme.skolemize k⟩) rhsElab bodyElab) bodyTy
  | fix :
      selfTy.WF k →
      self.Matches selfTy →
      TypingWith sig Det k (.mono selfTy :: ctx) body bodyElab selfTy →
      TypingWith sig Det k ctx (.fix self body) (.fix selfTy bodyElab) selfTy

/-- Ordinary typing (each derivation also determines an elaboration). -/
abbrev Typing (sig : Signature) := TypingWith sig fun _ _ _ _ _ => True

/-- A polymorphic signature's holes are determined by its definition and
context: no other completion lets the right-hand side check. Later uses could
not tell apart completions that mention the scheme's own binders. A signature
without binders is an ordinary partial annotation, which later uses may
determine. -/
def Determined (sig : Signature) : LetCondition := fun k ctx ann rhs scheme =>
  scheme.arity = 0 ∨
    ∀ other otherElab, ann.Completes k other →
      Typing sig (k + other.arity) ctx rhs otherElab (other.skolemize k) → other = scheme

/-- Typing in which every implicit type the elaboration records is
determined. Inference accepts exactly the programs with a unique elaboration.
Not every typable program elaborates: in
`let f : forall a. _ -> a -> a = fun z y => y in f True True`
the `_` could be `a` or `Bool`. -/
abbrev Elaborates (sig : Signature) := TypingWith sig (Determined sig)

/-- Typing of erased programs. Its one `let` rule asks the right-hand side to
have every instance of the bound scheme, at every extension of the rigid
context (Kripke style), so depth weakening and value substitution need no
type-level reasoning. Erasure (`TypingWith.erase`) is where the generic
skolem check of `letPoly` is turned into this form, by one type-substitution
lemma (`RuntimeTyping.substRigids`). A monomorphic let is the case
`arity = 0`. -/
inductive RuntimeTyping (sig : Signature) : Nat → Ctx Empty → RuntimeExpr → SemTy → Prop
  | lit :
      RuntimeTyping sig k ctx (.lit literal) literal.ty
  | primOp :
      op.ty sig = some ty →
      RuntimeTyping sig k ctx (.primOp op) ty
  | const :
      sig.schemeOf c = some scheme →
      scheme.Instance k ty →
      RuntimeTyping sig k ctx (.const c) ty
  | var :
      ctx[index]? = some scheme →
      scheme.Instance k ty →
      RuntimeTyping sig k ctx (.var index) ty
  | lambda :
      paramTy.WF k →
      RuntimeTyping sig k (.mono paramTy :: ctx) body bodyTy →
      RuntimeTyping sig k ctx (.lambda param body) (.arrow paramTy bodyTy)
  | app :
      RuntimeTyping sig k ctx function (.arrow argumentTy resultTy) →
      RuntimeTyping sig k ctx argument argumentTy →
      RuntimeTyping sig k ctx (.app function argument) resultTy
  | letIn :
      scheme.WF k →
      (∀ k', k ≤ k' → ∀ ty, scheme.Instance k' ty → RuntimeTyping sig k' ctx rhs ty) →
      RuntimeTyping sig k (scheme :: ctx) body bodyTy →
      RuntimeTyping sig k ctx (.letIn ann rhs body) bodyTy
  | fix :
      selfTy.WF k →
      RuntimeTyping sig k (.mono selfTy :: ctx) body selfTy →
      RuntimeTyping sig k ctx (.fix self body) selfTy

end EPL2
