import EPL.Syntax

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

namespace EPL

/-- The type of a literal. -/
def PrimLit.ty : PrimLit → Ty V
  | .unit => .prim .unit
  | .int _ => .prim .int
  | .char _ => .prim .char

/-- By convention, declaration 0 of a signature is `Bool`, with constructors
`True | False` in that order. Comparisons are typed only in signatures that
follow the convention. -/
def boolDecl : DataDecl := ⟨0, [[], []]⟩

/-- The type `Bool`: declaration 0, by convention (see `boolDecl`). -/
def Ty.bool : Ty V := .con 0

/-- The signature follows the `Bool` convention: declaration 0 is `boolDecl`. -/
def Signature.HasBool (sig : Signature) : Prop := sig[0]? = some boolDecl

/-- `Signature.HasBool` is decidable. -/
instance (sig : Signature) : Decidable sig.HasBool :=
  inferInstanceAs (Decidable (sig[0]? = some boolDecl))

/-- The type of an operator; `none` for a comparison if the signature has no
`Bool`. -/
def PrimOp.ty (sig : Signature) : PrimOp → Option (Ty V)
  | .intAdd | .intSub => some (.arrow (.prim .int) (.arrow (.prim .int) (.prim .int)))
  | .intLt => if sig.HasBool then some (.arrow (.prim .int) (.arrow (.prim .int) .bool)) else none
  | .charLt => if sig.HasBool then some (.arrow (.prim .char) (.arrow (.prim .char) .bool)) else none

/-- Apply `head` to `args` in order: `Ty.apps (.con 3) [a, b]` is `Pair a b`
if `Pair` is declaration 3. -/
def Ty.apps (head : Ty V) (args : List (Ty V)) : Ty V := args.foldl .app head

/-- `domain_1 -> ... -> domain_n -> codomain`. -/
def Ty.arrows (domains : List (Ty V)) (codomain : Ty V) : Ty V := domains.foldr .arrow codomain

/-- Declared type `type` applied to its own parameters. -/
def DataDecl.selfTy (decl : DataDecl) (type : Nat) : SemTy :=
  Ty.apps (.con type) ((List.range decl.params).map .bvar)

/-- `forall params. field_1 -> ... -> field_n -> T params`. -/
def DataDecl.ctorScheme (decl : DataDecl) (type : Nat) (fields : List SemTy) : Scheme Empty :=
  ⟨decl.params, Ty.arrows fields (decl.selfTy type)⟩

/-- Every field type mentions only the declaration's parameters. -/
def DataDecl.WF (decl : DataDecl) : Prop :=
  ∀ fields ∈ decl.ctors, ∀ field ∈ fields, field.Scoped 0 decl.params

/-- `DataDecl.WF` is decidable. -/
instance (decl : DataDecl) : Decidable decl.WF :=
  inferInstanceAs (Decidable (∀ fields ∈ decl.ctors, ∀ field ∈ fields, _))

/-- Declaration `type`; `none` if the signature does not declare it or the
declaration is not well formed. (The check is per declaration, so an
ill-formed declaration cannot take away `Bool`'s constructors, which the
comparison operators produce.) -/
def Signature.decl? (sig : Signature) (type : Nat) : Option DataDecl := do
  let decl ← sig[type]?
  if decl.WF then some decl else none

/-- The scheme of a constructor; `none` if `Signature.decl?` has no
declaration for its type or the declaration has no such constructor. -/
def Signature.ctorScheme (sig : Signature) (ref : CtorRef) : Option (Scheme Empty) := do
  let decl ← sig.decl? ref.type
  let fields ← decl.ctors[ref.index]?
  some (decl.ctorScheme ref.type fields)

/-- `scheme` completes the written annotation `ann` at depth `k`. -/
structure PolyAnn.Completes (k : Nat) (ann : PolyAnn Template) (scheme : Scheme Empty) :
    Prop where
  arity_eq : scheme.arity = ann.arity
  wf : scheme.WF k
  body_matches : ann.body.Matches (scheme.skolemize k)

/-- The type of a side condition on explicit polymorphic lets: a predicate on
the depth, context, written annotation, right-hand side and completed scheme.
`TypingWith` takes one as its `Det` parameter and checks it only in `letPoly`,
as one extra premise. So a `LetCondition` says how strict typing is about
explicit lets. `Typing` uses the condition that always holds; `Elaborates`
uses `Determined`, which requires the annotation's holes to have exactly one
valid filling. `Determined` is defined in terms of `Typing`, which is why it
is a parameter rather than a premise written into the rules. -/
abbrev LetCondition := Nat → Ctx Empty → PolyAnn Template → Source → Scheme Empty → Prop

/-- `TypingWith sig Det k ctx src elab ty`: at rigid depth `k` (rigid levels
below `k` in scope), in `ctx` (entry `i` types `var i`), source `src` has type
`ty`, and `elab` is `src` with every implicit type filled in. `Det` is a side
condition on explicit lets: see `Typing` and `Elaborates` for the two
instances. Every rule elaborates to the same shape of node as its source. -/
inductive TypingWith (sig : Signature) (Det : LetCondition) :
    Nat → Ctx Empty → Source → Elab → SemTy → Prop

  /-- A literal has its built-in type. -/
  | lit :
      TypingWith sig Det k ctx (.lit literal) (.lit literal) literal.ty

  /-- An operator has its fixed type (comparisons only if the signature has
  `Bool`). -/
  | primOp :
      op.ty sig = some ty →
      TypingWith sig Det k ctx (.primOp op) (.primOp op) ty

  /-- A constructor has any instance of its scheme from the signature, by type
  arguments well formed at depth `k`. -/
  | ctor :
      sig.ctorScheme ref = some scheme →
      scheme.Instance k ty →
      TypingWith sig Det k ctx (.ctor ref) (.ctor ref) ty

  /-- A variable has any instance of its scheme in the context, by type
  arguments well formed at depth `k`. -/
  | var :
      ctx[index]? = some scheme →
      scheme.Instance k ty →
      TypingWith sig Det k ctx (.var index) (.var index) ty

  /-- `fun x => body : paramTy -> bodyTy`, for some well-formed `paramTy` that
  completes the annotation (if any). The elaboration records `paramTy`. -/
  | lambda :
      paramTy.WF k →
      Template.MatchesOpt param paramTy →
      TypingWith sig Det k (.mono paramTy :: ctx) body bodyElab bodyTy →
      TypingWith sig Det k ctx (.lambda param body) (.lambda (some paramTy) bodyElab)
        (.arrow paramTy bodyTy)

  /-- Application: the argument's type is the function's domain. -/
  | app :
      TypingWith sig Det k ctx function functionElab (.arrow argumentTy resultTy) →
      TypingWith sig Det k ctx argument argumentElab argumentTy →
      TypingWith sig Det k ctx (.app function argument) (.app functionElab argumentElab) resultTy

  /-- Unannotated `let`: no generalization, so `body` sees the right-hand side
  at its one (mono)type. -/
  | letMono :
      TypingWith sig Det k ctx rhs rhsElab rhsTy →
      TypingWith sig Det k (.mono rhsTy :: ctx) body bodyElab bodyTy →
      TypingWith sig Det k ctx (.letIn none rhs body) (.letIn none rhsElab bodyElab) bodyTy

  /-- `let x : forall as. T = rhs in body`: complete the annotation to
  `scheme`, check `rhs` against its generic instance (binders as the fresh
  rigid levels `k, ..., k + arity - 1`), check the side condition `Det`, and
  give `body` the scheme. The elaboration records the scheme in `PolyAnn` form.
  -/
  | letPoly :
      ann.Completes k scheme →
      TypingWith sig Det (k + scheme.arity) ctx rhs rhsElab (scheme.skolemize k) →
      Det k ctx ann rhs scheme →
      TypingWith sig Det k (scheme :: ctx) body bodyElab bodyTy →
      TypingWith sig Det k ctx (.letIn (some ann) rhs body)
        (.letIn (some ⟨scheme.arity, scheme.skolemize k⟩) rhsElab bodyElab) bodyTy

  /-- `fix self => body : selfTy`, for some well-formed `selfTy` that completes
  the annotation (if any), if `body : selfTy` assuming `self : selfTy`. The
  elaboration records `selfTy`. -/
  | fix :
      selfTy.WF k →
      Template.MatchesOpt self selfTy →
      TypingWith sig Det k (.mono selfTy :: ctx) body bodyElab selfTy →
      TypingWith sig Det k ctx (.fix self body) (.fix (some selfTy) bodyElab) selfTy

  /-- A match on a value of type `T args`: there is at least one branch; every
  pattern is a constructor of `T`; and the branch for a constructor with
  fields `f_1 ... f_n` has type `f_1 -> ... -> f_n -> resultTy` (the fields
  instantiated at `args`). The match need not be exhaustive. The elaboration
  keeps the patterns and elaborates each branch body. -/
  | «match» :
      TypingWith sig Det k ctx scrutinee scrutineeElab (Ty.apps (.con type) args) →
      sig.decl? type = some decl →
      args.length = decl.params →
      branches ≠ [] →
      (∀ pattern ∈ branches.map (·.1), pattern.type = type ∧ pattern.index < decl.ctors.length) →
      branchesElab.map (·.1) = branches.map (·.1) →
      (∀ (i : Nat) pattern body bodyElab fields,
        branches[i]? = some (pattern, body) →
        branchesElab[i]? = some (pattern, bodyElab) →
        decl.ctors[pattern.index]? = some fields →
        TypingWith sig Det k ctx body bodyElab
          (Ty.arrows (fields.map (·.instantiate args)) resultTy)) →
      TypingWith sig Det k ctx (.match scrutinee branches) (.match scrutineeElab branchesElab)
        resultTy

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

  /-- A literal has its built-in type. -/
  | lit :
      RuntimeTyping sig k ctx (.lit literal) literal.ty

  /-- An operator has its fixed type (comparisons only if the signature has
  `Bool`). -/
  | primOp :
      op.ty sig = some ty →
      RuntimeTyping sig k ctx (.primOp op) ty

  /-- A constructor has any instance of its scheme from the signature, by type
  arguments well formed at depth `k`. -/
  | ctor :
      sig.ctorScheme ref = some scheme →
      scheme.Instance k ty →
      RuntimeTyping sig k ctx (.ctor ref) ty

  /-- A variable has any instance of its scheme in the context, by type
  arguments well formed at depth `k`. -/
  | var :
      ctx[index]? = some scheme →
      scheme.Instance k ty →
      RuntimeTyping sig k ctx (.var index) ty

  /-- `fun x => body : paramTy -> bodyTy`, for any well-formed `paramTy`. -/
  | lambda :
      paramTy.WF k →
      RuntimeTyping sig k (.mono paramTy :: ctx) body bodyTy →
      RuntimeTyping sig k ctx (.lambda param body) (.arrow paramTy bodyTy)

  /-- Application: the argument's type is the function's domain. -/
  | app :
      RuntimeTyping sig k ctx function (.arrow argumentTy resultTy) →
      RuntimeTyping sig k ctx argument argumentTy →
      RuntimeTyping sig k ctx (.app function argument) resultTy

  /-- `let x = rhs in body`, with `x : scheme` in `body`, if `rhs` has every
  instance of `scheme` at every depth `k' ≥ k`. -/
  | letIn :
      scheme.WF k →
      (∀ k', k ≤ k' → ∀ ty, scheme.Instance k' ty → RuntimeTyping sig k' ctx rhs ty) →
      RuntimeTyping sig k (scheme :: ctx) body bodyTy →
      RuntimeTyping sig k ctx (.letIn ann rhs body) bodyTy

  /-- `fix self => body : selfTy`, for any well-formed `selfTy`, if
  `body : selfTy` assuming `self : selfTy`. -/
  | fix :
      selfTy.WF k →
      RuntimeTyping sig k (.mono selfTy :: ctx) body selfTy →
      RuntimeTyping sig k ctx (.fix self body) selfTy

  /-- A match on a value of type `T args`, as in `TypingWith`: at least one
  branch, every pattern a constructor of `T`, and each branch a function of
  its constructor's fields (instantiated at `args`) to `resultTy`. -/
  | «match» :
      RuntimeTyping sig k ctx scrutinee (Ty.apps (.con type) args) →
      sig.decl? type = some decl →
      args.length = decl.params →
      branches ≠ [] →
      (∀ pattern ∈ branches.map (·.1), pattern.type = type ∧ pattern.index < decl.ctors.length) →
      (∀ pattern body fields, (pattern, body) ∈ branches →
        decl.ctors[pattern.index]? = some fields →
        RuntimeTyping sig k ctx body (Ty.arrows (fields.map (·.instantiate args)) resultTy)) →
      RuntimeTyping sig k ctx (.match scrutinee branches) resultTy

/-! ## Exhaustiveness

Separate from typing, as in FHM: a well-typed match may be partial, and
progress holds for programs that are well typed *and* exhaustive. -/

/-- Every type that a match's patterns name has each of its constructors
covered by some pattern. (With typing, a match's patterns name exactly one
type, which typing also requires to be the scrutinee's.) -/
def Signature.Covers (sig : Signature) (patterns : List CtorRef) : Prop :=
  ∀ pattern ∈ patterns, ∀ decl, sig[pattern.type]? = some decl →
    ∀ index < decl.ctors.length, ⟨pattern.type, index⟩ ∈ patterns

/-- Every match inside the expression covers its type (`Signature.Covers`). -/
inductive Exhaustive {A : Type} (sig : Signature) : Expr A → Prop

  | lit : Exhaustive sig (.lit literal)

  | primOp : Exhaustive sig (.primOp op)

  | ctor : Exhaustive sig (.ctor ref)

  | var : Exhaustive sig (.var index)

  | lambda : Exhaustive sig body → Exhaustive sig (.lambda param body)

  | app : Exhaustive sig function → Exhaustive sig argument →
      Exhaustive sig (.app function argument)

  | letIn : Exhaustive sig rhs → Exhaustive sig body → Exhaustive sig (.letIn ann rhs body)

  | fix : Exhaustive sig body → Exhaustive sig (.fix self body)

  /-- The patterns cover their type, and the scrutinee and every branch body
  are exhaustive. -/
  | «match» :
      Exhaustive sig scrutinee →
      (∀ branch ∈ branches, Exhaustive sig branch.2) →
      sig.Covers (branches.map (·.1)) →
      Exhaustive sig (.match scrutinee branches)

/-- `Signature.Covers`, as a check. -/
def Signature.covers (sig : Signature) (patterns : List CtorRef) : Bool :=
  patterns.all fun pattern =>
    match sig[pattern.type]? with
    | none => true
    | some decl =>
        (List.range decl.ctors.length).all fun index => patterns.contains ⟨pattern.type, index⟩

mutual
/-- `Exhaustive`, as a check. -/
def Expr.exhaustive (sig : Signature) : Expr A → Bool
  | .lit _ | .primOp _ | .ctor _ | .var _ => true
  | .lambda _ body | .fix _ body => body.exhaustive sig
  | .app function argument => function.exhaustive sig && argument.exhaustive sig
  | .letIn _ rhs body => rhs.exhaustive sig && body.exhaustive sig
  | .match scrutinee branches =>
      scrutinee.exhaustive sig && Expr.exhaustiveBranches sig branches &&
        sig.covers (branches.map (·.1))

/-- `Expr.exhaustive` on every branch body. -/
def Expr.exhaustiveBranches (sig : Signature) : List (CtorRef × Expr A) → Bool
  | [] => true
  | (_, body) :: rest => body.exhaustive sig && Expr.exhaustiveBranches sig rest
end

end EPL
