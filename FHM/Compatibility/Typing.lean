import FHM.Core

/-! Historical complete-annotation typing, available only to compatibility clients.
Canonical source syntax and runtime foundations do not import this module. -/

/-- An optional annotation, when present, pins a rule-internal choice: the
    `lambda` rule's parameter type must be the parameter ascription (if any),
    and the `letIn` rule's generalised scheme must be the `let`'s ascription
    (if any). For `none` this is vacuous — the choice is free (inferred).

    Pins are structural: an annotation fixes the corresponding type exactly. -/
def Option.Pins {α : Type _} (ann : Option α) (x : α) : Prop :=
  ∀ a, ann = some a → x = a

/-- **The cofinite let-generalisation premise**: the bound expression types at
    EVERY sufficiently-fresh opening `Xs` of the scheme `M`, with the
    annotation's own scoped type variables opened to the *same* `Xs`
    (`Expr.openBoundTyVars`; for an unannotated `let` the expression is typed
    unchanged). Quantifying over all fresh openings (rather than one existential
    choice) is what makes the rule stable under weakening and substitution; the
    ann-lockstep opening is the spec-level home of scoped type variables. -/
def GeneralisesTo (TypeOf : Ctx → Expr → Ty → Prop) (ctx : Ctx)
    (ann : Option PolyTy) (boundExpr : Expr) (M : PolyTy) (L : List Nat) : Prop :=
  ∀ Xs : List Nat, FreshNames L M.paramCount Xs →
    TypeOf ctx (Expr.openBoundTyVars ann Xs boundExpr) (M.openVars Xs)

/-- Cofinite typing of ordinary HM members one residual dependency SCC at a
time. Earlier components are generalized in `stageCtx`; the current component
and syntactically unreachable later components remain monomorphic. -/
def RecSpecs.StratifiedMonoTyped (TypeOf : Ctx → Expr → Ty → Prop) (ctx : Ctx)
    (bindings : List CoreRecBinding) (specs : List RecSpec) (groups : List (List Nat))
    (G L : List Nat) : Prop :=
  ∀ stage component, groups[stage]? = some component →
    ∀ Xs, FreshNames L G.length Xs →
      ∀ member ∈ component, ∀ binding τ,
        bindings[member]? = some binding →
        specs[member]? = some (.mono τ) →
        TypeOf
          (RecSpecs.stageCtx ctx specs (groups.take stage).flatten G Xs)
          binding.rhs (Ty.renameG G Xs τ)

/-- Cofinite scheme-relative checking for completely annotated members after
the ordinary HM members have been solved and generalised.  Complete signatures
are dependency cuts: a signed RHS sees the same FINAL schemes as the group body,
so both signed and inferred siblings are available polymorphically.  The
member's own quantified variables are still opened rigidly and cofinally. -/
def RecSpecs.PolyTypedFinal (TypeOf : Ctx → Expr → Ty → Prop) (ctx : Ctx)
    (bindings : List CoreRecBinding) (specs : List RecSpec) (G L : List Nat) : Prop :=
  ∀ pair ∈ bindings.zip specs, ∀ σ, pair.2 = .poly σ →
    ∀ Ys, FreshNames L σ.paramCount Ys →
      TypeOf (RecSpecs.bodyCtx ctx specs G)
        (pair.1.rhs.openTyVars Ys) (σ.openVars Ys)


/-! ### Historical complete-Core typing `TypeOfHM`.

Rank-one let-polymorphism with complete annotations admitting polymorphic
recursive uses. The canonical partial-source specification is `InputTyping`
in `SourceTyping.lean`; this relation retains complete-Core compatibility.
A variable use instantiates its environment scheme by
existential witness types. Source annotations constrain `lambda`, `letIn`,
and `letRec`.

Runtime safety is proved by erasing a source derivation into `RuntimeTyping.RunWT`,
whose scheme witnesses remain in the proof and never enter the runtime terms. -/

mutual

/-- Historical complete-Core typing, retained for compatibility, shared
primitive rules and neutral runtime lemmas. Canonical partial-source typing
is `InputTyping`. -/
inductive TypeOfHM : Ctx → Expr → Ty → Prop
  | primLitUnit :
    TypeOfHM ctx (.primLit .unit) (.prim .unit)

  | primLitInt :
    TypeOfHM ctx (.primLit (.int n)) (.prim .int)

  | primLitNat :
    TypeOfHM ctx (.primLit (.nat n)) (.prim .nat)

  | primLitChar :
    TypeOfHM ctx (.primLit (.char c)) (.prim .char)

  /-- `intAdd : int → int → int`. -/
  | primBinOpIntAdd :
    TypeOfHM ctx (.primBinOp .intAdd)
      (.arrow (.prim .int) (.arrow (.prim .int) (.prim .int)))

  /-- `intSub : int → int → int`. -/
  | primBinOpIntSub :
    TypeOfHM ctx (.primBinOp .intSub)
      (.arrow (.prim .int) (.arrow (.prim .int) (.prim .int)))

  /-- `intLt : int → int → Bool`. -/
  | primBinOpIntLt :
    TypeOfHM ctx (.ctor ⟨"True"⟩) (.customTy ⟨"Bool"⟩ []) →
    TypeOfHM ctx (.ctor ⟨"False"⟩) (.customTy ⟨"Bool"⟩ []) →
    TypeOfHM ctx (.primBinOp .intLt)
      (.arrow (.prim .int) (.arrow (.prim .int) (.customTy ⟨"Bool"⟩ [])))

  /-- `charLt : char → char → Bool`. -/
  | primBinOpCharLt :
    TypeOfHM ctx (.ctor ⟨"True"⟩) (.customTy ⟨"Bool"⟩ []) →
    TypeOfHM ctx (.ctor ⟨"False"⟩) (.customTy ⟨"Bool"⟩ []) →
    TypeOfHM ctx (.primBinOp .charLt)
      (.arrow (.prim .char) (.arrow (.prim .char) (.customTy ⟨"Bool"⟩ [])))

  | lambda :
    paramTy.IsLC →
    ann.Pins paramTy →
    bodyCtx = { ctx with env := PolyTy.mkTrivial paramTy :: ctx.env } →
    TypeOfHM bodyCtx body bodyTy →
    TypeOfHM ctx (.lambda ann body) (.arrow paramTy bodyTy)

  | app :
    TypeOfHM ctx f (.arrow argTy retTy) →
    TypeOfHM ctx input argTy →
    TypeOfHM ctx (.app f input) retTy


  /-- Cofinite let-generalisation; see `GeneralisesTo`. -/
  | letIn {M : PolyTy} {L : List Nat} :
    PolyTy.WF M →
    ann.Pins M →
    GeneralisesTo TypeOfHM ctx ann boundExpr M L →
    bodyCtx = { ctx with env := M :: ctx.env } →
    TypeOfHM bodyCtx body bodyTy →
    TypeOfHM ctx (.letIn ann boundExpr body) bodyTy

  /-- A variable scheme is instantiated by existential witness `instArgs`, with
      no separate term-level type application: classic erased HM
      instantiation. -/
  | var :
    ctx.env[dbl]? = some polyTy →
    (∀ tyArg ∈ instArgs, tyArg.IsLC) →
    polyTy.InstantiatesTo instArgs ty →
    TypeOfHM ctx (.var dbl) ty

  | ctor :
    LookupList.get? ctx.ctors name = some ctor →
    (∀ tyArg ∈ tyArgs, tyArg.IsLC) →
    ctor.toTy.InstantiatesTo tyArgs ty →
    TypeOfHM ctx (.ctor name) ty

  | match_ :
    TypeOfHM ctx scrutinee scrutTy →
    branches ≠ [] →
    (∀ branch ∈ branches, TypeOfMatchBranch ctx branch scrutTy resultTy) →
    TypeOfHM ctx (.match_ scrutinee branches) resultTy

  /-- Mixed recursive group. Completely annotated members are dependency cuts.
      The residual graph of unannotated members is partitioned into
      dependency-first components; each component is checked monomorphically
      while earlier components are already generalized. Signed RHSs are then
      checked at every fresh rigid opening under the final scheme environment. -/
  | letRec {specs : List RecSpec} {groups : List (List Nat)} {G L : List Nat} :
    RecGroups.ValidResidualGroups bindings groups →
    RecSpecs.WF bindings specs G →
    RecSpecs.StratifiedMonoTyped TypeOfHM ctx bindings specs groups G L →
    RecSpecs.PolyTypedFinal TypeOfHM ctx bindings specs G L →
    bodyCtx = RecSpecs.bodyCtx ctx specs G →
    TypeOfHM bodyCtx body ρ →
    TypeOfHM ctx (.letRec bindings body) ρ


/-- Match-branch typing for the declarative `TypeOfHM`. `BranchCtorSpec` carries
    the scrutinee's existential type-argument witness. -/
inductive TypeOfMatchBranch :
  (ctx : Ctx) → (MatchPattern × Expr) → (scrutTy : Ty) → (resultTy : Ty) → Prop
  | mk {ctor : Ctor} {ctx : Ctx} {c : CtorName} {n : Nat} {tyArgs instContents : List Ty} :
    BranchCtorSpec ctx.ctors c n scrutTy ctor tyArgs instContents →
    bodyCtx = { ctx with env := instContents.map PolyTy.mkTrivial ++ ctx.env } →
    TypeOfHM bodyCtx bodyExpr resultTy →
    TypeOfMatchBranch ctx (.named c n, bodyExpr) scrutTy resultTy
  | wildcard {ctx : Ctx} :
    TypeOfHM ctx bodyExpr resultTy →
    TypeOfMatchBranch ctx (.wildcard, bodyExpr) scrutTy resultTy

end
