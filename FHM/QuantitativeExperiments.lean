namespace QuantitativeExperiments

/-- Name of a type -/
inductive TyName
  | mk (str : String)
  deriving DecidableEq, Repr

/-- Name of a type constructor -/
inductive CtorName
  | mk (str : String)
  deriving DecidableEq, Repr

/-- Name of a value binding (or type variable) -/
inductive ValName
  | mk (str : String)
  deriving DecidableEq, Repr





inductive PrimTy
  | unit
  | int
  deriving DecidableEq, Repr


inductive Ty
  | prim : PrimTy → Ty
  | arrow : (from_ to_ : Ty) → Ty


  /-- This demarcates a new uniqueness scope, which means `contents` may contain `.uniqueTy`s where a `uniqBinder` of 0 denotes that those values must be unique inside this scope. This goes under binders though so if there is another `.uniqueScope` inside `contents`, a `uniqBinder` of 0 denotes that it is scoped inside that inner scope, so a `uniqBinder` of 1 will reference back to _this_ scope. -/
  | uniqueScope (contents : Ty) : Ty

  /-- Values of this type may appear up to once in any data structure under uniqueness scope `uniqBinder` -/
  | uniqueTy (uniqBinder : Nat) (inner : Ty)
  deriving Repr




/-- Primitive literals -/
inductive PrimLitExpr
  | unit : PrimLitExpr
  | int : Int → PrimLitExpr


/-- An expression in our language -/
inductive Expr
  | primLit (prim : PrimLitExpr)
  /-- A lambda -/
  | lambda (body : Expr)
  /-- A function application -/
  | app (f input : Expr)
  /-- A let binding -/
  | letIn (bindingExpr body : Expr)
  /-- A variable use -/
  | var (deBruijnIndex : Nat)

-- def PrimLitExpr.ty : PrimLitExpr → Ty
--   | .unit => .prim .unit
--   | .int _ => .prim .int

/-- Value typing context: de Bruijn index `i` looks up `ctx[i]`. -/
abbrev Ctx := List Ty

/-- Declarative typing. `uniqueScope` / `uniqueTy` appear only in `Ty`; this
    relation does not enforce uniqueness yet — it is ordinary structural typing. -/
inductive TypeOf : Ctx → Expr → Ty → Prop
  | primLitUnit (prim : PrimLitExpr) :
      TypeOf ctx (.primLit .unit) (.prim .unit)

  | primLitInt (prim : PrimLitExpr) :
      TypeOf ctx (.primLit (.int _)) (.prim .int)

  | lambda {paramTy bodyTy : Ty} :
      TypeOf (paramTy :: ctx) body bodyTy →
      TypeOf ctx (.lambda body) (.arrow paramTy bodyTy)

  | app {argTy retTy : Ty} :
      TypeOf ctx f (.arrow argTy retTy) →
      TypeOf ctx input argTy →
      TypeOf ctx (.app f input) retTy

  | letIn {bindingTy bodyTy : Ty} :
      TypeOf ctx bindingExpr bindingTy →
      TypeOf (bindingTy :: ctx) body bodyTy →
      TypeOf ctx (.letIn bindingExpr body) bodyTy

  | var {τ : Ty} (i : Nat) :
      ctx[i]? = some τ →
      TypeOf ctx (.var i) τ

end QuantitativeExperiments
