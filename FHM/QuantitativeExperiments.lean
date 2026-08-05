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
