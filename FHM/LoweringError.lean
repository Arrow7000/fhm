import FHM.SurfaceLang
import FHM.Decls

/-! Failure data shared by verified structural lowering and operational
provenance construction. Paths refer to authored surface children. -/

inductive SurfaceStep where
  | pairLeft | pairRight | consHead | consTail
  | listItem (index : Nat)
  | lambdaBody | appFun | appArg | letRhs | letBody
  | letRecRhs (index : Nat)
  | letRecBody | ifCondition | ifThen | ifElse | matchScrut
  | matchBranch (index : Nat)
  deriving Repr, DecidableEq, BEq

abbrev SurfacePath := List SurfaceStep

inductive LowerTypeStep where
  | domain | codomain | pairLeft | pairRight
  | argument (index : Nat)
  deriving Repr, DecidableEq, BEq

inductive LoweringSite where
  | expression
  | lambdaAnnotation
  | bindingAnnotation
  | parameterAnnotation (index : Nat)
  | declaration (name : TyName)
  | constructorFields (parent : TyName) (name : CtorName)
  deriving Repr

inductive LoweringErrorReason where
  | unboundValue (name : ValName)
  | unboundTypeVariable (name : ValName)
  | unknownType (name : TyName)
  | typeArity (name : TyName) (expected actual : Nat)
  | holeNotAllowed (name : Option String)
  | duplicateTypeParameters (parent : TyName) (names : List ValName)
  | duplicateTypes (names : List TyName)
  | duplicateConstructors (names : List CtorName)
  | duplicateBindings (names : List ValName)
  | declarationElaboration (error : DeclError)
  deriving Repr

structure LoweringError where
  path : SurfacePath := []
  typePath : List LowerTypeStep := []
  site : LoweringSite := .expression
  binding? : Option ValName := none
  reason : LoweringErrorReason
  deriving Repr

def LoweringError.root (reason : LoweringErrorReason) : LoweringError := { reason }

def LoweringError.below (step : SurfaceStep) (error : LoweringError) : LoweringError :=
  { error with path := step :: error.path }

def LoweringError.belowType (step : LowerTypeStep) (error : LoweringError) : LoweringError :=
  { error with typePath := step :: error.typePath }

def LoweringError.atSite (site : LoweringSite) (error : LoweringError) : LoweringError :=
  { error with site }

def LoweringError.inBinding (name : ValName) (error : LoweringError) : LoweringError :=
  { error with binding? := error.binding?.orElse (fun _ => some name) }

def LoweringError.nextTypeArgument (error : LoweringError) : LoweringError :=
  match error.typePath with
  | .argument index :: rest => { error with typePath := .argument (index + 1) :: rest }
  | _ => error

def LoweringError.nextListItem (error : LoweringError) : LoweringError :=
  match error.path with
  | .listItem index :: rest => { error with path := .listItem (index + 1) :: rest }
  | _ => error

def LoweringError.nextBranch (error : LoweringError) : LoweringError :=
  match error.path with
  | .matchBranch index :: rest => { error with path := .matchBranch (index + 1) :: rest }
  | _ => error

def LoweringError.nextRecBinding (error : LoweringError) : LoweringError :=
  match error.path with
  | .letRecRhs index :: rest => { error with path := .letRecRhs (index + 1) :: rest }
  | _ => error

def LoweringError.nextParameter (error : LoweringError) : LoweringError :=
  match error.site with
  | .parameterAnnotation index => { error with site := .parameterAnnotation (index + 1) }
  | _ => error
