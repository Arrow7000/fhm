import FHM.Unverified.HMDisplay

/-!
# Structured explanations for application errors

The verified worker supplies native failure data and logical Core paths.
This module only chooses presentation and authored source spans; it does not
rerun inference to reconstruct a failed application. Other native reasons are
rendered by the shared `Diagnostics` module.
-/

namespace FHM.Unverified.TypeDiagnostics

open SurfaceBridge.Provenance Surface.Span

inductive Reason where
  | argumentMismatch (expected actual : Ty)
  | namedArgumentMismatch (names : List String) (expected actual : Ty)
  | notFunction (actual : Ty)
  | infiniteType (varId : Nat) (within : Ty)
  | incompatibleApplication (functionType argumentType : Ty)
  deriving Repr

structure Error where
  path : CorePath
  reason : Reason
  deriving Repr

def Reason.code : Reason → String
  | .argumentMismatch .. | .namedArgumentMismatch .. => "type.argumentMismatch"
  | .notFunction .. => "type.notFunction"
  | .infiniteType .. => "type.infiniteType"
  | .incompatibleApplication .. => "type.incompatibleApplication"

/-- Choose application wording and the authored child that owns the failed
constraint. All type values and annotation names come from the native worker. -/
def applicationError (path : CorePath) (fnTy argTy : Ty) (names : List String)
    (failure : UnifyError) : Error :=
  match failure with
  | .occursCheck n within => ⟨path, .infiniteType n within⟩
  | _ => match fnTy with
    | .arrow expected _ =>
        let reason := if names.isEmpty then .argumentMismatch expected argTy
          else .namedArgumentMismatch names expected argTy
        ⟨path ++ [.appArg], reason⟩
    | .fvar _ => ⟨path, .incompatibleApplication fnTy argTy⟩
    | _ => ⟨path ++ [.appFun], .notFunction fnTy⟩

/-- Keep type values and location separate from human-facing wording. -/
def Reason.message (reason : Reason) : String :=
  let types := match reason with
    | .argumentMismatch a b | .namedArgumentMismatch _ a b | .incompatibleApplication a b => [a, b]
    | .notFunction a => [a]
    | .infiniteType n a => [.fvar n, a]
  let display : FHM.Unverified.HMDisplay.Context := {
    freeIds := (types.flatMap Ty.freeVars).eraseDups
  }
  let pretty := FHM.Unverified.HMDisplay.pretty display
  match reason with
  | .argumentMismatch expected actual =>
      s!"type mismatch: expected {pretty expected}, got {pretty actual}"
  | .namedArgumentMismatch names expected actual =>
      let labels := String.intercalate ", " (names.map ("?" ++ ·))
      s!"type mismatch: expected {pretty expected}, got {pretty actual}; repeated names ({labels}) each keep one type within this parameter annotation"
  | .notFunction actual => s!"cannot apply a value of type {pretty actual} as a function"
  | .infiniteType n within =>
      s!"infinite type: {pretty (.fvar n)} would have to equal {pretty within}"
  | .incompatibleApplication fn arg =>
      s!"cannot apply a value of type {pretty fn} to an argument of type {pretty arg}"

/-- Render a native rejection at an authored source origin. Generated lowering
nodes may share an owner's span, so those origins retain the existing fallback. -/
def explain (failure : InferError) (lowered : InputLowered) : Option (Reason × Span) := do
  let error ← match failure.reason with
    | .application fn arg names cause => some (applicationError failure.path fn arg names cause)
    | .unification (.occursCheck n within) => some ⟨failure.path, .infiniteType n within⟩
    | _ => none
  let origin ← (lowered.coreOrigins.find? fun p => p.1 == error.path).map (·.2)
  if origin.kind == .authored then some (error.reason, origin.source.span) else none

end FHM.Unverified.TypeDiagnostics
