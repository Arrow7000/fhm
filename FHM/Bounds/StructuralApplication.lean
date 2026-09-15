import FHM.Bounds.SchemeVariable

/-! Origin-backed structural application. Slot proposals come only from the
argument's certified bounds. They are untrusted until exact HM specialization,
local closure, count scope and semantic domain inclusion have all been checked.
Repeated slots use one proposal and may conservatively fail inclusion. Unused
slots receive Unit, never fabricated List bounds; mismatching HM uses reject.
This is not count-scheme inference or a completeness/principality algorithm. -/

namespace FHM.Bounds.StructuralApplication

open SchemeTyping

mutual
private def collect (pattern actual : BoundsTy) : Option (List (Nat × BoundsTy)) :=
  match pattern, actual with
  | .bvar i, β => some [(i, β)]
  | .prim _, .prim _ | .fvar _, .fvar _ => some []
  | .arrow a b, .arrow c d => do pure ((← collect a c) ++ (← collect b d))
  | .list _ _ a, .list _ _ b => collect a b
  | .custom n as, .custom m bs => if n = m then collectList as bs else none
  | _, _ => none
termination_by sizeOf pattern + sizeOf actual

private def collectList (as bs : List BoundsTy) : Option (List (Nat × BoundsTy)) :=
  match as, bs with
  | [], [] => some []
  | a :: as, b :: bs => do pure ((← collect a b) ++ (← collectList as bs))
  | _, _ => none
termination_by sizeOf as + sizeOf bs
end

/-- Untrusted complete HM-slot proposals from an argument's full bounds.
    This only collects structure: exact HM shape, local closure, caller scope
    and semantic domain inclusion must still be checked by the consumer. -/
def propose (pattern actual : BoundsTy) (arity : Nat) : Except String (List BoundsTy) := do
  let uses ← match collect pattern actual with
    | none => throw "bounds: unsupported structural argument bounds proposal"
    | some uses => pure uses
  pure ((List.range arity).map fun slot =>
    ((uses.find? (fun row => row.1 == slot)).map Prod.snd).getD (.prim .unit))

private def collectArguments (contract : BoundsTy) (actuals : List BoundsTy) :
    Option (List (Nat × BoundsTy)) :=
  match actuals with
  | [] => some []
  | actual :: rest =>
      match contract with
      | .arrow domain result => do
          pure ((← collect domain actual) ++ (← collectArguments result rest))
      | _ => none

private def occurrences : BoundsTy → List Nat
  | .prim _ | .fvar _ => []
  | .bvar i => [i]
  | .arrow a b => occurrences a ++ occurrences b
  | .list _ _ elem => occurrences elem
  | .custom _ args => args.flatMap occurrences

private def collectArgumentOrigins (contract : BoundsTy)
    (actuals : List (Option BoundsTy)) : Option (List (Nat × BoundsTy) × List Nat) :=
  match actuals with
  | [] => some ([], [])
  | actual :: rest =>
      match contract with
      | .arrow domain result => do
          let later ← collectArgumentOrigins result rest
          match actual with
          | some β => pure ((← collect domain β) ++ later.1, later.2)
          | none => pure (later.1, occurrences domain ++ later.2)
      | _ => none

/-- One untrusted HM vector for a whole supplied spine, including slots whose
    first actual origin is a later argument. Repeated slots keep their first
    proposal; EVERY domain still needs independent semantic inclusion. -/
def proposeArguments (contract : BoundsTy) (actuals : List BoundsTy) (arity : Nat) :
    Except String (List BoundsTy) := do
  let uses ← match collectArguments contract actuals with
    | some uses => pure uses
    | none => throw "bounds: unsupported full-spine HM proposal shape or excess arguments"
  pure ((List.range arity).map fun slot =>
    ((uses.find? (fun row => row.1 == slot)).map Prod.snd).getD (.prim .unit))

/-- Full-spine HM proposals may be gathered before every argument checks.  An
    absent argument contributes no proposal; every slot occurring there must be
    supplied independently by another actual argument.  Truly domain-absent
    slots retain the established `Unit` witness convention. -/
def proposeOrigins (contract : BoundsTy) (actuals : List (Option BoundsTy))
    (arity : Nat) : Except String (List BoundsTy) := do
  let (uses, blocked) ← match collectArgumentOrigins contract actuals with
    | some result => pure result
    | none => throw "bounds: unsupported staged HM argument proposal shape or excess arguments"
  (List.range arity).mapM fun slot =>
    match (uses.find? (fun row => row.1 == slot)).map Prod.snd with
    | some argument => pure argument
    | none =>
        if blocked.contains slot then
          throw "bounds: HM argument needs an independent origin before deferred argument checking"
        else pure (.prim .unit)

structure Result (Δ : List Constraint) (env : List Binding) (i : Nat) (arg : Expr)
    (functionHM resultHM : Ty) (scope : List Nat) where
  domain : BoundsTy
  bounds : BoundsTy
  functionTyping : Derives Δ env (.var i) (.arrow domain bounds)
  functionShape : Synth.BoundsTy.toTy (.arrow domain bounds) = functionHM.eraseBounds
  functionScope : ScopedScheme.BoundsScoped scope (.arrow domain bounds)
  derivation : Derives Δ env (.app (.var i) arg) bounds
  shape : Synth.BoundsTy.toTy bounds = resultHM.eraseBounds
  countScope : ScopedScheme.BoundsScoped scope bounds

def check (Δ : List Constraint) (env : List Binding) (i : Nat) (arg : Expr)
    (actual : BoundsTy) (typing : Derives Δ env arg actual)
    (functionHM resultHM : Ty) (scope : List Nat) :
    Except String (Result Δ env i arg functionHM resultHM scope) := do
  match lookup : env[i]? with
  | none => throw "bounds: polymorphic application variable outside environment"
  | some (.mono _) => throw "bounds: structural scheme application requires a polymorphic binding"
  | some (.poly s) =>
      match body : s.body with
      | .arrow pattern result =>
          let args ← propose pattern actual s.hm.paramCount
          let callee ← SchemeVariable.check Δ env i functionHM args scope
          have vb : callee.bounds = s.instantiate args := by
            rcases callee.selected with mono | ⟨selected, selectedAt, vb, _⟩
            · rw [lookup] at mono
              cases mono
            · rw [lookup] at selectedAt
              cases selectedAt
              exact vb
          let domain := TypeSubstitution.substitute (SchemeUse.vector args) pattern
          let bounds := TypeSubstitution.substitute (SchemeUse.vector args) result
          have fn : callee.bounds = .arrow domain bounds := by
            rw [vb, Scheme.instantiate, body]
            rfl
          let inclusion ← Typed.subtype Δ actual domain
          let shape ← match BinderBridge.equalTy (Synth.BoundsTy.toTy bounds) resultHM.eraseBounds with
            | none => throw "bounds: structural application result disagrees with found payload"
            | some shape => pure shape
          have fnTyping : Derives Δ env (.var i) (.arrow domain bounds) := by
            simpa only [fn] using callee.derivation
          have fnShape : Synth.BoundsTy.toTy (.arrow domain bounds) = functionHM.eraseBounds := by
            simpa only [fn] using callee.shape
          have fnScope : ScopedScheme.BoundsScoped scope (.arrow domain bounds) := by
            simpa only [fn] using callee.countScope
          pure ⟨domain, bounds, fnTyping, fnShape, fnScope,
            .app fnTyping typing inclusion.down, shape.down, fnScope.2⟩
      | _ => throw "bounds: polymorphic application has non-arrow scheme body"

#print axioms check

end FHM.Bounds.StructuralApplication
