import FHM.Bounds.RecursiveVariable
import FHM.Bounds.RecursiveCountTransport

/-! # One checked count instantiation for a full recursive application spine

Arguments retain derivations for their exact source expressions. Count proposals
are untrusted; accepting a spine uses the existing recursive variable rule once
and the ordinary application rule at EVERY frame. Every intermediate found HM
payload is checked. No source rewrite, HM instantiation or new typing rule.
-/

namespace FHM.Bounds.RecursiveSpine

open RecursiveTyping CountSubstitution RecursiveCountTransport

inductive Syntax : Expr → Type where
  | head (path : CorePath) (i : Nat) (hm : Ty) : Syntax (.found hm (.var i))
  | app {fn : Expr} (path : CorePath) (hm : Ty) (prior : Syntax fn) (arg : Expr) :
      Syntax (.found hm (.app fn arg))

def Syntax.index {e} : Syntax e → Nat
  | .head _ i _ => i
  | .app _ _ prior _ => prior.index

def Syntax.hm {e} : Syntax e → Ty
  | .head _ _ hm => hm
  | .app _ hm _ _ => hm

def Syntax.parse (path : CorePath) (e : Expr) : Option (Syntax e) :=
  match e with
  | .found hm (.var i) => some (.head path i hm)
  | .found hm (.app fn arg) => do
      let prior ← parse (path ++ [.appFun]) fn
      pure (.app path hm prior arg)
  | _ => none
termination_by sizeOf e

/-- Standalone polymorphic variables retain the walker's explicit restriction. -/
def parseApplication (path : CorePath) (e : Expr) : Option (Syntax e) :=
  match e with
  | .found hm (.app fn arg) => Syntax.parse path (.found hm (.app fn arg))
  | _ => none

structure Argument (ids : List Nat) (rows : Bindings) (caller : List Nat)
    (Δ : List Constraint) (env : List Binding) (e : Expr) where
  bounds : BoundsTy
  typing : Derives ids rows Δ env e.stripFound bounds
  scope : ScopedScheme.BoundsScoped caller bounds
  noGroups : NoGroups e.stripFound
  nodes : List Typed.NodeResult

inductive Checked (ids : List Nat) (rows : Bindings) (caller : List Nat)
    (Δ : List Constraint) (env : List Binding) : {e : Expr} → Syntax e → Type where
  | head (path : CorePath) (i : Nat) (hm : Ty) : Checked ids rows caller Δ env (.head path i hm)
  | app {fn : Expr} {prior : Syntax fn} {arg : Expr} (path : CorePath) (hm : Ty)
      (previous : Checked ids rows caller Δ env prior)
      (actual : Argument ids rows caller Δ env arg) :
      Checked ids rows caller Δ env (.app path hm prior arg)

/-- Accumulate in reverse once, avoiding repeated append during collection. -/
def Checked.actualsRev {ids rows caller Δ env e} {spine : Syntax e} :
    Checked ids rows caller Δ env spine → List BoundsTy
  | .head _ _ _ => []
  | .app _ _ previous actual => actual.bounds :: previous.actualsRev

theorem Checked.noGroups {ids rows caller Δ env e} {spine : Syntax e}
    (h : Checked ids rows caller Δ env spine) : NoGroups e.stripFound := by
  induction h with
  | head => simp [Expr.stripFound, NoGroups]
  | app _ _ _ actual ih => simpa only [Expr.stripFound, NoGroups] using And.intro ih actual.noGroups

structure Result (ids : List Nat) (rows : Bindings) (caller : List Nat)
    (Δ : List Constraint) (env : List Binding) {e : Expr} (spine : Syntax e) where
  bounds : BoundsTy
  typing : Derives ids rows Δ env e.stripFound bounds
  shape : Synth.BoundsTy.toTy bounds = spine.hm.eraseBounds
  scope : ScopedScheme.BoundsScoped caller bounds
  nodes : List Typed.NodeResult

/-- An absent argument has no invented bounds or typing evidence. -/
inductive Prepared (ids : List Nat) (rows : Bindings) (caller : List Nat)
    (Δ : List Constraint) (env : List Binding) : {e : Expr} → Syntax e → Type where
  | head (path : CorePath) (i : Nat) (hm : Ty) : Prepared ids rows caller Δ env (.head path i hm)
  | app {fn : Expr} {prior : Syntax fn} {arg : Expr} (path : CorePath) (hm : Ty)
      (previous : Prepared ids rows caller Δ env prior)
      (actual : Option (Argument ids rows caller Δ env arg)) :
      Prepared ids rows caller Δ env (.app path hm prior arg)

def Prepared.originsRev {ids rows caller Δ env e} {spine : Syntax e} :
    Prepared ids rows caller Δ env spine → List (Option BoundsTy)
  | .head _ _ _ => []
  | .app _ _ previous actual => actual.map (·.bounds) :: previous.originsRev

def Prepared.propose {ids rows caller Δ env e} {spine : Syntax e}
    (prepared : Prepared ids rows caller Δ env spine) : Except String (List Count) := do
  match env[spine.index]? with
  | some (.recursive c) =>
      CountProposal.proposeOrigins c.counts.quantified c.counts.body prepared.originsRev.reverse
  | _ => throw "bounds: recursive spine requires a declared recursive assumption"

/-- A completed spine contains evidence for every exact source argument. -/
structure Completed (ids : List Nat) (rows : Bindings) (caller : List Nat)
    (Δ : List Constraint) (env : List Binding) {e : Expr} (spine : Syntax e) where
  checked : Checked ids rows caller Δ env spine
  result : Result ids rows caller Δ env spine

/-- Extend an already checked callee without repeating its count instantiation. -/
def append {ids rows caller Δ env fn arg} {spine : Syntax fn}
    (path : CorePath) (hm : Ty) (prior : Result ids rows caller Δ env spine)
    (actual : Argument ids rows caller Δ env arg) :
    Except String (Result ids rows caller Δ env (.app path hm spine arg)) := do
  match hp : prior.bounds with
  | .arrow domain result =>
      let inclusion ← Typed.subtype Δ actual.bounds domain
      let shape ← match BinderBridge.equalTy (Synth.BoundsTy.toTy result) hm.eraseBounds with
        | none => throw "bounds: recursive spine result disagrees with intermediate found payload"
        | some h => pure h
      have functionTyping : Derives ids rows Δ env _ (.arrow domain result) :=
        by simpa only [hp] using prior.typing
      have scope : ScopedScheme.BoundsScoped caller (.arrow domain result) :=
        by simpa only [hp] using prior.scope
      have applied := Derives.app functionTyping actual.typing inclusion.down
      pure ⟨result, (by simpa only [Expr.stripFound] using applied),
        shape.down, scope.2,
        ⟨path, hm.eraseBounds, some result⟩ :: prior.nodes ++ actual.nodes⟩
  | _ => throw "bounds: recursive spine applies a non-function contract result"

def use {ids rows caller Δ env e} {spine : Syntax e}
    (checked : Checked ids rows caller Δ env spine) (args : List Count) :
    Except String (Result ids rows caller Δ env spine) := do
  match checked with
  | .head path i hm =>
      let callee ← RecursiveVariable.check ids rows Δ env i hm args caller
      pure ⟨callee.bounds, (by simpa only [Expr.stripFound] using callee.derivation),
        callee.shape, callee.countScope, [⟨path, hm.eraseBounds, some callee.bounds⟩]⟩
  | .app path hm previous actual =>
      let prior ← use previous args
      append path hm prior actual

/-- Conditional acceptance only. Whole-group introduction still requires all
    RHS certificates, and every recursive use keeps the group's fixed HM type. -/
def infer {ids rows caller Δ env e} {spine : Syntax e}
    (checked : Checked ids rows caller Δ env spine) :
    Except String (Result ids rows caller Δ env spine) := do
  match env[spine.index]? with
  | some (.recursive c) =>
      let args ← CountProposal.proposeArguments c.counts.quantified c.counts.body checked.actualsRev.reverse
      use checked args
  | _ => throw "bounds: recursive spine requires a declared recursive assumption"

#print axioms Checked.noGroups
#print axioms append
#print axioms use
#print axioms infer

end FHM.Bounds.RecursiveSpine
