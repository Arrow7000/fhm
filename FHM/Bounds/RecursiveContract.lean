import FHM.Bounds.ScopedAnnotation
import FHM.Bounds.BinderBridge

/-! # Declared assumptions for recursive count-polymorphic calls

A recursive assumption is not an RHS certificate. Its HM monotype is fixed for
the entire group: no HM argument array or HM instantiation rule exists here.
Only the declared count telescope may be instantiated, with scoped finite Nat
arguments and independently discharged premises. Group acceptance must prove
every implementation meets these assumptions before exporting any result.

The initial decoder accepts monomorphic HM annotations only. Opening a genuinely
polymorphic annotation at its group's fixed HM identities remains separate work;
annotation quantifiers must never be reopened independently at recursive calls.
Exact annotation/found alignment is required in this slice; valid HM artifacts
whose RHS remains more general than the carried signature explicitly defer.
-/

namespace FHM.Bounds.RecursiveContract

structure Declared where
  hm : Ty
  counts : ScopedScheme.Scheme
  wf : counts.WF
  shape : Synth.BoundsTy.toTy counts.body = hm
  lc : hm.IsLC

/-- Decoding authorizes an assumption interface, NOT acceptance of an RHS or
    group. The source signature must agree with the actual fixed found type. -/
def decode (annotation : PolyTy) (found : Ty) (quantified captures : List Nat)
    (premises : List Constraint := []) : Except String Declared := do
  unless annotation.paramCount = 0 do
    throw "bounds: fixed opening of polymorphic recursive annotation not yet supported"
  let source ← ScopedAnnotation.contract quantified captures premises annotation.body
  let shape ← match BinderBridge.equalTy annotation.body.eraseBounds found.eraseBounds with
    | none => throw "bounds: recursive annotation needs specialization or disagrees with fixed HM monotype"
    | some shape => pure shape
  if hlc : found.eraseBounds.bvarsBelow 0 = true then
    pure ⟨found.eraseBounds, source.scheme, source.wf,
      source.shape.trans shape.down, (Ty.bvarsBelow_iff found.eraseBounds).mp hlc⟩
  else throw "bounds: recursive HM monotype contains an enclosing bound slot"

structure Use (c : Declared) (Δ : List Constraint) (found : Ty) (caller : List Nat) where
  args : List Count
  inst : ScopedScheme.Instance c.counts args caller
  usable : inst.Usable Δ
  fixedHM : c.hm = found.eraseBounds

def Use.bounds {c Δ found caller} (u : Use c Δ found caller) : BoundsTy := u.inst.bounds

/-- Count uses preserve the one fixed HM type, including all free identities. -/
theorem Use.shape {c Δ found caller} (u : Use c Δ found caller) :
    Synth.BoundsTy.toTy u.bounds = found.eraseBounds :=
  u.inst.shape.trans (c.shape.trans u.fixedHM)

theorem Use.inScope {c Δ found caller} (u : Use c Δ found caller) :
    ScopedScheme.BoundsScoped caller u.bounds := u.inst.bodyScoped

def check (c : Declared) (Δ : List Constraint) (found : Ty) (args : List Count)
    (caller : List Nat) : Except String (Use c Δ found caller) := do
  let inst ← c.counts.instantiate args caller
  let usable ← inst.checkPremises Δ
  let fixed ← match BinderBridge.equalTy c.hm found.eraseBounds with
    | none => throw "bounds: recursive use changes the group's fixed HM monotype"
    | some h => pure h
  pure ⟨args, inst, usable.down, fixed.down⟩

#print axioms decode
#print axioms Use.shape
#print axioms check

end FHM.Bounds.RecursiveContract
