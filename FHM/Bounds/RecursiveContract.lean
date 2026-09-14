import FHM.Bounds.HMCountScheme

/-! # Declared assumptions for recursive count-polymorphic calls

A recursive assumption is not an RHS certificate. Its HM monotype is fixed for
the entire group: no HM argument array or HM instantiation rule exists here.
Only the declared count telescope may be instantiated, with scoped finite Nat
arguments and independently discharged premises. Group acceptance must prove
every implementation meets these assumptions before exporting any result.

The group decoder still accepts monomorphic HM annotations only. `decodeOpaque`
certifies a genuinely polymorphic interface at explicit fixed HM identities, but
its universal RHS/annotation/group introduction remains separate work. Annotation
quantifiers must never be reopened independently at recursive calls.
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

/-- Retain the closed interface alongside its one fixed opaque opening. This
    is still an assumption certificate, not a polymorphic RHS/group proof. -/
structure Opaque (found : Ty) (typeCaptures : List Ty) where
  template : HMCountScheme.Scheme
  opening : HMCountScheme.Opening template found typeCaptures

def Opaque.declared {found typeCaptures} (o : Opaque found typeCaptures) : Declared :=
  ⟨found.eraseBounds, o.opening.counts, o.opening.wf, o.opening.shape, o.opening.lc⟩

/-- Identities are supplied explicitly and checked against the fixed HM
    artifact. This API never opens quantifiers independently at recursive uses. -/
def decodeOpaque (annotation : PolyTy) (found : Ty) (ids quantified captures : List Nat)
    (typeCaptures : List Ty) (premises : List Constraint := []) :
    Except String (Opaque found typeCaptures) := do
  let template ← HMCountScheme.decode annotation quantified captures premises
  let opening ← HMCountScheme.openFixed template found ids typeCaptures
  pure ⟨template, opening⟩

/-- Decoding authorizes an assumption interface, NOT acceptance of an RHS or
    group. The source signature must agree with the actual fixed found type. -/
def decode (annotation : PolyTy) (found : Ty) (quantified captures : List Nat)
    (premises : List Constraint := []) : Except String Declared := do
  unless annotation.paramCount = 0 do
    throw "bounds: fixed opening of polymorphic recursive annotation not yet supported"
  if found.eraseBounds.bvarsBelow 0 then
    pure (← decodeOpaque annotation found [] quantified captures [] premises).declared
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
#print axioms decodeOpaque
#print axioms Opaque.declared
#print axioms Use.shape
#print axioms check

end FHM.Bounds.RecursiveContract
