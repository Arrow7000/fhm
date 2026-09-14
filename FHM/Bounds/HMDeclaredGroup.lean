import FHM.Bounds.HMDeclaredRHS
import FHM.Bounds.RecursiveHMEnvironment

/-! Ordered acceptance of every original annotated RHS in one recursive group.
Opaque HM slot vectors are explicit checked proposals, not inferred binder facts.
Shared solved identities must agree at HM shape; member count payloads need not.
Every actual RHS is universally signed in the SAME recursive environment.
This assembles RHS obligations, not generalized export or group-body typing. -/

namespace FHM.Bounds.HMDeclaredGroup

open HMDeclaredReconciliation RecursiveHMJudgement

abbrev Member (output : Expr) (metadata : Scope.Metadata) (path : CorePath)
    (index : Nat) (captures : List Nat) (premises : List Constraint) (typeCaptures : List Ty) :=
  HMDeclaredRHS.Prepared output metadata (.letRec path index) captures premises typeCaptures

def Member.contract {output metadata path index captures premises typeCaptures}
    (p : Member output metadata path index captures premises typeCaptures) : Contract :=
  ⟨p.reconciled.interface.scheme, _, RecursiveHMContract.fromOpaque p.reconciled.opening⟩

/-- Exact sequential source indices prevent silently omitting or swapping RHSs. -/
inductive Interfaces (output : Expr) (metadata : Scope.Metadata) (path : CorePath)
    (captures : List Nat) (premises : List Constraint) (typeCaptures : List Ty) :
    Nat → List (List Nat) → Type where
  | nil {index} : Interfaces output metadata path captures premises typeCaptures index []
  | cons {index ids rest} (p : Member output metadata path index captures premises typeCaptures) :
      p.reconciled.signatureIds = ids →
      Interfaces output metadata path captures premises typeCaptures (index + 1) rest →
      Interfaces output metadata path captures premises typeCaptures index (ids :: rest)

namespace Interfaces

def contracts {output metadata path captures premises typeCaptures index vectors}
    (ps : Interfaces output metadata path captures premises typeCaptures index vectors) : List Contract :=
  match ps with
  | .nil => []
  | .cons p _ rest => p.contract :: rest.contracts

def quantified {output metadata path captures premises typeCaptures index vectors}
    (ps : Interfaces output metadata path captures premises typeCaptures index vectors) : List Nat :=
  match ps with
  | .nil => []
  | .cons p _ rest => p.quantified ++ rest.quantified

def proposals {output metadata path captures premises typeCaptures index vectors}
    (ps : Interfaces output metadata path captures premises typeCaptures index vectors) : List (Nat × Ty) :=
  match ps with
  | .nil => []
  | .cons p _ rest =>
      p.reconciled.flexible.map (fun i => (i, Synth.BoundsTy.toTy (p.reconciled.interpretation i))) ++ rest.proposals

theorem length {output metadata path captures premises typeCaptures index vectors}
    (ps : Interfaces output metadata path captures premises typeCaptures index vectors) :
    ps.contracts.length = vectors.length := by
  induction ps with
  | nil => rfl
  | cons _ _ _ ih => simpa [contracts] using ih

end Interfaces

private def prepareMembers (output : Expr) (metadata : Scope.Metadata) (path : CorePath)
    (captures : List Nat) (premises : List Constraint) (typeCaptures : List Ty)
    (index : Nat) (vectors : List (List Nat)) :
    Except String (Interfaces output metadata path captures premises typeCaptures index vectors) := do
  match vectors with
  | [] => pure .nil
  | ids :: rest =>
      let p ← HMDeclaredRHS.prepare output metadata (.letRec path index) ids captures typeCaptures premises
      let tail ← prepareMembers output metadata path captures premises typeCaptures (index + 1) rest
      if he : p.reconciled.signatureIds = ids then pure (.cons p he tail)
      else throw "bounds: recursive member changed its proposed opaque HM coordinates"

def Consistent (rows : List (Nat × Ty)) : Prop :=
  ∀ a ∈ rows, ∀ b ∈ rows, a.1 = b.1 → a.2 = b.2

private def checkPair (a b : Nat × Ty) : Except String (PLift (a.1 = b.1 → a.2 = b.2)) :=
  if hi : a.1 = b.1 then
    match BinderBridge.equalTy a.2 b.2 with
    | some h => .ok ⟨fun _ => h.down⟩
    | none => .error "bounds: recursive members disagree on a shared solved HM identity"
  else .ok ⟨fun h => (hi h).elim⟩

private def checkRow (a : Nat × Ty) (rows : List (Nat × Ty)) :
    Except String (PLift (∀ b ∈ rows, a.1 = b.1 → a.2 = b.2)) := do
  match rows with
  | [] => pure ⟨by simp⟩
  | b :: rest =>
      let head ← checkPair a b
      let tail ← checkRow a rest
      pure ⟨by
        intro c hc
        rcases List.mem_cons.mp hc with rfl | ht
        · exact head.down
        · exact tail.down c ht⟩

def checkConsistent (rows : List (Nat × Ty)) : Except String (PLift (Consistent rows)) := do
  match rows with
  | [] => pure ⟨by simp [Consistent]⟩
  | a :: rest =>
      let head ← checkRow a rest
      let tail ← checkConsistent rest
      pure ⟨by
        intro b hb c hc hbc
        rcases List.mem_cons.mp hb with hab | hb
        · cases hab
          rcases List.mem_cons.mp hc with hca | hc
          · cases hca; rfl
          · exact head.down c hc hbc
        · rcases List.mem_cons.mp hc with hca | hc
          · cases hca; exact (head.down b hb hbc.symm).symm
          · exact tail.down b hb c hc hbc⟩

private def checkMemberTy (t : Ty) (ts : List Ty) : Except String (PLift (t ∈ ts)) := do
  match ts with
  | [] => throw "bounds: common recursive template is missing from protected type captures"
  | a :: rest =>
      match BinderBridge.equalTy t a with
      | some h => pure ⟨by simp [h.down]⟩
      | none =>
          let tail ← checkMemberTy t rest
          pure ⟨List.mem_cons_of_mem a tail.down⟩

private def checkRepresentedHead (ts : List Ty) (b : Binding) :
    Except String (PLift (∀ c, .recursive c = b → c.template.hm.body ∈ ts)) := do
  match b with
  | .mono _ => pure ⟨by intro c hc; cases hc⟩
  | .recursive c =>
      let h ← checkMemberTy c.template.hm.body ts
      pure ⟨by intro d hd; cases hd; exact h.down⟩

private def checkRepresented (ts : List Ty) (env : List Binding) :
    Except String (PLift (∀ c, .recursive c ∈ env → c.template.hm.body ∈ ts)) := do
  match env with
  | [] => pure ⟨by simp⟩
  | b :: rest =>
      let head ← checkRepresentedHead ts b
      let tail ← checkRepresented ts rest
      pure ⟨by
        intro c hc
        rcases List.mem_cons.mp hc with hb | ht
        · exact head.down c hb
        · exact tail.down c ht⟩

private def checkCountFreshHead (q : List Nat) (b : Binding) :
    Except String (PLift (∀ c, .recursive c = b → ∀ i ∈ c.template.counts.captures, i ∉ q)) :=
  match b with
  | .mono _ => .ok ⟨by intro c hc; cases hc⟩
  | .recursive c =>
      if h : c.template.counts.captures.all (fun i => !q.contains i) = true then
        .ok ⟨by
          intro d hd i hi
          cases hd
          simpa [List.contains_iff_mem] using List.all_eq_true.mp h i hi⟩
      else .error "bounds: common recursive template captures a member-local count"

private def checkCountFresh (q : List Nat) (env : List Binding) :
    Except String (PLift (∀ c, .recursive c ∈ env → ∀ i ∈ c.template.counts.captures, i ∉ q)) := do
  match env with
  | [] => pure ⟨by simp⟩
  | b :: rest =>
      let head ← checkCountFreshHead q b
      let tail ← checkCountFresh q rest
      pure ⟨by
        intro c hc
        rcases List.mem_cons.mp hc with hb | ht
        · exact head.down c hb
        · exact tail.down c ht⟩

structure MemberChecked {output metadata path index captures premises typeCaptures}
    (p : Member output metadata path index captures premises typeCaptures) (env : List Binding) where
  rhs : HMDeclaredRHS.Checked p.reconciled env
  stable : RecursiveHMEnvironment.TypesFixed p.reconciled.interpretation env
  represented : ∀ c, .recursive c ∈ env → c.template.hm.body ∈ typeCaptures
  countFresh : ∀ c, .recursive c ∈ env → ∀ i ∈ c.template.counts.captures, i ∉ p.quantified
  captured : RecursiveHMEnvironment.Captured captures env

/-- The certificate's environment is definitionally the common group env at
    the API boundary, not a separately interpreted environment for each RHS. -/
def MemberChecked.certificate {output metadata path index captures premises typeCaptures env}
    {p : Member output metadata path index captures premises typeCaptures} (checked : MemberChecked p env) :
    RecursiveHMSigned.Certified p.declaration.annotation p.quantified captures premises
      (ScopedHMInterpretation.AtNode.view p.declaration.node p.reconciled.interpretation BoundsTy.bvar)
      (p.declaration.node.original :: guardedTypes p.declaration typeCaptures)
      env p.declaration.node.inner.stripFound p.reconciled.interpretation BoundsTy.bvar := by
  have h := HMDeclaredRHS.certify p.reconciled checked.rhs checked.represented checked.countFresh
  have he := RecursiveHMEnvironment.typesFixed p.reconciled.interpretationLC checked.stable
  simpa only [he, slotsFor] using h

inductive CheckedMembers {output metadata path captures premises typeCaptures}
    (env : List Binding) : {index : Nat} → {vectors : List (List Nat)} →
    Interfaces output metadata path captures premises typeCaptures index vectors → Type where
  | nil {index} : CheckedMembers env (Interfaces.nil (index := index))
  | cons {index ids rest} {p : Member output metadata path index captures premises typeCaptures}
      {tail : Interfaces output metadata path captures premises typeCaptures (index + 1) rest}
      {he : p.reconciled.signatureIds = ids} :
      MemberChecked p env → CheckedMembers env tail → CheckedMembers env (Interfaces.cons p he tail)

private def checkMembers {output metadata path captures premises typeCaptures index vectors}
    (ps : Interfaces output metadata path captures premises typeCaptures index vectors)
    (env : List Binding) (schemes : BinderSchemeMap) : Except String (CheckedMembers env ps) := do
  match ps with
  | .nil => pure .nil
  | .cons p _ rest =>
      let stable ← RecursiveHMEnvironment.checkTypesFixed p.reconciled.interpretation env
      let represented ← checkRepresented typeCaptures env
      let countFresh ← checkCountFresh p.quantified env
      let captured ← RecursiveHMEnvironment.checkCaptured captures env
      let rhs ← HMDeclaredRHS.check p.reconciled env schemes
      let tail ← checkMembers rest env schemes
      pure (.cons ⟨rhs, stable.down, represented.down, countFresh.down, captured.down⟩ tail)

structure Checked (output : Expr) (metadata : Scope.Metadata) (path : CorePath)
    (vectors : List (List Nat)) (captures : List Nat) (premises : List Constraint)
    (outerTypes : List Ty) (outerEnv : List Binding) where
  originalHM : Ty
  annotations : List (Option PolyTy)
  rhss : List Expr
  body : Expr
  source : output.atCorePath path = some (.found originalHM (.letRec annotations rhss body))
  resolved : metadata.problems.isEmpty = true
  arity : annotations.length = rhss.length
  complete : vectors.length = rhss.length
  interfaces : Interfaces output metadata path captures premises
    (annotations.filterMap (fun a => a.map (fun s => s.body.eraseBounds)) ++ outerTypes) 0 vectors
  distinctCounts : interfaces.quantified.Nodup
  independentCaptures : ∀ i ∈ captures, i ∉ interfaces.quantified
  agreement : Consistent interfaces.proposals
  members : CheckedMembers (interfaces.contracts.map Binding.recursive ++ outerEnv) interfaces

theorem Checked.memberCount {output metadata path vectors captures premises outerTypes outerEnv}
    (g : Checked output metadata path vectors captures premises outerTypes outerEnv) :
    g.interfaces.contracts.length = g.rhss.length :=
  g.interfaces.length.trans g.complete

/-- All source members accept or the entire result rejects. Explicit per-member
    opaque vectors may have different arities; no machine schemes are invented.
    This entry point deliberately does NOT accept or export the group's body. -/
def check (output : Expr) (metadata : Scope.Metadata) (path : CorePath)
    (vectors : List (List Nat)) (captures : List Nat := []) (premises : List Constraint := [])
    (outerTypes : List Ty := []) (outerEnv : List Binding := []) (schemes : BinderSchemeMap := []) :
    Except String (Checked output metadata path vectors captures premises outerTypes outerEnv) := do
  if hp : metadata.problems.isEmpty = true then
   match hs : output.atCorePath path with
  | some (.found hm (.letRec anns rhss body)) =>
      if ha : anns.length = rhss.length then
        if hv : vectors.length = rhss.length then
          let guarded := anns.filterMap (fun a => a.map (fun s => s.body.eraseBounds)) ++ outerTypes
          let ps ← prepareMembers output metadata path captures premises guarded 0 vectors
          if hq : ps.quantified.Nodup then
            if hc : captures.all (fun i => !ps.quantified.contains i) = true then
              let agreement ← checkConsistent ps.proposals
              let checked ← checkMembers ps (ps.contracts.map Binding.recursive ++ outerEnv) schemes
              pure ⟨hm, anns, rhss, body, hs, hp, ha, hv, ps, hq,
                (fun i hi => by simpa [List.contains_iff_mem] using List.all_eq_true.mp hc i hi),
                agreement.down, checked⟩
            else throw "bounds: common captures overlap recursive member count telescopes"
          else throw "bounds: recursive member count telescopes overlap"
        else throw "bounds: recursive opaque vector/RHS arity mismatch"
      else throw "bounds: recursive annotation/RHS arity mismatch"
  | _ => throw "bounds: requested source path is not a found recursive group"
  else throw "bounds: unresolved or duplicate count scope in recursive group metadata"

#print axioms checkConsistent
#print axioms MemberChecked.certificate
#print axioms Checked.memberCount
#print axioms check

end FHM.Bounds.HMDeclaredGroup
