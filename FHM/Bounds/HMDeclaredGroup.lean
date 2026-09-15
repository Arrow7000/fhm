import FHM.Bounds.HMDeclaredRHS
import FHM.Bounds.RecursiveHMEnvironment
import FHM.Bounds.RecursiveHMCaller

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

/-- Metadata-only preparation for checked coordinate proposals. Actual RHS
    acceptance still requires `check`; this function licenses no assumptions. -/
def prepareInterfaces (output : Expr) (metadata : Scope.Metadata) (path : CorePath)
    (captures : List Nat) (premises : List Constraint) (typeCaptures : List Ty)
    (index : Nat) (vectors : List (List Nat)) :
    Except String (Interfaces output metadata path captures premises typeCaptures index vectors) := do
  match vectors with
  | [] => pure .nil
  | ids :: rest =>
      let p ← HMDeclaredRHS.prepare output metadata (.letRec path index) ids captures typeCaptures premises
      let tail ← prepareInterfaces output metadata path captures premises typeCaptures (index + 1) rest
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
  | .exported _ => pure ⟨by intro c hc; cases hc⟩

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

private def checkExportRepresentedHead (ts : List Ty) (b : Binding) :
    Except String (PLift (∀ s, .exported s = b → s.hm.body ∈ ts)) := do
  match b with
  | .mono _ => pure ⟨by intro s hs; cases hs⟩
  | .recursive _ => pure ⟨by intro s hs; cases hs⟩
  | .exported s =>
      let h ← checkMemberTy s.hm.body ts
      pure ⟨by intro t ht; cases ht; exact h.down⟩

private def checkExportRepresented (ts : List Ty) (env : List Binding) :
    Except String (PLift (∀ s, .exported s ∈ env → s.hm.body ∈ ts)) := do
  match env with
  | [] => pure ⟨by simp⟩
  | b :: rest =>
      let head ← checkExportRepresentedHead ts b
      let tail ← checkExportRepresented ts rest
      pure ⟨by
        intro s hs
        rcases List.mem_cons.mp hs with hb | ht
        · exact head.down s hb
        · exact tail.down s ht⟩

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
  | .exported _ => .ok ⟨by intro c hc; cases hc⟩

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

private def checkExportCountFreshHead (q : List Nat) (b : Binding) :
    Except String (PLift (∀ s, .exported s = b → ∀ i ∈ s.counts.captures, i ∉ q)) :=
  match b with
  | .mono _ => .ok ⟨by intro s hs; cases hs⟩
  | .recursive _ => .ok ⟨by intro s hs; cases hs⟩
  | .exported s =>
      if h : s.counts.captures.all (fun i => !q.contains i) = true then
        .ok ⟨by
          intro t ht i hi
          cases ht
          simpa [List.contains_iff_mem] using List.all_eq_true.mp h i hi⟩
      else .error "bounds: exported scheme captures a member-local count"

private def checkExportCountFresh (q : List Nat) (env : List Binding) :
    Except String (PLift (∀ s, .exported s ∈ env → ∀ i ∈ s.counts.captures, i ∉ q)) := do
  match env with
  | [] => pure ⟨by simp⟩
  | b :: rest =>
      let head ← checkExportCountFreshHead q b
      let tail ← checkExportCountFresh q rest
      pure ⟨by
        intro s hs
        rcases List.mem_cons.mp hs with hb | ht
        · exact head.down s hb
        · exact tail.down s ht⟩

structure MemberChecked {output metadata path index captures premises typeCaptures}
    (p : Member output metadata path index captures premises typeCaptures) (env : List Binding) where
  rhs : HMDeclaredRHS.Checked p.reconciled env
  stable : RecursiveHMEnvironment.TypesFixed p.reconciled.interpretation env
  represented : ∀ c, .recursive c ∈ env → c.template.hm.body ∈ typeCaptures
  exportsRepresented : ∀ s, .exported s ∈ env → s.hm.body ∈ typeCaptures
  countFresh : ∀ c, .recursive c ∈ env → ∀ i ∈ c.template.counts.captures, i ∉ p.quantified
  exportCountFresh : ∀ s, .exported s ∈ env → ∀ i ∈ s.counts.captures, i ∉ p.quantified
  captured : RecursiveHMEnvironment.Captured captures env

/-- The certificate's environment is definitionally the common group env at
    the API boundary, not a separately interpreted environment for each RHS. -/
def MemberChecked.certificate {output metadata path index captures premises typeCaptures env}
    {p : Member output metadata path index captures premises typeCaptures} (checked : MemberChecked p env) :
    RecursiveHMSigned.Certified p.declaration.annotation p.quantified captures premises
      (ScopedHMInterpretation.AtNode.view p.declaration.node p.reconciled.interpretation BoundsTy.bvar)
      (p.declaration.node.original :: guardedTypes p.declaration typeCaptures)
      env p.declaration.node.inner.stripFound p.reconciled.interpretation BoundsTy.bvar := by
  let h := HMDeclaredRHS.certify p.reconciled checked.rhs checked.represented
    checked.exportsRepresented checked.countFresh checked.exportCountFresh
  have he := RecursiveHMEnvironment.typesFixed p.reconciled.interpretationLC checked.stable
  -- Preserve source/template/opening data definitionally. Only the proof
  -- fields mentioning the environment need transport; casting the entire
  -- certificate hides otherwise stable projections behind an equality recursor.
  refine ⟨p.reconciled.interface, {
    opening := p.reconciled.opening
    actual := h.implementation.actual
    shape := h.implementation.shape
    actualScope := h.implementation.actualScope
    inclusion := h.implementation.inclusion
    typing := ?_
    typeFresh := ?_
    exportTypeFresh := ?_
    countFresh := ?_
    exportCountFresh := ?_ }⟩
  · simpa only [he, slotsFor] using h.implementation.typing
  · simpa only [he] using h.implementation.typeFresh
  · simpa only [he] using h.implementation.exportTypeFresh
  · simpa only [he] using h.implementation.countFresh
  · simpa only [he] using h.implementation.exportCountFresh

theorem MemberChecked.certificateScheme {output metadata path index captures premises typeCaptures env}
    {p : Member output metadata path index captures premises typeCaptures} (checked : MemberChecked p env) :
    checked.certificate.interface.scheme = p.contract.template := by
  rfl

theorem MemberChecked.certificateOpeningIds {output metadata path index captures premises typeCaptures env}
    {p : Member output metadata path index captures premises typeCaptures} (checked : MemberChecked p env) :
    checked.certificate.implementation.opening.ids = p.reconciled.opening.ids := by
  rfl

/-- Readiness comes from the actual source RHS traversal and survives the same
    common-environment reconciliation as its universal implementation proof.
    Absence preserves static acceptance but does not certify runtime safety. -/
def MemberChecked.runtimeReady {output metadata path index captures premises typeCaptures env}
    {p : Member output metadata path index captures premises typeCaptures} (checked : MemberChecked p env) :
    Option (PLift (RecursiveHMJudgement.ScopedDerives.RuntimeReady checked.certificate.implementation.typing)) := do
  let ready ← checked.rhs.located.typed.runtimeReady
  pure ⟨by
    have he := RecursiveHMEnvironment.typesFixed p.reconciled.interpretationLC checked.stable
    simpa only [MemberChecked.certificate, HMDeclaredRHS.certify,
      RecursiveHMUniversal.fromScopedChecked, he, slotsFor] using ready.down⟩

#print axioms MemberChecked.runtimeReady

inductive CheckedMembers {output metadata path captures premises typeCaptures}
    (env : List Binding) : {index : Nat} → {vectors : List (List Nat)} →
    Interfaces output metadata path captures premises typeCaptures index vectors → Type where
  | nil {index} : CheckedMembers env (Interfaces.nil (index := index))
  | cons {index ids rest} {p : Member output metadata path index captures premises typeCaptures}
      {tail : Interfaces output metadata path captures premises typeCaptures (index + 1) rest}
      {he : p.reconciled.signatureIds = ids} :
      MemberChecked p env → CheckedMembers env tail → CheckedMembers env (Interfaces.cons p he tail)

/-- Generalized exit interfaces come from the exact declarations whose actual
    RHSs ALL accepted. Annotated members deliberately have no fabricated machine
    binder fact; inferred/unannotated exports need their separate machine path. -/
def CheckedMembers.exports {output metadata path captures premises typeCaptures env index vectors}
    {ps : Interfaces output metadata path captures premises typeCaptures index vectors}
    (ms : CheckedMembers env ps) : List HMCountScheme.Scheme :=
  match ms with
  | .nil => []
  | .cons head rest => head.certificate.interface.scheme :: rest.exports

theorem CheckedMembers.exportCount {output metadata path captures premises typeCaptures env index vectors}
    {ps : Interfaces output metadata path captures premises typeCaptures index vectors}
    (ms : CheckedMembers env ps) : ms.exports.length = ps.contracts.length := by
  induction ms with
  | nil => rfl
  | cons _ _ ih => simpa [exports, Interfaces.contracts] using ih

/-- The exit position, source declaration and universal implementation are
    selected together. A successful lookup cannot swap the signature/RHS pair. -/
structure Selected {output metadata path captures premises typeCaptures env index vectors}
    {ps : Interfaces output metadata path captures premises typeCaptures index vectors}
    (ms : CheckedMembers env ps) (offset : Nat) where
  sourceIndex : Nat
  member : Member output metadata path sourceIndex captures premises typeCaptures
  rhs : MemberChecked member env
  position : sourceIndex = index + offset
  selection : ms.exports[offset]? = some rhs.certificate.interface.scheme
  contractSelection : ps.contracts[offset]? = some member.contract

/-- Total proof-side selection at a valid exit position. The source member,
    actual RHS certificate, generalized export and fixed recursive contract
    are selected together; outside-the-group rejection remains in `select`. -/
def CheckedMembers.memberAt {output metadata path captures premises typeCaptures env index vectors}
    {ps : Interfaces output metadata path captures premises typeCaptures index vectors}
    (ms : CheckedMembers env ps) (offset : Nat) (inside : offset < ms.exports.length) : Selected ms offset :=
  match ms, offset with
  | .nil, _ => False.elim (by simp [CheckedMembers.exports] at inside)
  | .cons (p := p) head _, 0 => ⟨index, p, head, by simp, rfl, rfl⟩
  | .cons _ rest, offset + 1 =>
      let tail := rest.memberAt offset (by simpa [CheckedMembers.exports] using inside)
      ⟨tail.sourceIndex, tail.member, tail.rhs, by have h := tail.position; omega,
        tail.selection, tail.contractSelection⟩

/-- Collect runtime evidence for every member, never just the demanded export.
    This consumes witnesses built by the existing RHS checker, without another
    traversal, constraint check or acceptance rule. -/
def CheckedMembers.runtimeReady {output metadata path captures premises typeCaptures env index vectors}
    {ps : Interfaces output metadata path captures premises typeCaptures index vectors}
    (ms : CheckedMembers env ps) :
    Option (PLift (∀ offset (inside : offset < ms.exports.length),
      RecursiveHMJudgement.ScopedDerives.RuntimeReady (ms.memberAt offset inside).rhs.certificate.implementation.typing ∧
      Runtime.Supported (ms.memberAt offset inside).rhs.certificate.implementation.opening.bounds)) :=
  match ms with
  | .nil => some ⟨by intro offset inside; simp [CheckedMembers.exports] at inside⟩
  | .cons checked rest => do
      let head ← checked.runtimeReady
      let demand ← Runtime.supported? checked.certificate.implementation.opening.bounds
      let tail ← rest.runtimeReady
      pure ⟨by
        intro offset inside
        cases offset with
        | zero => exact ⟨head.down, demand.down⟩
        | succ offset => exact tail.down offset (by
            simp only [CheckedMembers.exports, List.length_cons] at inside
            omega)⟩

#print axioms CheckedMembers.runtimeReady

def CheckedMembers.select {output metadata path captures premises typeCaptures env index vectors}
    {ps : Interfaces output metadata path captures premises typeCaptures index vectors}
    (ms : CheckedMembers env ps) (offset : Nat) : Except String (Selected ms offset) := do
  match ms, offset with
  | .nil, _ => throw "bounds: binding is outside the exported recursive group"
  | .cons (p := p) head _, 0 => pure ⟨index, p, head, by simp, rfl, rfl⟩
  | .cons _ rest, offset + 1 =>
      let tail ← rest.select offset
      pure ⟨tail.sourceIndex, tail.member, tail.rhs, by
        have h := tail.position
        omega, tail.selection, tail.contractSelection⟩

private def checkMembers {output metadata path captures premises typeCaptures index vectors}
    (ps : Interfaces output metadata path captures premises typeCaptures index vectors)
    (env : List Binding) (schemes : BinderSchemeMap) : Except String (CheckedMembers env ps) := do
  match ps with
  | .nil => pure .nil
  | .cons p _ rest =>
      let stable ← RecursiveHMEnvironment.checkTypesFixed p.reconciled.interpretation env
      let represented ← checkRepresented typeCaptures env
      let exportsRepresented ← checkExportRepresented typeCaptures env
      let countFresh ← checkCountFresh p.quantified env
      let exportCountFresh ← checkExportCountFresh p.quantified env
      let captured ← RecursiveHMEnvironment.checkCaptured captures env
      let rhs ← HMDeclaredRHS.check p.reconciled env schemes
      let tail ← checkMembers rest env schemes
      pure (.cons ⟨rhs, stable.down, represented.down, exportsRepresented.down,
        countFresh.down, exportCountFresh.down, captured.down⟩ tail)

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

/-- A member's certified RHS is the RHS at its source index in this exact
    original group. The proof composes logical paths; it does not reconcile
    structurally similar RHS expressions after elaboration. -/
theorem Checked.memberRhs {output metadata path vectors captures premises outerTypes outerEnv}
    (g : Checked output metadata path vectors captures premises outerTypes outerEnv)
    {index typeCaptures} (p : Member output metadata path index captures premises typeCaptures) :
    g.rhss[index]? = some (.found p.declaration.node.original p.declaration.node.inner) := by
  have rhsPath := HMDeclaredReconciliation.SourceAt.rhsPath p.declaration.source
  have pathEq : path ++ [.letRecRhs index] = p.declaration.path := Option.some.inj rhsPath
  have descent := Expr.atCorePath_append output path [.letRecRhs index]
  rw [g.source] at descent
  simp only [Expr.atCorePath, Option.bind_some] at descent
  have located := (congrArg (fun q => output.atCorePath q) pathEq).trans p.declaration.node.located
  cases atIndex : g.rhss[index]? <;> rw [atIndex] at descent <;>
    simpa using descent.symm.trans located

def Checked.exports {output metadata path vectors captures premises outerTypes outerEnv}
    (g : Checked output metadata path vectors captures premises outerTypes outerEnv) : List HMCountScheme.Scheme :=
  g.members.exports

theorem Checked.exportCount {output metadata path vectors captures premises outerTypes outerEnv}
    (g : Checked output metadata path vectors captures premises outerTypes outerEnv) :
    g.exports.length = g.rhss.length := g.members.exportCount.trans g.memberCount

theorem Checked.memberAtRhs {output metadata path vectors captures premises outerTypes outerEnv}
    (g : Checked output metadata path vectors captures premises outerTypes outerEnv)
    (offset : Nat) (inside : offset < g.exports.length) :
    let selected := g.members.memberAt offset inside
    g.rhss[offset]? = some (.found selected.member.declaration.node.original
      selected.member.declaration.node.inner) := by
  let selected := g.members.memberAt offset inside
  have sourceRhs := g.memberRhs selected.member
  simpa only [selected.position, Nat.zero_add] using sourceRhs

/-- Every actual erased RHS of a closed checked group has exactly the group's
    lexical slots. ALL-member certification discharges the scope premise of
    simultaneous runtime closure, without guessing scope from final HM types. -/
theorem Checked.rhssScoped {output metadata path vectors captures premises outerTypes}
    (g : Checked output metadata path vectors captures premises outerTypes []) :
    ∀ rhs ∈ g.rhss.map Expr.stripFound,
      rhs.varsBelow (g.rhss.map Expr.stripFound).length = true := by
  intro rhs member
  obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp member
  obtain ⟨i, atIndex⟩ := List.mem_iff_getElem?.mp originalMember
  obtain ⟨inside, _⟩ := List.getElem?_eq_some_iff.mp atIndex
  have exitInside : i < g.exports.length := by rw [g.exportCount]; exact inside
  let selected := g.members.memberAt i exitInside
  have sourceRhs := g.memberAtRhs i exitInside
  have originalEq := Option.some.inj (atIndex.symm.trans sourceRhs)
  rw [originalEq]
  have scope := selected.rhs.certificate.implementation.typing.varsBelow
  simpa only [Expr.stripFound, List.length_map, List.length_append, List.length_nil,
    Nat.add_zero, g.memberCount] using scope

structure ExportedUse {output metadata path vectors captures premises outerTypes outerEnv}
    (g : Checked output metadata path vectors captures premises outerTypes outerEnv)
    (index : Nat) (Δ : List Constraint) (found : Ty) (caller : List Nat) where
  selected : Selected g.members index
  result : RecursiveHMCaller.Checked selected.member.declaration.node
    selected.rhs.certificate Δ found caller

/-- Only an ALL-member checked group can expose this exit-use interface.
    External callers supply their own full HM/count arguments, unlike recursive
    calls' fixed HM vectors. The consuming body walk must still justify argument
    origins and its variable-environment lookup; this is not whole-body typing. -/
def Checked.checkExportedUse {output metadata path vectors captures premises outerTypes outerEnv}
    (g : Checked output metadata path vectors captures premises outerTypes outerEnv)
    (index : Nat) (Δ : List Constraint) (found : Ty) (counts : List Count)
    (types : List BoundsTy) (caller : List Nat) : Except String (ExportedUse g index Δ found caller) := do
  let selected ← g.members.select index
  let result ← RecursiveHMCaller.check selected.member.declaration.node selected.rhs.certificate
    selected.rhs.captured Δ found counts types caller
  pure ⟨selected, result⟩

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
          let ps ← prepareInterfaces output metadata path captures premises guarded 0 vectors
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
#print axioms MemberChecked.certificateScheme
#print axioms MemberChecked.certificateOpeningIds
#print axioms Checked.memberCount
#print axioms Checked.memberRhs
#print axioms CheckedMembers.select
#print axioms CheckedMembers.memberAt
#print axioms Checked.exportCount
#print axioms Checked.memberAtRhs
#print axioms Checked.rhssScoped
#print axioms Checked.checkExportedUse
#print axioms check

end FHM.Bounds.HMDeclaredGroup
