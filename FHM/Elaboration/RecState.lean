import FHM.Elaboration.RecOpening
import FHM.Elaboration.RecShapeCheck

namespace Elaboration

/-- Artifacts remain in inference-variable coordinates until each member's
written prefix is finalized. Closing an output expression is separate. -/
structure RecFacts where
  nodeTypes : InferredNodeTypes
  binderSchemes : InferredBinderSchemes

def RecFacts.empty : RecFacts := ⟨[], []⟩

def RecFacts.onSubst (S : Subst) (facts : RecFacts) : RecFacts :=
  ⟨facts.nodeTypes.onSubst S, facts.binderSchemes.onSubst S⟩

/-- All lists retain original recursive-group coordinates. `slots` records the
ordered current images of written slots, including unused ones; `exports`
contains complete contracts and already generalized inferred components. -/
structure RecState where
  specs : List RecSpec
  slots : List (List Ty)
  exports : List (Option PolyTy)
  outputs : List (Option Expr)
  facts : List RecFacts
  pool : List Nat

def RecState.init (frontier : Nat) (anns : List LetAnn) : RecState :=
  { specs := RecSpec.init frontier (anns.map LetAnn.recModeAnn)
    slots := anns.map (fun _ => [])
    exports := anns.map LetAnn.recModeAnn
    outputs := anns.map (fun _ => none)
    facts := anns.map (fun _ => .empty)
    pool := [] }

def RecState.onSubst (S : Subst) (state : RecState) : RecState :=
  { specs := state.specs.map (RecSpec.onSubstSource S)
    slots := state.slots.map (fun names => names.map S.onTy)
    exports := state.exports.map (Option.map S.onPolyTy)
    outputs := state.outputs.map (Option.map (Expr.substTyFvars S))
    facts := state.facts.map (RecFacts.onSubst S)
    pool := state.pool }

def _root_.RecSpec.monoEntry : RecSpec → PolyTy
  | .mono ty => PolyTy.mkTrivial ty
  | .poly scheme => scheme

def RecState.entries (state : RecState) : List PolyTy :=
  state.specs.zip state.exports |>.map (fun (spec, exported) => exported.getD spec.monoEntry)

def RecState.rhsCtx (state : RecState) (ctx : Ctx) : Ctx :=
  { ctx with env := state.entries ++ ctx.env }

def RecState.fixedCtx (state : RecState) (ctx : Ctx) : Ctx :=
  { ctx with env := state.exports.filterMap id ++ ctx.env }

/-- Install only this component's newly allocated written roots. Other members
retain their own ordered traces. -/
def RecState.installOpenings (state : RecState) (members : List Nat)
    (openings : List RecOpening) : RecState :=
  { state with slots := state.slots.mapIdx (fun i old =>
      if i ∈ members then ((openings[i]?).getD .empty).written.map Ty.fvar else old) }

/-- Open before applying the component's constraints. Provisional slots may
subsequently become nonvariables, so opening cannot be deferred until after S. -/
def openRecSources : List RecOpening → List Input → List Input
  | _, [] => []
  | [], bindings => bindings
  | opening :: openings, rhs :: rest => rhs.openTyVars opening.written :: openRecSources openings rest

@[simp] theorem sizeBindings_openRecSources (openings : List RecOpening) (bindings : List Input) :
    sizeBindings (openRecSources openings bindings) = sizeBindings bindings := by
  induction bindings generalizing openings with
  | nil => cases openings <;> rfl
  | cons rhs rest ih =>
    cases openings with
    | nil => rfl
    | cons opening openings => simp only [openRecSources, sizeBindings, Input.size_openTyVars, ih]


def RecState.shapes (state : RecState) (members : List Nat)
    (openings : List RecOpening) : List RecShape :=
  members.filterMap (fun i => do
    let spec ← state.specs[i]?
    let ty ← spec.monoTy?
    let opening ← openings[i]?
    pure (ty, opening.expected))

/-- Closed unsigned outputs use the member's own prefix order and the shared
pool. Metadata remains open until all later component substitutions are known. -/
def RecState.exportComponent (state : RecState) (members : List Nat)
    (written : List (List Nat)) (pool : List Nat)
    (outputs : List (Option Expr)) (facts : List RecFacts) : RecState :=
  { state with
    exports := state.exports.mapIdx (fun i old =>
      if i ∈ members then do
        let spec ← state.specs[i]?
        pure (spec.completedScheme (written[i]?.getD []) pool)
      else old)
    outputs := state.outputs.mapIdx (fun i old =>
      if i ∈ members then do
        let spec ← state.specs[i]?
        let ty ← spec.monoTy?
        let rhs ← (outputs[i]?).join
        pure (rhs.closeTyVars (recNames (written[i]?.getD []) pool ty))
      else old)
    facts := state.facts.mapIdx (fun i old => if i ∈ members then facts[i]?.getD .empty else old)
    pool := pool }

/-- Validate ordered slot images only for the component being exported. -/
inductive ResolveRecSlots (members : List Nat) (forbidden : List Nat) :
    Nat → List (List Ty) → List (List Nat) → Prop
  | nil : ResolveRecSlots members forbidden index [] []
  | skip : index ∉ members → ResolveRecSlots members forbidden (index + 1) rest names →
      ResolveRecSlots members forbidden index (images :: rest) ([] :: names)
  | cons : index ∈ members → written.map Ty.fvar = images → written.Nodup →
      (∀ name ∈ written, name ∉ forbidden) →
      ResolveRecSlots members forbidden (index + 1) rest names →
      ResolveRecSlots members forbidden index (images :: rest) (written :: names)

def resolveRecSlots (members forbidden : List Nat) (index : Nat) (slots : List (List Ty)) :
    Option { names : List (List Nat) // ResolveRecSlots members forbidden index slots names } :=
  match slots with
  | [] => some ⟨[], .nil⟩
  | images :: rest =>
      if hm : index ∈ members then
        match resolveRecWritten images forbidden, resolveRecSlots members forbidden (index + 1) rest with
        | some ⟨written, hbare, hnd, hav⟩, some ⟨names, hn⟩ =>
            some ⟨written :: names, .cons hm hbare hnd hav hn⟩
        | _, _ => none
      else
        match resolveRecSlots members forbidden (index + 1) rest with
        | some ⟨names, hn⟩ => some ⟨[] :: names, .skip hm hn⟩
        | none => none

def RecState.componentPool (state : RecState) (K soft members : List Nat)
    (ctx : Ctx) (written : List (List Nat)) : List Nat :=
  state.pool ++ ((written.flatten ++
    genGroupVars (K ++ soft ++ state.pool) (state.fixedCtx ctx).env
      (RecSpecs.monoTysAt state.specs members)).dedup.filter (fun v => decide (v ∉ state.pool)))

/-- The only export check on a partial written prefix is ordinary forall
validity: bare, distinct within that member, and fresh in the fixed boundary. -/
inductive FinishRecComponent (K soft members : List Nat) (ctx : Ctx)
    (state : RecState) (outputs : List (Option Expr)) (facts : List RecFacts) :
    RecState → Prop
  | mk {written : List (List Nat)} :
      ResolveRecSlots members ((state.fixedCtx ctx).env.freeVars ++ K ++ soft) 0 state.slots written →
      FinishRecComponent K soft members ctx state outputs facts
        (state.exportComponent members written (state.componentPool K soft members ctx written) outputs facts)

def finishRecComponent (K soft members : List Nat) (ctx : Ctx)
    (state : RecState) (outputs : List (Option Expr)) (facts : List RecFacts) :
    Option { result : RecState // FinishRecComponent K soft members ctx state outputs facts result } :=
  match resolveRecSlots members ((state.fixedCtx ctx).env.freeVars ++ K ++ soft) 0 state.slots with
  | none => none
  | some ⟨written, hw⟩ =>
      some ⟨state.exportComponent members written (state.componentPool K soft members ctx written) outputs facts, .mk hw⟩


def RecFacts.closeWritten (names : List Nat) (facts : RecFacts) : RecFacts :=
  ⟨(facts.nodeTypes.closeTyVars names).underTyBinders names.length,
    (facts.binderSchemes.closeTyVars names).underTyBinders names.length⟩

/-- Complete-signature RHSs close their rigid opening before leaving its scope.
Partial prefixes stay open in the stored metadata until final normalization. -/
def RecState.setSigned (state : RecState) (member : Nat) (names : List Nat)
    (output : Expr) (facts : RecFacts) : RecState :=
  { state with
    outputs := state.outputs.set member (some (output.closeTyVars names))
    facts := state.facts.set member (facts.closeWritten names) }


/-- Extract a completed aligned vector, retaining its exact positional equation. -/
def collectRecValues {α : Type} : (values : List (Option α)) →
    Option { result : List α // values = result.map some }
  | [] => some ⟨[], rfl⟩
  | none :: _ => none
  | some value :: rest =>
      match collectRecValues rest with
      | none => none
      | some ⟨values, hv⟩ => some ⟨value :: values, congrArg (some value :: ·) hv⟩

private def recSlotName : Ty → Option Nat
  | .fvar name => some name
  | _ => none

/-- Close only authored partial-prefix representatives in editor artifacts.
Additional generalized variables keep the ordinary inference-variable convention. -/
def finalizeRecFacts (ann : LetAnn) (slots : List Ty) (facts : RecFacts) : RecFacts :=
  match ann with
  | .partialForall count _ =>
      let written := slots.filterMap recSlotName
      ⟨(facts.nodeTypes.closeTyVars written).underTyBinders count,
        (facts.binderSchemes.closeTyVars written).underTyBinders count⟩
  | _ => facts

def inferredRecSchemes (anns : List LetAnn) (schemes : List PolyTy) : InferredBinderSchemes :=
  anns.zip schemes |>.mapIdx (fun i (ann, scheme) => match ann with
    | .complete _ => []
    | _ => [{ site := .letRec [] i, scheme := scheme, tyDepth := 0 }]) |>.flatten

def finalRecNodeTypes (anns : List LetAnn) (state : RecState) : InferredNodeTypes :=
  state.facts.mapIdx (fun i facts =>
    (finalizeRecFacts (anns[i]?.getD .absent) (state.slots[i]?.getD []) facts).nodeTypes.below (.letRecRhs i)) |>.flatten

def finalRecBinderSchemes (anns : List LetAnn) (state : RecState) : InferredBinderSchemes :=
  state.facts.mapIdx (fun i facts =>
    (finalizeRecFacts (anns[i]?.getD .absent) (state.slots[i]?.getD []) facts).binderSchemes.below (.letRecRhs i)) |>.flatten

@[simp] theorem sizeBindings_map_substTyFvars (bindings : List Input) (S : Subst) :
    sizeBindings (bindings.map (Input.substTyFvars S)) = sizeBindings bindings := by
  induction bindings with
  | nil => rfl
  | cons rhs rest ih => simp only [List.map_cons, sizeBindings, Input.size_substTyFvars, ih]

end Elaboration


namespace Elaboration

@[simp] theorem RecState.entries_onSubst (state : RecState) (S : Subst) :
    (state.onSubst S).entries = S.onEnv state.entries := by
  simp only [RecState.entries, RecState.onSubst, Subst.onEnv, List.zip_map_left,
    List.zip_map_right, List.map_map]
  apply List.map_congr_left
  intro pair _
  rcases pair with ⟨spec, exported⟩
  cases exported with
  | none => cases spec <;> rfl
  | some scheme => rfl

@[simp] theorem RecState.rhsCtx_onSubst (state : RecState) (S : Subst) (ctx : Ctx) :
    (state.onSubst S).rhsCtx (S.onCtx ctx) = S.onCtx (state.rhsCtx ctx) := by
  simp only [RecState.rhsCtx, RecState.entries_onSubst, Subst.onCtx, Subst.onEnv, List.map_append]

@[simp] theorem RecState.fixedCtx_onSubst (state : RecState) (S : Subst) (ctx : Ctx) :
    (state.onSubst S).fixedCtx (S.onCtx ctx) = S.onCtx (state.fixedCtx ctx) := by
  simp only [RecState.fixedCtx, RecState.onSubst, Subst.onCtx, Subst.onEnv,
    List.map_append, List.map_filterMap, List.filterMap_map, Function.comp_def, id_eq]

 theorem RecState.entries_length (state : RecState)
    (hlen : state.exports.length = state.specs.length) : state.entries.length = state.specs.length := by
  simp only [RecState.entries, List.length_map, List.length_zip, hlen, Nat.min_self]

@[simp] theorem RecState.init_lengths (base : Nat) (anns : List LetAnn) :
    (RecState.init base anns).specs.length = anns.length ∧
    (RecState.init base anns).slots.length = anns.length ∧
    (RecState.init base anns).exports.length = anns.length ∧
    (RecState.init base anns).outputs.length = anns.length ∧
    (RecState.init base anns).facts.length = anns.length := by
  simp only [RecState.init, RecSpec.init_length, List.length_map, and_self]

 theorem RecState.onSubst_lengths (state : RecState) (S : Subst) :
    (state.onSubst S).specs.length = state.specs.length ∧
    (state.onSubst S).slots.length = state.slots.length ∧
    (state.onSubst S).exports.length = state.exports.length ∧
    (state.onSubst S).outputs.length = state.outputs.length ∧
    (state.onSubst S).facts.length = state.facts.length := by
  simp only [RecState.onSubst, List.length_map, and_self]

private theorem initial_entries (base : Nat) (anns : List (Option PolyTy)) :
    ((RecSpec.init base anns).zip anns).map (fun (spec, exported) => exported.getD spec.monoEntry) =
      (RecSpec.init base anns).map RecSpec.monoEntry := by
  induction anns generalizing base with
  | nil => rfl
  | cons ann rest ih =>
      cases ann with
      | none => exact congrArg (List.cons (PolyTy.mkTrivial (.fvar base))) (ih (base + 1))
      | some scheme => exact congrArg (List.cons scheme) (ih (base + 1))

 theorem RecState.init_entries (base : Nat) (anns : List LetAnn) :
    (RecState.init base anns).entries =
      (RecSpec.init base (anns.map LetAnn.recModeAnn)).map RecSpec.monoEntry :=
  initial_entries base (anns.map LetAnn.recModeAnn)

 theorem RecState.init_rhsCtx (base : Nat) (anns : List LetAnn) (ctx : Ctx) :
    (RecState.init base anns).rhsCtx ctx =
      RecSpecs.algorithmStageCtx ctx (RecSpec.init base (anns.map LetAnn.recModeAnn)) [] [] := by
  simp only [RecState.rhsCtx, RecState.init_entries, RecSpecs.algorithmStageCtx]
  congr 1
  congr 1
  apply List.ext_getElem?
  intro i
  simp only [List.getElem?_map, List.getElem?_mapIdx]
  cases hs : (RecSpec.init base (anns.map LetAnn.recModeAnn))[i]? with
  | none => rfl
  | some spec => cases spec <;> simp [RecSpec.monoEntry, RecSpec.algorithmStageEntry]

 theorem RecState.pendingSeeds_init {base : Nat} {ctx : Ctx} {anns : List LetAnn}
    (hctx : CtxBelow base ctx)
    (hanns : ∀ ann ∈ anns, ∀ v ∈ ann.rigidVars, v < base) :
    RecSpecs.PendingSeeds base ctx (RecState.init base anns).specs [] := by
  apply RecSpecs.PendingSeeds.init hctx
  intro scheme hm
  obtain ⟨ann, hann, heq⟩ := List.mem_map.mp hm
  cases ann with
  | absent | template t | partialForall n t => cases heq
  | complete σ =>
      have hs : σ = scheme := Option.some.inj heq
      subst scheme
      exact Ty.BelowFvars.of_freeVars_lt (hanns (.complete σ) hann)

end Elaboration


namespace Elaboration

/-- Only recursive type specs and already exported schemes constrain LC. -/
def RecState.LC (state : RecState) : Prop :=
  (∀ spec ∈ state.specs, spec.LC) ∧ (∀ scheme, some scheme ∈ state.exports → scheme.WF)

 theorem RecState.LC.init {base : Nat} {anns : List LetAnn}
    (hanns : ∀ scheme, .complete scheme ∈ anns → scheme.WF) : (RecState.init base anns).LC := by
  have hmode : ∀ scheme, some scheme ∈ anns.map LetAnn.recModeAnn → scheme.WF := by
    intro scheme hm
    obtain ⟨ann, hann, heq⟩ := List.mem_map.mp hm
    cases ann with
    | absent | template t | partialForall n t => cases heq
    | complete σ =>
        have hs : σ = scheme := Option.some.inj heq
        subst scheme
        exact hanns σ hann
  constructor
  · intro spec hm
    rcases RecSpec.mem_init hm with ⟨m, _, _, rfl⟩ | ⟨scheme, hs, rfl⟩
    · exact .fvar
    · exact hmode scheme hs
  · exact hmode

 theorem RecState.LC.onSubst {state : RecState} (h : state.LC)
    (hS : ∀ p ∈ S, p.2.IsLC) : (state.onSubst S).LC := by
  constructor
  · intro spec hm
    obtain ⟨old, hold, rfl⟩ := List.mem_map.mp hm
    cases old with
    | mono ty => exact Subst.onTy_lc hS (h.1 _ hold)
    | poly scheme => exact Subst.onPolyTy_wf hS (h.1 _ hold)
  · intro scheme hm
    obtain ⟨old, hold, heq⟩ := List.mem_map.mp hm
    obtain ⟨original, ho, rfl⟩ := Option.map_eq_some_iff.mp heq
    exact Subst.onPolyTy_wf hS (h.2 original (ho ▸ hold))

 theorem RecState.LC.installOpenings {state : RecState} (h : state.LC) :
    (state.installOpenings members openings).LC := h

 theorem RecState.LC.setSigned {state : RecState} (h : state.LC) {facts : RecFacts} :
    (state.setSigned member names output facts).LC := h

 theorem RecState.LC.rhsCtx {state : RecState} (h : state.LC) (hctx : CtxWF ctx) :
    CtxWF (state.rhsCtx ctx) := by
  intro scheme hm
  rcases List.mem_append.mp hm with hm | hm
  · obtain ⟨⟨spec, exported⟩, hp, heq⟩ := List.mem_map.mp hm
    have hmem := List.of_mem_zip hp
    cases exported with
    | none =>
      subst scheme
      cases spec with
      | mono ty => exact h.1 _ hmem.1
      | poly σ => exact h.1 _ hmem.1
    | some σ =>
      cases heq
      exact h.2 σ hmem.2
  · exact hctx scheme hm

 theorem RecState.LC.fixedCtx {state : RecState} (h : state.LC) (hctx : CtxWF ctx) :
    CtxWF (state.fixedCtx ctx) := by
  intro scheme hm
  rcases List.mem_append.mp hm with hm | hm
  · obtain ⟨old, hold, heq⟩ := List.mem_filterMap.mp hm
    exact h.2 scheme (heq ▸ hold)
  · exact hctx scheme hm

 theorem RecState.LC.exportComponent {state : RecState} (h : state.LC)
    {pool : List Nat} {outputs : List (Option Expr)} {facts : List RecFacts} :
    (state.exportComponent members written pool outputs facts).LC := by
  refine ⟨h.1, ?_⟩
  intro scheme hm
  obtain ⟨i, hi, heq⟩ := List.mem_mapIdx.mp hm
  split at heq
  · cases hs : state.specs[i]? with
    | none => simp [hs] at heq
    | some spec =>
      simp [hs] at heq
      subst scheme
      exact RecSpec.completedScheme_wf (h.1 spec (List.mem_of_getElem? hs))
  · exact h.2 scheme (heq ▸ List.getElem_mem hi)

 theorem FinishRecComponent.lc (h : FinishRecComponent K soft members ctx state outputs facts final)
    (hstate : state.LC) : final.LC := by
  cases h
  exact hstate.exportComponent

end Elaboration
