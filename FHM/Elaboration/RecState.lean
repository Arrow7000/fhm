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


namespace Elaboration

/-- Bounds for live recursive types; completed expressions and metadata are separate. -/
def RecState.Below (frontier : Nat) (state : RecState) : Prop :=
  (∀ spec ∈ state.specs, spec.BelowFvars frontier) ∧
  (∀ images ∈ state.slots, ∀ ty ∈ images, Ty.BelowFvars frontier ty) ∧
  (∀ scheme, some scheme ∈ state.exports → Ty.BelowFvars frontier scheme.body) ∧
  (∀ name ∈ state.pool, name < frontier)

 theorem RecState.Below.init {base : Nat} {anns : List LetAnn}
    (hanns : ∀ ann ∈ anns, ∀ v ∈ ann.rigidVars, v < base) :
    (RecState.init base anns).Below (base + anns.length) := by
  have hmode : ∀ scheme, some scheme ∈ anns.map LetAnn.recModeAnn → Ty.BelowFvars (base + anns.length) scheme.body := by
    intro scheme hm
    obtain ⟨ann, hann, heq⟩ := List.mem_map.mp hm
    cases ann with
    | absent | template t | partialForall n t => cases heq
    | complete σ =>
      have hs : σ = scheme := Option.some.inj heq
      subst scheme
      exact Ty.BelowFvars.of_freeVars_lt (fun v hv => Nat.lt_of_lt_of_le (hanns _ hann v hv) (by omega))
  refine ⟨?_, ?_, hmode, by simp [RecState.init]⟩
  · intro spec hm
    rcases RecSpec.mem_init hm with ⟨m, _, hupper, rfl⟩ | ⟨scheme, hs, rfl⟩
    · exact .fvar (by simpa only [List.length_map] using hupper)
    · exact hmode scheme hs
  · intro images hm ty ht
    obtain ⟨ann, _, heq⟩ := List.mem_map.mp hm
    cases heq
    cases ht

 theorem RecState.Below.mono {state : RecState} (h : state.Below frontier) (hle : frontier ≤ next) :
    state.Below next :=
  ⟨fun spec hs => (h.1 spec hs).mono hle,
    fun images hi ty ht => (h.2.1 images hi ty ht).mono hle,
    fun scheme hs => (h.2.2.1 scheme hs).mono hle,
    fun name hn => Nat.lt_of_lt_of_le (h.2.2.2 name hn) hle⟩

 theorem RecState.Below.onSubst {state : RecState} (h : state.Below frontier)
    (hS : ∀ p ∈ S, Ty.BelowFvars next p.2) (hle : frontier ≤ next) :
    (state.onSubst S).Below next := by
  refine ⟨?_, ?_, ?_, fun name hn => Nat.lt_of_lt_of_le (h.2.2.2 name hn) hle⟩
  · intro spec hm
    obtain ⟨old, hold, rfl⟩ := List.mem_map.mp hm
    cases old with
    | mono ty => exact Subst.onTy_belowFvars hS ((h.1 _ hold).mono hle)
    | poly scheme => exact Subst.onTy_belowFvars hS ((h.1 _ hold).mono hle)
  · intro images hm ty ht
    obtain ⟨old, hold, rfl⟩ := List.mem_map.mp hm
    obtain ⟨original, ho, rfl⟩ := List.mem_map.mp ht
    exact Subst.onTy_belowFvars hS ((h.2.1 old hold original ho).mono hle)
  · intro scheme hm
    obtain ⟨old, hold, heq⟩ := List.mem_map.mp hm
    obtain ⟨original, ho, rfl⟩ := Option.map_eq_some_iff.mp heq
    exact Subst.onTy_belowFvars hS ((h.2.2.1 original (ho ▸ hold)).mono hle)

 theorem RecState.Below.setSigned {state : RecState} (h : state.Below frontier) {facts : RecFacts} :
    (state.setSigned member names output facts).Below frontier := h

 theorem RecState.Below.rhsCtx {state : RecState} (h : state.Below frontier) (hctx : CtxBelow frontier ctx) :
    CtxBelow frontier (state.rhsCtx ctx) := by
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
    | some σ => cases heq; exact h.2.2.1 σ hmem.2
  · exact hctx scheme hm

 theorem RecState.Below.fixedCtx {state : RecState} (h : state.Below frontier) (hctx : CtxBelow frontier ctx) :
    CtxBelow frontier (state.fixedCtx ctx) := by
  intro scheme hm
  rcases List.mem_append.mp hm with hm | hm
  · obtain ⟨old, hold, heq⟩ := List.mem_filterMap.mp hm
    exact h.2.2.1 scheme (heq ▸ hold)
  · exact hctx scheme hm

 theorem RecState.Below.installOpenings {state : RecState} (h : state.Below frontier)
    (hopen : OpenRecAnns members index frontier anns next openings) :
    (state.installOpenings members openings).Below next := by
  have hb := h.mono hopen.frontier_le
  refine ⟨hb.1, ?_, hb.2.2⟩
  intro images hm ty ht
  obtain ⟨i, hi, heq⟩ := List.mem_mapIdx.mp hm
  split at heq
  · cases ho : openings[i]? with
    | none => simp [ho, RecOpening.empty] at heq; subst images; cases ht
    | some opening =>
      simp only [ho, Option.getD_some] at heq
      subst images
      obtain ⟨name, hn, rfl⟩ := List.mem_map.mp ht
      exact .fvar ((hopen.written_range name (List.mem_flatMap.mpr
        ⟨opening, List.mem_of_getElem? ho, hn⟩)).2)
  · exact hb.2.1 _ (List.getElem_mem hi) ty (heq ▸ ht)

 theorem ResolveRecSlots.names_below
    (h : ResolveRecSlots members forbidden index slots names)
    (hslots : ∀ images ∈ slots, ∀ ty ∈ images, Ty.BelowFvars frontier ty) :
    ∀ name ∈ names.flatten, name < frontier := by
  induction h with
  | nil => intro name hn; cases hn
  | skip _ _ ih =>
    exact ih (fun images hi => hslots images (List.mem_cons_of_mem _ hi))
  | cons _ hbare _ _ _ ih =>
    intro name hn
    rcases List.mem_append.mp hn with hn | hn
    · have hb := hslots _ List.mem_cons_self (.fvar name)
        (hbare ▸ List.mem_map.mpr ⟨name, hn, rfl⟩)
      exact hb.mem_lt name (by simp [Ty.freeVars])
    · exact ih (fun images hi => hslots images (List.mem_cons_of_mem _ hi)) name hn

private theorem monoTysAt_below {specs : List RecSpec}
    (h : ∀ spec ∈ specs, spec.BelowFvars frontier) :
    ∀ ty ∈ RecSpecs.monoTysAt specs members, Ty.BelowFvars frontier ty := by
  intro ty hm
  obtain ⟨i, _, heq⟩ := List.mem_filterMap.mp hm
  cases hs : specs[i]? with
  | none => simp [hs] at heq
  | some spec =>
    cases spec with
    | poly σ => simp [hs, RecSpec.monoTy?] at heq
    | mono original =>
      simp [hs, RecSpec.monoTy?] at heq
      subst ty
      exact h _ (List.mem_of_getElem? hs)

private theorem freeVarsList_below {tys : List Ty}
    (h : ∀ ty ∈ tys, Ty.BelowFvars frontier ty) :
    ∀ v ∈ Ty.freeVarsList tys, v < frontier := by
  induction tys with
  | nil => intro v hv; cases hv
  | cons ty rest ih =>
    intro v hv
    rcases List.mem_append.mp (List.mem_dedup.mp hv) with hv | hv
    · exact (h ty List.mem_cons_self).mem_lt v hv
    · exact ih (fun t ht => h t (List.mem_cons_of_mem _ ht)) v hv

 theorem RecState.Below.componentPool {state : RecState} (h : state.Below frontier)
    (hnames : ∀ v ∈ written.flatten, v < frontier) :
    ∀ v ∈ state.componentPool K soft members ctx written, v < frontier := by
  intro v hv
  rcases List.mem_append.mp hv with hv | hv
  · exact h.2.2.2 v hv
  · have hm := List.mem_dedup.mp (List.mem_filter.mp hv).1
    rcases List.mem_append.mp hm with hm | hm
    · exact hnames v hm
    · have hf := (List.mem_filter.mp hm).1
      exact freeVarsList_below (monoTysAt_below h.1) v hf

 theorem RecState.Below.exportComponent {state : RecState} (h : state.Below frontier)
    {pool : List Nat} {outputs : List (Option Expr)} {facts : List RecFacts}
    (hpool : ∀ v ∈ pool, v < frontier) :
    (state.exportComponent members written pool outputs facts).Below frontier := by
  refine ⟨h.1, h.2.1, ?_, hpool⟩
  intro scheme hm
  obtain ⟨i, hi, heq⟩ := List.mem_mapIdx.mp hm
  split at heq
  · cases hs : state.specs[i]? with
    | none => simp [hs] at heq
    | some spec =>
      simp [hs] at heq
      subst scheme
      cases spec with
      | mono ty => exact (h.1 _ (List.mem_of_getElem? hs)).closeOver
      | poly σ => exact h.1 _ (List.mem_of_getElem? hs)
  · exact h.2.2.1 scheme (heq ▸ List.getElem_mem hi)

 theorem FinishRecComponent.below (h : FinishRecComponent K soft members ctx state outputs facts final)
    (hstate : state.Below frontier) : final.Below frontier := by
  cases h with
  | mk hslots =>
      exact hstate.exportComponent (hstate.componentPool (hslots.names_below hstate.2.1))

end Elaboration

namespace Elaboration

/-- The live type state of a dependency-first recursion solve. Completed members
are compared through their exported schemes; exact seed equations are retained
only for members that have not yet been solved. -/
structure RecState.Frame (base : Nat) (K : List Nat) (F : List Ty)
    (ctx : Ctx) (anns : List LetAnn) (done : List Nat) (state : RecState) : Prop where
  specs_length : state.specs.length = anns.length
  slots_length : state.slots.length = anns.length
  exports_length : state.exports.length = anns.length
  outputs_length : state.outputs.length = anns.length
  facts_length : state.facts.length = anns.length
  modes : state.specs.map RecSpec.ann = anns.map LetAnn.recModeAnn
  poly : ∀ (i : Nat) (scheme : PolyTy), state.specs[i]? = some (RecSpec.poly scheme) →
    state.exports[i]? = some (some scheme)
  mono : ∀ (i : Nat) (ty : Ty), state.specs[i]? = some (RecSpec.mono ty) →
    if i ∈ done then ∃ written,
      state.slots[i]? = some (written.map Ty.fvar) ∧
      written.length = (anns[i]?.getD .absent).recPrefixCount ∧ written.Nodup ∧
      (∀ v ∈ written, v ∈ state.pool) ∧
      state.exports[i]? = some (some (recScheme written state.pool ty))
    else state.exports[i]? = some none
  pending : RecSpecs.PendingSeeds base ctx state.specs done
  pool_nodup : state.pool.Nodup
  pool_ctx : ∀ v ∈ state.pool, v ∉ ctx.env.freeVars
  pool_rigid : ∀ v ∈ state.pool, v ∉ K
  pool_soft : ∀ v ∈ state.pool, v ∉ TyList.freeVars F
  pool_poly : ∀ (scheme : PolyTy), (∃ i : Nat, state.specs[i]? = some (.poly scheme)) →
    ∀ v ∈ state.pool, v ∉ scheme.body.freeVars
  pool_pending : ∀ (i : Nat) (ty : Ty), state.specs[i]? = some (RecSpec.mono ty) → i ∉ done →
    base + i ∉ state.pool
  rigid_below : ∀ v ∈ K, v < base
  pending_soft : ∀ (i : Nat) (ty : Ty), state.specs[i]? = some (RecSpec.mono ty) → i ∉ done →
    base + i ∉ TyList.freeVars F

 theorem RecState.Frame.entries_length {state : RecState} {base : Nat} {K : List Nat}
    {F : List Ty} {ctx : Ctx} {anns : List LetAnn} {done : List Nat}
    (h : state.Frame base K F ctx anns done) :
    state.entries.length = anns.length := by
  rw [state.entries_length (h.exports_length.trans h.specs_length.symm), h.specs_length]

 theorem RecState.Frame.init {base : Nat} {K : List Nat} {F : List Ty} {ctx : Ctx}
    {anns : List LetAnn} (hctx : CtxBelow base ctx)
    (hanns : ∀ v ∈ anns.flatMap LetAnn.rigidVars, v < base)
    (hK : ∀ v ∈ K, v < base) (hF : ∀ v ∈ TyList.freeVars F, v < base) :
    (RecState.init base anns).Frame base K F ctx anns [] := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := RecState.init_lengths base anns
  refine ⟨h1, h2, h3, h4, h5, ?_, ?_, ?_, ?_, by simp [RecState.init],
    by simp [RecState.init], by simp [RecState.init], by simp [RecState.init],
    by simp [RecState.init], by simp [RecState.init], hK, ?_⟩
  · exact RecSpec.map_ann_init base _
  · intro i scheme hspec
    have heq := congrArg (fun specs : List RecSpec => (specs.map RecSpec.ann)[i]?)
      (show (RecState.init base anns).specs = RecSpec.init base (anns.map LetAnn.recModeAnn) from rfl)
    have hm := congrArg (fun xs : List (Option PolyTy) => xs[i]?)
      (RecSpec.map_ann_init base (anns.map LetAnn.recModeAnn))
    simp only [List.getElem?_map, ← heq, hspec, Option.map_some, RecSpec.ann] at hm
    simpa only [RecState.init, List.getElem?_map] using hm.symm
  · intro i ty hspec
    simp only [List.not_mem_nil, ↓reduceIte]
    have hm := congrArg (fun xs : List (Option PolyTy) => xs[i]?)
      (RecSpec.map_ann_init base (anns.map LetAnn.recModeAnn))
    change (RecState.init base anns).exports[i]? = some none
    simp only [RecState.init, List.getElem?_map] at hspec ⊢
    have heq : (RecSpec.init base (anns.map LetAnn.recModeAnn))[i]? = some (.mono ty) := hspec
    simpa only [List.getElem?_map, heq, Option.map_some, RecSpec.ann] using hm.symm
  · apply RecSpecs.PendingSeeds.init hctx
    intro scheme hm
    apply Ty.BelowFvars.of_freeVars_lt
    intro v hv
    obtain ⟨ann, ha, heq⟩ := List.mem_map.mp hm
    have hs : scheme.body.freeVars = ann.rigidVars := by
      cases ann <;> simp_all [LetAnn.recModeAnn, LetAnn.rigidVars]
    exact hanns v (List.mem_flatMap.mpr ⟨ann, ha, hs ▸ hv⟩)
  · intro i ty _ _ hmem
    have := hF (base + i) hmem
    omega


 theorem RecState.Frame.pool_entries {state : RecState} {base : Nat} {K : List Nat}
    {F : List Ty} {ctx : Ctx} {anns : List LetAnn} {done : List Nat}
    (h : state.Frame base K F ctx anns done) :
    ∀ v ∈ state.pool, ∀ scheme ∈ state.entries, v ∉ scheme.body.freeVars := by
  intro v hv scheme hm
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hm
  rw [RecState.entries, List.getElem?_map] at hi
  obtain ⟨⟨spec, exported⟩, hz, heq⟩ := Option.map_eq_some_iff.mp hi
  obtain ⟨hs, he⟩ := List.getElem?_zip_eq_some.mp hz
  cases spec with
  | poly sigma =>
    have hex := h.poly i sigma hs
    have heqex := Option.some.inj (he.symm.trans hex)
    change exported = some sigma at heqex
    subst exported
    change sigma = scheme at heq
    subst scheme
    have hother : v ∉ sigma.body.freeVars := by
      have hfixed : sigma ∈ state.exports.filterMap id := by
        apply List.mem_filterMap.mpr
        exact ⟨some sigma, List.mem_of_getElem? hex, rfl⟩
      -- Complete contracts are entries in the fixed boundary. Their free
      -- variables must be excluded from a previously generalized pool.
      exact h.pool_poly sigma ⟨i, hs⟩ v hv
    exact hother
  | mono ty =>
    have hx := h.mono i ty hs
    by_cases hd : i ∈ done
    · simp only [hd, ↓reduceIte] at hx
      obtain ⟨written, _, _, _, _, hex⟩ := hx
      have heqex := Option.some.inj (he.symm.trans hex)
      change exported = some (recScheme written state.pool ty) at heqex
      subst exported
      change recScheme written state.pool ty = scheme at heq
      subst scheme
      exact fun hm => Ty.not_mem_closeOver_freeVars
        (mem_recNames_of_mem_pool hv (Ty.freeVars_closeOver_subset hm)) hm
    · simp only [hd, ↓reduceIte] at hx
      have heqex := Option.some.inj (he.symm.trans hx)
      change exported = none at heqex
      subst exported
      change PolyTy.mkTrivial ty = scheme at heq
      subst scheme
      rw [h.pending.mono i ty hs hd]
      simp only [PolyTy.mkTrivial, Ty.freeVars, List.mem_singleton]
      exact fun heq => h.pool_pending i ty hs hd (heq ▸ hv)

 theorem RecState.Frame.pool_rhsCtx {state : RecState} {base : Nat} {K : List Nat}
    {F : List Ty} {ctx : Ctx} {anns : List LetAnn} {done : List Nat}
    (h : state.Frame base K F ctx anns done) :
    ∀ v ∈ state.pool, v ∉ (state.rhsCtx ctx).env.freeVars := by
  intro v hv hm
  obtain ⟨scheme, hs, ht⟩ := Env.mem_freeVars_iff.mp hm
  exact (List.mem_append.mp hs).elim
    (fun hentry => h.pool_entries v hv scheme hentry ht)
    (fun houter => h.pool_ctx v hv (Env.mem_freeVars_iff.mpr ⟨scheme, houter, ht⟩))

 theorem RecState.Frame.installOpenings {state : RecState} {base : Nat} {K : List Nat}
    {F : List Ty} {ctx : Ctx} {anns : List LetAnn} {done members : List Nat}
    {openings : List RecOpening} (h : state.Frame base K F ctx anns done)
    (hnot : ∀ i ∈ members, i ∉ done) :
    (state.installOpenings members openings).Frame base K F ctx anns done := by
  refine ⟨h.specs_length, by simpa only [RecState.installOpenings, List.length_mapIdx] using h.slots_length,
    h.exports_length, h.outputs_length, h.facts_length, h.modes, h.poly, ?_, h.pending,
    h.pool_nodup, h.pool_ctx, h.pool_rigid, h.pool_soft, h.pool_poly, h.pool_pending,
    h.rigid_below, h.pending_soft⟩
  intro i ty hs
  have hm := h.mono i ty hs
  by_cases hd : i ∈ done
  · simp only [hd, ↓reduceIte] at hm ⊢
    obtain ⟨written, hslot, hcount, hnd, hpool, hex⟩ := hm
    refine ⟨written, ?_, hcount, hnd, hpool, hex⟩
    have hi : i ∉ members := fun hc => hnot i hc hd
    simp only [RecState.installOpenings, List.getElem?_mapIdx, hslot, Option.map_some, if_neg hi]
  · simpa only [hd, ↓reduceIte] using hm


end Elaboration
