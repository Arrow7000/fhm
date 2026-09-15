import FHM.Bounds.ScopedHMInterpretation
import FHM.Bounds.ScopedAnnotation
import FHM.Bounds.Typed

/-! Source obligations with simultaneous free/lexical HM interfaces. Count
specialization transforms both interfaces and the original source interpretation;
full caller types inserted subsequently cannot be captured by that telescope.
No expression/annotation rewriting, RHS typing or group export is assumed here.
-/

namespace FHM.Bounds.ScopedHMAnnotation

open ScopedHMInterpretation CountSubstitution ScopedScheme

def AnnotationOK (free slots : Nat → BoundsTy) (ids : List Nat) (rows : Bindings)
    (Δ : List Constraint) (τ : Ty) (actual : BoundsTy) : Prop :=
  ∃ d : ScopedAnnotation.Decoded ids τ, ScopedAnnotation.decode ids τ = .ok d ∧
    SemanticSub Δ actual (read free slots (bounds rows d.bounds))

def ParamOK (free slots : Nat → BoundsTy) (ids : List Nat) (rows : Bindings)
    (Δ : List Constraint) (ann : Option Ty) (actual : BoundsTy) : Prop :=
  match ann with | none => True | some τ => AnnotationOK free slots ids rows Δ τ actual

def BindingOK (free slots : Nat → BoundsTy) (ids : List Nat) (rows : Bindings)
    (Δ : List Constraint) (ann : Option PolyTy) (actual : BoundsTy) : Prop :=
  match ann with
  | none => True
  | some σ => σ.paramCount = 0 ∧ AnnotationOK free slots ids rows Δ σ.body actual

theorem AnnotationOK.types {free slots ids rows Δ τ actual}
    (h : AnnotationOK free slots ids rows Δ τ actual) (outer : Nat → BoundsTy) :
    AnnotationOK (fun i => SchemeSpecialization.mapFree outer (free i))
      (fun i => SchemeSpecialization.mapFree outer (slots i)) ids rows Δ τ
      (SchemeSpecialization.mapFree outer actual) := by
  obtain ⟨d, hd, hs⟩ := h
  exact ⟨d, hd, by simpa only [map_types] using SchemeSpecialization.subtype outer hs⟩

theorem AnnotationOK.counts {free slots ids rows Δ τ actual}
    (h : AnnotationOK free slots ids rows Δ τ actual) (outer : Bindings) (finite : Finite outer) :
    AnnotationOK (fun i => bounds outer (free i)) (fun i => bounds outer (slots i))
      ids (CountAlgebra.compose outer rows) (Δ.map (constraint outer)) τ (bounds outer actual) := by
  obtain ⟨d, hd, hs⟩ := h
  exact ⟨d, hd, by simpa only [map_counts, CountAlgebra.bounds_compose] using subtype outer finite hs⟩

theorem AnnotationOK.assuming {free slots ids rows Δ Δ' τ actual}
    (h : AnnotationOK free slots ids rows Δ τ actual) (premises : (⟨Δ', Δ⟩ : ForallProblem).Valid) :
    AnnotationOK free slots ids rows Δ' τ actual := by
  obtain ⟨d, hd, hs⟩ := h
  exact ⟨d, hd, hs.assuming premises⟩

/-- Source checking may change solved artifact identities without changing
    the meaning of identities carried by the original annotation. -/
theorem AnnotationOK.congrFree {free free' slots ids rows Δ τ actual}
    (h : AnnotationOK free slots ids rows Δ τ actual)
    (agree : ∀ i ∈ τ.freeVars, free i = free' i) :
    AnnotationOK free' slots ids rows Δ τ actual := by
  obtain ⟨d, decoded, inclusion⟩ := h
  have same : read free slots (bounds rows d.bounds) = read free' slots (bounds rows d.bounds) :=
    ScopedHMInterpretation.congrFree (fun i member => agree i (by
      simpa only [bounds_shape, d.shape, eraseFreeVars] using member))
  exact ⟨d, decoded, by rw [← same]; exact inclusion⟩

/-- Lexical readers may likewise be changed outside the bound slots actually
    named by the source annotation. -/
theorem AnnotationOK.congrSlots {free slots slots' ids rows Δ τ actual n}
    (h : AnnotationOK free slots ids rows Δ τ actual)
    (bounded : ContainsBvarsUpTo n τ)
    (agree : ∀ i < n, slots i = slots' i) :
    AnnotationOK free slots' ids rows Δ τ actual := by
  obtain ⟨d, decoded, inclusion⟩ := h
  have sourceBounded : ContainsBvarsUpTo n (Synth.BoundsTy.toTy (bounds rows d.bounds)) := by
    simpa only [bounds_shape, d.shape] using bounded.eraseBounds
  have same := ScopedHMInterpretation.congrSlots (free := free) sourceBounded agree
  exact ⟨d, decoded, by rw [← same]; exact inclusion⟩

theorem ParamOK.congrFree {free free' slots ids rows Δ ann actual}
    (h : ParamOK free slots ids rows Δ ann actual)
    (agree : ∀ i ∈ ann.elim [] Ty.freeVars, free i = free' i) :
    ParamOK free' slots ids rows Δ ann actual := by
  cases ann with
  | none => trivial
  | some τ => exact AnnotationOK.congrFree h agree

theorem ParamOK.congrSlots {free slots slots' ids rows Δ ann actual n}
    (h : ParamOK free slots ids rows Δ ann actual)
    (bounded : ∀ τ, ann = some τ → ContainsBvarsUpTo n τ)
    (agree : ∀ i < n, slots i = slots' i) :
    ParamOK free slots' ids rows Δ ann actual := by
  cases ann with
  | none => trivial
  | some τ => exact AnnotationOK.congrSlots h (bounded τ rfl) agree

theorem BindingOK.congrFree {free free' slots ids rows Δ ann actual}
    (h : BindingOK free slots ids rows Δ ann actual)
    (agree : ∀ i ∈ ann.elim [] (fun σ => σ.body.freeVars), free i = free' i) :
    BindingOK free' slots ids rows Δ ann actual := by
  cases ann with
  | none => trivial
  | some σ => exact ⟨h.1, AnnotationOK.congrFree h.2 agree⟩

theorem BindingOK.congrSlots {free slots slots' ids rows Δ ann actual n}
    (h : BindingOK free slots ids rows Δ ann actual)
    (bounded : ∀ σ, ann = some σ → ContainsBvarsUpTo (n + σ.paramCount) σ.body)
    (agree : ∀ i < n, slots i = slots' i) :
    BindingOK free slots' ids rows Δ ann actual := by
  cases ann with
  | none => trivial
  | some σ =>
      refine ⟨h.1, AnnotationOK.congrSlots h.2 ?_ agree⟩
      simpa [h.1] using bounded σ rfl

structure Demand (free slots : Nat → BoundsTy) (ids : List Nat) (rows : Bindings)
    (caller : List Nat) (τ : Ty) where
  source : ScopedAnnotation.Decoded ids τ
  decoded : ScopedAnnotation.decode ids τ = .ok source
  finite : Finite rows
  inScope : BoundsScoped caller (read free slots (bounds rows source.bounds))

def Demand.bounds {free slots ids rows caller τ} (d : Demand free slots ids rows caller τ) : BoundsTy :=
  read free slots (CountSubstitution.bounds rows d.source.bounds)

theorem Demand.shape {free slots ids rows caller τ} (d : Demand free slots ids rows caller τ) :
    Synth.BoundsTy.toTy d.bounds = ty free slots τ := by
  rw [Demand.bounds, ScopedHMInterpretation.shape, bounds_shape, d.source.shape, erased]

def decode (free slots : Nat → BoundsTy) (ids : List Nat) (rows : Bindings)
    (caller : List Nat) (τ : Ty) : Except String (Demand free slots ids rows caller τ) := do
  if hf : rows.all (fun row => row.2.noInf) = true then
    match hd : ScopedAnnotation.decode ids τ with
    | .error message => throw message
    | .ok source =>
        if hs : boundsScopedBool caller (read free slots (bounds rows source.bounds)) = true then
          pure ⟨source, hd, fun row hr => Count.noInf_of_isNoInf (List.all_eq_true.mp hf row hr),
            boundsScopedBool_sound hs⟩
        else throw "bounds: lexical HM annotation counts are outside caller scope"
  else throw "bounds: lexical HM annotation interpretation contains an infinite Nat replacement"

def check (free slots : Nat → BoundsTy) (ids : List Nat) (rows : Bindings) (caller : List Nat)
    (Δ : List Constraint) (τ : Ty) (actual : BoundsTy) :
    Except String (PLift (AnnotationOK free slots ids rows Δ τ actual)) := do
  let demand ← decode free slots ids rows caller τ
  let inclusion ← Typed.subtype Δ actual demand.bounds
  pure ⟨demand.source, demand.decoded, inclusion.down⟩

/-! ## Origin-pinned annotation holes

An annotation hole does not introduce an unconstrained semantic assumption.
It copies the already-derived endpoint at the same List node; solid source
counts continue to be interpreted through the declaration's count map.  The
relation below records that provenance independently of the executable
decoder.  In particular, a successful subtype check alone is not accepted as
evidence that a demand came from the written annotation. -/

inductive PinsCount (ids : List Nat) (rows : Bindings) :
    CountSlot → Count → Count → Prop where
  | hole : PinsCount ids rows .hole actual actual
  | solid : Scope.CountScoped ids source →
      PinsCount ids rows (.solid source) actual (CountSubstitution.count rows source)

mutual
inductive Pins (free slots : Nat → BoundsTy) (ids : List Nat) (rows : Bindings) :
    Ty → BoundsTy → BoundsTy → Prop where
  | prim : Pins free slots ids rows (.prim p) actual (.prim p)
  | fvar : Pins free slots ids rows (.fvar i) actual (free i)
  | bvar : Pins free slots ids rows (.bvar i) actual (slots i)
  | arrow :
      Pins free slots ids rows a actualA demandA →
      Pins free slots ids rows b actualB demandB →
      Pins free slots ids rows (.arrow a b) (.arrow actualA actualB) (.arrow demandA demandB)
  | bl :
      PinsCount ids rows lo actualLo demandLo →
      PinsCount ids rows hi actualHi demandHi →
      Pins free slots ids rows elem actualElem demandElem →
      Pins free slots ids rows (.bl lo hi elem) (.list actualLo actualHi actualElem)
        (.list demandLo demandHi demandElem)
  | bareList :
      Pins free slots ids rows elem actualElem demandElem →
      Pins free slots ids rows (.customTy listTyName [elem]) (.list actualLo actualHi actualElem)
        (.list (.lit 0) .inf demandElem)
  | custom : name ≠ listTyName →
      PinsList free slots ids rows args actualArgs demandArgs →
      Pins free slots ids rows (.customTy name args) (.custom name actualArgs)
        (.custom name demandArgs)

inductive PinsList (free slots : Nat → BoundsTy) (ids : List Nat) (rows : Bindings) :
    List Ty → List BoundsTy → List BoundsTy → Prop where
  | nil : PinsList free slots ids rows [] [] []
  | cons :
      Pins free slots ids rows a actual demand →
      PinsList free slots ids rows as actuals demands →
      PinsList free slots ids rows (a :: as) (actual :: actuals) (demand :: demands)
end

private def pinCount (ids : List Nat) (rows : Bindings) (slot : CountSlot)
    (actual : Count) : Except String (Σ demand, PLift (PinsCount ids rows slot actual demand)) := do
  match slot with
  | .hole => pure ⟨actual, ⟨.hole⟩⟩
  | .solid source =>
      if hscoped : countScopedBool ids source = true then
        pure ⟨CountSubstitution.count rows source, ⟨.solid (countScopedBool_sound hscoped)⟩⟩
      else throw "bounds: solid annotation count is outside lexical scope"

mutual
private def pinDemand (free slots : Nat → BoundsTy) (ids : List Nat) (rows : Bindings) :
    (τ : Ty) → (actual : BoundsTy) →
      Except String (Σ demand, PLift (Pins free slots ids rows τ actual demand))
  | .prim p, actual => pure ⟨.prim p, ⟨.prim⟩⟩
  | .fvar i, actual => pure ⟨free i, ⟨.fvar⟩⟩
  | .bvar i, actual => pure ⟨slots i, ⟨.bvar⟩⟩
  | .arrow a b, .arrow actualA actualB => do
      let ⟨demandA, pinnedA⟩ ← pinDemand free slots ids rows a actualA
      let ⟨demandB, pinnedB⟩ ← pinDemand free slots ids rows b actualB
      pure ⟨.arrow demandA demandB, ⟨.arrow pinnedA.down pinnedB.down⟩⟩
  | .arrow _ _, _ => throw "bounds: annotation arrow disagrees with derived origin"
  | .bl lo hi elem, .list actualLo actualHi actualElem => do
      let ⟨demandLo, pinnedLo⟩ ← pinCount ids rows lo actualLo
      let ⟨demandHi, pinnedHi⟩ ← pinCount ids rows hi actualHi
      let ⟨demandElem, pinnedElem⟩ ← pinDemand free slots ids rows elem actualElem
      pure ⟨.list demandLo demandHi demandElem,
        ⟨.bl pinnedLo.down pinnedHi.down pinnedElem.down⟩⟩
  | .bl _ _ _, _ => throw "bounds: BL annotation disagrees with derived List origin"
  | .customTy name [elem], .list actualLo actualHi actualElem => do
      if hn : name = listTyName then
        let ⟨demandElem, pinnedElem⟩ ← pinDemand free slots ids rows elem actualElem
        pure ⟨.list (.lit 0) .inf demandElem, ⟨by
          subst name
          exact .bareList pinnedElem.down⟩⟩
      else throw "bounds: nominal annotation disagrees with derived List origin"
  | .customTy name args, .custom actualName actualArgs => do
      if hn : name = actualName then
        if hl : name = listTyName then
          throw "bounds: malformed List annotation arity"
        else
          let ⟨demands, pinned⟩ ← pinDemandList free slots ids rows args actualArgs
          pure ⟨.custom name demands, ⟨by
            subst actualName
            exact .custom hl pinned.down⟩⟩
      else throw "bounds: annotation nominal name disagrees with derived origin"
  | .customTy name _, _ =>
      if name = listTyName then throw "bounds: malformed or mismatched List annotation"
      else throw "bounds: nominal annotation disagrees with derived origin"

private def pinDemandList (free slots : Nat → BoundsTy) (ids : List Nat) (rows : Bindings) :
    (types : List Ty) → (actuals : List BoundsTy) →
      Except String (Σ demands, PLift (PinsList free slots ids rows types actuals demands))
  | [], [] => pure ⟨[], ⟨.nil⟩⟩
  | ty :: types, actual :: actuals => do
      let ⟨demand, pinned⟩ ← pinDemand free slots ids rows ty actual
      let ⟨demands, pinnedRest⟩ ← pinDemandList free slots ids rows types actuals
      pure ⟨demand :: demands, ⟨.cons pinned.down pinnedRest.down⟩⟩
  | _, _ => throw "bounds: annotation nominal arity disagrees with derived origin"
end

structure Pinned (free slots : Nat → BoundsTy) (ids : List Nat) (rows : Bindings)
    (caller : List Nat) (Δ : List Constraint) (τ : Ty) (actual : BoundsTy) where
  demand : BoundsTy
  provenance : Pins free slots ids rows τ actual demand
  finite : Finite rows
  shape : Synth.BoundsTy.toTy demand = ScopedHMInterpretation.ty free slots τ
  inScope : BoundsScoped caller demand
  inclusion : SemanticSub Δ actual demand

def Pinned.assuming {free slots ids rows caller Δ Δ' τ actual}
    (p : Pinned free slots ids rows caller Δ τ actual)
    (premises : (⟨Δ', Δ⟩ : ForallProblem).Valid) :
    Pinned free slots ids rows caller Δ' τ actual where
  demand := p.demand
  provenance := p.provenance
  finite := p.finite
  shape := p.shape
  inScope := p.inScope
  inclusion := p.inclusion.assuming premises

mutual
/-- Does a carried type contain an endpoint hole that must be filled from an
    already-derived origin rather than decoded as a standalone demand? -/
def hasHole : Ty → Bool
  | .prim _ | .fvar _ | .bvar _ => false
  | .arrow a b => hasHole a || hasHole b
  | .bl lo hi elem =>
      (match lo with | .hole => true | .solid _ => false) ||
      (match hi with | .hole => true | .solid _ => false) || hasHole elem
  | .customTy _ args => hasHoleList args

def hasHoleList : List Ty → Bool
  | [] => false
  | ty :: rest => hasHole ty || hasHoleList rest
end

/-- Fill every annotation hole from a genuine origin, then validate shape,
caller scope and semantic inclusion.  The returned interface is safe to expose
to the binding body; it need not equal the more precise private RHS origin. -/
def pin (free slots : Nat → BoundsTy) (ids : List Nat) (rows : Bindings)
    (caller : List Nat) (Δ : List Constraint) (τ : Ty) (actual : BoundsTy) :
    Except String (Pinned free slots ids rows caller Δ τ actual) := do
  if hfinite : rows.all (fun row => row.2.noInf) = true then
    let ⟨demand, provenance⟩ ← pinDemand free slots ids rows τ actual
    let shape ← match BinderBridge.equalTy (Synth.BoundsTy.toTy demand)
        (ScopedHMInterpretation.ty free slots τ) with
      | some h => pure h
      | none => throw "bounds: pinned annotation disagrees with HM-interpreted source type"
    if hscoped : boundsScopedBool caller demand = true then
      let inclusion ← Typed.subtype Δ actual demand
      pure ⟨demand, provenance.down,
        (fun row member => Count.noInf_of_isNoInf (List.all_eq_true.mp hfinite row member)),
        shape.down, boundsScopedBool_sound hscoped, inclusion.down⟩
    else throw "bounds: pinned annotation counts are outside caller scope"
  else throw "bounds: pinned annotation interpretation contains an infinite Nat replacement"

#print axioms AnnotationOK.types
#print axioms AnnotationOK.counts
#print axioms AnnotationOK.assuming
#print axioms AnnotationOK.congrFree
#print axioms AnnotationOK.congrSlots
#print axioms Pinned.assuming
#print axioms Demand.shape
#print axioms decode
#print axioms check
#print axioms pin

end FHM.Bounds.ScopedHMAnnotation
