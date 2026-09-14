import FHM.Bounds.RecursiveContract
import FHM.Bounds.CountTransport
import FHM.Bounds.RecursiveCountTransport

/-! # Recursive assumptions with closed templates and fixed HM arguments

The HM argument vector belongs to the group interface, not to each recursive
call. Counts are substituted in the closed template before that vector is
inserted. This preserves caller-owned counts inside complete HM bounds arguments.

These certificates are assumptions only. They do not accept an RHS, introduce
a recursive group, or enable polymorphic recursion in the existing walker.
-/

namespace FHM.Bounds.RecursiveHMContract

open HMCountScheme ScopedScheme CountSubstitution SchemeSpecialization

structure Fixed (s : HMCountScheme.Scheme) (found : Ty) where
  types : List BoundsTy
  arity : types.length = s.hm.paramCount
  typesLC : ∀ a ∈ types, (Synth.BoundsTy.toTy a).IsLC
  shape : Synth.BoundsTy.toTy (opened s types) = found.eraseBounds
  lc : found.eraseBounds.IsLC

def fromOpaque {s found captures} (o : Opening s found captures) : Fixed s found :=
  ⟨o.ids.map BoundsTy.fvar, by simpa using o.arity, by
      intro a ha
      obtain ⟨i, _, rfl⟩ := List.mem_map.mp ha
      exact (Ty.bvarsBelow_iff _).mp (by simp [Synth.BoundsTy.toTy, Ty.bvarsBelow]),
    o.shape, o.lc⟩

/-- Reconcile a single fixed vector with the authoritative group HM artifact.
    Count scope is checked at uses, separately from the callee telescope. -/
def fix (s : HMCountScheme.Scheme) (found : Ty) (types : List BoundsTy) :
    Except String (Fixed s found) := do
  if ha : types.length = s.hm.paramCount then
    if hl : types.all (fun a => (Synth.BoundsTy.toTy a).bvarsBelow 0) = true then
      let shape ← match BinderBridge.equalTy (Synth.BoundsTy.toTy (opened s types)) found.eraseBounds with
        | some h => pure h
        | none => throw "bounds: fixed recursive HM arguments disagree with group monotype"
      if hc : found.eraseBounds.bvarsBelow 0 = true then
        pure ⟨types, ha, fun a hm => (Ty.bvarsBelow_iff _).mp (List.all_eq_true.mp hl a hm),
          shape.down, (Ty.bvarsBelow_iff _).mp hc⟩
      else throw "bounds: fixed recursive group monotype contains an enclosing bound slot"
    else throw "bounds: fixed recursive HM argument contains an enclosing bound slot"
  else throw "bounds: fixed recursive HM argument vector has wrong arity"

structure Use {s fixedFound} (c : Fixed s fixedFound) (Δ : List Constraint)
    (found : Ty) (caller : List Nat) where
  counts : List Count
  inst : Instance s.counts counts caller
  usable : inst.Usable Δ
  typesScoped : c.types.all (boundsScopedBool caller) = true
  fixedHM : fixedFound.eraseBounds = found.eraseBounds

def Use.bounds {s fixedFound Δ found caller} {c : Fixed s fixedFound}
    (u : Use c Δ found caller) : BoundsTy :=
  TypeSubstitution.combined (s.counts.quantified.zip u.counts) (SchemeUse.vector c.types) s.counts.body

def Use.external {s fixedFound Δ found caller} {c : Fixed s fixedFound}
    (u : Use c Δ found caller) : HMCountScheme.Use s Δ found caller :=
  ⟨u.counts, u.inst, u.usable, c.types, c.arity, c.typesLC, u.typesScoped, by
    simpa only [TypeSubstitution.combined, TypeSubstitution.shape, bounds_shape, opened] using
      c.shape.trans u.fixedHM⟩

theorem Use.shape {s fixedFound Δ found caller} {c : Fixed s fixedFound}
    (u : Use c Δ found caller) : Synth.BoundsTy.toTy u.bounds = found.eraseBounds := u.external.shape

theorem Use.inScope {s fixedFound Δ found caller} {c : Fixed s fixedFound}
    (u : Use c Δ found caller) : BoundsScoped caller u.bounds := u.external.inScope

theorem Use.subtype {s fixedFound Δ found caller} {c : Fixed s fixedFound}
    (u : Use c Δ found caller) {a b} (h : SemanticSub s.counts.premises a b) :
    SemanticSub Δ
      (TypeSubstitution.combined (s.counts.quantified.zip u.counts) (SchemeUse.vector c.types) a)
      (TypeSubstitution.combined (s.counts.quantified.zip u.counts) (SchemeUse.vector c.types) b) :=
  u.external.subtype h

/-- There is deliberately no HM argument input at a recursive call. -/
def check {s fixedFound} (c : Fixed s fixedFound) (Δ : List Constraint)
    (found : Ty) (counts : List Count) (caller : List Nat) : Except String (Use c Δ found caller) := do
  let inst ← s.counts.instantiate counts caller
  let usable ← inst.checkPremises Δ
  if hs : c.types.all (boundsScopedBool caller) = true then
    let fixed ← match BinderBridge.equalTy fixedFound.eraseBounds found.eraseBounds with
      | some h => pure h
      | none => throw "bounds: recursive call changes the group's fixed HM argument vector"
    pure ⟨counts, inst, usable.down, hs, fixed.down⟩
  else throw "bounds: fixed recursive HM argument counts are outside caller scope"

private theorem vector_map (f : Nat → BoundsTy) (types : List BoundsTy) (i : Nat) :
    SchemeUse.vector (types.map (mapFree f)) i = mapFree f (SchemeUse.vector types i) := by
  cases h : types[i]? <;> simp [SchemeUse.vector, List.getElem?_map, h, mapFree]

/-- Holding captured free HM identities fixed preserves the entire closed
    template, even after count instantiation. Inserted types remain separate. -/
theorem map_combined (s : HMCountScheme.Scheme) (types : List BoundsTy)
    (rows : Bindings) (f : Nat → BoundsTy)
    (hf : ∀ i, (Synth.BoundsTy.toTy (f i)).IsLC)
    (captured : ∀ i ∈ s.hm.body.freeVars, f i = .fvar i) :
    mapFree f (TypeSubstitution.combined rows (SchemeUse.vector types) s.counts.body) =
      TypeSubstitution.combined rows (SchemeUse.vector (types.map (mapFree f))) s.counts.body := by
  have fixed : mapFree f (bounds rows s.counts.body) = bounds rows s.counts.body :=
    SchemeSpecialization.fixed (by simpa only [bounds_shape, s.shape] using captured)
  rw [TypeSubstitution.combined, FreeAlgebra.instantiate_commute f hf, fixed]
  congr 1
  funext i
  exact (vector_map f types i).symm

theorem map_opened (s : HMCountScheme.Scheme) (types : List BoundsTy)
    (f : Nat → BoundsTy) (hf : ∀ i, (Synth.BoundsTy.toTy (f i)).IsLC)
    (captured : ∀ i ∈ s.hm.body.freeVars, f i = .fvar i) :
    mapFree f (opened s types) = opened s (types.map (mapFree f)) := by
  have fixed : mapFree f s.counts.body = s.counts.body :=
    SchemeSpecialization.fixed (by simpa only [s.shape] using captured)
  rw [opened, FreeAlgebra.instantiate_commute f hf, fixed]
  congr 1
  funext i
  exact (vector_map f types i).symm

/-- Mapping the fixed vector is total even when a template captures free HM
    identities. Equality with mapping an entire use additionally needs those
    captures fixed; the transport theorem checks that premise separately. -/
def Fixed.mapTypes {s found} (c : Fixed s found) (f : Nat → BoundsTy)
    (hf : ∀ i, (Synth.BoundsTy.toTy (f i)).IsLC) :
    Fixed s (Synth.BoundsTy.toTy (opened s (c.types.map (mapFree f)))) := by
  have argsLC : ∀ a ∈ c.types.map (mapFree f), (Synth.BoundsTy.toTy a).IsLC := by
    intro a ha
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
    exact FreeAlgebra.bvars f hf (c.typesLC b hb)
  refine ⟨c.types.map (mapFree f), by simpa using c.arity, argsLC,
    (FreeAlgebra.shape_erased _).symm, ?_⟩
  rw [FreeAlgebra.shape_erased, opened, TypeSubstitution.shape, s.shape]
  apply Ty.instantiate_isLC (n := s.hm.paramCount) _ s.hmWF
  intro i _
  cases h : (c.types.map (mapFree f))[i]? with
  | none => simp [SchemeUse.vector, h, Synth.BoundsTy.toTy, Ty.IsLC]; exact .prim
  | some a => simpa only [SchemeUse.vector, h, Option.getD_some] using argsLC a (List.mem_of_getElem? h)

/-- Before full caller bounds replace the opaque HM identities, the new
    count-first interface agrees exactly with the existing recursive rule. -/
theorem opaque_count_coherence {s found captures} (o : Opening s found captures)
    (rows : Bindings) :
    TypeSubstitution.combined rows (SchemeUse.vector (fromOpaque o).types) s.counts.body =
      bounds rows o.bounds := by
  rw [Opening.bounds, opened, CountTransport.instantiate_commute]
  change TypeSubstitution.substitute (SchemeUse.vector (o.ids.map BoundsTy.fvar)) (bounds rows s.counts.body) =
    TypeSubstitution.substitute (fun i => bounds rows (SchemeUse.vector (o.ids.map BoundsTy.fvar) i))
      (bounds rows s.counts.body)
  congr 1
  funext i
  cases h : o.ids[i]? <;>
    simp [SchemeUse.vector, List.getElem?_map, h, bounds]

/-- Specialize the whole fixed group interface once; recursive calls continue
    using its one resulting vector, with no per-call HM re-instantiation. -/
def Fixed.map {s found} (c : Fixed s found) (f : Nat → BoundsTy)
    (hf : ∀ i, (Synth.BoundsTy.toTy (f i)).IsLC)
    (captured : ∀ i ∈ s.hm.body.freeVars, f i = .fvar i) :
    Fixed s (Synth.BoundsTy.toTy (mapFree f (opened s c.types))) :=
  ⟨c.types.map (mapFree f), by simpa using c.arity, by
      intro a ha
      obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
      exact FreeAlgebra.bvars f hf (c.typesLC b hb),
    by rw [← map_opened s c.types f hf captured, FreeAlgebra.shape_erased],
    by
      rw [FreeAlgebra.shape_erased]
      apply FreeAlgebra.bvars f hf
      rw [c.shape]
      exact c.lc⟩

/-- A recursive-assumption use transports with unchanged count witnesses and
    premises. Caller scope of the complete inserted types remains explicit. -/
def Use.map {s fixedFound Δ found caller} {c : Fixed s fixedFound}
    (u : Use c Δ found caller) (f : Nat → BoundsTy)
    (hf : ∀ i, (Synth.BoundsTy.toTy (f i)).IsLC)
    (captured : ∀ i ∈ s.hm.body.freeVars, f i = .fvar i)
    (scope : (c.types.map (mapFree f)).all (boundsScopedBool caller) = true) :
    Use (c.map f hf captured) Δ (Synth.BoundsTy.toTy (mapFree f (opened s c.types))) caller :=
  ⟨u.counts, u.inst, u.usable, scope, rfl⟩

theorem Use.map_bounds {s fixedFound Δ found caller} {c : Fixed s fixedFound}
    (u : Use c Δ found caller) (f : Nat → BoundsTy)
    (hf : ∀ i, (Synth.BoundsTy.toTy (f i)).IsLC)
    (captured : ∀ i ∈ s.hm.body.freeVars, f i = .fvar i)
    (scope : (c.types.map (mapFree f)).all (boundsScopedBool caller) = true) :
    (u.map f hf captured scope).bounds = mapFree f u.bounds :=
  (map_combined s c.types _ f hf captured).symm

/-- Outer count interpretation affects counts in the caller-owned HM vector,
    not the callee's protected closed template or its fixed HM shape. -/
def Fixed.mapCounts {s found} (c : Fixed s found) (outer : Bindings) : Fixed s found :=
  ⟨c.types.map (bounds outer), by simpa using c.arity, by
      intro a ha
      obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
      rw [bounds_shape]
      exact c.typesLC b hb,
    by simpa only [opened, TypeSubstitution.shape, CountTransport.vector_mapped, bounds_shape] using c.shape,
    c.lc⟩

/-- Finite count transport maps caller count arguments and caller-owned types
    together, while protecting the callee telescope and captured coordinates. -/
def Use.mapCounts {s fixedFound Δ found caller} {c : Fixed s fixedFound}
    (u : Use c Δ found caller) (outer : Bindings) (hf : Finite outer) (target : List Nat)
    (hs : ∀ row ∈ outer, Scope.CountScoped target row.2)
    (hk : ∀ i ∈ s.counts.captures, lookup outer i = none) :
    Use (c.mapCounts outer) (Δ.map (constraint outer)) found (caller ++ target) := by
  refine ⟨u.counts.map (count outer),
    RecursiveCountTransport.instanceTransport u.inst outer hf target hs hk,
    RecursiveCountTransport.usable_transport u.inst u.usable outer hf target hs hk, ?_, u.fixedHM⟩
  apply List.all_eq_true.mpr
  intro a ha
  obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
  apply boundsScopedBool_complete
  exact bounds_scoped (boundsScopedBool_sound (List.all_eq_true.mp u.typesScoped b hb))
    (fun row hr => RecursiveCountTransport.scope_mono (hs row hr)
      (fun _ hi => List.mem_append_right _ hi))
    (fun _ hi _ => List.mem_append_left _ hi)

theorem Use.mapCounts_bounds {s fixedFound Δ found caller} {c : Fixed s fixedFound}
    (u : Use c Δ found caller) (outer : Bindings) (hf : Finite outer) (target : List Nat)
    (hs : ∀ row ∈ outer, Scope.CountScoped target row.2)
    (hk : ∀ i ∈ s.counts.captures, lookup outer i = none) :
    (u.mapCounts outer hf target hs hk).bounds = CountSubstitution.bounds outer u.bounds := by
  change TypeSubstitution.substitute (SchemeUse.vector (c.types.map (CountSubstitution.bounds outer)))
      (CountSubstitution.bounds (s.counts.quantified.zip (u.counts.map (count outer))) s.counts.body) =
    CountSubstitution.bounds outer (TypeSubstitution.substitute (SchemeUse.vector c.types) u.inst.bounds)
  rw [CountTransport.instantiate_commute, RecursiveCountTransport.bounds_transport u.inst outer hk]
  congr 1
  funext i
  exact CountTransport.vector_mapped outer c.types i

#print axioms fix
#print axioms fromOpaque
#print axioms Use.shape
#print axioms Use.inScope
#print axioms Use.subtype
#print axioms check
#print axioms map_combined
#print axioms opaque_count_coherence
#print axioms Fixed.map
#print axioms Use.map
#print axioms Use.map_bounds
#print axioms Fixed.mapCounts
#print axioms Use.mapCounts
#print axioms Use.mapCounts_bounds

end FHM.Bounds.RecursiveHMContract
