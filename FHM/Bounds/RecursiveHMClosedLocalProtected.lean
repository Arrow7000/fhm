import FHM.Bounds.RecursiveHMClosedLocalTargetReady

/-! # Protected specialization maps for capture-closed locals

An actual use of a lambda-lifted local owns its quantified count and HM
arguments.  These arguments must be inserted into the canonical RHS opening
without being interpreted a second time by the enclosing lexical world.  The
maps below are the local counterpart of generalized-group protected maps.
-/

namespace FHM.Bounds.RecursiveHMClosedExit

open RecursiveHMJudgement SchemeSpecialization CountSubstitution ScopedScheme
open RecursiveHMUniform

namespace ProtectedLocal

def sourceUse
    {s : HMCountScheme.Scheme} {calleeDelta : List Constraint} {found : Ty}
    {caller : List Nat}
    (used : HMCountScheme.Use (HMCountSchemeClosure.close s)
      calleeDelta found caller) :=
  HMCountSchemeClosure.sourceUse used

/-- Source-owned quantified arguments shadow the ambient rows. -/
def rows
    {s : HMCountScheme.Scheme} {calleeDelta : List Constraint} {found : Ty}
    {caller : List Nat}
    (used : HMCountScheme.Use (HMCountSchemeClosure.close s)
      calleeDelta found caller)
    (outer : Bindings) : Bindings :=
  (s.counts.quantified.zip (sourceUse used).counts) ++ outer

/-- Opening identities read the actual source-owned arguments; every other
    identity falls through to the ambient HM interpretation. -/
def types
    {s : HMCountScheme.Scheme} {found : Ty} {typeCaptures : List Ty}
    {env : List Binding} {rhs : Expr} {sourceTypes sourceSlots : Nat → BoundsTy}
    (cert : RecursiveHMUniversal.Certified s found typeCaptures env rhs
      sourceTypes sourceSlots)
    {calleeDelta targetFound caller}
    (used : HMCountScheme.Use (HMCountSchemeClosure.close s)
      calleeDelta targetFound caller)
    (ambient : Nat → BoundsTy) (i : Nat) : BoundsTy :=
  match cert.opening.ids.idxOf? i with
  | none => ambient i
  | some slot => SchemeUse.vector (sourceUse used).types slot

theorem rows_finite
    {s : HMCountScheme.Scheme} {calleeDelta : List Constraint} {found : Ty}
    {caller : List Nat}
    (used : HMCountScheme.Use (HMCountSchemeClosure.close s)
      calleeDelta found caller)
    (outer : Bindings) (outerFinite : Finite outer) :
    Finite (rows used outer) := by
  intro row member
  rcases List.mem_append.mp member with head | ambient
  · exact (sourceUse used).countInstance.finiteArgs row.2
      (List.of_mem_zip head).2
  · exact outerFinite row ambient

theorem rows_scoped
    {s : HMCountScheme.Scheme} {calleeDelta : List Constraint} {found : Ty}
    {caller : List Nat}
    (used : HMCountScheme.Use (HMCountSchemeClosure.close s)
      calleeDelta found caller)
    (outer : Bindings) (target : List Nat)
    (outerScope : ∀ row ∈ outer, Scope.CountScoped target row.2) :
    ∀ row ∈ rows used outer,
      Scope.CountScoped ((s.counts.captures ++ caller) ++ target) row.2 := by
  intro row member
  rcases List.mem_append.mp member with head | ambient
  · exact HMInterpretation.count_mono
      ((sourceUse used).countInstance.argsScoped row.2 (List.of_mem_zip head).2)
      (fun _ present => List.mem_append_left _ present)
  · exact HMInterpretation.count_mono (outerScope row ambient)
      (fun _ present => List.mem_append_right _ present)

theorem types_lc
    {s : HMCountScheme.Scheme} {found : Ty} {typeCaptures : List Ty}
    {env : List Binding} {rhs : Expr} {sourceTypes sourceSlots : Nat → BoundsTy}
    (cert : RecursiveHMUniversal.Certified s found typeCaptures env rhs
      sourceTypes sourceSlots)
    {calleeDelta targetFound caller}
    (used : HMCountScheme.Use (HMCountSchemeClosure.close s)
      calleeDelta targetFound caller)
    (ambient : Nat → BoundsTy)
    (ambientLC : ∀ i, (Synth.BoundsTy.toTy (ambient i)).IsLC) :
    ∀ i, (Synth.BoundsTy.toTy (types cert used ambient i)).IsLC := by
  intro i
  unfold types
  cases cert.opening.ids.idxOf? i with
  | none => exact ambientLC i
  | some slot =>
      exact RecursiveHMUniversal.argumentsLC (sourceUse used).types
        (sourceUse used).typesLC slot

theorem types_supported
    {s : HMCountScheme.Scheme} {found : Ty} {typeCaptures : List Ty}
    {env : List Binding} {rhs : Expr} {sourceTypes sourceSlots : Nat → BoundsTy}
    (cert : RecursiveHMUniversal.Certified s found typeCaptures env rhs
      sourceTypes sourceSlots)
    {calleeDelta targetFound caller}
    (used : HMCountScheme.Use (HMCountSchemeClosure.close s)
      calleeDelta targetFound caller)
    (ambient : Nat → BoundsTy)
    (arguments : ∀ a ∈ used.types, Runtime.Supported a)
    (ambientSupported : ∀ i, Runtime.Supported (ambient i)) :
    ∀ i, Runtime.Supported (types cert used ambient i) := by
  intro i
  unfold types
  cases located : cert.opening.ids.idxOf? i with
  | none => exact ambientSupported i
  | some slot =>
      cases atIndex : (sourceUse used).types[slot]? with
      | none =>
          simp only [SchemeUse.vector, atIndex, Option.getD_none]
          exact .prim
      | some a =>
          simp only [SchemeUse.vector, atIndex, Option.getD_some]
          exact arguments a (List.mem_of_mem_drop (List.mem_of_getElem? atIndex))

theorem types_scoped
    {s : HMCountScheme.Scheme} {found : Ty} {typeCaptures : List Ty}
    {env : List Binding} {rhs : Expr} {sourceTypes sourceSlots : Nat → BoundsTy}
    (cert : RecursiveHMUniversal.Certified s found typeCaptures env rhs
      sourceTypes sourceSlots)
    {calleeDelta targetFound caller}
    (used : HMCountScheme.Use (HMCountSchemeClosure.close s)
      calleeDelta targetFound caller)
    (ambient : Nat → BoundsTy) (target : List Nat)
    (ambientScope : ∀ i, BoundsScoped target (ambient i)) :
    ∀ i, BoundsScoped ((s.counts.captures ++ caller) ++ target)
      (types cert used ambient i) := by
  intro i
  unfold types
  cases cert.opening.ids.idxOf? i with
  | none =>
      exact HMInterpretation.scope_mono (ambientScope i)
        (fun _ present => List.mem_append_right _ present)
  | some slot =>
      exact HMInterpretation.scope_mono
        (SchemeUse.vector_scope (sourceUse used).typesScoped slot)
        (fun _ present => List.mem_append_left _ present)

theorem types_openingSlot
    {s : HMCountScheme.Scheme} {found : Ty} {typeCaptures : List Ty}
    {env : List Binding} {rhs : Expr} {sourceTypes sourceSlots : Nat → BoundsTy}
    (cert : RecursiveHMUniversal.Certified s found typeCaptures env rhs
      sourceTypes sourceSlots)
    {calleeDelta targetFound caller}
    (used : HMCountScheme.Use (HMCountSchemeClosure.close s)
      calleeDelta targetFound caller)
    (ambient : Nat → BoundsTy) (slot : Nat) (inside : slot < cert.opening.ids.length) :
    types cert used ambient cert.opening.ids[slot] =
      SchemeUse.vector (sourceUse used).types slot := by
  have exactSlot := SchemeSpecialization.argument_slot cert.opening.ids
    (SchemeUse.vector (sourceUse used).types) cert.opening.distinct slot inside
  unfold types
  cases located : cert.opening.ids.idxOf? cert.opening.ids[slot] with
  | none => exact False.elim ((List.idxOf?_eq_none_iff.mp located) (List.getElem_mem inside))
  | some position =>
      simpa only [SchemeSpecialization.argument, located] using exactSlot

theorem types_sourceAmbient
    {s : HMCountScheme.Scheme} {found : Ty} {typeCaptures : List Ty}
    {env : List Binding} {rhs : Expr} {sourceTypes sourceSlots : Nat → BoundsTy}
    (cert : RecursiveHMUniversal.Certified s found typeCaptures env rhs
      sourceTypes sourceSlots)
    {calleeDelta targetFound caller}
    (used : HMCountScheme.Use (HMCountSchemeClosure.close s)
      calleeDelta targetFound caller)
    (ambient : Nat → BoundsTy) (i : Nat) (free : i ∈ s.hm.body.freeVars) :
    types cert used ambient i = ambient i := by
  unfold types
  rw [List.idxOf?_eq_none_iff.mpr]
  intro present
  exact cert.opening.fresh i present s.hm.body List.mem_cons_self free

/-- Closed target premises are exactly the source premises interpreted under
    the protected rows. -/
theorem premises
    {s : HMCountScheme.Scheme} {calleeDelta : List Constraint} {found : Ty}
    {caller : List Nat}
    (used : HMCountScheme.Use (HMCountSchemeClosure.close s)
      calleeDelta found caller)
    (outer : Bindings) (ambient : Nat → BoundsTy)
    (captures : HMCountSchemeClosure.CapturesAgree s outer ambient used) :
    (HMCountSchemeClosure.close s).counts.premises.map
        (constraint ((HMCountSchemeClosure.close s).counts.quantified.zip used.counts)) =
      s.counts.premises.map (constraint (rows used outer)) := by
  exact HMCountSchemeClosure.closedUse_premises_protected used outer ambient captures

theorem usable
    {s : HMCountScheme.Scheme} {calleeDelta : List Constraint} {found : Ty}
    {caller : List Nat}
    (used : HMCountScheme.Use (HMCountSchemeClosure.close s)
      calleeDelta found caller)
    (outer : Bindings) (ambient : Nat → BoundsTy)
    (captures : HMCountSchemeClosure.CapturesAgree s outer ambient used) :
    (⟨calleeDelta, s.counts.premises.map (constraint (rows used outer))⟩ :
      ForallProblem).Valid := by
  exact HMCountSchemeClosure.closedUse_usable_protected used outer ambient captures

/-- The canonical opening demand under the protected maps is the demand of
    the actual target closed use. -/
theorem demand
    {s : HMCountScheme.Scheme} {found : Ty} {typeCaptures : List Ty}
    {env : List Binding} {rhs : Expr} {sourceTypes sourceSlots : Nat → BoundsTy}
    (cert : RecursiveHMUniversal.Certified s found typeCaptures env rhs
      sourceTypes sourceSlots)
    {calleeDelta targetFound caller}
    (used : HMCountScheme.Use (HMCountSchemeClosure.close s)
      calleeDelta targetFound caller)
    (outer : Bindings) (ambient : Nat → BoundsTy)
    (ambientLC : ∀ i, (Synth.BoundsTy.toTy (ambient i)).IsLC)
    (captures : HMCountSchemeClosure.CapturesAgree s outer ambient used) :
    mapFree (types cert used ambient) (bounds (rows used outer) cert.opening.bounds) =
      used.bounds := by
  let source := sourceUse used
  have sourceLength : source.types.length = cert.opening.ids.length := by
    rw [cert.opening.arity, source.arity]
  have openingArgs :
      (fun i => mapFree (types cert used ambient)
        (bounds (rows used outer) (SchemeUse.vector (cert.opening.ids.map BoundsTy.fvar) i))) =
        SchemeUse.vector source.types := by
    funext i
    by_cases inside : i < cert.opening.ids.length
    · have sourceInside : i < source.types.length := by omega
      rw [show SchemeUse.vector (cert.opening.ids.map BoundsTy.fvar) i =
          .fvar cert.opening.ids[i] by simp [SchemeUse.vector, inside]]
      simp only [bounds, mapFree]
      rw [types_openingSlot cert used ambient i inside]
    · have sourceOutside : i ≥ source.types.length := by omega
      rw [show SchemeUse.vector (cert.opening.ids.map BoundsTy.fvar) i = .prim .unit by
          simp [SchemeUse.vector, inside],
        show SchemeUse.vector source.types i = .prim .unit by
          simp [SchemeUse.vector, sourceOutside]]
      rfl
  have sourceMap :
      mapFree (types cert used ambient) (bounds (rows used outer) s.counts.body) =
        mapFree ambient (bounds (rows used outer) s.counts.body) := by
    apply FreeAlgebra.congrFree
    intro i member
    apply types_sourceAmbient cert used ambient i
    rw [bounds_shape, s.shape] at member
    exact member
  have rowsPromoted :
      bounds (rows used outer) s.counts.body =
        bounds ((s.counts.quantified ++ HMCountSchemeClosure.countCaptures s).zip
          ((sourceUse used).counts ++
            HMCountSchemeClosure.interpretedCountCaptures outer s)) s.counts.body := by
    simpa only [rows, sourceUse, HMCountSchemeClosure.interpretedCountCaptures] using
      HMCountSchemeClosure.bounds_protected outer s.counts.quantified
        (HMCountSchemeClosure.countCaptures s) (sourceUse used).counts
        (HMCountSchemeClosure.nodup_eraseDups _)
        (HMCountSchemeClosure.closedUse_sourceCountLength used).symm
        (HMCountSchemeClosure.boundsScope_mono s.countWF.2.2.1
          (HMCountSchemeClosure.promoted_subset s))
  calc
    mapFree (types cert used ambient) (bounds (rows used outer) cert.opening.bounds) =
        mapFree (types cert used ambient)
          (bounds (rows used outer) (TypeSubstitution.substitute
            (SchemeUse.vector (cert.opening.ids.map BoundsTy.fvar)) s.counts.body)) := rfl
    _ = mapFree (types cert used ambient)
          (TypeSubstitution.substitute
            (fun i => bounds (rows used outer)
              (SchemeUse.vector (cert.opening.ids.map BoundsTy.fvar) i))
            (bounds (rows used outer) s.counts.body)) := by
      rw [CountTransport.instantiate_commute]
    _ = TypeSubstitution.substitute
          (fun i => mapFree (types cert used ambient)
            (bounds (rows used outer)
              (SchemeUse.vector (cert.opening.ids.map BoundsTy.fvar) i)))
          (mapFree (types cert used ambient) (bounds (rows used outer) s.counts.body)) := by
      rw [FreeAlgebra.instantiate_commute _ (types_lc cert used ambient ambientLC)]
    _ = TypeSubstitution.substitute (SchemeUse.vector source.types)
          (mapFree ambient (bounds (rows used outer) s.counts.body)) := by
      rw [openingArgs, sourceMap]
    _ = TypeSubstitution.substitute (SchemeUse.vector source.types)
          (mapFree ambient
            (bounds ((s.counts.quantified ++ HMCountSchemeClosure.countCaptures s).zip
              ((sourceUse used).counts ++
                HMCountSchemeClosure.interpretedCountCaptures outer s))
              s.counts.body)) := by
      rw [rowsPromoted]
    _ = used.bounds := by
      exact (HMCountSchemeClosure.closedUse_bounds used outer ambient ambientLC captures).symm

/-- The canonical implementation-to-demand inclusion transports through the
    same protected maps and lands at the actual target-use demand. -/
theorem inclusion
    {s : HMCountScheme.Scheme} {found : Ty} {typeCaptures : List Ty}
    {env : List Binding} {rhs : Expr} {sourceTypes sourceSlots : Nat → BoundsTy}
    (cert : RecursiveHMUniversal.Certified s found typeCaptures env rhs
      sourceTypes sourceSlots)
    {calleeDelta targetFound caller}
    (used : HMCountScheme.Use (HMCountSchemeClosure.close s)
      calleeDelta targetFound caller)
    (outer : Bindings) (outerFinite : Finite outer)
    (ambient : Nat → BoundsTy)
    (ambientLC : ∀ i, (Synth.BoundsTy.toTy (ambient i)).IsLC)
    (captures : HMCountSchemeClosure.CapturesAgree s outer ambient used) :
    SemanticSub (s.counts.premises.map (constraint (rows used outer)))
      (mapFree (types cert used ambient) (bounds (rows used outer) cert.actual))
      used.bounds := by
  have counted := CountSubstitution.subtype (rows used outer)
    (rows_finite used outer outerFinite) cert.inclusion
  have mapped := SchemeSpecialization.subtype (types cert used ambient) counted
  rw [demand cert used outer ambient ambientLC captures] at mapped
  exact mapped

end ProtectedLocal

#print axioms ProtectedLocal.rows_finite
#print axioms ProtectedLocal.rows_scoped
#print axioms ProtectedLocal.types_lc
#print axioms ProtectedLocal.types_supported
#print axioms ProtectedLocal.types_scoped
#print axioms ProtectedLocal.premises
#print axioms ProtectedLocal.usable
#print axioms ProtectedLocal.demand
#print axioms ProtectedLocal.inclusion

end FHM.Bounds.RecursiveHMClosedExit
