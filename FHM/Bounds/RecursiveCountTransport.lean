import FHM.Bounds.RecursiveTyping

/-! # Count transport across a recursive contract's protected telescope

An outer interpretation changes caller count arguments, not a callee's bound
coordinates. Captures must be fixed. This applies even when an outer selected
identity coincides with a callee's quantified identity (the self-recursive case).
No HM identities are substituted and no contract premise is silently assumed.
-/

namespace FHM.Bounds.RecursiveCountTransport

open CountSubstitution ScopedScheme

private theorem lookup_mapped (outer rows : Bindings) (i : Nat) :
    lookup (rows.map (Prod.map id (count outer))) i =
      (lookup rows i).map (count outer) := by
  induction rows with
  | nil => rfl
  | cons row rest ih =>
      rcases row with ⟨key, value⟩
      simp only [List.map_cons, lookup, Prod.map_fst, Prod.map_snd, id_eq]
      split
      · rfl
      · exact ih

private theorem lookup_scoped {s args caller} (inst : Instance s args caller)
    (outer : Bindings) (hk : ∀ i ∈ s.captures, lookup outer i = none) :
    ∀ i ∈ s.quantified ++ s.captures,
      lookup (CountAlgebra.compose outer (s.quantified.zip args)) i =
        lookup (s.quantified.zip (args.map (count outer))) i := by
  intro i hi
  rw [CountAlgebra.lookup_compose, List.zip_map_right]
  rw [lookup_mapped]
  rcases List.mem_append.mp hi with hq | hc
  · cases hl : lookup (s.quantified.zip args) i with
    | some a => rfl
    | none =>
        have absent := lookup_none_iff.mp hl
        rw [List.map_fst_zip (Nat.le_of_eq inst.arity)] at absent
        exact False.elim (absent hq)
  · have hl : lookup (s.quantified.zip args) i = none := by
      apply lookup_none
      rw [List.map_fst_zip (Nat.le_of_eq inst.arity)]
      exact inst.wf.2.1 i hc
    simp only [hl, hk i hc, Option.map_none]

private theorem count_congr {ids a rows rows'} (ha : Scope.CountScoped ids a)
    (he : ∀ i ∈ ids, lookup rows i = lookup rows' i) : count rows a = count rows' a := by
  induction a with
  | lit | inf => rfl
  | var v =>
      cases v with | mk kind i =>
        cases kind with
        | inferable => cases ha
        | rigid => simp only [count, he i ha]
  | add a b ihA ihB | mul a b ihA ihB | min a b ihA ihB | max a b ihA ihB =>
      simp only [count, ihA ha.1, ihB ha.2]
  | pred a ih => simp only [count, ih ha]

mutual
private theorem bounds_congr {ids a rows rows'} (ha : BoundsScoped ids a)
    (he : ∀ i ∈ ids, lookup rows i = lookup rows' i) : bounds rows a = bounds rows' a := by
  cases a with
  | prim | fvar | bvar => rfl
  | arrow a b => simp only [bounds, bounds_congr ha.1 he, bounds_congr ha.2 he]
  | list lo hi elem =>
      simp only [bounds, count_congr ha.1 he, count_congr ha.2.1 he, bounds_congr ha.2.2 he]
  | custom name as => exact congrArg (BoundsTy.custom name) (list_congr ha he)
termination_by sizeOf a

private theorem list_congr {ids as rows rows'} (ha : BoundsListScoped ids as)
    (he : ∀ i ∈ ids, lookup rows i = lookup rows' i) : boundsList rows as = boundsList rows' as := by
  cases as with
  | nil => rfl
  | cons a as => simp only [boundsList, bounds_congr ha.1 he, list_congr ha.2 he]
termination_by sizeOf as
end

/-- Transport changes the caller arguments, including self-recursive arguments,
    while leaving the callee's quantified body unchanged. -/
theorem bounds_transport {s args caller} (inst : Instance s args caller)
    (outer : Bindings) (hk : ∀ i ∈ s.captures, lookup outer i = none) :
    bounds outer inst.bounds = bounds (s.quantified.zip (args.map (count outer))) s.body := by
  rw [Instance.bounds, ← CountAlgebra.bounds_compose]
  exact bounds_congr inst.wf.2.2.1 (lookup_scoped inst outer hk)

private theorem constraint_transport {s args caller} (inst : Instance s args caller)
    (outer : Bindings) (hk : ∀ i ∈ s.captures, lookup outer i = none) {c : Constraint}
    (hc : ConstraintScoped (s.quantified ++ s.captures) c) :
    constraint outer (constraint (s.quantified.zip args) c) =
      constraint (s.quantified.zip (args.map (count outer))) c := by
  cases c with | mk lhs rhs =>
    simp only [constraint]
    rw [← CountAlgebra.count_compose, ← CountAlgebra.count_compose]
    congr 1
    · exact count_congr hc.1 (lookup_scoped inst outer hk)
    · exact count_congr hc.2 (lookup_scoped inst outer hk)

theorem premises_transport {s args caller} (inst : Instance s args caller)
    (outer : Bindings) (hk : ∀ i ∈ s.captures, lookup outer i = none) :
    inst.premises.map (constraint outer) =
      s.premises.map (constraint (s.quantified.zip (args.map (count outer)))) := by
  rw [Instance.premises, List.map_map]
  apply List.map_congr_left
  intro c hc
  exact constraint_transport inst outer hk (inst.wf.2.2.2 c hc)

private theorem scope_mono {ids ids' c} (h : Scope.CountScoped ids c)
    (hk : ∀ i ∈ ids, i ∈ ids') : Scope.CountScoped ids' c := by
  induction c with
  | lit | inf => trivial
  | var v =>
      cases v with | mk kind i =>
        cases kind with
        | inferable => cases h
        | rigid => exact hk i h
  | add a b ihA ihB | mul a b ihA ihB | min a b ihA ihB | max a b ihA ihB =>
      exact ⟨ihA h.1, ihB h.2⟩
  | pred a ih => exact ih h

/-- Preserve the previous caller scope and add the replacement scope. This
    avoids requiring unused coordinates in a carried caller interface to be
    removed, and never admits inferable counts or infinite Nat arguments. -/
def instanceTransport {s args caller} (inst : Instance s args caller)
    (outer : Bindings) (hf : Finite outer) (target : List Nat)
    (hs : ∀ row ∈ outer, Scope.CountScoped target row.2)
    (hk : ∀ i ∈ s.captures, lookup outer i = none) :
    Instance s (args.map (count outer)) (caller ++ target) := by
  have scopedRows : ∀ row ∈ outer, Scope.CountScoped (caller ++ target) row.2 :=
    fun row hr => scope_mono (hs row hr) (fun _ hi => List.mem_append_right _ hi)
  have keep : ∀ i ∈ caller, lookup outer i = none → i ∈ caller ++ target :=
    fun _ hi _ => List.mem_append_left _ hi
  refine
    { wf := inst.wf
      arity := by simpa only [List.length_map] using inst.arity
      finiteArgs := ?_
      argsScoped := ?_
      capturesScoped := fun _ hi => List.mem_append_left _ (inst.capturesScoped _ hi)
      bodyScoped := ?_
      premisesScoped := ?_ }
  · intro a ha
    obtain ⟨original, hm, rfl⟩ := List.mem_map.mp ha
    exact CountAlgebra.count_noInf outer hf (inst.finiteArgs original hm)
  · intro a ha
    obtain ⟨original, hm, rfl⟩ := List.mem_map.mp ha
    exact count_scoped (inst.argsScoped original hm) scopedRows keep
  · rw [← bounds_transport inst outer hk]
    exact bounds_scoped inst.bodyScoped scopedRows keep
  · intro c hc
    rw [← premises_transport inst outer hk] at hc
    obtain ⟨original, hm, rfl⟩ := List.mem_map.mp hc
    exact ⟨count_scoped (inst.premisesScoped original hm).1 scopedRows keep,
      count_scoped (inst.premisesScoped original hm).2 scopedRows keep⟩

theorem usable_transport {s args caller Δ} (inst : Instance s args caller)
    (hu : inst.Usable Δ) (outer : Bindings) (hf : Finite outer) (target : List Nat)
    (hs : ∀ row ∈ outer, Scope.CountScoped target row.2)
    (hk : ∀ i ∈ s.captures, lookup outer i = none) :
    (instanceTransport inst outer hf target hs hk).Usable (Δ.map (constraint outer)) := by
  have transported := CountSubstitution.valid outer hf hu
  change (⟨Δ.map (constraint outer), _⟩ : ForallProblem).Valid
  rw [Instance.premises, ← premises_transport inst outer hk]
  exact transported

open RecursiveTyping

def mapBinding (outer : Bindings) : Binding → Binding
  | .mono β => .mono (bounds outer β)
  | .recursive c => .recursive c

def CapturesFixed (outer : Bindings) (env : List Binding) : Prop :=
  ∀ c, .recursive c ∈ env → ∀ i ∈ c.counts.captures, lookup outer i = none

/-- The initial symbolic-RHS transport slice excludes nested recursive groups.
    Such groups may capture the enclosing count telescope and need a separate
    captured-template transport rule. This restriction is explicit in the proof,
    not an unchecked assumption in the executable path. List matches recurse
    through every arm; source terms must have found wrappers stripped. -/
def NoGroups : Expr → Prop
  | .lambda _ body => NoGroups body
  | .app f arg => NoGroups f ∧ NoGroups arg
  | .letIn _ rhs body => NoGroups rhs ∧ NoGroups body
  | .letRec _ _ _ => False
  | .match_ scrut branches => NoGroups scrut ∧ ∀ br ∈ branches, NoGroups br.2
  | .found _ _ => False
  | _ => True
termination_by e => sizeOf e
decreasing_by
  all_goals simp_wf
  all_goals first | omega | (have hsz := List.sizeOf_lt_of_mem ‹_ ∈ _›; cases ‹MatchPattern × Expr›; simp_all; omega)

private theorem captures_cons {outer env β} (h : CapturesFixed outer env) :
    CapturesFixed outer (.mono β :: env) := by
  intro c hc i hi
  rcases List.mem_cons.mp hc with impossible | rest
  · cases impossible
  · exact h c rest i hi

private theorem captures_branch {outer env p lo hi elem} (h : CapturesFixed outer env) :
    CapturesFixed outer (branchEnv p lo hi elem env) := by
  unfold branchEnv
  split
  · exact captures_cons (captures_cons h)
  · exact h

theorem branchRefine_transport (outer : Bindings) (p : MatchPattern) (lo hi : Count) :
    (branchRefine p lo hi).map (constraint outer) =
      branchRefine p (count outer lo) (count outer hi) := by
  simp only [branchRefine]
  split
  · simp [nilRefine, constraint, count]
  · split <;> simp [consRefine, constraint, count]

theorem branchEnv_transport (outer : Bindings) (p : MatchPattern) (lo hi : Count)
    (elem : BoundsTy) (env : List Binding) :
    (branchEnv p lo hi elem env).map (mapBinding outer) =
      branchEnv p (count outer lo) (count outer hi) (bounds outer elem)
        (env.map (mapBinding outer)) := by
  simp only [branchEnv]
  split <;> simp [*, mapBinding, bounds, count]

private theorem param_transport (outer : Bindings) (hf : Finite outer) {ids inner Δ ann β}
    (h : InterpretedAnnotation.ParamOK ids inner Δ ann β) :
    InterpretedAnnotation.ParamOK ids (CountAlgebra.compose outer inner)
      (Δ.map (constraint outer)) ann (bounds outer β) := by
  cases ann with
  | none => trivial
  | some τ => exact InterpretedAnnotation.transport outer hf h

private theorem binding_transport (outer : Bindings) (hf : Finite outer) {ids inner Δ ann β}
    (h : InterpretedAnnotation.BindingOK ids inner Δ ann β) :
    InterpretedAnnotation.BindingOK ids (CountAlgebra.compose outer inner)
      (Δ.map (constraint outer)) ann (bounds outer β) := by
  cases ann with
  | none => trivial
  | some σ => exact ⟨h.1, InterpretedAnnotation.transport outer hf h.2⟩

/-- Checked symbolic RHSs transport without modifying their source annotations,
    recursive templates or HM identities. Recursive call arguments and premises
    transform together. Only monomorphic local bounds are mapped. -/
theorem transport (outer : Bindings) (hf : Finite outer) (target : List Nat)
    (hs : ∀ row ∈ outer, Scope.CountScoped target row.2) {ids inner Δ env e β}
    (h : Derives ids inner Δ env e β) (hk : CapturesFixed outer env) (hn : NoGroups e) :
    Derives ids (CountAlgebra.compose outer inner) (Δ.map (constraint outer))
      (env.map (mapBinding outer)) e (bounds outer β) := by
  cases h with
  | literal => cases ‹PrimLitExpr› <;> exact .literal
  | primBinOp => cases ‹PrimBinOp› <;> exact .primBinOp
  | nil => exact .nil
  | cons hh ht hi =>
      simp only [NoGroups] at hn
      exact .cons (transport outer hf target hs hh hk hn.1.2)
        (transport outer hf target hs ht hk hn.2) (CountSubstitution.subtype outer hf hi)
  | varMono hv => exact .varMono (by simpa [mapBinding] using congrArg (Option.map (mapBinding outer)) hv)
  | varRecursive hv inst hu =>
      have captured := hk _ (List.mem_of_getElem? hv)
      rw [bounds_transport inst outer captured]
      exact .varRecursive (by simpa [mapBinding] using congrArg (Option.map (mapBinding outer)) hv)
        (instanceTransport inst outer hf target hs captured)
        (usable_transport inst hu outer hf target hs captured)
  | app hf' ha hi =>
      simp only [NoGroups] at hn
      exact .app (transport outer hf target hs hf' hk hn.1)
        (transport outer hf target hs ha hk hn.2) (CountSubstitution.subtype outer hf hi)
  | lambda hp hb =>
      simp only [NoGroups] at hn
      exact .lambda (param_transport outer hf hp)
        (transport outer hf target hs hb (captures_cons hk) hn)
  | letMono hp hr hb =>
      simp only [NoGroups] at hn
      exact .letMono (binding_transport outer hf hp) (transport outer hf target hs hr hk hn.1)
        (transport outer hf target hs hb (captures_cons hk) hn.2)
  | matchList hscrut hc hpat hbranches hsub =>
      simp only [NoGroups] at hn
      apply Derives.matchList
        (transport outer hf target hs hscrut hk hn.1) (hc.transport outer hf) hpat
      · intro i br hb
        have ht := transport outer hf target hs (hbranches i br hb)
          (captures_branch hk) (hn.2 br (List.mem_of_getElem? hb))
        simpa only [List.map_append, branchRefine_transport, branchEnv_transport] using ht
      · intro i br hb
        simpa only [List.map_append, branchRefine_transport] using
          CountSubstitution.subtype outer hf (hsub i br hb)
  | letRec => simp only [NoGroups] at hn
termination_by sizeOf e
decreasing_by
  all_goals subst_vars
  all_goals simp_wf
  all_goals first | omega | (have hsz := List.sizeOf_lt_of_mem (List.mem_of_getElem? ‹_ = some _›); cases ‹MatchPattern × Expr›; simp_all; omega)

private theorem env_fixed {s : Scheme} (outer : Bindings) {env : List Binding}
    (hm : ∀ β, .mono β ∈ env → BoundsScoped s.captures β)
    (hk : ∀ i ∈ s.captures, lookup outer i = none) : env.map (mapBinding outer) = env := by
  conv_rhs => rw [← List.map_id env]
  apply List.map_congr_left
  intro b hb
  cases b with
  | recursive c => rfl
  | mono β => exact congrArg Binding.mono (CountTransport.bounds_fixed outer (hm β hb) hk)

/-- A symbolic RHS derivation supplies every finite scoped count instance when
    its outer monomorphic counts are captured and no recursive contract captures
    this member's quantified coordinates. Simultaneous group independence is
    designed to supply precisely that recursive freshness premise. -/
theorem universal_rhs {s : Scheme} {env rhs β}
    (h : Derives (s.quantified ++ s.captures) [] s.premises env rhs β)
    (hn : NoGroups rhs)
    (hm : ∀ γ, .mono γ ∈ env → BoundsScoped s.captures γ)
    (hr : ∀ c, .recursive c ∈ env → ∀ i ∈ c.counts.captures, i ∉ s.quantified) :
    ∀ args caller (inst : Instance s args caller),
      Derives (s.quantified ++ s.captures) (s.quantified.zip args) inst.premises env rhs
        (bounds (s.quantified.zip args) β) := by
  intro args caller inst
  let outer := s.quantified.zip args
  have captured : ∀ i ∈ s.captures, lookup outer i = none := by
    intro i hi
    apply lookup_none
    rw [List.map_fst_zip (Nat.le_of_eq inst.arity)]
    exact inst.wf.2.1 i hi
  have recFixed : CapturesFixed outer env := by
    intro c hc i hi
    apply lookup_none
    rw [List.map_fst_zip (Nat.le_of_eq inst.arity)]
    exact hr c hc i hi
  have argumentScope : ∀ row ∈ outer, Scope.CountScoped caller row.2 :=
    fun row hr => inst.argsScoped row.2 (List.of_mem_zip hr).2
  have typed := transport outer inst.finite caller argumentScope h recFixed hn
  rw [env_fixed outer hm captured] at typed
  simpa only [CountAlgebra.compose, List.map_nil, List.nil_append, Instance.premises] using typed

#print axioms bounds_transport
#print axioms premises_transport
#print axioms instanceTransport
#print axioms usable_transport
#print axioms transport
#print axioms universal_rhs

end FHM.Bounds.RecursiveCountTransport
