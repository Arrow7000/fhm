import FHM.Bounds.CountSubstitution
import FHM.Bounds.Scope

/-! # Count schemes with explicit captures

A scheme quantifies selected stable rigid identities, not every count occurring
in its body. Captures are a separate lexical interface. Instantiation is
simultaneous and transports the scheme's premises as well as its bounds.

This module certifies scope and substitution; it does not certify an RHS against
a declared scheme, discharge instantiated premises at a call, generalize machine
unknowns, or permit polymorphic recursion in HM.
-/

namespace FHM.Bounds.ScopedScheme

open Scope CountSubstitution

def countScopedBool (ids : List Nat) : Count → Bool
  | .lit _ | .inf => true
  | .var ⟨.rigid, i⟩ => ids.contains i
  | .var ⟨.inferable, _⟩ => false
  | .add a b | .mul a b | .min a b | .max a b =>
      countScopedBool ids a && countScopedBool ids b
  | .pred a => countScopedBool ids a

theorem countScopedBool_sound {ids : List Nat} {c : Count}
    (h : countScopedBool ids c = true) : CountScoped ids c := by
  induction c with
  | lit | inf => trivial
  | var v =>
      cases v with | mk kind i =>
        cases kind with
        | rigid => simpa [countScopedBool, List.contains_iff_mem] using h
        | inferable => cases h
  | add a b ha hb | mul a b ha hb | min a b ha hb | max a b ha hb =>
      simp only [countScopedBool, Bool.and_eq_true] at h
      exact ⟨ha h.1, hb h.2⟩
  | pred a ha => exact ha h

mutual
def BoundsScoped (ids : List Nat) : BoundsTy → Prop
  | .prim _ | .fvar _ | .bvar _ => True
  | .arrow a b => BoundsScoped ids a ∧ BoundsScoped ids b
  | .list lo hi elem => CountScoped ids lo ∧ CountScoped ids hi ∧ BoundsScoped ids elem
  | .custom _ args => BoundsListScoped ids args

def BoundsListScoped (ids : List Nat) : List BoundsTy → Prop
  | [] => True
  | a :: as => BoundsScoped ids a ∧ BoundsListScoped ids as
end

mutual
def boundsScopedBool (ids : List Nat) : BoundsTy → Bool
  | .prim _ | .fvar _ | .bvar _ => true
  | .arrow a b => boundsScopedBool ids a && boundsScopedBool ids b
  | .list lo hi elem =>
      countScopedBool ids lo && countScopedBool ids hi && boundsScopedBool ids elem
  | .custom _ args => boundsListScopedBool ids args

def boundsListScopedBool (ids : List Nat) : List BoundsTy → Bool
  | [] => true
  | a :: as => boundsScopedBool ids a && boundsListScopedBool ids as
end

mutual
theorem boundsScopedBool_sound {ids : List Nat} {β : BoundsTy}
    (h : boundsScopedBool ids β = true) : BoundsScoped ids β := by
  cases β with
  | prim | fvar | bvar => trivial
  | arrow a b =>
      simp only [boundsScopedBool, Bool.and_eq_true] at h
      exact ⟨boundsScopedBool_sound h.1, boundsScopedBool_sound h.2⟩
  | list lo hi elem =>
      simp only [boundsScopedBool, Bool.and_eq_true] at h
      exact ⟨countScopedBool_sound h.1.1, countScopedBool_sound h.1.2,
        boundsScopedBool_sound h.2⟩
  | custom name args => exact boundsListScopedBool_sound h
termination_by sizeOf β

private theorem boundsListScopedBool_sound {ids : List Nat} {as : List BoundsTy}
    (h : boundsListScopedBool ids as = true) : BoundsListScoped ids as := by
  cases as with
  | nil => trivial
  | cons a as =>
      simp only [boundsListScopedBool, Bool.and_eq_true] at h
      exact ⟨boundsScopedBool_sound h.1, boundsListScopedBool_sound h.2⟩
termination_by sizeOf as
end

def ConstraintScoped (ids : List Nat) (c : Constraint) : Prop :=
  CountScoped ids c.lhs ∧ CountScoped ids c.rhs

def constraintScopedBool (ids : List Nat) (c : Constraint) : Bool :=
  countScopedBool ids c.lhs && countScopedBool ids c.rhs

theorem constraintScopedBool_sound {ids : List Nat} {c : Constraint}
    (h : constraintScopedBool ids c = true) : ConstraintScoped ids c := by
  simp only [constraintScopedBool, Bool.and_eq_true] at h
  exact ⟨countScopedBool_sound h.1, countScopedBool_sound h.2⟩

structure Scheme where
  quantified : List Nat
  captures : List Nat
  premises : List Constraint := []
  body : BoundsTy
  deriving Repr

def Scheme.WF (s : Scheme) : Prop :=
  s.quantified.Nodup ∧ (∀ i ∈ s.captures, i ∉ s.quantified) ∧
  BoundsScoped (s.quantified ++ s.captures) s.body ∧
  ∀ c ∈ s.premises, ConstraintScoped (s.quantified ++ s.captures) c

def Scheme.wfBool (s : Scheme) : Bool :=
  decide s.quantified.Nodup &&
  s.captures.all (fun i => !s.quantified.contains i) &&
  boundsScopedBool (s.quantified ++ s.captures) s.body &&
  s.premises.all (constraintScopedBool (s.quantified ++ s.captures))

theorem Scheme.wfBool_sound {s : Scheme} (h : s.wfBool = true) : s.WF := by
  simp only [wfBool, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  refine ⟨h.1.1.1, ?_, boundsScopedBool_sound h.1.2, ?_⟩
  · intro i hi
    simpa [List.contains_iff_mem] using h.1.1.2 i hi
  · intro c hc
    exact constraintScopedBool_sound (h.2 c hc)

/-- Key membership and value membership for the selected-identity lookup. -/
theorem lookup_row {rows : Bindings} {i : Nat} {c : Count}
    (h : lookup rows i = some c) : (i, c) ∈ rows := by
  induction rows with
  | nil => cases h
  | cons row rest ih =>
      rcases row with ⟨key, value⟩
      simp only [lookup] at h
      split at h
      · rename_i he
        subst key
        cases h
        exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (ih h)

theorem lookup_none {rows : Bindings} {i : Nat}
    (h : i ∉ rows.map Prod.fst) : lookup rows i = none := by
  cases he : lookup rows i with
  | none => rfl
  | some c =>
      exact False.elim (h (List.mem_map.mpr ⟨(i, c), lookup_row he, rfl⟩))

theorem lookup_none_iff {rows : Bindings} {i : Nat} :
    lookup rows i = none ↔ i ∉ rows.map Prod.fst := by
  induction rows with
  | nil => simp [lookup]
  | cons row rest ih =>
      rcases row with ⟨key, value⟩
      simp only [lookup, List.map_cons, List.mem_cons]
      split <;> simp_all [eq_comm]

/-- Scope transport is independent of finiteness. Replacement expressions are
    checked in the caller's scope; unselected identities must already be there. -/
theorem count_scoped {rows : Bindings} {ids caller : List Nat} {c : Count}
    (h : CountScoped ids c)
    (hrows : ∀ row ∈ rows, CountScoped caller row.2)
    (hkeep : ∀ i ∈ ids, lookup rows i = none → i ∈ caller) :
    CountScoped caller (count rows c) := by
  induction c with
  | lit | inf => trivial
  | var v =>
      cases v with | mk kind i =>
        cases kind with
        | inferable => cases h
        | rigid =>
            cases he : lookup rows i with
            | none => simpa only [count, he, Option.getD_none] using hkeep i h he
            | some arg =>
                simpa only [count, he, Option.getD_some] using hrows (i, arg) (lookup_row he)
  | add a b ha hb | mul a b ha hb | min a b ha hb | max a b ha hb =>
      exact ⟨ha h.1, hb h.2⟩
  | pred a ha => exact ha h

mutual
theorem bounds_scoped {rows : Bindings} {ids caller : List Nat} {β : BoundsTy}
    (h : BoundsScoped ids β)
    (hrows : ∀ row ∈ rows, CountScoped caller row.2)
    (hkeep : ∀ i ∈ ids, lookup rows i = none → i ∈ caller) :
    BoundsScoped caller (bounds rows β) := by
  cases β with
  | prim | fvar | bvar => trivial
  | arrow a b =>
      exact ⟨bounds_scoped h.1 hrows hkeep, bounds_scoped h.2 hrows hkeep⟩
  | list lo hi elem =>
      exact ⟨count_scoped h.1 hrows hkeep, count_scoped h.2.1 hrows hkeep,
        bounds_scoped h.2.2 hrows hkeep⟩
  | custom name args => exact boundsList_scoped h hrows hkeep
termination_by sizeOf β

private theorem boundsList_scoped {rows : Bindings} {ids caller : List Nat}
    {as : List BoundsTy} (h : BoundsListScoped ids as)
    (hrows : ∀ row ∈ rows, CountScoped caller row.2)
    (hkeep : ∀ i ∈ ids, lookup rows i = none → i ∈ caller) :
    BoundsListScoped caller (boundsList rows as) := by
  cases as with
  | nil => trivial
  | cons a as =>
      exact ⟨bounds_scoped h.1 hrows hkeep, boundsList_scoped h.2 hrows hkeep⟩
termination_by sizeOf as
end

private theorem instantiate_keep {s : Scheme} {args : List Count} {caller : List Nat}
    (ha : s.quantified.length = args.length)
    (hc : ∀ i ∈ s.captures, i ∈ caller) :
    ∀ i ∈ s.quantified ++ s.captures,
      lookup (s.quantified.zip args) i = none → i ∈ caller := by
  intro i hi hn
  have hnot := lookup_none_iff.mp hn
  rw [List.map_fst_zip (Nat.le_of_eq ha)] at hnot
  rcases List.mem_append.mp hi with hq | hcap
  · exact False.elim (hnot hq)
  · exact hc i hcap

/-- Successful instantiation is scoped and finite. It retains obligations:
    `premises` are requirements on a use, not facts established by this API. -/
structure Instance (s : Scheme) (args : List Count) (caller : List Nat) : Type where
  wf : s.WF
  arity : s.quantified.length = args.length
  finiteArgs : ∀ a ∈ args, a.NoInf
  argsScoped : ∀ a ∈ args, CountScoped caller a
  capturesScoped : ∀ i ∈ s.captures, i ∈ caller
  bodyScoped : BoundsScoped caller (bounds (s.quantified.zip args) s.body)
  premisesScoped : ∀ c ∈ s.premises.map (constraint (s.quantified.zip args)),
    ConstraintScoped caller c

def Instance.bounds {s args caller} (_ : Instance s args caller) : BoundsTy :=
  CountSubstitution.bounds (s.quantified.zip args) s.body

def Instance.premises {s args caller} (_ : Instance s args caller) : List Constraint :=
  s.premises.map (constraint (s.quantified.zip args))

theorem Instance.finite {s args caller} (inst : Instance s args caller) :
    Finite (s.quantified.zip args) := by
  intro row hr
  exact inst.finiteArgs row.2 (List.of_mem_zip hr).2

/-- Changing quantified coordinates never changes a captured coordinate. -/
theorem Instance.capture_assignment {s args caller} (inst : Instance s args caller)
    (σ : Assign) {i : Nat} (hi : i ∈ s.captures) :
    assignment (s.quantified.zip args) σ ⟨.rigid, i⟩ = σ ⟨.rigid, i⟩ := by
  apply captured_assignment
  apply lookup_none
  rw [List.map_fst_zip (Nat.le_of_eq inst.arity)]
  exact inst.wf.2.1 i hi

theorem Instance.shape {s args caller} (inst : Instance s args caller) :
    Synth.BoundsTy.toTy inst.bounds = Synth.BoundsTy.toTy s.body :=
  bounds_shape _ _

/-- Sound transport, not a proof that a declaration's implementation meets it. -/
theorem Instance.subtype {s args caller} (inst : Instance s args caller) {a b}
    (h : SemanticSub s.premises a b) :
    SemanticSub inst.premises (CountSubstitution.bounds (s.quantified.zip args) a)
      (CountSubstitution.bounds (s.quantified.zip args) b) :=
  CountSubstitution.subtype _ inst.finite h

/-- Separate call-site obligations. These may not simply be appended to the
    caller's assumptions on the strength of successful instantiation. -/
def Instance.Usable {s args caller} (inst : Instance s args caller)
    (Δ : List Constraint) : Prop :=
  (⟨Δ, inst.premises⟩ : ForallProblem).Valid

theorem Instance.useSubtype {s args caller Δ} (inst : Instance s args caller)
    (hu : inst.Usable Δ) {a b} (h : SemanticSub s.premises a b) :
    SemanticSub Δ (CountSubstitution.bounds (s.quantified.zip args) a)
      (CountSubstitution.bounds (s.quantified.zip args) b) :=
  (inst.subtype h).assuming hu

/-- Conservative oracle use: only a positive validity verdict discharges the
    call-site premises; `invalid` and `unknown` both reject. -/
def Instance.checkPremises {s args caller} (inst : Instance s args caller)
    (Δ : List Constraint) : Except String (PLift (inst.Usable Δ)) := do
  let query : ForallProblem := ⟨Δ, inst.premises⟩
  if h : checkValid query = .valid then
    pure ⟨checkValid_sound query h⟩
  else throw "bounds: instantiated count premises not established (invalid or unknown)"

def Scheme.instantiate (s : Scheme) (args : List Count) (caller : List Nat) :
    Except String (Instance s args caller) := do
  if hw : s.wfBool = true then
    if ha : s.quantified.length = args.length then
      if hf : args.all Count.noInf = true then
        if hs : args.all (countScopedBool caller) = true then
          if hc : s.captures.all (fun i => caller.contains i) = true then
            let wf := Scheme.wfBool_sound hw
            have argsScoped : ∀ a ∈ args, CountScoped caller a :=
              fun a h => countScopedBool_sound (List.all_eq_true.mp hs a h)
            have capturesScoped : ∀ i ∈ s.captures, i ∈ caller := by
              intro i hi
              simpa [List.contains_iff_mem] using List.all_eq_true.mp hc i hi
            have rowsScoped : ∀ row ∈ s.quantified.zip args, CountScoped caller row.2 :=
              fun row hr => argsScoped row.2 (List.of_mem_zip hr).2
            have keep := instantiate_keep ha capturesScoped
            pure ⟨wf, ha,
              fun a h => Count.noInf_of_isNoInf (List.all_eq_true.mp hf a h),
              argsScoped, capturesScoped, bounds_scoped wf.2.2.1 rowsScoped keep, by
                intro c hc
                obtain ⟨original, hmem, rfl⟩ := List.mem_map.mp hc
                have h := wf.2.2.2 original hmem
                exact ⟨count_scoped h.1 rowsScoped keep, count_scoped h.2 rowsScoped keep⟩⟩
          else throw "bounds: count scheme capture is outside caller scope"
        else throw "bounds: count argument is outside caller scope"
      else throw "bounds: Nat count argument must be finite"
    else throw "bounds: count scheme has wrong arity"
  else throw "bounds: count scheme has invalid scope or repeated quantifiers"

#print axioms Scheme.instantiate
#print axioms Instance.capture_assignment
#print axioms Instance.subtype
#print axioms Instance.shape
#print axioms Instance.useSubtype
#print axioms Instance.checkPremises

end FHM.Bounds.ScopedScheme
