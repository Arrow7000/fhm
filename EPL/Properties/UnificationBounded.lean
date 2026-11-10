import EPL.Properties.InferenceScope

namespace EPL

/-- Every metavariable in a type was allocated below `frontier`. -/
def Ty.MVarBounded (frontier : Nat) (ty : Ty) : Prop :=
  ∀ id ∈ ty.mvars, id < frontier

/-- Both the targets and images of a substitution stay inside the allocator's
current namespace. -/
def MSubst.Bounded (frontier : Nat) (subst : MSubst) : Prop :=
  ∀ binding ∈ subst,
    binding.1 < frontier ∧ binding.2.MVarBounded frontier

def Constraints.MVarBounded
    (frontier : Nat) (constraints : List Constraint) : Prop :=
  ∀ constraint ∈ constraints,
    constraint.1.MVarBounded frontier ∧
      constraint.2.MVarBounded frontier

theorem Ty.mvarBounded_iff_mvarsBelow
    {ty : Ty} {frontier : Nat} :
    ty.MVarBounded frontier ↔ ty.mvarsBelow frontier = true := by
  exact Ty.mvarsBelow_eq_true_iff.symm

/-- Fuelled unification never invents a metavariable outside the namespace of
its initial substitution and constraints. -/
theorem unifyFuel_bounded
    (initialBounded : initial.Bounded frontier)
    (constraintsBounded : Constraints.MVarBounded frontier constraints)
    (run : unifyFuel fuel constraints initial = some result) :
    result.Bounded frontier := by
  have substMVar_bounded :
      ∀ {ty replacement : Ty} {target : Nat},
        ty.MVarBounded frontier →
        replacement.MVarBounded frontier →
        (ty.substMVar target replacement).MVarBounded frontier := by
    intro ty replacement target typeBounded replacementBounded
    induction ty with
    | prim name => simp [Ty.MVarBounded, Ty.substMVar, Ty.mvars]
    | arrow domain codomain ihDomain ihCodomain =>
        have domainBounded : domain.MVarBounded frontier := by
          intro id member
          exact typeBounded id (by simp [Ty.mvars, member])
        have codomainBounded : codomain.MVarBounded frontier := by
          intro id member
          exact typeBounded id (by simp [Ty.mvars, member])
        intro id member
        simp only [Ty.substMVar, Ty.mvars, List.mem_dedup,
          List.mem_append] at member
        rcases member with member | member
        · exact ihDomain domainBounded id member
        · exact ihCodomain codomainBounded id member
    | bvar index => simp [Ty.MVarBounded, Ty.substMVar, Ty.mvars]
    | rigid level => simp [Ty.MVarBounded, Ty.substMVar, Ty.mvars]
    | mvar id =>
        simp only [Ty.substMVar]
        split
        · exact replacementBounded
        · intro candidate member
          simp only [Ty.mvars, List.mem_singleton] at member
          subst candidate
          exact typeBounded id (by simp [Ty.mvars])
  have apply_bounded :
      ∀ {subst : MSubst} {ty : Ty},
        subst.Bounded frontier →
        ty.MVarBounded frontier →
        (subst.apply ty).MVarBounded frontier := by
    intro subst ty substBounded typeBounded
    induction subst generalizing ty with
    | nil => simpa [MSubst.apply] using typeBounded
    | cons binding rest ih =>
        have bindingBounded := substBounded binding (by simp)
        have restBounded : MSubst.Bounded frontier rest := by
          intro item member
          exact substBounded item (by simp [member])
        simpa [MSubst.apply, List.foldl] using
          ih restBounded (substMVar_bounded typeBounded bindingBounded.2)
  have append_one_bounded :
      ∀ {subst : MSubst} {id : Nat} {ty : Ty},
        subst.Bounded frontier → id < frontier →
        ty.MVarBounded frontier →
        (subst ++ [(id, ty)]).Bounded frontier := by
    intro subst id ty substBounded idBounded typeBounded binding member
    rcases List.mem_append.mp member with old | new
    · exact substBounded binding old
    · simp only [List.mem_singleton] at new
      subst binding
      exact ⟨idBounded, typeBounded⟩
  have arrow_parts :
      ∀ {domain codomain : Ty},
        (Ty.arrow domain codomain).MVarBounded frontier →
        domain.MVarBounded frontier ∧ codomain.MVarBounded frontier := by
    intro domain codomain bounded
    constructor <;> intro id member
    · exact bounded id (by simp [Ty.mvars, member])
    · exact bounded id (by simp [Ty.mvars, member])
  induction fuel generalizing constraints initial result with
  | zero =>
      cases constraints with
      | nil =>
          simp only [unifyFuel, Option.some.injEq] at run
          subst result
          exact initialBounded
      | cons constraint rest => simp [unifyFuel] at run
  | succ fuel ih =>
      cases constraints with
      | nil =>
          simp only [unifyFuel, Option.some.injEq] at run
          subst result
          exact initialBounded
      | cons constraint rest =>
          rcases constraint with ⟨left, right⟩
          have inputBounded := constraintsBounded (left, right) (by simp)
          have restBounded : Constraints.MVarBounded frontier rest := by
            intro item member
            exact constraintsBounded item (List.mem_cons_of_mem _ member)
          have leftBounded := apply_bounded initialBounded inputBounded.1
          have rightBounded := apply_bounded initialBounded inputBounded.2
          simp only [unifyFuel] at run
          by_cases equal : initial.apply left = initial.apply right
          · rw [if_pos equal] at run
            exact ih initialBounded restBounded run
          · rw [if_neg equal] at run
            generalize leftEq : initial.apply left = left' at leftBounded run
            generalize rightEq : initial.apply right = right' at rightBounded run
            have bindCase (id : Nat) (assigned : Ty)
                (idBounded : id < frontier)
                (assignedBounded : assigned.MVarBounded frontier)
                (bindRun :
                  (if assigned.occursMVar id = true then none
                    else unifyFuel fuel rest (initial ++ [(id, assigned)])) =
                      some result) :
                result.Bounded frontier := by
              by_cases occurs : assigned.occursMVar id = true
              · simp [occurs] at bindRun
              · apply ih
                  (append_one_bounded initialBounded idBounded assignedBounded)
                  restBounded
                simpa [occurs] using bindRun
            cases left' with
            | prim leftPrim =>
                cases right' with
                | prim rightPrim => simp at run
                | arrow _ _ => simp at run
                | bvar _ => simp at run
                | rigid _ => simp at run
                | mvar id =>
                    exact bindCase id (.prim leftPrim)
                      (rightBounded id (by simp [Ty.mvars])) leftBounded run
            | arrow leftDomain leftCodomain =>
                cases right' with
                | prim _ => simp at run
                | arrow rightDomain rightCodomain =>
                    have leftParts := arrow_parts leftBounded
                    have rightParts := arrow_parts rightBounded
                    change unifyFuel fuel
                      ((leftDomain, rightDomain) ::
                        (leftCodomain, rightCodomain) :: rest) initial =
                          some result at run
                    apply ih (constraints :=
                      (leftDomain, rightDomain) ::
                        (leftCodomain, rightCodomain) :: rest) initialBounded
                    · intro item member
                      rcases List.mem_cons.mp member with first | member
                      · simpa [first] using
                          (And.intro leftParts.1 rightParts.1)
                      · rcases List.mem_cons.mp member with second | member
                        · simpa [second] using
                            (And.intro leftParts.2 rightParts.2)
                        · exact restBounded item member
                    · exact run
                | bvar _ => simp at run
                | rigid _ => simp at run
                | mvar id =>
                    exact bindCase id (.arrow leftDomain leftCodomain)
                      (rightBounded id (by simp [Ty.mvars])) leftBounded run
            | bvar leftIndex =>
                cases right' with
                | prim _ => simp at run
                | arrow _ _ => simp at run
                | bvar _ => simp at run
                | rigid _ => simp at run
                | mvar id =>
                    exact bindCase id (.bvar leftIndex)
                      (rightBounded id (by simp [Ty.mvars])) leftBounded run
            | rigid leftLevel =>
                cases right' with
                | prim _ => simp at run
                | arrow _ _ => simp at run
                | bvar _ => simp at run
                | rigid _ => simp at run
                | mvar id =>
                    exact bindCase id (.rigid leftLevel)
                      (rightBounded id (by simp [Ty.mvars])) leftBounded run
            | mvar id =>
                have idBounded : id < frontier :=
                  leftBounded id (by simp [Ty.mvars])
                cases right' with
                | prim rightPrim =>
                    exact bindCase id (.prim rightPrim) idBounded rightBounded run
                | arrow rightDomain rightCodomain =>
                    exact bindCase id (.arrow rightDomain rightCodomain)
                      idBounded rightBounded run
                | bvar rightIndex =>
                    exact bindCase id (.bvar rightIndex) idBounded rightBounded run
                | rigid rightLevel =>
                    exact bindCase id (.rigid rightLevel) idBounded rightBounded run
                | mvar rightId =>
                    exact bindCase id (.mvar rightId) idBounded rightBounded run

/-- Public unification preserves a common metavariable frontier. -/
theorem unify_bounded
    (leftBounded : left.MVarBounded frontier)
    (rightBounded : right.MVarBounded frontier)
    (run : unify left right = some result) :
    result.Bounded frontier := by
  apply unifyFuel_bounded (initial := [])
      (constraints := [(left, right)])
  · simp [MSubst.Bounded]
  · intro constraint member
    simp only [List.mem_singleton] at member
    subst constraint
    exact ⟨leftBounded, rightBounded⟩
  · exact run

end EPL
