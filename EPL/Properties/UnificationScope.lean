import EPL.Unification

namespace EPL

private theorem scoped_substMVar
    {ty replacement : Ty} {rigidCount target : Nat}
    (typeScoped : Ty.Scoped rigidCount 0 ty)
    (replacementScoped : Ty.Scoped rigidCount 0 replacement) :
    (ty.substMVar target replacement).Scoped rigidCount 0 := by
  induction typeScoped with
  | prim => exact .prim
  | arrow _ _ domainIH codomainIH => exact .arrow domainIH codomainIH
  | bvar h => omega
  | rigid h => exact .rigid h
  | mvar id =>
      simp only [Ty.substMVar]
      split
      · exact replacementScoped
      · exact .mvar id

private theorem apply_scoped
    {subst : MSubst} {ty : Ty} {rigidCount : Nat}
    (substScoped : MSubst.Scoped rigidCount subst)
    (typeScoped : Ty.Scoped rigidCount 0 ty) :
    (subst.apply ty).Scoped rigidCount 0 := by
  induction subst generalizing ty with
  | nil => simpa [MSubst.apply] using typeScoped
  | cons binding rest ih =>
      have bindingScoped : binding.2.Scoped rigidCount 0 :=
        substScoped binding (by simp)
      have restScoped : MSubst.Scoped rigidCount rest := by
        intro item member
        exact substScoped item (by simp [member])
      simpa [MSubst.apply, List.foldl] using
        ih restScoped (scoped_substMVar typeScoped bindingScoped)

private theorem scoped_append_one
    {subst : MSubst} {ty : Ty} {rigidCount id : Nat}
    (substScoped : MSubst.Scoped rigidCount subst)
    (typeScoped : Ty.Scoped rigidCount 0 ty) :
    (subst ++ [(id, ty)]).Scoped rigidCount := by
  intro binding member
  rcases List.mem_append.mp member with old | new
  · exact substScoped binding old
  · simp only [List.mem_singleton] at new
    subst binding
    exact typeScoped

private theorem constraints_tail
    {constraint : Constraint} {rest : List Constraint} {rigidCount : Nat}
    (hscoped : Constraints.Scoped rigidCount (constraint :: rest)) :
    Constraints.Scoped rigidCount rest := by
  intro item member
  exact hscoped item (List.mem_cons_of_mem constraint member)

private theorem constraints_head
    {constraint : Constraint} {rest : List Constraint} {rigidCount : Nat}
    (hscoped : Constraints.Scoped rigidCount (constraint :: rest)) :
    constraint.1.Scoped rigidCount 0 ∧ constraint.2.Scoped rigidCount 0 :=
  hscoped constraint (by simp)

/-- Unification cannot invent an out-of-scope bound or rigid variable. -/
theorem unifyFuel_scoped
    (initialScoped : initial.Scoped rigidCount)
    (constraintsScoped : Constraints.Scoped rigidCount constraints)
    (run : unifyFuel fuel constraints initial = some result) :
    result.Scoped rigidCount := by
  induction fuel generalizing constraints initial result with
  | zero =>
      cases constraints with
      | nil =>
          simp only [unifyFuel, Option.some.injEq] at run
          subst result
          exact initialScoped
      | cons constraint rest => simp [unifyFuel] at run
  | succ fuel ih =>
      cases constraints with
      | nil =>
          simp only [unifyFuel, Option.some.injEq] at run
          subst result
          exact initialScoped
      | cons constraint rest =>
          rcases constraint with ⟨left, right⟩
          have inputScoped := constraints_head constraintsScoped
          have restScoped := constraints_tail constraintsScoped
          have leftScoped := apply_scoped initialScoped inputScoped.1
          have rightScoped := apply_scoped initialScoped inputScoped.2
          simp only [unifyFuel] at run
          by_cases equal : initial.apply left = initial.apply right
          · rw [if_pos equal] at run
            exact ih initialScoped restScoped run
          · rw [if_neg equal] at run
            generalize leftEq : initial.apply left = left' at leftScoped run
            generalize rightEq : initial.apply right = right' at rightScoped run
            have bindCase (id : Nat) (assigned : Ty)
                (assignedScoped : assigned.Scoped rigidCount 0)
                (bindRun :
                  (if assigned.occursMVar id = true then none
                    else unifyFuel fuel rest (initial ++ [(id, assigned)])) =
                      some result) :
                result.Scoped rigidCount := by
              by_cases occurs : assigned.occursMVar id = true
              · simp [occurs] at bindRun
              · apply ih (scoped_append_one initialScoped assignedScoped) restScoped
                simpa [occurs] using bindRun
            have impossible (h : (none : Option MSubst) = some result) :
                result.Scoped rigidCount := by
              cases h
            cases left' with
            | prim leftPrim =>
                cases right' with
                | prim rightPrim => simp at run
                | arrow _ _ => simp at run
                | bvar _ => simp at run
                | rigid _ => simp at run
                | mvar id => exact bindCase id (.prim leftPrim) leftScoped run
            | arrow leftDomain leftCodomain =>
                cases right' with
                | prim _ => simp at run
                | arrow rightDomain rightCodomain =>
                    cases leftScoped with
                    | arrow leftDomainScoped leftCodomainScoped =>
                      cases rightScoped with
                      | arrow rightDomainScoped rightCodomainScoped =>
                        change unifyFuel fuel
                          ((leftDomain, rightDomain) ::
                            (leftCodomain, rightCodomain) :: rest) initial =
                              some result at run
                        apply ih (constraints :=
                          (leftDomain, rightDomain) ::
                            (leftCodomain, rightCodomain) :: rest) initialScoped
                        · intro item member
                          by_cases first : item = (leftDomain, rightDomain)
                          · subst item
                            exact ⟨leftDomainScoped, rightDomainScoped⟩
                          · by_cases second : item = (leftCodomain, rightCodomain)
                            · subst item
                              exact ⟨leftCodomainScoped, rightCodomainScoped⟩
                            · apply restScoped item
                              simpa [first, second] using member
                        · exact run
                | bvar _ => simp at run
                | rigid _ => simp at run
                | mvar id =>
                    exact bindCase id (.arrow leftDomain leftCodomain) leftScoped run
            | bvar _ =>
                cases leftScoped with
                | bvar h => omega
            | rigid leftLevel =>
                cases right' with
                | prim _ => simp at run
                | arrow _ _ => simp at run
                | bvar _ => simp at run
                | rigid _ =>
                    apply impossible
                    change none = some result at run
                    exact run
                | mvar id => exact bindCase id (.rigid leftLevel) leftScoped run
            | mvar id =>
                cases right' with
                | prim rightPrim => exact bindCase id (.prim rightPrim) rightScoped run
                | arrow rightDomain rightCodomain =>
                    exact bindCase id (.arrow rightDomain rightCodomain) rightScoped run
                | bvar _ =>
                    cases rightScoped with
                    | bvar h => omega
                | rigid rightLevel => exact bindCase id (.rigid rightLevel) rightScoped run
                | mvar rightId => exact bindCase id (.mvar rightId) rightScoped run

theorem unify_scoped
    (leftScoped : left.Scoped rigidCount 0)
    (rightScoped : right.Scoped rigidCount 0)
    (run : unify left right = some result) :
    result.Scoped rigidCount := by
  apply unifyFuel_scoped (initial := []) (constraints := [(left, right)])
  · simp [MSubst.Scoped]
  · intro constraint member
    simp only [List.mem_singleton] at member
    subst constraint
    exact ⟨leftScoped, rightScoped⟩
  · exact run

end EPL
