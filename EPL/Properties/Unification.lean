import EPL.Unification

namespace EPL

private theorem apply_append (first second : MSubst) (ty : Ty) :
    (first ++ second).apply ty = second.apply (first.apply ty) := by
  simp [MSubst.apply, List.foldl_append]

private theorem substMVar_eq_self_of_occurs_false
    (ty replacement : Ty) (target : Nat)
    (occurs : ty.occursMVar target = false) :
    ty.substMVar target replacement = ty := by
  induction ty with
  | prim => rfl
  | arrow domain codomain domainIH codomainIH =>
      simp only [Ty.occursMVar, Bool.or_eq_false_iff] at occurs
      simp [Ty.substMVar, domainIH occurs.1, codomainIH occurs.2]
  | bvar => rfl
  | rigid => rfl
  | mvar id =>
      have unequal : id ≠ target := by
        intro equal
        subst target
        simp [Ty.occursMVar] at occurs
      simp [Ty.substMVar, unequal]

private theorem apply_arrow (subst : MSubst) (domain codomain : Ty) :
    subst.apply (.arrow domain codomain) =
      .arrow (subst.apply domain) (subst.apply codomain) := by
  induction subst generalizing domain codomain with
  | nil => rfl
  | cons binding rest ih =>
      simp only [MSubst.apply, List.foldl_cons, Ty.substMVar]
      change MSubst.apply rest
          (.arrow (domain.substMVar binding.1 binding.2)
            (codomain.substMVar binding.1 binding.2)) = _
      exact ih _ _

private theorem stable_nil : MSubst.Stable [] := by
  intro ty
  rfl

private theorem bind_fixed
    {initial : MSubst} {current replacement : Ty} {id : Nat}
    (currentFixed : initial.apply current = current)
    (replacementFixed : initial.apply replacement = replacement)
    (occurs : replacement.occursMVar id = false) :
    (initial ++ [(id, replacement)]).apply
        (current.substMVar id replacement) =
      current.substMVar id replacement := by
  induction current with
  | prim =>
      rw [Ty.substMVar, apply_append, currentFixed]
      rfl
  | arrow domain codomain domainIH codomainIH =>
      rw [apply_arrow] at currentFixed
      injection currentFixed with domainFixed codomainFixed
      rw [Ty.substMVar, apply_arrow, domainIH domainFixed,
        codomainIH codomainFixed]
  | bvar =>
      rw [Ty.substMVar, apply_append, currentFixed]
      rfl
  | rigid =>
      rw [Ty.substMVar, apply_append, currentFixed]
      rfl
  | mvar currentId =>
      by_cases selected : currentId = id
      · subst currentId
        rw [Ty.substMVar, if_pos rfl, apply_append, replacementFixed]
        exact substMVar_eq_self_of_occurs_false replacement replacement id occurs
      · rw [Ty.substMVar, if_neg selected, apply_append, currentFixed]
        simp [MSubst.apply, Ty.substMVar, selected]

private theorem stable_bind
    {initial : MSubst} {id : Nat} {replacement : Ty}
    (stable : initial.Stable)
    (replacementFixed : initial.apply replacement = replacement)
    (occurs : replacement.occursMVar id = false) :
    (initial ++ [(id, replacement)]).Stable := by
  intro ty
  have normalizedFixed : initial.apply (initial.apply ty) = initial.apply ty :=
    stable ty
  have extensionApply (current : Ty) :
      (initial ++ [(id, replacement)]).apply current =
        (initial.apply current).substMVar id replacement := by
    rw [apply_append]
    rfl
  calc
    (initial ++ [(id, replacement)]).apply
        ((initial ++ [(id, replacement)]).apply ty) =
      (initial ++ [(id, replacement)]).apply
        ((initial.apply ty).substMVar id replacement) := by
          exact congrArg (MSubst.apply (initial ++ [(id, replacement)]))
            (extensionApply ty)
    _ = (initial.apply ty).substMVar id replacement :=
      bind_fixed normalizedFixed replacementFixed occurs
    _ = (initial ++ [(id, replacement)]).apply ty :=
      (extensionApply ty).symm

private theorem normalized_fixed
    {initial : MSubst} {source normalized : Ty}
    (stable : initial.Stable)
    (normalizedEq : initial.apply source = normalized) :
    initial.apply normalized = normalized := by
  simpa [normalizedEq] using stable source

private theorem bool_eq_false_of_not_true {value : Bool}
    (notTrue : ¬ value = true) : value = false := by
  cases value <;> simp_all

private theorem bind_solves
    {initial : MSubst} {left right ty : Ty} {id : Nat}
    (leftEq : initial.apply left = .mvar id)
    (rightEq : initial.apply right = ty)
    (occurs : ty.occursMVar id = false) (suffix : MSubst) :
    ((initial ++ [(id, ty)]) ++ suffix).apply left =
      ((initial ++ [(id, ty)]) ++ suffix).apply right := by
  rw [apply_append, apply_append, apply_append, apply_append, leftEq, rightEq]
  simp only [MSubst.apply, List.foldl, Ty.substMVar, ↓reduceIte]
  rw [substMVar_eq_self_of_occurs_false ty ty id occurs]

private theorem bind_solves_symm
    {initial : MSubst} {left right ty : Ty} {id : Nat}
    (leftEq : initial.apply left = ty)
    (rightEq : initial.apply right = .mvar id)
    (occurs : ty.occursMVar id = false) (suffix : MSubst) :
    ((initial ++ [(id, ty)]) ++ suffix).apply left =
      ((initial ++ [(id, ty)]) ++ suffix).apply right := by
  exact (bind_solves rightEq leftEq occurs suffix).symm

private theorem finish_bind
    {initial result : MSubst} {left right ty : Ty} {id : Nat}
    {rest : List Constraint}
    (leftEq : initial.apply left = .mvar id)
    (rightEq : initial.apply right = ty)
    (occurs : ty.occursMVar id = false)
    (recursive :
      (∃ suffix, result = (initial ++ [(id, ty)]) ++ suffix) ∧
        result.Solves rest) :
    (∃ suffix, result = initial ++ suffix) ∧
      result.Solves ((left, right) :: rest) := by
  rcases recursive with ⟨⟨suffix, resultEq⟩, solvesRest⟩
  refine ⟨⟨[(id, ty)] ++ suffix, by simpa [List.append_assoc] using resultEq⟩, ?_⟩
  intro constraint membership
  rcases List.mem_cons.mp membership with rfl | inRest
  · rw [resultEq]
    exact bind_solves leftEq rightEq occurs suffix
  · exact solvesRest constraint inRest

private theorem finish_bind_symm
    {initial result : MSubst} {left right ty : Ty} {id : Nat}
    {rest : List Constraint}
    (leftEq : initial.apply left = ty)
    (rightEq : initial.apply right = .mvar id)
    (occurs : ty.occursMVar id = false)
    (recursive :
      (∃ suffix, result = (initial ++ [(id, ty)]) ++ suffix) ∧
        result.Solves rest) :
    (∃ suffix, result = initial ++ suffix) ∧
      result.Solves ((left, right) :: rest) := by
  rcases recursive with ⟨⟨suffix, resultEq⟩, solvesRest⟩
  refine ⟨⟨[(id, ty)] ++ suffix, by simpa [List.append_assoc] using resultEq⟩, ?_⟩
  intro constraint membership
  rcases List.mem_cons.mp membership with rfl | inRest
  · rw [resultEq]
    exact bind_solves_symm leftEq rightEq occurs suffix
  · exact solvesRest constraint inRest

private theorem finish_arrows
    {initial result : MSubst} {left right ld lc rd rc : Ty}
    {rest : List Constraint}
    (stable : initial.Stable)
    (leftEq : initial.apply left = .arrow ld lc)
    (rightEq : initial.apply right = .arrow rd rc)
    (recursive :
      (∃ suffix, result = initial ++ suffix) ∧
        result.Solves ((ld, rd) :: (lc, rc) :: rest)) :
    (∃ suffix, result = initial ++ suffix) ∧
      result.Solves ((left, right) :: rest) := by
  rcases recursive with ⟨⟨suffix, resultEq⟩, solves⟩
  refine ⟨⟨suffix, resultEq⟩, ?_⟩
  intro constraint membership
  rcases List.mem_cons.mp membership with rfl | inRest
  · have domains : result.apply ld = result.apply rd :=
      solves (ld, rd) (by simp)
    have codomains : result.apply lc = result.apply rc :=
      solves (lc, rc) (by simp)
    have leftFixed := stable left
    rw [leftEq, apply_arrow] at leftFixed
    injection leftFixed with ldFixed lcFixed
    have rightFixed := stable right
    rw [rightEq, apply_arrow] at rightFixed
    injection rightFixed with rdFixed rcFixed
    rw [resultEq, apply_append, apply_append, ldFixed, rdFixed] at domains
    rw [resultEq, apply_append, apply_append, lcFixed, rcFixed] at codomains
    rw [resultEq, apply_append, apply_append, leftEq, rightEq,
      apply_arrow, apply_arrow, domains, codomains]
  · exact solves constraint (by simp [inRest])

private theorem unifyFuel_sound_stable
    (stable : initial.Stable)
    (run : unifyFuel fuel constraints initial = some result) :
    result.Stable ∧ (∃ suffix, result = initial ++ suffix) ∧
      result.Solves constraints := by
  induction fuel generalizing constraints initial result with
  | zero =>
      cases constraints with
      | nil =>
          simp [unifyFuel] at run
          subst result
          exact ⟨stable, ⟨[], by simp⟩, by simp [MSubst.Solves]⟩
      | cons constraint rest => simp [unifyFuel] at run
  | succ fuel ih =>
      cases constraints with
      | nil =>
          simp [unifyFuel] at run
          subst result
          exact ⟨stable, ⟨[], by simp⟩, by simp [MSubst.Solves]⟩
      | cons constraint rest =>
          rcases constraint with ⟨left, right⟩
          simp only [unifyFuel] at run
          by_cases equal : initial.apply left = initial.apply right
          · rw [if_pos equal] at run
            rcases ih stable run with
              ⟨resultStable, ⟨suffix, resultEq⟩, solvesRest⟩
            refine ⟨resultStable, ⟨suffix, resultEq⟩, ?_⟩
            intro current membership
            rcases List.mem_cons.mp membership with rfl | inRest
            · simpa [resultEq, apply_append] using
                congrArg (MSubst.apply suffix) equal
            · exact solvesRest current inRest
          · rw [if_neg equal] at run
            generalize leftEq : initial.apply left = normalizedLeft at run equal
            generalize rightEq : initial.apply right = normalizedRight at run equal
            cases normalizedLeft <;> cases normalizedRight <;>
              simp_all only [Ty.occursMVar, Bool.false_eq_true, reduceCtorEq,
                Bool.or_eq_true, beq_iff_eq]
            case neg.prim.mvar name id =>
              simp only [if_false] at run
              have replacementFixed :
                  initial.apply (.prim name) = .prim name :=
                normalized_fixed stable leftEq
              have extendedStable :
                  (initial ++ [(id, Ty.prim name)]).Stable :=
                stable_bind stable replacementFixed (by rfl)
              rcases ih extendedStable run with
                ⟨resultStable, extension, solvesRest⟩
              exact ⟨resultStable,
                finish_bind_symm leftEq rightEq (by rfl)
                  ⟨extension, solvesRest⟩⟩
            case neg.arrow.arrow ld lc rd rc =>
              rcases ih stable run with
                ⟨resultStable, extension, solvesDecomposed⟩
              exact ⟨resultStable,
                finish_arrows stable leftEq rightEq
                  ⟨extension, solvesDecomposed⟩⟩
            case neg.arrow.mvar domain codomain id =>
              by_cases occursTrue :
                  domain.occursMVar id = true ∨ codomain.occursMVar id = true
              · rw [if_pos occursTrue] at run
                contradiction
              · rw [if_neg occursTrue] at run
                have domainOccurs : domain.occursMVar id = false :=
                  bool_eq_false_of_not_true (fun occurrence =>
                    occursTrue (Or.inl occurrence))
                have codomainOccurs : codomain.occursMVar id = false :=
                  bool_eq_false_of_not_true (fun occurrence =>
                    occursTrue (Or.inr occurrence))
                have occurs :
                    (Ty.arrow domain codomain).occursMVar id = false := by
                  simp [Ty.occursMVar, domainOccurs, codomainOccurs]
                have replacementFixed :
                    initial.apply (.arrow domain codomain) =
                      .arrow domain codomain :=
                  normalized_fixed stable leftEq
                have extendedStable :
                    (initial ++ [(id, Ty.arrow domain codomain)]).Stable :=
                  stable_bind stable replacementFixed occurs
                rcases ih extendedStable run with
                  ⟨resultStable, extension, solvesRest⟩
                exact ⟨resultStable,
                  finish_bind_symm leftEq rightEq occurs
                    ⟨extension, solvesRest⟩⟩
            case neg.bvar.mvar index id =>
              simp only [if_false] at run
              have replacementFixed :
                  initial.apply (.bvar index) = .bvar index :=
                normalized_fixed stable leftEq
              have extendedStable :
                  (initial ++ [(id, Ty.bvar index)]).Stable :=
                stable_bind stable replacementFixed (by rfl)
              rcases ih extendedStable run with
                ⟨resultStable, extension, solvesRest⟩
              exact ⟨resultStable,
                finish_bind_symm leftEq rightEq (by rfl)
                  ⟨extension, solvesRest⟩⟩
            case neg.rigid.mvar level id =>
              simp only [if_false] at run
              have replacementFixed :
                  initial.apply (.rigid level) = .rigid level :=
                normalized_fixed stable leftEq
              have extendedStable :
                  (initial ++ [(id, Ty.rigid level)]).Stable :=
                stable_bind stable replacementFixed (by rfl)
              rcases ih extendedStable run with
                ⟨resultStable, extension, solvesRest⟩
              exact ⟨resultStable,
                finish_bind_symm leftEq rightEq (by rfl)
                  ⟨extension, solvesRest⟩⟩
            case neg.mvar.prim id name =>
              simp only [if_false] at run
              have replacementFixed :
                  initial.apply (.prim name) = .prim name :=
                normalized_fixed stable rightEq
              have extendedStable :
                  (initial ++ [(id, Ty.prim name)]).Stable :=
                stable_bind stable replacementFixed (by rfl)
              rcases ih extendedStable run with
                ⟨resultStable, extension, solvesRest⟩
              exact ⟨resultStable,
                finish_bind leftEq rightEq (by rfl)
                  ⟨extension, solvesRest⟩⟩
            case neg.mvar.arrow id domain codomain =>
              by_cases occursTrue :
                  domain.occursMVar id = true ∨ codomain.occursMVar id = true
              · rw [if_pos occursTrue] at run
                contradiction
              · rw [if_neg occursTrue] at run
                have domainOccurs : domain.occursMVar id = false :=
                  bool_eq_false_of_not_true (fun occurrence =>
                    occursTrue (Or.inl occurrence))
                have codomainOccurs : codomain.occursMVar id = false :=
                  bool_eq_false_of_not_true (fun occurrence =>
                    occursTrue (Or.inr occurrence))
                have occurs :
                    (Ty.arrow domain codomain).occursMVar id = false := by
                  simp [Ty.occursMVar, domainOccurs, codomainOccurs]
                have replacementFixed :
                    initial.apply (.arrow domain codomain) =
                      .arrow domain codomain :=
                  normalized_fixed stable rightEq
                have extendedStable :
                    (initial ++ [(id, Ty.arrow domain codomain)]).Stable :=
                  stable_bind stable replacementFixed occurs
                rcases ih extendedStable run with
                  ⟨resultStable, extension, solvesRest⟩
                exact ⟨resultStable,
                  finish_bind leftEq rightEq occurs
                    ⟨extension, solvesRest⟩⟩
            case neg.mvar.bvar id index =>
              simp only [if_false] at run
              have replacementFixed :
                  initial.apply (.bvar index) = .bvar index :=
                normalized_fixed stable rightEq
              have extendedStable :
                  (initial ++ [(id, Ty.bvar index)]).Stable :=
                stable_bind stable replacementFixed (by rfl)
              rcases ih extendedStable run with
                ⟨resultStable, extension, solvesRest⟩
              exact ⟨resultStable,
                finish_bind leftEq rightEq (by rfl)
                  ⟨extension, solvesRest⟩⟩
            case neg.mvar.rigid id level =>
              simp only [if_false] at run
              have replacementFixed :
                  initial.apply (.rigid level) = .rigid level :=
                normalized_fixed stable rightEq
              have extendedStable :
                  (initial ++ [(id, Ty.rigid level)]).Stable :=
                stable_bind stable replacementFixed (by rfl)
              rcases ih extendedStable run with
                ⟨resultStable, extension, solvesRest⟩
              exact ⟨resultStable,
                finish_bind leftEq rightEq (by rfl)
                  ⟨extension, solvesRest⟩⟩
            case neg.mvar.mvar leftId rightId =>
              have idsNe : rightId ≠ leftId := by
                intro idsEq
                apply equal
                cases idsEq
                rfl
              rw [if_neg idsNe] at run
              have occurs : (Ty.mvar rightId).occursMVar leftId = false := by
                simp [Ty.occursMVar, idsNe]
              have replacementFixed :
                  initial.apply (.mvar rightId) = .mvar rightId :=
                normalized_fixed stable rightEq
              have extendedStable :
                  (initial ++ [(leftId, Ty.mvar rightId)]).Stable :=
                stable_bind stable replacementFixed occurs
              rcases ih extendedStable run with
                ⟨resultStable, extension, solvesRest⟩
              exact ⟨resultStable,
                finish_bind leftEq rightEq occurs
                  ⟨extension, solvesRest⟩⟩

/-- Every successful fuelled run from the public empty-substitution boundary
solves all of its original constraints. Arbitrary preloaded substitutions are
not part of EPL's unifier contract. -/
theorem unifyFuel_sound
    (run : unifyFuel fuel constraints [] = some result) :
    result.Solves constraints := by
  exact (unifyFuel_sound_stable stable_nil run).2.2

/-- Successful public unification produces a substitution stable under
reapplication. -/
theorem unify_stable (run : unify left right = some result) :
    result.Stable := by
  exact (unifyFuel_sound_stable stable_nil run).1

/-- The public unifier equates its two input types whenever it succeeds. -/
theorem unify_sound (run : unify left right = some result) :
    result.apply left = result.apply right := by
  exact unifyFuel_sound run (left, right) (by simp)

end EPL

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
