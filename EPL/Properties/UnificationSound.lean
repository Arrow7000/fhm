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

/-- The public unifier equates its two input types whenever it succeeds. -/
theorem unify_sound (run : unify left right = some result) :
    result.apply left = result.apply right := by
  exact unifyFuel_sound run (left, right) (by simp)

end EPL
