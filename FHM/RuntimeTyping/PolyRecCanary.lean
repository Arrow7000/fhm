import FHM.Compatibility.Erasure

namespace RuntimeTyping

/-! ## A real-Core erased polymorphic-recursion witness -/

def polyId : PolyTy := ⟨1, .arrow (.bvar 0) (.bvar 0)⟩

/-- `fun x => (fun _ => x) (self 0)`: the current call is at a rigid `a`,
while the recursive occurrence is independently instantiated at `Int`. -/
def polySelfRhs : Expr :=
  .lambda none
    (.app (.lambda none (.var 1)) (.app (.var 1) (.primLit (.int 0))))

def polySelfBindings : List CoreRecBinding :=
  [{ ann := some polyId, rhs := polySelfRhs }]

def erasedPolySelfBindings : List CoreRecBinding :=
  polySelfBindings.map fun binding => { ann := none, rhs := binding.rhs.erase }

theorem polyId_wf : polyId.WF := by
  show ContainsBvarsUpTo 1 (.arrow (.bvar 0) (.bvar 0))
  exact .arrow (.bvar (by omega)) (.bvar (by omega))

theorem polySelf_specs_wf :
    RecSpecsWF erasedPolySelfBindings [.poly polyId] [] := by
  refine ⟨by simp [erasedPolySelfBindings, polySelfBindings], by simp, ?_, ?_⟩
  · intro ty hty
    simp at hty
  · intro scheme hscheme
    simp only [List.mem_singleton, RecSpec.poly.injEq] at hscheme
    subst scheme
    exact polyId_wf

theorem polySelf_mono :
    MonoTyped RunWT ⟨[], []⟩ erasedPolySelfBindings [.poly polyId] [] [] := by
  intro Xs hXs pair hpair ty hmono
  have hXsNil : Xs = [] := List.length_eq_zero_iff.mp hXs.length
  subst Xs
  simp [erasedPolySelfBindings, polySelfBindings] at hpair
  subst pair
  simp at hmono

private theorem singleton_of_fresh_one {avoid names : List Nat}
    (h : FreshNames avoid 1 names) : ∃ name, names = [name] := by
  exact List.length_eq_one_iff.mp h.length

theorem polySelf_poly :
    PolyTyped RunWT ⟨[], []⟩ erasedPolySelfBindings [.poly polyId] [] [] := by
  intro pair hpair scheme hscheme Ys hYs
  simp [erasedPolySelfBindings, polySelfBindings] at hpair
  subst pair
  simp only [RecSpec.poly.injEq] at hscheme
  subst scheme
  obtain ⟨Y, rfl⟩ := singleton_of_fresh_one hYs
  change RunWT ⟨[polyId], []⟩ polySelfRhs.erase
    (.arrow (.fvar Y) (.fvar Y))
  simp only [polySelfRhs, Expr.erase]
  apply RunWT.lambda .fvar
  apply RunWT.app (argTy := .prim .int)
  · apply RunWT.lambda .prim
    exact RunWT.var (index := 1) (scheme := PolyTy.mkTrivial (.fvar Y))
      (args := []) rfl (by simp) .fvar
  · apply RunWT.app (argTy := .prim .int)
    · exact RunWT.var (index := 1) (scheme := polyId)
        (args := [.prim .int]) rfl (by simp; exact .prim)
        (.arrow (.bvar rfl) (.bvar rfl))
    · exact .primLitInt

theorem polySelf_body :
    RunWT (RecSpecs.bodyCtx ⟨[], []⟩ [.poly polyId] [])
      (.var 0) (.arrow (.prim .unit) (.prim .unit)) := by
  exact RunWT.var (index := 0) (scheme := polyId)
    (args := [.prim .unit]) rfl (by simp; exact .prim)
    (.arrow (.bvar rfl) (.bvar rfl))

/-- The annotated source accepts the same independently instantiated recursive
call. Its complete annotation is checked before the machine sees the term. -/
theorem annotated_polySelf_typed :
    TypeOfHM ⟨[], []⟩ (.letRec polySelfBindings (.var 0))
      (.arrow (.prim .unit) (.prim .unit)) := by
  refine TypeOfHM.letRec (specs := [.poly polyId]) (groups := [])
    (G := []) (L := []) ?_ ⟨rfl, by simp, ?_, ?_⟩ ?_ ?_ rfl ?_
  · refine ⟨?_, by simp, ?_, ?_, ?_⟩
    · intro component hcomponent
      simp at hcomponent
    · simp
    · intro member hbound
      have hzero : member = 0 := by
        simp [polySelfBindings] at hbound
        omega
      subst member
      simp [RecGroups.UnsignedAt, polySelfBindings]
    · intro stage dependencyStage component dependencyComponent source target rhs
        hstage _ _ _ _ _
      simp at hstage
  · intro ty hty
    simp at hty
  · intro scheme hscheme
    simp only [List.mem_singleton, RecSpec.poly.injEq] at hscheme
    subst scheme
    exact polyId_wf
  · intro stage component hstage
    simp at hstage
  · intro pair hpair scheme hscheme Ys hYs
    simp [polySelfBindings] at hpair
    subst pair
    simp only [RecSpec.poly.injEq] at hscheme
    subst scheme
    obtain ⟨Y, rfl⟩ := singleton_of_fresh_one hYs
    change TypeOfHM ⟨[polyId], []⟩ polySelfRhs
      (.arrow (.fvar Y) (.fvar Y))
    apply TypeOfHM.lambda .fvar (by simp [Option.Pins]) rfl
    apply TypeOfHM.app (argTy := .prim .int)
    · apply TypeOfHM.lambda .prim (by simp [Option.Pins]) rfl
      exact TypeOfHM.var (dbl := 1) (polyTy := PolyTy.mkTrivial (.fvar Y))
        (instArgs := []) rfl (by simp) .fvar
    · apply TypeOfHM.app (argTy := .prim .int)
      · exact TypeOfHM.var (dbl := 1) (polyTy := polyId)
          (instArgs := [.prim .int]) rfl (by simp; exact .prim)
          (.arrow (.bvar rfl) (.bvar rfl))
      · exact .primLitInt
  · exact TypeOfHM.var (dbl := 0) (polyTy := polyId)
      (instArgs := [.prim .unit]) rfl (by simp; exact .prim)
      (.arrow (.bvar rfl) (.bvar rfl))

/-- No scheme or type application occurs anywhere in this runtime expression. -/
theorem erased_polySelf_typed :
    RunWT ⟨[], []⟩
      (.letRec erasedPolySelfBindings (.var 0))
      (.arrow (.prim .unit) (.prim .unit)) := by
  simpa [Expr.erase, erasedPolySelfBindings, polySelfBindings, polySelfRhs] using
    TypeOfHM.erase_preserves_typing annotated_polySelf_typed

theorem erased_polySelf_steps :
    SmallStep.Step
      (.letRec erasedPolySelfBindings (.var 0))
      ((Expr.var 0).substN 0
        (erasedPolySelfBindings.map (fun binding =>
          .letRec erasedPolySelfBindings binding.rhs))) := by
  exact .letRecUnfold

theorem erased_polySelf_unfolded_typed :
    RunWT ⟨[], []⟩
      ((Expr.var 0).substN 0
        (erasedPolySelfBindings.map (fun binding =>
          .letRec erasedPolySelfBindings binding.rhs)))
      (.arrow (.prim .unit) (.prim .unit)) := by
  exact RunWT.letRecUnfold_preservation erased_polySelf_typed

#print axioms RunWT.substFvar
#print axioms TypeOfHM.erase_preserves_typing
#print axioms RunWT.substMany
#print axioms RunWT.letRecUnfold_preservation
#print axioms RunWT.preservation
#print axioms RunWT.progress
#print axioms annotated_polySelf_typed
#print axioms erased_polySelf_typed
#print axioms erased_polySelf_unfolded_typed

end RuntimeTyping
