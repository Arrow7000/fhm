import FHM.RuntimeTyping

namespace RuntimeTyping

/-! ## An erased polymorphic-recursion witness -/

def polyId : PolyTy := ⟨1, .arrow (.bvar 0) (.bvar 0)⟩

/-- `fun x => (fun _ => x) (self 0)`: the current call is at a rigid `a`,
while the recursive occurrence is independently instantiated at `Int`. -/
def polySelfRhs : Expr :=
  .lambda none
    (.app (.lambda none (.var 1)) (.app (.var 1) (.primLit (.int 0))))

def erasedPolySelfBindings : List CoreRecBinding :=
  [{ ann := none, rhs := polySelfRhs }]

theorem polyId_wf : polyId.WF := by
  show ContainsBvarsUpTo 1 (.arrow (.bvar 0) (.bvar 0))
  exact .arrow (.bvar (by omega)) (.bvar (by omega))

theorem polySelf_specs_wf :
    RecSpecsWF erasedPolySelfBindings [.poly polyId] [] := by
  refine ⟨by simp [erasedPolySelfBindings], by simp, ?_, ?_⟩
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
  simp [erasedPolySelfBindings] at hpair
  subst pair
  simp at hmono

private theorem singleton_of_fresh_one {avoid names : List Nat}
    (h : FreshNames avoid 1 names) : ∃ name, names = [name] := by
  exact List.length_eq_one_iff.mp h.length

theorem polySelf_poly :
    PolyTyped RunWT ⟨[], []⟩ erasedPolySelfBindings [.poly polyId] [] [] := by
  intro pair hpair scheme hscheme Ys hYs
  simp [erasedPolySelfBindings] at hpair
  subst pair
  simp only [RecSpec.poly.injEq] at hscheme
  subst scheme
  obtain ⟨Y, rfl⟩ := singleton_of_fresh_one hYs
  change RunWT ⟨[polyId], []⟩ polySelfRhs
    (.arrow (.fvar Y) (.fvar Y))
  simp only [polySelfRhs]
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

/-- Runtime recursion retains its scheme witnesses in the derivation, while
the executable syntax contains no annotations or type applications. -/
theorem erased_polySelf_typed :
    RunWT ⟨[], []⟩
      (.letRec erasedPolySelfBindings (.var 0))
      (.arrow (.prim .unit) (.prim .unit)) :=
  .letRec polySelf_specs_wf polySelf_mono polySelf_poly polySelf_body

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
#print axioms RunWT.substMany
#print axioms RunWT.letRecUnfold_preservation
#print axioms RunWT.preservation
#print axioms RunWT.progress
#print axioms erased_polySelf_typed
#print axioms erased_polySelf_unfolded_typed

end RuntimeTyping
