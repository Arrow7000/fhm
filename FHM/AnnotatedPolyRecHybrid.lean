import FHM.AnnotatedPolyRecErasure

/-!
# Mixed annotated/unannotated recursion over an erased runtime

This module is the second formal spike for annotated in-block polymorphism.  The
first spike, `FHM.AnnotatedPolyRecErasure`, proves erasure and recursive-unfolding
preservation when every member has a complete scheme.  Here the proof-only
runtime judgment records a `RecSpec` per member:

* `.poly σ` is available at `σ` while the group is checked and in its body;
* `.mono τ` is available at one shared opening of `τ` inside the group, then at
  `PolyTy.genGroup G τ` in the body; and
* neither the specs nor `G` occur in `RunExpr`.

The initial checkpoint fixes the mixed declarative rule and a concrete witness.
Its next obligation is the mixed recursive-rewrapping/preservation theorem.
-/

namespace AnnotatedPolyRecHybrid

open AnnotatedPolyRecErasure

/-- The proof-only recursive environment at one shared opening of the
unannotated members' generalisation pool. -/
def rhsEnv (env : Env) (specs : List RecSpec) (G Xs : List Nat) : Env :=
  specs.map (RecSpec.rhsEntry G Xs) ++ env

/-- The environment outside the recursive block.  Only here are unannotated
members generalized. -/
def bodyEnv (env : Env) (specs : List RecSpec) (G : List Nat) : Env :=
  specs.map (RecSpec.bodyScheme G) ++ env

/-- Runtime well-formedness deliberately contains no source-annotation
alignment premise: annotations have already erased. -/
structure SpecsWF (bindings : List RunExpr) (specs : List RecSpec)
    (G : List Nat) : Prop where
  length : bindings.length = specs.length
  nodup : G.Nodup
  mono_lc : ∀ τ, .mono τ ∈ specs → τ.IsLC
  poly_wf : ∀ σ, .poly σ ∈ specs → σ.WF

/-- The Damas--Milner half of a mixed group.  All unannotated members share the
same pool opening `G ↦ Xs`, hence remain monomorphic inside the SCC. -/
def MonoChecks (TypeOf : Env → RunExpr → Ty → Prop) (env : Env)
    (bindings : List RunExpr) (specs : List RecSpec) (G avoid : List Nat) : Prop :=
  ∀ Xs, FreshNames avoid G.length Xs →
    ∀ pair ∈ bindings.zip specs, ∀ τ, pair.2 = .mono τ →
      TypeOf (rhsEnv env specs G Xs) pair.1 (Ty.renameG G Xs τ)

/-- The annotation-directed half.  Pool names are chosen first; each annotated
member is then checked at its own rigid opening, whose names must also avoid the
pool opening. -/
def PolyChecks (TypeOf : Env → RunExpr → Ty → Prop) (env : Env)
    (bindings : List RunExpr) (specs : List RecSpec) (G avoid : List Nat) : Prop :=
  ∀ Xs, FreshNames avoid G.length Xs →
    ∀ pair ∈ bindings.zip specs, ∀ σ, pair.2 = .poly σ →
      ∀ Ys, FreshNames (avoid ++ Xs) σ.paramCount Ys →
        TypeOf (rhsEnv env specs G Xs) pair.1 (σ.openVars Ys)

def GeneralisesTo (TypeOf : Env → RunExpr → Ty → Prop) (env : Env)
    (scheme : PolyTy) (rhs : RunExpr) (avoid : List Nat) : Prop :=
  ∀ Xs, FreshNames avoid scheme.paramCount Xs →
    TypeOf env rhs (scheme.openVars Xs)

/-- Typing for erased runtime terms with a mixed proof-only recursive witness. -/
inductive HybridWT : Env → RunExpr → Ty → Prop
  | int : HybridWT env (.int n) (.prim .int)
  | var :
      env[index]? = some scheme →
      InstArgs scheme args →
      HybridWT env (.var index) (scheme.openWith args)
  | lam :
      HybridWT (PolyTy.mkTrivial paramTy :: env) body resultTy →
      HybridWT env (.lam body) (.arrow paramTy resultTy)
  | app :
      HybridWT env fn (.arrow argTy resultTy) →
      HybridWT env arg argTy →
      HybridWT env (.app fn arg) resultTy
  | letIn {scheme : PolyTy} {avoid : List Nat} :
      scheme.WF →
      GeneralisesTo HybridWT env scheme rhs avoid →
      HybridWT (scheme :: env) body resultTy →
      HybridWT env (.letIn rhs body) resultTy
  | letRec {specs : List RecSpec} {G avoid : List Nat} :
      SpecsWF bindings specs G →
      MonoChecks HybridWT env bindings specs G avoid →
      PolyChecks HybridWT env bindings specs G avoid →
      HybridWT (bodyEnv env specs G) body resultTy →
      HybridWT env (.letRec bindings body) resultTy

/-! ## A concrete mixed-group witness -/

/-- The unannotated member's shared monotype, before opening/generalisation. -/
def mixedIdTy : Ty := .arrow (.fvar 0) (.fvar 0)

def mixedSpecs : List RecSpec :=
  [.poly polyConstInt, .mono mixedIdTy]

/-- The annotated member: `forall a. a -> Int`. -/
def mixedPolyRhs : RunExpr := .lam (.int 0)

/-- The unannotated member: ordinary identity, monomorphic inside the group. -/
def mixedMonoRhs : RunExpr := .lam (.var 0)

def mixedBindings : List RunExpr := [mixedPolyRhs, mixedMonoRhs]

/-- Outside the group, the unannotated identity is used at `Int`. -/
def mixedBody : RunExpr := .app (.var 1) (.int 0)

def polyId : PolyTy := ⟨1, .arrow (.bvar 0) (.bvar 0)⟩

theorem mixedId_bodyScheme :
    PolyTy.genGroup [0] mixedIdTy = polyId := by
  simp [PolyTy.genGroup, Ty.genFilter, mixedIdTy, polyId,
    Ty.freeVars, Ty.closeOver]

theorem mixed_specs_wf : SpecsWF mixedBindings mixedSpecs [0] := by
  refine ⟨by simp [mixedBindings, mixedSpecs], by simp, ?_, ?_⟩
  · intro τ hτ
    simp [mixedSpecs] at hτ
    subst τ
    exact .arrow .fvar .fvar
  · intro σ hσ
    simp [mixedSpecs] at hσ
    subst σ
    exact polyConstInt_wf

private theorem singleton_of_fresh_one {avoid names : List Nat}
    (h : FreshNames avoid 1 names) : ∃ x, names = [x] := by
  exact List.length_eq_one_iff.mp h.length

theorem mixed_mono_checks :
    MonoChecks HybridWT [] mixedBindings mixedSpecs [0] [] := by
  intro Xs hXs pair hpair τ hmono
  obtain ⟨X, rfl⟩ := singleton_of_fresh_one hXs
  simp [mixedBindings, mixedSpecs] at hpair
  rcases hpair with hfirst | hsecond
  · subst pair
    simp at hmono
  · subst pair
    simp only [RecSpec.mono.injEq] at hmono
    subst τ
    change HybridWT
      [polyConstInt, PolyTy.mkTrivial (.arrow (.fvar X) (.fvar X))]
      mixedMonoRhs (.arrow (.fvar X) (.fvar X))
    apply HybridWT.lam
    have hx := HybridWT.var
      (env := [PolyTy.mkTrivial (.fvar X), polyConstInt,
        PolyTy.mkTrivial (.arrow (.fvar X) (.fvar X))])
      (index := 0) (scheme := PolyTy.mkTrivial (.fvar X)) (args := [])
      rfl ⟨rfl, by simp⟩
    simpa [PolyTy.openWith, PolyTy.mkTrivial, Ty.openWith,
      Ty.instantiate] using hx

theorem mixed_poly_checks :
    PolyChecks HybridWT [] mixedBindings mixedSpecs [0] [] := by
  intro Xs hXs pair hpair σ hpoly Ys hYs
  obtain ⟨X, rfl⟩ := singleton_of_fresh_one hXs
  simp [mixedBindings, mixedSpecs] at hpair
  rcases hpair with hfirst | hsecond
  · subst pair
    simp only [RecSpec.poly.injEq] at hpoly
    subst σ
    obtain ⟨Y, rfl⟩ := singleton_of_fresh_one hYs
    change HybridWT
      [polyConstInt, PolyTy.mkTrivial (.arrow (.fvar X) (.fvar X))]
      mixedPolyRhs (.arrow (.fvar Y) (.prim .int))
    exact .lam .int
  · subst pair
    simp at hpoly

theorem mixed_body_typed :
    HybridWT (bodyEnv [] mixedSpecs [0]) mixedBody (.prim .int) := by
  rw [show bodyEnv [] mixedSpecs [0] = [polyConstInt, polyId] by
    simp [bodyEnv, mixedSpecs, RecSpec.bodyScheme, mixedId_bodyScheme]]
  apply HybridWT.app (argTy := .prim .int)
  · exact .var (index := 1) (scheme := polyId) (args := [.prim .int]) rfl
      ⟨by simp [polyId], by simp; exact ContainsBvarsUpTo.prim⟩
  · exact .int

/-- The same proof-only recursive group presents its unannotated member as one
monotype inside the SCC and as a generalized scheme in the body. -/
theorem mixed_runtime_typed :
    HybridWT [] (.letRec mixedBindings mixedBody) (.prim .int) := by
  exact .letRec mixed_specs_wf mixed_mono_checks mixed_poly_checks mixed_body_typed

#print axioms mixed_runtime_typed

end AnnotatedPolyRecHybrid
