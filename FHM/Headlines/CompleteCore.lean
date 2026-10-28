import FHM.Headlines
import FHM.SurfaceBridge.CompleteCore

/-! # Complete-Core compatibility headlines

This opt-in façade preserves the original structural surface-typing witnesses,
complete-Core inference adapter checks, and proof-carrying complete-Core
lower-and-run demonstration. The default `FHM.Headlines` module presents the
canonical surface-to-`InferInput` pipeline. -/

open SurfaceBridge SmallStep PatComp

namespace Headlines

#check @surface_type_safe
#check @program_type_safe
#check @SurfaceBridge.coreTypecheck_isSome_iff
#check @SurfaceBridge.inferOfCore_source_sound
#check @SurfaceBridge.inferOfCore_erase
#check @SurfaceBridge.coreTypecheck_accepts_iff
#check @SurfaceBridge.inferOfCore_principal

/-- The `of_lowers` overlap, kept as a documented example: a match-free
    `.pair` surface term has TWO derivation paths through `SurfaceWTExpr` — the
    dedicated `pair` rule, or the generic `of_lowers` catch-all (since `.pair`
    has no `match`, it's `SurfaceExprNoMatch`). Both agree on the resulting
    type. The relation intentionally permits this harmless overlap for
    match-free expressions. -/
theorem SurfaceWTExpr_pair_inv {ctors : CtorEnv} {ke : KindEnv} {tvs vs : List ValName}
    {Γ : Env} {a b : Surface.Expr} {τ : Ty}
    (h : SurfaceWTExpr ctors ke tvs vs Γ (.pair a b) τ) :
    (∃ τa τb, SurfaceWTExpr ctors ke tvs vs Γ a τa ∧ SurfaceWTExpr ctors ke tvs vs Γ b τb ∧
        TypeOfHM ⟨Γ, ctors⟩ (.ctor cPair) (.arrow τa (.arrow τb τ)))
    ∨ (SurfaceExprNoMatch (.pair a b) ∧
        ∃ c, CoreLowersExpr ctors ke tvs vs (.pair a b) c ∧ TypeOfHM ⟨Γ, ctors⟩ c τ) := by
  cases h with
  | pair ha hb hc => exact Or.inl ⟨_, _, ha, hb, hc⟩
  | of_lowers hnm hL hT => exact Or.inr ⟨hnm, _, hL, hT⟩
/-! ## Structural-typing witnesses

Axiom-cleanliness cannot catch a *vacuous* relation — a typing rule with
unsatisfiable premises would still let every proof by induction over it go
through, silently. Witnesses close that gap: they exhibit CONCRETE terms
that actually inhabit the relations above, so the rules used to build them
are provably not dead code. -/

/-- The simplest possible witness: an integer literal is well-typed at `int`. -/
example (ctors : CtorEnv) : SurfaceWT ctors (.primLit (.int 0)) :=
  ⟨.prim .int, .of_lowers .primLit .primLitInt .primLitInt⟩

/-- The identity function `λx. x`, typed structurally (monomorphically) at
    `int → int`. -/
example (ctors : CtorEnv) :
    SurfaceWTExpr ctors (kindEnvOfCtors ctors) [] [] []
      (.lambda (.name ⟨"x"⟩) none (.var ⟨"x"⟩)) (.arrow (.prim .int) (.prim .int)) := by
  apply SurfaceWTExpr.lambda_name
  · exact ContainsBvarsUpTo.prim
  · trivial
  · exact .of_lowers .var (.var (by rfl))
      (TypeOfHM.var (polyTy := PolyTy.mkTrivial (.prim .int)) (instArgs := []) rfl (by simp) .prim)

/-! ### The annotated polymorphic let (`letInAnn`)

`letInAnn` is the composer-authored, cofinite-premise constructor with the
fiddliest hypothesis in the whole relation: `∀ Xs, FreshNames L σ.paramCount
Xs → …`. This witness — `let (id : ∀a. a→a) = λx. x in id` used at `int→int`
— proves the constructor is genuinely inhabitable at a REAL polymorphic
scheme (not just the `paramCount = 0` degenerate case): specialise the
cofinite premise at a single fresh skolem `X`, observe `σ.openVars [X]` is
literally `fvar X → fvar X` by computation, and reuse the identity-lambda
shape above at `paramTy := .fvar X`. The body then instantiates the scheme's
bound variable at `int` via `InstantiatesBy.bvar`. -/
example (ctors : CtorEnv) :
    SurfaceWTExpr ctors (kindEnvOfCtors ctors) [] [] []
      (.letIn (.mk "id") [] []
        (some ⟨[.mk "a"], .arrow (.tvar (.mk "a")) (.tvar (.mk "a"))⟩)
        (.lambda (.name (.mk "x")) none (.var (.mk "x")))
        (.var (.mk "id")))
      (.arrow (.prim .int) (.prim .int)) := by
  set σ : PolyTy := ⟨1, .arrow (.bvar 0) (.bvar 0)⟩
  have hlowσ : lowerPoly (kindEnvOfCtors ctors)
      ⟨[.mk "a"], .arrow (.tvar (.mk "a")) (.tvar (.mk "a"))⟩ = some σ := by
    simp only [lowerPoly, σ]
    have h : ([.mk "a"] : List ValName).eraseDups = [.mk "a"] := rfl
    simp [h, lowerTy, tvarIndex]
  refine SurfaceWTExpr.letInAnn (tvs := []) (vs := []) (Γ := []) (ΓRhs := [])
    (name := .mk "id") (tyParams := []) (params := [])
    (σs := ⟨[.mk "a"], .arrow (.tvar (.mk "a")) (.tvar (.mk "a"))⟩)
    (σ := σ) (rhs := _) (body := _) (τ := _) (L := []) (paramTys := [])
    (τretOf := fun Xs => σ.openVars Xs) ?htvs ?hσeq ?hσwf ?hLL ?hrhs ?hτbinds ?hbody
  · rfl
  · exact lowerPolyAnn_finalizeAnn_nil hlowσ
  · exact .arrow (.bvar (by decide)) (.bvar (by decide))
  · exact LowerLetParams.nil
  · intro Xs hfresh
    have hlen : Xs.length = 1 := by simpa [σ] using hfresh.length
    obtain ⟨X, hXeq⟩ := List.length_eq_one_iff.mp hlen
    subst hXeq
    have hed : ([.mk "a"] : List ValName).eraseDups = [.mk "a"] := rfl
    have hscope : letRhsTyScope [] []
        (some ⟨[.mk "a"], .arrow (.tvar (.mk "a")) (.tvar (.mk "a"))⟩) [] = [.mk "a"] := by
      simp [letRhsTyScope, letAnnTyPrefix, finalizeAnn, mergeTyParams, mergeTyParamNames, hed]
    simp only [hscope, letRhsTermScope, paramTermScope, List.map_nil, List.reverse_nil,
      List.nil_append]
    apply SurfaceWTExpr.lambda_name (paramTy := .fvar X) (bodyTy := .fvar X)
    · exact ContainsBvarsUpTo.fvar
    · trivial
    · exact .of_lowers .var (.var (by rfl))
        (TypeOfHM.var (polyTy := PolyTy.mkTrivial (.fvar X)) (instArgs := []) rfl (by simp) .fvar)
  · intro Xs _; rfl
  · exact .of_lowers .var (.var (by rfl))
      (TypeOfHM.var (polyTy := σ) (instArgs := [Ty.prim .int]) rfl
        (by
          intro t ht
          simp only [List.mem_singleton] at ht
          subst ht
          exact ContainsBvarsUpTo.prim)
        (InstantiatesBy.arrow (InstantiatesBy.bvar rfl) (InstantiatesBy.bvar rfl)))

/-! ### Annotated polymorphic `letRecIn`

The structural constructor exposes the same contract boundary as Core: unsigned
members are monomorphic within the residual component currently being checked,
completed dependency components may already be generalized, and signed members are
checked under the final scheme environment. The closed monomorphic contract below
uses a single residual component, keeping the cofinite openings computationally
small while exercising `letRecInAnn`. -/

/-! ### Packing B — annotated mono + head binders

Surface-ish:
```
let f (x : Int) : Int = x in f
```
AST: nonempty `params`, return-type `ann`, open body (not `λ` in the RHS).
`finalizeAnn` synthesises the full binding scheme `Int → Int` (paramCount 0);
raw RHS is typed at the return type under the head binder; wrap supplies the
Core λ. -/
private theorem packingB_finalize :
    finalizeAnn [] [(.mk "x", some (.prim .int))] (some ⟨[], .prim .int⟩) =
      some ⟨[], .arrow (.prim .int) (.prim .int)⟩ := by
  simp [finalizeAnn, paramsToArrows, paramsToArrows.go, mergeTyParamNames]

private theorem packingB_lowerPoly (ctors : CtorEnv) :
    lowerPolyAnn (kindEnvOfCtors ctors)
      (finalizeAnn [] [(.mk "x", some (.prim .int))] (some ⟨[], .prim .int⟩)) =
      some (some ⟨0, .arrow (.prim .int) (.prim .int)⟩) := by
  rw [packingB_finalize]
  simp [lowerPolyAnn, lowerPoly, lowerTy]

example (ctors : CtorEnv) :
    SurfaceWTExpr ctors (kindEnvOfCtors ctors) [] [] []
      (.letIn (.mk "f") [] [(.mk "x", some (.prim .int))]
        (some ⟨[], .prim .int⟩)
        (.var (.mk "x"))
        (.var (.mk "f")))
      (.arrow (.prim .int) (.prim .int)) := by
  set σ : PolyTy := ⟨0, .arrow (.prim .int) (.prim .int)⟩
  set paramTys : List Ty := [.prim .int]
  set τret : Ty := .prim .int
  refine SurfaceWTExpr.letInAnn (tvs := []) (vs := []) (Γ := [])
    (ΓRhs := [PolyTy.mkTrivial (.prim .int)])
    (name := .mk "f") (tyParams := [])
    (params := [(.mk "x", some (.prim .int))])
    (σs := ⟨[], .prim .int⟩) (σ := σ)
    (rhs := _) (body := _) (τ := _) (L := [])
    (paramTys := paramTys) (τretOf := fun _ => τret)
    ?htvs ?hσeq ?hσwf ?hLL ?hrhs ?hτbinds ?hbody
  · rfl
  · simpa [σ] using packingB_lowerPoly ctors
  · -- `PolyTy.WF σ` = `ContainsBvarsUpTo 0 (Int → Int)`
    exact .arrow ContainsBvarsUpTo.prim ContainsBvarsUpTo.prim
  · refine LowerLetParams.cons rfl (by simp [lowerTy]) ContainsBvarsUpTo.prim LowerLetParams.nil
  · intro Xs hfresh
    have hXs : Xs = [] := List.eq_nil_of_length_eq_zero (by simpa [σ] using hfresh.length)
    subst hXs
    exact .of_lowers .var (.var (by rfl))
      (TypeOfHM.var (polyTy := PolyTy.mkTrivial (.prim .int)) (instArgs := []) rfl
        (by simp) .prim)
  · intro Xs hfresh
    have hXs : Xs = [] := List.eq_nil_of_length_eq_zero (by simpa [σ] using hfresh.length)
    subst hXs
    simp [paramTys, τret, σ, coreParamsToArrows, PolyTy.openVars]
  · exact .of_lowers .var (.var (by rfl))
      (TypeOfHM.var (polyTy := σ) (instArgs := []) rfl (by simp)
        (InstantiatesBy.arrow InstantiatesBy.prim InstantiatesBy.prim))

/-! ### Packing B — annotated mono letrec + head binders

Same packing as a singleton rec group (`RecSpec.poly` with `paramCount = 0`,
because Core stores annotated schemes via `RecSpec.poly`, not `mono`):
```
let f (x : Int) : Int = x in f
```
-/
example (ctors : CtorEnv) :
    SurfaceWTExpr ctors (kindEnvOfCtors ctors) [] [] []
      (.letRecIn
        [{ name := .mk "f",
           params := [(.mk "x", some (.prim .int))],
           ann := some ⟨[], .prim .int⟩,
           rhs := .var (.mk "x") }]
        (.var (.mk "f")))
      (.arrow (.prim .int) (.prim .int)) := by
  set σ : PolyTy := ⟨0, .arrow (.prim .int) (.prim .int)⟩
  set binds : List Surface.Binding :=
    [{ name := .mk "f",
       params := [(.mk "x", some (.prim .int))],
       ann := some ⟨[], .prim .int⟩,
       rhs := .var (.mk "x") }]
  refine SurfaceWTExpr.letRecInAnn (tvs := []) (vs := []) (Γ := [])
    (binds := binds) (anns' := [some σ]) (specs := [RecSpec.poly σ])
    (G := []) (L := []) (paramTysList := fun _ _ => [[Ty.prim .int]])
    (ΓRhsList := fun _ _ => [[PolyTy.mkTrivial (.prim .int), σ]])
    (τretsList := fun _ _ => [Ty.prim .int])
    (body := _) (τ := _)
    ?htvs ?hann ?hlen ?hparamLen ?hΓRhsLen ?hretsLen ?hanns_eq ?hnodup
    ?hmono_lc ?hpoly_wf ?hLLMono ?hLLPoly ?hτbindsMono ?hτbindsPoly
    ?hmono ?hpoly ?hbody
  · rfl
  · -- lowerAnnList of finalizeAnn return-type sugar
    have h1 := packingB_lowerPoly ctors
    simp [binds, lowerAnnList, h1, σ]
  · rfl
  · intro Xs Ys; rfl
  · intro Xs Ys; rfl
  · intro Xs Ys; rfl
  · rfl  -- RecSpec.ann (poly σ) = some σ
  · exact List.nodup_nil
  · intro τm h; simp [σ] at h
  · intro σ' h
    simp only [List.mem_singleton, σ] at h
    injection h with h; subst h
    exact .arrow ContainsBvarsUpTo.prim ContainsBvarsUpTo.prim
  · intro Xs _ i hi τm hspec
    have hi0 : i = 0 := by
      simp only [binds, List.length_cons, List.length_nil] at hi; omega
    subst hi0
    simp [σ] at hspec
  · intro i hi σ' hspec Ys hYs
    have hi0 : i = 0 := by
      simp only [binds, List.length_cons, List.length_nil] at hi; omega
    subst hi0
    have hσ' : σ' = σ := by symm; simpa using hspec
    subst hσ'
    refine LowerLetParams.cons rfl (by simp [lowerTy]) ContainsBvarsUpTo.prim LowerLetParams.nil
  · intro Xs hfresh i hi τm hspec
    have hi0 : i = 0 := by
      simp only [binds, List.length_cons, List.length_nil] at hi; omega
    subst hi0
    simp [σ] at hspec
  · intro i hi σ' hspec Ys hYs
    have hi0 : i = 0 := by
      simp only [binds, List.length_cons, List.length_nil] at hi; omega
    subst hi0
    have hσ' : σ' = σ := by symm; simpa using hspec
    subst hσ'
    have hYs0 : Ys = [] := List.eq_nil_of_length_eq_zero (by simpa [σ] using hYs.length)
    subst hYs0
    simp [σ, coreParamsToArrows, PolyTy.openVars]
  · intro Xs hfresh i hi τm hspec
    have hi0 : i = 0 := by
      simp only [binds, List.length_cons, List.length_nil] at hi; omega
    subst hi0
    simp [σ] at hspec
  · intro i hi σ' hspec Ys hYs
    have hi0 : i = 0 := by
      simp only [binds, List.length_cons, List.length_nil] at hi; omega
    subst hi0
    have hσ' : σ' = σ := by symm; simpa using hspec
    subst hσ'
    have hYs0 : Ys = [] := List.eq_nil_of_length_eq_zero (by simpa [σ] using hYs.length)
    subst hYs0
    exact .of_lowers .var (.var (by rfl))
      (TypeOfHM.var (polyTy := PolyTy.mkTrivial (.prim .int)) (instArgs := []) rfl
        (by simp) .prim)
  · exact .of_lowers .var (.var (by rfl))
      (TypeOfHM.var (polyTy := σ) (instArgs := []) rfl (by simp)
        (InstantiatesBy.arrow InstantiatesBy.prim InstantiatesBy.prim))


/-- Complete-Core safe-lowering demonstration, separate from production Input
    elaboration. `lowerCoreProgram` rejects holeful types; the CLI/editor instead use
    provenance lowering and canonical `inferWithTypes`.
    Run a surface program through both checks (typechecking, via
    canonical `inferWithTypes`, and exhaustiveness, via `checkExhaustive`); `some ⟨ctors, ⟨e,
    _⟩⟩` hands back a term that is well-typed AND exhaustive **by
    construction** — the proof is built once here from `program_type_safe` +
    `checkExhaustive_sound` and travels with the term from then on. `none`
    means the program was rejected by lowering, typechecking, or coverage. -/
def elaborateSafe (p : Surface.Program) : Option (Σ ctors : CtorEnv, Safe ctors) :=
  match hlow : lowerCoreProgram p with
  | none => none
  | some (ctors, c) =>
    match hresult : inferWithTypes ctors (InferInput.ofCore c) with
    | none => none
    | some result =>
      match hcov : checkExhaustive ctors p.term with
      | false => none
      | true =>
        some ⟨ctors, ⟨c.erase, by
          obtain ⟨τ, hty, hexh, _⟩ := program_type_safe hlow
            (coreTypecheck_of_infer hresult) (checkExhaustive_sound p.term hcov)
          exact ⟨Expr.erase_idem _, ⟨τ, hty⟩, hexh⟩⟩⟩
/-! ## Demos

Two small end-to-end runs through `elaborateSafe`/`runSafe`: one that's
accepted (a polymorphic `id`, applied at `int`), and one that's correctly
REJECTED for missing a match arm — `elaborateSafe` returning `none` there is
the pipeline doing its job, not a bug. -/

/-- `let (id : ∀a. a→a) = λx. x in id 41`  — accepted, runs to `41`. -/
private def sHeadlineAnnId : Surface.Program :=
  ⟨[], [],
   .letIn (.mk "id") [] []
     (some ⟨[.mk "a"], .arrow (.tvar (.mk "a")) (.tvar (.mk "a"))⟩)
     (.lambda (.name (.mk "x")) none (.var (.mk "x")))
     (.app (.var (.mk "id")) (.primLit (.int 41)))⟩

/-- `match Just 5 with Just x => x`  — missing the `Nothing` arm, so coverage
    fails and `elaborateSafe` must reject it. -/
private def sHeadlineNonExhaustive : Surface.Program :=
  ⟨[⟨.mk "Maybe", [.mk "a"],
      [(.mk "Just", [.tvar (.mk "a")]), (.mk "Nothing", [])]⟩],
   [],
   .match_ (.app (.ctor ⟨"Just"⟩) (.primLit (.int 5)))
     [(.ctor ⟨"Just"⟩ [.name ⟨"x"⟩], .var ⟨"x"⟩)]⟩

/-- Run a program through the full safe pipeline and print the result: a
    finished value, a still-safe-but-unfinished term (fuel ran out — genuinely
    resumable via `Running.toSafe`), or a rejection from `elaborateSafe`
    itself (ill-typed or non-exhaustive). -/
private def runSafeStr (p : Surface.Program) (fuel : Nat := 100) : String :=
  match elaborateSafe p with
  | none => "elaborateSafe: rejected"
  | some ⟨ctors, t⟩ =>
    match runSafe ctors fuel t with
    | .inl v => toString v.val
    | .inr r => "still running: " ++ toString r.val

#eval! runSafeStr sHeadlineAnnId
#guard runSafeStr sHeadlineAnnId = "41"

-- The same program, starved of fuel: `elaborateSafe` still accepts it (it IS
-- safe), but `runSafe` can't finish in zero steps, so it lands in `.inr`
-- instead of `.inl` — the resumable, "genuinely more to do" outcome.
#eval! runSafeStr sHeadlineAnnId 0

#eval! runSafeStr sHeadlineNonExhaustive
#guard (elaborateSafe sHeadlineNonExhaustive).isSome = false


/-! ## Compatibility axiom-budget guards -/

#print axioms SurfaceBridge.coreTypecheck_isSome_iff
#print axioms SurfaceBridge.inferOfCore_source_sound
#print axioms SurfaceBridge.inferOfCore_erase
#print axioms SurfaceBridge.coreTypecheck_accepts_iff
#print axioms SurfaceBridge.inferOfCore_principal
#print axioms elaborateSafe

end Headlines
