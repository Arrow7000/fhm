import FHM.Core

/-!
# Typing for fully erased runtime terms

`TypeOfHM` specifies which annotated source programs the checker accepts.
`RunWT` instead types machine terms after every annotation has disappeared.
Its recursive schemes are proof-only witnesses: they are not recoverable from,
and do not occur in, the `Expr` being evaluated.

The recursive rule is deliberately mixed:

* `.poly σ` members are available at the complete scheme `σ` inside the SCC;
* `.mono τ` members share one monotype inside the SCC and are generalized only
  in the enclosing body; and
* the runtime node stores only `none` annotations.

This module initially fixes the production judgment and a real-`Expr` witness.
Erasure soundness and operational preservation are proved in subsequent
checkpoints, using the completed small-calculus proofs as their template.
-/

namespace RuntimeTyping

/-- Runtime group evidence has no source-annotation alignment premise: those
annotations have already erased. -/
structure RecSpecsWF (bindings : List Expr) (specs : List RecSpec)
    (G : List Nat) : Prop where
  length : bindings.length = specs.length
  nodup : G.Nodup
  mono_lc : ∀ τ, .mono τ ∈ specs → τ.IsLC
  poly_wf : ∀ σ, .poly σ ∈ specs → σ.WF

/-- Ordinary HM members share one opening of the group's generalisation pool. -/
def MonoTyped (TypeOf : Ctx → Expr → Ty → Prop) (ctx : Ctx)
    (bindings : List Expr) (specs : List RecSpec) (G avoid : List Nat) : Prop :=
  ∀ Xs, FreshNames avoid G.length Xs →
    ∀ pair ∈ bindings.zip specs, ∀ τ, pair.2 = .mono τ →
      TypeOf (RecSpecs.rhsCtx ctx specs G Xs) pair.1 (Ty.renameG G Xs τ)

/-- Complete annotations enable scheme-polymorphic recursive use. Runtime terms
contain no type syntax, so only the expected type is opened at the member's
fresh rigid names. -/
def PolyTyped (TypeOf : Ctx → Expr → Ty → Prop) (ctx : Ctx)
    (bindings : List Expr) (specs : List RecSpec) (G avoid : List Nat) : Prop :=
  ∀ Xs, FreshNames avoid G.length Xs →
    ∀ pair ∈ bindings.zip specs, ∀ σ, pair.2 = .poly σ →
      ∀ Ys, FreshNames (avoid ++ Xs) σ.paramCount Ys →
        TypeOf (RecSpecs.rhsCtx ctx specs G Xs) pair.1 (σ.openVars Ys)

def GeneralisesTo (TypeOf : Ctx → Expr → Ty → Prop) (ctx : Ctx)
    (rhs : Expr) (scheme : PolyTy) (avoid : List Nat) : Prop :=
  ∀ Xs, FreshNames avoid scheme.paramCount Xs →
    TypeOf ctx rhs (scheme.openVars Xs)

mutual

/-- Typing for annotation-free machine terms. -/
inductive RunWT : Ctx → Expr → Ty → Prop
  | primLitUnit : RunWT ctx (.primLit .unit) (.prim .unit)
  | primLitInt : RunWT ctx (.primLit (.int n)) (.prim .int)
  | primLitNat : RunWT ctx (.primLit (.nat n)) (.prim .nat)
  | primLitChar : RunWT ctx (.primLit (.char c)) (.prim .char)
  | primBinOpIntAdd :
      RunWT ctx (.primBinOp .intAdd)
        (.arrow (.prim .int) (.arrow (.prim .int) (.prim .int)))
  | primBinOpIntSub :
      RunWT ctx (.primBinOp .intSub)
        (.arrow (.prim .int) (.arrow (.prim .int) (.prim .int)))
  | primBinOpIntLt :
      RunWT ctx (.ctor ⟨"True"⟩) (.customTy ⟨"Bool"⟩ []) →
      RunWT ctx (.ctor ⟨"False"⟩) (.customTy ⟨"Bool"⟩ []) →
      RunWT ctx (.primBinOp .intLt)
        (.arrow (.prim .int) (.arrow (.prim .int) (.customTy ⟨"Bool"⟩ [])))
  | primBinOpCharLt :
      RunWT ctx (.ctor ⟨"True"⟩) (.customTy ⟨"Bool"⟩ []) →
      RunWT ctx (.ctor ⟨"False"⟩) (.customTy ⟨"Bool"⟩ []) →
      RunWT ctx (.primBinOp .charLt)
        (.arrow (.prim .char) (.arrow (.prim .char) (.customTy ⟨"Bool"⟩ [])))
  | lambda :
      paramTy.IsLC →
      RunWT { ctx with env := PolyTy.mkTrivial paramTy :: ctx.env }
        body bodyTy →
      RunWT ctx (.lambda none body) (.arrow paramTy bodyTy)
  | app :
      RunWT ctx fn (.arrow argTy resultTy) →
      RunWT ctx arg argTy →
      RunWT ctx (.app fn arg) resultTy
  | letIn {scheme : PolyTy} {avoid : List Nat} :
      scheme.WF →
      GeneralisesTo RunWT ctx rhs scheme avoid →
      RunWT { ctx with env := scheme :: ctx.env } body resultTy →
      RunWT ctx (.letIn none rhs body) resultTy
  | var :
      ctx.env[index]? = some scheme →
      (∀ arg ∈ args, arg.IsLC) →
      scheme.InstantiatesTo args ty →
      RunWT ctx (.var index) ty
  | ctor :
      LookupList.get? ctx.ctors name = some ctor →
      (∀ arg ∈ args, arg.IsLC) →
      ctor.toTy.InstantiatesTo args ty →
      RunWT ctx (.ctor name) ty
  | match_ :
      RunWT ctx scrutinee scrutTy →
      branches ≠ [] →
      (∀ branch ∈ branches,
        RunWTMatchBranch ctx branch scrutTy resultTy) →
      RunWT ctx (.match_ scrutinee branches) resultTy
  | letRec {specs : List RecSpec} {G avoid : List Nat} :
      RecSpecsWF bindings specs G →
      MonoTyped RunWT ctx bindings specs G avoid →
      PolyTyped RunWT ctx bindings specs G avoid →
      RunWT (RecSpecs.bodyCtx ctx specs G) body resultTy →
      RunWT ctx (.letRec (bindings.map (fun _ => none)) bindings body) resultTy

/-- Match-branch typing for erased terms. -/
inductive RunWTMatchBranch :
    Ctx → (MatchPattern × Expr) → Ty → Ty → Prop
  | mk {ctor : Ctor} {ctx : Ctx} {c : CtorName} {n : Nat}
      {tyArgs instContents : List Ty} :
      BranchCtorSpec ctx.ctors c n scrutTy ctor tyArgs instContents →
      RunWT { ctx with env := instContents.map PolyTy.mkTrivial ++ ctx.env }
        body resultTy →
      RunWTMatchBranch ctx (.named c n, body) scrutTy resultTy
  | wildcard :
      RunWT ctx body resultTy →
      RunWTMatchBranch ctx (.wildcard, body) scrutTy resultTy

end


/-! ## Runtime type substitution

This is proof-only substitution.  Runtime expressions contain no type
annotations, so substituting a free type variable changes the context and the
derived type but leaves the expression itself untouched.  The recursive case
freshens the shared HM pool before applying the substitution.
-/

private theorem Ty.IsLC.substFvars_runtime {pairs : List (Nat × Ty)} {ty : Ty}
    (hpairs : ∀ pair ∈ pairs, pair.2.IsLC) (hty : ty.IsLC) :
    (Ty.substFvars pairs ty).IsLC := by
  induction pairs generalizing ty with
  | nil => exact hty
  | cons pair rest ih =>
      obtain ⟨name, replacement⟩ := pair
      simp only [Ty.substFvars]
      exact ih
        (fun pair hpair => hpairs pair (List.mem_cons_of_mem _ hpair))
        (Ty.IsLC.substFvar (hpairs (name, replacement) List.mem_cons_self) hty)

private theorem Ty.renameG_isLC_runtime {G Xs : List Nat} {ty : Ty}
    (hty : ty.IsLC) : (Ty.renameG G Xs ty).IsLC := by
  unfold Ty.renameG
  apply Ty.IsLC.substFvars_runtime
  · intro pair hpair
    obtain ⟨name, _, heq⟩ := List.mem_map.mp (List.of_mem_zip hpair).2
    rw [← heq]
    exact ContainsBvarsUpTo.fvar
  · exact hty

private theorem mem_zip_map_right_runtime {α β γ : Type _} {f : β → γ} :
    ∀ {left : List α} {right : List β} {pair : α × γ},
      pair ∈ left.zip (right.map f) →
      ∃ a b, (a, b) ∈ left.zip right ∧ pair = (a, f b) := by
  intro left
  induction left with
  | nil => intro right pair hpair; simp at hpair
  | cons head tail ih =>
      intro right pair hpair
      cases right with
      | nil => simp at hpair
      | cons rhead rtail =>
          simp only [List.map_cons, List.zip_cons_cons, List.mem_cons] at hpair
          rcases hpair with hpair | hpair
          · exact ⟨head, rhead, by simp, hpair⟩
          · obtain ⟨a, b, hab, heq⟩ := ih hpair
            exact ⟨a, b, by simp [hab], heq⟩

private def substSpecs (Z : Nat) (U : Ty) (G W : List Nat)
    (specs : List RecSpec) : List RecSpec :=
  specs.map (RecSpec.substFreshened Z U G W)

theorem RunWT.substFvar {ctx : Ctx} {e : Expr} {ty U : Ty} {Z : Nat}
    (hU : U.IsLC) (h : RunWT ctx e ty) :
    RunWT { ctx with env := ctx.env.substFvar Z U } e
      (Ty.substFvar Z U ty) := by
  induction h using RunWT.rec
    (motive_2 := fun ctx branch scrutTy resultTy _ =>
      RunWTMatchBranch { ctx with env := ctx.env.substFvar Z U }
        branch (Ty.substFvar Z U scrutTy) (Ty.substFvar Z U resultTy)) with
  | primLitUnit => exact .primLitUnit
  | primLitInt => exact .primLitInt
  | primLitNat => exact .primLitNat
  | primLitChar => exact .primLitChar
  | primBinOpIntAdd => exact .primBinOpIntAdd
  | primBinOpIntSub => exact .primBinOpIntSub
  | primBinOpIntLt _ _ ihtrue ihfalse =>
      exact .primBinOpIntLt ihtrue ihfalse
  | primBinOpCharLt _ _ ihtrue ihfalse =>
      exact .primBinOpCharLt ihtrue ihfalse
  | lambda hparam _ ihbody =>
      expose_names
      simpa only [Env.substFvar, List.map_cons, PolyTy.substFvar,
        PolyTy.mkTrivial] using
        (RunWT.lambda (ctx := { ctx_1 with env := ctx_1.env.substFvar Z U })
          (Ty.IsLC.substFvar hU hparam) ihbody)
  | app _ _ ihfn iharg => exact .app ihfn iharg
  | letIn hwf hgen _ ihgen ihbody =>
      expose_names
      let avoid' := Z :: avoid
      apply RunWT.letIn (scheme := scheme.substFvar Z U) (avoid := avoid')
      · exact hwf.substFvar hU
      · intro names hfresh
        have hfresh0 : FreshNames avoid scheme.paramCount names := by
          refine ⟨by simpa [PolyTy.substFvar] using hfresh.length,
            hfresh.nodup, ?_⟩
          intro x hx hmem
          exact hfresh.avoid x hx (List.mem_cons_of_mem _ hmem)
        have hZ : Z ∉ names := fun hmem =>
          hfresh.avoid Z hmem List.mem_cons_self
        have hrhs := ihgen names hfresh0
        rw [PolyTy.substFvar_openVars hU hZ]
        exact hrhs
      · simpa only [Env.substFvar, List.map_cons] using ihbody
  | var hlookup hlc hinst =>
      expose_names
      have hlookup' : (ctx_1.env.substFvar Z U)[index]? =
          some (scheme.substFvar Z U) := by
        simp only [Env.substFvar, List.getElem?_map, hlookup, Option.map_some]
      apply RunWT.var (ctx := { ctx_1 with env := ctx_1.env.substFvar Z U })
        (args := args.map (Ty.substFvar Z U))
        hlookup'
      · intro arg harg
        obtain ⟨arg0, harg0, rfl⟩ := List.mem_map.mp harg
        exact Ty.IsLC.substFvar hU (hlc arg0 harg0)
      · exact InstantiatesBy.substFvar hU hinst
  | ctor hlookup hlc hinst =>
      expose_names
      have hinst' := InstantiatesBy.substFvar (Z := Z) (U := U) hU hinst
      rw [Ty.substFvar_fresh
        (NoFreeVars.not_mem_freeVars (Ctor.toTy_body_noFreeVars _) Z)] at hinst'
      apply RunWT.ctor (ctx := { ctx_1 with env := ctx_1.env.substFvar Z U })
        (args := args.map (Ty.substFvar Z U))
        hlookup
      · intro arg harg
        obtain ⟨arg0, harg0, rfl⟩ := List.mem_map.mp harg
        exact Ty.IsLC.substFvar hU (hlc arg0 harg0)
      · exact hinst'
  | match_ _ hne _ ihscrut ihbranches =>
      exact .match_ ihscrut hne ihbranches
  | @letRec bindings ctx body resultTy specs G avoid hwf hmono hpoly _
      ihmono ihpoly ihbody =>
      obtain ⟨W, hWlen, hWnodup, hWavoid⟩ :=
        exists_fresh_names
          (G ++ [Z] ++ U.freeVars ++ specs.flatMap RecSpec.monoFreeVars)
          G.length
      have hGW : ∀ g ∈ G, g ∉ W := fun g hg hc =>
        hWavoid g hc (by simp [List.mem_append, hg])
      have hZW : Z ∉ W := fun hc =>
        hWavoid Z hc (by simp [List.mem_append])
      have hUW : ∀ u ∈ U.freeVars, u ∉ W := fun u hu hc =>
        hWavoid u hc (by simp [List.mem_append, hu])
      have hWfree : ∀ τ, RecSpec.mono τ ∈ specs →
          ∀ w ∈ W, w ∉ τ.freeVars := by
        intro τ hτ w hw hc
        have hflat : w ∈ specs.flatMap RecSpec.monoFreeVars :=
          List.mem_flatMap.mpr ⟨.mono τ, hτ, hc⟩
        exact hWavoid w hw (by simp [List.mem_append, hflat])
      let specs' := substSpecs Z U G W specs
      let avoid' := Z :: G ++ W ++ avoid
      have hwf' : RecSpecsWF bindings specs' W := by
        refine ⟨by simpa [specs', substSpecs] using hwf.length,
          hWnodup, ?_, ?_⟩
        · intro τ' hτ'
          obtain ⟨spec, hspec, heq⟩ := List.mem_map.mp hτ'
          cases spec with
          | mono τ =>
              simp only [RecSpec.substFreshened, RecSpec.mono.injEq] at heq
              subst τ'
              exact Ty.IsLC.substFvar hU
                (Ty.renameG_isLC_runtime (hwf.mono_lc τ hspec))
          | poly scheme => exact RecSpec.noConfusion heq
        · intro scheme' hscheme'
          obtain ⟨spec, hspec, heq⟩ := List.mem_map.mp hscheme'
          cases spec with
          | mono τ => exact RecSpec.noConfusion heq
          | poly scheme =>
              simp only [RecSpec.substFreshened, RecSpec.poly.injEq] at heq
              subst scheme'
              exact (hwf.poly_wf scheme hspec).substFvar hU
      apply RunWT.letRec (specs := specs') (G := W) (avoid := avoid') hwf'
      · intro Xs hXs pair hpair τ' hτ'
        have hXlen : Xs.length = G.length := hXs.length.trans hWlen
        have hZXs : Z ∉ Xs := fun hc =>
          hXs.avoid Z hc (by simp [avoid'])
        have hGXs : ∀ g ∈ G, g ∉ Xs := fun g hg hc =>
          hXs.avoid g hc (by simp [avoid', List.mem_append, hg])
        have hWXs : ∀ w ∈ W, w ∉ Xs := fun w hw hc =>
          hXs.avoid w hc (by simp [avoid', List.mem_append, hw])
        have hXs0 : FreshNames avoid G.length Xs := by
          refine ⟨hXlen, hXs.nodup, ?_⟩
          intro x hx ha
          exact hXs.avoid x hx (by simp [avoid', List.mem_append, ha])
        obtain ⟨rhs0, spec0, hold, rfl⟩ := mem_zip_map_right_runtime hpair
        cases spec0 with
        | poly scheme => exact RecSpec.noConfusion hτ'
        | mono τ =>
            simp only [RecSpec.substFreshened, RecSpec.mono.injEq] at hτ'
            subst τ'
            have hτmem : RecSpec.mono τ ∈ specs := (List.of_mem_zip hold).2
            have hkey :
                Ty.renameG W Xs (Ty.substFvar Z U (Ty.renameG G W τ)) =
                  Ty.substFvar Z U (Ty.renameG G Xs τ) := by
              rw [Ty.renameG_substFvar_comm hU hZW hUW hZXs
                    (Ty.renameG_isLC_runtime (hwf.mono_lc τ hτmem))
                    hWnodup hXs.length hWXs,
                Ty.renameG_renameG (hwf.mono_lc τ hτmem) hwf.nodup
                  hWnodup hWlen hXlen hGW (hWfree τ hτmem) hWXs hGXs]
            have henv :
                (RecSpecs.rhsCtx { ctx with env := ctx.env.substFvar Z U }
                    specs' W Xs).env =
                  (RecSpecs.rhsCtx ctx specs G Xs).env.substFvar Z U := by
              unfold RecSpecs.rhsCtx specs' substSpecs
              rw [Env.substFvar_append]
              simp only [Env.substFvar, List.map_map]
              congr 1
              apply List.map_congr_left
              intro spec hspec
              cases spec with
              | poly scheme => rfl
              | mono original =>
                  have horig : RecSpec.mono original ∈ specs := hspec
                  have horigKey :
                      Ty.renameG W Xs
                          (Ty.substFvar Z U (Ty.renameG G W original)) =
                        Ty.substFvar Z U (Ty.renameG G Xs original) := by
                    rw [Ty.renameG_substFvar_comm hU hZW hUW hZXs
                          (Ty.renameG_isLC_runtime
                            (hwf.mono_lc original horig))
                          hWnodup hXs.length hWXs,
                      Ty.renameG_renameG (hwf.mono_lc original horig)
                        hwf.nodup hWnodup hWlen hXlen hGW
                        (hWfree original horig) hWXs hGXs]
                  simp only [Function.comp_apply, RecSpec.substFreshened,
                    RecSpec.rhsEntry, PolyTy.substFvar, PolyTy.mkTrivial]
                  rw [horigKey]
            rw [hkey]
            have ht := ihmono Xs hXs0 (rhs0, .mono τ) hold τ rfl
            have hctx :
                RecSpecs.rhsCtx { ctx with env := ctx.env.substFvar Z U }
                    specs' W Xs =
                  { RecSpecs.rhsCtx ctx specs G Xs with
                    env := (RecSpecs.rhsCtx ctx specs G Xs).env.substFvar Z U } := by
              cases ctx
              simp only [RecSpecs.rhsCtx] at henv ⊢
              rw [henv]
            rw [hctx]
            exact ht
      · intro Xs hXs pair hpair scheme' hscheme' Ys hYs
        have hXlen : Xs.length = G.length := hXs.length.trans hWlen
        have hZXs : Z ∉ Xs := fun hc =>
          hXs.avoid Z hc (by simp [avoid'])
        have hGXs : ∀ g ∈ G, g ∉ Xs := fun g hg hc =>
          hXs.avoid g hc (by simp [avoid', List.mem_append, hg])
        have hWXs : ∀ w ∈ W, w ∉ Xs := fun w hw hc =>
          hXs.avoid w hc (by simp [avoid', List.mem_append, hw])
        have hXs0 : FreshNames avoid G.length Xs := by
          refine ⟨hXlen, hXs.nodup, ?_⟩
          intro x hx ha
          exact hXs.avoid x hx (by simp [avoid', List.mem_append, ha])
        obtain ⟨rhs0, spec0, hold, rfl⟩ := mem_zip_map_right_runtime hpair
        cases spec0 with
        | mono τ => exact RecSpec.noConfusion hscheme'
        | poly scheme =>
            simp only [RecSpec.substFreshened, RecSpec.poly.injEq] at hscheme'
            subst scheme'
            have hYs0 : FreshNames (avoid ++ Xs) scheme.paramCount Ys := by
              refine ⟨by simpa [PolyTy.substFvar] using hYs.length,
                hYs.nodup, ?_⟩
              intro y hy hmem
              apply hYs.avoid y hy
              simp only [avoid', List.append_assoc, List.mem_append,
                List.mem_cons]
              simp only [List.mem_append] at hmem ⊢
              tauto
            have hZYs : Z ∉ Ys := fun hc =>
              hYs.avoid Z hc (by simp [avoid', List.mem_append])
            have henv :
                (RecSpecs.rhsCtx { ctx with env := ctx.env.substFvar Z U }
                    specs' W Xs).env =
                  (RecSpecs.rhsCtx ctx specs G Xs).env.substFvar Z U := by
              unfold RecSpecs.rhsCtx specs' substSpecs
              rw [Env.substFvar_append]
              simp only [Env.substFvar, List.map_map]
              congr 1
              apply List.map_congr_left
              intro spec hspec
              cases spec with
              | poly original => rfl
              | mono original =>
                  have horig : RecSpec.mono original ∈ specs := hspec
                  have horigKey :
                      Ty.renameG W Xs
                          (Ty.substFvar Z U (Ty.renameG G W original)) =
                        Ty.substFvar Z U (Ty.renameG G Xs original) := by
                    rw [Ty.renameG_substFvar_comm hU hZW hUW hZXs
                          (Ty.renameG_isLC_runtime
                            (hwf.mono_lc original horig))
                          hWnodup hXs.length hWXs,
                      Ty.renameG_renameG (hwf.mono_lc original horig)
                        hwf.nodup hWnodup hWlen hXlen hGW
                        (hWfree original horig) hWXs hGXs]
                  simp only [Function.comp_apply, RecSpec.substFreshened,
                    RecSpec.rhsEntry, PolyTy.substFvar,
                    PolyTy.mkTrivial]
                  rw [horigKey]
            rw [show (scheme.substFvar Z U).openVars Ys =
                Ty.substFvar Z U (scheme.openVars Ys) by
                  unfold PolyTy.openVars PolyTy.substFvar
                  exact (Ty.substFvar_openVars hU hZYs).symm]
            have ht := ihpoly Xs hXs0 (rhs0, .poly scheme) hold scheme rfl
              Ys hYs0
            have hctx :
                RecSpecs.rhsCtx { ctx with env := ctx.env.substFvar Z U }
                    specs' W Xs =
                  { RecSpecs.rhsCtx ctx specs G Xs with
                    env := (RecSpecs.rhsCtx ctx specs G Xs).env.substFvar Z U } := by
              cases ctx
              simp only [RecSpecs.rhsCtx] at henv ⊢
              rw [henv]
            rw [hctx]
            exact ht
      · have henv :
            (RecSpecs.bodyCtx { ctx with env := ctx.env.substFvar Z U }
                specs' W).env =
              (RecSpecs.bodyCtx ctx specs G).env.substFvar Z U := by
          unfold RecSpecs.bodyCtx specs' substSpecs
          rw [Env.substFvar_append]
          simp only [Env.substFvar, List.map_map]
          congr 1
          apply List.map_congr_left
          intro spec hspec
          cases spec with
          | poly scheme => rfl
          | mono τ =>
              have hτ : RecSpec.mono τ ∈ specs := hspec
              have hrename := PolyTy.genGroup_renameG
                (hwf.mono_lc τ hτ) hWlen hwf.nodup hWnodup hGW
                (hWfree τ hτ)
              have hsubst := PolyTy.genGroup_substFvar
                (Z := Z) (U := U) (G := W) (τ := Ty.renameG G W τ) hZW hUW
              simp only [Function.comp_apply, RecSpec.substFreshened,
                RecSpec.bodyScheme]
              rw [← hsubst, ← hrename]
        have hctx :
            RecSpecs.bodyCtx { ctx with env := ctx.env.substFvar Z U }
                specs' W =
              { RecSpecs.bodyCtx ctx specs G with
                env := (RecSpecs.bodyCtx ctx specs G).env.substFvar Z U } := by
          cases ctx
          simp only [RecSpecs.bodyCtx] at henv ⊢
          rw [henv]
        rw [hctx]
        exact ihbody
  | mk hspec _ ihbody =>
      expose_names
      have hcontents : ctor.contents.map (Ty.substFvar Z U) = ctor.contents := by
        calc
          ctor.contents.map (Ty.substFvar Z U) = ctor.contents.map id := by
            apply List.map_congr_left
            intro field hfield
            exact Ty.substFvar_fresh
              ((ctor.closed field hfield).not_mem_freeVars Z)
          _ = ctor.contents := by simp only [List.map_id]
      have hfields := InstantiatesBy.forall2_substFvar
        (Z := Z) (U := U) hU hspec.fields
      rw [hcontents] at hfields
      rw [Env.substFvar_append, Env.substFvar_map_mkTrivial] at ihbody
      have hspec' : BranchCtorSpec ctx_1.ctors c n
          (Ty.substFvar Z U scrutTy) ctor
          (tyArgs.map (Ty.substFvar Z U))
          (instContents.map (Ty.substFvar Z U)) :=
        ⟨hspec.lookup, by
          rw [hspec.scrut_eq]
          simp [Ty.substFvar, TyList.substFvar_eq_map],
          by simpa using hspec.arity,
          hspec.bind_count, hfields⟩
      exact RunWTMatchBranch.mk
        (ctx := { ctx_1 with env := ctx_1.env.substFvar Z U })
        hspec' (by simpa only using ihbody)
  | wildcard _ ihbody => exact .wildcard ihbody


/-! ## Recursive rewrapping and scheme inhabitants

The operational `letRecUnfold` step substitutes each recursively wrapped
member for the corresponding body variable.  The wrapper is an ordinary
erased `letRec`: its typing derivation remembers the mixed recursive specs,
but its `Expr` contains only `none` annotations.

At a fixed opening `G ↦ Xs` of the ordinary HM members' shared pool, we can
freeze that opening into the monomorphic specs and re-derive the group with an
empty pool.  This turns an RHS typing premise into a typing for the recursively
wrapped member without adding any runtime type construct.
-/

private theorem PolyTy.genGroup_nil_runtime {ty : Ty} :
    PolyTy.genGroup [] ty = PolyTy.mkTrivial ty := by
  have hclose : Ty.closeOver [] ty = ty :=
    Ty.closeOver_eq_self_of_fresh (by simp)
  simp [PolyTy.genGroup, Ty.genFilter, hclose, PolyTy.mkTrivial]

private theorem map_rhsEntry_openAt_runtime (G Xs Zs : List Nat)
    (specs : List RecSpec) :
    (specs.map (RecSpec.openAt G Xs)).map (RecSpec.rhsEntry [] Zs) =
      specs.map (RecSpec.rhsEntry G Xs) := by
  rw [List.map_map]
  apply List.map_congr_left
  intro spec _
  cases spec with
  | mono ty => rfl
  | poly scheme => rfl

private theorem map_bodyScheme_openAt_runtime (G Xs : List Nat)
    (specs : List RecSpec) :
    (specs.map (RecSpec.openAt G Xs)).map (RecSpec.bodyScheme []) =
      specs.map (RecSpec.rhsEntry G Xs) := by
  rw [List.map_map]
  apply List.map_congr_left
  intro spec _
  cases spec with
  | mono ty => exact PolyTy.genGroup_nil_runtime
  | poly scheme => rfl

private theorem specs_wf_openAt_runtime {bindings : List Expr}
    {specs : List RecSpec} {G Xs : List Nat}
    (hwf : RecSpecsWF bindings specs G) :
    RecSpecsWF bindings (specs.map (RecSpec.openAt G Xs)) [] := by
  refine ⟨by simpa using hwf.length, by simp, ?_, ?_⟩
  · intro ty hty
    obtain ⟨spec, hspec, heq⟩ := List.mem_map.mp hty
    cases spec with
    | mono original =>
        simp only [RecSpec.openAt, RecSpec.mono.injEq] at heq
        subst ty
        exact Ty.renameG_isLC_runtime (hwf.mono_lc original hspec)
    | poly scheme => exact RecSpec.noConfusion heq
  · intro scheme hscheme
    obtain ⟨spec, hspec, heq⟩ := List.mem_map.mp hscheme
    cases spec with
    | mono ty => exact RecSpec.noConfusion heq
    | poly original =>
        simp only [RecSpec.openAt, RecSpec.poly.injEq] at heq
        subst scheme
        exact hwf.poly_wf original hspec

/-- Re-wrap one recursive member at a fixed shared-pool opening. -/
theorem RunWT.rec_rewrap_at {ctx : Ctx} {bindings : List Expr}
    {specs : List RecSpec} {G avoid Xs : List Nat}
    (hwf : RecSpecsWF bindings specs G)
    (hmono : MonoTyped RunWT ctx bindings specs G avoid)
    (hpoly : PolyTyped RunWT ctx bindings specs G avoid)
    (hXs : FreshNames avoid G.length Xs)
    {rhs : Expr} {ty : Ty}
    (hrhs : RunWT (RecSpecs.rhsCtx ctx specs G Xs) rhs ty) :
    RunWT ctx (.letRec (bindings.map (fun _ => none)) bindings rhs) ty := by
  let openedSpecs := specs.map (RecSpec.openAt G Xs)
  apply RunWT.letRec (specs := openedSpecs) (G := [])
    (avoid := avoid ++ Xs)
  · exact specs_wf_openAt_runtime hwf
  · intro Zs hZs pair hpair openedTy hopened
    have hZsNil : Zs = [] := List.length_eq_zero_iff.mp hZs.length
    subst Zs
    obtain ⟨rhs0, spec0, hold, rfl⟩ := mem_zip_map_right_runtime hpair
    cases spec0 with
    | mono original =>
        simp only [RecSpec.openAt, RecSpec.mono.injEq] at hopened
        subst openedTy
        have ht := hmono Xs hXs (rhs0, .mono original) hold original rfl
        have hctx :
            RecSpecs.rhsCtx ctx openedSpecs [] [] =
              RecSpecs.rhsCtx ctx specs G Xs := by
          unfold RecSpecs.rhsCtx openedSpecs
          rw [map_rhsEntry_openAt_runtime]
        rw [hctx]
        simpa [Ty.renameG] using ht
    | poly scheme => exact RecSpec.noConfusion hopened
  · intro Zs hZs pair hpair scheme hopened Ys hYs
    have hZsNil : Zs = [] := List.length_eq_zero_iff.mp hZs.length
    subst Zs
    obtain ⟨rhs0, spec0, hold, rfl⟩ := mem_zip_map_right_runtime hpair
    cases spec0 with
    | mono original => exact RecSpec.noConfusion hopened
    | poly original =>
        simp only [RecSpec.openAt, RecSpec.poly.injEq] at hopened
        subst scheme
        have hYs' : FreshNames (avoid ++ Xs) original.paramCount Ys := by
          simpa using hYs
        have ht := hpoly Xs hXs (rhs0, .poly original) hold original rfl Ys hYs'
        have hctx :
            RecSpecs.rhsCtx ctx openedSpecs [] [] =
              RecSpecs.rhsCtx ctx specs G Xs := by
          unfold RecSpecs.rhsCtx openedSpecs
          rw [map_rhsEntry_openAt_runtime]
        rw [hctx]
        exact ht
  · rw [show RecSpecs.bodyCtx ctx openedSpecs [] =
        RecSpecs.rhsCtx ctx specs G Xs by
      unfold RecSpecs.bodyCtx RecSpecs.rhsCtx openedSpecs
      rw [map_bodyScheme_openAt_runtime]]
    exact hrhs

/-- An erased value inhabits a scheme when it has every locally-closed
`InstantiatesBy` instance accepted by the production variable rule. -/
def RunHasScheme (ctx : Ctx) (value : Expr) (scheme : PolyTy) : Prop :=
  ∀ args ty, (∀ arg ∈ args, arg.IsLC) →
    scheme.InstantiatesTo args ty → RunWT ctx value ty


/-! ### From cofinite openings to production scheme instances

The production variable rule intentionally does not require its witness list
to have exactly the scheme arity: unused quantifiers may be omitted and extra
arguments are harmless.  For the cofinite proof we canonicalize that witness
to exactly `paramCount` entries, padding omitted unused entries with `Unit`.
-/

private def exactInstArgs (n : Nat) (args : List Ty) : List Ty :=
  (List.range n).map (fun i => (args[i]?).getD (.prim .unit))

private theorem exactInstArgs_areLC {n : Nat} {args : List Ty}
    (hlc : ∀ arg ∈ args, arg.IsLC) : Ty.AreLC n (exactInstArgs n args) := by
  constructor
  · simp [exactInstArgs]
  · intro arg harg
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp harg
    cases hget : args[i]? with
    | none => exact ContainsBvarsUpTo.prim
    | some actual =>
        simp only [Option.getD_some]
        exact hlc actual (List.mem_of_getElem? hget)

private theorem exactInstArgs_realise {scheme : PolyTy} {args : List Ty}
    {ty : Ty} (hwf : scheme.WF)
    (hinst : scheme.InstantiatesTo args ty) :
    ty = scheme.openWith (exactInstArgs scheme.paramCount args) := by
  unfold PolyTy.InstantiatesTo at hinst
  have h := InstantiatesBy.eq_openWith_range hinst hwf
  simpa [exactInstArgs, PolyTy.openWith] using h

private def substFvarsEnvRuntime : List (Nat × Ty) → Env → Env
  | [], env => env
  | (name, replacement) :: rest, env =>
      substFvarsEnvRuntime rest (env.substFvar name replacement)

private theorem RunWT.substFvars {ctx : Ctx} {e : Expr} {ty : Ty}
    {pairs : List (Nat × Ty)}
    (hlc : ∀ pair ∈ pairs, pair.2.IsLC) (h : RunWT ctx e ty) :
    RunWT { ctx with env := substFvarsEnvRuntime pairs ctx.env }
      e (Ty.substFvars pairs ty) := by
  induction pairs generalizing ctx ty with
  | nil => simpa [substFvarsEnvRuntime, Ty.substFvars] using h
  | cons pair rest ih =>
      obtain ⟨name, replacement⟩ := pair
      simp only [substFvarsEnvRuntime, Ty.substFvars]
      exact ih (fun pair hpair => hlc pair (List.mem_cons_of_mem _ hpair))
        (h.substFvar (hlc (name, replacement) List.mem_cons_self))

private theorem substFvarsEnvRuntime_eq_self_of_fresh
    {pairs : List (Nat × Ty)} {env : Env}
    (hfresh : ∀ pair ∈ pairs, pair.1 ∉ env.freeVars) :
    substFvarsEnvRuntime pairs env = env := by
  induction pairs generalizing env with
  | nil => rfl
  | cons pair rest ih =>
      obtain ⟨name, replacement⟩ := pair
      simp only [substFvarsEnvRuntime]
      rw [Env.substFvar_fresh (hfresh (name, replacement) List.mem_cons_self)]
      exact ih (fun pair hpair => hfresh pair (List.mem_cons_of_mem _ hpair))

private theorem pairs_zip_values_lc_runtime {names : List Nat} {args : List Ty}
    (hlc : ∀ arg ∈ args, arg.IsLC) :
    ∀ pair ∈ names.zip args, pair.2.IsLC := by
  intro pair hpair
  exact hlc pair.2 (List.of_mem_zip hpair).2

private theorem pairs_zip_names_fresh_runtime {names : List Nat}
    {args : List Ty} {env : Env}
    (hfresh : ∀ name ∈ names, name ∉ env.freeVars) :
    ∀ pair ∈ names.zip args, pair.1 ∉ env.freeVars := by
  intro pair hpair
  exact hfresh pair.1 (List.of_mem_zip hpair).1

/-- Replace one fresh rigid opening by an exact concrete scheme instance.
The erased runtime expression itself is unchanged. -/
private theorem RunWT.instantiate_opening {ctx : Ctx} {e : Expr}
    {scheme : PolyTy} {names : List Nat} {args : List Ty}
    (hargs : Ty.AreLC scheme.paramCount args)
    (hnamesLen : names.length = scheme.paramCount)
    (hnamesNodup : names.Nodup)
    (hnamesEnv : ∀ x ∈ names, x ∉ ctx.env.freeVars)
    (hnamesBody : ∀ x ∈ names, x ∉ scheme.body.freeVars)
    (hnamesArgs : ∀ x ∈ names, x ∉ Ty.freeVarsList args)
    (htyped : RunWT ctx e (scheme.openVars names)) :
    RunWT ctx e (scheme.openWith args) := by
  have hsub := RunWT.substFvars (pairs := names.zip args)
    (pairs_zip_values_lc_runtime (names := names) hargs.2) htyped
  rw [substFvarsEnvRuntime_eq_self_of_fresh
    (pairs_zip_names_fresh_runtime hnamesEnv)] at hsub
  have hopen := Ty.openWith_eq_substFvars_openVars
    (ty := scheme.body) (Vs := args) (Xs := names)
    ⟨hargs.1.trans hnamesLen.symm, hargs.2⟩
    hnamesNodup hnamesBody hnamesArgs
  simpa [PolyTy.openVars, PolyTy.openWith, hopen] using hsub

/-- A completely annotated recursive member retains its declared scheme when
the erased group is wrapped around it. -/
theorem RunHasScheme.ofPolyRecMember {ctx : Ctx}
    {bindings : List Expr} {specs : List RecSpec} {G avoid : List Nat}
    (hwf : RecSpecsWF bindings specs G)
    (hmono : MonoTyped RunWT ctx bindings specs G avoid)
    (hpoly : PolyTyped RunWT ctx bindings specs G avoid)
    {rhs : Expr} {scheme : PolyTy}
    (hmember : (rhs, .poly scheme) ∈ bindings.zip specs) :
    RunHasScheme ctx
      (.letRec (bindings.map (fun _ => none)) bindings rhs) scheme := by
  intro args ty hlc hinst
  let exactArgs := exactInstArgs scheme.paramCount args
  have hargs : Ty.AreLC scheme.paramCount exactArgs :=
    exactInstArgs_areLC hlc
  have hschemeWf : scheme.WF := hwf.poly_wf scheme (List.of_mem_zip hmember).2
  have hrealise := exactInstArgs_realise hschemeWf hinst
  rw [hrealise]
  obtain ⟨Xs, hXsLen, hXsNodup, hXsAvoid⟩ :=
    exists_fresh_names avoid G.length
  have hXs : FreshNames avoid G.length Xs :=
    ⟨hXsLen, hXsNodup, hXsAvoid⟩
  obtain ⟨Ys, hYsLen, hYsNodup, hYsAvoid⟩ :=
    exists_fresh_names
      (avoid ++ Xs ++ ctx.env.freeVars ++ scheme.body.freeVars ++
        Ty.freeVarsList exactArgs)
      scheme.paramCount
  have hYs : FreshNames (avoid ++ Xs) scheme.paramCount Ys :=
    ⟨hYsLen, hYsNodup, fun y hy hmem => hYsAvoid y hy (by
      simp only [List.mem_append]
      rcases List.mem_append.mp hmem with ha | hx
      · exact Or.inl (Or.inl (Or.inl (Or.inl ha)))
      · exact Or.inl (Or.inl (Or.inl (Or.inr hx))))⟩
  have htyped := hpoly Xs hXs (rhs, .poly scheme) hmember scheme rfl Ys hYs
  have hwrapped := RunWT.rec_rewrap_at hwf hmono hpoly hXs htyped
  apply RunWT.instantiate_opening hargs hYsLen hYsNodup
    (htyped := hwrapped)
  · intro y hy hmem
    exact hYsAvoid y hy (by simp [List.mem_append, hmem])
  · intro y hy hmem
    exact hYsAvoid y hy (by simp [List.mem_append, hmem])
  · intro y hy hmem
    exact hYsAvoid y hy (by simp [List.mem_append, hmem])

/-- An ordinary recursive member becomes polymorphic only at the HM scheme
obtained by generalising its shared monotype after leaving the group. -/
theorem RunHasScheme.ofMonoRecMember {ctx : Ctx}
    {bindings : List Expr} {specs : List RecSpec} {G avoid : List Nat}
    (hwf : RecSpecsWF bindings specs G)
    (hmono : MonoTyped RunWT ctx bindings specs G avoid)
    (hpoly : PolyTyped RunWT ctx bindings specs G avoid)
    {rhs : Expr} {ty : Ty}
    (hmember : (rhs, .mono ty) ∈ bindings.zip specs) :
    RunHasScheme ctx
      (.letRec (bindings.map (fun _ => none)) bindings rhs)
      (PolyTy.genGroup G ty) := by
  intro args result hlc hinst
  let scheme := PolyTy.genGroup G ty
  let exactArgs := exactInstArgs scheme.paramCount args
  have hargs : Ty.AreLC scheme.paramCount exactArgs :=
    exactInstArgs_areLC hlc
  have htyLC : ty.IsLC := hwf.mono_lc ty (List.of_mem_zip hmember).2
  have hschemeWf : scheme.WF := PolyTy.genGroup_wf htyLC
  have hrealise := exactInstArgs_realise hschemeWf hinst
  rw [hrealise]
  obtain ⟨Xs, hXsLen, hXsNodup, hXsAvoid⟩ :=
    exists_fresh_names
      (avoid ++ G ++ ty.freeVars ++ ctx.env.freeVars ++ Ty.freeVarsList exactArgs ++
        scheme.body.freeVars)
      G.length
  have hXs : FreshNames avoid G.length Xs :=
    ⟨hXsLen, hXsNodup, fun x hx hmem =>
      hXsAvoid x hx (by simp [List.mem_append, hmem])⟩
  have hdisj : ∀ g ∈ G, g ∉ Xs := fun g hg hc =>
    hXsAvoid g hc (by simp [List.mem_append, hg])
  have hXsTy : ∀ x ∈ Xs, x ∉ ty.freeVars := fun x hx hc =>
    hXsAvoid x hx (by simp [List.mem_append, hc])
  have hXsEnv : ∀ x ∈ Xs, x ∉ ctx.env.freeVars := fun x hx hc =>
    hXsAvoid x hx (by simp [List.mem_append, hc])
  have hXsArgs : ∀ x ∈ Xs, x ∉ Ty.freeVarsList exactArgs := fun x hx hc =>
    hXsAvoid x hx (by simp [List.mem_append, hc])
  have hXsBody : ∀ x ∈ Xs, x ∉ scheme.body.freeVars := fun x hx hc =>
    hXsAvoid x hx (by simp [List.mem_append, hc])
  have htyped := hmono Xs hXs (rhs, .mono ty) hmember ty rfl
  have hwrapped : RunWT ctx
      (.letRec (bindings.map (fun _ => none)) bindings rhs)
      (Ty.renameG G Xs ty) :=
    RunWT.rec_rewrap_at hwf hmono hpoly hXs htyped
  set Xs' := Ty.genFilter Xs (Ty.renameG G Xs ty) with hXsDef
  have hXsLen' : Xs'.length = (Ty.genFilter G ty).length := by
    have h := congrArg PolyTy.paramCount
      (PolyTy.genGroup_renameG htyLC hXsLen hwf.nodup hXsNodup
        hdisj hXsTy)
    simp only [PolyTy.genGroup] at h
    rw [hXsDef]
    exact h.symm
  have hXsNodup' : Xs'.Nodup := by
    rw [hXsDef]
    unfold Ty.genFilter
    exact hXsNodup.filter _
  have hGNodup : (Ty.genFilter G ty).Nodup := by
    unfold Ty.genFilter
    exact hwf.nodup.filter _
  have hGDisj : ∀ g ∈ Ty.genFilter G ty, g ∉ Xs' := by
    intro g hg hc
    exact hdisj g (Ty.mem_of_mem_genFilter hg) (by
      rw [hXsDef] at hc
      exact Ty.mem_of_mem_genFilter hc)
  have hrewrite : Ty.renameG G Xs ty =
      Ty.openVars Xs' (Ty.closeOver (Ty.genFilter G ty) ty) := by
    rw [Ty.renameG_eq_genFilter hXsLen hwf.nodup hXsNodup hdisj hXsTy]
    exact (Ty.openVars_closeOver_rename htyLC hGNodup hXsLen' hGDisj).symm
  rw [hrewrite] at hwrapped
  apply RunWT.instantiate_opening hargs
    (scheme := scheme) (names := Xs')
    (by simpa [scheme, PolyTy.genGroup] using hXsLen') hXsNodup'
    (htyped := by simpa [scheme, PolyTy.genGroup, PolyTy.openVars] using hwrapped)
  · intro x hx
    apply hXsEnv x
    rw [hXsDef] at hx
    exact Ty.mem_of_mem_genFilter hx
  · intro x hx
    apply hXsBody x
    rw [hXsDef] at hx
    exact Ty.mem_of_mem_genFilter hx
  · intro x hx
    apply hXsArgs x
    rw [hXsDef] at hx
    exact Ty.mem_of_mem_genFilter hx

/-- Runtime typing produces a locally closed result type. -/
theorem RunWT.regular {ctx : Ctx} {e : Expr} {ty : Ty}
    (h : RunWT ctx e ty) : ty.IsLC := by
  induction h using RunWT.rec
    (motive_2 := fun _ _ _ resultTy _ => resultTy.IsLC) with
  | primLitUnit => exact .prim
  | primLitInt => exact .prim
  | primLitNat => exact .prim
  | primLitChar => exact .prim
  | primBinOpIntAdd => exact .arrow .prim (.arrow .prim .prim)
  | primBinOpIntSub => exact .arrow .prim (.arrow .prim .prim)
  | primBinOpIntLt _ _ _ _ => exact .arrow .prim (.arrow .prim (.customTy (by simp)))
  | primBinOpCharLt _ _ _ _ => exact .arrow .prim (.arrow .prim (.customTy (by simp)))
  | lambda hparam _ ihbody => exact .arrow hparam ihbody
  | app _ _ ihfn _ =>
      cases ihfn with
      | arrow _ hresult => exact hresult
  | letIn _ _ _ _ ihbody => exact ihbody
  | var _ hlc hinst => exact InstantiatesBy.preserves_bvars hlc hinst
  | ctor _ hlc hinst => exact InstantiatesBy.preserves_bvars hlc hinst
  | match_ _ hne _ _ ihbranches =>
      obtain ⟨hd, tl, rfl⟩ := List.exists_cons_of_ne_nil hne
      exact ihbranches hd (List.mem_cons_self ..)
  | letRec _ _ _ _ _ _ ihbody => exact ihbody
  | mk _ _ ihbody => exact ihbody
  | wildcard _ ihbody => exact ihbody

/-- A term typed at a monotype inhabits its trivial scheme. -/
theorem RunHasScheme.ofTrivial {ctx : Ctx} {value : Expr} {ty : Ty}
    (h : RunWT ctx value ty) :
    RunHasScheme ctx value (PolyTy.mkTrivial ty) := by
  intro args result _ hinst
  have heq := InstantiatesBy.eq_openWith_range hinst h.regular
  have hresult : result = ty := by
    simpa [PolyTy.mkTrivial, Ty.openWith_nil] using heq
  rw [hresult]
  exact h

/-- A cofinally checked let-bound expression inhabits every production
`InstantiatesBy` instance of its generalized scheme. -/
theorem RunHasScheme.ofGeneralisesTo {ctx : Ctx} {rhs : Expr}
    {scheme : PolyTy} {avoid : List Nat}
    (hwf : scheme.WF)
    (hgen : GeneralisesTo RunWT ctx rhs scheme avoid) :
    RunHasScheme ctx rhs scheme := by
  intro args ty hlc hinst
  let exactArgs := exactInstArgs scheme.paramCount args
  have hargs : Ty.AreLC scheme.paramCount exactArgs :=
    exactInstArgs_areLC hlc
  have hrealise := exactInstArgs_realise hwf hinst
  rw [hrealise]
  obtain ⟨Xs, hXsLen, hXsNodup, hXsAvoid⟩ :=
    exists_fresh_names
      (avoid ++ ctx.env.freeVars ++ scheme.body.freeVars ++
        Ty.freeVarsList exactArgs)
      scheme.paramCount
  have hXs : FreshNames avoid scheme.paramCount Xs :=
    ⟨hXsLen, hXsNodup, fun x hx hmem =>
      hXsAvoid x hx (by simp [List.mem_append, hmem])⟩
  apply RunWT.instantiate_opening hargs hXsLen hXsNodup
    (htyped := hgen Xs hXs)
  · intro x hx hmem
    exact hXsAvoid x hx (by simp [List.mem_append, hmem])
  · intro x hx hmem
    exact hXsAvoid x hx (by simp [List.mem_append, hmem])
  · intro x hx hmem
    exact hXsAvoid x hx (by simp [List.mem_append, hmem])

/-! ### Constructor-spine inversion for match reduction -/

private theorem List.Forall₂.snoc_runtime {α β : Type _} {R : α → β → Prop}
    {left : List α} {right : List β} {a : α} {b : β}
    (h : List.Forall₂ R left right) (hab : R a b) :
    List.Forall₂ R (left ++ [a]) (right ++ [b]) := by
  induction h with
  | nil => exact .cons hab .nil
  | cons hhd _ ih => exact .cons hhd ih

/-- Invert typing directly along the constructor spine supplied by the
operational match rule. No separate canonical-forms detour is required. -/
theorem RunWT.ctor_applied_inversion {ctx : Ctx} {e : Expr}
    {name : CtorName} {args : List Expr} {ty : Ty}
    (hcat : SmallStep.CtorAppliedTo e name args)
    (htyped : RunWT ctx e ty) :
    ∃ (ctor : Ctor) (tyArgs consumed remaining : List Ty),
      LookupList.get? ctx.ctors name = some ctor ∧
      (∀ arg ∈ tyArgs, arg.IsLC) ∧
      ctor.contents = consumed ++ remaining ∧
      List.Forall₂
        (fun value field =>
          ∃ fieldTy, InstantiatesBy tyArgs field fieldTy ∧
            RunWT ctx value fieldTy)
        args consumed ∧
      InstantiatesBy tyArgs
        (Ty.wrapArrows
          (.customTy ctor.tyName (Ty.bvarRange ctor.paramCount)) remaining)
        ty := by
  induction hcat generalizing ty with
  | base name =>
      cases htyped with
      | ctor hlook htyargs hinst =>
          exact ⟨_, _, [], _, hlook, htyargs, rfl, .nil,
            by simpa [Ctor.toTy] using hinst⟩
  | step hcat ih =>
      cases htyped with
      | app hf harg =>
          obtain ⟨ctor, tyArgs, consumed, remaining, hlook, htyargs,
            hcontents, hforall, hinst_f⟩ := ih hf
          cases remaining with
          | nil =>
              simp only [Ty.wrapArrows] at hinst_f
              cases hinst_f
          | cons field rest =>
              simp only [Ty.wrapArrows] at hinst_f
              cases hinst_f with
              | arrow hfield hrest =>
                  refine ⟨ctor, tyArgs, consumed ++ [field], rest,
                    hlook, htyargs, ?_, List.Forall₂.snoc_runtime hforall
                      ⟨_, hfield, harg⟩,
                    hrest⟩
                  rw [hcontents]
                  exact (List.append_assoc consumed [field] rest).symm

/-- Align constructor-field instances from the branch typing and the runtime
constructor spine, producing the scheme inhabitants consumed by `substMany`. -/
private theorem InstantiatesBy.build_run_match_values
    {ctx : Ctx} {n : Nat} {tyArgs tyArgsSpine : List Ty}
    (hagree : ∀ k, k < n → tyArgs[k]? = tyArgsSpine[k]?) :
    ∀ {contents instContents : List Ty} {args : List Expr},
      (∀ field ∈ contents, ContainsBvarsUpTo n field) →
      List.Forall₂ (InstantiatesBy tyArgs) contents instContents →
      List.Forall₂
        (fun value field =>
          ∃ fieldTy, InstantiatesBy tyArgsSpine field fieldTy ∧
            RunWT ctx value fieldTy)
        args contents →
      List.Forall₂ (RunHasScheme ctx)
        args (instContents.map PolyTy.mkTrivial) := by
  intro contents
  induction contents with
  | nil =>
      intro instContents args _ hinst hfor
      cases hinst
      cases hfor
      exact .nil
  | cons field rest ih =>
      intro instContents args hbound hinst hfor
      cases hinst with
      | cons hinstField hinstRest =>
          cases hfor with
          | cons hforField hforRest =>
              obtain ⟨fieldTy, hspine, hvalue⟩ := hforField
              have heq := InstantiatesBy.det_agree hagree
                (hbound field List.mem_cons_self) hinstField hspine
              refine List.Forall₂.cons ?_
                (ih (fun ty hty => hbound ty (List.mem_cons_of_mem _ hty))
                  hinstRest hforRest)
              rw [heq]
              exact RunHasScheme.ofTrivial hvalue

private theorem RunHasScheme.ofRecMember {ctx : Ctx}
    {bindings : List Expr} {specs : List RecSpec} {G avoid : List Nat}
    (hwf : RecSpecsWF bindings specs G)
    (hmono : MonoTyped RunWT ctx bindings specs G avoid)
    (hpoly : PolyTyped RunWT ctx bindings specs G avoid)
    {rhs : Expr} {spec : RecSpec}
    (hmember : (rhs, spec) ∈ bindings.zip specs) :
    RunHasScheme ctx
      (.letRec (bindings.map (fun _ => none)) bindings rhs)
      (spec.bodyScheme G) := by
  cases spec with
  | mono ty =>
      simpa [RecSpec.bodyScheme] using
        RunHasScheme.ofMonoRecMember hwf hmono hpoly hmember
  | poly scheme =>
      simpa [RecSpec.bodyScheme] using
        RunHasScheme.ofPolyRecMember hwf hmono hpoly hmember

/-- Every recursively wrapped RHS inhabits the scheme exported for its slot.
This is exactly the replacement list used by `Step.letRecUnfold`. -/
private theorem recursiveValuesHaveSchemes {ctx : Ctx}
    {bindings : List Expr} {specs : List RecSpec} {G avoid : List Nat}
    (hwf : RecSpecsWF bindings specs G)
    (hmono : MonoTyped RunWT ctx bindings specs G avoid)
    (hpoly : PolyTyped RunWT ctx bindings specs G avoid) :
    List.Forall₂ (RunHasScheme ctx)
      (bindings.map (fun rhs =>
        .letRec (bindings.map (fun _ => none)) bindings rhs))
      (specs.map (RecSpec.bodyScheme G)) := by
  have hall : ∀ pair ∈ bindings.zip specs,
      RunHasScheme ctx
        (.letRec (bindings.map (fun _ => none)) bindings pair.1)
        (pair.2.bodyScheme G) := by
    intro pair hpair
    exact RunHasScheme.ofRecMember hwf hmono hpoly hpair
  have go : ∀ (bs : List Expr) (ss : List RecSpec),
      bs.length = ss.length →
      (∀ pair ∈ bs.zip ss,
        RunHasScheme ctx
          (.letRec (bindings.map (fun _ => none)) bindings pair.1)
          (pair.2.bodyScheme G)) →
      List.Forall₂ (RunHasScheme ctx)
        (bs.map (fun rhs =>
          .letRec (bindings.map (fun _ => none)) bindings rhs))
        (ss.map (RecSpec.bodyScheme G)) := by
    intro bs
    induction bs with
    | nil =>
        intro ss hlen _
        cases ss with
        | nil => exact .nil
        | cons _ _ => simp at hlen
    | cons rhs rest ih =>
        intro ss hlen hmembers
        cases ss with
        | nil => simp at hlen
        | cons spec specs =>
            refine .cons ?_ ?_
            · exact hmembers (rhs, spec) (by simp)
            · apply ih specs (by simpa using hlen)
              intro pair hpair
              exact hmembers pair (by simp [hpair])
  exact go bindings specs hwf.length hall

/-! ### Term-environment transport

Operational substitution inserts erased values under binders.  The following
weakening theorem accounts for that insertion by shifting free de Bruijn
indices; types, schemes, and constructor declarations are unchanged.
-/

theorem RunWT.weakenEnv {ctors : CtorEnv} {envPre envExtra env : Env}
    {e : Expr} {ty : Ty}
    (h : RunWT ⟨envPre ++ env, ctors⟩ e ty) :
    RunWT ⟨envPre ++ envExtra ++ env, ctors⟩
      (e.shiftFrom envPre.length envExtra.length) ty := by
  suffices H : ∀ {ctx' : Ctx} {e' : Expr} {ty' : Ty}, RunWT ctx' e' ty' →
      ∀ pre : Env, ctx'.env = pre ++ env →
        RunWT ⟨pre ++ envExtra ++ env, ctx'.ctors⟩
          (e'.shiftFrom pre.length envExtra.length) ty' by
    exact H h envPre rfl
  intro ctx' e' ty' hd
  induction hd using RunWT.rec
    (motive_2 := fun ctx branch scrutTy resultTy _ =>
      ∀ pre : Env, ctx.env = pre ++ env →
        RunWTMatchBranch ⟨pre ++ envExtra ++ env, ctx.ctors⟩
          (branch.1, branch.2.shiftFrom (pre.length + branch.1.bindCount)
            envExtra.length) scrutTy resultTy) with
  | primLitUnit => intro _ _; exact .primLitUnit
  | primLitInt => intro _ _; exact .primLitInt
  | primLitNat => intro _ _; exact .primLitNat
  | primLitChar => intro _ _; exact .primLitChar
  | primBinOpIntAdd => intro _ _; exact .primBinOpIntAdd
  | primBinOpIntSub => intro _ _; exact .primBinOpIntSub
  | primBinOpIntLt _ _ ihtrue ihfalse =>
      intro pre hctx
      exact .primBinOpIntLt (ihtrue pre hctx) (ihfalse pre hctx)
  | primBinOpCharLt _ _ ihtrue ihfalse =>
      intro pre hctx
      exact .primBinOpCharLt (ihtrue pre hctx) (ihfalse pre hctx)
  | lambda hparam _ ihbody =>
      intro pre hctx
      expose_names
      simp only [Expr.shiftFrom]
      have hb := ihbody (PolyTy.mkTrivial paramTy :: pre) (by rw [hctx, List.cons_append])
      exact RunWT.lambda hparam (by
        simpa only [List.cons_append, List.length_cons] using hb)
  | app _ _ ihfn iharg =>
      intro pre hctx
      simp only [Expr.shiftFrom]
      exact .app (ihfn pre hctx) (iharg pre hctx)
  | letIn hwf hgen _ ihgen ihbody =>
      intro pre hctx
      expose_names
      simp only [Expr.shiftFrom]
      apply RunWT.letIn (scheme := scheme) (avoid := avoid) hwf
      · intro names hfresh
        exact ihgen names hfresh pre hctx
      · have hb := ihbody (scheme :: pre) (by rw [hctx, List.cons_append])
        simpa only [List.cons_append, List.length_cons] using hb
  | var hlookup hlc hinst =>
      intro pre hctx
      expose_names
      rw [hctx] at hlookup
      simp only [Expr.shiftFrom]
      by_cases hlt : index < pre.length
      · rw [if_pos hlt]
        refine .var ?_ hlc hinst
        rw [List.getElem?_append_left
          (by simp only [List.length_append]; omega : index < (pre ++ envExtra).length),
          List.getElem?_append_left hlt]
        rwa [List.getElem?_append_left hlt] at hlookup
      · rw [if_neg hlt]
        refine .var ?_ hlc hinst
        rw [List.getElem?_append_right
          (by simp only [List.length_append]; omega :
            (pre ++ envExtra).length ≤ index + envExtra.length)]
        rw [show index + envExtra.length - (pre ++ envExtra).length =
          index - pre.length by simp only [List.length_append]; omega]
        rwa [List.getElem?_append_right (by omega)] at hlookup
  | ctor hlookup hlc hinst =>
      intro _ _
      exact .ctor hlookup hlc hinst
  | match_ _ hne _ ihscrut ihbranches =>
      intro pre hctx
      simp only [Expr.shiftFrom]
      refine .match_ (ihscrut pre hctx) ?_ ?_
      · intro hnil
        obtain ⟨⟨p, b⟩, rest, hb⟩ := List.exists_cons_of_ne_nil hne
        have hm := BranchList.mem_shiftFrom_of_mem
          (threshold := pre.length) (n := envExtra.length)
          (hb ▸ List.mem_cons_self (a := (p, b)))
        rw [hnil] at hm
        exact List.not_mem_nil hm
      · intro branch' hm'
        obtain ⟨pat, body, hm, rfl⟩ := BranchList.mem_shiftFrom hm'
        exact ihbranches (pat, body) hm pre hctx
  | @letRec bindings ctx body resultTy specs G avoid hwf hmono hpoly _
      ihmono ihpoly ihbody =>
      intro pre hctx
      simp only [Expr.shiftFrom, RecGroup.shiftFrom_eq_map]
      have hwf' : RecSpecsWF
          (bindings.map
            (Expr.shiftFrom (pre.length + bindings.length) envExtra.length))
          specs G :=
        { hwf with length := by simpa using hwf.length }
      have hann :
          (bindings.map
            (Expr.shiftFrom (pre.length + bindings.length) envExtra.length)).map
              (fun _ => (none : Option PolyTy)) =
            bindings.map (fun _ => (none : Option PolyTy)) := by
        simp only [List.map_map, Function.comp_def]
      rw [← hann]
      apply RunWT.letRec (specs := specs) (G := G) (avoid := avoid) hwf'
      · intro Xs hXs pair hpair τ hτ
        rw [List.zip_map_left] at hpair
        obtain ⟨oldPair, holdPair, rfl⟩ := List.mem_map.mp hpair
        have ht := ihmono Xs hXs oldPair holdPair τ hτ
          (specs.map (RecSpec.rhsEntry G Xs) ++ pre) (by
            simp only [RecSpecs.rhsCtx, hctx, List.append_assoc])
        simp only [RecSpecs.rhsCtx, List.length_append, List.length_map] at ht
        rw [← hwf.length, Nat.add_comm bindings.length pre.length] at ht
        simpa only [RecSpecs.rhsCtx, List.append_assoc] using ht
      · intro Xs hXs pair hpair scheme hscheme Ys hYs
        rw [List.zip_map_left] at hpair
        obtain ⟨oldPair, holdPair, rfl⟩ := List.mem_map.mp hpair
        have ht := ihpoly Xs hXs oldPair holdPair scheme hscheme Ys hYs
          (specs.map (RecSpec.rhsEntry G Xs) ++ pre) (by
            simp only [RecSpecs.rhsCtx, hctx, List.append_assoc])
        simp only [RecSpecs.rhsCtx, List.length_append, List.length_map] at ht
        rw [← hwf.length, Nat.add_comm bindings.length pre.length] at ht
        simpa only [RecSpecs.rhsCtx, List.append_assoc] using ht
      · have hb := ihbody (specs.map (RecSpec.bodyScheme G) ++ pre) (by
          simp only [RecSpecs.bodyCtx, hctx, List.append_assoc])
        simp only [RecSpecs.bodyCtx, List.length_append, List.length_map] at hb
        rw [← hwf.length, Nat.add_comm bindings.length pre.length] at hb
        simpa only [RecSpecs.bodyCtx, List.append_assoc] using hb
  | mk hspec _ ihbody =>
      expose_names
      have hb := ihbody (instContents.map PolyTy.mkTrivial ++ pre) (by
        rw [h_2, List.append_assoc])
      simp only [List.length_append, List.length_map] at hb
      have hlen : instContents.length = n := by
        have := List.Forall₂.length_eq hspec.fields
        simpa [hspec.bind_count] using this.symm
      rw [hlen, Nat.add_comm n pre.length] at hb
      exact RunWTMatchBranch.mk hspec (by
        simpa only [List.append_assoc] using hb)
  | wildcard _ ihbody =>
      expose_names
      simpa only [MatchPattern.bindCount, Nat.add_zero] using
        (RunWTMatchBranch.wildcard (ihbody pre h_2))

/-- Simultaneous de Bruijn substitution preserves runtime typing when every
replacement inhabits the scheme stored in the environment segment it removes.
The replacement expressions remain entirely type-erased. -/
theorem RunWT.substMany {ctors : CtorEnv} {envPre env : Env}
    {schemes : List PolyTy} {values : List Expr} {e : Expr} {ty : Ty}
    (hvalues : List.Forall₂ (RunHasScheme ⟨env, ctors⟩) values schemes)
    (h : RunWT ⟨envPre ++ schemes ++ env, ctors⟩ e ty) :
    RunWT ⟨envPre ++ env, ctors⟩
      (e.substN envPre.length values) ty := by
  have hvaluesLen : values.length = schemes.length := hvalues.length_eq
  suffices H : ∀ {ctx' : Ctx} {e' : Expr} {ty' : Ty}, RunWT ctx' e' ty' →
      ∀ pre : Env, ctx'.env = pre ++ schemes ++ env → ctx'.ctors = ctors →
        RunWT ⟨pre ++ env, ctx'.ctors⟩ (e'.substN pre.length values) ty' by
    exact H h envPre rfl rfl
  intro ctx' e' ty' hd
  induction hd using RunWT.rec
    (motive_2 := fun ctx branch scrutTy resultTy _ =>
      ∀ pre : Env, ctx.env = pre ++ schemes ++ env → ctx.ctors = ctors →
        RunWTMatchBranch ⟨pre ++ env, ctx.ctors⟩
          (branch.1, branch.2.substN (pre.length + branch.1.bindCount) values)
          scrutTy resultTy) with
  | primLitUnit => intro _ _ _; exact .primLitUnit
  | primLitInt => intro _ _ _; exact .primLitInt
  | primLitNat => intro _ _ _; exact .primLitNat
  | primLitChar => intro _ _ _; exact .primLitChar
  | primBinOpIntAdd => intro _ _ _; exact .primBinOpIntAdd
  | primBinOpIntSub => intro _ _ _; exact .primBinOpIntSub
  | primBinOpIntLt _ _ ihtrue ihfalse =>
      intro pre hctx hctors
      exact .primBinOpIntLt (ihtrue pre hctx hctors) (ihfalse pre hctx hctors)
  | primBinOpCharLt _ _ ihtrue ihfalse =>
      intro pre hctx hctors
      exact .primBinOpCharLt (ihtrue pre hctx hctors) (ihfalse pre hctx hctors)
  | lambda hparam _ ihbody =>
      intro pre hctx hctors
      expose_names
      simp only [Expr.substN]
      have hb := ihbody (PolyTy.mkTrivial paramTy :: pre)
        (by simp only [hctx, List.cons_append, List.append_assoc]) hctors
      exact RunWT.lambda hparam (by
        simpa only [List.cons_append, List.length_cons] using hb)
  | app _ _ ihfn iharg =>
      intro pre hctx hctors
      simp only [Expr.substN]
      exact .app (ihfn pre hctx hctors) (iharg pre hctx hctors)
  | letIn hwf hgen _ ihgen ihbody =>
      intro pre hctx hctors
      expose_names
      simp only [Expr.substN]
      apply RunWT.letIn (scheme := scheme) (avoid := avoid) hwf
      · intro names hfresh
        exact ihgen names hfresh pre hctx hctors
      · have hb := ihbody (scheme :: pre)
          (by simp only [hctx, List.cons_append, List.append_assoc]) hctors
        simpa only [List.cons_append, List.length_cons] using hb
  | var hlookup hlc hinst =>
      intro pre hctx hctors
      expose_names
      rw [hctx] at hlookup
      rw [List.append_assoc] at hlookup
      simp only [Expr.substN]
      by_cases hlt : index < pre.length
      · rw [if_pos hlt]
        refine .var ?_ hlc hinst
        rw [List.getElem?_append_left hlt]
        rwa [List.getElem?_append_left hlt] at hlookup
      · rw [if_neg hlt]
        by_cases hin : index - pre.length < values.length
        · rw [dif_pos hin]
          have hschemeLt : index - pre.length < schemes.length := by omega
          rw [List.getElem?_append_right (by omega),
            List.getElem?_append_left hschemeLt,
            List.getElem?_eq_getElem hschemeLt, Option.some.injEq] at hlookup
          subst scheme
          have hs : RunHasScheme ⟨env, ctors⟩ values[index - pre.length]
              schemes[index - pre.length] :=
            (List.forall₂_iff_get.mp hvalues).2 _ hin hschemeLt
          have hv := hs args _ hlc hinst
          rw [← hctors] at hv
          simpa only [List.nil_append] using
            (RunWT.weakenEnv (envPre := []) (envExtra := pre) hv)
        · rw [dif_neg hin]
          refine .var ?_ hlc hinst
          rw [List.getElem?_append_right (by omega : pre.length ≤ index - values.length)]
          rw [List.getElem?_append_right (by omega),
            List.getElem?_append_right (by omega : schemes.length ≤ index - pre.length)]
            at hlookup
          rw [show index - values.length - pre.length =
              index - pre.length - schemes.length by omega]
          exact hlookup
  | ctor hlookup hlc hinst =>
      intro _ _ _
      exact .ctor hlookup hlc hinst
  | match_ _ hne _ ihscrut ihbranches =>
      intro pre hctx hctors
      simp only [Expr.substN]
      refine .match_ (ihscrut pre hctx hctors) ?_ ?_
      · intro hnil
        obtain ⟨⟨p, b⟩, rest, hb⟩ := List.exists_cons_of_ne_nil hne
        have hm := BranchList.mem_substN_of_mem
          (k := pre.length) (vs := values)
          (hb ▸ List.mem_cons_self (a := (p, b)))
        rw [hnil] at hm
        exact List.not_mem_nil hm
      · intro branch' hm'
        obtain ⟨pat, body, hm, rfl⟩ := BranchList.mem_substN hm'
        exact ihbranches (pat, body) hm pre hctx hctors
  | @letRec bindings ctx body resultTy specs G avoid hwf hmono hpoly _
      ihmono ihpoly ihbody =>
      intro pre hctx hctors
      simp only [Expr.substN, RecGroup.substN_eq_map]
      have hwf' : RecSpecsWF
          (bindings.map
            (Expr.substN (pre.length + bindings.length) values))
          specs G :=
        { hwf with length := by simpa using hwf.length }
      have hann :
          (bindings.map
            (Expr.substN (pre.length + bindings.length) values)).map
              (fun _ => (none : Option PolyTy)) =
            bindings.map (fun _ => (none : Option PolyTy)) := by
        simp only [List.map_map, Function.comp_def]
      rw [← hann]
      apply RunWT.letRec (specs := specs) (G := G) (avoid := avoid) hwf'
      · intro Xs hXs pair hpair τ hτ
        rw [List.zip_map_left] at hpair
        obtain ⟨oldPair, holdPair, rfl⟩ := List.mem_map.mp hpair
        have ht := ihmono Xs hXs oldPair holdPair τ hτ
          (specs.map (RecSpec.rhsEntry G Xs) ++ pre) (by
            simp only [RecSpecs.rhsCtx, hctx, List.append_assoc]) hctors
        simp only [RecSpecs.rhsCtx, List.length_append, List.length_map] at ht
        rw [← hwf.length, Nat.add_comm bindings.length pre.length] at ht
        simpa only [RecSpecs.rhsCtx, List.append_assoc] using ht
      · intro Xs hXs pair hpair scheme hscheme Ys hYs
        rw [List.zip_map_left] at hpair
        obtain ⟨oldPair, holdPair, rfl⟩ := List.mem_map.mp hpair
        have ht := ihpoly Xs hXs oldPair holdPair scheme hscheme Ys hYs
          (specs.map (RecSpec.rhsEntry G Xs) ++ pre) (by
            simp only [RecSpecs.rhsCtx, hctx, List.append_assoc]) hctors
        simp only [RecSpecs.rhsCtx, List.length_append, List.length_map] at ht
        rw [← hwf.length, Nat.add_comm bindings.length pre.length] at ht
        simpa only [RecSpecs.rhsCtx, List.append_assoc] using ht
      · have hb := ihbody (specs.map (RecSpec.bodyScheme G) ++ pre) (by
          simp only [RecSpecs.bodyCtx, hctx, List.append_assoc]) hctors
        simp only [RecSpecs.bodyCtx, List.length_append, List.length_map] at hb
        rw [← hwf.length, Nat.add_comm bindings.length pre.length] at hb
        simpa only [RecSpecs.bodyCtx, List.append_assoc] using hb
  | mk hspec _ ihbody =>
      expose_names
      have hb := ihbody (instContents.map PolyTy.mkTrivial ++ pre) (by
        simp only [h_2, List.append_assoc]) h_3
      simp only [List.length_append, List.length_map] at hb
      have hlen : instContents.length = n := by
        have := List.Forall₂.length_eq hspec.fields
        simpa [hspec.bind_count] using this.symm
      rw [hlen, Nat.add_comm n pre.length] at hb
      exact RunWTMatchBranch.mk hspec (by
        simpa only [List.append_assoc] using hb)
  | wildcard _ ihbody =>
      expose_names
      simpa only [MatchPattern.bindCount, Nat.add_zero] using
        (RunWTMatchBranch.wildcard (ihbody pre h_2 h_3))


/-- Subject reduction for the recursive-group unfolding rule. Each RHS is
substituted as an erased self-wrapped value at its exported scheme. -/
theorem RunWT.letRecUnfold_preservation {ctx : Ctx}
    {anns : List (Option PolyTy)} {bindings : List Expr} {body : Expr}
    {ty : Ty}
    (h : RunWT ctx (.letRec anns bindings body) ty) :
    RunWT ctx
      (body.substN 0
        (bindings.map (fun rhs => .letRec anns bindings rhs))) ty := by
  cases h with
  | letRec hwf hmono hpoly hbody =>
      have hvalues := recursiveValuesHaveSchemes hwf hmono hpoly
      have hsubst := RunWT.substMany (envPre := []) hvalues hbody
      simpa [RecSpecs.bodyCtx, List.nil_append, RecSpec.bodyScheme] using hsubst


/-! ## A real-Core erased polymorphic-recursion witness -/

def polyId : PolyTy := ⟨1, .arrow (.bvar 0) (.bvar 0)⟩

/-- `fun x => (fun _ => x) (self 0)`: the current call is at a rigid `a`,
while the recursive occurrence is independently instantiated at `Int`. -/
def polySelfRhs : Expr :=
  .lambda none
    (.app (.lambda none (.var 1)) (.app (.var 1) (.primLit (.int 0))))

def polySelfBindings : List Expr := [polySelfRhs]

theorem polyId_wf : polyId.WF := by
  show ContainsBvarsUpTo 1 (.arrow (.bvar 0) (.bvar 0))
  exact .arrow (.bvar (by omega)) (.bvar (by omega))

theorem polySelf_specs_wf :
    RecSpecsWF polySelfBindings [.poly polyId] [] := by
  refine ⟨by simp [polySelfBindings], by simp, ?_, ?_⟩
  · intro ty hty
    simp at hty
  · intro scheme hscheme
    simp only [List.mem_singleton, RecSpec.poly.injEq] at hscheme
    subst scheme
    exact polyId_wf

theorem polySelf_mono :
    MonoTyped RunWT ⟨[], []⟩ polySelfBindings [.poly polyId] [] [] := by
  intro Xs hXs pair hpair ty hmono
  have hXsNil : Xs = [] := List.length_eq_zero_iff.mp hXs.length
  subst Xs
  simp [polySelfBindings] at hpair
  subst pair
  simp at hmono

private theorem singleton_of_fresh_one {avoid names : List Nat}
    (h : FreshNames avoid 1 names) : ∃ name, names = [name] := by
  exact List.length_eq_one_iff.mp h.length

theorem polySelf_poly :
    PolyTyped RunWT ⟨[], []⟩ polySelfBindings [.poly polyId] [] [] := by
  intro Xs hXs pair hpair scheme hscheme Ys hYs
  have hXsNil : Xs = [] := List.length_eq_zero_iff.mp hXs.length
  subst Xs
  simp [polySelfBindings] at hpair
  subst pair
  simp only [RecSpec.poly.injEq] at hscheme
  subst scheme
  obtain ⟨Y, rfl⟩ := singleton_of_fresh_one hYs
  change RunWT ⟨[polyId], []⟩ polySelfRhs
    (.arrow (.fvar Y) (.fvar Y))
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

/-- No scheme or type application occurs anywhere in this runtime expression. -/
theorem erased_polySelf_typed :
    RunWT ⟨[], []⟩
      (.letRec (polySelfBindings.map (fun _ => none))
        polySelfBindings (.var 0))
      (.arrow (.prim .unit) (.prim .unit)) := by
  exact .letRec polySelf_specs_wf polySelf_mono polySelf_poly polySelf_body

theorem erased_polySelf_steps :
    SmallStep.Step
      (.letRec (polySelfBindings.map (fun _ => none))
        polySelfBindings (.var 0))
      ((Expr.var 0).substN 0
        (polySelfBindings.map (fun rhs =>
          .letRec (polySelfBindings.map (fun _ => none))
            polySelfBindings rhs))) := by
  exact .letRecUnfold

theorem erased_polySelf_unfolded_typed :
    RunWT ⟨[], []⟩
      ((Expr.var 0).substN 0
        (polySelfBindings.map (fun rhs =>
          .letRec (polySelfBindings.map (fun _ => none))
            polySelfBindings rhs)))
      (.arrow (.prim .unit) (.prim .unit)) := by
  exact RunWT.letRecUnfold_preservation erased_polySelf_typed

#print axioms RunWT.substFvar
#print axioms RunWT.substMany
#print axioms RunWT.letRecUnfold_preservation
#print axioms erased_polySelf_typed
#print axioms erased_polySelf_unfolded_typed

end RuntimeTyping
