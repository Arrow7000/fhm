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

#print axioms RunWT.substFvar
#print axioms erased_polySelf_typed

end RuntimeTyping
