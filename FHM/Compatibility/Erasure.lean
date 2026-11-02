import FHM.Compatibility.Typing
import FHM.RuntimeTyping

/-! The optional complete-Core erasure bridge. Runtime typing itself has no
historical source-typing dependency. -/

/-- Checking the annotated source first justifies its completely erased runtime
term. Recursive schemes survive only as witnesses in the runtime derivation. -/
theorem TypeOfHM.erase_preserves_typing {ctx : Ctx} {e : Expr} {τ : Ty}
    (h : TypeOfHM ctx e τ) : RuntimeTyping.RunWT ctx e.erase τ := by
  induction h using TypeOfHM.rec
    (motive_2 := fun ctx branch scrutTy resultTy _ =>
      RuntimeTyping.RunWTMatchBranch ctx (branch.1, branch.2.erase)
        scrutTy resultTy) with
  | primLitUnit => simpa only [Expr.erase] using RuntimeTyping.RunWT.primLitUnit
  | primLitInt => simpa only [Expr.erase] using RuntimeTyping.RunWT.primLitInt
  | primLitNat => simpa only [Expr.erase] using RuntimeTyping.RunWT.primLitNat
  | primLitChar => simpa only [Expr.erase] using RuntimeTyping.RunWT.primLitChar
  | primBinOpIntAdd =>
      simpa only [Expr.erase] using RuntimeTyping.RunWT.primBinOpIntAdd
  | primBinOpIntSub =>
      simpa only [Expr.erase] using RuntimeTyping.RunWT.primBinOpIntSub
  | primBinOpIntLt _ _ ihtrue ihfalse =>
      simp only [Expr.erase] at ihtrue ihfalse ⊢
      exact RuntimeTyping.RunWT.primBinOpIntLt ihtrue ihfalse
  | primBinOpCharLt _ _ ihtrue ihfalse =>
      simp only [Expr.erase] at ihtrue ihfalse ⊢
      exact RuntimeTyping.RunWT.primBinOpCharLt ihtrue ihfalse
  | lambda hpc _ _ _ ihbody =>
      expose_names
      subst bodyCtx
      simp only [Expr.erase]
      exact RuntimeTyping.RunWT.lambda hpc ihbody
  | app _ _ ihfn iharg =>
      simpa only [Expr.erase] using RuntimeTyping.RunWT.app ihfn iharg
  | letIn hwf _ _ _ _ ihcofin ihbody =>
      expose_names
      subst bodyCtx
      simp only [Expr.erase]
      refine RuntimeTyping.RunWT.letIn (scheme := M) (avoid := L) hwf ?_ ihbody
      intro Xs hfresh
      have hrhs := ihcofin Xs hfresh
      rwa [Expr.erase_openBoundTyVars] at hrhs
  | var hlook hargs hinst =>
      simpa only [Expr.erase] using RuntimeTyping.RunWT.var hlook hargs hinst
  | ctor hlook hargs hinst =>
      simpa only [Expr.erase] using RuntimeTyping.RunWT.ctor hlook hargs hinst
  | match_ _ hne _ ihscrut ihbranches =>
      expose_names
      simp only [Expr.erase_match]
      refine RuntimeTyping.RunWT.match_ ihscrut ?_ ?_
      · intro hempty
        obtain ⟨head, tail, rfl⟩ := List.exists_cons_of_ne_nil hne
        simp at hempty
      · intro branch' hmem'
        obtain ⟨⟨pat, branchBody⟩, hmem, rfl⟩ := List.mem_map.mp hmem'
        exact ihbranches (pat, branchBody) hmem
  | letRec hgroups hwf _ _ heq _ ihstrat ihpoly ihbody =>
      expose_names
      subst heq
      let runtimeAvoid := L ++ G ++ specs.flatMap RecSpec.monoFreeVars
      simp only [Expr.erase_letRec]
      refine RuntimeTyping.RunWT.letRec (specs := specs) (G := G)
        (avoid := runtimeAvoid)
        ⟨by simpa using hwf.length, hwf.nodup, hwf.mono_lc, hwf.poly_wf⟩
        ?_ ?_ ihbody
      · intro Xs hfresh pair hpair ty heq
        obtain ⟨binding, spec, _, hpair', rfl⟩ := List.mem_zip_map_left hpair
        have hmono : spec = .mono ty := heq
        obtain ⟨member, hzip⟩ := List.mem_iff_getElem?.mp hpair'
        obtain ⟨hbinding, hspec⟩ := List.getElem?_zip_eq_some.mp hzip
        rw [hmono] at hspec
        have hbound : member < bindings.length := by
          exact (List.getElem?_eq_some_iff.mp hbinding).1
        have hunsigned : RecGroups.UnsignedAt bindings member := by
          have halign := congrArg (fun entries => entries[member]?) hwf.anns_eq
          simp only [List.getElem?_map, hspec, hbinding, Option.map_some,
            RecSpec.ann] at halign
          simpa only [RecGroups.UnsignedAt, hbinding, Option.map_some] using
            halign.symm
        have hcovered := (hgroups.covers_unsigned member hbound).2 hunsigned
        obtain ⟨component, hcomponent, hmember⟩ := List.mem_flatten.mp hcovered
        obtain ⟨stage, hstage⟩ := List.mem_iff_getElem?.mp hcomponent
        have hfreshSource : FreshNames L G.length Xs := by
          refine ⟨hfresh.length, hfresh.nodup, ?_⟩
          intro x hx hL
          exact hfresh.avoid x hx (by
            simp only [runtimeAvoid, List.mem_append]
            exact .inl (.inl hL))
        have hrhs := ihstrat stage component hstage Xs hfreshSource
          member hmember binding ty hbinding hspec
        have hGXs : ∀ g ∈ G, g ∉ Xs := by
          intro g hg hmem
          exact hfresh.avoid g hmem (by
            simp only [runtimeAvoid, List.mem_append]
            exact .inl (.inr hg))
        have hXsMono : ∀ monoTy, RecSpec.mono monoTy ∈ specs →
            ∀ x ∈ Xs, x ∉ monoTy.freeVars := by
          intro monoTy hmember x hx hfree
          exact hfresh.avoid x hx (by
            simp only [runtimeAvoid, List.mem_append]
            exact .inr (List.mem_flatMap.mpr
              ⟨.mono monoTy, hmember, hfree⟩))
        have hgens :=
          RuntimeTyping.bodySchemes_generalize_stageEntries_runtime
            (done := (groups.take stage).flatten)
            hwf.nodup hfresh.length hfresh.nodup hwf.mono_lc hGXs hXsMono
        have hfinal := RuntimeTyping.RunWT.weaken_schemes hgens hrhs
        simpa only [RecSpecs.stageCtx, RecSpecs.bodyCtx] using hfinal
      · intro pair hpair scheme heq Ys hfreshY
        obtain ⟨binding, spec, _, hpair', rfl⟩ := List.mem_zip_map_left hpair
        have hfreshSource : FreshNames L scheme.paramCount Ys := by
          refine ⟨hfreshY.length, hfreshY.nodup, ?_⟩
          intro x hx hL
          exact hfreshY.avoid x hx (by
            simp only [runtimeAvoid, List.mem_append]
            exact .inl (.inl hL))
        have hrhs := ihpoly (binding, spec) hpair' scheme heq Ys hfreshSource
        rwa [Expr.erase_openTyVars] at hrhs
  | mk hspec _ _ ihbody =>
      expose_names
      subst bodyCtx
      exact RuntimeTyping.RunWTMatchBranch.mk hspec ihbody
  | wildcard _ ihbody => exact RuntimeTyping.RunWTMatchBranch.wildcard ihbody
