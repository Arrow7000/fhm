import FHM.Bounds.RecursiveHMJudgement
import FHM.Bounds.RecursiveRHS

/-! The already checked recursive RHS fragment embeds in the HM-interpreted
judgement with its exact intervals and unchanged source expression. No new
inference pass, guessed argument bounds or decoded-assumption shortcut. -/

namespace FHM.Bounds.RecursiveHMEmbedding

open RecursiveHMJudgement CountSubstitution

private theorem erased (c : RecursiveContract.Declared) : c.hm.eraseBounds = c.hm := by
  rw [← c.shape]
  exact FreeAlgebra.shape_erased _

def template (c : RecursiveContract.Declared) : HMCountScheme.Scheme :=
  ⟨⟨0, c.hm⟩, c.counts, c.lc, c.wf, c.shape⟩

def contract (c : RecursiveContract.Declared) : Contract :=
  ⟨template c, c.hm, ⟨[], rfl, by simp, by
      change Synth.BoundsTy.toTy (TypeSubstitution.substitute (SchemeUse.vector []) c.counts.body) = c.hm.eraseBounds
      have lc : (Synth.BoundsTy.toTy c.counts.body).IsLC := by rw [c.shape]; exact c.lc
      rw [FreeAlgebra.instantiate_fixed _ lc]
      exact c.shape.trans (erased c).symm,
    by rw [erased c]; exact c.lc⟩⟩

def binding : RecursiveTyping.Binding → Binding
  | .mono β => .mono β
  | .recursive c => .recursive (contract c)

private def recursiveUse {c : RecursiveContract.Declared} {Δ args caller}
    (inst : ScopedScheme.Instance c.counts args caller)
    (hu : inst.Usable Δ) : RecursiveHMContract.Use (contract c).fixed Δ (contract c).hm caller :=
  ⟨args, inst, hu, rfl, rfl⟩

private theorem recursiveUse_bounds {c : RecursiveContract.Declared} {Δ args caller}
    (inst : ScopedScheme.Instance c.counts args caller)
    (hu : inst.Usable Δ) : (recursiveUse inst hu).bounds = inst.bounds := by
  change TypeSubstitution.substitute (SchemeUse.vector []) inst.bounds = inst.bounds
  apply FreeAlgebra.instantiate_fixed
  rw [inst.shape, c.shape]
  exact c.lc

private theorem param {ids rows Δ ann β} (h : InterpretedAnnotation.ParamOK ids rows Δ ann β) :
    HMInterpretation.ParamOK BoundsTy.fvar ids rows Δ ann β := by
  cases ann with
  | none => trivial
  | some τ => exact HMInterpretation.AnnotationOK.identity h

private theorem annotation {ids rows Δ ann β} (h : InterpretedAnnotation.BindingOK ids rows Δ ann β) :
    HMInterpretation.BindingOK BoundsTy.fvar ids rows Δ ann β := by
  cases ann with
  | none => trivial
  | some σ => exact ⟨h.1, HMInterpretation.AnnotationOK.identity h.2⟩

/-- Every existing checked no-group RHS keeps its exact bounds derivation in
    the new judgement. The explicit no-group premise is the current RHS slice,
    not a weakening of recursive group introduction. -/
theorem typing {ids rows Δ env e β} (h : RecursiveTyping.Derives ids rows Δ env e β)
    (noGroups : RecursiveCountTransport.NoGroups e) :
    Derives BoundsTy.fvar ids rows Δ (env.map binding) e β := by
  cases h with
  | literal => exact .literal
  | primBinOp => exact .primBinOp
  | nil => exact .nil
  | boolCtor hn => exact .boolCtor hn
  | cons hh ht hs =>
      simp only [RecursiveCountTransport.NoGroups] at noGroups
      exact .cons (typing hh noGroups.1.2) (typing ht noGroups.2) hs
  | varMono hv => exact .varMono (by simpa [binding] using congrArg (Option.map binding) hv)
  | varRecursive hv inst hu =>
      rw [← recursiveUse_bounds inst hu]
      exact .varRecursive (by
        simpa only [List.getElem?_map, binding, Option.map_some] using
          congrArg (Option.map binding) hv) (recursiveUse inst hu)
  | app hf ha hs =>
      simp only [RecursiveCountTransport.NoGroups] at noGroups
      exact .app (typing hf noGroups.1) (typing ha noGroups.2) hs
  | lambda hp hb =>
      simp only [RecursiveCountTransport.NoGroups] at noGroups
      exact .lambda (param hp) (by simpa [binding] using typing hb noGroups)
  | letMono hp hr hb =>
      simp only [RecursiveCountTransport.NoGroups] at noGroups
      exact .letMono (annotation hp) (typing hr noGroups.1) (by simpa [binding] using typing hb noGroups.2)
  | matchList hs hc hpat hbranches hsub =>
      simp only [RecursiveCountTransport.NoGroups] at noGroups
      apply Derives.matchList (typing hs noGroups.1) hc hpat
      · intro i br hb
        have ht := typing (hbranches i br hb) (noGroups.2 br (List.mem_of_getElem? hb))
        by_cases hbr : br.1 = .named consCtorName 2
        · simpa [RecursiveTyping.branchEnv, branchEnv, hbr, binding] using ht
        · simpa [RecursiveTyping.branchEnv, branchEnv, hbr] using ht
      · exact hsub
  | matchBool hs hc hpat hbranches hsub =>
      simp only [RecursiveCountTransport.NoGroups] at noGroups
      exact .matchBool (typing hs noGroups.1) hc hpat
        (fun i br hb => typing (hbranches i br hb) (noGroups.2 br (List.mem_of_getElem? hb))) hsub
  | letRec => simp only [RecursiveCountTransport.NoGroups] at noGroups
termination_by sizeOf e
decreasing_by
  all_goals subst_vars
  all_goals simp_wf
  all_goals first | omega |
    (have hsz := List.sizeOf_lt_of_mem (List.mem_of_getElem? ‹_ = some _›)
     cases ‹MatchPattern × Expr›
     simp only [Prod.mk.sizeOf_spec] at hsz ⊢
     omega)

theorem certified {c env rhs ann} (cert : RecursiveRHS.Certified c env rhs ann) :
    Derives BoundsTy.fvar (c.counts.quantified ++ c.counts.captures) [] c.counts.premises
      (env.map binding) rhs cert.actual := typing cert.typing cert.noGroups

#print axioms contract
#print axioms typing
#print axioms certified

end FHM.Bounds.RecursiveHMEmbedding
