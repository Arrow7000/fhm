import FHM.Bounds.RecursiveHMContract
import FHM.Bounds.HMInterpretation

/-! # Recursive RHS typing with an explicit proof-side HM interpretation

This is the HM-generalization target of the checked recursive RHS fragment.
Source annotations are interpreted using one simultaneous map for the whole
derivation. Recursive assumptions retain closed templates and fixed HM vectors.
Group introduction is separate: this judgement alone licenses no assumptions.
-/

namespace FHM.Bounds.RecursiveHMJudgement

open CountSubstitution SchemeSpecialization HMInterpretation

structure Contract where
  template : HMCountScheme.Scheme
  hm : Ty
  fixed : RecursiveHMContract.Fixed template hm

inductive Binding where
  | mono (bounds : BoundsTy)
  | recursive (contract : Contract)

def branchEnv (p : MatchPattern) (lo hi : Count) (elem : BoundsTy) (env : List Binding) : List Binding :=
  if p = .named consCtorName 2 then
    .mono elem :: .mono (.list (.pred lo) (.pred hi) elem) :: env
  else env

inductive ScopedDerives (types slots : Nat → BoundsTy) : List Nat → Bindings → List Constraint →
    List Binding → Expr → BoundsTy → Prop where
  | literal {env p} : ScopedDerives types slots ids rows Δ env (.primLit p) (boundInfoOfPrimLit p)
  | primBinOp {env op} : ScopedDerives types slots ids rows Δ env (.primBinOp op) (Typed.primOpBounds op)
  | nil {env elem} : ScopedDerives types slots ids rows Δ env (.ctor nilCtorName) (.list (.lit 0) (.lit 0) elem)
  | boolCtor {env name} : BoolBranches.IsCtor name →
      ScopedDerives types slots ids rows Δ env (.ctor name) (.custom boolTyName [])
  | cons {env h t head elem lo hi} :
      ScopedDerives types slots ids rows Δ env h head → ScopedDerives types slots ids rows Δ env t (.list lo hi elem) →
      SemanticSub Δ head elem →
      ScopedDerives types slots ids rows Δ env (.app (.app (.ctor consCtorName) h) t)
        (.list (.add lo (.lit 1)) (.add hi (.lit 1)) elem)
  | varMono {env i β} : env[i]? = some (.mono β) → ScopedDerives types slots ids rows Δ env (.var i) β
  | varRecursive {env i c caller} : env[i]? = some (.recursive c) →
      (u : RecursiveHMContract.Use c.fixed Δ c.hm caller) →
      ScopedDerives types slots ids rows Δ env (.var i) u.bounds
  | app {env f arg domain actual result} :
      ScopedDerives types slots ids rows Δ env f (.arrow domain result) → ScopedDerives types slots ids rows Δ env arg actual →
      SemanticSub Δ actual domain → ScopedDerives types slots ids rows Δ env (.app f arg) result
  | lambda {env ann body param result} :
      ScopedHMAnnotation.ParamOK types slots ids rows Δ ann param →
      ScopedDerives types slots ids rows Δ (.mono param :: env) body result →
      ScopedDerives types slots ids rows Δ env (.lambda ann body) (.arrow param result)
  | letMono {env ann rhs body actual result} :
      ScopedHMAnnotation.BindingOK types slots ids rows Δ ann actual →
      ScopedDerives types slots ids rows Δ env rhs actual → ScopedDerives types slots ids rows Δ (.mono actual :: env) body result →
      ScopedDerives types slots ids rows Δ env (.letIn ann rhs body) result
  | matchList {env scrut branches lo hi elem result} {actuals : Nat → BoundsTy} :
      ScopedDerives types slots ids rows Δ env scrut (.list lo hi elem) →
      ListBranches.Covers Δ ⟨lo, hi⟩ branches →
      (∀ br ∈ branches, RecursiveTyping.ListPattern br.1) →
      (∀ i br, branches[i]? = some br →
        ScopedDerives types slots ids rows (Δ ++ RecursiveTyping.branchRefine br.1 lo hi)
          (branchEnv br.1 lo hi elem env) br.2 (actuals i)) →
      (∀ i br, branches[i]? = some br →
        SemanticSub (Δ ++ RecursiveTyping.branchRefine br.1 lo hi) (actuals i) result) →
      ScopedDerives types slots ids rows Δ env (.match_ scrut branches) result
  | matchBool {env scrut branches result} {actuals : Nat → BoundsTy} :
      ScopedDerives types slots ids rows Δ env scrut (.custom boolTyName []) → BoolBranches.Covers branches →
      (∀ br ∈ branches, BoolBranches.Pattern br.1) →
      (∀ i br, branches[i]? = some br → ScopedDerives types slots ids rows Δ env br.2 (actuals i)) →
      (∀ i br, branches[i]? = some br → SemanticSub Δ (actuals i) result) →
      ScopedDerives types slots ids rows Δ env (.match_ scrut branches) result

/-- Compatibility view: the original API leaves lexical slots unchanged. -/
abbrev Derives (types : Nat → BoundsTy) := ScopedDerives types BoundsTy.bvar

namespace Derives
abbrev literal {types : Nat → BoundsTy} := @ScopedDerives.literal types BoundsTy.bvar
abbrev primBinOp {types : Nat → BoundsTy} := @ScopedDerives.primBinOp types BoundsTy.bvar
abbrev nil {types : Nat → BoundsTy} := @ScopedDerives.nil types BoundsTy.bvar
abbrev boolCtor {types : Nat → BoundsTy} := @ScopedDerives.boolCtor types BoundsTy.bvar
abbrev cons {types : Nat → BoundsTy} := @ScopedDerives.cons types BoundsTy.bvar
abbrev varMono {types : Nat → BoundsTy} := @ScopedDerives.varMono types BoundsTy.bvar
abbrev varRecursive {types : Nat → BoundsTy} := @ScopedDerives.varRecursive types BoundsTy.bvar
abbrev app {types : Nat → BoundsTy} := @ScopedDerives.app types BoundsTy.bvar
abbrev lambda {types : Nat → BoundsTy} := @ScopedDerives.lambda types BoundsTy.bvar
abbrev letMono {types : Nat → BoundsTy} := @ScopedDerives.letMono types BoundsTy.bvar
abbrev matchList {types : Nat → BoundsTy} := @ScopedDerives.matchList types BoundsTy.bvar
abbrev matchBool {types : Nat → BoundsTy} := @ScopedDerives.matchBool types BoundsTy.bvar
end Derives

/-- Shared source-parameter obligation transport for RHS and body judgments. -/
theorem param_assuming {types slots ids rows Δ Δ' ann β}
    (h : ScopedHMAnnotation.ParamOK types slots ids rows Δ ann β)
    (hp : (⟨Δ', Δ⟩ : ForallProblem).Valid) :
    ScopedHMAnnotation.ParamOK types slots ids rows Δ' ann β := by
  cases ann with
  | none => trivial
  | some τ => exact h.assuming hp

/-- Shared source mono-binding obligation transport; forall guards remain intact. -/
theorem binding_assuming {types slots ids rows Δ Δ' ann β}
    (h : ScopedHMAnnotation.BindingOK types slots ids rows Δ ann β)
    (hp : (⟨Δ', Δ⟩ : ForallProblem).Valid) :
    ScopedHMAnnotation.BindingOK types slots ids rows Δ' ann β := by
  cases ann with
  | none => trivial
  | some σ => exact ⟨h.1, h.2.assuming hp⟩

/-- A caller must establish instantiated contract premises. Transport the
    entire actual RHS, including nested source obligations and refined arms,
    into that caller context rather than silently appending assumptions. -/
theorem ScopedDerives.assuming {types slots ids rows Δ Δ' env e β}
    (h : ScopedDerives types slots ids rows Δ env e β)
    (hp : (⟨Δ', Δ⟩ : ForallProblem).Valid) : ScopedDerives types slots ids rows Δ' env e β := by
  induction h generalizing Δ' with
  | literal => exact .literal
  | primBinOp => exact .primBinOp
  | nil => exact .nil
  | boolCtor hn => exact .boolCtor hn
  | cons _ _ hs ihh iht => exact .cons (ihh hp) (iht hp) (hs.assuming hp)
  | varMono hv => exact .varMono hv
  | varRecursive hv used =>
      let next : RecursiveHMContract.Use _ Δ' _ _ :=
        ⟨used.counts, used.inst, by
          intro σ hΔ goal hgoal
          exact used.usable σ (fun c hc => hp σ hΔ c hc) goal hgoal,
          used.typesScoped, used.fixedHM⟩
      exact .varRecursive hv next
  | app _ _ hs ihh iht => exact .app (ihh hp) (iht hp) (hs.assuming hp)
  | lambda hparam _ ih => exact .lambda (param_assuming hparam hp) (ih hp)
  | letMono hbind _ _ ihr ihb => exact .letMono (binding_assuming hbind hp) (ihr hp) (ihb hp)
  | matchList _ hc hpat _ hsub ihscrut ihbranches =>
      exact .matchList (ihscrut hp) (hc.assuming hp) hpat
        (fun i br hb => ihbranches i br hb (RecursiveTyping.assuming_append hp))
        (fun i br hb => (hsub i br hb).assuming (RecursiveTyping.assuming_append hp))
  | matchBool _ hc hpat _ hsub ihscrut ihbranches =>
      exact .matchBool (ihscrut hp) hc hpat
        (fun i br hb => ihbranches i br hb hp)
        (fun i br hb => (hsub i br hb).assuming hp)

def Contract.mapTypes (c : Contract) (f : Nat → BoundsTy)
    (hf : ∀ i, (Synth.BoundsTy.toTy (f i)).IsLC) : Contract :=
  ⟨c.template, Synth.BoundsTy.toTy (HMCountScheme.opened c.template (c.fixed.types.map (mapFree f))),
    c.fixed.mapTypes f hf⟩

def mapBinding (f : Nat → BoundsTy) (hf : ∀ i, (Synth.BoundsTy.toTy (f i)).IsLC) : Binding → Binding
  | .mono β => .mono (mapFree f β)
  | .recursive c => .recursive (c.mapTypes f hf)

def CapturesFixed (f : Nat → BoundsTy) (env : List Binding) : Prop :=
  ∀ c, .recursive c ∈ env → ∀ i ∈ c.template.hm.body.freeVars, f i = .fvar i

private theorem captures_cons {f env β} (h : CapturesFixed f env) : CapturesFixed f (.mono β :: env) := by
  intro c hc i hi
  rcases List.mem_cons.mp hc with impossible | rest
  · cases impossible
  · exact h c rest i hi

private theorem captures_branch {f env p lo hi elem} (h : CapturesFixed f env) :
    CapturesFixed f (branchEnv p lo hi elem env) := by
  unfold branchEnv
  split
  · exact captures_cons (captures_cons h)
  · exact h

private def weakenInstance {s args caller} (inst : ScopedScheme.Instance s args caller) (target : List Nat) :
    ScopedScheme.Instance s args (caller ++ target) :=
  { wf := inst.wf, arity := inst.arity, finiteArgs := inst.finiteArgs
    argsScoped := fun a ha => count_mono (inst.argsScoped a ha) (fun _ hi => List.mem_append_left _ hi)
    capturesScoped := fun i hi => List.mem_append_left _ (inst.capturesScoped i hi)
    bodyScoped := scope_mono inst.bodyScoped (fun _ hi => List.mem_append_left _ hi)
    premisesScoped := fun c hc =>
      ⟨count_mono (inst.premisesScoped c hc).1 (fun _ hi => List.mem_append_left _ hi),
        count_mono (inst.premisesScoped c hc).2 (fun _ hi => List.mem_append_left _ hi)⟩ }

private def mapUse {c : Contract} {Δ caller} (u : RecursiveHMContract.Use c.fixed Δ c.hm caller)
    (f : Nat → BoundsTy) (hf : ∀ i, (Synth.BoundsTy.toTy (f i)).IsLC) (target : List Nat)
    (scope : ∀ i, ScopedScheme.BoundsScoped target (f i)) :
    RecursiveHMContract.Use (c.mapTypes f hf).fixed Δ (c.mapTypes f hf).hm (caller ++ target) := by
  refine ⟨u.counts, weakenInstance u.inst target, u.usable, ?_, rfl⟩
  apply List.all_eq_true.mpr
  intro a ha
  obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
  exact ScopedScheme.boundsScopedBool_complete
    (map_scope (ScopedScheme.boundsScopedBool_sound (List.all_eq_true.mp u.typesScoped b hb)) f scope)

private theorem mapUse_bounds {c : Contract} {Δ caller} (u : RecursiveHMContract.Use c.fixed Δ c.hm caller)
    (f : Nat → BoundsTy) (hf : ∀ i, (Synth.BoundsTy.toTy (f i)).IsLC) (target : List Nat)
    (scope : ∀ i, ScopedScheme.BoundsScoped target (f i))
    (captured : ∀ i ∈ c.template.hm.body.freeVars, f i = .fvar i) :
    (mapUse u f hf target scope).bounds = mapFree f u.bounds :=
  (RecursiveHMContract.map_combined c.template c.fixed.types _ f hf captured).symm

private theorem param_types {types slots ids rows Δ ann β}
    (h : ScopedHMAnnotation.ParamOK types slots ids rows Δ ann β) (f : Nat → BoundsTy) :
    ScopedHMAnnotation.ParamOK (fun i => mapFree f (types i)) (fun i => mapFree f (slots i)) ids rows Δ ann (mapFree f β) := by
  cases ann with
  | none => trivial
  | some τ => exact h.types f

private theorem binding_types {types slots ids rows Δ ann β}
    (h : ScopedHMAnnotation.BindingOK types slots ids rows Δ ann β) (f : Nat → BoundsTy) :
    ScopedHMAnnotation.BindingOK (fun i => mapFree f (types i)) (fun i => mapFree f (slots i)) ids rows Δ ann (mapFree f β) := by
  cases ann with
  | none => trivial
  | some σ => exact ⟨h.1, h.2.types f⟩

/-- Full RHS HM transport, including annotated lambdas, lets, recursive calls
    and all match arms. One map interprets the whole source derivation. -/
theorem transportScopedTypes (f : Nat → BoundsTy) (hf : ∀ i, (Synth.BoundsTy.toTy (f i)).IsLC)
    (target : List Nat) (scope : ∀ i, ScopedScheme.BoundsScoped target (f i))
    {types slots ids rows Δ env e β} (h : ScopedDerives types slots ids rows Δ env e β) (fresh : CapturesFixed f env) :
    ScopedDerives (fun i => mapFree f (types i)) (fun i => mapFree f (slots i)) ids rows Δ (env.map (mapBinding f hf)) e (mapFree f β) := by
  induction h with
  | literal => cases ‹PrimLitExpr› <;> exact .literal
  | primBinOp => cases ‹PrimBinOp› <;> exact .primBinOp
  | nil => exact .nil
  | boolCtor hn => exact .boolCtor hn
  | cons _ _ hs ihh iht => exact .cons (ihh fresh) (iht fresh) (SchemeSpecialization.subtype f hs)
  | varMono hv => exact .varMono (by simpa [mapBinding] using congrArg (Option.map (mapBinding f hf)) hv)
  | varRecursive hv u =>
      rw [← mapUse_bounds u f hf target scope (fresh _ (List.mem_of_getElem? hv))]
      exact .varRecursive (by simpa [mapBinding] using congrArg (Option.map (mapBinding f hf)) hv)
        (mapUse u f hf target scope)
  | app _ _ hs ihf iha => exact .app (ihf fresh) (iha fresh) (SchemeSpecialization.subtype f hs)
  | lambda hp _ ih =>
      exact .lambda (param_types hp f) (by simpa [mapBinding] using ih (captures_cons fresh))
  | letMono hp _ _ ihr ihb =>
      exact .letMono (binding_types hp f) (ihr fresh) (by simpa [mapBinding] using ihb (captures_cons fresh))
  | matchList _ hc hpat _ hsub ihscrut ihbranches =>
      apply ScopedDerives.matchList (ihscrut fresh) hc hpat
      · intro i br hb
        have ht := ihbranches i br hb (captures_branch fresh)
        by_cases hcbr : br.1 = .named consCtorName 2
        · simpa [branchEnv, hcbr, mapBinding, mapFree] using ht
        · simpa [branchEnv, hcbr] using ht
      · intro i br hb
        exact SchemeSpecialization.subtype f (hsub i br hb)
  | matchBool _ hc hpat _ hsub ihscrut ihbranches =>
      exact .matchBool (ihscrut fresh) hc hpat
        (fun i br hb => ihbranches i br hb fresh)
        (fun i br hb => SchemeSpecialization.subtype f (hsub i br hb))

def Contract.mapCounts (c : Contract) (outer : Bindings) : Contract :=
  ⟨c.template, c.hm, c.fixed.mapCounts outer⟩

def mapCountBinding (outer : Bindings) : Binding → Binding
  | .mono β => .mono (bounds outer β)
  | .recursive c => .recursive (c.mapCounts outer)

def CountCapturesFixed (outer : Bindings) (env : List Binding) : Prop :=
  ∀ c, .recursive c ∈ env → ∀ i ∈ c.template.counts.captures, lookup outer i = none

private theorem count_captures_cons {outer env β} (h : CountCapturesFixed outer env) :
    CountCapturesFixed outer (.mono β :: env) := by
  intro c hc i hi
  rcases List.mem_cons.mp hc with impossible | rest
  · cases impossible
  · exact h c rest i hi

private theorem count_captures_branch {outer env p lo hi elem} (h : CountCapturesFixed outer env) :
    CountCapturesFixed outer (branchEnv p lo hi elem env) := by
  unfold branchEnv
  split
  · exact count_captures_cons (count_captures_cons h)
  · exact h

private theorem param_counts {types slots ids rows Δ ann β}
    (h : ScopedHMAnnotation.ParamOK types slots ids rows Δ ann β) (outer : Bindings) (hf : Finite outer) :
    ScopedHMAnnotation.ParamOK (fun i => bounds outer (types i)) (fun i => bounds outer (slots i)) ids (CountAlgebra.compose outer rows)
      (Δ.map (constraint outer)) ann (bounds outer β) := by
  cases ann with
  | none => trivial
  | some τ => exact h.counts outer hf

private theorem binding_counts {types slots ids rows Δ ann β}
    (h : ScopedHMAnnotation.BindingOK types slots ids rows Δ ann β) (outer : Bindings) (hf : Finite outer) :
    ScopedHMAnnotation.BindingOK (fun i => bounds outer (types i)) (fun i => bounds outer (slots i)) ids (CountAlgebra.compose outer rows)
      (Δ.map (constraint outer)) ann (bounds outer β) := by
  cases ann with
  | none => trivial
  | some σ => exact ⟨h.1, h.2.counts outer hf⟩

/-- Whole-RHS count transport also maps counts inside inserted HM types. Closed
    callee telescopes stay protected and source annotations stay unchanged. -/
theorem transportScopedCounts (outer : Bindings) (hf : Finite outer) (target : List Nat)
    (scope : ∀ row ∈ outer, Scope.CountScoped target row.2)
    {types slots ids rows Δ env e β} (h : ScopedDerives types slots ids rows Δ env e β)
    (fresh : CountCapturesFixed outer env) :
    ScopedDerives (fun i => bounds outer (types i)) (fun i => bounds outer (slots i)) ids (CountAlgebra.compose outer rows)
      (Δ.map (constraint outer)) (env.map (mapCountBinding outer)) e (bounds outer β) := by
  induction h with
  | literal => cases ‹PrimLitExpr› <;> exact .literal
  | primBinOp => cases ‹PrimBinOp› <;> exact .primBinOp
  | nil => exact .nil
  | boolCtor hn => exact .boolCtor hn
  | cons _ _ hs ihh iht => exact .cons (ihh fresh) (iht fresh) (CountSubstitution.subtype outer hf hs)
  | varMono hv => exact .varMono (by simpa [mapCountBinding] using congrArg (Option.map (mapCountBinding outer)) hv)
  | @varRecursive Δ ids rows env i c caller hv u =>
      have captured := fresh _ (List.mem_of_getElem? hv)
      rw [← u.mapCounts_bounds outer hf target scope captured]
      exact .varRecursive (env := env.map (mapCountBinding outer)) (i := i) (c := c.mapCounts outer) (by
        simpa only [List.getElem?_map, mapCountBinding, Option.map_some] using
          congrArg (Option.map (mapCountBinding outer)) hv)
        (u.mapCounts outer hf target scope captured)
  | app _ _ hs ihf iha => exact .app (ihf fresh) (iha fresh) (CountSubstitution.subtype outer hf hs)
  | lambda hp _ ih =>
      exact .lambda (param_counts hp outer hf) (by simpa [mapCountBinding] using ih (count_captures_cons fresh))
  | letMono hp _ _ ihr ihb =>
      exact .letMono (binding_counts hp outer hf) (ihr fresh)
        (by simpa [mapCountBinding] using ihb (count_captures_cons fresh))
  | matchList _ hc hpat _ hsub ihscrut ihbranches =>
      apply ScopedDerives.matchList (ihscrut fresh) (hc.transport outer hf) hpat
      · intro i br hb
        have ht := ihbranches i br hb (count_captures_branch fresh)
        by_cases hcbr : br.1 = .named consCtorName 2
        · simpa [branchEnv, hcbr, mapCountBinding, bounds, List.map_append,
            RecursiveCountTransport.branchRefine_transport] using ht
        · simpa [branchEnv, hcbr, List.map_append, RecursiveCountTransport.branchRefine_transport] using ht
      · intro i br hb
        simpa only [List.map_append, RecursiveCountTransport.branchRefine_transport] using
          CountSubstitution.subtype outer hf (hsub i br hb)
  | matchBool _ hc hpat _ hsub ihscrut ihbranches =>
      exact .matchBool (ihscrut fresh) hc hpat
        (fun i br hb => ihbranches i br hb fresh)
        (fun i br hb => CountSubstitution.subtype outer hf (hsub i br hb))

/-- Identity-slot specialization of the canonical scoped transport. -/
theorem transportTypes (f : Nat → BoundsTy) (hf : ∀ i, (Synth.BoundsTy.toTy (f i)).IsLC)
    (target : List Nat) (scope : ∀ i, ScopedScheme.BoundsScoped target (f i))
    {types ids rows Δ env e β} (h : Derives types ids rows Δ env e β) (fresh : CapturesFixed f env) :
    Derives (fun i => mapFree f (types i)) ids rows Δ (env.map (mapBinding f hf)) e (mapFree f β) := by
  simpa only [mapFree] using transportScopedTypes f hf target scope h fresh

/-- Identity-slot specialization of the canonical scoped count transport. -/
theorem transportCounts (outer : Bindings) (hf : Finite outer) (target : List Nat)
    (scope : ∀ row ∈ outer, Scope.CountScoped target row.2)
    {types ids rows Δ env e β} (h : Derives types ids rows Δ env e β)
    (fresh : CountCapturesFixed outer env) :
    Derives (fun i => bounds outer (types i)) ids (CountAlgebra.compose outer rows)
      (Δ.map (constraint outer)) (env.map (mapCountBinding outer)) e (bounds outer β) := by
  simpa only [bounds] using transportScopedCounts outer hf target scope h fresh

#print axioms transportScopedTypes
#print axioms transportScopedCounts
#print axioms transportTypes
#print axioms transportCounts

end FHM.Bounds.RecursiveHMJudgement
