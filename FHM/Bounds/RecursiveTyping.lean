import FHM.Bounds.RecursiveContract
import FHM.Bounds.ScopedTyping
import FHM.Bounds.ListBranches

/-! # Scoped bounds typing with explicit recursive contract assumptions

Count-polymorphic recursive variables have fixed HM monotypes. A group rule
requires all RHSs, at every finite scoped count instantiation, to satisfy their
carried annotations and their declared contracts under the simultaneous group
assumptions. Merely decoding those assumptions never proves this premise.

The initial group body retains fixed HM monotypes. `RecursiveGroup` supplies an
optional executable introduction; exit HM generalization and runtime length
soundness are separate.
-/

namespace FHM.Bounds.RecursiveTyping

open CountSubstitution RecursiveContract

inductive Binding where
  | mono (bounds : BoundsTy)
  | recursive (contract : Declared)

def BindingScoped (ids : List Nat) : Binding → Prop
  | .mono β => ScopedScheme.BoundsScoped ids β
  | .recursive c => ∀ i ∈ c.counts.captures, i ∈ ids

def Independent (contracts : List Declared) : Prop :=
  (contracts.flatMap fun c => c.counts.quantified).Nodup ∧
    ∀ c ∈ contracts, ∀ d ∈ contracts, ∀ i ∈ c.counts.captures, i ∉ d.counts.quantified

def independentBool (contracts : List Declared) : Bool :=
  let quantified := contracts.flatMap fun c => c.counts.quantified
  decide quantified.Nodup &&
    contracts.all (fun c => c.counts.captures.all (fun i => !quantified.contains i))

theorem independentBool_sound {contracts : List Declared}
    (h : independentBool contracts = true) : Independent contracts := by
  simp only [independentBool, Bool.and_eq_true, decide_eq_true_eq] at h
  refine ⟨h.1, ?_⟩
  intro c hc d hd i hi hq
  have absent : i ∉ contracts.flatMap (fun c => c.counts.quantified) := by
    simpa [List.contains_iff_mem] using
      List.all_eq_true.mp (List.all_eq_true.mp h.2 c hc) i hi
  exact absent (List.mem_flatMap.mpr ⟨d, hd, hq⟩)

/-- Only the constructors whose refinements and binder layout are justified
    by the List semantics are admitted. Coverage is a separate premise. -/
def ListPattern (p : MatchPattern) : Prop :=
  p = .wildcard ∨ p = .named nilCtorName 0 ∨ p = .named consCtorName 2

instance (p : MatchPattern) : Decidable (ListPattern p) :=
  inferInstanceAs (Decidable (p = .wildcard ∨ p = .named nilCtorName 0 ∨ p = .named consCtorName 2))

def branchRefine (p : MatchPattern) (lo hi : Count) : List Constraint :=
  if p = .named nilCtorName 0 then nilRefine lo
  else if p = .named consCtorName 2 then consRefine hi else []

/-- Core opens Cons contents head first, tail second. -/
def branchEnv (p : MatchPattern) (lo hi : Count) (elem : BoundsTy)
    (env : List Binding) : List Binding :=
  if p = .named consCtorName 2 then
    .mono elem :: .mono (.list (.pred lo) (.pred hi) elem) :: env
  else env

inductive Derives : List Nat → Bindings → List Constraint →
    List Binding → Expr → BoundsTy → Prop where
  | literal {env p} : Derives ids rows Δ env (.primLit p) (boundInfoOfPrimLit p)
  | primBinOp {env op} : Derives ids rows Δ env (.primBinOp op) (Typed.primOpBounds op)
  | nil {env elem} : Derives ids rows Δ env (.ctor nilCtorName) (.list (.lit 0) (.lit 0) elem)
  | cons {env h t head elem lo hi} :
      Derives ids rows Δ env h head → Derives ids rows Δ env t (.list lo hi elem) →
      SemanticSub Δ head elem →
      Derives ids rows Δ env (.app (.app (.ctor consCtorName) h) t)
        (.list (.add lo (.lit 1)) (.add hi (.lit 1)) elem)
  | varMono {env i β} : env[i]? = some (.mono β) → Derives ids rows Δ env (.var i) β
  | varRecursive {env i c args caller} : env[i]? = some (.recursive c) →
      (inst : ScopedScheme.Instance c.counts args caller) → inst.Usable Δ →
      Derives ids rows Δ env (.var i) inst.bounds
  | app {env f arg domain actual result} :
      Derives ids rows Δ env f (.arrow domain result) → Derives ids rows Δ env arg actual →
      SemanticSub Δ actual domain → Derives ids rows Δ env (.app f arg) result
  | lambda {env ann body param result} :
      InterpretedAnnotation.ParamOK ids rows Δ ann param →
      Derives ids rows Δ (.mono param :: env) body result →
      Derives ids rows Δ env (.lambda ann body) (.arrow param result)
  | letMono {env ann rhs body actual result} :
      InterpretedAnnotation.BindingOK ids rows Δ ann actual →
      Derives ids rows Δ env rhs actual → Derives ids rows Δ (.mono actual :: env) body result →
      Derives ids rows Δ env (.letIn ann rhs body) result
  | matchList {env scrut branches lo hi elem result}
      {actuals : Nat → BoundsTy} :
      Derives ids rows Δ env scrut (.list lo hi elem) →
      ListBranches.Covers Δ ⟨lo, hi⟩ branches →
      (∀ br ∈ branches, ListPattern br.1) →
      (∀ i br, branches[i]? = some br → Derives ids rows (Δ ++ branchRefine br.1 lo hi)
        (branchEnv br.1 lo hi elem env) br.2 (actuals i)) →
      (∀ i br, branches[i]? = some br →
        SemanticSub (Δ ++ branchRefine br.1 lo hi) (actuals i) result) →
      Derives ids rows Δ env (.match_ scrut branches) result
  | letRec {env : List Binding} {contracts : List Declared}
      {anns : List (Option PolyTy)} {rhss : List Expr} {body result}
      {actuals : Nat → List Count → BoundsTy} :
      anns.length = contracts.length → rhss.length = contracts.length →
      Independent contracts →
      (∀ c ∈ contracts, ∀ b ∈ env, BindingScoped c.counts.captures b) →
      (∀ i c rhs ann, contracts[i]? = some c → rhss[i]? = some rhs → anns[i]? = some ann →
        ∀ args caller (inst : ScopedScheme.Instance c.counts args caller),
        Derives (c.counts.quantified ++ c.counts.captures) (c.counts.quantified.zip args)
          inst.premises (contracts.map Binding.recursive ++ env) rhs (actuals i args)) →
      (∀ i c rhs ann, contracts[i]? = some c → rhss[i]? = some rhs → anns[i]? = some ann →
        ∀ args caller (inst : ScopedScheme.Instance c.counts args caller),
        InterpretedAnnotation.BindingOK (c.counts.quantified ++ c.counts.captures)
          (c.counts.quantified.zip args) inst.premises ann (actuals i args)) →
      (∀ i c rhs ann, contracts[i]? = some c → rhss[i]? = some rhs → anns[i]? = some ann →
        ∀ args caller (inst : ScopedScheme.Instance c.counts args caller),
        SemanticSub inst.premises (actuals i args) inst.bounds) →
      Derives ids rows Δ (contracts.map Binding.recursive ++ env) body result →
      Derives ids rows Δ env (.letRec anns rhss body) result

/-- Even the declarative recursive-variable rule permits only count
    polymorphism. All its uses have the same HM spine, not merely those passing
    the executable found-payload comparison. -/
theorem recursive_var_shape {ids rows Δ env i c β}
    (hv : env[i]? = some (.recursive c)) (h : Derives ids rows Δ env (.var i) β) :
    Synth.BoundsTy.toTy β = c.hm := by
  cases h with
  | varMono hm => rw [hv] at hm; cases hm
  | varRecursive hr inst _ =>
      rw [hv] at hr
      cases hr
      exact inst.shape.trans c.shape

/-- The old annotation-aware fragment embeds without adding any recursive
    assumption or weakening an annotation obligation. -/
theorem ofScoped {ids rows Δ env e β} (h : ScopedTyping.Derives ids rows Δ env e β) :
    Derives ids rows Δ (env.map Binding.mono) e β := by
  induction h with
  | literal => exact .literal
  | primBinOp => exact .primBinOp
  | nil => exact .nil
  | cons _ _ hs ihh iht => exact .cons ihh iht hs
  | var hv => exact .varMono (by simpa using congrArg (Option.map Binding.mono) hv)
  | app _ _ hs ihh iht => exact .app ihh iht hs
  | lambda hp _ ih => exact .lambda hp ih
  | letMono hp _ _ ihr ihb => exact .letMono hp ihr ihb

private theorem param_assuming {ids rows Δ Δ' ann β}
    (h : InterpretedAnnotation.ParamOK ids rows Δ ann β)
    (hp : (⟨Δ', Δ⟩ : ForallProblem).Valid) : InterpretedAnnotation.ParamOK ids rows Δ' ann β := by
  cases ann with
  | none => trivial
  | some τ => exact InterpretedAnnotation.assuming h hp

private theorem binding_assuming {ids rows Δ Δ' ann β}
    (h : InterpretedAnnotation.BindingOK ids rows Δ ann β)
    (hp : (⟨Δ', Δ⟩ : ForallProblem).Valid) : InterpretedAnnotation.BindingOK ids rows Δ' ann β := by
  cases ann with
  | none => trivial
  | some σ => exact ⟨h.1, InterpretedAnnotation.assuming h.2 hp⟩

theorem assuming_append {Δ Δ' Γ : List Constraint}
    (hp : (⟨Δ', Δ⟩ : ForallProblem).Valid) :
    (⟨Δ' ++ Γ, Δ ++ Γ⟩ : ForallProblem).Valid := by
  intro σ h c hc
  rcases List.mem_append.mp hc with hc | hc
  · exact hp σ (fun d hd => h d (List.mem_append_left Γ hd)) c hc
  · exact h c (List.mem_append_right Δ' hc)

/-- Universal group RHS obligations use each contract's own instantiated
    premises, not unproved assumptions appended by the caller. -/
theorem assuming {ids rows Δ Δ' env e β} (h : Derives ids rows Δ env e β)
    (hp : (⟨Δ', Δ⟩ : ForallProblem).Valid) : Derives ids rows Δ' env e β := by
  induction h generalizing Δ' with
  | literal => exact .literal
  | primBinOp => exact .primBinOp
  | nil => exact .nil
  | cons _ _ hs ihh iht => exact .cons (ihh hp) (iht hp) (hs.assuming hp)
  | varMono hv => exact .varMono hv
  | varRecursive hv inst hu =>
      exact .varRecursive hv inst (by
        intro σ hΔ goal hgoal
        apply hu σ (fun c hc => hp σ hΔ c hc) goal hgoal)
  | app _ _ hs ihh iht => exact .app (ihh hp) (iht hp) (hs.assuming hp)
  | lambda hparam _ ih => exact .lambda (param_assuming hparam hp) (ih hp)
  | letMono hbind _ _ ihr ihb => exact .letMono (binding_assuming hbind hp) (ihr hp) (ihb hp)
  | matchList _ hc hpat _ hsub ihscrut ihbranches =>
      exact .matchList (ihscrut hp) (hc.assuming hp) hpat
        (fun i br hb => ihbranches i br hb (assuming_append hp))
        (fun i br hb => (hsub i br hb).assuming (assuming_append hp))
  | letRec hanns hrhss hIndependent hcapture hall hAnn hSub _ _ ihbody =>
      exact .letRec hanns hrhss hIndependent hcapture hall hAnn hSub (ihbody hp)

#print axioms ofScoped
#print axioms assuming
#print axioms recursive_var_shape
#print axioms independentBool_sound

end FHM.Bounds.RecursiveTyping
