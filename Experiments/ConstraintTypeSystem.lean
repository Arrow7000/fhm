import Experiments.FreshTypeSystem

/-! # Constraint-based Hindley–Milner inference

An alternative to the Algorithm-W development in `Experiments.FreshTypeSystem`
(approach A). The hypothesis under test: a **constraint-based** presentation
(Wand / Pottier–Rémy, *The Essence of ML Type Inference*) is cleaner — fewer
naked substitutions and fresh-`Nat` frontiers leaking through the *inference*
layer, because all of that is confined to the (already-proven) unification
module, and generation is a substitution-free, syntax-directed relation.

We **reuse** the shared foundation from `FreshTypeSystem` (imported above):

* the declarative relation `TypeOfHM` and its metatheory,
* the substitution algebra `Subst`/`Subst.onTy`/`onPolyTy`/`onEnv`/`onCtx`,
* the unification kernel `UnifyRel` / `IsMGU` / `UnifyRel.isMGU` /
  `UnifyRel.complete` and the executable `unify` (for the solver later).

We do **not** use approach A's `Infer` relation or its frontier machinery.

## Plan

1. `Constraint` — a tiny syntax: `⊤`, type equality, conjunction, and a scheme
   *instance* constraint. **No substitutions, no fresh-var counter.**
2. `Sat S C` — when substitution `S` satisfies `C` (recursion on `C`; the only
   place `Subst` appears).
3. `Gen ctx e τ C` — constraint generation: syntax-directed, **substitution-free**,
   relating an expression (at an expected type `τ`) to the constraint whose
   solutions are exactly its typings.
4. `Gen.sound` — every solution of a generated constraint is a real `TypeOfHM`
   typing. (Completeness, the solver, and the `let`/`ctor`/`match` extensions
   come next.)

This first cut covers the core `primLit`/`pair`/`lambda`/`app`/`var` fragment;
`let`-generalisation needs constraint *schemes* and is designed separately. -/


/-- Typing constraints. Variables are the same `Ty.fvar` unification variables
    used by the unification kernel; there are deliberately no substitutions and
    no fresh-variable binders here — generation chooses the fresh names and
    `Sat` interprets equality/instance via the shared `Subst` machinery. -/
inductive Constraint
  /-- `⊤`, trivially satisfied. -/
  | tru
  /-- `τ₁ ≐ τ₂`: the two monotypes must be made equal. -/
  | eq (τ₁ τ₂ : Ty)
  /-- `C₁ ∧ C₂`. -/
  | conj (c₁ c₂ : Constraint)
  /-- `M ⪰ τ`: `τ` must be a (monomorphic) instance of scheme `M`. -/
  | inst (M : PolyTy) (τ : Ty)

/-- When substitution `S` satisfies constraint `C`. This is the *only* place a
    `Subst` appears in the constraint layer. -/
def Sat (S : Subst) : Constraint → Prop
  | .tru        => True
  | .eq τ₁ τ₂   => S.onTy τ₁ = S.onTy τ₂
  | .conj c₁ c₂ => Sat S c₁ ∧ Sat S c₂
  | .inst M τ   => ∃ Vs : List Ty, Ty.AreLC M.paramCount Vs ∧ (S.onPolyTy M).openWith Vs = S.onTy τ

/-- Constraint generation, à la Pottier–Rémy: `Gen ctx e τ C` reads "expression
    `e`, checked against expected type `τ` in context `ctx`, generates
    constraint `C`." Syntax-directed and **substitution-free**: each rule only
    emits equalities and instance constraints over fresh `.fvar`s. -/
inductive Gen : Ctx → Expr → Ty → Constraint → Prop
  | primLitUnit {ctx τ} :
    Gen ctx (.primLit .unit) τ (.eq τ (.prim .unit))
  | primLitInt {ctx τ n} :
    Gen ctx (.primLit (.int n)) τ (.eq τ (.prim .int))
  | primLitNat {ctx τ n} :
    Gen ctx (.primLit (.nat n)) τ (.eq τ (.prim .nat))
  | primLitBool {ctx τ b} :
    Gen ctx (.primLit (.bool b)) τ (.eq τ (.prim .bool))
  | primLitStr {ctx τ s} :
    Gen ctx (.primLit (.str s)) τ (.eq τ (.prim .str))
  | pair {ctx a b τ α β Ca Cb} :
    Gen ctx a (.fvar α) Ca →
    Gen ctx b (.fvar β) Cb →
    Gen ctx (.pair a b) τ (.conj (.eq τ (.pair (.fvar α) (.fvar β))) (.conj Ca Cb))
  | lambda {ctx body τ α β Cbody} :
    Gen { ctx with env := PolyTy.mkTrivial (.fvar α) :: ctx.env } body (.fvar β) Cbody →
    Gen ctx (.lambda body) τ (.conj (.eq τ (.arrow (.fvar α) (.fvar β))) Cbody)
  | app {ctx f arg τ α Cf Carg} :
    Gen ctx f (.arrow (.fvar α) τ) Cf →
    Gen ctx arg (.fvar α) Carg →
    Gen ctx (.app f arg) τ (.conj Cf Carg)
  | var {ctx i τ M} :
    ctx.env[i]? = some M →
    Gen ctx (.var i) τ (.inst M τ)
  | ctor {ctx name τ ctorDef} :
    LookupList.get? ctx.ctors name = some ctorDef →
    Gen ctx (.ctor name) τ (.inst ctorDef.toTy τ)

/-- **Soundness of generation.** Any locally-closed substitution satisfying a
    generated constraint yields a declarative `TypeOfHM` typing. Note: the
    returned/expected type `τ` is read off as `S.onTy τ`, and only the *context*
    is substituted — no separate "apply `S` again" step. -/
theorem Gen.sound {ctx : Ctx} {e : Expr} {τ : Ty} {C : Constraint}
    (h : Gen ctx e τ C) :
    CtxWF ctx → ∀ {S : Subst}, (∀ p ∈ S, p.2.IsLC) → Sat S C →
    TypeOfHM (S.onCtx ctx) e (S.onTy τ) := by
  induction h with
  | primLitUnit => intro _ S _ hsat; simp only [Sat, Subst.onTy_prim] at hsat; rw [hsat]; exact .primLitUnit
  | primLitInt  => intro _ S _ hsat; simp only [Sat, Subst.onTy_prim] at hsat; rw [hsat]; exact .primLitInt
  | primLitNat  => intro _ S _ hsat; simp only [Sat, Subst.onTy_prim] at hsat; rw [hsat]; exact .primLitNat
  | primLitBool => intro _ S _ hsat; simp only [Sat, Subst.onTy_prim] at hsat; rw [hsat]; exact .primLitBool
  | primLitStr  => intro _ S _ hsat; simp only [Sat, Subst.onTy_prim] at hsat; rw [hsat]; exact .primLitStr
  | pair _ _ iha ihb =>
    intro hwf S hS hsat
    simp only [Sat] at hsat
    obtain ⟨heq, hsa, hsb⟩ := hsat
    have hta := iha hwf hS hsa
    have htb := ihb hwf hS hsb
    simp only [Subst.onTy_pair] at heq
    rw [heq]
    exact .pair hta htb
  | lambda _ ih =>
    intro hwf S hS hsat
    simp only [Sat] at hsat
    obtain ⟨heq, hsbody⟩ := hsat
    simp only [Subst.onTy_arrow] at heq
    rw [heq]
    refine TypeOfHM.lambda (Subst.onTy_lc hS ContainsBvarsUpTo.fvar) rfl ?_
    refine ih ?_ hS hsbody
    intro M hM
    rcases List.mem_cons.mp hM with rfl | hM
    · exact ContainsBvarsUpTo.fvar
    · exact hwf M hM
  | app _ _ ihf iharg =>
    intro hwf S hS hsat
    simp only [Sat] at hsat
    obtain ⟨hsf, hsa⟩ := hsat
    have htf := ihf hwf hS hsf
    have hta := iharg hwf hS hsa
    simp only [Subst.onTy_arrow] at htf
    exact .app htf hta
  | @var ctxv iv τv Mv hlookup =>
    intro hwf S hS hsat
    simp only [Sat] at hsat
    obtain ⟨Vs, hVsLC, hVseq⟩ := hsat
    refine TypeOfHM.var (polyTy := S.onPolyTy Mv) ?_ hVsLC.2 ?_
    · simp only [Subst.onCtx, Subst.onEnv, List.getElem?_map, hlookup, Option.map_some]
    · rw [← hVseq]
      exact InstantiatesBy.openWith (Subst.onPolyTy_wf hS (hwf Mv (List.mem_of_getElem? hlookup)))
        (le_of_eq hVsLC.1.symm)
  | @ctor ctxv namev τv ctorDefv hlookup =>
    intro _ S hS hsat
    simp only [Sat] at hsat
    obtain ⟨Vs, hVsLC, hVseq⟩ := hsat
    refine TypeOfHM.ctor (ctor := ctorDefv) ?_ hVsLC.2 ?_
    · simpa only [Subst.onCtx] using hlookup
    · have hbody : (S.onPolyTy ctorDefv.toTy).body = ctorDefv.toTy.body := by
        simp only [Subst.onPolyTy]
        exact Ty.substFvars_eq_self_of_no_key
          (fun p _ => NoFreeVars.not_mem_freeVars (Ctor.toTy_body_noFreeVars ctorDefv) p.1)
      rw [← hVseq, ← hbody]
      exact InstantiatesBy.openWith (Subst.onPolyTy_wf hS (Ctor.toTy_wf ctorDefv))
        (le_of_eq hVsLC.1.symm)
