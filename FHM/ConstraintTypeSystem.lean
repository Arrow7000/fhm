import FHM.InferW

/-! # Constraint-based Hindley–Milner inference

An alternative to the Algorithm-W development in `FHM.InferW`
(approach A), testing whether a **constraint-based** presentation (Wand /
Pottier–Rémy) keeps the *inference* layer free of the naked substitutions and
fresh-variable frontiers that pervade W. We reuse the shared foundation +
unification kernel from `FHM` (the declarative `TypeOfElabHM`, its
metatheory, `Subst`/`UnifyRel`/`IsMGU`, the executable `unify`).

## Schemes with guards

`let`-generalisation forces the move to **constraint schemes** `∀ᾱ[C].τ`: a
scheme records the bound type variables `ᾱ`, a *guard* constraint `C`, and a
body type `τ`. Each *use* of the bound variable re-instantiates the guard with
fresh types, so an over-generalised variable stays sound (the guard travels with
the scheme). We use **named** bound variables (`Ty.fvar` names listed in
`CScheme.vars`) so instantiation is a plain substitution (no de Bruijn shifting).

`Sat` threads the substitution as its first argument and recurses structurally
on the constraint — instantiating a scheme just extends the substitution on the
bound names, so the guard is checked under the extended substitution.

This file is built incrementally. Increment 1 (here): datatypes, `Sat`, the
generation env, and the guard-free fragment (`primLit`/`pair`/`lambda`/`app`/
`var`) with soundness. `ctor` and the headline `let` rule + its cofinite
soundness bridge are added next. -/


mutual

/-- Typing constraints. Variables are the unification variables `Ty.fvar`. -/
inductive Constraint
  /-- `⊤`. -/
  | tru
  /-- `τ₁ ≐ τ₂`. -/
  | eq (τ₁ τ₂ : Ty)
  /-- `C₁ ∧ C₂`. -/
  | conj (c₁ c₂ : Constraint)
  /-- `cs ⪰ τ`: `τ` is an instance of constraint scheme `cs`. -/
  | inst (cs : CScheme) (τ : Ty)
  /-- `M ⪰ τ` for a *closed* (constructor) `PolyTy` scheme `M`. Constructor
      schemes are closed and de Bruijn, so they bypass the named-variable
      `CScheme` machinery and instantiate directly via `openWith`. -/
  | instC (M : PolyTy) (τ : Ty)

/-- A constraint scheme `∀ vars [guard]. body`, with named bound variables. -/
inductive CScheme
  | mk (vars : List Nat) (guard : Constraint) (body : Ty)

end

/-- The bound (generalised) variable names of a scheme. -/
def CScheme.vars : CScheme → List Nat | .mk v _ _ => v
/-- The guard constraint of a scheme. -/
def CScheme.guard : CScheme → Constraint | .mk _ g _ => g
/-- The body type of a scheme. -/
def CScheme.body : CScheme → Ty | .mk _ _ b => b

/-- A monomorphic scheme `∀ [] [⊤]. τ` (no generalisation, trivial guard). -/
def CScheme.mono (τ : Ty) : CScheme := .mk [] .tru τ

/-- When substitution `S` satisfies constraint `C`. The substitution is threaded
    (it varies in the `inst` case); recursion is structural on the constraint.
    Instantiating a scheme picks locally-closed witnesses `Vs` for its bound
    names, extends `S` to map them, and checks the guard + that the body matches
    the target under that extension. -/
def Sat : Subst → Constraint → Prop
  | _, .tru        => True
  | S, .eq τ₁ τ₂   => S.onTy τ₁ = S.onTy τ₂
  | S, .conj c₁ c₂ => Sat S c₁ ∧ Sat S c₂
  | S, .inst (.mk vars guard body) τ =>
      ∃ Vs : List Ty, Ty.AreLC vars.length Vs ∧
        Sat (vars.zip Vs ++ S) guard ∧
        Subst.onTy (vars.zip Vs ++ S) body = S.onTy τ
  | S, .instC M τ =>
      ∃ Vs : List Ty, Ty.AreLC M.paramCount Vs ∧ (S.onPolyTy M).openWith Vs = S.onTy τ

/-- Generation context: like `Ctx` but the value env maps to constraint
    schemes (lambda/`let`/pattern bindings), enabling guarded `let` schemes. -/
structure GenCtx where
  env : List CScheme
  ctors : CtorEnv

/-- A scheme is well-formed.

    @TODO: this is temporarily restricted to *monomorphic* schemes
    (`cs.vars = []`), because the only schemes in the env so far come from
    `lambda` (which binds a monotype). When the `let` rule lands it will
    introduce genuinely polymorphic, guarded schemes (`cs.vars ≠ []`), and this
    predicate must be generalised — e.g. "the guard/body only mention bound vars
    in `cs.vars` plus env-fixed vars, and bound vars are distinct/fresh." -/
def CScheme.WF (cs : CScheme) : Prop := cs.vars = [] ∧ cs.body.IsLC

/-- All schemes in the generation context's env are well-formed. -/
def GenCtxWF (ctx : GenCtx) : Prop := ∀ cs ∈ ctx.env, cs.WF

/-- The declarative `PolyTy` that a scheme grounds to under solution `S`:
    close the (substituted) body over the bound names. For monomorphic schemes
    this is just `mkTrivial (S.onTy body)`. -/
def CScheme.ground (S : Subst) : CScheme → PolyTy
  | .mk [] _ body   => PolyTy.mkTrivial (S.onTy body)
  | .mk vars _ body => ⟨vars.length, (S.onTy body).closeOver vars⟩

/-- Ground a whole generation context to a declarative `Ctx` under `S`. -/
def GenCtx.toCtx (S : Subst) (ctx : GenCtx) : Ctx :=
  ⟨ctx.env.map (CScheme.ground S), ctx.ctors⟩

mutual

/-- Free unification variables occurring in a constraint. -/
def Constraint.freeVars : Constraint → List Nat
  | .tru        => []
  | .eq τ₁ τ₂   => (τ₁.freeVars ++ τ₂.freeVars).dedup
  | .conj c₁ c₂ => (Constraint.freeVars c₁ ++ Constraint.freeVars c₂).dedup
  | .inst cs τ  => (CScheme.freeVars cs ++ τ.freeVars).dedup
  | .instC M τ  => (M.body.freeVars ++ τ.freeVars).dedup

/-- Free unification variables of a scheme: those of the guard/body, minus the
    bound (generalised) names. -/
def CScheme.freeVars : CScheme → List Nat
  | .mk vars guard body =>
      ((Constraint.freeVars guard ++ body.freeVars).dedup).filter (fun x => !vars.contains x)

end

/-- Free unification variables fixed by a generation context (union over its env
    schemes). The `let` rule generalises exactly the young vars *not* in here. -/
def GenCtx.freeVars (ctx : GenCtx) : List Nat :=
  (ctx.env.map CScheme.freeVars).flatten.dedup

/-- Constraint generation, à la Pottier–Rémy: substitution-free and
    frontier-free (fresh vars are existentially chosen). -/
inductive Gen : GenCtx → Expr → Ty → Constraint → Prop
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
  -- Constraint generation currently handles only *unannotated* lambdas (the
  -- param type is a fresh monotype `α`). Annotated lambdas are out of scope for
  -- this guard-free fragment.
  | lambda {ctx body τ α β Cbody} :
    Gen { ctx with env := CScheme.mono (.fvar α) :: ctx.env } body (.fvar β) Cbody →
    Gen ctx (.lambda none body) τ (.conj (.eq τ (.arrow (.fvar α) (.fvar β))) Cbody)
  | app {ctx f arg τ α Cf Carg} :
    Gen ctx f (.arrow (.fvar α) τ) Cf →
    Gen ctx arg (.fvar α) Carg →
    Gen ctx (.app f arg) τ (.conj Cf Carg)
  | var {ctx i τ cs} :
    ctx.env[i]? = some cs →
    Gen ctx (.var i) τ (.inst cs τ)
  | ctor {ctx name τ ctorDef} :
    LookupList.get? ctx.ctors name = some ctorDef →
    Gen ctx (.ctor name) τ (.instC ctorDef.toTy τ)

/-- **Soundness of generation (guard-free fragment).** Any locally-closed
    substitution satisfying a generated constraint yields a declarative
    `TypeOfElabHM` typing under the grounded context. -/
theorem Gen.sound {ctx : GenCtx} {e : Expr} {τ : Ty} {C : Constraint}
    (h : Gen ctx e τ C) :
    GenCtxWF ctx → ∀ {S : Subst}, (∀ p ∈ S, p.2.IsLC) → Sat S C →
    TypeOfElabHM (ctx.toCtx S) e (S.onTy τ) := by
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
    refine TypeOfElabHM.lambda (Subst.onTy_lc hS ContainsBvarsUpTo.fvar)
      (fun T hT => absurd hT (by simp)) rfl ?_
    refine ih ?_ hS hsbody
    intro cs hcs
    rcases List.mem_cons.mp hcs with rfl | hcs
    · exact ⟨rfl, ContainsBvarsUpTo.fvar⟩
    · exact hwf cs hcs
  | app _ _ ihf iharg =>
    intro hwf S hS hsat
    simp only [Sat] at hsat
    obtain ⟨hsf, hsa⟩ := hsat
    have htf := ihf hwf hS hsf
    have hta := iharg hwf hS hsa
    simp only [Subst.onTy_arrow] at htf
    exact .app htf hta
  | @var ctxv iv τv csv hlookup =>
    intro hwf S hS hsat
    obtain ⟨hvars, hbodyLC⟩ := hwf csv (List.mem_of_getElem? hlookup)
    obtain ⟨vars, guard, body⟩ := csv
    simp only [CScheme.vars] at hvars; subst hvars
    simp only [CScheme.body] at hbodyLC
    simp only [Sat] at hsat
    obtain ⟨Vs, _, _, hbodyeq⟩ := hsat
    -- `[].zip Vs ++ S` is definitionally `S`
    have hbeq : S.onTy body = S.onTy τv := hbodyeq
    refine TypeOfElabHM.var (polyTy := CScheme.ground S (.mk [] guard body)) (tyArgs := []) ?_ (by simp) ?_
    · show (ctxv.toCtx S).env[iv]? = _
      simp only [GenCtx.toCtx, List.getElem?_map, hlookup, Option.map_some]
    · simp only [CScheme.ground, PolyTy.mkTrivial]
      rw [← hbeq]
      exact InstantiatesBy.refl_of_closed (Subst.onTy_lc hS hbodyLC)
  | @ctor ctxv namev τv ctorDefv hlookup =>
    intro _ S hS hsat
    simp only [Sat] at hsat
    obtain ⟨Vs, hVsLC, hVseq⟩ := hsat
    refine TypeOfElabHM.ctor (ctor := ctorDefv) ?_ hVsLC.2 ?_
    · simpa only [GenCtx.toCtx] using hlookup
    · have hbody : (S.onPolyTy ctorDefv.toTy).body = ctorDefv.toTy.body := by
        simp only [Subst.onPolyTy]
        exact Ty.substFvars_eq_self_of_no_key
          (fun p _ => NoFreeVars.not_mem_freeVars (Ctor.toTy_body_noFreeVars ctorDefv) p.1)
      rw [← hVseq, ← hbody]
      exact InstantiatesBy.openWith (Subst.onPolyTy_wf hS (Ctor.toTy_wf ctorDefv))
        (le_of_eq hVsLC.1.symm)
