<!-- Handoff brief for the next agent. Written at the end of the "type annotations" session. -->

# Handoff: review the annotation work, then (1) scoped type variables, (2) the surface language

## 0. Workflow the user wants from you (in order)

1. **First, dispatch a read‑only review subagent** (`readonly: true`) to scrutinize everything created in the prior session — the threading machinery, the closedness restriction, and the two unfilled `@TODO`s (§2).
2. **If the review finds issues:** think them through, then **surface them to the user** with **concrete program examples** showing exactly where each issue crops up and what *unsound/incorrect* behavior it causes. Do **not** silently fix — present first.
3. **If the review is clean:** proceed to the work below, in this order (the user's chosen priority): **(A) scoped type variables / the `@TODO`s first** (§4) to get the core solid, then **(B) the surface language + its bridging lemmas** (§5). Confirm the design points in §6 with the user before starting large pieces.

## 1. Current state (all committed, green, sorry‑free, axiom‑clean)

Type annotations are a real, fully‑proven part of the core HM/Algorithm‑W system. Three layers agree:

- **AST** (`Experiments/FreshTypeSystem/Core.lean`): `Expr.lambda (paramAnn : Option Ty) (body)` and `Expr.letIn (ann : Option PolyTy) (bindingExpr body)`. `none` = inferred, `some _` = annotated. (Param annotations are monotypes; let annotations are full schemes.)
- **Declarative spec** `TypeOfHM` (Core): the `lambda` rule pins the parameter type to the annotation when present; the `letIn` rule makes the generalized scheme **be** the annotation `σ`, and its cofinite premise ("`boundExpr` types at every fresh opening of `σ`") rejects over‑general annotations *for free*. Both annotated rules currently require the annotation to be **closed** (`NoFreeVars`) — this is exactly what §4 removes.
- **Algorithm** `Infer`/`inferCore` (`InferW.lean`): lambda via `LamSeed`; let via the **threading** design `Infer.letInAnn` (skolemize the annotation, unify `rhs`'s type against it, **thread** the substitution outward so an annotation can refine outer fresh vars, escape‑check that no skolem is bound or leaks into the env).

Commits: `b086a6b` (lambda + declarative let) → `e2cdcf2` (threading + soundness) → `ac789e3` (orientation kernel) → `91e3626` (completeness) → (this session) dead‑code removal. `infer_complete`/`Infer.principal` were `lean_verify`‑checked: only `propext`/`Classical.choice`/`Quot.sound`, no `sorryAx`.

Build: `lake build Experiments.FreshTypeSystem.ConstraintTypeSystem`. Re‑run `lean_verify` (lean‑lsp MCP) on the top theorems as part of review.

**Note:** `PolyTy.AtLeastAsGeneralAs` and `polyTyAtLeastAsGeneral?` were created early (the abandoned "infer‑then‑check‑≥" design) and have now been **removed** as dead code — the final algorithm uses threading instead. Nothing references them.

## 2. What to review (fresh this session)

- **The threading machinery** (load‑bearing; lower risk since it's exercised by the axiom‑clean sound/complete proofs, but worth a sanity pass that the premises capture the intended semantics): `LamSeed`, `Infer.letInAnn` and its two escape premises (`hesc1` no skolem bound, `hesc2` no skolem leaks into env), `OUnify`/`OUnifyList` (a "left‑leaning" unification relation), `OUnify.skolem_escape`, `exists_skolem_unifier`, `skolem_no_env_leak`, `unifyCore_oUnify`.
- **The closedness restriction** (`NoFreeVars`) on annotations in `TypeOfHM.lambda`/`letIn`: is it sound and faithful *as it stands*? Probe with concrete programs (empty/zero‑param schemes, `bvar`s in annotations, nested lets, annotation interacting with generalization, shadowing). This matters because §4 removes it — the review should confirm the *current* behavior is correct so the relaxation is built on solid ground.
- **Helpers:** `Ty.isClosed`/`Ty.isClosed_iff`, `PolyTy.substFvar_eq_self_of_closed`.

## 3. Context / caveats from the prior session

- The `let` algorithm uses **threading** (skolemize‑and‑unify), NOT a generality‑ordering check. "Infer‑principal‑then‑check‑≥" was tried first and is **incomplete**: `λx. let f : Int = x in f` must infer `Int → Int` (the annotation *refines* the outer parameter `α := Int`), which a pure ≥‑check can't propagate. Key insight: the algorithm's fresh **skolems are exactly the cofinite "fresh opening" names** of the declarative `let` rule.
- Lean ergonomics: after `cases`/`induction`, index‑determined vars are inaccessible by name — use unstructured `cases h` then `case ctor h => expose_names` (or name binders in helper‑lemma signatures). `Subst.onTy S = Ty.substFvars S` definitionally, but `rw` needs a syntactic match (ascribe `have : S.onTy t = t := …`).
- Don't change the declarative `TypeOfHM` rules without flagging — they are the spec.

## 4. PRIORITY 1 — scoped type variables (remove the closedness `@TODO`s)

**The user wants scoped type variables in v1** (referencing a type variable anywhere inside a function whose signature introduced it, à la Elm / GHC `ScopedTypeVariables`; the closed‑only restriction is considered an unacceptable limitation). The two `@TODO`s on the `lambda`/`letIn` rules in Core mark where this lives.

**This is a genuine feature, not a one‑line `NoFreeVars` drop — design it before implementing (brainstorm with the user).** It spans:
1. **Spec/preservation (core):** define `Expr.substTyFvar (Z : Nat) (U : Ty) : Expr → Expr` that pushes `Ty.substFvar Z U` through the annotations *inside* terms (and recurses), and change `typ_subst_preservation` to conclude `… (e.substTyFvar Z U) …` instead of `… e …`, so type‑substitution stays consistent with a non‑closed annotation. Then drop the `NoFreeVars` conjunct from the `lambda`/`letIn` rules and re‑prove. *(This is the part the `@TODO` comments literally describe.)*
2. **Algorithm (the subtle part):** a scoped type variable resolves to an **in‑scope rigid skolem** (e.g. the `Ys` the `letIn` body is already checked under). So an annotation may now contain *free fvars that must be treated rigidly* (not unified away) — otherwise unsound. Today `LamSeed.some` requires `Ty.isClosed`; relaxing it needs a clear story for which annotation fvars are rigid vs flexible and how `inferCore` keeps the rigid ones fixed (the escape machinery already protects skolems — leverage it). **Get this right or it's unsound; have the review/the user pressure‑test the design with examples first.**
3. **Surface (later, with §5):** the resolver must *bind* type‑variable names to the enclosing signature's skolems so `a` inside the body refers to the right one. The core mechanism (1)+(2) can land and be tested first with hand‑built core terms (annotations referencing skolem fvars); the surface binding comes with the surface language.

Honest sizing: substantial, and the algorithm part (2) is where soundness can break — treat it carefully.

(Also still deferred, confirm still out of scope: a standalone expression‑level **ascription** node `(e : T)`; the **intrinsically‑typed elaboration** pass.)

## 5. PRIORITY 2 — the surface language + bridging lemmas

Design settled on earlier in the thread:
- Surface AST = **named** (string variables); core stays de Bruijn. No "surface‑surface" layer — the named layer *is* the surface language.
- Pipeline: `text → parse → surface AST (named, with sugar) → desugar (named→named, minimal kernel, NO index arithmetic) → resolve names (named → de Bruijn core; CAN FAIL with "unbound variable") → infer`.
- **Confine ALL de Bruijn index bookkeeping to the single name‑resolution pass** (do sugar in the named world). This keeps proofs clean.
- Surface annotations carry **named type variables** → a small **type‑variable resolution** pass (named type vars → core `Ty` `bvar`/`fvar`), which is also where scoped type variables get bound (§4.3).

**Bridging / equivalence lemmas to prove** (the user wants these verified — the surface lang shouldn't differ much from core, so this is expected to be tractable):
1. **Resolver soundness vs `WellScopedUnder`** (the main, cheap bridge): resolving a surface term well‑scoped under a naming context `Γ` yields a core term satisfying `Expr.WellScopedUnder Γ.length`. Plugs directly into the existing `WellScopedUnder` predicate.
2. **Desugaring preservation**: the named→named desugaring preserves meaning/typing (sugar is just sugar).
3. **Annotation‑resolution well‑formedness**: resolved annotation types are valid core `Ty`/`PolyTy` (and, post‑§4, correctly classify scoped type vars as rigid).
4. **Surface‑typing → core‑typing preservation**: if a surface‑level typing/elaboration relation is defined, a well‑typed surface program translates to one accepted by `TypeOfHM`/`infer`.

## 6. Design points to confirm with the user (surface early)

- **Scoped type variables (§4):** agree the representation (annotations referencing in‑scope skolem fvars) and the rigid‑vs‑flexible story in the algorithm *before* implementing — this is where soundness is at risk.
- Confirm the **ascription node** and **intrinsic‑typing pass** remain out of scope for now.
- (Resolved earlier: `AtLeastAsGeneralAs` removed; `@TODO`s before the surface language; bridging lemmas to be proven.)
