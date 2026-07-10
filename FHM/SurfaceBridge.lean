import FHM.Core
import FHM.SurfaceLang
import FHM.Decls
import FHM.PatComp
import FHM.InferW

/-! # The surface → Core bridge (item-0 skeleton)

This module is the **front end**: it lowers `Surface.Expr`/`Surface.Ty`/data
declarations into Core, and states the campaign's headline payoff — *a well-typed
surface program elaborates to a Core program that is type-safe and never gets
stuck*.

**Status:** `lowerTy` and `lower` are **real** (`#guard`-tested). `Lowers`,
`SurfaceCovers`, and `PatternWF` are **real** inductive definitions below. Proof
bodies remain `sorry` (delegable to Grok 4.5 xhigh).

## Design decisions this skeleton bakes in (settled with Aron)

1. **Spec/impl separation, `Infer`-style.** `Lowers` is the declarative
   relation (the spec); `lower` is the executable function. Bridged by
   soundness (`lower s = some c → Lowers … s c`) and completeness (a valid
   lowering exists ⟹ `lower` produces one). **`Lowers` is kept NON-deterministic
   at the `match` case** (many behaviourally-equivalent Core renderings of one
   surface match); the deterministic parts (names, sugar) stay one-to-one. The
   `lower`-soundness obligation for the match case *is* the already-proven
   compilation-correctness theorem (`PatComp.lowerMatch_adequate_of_typed`).

2. **The payoff is a TWO-hop composition, and the object that runs is `eOut`,
   not `lower s`.** `typecheck`/`Lowers` speak the DECLARATIVE `TypeOfHM`, but
   the dynamics (`Step`, `progress`, `type_safety`) are stated on the ELABORATED
   `TypeOfElabHM` over the decorated term `eOut` produced by `infer`. So the
   runtime term is `eOut = infer (lower s)`, and the headline goes
   `s → lower → c → infer → eOut → type_safety_star`. `typecheck` alone is
   insufficient (it discards `eOut`), which is why `elaborate` runs `infer`.

3. **Exhaustiveness is a separate, mandatory conjunct.** `type_safety` requires
   `AllMatchesExhaustive` on the runtime term, which typechecking never gives.
   The scope we need is exactly the corollary `lower_elab_exhaustive` below
   (surface coverage ⇒ the *emitted-and-elaborated* matches are exhaustive) —
   NOT a general standalone `checkExhaustive`. -/

open SmallStep
open PatComp

namespace SurfaceBridge


/-! ## 1. The prelude contract (canonical special type/ctor names)

Sugar and pattern normalisation hard-code a few prelude names: pairs desugar to
the `Pair` ADT, `bool`/`if` to `Bool`, lists to `Cons`/`Nil`. These are the
canonical names. The `Has*` contract props (pinning arity + field shape at the
`CtorEnv` level) arrive with the `Expr` layer, where the value-level ctors are
actually used. -/

def nBool : TyName := .mk "Bool"
def nPair : TyName := .mk "Pair"
def nList : TyName := .mk "List"


/-! ## 2. `Surface.Ty → Core.Ty` lowering (plan item 2)

Named tyvars resolve to de Bruijn `bvar`s against the scope `tvs` (position =
index, head = 0, matching `Decls`' param convention). Type applications are
arity-checked against the `KindEnv` — Core has NO type-name→arity env, so this is
the mandatory front-end kind-check. Sugar: `pair` → `Pair`, `bool` → `Bool`
(both checked as ordinary applications of the declared prelude type; note Core's
`PrimTy` has no `bool` and `Ty` has no `pair`, so these MUST become `customTy`s).
Fails on unbound tyvar, unknown type name, or wrong arity — so a successful
lowering is always WELL-KINDED (`lowerTy_wellKinded`, below).

This transformation is DETERMINISTIC, so the `Expr` relation may consume
`lowerTy` directly rather than a separate `TyLowers` relation (spec/impl
separation only earns its keep where lowering is one-to-many — i.e. matches). -/

/-- Resolve a named tyvar to its de Bruijn index in scope (head = 0). -/
def tvarIndex : List ValName → ValName → Option Nat
  | [], _ => none
  | x :: xs, n => if x = n then some 0 else (tvarIndex xs n).map (· + 1)

mutual
/-- Lower a surface type against a kind env and a tyvar scope. -/
def lowerTy (ke : KindEnv) (tvs : List ValName) : Surface.Ty → Option Ty
  | .prim .unit => some (.prim .unit)
  | .prim .int  => some (.prim .int)
  | .prim .nat  => some (.prim .nat)
  | .prim .char => some (.prim .char)
  | .prim .bool =>
      if LookupList.get? ke nBool = some 0 then some (.customTy nBool []) else none
  | .arrow a b =>
      match lowerTy ke tvs a, lowerTy ke tvs b with
      | some a', some b' => some (.arrow a' b')
      | _, _ => none
  | .pair a b =>
      match lowerTy ke tvs a, lowerTy ke tvs b with
      | some a', some b' =>
          if LookupList.get? ke nPair = some 2 then some (.customTy nPair [a', b']) else none
      | _, _ => none
  | .tvar name =>
      match tvarIndex tvs name with
      | some i => some (.bvar i)
      | none => none
  | .customTy T args =>
      match lowerTyList ke tvs args with
      | some args' =>
          if LookupList.get? ke T = some args'.length then some (.customTy T args') else none
      | none => none
/-- Pointwise lowering of a type-argument list (mutual to make termination
    structural, mirroring `Decls.TyList.wellKindedB`). -/
def lowerTyList (ke : KindEnv) (tvs : List ValName) : List Surface.Ty → Option (List Ty)
  | [] => some []
  | t :: ts =>
      match lowerTy ke tvs t, lowerTyList ke tvs ts with
      | some t', some ts' => some (t' :: ts')
      | _, _ => none
end

/-- A resolved tyvar index is in range (feeds `Ty.WellKinded.bvar`). -/
theorem tvarIndex_lt {tvs : List ValName} {n : ValName} {i : Nat}
    (h : tvarIndex tvs n = some i) : i < tvs.length := by
  induction tvs generalizing i with
  | nil => simp [tvarIndex] at h
  | cons x xs ih =>
    simp only [tvarIndex] at h
    split at h
    · simp only [Option.some.injEq] at h
      subst h
      simp only [List.length_cons]; omega
    · obtain ⟨j, hj, heq⟩ := Option.map_eq_some_iff.mp h
      have := ih hj
      simp only [List.length_cons]; omega

/-- **Kind-check soundness of `Surface.Ty` lowering** (plan item 2's payoff): a
    successful `lowerTy` produces a well-kinded Core type at arity `tvs.length`.
    So the front-end annotation kind-check is correct — the produced type never
    references an undeclared type name, a wrong arity, or an out-of-scope tyvar.
    (Proof: mutual induction on `lowerTy`/`lowerTyList`; `tvar` via
    `tvarIndex_lt`. DELEGABLE proof of a concrete, `#guard`-tested function.) -/
theorem lowerTy_wellKinded {ke : KindEnv} {tvs : List ValName} {s : Surface.Ty} {c : Ty}
    (h : lowerTy ke tvs s = some c) : Ty.WellKinded ke tvs.length c := by
  sorry

-- Adversarial `#guard`s (per the house lesson: eval the executable side on
-- mismatched / out-of-range / missing-prelude inputs before trusting it).
private def keDemo : KindEnv := [(nBool, 0), (nPair, 2), (nList, 1), (.mk "Maybe", 1)]

-- bool desugars to the Bool ADT (not a Core prim)
#guard match lowerTy keDemo [] (.prim .bool) with
  | some (.customTy (.mk "Bool") []) => true | _ => false
-- named tyvars resolve by position (head = 0)
#guard match lowerTy keDemo [.mk "a", .mk "b"] (.tvar (.mk "a")) with
  | some (.bvar 0) => true | _ => false
#guard match lowerTy keDemo [.mk "a", .mk "b"] (.tvar (.mk "b")) with
  | some (.bvar 1) => true | _ => false
-- unbound tyvar fails
#guard (lowerTy keDemo [] (.tvar (.mk "z"))).isNone
-- unknown type name fails
#guard (lowerTy keDemo [] (.customTy (.mk "Nope") [])).isNone
-- wrong arity fails (List is unary)
#guard (lowerTy keDemo [] (.customTy nList [])).isNone
-- pair without a Pair declaration fails
#guard (lowerTy [] [] (.pair (.prim .int) (.prim .int))).isNone
-- pair with the prelude present desugars to customTy Pair
#guard match lowerTy keDemo [] (.pair (.prim .int) (.prim .int)) with
  | some (.customTy (.mk "Pair") [.prim .int, .prim .int]) => true | _ => false
-- nested application under a tyvar scope
#guard match lowerTy keDemo [.mk "a"] (.customTy nList [.tvar (.mk "a")]) with
  | some (.customTy (.mk "List") [.bvar 0]) => true | _ => false


/-! ## 3. Prelude value-constructor names + the `KindEnv` from a `CtorEnv`

The value-level ctors the sugar/pattern layers emit (`True`/`False`/`Pair`/
`Cons`/`Nil`). `lower` just *emits* these — whether they exist / have the right
arity is Core's `typecheck`'s job (Core has the ctor env), unlike *type*-level
kinding which we must do ourselves. -/

def cTrue  : CtorName := .mk "True"
def cFalse : CtorName := .mk "False"
def cPair  : CtorName := .mk "Pair"
def cCons  : CtorName := .mk "Cons"
def cNil   : CtorName := .mk "Nil"

/-- Recover the `KindEnv` (declared type name ↦ arity) from a `CtorEnv`: every
    ctor witnesses its type's name + param count. Used to feed `lowerTy` at the
    headline, where only the `CtorEnv` is in hand. -/
def kindEnvOfCtors (ctors : CtorEnv) : KindEnv :=
  ctors.map (fun p => (p.2.tyName, p.2.paramCount))


/-! ## 4. Executable expression lowering (`lower`)

The recursive lowering. It threads three scopes: `ke` (kinds, for annotations),
`tvs` (tyvar scope, for annotations), and `vs` (term-var scope; head = de Bruijn
`0` = innermost). Name resolution turns `var name` into its de Bruijn index;
sugar expands `pair`/`cons`/`list`/`bool`/`ife`/pattern-λ; and `match` is
compiled by the verified `PatComp.lowerMatch`. Deterministic everywhere.

v1 scoping choices (documented, refine later): a `PolyTy` annotation binds
exactly its own `foralls` (`lowerPoly`); a λ-param monotype annotation is lowered
under the ambient `tvs` (empty at top level); complex pattern-λs (a λ whose
parameter is a non-trivial pattern) are deferred (`none`). -/

mutual
/-- The names a pattern binds, in **pre-order** (left-to-right, depth-first) —
    exactly the capture order of `matchPat`/`firstMatch`, so binding `j` lands at
    de Bruijn `j` in the compiled body. -/
def patVars : Surface.Pattern → List ValName
  | .name n     => [n]
  | .wildcard   => []
  | .ctor _ ps  => patVarsList ps
  | .pair a b   => patVars a ++ patVars b
  | .cons h t   => patVars h ++ patVars t
  | .list items => patVarsList items
def patVarsList : List Surface.Pattern → List ValName
  | []      => []
  | p :: ps => patVars p ++ patVarsList ps
end

/-- Build a Core list value from element expressions: `[x,y] ↦ Cons x (Cons y Nil)`. -/
def mkList : List Expr → Expr
  | []      => .ctor cNil
  | x :: xs => .app (.app (.ctor cCons) x) (mkList xs)

/-- Lower an optional monotype annotation (λ-param): `none` stays `none`; `some τ`
    must kind-check via `lowerTy` (else the whole lowering fails). -/
def lowerAnn (ke : KindEnv) (tvs : List ValName) : Option Surface.Ty → Option (Option Ty)
  | none   => some none
  | some τ => (lowerTy ke tvs τ).map some

/-- Lower a surface scheme to a Core scheme: `foralls` become the `paramCount`
    binders, and the body is kind-checked with `foralls` as the tyvar scope. -/
def lowerPoly (ke : KindEnv) (σ : Surface.PolyTy) : Option PolyTy :=
  (lowerTy ke σ.foralls σ.body).map (fun b => ⟨σ.foralls.length, b⟩)

def lowerPolyAnn (ke : KindEnv) : Option Surface.PolyTy → Option (Option PolyTy)
  | none   => some none
  | some σ => (lowerPoly ke σ).map some

def lowerAnnList (ke : KindEnv) : List (Option Surface.PolyTy) → Option (List (Option PolyTy))
  | []      => some []
  | a :: as =>
    match lowerPolyAnn ke a, lowerAnnList ke as with
    | some a', some as' => some (a' :: as')
    | _, _              => none

mutual
/-- Lower a surface expression against kind env `ke`, tyvar scope `tvs`, and
    term-var scope `vs`. -/
def lowerExpr (ke : KindEnv) (tvs vs : List ValName) : Surface.Expr → Option Expr
  | .primLit (.bool b)  => some (.ctor (if b then cTrue else cFalse))
  | .primLit .unit      => some (.primLit .unit)
  | .primLit (.int n)   => some (.primLit (.int n))
  | .primLit (.nat n)   => some (.primLit (.nat n))
  | .primLit (.char c)  => some (.primLit (.char c))
  | .pair a b =>
    match lowerExpr ke tvs vs a, lowerExpr ke tvs vs b with
    | some a', some b' => some (.app (.app (.ctor cPair) a') b')
    | _, _             => none
  | .cons h t =>
    match lowerExpr ke tvs vs h, lowerExpr ke tvs vs t with
    | some h', some t' => some (.app (.app (.ctor cCons) h') t')
    | _, _             => none
  | .list items =>
    match lowerExprList ke tvs vs items with
    | some items' => some (mkList items')
    | none        => none
  | .lambda param paramAnn body =>
    match lowerAnn ke tvs paramAnn with
    | none       => none
    | some ann'  =>
      match param with
      | .name x =>
        match lowerExpr ke tvs (x :: vs) body with
        | some b' => some (.lambda ann' b')
        | none    => none
      | .wildcard =>
        match lowerExpr ke tvs (.mk "_" :: vs) body with
        | some b' => some (.lambda ann' b')
        | none    => none
      | _ => none   -- v1: complex pattern-λ deferred
  | .app f x =>
    match lowerExpr ke tvs vs f, lowerExpr ke tvs vs x with
    | some f', some x' => some (.app f' x')
    | _, _             => none
  | .letIn name ann rhs body =>
    match lowerPolyAnn ke ann with
    | none      => none
    | some ann' =>
      match lowerExpr ke tvs vs rhs, lowerExpr ke tvs (name :: vs) body with
      | some rhs', some body' => some (.letIn ann' rhs' body')
      | _, _                  => none
  | .letRecIn binds body =>
    let recScope := binds.map (·.1) ++ vs
    match lowerAnnList ke (binds.map (·.2.1)),
          lowerRecBinds ke tvs recScope binds,
          lowerExpr ke tvs recScope body with
    | some anns', some bindings', some body' => some (.letRec anns' bindings' body')
    | _, _, _                                => none
  | .var name =>
    match tvarIndex vs name with
    | some i => some (.var i [])
    | none   => none
  | .ctor name => some (.ctor name)
  | .ife c t f =>
    match lowerExpr ke tvs vs c, lowerExpr ke tvs vs t, lowerExpr ke tvs vs f with
    | some c', some t', some f' =>
        some (lowerMatch c' [.ctor cTrue [], .ctor cFalse []] (fun i => if i = 0 then t' else f'))
    | _, _, _ => none
  | .match_ scrut brs =>
    match lowerExpr ke tvs vs scrut, lowerBranches ke tvs vs brs with
    | some scrut', some bodies' =>
        some (lowerMatch scrut' (brs.map Prod.fst) (fun i => bodies'.getD i (.ctor cNil)))
    | _, _ => none
/-- Lower a list of expressions, all under the same scope (`list` sugar). -/
def lowerExprList (ke : KindEnv) (tvs vs : List ValName) : List Surface.Expr → Option (List Expr)
  | []      => some []
  | e :: es =>
    match lowerExpr ke tvs vs e, lowerExprList ke tvs vs es with
    | some e', some es' => some (e' :: es')
    | _, _              => none
/-- Lower each match branch body under its pattern's captures (pre-order) prepended
    to the term scope. Returns the bodies in branch order. -/
def lowerBranches (ke : KindEnv) (tvs vs : List ValName) : List (Surface.Pattern × Surface.Expr) → Option (List Expr)
  | []           => some []
  | (p, b) :: rest =>
    match lowerExpr ke tvs (patVars p ++ vs) b, lowerBranches ke tvs vs rest with
    | some b', some rest' => some (b' :: rest')
    | _, _                => none
/-- Lower each recursive binding's RHS under the shared group scope. -/
def lowerRecBinds (ke : KindEnv) (tvs recScope : List ValName) :
    List (ValName × Option Surface.PolyTy × Surface.Expr) → Option (List Expr)
  | []               => some []
  | (_, _, e) :: rest =>
    match lowerExpr ke tvs recScope e, lowerRecBinds ke tvs recScope rest with
    | some e', some rest' => some (e' :: rest')
    | _, _                => none
end

/-- **The executable lowering** (closed program): resolve, kind-check, desugar,
    and pattern-compile `s` into Core, starting from empty scopes and the kind env
    recovered from `ctors`. -/
def lower (ctors : CtorEnv) (s : Surface.Expr) : Option Expr :=
  lowerExpr (kindEnvOfCtors ctors) [] [] s

-- Adversarial `#guard`s for the executable lowering.
private def ctorsDemo : CtorEnv := (elabDecls preludeDecls).getD []

-- bool literal desugars to the True/False ctor
#guard match lower ctorsDemo (.primLit (.bool true)) with
  | some (.ctor (.mk "True")) => true | _ => false
-- unbound variable fails
#guard (lower ctorsDemo (.var (.mk "x"))).isNone
-- λx. x  ↦  λ. var 0
#guard match lower ctorsDemo (.lambda (.name (.mk "x")) none (.var (.mk "x"))) with
  | some (.lambda none (.var 0 [])) => true | _ => false
-- let x = 1 in x  ↦  let 1 in var 0
#guard match lower ctorsDemo (.letIn (.mk "x") none (.primLit (.int 1)) (.var (.mk "x"))) with
  | some (.letIn none (.primLit (.int 1)) (.var 0 [])) => true | _ => false
-- (1, 2)  ↦  Pair 1 2
#guard match lower ctorsDemo (.pair (.primLit (.int 1)) (.primLit (.int 2))) with
  | some (.app (.app (.ctor (.mk "Pair")) (.primLit (.int 1))) (.primLit (.int 2))) => true | _ => false
-- [1]  ↦  Cons 1 Nil
#guard match lower ctorsDemo (.list [.primLit (.int 1)]) with
  | some (.app (.app (.ctor (.mk "Cons")) (.primLit (.int 1))) (.ctor (.mk "Nil"))) => true | _ => false
-- shadowing: λx. λx. x  ↦  inner x is var 0
#guard match lower ctorsDemo (.lambda (.name (.mk "x")) none (.lambda (.name (.mk "x")) none (.var (.mk "x")))) with
  | some (.lambda none (.lambda none (.var 0 []))) => true | _ => false
-- outer reference: λx. λy. x  ↦  x is var 1 under two binders
#guard match lower ctorsDemo (.lambda (.name (.mk "x")) none (.lambda (.name (.mk "y")) none (.var (.mk "x")))) with
  | some (.lambda none (.lambda none (.var 1 []))) => true | _ => false
-- ife and match produce some (structure checked by the pattern-compilation tests)
#guard (lower ctorsDemo (.ife (.primLit (.bool true)) (.primLit (.int 1)) (.primLit (.int 0)))).isSome
#guard (lower ctorsDemo (.match_ (.var (.mk "x")) [])).isNone  -- unbound scrutinee


/-! ## 5. Surface pattern well-formedness + coverage predicates

`PatternWF` is the surface-level counterpart of `GPatWF`: a pattern is well-formed
at type `τ` when its constructors exist and sub-patterns fit field types (with
sugar `pair`/`cons`/`list` desugaring to `Pair`/`Cons`/`Nil`). The bridge lemma
`PatternWF_to_GPatWF` connects it to the kernel's `GPatWF (norm p)`.

`MatchPatternsCover` / `SurfaceCovers` are the exhaustiveness side: at each
`match`, patterns must cover the scrutinee's ADT type `T` (every ctor of `T` has
a testing branch, or a trailing irrefutable catch-all). The type `T` is carried
in the `SurfaceCovers.match_` witness — the proof of O5 instantiates it from
scrutinee typing after `typecheck`. -/

/-- **Surface pattern well-formedness**, defined as `GPatWF` of the *normalised*
    pattern. Defining it via `norm` (rather than as a fresh surface-native
    inductive) makes it correct-by-construction and consistent with the kernel:
    the sugar cases `pair`/`cons`/`list` inherit `GPatWF.gctor`'s ctor-existence +
    instantiated-field-type obligations automatically. (An earlier bespoke
    inductive OMITTED those obligations on the sugar rules, making the bridge to
    `GPatWF` FALSE — e.g. `PatternWF [] (.pair _ _) (customTy Pair …)` held but
    `GPatWF [] (.gctor Pair …) …` cannot, since `Pair ∉ []`.) -/
def PatternWF (ctors : CtorEnv) (p : Surface.Pattern) (τ : Ty) : Prop :=
  GPatWF ctors (norm p) τ

/-- **Bridge (★):** trivial by definition. Kept as a named lemma for the
    match-case soundness plumbing (`lowerMatch_adequate_of_typed` consumes
    `GPatWF (norm p)` per row of `initMatrix`). -/
theorem PatternWF_to_GPatWF {ctors : CtorEnv} {p : Surface.Pattern} {τ : Ty}
    (h : PatternWF ctors p τ) : GPatWF ctors (norm p) τ := h

/-- **Semantic exhaustiveness of one match's branch patterns** at scrutinee type
    `customTy T tyArgs`: the surface oracle `firstMatch` selects SOME branch for
    every well-typed value of that type. This is the honest coverage condition —
    a flat "top-level ctors covered" check is UNSOUND (it misses nested gaps: e.g.
    `Cons (Just x) t | Nil` leaves `Cons Nothing Nil` unmatched, verified by
    `firstMatch (Cons Nothing Nil) … = none`). Via `PatComp.compile_surface_total_iff`
    this lifts to "the compiled tree has no reachable `fail`", hence (with the
    emit fix) the emitted match covers every ctor ⇒ `AllMatchesExhaustive` (O5).
    NOTE: not executable; an executable checker implying this is the deferred
    item-6 refinement (`checkExhaustive`). -/
def MatchExhaustive (ctors : CtorEnv) (T : TyName) (tyArgs : List Ty)
    (ps : List Surface.Pattern) : Prop :=
  ∀ v, IsValue v → TypeOfElabHM ⟨[], ctors⟩ v (.customTy T tyArgs) →
    (firstMatch v ps).isSome

/-- Every `match` in `s` is exhaustive (and subexpressions recurse). At `match_`
    the witness carries the scrutinee's ADT type `(T, tyArgs)` — O5 instantiates it
    from the lowered scrutinee's typing. -/
inductive SurfaceCovers (ctors : CtorEnv) : Surface.Expr → Prop where
  | primLit {p} : SurfaceCovers ctors (.primLit p)
  | var {n} : SurfaceCovers ctors (.var n)
  | ctor {n} : SurfaceCovers ctors (.ctor n)
  | pair {a b} :
      SurfaceCovers ctors a → SurfaceCovers ctors b →
      SurfaceCovers ctors (.pair a b)
  | cons {h t} :
      SurfaceCovers ctors h → SurfaceCovers ctors t →
      SurfaceCovers ctors (.cons h t)
  | list {items} :
      (∀ e ∈ items, SurfaceCovers ctors e) →
      SurfaceCovers ctors (.list items)
  | lambda {param ann body} :
      SurfaceCovers ctors body →
      SurfaceCovers ctors (.lambda param ann body)
  | app {f x} :
      SurfaceCovers ctors f → SurfaceCovers ctors x →
      SurfaceCovers ctors (.app f x)
  | letIn {name ann rhs body} :
      SurfaceCovers ctors rhs → SurfaceCovers ctors body →
      SurfaceCovers ctors (.letIn name ann rhs body)
  | letRecIn {binds body} :
      (∀ b ∈ binds, SurfaceCovers ctors b.2.2) → SurfaceCovers ctors body →
      SurfaceCovers ctors (.letRecIn binds body)
  | ife {c t f} :
      SurfaceCovers ctors c → SurfaceCovers ctors t → SurfaceCovers ctors f →
      SurfaceCovers ctors (.ife c t f)
  | match_ {scrut brs T tyArgs} :
      SurfaceCovers ctors scrut →
      (∀ p b, (p, b) ∈ brs → SurfaceCovers ctors b) →
      MatchExhaustive ctors T tyArgs (brs.map Prod.fst) →
      SurfaceCovers ctors (.match_ scrut brs)


/-! ## 6. The `Lowers` relation (spec — B1 behavioural match)

Mirrors `lowerExpr` for the deterministic cases. At `match`, **non-deterministic**:
any `emitInner` + branch bodies satisfying the behavioural premise (surface
`firstMatch` agrees with Core `Step` on well-typed ADT values). `lower` emits
one witness (`lowerMatch`); soundness cites `lowerMatch_adequate_of_typed`. -/

/-- The default body used when indexing past the branch bodies list; never
    actually reached (`firstMatch` only returns indices `< brs.length`), but
    needed to give `lowerMatch` a total `Nat → Expr` body function. Shared by
    `lower` and the `Lowers` match rule so they pin the *same* body function. -/
def matchBodyDefault : Expr := .ctor cNil

/-- The `Nat → Expr` body function for a match with lowered branch bodies
    `bodies'`, mirroring `lower`'s `fun i => bodies'.getD i _`. -/
def bodyFn (bodies' : List Expr) : Nat → Expr := fun i => bodies'.getD i matchBodyDefault

mutual
/-- Declarative lowering of a surface expression under kind env `ke`, tyvar scope
    `tvs` (parameters), and term-var scope `vs` (an **index** — it grows under
    binders). Mirrors `lowerExpr` for the deterministic cases; the `match_` rule
    is **behavioural** (B1): the emitted body `emitInner` is existential, pinned
    only by agreement with the surface oracle `firstMatch` under Core `Step` on
    well-typed ADT values. -/
inductive LowersExpr (ctors : CtorEnv) (ke : KindEnv) (tvs : List ValName) :
    List ValName → Surface.Expr → Expr → Prop where
  | primLitUnit {vs} :
      LowersExpr ctors ke tvs vs (.primLit .unit) (.primLit .unit)
  | primLitInt {vs n} :
      LowersExpr ctors ke tvs vs (.primLit (.int n)) (.primLit (.int n))
  | primLitNat {vs n} :
      LowersExpr ctors ke tvs vs (.primLit (.nat n)) (.primLit (.nat n))
  | primLitChar {vs c} :
      LowersExpr ctors ke tvs vs (.primLit (.char c)) (.primLit (.char c))
  | primLitBool {vs b} :
      LowersExpr ctors ke tvs vs (.primLit (.bool b)) (.ctor (if b then cTrue else cFalse))
  | pair {vs a b a' b'} :
      LowersExpr ctors ke tvs vs a a' → LowersExpr ctors ke tvs vs b b' →
      LowersExpr ctors ke tvs vs (.pair a b) (.app (.app (.ctor cPair) a') b')
  | cons {vs h t h' t'} :
      LowersExpr ctors ke tvs vs h h' → LowersExpr ctors ke tvs vs t t' →
      LowersExpr ctors ke tvs vs (.cons h t) (.app (.app (.ctor cCons) h') t')
  | list {vs items items'} :
      LowersExprList ctors ke tvs vs items items' →
      LowersExpr ctors ke tvs vs (.list items) (mkList items')
  | lambda_name {vs x ann ann' body body'} :
      (match ann with | none => ann' = none | some τ => lowerTy ke tvs τ = some ann') →
      LowersExpr ctors ke tvs (x :: vs) body body' →
      LowersExpr ctors ke tvs vs (.lambda (.name x) ann body) (.lambda ann' body')
  | lambda_wild {vs ann ann' body body'} :
      (match ann with | none => ann' = none | some τ => lowerTy ke tvs τ = some ann') →
      LowersExpr ctors ke tvs (.mk "_" :: vs) body body' →
      LowersExpr ctors ke tvs vs (.lambda .wildcard ann body) (.lambda ann' body')
  | app {vs f x f' x'} :
      LowersExpr ctors ke tvs vs f f' → LowersExpr ctors ke tvs vs x x' →
      LowersExpr ctors ke tvs vs (.app f x) (.app f' x')
  | letIn {vs name ann ann' rhs rhs' body body'} :
      (match ann with | none => ann' = none | some σ => lowerPoly ke σ = some ann') →
      LowersExpr ctors ke tvs vs rhs rhs' →
      LowersExpr ctors ke tvs (name :: vs) body body' →
      LowersExpr ctors ke tvs vs (.letIn name ann rhs body) (.letIn ann' rhs' body')
  | letRecIn {vs binds anns' bindings' body body'} :
      lowerAnnList ke (binds.map (·.2.1)) = some anns' →
      LowersRecBinds ctors ke tvs (binds.map (·.1) ++ vs) binds bindings' →
      LowersExpr ctors ke tvs (binds.map (·.1) ++ vs) body body' →
      LowersExpr ctors ke tvs vs (.letRecIn binds body)
        (.letRec anns' bindings' body')
  | var {vs name i} :
      tvarIndex vs name = some i →
      LowersExpr ctors ke tvs vs (.var name) (.var i [])
  | ctor {vs name} :
      LowersExpr ctors ke tvs vs (.ctor name) (.ctor name)
  -- `ife` is deterministic sugar: pinned to the same 2-branch Bool match `lower`
  -- emits (this mentions `lowerMatch`, tolerable for deterministic sugar — the
  -- genuine non-determinism lives in `match_` below, which stays impl-free).
  | ife {vs c t f c' t' f'} :
      LowersExpr ctors ke tvs vs c c' →
      LowersExpr ctors ke tvs vs t t' →
      LowersExpr ctors ke tvs vs f f' →
      LowersExpr ctors ke tvs vs (.ife c t f)
        (lowerMatch c' [.ctor cTrue [], .ctor cFalse []] (fun i => if i = 0 then t' else f'))
  -- `match_` (B1, behavioural + non-deterministic): scrutinee + branch bodies
  -- lower recursively; `emitInner` is ANY Core term that, wrapped as
  -- `let scrut in emitInner`, reduces to the `firstMatch`-selected branch body
  -- (with pre-order captures) on every well-typed ADT value with WF patterns.
  -- `lower` witnesses it via `lowerMatch` + `lowerMatch_adequate_of_typed`.
  | match_ {vs scrut brs scrut' bodies' emitInner} :
      LowersExpr ctors ke tvs vs scrut scrut' →
      LowersBranches ctors ke tvs vs brs bodies' →
      (∀ (T : TyName) (tyArgs : List Ty) (root : Expr),
        IsValue root →
        TypeOfElabHM ⟨[], ctors⟩ root (.customTy T tyArgs) →
        (∀ p ∈ brs.map Prod.fst, PatternWF ctors p (.customTy T tyArgs)) →
        ∀ (i : Nat) (ws : List Expr),
          firstMatch root (brs.map Prod.fst) = some (i, ws) →
            Relation.ReflTransGen Step (.letIn none root emitInner)
              ((bodyFn bodies' i).substN 0 ws)) →
      LowersExpr ctors ke tvs vs (.match_ scrut brs) (.letIn none scrut' emitInner)
/-- Pointwise lowering of a list of expressions under one scope (`list` sugar). -/
inductive LowersExprList (ctors : CtorEnv) (ke : KindEnv) (tvs : List ValName) :
    List ValName → List Surface.Expr → List Expr → Prop where
  | nil {vs} : LowersExprList ctors ke tvs vs [] []
  | cons {vs e es e' es'} :
      LowersExpr ctors ke tvs vs e e' → LowersExprList ctors ke tvs vs es es' →
      LowersExprList ctors ke tvs vs (e :: es) (e' :: es')
/-- Lowering of a recursive binding group's RHSs under the shared group scope
    (here carried in the `vs` index). -/
inductive LowersRecBinds (ctors : CtorEnv) (ke : KindEnv) (tvs : List ValName) :
    List ValName → List (ValName × Option Surface.PolyTy × Surface.Expr) → List Expr → Prop where
  | nil {vs} : LowersRecBinds ctors ke tvs vs [] []
  | cons {vs bind rest e' rest'} :
      LowersExpr ctors ke tvs vs bind.2.2 e' →
      LowersRecBinds ctors ke tvs vs rest rest' →
      LowersRecBinds ctors ke tvs vs (bind :: rest) (e' :: rest')
/-- Lowering of match branch bodies: body `i` lowers under its pattern's captures
    (pre-order) prepended to `vs`. Result is the bodies in branch order. -/
inductive LowersBranches (ctors : CtorEnv) (ke : KindEnv) (tvs : List ValName) :
    List ValName → List (Surface.Pattern × Surface.Expr) → List Expr → Prop where
  | nil {vs} : LowersBranches ctors ke tvs vs [] []
  | cons {vs p b rest b' rest'} :
      LowersExpr ctors ke tvs (patVars p ++ vs) b b' →
      LowersBranches ctors ke tvs vs rest rest' →
      LowersBranches ctors ke tvs vs ((p, b) :: rest) (b' :: rest')
end

/-- Top-level declarative lowering (closed program): empty tyvar + term scopes,
    kind env recovered from `ctors`. -/
def Lowers (ctors : CtorEnv) (s : Surface.Expr) (c : Expr) : Prop :=
  LowersExpr ctors (kindEnvOfCtors ctors) [] [] s c

/-- **`lower` soundness:** the executable lowering satisfies the spec. Match case
    cites `lowerMatch_adequate_of_typed` via `PatternWF_to_GPatWF`. -/
theorem lower_sound {ctors : CtorEnv} {s : Surface.Expr} {c : Expr}
    (h : lower ctors s = some c) : Lowers ctors s c := by
  sorry

/-- **`lower` completeness:** if some valid lowering exists, `lower` finds one. -/
theorem lower_complete {ctors : CtorEnv} {s : Surface.Expr} {c : Expr}
    (h : Lowers ctors s c) : (lower ctors s).isSome := by
  sorry


/-! ## 7. Surface well-typedness — DEFINED via the relation (no `Surface.TypeOf`)

`s` is well-typed exactly when *some* lowering of it is Core-typeable. The
executable pipeline decides this with `lower` + `typecheck`. -/

/-- A surface program is well-typed iff some lowering of it typechecks in Core. -/
def SurfaceWT (ctors : CtorEnv) (s : Surface.Expr) : Prop :=
  ∃ c, Lowers ctors s c ∧ (typecheck ctors c).isSome


/-! ## 8. The runtime term: lower, then ELABORATE

The Core term that actually executes is the elaborated `eOut` (decorated `var`
type-arguments), substituted by the inferred `S`. `typecheck` throws `eOut`
away, so we go through `infer` directly. For a closed program the frontier seed
is `c.freshFloor` and the rigid set is empty. -/

/-- Lower `s`, then run inference to obtain the decorated, runnable Core term
    `eOut.substTyFvars S`. `none` if lowering or inference fails. -/
def elaborate (ctors : CtorEnv) (s : Surface.Expr) : Option Expr :=
  (lower ctors s).bind fun c =>
    (infer c.freshFloor ⟨[], ctors⟩ c).map fun r => r.2.2.1.substTyFvars r.2.1

/-! ### Trust-free regression guards for the `emit` fix (see PatComp `emit`)

These `#guard`s RUN the pipeline, so they catch a regression in `emit`'s
wildcard handling independently of any proof: before the fix, `emit` appended an
untypeable `PatCompFail` wildcard to every switch, so `if` and enumerated
(catch-all-free) matches failed to typecheck. -/

private def maybeCtors : CtorEnv :=
  (elabDecls (preludeDecls ++
    [{ name := ⟨"Maybe"⟩, paramCount := 1,
       ctors := [(⟨"Just"⟩, [.bvar 0]), (⟨"Nothing"⟩, [])] }])).getD []

-- `if true then 1 else 0` now typechecks (desugars to an enumerated True|False match).
#guard (elaborate ctorsDemo (.ife (.primLit (.bool true)) (.primLit (.int 1)) (.primLit (.int 0)))).isSome
-- a fully-enumerated exhaustive match (no catch-all) now typechecks.
#guard (elaborate maybeCtors (.match_ (.app (.ctor (⟨"Just"⟩)) (.primLit (.int 5)))
    [(.ctor ⟨"Just"⟩ [.name ⟨"x"⟩], .var ⟨"x"⟩), (.ctor ⟨"Nothing"⟩ [], .primLit (.int 0))])).isSome
-- a catch-all match still typechecks.
#guard (elaborate maybeCtors (.match_ (.app (.ctor (⟨"Just"⟩)) (.primLit (.int 5)))
    [(.ctor ⟨"Just"⟩ [.name ⟨"x"⟩], .var ⟨"x"⟩), (.wildcard, .primLit (.int 0))])).isSome
-- a NON-exhaustive match (missing Nothing, no catch-all) ALSO typechecks — so
-- `typecheck` does NOT enforce exhaustiveness; `SurfaceCovers` genuinely is.
#guard (elaborate maybeCtors (.match_ (.app (.ctor (⟨"Just"⟩)) (.primLit (.int 5)))
    [(.ctor ⟨"Just"⟩ [.name ⟨"x"⟩], .var ⟨"x"⟩)])).isSome


/-! ## 9. The obligations the seam creates (proof bodies — delegable)

These are the ONLY genuinely-new proof obligations behind the headline; the rest
of the payoff is `infer_sound`/`Infer.sound` + `type_safety_star`, discharged
inline in `surface_type_safe`. -/

/-- **(O2) Lowered programs are type-closed.** A `lower` output has no free type
    variables, so inference's rigid seed is empty and the frontier machinery
    disappears. Provable once `lower` is defined (it emits `bvar`-indexed types
    from the kind-checker; no `fvar`s). -/
theorem lower_tyClosed {ctors : CtorEnv} {s : Surface.Expr} {c : Expr}
    (h : lower ctors s = some c) : c.tyFreeVars = [] := by
  sorry

/-- **(O3) Typechecking ⇒ inference succeeds (recovering the runtime term).**
    For a type-closed `c`, `typecheck` and `infer` run the *same* `inferCore`
    call (`principalType` seeds `c.tyFreeVars = []`, matching `infer`'s empty
    rigid set), so a successful `typecheck` yields the elaborated `(Φ',S,eOut,τ)`.
    Mechanical from `typecheck`/`principalType`/`infer` unfolding. -/
theorem infer_of_typecheck {ctors : CtorEnv} {c : Expr}
    (hclosed : c.tyFreeVars = []) (htc : (typecheck ctors c).isSome) :
    ∃ Φ' S eOut τ, infer c.freshFloor ⟨[], ctors⟩ c = some (Φ', S, eOut, τ) := by
  sorry

/-- **(O5) Exhaustiveness of the emitted-and-elaborated matches — THE workhorse
    target.** If every surface `match` in `s` covers its scrutinee's ADT type
    (`SurfaceCovers`), then the lowered-then-elaborated Core term's matches are
    all `AllMatchesExhaustive` — exactly the conjunct `type_safety` demands.

    Sub-obligations (for the handoff):
    * lowering emits, for each surface match, the compiled `PatComp.lowerMatch`
      whose branch set is the compiler's `DTree` leaves;
    * a `DTree.NoFail` ⇒ totality lemma connects "no reachable `fail`" to
      `AllMatchesExhaustive` on the emitted `match_` (the memo's deferred (X)
      piece; needs the nested-recursive `DTree.occs`);
    * `SurfaceCovers` ⇒ the compiled tree has no reachable `fail`
      (`PatComp.compile_surface_total_iff`, given scrutinee typing);
    * exhaustiveness is preserved by elaboration
      (`AllMatchesExhaustive.instTy`/`substN`/`shiftFrom`) down to
      `eOut.substTyFvars S`. -/
theorem lower_elab_exhaustive {ctors : CtorEnv} {s : Surface.Expr} {c : Expr}
    {Φ' : Nat} {S : Subst} {eOut : Expr} {τ : Ty}
    (hcov : SurfaceCovers ctors s) (hlow : lower ctors s = some c)
    (hinf : infer c.freshFloor ⟨[], ctors⟩ c = some (Φ', S, eOut, τ)) :
    AllMatchesExhaustive ctors (eOut.substTyFvars S) := by
  sorry


/-! ## 10. THE HEADLINE

A well-typed, exhaustive surface program elaborates to a Core term that is
type-safe and never gets stuck. Stated over the executable pipeline (`lower`
succeeds, `typecheck` succeeds, patterns cover) — the object that actually runs.
The declarative `SurfaceWT`-phrased corollary is future work (goes through
`lower`-completeness + typeability-invariance across valid lowerings). -/

/-- **Well-typed surface programs don't go wrong.** Given a lowering `c` of `s`
    that typechecks and whose matches cover their types, `elaborate ctors s`
    yields a Core term `e` that is well-typed at `τ`, all-matches-exhaustive, and
    never stuck: every term reachable from `e` under Core's real `Step` is a
    value or steps again. -/
theorem surface_type_safe {ctors : CtorEnv} {s : Surface.Expr} {c : Expr}
    (hlow : lower ctors s = some c)
    (htc : (typecheck ctors c).isSome)
    (hcov : SurfaceCovers ctors s) :
    ∃ e τ, elaborate ctors s = some e ∧
      TypeOfElabHM ⟨[], ctors⟩ e τ ∧
      AllMatchesExhaustive ctors e ∧
      ∀ e', Relation.ReflTransGen Step e e' →
        (IsValue e' ∨ ∃ e'', Step e' e'') := by
  have hclosed : c.tyFreeVars = [] := lower_tyClosed hlow
  obtain ⟨Φ', S, eOut, τ, hinf⟩ := infer_of_typecheck hclosed htc
  -- (O4) elab typing of the runtime term: mechanical from infer_sound + Infer.sound.
  have hty : TypeOfElabHM ⟨[], ctors⟩ (eOut.substTyFvars S) τ := by
    have h := Infer.sound (infer_sound hinf) CtxWF.empty CtxBelow.empty []
      (by simp) (by rw [hclosed]; simp) (by simp)
    simpa using h
  -- (O5) exhaustiveness of the runtime term.
  have hexh : AllMatchesExhaustive ctors (eOut.substTyFvars S) :=
    lower_elab_exhaustive hcov hlow hinf
  refine ⟨eOut.substTyFvars S, τ, ?_, hty, hexh, ?_⟩
  · -- `elaborate` produces exactly this term.
    simp [elaborate, hlow, hinf]
  · -- (O6) non-stuckness: iterated type safety of the elaborated term.
    intro e' hrtc
    exact (TypeOfElabHM.type_safety_star hty hexh e' hrtc).2

end SurfaceBridge
