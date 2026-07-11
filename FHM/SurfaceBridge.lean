import FHM.Core
import FHM.SurfaceLang
import FHM.Decls
import FHM.PatComp
import FHM.InferW

/-! # The surface → Core bridge

This module is the **front end**: it lowers `Surface.Expr`/`Surface.Ty` into Core
and states the campaign's headline payoff — *a well-typed, exhaustive surface
program elaborates to a Core program that is type-safe and never gets stuck*.

**Status: expression headline + DataDecl + Program groups + freeNames + sccGroups.**
`sccGroups` (naive mutual-reachability SCC) feeds `Program.groups`;
`ValidBindingGroups` is the non-det spec (`sccGroups_sound`/`_complete` still `sorry`).
See `briefs/next-agent-brief-surface-bridge-followups.md`.

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

mutual
/-- Kind-check soundness for a list of surface types (mutual with `lowerTy_wellKinded`). -/
theorem lowerTyList_wellKinded {ke : KindEnv} {tvs : List ValName}
    {ss : List Surface.Ty} {cs : List Ty}
    (h : lowerTyList ke tvs ss = some cs) :
    ∀ c ∈ cs, Ty.WellKinded ke tvs.length c := by
  cases ss with
  | nil =>
    simp only [lowerTyList, Option.some.injEq] at h; subst h
    intro c hc; cases hc
  | cons s ss =>
    simp only [lowerTyList] at h
    cases ht : lowerTy ke tvs s with
    | none => simp [ht] at h
    | some t' =>
      cases hts : lowerTyList ke tvs ss with
      | none => simp [ht, hts] at h
      | some ts' =>
        simp only [ht, hts, Option.some.injEq] at h; subst h
        intro c hc
        simp only [List.mem_cons] at hc
        rcases hc with rfl | hc
        · exact lowerTy_wellKinded ht
        · exact lowerTyList_wellKinded hts c hc

/-- **Kind-check soundness of `Surface.Ty` lowering** (plan item 2's payoff): a
    successful `lowerTy` produces a well-kinded Core type at arity `tvs.length`.
    So the front-end annotation kind-check is correct — the produced type never
    references an undeclared type name, a wrong arity, or an out-of-scope tyvar.
    (Proof: mutual induction on `lowerTy`/`lowerTyList`; `tvar` via
    `tvarIndex_lt`. DELEGABLE proof of a concrete, `#guard`-tested function.) -/
theorem lowerTy_wellKinded {ke : KindEnv} {tvs : List ValName} {s : Surface.Ty} {c : Ty}
    (h : lowerTy ke tvs s = some c) : Ty.WellKinded ke tvs.length c := by
  cases s with
  | prim p =>
    cases p with
    | unit | int | nat | char =>
      simp only [lowerTy, Option.some.injEq] at h; subst h; exact .prim
    | bool =>
      simp only [lowerTy] at h
      split at h
      · rename_i hg; simp only [Option.some.injEq] at h; subst h
        exact .customTy hg (by intro _ hmem; simp at hmem)
      · cases h
  | arrow a b =>
    simp only [lowerTy] at h
    cases ha : lowerTy ke tvs a with
    | none => simp [ha] at h
    | some a' =>
      cases hb : lowerTy ke tvs b with
      | none => simp [ha, hb] at h
      | some b' =>
        simp only [ha, hb, Option.some.injEq] at h; subst h
        exact .arrow (lowerTy_wellKinded ha) (lowerTy_wellKinded hb)
  | pair a b =>
    simp only [lowerTy] at h
    cases ha : lowerTy ke tvs a with
    | none => simp [ha] at h
    | some a' =>
      cases hb : lowerTy ke tvs b with
      | none => simp [ha, hb] at h
      | some b' =>
        simp only [ha, hb] at h
        split at h
        · rename_i hg; simp only [Option.some.injEq] at h; subst h
          exact .customTy hg (by
            intro arg hmem
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
            rcases hmem with rfl | rfl
            · exact lowerTy_wellKinded ha
            · exact lowerTy_wellKinded hb)
        · cases h
  | tvar name =>
    simp only [lowerTy] at h
    cases hi : tvarIndex tvs name with
    | none => simp [hi] at h
    | some i =>
      simp only [hi, Option.some.injEq] at h; subst h
      exact .bvar (tvarIndex_lt hi)
  | customTy T args =>
    simp only [lowerTy] at h
    cases hargs : lowerTyList ke tvs args with
    | none => simp [hargs] at h
    | some args' =>
      simp only [hargs] at h
      split at h
      · rename_i hg; simp only [Option.some.injEq] at h; subst h
        exact .customTy hg (lowerTyList_wellKinded hargs)
      · cases h
end

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


/-! ## 2b. Surface `DataDecl` lowering (plan item 1)

Named params → `paramCount` + de Bruijn field types via `lowerTy`. An ambient
`KindEnv` (`ke₀`, typically the prelude) is prepended so user fields may mention
prelude types; headers of `sdecls` still contribute mutual refs. Spec/impl:
`LowersDataDeclsIn` / `lowerDataDeclsIn`. The `ke₀ = []` specializations recover
the original closed-group API. -/

/-- Pass 1: type name ↦ arity from surface decl headers (params still named). -/
def surfaceKindEnv (sdecls : List Surface.DataDecl) : KindEnv :=
  sdecls.map (fun d => (d.name, d.params.length))

/-- Prelude kinds (from the Core `preludeDecls`). -/
def preludeKindEnv : KindEnv := DataDecls.kindEnv preludeDecls

/-- Ambient kinds ++ surface headers (prelude first). -/
def declKindEnv (ke₀ : KindEnv) (sdecls : List Surface.DataDecl) : KindEnv :=
  ke₀ ++ surfaceKindEnv sdecls

/-- Field-type list lowers pointwise via `lowerTy`. -/
inductive LowersFields (ke : KindEnv) (tvs : List ValName) :
    List Surface.Ty → List Ty → Prop
  | nil : LowersFields ke tvs [] []
  | cons {sty cty stys ctys} :
      lowerTy ke tvs sty = some cty →
      LowersFields ke tvs stys ctys →
      LowersFields ke tvs (sty :: stys) (cty :: ctys)

/-- Constructor list: names preserved, fields via `LowersFields`. -/
inductive LowersCtors (ke : KindEnv) (tvs : List ValName) :
    List (CtorName × List Surface.Ty) → List (CtorName × List Ty) → Prop
  | nil : LowersCtors ke tvs [] []
  | cons {n fs fs' rest rest'} :
      LowersFields ke tvs fs fs' →
      LowersCtors ke tvs rest rest' →
      LowersCtors ke tvs ((n, fs) :: rest) ((n, fs') :: rest')

/-- One surface decl lowers to a Core `DataDecl` against an ambient `KindEnv`. -/
inductive LowersDataDecl (ke : KindEnv) : Surface.DataDecl → DataDecl → Prop
  | mk {name params ctors ctors'} :
      params.Nodup →
      LowersCtors ke params ctors ctors' →
      LowersDataDecl ke
        ⟨name, params, ctors⟩
        ⟨name, params.length, ctors'⟩

/-- A surface decl group lowers under ambient kinds `ke₀`. -/
structure LowersDataDeclsIn (ke₀ : KindEnv)
    (sdecls : List Surface.DataDecl) (decls : List DataDecl) : Prop where
  tyNamesNodup : (sdecls.map (·.name)).Nodup
  ctorNamesNodup :
    (sdecls.flatMap (fun d => d.ctors.map Prod.fst)).Nodup
  lowers :
    List.Forall₂ (LowersDataDecl (declKindEnv ke₀ sdecls)) sdecls decls

/-- Closed-group specialization (`ke₀ = []`). -/
abbrev LowersDataDecls (sdecls : List Surface.DataDecl) (decls : List DataDecl) : Prop :=
  LowersDataDeclsIn [] sdecls decls

/-- Lower one surface decl against a kind env. -/
def lowerDataDecl (ke : KindEnv) (s : Surface.DataDecl) : Option DataDecl := do
  guard s.params.Nodup
  let ctors' ← s.ctors.mapM fun (n, fs) =>
    (lowerTyList ke s.params fs).map fun fs' => (n, fs')
  pure ⟨s.name, s.params.length, ctors'⟩

/-- Lower a surface decl group under ambient kinds `ke₀`. -/
def lowerDataDeclsIn (ke₀ : KindEnv) (sdecls : List Surface.DataDecl) :
    Option (List DataDecl) := do
  guard ((sdecls.map (·.name)).Nodup)
  guard ((sdecls.flatMap (fun d => d.ctors.map Prod.fst)).Nodup)
  let ke := declKindEnv ke₀ sdecls
  sdecls.mapM (lowerDataDecl ke)

/-- Closed-group specialization (`ke₀ = []`). -/
def lowerDataDecls (sdecls : List Surface.DataDecl) : Option (List DataDecl) :=
  lowerDataDeclsIn [] sdecls

/-- A successful `mapM` yields pointwise `f a = some b`. -/
private theorem mapM_forall₂_of_eq {α β : Type} (f : α → Option β) :
    ∀ {l vs}, l.mapM f = some vs → List.Forall₂ (fun a b => f a = some b) l vs
  | [], vs => by
    intro h; rw [List.mapM_nil] at h; injection h with hvs; subst hvs; exact .nil
  | a :: l, vs => by
    intro h
    rw [List.mapM_cons] at h
    cases hfa : f a with
    | none => simp [hfa] at h
    | some b =>
      cases hrest : l.mapM f with
      | none => simp [hrest] at h
      | some rest =>
        rw [hfa, hrest] at h
        simp only [Option.bind_eq_bind, Option.bind_some, Option.pure_def,
          Option.some.injEq] at h
        obtain rfl := h.symm
        exact .cons hfa (mapM_forall₂_of_eq f hrest)

/-- Converse: pointwise `f a = some b` makes `mapM` succeed. -/
private theorem mapM_of_forall₂_of_eq {α β : Type} (f : α → Option β) :
    ∀ {l vs}, List.Forall₂ (fun a b => f a = some b) l vs → l.mapM f = some vs
  | [], vs => by
    intro h; cases h; simp [List.mapM_nil]
  | a :: l, b :: vs => by
    intro h
    cases h with
    | cons hab htl =>
      simp [List.mapM_cons, hab, mapM_of_forall₂_of_eq f htl]
  | a :: l, [] => by
    intro h; cases h

private theorem Forall₂_length {α β : Type} (R : α → β → Prop) :
    ∀ {l1 l2}, List.Forall₂ R l1 l2 → l1.length = l2.length := by
  intro l1 l2 h
  induction h with
  | nil => rfl
  | cons _ htl ih => simp only [List.length_cons, ih]

private theorem Forall₂_mem_right {α β : Type} {R : α → β → Prop} :
    ∀ {l1 l2}, List.Forall₂ R l1 l2 → ∀ {b}, b ∈ l2 → ∃ a, a ∈ l1 ∧ R a b := by
  intro l1 l2 h
  induction h with
  | nil => intro b hb; simp at hb
  | cons hr htl ih =>
    intro b hb
    simp only [List.mem_cons] at hb
    rcases hb with rfl | hb
    · exact ⟨_, List.mem_cons_self, hr⟩
    · obtain ⟨a, ha, hr⟩ := ih hb
      exact ⟨a, List.mem_cons_of_mem _ ha, hr⟩

private theorem Forall₂_imp {α β : Type} {R S : α → β → Prop} (himp : ∀ {a b}, R a b → S a b) :
    ∀ {l1 l2}, List.Forall₂ R l1 l2 → List.Forall₂ S l1 l2 := by
  intro l1 l2 h
  induction h with
  | nil => exact .nil
  | cons hr htl ih => exact .cons (himp hr) ih

mutual
/-- `lowerTyList` success implies the declarative field-lowering relation. -/
theorem LowersFields.of_lowerTyList {ke : KindEnv} {tvs : List ValName}
    {ss : List Surface.Ty} {cs : List Ty}
    (h : lowerTyList ke tvs ss = some cs) : LowersFields ke tvs ss cs := by
  cases ss with
  | nil =>
    simp only [lowerTyList, Option.some.injEq] at h; subst h
    exact .nil
  | cons s ss =>
    simp only [lowerTyList] at h
    cases ht : lowerTy ke tvs s with
    | none => simp [ht] at h
    | some c =>
      cases hts : lowerTyList ke tvs ss with
      | none => simp [ht, hts] at h
      | some cs' =>
        simp only [ht, hts, Option.some.injEq] at h; subst h
        exact .cons ht (LowersFields.of_lowerTyList hts)

/-- The declarative field-lowering relation makes `lowerTyList` succeed. -/
theorem LowersFields.to_lowerTyList {ke : KindEnv} {tvs : List ValName}
    {ss : List Surface.Ty} {cs : List Ty}
    (h : LowersFields ke tvs ss cs) : lowerTyList ke tvs ss = some cs := by
  induction h with
  | nil => rfl
  | cons ht htl ih =>
    simp only [lowerTyList, ht, ih]
end

private theorem LowersFields.mem_lowerTy {ke : KindEnv} {tvs : List ValName}
    {stys : List Surface.Ty} {ctys : List Ty} (h : LowersFields ke tvs stys ctys) :
    ∀ {cty}, cty ∈ ctys → ∃ sty, sty ∈ stys ∧ lowerTy ke tvs sty = some cty := by
  induction h with
  | nil => intro cty hmem; simp at hmem
  | cons ht htl ih =>
    intro cty hmem
    simp only [List.mem_cons] at hmem
    rcases hmem with rfl | hmem
    · exact ⟨_, List.mem_cons_self, ht⟩
    · obtain ⟨sty, hsty, heq⟩ := ih hmem
      exact ⟨sty, List.mem_cons_of_mem _ hsty, heq⟩

private theorem LowersCtors.of_forall₂' {ke : KindEnv} {tvs : List ValName}
    {ss : List (CtorName × List Surface.Ty)} {cs : List (CtorName × List Ty)}
    (h : List.Forall₂
      (fun (nc, fs) (nc', fs') => nc = nc' ∧ LowersFields ke tvs fs fs') ss cs) :
    LowersCtors ke tvs ss cs := by
  revert cs
  induction ss with
  | nil =>
    intro cs h
    cases cs with
    | nil => exact .nil
    | cons _ _ => cases h
  | cons a ss ih =>
    intro cs h
    match cs with
    | [] => cases h
    | b :: cs =>
      match h with
      | List.Forall₂.cons hr htl =>
        rcases a with ⟨nc, fs⟩
        rcases b with ⟨nc', fs'⟩
        obtain ⟨hn, hfs⟩ := hr
        subst hn
        exact .cons hfs (ih htl)

private theorem LowersCtors.to_forall₂ {ke : KindEnv} {tvs : List ValName}
    {ss : List (CtorName × List Surface.Ty)} {cs : List (CtorName × List Ty)}
    (h : LowersCtors ke tvs ss cs) :
    List.Forall₂ (fun (nc, fs) (nc', fs') => nc = nc' ∧ LowersFields ke tvs fs fs') ss cs := by
  induction h with
  | nil => exact .nil
  | cons hfs htl ih => exact .cons ⟨rfl, hfs⟩ ih

private def lowerCtorFields (ke : KindEnv) (tvs : List ValName)
    (p : CtorName × List Surface.Ty) : Option (CtorName × List Ty) :=
  (lowerTyList ke tvs p.2).map fun fs' => (p.1, fs')

private theorem lowerDataDecl_sound {ke : KindEnv} {s : Surface.DataDecl} {d : DataDecl}
    (h : lowerDataDecl ke s = some d) : LowersDataDecl ke s d := by
  unfold lowerDataDecl at h
  obtain ⟨hp, hbind⟩ := option_guard_bind h
  obtain ⟨ctors', hmap⟩ := option_bind_eq_some_left hbind
  have hpure :
      (pure { name := s.name, paramCount := s.params.length, ctors := ctors' }) = some d := by
    have h' := hbind
    rw [hmap] at h'
    simp only [Option.bind_eq_bind, Option.bind_some, Option.pure_def] at h'
    exact h'
  have hct := mapM_forall₂_of_eq (lowerCtorFields ke s.params) hmap
  have hct' := Forall₂_imp
    (R := fun a b => lowerCtorFields ke s.params a = some b)
    (S := fun a b => a.1 = b.1 ∧ LowersFields ke s.params a.2 b.2)
    (fun {a b} h => by
      unfold lowerCtorFields at h
      obtain ⟨fs', hfs, heq⟩ := Option.map_eq_some_iff.mp h
      rcases b with ⟨nc, fs''⟩
      cases heq
      exact ⟨rfl, LowersFields.of_lowerTyList hfs⟩) hct
  have hctors := LowersCtors.of_forall₂' hct'
  have heq : d = ⟨s.name, s.params.length, ctors'⟩ := (Option.some.inj hpure).symm
  exact heq ▸ LowersDataDecl.mk hp hctors

private theorem lowerDataDecl_complete {ke : KindEnv} {s : Surface.DataDecl} {d : DataDecl}
    (h : LowersDataDecl ke s d) : lowerDataDecl ke s = some d := by
  rcases s with ⟨sname, params, sctors⟩
  rcases d with ⟨dname, pc, dctors⟩
  cases h with
  | mk hp hctors =>
    have hct := LowersCtors.to_forall₂ hctors
    have hct' := Forall₂_imp
      (R := fun a b => a.1 = b.1 ∧ LowersFields ke params a.2 b.2)
      (S := fun a b => lowerCtorFields ke params a = some b)
      (fun {a b} ⟨hn, hfs⟩ => by
        dsimp [lowerCtorFields]
        rw [LowersFields.to_lowerTyList hfs, Option.map_some, hn])
      hct
    have hmap := mapM_of_forall₂_of_eq (lowerCtorFields ke params) hct'
    rw [lowerDataDecl, option_guard_bind_pos hp]
    have hbind :
        (sctors.mapM (fun x =>
          (lowerTyList ke params x.2).map fun fs' => (x.1, fs'))) = some dctors := by
      simpa [lowerCtorFields] using hmap
    rw [hbind, Option.bind_eq_bind, Option.bind_some, Option.pure_def]

private theorem LowersCtors.flatMap_names_eq {ke : KindEnv} {tvs : List ValName}
    {ss : List (CtorName × List Surface.Ty)} {cs : List (CtorName × List Ty)}
    (h : LowersCtors ke tvs ss cs) :
    ss.map Prod.fst = cs.map Prod.fst := by
  induction h with
  | nil => rfl
  | cons _ htl ih => simp only [List.map_cons, ih]

private theorem LowersDataDeclsIn.map_names_eq {ke : KindEnv}
    {sdecls : List Surface.DataDecl} {decls : List DataDecl}
    (h : List.Forall₂ (LowersDataDecl ke) sdecls decls) :
    sdecls.map (·.name) = decls.map (·.name) := by
  induction h with
  | nil => rfl
  | cons hdecl htl ih =>
    cases hdecl with | mk _ _ =>
    simp only [List.map_cons, ih]

private theorem LowersDataDeclsIn.flatMap_ctorNames_eq {ke : KindEnv}
    {sdecls : List Surface.DataDecl} {decls : List DataDecl}
    (h : List.Forall₂ (LowersDataDecl ke) sdecls decls) :
    (sdecls.flatMap (fun d => d.ctors.map Prod.fst)) =
      (decls.flatMap (fun d => d.ctors.map Prod.fst)) := by
  induction h with
  | nil => rfl
  | cons hdecl htl ih =>
    cases hdecl with
    | mk _ hctors =>
      have hflat := LowersCtors.flatMap_names_eq hctors
      simp only [List.flatMap_cons, ih, hflat]

private theorem LowersDataDeclsIn.kindEnv_eq {ke : KindEnv}
    {sdecls : List Surface.DataDecl} {decls : List DataDecl}
    (h : List.Forall₂ (LowersDataDecl ke) sdecls decls) :
    surfaceKindEnv sdecls = DataDecls.kindEnv decls := by
  have hmap :
      sdecls.map (fun d => (d.name, d.params.length)) =
        decls.map (fun d => (d.name, d.paramCount)) := by
    induction h with
    | nil => rfl
    | cons hdecl htl ih =>
      cases hdecl with | mk _ _ =>
      simp only [List.map_cons, ih]
  simpa [surfaceKindEnv, DataDecls.kindEnv] using hmap

private theorem LowersCtors.fieldsWF {ke : KindEnv} {tvs : List ValName}
    {ctors : List (CtorName × List Surface.Ty)} {ctors' : List (CtorName × List Ty)}
    (h : LowersCtors ke tvs ctors ctors') :
    ∀ (c : CtorName × List Ty) (_ : c ∈ ctors'), ∀ ty ∈ c.2, Ty.WellKinded ke tvs.length ty := by
  induction h with
  | nil => intro c hc; simp at hc
  | cons hfs htl ih =>
    intro c hc ty hty
    rcases c with ⟨n, fs'⟩
    simp only [List.mem_cons] at hc
    rcases hc with ⟨rfl, hty⟩ | hc'
    · obtain ⟨_, _, hsty⟩ := LowersFields.mem_lowerTy hfs hty
      exact lowerTy_wellKinded hsty
    · exact ih ⟨n, fs'⟩ hc' ty hty

private theorem LowersDataDecl.fieldsWF {ke : KindEnv} {s : Surface.DataDecl} {d : DataDecl}
    (h : LowersDataDecl ke s d) : DataDecl.WF ke d := by
  cases h with
  | mk _ hctors =>
    intro c hc ty hty
    exact LowersCtors.fieldsWF hctors c hc ty hty

private theorem LookupList.get?_append_left {k v : Type} [DecidableEq k]
    (l l' : LookupList k v) (key : k) {val : v}
    (h : LookupList.get? l key = some val) :
    LookupList.get? (l ++ l') key = some val := by
  induction l generalizing key with
  | nil =>
    simp [LookupList.get?] at h
  | cons hd tl ih =>
    cases hd with
    | mk k' v' =>
      by_cases hk : key = k'
      · subst hk
        simp only [LookupList.get?] at h
        cases h
        simp only [LookupList.get?, List.cons_append]
        split_ifs <;> rfl
      · have htl : LookupList.get? tl key = some val := by
          simp [LookupList.get?, hk] at h
          exact h
        simp [LookupList.get?, List.cons_append, hk]
        exact ih key htl

private theorem Ty.WellKinded.weaken {ke ke' : KindEnv} {pc : Nat} {ty : Ty}
    (h : Ty.WellKinded ke pc ty) : Ty.WellKinded (ke ++ ke') pc ty := by
  cases h with
  | prim => exact .prim
  | bvar hi => exact .bvar hi
  | arrow ha hb => exact .arrow (Ty.WellKinded.weaken ha) (Ty.WellKinded.weaken hb)
  | customTy hget hargs =>
    exact .customTy (LookupList.get?_append_left ke ke' _ hget)
      (fun arg ha => Ty.WellKinded.weaken (hargs arg ha))

private theorem DataDecls.kindEnv_append (pre user : List DataDecl) :
    DataDecls.kindEnv (pre ++ user) = DataDecls.kindEnv pre ++ DataDecls.kindEnv user := by
  simp [DataDecls.kindEnv, List.map_append]

/-- Soundness: executable success implies the declarative relation. -/
theorem lowerDataDeclsIn_sound {ke₀ : KindEnv}
    {sdecls : List Surface.DataDecl} {decls : List DataDecl} :
    lowerDataDeclsIn ke₀ sdecls = some decls → LowersDataDeclsIn ke₀ sdecls decls := by
  intro h
  unfold lowerDataDeclsIn at h
  obtain ⟨hP1, h⟩ := option_guard_bind h
  obtain ⟨hP2, h⟩ := option_guard_bind h
  have hfor := mapM_forall₂_of_eq (lowerDataDecl (declKindEnv ke₀ sdecls)) h
  have hlowers := Forall₂_imp
    (R := fun s d => lowerDataDecl (declKindEnv ke₀ sdecls) s = some d)
    (S := LowersDataDecl (declKindEnv ke₀ sdecls))
    (fun {s d} hs => lowerDataDecl_sound hs) hfor
  exact { tyNamesNodup := hP1, ctorNamesNodup := hP2, lowers := hlowers }

/-- Completeness: the relation is realized by the executable lowerer. -/
theorem lowerDataDeclsIn_complete {ke₀ : KindEnv}
    {sdecls : List Surface.DataDecl} {decls : List DataDecl} :
    LowersDataDeclsIn ke₀ sdecls decls → lowerDataDeclsIn ke₀ sdecls = some decls := by
  intro h
  unfold lowerDataDeclsIn
  rw [option_guard_bind_pos h.tyNamesNodup, option_guard_bind_pos h.ctorNamesNodup]
  simp only
  rw [mapM_of_forall₂_of_eq _ (Forall₂_imp
    (R := LowersDataDecl (declKindEnv ke₀ sdecls))
    (S := fun s d => lowerDataDecl (declKindEnv ke₀ sdecls) s = some d)
    (fun {s d} hs => lowerDataDecl_complete hs) h.lowers)]

/-- Determinism of the relation. -/
theorem LowersDataDeclsIn.unique {ke₀ : KindEnv} {sdecls : List Surface.DataDecl}
    {decls decls' : List DataDecl} :
    LowersDataDeclsIn ke₀ sdecls decls → LowersDataDeclsIn ke₀ sdecls decls' →
      decls = decls' := by
  intro h1 h2
  exact Option.some.inj
    ((lowerDataDeclsIn_complete h1).symm.trans (lowerDataDeclsIn_complete h2))

/-- Closed-group payoff: related Core decls are well-formed on their own kind env. -/
theorem LowersDataDeclsIn.toWF {sdecls : List Surface.DataDecl} {decls : List DataDecl} :
    LowersDataDeclsIn [] sdecls decls → DataDecls.WF decls := by
  intro h
  have hke := LowersDataDeclsIn.kindEnv_eq h.lowers
  have hnames := LowersDataDeclsIn.map_names_eq h.lowers
  have hctors := LowersDataDeclsIn.flatMap_ctorNames_eq h.lowers
  exact {
    tyNamesNodup := hnames ▸ h.tyNamesNodup
    ctorNamesNodup := hctors ▸ h.ctorNamesNodup
    fields := fun d hd c hc ty hty => by
      obtain ⟨sd, _, hdecl⟩ := Forall₂_mem_right h.lowers hd
      have hwf := LowersDataDecl.fieldsWF hdecl
      have hke' : declKindEnv [] sdecls = DataDecls.kindEnv decls := by
        simpa [declKindEnv] using hke
      rw [hke'] at hwf
      exact hwf c hc ty hty
  }

/-- Prelude + user decls form a well-formed combined group.
    Declarative-side companion for `LowersProgram` witnesses; the executable
    `lowerProgram_sound` path gets the same fact from `elabDecls_sound` instead.
    Needs `Ty.WellKinded` weakening along kind-env extension + name disjointness. -/
theorem LowersDataDeclsIn.toCombinedWF
    {sdecls : List Surface.DataDecl} {userCore : List DataDecl}
    (hP : DataDecls.WF preludeDecls)
    (hU : LowersDataDeclsIn preludeKindEnv sdecls userCore)
    (hTy : (preludeDecls.map (·.name) ++ sdecls.map (·.name)).Nodup)
    (hCtor :
      ((preludeDecls.flatMap (fun d => d.ctors.map Prod.fst)) ++
        (sdecls.flatMap (fun d => d.ctors.map Prod.fst))).Nodup) :
    DataDecls.WF (preludeDecls ++ userCore) := by
  have hnames := LowersDataDeclsIn.map_names_eq hU.lowers
  have hctors := LowersDataDeclsIn.flatMap_ctorNames_eq hU.lowers
  have hkeUser := LowersDataDeclsIn.kindEnv_eq hU.lowers
  have hcombinedKe :
      DataDecls.kindEnv (preludeDecls ++ userCore) = declKindEnv preludeKindEnv sdecls := by
    rw [DataDecls.kindEnv_append, declKindEnv, preludeKindEnv, hkeUser]
  exact {
    tyNamesNodup := by simpa [List.map_append, hnames] using hTy
    ctorNamesNodup := by simpa [List.flatMap_append, hctors] using hCtor
    fields := fun d hd c hc ty hty => by
      rcases List.mem_append.mp hd with hdPre | hdUser
      · exact Ty.WellKinded.weaken (hP.fields d hdPre c hc ty hty)
      · obtain ⟨sd, _, hdecl⟩ := Forall₂_mem_right hU.lowers hdUser
        have hwf := LowersDataDecl.fieldsWF hdecl
        exact (hcombinedKe ▸ hwf) c hc ty hty
  }

/-- Closed-group soundness (abbrev API). -/
theorem lowerDataDecls_sound {sdecls : List Surface.DataDecl} {decls : List DataDecl} :
    lowerDataDecls sdecls = some decls → LowersDataDecls sdecls decls :=
  fun h => lowerDataDeclsIn_sound (by simpa [lowerDataDecls] using h)

/-- Closed-group completeness (abbrev API). -/
theorem lowerDataDecls_complete {sdecls : List Surface.DataDecl} {decls : List DataDecl} :
    LowersDataDecls sdecls decls → lowerDataDecls sdecls = some decls :=
  fun h => by simpa [lowerDataDecls] using lowerDataDeclsIn_complete h

theorem LowersDataDecls.unique {sdecls : List Surface.DataDecl}
    {decls decls' : List DataDecl} :
    LowersDataDecls sdecls decls → LowersDataDecls sdecls decls' → decls = decls' :=
  LowersDataDeclsIn.unique

theorem LowersDataDecls.toWF {sdecls : List Surface.DataDecl} {decls : List DataDecl} :
    LowersDataDecls sdecls decls → DataDecls.WF decls :=
  LowersDataDeclsIn.toWF

/-- Corollary: successful closed-group lowering yields a well-formed Core decl group. -/
theorem lowerDataDecls_WF {sdecls : List Surface.DataDecl} {decls : List DataDecl} :
    lowerDataDecls sdecls = some decls → DataDecls.WF decls :=
  fun h => LowersDataDecls.toWF (lowerDataDecls_sound h)

/-- Corollary: successful closed-group lowering elaborates into a `CtorEnv`. -/
theorem lowerDataDecls_elab {sdecls : List Surface.DataDecl} {decls : List DataDecl} :
    lowerDataDecls sdecls = some decls → (elabDecls decls).isSome :=
  fun h => elabDecls_complete (lowerDataDecls_WF h)

-- Adversarial `#guard`s for decl lowering.
private def sMaybe : Surface.DataDecl :=
  ⟨.mk "Maybe", [.mk "a"],
    [(.mk "Just", [.tvar (.mk "a")]), (.mk "Nothing", [])]⟩

private def sTree : Surface.DataDecl :=
  ⟨.mk "Tree", [.mk "a"],
    [(.mk "Node", [.tvar (.mk "a"), .customTy (.mk "Forest") [.tvar (.mk "a")]])]⟩

private def sForest : Surface.DataDecl :=
  ⟨.mk "Forest", [.mk "a"],
    [(.mk "FNil", []),
     (.mk "FCons", [.customTy (.mk "Tree") [.tvar (.mk "a")],
                    .customTy (.mk "Forest") [.tvar (.mk "a")]])]⟩

-- Maybe lowers and elaborates
#guard match lowerDataDecls [sMaybe] with
  | some decls => (elabDecls decls).isSome
  | none => false
#guard match lowerDataDecls [sMaybe] with
  | some [⟨.mk "Maybe", 1, [(.mk "Just", [.bvar 0]), (.mk "Nothing", [])]⟩] => true
  | _ => false
-- mutual Tree/Forest
#guard match lowerDataDecls [sTree, sForest] with
  | some decls => (elabDecls decls).isSome
  | none => false
-- duplicate type name fails
#guard (lowerDataDecls [sMaybe, sMaybe]).isNone
-- duplicate ctor name across the group fails
#guard (lowerDataDecls [
  ⟨.mk "A", [], [(.mk "C", [])]⟩,
  ⟨.mk "B", [], [(.mk "C", [])]⟩]).isNone
-- duplicate type params fail
#guard (lowerDataDecls [
  ⟨.mk "Dup", [.mk "a", .mk "a"], [(.mk "Mk", [])]⟩]).isNone
-- unbound tvar in a field fails
#guard (lowerDataDecls [
  ⟨.mk "Bad", [.mk "a"], [(.mk "Mk", [.tvar (.mk "z")])]⟩]).isNone
-- unknown type name in a field fails
#guard (lowerDataDecls [
  ⟨.mk "Bad", [], [(.mk "Mk", [.customTy (.mk "Nope") []])]⟩]).isNone
-- wrong arity fails
#guard (lowerDataDecls [
  ⟨.mk "Wrap", [], [(.mk "Mk", [.customTy (.mk "Wrap") [.prim .int]])]⟩]).isNone


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

/-! ### Free value-names (C0 — dependency analysis for future SCC)

Executable free-name collection under a bound-name scope. Reuses `patVars` for
pattern binders. This is **not** Infer’s job: Infer never sees a flat binding
list (surface already has `letRecIn`). Top-level SCC will use these free names
to build a dependency graph among `Binding`s, then emit `Program.groups`.

Future (not yet): collapse surface `letIn`/`letRecIn` into a single `letBlock`
and run this analysis in lowering so authors don’t declare SCCs by hand — still
one language layer, one desugar, no extra IR. -/

mutual
/-- Value names occurring free in `e` relative to `bound` (shadowing). -/
def freeNames (bound : List ValName) : Surface.Expr → List ValName
  | .primLit _ => []
  | .ctor _ => []
  | .var n => if n ∈ bound then [] else [n]
  | .pair a b => freeNames bound a ++ freeNames bound b
  | .cons h t => freeNames bound h ++ freeNames bound t
  | .list xs => freeNamesList bound xs
  | .app f x => freeNames bound f ++ freeNames bound x
  | .lambda p _ann body => freeNames (patVars p ++ bound) body
  | .letIn n _ann rhs body =>
      freeNames bound rhs ++ freeNames (n :: bound) body
  | .letRecIn binds body =>
      let bound' := binds.map (·.1) ++ bound
      freeNamesBinds bound' binds ++ freeNames bound' body
  | .ife c t f =>
      freeNames bound c ++ freeNames bound t ++ freeNames bound f
  | .match_ s brs => freeNames bound s ++ freeNamesBranches bound brs

def freeNamesList (bound : List ValName) : List Surface.Expr → List ValName
  | [] => []
  | e :: es => freeNames bound e ++ freeNamesList bound es

def freeNamesBinds (bound : List ValName) :
    List (ValName × Option Surface.PolyTy × Surface.Expr) → List ValName
  | [] => []
  | (_n, _ann, rhs) :: rest => freeNames bound rhs ++ freeNamesBinds bound rest

def freeNamesBranches (bound : List ValName) :
    List (Surface.Pattern × Surface.Expr) → List ValName
  | [] => []
  | (p, e) :: rest =>
      freeNames (patVars p ++ bound) e ++ freeNamesBranches bound rest
end

/-- Deduped free names (stable order of first occurrence). -/
def freeNamesD (bound : List ValName) (e : Surface.Expr) : List ValName :=
  (freeNames bound e).eraseDups

/-- Does binding `b`'s RHS freely mention value name `n`? (top-level / empty scope) -/
def Binding.refersTo (b : Surface.Binding) (n : ValName) : Bool :=
  n ∈ freeNames [] b.rhs

/-- Dependency edges among a flat binding list: `(src, dst)` means `src`'s RHS
    mentions `dst` (including self-loops for recursive singles). -/
def bindingDepEdges (binds : List Surface.Binding) : List (ValName × ValName) :=
  let names := binds.map (·.name)
  binds.flatMap fun b =>
    names.filterMap fun n =>
      if Binding.refersTo b n then some (b.name, n) else none

-- Free-name / dependency `#guard`s
#guard freeNamesD [] (.var (.mk "x")) = [.mk "x"]
#guard freeNamesD [] (.lambda (.name (.mk "x")) none (.var (.mk "x"))) = []
#guard freeNamesD [] (.lambda (.name (.mk "x")) none (.var (.mk "y"))) = [.mk "y"]
-- λ-bound name must not count as a free ref to a same-named outer
#guard freeNamesD [.mk "x"] (.lambda (.name (.mk "x")) none (.var (.mk "x"))) = []
#guard freeNamesD [] (.letIn (.mk "x") none (.var (.mk "y")) (.var (.mk "x"))) = [.mk "y"]
#guard freeNamesD [] (.letRecIn [(.mk "f", none, .var (.mk "f"))] (.var (.mk "f"))) = []
-- match binders shadow
#guard freeNamesD [] (.match_ (.var (.mk "s"))
  [(.name (.mk "x"), .var (.mk "x")), (.wildcard, .var (.mk "z"))]) = [.mk "s", .mk "z"]
-- binding dependency edges
#guard Binding.refersTo ⟨.mk "g", none, .var (.mk "f")⟩ (.mk "f") = true
#guard Binding.refersTo ⟨.mk "g", none, .lambda (.name (.mk "f")) none (.var (.mk "f"))⟩
  (.mk "f") = false
#guard (bindingDepEdges [
  ⟨.mk "f", none, .lambda (.name (.mk "x")) none (.app (.var (.mk "f")) (.var (.mk "x")))⟩,
  ⟨.mk "g", none, .var (.mk "f")⟩]).contains ((.mk "g", .mk "f"))
#guard (bindingDepEdges [
  ⟨.mk "f", none, .lambda (.name (.mk "x")) none (.app (.var (.mk "f")) (.var (.mk "x")))⟩,
  ⟨.mk "g", none, .var (.mk "f")⟩]).contains ((.mk "f", .mk "f"))


/-! ### C1 — naive SCC groups (mutual reachability + condensation topo)

Non-deterministic spec `ValidBindingGroups`: partition into SCCs of the
dependency graph, topo-ordered so callees are outer. Executable `sccGroups`
uses pairwise reachability (fine for small binding lists) + Kahn on the
condensation. Adequacy proofs are frozen with `sorry` for a follow-up handoff. -/

/-- Direct edge: some binding named `a` refers to `b`. -/
def DepEdge (binds : List Surface.Binding) (a b : ValName) : Prop :=
  ∃ bdg ∈ binds, bdg.name = a ∧ Binding.refersTo bdg b = true

/-- Reflexive-transitive closure of `DepEdge` (follow “depends on” edges). -/
inductive DepReach (binds : List Surface.Binding) : ValName → ValName → Prop
  | refl {a} : DepReach binds a a
  | tail {a b c} :
      DepEdge binds a b → DepReach binds b c → DepReach binds a c

def DepMutual (binds : List Surface.Binding) (a b : ValName) : Prop :=
  DepReach binds a b ∧ DepReach binds b a

/-- Declarative: `groups` is a valid SCC grouping of `binds` for desugaring.
    Intra-group order and order among incomparable SCCs are left free. -/
structure ValidBindingGroups
    (binds : List Surface.Binding) (groups : List (List Surface.Binding)) : Prop where
  namesNodup : (binds.map (·.name)).Nodup
  flatPerm : groups.flatten.Perm binds
  nonempty : ∀ g ∈ groups, g ≠ []
  sameScc :
    ∀ g ∈ groups, ∀ b1 ∈ g, ∀ b2 ∈ g, DepMutual binds b1.name b2.name
  maxScc :
    ∀ b1 ∈ binds, ∀ b2 ∈ binds,
      DepMutual binds b1.name b2.name → ∃ g ∈ groups, b1 ∈ g ∧ b2 ∈ g
  /-- Direct edge across groups ⇒ dependency’s group is strictly outer (smaller index). -/
  topo :
    ∀ (i j : Nat) (gi gj : List Surface.Binding),
      groups[i]? = some gi → groups[j]? = some gj → i ≠ j →
      ∀ b1 ∈ gi, ∀ b2 ∈ gj,
        Binding.refersTo b1 b2.name = true → j < i

/-- Successors of binding index `i`: indices `j` that `binds[i]` refers to. -/
def bindSucc (binds : List Surface.Binding) (i : Nat) : List Nat :=
  match binds[i]? with
  | none => []
  | some b =>
    (List.range binds.length).filterMap fun j =>
      match binds[j]? with
      | some b' => if Binding.refersTo b b'.name then some j else none
      | none => none

/-- Reachability in the index graph (empty path ⇒ `src = dst`). -/
def canReach (succ : Nat → List Nat) (fuel : Nat) (seen : List Nat)
    (src dst : Nat) : Bool :=
  if src = dst then true
  else match fuel with
  | 0 => false
  | fuel + 1 =>
    if src ∈ seen then false
    else (succ src).any fun n => canReach succ fuel (src :: seen) n dst

def mutuallyReachable (succ : Nat → List Nat) (fuel : Nat) (i j : Nat) : Bool :=
  canReach succ fuel [] i j && canReach succ fuel [] j i

/-- Partition indices `0..n-1` into mutual-reachability classes (stable: seed order). -/
def sccIndexSets (binds : List Surface.Binding) : List (List Nat) :=
  let n := binds.length
  let succ := bindSucc binds
  let fuelN := n
  let mutReach (i j : Nat) := mutuallyReachable succ fuelN i j
  let rec go (fuel : Nat) (todo : List Nat) (acc : List (List Nat)) : List (List Nat) :=
    match fuel with
    | 0 => acc
    | fuel + 1 =>
      match todo with
      | [] => acc
      | i :: _ =>
        let comp := todo.filter (mutReach i)
        let rest := todo.filter (fun j => !(mutReach i j))
        go fuel rest (acc ++ [comp])
  go (n + 1) (List.range n) []

/-- Does component `ca` directly depend on component `cb`? -/
def compDependsOn (succ : Nat → List Nat) (ca cb : List Nat) : Bool :=
  ca.any fun i => (succ i).any fun j => j ∈ cb

/-- Kahn edges `(u,v)` meaning `u` should appear before `v` in `groups`
    (dependency before dependent). -/
def sccBeforeEdges (succ : Nat → List Nat) (comps : List (List Nat)) :
    List (Nat × Nat) :=
  let nc := comps.length
  (List.range nc).flatMap fun a =>
    (List.range nc).filterMap fun b =>
      if a = b then none
      else
        match comps[a]?, comps[b]? with
        | some ca, some cb =>
          if compDependsOn succ ca cb then some (b, a) else none
        | _, _ => none

/-- Read `indeg[i]` (0 if OOB). -/
private def indegGet (indeg : List Nat) (i : Nat) : Nat :=
  indeg[i]?.getD 0

/-- Set `indeg[i] := v`. -/
private def indegSet (indeg : List Nat) (i v : Nat) : List Nat :=
  indeg.mapIdx fun j x => if j = i then v else x

/-- Kahn topological order on `0..n-1` given before-edges `(u,v)` (u before v). -/
def kahnTopo (n : Nat) (beforeEdges : List (Nat × Nat)) : List Nat :=
  let indeg0 : List Nat :=
    (List.range n).map fun v =>
      beforeEdges.filter (fun e => e.2 = v) |>.length
  let ready0 := (List.range n).filter fun v => indegGet indeg0 v = 0
  let rec go (fuel : Nat) (indeg : List Nat) (ready : List Nat) (acc : List Nat) :
      List Nat :=
    match fuel with
    | 0 => acc
    | fuel + 1 =>
      match ready with
      | [] => acc
      | u :: us =>
        let acc' := acc ++ [u]
        let nbrs := beforeEdges.filterMap fun ⟨a, b⟩ => if a = u then some b else none
        let indeg' := nbrs.foldl (fun ig b =>
          indegSet ig b (indegGet ig b - 1)) indeg
        let newReady := nbrs.filter fun b =>
          indegGet indeg' b = 0 && b ∉ acc' && b ∉ us
        go fuel indeg' (us ++ newReady) acc'
  go (n + 1) indeg0 ready0 []

/-- Map index sets through `binds` (skips OOB defensively). -/
def indexSetsToBindings (binds : List Surface.Binding) (sets : List (List Nat)) :
    List (List Surface.Binding) :=
  sets.map fun idxs =>
    idxs.filterMap fun i => binds[i]?

/-- Executable SCC grouping: `none` if binding names are not unique. -/
def sccGroups (binds : List Surface.Binding) :
    Option (List (List Surface.Binding)) := do
  guard (binds.map (·.name)).Nodup
  let succ := bindSucc binds
  let comps := sccIndexSets binds
  let order := kahnTopo comps.length (sccBeforeEdges succ comps)
  let ordered := order.filterMap fun k => comps[k]?
  pure (indexSetsToBindings binds ordered)

/-- Soundness: executable groups satisfy the declarative SCC spec. -/
theorem sccGroups_sound {binds : List Surface.Binding}
    {groups : List (List Surface.Binding)} :
    sccGroups binds = some groups → ValidBindingGroups binds groups := by
  sorry

/-- Completeness: some valid grouping exists ⇒ executable succeeds
    (not that it returns this exact `groups` — topo/intra-group order is free). -/
theorem sccGroups_complete {binds : List Surface.Binding}
    {groups : List (List Surface.Binding)} :
    ValidBindingGroups binds groups → (sccGroups binds).isSome := by
  sorry

-- SCC `#guard`s
private def bF : Surface.Binding :=
  ⟨.mk "f", none,
    .lambda (.name (.mk "x")) none (.app (.var (.mk "f")) (.var (.mk "x")))⟩
private def bG : Surface.Binding :=
  ⟨.mk "g", none, .var (.mk "f")⟩
private def bA : Surface.Binding :=
  ⟨.mk "a", none, .primLit (.int 1)⟩
private def bB : Surface.Binding :=
  ⟨.mk "b", none, .primLit (.int 2)⟩
private def bH : Surface.Binding :=
  ⟨.mk "h", none, .var (.mk "k")⟩
private def bK : Surface.Binding :=
  ⟨.mk "k", none, .var (.mk "h")⟩

-- g depends on f ⇒ [f]-group outer, then [g]
#guard match sccGroups [bF, bG] with
  | some [[⟨.mk "f", _, _⟩], [⟨.mk "g", _, _⟩]] => true
  | _ => false
-- mutual h↔ k ⇒ one group containing both (order inside free)
#guard match sccGroups [bH, bK] with
  | some [g] =>
      g.length = 2 && (g.map (·.name)).contains (.mk "h") &&
        (g.map (·.name)).contains (.mk "k")
  | _ => false
-- independent a, b ⇒ two singleton groups (stable by seed order)
#guard match sccGroups [bA, bB] with
  | some [[⟨.mk "a", _, _⟩], [⟨.mk "b", _, _⟩]] => true
  | _ => false
-- duplicate names rejected
#guard (sccGroups [bA, ⟨.mk "a", none, .primLit (.int 0)⟩]).isNone
-- empty
#guard match sccGroups [] with | some [] => true | _ => false


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

/-- **Occurrence typing context**: the ADT type known to sit at each occurrence
    the compiled tree may switch on. `[] ↦ scrutinee type` at the root; a case for
    ctor `c` extends it with `c`'s instantiated field types at the field
    occurrences `subOccs occ arity`. (Keyed by `Occ = List Nat`, which has
    `DecidableEq`, so `get?` works.) -/
abbrev OccCtx := LookupList Occ Ty

/-- A constructor's *instantiated* field types at type arguments `tyArgs`
    (`ctor.contents` with its `bvar` params replaced by `tyArgs`, via `Ty.openWith`
    — the functional twin of `InstantiatesBy`, bridged by `InstantiatesBy.eq_openWith`).
    `[]` if `c` is unknown. Computed (not existential) so the tree-coverage
    recursion below stays strictly positive. -/
def instFieldTys (ctors : CtorEnv) (c : CtorName) (tyArgs : List Ty) : List Ty :=
  ((LookupList.get? ctors c).map (fun ctor => ctor.contents.map (Ty.openWith tyArgs))).getD []

/-- Extend an occurrence context with a ctor's field-occurrence types. -/
def OccCtx.extend (octx : OccCtx) (occ : Occ) (fieldTys : List Ty) : OccCtx :=
  (subOccs occ fieldTys.length).zip fieldTys ++ octx

/-- **Syntactic (tree) exhaustiveness** of a compiled decision tree under an
    occurrence typing `octx`. This is the decidable coverage condition matching
    Core's `AllMatchesExhaustive` (item 6), robust to the pop rule because it
    types each switch by its *occurrence* (not by a positional column list):

    * a `leaf` is exhaustive (its body's exhaustiveness is a separate obligation);
    * a `switch occ cases .fail` (a COMPLETE signature — `emit` emits NO wildcard)
      is exhaustive iff `occ` holds an ADT `T`, every case tests a real ctor of
      `T` (with matching arity) whose subtree is exhaustive (fields typed by
      `instFieldTys`), and EVERY ctor of `T` in the env is tested (full coverage);
    * a `switch occ cases dflt` with `dflt ≠ .fail` (an emitted wildcard covers
      the rest) is exhaustive iff `occ` holds an ADT `T`, every case is a real
      ctor of `T` with an exhaustive subtree, and the default is exhaustive;
    * a bare `.fail` is NEVER exhaustive (an uncovered match). -/
inductive DTreeExhaustive (ctors : CtorEnv) : OccCtx → DTree → Prop
  | leaf {octx act binds} : DTreeExhaustive ctors octx (.leaf act binds)
  | switchFail {octx occ cases T tyArgs} :
      LookupList.get? octx occ = some (.customTy T tyArgs) →
      (∀ c a t, (c, a, t) ∈ cases →
        ∃ ctor, LookupList.get? ctors c = some ctor ∧ ctor.tyName = T ∧
          a = ctor.contents.length) →
      (∀ c a t, (c, a, t) ∈ cases →
        DTreeExhaustive ctors (OccCtx.extend octx occ (instFieldTys ctors c tyArgs)) t) →
      (∀ c ctor, LookupList.get? ctors c = some ctor → ctor.tyName = T →
        ∃ a t, (c, a, t) ∈ cases) →
      DTreeExhaustive ctors octx (.switch occ cases .fail)
  | switchDefault {octx occ cases dflt T tyArgs} :
      dflt ≠ .fail →
      LookupList.get? octx occ = some (.customTy T tyArgs) →
      (∀ c a t, (c, a, t) ∈ cases →
        ∃ ctor, LookupList.get? ctors c = some ctor ∧ ctor.tyName = T ∧
          a = ctor.contents.length) →
      (∀ c a t, (c, a, t) ∈ cases →
        DTreeExhaustive ctors (OccCtx.extend octx occ (instFieldTys ctors c tyArgs)) t) →
      DTreeExhaustive ctors octx dflt →
      DTreeExhaustive ctors octx (.switch occ cases dflt)

/-- **Syntactic exhaustiveness of one match's branch patterns** at scrutinee type
    `customTy T tyArgs`: the compiled decision tree is tree-exhaustive, starting
    from the root occurrence `[]` typed at the scrutinee's ADT type. This is the
    decidable, honest coverage condition (matches Core's `AllMatchesExhaustive`);
    `emit_compile_AllMatchesExhaustive` turns it into the real predicate on the
    emitted match. A flat "top-level ctors covered" check is UNSOUND (misses
    nested gaps: `Cons (Just x) t | Nil` leaves `Cons Nothing Nil` — the `Cons`
    sub-switch omits `Nothing`, so `DTreeExhaustive` fails there, correctly). -/
def MatchExhaustive (ctors : CtorEnv) (T : TyName) (tyArgs : List Ty)
    (ps : List Surface.Pattern) : Prop :=
  DTreeExhaustive ctors [([], .customTy T tyArgs)] (compile [[]] (initMatrix ps))

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
      -- `ife` desugars to a `True | False` match on `Bool`; its exhaustiveness
      -- depends on `ctors` having `Bool = {True, False}` (no rogue extra ctor),
      -- so carry the coverage witness here (as `match_` does).
      MatchExhaustive ctors nBool [] [.ctor cTrue [], .ctor cFalse []] →
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

mutual
theorem lowerExpr_isSome_of_LowersExpr {ctors : CtorEnv} {ke : KindEnv} {tvs : List ValName} :
    ∀ {vs : List ValName} {s : Surface.Expr} {c : Expr},
      LowersExpr ctors ke tvs vs s c → (lowerExpr ke tvs vs s).isSome := by
  intro vs s c h
  cases h with
  | primLitUnit | primLitInt | primLitNat | primLitChar | primLitBool | ctor =>
    simp [lowerExpr]
  | pair ha hb =>
    simp only [lowerExpr]
    obtain ⟨_, ha'⟩ := Option.isSome_iff_exists.mp (lowerExpr_isSome_of_LowersExpr ha)
    obtain ⟨_, hb'⟩ := Option.isSome_iff_exists.mp (lowerExpr_isSome_of_LowersExpr hb)
    simp [ha', hb']
  | cons ha hb =>
    simp only [lowerExpr]
    obtain ⟨_, ha'⟩ := Option.isSome_iff_exists.mp (lowerExpr_isSome_of_LowersExpr ha)
    obtain ⟨_, hb'⟩ := Option.isSome_iff_exists.mp (lowerExpr_isSome_of_LowersExpr hb)
    simp [ha', hb']
  | list hitems =>
    simp only [lowerExpr]
    obtain ⟨_, hi⟩ := Option.isSome_iff_exists.mp (lowerExprList_isSome_of_LowersExprList hitems)
    simp [hi]
  | lambda_name hann hb =>
    simp only [lowerExpr]
    obtain ⟨_, hb'⟩ := Option.isSome_iff_exists.mp (lowerExpr_isSome_of_LowersExpr hb)
    split at hann
    · subst hann; simp [lowerAnn, hb']
    · expose_names
      simp only [lowerAnn]
      have hmap : Option.map some (lowerTy ke tvs τ) = some ann' := by
        rwa [Option.map_eq_bind]
      simp [hmap, hb']
  | lambda_wild hann hb =>
    simp only [lowerExpr]
    obtain ⟨_, hb'⟩ := Option.isSome_iff_exists.mp (lowerExpr_isSome_of_LowersExpr hb)
    split at hann
    · subst hann; simp [lowerAnn, hb']
    · expose_names
      simp only [lowerAnn]
      have hmap : Option.map some (lowerTy ke tvs τ) = some ann' := by
        rwa [Option.map_eq_bind]
      simp [hmap, hb']
  | app hf hx =>
    simp only [lowerExpr]
    obtain ⟨_, hf'⟩ := Option.isSome_iff_exists.mp (lowerExpr_isSome_of_LowersExpr hf)
    obtain ⟨_, hx'⟩ := Option.isSome_iff_exists.mp (lowerExpr_isSome_of_LowersExpr hx)
    simp [hf', hx']
  | letIn hann hr hb =>
    simp only [lowerExpr]
    obtain ⟨_, hr'⟩ := Option.isSome_iff_exists.mp (lowerExpr_isSome_of_LowersExpr hr)
    obtain ⟨_, hb'⟩ := Option.isSome_iff_exists.mp (lowerExpr_isSome_of_LowersExpr hb)
    split at hann
    · subst hann; simp [lowerPolyAnn, hr', hb']
    · expose_names
      simp only [lowerPolyAnn]
      have hmap : Option.map some (lowerPoly ke σ) = some ann' := by
        rwa [Option.map_eq_bind]
      simp [hmap, hr', hb']
  | letRecIn hann hbinds hb =>
    simp only [lowerExpr]
    obtain ⟨_, hbinds'⟩ := Option.isSome_iff_exists.mp (lowerRecBinds_isSome_of_LowersRecBinds hbinds)
    obtain ⟨_, hb'⟩ := Option.isSome_iff_exists.mp (lowerExpr_isSome_of_LowersExpr hb)
    simp [hann, hbinds', hb']
  | var hi =>
    simp [lowerExpr, hi]
  | ife hc ht hf =>
    simp only [lowerExpr]
    obtain ⟨_, hc'⟩ := Option.isSome_iff_exists.mp (lowerExpr_isSome_of_LowersExpr hc)
    obtain ⟨_, ht'⟩ := Option.isSome_iff_exists.mp (lowerExpr_isSome_of_LowersExpr ht)
    obtain ⟨_, hf'⟩ := Option.isSome_iff_exists.mp (lowerExpr_isSome_of_LowersExpr hf)
    simp [hc', ht', hf']
  | match_ hs hbrs _hbeh =>
    simp only [lowerExpr]
    obtain ⟨_, hs'⟩ := Option.isSome_iff_exists.mp (lowerExpr_isSome_of_LowersExpr hs)
    obtain ⟨_, hbrs'⟩ := Option.isSome_iff_exists.mp (lowerBranches_isSome_of_LowersBranches hbrs)
    simp [hs', hbrs']

theorem lowerExprList_isSome_of_LowersExprList {ctors : CtorEnv} {ke : KindEnv} {tvs : List ValName} :
    ∀ {vs : List ValName} {es : List Surface.Expr} {es' : List Expr},
      LowersExprList ctors ke tvs vs es es' → (lowerExprList ke tvs vs es).isSome := by
  intro vs es es' h
  cases h with
  | nil => simp [lowerExprList]
  | cons he hrest =>
    simp only [lowerExprList]
    obtain ⟨_, he'⟩ := Option.isSome_iff_exists.mp (lowerExpr_isSome_of_LowersExpr he)
    obtain ⟨_, hrest'⟩ := Option.isSome_iff_exists.mp (lowerExprList_isSome_of_LowersExprList hrest)
    simp [he', hrest']

theorem lowerRecBinds_isSome_of_LowersRecBinds {ctors : CtorEnv} {ke : KindEnv} {tvs : List ValName} :
    ∀ {vs : List ValName} {binds : List (ValName × Option Surface.PolyTy × Surface.Expr)}
      {bindings' : List Expr},
      LowersRecBinds ctors ke tvs vs binds bindings' →
      (lowerRecBinds ke tvs vs binds).isSome := by
  intro vs binds bindings' h
  cases h with
  | nil => simp [lowerRecBinds]
  | cons he hrest =>
    simp only [lowerRecBinds]
    obtain ⟨_, he'⟩ := Option.isSome_iff_exists.mp (lowerExpr_isSome_of_LowersExpr he)
    obtain ⟨_, hrest'⟩ := Option.isSome_iff_exists.mp (lowerRecBinds_isSome_of_LowersRecBinds hrest)
    simp [he', hrest']

theorem lowerBranches_isSome_of_LowersBranches {ctors : CtorEnv} {ke : KindEnv} {tvs : List ValName} :
    ∀ {vs : List ValName} {brs : List (Surface.Pattern × Surface.Expr)} {bodies' : List Expr},
      LowersBranches ctors ke tvs vs brs bodies' →
      (lowerBranches ke tvs vs brs).isSome := by
  intro vs brs bodies' h
  cases h with
  | nil => simp [lowerBranches]
  | cons hb hrest =>
    simp only [lowerBranches]
    obtain ⟨_, hb'⟩ := Option.isSome_iff_exists.mp (lowerExpr_isSome_of_LowersExpr hb)
    obtain ⟨_, hrest'⟩ := Option.isSome_iff_exists.mp (lowerBranches_isSome_of_LowersBranches hrest)
    simp [hb', hrest']
end

theorem lower_complete {ctors : CtorEnv} {s : Surface.Expr} {c : Expr}
    (h : Lowers ctors s c) : (lower ctors s).isSome := by
  simp only [Lowers] at h
  exact lowerExpr_isSome_of_LowersExpr h

/-- Generalized: every row of `initMatrix ps k` has `pats = [norm p]` for the corresponding pattern. -/
theorem initMatrix_GPatWFList_shift {ctors : CtorEnv} {τ : Ty}
    (ps : List Surface.Pattern) (k : Nat)
    (hpwf : ∀ p ∈ ps, PatternWF ctors p τ) :
    ∀ r ∈ initMatrix ps k, GPatWFList ctors r.pats [τ] := by
  induction ps generalizing k with
  | nil => intro r hr; cases hr
  | cons p rest ih =>
    intro r hr
    simp only [initMatrix, List.mem_cons] at hr
    rcases hr with rfl | hr
    · exact .cons (PatternWF_to_GPatWF (hpwf p List.mem_cons_self)) .nil
    · exact ih (k + 1) (fun p' hp' => hpwf p' (List.mem_cons_of_mem _ hp')) r hr

/-- Rows of `initMatrix ps` are single-column `[norm p]` for each pattern `p`. -/
theorem initMatrix_GPatWFList {ctors : CtorEnv} {ps : List Surface.Pattern} {τ : Ty}
    (hpwf : ∀ p ∈ ps, PatternWF ctors p τ) :
    ∀ r ∈ initMatrix ps, GPatWFList ctors r.pats [τ] :=
  initMatrix_GPatWFList_shift ps 0 hpwf

mutual
theorem lowerExpr_LowersExpr {ctors : CtorEnv} {ke : KindEnv} {tvs : List ValName} :
    ∀ {vs : List ValName} {s : Surface.Expr} {c : Expr},
      lowerExpr ke tvs vs s = some c → LowersExpr ctors ke tvs vs s c := by
  intro vs s c h
  match s with
  | .primLit .unit =>
    simp only [lowerExpr, Option.some.injEq] at h; subst h; exact .primLitUnit
  | .primLit (.int n) =>
    simp only [lowerExpr, Option.some.injEq] at h; subst h; exact .primLitInt
  | .primLit (.nat n) =>
    simp only [lowerExpr, Option.some.injEq] at h; subst h; exact .primLitNat
  | .primLit (.char ch) =>
    simp only [lowerExpr, Option.some.injEq] at h; subst h; exact .primLitChar
  | .primLit (.bool b) =>
    simp only [lowerExpr, Option.some.injEq] at h; subst h; exact .primLitBool
  | .pair a b =>
    simp only [lowerExpr] at h
    cases ha : lowerExpr ke tvs vs a with
    | none => simp [ha] at h
    | some a' =>
      cases hb : lowerExpr ke tvs vs b with
      | none => simp [ha, hb] at h
      | some b' =>
        simp only [ha, hb, Option.some.injEq] at h; subst h
        exact .pair (lowerExpr_LowersExpr ha) (lowerExpr_LowersExpr hb)
  | .cons hd tl =>
    simp only [lowerExpr] at h
    cases ha : lowerExpr ke tvs vs hd with
    | none => simp [ha] at h
    | some h' =>
      cases hb : lowerExpr ke tvs vs tl with
      | none => simp [ha, hb] at h
      | some t' =>
        simp only [ha, hb, Option.some.injEq] at h; subst h
        exact .cons (lowerExpr_LowersExpr ha) (lowerExpr_LowersExpr hb)
  | .list items =>
    simp only [lowerExpr] at h
    cases hi : lowerExprList ke tvs vs items with
    | none => simp [hi] at h
    | some items' =>
      simp only [hi, Option.some.injEq] at h; subst h
      exact .list (lowerExprList_LowersExprList hi)
  | .lambda param paramAnn body =>
    simp only [lowerExpr] at h
    cases hann : lowerAnn ke tvs paramAnn with
    | none => simp [hann] at h
    | some ann' =>
      cases param with
      | name x =>
        cases hb : lowerExpr ke tvs (x :: vs) body with
        | none => simp [hann, hb] at h
        | some b' =>
          simp only [hann, hb, Option.some.injEq] at h; subst h
          refine .lambda_name ?_ (lowerExpr_LowersExpr hb)
          cases paramAnn with
          | none =>
            simp only [lowerAnn, Option.some.injEq] at hann
            subst hann; rfl
          | some τ =>
            simp only [lowerAnn] at hann
            obtain ⟨τ', hτ, rfl⟩ := Option.map_eq_some_iff.mp hann
            simp [hτ]
      | wildcard =>
        cases hb : lowerExpr ke tvs (.mk "_" :: vs) body with
        | none => simp [hann, hb] at h
        | some b' =>
          simp only [hann, hb, Option.some.injEq] at h; subst h
          refine .lambda_wild ?_ (lowerExpr_LowersExpr hb)
          cases paramAnn with
          | none =>
            simp only [lowerAnn, Option.some.injEq] at hann
            subst hann; rfl
          | some τ =>
            simp only [lowerAnn] at hann
            obtain ⟨τ', hτ, rfl⟩ := Option.map_eq_some_iff.mp hann
            simp [hτ]
      | ctor | pair | cons | list => simp [hann] at h
  | .app f x =>
    simp only [lowerExpr] at h
    cases hf : lowerExpr ke tvs vs f with
    | none => simp [hf] at h
    | some f' =>
      cases hx : lowerExpr ke tvs vs x with
      | none => simp [hf, hx] at h
      | some x' =>
        simp only [hf, hx, Option.some.injEq] at h; subst h
        exact .app (lowerExpr_LowersExpr hf) (lowerExpr_LowersExpr hx)
  | .letIn name ann rhs body =>
    simp only [lowerExpr] at h
    cases hann : lowerPolyAnn ke ann with
    | none => simp [hann] at h
    | some ann' =>
      cases hr : lowerExpr ke tvs vs rhs with
      | none => simp [hann, hr] at h
      | some rhs' =>
        cases hb : lowerExpr ke tvs (name :: vs) body with
        | none => simp [hann, hr, hb] at h
        | some body' =>
          simp only [hann, hr, hb, Option.some.injEq] at h; subst h
          refine .letIn ?_ (lowerExpr_LowersExpr hr) (lowerExpr_LowersExpr hb)
          cases ann with
          | none =>
            simp only [lowerPolyAnn, Option.some.injEq] at hann
            subst hann; rfl
          | some σ =>
            simp only [lowerPolyAnn] at hann
            obtain ⟨σ', hσ, rfl⟩ := Option.map_eq_some_iff.mp hann
            simp [hσ]
  | .letRecIn binds body =>
    simp only [lowerExpr] at h
    cases hann : lowerAnnList ke (binds.map (·.2.1)) with
    | none => simp [hann] at h
    | some anns' =>
      cases hbinds : lowerRecBinds ke tvs (binds.map (·.1) ++ vs) binds with
      | none => simp [hann, hbinds] at h
      | some bindings' =>
        cases hb : lowerExpr ke tvs (binds.map (·.1) ++ vs) body with
        | none => simp [hann, hbinds, hb] at h
        | some body' =>
          simp only [hann, hbinds, hb, Option.some.injEq] at h; subst h
          exact .letRecIn hann (lowerRecBinds_LowersRecBinds hbinds)
            (lowerExpr_LowersExpr hb)
  | .var name =>
    simp only [lowerExpr] at h
    cases hi : tvarIndex vs name with
    | none => simp [hi] at h
    | some i =>
      simp only [hi, Option.some.injEq] at h; subst h
      exact .var hi
  | .ctor name =>
    simp only [lowerExpr, Option.some.injEq] at h; subst h; exact .ctor
  | .ife c t f =>
    simp only [lowerExpr] at h
    cases hc : lowerExpr ke tvs vs c with
    | none => simp [hc] at h
    | some c' =>
      cases ht : lowerExpr ke tvs vs t with
      | none => simp [hc, ht] at h
      | some t' =>
        cases hf : lowerExpr ke tvs vs f with
        | none => simp [hc, ht, hf] at h
        | some f' =>
          simp only [hc, ht, hf, Option.some.injEq] at h; subst h
          exact .ife (lowerExpr_LowersExpr hc) (lowerExpr_LowersExpr ht)
            (lowerExpr_LowersExpr hf)
  | .match_ scrut brs =>
    simp only [lowerExpr] at h
    cases hs : lowerExpr ke tvs vs scrut with
    | none => simp [hs] at h
    | some scrut' =>
      cases hb : lowerBranches ke tvs vs brs with
      | none => simp [hs, hb] at h
      | some bodies' =>
        simp only [hs, hb, Option.some.injEq] at h; subst h
        -- c = lowerMatch scrut' (brs.map Prod.fst) (fun i => bodies'.getD i (.ctor cNil))
        -- = lowerMatch scrut' pats (bodyFn bodies')
        have hbodyFn : (fun i => bodies'.getD i (.ctor cNil)) = bodyFn bodies' := by
          funext i; rfl
        rw [hbodyFn]
        -- lowerMatch = .letIn none scrut' emitInner
        refine .match_ (lowerExpr_LowersExpr hs) (lowerBranches_LowersBranches hb) ?_
        intro T tyArgs root hval hty hpwf i ws hfm
        -- Need ReflTransGen Step (.letIn none root emitInner) ((bodyFn bodies' i).substN 0 ws)
        -- where emitInner is from lowerMatch scrut' ... = .letIn none scrut' emitInner
        -- Apply lowerMatch_adequate_of_typed with root, bodies := bodyFn bodies'
        have hwf := initMatrix_GPatWFList hpwf
        have := lowerMatch_adequate_of_typed hty hval (brs.map Prod.fst) (bodyFn bodies') hwf hfm
        -- this : ReflTransGen Step (lowerMatch root pats (bodyFn bodies')) (...)
        -- and lowerMatch root = .letIn none root (emit ...)
        simpa [lowerMatch] using this

theorem lowerExprList_LowersExprList {ctors : CtorEnv} {ke : KindEnv} {tvs : List ValName} :
    ∀ {vs : List ValName} {es : List Surface.Expr} {es' : List Expr},
      lowerExprList ke tvs vs es = some es' →
      LowersExprList ctors ke tvs vs es es' := by
  intro vs es es' h
  match es with
  | [] =>
    simp only [lowerExprList, Option.some.injEq] at h; subst h; exact .nil
  | e :: rest =>
    simp only [lowerExprList] at h
    cases he : lowerExpr ke tvs vs e with
    | none => simp [he] at h
    | some e' =>
      cases hrest : lowerExprList ke tvs vs rest with
      | none => simp [he, hrest] at h
      | some rest' =>
        simp only [he, hrest, Option.some.injEq] at h; subst h
        exact .cons (lowerExpr_LowersExpr he) (lowerExprList_LowersExprList hrest)

theorem lowerRecBinds_LowersRecBinds {ctors : CtorEnv} {ke : KindEnv} {tvs : List ValName} :
    ∀ {vs : List ValName} {binds : List (ValName × Option Surface.PolyTy × Surface.Expr)}
      {bindings' : List Expr},
      lowerRecBinds ke tvs vs binds = some bindings' →
      LowersRecBinds ctors ke tvs vs binds bindings' := by
  intro vs binds bindings' h
  match binds with
  | [] =>
    simp only [lowerRecBinds, Option.some.injEq] at h; subst h; exact .nil
  | b :: rest =>
    simp only [lowerRecBinds] at h
    cases he : lowerExpr ke tvs vs b.2.2 with
    | none => simp [he] at h
    | some e' =>
      cases hrest : lowerRecBinds ke tvs vs rest with
      | none => simp [he, hrest] at h
      | some rest' =>
        simp only [he, hrest, Option.some.injEq] at h; subst h
        exact .cons (lowerExpr_LowersExpr he) (lowerRecBinds_LowersRecBinds hrest)

theorem lowerBranches_LowersBranches {ctors : CtorEnv} {ke : KindEnv} {tvs : List ValName} :
    ∀ {vs : List ValName} {brs : List (Surface.Pattern × Surface.Expr)} {bodies' : List Expr},
      lowerBranches ke tvs vs brs = some bodies' →
      LowersBranches ctors ke tvs vs brs bodies' := by
  intro vs brs bodies' h
  match brs with
  | [] =>
    simp only [lowerBranches, Option.some.injEq] at h; subst h; exact .nil
  | (p, b) :: rest =>
    simp only [lowerBranches] at h
    cases hb : lowerExpr ke tvs (patVars p ++ vs) b with
    | none => simp [hb] at h
    | some b' =>
      cases hrest : lowerBranches ke tvs vs rest with
      | none => simp [hb, hrest] at h
      | some rest' =>
        simp only [hb, hrest, Option.some.injEq] at h; subst h
        exact .cons (lowerExpr_LowersExpr hb) (lowerBranches_LowersBranches hrest)
end

/-- **`lower` soundness:** the executable lowering satisfies the spec. Match case
    cites `lowerMatch_adequate_of_typed` via `PatternWF_to_GPatWF`. -/
theorem lower_sound {ctors : CtorEnv} {s : Surface.Expr} {c : Expr}
    (h : lower ctors s = some c) : Lowers ctors s c := by
  simp only [lower] at h
  exact lowerExpr_LowersExpr h


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

/-- `lowerTy` never emits free type variables (only `.bvar`/`.prim`/`.customTy`/`.arrow`). -/
theorem lowerTy_freeVars {ke : KindEnv} {tvs : List ValName} {s : Surface.Ty} {c : Ty}
    (h : lowerTy ke tvs s = some c) : c.freeVars = [] :=
  List.eq_nil_iff_forall_not_mem.mpr fun z =>
    NoFreeVars.not_mem_freeVars (Ty.WellKinded.toNoFreeVars (lowerTy_wellKinded h)) z

theorem lowerPoly_freeVars {ke : KindEnv} {σ : Surface.PolyTy} {σ' : PolyTy}
    (h : lowerPoly ke σ = some σ') : σ'.body.freeVars = [] := by
  simp only [lowerPoly] at h
  obtain ⟨b, hb, rfl⟩ := Option.map_eq_some_iff.mp h
  exact lowerTy_freeVars hb

theorem lowerAnn_freeVars {ke : KindEnv} {tvs : List ValName} {ann : Option Surface.Ty}
    {ann' : Option Ty} (h : lowerAnn ke tvs ann = some ann') :
    ann'.elim [] Ty.freeVars = [] := by
  cases ann with
  | none =>
    simp only [lowerAnn, Option.some.injEq] at h; subst h; rfl
  | some τ =>
    simp only [lowerAnn] at h
    obtain ⟨c, hc, rfl⟩ := Option.map_eq_some_iff.mp h
    simp [lowerTy_freeVars hc]

theorem lowerPolyAnn_freeVars {ke : KindEnv} {ann : Option Surface.PolyTy}
    {ann' : Option PolyTy} (h : lowerPolyAnn ke ann = some ann') :
    ann'.elim [] (fun σ => σ.body.freeVars) = [] := by
  cases ann with
  | none =>
    simp only [lowerPolyAnn, Option.some.injEq] at h; subst h; rfl
  | some σ =>
    simp only [lowerPolyAnn] at h
    obtain ⟨σ', hσ, rfl⟩ := Option.map_eq_some_iff.mp h
    simp [lowerPoly_freeVars hσ]

theorem lowerAnnList_freeVars {ke : KindEnv} :
    ∀ {as : List (Option Surface.PolyTy)} {as' : List (Option PolyTy)},
      lowerAnnList ke as = some as' →
      Expr.tyFreeVars.AnnList.tyFreeVars as' = []
  | [], as', h => by
    simp only [lowerAnnList, Option.some.injEq] at h; subst h; rfl
  | a :: as, as', h => by
    simp only [lowerAnnList] at h
    cases ha : lowerPolyAnn ke a with
    | none => simp [ha] at h
    | some a' =>
      cases has : lowerAnnList ke as with
      | none => simp [ha, has] at h
      | some as'' =>
        simp only [ha, has, Option.some.injEq] at h; subst h
        simp only [Expr.tyFreeVars.AnnList.tyFreeVars, lowerPolyAnn_freeVars ha,
          lowerAnnList_freeVars has, List.nil_append]

/-- Public face of private `BranchList.shiftFrom` via `matchBranchesOf`. -/
private theorem shiftFrom_match_cons (scrut : Expr) (pat : MatchPattern)
    (body : Expr) (rest : List (MatchPattern × Expr)) (t n : Nat) :
    ((Expr.match_ scrut ((pat, body) :: rest)).shiftFrom t n).matchBranchesOf
      = (pat, body.shiftFrom (t + pat.bindCount) n)
        :: ((Expr.match_ scrut rest).shiftFrom t n).matchBranchesOf := rfl

private theorem shiftFrom_matchBranches (n : Nat) (scrut : Expr)
    (brs : List (MatchPattern × Expr)) (t : Nat) :
    ((Expr.match_ scrut brs).shiftFrom t n).matchBranchesOf
      = brs.map (fun pb => (pb.1, pb.2.shiftFrom (t + pb.1.bindCount) n)) := by
  induction brs generalizing t with
  | nil => rfl
  | cons hd tl ih =>
    obtain ⟨pat, body⟩ := hd
    rw [shiftFrom_match_cons, ih]
    simp only [List.map_cons]

private theorem shiftFrom_letRec_bridge (anns : List (Option PolyTy)) (e : Expr)
    (rest : List Expr) (body : Expr) (base n : Nat) :
    ((Expr.letRec anns (e :: rest) body).shiftFrom base n).letRecBindingsOf.tail
      = ((Expr.letRec anns rest body).shiftFrom (base + 1) n).letRecBindingsOf := by
  simp only [Expr.shiftFrom, Expr.letRecBindingsOf, List.length_cons]
  rw [show base + (rest.length + 1) = base + 1 + rest.length from by omega]
  rfl

private theorem shiftFrom_letRec_headtail (anns : List (Option PolyTy)) (e : Expr)
    (rest : List Expr) (body : Expr) (t n : Nat) :
    ((Expr.letRec anns (e :: rest) body).shiftFrom t n).letRecBindingsOf
      = e.shiftFrom (t + (e :: rest).length) n
        :: ((Expr.letRec anns (e :: rest) body).shiftFrom t n).letRecBindingsOf.tail := rfl

private theorem shiftFrom_letRecBindings (n : Nat) (bs : List Expr) (base : Nat)
    (anns : List (Option PolyTy)) (body : Expr) :
    ((Expr.letRec anns bs body).shiftFrom base n).letRecBindingsOf
      = bs.map (·.shiftFrom (base + bs.length) n) := by
  induction bs generalizing base with
  | nil => rfl
  | cons e rest ih =>
    rw [shiftFrom_letRec_headtail, shiftFrom_letRec_bridge, ih]
    simp only [List.map_cons, List.length_cons]
    congr 1
    apply List.map_congr_left
    intro x _; congr 1; omega

private theorem branchList_tyFreeVars_nil (brs : List (MatchPattern × Expr))
    (h : ∀ p e, (p, e) ∈ brs → e.tyFreeVars = []) :
    Expr.tyFreeVars.BranchList.tyFreeVars brs = [] := by
  induction brs with
  | nil => rfl
  | cons br rest ih =>
    simp only [Expr.tyFreeVars.BranchList.tyFreeVars, List.append_eq_nil_iff]
    exact ⟨h br.1 br.2 List.mem_cons_self, ih fun p e hp => h p e (List.mem_cons_of_mem _ hp)⟩

private theorem recGroup_tyFreeVars_nil (bs : List Expr)
    (h : ∀ e ∈ bs, e.tyFreeVars = []) :
    Expr.tyFreeVars.RecGroup.tyFreeVars bs = [] := by
  induction bs with
  | nil => rfl
  | cons e rest ih =>
    simp only [Expr.tyFreeVars.RecGroup.tyFreeVars, List.append_eq_nil_iff]
    exact ⟨h e List.mem_cons_self, ih fun e' he' => h e' (List.mem_cons_of_mem _ he')⟩

private theorem mem_of_branchList_tyFreeVars_nil (brs : List (MatchPattern × Expr))
    (h : Expr.tyFreeVars.BranchList.tyFreeVars brs = []) :
    ∀ p e, (p, e) ∈ brs → e.tyFreeVars = [] := by
  induction brs with
  | nil => intro _ _ he; cases he
  | cons br rest ih =>
    intro p e he
    simp only [Expr.tyFreeVars.BranchList.tyFreeVars, List.append_eq_nil_iff, List.mem_cons] at h he
    rcases he with he | he
    · obtain ⟨rfl, rfl⟩ := he; exact h.1
    · exact ih h.2 p e he

private theorem mem_of_recGroup_tyFreeVars_nil (bs : List Expr)
    (h : Expr.tyFreeVars.RecGroup.tyFreeVars bs = []) :
    ∀ e ∈ bs, e.tyFreeVars = [] := by
  induction bs with
  | nil => intro _ he; cases he
  | cons e rest ih =>
    intro e' he'
    simp only [Expr.tyFreeVars.RecGroup.tyFreeVars, List.append_eq_nil_iff, List.mem_cons] at h he'
    rcases he' with rfl | he'
    · exact h.1
    · exact ih h.2 e' he'

/-- Term-variable shifting does not introduce free type variables. -/
theorem Expr.tyFreeVars_shiftFrom (e : Expr) (threshold n : Nat)
    (h : e.tyFreeVars = []) : (e.shiftFrom threshold n).tyFreeVars = [] := by
  induction e using Expr.rec_strong generalizing threshold with
  | primLit | primBinOp | ctor =>
    simp only [Expr.shiftFrom, Expr.tyFreeVars] at *
  | var i tyArgs =>
    simp only [Expr.shiftFrom]
    split <;> simpa [Expr.tyFreeVars] using h
  | lambda ann body ih =>
    simp only [Expr.shiftFrom, Expr.tyFreeVars, List.append_eq_nil_iff] at h ⊢
    exact ⟨h.1, ih (threshold + 1) h.2⟩
  | app f arg ihf iharg =>
    simp only [Expr.shiftFrom, Expr.tyFreeVars, List.append_eq_nil_iff] at h ⊢
    exact ⟨ihf threshold h.1, iharg threshold h.2⟩
  | letIn ann rhs body ihrhs ihbody =>
    simp only [Expr.shiftFrom, Expr.tyFreeVars, List.append_eq_nil_iff] at h ⊢
    exact ⟨⟨h.1.1, ihrhs threshold h.1.2⟩, ihbody (threshold + 1) h.2⟩
  | match_ scrut branches ihscrut ihbr =>
    have heq : (Expr.match_ scrut branches).shiftFrom threshold n =
        .match_ (scrut.shiftFrom threshold n)
          ((Expr.match_ scrut branches).shiftFrom threshold n).matchBranchesOf := rfl
    rw [heq, shiftFrom_matchBranches]
    simp only [Expr.tyFreeVars, List.append_eq_nil_iff] at h ⊢
    refine ⟨ihscrut threshold h.1, branchList_tyFreeVars_nil _ ?_⟩
    intro p e hin
    obtain ⟨pb, hpb, heq'⟩ := List.mem_map.mp hin
    cases heq'
    exact ihbr pb.1 pb.2 hpb (threshold + pb.1.bindCount)
      (mem_of_branchList_tyFreeVars_nil branches h.2 pb.1 pb.2 hpb)
  | letRec anns bindings body ihbind ihbody =>
    have heq : (Expr.letRec anns bindings body).shiftFrom threshold n =
        .letRec anns ((Expr.letRec anns bindings body).shiftFrom threshold n).letRecBindingsOf
          (body.shiftFrom (threshold + bindings.length) n) := rfl
    rw [heq, shiftFrom_letRecBindings]
    simp only [Expr.tyFreeVars, List.append_eq_nil_iff] at h ⊢
    refine ⟨⟨h.1.1, recGroup_tyFreeVars_nil _ ?_⟩, ihbody (threshold + bindings.length) h.2⟩
    intro e he
    obtain ⟨e0, he0, rfl⟩ := List.mem_map.mp he
    exact ihbind e0 he0 (threshold + bindings.length)
      (mem_of_recGroup_tyFreeVars_nil bindings h.1.2 e0 he0)

private theorem emitLets_tyFreeVars (env : List Occ) (binds : List Occ) (body : Expr)
    (hb : body.tyFreeVars = []) :
    (emitLets env binds body).tyFreeVars = [] := by
  unfold emitLets
  have hshift : (body.shiftFrom binds.length env.length).tyFreeVars = [] :=
    Expr.tyFreeVars_shiftFrom body _ _ hb
  suffices ∀ rest depth,
      (emitLets.go env binds body rest depth).tyFreeVars = [] from this _ _
  intro rest; induction rest with
  | nil => intro depth; exact hshift
  | cons _ rest ih =>
    intro depth
    simp only [emitLets.go, Expr.tyFreeVars, List.append_eq_nil_iff]
    exact ⟨⟨rfl, rfl⟩, ih (depth + 1)⟩

mutual
private theorem emit_tyFreeVars (env : List Occ) (bodies : Nat → Expr) (t : DTree)
    (hb : ∀ i, (bodies i).tyFreeVars = []) :
    (emit env bodies t).tyFreeVars = [] := by
  match t with
  | .fail =>
    rw [emit]
    simp only [Expr.tyFreeVars, Expr.tyFreeVars.BranchList.tyFreeVars, List.nil_append]
  | .leaf act binds =>
    rw [emit]
    exact emitLets_tyFreeVars env binds (bodies act) (hb act)
  | .switch occ cases dflt =>
    have happ : ∀ cs (e : Expr),
        Expr.tyFreeVars.BranchList.tyFreeVars (cs ++ [(.wildcard, e)]) =
          Expr.tyFreeVars.BranchList.tyFreeVars cs ++ e.tyFreeVars := by
      intro cs; induction cs with
      | nil => intro e; simp [Expr.tyFreeVars.BranchList.tyFreeVars]
      | cons _ tl ih =>
        intro e; simp [Expr.tyFreeVars.BranchList.tyFreeVars, ih]
    cases dflt with
    | fail =>
      rw [emit]
      have hcases := emitCases_tyFreeVars env bodies occ cases hb
      simp [Expr.tyFreeVars, resolveOcc, hcases]
    | leaf act binds =>
      rw [emit]
      have hcases := emitCases_tyFreeVars env bodies occ cases hb
      have hd := emit_tyFreeVars env bodies (.leaf act binds) hb
      simp only [Expr.tyFreeVars, resolveOcc]
      rw [happ, hcases, hd]
      simp
      intro h; cases h
    | switch occ' cases' dflt' =>
      rw [emit]
      have hcases := emitCases_tyFreeVars env bodies occ cases hb
      have hd := emit_tyFreeVars env bodies (.switch occ' cases' dflt') hb
      simp only [Expr.tyFreeVars, resolveOcc]
      rw [happ, hcases, hd]
      simp
      intro h; cases h


private theorem emitCases_tyFreeVars (env : List Occ) (bodies : Nat → Expr) (occ : Occ) :
    ∀ (cases : List (CtorName × Nat × DTree)),
      (∀ i, (bodies i).tyFreeVars = []) →
      Expr.tyFreeVars.BranchList.tyFreeVars (emitCases env bodies occ cases) = []
  | [], _ => rfl
  | (_c, a, t) :: rest, hb => by
    simp only [emitCases, Expr.tyFreeVars.BranchList.tyFreeVars, List.append_eq_nil_iff]
    exact ⟨emit_tyFreeVars (subOccs occ a ++ env) bodies t hb,
      emitCases_tyFreeVars env bodies occ rest hb⟩
end

theorem lowerMatch_tyFreeVars (scrut : Expr) (pats : List Surface.Pattern) (bodies : Nat → Expr)
    (hs : scrut.tyFreeVars = []) (hb : ∀ i, (bodies i).tyFreeVars = []) :
    (lowerMatch scrut pats bodies).tyFreeVars = [] := by
  simp only [lowerMatch, Expr.tyFreeVars, Option.elim, List.nil_append, hs]
  exact emit_tyFreeVars [[]] bodies (compile [[]] (initMatrix pats)) hb

theorem mkList_tyFreeVars :
    ∀ (items : List Expr), (∀ e ∈ items, e.tyFreeVars = []) → (mkList items).tyFreeVars = []
  | [], _ => rfl
  | x :: xs, h => by
    simp only [mkList, Expr.tyFreeVars, List.nil_append, List.append_eq_nil_iff]
    exact ⟨h x List.mem_cons_self, mkList_tyFreeVars xs fun e he =>
      h e (List.mem_cons_of_mem _ he)⟩

mutual
theorem lowerExpr_tyFreeVars {ke : KindEnv} {tvs vs : List ValName} :
    ∀ {s : Surface.Expr} {c : Expr},
      lowerExpr ke tvs vs s = some c → c.tyFreeVars = [] := by
  intro s c h
  match s with
  | .primLit (.bool _) =>
    simp only [lowerExpr, Option.some.injEq] at h; subst h; rfl
  | .primLit .unit | .primLit (.int _) | .primLit (.nat _) | .primLit (.char _) =>
    simp only [lowerExpr, Option.some.injEq] at h; subst h; rfl
  | .pair a b =>
    simp only [lowerExpr] at h
    cases ha : lowerExpr ke tvs vs a with
    | none => simp [ha] at h
    | some a' =>
      cases hb : lowerExpr ke tvs vs b with
      | none => simp [ha, hb] at h
      | some b' =>
        simp only [ha, hb, Option.some.injEq] at h; subst h
        simp [Expr.tyFreeVars, lowerExpr_tyFreeVars ha, lowerExpr_tyFreeVars hb]
  | .cons hd tl =>
    simp only [lowerExpr] at h
    cases ha : lowerExpr ke tvs vs hd with
    | none => simp [ha] at h
    | some h' =>
      cases hb : lowerExpr ke tvs vs tl with
      | none => simp [ha, hb] at h
      | some t' =>
        simp only [ha, hb, Option.some.injEq] at h; subst h
        simp [Expr.tyFreeVars, lowerExpr_tyFreeVars ha, lowerExpr_tyFreeVars hb]
  | .list items =>
    simp only [lowerExpr] at h
    cases hi : lowerExprList ke tvs vs items with
    | none => simp [hi] at h
    | some items' =>
      simp only [hi, Option.some.injEq] at h; subst h
      exact mkList_tyFreeVars items' (lowerExprList_tyFreeVars hi)
  | .lambda param paramAnn body =>
    simp only [lowerExpr] at h
    cases hann : lowerAnn ke tvs paramAnn with
    | none => simp [hann] at h
    | some ann' =>
      cases param with
      | name x =>
        cases hb : lowerExpr ke tvs (x :: vs) body with
        | none => simp [hann, hb] at h
        | some b' =>
          simp only [hann, hb, Option.some.injEq] at h; subst h
          simp [Expr.tyFreeVars, lowerAnn_freeVars hann, lowerExpr_tyFreeVars hb]
      | wildcard =>
        cases hb : lowerExpr ke tvs (.mk "_" :: vs) body with
        | none => simp [hann, hb] at h
        | some b' =>
          simp only [hann, hb, Option.some.injEq] at h; subst h
          simp [Expr.tyFreeVars, lowerAnn_freeVars hann, lowerExpr_tyFreeVars hb]
      | ctor | pair | cons | list => simp [hann] at h
  | .app f x =>
    simp only [lowerExpr] at h
    cases hf : lowerExpr ke tvs vs f with
    | none => simp [hf] at h
    | some f' =>
      cases hx : lowerExpr ke tvs vs x with
      | none => simp [hf, hx] at h
      | some x' =>
        simp only [hf, hx, Option.some.injEq] at h; subst h
        simp [Expr.tyFreeVars, lowerExpr_tyFreeVars hf, lowerExpr_tyFreeVars hx]
  | .letIn name ann rhs body =>
    simp only [lowerExpr] at h
    cases hann : lowerPolyAnn ke ann with
    | none => simp [hann] at h
    | some ann' =>
      cases hr : lowerExpr ke tvs vs rhs with
      | none => simp [hann, hr] at h
      | some rhs' =>
        cases hb : lowerExpr ke tvs (name :: vs) body with
        | none => simp [hann, hr, hb] at h
        | some body' =>
          simp only [hann, hr, hb, Option.some.injEq] at h; subst h
          simp [Expr.tyFreeVars, lowerPolyAnn_freeVars hann,
            lowerExpr_tyFreeVars hr, lowerExpr_tyFreeVars hb]
  | .letRecIn binds body =>
    simp only [lowerExpr] at h
    cases hann : lowerAnnList ke (binds.map (·.2.1)) with
    | none => simp [hann] at h
    | some anns' =>
      cases hbinds : lowerRecBinds ke tvs (binds.map (·.1) ++ vs) binds with
      | none => simp [hann, hbinds] at h
      | some bindings' =>
        cases hb : lowerExpr ke tvs (binds.map (·.1) ++ vs) body with
        | none => simp [hann, hbinds, hb] at h
        | some body' =>
          simp only [hann, hbinds, hb, Option.some.injEq] at h; subst h
          simp [Expr.tyFreeVars, lowerAnnList_freeVars hann,
            lowerRecBinds_tyFreeVars hbinds, lowerExpr_tyFreeVars hb]
  | .var name =>
    simp only [lowerExpr] at h
    cases hi : tvarIndex vs name with
    | none => simp [hi] at h
    | some i =>
      simp only [hi, Option.some.injEq] at h; subst h
      simp [Expr.tyFreeVars]
  | .ctor name =>
    simp only [lowerExpr, Option.some.injEq] at h; subst h; rfl
  | .ife c t f =>
    simp only [lowerExpr] at h
    cases hc : lowerExpr ke tvs vs c with
    | none => simp [hc] at h
    | some c' =>
      cases ht : lowerExpr ke tvs vs t with
      | none => simp [hc, ht] at h
      | some t' =>
        cases hf : lowerExpr ke tvs vs f with
        | none => simp [hc, ht, hf] at h
        | some f' =>
          simp only [hc, ht, hf, Option.some.injEq] at h; subst h
          exact lowerMatch_tyFreeVars c' _ _ (lowerExpr_tyFreeVars hc) (fun i => by
            split <;> first | exact lowerExpr_tyFreeVars ht | exact lowerExpr_tyFreeVars hf)
  | .match_ scrut brs =>
    simp only [lowerExpr] at h
    cases hs : lowerExpr ke tvs vs scrut with
    | none => simp [hs] at h
    | some scrut' =>
      cases hb : lowerBranches ke tvs vs brs with
      | none => simp [hs, hb] at h
      | some bodies' =>
        simp only [hs, hb, Option.some.injEq] at h; subst h
        exact lowerMatch_tyFreeVars scrut' _ (bodyFn bodies')
          (lowerExpr_tyFreeVars hs) (fun i => by
            change (bodies'.getD i matchBodyDefault).tyFreeVars = []
            rw [List.getD]
            cases hget : bodies'[i]? with
            | none => simp [Option.getD, matchBodyDefault, Expr.tyFreeVars]
            | some e =>
              simp only [Option.getD]
              exact lowerBranches_tyFreeVars hb e (List.mem_of_getElem? hget))

theorem lowerExprList_tyFreeVars {ke : KindEnv} {tvs vs : List ValName} :
    ∀ {es : List Surface.Expr} {es' : List Expr},
      lowerExprList ke tvs vs es = some es' →
      ∀ e ∈ es', e.tyFreeVars = [] := by
  intro es es' h e he
  match es with
  | [] =>
    simp only [lowerExprList, Option.some.injEq] at h; subst h; cases he
  | e0 :: rest =>
    simp only [lowerExprList] at h
    cases he0 : lowerExpr ke tvs vs e0 with
    | none => simp [he0] at h
    | some e0' =>
      cases hrest : lowerExprList ke tvs vs rest with
      | none => simp [he0, hrest] at h
      | some rest' =>
        simp only [he0, hrest, Option.some.injEq] at h; subst h
        simp only [List.mem_cons] at he
        rcases he with rfl | he
        · exact lowerExpr_tyFreeVars he0
        · exact lowerExprList_tyFreeVars hrest e he

theorem lowerBranches_tyFreeVars {ke : KindEnv} {tvs vs : List ValName} :
    ∀ {brs : List (Surface.Pattern × Surface.Expr)} {bodies' : List Expr},
      lowerBranches ke tvs vs brs = some bodies' →
      ∀ e ∈ bodies', e.tyFreeVars = [] := by
  intro brs bodies' h e he
  match brs with
  | [] =>
    simp only [lowerBranches, Option.some.injEq] at h; subst h; cases he
  | (p, b) :: rest =>
    simp only [lowerBranches] at h
    cases hb : lowerExpr ke tvs (patVars p ++ vs) b with
    | none => simp [hb] at h
    | some b' =>
      cases hrest : lowerBranches ke tvs vs rest with
      | none => simp [hb, hrest] at h
      | some rest' =>
        simp only [hb, hrest, Option.some.injEq] at h; subst h
        simp only [List.mem_cons] at he
        rcases he with rfl | he
        · exact lowerExpr_tyFreeVars hb
        · exact lowerBranches_tyFreeVars hrest e he

theorem lowerRecBinds_tyFreeVars {ke : KindEnv} {tvs recScope : List ValName} :
    ∀ {binds : List (ValName × Option Surface.PolyTy × Surface.Expr)} {bindings' : List Expr},
      lowerRecBinds ke tvs recScope binds = some bindings' →
      Expr.tyFreeVars.RecGroup.tyFreeVars bindings' = [] := by
  intro binds bindings' h
  match binds with
  | [] =>
    simp only [lowerRecBinds, Option.some.injEq] at h; subst h; rfl
  | (_, _, e) :: rest =>
    simp only [lowerRecBinds] at h
    cases he : lowerExpr ke tvs recScope e with
    | none => simp [he] at h
    | some e' =>
      cases hrest : lowerRecBinds ke tvs recScope rest with
      | none => simp [he, hrest] at h
      | some rest' =>
        simp only [he, hrest, Option.some.injEq] at h; subst h
        simp [Expr.tyFreeVars.RecGroup.tyFreeVars, lowerExpr_tyFreeVars he,
          lowerRecBinds_tyFreeVars hrest]
end

/-- **(O2) Lowered programs are type-closed.** A `lower` output has no free type
    variables, so inference's rigid seed is empty and the frontier machinery
    disappears. Provable once `lower` is defined (it emits `bvar`-indexed types
    from the kind-checker; no `fvar`s). -/
theorem lower_tyClosed {ctors : CtorEnv} {s : Surface.Expr} {c : Expr}
    (h : lower ctors s = some c) : c.tyFreeVars = [] := by
  simp only [lower] at h
  exact lowerExpr_tyFreeVars h

/-- **(O3) Typechecking ⇒ inference succeeds (recovering the runtime term).**
    For a type-closed `c`, `typecheck` and `infer` run the *same* `inferCore`
    call (`principalType` seeds `c.tyFreeVars = []`, matching `infer`'s empty
    rigid set), so a successful `typecheck` yields the elaborated `(Φ',S,eOut,τ)`.
    Mechanical from `typecheck`/`principalType`/`infer` unfolding. -/
theorem infer_of_typecheck {ctors : CtorEnv} {c : Expr}
    (hclosed : c.tyFreeVars = []) (htc : (typecheck ctors c).isSome) :
    ∃ Φ' S eOut τ, infer c.freshFloor ⟨[], ctors⟩ c = some (Φ', S, eOut, τ) := by
  simp only [typecheck, principalType, Option.isSome_map] at htc
  rw [hclosed] at htc
  simp only [infer]
  rcases hcore : inferCore [] c.freshFloor ⟨[], ctors⟩ c with _ | ⟨⟨Φ', S, eOut, τ⟩, _⟩
  · simp [hcore] at htc
  · exact ⟨Φ', S, eOut, τ, by simp⟩

/-! ### O5 helpers

Transport across elaboration is mechanical (`AllMatchesExhaustive.substTyFvars`
in Core; `infer_preserves_AllMatchesExhaustive` via induction on `Infer`). The
crux (A) is now SYNTACTIC: `emit` of a `DTreeExhaustive` tree is
`AllMatchesExhaustive`, by induction on the coverage derivation — no semantic
totality, no inhabitation. -/

/-- `emitLets` (leaf `let`-cascade) preserves exhaustiveness: it wraps the body in
    `.letIn none (.var …)` binders (vars are exhaustive) over `body.shiftFrom …`
    (`AllMatchesExhaustive.shiftFrom`). -/
theorem emitLets_AllMatchesExhaustive {ctors : CtorEnv} (env binds : List Occ)
    {body : Expr} (h : AllMatchesExhaustive ctors body) :
    AllMatchesExhaustive ctors (emitLets env binds body) := by
  unfold emitLets
  have go_exh : ∀ (bs : List Occ) (depth : Nat),
      AllMatchesExhaustive ctors (emitLets.go env binds body bs depth) := by
    intro bs depth
    induction bs generalizing depth with
    | nil => exact AllMatchesExhaustive.shiftFrom h _ _
    | cons _b rest ih => exact .letIn .var (ih (depth + 1))
  exact go_exh binds.reverse 0

/-- `emitCases` as a `List.map` (local copy of PatComp's private lemma). -/
private theorem emitCases_eq_map' (env : List Occ) (bodies : Nat → Expr) (occ : Occ) :
    ∀ (cases : List (CtorName × Nat × DTree)),
      emitCases env bodies occ cases
        = cases.map (fun x => (MatchPattern.named x.1 x.2.1,
            emit (subOccs occ x.2.1 ++ env) bodies x.2.2))
  | [] => rfl
  | (_c, _a, _t) :: rest => by
    rw [emitCases, emitCases_eq_map' env bodies occ rest, List.map_cons]

/-- Membership: a case in `cases` yields the corresponding named branch in `emitCases`. -/
private theorem mem_emitCases_of_mem_cases (env : List Occ) (bodies : Nat → Expr)
    (occ : Occ) {cases : List (CtorName × Nat × DTree)} {c : CtorName} {a : Nat}
    {t : DTree} (h : (c, a, t) ∈ cases) :
    (MatchPattern.named c a, emit (subOccs occ a ++ env) bodies t) ∈
      emitCases env bodies occ cases := by
  rw [emitCases_eq_map']
  exact List.mem_map.mpr ⟨(c, a, t), h, rfl⟩

/-- Inverse membership: a named branch in `emitCases` comes from a case. -/
private theorem mem_cases_of_mem_emitCases (env : List Occ) (bodies : Nat → Expr)
    (occ : Occ) {cases : List (CtorName × Nat × DTree)} {c : CtorName} {n : Nat}
    {body : Expr}
    (h : (MatchPattern.named c n, body) ∈ emitCases env bodies occ cases) :
    ∃ t, (c, n, t) ∈ cases ∧ body = emit (subOccs occ n ++ env) bodies t := by
  rw [emitCases_eq_map'] at h
  obtain ⟨⟨c', a', t'⟩, hx, heq⟩ := List.mem_map.mp h
  obtain ⟨⟨rfl, rfl⟩, rfl⟩ := (Prod.mk.injEq _ _ _ _).mp heq
  exact ⟨t', hx, rfl⟩

/-- Branch bodies of `emitCases` are exhaustive when each case subtree is. -/
private theorem emitCases_AllBranchBodiesExhaustive {ctors : CtorEnv}
    (bodies : Nat → Expr) (env : List Occ) (occ : Occ)
    (cases : List (CtorName × Nat × DTree))
    (h : ∀ c a t, (c, a, t) ∈ cases →
      AllMatchesExhaustive ctors (emit (subOccs occ a ++ env) bodies t)) :
    AllBranchBodiesExhaustive ctors (emitCases env bodies occ cases) := by
  induction cases with
  | nil => exact .nil
  | cons hd tl ih =>
    obtain ⟨c, a, t⟩ := hd
    rw [emitCases]
    exact .cons (h c a t List.mem_cons_self)
      (ih fun c' a' t' hm => h c' a' t' (List.mem_cons_of_mem _ hm))

/-- Append a single exhaustive branch onto an exhaustive branch list. -/
private theorem AllBranchBodiesExhaustive.append_singleton {ctors : CtorEnv}
    {brs : List (MatchPattern × Expr)} {pat : MatchPattern} {body : Expr}
    (hbrs : AllBranchBodiesExhaustive ctors brs)
    (hbody : AllMatchesExhaustive ctors body) :
    AllBranchBodiesExhaustive ctors (brs ++ [(pat, body)]) := by
  induction brs with
  | nil => exact .cons hbody .nil
  | cons hd tl ih =>
    cases hbrs with
    | cons hb0 hrest => exact .cons hb0 (ih hrest)

/-- **(A-core) Emitting a tree-exhaustive decision tree yields an
    `AllMatchesExhaustive` Core term** — given the leaf bodies are exhaustive.
    Structural induction on the `DTreeExhaustive` derivation: `switchFail` uses
    the coverage clause (every ctor of `T` tested) for `AllMatchesExhaustive`'s
    cover obligation with no wildcard; `switchDefault`'s emitted wildcard covers
    the rest; the per-case ctor typing gives the "pinned" (named ctors ∈ `T`)
    obligation; `leaf` via `emitLets_AllMatchesExhaustive`. `env` is generalized
    (it only drives `resolveOcc`/leaf-lets, irrelevant to coverage). -/
theorem emit_DTreeExhaustive {ctors : CtorEnv} (bodies : Nat → Expr)
    (hbodies : ∀ i, AllMatchesExhaustive ctors (bodies i)) :
    ∀ {octx : OccCtx} {t : DTree}, DTreeExhaustive ctors octx t →
      ∀ (env : List Occ), AllMatchesExhaustive ctors (emit env bodies t) := by
  intro octx t hexh
  induction hexh with
  | leaf =>
    intro env
    simp only [emit]
    exact emitLets_AllMatchesExhaustive env _ (hbodies _)
  | @switchFail octx occ cases T tyArgs hlook htyped hsub hcover ih =>
    intro env
    change AllMatchesExhaustive ctors
      (.match_ (resolveOcc env occ) (emitCases env bodies occ cases ++ []))
    rw [List.append_nil]
    refine AllMatchesExhaustive.match_ (tyName := T) .var
      (emitCases_AllBranchBodiesExhaustive bodies env occ cases
        (fun c a t hm => ih c a t hm (subOccs occ a ++ env))) ?_ ?_
    · intro c n body hmem
      obtain ⟨t, ht, rfl⟩ := mem_cases_of_mem_emitCases env bodies occ hmem
      obtain ⟨ctor, hctor, hty, _⟩ := htyped c n t ht
      exact ⟨ctor, hctor, hty⟩
    · intro ctorName ctor hctor hty
      obtain ⟨a, t, ht⟩ := hcover ctorName ctor hctor hty
      obtain ⟨ctor', hctor', _, ha⟩ := htyped ctorName a t ht
      have hlen : a = ctor.contents.length := by
        have : ctor' = ctor := Option.some.inj (hctor'.symm.trans hctor)
        exact this ▸ ha
      refine ⟨.named ctorName a, emit (subOccs occ a ++ env) bodies t,
        mem_emitCases_of_mem_cases env bodies occ ht, ?_⟩
      simp only [MatchPattern.matchesCtor, Bool.and_eq_true, beq_iff_eq, true_and, hlen]
  | @switchDefault octx occ cases dflt T tyArgs hdne hlook htyped hsub hexh_dflt ih ihd =>
    intro env
    have hemit :
        emit env bodies (.switch occ cases dflt) =
          .match_ (resolveOcc env occ)
            (emitCases env bodies occ cases ++
              [(.wildcard, emit env bodies dflt)]) := by
      cases dflt with
      | fail => exact (hdne rfl).elim
      | leaf | switch => rfl
    rw [hemit]
    refine AllMatchesExhaustive.match_ (tyName := T) .var
      (AllBranchBodiesExhaustive.append_singleton
        (emitCases_AllBranchBodiesExhaustive bodies env occ cases
          (fun c a t hm => ih c a t hm (subOccs occ a ++ env)))
        (ihd env)) ?_ ?_
    · intro c n body hmem
      simp only [List.mem_append, List.mem_singleton] at hmem
      rcases hmem with hmem | hmem
      · obtain ⟨t, ht, rfl⟩ := mem_cases_of_mem_emitCases env bodies occ hmem
        obtain ⟨ctor, hctor, hty, _⟩ := htyped c n t ht
        exact ⟨ctor, hctor, hty⟩
      · nomatch hmem
    · intro ctorName ctor hctor hty
      exact ⟨.wildcard, emit env bodies dflt,
        by simp only [List.mem_append, List.mem_singleton, or_true], rfl⟩

/-- Corollary at a compiled match tree: `MatchExhaustive` (tree coverage) plus
    exhaustive branch bodies ⇒ the emitted match is `AllMatchesExhaustive`. -/
theorem emit_compile_AllMatchesExhaustive {ctors : CtorEnv} {T : TyName}
    {tyArgs : List Ty} (bodies : Nat → Expr) (ps : List Surface.Pattern)
    (hbodies : ∀ i, AllMatchesExhaustive ctors (bodies i))
    (hexh : MatchExhaustive ctors T tyArgs ps) :
    AllMatchesExhaustive ctors (emit [[]] bodies (compile [[]] (initMatrix ps))) := by
  unfold MatchExhaustive at hexh
  exact emit_DTreeExhaustive bodies hbodies hexh [[]]

/-- `mkList` of exhaustive elements is exhaustive. -/
private theorem mkList_AllMatchesExhaustive {ctors : CtorEnv} :
    ∀ (es : List Expr), (∀ e ∈ es, AllMatchesExhaustive ctors e) →
      AllMatchesExhaustive ctors (mkList es)
  | [], _ => .ctor
  | e :: rest, h =>
    .app (.app .ctor (h e List.mem_cons_self))
      (mkList_AllMatchesExhaustive rest fun e' he' => h e' (List.mem_cons_of_mem _ he'))

/-- Successful `lowerExprList` yields exhaustive Core terms when each surface item is covered. -/
private theorem lowerExprList_exhaustive {ctors : CtorEnv} {ke : KindEnv} {tvs : List ValName}
    {vs : List ValName} {es : List Surface.Expr} {es' : List Expr}
    (hcov : ∀ e ∈ es, SurfaceCovers ctors e)
    (ih : ∀ e ∈ es, ∀ {vs : List ValName} {c : Expr},
      lowerExpr ke tvs vs e = some c → AllMatchesExhaustive ctors c)
    (hlow : lowerExprList ke tvs vs es = some es') :
    (∀ e ∈ es', AllMatchesExhaustive ctors e) := by
  induction es generalizing es' with
  | nil =>
    simp only [lowerExprList, Option.some.injEq] at hlow; subst hlow
    intro _ he; exact nomatch he
  | cons e rest ih_es =>
    simp only [lowerExprList] at hlow
    cases he : lowerExpr ke tvs vs e with
    | none => simp [he] at hlow
    | some e' =>
      cases hr : lowerExprList ke tvs vs rest with
      | none => simp [he, hr] at hlow
      | some rest' =>
        simp only [he, hr, Option.some.injEq] at hlow; subst hlow
        intro x hx
        simp only [List.mem_cons] at hx
        rcases hx with rfl | hx
        · exact ih e List.mem_cons_self he
        · exact ih_es (fun e' he' => hcov e' (List.mem_cons_of_mem _ he'))
            (fun e' he' => ih e' (List.mem_cons_of_mem _ he')) hr x hx

/-- Successful `lowerRecBinds` yields exhaustive Core bindings. -/
private theorem lowerRecBinds_exhaustive {ctors : CtorEnv} {ke : KindEnv} {tvs : List ValName}
    {recScope : List ValName}
    {binds : List (ValName × Option Surface.PolyTy × Surface.Expr)} {bs' : List Expr}
    (hcov : ∀ b ∈ binds, SurfaceCovers ctors b.2.2)
    (ih : ∀ b ∈ binds, ∀ {vs : List ValName} {c : Expr},
      lowerExpr ke tvs vs b.2.2 = some c → AllMatchesExhaustive ctors c)
    (hlow : lowerRecBinds ke tvs recScope binds = some bs') :
    ∀ e ∈ bs', AllMatchesExhaustive ctors e := by
  induction binds generalizing bs' with
  | nil =>
    simp only [lowerRecBinds, Option.some.injEq] at hlow; subst hlow
    intro _ he; exact nomatch he
  | cons b rest ih_bs =>
    simp only [lowerRecBinds] at hlow
    cases he : lowerExpr ke tvs recScope b.2.2 with
    | none => simp [he] at hlow
    | some e' =>
      cases hr : lowerRecBinds ke tvs recScope rest with
      | none => simp [he, hr] at hlow
      | some rest' =>
        simp only [he, hr, Option.some.injEq] at hlow; subst hlow
        intro x hx
        simp only [List.mem_cons] at hx
        rcases hx with rfl | hx
        · exact ih b List.mem_cons_self he
        · exact ih_bs (fun b' hb' => hcov b' (List.mem_cons_of_mem _ hb'))
            (fun b' hb' => ih b' (List.mem_cons_of_mem _ hb')) hr x hx

/-- `lowerBranches` bodies (and the `.ctor cNil` default) are exhaustive. -/
private theorem lowerBranches_getD_exhaustive {ctors : CtorEnv} {ke : KindEnv}
    {tvs : List ValName} {vs : List ValName}
    {brs : List (Surface.Pattern × Surface.Expr)} {bodies' : List Expr}
    (hcov : ∀ p b, (p, b) ∈ brs → SurfaceCovers ctors b)
    (ih : ∀ p b, (p, b) ∈ brs → ∀ {vs : List ValName} {c : Expr},
      lowerExpr ke tvs vs b = some c → AllMatchesExhaustive ctors c)
    (hlow : lowerBranches ke tvs vs brs = some bodies') :
    ∀ i, AllMatchesExhaustive ctors (bodies'.getD i (.ctor cNil)) := by
  induction brs generalizing bodies' with
  | nil =>
    simp only [lowerBranches, Option.some.injEq] at hlow; subst hlow
    intro i; simp only [List.getD_nil]; exact .ctor
  | cons pb rest ih_brs =>
    obtain ⟨p, b⟩ := pb
    simp only [lowerBranches] at hlow
    cases hb : lowerExpr ke tvs (patVars p ++ vs) b with
    | none => simp [hb] at hlow
    | some b' =>
      cases hr : lowerBranches ke tvs vs rest with
      | none => simp [hb, hr] at hlow
      | some rest' =>
        simp only [hb, hr, Option.some.injEq] at hlow; subst hlow
        intro i
        cases i with
        | zero =>
          simp only [List.getD_cons_zero]
          exact ih p b List.mem_cons_self hb
        | succ i =>
          simp only [List.getD_cons_succ]
          exact ih_brs (fun p' b' hm => hcov p' b' (List.mem_cons_of_mem _ hm))
            (fun p' b' hm => ih p' b' (List.mem_cons_of_mem _ hm)) hr i

/-- Generalized: `SurfaceCovers` + successful `lowerExpr` ⇒ Core exhaustiveness. -/
theorem lowerExpr_exhaustive {ctors : CtorEnv} {ke : KindEnv} {tvs : List ValName} :
    ∀ {vs : List ValName} {s : Surface.Expr} {c : Expr},
      SurfaceCovers ctors s → lowerExpr ke tvs vs s = some c →
      AllMatchesExhaustive ctors c := by
  intro vs s c hcov hlow
  induction hcov generalizing vs c with
  | @primLit p =>
    cases p with
    | bool b =>
      simp only [lowerExpr, Option.some.injEq] at hlow; subst hlow; exact .ctor
    | unit =>
      simp only [lowerExpr, Option.some.injEq] at hlow; subst hlow; exact .primLit
    | int n =>
      simp only [lowerExpr, Option.some.injEq] at hlow; subst hlow; exact .primLit
    | nat n =>
      simp only [lowerExpr, Option.some.injEq] at hlow; subst hlow; exact .primLit
    | char ch =>
      simp only [lowerExpr, Option.some.injEq] at hlow; subst hlow; exact .primLit
  | @var n =>
    simp only [lowerExpr] at hlow
    cases hi : tvarIndex vs n with
    | none => simp [hi] at hlow
    | some i =>
      simp only [hi, Option.some.injEq] at hlow; subst hlow; exact .var
  | @ctor n =>
    simp only [lowerExpr, Option.some.injEq] at hlow; subst hlow; exact .ctor
  | @pair a b ha hb iha ihb =>
    simp only [lowerExpr] at hlow
    cases ha' : lowerExpr ke tvs vs a with
    | none => simp [ha'] at hlow
    | some a' =>
      cases hb' : lowerExpr ke tvs vs b with
      | none => simp [ha', hb'] at hlow
      | some b' =>
        simp only [ha', hb', Option.some.injEq] at hlow; subst hlow
        exact .app (.app .ctor (iha ha')) (ihb hb')
  | @cons h t hh ht ihh iht =>
    simp only [lowerExpr] at hlow
    cases hh' : lowerExpr ke tvs vs h with
    | none => simp [hh'] at hlow
    | some h' =>
      cases ht' : lowerExpr ke tvs vs t with
      | none => simp [hh', ht'] at hlow
      | some t' =>
        simp only [hh', ht', Option.some.injEq] at hlow; subst hlow
        exact .app (.app .ctor (ihh hh')) (iht ht')
  | @list items hitems ih =>
    simp only [lowerExpr] at hlow
    cases hi : lowerExprList ke tvs vs items with
    | none => simp [hi] at hlow
    | some items' =>
      simp only [hi, Option.some.injEq] at hlow; subst hlow
      exact mkList_AllMatchesExhaustive items'
        (lowerExprList_exhaustive hitems ih hi)
  | @lambda param ann body hb ihb =>
    simp only [lowerExpr] at hlow
    cases hann : lowerAnn ke tvs ann with
    | none => simp [hann] at hlow
    | some ann' =>
      cases param with
      | name x =>
        cases hb' : lowerExpr ke tvs (x :: vs) body with
        | none => simp [hann, hb'] at hlow
        | some b' =>
          simp only [hann, hb', Option.some.injEq] at hlow; subst hlow
          exact .lambda (ihb hb')
      | wildcard =>
        cases hb' : lowerExpr ke tvs (.mk "_" :: vs) body with
        | none => simp [hann, hb'] at hlow
        | some b' =>
          simp only [hann, hb', Option.some.injEq] at hlow; subst hlow
          exact .lambda (ihb hb')
      | ctor | pair | cons | list => simp [hann] at hlow
  | @app f x hf hx ihf ihx =>
    simp only [lowerExpr] at hlow
    cases hf' : lowerExpr ke tvs vs f with
    | none => simp [hf'] at hlow
    | some f' =>
      cases hx' : lowerExpr ke tvs vs x with
      | none => simp [hf', hx'] at hlow
      | some x' =>
        simp only [hf', hx', Option.some.injEq] at hlow; subst hlow
        exact .app (ihf hf') (ihx hx')
  | @letIn name ann rhs body hr hb ihr ihb =>
    simp only [lowerExpr] at hlow
    cases hann : lowerPolyAnn ke ann with
    | none => simp [hann] at hlow
    | some ann' =>
      cases hr' : lowerExpr ke tvs vs rhs with
      | none => simp [hann, hr'] at hlow
      | some rhs' =>
        cases hb' : lowerExpr ke tvs (name :: vs) body with
        | none => simp [hann, hr', hb'] at hlow
        | some body' =>
          simp only [hann, hr', hb', Option.some.injEq] at hlow; subst hlow
          exact .letIn (ihr hr') (ihb hb')
  | @letRecIn binds body hbinds hb ihbinds ihb =>
    simp only [lowerExpr] at hlow
    cases hann : lowerAnnList ke (binds.map (·.2.1)) with
    | none => simp [hann] at hlow
    | some anns' =>
      cases hbs : lowerRecBinds ke tvs (binds.map (·.1) ++ vs) binds with
      | none => simp [hann, hbs] at hlow
      | some bindings' =>
        cases hb' : lowerExpr ke tvs (binds.map (·.1) ++ vs) body with
        | none => simp [hann, hbs, hb'] at hlow
        | some body' =>
          simp only [hann, hbs, hb', Option.some.injEq] at hlow; subst hlow
          exact .letRec (lowerRecBinds_exhaustive hbinds ihbinds hbs) (ihb hb')
  | @ife cond t f hc ht hf hexh ihc iht ihf =>
    simp only [lowerExpr] at hlow
    cases hc' : lowerExpr ke tvs vs cond with
    | none => simp [hc'] at hlow
    | some c' =>
      cases ht' : lowerExpr ke tvs vs t with
      | none => simp [hc', ht'] at hlow
      | some t' =>
        cases hf' : lowerExpr ke tvs vs f with
        | none => simp [hc', ht', hf'] at hlow
        | some f' =>
          simp only [hc', ht', hf', Option.some.injEq] at hlow; subst hlow
          simp only [lowerMatch]
          refine .letIn (ihc hc')
            (emit_compile_AllMatchesExhaustive
              (fun i => if i = 0 then t' else f')
              [.ctor cTrue [], .ctor cFalse []]
              (fun i => by
                by_cases hi : i = 0
                · simp only [hi, ↓reduceIte]; exact iht ht'
                · simp only [hi, ↓reduceIte]; exact ihf hf')
              hexh)
  | @match_ scrut brs T tyArgs hs hbrs hexh ihs ihbrs =>
    simp only [lowerExpr] at hlow
    cases hs' : lowerExpr ke tvs vs scrut with
    | none => simp [hs'] at hlow
    | some scrut' =>
      cases hb' : lowerBranches ke tvs vs brs with
      | none => simp [hs', hb'] at hlow
      | some bodies' =>
        simp only [hs', hb', Option.some.injEq] at hlow; subst hlow
        simp only [lowerMatch]
        exact .letIn (ihs hs')
          (emit_compile_AllMatchesExhaustive
            (fun i => bodies'.getD i (.ctor cNil))
            (brs.map Prod.fst)
            (lowerBranches_getD_exhaustive hbrs ihbrs hb')
            hexh)

/-- **(A) Surface coverage + successful lowering ⇒ the Core term is exhaustive.**
    Induction on `SurfaceCovers` threaded through `lowerExpr`; the `match` case
    feeds `emit_compile_AllMatchesExhaustive` (its `MatchExhaustive` comes from the
    `SurfaceCovers.match_` witness, its exhaustive branch bodies from the recursive
    `SurfaceCovers` on the branches). No typing hypothesis needed — `DTreeExhaustive`
    is self-contained (it carries the tested ctors' env membership). -/
theorem lower_exhaustive {ctors : CtorEnv} {s : Surface.Expr} {c : Expr}
    (hcov : SurfaceCovers ctors s) (hlow : lower ctors s = some c) :
    AllMatchesExhaustive ctors c := by
  simp only [lower] at hlow
  exact lowerExpr_exhaustive hcov hlow

/-- `openTyVars` preserves exhaustiveness (via `instTy`). -/
private theorem AllMatchesExhaustive.openTyVars {ctors : CtorEnv} (Xs : List Nat)
    {e : Expr} (h : AllMatchesExhaustive ctors e) :
    AllMatchesExhaustive ctors (e.openTyVars Xs) := by
  rw [← Expr.instTy_fvar_eq_openTyVars]
  exact AllMatchesExhaustive.instTy _ h

/-- Local copy of private `BranchList.closeTyVarsAux_eq_map`. -/
private theorem closeTyVarsAux_match_eq (d : Nat) (Xs : List Nat) (scrut : Expr) :
    ∀ (brs : List (MatchPattern × Expr)),
      (Expr.match_ scrut brs).closeTyVarsAux d Xs =
        .match_ (scrut.closeTyVarsAux d Xs)
          (brs.map fun pb => (pb.1, pb.2.closeTyVarsAux d Xs))
  | [] => rfl
  | (p, b) :: rest => by
    have hrest := closeTyVarsAux_match_eq d Xs scrut rest
    simp only [Expr.closeTyVarsAux] at hrest ⊢
    injection hrest with _ hbr
    exact congrArg (fun t => Expr.match_ _ ((p, b.closeTyVarsAux d Xs) :: t)) hbr

/-- Local copy of private `RecGroup.closeTyVarsAux_eq_zip`. -/
private theorem closeTyVarsAux_letRec_eq (d : Nat) (Xs : List Nat) (body : Expr) :
    ∀ (anns : List (Option PolyTy)) (bs : List Expr),
      (Expr.letRec anns bs body).closeTyVarsAux d Xs =
        .letRec (RecGroup.closeAnns d Xs anns)
          ((bs.zip (RecGroup.shieldDepths d anns bs)).map
            fun p => p.1.closeTyVarsAux p.2 Xs)
          (body.closeTyVarsAux d Xs) := by
  intro anns bs
  induction bs generalizing anns with
  | nil => cases anns <;> rfl
  | cons e rest ih =>
    cases anns with
    | nil =>
      have hrest := ih ([] : List (Option PolyTy))
      simp only [Expr.closeTyVarsAux, RecGroup.shieldDepths, List.zip_cons_cons,
        List.map_cons, RecGroup.closeAnns_nil] at hrest ⊢
      injection hrest with _ hbind _
      exact congrArg (fun t => Expr.letRec _ (e.closeTyVarsAux d Xs :: t) _) hbind
    | cons a as =>
      have hrest := ih as
      simp only [Expr.closeTyVarsAux, RecGroup.shieldDepths, List.zip_cons_cons,
        List.map_cons, RecGroup.closeAnns_cons] at hrest ⊢
      injection hrest with _ hbind _
      exact congrArg
        (fun t => Expr.letRec _ (e.closeTyVarsAux (d + RecAnn.params a) Xs :: t) _) hbind

/-- Map-form of `AllBranchBodiesExhaustive` under `closeTyVarsAux`. -/
private theorem AllBranchBodiesExhaustive.closeTyVarsAux_map {ctors : CtorEnv}
    {d : Nat} {Xs : List Nat} :
    ∀ (brs : List (MatchPattern × Expr)),
      (∀ p b, (p, b) ∈ brs → AllMatchesExhaustive ctors b →
        AllMatchesExhaustive ctors (b.closeTyVarsAux d Xs)) →
      AllBranchBodiesExhaustive ctors brs →
      AllBranchBodiesExhaustive ctors
        (brs.map fun pb => (pb.1, pb.2.closeTyVarsAux d Xs))
  | [], _, _ => .nil
  | (p, b) :: rest, ih, h => by
    cases h with
    | cons hbody hrest =>
      exact .cons (ih p b List.mem_cons_self hbody)
        (AllBranchBodiesExhaustive.closeTyVarsAux_map rest
          (fun p' b' hm => ih p' b' (List.mem_cons_of_mem _ hm)) hrest)

/-- `closeTyVarsAux` preserves exhaustiveness. -/
private theorem AllMatchesExhaustive.closeTyVarsAux {ctors : CtorEnv}
    (Xs : List Nat) :
    ∀ (e : Expr) (d : Nat), AllMatchesExhaustive ctors e →
      AllMatchesExhaustive ctors (e.closeTyVarsAux d Xs) := by
  intro e
  induction e using Expr.rec_strong with
  | primLit p => intro _ _; exact .primLit
  | primBinOp op => intro _ h; exact h
  | var i tyArgs => intro _ _; exact .var
  | ctor nm => intro _ _; exact .ctor
  | lambda ann body ih =>
    intro d h; cases h with | lambda hb => exact .lambda (ih d hb)
  | app f arg ihf iharg =>
    intro d h; cases h with | app hf ha => exact .app (ihf d hf) (iharg d ha)
  | letIn ann rhs body ihr ihb =>
    intro d h; cases h with
    | letIn hr hb =>
      cases ann with
      | none => exact .letIn (ihr d hr) (ihb d hb)
      | some σ => exact .letIn (ihr (d + σ.paramCount) hr) (ihb d hb)
  | match_ scrut branches ihs ihbs =>
    intro d h
    cases h with
    | match_ hscrut hbranches hpinned hcover =>
      expose_names
      rw [closeTyVarsAux_match_eq]
      refine .match_ (tyName := tyName) (ihs d hscrut)
        (AllBranchBodiesExhaustive.closeTyVarsAux_map branches
          (fun p b hm hb => ihbs p b hm d hb) hbranches) ?_ ?_
      · intro c n body' hmem
        obtain ⟨⟨p, b⟩, hmem0, heq⟩ := List.mem_map.mp hmem
        simp only [Prod.mk.injEq] at heq; obtain ⟨rfl, rfl⟩ := heq
        exact hpinned c n b hmem0
      · intro ctorName ctor hlook htyn
        obtain ⟨pat, body, hmem, hcov⟩ := hcover ctorName ctor hlook htyn
        exact ⟨pat, body.closeTyVarsAux d Xs,
          List.mem_map.mpr ⟨(pat, body), hmem, rfl⟩, hcov⟩
  | letRec anns bindings body ihbs ihb =>
    intro d h
    cases h with
    | letRec hbs hb =>
      rw [closeTyVarsAux_letRec_eq]
      refine .letRec ?_ (ihb d hb)
      intro e he
      obtain ⟨⟨e0, d0⟩, he0, rfl⟩ := List.mem_map.mp he
      exact ihbs e0 (List.of_mem_zip he0).1 d0 (hbs e0 (List.of_mem_zip he0).1)

private theorem AllMatchesExhaustive.closeTyVars {ctors : CtorEnv} (Xs : List Nat)
    {e : Expr} (h : AllMatchesExhaustive ctors e) :
    AllMatchesExhaustive ctors (e.closeTyVars Xs) :=
  AllMatchesExhaustive.closeTyVarsAux Xs e 0 h

/-- `letRecElabNest` preserves exhaustiveness given exhaustive raw bindings + body. -/
private theorem letRecElabNest_AllMatchesExhaustive {ctors : CtorEnv}
    (G : List Nat) (anns : List (Option PolyTy)) (n : Nat)
    (rawBindings : List Expr)
    (hraw : ∀ e ∈ rawBindings, AllMatchesExhaustive ctors e)
    (members : List (Nat × RecSpec)) (body : Expr)
    (hbody : AllMatchesExhaustive ctors body) :
    AllMatchesExhaustive ctors
      (Expr.letRecElabNest G anns n rawBindings members body) := by
  induction members with
  | nil => exact hbody
  | cons hd rest ih =>
    obtain ⟨i, spec⟩ := hd
    cases spec with
    | mono τ =>
      simp only [Expr.letRecElabNest]
      refine .letIn ?_ ih
      · exact AllMatchesExhaustive.closeTyVars _
          (.letRec (fun e he => by
              obtain ⟨e0, he0, rfl⟩ := List.mem_map.mp he
              exact AllMatchesExhaustive.shiftFrom (hraw e0 he0) _ _)
            .var)
    | poly σ =>
      simp only [Expr.letRecElabNest]
      refine .letIn
        (.letRec (fun e he => by
            obtain ⟨e0, he0, rfl⟩ := List.mem_map.mp he
            exact AllMatchesExhaustive.shiftFrom (hraw e0 he0) _ _)
          .var)
        ih

private theorem letRecElab_AllMatchesExhaustive {ctors : CtorEnv}
    (G : List Nat) (anns : List (Option PolyTy)) (rawBindings : List Expr)
    (specs : List RecSpec) (body : Expr)
    (hraw : ∀ e ∈ rawBindings, AllMatchesExhaustive ctors e)
    (hbody : AllMatchesExhaustive ctors body) :
    AllMatchesExhaustive ctors (Expr.letRecElab G anns rawBindings specs body) := by
  simp only [Expr.letRecElab]
  exact letRecElabNest_AllMatchesExhaustive G anns _ rawBindings hraw _ body hbody

/-- Transfer `(a, _)` membership across a branch list whose first projections
    (patterns) agree — the key fact letting a `match`'s pinned/cover clauses
    survive inference (which preserves patterns, only rewriting branch bodies). -/
private theorem mem_of_map_fst_eq {α β : Type _} {l l' : List (α × β)}
    (h : l.map (·.1) = l'.map (·.1)) {a : α} {b : β} (hm : (a, b) ∈ l) :
    ∃ b', (a, b') ∈ l' := by
  have hmem : a ∈ l.map (·.1) := List.mem_map.mpr ⟨(a, b), hm, rfl⟩
  rw [h] at hmem
  obtain ⟨⟨a', b'⟩, hmem', heq⟩ := List.mem_map.mp hmem
  obtain rfl : a' = a := heq
  exact ⟨b', hmem'⟩

/-! **Inference preserves match-exhaustiveness** (`Infer`/`InferBranches`/`InferRecGroup`
    mutual family). Mirrors the `Infer.sourceSound` template: a `cases h`-style mutual
    block (WF on `Expr.size`/`sizeBranches`/`sizeRecGroup`) whose arms recurse through
    the companions. Inference only decorates `var` tyArgs, substitutes annotations, and
    wraps let/letRec generalisation (`closeTyVars`/`letRecElab`) — none of which touch
    a match's pattern skeleton — so each output stays exhaustive. Type-level wrappers
    are discharged by the `substTyFvars`/`openTyVars`/`closeTyVars`/`letRecElab`
    preservation helpers above. -/
set_option maxRecDepth 8000 in
mutual
/-- **(O5 transport)** `Infer` preserves `AllMatchesExhaustive` on the elaborated term. -/
theorem infer_preserves_AllMatchesExhaustive {Φ ctx e Φ' S eOut τ}
    (h : Infer Φ ctx e Φ' S eOut τ)
    (hexh : AllMatchesExhaustive ctx.ctors e) :
    AllMatchesExhaustive ctx.ctors eOut := by
  cases h with
  | primLitUnit | primLitInt | primLitNat | primLitChar => exact .primLit
  | primBinOpIntAdd => exact hexh
  | primBinOpIntSub => exact hexh
  | primBinOpIntLt _ _ _ _ => exact hexh
  | primBinOpCharLt _ _ _ _ => exact hexh
  | var _ => exact .var
  | ctor _ => exact .ctor
  | lambda _ hbody =>
    cases hexh with
    | lambda hbe =>
      have hbo := infer_preserves_AllMatchesExhaustive hbody hbe
      exact .lambda hbo
  | app hf harg _ =>
    cases hexh with
    | app hfe hae =>
      have hfo := infer_preserves_AllMatchesExhaustive hf hfe
      have hao := infer_preserves_AllMatchesExhaustive harg hae
      exact .app hfo hao
  | letIn hrhs hbody =>
    cases hexh with
    | letIn hre hbe =>
      have hro := infer_preserves_AllMatchesExhaustive hrhs hre
      have hbo := infer_preserves_AllMatchesExhaustive hbody hbe
      exact .letIn
        (AllMatchesExhaustive.closeTyVars _ (AllMatchesExhaustive.substTyFvars _ hro)) hbo
  | letInAnn _ _ hrhs _ _ _ hbody =>
    cases hexh with
    | letIn hre hbe =>
      have hro := infer_preserves_AllMatchesExhaustive hrhs
        (AllMatchesExhaustive.openTyVars _ hre)
      have hbo := infer_preserves_AllMatchesExhaustive hbody hbe
      exact .letIn
        (AllMatchesExhaustive.closeTyVars _ (AllMatchesExhaustive.substTyFvars _ hro)) hbo
  | match_ hscrut _ hbranches =>
    cases hexh with
    | match_ hse hbodies hpinned hcover =>
      expose_names
      have hso := infer_preserves_AllMatchesExhaustive hscrut hse
      obtain ⟨hbodiesOut, hpats⟩ := inferBranches_preserves_exh hbranches hbodies
      refine AllMatchesExhaustive.match_ (tyName := tyName) hso hbodiesOut ?_ ?_
      · intro c n body' hmem
        obtain ⟨b0, hb0⟩ := mem_of_map_fst_eq hpats hmem
        exact hpinned c n b0 hb0
      · intro ctorName ctor hlook hty
        obtain ⟨pat, body, hmem, hcov⟩ := hcover ctorName ctor hlook hty
        obtain ⟨b', hb'⟩ := mem_of_map_fst_eq hpats.symm hmem
        exact ⟨pat, b', hb', hcov⟩
  | letRec _ hgroup hbody =>
    cases hexh with
    | letRec hbs hbe =>
      have hbo := infer_preserves_AllMatchesExhaustive hbody hbe
      have hraw := inferRecGroup_preserves_exh hgroup hbs
      exact letRecElab_AllMatchesExhaustive _ _ _ _ _
        (fun e he => by
          obtain ⟨e0, he0, rfl⟩ := List.mem_map.mp he
          exact AllMatchesExhaustive.substTyFvars _ (hraw e0 he0))
        hbo
termination_by e.size
decreasing_by
  all_goals (try subst_vars; try simp only [Expr.size, Expr.size_openTyVars]; omega)

/-- Branch-list companion: preserves branch-body exhaustiveness AND the pattern list
    (only bodies are re-inferred). -/
theorem inferBranches_preserves_exh {Φ ctx scrutTy ρ brs Φ' S brsOut}
    (h : InferBranches Φ ctx scrutTy ρ brs Φ' S brsOut)
    (hexh : AllBranchBodiesExhaustive ctx.ctors brs) :
    AllBranchBodiesExhaustive ctx.ctors brsOut ∧
      brsOut.map (·.1) = brs.map (·.1) := by
  cases h with
  | nil => exact ⟨.nil, rfl⟩
  | cons _ _ _ hbody _ hrest =>
    cases hexh with
    | cons hbe hreste =>
      have hbo := infer_preserves_AllMatchesExhaustive hbody hbe
      obtain ⟨hre, hpe⟩ := inferBranches_preserves_exh hrest hreste
      exact ⟨.cons hbo hre, by simp only [List.map_cons, hpe]⟩
  | consWild hbody _ hrest =>
    cases hexh with
    | cons hbe hreste =>
      have hbo := infer_preserves_AllMatchesExhaustive hbody hbe
      obtain ⟨hre, hpe⟩ := inferBranches_preserves_exh hrest hreste
      exact ⟨.cons hbo hre, by simp only [List.map_cons, hpe]⟩
termination_by Expr.sizeBranches brs
decreasing_by
  all_goals (try subst_vars; try simp only [Expr.sizeBranches]; omega)

/-- Rec-group companion: every output binding is exhaustive given every input is. -/
theorem inferRecGroup_preserves_exh {Φ ctx bindings specs Φ' S bindingsOut}
    (h : InferRecGroup Φ ctx bindings specs Φ' S bindingsOut)
    (hexh : ∀ e ∈ bindings, AllMatchesExhaustive ctx.ctors e) :
    ∀ e ∈ bindingsOut, AllMatchesExhaustive ctx.ctors e := by
  cases h with
  | nil => intro e he; simp at he
  | consMono he0 _ hrest =>
    intro e he
    simp only [List.mem_cons] at he
    rcases he with rfl | he
    · exact infer_preserves_AllMatchesExhaustive he0 (hexh _ List.mem_cons_self)
    · have hraw := inferRecGroup_preserves_exh hrest
        (fun e' he' => hexh e' (List.mem_cons_of_mem _ he'))
      exact hraw e he
  | consPoly _ hinfer _ _ _ hrest =>
    intro e he
    simp only [List.mem_cons] at he
    rcases he with rfl | he
    · have hio := infer_preserves_AllMatchesExhaustive hinfer
        (AllMatchesExhaustive.openTyVars _ (hexh _ List.mem_cons_self))
      exact AllMatchesExhaustive.closeTyVars _ (AllMatchesExhaustive.substTyFvars _ hio)
    · have hraw := inferRecGroup_preserves_exh hrest
        (fun e' he' => hexh e' (List.mem_cons_of_mem _ he'))
      exact hraw e he
termination_by Expr.sizeRecGroup bindings
decreasing_by
  all_goals (try subst_vars; try simp only [Expr.sizeRecGroup, Expr.size_openTyVars]; omega)
end

/-- **(O5) Exhaustiveness of the emitted-and-elaborated matches.** If every surface
    `match` in `s` covers its scrutinee's ADT type (`SurfaceCovers`), then the
    lowered-then-elaborated Core term's matches are all `AllMatchesExhaustive` —
    the conjunct `type_safety` demands. Composition: `lower_exhaustive` (A) then
    `infer_preserves_AllMatchesExhaustive` then `AllMatchesExhaustive.substTyFvars`. -/
theorem lower_elab_exhaustive {ctors : CtorEnv} {s : Surface.Expr} {c : Expr}
    {Φ' : Nat} {S : Subst} {eOut : Expr} {τ : Ty}
    (hcov : SurfaceCovers ctors s) (hlow : lower ctors s = some c)
    (hinf : infer c.freshFloor ⟨[], ctors⟩ c = some (Φ', S, eOut, τ)) :
    AllMatchesExhaustive ctors (eOut.substTyFvars S) := by
  have hexh_c : AllMatchesExhaustive ctors c := lower_exhaustive hcov hlow
  have hInfer : Infer c.freshFloor ⟨[], ctors⟩ c Φ' S eOut τ := infer_sound hinf
  have hexh_out : AllMatchesExhaustive ctors eOut :=
    infer_preserves_AllMatchesExhaustive hInfer hexh_c
  exact AllMatchesExhaustive.substTyFvars S hexh_out


/-! ## 9b. Whole-program pipeline (plan item 7)

`Surface.Program` = user `DataDecl`s + explicit binding `groups` + body.
Groups desugar to nested `letRecIn` (`Program.term`); prelude is merged in;
then reuse expression `lower`/`elaborate`/`surface_type_safe`. SCC that *invents*
`groups` from a flat binding list is a later slice — same desugarer consumer. -/

theorem desugarGroups_nil (body : Surface.Expr) :
    Surface.desugarGroups [] body = body := rfl

theorem Program.term_no_groups (p : Surface.Program) (h : p.groups = []) :
    p.term = p.body := by
  rcases p with ⟨decls, groups, body⟩
  simp only [Surface.Program.term] at *
  subst h
  rfl

/-- Declarative program lowering: user decls under the prelude, combined env,
    desugared term. -/
inductive LowersProgram : Surface.Program → CtorEnv → Expr → Prop
  | mk {p : Surface.Program} {ctors : CtorEnv} {c : Expr} {userCore : List DataDecl} :
      LowersDataDeclsIn preludeKindEnv p.decls userCore →
      DataDecls.WF (preludeDecls ++ userCore) →
      elabDecls (preludeDecls ++ userCore) = some ctors →
      Lowers ctors p.term c →
      LowersProgram p ctors c

/-- Elaborate a program's decl group + lower its desugared term to Core. -/
def lowerProgram (p : Surface.Program) : Option (CtorEnv × Expr) := do
  let userCore ← lowerDataDeclsIn preludeKindEnv p.decls
  let ctors ← elabDecls (preludeDecls ++ userCore)
  let c ← lower ctors p.term
  pure (ctors, c)

/-- Lower then elaborate the program term under the program's `CtorEnv`. -/
def elaborateProgram (p : Surface.Program) : Option Expr := do
  let (ctors, _) ← lowerProgram p
  elaborate ctors p.term

private theorem option_bind_eq_some {α β : Type} {o : Option α} {f : α → Option β} {b : β}
    (h : o >>= f = some b) : ∃ a, o = some a ∧ f a = some b :=
  Option.bind_eq_some_iff.mp h

/-- Soundness: executable program lowering implies the declarative relation. -/
theorem lowerProgram_sound {p : Surface.Program} {ctors : CtorEnv} {c : Expr} :
    lowerProgram p = some (ctors, c) → LowersProgram p ctors c := by
  intro h
  unfold lowerProgram at h
  obtain ⟨userCore, hUser, hb⟩ := option_bind_eq_some h
  obtain ⟨ctors', hElab, hb'⟩ := option_bind_eq_some hb
  obtain ⟨c', hBody, hPure⟩ := option_bind_eq_some hb'
  simp at hPure
  obtain ⟨rfl, rfl⟩ := hPure
  refine LowersProgram.mk (lowerDataDeclsIn_sound hUser) (elabDecls_sound hElab) hElab
    (lower_sound hBody)

/-- Completeness: a related program has *some* executable lowering to the same
    `CtorEnv`. The Core body need not be definitionally `c` — `Lowers` /
    `LowersExpr.match_` is one-to-many (any behaviourally adequate `emitInner`),
    matching expression-level `lower_complete` (which only concludes `.isSome`). -/
theorem lowerProgram_complete {p : Surface.Program} {ctors : CtorEnv} {c : Expr} :
    LowersProgram p ctors c → ∃ c', lowerProgram p = some (ctors, c') := by
  intro h
  cases h with
  | mk hUser _hWF hElab hBody =>
    obtain ⟨c', hc'⟩ := Option.isSome_iff_exists.mp (lower_complete hBody)
    refine ⟨c', ?_⟩
    simp [lowerProgram, lowerDataDeclsIn_complete hUser, hElab, hc']

-- Program-level `#guard`s
private def pPreludeIf : Surface.Program :=
  ⟨[], [], .ife (.primLit (.bool true)) (.primLit (.int 1)) (.primLit (.int 0))⟩

private def pMaybeId : Surface.Program :=
  ⟨[⟨.mk "Maybe", [.mk "a"],
      [(.mk "Just", [.tvar (.mk "a")]), (.mk "Nothing", [])]⟩],
   [],
   .app (.ctor ⟨"Just"⟩) (.primLit (.int 5))⟩

private def pClashBool : Surface.Program :=
  ⟨[⟨.mk "Bool", [], [(.mk "Nope", [])]⟩], [], .primLit (.int 0)⟩

-- Simple top-level binding group: `let rec x = 1 in x`
private def pLetRecOne : Surface.Program :=
  ⟨[], [[{ name := .mk "x", ann := none, rhs := .primLit (.int 1) }]],
   .var (.mk "x")⟩

-- Two nested singleton groups: `let rec x = 1 in let rec y = x in y`
private def pLetRecTwo : Surface.Program :=
  ⟨[],
   [[{ name := .mk "x", ann := none, rhs := .primLit (.int 1) }],
    [{ name := .mk "y", ann := none, rhs := .var (.mk "x") }]],
   .var (.mk "y")⟩

-- prelude-only body (if) elaborates
#guard (elaborateProgram pPreludeIf).isSome
-- user Maybe + Just 5 elaborates
#guard (elaborateProgram pMaybeId).isSome
-- redeclaring Bool clashes with prelude
#guard (lowerProgram pClashBool).isNone
-- user field references prelude type; combined decl group elaborates
#guard match lowerDataDeclsIn preludeKindEnv
    [⟨.mk "Box", [], [(.mk "Mk", [.customTy (.mk "List") [.prim .bool]])]⟩] with
  | some userCore => (elabDecls (preludeDecls ++ userCore)).isSome
  | none => false
-- wrong-arity prelude ref in a user field → rejected
#guard (lowerDataDeclsIn preludeKindEnv
  [⟨.mk "Bad", [], [(.mk "Mk", [.customTy (.mk "List") [.prim .int, .prim .int]])]⟩]).isNone
-- user ctor name clashes with prelude ctor True → rejected
#guard (lowerProgram ⟨[⟨.mk "Box", [], [(.mk "True", [])]⟩], [], .primLit (.int 0)⟩).isNone
-- top-level binding groups desugar + elaborate
#guard (elaborateProgram pLetRecOne).isSome
#guard (elaborateProgram pLetRecTwo).isSome
-- empty group is a no-op (`term` equals body)
#guard match Surface.desugarGroups [[]] (.primLit (.int 0)) with
  | .primLit (.int 0) => true
  | _ => false
-- SCC → desugar → elaborate
#guard (elaborateProgram ⟨[], (sccGroups [bF, bG]).getD [], .var (.mk "g")⟩).isSome
-- SurfaceCovers is inhabited for the Maybe term (no matches → trivial coverage)
example : ∀ ctors, SurfaceCovers ctors pMaybeId.term := fun _ =>
  .app (.ctor) (.primLit)


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

/-- **Well-typed surface programs don't go wrong** (program-level).
    Composes decl elaboration with `surface_type_safe` on the desugared term. -/
theorem program_type_safe {p : Surface.Program} {ctors : CtorEnv} {c : Expr}
    (hlow : lowerProgram p = some (ctors, c))
    (htc : (typecheck ctors c).isSome)
    (hcov : SurfaceCovers ctors p.term) :
    ∃ e τ, elaborateProgram p = some e ∧
      TypeOfElabHM ⟨[], ctors⟩ e τ ∧
      AllMatchesExhaustive ctors e ∧
      ∀ e', Relation.ReflTransGen Step e e' →
        (IsValue e' ∨ ∃ e'', Step e' e'') := by
  have hlp := hlow
  unfold lowerProgram at hlow
  obtain ⟨userCore, _, hb'⟩ := option_bind_eq_some hlow
  obtain ⟨ctors', _, hb''⟩ := option_bind_eq_some hb'
  obtain ⟨c', hBody, hPure⟩ := option_bind_eq_some hb''
  rcases hPure with ⟨rfl, rfl⟩
  obtain ⟨e, τ, helab, hty, hexh, hsafe⟩ := surface_type_safe hBody htc hcov
  refine ⟨e, τ, ?_, hty, hexh, hsafe⟩
  simp [elaborateProgram, hlp, helab]

end SurfaceBridge
