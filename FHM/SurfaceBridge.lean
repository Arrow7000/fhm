import FHM.Core
import FHM.SurfaceLang
import FHM.Decls
import FHM.PatComp
import FHM.InferW

/-! # The surface → Core bridge

This module is the **front end**: it lowers `Surface.Expr`/`Surface.Ty` into Core
and states the campaign's headline payoff — *a well-typed, exhaustive surface
program elaborates to a Core program that is type-safe and never gets stuck*.

**Status: expression headline + DataDecl + Program groups + freeNames + sccGroups
(+ `Program.ofFlat`) + executable exhaustiveness (`dTreeExhaustiveB` /
`matchExhaustiveB` / `checkExhaustive` with Bool→Prop soundness).**
`sccGroups` (naive mutual-reachability SCC) feeds `Program.groups`;
`ValidBindingGroups` is the non-det spec (`sccGroups_sound` / `_complete` proved).
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

/-- Every ctor agrees with `kindEnvOfCtors` (all ctors of a type share arity).
    True of any `elabDecls` env. -/
def CtorEnv.arityConsistent (ctors : CtorEnv) : Prop :=
  ∀ c ctor, LookupList.get? ctors c = some ctor →
    LookupList.get? (kindEnvOfCtors ctors) ctor.tyName = some ctor.paramCount

/-- Ctor field types are well-kinded against `kindEnvOfCtors` at the ctor arity.
    True of any `elabDecls` env. -/
def CtorEnv.fieldsKinded (ctors : CtorEnv) : Prop :=
  ∀ c ctor, LookupList.get? ctors c = some ctor →
    ∀ ty ∈ ctor.contents, Ty.WellKinded (kindEnvOfCtors ctors) ctor.paramCount ty

/-- Root/local arity pin from global ctor-env hygiene + a kinding fact for `T`. -/
theorem CtorEnv.paramCount_eq_of_arityConsistent {ctors : CtorEnv}
    (hcons : CtorEnv.arityConsistent ctors)
    {T : TyName} {tyArgs : List Ty} {c : CtorName} {ctor : Ctor}
    (hkind : LookupList.get? (kindEnvOfCtors ctors) T = some tyArgs.length)
    (hctor : LookupList.get? ctors c = some ctor)
    (hty : ctor.tyName = T) :
    ctor.paramCount = tyArgs.length := by
  have h1 := hcons c ctor hctor
  rw [hty] at h1
  exact Option.some.inj (h1.symm.trans hkind)

/-- Opening a well-kinded type at arity `n ≤ |Vs|` with well-kinded (at 0) args
    yields a well-kinded type at arity 0. In particular `customTy` argument-list
    length is preserved, so `get? ke T = some args.length` survives `openWith`. -/
theorem Ty.WellKinded_openWith {ke : KindEnv} {Vs : List Ty} {n : Nat} {ty : Ty}
    (hty : Ty.WellKinded ke n ty)
    (hVs : ∀ v ∈ Vs, Ty.WellKinded ke 0 v)
    (hn : n ≤ Vs.length) :
    Ty.WellKinded ke 0 (Ty.openWith Vs ty) := by
  induction ty using Ty.rec_strong generalizing n with
  | prim p =>
    cases hty
    simp only [Ty.openWith, Ty.instantiate]
    exact .prim
  | bvar i =>
    cases hty with
    | bvar hi =>
      have hi' : i < Vs.length := by omega
      simp only [Ty.openWith, Ty.instantiate, List.getElem?_eq_getElem hi', Option.getD_some]
      exact hVs _ (List.getElem_mem _)
  | fvar _ => cases hty
  | arrow a b iha ihb =>
    cases hty with
    | arrow ha hb =>
      simp only [Ty.openWith, Ty.instantiate]
      exact .arrow (iha ha hn) (ihb hb hn)
  | customTy T args ih =>
    cases hty with
    | customTy hget hargs =>
      simp only [Ty.openWith, Ty.instantiate, TyList.instantiate_eq_map]
      refine .customTy (by simpa [List.length_map] using hget) ?_
      intro arg harg
      obtain ⟨arg0, harg0, rfl⟩ := List.mem_map.mp harg
      exact ih arg0 harg0 (hargs arg0 harg0) hn

/-- Inversion: well-kinded `customTy` pins the kind-env arity. -/
theorem Ty.WellKinded.customTy_inv {ke : KindEnv} {pc : Nat} {T : TyName} {args : List Ty}
    (h : Ty.WellKinded ke pc (.customTy T args)) :
    LookupList.get? ke T = some args.length ∧
      (∀ arg ∈ args, Ty.WellKinded ke pc arg) := by
  cases h with
  | customTy hget hargs => exact ⟨hget, hargs⟩


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
condensation. Adequacy (`sccGroups_sound` / `_complete`) is proved. -/

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

/-- Extracted Kahn loop body for induction. -/
private def kahnGo (beforeEdges : List (Nat × Nat)) :
    Nat → List Nat → List Nat → List Nat → List Nat
  | 0, _indeg, _ready, acc => acc
  | _fuel + 1, _indeg, [], acc => acc
  | fuel + 1, indeg, u :: us, acc =>
    let acc' := acc ++ [u]
    let nbrs := beforeEdges.filterMap fun ⟨a, b⟩ => if a = u then some b else none
    let indeg' := nbrs.foldl (fun ig b =>
      indegSet ig b (indegGet ig b - 1)) indeg
    let newReady := nbrs.filter fun b =>
      indegGet indeg' b = 0 && b ∉ acc' && b ∉ us
    kahnGo beforeEdges fuel indeg' (us ++ newReady) acc'

/-- Kahn topological order on `0..n-1` given before-edges `(u,v)` (u before v). -/
def kahnTopo (n : Nat) (beforeEdges : List (Nat × Nat)) : List Nat :=
  let indeg0 : List Nat :=
    (List.range n).map fun v =>
      beforeEdges.filter (fun e => e.2 = v) |>.length
  let ready0 := (List.range n).filter fun v => indegGet indeg0 v = 0
  kahnGo beforeEdges (n + 1) indeg0 ready0 []

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

/-! #### SCC adequacy helpers -/

private def sccOrderedIndexSets (binds : List Surface.Binding) : List (List Nat) :=
  let comps := sccIndexSets binds
  (kahnTopo comps.length (sccBeforeEdges (bindSucc binds) comps)).filterMap
    fun k => comps[k]?

theorem sccGroups_eq_some_iff {binds : List Surface.Binding}
    {groups : List (List Surface.Binding)} :
    sccGroups binds = some groups ↔
      (binds.map (·.name)).Nodup ∧
        groups = indexSetsToBindings binds (sccOrderedIndexSets binds) := by
  constructor
  · intro h
    have hn : (binds.map (·.name)).Nodup := by
      by_contra hdup
      simp [sccGroups, guard, hdup] at h
    refine ⟨hn, ?_⟩
    simp [sccGroups, guard, hn] at h
    exact h.symm
  · intro ⟨hn, hg⟩
    simp [sccGroups, guard, hn, sccOrderedIndexSets, hg]

private theorem map_name_length (binds : List Surface.Binding) :
    (binds.map (·.name)).length = binds.length := by
  simp

private theorem map_name_getElem {binds : List Surface.Binding} {i : Nat}
    (hi : i < binds.length) :
    (binds.map (·.name))[i]'(by rw [map_name_length]; exact hi) = (binds[i]).name := by
  simp [List.getElem_map]

private theorem name_inj_of_nodup {binds : List Surface.Binding}
    (hn : (binds.map (·.name)).Nodup) {i j : Nat}
    (hi : i < binds.length) (hj : j < binds.length)
    (h : (binds[i]).name = (binds[j]).name) : i = j := by
  have hi' : i < (binds.map (·.name)).length := by simpa [map_name_length] using hi
  have hj' : j < (binds.map (·.name)).length := by simpa [map_name_length] using hj
  have hinj := List.nodup_iff_injective_getElem.mp hn
  have hfin : (⟨i, hi'⟩ : Fin (binds.map (·.name)).length) = ⟨j, hj'⟩ :=
    hinj (by simpa [map_name_getElem hi, map_name_getElem hj] using h)
  exact congrArg Fin.val hfin

private theorem bind_eq_of_name_eq {binds : List Surface.Binding}
    (hn : (binds.map (·.name)).Nodup) {bdg : Surface.Binding} {i : Nat}
    (hbdg : bdg ∈ binds) (hi : i < binds.length)
    (hname : bdg.name = (binds[i]).name) : bdg = binds[i] := by
  obtain ⟨k, hk, hkget⟩ := List.mem_iff_getElem.mp hbdg
  have : k = i := name_inj_of_nodup hn hk hi (by simpa [hkget] using hname)
  simpa [this] using hkget.symm

private theorem DepEdge_src_mem {binds : List Surface.Binding} {a b : ValName}
    (h : DepEdge binds a b) : a ∈ binds.map (·.name) := by
  obtain ⟨bdg, hmem, hname, _⟩ := h
  exact List.mem_map.mpr ⟨bdg, hmem, hname⟩

private theorem DepReach_start_mem {binds : List Surface.Binding} {b c : ValName}
    (hend : c ∈ binds.map (·.name)) (h : DepReach binds b c) :
    b ∈ binds.map (·.name) := by
  induction h with
  | refl => exact hend
  | tail hab _ _ => exact DepEdge_src_mem hab

private theorem name_mem_idxOf {binds : List Surface.Binding}
    (_hn : (binds.map (·.name)).Nodup) {b : ValName}
    (hmem : b ∈ binds.map (·.name)) :
    ∃ (k : Nat) (hk : k < binds.length), (binds[k]).name = b := by
  obtain ⟨bdg, hbdg, hname⟩ := List.mem_map.mp hmem
  obtain ⟨k, hk, hkget⟩ := List.mem_iff_getElem.mp hbdg
  exact ⟨k, hk, by simpa [hkget] using hname⟩

theorem bindSucc_mem {binds : List Surface.Binding} {i j : Nat} :
    j ∈ bindSucc binds i ↔
      ∃ b b', binds[i]? = some b ∧ binds[j]? = some b' ∧
        Binding.refersTo b b'.name = true := by
  unfold bindSucc
  cases hbi : binds[i]? with
  | none => simp
  | some b =>
    simp only [List.mem_filterMap, List.mem_range]
    constructor
    · intro ⟨j', hj', hj⟩
      cases hbj : binds[j']? with
      | none => simp [hbj] at hj
      | some b' =>
        simp only [hbj] at hj
        by_cases href : Binding.refersTo b b'.name = true
        · simp [href] at hj
          cases hj
          exact ⟨b, b', rfl, hbj, href⟩
        · simp [href] at hj
    · intro ⟨b, b', hb, hj, hrt⟩
      obtain ⟨rfl⟩ := hb
      refine ⟨j, (List.getElem?_eq_some_iff.mp hj).1, ?_⟩
      simp [hj, hrt]

theorem DepEdge_of_bindSucc {binds : List Surface.Binding} {i j : Nat}
    (h : j ∈ bindSucc binds i) :
    ∃ b b', binds[i]? = some b ∧ binds[j]? = some b' ∧
      DepEdge binds b.name b'.name := by
  obtain ⟨b, b', hi, hj, hrt⟩ := (bindSucc_mem (binds := binds) (i := i) (j := j)).mp h
  exact ⟨b, b', hi, hj, ⟨b, List.mem_of_getElem? hi, rfl, hrt⟩⟩

private theorem bindSucc_lt {binds : List Surface.Binding} {i j : Nat}
    (h : j ∈ bindSucc binds i) : j < binds.length := by
  obtain ⟨_, _, _, hj, _⟩ := (bindSucc_mem (binds := binds) (i := i) (j := j)).mp h
  exact (List.getElem?_eq_some_iff.mp hj).1

private theorem DepEdge_to_bindSucc {binds : List Surface.Binding} {i : Nat}
    (hn : (binds.map (·.name)).Nodup) (hi : i < binds.length) {b : ValName}
    (hmem : b ∈ binds.map (·.name))
    (he : DepEdge binds (binds[i]).name b) :
    ∃ (k : Nat) (hk : k < binds.length),
      (binds[k]).name = b ∧ k ∈ bindSucc binds i := by
  obtain ⟨bdg, hbdg, hname, hrt⟩ := he
  have heq : bdg = binds[i] := bind_eq_of_name_eq hn hbdg hi hname
  subst heq
  obtain ⟨k, hk, hkname⟩ := name_mem_idxOf hn hmem
  refine ⟨k, hk, hkname, ?_⟩
  refine (bindSucc_mem (binds := binds) (i := i) (j := k)).mpr ?_
  refine ⟨binds[i], binds[k], List.getElem?_eq_getElem hi, List.getElem?_eq_getElem hk, ?_⟩
  simpa [hkname] using hrt

private theorem canReach_sound_go (binds : List Surface.Binding) :
    ∀ (fuel : Nat) (seen : List Nat) (src dst : Nat)
      (hsrc : src < binds.length) (hdst : dst < binds.length),
      (∀ s ∈ seen, s < binds.length) →
      canReach (bindSucc binds) fuel seen src dst = true →
      DepReach binds (binds[src]).name (binds[dst]).name := by
  intro fuel
  induction fuel with
  | zero =>
    intro seen src dst hsrc hdst _hseen h
    unfold canReach at h
    by_cases heq : src = dst
    · subst heq; exact DepReach.refl
    · simp [heq] at h
  | succ fuel ih =>
    intro seen src dst hsrc hdst hseen h
    unfold canReach at h
    by_cases heq : src = dst
    · subst heq; exact DepReach.refl
    · by_cases hmem : src ∈ seen
      · simp [heq, hmem] at h
      · simp [heq, hmem, List.any_eq_true] at h
        obtain ⟨n, hnmem, hn⟩ := h
        have hnlt : n < binds.length := bindSucc_lt hnmem
        have hnreach := ih (src :: seen) n dst hnlt hdst
          (by
            intro s hs
            cases List.mem_cons.mp hs with
            | inl hseq => cases hseq; exact hsrc
            | inr hs' => exact hseen s hs')
          hn
        obtain ⟨b, b', hb, hj, hedge⟩ := DepEdge_of_bindSucc hnmem
        have hb' : b = binds[src] := (List.getElem?_eq_some_iff.mp hb).2.symm
        have hj' : b' = binds[n] := (List.getElem?_eq_some_iff.mp hj).2.symm
        subst hb' hj'
        exact DepReach.tail hedge hnreach

theorem canReach_sound {binds : List Surface.Binding} {fuel : Nat} {i j : Nat}
    (h : canReach (bindSucc binds) fuel [] i j = true)
    (hi : i < binds.length) (hj : j < binds.length) :
    DepReach binds (binds[i]).name (binds[j]).name :=
  canReach_sound_go binds fuel [] i j hi hj (by simp) h

/-- Consecutive `bindSucc` edges along an index list. -/
private def isBindChain (binds : List Surface.Binding) : List Nat → Prop
  | [] => True
  | [_] => True
  | a :: b :: rest => b ∈ bindSucc binds a ∧ isBindChain binds (b :: rest)

private theorem isBindChain_append {binds : List Surface.Binding}
    {xs ys : List Nat} (hx : isBindChain binds xs) (hy : isBindChain binds ys)
    (hbridge : ∀ a b, xs.getLast? = some a → ys.head? = some b → b ∈ bindSucc binds a) :
    isBindChain binds (xs ++ ys) := by
  induction xs with
  | nil => simpa using hy
  | cons x xs ih =>
    cases xs with
    | nil =>
      cases ys with
      | nil => trivial
      | cons y ys =>
        refine ⟨hbridge x y rfl rfl, hy⟩
    | cons x' xs =>
      simp only [List.cons_append, isBindChain] at hx ⊢
      exact ⟨hx.1, ih hx.2 (by
        intro a b ha hb
        exact hbridge a b (by
          simpa [List.getLast?_cons_cons] using ha) hb)⟩

private theorem isBindChain_take {binds : List Surface.Binding}
    {vs : List Nat} (n : Nat) (h : isBindChain binds vs) :
    isBindChain binds (vs.take n) := by
  induction vs generalizing n with
  | nil =>
    simp [isBindChain]
  | cons a vs ih =>
    cases n with
    | zero => simp [isBindChain]
    | succ n =>
      cases vs with
      | nil => simp [isBindChain]
      | cons b vs =>
        cases n with
        | zero => simp [isBindChain]
        | succ n =>
          simp only [List.take_succ_cons, isBindChain] at h ⊢
          exact ⟨h.1, by simpa [List.take_cons] using ih (n + 1) h.2⟩

private theorem isBindChain_drop {binds : List Surface.Binding}
    {vs : List Nat} (n : Nat) (h : isBindChain binds vs) :
    isBindChain binds (vs.drop n) := by
  induction n generalizing vs with
  | zero => simpa using h
  | succ n ih =>
    cases vs with
    | nil => simp [isBindChain]
    | cons a vs =>
      simp only [List.drop_succ_cons]
      cases vs with
      | nil => simp [isBindChain]
      | cons b vs =>
        exact ih h.2

private theorem isBindChain_succ_getElem {binds : List Surface.Binding}
    {vs : List Nat} {j : Nat} (h : isBindChain binds vs)
    (hj : j + 1 < vs.length) :
    vs[j + 1] ∈ bindSucc binds vs[j] := by
  induction vs generalizing j with
  | nil => cases hj
  | cons a vs ih =>
    cases vs with
    | nil =>
      simp at hj
    | cons b vs =>
      cases j with
      | zero =>
        exact h.1
      | succ j =>
        have : j + 1 < (b :: vs).length := by simp at hj ⊢; omega
        simpa [List.getElem_cons_succ] using ih h.2 this

private theorem isBindChain_take_append_drop {binds : List Surface.Binding}
    {vs : List Nat} {i j : Nat}
    (hij : i < j) (hjlen : j < vs.length)
    (hget : vs[i]? = vs[j]?) (hchain : isBindChain binds vs) :
    isBindChain binds (vs.take (i + 1) ++ vs.drop (j + 1)) := by
  have htake := isBindChain_take (i + 1) hchain
  have hdrop := isBindChain_drop (j + 1) hchain
  refine isBindChain_append htake hdrop ?_
  intro a b ha hb
  have hi1 : i < vs.length := Nat.lt_trans hij hjlen
  have htake_last : (vs.take (i + 1)).getLast? = vs[i]? := by
    rw [List.getLast?_take]
    simp [List.getElem?_eq_getElem hi1]
  have ha' : vs[i]? = some a := htake_last ▸ ha
  cases hdropNil : vs.drop (j + 1) with
  | nil =>
    simp [hdropNil] at hb
  | cons b' rest =>
    have eqb : b = b' := by
      have : (b' :: rest).head? = some b := by simpa [hdropNil] using hb
      simp at this; exact this.symm
    subst eqb
    have hj1 : j + 1 < vs.length := by
      have hlen := congrArg List.length hdropNil
      simp [List.length_drop] at hlen
      omega
    have hb_get : vs[j + 1]? = some b := by
      rw [← List.head?_drop, hdropNil]; rfl
    have hedge := isBindChain_succ_getElem hchain hj1
    have hvi : vs[i] = a := (List.getElem?_eq_some_iff.mp ha').2
    have hvj : vs[j] = a := by
      have : vs[j]? = some a := hget ▸ ha'
      exact (List.getElem?_eq_some_iff.mp this).2
    have hvj1 : vs[j + 1] = b := (List.getElem?_eq_some_iff.mp hb_get).2
    rw [← hvj1, ← hvj]
    exact hedge

private theorem DepReach_exists_chain {binds : List Surface.Binding}
    (hn : (binds.map (·.name)).Nodup) {i j : Nat}
    (hi : i < binds.length) (hj : j < binds.length)
    (h : DepReach binds (binds[i]).name (binds[j]).name) :
    ∃ vs : List Nat,
      vs.head? = some i ∧ vs.getLast? = some j ∧
        isBindChain binds vs ∧ ∀ v ∈ vs, v < binds.length := by
  suffices ∀ a c, DepReach binds a c →
      ∀ (i j : Nat) (hi : i < binds.length) (hj : j < binds.length),
        a = (binds[i]).name → c = (binds[j]).name →
        ∃ vs : List Nat,
          vs.head? = some i ∧ vs.getLast? = some j ∧
            isBindChain binds vs ∧ ∀ v ∈ vs, v < binds.length from
    this _ _ h i j hi hj rfl rfl
  intro a c hreach
  induction hreach with
  | refl =>
    intro i j hi hj ha hc
    have hij : i = j := name_inj_of_nodup hn hi hj (ha.symm.trans hc)
    subst hij
    exact ⟨[i], rfl, rfl, trivial, by intro v hv; simp at hv; subst hv; exact hi⟩
  | @tail a b c hab hbc ih =>
    intro i j hi hj ha hc
    have hbmem : b ∈ binds.map (·.name) :=
      DepReach_start_mem
        (List.mem_map.mpr ⟨binds[j], List.getElem_mem hj, hc.symm⟩) hbc
    have hedge : DepEdge binds (binds[i]).name b := by simpa [← ha] using hab
    obtain ⟨k, hk, hkname, hksucc⟩ := DepEdge_to_bindSucc hn hi hbmem hedge
    obtain ⟨vs, hvsh, hvsl, hvsc, hvsb⟩ := ih k j hk hj hkname.symm hc
    refine ⟨i :: vs, by simp, ?_, ?_, ?_⟩
    · cases vs with
      | nil => simp at hvsh
      | cons v vs' => simpa [List.getLast?_cons_cons] using hvsl
    · cases vs with
      | nil => simp at hvsh
      | cons v vs' =>
        have hv : v = k := by simp at hvsh; exact hvsh
        subst hv
        exact ⟨hksucc, hvsc⟩
    · intro v hv
      cases List.mem_cons.mp hv with
      | inl hvi => subst hvi; exact hi
      | inr hv' => exact hvsb v hv'

private theorem exists_nodup_bindChain (binds : List Surface.Binding) :
    ∀ (vs : List Nat), isBindChain binds vs → vs ≠ [] →
      (∀ v ∈ vs, v < binds.length) →
      ∃ ws : List Nat, isBindChain binds ws ∧ ws.Nodup ∧ ws ≠ [] ∧
        ws.head? = vs.head? ∧ ws.getLast? = vs.getLast? ∧
        (∀ v ∈ ws, v < binds.length) := by
  intro vs
  induction hlen : vs.length using Nat.strongRecOn generalizing vs with
  | ind n ih =>
    intro hchain hne hbound
    subst hlen
    by_cases hn : vs.Nodup
    · exact ⟨vs, hchain, hn, hne, rfl, rfl, hbound⟩
    · have hrep : ∃ (i j : Nat), i < j ∧ j < vs.length ∧ vs[i]? = vs[j]? := by
        have := mt (List.nodup_iff_getElem?_ne_getElem? (l := vs)).2 hn
        push_neg at this
        exact this
      obtain ⟨i, j, hij, hjlen, hget⟩ := hrep
      set ws := vs.take (i + 1) ++ vs.drop (j + 1)
      have hi1 : i + 1 ≤ vs.length := Nat.succ_le_of_lt (Nat.lt_trans hij hjlen)
      have hj1 : j + 1 ≤ vs.length := Nat.succ_le_of_lt hjlen
      have hlen' : ws.length < vs.length := by
        -- |take (i+1)| + |drop (j+1)| = (i+1) + (len - (j+1)) = len + (i - j) < len
        have htake_len : (vs.take (i + 1)).length = i + 1 := by
          simp [List.length_take, Nat.min_eq_left hi1]
        have hdrop_len : (vs.drop (j + 1)).length = vs.length - (j + 1) := by
          simp [List.length_drop]
        simp only [ws, List.length_append, htake_len, hdrop_len]
        omega
      have hne' : ws ≠ [] := by
        have hpos : (vs.take (i + 1)).length = i + 1 := by
          simp [List.length_take, Nat.min_eq_left hi1]
        intro hempty
        have hlen0 : ws.length = 0 := by simp [hempty]
        simp only [ws, List.length_append, hpos] at hlen0
        omega
      have hchain' : isBindChain binds ws :=
        isBindChain_take_append_drop hij hjlen hget hchain
      have hbound' : ∀ v ∈ ws, v < binds.length := by
        intro v hv
        simp only [ws, List.mem_append] at hv
        cases hv with
        | inl ht => exact hbound v (List.mem_of_mem_take ht)
        | inr hd => exact hbound v (List.mem_of_mem_drop hd)
      have hhead : ws.head? = vs.head? := by
        cases vs with
        | nil => cases hne rfl
        | cons v vs' => simp [ws]
      have hlast : ws.getLast? = vs.getLast? := by
        cases hdrop : vs.drop (j + 1) with
        | nil =>
          have hjend : j + 1 = vs.length := by
            have := congrArg List.length hdrop
            simp [List.length_drop] at this; omega
          have hws : ws = vs.take (i + 1) := by simp [ws, hdrop]
          have hti : (vs.take (i + 1)).getLast? = vs[i]? := by
            rw [List.getLast?_take]
            simp [List.getElem?_eq_getElem (Nat.lt_trans hij hjlen)]
          have hlastj : vs.getLast? = vs[j]? := by
            have hj' : j = vs.length - 1 := by omega
            rw [hj', List.getLast?_eq_getElem?]
          rw [hws, hti, hget, hlastj]
        | cons x xs =>
          have hws_last : ws.getLast? = (x :: xs).getLast? := by
            simp [ws, hdrop, List.getLast?_append]
            cases hgl : (x :: xs).getLast? with
            | none => simp at hgl
            | some v => simp
          have hdrop_last : (vs.drop (j + 1)).getLast? = vs.getLast? := by
            have hjlt : ¬(vs.length ≤ j + 1) := by
              have := congrArg List.length hdrop
              simp [List.length_drop] at this; omega
            simp [List.getLast?_drop, hjlt]
          rw [hws_last, ← hdrop, hdrop_last]
      obtain ⟨ws', hc', hn', hne'', hh', hl', hb'⟩ :=
        ih ws.length hlen' ws rfl hchain' hne' hbound'
      exact ⟨ws', hc', hn', hne'', hh'.trans hhead, hl'.trans hlast, hb'⟩

private theorem canReach_of_nodup_chain {binds : List Surface.Binding}
    {fuel : Nat} {seen vs : List Nat} {src dst : Nat}
    (hchain : isBindChain binds vs) (hnodup : vs.Nodup)
    (hhead : vs.head? = some src) (hlast : vs.getLast? = some dst)
    (havoid : ∀ v ∈ vs, v ∉ seen)
    (hfuel : vs.length - 1 ≤ fuel) :
    canReach (bindSucc binds) fuel seen src dst = true := by
  induction vs generalizing fuel seen src dst with
  | nil => simp at hhead
  | cons a rest ih =>
    cases rest with
    | nil =>
      simp only [List.head?, Option.some.injEq] at hhead
      simp only [List.getLast?] at hlast
      subst hhead; cases hlast
      unfold canReach; simp
    | cons b rest =>
      simp only [List.head?, Option.some.injEq] at hhead
      subst hhead
      have hlast_tail : (b :: rest).getLast? = some dst := by
        simpa [List.getLast?_cons_cons] using hlast
      have hlast_mem : dst ∈ b :: rest := by
        obtain ⟨ys, hys⟩ := (List.getLast?_eq_some_iff).1 hlast_tail
        rw [hys]; exact List.mem_append_right _ (by simp)
      have hsrc_ne : a ≠ dst := by
        intro heq; subst heq
        exact (List.nodup_cons.mp hnodup).1 hlast_mem
      have hnotin : a ∉ seen := havoid a (by simp)
      cases fuel with
      | zero =>
        have : (a :: b :: rest).length - 1 ≤ 0 := hfuel
        simp at this
      | succ fuel =>
        unfold canReach
        simp [hsrc_ne, hnotin, List.any_eq_true]
        refine ⟨b, hchain.1, ?_⟩
        refine ih (fuel := fuel) (seen := a :: seen) (src := b) (dst := dst)
          hchain.2 (List.nodup_cons.mp hnodup).2 rfl hlast_tail
          (fun v hv hin => by
            cases List.mem_cons.mp hin with
            | inl heq =>
              subst heq
              exact (List.nodup_cons.mp hnodup).1 hv
            | inr hs =>
              exact havoid v (List.mem_cons_of_mem _ hv) hs)
          (by have := hfuel; simp at this ⊢; omega)

theorem canReach_complete {binds : List Surface.Binding} {i j : Nat}
    (hn : (binds.map (·.name)).Nodup)
    (hi : i < binds.length) (hj : j < binds.length)
    (h : DepReach binds (binds[i]).name (binds[j]).name) :
    canReach (bindSucc binds) binds.length [] i j = true := by
  obtain ⟨vs, hvsh, hvsl, hchain, hbound⟩ := DepReach_exists_chain hn hi hj h
  have hne : vs ≠ [] := fun he => by subst he; simp at hvsh
  obtain ⟨ws, hchain', hnodup, _hne', hhead, hlast, hbound'⟩ :=
    exists_nodup_bindChain binds vs hchain hne hbound
  have hfuel : ws.length - 1 ≤ binds.length := by
    have hle : ws.length ≤ binds.length := by
      have hcard := List.toFinset_card_of_nodup hnodup
      have hsub : ws.toFinset ⊆ Finset.range binds.length := by
        intro x hx
        simp [Finset.mem_range]
        exact hbound' x (List.mem_toFinset.mp hx)
      have := Finset.card_le_card hsub
      simpa [hcard, Finset.card_range] using this
    omega
  exact canReach_of_nodup_chain hchain' hnodup
    (hhead.trans hvsh) (hlast.trans hvsl) (fun _ _ => by simp) hfuel

/-! ##### Partition / Kahn helpers for `sccOrderedIndexSets` -/

/-- Same algorithm as the `let rec go` inside `sccIndexSets`, extracted for induction. -/
private def sccPartitionGo (mutReach : Nat → Nat → Bool) :
    Nat → List Nat → List (List Nat) → List (List Nat)
  | 0, _todo, acc => acc
  | _fuel + 1, [], acc => acc
  | fuel + 1, i :: rest, acc =>
    let todo := i :: rest
    let comp := todo.filter (mutReach i)
    let rest' := todo.filter (fun j => !mutReach i j)
    sccPartitionGo mutReach fuel rest' (acc ++ [comp])

private theorem sccIndexSets.go_eq_partitionGo
    (mutReach : Nat → Nat → Bool) :
    ∀ fuel todo acc,
      sccIndexSets.go mutReach fuel todo acc =
        sccPartitionGo mutReach fuel todo acc := by
  intro fuel
  induction fuel with
  | zero => intros; rfl
  | succ fuel ih =>
    intro todo acc
    cases todo with
    | nil => rfl
    | cons i rest =>
      simp only [sccIndexSets.go, sccPartitionGo, ih]

private theorem sccIndexSets_eq_partitionGo (binds : List Surface.Binding) :
    sccIndexSets binds =
      sccPartitionGo
        (fun i j => mutuallyReachable (bindSucc binds) binds.length i j)
        (binds.length + 1) (List.range binds.length) [] := by
  unfold sccIndexSets
  rw [sccIndexSets.go_eq_partitionGo]

private theorem mutuallyReachable_refl (succ : Nat → List Nat) (fuel i : Nat) :
    mutuallyReachable succ fuel i i = true := by
  simp only [mutuallyReachable, Bool.and_self]
  unfold canReach
  simp

private theorem filter_append_filter_not_perm {α} (p : α → Bool) (l : List α) :
    (l.filter p ++ l.filter (fun x => !p x)).Perm l := by
  induction l with
  | nil => simp
  | cons a l ih =>
    cases hp : p a
    · simp only [List.filter_cons, hp, Bool.not_false]
      exact (List.perm_middle).trans (ih.cons a)
    · simp only [List.filter_cons, hp, Bool.not_true]
      exact ih.cons a

/-- Needs reflexivity so each step removes the seed (otherwise fuel can run out
    with `todo` nonempty and the unconstrained claim is false). -/
private theorem sccPartitionGo_flatten_perm (mutReach : Nat → Nat → Bool)
    (hrefl : ∀ i, mutReach i i = true) :
    ∀ (fuel : Nat) (todo : List Nat) (accs : List (List Nat)),
      todo.length ≤ fuel →
      (sccPartitionGo mutReach fuel todo accs).flatten.Perm
        (accs.flatten ++ todo) := by
  intro fuel
  induction fuel with
  | zero =>
    intro todo accs hlen
    have : todo = [] := by
      cases todo with
      | nil => rfl
      | cons _ _ => simp at hlen
    subst this
    simp [sccPartitionGo]
  | succ fuel ih =>
    intro todo accs hlen
    cases todo with
    | nil => simp [sccPartitionGo]
    | cons i rest =>
      simp only [sccPartitionGo]
      have hsplit := filter_append_filter_not_perm (mutReach i) (i :: rest)
      have himem : i ∈ (i :: rest).filter (mutReach i) := by
        simp [List.mem_filter, hrefl]
      have hlen' : ((i :: rest).filter (fun j => !mutReach i j)).length ≤ fuel := by
        have hsum := List.length_eq_length_filter_add (f := mutReach i) (l := i :: rest)
        have hpos : 0 < ((i :: rest).filter (mutReach i)).length :=
          List.length_pos_of_mem himem
        have htodo : (i :: rest).length ≤ fuel + 1 := hlen
        omega
      have hih := ih _ (accs ++ [(i :: rest).filter (mutReach i)]) hlen'
      refine hih.trans ?_
      simp only [List.flatten_append, List.flatten_cons, List.flatten_nil, List.append_assoc,
        List.nil_append]
      exact List.Perm.append_left accs.flatten hsplit

private theorem sccPartitionGo_nonempty (mutReach : Nat → Nat → Bool)
    (hrefl : ∀ i, mutReach i i = true) :
    ∀ (fuel : Nat) (todo : List Nat) (accs : List (List Nat)),
      (∀ g ∈ accs, g ≠ []) →
      (∀ g ∈ sccPartitionGo mutReach fuel todo accs, g ≠ []) := by
  intro fuel
  induction fuel with
  | zero =>
    intro todo accs hacc g hg; exact hacc g hg
  | succ fuel ih =>
    intro todo accs hacc g hg
    cases todo with
    | nil =>
      simp [sccPartitionGo] at hg; exact hacc g hg
    | cons i rest =>
      simp only [sccPartitionGo] at hg
      refine ih _ _ ?_ g hg
      intro g' hg'
      simp only [List.mem_append, List.mem_singleton] at hg'
      cases hg' with
      | inl h => exact hacc g' h
      | inr h =>
        subst h
        intro hempty
        have : i ∈ (i :: rest).filter (mutReach i) := by
          simp [List.mem_filter, hrefl]
        simp [hempty] at this

private theorem sccIndexSets_flatten_perm (binds : List Surface.Binding) :
    (sccIndexSets binds).flatten.Perm (List.range binds.length) := by
  rw [sccIndexSets_eq_partitionGo]
  have h := sccPartitionGo_flatten_perm
    (fun i j => mutuallyReachable (bindSucc binds) binds.length i j)
    (fun i => mutuallyReachable_refl _ _ i)
    (binds.length + 1) (List.range binds.length) []
    (by simp [List.length_range])
  simpa using h

private theorem sccIndexSets_nonempty_comp (binds : List Surface.Binding) :
    ∀ g ∈ sccIndexSets binds, g ≠ [] := by
  rw [sccIndexSets_eq_partitionGo]
  exact sccPartitionGo_nonempty _
    (fun i => mutuallyReachable_refl _ _ i) _ _ _
    (by intro g hg; cases hg)

private theorem flatten_map_filterMap {α β}
    (f : α → Option β) (sets : List (List α)) :
    (sets.map (fun idxs => idxs.filterMap f)).flatten =
      sets.flatten.filterMap f := by
  induction sets with
  | nil => simp
  | cons s sets ih =>
    simp only [List.map_cons, List.flatten_cons, List.filterMap_append, ih]

private theorem range_filterMap_getElem? {α} (l : List α) :
    (List.range l.length).filterMap (fun i => l[i]?) = l := by
  induction l with
  | nil => simp
  | cons a xs ih =>
    simp only [List.length_cons]
    rw [List.range_succ_eq_map]
    simp only [List.filterMap_cons, List.getElem?_cons_zero, List.filterMap_map]
    change a :: (List.range xs.length).filterMap (fun i => (a :: xs)[i + 1]?) = a :: xs
    have h := List.filterMap_congr (f := fun i => (a :: xs)[i + 1]?) (g := fun i => xs[i]?)
      (l := List.range xs.length) (fun i _ => List.getElem?_cons_succ)
    rw [h, ih]

private theorem indexSetsToBindings_flatten_of_perm
    {binds : List Surface.Binding} {sets : List (List Nat)}
    (hperm : sets.flatten.Perm (List.range binds.length)) :
    (indexSetsToBindings binds sets).flatten.Perm binds := by
  unfold indexSetsToBindings
  rw [flatten_map_filterMap]
  have h := hperm.filterMap (fun i => binds[i]?)
  rw [range_filterMap_getElem?] at h
  exact h

private theorem sccIndexSets_mem_lt (binds : List Surface.Binding) :
    ∀ g ∈ sccIndexSets binds, ∀ i ∈ g, i < binds.length := by
  intro g hg i hi
  have hperm := sccIndexSets_flatten_perm binds
  have himem : i ∈ (sccIndexSets binds).flatten :=
    List.mem_flatten.mpr ⟨g, hg, hi⟩
  have : i ∈ List.range binds.length := (List.Perm.mem_iff hperm).1 himem
  exact List.mem_range.mp this

private theorem DepReach_trans {binds : List Surface.Binding} {a b c : ValName}
    (hab : DepReach binds a b) (hbc : DepReach binds b c) :
    DepReach binds a c := by
  induction hab with
  | refl => exact hbc
  | tail hedge _ ih => exact DepReach.tail hedge (ih hbc)

private theorem mutuallyReachable_sym (succ : Nat → List Nat) (fuel i j : Nat) :
    mutuallyReachable succ fuel i j = mutuallyReachable succ fuel j i := by
  simp only [mutuallyReachable, Bool.and_comm]

/-- Seed-filter components are pairwise `DepMutual` (no Bool-trans / Nodup needed). -/
private theorem sccPartitionGo_depMutual (binds : List Surface.Binding) :
    let mutReach := fun i j =>
      mutuallyReachable (bindSucc binds) binds.length i j
    ∀ (fuel : Nat) (todo : List Nat) (accs : List (List Nat)),
      (∀ x ∈ todo, x < binds.length) →
      (∀ g ∈ accs, ∀ a ∈ g, ∀ b ∈ g,
        ∀ (ha : a < binds.length) (hb : b < binds.length),
          DepMutual binds (binds[a]).name (binds[b]).name) →
      (∀ g ∈ sccPartitionGo mutReach fuel todo accs,
        ∀ a ∈ g, ∀ b ∈ g,
          ∀ (ha : a < binds.length) (hb : b < binds.length),
            DepMutual binds (binds[a]).name (binds[b]).name) := by
  intro mutReach fuel
  induction fuel with
  | zero =>
    intro todo accs _hbound hacc g hg; exact hacc g hg
  | succ fuel ih =>
    intro todo accs hbound hacc g hg
    cases todo with
    | nil =>
      simp [sccPartitionGo] at hg; exact hacc g hg
    | cons seed rest =>
      simp only [sccPartitionGo] at hg
      have hseed_lt : seed < binds.length := hbound seed (by simp)
      have htodo_bound : ∀ x ∈ seed :: rest, x < binds.length := hbound
      refine ih _ _ ?_ ?_ g hg
      · intro x hx
        exact htodo_bound x (List.mem_of_mem_filter hx)
      · intro g' hg' a ha b hb ha_lt hb_lt
        simp only [List.mem_append, List.mem_singleton] at hg'
        cases hg' with
        | inl h => exact hacc g' h a ha b hb ha_lt hb_lt
        | inr h =>
          subst h
          have hsa : mutReach seed a = true := (List.mem_filter.mp ha).2
          have hsb : mutReach seed b = true := (List.mem_filter.mp hb).2
          have ⟨hsa1, hsa2⟩ := Bool.and_eq_true_iff.mp hsa
          have ⟨hsb1, hsb2⟩ := Bool.and_eq_true_iff.mp hsb
          have dsa := canReach_sound hsa1 hseed_lt ha_lt
          have das := canReach_sound hsa2 ha_lt hseed_lt
          have dsb := canReach_sound hsb1 hseed_lt hb_lt
          have dbs := canReach_sound hsb2 hb_lt hseed_lt
          exact ⟨DepReach_trans das dsb, DepReach_trans dbs dsa⟩

private theorem sccIndexSets_comp_depMutual (binds : List Surface.Binding)
    {g : List Nat} (hg : g ∈ sccIndexSets binds)
    {i j : Nat} (hi : i ∈ g) (hj : j ∈ g) :
    DepMutual binds (binds[i]'(sccIndexSets_mem_lt binds g hg i hi)).name
      (binds[j]'(sccIndexSets_mem_lt binds g hg j hj)).name := by
  have hi_lt := sccIndexSets_mem_lt binds g hg i hi
  have hj_lt := sccIndexSets_mem_lt binds g hg j hj
  have hg' : g ∈
      sccPartitionGo
        (fun i j => mutuallyReachable (bindSucc binds) binds.length i j)
        (binds.length + 1) (List.range binds.length) [] := by
    rwa [← sccIndexSets_eq_partitionGo]
  exact sccPartitionGo_depMutual binds (binds.length + 1)
    (List.range binds.length) []
    (fun x hx => List.mem_range.mp hx)
    (fun g hg => by cases hg)
    g hg' i hi j hj hi_lt hj_lt

private theorem filterMap_ne_nil_of_isSome {α β}
    (f : α → Option β) {l : List α} (hne : l ≠ [])
    (h : ∀ x ∈ l, (f x).isSome) : l.filterMap f ≠ [] := by
  cases l with
  | nil => cases hne rfl
  | cons a as =>
    have ha := h a (by simp)
    cases hf : f a with
    | none => simp [hf] at ha
    | some b => simp [hf]

private theorem mutuallyReachable_trans_of_nodup {binds : List Surface.Binding}
    (hn : (binds.map (·.name)).Nodup)
    {i j k : Nat}
    (hi : i < binds.length) (hj : j < binds.length) (hk : k < binds.length)
    (hij : mutuallyReachable (bindSucc binds) binds.length i j = true)
    (hjk : mutuallyReachable (bindSucc binds) binds.length j k = true) :
    mutuallyReachable (bindSucc binds) binds.length i k = true := by
  obtain ⟨hij1, hij2⟩ := Bool.and_eq_true_iff.mp hij
  obtain ⟨hjk1, hjk2⟩ := Bool.and_eq_true_iff.mp hjk
  have dik := DepReach_trans (canReach_sound hij1 hi hj) (canReach_sound hjk1 hj hk)
  have dki := DepReach_trans (canReach_sound hjk2 hk hj) (canReach_sound hij2 hj hi)
  exact Bool.and_eq_true_iff.mpr ⟨canReach_complete hn hi hk dik,
    canReach_complete hn hk hi dki⟩

private theorem sccOrderedIndexSets_mem_of_getElem
    (binds : List Surface.Binding) {idxs : List Nat}
    (h : idxs ∈ sccOrderedIndexSets binds) :
    idxs ∈ sccIndexSets binds := by
  simp only [sccOrderedIndexSets] at h
  obtain ⟨k, _hk, hget⟩ := List.mem_filterMap.mp h
  exact List.mem_of_getElem? hget

private theorem filterMap_getElem?_of_perm {α} {l : List α} {order : List Nat}
    (h : order.Perm (List.range l.length)) :
    (order.filterMap (fun i => l[i]?)).Perm l := by
  have h' := h.filterMap (fun i => l[i]?)
  rwa [range_filterMap_getElem?] at h'

private theorem perm_range_of_nodup_length {l : List Nat} {n : Nat}
    (hn : l.Nodup) (hbound : ∀ x ∈ l, x < n) (hlen : l.length = n) :
    l.Perm (List.range n) := by
  refine (List.perm_ext_iff_of_nodup hn List.nodup_range).2 ?_
  intro a
  constructor
  · intro ha
    exact List.mem_range.mpr (hbound a ha)
  · intro ha
    have hsub : l.toFinset ⊆ Finset.range n := by
      intro x hx
      exact Finset.mem_range.mpr (hbound x (List.mem_toFinset.mp hx))
    have hcard : l.toFinset.card = n := by
      rw [List.toFinset_card_of_nodup hn, hlen]
    have hEq : l.toFinset = Finset.range n :=
      Finset.eq_of_subset_of_card_le hsub (by simp [hcard])
    exact List.mem_toFinset.mp (by
      rw [hEq]
      simpa [Finset.mem_range] using List.mem_range.mp ha)

/-! ##### Abstract Kahn invariants

`kahnTopo_edge_before` is false for arbitrary edges: targets `≥ n` always read
`indegGet = 0`, so Kahn can emit them before an out-of-range source. All lemmas
below assume every before-edge endpoint lies in `0 .. n-1`. -/

/-- Edges into `v` whose source is not yet emitted. -/
private def remInDeg (beforeEdges : List (Nat × Nat)) (acc : List Nat) (v : Nat) : Nat :=
  (beforeEdges.filter (fun e => e.2 = v && e.1 ∉ acc)).length

private theorem indegSet_length (indeg : List Nat) (i v : Nat) :
    (indegSet indeg i v).length = indeg.length := by
  simp only [indegSet, List.length_mapIdx]

private theorem indegGet_indegSet_eq (indeg : List Nat) (i v : Nat)
    (hi : i < indeg.length) :
    indegGet (indegSet indeg i v) i = v := by
  simp only [indegGet, indegSet]
  have hget : (indeg.mapIdx fun j x => if j = i then v else x)[i]? = some v := by
    rw [List.getElem?_mapIdx, List.getElem?_eq_getElem hi]
    simp
  simp [hget]

private theorem indegGet_indegSet_ne (indeg : List Nat) (i j v : Nat)
    (hne : j ≠ i) :
    indegGet (indegSet indeg i v) j = indegGet indeg j := by
  simp only [indegGet, indegSet]
  by_cases hj : j < indeg.length
  · have hget :
        (indeg.mapIdx fun k x => if k = i then v else x)[j]? =
          some (if j = i then v else indeg[j]) := by
      rw [List.getElem?_mapIdx, List.getElem?_eq_getElem hj]
      simp
    simp only [hget, Option.getD_some, hne, ↓reduceIte]
    simp [List.getElem?_eq_getElem hj]
  · have hlen : indeg.length ≤ j := Nat.le_of_not_gt hj
    simp [List.getElem?_eq_none_iff.mpr hlen,
      List.getElem?_eq_none_iff.mpr (by rwa [List.length_mapIdx] : (indeg.mapIdx fun k x =>
        if k = i then v else x).length ≤ j)]

private theorem remInDeg_nil_acc (beforeEdges : List (Nat × Nat)) (v : Nat) :
    remInDeg beforeEdges [] v =
      (beforeEdges.filter (fun e => e.2 = v)).length := by
  simp only [remInDeg]
  congr 1
  refine List.filter_congr ?_
  intro e _
  simp

private theorem remInDeg_eq_zero_preds (beforeEdges : List (Nat × Nat))
    (acc : List Nat) {u v : Nat}
    (he : (u, v) ∈ beforeEdges)
    (hz : remInDeg beforeEdges acc v = 0) :
    u ∈ acc := by
  by_contra hnotin
  have hmem : (u, v) ∈ beforeEdges.filter (fun e => e.2 = v && e.1 ∉ acc) := by
    simp only [List.mem_filter, he, true_and]
    simp [hnotin]
  have hpos : 0 < remInDeg beforeEdges acc v :=
    List.length_pos_of_mem hmem
  omega

private theorem filter_length_split {α} (p q : α → Bool) (l : List α) :
    (l.filter fun x => p x && q x).length +
      (l.filter fun x => p x && !q x).length =
      (l.filter p).length := by
  induction l with
  | nil => simp
  | cons a as ih =>
    simp only [List.filter_cons]
    cases hp : p a <;> cases hq : q a <;> simp <;> omega

/-- Emitting `u` (not already in `acc`) removes exactly the `(u, v)` edges. -/
private theorem remInDeg_append (beforeEdges : List (Nat × Nat)) (acc : List Nat)
    (u v : Nat) (hu : u ∉ acc) :
    remInDeg beforeEdges (acc ++ [u]) v +
        (beforeEdges.filter (fun e => e.1 = u && e.2 = v)).length =
      remInDeg beforeEdges acc v := by
  simp only [remInDeg]
  let p : Nat × Nat → Bool := fun e => decide (e.2 = v) && decide (e.1 ∉ acc)
  let q : Nat × Nat → Bool := fun e => decide (e.1 = u)
  have hleft : ∀ e ∈ beforeEdges,
      (decide (e.2 = v) && decide (e.1 ∉ (acc ++ [u]))) = (p e && !q e) := by
    intro e _
    simp [p, q, List.mem_append, Bool.and_assoc]
  have hright : ∀ e ∈ beforeEdges,
      (decide (e.1 = u) && decide (e.2 = v)) = (p e && q e) := by
    intro e _
    simp only [p, q]
    by_cases heq : e.1 = u
    · simp [heq, hu, Bool.and_true, Bool.true_and]
    · simp [heq]
  rw [List.filter_congr hleft, List.filter_congr hright]
  change (beforeEdges.filter fun e => p e && !q e).length +
      (beforeEdges.filter fun e => p e && q e).length =
    (beforeEdges.filter (fun e => decide (e.2 = v) && decide (e.1 ∉ acc))).length
  have hp : beforeEdges.filter p =
      beforeEdges.filter (fun e => decide (e.2 = v) && decide (e.1 ∉ acc)) := rfl
  rw [← hp]
  exact Nat.add_comm _ _ ▸ filter_length_split p q beforeEdges

private theorem kahnTopo_indeg0_eq (n : Nat) (beforeEdges : List (Nat × Nat))
    {v : Nat} (hv : v < n) :
    indegGet
      ((List.range n).map fun w =>
        (beforeEdges.filter (fun e => e.2 = w)).length)
      v =
      remInDeg beforeEdges [] v := by
  simp only [indegGet, remInDeg_nil_acc]
  have hlen :
      ((List.range n).map fun w =>
        (beforeEdges.filter (fun e => e.2 = w)).length).length = n := by
    simp [List.length_map, List.length_range]
  rw [List.getElem?_eq_getElem (by omega)]
  simp only [Option.getD_some, List.getElem_map, List.getElem_range]

/-- Bounded edges: every endpoint is `< n`. -/
private def edgesBounded (n : Nat) (edges : List (Nat × Nat)) : Prop :=
  ∀ e ∈ edges, e.1 < n ∧ e.2 < n

private theorem filterMap_nbrs_count (beforeEdges : List (Nat × Nat)) (u w : Nat) :
    ((beforeEdges.filterMap fun ⟨a, b⟩ => if a = u then some b else none).count w) =
      (beforeEdges.filter fun e => e.1 = u && e.2 = w).length := by
  induction beforeEdges with
  | nil => simp
  | cons e es ih =>
    rcases e with ⟨a, b⟩
    simp only [List.filterMap_cons, List.filter_cons]
    by_cases ha : a = u
    · by_cases hb : b = w
      · simp [ha, hb, ih]
      · simp [ha, hb, ih]
    · simp [ha, ih]

private theorem foldl_indegSet_sub (indeg : List Nat) (nbrs : List Nat) (w : Nat)
    (hw : w < indeg.length) :
    indegGet (nbrs.foldl (fun ig b => indegSet ig b (indegGet ig b - 1)) indeg) w =
      indegGet indeg w - nbrs.count w := by
  induction nbrs generalizing indeg with
  | nil => simp
  | cons b bs ih =>
    simp only [List.foldl_cons]
    have hw' : w < (indegSet indeg b (indegGet indeg b - 1)).length := by
      rw [indegSet_length]; exact hw
    rw [ih _ hw']
    by_cases hb : b = w
    · rw [hb, indegGet_indegSet_eq _ _ _ hw]
      simp [Nat.sub_sub, Nat.add_comm 1]
    · rw [indegGet_indegSet_ne indeg b w _ (Ne.symm hb)]
      simp [hb]

/-- After emitting `u`, foldl-decrements preserve `remInDeg` for indices `< indeg.length`. -/
private theorem foldl_indeg_remInDeg (beforeEdges : List (Nat × Nat))
    (acc : List Nat) (u : Nat) (indeg : List Nat)
    (hu : u ∉ acc)
    (hinv : ∀ w < indeg.length, indegGet indeg w = remInDeg beforeEdges acc w)
    {w : Nat} (hw : w < indeg.length) :
    indegGet
        ((beforeEdges.filterMap fun ⟨a, b⟩ => if a = u then some b else none).foldl
          (fun ig b => indegSet ig b (indegGet ig b - 1)) indeg)
        w =
      remInDeg beforeEdges (acc ++ [u]) w := by
  set nbrs := beforeEdges.filterMap fun ⟨a, b⟩ => if a = u then some b else none
  have hsub := foldl_indegSet_sub indeg nbrs w hw
  have hcnt : nbrs.count w =
      (beforeEdges.filter fun e => e.1 = u && e.2 = w).length :=
    filterMap_nbrs_count beforeEdges u w
  have happ := remInDeg_append beforeEdges acc u w hu
  have hinvw := hinv w hw
  rw [hsub, hinvw, hcnt]
  exact (Nat.eq_sub_of_add_eq happ).symm

private theorem getElem?_append_left_of_eq {α} {l₁ l₂ : List α} {i : Nat} {x : α}
    (h : l₁[i]? = some x) : (l₁ ++ l₂)[i]? = some x := by
  have hi : i < l₁.length := (List.getElem?_eq_some_iff.mp h).1
  rw [List.getElem?_append_left hi, h]

private theorem getElem?_append_snoc {α} (l : List α) (x : α) :
    (l ++ [x])[l.length]? = some x := by
  rw [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
  rfl

private theorem foldl_indegSet_length (indeg : List Nat) (nbrs : List Nat) :
    (nbrs.foldl (fun ig b => indegSet ig b (indegGet ig b - 1)) indeg).length =
      indeg.length := by
  induction nbrs generalizing indeg with
  | nil => rfl
  | cons b bs ih =>
    simp only [List.foldl_cons]
    rw [ih, indegSet_length]

private theorem filterMap_succ_nodup (beforeEdges : List (Nat × Nat))
    (hedges_nodup : beforeEdges.Nodup) (u : Nat) :
    (beforeEdges.filterMap fun ⟨a, b⟩ => if a = u then some b else none).Nodup := by
  refine List.Nodup.filterMap ?_ hedges_nodup
  intro e1 e2 b hb1 hb2
  rcases e1 with ⟨a1, b1⟩
  rcases e2 with ⟨a2, b2⟩
  by_cases h1 : a1 = u
  · by_cases h2 : a2 = u
    · simp only [h1, h2, ↓reduceIte, Option.mem_def, Option.some.injEq] at hb1 hb2
      subst hb1; subst hb2
      simp [h1, h2]
    · simp [h2] at hb2
  · simp [h1] at hb1

/-- Core order invariant of `kahnGo` under bounded edges.
    Needs `beforeEdges.Nodup` so successor lists stay Nodup (multi-edges can
    duplicate `ready` and break `b ∉ acc`). Also tracks `remInDeg = 0` on `acc`. -/
private theorem kahnGo_edge_before_of_bounded (beforeEdges : List (Nat × Nat))
    (n : Nat) (hn : edgesBounded n beforeEdges) (hedges_nodup : beforeEdges.Nodup) :
    ∀ (fuel : Nat) (indeg ready acc : List Nat),
      indeg.length = n →
      (∀ w < n, indegGet indeg w = remInDeg beforeEdges acc w) →
      (∀ b ∈ ready, b < n ∧ remInDeg beforeEdges acc b = 0 ∧ b ∉ acc) →
      ready.Nodup →
      (∀ y ∈ acc, remInDeg beforeEdges acc y = 0) →
      (∀ {x y i j : Nat}, (x, y) ∈ beforeEdges →
        acc[i]? = some x → acc[j]? = some y → i < j) →
      ∀ {x y i j : Nat}, (x, y) ∈ beforeEdges →
        (kahnGo beforeEdges fuel indeg ready acc)[i]? = some x →
        (kahnGo beforeEdges fuel indeg ready acc)[j]? = some y → i < j := by
  intro fuel
  induction fuel with
  | zero =>
    intro indeg ready acc _hlen _hinv _hready _hnodup _hacc hedge x y i j he hi hj
    simp only [kahnGo] at hi hj
    exact hedge he hi hj
  | succ fuel ih =>
    intro indeg ready acc hlen hinv hready hnodup hacc hedge x y i j he hi hj
    cases ready with
    | nil =>
      simp only [kahnGo] at hi hj
      exact hedge he hi hj
    | cons u us =>
      simp only [kahnGo] at hi hj
      set acc' := acc ++ [u]
      set nbrs := beforeEdges.filterMap fun ⟨a, b⟩ => if a = u then some b else none
      set indeg' := nbrs.foldl (fun ig b => indegSet ig b (indegGet ig b - 1)) indeg
      set newReady := nbrs.filter fun b =>
        indegGet indeg' b = 0 && b ∉ acc' && b ∉ us
      have hu_ready := hready u List.mem_cons_self
      have hu : u ∉ acc := hu_ready.2.2
      have hu_lt : u < n := hu_ready.1
      have hu_deg : remInDeg beforeEdges acc u = 0 := hu_ready.2.1
      have hu_us : u ∉ us := (List.nodup_cons.mp hnodup).1
      have hlen' : indeg'.length = n := by
        simp only [indeg']
        rw [foldl_indegSet_length, hlen]
      have hinv' : ∀ w < n, indegGet indeg' w = remInDeg beforeEdges acc' w := by
        intro w hw
        have hw' : w < indeg.length := by omega
        simpa [indeg', nbrs, acc'] using
          foldl_indeg_remInDeg beforeEdges acc u indeg hu
            (fun w'' hw'' => by
              have : w'' < n := by omega
              exact hinv w'' this) hw'
      have hacc' : ∀ z ∈ acc', remInDeg beforeEdges acc' z = 0 := by
        intro z hz
        have hz' : z ∈ acc ∨ z = u := by
          simpa [acc', List.mem_append, List.mem_singleton] using hz
        cases hz' with
        | inl hzacc =>
          have happ := remInDeg_append beforeEdges acc u z hu
          have h0 := hacc z hzacc
          have : remInDeg beforeEdges (acc ++ [u]) z = 0 := by omega
          simpa [acc'] using this
        | inr hzu =>
          rw [hzu]
          have happ := remInDeg_append beforeEdges acc u u hu
          have : remInDeg beforeEdges (acc ++ [u]) u = 0 := by
            have h0 := hu_deg
            omega
          simpa [acc'] using this
      have hready' : ∀ b ∈ us ++ newReady,
          b < n ∧ remInDeg beforeEdges acc' b = 0 ∧ b ∉ acc' := by
        intro b hb
        simp only [List.mem_append] at hb
        cases hb with
        | inl hbus =>
          have hb0 := hready b (List.mem_cons_of_mem u hbus)
          refine ⟨hb0.1, ?_, ?_⟩
          · have happ := remInDeg_append beforeEdges acc u b hu
            have h0 := hb0.2.1
            have : remInDeg beforeEdges (acc ++ [u]) b = 0 := by omega
            simpa [acc'] using this
          · intro hin
            have hin' : b ∈ acc ∨ b = u := by
              simpa [acc', List.mem_append, List.mem_singleton] using hin
            cases hin' with
            | inl h => exact hb0.2.2 h
            | inr h => exact hu_us (h ▸ hbus)
        | inr hbnew =>
          have ⟨hbmem, hcond⟩ := List.mem_filter.mp hbnew
          simp only [Bool.and_eq_true, decide_eq_true_eq] at hcond
          obtain ⟨⟨hz, hnotin⟩, _⟩ := hcond
          have hb_lt : b < n := by
            simp only [nbrs, List.mem_filterMap] at hbmem
            obtain ⟨e, hee, hopt⟩ := hbmem
            rcases e with ⟨a, b'⟩
            by_cases ha : a = u
            · simp only [ha, ↓reduceIte, Option.some.injEq] at hopt
              subst hopt; exact (hn _ hee).2
            · simp [ha] at hopt
          refine ⟨hb_lt, by rwa [← hinv' b hb_lt], hnotin⟩
      have hnodup' : (us ++ newReady).Nodup := by
        have hus : us.Nodup := (List.nodup_cons.mp hnodup).2
        have hnbrs : nbrs.Nodup := by
          simpa [nbrs] using filterMap_succ_nodup beforeEdges hedges_nodup u
        have hnew : newReady.Nodup := List.Nodup.filter _ hnbrs
        refine List.Nodup.append hus hnew ?_
        intro x hx hx'
        have hcond := (List.mem_filter.mp hx').2
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hcond
        exact hcond.2 hx
      have hedge' : ∀ {x y i j : Nat}, (x, y) ∈ beforeEdges →
          acc'[i]? = some x → acc'[j]? = some y → i < j := by
        intro x y i j he' hi' hj'
        have hi_lt : i < acc'.length := (List.getElem?_eq_some_iff.mp hi').1
        have hj_lt : j < acc'.length := (List.getElem?_eq_some_iff.mp hj').1
        simp only [acc', List.length_append, List.length_singleton] at hi_lt hj_lt
        by_cases hi_acc : i < acc.length
        · have hi'' : acc[i]? = some x := by
            rwa [List.getElem?_append_left hi_acc] at hi'
          by_cases hj_acc : j < acc.length
          · have hj'' : acc[j]? = some y := by
              rwa [List.getElem?_append_left hj_acc] at hj'
            exact hedge he' hi'' hj''
          · have hj_eq : j = acc.length := by omega
            have hyu : y = u := by
              have : acc'[j]? = some u := by
                simp only [acc', hj_eq]
                exact getElem?_append_snoc acc u
              simp only [this, Option.some.injEq] at hj'; exact hj'.symm
            exact Nat.lt_of_lt_of_le hi_acc (by omega)
        · have hi_eq : i = acc.length := by omega
          have hxu : x = u := by
            have : acc'[i]? = some u := by
              simp only [acc', hi_eq]
              exact getElem?_append_snoc acc u
            simp only [this, Option.some.injEq] at hi'; exact hi'.symm
          have hy_mem : y ∈ acc' := List.mem_of_getElem? hj'
          have hy_mem' : y ∈ acc ∨ y = u := by
            simpa [acc', List.mem_append, List.mem_singleton] using hy_mem
          cases hy_mem' with
          | inl hyacc =>
            have heu : (u, y) ∈ beforeEdges := by simpa [hxu] using he'
            exact (hu (remInDeg_eq_zero_preds beforeEdges acc heu (hacc y hyacc))).elim
          | inr hyu =>
            have heu : (u, u) ∈ beforeEdges := by simpa [hxu, hyu] using he'
            exact (hu (remInDeg_eq_zero_preds beforeEdges acc heu hu_deg)).elim
      exact ih indeg' (us ++ newReady) acc' hlen' hinv' hready' hnodup' hacc' hedge'
        he hi hj

/-- Kahn emits sources before dependents, when all edge endpoints are `< n`
    and `edges` has no duplicates. -/
private theorem kahnTopo_edge_before (n : Nat) (edges : List (Nat × Nat))
    (hb : edgesBounded n edges) (hnodup : edges.Nodup)
    {u v : Nat} (he : (u, v) ∈ edges)
    {i j : Nat}
    (hi : (kahnTopo n edges)[i]? = some u)
    (hj : (kahnTopo n edges)[j]? = some v) :
    i < j := by
  simp only [kahnTopo] at hi hj
  refine kahnGo_edge_before_of_bounded edges n hb hnodup (n + 1)
    ((List.range n).map fun w => (edges.filter (fun e => e.2 = w)).length)
    ((List.range n).filter fun w =>
      indegGet ((List.range n).map fun w =>
        (edges.filter (fun e => e.2 = w)).length) w = 0)
    [] ?hlen ?hinv ?hready ?hnodup_ready ?hacc ?hedge he hi hj
  · simp [List.length_map, List.length_range]
  · intro w hw
    exact kahnTopo_indeg0_eq n edges hw
  · intro b hb'
    have hbmem := List.mem_filter.mp hb'
    refine ⟨List.mem_range.mp hbmem.1, ?_, by simp⟩
    have hdec : decide
        (indegGet ((List.range n).map fun w =>
          (edges.filter (fun e => e.2 = w)).length) b = 0) = true := hbmem.2
    have heq : indegGet ((List.range n).map fun w =>
        (edges.filter (fun e => e.2 = w)).length) b = 0 :=
      of_decide_eq_true hdec
    rwa [kahnTopo_indeg0_eq n edges (List.mem_range.mp hbmem.1)] at heq
  · exact List.Nodup.filter _ List.nodup_range
  · intro y hy; cases hy
  · intro x y i j _he' hi' _hj'
    simp at hi'

/-- `sccBeforeEdges` only emits component-index pairs. -/
private theorem sccBeforeEdges_bounded (succ : Nat → List Nat)
    (comps : List (List Nat)) :
    edgesBounded comps.length (sccBeforeEdges succ comps) := by
  intro e he
  simp only [sccBeforeEdges, List.mem_flatMap] at he
  obtain ⟨a, ha, h⟩ := he
  have ha' : a ∈ List.range comps.length := ha
  simp only [List.mem_filterMap] at h
  obtain ⟨b, hb, hopt⟩ := h
  by_cases hab : a = b
  · simp [hab] at hopt
  · simp only [hab, ↓reduceIte] at hopt
    cases hca : comps[a]? with
    | none => simp [hca] at hopt
    | some ca =>
      cases hcb : comps[b]? with
      | none => simp [hca, hcb] at hopt
      | some cb =>
        simp only [hca, hcb] at hopt
        split at hopt
        · next hdep =>
          simp only [Option.some.injEq] at hopt
          subst hopt
          exact ⟨List.mem_range.mp hb, List.mem_range.mp ha'⟩
        · simp at hopt

/-- Each `(dependency, dependent)` pair appears at most once. -/
private theorem sccBeforeEdges_nodup (succ : Nat → List Nat)
    (comps : List (List Nat)) :
    (sccBeforeEdges succ comps).Nodup := by
  simp only [sccBeforeEdges]
  set nc := comps.length
  refine (List.nodup_flatMap).2 ⟨?_, ?_⟩
  · intro a ha
    refine List.Nodup.filterMap ?_ List.nodup_range
    intro b1 b2 e he1 he2
    by_cases h1 : a = b1
    · simp [h1] at he1
    · by_cases h2 : a = b2
      · simp [h2] at he2
      · simp only [h1, h2, ↓reduceIte] at he1 he2
        cases hca : comps[a]? with
        | none => simp [hca] at he1
        | some ca =>
          cases hcb1 : comps[b1]? with
          | none => simp [hca, hcb1] at he1
          | some cb1 =>
            cases hcb2 : comps[b2]? with
            | none => simp [hca, hcb2] at he2
            | some cb2 =>
              simp only [hca, hcb1] at he1
              simp only [hca, hcb2] at he2
              split at he1
              · next =>
                split at he2
                · next =>
                  simp only [Option.mem_def, Option.some.injEq] at he1 he2
                  cases he1; cases he2
                  rfl
                · simp at he2
              · simp at he1
  · refine List.Pairwise.imp ?_ (List.nodup_iff_pairwise_ne.mp List.nodup_range)
    intro a1 a2 hne e he1 he2
    simp only [List.mem_filterMap] at he1 he2
    obtain ⟨b1, hb1, hopt1⟩ := he1
    obtain ⟨b2, hb2, hopt2⟩ := he2
    by_cases h1 : a1 = b1
    · simp [h1] at hopt1
    · by_cases h2 : a2 = b2
      · simp [h2] at hopt2
      · simp only [h1, h2, ↓reduceIte] at hopt1 hopt2
        cases hca1 : comps[a1]? with
        | none => simp [hca1] at hopt1
        | some ca1 =>
          cases hcb1 : comps[b1]? with
          | none => simp [hca1, hcb1] at hopt1
          | some cb1 =>
            cases hca2 : comps[a2]? with
            | none => simp [hca2] at hopt2
            | some ca2 =>
              cases hcb2 : comps[b2]? with
              | none => simp [hca2, hcb2] at hopt2
              | some cb2 =>
                simp only [hca1, hcb1] at hopt1
                simp only [hca2, hcb2] at hopt2
                split at hopt1
                · next =>
                  split at hopt2
                  · next =>
                    simp only [Option.some.injEq] at hopt1 hopt2
                    cases hopt1; cases hopt2
                    exact hne rfl
                  · simp at hopt2
                · simp at hopt1

/-- Positive remaining in-degree ⇒ some unemitted predecessor edge. -/
private theorem exists_pred_of_remInDeg_pos (beforeEdges : List (Nat × Nat))
    (acc : List Nat) {v : Nat} (hpos : 0 < remInDeg beforeEdges acc v) :
    ∃ u, (u, v) ∈ beforeEdges ∧ u ∉ acc := by
  simp only [remInDeg] at hpos
  obtain ⟨e, he⟩ := List.exists_mem_of_length_pos hpos
  have ⟨hem, hcond⟩ := List.mem_filter.mp he
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hcond
  rcases e with ⟨u, v'⟩
  obtain ⟨hv, hu⟩ := hcond
  subst hv
  exact ⟨u, hem, hu⟩

/-- Length bound from Nodup + range membership. -/
private theorem length_le_of_nodup_lt {l : List Nat} {n : Nat}
    (hn : l.Nodup) (hbound : ∀ x ∈ l, x < n) :
    l.length ≤ n := by
  have hsub : l.toFinset ⊆ Finset.range n := by
    intro x hx
    exact Finset.mem_range.mpr (hbound x (List.mem_toFinset.mp hx))
  have := Finset.card_le_card hsub
  rwa [List.toFinset_card_of_nodup hn, Finset.card_range] at this

/-- Zero-closed ready invariant: every `remInDeg = 0` vertex is queued or emitted. -/
private theorem kahnGo_zero_closed (beforeEdges : List (Nat × Nat))
    (n : Nat) (hn : edgesBounded n beforeEdges) (hedges_nodup : beforeEdges.Nodup) :
    ∀ (fuel : Nat) (indeg ready acc : List Nat),
      indeg.length = n →
      (∀ w < n, indegGet indeg w = remInDeg beforeEdges acc w) →
      (∀ b ∈ ready, b < n ∧ remInDeg beforeEdges acc b = 0 ∧ b ∉ acc) →
      ready.Nodup →
      (∀ y ∈ acc, y < n ∧ remInDeg beforeEdges acc y = 0) →
      acc.Nodup →
      (∀ v < n, remInDeg beforeEdges acc v = 0 → v ∈ acc ∨ v ∈ ready) →
      fuel + acc.length ≥ n + 1 →
      let out := kahnGo beforeEdges fuel indeg ready acc
      out.Nodup ∧
        (∀ x ∈ out, x < n) ∧
        (out.length = n ∨
          (∃ v < n, v ∉ out ∧
            ∀ w < n, w ∉ out → ∃ u, u < n ∧ u ∉ out ∧ (u, w) ∈ beforeEdges)) := by
  intro fuel
  induction fuel with
  | zero =>
    intro indeg ready acc hlen hinv hready hnodup_r hacc hnodup_a hclosed hfuel
    -- fuel = 0 ⇒ acc.length ≥ n + 1, contradicting Nodup+bound
    have hacc_lt : ∀ y ∈ acc, y < n := fun y hy => (hacc y hy).1
    have hle := length_le_of_nodup_lt hnodup_a hacc_lt
    omega
  | succ fuel ih =>
    intro indeg ready acc hlen hinv hready hnodup_r hacc hnodup_a hclosed hfuel
    cases ready with
    | nil =>
      simp only [kahnGo]
      refine ⟨hnodup_a, fun x hx => (hacc x hx).1, ?_⟩
      by_cases hlen_acc : acc.length = n
      · exact Or.inl hlen_acc
      · have hlt : acc.length < n := by
          have hle := length_le_of_nodup_lt hnodup_a (fun y hy => (hacc y hy).1)
          omega
        refine Or.inr ?_
        have hex : ∃ v, v < n ∧ v ∉ acc := by
          by_contra hnone
          push_neg at hnone
          have hsub : Finset.range n ⊆ acc.toFinset := by
            intro v hv
            exact List.mem_toFinset.mpr (hnone v (Finset.mem_range.mp hv))
          have hcard := Finset.card_le_card hsub
          simp only [Finset.card_range, List.toFinset_card_of_nodup hnodup_a] at hcard
          omega
        obtain ⟨v0, hv0, hv0n⟩ := hex
        refine ⟨v0, hv0, hv0n, ?_⟩
        intro w hw hwn
        have hpos : 0 < remInDeg beforeEdges acc w := by
          by_contra hnp
          have hz : remInDeg beforeEdges acc w = 0 := by omega
          have := hclosed w hw hz
          simp only [List.mem_nil_iff, or_false] at this
          exact hwn this
        obtain ⟨u, he, hu⟩ := exists_pred_of_remInDeg_pos beforeEdges acc hpos
        exact ⟨u, (hn _ he).1, hu, he⟩
    | cons u us =>
      simp only [kahnGo]
      set acc' := acc ++ [u]
      set nbrs := beforeEdges.filterMap fun ⟨a, b⟩ => if a = u then some b else none
      set indeg' := nbrs.foldl (fun ig b => indegSet ig b (indegGet ig b - 1)) indeg
      set newReady := nbrs.filter fun b =>
        indegGet indeg' b = 0 && b ∉ acc' && b ∉ us
      have hu_ready := hready u List.mem_cons_self
      have hu : u ∉ acc := hu_ready.2.2
      have hu_lt : u < n := hu_ready.1
      have hu_deg : remInDeg beforeEdges acc u = 0 := hu_ready.2.1
      have hu_us : u ∉ us := (List.nodup_cons.mp hnodup_r).1
      have hlen' : indeg'.length = n := by
        simp only [indeg']
        rw [foldl_indegSet_length, hlen]
      have hinv' : ∀ w < n, indegGet indeg' w = remInDeg beforeEdges acc' w := by
        intro w hw
        have hw' : w < indeg.length := by omega
        simpa [indeg', nbrs, acc'] using
          foldl_indeg_remInDeg beforeEdges acc u indeg hu
            (fun w'' hw'' => by
              have : w'' < n := by omega
              exact hinv w'' this) hw'
      have hacc' : ∀ z ∈ acc', z < n ∧ remInDeg beforeEdges acc' z = 0 := by
        intro z hz
        have hz' : z ∈ acc ∨ z = u := by
          simpa [acc', List.mem_append, List.mem_singleton] using hz
        cases hz' with
        | inl hzacc =>
          refine ⟨(hacc z hzacc).1, ?_⟩
          have happ := remInDeg_append beforeEdges acc u z hu
          have h0 := (hacc z hzacc).2
          have : remInDeg beforeEdges (acc ++ [u]) z = 0 := by omega
          simpa [acc'] using this
        | inr hzu =>
          rw [hzu]
          refine ⟨hu_lt, ?_⟩
          have happ := remInDeg_append beforeEdges acc u u hu
          have : remInDeg beforeEdges (acc ++ [u]) u = 0 := by omega
          simpa [acc'] using this
      have hready' : ∀ b ∈ us ++ newReady,
          b < n ∧ remInDeg beforeEdges acc' b = 0 ∧ b ∉ acc' := by
        intro b hb
        simp only [List.mem_append] at hb
        cases hb with
        | inl hbus =>
          have hb0 := hready b (List.mem_cons_of_mem u hbus)
          refine ⟨hb0.1, ?_, ?_⟩
          · have happ := remInDeg_append beforeEdges acc u b hu
            have h0 := hb0.2.1
            have : remInDeg beforeEdges (acc ++ [u]) b = 0 := by omega
            simpa [acc'] using this
          · intro hin
            have hin' : b ∈ acc ∨ b = u := by
              simpa [acc', List.mem_append, List.mem_singleton] using hin
            cases hin' with
            | inl h => exact hb0.2.2 h
            | inr h => exact hu_us (h ▸ hbus)
        | inr hbnew =>
          have ⟨hbmem, hcond⟩ := List.mem_filter.mp hbnew
          simp only [Bool.and_eq_true, decide_eq_true_eq] at hcond
          obtain ⟨⟨hz, hnotin⟩, _⟩ := hcond
          have hb_lt : b < n := by
            simp only [nbrs, List.mem_filterMap] at hbmem
            obtain ⟨e, hee, hopt⟩ := hbmem
            rcases e with ⟨a, b'⟩
            by_cases ha : a = u
            · simp only [ha, ↓reduceIte, Option.some.injEq] at hopt
              subst hopt; exact (hn _ hee).2
            · simp [ha] at hopt
          refine ⟨hb_lt, by rwa [← hinv' b hb_lt], hnotin⟩
      have hnodup' : (us ++ newReady).Nodup := by
        have hus : us.Nodup := (List.nodup_cons.mp hnodup_r).2
        have hnbrs : nbrs.Nodup := by
          simpa [nbrs] using filterMap_succ_nodup beforeEdges hedges_nodup u
        have hnew : newReady.Nodup := List.Nodup.filter _ hnbrs
        refine List.Nodup.append hus hnew ?_
        intro x hx hx'
        have hcond := (List.mem_filter.mp hx').2
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hcond
        exact hcond.2 hx
      have hnodup_a' : acc'.Nodup := by
        refine List.Nodup.append hnodup_a (List.nodup_singleton u) ?_
        intro x hx hx'
        simp only [List.mem_singleton] at hx'
        exact hu (hx' ▸ hx)
      have hclosed' : ∀ v < n, remInDeg beforeEdges acc' v = 0 →
          v ∈ acc' ∨ v ∈ us ++ newReady := by
        intro v hv hz'
        by_cases hvacc : v ∈ acc'
        · exact Or.inl hvacc
        · right
          -- remInDeg became / stayed 0; not in acc'
          have happ := remInDeg_append beforeEdges acc u v hu
          have hrem' : remInDeg beforeEdges (acc ++ [u]) v = 0 := by
            simpa [acc'] using hz'
          have hcount :
              (beforeEdges.filter fun e => e.1 = u && e.2 = v).length =
                remInDeg beforeEdges acc v := by omega
          by_cases hz0 : remInDeg beforeEdges acc v = 0
          · have hmem := hclosed v hv hz0
            simp only [List.mem_cons] at hmem
            cases hmem with
            | inl h =>
              exact (hvacc (by simpa [acc', List.mem_append] using Or.inl h)).elim
            | inr h =>
              cases h with
              | inl hvu =>
                exact (hvacc (by simp [acc', hvu, List.mem_append])).elim
              | inr hus =>
                exact List.mem_append.mpr (Or.inl hus)
          · -- newly zeroed via edges from u ⇒ in nbrs, hence newReady
            have hpos : 0 < remInDeg beforeEdges acc v := by omega
            have hcnt_pos :
                0 < (beforeEdges.filter fun e => e.1 = u && e.2 = v).length := by
              omega
            obtain ⟨⟨a, b⟩, he⟩ := List.exists_mem_of_length_pos hcnt_pos
            have ⟨hem, hcond⟩ := List.mem_filter.mp he
            simp only [Bool.and_eq_true, decide_eq_true_eq] at hcond
            obtain ⟨ha, hb⟩ := hcond
            have hbmem : v ∈ nbrs := by
              simp only [nbrs, List.mem_filterMap]
              refine ⟨(a, b), hem, ?_⟩
              simp [ha, hb]
            have hvus : v ∉ us := by
              intro hus
              have hb0 := hready v (List.mem_cons_of_mem u hus)
              exact hz0 hb0.2.1
            have hnew : v ∈ newReady := by
              refine List.mem_filter.mpr ⟨hbmem, ?_⟩
              simp only [Bool.and_eq_true, decide_eq_true_eq]
              exact ⟨⟨by rwa [← hinv' v hv] at hrem', hvacc⟩, hvus⟩
            exact List.mem_append.mpr (Or.inr hnew)
      have hfuel' : fuel + acc'.length ≥ n + 1 := by
        simp only [acc', List.length_append, List.length_singleton]
        omega
      exact ih indeg' (us ++ newReady) acc' hlen' hinv' hready' hnodup' hacc'
        hnodup_a' hclosed' hfuel'

/-- Stuck remainder with a predecessor in the remainder ⇒ a before-edge cycle
    (two distinct vertices mutually reachable by `TransGen`). -/
private theorem exists_edge_cycle_of_pred_closed (beforeEdges : List (Nat × Nat))
    {n : Nat} {out : List Nat}
    (hout_nodup : out.Nodup)
    (hlen : out.length < n)
    (hloop : ∀ u, (u, u) ∉ beforeEdges)
    (hpred : ∀ w < n, w ∉ out → ∃ u, u < n ∧ u ∉ out ∧ (u, w) ∈ beforeEdges) :
    ∃ u v, u ≠ v ∧
      Relation.TransGen (fun a b => (a, b) ∈ beforeEdges) u v ∧
      Relation.TransGen (fun a b => (a, b) ∈ beforeEdges) v u := by
  classical
  let rem := (List.range n).filter (fun v => decide (v ∉ out))
  have hrem_nodup : rem.Nodup := List.Nodup.filter _ List.nodup_range
  have hrem_mem : ∀ v ∈ rem, v < n ∧ v ∉ out := by
    intro v hv
    have ⟨hrm, hcond⟩ := List.mem_filter.mp hv
    exact ⟨List.mem_range.mp hrm, of_decide_eq_true hcond⟩
  have hrem_ne : rem ≠ [] := by
    intro hempty
    have hall : ∀ v < n, v ∈ out := by
      intro v hv
      by_contra hnotin
      have : v ∈ rem :=
        List.mem_filter.mpr ⟨List.mem_range.mpr hv, decide_eq_true hnotin⟩
      simp [hempty] at this
    have hsub : Finset.range n ⊆ out.toFinset := by
      intro v hv
      exact List.mem_toFinset.mpr (hall v (Finset.mem_range.mp hv))
    have hcard := Finset.card_le_card hsub
    simp only [Finset.card_range, List.toFinset_card_of_nodup hout_nodup] at hcard
    omega
  have pred_spec : ∀ v ∈ rem, ∃ u ∈ rem, (u, v) ∈ beforeEdges := by
    intro v hv
    obtain ⟨hvlt, hvout⟩ := hrem_mem v hv
    obtain ⟨u, hult, huout, he⟩ := hpred v hvlt hvout
    exact ⟨u, List.mem_filter.mpr ⟨List.mem_range.mpr hult, decide_eq_true huout⟩, he⟩
  let predOf (v : Nat) : Nat :=
    if hv : v ∈ rem then Classical.choose (pred_spec v hv) else v
  have predOf_spec : ∀ v ∈ rem,
      predOf v ∈ rem ∧ (predOf v, v) ∈ beforeEdges := by
    intro v hv
    dsimp [predOf]
    rw [dif_pos hv]
    exact Classical.choose_spec (pred_spec v hv)
  let walk : Nat → Nat :=
    Nat.rec (rem.head hrem_ne) fun _ w => predOf w
  have walk_mem : ∀ k, walk k ∈ rem := by
    intro k
    induction k with
    | zero => exact List.head_mem hrem_ne
    | succ k ih => exact (predOf_spec (walk k) ih).1
  have walk_edge : ∀ k, (walk (k + 1), walk k) ∈ beforeEdges := by
    intro k
    exact (predOf_spec (walk k) (walk_mem k)).2
  let ws := (List.range (rem.length + 1)).map walk
  have hws_len : ws.length = rem.length + 1 := by
    simp [ws, List.length_map, List.length_range]
  have hws_mem : ∀ x ∈ ws, x ∈ rem := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
    exact walk_mem _
  have hws_not_nodup : ¬ws.Nodup := by
    intro hnodup
    have hsub : ws.toFinset ⊆ rem.toFinset := by
      intro x hx
      exact List.mem_toFinset.mpr (hws_mem x (List.mem_toFinset.mp hx))
    have hcard := Finset.card_le_card hsub
    rw [List.toFinset_card_of_nodup hnodup, List.toFinset_card_of_nodup hrem_nodup,
      hws_len] at hcard
    omega
  obtain ⟨d, hd⟩ := (List.exists_duplicate_iff_not_nodup).2 hws_not_nodup
  obtain ⟨i, j, hij, hx_i, hx_j⟩ := (List.duplicate_iff_exists_distinct_get).1 hd
  have hwi : ws[i.1] = walk i.1 := by
    simp only [ws, List.getElem_map, List.getElem_range]
  have hwj : ws[j.1] = walk j.1 := by
    simp only [ws, List.getElem_map, List.getElem_range]
  have heq : walk i.1 = walk j.1 := by
    have ei : ws[i.1] = d := by simpa [List.get_eq_getElem] using hx_i.symm
    have ej : ws[j.1] = d := by simpa [List.get_eq_getElem] using hx_j.symm
    rw [hwi] at ei; rw [hwj] at ej; exact ei.trans ej.symm
  have hlt : i.1 < j.1 := hij
  let ilo := i.1
  let j0 := j.1
  have hj0_ge : ilo + 2 ≤ j0 := by
    have hne1 : j0 ≠ ilo + 1 := by
      intro h
      have he : walk (ilo + 1) = walk ilo := by
        rw [show ilo + 1 = j0 from h.symm, ← heq]
      exact hloop _ (by simpa [he] using walk_edge ilo)
    omega
  have hj0_eq : walk j0 = walk ilo := heq.symm
  -- TransGen along walk (m+d) → … → walk m
  have hseg : ∀ m d, Relation.ReflTransGen (fun a b => (a, b) ∈ beforeEdges)
      (walk (m + d)) (walk m) := by
    intro m d
    induction d with
    | zero => exact Relation.ReflTransGen.refl
    | succ d ih =>
      exact Relation.ReflTransGen.head (walk_edge (m + d)) ih
  have huv : walk (ilo + 1) ≠ walk ilo := by
    intro he
    exact hloop _ (by simpa [he] using walk_edge ilo)
  refine ⟨walk (ilo + 1), walk ilo, huv, ?_, ?_⟩
  · exact Relation.TransGen.single (walk_edge ilo)
  · have hrt : Relation.ReflTransGen (fun a b => (a, b) ∈ beforeEdges)
        (walk j0) (walk (ilo + 1)) := by
      have := hseg (ilo + 1) (j0 - (ilo + 1))
      rwa [show (ilo + 1) + (j0 - (ilo + 1)) = j0 by omega] at this
    have hrt' : Relation.ReflTransGen (fun a b => (a, b) ∈ beforeEdges)
        (walk ilo) (walk (ilo + 1)) := by
      rwa [← hj0_eq]
    exact (Relation.reflTransGen_iff_eq_or_transGen.mp hrt').resolve_left huv

/-- No self-loops in `sccBeforeEdges`. -/
private theorem sccBeforeEdges_no_loop (succ : Nat → List Nat)
    (comps : List (List Nat)) (u : Nat) :
    (u, u) ∉ sccBeforeEdges succ comps := by
  intro he
  simp only [sccBeforeEdges, List.mem_flatMap] at he
  obtain ⟨a, ha, h⟩ := he
  simp only [List.mem_filterMap] at h
  obtain ⟨b, hb, hopt⟩ := h
  by_cases hab : a = b
  · simp [hab] at hopt
  · simp only [hab, ↓reduceIte] at hopt
    cases hca : comps[a]? with
    | none => simp [hca] at hopt
    | some ca =>
      cases hcb : comps[b]? with
      | none => simp [hca, hcb] at hopt
      | some cb =>
        simp only [hca, hcb] at hopt
        split at hopt
        · next =>
          simp only [Option.some.injEq] at hopt
          cases hopt
          exact hab rfl
        · simp at hopt

/-- Unpack a condensation before-edge into a concrete `bindSucc` hop. -/
private theorem exists_succ_of_mem_sccBeforeEdges (succ : Nat → List Nat)
    (comps : List (List Nat)) {u v : Nat}
    (he : (u, v) ∈ sccBeforeEdges succ comps) :
    u ≠ v ∧ u < comps.length ∧ v < comps.length ∧
      ∃ ca cb, comps[v]? = some ca ∧ comps[u]? = some cb ∧
        ∃ p ∈ ca, ∃ q ∈ cb, q ∈ succ p := by
  simp only [sccBeforeEdges, List.mem_flatMap] at he
  obtain ⟨a, ha, h⟩ := he
  simp only [List.mem_filterMap] at h
  obtain ⟨b, hb, hopt⟩ := h
  by_cases hab : a = b
  · simp [hab] at hopt
  · simp only [hab, ↓reduceIte] at hopt
    have ha' := List.mem_range.mp ha
    have hb' := List.mem_range.mp hb
    cases hca : comps[a]? with
    | none => simp [hca] at hopt
    | some ca =>
      cases hcb : comps[b]? with
      | none => simp [hca, hcb] at hopt
      | some cb =>
        simp only [hca, hcb] at hopt
        split at hopt
        · next hdep =>
          simp only [Option.some.injEq] at hopt
          obtain ⟨rfl, rfl⟩ := hopt
          refine ⟨Ne.symm hab, hb', ha', ca, cb, ?_, ?_, ?_⟩
          · simpa [List.getElem?_eq_getElem ha'] using hca
          · simpa [List.getElem?_eq_getElem hb'] using hcb
          · simp only [compDependsOn, List.any_eq_true] at hdep
            obtain ⟨p, hp, hq⟩ := hdep
            obtain ⟨q, hqsucc, hqmem⟩ := hq
            exact ⟨p, hp, q, by simpa using hqmem, hqsucc⟩
        · simp at hopt

/-- One condensation before-edge ⇒ `DepReach` from dependent component into dependency. -/
private theorem DepReach_of_sccBeforeEdge (binds : List Surface.Binding)
    {u v x y : Nat}
    (he : (u, v) ∈ sccBeforeEdges (bindSucc binds) (sccIndexSets binds))
    {ca cb : List Nat}
    (hca : (sccIndexSets binds)[v]? = some ca)
    (hcb : (sccIndexSets binds)[u]? = some cb)
    (hx : x ∈ ca) (hy : y ∈ cb)
    (hx_lt : x < binds.length) (hy_lt : y < binds.length) :
    DepReach binds (binds[x]).name (binds[y]).name := by
  set comps := sccIndexSets binds
  obtain ⟨_hne, _hu_lt, _hv_lt, ca', cb', hca', hcb', p, hp, q, hq, hsucc⟩ :=
    exists_succ_of_mem_sccBeforeEdges (bindSucc binds) comps he
  have hca_eq : ca' = ca := by
    rw [hca'] at hca; exact Option.some.inj hca
  have hcb_eq : cb' = cb := by
    rw [hcb'] at hcb; exact Option.some.inj hcb
  rw [hca_eq] at hp; rw [hcb_eq] at hq
  have hv_mem : ca ∈ comps := List.mem_of_getElem? hca
  have hu_mem : cb ∈ comps := List.mem_of_getElem? hcb
  have hp_lt := sccIndexSets_mem_lt binds ca hv_mem p hp
  have hq_lt := sccIndexSets_mem_lt binds cb hu_mem q hq
  obtain ⟨b, b', hb, hb', hedge⟩ := DepEdge_of_bindSucc hsucc
  have hb1 : b = binds[p] := by
    rw [List.getElem?_eq_getElem hp_lt] at hb; exact Option.some.inj hb.symm
  have hb2 : b' = binds[q] := by
    rw [List.getElem?_eq_getElem hq_lt] at hb'; exact Option.some.inj hb'.symm
  rw [hb1, hb2] at hedge
  have hxp : DepMutual binds (binds[x]).name (binds[p]).name :=
    sccIndexSets_comp_depMutual binds hv_mem hx hp
  have hqy : DepMutual binds (binds[q]).name (binds[y]).name :=
    sccIndexSets_comp_depMutual binds hu_mem hq hy
  exact DepReach_trans hxp.1 (DepReach.tail hedge hqy.1)

/-- Endpoints of a condensation path are valid component indices. -/
private theorem sccBeforeReach_lt (binds : List Surface.Binding)
    {u v : Nat}
    (h : Relation.TransGen
      (fun a b => (a, b) ∈ sccBeforeEdges (bindSucc binds) (sccIndexSets binds)) u v) :
    u < (sccIndexSets binds).length ∧ v < (sccIndexSets binds).length := by
  induction h with
  | single he =>
    exact ⟨(exists_succ_of_mem_sccBeforeEdges (bindSucc binds) _ he).2.1,
      (exists_succ_of_mem_sccBeforeEdges (bindSucc binds) _ he).2.2.1⟩
  | tail _hab hbc ih =>
    exact ⟨ih.1, (exists_succ_of_mem_sccBeforeEdges (bindSucc binds) _ hbc).2.2.1⟩

/-- Condensation path ⇒ `DepReach` from the path end's component back to the start's. -/
private theorem DepReach_of_sccBeforeReach (binds : List Surface.Binding)
    {u v : Nat}
    (h : Relation.TransGen
      (fun a b => (a, b) ∈ sccBeforeEdges (bindSucc binds) (sccIndexSets binds)) u v)
    {ca cb : List Nat}
    (hca : (sccIndexSets binds)[v]? = some ca)
    (hcb : (sccIndexSets binds)[u]? = some cb)
    {x y : Nat} (hx : x ∈ ca) (hy : y ∈ cb)
    (hx_lt : x < binds.length) (hy_lt : y < binds.length) :
    DepReach binds (binds[x]).name (binds[y]).name := by
  induction h generalizing ca cb x y with
  | single he =>
    exact DepReach_of_sccBeforeEdge binds he hca hcb hx hy hx_lt hy_lt
  | tail hab hbc ih =>
    -- hab : TransGen u w, hbc : (w, v) ∈ edges
    obtain ⟨_hne, _hw_lt, _hv_lt, cv, cw, hcv, hcw, p, hp, q, hq, hsucc⟩ :=
      exists_succ_of_mem_sccBeforeEdges (bindSucc binds) (sccIndexSets binds) hbc
    have hcv_eq : cv = ca := by
      rw [hcv] at hca; exact Option.some.inj hca
    rw [hcv_eq] at hp
    have hq_lt := sccIndexSets_mem_lt binds cw (List.mem_of_getElem? hcw) q hq
    have hp_lt := sccIndexSets_mem_lt binds ca (List.mem_of_getElem? hca) p hp
    have h_to_q : DepReach binds (binds[x]).name (binds[q]).name := by
      obtain ⟨b, b', hb, hb', hedge⟩ := DepEdge_of_bindSucc hsucc
      have hb1 : b = binds[p] := by
        rw [List.getElem?_eq_getElem hp_lt] at hb; exact Option.some.inj hb.symm
      have hb2 : b' = binds[q] := by
        rw [List.getElem?_eq_getElem hq_lt] at hb'; exact Option.some.inj hb'.symm
      rw [hb1, hb2] at hedge
      have hxp : DepMutual binds (binds[x]).name (binds[p]).name :=
        sccIndexSets_comp_depMutual binds (List.mem_of_getElem? hca) hx hp
      exact DepReach_trans hxp.1 (DepReach.tail hedge DepReach.refl)
    have h_from_q : DepReach binds (binds[q]).name (binds[y]).name :=
      ih hcw hcb hq hy hq_lt hy_lt
    exact DepReach_trans h_to_q h_from_q

private theorem eq_of_mem_of_mem_of_pairwise_disjoint {α} {L : List (List α)}
    (hdisj : List.Pairwise List.Disjoint L)
    {g g' : List α} (hg : g ∈ L) (hg' : g' ∈ L) {x : α}
    (hx : x ∈ g) (hx' : x ∈ g') : g = g' := by
  induction L with
  | nil => cases hg
  | cons hd tl ih =>
    have hdisj' := List.pairwise_cons.mp hdisj
    cases List.mem_cons.mp hg with
    | inl h =>
      subst h
      cases List.mem_cons.mp hg' with
      | inl h' => exact h'.symm
      | inr h' => exact (hdisj'.1 g' h' hx hx').elim
    | inr h =>
      cases List.mem_cons.mp hg' with
      | inl h' =>
        subst h'
        exact (hdisj'.1 g h hx' hx).elim
      | inr h' => exact ih hdisj'.2 h h'

/-- Each index appears in exactly one `sccIndexSets` component. -/
private theorem sccIndexSets_unique_comp (binds : List Surface.Binding) {i : Nat}
    (hi : i < binds.length) :
    ∃ g ∈ sccIndexSets binds, i ∈ g ∧
      ∀ g' ∈ sccIndexSets binds, i ∈ g' → g' = g := by
  have hperm := sccIndexSets_flatten_perm binds
  have himem : i ∈ (sccIndexSets binds).flatten :=
    (List.Perm.mem_iff hperm).2 (List.mem_range.mpr hi)
  obtain ⟨g, hg, hi'⟩ := List.mem_flatten.mp himem
  refine ⟨g, hg, hi', ?_⟩
  intro g' hg' hi''
  have hnodup : (sccIndexSets binds).flatten.Nodup :=
    (List.Perm.nodup_iff hperm).2 List.nodup_range
  have hdisj : List.Pairwise List.Disjoint (sccIndexSets binds) :=
    (List.nodup_flatten.mp hnodup).2
  exact (eq_of_mem_of_mem_of_pairwise_disjoint hdisj hg hg' hi' hi'').symm

/-- Partition components are pairwise `mutReach`-separated (needs Bool-trans / Nodup). -/
private theorem sccPartitionGo_separated (binds : List Surface.Binding)
    (hn : (binds.map (·.name)).Nodup) :
    let mutReach := fun i j =>
      mutuallyReachable (bindSucc binds) binds.length i j
    ∀ (fuel : Nat) (todo : List Nat) (accs : List (List Nat)),
      (∀ x ∈ todo, x < binds.length) →
      (∀ g ∈ accs, ∀ x ∈ g, x < binds.length) →
      (∀ g1 ∈ accs, ∀ g2 ∈ accs, g1 ≠ g2 →
        ∀ a ∈ g1, ∀ b ∈ g2, mutReach a b = false) →
      (∀ g ∈ accs, ∀ a ∈ g, ∀ b ∈ todo, mutReach a b = false) →
      (∀ g1 ∈ sccPartitionGo mutReach fuel todo accs,
        ∀ g2 ∈ sccPartitionGo mutReach fuel todo accs, g1 ≠ g2 →
          ∀ a ∈ g1, ∀ b ∈ g2, mutReach a b = false) := by
  intro mutReach fuel
  induction fuel with
  | zero =>
    intro todo accs _hbound _haccBound hacc_sep _hacc_todo g1 hg1 g2 hg2 hne a ha b hb
    simp only [sccPartitionGo] at hg1 hg2
    exact hacc_sep g1 hg1 g2 hg2 hne a ha b hb
  | succ fuel ih =>
    intro todo accs hbound haccbound hacc_sep hacc_todo g1 hg1 g2 hg2 hne a ha b hb
    cases todo with
    | nil =>
      simp only [sccPartitionGo] at hg1 hg2
      exact hacc_sep g1 hg1 g2 hg2 hne a ha b hb
    | cons seed rest =>
      simp only [sccPartitionGo] at hg1 hg2
      have hseed_lt : seed < binds.length := hbound seed (by simp)
      have hcomp_lt : ∀ x ∈ (seed :: rest).filter (mutReach seed), x < binds.length := by
        intro x hx
        exact hbound x (List.mem_of_mem_filter hx)
      have hrest'_lt : ∀ x ∈ (seed :: rest).filter (fun j => !mutReach seed j),
          x < binds.length := by
        intro x hx
        exact hbound x (List.mem_of_mem_filter hx)
      have hcomp_clique : ∀ x ∈ (seed :: rest).filter (mutReach seed),
          mutReach seed x = true := by
        intro x hx; exact (List.mem_filter.mp hx).2
      have hrest'_sep_seed : ∀ x ∈ (seed :: rest).filter (fun j => !mutReach seed j),
          mutReach seed x = false := by
        intro x hx
        cases hmr : mutReach seed x
        · rfl
        · have hnot : (!mutReach seed x) = true := (List.mem_filter.mp hx).2
          simp [hmr] at hnot
      have hmut_sym : ∀ x y, mutReach x y = mutReach y x := by
        intro x y
        simpa [mutReach] using mutuallyReachable_sym (bindSucc binds) binds.length x y
      have hcross_comp_rest :
          ∀ x ∈ (seed :: rest).filter (mutReach seed),
            ∀ y ∈ (seed :: rest).filter (fun j => !mutReach seed j),
              mutReach x y = false := by
        intro x hx y hy
        cases hxy : mutReach x y with
        | false => rfl
        | true =>
          have hsx := hcomp_clique x hx
          have hsy := hrest'_sep_seed y hy
          have hx_lt := hcomp_lt x hx
          have hy_lt := hrest'_lt y hy
          have hsy' : mutReach seed y = true :=
            mutuallyReachable_trans_of_nodup hn hseed_lt hx_lt hy_lt hsx hxy
          simp [hsy] at hsy'
      have hcross_acc_comp :
          ∀ g ∈ accs, ∀ x ∈ g, ∀ y ∈ (seed :: rest).filter (mutReach seed),
            mutReach x y = false := by
        intro g hg x hx y hy
        cases hxy : mutReach x y with
        | false => rfl
        | true =>
          have hsy := hcomp_clique y hy
          have hx_lt := haccbound g hg x hx
          have hy_lt := hcomp_lt y hy
          have hxs : mutReach x seed = false :=
            hacc_todo g hg x hx seed (by simp)
          have hys : mutReach y seed = true := by
            rw [hmut_sym]; exact hsy
          have hxs' : mutReach x seed = true :=
            mutuallyReachable_trans_of_nodup hn hx_lt hy_lt hseed_lt hxy hys
          simp [hxs] at hxs'
      have hacc'_sep :
          ∀ g1 ∈ accs ++ [(seed :: rest).filter (mutReach seed)],
            ∀ g2 ∈ accs ++ [(seed :: rest).filter (mutReach seed)], g1 ≠ g2 →
              ∀ a ∈ g1, ∀ b ∈ g2, mutReach a b = false := by
        intro g1' hg1' g2' hg2' hne' a' ha' b' hb'
        simp only [List.mem_append, List.mem_singleton] at hg1' hg2'
        cases hg1' with
        | inl h1 =>
          cases hg2' with
          | inl h2 => exact hacc_sep g1' h1 g2' h2 hne' a' ha' b' hb'
          | inr h2 =>
            subst h2; exact hcross_acc_comp g1' h1 a' ha' b' hb'
        | inr h1 =>
          subst h1
          cases hg2' with
          | inl h2 =>
            have h := hcross_acc_comp g2' h2 b' hb' a' ha'
            rwa [hmut_sym] at h
          | inr h2 =>
            subst h2; exact (hne' rfl).elim
      have hacc'_todo :
          ∀ g ∈ accs ++ [(seed :: rest).filter (mutReach seed)],
            ∀ a ∈ g, ∀ b ∈ (seed :: rest).filter (fun j => !mutReach seed j),
              mutReach a b = false := by
        intro g hg a ha b hb
        simp only [List.mem_append, List.mem_singleton] at hg
        cases hg with
        | inl h =>
          exact hacc_todo g h a ha b (List.mem_of_mem_filter hb)
        | inr h =>
          subst h; exact hcross_comp_rest a ha b hb
      exact ih ((seed :: rest).filter (fun j => !mutReach seed j))
        (accs ++ [(seed :: rest).filter (mutReach seed)]) hrest'_lt
        (by
          intro g hg x hx
          simp only [List.mem_append, List.mem_singleton] at hg
          cases hg with
          | inl h => exact haccbound g h x hx
          | inr h => subst h; exact hcomp_lt x hx)
        hacc'_sep hacc'_todo g1 hg1 g2 hg2 hne a ha b hb

private theorem sccIndexSets_separated (binds : List Surface.Binding)
    (hn : (binds.map (·.name)).Nodup)
    {g1 g2 : List Nat} (hg1 : g1 ∈ sccIndexSets binds) (hg2 : g2 ∈ sccIndexSets binds)
    (hne : g1 ≠ g2) {a b : Nat} (ha : a ∈ g1) (hb : b ∈ g2) :
    mutuallyReachable (bindSucc binds) binds.length a b = false := by
  have hg1' : g1 ∈
      sccPartitionGo
        (fun i j => mutuallyReachable (bindSucc binds) binds.length i j)
        (binds.length + 1) (List.range binds.length) [] := by
    rwa [← sccIndexSets_eq_partitionGo]
  have hg2' : g2 ∈
      sccPartitionGo
        (fun i j => mutuallyReachable (bindSucc binds) binds.length i j)
        (binds.length + 1) (List.range binds.length) [] := by
    rwa [← sccIndexSets_eq_partitionGo]
  exact sccPartitionGo_separated binds hn (binds.length + 1)
    (List.range binds.length) []
    (fun x hx => List.mem_range.mp hx)
    (fun g hg => by cases hg)
    (fun g1 hg => by cases hg)
    (fun g hg => by cases hg)
    g1 hg1' g2 hg2' hne a ha b hb

/-- A before-edge cycle among distinct SCC indices contradicts separation. -/
private theorem sccBeforeEdges_acyclic (binds : List Surface.Binding)
    (hn : (binds.map (·.name)).Nodup)
    {u v : Nat} (hne : u ≠ v)
    (huv : Relation.TransGen
      (fun a b => (a, b) ∈ sccBeforeEdges (bindSucc binds) (sccIndexSets binds)) u v)
    (hvu : Relation.TransGen
      (fun a b => (a, b) ∈ sccBeforeEdges (bindSucc binds) (sccIndexSets binds)) v u) :
    False := by
  set comps := sccIndexSets binds
  have ⟨hu_lt, hv_lt⟩ := sccBeforeReach_lt binds huv
  have hcu : comps[u]? = some comps[u] := List.getElem?_eq_getElem hu_lt
  have hcv : comps[v]? = some comps[v] := List.getElem?_eq_getElem hv_lt
  have hu_mem : comps[u] ∈ comps := List.getElem_mem hu_lt
  have hv_mem : comps[v] ∈ comps := List.getElem_mem hv_lt
  have hu_ne : comps[u] ≠ [] := sccIndexSets_nonempty_comp binds _ hu_mem
  have hv_ne : comps[v] ≠ [] := sccIndexSets_nonempty_comp binds _ hv_mem
  have hx := List.head_mem hu_ne
  have hy := List.head_mem hv_ne
  set x := comps[u].head hu_ne
  set y := comps[v].head hv_ne
  have hx_lt := sccIndexSets_mem_lt binds _ hu_mem x hx
  have hy_lt := sccIndexSets_mem_lt binds _ hv_mem y hy
  have hne_g : comps[u] ≠ comps[v] := by
    intro heq
    have hnodup : comps.flatten.Nodup :=
      (List.Perm.nodup_iff (sccIndexSets_flatten_perm binds)).2 List.nodup_range
    have hdisj : List.Pairwise List.Disjoint comps :=
      (List.nodup_flatten.mp hnodup).2
    have hlt : (⟨u, hu_lt⟩ : Fin comps.length) < ⟨v, hv_lt⟩ ∨
        (⟨v, hv_lt⟩ : Fin comps.length) < ⟨u, hu_lt⟩ := by
      rcases Nat.lt_or_gt_of_ne hne with h | h
      · exact Or.inl h
      · exact Or.inr h
    cases hlt with
    | inl h =>
      have hd := List.Pairwise.rel_get_of_lt hdisj h
      exact hd hx (by simpa [heq] using hx)
    | inr h =>
      have hd := List.Pairwise.rel_get_of_lt hdisj h
      exact hd (by simpa [heq] using hx) hx
  have dxy : DepReach binds (binds[y]).name (binds[x]).name :=
    DepReach_of_sccBeforeReach binds huv hcv hcu hy hx hy_lt hx_lt
  have dyx : DepReach binds (binds[x]).name (binds[y]).name :=
    DepReach_of_sccBeforeReach binds hvu hcu hcv hx hy hx_lt hy_lt
  have hmut : mutuallyReachable (bindSucc binds) binds.length x y = true :=
    Bool.and_eq_true_iff.mpr ⟨canReach_complete hn hx_lt hy_lt dyx,
      canReach_complete hn hy_lt hx_lt dxy⟩
  have hsep : mutuallyReachable (bindSucc binds) binds.length x y = false :=
    sccIndexSets_separated binds hn hu_mem hv_mem hne_g hx hy
  simp [hmut] at hsep

/-- Critical Kahn gap: condensation of `sccIndexSets` is a DAG, so Kahn returns a
    full permutation of `0 .. comps.length - 1`.
    Needs name-Nodup so Bool mutual-reachability is transitive (condensation acyclic). -/
private theorem kahnTopo_scc_perm (binds : List Surface.Binding)
    (hn : (binds.map (·.name)).Nodup) :
    let comps := sccIndexSets binds
    let edges := sccBeforeEdges (bindSucc binds) comps
    (kahnTopo comps.length edges).Perm (List.range comps.length) := by
  set comps := sccIndexSets binds
  set edges := sccBeforeEdges (bindSucc binds) comps
  have hb := sccBeforeEdges_bounded (bindSucc binds) comps
  have hnodup_e := sccBeforeEdges_nodup (bindSucc binds) comps
  simp only [kahnTopo]
  set indeg0 := (List.range comps.length).map fun w =>
    (edges.filter (fun e => e.2 = w)).length
  set ready0 := (List.range comps.length).filter fun w => indegGet indeg0 w = 0
  set out := kahnGo edges (comps.length + 1) indeg0 ready0 []
  have hres := kahnGo_zero_closed edges comps.length hb hnodup_e
    (comps.length + 1) indeg0 ready0 []
    (by simp [indeg0, List.length_map, List.length_range])
    (fun w hw => by simpa [indeg0] using kahnTopo_indeg0_eq comps.length edges hw)
    (fun b hb' => by
      have hbmem := List.mem_filter.mp hb'
      refine ⟨List.mem_range.mp hbmem.1, ?_, by simp⟩
      have heq : indegGet indeg0 b = 0 := of_decide_eq_true hbmem.2
      rwa [show indeg0 = (List.range comps.length).map fun w =>
        (edges.filter (fun e => e.2 = w)).length from rfl,
        kahnTopo_indeg0_eq comps.length edges (List.mem_range.mp hbmem.1)] at heq)
    (List.Nodup.filter _ List.nodup_range)
    (fun y hy => by cases hy)
    (by simp)
    (fun v hv hz => by
      right
      refine List.mem_filter.mpr ⟨List.mem_range.mpr hv, ?_⟩
      have : indegGet indeg0 v = 0 := by
        rwa [show indeg0 = (List.range comps.length).map fun w =>
          (edges.filter (fun e => e.2 = w)).length from rfl,
          kahnTopo_indeg0_eq comps.length edges hv]
      exact decide_eq_true this)
    (by omega)
  change out.Perm (List.range comps.length)
  obtain ⟨hnodup_out, hlt_out, hlen_or⟩ := hres
  refine perm_range_of_nodup_length hnodup_out hlt_out ?_
  cases hlen_or with
  | inl hlen => exact hlen
  | inr hstuck =>
    obtain ⟨v0, hv0, hv0n, hpred⟩ := hstuck
    have hlen_lt : out.length < comps.length := by
      have hle := length_le_of_nodup_lt hnodup_out hlt_out
      by_contra hnge
      have heq : out.length = comps.length := Nat.le_antisymm hle (by omega)
      have hperm := perm_range_of_nodup_length hnodup_out hlt_out heq
      exact hv0n ((List.Perm.mem_iff hperm).2 (List.mem_range.mpr hv0))
    obtain ⟨u, v, hne, huv, hvu⟩ :=
      exists_edge_cycle_of_pred_closed edges hnodup_out hlen_lt
        (sccBeforeEdges_no_loop (bindSucc binds) comps) hpred
    exact (sccBeforeEdges_acyclic binds hn hne huv hvu).elim

private theorem sccOrderedIndexSets_flatten_perm (binds : List Surface.Binding)
    (hn : (binds.map (·.name)).Nodup) :
    (sccOrderedIndexSets binds).flatten.Perm (List.range binds.length) := by
  simp only [sccOrderedIndexSets]
  set comps := sccIndexSets binds
  set edges := sccBeforeEdges (bindSucc binds) comps
  set order := kahnTopo comps.length edges
  have hord := kahnTopo_scc_perm binds hn
  have hcomps : (order.filterMap (fun k => comps[k]?)).Perm comps :=
    filterMap_getElem?_of_perm hord
  have hflat := hcomps.flatten
  exact hflat.trans (sccIndexSets_flatten_perm binds)

/-- If `mutReach i j` and `i` lies in an `sccIndexSets` component, so does `j`. -/
private theorem sccIndexSets_mem_of_mutReach (binds : List Surface.Binding)
    (hn : (binds.map (·.name)).Nodup)
    {g : List Nat} (hg : g ∈ sccIndexSets binds)
    {i j : Nat} (hi : i ∈ g)
    (hmut : mutuallyReachable (bindSucc binds) binds.length i j = true)
    (hj : j < binds.length) :
    j ∈ g := by
  obtain ⟨g', hg', hj', _⟩ := sccIndexSets_unique_comp binds hj
  suffices g' = g by rwa [← this]
  by_contra hne
  have hsep : mutuallyReachable (bindSucc binds) binds.length i j = false :=
    sccIndexSets_separated binds hn hg hg' (Ne.symm hne) hi hj'
  simp [hmut] at hsep

theorem sccOrderedIndexSets_flatPerm (binds : List Surface.Binding)
    (hn : (binds.map (·.name)).Nodup) :
    (indexSetsToBindings binds (sccOrderedIndexSets binds)).flatten.Perm binds :=
  indexSetsToBindings_flatten_of_perm (sccOrderedIndexSets_flatten_perm binds hn)

theorem sccOrderedIndexSets_nonempty (binds : List Surface.Binding) :
    ∀ g ∈ indexSetsToBindings binds (sccOrderedIndexSets binds), g ≠ [] := by
  intro g hg
  simp only [indexSetsToBindings, List.mem_map] at hg
  obtain ⟨idxs, hidxs, rfl⟩ := hg
  have hcomp := sccOrderedIndexSets_mem_of_getElem binds hidxs
  have hne := sccIndexSets_nonempty_comp binds idxs hcomp
  refine filterMap_ne_nil_of_isSome (fun i => binds[i]?) hne ?_
  intro i hi
  have hlt := sccIndexSets_mem_lt binds idxs hcomp i hi
  simp [List.getElem?_eq_getElem hlt]

theorem sccOrderedIndexSets_sameScc (binds : List Surface.Binding) :
    ∀ g ∈ indexSetsToBindings binds (sccOrderedIndexSets binds),
      ∀ b1 ∈ g, ∀ b2 ∈ g, DepMutual binds b1.name b2.name := by
  intro g hg b1 hb1 b2 hb2
  simp only [indexSetsToBindings, List.mem_map] at hg
  obtain ⟨idxs, hidxs, rfl⟩ := hg
  have hcomp := sccOrderedIndexSets_mem_of_getElem binds hidxs
  have hb1' := List.mem_filterMap.mp hb1
  have hb2' := List.mem_filterMap.mp hb2
  obtain ⟨i, hi, hbi⟩ := hb1'
  obtain ⟨j, hj, hbj⟩ := hb2'
  have hi_lt := sccIndexSets_mem_lt binds idxs hcomp i hi
  have hj_lt := sccIndexSets_mem_lt binds idxs hcomp j hj
  have hbi' : binds[i] = b1 := by
    rw [List.getElem?_eq_getElem hi_lt] at hbi; exact Option.some.inj hbi
  have hbj' : binds[j] = b2 := by
    rw [List.getElem?_eq_getElem hj_lt] at hbj; exact Option.some.inj hbj
  have hmut := sccIndexSets_comp_depMutual binds hcomp hi hj
  simpa [hbi', hbj'] using hmut

theorem sccOrderedIndexSets_maxScc (binds : List Surface.Binding)
    (hn : (binds.map (·.name)).Nodup) :
    ∀ b1 ∈ binds, ∀ b2 ∈ binds,
      DepMutual binds b1.name b2.name →
        ∃ g ∈ indexSetsToBindings binds (sccOrderedIndexSets binds),
          b1 ∈ g ∧ b2 ∈ g := by
  intro b1 hb1 b2 hb2 ⟨hab, hba⟩
  obtain ⟨i, hi, hib⟩ := List.mem_iff_getElem.mp hb1
  obtain ⟨j, hj, hjb⟩ := List.mem_iff_getElem.mp hb2
  subst hib; subst hjb
  have hmut : mutuallyReachable (bindSucc binds) binds.length i j = true :=
    Bool.and_eq_true_iff.mpr ⟨canReach_complete hn hi hj hab,
      canReach_complete hn hj hi hba⟩
  obtain ⟨gIdxs, hgIdxs, hi_mem, _huniq⟩ := sccIndexSets_unique_comp binds hi
  have hj_mem : j ∈ gIdxs :=
    sccIndexSets_mem_of_mutReach binds hn hgIdxs hi_mem hmut hj
  -- Kahn perm ⇒ gIdxs appears in ordered index sets
  have hord := kahnTopo_scc_perm binds hn
  obtain ⟨k, hklt, rfl⟩ := List.mem_iff_getElem.mp hgIdxs
  have hk_ord : k ∈
      kahnTopo (sccIndexSets binds).length
        (sccBeforeEdges (bindSucc binds) (sccIndexSets binds)) :=
    (List.Perm.mem_iff hord).2 (List.mem_range.mpr hklt)
  have hidxs : (sccIndexSets binds)[k] ∈ sccOrderedIndexSets binds := by
    simp only [sccOrderedIndexSets, List.mem_filterMap]
    exact ⟨k, hk_ord, List.getElem?_eq_getElem hklt⟩
  refine ⟨(sccIndexSets binds)[k].filterMap (fun t => binds[t]?), ?_, ?_, ?_⟩
  · simp only [indexSetsToBindings, List.mem_map]
    exact ⟨(sccIndexSets binds)[k], hidxs, rfl⟩
  · exact List.mem_filterMap.mpr ⟨i, hi_mem, by simp [List.getElem?_eq_getElem hi]⟩
  · exact List.mem_filterMap.mpr ⟨j, hj_mem, by simp [List.getElem?_eq_getElem hj]⟩

private theorem kahnGo_nodup (beforeEdges : List (Nat × Nat))
    (hedges_nodup : beforeEdges.Nodup) :
    ∀ (fuel : Nat) (indeg ready acc : List Nat),
      ready.Nodup → acc.Nodup → (∀ x ∈ ready, x ∉ acc) →
      (kahnGo beforeEdges fuel indeg ready acc).Nodup := by
  intro fuel
  induction fuel with
  | zero =>
    intro indeg ready acc _hr ha _hdisj
    simpa [kahnGo] using ha
  | succ fuel ih =>
    intro indeg ready acc hr ha hdisj
    cases ready with
    | nil => simpa [kahnGo] using ha
    | cons u us =>
      simp only [kahnGo]
      set acc' := acc ++ [u]
      set nbrs := beforeEdges.filterMap fun ⟨a, b⟩ => if a = u then some b else none
      set indeg' := nbrs.foldl (fun ig b => indegSet ig b (indegGet ig b - 1)) indeg
      set newReady := nbrs.filter fun b =>
        indegGet indeg' b = 0 && b ∉ acc' && b ∉ us
      have hu_us : u ∉ us := (List.nodup_cons.mp hr).1
      have hu_acc : u ∉ acc := hdisj u List.mem_cons_self
      have hacc' : acc'.Nodup := by
        refine List.Nodup.append ha (List.nodup_singleton u) ?_
        intro x hx hx'
        simp only [List.mem_singleton] at hx'
        exact hu_acc (hx' ▸ hx)
      have hready' : (us ++ newReady).Nodup := by
        have hus := (List.nodup_cons.mp hr).2
        have hnbrs := filterMap_succ_nodup beforeEdges hedges_nodup u
        have hnew : newReady.Nodup := List.Nodup.filter _ hnbrs
        refine List.Nodup.append hus hnew ?_
        intro x hx hx'
        have hcond := (List.mem_filter.mp hx').2
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hcond
        exact hcond.2 hx
      have hdisj' : ∀ x ∈ us ++ newReady, x ∉ acc' := by
        intro x hx
        simp only [List.mem_append] at hx
        cases hx with
        | inl h =>
          intro hin
          simp only [acc', List.mem_append, List.mem_singleton] at hin
          cases hin with
          | inl hacc => exact hdisj x (List.mem_cons_of_mem _ h) hacc
          | inr hu => exact hu_us (hu ▸ h)
        | inr h =>
          have hcond := (List.mem_filter.mp h).2
          simp only [Bool.and_eq_true, decide_eq_true_eq] at hcond
          exact hcond.1.2
      exact ih indeg' (us ++ newReady) acc' hready' hacc' hdisj'

private theorem kahnTopo_nodup (n : Nat) (edges : List (Nat × Nat))
    (hnodup : edges.Nodup) :
    (kahnTopo n edges).Nodup := by
  simp only [kahnTopo]
  refine kahnGo_nodup edges hnodup (n + 1) _ _ []
    (List.Nodup.filter _ List.nodup_range) (by simp) (by simp)

/-- If Kahn only queues in-bounds nodes and edges are bounded, outputs stay `< n`. -/
private theorem kahnGo_lt (beforeEdges : List (Nat × Nat)) (n : Nat)
    (hn : edgesBounded n beforeEdges) :
    ∀ (fuel : Nat) (indeg ready acc : List Nat),
      (∀ b ∈ ready, b < n) →
      (∀ y ∈ acc, y < n) →
      ∀ x ∈ kahnGo beforeEdges fuel indeg ready acc, x < n := by
  intro fuel
  induction fuel with
  | zero =>
    intro indeg ready acc _hready hacc x hx
    simp only [kahnGo] at hx; exact hacc x hx
  | succ fuel ih =>
    intro indeg ready acc hready hacc x hx
    cases ready with
    | nil =>
      simp only [kahnGo] at hx; exact hacc x hx
    | cons u us =>
      simp only [kahnGo] at hx
      set acc' := acc ++ [u]
      set nbrs := beforeEdges.filterMap fun ⟨a, b⟩ => if a = u then some b else none
      set indeg' := nbrs.foldl (fun ig b => indegSet ig b (indegGet ig b - 1)) indeg
      set newReady := nbrs.filter fun b =>
        indegGet indeg' b = 0 && b ∉ acc' && b ∉ us
      refine ih indeg' (us ++ newReady) acc' ?_ ?_ x hx
      · intro b hb
        simp only [List.mem_append] at hb
        cases hb with
        | inl h => exact hready b (List.mem_cons_of_mem _ h)
        | inr h =>
          have ⟨hbmem, _⟩ := List.mem_filter.mp h
          simp only [nbrs, List.mem_filterMap] at hbmem
          obtain ⟨e, hee, hopt⟩ := hbmem
          rcases e with ⟨a, b'⟩
          by_cases ha : a = u
          · simp only [ha, ↓reduceIte, Option.some.injEq] at hopt
            subst hopt; exact (hn _ hee).2
          · simp [ha] at hopt
      · intro y hy
        simp only [acc', List.mem_append, List.mem_singleton] at hy
        cases hy with
        | inl h => exact hacc y h
        | inr h => exact h ▸ hready u List.mem_cons_self

private theorem kahnTopo_lt (n : Nat) (edges : List (Nat × Nat))
    (hb : edgesBounded n edges) :
    ∀ x ∈ kahnTopo n edges, x < n := by
  simp only [kahnTopo]
  refine kahnGo_lt edges n hb (n + 1) _ _ [] ?_ (by intro y hy; cases hy)
  intro b hb'
  exact List.mem_range.mp (List.mem_of_mem_filter hb')

/-- `filterMap` of always-`some` is `map` of the forced values. -/
private theorem filterMap_getElem?_eq_map {α β} (f : α → Option β) (l : List α)
    (h : ∀ x ∈ l, (f x).isSome) (i : Nat) :
    (l.filterMap f)[i]? = l[i]? >>= f := by
  induction l generalizing i with
  | nil => simp
  | cons a as ih =>
    have ha := h a (by simp)
    cases hf : f a with
    | none => simp [hf] at ha
    | some b =>
      simp only [List.filterMap_cons, hf]
      cases i with
      | zero => simp [hf]
      | succ i =>
        simp only [List.getElem?_cons_succ]
        exact ih (fun x hx => h x (List.mem_cons_of_mem _ hx)) i

private theorem mem_sccBeforeEdges_of_compDependsOn (succ : Nat → List Nat)
    (comps : List (List Nat)) {a b : Nat}
    (ha : a < comps.length) (hb : b < comps.length) (hne : a ≠ b)
    (hdep : compDependsOn succ (comps[a]) (comps[b]) = true) :
    (b, a) ∈ sccBeforeEdges succ comps := by
  simp only [sccBeforeEdges, List.mem_flatMap]
  refine ⟨a, List.mem_range.mpr ha, ?_⟩
  simp only [List.mem_filterMap]
  refine ⟨b, List.mem_range.mpr hb, ?_⟩
  simp [hne, List.getElem?_eq_getElem ha, List.getElem?_eq_getElem hb, hdep]

private theorem compDependsOn_of_succ_mem (succ : Nat → List Nat)
    {ca cb : List Nat} {p q : Nat}
    (hp : p ∈ ca) (hq : q ∈ cb) (hs : q ∈ succ p) :
    compDependsOn succ ca cb = true := by
  simp only [compDependsOn, List.any_eq_true]
  refine ⟨p, hp, ?_⟩
  exact ⟨q, hs, by simpa using hq⟩

theorem sccOrderedIndexSets_topo (binds : List Surface.Binding) :
    let groups := indexSetsToBindings binds (sccOrderedIndexSets binds)
    ∀ (i j : Nat) (gi gj : List Surface.Binding),
      groups[i]? = some gi → groups[j]? = some gj → i ≠ j →
      ∀ b1 ∈ gi, ∀ b2 ∈ gj,
        Binding.refersTo b1 b2.name = true → j < i := by
  intro groups i j gi gj hgi hgj _hne b1 hb1 b2 hb2 href
  set comps := sccIndexSets binds
  set edges := sccBeforeEdges (bindSucc binds) comps
  set order := kahnTopo comps.length edges
  have hb := sccBeforeEdges_bounded (bindSucc binds) comps
  have hnodup := sccBeforeEdges_nodup (bindSucc binds) comps
  simp only [groups, indexSetsToBindings, sccOrderedIndexSets] at hgi hgj
  -- groups[i]? = (ordered.map ... )[i]? where ordered = order.filterMap comps[·]?
  rw [List.getElem?_map] at hgi hgj
  have hord_lt : ∀ x ∈ order, x < comps.length := kahnTopo_lt _ _ hb
  have hgi_fm :
      ((order.filterMap fun k => comps[k]?)[i]?).map
        (fun idxs => idxs.filterMap fun t => binds[t]?) = some gi := hgi
  have hgj_fm :
      ((order.filterMap fun k => comps[k]?)[j]?).map
        (fun idxs => idxs.filterMap fun t => binds[t]?) = some gj := hgj
  -- Extract the index-sets at positions i, j
  cases hi_ord : (order.filterMap fun k => comps[k]?)[i]? with
  | none => simp [hi_ord] at hgi_fm
  | some idxsi =>
    cases hj_ord : (order.filterMap fun k => comps[k]?)[j]? with
    | none => simp [hj_ord] at hgj_fm
    | some idxsj =>
      simp only [hi_ord, hj_ord, Option.map_some, Option.some.injEq] at hgi_fm hgj_fm
      -- Relate filterMap getElem? to order[i]?
      have hfm_i := filterMap_getElem?_eq_map (fun k => comps[k]?) order
        (fun x hx => by
          have := hord_lt x hx
          simp [List.getElem?_eq_getElem this]) i
      have hfm_j := filterMap_getElem?_eq_map (fun k => comps[k]?) order
        (fun x hx => by
          have := hord_lt x hx
          simp [List.getElem?_eq_getElem this]) j
      rw [hfm_i] at hi_ord
      rw [hfm_j] at hj_ord
      cases hi_o : order[i]? with
      | none => simp [hi_o] at hi_ord
      | some ki =>
        cases hj_o : order[j]? with
        | none => simp [hj_o] at hj_ord
        | some kj =>
          simp only [hi_o, hj_o, Option.bind_eq_bind] at hi_ord hj_ord
          have hki_lt : ki < comps.length := hord_lt ki (List.mem_of_getElem? hi_o)
          have hkj_lt : kj < comps.length := hord_lt kj (List.mem_of_getElem? hj_o)
          have hidxsi : idxsi = comps[ki] := by
            simpa [List.getElem?_eq_getElem hki_lt] using hi_ord.symm
          have hidxsj : idxsj = comps[kj] := by
            simpa [List.getElem?_eq_getElem hkj_lt] using hj_ord.symm
          have hb1' := List.mem_filterMap.mp (by simpa [← hgi_fm] using hb1)
          have hb2' := List.mem_filterMap.mp (by simpa [← hgj_fm] using hb2)
          obtain ⟨p, hp, hbp⟩ := hb1'
          obtain ⟨q, hq, hbq⟩ := hb2'
          have hp' : p ∈ comps[ki] := by simpa [hidxsi] using hp
          have hq' : q ∈ comps[kj] := by simpa [hidxsj] using hq
          have hsucc : q ∈ bindSucc binds p :=
            (bindSucc_mem (binds := binds) (i := p) (j := q)).mpr
              ⟨b1, b2, hbp, hbq, href⟩
          have hne_kj : ki ≠ kj := by
            intro heq
            subst heq
            have hnodup_ord := kahnTopo_nodup comps.length edges hnodup
            have hi_lt : i < order.length := (List.getElem?_eq_some_iff.mp hi_o).1
            have hj_lt : j < order.length := (List.getElem?_eq_some_iff.mp hj_o).1
            have hei : order[i] = ki := (List.getElem?_eq_some_iff.mp hi_o).2
            have hej : order[j] = ki := (List.getElem?_eq_some_iff.mp hj_o).2
            exact _hne ((List.Nodup.getElem_inj_iff hnodup_ord).1 (hei.trans hej.symm))
          have hdep := compDependsOn_of_succ_mem (bindSucc binds) hp' hq' hsucc
          have hedge := mem_sccBeforeEdges_of_compDependsOn (bindSucc binds) comps
            hki_lt hkj_lt hne_kj hdep
          exact kahnTopo_edge_before comps.length edges hb hnodup hedge hj_o hi_o

/-- Soundness: executable groups satisfy the declarative SCC spec. -/
theorem sccGroups_sound {binds : List Surface.Binding}
    {groups : List (List Surface.Binding)} :
    sccGroups binds = some groups → ValidBindingGroups binds groups := by
  intro h
  obtain ⟨hn, rfl⟩ := (sccGroups_eq_some_iff).1 h
  exact ⟨hn,
    sccOrderedIndexSets_flatPerm binds hn,
    sccOrderedIndexSets_nonempty binds,
    sccOrderedIndexSets_sameScc binds,
    sccOrderedIndexSets_maxScc binds hn,
    sccOrderedIndexSets_topo binds⟩

/-- Completeness: some valid grouping exists ⇒ executable succeeds
    (not that it returns this exact `groups` — topo/intra-group order is free). -/
theorem sccGroups_complete {binds : List Surface.Binding}
    {groups : List (List Surface.Binding)} :
    ValidBindingGroups binds groups → (sccGroups binds).isSome := by
  intro h
  have hn := h.namesNodup
  simp [sccGroups, guard, hn]

/-- Build a `Program` from a flat binding list: SCC-infer groups, keep
    `desugarGroups` as the sole consumer of `List (List Binding)`.
    Fails (`none`) iff binding names are not unique. -/
def Program.ofFlat (decls : List Surface.DataDecl)
    (binds : List Surface.Binding) (body : Surface.Expr) :
    Option Surface.Program :=
  (sccGroups binds).map fun groups => ⟨decls, groups, body⟩

theorem Program.ofFlat_groups_valid {decls : List Surface.DataDecl}
    {binds : List Surface.Binding} {body : Surface.Expr}
    {p : Surface.Program}
    (h : Program.ofFlat decls binds body = some p) :
    ValidBindingGroups binds p.groups := by
  simp only [Program.ofFlat, Option.map_eq_some_iff] at h
  obtain ⟨groups, hscc, rfl⟩ := h
  exact sccGroups_sound hscc

theorem Program.ofFlat_decls_body {decls : List Surface.DataDecl}
    {binds : List Surface.Binding} {body : Surface.Expr}
    {p : Surface.Program}
    (h : Program.ofFlat decls binds body = some p) :
    p.decls = decls ∧ p.body = body := by
  simp only [Program.ofFlat, Option.map_eq_some_iff] at h
  obtain ⟨groups, _, rfl⟩ := h
  exact ⟨rfl, rfl⟩

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
      -- @TODO(pattern-λ): desugar `λ(p). body` → `λx. match x with p => body`
      -- for nontrivial `p` (ctor/pair/cons/list). Currently rejected.
      | _ => none
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
        -- Same body function as `match_` / `bodyFn [t', f']` (defined later).
        some (lowerMatch c' [.ctor cTrue [], .ctor cFalse []]
          (fun i => [t', f'].getD i (.ctor cNil)))
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


/-! ## 5b. Executable exhaustiveness (`dTreeExhaustiveB` / `checkExhaustive`)

Bool mirrors of `DTreeExhaustive` / `MatchExhaustive` / `SurfaceCovers`.
Soundness (`= true → Prop`) is the confidence gate — not `#guard` smoke.
Concrete instances preferred as `example … := by native_decide` (kernel-checked). -/

/-- Every case tests a real ctor of `T` at the declared arity. -/
def dTreeCasesOk (ctors : CtorEnv) (T : TyName) :
    List (CtorName × Nat × DTree) → Bool
  | [] => true
  | (c, a, _) :: rest =>
    match LookupList.get? ctors c with
    | some ctor =>
        (ctor.tyName == T) && (a == ctor.contents.length) &&
          dTreeCasesOk ctors T rest
    | none => false

/-- Every env ctor of type `T` appears as a case (complete signature).
    Iterates ctor *names*; `get?` selects the visible binding (same as the Prop). -/
def dTreeAllCtorsCovered (ctors : CtorEnv) (T : TyName)
    (cases : List (CtorName × Nat × DTree)) : Bool :=
  (ctors.map (·.1)).all fun c =>
    match LookupList.get? ctors c with
    | some ctor =>
        ctor.tyName != T || cases.any fun ⟨c', _, _⟩ => c' == c
    | none => true

mutual

/-- Recurse into switch cases under extended occurrence typing. -/
def dTreeCasesRec (ctors : CtorEnv) (octx : OccCtx) (occ : Occ) (tyArgs : List Ty) :
    List (CtorName × Nat × DTree) → Bool
  | [] => true
  | (c, _, t) :: rest =>
    dTreeExhaustiveB ctors (OccCtx.extend octx occ (instFieldTys ctors c tyArgs)) t &&
      dTreeCasesRec ctors octx occ tyArgs rest

/-- **Executable tree exhaustiveness.** Structural Bool twin of `DTreeExhaustive`. -/
def dTreeExhaustiveB (ctors : CtorEnv) (octx : OccCtx) : DTree → Bool
  | .fail => false
  | .leaf _ _ => true
  | .switch occ cases dflt =>
    match LookupList.get? octx occ with
    | some (.customTy T tyArgs) =>
      let casesOk := dTreeCasesOk ctors T cases
      let recOk := dTreeCasesRec ctors octx occ tyArgs cases
      match dflt with
      | .fail =>
        casesOk && recOk && dTreeAllCtorsCovered ctors T cases
      | _ =>
        casesOk && recOk && dTreeExhaustiveB ctors octx dflt
    | _ => false

end

/-- **Executable match-pattern exhaustiveness** at scrutinee type `customTy T tyArgs`. -/
def matchExhaustiveB (ctors : CtorEnv) (T : TyName) (tyArgs : List Ty)
    (ps : List Surface.Pattern) : Bool :=
  dTreeExhaustiveB ctors [([], .customTy T tyArgs)] (compile [[]] (initMatrix ps))

/-- Guess `tyArgs` length from any ctor of `T` (placeholders; fail-closed for nested ADTs
    when placeholders don't instantiate field ADTs — soundness still holds). -/
private def tyArgsGuess (ctors : CtorEnv) (T : TyName) : List Ty :=
  match ctors.find? fun ⟨_, ctor⟩ => ctor.tyName == T with
  | some ⟨_, ctor⟩ => List.replicate ctor.paramCount (.prim .unit)
  | none => []

/-- Top-level ctor name in a pattern, if any. -/
private def patternTopCtor : Surface.Pattern → Option CtorName
  | .ctor n _ => some n
  | .pair _ _ | .cons _ _ | .list _ | .name _ | .wildcard => none

/-- Recover a candidate ADT name from top-level ctor patterns (all must agree). -/
private def tyNameFromPatterns (ctors : CtorEnv) :
    List Surface.Pattern → Option TyName
  | [] => none
  | p :: ps =>
    match patternTopCtor p >>= LookupList.get? ctors with
    | none => tyNameFromPatterns ctors ps
    | some ctor =>
      let T := ctor.tyName
      if ps.all fun q =>
        match patternTopCtor q >>= LookupList.get? ctors with
        | none => true
        | some ctor' => ctor'.tyName == T
      then some T else none

mutual

/-- Structural size for `checkExhaustive` termination (mirrors `Core.Expr.size`). -/
def surfaceExprSize : Surface.Expr → Nat
  | .primLit _ | .var _ | .ctor _ => 1
  | .pair a b => 1 + surfaceExprSize a + surfaceExprSize b
  | .cons h t => 1 + surfaceExprSize h + surfaceExprSize t
  | .list items => 1 + surfaceExprSizeList items
  | .lambda _ _ body => 1 + surfaceExprSize body
  | .app f x => 1 + surfaceExprSize f + surfaceExprSize x
  | .letIn _ _ rhs body => 1 + surfaceExprSize rhs + surfaceExprSize body
  | .letRecIn binds body => 1 + surfaceExprSizeLetRecBinds binds + surfaceExprSize body
  | .ife c t f => 1 + surfaceExprSize c + surfaceExprSize t + surfaceExprSize f
  | .match_ scrut brs => 1 + surfaceExprSize scrut + surfaceExprSizeBranches brs

def surfaceExprSizeList : List Surface.Expr → Nat
  | [] => 0
  | e :: es => 1 + surfaceExprSize e + surfaceExprSizeList es

def surfaceExprSizeLetRecBinds : List (ValName × Option Surface.PolyTy × Surface.Expr) → Nat
  | [] => 0
  | (_, _, rhs) :: rest => 1 + surfaceExprSize rhs + surfaceExprSizeLetRecBinds rest

def surfaceExprSizeBranches : List (Surface.Pattern × Surface.Expr) → Nat
  | [] => 0
  | (_, b) :: rest => 1 + surfaceExprSize b + surfaceExprSizeBranches rest

/-- List-element coverage helper (mutual with `checkExhaustive`). -/
def checkExhaustiveList (ctors : CtorEnv) : List Surface.Expr → Bool
  | [] => true
  | e :: es => checkExhaustive ctors e && checkExhaustiveList ctors es
termination_by es => surfaceExprSizeList es
decreasing_by
  all_goals (simp only [surfaceExprSizeList]; omega)

/-- `letRecIn` binding-RHS coverage helper (mutual with `checkExhaustive`). -/
def checkExhaustiveLetRecBinds (ctors : CtorEnv) :
    List (ValName × Option Surface.PolyTy × Surface.Expr) → Bool
  | [] => true
  | (_, _, rhs) :: rest =>
      checkExhaustive ctors rhs && checkExhaustiveLetRecBinds ctors rest
termination_by binds => surfaceExprSizeLetRecBinds binds
decreasing_by
  all_goals (simp only [surfaceExprSizeLetRecBinds]; omega)

/-- Branch-body coverage helper (mutual with `checkExhaustive`). -/
def checkExhaustiveBranches (ctors : CtorEnv) :
    List (Surface.Pattern × Surface.Expr) → Bool
  | [] => true
  | (_, b) :: rest =>
      checkExhaustive ctors b && checkExhaustiveBranches ctors rest
termination_by brs => surfaceExprSizeBranches brs
decreasing_by
  all_goals (simp only [surfaceExprSizeBranches]; omega)

/-- **Executable `SurfaceCovers`.** At `match_`, recovers `T` from branch ctor
    patterns when possible and seeds `tyArgs` via `tyArgsGuess` (fail-closed).
    Drivers that already know scrutinee types may call `matchExhaustiveB` directly. -/
def checkExhaustive (ctors : CtorEnv) : Surface.Expr → Bool
  | .primLit _ | .var _ | .ctor _ => true
  | .pair a b => checkExhaustive ctors a && checkExhaustive ctors b
  | .cons h t => checkExhaustive ctors h && checkExhaustive ctors t
  | .list items => checkExhaustiveList ctors items
  | .lambda _ _ body => checkExhaustive ctors body
  | .app f x => checkExhaustive ctors f && checkExhaustive ctors x
  | .letIn _ _ rhs body =>
      checkExhaustive ctors rhs && checkExhaustive ctors body
  | .letRecIn binds body =>
      checkExhaustiveLetRecBinds ctors binds && checkExhaustive ctors body
  | .ife c t f =>
      checkExhaustive ctors c && checkExhaustive ctors t && checkExhaustive ctors f &&
        matchExhaustiveB ctors nBool []
          [.ctor cTrue [], .ctor cFalse []]
  | .match_ scrut brs =>
      checkExhaustive ctors scrut &&
        checkExhaustiveBranches ctors brs &&
        match tyNameFromPatterns ctors (brs.map Prod.fst) with
        | some T =>
          matchExhaustiveB ctors T (tyArgsGuess ctors T) (brs.map Prod.fst)
        | none =>
          matchExhaustiveB ctors nBool [] (brs.map Prod.fst)
termination_by s => surfaceExprSize s
decreasing_by
  all_goals (simp only [surfaceExprSize]; omega)

end

private theorem surfaceExprSize_lt_pair_left (a b : Surface.Expr) :
    surfaceExprSize a < surfaceExprSize (.pair a b) := by simp only [surfaceExprSize]; omega

private theorem surfaceExprSize_lt_pair_right (a b : Surface.Expr) :
    surfaceExprSize b < surfaceExprSize (.pair a b) := by simp only [surfaceExprSize]; omega

private theorem surfaceExprSize_lt_cons_head (h t : Surface.Expr) :
    surfaceExprSize h < surfaceExprSize (.cons h t) := by simp only [surfaceExprSize]; omega

private theorem surfaceExprSize_lt_cons_tail (h t : Surface.Expr) :
    surfaceExprSize t < surfaceExprSize (.cons h t) := by simp only [surfaceExprSize]; omega

private theorem surfaceExprSize_lt_lambda_body (param : Surface.Pattern) (ann : Option Surface.Ty)
    (body : Surface.Expr) :
    surfaceExprSize body < surfaceExprSize (.lambda param ann body) := by
  simp only [surfaceExprSize]; omega

private theorem surfaceExprSize_lt_app_fn (f x : Surface.Expr) :
    surfaceExprSize f < surfaceExprSize (.app f x) := by simp only [surfaceExprSize]; omega

private theorem surfaceExprSize_lt_app_arg (f x : Surface.Expr) :
    surfaceExprSize x < surfaceExprSize (.app f x) := by simp only [surfaceExprSize]; omega

private theorem surfaceExprSize_lt_letIn_rhs (vname : ValName) (ann : Option Surface.PolyTy)
    (rhs body : Surface.Expr) :
    surfaceExprSize rhs < surfaceExprSize (.letIn vname ann rhs body) := by
  simp only [surfaceExprSize]; omega

private theorem surfaceExprSize_lt_letIn_body (vname : ValName) (ann : Option Surface.PolyTy)
    (rhs body : Surface.Expr) :
    surfaceExprSize body < surfaceExprSize (.letIn vname ann rhs body) := by
  simp only [surfaceExprSize]; omega

private theorem surfaceExprSize_lt_letRecIn_body
    (binds : List (ValName × Option Surface.PolyTy × Surface.Expr)) (body : Surface.Expr) :
    surfaceExprSize body < surfaceExprSize (.letRecIn binds body) := by
  simp only [surfaceExprSize]; omega

private theorem surfaceExprSize_lt_ife_cond (c t f : Surface.Expr) :
    surfaceExprSize c < surfaceExprSize (.ife c t f) := by simp only [surfaceExprSize]; omega

private theorem surfaceExprSize_lt_ife_then (c t f : Surface.Expr) :
    surfaceExprSize t < surfaceExprSize (.ife c t f) := by simp only [surfaceExprSize]; omega

private theorem surfaceExprSize_lt_ife_else (c t f : Surface.Expr) :
    surfaceExprSize f < surfaceExprSize (.ife c t f) := by simp only [surfaceExprSize]; omega

private theorem surfaceExprSize_lt_match_scrut (scrut : Surface.Expr)
    (brs : List (Surface.Pattern × Surface.Expr)) :
    surfaceExprSize scrut < surfaceExprSize (.match_ scrut brs) := by simp only [surfaceExprSize]; omega

/-! ### Soundness: Bool → Prop -/

private theorem dTreeCasesOk_sound {ctors : CtorEnv} {T : TyName} :
    ∀ cases, dTreeCasesOk ctors T cases = true →
      ∀ c a t, (c, a, t) ∈ cases →
        ∃ ctor, LookupList.get? ctors c = some ctor ∧ ctor.tyName = T ∧
          a = ctor.contents.length
  | [], _, _c, _a, _t, hmem => nomatch hmem
  | (c, a, t) :: rest, hok, c', a', t', hmem => by
    simp only [dTreeCasesOk] at hok
    cases hg : LookupList.get? ctors c with
    | none => simp [hg] at hok
    | some ctor =>
      simp only [hg, Bool.and_eq_true, beq_iff_eq] at hok
      rcases hok with ⟨⟨hty, har⟩, hrest⟩
      simp only [List.mem_cons] at hmem
      rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
      · exact ⟨ctor, hg, hty, har⟩
      · exact dTreeCasesOk_sound rest hrest c' a' t' hmem

private theorem mem_of_get?_eq_some {k v : Type} [DecidableEq k]
    {l : LookupList k v} {key : k} {val : v}
    (h : LookupList.get? l key = some val) : (key, val) ∈ l := by
  induction l with
  | nil => simp [LookupList.get?] at h
  | cons hd tl ih =>
    simp only [LookupList.get?] at h
    cases hd with
    | mk k₀ v₀ =>
      split_ifs at h with hk
      · simp only [List.mem_cons]; left; simp_all
      · exact List.mem_cons_of_mem _ (ih h)

private theorem dTreeAllCtorsCovered_sound {ctors : CtorEnv} {T : TyName}
    {cases : List (CtorName × Nat × DTree)}
    (h : dTreeAllCtorsCovered ctors T cases = true) :
    ∀ c ctor, LookupList.get? ctors c = some ctor → ctor.tyName = T →
      ∃ a t, (c, a, t) ∈ cases := by
  intro c ctor hg hty
  have hc := (List.all_eq_true.mp h) c
    (List.mem_map.mpr ⟨(c, ctor), mem_of_get?_eq_some hg, rfl⟩)
  simp only [hg, Bool.or_eq_true, bne_iff_ne] at hc
  rcases hc with hne | hin
  · exact (hne hty).elim
  · obtain ⟨⟨c', a, t⟩, hmemC, hc'⟩ := List.any_eq_true.mp hin
    simp only [beq_iff_eq] at hc'
    exact hc' ▸ ⟨a, t, hmemC⟩

/-- Unpack `dTreeCasesRec = true` into per-case Bool exhaustiveness. -/
private theorem dTreeCasesRec_get {ctors : CtorEnv} {octx : OccCtx} {occ : Occ}
    {tyArgs : List Ty} :
    ∀ cases, dTreeCasesRec ctors octx occ tyArgs cases = true →
      ∀ c a t, (c, a, t) ∈ cases →
        dTreeExhaustiveB ctors (OccCtx.extend octx occ (instFieldTys ctors c tyArgs)) t = true
  | [], _, _c, _a, _t, hmem => nomatch hmem
  | (c, a, t) :: rest, hok, c', a', t', hmem => by
    simp only [dTreeCasesRec, Bool.and_eq_true] at hok
    simp only [List.mem_cons] at hmem
    rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
    · exact hok.1
    · exact dTreeCasesRec_get rest hok.2 c' a' t' hmem

private theorem sizeOf_lt_of_mem_dTree_cases {occ : Occ}
    {cases : List (CtorName × Nat × DTree)} {dflt : DTree}
    {c : CtorName} {a : Nat} {t : DTree}
    (h : (c, a, t) ∈ cases) :
    sizeOf t < sizeOf (DTree.switch occ cases dflt) := by
  have h1 := List.sizeOf_lt_of_mem h
  have h2 : sizeOf t < sizeOf (c, a, t) := by
    simp only [Prod.mk.sizeOf_spec]; omega
  have h3 : sizeOf (c, a, t) < sizeOf (DTree.switch occ cases dflt) := by
    simp only [DTree.switch.sizeOf_spec]; omega
  exact Nat.lt_trans h2 h3

private theorem sizeOf_dflt_lt_switch {occ : Occ}
    {cases : List (CtorName × Nat × DTree)} {dflt : DTree} :
    sizeOf dflt < sizeOf (DTree.switch occ cases dflt) := by
  simp only [DTree.switch.sizeOf_spec]; omega

theorem dTreeExhaustiveB_sound {ctors : CtorEnv} {octx : OccCtx} {t : DTree}
    (h : dTreeExhaustiveB ctors octx t = true) :
    DTreeExhaustive ctors octx t := by
  suffices hgoal : ∀ (n : Nat) (t : DTree) (octx : OccCtx), sizeOf t ≤ n →
      dTreeExhaustiveB ctors octx t = true → DTreeExhaustive ctors octx t by
    exact hgoal (sizeOf t) t octx le_rfl h
  intro n
  induction n with
  | zero =>
    intro t octx hsz hB
    have h0 : sizeOf t = 0 := Nat.le_zero.mp hsz
    cases t <;> simp [DTree.leaf.sizeOf_spec, DTree.fail.sizeOf_spec,
      DTree.switch.sizeOf_spec] at h0 hB ⊢
  | succ n ihn =>
    intro t octx hsz hB
    match t with
    | .fail => cases hB
    | .leaf act binds => exact .leaf
    | .switch occ cases dflt =>
      simp only [dTreeExhaustiveB] at hB
      cases hg : LookupList.get? octx occ with
      | none => simp [hg] at hB
      | some ty =>
        match ty with
        | .prim _ | .arrow _ _ | .bvar _ | .fvar _ => simp [hg] at hB
        | .customTy T tyArgs =>
          simp only [hg] at hB
          have casesOk : dTreeCasesOk ctors T cases = true := by
            cases dflt <;> simp only [Bool.and_eq_true] at hB <;> exact hB.1.1
          have recOk : dTreeCasesRec ctors octx occ tyArgs cases = true := by
            cases dflt <;> simp only [Bool.and_eq_true] at hB <;> exact hB.1.2
          have hcases := dTreeCasesOk_sound cases casesOk
          have hrec : ∀ c a t, (c, a, t) ∈ cases →
              DTreeExhaustive ctors
                (OccCtx.extend octx occ (instFieldTys ctors c tyArgs)) t := by
            intro c a t' hmem
            have hB' := dTreeCasesRec_get cases recOk c a t' hmem
            have hlt := sizeOf_lt_of_mem_dTree_cases (occ := occ) (dflt := dflt) hmem
            have hle : sizeOf t' ≤ n := Nat.le_of_lt_succ (Nat.lt_of_lt_of_le hlt hsz)
            exact ihn t' _ hle hB'
          match dflt with
          | .fail =>
            simp only [Bool.and_eq_true] at hB
            exact .switchFail hg hcases hrec (dTreeAllCtorsCovered_sound hB.2)
          | .leaf act binds =>
            simp only [Bool.and_eq_true] at hB
            have hle : sizeOf (DTree.leaf act binds) ≤ n :=
              Nat.le_of_lt_succ (Nat.lt_of_lt_of_le sizeOf_dflt_lt_switch hsz)
            exact .switchDefault (fun hneq => nomatch hneq) hg hcases hrec
              (ihn (.leaf act binds) octx hle hB.2)
          | .switch occ' cases' dflt' =>
            simp only [Bool.and_eq_true] at hB
            have hle : sizeOf (DTree.switch occ' cases' dflt') ≤ n :=
              Nat.le_of_lt_succ (Nat.lt_of_lt_of_le sizeOf_dflt_lt_switch hsz)
            exact .switchDefault (fun hneq => nomatch hneq) hg hcases hrec
              (ihn (.switch occ' cases' dflt') octx hle hB.2)

theorem matchExhaustiveB_sound {ctors : CtorEnv} {T : TyName} {tyArgs : List Ty}
    {ps : List Surface.Pattern}
    (h : matchExhaustiveB ctors T tyArgs ps = true) :
    MatchExhaustive ctors T tyArgs ps :=
  dTreeExhaustiveB_sound h

/-- Unpack list Bool coverage into per-element checks. -/
private theorem checkExhaustiveList_get {ctors : CtorEnv} :
    ∀ es, checkExhaustiveList ctors es = true →
      ∀ e ∈ es, checkExhaustive ctors e = true
  | [] => by intro _ e he; nomatch he
  | e :: es => by
    intro h e' he'
    simp only [checkExhaustiveList, Bool.and_eq_true] at h
    simp only [List.mem_cons] at he'
    rcases he' with ⟨rfl, _⟩ | he'
    · exact h.1
    · exact checkExhaustiveList_get es h.2 e' he'

/-- Unpack `letRecIn` binding Bool coverage into per-binding checks. -/
private theorem checkExhaustiveLetRecBinds_get {ctors : CtorEnv} :
    ∀ binds, checkExhaustiveLetRecBinds ctors binds = true →
      ∀ b ∈ binds, checkExhaustive ctors b.2.2 = true
  | [] => by intro _ b hb; nomatch hb
  | (_, _, rhs) :: rest => by
    intro h b' hb'
    simp only [checkExhaustiveLetRecBinds, Bool.and_eq_true] at h
    simp only [List.mem_cons] at hb'
    rcases hb' with ⟨rfl, rfl, rfl⟩ | hb'
    · exact h.1
    · exact checkExhaustiveLetRecBinds_get rest h.2 b' hb'

/-- Unpack branch Bool coverage into per-branch checks. -/
private theorem checkExhaustiveBranches_get {ctors : CtorEnv} :
    ∀ brs, checkExhaustiveBranches ctors brs = true →
      ∀ pb ∈ brs, checkExhaustive ctors pb.2 = true
  | [] => by intro _ pb hmem; nomatch hmem
  | (p, b) :: rest => by
    intro h pb' hmem
    simp only [checkExhaustiveBranches, Bool.and_eq_true] at h
    simp only [List.mem_cons] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | hmem
    · exact h.1
    · exact checkExhaustiveBranches_get rest h.2 pb' hmem

/-- Unpack branch Bool coverage. -/
private theorem checkExhaustiveBranches_sound {ctors : CtorEnv} :
    ∀ brs, checkExhaustiveBranches ctors brs = true →
      (∀ s, checkExhaustive ctors s = true → SurfaceCovers ctors s) →
      ∀ p b, (p, b) ∈ brs → SurfaceCovers ctors b
  | [] => by intro _ _ _ _ hmem; nomatch hmem
  | (p, b) :: rest => by
    intro h ih p' b' hmem
    simp only [checkExhaustiveBranches, Bool.and_eq_true] at h
    simp only [List.mem_cons] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | hmem
    · exact ih b h.1
    · exact checkExhaustiveBranches_sound rest h.2 ih p' b' hmem

private theorem surfaceExprSize_lt_of_mem_list {items : List Surface.Expr} {e : Surface.Expr}
    (h : e ∈ items) : surfaceExprSize e < surfaceExprSize (.list items) := by
  induction items with
  | nil => nomatch h
  | cons hd tl ih =>
    simp only [List.mem_cons] at h
    rcases h with rfl | h
    · simp only [surfaceExprSize, surfaceExprSizeList]; omega
    · have hlt := ih h
      have htail : surfaceExprSize (.list tl) < surfaceExprSize (.list (hd :: tl)) := by
        simp only [surfaceExprSize, surfaceExprSizeList]; omega
      exact Nat.lt_trans hlt htail

private theorem surfaceExprSize_lt_of_mem_letRecBinds
    {binds : List (ValName × Option Surface.PolyTy × Surface.Expr)}
    {body : Surface.Expr}
    {b : ValName × Option Surface.PolyTy × Surface.Expr}
    (h : b ∈ binds) :
    surfaceExprSize b.2.2 < surfaceExprSize (.letRecIn binds body) := by
  induction binds with
  | nil => nomatch h
  | cons hd rest ih =>
    rcases hd with ⟨v, ann, rhs⟩
    simp only [List.mem_cons] at h
    rcases h with ⟨⟨rfl, rfl, rfl⟩, _⟩ | h
    · simp only [surfaceExprSize, surfaceExprSizeLetRecBinds]; omega
    · have hlt := ih h
      have htail : surfaceExprSize (.letRecIn rest body) <
          surfaceExprSize (.letRecIn ((v, ann, rhs) :: rest) body) := by
        simp only [surfaceExprSize, surfaceExprSizeLetRecBinds]; omega
      exact Nat.lt_trans hlt htail

private theorem surfaceExprSize_lt_of_mem_branches
    {scrut : Surface.Expr} {brs : List (Surface.Pattern × Surface.Expr)}
    {p : Surface.Pattern} {b : Surface.Expr} (h : (p, b) ∈ brs) :
    surfaceExprSize b < surfaceExprSize (.match_ scrut brs) := by
  induction brs with
  | nil => nomatch h
  | cons pb rest ih =>
    rcases pb with ⟨p', b'⟩
    simp only [List.mem_cons] at h
    rcases h with ⟨rfl, rfl⟩ | h
    · simp only [surfaceExprSize, surfaceExprSizeBranches]; omega
    · have hlt := ih h
      have htail : surfaceExprSize (.match_ scrut rest) <
          surfaceExprSize (.match_ scrut ((p', b') :: rest)) := by
        simp only [surfaceExprSize, surfaceExprSizeBranches]; omega
      exact Nat.lt_trans hlt htail

/-- Bool surface coverage ⇒ `SurfaceCovers` (uses the same `T`/`tyArgs` seed as the checker). -/
theorem checkExhaustive_sound {ctors : CtorEnv} :
    ∀ (s : Surface.Expr), checkExhaustive ctors s = true → SurfaceCovers ctors s := by
  suffices hgoal : ∀ (n : Nat) (s : Surface.Expr), surfaceExprSize s ≤ n →
      checkExhaustive ctors s = true → SurfaceCovers ctors s by
    intro s h
    exact hgoal (surfaceExprSize s) s le_rfl h
  intro n
  induction n with
  | zero =>
    intro s hsz h
    have h0 : surfaceExprSize s = 0 := Nat.le_zero.mp hsz
    cases s <;> simp only [surfaceExprSize] at h0 <;> omega
  | succ n ih =>
    intro s hsz h
    match s with
    | .primLit _ => exact .primLit
    | .var _ => exact .var
    | .ctor _ => exact .ctor
    | .pair a b =>
      simp only [checkExhaustive, Bool.and_eq_true] at h
      have hle₁ : surfaceExprSize a ≤ n :=
        Nat.le_of_lt_succ (Nat.lt_of_lt_of_le (surfaceExprSize_lt_pair_left a b) hsz)
      have hle₂ : surfaceExprSize b ≤ n :=
        Nat.le_of_lt_succ (Nat.lt_of_lt_of_le (surfaceExprSize_lt_pair_right a b) hsz)
      exact .pair (ih a hle₁ h.1) (ih b hle₂ h.2)
    | .cons hd tl =>
      simp only [checkExhaustive, Bool.and_eq_true] at h
      have hle₁ : surfaceExprSize hd ≤ n :=
        Nat.le_of_lt_succ (Nat.lt_of_lt_of_le (surfaceExprSize_lt_cons_head hd tl) hsz)
      have hle₂ : surfaceExprSize tl ≤ n :=
        Nat.le_of_lt_succ (Nat.lt_of_lt_of_le (surfaceExprSize_lt_cons_tail hd tl) hsz)
      exact .cons (ih hd hle₁ h.1) (ih tl hle₂ h.2)
    | .list items =>
      simp only [checkExhaustive] at h
      refine .list ?_
      intro e he
      have heq := checkExhaustiveList_get items h e he
      have hle : surfaceExprSize e ≤ n :=
        Nat.le_of_lt_succ (Nat.lt_of_lt_of_le (surfaceExprSize_lt_of_mem_list he) hsz)
      exact ih e hle heq
    | .lambda param ann body =>
      simp only [checkExhaustive] at h
      have hle : surfaceExprSize body ≤ n :=
        Nat.le_of_lt_succ (Nat.lt_of_lt_of_le (surfaceExprSize_lt_lambda_body param ann body) hsz)
      exact .lambda (ih body hle h)
    | .app f x =>
      simp only [checkExhaustive, Bool.and_eq_true] at h
      have hle₁ : surfaceExprSize f ≤ n :=
        Nat.le_of_lt_succ (Nat.lt_of_lt_of_le (surfaceExprSize_lt_app_fn f x) hsz)
      have hle₂ : surfaceExprSize x ≤ n :=
        Nat.le_of_lt_succ (Nat.lt_of_lt_of_le (surfaceExprSize_lt_app_arg f x) hsz)
      exact .app (ih f hle₁ h.1) (ih x hle₂ h.2)
    | .letIn vname ann rhs body =>
      simp only [checkExhaustive, Bool.and_eq_true] at h
      have hle₁ : surfaceExprSize rhs ≤ n :=
        Nat.le_of_lt_succ (Nat.lt_of_lt_of_le (surfaceExprSize_lt_letIn_rhs vname ann rhs body) hsz)
      have hle₂ : surfaceExprSize body ≤ n :=
        Nat.le_of_lt_succ (Nat.lt_of_lt_of_le (surfaceExprSize_lt_letIn_body vname ann rhs body) hsz)
      exact .letIn (ih rhs hle₁ h.1) (ih body hle₂ h.2)
    | .letRecIn binds body =>
      simp only [checkExhaustive, Bool.and_eq_true] at h
      refine .letRecIn ?_ (ih body (Nat.le_of_lt_succ (Nat.lt_of_lt_of_le
        (surfaceExprSize_lt_letRecIn_body binds body) hsz)) h.2)
      intro b hb
      have heq := checkExhaustiveLetRecBinds_get binds h.1 b hb
      have hle : surfaceExprSize b.2.2 ≤ n :=
        Nat.le_of_lt_succ (Nat.lt_of_lt_of_le (surfaceExprSize_lt_of_mem_letRecBinds hb) hsz)
      exact ih b.2.2 hle heq
    | .ife c t f =>
      simp only [checkExhaustive, Bool.and_eq_true] at h
      have hle₁ : surfaceExprSize c ≤ n :=
        Nat.le_of_lt_succ (Nat.lt_of_lt_of_le (surfaceExprSize_lt_ife_cond c t f) hsz)
      have hle₂ : surfaceExprSize t ≤ n :=
        Nat.le_of_lt_succ (Nat.lt_of_lt_of_le (surfaceExprSize_lt_ife_then c t f) hsz)
      have hle₃ : surfaceExprSize f ≤ n :=
        Nat.le_of_lt_succ (Nat.lt_of_lt_of_le (surfaceExprSize_lt_ife_else c t f) hsz)
      exact .ife (ih c hle₁ h.1.1.1) (ih t hle₂ h.1.1.2) (ih f hle₃ h.1.2)
        (matchExhaustiveB_sound h.2)
    | .match_ scrut brs =>
      simp only [checkExhaustive, Bool.and_eq_true] at h
      rcases h with ⟨⟨hs, hbrs⟩, hexh⟩
      have hscrut : surfaceExprSize scrut ≤ n :=
        Nat.le_of_lt_succ (Nat.lt_of_lt_of_le (surfaceExprSize_lt_match_scrut scrut brs) hsz)
      cases hT : tyNameFromPatterns ctors (brs.map Prod.fst) with
      | some T =>
        simp only [hT] at hexh
        refine .match_ (T := T) (tyArgs := tyArgsGuess ctors T) (ih scrut hscrut hs) ?_ ?_
        · intro p b hb
          have heq := checkExhaustiveBranches_get brs hbrs (p, b) hb
          have hle : surfaceExprSize b ≤ n :=
            Nat.le_of_lt_succ (Nat.lt_of_lt_of_le (surfaceExprSize_lt_of_mem_branches hb) hsz)
          exact ih b hle heq
        · exact matchExhaustiveB_sound hexh
      | none =>
        simp only [hT] at hexh
        refine .match_ (T := nBool) (tyArgs := []) (ih scrut hscrut hs) ?_ ?_
        · intro p b hb
          have heq := checkExhaustiveBranches_get brs hbrs (p, b) hb
          have hle : surfaceExprSize b ≤ n :=
            Nat.le_of_lt_succ (Nat.lt_of_lt_of_le (surfaceExprSize_lt_of_mem_branches hb) hsz)
          exact ih b hle heq
        · exact matchExhaustiveB_sound hexh

/- Concrete instances are *theorems* (`native_decide`), not `#guard` smoke.
    Soundness is `checkExhaustive_sound` / `matchExhaustiveB_sound` above. -/
example : matchExhaustiveB ctorsDemo nBool []
    [.ctor cTrue [], .ctor cFalse []] = true := by native_decide
example : matchExhaustiveB ctorsDemo nBool []
    [.ctor cTrue []] = false := by native_decide
example : checkExhaustive ctorsDemo (.primLit (.int 0)) = true := by native_decide
example : checkExhaustive ctorsDemo
    (.ife (.primLit (.bool true)) (.primLit (.int 1)) (.primLit (.int 0))) = true := by
  native_decide
example : checkExhaustive ctorsDemo (.primLit (.int 0)) = true →
    SurfaceCovers ctorsDemo (.primLit (.int 0)) :=
  checkExhaustive_sound _

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
  -- @TODO(pattern-λ): no `LowersExpr` ctors for `.lambda (.ctor/pair/cons/list) …`.
  -- Executable `lowerExpr` returns `none` for those; add desugar + ctors together.
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
        (lowerMatch c' [.ctor cTrue [], .ctor cFalse []] (bodyFn [t', f']))
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
          have hbodyFn : (fun i => [t', f'].getD i (.ctor cNil)) = bodyFn [t', f'] := by
            funext i; simp [bodyFn, matchBodyDefault]
          rw [hbodyFn]
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


/-! ### Functional `Lowers` away from surface `match_`

`LowersExpr.match_` is one-to-many (`emitInner`). Every other rule — including
`ife`, which pins the same `lowerMatch` as `lower` — is deterministic in the
Core term. Full uniqueness therefore holds on the `NoMatch` fragment (no
surface `match_` node anywhere). Nested `match_` inside `pair`/`let`/… also
breaks uniqueness of the outer term, so the hypothesis is global on `s`. -/

mutual
/-- No surface `match_` anywhere in the expression. `ife` is allowed (Core-level
    match via deterministic `lowerMatch` sugar). -/
inductive SurfaceExprNoMatch : Surface.Expr → Prop where
  | primLit {p} : SurfaceExprNoMatch (.primLit p)
  | pair {a b} : SurfaceExprNoMatch a → SurfaceExprNoMatch b → SurfaceExprNoMatch (.pair a b)
  | cons {h t} : SurfaceExprNoMatch h → SurfaceExprNoMatch t → SurfaceExprNoMatch (.cons h t)
  | list {items} : SurfaceExprListNoMatch items → SurfaceExprNoMatch (.list items)
  | lambda {param ann body} :
      SurfaceExprNoMatch body → SurfaceExprNoMatch (.lambda param ann body)
  | app {f x} : SurfaceExprNoMatch f → SurfaceExprNoMatch x → SurfaceExprNoMatch (.app f x)
  | letIn {name ann rhs body} :
      SurfaceExprNoMatch rhs → SurfaceExprNoMatch body →
      SurfaceExprNoMatch (.letIn name ann rhs body)
  | letRecIn {binds body} :
      SurfaceExprLetRecNoMatch binds → SurfaceExprNoMatch body →
      SurfaceExprNoMatch (.letRecIn binds body)
  | var {name} : SurfaceExprNoMatch (.var name)
  | ctor {name} : SurfaceExprNoMatch (.ctor name)
  | ife {c t f} :
      SurfaceExprNoMatch c → SurfaceExprNoMatch t → SurfaceExprNoMatch f →
      SurfaceExprNoMatch (.ife c t f)

inductive SurfaceExprListNoMatch : List Surface.Expr → Prop where
  | nil : SurfaceExprListNoMatch []
  | cons {e es} : SurfaceExprNoMatch e → SurfaceExprListNoMatch es → SurfaceExprListNoMatch (e :: es)

inductive SurfaceExprLetRecNoMatch :
    List (ValName × Option Surface.PolyTy × Surface.Expr) → Prop where
  | nil : SurfaceExprLetRecNoMatch []
  | cons {bind rest} :
      SurfaceExprNoMatch bind.2.2 → SurfaceExprLetRecNoMatch rest →
      SurfaceExprLetRecNoMatch (bind :: rest)
end

mutual
theorem LowersExpr_unique_of_NoMatch (ctors : CtorEnv) (ke : KindEnv) (tvs : List ValName)
    (vs : List ValName) (s : Surface.Expr) (c₁ c₂ : Expr)
    (hnm : SurfaceExprNoMatch s)
    (h₁ : LowersExpr ctors ke tvs vs s c₁) (h₂ : LowersExpr ctors ke tvs vs s c₂) :
    c₁ = c₂ := by
  cases hnm with
  | primLit =>
    cases h₁ with
    | primLitUnit | primLitInt | primLitNat | primLitChar | primLitBool =>
      cases h₂; rfl
  | pair ha hb =>
    cases h₁; cases h₂
    expose_names
    have := LowersExpr_unique_of_NoMatch ctors ke tvs vs _ _ _ ha h h_2
    have := LowersExpr_unique_of_NoMatch ctors ke tvs vs _ _ _ hb h_1 h_3
    simp_all
  | cons hh ht =>
    cases h₁; cases h₂
    expose_names
    have := LowersExpr_unique_of_NoMatch ctors ke tvs vs _ _ _ hh h_1 h_3
    have := LowersExpr_unique_of_NoMatch ctors ke tvs vs _ _ _ ht h_2 h_4
    simp_all
  | list hitems =>
    cases h₁; cases h₂
    expose_names
    have := LowersExprList_unique_of_NoMatch ctors ke tvs vs _ _ _ hitems h h_1
    simp_all
  | lambda hb =>
    cases h₁ with
    | lambda_name hann₁ hb₁ =>
      cases h₂ with
      | lambda_name hann₂ hb₂ =>
        expose_names
        have hb' := LowersExpr_unique_of_NoMatch ctors ke tvs _ _ _ _ hb hb₁ hb₂
        cases ann with
        | none =>
          cases hann₁; cases hann₂; simp [hb']
        | some τ =>
          cases hτ : lowerTy ke tvs τ with
          | none => simp [hτ] at hann₁
          | some τ' =>
            simp [hτ] at hann₁ hann₂
            cases hann₁; cases hann₂; simp [hb']
    | lambda_wild hann₁ hb₁ =>
      cases h₂ with
      | lambda_wild hann₂ hb₂ =>
        expose_names
        have hb' := LowersExpr_unique_of_NoMatch ctors ke tvs _ _ _ _ hb hb₁ hb₂
        cases ann with
        | none =>
          cases hann₁; cases hann₂; simp [hb']
        | some τ =>
          cases hτ : lowerTy ke tvs τ with
          | none => simp [hτ] at hann₁
          | some τ' =>
            simp [hτ] at hann₁ hann₂
            cases hann₁; cases hann₂; simp [hb']
  | app hf hx =>
    cases h₁; cases h₂
    expose_names
    have := LowersExpr_unique_of_NoMatch ctors ke tvs vs _ _ _ hf h h_2
    have := LowersExpr_unique_of_NoMatch ctors ke tvs vs _ _ _ hx h_1 h_3
    simp_all
  | letIn hr hb =>
    cases h₁; cases h₂
    expose_names
    have hr' := LowersExpr_unique_of_NoMatch ctors ke tvs vs _ _ _ hr h_1 h_4
    have hb' := LowersExpr_unique_of_NoMatch ctors ke tvs _ _ _ _ hb h_2 h_5
    cases ann with
    | none =>
      cases h; cases h_3; simp [hr', hb']
    | some σ =>
      cases hσ : lowerPoly ke σ with
      | none => simp [hσ] at h
      | some σ' =>
        simp [hσ] at h h_3
        cases h; cases h_3; simp [hr', hb']
  | letRecIn hbinds hb =>
    cases h₁; cases h₂
    expose_names
    have hann : anns' = anns'_1 := Option.some_inj.mp (h.symm.trans h_3)
    have hbinds' :=
      LowersRecBinds_unique_of_NoMatch ctors ke tvs _ _ _ _ hbinds h_1 h_4
    have hb' := LowersExpr_unique_of_NoMatch ctors ke tvs _ _ _ _ hb h_2 h_5
    simp [hann, hbinds', hb']
  | var =>
    cases h₁; cases h₂
    expose_names
    have hi : i = i_1 := Option.some_inj.mp (h.symm.trans h_1)
    simp [hi]
  | ctor =>
    cases h₁; cases h₂; rfl
  | ife hc ht hf =>
    cases h₁; cases h₂
    expose_names
    have := LowersExpr_unique_of_NoMatch ctors ke tvs vs _ _ _ hc h h_3
    have := LowersExpr_unique_of_NoMatch ctors ke tvs vs _ _ _ ht h_1 h_4
    have := LowersExpr_unique_of_NoMatch ctors ke tvs vs _ _ _ hf h_2 h_5
    simp_all

theorem LowersExprList_unique_of_NoMatch (ctors : CtorEnv) (ke : KindEnv) (tvs : List ValName)
    (vs : List ValName) (es : List Surface.Expr) (es₁ es₂ : List Expr)
    (hnm : SurfaceExprListNoMatch es)
    (h₁ : LowersExprList ctors ke tvs vs es es₁)
    (h₂ : LowersExprList ctors ke tvs vs es es₂) : es₁ = es₂ := by
  cases hnm with
  | nil =>
    cases h₁; cases h₂; rfl
  | cons he hes =>
    cases h₁; cases h₂
    expose_names
    have := LowersExpr_unique_of_NoMatch ctors ke tvs vs _ _ _ he h h_2
    have := LowersExprList_unique_of_NoMatch ctors ke tvs vs _ _ _ hes h_1 h_3
    simp_all

theorem LowersRecBinds_unique_of_NoMatch (ctors : CtorEnv) (ke : KindEnv) (tvs : List ValName)
    (vs : List ValName) (binds : List (ValName × Option Surface.PolyTy × Surface.Expr))
    (es₁ es₂ : List Expr)
    (hnm : SurfaceExprLetRecNoMatch binds)
    (h₁ : LowersRecBinds ctors ke tvs vs binds es₁)
    (h₂ : LowersRecBinds ctors ke tvs vs binds es₂) : es₁ = es₂ := by
  cases hnm with
  | nil =>
    cases h₁; cases h₂; rfl
  | cons he hrest =>
    cases h₁; cases h₂
    expose_names
    have := LowersExpr_unique_of_NoMatch ctors ke tvs vs _ _ _ he h h_2
    have := LowersRecBinds_unique_of_NoMatch ctors ke tvs vs _ _ _ hrest h_1 h_3
    simp_all
end

/-- On the `NoMatch` fragment, a `Lowers` witness equals the executable `lower`. -/
theorem lowerExpr_eq_of_LowersExpr_of_NoMatch {ctors : CtorEnv} {ke : KindEnv}
    {tvs vs : List ValName} {s : Surface.Expr} {c₀ c : Expr}
    (hnm : SurfaceExprNoMatch s)
    (hL : LowersExpr ctors ke tvs vs s c₀)
    (hlow : lowerExpr ke tvs vs s = some c) :
    c₀ = c :=
  LowersExpr_unique_of_NoMatch ctors ke tvs vs s c₀ c hnm hL (lowerExpr_LowersExpr hlow)


/-! ## 7. Surface well-typedness — DEFINED via the relation (no `Surface.TypeOf`)

Approach A / **option 1a**: closed well-typedness is inhabited open inductive
`SurfaceWTExpr`. Former weak meaning was
`∃ c, Lowers s c ∧ (typecheck ctors c).isSome` — archaeology:

```
-- old: def SurfaceWT ctors s := ∃ c, Lowers ctors s c ∧ (typecheck ctors c).isSome
```

The strong carrier requires open branch typings at `match_` / `ife`, so the
executable `lower` output is typeable without transferring from a weird B1
`emitInner`. -/

/-- Env for a match branch body: trivial schemes for pattern binders (in
    `patBindTys` / `patVars` pre-order) prepended to `Γ`. Mirrors
    `LowersBranches` typing under `patVars p ++ vs`. -/
def branchBodyEnv (Γ : Env) (bindTys : List Ty) : Env :=
  bindTys.map PolyTy.mkTrivial ++ Γ

/-- Instantiated ctor field types when `τ = customTy T tyArgs` and `c ∈ T`. -/
def patGctorFieldTys (ctors : CtorEnv) (c : CtorName) (τ : Ty) : Option (List Ty) :=
  match τ with
  | .customTy T tyArgs =>
    match LookupList.get? ctors c with
    | some ctor => if ctor.tyName = T then some (instFieldTys ctors c tyArgs) else none
    | none => none
  | _ => none

mutual
/-- Types of variables bound by a generic pattern, in capture (`matchG`) order. -/
def patBindTysG (ctors : CtorEnv) : GPat → Ty → List Ty
  | .gbind, τ => [τ]
  | .gwild, _ => []
  | .gctor c args, τ =>
    match patGctorFieldTys ctors c τ with
    | none => []
    | some fieldTys => patBindTysGList ctors args fieldTys

def patBindTysGList (ctors : CtorEnv) : List GPat → List Ty → List Ty
  | [], _ => []
  | p :: ps, τ :: τs => patBindTysG ctors p τ ++ patBindTysGList ctors ps τs
  | _, _ => []
end

/-- Surface-facing wrapper: bind types of `p` at scrutinee type `τ`. -/
def patBindTys (ctors : CtorEnv) (p : Surface.Pattern) (τ : Ty) : List Ty :=
  patBindTysG ctors (norm p) τ

/-- Strong open surface well-typedness (Approach A / 1a).
    At `match_`, ingredients are typed openly — not “some weird emitInner typechecks”.
    Match-free fragments use `of_lowers` (unique Lowers + TypeOfHM). Match-capable
    forms recurse so induction reaches nested matches. -/
inductive SurfaceWTExpr (ctors : CtorEnv) (ke : KindEnv) :
    List ValName → List ValName → Env → Surface.Expr → Ty → Prop where
  /-- Match-free fragment: Lowers is unique, so TypeOfHM transfers to `lowerExpr`. -/
  | of_lowers {tvs vs Γ s c τ} :
      SurfaceExprNoMatch s →
      LowersExpr ctors ke tvs vs s c →
      TypeOfHM ⟨Γ, ctors⟩ c τ →
      SurfaceWTExpr ctors ke tvs vs Γ s τ
  | pair {tvs vs Γ a b τa τb τ} :
      SurfaceWTExpr ctors ke tvs vs Γ a τa →
      SurfaceWTExpr ctors ke tvs vs Γ b τb →
      TypeOfHM ⟨Γ, ctors⟩ (.ctor cPair) (.arrow τa (.arrow τb τ)) →
      SurfaceWTExpr ctors ke tvs vs Γ (.pair a b) τ
  | cons {tvs vs Γ h t τh τt τ} :
      SurfaceWTExpr ctors ke tvs vs Γ h τh →
      SurfaceWTExpr ctors ke tvs vs Γ t τt →
      TypeOfHM ⟨Γ, ctors⟩ (.ctor cCons) (.arrow τh (.arrow τt τ)) →
      SurfaceWTExpr ctors ke tvs vs Γ (.cons h t) τ
  | list {tvs vs Γ items τelem} :
      (∀ e ∈ items, SurfaceWTExpr ctors ke tvs vs Γ e τelem) →
      TypeOfHM ⟨Γ, ctors⟩ (.ctor cNil) (.customTy nList [τelem]) →
      TypeOfHM ⟨Γ, ctors⟩ (.ctor cCons)
        (.arrow τelem (.arrow (.customTy nList [τelem]) (.customTy nList [τelem]))) →
      SurfaceWTExpr ctors ke tvs vs Γ (.list items) (.customTy nList [τelem])
  | app {tvs vs Γ f x τarg τ} :
      SurfaceWTExpr ctors ke tvs vs Γ f (.arrow τarg τ) →
      SurfaceWTExpr ctors ke tvs vs Γ x τarg →
      SurfaceWTExpr ctors ke tvs vs Γ (.app f x) τ
  | lambda_name {tvs vs Γ x ann body paramTy bodyTy} :
      paramTy.IsLC →
      (match ann with
        | none => True
        | some τs => lowerTy ke tvs τs = some paramTy) →
      SurfaceWTExpr ctors ke tvs (x :: vs) (PolyTy.mkTrivial paramTy :: Γ) body bodyTy →
      SurfaceWTExpr ctors ke tvs vs Γ (.lambda (.name x) ann body) (.arrow paramTy bodyTy)
  | lambda_wild {tvs vs Γ ann body paramTy bodyTy} :
      paramTy.IsLC →
      (match ann with
        | none => True
        | some τs => lowerTy ke tvs τs = some paramTy) →
      SurfaceWTExpr ctors ke tvs (.mk "_" :: vs) (PolyTy.mkTrivial paramTy :: Γ) body bodyTy →
      SurfaceWTExpr ctors ke tvs vs Γ (.lambda .wildcard ann body) (.arrow paramTy bodyTy)
  /-- Unannotated mono let. Nested matches OK. -/
  | letIn {tvs vs Γ name rhs body τrhs τ} :
      SurfaceWTExpr ctors ke tvs vs Γ rhs τrhs →
      SurfaceWTExpr ctors ke tvs (name :: vs) (PolyTy.mkTrivial τrhs :: Γ) body τ →
      SurfaceWTExpr ctors ke tvs vs Γ (.letIn name none rhs body) τ
  /-- Annotated let (mono or poly). Requires `tvs = []`: ambient surface tyvars
      lower to type-bvars, and `openBoundTyVars` opens at depth 0, so the ladder
      collapse needs `TyBvarBounded 0` (true under `SurfaceWT`). Cofinite RHS
      openings mirror Core `GeneralisesTo`. -/
  | letInAnn {tvs vs Γ name σs σ rhs body τ L} :
      tvs = [] →
      lowerPoly ke σs = some σ →
      PolyTy.WF σ →
      (∀ Xs, FreshNames L σ.paramCount Xs →
        SurfaceWTExpr ctors ke tvs vs Γ rhs (σ.openVars Xs)) →
      SurfaceWTExpr ctors ke tvs (name :: vs) (σ :: Γ) body τ →
      SurfaceWTExpr ctors ke tvs vs Γ (.letIn name (some σs) rhs body) τ
  /-- Unannotated monomorphic `letRecIn` under the empty gen-var pool (RHS + body
      share `τs.map mkTrivial ++ Γ`). Annotated / poly-recursion groups use
      `letRecInAnn`. -/
  | letRecIn {tvs vs Γ}
      {binds : List (ValName × Option Surface.PolyTy × Surface.Expr)}
      {τs : List Ty} {body : Surface.Expr} {τ : Ty}
      (hlen : binds.length = τs.length)
      (hann : ∀ b ∈ binds, b.2.1 = none)
      (hbinds : ∀ (i : Nat) (hi : i < binds.length),
        SurfaceWTExpr ctors ke tvs (binds.map (·.1) ++ vs)
          (τs.map PolyTy.mkTrivial ++ Γ)
          (binds[i]'hi).2.2 (τs[i]'(Nat.lt_of_lt_of_eq hi hlen)))
      (hbody : SurfaceWTExpr ctors ke tvs (binds.map (·.1) ++ vs)
          (τs.map PolyTy.mkTrivial ++ Γ) body τ) :
      SurfaceWTExpr ctors ke tvs vs Γ (.letRecIn binds body) τ
  /-- Annotated / mixed / poly-recursion `letRecIn`. Surface analogue of Core
      `TypeOfHM.letRec` + `RecSpecs.MonoTyped`/`PolyTyped`. Requires `tvs = []`
      (same openBoundTyVars / `TyBvarBounded 0` reason as `letInAnn`).
      Core `PolyTyped` opens the RHS with `openTyVars Ys`; surface types the
      unopened RHS at `σ.openVars Ys` and the ladder collapses opening. -/
  | letRecInAnn {tvs vs Γ}
      {binds : List (ValName × Option Surface.PolyTy × Surface.Expr)}
      {anns' : List (Option PolyTy)}
      {specs : List RecSpec}
      {G L : List Nat}
      {body : Surface.Expr} {τ : Ty}
      (htvs : tvs = [])
      (hann : lowerAnnList ke (binds.map (·.2.1)) = some anns')
      (hlen : binds.length = specs.length)
      (hanns_eq : specs.map RecSpec.ann = anns')
      (hnodup : G.Nodup)
      (hmono_lc : ∀ τm, RecSpec.mono τm ∈ specs → τm.IsLC)
      (hpoly_wf : ∀ σ, RecSpec.poly σ ∈ specs → σ.WF)
      (hmono : ∀ Xs, FreshNames L G.length Xs →
        ∀ (i : Nat) (hi : i < binds.length), ∀ τm,
          specs[i]'(Nat.lt_of_lt_of_eq hi hlen) = .mono τm →
          SurfaceWTExpr ctors ke tvs (binds.map (·.1) ++ vs)
            (specs.map (RecSpec.rhsEntry G Xs) ++ Γ)
            (binds[i]'hi).2.2 (Ty.renameG G Xs τm))
      (hpoly : ∀ Xs, FreshNames L G.length Xs →
        ∀ (i : Nat) (hi : i < binds.length), ∀ σ,
          specs[i]'(Nat.lt_of_lt_of_eq hi hlen) = .poly σ →
          ∀ Ys, FreshNames (L ++ Xs) σ.paramCount Ys →
            SurfaceWTExpr ctors ke tvs (binds.map (·.1) ++ vs)
              (specs.map (RecSpec.rhsEntry G Xs) ++ Γ)
              (binds[i]'hi).2.2 (σ.openVars Ys))
      (hbody : SurfaceWTExpr ctors ke tvs (binds.map (·.1) ++ vs)
          (specs.map (RecSpec.bodyScheme G) ++ Γ) body τ) :
      SurfaceWTExpr ctors ke tvs vs Γ (.letRecIn binds body) τ
  | match_ {tvs vs Γ scrut brs T tyArgs τres} :
      SurfaceWTExpr ctors ke tvs vs Γ scrut (.customTy T tyArgs) →
      (∀ (i : Nat) (hi : i < brs.length),
        SurfaceWTExpr ctors ke tvs (patVars (brs[i]'hi).1 ++ vs)
          (branchBodyEnv Γ (patBindTys ctors (brs[i]'hi).1 (.customTy T tyArgs)))
          (brs[i]'hi).2 τres) →
      (∀ p ∈ brs.map Prod.fst, PatternWF ctors p (.customTy T tyArgs)) →
      MatchExhaustive ctors T tyArgs (brs.map Prod.fst) →
      LookupList.get? (kindEnvOfCtors ctors) T = some tyArgs.length →
      Ty.WellKinded (kindEnvOfCtors ctors) 0 (.customTy T tyArgs) →
      SurfaceWTExpr ctors ke tvs vs Γ (.match_ scrut brs) τres
  | ife {tvs vs Γ c t f τ} :
      SurfaceWTExpr ctors ke tvs vs Γ c (.customTy nBool []) →
      SurfaceWTExpr ctors ke tvs vs Γ t τ →
      SurfaceWTExpr ctors ke tvs vs Γ f τ →
      (∀ p ∈ ([.ctor cTrue [], .ctor cFalse []] : List Surface.Pattern),
        PatternWF ctors p (.customTy nBool [])) →
      MatchExhaustive ctors nBool [] [.ctor cTrue [], .ctor cFalse []] →
      LookupList.get? (kindEnvOfCtors ctors) nBool = some 0 →
      Ty.WellKinded (kindEnvOfCtors ctors) 0 (.customTy nBool []) →
      SurfaceWTExpr ctors ke tvs vs Γ (.ife c t f) τ

/-- Closed surface well-typedness: some result type under empty scopes/env. -/
def SurfaceWT (ctors : CtorEnv) (s : Surface.Expr) : Prop :=
  ∃ τ, SurfaceWTExpr ctors (kindEnvOfCtors ctors) [] [] [] s τ

/-- Weak (pre-1a) SurfaceWT, retained for the match-free uniqueness transfer. -/
def SurfaceWT_weak (ctors : CtorEnv) (s : Surface.Expr) : Prop :=
  ∃ c, Lowers ctors s c ∧ (typecheck ctors c).isSome

/-- Match-free corollary: `SurfaceWT_weak` + `lower` ⇒ `typecheck`. -/
theorem typecheck_of_lower_of_SurfaceWT_of_NoMatch {ctors : CtorEnv} {s : Surface.Expr}
    {c : Expr}
    (hnm : SurfaceExprNoMatch s)
    (hwt : SurfaceWT_weak ctors s) (hlow : lower ctors s = some c) :
    (typecheck ctors c).isSome := by
  obtain ⟨c₀, hL, htc₀⟩ := hwt
  have heq : c₀ = c := by
    simp only [Lowers, lower] at hL hlow
    exact lowerExpr_eq_of_LowersExpr_of_NoMatch hnm hL hlow
  simpa [heq] using htc₀

/-- Invert a `Lowers` derivation at surface `match_`. -/
theorem LowersExpr_match_inv {ctors : CtorEnv} {ke : KindEnv} {tvs vs : List ValName}
    {scrut : Surface.Expr} {brs : List (Surface.Pattern × Surface.Expr)} {c : Expr}
    (h : LowersExpr ctors ke tvs vs (.match_ scrut brs) c) :
    ∃ scrut' bodies' emitInner,
      c = .letIn none scrut' emitInner ∧
      LowersExpr ctors ke tvs vs scrut scrut' ∧
      LowersBranches ctors ke tvs vs brs bodies' ∧
      (∀ (T : TyName) (tyArgs : List Ty) (root : Expr),
        IsValue root →
        TypeOfElabHM ⟨[], ctors⟩ root (.customTy T tyArgs) →
        (∀ p ∈ brs.map Prod.fst, PatternWF ctors p (.customTy T tyArgs)) →
        ∀ (i : Nat) (ws : List Expr),
          firstMatch root (brs.map Prod.fst) = some (i, ws) →
            Relation.ReflTransGen Step (.letIn none root emitInner)
              ((bodyFn bodies' i).substN 0 ws)) := by
  cases h with
  | match_ hs hb hadq =>
    exact ⟨_, _, _, rfl, hs, hb, hadq⟩

/-- From strong `SurfaceWT` of a match, the scrutinee is `SurfaceWT`. -/
theorem SurfaceWT_of_match_scrut {ctors : CtorEnv}
    {scrut : Surface.Expr} {brs : List (Surface.Pattern × Surface.Expr)}
    (hwt : SurfaceWT ctors (.match_ scrut brs)) : SurfaceWT ctors scrut := by
  obtain ⟨τ, hwt'⟩ := hwt
  cases hwt' with
  | match_ hscrut _ _ _ _ _ => exact ⟨_, hscrut⟩
  | of_lowers hnm _ _ => cases hnm


/-! ### Emit typing (Approach A rung 2 infrastructure)

Parallel to `DTreeExhaustive` / `emit_DTreeExhaustive`: a syntactic typing
layer showing `emit` of a well-formed compiled tree is `TypeOfHM`. -/

private theorem patBindTysG_gbind (ctors : CtorEnv) (τ : Ty) :
    patBindTysG ctors .gbind τ = [τ] := rfl

private theorem Ty.openVars_self_of_IsLC {τ : Ty} (h : τ.IsLC) (Xs : List Nat) :
    Ty.openVars Xs τ = τ := by
  simp only [Ty.openVars]
  exact Ty.instantiate_eq_self_of_lc h

private theorem generalisesTo_of_typeable {Γ : Env} {ctors : CtorEnv} {e : Expr} {τ : Ty}
    (h : TypeOfHM ⟨Γ, ctors⟩ e τ) :
    GeneralisesTo TypeOfHM ⟨Γ, ctors⟩ none e (PolyTy.mkTrivial τ) [] := by
  intro Xs _
  simp only [Expr.openBoundTyVars, PolyTy.openVars, PolyTy.mkTrivial,
    Ty.openVars_self_of_IsLC (TypeOfHM.regular h) Xs]
  exact h

/-- `PatternWF` computes the correct bind-type list for `norm p`. -/
theorem PatternWF_patBindTys_eq {ctors : CtorEnv} {p : Surface.Pattern} {τ : Ty}
    (_h : PatternWF ctors p τ) :
    patBindTys ctors p τ = patBindTysG ctors (norm p) τ := rfl

/-- **Emit typing context**: base env `Γ` (occurrence schemes prepended to the
    outer surface env), occurrence index map, and occurrence typing. -/
structure EmitTyCtx (ctors : CtorEnv) where
  Γ : Env
  occEnv : List Occ
  octx : OccCtx

/-- `ectx.Γ` is trivial schemes for `occEnv` (typed by `octx`) prepended to
    `Γ_outer`. This is the invariant `emit` typing maintains under switches. -/
def EmitTyCtx.agrees (ectx : EmitTyCtx ctors) (Γ_outer : Env) : Prop :=
  ∃ (τs : List Ty) (hlen : τs.length = ectx.occEnv.length),
    ectx.Γ = τs.map PolyTy.mkTrivial ++ Γ_outer ∧
    ∀ (i : Nat) (hi : i < ectx.occEnv.length),
      LookupList.get? ectx.octx (ectx.occEnv[i]) = some (τs[i]'(hlen ▸ hi)) ∧
        (τs[i]'(hlen ▸ hi)).IsLC

/-- Syntactic typing of a compiled tree under `EmitTyCtx`, indexed by the outer
    env / branch bodies / result type so leaves can carry `TypeOfHM` obligations.
    Switches extend `Γ` with instantiated field schemes (parallel to `occEnv` /
    `octx` growth). Twin of `DTreeExhaustive`, plus leaf body typing. -/
inductive DTreeTypeable (ctors : CtorEnv) (Γ_outer : Env) (bodies : Nat → Expr)
    (τres : Ty) : EmitTyCtx ctors → DTree → Prop
  | leaf {ectx : EmitTyCtx ctors} {act : Nat} {binds : List Occ} {bindTys : List Ty}
      (hag : EmitTyCtx.agrees ectx Γ_outer)
      (hlen : binds.length = bindTys.length)
      (hbnds : ∀ (i : Nat) (hi : i < binds.length),
        LookupList.get? ectx.octx (binds[i]) = some (bindTys[i]'(hlen ▸ hi)) ∧
          binds[i] ∈ ectx.occEnv)
      (hbody : TypeOfHM ⟨bindTys.map PolyTy.mkTrivial ++ Γ_outer, ctors⟩ (bodies act) τres) :
      DTreeTypeable ctors Γ_outer bodies τres ectx (.leaf act binds)
  | switchFail {ectx : EmitTyCtx ctors} {occ : Occ}
      {cases : List (CtorName × Nat × DTree)} {T : TyName} {tyArgs : List Ty}
      (hne : cases ≠ [])
      (hag : EmitTyCtx.agrees ectx Γ_outer)
      (hlook : LookupList.get? ectx.octx occ = some (.customTy T tyArgs))
      (hmem : occ ∈ ectx.occEnv)
      (hlc : ∀ ty ∈ tyArgs, ty.IsLC)
      (htyped : ∀ c a t, (c, a, t) ∈ cases →
        ∃ ctor, LookupList.get? ctors c = some ctor ∧ ctor.tyName = T ∧
          a = ctor.contents.length ∧ ctor.paramCount = tyArgs.length)
      (hsub : ∀ c a t, (c, a, t) ∈ cases →
        DTreeTypeable ctors Γ_outer bodies τres
          { Γ := (instFieldTys ctors c tyArgs).map PolyTy.mkTrivial ++ ectx.Γ
            occEnv := subOccs occ a ++ ectx.occEnv
            octx := OccCtx.extend ectx.octx occ (instFieldTys ctors c tyArgs) } t)
      (hcover : ∀ c ctor, LookupList.get? ctors c = some ctor → ctor.tyName = T →
        ∃ a t, (c, a, t) ∈ cases) :
      DTreeTypeable ctors Γ_outer bodies τres ectx (.switch occ cases .fail)
  | switchDefault {ectx : EmitTyCtx ctors} {occ : Occ}
      {cases : List (CtorName × Nat × DTree)} {dflt : DTree} {T : TyName} {tyArgs : List Ty}
      (hdne : dflt ≠ .fail)
      (hag : EmitTyCtx.agrees ectx Γ_outer)
      (hlook : LookupList.get? ectx.octx occ = some (.customTy T tyArgs))
      (hmem : occ ∈ ectx.occEnv)
      (hlc : ∀ ty ∈ tyArgs, ty.IsLC)
      (htyped : ∀ c a t, (c, a, t) ∈ cases →
        ∃ ctor, LookupList.get? ctors c = some ctor ∧ ctor.tyName = T ∧
          a = ctor.contents.length ∧ ctor.paramCount = tyArgs.length)
      (hsub : ∀ c a t, (c, a, t) ∈ cases →
        DTreeTypeable ctors Γ_outer bodies τres
          { Γ := (instFieldTys ctors c tyArgs).map PolyTy.mkTrivial ++ ectx.Γ
            occEnv := subOccs occ a ++ ectx.occEnv
            octx := OccCtx.extend ectx.octx occ (instFieldTys ctors c tyArgs) } t)
      (hdflt : DTreeTypeable ctors Γ_outer bodies τres ectx dflt) :
      DTreeTypeable ctors Γ_outer bodies τres ectx (.switch occ cases dflt)

/-- `resolveOcc` is a monomorphic var: `Γ_env` is parallel to `env`, and the
    occurrence's scheme is `mkTrivial τ`. -/
theorem resolveOcc_typeable {ctors : CtorEnv} {Γ_env Γ_outer : Env}
    {env : List Occ} {occ : Occ} {τ : Ty}
    (hlen : Γ_env.length = env.length)
    (hmem : occ ∈ env)
    (hlook : Γ_env[env.idxOf occ]? = some (PolyTy.mkTrivial τ))
    (hlc : τ.IsLC) :
    TypeOfHM ⟨Γ_env ++ Γ_outer, ctors⟩ (resolveOcc env occ) τ := by
  simp only [resolveOcc]
  refine TypeOfHM.var (polyTy := PolyTy.mkTrivial τ) (instArgs := []) ?_
    (fun _ h => (List.not_mem_nil h).elim) (InstantiatesBy.refl_of_closed hlc)
  have hlt : env.idxOf occ < Γ_env.length := by
    rw [hlen]; exact List.idxOf_lt_length_of_mem hmem
  rw [List.getElem?_append_left hlt]
  exact hlook

/-- Under `doneTys ++ Γ_env ++ Γ_outer` with `doneTys.length = depth`, the RHS
    `var (env.idxOf b + depth)` types at `τ` when `Γ_env` holds `mkTrivial τ`
    at `env.idxOf b`. -/
private theorem emitLets_rhs_typeable {ctors : CtorEnv} {Γ_env Γ_outer doneTys : Env}
    {env : List Occ} {b : Occ} {τ : Ty} {depth : Nat}
    (hlen : Γ_env.length = env.length)
    (hdepth : doneTys.length = depth)
    (hmem : b ∈ env)
    (hlook : Γ_env[env.idxOf b]? = some (PolyTy.mkTrivial τ))
    (hlc : τ.IsLC) :
    TypeOfHM ⟨doneTys ++ Γ_env ++ Γ_outer, ctors⟩
      (.var (env.idxOf b + depth) []) τ := by
  refine TypeOfHM.var (polyTy := PolyTy.mkTrivial τ) (instArgs := []) ?_
    (fun _ h => (List.not_mem_nil h).elim) (InstantiatesBy.refl_of_closed hlc)
  have hlt : env.idxOf b < Γ_env.length := by
    rw [hlen]; exact List.idxOf_lt_length_of_mem hmem
  have hge : doneTys.length ≤ env.idxOf b + depth := by omega
  rw [show doneTys ++ Γ_env ++ Γ_outer = doneTys ++ (Γ_env ++ Γ_outer) from List.append_assoc _ _ _]
  rw [List.getElem?_append_right hge]
  rw [show env.idxOf b + depth - doneTys.length = env.idxOf b from by omega]
  rw [List.getElem?_append_left hlt]
  exact hlook

/-- **Leaf-let cascade typing.** If `body` types under capture schemes
    `bindTys` prepended to `Γ_outer`, and each capture `binds[i]` looks up in
    the occurrence env segment `Γ_env` at `mkTrivial bindTys[i]`, then
    `emitLets` types under `Γ_env ++ Γ_outer`.

    Proof: `emitLets.go` induction on remaining reversed captures; base case is
    `TypeOfHM.weaken_env` for `shiftFrom binds.length env.length`; step is
    unannotated monomorphic `letIn`. -/
theorem emitLets_typeable {ctors : CtorEnv} {Γ_env Γ_outer : Env}
    {env binds : List Occ} {bindTys : List Ty} {body : Expr} {τ : Ty}
    (hlen_env : Γ_env.length = env.length)
    (hlen_binds : binds.length = bindTys.length)
    (hbound : ∀ o ∈ binds, o ∈ env)
    (hbind_look : ∀ (i : Nat) (hi : i < binds.length),
      Γ_env[env.idxOf (binds[i])]? = some (PolyTy.mkTrivial (bindTys[i]'(hlen_binds ▸ hi))) ∧
        (bindTys[i]'(hlen_binds ▸ hi)).IsLC)
    (hbody : TypeOfHM ⟨bindTys.map PolyTy.mkTrivial ++ Γ_outer, ctors⟩ body τ) :
    TypeOfHM ⟨Γ_env ++ Γ_outer, ctors⟩ (emitLets env binds body) τ := by
  unfold emitLets
  have go_ty : ∀ (rem : List Occ) (k : Nat),
      k + rem.length = binds.length →
      rem = binds.reverse.drop k →
      TypeOfHM
        ⟨(bindTys.drop rem.length).map PolyTy.mkTrivial ++ Γ_env ++ Γ_outer, ctors⟩
        (emitLets.go env binds body rem k) τ := by
    intro rem k hsum hrem
    induction rem generalizing k with
    | nil =>
      simp only [List.length_nil, List.drop_zero, emitLets.go] at hsum ⊢
      subst hsum
      have hw := TypeOfHM.weaken_env (env_pre := bindTys.map PolyTy.mkTrivial)
        (env_extra := Γ_env) (env := Γ_outer) hbody
      simpa only [List.length_map, hlen_binds, hlen_env, List.append_assoc] using hw
    | cons b rest ih =>
      simp only [emitLets.go]
      have hsum' : k + 1 + rest.length = binds.length := by
        simp only [List.length_cons] at hsum; omega
      have hrest : rest = binds.reverse.drop (k + 1) := by
        have ht := congrArg List.tail hrem
        simpa only [List.tail_cons, List.tail_drop] using ht
      have hi : rest.length < bindTys.length := by
        simp only [List.length_cons] at hsum; omega
      have hb_eq : binds[rest.length]'(by omega) = b := by
        have hklt : k < binds.reverse.length := by
          simp only [List.length_reverse]; omega
        have hget : binds.reverse[k] = b := by
          have hpos : 0 < (binds.reverse.drop k).length := by
            rw [← hrem]; simp
          have : (binds.reverse.drop k)[0]'hpos = b := by
            simp only [← hrem, List.getElem_cons_zero]
          rwa [List.getElem_drop] at this
        rw [← hget, List.getElem_reverse hklt]
        congr 1; omega
      obtain ⟨hlookb, hlcb⟩ := hbind_look rest.length (by omega)
      rw [hb_eq] at hlookb
      set τb : Ty := bindTys[rest.length]'hi with hτb
      have hdrop_cons :
          bindTys.drop rest.length =
            τb :: bindTys.drop (rest.length + 1) := by
        simp only [τb, List.drop_eq_getElem_cons hi]
      have hih := ih (k + 1) hsum' hrest
      have hrhs : TypeOfHM
          ⟨(bindTys.drop (rest.length + 1)).map PolyTy.mkTrivial ++ Γ_env ++ Γ_outer,
            ctors⟩
          (.var (env.idxOf b + k) []) τb := by
        refine emitLets_rhs_typeable (doneTys :=
            (bindTys.drop (rest.length + 1)).map PolyTy.mkTrivial)
          hlen_env ?_ (hbound b (by
            have : b ∈ binds.reverse.drop k := by rw [← hrem]; exact List.mem_cons_self
            exact List.mem_reverse.mp (List.mem_of_mem_drop this)))
          hlookb hlcb
        simp only [List.length_map, List.length_drop]
        omega
      refine TypeOfHM.letIn (M := PolyTy.mkTrivial τb) (L := []) hlcb
        (fun _ h => nomatch h) (generalisesTo_of_typeable hrhs) rfl ?_
      -- body under τb :: drop (rest+1) = drop rest, which is hih after rewriting rem length
      have hih' : TypeOfHM
          ⟨(τb :: bindTys.drop (rest.length + 1)).map PolyTy.mkTrivial ++ Γ_env ++ Γ_outer,
            ctors⟩
          (emitLets.go env binds body rest (k + 1)) τ := by
        convert hih using 2
        rw [← hdrop_cons]
      simpa only [List.map_cons, List.cons_append, List.length_cons] using hih'
  have hgo := go_ty binds.reverse 0 (by simp [List.length_reverse]) (by simp [List.drop_zero])
  simpa only [List.length_reverse, hlen_binds, List.drop_length, List.map_nil,
    List.nil_append] using hgo

/-- From `agrees`, the occurrence-env prefix of `Γ` looks up like `octx`. -/
private theorem EmitTyCtx.agrees_lookup {ctors : CtorEnv} {ectx : EmitTyCtx ctors}
    {Γ_outer : Env} {occ : Occ} {τ : Ty}
    (hag : EmitTyCtx.agrees ectx Γ_outer)
    (hmem : occ ∈ ectx.occEnv)
    (hτ : LookupList.get? ectx.octx occ = some τ) :
    ∃ Γ_env, Γ_env.length = ectx.occEnv.length ∧
      ectx.Γ = Γ_env ++ Γ_outer ∧
      Γ_env[ectx.occEnv.idxOf occ]? = some (PolyTy.mkTrivial τ) ∧ τ.IsLC := by
  obtain ⟨τs, hlen, hΓ, hlook⟩ := hag
  refine ⟨τs.map PolyTy.mkTrivial, ?_, hΓ, ?_, ?_⟩
  · simp [hlen]
  · have hi : ectx.occEnv.idxOf occ < ectx.occEnv.length :=
      List.idxOf_lt_length_of_mem hmem
    have ⟨hτ', hlc⟩ := hlook (ectx.occEnv.idxOf occ) hi
    have hocceq : ectx.occEnv[ectx.occEnv.idxOf occ] = occ := List.getElem_idxOf hi
    rw [hocceq] at hτ'
    have hτs : τs[ectx.occEnv.idxOf occ]'(hlen ▸ hi) = τ :=
      Option.some.inj (hτ'.symm.trans hτ)
    rw [List.getElem?_map, List.getElem?_eq_getElem (by omega)]
    simp only [hτs, Option.map_some]
  · have hi : ectx.occEnv.idxOf occ < ectx.occEnv.length :=
      List.idxOf_lt_length_of_mem hmem
    have ⟨hτ', hlc⟩ := hlook (ectx.occEnv.idxOf occ) hi
    have hocceq : ectx.occEnv[ectx.occEnv.idxOf occ] = occ := List.getElem_idxOf hi
    rw [hocceq] at hτ'
    have hτs : τs[ectx.occEnv.idxOf occ]'(hlen ▸ hi) = τ :=
      Option.some.inj (hτ'.symm.trans hτ)
    simpa [hτs] using hlc

/-- `emitCases` as a `List.map` (local copy — private below §O5). -/
private theorem emitCases_eq_map' (env : List Occ) (bodies : Nat → Expr) (occ : Occ) :
    ∀ (cases : List (CtorName × Nat × DTree)),
      emitCases env bodies occ cases
        = cases.map (fun x => (MatchPattern.named x.1 x.2.1,
            emit (subOccs occ x.2.1 ++ env) bodies x.2.2))
  | [] => rfl
  | (_c, _a, _t) :: rest => by
    rw [emitCases, emitCases_eq_map' env bodies occ rest, List.map_cons]

/-- Branches in `emitCases` are always named patterns. -/
private theorem emitCases_named_mem (env : List Occ) (bodies : Nat → Expr) (occ : Occ)
    {cases : List (CtorName × Nat × DTree)} {pat : MatchPattern} {body : Expr}
    (h : (pat, body) ∈ emitCases env bodies occ cases) :
    ∃ c n, pat = .named c n := by
  rw [emitCases_eq_map'] at h
  obtain ⟨_, _, heq⟩ := List.mem_map.mp h
  obtain ⟨rfl, rfl⟩ := (Prod.mk.injEq _ _ _ _).mp heq
  exact ⟨_, _, rfl⟩

private theorem emitCases_ne_nil (env : List Occ) (bodies : Nat → Expr) (occ : Occ)
    {cases : List (CtorName × Nat × DTree)} (hne : cases ≠ []) :
    emitCases env bodies occ cases ≠ [] := by
  cases cases with
  | nil => exact (hne rfl).elim
  | cons _ _ => simp [emitCases]

/-- `List.Forall₂` for a pointwise map (local copy of InferW's private lemma). -/
private theorem List.forall₂_self_map {α β} {R : α → β → Prop} {f : α → β} :
    ∀ {l : List α}, (∀ x ∈ l, R x (f x)) → List.Forall₂ R l (l.map f)
  | [], _ => .nil
  | _ :: _, h =>
    .cons (h _ (List.mem_cons_self ..))
      (List.forall₂_self_map (fun x hx => h x (List.mem_cons_of_mem _ hx)))

/-- `instFieldTys` instantiates ctor field types via `InstantiatesBy`. -/
private theorem instFieldTys_forall₂ {ctors : CtorEnv} {c : CtorName} {tyArgs : List Ty}
    {ctor : Ctor} (hlook : LookupList.get? ctors c = some ctor)
    (hpc : ctor.paramCount = tyArgs.length) :
    List.Forall₂ (InstantiatesBy tyArgs) ctor.contents (instFieldTys ctors c tyArgs) := by
  unfold instFieldTys
  simp only [hlook, Option.map_some, Option.getD]
  exact List.forall₂_self_map (fun c0 hc0 =>
    InstantiatesBy.openWith (ctor.bound c0 hc0) (Nat.le_of_eq hpc))

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

/-- **(Typing A-core, FROZEN).** Emitting a `DTreeTypeable` tree yields a
    `TypeOfHM` term at `τres`. Mirror of `emit_DTreeExhaustive`. -/
theorem emit_DTreeTypeable {ctors : CtorEnv} {Γ_outer : Env} {ectx : EmitTyCtx ctors}
    {t : DTree} {bodies : Nat → Expr} {τres : Ty}
    (hdt : DTreeTypeable ctors Γ_outer bodies τres ectx t) :
    TypeOfHM ⟨ectx.Γ, ctors⟩ (emit ectx.occEnv bodies t) τres := by
  induction hdt with
  | @leaf ectx act binds bindTys hag hlen hbnds hbody =>
    obtain ⟨τs, hlen_occ, hΓ, hlook_agrees⟩ := hag
    set Γ_env := τs.map PolyTy.mkTrivial
    have hlen_env : Γ_env.length = ectx.occEnv.length := by simp [Γ_env, hlen_occ]
    have hbound : ∀ o ∈ binds, o ∈ ectx.occEnv := fun o ho => by
      have hi := List.idxOf_lt_length_of_mem ho
      have hmem := (hbnds _ hi).2
      simpa [List.getElem_idxOf hi] using hmem
    have hbind_look : ∀ (i : Nat) (hi : i < binds.length),
        Γ_env[ectx.occEnv.idxOf (binds[i])]? = some (PolyTy.mkTrivial (bindTys[i]'(hlen ▸ hi))) ∧
          (bindTys[i]'(hlen ▸ hi)).IsLC := by
      intro i hi
      have ⟨hτ, hmem⟩ := hbnds i hi
      have hi' : ectx.occEnv.idxOf (binds[i]) < ectx.occEnv.length :=
        List.idxOf_lt_length_of_mem hmem
      have ⟨hτ_octx, hlc⟩ := hlook_agrees (ectx.occEnv.idxOf (binds[i])) hi'
      have hocceq : ectx.occEnv[ectx.occEnv.idxOf (binds[i])] = binds[i] :=
        List.getElem_idxOf hi'
      rw [hocceq] at hτ_octx
      have hτs : τs[ectx.occEnv.idxOf (binds[i])]'(hlen_occ ▸ hi') = bindTys[i]'(hlen ▸ hi) :=
        Option.some.inj (hτ_octx.symm.trans hτ)
      constructor
      · rw [List.getElem?_map, List.getElem?_eq_getElem (by omega)]
        simp only [hτs, Option.map_some]
      · simpa [hτs] using hlc
    have ht := emitLets_typeable (env := ectx.occEnv) (Γ_env := Γ_env)
      hlen_env hlen hbound hbind_look hbody
    simpa only [emit, Γ_env, hΓ] using ht
  | @switchFail ectx occ cases T tyArgs hne hag hlook hmem hlc htyped hsub hcover ih =>
    simp only [emit]
    obtain ⟨Γ_env, hlen_env, hΓ, hlook', hlc_scrut⟩ :=
      EmitTyCtx.agrees_lookup hag hmem hlook
    have hscrut : TypeOfHM ⟨ectx.Γ, ctors⟩ (resolveOcc ectx.occEnv occ) (.customTy T tyArgs) :=
      hΓ ▸ resolveOcc_typeable hlen_env hmem hlook' hlc_scrut
    have hbrs_ne := emitCases_ne_nil ectx.occEnv bodies occ hne
    change TypeOfHM ⟨ectx.Γ, ctors⟩
      (.match_ (resolveOcc ectx.occEnv occ) (emitCases ectx.occEnv bodies occ cases ++ [])) τres
    rw [List.append_nil]
    refine TypeOfHM.match_ hscrut hbrs_ne ?_
    intro branch hmem
    obtain ⟨pat, body⟩ := branch
    cases pat with
    | named c n =>
      obtain ⟨t, ht, rfl⟩ := mem_cases_of_mem_emitCases ectx.occEnv bodies occ hmem
      obtain ⟨ctor, hctor, hty, ha, hpc⟩ := htyped _ _ _ ht
      have hfields : List.Forall₂ (InstantiatesBy tyArgs) ctor.contents
          (instFieldTys ctors _ tyArgs) :=
        instFieldTys_forall₂ hctor hpc
      refine TypeOfMatchBranch.mk
        ⟨hctor, (by rw [hty]), hpc, ha, hfields⟩ rfl ?_
      exact ih c n t ht
    | wildcard =>
      rcases emitCases_named_mem ectx.occEnv bodies occ hmem with ⟨_, _, hnom⟩
      cases hnom
  | @switchDefault ectx occ cases dflt T tyArgs hdne hag hlook hmem hlc htyped hsub hdflt ih_sub ih_dflt =>
    obtain ⟨Γ_env, hlen_env, hΓ, hlook', hlc_scrut⟩ :=
      EmitTyCtx.agrees_lookup hag hmem hlook
    have hscrut : TypeOfHM ⟨ectx.Γ, ctors⟩ (resolveOcc ectx.occEnv occ) (.customTy T tyArgs) :=
      hΓ ▸ resolveOcc_typeable hlen_env hmem hlook' hlc_scrut
    have hemit :
        emit ectx.occEnv bodies (.switch occ cases dflt) =
          .match_ (resolveOcc ectx.occEnv occ)
            (emitCases ectx.occEnv bodies occ cases ++
              [(.wildcard, emit ectx.occEnv bodies dflt)]) := by
      cases dflt with
      | fail => exact (hdne rfl).elim
      | leaf | switch => rfl
    rw [hemit]
    have hbrs_ne : emitCases ectx.occEnv bodies occ cases ++
        [(.wildcard, emit ectx.occEnv bodies dflt)] ≠ [] := by
      intro h
      rcases List.append_eq_nil_iff.mp h with ⟨_, hnil⟩
      cases hnil
    refine TypeOfHM.match_ hscrut hbrs_ne ?_
    intro branch hmem
    obtain ⟨pat, body⟩ := branch
    simp only [List.mem_append, List.mem_singleton] at hmem
    rcases hmem with hmem | hmem
    · cases pat with
      | named c n =>
        obtain ⟨t, ht, rfl⟩ := mem_cases_of_mem_emitCases ectx.occEnv bodies occ hmem
        obtain ⟨ctor, hctor, hty, ha, hpc⟩ := htyped _ _ _ ht
        have hfields : List.Forall₂ (InstantiatesBy tyArgs) ctor.contents
            (instFieldTys ctors _ tyArgs) :=
          instFieldTys_forall₂ hctor hpc
        refine TypeOfMatchBranch.mk
          ⟨hctor, (by rw [hty]), hpc, ha, hfields⟩ rfl ?_
        exact ih_sub c n t ht
      | wildcard =>
        rcases emitCases_named_mem ectx.occEnv bodies occ hmem with ⟨_, _, hnom⟩
        cases hnom
    · cases pat with
      | wildcard =>
        obtain ⟨rfl, rfl⟩ := hmem
        exact TypeOfMatchBranch.wildcard ih_dflt
      | named c n =>
        rcases hmem with ⟨rfl, _⟩

/-! ### `compile_initMatrix_typeable` infrastructure

Private WF helpers (copied from `PatComp` — originals are `private` there). -/

private def compile_GPatWFList_forall₂ {ctors : CtorEnv} {l t} :
    GPatWFList ctors l t → List.Forall₂ (GPatWF ctors) l t
  | .nil => .nil
  | .cons hp htl => .cons hp (compile_GPatWFList_forall₂ htl)

private theorem compile_GPatWFList_of_forall₂ {ctors : CtorEnv} :
    ∀ {l t}, List.Forall₂ (GPatWF ctors) l t → GPatWFList ctors l t
  | _, _, .nil => .nil
  | _, _, .cons hp htl => .cons hp (compile_GPatWFList_of_forall₂ htl)

private theorem compile_Forall₂_append {α β : Type _} (R : α → β → Prop) {l1 t1 l2 t2}
    (h1 : List.Forall₂ R l1 t1) (h2 : List.Forall₂ R l2 t2) :
    List.Forall₂ R (l1 ++ l2) (t1 ++ t2) := by
  induction h1 with
  | nil => simp only [List.nil_append]; exact h2
  | cons hp hps ih => simp only [List.cons_append]; exact .cons hp ih

private theorem compile_GPatWFList_append {ctors : CtorEnv} {l1 t1 l2 t2}
    (h1 : GPatWFList ctors l1 t1) (h2 : GPatWFList ctors l2 t2) :
    GPatWFList ctors (l1 ++ l2) (t1 ++ t2) :=
  compile_GPatWFList_of_forall₂
    (compile_Forall₂_append _ (compile_GPatWFList_forall₂ h1) (compile_GPatWFList_forall₂ h2))

private theorem compile_GPatWFList_length {ctors : CtorEnv} {l t} (h : GPatWFList ctors l t) :
    l.length = t.length := by
  match h with
  | .nil => rfl
  | .cons _ htl => simp [compile_GPatWFList_length htl]

private theorem compile_GPatWF.gctor_inv {ctors : CtorEnv} {c : CtorName} {cargs : List GPat} {τ : Ty}
    (h : GPatWF ctors (.gctor c cargs) τ) :
    ∃ T tyArgs ctor fieldTys, τ = .customTy T tyArgs ∧ LookupList.get? ctors c = some ctor ∧
      ctor.tyName = T ∧ List.Forall₂ (InstantiatesBy tyArgs) ctor.contents fieldTys ∧
      GPatWFList ctors cargs fieldTys := by
  cases h with
  | gctor hlook hname hinst hwfargs => exact ⟨_, _, _, _, rfl, hlook, hname, hinst, hwfargs⟩

private theorem compile_GPatWFList_replicate_gwild {ctors : CtorEnv} :
    ∀ (n : Nat) (tys : List Ty), tys.length = n →
      GPatWFList ctors (List.replicate n GPat.gwild) tys
  | 0, [], _ => .nil
  | 0, _ :: _, h => by simp at h
  | n + 1, [], h => by simp at h
  | n + 1, τ :: τs, h => by
    rw [List.length_cons] at h
    simp only [List.replicate_succ]
    exact .cons .gwild (compile_GPatWFList_replicate_gwild n τs (by omega))

private theorem compile_InstantiatesBy_forall2_det_agree {tyArgs1 tyArgs2 : List Ty} {n : Nat}
    (hag : ∀ k, k < n → tyArgs1[k]? = tyArgs2[k]?)
    {tys l1 l2 : List Ty}
    (hbound : ∀ c ∈ tys, ContainsBvarsUpTo n c)
    (h1 : List.Forall₂ (InstantiatesBy tyArgs1) tys l1)
    (h2 : List.Forall₂ (InstantiatesBy tyArgs2) tys l2) : l1 = l2 := by
  induction h1 generalizing l2 with
  | nil => cases h2; rfl
  | cons hi1 h1tl ih =>
    cases h2 with
    | cons hi2 h2tl =>
      have hhd := InstantiatesBy.det_agree hag (hbound _ List.mem_cons_self) hi1 hi2
      rw [hhd, ih (fun c hc => hbound c (List.mem_cons_of_mem _ hc)) h2tl]

private theorem compile_defaultRow_wf {ctors : CtorEnv} {occ0 : Occ} {τ0 : Ty} {ttys : List Ty}
    {r r' : Row} (hwf : GPatWFList ctors r.pats (τ0 :: ttys))
    (hs : defaultRow occ0 r = some r') :
    GPatWFList ctors r'.pats ttys := by
  obtain ⟨captured, pats, act⟩ := r
  cases pats with
  | nil => simp [defaultRow] at hs
  | cons p prest =>
    cases p with
    | gctor c cargs => simp [defaultRow] at hs
    | gbind =>
      simp only [defaultRow, Option.some.injEq] at hs
      subst hs
      cases hwf with | cons _ htl => exact htl
    | gwild =>
      simp only [defaultRow, Option.some.injEq] at hs
      subst hs
      cases hwf with | cons _ htl => exact htl

private theorem compile_specializeRow_wf {ctors : CtorEnv} {c : CtorName} {arity : Nat} {occ0 : Occ}
    {T : TyName} {tyArgs : List Ty} {ctor : Ctor} {fieldTys ttys : List Ty} {r r' : Row}
    (hlook : LookupList.get? ctors c = some ctor)
    (hinst : List.Forall₂ (InstantiatesBy tyArgs) ctor.contents fieldTys)
    (hlen : fieldTys.length = arity)
    (hwf : GPatWFList ctors r.pats (.customTy T tyArgs :: ttys))
    (hs : specializeRow c arity occ0 r = some r') :
    GPatWFList ctors r'.pats (fieldTys ++ ttys) := by
  obtain ⟨captured, pats, act⟩ := r
  cases pats with
  | nil => simp [specializeRow] at hs
  | cons p prest =>
    cases p with
    | gctor c' cargs =>
      by_cases hcond : c' = c ∧ cargs.length = arity
      · simp only [specializeRow, if_pos hcond, Option.some.injEq] at hs
        subst hs
        cases hwf with
        | cons hwf_hd hwf_tl =>
          obtain ⟨hc', _⟩ := hcond
          rw [hc'] at hwf_hd
          cases hwf_hd with
          | gctor hlook' hname' hinst' hwfargs =>
            rw [hlook'] at hlook
            injection hlook with hceq
            rw [hceq] at hinst' hname'
            have hdet := compile_InstantiatesBy_forall2_det_agree (fun _ _ => rfl) ctor.bound hinst' hinst
            rw [hdet] at hwfargs
            exact compile_GPatWFList_append hwfargs hwf_tl
      · simp only [specializeRow, if_neg hcond] at hs
        simp at hs
    | gbind =>
      simp only [specializeRow, Option.some.injEq] at hs
      subst hs
      cases hwf with
      | cons _ hwf_tl =>
        exact compile_GPatWFList_append
          (compile_GPatWFList_replicate_gwild arity fieldTys hlen) hwf_tl
    | gwild =>
      simp only [specializeRow, Option.some.injEq] at hs
      subst hs
      cases hwf with
      | cons _ hwf_tl =>
        exact compile_GPatWFList_append
          (compile_GPatWFList_replicate_gwild arity fieldTys hlen) hwf_tl

private theorem compile_colHeads_mem_witness (M : Matrix) (c : CtorName) (arity : Nat)
    (h : (c, arity) ∈ colHeads M) :
    ∃ r ∈ M, ∃ args rest, r.pats = GPat.gctor c args :: rest ∧ args.length = arity := by
  simp only [colHeads, List.mem_dedup, List.mem_filterMap] at h
  obtain ⟨r, hrmem, hgr⟩ := h
  refine ⟨r, hrmem, ?_⟩
  cases hpats : r.pats with
  | nil => rw [hpats] at hgr; simp at hgr
  | cons q t =>
      cases q with
      | gctor c' cargs =>
          rw [hpats] at hgr
          simp [GPat.headCtor] at hgr
          obtain ⟨rfl, ha⟩ := hgr
          exact ⟨cargs, t, rfl, ha⟩
      | gbind => rw [hpats] at hgr; simp [GPat.headCtor] at hgr
      | gwild => rw [hpats] at hgr; simp [GPat.headCtor] at hgr

private theorem compile_defaultRow_captured_sub {occ0 : Occ} {r r' : Row}
    (hs : defaultRow occ0 r = some r') :
    ∀ o ∈ r'.captured, o ∈ r.captured ∨ o = occ0 := by
  obtain ⟨captured, pats, act⟩ := r
  cases pats with
  | nil => simp [defaultRow] at hs
  | cons p prest =>
    cases p with
    | gctor _ _ => simp [defaultRow] at hs
    | gbind =>
      simp only [defaultRow, Option.some.injEq] at hs
      subst hs
      intro o ho
      simpa using ho
    | gwild =>
      simp only [defaultRow, Option.some.injEq] at hs
      subst hs
      intro o ho
      exact Or.inl ho

private theorem compile_specializeRow_captured_sub {c : CtorName} {a : Nat} {occ0 : Occ}
    {r r' : Row} (hs : specializeRow c a occ0 r = some r') :
    ∀ o ∈ r'.captured, o ∈ r.captured ∨ o = occ0 := by
  obtain ⟨captured, pats, act⟩ := r
  cases pats with
  | nil => simp [specializeRow] at hs
  | cons p prest =>
    cases p with
    | gctor c' args =>
      simp only [specializeRow] at hs
      split_ifs at hs
      simp only [Option.some.injEq] at hs
      subst hs
      intro o ho
      exact Or.inl ho
    | gbind =>
      simp only [specializeRow, Option.some.injEq] at hs
      subst hs
      intro o ho
      simpa using ho
    | gwild =>
      simp only [specializeRow, Option.some.injEq] at hs
      subst hs
      intro o ho
      exact Or.inl ho

private theorem DTreeExhaustive_not_fail {ctors : CtorEnv} {octx : OccCtx} :
    ¬ DTreeExhaustive ctors octx DTree.fail := by intro h; cases h

/-- Bind types for a matrix row: captured occurrence types (from `octx`) plus
    pattern binders from residual columns. -/
private def captureBindTys (octx : OccCtx) (captured : List Occ) : List Ty :=
  captured.map (fun o => (LookupList.get? octx o).getD (.prim .unit))

private def rowBindTys (ctors : CtorEnv) (octx : OccCtx) (captured : List Occ)
    (pats : List GPat) (tys : List Ty) : List Ty :=
  captureBindTys octx captured ++ patBindTysGList ctors pats tys

private theorem patBindTysGList_cons {ctors : CtorEnv} {p ps τ τs} :
    patBindTysGList ctors (p :: ps) (τ :: τs) =
      patBindTysG ctors p τ ++ patBindTysGList ctors ps τs := rfl

private theorem patBindTysGList_append {ctors : CtorEnv} {l1 l2 t1 t2}
    (hlen : l1.length = t1.length) :
    patBindTysGList ctors (l1 ++ l2) (t1 ++ t2) =
      patBindTysGList ctors l1 t1 ++ patBindTysGList ctors l2 t2 := by
  revert t1
  induction l1 <;> intro t1 hlen <;> cases t1 <;> simp_all [patBindTysGList]

private theorem captureBindTys_snoc {octx : OccCtx} {xs : List Occ} {o : Occ} {τ : Ty}
    (hτ : LookupList.get? octx o = some τ) :
    captureBindTys octx (xs ++ [o]) = captureBindTys octx xs ++ [τ] := by
  simp only [captureBindTys, List.map_append, List.map_cons, hτ, Option.getD_some]
  rfl

private theorem rowBindTys_defaultRow_gbind {ctors : CtorEnv} {octx : OccCtx}
    {occ0 : Occ} {captured pats : List _} {τ0 : Ty} {ttys : List Ty}
    (hlook : LookupList.get? octx occ0 = some τ0) :
    rowBindTys ctors octx (captured ++ [occ0]) pats ttys =
      rowBindTys ctors octx captured (.gbind :: pats) (τ0 :: ttys) := by
  simp only [rowBindTys, captureBindTys_snoc hlook, patBindTysGList_cons, patBindTysG_gbind,
    List.append_assoc]

private theorem rowBindTys_defaultRow_gwild {ctors : CtorEnv} {octx : OccCtx}
    {captured pats : List _} {τ0 : Ty} {ttys : List Ty} :
    rowBindTys ctors octx captured pats ttys =
      rowBindTys ctors octx captured (.gwild :: pats) (τ0 :: ttys) := by
  ac_rfl

private theorem patBindTysG_gctor {ctors : CtorEnv} {c : CtorName} {args : List GPat} {τ : Ty}
    {fieldTys : List Ty} (hfield : patGctorFieldTys ctors c τ = some fieldTys) :
    patBindTysG ctors (.gctor c args) τ = patBindTysGList ctors args fieldTys := by
  simp only [patBindTysG, hfield]

private theorem rowBindTys_gctor_cons {ctors : CtorEnv} {octx : OccCtx}
    {captured : List Occ} {args rest : List GPat} {c : CtorName} {τ : Ty} {ttys : List Ty}
    {fieldTys : List Ty}
    (hfield : patGctorFieldTys ctors c τ = some fieldTys)
    (hlen : args.length = fieldTys.length) :
    rowBindTys ctors octx captured (.gctor c args :: rest) (τ :: ttys) =
      rowBindTys ctors octx captured (args ++ rest) (fieldTys ++ ttys) := by
  simp only [rowBindTys, patBindTysGList_cons, patBindTysG_gctor hfield]
  rw [patBindTysGList_append hlen]

private theorem defaultRow_body_inv {ctors : CtorEnv} {octx : OccCtx} {Γ_outer : Env}
    {τres : Ty} {occ0 : Occ} {τ0 : Ty} {ttys : List Ty} {bodies : Nat → Expr}
    {r r' : Row}
    (hlook : LookupList.get? octx occ0 = some τ0)
    (hs : defaultRow occ0 r = some r')
    (hbody : TypeOfHM
      ⟨(rowBindTys ctors octx r.captured r.pats (τ0 :: ttys)).map PolyTy.mkTrivial ++ Γ_outer,
        ctors⟩
      (bodies r.act) τres) :
    TypeOfHM
      ⟨(rowBindTys ctors octx r'.captured r'.pats ttys).map PolyTy.mkTrivial ++ Γ_outer, ctors⟩
      (bodies r'.act) τres := by
  obtain ⟨captured, pats, act⟩ := r
  cases pats with
  | nil => simp [defaultRow] at hs
  | cons p prest =>
    cases p with
    | gctor _ _ => simp [defaultRow] at hs
    | gbind =>
      simp only [defaultRow, Option.some.injEq] at hs
      subst hs
      simpa [rowBindTys_defaultRow_gbind hlook] using hbody
    | gwild =>
      simp only [defaultRow, Option.some.injEq] at hs
      subst hs
      simpa [rowBindTys_defaultRow_gwild] using hbody

private theorem specializeRow_body_inv_gctor {ctors : CtorEnv} {octx : OccCtx} {Γ_outer : Env}
    {τres : Ty} {occ0 : Occ} {c : CtorName} {τ : Ty} {ttys : List Ty} {bodies : Nat → Expr}
    {r r' : Row} {args rest : List GPat} {fieldTys : List Ty}
    (hfield : patGctorFieldTys ctors c τ = some fieldTys)
    (hs : specializeRow c args.length occ0 r = some r')
    (hpats : r.pats = .gctor c args :: rest)
    (hlen : args.length = fieldTys.length)
    (hbody : TypeOfHM
      ⟨(rowBindTys ctors octx r.captured r.pats (τ :: ttys)).map PolyTy.mkTrivial ++ Γ_outer,
        ctors⟩
      (bodies r.act) τres) :
    TypeOfHM
      ⟨(rowBindTys ctors octx r'.captured r'.pats (fieldTys ++ ttys)).map PolyTy.mkTrivial ++ Γ_outer,
        ctors⟩
      (bodies r'.act) τres := by
  obtain ⟨captured, pats, act⟩ := r
  subst hpats
  simp only [specializeRow, and_self, ↓reduceIte, Option.some.injEq] at hs
  subst hs
  simpa [rowBindTys_gctor_cons hfield hlen] using hbody

private theorem patBindTysGList_replicate_gwild (ctors : CtorEnv) :
    ∀ (n : Nat) (tys : List Ty), tys.length = n →
      patBindTysGList ctors (List.replicate n .gwild) tys = []
  | 0, [], _ => rfl
  | 0, _ :: _, h => by cases h
  | n + 1, [], h => by cases h
  | n + 1, τ :: τs, h => by
    simp only [List.replicate_succ, patBindTysGList_cons, patBindTysG]
    exact patBindTysGList_replicate_gwild ctors n τs (by simpa using h)

private theorem specializeRow_body_inv_gbind {ctors : CtorEnv} {octx : OccCtx} {Γ_outer : Env}
    {τres : Ty} {occ0 : Occ} {c : CtorName} {τ0 : Ty} {ttys : List Ty} {bodies : Nat → Expr}
    {r r' : Row} {prest : List GPat} {arity : Nat}
    (hlook : LookupList.get? octx occ0 = some τ0)
    (hs : specializeRow c arity occ0 r = some r')
    (hpats : r.pats = .gbind :: prest)
    (hbody : TypeOfHM
      ⟨(rowBindTys ctors octx r.captured r.pats (τ0 :: ttys)).map PolyTy.mkTrivial ++ Γ_outer,
        ctors⟩
      (bodies r.act) τres) :
    TypeOfHM
      ⟨(rowBindTys ctors octx r'.captured r'.pats (List.replicate arity τ0 ++ ttys)).map
          PolyTy.mkTrivial ++ Γ_outer, ctors⟩
      (bodies r'.act) τres := by
  obtain ⟨captured, pats, act⟩ := r
  subst hpats
  simp only [specializeRow, Option.some.injEq] at hs
  subst hs
  have hrow :
      rowBindTys ctors octx (captured ++ [occ0]) (List.replicate arity .gwild ++ prest)
        (List.replicate arity τ0 ++ ttys) =
      rowBindTys ctors octx captured (.gbind :: prest) (τ0 :: ttys) := by
    simp only [rowBindTys, captureBindTys_snoc hlook, patBindTysGList_cons, patBindTysG_gbind]
    rw [patBindTysGList_append (by simp [List.length_replicate]),
      patBindTysGList_replicate_gwild ctors arity _ (by simp [List.length_replicate])]
    simp [List.append_assoc]
  simpa [hrow] using hbody

private theorem bodyFn_get {bodies' : List Expr} {i : Nat} (hi : i < bodies'.length) :
    bodyFn bodies' i = bodies'[i]'hi := by
  simp [bodyFn, List.getElem?_eq_getElem hi]

private theorem initMatrix_row {ps : List Surface.Pattern} {k : Nat} {p : Surface.Pattern}
    (hp : p ∈ ps) :
    ∃ r ∈ initMatrix ps k, r.captured = [] ∧ r.pats = [norm p] ∧
      ∃ i, r.act = k + i ∧ ps[i]? = some p := by
  induction ps generalizing k with
  | nil => cases hp
  | cons q qs ih =>
    simp only [List.mem_cons] at hp
    rcases hp with rfl | hp
    · refine ⟨{ captured := [], pats := [norm p], act := k }, ?_, rfl, rfl, 0, by simp⟩
      simp [initMatrix]
    · obtain ⟨r, hr, hcap, hpats, i, hact, hget⟩ := ih (k := k + 1) hp
      refine ⟨r, ?_, hcap, hpats, i + 1, by omega, ?_⟩
      · simp only [initMatrix, List.mem_cons]
        exact Or.inr hr
      · simpa [List.getElem?_cons_succ] using hget

private theorem initMatrix_ne_nil_of_hexh {ctors : CtorEnv} {T : TyName} {tyArgs : List Ty}
    {ps : List Surface.Pattern} (hexh : MatchExhaustive ctors T tyArgs ps) :
    ps ≠ [] := by
  intro hnil
  subst hnil
  simp only [MatchExhaustive, initMatrix, compile] at hexh
  exact DTreeExhaustive_not_fail hexh

private theorem EmitTyCtx.agrees_root (ctors : CtorEnv) {Γ_outer : Env} {τ : Ty}
    (hlc : τ.IsLC) :
    EmitTyCtx.agrees (ctors := ctors)
      { Γ := PolyTy.mkTrivial τ :: Γ_outer, occEnv := [[]],
        octx := [([], τ)] }
      Γ_outer := by
  refine ⟨[τ], by rfl, by rfl, ?_⟩
  intro i hi
  have hi0 : i = 0 := by simpa using hi
  subst hi0
  simp only [List.getElem_cons_zero, LookupList.get?]
  exact And.intro rfl hlc

/-- `get?` on a zip finds the `i`-th entry when earlier keys differ from `ks[i]`. -/
private theorem LookupList.get?_zip_getElem {α β : Type _} [DecidableEq α]
    {ks : List α} {vs : List β} (i : Nat)
    (hlen : ks.length = vs.length) (hi : i < vs.length)
    (hbefore : ∀ j : Nat, j < i →
      (hj : j < ks.length) → (hii : i < ks.length) → ks[j]'hj ≠ ks[i]'hii) :
    LookupList.get? (ks.zip vs) (ks[i]'(by omega)) = some (vs[i]'hi) := by
  induction ks generalizing vs i with
  | nil =>
    cases vs with
    | nil => cases hi
    | cons _ _ => cases hlen
  | cons k ks ih =>
    cases vs with
    | nil => cases hlen
    | cons v vs =>
      cases i with
      | zero =>
        simp only [List.zip_cons_cons, List.getElem_cons_zero, LookupList.get?, ↓reduceIte]
      | succ i =>
        simp only [List.length_cons] at hlen hi
        have hlen' : ks.length = vs.length := by omega
        have hi' : i < vs.length := by omega
        have hiks : i < ks.length := by omega
        have hne : ks[i]'hiks ≠ k :=
          (hbefore 0 (Nat.zero_lt_succ i) (Nat.zero_lt_succ _) (Nat.succ_lt_succ hiks)).symm
        simp only [List.zip_cons_cons, List.getElem_cons_succ, LookupList.get?, hne, ↓reduceIte]
        exact ih i hlen' hi' (fun j hj hji hii =>
          hbefore (j + 1) (Nat.succ_lt_succ hj) (Nat.succ_lt_succ hji) (Nat.succ_lt_succ hii))

private theorem subOccs_getElem (occ : Occ) (n i : Nat) (hi : i < n) :
    (subOccs occ n)[i]'(by simp [subOccs, List.length_map, List.length_range]; omega) =
      occ ++ [i] := by
  simp only [subOccs, List.getElem_map, List.getElem_range]

private theorem subOccs_before_ne (occ : Occ) (n i j : Nat) (hj : j < i) (hi : i < n) :
    (subOccs occ n)[j]'(by simp [subOccs]; omega) ≠
      (subOccs occ n)[i]'(by simp [subOccs]; omega) := by
  rw [subOccs_getElem occ n j (by omega), subOccs_getElem occ n i hi]
  intro h
  exact Nat.ne_of_lt hj (List.cons.inj (List.append_cancel_left h)).1

private theorem LookupList.get?_zip_eq_none {α β : Type _} [DecidableEq α]
    {ks : List α} {vs : List β} {key : α} (h : key ∉ ks) :
    LookupList.get? (ks.zip vs) key = none := by
  induction ks generalizing vs with
  | nil => simp [LookupList.get?]
  | cons k ks ih =>
    cases vs with
    | nil => simp [List.zip_nil_right, LookupList.get?]
    | cons v vs =>
      have hk : key ≠ k := fun he => h (by simp [he])
      have htl : key ∉ ks := fun hm => h (List.mem_cons_of_mem _ hm)
      simp only [List.zip_cons_cons, LookupList.get?, hk, ↓reduceIte]
      exact ih htl

private theorem LookupList.get?_append_of_left_eq_none {k v : Type} [DecidableEq k]
    {l l' : LookupList k v} {key : k} {val : v}
    (hn : LookupList.get? l key = none)
    (h : LookupList.get? l' key = some val) :
    LookupList.get? (l ++ l') key = some val := by
  induction l with
  | nil => simpa using h
  | cons hd tl ih =>
    cases hd with
    | mk k' v' =>
      by_cases hk : key = k'
      · simp only [LookupList.get?, hk, ↓reduceIte] at hn
        nomatch hn
      · simp only [List.cons_append, LookupList.get?, hk, ↓reduceIte]
        exact ih (by simpa [LookupList.get?, hk] using hn)

private theorem OccCtx.get?_extend_sub {octx : OccCtx} {occ : Occ} {fieldTys : List Ty} {i : Nat}
    (hi : i < fieldTys.length) :
    LookupList.get? (OccCtx.extend octx occ fieldTys)
      ((subOccs occ fieldTys.length)[i]'(by simp [subOccs, List.length_map, List.length_range]; omega)) =
      some (fieldTys[i]'hi) := by
  simp only [OccCtx.extend]
  have hlen : (subOccs occ fieldTys.length).length = fieldTys.length := by
    simp [subOccs]
  have hzip := LookupList.get?_zip_getElem (ks := subOccs occ fieldTys.length) (vs := fieldTys) i
    hlen hi (fun j hj _ _ => subOccs_before_ne occ fieldTys.length i j hj hi)
  exact LookupList.get?_append_left _ octx _ hzip

/-- Preserve an existing lookup across `OccCtx.extend`, provided the key is not
    among the freshly prepended field occurrences. -/
private theorem OccCtx.get?_extend_orig {octx : OccCtx} {occ : Occ} {fieldTys : List Ty}
    {o : Occ} {τ : Ty}
    (hdisj : o ∉ subOccs occ fieldTys.length)
    (h : LookupList.get? octx o = some τ) :
    LookupList.get? (OccCtx.extend octx occ fieldTys) o = some τ := by
  simp only [OccCtx.extend]
  exact LookupList.get?_append_of_left_eq_none
    (LookupList.get?_zip_eq_none hdisj) h

private theorem LookupList.get?_append_left_none {k v : Type} [DecidableEq k]
    {l l' : LookupList k v} {key : k}
    (hn : LookupList.get? l key = none) :
    LookupList.get? (l ++ l') key = LookupList.get? l' key := by
  induction l with
  | nil => simp
  | cons hd tl ih =>
    cases hd with
    | mk k' v' =>
      by_cases hk : key = k'
      · simp only [LookupList.get?, hk, ↓reduceIte] at hn
        nomatch hn
      · simp only [List.cons_append, LookupList.get?, hk, ↓reduceIte]
        exact ih (by simpa [LookupList.get?, hk] using hn)

private theorem OccCtx.get?_extend_eq_of_not_mem {octx : OccCtx} {occ : Occ}
    {fieldTys : List Ty} {o : Occ}
    (hdisj : o ∉ subOccs occ fieldTys.length) :
    LookupList.get? (OccCtx.extend octx occ fieldTys) o = LookupList.get? octx o := by
  simp only [OccCtx.extend]
  exact LookupList.get?_append_left_none (LookupList.get?_zip_eq_none hdisj)

private theorem captureBindTys_extend_eq {octx : OccCtx} {occ0 : Occ} {fieldTys : List Ty}
    {captured : List Occ}
    (hdisj : ∀ o ∈ captured, o ∉ subOccs occ0 fieldTys.length) :
    captureBindTys (OccCtx.extend octx occ0 fieldTys) captured =
      captureBindTys octx captured := by
  simp only [captureBindTys]
  refine List.map_congr_left ?_
  intro o ho
  simp [OccCtx.get?_extend_eq_of_not_mem (hdisj o ho)]

private theorem rowBindTys_extend_eq {ctors : CtorEnv} {octx : OccCtx} {occ0 : Occ}
    {fieldTys : List Ty} {captured : List Occ} {pats : List GPat} {tys : List Ty}
    (hdisj : ∀ o ∈ captured, o ∉ subOccs occ0 fieldTys.length) :
    rowBindTys ctors (OccCtx.extend octx occ0 fieldTys) captured pats tys =
      rowBindTys ctors octx captured pats tys := by
  simp only [rowBindTys, captureBindTys_extend_eq hdisj]

private theorem rowBindTys_gwild_prefix_irrel {ctors : CtorEnv} {octx : OccCtx}
    {captured : List Occ} {n : Nat} {prest : List GPat} {tys1 tys2 ttys : List Ty}
    (h1 : tys1.length = n) (h2 : tys2.length = n) :
    rowBindTys ctors octx captured (List.replicate n .gwild ++ prest) (tys1 ++ ttys) =
      rowBindTys ctors octx captured (List.replicate n .gwild ++ prest) (tys2 ++ ttys) := by
  simp only [rowBindTys]
  rw [patBindTysGList_append (l1 := List.replicate n .gwild) (l2 := prest) (t1 := tys1)
        (t2 := ttys) (by simp [List.length_replicate, h1]),
    patBindTysGList_append (l1 := List.replicate n .gwild) (l2 := prest) (t1 := tys2)
      (t2 := ttys) (by simp [List.length_replicate, h2]),
    patBindTysGList_replicate_gwild ctors n tys1 h1,
    patBindTysGList_replicate_gwild ctors n tys2 h2]

private theorem instFieldTys_eq_of_inst {ctors : CtorEnv} {c : CtorName} {ctor : Ctor}
    {tyArgs fieldTys : List Ty}
    (hlook : LookupList.get? ctors c = some ctor)
    (hpc : ctor.paramCount = tyArgs.length)
    (hinst : List.Forall₂ (InstantiatesBy tyArgs) ctor.contents fieldTys) :
    fieldTys = instFieldTys ctors c tyArgs :=
  compile_InstantiatesBy_forall2_det_agree (fun _ _ => rfl) ctor.bound hinst
    (instFieldTys_forall₂ hlook hpc)

private theorem EmitTyCtx.agrees_switch_sub (ctors : CtorEnv) {ectx : EmitTyCtx ctors}
    {Γ_outer : Env} {occ0 : Occ} {fieldTys : List Ty}
    (hag : EmitTyCtx.agrees ectx Γ_outer)
    (hlc_f : ∀ t ∈ fieldTys, t.IsLC)
    (hdisj : ∀ o ∈ ectx.occEnv, o ∉ subOccs occ0 fieldTys.length) :
    EmitTyCtx.agrees (ctors := ctors)
      { Γ := fieldTys.map PolyTy.mkTrivial ++ ectx.Γ
        occEnv := subOccs occ0 fieldTys.length ++ ectx.occEnv
        octx := OccCtx.extend ectx.octx occ0 fieldTys }
      Γ_outer := by
  obtain ⟨τs, hlen, hΓ, hlook⟩ := hag
  refine ⟨fieldTys ++ τs, by simp [subOccs, hlen], ?_, ?_⟩
  · simp only [List.map_append, hΓ, List.append_assoc]
  · intro i hi
    have hi' : i < fieldTys.length + τs.length := by
      simpa [subOccs, hlen] using hi
    by_cases hlt : i < fieldTys.length
    · have hget := OccCtx.get?_extend_sub (octx := ectx.octx) (occ := occ0) hlt
      have hkey :
          (subOccs occ0 fieldTys.length ++ ectx.occEnv)[i]'(by simpa [subOccs, hlen] using hi) =
            (subOccs occ0 fieldTys.length)[i]'(by simp [subOccs]; omega) :=
        List.getElem_append_left (by simp [subOccs]; omega)
      refine ⟨?_, ?_⟩
      · rw [hkey, List.getElem_append_left hlt]
        exact hget
      · rw [List.getElem_append_left hlt]
        exact hlc_f _ (List.getElem_mem _)
    · have hix : i - fieldTys.length < ectx.occEnv.length := by omega
      have hkey :
          (subOccs occ0 fieldTys.length ++ ectx.occEnv)[i]'(by simpa [subOccs, hlen] using hi) =
            ectx.occEnv[i - fieldTys.length]'hix := by
        rw [List.getElem_append_right (by simp [subOccs]; omega)]
        simp [subOccs]
      have ⟨hτ, hlc⟩ := hlook (i - fieldTys.length) hix
      have hdisj' : ectx.occEnv[i - fieldTys.length]'hix ∉ subOccs occ0 fieldTys.length :=
        hdisj _ (List.getElem_mem _)
      refine ⟨?_, ?_⟩
      · rw [hkey, List.getElem_append_right (by omega)]
        exact OccCtx.get?_extend_orig hdisj' hτ
      · rw [List.getElem_append_right (by omega)]
        exact hlc

private theorem specializeRow_body_inv_gwild {ctors : CtorEnv} {octx : OccCtx} {Γ_outer : Env}
    {τres : Ty} {occ0 : Occ} {c : CtorName} {τ0 : Ty} {ttys : List Ty} {bodies : Nat → Expr}
    {r r' : Row} {prest : List GPat} {arity : Nat} {fieldTys : List Ty}
    (hlen : fieldTys.length = arity)
    (hs : specializeRow c arity occ0 r = some r')
    (hpats : r.pats = .gwild :: prest)
    (hbody : TypeOfHM
      ⟨(rowBindTys ctors octx r.captured r.pats (τ0 :: ttys)).map PolyTy.mkTrivial ++ Γ_outer,
        ctors⟩
      (bodies r.act) τres) :
    TypeOfHM
      ⟨(rowBindTys ctors octx r'.captured r'.pats (fieldTys ++ ttys)).map
          PolyTy.mkTrivial ++ Γ_outer, ctors⟩
      (bodies r'.act) τres := by
  obtain ⟨captured, pats, act⟩ := r
  subst hpats
  simp only [specializeRow, Option.some.injEq] at hs
  subst hs
  have hrow :
      rowBindTys ctors octx captured (List.replicate arity .gwild ++ prest)
        (fieldTys ++ ttys) =
      rowBindTys ctors octx captured (.gwild :: prest) (τ0 :: ttys) := by
    simp only [rowBindTys, patBindTysGList_cons, patBindTysG]
    rw [patBindTysGList_append (by simp [hlen]),
      patBindTysGList_replicate_gwild ctors arity _ (by simp [hlen])]
  simpa [hrow] using hbody

mutual
/-- An `InstantiatesBy tyArgs` witness only ever consults `tyArgs` within its own
    length (every `.bvar i` it touches has `tyArgs[i]? = some _`, forcing
    `i < tyArgs.length`) — so the *source* type is automatically
    `ContainsBvarsUpTo tyArgs.length`, with NO separate arity/`paramCount`
    hypothesis needed. This lets us recover `instFieldTys ctors c tyArgs =
    fieldTys` from a `GPatWF`-derived `Forall₂` alone (via
    `InstantiatesBy.eq_openWith`), independently of the (possibly false, see
    `compile_initMatrix_typeable`'s `harity`) `ctor.paramCount = tyArgs.length`
    fact. -/
private theorem InstantiatesBy.containsBvarsUpTo_length {tyArgs : List Ty} :
    ∀ {ty τ : Ty}, InstantiatesBy tyArgs ty τ → ContainsBvarsUpTo tyArgs.length ty
  | _, _, .prim => .prim
  | _, _, .fvar => .fvar
  | _, _, .bvar h => .bvar (List.getElem?_eq_some_iff.mp h).1
  | _, _, .arrow ha hb =>
      .arrow (InstantiatesBy.containsBvarsUpTo_length ha)
        (InstantiatesBy.containsBvarsUpTo_length hb)
  | _, _, .customTy hforall =>
      .customTy (InstantiatesBy_forall₂_containsBvarsUpTo hforall)

private theorem InstantiatesBy_forall₂_containsBvarsUpTo {tyArgs : List Ty} :
    ∀ {tys instTys : List Ty}, List.Forall₂ (InstantiatesBy tyArgs) tys instTys →
      ∀ t ∈ tys, ContainsBvarsUpTo tyArgs.length t
  | _, _, .nil => by simp
  | _, _, .cons hhd htl => fun t ht => by
      rcases List.mem_cons.mp ht with rfl | ht'
      · exact InstantiatesBy.containsBvarsUpTo_length hhd
      · exact InstantiatesBy_forall₂_containsBvarsUpTo htl t ht'
end

/-- `InstantiatesBy` determines `Ty.openWith` at exactly its own witness length
    (specialising `InstantiatesBy.eq_openWith` with `n := tyArgs.length`, using
    `containsBvarsUpTo_length` for the side condition — no `paramCount`
    hypothesis needed). -/
private theorem InstantiatesBy.eq_openWith_self {tyArgs : List Ty} {ty τ : Ty}
    (h : InstantiatesBy tyArgs ty τ) : τ = Ty.openWith tyArgs ty :=
  InstantiatesBy.eq_openWith h (InstantiatesBy.containsBvarsUpTo_length h) rfl

private theorem instFieldTys_eq_of_forall₂' {tyArgs : List Ty} :
    ∀ {contents fieldTys : List Ty},
      List.Forall₂ (InstantiatesBy tyArgs) contents fieldTys →
      contents.map (Ty.openWith tyArgs) = fieldTys
  | _, _, .nil => rfl
  | _, _, .cons hhd htl => by
      simp only [List.map_cons, instFieldTys_eq_of_forall₂' htl,
        ← InstantiatesBy.eq_openWith_self hhd]

private theorem instFieldTys_eq_of_forall₂ {ctors : CtorEnv} {c : CtorName} {ctor : Ctor}
    {tyArgs fieldTys : List Ty}
    (hctor : LookupList.get? ctors c = some ctor)
    (hinst : List.Forall₂ (InstantiatesBy tyArgs) ctor.contents fieldTys) :
    instFieldTys ctors c tyArgs = fieldTys := by
  unfold instFieldTys
  simp only [hctor, Option.map_some, Option.getD]
  exact instFieldTys_eq_of_forall₂' hinst

private theorem subOccs_nodup (occ : Occ) : ∀ n, List.Nodup (subOccs occ n)
  | 0 => by simp [subOccs]
  | n + 1 => by
    have ih := subOccs_nodup occ n
    simp only [subOccs, List.range_succ, List.map_append, List.map_cons, List.map_nil] at ih ⊢
    refine List.Nodup.append ih (List.nodup_singleton _) ?_
    intro a ha hin
    simp only [List.mem_singleton] at hin
    subst hin
    simp only [List.mem_map, List.mem_range] at ha
    obtain ⟨i, hi, h⟩ := ha
    exact Nat.ne_of_lt hi (List.cons.inj (List.append_cancel_left h)).1

private theorem subOccs_disjoint_of_fringe {occ0 : Occ} {n : Nat} {orest : List Occ}
    {occEnv : List Occ}
    (horest : ∀ o ∈ orest, o ∈ occEnv)
    (hnochild : ∀ o ∈ occEnv, ∀ suffix : List Nat, suffix ≠ [] → o ≠ occ0 ++ suffix) :
    ∀ a ∈ subOccs occ0 n, a ∉ orest := by
  intro a ha hin
  simp only [subOccs, List.mem_map, List.mem_range] at ha
  obtain ⟨i, hi, rfl⟩ := ha
  exact hnochild _ (horest _ hin) [i] (List.cons_ne_nil _ _) rfl

/-- Auxiliary: `DTreeTypeable` for `compile occs M`. Strengthened with column
    lookups, frontier membership, no-proper-extension fringe, frontier `Nodup`,
    global ctor-env hygiene (`arityConsistent` / `fieldsKinded`), and
    octx-kinded occurrences (every `customTy` in `octx` agrees with
    `kindEnvOfCtors`). Local arity pin is `hcons` + `hoctx_kinded`.
    Fringe: no `occEnv` entry is a proper extension of a frontier occurrence
    (generalizes “no direct child”, needed under nested `OccCtx.extend`).
    Column types are also `WellKinded ke 0` so field types under `openWith`
    stay kinded (needed for nested foreign ADT arity). -/
private theorem compile_typeable_aux {ctors : CtorEnv} {Γ_outer : Env} {bodies : Nat → Expr}
    {τres : Ty}
    (hcons : CtorEnv.arityConsistent ctors)
    (hfields : CtorEnv.fieldsKinded ctors) :
    ∀ (ectx : EmitTyCtx ctors), EmitTyCtx.agrees ectx Γ_outer →
    ∀ (occs : List Occ) (M : Matrix) (tys : List Ty)
      (hlen : tys.length = occs.length),
      List.Nodup occs →
      (∀ o ∈ occs, o ∈ ectx.occEnv) →
      (∀ (i : Nat) (hi : i < occs.length),
        LookupList.get? ectx.octx (occs[i]) = some (tys[i]'(hlen ▸ hi)) ∧
          (tys[i]'(hlen ▸ hi)).IsLC ∧
          Ty.WellKinded (kindEnvOfCtors ctors) 0 (tys[i]'(hlen ▸ hi))) →
      (∀ occ ∈ occs, ∀ o ∈ ectx.occEnv, ∀ suffix : List Nat,
        suffix ≠ [] → o ≠ occ ++ suffix) →
      (∀ {occ : Occ} {T' : TyName} {args : List Ty},
        LookupList.get? ectx.octx occ = some (.customTy T' args) →
        LookupList.get? (kindEnvOfCtors ctors) T' = some args.length) →
      (∀ r ∈ M, GPatWFList ctors r.pats tys) →
      DTreeExhaustive ctors ectx.octx (compile occs M) →
      (∀ r ∈ M, ∀ o ∈ r.captured, o ∈ ectx.occEnv) →
      (∀ r ∈ M,
        TypeOfHM
          ⟨(rowBindTys ctors ectx.octx r.captured r.pats tys).map PolyTy.mkTrivial ++ Γ_outer,
            ctors⟩
          (bodies r.act) τres) →
      DTreeTypeable ctors Γ_outer bodies τres ectx (compile occs M) := by
  intro ectx hag occs M
  induction occs, M using compile.induct generalizing ectx with
  | case1 occs =>
    intro tys hlen hnodup hoccs htys hnochild hoctx_kinded hMwf hexh hcap hbody
    simp only [compile] at hexh ⊢
    exact (DTreeExhaustive_not_fail hexh).elim
  | case2 r1 rest =>
    intro tys hlen hnodup hoccs htys hnochild hoctx_kinded hMwf hexh hcap hbody
    simp only [compile]
    have hnil : tys = [] := (List.length_eq_zero_iff).mp hlen
    subst hnil
    have hwf := hMwf r1 List.mem_cons_self
    have hpats : r1.pats = [] :=
      (List.length_eq_zero_iff).mp (compile_GPatWFList_length hwf)
    have hcap1 := hcap r1 List.mem_cons_self
    have hbody1 := hbody r1 List.mem_cons_self
    refine DTreeTypeable.leaf (binds := r1.captured)
      (bindTys := captureBindTys ectx.octx r1.captured) hag (by simp [captureBindTys]) ?_ ?_
    · intro i hi
      have hmem := hcap1 (r1.captured[i]'hi) (List.getElem_mem hi)
      refine ⟨?_, hmem⟩
      simp only [captureBindTys, List.getElem_map]
      obtain ⟨τs, hlenτ, _, hlook⟩ := hag
      have hj := List.idxOf_lt_length_of_mem hmem
      have ⟨hτ, _⟩ := hlook _ hj
      have hocceq : ectx.occEnv[ectx.occEnv.idxOf (r1.captured[i]'hi)]'hj =
          r1.captured[i]'hi := List.getElem_idxOf hj
      rw [hocceq] at hτ
      simp [hτ]
    · convert hbody1
      simp only [rowBindTys, hpats, patBindTysGList, List.append_nil]
  | case3 r1 rest occ0 orest hh ih =>
    intro tys hlen hnodup hoccs htys hnochild hoctx_kinded hMwf hexh hcap hbody
    rw [compile]
    split
    · rename_i heq
      cases tys with
      | nil => cases hlen
      | cons τ0 ttys =>
        have hlen' : ttys.length = orest.length := by
          simpa [List.length_cons] using hlen
        have hlook0 : LookupList.get? ectx.octx occ0 = some τ0 := (htys 0 (Nat.zero_lt_succ _)).1
        have hmem0 : occ0 ∈ ectx.occEnv := hoccs _ List.mem_cons_self
        have hexh' : DTreeExhaustive ctors ectx.octx
            (compile orest (defaultMatrix occ0 (r1 :: rest))) := by
          have hexh2 := hexh
          simp only [compile] at hexh2
          split at hexh2
          · exact hexh2
          · rename_i heq2
            cases heq.symm.trans heq2
        refine ih ectx hag ttys hlen'
          (List.nodup_cons.mp hnodup).2
          (fun o ho => hoccs o (List.mem_cons_of_mem _ ho))
          (fun i hi => htys (i + 1) (Nat.succ_lt_succ hi))
          (fun occ hoc o ho suf hsuf =>
            hnochild occ (List.mem_cons_of_mem _ hoc) o ho suf hsuf)
          hoctx_kinded
          (fun r' hr' => by
            obtain ⟨r, hr, hs⟩ := List.mem_filterMap.mp hr'
            exact compile_defaultRow_wf (hMwf r hr) hs)
          hexh'
          (fun r' hr' o ho => by
            obtain ⟨r, hr, hs⟩ := List.mem_filterMap.mp hr'
            rcases compile_defaultRow_captured_sub hs o ho with h | rfl
            · exact hcap r hr o h
            · exact hmem0)
          (fun r' hr' => by
            obtain ⟨r, hr, hs⟩ := List.mem_filterMap.mp hr'
            exact defaultRow_body_inv hlook0 hs (hbody r hr))
    · rename_i heq
      rw [hh] at heq
      exact absurd heq.symm (List.cons_ne_nil _ _)
  | case4 r1 rest occ0 orest hhd htl hh ihcases ihdflt =>
    intro tys hlen hnodup hoccs htys hnochild hoctx_kinded hMwf hexh hcap hbody
    cases tys with
    | nil => cases hlen
    | cons τ0 ttys =>
      have hlen' : ttys.length = orest.length := by
        simpa [List.length_cons] using hlen
      have hlook0 : LookupList.get? ectx.octx occ0 = some τ0 := (htys 0 (Nat.zero_lt_succ _)).1
      have hlc0 : τ0.IsLC := (htys 0 (Nat.zero_lt_succ _)).2.1
      have hwk0 : Ty.WellKinded (kindEnvOfCtors ctors) 0 τ0 :=
        (htys 0 (Nat.zero_lt_succ _)).2.2
      have hmem0 : occ0 ∈ ectx.occEnv := hoccs _ List.mem_cons_self
      have hhdmem : hhd ∈ colHeads (r1 :: rest) := by rw [hh]; exact List.mem_cons_self
      obtain ⟨r0, hr0, cargs0, rest0, hpats0, hlen0⟩ :=
        compile_colHeads_mem_witness (r1 :: rest) hhd.1 hhd.2 hhdmem
      have hwf0 := hMwf r0 hr0
      rw [hpats0] at hwf0
      obtain ⟨T0, tyArgs0, ctor0, fieldTys0, hTy0, hlook_ctor0, hname0, hinst0, hwfargs0⟩ :=
        compile_GPatWF.gctor_inv (by cases hwf0 with | cons hwf0_hd _ => exact hwf0_hd)
      subst hTy0
      have htyArgs_lc : ∀ t ∈ tyArgs0, t.IsLC := by
        cases hlc0 with | customTy h => exact h
      have htyArgs_wk : ∀ t ∈ tyArgs0, Ty.WellKinded (kindEnvOfCtors ctors) 0 t :=
        (Ty.WellKinded.customTy_inv hwk0).2
      have hkind0 : LookupList.get? (kindEnvOfCtors ctors) T0 = some tyArgs0.length :=
        (Ty.WellKinded.customTy_inv hwk0).1
      rw [compile]
      split
      · rename_i heq
        rw [hh] at heq
        exact absurd heq (List.cons_ne_nil _ _)
      · rename_i hhd' htl' heq
        rw [hh] at heq
        injection heq with h1 h2
        subst h1; subst h2
        set cases : List (CtorName × Nat × DTree) :=
          (hhd :: htl).attach.map (fun x =>
            (x.1.1, x.1.2,
              compile (subOccs occ0 x.1.2 ++ orest)
                (specialize x.1.1 x.1.2 occ0 (r1 :: rest))))
        have hne : cases ≠ [] := by
          intro hnil
          have : (hhd :: htl).attach = [] := (List.map_eq_nil_iff).mp hnil
          exact List.cons_ne_nil _ _ (List.attach_eq_nil_iff.mp this)
        have hexh' : DTreeExhaustive ctors ectx.octx
            (.switch occ0 cases (compile orest (defaultMatrix occ0 (r1 :: rest)))) := by
          have hexh2 := hexh
          simp only [compile] at hexh2
          split at hexh2
          · rename_i heq2
            rw [hh] at heq2
            exact absurd heq2 (List.cons_ne_nil _ _)
          · rename_i hhd2 htl2 heq2
            rw [hh] at heq2
            injection heq2 with h1 h2
            subst h1; subst h2
            simpa [cases] using hexh2
        have hdisj_frontier :
            ∀ o ∈ ectx.occEnv, ∀ n : Nat, o ∉ subOccs occ0 n := by
          intro o ho n hin
          simp only [subOccs, List.mem_map, List.mem_range] at hin
          obtain ⟨i, hi, heq⟩ := hin
          exact hnochild occ0 List.mem_cons_self o ho [i] (List.cons_ne_nil i []) heq.symm
        have htyped_cases : ∀ c a t, (c, a, t) ∈ cases →
            ∃ ctor, LookupList.get? ctors c = some ctor ∧ ctor.tyName = T0 ∧
              a = ctor.contents.length ∧ ctor.paramCount = tyArgs0.length := by
          intro c a t ht
          obtain ⟨x, hx, heq⟩ := List.mem_map.mp ht
          injection heq with hc hrest
          injection hrest with ha htEq
          subst hc; subst ha; subst htEq
          have hmem : x.val ∈ hhd :: htl := x.property
          obtain ⟨rN, hrN, cargsN, restN, hpatsN, hlenN⟩ :=
            compile_colHeads_mem_witness (r1 :: rest) x.val.1 x.val.2
              (by rw [hh]; exact hmem)
          have hwfN := hMwf rN hrN
          rw [hpatsN] at hwfN
          cases hwfN with
          | cons hwfN_hd _ =>
            obtain ⟨TN, tyArgsN, ctorN, fieldTysN, hTyN, hlookN, hnameN, hinstN, hwfargsN⟩ :=
              compile_GPatWF.gctor_inv hwfN_hd
            injection hTyN with hTN hTyArgsN
            subst hTN; subst hTyArgsN
            have hlen_c := compile_GPatWFList_length hwfargsN
            have hlen_f := List.Forall₂.length_eq hinstN
            refine ⟨ctorN, hlookN, hnameN, ?_,
              CtorEnv.paramCount_eq_of_arityConsistent hcons hkind0 hlookN hnameN⟩
            omega
        -- Child specialize IH under `OccCtx.extend`. Nested foreign / differently-
        -- parameterized ADT arity is discharged by `hfields` + `WellKinded_openWith`
        -- + `hoctx_kinded` maintained under extend (not a root-only `harity`).
        have hsub_cases :
            (∀ c a t, (c, a, t) ∈ cases →
              DTreeExhaustive ctors
                (OccCtx.extend ectx.octx occ0 (instFieldTys ctors c tyArgs0)) t) →
            ∀ c a t, (c, a, t) ∈ cases →
              DTreeTypeable ctors Γ_outer bodies τres
                { Γ := (instFieldTys ctors c tyArgs0).map PolyTy.mkTrivial ++ ectx.Γ
                  occEnv := subOccs occ0 a ++ ectx.occEnv
                  octx := OccCtx.extend ectx.octx occ0 (instFieldTys ctors c tyArgs0) } t := by
          intro hsubExh c a t ht
          obtain ⟨x, hx, heq⟩ := List.mem_map.mp ht
          injection heq with hc hrest
          injection hrest with ha htEq
          subst hc; subst ha; subst htEq
          have hmem : x.val ∈ hhd :: htl := x.property
          obtain ⟨rN, hrN, cargsN, restN, hpatsN, hlenN⟩ :=
            compile_colHeads_mem_witness (r1 :: rest) x.val.1 x.val.2
              (by rw [hh]; exact hmem)
          have hwfN := hMwf rN hrN
          rw [hpatsN] at hwfN
          cases hwfN with
          | cons hwfN_hd hwfN_tl =>
            obtain ⟨TN, tyArgsN, ctorN, fieldTysN, hTyN, hlookN, hnameN, hinstN, hwfargsN⟩ :=
              compile_GPatWF.gctor_inv hwfN_hd
            injection hTyN with hTN hTyArgsN
            subst hTN; subst hTyArgsN
            have hpcN : ctorN.paramCount = tyArgs0.length :=
              CtorEnv.paramCount_eq_of_arityConsistent hcons hkind0 hlookN hnameN
            have hfields_eq : fieldTysN = instFieldTys ctors x.val.1 tyArgs0 :=
              instFieldTys_eq_of_inst hlookN hpcN hinstN
            have hlen_c := compile_GPatWFList_length hwfargsN
            have hlen_f := List.Forall₂.length_eq hinstN
            have hlen_inst : (instFieldTys ctors x.val.1 tyArgs0).length = x.val.2 := by
              rw [← hfields_eq]; omega
            set fieldTys := instFieldTys ctors x.val.1 tyArgs0
            have hlc_f : ∀ ty ∈ fieldTys, ty.IsLC := by
              intro ty hty
              obtain ⟨c0, hc0, heqTy⟩ :
                  ∃ c0 ∈ ctorN.contents, Ty.openWith tyArgs0 c0 = ty := by
                simpa [fieldTys, instFieldTys, hlookN, Option.map_some, Option.getD] using hty
              exact heqTy ▸
                Ty.openWith_isLC htyArgs_lc (hpcN ▸ ctorN.bound c0 hc0) (le_of_eq hpcN)
            have hwk_f : ∀ ty ∈ fieldTys, Ty.WellKinded (kindEnvOfCtors ctors) 0 ty := by
              intro ty hty
              obtain ⟨c0, hc0, heqTy⟩ :
                  ∃ c0 ∈ ctorN.contents, Ty.openWith tyArgs0 c0 = ty := by
                simpa [fieldTys, instFieldTys, hlookN, Option.map_some, Option.getD] using hty
              exact heqTy ▸
                Ty.WellKinded_openWith (hpcN ▸ hfields _ _ hlookN c0 hc0)
                  htyArgs_wk (le_of_eq hpcN)
            have hdisj_env : ∀ o ∈ ectx.occEnv, o ∉ subOccs occ0 fieldTys.length :=
              fun o ho => hdisj_frontier o ho fieldTys.length
            have hag' :=
              EmitTyCtx.agrees_switch_sub ctors hag hlc_f hdisj_env
            set ectx' : EmitTyCtx ctors :=
              { Γ := fieldTys.map PolyTy.mkTrivial ++ ectx.Γ
                occEnv := subOccs occ0 fieldTys.length ++ ectx.occEnv
                octx := OccCtx.extend ectx.octx occ0 fieldTys }
            have hlen_child : (fieldTys ++ ttys).length =
                (subOccs occ0 x.val.2 ++ orest).length := by
              simp [subOccs, hlen', hlen_inst]
            have hoccs_child : ∀ o ∈ subOccs occ0 x.val.2 ++ orest, o ∈ ectx'.occEnv := by
              intro o ho
              simp only [ectx']
              rcases List.mem_append.mp ho with ho | ho
              · refine List.mem_append_left _ ?_
                simpa [hlen_inst] using ho
              · exact List.mem_append_right _ (hoccs o (List.mem_cons_of_mem _ ho))
            have hnodup_child : List.Nodup (subOccs occ0 x.val.2 ++ orest) := by
              refine List.Nodup.append (by simpa [hlen_inst] using subOccs_nodup occ0 fieldTys.length)
                (List.nodup_cons.mp hnodup).2 ?_
              intro a ha hin
              exact subOccs_disjoint_of_fringe
                (fun o ho => hoccs o (List.mem_cons_of_mem _ ho))
                (fun o ho suf hsuf => hnochild occ0 List.mem_cons_self o ho suf hsuf)
                a (by simpa [hlen_inst] using ha) hin
            have htys_child : ∀ (i : Nat) (hi : i < (subOccs occ0 x.val.2 ++ orest).length),
                LookupList.get? ectx'.octx ((subOccs occ0 x.val.2 ++ orest)[i]'hi) =
                  some ((fieldTys ++ ttys)[i]'(by simpa [hlen_child] using hi)) ∧
                ((fieldTys ++ ttys)[i]'(by simpa [hlen_child] using hi)).IsLC ∧
                Ty.WellKinded (kindEnvOfCtors ctors) 0
                  ((fieldTys ++ ttys)[i]'(by simpa [hlen_child] using hi)) := by
              intro i hi
              have hiτ : i < (fieldTys ++ ttys).length := by simpa [hlen_child] using hi
              by_cases hlt : i < fieldTys.length
              · have hkey :
                    (subOccs occ0 x.val.2 ++ orest)[i]'hi =
                      (subOccs occ0 fieldTys.length)[i]'(by simp [subOccs]; omega) := by
                  simp only [← hlen_inst]
                  exact List.getElem_append_left (by simp [subOccs]; omega)
                refine ⟨?_, ?_, ?_⟩
                · rw [hkey, List.getElem_append_left hlt]
                  simpa [ectx', hlen_inst] using
                    OccCtx.get?_extend_sub (octx := ectx.octx) (occ := occ0)
                      (fieldTys := fieldTys) hlt
                · rw [List.getElem_append_left hlt]
                  exact hlc_f _ (List.getElem_mem _)
                · rw [List.getElem_append_left hlt]
                  exact hwk_f _ (List.getElem_mem _)
              · have hix : i - fieldTys.length < orest.length := by
                  simp [subOccs] at hi; omega
                have hkey :
                    (subOccs occ0 x.val.2 ++ orest)[i]'hi =
                      orest[i - fieldTys.length]'hix := by
                  have hi' : i < (subOccs occ0 fieldTys.length ++ orest).length := by
                    simpa [hlen_inst] using hi
                  have h := List.getElem_append_right
                    (as := subOccs occ0 fieldTys.length) (bs := orest)
                    (h₁ := by simp [subOccs]; omega) (h₂ := hi')
                  simpa [hlen_inst, subOccs, List.length_map, List.length_range] using h
                have ⟨hτ, hlc, hwk⟩ := htys (i - fieldTys.length + 1) (Nat.succ_lt_succ hix)
                have hdisj' :
                    orest[i - fieldTys.length]'hix ∉ subOccs occ0 fieldTys.length :=
                  hdisj_frontier _ (hoccs _ (List.mem_cons_of_mem _
                    (List.getElem_mem hix))) _
                refine ⟨?_, ?_, ?_⟩
                · rw [hkey, List.getElem_append_right (by omega)]
                  simpa [ectx', List.getElem_cons_succ] using
                    OccCtx.get?_extend_orig hdisj' hτ
                · rw [List.getElem_append_right (by omega)]
                  simpa [List.getElem_cons_succ] using hlc
                · rw [List.getElem_append_right (by omega)]
                  simpa [List.getElem_cons_succ] using hwk
            have hnochild_child :
                ∀ occ ∈ subOccs occ0 x.val.2 ++ orest,
                  ∀ o ∈ ectx'.occEnv, ∀ suffix : List Nat,
                    suffix ≠ [] → o ≠ occ ++ suffix := by
              intro occ hoc o ho suf hsuf heq
              have hnotin0 : occ0 ∉ orest := (List.nodup_cons.mp hnodup).1
              simp only [List.mem_append, ectx'] at hoc ho
              rcases hoc with hoc | hoc <;> rcases ho with ho | ho
              · simp only [subOccs, List.mem_map, List.mem_range, hlen_inst] at hoc ho
                obtain ⟨i, hi, rfl⟩ := hoc
                obtain ⟨j, hj, rfl⟩ := ho
                have heq' : occ0 ++ [j] = occ0 ++ ([i] ++ suf) := by
                  simpa [List.append_assoc] using heq
                have htail : [j] = [i] ++ suf := List.append_cancel_left heq'
                have hsuf0 : suf = [] := by
                  have := congrArg List.length htail
                  simp only [List.length_append, List.length_cons, List.length_nil] at this
                  exact List.eq_nil_of_length_eq_zero (by omega)
                exact hsuf hsuf0
              · simp only [subOccs, List.mem_map, List.mem_range] at hoc
                obtain ⟨i, hi, rfl⟩ := hoc
                exact hnochild occ0 List.mem_cons_self o ho (i :: suf)
                  (List.cons_ne_nil _ _) (by simpa [List.append_assoc] using heq)
              · simp only [subOccs, List.mem_map, List.mem_range, hlen_inst] at ho
                obtain ⟨i, hi, rfl⟩ := ho
                have hlenEq := congrArg List.length heq
                simp [List.length_append] at hlenEq
                have hle : occ.length ≤ occ0.length := by
                  have := List.length_pos_of_ne_nil hsuf; omega
                have htake : (occ0 ++ [i]).take occ.length = occ := by
                  simpa [List.take_left' (by omega)] using
                    (congrArg (fun l : List Nat => l.take occ.length) heq.symm).symm
                have htake0 : occ0.take occ.length = occ := by
                  simpa [List.take_append_of_le_length hle] using htake
                have hmid : occ0 = occ ++ occ0.drop occ.length := by
                  simpa [htake0] using (List.take_append_drop occ.length occ0).symm
                cases hdrop : occ0.drop occ.length with
                | nil =>
                  have : occ = occ0 := by
                    have := hmid; simp [hdrop, List.append_nil] at this; exact this.symm
                  exact hnotin0 (this ▸ hoc)
                | cons k mid' =>
                  have hmid' : occ0 = occ ++ (k :: mid') := by simpa [hdrop] using hmid
                  exact hnochild occ (List.mem_cons_of_mem _ hoc) occ0 hmem0 (k :: mid')
                    (List.cons_ne_nil _ _) hmid'
              · exact hnochild occ (List.mem_cons_of_mem _ hoc) o ho suf hsuf heq
            have hoctx_kinded_child :
                ∀ {occ : Occ} {T' : TyName} {args : List Ty},
                  LookupList.get? ectx'.octx occ = some (.customTy T' args) →
                  LookupList.get? (kindEnvOfCtors ctors) T' = some args.length := by
              intro occ T' args hlookOcc
              by_cases hin : occ ∈ subOccs occ0 fieldTys.length
              · simp only [subOccs, List.mem_map, List.mem_range] at hin
                obtain ⟨i, hi, rfl⟩ := hin
                have hlook_f :=
                  OccCtx.get?_extend_sub (octx := ectx.octx) (occ := occ0)
                    (fieldTys := fieldTys) hi
                simp only [ectx'] at hlookOcc
                rw [← subOccs_getElem occ0 fieldTys.length i hi] at hlookOcc
                rw [hlook_f] at hlookOcc
                injection hlookOcc with hτEq
                have hwk_i := hwk_f _ (List.getElem_mem hi)
                exact (Ty.WellKinded.customTy_inv (hτEq ▸ hwk_i)).1
              · have hlook' :
                    LookupList.get? ectx.octx occ = some (.customTy T' args) := by
                  simpa [ectx', OccCtx.get?_extend_eq_of_not_mem hin] using hlookOcc
                exact hoctx_kinded hlook'
            have hwf_child : ∀ r ∈ specialize x.val.1 x.val.2 occ0 (r1 :: rest),
                GPatWFList ctors r.pats (fieldTys ++ ttys) := by
              intro r' hr'
              obtain ⟨r, hr, hs⟩ := List.mem_filterMap.mp hr'
              have hinst' : List.Forall₂ (InstantiatesBy tyArgs0) ctorN.contents fieldTys := by
                simpa [fieldTys, ← hfields_eq] using hinstN
              exact compile_specializeRow_wf hlookN hinst' hlen_inst
                (hMwf r hr) hs
            have hexh_child :
                DTreeExhaustive ctors ectx'.octx
                  (compile (subOccs occ0 x.val.2 ++ orest)
                    (specialize x.val.1 x.val.2 occ0 (r1 :: rest))) := by
              simpa [ectx', fieldTys, hlen_inst] using hsubExh x.val.1 x.val.2 _ ht
            have hcap_child : ∀ r ∈ specialize x.val.1 x.val.2 occ0 (r1 :: rest),
                ∀ o ∈ r.captured, o ∈ ectx'.occEnv := by
              intro r' hr' o ho
              simp only [ectx']
              obtain ⟨r, hr, hs⟩ := List.mem_filterMap.mp hr'
              rcases compile_specializeRow_captured_sub hs o ho with h | hocceq
              · exact List.mem_append_right _ (hcap r hr o h)
              · exact List.mem_append_right _ (hocceq ▸ hmem0)
            have hbody_child : ∀ r ∈ specialize x.val.1 x.val.2 occ0 (r1 :: rest),
                TypeOfHM
                  ⟨(rowBindTys ctors ectx'.octx r.captured r.pats (fieldTys ++ ttys)).map
                      PolyTy.mkTrivial ++ Γ_outer, ctors⟩
                  (bodies r.act) τres := by
              intro r' hr'
              obtain ⟨r, hr, hs⟩ := List.mem_filterMap.mp hr'
              have hbody0 := hbody r hr
              cases hp : r.pats with
              | nil => simp [specializeRow, hp] at hs
              | cons p prest =>
                match p with
                | .gctor c' args =>
                  by_cases hcond : c' = x.val.1 ∧ args.length = x.val.2
                  · obtain ⟨rfl, ha'⟩ := hcond
                    have hfield :
                        patGctorFieldTys ctors x.val.1 (.customTy T0 tyArgs0) =
                          some fieldTys := by
                      simp only [patGctorFieldTys, hlookN, hnameN, ↓reduceIte, fieldTys]
                    have hs' : specializeRow x.val.1 args.length occ0 r = some r' := by
                      simpa [specializeRow, hp, ha'] using hs
                    have hbody1 :=
                      specializeRow_body_inv_gctor hfield hs' hp (by omega) hbody0
                    have hdisj_cap : ∀ o ∈ r'.captured, o ∉ subOccs occ0 fieldTys.length := by
                      intro o ho
                      have hs'' := hs'
                      simp only [specializeRow, hp, ha', and_self, ↓reduceIte,
                        Option.some.injEq] at hs''
                      cases hs''; exact hdisj_frontier o (hcap r hr o ho) _
                    simpa [ectx', rowBindTys_extend_eq hdisj_cap] using hbody1
                  · simp [specializeRow, hp, hcond] at hs
                | .gbind =>
                  have hbody1 :=
                    specializeRow_body_inv_gbind (c := x.val.1) hlook0 hs hp hbody0
                  simp only [specializeRow, hp, Option.some.injEq] at hs
                  subst hs
                  have hrow :=
                    rowBindTys_gwild_prefix_irrel (ctors := ctors) (octx := ectx.octx)
                      (captured := r.captured ++ [occ0]) (n := x.val.2) (prest := prest)
                      (tys1 := List.replicate x.val.2 (.customTy T0 tyArgs0))
                      (tys2 := fieldTys) (ttys := ttys)
                      (by simp [List.length_replicate]) (by omega)
                  have hbody2 :
                      TypeOfHM
                        ⟨(rowBindTys ctors ectx.octx (r.captured ++ [occ0])
                            (List.replicate x.val.2 .gwild ++ prest)
                            (fieldTys ++ ttys)).map PolyTy.mkTrivial ++ Γ_outer, ctors⟩
                        (bodies r.act) τres := by
                    simpa [hrow] using hbody1
                  have hdisj_cap : ∀ o ∈ r.captured ++ [occ0], o ∉ subOccs occ0 fieldTys.length := by
                    intro o ho
                    simp only [List.mem_append, List.mem_singleton] at ho
                    rcases ho with ho | rfl
                    · exact hdisj_frontier o (hcap r hr o ho) _
                    · exact hdisj_frontier _ hmem0 _
                  simpa [ectx', rowBindTys_extend_eq hdisj_cap] using hbody2
                | .gwild =>
                  have hbody1 :=
                    specializeRow_body_inv_gwild hlen_inst hs hp hbody0
                  have hdisj_cap : ∀ o ∈ r'.captured, o ∉ subOccs occ0 fieldTys.length := by
                    intro o ho
                    simp only [specializeRow, hp, Option.some.injEq] at hs
                    subst hs
                    exact hdisj_frontier o (hcap r hr o ho) _
                  simpa [ectx', rowBindTys_extend_eq hdisj_cap] using hbody1
            have hgoal :=
              ihcases x ectx' hag' (fieldTys ++ ttys) hlen_child hnodup_child
                hoccs_child htys_child hnochild_child hoctx_kinded_child hwf_child hexh_child
                hcap_child hbody_child
            convert hgoal using 1 <;> first | rfl | simp [ectx', fieldTys, hlen_inst]
        cases hdef : compile orest (defaultMatrix occ0 (r1 :: rest)) with
        | fail =>
          have hexhF : DTreeExhaustive ctors ectx.octx (.switch occ0 cases .fail) := by
            simpa [hdef] using hexh'
          cases hexhF with
          | switchFail hlookEx htypedEx hsubEx hcoverEx =>
            rename_i TEx tyArgsEx
            rw [hlook0] at hlookEx
            injection hlookEx with hτ
            injection hτ with hT hArgs
            subst hT; subst hArgs
            exact DTreeTypeable.switchFail hne hag hlook0 hmem0 htyArgs_lc
              htyped_cases (hsub_cases hsubEx) hcoverEx
          | switchDefault hdne hlookEx htypedEx hsubEx hexhDflt =>
            rename_i TEx tyArgsEx
            exact (hdne rfl).elim
        | leaf act binds =>
          have hexhD : DTreeExhaustive ctors ectx.octx
              (.switch occ0 cases (.leaf act binds)) := by simpa [hdef] using hexh'
          cases hexhD with
          | switchDefault hdne hlookEx htypedEx hsubEx hexhDflt =>
            rename_i TEx tyArgsEx
            rw [hlook0] at hlookEx
            injection hlookEx with hτ
            injection hτ with hT hArgs
            subst hT; subst hArgs
            refine DTreeTypeable.switchDefault hdne hag hlook0 hmem0 htyArgs_lc
              htyped_cases (hsub_cases hsubEx) ?_
            have hd := ihdflt ectx hag ttys hlen'
              (List.nodup_cons.mp hnodup).2
              (fun o ho => hoccs o (List.mem_cons_of_mem _ ho))
              (fun i hi => htys (i + 1) (Nat.succ_lt_succ hi))
              (fun occ hoc o ho suf hsuf =>
                hnochild occ (List.mem_cons_of_mem _ hoc) o ho suf hsuf)
              hoctx_kinded
              (fun r' hr' => by
                obtain ⟨r, hr, hs⟩ := List.mem_filterMap.mp hr'
                exact compile_defaultRow_wf (hMwf r hr) hs)
              (by simpa [hdef] using hexhDflt)
              (fun r' hr' o ho => by
                obtain ⟨r, hr, hs⟩ := List.mem_filterMap.mp hr'
                rcases compile_defaultRow_captured_sub hs o ho with h | hocceq
                · exact hcap r hr o h
                · exact hocceq ▸ hmem0)
              (fun r' hr' => by
                obtain ⟨r, hr, hs⟩ := List.mem_filterMap.mp hr'
                exact defaultRow_body_inv hlook0 hs (hbody r hr))
            simpa [hdef] using hd
        | switch occ' cases' dflt' =>
          have hexhD : DTreeExhaustive ctors ectx.octx
              (.switch occ0 cases (.switch occ' cases' dflt')) := by
            simpa [hdef] using hexh'
          cases hexhD with
          | switchDefault hdne hlookEx htypedEx hsubEx hexhDflt =>
            rename_i TEx tyArgsEx
            rw [hlook0] at hlookEx
            injection hlookEx with hτ
            injection hτ with hT hArgs
            subst hT; subst hArgs
            refine DTreeTypeable.switchDefault hdne hag hlook0 hmem0 htyArgs_lc
              htyped_cases (hsub_cases hsubEx) ?_
            have hd := ihdflt ectx hag ttys hlen'
              (List.nodup_cons.mp hnodup).2
              (fun o ho => hoccs o (List.mem_cons_of_mem _ ho))
              (fun i hi => htys (i + 1) (Nat.succ_lt_succ hi))
              (fun occ hoc o ho suf hsuf =>
                hnochild occ (List.mem_cons_of_mem _ hoc) o ho suf hsuf)
              hoctx_kinded
              (fun r' hr' => by
                obtain ⟨r, hr, hs⟩ := List.mem_filterMap.mp hr'
                exact compile_defaultRow_wf (hMwf r hr) hs)
              (by simpa [hdef] using hexhDflt)
              (fun r' hr' o ho => by
                obtain ⟨r, hr, hs⟩ := List.mem_filterMap.mp hr'
                rcases compile_defaultRow_captured_sub hs o ho with h | hocceq
                · exact hcap r hr o h
                · exact hocceq ▸ hmem0)
              (fun r' hr' => by
                obtain ⟨r, hr, hs⟩ := List.mem_filterMap.mp hr'
                exact defaultRow_body_inv hlook0 hs (hbody r hr))
            simpa [hdef] using hd

/-- **(Typing A compile, FROZEN).** Thread branch typings through `compile` on
    `initMatrix`, producing `DTreeTypeable` (which carries leaf body `TypeOfHM`).

    **Do not change this statement.** Root `EmitTyCtx.agrees` holds from `hlc`
    (`Γ = [mkTrivial τscrut] ++ Γ`, `occEnv = [[]]`, `octx = [([], τscrut)]`).

    **Proof plan for subagent:**
    1. Likely need an auxiliary `compile_typeable_aux` by induction on
       `compile` (mirror `PatComp.compile_ctorSwitches_aux`), threading:
       * `EmitTyCtx.agrees ectx Γ_outer`
       * matrix rows well-formed (`GPatWFList` / `patBindTys` surviving
         `specialize` / `defaultRow` / `pop`)
       * for each row `r` with action `act`, body typing under captures
         reconstructed from `octx` equals `branchBodyEnv` / `patBindTys` of the
         original clause (or a generalized open-body invariant)
    2. At `compile` leaf: build `DTreeTypeable.leaf` from `hbodies` via `bodyFn`
       (acts are row indices `< pats.length`).
    3. At switch: use `MatchExhaustive` = `DTreeExhaustive` structure for
       coverage/`htyped`; extend `Γ`/`occEnv`/`octx` as in `DTreeTypeable.switch*`.
    4. Top theorem = aux at `occs = [[]]`, `M = initMatrix pats`.

    Prefer `composer-2.5-fast`; bump if compile induction / `patBindTys` gets
    nasty. Escape hatch: report obstruction, leave sorry — do not change A/B/C. -/
private theorem initMatrix_captured_empty :
    ∀ (ps : List Surface.Pattern) (k : Nat), ∀ r ∈ initMatrix ps k, r.captured = []
  | [], _, r, hr => by cases hr
  | _ :: ps, k, r, hr => by
    simp only [initMatrix, List.mem_cons] at hr
    rcases hr with rfl | hr
    · rfl
    · exact initMatrix_captured_empty ps (k + 1) r hr

private theorem initMatrix_mem_inv {ps : List Surface.Pattern} {k : Nat} {r : Row}
    (hr : r ∈ initMatrix ps k) :
    ∃ p ∈ ps, r.captured = [] ∧ r.pats = [norm p] ∧
      ∃ i, r.act = k + i ∧ ps[i]? = some p := by
  induction ps generalizing k with
  | nil => cases hr
  | cons q qs ih =>
    simp only [initMatrix, List.mem_cons] at hr
    rcases hr with rfl | hr
    · exact ⟨q, List.mem_cons_self, rfl, rfl, 0, rfl, by simp⟩
    · obtain ⟨p, hp, hcap, hpats, i, hact, hget⟩ := ih hr
      refine ⟨p, List.mem_cons_of_mem _ hp, hcap, hpats, i + 1, by omega, ?_⟩
      simpa [List.getElem?_cons_succ] using hget

/-- **(Typing A compile).** Thread branch typings through `compile` on
    `initMatrix`, producing `DTreeTypeable` (which carries leaf body `TypeOfHM`).

    **Premise note (2026-07-13, strengthened):** root arity follows from global
    `CtorEnv.arityConsistent` + `get? (kindEnvOfCtors ctors) T = some tyArgs.length`.
    Nested field occurrences (foreign / differently-parameterized ADTs under
    `OccCtx.extend`) need the same facts globally, plus `CtorEnv.fieldsKinded` and
    `Ty.WellKinded ke 0` of column types (so `WellKinded_openWith` kinds field
    types). True of any `elabDecls` env at a well-kinded `customTy T tyArgs`;
    thread through `TypeOfHM_lowerMatch` and discharge at the corollary. -/
theorem compile_initMatrix_typeable {ctors : CtorEnv} {Γ : Env} {pats : List Surface.Pattern}
    {bodies' : List Expr} {T : TyName} {tyArgs : List Ty} {τscrut τres : Ty}
    (hτscrut : τscrut = .customTy T tyArgs)
    (hlen : bodies'.length = pats.length)
    (hpats : ∀ p ∈ pats, PatternWF ctors p τscrut)
    (hbodies : ∀ (i : Nat) (hi : i < bodies'.length),
      TypeOfHM ⟨branchBodyEnv Γ (patBindTys ctors (pats[i]'(hlen ▸ hi)) τscrut), ctors⟩
        (bodies'[i]'hi) τres)
    (hexh : MatchExhaustive ctors T tyArgs pats)
    (hlc : τscrut.IsLC)
    (hcons : CtorEnv.arityConsistent ctors)
    (hfields : CtorEnv.fieldsKinded ctors)
    (hkind : LookupList.get? (kindEnvOfCtors ctors) T = some tyArgs.length)
    (hwk : Ty.WellKinded (kindEnvOfCtors ctors) 0 τscrut) :
    DTreeTypeable ctors Γ (bodyFn bodies') τres
      { Γ := PolyTy.mkTrivial τscrut :: Γ, occEnv := [[]],
        octx := [([], τscrut)] }
      (compile [[]] (initMatrix pats)) := by
  subst hτscrut
  refine compile_typeable_aux hcons hfields
    (ectx := { Γ := PolyTy.mkTrivial (.customTy T tyArgs) :: Γ, occEnv := [[]],
               octx := [([], .customTy T tyArgs)] })
    (EmitTyCtx.agrees_root ctors hlc)
    [[]] (initMatrix pats) [.customTy T tyArgs] rfl
    (List.nodup_singleton _)
    (by intro o ho; simpa using ho)
    (fun i hi => by
      have hi0 : i = 0 := by simpa using hi
      subst hi0
      simp only [List.getElem_cons_zero, LookupList.get?]
      exact ⟨rfl, hlc, hwk⟩)
    (fun occ hoc o ho suffix hsuf => by
      simp only [List.mem_singleton] at hoc ho
      subst hoc; subst ho
      intro h
      have : ([] : Occ).length = (suffix).length := by
        simpa using congrArg List.length h
      exact hsuf (List.eq_nil_of_length_eq_zero this.symm))
    (fun {occ T' args} hlook => by
      -- Root octx is a singleton, so the looked-up ADT is exactly `T`/`tyArgs`.
      have hlook' : LookupList.get? ([([], Ty.customTy T tyArgs)] : OccCtx) occ =
          some (.customTy T' args) := hlook
      simp only [LookupList.get?] at hlook'
      split_ifs at hlook'
      injection hlook' with htyeq
      injection htyeq with hT hArgs
      subst hT; subst hArgs
      exact hkind)
    (initMatrix_GPatWFList hpats)
    (by simpa [MatchExhaustive] using hexh)
    (fun r hr o ho => by
      have hcap := initMatrix_captured_empty pats 0 r hr
      rw [hcap] at ho
      cases ho)
    (fun r hr => by
      obtain ⟨p, hp, hcap0, hpats0, i, hact, hget⟩ := initMatrix_mem_inv hr
      have hi : i < pats.length := (List.getElem?_eq_some_iff.mp hget).1
      have hi' : i < bodies'.length := by omega
      have hbody_i := hbodies i hi'
      have hp_eq : pats[i]'(hlen ▸ hi') = p :=
        Option.some.inj ((List.getElem?_eq_getElem hi).symm.trans hget)
      have henv :
          (rowBindTys ctors [([], Ty.customTy T tyArgs)] r.captured r.pats
            [.customTy T tyArgs]).map PolyTy.mkTrivial ++ Γ =
          branchBodyEnv Γ (patBindTys ctors (pats[i]'(hlen ▸ hi')) (.customTy T tyArgs)) := by
        simp only [rowBindTys, hcap0, captureBindTys, List.map_nil, List.nil_append,
          hpats0, patBindTysGList, List.append_nil, branchBodyEnv, patBindTys, hp_eq]
      have hact' : bodyFn bodies' r.act = bodies'[i]'hi' := by
        simp only [bodyFn_get hi', hact, Nat.zero_add]
      simpa [henv, hact'] using hbody_i)


/-! ### Approach A lemma ladder (1a)

Strategy: do **not** transfer typecheck from a weird B1 `emitInner` to canonical
`emit compile`. Instead typecheck what `lower` builds, using open typing of
ingredients from strong `SurfaceWTExpr` (defined in §7). Coverage (`SurfaceCovers`)
remains on the closed transfer / corollary. -/

/-- **Rung 1.** Executable match lowering is exactly `lowerMatch` of lowered parts. -/
theorem lowerExpr_match_decomp {ke : KindEnv} {tvs vs : List ValName}
    {scrut : Surface.Expr} {brs : List (Surface.Pattern × Surface.Expr)} {c : Expr}
    (hlow : lowerExpr ke tvs vs (.match_ scrut brs) = some c) :
    ∃ scrut' bodies',
      lowerExpr ke tvs vs scrut = some scrut' ∧
      lowerBranches ke tvs vs brs = some bodies' ∧
      c = lowerMatch scrut' (brs.map Prod.fst) (bodyFn bodies') := by
  simp only [lowerExpr] at hlow
  cases hs : lowerExpr ke tvs vs scrut with
  | none => simp [hs] at hlow
  | some scrut' =>
    cases hb : lowerBranches ke tvs vs brs with
    | none => simp [hs, hb] at hlow
    | some bodies' =>
      simp only [hs, hb, Option.some.injEq] at hlow
      refine ⟨scrut', bodies', rfl, rfl, ?_⟩
      have hfn : (fun i => bodies'.getD i (.ctor cNil)) = bodyFn bodies' := by
        funext i; simp [bodyFn, matchBodyDefault]
      rw [← hfn, hlow]

/-- **Rung 2.** Canonical `lowerMatch` is typeable from open typings + hygiene. -/
theorem TypeOfHM_lowerMatch {ctors : CtorEnv} {Γ : Env} {scrut' : Expr}
    {bodies' : List Expr} {pats : List Surface.Pattern} {T : TyName} {tyArgs : List Ty}
    {τscrut τres : Ty}
    (hτscrut : τscrut = .customTy T tyArgs)
    (hlen : bodies'.length = pats.length)
    (hscrut : TypeOfHM ⟨Γ, ctors⟩ scrut' τscrut)
    (hpats : ∀ p ∈ pats, PatternWF ctors p τscrut)
    (hbodies : ∀ (i : Nat) (hi : i < bodies'.length),
      TypeOfHM ⟨branchBodyEnv Γ (patBindTys ctors (pats[i]'(hlen ▸ hi)) τscrut), ctors⟩
        (bodies'[i]'hi) τres)
    (hexh : MatchExhaustive ctors T tyArgs pats)
    (hcons : CtorEnv.arityConsistent ctors)
    (hfields : CtorEnv.fieldsKinded ctors)
    (hkind : LookupList.get? (kindEnvOfCtors ctors) T = some tyArgs.length)
    (hwk : Ty.WellKinded (kindEnvOfCtors ctors) 0 τscrut)
    : TypeOfHM ⟨Γ, ctors⟩ (lowerMatch scrut' pats (bodyFn bodies')) τres := by
  have hdt := compile_initMatrix_typeable (Γ := Γ) (bodies' := bodies')
    (hτscrut := hτscrut) (hlen := hlen) (hpats := hpats) (hbodies := hbodies)
    (hexh := hexh) (hlc := TypeOfHM.regular hscrut)
    (hcons := hcons) (hfields := hfields) (hkind := hkind) (hwk := hwk)
  subst hτscrut
  simp only [lowerMatch]
  apply TypeOfHM.letIn (M := PolyTy.mkTrivial (.customTy T tyArgs)) (L := [])
  · simpa [PolyTy.WF, PolyTy.mkTrivial, Ty.IsLC] using TypeOfHM.regular hscrut
  · intro σ hσ; cases hσ
  · exact generalisesTo_of_typeable hscrut
  · rfl
  · exact emit_DTreeTypeable (Γ_outer := Γ) (bodies := bodyFn bodies') hdt

private theorem lowerBranches_length {ke : KindEnv} {tvs vs : List ValName}
    {brs : List (Surface.Pattern × Surface.Expr)} {bodies : List Expr}
    (h : lowerBranches ke tvs vs brs = some bodies) :
    bodies.length = brs.length := by
  induction brs generalizing bodies with
  | nil =>
    simp only [lowerBranches, Option.some.injEq] at h; subst h; rfl
  | cons hd tl ih =>
    simp only [lowerBranches] at h
    cases hb : lowerExpr ke tvs (patVars hd.1 ++ vs) hd.2 with
    | none => simp [hb] at h
    | some b' =>
      cases hrest : lowerBranches ke tvs vs tl with
      | none => simp [hb, hrest] at h
      | some rest' =>
        simp only [hb, hrest, Option.some.injEq] at h; subst h
        simp [ih hrest]

private theorem lowerBranches_get {ke : KindEnv} {tvs vs : List ValName}
    {brs : List (Surface.Pattern × Surface.Expr)} {bodies : List Expr}
    (h : lowerBranches ke tvs vs brs = some bodies) :
    ∀ (i : Nat) (hi : i < brs.length),
      lowerExpr ke tvs (patVars (brs[i]'hi).1 ++ vs) (brs[i]'hi).2 =
        some (bodies[i]'(by simpa [lowerBranches_length h] using hi)) := by
  induction brs generalizing bodies with
  | nil => intro i hi; cases hi
  | cons hd tl ih =>
    simp only [lowerBranches] at h
    cases hb : lowerExpr ke tvs (patVars hd.1 ++ vs) hd.2 with
    | none => simp [hb] at h
    | some b' =>
      cases hrest : lowerBranches ke tvs vs tl with
      | none => simp [hb, hrest] at h
      | some rest' =>
        simp only [hb, hrest, Option.some.injEq] at h; subst h
        intro i hi
        match i with
        | 0 => simpa using hb
        | i' + 1 =>
          have hi' : i' < tl.length := Nat.lt_of_succ_lt_succ hi
          simpa using ih hrest i' hi'

private theorem lowerExprList_length_get {ke : KindEnv} {tvs vs : List ValName}
    {items : List Surface.Expr} {items' : List Expr}
    (h : lowerExprList ke tvs vs items = some items') :
    items'.length = items.length ∧
      ∀ (i : Nat) (hi : i < items.length),
        ∃ hi' : i < items'.length,
          lowerExpr ke tvs vs (items[i]'hi) = some (items'[i]'hi') := by
  induction items generalizing items' with
  | nil =>
    simp only [lowerExprList, Option.some.injEq] at h; subst h
    exact ⟨rfl, fun i hi => by cases hi⟩
  | cons hd tl ih =>
    simp only [lowerExprList] at h
    cases he : lowerExpr ke tvs vs hd with
    | none => simp [he] at h
    | some e' =>
      cases hrest : lowerExprList ke tvs vs tl with
      | none => simp [he, hrest] at h
      | some rest' =>
        simp only [he, hrest, Option.some.injEq] at h; subst h
        have ⟨hlen, hget⟩ := ih hrest
        refine ⟨by simp [hlen], ?_⟩
        intro i hi
        match i with
        | 0 => exact ⟨Nat.zero_lt_succ _, he⟩
        | i' + 1 =>
          have hi' : i' < tl.length := Nat.lt_of_succ_lt_succ hi
          obtain ⟨hi'', hget'⟩ := hget i' hi'
          exact ⟨Nat.succ_lt_succ hi'', hget'⟩

private theorem mkList_TypeOfHM {ctors : CtorEnv} {Γ : Env} {items : List Expr}
    {τelem : Ty}
    (hnil : TypeOfHM ⟨Γ, ctors⟩ (.ctor cNil) (.customTy nList [τelem]))
    (hcons : TypeOfHM ⟨Γ, ctors⟩ (.ctor cCons)
      (.arrow τelem (.arrow (.customTy nList [τelem]) (.customTy nList [τelem]))))
    (hitems : ∀ e ∈ items, TypeOfHM ⟨Γ, ctors⟩ e τelem) :
    TypeOfHM ⟨Γ, ctors⟩ (mkList items) (.customTy nList [τelem]) := by
  induction items with
  | nil => exact hnil
  | cons hd tl ih =>
    exact TypeOfHM.app
      (TypeOfHM.app hcons (hitems hd List.mem_cons_self))
      (ih fun e he => hitems e (List.mem_cons_of_mem _ he))

private theorem lowerBranches_isSome_of_forall {ke : KindEnv} {tvs vs : List ValName}
    {brs : List (Surface.Pattern × Surface.Expr)}
    (h : ∀ (i : Nat) (hi : i < brs.length),
      (lowerExpr ke tvs (patVars (brs[i]'hi).1 ++ vs) (brs[i]'hi).2).isSome) :
    (lowerBranches ke tvs vs brs).isSome := by
  induction brs with
  | nil => simp [lowerBranches]
  | cons hd tl ih =>
    simp only [lowerBranches]
    have hhd := h 0 (by simp)
    simp only [List.getElem_cons_zero] at hhd
    obtain ⟨b', hhd'⟩ := Option.isSome_iff_exists.mp hhd
    have htl := ih fun i hi => by
      simpa [List.getElem_cons_succ] using h (i + 1) (Nat.succ_lt_succ hi)
    obtain ⟨rest', htl'⟩ := Option.isSome_iff_exists.mp htl
    simp [hhd', htl']

private theorem lowerExprList_isSome_of_forall {ke : KindEnv} {tvs vs : List ValName}
    {items : List Surface.Expr}
    (h : ∀ e ∈ items, (lowerExpr ke tvs vs e).isSome) :
    (lowerExprList ke tvs vs items).isSome := by
  induction items with
  | nil => simp [lowerExprList]
  | cons hd tl ih =>
    simp only [lowerExprList]
    obtain ⟨_, hhd⟩ := Option.isSome_iff_exists.mp (h hd List.mem_cons_self)
    obtain ⟨_, htl⟩ := Option.isSome_iff_exists.mp
      (ih fun e he => h e (List.mem_cons_of_mem _ he))
    simp [hhd, htl]

private theorem lowerRecBinds_isSome_of_forall {ke : KindEnv} {tvs recScope : List ValName}
    {binds : List (ValName × Option Surface.PolyTy × Surface.Expr)}
    (h : ∀ (i : Nat) (hi : i < binds.length),
      (lowerExpr ke tvs recScope (binds[i]'hi).2.2).isSome) :
    (lowerRecBinds ke tvs recScope binds).isSome := by
  induction binds with
  | nil => simp [lowerRecBinds]
  | cons hd tl ih =>
    simp only [lowerRecBinds]
    have hhd := h 0 (by simp)
    simp only [List.getElem_cons_zero] at hhd
    obtain ⟨_, hhd'⟩ := Option.isSome_iff_exists.mp hhd
    have htl := ih fun i hi => by
      simpa [List.getElem_cons_succ] using h (i + 1) (Nat.succ_lt_succ hi)
    obtain ⟨_, htl'⟩ := Option.isSome_iff_exists.mp htl
    simp [hhd', htl']

private theorem lowerAnnList_all_none
    {ke : KindEnv} {binds : List (ValName × Option Surface.PolyTy × Surface.Expr)}
    (h : ∀ b ∈ binds, b.2.1 = none) :
    lowerAnnList ke (binds.map (·.2.1)) = some (List.replicate binds.length none) := by
  induction binds with
  | nil => simp [lowerAnnList]
  | cons hd tl ih =>
    have hhd : hd.2.1 = none := h hd List.mem_cons_self
    have htl := ih fun b hb => h b (List.mem_cons_of_mem _ hb)
    simp only [List.map_cons, List.length_cons, List.replicate_succ, lowerAnnList, hhd,
      lowerPolyAnn, htl]

/-- Empty-pool `genGroup` is the trivial scheme. -/
private theorem PolyTy.genGroup_nil' {t : Ty} :
    PolyTy.genGroup [] t = PolyTy.mkTrivial t := by
  have hgf : Ty.genFilter [] t = [] := rfl
  have hcl : Ty.closeOver [] t = t := Ty.closeOver_eq_self_of_fresh (by simp)
  simp only [PolyTy.genGroup, hgf, List.length_nil, hcl, PolyTy.mkTrivial]

private theorem RecSpec.bodyScheme_nil_mono {τ : Ty} :
    RecSpec.bodyScheme [] (.mono τ) = PolyTy.mkTrivial τ :=
  PolyTy.genGroup_nil'

private theorem RecSpec.rhsEntry_nil_mono {τ : Ty} {Xs : List Nat} :
    RecSpec.rhsEntry [] Xs (.mono τ) = PolyTy.mkTrivial τ := by
  simp only [RecSpec.rhsEntry, Ty.renameG_nil_pool, PolyTy.mkTrivial]

/-- Recover the shared index of a `zip` membership when lengths agree. -/
private theorem List.mem_zip_getElem {α β : Type _} {as : List α} {bs : List β}
    {a : α} {b : β} (hlen : as.length = bs.length)
    (h : (a, b) ∈ as.zip bs) :
    ∃ (i : Nat) (hi : i < as.length), as[i] = a ∧ bs[i]'(by omega) = b := by
  induction as generalizing bs with
  | nil =>
    simp only [List.zip_nil_left, List.not_mem_nil] at h
  | cons ahd atl ih =>
    cases bs with
    | nil =>
      simp only [List.zip_nil_right, List.not_mem_nil] at h
    | cons bhd btl =>
      simp only [List.zip_cons_cons, List.mem_cons] at h
      rcases h with hhere | hrest
      · cases hhere
        exact ⟨0, by simp, rfl, rfl⟩
      · have hlen' : atl.length = btl.length := by
          simp only [List.length_cons] at hlen; omega
        obtain ⟨i, hi, ha, hb⟩ := ih hlen' hrest
        exact ⟨i + 1, by simp; omega,
          by simpa [List.getElem_cons_succ] using ha,
          by simpa [List.getElem_cons_succ] using hb⟩

private theorem RecSpec.map_ann_mono (τs : List Ty) :
    (τs.map RecSpec.mono).map RecSpec.ann = List.replicate τs.length none := by
  induction τs with
  | nil => rfl
  | cons _ _ ih => simp [List.replicate_succ, RecSpec.ann, ih]

private theorem lowerRecBinds_length {ke : KindEnv} {tvs recScope : List ValName}
    {binds : List (ValName × Option Surface.PolyTy × Surface.Expr)} {bs' : List Expr}
    (h : lowerRecBinds ke tvs recScope binds = some bs') :
    bs'.length = binds.length := by
  induction binds generalizing bs' with
  | nil =>
    simp only [lowerRecBinds, Option.some.injEq] at h; subst h; rfl
  | cons hd tl ih =>
    simp only [lowerRecBinds] at h
    cases hhd : lowerExpr ke tvs recScope hd.2.2 with
    | none => simp [hhd] at h
    | some e' =>
      cases htl : lowerRecBinds ke tvs recScope tl with
      | none => simp [hhd, htl] at h
      | some rest' =>
        simp only [hhd, htl, Option.some.injEq] at h; subst h
        simp [ih htl]

private theorem lowerRecBinds_get {ke : KindEnv} {tvs recScope : List ValName}
    {binds : List (ValName × Option Surface.PolyTy × Surface.Expr)} {bs' : List Expr}
    (h : lowerRecBinds ke tvs recScope binds = some bs') :
    ∀ (i : Nat) (hi : i < binds.length),
      lowerExpr ke tvs recScope (binds[i]'hi).2.2 =
        some (bs'[i]'(by simpa [lowerRecBinds_length h] using hi)) := by
  induction binds generalizing bs' with
  | nil => intro i hi; cases hi
  | cons hd tl ih =>
    simp only [lowerRecBinds] at h
    cases hhd : lowerExpr ke tvs recScope hd.2.2 with
    | none => simp [hhd] at h
    | some e' =>
      cases htl : lowerRecBinds ke tvs recScope tl with
      | none => simp [hhd, htl] at h
      | some rest' =>
        simp only [hhd, htl, Option.some.injEq] at h; subst h
        intro i hi
        match i with
        | 0 => simpa using hhd
        | i' + 1 =>
          have hi' : i' < tl.length := Nat.lt_of_succ_lt_succ hi
          simpa using ih htl i' hi'

/-- `lowerPoly` yields a well-formed scheme (`PolyTy.WF`). -/
theorem lowerPoly_WF {ke : KindEnv} {σ : Surface.PolyTy} {σ' : PolyTy}
    (h : lowerPoly ke σ = some σ') : PolyTy.WF σ' := by
  simp only [lowerPoly] at h
  obtain ⟨b, hb, rfl⟩ := Option.map_eq_some_iff.mp h
  exact Ty.WellKinded.toContainsBvars (lowerTy_wellKinded hb)

theorem lowerAnn_containsBvars {ke : KindEnv} {tvs : List ValName} {ann : Option Surface.Ty}
    {ann' : Option Ty} (h : lowerAnn ke tvs ann = some ann') :
    ∀ t, ann' = some t → ContainsBvarsUpTo tvs.length t := by
  rintro t ht
  cases ann with
  | none =>
    simp only [lowerAnn, Option.some.injEq] at h; subst h; cases ht
  | some τ =>
    simp only [lowerAnn] at h
    obtain ⟨c, hc, rfl⟩ := Option.map_eq_some_iff.mp h
    obtain ⟨rfl⟩ := ht
    exact Ty.WellKinded.toContainsBvars (lowerTy_wellKinded hc)

theorem lowerPolyAnn_containsBvars {ke : KindEnv} {tvs : List ValName}
    {ann : Option Surface.PolyTy} {ann' : Option PolyTy}
    (h : lowerPolyAnn ke ann = some ann') :
    ∀ σ, ann' = some σ → ContainsBvarsUpTo (tvs.length + σ.paramCount) σ.body := by
  rintro σ ht
  cases ann with
  | none =>
    simp only [lowerPolyAnn, Option.some.injEq] at h; subst h; cases ht
  | some σs =>
    simp only [lowerPolyAnn] at h
    obtain ⟨σ', hσ, rfl⟩ := Option.map_eq_some_iff.mp h
    obtain ⟨rfl⟩ := ht
    have hwf : ContainsBvarsUpTo σ.paramCount σ.body := lowerPoly_WF hσ
    exact ContainsBvarsUpTo.mono (m := σ.paramCount) (n := tvs.length + σ.paramCount)
      (Nat.le_add_left σ.paramCount tvs.length) hwf

private theorem lowerAnnList_length {ke : KindEnv}
    {as : List (Option Surface.PolyTy)} {as' : List (Option PolyTy)}
    (h : lowerAnnList ke as = some as') : as'.length = as.length := by
  induction as generalizing as' with
  | nil =>
    simp only [lowerAnnList, Option.some.injEq] at h; subst h; rfl
  | cons a as ih =>
    simp only [lowerAnnList] at h
    cases ha : lowerPolyAnn ke a with
    | none => simp [ha] at h
    | some a' =>
      cases has : lowerAnnList ke as with
      | none => simp [ha, has] at h
      | some as'' =>
        simp only [ha, has, Option.some.injEq] at h; subst h
        simp [ih has]

theorem lowerAnnList_containsBvars {ke : KindEnv} {tvs : List ValName} :
    ∀ {as : List (Option Surface.PolyTy)} {as' : List (Option PolyTy)},
      lowerAnnList ke as = some as' →
      ∀ σ, some σ ∈ as' → ContainsBvarsUpTo (tvs.length + σ.paramCount) σ.body := by
  intro as as' h σ hσ
  induction as generalizing as' with
  | nil =>
    simp only [lowerAnnList, Option.some.injEq] at h; subst h; cases hσ
  | cons a as ih =>
    simp only [lowerAnnList] at h
    cases ha : lowerPolyAnn ke a with
    | none => simp [ha] at h
    | some a' =>
      cases htl : lowerAnnList ke as with
      | none => simp [ha, htl] at h
      | some as'' =>
        simp only [ha, htl, Option.some.injEq] at h; subst h
        simp only [List.mem_cons] at hσ
        rcases hσ with hσhead | hσtail
        · subst hσhead
          exact lowerPolyAnn_containsBvars ha σ rfl
        · exact ih htl hσtail

private theorem TyBvarBounded_BranchList_append_wildcard (n : Nat) :
    ∀ (cs : List (MatchPattern × Expr)) (e : Expr),
      Expr.TyBvarBounded.BranchList n (cs ++ [(.wildcard, e)]) ↔
        Expr.TyBvarBounded.BranchList n cs ∧ e.TyBvarBounded n := by
  intro cs; induction cs with
  | nil => intro e; simp [Expr.TyBvarBounded.BranchList]
  | cons hd tl ih =>
    obtain ⟨p, b⟩ := hd
    intro e
    constructor
    · intro h
      dsimp [Expr.TyBvarBounded.BranchList, List.cons_append] at h ⊢
      rcases (ih e).mp h.2 with ⟨hrest, he⟩
      exact And.intro (And.intro h.1 hrest) he
    · intro h
      rcases h with ⟨hcs, he⟩
      rcases hcs with ⟨hb, hrest⟩
      dsimp [Expr.TyBvarBounded.BranchList, List.cons_append]
      exact And.intro hb ((ih e).mpr (And.intro hrest he))

/-! ### Frozen: surface-lowered terms are `TyBvarBounded tvs.length`

Needed so the `letInAnn` ladder can collapse
`openBoundTyVars (some σ) Xs rhs = rhs.openTyVars Xs` to `rhs` via
`Expr.openTyVarsAux_eq_self_of_tyBvarBounded` when `tvs = []` (the `SurfaceWT`
case). Mirror the existing `*_tyFreeVars` / `emit_tyFreeVars` layer.

Emit helpers are depth-parametric (`n`) so they compose under nonempty `tvs`. -/

private theorem emitLets_tyBvarBounded (n : Nat) (env : List Occ) (binds : List Occ)
    (body : Expr) (hb : body.TyBvarBounded n) :
    (emitLets env binds body).TyBvarBounded n := by
  unfold emitLets
  have hshift : (body.shiftFrom binds.length env.length).TyBvarBounded n :=
    Expr.shiftFrom_tyBvarBounded env.length binds.length n hb
  suffices ∀ rest depth,
      (emitLets.go env binds body rest depth).TyBvarBounded n from this _ _
  intro rest; induction rest with
  | nil => intro depth; exact hshift
  | cons _ rest ih =>
    intro depth
    simp only [emitLets.go, Expr.TyBvarBounded]
    refine And.intro ?_ (ih (depth + 1))
    intro t ht; cases ht

mutual
private theorem emit_tyBvarBounded (n : Nat) (env : List Occ) (bodies : Nat → Expr)
    (t : DTree) (hb : ∀ i, (bodies i).TyBvarBounded n) :
    (emit env bodies t).TyBvarBounded n := by
  match t with
  | .fail =>
    rw [emit]
    simp only [Expr.TyBvarBounded, Expr.TyBvarBounded.BranchList]
    trivial
  | .leaf act binds =>
    rw [emit]
    exact emitLets_tyBvarBounded n env binds (bodies act) (hb act)
  | .switch occ cases dflt =>
    cases dflt with
    | fail =>
      rw [emit]
      have hcases := emitCases_tyBvarBounded n env bodies occ cases hb
      simp only [Expr.TyBvarBounded, resolveOcc, List.append_nil]
      exact And.intro (by intro t ht; cases ht) hcases
    | leaf act binds =>
      rw [emit]
      have hcases := emitCases_tyBvarBounded n env bodies occ cases hb
      have hd := emit_tyBvarBounded n env bodies (.leaf act binds) hb
      simp only [Expr.TyBvarBounded, resolveOcc]
      refine And.intro ?_ ((TyBvarBounded_BranchList_append_wildcard n _ _).mpr (And.intro hcases hd))
      intro t ht; cases ht
      intro h; cases h
    | switch occ' cases' dflt' =>
      rw [emit]
      have hcases := emitCases_tyBvarBounded n env bodies occ cases hb
      have hd := emit_tyBvarBounded n env bodies (.switch occ' cases' dflt') hb
      simp only [Expr.TyBvarBounded, resolveOcc]
      refine And.intro ?_ ((TyBvarBounded_BranchList_append_wildcard n _ _).mpr (And.intro hcases hd))
      intro t ht; cases ht
      intro h; cases h

private theorem emitCases_tyBvarBounded (n : Nat) (env : List Occ) (bodies : Nat → Expr)
    (occ : Occ) (cases : List (CtorName × Nat × DTree))
    (hb : ∀ i, (bodies i).TyBvarBounded n) :
    Expr.TyBvarBounded.BranchList n (emitCases env bodies occ cases) := by
  match cases with
  | [] => exact trivial
  | (_c, a, t) :: rest =>
    simp only [emitCases, Expr.TyBvarBounded.BranchList]
    exact And.intro (emit_tyBvarBounded n (subOccs occ a ++ env) bodies t hb)
      (emitCases_tyBvarBounded n env bodies occ rest hb)
end

theorem lowerMatch_tyBvarBounded (n : Nat) (scrut : Expr) (pats : List Surface.Pattern)
    (bodies : Nat → Expr)
    (hs : scrut.TyBvarBounded n) (hb : ∀ i, (bodies i).TyBvarBounded n) :
    (lowerMatch scrut pats bodies).TyBvarBounded n := by
  simp only [lowerMatch, Expr.TyBvarBounded]
  exact And.intro hs (emit_tyBvarBounded n [[]] bodies (compile [[]] (initMatrix pats)) hb)

theorem mkList_tyBvarBounded (n : Nat) :
    ∀ (items : List Expr), (∀ e ∈ items, e.TyBvarBounded n) →
      (mkList items).TyBvarBounded n
  | [], _ => by simp [mkList, Expr.TyBvarBounded]
  | x :: xs, h => by
    simp only [mkList, Expr.TyBvarBounded]
    constructor
    · constructor
      · trivial
      · exact h x List.mem_cons_self
    · exact mkList_tyBvarBounded n xs fun e he => h e (List.mem_cons_of_mem _ he)

mutual
theorem lowerExpr_tyBvarBounded {ke : KindEnv} {tvs vs : List ValName} :
    ∀ {s : Surface.Expr} {c : Expr},
      lowerExpr ke tvs vs s = some c → c.TyBvarBounded tvs.length := by
  intro s c h
  match s with
  | .primLit (.bool _) =>
    simp only [lowerExpr, Option.some.injEq] at h; subst h; simp [Expr.TyBvarBounded]
  | .primLit .unit | .primLit (.int _) | .primLit (.nat _) | .primLit (.char _) =>
    simp only [lowerExpr, Option.some.injEq] at h; subst h; simp [Expr.TyBvarBounded]
  | .pair a b =>
    simp only [lowerExpr] at h
    cases ha : lowerExpr ke tvs vs a with
    | none => simp [ha] at h
    | some a' =>
      cases hb : lowerExpr ke tvs vs b with
      | none => simp [ha, hb] at h
      | some b' =>
        simp only [ha, hb, Option.some.injEq] at h; subst h
        simp only [Expr.TyBvarBounded]
        constructor
        · constructor
          · trivial
          · exact lowerExpr_tyBvarBounded ha
        · exact lowerExpr_tyBvarBounded hb
  | .cons hd tl =>
    simp only [lowerExpr] at h
    cases ha : lowerExpr ke tvs vs hd with
    | none => simp [ha] at h
    | some h' =>
      cases hb : lowerExpr ke tvs vs tl with
      | none => simp [ha, hb] at h
      | some t' =>
        simp only [ha, hb, Option.some.injEq] at h; subst h
        simp only [Expr.TyBvarBounded]
        constructor
        · constructor
          · trivial
          · exact lowerExpr_tyBvarBounded ha
        · exact lowerExpr_tyBvarBounded hb
  | .list items =>
    simp only [lowerExpr] at h
    cases hi : lowerExprList ke tvs vs items with
    | none => simp [hi] at h
    | some items' =>
      simp only [hi, Option.some.injEq] at h; subst h
      exact mkList_tyBvarBounded tvs.length items' (lowerExprList_tyBvarBounded hi)
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
          simp only [Expr.TyBvarBounded]
          exact ⟨lowerAnn_containsBvars hann, lowerExpr_tyBvarBounded hb⟩
      | wildcard =>
        cases hb : lowerExpr ke tvs (.mk "_" :: vs) body with
        | none => simp [hann, hb] at h
        | some b' =>
          simp only [hann, hb, Option.some.injEq] at h; subst h
          simp only [Expr.TyBvarBounded]
          exact ⟨lowerAnn_containsBvars hann, lowerExpr_tyBvarBounded hb⟩
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
        simp only [Expr.TyBvarBounded]
        exact ⟨lowerExpr_tyBvarBounded hf, lowerExpr_tyBvarBounded hx⟩
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
          cases ann' with
          | none =>
            simp only [Expr.TyBvarBounded]
            exact ⟨lowerExpr_tyBvarBounded hr, lowerExpr_tyBvarBounded hb⟩
          | some σ =>
            simp only [Expr.TyBvarBounded]
            refine ⟨lowerPolyAnn_containsBvars hann σ rfl, ?_, lowerExpr_tyBvarBounded hb⟩
            exact Expr.TyBvarBounded.mono (lowerExpr_tyBvarBounded hr) (by omega)
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
          simp only [Expr.TyBvarBounded]
          refine ⟨?_, ?_, lowerExpr_tyBvarBounded hb⟩
          · intro σ hσ; exact lowerAnnList_containsBvars hann σ hσ
          · exact Expr.TyBvarBounded.RecGroup_of_zip
              (by
                have h1 := lowerRecBinds_length hbinds
                have h2 := lowerAnnList_length hann
                rw [h1, h2, List.length_map])
              (by
                intro p hp
                have he := (List.of_mem_zip hp).1
                exact Expr.TyBvarBounded.mono (lowerRecBinds_tyBvarBounded hbinds _ he)
                  (Nat.le_add_right _ _))
  | .var name =>
    simp only [lowerExpr] at h
    cases hi : tvarIndex vs name with
    | none => simp [hi] at h
    | some i =>
      simp only [hi, Option.some.injEq] at h; subst h
      simp only [Expr.TyBvarBounded]
      intro t ht; cases ht
  | .ctor name =>
    simp only [lowerExpr, Option.some.injEq] at h; subst h; simp [Expr.TyBvarBounded]
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
          exact lowerMatch_tyBvarBounded tvs.length c' _ _ (lowerExpr_tyBvarBounded hc) (fun i => by
            rw [List.getD]
            match i with
            | 0 => simpa [Option.getD] using lowerExpr_tyBvarBounded ht
            | 1 => simpa [Option.getD] using lowerExpr_tyBvarBounded hf
            | _ + 2 => simp [Option.getD, Expr.TyBvarBounded])
  | .match_ scrut brs =>
    simp only [lowerExpr] at h
    cases hs : lowerExpr ke tvs vs scrut with
    | none => simp [hs] at h
    | some scrut' =>
      cases hb : lowerBranches ke tvs vs brs with
      | none => simp [hs, hb] at h
      | some bodies' =>
        simp only [hs, hb, Option.some.injEq] at h; subst h
        exact lowerMatch_tyBvarBounded tvs.length scrut' _ (bodyFn bodies')
          (lowerExpr_tyBvarBounded hs) (fun i => by
            change (bodies'.getD i matchBodyDefault).TyBvarBounded tvs.length
            rw [List.getD]
            cases hget : bodies'[i]? with
            | none => simp [Option.getD, matchBodyDefault, Expr.TyBvarBounded]
            | some e =>
              simp only [Option.getD]
              exact lowerBranches_tyBvarBounded hb e (List.mem_of_getElem? hget))

theorem lowerExprList_tyBvarBounded {ke : KindEnv} {tvs vs : List ValName} :
    ∀ {es : List Surface.Expr} {es' : List Expr},
      lowerExprList ke tvs vs es = some es' →
      ∀ e ∈ es', e.TyBvarBounded tvs.length := by
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
        · exact lowerExpr_tyBvarBounded he0
        · exact lowerExprList_tyBvarBounded hrest e he

theorem lowerBranches_tyBvarBounded {ke : KindEnv} {tvs vs : List ValName} :
    ∀ {brs : List (Surface.Pattern × Surface.Expr)} {bodies' : List Expr},
      lowerBranches ke tvs vs brs = some bodies' →
      ∀ e ∈ bodies', e.TyBvarBounded tvs.length := by
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
        · exact lowerExpr_tyBvarBounded hb
        · exact lowerBranches_tyBvarBounded hrest e he

theorem lowerRecBinds_tyBvarBounded {ke : KindEnv} {tvs recScope : List ValName} :
    ∀ {binds : List (ValName × Option Surface.PolyTy × Surface.Expr)} {bs' : List Expr},
      lowerRecBinds ke tvs recScope binds = some bs' →
      ∀ e ∈ bs', e.TyBvarBounded tvs.length := by
  intro binds bs' h e he
  match binds with
  | [] =>
    simp only [lowerRecBinds, Option.some.injEq] at h; subst h; cases he
  | (_, _, e0) :: rest =>
    simp only [lowerRecBinds] at h
    cases he0 : lowerExpr ke tvs recScope e0 with
    | none => simp [he0] at h
    | some e0' =>
      cases hrest : lowerRecBinds ke tvs recScope rest with
      | none => simp [he0, hrest] at h
      | some rest' =>
        simp only [he0, hrest, Option.some.injEq] at h; subst h
        simp only [List.mem_cons] at he
        rcases he with rfl | he
        · exact lowerExpr_tyBvarBounded he0
        · exact lowerRecBinds_tyBvarBounded hrest e he
end

/-- `SurfaceWTExpr` ⇒ `lowerExpr` succeeds. -/
theorem lowerExpr_isSome_of_SurfaceWTExpr {ctors : CtorEnv} {ke : KindEnv}
    {tvs vs : List ValName} {Γ : Env} {s : Surface.Expr} {τ : Ty}
    (hwt : SurfaceWTExpr ctors ke tvs vs Γ s τ) :
    (lowerExpr ke tvs vs s).isSome := by
  induction hwt with
  | of_lowers _ hL _ => exact lowerExpr_isSome_of_LowersExpr hL
  | pair _ _ _ iha ihb =>
    simp only [lowerExpr]
    obtain ⟨_, ha⟩ := Option.isSome_iff_exists.mp iha
    obtain ⟨_, hb⟩ := Option.isSome_iff_exists.mp ihb
    simp [ha, hb]
  | cons _ _ _ iha ihb =>
    simp only [lowerExpr]
    obtain ⟨_, ha⟩ := Option.isSome_iff_exists.mp iha
    obtain ⟨_, hb⟩ := Option.isSome_iff_exists.mp ihb
    simp [ha, hb]
  | list _ _ _ ih =>
    simp only [lowerExpr]
    obtain ⟨_, hlist'⟩ := Option.isSome_iff_exists.mp (lowerExprList_isSome_of_forall ih)
    simp [hlist']
  | app _ _ ihf ihx =>
    simp only [lowerExpr]
    obtain ⟨_, hf⟩ := Option.isSome_iff_exists.mp ihf
    obtain ⟨_, hx⟩ := Option.isSome_iff_exists.mp ihx
    simp [hf, hx]
  | lambda_name =>
    rename_i vs Γ x ann body paramTy bodyTy hlc hann _hb ihb
    simp only [lowerExpr]
    cases hAnn : lowerAnn ke tvs ann with
    | none =>
      cases ann with
      | none => simp [lowerAnn] at hAnn
      | some τs =>
        have : lowerTy ke tvs τs = some paramTy := by simpa using hann
        simp [lowerAnn, this] at hAnn
    | some annL =>
      obtain ⟨_, hb⟩ := Option.isSome_iff_exists.mp ihb
      simp [hb]
  | lambda_wild =>
    rename_i vs Γ ann body paramTy bodyTy hlc hann _hb ihb
    simp only [lowerExpr]
    cases hAnn : lowerAnn ke tvs ann with
    | none =>
      cases ann with
      | none => simp [lowerAnn] at hAnn
      | some τs =>
        have : lowerTy ke tvs τs = some paramTy := by simpa using hann
        simp [lowerAnn, this] at hAnn
    | some annL =>
      obtain ⟨_, hb⟩ := Option.isSome_iff_exists.mp ihb
      simp [hb]
  | letIn =>
    rename_i vs Γ name rhs body τrhs τ _hr _hb ihr ihb
    simp only [lowerExpr, lowerPolyAnn]
    obtain ⟨_, hr⟩ := Option.isSome_iff_exists.mp ihr
    obtain ⟨_, hb⟩ := Option.isSome_iff_exists.mp ihb
    simp [hr, hb]
  | letInAnn =>
    rename_i vs Γ name σs σ rhs body τ L htvs hσ hσwf _hrhs_forall _hb ihr ihb
    simp only [lowerExpr, lowerPolyAnn, hσ, Option.map_some]
    obtain ⟨Xs, hXlen, hXnodup, hXavoid⟩ := exists_fresh_names L σ.paramCount
    have hfresh : FreshNames L σ.paramCount Xs := ⟨hXlen, hXnodup, hXavoid⟩
    obtain ⟨_, hr⟩ := Option.isSome_iff_exists.mp (ihr Xs hfresh)
    obtain ⟨_, hb⟩ := Option.isSome_iff_exists.mp ihb
    simp [hr, hb]
  | letRecIn =>
    rename_i vs Γ binds τs body τ hlen hann _hbinds _hb ihbinds ihb
    simp only [lowerExpr]
    have hann' := lowerAnnList_all_none (ke := ke) hann
    obtain ⟨_, hb⟩ := Option.isSome_iff_exists.mp ihb
    obtain ⟨_, hbinds'⟩ := Option.isSome_iff_exists.mp
      (lowerRecBinds_isSome_of_forall ihbinds)
    simp [hann', hbinds', hb]
  | letRecInAnn =>
    rename_i vs Γ binds anns' specs G L body τ htvs hann hlen hanns_eq hnodup hmono_lc hpoly_wf
      hmono hpoly hbody hmono_ih hpoly_ih hbody_ih
    simp only [lowerExpr]
    obtain ⟨_, hb⟩ := Option.isSome_iff_exists.mp (by simpa using hbody_ih)
    obtain ⟨Xs, hXlen, hXnodup, hXavoid⟩ := exists_fresh_names L G.length
    have hfresh : FreshNames L G.length Xs := ⟨hXlen, hXnodup, hXavoid⟩
    have hbinds_forall : ∀ (i : Nat) (hi : i < binds.length),
        (lowerExpr ke tvs (binds.map (·.1) ++ vs) (binds[i]'hi).2.2).isSome := by
      intro i hi
      cases hspec : specs[i]'(Nat.lt_of_lt_of_eq hi hlen) with
      | mono τm => simpa using hmono_ih Xs hfresh i hi τm hspec
      | poly σ =>
        obtain ⟨Ys, hYlen, hYnodup, hYavoid⟩ := exists_fresh_names (L ++ Xs) σ.paramCount
        have hfreshY : FreshNames (L ++ Xs) σ.paramCount Ys := ⟨hYlen, hYnodup, hYavoid⟩
        simpa using hpoly_ih Xs hfresh i hi σ hspec Ys hfreshY
    obtain ⟨_, hbinds'⟩ := Option.isSome_iff_exists.mp
      (lowerRecBinds_isSome_of_forall hbinds_forall)
    simp [hann, hbinds', hb]
  | match_ _ _ _ _ _ _ ihs ihbrs =>
    simp only [lowerExpr]
    obtain ⟨_, hs⟩ := Option.isSome_iff_exists.mp ihs
    obtain ⟨_, hb'⟩ := Option.isSome_iff_exists.mp (lowerBranches_isSome_of_forall ihbrs)
    simp [hs, hb']
  | ife _ _ _ _ _ _ _ ihc iht ihf =>
    simp only [lowerExpr]
    obtain ⟨_, hc⟩ := Option.isSome_iff_exists.mp ihc
    obtain ⟨_, ht⟩ := Option.isSome_iff_exists.mp iht
    obtain ⟨_, hf⟩ := Option.isSome_iff_exists.mp ihf
    simp [hc, ht, hf]

/-- **Rung 3.** Open transfer: `SurfaceWTExpr` + `lowerExpr` ⇒ `TypeOfHM` at same `τ`. -/
theorem TypeOfHM_of_lowerExpr_of_SurfaceWTExpr {ctors : CtorEnv} {ke : KindEnv}
    {tvs vs : List ValName} {Γ : Env} {s : Surface.Expr} {c : Expr} {τ : Ty}
    (hwt : SurfaceWTExpr ctors ke tvs vs Γ s τ)
    (hlow : lowerExpr ke tvs vs s = some c)
    (hcons : CtorEnv.arityConsistent ctors)
    (hfields : CtorEnv.fieldsKinded ctors) :
    TypeOfHM ⟨Γ, ctors⟩ c τ := by
  induction hwt generalizing c with
  | of_lowers hnm hL hT =>
    have heq := lowerExpr_eq_of_LowersExpr_of_NoMatch hnm hL hlow
    simpa [heq] using hT
  | pair =>
    rename_i vs Γ a b τa τb τ ha hb hctor iha ihb
    simp only [lowerExpr] at hlow
    cases haL : lowerExpr ke tvs vs a with
    | none => simp [haL] at hlow
    | some aL =>
      cases hbL : lowerExpr ke tvs vs b with
      | none => simp [haL, hbL] at hlow
      | some bL =>
        simp only [haL, hbL, Option.some.injEq] at hlow; subst hlow
        exact TypeOfHM.app (TypeOfHM.app hctor (iha haL)) (ihb hbL)
  | cons =>
    rename_i vs Γ h t τh τt τ hh ht hctor ihh iht
    simp only [lowerExpr] at hlow
    cases hhL : lowerExpr ke tvs vs h with
    | none => simp [hhL] at hlow
    | some hL =>
      cases htL : lowerExpr ke tvs vs t with
      | none => simp [hhL, htL] at hlow
      | some tL =>
        simp only [hhL, htL, Option.some.injEq] at hlow; subst hlow
        exact TypeOfHM.app (TypeOfHM.app hctor (ihh hhL)) (iht htL)
  | list =>
    rename_i vs Γ items τelem hitems hnil hconsC ih
    simp only [lowerExpr] at hlow
    cases hi : lowerExprList ke tvs vs items with
    | none => simp [hi] at hlow
    | some items' =>
      simp only [hi, Option.some.injEq] at hlow; subst hlow
      have ⟨hlen, hget⟩ := lowerExprList_length_get hi
      apply mkList_TypeOfHM hnil hconsC
      intro e' he'
      obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp he'
      have hiS : i < items.length := by omega
      obtain ⟨_, hlowi⟩ := hget i hiS
      exact ih (items[i]'hiS) (List.getElem_mem hiS) hlowi
  | app =>
    rename_i vs Γ f x τarg τ hf hx ihf ihx
    simp only [lowerExpr] at hlow
    cases hfL : lowerExpr ke tvs vs f with
    | none => simp [hfL] at hlow
    | some fL =>
      cases hxL : lowerExpr ke tvs vs x with
      | none => simp [hfL, hxL] at hlow
      | some xL =>
        simp only [hfL, hxL, Option.some.injEq] at hlow; subst hlow
        exact TypeOfHM.app (ihf hfL) (ihx hxL)
  | lambda_name =>
    rename_i vs Γ x ann body paramTy bodyTy hlc hann hb ihb
    simp only [lowerExpr] at hlow
    cases hann' : lowerAnn ke tvs ann with
    | none => simp [hann'] at hlow
    | some annL =>
      cases hbL : lowerExpr ke tvs (x :: vs) body with
      | none => simp [hann', hbL] at hlow
      | some bL =>
        simp only [hann', hbL, Option.some.injEq] at hlow; subst hlow
        have hpins : annL.Pins paramTy := by
          intro a ha
          cases ann with
          | none =>
            simp only [lowerAnn, Option.some.injEq] at hann'; subst hann'
            cases ha
          | some τs =>
            have : lowerTy ke tvs τs = some paramTy := by simpa using hann
            simp only [lowerAnn, this, Option.map_some, Option.some.injEq] at hann'
            subst hann'; cases ha; rfl
        exact TypeOfHM.lambda hlc hpins rfl (ihb hbL)
  | lambda_wild =>
    rename_i vs Γ ann body paramTy bodyTy hlc hann hb ihb
    simp only [lowerExpr] at hlow
    cases hann' : lowerAnn ke tvs ann with
    | none => simp [hann'] at hlow
    | some annL =>
      cases hbL : lowerExpr ke tvs (.mk "_" :: vs) body with
      | none => simp [hann', hbL] at hlow
      | some bL =>
        simp only [hann', hbL, Option.some.injEq] at hlow; subst hlow
        have hpins : annL.Pins paramTy := by
          intro a ha
          cases ann with
          | none =>
            simp only [lowerAnn, Option.some.injEq] at hann'; subst hann'
            cases ha
          | some τs =>
            have : lowerTy ke tvs τs = some paramTy := by simpa using hann
            simp only [lowerAnn, this, Option.map_some, Option.some.injEq] at hann'
            subst hann'; cases ha; rfl
        exact TypeOfHM.lambda hlc hpins rfl (ihb hbL)
  | letIn =>
    rename_i vs Γ name rhs body τrhs τ _hr _hb ihr ihb
    simp only [lowerExpr] at hlow
    -- ann is definitionally `none`
    cases hrL : lowerExpr ke tvs vs rhs with
    | none => simp [lowerPolyAnn, hrL] at hlow
    | some rhsL =>
      cases hbL : lowerExpr ke tvs (name :: vs) body with
      | none => simp [lowerPolyAnn, hrL, hbL] at hlow
      | some bodyL =>
        simp only [lowerPolyAnn, hrL, hbL, Option.some.injEq] at hlow; subst hlow
        have hTyR := ihr hrL
        refine TypeOfHM.letIn (M := PolyTy.mkTrivial τrhs) (L := [])
          (by simpa [PolyTy.WF, PolyTy.mkTrivial] using TypeOfHM.regular hTyR)
          (fun _ h => Option.noConfusion h)
          (generalisesTo_of_typeable hTyR) rfl (ihb hbL)
  | letInAnn =>
    rename_i vs Γ name σs σ rhs body τ L htvs hσ hσwf _hrhs_forall _hb ihr ihb
    simp only [lowerExpr, lowerPolyAnn, hσ, Option.map_some] at hlow
    cases hrL : lowerExpr ke tvs vs rhs with
    | none =>
      simp only [hrL] at hlow
      injection hlow
    | some rhsL =>
      cases hbL : lowerExpr ke tvs (name :: vs) body with
      | none =>
        simp only [hrL, hbL] at hlow
        injection hlow
      | some bodyL =>
        simp only [hrL, hbL, Option.some.injEq] at hlow
        subst hlow
        have hpins : (some σ).Pins σ := fun _ ha => by cases ha; rfl
        refine TypeOfHM.letIn (M := σ) (L := L) hσwf hpins ?_ rfl (ihb hbL)
        intro Xs hfresh
        have hTyR := ihr Xs hfresh hrL
        have hopen : rhsL.openTyVarsAux 0 Xs = rhsL :=
          Expr.openTyVarsAux_eq_self_of_tyBvarBounded Xs rhsL 0
            (by simpa [htvs] using lowerExpr_tyBvarBounded hrL)
        simpa [Expr.openBoundTyVars, Expr.openTyVars, hopen] using hTyR
  | letRecIn =>
    rename_i vs Γ binds τs body τ hlen hann _hbinds _hb ihbinds ihb
    simp only [lowerExpr] at hlow
    have hann' := lowerAnnList_all_none (ke := ke) hann
    cases hbindsL : lowerRecBinds ke tvs (binds.map (·.1) ++ vs) binds with
    | none => simp [hann', hbindsL] at hlow
    | some bindings' =>
      cases hbL : lowerExpr ke tvs (binds.map (·.1) ++ vs) body with
      | none => simp [hann', hbindsL, hbL] at hlow
      | some bodyL =>
        simp only [hann', hbindsL, hbL, Option.some.injEq] at hlow; subst hlow
        have hlenB := lowerRecBinds_length hbindsL
        have hgetB := lowerRecBinds_get hbindsL
        set specs : List RecSpec := τs.map RecSpec.mono with hspecs
        have hanns_eq : specs.map RecSpec.ann =
            List.replicate binds.length (none : Option PolyTy) := by
          simpa [specs, hlen] using RecSpec.map_ann_mono τs
        have hwf : RecSpecs.WF (List.replicate binds.length none) bindings' specs [] := by
          refine ⟨hanns_eq, ?_, List.nodup_nil, ?_, ?_⟩
          · simp only [specs, List.length_map, hlenB, hlen]
          · intro τm hτ
            simp only [specs, List.mem_map] at hτ
            obtain ⟨τ', hτ', hτeq⟩ := hτ
            cases hτeq
            obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hτ'
            have hiB : i < binds.length := by omega
            exact TypeOfHM.regular (ihbinds i hiB (hgetB i hiB))
          · intro σ hσ
            simp only [specs, List.mem_map] at hσ
            obtain ⟨_, _, hcontrad⟩ := hσ
            cases hcontrad
        refine TypeOfHM.letRec (specs := specs) (G := []) (L := [])
          hwf ?mono ?poly rfl ?body
        · -- MonoTyped at empty pool
          intro Xs hXs p hp τ0 hτ0
          have hXs_nil : Xs = [] := List.eq_nil_of_length_eq_zero hXs.length
          subst hXs_nil
          obtain ⟨b, s⟩ := p
          have hs : s = .mono τ0 := hτ0
          subst hs
          simp only [RecSpecs.rhsCtx, Ty.renameG_nil_pool]
          have hzip_len : bindings'.length = specs.length := by
            simp only [specs, List.length_map, hlenB, hlen]
          obtain ⟨i, hi, hb_eq, hs_eq⟩ := List.mem_zip_getElem hzip_len hp
          subst hb_eq
          have hτs : τs[i]'(by omega) = τ0 := by
            simp only [specs, List.getElem_map, RecSpec.mono.injEq] at hs_eq
            exact hs_eq
          have henv : specs.map (RecSpec.rhsEntry [] []) = τs.map PolyTy.mkTrivial := by
            simp only [specs, List.map_map]
            exact List.map_congr_left fun _ _ => RecSpec.rhsEntry_nil_mono
          rw [henv, ← hτs]
          exact ihbinds i (by omega) (hgetB i (by omega))
        · -- PolyTyped: no poly specs
          intro Xs _hXs p hp σ hσ
          have hs := (List.of_mem_zip hp).2
          simp only [specs, List.mem_map] at hs
          obtain ⟨_, _, hcontrad⟩ := hs
          rw [hσ] at hcontrad
          cases hcontrad
        · -- body under empty-pool bodyCtx = mkTrivial schemes
          simp only [RecSpecs.bodyCtx, specs, List.map_map]
          have hmap : List.map (RecSpec.bodyScheme [] ∘ RecSpec.mono) τs =
              τs.map PolyTy.mkTrivial :=
            List.map_congr_left fun _ _ => RecSpec.bodyScheme_nil_mono
          rw [hmap]
          exact ihb hbL
  | letRecInAnn =>
    rename_i vs Γ binds anns' specs G L body τ htvs hann hlen hanns_eq hnodup hmono_lc hpoly_wf
      hmono hpoly hbody hmono_ih hpoly_ih hbody_ih
    simp only [lowerExpr, hann] at hlow
    cases hbindsL : lowerRecBinds ke tvs (binds.map (·.1) ++ vs) binds with
    | none => simp [hbindsL] at hlow
    | some bindings' =>
      cases hbL : lowerExpr ke tvs (binds.map (·.1) ++ vs) body with
      | none => simp [hbindsL, hbL] at hlow
      | some bodyL =>
        simp only [hbindsL, hbL, Option.some.injEq] at hlow; subst hlow
        have hlenB := lowerRecBinds_length hbindsL
        have hgetB := lowerRecBinds_get hbindsL
        have hwf : RecSpecs.WF anns' bindings' specs G :=
          ⟨hanns_eq, hlenB.trans hlen, hnodup, hmono_lc, hpoly_wf⟩
        exact TypeOfHM.letRec (specs := specs) (G := G) (L := L) hwf
          (by
            intro Xs hfresh p hp τ hτ
            have hzip_len : bindings'.length = specs.length := hwf.length
            obtain ⟨i, hi, hb_eq, hs_eq⟩ := List.mem_zip_getElem hzip_len hp
            have hspec_i : specs[i] = .mono τ := hs_eq.trans hτ
            simpa [RecSpecs.rhsCtx, hb_eq] using
              hmono_ih Xs hfresh i (Nat.lt_of_lt_of_eq hi hlenB) τ
                (by simpa using hspec_i) (hgetB i (Nat.lt_of_lt_of_eq hi hlenB)))
          (by
            intro Xs hfresh p hp σ hσ Ys hYs
            have hzip_len : bindings'.length = specs.length := hwf.length
            obtain ⟨i, hi, hb_eq, hs_eq⟩ := List.mem_zip_getElem hzip_len hp
            have hiB : i < binds.length := Nat.lt_of_lt_of_eq hi hlenB
            have hspec_i : specs[i] = .poly σ := hs_eq.trans hσ
            have hc := hpoly_ih Xs hfresh i hiB σ (by simpa using hspec_i) Ys hYs
              (hgetB i hiB)
            have hopen : (bindings'[i]'hi).openTyVarsAux 0 Ys = bindings'[i]'hi :=
              Expr.openTyVarsAux_eq_self_of_tyBvarBounded Ys _ 0
                (by simpa [htvs] using lowerExpr_tyBvarBounded (hgetB i hiB))
            have hc' : TypeOfHM { env := specs.map (RecSpec.rhsEntry G Xs) ++ Γ, ctors } p.1
                (σ.openVars Ys) :=
              by simpa [hb_eq] using hc
            have hopen_p : Expr.openTyVars Ys p.1 = p.1 := by
              rw [← hb_eq, Expr.openTyVars]
              exact hopen
            simpa [RecSpecs.rhsCtx] using hopen_p.symm ▸ hc')
          rfl (hbody_ih hbL)
  | match_ =>
    rename_i vs Γ scrut brs T tyArgs τres hs hbrs hpats hexh hkind hwk ihs ihbrs
    obtain ⟨scrut', bodies', hsL, hbL, rfl⟩ := lowerExpr_match_decomp hlow
    have hscrut := ihs hsL
    have hlen := lowerBranches_length hbL
    have hbodies : ∀ (i : Nat) (hi : i < bodies'.length),
        TypeOfHM ⟨branchBodyEnv Γ
          (patBindTys ctors ((brs.map Prod.fst)[i]'(by
            simpa [List.length_map, hlen] using hi)) (.customTy T tyArgs)), ctors⟩
          (bodies'[i]'hi) τres := by
      intro i hi
      have hi' : i < brs.length := by omega
      have hlow_i := lowerBranches_get hbL i hi'
      have := ihbrs i hi' hlow_i
      simpa [List.getElem_map] using this
    exact TypeOfHM_lowerMatch
      (τscrut := .customTy T tyArgs) (τres := τres)
      rfl (by simpa [List.length_map] using hlen) hscrut hpats hbodies hexh
      hcons hfields hkind hwk
  | ife =>
    rename_i vs Γ cond t f τ hc ht hf hpats hexh hkind hwk ihc iht ihf
    simp only [lowerExpr] at hlow
    cases hcL : lowerExpr ke tvs vs cond with
    | none => simp [hcL] at hlow
    | some cL =>
      cases htL : lowerExpr ke tvs vs t with
      | none => simp [hcL, htL] at hlow
      | some tL =>
        cases hfL : lowerExpr ke tvs vs f with
        | none => simp [hcL, htL, hfL] at hlow
        | some fL =>
          simp only [hcL, htL, hfL, Option.some.injEq] at hlow
          have hbodyFn : (fun i => [tL, fL].getD i (.ctor cNil)) = bodyFn [tL, fL] := by
            funext i; simp [bodyFn, matchBodyDefault]
          rw [hbodyFn] at hlow; subst hlow
          have hbindT : patBindTys ctors (.ctor cTrue []) (.customTy nBool []) = [] := by
            simp only [patBindTys, PatComp.norm, patBindTysG]
            cases patGctorFieldTys ctors cTrue (.customTy nBool []) <;> rfl
          have hbindF : patBindTys ctors (.ctor cFalse []) (.customTy nBool []) = [] := by
            simp only [patBindTys, PatComp.norm, patBindTysG]
            cases patGctorFieldTys ctors cFalse (.customTy nBool []) <;> rfl
          have hbodies' : ∀ (i : Nat) (hi : i < ([tL, fL] : List Expr).length),
              TypeOfHM ⟨branchBodyEnv Γ
                (patBindTys ctors
                  (([.ctor cTrue [], .ctor cFalse []] : List Surface.Pattern)[i]'(by
                    simpa using hi)) (.customTy nBool [])), ctors⟩
                ([tL, fL][i]'hi) τ := by
            intro i hi
            have hi2 : i < 2 := by simpa using hi
            match i with
            | 0 =>
              simpa [branchBodyEnv, hbindT] using iht htL
            | 1 =>
              simpa [branchBodyEnv, hbindF] using ihf hfL
            | n + 2 =>
              exact (Nat.not_lt_zero n (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ hi2))).elim
          exact TypeOfHM_lowerMatch
            (τscrut := .customTy nBool []) (τres := τ)
            rfl (by simp) (ihc hcL) hpats hbodies' hexh hcons hfields hkind hwk

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
            rw [List.getD]
            match i with
            | 0 => simpa [Option.getD] using lowerExpr_tyFreeVars ht
            | 1 => simpa [Option.getD] using lowerExpr_tyFreeVars hf
            | _ + 2 => simp [Option.getD, Expr.tyFreeVars])
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
              (fun i => [t', f'].getD i (.ctor cNil))
              [.ctor cTrue [], .ctor cFalse []]
              (fun i => by
                change AllMatchesExhaustive ctors ([t', f'].getD i (.ctor cNil))
                rw [List.getD]
                match i with
                | 0 => simpa [Option.getD] using iht ht'
                | 1 => simpa [Option.getD] using ihf hf'
                | _ + 2 => simp [Option.getD]; exact .ctor)
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

`Surface.Program` = user `DataDecl`s + binding `groups` + body.
Groups desugar to nested `letRecIn` (`Program.term`); prelude is merged in;
then reuse expression `lower`/`elaborate`/`surface_type_safe`. Flat bindings
go through `Program.ofFlat` → `sccGroups` → the same desugarer. -/

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
-- SCC → desugar → elaborate (via ofFlat)
#guard match Program.ofFlat [] [bF, bG] (.var (.mk "g")) with
  | some p => (elaborateProgram p).isSome
  | none => false
#guard (Program.ofFlat [] [bA, ⟨.mk "a", none, .primLit (.int 0)⟩]
  (.primLit (.int 0))).isNone
-- SurfaceCovers is inhabited for the Maybe term (no matches → trivial coverage)
example : ∀ ctors, SurfaceCovers ctors pMaybeId.term := fun _ =>
  .app (.ctor) (.primLit)


/-! ## 10. THE HEADLINE

A well-typed, exhaustive surface program elaborates to a Core term that is
type-safe and never gets stuck. Stated over the executable pipeline (`lower`
succeeds, `typecheck` succeeds, patterns cover) — the object that actually runs.

The declarative `SurfaceWT` corollary (below) closes the spec/impl loop under
Approach A / 1a: strong open `SurfaceWTExpr` + coverage ⇒ the concrete `lower`
output typechecks, then reuse `surface_type_safe`. -/

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

/-! ### SurfaceWT corollary (Approach A / 1a)

Strong `SurfaceWTExpr` carries open branch typings; rung 3 transfers to
`lowerExpr` via `TypeOfHM_lowerMatch`. Do **not** pin `LowersExpr.match_`
(Approach B) without parent approval. -/

/-- Coverage is load-bearing on the closed claim; hygiene feeds `TypeOfHM_lowerMatch`. -/
theorem typecheck_of_lower_of_SurfaceWT {ctors : CtorEnv} {s : Surface.Expr}
    {c : Expr}
    (hwt : SurfaceWT ctors s) (_hcov : SurfaceCovers ctors s)
    (hlow : lower ctors s = some c)
    (hcons : CtorEnv.arityConsistent ctors)
    (hfields : CtorEnv.fieldsKinded ctors) :
    (typecheck ctors c).isSome := by
  obtain ⟨τ, hwt'⟩ := hwt
  have hT := TypeOfHM_of_lowerExpr_of_SurfaceWTExpr hwt' hlow hcons hfields
  exact (typecheck_iff (ctors := ctors) (e := c)).mpr ⟨τ, hT⟩

/-- Declarative headline: `SurfaceWT` + `SurfaceCovers` ⇒ type-safe Core.
    Hygiene premises: true of any `elabDecls` `CtorEnv`. -/
theorem surface_type_safe_of_SurfaceWT {ctors : CtorEnv} {s : Surface.Expr}
    (hwt : SurfaceWT ctors s) (hcov : SurfaceCovers ctors s)
    (hcons : CtorEnv.arityConsistent ctors)
    (hfields : CtorEnv.fieldsKinded ctors) :
    ∃ e τ, elaborate ctors s = some e ∧
      TypeOfElabHM ⟨[], ctors⟩ e τ ∧
      AllMatchesExhaustive ctors e ∧
      ∀ e', Relation.ReflTransGen Step e e' →
        (IsValue e' ∨ ∃ e'', Step e' e'') := by
  obtain ⟨τ, hwt'⟩ := hwt
  have hlow_some : (lower ctors s).isSome := by
    simpa [lower] using lowerExpr_isSome_of_SurfaceWTExpr hwt'
  obtain ⟨c, hc⟩ := Option.isSome_iff_exists.mp hlow_some
  exact surface_type_safe hc
    (typecheck_of_lower_of_SurfaceWT ⟨τ, hwt'⟩ hcov hc hcons hfields) hcov

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
