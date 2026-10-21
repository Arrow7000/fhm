import FHM.PatComp.Trace
import FHM.Decls
import FHM.PatComp
import FHM.InferInput

/-! # The canonical surface → inference-input bridge

This module lowers surface types and declarations, groups flat bindings into
dependency SCCs, compiles patterns, checks pattern coverage, and lowers surface
expressions to `InferInput`.

`LowersExpr` and `lowerExpr` describe the production pipeline. Partial
annotations remain templates until inference returns completed Core. The
structural relation and executable lowerer share one target-parametric syntax
traversal, with soundness and completeness proved once.

The former surface-to-complete-Core policy and its structural surface typing and
runtime-safety theory remain available from the opt-in
`FHM.SurfaceBridge.CompleteCore` compatibility module. -/

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


/-! ## 2. `Surface.Ty → Core.Ty` lowering

Named tyvars resolve to de Bruijn `bvar`s against the scope `tvs` (position =
index, head = 0, matching `Decls`' param convention). Type applications are
arity-checked against the `KindEnv` — Core has NO type-name→arity env, so this is
the mandatory front-end kind-check. Sugar: `pair` → `Pair`, `bool` → `Bool`
(both checked as ordinary applications of the declared prelude type; note Core's
`PrimTy` has no `bool` and `Ty` has no `pair`, so these MUST become `customTy`s).
Fails on unbound tyvar, unknown type name, or wrong arity — so a successful
lowering is always WELL-KINDED (`lowerTy_wellKinded`, below).

This transformation is DETERMINISTIC, so the `Expr` relation may consume
`lowerTy` directly rather than a separate `TyLowers` relation. Expression
lowering is also fully deterministic (including `match_` / `ife`). -/

/-- Resolve a named tyvar to its de Bruijn index in scope (head = 0). -/
def tvarIndex : List ValName → ValName → Option Nat
  | [], _ => none
  | x :: xs, n => if x = n then some 0 else (tvarIndex xs n).map (· + 1)

mutual
/-- Lower a surface type against a kind env and a tyvar scope. -/
def lowerTy (ke : KindEnv) (tvs : List ValName) : Surface.Ty → Option Ty
  | .hole => none
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
def lowerTyList (ke : KindEnv) (tvs : List ValName) :
    List Surface.Ty → Option (List Ty)
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

/-- **Kind-check soundness of `Surface.Ty` lowering:** a
    successful `lowerTy` produces a well-kinded Core type at arity `tvs.length`.
    So the front-end annotation kind-check is correct — the produced type never
    references an undeclared type name, a wrong arity, or an out-of-scope tyvar.
    The proof is by mutual induction on `lowerTy`/`lowerTyList`, with the
    variable case supplied by `tvarIndex_lt`. -/
theorem lowerTy_wellKinded {ke : KindEnv} {tvs : List ValName} {s : Surface.Ty} {c : Ty}
    (h : lowerTy ke tvs s = some c) : Ty.WellKinded ke tvs.length c := by
  cases s with
  | hole => cases h
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


/-! ## 2b. Surface `DataDecl` lowering

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

The value-level ctors the sugar and pattern layers emit (`True`/`False`/`Pair`/
`Cons`/`Nil`). Term lowering emits these names; inference and Core typing validate
them against the constructor environment. Type-level kinding is checked here. -/

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


/-! ## 4. Surface binding dependencies and SCC grouping

Free-name analysis builds the binding dependency graph. Verified Kosaraju SCCs
are then condensation-sorted into the order used by `Program.ofFlat` and the
canonical lowering pipeline. -/

/-! ### Free value names and binding dependencies

The syntax-level traversals live in `SurfaceLang`, since `Program.term` also
uses them to distinguish acyclic from self-recursive singleton SCCs. These
aliases preserve the bridge-facing API used by the dependency proofs. -/

abbrev patVars := Surface.patVars
abbrev patVarsList := Surface.patVarsList
abbrev freeNames := Surface.freeNames
abbrev freeNamesList := Surface.freeNamesList
abbrev freeNamesBinds := Surface.freeNamesBinds
abbrev freeNamesBranches := Surface.freeNamesBranches

/-- Deduped free names (stable order of first occurrence). -/
def freeNamesD (bound : List ValName) (e : Surface.Expr) : List ValName :=
  (freeNames bound e).eraseDups

/-- Does binding `b`'s RHS freely mention value name `n`? (top-level / empty scope) -/
abbrev Binding.refersTo := Surface.Binding.refersTo

/-- Dependency edges among a flat binding list: `(src, dst)` means `src`'s RHS
    mentions `dst` (including self-loops for recursive singles). -/
def bindingDepEdges (binds : List Surface.Binding) : List (ValName × ValName) :=
  let names := binds.map (·.name)
  binds.flatMap fun b =>
    names.filterMap fun n =>
      if Binding.refersTo b n then some (b.name, n) else none

-- Free-name / dependency `#guard`s
#guard freeNamesD [] (.var (.mk "x")) = [.mk "x"]
#guard freeNamesD [] (.primBinOp .intAdd) = []
#guard freeNamesD [] (.lambda (.name (.mk "x")) none (.var (.mk "x"))) = []
#guard freeNamesD [] (.lambda (.name (.mk "x")) none (.var (.mk "y"))) = [.mk "y"]
-- λ-bound name must not count as a free ref to a same-named outer
#guard freeNamesD [.mk "x"] (.lambda (.name (.mk "x")) none (.var (.mk "x"))) = []
#guard freeNamesD [] (.letIn (.mk "x") [] [] none (.var (.mk "y")) (.var (.mk "x"))) = [.mk "y"]
#guard freeNamesD [] (.letRecIn [{ name := .mk "f", ann := none, rhs := .var (.mk "f") }]
  (.var (.mk "f"))) = []
-- match binders shadow
#guard freeNamesD [] (.match_ (.var (.mk "s"))
  [(.name (.mk "x"), .var (.mk "x")), (.wildcard, .var (.mk "z"))]) = [.mk "s", .mk "z"]
-- binding dependency edges
#guard Binding.refersTo { name := .mk "g", ann := none, rhs := .var (.mk "f") } (.mk "f") = true
#guard (Binding.refersTo
  { name := .mk "g", ann := none,
    rhs := .lambda (.name (.mk "f")) none (.var (.mk "f")) }
  (.mk "f")) = false
#guard (bindingDepEdges [
  { name := .mk "f", ann := none,
    rhs := .lambda (.name (.mk "x")) none (.app (.var (.mk "f")) (.var (.mk "x"))) },
  { name := .mk "g", ann := none, rhs := .var (.mk "f") }]).contains ((.mk "g", .mk "f"))
#guard (bindingDepEdges [
  { name := .mk "f", ann := none,
    rhs := .lambda (.name (.mk "x")) none (.app (.var (.mk "f")) (.var (.mk "x"))) },
  { name := .mk "g", ann := none, rhs := .var (.mk "f") }]).contains ((.mk "f", .mk "f"))


/-! ### SCC groups (Kosaraju + condensation topological order)

Non-deterministic spec `ValidBindingGroups`: partition into SCCs of the
dependency graph, topo-ordered so callees are outer. Executable `sccGroups`
uses Kosaraju on `bindDigraph` + Kahn on the condensation. Adequacy
(`sccGroups_sound` / `_complete`) is proved. -/

open Scc

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
    let fv := freeNames (b.params.map (·.1)) b.rhs
    (List.range binds.length).filterMap fun j =>
      match binds[j]? with
      | some b' => if b'.name ∈ fv then some j else none
      | none => none

/-- Successor table: `bindSucc binds` precomputed once per index, so repeated
    `Digraph.succ` queries (Kosaraju visits each vertex, `sccBeforeEdges` visits
    each component pair) do O(1) lookups instead of rescanning `bindSucc`. -/
def bindSuccTable (binds : List Surface.Binding) : Array (List Nat) :=
  Array.ofFn (fun i : Fin binds.length => bindSucc binds i.val)

/-- The table agrees with `bindSucc` pointwise, including OOB (`[]` on both sides). -/
theorem bindSuccTable_get (binds : List Surface.Binding) (i : Nat) :
    (bindSuccTable binds)[i]?.getD [] = bindSucc binds i := by
  simp only [bindSuccTable, Array.getElem?_ofFn]
  by_cases h : i < binds.length
  · simp [h]
  · simp [h, bindSucc]

/-- Binding dependency digraph on indices `Fin binds.length`. Builds the
    successor table once (`let`, shared by the closure below) rather than per query. -/
def bindDigraph (binds : List Surface.Binding) : Digraph (Fin binds.length) :=
  let tbl := bindSuccTable binds
  { succ := fun i =>
      ((tbl[i.val]?.getD []).filterMap fun j =>
        if h : j < binds.length then some ⟨j, h⟩ else none).toFinset }

/-- Kosaraju partition of binding indices, projected to `Nat` for Kahn. -/
def sccIndexSets (binds : List Surface.Binding) : List (List Nat) :=
  (kosaraju (bindDigraph binds)).map fun c => c.map Fin.val

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

/-- Read `indeg[i]` (0 if OOB). Public for reuse (Kahn / condensation). -/
def indegGet (indeg : List Nat) (i : Nat) : Nat :=
  indeg[i]?.getD 0

/-- Set `indeg[i] := v`. -/
private def indegSet (indeg : List Nat) (i v : Nat) : List Nat :=
  indeg.mapIdx fun j x => if j = i then v else x

/-- Extracted Kahn loop body for induction. -/
def kahnGo (beforeEdges : List (Nat × Nat)) :
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
  let tbl := bindSuccTable binds
  let succ := fun i => tbl[i]?.getD []
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
  -- `sccGroups`'s table-backed `succ` agrees with `bindSucc` pointwise, so the
  -- `sccBeforeEdges` call inside `sccGroups` matches the one in `sccOrderedIndexSets`.
  have hsucc : (fun i => (bindSuccTable binds)[i]?.getD ([] : List Nat)) = bindSucc binds :=
    funext (bindSuccTable_get binds)
  constructor
  · intro h
    have hn : (binds.map (·.name)).Nodup := by
      by_contra hdup
      simp [sccGroups, guard, hdup] at h
    refine ⟨hn, ?_⟩
    simp [sccGroups, guard, hn, hsucc] at h
    exact h.symm
  · intro ⟨hn, hg⟩
    simp [sccGroups, guard, hn, sccOrderedIndexSets, hg, hsucc]

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
        by_cases href : b'.name ∈ freeNames (b.params.map (·.1)) b.rhs
        · simp only [href, if_true] at hj
          obtain rfl := Option.some.inj hj
          exact ⟨b, b', rfl, hbj,
            by simpa [Binding.refersTo, Surface.Binding.refersTo, decide_eq_true_eq] using href⟩
        · simp [href] at hj
    · intro ⟨b, b', hb, hj, hrt⟩
      obtain ⟨rfl⟩ := hb
      refine ⟨j, (List.getElem?_eq_some_iff.mp hj).1, ?_⟩
      have href : b'.name ∈ freeNames (b.params.map (·.1)) b.rhs := by
        simpa [Binding.refersTo, Surface.Binding.refersTo, decide_eq_true_eq] using hrt
      simp [hj, href]

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

/-! ##### Binding digraph ↔ DepReach (Kosaraju bridge) -/

/-- `j` is a successor of `i` in `bindDigraph` iff it is in `bindSucc`. -/
theorem mem_bindDigraph_succ {binds : List Surface.Binding}
    {i j : Fin binds.length} :
    j ∈ (bindDigraph binds).succ i ↔ j.val ∈ bindSucc binds i.val := by
  constructor
  · intro h
    simp only [bindDigraph, bindSuccTable_get binds i.val, List.mem_toFinset,
      List.mem_filterMap] at h
    obtain ⟨j', hj', hj⟩ := h
    by_cases hlt : j' < binds.length
    · simp only [hlt, ↓reduceDIte, Option.some.injEq] at hj
      subst hj
      exact hj'
    · simp only [hlt, ↓reduceDIte] at hj
      cases hj
  · intro hj
    simp only [bindDigraph, bindSuccTable_get binds i.val, List.mem_toFinset, List.mem_filterMap]
    exact ⟨j.val, hj, by simp [j.isLt]⟩

theorem bindDigraph_succ_of_bindSucc {binds : List Surface.Binding}
    {i : Fin binds.length} {j : Nat} (hj : j < binds.length)
    (h : j ∈ bindSucc binds i.val) :
    (⟨j, hj⟩ : Fin binds.length) ∈ (bindDigraph binds).succ i :=
  (mem_bindDigraph_succ (i := i) (j := ⟨j, hj⟩)).mpr h

/-- Direct edge on the Fin digraph ⇒ `DepEdge` on binding names. -/
theorem DepEdge_of_bindDigraph_succ {binds : List Surface.Binding}
    {i j : Fin binds.length} (h : j ∈ (bindDigraph binds).succ i) :
    ∃ b b', binds[i.val]? = some b ∧ binds[j.val]? = some b' ∧
      DepEdge binds b.name b'.name :=
  DepEdge_of_bindSucc ((mem_bindDigraph_succ (i := i) (j := j)).mp h)

/-- `Reach` on `bindDigraph` ⇒ `DepReach` on the corresponding names. -/
theorem DepReach_of_Reach {binds : List Surface.Binding}
    {i j : Fin binds.length}
    (h : Reach (bindDigraph binds) i j) :
    DepReach binds (binds[i.val]).name (binds[j.val]).name := by
  induction h with
  | refl => exact DepReach.refl
  | @tail a b c hab _rbc ih =>
    obtain ⟨ba, bb, hai, hbj, hedge⟩ := DepEdge_of_bindDigraph_succ hab
    have hai' : binds[a.val] = ba := (List.getElem?_eq_some_iff.mp hai).2
    have hbj' : binds[b.val] = bb := (List.getElem?_eq_some_iff.mp hbj).2
    rw [hai']
    refine DepReach.tail (by simpa [hai', hbj'] using hedge) ?_
    simpa [hbj'] using ih

/-- `DepReach` between in-range indexed names ⇒ `Reach` on `bindDigraph`. -/
theorem Reach_of_DepReach {binds : List Surface.Binding}
    (hn : (binds.map (·.name)).Nodup)
    {i j : Fin binds.length}
    (h : DepReach binds (binds[i.val]).name (binds[j.val]).name) :
    Reach (bindDigraph binds) i j := by
  generalize hsource : (binds[i.val]).name = source at h
  generalize htarget : (binds[j.val]).name = target at h
  induction h generalizing i j with
  | refl =>
    have hij := name_inj_of_nodup hn i.isLt j.isLt (hsource.trans htarget.symm)
    have : i = j := Fin.ext hij
    subst j
    exact Reach.refl
  | @tail source dependency target hedge hrest ih =>
    have htargetMem : target ∈ binds.map (·.name) := by
      exact List.mem_map.mpr
        ⟨binds[j.val], List.getElem_mem j.isLt, htarget⟩
    have hdependency := DepReach_start_mem htargetMem hrest
    have hedge' : DepEdge binds (binds[i.val]).name dependency := by
      simpa [hsource] using hedge
    obtain ⟨k, hk, hkname, hsucc⟩ :=
      DepEdge_to_bindSucc hn i.isLt hdependency hedge'
    exact Reach.tail (bindDigraph_succ_of_bindSucc hk hsucc)
      (ih (i := (⟨k, hk⟩ : Fin binds.length)) (j := j) hkname htarget)

theorem Reach_iff_DepReach {binds : List Surface.Binding}
    (hn : (binds.map (·.name)).Nodup)
    {i j : Fin binds.length} :
    Reach (bindDigraph binds) i j ↔
      DepReach binds (binds[i.val]).name (binds[j.val]).name :=
  ⟨DepReach_of_Reach, Reach_of_DepReach hn⟩

theorem Mutual_iff_DepMutual {binds : List Surface.Binding}
    (hn : (binds.map (·.name)).Nodup)
    {i j : Fin binds.length} :
    Mutual (bindDigraph binds) i j ↔
      DepMutual binds (binds[i.val]).name (binds[j.val]).name := by
  simp only [Mutual, DepMutual, Reach_iff_DepReach hn]

/-- Kosaraju on the binding digraph is a valid abstract SCC partition. -/
theorem bindDigraph_kosaraju_sound (binds : List Surface.Binding) :
    ValidSccPartition (bindDigraph binds) (kosaraju (bindDigraph binds)) :=
  kosaraju_sound _

/-! ##### Partition / Kahn helpers for `sccOrderedIndexSets` -/

theorem DepReach_trans {binds : List Surface.Binding} {a b c : ValName}
    (hab : DepReach binds a b) (hbc : DepReach binds b c) :
    DepReach binds a c := by
  induction hab with
  | refl => exact hbc
  | tail hedge _ ih => exact DepReach.tail hedge (ih hbc)

theorem flatten_map_filterMap {α β}
    (f : α → Option β) (sets : List (List α)) :
    (sets.map (fun idxs => idxs.filterMap f)).flatten =
      sets.flatten.filterMap f := by
  induction sets with
  | nil => simp
  | cons s sets ih =>
    simp only [List.map_cons, List.flatten_cons, List.filterMap_append, ih]

theorem range_filterMap_getElem? {α} (l : List α) :
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

theorem indexSetsToBindings_flatten_of_perm
    {binds : List Surface.Binding} {sets : List (List Nat)}
    (hperm : sets.flatten.Perm (List.range binds.length)) :
    (indexSetsToBindings binds sets).flatten.Perm binds := by
  unfold indexSetsToBindings
  rw [flatten_map_filterMap]
  have h := hperm.filterMap (fun i => binds[i]?)
  rw [range_filterMap_getElem?] at h
  exact h

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

theorem perm_range_of_nodup_length {l : List Nat} {n : Nat}
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

theorem sccIndexSets_nonempty_comp (binds : List Surface.Binding) :
    ∀ c ∈ sccIndexSets binds, c ≠ [] := by
  intro c hc
  simp only [sccIndexSets, List.mem_map] at hc
  obtain ⟨cFin, hcFin, rfl⟩ := hc
  have hne := kosaraju_nonempty (bindDigraph binds) cFin hcFin
  intro hempty
  have : cFin = [] := by
    cases cFin with
    | nil => rfl
    | cons _ _ => simp [List.map] at hempty
  exact hne this

theorem sccIndexSets_flatten_nodup (binds : List Surface.Binding) :
    (sccIndexSets binds).flatten.Nodup := by
  simpa [sccIndexSets, ← List.map_flatten] using
    (kosaraju_flatten_nodup (bindDigraph binds)).map Fin.val_injective

/-- Every in-range index appears in some Kosaraju component. -/
theorem sccIndexSets_cover (binds : List Surface.Binding) :
    ∀ i, i < binds.length → ∃ c ∈ sccIndexSets binds, i ∈ c := by
  intro i hi
  obtain ⟨cFin, hcFin, hmem⟩ :=
    (bindDigraph_kosaraju_sound binds).cover ⟨i, hi⟩
  refine ⟨cFin.map Fin.val, ?_, ?_⟩
  · simp only [sccIndexSets, List.mem_map]
    exact ⟨cFin, hcFin, rfl⟩
  · exact List.mem_map.mpr ⟨⟨i, hi⟩, hmem, rfl⟩

theorem sccIndexSets_mem_lt (binds : List Surface.Binding) :
    ∀ c ∈ sccIndexSets binds, ∀ i ∈ c, i < binds.length := by
  intro c hc i hi
  simp only [sccIndexSets, List.mem_map] at hc
  obtain ⟨cFin, _, rfl⟩ := hc
  obtain ⟨⟨j, hj⟩, _, rfl⟩ := List.mem_map.mp hi
  exact hj

/-- Flatten of Kosaraju index sets is a permutation of `0 .. n-1`. -/
theorem sccIndexSets_flatten_perm (binds : List Surface.Binding) :
    (sccIndexSets binds).flatten.Perm (List.range binds.length) := by
  have hnodup := sccIndexSets_flatten_nodup binds
  have hbound : ∀ x ∈ (sccIndexSets binds).flatten, x < binds.length := by
    intro x hx
    obtain ⟨c, hc, hx'⟩ := List.mem_flatten.mp hx
    exact sccIndexSets_mem_lt binds c hc x hx'
  have hlen : (sccIndexSets binds).flatten.length = binds.length := by
    have hsub : ((sccIndexSets binds).flatten).toFinset ⊆ Finset.range binds.length := by
      intro x hx
      exact Finset.mem_range.mpr (hbound x (List.mem_toFinset.mp hx))
    have hsup : Finset.range binds.length ⊆ ((sccIndexSets binds).flatten).toFinset := by
      intro x hx
      have hx' : x < binds.length := Finset.mem_range.mp hx
      obtain ⟨c, hc, hxmem⟩ := sccIndexSets_cover binds x hx'
      exact List.mem_toFinset.mpr (List.mem_flatten.mpr ⟨c, hc, hxmem⟩)
    have hEq : ((sccIndexSets binds).flatten).toFinset = Finset.range binds.length :=
      Finset.Subset.antisymm hsub hsup
    have hcard := congrArg Finset.card hEq
    rwa [List.toFinset_card_of_nodup hnodup, Finset.card_range] at hcard
  exact perm_range_of_nodup_length hnodup hbound hlen

/-- Length hyps are explicit so `binds[a]` elaborates without `binds[a]'…`. -/
theorem sccIndexSets_sameScc (binds : List Surface.Binding)
    (hn : (binds.map (·.name)).Nodup)
    {c : List Nat} (hc : c ∈ sccIndexSets binds)
    {a b : Nat} (ha : a ∈ c) (hb : b ∈ c)
    (ha_lt : a < binds.length) (hb_lt : b < binds.length) :
    DepMutual binds (binds[a]).name (binds[b]).name := by
  simp only [sccIndexSets, List.mem_map] at hc
  obtain ⟨cFin, hcFin, rfl⟩ := hc
  obtain ⟨ia, hia, rfl⟩ := List.mem_map.mp ha
  obtain ⟨ib, hib, rfl⟩ := List.mem_map.mp hb
  have hmut := (bindDigraph_kosaraju_sound binds).sameScc cFin hcFin ia hia ib hib
  exact (Mutual_iff_DepMutual hn (i := ia) (j := ib)).mp hmut

theorem sccIndexSets_maxScc (binds : List Surface.Binding)
    (hn : (binds.map (·.name)).Nodup)
    {a b : Nat} (ha : a < binds.length) (hb : b < binds.length)
    (hmut : DepMutual binds (binds[a]).name (binds[b]).name) :
    ∃ c ∈ sccIndexSets binds, a ∈ c ∧ b ∈ c := by
  have hR : Mutual (bindDigraph binds) ⟨a, ha⟩ ⟨b, hb⟩ :=
    (Mutual_iff_DepMutual hn).mpr hmut
  obtain ⟨cFin, hcFin, ha', hb'⟩ :=
    (bindDigraph_kosaraju_sound binds).maxScc _ _ hR
  refine ⟨cFin.map Fin.val, ?_, ?_, ?_⟩
  · simp only [sccIndexSets, List.mem_map]
    exact ⟨cFin, hcFin, rfl⟩
  · exact List.mem_map.mpr ⟨⟨a, ha⟩, ha', rfl⟩
  · exact List.mem_map.mpr ⟨⟨b, hb⟩, hb', rfl⟩

/-! ##### Abstract Kahn invariants

`kahnTopo_edge_before` is false for arbitrary edges: targets `≥ n` always read
`indegGet = 0`, so Kahn can emit them before an out-of-range source. All lemmas
below assume every before-edge endpoint lies in `0 .. n-1`. -/

/-- Edges into `v` whose source is not yet emitted. -/
def remInDeg (beforeEdges : List (Nat × Nat)) (acc : List Nat) (v : Nat) : Nat :=
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

theorem remInDeg_nil_acc (beforeEdges : List (Nat × Nat)) (v : Nat) :
    remInDeg beforeEdges [] v =
      (beforeEdges.filter (fun e => e.2 = v)).length := by
  simp only [remInDeg]
  congr 1
  refine List.filter_congr ?_
  intro e _
  simp

theorem remInDeg_eq_zero_preds (beforeEdges : List (Nat × Nat))
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
theorem remInDeg_append (beforeEdges : List (Nat × Nat)) (acc : List Nat)
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

theorem kahnTopo_indeg0_eq (n : Nat) (beforeEdges : List (Nat × Nat))
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

/-- Bounded edges: every endpoint is `< n`.
    Generic Kahn/condensation helpers below are public for reuse. -/
def edgesBounded (n : Nat) (edges : List (Nat × Nat)) : Prop :=
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
theorem kahnGo_edge_before_of_bounded (beforeEdges : List (Nat × Nat))
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
theorem kahnTopo_edge_before (n : Nat) (edges : List (Nat × Nat))
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
theorem sccBeforeEdges_bounded (succ : Nat → List Nat)
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
theorem sccBeforeEdges_nodup (succ : Nat → List Nat)
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
theorem length_le_of_nodup_lt {l : List Nat} {n : Nat}
    (hn : l.Nodup) (hbound : ∀ x ∈ l, x < n) :
    l.length ≤ n := by
  have hsub : l.toFinset ⊆ Finset.range n := by
    intro x hx
    exact Finset.mem_range.mpr (hbound x (List.mem_toFinset.mp hx))
  have := Finset.card_le_card hsub
  rwa [List.toFinset_card_of_nodup hn, Finset.card_range] at this

/-- Zero-closed ready invariant: every `remInDeg = 0` vertex is queued or emitted. -/
theorem kahnGo_zero_closed (beforeEdges : List (Nat × Nat))
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
theorem exists_edge_cycle_of_pred_closed (beforeEdges : List (Nat × Nat))
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
theorem sccBeforeEdges_no_loop (succ : Nat → List Nat)
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
theorem exists_succ_of_mem_sccBeforeEdges (succ : Nat → List Nat)
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

/-- One condensation before-edge ⇒ `DepReach` from dependent into dependency. -/
private theorem DepReach_of_sccBeforeEdge (binds : List Surface.Binding)
    (hn : (binds.map (·.name)).Nodup)
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
    sccIndexSets_sameScc binds hn hv_mem hx hp hx_lt hp_lt
  have hqy : DepMutual binds (binds[q]).name (binds[y]).name :=
    sccIndexSets_sameScc binds hn hu_mem hq hy hq_lt hy_lt
  exact DepReach_trans hxp.1 (DepReach.tail hedge hqy.1)

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

/-- Condensation path ⇒ `DepReach` from path-end component back to start. -/
private theorem DepReach_of_sccBeforeReach (binds : List Surface.Binding)
    (hn : (binds.map (·.name)).Nodup)
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
    exact DepReach_of_sccBeforeEdge binds hn he hca hcb hx hy hx_lt hy_lt
  | tail hab hbc ih =>
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
        sccIndexSets_sameScc binds hn (List.mem_of_getElem? hca) hx hp hx_lt hp_lt
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

/-- Each index appears in exactly one Kosaraju component. -/
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

/-- Distinct components are mutual-reachability separated. -/
private theorem sccIndexSets_separated (binds : List Surface.Binding)
    (hn : (binds.map (·.name)).Nodup)
    {c₁ c₂ : List Nat} (hc₁ : c₁ ∈ sccIndexSets binds)
    (hc₂ : c₂ ∈ sccIndexSets binds) (hne : c₁ ≠ c₂)
    {a b : Nat} (ha : a ∈ c₁) (hb : b ∈ c₂)
    (ha_lt : a < binds.length) (hb_lt : b < binds.length) :
    ¬DepMutual binds (binds[a]).name (binds[b]).name := by
  intro hmut
  obtain ⟨c, hc, ha', hb'⟩ := sccIndexSets_maxScc binds hn ha_lt hb_lt hmut
  have hnodup := sccIndexSets_flatten_nodup binds
  have hdisj : List.Pairwise List.Disjoint (sccIndexSets binds) :=
    (List.nodup_flatten.mp hnodup).2
  have hc₁c : c₁ = c :=
    eq_of_mem_of_mem_of_pairwise_disjoint hdisj hc₁ hc ha ha'
  have hc₂c : c₂ = c :=
    eq_of_mem_of_mem_of_pairwise_disjoint hdisj hc₂ hc hb hb'
  exact hne (hc₁c.trans hc₂c.symm)

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
    DepReach_of_sccBeforeReach binds hn huv hcv hcu hy hx hy_lt hx_lt
  have dyx : DepReach binds (binds[x]).name (binds[y]).name :=
    DepReach_of_sccBeforeReach binds hn hvu hcu hcv hx hy hx_lt hy_lt
  have hmut : DepMutual binds (binds[x]).name (binds[y]).name := ⟨dyx, dxy⟩
  exact sccIndexSets_separated binds hn hu_mem hv_mem hne_g hx hy hx_lt hy_lt hmut

/-- Critical Kahn gap: condensation of Kosaraju comps is a DAG. -/
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

private theorem sccIndexSets_mem_of_DepMutual (binds : List Surface.Binding)
    (hn : (binds.map (·.name)).Nodup)
    {g : List Nat} (hg : g ∈ sccIndexSets binds)
    {i j : Nat} (hi : i ∈ g)
    (hi_lt : i < binds.length) (hj : j < binds.length)
    (hmut : DepMutual binds (binds[i]).name (binds[j]).name) :
    j ∈ g := by
  obtain ⟨g', hg', hj', _⟩ := sccIndexSets_unique_comp binds hj
  suffices g' = g by rwa [← this]
  by_contra hne
  exact sccIndexSets_separated binds hn hg hg' (Ne.symm hne) hi hj' hi_lt hj hmut

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

theorem sccOrderedIndexSets_sameScc (binds : List Surface.Binding)
    (hn : (binds.map (·.name)).Nodup) :
    ∀ g ∈ indexSetsToBindings binds (sccOrderedIndexSets binds),
      ∀ b1 ∈ g, ∀ b2 ∈ g, DepMutual binds b1.name b2.name := by
  intro g hg b1 hb1 b2 hb2
  simp only [indexSetsToBindings, List.mem_map] at hg
  obtain ⟨idxs, hidxs, rfl⟩ := hg
  have hcomp := sccOrderedIndexSets_mem_of_getElem binds hidxs
  obtain ⟨i, hi, hbi⟩ := List.mem_filterMap.mp hb1
  obtain ⟨j, hj, hbj⟩ := List.mem_filterMap.mp hb2
  have hi_lt := sccIndexSets_mem_lt binds idxs hcomp i hi
  have hj_lt := sccIndexSets_mem_lt binds idxs hcomp j hj
  have hbi' : binds[i] = b1 := by
    rw [List.getElem?_eq_getElem hi_lt] at hbi; exact Option.some.inj hbi
  have hbj' : binds[j] = b2 := by
    rw [List.getElem?_eq_getElem hj_lt] at hbj; exact Option.some.inj hbj
  have hmut := sccIndexSets_sameScc binds hn hcomp hi hj hi_lt hj_lt
  simpa [hbi', hbj'] using hmut

theorem sccOrderedIndexSets_maxScc (binds : List Surface.Binding)
    (hn : (binds.map (·.name)).Nodup) :
    ∀ b1 ∈ binds, ∀ b2 ∈ binds,
      DepMutual binds b1.name b2.name →
        ∃ g ∈ indexSetsToBindings binds (sccOrderedIndexSets binds),
          b1 ∈ g ∧ b2 ∈ g := by
  intro b1 hb1 b2 hb2 hmut
  obtain ⟨i, hi, hib⟩ := List.mem_iff_getElem.mp hb1
  obtain ⟨j, hj, hjb⟩ := List.mem_iff_getElem.mp hb2
  subst hib; subst hjb
  obtain ⟨gIdxs, hgIdxs, hi_mem, _huniq⟩ := sccIndexSets_unique_comp binds hi
  have hj_mem : j ∈ gIdxs :=
    sccIndexSets_mem_of_DepMutual binds hn hgIdxs hi_mem hi hj hmut
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

theorem kahnTopo_nodup (n : Nat) (edges : List (Nat × Nat))
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

theorem kahnTopo_lt (n : Nat) (edges : List (Nat × Nat))
    (hb : edgesBounded n edges) :
    ∀ x ∈ kahnTopo n edges, x < n := by
  simp only [kahnTopo]
  refine kahnGo_lt edges n hb (n + 1) _ _ [] ?_ (by intro y hy; cases hy)
  intro b hb'
  exact List.mem_range.mp (List.mem_of_mem_filter hb')

/-- `filterMap` of always-`some` is `map` of the forced values. -/
theorem filterMap_getElem?_eq_map {α β} (f : α → Option β) (l : List α)
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

theorem mem_sccBeforeEdges_of_compDependsOn (succ : Nat → List Nat)
    (comps : List (List Nat)) {a b : Nat}
    (ha : a < comps.length) (hb : b < comps.length) (hne : a ≠ b)
    (hdep : compDependsOn succ (comps[a]) (comps[b]) = true) :
    (b, a) ∈ sccBeforeEdges succ comps := by
  simp only [sccBeforeEdges, List.mem_flatMap]
  refine ⟨a, List.mem_range.mpr ha, ?_⟩
  simp only [List.mem_filterMap]
  refine ⟨b, List.mem_range.mpr hb, ?_⟩
  simp [hne, List.getElem?_eq_getElem ha, List.getElem?_eq_getElem hb, hdep]

theorem compDependsOn_of_succ_mem (succ : Nat → List Nat)
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
    sccOrderedIndexSets_sameScc binds hn,
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

/-- Build a `Program` from a flat binding list: SCC-sort groups, keep
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
  { name := .mk "f", ann := none,
    rhs := .lambda (.name (.mk "x")) none (.app (.var (.mk "f")) (.var (.mk "x"))) }
private def bG : Surface.Binding :=
  { name := .mk "g", ann := none, rhs := .var (.mk "f") }
private def bA : Surface.Binding :=
  { name := .mk "a", ann := none, rhs := .primLit (.int 1) }
private def bB : Surface.Binding :=
  { name := .mk "b", ann := none, rhs := .primLit (.int 2) }
private def bH : Surface.Binding :=
  { name := .mk "h", ann := none, rhs := .var (.mk "k") }
private def bK : Surface.Binding :=
  { name := .mk "k", ann := none, rhs := .var (.mk "h") }

-- g depends on f ⇒ [f]-group outer, then [g]
#guard match sccGroups [bF, bG] with
  | some [[{ name := .mk "f", .. }], [{ name := .mk "g", .. }]] => true
  | _ => false
-- mutual h↔ k ⇒ one group containing both (order inside free)
#guard match sccGroups [bH, bK] with
  | some [g] =>
      g.length = 2 && (g.map (·.name)).contains (.mk "h") &&
        (g.map (·.name)).contains (.mk "k")
  | _ => false
-- independent a, b ⇒ two singleton groups (intra-order free under Kosaraju)
#guard match sccGroups [bA, bB] with
  | some [[{ name := .mk "a", .. }], [{ name := .mk "b", .. }]] => true
  | some [[{ name := .mk "b", .. }], [{ name := .mk "a", .. }]] => true
  | _ => false
-- duplicate names rejected
#guard (sccGroups [bA, { name := .mk "a", ann := none, rhs := .primLit (.int 0) }]).isNone
-- empty
#guard match sccGroups [] with | some [] => true | _ => false



/-- Lower a surface scheme inside an ambient named type-variable scope. The
    scheme's own `foralls` are innermost, so they precede `tvs`; only those own
    binders contribute to `paramCount`. Ambient names therefore lower to bvars
    beyond the scheme's own binder block and are opened by the enclosing term. -/
def lowerPolyIn (ke : KindEnv) (tvs : List ValName) (σ : Surface.PolyTy) : Option PolyTy :=
  let fs := σ.foralls.eraseDups
  (lowerTy ke (fs ++ tvs) σ.body).map (fun b => ⟨fs.length, b⟩)

/-- Closed-scope specialization used by declarations and compatibility lemmas. -/
def lowerPoly (ke : KindEnv) (σ : Surface.PolyTy) : Option PolyTy :=
  let fs := σ.foralls.eraseDups
  (lowerTy ke fs σ.body).map (fun b => ⟨fs.length, b⟩)



/-! ## Shared binding-head normalization -/

/-- Prenex merge of binder lists; duplicates keep the first (`tyParams` win). -/
def mergeTyParamNames (tyParams foralls : List ValName) : List ValName :=
  (tyParams ++ foralls).eraseDups

/-- Merge `{tyParams}` into an existing scheme; `none` stays `none`. -/
def mergeTyParams (tyParams : List ValName) : Option Surface.PolyTy → Option Surface.PolyTy
  | none => none
  | some σ => some { foralls := mergeTyParamNames tyParams σ.foralls, body := σ.body }

/-- Right-nest value-param domains onto `ret` (surface order = outer λ first). -/
def paramsToArrows (params : List (ValName × Option Surface.Ty)) (ret : Surface.Ty) :
    Option Surface.Ty :=
  let rec go : List (ValName × Option Surface.Ty) → Option Surface.Ty
    | [] => some ret
    | (_, none) :: _ => none
    | (_, some τ) :: rest => (go rest).map (fun acc => Surface.Ty.arrow τ acc)
  go params

/-- Term-var scope for lowering a surface RHS before wrapping params as nested
    lambdas: the innermost parameter is index 0. -/
def paramTermScope (params : List (ValName × Option Surface.Ty)) (vs : List ValName) :
    List ValName :=
  (params.map (·.1)).reverse ++ vs

/-- Ty-param prefix prepended to the ambient tyvar scope for a binding RHS.
    Empty when there is no finalized scheme: Core `letIn none` / `RecAnn.params none = 0`
    introduces no ty binders, so `{t}` alone does not extend the scope (use `: ret` /
    scheme synthesis via `finalizeInputAnn` to bind tyParams). -/
def letAnnTyPrefix (tyParams : List ValName) (annF : Option Surface.PolyTy) : List ValName :=
  (annF.map (fun σ => mergeTyParamNames tyParams σ.foralls)).getD []

mutual
private def lowerExprSize : Surface.Expr → Nat
  | .primLit _ | .primBinOp _ | .var _ | .ctor _ => 1
  | .pair a b | .cons a b | .app a b => 1 + lowerExprSize a + lowerExprSize b
  | .list es => 1 + lowerExprListSize es
  | .lambda _ _ body => 1 + lowerExprSize body
  | .letIn _ _ params _ rhs body => 1 + params.length + lowerExprSize rhs + lowerExprSize body
  | .letRecIn binds body => 1 + lowerRecBindsSize binds + lowerExprSize body
  | .ife c t f => 1 + lowerExprSize c + lowerExprSize t + lowerExprSize f
  | .match_ scrut brs => 1 + lowerExprSize scrut + lowerBranchesSize brs
private def lowerExprListSize : List Surface.Expr → Nat
  | [] => 0
  | e :: es => 1 + lowerExprSize e + lowerExprListSize es
private def lowerBranchesSize : List (Surface.Pattern × Surface.Expr) → Nat
  | [] => 0
  | (_, e) :: es => 1 + lowerExprSize e + lowerBranchesSize es
private def lowerRecBindsSize : List Surface.Binding → Nat
  | [] => 0
  | { params := ps, rhs := rhs, .. } :: bs =>
      1 + ps.length + lowerExprSize rhs + lowerRecBindsSize bs
end
/-- Names and wildcards use ordinary lambdas; other patterns need compilation. -/
def compoundLambdaPattern : Surface.Pattern → Bool
  | .name _ | .wildcard => false
  | _ => true

/-! ## Shared structural lowering and annotation policies -/
end SurfaceBridge

mutual
/-- Lower a template with the same name, kind and arity checks as ordinary
surface type lowering. Named scoped variables remain fixed bound variables. -/
def lowerTemplate (ke : KindEnv) (tvs : List ValName) : Surface.Ty → Option TyTemplate
  | .hole => some .hole
  | .prim p => (SurfaceBridge.lowerTy ke tvs (.prim p)).map .fixed
  | .tvar name => (SurfaceBridge.lowerTy ke tvs (.tvar name)).map .fixed
  | .arrow a b => return .arrow (← lowerTemplate ke tvs a) (← lowerTemplate ke tvs b)
  | .pair a b => do
      let a' ← lowerTemplate ke tvs a
      let b' ← lowerTemplate ke tvs b
      if LookupList.get? ke SurfaceBridge.nPair = some 2 then
        some (.custom SurfaceBridge.nPair [a', b'])
      else none
  | .customTy name args => do
      let args' ← lowerTemplateList ke tvs args
      if LookupList.get? ke name = some args'.length then some (.custom name args') else none

def lowerTemplateList (ke : KindEnv) (tvs : List ValName) :
    List Surface.Ty → Option (List TyTemplate)
  | [] => some []
  | ty :: rest => return (← lowerTemplate ke tvs ty) :: (← lowerTemplateList ke tvs rest)
end

/-- Lower an optional lambda-parameter annotation without filling its holes. -/
def lowerTemplateAnn (ke : KindEnv) (tvs : List ValName) :
    Option Surface.Ty → Option (Option TyTemplate)
  | none => some none
  | some ty => (lowerTemplate ke tvs ty).map some

/-- Normalize binding-head sugar for the canonical input pipeline.
A result annotation describes the RHS after every head parameter. Missing
parameter types become independent holes; a head forall without a result
annotation retains its scope using a partial signature. Parameter-only heads
without a result annotation keep ordinary HM lambda inference. -/
def finalizeInputAnn (tyParams : List ValName)
    (params : List (ValName × Option Surface.Ty)) (ann : Option Surface.PolyTy) :
    Option Surface.PolyTy :=
  if tyParams.isEmpty && params.isEmpty then SurfaceBridge.mergeTyParams [] ann
  else if tyParams.isEmpty && ann.isNone then none
  else
    some {
      foralls := SurfaceBridge.mergeTyParamNames tyParams ((ann.map (·.foralls)).getD [])
      body := params.foldr (fun (_, domain) result => .arrow (domain.getD .hole) result)
        ((ann.map (·.body)).getD .hole) }



@[simp] theorem finalizeInputAnn_noHead_eq_merge (ann : Option Surface.PolyTy) :
    finalizeInputAnn [] [] ann = SurfaceBridge.mergeTyParams [] ann := rfl

example : finalizeInputAnn [] [] (some ⟨[], .prim .int⟩) = some ⟨[], .prim .int⟩ := rfl

example : finalizeInputAnn [] [(.mk "x", none), (.mk "y", some (.prim .bool))]
    (some ⟨[], .prim .int⟩) =
  some ⟨[], .arrow .hole (.arrow (.prim .bool) (.prim .int))⟩ := rfl

example : finalizeInputAnn [.mk "a"] [(.mk "x", some (.tvar (.mk "a")))] none =
  some ⟨[.mk "a"], .arrow (.tvar (.mk "a")) .hole⟩ := rfl

example : finalizeInputAnn [.mk "unused"] [] none = some ⟨[.mk "unused"], .hole⟩ := rfl

example : finalizeInputAnn [] [(.mk "x", some (.prim .int)), (.mk "y", none)] none = none := rfl

example : finalizeInputAnn [.mk "a"] [(.mk "x", none)]
    (some ⟨[.mk "b"], .tvar (.mk "b")⟩) =
  some ⟨[.mk "a", .mk "b"], .arrow .hole (.tvar (.mk "b"))⟩ := rfl

/-- Classify a finalized binding signature by whether its lowered template is
complete. The caller applies `finalizeInputAnn` before this adapter. -/
def lowerInputLetAnn (ke : KindEnv) (tvs : List ValName) :
    Option Surface.PolyTy → Option BindingAnn
  | none => some .absent
  | some scheme => do
      let names := scheme.foralls.eraseDups
      let template ← lowerTemplate ke (names ++ tvs) scheme.body
      match template.toCore with
      | some body => some (.complete ⟨names.length, body⟩)
      | none =>
          if names.isEmpty then some (.template template)
          else some (.partialForall names.length template)

/-- Preserve input annotations while using the single generic pattern emitter. -/
def inputEmissionOps : PatComp.EmissionOps InferInput :=
  { var := InferInput.var
    ctor := InferInput.ctor
    letIn := InferInput.letIn .absent
    match_ := InferInput.match_
    shiftFrom := InferInput.shiftFrom }

def lowerInputMatch (scrut : InferInput) (pats : List Surface.Pattern) (bodies : Nat → InferInput) : InferInput :=
  PatComp.lowerMatchWith inputEmissionOps scrut pats bodies

def lowerInputMatchTrace (scrut : InferInput) (pats : List Surface.Pattern)
    (bodies : Nat → InferInput) : PatComp.TracedLowering InferInput :=
  PatComp.lowerMatchTraceWith inputEmissionOps scrut pats bodies

@[simp] theorem lowerInputMatchTrace_expr (scrut : InferInput) (pats : List Surface.Pattern)
    (bodies : Nat → InferInput) :
    (lowerInputMatchTrace scrut pats bodies).expr = lowerInputMatch scrut pats bodies := rfl


namespace SurfaceBridge

/-- Target constructors and annotation policy for the shared structural lowerer. -/
structure LoweringOps (Term ParamAnn BindAnn : Type) where
  emission : PatComp.EmissionOps Term
  primLit : PrimLitExpr → Term
  primBinOp : PrimBinOp → Term
  app : Term → Term → Term
  lambda : ParamAnn → Term → Term
  letIn : BindAnn → Term → Term → Term
  letRec : List (RecBinding BindAnn Term) → Term → Term
  lowerParamAnn : KindEnv → List ValName → Option Surface.Ty → Option ParamAnn
  finalize : List ValName → List (ValName × Option Surface.Ty) → Option Surface.PolyTy → Option Surface.PolyTy
  lowerBindAnn : KindEnv → List ValName → Option Surface.PolyTy → Option BindAnn

private theorem lowering_bind_eq_some {α β : Type} {o : Option α} {f : α → Option β} {b : β}
    (h : o.bind f = some b) : ∃ a, o = some a ∧ f a = some b := by
  cases o with
  | none => simp at h
  | some a => exact ⟨a, rfl, h⟩

variable {Term ParamAnn BindAnn : Type}

def LoweringOps.mkList (ops : LoweringOps Term ParamAnn BindAnn) : List Term → Term
  | [] => ops.emission.ctor cNil
  | x :: xs => ops.app (ops.app (ops.emission.ctor cCons) x) (ops.mkList xs)

def LoweringOps.wrapParams (ops : LoweringOps Term ParamAnn BindAnn)
    (ke : KindEnv) (tvs : List ValName) : List (ValName × Option Surface.Ty) → Term → Option Term
  | [], body => some body
  | (_, ann) :: rest, body => do
      let ann' ← ops.lowerParamAnn ke tvs ann
      let inner ← ops.wrapParams ke tvs rest body
      pure (ops.lambda ann' inner)

def LoweringOps.match_ (ops : LoweringOps Term ParamAnn BindAnn)
    (scrut : Term) (pats : List Surface.Pattern) (bodies : List Term) : Term :=
  PatComp.lowerMatchWith ops.emission scrut pats (fun i => bodies.getD i (ops.emission.ctor cNil))

def LoweringOps.patternLambda (ops : LoweringOps Term ParamAnn BindAnn)
    (ann : ParamAnn) (pat : Surface.Pattern) (body : Term) : Term :=
  ops.lambda ann (ops.match_ (ops.emission.var 0) [pat] [body])

mutual
 def lowerExprWith (ops : LoweringOps Term ParamAnn BindAnn) (ke : KindEnv)
     (tvs vs : List ValName) : Surface.Expr → Option Term
   | .primLit (.bool b) => some (ops.emission.ctor (if b then cTrue else cFalse))
   | .primLit .unit => some (ops.primLit .unit)
   | .primLit (.int n) => some (ops.primLit (.int n))
   | .primLit (.nat n) => some (ops.primLit (.nat n))
   | .primLit (.char c) => some (ops.primLit (.char c))
   | .primBinOp op => some (ops.primBinOp op)
   | .pair a b => return ops.app (ops.app (ops.emission.ctor cPair) (← lowerExprWith ops ke tvs vs a)) (← lowerExprWith ops ke tvs vs b)
   | .cons h t => return ops.app (ops.app (ops.emission.ctor cCons) (← lowerExprWith ops ke tvs vs h)) (← lowerExprWith ops ke tvs vs t)
   | .list items => (lowerExprListWith ops ke tvs vs items).map ops.mkList
   | .lambda param ann body => do
       let ann' ← ops.lowerParamAnn ke tvs ann
       match param with
       | .name x => return ops.lambda ann' (← lowerExprWith ops ke tvs (x :: vs) body)
       | .wildcard => return ops.lambda ann' (← lowerExprWith ops ke tvs (.mk "_" :: vs) body)
       | _ => return ops.patternLambda ann' param (← lowerExprWith ops ke tvs (patVars param ++ .mk "_" :: vs) body)
   | .app f x => return ops.app (← lowerExprWith ops ke tvs vs f) (← lowerExprWith ops ke tvs vs x)
   | .letIn name tyParams params ann rhs body => do
       let annF := ops.finalize tyParams params ann
       let ann' ← ops.lowerBindAnn ke tvs annF
       let tvs' := letAnnTyPrefix tyParams annF ++ tvs
       let rhsCore ← lowerExprWith ops ke tvs' (paramTermScope params vs) rhs
       let rhs' ← ops.wrapParams ke tvs' params rhsCore
       let body' ← lowerExprWith ops ke tvs (name :: vs) body
       pure (ops.letIn ann' rhs' body')
   | .letRecIn binds body => do
       let recScope := binds.map (·.name) ++ vs
       let bindings' ← lowerRecBindsWith ops ke tvs recScope binds
       let body' ← lowerExprWith ops ke tvs recScope body
       pure (ops.letRec bindings' body')
   | .var name => (tvarIndex vs name).map ops.emission.var
   | .ctor name => some (ops.emission.ctor name)
   | .ife c t f => do
       let c' ← lowerExprWith ops ke tvs vs c
       let t' ← lowerExprWith ops ke tvs vs t
       let f' ← lowerExprWith ops ke tvs vs f
       pure (ops.match_ c' [.ctor cTrue [], .ctor cFalse []] [t', f'])
   | .match_ scrut brs => do
       let scrut' ← lowerExprWith ops ke tvs vs scrut
       let bodies' ← lowerBranchesWith ops ke tvs vs brs
       pure (ops.match_ scrut' (brs.map Prod.fst) bodies')
 termination_by e => lowerExprSize e
 decreasing_by all_goals simp [lowerExprSize] <;> omega
 def lowerExprListWith (ops : LoweringOps Term ParamAnn BindAnn) (ke : KindEnv)
     (tvs vs : List ValName) : List Surface.Expr → Option (List Term)
   | [] => some []
   | e :: es => return (← lowerExprWith ops ke tvs vs e) :: (← lowerExprListWith ops ke tvs vs es)
 termination_by es => lowerExprListSize es
 decreasing_by all_goals simp [lowerExprListSize] <;> omega
 def lowerBranchesWith (ops : LoweringOps Term ParamAnn BindAnn) (ke : KindEnv)
     (tvs vs : List ValName) : List (Surface.Pattern × Surface.Expr) → Option (List Term)
   | [] => some []
   | (p,b) :: rest => return (← lowerExprWith ops ke tvs (patVars p ++ vs) b) :: (← lowerBranchesWith ops ke tvs vs rest)
 termination_by bs => lowerBranchesSize bs
 decreasing_by all_goals simp [lowerBranchesSize] <;> omega
 def lowerRecBindsWith (ops : LoweringOps Term ParamAnn BindAnn) (ke : KindEnv)
     (tvs vs : List ValName) :
     List Surface.Binding → Option (List (RecBinding BindAnn Term))
   | [] => some []
   | b :: rest => do
       let annF := ops.finalize b.tyParams b.params b.ann
       let ann' ← ops.lowerBindAnn ke tvs annF
       let tvs' := letAnnTyPrefix b.tyParams annF ++ tvs
       let rhsCore ← lowerExprWith ops ke tvs' (paramTermScope b.params vs) b.rhs
       let rhs' ← ops.wrapParams ke tvs' b.params rhsCore
       return { ann := ann', rhs := rhs' } :: (← lowerRecBindsWith ops ke tvs vs rest)
 termination_by bs => lowerRecBindsSize bs
 decreasing_by all_goals simp [lowerRecBindsSize] <;> omega
end
mutual
/-- Structural surface lowering, parameterized only by target syntax and annotation policy. -/
inductive LowersExprWith (ops : LoweringOps Term ParamAnn BindAnn) (ctors : CtorEnv) (ke : KindEnv) :
    List ValName → List ValName → Surface.Expr → Term → Prop where
  | primLitUnit {tvs vs} : LowersExprWith ops ctors ke tvs vs (.primLit .unit) (ops.primLit .unit)
  | primLitInt {tvs vs n} : LowersExprWith ops ctors ke tvs vs (.primLit (.int n)) (ops.primLit (.int n))
  | primLitNat {tvs vs n} : LowersExprWith ops ctors ke tvs vs (.primLit (.nat n)) (ops.primLit (.nat n))
  | primLitChar {tvs vs c} : LowersExprWith ops ctors ke tvs vs (.primLit (.char c)) (ops.primLit (.char c))
  | primLitBool {tvs vs b} : LowersExprWith ops ctors ke tvs vs (.primLit (.bool b)) (ops.emission.ctor (if b then cTrue else cFalse))
  | primBinOp {tvs vs op} : LowersExprWith ops ctors ke tvs vs (.primBinOp op) (ops.primBinOp op)
  | pair {tvs vs a b a' b'} :
      LowersExprWith ops ctors ke tvs vs a a' → LowersExprWith ops ctors ke tvs vs b b' →
      LowersExprWith ops ctors ke tvs vs (.pair a b) (ops.app (ops.app (ops.emission.ctor cPair) a') b')
  | cons {tvs vs h t h' t'} :
      LowersExprWith ops ctors ke tvs vs h h' → LowersExprWith ops ctors ke tvs vs t t' →
      LowersExprWith ops ctors ke tvs vs (.cons h t) (ops.app (ops.app (ops.emission.ctor cCons) h') t')
  | list {tvs vs items items'} : LowersExprListWith ops ctors ke tvs vs items items' →
      LowersExprWith ops ctors ke tvs vs (.list items) (ops.mkList items')
  | lambda_name {tvs vs x ann ann' body body'} :
      ops.lowerParamAnn ke tvs ann = some ann' →
      LowersExprWith ops ctors ke tvs (x :: vs) body body' →
      LowersExprWith ops ctors ke tvs vs (.lambda (.name x) ann body) (ops.lambda ann' body')
  | lambda_wild {tvs vs ann ann' body body'} :
      ops.lowerParamAnn ke tvs ann = some ann' →
      LowersExprWith ops ctors ke tvs (.mk "_" :: vs) body body' →
      LowersExprWith ops ctors ke tvs vs (.lambda .wildcard ann body) (ops.lambda ann' body')
  | lambda_pattern {tvs vs param ann ann' body body'} :
      compoundLambdaPattern param = true → ops.lowerParamAnn ke tvs ann = some ann' →
      LowersExprWith ops ctors ke tvs (patVars param ++ .mk "_" :: vs) body body' →
      LowersExprWith ops ctors ke tvs vs (.lambda param ann body) (ops.patternLambda ann' param body')
  | app {tvs vs f x f' x'} :
      LowersExprWith ops ctors ke tvs vs f f' → LowersExprWith ops ctors ke tvs vs x x' →
      LowersExprWith ops ctors ke tvs vs (.app f x) (ops.app f' x')
  | letIn {tvs vs name tyParams params ann ann' rhs rhsCore rhs' body body'} :
      ops.lowerBindAnn ke tvs (ops.finalize tyParams params ann) = some ann' →
      LowersExprWith ops ctors ke
        (letAnnTyPrefix tyParams (ops.finalize tyParams params ann) ++ tvs)
        (paramTermScope params vs) rhs rhsCore →
      ops.wrapParams ke (letAnnTyPrefix tyParams (ops.finalize tyParams params ann) ++ tvs)
        params rhsCore = some rhs' →
      LowersExprWith ops ctors ke tvs (name :: vs) body body' →
      LowersExprWith ops ctors ke tvs vs (.letIn name tyParams params ann rhs body) (ops.letIn ann' rhs' body')
  | letRecIn {tvs vs binds bindings' body body'} :
      LowersRecBindsWith ops ctors ke tvs (binds.map (·.name) ++ vs) binds bindings' →
      LowersExprWith ops ctors ke tvs (binds.map (·.name) ++ vs) body body' →
      LowersExprWith ops ctors ke tvs vs (.letRecIn binds body) (ops.letRec bindings' body')
  | var {tvs vs name i} : tvarIndex vs name = some i →
      LowersExprWith ops ctors ke tvs vs (.var name) (ops.emission.var i)
  | ctor {tvs vs name} : LowersExprWith ops ctors ke tvs vs (.ctor name) (ops.emission.ctor name)
  | ife {tvs vs c t f c' t' f'} :
      LowersExprWith ops ctors ke tvs vs c c' → LowersExprWith ops ctors ke tvs vs t t' →
      LowersExprWith ops ctors ke tvs vs f f' →
      LowersExprWith ops ctors ke tvs vs (.ife c t f) (ops.match_ c' [.ctor cTrue [], .ctor cFalse []] [t', f'])
  | match_ {tvs vs scrut brs scrut' bodies'} :
      LowersExprWith ops ctors ke tvs vs scrut scrut' → LowersBranchesWith ops ctors ke tvs vs brs bodies' →
      LowersExprWith ops ctors ke tvs vs (.match_ scrut brs) (ops.match_ scrut' (brs.map Prod.fst) bodies')
inductive LowersExprListWith (ops : LoweringOps Term ParamAnn BindAnn) (ctors : CtorEnv) (ke : KindEnv) :
    List ValName → List ValName → List Surface.Expr → List Term → Prop where
  | nil {tvs vs} : LowersExprListWith ops ctors ke tvs vs [] []
  | cons {tvs vs e es e' es'} : LowersExprWith ops ctors ke tvs vs e e' →
      LowersExprListWith ops ctors ke tvs vs es es' → LowersExprListWith ops ctors ke tvs vs (e :: es) (e' :: es')
inductive LowersRecBindsWith (ops : LoweringOps Term ParamAnn BindAnn) (ctors : CtorEnv) (ke : KindEnv) :
    List ValName → List ValName → List Surface.Binding →
      List (RecBinding BindAnn Term) → Prop where
  | nil {tvs vs} : LowersRecBindsWith ops ctors ke tvs vs [] []
  | cons {tvs vs bind ann' rhsCore e' rest rest'} :
      ops.lowerBindAnn ke tvs (ops.finalize bind.tyParams bind.params bind.ann) = some ann' →
      LowersExprWith ops ctors ke (letAnnTyPrefix bind.tyParams (ops.finalize bind.tyParams bind.params bind.ann) ++ tvs)
        (paramTermScope bind.params vs) bind.rhs rhsCore →
      ops.wrapParams ke (letAnnTyPrefix bind.tyParams (ops.finalize bind.tyParams bind.params bind.ann) ++ tvs)
        bind.params rhsCore = some e' →
      LowersRecBindsWith ops ctors ke tvs vs rest rest' →
      LowersRecBindsWith ops ctors ke tvs vs (bind :: rest)
        ({ ann := ann', rhs := e' } :: rest')
inductive LowersBranchesWith (ops : LoweringOps Term ParamAnn BindAnn) (ctors : CtorEnv) (ke : KindEnv) :
    List ValName → List ValName → List (Surface.Pattern × Surface.Expr) → List Term → Prop where
  | nil {tvs vs} : LowersBranchesWith ops ctors ke tvs vs [] []
  | cons {tvs vs p b rest b' rest'} :
      LowersExprWith ops ctors ke tvs (patVars p ++ vs) b b' → LowersBranchesWith ops ctors ke tvs vs rest rest' →
      LowersBranchesWith ops ctors ke tvs vs ((p,b) :: rest) (b' :: rest')
end

mutual
theorem lowerExprWith_complete {ops : LoweringOps Term ParamAnn BindAnn}
    {ctors ke tvs vs s c} (h : LowersExprWith ops ctors ke tvs vs s c) :
    lowerExprWith ops ke tvs vs s = some c := by
  cases h with
  | primLitUnit | primLitInt | primLitNat | primLitChar | primLitBool | primBinOp | ctor => simp [lowerExprWith]
  | pair ha hb => simp [lowerExprWith, lowerExprWith_complete ha, lowerExprWith_complete hb]
  | cons ha hb => simp [lowerExprWith, lowerExprWith_complete ha, lowerExprWith_complete hb]
  | list hs => simp [lowerExprWith, lowerExprListWith_complete hs]
  | lambda_name ha hb => simp [lowerExprWith, ha, lowerExprWith_complete hb]
  | lambda_wild ha hb => simp [lowerExprWith, ha, lowerExprWith_complete hb]
  | @lambda_pattern tvs vs param ann ann' body body' hp ha hb =>
      cases param <;> simp_all [compoundLambdaPattern, lowerExprWith, lowerExprWith_complete hb]
  | app ha hb => simp [lowerExprWith, lowerExprWith_complete ha, lowerExprWith_complete hb]
  | letIn ha hr hw hb => simp [lowerExprWith, ha, lowerExprWith_complete hr, hw, lowerExprWith_complete hb]
  | letRecIn hr hb => simp [lowerExprWith, lowerRecBindsWith_complete hr, lowerExprWith_complete hb]
  | var hi => simp [lowerExprWith, hi]
  | ife hc ht hf => simp [lowerExprWith, lowerExprWith_complete hc, lowerExprWith_complete ht, lowerExprWith_complete hf]
  | match_ hs hb => simp [lowerExprWith, lowerExprWith_complete hs, lowerBranchesWith_complete hb]
theorem lowerExprListWith_complete {ops : LoweringOps Term ParamAnn BindAnn}
    {ctors ke tvs vs es cs} (h : LowersExprListWith ops ctors ke tvs vs es cs) :
    lowerExprListWith ops ke tvs vs es = some cs := by
  cases h with
  | nil => simp [lowerExprListWith]
  | cons he hr => simp [lowerExprListWith, lowerExprWith_complete he, lowerExprListWith_complete hr]
theorem lowerRecBindsWith_complete {ops : LoweringOps Term ParamAnn BindAnn}
    {ctors ke tvs vs bs cs} (h : LowersRecBindsWith ops ctors ke tvs vs bs cs) :
    lowerRecBindsWith ops ke tvs vs bs = some cs := by
  cases h with
  | nil => simp [lowerRecBindsWith]
  | cons ha he hw hr =>
      simp [lowerRecBindsWith, ha, lowerExprWith_complete he, hw,
        lowerRecBindsWith_complete hr]
theorem lowerBranchesWith_complete {ops : LoweringOps Term ParamAnn BindAnn}
    {ctors ke tvs vs bs cs} (h : LowersBranchesWith ops ctors ke tvs vs bs cs) :
    lowerBranchesWith ops ke tvs vs bs = some cs := by
  cases h with
  | nil => simp [lowerBranchesWith]
  | cons he hr => simp [lowerBranchesWith, lowerExprWith_complete he, lowerBranchesWith_complete hr]
end

mutual
theorem lowerExprWith_sound {ops : LoweringOps Term ParamAnn BindAnn} {ctors ke tvs vs}
    (s : Surface.Expr) {c} (h : lowerExprWith ops ke tvs vs s = some c) :
    LowersExprWith ops ctors ke tvs vs s c := by
  match s with
  | .primLit p => cases p <;> simp only [lowerExprWith, Option.some.injEq] at h <;> subst h
                  · exact .primLitUnit
                  · exact .primLitInt
                  · exact .primLitNat
                  · exact .primLitBool
                  · exact .primLitChar
  | .primBinOp op => simp only [lowerExprWith, Option.some.injEq] at h; subst h; exact .primBinOp
  | .pair a b =>
      simp only [lowerExprWith] at h
      obtain ⟨a', ha, h⟩ := lowering_bind_eq_some h
      obtain ⟨b', hb, h⟩ := lowering_bind_eq_some h
      simp only [pure, Option.some.injEq] at h; subst h
      exact .pair (lowerExprWith_sound a ha) (lowerExprWith_sound b hb)
  | .cons a b =>
      simp only [lowerExprWith] at h
      obtain ⟨a', ha, h⟩ := lowering_bind_eq_some h
      obtain ⟨b', hb, h⟩ := lowering_bind_eq_some h
      simp only [pure, Option.some.injEq] at h; subst h
      exact .cons (lowerExprWith_sound a ha) (lowerExprWith_sound b hb)
  | .list items =>
      simp only [lowerExprWith] at h
      cases he : lowerExprListWith ops ke tvs vs items with
      | none => simp [he] at h
      | some items' =>
          simp only [he, Option.map_some, Option.some.injEq] at h; subst h
          exact .list (lowerExprListWith_sound items he)
  | .lambda param ann body =>
      simp only [lowerExprWith] at h
      obtain ⟨ann', ha, h⟩ := lowering_bind_eq_some h
      cases param with
      | name x =>
          obtain ⟨b', hb, h⟩ := lowering_bind_eq_some h
          simp only [pure, Option.some.injEq] at h; subst h
          exact .lambda_name ha (lowerExprWith_sound body hb)
      | wildcard =>
          obtain ⟨b', hb, h⟩ := lowering_bind_eq_some h
          simp only [pure, Option.some.injEq] at h; subst h
          exact .lambda_wild ha (lowerExprWith_sound body hb)
      | ctor name args | pair name args | cons name args =>
          obtain ⟨b', hb, h⟩ := lowering_bind_eq_some h
          simp only [pure, Option.some.injEq] at h; subst h
          exact .lambda_pattern rfl ha (lowerExprWith_sound body hb)
      | list items =>
          obtain ⟨b', hb, h⟩ := lowering_bind_eq_some h
          simp only [pure, Option.some.injEq] at h; subst h
          exact .lambda_pattern rfl ha (lowerExprWith_sound body hb)
  | .app f x =>
      simp only [lowerExprWith] at h
      obtain ⟨f', hf, h⟩ := lowering_bind_eq_some h
      obtain ⟨x', hx, h⟩ := lowering_bind_eq_some h
      simp only [pure, Option.some.injEq] at h; subst h
      exact .app (lowerExprWith_sound f hf) (lowerExprWith_sound x hx)
  | .letIn name tyParams params ann rhs body =>
      simp only [lowerExprWith] at h
      obtain ⟨ann', ha, h⟩ := lowering_bind_eq_some h
      obtain ⟨rhsCore, hr, h⟩ := lowering_bind_eq_some h
      obtain ⟨rhs', hw, h⟩ := lowering_bind_eq_some h
      obtain ⟨body', hb, h⟩ := lowering_bind_eq_some h
      simp only [pure, Option.some.injEq] at h; subst h
      exact .letIn ha (lowerExprWith_sound rhs hr) hw (lowerExprWith_sound body hb)
  | .letRecIn binds body =>
      simp only [lowerExprWith] at h
      obtain ⟨bs', hr, h⟩ := lowering_bind_eq_some h
      obtain ⟨body', hb, h⟩ := lowering_bind_eq_some h
      simp only [pure, Option.some.injEq] at h; subst h
      exact .letRecIn (lowerRecBindsWith_sound binds hr) (lowerExprWith_sound body hb)
  | .var name =>
      simp only [lowerExprWith] at h
      cases hi : tvarIndex vs name with
      | none => simp [hi] at h
      | some i => simp only [hi, Option.map_some, Option.some.injEq] at h; subst h; exact .var hi
  | .ctor name => simp only [lowerExprWith, Option.some.injEq] at h; subst h; exact .ctor
  | .ife cond t f =>
      simp only [lowerExprWith] at h
      obtain ⟨c', hc, h⟩ := lowering_bind_eq_some h
      obtain ⟨t', ht, h⟩ := lowering_bind_eq_some h
      obtain ⟨f', hf, h⟩ := lowering_bind_eq_some h
      simp only [pure, Option.some.injEq] at h; subst h
      exact .ife (lowerExprWith_sound cond hc) (lowerExprWith_sound t ht) (lowerExprWith_sound f hf)
  | .match_ scrut brs =>
      simp only [lowerExprWith] at h
      obtain ⟨s', hs, h⟩ := lowering_bind_eq_some h
      obtain ⟨bs', hb, h⟩ := lowering_bind_eq_some h
      simp only [pure, Option.some.injEq] at h; subst h
      exact .match_ (lowerExprWith_sound scrut hs) (lowerBranchesWith_sound brs hb)
termination_by lowerExprSize s
decreasing_by
  all_goals (try simp only [lowerExprSize])
  all_goals omega
theorem lowerExprListWith_sound {ops : LoweringOps Term ParamAnn BindAnn} {ctors ke tvs vs}
    (es : List Surface.Expr) {cs} (h : lowerExprListWith ops ke tvs vs es = some cs) :
    LowersExprListWith ops ctors ke tvs vs es cs := by
  match es with
  | [] => simp only [lowerExprListWith, Option.some.injEq] at h; subst h; exact .nil
  | e :: es =>
      simp only [lowerExprListWith] at h
      obtain ⟨e', he, h⟩ := lowering_bind_eq_some h
      obtain ⟨es', hr, h⟩ := lowering_bind_eq_some h
      simp only [pure, Option.some.injEq] at h; subst h
      exact .cons (lowerExprWith_sound e he) (lowerExprListWith_sound es hr)
termination_by lowerExprListSize es
decreasing_by
  all_goals (try simp only [lowerExprListSize])
  all_goals omega
theorem lowerRecBindsWith_sound {ops : LoweringOps Term ParamAnn BindAnn} {ctors ke tvs vs}
    (bs : List Surface.Binding) {cs} (h : lowerRecBindsWith ops ke tvs vs bs = some cs) :
    LowersRecBindsWith ops ctors ke tvs vs bs cs := by
  match bs with
  | [] => simp only [lowerRecBindsWith, Option.some.injEq] at h; subst h; exact .nil
  | b :: rest =>
      simp only [lowerRecBindsWith] at h
      obtain ⟨ann', ha, h⟩ := lowering_bind_eq_some h
      obtain ⟨e', he, h⟩ := lowering_bind_eq_some h
      obtain ⟨wrapped, hw, h⟩ := lowering_bind_eq_some h
      obtain ⟨rest', hr, h⟩ := lowering_bind_eq_some h
      simp only [pure, Option.some.injEq] at h; subst h
      exact .cons ha (lowerExprWith_sound b.rhs he) hw (lowerRecBindsWith_sound rest hr)
termination_by lowerRecBindsSize bs
decreasing_by
  all_goals (try simp only [lowerRecBindsSize])
  all_goals omega
theorem lowerBranchesWith_sound {ops : LoweringOps Term ParamAnn BindAnn} {ctors ke tvs vs}
    (bs : List (Surface.Pattern × Surface.Expr)) {cs} (h : lowerBranchesWith ops ke tvs vs bs = some cs) :
    LowersBranchesWith ops ctors ke tvs vs bs cs := by
  match bs with
  | [] => simp only [lowerBranchesWith, Option.some.injEq] at h; subst h; exact .nil
  | (pat, b) :: rest =>
      simp only [lowerBranchesWith] at h
      obtain ⟨e', he, h⟩ := lowering_bind_eq_some h
      obtain ⟨rest', hr, h⟩ := lowering_bind_eq_some h
      simp only [pure, Option.some.injEq] at h; subst h
      exact .cons (lowerExprWith_sound b he) (lowerBranchesWith_sound rest hr)
termination_by lowerBranchesSize bs
decreasing_by
  all_goals (try simp only [lowerBranchesSize])
  all_goals omega
end


/-- Production annotation policy: preserve holes and scoped partial signatures. -/
def inputLoweringOps : LoweringOps InferInput (Option TyTemplate) BindingAnn :=
  { emission := inputEmissionOps
    primLit := InferInput.primLit
    primBinOp := InferInput.primBinOp
    app := InferInput.app
    lambda := InferInput.lambda
    letIn := InferInput.letIn
    letRec := InferInput.letRec
    lowerParamAnn := lowerTemplateAnn
    finalize := finalizeInputAnn
    lowerBindAnn := lowerInputLetAnn }
abbrev lowerInputExpr := lowerExprWith inputLoweringOps
abbrev lowerInputExprList := lowerExprListWith inputLoweringOps
abbrev lowerInputBranches := lowerBranchesWith inputLoweringOps
abbrev lowerInputRecBinds := lowerRecBindsWith inputLoweringOps
abbrev wrapInputParams := inputLoweringOps.wrapParams
abbrev mkInputList := inputLoweringOps.mkList
abbrev InputLowersExpr := LowersExprWith inputLoweringOps
abbrev InputLowersExprList := LowersExprListWith inputLoweringOps
abbrev InputLowersBranches := LowersBranchesWith inputLoweringOps
abbrev InputLowersRecBinds := LowersRecBindsWith inputLoweringOps

def lowerInput (ctors : CtorEnv) (s : Surface.Expr) : Option InferInput :=
  lowerInputExpr (kindEnvOfCtors ctors) [] [] s

def InputLowers (ctors : CtorEnv) (s : Surface.Expr) (input : InferInput) : Prop :=
  InputLowersExpr ctors (kindEnvOfCtors ctors) [] [] s input

theorem lowerInputExpr_sound {ctors ke tvs vs s input}
    (h : lowerInputExpr ke tvs vs s = some input) : InputLowersExpr ctors ke tvs vs s input :=
  lowerExprWith_sound s h

theorem lowerInputExpr_complete {ctors ke tvs vs s input}
    (h : InputLowersExpr ctors ke tvs vs s input) : lowerInputExpr ke tvs vs s = some input :=
  lowerExprWith_complete h

theorem InputLowersExpr.unique {ctors ke tvs vs s a b}
    (ha : InputLowersExpr ctors ke tvs vs s a) (hb : InputLowersExpr ctors ke tvs vs s b) : a = b :=
  Option.some.inj ((lowerInputExpr_complete ha).symm.trans (lowerInputExpr_complete hb))

theorem lowerInput_sound {ctors s input} (h : lowerInput ctors s = some input) : InputLowers ctors s input :=
  lowerInputExpr_sound h

theorem lowerInput_complete {ctors s input} (h : InputLowers ctors s input) : lowerInput ctors s = some input :=
  lowerInputExpr_complete h

/-- The same declaration elaboration precedes canonical annotated expression lowering. -/
def lowerInputProgram (p : Surface.Program) : Option (CtorEnv × InferInput) := do
  let userCore ← lowerDataDeclsIn preludeKindEnv p.decls
  let ctors ← elabDecls (preludeDecls ++ userCore)
  let input ← lowerInput ctors p.term
  pure (ctors, input)

inductive InputLowersProgram : Surface.Program → CtorEnv → InferInput → Prop where
  | mk {p userCore ctors input} :
      LowersDataDeclsIn preludeKindEnv p.decls userCore →
      DataDecls.WF (preludeDecls ++ userCore) →
      elabDecls (preludeDecls ++ userCore) = some ctors →
      InputLowers ctors p.term input → InputLowersProgram p ctors input

theorem lowerInputProgram_sound {p ctors input} (h : lowerInputProgram p = some (ctors,input)) :
    InputLowersProgram p ctors input := by
  obtain ⟨userCore, huser, h⟩ := lowering_bind_eq_some h
  obtain ⟨ctors', helab, h⟩ := lowering_bind_eq_some h
  obtain ⟨input', hi, h⟩ := lowering_bind_eq_some h
  simp only [pure, Option.some.injEq, Prod.mk.injEq] at h
  rcases h with ⟨rfl,rfl⟩
  exact .mk (lowerDataDeclsIn_sound huser) (elabDecls_sound helab) helab (lowerInput_sound hi)

theorem lowerInputProgram_complete {p ctors input} (h : InputLowersProgram p ctors input) :
    lowerInputProgram p = some (ctors,input) := by
  cases h with
  | mk hd _hwf he hl => simp [lowerInputProgram, lowerDataDeclsIn_complete hd, he, lowerInput_complete hl]

/-- Canonical surface lowering preserves partial annotations for inference. -/
abbrev lowerExpr := lowerInputExpr
abbrev lowerExprList := lowerInputExprList
abbrev lowerBranches := lowerInputBranches
abbrev lowerRecBinds := lowerInputRecBinds
abbrev LowersExpr := InputLowersExpr
abbrev LowersExprList := InputLowersExprList
abbrev LowersBranches := InputLowersBranches
abbrev LowersRecBinds := InputLowersRecBinds
abbrev lower := lowerInput
abbrev Lowers := InputLowers
abbrev lowerProgram := lowerInputProgram
abbrev LowersProgram := InputLowersProgram

theorem lowerExpr_sound {ctors : CtorEnv} {ke : KindEnv} {tvs vs : List ValName}
    {s : Surface.Expr} {input : InferInput}
    (h : lowerExpr ke tvs vs s = some input) : LowersExpr ctors ke tvs vs s input :=
  lowerInputExpr_sound h

theorem lowerExpr_complete {ctors : CtorEnv} {ke : KindEnv} {tvs vs : List ValName}
    {s : Surface.Expr} {input : InferInput}
    (h : LowersExpr ctors ke tvs vs s input) : lowerExpr ke tvs vs s = some input :=
  lowerInputExpr_complete h

theorem LowersExpr.unique {ctors : CtorEnv} {ke : KindEnv} {tvs vs : List ValName}
    {s : Surface.Expr} {a b : InferInput}
    (ha : LowersExpr ctors ke tvs vs s a) (hb : LowersExpr ctors ke tvs vs s b) : a = b :=
  InputLowersExpr.unique ha hb

theorem lower_sound {ctors : CtorEnv} {s : Surface.Expr} {input : InferInput}
    (h : lower ctors s = some input) : Lowers ctors s input :=
  lowerInput_sound h

theorem lower_complete {ctors : CtorEnv} {s : Surface.Expr} {input : InferInput}
    (h : Lowers ctors s input) : lower ctors s = some input :=
  lowerInput_complete h

theorem lowerProgram_sound {p : Surface.Program} {ctors : CtorEnv} {input : InferInput}
    (h : lowerProgram p = some (ctors, input)) : LowersProgram p ctors input :=
  lowerInputProgram_sound h

theorem lowerProgram_complete {p : Surface.Program} {ctors : CtorEnv} {input : InferInput}
    (h : LowersProgram p ctors input) : lowerProgram p = some (ctors, input) :=
  lowerInputProgram_complete h


/-! ## 5. Surface pattern well-formedness + coverage predicates

`PatternWF` is the surface-level counterpart of `GPatWF`: a pattern is well-formed
at type `τ` when its constructors exist and sub-patterns fit field types (with
sugar `pair`/`cons`/`list` desugaring to `Pair`/`Cons`/`Nil`). The bridge lemma
`PatternWF_to_GPatWF` connects it to the kernel's `GPatWF (norm p)`.

`MatchPatternsCover` / `SurfaceCovers` are the exhaustiveness side: at each
`match`, patterns must cover the scrutinee's ADT type `T` (every ctor of `T` has
a testing branch, or a trailing irrefutable catch-all). The type `T` is carried
in the `SurfaceCovers.match_` witness; the executable checker reconstructs it
from the branch patterns and fails closed when it cannot. -/

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
    decidable, honest coverage condition. The opt-in complete-Core compatibility
    proof connects it to Core's `AllMatchesExhaustive`. A flat "top-level ctors
    covered" check is UNSOUND (misses
    nested gaps: `Cons (Just x) t | Nil` leaves `Cons Nothing Nil` — the `Cons`
    sub-switch omits `Nothing`, so `DTreeExhaustive` fails there, correctly). -/
def MatchExhaustive (ctors : CtorEnv) (T : TyName) (tyArgs : List Ty)
    (ps : List Surface.Pattern) : Prop :=
  DTreeExhaustive ctors [([], .customTy T tyArgs)] (compile [[]] (initMatrix ps))

/-- Every `match` in `s` is exhaustive (and subexpressions recurse). At `match_`
    the witness carries the scrutinee's ADT type `(T, tyArgs)` and the lowering proof instantiates it
    from the lowered scrutinee's typing. -/
inductive SurfaceCovers (ctors : CtorEnv) : Surface.Expr → Prop where
  | primLit {p} : SurfaceCovers ctors (.primLit p)
  | primBinOp {op} : SurfaceCovers ctors (.primBinOp op)
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
      (∃ T tyArgs, MatchExhaustive ctors T tyArgs [param]) →
      SurfaceCovers ctors (.lambda param ann body)
  | app {f x} :
      SurfaceCovers ctors f → SurfaceCovers ctors x →
      SurfaceCovers ctors (.app f x)
  | letIn {name tyParams params ann rhs body} :
      SurfaceCovers ctors rhs → SurfaceCovers ctors body →
      SurfaceCovers ctors (.letIn name tyParams params ann rhs body)
  | letRecIn {binds body} :
      (∀ b ∈ binds, SurfaceCovers ctors b.rhs) → SurfaceCovers ctors body →
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

mutual

/-- Infer only the type constraints contributed by constructor tests. Wildcards
    and binders impose none. This proposes a coverage witness; acceptance still
    goes through `matchExhaustiveB` and its soundness theorem. -/
private def constrainCoveragePat (ctors : CtorEnv) :
    GPat → Ty → Nat → Subst → Option (Nat × Subst)
  | .gbind, _, next, S | .gwild, _, next, S => some (next, S)
  | .gctor name pats, expected, next, S => do
      let ctor ← LookupList.get? ctors name
      let args := (List.range ctor.paramCount).map fun i => Ty.fvar (next + i)
      let U ← unify (S.onTy expected) (.customTy ctor.tyName args)
      constrainCoveragePats ctors pats (ctor.contents.map (Ty.openWith args))
        (next + ctor.paramCount) (S ++ U)

private def constrainCoveragePats (ctors : CtorEnv) :
    List GPat → List Ty → Nat → Subst → Option (Nat × Subst)
  | [], [], next, S => some (next, S)
  | p :: ps, t :: ts, next, S => do
      let (next, S) ← constrainCoveragePat ctors p t next S
      constrainCoveragePats ctors ps ts next S
  | _, _, _, _ => none

end

/-- Recover nested type arguments from all branch patterns, sharing root type
    variables across rows and freshening each constructor's parameters. Unlike
    `Unit` placeholders, these retain the ADT structure needed by nested switches.
    The existing tree checker remains the final, proved acceptance gate. -/
private def tyArgsGuess (ctors : CtorEnv) (T : TyName)
    (ps : List Surface.Pattern) : List Ty :=
  match ctors.find? fun ⟨_, ctor⟩ => ctor.tyName == T with
  | some ⟨_, ctor⟩ =>
      let args := (List.range ctor.paramCount).map Ty.fvar
      let root := Ty.customTy T args
      match constrainCoveragePats ctors (ps.map norm) (List.replicate ps.length root)
          ctor.paramCount [] with
      | some (_, S) => args.map S.onTy
      | none => List.replicate ctor.paramCount (.prim .unit)
  | none => []

/-- Top-level ctor name in a pattern, if any (incl. List/Pair sugar). -/
private def patternTopCtor : Surface.Pattern → Option CtorName
  | .ctor n _ => some n
  | .cons _ _ => some cCons
  | .list [] => some cNil
  | .list (_ :: _) => some cCons
  | .pair _ _ => some cPair
  | .name _ | .wildcard => none

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

/-- Single-branch coverage used by lambda parameters, including the
    irrefutable name/wildcard cases. -/
private def checkLambdaPattern (ctors : CtorEnv) (param : Surface.Pattern) : Bool :=
  match tyNameFromPatterns ctors [param] with
  | some T => matchExhaustiveB ctors T (tyArgsGuess ctors T [param]) [param]
  | none => matchExhaustiveB ctors nBool [] [param]

mutual

/-- Structural size for `checkExhaustive` termination (mirrors `Core.Expr.size`). -/
def surfaceExprSize : Surface.Expr → Nat
  | .primLit _ | .primBinOp _ | .var _ | .ctor _ => 1
  | .pair a b => 1 + surfaceExprSize a + surfaceExprSize b
  | .cons h t => 1 + surfaceExprSize h + surfaceExprSize t
  | .list items => 1 + surfaceExprSizeList items
  | .lambda _ _ body => 1 + surfaceExprSize body
  | .app f x => 1 + surfaceExprSize f + surfaceExprSize x
  | .letIn _ _ _ _ rhs body => 1 + surfaceExprSize rhs + surfaceExprSize body
  | .letRecIn binds body => 1 + surfaceExprSizeLetRecBinds binds + surfaceExprSize body
  | .ife c t f => 1 + surfaceExprSize c + surfaceExprSize t + surfaceExprSize f
  | .match_ scrut brs => 1 + surfaceExprSize scrut + surfaceExprSizeBranches brs

def surfaceExprSizeList : List Surface.Expr → Nat
  | [] => 0
  | e :: es => 1 + surfaceExprSize e + surfaceExprSizeList es

def surfaceExprSizeLetRecBinds : List Surface.Binding → Nat
  | [] => 0
  | { rhs := r, .. } :: rest => 1 + surfaceExprSize r + surfaceExprSizeLetRecBinds rest

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
    List Surface.Binding → Bool
  | [] => true
  | b :: rest =>
      checkExhaustive ctors b.rhs && checkExhaustiveLetRecBinds ctors rest
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
  | .primLit _ | .primBinOp _ | .var _ | .ctor _ => true
  | .pair a b => checkExhaustive ctors a && checkExhaustive ctors b
  | .cons h t => checkExhaustive ctors h && checkExhaustive ctors t
  | .list items => checkExhaustiveList ctors items
  | .lambda param _ body => checkExhaustive ctors body && checkLambdaPattern ctors param
  | .app f x => checkExhaustive ctors f && checkExhaustive ctors x
  | .letIn _ _ _ _ rhs body =>
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
          matchExhaustiveB ctors T (tyArgsGuess ctors T (brs.map Prod.fst)) (brs.map Prod.fst)
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

private theorem surfaceExprSize_lt_letIn_rhs (vname : ValName) (tyParams : List ValName)
    (params : List (ValName × Option Surface.Ty)) (ann : Option Surface.PolyTy)
    (rhs body : Surface.Expr) :
    surfaceExprSize rhs < surfaceExprSize (.letIn vname tyParams params ann rhs body) := by
  simp only [surfaceExprSize]; omega

private theorem surfaceExprSize_lt_letIn_body (vname : ValName) (tyParams : List ValName)
    (params : List (ValName × Option Surface.Ty)) (ann : Option Surface.PolyTy)
    (rhs body : Surface.Expr) :
    surfaceExprSize body < surfaceExprSize (.letIn vname tyParams params ann rhs body) := by
  simp only [surfaceExprSize]; omega

private theorem surfaceExprSize_lt_letRecIn_body
    (binds : List Surface.Binding) (body : Surface.Expr) :
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

private theorem checkLambdaPattern_sound {ctors : CtorEnv} {param : Surface.Pattern}
    (h : checkLambdaPattern ctors param = true) :
    ∃ T tyArgs, MatchExhaustive ctors T tyArgs [param] := by
  unfold checkLambdaPattern at h
  cases ht : tyNameFromPatterns ctors [param] with
  | none => exact ⟨nBool, [], matchExhaustiveB_sound (by simpa [ht] using h)⟩
  | some T => exact ⟨T, tyArgsGuess ctors T [param],
      matchExhaustiveB_sound (by simpa [ht] using h)⟩

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
      ∀ b ∈ binds, checkExhaustive ctors b.rhs = true
  | [] => by intro _ b hb; nomatch hb
  | b :: rest => by
    intro h b' hb'
    simp only [checkExhaustiveLetRecBinds, Bool.and_eq_true] at h
    simp only [List.mem_cons] at hb'
    rcases hb' with rfl | hb'
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
    {binds : List Surface.Binding}
    {body : Surface.Expr}
    {b : Surface.Binding}
    (h : b ∈ binds) :
    surfaceExprSize b.rhs < surfaceExprSize (.letRecIn binds body) := by
  induction binds with
  | nil => nomatch h
  | cons hd rest ih =>
    simp only [List.mem_cons] at h
    rcases h with rfl | h
    · simp only [surfaceExprSize, surfaceExprSizeLetRecBinds]; omega
    · have hlt := ih h
      have htail : surfaceExprSize (.letRecIn rest body) <
          surfaceExprSize (.letRecIn (hd :: rest) body) := by
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
    | .primBinOp _ => exact .primBinOp
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
      simp only [checkExhaustive, Bool.and_eq_true] at h
      have hle : surfaceExprSize body ≤ n :=
        Nat.le_of_lt_succ (Nat.lt_of_lt_of_le (surfaceExprSize_lt_lambda_body param ann body) hsz)
      exact .lambda (ih body hle h.1) (checkLambdaPattern_sound h.2)
    | .app f x =>
      simp only [checkExhaustive, Bool.and_eq_true] at h
      have hle₁ : surfaceExprSize f ≤ n :=
        Nat.le_of_lt_succ (Nat.lt_of_lt_of_le (surfaceExprSize_lt_app_fn f x) hsz)
      have hle₂ : surfaceExprSize x ≤ n :=
        Nat.le_of_lt_succ (Nat.lt_of_lt_of_le (surfaceExprSize_lt_app_arg f x) hsz)
      exact .app (ih f hle₁ h.1) (ih x hle₂ h.2)
    | .letIn vname tyParams params ann rhs body =>
      simp only [checkExhaustive, Bool.and_eq_true] at h
      have hle₁ : surfaceExprSize rhs ≤ n :=
        Nat.le_of_lt_succ (Nat.lt_of_lt_of_le
          (surfaceExprSize_lt_letIn_rhs vname tyParams params ann rhs body) hsz)
      have hle₂ : surfaceExprSize body ≤ n :=
        Nat.le_of_lt_succ (Nat.lt_of_lt_of_le
          (surfaceExprSize_lt_letIn_body vname tyParams params ann rhs body) hsz)
      exact .letIn (ih rhs hle₁ h.1) (ih body hle₂ h.2)
    | .letRecIn binds body =>
      simp only [checkExhaustive, Bool.and_eq_true] at h
      refine .letRecIn ?_ (ih body (Nat.le_of_lt_succ (Nat.lt_of_lt_of_le
        (surfaceExprSize_lt_letRecIn_body binds body) hsz)) h.2)
      intro b hb
      have heq := checkExhaustiveLetRecBinds_get binds h.1 b hb
      have hle : surfaceExprSize b.rhs ≤ n :=
        Nat.le_of_lt_succ (Nat.lt_of_lt_of_le (surfaceExprSize_lt_of_mem_letRecBinds hb) hsz)
      exact ih b.rhs hle heq
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
        refine .match_ (T := T) (tyArgs := tyArgsGuess ctors T (brs.map Prod.fst)) (ih scrut hscrut hs) ?_ ?_
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

private def ctorsDemo : CtorEnv := (elabDecls preludeDecls).getD []

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

-- List sugar (`[]` / `h :: t`) recovers `nList` via `patternTopCtor`, not Bool fallback.
#guard checkExhaustive ctorsDemo
  (.match_ (.var (.mk "xs"))
    [(.list [], .primLit (.int 0)),
     (.cons (.name (.mk "h")) (.name (.mk "t")), .primLit (.int 1))]) = true

-- Nested parameter positions must retain the types imposed by their patterns.
example : checkExhaustive ctorsDemo
    (.match_ (.var (.mk "p"))
      [(.pair (.pair .wildcard .wildcard) .wildcard, .primLit (.int 0))]) = true := by
  native_decide

example : checkExhaustive ctorsDemo
    (.match_ (.var (.mk "p"))
      [(.pair .wildcard (.pair .wildcard .wildcard), .primLit (.int 0))]) = true := by
  native_decide

example : checkExhaustive ctorsDemo
    (.match_ (.var (.mk "xs"))
      [(.list [], .primLit (.int 0)),
       (.cons (.list []) .wildcard, .primLit (.int 1)),
       (.cons (.cons .wildcard .wildcard) .wildcard, .primLit (.int 2))]) = true := by
  native_decide

-- Covering the outer List does not excuse an uncovered nonempty inner List.
example : checkExhaustive ctorsDemo
    (.match_ (.var (.mk "xs"))
      [(.list [], .primLit (.int 0)),
       (.cons (.list []) .wildcard, .primLit (.int 1))]) = false := by
  native_decide



end SurfaceBridge

/-! ## Lowering -/

section

/-! Annotation adapters for the shared surface and pattern-lowering pipeline.
Holes remain syntax until inference visits each generated occurrence. -/

@[simp] private theorem eraseBindings_length (bindings : List InputRecBinding) :
    (eraseBindings bindings).length = bindings.length := by
  induction bindings with
  | nil => rfl
  | cons binding rest ih =>
      rcases binding with ⟨ann, rhs⟩
      simp only [eraseBindings, List.length_cons, ih]

mutual
/-- Erasure commutes with term shifting, including recursive group binders. -/
theorem InferInput.erase_shiftFrom (input : InferInput) (threshold count : Nat) :
    (input.shiftFrom threshold count).erase = input.erase.shiftFrom threshold count := by
  cases input with
  | primLit p => rfl
  | primBinOp op => rfl
  | var i => simp only [InferInput.shiftFrom, InferInput.erase, Expr.shiftFrom]; split <;> rfl
  | ctor name => rfl
  | lambda ann body =>
    simp only [InferInput.shiftFrom, InferInput.erase, Expr.shiftFrom, body.erase_shiftFrom]
  | app f arg =>
    simp only [InferInput.shiftFrom, InferInput.erase, Expr.shiftFrom, f.erase_shiftFrom, arg.erase_shiftFrom]
  | letIn ann rhs body =>
    simp only [InferInput.shiftFrom, InferInput.erase, Expr.shiftFrom, rhs.erase_shiftFrom, body.erase_shiftFrom]
  | match_ scrut branches =>
    simp only [InferInput.shiftFrom, InferInput.erase, scrut.erase_shiftFrom]
    change Expr.match_ (scrut.erase.shiftFrom threshold count) (eraseBranches (shiftBranches threshold count branches)) =
      Expr.match_ (scrut.erase.shiftFrom threshold count)
        (((Expr.match_ (.primLit .unit) (eraseBranches branches)).shiftFrom threshold count).matchBranchesOf)
    rw [eraseBranches_shiftFrom]
  | letRec bindings body =>
    have hbindings := eraseBindings_shiftFrom bindings (threshold + bindings.length) count
    simp only [InferInput.shiftFrom, InferInput.erase, Expr.shiftFrom, body.erase_shiftFrom,
      hbindings, eraseBindings_length]
termination_by sizeOf input
decreasing_by
  all_goals simp_wf
  all_goals omega
private theorem eraseBranches_shiftFrom (branches : List (MatchPattern × InferInput)) (threshold count : Nat) :
    eraseBranches (shiftBranches threshold count branches) =
      ((Expr.match_ (.primLit .unit) (eraseBranches branches)).shiftFrom threshold count).matchBranchesOf := by
  cases branches with
  | nil => rfl
  | cons head rest =>
    rcases head with ⟨pat, body⟩
    change (pat, (body.shiftFrom (threshold + pat.bindCount) count).erase) ::
      eraseBranches (shiftBranches threshold count rest) =
      (pat, body.erase.shiftFrom (threshold + pat.bindCount) count) ::
        (((Expr.match_ (.primLit .unit) (eraseBranches rest)).shiftFrom threshold count).matchBranchesOf)
    rw [body.erase_shiftFrom, eraseBranches_shiftFrom]
termination_by sizeOf branches
decreasing_by
  all_goals simp_wf
  all_goals omega
private theorem eraseBindings_shiftFrom (bindings : List InputRecBinding) (threshold count : Nat) :
    eraseBindings (shiftBindings threshold count bindings) =
      RecGroup.shiftFrom threshold count (eraseBindings bindings) := by
  cases bindings with
  | nil => rfl
  | cons binding rest =>
    rcases binding with ⟨ann, rhs⟩
    have hrest := eraseBindings_shiftFrom rest threshold count
    simp only [shiftBindings, eraseBindings, RecGroup.shiftFrom, rhs.erase_shiftFrom, hrest]
termination_by sizeOf bindings
decreasing_by
  all_goals simp_wf
  all_goals omega
end

private theorem eraseBranches_append (left right : List (MatchPattern × InferInput)) :
    eraseBranches (left ++ right) = eraseBranches left ++ eraseBranches right := by
  induction left with
  | nil => rfl
  | cons head rest ih => rcases head with ⟨pat, body⟩; simp only [List.cons_append, eraseBranches, ih]

private theorem erase_emitLetsInput (env binds : List PatComp.Occ) (body : InferInput) :
    (PatComp.emitLetsWith inputEmissionOps env binds body).erase =
      PatComp.emitLets env binds body.erase := by
  have hgo : ∀ rest depth,
      (PatComp.emitLetsWith.go inputEmissionOps env binds body rest depth).erase =
        PatComp.emitLets.go env binds body.erase rest depth := by
    intro rest
    induction rest with
    | nil => intro depth; exact body.erase_shiftFrom _ _
    | cons head rest ih =>
      intro depth
      change Expr.letIn none (.var _) _ = Expr.letIn none (.var _) _
      rw [ih]
      rfl
  exact hgo binds.reverse 0

mutual
/-- The shared emitter has the same erased runtime structure for InferInput and Core. -/
theorem erase_emitInput (env : List PatComp.Occ) (bodies : Nat → InferInput) (tree : PatComp.DTree) :
    (PatComp.emitWith inputEmissionOps env bodies tree).erase =
      PatComp.emit env (fun i => (bodies i).erase) tree := by
  cases tree with
  | fail => rfl
  | leaf act binds => exact erase_emitLetsInput env binds (bodies act)
  | switch occ cases dflt =>
    by_cases hd : dflt = .fail
    · subst dflt
      rw [PatComp.emitWith.eq_3, PatComp.emit, PatComp.emitWith.eq_3]
      change Expr.match_ (.var _) (eraseBranches (_ ++ [])) = Expr.match_ (.var _) (_ ++ [])
      simp only [List.append_nil]
      rw [erase_emitCasesInput env bodies occ cases]
      rfl
    · rw [PatComp.emitWith.eq_4 _ _ _ _ _ _ hd, PatComp.emit,
        PatComp.emitWith.eq_4 _ _ _ _ _ _ hd]
      change Expr.match_ (.var _) (eraseBranches (_ ++ [(.wildcard,
        PatComp.emitWith inputEmissionOps env bodies dflt)])) = Expr.match_ (.var _) (_ ++ _)
      rw [eraseBranches_append, erase_emitCasesInput env bodies occ cases]
      simp only [eraseBranches]
      rw [erase_emitInput env bodies dflt]
      rfl

termination_by sizeOf tree
decreasing_by
  all_goals simp_wf
  all_goals omega
private theorem erase_emitCasesInput (env : List PatComp.Occ) (bodies : Nat → InferInput)
    (occ : PatComp.Occ) (cases : List (CtorName × Nat × PatComp.DTree)) :
    eraseBranches (PatComp.emitCasesWith inputEmissionOps env bodies occ cases) =
      PatComp.emitCases env (fun i => (bodies i).erase) occ cases := by
  cases cases with
  | nil => rfl
  | cons head rest =>
    rcases head with ⟨name, arity, tree⟩
    change (MatchPattern.named name arity,
      (PatComp.emitWith inputEmissionOps (PatComp.subOccs occ arity ++ env) bodies tree).erase) ::
      eraseBranches (PatComp.emitCasesWith inputEmissionOps env bodies occ rest) = _
    rw [erase_emitInput, erase_emitCasesInput env bodies occ rest]
    rfl
termination_by sizeOf cases
decreasing_by
  all_goals simp_wf
  all_goals omega
end

@[simp] theorem erase_lowerInputMatch (scrut : InferInput) (pats : List Surface.Pattern)
    (bodies : Nat → InferInput) :
    (lowerInputMatch scrut pats bodies).erase =
      PatComp.lowerMatch scrut.erase pats (fun i => (bodies i).erase) := by
  change Expr.letIn none scrut.erase _ = Expr.letIn none scrut.erase _
  rw [erase_emitInput]
  rfl

end
