import FHM.TypedResult

/-! # Verified type-declaration elaboration

The surface language lets users declare algebraic data types (`type Maybe a =
Just a | Nothing`). After name resolution they arrive here as `DataDecl`s — with
type params already turned into de Bruijn `bvar`s (matching `Ctor.paramCount`) —
which are validated and elaborated into the `CtorEnv` that `Core`'s typing rules
(`ctor`, `match_`, the comparison primops) consult.

**Nothing new is needed in `Core`.** `Ctor`/`CtorEnv` already exist, and every
Core theorem is `∀ ctors`, so a well-formed declaration group is simply a
well-formed `CtorEnv` the existing metatheory already covers. This module is the
front-end that *produces* such an env.

This file contains the declarative specification—the `DataDecl` AST and the
predicates for well-formed declaration groups—together with a decidable checker
and a verified elaborator into `CtorEnv`.

## The two passes (why the spec is shaped this way)

Types may reference each other out of order and mutually (`type Tree a = Node a
(Forest a)` / `type Forest a = …`). So well-formedness is stated in two stages,
mirroring how the checker runs:

1. **Collect** a `KindEnv` — every declared type name with its arity
   (`DataDecls.kindEnv`). This is a pure "names first" pass.
2. **Check** each constructor's field types against that `KindEnv`
   (`Ty.WellKinded`): type applications reference only declared types at the
   right arity, own-params are in range, and there are no free type variables. -/


/-- A resolved algebraic data-type declaration: a type constructor `name` of
    arity `paramCount`, with data constructors each carrying a list of field
    types. A field type may reference this type's own params via `.bvar i`
    (`i < paramCount`) and any declared type via `.customTy`; it carries no
    `.fvar`s. (This is the *post-name-resolution* form — the surface syntax with
    named params/fields resolves down to this.) -/
structure DataDecl where
  name : TyName
  paramCount : Nat
  ctors : List (CtorName × List Ty)
  deriving Repr


/-- The kinding environment for a declaration group: each declared type name
    mapped to its arity. Produced by the "names first" pass so that constructor
    bodies may reference types declared out of order or mutually. -/
abbrev KindEnv := LookupList TyName Nat


/-- **Kinding of a field type**, relative to a kind env `ke` and the declaring
    type's arity `pc`. This single predicate bundles the three obligations a
    `Ctor` field must meet — and, being an inductive over `Ty`, it *is* the
    "kind-checking logic":

    * **type applications** (`customTy T args`) reference a *declared* type `T`
      at its *declared arity* (`get? ke T = some args.length`), recursively;
    * **bound type vars** are in range (`bvar i` with `i < pc`) — the declaring
      type's own parameters, nothing else;
    * **closedness**: no `fvar` (note the deliberate absence of an `fvar` case).

    Consequently `WellKinded ke pc ty` implies both `ContainsBvarsUpTo pc ty`
    (the `Ctor.bound` obligation) and `NoFreeVars ty` (the `Ctor.closed`
    obligation) — so the elaborator can discharge a `Ctor`'s side-conditions
    straight from this. -/
inductive Ty.WellKinded (ke : KindEnv) (pc : Nat) : Ty → Prop
  | prim {p} :
      Ty.WellKinded ke pc (.prim p)
  | bvar {i} :
      i < pc →
      Ty.WellKinded ke pc (.bvar i)
  | arrow {a b} :
      Ty.WellKinded ke pc a →
      Ty.WellKinded ke pc b →
      Ty.WellKinded ke pc (.arrow a b)
  | customTy {T args} :
      LookupList.get? ke T = some args.length →
      (∀ arg ∈ args, Ty.WellKinded ke pc arg) →
      Ty.WellKinded ke pc (.customTy T args)


/-- Pass 1: the kind env induced by a declaration group (names + arities). -/
def DataDecls.kindEnv (decls : List DataDecl) : KindEnv :=
  decls.map (fun d => (d.name, d.paramCount))


/-- A single declaration is well-formed against a kind env when every field type
    of every constructor is well-kinded at the declaration's arity. -/
def DataDecl.WF (ke : KindEnv) (d : DataDecl) : Prop :=
  ∀ c ∈ d.ctors, ∀ ty ∈ c.2, Ty.WellKinded ke d.paramCount ty


/-- **A declaration group is well-formed** when, against the group's own kind env:
    every declaration's fields are well-kinded, and both the type names and the
    (group-wide) constructor names are distinct (the `CtorEnv` is keyed by ctor
    name, so ctor names must be globally unique). -/
structure DataDecls.WF (decls : List DataDecl) : Prop where
  /-- every declaration's constructor fields are well-kinded against the group env -/
  fields : ∀ d ∈ decls, DataDecl.WF (DataDecls.kindEnv decls) d
  /-- declared type names are distinct -/
  tyNamesNodup : (decls.map (·.name)).Nodup
  /-- constructor names are distinct across the whole group -/
  ctorNamesNodup : (decls.flatMap (fun d => d.ctors.map Prod.fst)).Nodup


/-- The semantic fields of a constructor, independent of its proof fields. -/
def Ctor.signature (ctor : Ctor) : Nat × TyName × List Ty :=
  (ctor.paramCount, ctor.tyName, ctor.contents)

def CtorEnv.signatures (env : CtorEnv) : List (CtorName × (Nat × TyName × List Ty)) :=
  env.map fun entry => (entry.1, entry.2.signature)

/-- Written constructors in declaration order, including all their type data. -/
def DataDecls.constructorSignatures (decls : List DataDecl) :
    List (CtorName × (Nat × TyName × List Ty)) :=
  (decls.map fun decl => decl.ctors.map fun ctor =>
    (ctor.1, (decl.paramCount, decl.name, ctor.2))).flatten

/-- Declaration elaboration preserves every constructor and all its fields.
The equality also excludes missing, extra, duplicated or reordered entries. -/
structure DataDecls.ElaboratesTo (decls : List DataDecl) (env : CtorEnv) : Prop where
  wellFormed : DataDecls.WF decls
  constructors : env.signatures = DataDecls.constructorSignatures decls

theorem Ctor.signature_injective : Function.Injective Ctor.signature := by
  rintro ⟨ap, an, ac, ab, af⟩ ⟨bp, bn, bc, bb, bf⟩ h
  simp only [Ctor.signature, Prod.mk.injEq] at h
  rcases h with ⟨rfl, rfl, rfl⟩
  rfl

theorem CtorEnv.signatures_injective : Function.Injective CtorEnv.signatures := by
  intro a b h
  induction a generalizing b with
  | nil => cases b <;> simp_all [CtorEnv.signatures]
  | cons x xs ih =>
    cases b with
    | nil => simp [CtorEnv.signatures] at h
    | cons y ys =>
      simp only [CtorEnv.signatures, List.map_cons, List.cons.injEq] at h
      have hname : x.1 = y.1 := congrArg
        (fun entry : CtorName × (Nat × TyName × List Ty) => entry.1) h.1
      have hsignature : x.2.signature = y.2.signature := congrArg
        (fun entry : CtorName × (Nat × TyName × List Ty) => entry.2) h.1
      have hxy : x = y := Prod.ext hname (Ctor.signature_injective hsignature)
      exact congrArg₂ List.cons hxy (ih h.2)

theorem DataDecls.ElaboratesTo.unique
    (ha : DataDecls.ElaboratesTo decls a) (hb : DataDecls.ElaboratesTo decls b) : a = b :=
  CtorEnv.signatures_injective (ha.constructors.trans hb.constructors.symm)


/-! ## The executable side (checker, elaborator, prelude)

Everything below turns the spec above into running code with proofs — no `Core`
changes needed. `bvarsBelow`-style helpers live in `InferW` (not importable
here), so the checkers are self-contained, reusing only `Core`'s `Ty`,
`ContainsBvarsUpTo`, `NoFreeVars`, `Ctor`, and `LookupList.get?`. -/


/-! ### 1. The `Bool` kind-checker (mirrors `Core`'s `Ty.freeVars` mutual idiom). -/

mutual
/-- Decidable kind-check of a single field type against `ke` at arity `pc`. -/
def Ty.wellKindedB (ke : KindEnv) (pc : Nat) : Ty → Bool
  | .prim _        => true
  | .bvar i        => decide (i < pc)
  | .fvar _        => false
  | .arrow a b     => Ty.wellKindedB ke pc a && Ty.wellKindedB ke pc b
  | .customTy T args => decide (LookupList.get? ke T = some args.length) && TyList.wellKindedB ke pc args
/-- Pointwise kind-check of a list of field types. -/
def TyList.wellKindedB (ke : KindEnv) (pc : Nat) : List Ty → Bool
  | []      => true
  | t :: ts => Ty.wellKindedB ke pc t && TyList.wellKindedB ke pc ts
end


/-! ### 2. Reflection: the checker agrees with `Ty.WellKinded`. -/

/-- The list checker succeeds iff each element passes the `Bool` checker. Pure
    list induction (mirrors `Core`'s `TyList.isClosed_iff_forall`). -/
theorem TyList.wellKindedB_iff_forall {ke : KindEnv} {pc : Nat} (tys : List Ty) :
    TyList.wellKindedB ke pc tys = true ↔ ∀ t ∈ tys, Ty.wellKindedB ke pc t = true := by
  induction tys with
  | nil => simp [TyList.wellKindedB]
  | cons hd tl ih =>
    simp only [TyList.wellKindedB, Bool.and_eq_true, List.mem_cons]
    rw [ih]
    constructor
    · rintro ⟨hhd, htl⟩ t (rfl | ht)
      · exact hhd
      · exact htl t ht
    · intro h
      exact ⟨h hd (Or.inl rfl), fun t ht => h t (Or.inr ht)⟩

/-- **Reflection for a single type**: the `Bool` checker agrees with the
    `Ty.WellKinded` spec. Structural induction via `Core`'s `Ty.rec_strong`,
    whose `customTy` IH ranges over the argument list. -/
theorem Ty.wellKindedB_iff {ke : KindEnv} {pc : Nat} (ty : Ty) :
    Ty.wellKindedB ke pc ty = true ↔ Ty.WellKinded ke pc ty := by
  induction ty using Ty.rec_strong with
  | prim p => exact iff_of_true rfl .prim
  | bvar i =>
    simp only [Ty.wellKindedB, decide_eq_true_eq]
    constructor
    · intro h; exact .bvar h
    · intro h; cases h with | bvar hlt => exact hlt
  | fvar n =>
    refine iff_of_false (by simp [Ty.wellKindedB]) ?_
    intro h; cases h
  | arrow a b iha ihb =>
    simp only [Ty.wellKindedB, Bool.and_eq_true]
    rw [iha, ihb]
    constructor
    · rintro ⟨ha, hb⟩; exact .arrow ha hb
    · intro h; cases h with | arrow ha hb => exact ⟨ha, hb⟩
  | customTy T args ih =>
    simp only [Ty.wellKindedB, Bool.and_eq_true, decide_eq_true_eq]
    rw [TyList.wellKindedB_iff_forall]
    constructor
    · rintro ⟨harity, hargs⟩
      exact .customTy harity (fun t ht => (ih t ht).mp (hargs t ht))
    · intro h
      cases h with
      | customTy harity hargs =>
        exact ⟨harity, fun t ht => (ih t ht).mpr (hargs t ht)⟩

/-- **Reflection for a list of types**, phrased directly against the spec (the
    form the elaborator consumes). -/
theorem TyList.wellKindedB_iff {ke : KindEnv} {pc : Nat} (tys : List Ty) :
    TyList.wellKindedB ke pc tys = true ↔ ∀ t ∈ tys, Ty.WellKinded ke pc t := by
  rw [TyList.wellKindedB_iff_forall]
  constructor
  · intro h t ht; exact (Ty.wellKindedB_iff t).mp (h t ht)
  · intro h t ht; exact (Ty.wellKindedB_iff t).mpr (h t ht)

/-- The spec is decidable, via the checker. -/
instance (ke : KindEnv) (pc : Nat) (ty : Ty) : Decidable (Ty.WellKinded ke pc ty) :=
  decidable_of_iff _ (Ty.wellKindedB_iff ty)


/-! ### 3. `WellKinded` discharges a `Ctor`'s `bound`/`closed` obligations. -/

/-- A well-kinded type only references params in range (`Ctor.bound`). -/
theorem Ty.WellKinded.toContainsBvars {ke : KindEnv} {pc : Nat} {ty : Ty}
    (h : Ty.WellKinded ke pc ty) : ContainsBvarsUpTo pc ty := by
  induction h with
  | prim => exact .prim
  | bvar hlt => exact .bvar hlt
  | arrow _ _ iha ihb => exact .arrow iha ihb
  | customTy _ _ ih => exact .customTy ih

/-- A well-kinded type has no free type vars (`Ctor.closed`). -/
theorem Ty.WellKinded.toNoFreeVars {ke : KindEnv} {pc : Nat} {ty : Ty}
    (h : Ty.WellKinded ke pc ty) : NoFreeVars ty := by
  induction h with
  | prim => exact .prim
  | bvar _ => exact .bvar
  | arrow _ _ iha ihb => exact .arrow iha ihb
  | customTy _ _ ih => exact .customTy ih


/-! ### 4. Building one `Ctor` from a constructor's checked field list. -/

/-- Build a `Ctor` for the type `tn` (arity `pc`) from `fields`, discharging the
    `bound`/`closed` obligations from a successful kind-check. `none` if the
    fields don't kind-check. -/
/-- Native declaration validation failures, before source lookup or wording. -/
inductive DeclError where
  | duplicateTypes (names : List TyName)
  | duplicateConstructors (names : List CtorName)
  | invalidFields (parent : TyName) (paramCount : Nat) (fields : List Ty)
  | inConstructor (name : CtorName) (error : DeclError)
  deriving Repr

def mkCtorFromFieldsResult (ke : KindEnv) (pc : Nat) (tn : TyName) (fields : List Ty) : Except DeclError Ctor :=
  if h : TyList.wellKindedB ke pc fields = true then
    .ok { paramCount := pc, tyName := tn, contents := fields,
           bound  := fun ty hty => ((TyList.wellKindedB_iff fields).mp h ty hty).toContainsBvars,
           closed := fun ty hty => ((TyList.wellKindedB_iff fields).mp h ty hty).toNoFreeVars }
  else .error (.invalidFields tn pc (fields.filter fun ty => !Ty.wellKindedB ke pc ty))

def mkCtorFromFields (ke : KindEnv) (pc : Nat) (tn : TyName) (fields : List Ty) : Option Ctor :=
  (mkCtorFromFieldsResult ke pc tn fields).toOption

@[typed_result_projection] theorem mkCtorFromFieldsResult_toOption
    (ke : KindEnv) (pc : Nat) (tn : TyName) (fields : List Ty) :
    (mkCtorFromFieldsResult ke pc tn fields).toOption = mkCtorFromFields ke pc tn fields := rfl

theorem mkCtorFromFields_eq (ke : KindEnv) (pc : Nat) (tn : TyName) (fields : List Ty) : mkCtorFromFields ke pc tn fields =
  if h : TyList.wellKindedB ke pc fields = true then
    some { paramCount := pc, tyName := tn, contents := fields,
           bound  := fun ty hty => ((TyList.wellKindedB_iff fields).mp h ty hty).toContainsBvars,
           closed := fun ty hty => ((TyList.wellKindedB_iff fields).mp h ty hty).toNoFreeVars }
  else none := by
  unfold mkCtorFromFields mkCtorFromFieldsResult
  split <;> rfl

/-- A successful `mkCtorFromFields` implies its fields kind-checked. -/
theorem mkCtorFromFields_wellKinded {ke : KindEnv} {pc : Nat} {tn : TyName}
    {fields : List Ty} {ct : Ctor} (h : mkCtorFromFields ke pc tn fields = some ct) :
    TyList.wellKindedB ke pc fields = true := by
  rw [mkCtorFromFields_eq] at h
  split at h
  · assumption
  · exact absurd h (by simp)

theorem mkCtorFromFields_signature {ke : KindEnv} {pc : Nat} {tn : TyName}
    {fields : List Ty} {ctor : Ctor} (h : mkCtorFromFields ke pc tn fields = some ctor) :
    ctor.signature = (pc, tn, fields) := by
  rw [mkCtorFromFields_eq] at h
  split at h
  · cases h; rfl
  · cases h


/-! ### 5. The two-pass elaborator into a `CtorEnv`. -/

/-- A successful `Option` bind forces its scrutinee to have succeeded. -/
theorem option_bind_eq_some_left {α β : Type} {o : Option α} {f : α → Option β}
    {b : β} (h : (o >>= f) = some b) : ∃ a, o = some a := by
  cases o with
  | none => simp at h
  | some a => exact ⟨a, rfl⟩

/-- Generic inversion: if a `List.mapM` in the `Option` monad succeeds, then each
    input element mapped to `some`. Used to invert `elabDecls`' nested `mapM`s. -/
theorem mapM_option_mem {α β : Type} {g : α → Option β} :
    ∀ {l : List α} {r : List β}, l.mapM g = some r → ∀ x ∈ l, ∃ y, g x = some y := by
  intro l
  induction l with
  | nil => intro r _ x hx; simp at hx
  | cons a as ih =>
    intro r h x hx
    rw [List.mapM_cons] at h
    cases hga : g a with
    | none => rw [hga] at h; simp at h
    | some b =>
      cases hmas : List.mapM g as with
      | none => rw [hga, hmas] at h; simp at h
      | some bs =>
        rcases List.mem_cons.mp hx with rfl | hx'
        · exact ⟨b, hga⟩
        · exact ih hmas x hx'

/-- Inversion of a single `guard` in the `Option` monad: success forces the
    predicate and reduces the continuation. -/
theorem option_guard_bind {P : Prop} [Decidable P] {β : Type} {k : Unit → Option β}
    {b : β} (h : (guard P >>= k) = some b) : P ∧ k () = some b := by
  by_cases hP : P
  · exact ⟨hP, by simpa [guard, hP] using h⟩
  · simp [guard, hP] at h

/-- **Elaborate a declaration group into a `CtorEnv`.** Two passes: build the
    `KindEnv` (names + arities), then — after checking type/constructor names are
    distinct — kind-check every constructor's fields and emit one `Ctor` each.
    `none` on any violation. -/
def elabDeclsResult (decls : List DataDecl) : Except DeclError CtorEnv := do
  let ke := DataDecls.kindEnv decls
  let types := decls.map (·.name)
  TypedResult.ensure (.duplicateTypes (types.filter (fun name => 1 < types.count name)).dedup) types.Nodup
  let constructors := decls.flatMap (fun d => d.ctors.map Prod.fst)
  TypedResult.ensure
    (.duplicateConstructors (constructors.filter (fun name => 1 < constructors.count name)).dedup)
    constructors.Nodup
  let nested ← decls.mapM fun d =>
    d.ctors.mapM fun c => do
      let ctor ← (mkCtorFromFieldsResult ke d.paramCount d.name c.2).mapError (.inConstructor c.1)
      pure (c.1, ctor)
  pure nested.flatten

def elabDecls (decls : List DataDecl) : Option CtorEnv := (elabDeclsResult decls).toOption

@[typed_result_projection] theorem elabDeclsResult_toOption (decls : List DataDecl) :
    (elabDeclsResult decls).toOption = elabDecls decls := rfl

theorem elabDecls_eq (decls : List DataDecl) : elabDecls decls = (show Option CtorEnv from
 do
  let ke := DataDecls.kindEnv decls
  guard ((decls.map (·.name)).Nodup)
  guard ((decls.flatMap (fun d => d.ctors.map Prod.fst)).Nodup)
  let nested ← decls.mapM (fun d =>
    d.ctors.mapM (fun c => (mkCtorFromFields ke d.paramCount d.name c.2).map (fun ct => (c.1, ct))))
  pure nested.flatten) := by
  unfold elabDecls elabDeclsResult
  simp only [TypedResult.toOption_bind, TypedResult.toOption_ensure, TypedResult.toOption_mapM,
    TypedResult.toOption_mapError, mkCtorFromFieldsResult_toOption, TypedResult.toOption_pure]
  rfl

/-! ### 6. Soundness: a produced env came from a well-formed declaration group. -/

/-- **Soundness of the elaborator.** If `elabDecls` succeeds, the input group is
    well-formed (`DataDecls.WF`): the two `guard`s give the `Nodup` conditions,
    and each constructor's successful `mkCtorFromFields` gives its fields'
    well-kindedness via `TyList.wellKindedB_iff`. -/
theorem elabDecls_wellFormed {decls : List DataDecl} {env : CtorEnv}
    (h : elabDecls decls = some env) : DataDecls.WF decls := by
  rw [elabDecls_eq] at h
  simp only [] at h
  obtain ⟨hP1, h⟩ := option_guard_bind h
  obtain ⟨hP2, h⟩ := option_guard_bind h
  obtain ⟨nested, hmapM⟩ := option_bind_eq_some_left h
  refine ⟨?_, hP1, hP2⟩
  intro d hd c hc ty hty
  obtain ⟨inner, hinner⟩ := mapM_option_mem hmapM d hd
  obtain ⟨pair, hpair⟩ := mapM_option_mem hinner c hc
  obtain ⟨ct, hct, _⟩ := Option.map_eq_some_iff.mp hpair
  exact (TyList.wellKindedB_iff c.2).mp (mkCtorFromFields_wellKinded hct) ty hty


private theorem mapM_option_projection {f : α → Option β} {project : β → γ}
    {expected : α → γ} {xs : List α} {ys : List β}
    (h : xs.mapM f = some ys)
    (hf : ∀ x y, f x = some y → project y = expected x) :
    ys.map project = xs.map expected := by
  induction xs generalizing ys with
  | nil => simp only [List.mapM_nil, pure, Option.some.injEq] at h; subst ys; rfl
  | cons x xs ih =>
    rw [List.mapM_cons] at h
    cases hx : f x with
    | none => simp [hx] at h
    | some y =>
      cases ht : xs.mapM f with
      | none => simp [hx, ht] at h
      | some rest =>
        simp [hx, ht] at h
        subst ys
        simp only [List.map_cons, hf x y hx, ih ht]

/-- Successful elaboration relates the actual returned environment to the
written declarations, including constructor names, arities, parents and fields. -/
theorem elabDecls_sound {decls : List DataDecl} {env : CtorEnv}
    (h : elabDecls decls = some env) : DataDecls.ElaboratesTo decls env := by
  refine ⟨elabDecls_wellFormed h, ?_⟩
  rw [elabDecls_eq] at h
  simp only [] at h
  obtain ⟨_, h⟩ := option_guard_bind h
  obtain ⟨_, h⟩ := option_guard_bind h
  obtain ⟨nested, hmap, hreturn⟩ := Option.bind_eq_some_iff.mp h
  simp only [pure, Option.some.injEq] at hreturn
  subst env
  have hsignatures : nested.map CtorEnv.signatures =
      decls.map (fun decl => decl.ctors.map fun ctor =>
        (ctor.1, (decl.paramCount, decl.name, ctor.2))) := by
    apply mapM_option_projection hmap
    intro decl entries hentries
    apply mapM_option_projection hentries
    intro ctor entry hentry
    obtain ⟨core, hc, rfl⟩ := Option.map_eq_some_iff.mp hentry
    exact congrArg (fun signature => (ctor.1, signature)) (mkCtorFromFields_signature hc)
  simpa only [CtorEnv.signatures, DataDecls.constructorSignatures, List.map_flatten]
    using congrArg List.flatten hsignatures

/-! ### 6b. Completeness: a well-formed declaration group elaborates. -/

/-- Converse of `mapM_option_mem`: if every element maps to `some`, then a
    `List.mapM` in the `Option` monad succeeds. Pure list induction. -/
theorem mapM_option_isSome {α β : Type} {g : α → Option β} :
    ∀ {l : List α}, (∀ x ∈ l, (g x).isSome) → (l.mapM g).isSome := by
  intro l
  induction l with
  | nil => intro _; rfl
  | cons a as ih =>
    intro h
    rw [List.mapM_cons]
    obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp (h a (List.mem_cons_self))
    obtain ⟨bs, hbs⟩ :=
      Option.isSome_iff_exists.mp (ih (fun x hx => h x (List.mem_cons_of_mem a hx)))
    rw [hb, hbs]
    rfl

/-- A successful kind-check makes `mkCtorFromFields` succeed (converse of
    `mkCtorFromFields_wellKinded`): the `if h : … = true` takes the `then`
    branch. -/
theorem mkCtorFromFields_isSome {ke : KindEnv} {pc : Nat} {tn : TyName}
    {fields : List Ty} (h : TyList.wellKindedB ke pc fields = true) :
    (mkCtorFromFields ke pc tn fields).isSome := by
  rw [mkCtorFromFields_eq]
  rw [dif_pos h]
  rfl

/-- Forward inversion of a single `guard` in the `Option` monad: if the
    predicate holds, the `guard` vanishes into its continuation. -/
theorem option_guard_bind_pos {P : Prop} [Decidable P] {β : Type} {k : Unit → Option β}
    (hP : P) : (guard P >>= k) = k () := by
  simp [guard, hP]

/-- **Completeness of the elaborator.** A well-formed declaration group
    (`DataDecls.WF`) elaborates successfully: the two `guard`s pass from the
    `Nodup` fields, and every constructor's fields kind-check (from `h.fields`
    via `TyList.wellKindedB_iff`), so both the inner and outer `mapM`s succeed. -/
theorem elabDecls_complete {decls : List DataDecl} (h : DataDecls.WF decls) :
    (elabDecls decls).isSome := by
  rw [elabDecls_eq]
  simp only []
  rw [option_guard_bind_pos h.tyNamesNodup, option_guard_bind_pos h.ctorNamesNodup]
  have hOuter :
      (decls.mapM (fun (d : DataDecl) =>
        d.ctors.mapM (fun c =>
          (mkCtorFromFields (DataDecls.kindEnv decls) d.paramCount d.name c.2).map
            (fun ct => (c.1, ct))))).isSome := by
    apply mapM_option_isSome
    intro d hd
    apply mapM_option_isSome
    intro c hc
    have hwk : TyList.wellKindedB (DataDecls.kindEnv decls) d.paramCount c.2 = true :=
      (TyList.wellKindedB_iff c.2).mpr (h.fields d hd c hc)
    obtain ⟨ct, hct⟩ := Option.isSome_iff_exists.mp (mkCtorFromFields_isSome hwk)
    rw [hct]
    rfl
  obtain ⟨nested, hnested⟩ := Option.isSome_iff_exists.mp hOuter
  rw [hnested]
  rfl


/-- The elaborator's complete result graph is exactly the declarative contract. -/
theorem elabDecls_eq_some_iff {decls : List DataDecl} {env : CtorEnv} :
    elabDecls decls = some env ↔ DataDecls.ElaboratesTo decls env := by
  constructor
  · exact elabDecls_sound
  · intro h
    obtain ⟨actual, ha⟩ := Option.isSome_iff_exists.mp (elabDecls_complete h.wellFormed)
    exact (elabDecls_sound ha).unique h ▸ ha


/-! ### 7. A fixed prelude, elaborated through the checker. -/

/-- A small prelude: `Bool` (nullary), the recursive unary `List`, and the
    binary `Pair` (the tuple type — needed by the surface bridge's `(a, b)`
    sugar; its single ctor `Pair` has two fields `.bvar 0`/`.bvar 1`). -/
def preludeDecls : List DataDecl :=
  [ { name := ⟨"Bool"⟩, paramCount := 0, ctors := [(⟨"True"⟩, []), (⟨"False"⟩, [])] },
    { name := ⟨"List"⟩, paramCount := 1,
      ctors := [(⟨"Nil"⟩, []), (⟨"Cons"⟩, [.bvar 0, .customTy ⟨"List"⟩ [.bvar 0]])] },
    { name := ⟨"Pair"⟩, paramCount := 2, ctors := [(⟨"Pair"⟩, [.bvar 0, .bvar 1])] } ]

-- The prelude elaborates successfully (witnessing the whole pipeline).
#guard (elabDecls preludeDecls).isSome
#guard (elabDecls preludeDecls).isSome = true
