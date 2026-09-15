import FHM.Bounds.FreeAlgebra
import FHM.Bounds.CountTransport

/-!
# Declaration-indexed nominal match branches

Generic ADT matching must use the same `CtorEnv` that lowered and typed the
program.  This module is deliberately independent of the walkers: it computes
field bounds from declared constructor contents, validates constructor
ownership/arity, and defines finite coverage over the declaration environment.
-/

namespace FHM.Bounds.NominalBranches

open TypeSubstitution

mutual
/-- Read constructor fields at their honest HM-shape ceiling.  Nominal matching
    does not invent a value-origin interval for a stored field: a carried `BL`
    therefore becomes `[0,∞]`, while ordinary nominal applications retain only
    their structural arguments. Actual scrutinee type arguments are substituted
    afterwards, retaining any bounds they already carry. -/
def template : Ty → BoundsTy
  | .prim p => .prim p
  | .fvar i => .fvar i
  | .bvar i => .bvar i
  | .arrow a b => .arrow (template a) (template b)
  | .customTy name args => .custom name (templates args)
  | .bl _ _ elem => .list (.lit 0) .inf (template elem)
termination_by ty => sizeOf ty
decreasing_by all_goals simp_all <;> omega

def templates : List Ty → List BoundsTy
  | [] => []
  | ty :: rest => template ty :: templates rest
termination_by types => sizeOf types
decreasing_by all_goals simp_all <;> omega
end

mutual
theorem template_shape (ty : Ty) : Synth.BoundsTy.toTy (template ty) = ty.eraseBounds := by
  cases ty with
  | prim | fvar | bvar => simp [template, Synth.BoundsTy.toTy, Ty.eraseBounds]
  | arrow a b => simp only [template, Synth.BoundsTy.toTy, Ty.eraseBounds,
      template_shape a, template_shape b]
  | customTy name args =>
      simp only [template, Synth.BoundsTy.toTy, Ty.eraseBounds]
      change Ty.customTy name ((templates args).map Synth.BoundsTy.toTy) =
        Ty.customTy name (TyList.eraseBounds args)
      rw [templates_shape args]
  | bl lo hi elem =>
      simp [template, Synth.BoundsTy.toTy, Ty.eraseBounds, listTy, bareListTy,
        FHM.Bounds.listTyName, _root_.listTyName, template_shape elem]
termination_by sizeOf ty

theorem templates_shape (types : List Ty) :
    (templates types).map Synth.BoundsTy.toTy = TyList.eraseBounds types := by
  cases types with
  | nil => simp [templates, TyList.eraseBounds]
  | cons ty rest =>
      simp only [templates, List.map_cons, TyList.eraseBounds]
      change Synth.BoundsTy.toTy (template ty) ::
          (templates rest).map Synth.BoundsTy.toTy =
        ty.eraseBounds :: TyList.eraseBounds rest
      rw [template_shape ty, templates_shape rest]
termination_by sizeOf types
end

/-- Bounds on constructor fields after substituting the scrutinee's actual type
    arguments for the declaration's bound type parameters. -/
def instantiatedFields (ctor : Ctor) (args : List BoundsTy) : List BoundsTy :=
  substituteList (SchemeUse.vector args) (templates ctor.contents)

private theorem templates_length (types : List Ty) :
    (templates types).length = types.length := by
  induction types <;> simp [templates, *]

private theorem substituteList_length (subst : Nat → BoundsTy) (types : List BoundsTy) :
    (substituteList subst types).length = types.length := by
  induction types <;> simp [TypeSubstitution.substituteList, *]

theorem instantiatedFields_length (ctor : Ctor) (args : List BoundsTy) :
    (instantiatedFields ctor args).length = ctor.contents.length := by
  simp [instantiatedFields, substituteList_length, templates_length]

private theorem substituteTemplates_shape (args : List BoundsTy) (types : List Ty) :
    (substituteList (SchemeUse.vector args) (templates types)).map
        Synth.BoundsTy.toTy =
      TyList.instantiate (fun i => Synth.BoundsTy.toTy (SchemeUse.vector args i))
        (TyList.eraseBounds types) := by
  induction types with
  | nil => simp [templates, TypeSubstitution.substituteList, TyList.eraseBounds,
      TyList.instantiate]
  | cons field rest ih =>
      simp only [templates, TypeSubstitution.substituteList, List.map_cons,
        TyList.instantiate, TyList.eraseBounds, TypeSubstitution.shape,
        template_shape, ih]

theorem instantiatedFields_shape (ctor : Ctor) (args : List BoundsTy) :
    (instantiatedFields ctor args).map Synth.BoundsTy.toTy =
      TyList.instantiate (fun i => Synth.BoundsTy.toTy (SchemeUse.vector args i))
        (TyList.eraseBounds ctor.contents) := by
  simpa [instantiatedFields] using
    substituteTemplates_shape args ctor.contents

private theorem templates_bound {n : Nat} {types : List Ty}
    (bound : ∀ ty ∈ types, ContainsBvarsUpTo n ty) :
    ∀ ty ∈ (templates types).map Synth.BoundsTy.toTy, ContainsBvarsUpTo n ty := by
  rw [templates_shape, TyList.eraseBounds_eq_map]
  intro erased member
  obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp member
  exact (bound original originalMember).eraseBounds

mutual
private theorem template_free_fixed (f : Nat → BoundsTy) {ty : Ty}
    (closed : NoFreeVars ty) : SchemeSpecialization.mapFree f (template ty) = template ty := by
  cases closed with
  | prim | bvar => simp [template, SchemeSpecialization.mapFree]
  | arrow ha hb => simp only [template, SchemeSpecialization.mapFree,
      template_free_fixed f ha, template_free_fixed f hb]
  | customTy hall =>
      simp only [template, SchemeSpecialization.mapFree]
      exact congrArg (BoundsTy.custom _) (templates_free_fixed f hall)
  | bl he =>
      simp only [template, SchemeSpecialization.mapFree]
      exact congrArg (BoundsTy.list (.lit 0) .inf) (template_free_fixed f he)
termination_by sizeOf ty

private theorem templates_free_fixed (f : Nat → BoundsTy) {types : List Ty}
    (closed : ∀ ty ∈ types, NoFreeVars ty) :
    SchemeSpecialization.mapFreeList f (templates types) = templates types := by
  cases types with
  | nil => simp [templates, SchemeSpecialization.mapFreeList]
  | cons ty rest =>
      simp only [templates, SchemeSpecialization.mapFreeList]
      exact congrArg₂ List.cons (template_free_fixed f (closed ty (by simp)))
        (templates_free_fixed f (fun field member => closed field (List.mem_cons_of_mem _ member)))
termination_by sizeOf types
end

private theorem mapFree_vector (f : Nat → BoundsTy) (args : List BoundsTy) (i : Nat) :
    SchemeUse.vector (SchemeSpecialization.mapFreeList f args) i =
      SchemeSpecialization.mapFree f (SchemeUse.vector args i) := by
  have mapped : SchemeSpecialization.mapFreeList f args =
      args.map (SchemeSpecialization.mapFree f) := by
    induction args with
    | nil => rfl
    | cons arg rest ih => simp [SchemeSpecialization.mapFreeList, ih]
  rw [mapped]
  cases harg : args[i]? <;>
    simp [SchemeUse.vector, List.getElem?_map, harg, SchemeSpecialization.mapFree]

private theorem substitute_mapFreeList (f : Nat → BoundsTy)
    (hf : ∀ i, (Synth.BoundsTy.toTy (f i)).IsLC)
    (args : Nat → BoundsTy) (types : List BoundsTy) :
    SchemeSpecialization.mapFreeList f (substituteList args types) =
      substituteList (fun i => SchemeSpecialization.mapFree f (args i))
        (SchemeSpecialization.mapFreeList f types) := by
  induction types with
  | nil => rfl
  | cons ty rest ih =>
      simp only [TypeSubstitution.substituteList, SchemeSpecialization.mapFreeList,
        FreeAlgebra.instantiate_commute f hf args ty, ih]

theorem instantiatedFields_types (ctor : Ctor) (args : List BoundsTy)
    (f : Nat → BoundsTy) (hf : ∀ i, (Synth.BoundsTy.toTy (f i)).IsLC) :
    SchemeSpecialization.mapFreeList f (instantiatedFields ctor args) =
      instantiatedFields ctor (SchemeSpecialization.mapFreeList f args) := by
  rw [instantiatedFields, instantiatedFields, substitute_mapFreeList f hf]
  rw [templates_free_fixed f ctor.closed]
  apply FreeAlgebra.list_instantiate_congr (n := ctor.paramCount)
    (as := templates ctor.contents) (templates_bound ctor.bound)
  intro i inside
  exact (mapFree_vector f args i).symm

private theorem bounds_vector (rows : CountSubstitution.Bindings)
    (args : List BoundsTy) (i : Nat) :
    SchemeUse.vector (CountSubstitution.boundsList rows args) i =
      CountSubstitution.bounds rows (SchemeUse.vector args i) := by
  have mapped : CountSubstitution.boundsList rows args =
      args.map (CountSubstitution.bounds rows) := by
    induction args with
    | nil => rfl
    | cons arg rest ih => simp [CountSubstitution.boundsList, ih]
  rw [mapped]
  exact CountTransport.vector_mapped rows args i

mutual
private theorem template_counts_fixed (rows : CountSubstitution.Bindings) (ty : Ty) :
    CountSubstitution.bounds rows (template ty) = template ty := by
  cases ty with
  | prim | fvar | bvar => simp [template, CountSubstitution.bounds]
  | arrow a b => simp only [template, CountSubstitution.bounds,
      template_counts_fixed rows a, template_counts_fixed rows b]
  | customTy name args =>
      simp only [template, CountSubstitution.bounds, templates_counts_fixed rows args]
  | bl lo hi elem =>
      simp only [template, CountSubstitution.bounds, CountSubstitution.count,
        template_counts_fixed rows elem]
termination_by sizeOf ty

private theorem templates_counts_fixed (rows : CountSubstitution.Bindings) (types : List Ty) :
    CountSubstitution.boundsList rows (templates types) = templates types := by
  cases types with
  | nil => simp [templates, CountSubstitution.boundsList]
  | cons ty rest => simp only [templates, CountSubstitution.boundsList,
      template_counts_fixed rows ty, templates_counts_fixed rows rest]
termination_by sizeOf types
end

private theorem substitute_boundsList (rows : CountSubstitution.Bindings)
    (args : Nat → BoundsTy) (types : List BoundsTy) :
    CountSubstitution.boundsList rows (substituteList args types) =
      substituteList (fun i => CountSubstitution.bounds rows (args i))
        (CountSubstitution.boundsList rows types) := by
  induction types with
  | nil => rfl
  | cons ty rest ih =>
      simp only [TypeSubstitution.substituteList, CountSubstitution.boundsList,
        CountTransport.instantiate_commute rows args ty, ih]

theorem instantiatedFields_counts (ctor : Ctor) (args : List BoundsTy)
    (rows : CountSubstitution.Bindings) :
    CountSubstitution.boundsList rows (instantiatedFields ctor args) =
      instantiatedFields ctor (CountSubstitution.boundsList rows args) := by
  rw [instantiatedFields, instantiatedFields, substitute_boundsList]
  rw [templates_counts_fixed]
  apply FreeAlgebra.list_instantiate_congr (n := ctor.paramCount)
    (as := templates ctor.contents) (templates_bound ctor.bound)
  intro i inside
  exact (bounds_vector rows args i).symm

/-- Executable pattern validation and its exact branch environment prefix.
    Wildcards bind nothing; named patterns must belong to the scrutinee ADT and
    bind precisely the declared number of fields. -/
def fields? (ctors : CtorEnv) (typeName : TyName) (args : List BoundsTy) :
    MatchPattern → Option (List BoundsTy)
  | .wildcard => some []
  | .named name arity => do
      let ctor ← LookupList.get? ctors name
      if ctor.tyName = typeName && ctor.paramCount = args.length &&
          arity = ctor.contents.length then
        some (instantiatedFields ctor args)
      else none

def PatternFields (ctors : CtorEnv) (typeName : TyName) (args : List BoundsTy)
    (pattern : MatchPattern) (fields : List BoundsTy) : Prop :=
  fields? ctors typeName args pattern = some fields

private theorem mapFreeList_length (f : Nat → BoundsTy) (args : List BoundsTy) :
    (SchemeSpecialization.mapFreeList f args).length = args.length := by
  induction args <;> simp [SchemeSpecialization.mapFreeList, *]

private theorem boundsList_length (rows : CountSubstitution.Bindings) (args : List BoundsTy) :
    (CountSubstitution.boundsList rows args).length = args.length := by
  induction args <;> simp [CountSubstitution.boundsList, *]

private theorem fields?_types (ctors : CtorEnv) (typeName : TyName)
    (args : List BoundsTy) (pattern : MatchPattern) (f : Nat → BoundsTy)
    (hf : ∀ i, (Synth.BoundsTy.toTy (f i)).IsLC) :
    fields? ctors typeName (SchemeSpecialization.mapFreeList f args) pattern =
      (fields? ctors typeName args pattern).map (SchemeSpecialization.mapFreeList f) := by
  cases pattern with
  | wildcard => rfl
  | named name arity =>
      cases lookup : LookupList.get? ctors name with
      | none => simp [fields?, lookup]
      | some ctor =>
          simp [fields?, lookup, mapFreeList_length,
            instantiatedFields_types ctor args f hf]

theorem PatternFields.types {ctors typeName args pattern fields}
    (h : PatternFields ctors typeName args pattern fields)
    (f : Nat → BoundsTy) (hf : ∀ i, (Synth.BoundsTy.toTy (f i)).IsLC) :
    PatternFields ctors typeName (SchemeSpecialization.mapFreeList f args) pattern
      (SchemeSpecialization.mapFreeList f fields) := by
  unfold PatternFields
  rw [fields?_types ctors typeName args pattern f hf, h]
  rfl

private theorem fields?_counts (ctors : CtorEnv) (typeName : TyName)
    (args : List BoundsTy) (pattern : MatchPattern) (rows : CountSubstitution.Bindings) :
    fields? ctors typeName (CountSubstitution.boundsList rows args) pattern =
      (fields? ctors typeName args pattern).map (CountSubstitution.boundsList rows) := by
  cases pattern with
  | wildcard => rfl
  | named name arity =>
      cases lookup : LookupList.get? ctors name with
      | none => simp [fields?, lookup]
      | some ctor =>
          simp [fields?, lookup, boundsList_length,
            instantiatedFields_counts ctor args rows]

theorem PatternFields.counts {ctors typeName args pattern fields}
    (h : PatternFields ctors typeName args pattern fields)
    (rows : CountSubstitution.Bindings) :
    PatternFields ctors typeName (CountSubstitution.boundsList rows args) pattern
      (CountSubstitution.boundsList rows fields) := by
  unfold PatternFields
  rw [fields?_counts ctors typeName args pattern rows, h]
  rfl

theorem PatternFields.length {ctors typeName args pattern fields}
    (h : PatternFields ctors typeName args pattern fields) :
    fields.length = pattern.bindCount := by
  cases pattern with
  | wildcard =>
      change some [] = some fields at h
      injection h with same
      subst fields
      rfl
  | named name arity =>
      change (do
        let ctor ← LookupList.get? ctors name
        if ctor.tyName = typeName && ctor.paramCount = args.length &&
            arity = ctor.contents.length then
          some (instantiatedFields ctor args)
        else none) = some fields at h
      cases lookup : LookupList.get? ctors name with
      | none => simp [lookup] at h
      | some ctor =>
          by_cases owner : ctor.tyName = typeName
          · by_cases params : ctor.paramCount = args.length
            · by_cases count : arity = ctor.contents.length
              · simp [lookup, owner, params, count] at h
                subst fields
                simpa [MatchPattern.bindCount, instantiatedFields_length] using count.symm
              · simp [lookup, owner, params, count] at h
            · simp [lookup, owner, params] at h
          · simp [lookup, owner] at h

/-- Wildcard coverage, or one correctly-formed matching branch for every
    constructor owned by the scrutinee's declared type.  Pattern validity is a
    separate premise so constructors from another type cannot hide here. -/
def coversB (ctors : CtorEnv) (typeName : TyName)
    (branches : List (MatchPattern × Expr)) : Bool :=
  hasWildcardBranchB branches || ctors.all fun (name, ctor) =>
    ctor.tyName != typeName || branches.any fun branch =>
      branch.1 == .named name ctor.contents.length

def Covers (ctors : CtorEnv) (typeName : TyName)
    (branches : List (MatchPattern × Expr)) : Prop :=
  coversB ctors typeName branches = true

def checkCoverage (ctors : CtorEnv) (typeName : TyName)
    (branches : List (MatchPattern × Expr)) : Except String (PLift (Covers ctors typeName branches)) :=
  if h : coversB ctors typeName branches = true then pure ⟨h⟩
  else throw "bounds: nominal match is not exhaustive for its declared constructors"

def checkFields (ctors : CtorEnv) (typeName : TyName) (args : List BoundsTy)
    (pattern : MatchPattern) :
    Except String (Σ fields, PLift (PatternFields ctors typeName args pattern fields)) :=
  match h : fields? ctors typeName args pattern with
  | some fields => pure ⟨fields, ⟨h⟩⟩
  | none => throw "bounds: nominal match pattern has the wrong constructor, type, or arity"

theorem Covers.assuming {ctors typeName branches} (h : Covers ctors typeName branches) :
    Covers ctors typeName branches := h

#print axioms checkCoverage
#print axioms checkFields

end FHM.Bounds.NominalBranches
