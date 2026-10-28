import FHM.SurfaceBridge
import FHM.Completeness

/-! # Complete-Core surface lowering compatibility

This opt-in module preserves the original surface-to-complete-Core lowering,
structural surface typing, and runtime-safety theory. Production lowering lives
in `FHM.SurfaceBridge` and targets `InferInput`, retaining partial annotations
for the canonical inference engine. -/

open SmallStep
open PatComp

namespace SurfaceBridge

private def bA : Surface.Binding :=
  { name := .mk "a", ann := none, rhs := .primLit (.int 1) }

/-- Complete Core is an input adapter to the canonical inference engine. -/
def coreTypecheck (ctors : CtorEnv) (core : Expr) : Option PolyTy :=
  typecheck ctors (InferInput.ofCore core)

/-- The artifact and scheme APIs project the same canonical worker run. -/
theorem coreTypecheck_isSome_iff {ctors : CtorEnv} {core : Expr} :
    (coreTypecheck ctors core).isSome ↔
      (inferWithTypes ctors (InferInput.ofCore core)).isSome := by
  simp only [coreTypecheck, typecheck, principalType, Option.isSome_map, inferCore_isSome,
    inferWithTypes]

/-- Canonical inference conserves the original complete-Core typing contract. -/
theorem inferOfCore_source_sound {ctors : CtorEnv} {core : Expr} {result : InferenceResult}
    (h : inferWithTypes ctors (InferInput.ofCore core) = some result) :
    TypeOfHM ⟨[], ctors⟩ core result.ty :=
  ((inferWithTypes_input_sound h).scoped.toCore (InferInput.toCore_ofCore core)).1

/-- Complete Core acceptance is exactly the existing declarative source relation. -/
theorem coreTypecheck_accepts_iff {ctors : CtorEnv} {core : Expr} :
    (coreTypecheck ctors core).isSome ↔ ∃ ty, TypeOfHM ⟨[], ctors⟩ core ty := by
  constructor
  · intro hc
    obtain ⟨result,hr⟩ := Option.isSome_iff_exists.mp (coreTypecheck_isSome_iff.mp hc)
    exact ⟨result.ty,inferOfCore_source_sound hr⟩
  · rintro ⟨ty,ht⟩
    apply coreTypecheck_isSome_iff.mpr
    apply inferWithTypes_complete
    exact (ScopedTyping.ofComplete (InferInput.toCore_ofCore core)
      (fun v hv => ((InferInput.ofCore core).toCore_rigidVars
        (InferInput.toCore_ofCore core) v).mpr hv) ht).source

theorem coreTypecheck_of_infer {ctors : CtorEnv} {core : Expr} {result : InferenceResult}
    (h : inferWithTypes ctors (InferInput.ofCore core) = some result) :
    (coreTypecheck ctors core).isSome :=
  coreTypecheck_isSome_iff.mpr (Option.isSome_iff_exists.mpr ⟨result,h⟩)

/-- Complete Core candidates factor through the same canonical inferred type. -/
theorem inferOfCore_principal {ctors : CtorEnv} {core : Expr} {result : InferenceResult}
    (h : inferWithTypes ctors (InferInput.ofCore core) = some result)
    (ht : TypeOfHM ⟨[], ctors⟩ core target) :
    ∃ R : Subst,(∀ pair ∈ R,pair.2.IsLC) ∧ target = R.onTy result.ty ∧
      ∀ v ∈ core.tyFreeVars,R.onTy (.fvar v) = .fvar v := by
  obtain ⟨R,hR,he,hfix⟩ := inferWithTypes_principal h target
    (ScopedTyping.ofComplete (InferInput.toCore_ofCore core)
      (fun v hv => ((InferInput.ofCore core).toCore_rigidVars
        (InferInput.toCore_ofCore core) v).mpr hv) ht).source
  exact ⟨R,hR,he,fun v hv => hfix v (((InferInput.ofCore core).toCore_rigidVars
    (InferInput.toCore_ofCore core) v).mpr hv)⟩

/-- The adapter executes erasure of the original complete source. -/
theorem inferOfCore_erase {ctors : CtorEnv} {core : Expr} {result : InferenceResult}
    (_h : inferWithTypes ctors (InferInput.ofCore core) = some result) :
    (InferInput.ofCore core).erase = core.erase :=
  ((InferInput.ofCore core).toCore_erase (InferInput.toCore_ofCore core)).symm

private def oneResidualGroup (bindings : List CoreRecBinding) : List (List Nat) :=
  let members := (List.range bindings.length).filter (RecGroups.unsignedAtB bindings)
  if members = [] then [] else [members]

private theorem mem_oneResidualGroupMembers {bindings : List CoreRecBinding} {i : Nat} :
    i ∈ (List.range bindings.length).filter (RecGroups.unsignedAtB bindings) ↔
      i < bindings.length ∧ RecGroups.UnsignedAt bindings i := by
  simp [RecGroups.unsignedAtB_eq_true_iff]

private theorem oneResidualGroup_valid {bindings : List CoreRecBinding} :
    RecGroups.ValidResidualGroups bindings (oneResidualGroup bindings) := by
  let members := (List.range bindings.length).filter (RecGroups.unsignedAtB bindings)
  have hmembers_nodup : members.Nodup := by
    exact List.nodup_range.filter _
  have hmembers_spec (i : Nat) :
      i ∈ members ↔ i < bindings.length ∧ RecGroups.UnsignedAt bindings i := by
    exact mem_oneResidualGroupMembers
  refine {
    nonempty := ?_
    flatten_nodup := ?_
    bounded := ?_
    covers_unsigned := ?_
    dependencies_first := ?_ }
  · intro component hcomponent
    by_cases hm : members = []
    · simp [oneResidualGroup, members, hm] at hcomponent
    · have hc : component = members := by
        simpa [oneResidualGroup, members, hm] using hcomponent
      subst component
      exact hm
  · by_cases hm : members = []
    · simp [oneResidualGroup, members, hm]
    · simpa [oneResidualGroup, members, hm] using hmembers_nodup
  · intro member hmember
    by_cases hm : members = []
    · simp [oneResidualGroup, members, hm] at hmember
    · have hmem : member ∈ members := by
        simpa [oneResidualGroup, members, hm] using hmember
      have hmem := (hmembers_spec member).mp hmem
      omega

  · intro member hbound
    by_cases hm : members = []
    · constructor
      · intro hgroup
        simp [oneResidualGroup, members, hm] at hgroup
      · intro hu
        have hmem : member ∈ members :=
          (hmembers_spec member).mpr ⟨by omega, hu⟩
        simp [hm] at hmem
    · simp [oneResidualGroup, members, hm]
      constructor
      · intro hgroup
        exact (RecGroups.unsignedAtB_eq_true_iff bindings member).mp hgroup.2
      · intro hu
        exact ⟨by omega, (RecGroups.unsignedAtB_eq_true_iff bindings member).mpr hu⟩
  · intro stage dependencyStage component dependencyComponent source target binding
      hcomponent hdependencyComponent hsource htarget hbinding href
    by_cases hm : members = []
    · simp [oneResidualGroup, members, hm] at hcomponent
    · have hs : stage = 0 := by
        simpa [oneResidualGroup, members, hm] using congrArg Option.isSome hcomponent
      have hd : dependencyStage = 0 := by
        simpa [oneResidualGroup, members, hm] using congrArg Option.isSome hdependencyComponent
      omega

private theorem stageEntries_none_eq_rhsEntries (specs : List RecSpec)
    (G Xs : List Nat) :
    specs.mapIdx (RecSpec.stageEntry [] G Xs) =
      specs.map (RecSpec.rhsEntry G Xs) := by
  apply List.ext_getElem
  · simp
  · intro i hi₁ hi₂
    have hi : i < specs.length := by simpa using hi₂
    generalize hs : specs[i]'hi = spec
    cases spec <;> simp_all [RecSpec.stageEntry, RecSpec.rhsEntry]

/-- Build a Core list value from element expressions: `[x,y] ↦ Cons x (Cons y Nil)`. -/
def mkList : List Expr → Expr
  | []      => .ctor cNil
  | x :: xs => .app (.app (.ctor cCons) x) (mkList xs)

/-- Lower an optional monotype annotation (λ-param): `none` stays `none`; `some τ`
    must kind-check via `lowerTy` (else the whole lowering fails). -/
def lowerAnn (ke : KindEnv) (tvs : List ValName) : Option Surface.Ty → Option (Option Ty)
  | none   => some none
  | some τ => (lowerTy ke tvs τ).map some

def lowerPolyAnnIn (ke : KindEnv) (tvs : List ValName) :
    Option Surface.PolyTy → Option (Option PolyTy)
  | none   => some none
  | some σ => (lowerPolyIn ke tvs σ).map some

def lowerPolyAnn (ke : KindEnv) : Option Surface.PolyTy → Option (Option PolyTy)
  | none   => some none
  | some σ => (lowerPoly ke σ).map some

def lowerAnnListIn (ke : KindEnv) (tvs : List ValName) :
    List (Option Surface.PolyTy) → Option (List (Option PolyTy))
  | []      => some []
  | a :: as =>
    match lowerPolyAnnIn ke tvs a, lowerAnnListIn ke tvs as with
    | some a', some as' => some (a' :: as')
    | _, _              => none

def lowerAnnList (ke : KindEnv) : List (Option Surface.PolyTy) → Option (List (Option PolyTy))
  | []      => some []
  | a :: as =>
    match lowerPolyAnn ke a, lowerAnnList ke as with
    | some a', some as' => some (a' :: as')
    | _, _              => none

@[simp] theorem lowerPolyIn_nil (ke : KindEnv) (σ : Surface.PolyTy) :
    lowerPolyIn ke [] σ = lowerPoly ke σ := by
  simp [lowerPolyIn, lowerPoly]

@[simp] theorem lowerPolyAnnIn_nil (ke : KindEnv) (ann : Option Surface.PolyTy) :
    lowerPolyAnnIn ke [] ann = lowerPolyAnn ke ann := by
  cases ann <;> simp [lowerPolyAnnIn, lowerPolyAnn]

@[simp] theorem lowerAnnListIn_nil (ke : KindEnv) (anns : List (Option Surface.PolyTy)) :
    lowerAnnListIn ke [] anns = lowerAnnList ke anns := by
  induction anns with
  | nil => rfl
  | cons ann anns ih =>
    simp only [lowerAnnListIn, lowerAnnList, lowerPolyAnnIn_nil, ih]
/-- Complete-Core compatibility policy for prenex binding signatures.
Head and annotation quantifiers are merged. Fully annotated head parameters
become leading arrows on the written return type. Incomplete parameter
annotations retain the written annotation, and an omitted return annotation
stays absent. Canonical lowering uses `finalizeInputAnn`, which preserves the
missing pieces as templates for inference. -/
def finalizeAnn (tyParams : List ValName)
    (params : List (ValName × Option Surface.Ty)) (ann : Option Surface.PolyTy) :
    Option Surface.PolyTy :=
  match params, ann with
  | [], _ => mergeTyParams tyParams ann
  | _ :: _, some ⟨foralls, ret⟩ =>
      match paramsToArrows params ret with
      | some body =>
          some { foralls := mergeTyParamNames tyParams foralls, body }
      | none => mergeTyParams tyParams ann
  | _ :: _, none => none

/-- Wrap a Core RHS in λs for surface value-params (outer param = outermost λ).
    Param anns are kind-checked at `tvs` (already including binding tyParams when
    a finalized scheme is present). -/
def wrapCoreParams (ke : KindEnv) (tvs : List ValName) :
    List (ValName × Option Surface.Ty) → Expr → Option Expr
  | [], e => some e
  | (_x, pann) :: rest, e =>
    match wrapCoreParams ke tvs rest e with
    | none => none
    | some e' =>
      match lowerAnn ke tvs pann with
      | none => none
      | some ann' => some (.lambda ann' e')



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

private theorem lowerCoreExprSize_lambda_body (param : Surface.Pattern) (paramAnn : Option Surface.Ty)
    (body : Surface.Expr) :
    lowerExprSize body < lowerExprSize (.lambda param paramAnn body) := by
  simp [lowerExprSize]

private theorem lowerCoreExprSize_letIn_rhs (name : ValName) (tyParams : List ValName)
    (params : List (ValName × Option Surface.Ty)) (ann : Option Surface.PolyTy)
    (rhs body : Surface.Expr) :
    lowerExprSize rhs < lowerExprSize (.letIn name tyParams params ann rhs body) := by
  simp [lowerExprSize]; omega

private theorem lowerCoreExprSize_letIn_body (name : ValName) (tyParams : List ValName)
    (params : List (ValName × Option Surface.Ty)) (ann : Option Surface.PolyTy)
    (rhs body : Surface.Expr) :
    lowerExprSize body < lowerExprSize (.letIn name tyParams params ann rhs body) := by
  simp [lowerExprSize]

private theorem lowerCoreExprSize_letRecIn_body (binds : List Surface.Binding) (body : Surface.Expr) :
    lowerExprSize body < lowerExprSize (.letRecIn binds body) := by
  simp [lowerExprSize]

private theorem lowerCoreRecBindsSize_pos_rhs {binds : List Surface.Binding} {b : Surface.Binding}
    (hb : b ∈ binds) :
    lowerExprSize b.rhs < lowerRecBindsSize binds := by
  induction binds with
  | nil => cases hb
  | cons b' bs ih =>
    cases hb with
    | head => simp [lowerRecBindsSize]; omega
    | tail _ hbIn =>
      simp [lowerRecBindsSize]
      exact Nat.lt_trans (ih hbIn) (by omega)

private theorem lowerCoreExprSize_letRecIn_bind_rhs {binds : List Surface.Binding} {body : Surface.Expr}
    {b : Surface.Binding} (hb : b ∈ binds) :
    lowerExprSize b.rhs < lowerExprSize (.letRecIn binds body) := by
  simp [lowerExprSize]
  exact Nat.lt_trans (lowerCoreRecBindsSize_pos_rhs hb) (by omega)

private theorem lowerCoreExprSize_letRecIn_bind_rhs_get {binds : List Surface.Binding} {body : Surface.Expr}
    {i : Nat} (hi : i < binds.length) :
    lowerExprSize binds[i].rhs < lowerExprSize (.letRecIn binds body) := by
  exact lowerCoreExprSize_letRecIn_bind_rhs (List.getElem_mem hi)

private theorem lowerCoreBranchesSize_pos_branch {brs : List (Surface.Pattern × Surface.Expr)}
    {p : Surface.Pattern} {b : Surface.Expr} (hb : (p, b) ∈ brs) :
    lowerExprSize b < lowerBranchesSize brs := by
  induction brs with
  | nil => cases hb
  | cons pb brs ih =>
    cases hb with
    | head => simp [lowerBranchesSize]; omega
    | tail _ hbIn =>
      simp [lowerBranchesSize]
      exact Nat.lt_trans (ih hbIn) (by omega)

private theorem lowerCoreExprSize_match_branch {scrut : Surface.Expr}
    {brs : List (Surface.Pattern × Surface.Expr)} {p : Surface.Pattern} {b : Surface.Expr}
    (hb : (p, b) ∈ brs) :
    lowerExprSize b < lowerExprSize (.match_ scrut brs) := by
  simp [lowerExprSize]
  exact Nat.lt_trans (lowerCoreBranchesSize_pos_branch hb) (by omega)

private theorem lowerCoreExprSize_pair_left (a b : Surface.Expr) :
    lowerExprSize a < lowerExprSize (.pair a b) := by simp [lowerExprSize]; omega

private theorem lowerCoreExprSize_pair_right (a b : Surface.Expr) :
    lowerExprSize b < lowerExprSize (.pair a b) := by simp [lowerExprSize]

private theorem lowerCoreExprSize_cons_head (head tail : Surface.Expr) :
    lowerExprSize head < lowerExprSize (.cons head tail) := by simp [lowerExprSize]; omega

private theorem lowerCoreExprSize_cons_tail (head tail : Surface.Expr) :
    lowerExprSize tail < lowerExprSize (.cons head tail) := by simp [lowerExprSize]

private theorem lowerCoreExprSize_app_fn (f x : Surface.Expr) :
    lowerExprSize f < lowerExprSize (.app f x) := by simp [lowerExprSize]; omega

private theorem lowerCoreExprSize_app_arg (f x : Surface.Expr) :
    lowerExprSize x < lowerExprSize (.app f x) := by simp [lowerExprSize]

private theorem lowerCoreExprSize_ife_cond (c t f : Surface.Expr) :
    lowerExprSize c < lowerExprSize (.ife c t f) := by simp [lowerExprSize]; omega

private theorem lowerCoreExprSize_ife_thn (c t f : Surface.Expr) :
    lowerExprSize t < lowerExprSize (.ife c t f) := by simp [lowerExprSize]; omega

private theorem lowerCoreExprSize_ife_else (c t f : Surface.Expr) :
    lowerExprSize f < lowerExprSize (.ife c t f) := by simp [lowerExprSize]

private theorem lowerCoreExprSize_match_scrut {scrut : Surface.Expr}
    {brs : List (Surface.Pattern × Surface.Expr)} :
    lowerExprSize scrut < lowerExprSize (.match_ scrut brs) := by simp [lowerExprSize]; omega

private theorem lowerCoreExprSize_match_branches {scrut : Surface.Expr}
    {brs : List (Surface.Pattern × Surface.Expr)} :
    lowerBranchesSize brs < lowerExprSize (.match_ scrut brs) := by simp [lowerExprSize]

private theorem lowerCoreExprListSize_pos_mem {items : List Surface.Expr} {e : Surface.Expr}
    (he : e ∈ items) :
    lowerExprSize e < lowerExprListSize items := by
  induction items with
  | nil => cases he
  | cons x xs ih =>
    cases he with
    | head => simp [lowerExprListSize]; omega
    | tail _ hin =>
      simp [lowerExprListSize]
      exact Nat.lt_trans (ih hin) (by omega)

private theorem lowerCoreExprSize_list_mem {items : List Surface.Expr} {e : Surface.Expr}
    (he : e ∈ items) :
    lowerExprSize e < lowerExprSize (.list items) := by
  simp [lowerExprSize]
  exact Nat.lt_trans (lowerCoreExprListSize_pos_mem he) (by omega)

private theorem lowerCoreExprSize_list {items : List Surface.Expr} :
    lowerExprListSize items < lowerExprSize (.list items) := by
  simp [lowerExprSize]

private theorem lowerCoreBranchesSize_lt_cons {p : Surface.Pattern} {b : Surface.Expr}
    {rest : List (Surface.Pattern × Surface.Expr)} :
    lowerBranchesSize rest < lowerBranchesSize ((p, b) :: rest) := by
  simp [lowerBranchesSize]

private theorem lowerCoreExprListSize_lt_cons {e : Surface.Expr} {es : List Surface.Expr} :
    lowerExprListSize es < lowerExprListSize (e :: es) := by
  simp [lowerExprListSize]

private theorem lowerCoreRecBindsSize_lt_cons {b : Surface.Binding} {rest : List Surface.Binding} :
    lowerRecBindsSize rest < lowerRecBindsSize (b :: rest) := by
  simp [lowerRecBindsSize]


/-- Tyvar scope for lowering a binding RHS — shared by `lowerCoreRecBinds` / `CoreLowersRecBinds`. -/
def bindingLowerTyScope (b : Surface.Binding) (outerTvs : List ValName) : List ValName :=
  letAnnTyPrefix b.tyParams (finalizeAnn b.tyParams b.params b.ann) ++ outerTvs

@[simp] theorem finalizeAnn_none (tyParams : List ValName)
    (params : List (ValName × Option Surface.Ty)) :
    finalizeAnn tyParams params none = none := by
  simp only [finalizeAnn]
  rcases params with _ | _ <;> rfl

theorem finalizeAnn_nil_nil_none : finalizeAnn [] [] none = none := by
  simp [finalizeAnn, mergeTyParams]

theorem finalizeAnn_nil_some (σ : Surface.PolyTy) :
    finalizeAnn [] [] (some σ) = some { foralls := σ.foralls.eraseDups, body := σ.body } := rfl

private theorem mem_eraseDups_go :
    ∀ n, ∀ (l : List ValName), l.length = n → ∀ a, a ∈ l.eraseDups → a ∈ l := by
  intro n
  refine Nat.strongRecOn n (motive := fun n => ∀ (l : List ValName), l.length = n → ∀ a, a ∈ l.eraseDups → a ∈ l) fun n ih => ?_
  intro l hn a hmem
  match l with
  | [] => cases hmem
  | b :: l =>
    simp only [List.length_cons] at hn
    simp only [List.eraseDups_cons, List.mem_cons] at hmem
    cases hmem with
    | inl hab => subst hab; simp
    | inr htl =>
      have hlt : (List.filter (fun x => !x == b) l).length < n := by
        rw [← hn]
        exact Nat.lt_add_one_of_le (List.length_filter_le _ l)
      exact List.mem_cons_of_mem b
        (List.mem_of_mem_filter (ih _ hlt _ rfl _ htl))

private theorem mem_eraseDups {a : ValName} {l : List ValName} (h : a ∈ l.eraseDups) : a ∈ l :=
  mem_eraseDups_go l.length l rfl a h

private theorem mem_eraseDups_of_mem_go :
    ∀ n, ∀ (l : List ValName), l.length = n → ∀ a, a ∈ l → a ∈ l.eraseDups := by
  intro n
  refine Nat.strongRecOn n (motive := fun n => ∀ (l : List ValName), l.length = n → ∀ a, a ∈ l → a ∈ l.eraseDups) fun n ih => ?_
  intro l hn a hmem
  match l with
  | [] => cases hmem
  | b :: l =>
    simp only [List.length_cons] at hn
    cases List.mem_cons.mp hmem with
    | inl hab =>
      simp only [List.eraseDups_cons, List.mem_cons]
      exact Or.inl hab
    | inr ha =>
      simp only [List.eraseDups_cons, List.mem_cons]
      have hlt : (List.filter (fun x => !x == b) l).length < n := by
        rw [← hn]
        exact Nat.lt_add_one_of_le (List.length_filter_le _ l)
      by_cases hab : a = b
      · exact Or.inl hab
      · have ha' : a ∈ List.filter (fun x => !x == b) l := by
          simp [List.mem_filter, hab, ha]
        exact Or.inr (ih _ hlt _ rfl a ha')

private theorem mem_eraseDups_of_mem {a : ValName} {l : List ValName} (h : a ∈ l) : a ∈ l.eraseDups :=
  mem_eraseDups_of_mem_go l.length l rfl a h

private theorem ValName_list_eraseDups_idem_go :
    ∀ n, ∀ (l : List ValName), l.length = n → l.eraseDups.eraseDups = l.eraseDups := by
  intro n
  refine Nat.strongRecOn n (motive := fun n => ∀ (l : List ValName), l.length = n → l.eraseDups.eraseDups = l.eraseDups) fun n ih => ?_
  intro l hn
  match l with
  | [] => rfl
  | a :: l =>
    simp only [List.length_cons] at hn
    simp only [List.eraseDups_cons]
    set t := (List.filter (fun b => !b == a) l).eraseDups
    have hlt : (List.filter (fun b => !b == a) l).length < n := by
      rw [← hn]
      exact Nat.lt_add_one_of_le (List.length_filter_le _ l)
    have ih' := ih _ hlt _ rfl
    have ht : t.eraseDups = t := ih'
    have hfilter : List.filter (fun b => !b == a) t = t := by
      apply List.filter_eq_self.mpr
      intro b hb
      have hb' := mem_eraseDups hb
      simp [List.mem_filter] at hb' ⊢
      exact hb'.2
    congr 1
    calc (List.filter (fun b => !b == a) t).eraseDups
        = t.eraseDups := by rw [hfilter]
      _ = t := ht

private theorem ValName_list_eraseDups_idem (l : List ValName) :
    l.eraseDups.eraseDups = l.eraseDups :=
  ValName_list_eraseDups_idem_go l.length l rfl

private theorem lowerPoly_eraseDups_scheme {ke : KindEnv} (σ : Surface.PolyTy) :
    lowerPoly ke σ = lowerPoly ke { foralls := σ.foralls.eraseDups, body := σ.body } := by
  simp only [lowerPoly, ValName_list_eraseDups_idem]

/-- `finalizeAnn [] [] (some σ)` lowers exactly when `σ` does (after `eraseDups`). -/
theorem lowerPolyAnn_finalizeAnn_nil {ke : KindEnv} {σ : Surface.PolyTy} {σ' : PolyTy}
    (hσ : lowerPoly ke σ = some σ') :
    lowerPolyAnn ke (finalizeAnn [] [] (some σ)) = some (some σ') := by
  rw [finalizeAnn_nil_some, lowerPolyAnn, ← lowerPoly_eraseDups_scheme, hσ]
  simp

theorem bindingLowerTyScope_length (b : Surface.Binding) (tvs : List ValName) :
    tvs.length ≤ (bindingLowerTyScope b tvs).length := by
  simp only [bindingLowerTyScope, List.length_append]
  exact Nat.le_add_left _ _

@[simp] theorem wrapCoreParams_nil (ke : KindEnv) (tvs : List ValName) (e : Expr) :
    wrapCoreParams ke tvs [] e = some e := rfl

@[simp] theorem paramTermScope_nil (vs : List ValName) :
    paramTermScope [] vs = vs := rfl

theorem mergeTyParamNames_nil (foralls : List ValName) :
    mergeTyParamNames [] foralls = foralls.eraseDups := rfl

@[simp] theorem letAnnTyPrefix_none (tyParams : List ValName) :
    letAnnTyPrefix tyParams none = [] := rfl

private theorem bindingLowerTyScope_tyParams_nil {b : Surface.Binding} {tvs : List ValName}
    (htp : b.tyParams = []) :
    bindingLowerTyScope b tvs =
      letAnnTyPrefix [] (finalizeAnn [] b.params b.ann) ++ tvs := by
  simp [bindingLowerTyScope, letAnnTyPrefix, htp]

private theorem bindingLowerTyScope_nilTyParams_nilAnn {b : Surface.Binding} {tvs : List ValName}
    (htp : b.tyParams = []) (hann : b.ann = none) :
    bindingLowerTyScope b tvs = tvs := by
  simp [bindingLowerTyScope, letAnnTyPrefix, htp, hann, finalizeAnn_none]

private theorem not_mem_removeAll_singleton {x : ValName} {l : List ValName}
    (h : ∀ a, a ∈ l → a ≠ x) : l.removeAll [x] = l := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.removeAll, List.filter_cons]
    by_cases heq : a = x
    · exact absurd heq (h a (by simp))
    · grind

private theorem removeAll_cons_dup {x : ValName} {xs l : List ValName} :
    l.removeAll (x :: x :: xs) = l.removeAll (x :: xs) := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.removeAll, List.filter_cons]
    grind

private theorem removeAll_cons_head {x : ValName} {L xs : List ValName} :
    (x :: L).removeAll (x :: xs) = L.removeAll (x :: xs) := by
  simp [List.cons_removeAll]

private theorem mem_filter_ne {x a : ValName} {l : List ValName}
    (ha : a ∈ List.filter (fun b => !b == x) l) : a ≠ x := by
  simp [List.mem_filter] at ha
  exact ha.2

private theorem mem_removeAll_ne {a : ValName} {l ys : List ValName}
    (h : a ∈ l.removeAll ys) (hy : a ∈ ys) : False := by
  unfold List.removeAll at h
  simp [List.mem_filter] at h
  exact h.2 (by simp [hy])

private theorem mem_removeAll_left {a : ValName} {l ys : List ValName}
    (h : a ∈ l.removeAll ys) : a ∈ l := by
  unfold List.removeAll at h
  simp [List.mem_filter] at h
  exact h.1

private theorem removeAll_append_left_subset {xs A B : List ValName}
    (hA : ∀ a, a ∈ A → a ∈ xs) (hB : ∀ b, b ∈ B → b ∉ xs) :
    (A ++ B).removeAll xs = B := by
  simp only [List.removeAll, List.filter_append]
  have hFA : List.filter (fun x => !List.elem x xs) A = [] := by
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro a ha
    simp [List.mem_filter] at ha
    have hx := hA a ha.1
    simp [hx] at ha
  rw [hFA, List.nil_append]
  apply List.filter_eq_self.mpr
  intro b hb
  have hx := hB b hb
  simp [hx]

private theorem removeAll_eraseDups_cons {x : ValName} {xs rest : List ValName} :
    let fx := List.filter (fun b => !b == x) xs
    let fr := List.filter (fun b => !b == x) rest
    ((fx ++ fr).eraseDups.removeAll (x :: xs)).eraseDups = (fr.removeAll fx).eraseDups := by
  intro fx fr
  induction xs with
  | nil =>
    change ((List.filter (fun b => !b == x) [] ++ fr).eraseDups.removeAll [x]).eraseDups =
      (fr.removeAll []).eraseDups
    simp [List.filter_nil, List.nil_append, List.removeAll_nil]
    rw [not_mem_removeAll_singleton (l := fr.eraseDups)
      (fun a ha => mem_filter_ne (ha := mem_eraseDups ha)), ValName_list_eraseDups_idem]
  | cons y xs ih =>
    by_cases heq : y = x
    · rw [heq, removeAll_cons_dup]
      grind
    · have hfx : fx = y :: List.filter (fun b => !b == x) xs := by
        dsimp [fx]
        simp [beq_eq_false_iff_ne.mpr heq]
      rw [hfx, List.eraseDups_append]
      simp only [List.eraseDups_cons, List.cons_append, List.cons_removeAll, List.contains_cons,
        beq_self_eq_true, beq_eq_false_iff_ne.mpr heq, Bool.true_or]
      split_ifs
      · rename_i hif
        exact False.elim (by simp at hif)
      · rw [List.removeAll_cons, List.removeAll_cons]
        have h1 : List.filter (fun x_1 => !x_1 == x)
            ((List.filter (fun b => !b == y) (List.filter (fun b => !b == x) xs)).eraseDups ++
              (fr.removeAll (y :: List.filter (fun b => !b == x) xs)).eraseDups) =
          (List.filter (fun b => !b == y) (List.filter (fun b => !b == x) xs)).eraseDups ++
            (fr.removeAll (y :: List.filter (fun b => !b == x) xs)).eraseDups := by
          apply List.filter_eq_self.mpr
          intro a ha
          simp [List.mem_append] at ha
          cases ha with
          | inl ha =>
            have ha01 := List.mem_filter.mp (mem_eraseDups ha)
            exact (Bool.and_eq_true_iff.mp ha01.2).2
          | inr ha =>
            have ha01 := List.mem_filter.mp (mem_removeAll_left (mem_eraseDups ha))
            exact ha01.2
        rw [h1]
        have h2 : List.filter (fun x => !x == y)
            ((List.filter (fun b => !b == y) (List.filter (fun b => !b == x) xs)).eraseDups ++
              (fr.removeAll (y :: List.filter (fun b => !b == x) xs)).eraseDups) =
          (List.filter (fun b => !b == y) (List.filter (fun b => !b == x) xs)).eraseDups ++
            (fr.removeAll (y :: List.filter (fun b => !b == x) xs)).eraseDups := by
          apply List.filter_eq_self.mpr
          intro a ha
          simp [List.mem_append] at ha
          cases ha with
          | inl ha =>
            have ha01 := List.mem_filter.mp (mem_eraseDups ha)
            exact (Bool.and_eq_true_iff.mp ha01.2).1
          | inr ha =>
            have ha0 := mem_eraseDups ha
            simp [beq_eq_false_iff_ne]
            intro hy
            exact mem_removeAll_ne ha0 (by simp [List.mem_cons, hy])
        rw [h2]
        rw [removeAll_append_left_subset (xs := xs)
          (A := (List.filter (fun b => !b == y) (List.filter (fun b => !b == x) xs)).eraseDups)
          (B := (fr.removeAll (y :: List.filter (fun b => !b == x) xs)).eraseDups)]
        · rw [ValName_list_eraseDups_idem]
        · intro a ha
          have ha1 := List.mem_filter.mp (mem_eraseDups ha)
          exact (List.mem_filter.mp ha1.1).1
        · intro b hb
          have hb0 := mem_eraseDups hb
          intro hx
          by_cases hy : b = y
          · subst hy
            exact mem_removeAll_ne hb0 (List.mem_cons.mpr (Or.inl rfl))
          · have hbx := mem_filter_ne (ha := mem_removeAll_left hb0)
            have hx' : b ∈ List.filter (fun b => !b == x) xs := by
              simp [List.mem_filter, hx, hbx]
            exact mem_removeAll_ne hb0 (List.mem_cons.mpr (Or.inr hx'))

private theorem eraseDups_removeAll_append {xs rest : List ValName} :
    xs.eraseDups ++ ((xs ++ rest).eraseDups.removeAll xs).eraseDups = (xs ++ rest).eraseDups := by
  match xs with
  | [] => simp [ValName_list_eraseDups_idem]
  | x :: xs =>
    simp only [List.cons_append, List.eraseDups_cons, List.filter_append, List.cons.injEq, true_and,
      List.eraseDups_append]
    apply congrArg
    rw [removeAll_cons_head, ← List.eraseDups_append]
    exact removeAll_eraseDups_cons (x := x) (xs := xs) (rest := rest)

private theorem eraseDups_append_left_subset {xs rest : List ValName} :
    (xs ++ (xs ++ rest).eraseDups).eraseDups = (xs ++ rest).eraseDups := by
  rw [List.eraseDups_append, eraseDups_removeAll_append]

private theorem eraseDups_append_eraseDups {xs : List ValName} :
    (xs ++ xs.eraseDups).eraseDups = xs.eraseDups := by
  have := eraseDups_append_left_subset (xs := xs) (rest := [])
  simp only [List.append_nil] at this
  exact this

private theorem mergeTyParamNames_idem (tyParams foralls : List ValName) :
    mergeTyParamNames tyParams (mergeTyParamNames tyParams foralls) =
      mergeTyParamNames tyParams foralls := by
  simp only [mergeTyParamNames, eraseDups_append_left_subset]

private theorem lowerPoly_paramCount {ke : KindEnv} {σ : Surface.PolyTy} {σ' : PolyTy}
    (h : lowerPoly ke σ = some σ') :
    σ'.paramCount = σ.foralls.eraseDups.length := by
  rw [lowerPoly] at h
  cases hty : lowerTy ke (σ.foralls.eraseDups) σ.body with
  | none => simp [hty] at h
  | some b =>
    simp [hty, Option.map_some] at h
    cases h
    rfl

private theorem finalizeAnn_foralls_merge {tyParams : List ValName}
    {params : List (ValName × Option Surface.Ty)} {ann : Option Surface.PolyTy}
    {σs : Surface.PolyTy} (h : finalizeAnn tyParams params ann = some σs) :
    mergeTyParamNames tyParams σs.foralls = σs.foralls.eraseDups := by
  cases params with
  | nil =>
    cases ann with
    | none => simp [finalizeAnn, mergeTyParams] at h
    | some poly =>
      cases h
      simp only [mergeTyParamNames]
      rw [eraseDups_append_left_subset (rest := poly.foralls), ValName_list_eraseDups_idem]
  | cons hd tl =>
    cases ann with
    | none => simp [finalizeAnn] at h
    | some poly =>
      cases poly with
      | mk foralls body =>
        cases hpt : paramsToArrows (hd :: tl) body with
        | none =>
          have hfin :
              finalizeAnn tyParams (hd :: tl) (some { foralls := foralls, body := body }) =
                some { foralls := mergeTyParamNames tyParams foralls, body := body } := by
            simp [finalizeAnn, hpt, mergeTyParams, mergeTyParamNames]
          rw [hfin] at h
          cases h
          simp only [mergeTyParamNames]
          rw [eraseDups_append_left_subset (rest := foralls), ValName_list_eraseDups_idem]
        | some body' =>
          have hfin :
              finalizeAnn tyParams (hd :: tl) (some { foralls := foralls, body := body }) =
                some { foralls := mergeTyParamNames tyParams foralls, body := body' } := by
            simp [finalizeAnn, hpt]
          rw [hfin] at h
          cases h
          simp only [mergeTyParamNames]
          rw [eraseDups_append_left_subset (rest := foralls), ValName_list_eraseDups_idem]

private theorem lowerPolyAnn_finalizeAnn_none {ke : KindEnv} {tyParams : List ValName}
    {params : List (ValName × Option Surface.Ty)} {ann : Option Surface.PolyTy}
    (h : lowerPolyAnn ke (finalizeAnn tyParams params ann) = some none) :
    finalizeAnn tyParams params ann = none := by
  cases hF : finalizeAnn tyParams params ann with
  | none => rfl
  | some σ =>
    simp only [lowerPolyAnn, hF] at h
    cases hσ : lowerPoly ke σ with
    | none => simp [hσ] at h
    | some σ' => simp [hσ, Option.map_some] at h

private theorem lowerPolyAnn_some_paramCount {ke : KindEnv} {tyParams : List ValName}
    {params : List (ValName × Option Surface.Ty)} {ann : Option Surface.PolyTy} {σ : PolyTy}
    (h : lowerPolyAnn ke (finalizeAnn tyParams params ann) = some (some σ)) :
    σ.paramCount =
      (letAnnTyPrefix tyParams (finalizeAnn tyParams params ann)).length := by
  cases hF : finalizeAnn tyParams params ann with
  | none => simp [lowerPolyAnn, hF] at h
  | some σs =>
    simp only [lowerPolyAnn, hF] at h
    cases hσ : lowerPoly ke σs with
    | none => simp [hσ] at h
    | some σ' =>
      have hσeq : σ' = σ := by
        have : some (some σ') = some (some σ) := by simpa [hσ, Option.map_some] using h
        exact Option.some.inj (Option.some.inj this)
      rw [← hσeq, lowerPoly_paramCount hσ]
      simp [letAnnTyPrefix, finalizeAnn_foralls_merge hF]

private theorem lowerPolyAnnIn_finalizeAnn_none {ke : KindEnv} {tvs : List ValName}
    {tyParams : List ValName} {params : List (ValName × Option Surface.Ty)}
    {ann : Option Surface.PolyTy}
    (h : lowerPolyAnnIn ke tvs (finalizeAnn tyParams params ann) = some none) :
    finalizeAnn tyParams params ann = none := by
  cases hF : finalizeAnn tyParams params ann with
  | none => rfl
  | some σ =>
    simp only [lowerPolyAnnIn, hF] at h
    cases hσ : lowerPolyIn ke tvs σ with
    | none => simp [hσ] at h
    | some σ' => simp [hσ, Option.map_some] at h

private theorem lowerPolyAnnIn_some_paramCount {ke : KindEnv} {tvs : List ValName}
    {tyParams : List ValName} {params : List (ValName × Option Surface.Ty)}
    {ann : Option Surface.PolyTy} {σ : PolyTy}
    (h : lowerPolyAnnIn ke tvs (finalizeAnn tyParams params ann) = some (some σ)) :
    σ.paramCount =
      (letAnnTyPrefix tyParams (finalizeAnn tyParams params ann)).length := by
  cases hF : finalizeAnn tyParams params ann with
  | none => simp [lowerPolyAnnIn, hF] at h
  | some σs =>
    simp only [lowerPolyAnnIn, hF] at h
    cases hσ : lowerPolyIn ke tvs σs with
    | none => simp [hσ] at h
    | some σ' =>
      have hσeq : σ' = σ := by
        have : some (some σ') = some (some σ) := by simpa [hσ, Option.map_some] using h
        exact Option.some.inj (Option.some.inj this)
      rw [← hσeq]
      simp only [lowerPolyIn] at hσ
      obtain ⟨b, hb, rfl⟩ := Option.map_eq_some_iff.mp hσ
      simp [letAnnTyPrefix, finalizeAnn_foralls_merge hF]

private theorem letIn_lowerTyScope_length {ke : KindEnv} {tyParams : List ValName}
    {params : List (ValName × Option Surface.Ty)} {ann : Option Surface.PolyTy}
    {ann' : Option PolyTy} {tvs : List ValName}
    (hann : lowerPolyAnn ke (finalizeAnn tyParams params ann) = some ann') :
    (letAnnTyPrefix tyParams (finalizeAnn tyParams params ann) ++ tvs).length =
      tvs.length +
        match ann' with
        | none => 0
        | some σ => σ.paramCount := by
  cases ann' with
  | none =>
    have hF := lowerPolyAnn_finalizeAnn_none hann
    simp [letAnnTyPrefix, hF]
  | some σ =>
    have hpc := lowerPolyAnn_some_paramCount hann
    simp [List.length_append, hpc, Nat.add_comm]

private theorem letIn_lowerTyScope_nilTyParams {ke : KindEnv}
    {params : List (ValName × Option Surface.Ty)} {ann : Option Surface.PolyTy}
    {ann' : Option PolyTy} {tvs : List ValName}
    (hann : lowerPolyAnn ke (finalizeAnn [] params ann) = some ann') :
    (letAnnTyPrefix [] (finalizeAnn [] params ann) ++ tvs).length =
      tvs.length + RecAnn.params ann' := by
  simp only [List.length_append, RecAnn.params]
  cases ann' with
  | none =>
    have hF := lowerPolyAnn_finalizeAnn_none hann
    simp [letAnnTyPrefix, hF]
  | some σ =>
    have hpc := lowerPolyAnn_some_paramCount hann
    simp [hpc, Nat.add_comm]

private theorem bindingLowerTyScope_ann_length {ke : KindEnv} {b : Surface.Binding}
    {tvs : List ValName} {ann' : Option PolyTy}
    (htp : b.tyParams = [])
    (hann : lowerPolyAnn ke (finalizeAnn b.tyParams b.params b.ann) = some ann') :
    (bindingLowerTyScope b tvs).length =
      tvs.length + RecAnn.params ann' := by
  rw [bindingLowerTyScope_tyParams_nil htp]
  exact letIn_lowerTyScope_nilTyParams (by rw [← htp]; exact hann)

private theorem lowerCoreExprSize_lt_lowerBranchesSize_cons {p : Surface.Pattern} {b : Surface.Expr}
    {rest : List (Surface.Pattern × Surface.Expr)} :
    lowerExprSize b < lowerBranchesSize ((p, b) :: rest) := by
  simp [lowerBranchesSize]; omega

/-- Compound lambda patterns compile as one exhaustive match on a hidden
    parameter. `_` cannot be written as a surface expression name. -/
def patternLambdaCore (ann : Option Ty) (pat : Surface.Pattern) (body : Expr) : Expr :=
  .lambda ann (lowerMatch (.var 0) [pat] (fun i => [body].getD i (.ctor cNil)))



/-- Complete-Core compatibility policy. Partial annotations deliberately fail here. -/
def coreLoweringOps : LoweringOps Expr (Option Ty) (Option PolyTy) :=
  { emission := PatComp.coreEmissionOps
    primLit := Expr.primLit
    primBinOp := Expr.primBinOp
    app := Expr.app
    lambda := Expr.lambda
    letIn := Expr.letIn
    letRec := Expr.letRec
    lowerParamAnn := lowerAnn
    finalize := finalizeAnn
    lowerBindAnn := lowerPolyAnnIn }
abbrev lowerCoreExpr := lowerExprWith coreLoweringOps
abbrev lowerCoreExprList := lowerExprListWith coreLoweringOps
abbrev lowerCoreBranches := lowerBranchesWith coreLoweringOps
abbrev lowerCoreRecBinds := lowerRecBindsWith coreLoweringOps
abbrev CoreLowersExpr := LowersExprWith coreLoweringOps
abbrev CoreLowersExprList := LowersExprListWith coreLoweringOps
abbrev CoreLowersBranches := LowersBranchesWith coreLoweringOps
abbrev CoreLowersRecBinds := LowersRecBindsWith coreLoweringOps

def lowerCore (ctors : CtorEnv) (s : Surface.Expr) : Option Expr :=
  lowerCoreExpr (kindEnvOfCtors ctors) [] [] s

def CoreLowers (ctors : CtorEnv) (s : Surface.Expr) (core : Expr) : Prop :=
  CoreLowersExpr ctors (kindEnvOfCtors ctors) [] [] s core

/-! ### Complete-Core compatibility equations -/

@[simp] private theorem coreLoweringOps_emission_proj : coreLoweringOps.emission = PatComp.coreEmissionOps := rfl
@[simp] private theorem coreLoweringOps_primLit_proj : coreLoweringOps.primLit = Expr.primLit := rfl
@[simp] private theorem coreLoweringOps_primBinOp_proj : coreLoweringOps.primBinOp = Expr.primBinOp := rfl
@[simp] private theorem coreLoweringOps_app_proj : coreLoweringOps.app = Expr.app := rfl
@[simp] private theorem coreLoweringOps_lambda_proj : coreLoweringOps.lambda = Expr.lambda := rfl
@[simp] private theorem coreLoweringOps_letIn_proj : coreLoweringOps.letIn = Expr.letIn := rfl
@[simp] private theorem coreLoweringOps_letRec_proj : coreLoweringOps.letRec = Expr.letRec := rfl
@[simp] private theorem coreLoweringOps_lowerParamAnn_proj : coreLoweringOps.lowerParamAnn = lowerAnn := rfl
@[simp] private theorem coreLoweringOps_finalize_proj : coreLoweringOps.finalize = finalizeAnn := rfl
@[simp] private theorem coreLoweringOps_lowerBindAnn_proj : coreLoweringOps.lowerBindAnn = lowerPolyAnnIn := rfl
@[simp] theorem coreLoweringOps_mkList (xs : List Expr) : coreLoweringOps.mkList xs = mkList xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [LoweringOps.mkList, mkList, ih]; rfl
@[simp] theorem coreLoweringOps_wrapParams (ke : KindEnv) (tvs : List ValName)
    (params : List (ValName × Option Surface.Ty)) (body : Expr) :
    coreLoweringOps.wrapParams ke tvs params body = wrapCoreParams ke tvs params body := by
  induction params with
  | nil => rfl
  | cons p rest ih =>
      rcases p with ⟨name, ann⟩
      rw [LoweringOps.wrapParams, ih, wrapCoreParams]
      change (do
        let ann' ← lowerAnn ke tvs ann
        let inner ← wrapCoreParams ke tvs rest body
        pure (Expr.lambda ann' inner)) = _
      cases lowerAnn ke tvs ann <;> cases wrapCoreParams ke tvs rest body <;> rfl
@[simp] theorem coreLoweringOps_match (scrut : Expr) (pats : List Surface.Pattern) (bodies : List Expr) :
    coreLoweringOps.match_ scrut pats bodies = lowerMatch scrut pats (fun i => bodies.getD i (.ctor cNil)) := rfl
@[simp] theorem coreLoweringOps_patternLambda (ann : Option Ty) (pat : Surface.Pattern) (body : Expr) :
    coreLoweringOps.patternLambda ann pat body = patternLambdaCore ann pat body := rfl
theorem lowerCoreExpr_eq (ke : KindEnv) (tvs vs : List ValName) (e : Surface.Expr) :
    lowerCoreExpr ke tvs vs e =
  match e with
  | .primLit (.bool b)  => some (.ctor (if b then cTrue else cFalse))
  | .primLit .unit      => some (.primLit .unit)
  | .primLit (.int n)   => some (.primLit (.int n))
  | .primLit (.nat n)   => some (.primLit (.nat n))
  | .primLit (.char c)  => some (.primLit (.char c))
  | .primBinOp op => some (.primBinOp op)
  | .pair a b =>
    match lowerCoreExpr ke tvs vs a, lowerCoreExpr ke tvs vs b with
    | some a', some b' => some (.app (.app (.ctor cPair) a') b')
    | _, _             => none
  | .cons h t =>
    match lowerCoreExpr ke tvs vs h, lowerCoreExpr ke tvs vs t with
    | some h', some t' => some (.app (.app (.ctor cCons) h') t')
    | _, _             => none
  | .list items =>
    match lowerCoreExprList ke tvs vs items with
    | some items' => some (mkList items')
    | none        => none
  | .lambda param paramAnn body =>
    match lowerAnn ke tvs paramAnn with
    | none       => none
    | some ann'  =>
      match param with
      | .name x =>
        match lowerCoreExpr ke tvs (x :: vs) body with
        | some b' => some (.lambda ann' b')
        | none    => none
      | .wildcard =>
        match lowerCoreExpr ke tvs (.mk "_" :: vs) body with
        | some b' => some (.lambda ann' b')
        | none    => none
      | _ =>
        match lowerCoreExpr ke tvs (patVars param ++ .mk "_" :: vs) body with
        | some b' => some (patternLambdaCore ann' param b')
        | none => none
  | .app f x =>
    match lowerCoreExpr ke tvs vs f, lowerCoreExpr ke tvs vs x with
    | some f', some x' => some (.app f' x')
    | _, _             => none
  | .letIn name tyParams params ann rhs body =>
    let annF := finalizeAnn tyParams params ann
    match lowerPolyAnnIn ke tvs annF with
    | none      => none
    | some ann' =>
      let tvs' := letAnnTyPrefix tyParams annF ++ tvs
      match lowerCoreExpr ke tvs' (paramTermScope params vs) rhs with
      | none => none
      | some rhsCore =>
        match wrapCoreParams ke tvs' params rhsCore with
        | none => none
        | some rhs' =>
          match lowerCoreExpr ke tvs (name :: vs) body with
          | some body' => some (.letIn ann' rhs' body')
          | none => none
  | .letRecIn binds body =>
    let recScope := binds.map (·.name) ++ vs
    match lowerCoreRecBinds ke tvs recScope binds,
          lowerCoreExpr ke tvs recScope body with
    | some bindings', some body' => some (.letRec bindings' body')
    | _, _                           => none
  | .var name =>
    match tvarIndex vs name with
    | some i => some (.var i)
    | none   => none
  | .ctor name => some (.ctor name)
  | .ife c t f =>
    match lowerCoreExpr ke tvs vs c, lowerCoreExpr ke tvs vs t, lowerCoreExpr ke tvs vs f with
    | some c', some t', some f' =>
        -- Same body function as `match_` / `bodyFn [t', f']` (defined later).
        some (lowerMatch c' [.ctor cTrue [], .ctor cFalse []]
          (fun i => [t', f'].getD i (.ctor cNil)))
    | _, _, _ => none
  | .match_ scrut brs =>
    match lowerCoreExpr ke tvs vs scrut, lowerCoreBranches ke tvs vs brs with
    | some scrut', some bodies' =>
        some (lowerMatch scrut' (brs.map Prod.fst) (fun i => bodies'.getD i (.ctor cNil)))
    | _, _ => none := by
  cases e <;> simp only [lowerCoreExpr, lowerExprWith, coreLoweringOps_wrapParams,
    coreLoweringOps_match, coreLoweringOps_patternLambda]
  all_goals first | rfl | (repeat' split <;> simp_all [lowerCoreExprList, lowerCoreBranches, lowerCoreRecBinds, lowerExprWith, coreLoweringOps_mkList, PatComp.coreEmissionOps])

theorem lowerCoreExprList_eq (ke : KindEnv) (tvs vs : List ValName) (es : List Surface.Expr) :
    lowerCoreExprList ke tvs vs es =
  match es with
  | []      => some []
  | e :: es =>
    match lowerCoreExpr ke tvs vs e, lowerCoreExprList ke tvs vs es with
    | some e', some es' => some (e' :: es')
    | _, _              => none := by
  cases es <;> simp only [lowerCoreExprList, lowerExprListWith]
  all_goals first | rfl | (repeat' split <;> simp_all [lowerCoreExpr])

theorem lowerCoreBranches_eq (ke : KindEnv) (tvs vs : List ValName) (brs : List (Surface.Pattern × Surface.Expr)) :
    lowerCoreBranches ke tvs vs brs =
  match brs with
  | []           => some []
  | (p, b) :: rest =>
    match lowerCoreExpr ke tvs (patVars p ++ vs) b, lowerCoreBranches ke tvs vs rest with
    | some b', some rest' => some (b' :: rest')
    | _, _                => none := by
  cases brs <;> try (rename_i head tail; rcases head with ⟨pat, body⟩); all_goals simp only [lowerCoreBranches, lowerBranchesWith]
  all_goals first | rfl | (repeat' split <;> simp_all [lowerCoreExpr, lowerCoreBranches, lowerBranchesWith])

theorem lowerCoreRecBinds_eq (ke : KindEnv) (tvs recScope : List ValName) (binds : List Surface.Binding) :
    lowerCoreRecBinds ke tvs recScope binds =
  match binds with
  | []               => some []
  | b :: rest =>
    let annF := finalizeAnn b.tyParams b.params b.ann
    match lowerPolyAnnIn ke tvs annF with
    | none => none
    | some ann' =>
      let tvs' := letAnnTyPrefix b.tyParams annF ++ tvs
      match lowerCoreExpr ke tvs' (paramTermScope b.params recScope) b.rhs with
      | none => none
      | some rhsCore =>
        match wrapCoreParams ke tvs' b.params rhsCore with
        | none => none
        | some rhs' =>
          match lowerCoreRecBinds ke tvs recScope rest with
          | some rest' => some ({ ann := ann', rhs := rhs' } :: rest')
          | none => none := by
  cases binds <;> simp only [lowerCoreRecBinds, lowerRecBindsWith, coreLoweringOps_wrapParams]
  all_goals first | rfl | (repeat' split <;> simp_all [lowerCoreExpr])


private theorem lowerCoreExpr_eqs (ke : KindEnv) (tvs vs : List ValName) :
    (∀ (b : Bool) , lowerCoreExpr ke tvs vs (.primLit (.bool b)) =
      (some (.ctor (if b then cTrue else cFalse)))) ∧
    (lowerCoreExpr ke tvs vs (.primLit .unit) =
      (some (.primLit .unit))) ∧
    (∀ (n : Int) , lowerCoreExpr ke tvs vs (.primLit (.int n)) =
      (some (.primLit (.int n)))) ∧
    (∀ (n : Nat) , lowerCoreExpr ke tvs vs (.primLit (.nat n)) =
      (some (.primLit (.nat n)))) ∧
    (∀ (c : Char) , lowerCoreExpr ke tvs vs (.primLit (.char c)) =
      (some (.primLit (.char c)))) ∧
    (∀ (op : PrimBinOp) , lowerCoreExpr ke tvs vs (.primBinOp op) =
      (some (.primBinOp op))) ∧
    (∀ (a b : Surface.Expr) , lowerCoreExpr ke tvs vs (.pair a b) =
      (match lowerCoreExpr ke tvs vs a, lowerCoreExpr ke tvs vs b with
    | some a', some b' => some (.app (.app (.ctor cPair) a') b')
    | _, _             => none)) ∧
    (∀ (h t : Surface.Expr) , lowerCoreExpr ke tvs vs (.cons h t) =
      (match lowerCoreExpr ke tvs vs h, lowerCoreExpr ke tvs vs t with
    | some h', some t' => some (.app (.app (.ctor cCons) h') t')
    | _, _             => none)) ∧
    (∀ (items : List Surface.Expr) , lowerCoreExpr ke tvs vs (.list items) =
      (match lowerCoreExprList ke tvs vs items with
    | some items' => some (mkList items')
    | none        => none)) ∧
    (∀ (param : Surface.Pattern) (paramAnn : Option Surface.Ty) (body : Surface.Expr) , lowerCoreExpr ke tvs vs (.lambda param paramAnn body) =
      (match lowerAnn ke tvs paramAnn with
    | none       => none
    | some ann'  =>
      match param with
      | .name x =>
        match lowerCoreExpr ke tvs (x :: vs) body with
        | some b' => some (.lambda ann' b')
        | none    => none
      | .wildcard =>
        match lowerCoreExpr ke tvs (.mk "_" :: vs) body with
        | some b' => some (.lambda ann' b')
        | none    => none
      | _ =>
        match lowerCoreExpr ke tvs (patVars param ++ .mk "_" :: vs) body with
        | some b' => some (patternLambdaCore ann' param b')
        | none => none)) ∧
    (∀ (f x : Surface.Expr) , lowerCoreExpr ke tvs vs (.app f x) =
      (match lowerCoreExpr ke tvs vs f, lowerCoreExpr ke tvs vs x with
    | some f', some x' => some (.app f' x')
    | _, _             => none)) ∧
    (∀ (name : ValName) (tyParams : List ValName) (params : List (ValName × Option Surface.Ty)) (ann : Option Surface.PolyTy) (rhs body : Surface.Expr) , lowerCoreExpr ke tvs vs (.letIn name tyParams params ann rhs body) =
      (let annF := finalizeAnn tyParams params ann
    match lowerPolyAnnIn ke tvs annF with
    | none      => none
    | some ann' =>
      let tvs' := letAnnTyPrefix tyParams annF ++ tvs
      match lowerCoreExpr ke tvs' (paramTermScope params vs) rhs with
      | none => none
      | some rhsCore =>
        match wrapCoreParams ke tvs' params rhsCore with
        | none => none
        | some rhs' =>
          match lowerCoreExpr ke tvs (name :: vs) body with
          | some body' => some (.letIn ann' rhs' body')
          | none => none)) ∧
    (∀ (binds : List Surface.Binding) (body : Surface.Expr) , lowerCoreExpr ke tvs vs (.letRecIn binds body) =
      (let recScope := binds.map (·.name) ++ vs
    match lowerCoreRecBinds ke tvs recScope binds,
          lowerCoreExpr ke tvs recScope body with
    | some bindings', some body' => some (.letRec bindings' body')
    | _, _                           => none)) ∧
    (∀ (name : ValName) , lowerCoreExpr ke tvs vs (.var name) =
      (match tvarIndex vs name with
    | some i => some (.var i)
    | none   => none)) ∧
    (∀ (name : CtorName) , lowerCoreExpr ke tvs vs (.ctor name) =
      (some (.ctor name))) ∧
    (∀ (c t f : Surface.Expr) , lowerCoreExpr ke tvs vs (.ife c t f) =
      (match lowerCoreExpr ke tvs vs c, lowerCoreExpr ke tvs vs t, lowerCoreExpr ke tvs vs f with
    | some c', some t', some f' =>
        -- Same body function as `match_` / `bodyFn [t', f']` (defined later).
        some (lowerMatch c' [.ctor cTrue [], .ctor cFalse []]
          (fun i => [t', f'].getD i (.ctor cNil)))
    | _, _, _ => none)) ∧
    (∀ (scrut : Surface.Expr) (brs : List (Surface.Pattern × Surface.Expr)) , lowerCoreExpr ke tvs vs (.match_ scrut brs) =
      (match lowerCoreExpr ke tvs vs scrut, lowerCoreBranches ke tvs vs brs with
    | some scrut', some bodies' =>
        some (lowerMatch scrut' (brs.map Prod.fst) (fun i => bodies'.getD i (.ctor cNil)))
    | _, _ => none)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intros <;> rw [lowerCoreExpr_eq]

private theorem lowerCoreExprList_eqs (ke : KindEnv) (tvs vs : List ValName) :
    (lowerCoreExprList ke tvs vs ([]) =
      (some [])) ∧
    (∀ (e : Surface.Expr) (es : List Surface.Expr) , lowerCoreExprList ke tvs vs (e :: es) =
      (match lowerCoreExpr ke tvs vs e, lowerCoreExprList ke tvs vs es with
    | some e', some es' => some (e' :: es')
    | _, _              => none)) := by
  refine ⟨?_, ?_⟩ <;> intros <;> rw [lowerCoreExprList_eq]

private theorem lowerCoreBranches_eqs (ke : KindEnv) (tvs vs : List ValName) :
    (lowerCoreBranches ke tvs vs ([]) =
      (some [])) ∧
    (∀ (p : Surface.Pattern) (b : Surface.Expr) (rest : List (Surface.Pattern × Surface.Expr)) , lowerCoreBranches ke tvs vs ((p, b) :: rest) =
      (match lowerCoreExpr ke tvs (patVars p ++ vs) b, lowerCoreBranches ke tvs vs rest with
    | some b', some rest' => some (b' :: rest')
    | _, _                => none)) := by
  refine ⟨?_, ?_⟩ <;> intros <;> rw [lowerCoreBranches_eq]

private theorem lowerCoreRecBinds_eqs (ke : KindEnv) (tvs recScope : List ValName) :
    (lowerCoreRecBinds ke tvs recScope ([]) =
      (some [])) ∧
    (∀ (b : Surface.Binding) (rest : List Surface.Binding) , lowerCoreRecBinds ke tvs recScope (b :: rest) =
      (let annF := finalizeAnn b.tyParams b.params b.ann
    match lowerPolyAnnIn ke tvs annF with
    | none => none
    | some ann' =>
      let tvs' := letAnnTyPrefix b.tyParams annF ++ tvs
      match lowerCoreExpr ke tvs' (paramTermScope b.params recScope) b.rhs with
      | none => none
      | some rhsCore =>
        match wrapCoreParams ke tvs' b.params rhsCore with
        | none => none
        | some rhs' =>
          match lowerCoreRecBinds ke tvs recScope rest with
          | some rest' => some ({ ann := ann', rhs := rhs' } :: rest')
          | none => none)) := by
  refine ⟨?_, ?_⟩ <;> intros <;> rw [lowerCoreRecBinds_eq]



/-- A compound lambda lowers exactly like a lambda around a singleton match.
    The inaccessible `_` slot is the argument; captures precede it in the body. -/
private theorem lowerCoreExpr_patternLambda {ke : KindEnv} {tvs vs : List ValName}
    {param : Surface.Pattern} {ann : Option Surface.Ty} {body : Surface.Expr}
    (hp : compoundLambdaPattern param = true) :
    lowerCoreExpr ke tvs vs (.lambda param ann body) =
      match lowerAnn ke tvs ann,
        lowerCoreExpr ke tvs (.mk "_" :: vs) (.match_ (.var (.mk "_")) [(param, body)]) with
      | some ann', some matched => some (.lambda ann' matched)
      | _, _ => none := by
  cases param <;> simp_all [compoundLambdaPattern, lowerCoreExpr_eqs, lowerCoreBranches_eqs, tvarIndex]
  all_goals
    cases lowerAnn ke tvs ann <;>
      cases lowerCoreExpr ke tvs _ body <;> rfl

-- Adversarial `#guard`s for the executable lowering.
private def ctorsDemo : CtorEnv := (elabDecls preludeDecls).getD []

-- bool literal desugars to the True/False ctor
#guard match lowerCore ctorsDemo (.primLit (.bool true)) with
  | some (.ctor (.mk "True")) => true | _ => false
-- unbound variable fails
#guard (lowerCore ctorsDemo (.var (.mk "x"))).isNone
-- λx. x  ↦  λ. var 0
#guard match lowerCore ctorsDemo (.lambda (.name (.mk "x")) none (.var (.mk "x"))) with
  | some (.lambda none (.var 0)) => true | _ => false
-- let x = 1 in x  ↦  let 1 in var 0
#guard match lowerCore ctorsDemo (.letIn (.mk "x") [] [] none (.primLit (.int 1)) (.var (.mk "x"))) with
  | some (.letIn none (.primLit (.int 1)) (.var 0)) => true | _ => false
-- (1, 2)  ↦  Pair 1 2
#guard match lowerCore ctorsDemo (.pair (.primLit (.int 1)) (.primLit (.int 2))) with
  | some (.app (.app (.ctor (.mk "Pair")) (.primLit (.int 1))) (.primLit (.int 2))) => true | _ => false
-- [1]  ↦  Cons 1 Nil
#guard match lowerCore ctorsDemo (.list [.primLit (.int 1)]) with
  | some (.app (.app (.ctor (.mk "Cons")) (.primLit (.int 1))) (.ctor (.mk "Nil"))) => true | _ => false
-- shadowing: λx. λx. x  ↦  inner x is var 0
#guard match lowerCore ctorsDemo (.lambda (.name (.mk "x")) none (.lambda (.name (.mk "x")) none (.var (.mk "x")))) with
  | some (.lambda none (.lambda none (.var 0))) => true | _ => false
-- outer reference: λx. λy. x  ↦  x is var 1 under two binders
#guard match lowerCore ctorsDemo (.lambda (.name (.mk "x")) none (.lambda (.name (.mk "y")) none (.var (.mk "x")))) with
  | some (.lambda none (.lambda none (.var 1))) => true | _ => false
-- ife and match produce some (structure checked by the pattern-compilation tests)
#guard (lowerCore ctorsDemo (.ife (.primLit (.bool true)) (.primLit (.int 1)) (.primLit (.int 0)))).isSome
#guard (lowerCore ctorsDemo (.match_ (.var (.mk "x")) [])).isNone  -- unbound scrutinee
-- primBinOp leaves lowerCore identity
#guard match lowerCoreExpr ([] : KindEnv) [] [] (.primBinOp .intAdd) with
  | some (.primBinOp .intAdd) => true | _ => false
#guard match lowerCoreExpr ([] : KindEnv) [] [] (.primBinOp .intSub) with
  | some (.primBinOp .intSub) => true | _ => false



/-! ## 6. The `CoreLowers` relation (spec — deterministic, pins `lowerMatch`)

Mirrors `lowerCoreExpr` everywhere, including `match_` / `ife`: both pin the Core
term to the same `lowerMatch scrut' pats (bodyFn bodies')` that the executable
pipeline emits. Behavioural adequacy of that sugar is a separate theorem
(`lowerMatch_adequate_of_typed`); it is not packed into the `CoreLowers` rule. -/

/-- The default body used when indexing past the branch bodies list; never
    actually reached (`firstMatch` only returns indices `< brs.length`), but
    needed to give `lowerMatch` a total `Nat → Expr` body function. Shared by
    `lowerCore` and the `CoreLowers` match rule so they pin the *same* body function. -/
def matchBodyDefault : Expr := .ctor cNil

/-- The `Nat → Expr` body function for a match with lowered branch bodies
    `bodies'`, mirroring `lowerCore`'s `fun i => bodies'.getD i _`. -/
def bodyFn (bodies' : List Expr) : Nat → Expr := fun i => bodies'.getD i matchBodyDefault

/-! ### Complete-Core correctness corollaries

The shared structural compiler supplies soundness and completeness for this
specialization; the existing surface typing proofs below use these corollaries. -/

/-- Body function emitted by `lowerCoreExpr` matches the pinned `bodyFn`. -/
private theorem bodyFn_eq_getD_cNil (bodies' : List Expr) :
    (fun i => bodies'.getD i (.ctor cNil)) = bodyFn bodies' := by
  funext i; simp [bodyFn, matchBodyDefault]

theorem lowerCoreExpr_eq_some_of_CoreLowersExpr {ctors : CtorEnv} {ke : KindEnv}
    {tvs vs : List ValName} {s : Surface.Expr} {out : Expr}
    (h : CoreLowersExpr ctors ke tvs vs s out) :
    lowerCoreExpr ke tvs vs s = some out :=
  lowerExprWith_complete h

theorem lowerCoreExprList_eq_some_of_CoreLowersExprList {ctors : CtorEnv} {ke : KindEnv}
    {tvs vs : List ValName} {es : List Surface.Expr} {out : List Expr}
    (h : CoreLowersExprList ctors ke tvs vs es out) :
    lowerCoreExprList ke tvs vs es = some out :=
  lowerExprListWith_complete h

theorem lowerCoreRecBinds_eq_some_of_CoreLowersRecBinds {ctors : CtorEnv} {ke : KindEnv}
    {tvs vs : List ValName} {bs : List Surface.Binding} {out : List CoreRecBinding}
    (h : CoreLowersRecBinds ctors ke tvs vs bs out) :
    lowerCoreRecBinds ke tvs vs bs = some out :=
  lowerRecBindsWith_complete h

theorem lowerCoreBranches_eq_some_of_CoreLowersBranches {ctors : CtorEnv} {ke : KindEnv}
    {tvs vs : List ValName} {bs : List (Surface.Pattern × Surface.Expr)} {out : List Expr}
    (h : CoreLowersBranches ctors ke tvs vs bs out) :
    lowerCoreBranches ke tvs vs bs = some out :=
  lowerBranchesWith_complete h

theorem lowerCoreExpr_isSome_of_CoreLowersExpr {ctors : CtorEnv} {ke : KindEnv} {tvs : List ValName}
    {vs : List ValName} (s : Surface.Expr) {c : Expr}
    (h : CoreLowersExpr ctors ke tvs vs s c) : (lowerCoreExpr ke tvs vs s).isSome :=
  Option.isSome_iff_exists.mpr ⟨_, lowerCoreExpr_eq_some_of_CoreLowersExpr h⟩

theorem lowerCoreExprList_isSome_of_CoreLowersExprList {ctors : CtorEnv} {ke : KindEnv} {tvs : List ValName}
    {vs : List ValName} (es : List Surface.Expr) {es' : List Expr}
    (h : CoreLowersExprList ctors ke tvs vs es es') : (lowerCoreExprList ke tvs vs es).isSome := by
  rw [lowerCoreExprList_eq_some_of_CoreLowersExprList h, Option.isSome_some]

theorem lowerCoreRecBinds_isSome_of_CoreLowersRecBinds {ctors : CtorEnv} {ke : KindEnv} {tvs : List ValName}
    {vs : List ValName} (binds : List Surface.Binding) {bindings' : List CoreRecBinding}
    (h : CoreLowersRecBinds ctors ke tvs vs binds bindings') :
    (lowerCoreRecBinds ke tvs vs binds).isSome := by
  rw [lowerCoreRecBinds_eq_some_of_CoreLowersRecBinds h, Option.isSome_some]

theorem lowerCoreBranches_isSome_of_CoreLowersBranches {ctors : CtorEnv} {ke : KindEnv} {tvs : List ValName}
    {vs : List ValName} (brs : List (Surface.Pattern × Surface.Expr)) {bodies' : List Expr}
    (h : CoreLowersBranches ctors ke tvs vs brs bodies') :
    (lowerCoreBranches ke tvs vs brs).isSome := by
  rw [lowerCoreBranches_eq_some_of_CoreLowersBranches h, Option.isSome_some]

/-- Completeness: declarative `CoreLowers` ⇒ executable `lowerCore` returns that same Core term. -/
theorem lowerCore_complete {ctors : CtorEnv} {s : Surface.Expr} {c : Expr}
    (h : CoreLowers ctors s c) : lowerCore ctors s = some c := by
  simp only [CoreLowers, lowerCore] at h ⊢
  exact lowerCoreExpr_eq_some_of_CoreLowersExpr h

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

theorem lowerCoreExpr_CoreLowersExpr {ctors : CtorEnv} {ke : KindEnv}
    {tvs vs : List ValName} (s : Surface.Expr) {out : Expr}
    (h : lowerCoreExpr ke tvs vs s = some out) :
    CoreLowersExpr ctors ke tvs vs s out :=
  lowerExprWith_sound s h

theorem lowerCoreExprList_CoreLowersExprList {ctors : CtorEnv} {ke : KindEnv}
    {tvs vs : List ValName} (es : List Surface.Expr) {out : List Expr}
    (h : lowerCoreExprList ke tvs vs es = some out) :
    CoreLowersExprList ctors ke tvs vs es out :=
  lowerExprListWith_sound es h

theorem lowerCoreRecBinds_CoreLowersRecBinds {ctors : CtorEnv} {ke : KindEnv}
    {tvs vs : List ValName} (bs : List Surface.Binding) {out : List CoreRecBinding}
    (h : lowerCoreRecBinds ke tvs vs bs = some out) :
    CoreLowersRecBinds ctors ke tvs vs bs out :=
  lowerRecBindsWith_sound bs h

theorem lowerCoreBranches_CoreLowersBranches {ctors : CtorEnv} {ke : KindEnv}
    {tvs vs : List ValName} (bs : List (Surface.Pattern × Surface.Expr)) {out : List Expr}
    (h : lowerCoreBranches ke tvs vs bs = some out) :
    CoreLowersBranches ctors ke tvs vs bs out :=
  lowerBranchesWith_sound bs h

/-- **`lowerCore` soundness:** the executable lowering satisfies the spec. -/
theorem lowerCore_sound {ctors : CtorEnv} {s : Surface.Expr} {c : Expr}
    (h : lowerCore ctors s = some c) : CoreLowers ctors s c := by
  simp only [lowerCore] at h
  exact lowerCoreExpr_CoreLowersExpr s h


/-! ### Functional `CoreLowers` uniqueness (NoMatch fragment)

With `match_` / `ife` both pinned to `lowerMatch`, `CoreLowersExpr` is deterministic
in the Core term for every constructor. The historical uniqueness proof still
lives under `SurfaceExprNoMatch` (no surface `match_` node); full uniqueness
follows from `lowerCoreExpr_eq_some_of_CoreLowersExpr` + injectivity of `some` once both
sides lowerCore. -/

mutual
/-- No surface `match_` anywhere in the expression. `ife` is allowed (Core-level
    match via deterministic `lowerMatch` sugar). -/
inductive SurfaceExprNoMatch : Surface.Expr → Prop where
  | primLit {p} : SurfaceExprNoMatch (.primLit p)
  | primBinOp {op} : SurfaceExprNoMatch (.primBinOp op)
  | pair {a b} : SurfaceExprNoMatch a → SurfaceExprNoMatch b → SurfaceExprNoMatch (.pair a b)
  | cons {h t} : SurfaceExprNoMatch h → SurfaceExprNoMatch t → SurfaceExprNoMatch (.cons h t)
  | list {items} : SurfaceExprListNoMatch items → SurfaceExprNoMatch (.list items)
  | lambda {param ann body} :
      SurfaceExprNoMatch body → SurfaceExprNoMatch (.lambda param ann body)
  | app {f x} : SurfaceExprNoMatch f → SurfaceExprNoMatch x → SurfaceExprNoMatch (.app f x)
  | letIn {name tyParams params ann rhs body} :
      SurfaceExprNoMatch rhs → SurfaceExprNoMatch body →
      SurfaceExprNoMatch (.letIn name tyParams params ann rhs body)
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
    List Surface.Binding → Prop where
  | nil : SurfaceExprLetRecNoMatch []
  | cons {bind rest} :
      SurfaceExprNoMatch bind.rhs → SurfaceExprLetRecNoMatch rest →
      SurfaceExprLetRecNoMatch (bind :: rest)
end

mutual
theorem CoreLowersExpr_unique_of_NoMatch (ctors : CtorEnv) (ke : KindEnv) (tvs : List ValName)
    (vs : List ValName) (s : Surface.Expr) (c₁ c₂ : Expr)
    (_hnm : SurfaceExprNoMatch s)
    (_h₁ : CoreLowersExpr ctors ke tvs vs s c₁) (_h₂ : CoreLowersExpr ctors ke tvs vs s c₂) :
    c₁ = c₂ := by
  exact Option.some.inj ((lowerCoreExpr_eq_some_of_CoreLowersExpr _h₁).symm.trans
    (lowerCoreExpr_eq_some_of_CoreLowersExpr _h₂))

theorem CoreLowersExprList_unique_of_NoMatch (ctors : CtorEnv) (ke : KindEnv) (tvs : List ValName)
    (vs : List ValName) (es : List Surface.Expr) (es₁ es₂ : List Expr)
    (_hnm : SurfaceExprListNoMatch es)
    (_h₁ : CoreLowersExprList ctors ke tvs vs es es₁)
    (_h₂ : CoreLowersExprList ctors ke tvs vs es es₂) : es₁ = es₂ := by
  cases _hnm with
  | nil =>
    cases _h₁; cases _h₂; rfl
  | cons he hes =>
    cases _h₁; cases _h₂
    expose_names
    have := CoreLowersExpr_unique_of_NoMatch ctors ke tvs vs _ _ _ he h h_2
    have := CoreLowersExprList_unique_of_NoMatch ctors ke tvs vs _ _ _ hes h_1 h_3
    simp_all

theorem CoreLowersRecBinds_unique_of_NoMatch (ctors : CtorEnv) (ke : KindEnv) (tvs : List ValName)
    (vs : List ValName) (binds : List Surface.Binding)
    (es₁ es₂ : List CoreRecBinding)
    (_hnm : SurfaceExprLetRecNoMatch binds)
    (_h₁ : CoreLowersRecBinds ctors ke tvs vs binds es₁)
    (_h₂ : CoreLowersRecBinds ctors ke tvs vs binds es₂) : es₁ = es₂ := by
  cases _hnm with
  | nil =>
    cases _h₁; cases _h₂; rfl
  | cons he hrest =>
    cases _h₁ with
    | cons hann₁ he₁ hwrap₁ hrest₁ =>
      cases _h₂ with
      | cons hann₂ he₂ hwrap₂ hrest₂ =>
        expose_names
        have hannEq : ann' = ann'_1 :=
          Option.some_inj.mp (hann₁.symm.trans hann₂)
        have hrhs := CoreLowersExpr_unique_of_NoMatch ctors ke (bindingLowerTyScope bind tvs)
            (paramTermScope bind.params vs) bind.rhs _ _ he he₁ he₂
        have hwrapEq : e' = e'_1 :=
          Option.some_inj.mp (hwrap₁.symm.trans (by rw [hrhs]; exact hwrap₂))
        have hrest' :=
          CoreLowersRecBinds_unique_of_NoMatch ctors ke tvs vs _ _ _ hrest hrest₁ hrest₂
        simp [hannEq, hwrapEq, hrest']
end

/-- On the `NoMatch` fragment, a `CoreLowers` witness equals the executable `lowerCore`. -/
theorem lowerCoreExpr_eq_of_CoreLowersExpr_of_NoMatch {ctors : CtorEnv} {ke : KindEnv}
    {tvs vs : List ValName} {s : Surface.Expr} {c₀ c : Expr}
    (hnm : SurfaceExprNoMatch s)
    (hL : CoreLowersExpr ctors ke tvs vs s c₀)
    (hlow : lowerCoreExpr ke tvs vs s = some c) :
    c₀ = c :=
  CoreLowersExpr_unique_of_NoMatch ctors ke tvs vs s c₀ c hnm hL (lowerCoreExpr_CoreLowersExpr s hlow)


/-! ## 7. Structural surface well-typedness

`SurfaceWTExpr` carries open branch typings at `match_` and `ife`, so the
executable `lowerCore` output is typeable via `TypeOfHM_lowerMatch` without a
side-channel on the compiled tree shape. -/

/-- Env for a match branch body: trivial schemes for pattern binders (in
    `patBindTys` / `patVars` pre-order) prepended to `Γ`. Mirrors
    `CoreLowersBranches` typing under `patVars p ++ vs`. -/
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

/-- Tyvar scope for typing / lowering a `let` binding RHS (matches `lowerCoreExpr`). -/
def letRhsTyScope (tyParams : List ValName) (params : List (ValName × Option Surface.Ty))
    (ann : Option Surface.PolyTy) (tvs : List ValName) : List ValName :=
  letAnnTyPrefix tyParams (finalizeAnn tyParams params ann) ++ tvs

def letRhsTermScope (params : List (ValName × Option Surface.Ty)) (vs : List ValName) :
    List ValName :=
  paramTermScope params vs

/-- Nest lowered param types over a Core return type (surface param order). -/
def coreParamsToArrows (paramTys : List Ty) (ret : Ty) : Ty :=
  paramTys.foldr Ty.arrow ret

/-- Lower annotated value-params into a Core env prefix (outer param leftmost in `params`).
    Rest params are typed under the outer param's binder; `paramTys` is outer-first so
    `coreParamsToArrows` / `wrapCoreParams` agree. Each lowered param type is `IsLC`
    (same obligation as `TypeOfHM.lambda` / `SurfaceWTExpr.lambda_*`). -/
inductive LowerLetParams (ke : KindEnv) (tvs : List ValName) :
    List (ValName × Option Surface.Ty) → Env → Env → List Ty → Prop
  | nil {Γ : Env} : LowerLetParams ke tvs [] Γ Γ []
  | cons {p : ValName × Option Surface.Ty} {rest : List (ValName × Option Surface.Ty)}
      {Γ Γ' : Env} {paramTys : List Ty} {τsurf : Surface.Ty} {τ : Ty} :
      p.2 = some τsurf →
      lowerTy ke tvs τsurf = some τ →
      τ.IsLC →
      LowerLetParams ke tvs rest (PolyTy.mkTrivial τ :: Γ) Γ' paramTys →
      LowerLetParams ke tvs (p :: rest) Γ Γ' (τ :: paramTys)

/-- `LowerLetParams` forces every param ann to `lowerTy`-successfully, so wrapping
    always succeeds (independent of the Core body being wrapped). -/
theorem wrapCoreParams_isSome_of_LowerLetParams {ke : KindEnv} {tvs : List ValName}
    {params : List (ValName × Option Surface.Ty)} {Γ Γ' : Env} {paramTys : List Ty}
    (h : LowerLetParams ke tvs params Γ Γ' paramTys) (e : Expr) :
    (wrapCoreParams ke tvs params e).isSome := by
  induction h generalizing e with
  | nil => simp [wrapCoreParams]
  | @cons p rest Γ Γ' paramTys τsurf τ hpann hty hlc hrest ih =>
    obtain ⟨e', he'⟩ := Option.isSome_iff_exists.mp (ih e)
    have hann : lowerAnn ke tvs p.2 = some (some τ) := by
      simp [lowerAnn, hpann, hty]
    simp [wrapCoreParams, he', hann]

/-- Wrapping value-params as Core λs preserves HM typing at `coreParamsToArrows`. -/
theorem wrapCoreParams_TypeOfHM {ctors : CtorEnv} {ke : KindEnv} {tvs : List ValName}
    {params : List (ValName × Option Surface.Ty)} {Γ ΓRhs : Env} {paramTys : List Ty}
    {e e' : Expr} {τret : Ty}
    (hLL : LowerLetParams ke tvs params Γ ΓRhs paramTys)
    (hwrap : wrapCoreParams ke tvs params e = some e')
    (h : TypeOfHM ⟨ΓRhs, ctors⟩ e τret) :
    TypeOfHM ⟨Γ, ctors⟩ e' (coreParamsToArrows paramTys τret) := by
  induction hLL generalizing e e' with
  | nil =>
    simp only [wrapCoreParams, Option.some.injEq] at hwrap
    subst hwrap
    simpa [coreParamsToArrows] using h
  | @cons p rest Γ Γ' paramTys τsurf τ hpann hty hlc hrest ih =>
    have hann : lowerAnn ke tvs p.2 = some (some τ) := by
      simp [lowerAnn, hpann, hty]
    cases hwr : wrapCoreParams ke tvs rest e with
    | none =>
      simp only [wrapCoreParams, hwr] at hwrap
      cases hwrap
    | some erest =>
      simp only [wrapCoreParams, hwr, hann, Option.some.injEq] at hwrap
      subst hwrap
      refine TypeOfHM.lambda hlc (fun a ha => by cases ha; rfl) rfl ?_
      simpa [coreParamsToArrows] using ih hwr h

@[simp] theorem letRhsTyScope_none (tyParams : List ValName)
    (params : List (ValName × Option Surface.Ty)) (tvs : List ValName) :
    letRhsTyScope tyParams params (none : Option Surface.PolyTy) tvs = tvs := by
  simp [letRhsTyScope, letAnnTyPrefix, finalizeAnn_none]

/-- Strong open surface well-typedness.
    At `match_`, ingredients are typed openly — not “the compiled tree typechecks”.
    Match-free fragments use `of_lowers` (unique CoreLowers + TypeOfHM). Match-capable
    forms recurse so induction reaches nested matches. -/
inductive SurfaceWTExpr (ctors : CtorEnv) (ke : KindEnv) :
    List ValName → List ValName → Env → Surface.Expr → Ty → Prop where
  /-- Match-free fragment: CoreLowers is unique, so TypeOfHM transfers to `lowerCoreExpr`. -/
  | of_lowers {tvs vs : List ValName} {Γ : Env} {s : Surface.Expr} {c : Expr} {τ : Ty} :
      SurfaceExprNoMatch s →
      CoreLowersExpr ctors ke tvs vs s c →
      TypeOfHM ⟨Γ, ctors⟩ c τ →
      SurfaceWTExpr ctors ke tvs vs Γ s τ
  | pair {tvs vs : List ValName} {Γ : Env} {a b : Surface.Expr} {τa τb τ : Ty} :
      SurfaceWTExpr ctors ke tvs vs Γ a τa →
      SurfaceWTExpr ctors ke tvs vs Γ b τb →
      TypeOfHM ⟨Γ, ctors⟩ (.ctor cPair) (.arrow τa (.arrow τb τ)) →
      SurfaceWTExpr ctors ke tvs vs Γ (.pair a b) τ
  | cons {tvs vs : List ValName} {Γ : Env} {h t : Surface.Expr} {τh τt τ : Ty} :
      SurfaceWTExpr ctors ke tvs vs Γ h τh →
      SurfaceWTExpr ctors ke tvs vs Γ t τt →
      TypeOfHM ⟨Γ, ctors⟩ (.ctor cCons) (.arrow τh (.arrow τt τ)) →
      SurfaceWTExpr ctors ke tvs vs Γ (.cons h t) τ
  | list {tvs vs : List ValName} {Γ : Env} {items : List Surface.Expr} {τelem : Ty} :
      (∀ e ∈ items, SurfaceWTExpr ctors ke tvs vs Γ e τelem) →
      TypeOfHM ⟨Γ, ctors⟩ (.ctor cNil) (.customTy nList [τelem]) →
      TypeOfHM ⟨Γ, ctors⟩ (.ctor cCons)
        (.arrow τelem (.arrow (.customTy nList [τelem]) (.customTy nList [τelem]))) →
      SurfaceWTExpr ctors ke tvs vs Γ (.list items) (.customTy nList [τelem])
  | app {tvs vs : List ValName} {Γ : Env} {f x : Surface.Expr} {τarg τ : Ty} :
      SurfaceWTExpr ctors ke tvs vs Γ f (.arrow τarg τ) →
      SurfaceWTExpr ctors ke tvs vs Γ x τarg →
      SurfaceWTExpr ctors ke tvs vs Γ (.app f x) τ
  | lambda_name {tvs vs : List ValName} {Γ : Env} {x : ValName} {ann : Option Surface.Ty}
      {body : Surface.Expr} {paramTy bodyTy : Ty} :
      paramTy.IsLC →
      (match ann with
        | none => True
        | some τs => lowerTy ke tvs τs = some paramTy) →
      SurfaceWTExpr ctors ke tvs (x :: vs) (PolyTy.mkTrivial paramTy :: Γ) body bodyTy →
      SurfaceWTExpr ctors ke tvs vs Γ (.lambda (.name x) ann body) (.arrow paramTy bodyTy)
  | lambda_wild {tvs vs : List ValName} {Γ : Env} {ann : Option Surface.Ty}
      {body : Surface.Expr} {paramTy bodyTy : Ty} :
      paramTy.IsLC →
      (match ann with
        | none => True
        | some τs => lowerTy ke tvs τs = some paramTy) →
      SurfaceWTExpr ctors ke tvs (.mk "_" :: vs) (PolyTy.mkTrivial paramTy :: Γ) body bodyTy →
      SurfaceWTExpr ctors ke tvs vs Γ (.lambda .wildcard ann body) (.arrow paramTy bodyTy)
  /-- Compound parameters use the existing open typing rule for singleton matches. -/
  | lambda_pattern {tvs vs : List ValName} {Γ : Env} {param : Surface.Pattern}
      {ann : Option Surface.Ty} {body : Surface.Expr} {paramTy bodyTy : Ty} :
      compoundLambdaPattern param = true →
      paramTy.IsLC →
      (match ann with
        | none => True
        | some τs => lowerTy ke tvs τs = some paramTy) →
      SurfaceWTExpr ctors ke tvs (.mk "_" :: vs) (PolyTy.mkTrivial paramTy :: Γ)
        (.match_ (.var (.mk "_")) [(param, body)]) bodyTy →
      SurfaceWTExpr ctors ke tvs vs Γ (.lambda param ann body) (.arrow paramTy bodyTy)
  /-- Unannotated mono let (value-param sugar allowed; `{tyParams}` bind only via a
      finalized scheme / `: ret` synthesis — see `letAnnTyPrefix`). Type the raw RHS
      under `letRhsTyScope` / `letRhsTermScope`; the bound name carries
      `τbind = coreParamsToArrows paramTys τret`. -/
  | letIn {tvs vs : List ValName} {Γ ΓRhs : Env}
      {name : ValName} {tyParams : List ValName}
      {params : List (ValName × Option Surface.Ty)}
      {rhs body : Surface.Expr} {τret τ τbind : Ty} {paramTys : List Ty} :
      LowerLetParams ke (letRhsTyScope tyParams params (none : Option Surface.PolyTy) tvs) params Γ ΓRhs paramTys →
      τbind = coreParamsToArrows paramTys τret →
      SurfaceWTExpr ctors ke (letRhsTyScope tyParams params (none : Option Surface.PolyTy) tvs)
        (letRhsTermScope params vs) ΓRhs rhs τret →
      SurfaceWTExpr ctors ke tvs (name :: vs) (PolyTy.mkTrivial τbind :: Γ) body τ →
      SurfaceWTExpr ctors ke tvs vs Γ (.letIn name tyParams params (none : Option Surface.PolyTy) rhs body) τ
  /-- Annotated let (mono or poly). Cofinite RHS openings mirror Core
      `GeneralisesTo`; `finalizeAnn` supplies the binding scheme.
      Value-param head binders are allowed: type the *raw* RHS under
      `paramTermScope` at `τretOf Xs`, and require
      `coreParamsToArrows paramTys (τretOf Xs) = σ.openVars Xs` so that
      `wrapCoreParams` yields a term typeable at the scheme opening
      (packing-B return-type sugar is the mono special case
      `τretOf = fun _ => τret`, `paramTys` the domains; poly with `params = []`
      is `τretOf = σ.openVars`, wrap identity).

      @TODO(ann-open-tvs): premise `tvs = []` is a **metatheory** restriction on this
      *constructor*, not a SurfaceLang authoring ban. The executable pipeline
      (`lowerCore` / `coreTypecheck` / `surface_type_safe`) does **not** consult it.

      What it blocks: inhabiting `SurfaceWTExpr` *via this structural rule* when the
      ambient open tyvar index `tvs` is already non-empty — e.g. while typing the RHS
      of an outer binding that extended `tvs` with `{a}`:

      ```
      -- surface (may still lowerCore + Core-coreTypecheck fine)
      let outer {a} : a → a =
        (\\x -> let inner (y : Int) : Int = y in x) in outer
      ```

      Here a structural proof of the *inner* annotated let would need
      `letInAnn` under `tvs` containing `a`, which this premise forbids. Closed
      top-level `SurfaceWT` still starts at `tvs = []`. Workarounds for the
      declarative relation: `of_lowers` (match-free + CoreLowers + TypeOfHM), or
      unannotated `letIn` for the inner binding. Fix: generalise ann transfer past
      `TyBvarBounded 0` / empty ambient `tvs` (open ladder under `n`). -/
  | letInAnn {tvs vs : List ValName} {Γ ΓRhs : Env}
      {name : ValName} {tyParams : List ValName}
      {params : List (ValName × Option Surface.Ty)}
      {σs : Surface.PolyTy} {σ : PolyTy}
      {rhs body : Surface.Expr} {τ : Ty} {L : List Nat}
      {paramTys : List Ty} {τretOf : List Nat → Ty} :
      tvs = [] →
      lowerPolyAnn ke (finalizeAnn tyParams params (some σs)) = some (some σ) →
      PolyTy.WF σ →
      LowerLetParams ke (letRhsTyScope tyParams params (some σs) tvs) params Γ ΓRhs paramTys →
      (∀ (Xs : List Nat), FreshNames L σ.paramCount Xs →
        SurfaceWTExpr ctors ke (letRhsTyScope tyParams params (some σs) tvs)
          (letRhsTermScope params vs) ΓRhs rhs (τretOf Xs)) →
      (∀ (Xs : List Nat), FreshNames L σ.paramCount Xs →
        coreParamsToArrows paramTys (τretOf Xs) = σ.openVars Xs) →
      SurfaceWTExpr ctors ke tvs (name :: vs) (σ :: Γ) body τ →
      SurfaceWTExpr ctors ke tvs vs Γ (.letIn name tyParams params (some σs) rhs body) τ
  /-- Unannotated monomorphic `letRecIn`. Each binding's `τs[i]` is the full
      binding type after value-param arrows, not the raw RHS result type. -/
  | letRecIn {tvs vs : List ValName} {Γ : Env}
      {binds : List Surface.Binding}
      {τs τrets : List Ty} {paramTysList : List (List Ty)} {ΓRhsList : List Env}
      {body : Surface.Expr} {τ : Ty}
      (hlen : binds.length = τs.length)
      (hrets : binds.length = τrets.length)
      (hparamLen : binds.length = paramTysList.length)
      (hΓRhsLen : binds.length = ΓRhsList.length)
      (hann : ∀ b ∈ binds, b.ann = (none : Option Surface.PolyTy))
      (hLL : ∀ (i : Nat) (hi : i < binds.length),
        LowerLetParams ke
          (letRhsTyScope (binds[i]'hi).tyParams (binds[i]'hi).params (none : Option Surface.PolyTy) tvs)
          (binds[i]'hi).params (τs.map PolyTy.mkTrivial ++ Γ)
          (ΓRhsList[i]'(Nat.lt_of_lt_of_eq hi hΓRhsLen))
          (paramTysList[i]'(Nat.lt_of_lt_of_eq hi hparamLen)))
      (hτbinds : ∀ (i : Nat) (hi : i < binds.length),
        coreParamsToArrows (paramTysList[i]'(Nat.lt_of_lt_of_eq hi hparamLen))
            (τrets[i]'(Nat.lt_of_lt_of_eq hi hrets)) =
          τs[i]'(Nat.lt_of_lt_of_eq hi hlen))
      (hrhs : ∀ (i : Nat) (hi : i < binds.length),
        SurfaceWTExpr ctors ke
          (letRhsTyScope (binds[i]'hi).tyParams (binds[i]'hi).params (none : Option Surface.PolyTy) tvs)
          (letRhsTermScope (binds[i]'hi).params (binds.map (·.name) ++ vs))
          (ΓRhsList[i]'(Nat.lt_of_lt_of_eq hi hΓRhsLen))
          (binds[i]'hi).rhs (τrets[i]'(Nat.lt_of_lt_of_eq hi hrets)))
      (hbody : SurfaceWTExpr ctors ke tvs (binds.map (·.name) ++ vs)
          (τs.map PolyTy.mkTrivial ++ Γ) body τ) :
      SurfaceWTExpr ctors ke tvs vs Γ (.letRecIn binds body) τ
  /-- Contract-stratified recursive checking. Ordinary members use the shared
      monotype opening while they are inferred. Completely annotated members
      are dependency cuts: after the ordinary members have been generalised,
      their RHSs are checked in the same final scheme environment as the body.
      Consequently only ordinary members depend on the shared pool opening;
      an annotated member depends solely on its own rigid opening.

      As for `letInAnn`, this structural bridge currently requires an empty
      ambient surface type-variable scope. The executable checker supports the
      broader scoped-annotation language independently of this sufficient rule. -/
  | letRecInAnn {tvs vs : List ValName} {Γ : Env}
      {binds : List Surface.Binding} {anns' : List (Option PolyTy)}
      {specs : List RecSpec} {G L : List Nat}
      {paramTysList : List Nat → List Nat → List (List Ty)}
      {ΓRhsList : List Nat → List Nat → List Env}
      {τretsList : List Nat → List Nat → List Ty}
      {body : Surface.Expr} {τ : Ty}
      (htvs : tvs = [])
      (hann : lowerAnnList ke (binds.map fun b =>
          finalizeAnn b.tyParams b.params b.ann) = some anns')
      (hlen : binds.length = specs.length)
      (hparamLen : ∀ Xs Ys, binds.length = (paramTysList Xs Ys).length)
      (hΓRhsLen : ∀ Xs Ys, binds.length = (ΓRhsList Xs Ys).length)
      (hretsLen : ∀ Xs Ys, binds.length = (τretsList Xs Ys).length)
      (hanns_eq : specs.map RecSpec.ann = anns')
      (hnodup : G.Nodup)
      (hmono_lc : ∀ τm, RecSpec.mono τm ∈ specs → τm.IsLC)
      (hpoly_wf : ∀ σ, RecSpec.poly σ ∈ specs → σ.WF)
      (hLLMono : ∀ (Xs : List Nat), FreshNames L G.length Xs →
        ∀ (i : Nat) (hi : i < binds.length) (τm : Ty),
          specs[i]'(Nat.lt_of_lt_of_eq hi hlen) = .mono τm →
        LowerLetParams ke
          (letRhsTyScope (binds[i]'hi).tyParams (binds[i]'hi).params (binds[i]'hi).ann tvs)
          (binds[i]'hi).params (specs.map (RecSpec.rhsEntry G Xs) ++ Γ)
          ((ΓRhsList Xs [])[i]'(Nat.lt_of_lt_of_eq hi (hΓRhsLen Xs [])))
          ((paramTysList Xs [])[i]'(Nat.lt_of_lt_of_eq hi (hparamLen Xs []))))
      (hLLPoly : ∀ (i : Nat) (hi : i < binds.length) (σ : PolyTy),
          specs[i]'(Nat.lt_of_lt_of_eq hi hlen) = .poly σ →
        ∀ (Ys : List Nat), FreshNames L σ.paramCount Ys →
        LowerLetParams ke
          (letRhsTyScope (binds[i]'hi).tyParams (binds[i]'hi).params (binds[i]'hi).ann tvs)
          (binds[i]'hi).params (specs.map (RecSpec.bodyScheme G) ++ Γ)
          ((ΓRhsList [] Ys)[i]'(Nat.lt_of_lt_of_eq hi (hΓRhsLen [] Ys)))
          ((paramTysList [] Ys)[i]'(Nat.lt_of_lt_of_eq hi (hparamLen [] Ys))))
      (hτbindsMono : ∀ (Xs : List Nat), FreshNames L G.length Xs →
        ∀ (i : Nat) (hi : i < binds.length) (τm : Ty),
          specs[i]'(Nat.lt_of_lt_of_eq hi hlen) = .mono τm →
          coreParamsToArrows ((paramTysList Xs [])[i]'(Nat.lt_of_lt_of_eq hi (hparamLen Xs [])))
              ((τretsList Xs [])[i]'(Nat.lt_of_lt_of_eq hi (hretsLen Xs []))) =
            Ty.renameG G Xs τm)
      (hτbindsPoly : ∀ (i : Nat) (hi : i < binds.length) (σ : PolyTy),
          specs[i]'(Nat.lt_of_lt_of_eq hi hlen) = .poly σ →
        ∀ (Ys : List Nat), FreshNames L σ.paramCount Ys →
          coreParamsToArrows ((paramTysList [] Ys)[i]'(Nat.lt_of_lt_of_eq hi (hparamLen [] Ys)))
              ((τretsList [] Ys)[i]'(Nat.lt_of_lt_of_eq hi (hretsLen [] Ys))) =
            σ.openVars Ys)
      (hmono : ∀ (Xs : List Nat), FreshNames L G.length Xs →
        ∀ (i : Nat) (hi : i < binds.length) (τm : Ty),
          specs[i]'(Nat.lt_of_lt_of_eq hi hlen) = .mono τm →
          SurfaceWTExpr ctors ke
            (letRhsTyScope (binds[i]'hi).tyParams (binds[i]'hi).params (binds[i]'hi).ann tvs)
            (letRhsTermScope (binds[i]'hi).params (binds.map (·.name) ++ vs))
            ((ΓRhsList Xs [])[i]'(Nat.lt_of_lt_of_eq hi (hΓRhsLen Xs [])))
            (binds[i]'hi).rhs ((τretsList Xs [])[i]'(Nat.lt_of_lt_of_eq hi (hretsLen Xs []))))
      (hpoly : ∀ (i : Nat) (hi : i < binds.length) (σ : PolyTy),
          specs[i]'(Nat.lt_of_lt_of_eq hi hlen) = .poly σ →
        ∀ (Ys : List Nat), FreshNames L σ.paramCount Ys →
          SurfaceWTExpr ctors ke
            (letRhsTyScope (binds[i]'hi).tyParams (binds[i]'hi).params (binds[i]'hi).ann tvs)
            (letRhsTermScope (binds[i]'hi).params (binds.map (·.name) ++ vs))
            ((ΓRhsList [] Ys)[i]'(Nat.lt_of_lt_of_eq hi (hΓRhsLen [] Ys)))
            (binds[i]'hi).rhs ((τretsList [] Ys)[i]'(Nat.lt_of_lt_of_eq hi (hretsLen [] Ys))))
      (hbody : SurfaceWTExpr ctors ke tvs (binds.map (·.name) ++ vs)
          (specs.map (RecSpec.bodyScheme G) ++ Γ) body τ) :
      SurfaceWTExpr ctors ke tvs vs Γ (.letRecIn binds body) τ
  | match_ {tvs vs : List ValName} {Γ : Env}
      {scrut : Surface.Expr} {brs : List (Surface.Pattern × Surface.Expr)}
      {T : TyName} {tyArgs : List Ty} {τres : Ty} :
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
  | ife {tvs vs : List ValName} {Γ : Env} {c t f : Surface.Expr} {τ : Ty} :
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
  ∃ (τ : Ty), SurfaceWTExpr ctors (kindEnvOfCtors ctors) [] [] [] s τ

/-- Weak (pre-1a) SurfaceWT, retained for the match-free uniqueness transfer. -/
def SurfaceWT_weak (ctors : CtorEnv) (s : Surface.Expr) : Prop :=
  ∃ c, CoreLowers ctors s c ∧ (coreTypecheck ctors c).isSome

/-- Match-free corollary: `SurfaceWT_weak` + `lowerCore` ⇒ `coreTypecheck`. -/
theorem typecheck_of_lower_of_SurfaceWT_of_NoMatch {ctors : CtorEnv} {s : Surface.Expr}
    {c : Expr}
    (hnm : SurfaceExprNoMatch s)
    (hwt : SurfaceWT_weak ctors s) (hlow : lowerCore ctors s = some c) :
    (coreTypecheck ctors c).isSome := by
  obtain ⟨c₀, hL, htc₀⟩ := hwt
  have heq : c₀ = c := by
    simp only [CoreLowers, lowerCore] at hL hlow
    exact lowerCoreExpr_eq_of_CoreLowersExpr_of_NoMatch hnm hL hlow
  simpa [heq] using htc₀

/-- Invert a `CoreLowers` derivation at surface `match_`. -/
theorem CoreLowersExpr_match_inv {ctors : CtorEnv} {ke : KindEnv} {tvs vs : List ValName}
    {scrut : Surface.Expr} {brs : List (Surface.Pattern × Surface.Expr)} {c : Expr}
    (h : CoreLowersExpr ctors ke tvs vs (.match_ scrut brs) c) :
    ∃ scrut' bodies',
      c = lowerMatch scrut' (brs.map Prod.fst) (bodyFn bodies') ∧
      CoreLowersExpr ctors ke tvs vs scrut scrut' ∧
      CoreLowersBranches ctors ke tvs vs brs bodies' := by
  cases h with
  | match_ hs hb =>
    exact ⟨_, _, rfl, hs, hb⟩

/-- From strong `SurfaceWT` of a match, the scrutinee is `SurfaceWT`. -/
theorem SurfaceWT_of_match_scrut {ctors : CtorEnv}
    {scrut : Surface.Expr} {brs : List (Surface.Pattern × Surface.Expr)}
    (hwt : SurfaceWT ctors (.match_ scrut brs)) : SurfaceWT ctors scrut := by
  obtain ⟨τ, hwt'⟩ := hwt
  cases hwt' with
  | match_ hscrut _ _ _ _ _ => exact ⟨_, hscrut⟩
  | of_lowers hnm _ _ => cases hnm


/-! ### Typing emitted decision trees

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
      (.var (env.idxOf b + depth)) τ := by
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
      simp only [List.length_nil, List.drop_zero, emitLets.go, emitLetsWith.go, coreEmissionOps] at hsum ⊢
      subst hsum
      have hw := TypeOfHM.weaken_env (env_pre := bindTys.map PolyTy.mkTrivial)
        (env_extra := Γ_env) (env := Γ_outer) hbody
      simpa only [List.length_map, hlen_binds, hlen_env, List.append_assoc] using hw
    | cons b rest ih =>
      simp only [emitLets.go, emitLetsWith.go, coreEmissionOps]
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
          (.var (env.idxOf b + k)) τb := by
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

/-- `emitCases` as a `List.map`. -/
private theorem emitCases_eq_map' (env : List Occ) (bodies : Nat → Expr) (occ : Occ) :
    ∀ (cases : List (CtorName × Nat × DTree)),
      emitCases env bodies occ cases
        = cases.map (fun x => (MatchPattern.named x.1 x.2.1,
            emit (subOccs occ x.2.1 ++ env) bodies x.2.2))
  | [] => rfl
  | (_c, _a, _t) :: rest => by
    change (MatchPattern.named _c _a, emit (subOccs occ _a ++ env) bodies _t)
      :: emitCases env bodies occ rest = _
    rw [emitCases_eq_map' env bodies occ rest, List.map_cons]

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
  | cons _ _ => simp [emitCases, emitCasesWith]

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

/-- Emitting a `DTreeTypeable` tree yields a
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
    simp only [emit, emitWith]
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
            convert hgoal using 1; first | rfl | simp [ectx', fieldTys, hlen_inst]
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

/-- Thread branch typings through `compile` on `initMatrix`, producing a
    `DTreeTypeable` tree whose leaves carry the corresponding body typings. -/
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

/-- Thread branch typings through `compile` on
    `initMatrix`, producing `DTreeTypeable` (which carries leaf body `TypeOfHM`).

    Root arity follows from global `CtorEnv.arityConsistent` together with
    `get? (kindEnvOfCtors ctors) T = some tyArgs.length`.
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


/-! ### Typing executable match lowering

The following lemmas type what `lowerCore` builds from the open ingredients carried
by `SurfaceWTExpr`. Coverage remains a separate closed property. -/

/-- **Rung 1.** Executable match lowering is exactly `lowerMatch` of lowered parts. -/
theorem lowerCoreExpr_match_decomp {ke : KindEnv} {tvs vs : List ValName}
    {scrut : Surface.Expr} {brs : List (Surface.Pattern × Surface.Expr)} {c : Expr}
    (hlow : lowerCoreExpr ke tvs vs (.match_ scrut brs) = some c) :
    ∃ scrut' bodies',
      lowerCoreExpr ke tvs vs scrut = some scrut' ∧
      lowerCoreBranches ke tvs vs brs = some bodies' ∧
      c = lowerMatch scrut' (brs.map Prod.fst) (bodyFn bodies') := by
  simp only [lowerCoreExpr_eqs] at hlow
  cases hs : lowerCoreExpr ke tvs vs scrut with
  | none => simp [hs] at hlow
  | some scrut' =>
    cases hb : lowerCoreBranches ke tvs vs brs with
    | none => simp [hs, hb] at hlow
    | some bodies' =>
      simp only [hs, hb, Option.some.injEq] at hlow
      refine ⟨scrut', bodies', rfl, rfl, ?_⟩
      have hfn : (fun i => bodies'.getD i (.ctor cNil)) = bodyFn bodies' := by
        funext i; simp [bodyFn, matchBodyDefault]
      rw [← hfn, hlow]


/-- **Rung 1b.** Executable letRec lowering is exactly `letRec` of lowered parts. -/
theorem lowerCoreExpr_letRecIn_decomp {ke : KindEnv} {tvs vs : List ValName}
    {binds : List Surface.Binding} {body : Surface.Expr} {c : Expr}
    (hlow : lowerCoreExpr ke tvs vs (.letRecIn binds body) = some c) :
    ∃ bindings' body',
      lowerCoreRecBinds ke tvs (binds.map (·.name) ++ vs) binds = some bindings' ∧
      lowerCoreExpr ke tvs (binds.map (·.name) ++ vs) body = some body' ∧
      c = Expr.letRec bindings' body' := by
  simp only [lowerCoreExpr_eqs] at hlow
  cases hbinds : lowerCoreRecBinds ke tvs (binds.map (·.name) ++ vs) binds with
  | none => simp [hbinds] at hlow
  | some bindings' =>
    cases hb : lowerCoreExpr ke tvs (binds.map (·.name) ++ vs) body with
    | none => simp [hbinds, hb] at hlow
    | some body' =>
      simp only [hbinds, hb, Option.some.injEq] at hlow
      exact ⟨bindings', body', rfl, rfl, hlow.symm⟩

/-- **Rung 1c.** Executable letIn lowering is exactly `letIn` of lowered/wrapped parts. -/
theorem lowerCoreExpr_letIn_decomp {ke : KindEnv} {tvs vs : List ValName}
    {name : ValName} {tyParams : List ValName}
    {params : List (ValName × Option Surface.Ty)} {ann : Option Surface.PolyTy}
    {rhs body : Surface.Expr} {c : Expr}
    (hlow : lowerCoreExpr ke tvs vs (.letIn name tyParams params ann rhs body) = some c) :
    ∃ ann' rhsCore rhs' body',
      lowerPolyAnnIn ke tvs (finalizeAnn tyParams params ann) = some ann' ∧
      lowerCoreExpr ke (letRhsTyScope tyParams params ann tvs)
        (letRhsTermScope params vs) rhs = some rhsCore ∧
      wrapCoreParams ke (letRhsTyScope tyParams params ann tvs) params rhsCore = some rhs' ∧
      lowerCoreExpr ke tvs (name :: vs) body = some body' ∧
      c = Expr.letIn ann' rhs' body' := by
  simp only [lowerCoreExpr_eqs] at hlow
  cases hann : lowerPolyAnnIn ke tvs (finalizeAnn tyParams params ann) with
  | none => simp [hann] at hlow
  | some ann' =>
    cases hr : lowerCoreExpr ke (letAnnTyPrefix tyParams (finalizeAnn tyParams params ann) ++ tvs)
        (paramTermScope params vs) rhs with
    | none => simp [hann, hr] at hlow
    | some rhsCore =>
      cases hwrap : wrapCoreParams ke
          (letAnnTyPrefix tyParams (finalizeAnn tyParams params ann) ++ tvs) params rhsCore with
      | none => simp [hann, hr, hwrap] at hlow
      | some rhs' =>
        cases hb : lowerCoreExpr ke tvs (name :: vs) body with
        | none => simp [hann, hr, hwrap, hb] at hlow
        | some body' =>
          simp only [hann, hr, hwrap, hb, Option.some.injEq] at hlow
          refine ⟨ann', rhsCore, rhs', body', rfl, ?_, ?_, rfl, hlow.symm⟩
          · simpa [letRhsTyScope, letRhsTermScope] using hr
          · simpa [letRhsTyScope] using hwrap

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

private theorem lowerCoreBranches_length {ke : KindEnv} {tvs vs : List ValName}
    {brs : List (Surface.Pattern × Surface.Expr)} {bodies : List Expr}
    (h : lowerCoreBranches ke tvs vs brs = some bodies) :
    bodies.length = brs.length := by
  induction brs generalizing bodies with
  | nil =>
    simp only [lowerCoreBranches_eqs, Option.some.injEq] at h; subst h; rfl
  | cons hd tl ih =>
    rw [lowerCoreBranches_eq] at h
    cases hb : lowerCoreExpr ke tvs (patVars hd.1 ++ vs) hd.2 with
    | none => simp [hb] at h
    | some b' =>
      cases hrest : lowerCoreBranches ke tvs vs tl with
      | none => simp [hb, hrest] at h
      | some rest' =>
        simp only [hb, hrest, Option.some.injEq] at h; subst h
        simp [ih hrest]

private theorem lowerCoreBranches_get {ke : KindEnv} {tvs vs : List ValName}
    {brs : List (Surface.Pattern × Surface.Expr)} {bodies : List Expr}
    (h : lowerCoreBranches ke tvs vs brs = some bodies) :
    ∀ (i : Nat) (hi : i < brs.length),
      lowerCoreExpr ke tvs (patVars (brs[i]'hi).1 ++ vs) (brs[i]'hi).2 =
        some (bodies[i]'(by simpa [lowerCoreBranches_length h] using hi)) := by
  induction brs generalizing bodies with
  | nil => intro i hi; cases hi
  | cons hd tl ih =>
    rw [lowerCoreBranches_eq] at h
    cases hb : lowerCoreExpr ke tvs (patVars hd.1 ++ vs) hd.2 with
    | none => simp [hb] at h
    | some b' =>
      cases hrest : lowerCoreBranches ke tvs vs tl with
      | none => simp [hb, hrest] at h
      | some rest' =>
        simp only [hb, hrest, Option.some.injEq] at h; subst h
        intro i hi
        match i with
        | 0 => simpa using hb
        | i' + 1 =>
          have hi' : i' < tl.length := Nat.lt_of_succ_lt_succ hi
          simpa using ih hrest i' hi'

private theorem lowerCoreExprList_length_get {ke : KindEnv} {tvs vs : List ValName}
    {items : List Surface.Expr} {items' : List Expr}
    (h : lowerCoreExprList ke tvs vs items = some items') :
    items'.length = items.length ∧
      ∀ (i : Nat) (hi : i < items.length),
        ∃ hi' : i < items'.length,
          lowerCoreExpr ke tvs vs (items[i]'hi) = some (items'[i]'hi') := by
  induction items generalizing items' with
  | nil =>
    simp only [lowerCoreExprList_eqs, Option.some.injEq] at h; subst h
    exact ⟨rfl, fun i hi => by cases hi⟩
  | cons hd tl ih =>
    simp only [lowerCoreExprList_eqs] at h
    cases he : lowerCoreExpr ke tvs vs hd with
    | none => simp [he] at h
    | some e' =>
      cases hrest : lowerCoreExprList ke tvs vs tl with
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

private theorem lowerCoreBranches_isSome_of_forall {ke : KindEnv} {tvs vs : List ValName}
    {brs : List (Surface.Pattern × Surface.Expr)}
    (h : ∀ (i : Nat) (hi : i < brs.length),
      (lowerCoreExpr ke tvs (patVars (brs[i]'hi).1 ++ vs) (brs[i]'hi).2).isSome) :
    (lowerCoreBranches ke tvs vs brs).isSome := by
  induction brs with
  | nil => simp [lowerCoreBranches_eqs]
  | cons hd tl ih =>
    rw [lowerCoreBranches_eq]
    have hhd := h 0 (by simp)
    simp only [List.getElem_cons_zero] at hhd
    obtain ⟨b', hhd'⟩ := Option.isSome_iff_exists.mp hhd
    have htl := ih fun i hi => by
      simpa [List.getElem_cons_succ] using h (i + 1) (Nat.succ_lt_succ hi)
    obtain ⟨rest', htl'⟩ := Option.isSome_iff_exists.mp htl
    simp [hhd', htl']

private theorem lowerCoreExprList_isSome_of_forall {ke : KindEnv} {tvs vs : List ValName}
    {items : List Surface.Expr}
    (h : ∀ e ∈ items, (lowerCoreExpr ke tvs vs e).isSome) :
    (lowerCoreExprList ke tvs vs items).isSome := by
  induction items with
  | nil => simp [lowerCoreExprList_eqs]
  | cons hd tl ih =>
    simp only [lowerCoreExprList_eqs]
    obtain ⟨_, hhd⟩ := Option.isSome_iff_exists.mp (h hd List.mem_cons_self)
    obtain ⟨_, htl⟩ := Option.isSome_iff_exists.mp
      (ih fun e he => h e (List.mem_cons_of_mem _ he))
    simp [hhd, htl]

private theorem tvarIndex_mem_of_some {tvs : List ValName} {n : ValName} {i : Nat}
    (h : tvarIndex tvs n = some i) : n ∈ tvs := by
  induction tvs generalizing n i with
  | nil => simp [tvarIndex] at h
  | cons x xs ih =>
    simp only [tvarIndex] at h
    by_cases hx : x = n
    · simp [hx, List.mem_cons]
    · simp [hx, Option.map] at h
      cases hi : tvarIndex xs n with
      | none => simp [hi] at h
      | some j =>
        simp [hi, Option.some.injEq] at h; subst h
        exact List.mem_cons_of_mem x (ih hi)

private theorem tvarIndex_isSome_of_mem {tvs : List ValName} {n : ValName}
    (h : n ∈ tvs) : (tvarIndex tvs n).isSome := by
  induction tvs with
  | nil => cases h
  | cons x xs ih =>
    by_cases hx : x = n
    · subst hx; simp [tvarIndex]
    · have hn : n ∈ xs := (List.mem_cons.mp h).resolve_left (Ne.symm hx)
      simp [tvarIndex, hx, ih hn]

private theorem lowerTyList_length_of_some {ke : KindEnv} {tvs : List ValName}
    {ss : List Surface.Ty} {ts : List Ty}
    (h : lowerTyList ke tvs ss = some ts) : ts.length = ss.length := by
  induction ss generalizing ts with
  | nil => simp [lowerTyList] at h; cases h; rfl
  | cons s ss ih =>
    simp only [lowerTyList] at h
    cases ht : lowerTy ke tvs s with
    | none => simp [ht] at h
    | some t' =>
      cases hts : lowerTyList ke tvs ss with
      | none => simp [hts] at h
      | some ts' =>
        simp only [ht, hts] at h
        cases h
        simp
        exact ih hts

private theorem lowerTyList_isSome_appendTyScope_aux {ke : KindEnv} {tvs tvs' : List ValName}
    {ss : List Surface.Ty}
    (h : ∀ t ∈ ss, (lowerTy ke tvs t).isSome → (lowerTy ke (tvs' ++ tvs) t).isSome)
    (hss : (lowerTyList ke tvs ss).isSome) :
    (lowerTyList ke (tvs' ++ tvs) ss).isSome := by
  induction ss with
  | nil => simp [lowerTyList] at hss ⊢
  | cons s ss ih =>
    simp only [lowerTyList] at hss ⊢
    cases hs : lowerTy ke tvs s with
    | none => simp [hs] at hss
    | some s' =>
      cases htail : lowerTyList ke tvs ss with
      | none => simp [htail] at hss
      | some ss' =>
        have hs' := h s List.mem_cons_self (Option.isSome_iff_exists.mpr ⟨s', hs⟩)
        have htail' := ih (fun t ht hIs => h t (List.mem_cons_of_mem s ht) hIs)
          (Option.isSome_iff_exists.mpr ⟨ss', htail⟩)
        obtain ⟨_, hs''⟩ := Option.isSome_iff_exists.mp hs'
        obtain ⟨_, htail''⟩ := Option.isSome_iff_exists.mp htail'
        simp [hs'', htail'', Option.isSome_some]

private theorem lowerTyList_isSome_appendTyScopeMid_aux {ke : KindEnv} {A tvs' B : List ValName}
    {ss : List Surface.Ty}
    (h : ∀ t ∈ ss, (lowerTy ke (A ++ B) t).isSome → (lowerTy ke (A ++ tvs' ++ B) t).isSome)
    (hss : (lowerTyList ke (A ++ B) ss).isSome) :
    (lowerTyList ke (A ++ tvs' ++ B) ss).isSome := by
  induction ss with
  | nil => simp [lowerTyList] at hss ⊢
  | cons s ss ih =>
    simp only [lowerTyList] at hss ⊢
    cases hs : lowerTy ke (A ++ B) s with
    | none => simp [hs] at hss
    | some s' =>
      cases htail : lowerTyList ke (A ++ B) ss with
      | none => simp [htail] at hss
      | some ss' =>
        have hs' := h s List.mem_cons_self (Option.isSome_iff_exists.mpr ⟨s', hs⟩)
        have htail' := ih (fun t ht hIs => h t (List.mem_cons_of_mem s ht) hIs)
          (Option.isSome_iff_exists.mpr ⟨ss', htail⟩)
        obtain ⟨_, hs''⟩ := Option.isSome_iff_exists.mp hs'
        obtain ⟨_, htail''⟩ := Option.isSome_iff_exists.mp htail'
        have hs''' := show lowerTy ke (A ++ (tvs' ++ B)) s = _ from (List.append_assoc A tvs' B).symm ▸ hs''
        have htail''' := show lowerTyList ke (A ++ (tvs' ++ B)) ss = _ from (List.append_assoc A tvs' B).symm ▸ htail''
        simp [hs''', htail''', Option.isSome_some]

private theorem lowerCoreExprList_isSome_appendTyScope_aux {ke : KindEnv} {tvs vs tvs' : List ValName}
    {items : List Surface.Expr}
    (h : ∀ e ∈ items, (lowerCoreExpr ke tvs vs e).isSome → (lowerCoreExpr ke (tvs' ++ tvs) vs e).isSome)
    (hitems : (lowerCoreExprList ke tvs vs items).isSome) :
    (lowerCoreExprList ke (tvs' ++ tvs) vs items).isSome := by
  induction items with
  | nil => simp [lowerCoreExprList_eqs] at hitems ⊢
  | cons e es ih =>
    simp only [lowerCoreExprList_eqs] at hitems ⊢
    cases he : lowerCoreExpr ke tvs vs e with
    | none => simp [he] at hitems
    | some e' =>
      cases hes : lowerCoreExprList ke tvs vs es with
      | none => simp [hes] at hitems
      | some es' =>
        have he' := h e List.mem_cons_self (Option.isSome_iff_exists.mpr ⟨e', he⟩)
        have hes' := ih (fun e' he' hIs => h e' (List.mem_cons_of_mem e he') hIs)
          (Option.isSome_iff_exists.mpr ⟨es', hes⟩)
        obtain ⟨_, he''⟩ := Option.isSome_iff_exists.mp he'
        obtain ⟨_, hes''⟩ := Option.isSome_iff_exists.mp hes'
        simp [he'', hes'', Option.isSome_some]

private theorem lowerCoreExprList_isSome_appendTyScopeMid_aux {ke : KindEnv} {A tvs' B vs : List ValName}
    {items : List Surface.Expr}
    (h : ∀ e ∈ items, (lowerCoreExpr ke (A ++ B) vs e).isSome → (lowerCoreExpr ke (A ++ tvs' ++ B) vs e).isSome)
    (hitems : (lowerCoreExprList ke (A ++ B) vs items).isSome) :
    (lowerCoreExprList ke (A ++ tvs' ++ B) vs items).isSome := by
  induction items with
  | nil => simp [lowerCoreExprList_eqs] at hitems ⊢
  | cons e es ih =>
    simp only [lowerCoreExprList_eqs] at hitems ⊢
    cases he : lowerCoreExpr ke (A ++ B) vs e with
    | none => simp [he] at hitems
    | some e' =>
      cases hes : lowerCoreExprList ke (A ++ B) vs es with
      | none => simp [hes] at hitems
      | some es' =>
        have he' := h e List.mem_cons_self (Option.isSome_iff_exists.mpr ⟨e', he⟩)
        have hes' := ih (fun e' he' hIs => h e' (List.mem_cons_of_mem e he') hIs)
          (Option.isSome_iff_exists.mpr ⟨es', hes⟩)
        obtain ⟨_, he''⟩ := Option.isSome_iff_exists.mp he'
        obtain ⟨_, hes''⟩ := Option.isSome_iff_exists.mp hes'
        have he''' := show lowerCoreExpr ke (A ++ (tvs' ++ B)) vs e = _ from (List.append_assoc A tvs' B).symm ▸ he''
        have hes''' := show lowerCoreExprList ke (A ++ (tvs' ++ B)) vs es = _ from (List.append_assoc A tvs' B).symm ▸ hes''
        simp [he''', hes''', Option.isSome_some]

private theorem lowerCoreBranches_isSome_appendTyScope_aux {ke : KindEnv} {tvs vs tvs' : List ValName}
    {brs : List (Surface.Pattern × Surface.Expr)}
    (hBody :
      ∀ (p : Surface.Pattern) (b : Surface.Expr),
        (p, b) ∈ brs →
          (lowerCoreExpr ke tvs (patVars p ++ vs) b).isSome →
            (lowerCoreExpr ke (tvs' ++ tvs) (patVars p ++ vs) b).isSome)
    (hbrs : (lowerCoreBranches ke tvs vs brs).isSome) :
    (lowerCoreBranches ke (tvs' ++ tvs) vs brs).isSome := by
  induction brs with
  | nil => simp [lowerCoreBranches_eqs] at hbrs ⊢
  | cons hd tl ih =>
    rcases hd with ⟨p, b⟩
    simp only [lowerCoreBranches_eqs] at hbrs ⊢
    cases hb : lowerCoreExpr ke tvs (patVars p ++ vs) b with
    | none => simp [hb] at hbrs
    | some b' =>
      cases hrest : lowerCoreBranches ke tvs vs tl with
      | none => simp [hrest] at hbrs
      | some rest' =>
        have hb' := hBody p b List.mem_cons_self (Option.isSome_iff_exists.mpr ⟨b', hb⟩)
        have hrest' := ih (fun p' b' hb' hIs => hBody p' b' (List.mem_cons_of_mem _ hb') hIs)
          (Option.isSome_iff_exists.mpr ⟨rest', hrest⟩)
        obtain ⟨_, hb''⟩ := Option.isSome_iff_exists.mp hb'
        obtain ⟨_, hrest''⟩ := Option.isSome_iff_exists.mp hrest'
        simp [hb'', hrest'', Option.isSome_some]

private theorem lowerCoreBranches_isSome_appendTyScopeMid_aux {ke : KindEnv} {A tvs' B vs : List ValName}
    {brs : List (Surface.Pattern × Surface.Expr)}
    (hBody :
      ∀ (p : Surface.Pattern) (b : Surface.Expr),
        (p, b) ∈ brs →
          (lowerCoreExpr ke (A ++ B) (patVars p ++ vs) b).isSome →
            (lowerCoreExpr ke (A ++ tvs' ++ B) (patVars p ++ vs) b).isSome)
    (hbrs : (lowerCoreBranches ke (A ++ B) vs brs).isSome) :
    (lowerCoreBranches ke (A ++ tvs' ++ B) vs brs).isSome := by
  induction brs with
  | nil => simp [lowerCoreBranches_eqs] at hbrs ⊢
  | cons hd tl ih =>
    rcases hd with ⟨p, b⟩
    simp only [lowerCoreBranches_eqs] at hbrs ⊢
    cases hb : lowerCoreExpr ke (A ++ B) (patVars p ++ vs) b with
    | none => simp [hb] at hbrs
    | some b' =>
      cases hrest : lowerCoreBranches ke (A ++ B) vs tl with
      | none => simp [hrest] at hbrs
      | some rest' =>
        have hb' := hBody p b List.mem_cons_self (Option.isSome_iff_exists.mpr ⟨b', hb⟩)
        have hrest' := ih (fun p' b' hb' hIs => hBody p' b' (List.mem_cons_of_mem _ hb') hIs)
          (Option.isSome_iff_exists.mpr ⟨rest', hrest⟩)
        obtain ⟨_, hb''⟩ := Option.isSome_iff_exists.mp hb'
        obtain ⟨_, hrest''⟩ := Option.isSome_iff_exists.mp hrest'
        have hb''' := show lowerCoreExpr ke (A ++ (tvs' ++ B)) (patVars p ++ vs) b = _ from (List.append_assoc A tvs' B).symm ▸ hb''
        have hrest''' := show lowerCoreBranches ke (A ++ (tvs' ++ B)) vs tl = _ from (List.append_assoc A tvs' B).symm ▸ hrest''
        simp [hb''', hrest''', Option.isSome_some]

theorem lowerTy_isSome_appendTyScope {ke : KindEnv} {tvs tvs' : List ValName}
    {τ : Surface.Ty} (h : (lowerTy ke tvs τ).isSome) :
    (lowerTy ke (tvs' ++ tvs) τ).isSome := by
  revert h
  induction τ using Surface.Ty.rec_strong with
  | hole | namedHole => simp [lowerTy]
  | prim p =>
    intro h
    cases p with
    | unit | int | nat | char => simp [lowerTy]
    | bool => simp [lowerTy] at h ⊢; exact h
  | arrow a b iha ihb =>
    intro h
    simp only [lowerTy] at h
    cases ha : lowerTy ke tvs a with
    | none => simp [ha] at h
    | some a' =>
      cases hb : lowerTy ke tvs b with
      | none => simp [hb] at h
      | some b' =>
        have ha' := iha (Option.isSome_iff_exists.mpr ⟨a', ha⟩)
        have hb' := ihb (Option.isSome_iff_exists.mpr ⟨b', hb⟩)
        obtain ⟨_, ha''⟩ := Option.isSome_iff_exists.mp ha'
        obtain ⟨_, hb''⟩ := Option.isSome_iff_exists.mp hb'
        simp only [lowerTy, ha'', hb'', Option.isSome_some]
  | pair a b iha ihb =>
    intro h
    simp only [lowerTy] at h
    cases ha : lowerTy ke tvs a with
    | none => simp [ha] at h
    | some a' =>
      cases hb : lowerTy ke tvs b with
      | none => simp [hb] at h
      | some b' =>
        simp only [ha, hb] at h
        split at h
        · rename_i hg
          have ha' := iha (Option.isSome_iff_exists.mpr ⟨a', ha⟩)
          have hb' := ihb (Option.isSome_iff_exists.mpr ⟨b', hb⟩)
          obtain ⟨_, ha''⟩ := Option.isSome_iff_exists.mp ha'
          obtain ⟨_, hb''⟩ := Option.isSome_iff_exists.mp hb'
          simp only [lowerTy, ha'', hb'', hg, ↓reduceIte, Option.isSome_some]
        · simp at h
  | tvar name =>
    intro h
    simp only [lowerTy] at h ⊢
    cases hi : tvarIndex tvs name with
    | none => simp [hi] at h
    | some i =>
      cases hi' : tvarIndex (tvs' ++ tvs) name with
      | none =>
        exfalso
        have hn : name ∈ tvs' ++ tvs := List.mem_append_right _ (tvarIndex_mem_of_some hi)
        obtain ⟨j, hj⟩ := Option.isSome_iff_exists.mp (tvarIndex_isSome_of_mem hn)
        exact Option.noConfusion (hi'.symm.trans hj)
      | some j => simp [Option.isSome_some]
  | customTy T args ih =>
    intro h
    simp only [lowerTy] at h
    cases hargs : lowerTyList ke tvs args with
    | none => simp [hargs] at h
    | some tyArgs' =>
      simp only [hargs] at h
      split at h
      · rename_i hg
        have hargs' := lowerTyList_isSome_appendTyScope_aux
          (fun t ht hIs => ih t ht hIs)
          (Option.isSome_iff_exists.mpr ⟨tyArgs', hargs⟩)
        obtain ⟨w, hlowered⟩ := Option.isSome_iff_exists.mp hargs'
        have hlen : w.length = tyArgs'.length :=
          (lowerTyList_length_of_some hlowered).trans (lowerTyList_length_of_some hargs).symm
        simp only [lowerTy, hlowered, hg, hlen, ↓reduceIte, Option.isSome_some]
      · simp at h

theorem lowerTy_isSome_appendTyScopeMid {ke : KindEnv} {A tvs' B : List ValName}
    {τ : Surface.Ty} (h : (lowerTy ke (A ++ B) τ).isSome) :
    (lowerTy ke (A ++ tvs' ++ B) τ).isSome := by
  revert h
  induction τ using Surface.Ty.rec_strong with
  | hole | namedHole => simp [lowerTy]
  | prim p =>
    intro h
    cases p with
    | unit | int | nat | char => simp [lowerTy]
    | bool => simp [lowerTy] at h ⊢; exact h
  | arrow a b iha ihb =>
    intro h
    simp only [lowerTy] at h
    cases ha : lowerTy ke (A ++ B) a with
    | none => simp [ha] at h
    | some a' =>
      cases hb : lowerTy ke (A ++ B) b with
      | none => simp [hb] at h
      | some b' =>
        have ha' := iha (Option.isSome_iff_exists.mpr ⟨a', ha⟩)
        have hb' := ihb (Option.isSome_iff_exists.mpr ⟨b', hb⟩)
        obtain ⟨_, ha''⟩ := Option.isSome_iff_exists.mp ha'
        obtain ⟨_, hb''⟩ := Option.isSome_iff_exists.mp hb'
        simp only [lowerTy, ha'', hb'', Option.isSome_some]
  | pair a b iha ihb =>
    intro h
    simp only [lowerTy] at h
    cases ha : lowerTy ke (A ++ B) a with
    | none => simp [ha] at h
    | some a' =>
      cases hb : lowerTy ke (A ++ B) b with
      | none => simp [hb] at h
      | some b' =>
        simp only [ha, hb] at h
        split at h
        · rename_i hg
          have ha' := iha (Option.isSome_iff_exists.mpr ⟨a', ha⟩)
          have hb' := ihb (Option.isSome_iff_exists.mpr ⟨b', hb⟩)
          obtain ⟨_, ha''⟩ := Option.isSome_iff_exists.mp ha'
          obtain ⟨_, hb''⟩ := Option.isSome_iff_exists.mp hb'
          simp only [lowerTy, ha'', hb'', hg, ↓reduceIte, Option.isSome_some]
        · simp at h
  | tvar name =>
    intro h
    simp only [lowerTy] at h ⊢
    cases hi : tvarIndex (A ++ B) name with
    | none => simp [hi] at h
    | some i =>
      cases hi' : tvarIndex (A ++ tvs' ++ B) name with
      | none =>
        exfalso
        have hn : name ∈ (A ++ tvs') ++ B := by
          rcases (List.mem_append.mp (tvarIndex_mem_of_some hi)) with ha | hb
          · exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl ha)))
          · exact List.mem_append.mpr (Or.inr hb)
        obtain ⟨j, hj⟩ := Option.isSome_iff_exists.mp (tvarIndex_isSome_of_mem hn)
        exact Option.noConfusion (hi'.symm.trans hj)
      | some j => simp [Option.isSome_some]
  | customTy T args ih =>
    intro h
    simp only [lowerTy] at h
    cases hargs : lowerTyList ke (A ++ B) args with
    | none => simp [hargs] at h
    | some tyArgs' =>
      simp only [hargs] at h
      split at h
      · rename_i hg
        have hargs' := lowerTyList_isSome_appendTyScopeMid_aux
          (fun t ht hIs => ih t ht hIs)
          (Option.isSome_iff_exists.mpr ⟨tyArgs', hargs⟩)
        obtain ⟨w, hlowered⟩ := Option.isSome_iff_exists.mp hargs'
        have hlen : w.length = tyArgs'.length :=
          (lowerTyList_length_of_some hlowered).trans (lowerTyList_length_of_some hargs).symm
        simp only [lowerTy, hlowered, hg, hlen, ↓reduceIte, Option.isSome_some]
      · simp at h

private theorem wrapCoreParams_isSome_invariant {ke : KindEnv} {tvs : List ValName}
    {params : List (ValName × Option Surface.Ty)} {e e' : Expr}
    (h : (wrapCoreParams ke tvs params e).isSome) :
    (wrapCoreParams ke tvs params e').isSome := by
  revert e e'
  induction params with
  | nil => intro e e' _; simp [wrapCoreParams]
  | cons p rest ih =>
    intro e e' h
    simp only [wrapCoreParams] at h ⊢
    cases hrest : wrapCoreParams ke tvs rest e with
    | none => simp [hrest] at h
    | some e'' =>
      cases hann : lowerAnn ke tvs p.2 with
      | none => simp [hann, hrest] at h
      | some ann' =>
        have hrest' := ih (e' := e') (Option.isSome_iff_exists.mpr ⟨e'', hrest⟩)
        cases hrest'' : wrapCoreParams ke tvs rest e' with
        | none =>
          exfalso
          simp [hrest''] at hrest'
        | some _ =>
          simp only [Option.isSome_some]

private theorem lowerAnn_isSome_appendTyScope {ke : KindEnv} {tvs tvs' : List ValName}
    {ann : Option Surface.Ty} (h : (lowerAnn ke tvs ann).isSome) :
    (lowerAnn ke (tvs' ++ tvs) ann).isSome := by
  cases ann with
  | none => simp [lowerAnn] at h ⊢
  | some τ =>
    simp only [lowerAnn] at h ⊢
    cases ht : lowerTy ke tvs τ with
    | none => simp [ht] at h
    | some t' =>
      have ht' := lowerTy_isSome_appendTyScope (tvs' := tvs')
        (Option.isSome_iff_exists.mpr ⟨t', ht⟩)
      obtain ⟨t'', ht''⟩ := Option.isSome_iff_exists.mp ht'
      simp only [ht'', Option.map, Option.isSome_some]

private theorem lowerAnn_isSome_appendTyScopeMid {ke : KindEnv} {A tvs' B : List ValName}
    {ann : Option Surface.Ty} (h : (lowerAnn ke (A ++ B) ann).isSome) :
    (lowerAnn ke (A ++ tvs' ++ B) ann).isSome := by
  cases ann with
  | none => simp [lowerAnn] at h ⊢
  | some τ =>
    simp only [lowerAnn] at h ⊢
    cases ht : lowerTy ke (A ++ B) τ with
    | none => simp [ht] at h
    | some t' =>
      have ht' := lowerTy_isSome_appendTyScopeMid (A := A) (tvs' := tvs') (B := B)
        (Option.isSome_iff_exists.mpr ⟨t', ht⟩)
      obtain ⟨t'', ht''⟩ := Option.isSome_iff_exists.mp ht'
      simp only [ht'', Option.map, Option.isSome_some]

private theorem lowerPolyAnnIn_isSome_appendTyScope {ke : KindEnv}
    {tvs tvs' : List ValName} {ann : Option Surface.PolyTy}
    (h : (lowerPolyAnnIn ke tvs ann).isSome) :
    (lowerPolyAnnIn ke (tvs' ++ tvs) ann).isSome := by
  cases ann with
  | none => simp [lowerPolyAnnIn]
  | some σ =>
    simp only [lowerPolyAnnIn, lowerPolyIn] at h ⊢
    cases ht : lowerTy ke (σ.foralls.eraseDups ++ tvs) σ.body with
    | none => simp [ht] at h
    | some t =>
      have ht' := lowerTy_isSome_appendTyScopeMid
        (A := σ.foralls.eraseDups) (tvs' := tvs') (B := tvs)
        (Option.isSome_iff_exists.mpr ⟨t, ht⟩)
      obtain ⟨t', ht'⟩ := Option.isSome_iff_exists.mp ht'
      rw [show σ.foralls.eraseDups ++ (tvs' ++ tvs) =
          σ.foralls.eraseDups ++ tvs' ++ tvs by simp only [List.append_assoc], ht']
      rfl

private theorem lowerPolyAnnIn_isSome_appendTyScopeMid {ke : KindEnv}
    {A tvs' B : List ValName} {ann : Option Surface.PolyTy}
    (h : (lowerPolyAnnIn ke (A ++ B) ann).isSome) :
    (lowerPolyAnnIn ke (A ++ tvs' ++ B) ann).isSome := by
  cases ann with
  | none => simp [lowerPolyAnnIn]
  | some σ =>
    simp only [lowerPolyAnnIn, lowerPolyIn] at h ⊢
    cases ht : lowerTy ke (σ.foralls.eraseDups ++ (A ++ B)) σ.body with
    | none => simp [ht] at h
    | some t =>
      have htAt : lowerTy ke ((σ.foralls.eraseDups ++ A) ++ B) σ.body = some t := by
        simpa only [List.append_assoc] using ht
      have ht' := lowerTy_isSome_appendTyScopeMid
        (A := σ.foralls.eraseDups ++ A) (tvs' := tvs') (B := B)
        (Option.isSome_iff_exists.mpr ⟨t, htAt⟩)
      obtain ⟨t', ht'⟩ := Option.isSome_iff_exists.mp ht'
      have htGoal : lowerTy ke (σ.foralls.eraseDups ++ (A ++ tvs' ++ B)) σ.body = some t' := by
        simpa only [List.append_assoc] using ht'
      rw [htGoal]
      rfl

private theorem lowerAnnListIn_isSome_appendTyScope {ke : KindEnv}
    {tvs tvs' : List ValName} {anns : List (Option Surface.PolyTy)}
    (h : (lowerAnnListIn ke tvs anns).isSome) :
    (lowerAnnListIn ke (tvs' ++ tvs) anns).isSome := by
  induction anns with
  | nil => simp [lowerAnnListIn]
  | cons ann anns ih =>
    simp only [lowerAnnListIn] at h ⊢
    cases ha : lowerPolyAnnIn ke tvs ann with
    | none => simp [ha] at h
    | some ann' =>
      cases has : lowerAnnListIn ke tvs anns with
      | none => simp [ha, has] at h
      | some anns' =>
        have ha' := lowerPolyAnnIn_isSome_appendTyScope (tvs' := tvs')
          (Option.isSome_iff_exists.mpr ⟨ann', ha⟩)
        have has' := ih (Option.isSome_iff_exists.mpr ⟨anns', has⟩)
        obtain ⟨_, ha''⟩ := Option.isSome_iff_exists.mp ha'
        obtain ⟨_, has''⟩ := Option.isSome_iff_exists.mp has'
        simp [ha'', has'']

private theorem lowerAnnListIn_isSome_appendTyScopeMid {ke : KindEnv}
    {A tvs' B : List ValName} {anns : List (Option Surface.PolyTy)}
    (h : (lowerAnnListIn ke (A ++ B) anns).isSome) :
    (lowerAnnListIn ke (A ++ tvs' ++ B) anns).isSome := by
  induction anns with
  | nil => simp [lowerAnnListIn]
  | cons ann anns ih =>
    simp only [lowerAnnListIn] at h ⊢
    cases ha : lowerPolyAnnIn ke (A ++ B) ann with
    | none => simp [ha] at h
    | some ann' =>
      cases has : lowerAnnListIn ke (A ++ B) anns with
      | none => simp [ha, has] at h
      | some anns' =>
        have ha' := lowerPolyAnnIn_isSome_appendTyScopeMid
          (A := A) (tvs' := tvs') (B := B)
          (Option.isSome_iff_exists.mpr ⟨ann', ha⟩)
        have has' := ih (Option.isSome_iff_exists.mpr ⟨anns', has⟩)
        obtain ⟨ann'', ha''⟩ := Option.isSome_iff_exists.mp ha'
        obtain ⟨anns'', has''⟩ := Option.isSome_iff_exists.mp has'
        have haGoal : lowerPolyAnnIn ke (A ++ (tvs' ++ B)) ann = some ann'' := by
          simpa only [List.append_assoc] using ha''
        have hasGoal : lowerAnnListIn ke (A ++ (tvs' ++ B)) anns = some anns'' := by
          simpa only [List.append_assoc] using has''
        simp [haGoal, hasGoal]

private theorem wrapCoreParams_isSome_appendTyScope {ke : KindEnv} {tvs tvs' : List ValName}
    {params : List (ValName × Option Surface.Ty)} {e : Expr}
    (h : (wrapCoreParams ke tvs params e).isSome) :
    (wrapCoreParams ke (tvs' ++ tvs) params e).isSome := by
  induction params generalizing e with
  | nil => simp [wrapCoreParams]
  | cons p rest ih =>
    simp only [wrapCoreParams] at h ⊢
    cases hrest : wrapCoreParams ke tvs rest e with
    | none => simp [hrest] at h
    | some e' =>
      cases hann : lowerAnn ke tvs p.2 with
      | none => simp [hann, hrest] at h
      | some ann' =>
        have hrest' := ih (Option.isSome_iff_exists.mpr ⟨e', hrest⟩)
        have hann' := lowerAnn_isSome_appendTyScope (tvs' := tvs') (Option.isSome_iff_exists.mpr ⟨ann', hann⟩)
        obtain ⟨e'', hrest''⟩ := Option.isSome_iff_exists.mp hrest'
        obtain ⟨ann'', hann''⟩ := Option.isSome_iff_exists.mp hann'
        simp only [hrest'', hann'', Option.isSome_some]

private theorem wrapCoreParams_isSome_appendTyScopeMid {ke : KindEnv} {A tvs' B : List ValName}
    {params : List (ValName × Option Surface.Ty)} {e : Expr}
    (h : (wrapCoreParams ke (A ++ B) params e).isSome) :
    (wrapCoreParams ke (A ++ tvs' ++ B) params e).isSome := by
  induction params generalizing e with
  | nil => simp [wrapCoreParams]
  | cons p rest ih =>
    simp only [wrapCoreParams] at h ⊢
    cases hrest : wrapCoreParams ke (A ++ B) rest e with
    | none => simp [hrest] at h
    | some e' =>
      cases hann : lowerAnn ke (A ++ B) p.2 with
      | none => simp [hann, hrest] at h
      | some ann' =>
        have hrest' := ih (Option.isSome_iff_exists.mpr ⟨e', hrest⟩)
        have hann' := lowerAnn_isSome_appendTyScopeMid (A := A) (tvs' := tvs') (B := B)
          (Option.isSome_iff_exists.mpr ⟨ann', hann⟩)
        obtain ⟨e'', hrest''⟩ := Option.isSome_iff_exists.mp hrest'
        obtain ⟨ann'', hann''⟩ := Option.isSome_iff_exists.mp hann'
        simp only [hrest'', hann'', Option.isSome_some]

private theorem lowerCoreRecBinds_isSome_appendTyScopeMid_aux {ke : KindEnv} {A tvs' B recScope : List ValName}
    {binds : List Surface.Binding}
    (hBindRhs :
      ∀ b ∈ binds,
        (lowerCoreExpr ke (bindingLowerTyScope b (A ++ B)) (paramTermScope b.params recScope) b.rhs).isSome →
          (lowerCoreExpr ke (bindingLowerTyScope b (A ++ tvs' ++ B)) (paramTermScope b.params recScope) b.rhs).isSome)
    (h : (lowerCoreRecBinds ke (A ++ B) recScope binds).isSome) :
    (lowerCoreRecBinds ke (A ++ tvs' ++ B) recScope binds).isSome := by
  induction binds with
  | nil => simp [lowerCoreRecBinds_eqs] at h ⊢
  | cons b rest ih =>
    simp only [lowerCoreRecBinds_eqs] at h ⊢
    cases hann : lowerPolyAnnIn ke (A ++ B)
        (finalizeAnn b.tyParams b.params b.ann) with
    | none => simp [hann] at h
    | some ann =>
      cases hr : lowerCoreExpr ke (bindingLowerTyScope b (A ++ B))
          (paramTermScope b.params recScope) b.rhs with
      | none =>
        have hrAt : lowerCoreExpr ke
            (letAnnTyPrefix b.tyParams (finalizeAnn b.tyParams b.params b.ann) ++ (A ++ B))
            (paramTermScope b.params recScope) b.rhs = none := by
          simpa [bindingLowerTyScope] using hr
        simp [hann, hrAt] at h
      | some rhsCore =>
        cases hwrap : wrapCoreParams ke (bindingLowerTyScope b (A ++ B))
            b.params rhsCore with
        | none =>
          have hrAt : lowerCoreExpr ke
              (letAnnTyPrefix b.tyParams (finalizeAnn b.tyParams b.params b.ann) ++ (A ++ B))
              (paramTermScope b.params recScope) b.rhs = some rhsCore := by
            simpa [bindingLowerTyScope] using hr
          have hwrapAt : wrapCoreParams ke
              (letAnnTyPrefix b.tyParams (finalizeAnn b.tyParams b.params b.ann) ++ (A ++ B))
              b.params rhsCore = none := by
            simpa [bindingLowerTyScope] using hwrap
          simp [hann, hrAt, hwrapAt] at h
        | some rhs =>
          cases hrest : lowerCoreRecBinds ke (A ++ B) recScope rest with
          | none =>
            have hrAt : lowerCoreExpr ke
                (letAnnTyPrefix b.tyParams (finalizeAnn b.tyParams b.params b.ann) ++ (A ++ B))
                (paramTermScope b.params recScope) b.rhs = some rhsCore := by
              simpa [bindingLowerTyScope] using hr
            have hwrapAt : wrapCoreParams ke
                (letAnnTyPrefix b.tyParams (finalizeAnn b.tyParams b.params b.ann) ++ (A ++ B))
                b.params rhsCore = some rhs := by
              simpa [bindingLowerTyScope] using hwrap
            simp [hann, hrAt, hwrapAt, hrest] at h
          | some rest' =>
            have hannNew := lowerPolyAnnIn_isSome_appendTyScopeMid
              (A := A) (tvs' := tvs') (B := B)
              (Option.isSome_iff_exists.mpr ⟨ann, hann⟩)
            obtain ⟨annNew, hannNew⟩ := Option.isSome_iff_exists.mp hannNew
            have hrNew := hBindRhs b List.mem_cons_self
              (Option.isSome_iff_exists.mpr ⟨rhsCore, hr⟩)
            obtain ⟨rhsCoreNew, hrNew⟩ := Option.isSome_iff_exists.mp hrNew
            let tyPrefix := letAnnTyPrefix b.tyParams
              (finalizeAnn b.tyParams b.params b.ann)
            have hwrapAt :
                wrapCoreParams ke ((tyPrefix ++ A) ++ B) b.params rhsCore = some rhs := by
              simpa [tyPrefix, bindingLowerTyScope, List.append_assoc] using hwrap
            have hwrapExtended := wrapCoreParams_isSome_appendTyScopeMid
              (A := tyPrefix ++ A) (tvs' := tvs') (B := B)
              (Option.isSome_iff_exists.mpr ⟨rhs, hwrapAt⟩)
            have hwrapNew :
                (wrapCoreParams ke (bindingLowerTyScope b (A ++ tvs' ++ B))
                  b.params rhsCoreNew).isSome := by
              refine wrapCoreParams_isSome_invariant (e := rhsCore) ?_
              simpa [tyPrefix, bindingLowerTyScope, List.append_assoc] using hwrapExtended
            obtain ⟨rhsNew, hwrapNew⟩ := Option.isSome_iff_exists.mp hwrapNew
            have hrestNew := ih
              (fun b' hb' hIs => hBindRhs b' (List.mem_cons_of_mem _ hb') hIs)
              (Option.isSome_iff_exists.mpr ⟨rest', hrest⟩)
            obtain ⟨restNew, hrestNew⟩ := Option.isSome_iff_exists.mp hrestNew
            have hrNewAt : lowerCoreExpr ke
                (letAnnTyPrefix b.tyParams (finalizeAnn b.tyParams b.params b.ann) ++
                  (A ++ tvs' ++ B))
                (paramTermScope b.params recScope) b.rhs = some rhsCoreNew := by
              simpa [bindingLowerTyScope] using hrNew
            have hwrapNewAt : wrapCoreParams ke
                (letAnnTyPrefix b.tyParams (finalizeAnn b.tyParams b.params b.ann) ++
                  (A ++ tvs' ++ B))
                b.params rhsCoreNew = some rhsNew := by
              simpa [bindingLowerTyScope] using hwrapNew
            have hannNew' : lowerPolyAnnIn ke (A ++ (tvs' ++ B))
                (finalizeAnn b.tyParams b.params b.ann) = some annNew := by
              simpa only [List.append_assoc] using hannNew
            have hrNewAt' : lowerCoreExpr ke
                (letAnnTyPrefix b.tyParams (finalizeAnn b.tyParams b.params b.ann) ++
                  (A ++ (tvs' ++ B)))
                (paramTermScope b.params recScope) b.rhs = some rhsCoreNew := by
              simpa only [List.append_assoc] using hrNewAt
            have hwrapNewAt' : wrapCoreParams ke
                (letAnnTyPrefix b.tyParams (finalizeAnn b.tyParams b.params b.ann) ++
                  (A ++ (tvs' ++ B)))
                b.params rhsCoreNew = some rhsNew := by
              simpa only [List.append_assoc] using hwrapNewAt
            have hrestNew' : lowerCoreRecBinds ke (A ++ (tvs' ++ B)) recScope rest =
                some restNew := by
              simpa only [List.append_assoc] using hrestNew
            simp [hannNew', hrNewAt', hwrapNewAt', hrestNew']

private theorem lowerCoreRecBinds_isSome_appendTyScope_aux {ke : KindEnv} {tvs recScope tvs' : List ValName}
    {binds : List Surface.Binding}
    (hBindRhs :
      ∀ b ∈ binds,
        (lowerCoreExpr ke (bindingLowerTyScope b tvs) (paramTermScope b.params recScope) b.rhs).isSome →
          (lowerCoreExpr ke (bindingLowerTyScope b (tvs' ++ tvs)) (paramTermScope b.params recScope) b.rhs).isSome)
    (h : (lowerCoreRecBinds ke tvs recScope binds).isSome) :
    (lowerCoreRecBinds ke (tvs' ++ tvs) recScope binds).isSome := by
  have h' := lowerCoreRecBinds_isSome_appendTyScopeMid_aux
    (A := []) (tvs' := tvs') (B := tvs) (recScope := recScope)
    (binds := binds)
    (fun b hb hIs => by
      simpa using hBindRhs b hb (by simpa using hIs))
    (by simpa using h)
  simpa using h'

theorem lowerTyList_isSome_appendTyScope {ke : KindEnv} {tvs tvs' : List ValName}
    {ss : List Surface.Ty} (h : (lowerTyList ke tvs ss).isSome) :
    (lowerTyList ke (tvs' ++ tvs) ss).isSome := by
  induction ss with
  | nil => simp [lowerTyList] at h ⊢
  | cons s ss ih =>
    simp only [lowerTyList] at h
    cases hs : lowerTy ke tvs s with
    | none => simp [hs] at h
    | some _ =>
      cases hss : lowerTyList ke tvs ss with
      | none => simp [hss] at h
      | some _ =>
        have hs' := lowerTy_isSome_appendTyScope (tvs' := tvs') (Option.isSome_iff_exists.mpr ⟨_, hs⟩)
        have hss' := ih (Option.isSome_iff_exists.mpr ⟨_, hss⟩)
        obtain ⟨_, hs''⟩ := Option.isSome_iff_exists.mp hs'
        obtain ⟨_, hss''⟩ := Option.isSome_iff_exists.mp hss'
        simp only [lowerTyList, hs'', hss'', Option.isSome_some]

theorem lowerTyList_isSome_appendTyScopeMid {ke : KindEnv} {A tvs' B : List ValName}
    {ss : List Surface.Ty} (h : (lowerTyList ke (A ++ B) ss).isSome) :
    (lowerTyList ke (A ++ tvs' ++ B) ss).isSome := by
  induction ss with
  | nil => simp [lowerTyList] at h ⊢
  | cons s ss ih =>
    simp only [lowerTyList] at h
    cases hs : lowerTy ke (A ++ B) s with
    | none => simp [hs] at h
    | some _ =>
      cases hss : lowerTyList ke (A ++ B) ss with
      | none => simp [hss] at h
      | some _ =>
        have hs' := lowerTy_isSome_appendTyScopeMid (A := A) (tvs' := tvs') (B := B)
          (Option.isSome_iff_exists.mpr ⟨_, hs⟩)
        have hss' := ih (Option.isSome_iff_exists.mpr ⟨_, hss⟩)
        obtain ⟨_, hs''⟩ := Option.isSome_iff_exists.mp hs'
        obtain ⟨_, hss''⟩ := Option.isSome_iff_exists.mp hss'
        simp only [lowerTyList, hs'', hss'', Option.isSome_some]

theorem lowerCoreExpr_isSome_appendTyScopeMid {ke : KindEnv} {A tvs' B vs : List ValName}
    {e : Surface.Expr} (h : (lowerCoreExpr ke (A ++ B) vs e).isSome) :
    (lowerCoreExpr ke (A ++ tvs' ++ B) vs e).isSome := by
  match e with
  | .primLit p =>
    cases p <;> simp [lowerCoreExpr_eqs] at h ⊢
  | .primBinOp op =>
    simp [lowerCoreExpr_eqs] at h ⊢
  | .ctor name =>
    simp [lowerCoreExpr_eqs] at h ⊢
  | .var binding =>
    simp [lowerCoreExpr_eqs] at h ⊢
    exact h
  | .pair a b =>
    simp only [lowerCoreExpr_eqs] at h
    cases ha : lowerCoreExpr ke (A ++ B) vs a with
    | none => simp [ha, Option.isSome_none] at h
    | some a' =>
      cases hb : lowerCoreExpr ke (A ++ B) vs b with
      | none => simp [hb, Option.isSome_none] at h
      | some b' =>
        have ha' := lowerCoreExpr_isSome_appendTyScopeMid (A := A) (tvs' := tvs') (B := B) (vs := vs) (e := a)
          (Option.isSome_iff_exists.mpr ⟨a', ha⟩)
        have hb' := lowerCoreExpr_isSome_appendTyScopeMid (A := A) (tvs' := tvs') (B := B) (vs := vs) (e := b)
          (Option.isSome_iff_exists.mpr ⟨b', hb⟩)
        obtain ⟨_, ha''⟩ := Option.isSome_iff_exists.mp ha'
        obtain ⟨_, hb''⟩ := Option.isSome_iff_exists.mp hb'
        simp only [lowerCoreExpr_eqs, ha'', hb'', Option.isSome_some]
  | .cons head tail =>
    simp only [lowerCoreExpr_eqs] at h
    cases hh : lowerCoreExpr ke (A ++ B) vs head with
    | none => simp [hh, Option.isSome_none] at h
    | some h'' =>
      cases ht : lowerCoreExpr ke (A ++ B) vs tail with
      | none => simp [ht, Option.isSome_none] at h
      | some t' =>
        have hh' := lowerCoreExpr_isSome_appendTyScopeMid (A := A) (tvs' := tvs') (B := B) (vs := vs) (e := head)
          (Option.isSome_iff_exists.mpr ⟨h'', hh⟩)
        have ht' := lowerCoreExpr_isSome_appendTyScopeMid (A := A) (tvs' := tvs') (B := B) (vs := vs) (e := tail)
          (Option.isSome_iff_exists.mpr ⟨t', ht⟩)
        obtain ⟨_, hh''⟩ := Option.isSome_iff_exists.mp hh'
        obtain ⟨_, ht''⟩ := Option.isSome_iff_exists.mp ht'
        simp only [lowerCoreExpr_eqs, hh'', ht'', Option.isSome_some]
  | .list items =>
    simp only [lowerCoreExpr_eqs] at h
    cases hitems : lowerCoreExprList ke (A ++ B) vs items with
    | none => simp [hitems, Option.isSome_none] at h
    | some items' =>
      have hitems' := lowerCoreExprList_isSome_appendTyScopeMid_aux
        (fun e' _ hIs =>
          lowerCoreExpr_isSome_appendTyScopeMid (A := A) (tvs' := tvs') (B := B) (vs := vs) (e := e') hIs)
        (Option.isSome_iff_exists.mpr ⟨items', hitems⟩)
      obtain ⟨_, hitems''⟩ := Option.isSome_iff_exists.mp hitems'
      simp only [lowerCoreExpr_eqs, hitems'', Option.isSome_some]
  | .lambda param paramAnn body =>
    simp only [lowerCoreExpr_eqs] at h
    cases hann : lowerAnn ke (A ++ B) paramAnn with
    | none => simp [hann, Option.isSome_none] at h
    | some ann' =>
      have hann' := lowerAnn_isSome_appendTyScopeMid (A := A) (tvs' := tvs') (B := B)
        (Option.isSome_iff_exists.mpr ⟨ann', hann⟩)
      obtain ⟨ann'', hann''⟩ := Option.isSome_iff_exists.mp hann'
      match param with
      | .name x =>
        cases hb : lowerCoreExpr ke (A ++ B) (x :: vs) body with
        | none => simp [hann, hb, Option.isSome_none] at h
        | some b' =>
          have hb' := lowerCoreExpr_isSome_appendTyScopeMid (A := A) (tvs' := tvs') (B := B) (vs := x :: vs)
              (e := body) (Option.isSome_iff_exists.mpr ⟨b', hb⟩)
          obtain ⟨_, hb''⟩ := Option.isSome_iff_exists.mp hb'
          simp only [lowerCoreExpr_eqs, hann'', hb'', Option.isSome_some]
      | .wildcard =>
        cases hb : lowerCoreExpr ke (A ++ B) (.mk "_" :: vs) body with
        | none => simp [hann, hb, Option.isSome_none] at h
        | some b' =>
          have hb' := lowerCoreExpr_isSome_appendTyScopeMid (A := A) (tvs' := tvs') (B := B) (vs := .mk "_" :: vs)
              (e := body) (Option.isSome_iff_exists.mpr ⟨b', hb⟩)
          obtain ⟨_, hb''⟩ := Option.isSome_iff_exists.mp hb'
          simp only [lowerCoreExpr_eqs, hann'', hb'', Option.isSome_some]
      | .ctor n ps =>
        cases hb : lowerCoreExpr ke (A ++ B) (patVars (.ctor n ps) ++ .mk "_" :: vs) body with
        | none => simp [hann, hb, Option.isSome_none] at h
        | some b' =>
          have hb' := lowerCoreExpr_isSome_appendTyScopeMid (A := A) (tvs' := tvs') (B := B)
            (vs := patVars (.ctor n ps) ++ .mk "_" :: vs) (e := body)
            (Option.isSome_iff_exists.mpr ⟨b', hb⟩)
          obtain ⟨_, hb''⟩ := Option.isSome_iff_exists.mp hb'
          simp only [lowerCoreExpr_eqs, hann'', hb'', Option.isSome_some]
      | .pair a b =>
        cases hb : lowerCoreExpr ke (A ++ B) (patVars (.pair a b) ++ .mk "_" :: vs) body with
        | none => simp [hann, hb, Option.isSome_none] at h
        | some b' =>
          have hb' := lowerCoreExpr_isSome_appendTyScopeMid (A := A) (tvs' := tvs') (B := B)
            (vs := patVars (.pair a b) ++ .mk "_" :: vs) (e := body)
            (Option.isSome_iff_exists.mpr ⟨b', hb⟩)
          obtain ⟨_, hb''⟩ := Option.isSome_iff_exists.mp hb'
          simp only [lowerCoreExpr_eqs, hann'', hb'', Option.isSome_some]
      | .cons a b =>
        cases hb : lowerCoreExpr ke (A ++ B) (patVars (.cons a b) ++ .mk "_" :: vs) body with
        | none => simp [hann, hb, Option.isSome_none] at h
        | some b' =>
          have hb' := lowerCoreExpr_isSome_appendTyScopeMid (A := A) (tvs' := tvs') (B := B)
            (vs := patVars (.cons a b) ++ .mk "_" :: vs) (e := body)
            (Option.isSome_iff_exists.mpr ⟨b', hb⟩)
          obtain ⟨_, hb''⟩ := Option.isSome_iff_exists.mp hb'
          simp only [lowerCoreExpr_eqs, hann'', hb'', Option.isSome_some]
      | .list ps =>
        cases hb : lowerCoreExpr ke (A ++ B) (patVars (.list ps) ++ .mk "_" :: vs) body with
        | none => simp [hann, hb, Option.isSome_none] at h
        | some b' =>
          have hb' := lowerCoreExpr_isSome_appendTyScopeMid (A := A) (tvs' := tvs') (B := B)
            (vs := patVars (.list ps) ++ .mk "_" :: vs) (e := body)
            (Option.isSome_iff_exists.mpr ⟨b', hb⟩)
          obtain ⟨_, hb''⟩ := Option.isSome_iff_exists.mp hb'
          simp only [lowerCoreExpr_eqs, hann'', hb'', Option.isSome_some]
  | .app f input =>
    simp only [lowerCoreExpr_eqs] at h
    cases hf : lowerCoreExpr ke (A ++ B) vs f with
    | none => simp [hf, Option.isSome_none] at h
    | some f' =>
      cases hx : lowerCoreExpr ke (A ++ B) vs input with
      | none => simp [hx, Option.isSome_none] at h
      | some x' =>
        have hf' := lowerCoreExpr_isSome_appendTyScopeMid (A := A) (tvs' := tvs') (B := B) (vs := vs) (e := f)
          (Option.isSome_iff_exists.mpr ⟨f', hf⟩)
        have hx' := lowerCoreExpr_isSome_appendTyScopeMid (A := A) (tvs' := tvs') (B := B) (vs := vs) (e := input)
          (Option.isSome_iff_exists.mpr ⟨x', hx⟩)
        obtain ⟨_, hf''⟩ := Option.isSome_iff_exists.mp hf'
        obtain ⟨_, hx''⟩ := Option.isSome_iff_exists.mp hx'
        simp only [lowerCoreExpr_eqs, hf'', hx'', Option.isSome_some]
  | .letIn name tyParams params ann rhs body =>
    simp only [lowerCoreExpr_eqs] at h
    cases hann : lowerPolyAnnIn ke (A ++ B) (finalizeAnn tyParams params ann) with
    | none => simp [hann, Option.isSome_none] at h
    | some ann' =>
      have hannExt := lowerPolyAnnIn_isSome_appendTyScopeMid
        (A := A) (tvs' := tvs') (B := B)
        (Option.isSome_iff_exists.mpr ⟨ann', hann⟩)
      obtain ⟨annExt, hannExt⟩ := Option.isSome_iff_exists.mp hannExt
      set Alet := letAnnTyPrefix tyParams (finalizeAnn tyParams params ann) with hAlet
      set tvsInner := Alet ++ (A ++ B) with htvsInner
      cases hr : lowerCoreExpr ke tvsInner (paramTermScope params vs) rhs with
      | none => simp [hann, hr, Option.isSome_none] at h
      | some rhsCore =>
        cases hwrap : wrapCoreParams ke tvsInner params rhsCore with
        | none => simp [hann, hr, hwrap, Option.isSome_none] at h
        | some rhs' =>
          cases hb : lowerCoreExpr ke (A ++ B) (name :: vs) body with
          | none => simp [hann, hr, hwrap, hb, Option.isSome_none] at h
          | some body' =>
            have hrAt : lowerCoreExpr ke (Alet ++ A ++ B) (paramTermScope params vs) rhs = some rhsCore := by
              simpa [htvsInner, List.append_assoc] using hr
            have hr' := lowerCoreExpr_isSome_appendTyScopeMid (A := Alet ++ A) (tvs' := tvs') (B := B)
              (vs := paramTermScope params vs) (e := rhs)
              (Option.isSome_iff_exists.mpr ⟨rhsCore, hrAt⟩)
            obtain ⟨rhsCore', hr'⟩ := Option.isSome_iff_exists.mp hr'
            have hwrapAt : wrapCoreParams ke (Alet ++ A ++ B) params rhsCore = some rhs' := by
              simpa [htvsInner, List.append_assoc] using hwrap
            have hwrap' := wrapCoreParams_isSome_appendTyScopeMid (A := Alet ++ A) (tvs' := tvs') (B := B)
              (Option.isSome_iff_exists.mpr ⟨rhs', hwrapAt⟩)
            obtain ⟨rhs'', hwrap'⟩ := Option.isSome_iff_exists.mp hwrap'
            have hb' := lowerCoreExpr_isSome_appendTyScopeMid (A := A) (tvs' := tvs') (B := B)
              (vs := name :: vs) (e := body) (Option.isSome_iff_exists.mpr ⟨body', hb⟩)
            obtain ⟨bodyW, hbW⟩ := Option.isSome_iff_exists.mp hb'
            have hrGoal : lowerCoreExpr ke (Alet ++ (A ++ tvs' ++ B))
                (paramTermScope params vs) rhs = some rhsCore' := by
              convert hr' using 2
              simp only [List.append_assoc]
            have hwrapOnCore : wrapCoreParams ke (Alet ++ (A ++ tvs' ++ B)) params rhsCore =
                some rhs'' := by
              convert hwrap' using 2
              simp only [List.append_assoc]
            have hwrapGoal : (wrapCoreParams ke (Alet ++ (A ++ tvs' ++ B)) params rhsCore').isSome :=
              wrapCoreParams_isSome_invariant (e := rhsCore) (e' := rhsCore')
                (Option.isSome_iff_exists.mpr ⟨rhs'', hwrapOnCore⟩)
            obtain ⟨w, hw⟩ := Option.isSome_iff_exists.mp hwrapGoal
            simp only [lowerCoreExpr_eqs, hannExt, ← hAlet, hrGoal, hw, hbW, Option.isSome_some]
  | .letRecIn binds body =>
    let recScope := binds.map (·.name) ++ vs
    simp only [lowerCoreExpr_eqs] at h
    cases hbinds : lowerCoreRecBinds ke (A ++ B) recScope binds with
    | none =>
      simp [hbinds, recScope, Option.isSome_none] at h
    | some _ =>
      cases hb : lowerCoreExpr ke (A ++ B) recScope body with
      | none =>
        simp [hbinds, hb, recScope, Option.isSome_none] at h
      | some body' =>
          have hbinds' := lowerCoreRecBinds_isSome_appendTyScopeMid_aux
            (fun b _hbIn hIs => by
              obtain ⟨rhsCore, hrScope⟩ := Option.isSome_iff_exists.mp hIs
              set A' := letAnnTyPrefix b.tyParams (finalizeAnn b.tyParams b.params b.ann) with hA'
              have hrAt : lowerCoreExpr ke (A' ++ A ++ B) (paramTermScope b.params recScope) b.rhs = some rhsCore := by
                simpa [bindingLowerTyScope, hA', List.append_assoc] using hrScope
              have hr' := lowerCoreExpr_isSome_appendTyScopeMid (A := A' ++ A) (tvs' := tvs') (B := B)
                  (vs := paramTermScope b.params recScope) (e := b.rhs)
                (Option.isSome_iff_exists.mpr ⟨rhsCore, hrAt⟩)
              obtain ⟨rhsCore', hr'⟩ := Option.isSome_iff_exists.mp hr'
              have hrScopeMid : lowerCoreExpr ke (A' ++ (A ++ (tvs' ++ B))) (paramTermScope b.params recScope) b.rhs =
                  some rhsCore' := by
                rw [← List.append_assoc A' A, ← List.append_assoc (A' ++ A) tvs' B]
                exact hr'
              have hrScope' : lowerCoreExpr ke (A' ++ (A ++ tvs' ++ B)) (paramTermScope b.params recScope) b.rhs =
                  some rhsCore' :=
                (List.append_assoc A tvs' B).symm ▸ hrScopeMid
              have hbindScope : bindingLowerTyScope b (A ++ tvs' ++ B) = A' ++ (A ++ tvs' ++ B) := by
                simp [bindingLowerTyScope, hA', List.append_assoc]
              exact Option.isSome_iff_exists.mpr ⟨rhsCore', hbindScope ▸ hrScope'⟩)
            (Option.isSome_iff_exists.mpr ⟨_, hbinds⟩)
          obtain ⟨bindings'', hbinds''⟩ := Option.isSome_iff_exists.mp hbinds'
          have hb' := lowerCoreExpr_isSome_appendTyScopeMid (A := A) (tvs' := tvs') (B := B) (vs := recScope)
            (e := body) (Option.isSome_iff_exists.mpr ⟨body', hb⟩)
          obtain ⟨body'', hb''⟩ := Option.isSome_iff_exists.mp hb'
          simp only [lowerCoreExpr_eqs, recScope, hbinds'', hb'', Option.isSome_some]
  | .ife c t f =>
    simp only [lowerCoreExpr_eqs] at h
    cases hc : lowerCoreExpr ke (A ++ B) vs c with
    | none => simp [hc, Option.isSome_none] at h
    | some c' =>
      cases ht : lowerCoreExpr ke (A ++ B) vs t with
      | none => simp [ht, Option.isSome_none] at h
      | some t' =>
        cases hf : lowerCoreExpr ke (A ++ B) vs f with
        | none => simp [hf, Option.isSome_none] at h
        | some f' =>
          have hc' := lowerCoreExpr_isSome_appendTyScopeMid (A := A) (tvs' := tvs') (B := B) (vs := vs) (e := c)
            (Option.isSome_iff_exists.mpr ⟨c', hc⟩)
          have ht' := lowerCoreExpr_isSome_appendTyScopeMid (A := A) (tvs' := tvs') (B := B) (vs := vs) (e := t)
            (Option.isSome_iff_exists.mpr ⟨t', ht⟩)
          have hf' := lowerCoreExpr_isSome_appendTyScopeMid (A := A) (tvs' := tvs') (B := B) (vs := vs) (e := f)
            (Option.isSome_iff_exists.mpr ⟨f', hf⟩)
          obtain ⟨_, hc''⟩ := Option.isSome_iff_exists.mp hc'
          obtain ⟨_, ht''⟩ := Option.isSome_iff_exists.mp ht'
          obtain ⟨_, hf''⟩ := Option.isSome_iff_exists.mp hf'
          simp only [lowerCoreExpr_eqs, hc'', ht'', hf'', Option.isSome_some]
  | .match_ scrut brs =>
    simp only [lowerCoreExpr_eqs] at h
    cases hs : lowerCoreExpr ke (A ++ B) vs scrut with
    | none => simp [hs, Option.isSome_none] at h
    | some scrut' =>
      cases hb : lowerCoreBranches ke (A ++ B) vs brs with
      | none => simp [hb, Option.isSome_none] at h
      | some branchBodies =>
        have hs' := lowerCoreExpr_isSome_appendTyScopeMid (A := A) (tvs' := tvs') (B := B) (vs := vs) (e := scrut)
          (Option.isSome_iff_exists.mpr ⟨scrut', hs⟩)
        have hb' := lowerCoreBranches_isSome_appendTyScopeMid_aux
          (fun p b hbMem hIs =>
            lowerCoreExpr_isSome_appendTyScopeMid (A := A) (tvs' := tvs') (B := B)
              (vs := patVars p ++ vs) (e := b) hIs)
          (Option.isSome_iff_exists.mpr ⟨branchBodies, hb⟩)
        obtain ⟨_, hs''⟩ := Option.isSome_iff_exists.mp hs'
        obtain ⟨_, hb''⟩ := Option.isSome_iff_exists.mp hb'
        simp only [lowerCoreExpr_eqs, hs'', hb'', Option.isSome_some]
termination_by lowerExprSize e
decreasing_by
  all_goals first
    | exact lowerCoreExprSize_pair_left a b
    | exact lowerCoreExprSize_pair_right a b
    | exact lowerCoreExprSize_cons_head head tail
    | exact lowerCoreExprSize_cons_tail head tail
    | exact lowerCoreExprSize_list_mem ‹_›
    | exact lowerCoreExprSize_lambda_body param paramAnn body
    | exact lowerCoreExprSize_app_fn f input
    | exact lowerCoreExprSize_app_arg f input
    | first
      | exact lowerCoreExprSize_letIn_rhs name tyParams params ann rhs body
      | exact lowerCoreExprSize_letIn_body name tyParams params ann rhs body
    | first
      | exact lowerCoreExprSize_letRecIn_body binds body
      | exact lowerCoreExprSize_letRecIn_bind_rhs _hbIn
    | first
      | exact lowerCoreExprSize_ife_cond c t f
      | exact lowerCoreExprSize_ife_thn c t f
      | exact lowerCoreExprSize_ife_else c t f
    | first
      | exact lowerCoreExprSize_match_scrut
      | exact lowerCoreExprSize_match_branch hbMem

theorem lowerCoreExpr_isSome_appendTyScope {ke : KindEnv} {tvs vs tvs' : List ValName}
    {e : Surface.Expr} (h : (lowerCoreExpr ke tvs vs e).isSome) :
    (lowerCoreExpr ke (tvs' ++ tvs) vs e).isSome := by
  match e with
  | .primLit p =>
    cases p <;> simp [lowerCoreExpr_eqs] at h ⊢
  | .primBinOp op =>
    simp [lowerCoreExpr_eqs] at h ⊢
  | .ctor name =>
    simp [lowerCoreExpr_eqs] at h ⊢
  | .var binding =>
    simp [lowerCoreExpr_eqs] at h ⊢
    exact h
  | .pair a b =>
    simp only [lowerCoreExpr_eqs] at h
    cases ha : lowerCoreExpr ke tvs vs a with
    | none => simp [ha, Option.isSome_none] at h
    | some a' =>
      cases hb : lowerCoreExpr ke tvs vs b with
      | none => simp [hb, Option.isSome_none] at h
      | some b' =>
        have ha' := lowerCoreExpr_isSome_appendTyScope (tvs' := tvs') (vs := vs) (e := a)
          (Option.isSome_iff_exists.mpr ⟨a', ha⟩)
        have hb' := lowerCoreExpr_isSome_appendTyScope (tvs' := tvs') (vs := vs) (e := b)
          (Option.isSome_iff_exists.mpr ⟨b', hb⟩)
        obtain ⟨_, ha''⟩ := Option.isSome_iff_exists.mp ha'
        obtain ⟨_, hb''⟩ := Option.isSome_iff_exists.mp hb'
        simp only [lowerCoreExpr_eqs, ha'', hb'', Option.isSome_some]
  | .cons head tail =>
    simp only [lowerCoreExpr_eqs] at h
    cases hh : lowerCoreExpr ke tvs vs head with
    | none => simp [hh, Option.isSome_none] at h
    | some h'' =>
      cases ht : lowerCoreExpr ke tvs vs tail with
      | none => simp [ht, Option.isSome_none] at h
      | some t' =>
        have hh' := lowerCoreExpr_isSome_appendTyScope (tvs' := tvs') (vs := vs) (e := head)
          (Option.isSome_iff_exists.mpr ⟨h'', hh⟩)
        have ht' := lowerCoreExpr_isSome_appendTyScope (tvs' := tvs') (vs := vs) (e := tail)
          (Option.isSome_iff_exists.mpr ⟨t', ht⟩)
        obtain ⟨_, hh''⟩ := Option.isSome_iff_exists.mp hh'
        obtain ⟨_, ht''⟩ := Option.isSome_iff_exists.mp ht'
        simp only [lowerCoreExpr_eqs, hh'', ht'', Option.isSome_some]
  | .list items =>
    simp only [lowerCoreExpr_eqs] at h
    cases hitems : lowerCoreExprList ke tvs vs items with
    | none => simp [hitems, Option.isSome_none] at h
    | some items' =>
      have hitems' := lowerCoreExprList_isSome_appendTyScope_aux
        (fun e' _ hIs =>
          lowerCoreExpr_isSome_appendTyScope (tvs' := tvs') (vs := vs) (e := e') hIs)
        (Option.isSome_iff_exists.mpr ⟨items', hitems⟩)
      obtain ⟨_, hitems''⟩ := Option.isSome_iff_exists.mp hitems'
      simp only [lowerCoreExpr_eqs, hitems'', Option.isSome_some]
  | .lambda param paramAnn body =>
    simp only [lowerCoreExpr_eqs] at h
    cases hann : lowerAnn ke tvs paramAnn with
    | none => simp [hann, Option.isSome_none] at h
    | some ann' =>
      have hann' := lowerAnn_isSome_appendTyScope (tvs' := tvs') (Option.isSome_iff_exists.mpr ⟨ann', hann⟩)
      obtain ⟨ann'', hann''⟩ := Option.isSome_iff_exists.mp hann'
      match param with
      | .name x =>
        cases hb : lowerCoreExpr ke tvs (x :: vs) body with
        | none => simp [hann, hb, Option.isSome_none] at h
        | some b' =>
          have hb' := lowerCoreExpr_isSome_appendTyScope (tvs' := tvs') (vs := x :: vs) (e := body)
            (Option.isSome_iff_exists.mpr ⟨b', hb⟩)
          obtain ⟨b'', hb''⟩ := Option.isSome_iff_exists.mp hb'
          simp only [lowerCoreExpr_eqs, hann'', hb'', Option.isSome_some]
      | .wildcard =>
        cases hb : lowerCoreExpr ke tvs (.mk "_" :: vs) body with
        | none => simp [hann, hb, Option.isSome_none] at h
        | some b' =>
          have hb' := lowerCoreExpr_isSome_appendTyScope (tvs' := tvs') (vs := .mk "_" :: vs) (e := body)
            (Option.isSome_iff_exists.mpr ⟨b', hb⟩)
          obtain ⟨b'', hb''⟩ := Option.isSome_iff_exists.mp hb'
          simp only [lowerCoreExpr_eqs, hann'', hb'', Option.isSome_some]
      | .ctor n ps =>
        cases hb : lowerCoreExpr ke tvs (patVars (.ctor n ps) ++ .mk "_" :: vs) body with
        | none => simp [hann, hb, Option.isSome_none] at h
        | some b' =>
          have hb' := lowerCoreExpr_isSome_appendTyScope (tvs' := tvs')
            (vs := patVars (.ctor n ps) ++ .mk "_" :: vs) (e := body)
            (Option.isSome_iff_exists.mpr ⟨b', hb⟩)
          obtain ⟨_, hb''⟩ := Option.isSome_iff_exists.mp hb'
          simp only [lowerCoreExpr_eqs, hann'', hb'', Option.isSome_some]
      | .pair a b =>
        cases hb : lowerCoreExpr ke tvs (patVars (.pair a b) ++ .mk "_" :: vs) body with
        | none => simp [hann, hb, Option.isSome_none] at h
        | some b' =>
          have hb' := lowerCoreExpr_isSome_appendTyScope (tvs' := tvs')
            (vs := patVars (.pair a b) ++ .mk "_" :: vs) (e := body)
            (Option.isSome_iff_exists.mpr ⟨b', hb⟩)
          obtain ⟨_, hb''⟩ := Option.isSome_iff_exists.mp hb'
          simp only [lowerCoreExpr_eqs, hann'', hb'', Option.isSome_some]
      | .cons a b =>
        cases hb : lowerCoreExpr ke tvs (patVars (.cons a b) ++ .mk "_" :: vs) body with
        | none => simp [hann, hb, Option.isSome_none] at h
        | some b' =>
          have hb' := lowerCoreExpr_isSome_appendTyScope (tvs' := tvs')
            (vs := patVars (.cons a b) ++ .mk "_" :: vs) (e := body)
            (Option.isSome_iff_exists.mpr ⟨b', hb⟩)
          obtain ⟨_, hb''⟩ := Option.isSome_iff_exists.mp hb'
          simp only [lowerCoreExpr_eqs, hann'', hb'', Option.isSome_some]
      | .list ps =>
        cases hb : lowerCoreExpr ke tvs (patVars (.list ps) ++ .mk "_" :: vs) body with
        | none => simp [hann, hb, Option.isSome_none] at h
        | some b' =>
          have hb' := lowerCoreExpr_isSome_appendTyScope (tvs' := tvs')
            (vs := patVars (.list ps) ++ .mk "_" :: vs) (e := body)
            (Option.isSome_iff_exists.mpr ⟨b', hb⟩)
          obtain ⟨_, hb''⟩ := Option.isSome_iff_exists.mp hb'
          simp only [lowerCoreExpr_eqs, hann'', hb'', Option.isSome_some]
  | .app f input =>
    simp only [lowerCoreExpr_eqs] at h
    cases hf : lowerCoreExpr ke tvs vs f with
    | none => simp [hf, Option.isSome_none] at h
    | some f' =>
      cases hx : lowerCoreExpr ke tvs vs input with
      | none => simp [hx, Option.isSome_none] at h
      | some x' =>
        have hf' := lowerCoreExpr_isSome_appendTyScope (tvs' := tvs') (vs := vs) (e := f)
          (Option.isSome_iff_exists.mpr ⟨f', hf⟩)
        have hx' := lowerCoreExpr_isSome_appendTyScope (tvs' := tvs') (vs := vs) (e := input)
          (Option.isSome_iff_exists.mpr ⟨x', hx⟩)
        obtain ⟨_, hf''⟩ := Option.isSome_iff_exists.mp hf'
        obtain ⟨_, hx''⟩ := Option.isSome_iff_exists.mp hx'
        simp only [lowerCoreExpr_eqs, hf'', hx'', Option.isSome_some]
  | .letIn name tyParams params ann rhs body =>
    simp only [lowerCoreExpr_eqs] at h
    cases hann : lowerPolyAnnIn ke tvs (finalizeAnn tyParams params ann) with
    | none => simp [hann, Option.isSome_none] at h
    | some ann' =>
      have hannExt := lowerPolyAnnIn_isSome_appendTyScope (tvs' := tvs')
        (Option.isSome_iff_exists.mpr ⟨ann', hann⟩)
      obtain ⟨annExt, hannExt⟩ := Option.isSome_iff_exists.mp hannExt
      set Alet := letAnnTyPrefix tyParams (finalizeAnn tyParams params ann) with hAlet
      set tvsInner := Alet ++ tvs with htvsInner
      cases hr : lowerCoreExpr ke tvsInner (paramTermScope params vs) rhs with
      | none => simp [hann, hr, Option.isSome_none] at h
      | some rhsCore =>
        cases hwrap : wrapCoreParams ke tvsInner params rhsCore with
        | none => simp [hann, hr, hwrap, Option.isSome_none] at h
        | some rhs' =>
          cases hb : lowerCoreExpr ke tvs (name :: vs) body with
          | none => simp [hann, hr, hwrap, hb, Option.isSome_none] at h
          | some body' =>
            have hr' := lowerCoreExpr_isSome_appendTyScopeMid (A := Alet) (tvs' := tvs') (B := tvs)
              (vs := paramTermScope params vs) (e := rhs)
              (by simpa [htvsInner] using Option.isSome_iff_exists.mpr ⟨rhsCore, hr⟩)
            obtain ⟨rhsCore', hr'⟩ := Option.isSome_iff_exists.mp hr'
            have hwrap' := wrapCoreParams_isSome_appendTyScopeMid (A := Alet) (tvs' := tvs') (B := tvs)
              (by simpa [htvsInner] using Option.isSome_iff_exists.mpr ⟨rhs', hwrap⟩)
            obtain ⟨rhs'', hwrap'⟩ := Option.isSome_iff_exists.mp hwrap'
            have hb' := lowerCoreExpr_isSome_appendTyScope (tvs' := tvs') (vs := name :: vs) (e := body)
              (Option.isSome_iff_exists.mpr ⟨body', hb⟩)
            obtain ⟨_, hb''⟩ := Option.isSome_iff_exists.mp hb'
            have hrGoal : lowerCoreExpr ke (Alet ++ (tvs' ++ tvs))
                (paramTermScope params vs) rhs = some rhsCore' := by
              convert hr' using 2
              simp only [List.append_assoc]
            have hwrapOnCore : wrapCoreParams ke (Alet ++ (tvs' ++ tvs)) params rhsCore =
                some rhs'' := by
              convert hwrap' using 2
              simp only [List.append_assoc]
            have hwrapGoal : (wrapCoreParams ke (Alet ++ (tvs' ++ tvs)) params rhsCore').isSome :=
              wrapCoreParams_isSome_invariant (e := rhsCore) (e' := rhsCore')
                (Option.isSome_iff_exists.mpr ⟨rhs'', hwrapOnCore⟩)
            obtain ⟨w, hw⟩ := Option.isSome_iff_exists.mp hwrapGoal
            simp only [lowerCoreExpr_eqs, hannExt, ← hAlet, hrGoal, hw, hb'', Option.isSome_some]
  | .letRecIn binds body =>
    let recScope := binds.map (·.name) ++ vs
    simp only [lowerCoreExpr_eqs] at h
    cases hbinds : lowerCoreRecBinds ke tvs recScope binds with
    | none =>
      simp [hbinds, recScope, Option.isSome_none] at h
    | some _ =>
      cases hb : lowerCoreExpr ke tvs recScope body with
      | none =>
        simp [hbinds, hb, recScope, Option.isSome_none] at h
      | some body' =>
          have hbinds' := lowerCoreRecBinds_isSome_appendTyScope_aux
            (fun b _hbIn hIs => by
              obtain ⟨rhsCore, hrScope⟩ := Option.isSome_iff_exists.mp hIs
              set A := letAnnTyPrefix b.tyParams (finalizeAnn b.tyParams b.params b.ann) with hA
              have hrAt : lowerCoreExpr ke (A ++ tvs) (paramTermScope b.params recScope) b.rhs = some rhsCore := by
                simpa [bindingLowerTyScope, hA] using hrScope
              have hr' := lowerCoreExpr_isSome_appendTyScopeMid (A := A) (tvs' := tvs') (B := tvs)
                  (vs := paramTermScope b.params recScope) (e := b.rhs)
                (Option.isSome_iff_exists.mpr ⟨rhsCore, hrAt⟩)
              obtain ⟨rhsCore', hr'⟩ := Option.isSome_iff_exists.mp hr'
              have hrScope' : lowerCoreExpr ke (A ++ (tvs' ++ tvs)) (paramTermScope b.params recScope) b.rhs =
                  some rhsCore' := by
                rw [← List.append_assoc A tvs' tvs]
                exact hr'
              have hbindScope : bindingLowerTyScope b (tvs' ++ tvs) = A ++ (tvs' ++ tvs) := by
                simp [bindingLowerTyScope, hA]
              exact Option.isSome_iff_exists.mpr ⟨rhsCore', hbindScope ▸ hrScope'⟩)
            (Option.isSome_iff_exists.mpr ⟨_, hbinds⟩)
          obtain ⟨bindings'', hbinds''⟩ := Option.isSome_iff_exists.mp hbinds'
          have hb' := lowerCoreExpr_isSome_appendTyScope (tvs' := tvs') (vs := recScope) (e := body)
            (Option.isSome_iff_exists.mpr ⟨body', hb⟩)
          obtain ⟨body'', hb''⟩ := Option.isSome_iff_exists.mp hb'
          simp only [lowerCoreExpr_eqs, recScope, hbinds'', hb'', Option.isSome_some]
  | .ife c t f =>
    simp only [lowerCoreExpr_eqs] at h
    cases hc : lowerCoreExpr ke tvs vs c with
    | none => simp [hc, Option.isSome_none] at h
    | some c' =>
      cases ht : lowerCoreExpr ke tvs vs t with
      | none => simp [ht, Option.isSome_none] at h
      | some t' =>
        cases hf : lowerCoreExpr ke tvs vs f with
        | none => simp [hf, Option.isSome_none] at h
        | some f' =>
          have hc' := lowerCoreExpr_isSome_appendTyScope (tvs' := tvs') (vs := vs) (e := c)
            (Option.isSome_iff_exists.mpr ⟨c', hc⟩)
          have ht' := lowerCoreExpr_isSome_appendTyScope (tvs' := tvs') (vs := vs) (e := t)
            (Option.isSome_iff_exists.mpr ⟨t', ht⟩)
          have hf' := lowerCoreExpr_isSome_appendTyScope (tvs' := tvs') (vs := vs) (e := f)
            (Option.isSome_iff_exists.mpr ⟨f', hf⟩)
          obtain ⟨_, hc''⟩ := Option.isSome_iff_exists.mp hc'
          obtain ⟨_, ht''⟩ := Option.isSome_iff_exists.mp ht'
          obtain ⟨_, hf''⟩ := Option.isSome_iff_exists.mp hf'
          simp only [lowerCoreExpr_eqs, hc'', ht'', hf'', Option.isSome_some]
  | .match_ scrut brs =>
    simp only [lowerCoreExpr_eqs] at h
    cases hs : lowerCoreExpr ke tvs vs scrut with
    | none => simp [hs, Option.isSome_none] at h
    | some scrut' =>
      cases hb : lowerCoreBranches ke tvs vs brs with
      | none => simp [hb, Option.isSome_none] at h
      | some branchBodies =>
        have hs' := lowerCoreExpr_isSome_appendTyScope (tvs' := tvs') (vs := vs) (e := scrut)
          (Option.isSome_iff_exists.mpr ⟨scrut', hs⟩)
        have hb' := lowerCoreBranches_isSome_appendTyScope_aux
          (fun p b hbMem hIs =>
            lowerCoreExpr_isSome_appendTyScope (tvs' := tvs') (vs := patVars p ++ vs) (e := b) hIs)
          (Option.isSome_iff_exists.mpr ⟨branchBodies, hb⟩)
        obtain ⟨_, hs''⟩ := Option.isSome_iff_exists.mp hs'
        obtain ⟨_, hb''⟩ := Option.isSome_iff_exists.mp hb'
        simp only [lowerCoreExpr_eqs, hs'', hb'', Option.isSome_some]
termination_by lowerExprSize e
decreasing_by
  all_goals first
    | exact lowerCoreExprSize_pair_left a b
    | exact lowerCoreExprSize_pair_right a b
    | exact lowerCoreExprSize_cons_head head tail
    | exact lowerCoreExprSize_cons_tail head tail
    | exact lowerCoreExprSize_list_mem ‹_›
    | exact lowerCoreExprSize_lambda_body param paramAnn body
    | exact lowerCoreExprSize_app_fn f input
    | exact lowerCoreExprSize_app_arg f input
    | first
      | exact lowerCoreExprSize_letIn_rhs name tyParams params ann rhs body
      | exact lowerCoreExprSize_letIn_body name tyParams params ann rhs body
    | first
      | exact lowerCoreExprSize_letRecIn_body binds body
      | exact lowerCoreExprSize_letRecIn_bind_rhs _hbIn
    | first
      | exact lowerCoreExprSize_ife_cond c t f
      | exact lowerCoreExprSize_ife_thn c t f
      | exact lowerCoreExprSize_ife_else c t f
    | first
      | exact lowerCoreExprSize_match_scrut
      | exact lowerCoreExprSize_match_branch hbMem

theorem lowerCoreExprList_isSome_appendTyScope {ke : KindEnv} {tvs vs tvs' : List ValName}
    {items : List Surface.Expr} (h : (lowerCoreExprList ke tvs vs items).isSome) :
    (lowerCoreExprList ke (tvs' ++ tvs) vs items).isSome := by
  induction items with
  | nil => simp [lowerCoreExprList_eqs] at h ⊢
  | cons e es ih =>
    simp only [lowerCoreExprList_eqs] at h
    cases he : lowerCoreExpr ke tvs vs e with
    | none => simp [he] at h
    | some e' =>
      cases hes : lowerCoreExprList ke tvs vs es with
      | none => simp [hes] at h
      | some es' =>
        have he' := lowerCoreExpr_isSome_appendTyScope (tvs' := tvs') (Option.isSome_iff_exists.mpr ⟨e', he⟩)
        have hes' := ih (Option.isSome_iff_exists.mpr ⟨es', hes⟩)
        obtain ⟨_, he''⟩ := Option.isSome_iff_exists.mp he'
        obtain ⟨_, hes''⟩ := Option.isSome_iff_exists.mp hes'
        simp only [lowerCoreExprList_eqs, he'', hes'', Option.isSome_some]


theorem lowerCoreExprList_isSome_appendTyScopeMid {ke : KindEnv} {A tvs' B vs : List ValName}
    {items : List Surface.Expr} (h : (lowerCoreExprList ke (A ++ B) vs items).isSome) :
    (lowerCoreExprList ke (A ++ tvs' ++ B) vs items).isSome := by
  induction items with
  | nil => simp [lowerCoreExprList_eqs] at h ⊢
  | cons e es ih =>
    simp only [lowerCoreExprList_eqs] at h
    cases he : lowerCoreExpr ke (A ++ B) vs e with
    | none => simp [he] at h
    | some e' =>
      cases hes : lowerCoreExprList ke (A ++ B) vs es with
      | none => simp [hes] at h
      | some es' =>
        have he' := lowerCoreExpr_isSome_appendTyScopeMid (A := A) (tvs' := tvs') (B := B)
          (Option.isSome_iff_exists.mpr ⟨e', he⟩)
        have hes' := ih (Option.isSome_iff_exists.mpr ⟨es', hes⟩)
        obtain ⟨_, he''⟩ := Option.isSome_iff_exists.mp he'
        obtain ⟨_, hes''⟩ := Option.isSome_iff_exists.mp hes'
        simp only [lowerCoreExprList_eqs, he'', hes'', Option.isSome_some]


theorem lowerCoreBranches_isSome_appendTyScope {ke : KindEnv} {tvs vs tvs' : List ValName}
    {brs : List (Surface.Pattern × Surface.Expr)} (h : (lowerCoreBranches ke tvs vs brs).isSome) :
    (lowerCoreBranches ke (tvs' ++ tvs) vs brs).isSome := by
  induction brs with
  | nil => simp [lowerCoreBranches_eqs] at h ⊢
  | cons hd tl ih =>
    rcases hd with ⟨p, b⟩
    simp only [lowerCoreBranches_eqs] at h
    cases hb : lowerCoreExpr ke tvs (patVars p ++ vs) b with
    | none => simp [hb] at h
    | some b' =>
      cases hrest : lowerCoreBranches ke tvs vs tl with
      | none => simp [hrest] at h
      | some rest' =>
        have hb' := lowerCoreExpr_isSome_appendTyScope (tvs' := tvs') (Option.isSome_iff_exists.mpr ⟨b', hb⟩)
        have hrest' := ih (Option.isSome_iff_exists.mpr ⟨rest', hrest⟩)
        obtain ⟨_, hb''⟩ := Option.isSome_iff_exists.mp hb'
        obtain ⟨_, hrest''⟩ := Option.isSome_iff_exists.mp hrest'
        simp only [lowerCoreBranches_eqs, hb'', hrest'', Option.isSome_some]


theorem lowerCoreBranches_isSome_appendTyScopeMid {ke : KindEnv} {A tvs' B vs : List ValName}
    {brs : List (Surface.Pattern × Surface.Expr)} (h : (lowerCoreBranches ke (A ++ B) vs brs).isSome) :
    (lowerCoreBranches ke (A ++ tvs' ++ B) vs brs).isSome := by
  induction brs with
  | nil => simp [lowerCoreBranches_eqs] at h ⊢
  | cons hd tl ih =>
    rcases hd with ⟨p, b⟩
    simp only [lowerCoreBranches_eqs] at h
    cases hb : lowerCoreExpr ke (A ++ B) (patVars p ++ vs) b with
    | none => simp [hb] at h
    | some b' =>
      cases hrest : lowerCoreBranches ke (A ++ B) vs tl with
      | none => simp [hrest] at h
      | some rest' =>
        have hb' := lowerCoreExpr_isSome_appendTyScopeMid (A := A) (tvs' := tvs') (B := B)
          (Option.isSome_iff_exists.mpr ⟨b', hb⟩)
        have hrest' := ih (Option.isSome_iff_exists.mpr ⟨rest', hrest⟩)
        obtain ⟨_, hb''⟩ := Option.isSome_iff_exists.mp hb'
        obtain ⟨_, hrest''⟩ := Option.isSome_iff_exists.mp hrest'
        simp only [lowerCoreBranches_eqs, hb'', hrest'', Option.isSome_some]


theorem lowerCoreRecBinds_isSome_appendTyScope {ke : KindEnv} {tvs recScope tvs' : List ValName}
    {binds : List Surface.Binding} (h : (lowerCoreRecBinds ke tvs recScope binds).isSome) :
    (lowerCoreRecBinds ke (tvs' ++ tvs) recScope binds).isSome := by
  exact lowerCoreRecBinds_isSome_appendTyScope_aux
    (fun b _ hIs => by
      have h' := lowerCoreExpr_isSome_appendTyScopeMid
        (A := letAnnTyPrefix b.tyParams (finalizeAnn b.tyParams b.params b.ann))
        (tvs' := tvs') (B := tvs) (by
          simpa [bindingLowerTyScope] using hIs)
      simpa [bindingLowerTyScope, List.append_assoc] using h') h


theorem lowerCoreRecBinds_isSome_appendTyScopeMid {ke : KindEnv} {A tvs' B recScope : List ValName}
    {binds : List Surface.Binding} (h : (lowerCoreRecBinds ke (A ++ B) recScope binds).isSome) :
    (lowerCoreRecBinds ke (A ++ tvs' ++ B) recScope binds).isSome := by
  exact lowerCoreRecBinds_isSome_appendTyScopeMid_aux
    (fun b hb hIs => by
      have h' := lowerCoreExpr_isSome_appendTyScopeMid
        (A := letAnnTyPrefix b.tyParams (finalizeAnn b.tyParams b.params b.ann) ++ A)
        (tvs' := tvs') (B := B) (by
          simpa [bindingLowerTyScope, List.append_assoc] using hIs)
      simpa [bindingLowerTyScope, List.append_assoc] using h') h



private theorem lowerCoreRecBinds_isSome_of_forall {ke : KindEnv} {tvs recScope : List ValName}
    {binds : List Surface.Binding}
    (hanns : ∀ (i : Nat) (hi : i < binds.length),
      (lowerPolyAnnIn ke tvs
        (finalizeAnn (binds[i]'hi).tyParams (binds[i]'hi).params (binds[i]'hi).ann)).isSome)
    (h : ∀ (i : Nat) (hi : i < binds.length),
      ∃ rhsCore,
        lowerCoreExpr ke (bindingLowerTyScope (binds[i]'hi) tvs)
          (paramTermScope (binds[i]'hi).params recScope) (binds[i]'hi).rhs = some rhsCore ∧
        (wrapCoreParams ke (bindingLowerTyScope (binds[i]'hi) tvs)
          (binds[i]'hi).params rhsCore).isSome) :
    (lowerCoreRecBinds ke tvs recScope binds).isSome := by
  induction binds with
  | nil => simp [lowerCoreRecBinds_eqs]
  | cons hd tl ih =>
    simp only [lowerCoreRecBinds_eqs]
    have hann := hanns 0 (by simp)
    simp only [List.getElem_cons_zero] at hann
    obtain ⟨ann', hann'⟩ := Option.isSome_iff_exists.mp hann
    have hhd := h 0 (by simp)
    simp only [List.getElem_cons_zero] at hhd
    obtain ⟨rhsCore, hhd', hwrap⟩ := hhd
    obtain ⟨rhs', hwrap'⟩ := Option.isSome_iff_exists.mp hwrap
    have htl := ih
      (fun i hi => by
        simpa [List.getElem_cons_succ] using hanns (i + 1) (Nat.succ_lt_succ hi))
      (fun i hi => by
        simpa [List.getElem_cons_succ] using h (i + 1) (Nat.succ_lt_succ hi))
    obtain ⟨_, htl'⟩ := Option.isSome_iff_exists.mp htl
    have hhdAt : lowerCoreExpr ke
        (letAnnTyPrefix hd.tyParams (finalizeAnn hd.tyParams hd.params hd.ann) ++ tvs)
        (paramTermScope hd.params recScope) hd.rhs = some rhsCore := by
      simpa [bindingLowerTyScope] using hhd'
    have hwrapAt : wrapCoreParams ke
        (letAnnTyPrefix hd.tyParams (finalizeAnn hd.tyParams hd.params hd.ann) ++ tvs)
        hd.params rhsCore = some rhs' := by
      simpa [bindingLowerTyScope] using hwrap'
    simp only [hann', hhdAt, hwrapAt, htl', Option.isSome_some]

private theorem lowerAnnList_all_none
    {ke : KindEnv} {binds : List Surface.Binding}
    (h : ∀ b ∈ binds, b.ann = none) :
    lowerAnnList ke (binds.map (·.ann)) = some (List.replicate binds.length none) := by
  induction binds with
  | nil => simp [lowerAnnList]
  | cons hd tl ih =>
    have hhd : hd.ann = none := h hd List.mem_cons_self
    have htl := ih fun b hb => h b (List.mem_cons_of_mem _ hb)
    simp only [List.map_cons, List.length_cons, List.replicate_succ, lowerAnnList, hhd,
      lowerPolyAnn, htl]

private theorem lowerAnnList_finalizeAnn_none
    {ke : KindEnv} {binds : List Surface.Binding}
    (h : ∀ b ∈ binds, b.ann = none) :
    lowerAnnList ke (binds.map fun b => finalizeAnn b.tyParams b.params b.ann) =
    some (List.replicate binds.length none) := by
  induction binds with
  | nil => simp [lowerAnnList]
  | cons hd tl ih =>
    have hhd : hd.ann = none := h hd List.mem_cons_self
    have htl := ih fun b hb => h b (List.mem_cons_of_mem _ hb)
    simp only [List.map_cons, List.length_cons, List.replicate_succ, lowerAnnList,
      finalizeAnn_none, lowerPolyAnn, hhd, htl]

private theorem lowerAnnListIn_finalizeAnn_none
    {ke : KindEnv} {tvs : List ValName} {binds : List Surface.Binding}
    (h : ∀ b ∈ binds, b.ann = none) :
    lowerAnnListIn ke tvs (binds.map fun b => finalizeAnn b.tyParams b.params b.ann) =
      some (List.replicate binds.length none) := by
  induction binds with
  | nil => simp [lowerAnnListIn]
  | cons hd tl ih =>
    have hhd : hd.ann = none := h hd List.mem_cons_self
    have htl := ih fun b hb => h b (List.mem_cons_of_mem _ hb)
    simp only [List.map_cons, List.length_cons, List.replicate_succ, lowerAnnListIn,
      finalizeAnn_none, lowerPolyAnnIn, hhd, htl]

private theorem lowerAnnList_finalizeAnn_nil_nil {ke : KindEnv} {binds : List Surface.Binding}
    {anns' : List (Option PolyTy)}
    (h : lowerAnnList ke (binds.map (·.ann)) = some anns') :
    lowerAnnList ke (binds.map fun b => finalizeAnn [] [] b.ann) = some anns' := by
  induction binds generalizing anns' with
  | nil =>
    simp only [lowerAnnList, List.map_nil] at h ⊢
    exact h
  | cons hd tl ih =>
    simp only [lowerAnnList, List.map_cons] at h
    cases hann : hd.ann with
    | none =>
      have hfinal : finalizeAnn [] [] none = none := finalizeAnn_nil_nil_none
      cases htl : lowerAnnList ke (tl.map (·.ann)) with
      | none => simp [htl] at h
      | some tl' =>
        have htl' := ih htl
        simp only [lowerPolyAnn, htl, hann] at h
        cases h
        simp only [lowerAnnList, List.map_cons, hann, hfinal, lowerPolyAnn, htl']
    | some σ =>
      have hfinal := finalizeAnn_nil_some σ
      cases hσ : lowerPoly ke σ with
      | none =>
        rw [hann] at h
        simp [lowerPolyAnn, hσ] at h
      | some σ' =>
        cases htl : lowerAnnList ke (tl.map (·.ann)) with
        | none => simp [htl] at h
        | some tl' =>
          have htl' := ih htl
          rw [hann] at h
          simp only [lowerPolyAnn, hσ, Option.map_some, htl] at h
          cases h
          have hpoly :
              lowerPolyAnn ke (some { foralls := σ.foralls.eraseDups, body := σ.body }) = some (some σ') := by
            rw [← hfinal]
            exact lowerPolyAnn_finalizeAnn_nil hσ
          simp only [lowerAnnList, List.map_cons, hann, hfinal, hpoly, htl']

private theorem lowerAnnList_finalizeAnn_bind {ke : KindEnv} {binds : List Surface.Binding}
    {anns' : List (Option PolyTy)}
    (h : lowerAnnList ke (binds.map (·.ann)) = some anns')
    (hempty : ∀ b ∈ binds, b.tyParams = [] ∧ b.params = []) :
    lowerAnnList ke (binds.map fun b => finalizeAnn b.tyParams b.params b.ann) = some anns' := by
  have hmap :
      binds.map (fun b => finalizeAnn b.tyParams b.params b.ann) =
        binds.map (fun b => finalizeAnn [] [] b.ann) := by
    apply List.map_congr_left
    intro b hb
    rw [(hempty b hb).1, (hempty b hb).2]
  rw [hmap]
  exact lowerAnnList_finalizeAnn_nil_nil h

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
        exact ⟨i + 1, by simp [hi], ha, hb⟩

/-- Index witness implies zip membership. -/
private theorem List.getElem_mem_zip {α β : Type _} {as : List α} {bs : List β}
    {i : Nat} (hi : i < as.length) (hj : i < bs.length) :
    (as[i]'hi, bs[i]'hj) ∈ as.zip bs := by
  induction as generalizing bs i with
  | nil => cases hi
  | cons ahd atl ih =>
    cases bs with
    | nil => cases hj
    | cons bhd btl =>
      cases i with
      | zero => simp [List.zip_cons_cons]
      | succ i =>
        simp only [List.zip_cons_cons, List.getElem_cons_succ, List.mem_cons]
        exact Or.inr (ih (Nat.lt_of_succ_lt_succ hi) (Nat.lt_of_succ_lt_succ hj))

private theorem Expr.TyBvarBounded.RecGroup_of_forall
    {n : Nat} {bindings : List CoreRecBinding}
    (h : ∀ binding ∈ bindings,
      (∀ σ, binding.ann = some σ → ContainsBvarsUpTo (n + σ.paramCount) σ.body) ∧
      binding.rhs.TyBvarBounded (n + RecAnn.params binding.ann)) :
    Expr.TyBvarBounded.RecGroup n bindings := by
  induction bindings with
  | nil => trivial
  | cons binding rest ih =>
      simp only [Expr.TyBvarBounded.RecGroup]
      exact ⟨(h binding List.mem_cons_self).1, (h binding List.mem_cons_self).2,
        ih (fun binding' hbinding' => h binding' (List.mem_cons_of_mem binding hbinding'))⟩

private theorem RecSpec.map_ann_mono (τs : List Ty) :
    (τs.map RecSpec.mono).map RecSpec.ann = List.replicate τs.length none := by
  induction τs with
  | nil => rfl
  | cons _ _ ih => simp [List.replicate_succ, RecSpec.ann, ih]

private theorem lowerCoreRecBinds_length {ke : KindEnv} {tvs recScope : List ValName}
    {binds : List Surface.Binding} {bs' : List CoreRecBinding}
    (h : lowerCoreRecBinds ke tvs recScope binds = some bs') :
    bs'.length = binds.length := by
  have hrel := lowerCoreRecBinds_CoreLowersRecBinds (ctors := []) binds h
  cases hrel with
  | nil => rfl
  | cons _ _ _ hrest =>
      simp only [List.length_cons,
        lowerCoreRecBinds_length (lowerCoreRecBinds_eq_some_of_CoreLowersRecBinds hrest)]
termination_by binds.length
decreasing_by simp_all

private theorem lowerCoreRecBinds_get {ke : KindEnv} {tvs recScope : List ValName}
    {binds : List Surface.Binding} {bs' : List CoreRecBinding}
    (h : lowerCoreRecBinds ke tvs recScope binds = some bs') :
    ∀ (i : Nat) (hi : i < binds.length),
      ∃ rhsCore,
        lowerPolyAnnIn ke tvs
            (finalizeAnn (binds[i]'hi).tyParams (binds[i]'hi).params (binds[i]'hi).ann) =
          some (bs'[i]'(by simpa [lowerCoreRecBinds_length h] using hi)).ann ∧
        lowerCoreExpr ke (bindingLowerTyScope (binds[i]'hi) tvs)
            (paramTermScope (binds[i]'hi).params recScope) (binds[i]'hi).rhs = some rhsCore ∧
        wrapCoreParams ke (bindingLowerTyScope (binds[i]'hi) tvs)
          (binds[i]'hi).params rhsCore =
          some (bs'[i]'(by simpa [lowerCoreRecBinds_length h] using hi)).rhs := by
  have hrel := lowerCoreRecBinds_CoreLowersRecBinds (ctors := []) binds h
  cases hrel with
  | nil => intro i hi; cases hi
  | @cons _ _ bind ann' rhsCore rhs' rest rest' hann hrhs hwrap hrest =>
      intro i hi
      match i with
      | 0 =>
        simp only [List.getElem_cons_zero]
        change lowerPolyAnnIn ke tvs
          (finalizeAnn bind.tyParams bind.params bind.ann) = some ann' at hann
        have hrhs' : lowerCoreExpr ke (bindingLowerTyScope bind tvs)
            (paramTermScope bind.params recScope) bind.rhs = some rhsCore := by
          simpa [bindingLowerTyScope] using
            lowerCoreExpr_eq_some_of_CoreLowersExpr hrhs
        have hwrap' : wrapCoreParams ke (bindingLowerTyScope bind tvs)
            bind.params rhsCore = some rhs' := by
          simpa [bindingLowerTyScope] using hwrap
        exact ⟨rhsCore, hann, hrhs', hwrap'⟩
      | i' + 1 =>
        have hi' : i' < rest.length := Nat.lt_of_succ_lt_succ hi
        simpa using lowerCoreRecBinds_get
          (lowerCoreRecBinds_eq_some_of_CoreLowersRecBinds hrest) i' hi'
termination_by binds.length
decreasing_by simp_all

private theorem lowerCoreRecBinds_anns {ke : KindEnv} {tvs recScope : List ValName}
    {binds : List Surface.Binding} {bs' : List CoreRecBinding}
    (h : lowerCoreRecBinds ke tvs recScope binds = some bs') :
    lowerAnnListIn ke tvs
      (binds.map fun b => finalizeAnn b.tyParams b.params b.ann) =
        some (bs'.map (·.ann)) := by
  match binds with
  | [] =>
    simp only [lowerCoreRecBinds_eqs, Option.some.injEq] at h
    subst h
    rfl
  | b :: rest =>
    simp only [lowerCoreRecBinds_eqs] at h
    cases hann : lowerPolyAnnIn ke tvs
        (finalizeAnn b.tyParams b.params b.ann) with
    | none => simp [hann] at h
    | some ann' =>
      cases hrhs : lowerCoreExpr ke
          (letAnnTyPrefix b.tyParams (finalizeAnn b.tyParams b.params b.ann) ++ tvs)
          (paramTermScope b.params recScope) b.rhs with
      | none => simp [hann, hrhs] at h
      | some rhsCore =>
        cases hwrap : wrapCoreParams ke
            (letAnnTyPrefix b.tyParams (finalizeAnn b.tyParams b.params b.ann) ++ tvs)
            b.params rhsCore with
        | none => simp [hann, hrhs, hwrap] at h
        | some rhs' =>
          cases hrest : lowerCoreRecBinds ke tvs recScope rest with
          | none => simp [hann, hrhs, hwrap, hrest] at h
          | some rest' =>
            simp only [hann, hrhs, hwrap, hrest, Option.some.injEq] at h
            subst h
            simp only [List.map_cons, lowerAnnListIn, hann,
              lowerCoreRecBinds_anns hrest]
termination_by binds.length
decreasing_by simp_wf

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

theorem lowerPolyAnnIn_containsBvars {ke : KindEnv} {tvs : List ValName}
    {ann : Option Surface.PolyTy} {ann' : Option PolyTy}
    (h : lowerPolyAnnIn ke tvs ann = some ann') :
    ∀ σ, ann' = some σ → ContainsBvarsUpTo (tvs.length + σ.paramCount) σ.body := by
  rintro σ ht
  cases ann with
  | none =>
    simp only [lowerPolyAnnIn, Option.some.injEq] at h
    subst h
    cases ht
  | some σs =>
    simp only [lowerPolyAnnIn] at h
    obtain ⟨σ', hσ, rfl⟩ := Option.map_eq_some_iff.mp h
    obtain ⟨rfl⟩ := ht
    simp only [lowerPolyIn] at hσ
    obtain ⟨b, hb, hEq⟩ := Option.map_eq_some_iff.mp hσ
    cases hEq
    have hwk := Ty.WellKinded.toContainsBvars (lowerTy_wellKinded hb)
    simpa [List.length_append, Nat.add_comm] using hwk

private theorem lowerAnnListIn_length {ke : KindEnv} {tvs : List ValName}
    {as : List (Option Surface.PolyTy)} {as' : List (Option PolyTy)}
    (h : lowerAnnListIn ke tvs as = some as') : as'.length = as.length := by
  induction as generalizing as' with
  | nil =>
    simp only [lowerAnnListIn, Option.some.injEq] at h
    subst h
    rfl
  | cons a as ih =>
    simp only [lowerAnnListIn] at h
    cases ha : lowerPolyAnnIn ke tvs a with
    | none => simp [ha] at h
    | some a' =>
      cases has : lowerAnnListIn ke tvs as with
      | none => simp [ha, has] at h
      | some as'' =>
        simp only [ha, has, Option.some.injEq] at h
        subst h
        simp [ih has]

private theorem lowerAnnListIn_containsBvars {ke : KindEnv} {tvs : List ValName} :
    ∀ {as : List (Option Surface.PolyTy)} {as' : List (Option PolyTy)},
      lowerAnnListIn ke tvs as = some as' →
      ∀ σ, some σ ∈ as' → ContainsBvarsUpTo (tvs.length + σ.paramCount) σ.body := by
  intro as
  induction as with
  | nil =>
    intro as' h
    simp only [lowerAnnListIn, Option.some.injEq] at h
    subst h
    simp
  | cons a as ih =>
    intro as' h
    simp only [lowerAnnListIn] at h
    cases ha : lowerPolyAnnIn ke tvs a with
    | none => simp [ha] at h
    | some a' =>
      cases has : lowerAnnListIn ke tvs as with
      | none => simp [ha, has] at h
      | some as'' =>
        simp only [ha, has, Option.some.injEq] at h
        subst h
        intro σ hσ
        simp only [List.mem_cons] at hσ
        rcases hσ with hσ | hσ
        · exact lowerPolyAnnIn_containsBvars ha σ hσ.symm
        · exact ih has σ hσ

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

private theorem lowerAnnList_getElem_lt {ke : KindEnv} {binds : List Surface.Binding}
    {anns' : List (Option PolyTy)} {i : Nat}
    (hann : lowerAnnList ke (binds.map fun b => finalizeAnn b.tyParams b.params b.ann) = some anns')
    (hi : i < binds.length) : i < anns'.length := by
  have hlen := lowerAnnList_length hann
  rw [List.length_map] at hlen
  rw [hlen]
  exact hi

private theorem lowerAnnList_getElem_ann {ke : KindEnv} {binds : List Surface.Binding}
    {anns' : List (Option PolyTy)} {i : Nat}
    (hann : lowerAnnList ke (binds.map fun b => finalizeAnn b.tyParams b.params b.ann) = some anns')
    (hi : i < binds.length) :
    lowerPolyAnn ke (finalizeAnn (binds[i]'hi).tyParams (binds[i]'hi).params (binds[i]'hi).ann) =
      some (anns'[i]'(lowerAnnList_getElem_lt hann hi)) := by
  induction binds generalizing anns' i with
  | nil => cases hi
  | cons b rest ih =>
    simp only [lowerAnnList, List.map_cons] at hann
    cases hb : lowerPolyAnn ke (finalizeAnn b.tyParams b.params b.ann) with
    | none => simp [hb] at hann
    | some a' =>
      cases hrest : lowerAnnList ke (rest.map fun b => finalizeAnn b.tyParams b.params b.ann) with
      | none => simp [hb, hrest] at hann
      | some rest' =>
        have heq : anns' = a' :: rest' := by
          apply Option.some.inj
          rw [← hann, hb, hrest]
        match i with
        | 0 =>
          simp only [List.getElem_cons_zero, heq, hb]
        | i' + 1 =>
          have hi' : i' < rest.length := Nat.lt_of_succ_lt_succ hi
          have hlen' : rest'.length = rest.length :=
            (lowerAnnList_length hrest).trans
              (List.length_map
                (f := fun (bd : Surface.Binding) => finalizeAnn bd.tyParams bd.params bd.ann)
                (as := rest))
          have hi'' : i' < rest'.length := hlen'.symm ▸ hi'
          have heqlen : anns'.length = (b :: rest).length := by simp [heq, hlen', List.length_cons]
          have hidx : i' + 1 < anns'.length := heqlen.symm ▸ hi
          have himain := ih (anns' := rest') (i := i') hrest hi'
          have hget : anns'[i' + 1] = rest'[i'] := by simp [heq, List.getElem_cons_succ]
          exact himain.trans (congrArg some hget.symm)

private theorem lowerAnnListIn_getElem_ann {ke : KindEnv} {tvs : List ValName}
    {binds : List Surface.Binding} {anns' : List (Option PolyTy)} {i : Nat}
    (hann : lowerAnnListIn ke tvs
      (binds.map fun b => finalizeAnn b.tyParams b.params b.ann) = some anns')
    (hi : i < binds.length) :
    lowerPolyAnnIn ke tvs
        (finalizeAnn (binds[i]'hi).tyParams (binds[i]'hi).params (binds[i]'hi).ann) =
      some (anns'[i]'(by
        have hlen := lowerAnnListIn_length hann
        rw [List.length_map] at hlen
        exact hlen.symm ▸ hi)) := by
  induction binds generalizing anns' i with
  | nil => cases hi
  | cons b rest ih =>
    simp only [lowerAnnListIn, List.map_cons] at hann
    cases hb : lowerPolyAnnIn ke tvs (finalizeAnn b.tyParams b.params b.ann) with
    | none => simp [hb] at hann
    | some a' =>
      cases hrest : lowerAnnListIn ke tvs
          (rest.map fun b => finalizeAnn b.tyParams b.params b.ann) with
      | none => simp [hb, hrest] at hann
      | some rest' =>
        have heq : anns' = a' :: rest' := by
          apply Option.some.inj
          rw [← hann, hb, hrest]
        match i with
        | 0 => simp only [List.getElem_cons_zero, heq, hb]
        | i' + 1 =>
          have hi' : i' < rest.length := Nat.lt_of_succ_lt_succ hi
          have himain := ih (anns' := rest') (i := i') hrest hi'
          simpa [heq, List.getElem_cons_succ] using himain

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

theorem wrapCoreParams_tyBvarBounded {ke : KindEnv} {tvs : List ValName}
    {params : List (ValName × Option Surface.Ty)} {e e' : Expr}
    (hwrap : wrapCoreParams ke tvs params e = some e')
    (he : e.TyBvarBounded tvs.length) :
    e'.TyBvarBounded tvs.length := by
  induction params generalizing e e' with
  | nil =>
    simp [wrapCoreParams] at hwrap
    subst hwrap
    exact he
  | cons p rest ih =>
    simp [wrapCoreParams] at hwrap
    cases hrest : wrapCoreParams ke tvs rest e with
    | none => simp [hrest] at hwrap
    | some e'' =>
      cases hann : lowerAnn ke tvs p.2 with
      | none =>
        simp [hann, hrest] at hwrap
      | some ann' =>
        simp [hrest, hann] at hwrap
        subst hwrap
        simp only [Expr.TyBvarBounded]
        exact ⟨fun t ht => lowerAnn_containsBvars hann t ht, ih hrest he⟩

private theorem wrapCoreParams_tyBvarBounded_ambient {ke : KindEnv} {b : Surface.Binding}
    {tvs _recScope : List ValName} {e0' e : Expr}
    (htp : b.tyParams = []) (hann : b.ann = none)
    (hwrap : wrapCoreParams ke (bindingLowerTyScope b tvs) b.params e0' = some e)
    (he0 : e0'.TyBvarBounded (bindingLowerTyScope b tvs).length) :
    e.TyBvarBounded tvs.length := by
  have hscope := bindingLowerTyScope_nilTyParams_nilAnn (tvs := tvs) htp hann
  rw [hscope] at hwrap he0
  exact wrapCoreParams_tyBvarBounded hwrap he0

private theorem wrapCoreParams_tyBvarBounded_letIn_none {ke : KindEnv}
    {tyParams : List ValName} {params : List (ValName × Option Surface.Ty)}
    {tvs : List ValName} {e e' : Expr}
    (hann : lowerPolyAnn ke (finalizeAnn tyParams params (none : Option Surface.PolyTy)) = some none)
    (hwrap : wrapCoreParams ke (letRhsTyScope tyParams params (none : Option Surface.PolyTy) tvs) params e =
        some e')
    (he : e.TyBvarBounded tvs.length) :
    e'.TyBvarBounded tvs.length := by
  have hF := lowerPolyAnn_finalizeAnn_none hann
  have hscopeEq : letRhsTyScope tyParams params (none : Option Surface.PolyTy) tvs = tvs := by
    simp [letRhsTyScope, letAnnTyPrefix, hF]
  rw [hscopeEq] at hwrap
  exact wrapCoreParams_tyBvarBounded hwrap he

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

/-! ### Surface-lowered terms are `TyBvarBounded tvs.length`

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
    simp only [emitLets.go, emitLetsWith.go, coreEmissionOps, Expr.TyBvarBounded]
    refine And.intro ?_ (ih (depth + 1))
    trivial

mutual
private theorem emit_tyBvarBounded (n : Nat) (env : List Occ) (bodies : Nat → Expr)
    (t : DTree) (hb : ∀ i, (bodies i).TyBvarBounded n) :
    (emit env bodies t).TyBvarBounded n := by
  match t with
  | .fail =>
    rw [emit, emitWith]
    simp only [coreEmissionOps, Expr.TyBvarBounded, Expr.TyBvarBounded.BranchList]
    trivial
  | .leaf act binds =>
    rw [emit, emitWith]
    exact emitLets_tyBvarBounded n env binds (bodies act) (hb act)
  | .switch occ cases dflt =>
    cases dflt with
    | fail =>
      rw [emit, emitWith]
      have hcases := emitCases_tyBvarBounded n env bodies occ cases hb
      simp only [coreEmissionOps, Expr.TyBvarBounded, List.append_nil]
      exact And.intro (by trivial) hcases
    | leaf act binds =>
      rw [emit, emitWith]
      have hcases := emitCases_tyBvarBounded n env bodies occ cases hb
      have hd := emit_tyBvarBounded n env bodies (.leaf act binds) hb
      simp only [coreEmissionOps, Expr.TyBvarBounded]
      refine And.intro ?_ ((TyBvarBounded_BranchList_append_wildcard n _ _).mpr (And.intro hcases hd))
      trivial
      intro h; cases h
    | switch occ' cases' dflt' =>
      rw [emit, emitWith]
      have hcases := emitCases_tyBvarBounded n env bodies occ cases hb
      have hd := emit_tyBvarBounded n env bodies (.switch occ' cases' dflt') hb
      simp only [coreEmissionOps, Expr.TyBvarBounded]
      refine And.intro ?_ ((TyBvarBounded_BranchList_append_wildcard n _ _).mpr (And.intro hcases hd))
      trivial
      intro h; cases h

private theorem emitCases_tyBvarBounded (n : Nat) (env : List Occ) (bodies : Nat → Expr)
    (occ : Occ) (cases : List (CtorName × Nat × DTree))
    (hb : ∀ i, (bodies i).TyBvarBounded n) :
    Expr.TyBvarBounded.BranchList n (emitCases env bodies occ cases) := by
  match cases with
  | [] => exact trivial
  | (_c, a, t) :: rest =>
    simp only [emitCases, emitCasesWith, Expr.TyBvarBounded.BranchList]
    exact And.intro (emit_tyBvarBounded n (subOccs occ a ++ env) bodies t hb)
      (emitCases_tyBvarBounded n env bodies occ rest hb)
end

theorem lowerMatch_tyBvarBounded (n : Nat) (scrut : Expr) (pats : List Surface.Pattern)
    (bodies : Nat → Expr)
    (hs : scrut.TyBvarBounded n) (hb : ∀ i, (bodies i).TyBvarBounded n) :
    (lowerMatch scrut pats bodies).TyBvarBounded n := by
  simp only [lowerMatch, lowerMatchWith, coreEmissionOps, Expr.TyBvarBounded]
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
theorem lowerCoreExpr_tyBvarBounded {ke : KindEnv} {tvs vs : List ValName} :
    ∀ {s : Surface.Expr} {c : Expr},
      lowerCoreExpr ke tvs vs s = some c → c.TyBvarBounded tvs.length := by
  intro s c h
  match s with
  | .primLit (.bool _) =>
    simp only [lowerCoreExpr_eqs, Option.some.injEq] at h; subst h; simp [Expr.TyBvarBounded]
  | .primLit .unit | .primLit (.int _) | .primLit (.nat _) | .primLit (.char _) =>
    simp only [lowerCoreExpr_eqs, Option.some.injEq] at h; subst h; simp [Expr.TyBvarBounded]
  | .primBinOp _ =>
    simp only [lowerCoreExpr_eqs, Option.some.injEq] at h; subst h; simp [Expr.TyBvarBounded]
  | .pair a b =>
    simp only [lowerCoreExpr_eqs] at h
    cases ha : lowerCoreExpr ke tvs vs a with
    | none => simp [ha] at h
    | some a' =>
      cases hb : lowerCoreExpr ke tvs vs b with
      | none => simp [ha, hb] at h
      | some b' =>
        simp only [ha, hb, Option.some.injEq] at h; subst h
        simp only [Expr.TyBvarBounded]
        constructor
        · constructor
          · trivial
          · exact lowerCoreExpr_tyBvarBounded ha
        · exact lowerCoreExpr_tyBvarBounded hb
  | .cons hd tl =>
    simp only [lowerCoreExpr_eqs] at h
    cases ha : lowerCoreExpr ke tvs vs hd with
    | none => simp [ha] at h
    | some h' =>
      cases hb : lowerCoreExpr ke tvs vs tl with
      | none => simp [ha, hb] at h
      | some t' =>
        simp only [ha, hb, Option.some.injEq] at h; subst h
        simp only [Expr.TyBvarBounded]
        constructor
        · constructor
          · trivial
          · exact lowerCoreExpr_tyBvarBounded ha
        · exact lowerCoreExpr_tyBvarBounded hb
  | .list items =>
    simp only [lowerCoreExpr_eqs] at h
    cases hi : lowerCoreExprList ke tvs vs items with
    | none => simp [hi] at h
    | some items' =>
      simp only [hi, Option.some.injEq] at h; subst h
      exact mkList_tyBvarBounded tvs.length items' (lowerCoreExprList_tyBvarBounded hi)
  | .lambda param paramAnn body =>
    simp only [lowerCoreExpr_eqs] at h
    cases hann : lowerAnn ke tvs paramAnn with
    | none => simp [hann] at h
    | some ann' =>
      cases param with
      | name x =>
        cases hb : lowerCoreExpr ke tvs (x :: vs) body with
        | none => simp [hann, hb] at h
        | some b' =>
          simp only [hann, hb, Option.some.injEq] at h; subst h
          simp only [Expr.TyBvarBounded]
          exact ⟨lowerAnn_containsBvars hann, lowerCoreExpr_tyBvarBounded hb⟩
      | wildcard =>
        cases hb : lowerCoreExpr ke tvs (.mk "_" :: vs) body with
        | none => simp [hann, hb] at h
        | some b' =>
          simp only [hann, hb, Option.some.injEq] at h; subst h
          simp only [Expr.TyBvarBounded]
          exact ⟨lowerAnn_containsBvars hann, lowerCoreExpr_tyBvarBounded hb⟩
      | ctor n ps =>
        cases hb : lowerCoreExpr ke tvs (patVars (.ctor n ps) ++ .mk "_" :: vs) body with
        | none => simp [hann, hb] at h
        | some b' =>
          simp only [hann, hb, Option.some.injEq] at h; subst h
          simp only [patternLambdaCore, Expr.TyBvarBounded]
          refine ⟨lowerAnn_containsBvars hann, lowerMatch_tyBvarBounded _ _ _ _ trivial ?_⟩
          intro i
          cases i with
          | zero => simpa using lowerCoreExpr_tyBvarBounded hb
          | succ i => simp [List.getD, Expr.TyBvarBounded]
      | pair a b =>
        cases hb : lowerCoreExpr ke tvs (patVars (.pair a b) ++ .mk "_" :: vs) body with
        | none => simp [hann, hb] at h
        | some b' =>
          simp only [hann, hb, Option.some.injEq] at h; subst h
          simp only [patternLambdaCore, Expr.TyBvarBounded]
          refine ⟨lowerAnn_containsBvars hann, lowerMatch_tyBvarBounded _ _ _ _ trivial ?_⟩
          intro i
          cases i with
          | zero => simpa using lowerCoreExpr_tyBvarBounded hb
          | succ i => simp [List.getD, Expr.TyBvarBounded]
      | cons a b =>
        cases hb : lowerCoreExpr ke tvs (patVars (.cons a b) ++ .mk "_" :: vs) body with
        | none => simp [hann, hb] at h
        | some b' =>
          simp only [hann, hb, Option.some.injEq] at h; subst h
          simp only [patternLambdaCore, Expr.TyBvarBounded]
          refine ⟨lowerAnn_containsBvars hann, lowerMatch_tyBvarBounded _ _ _ _ trivial ?_⟩
          intro i
          cases i with
          | zero => simpa using lowerCoreExpr_tyBvarBounded hb
          | succ i => simp [List.getD, Expr.TyBvarBounded]
      | list ps =>
        cases hb : lowerCoreExpr ke tvs (patVars (.list ps) ++ .mk "_" :: vs) body with
        | none => simp [hann, hb] at h
        | some b' =>
          simp only [hann, hb, Option.some.injEq] at h; subst h
          simp only [patternLambdaCore, Expr.TyBvarBounded]
          refine ⟨lowerAnn_containsBvars hann, lowerMatch_tyBvarBounded _ _ _ _ trivial ?_⟩
          intro i
          cases i with
          | zero => simpa using lowerCoreExpr_tyBvarBounded hb
          | succ i => simp [List.getD, Expr.TyBvarBounded]
  | .app f x =>
    simp only [lowerCoreExpr_eqs] at h
    cases hf : lowerCoreExpr ke tvs vs f with
    | none => simp [hf] at h
    | some f' =>
      cases hx : lowerCoreExpr ke tvs vs x with
      | none => simp [hf, hx] at h
      | some x' =>
        simp only [hf, hx, Option.some.injEq] at h; subst h
        simp only [Expr.TyBvarBounded]
        exact ⟨lowerCoreExpr_tyBvarBounded hf, lowerCoreExpr_tyBvarBounded hx⟩
  | .letIn name tyParams params ann rhs body =>
    simp only [lowerCoreExpr_eqs] at h
    cases hann : lowerPolyAnnIn ke tvs (finalizeAnn tyParams params ann) with
    | none => simp [hann] at h
    | some ann' =>
      set tvs' := letAnnTyPrefix tyParams (finalizeAnn tyParams params ann) ++ tvs with htvs'
      cases hr : lowerCoreExpr ke tvs' (paramTermScope params vs) rhs with
      | none => simp [hann, hr] at h
      | some rhsCore =>
        cases hwrap : wrapCoreParams ke tvs' params rhsCore with
        | none => simp [hann, hr, hwrap] at h
        | some rhs' =>
          cases hb : lowerCoreExpr ke tvs (name :: vs) body with
          | none => simp [hann, hr, hwrap, hb] at h
          | some body' =>
            have hEq : some (Expr.letIn ann' rhs' body') = some c := by
              simpa [hann, hr, hwrap, hb] using h
            cases hEq
            cases ann' with
            | none =>
              simp only [Expr.TyBvarBounded]
              refine ⟨?_, lowerCoreExpr_tyBvarBounded hb⟩
              have hF := lowerPolyAnnIn_finalizeAnn_none hann
              have hscopeEq : tvs' = tvs := by
                simp [htvs', letAnnTyPrefix, hF]
              have hr' : lowerCoreExpr ke tvs (paramTermScope params vs) rhs = some rhsCore := by
                simpa [hscopeEq] using hr
              have hwrap' : wrapCoreParams ke tvs params rhsCore = some rhs' := by
                simpa [hscopeEq] using hwrap
              exact wrapCoreParams_tyBvarBounded hwrap' (lowerCoreExpr_tyBvarBounded hr')
            | some σ =>
              simp only [Expr.TyBvarBounded]
              refine ⟨lowerPolyAnnIn_containsBvars hann σ rfl, ?_, lowerCoreExpr_tyBvarBounded hb⟩
              have hpc := lowerPolyAnnIn_some_paramCount hann
              have hlen : tvs'.length = tvs.length + σ.paramCount := by
                simp [htvs', hpc, List.length_append, Nat.add_comm]
              have hrhs := wrapCoreParams_tyBvarBounded hwrap (lowerCoreExpr_tyBvarBounded hr)
              rwa [hlen] at hrhs
  | .letRecIn binds body =>
    simp only [lowerCoreExpr_eqs] at h
    cases hbinds : lowerCoreRecBinds ke tvs (binds.map (·.name) ++ vs) binds with
    | none => simp [hbinds] at h
    | some bindings' =>
      cases hb : lowerCoreExpr ke tvs (binds.map (·.name) ++ vs) body with
      | none => simp [hbinds, hb] at h
      | some body' =>
        have hEq : some (Expr.letRec bindings' body') = some c := by
          simpa [hbinds, hb] using h
        cases hEq
        simp only [Expr.TyBvarBounded]
        refine ⟨Expr.TyBvarBounded.RecGroup_of_forall ?_,
          lowerCoreExpr_tyBvarBounded hb⟩
        intro binding hbinding
        obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hbinding
        have hlen := lowerCoreRecBinds_length hbinds
        have hiB : i < binds.length := by simpa [hlen] using hi
        obtain ⟨rhsCore, hann_i, hr, hwrap⟩ :=
          lowerCoreRecBinds_get hbinds i hiB
        constructor
        · intro σ hσ
          exact lowerPolyAnnIn_containsBvars hann_i σ hσ
        · cases hann : bindings'[i].ann with
          | none =>
            have hF := lowerPolyAnnIn_finalizeAnn_none (hann_i.trans (congrArg some hann))
            have hscopeEq : bindingLowerTyScope binds[i] tvs = tvs := by
              simp [bindingLowerTyScope, letAnnTyPrefix, hF]
            have hrhs := wrapCoreParams_tyBvarBounded hwrap
              (lowerCoreExpr_tyBvarBounded hr)
            simpa [hann, hscopeEq] using hrhs
          | some σ =>
            have hann_some := hann_i.trans (congrArg some hann)
            have hpc := lowerPolyAnnIn_some_paramCount hann_some
            have hrhs := wrapCoreParams_tyBvarBounded hwrap
              (lowerCoreExpr_tyBvarBounded hr)
            have hlen' : (bindingLowerTyScope binds[i] tvs).length =
                tvs.length + RecAnn.params (some σ) := by
              simp [bindingLowerTyScope, RecAnn.params, hpc, List.length_append,
                Nat.add_comm]
            simpa [hann, hlen'] using hrhs
  | .var name =>
    simp only [lowerCoreExpr_eqs] at h
    cases hi : tvarIndex vs name with
    | none => simp [hi] at h
    | some i =>
      simp only [hi, Option.some.injEq] at h; subst h

      trivial
  | .ctor name =>
    simp only [lowerCoreExpr_eqs, Option.some.injEq] at h; subst h; simp [Expr.TyBvarBounded]
  | .ife c t f =>
    simp only [lowerCoreExpr_eqs] at h
    cases hc : lowerCoreExpr ke tvs vs c with
    | none => simp [hc] at h
    | some c' =>
      cases ht : lowerCoreExpr ke tvs vs t with
      | none => simp [hc, ht] at h
      | some t' =>
        cases hf : lowerCoreExpr ke tvs vs f with
        | none => simp [hc, ht, hf] at h
        | some f' =>
          simp only [hc, ht, hf, Option.some.injEq] at h; subst h
          exact lowerMatch_tyBvarBounded tvs.length c' _ _ (lowerCoreExpr_tyBvarBounded hc) (fun i => by
            rw [List.getD]
            match i with
            | 0 => simpa [Option.getD] using lowerCoreExpr_tyBvarBounded ht
            | 1 => simpa [Option.getD] using lowerCoreExpr_tyBvarBounded hf
            | _ + 2 => simp [Option.getD, Expr.TyBvarBounded])
  | .match_ scrut brs =>
    simp only [lowerCoreExpr_eqs] at h
    cases hs : lowerCoreExpr ke tvs vs scrut with
    | none => simp [hs] at h
    | some scrut' =>
      cases hb : lowerCoreBranches ke tvs vs brs with
      | none => simp [hs, hb] at h
      | some bodies' =>
        simp only [hs, hb, Option.some.injEq] at h; subst h
        exact lowerMatch_tyBvarBounded tvs.length scrut' _ (bodyFn bodies')
          (lowerCoreExpr_tyBvarBounded hs) (fun i => by
            change (bodies'.getD i matchBodyDefault).TyBvarBounded tvs.length
            rw [List.getD]
            cases hget : bodies'[i]? with
            | none => simp [Option.getD, matchBodyDefault, Expr.TyBvarBounded]
            | some e =>
              simp only [Option.getD]
              exact lowerCoreBranches_tyBvarBounded hb e (List.mem_of_getElem? hget))
termination_by s => lowerExprSize s
decreasing_by
  all_goals first
    | exact lowerCoreExprSize_pair_left _ _
    | exact lowerCoreExprSize_pair_right _ _
    | exact lowerCoreExprSize_cons_head _ _
    | exact lowerCoreExprSize_cons_tail _ _
    | exact lowerCoreExprSize_app_fn _ _
    | exact lowerCoreExprSize_app_arg _ _
    | exact lowerCoreExprSize_lambda_body _ _ _
    | exact lowerCoreExprSize_letIn_rhs _ _ _ _ _ _
    | exact lowerCoreExprSize_letIn_body _ _ _ _ _ _
    | exact lowerCoreExprSize_letRecIn_body _ _
    | exact lowerCoreExprSize_letRecIn_bind_rhs (by assumption)
    | exact lowerCoreExprSize_letRecIn_bind_rhs_get (by assumption)
    | exact lowerCoreExprSize_letRecIn_bind_rhs_get (by omega)
    | exact lowerCoreExprSize_ife_cond _ _ _
    | exact lowerCoreExprSize_ife_thn _ _ _
    | exact lowerCoreExprSize_ife_else _ _ _
    | exact lowerCoreExprSize_match_scrut
    | exact lowerCoreExprSize_match_branches
    | exact lowerCoreExprSize_match_branch (by assumption)
    | exact lowerCoreExprSize_list_mem (by assumption)
    | exact lowerCoreExprSize_list

theorem lowerCoreExprList_tyBvarBounded {ke : KindEnv} {tvs vs : List ValName} :
    ∀ {es : List Surface.Expr} {es' : List Expr},
      lowerCoreExprList ke tvs vs es = some es' →
      ∀ e ∈ es', e.TyBvarBounded tvs.length := by
  intro es es' h e he
  match es with
  | [] =>
    simp only [lowerCoreExprList_eqs, Option.some.injEq] at h; subst h; cases he
  | e0 :: rest =>
    simp only [lowerCoreExprList_eqs] at h
    cases he0 : lowerCoreExpr ke tvs vs e0 with
    | none => simp [he0] at h
    | some e0' =>
      cases hrest : lowerCoreExprList ke tvs vs rest with
      | none => simp [he0, hrest] at h
      | some rest' =>
        simp only [he0, hrest, Option.some.injEq] at h; subst h
        simp only [List.mem_cons] at he
        rcases he with rfl | he
        · exact lowerCoreExpr_tyBvarBounded he0
        · exact lowerCoreExprList_tyBvarBounded hrest e he
termination_by es => lowerExprListSize es
decreasing_by
  all_goals first
    | exact lowerCoreExprListSize_lt_cons
    | exact lowerCoreExprListSize_pos_mem List.mem_cons_self

theorem lowerCoreBranches_tyBvarBounded {ke : KindEnv} {tvs vs : List ValName} :
    ∀ {brs : List (Surface.Pattern × Surface.Expr)} {bodies' : List Expr},
      lowerCoreBranches ke tvs vs brs = some bodies' →
      ∀ e ∈ bodies', e.TyBvarBounded tvs.length := by
  intro brs bodies' h e he
  match brs with
  | [] =>
    simp only [lowerCoreBranches_eqs, Option.some.injEq] at h; subst h; cases he
  | (p, b) :: rest =>
    simp only [lowerCoreBranches_eqs] at h
    cases hb : lowerCoreExpr ke tvs (patVars p ++ vs) b with
    | none => simp [hb] at h
    | some b' =>
      cases hrest : lowerCoreBranches ke tvs vs rest with
      | none => simp [hb, hrest] at h
      | some rest' =>
        simp only [hb, hrest, Option.some.injEq] at h; subst h
        simp only [List.mem_cons] at he
        rcases he with rfl | he
        · exact lowerCoreExpr_tyBvarBounded hb
        · exact lowerCoreBranches_tyBvarBounded hrest e he
termination_by brs => lowerBranchesSize brs
decreasing_by
  all_goals first
    | exact lowerCoreBranchesSize_lt_cons
    | exact lowerCoreBranchesSize_pos_branch List.mem_cons_self
end

/-- Ambient bridge: with `finalizeAnn = none`, `letRhsTyScope` collapses to ambient `tvs`. -/
private theorem lowerCoreExpr_tyBvarBounded_letRhs_ambient {ke : KindEnv}
    {tyParams : List ValName} {params : List (ValName × Option Surface.Ty)}
    {tvs vs : List ValName} {rhs : Surface.Expr} {e : Expr}
    (hF : finalizeAnn tyParams params (none : Option Surface.PolyTy) = none)
    (hlow : lowerCoreExpr ke (letRhsTyScope tyParams params (none : Option Surface.PolyTy) tvs)
        (letRhsTermScope params vs) rhs = some e) :
    e.TyBvarBounded tvs.length := by
  have hscopeEq : letRhsTyScope tyParams params (none : Option Surface.PolyTy) tvs = tvs := by
    simp [letRhsTyScope, letAnnTyPrefix, hF]
  rw [hscopeEq] at hlow
  exact lowerCoreExpr_tyBvarBounded hlow

/-- `SurfaceWTExpr` ⇒ `lowerCoreExpr` succeeds. -/
theorem lowerCoreExpr_isSome_of_SurfaceWTExpr {ctors : CtorEnv} {ke : KindEnv}
    {tvs vs : List ValName} {Γ : Env} {s : Surface.Expr} {τ : Ty}
    (hwt : SurfaceWTExpr ctors ke tvs vs Γ s τ) :
    (lowerCoreExpr ke tvs vs s).isSome := by
  induction hwt with
  | of_lowers _ hL _ => exact lowerCoreExpr_isSome_of_CoreLowersExpr _ hL
  | pair _ _ _ iha ihb =>
    simp only [lowerCoreExpr_eqs]
    obtain ⟨_, ha⟩ := Option.isSome_iff_exists.mp iha
    obtain ⟨_, hb⟩ := Option.isSome_iff_exists.mp ihb
    simp [ha, hb]
  | cons _ _ _ iha ihb =>
    simp only [lowerCoreExpr_eqs]
    obtain ⟨_, ha⟩ := Option.isSome_iff_exists.mp iha
    obtain ⟨_, hb⟩ := Option.isSome_iff_exists.mp ihb
    simp [ha, hb]
  | list _ _ _ ih =>
    simp only [lowerCoreExpr_eqs]
    obtain ⟨_, hlist'⟩ := Option.isSome_iff_exists.mp (lowerCoreExprList_isSome_of_forall ih)
    simp [hlist']
  | app _ _ ihf ihx =>
    simp only [lowerCoreExpr_eqs]
    obtain ⟨_, hf⟩ := Option.isSome_iff_exists.mp ihf
    obtain ⟨_, hx⟩ := Option.isSome_iff_exists.mp ihx
    simp [hf, hx]
  | lambda_name =>
    rename_i tvs' vs Γ x ann body paramTy bodyTy hIsLC hAnnMatch hBodyWT hBody_ih
    obtain ⟨w, hb⟩ := Option.isSome_iff_exists.mp hBody_ih
    cases hAnn : lowerAnn ke tvs' ann with
    | none =>
      cases ann with
      | none => simp [lowerCoreExpr_eqs, lowerAnn, hb]
      | some τs =>
        have hty : lowerTy ke tvs' τs = some paramTy := hAnnMatch
        simp [lowerAnn, hty] at hAnn
    | some annL => simp [lowerCoreExpr_eqs, hAnn, hb]
  | lambda_wild =>
    rename_i tvs' vs Γ ann body paramTy bodyTy hIsLC hAnnMatch hBodyWT hBody_ih
    obtain ⟨w, hb⟩ := Option.isSome_iff_exists.mp hBody_ih
    cases hAnn : lowerAnn ke tvs' ann with
    | none =>
      cases ann with
      | none => simp [lowerCoreExpr_eqs, lowerAnn, hb]
      | some τs =>
        have hty : lowerTy ke tvs' τs = some paramTy := hAnnMatch
        simp [lowerAnn, hty] at hAnn
    | some annL => simp [lowerCoreExpr_eqs, hAnn, hb]
  | lambda_pattern =>
    rename_i tvs' vs Γ param ann body paramTy bodyTy hp hlc hann hmatched ih
    rw [lowerCoreExpr_patternLambda hp]
    obtain ⟨matched, hm⟩ := Option.isSome_iff_exists.mp ih
    cases ann with
    | none => simp [lowerAnn, hm]
    | some τs => simp [lowerAnn, hann, hm]
  | letIn =>
    rename_i tvs' vs' Γ' ΓRhs name tyParams params rhs body τret τCase τbind paramTys
      hLL hτbind hrhs hbody hrhs_ih hbody_ih
    obtain ⟨rhsCore, hr⟩ := Option.isSome_iff_exists.mp hrhs_ih
    obtain ⟨bodyCore, hb⟩ := Option.isSome_iff_exists.mp hbody_ih
    cases hann : lowerPolyAnn ke (finalizeAnn tyParams params (none : Option Surface.PolyTy)) with
    | none =>
      simp [finalizeAnn_none, lowerPolyAnn] at hann
    | some ann' =>
      cases ann' with
      | none =>
        have hwrap_some := wrapCoreParams_isSome_of_LowerLetParams
          (by simpa [letRhsTyScope_none] using hLL) rhsCore
        obtain ⟨rhs', hwrap⟩ := Option.isSome_iff_exists.mp hwrap_some
        have hr' : lowerCoreExpr ke tvs' (paramTermScope params vs') rhs = some rhsCore := by
          simpa [letRhsTyScope_none, letRhsTermScope] using hr
        simp only [lowerCoreExpr_eqs, finalizeAnn_none, lowerPolyAnnIn, letAnnTyPrefix_none]
        rw [List.nil_append]
        simp [hr', hwrap, hb]
      | some σ =>
        simp [finalizeAnn_none, lowerPolyAnn] at hann
  | letInAnn =>
    rename_i tvs' vs' Γ ΓRhs name tyParams params σs σ rhs body τ L paramTys τretOf
      htvs hσeq hσwf hLL hrhs hτbinds hbody hrhs_ih hbody_ih
    subst htvs
    obtain ⟨Xs, hXlen, hXnodup, hXavoid⟩ := exists_fresh_names L σ.paramCount
    have hfresh : FreshNames L σ.paramCount Xs := ⟨hXlen, hXnodup, hXavoid⟩
    obtain ⟨rhsCore, hr⟩ := Option.isSome_iff_exists.mp (hrhs_ih Xs hfresh)
    obtain ⟨bodyCore, hb⟩ := Option.isSome_iff_exists.mp hbody_ih
    have hwrap_some := wrapCoreParams_isSome_of_LowerLetParams hLL rhsCore
    obtain ⟨rhs', hwrap⟩ := Option.isSome_iff_exists.mp hwrap_some
    -- `lowerCoreExpr` uses `letAnnTyPrefix ++ tvs` with `tvs = []`; same as `letRhsTyScope`.
    have hr' :
        lowerCoreExpr ke
            (letAnnTyPrefix tyParams (finalizeAnn tyParams params (some σs)) ++ [])
          (paramTermScope params vs') rhs = some rhsCore := by
      simpa [letRhsTyScope, letRhsTermScope] using hr
    have hwrap' :
        wrapCoreParams ke
            (letAnnTyPrefix tyParams (finalizeAnn tyParams params (some σs)) ++ [])
          params rhsCore = some rhs' := by
      simpa [letRhsTyScope] using hwrap
    have hσeqIn :
        lowerPolyAnnIn ke [] (finalizeAnn tyParams params (some σs)) = some (some σ) := by
      simpa only [lowerPolyAnnIn_nil] using hσeq
    simp only [lowerCoreExpr_eqs, hσeqIn, hr', hwrap', hb, Option.isSome_some]
  | letRecIn =>
    rename_i tvs' vs' Γ binds τs τrets paramTysList ΓRhsList body τ hlen hrets hparamLen hΓRhsLen
      hann hLL hτbinds hrhs hbody hrhs_ih hbody_ih
    simp only [lowerCoreExpr_eqs]
    obtain ⟨bodyCore, hb⟩ := Option.isSome_iff_exists.mp hbody_ih
    have hanns_forall : ∀ (i : Nat) (hi : i < binds.length),
        (lowerPolyAnnIn ke tvs'
          (finalizeAnn (binds[i]'hi).tyParams (binds[i]'hi).params (binds[i]'hi).ann)).isSome := by
      intro i hi
      have hann_i : (binds[i]'hi).ann = (none : Option Surface.PolyTy) :=
        hann _ (List.getElem_mem hi)
      simp [hann_i, finalizeAnn_none, lowerPolyAnnIn]
    have hbinds_forall : ∀ (i : Nat) (hi : i < binds.length),
        ∃ rhsCore,
          lowerCoreExpr ke (bindingLowerTyScope (binds[i]'hi) tvs')
              (paramTermScope (binds[i]'hi).params (binds.map (·.name) ++ vs'))
              (binds[i]'hi).rhs = some rhsCore ∧
          (wrapCoreParams ke (bindingLowerTyScope (binds[i]'hi) tvs')
              (binds[i]'hi).params rhsCore).isSome := by
      intro i hi
      have hann_i : (binds[i]'hi).ann = (none : Option Surface.PolyTy) :=
        hann _ (List.getElem_mem hi)
      have hscope : bindingLowerTyScope (binds[i]'hi) tvs' =
          letRhsTyScope (binds[i]'hi).tyParams (binds[i]'hi).params
            (none : Option Surface.PolyTy) tvs' := by
        simp [bindingLowerTyScope, letRhsTyScope, hann_i, finalizeAnn_none, letAnnTyPrefix]
      obtain ⟨c, hc⟩ := Option.isSome_iff_exists.mp (hrhs_ih i hi)
      refine ⟨c, ?_, ?_⟩
      · simpa [hscope, letRhsTermScope] using hc
      · simpa [hscope] using wrapCoreParams_isSome_of_LowerLetParams (hLL i hi) c
    obtain ⟨_, hbinds'⟩ := Option.isSome_iff_exists.mp
      (lowerCoreRecBinds_isSome_of_forall hanns_forall hbinds_forall)
    simp [hbinds', hb]
  | letRecInAnn =>
    rename_i tvs' vs' Γ binds anns' specs G L paramTysList ΓRhsList τretsList body τ
      htvs hann hlen hparamLen hΓRhsLen hretsLen hanns_eq hnodup hmono_lc hpoly_wf
      hLLMono hLLPoly hτbindsMono hτbindsPoly hmono hpoly hbody hmono_ih hpoly_ih hbody_ih
    subst htvs
    simp only [lowerCoreExpr_eqs]
    have hannIn : lowerAnnListIn ke []
        (binds.map fun b => finalizeAnn b.tyParams b.params b.ann) = some anns' := by
      simpa only [lowerAnnListIn_nil] using hann
    obtain ⟨bodyCore, hb⟩ := Option.isSome_iff_exists.mp hbody_ih
    have hanns_forall : ∀ (i : Nat) (hi : i < binds.length),
        (lowerPolyAnnIn ke []
          (finalizeAnn (binds[i]'hi).tyParams (binds[i]'hi).params (binds[i]'hi).ann)).isSome := by
      intro i hi
      exact Option.isSome_iff_exists.mpr
        ⟨_, lowerAnnListIn_getElem_ann hannIn hi⟩
    have hbinds_forall : ∀ (i : Nat) (hi : i < binds.length),
        ∃ rhsCore,
          lowerCoreExpr ke (bindingLowerTyScope (binds[i]'hi) [])
              (paramTermScope (binds[i]'hi).params (binds.map (·.name) ++ vs'))
              (binds[i]'hi).rhs = some rhsCore ∧
          (wrapCoreParams ke (bindingLowerTyScope (binds[i]'hi) [])
              (binds[i]'hi).params rhsCore).isSome := by
      intro i hi
      have hscope : bindingLowerTyScope (binds[i]'hi) [] =
          letRhsTyScope (binds[i]'hi).tyParams (binds[i]'hi).params (binds[i]'hi).ann [] := by
        simp [bindingLowerTyScope, letRhsTyScope]
      obtain ⟨Xs, hXlen, hXnodup, hXavoid⟩ := exists_fresh_names L G.length
      have hfresh : FreshNames L G.length Xs := ⟨hXlen, hXnodup, hXavoid⟩
      have assemble : ∀ {Γ0 ΓR : Env} {paramTys : List Ty},
          LowerLetParams ke
            (letRhsTyScope (binds[i]'hi).tyParams (binds[i]'hi).params
              (binds[i]'hi).ann [])
            (binds[i]'hi).params Γ0 ΓR paramTys →
          (lowerCoreExpr ke (letRhsTyScope (binds[i]'hi).tyParams (binds[i]'hi).params
              (binds[i]'hi).ann [])
            (letRhsTermScope (binds[i]'hi).params (binds.map (·.name) ++ vs'))
            (binds[i]'hi).rhs).isSome →
          ∃ rhsCore,
            lowerCoreExpr ke (bindingLowerTyScope (binds[i]'hi) [])
              (paramTermScope (binds[i]'hi).params (binds.map (·.name) ++ vs'))
              (binds[i]'hi).rhs = some rhsCore ∧
            (wrapCoreParams ke (bindingLowerTyScope (binds[i]'hi) [])
              (binds[i]'hi).params rhsCore).isSome := by
        intro Γ0 ΓR paramTys hparams hlower
        obtain ⟨c, hc⟩ := Option.isSome_iff_exists.mp hlower
        refine ⟨c, ?_, ?_⟩
        · simpa [hscope, letRhsTermScope] using hc
        · simpa [hscope] using
            wrapCoreParams_isSome_of_LowerLetParams hparams c
      cases hs : specs[i]'(Nat.lt_of_lt_of_eq hi hlen) with
      | mono τm =>
          exact assemble (hLLMono Xs hfresh i hi τm hs)
            (hmono_ih Xs hfresh i hi τm hs)
      | poly σ =>
          obtain ⟨Ys, hYlen, hYnodup, hYavoid⟩ :=
            exists_fresh_names L σ.paramCount
          have hYfresh : FreshNames L σ.paramCount Ys :=
            ⟨hYlen, hYnodup, hYavoid⟩
          exact assemble (hLLPoly i hi σ hs Ys hYfresh)
            (hpoly_ih i hi σ hs Ys hYfresh)
    obtain ⟨_, hbinds'⟩ := Option.isSome_iff_exists.mp
      (lowerCoreRecBinds_isSome_of_forall hanns_forall hbinds_forall)
    simp [hbinds', hb]
  | match_ _ _ _ _ _ _ ihs ihbrs =>
    simp only [lowerCoreExpr_eqs]
    obtain ⟨_, hs⟩ := Option.isSome_iff_exists.mp ihs
    obtain ⟨_, hb'⟩ := Option.isSome_iff_exists.mp (lowerCoreBranches_isSome_of_forall ihbrs)
    simp [hs, hb']
  | ife _ _ _ _ _ _ _ ihc iht ihf =>
    simp only [lowerCoreExpr_eqs]
    obtain ⟨_, hc⟩ := Option.isSome_iff_exists.mp ihc
    obtain ⟨_, ht⟩ := Option.isSome_iff_exists.mp iht
    obtain ⟨_, hf⟩ := Option.isSome_iff_exists.mp ihf
    simp [hc, ht, hf]

/-! ### Annotation well-scopedness from declarative typing -/

/-- Every annotation in a declaratively well-typed expression is locally
    well-scoped. This follows directly from the annotation premises of
    `TypeOfHM`; term variables carry no type decorations. -/
theorem TypeOfHM.tyBvarBounded {ctx : Ctx} {e : Expr} {τ : Ty}
    (h : TypeOfHM ctx e τ) : e.TyBvarBounded 0 := by
  induction h using TypeOfHM.rec
      (motive_2 := fun _ branch _ _ _ => branch.2.TyBvarBounded 0) with
  | primLitUnit | primLitInt | primLitNat | primLitChar => trivial
  | primBinOpIntAdd | primBinOpIntSub => trivial
  | primBinOpIntLt | primBinOpCharLt => trivial
  | app _ _ ihf iha => exact ⟨ihf, iha⟩
  | var _ _ _ => trivial
  | ctor => trivial
  | lambda hpc hann _ _ ih =>
    refine ⟨?_, ih⟩
    intro t ht
    have := hann t ht
    simpa [this] using hpc
  | letIn hwf hann _ _ _ ihgen ihbody =>
    expose_names
    cases hann_ann : ann with
    | none =>
      simp only [Expr.TyBvarBounded]
      refine ⟨?_, ihbody⟩
      obtain ⟨Xs, hXlen, hXnodup, hXavoid⟩ := exists_fresh_names L M.paramCount
      have := ihgen Xs ⟨hXlen, hXnodup, hXavoid⟩
      rw [hann_ann] at this
      simpa only [Expr.openBoundTyVars] using this
    | some σ =>
      have hMσ : M = σ := hann σ hann_ann
      subst hMσ
      simp only [Expr.TyBvarBounded]
      refine ⟨by simpa using hwf, ?_, ihbody⟩
      obtain ⟨Xs, hXlen, hXnodup, hXavoid⟩ := exists_fresh_names L M.paramCount
      have hc := ihgen Xs ⟨hXlen, hXnodup, hXavoid⟩
      rw [hann_ann] at hc
      simp only [Expr.openBoundTyVars] at hc
      have := Expr.tyBvarBounded_of_openTyVarsAux Xs boundExpr 0
        (by simpa only [Expr.openTyVars] using hc)
      simpa only [Nat.zero_add, hXlen] using this
  | match_ _ _ _ ihscrut ihbrs =>
    expose_names
    refine ⟨ihscrut, ?_⟩
    rw [Expr.TyBvarBounded.BranchList_iff]
    intro p b hmem
    exact ihbrs (p, b) hmem
  | letRec hgroups hwf hmono hpoly heq hbody ihmono ihpoly ihbody =>
    expose_names
    refine ⟨Expr.TyBvarBounded.RecGroup_of_forall ?_, ihbody⟩
    intro binding hbindingMem
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hbindingMem
    have hiS : i < specs.length := by
      simpa [hwf.length] using hi
    have hann' : (specs[i]'hiS).ann = bindings[i].ann := by
      have hannAt := congrArg (fun xs => xs[i]?) hwf.anns_eq
      simpa [List.getElem?_map, hiS, hi] using hannAt
    constructor
    · intro σ hσ
      have hs : specs[i]'hiS = .poly σ :=
        RecSpec.ann_eq_some (hann'.trans hσ)
      simpa [PolyTy.WF] using hwf.poly_wf σ (hs ▸ List.getElem_mem hiS)
    · obtain ⟨Xs, hXlen, hXnodup, hXavoid⟩ := exists_fresh_names L G.length
      have hfresh : FreshNames L G.length Xs := ⟨hXlen, hXnodup, hXavoid⟩
      have hmem : (bindings[i]'hi, specs[i]'hiS) ∈ bindings.zip specs :=
        List.getElem_mem_zip hi hiS
      cases hs : specs[i]'hiS with
      | mono τm =>
          have hannNone : bindings[i].ann = none := by
            simpa [hs, RecSpec.ann] using hann'.symm
          have hunsigned : RecGroups.UnsignedAt bindings i := by
            simp [RecGroups.UnsignedAt, hi, hannNone]
          have hmemGroups : i ∈ groups.flatten := by
            exact (hgroups.covers_unsigned i hi).2 hunsigned
          obtain ⟨component, hcomponentMem, hiComponent⟩ :=
            List.mem_flatten.mp hmemGroups
          obtain ⟨stage, hstage, hcomponentEq⟩ :=
            List.mem_iff_getElem.mp hcomponentMem
          have hcomponent : groups[stage]? = some component := by
            simp [hstage, hcomponentEq]
          have hbinding : bindings[i]? = some bindings[i] := by simp [hi]
          have hspec : specs[i]? = some (.mono τm) := by
            simp [hiS, hs]
          have hb0 := ihmono stage component hcomponent Xs hfresh i hiComponent
            bindings[i] τm
            hbinding hspec
          simpa [hannNone, RecAnn.params] using hb0
      | poly σ =>
          obtain ⟨Ys, hYlen, hYnodup, hYavoid⟩ :=
            exists_fresh_names L σ.paramCount
          have hb0 := ihpoly (bindings[i], .poly σ) (hs ▸ hmem) σ rfl Ys
            ⟨hYlen, hYnodup, hYavoid⟩
          have hb := Expr.tyBvarBounded_of_openTyVarsAux Ys bindings[i].rhs 0
            (by simpa only [Expr.openTyVars] using hb0)
          have hσann : bindings[i].ann = some σ := by
            simpa [hs, RecSpec.ann] using hann'.symm
          simpa only [hσann, RecAnn.params, Nat.zero_add, hYlen] using hb
  | mk _ _ _ ih => exact ih
  | wildcard _ ih => exact ih

/-- **Rung 3.** Open transfer: `SurfaceWTExpr` + `lowerCoreExpr` ⇒ `TypeOfHM` at same `τ`. -/
theorem TypeOfHM_of_lowerExpr_of_SurfaceWTExpr {ctors : CtorEnv} {ke : KindEnv}
    {tvs vs : List ValName} {Γ : Env} {s : Surface.Expr} {c : Expr} {τ : Ty}
    (hwt : SurfaceWTExpr ctors ke tvs vs Γ s τ)
    (hlow : lowerCoreExpr ke tvs vs s = some c)
    (hcons : CtorEnv.arityConsistent ctors)
    (hfields : CtorEnv.fieldsKinded ctors) :
    TypeOfHM ⟨Γ, ctors⟩ c τ := by
  induction hwt generalizing c with
  | of_lowers hnm hL hT =>
    have heq := lowerCoreExpr_eq_of_CoreLowersExpr_of_NoMatch hnm hL hlow
    simpa [heq] using hT
  | pair =>
    rename_i tvs' vs Γ a b τa τb τ ha hb hctor iha ihb
    simp only [lowerCoreExpr_eqs] at hlow
    cases haL : lowerCoreExpr ke tvs' vs a with
    | none => simp [haL] at hlow
    | some aL =>
      cases hbL : lowerCoreExpr ke tvs' vs b with
      | none => simp [haL, hbL] at hlow
      | some bL =>
        simp only [haL, hbL, Option.some.injEq] at hlow; subst hlow
        exact TypeOfHM.app (TypeOfHM.app hctor (iha haL)) (ihb hbL)
  | cons =>
    rename_i tvs' vs Γ h t τh τt τ hh ht hctor ihh iht
    simp only [lowerCoreExpr_eqs] at hlow
    cases hhL : lowerCoreExpr ke tvs' vs h with
    | none => simp [hhL] at hlow
    | some hL =>
      cases htL : lowerCoreExpr ke tvs' vs t with
      | none => simp [hhL, htL] at hlow
      | some tL =>
        simp only [hhL, htL, Option.some.injEq] at hlow; subst hlow
        exact TypeOfHM.app (TypeOfHM.app hctor (ihh hhL)) (iht htL)
  | list =>
    rename_i tvs' vs Γ items τelem hitems hnil hconsC ih
    simp only [lowerCoreExpr_eqs] at hlow
    cases hi : lowerCoreExprList ke tvs' vs items with
    | none => simp [hi] at hlow
    | some items' =>
      simp only [hi, Option.some.injEq] at hlow; subst hlow
      have ⟨hlen, hget⟩ := lowerCoreExprList_length_get hi
      apply mkList_TypeOfHM hnil hconsC
      intro e' he'
      obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp he'
      have hiS : i < items.length := by omega
      obtain ⟨_, hlowi⟩ := hget i hiS
      exact ih (items[i]'hiS) (List.getElem_mem hiS) hlowi
  | app =>
    rename_i tvs' vs Γ f x τarg τ hf hx ihf ihx
    simp only [lowerCoreExpr_eqs] at hlow
    cases hfL : lowerCoreExpr ke tvs' vs f with
    | none => simp [hfL] at hlow
    | some fL =>
      cases hxL : lowerCoreExpr ke tvs' vs x with
      | none => simp [hfL, hxL] at hlow
      | some xL =>
        simp only [hfL, hxL, Option.some.injEq] at hlow; subst hlow
        exact TypeOfHM.app (ihf hfL) (ihx hxL)
  | lambda_name =>
    rename_i tvs' vs Γ x ann body paramTy bodyTy hIsLC hAnnMatch hBodyWT hBody_ih
    simp only [lowerCoreExpr_eqs] at hlow
    cases hann : lowerAnn ke tvs' ann with
    | none =>
      cases ann with
      | none => simp [lowerAnn] at hann
      | some τs =>
        have hty : lowerTy ke tvs' τs = some paramTy := hAnnMatch
        simp [lowerAnn, hty] at hann
    | some annOpt =>
      cases hbL : lowerCoreExpr ke tvs' (x :: vs) body with
      | none => simp [hbL, hann] at hlow
      | some bL =>
        cases annOpt with
        | none =>
          have hc : c = Expr.lambda (none : Option Ty) bL := by
            simp only [hann, hbL, Option.some.injEq] at hlow
            exact hlow.symm
          subst hc
          have hpins : (none : Option Ty).Pins paramTy := fun _ ha => by cases ha
          exact TypeOfHM.lambda hIsLC hpins rfl (hBody_ih hbL)
        | some annTy =>
          have hc : c = Expr.lambda (some annTy) bL := by
            simp only [hann, hbL, Option.some.injEq] at hlow
            exact hlow.symm
          subst hc
          have hpins : (some annTy).Pins paramTy := by
            intro a ha
            have ha' : annTy = a := Option.some.inj ha
            cases ann with
            | none =>
              simp [lowerAnn] at hann
            | some τs =>
              have hty : lowerTy ke tvs' τs = some paramTy := hAnnMatch
              have hann' : lowerAnn ke tvs' (some τs) = some (some paramTy) := by
                simp [lowerAnn, hty, Option.map_some]
              have hannTy : annTy = paramTy :=
                Option.some.inj (Option.some.inj (hann.symm.trans hann'))
              exact hannTy.symm.trans ha'
          exact TypeOfHM.lambda hIsLC hpins rfl (hBody_ih hbL)
  | lambda_wild =>
    rename_i tvs' vs Γ ann body paramTy bodyTy hIsLC hAnnMatch hBodyWT hBody_ih
    simp only [lowerCoreExpr_eqs] at hlow
    cases hann : lowerAnn ke tvs' ann with
    | none =>
      cases ann with
      | none => simp [lowerAnn] at hann
      | some τs =>
        have hty : lowerTy ke tvs' τs = some paramTy := hAnnMatch
        simp [lowerAnn, hty] at hann
    | some annOpt =>
      cases hbL : lowerCoreExpr ke tvs' (ValName.mk "_" :: vs) body with
      | none => simp [hbL, hann] at hlow
      | some bL =>
        cases annOpt with
        | none =>
          have hc : c = Expr.lambda (none : Option Ty) bL := by
            simp only [hann, hbL, Option.some.injEq] at hlow
            exact hlow.symm
          subst hc
          have hpins : (none : Option Ty).Pins paramTy := fun _ ha => by cases ha
          exact TypeOfHM.lambda hIsLC hpins rfl (hBody_ih hbL)
        | some annTy =>
          have hc : c = Expr.lambda (some annTy) bL := by
            simp only [hann, hbL, Option.some.injEq] at hlow
            exact hlow.symm
          subst hc
          have hpins : (some annTy).Pins paramTy := by
            intro a ha
            have ha' : annTy = a := Option.some.inj ha
            cases ann with
            | none =>
              simp [lowerAnn] at hann
            | some τs =>
              have hty : lowerTy ke tvs' τs = some paramTy := hAnnMatch
              have hann' : lowerAnn ke tvs' (some τs) = some (some paramTy) := by
                simp [lowerAnn, hty, Option.map_some]
              have hannTy : annTy = paramTy :=
                Option.some.inj (Option.some.inj (hann.symm.trans hann'))
              exact hannTy.symm.trans ha'
          exact TypeOfHM.lambda hIsLC hpins rfl (hBody_ih hbL)
  | lambda_pattern =>
    rename_i tvs' vs Γ param ann body paramTy bodyTy hp hlc hann hmatched ih
    rw [lowerCoreExpr_patternLambda hp] at hlow
    have hmExists := lowerCoreExpr_isSome_of_SurfaceWTExpr hmatched
    obtain ⟨matched, hm⟩ := Option.isSome_iff_exists.mp hmExists
    have hty := ih hm
    cases ann with
    | none =>
      simp only [lowerAnn, hm, Option.some.injEq] at hlow
      subst hlow
      exact TypeOfHM.lambda hlc (fun _ h => by cases h) rfl hty
    | some τs =>
      simp only [lowerAnn, hann, Option.map_some, hm, Option.some.injEq] at hlow
      subst hlow
      exact TypeOfHM.lambda hlc (fun _ h => Option.some.inj h) rfl hty
  | letIn =>
    rename_i tvs' vs' Γ' ΓRhs name tyParams params rhs body τret τCase τbind paramTys
      hLL hτbind hrhs hbody hrhs_ih hbody_ih
    obtain ⟨ann', rhsCore, rhsL, bodyL, hann, hrL, hwrap, hbL, rfl⟩ :=
      lowerCoreExpr_letIn_decomp hlow
    have hann_none : ann' = none := by
      have : lowerPolyAnnIn ke tvs'
          (finalizeAnn tyParams params (none : Option Surface.PolyTy)) =
          some none := by
        rw [finalizeAnn_none]
        rfl
      exact Option.some.inj (hann.symm.trans this)
    subst hann_none
    have hTyR := hrhs_ih hrL
    have hTyW : TypeOfHM ⟨Γ', ctors⟩ rhsL τbind := by
      have w := wrapCoreParams_TypeOfHM hLL hwrap hTyR
      exact hτbind ▸ w
    refine TypeOfHM.letIn (M := PolyTy.mkTrivial τbind) (L := [])
      (TypeOfHM.regular hTyW) (fun _ h => Option.noConfusion h)
      (generalisesTo_of_typeable hTyW) rfl (hbody_ih hbL)
  | letInAnn =>
    rename_i tvs' vs' Γ ΓRhs name tyParams params σs σ rhs body τ L paramTys τretOf
      htvs hσeq hσwf hLL hrhs hτbinds hbody hrhs_ih hbody_ih
    subst htvs
    obtain ⟨ann', rhsCore, rhsL, bodyL, hann, hrL, hwrap, hbL, rfl⟩ :=
      lowerCoreExpr_letIn_decomp hlow
    have hσeqIn : lowerPolyAnnIn ke []
        (finalizeAnn tyParams params (some σs)) = some (some σ) := by
      simpa only [lowerPolyAnnIn_nil] using hσeq
    have hannσ : ann' = some σ := Option.some.inj (hann.symm.trans hσeqIn)
    subst hannσ
    have hpins : (some σ).Pins σ := fun _ ha => Option.some.inj ha
    refine TypeOfHM.letIn (M := σ) (L := L) hσwf hpins ?_ rfl (hbody_ih hbL)
    intro Xs hfresh
    have hTyR := hrhs_ih Xs hfresh hrL
    have hTyW : TypeOfHM ⟨Γ, ctors⟩ rhsL (coreParamsToArrows paramTys (τretOf Xs)) :=
      wrapCoreParams_TypeOfHM hLL hwrap hTyR
    have hTyOpen : TypeOfHM ⟨Γ, ctors⟩ rhsL (σ.openVars Xs) :=
      (hτbinds Xs hfresh) ▸ hTyW
    -- Declarative typing bounds every embedded annotation, so opening the
    -- enclosing scheme variables is a no-op on this already lowered RHS.
    have hb0 : rhsL.TyBvarBounded 0 := TypeOfHM.tyBvarBounded hTyOpen
    simp only [Expr.openBoundTyVars, Expr.openTyVars]
    rwa [Expr.openTyVarsAux_eq_self_of_tyBvarBounded Xs rhsL 0 hb0]
  | letRecIn =>
    rename_i tvs' vs' Γ binds τs τrets paramTysList ΓRhsList body τ
      hlen hrets hparamLen hΓRhsLen hann hLL hτbinds hrhs hbody hrhs_ih hbody_ih
    obtain ⟨members, bodyL, hbindsL, hbL, hc⟩ :=
      lowerCoreExpr_letRecIn_decomp (binds := binds) (body := body) hlow
    subst hc
    let annsL := members.map (·.ann)
    have hann' := @lowerAnnListIn_finalizeAnn_none ke tvs' binds hann
    have hannL := lowerCoreRecBinds_anns hbindsL
    have anns_eq : annsL = List.replicate binds.length (none : Option PolyTy) := by
      exact Option.some.inj (hannL.symm.trans hann')
    have hlenB : members.length = binds.length := lowerCoreRecBinds_length hbindsL
    have hgetB := lowerCoreRecBinds_get hbindsL
    set specs : List RecSpec := τs.map RecSpec.mono with hspecs
    have hanns_eq : specs.map RecSpec.ann = annsL := by
      simpa [specs, hlen, anns_eq] using RecSpec.map_ann_mono τs
    have hgroups : RecGroups.ValidResidualGroups members
        (oneResidualGroup members) := oneResidualGroup_valid
    have hgroups_eq : oneResidualGroup members =
        if members.length = 0 then [] else [List.range members.length] := by
      rw [oneResidualGroup]
      have hfilter :
          List.filter (RecGroups.unsignedAtB members) (List.range members.length) =
            List.range members.length := by
        apply List.filter_eq_self.mpr
        intro member hmember
        have hbound := List.mem_range.mp hmember
        apply (RecGroups.unsignedAtB_eq_true_iff members member).mpr
        simp only [RecGroups.UnsignedAt]
        rw [← List.getElem?_map]
        change annsL[member]? = some none
        calc
          annsL[member]? = (List.replicate binds.length (none : Option PolyTy))[member]? :=
            congrArg (fun xs => xs[member]?) anns_eq
          _ = some none := by
            apply List.getElem?_eq_some_iff.mpr
            have hm : member < binds.length := by omega
            have hr : member < (List.replicate binds.length
                (none : Option PolyTy)).length := by simpa using hm
            exact ⟨hr, List.getElem_replicate hr⟩
      rw [hfilter]
      by_cases hnil : members.length = 0 <;> simp [hnil]
    have hscope_i : ∀ (i : Nat) (hi : i < binds.length),
        bindingLowerTyScope (binds[i]'hi) tvs' =
          letRhsTyScope (binds[i]'hi).tyParams (binds[i]'hi).params
            (none : Option Surface.PolyTy) tvs' := by
      intro i hi
      have hann_i : (binds[i]'hi).ann = (none : Option Surface.PolyTy) :=
        hann _ (List.getElem_mem hi)
      simp [bindingLowerTyScope, letRhsTyScope, hann_i, finalizeAnn_none, letAnnTyPrefix]
    have hwf : RecSpecs.WF members specs [] := by
      refine ⟨hanns_eq, List.nodup_nil, ?_, ?_⟩
      · intro τm hτ
        simp only [specs, List.mem_map] at hτ
        obtain ⟨τ', hτ', hτeq⟩ := hτ
        cases hτeq
        obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hτ'
        have hiB : i < binds.length := by omega
        obtain ⟨rhsCore, _hann, hr, hwrap⟩ := hgetB i hiB
        have hr' :
            lowerCoreExpr ke (letRhsTyScope (binds[i]'hiB).tyParams (binds[i]'hiB).params
                (none : Option Surface.PolyTy) tvs')
              (letRhsTermScope (binds[i]'hiB).params (binds.map (·.name) ++ vs'))
              (binds[i]'hiB).rhs = some rhsCore := by
          simpa [hscope_i i hiB, letRhsTermScope] using hr
        have hwrap' :
            wrapCoreParams ke (letRhsTyScope (binds[i]'hiB).tyParams (binds[i]'hiB).params
                (none : Option Surface.PolyTy) tvs') (binds[i]'hiB).params rhsCore =
              some (members[i]'(by omega : i < members.length)).rhs := by
          simpa [hscope_i i hiB] using hwrap
        have hTyW := wrapCoreParams_TypeOfHM (hLL i hiB) hwrap' (hrhs_ih i hiB hr')
        exact TypeOfHM.regular (by simpa [← hτbinds i hiB] using hTyW)
      · intro σ hσ
        simp only [specs, List.mem_map] at hσ
        obtain ⟨_, _, hcontrad⟩ := hσ
        cases hcontrad
    refine TypeOfHM.letRec (specs := specs) (groups := oneResidualGroup members)
      (G := []) (L := []) hgroups hwf ?mono ?poly rfl ?body
    · intro stage component hcomponent Xs hXs member hmember binding τm hbinding hτm
      rw [hgroups_eq] at hcomponent
      have hzero : members.length ≠ 0 := by
        intro hz
        simp [hz] at hcomponent
      rw [if_neg hzero] at hcomponent
      have hlookup := List.getElem?_eq_some_iff.mp hcomponent
      have hstageLt : stage < 1 := by simpa using hlookup.1
      have hstage : stage = 0 := by omega
      subst stage
      have hcomponent_eq : component = List.range members.length := by
        simpa using hlookup.2.symm
      subst component
      have hiB : member < members.length := List.mem_range.mp hmember
      have hbinding' := List.getElem?_eq_some_iff.mp hbinding
      have hiRhs : member < members.length := hbinding'.1
      have hbindingEq : members[member]'hiRhs = binding := hbinding'.2
      have hspec' : τs[member]? = some τm := by
        cases hopt : τs[member]? with
        | none => simp [specs, hopt] at hτm
        | some τ' =>
          have heq : τ' = τm := by simpa [specs, hopt] using hτm
          exact congrArg some heq
      have hτs' := List.getElem?_eq_some_iff.mp hspec'
      have hiTy : member < τs.length := hτs'.1
      have hτsEq : τs[member]'hiTy = τm := hτs'.2
      have hiBind : member < binds.length := by omega
      obtain ⟨rhsCore, _hann, hr, hwrap⟩ := hgetB member hiBind
      have hr' :
          lowerCoreExpr ke (letRhsTyScope (binds[member]'hiBind).tyParams
              (binds[member]'hiBind).params (none : Option Surface.PolyTy) tvs')
            (letRhsTermScope (binds[member]'hiBind).params (binds.map (·.name) ++ vs'))
            (binds[member]'hiBind).rhs = some rhsCore := by
        simpa [hscope_i member hiBind, letRhsTermScope] using hr
      have hwrap' :
          wrapCoreParams ke (letRhsTyScope (binds[member]'hiBind).tyParams
              (binds[member]'hiBind).params (none : Option Surface.PolyTy) tvs')
            (binds[member]'hiBind).params rhsCore = some (members[member]'hiRhs).rhs := by
        simpa [hscope_i member hiBind] using hwrap
      have hTyW := wrapCoreParams_TypeOfHM
        (hLL member hiBind) hwrap' (hrhs_ih member hiBind hr')
      simp only [List.take_zero, List.flatten_nil, RecSpecs.stageCtx]
      rw [stageEntries_none_eq_rhsEntries]
      simpa [RecSpecs.rhsCtx, RecSpec.rhsEntry, specs, hbindingEq,
        ← hτsEq, ← hτbinds member hiBind] using hTyW
    · intro p hp σ hσ
      have hs : p.2 ∈ specs := (List.of_mem_zip hp).2
      rw [hσ] at hs
      simp [specs] at hs
    · simp only [RecSpecs.bodyCtx, specs, List.map_map]
      have hmap : List.map (RecSpec.bodyScheme [] ∘ RecSpec.mono) τs =
          τs.map PolyTy.mkTrivial :=
        List.map_congr_left fun _ _ => RecSpec.bodyScheme_nil_mono
      rw [hmap]
      exact hbody_ih hbL
  | letRecInAnn =>
    rename_i tvs' vs' Γ binds anns' specs G L paramTysList ΓRhsList τretsList body τ
      htvs hann hlen hparamLen hΓRhsLen hretsLen hanns_eq hnodup hmono_lc hpoly_wf
      hLLMono hLLPoly hτbindsMono hτbindsPoly hmono hpoly hbody hmono_ih hpoly_ih hbody_ih
    subst htvs
    obtain ⟨members, bodyL, hbindsL, hbL, hc⟩ :=
      lowerCoreExpr_letRecIn_decomp (binds := binds) (body := body) hlow
    subst hc
    let annsL := members.map (·.ann)
    have hannL := lowerCoreRecBinds_anns hbindsL
    have hlenB : members.length = binds.length := lowerCoreRecBinds_length hbindsL
    have hgetB := lowerCoreRecBinds_get hbindsL
    have hannIn : lowerAnnListIn ke []
        (binds.map fun b => finalizeAnn b.tyParams b.params b.ann) = some anns' := by
      simpa only [lowerAnnListIn_nil] using hann
    have anns_eq : annsL = anns' := Option.some.inj (hannL.symm.trans hannIn)
    have hwf : RecSpecs.WF members specs G :=
      ⟨by simpa [annsL] using hanns_eq.trans anns_eq.symm,
        hnodup, hmono_lc, hpoly_wf⟩
    have hgroups : RecGroups.ValidResidualGroups members
        (oneResidualGroup members) := oneResidualGroup_valid
    refine TypeOfHM.letRec (specs := specs) (groups := oneResidualGroup members)
      (G := G) (L := L) hgroups hwf ?_ ?_ rfl ?_
    · intro stage component hcomponent Xs hfresh member hmember binding τm hbinding hτm
      let unsignedMembers :=
        (List.range members.length).filter (RecGroups.unsignedAtB members)
      have hmembers_ne : unsignedMembers ≠ [] := by
        intro hnil
        simp [oneResidualGroup, unsignedMembers, hnil] at hcomponent
      simp only [oneResidualGroup, unsignedMembers, hmembers_ne] at hcomponent
      have hlookup := List.getElem?_eq_some_iff.mp hcomponent
      have hstageLt : stage < 1 := by simpa using hlookup.1
      have hstage : stage = 0 := by omega
      subst stage
      have hcomponent_eq : component = unsignedMembers := by
        simpa using hlookup.2.symm
      subst component
      have hiCore : member < members.length := hgroups.bounded member (by
        simpa [oneResidualGroup, unsignedMembers, hmembers_ne] using hmember)
      have hiB : member < binds.length := by omega
      have hiSpec : member < specs.length := by
        rw [← hwf.length]
        exact hiCore
      have hspecLookup := List.getElem?_eq_some_iff.mp hτm
      have hspec : specs[member]'hiSpec = .mono τm := hspecLookup.2
      have hbindingLookup := List.getElem?_eq_some_iff.mp hbinding
      have hbindingEq : members[member]'hbindingLookup.1 = binding := hbindingLookup.2
      obtain ⟨rhsCore, _hann, hr, hwrap⟩ := hgetB member hiB
      have hr' :
          lowerCoreExpr ke (letRhsTyScope (binds[member]'hiB).tyParams (binds[member]'hiB).params
              (binds[member]'hiB).ann [])
            (letRhsTermScope (binds[member]'hiB).params (binds.map (·.name) ++ vs'))
            (binds[member]'hiB).rhs = some rhsCore := by
        simpa [bindingLowerTyScope, letRhsTyScope, letRhsTermScope, paramTermScope] using hr
      have hwrap' :
          wrapCoreParams ke (letRhsTyScope (binds[member]'hiB).tyParams (binds[member]'hiB).params
              (binds[member]'hiB).ann []) (binds[member]'hiB).params rhsCore =
            some (members[member]'hiCore).rhs := by
        simpa [bindingLowerTyScope, letRhsTyScope] using hwrap
      have hTyR := hmono_ih Xs hfresh member hiB τm hspec hr'
      have hTyW := wrapCoreParams_TypeOfHM
        (hLLMono Xs hfresh member hiB τm hspec) hwrap' hTyR
      have harr := hτbindsMono Xs hfresh member hiB τm hspec
      have hTyW' : TypeOfHM (RecSpecs.stageCtx ⟨Γ, ctors⟩ specs
          (oneResidualGroup members |>.take 0).flatten G Xs) binding.rhs
          (Ty.renameG G Xs τm) := by
        simp only [List.take_zero, List.flatten_nil, RecSpecs.stageCtx]
        rw [stageEntries_none_eq_rhsEntries]
        simpa [RecSpecs.rhsCtx, ← harr, hbindingEq] using hTyW
      exact hTyW'
    · intro p hp σ hσ Ys hYs
      obtain ⟨i, hi, hb_eq, hs_eq⟩ := List.mem_zip_getElem hwf.length hp
      have hiB : i < binds.length := by omega
      have hspec : specs[i]'(Nat.lt_of_lt_of_eq hiB hlen) = .poly σ := hs_eq.trans hσ
      obtain ⟨rhsCore, _hann, hr, hwrap⟩ := hgetB i hiB
      have hr' :
          lowerCoreExpr ke (letRhsTyScope (binds[i]'hiB).tyParams (binds[i]'hiB).params
              (binds[i]'hiB).ann [])
            (letRhsTermScope (binds[i]'hiB).params (binds.map (·.name) ++ vs'))
            (binds[i]'hiB).rhs = some rhsCore := by
        simpa [bindingLowerTyScope, letRhsTyScope, letRhsTermScope, paramTermScope] using hr
      have hwrap' :
          wrapCoreParams ke (letRhsTyScope (binds[i]'hiB).tyParams (binds[i]'hiB).params
              (binds[i]'hiB).ann []) (binds[i]'hiB).params rhsCore =
            some (members[i]'hi).rhs := by
        simpa [bindingLowerTyScope, letRhsTyScope] using hwrap
      have hTyR := hpoly_ih i hiB σ hspec Ys hYs hr'
      have hTyW := wrapCoreParams_TypeOfHM
        (hLLPoly i hiB σ hspec Ys hYs) hwrap' hTyR
      have harr := hτbindsPoly i hiB σ hspec Ys hYs
      have hTy : TypeOfHM (RecSpecs.bodyCtx ⟨Γ, ctors⟩ specs G)
          (members[i]'hi).rhs (σ.openVars Ys) := by
        simpa [RecSpecs.bodyCtx, ← harr] using hTyW
      have hb0 : (members[i]'hi).rhs.TyBvarBounded 0 := TypeOfHM.tyBvarBounded hTy
      have hp1 : p.1 = members[i]'hi := hb_eq.symm
      simp only [hp1, Expr.openTyVars]
      rwa [Expr.openTyVarsAux_eq_self_of_tyBvarBounded Ys (members[i]'hi).rhs 0 hb0]
    · simpa [RecSpecs.bodyCtx] using hbody_ih hbL
  | match_ =>
    rename_i vs Γ scrut brs T tyArgs τres hs hbrs hpats hexh hkind hwk ihs ihbrs
    obtain ⟨scrut', bodies', hsL, hbL, rfl⟩ := lowerCoreExpr_match_decomp hlow
    have hscrut := ihs hsL
    have hlen := lowerCoreBranches_length hbL
    have hbodies : ∀ (i : Nat) (hi : i < bodies'.length),
        TypeOfHM ⟨branchBodyEnv Γ
          (patBindTys ctors ((brs.map Prod.fst)[i]'(by
            simpa [List.length_map, hlen] using hi)) (.customTy T tyArgs)), ctors⟩
          (bodies'[i]'hi) τres := by
      intro i hi
      have hi' : i < brs.length := by omega
      have hlow_i := lowerCoreBranches_get hbL i hi'
      have := ihbrs i hi' hlow_i
      simpa [List.getElem_map] using this
    exact TypeOfHM_lowerMatch
      (τscrut := .customTy T tyArgs) (τres := τres)
      rfl (by simpa [List.length_map] using hlen) hscrut hpats hbodies hexh
      hcons hfields hkind hwk
  | ife =>
    rename_i tvs' vs Γ cond t f τ hc ht hf hpats hexh hkind hwk ihc iht ihf
    simp only [lowerCoreExpr_eqs] at hlow
    cases hcL : lowerCoreExpr ke tvs' vs cond with
    | none => simp [hcL] at hlow
    | some cL =>
      cases htL : lowerCoreExpr ke tvs' vs t with
      | none => simp [hcL, htL] at hlow
      | some tL =>
        cases hfL : lowerCoreExpr ke tvs' vs f with
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

/-! ## 8. The runtime term: canonical completion, then erasure

Complete Core lowering is adapted with `Input.ofCore`; canonical inference returns
its completed output and type. `inferOfCore_source_sound` retains typing of the
original Core, while `inferOfCore_erase` identifies the exact erased runtime term.
-/

/-! ## 9. Lowering invariants used by the safety theorem -/

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

theorem lowerPolyAnnIn_freeVars {ke : KindEnv} {tvs : List ValName}
    {ann : Option Surface.PolyTy} {ann' : Option PolyTy}
    (h : lowerPolyAnnIn ke tvs ann = some ann') :
    ann'.elim [] (fun σ => σ.body.freeVars) = [] := by
  cases ann with
  | none =>
    simp only [lowerPolyAnnIn, Option.some.injEq] at h
    subst h
    rfl
  | some σ =>
    simp only [lowerPolyAnnIn] at h
    obtain ⟨σ', hσ, rfl⟩ := Option.map_eq_some_iff.mp h
    simp only [lowerPolyIn] at hσ
    obtain ⟨b, hb, rfl⟩ := Option.map_eq_some_iff.mp hσ
    simp [lowerTy_freeVars hb]

theorem wrapCoreParams_tyFreeVars {ke : KindEnv} {tvs : List ValName}
    {params : List (ValName × Option Surface.Ty)} {e e' : Expr}
    (hwrap : wrapCoreParams ke tvs params e = some e')
    (he : e.tyFreeVars = []) :
    e'.tyFreeVars = [] := by
  induction params generalizing e e' with
  | nil =>
    simp [wrapCoreParams] at hwrap
    subst hwrap
    exact he
  | cons p rest ih =>
    simp only [wrapCoreParams] at hwrap
    cases hrest : wrapCoreParams ke tvs rest e with
    | none =>
      simp only [hrest] at hwrap
      cases hwrap
    | some e'' =>
      cases hann : lowerAnn ke tvs p.2 with
      | none =>
        simp only [hann, hrest] at hwrap
        cases hwrap
      | some ann' =>
        simp only [hrest, hann, Option.some.injEq] at hwrap
        subst hwrap
        simp [Expr.tyFreeVars, lowerAnn_freeVars hann, ih hrest he]

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

private theorem branchList_tyFreeVars_nil (brs : List (MatchPattern × Expr))
    (h : ∀ p e, (p, e) ∈ brs → e.tyFreeVars = []) :
    Expr.tyFreeVars.BranchList.tyFreeVars brs = [] := by
  induction brs with
  | nil => rfl
  | cons br rest ih =>
    simp only [Expr.tyFreeVars.BranchList.tyFreeVars, List.append_eq_nil_iff]
    exact ⟨h br.1 br.2 List.mem_cons_self, ih fun p e hp => h p e (List.mem_cons_of_mem _ hp)⟩

private theorem recGroup_tyFreeVars_nil (bs : List CoreRecBinding)
    (h : ∀ binding ∈ bs,
      binding.ann.elim [] (fun σ => σ.body.freeVars) = [] ∧
      binding.rhs.tyFreeVars = []) :
    Expr.tyFreeVars.RecGroup.tyFreeVars bs = [] := by
  induction bs with
  | nil => rfl
  | cons binding rest ih =>
    simp only [Expr.tyFreeVars.RecGroup.tyFreeVars, List.append_eq_nil_iff]
    exact ⟨⟨(h binding List.mem_cons_self).1, (h binding List.mem_cons_self).2⟩,
      ih fun binding' hbinding' => h binding' (List.mem_cons_of_mem _ hbinding')⟩

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

private theorem mem_of_recGroup_tyFreeVars_nil (bs : List CoreRecBinding)
    (h : Expr.tyFreeVars.RecGroup.tyFreeVars bs = []) :
    ∀ binding ∈ bs,
      binding.ann.elim [] (fun σ => σ.body.freeVars) = [] ∧
      binding.rhs.tyFreeVars = [] := by
  induction bs with
  | nil => intro _ he; cases he
  | cons binding rest ih =>
    intro binding' he'
    simp only [Expr.tyFreeVars.RecGroup.tyFreeVars, List.append_eq_nil_iff, List.mem_cons] at h he'
    rcases he' with rfl | he'
    · exact h.1
    · exact ih h.2 binding' he'

/-- Term-variable shifting does not introduce free type variables. -/
theorem Expr.tyFreeVars_shiftFrom (e : Expr) (threshold n : Nat)
    (h : e.tyFreeVars = []) : (e.shiftFrom threshold n).tyFreeVars = [] := by
  induction e using Expr.rec_strong generalizing threshold with
  | primLit | primBinOp | ctor =>
    simp only [Expr.shiftFrom, Expr.tyFreeVars] at *
  | var i =>
    simp only [Expr.shiftFrom]
    split <;> simp [Expr.tyFreeVars]
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
  | letRec bindings body ihbind ihbody =>
    simp only [Expr.shiftFrom, Expr.tyFreeVars, List.append_eq_nil_iff] at h ⊢
    refine ⟨?_, ihbody (threshold + bindings.length) h.2⟩
    rw [RecGroup.shiftFrom_eq_map]
    refine recGroup_tyFreeVars_nil _ ?_
    intro shifted hshifted
    obtain ⟨binding, hbinding, rfl⟩ := List.mem_map.mp hshifted
    have hfree := mem_of_recGroup_tyFreeVars_nil bindings h.1 binding hbinding
    exact ⟨by simpa [RecBinding.mapRhs] using hfree.1,
      by simpa [RecBinding.mapRhs] using
        ihbind binding hbinding (threshold + bindings.length) hfree.2⟩

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
    simp only [emitLets.go, emitLetsWith.go, coreEmissionOps, Expr.tyFreeVars, List.append_eq_nil_iff]
    exact ⟨⟨rfl, trivial⟩, ih (depth + 1)⟩

mutual
private theorem emit_tyFreeVars (env : List Occ) (bodies : Nat → Expr) (t : DTree)
    (hb : ∀ i, (bodies i).tyFreeVars = []) :
    (emit env bodies t).tyFreeVars = [] := by
  match t with
  | .fail =>
    rw [emit, emitWith]
    simp only [coreEmissionOps, Expr.tyFreeVars, Expr.tyFreeVars.BranchList.tyFreeVars, List.nil_append]
  | .leaf act binds =>
    rw [emit, emitWith]
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
      rw [emit, emitWith]
      have hcases := emitCases_tyFreeVars env bodies occ cases hb
      simp only [emitCases, coreEmissionOps] at hcases
      simpa only [coreEmissionOps, Expr.tyFreeVars, List.nil_append, List.append_nil] using hcases
    | leaf act binds =>
      rw [emit, emitWith]
      have hcases := emitCases_tyFreeVars env bodies occ cases hb
      simp only [emitCases, coreEmissionOps] at hcases
      have hd := emit_tyFreeVars env bodies (.leaf act binds) hb
      simp only [emit, coreEmissionOps] at hd
      simp only [coreEmissionOps, Expr.tyFreeVars]
      rw [happ, hcases, hd]
      simp
      intro h; cases h
    | switch occ' cases' dflt' =>
      rw [emit, emitWith]
      have hcases := emitCases_tyFreeVars env bodies occ cases hb
      simp only [emitCases, coreEmissionOps] at hcases
      have hd := emit_tyFreeVars env bodies (.switch occ' cases' dflt') hb
      simp only [emit, coreEmissionOps] at hd
      simp only [coreEmissionOps, Expr.tyFreeVars]
      rw [happ, hcases, hd]
      simp
      intro h; cases h


private theorem emitCases_tyFreeVars (env : List Occ) (bodies : Nat → Expr) (occ : Occ) :
    ∀ (cases : List (CtorName × Nat × DTree)),
      (∀ i, (bodies i).tyFreeVars = []) →
      Expr.tyFreeVars.BranchList.tyFreeVars (emitCases env bodies occ cases) = []
  | [], _ => rfl
  | (_c, a, t) :: rest, hb => by
    simp only [emitCases, emitCasesWith, Expr.tyFreeVars.BranchList.tyFreeVars, List.append_eq_nil_iff]
    exact ⟨emit_tyFreeVars (subOccs occ a ++ env) bodies t hb,
      emitCases_tyFreeVars env bodies occ rest hb⟩
end

theorem lowerMatch_tyFreeVars (scrut : Expr) (pats : List Surface.Pattern) (bodies : Nat → Expr)
    (hs : scrut.tyFreeVars = []) (hb : ∀ i, (bodies i).tyFreeVars = []) :
    (lowerMatch scrut pats bodies).tyFreeVars = [] := by
  simp only [lowerMatch, lowerMatchWith, coreEmissionOps, Expr.tyFreeVars, Option.elim, List.nil_append, hs]
  exact emit_tyFreeVars [[]] bodies (compile [[]] (initMatrix pats)) hb

theorem mkList_tyFreeVars :
    ∀ (items : List Expr), (∀ e ∈ items, e.tyFreeVars = []) → (mkList items).tyFreeVars = []
  | [], _ => rfl
  | x :: xs, h => by
    simp only [mkList, Expr.tyFreeVars, List.nil_append, List.append_eq_nil_iff]
    exact ⟨h x List.mem_cons_self, mkList_tyFreeVars xs fun e he =>
      h e (List.mem_cons_of_mem _ he)⟩

mutual
theorem lowerCoreExpr_tyFreeVars {ke : KindEnv} {tvs vs : List ValName} :
    ∀ {s : Surface.Expr} {c : Expr},
      lowerCoreExpr ke tvs vs s = some c → c.tyFreeVars = [] := by
  intro s c h
  match s with
  | .primLit (.bool _) | .primLit .unit | .primLit (.int _) | .primLit (.nat _) | .primLit (.char _) =>
    simp only [lowerCoreExpr_eqs, Option.some.injEq] at h; subst h; simp [Expr.tyFreeVars]
  | .primBinOp _ =>
    simp only [lowerCoreExpr_eqs, Option.some.injEq] at h; subst h; simp [Expr.tyFreeVars]
  | .pair a b =>
    simp only [lowerCoreExpr_eqs] at h
    cases ha : lowerCoreExpr ke tvs vs a with
    | none => simp [ha] at h
    | some a' =>
      cases hb : lowerCoreExpr ke tvs vs b with
      | none => simp [ha, hb] at h
      | some b' =>
        simp only [ha, hb, Option.some.injEq] at h; subst h
        simp only [Expr.tyFreeVars, lowerCoreExpr_tyFreeVars ha, lowerCoreExpr_tyFreeVars hb,
          List.nil_append]
  | .cons hd tl =>
    simp only [lowerCoreExpr_eqs] at h
    cases ha : lowerCoreExpr ke tvs vs hd with
    | none => simp [ha] at h
    | some h' =>
      cases hb : lowerCoreExpr ke tvs vs tl with
      | none => simp [ha, hb] at h
      | some t' =>
        simp only [ha, hb, Option.some.injEq] at h; subst h
        simp only [Expr.tyFreeVars, lowerCoreExpr_tyFreeVars ha, lowerCoreExpr_tyFreeVars hb,
          List.nil_append]
  | .list items =>
    simp only [lowerCoreExpr_eqs] at h
    cases hi : lowerCoreExprList ke tvs vs items with
    | none => simp [hi] at h
    | some items' =>
      simp only [hi, Option.some.injEq] at h; subst h
      exact mkList_tyFreeVars items' (lowerCoreExprList_tyFreeVars hi)
  | .lambda param paramAnn body =>
    simp only [lowerCoreExpr_eqs] at h
    cases hann : lowerAnn ke tvs paramAnn with
    | none => simp [hann] at h
    | some ann' =>
      cases param with
      | name x =>
        cases hb : lowerCoreExpr ke tvs (x :: vs) body with
        | none => simp [hann, hb] at h
        | some b' =>
          simp only [hann, hb, Option.some.injEq] at h; subst h
          simp only [Expr.tyFreeVars, lowerAnn_freeVars hann, lowerCoreExpr_tyFreeVars hb,
            List.nil_append]
      | wildcard =>
        cases hb : lowerCoreExpr ke tvs (.mk "_" :: vs) body with
        | none => simp [hann, hb] at h
        | some b' =>
          simp only [hann, hb, Option.some.injEq] at h; subst h
          simp only [Expr.tyFreeVars, lowerAnn_freeVars hann, lowerCoreExpr_tyFreeVars hb,
            List.nil_append]
      | ctor n ps =>
        cases hb : lowerCoreExpr ke tvs (patVars (.ctor n ps) ++ .mk "_" :: vs) body with
        | none => simp [hann, hb] at h
        | some b' =>
          simp only [hann, hb, Option.some.injEq] at h; subst h
          simp only [patternLambdaCore, Expr.tyFreeVars, lowerAnn_freeVars hann,
            List.nil_append]
          refine lowerMatch_tyFreeVars _ _ _ rfl ?_
          intro i
          cases i with
          | zero => simpa using lowerCoreExpr_tyFreeVars hb
          | succ i => simp [List.getD, Expr.tyFreeVars]
      | pair a b =>
        cases hb : lowerCoreExpr ke tvs (patVars (.pair a b) ++ .mk "_" :: vs) body with
        | none => simp [hann, hb] at h
        | some b' =>
          simp only [hann, hb, Option.some.injEq] at h; subst h
          simp only [patternLambdaCore, Expr.tyFreeVars, lowerAnn_freeVars hann,
            List.nil_append]
          refine lowerMatch_tyFreeVars _ _ _ rfl ?_
          intro i
          cases i with
          | zero => simpa using lowerCoreExpr_tyFreeVars hb
          | succ i => simp [List.getD, Expr.tyFreeVars]
      | cons a b =>
        cases hb : lowerCoreExpr ke tvs (patVars (.cons a b) ++ .mk "_" :: vs) body with
        | none => simp [hann, hb] at h
        | some b' =>
          simp only [hann, hb, Option.some.injEq] at h; subst h
          simp only [patternLambdaCore, Expr.tyFreeVars, lowerAnn_freeVars hann,
            List.nil_append]
          refine lowerMatch_tyFreeVars _ _ _ rfl ?_
          intro i
          cases i with
          | zero => simpa using lowerCoreExpr_tyFreeVars hb
          | succ i => simp [List.getD, Expr.tyFreeVars]
      | list ps =>
        cases hb : lowerCoreExpr ke tvs (patVars (.list ps) ++ .mk "_" :: vs) body with
        | none => simp [hann, hb] at h
        | some b' =>
          simp only [hann, hb, Option.some.injEq] at h; subst h
          simp only [patternLambdaCore, Expr.tyFreeVars, lowerAnn_freeVars hann,
            List.nil_append]
          refine lowerMatch_tyFreeVars _ _ _ rfl ?_
          intro i
          cases i with
          | zero => simpa using lowerCoreExpr_tyFreeVars hb
          | succ i => simp [List.getD, Expr.tyFreeVars]
  | .app f x =>
    simp only [lowerCoreExpr_eqs] at h
    cases hf : lowerCoreExpr ke tvs vs f with
    | none => simp [hf] at h
    | some f' =>
      cases hx : lowerCoreExpr ke tvs vs x with
      | none => simp [hf, hx] at h
      | some x' =>
        simp only [hf, hx, Option.some.injEq] at h; subst h
        simp only [Expr.tyFreeVars, lowerCoreExpr_tyFreeVars hf, lowerCoreExpr_tyFreeVars hx,
          List.nil_append]
  | .letIn name tyParams params ann rhs body =>
    simp only [lowerCoreExpr_eqs] at h
    cases hann : lowerPolyAnnIn ke tvs (finalizeAnn tyParams params ann) with
    | none => simp [hann] at h
    | some ann' =>
      set tvs' := letAnnTyPrefix tyParams (finalizeAnn tyParams params ann) ++ tvs with htvs'
      cases hr : lowerCoreExpr ke tvs' (paramTermScope params vs) rhs with
      | none => simp [hann, hr] at h
      | some rhsCore =>
        cases hwrap : wrapCoreParams ke tvs' params rhsCore with
        | none => simp [hann, hr, hwrap] at h
        | some rhs' =>
          cases hb : lowerCoreExpr ke tvs (name :: vs) body with
          | none => simp [hann, hr, hwrap, hb] at h
          | some body' =>
            have hEq : some (Expr.letIn ann' rhs' body') = some c := by
              simpa [hann, hr, hwrap, hb] using h
            cases hEq
            simp only [Expr.tyFreeVars, lowerPolyAnnIn_freeVars hann,
              wrapCoreParams_tyFreeVars hwrap (lowerCoreExpr_tyFreeVars hr),
              lowerCoreExpr_tyFreeVars hb, List.nil_append]
  | .letRecIn binds body =>
    simp only [lowerCoreExpr_eqs] at h
    cases hbinds : lowerCoreRecBinds ke tvs (binds.map (·.name) ++ vs) binds with
    | none => simp [hbinds] at h
    | some bindings' =>
      cases hb : lowerCoreExpr ke tvs (binds.map (·.name) ++ vs) body with
      | none => simp [hbinds, hb] at h
      | some body' =>
        have hEq : some (Expr.letRec bindings' body') = some c := by
          simpa [hbinds, hb] using h
        cases hEq
        have hbindings := lowerCoreRecBinds_tyFreeVars hbinds
        simp only [Expr.tyFreeVars, List.append_eq_nil_iff]
        exact ⟨hbindings, lowerCoreExpr_tyFreeVars hb⟩
  | .var name =>
    simp only [lowerCoreExpr_eqs] at h
    cases hi : tvarIndex vs name with
    | none => simp [hi] at h
    | some i =>
      simp only [hi, Option.some.injEq] at h; subst h
      simp [Expr.tyFreeVars]
  | .ctor name =>
    simp only [lowerCoreExpr_eqs, Option.some.injEq] at h; subst h; simp [Expr.tyFreeVars]
  | .ife c t f =>
    simp only [lowerCoreExpr_eqs] at h
    cases hc : lowerCoreExpr ke tvs vs c with
    | none => simp [hc] at h
    | some c' =>
      cases ht : lowerCoreExpr ke tvs vs t with
      | none => simp [hc, ht] at h
      | some t' =>
        cases hf : lowerCoreExpr ke tvs vs f with
        | none => simp [hc, ht, hf] at h
        | some f' =>
          simp only [hc, ht, hf, Option.some.injEq] at h; subst h
          exact lowerMatch_tyFreeVars c' _ _
            (lowerCoreExpr_tyFreeVars hc) (fun i => by
              rw [List.getD]
              match i with
              | 0 => simpa [Option.getD] using lowerCoreExpr_tyFreeVars ht
              | 1 => simpa [Option.getD] using lowerCoreExpr_tyFreeVars hf
              | _ + 2 => simp [Option.getD, Expr.tyFreeVars])
  | .match_ scrut brs =>
    simp only [lowerCoreExpr_eqs] at h
    cases hs : lowerCoreExpr ke tvs vs scrut with
    | none => simp [hs] at h
    | some scrut' =>
      cases hb : lowerCoreBranches ke tvs vs brs with
      | none => simp [hs, hb] at h
      | some bodies' =>
        simp only [hs, hb, Option.some.injEq] at h; subst h
        exact lowerMatch_tyFreeVars scrut' _ (bodyFn bodies')
          (lowerCoreExpr_tyFreeVars hs) (fun i => by
            change (bodies'.getD i matchBodyDefault).tyFreeVars = []
            rw [List.getD]
            cases hget : bodies'[i]? with
            | none => simp [Option.getD, matchBodyDefault, Expr.tyFreeVars]
            | some e =>
              simp only [Option.getD]
              exact lowerCoreBranches_tyFreeVars hb e (List.mem_of_getElem? hget))

theorem lowerCoreExprList_tyFreeVars {ke : KindEnv} {tvs vs : List ValName} :
    ∀ {es : List Surface.Expr} {es' : List Expr},
      lowerCoreExprList ke tvs vs es = some es' →
      ∀ e ∈ es', e.tyFreeVars = [] := by
  intro es es' h e he
  match es with
  | [] =>
    simp only [lowerCoreExprList_eqs, Option.some.injEq] at h; subst h; cases he
  | e0 :: rest =>
    simp only [lowerCoreExprList_eqs] at h
    cases he0 : lowerCoreExpr ke tvs vs e0 with
    | none => simp [he0] at h
    | some e0' =>
      cases hrest : lowerCoreExprList ke tvs vs rest with
      | none => simp [he0, hrest] at h
      | some rest' =>
        simp only [he0, hrest, Option.some.injEq] at h; subst h
        simp only [List.mem_cons] at he
        rcases he with rfl | he
        · exact lowerCoreExpr_tyFreeVars he0
        · exact lowerCoreExprList_tyFreeVars hrest e he

theorem lowerCoreBranches_tyFreeVars {ke : KindEnv} {tvs vs : List ValName} :
    ∀ {brs : List (Surface.Pattern × Surface.Expr)} {bodies' : List Expr},
      lowerCoreBranches ke tvs vs brs = some bodies' →
      ∀ e ∈ bodies', e.tyFreeVars = [] := by
  intro brs bodies' h e he
  match brs with
  | [] =>
    simp only [lowerCoreBranches_eqs, Option.some.injEq] at h; subst h; cases he
  | (p, b) :: rest =>
    simp only [lowerCoreBranches_eqs] at h
    cases hb : lowerCoreExpr ke tvs (patVars p ++ vs) b with
    | none => simp [hb] at h
    | some b' =>
      cases hrest : lowerCoreBranches ke tvs vs rest with
      | none => simp [hb, hrest] at h
      | some rest' =>
        simp only [hb, hrest, Option.some.injEq] at h; subst h
        simp only [List.mem_cons] at he
        rcases he with rfl | he
        · exact lowerCoreExpr_tyFreeVars hb
        · exact lowerCoreBranches_tyFreeVars hrest e he

theorem lowerCoreRecBinds_tyFreeVars {ke : KindEnv} {tvs recScope : List ValName} :
    ∀ {binds : List Surface.Binding} {bindings' : List CoreRecBinding},
      lowerCoreRecBinds ke tvs recScope binds = some bindings' →
      Expr.tyFreeVars.RecGroup.tyFreeVars bindings' = [] := by
  intro binds bindings' h
  have hrel := lowerCoreRecBinds_CoreLowersRecBinds (ctors := []) binds h
  cases hrel with
  | nil => rfl
  | @cons _ _ bind ann' rhsCore rhs' rest rest' hann hrhs hwrap hrest =>
      have hrhs' : lowerCoreExpr ke _ _ _ = some _ :=
        lowerCoreExpr_eq_some_of_CoreLowersExpr hrhs
      have hwrap' : wrapCoreParams ke (bindingLowerTyScope bind tvs)
          bind.params rhsCore = some rhs' := by
        simpa [bindingLowerTyScope] using hwrap
      simp only [Expr.tyFreeVars.RecGroup.tyFreeVars, List.append_eq_nil_iff]
      exact ⟨⟨lowerPolyAnnIn_freeVars hann,
        wrapCoreParams_tyFreeVars hwrap' (lowerCoreExpr_tyFreeVars hrhs')⟩,
        lowerCoreRecBinds_tyFreeVars
          (lowerCoreRecBinds_eq_some_of_CoreLowersRecBinds hrest)⟩

end

/-- **Lowered programs are type-closed.** A `lowerCore` output has no free type
    variables, so inference's rigid seed is empty and the frontier machinery
    disappears. Provable once `lowerCore` is defined (it emits `bvar`-indexed types
    from the kind-checker; no `fvar`s). -/
theorem lowerCore_tyClosed {ctors : CtorEnv} {s : Surface.Expr} {c : Expr}
    (h : lowerCore ctors s = some c) : c.tyFreeVars = [] := by
  simp only [lowerCore] at h
  exact lowerCoreExpr_tyFreeVars h

/-- Typechecking exposes the same canonical artifact run used for execution. -/
theorem infer_of_typecheck {ctors : CtorEnv} {c : Expr}
    (_hclosed : c.tyFreeVars = []) (htc : (coreTypecheck ctors c).isSome) :
    ∃ result, inferWithTypes ctors (InferInput.ofCore c) = some result :=
  Option.isSome_iff_exists.mp (coreTypecheck_isSome_iff.mp htc)

/-! ### Exhaustiveness-transfer helpers

Transport across erasure is mechanical (`AllMatchesExhaustive.erase` in Core;
`lowerCore_exhaustive` via induction on the coverage derivation — no semantic
totality, no inhabitation). The crux (A) is SYNTACTIC: `emit` of a
`DTreeExhaustive` tree is `AllMatchesExhaustive`. -/

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
    rw [emitCases, emitCasesWith]
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
    simp only [emit, emitWith]
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

/-- Successful `lowerCoreExprList` yields exhaustive Core terms when each surface item is covered. -/
private theorem lowerCoreExprList_exhaustive {ctors : CtorEnv} {ke : KindEnv} {tvs : List ValName}
    {vs : List ValName} {es : List Surface.Expr} {es' : List Expr}
    (hcov : ∀ e ∈ es, SurfaceCovers ctors e)
    (ih : ∀ e ∈ es, ∀ {vs : List ValName} {c : Expr},
      lowerCoreExpr ke tvs vs e = some c → AllMatchesExhaustive ctors c)
    (hlow : lowerCoreExprList ke tvs vs es = some es') :
    (∀ e ∈ es', AllMatchesExhaustive ctors e) := by
  induction es generalizing es' with
  | nil =>
    simp only [lowerCoreExprList_eqs, Option.some.injEq] at hlow; subst hlow
    intro _ he; exact nomatch he
  | cons e rest ih_es =>
    simp only [lowerCoreExprList_eqs] at hlow
    cases he : lowerCoreExpr ke tvs vs e with
    | none => simp [he] at hlow
    | some e' =>
      cases hr : lowerCoreExprList ke tvs vs rest with
      | none => simp [he, hr] at hlow
      | some rest' =>
        simp only [he, hr, Option.some.injEq] at hlow; subst hlow
        intro x hx
        simp only [List.mem_cons] at hx
        rcases hx with rfl | hx
        · exact ih e List.mem_cons_self he
        · exact ih_es (fun e' he' => hcov e' (List.mem_cons_of_mem _ he'))
            (fun e' he' => ih e' (List.mem_cons_of_mem _ he')) hr x hx

private theorem wrapCoreParams_exhaustive {ctors : CtorEnv} {ke : KindEnv} {tvs : List ValName}
    {params : List (ValName × Option Surface.Ty)} {e e' : Expr}
    (hwrap : wrapCoreParams ke tvs params e = some e')
    (he : AllMatchesExhaustive ctors e) :
    AllMatchesExhaustive ctors e' := by
  induction params generalizing e e' with
  | nil =>
    simp [wrapCoreParams] at hwrap
    subst hwrap
    exact he
  | cons p rest ih =>
    simp [wrapCoreParams] at hwrap
    cases hrest : wrapCoreParams ke tvs rest e with
    | none => simp [hrest] at hwrap
    | some e'' =>
      cases hann : lowerAnn ke tvs p.2 with
      | none =>
        simp [hann, hrest] at hwrap
      | some _ =>
        simp [hrest, hann] at hwrap
        subst hwrap
        exact .lambda (ih hrest he)

/-- Successful `lowerCoreRecBinds` yields exhaustive Core bindings. -/
private theorem lowerCoreRecBinds_exhaustive {ctors : CtorEnv} {ke : KindEnv} {tvs : List ValName}
    {recScope : List ValName}
    {binds : List Surface.Binding} {bs' : List CoreRecBinding}
    (hcov : ∀ b ∈ binds, SurfaceCovers ctors b.rhs)
    (ih : ∀ b ∈ binds, ∀ {vs : List ValName} {c : Expr},
      lowerCoreExpr ke (bindingLowerTyScope b tvs)
        (paramTermScope b.params vs) b.rhs = some c →
      ∀ rhs', wrapCoreParams ke (bindingLowerTyScope b tvs) b.params c = some rhs' →
        AllMatchesExhaustive ctors rhs')
    (hlow : lowerCoreRecBinds ke tvs recScope binds = some bs') :
    ∀ binding ∈ bs', AllMatchesExhaustive ctors binding.rhs := by
  match binds with
  | [] =>
    simp only [lowerCoreRecBinds_eqs, Option.some.injEq] at hlow
    subst hlow
    intro _ hmem
    exact nomatch hmem
  | b :: rest =>
    simp only [lowerCoreRecBinds_eqs] at hlow
    cases hann : lowerPolyAnnIn ke tvs
        (finalizeAnn b.tyParams b.params b.ann) with
    | none => simp [hann] at hlow
    | some ann' =>
      cases hrhs : lowerCoreExpr ke
          (letAnnTyPrefix b.tyParams (finalizeAnn b.tyParams b.params b.ann) ++ tvs)
          (paramTermScope b.params recScope) b.rhs with
      | none => simp [hann, hrhs] at hlow
      | some rhsCore =>
        cases hwrap : wrapCoreParams ke
            (letAnnTyPrefix b.tyParams (finalizeAnn b.tyParams b.params b.ann) ++ tvs)
            b.params rhsCore with
        | none => simp [hann, hrhs, hwrap] at hlow
        | some rhs' =>
          cases hrest : lowerCoreRecBinds ke tvs recScope rest with
          | none => simp [hann, hrhs, hwrap, hrest] at hlow
          | some rest' =>
            simp only [hann, hrhs, hwrap, hrest, Option.some.injEq] at hlow
            subst hlow
            intro binding hbinding
            simp only [List.mem_cons] at hbinding
            rcases hbinding with rfl | hbinding
            · have hrhs' : lowerCoreExpr ke (bindingLowerTyScope b tvs)
                  (paramTermScope b.params recScope) b.rhs = some rhsCore := by
                simpa [bindingLowerTyScope] using hrhs
              have hwrap' : wrapCoreParams ke (bindingLowerTyScope b tvs)
                  b.params rhsCore = some rhs' := by
                simpa [bindingLowerTyScope] using hwrap
              exact ih b List.mem_cons_self hrhs' _ hwrap'
            · exact lowerCoreRecBinds_exhaustive
                (fun b' hb' => hcov b' (List.mem_cons_of_mem _ hb'))
                (fun b' hb' => ih b' (List.mem_cons_of_mem _ hb'))
                hrest binding hbinding
termination_by binds.length
decreasing_by simp_wf

/-- `lowerCoreBranches` bodies (and the `.ctor cNil` default) are exhaustive. -/
private theorem lowerCoreBranches_getD_exhaustive {ctors : CtorEnv} {ke : KindEnv}
    {tvs : List ValName} {vs : List ValName}
    {brs : List (Surface.Pattern × Surface.Expr)} {bodies' : List Expr}
    (hcov : ∀ p b, (p, b) ∈ brs → SurfaceCovers ctors b)
    (ih : ∀ p b, (p, b) ∈ brs → ∀ {vs : List ValName} {c : Expr},
      lowerCoreExpr ke tvs vs b = some c → AllMatchesExhaustive ctors c)
    (hlow : lowerCoreBranches ke tvs vs brs = some bodies') :
    ∀ i, AllMatchesExhaustive ctors (bodies'.getD i (.ctor cNil)) := by
  induction brs generalizing bodies' with
  | nil =>
    simp only [lowerCoreBranches_eqs, Option.some.injEq] at hlow; subst hlow
    intro i; simp only [List.getD_nil]; exact .ctor
  | cons pb rest ih_brs =>
    obtain ⟨p, b⟩ := pb
    simp only [lowerCoreBranches_eqs] at hlow
    cases hb : lowerCoreExpr ke tvs (patVars p ++ vs) b with
    | none => simp [hb] at hlow
    | some b' =>
      cases hr : lowerCoreBranches ke tvs vs rest with
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

/-- Generalized: `SurfaceCovers` + successful `lowerCoreExpr` ⇒ Core exhaustiveness.
    Quantifies over `tvs` so letIn/letRec IHs apply under extended type scopes. -/
theorem lowerCoreExpr_exhaustive {ctors : CtorEnv} {ke : KindEnv} :
    ∀ {tvs vs : List ValName} {s : Surface.Expr} {c : Expr},
      SurfaceCovers ctors s → lowerCoreExpr ke tvs vs s = some c →
      AllMatchesExhaustive ctors c := by
  intro tvs vs s c hcov hlow
  induction hcov generalizing tvs vs c with
  | @primLit p =>
    cases p with
    | bool b =>
      simp only [lowerCoreExpr_eqs, Option.some.injEq] at hlow; subst hlow; exact .ctor
    | unit =>
      simp only [lowerCoreExpr_eqs, Option.some.injEq] at hlow; subst hlow; exact .primLit
    | int n =>
      simp only [lowerCoreExpr_eqs, Option.some.injEq] at hlow; subst hlow; exact .primLit
    | nat n =>
      simp only [lowerCoreExpr_eqs, Option.some.injEq] at hlow; subst hlow; exact .primLit
    | char ch =>
      simp only [lowerCoreExpr_eqs, Option.some.injEq] at hlow; subst hlow; exact .primLit
  | @primBinOp op =>
    simp only [lowerCoreExpr_eqs, Option.some.injEq] at hlow; subst hlow; exact .primBinOp
  | @var n =>
    simp only [lowerCoreExpr_eqs] at hlow
    cases hi : tvarIndex vs n with
    | none => simp [hi] at hlow
    | some i =>
      simp only [hi, Option.some.injEq] at hlow; subst hlow; exact .var
  | @ctor n =>
    simp only [lowerCoreExpr_eqs, Option.some.injEq] at hlow; subst hlow; exact .ctor
  | @pair a b ha hb iha ihb =>
    simp only [lowerCoreExpr_eqs] at hlow
    cases ha' : lowerCoreExpr ke tvs vs a with
    | none => simp [ha'] at hlow
    | some a' =>
      cases hb' : lowerCoreExpr ke tvs vs b with
      | none => simp [ha', hb'] at hlow
      | some b' =>
        simp only [ha', hb', Option.some.injEq] at hlow; subst hlow
        exact .app (.app .ctor (iha ha')) (ihb hb')
  | @cons h t hh ht ihh iht =>
    simp only [lowerCoreExpr_eqs] at hlow
    cases hh' : lowerCoreExpr ke tvs vs h with
    | none => simp [hh'] at hlow
    | some h' =>
      cases ht' : lowerCoreExpr ke tvs vs t with
      | none => simp [hh', ht'] at hlow
      | some t' =>
        simp only [hh', ht', Option.some.injEq] at hlow; subst hlow
        exact .app (.app .ctor (ihh hh')) (iht ht')
  | @list items hitems ih =>
    simp only [lowerCoreExpr_eqs] at hlow
    cases hi : lowerCoreExprList ke tvs vs items with
    | none => simp [hi] at hlow
    | some items' =>
      simp only [hi, Option.some.injEq] at hlow; subst hlow
      exact mkList_AllMatchesExhaustive items'
        (lowerCoreExprList_exhaustive hitems (fun e he => ih e he) hi)
  | @lambda param ann body hb hpat ihb =>
    simp only [lowerCoreExpr_eqs] at hlow
    cases hann : lowerAnn ke tvs ann with
    | none => simp [hann] at hlow
    | some ann' =>
      cases param with
      | name x =>
        cases hb' : lowerCoreExpr ke tvs (x :: vs) body with
        | none => simp [hann, hb'] at hlow
        | some b' =>
          simp only [hann, hb', Option.some.injEq] at hlow; subst hlow
          exact .lambda (ihb hb')
      | wildcard =>
        cases hb' : lowerCoreExpr ke tvs (.mk "_" :: vs) body with
        | none => simp [hann, hb'] at hlow
        | some b' =>
          simp only [hann, hb', Option.some.injEq] at hlow; subst hlow
          exact .lambda (ihb hb')
      | ctor n ps =>
        cases hb' : lowerCoreExpr ke tvs (patVars (.ctor n ps) ++ .mk "_" :: vs) body with
        | none => simp [hann, hb'] at hlow
        | some b' =>
          simp only [hann, hb', Option.some.injEq] at hlow; subst hlow
          obtain ⟨T, args, hexh⟩ := hpat
          apply AllMatchesExhaustive.lambda
          simp only [lowerMatch]
          refine .letIn .var (emit_compile_AllMatchesExhaustive _ _ ?_ hexh)
          intro i
          cases i with
          | zero => simpa using ihb hb'
          | succ i => simpa [List.getD] using (AllMatchesExhaustive.ctor (name := cNil))
      | pair a b =>
        cases hb' : lowerCoreExpr ke tvs (patVars (.pair a b) ++ .mk "_" :: vs) body with
        | none => simp [hann, hb'] at hlow
        | some b' =>
          simp only [hann, hb', Option.some.injEq] at hlow; subst hlow
          obtain ⟨T, args, hexh⟩ := hpat
          apply AllMatchesExhaustive.lambda
          simp only [lowerMatch]
          refine .letIn .var (emit_compile_AllMatchesExhaustive _ _ ?_ hexh)
          intro i
          cases i with
          | zero => simpa using ihb hb'
          | succ i => simpa [List.getD] using (AllMatchesExhaustive.ctor (name := cNil))
      | cons a b =>
        cases hb' : lowerCoreExpr ke tvs (patVars (.cons a b) ++ .mk "_" :: vs) body with
        | none => simp [hann, hb'] at hlow
        | some b' =>
          simp only [hann, hb', Option.some.injEq] at hlow; subst hlow
          obtain ⟨T, args, hexh⟩ := hpat
          apply AllMatchesExhaustive.lambda
          simp only [lowerMatch]
          refine .letIn .var (emit_compile_AllMatchesExhaustive _ _ ?_ hexh)
          intro i
          cases i with
          | zero => simpa using ihb hb'
          | succ i => simpa [List.getD] using (AllMatchesExhaustive.ctor (name := cNil))
      | list ps =>
        cases hb' : lowerCoreExpr ke tvs (patVars (.list ps) ++ .mk "_" :: vs) body with
        | none => simp [hann, hb'] at hlow
        | some b' =>
          simp only [hann, hb', Option.some.injEq] at hlow; subst hlow
          obtain ⟨T, args, hexh⟩ := hpat
          apply AllMatchesExhaustive.lambda
          simp only [lowerMatch]
          refine .letIn .var (emit_compile_AllMatchesExhaustive _ _ ?_ hexh)
          intro i
          cases i with
          | zero => simpa using ihb hb'
          | succ i => simpa [List.getD] using (AllMatchesExhaustive.ctor (name := cNil))
  | @app f x hf hx ihf ihx =>
    simp only [lowerCoreExpr_eqs] at hlow
    cases hf' : lowerCoreExpr ke tvs vs f with
    | none => simp [hf'] at hlow
    | some f' =>
      cases hx' : lowerCoreExpr ke tvs vs x with
      | none => simp [hf', hx'] at hlow
      | some x' =>
        simp only [hf', hx', Option.some.injEq] at hlow; subst hlow
        exact .app (ihf hf') (ihx hx')
  | @letIn name tyParams params ann rhs body hr hb ihr ihb =>
    obtain ⟨ann', rhsCore, rhs', body', hann, hr', hwrap, hb', rfl⟩ :=
      lowerCoreExpr_letIn_decomp hlow
    exact .letIn (wrapCoreParams_exhaustive hwrap (ihr hr')) (ihb hb')
  | @letRecIn binds body hbinds hb ihbinds ihb =>
    obtain ⟨bindings', body', hbs, hb', rfl⟩ :=
      lowerCoreExpr_letRecIn_decomp hlow
    refine .letRec ?_ (ihb hb')
    refine lowerCoreRecBinds_exhaustive hbinds ?_ hbs
    intro b hb vs c hlo rhs' hwrap
    exact wrapCoreParams_exhaustive hwrap (ihbinds b hb hlo)
  | @ife cond t f hc ht hf hexh ihc iht ihf =>
    simp only [lowerCoreExpr_eqs] at hlow
    cases hc' : lowerCoreExpr ke tvs vs cond with
    | none => simp [hc'] at hlow
    | some c' =>
      cases ht' : lowerCoreExpr ke tvs vs t with
      | none => simp [hc', ht'] at hlow
      | some t' =>
        cases hf' : lowerCoreExpr ke tvs vs f with
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
    obtain ⟨scrut', bodies', hsL, hbL, rfl⟩ := lowerCoreExpr_match_decomp hlow
    simp only [lowerMatch]
    exact .letIn (ihs hsL)
      (emit_compile_AllMatchesExhaustive
        (bodyFn bodies')
        (brs.map Prod.fst)
        (by
          intro i
          simp only [bodyFn, matchBodyDefault]
          exact lowerCoreBranches_getD_exhaustive hbrs (fun p b hm => ihbrs p b hm) hbL i)
        hexh)

/-- **(A) Surface coverage + successful lowering ⇒ the Core term is exhaustive.**
    Induction on `SurfaceCovers` threaded through `lowerCoreExpr`; the `match` case
    feeds `emit_compile_AllMatchesExhaustive` (its `MatchExhaustive` comes from the
    `SurfaceCovers.match_` witness, its exhaustive branch bodies from the recursive
    `SurfaceCovers` on the branches). No typing hypothesis needed — `DTreeExhaustive`
    is self-contained (it carries the tested ctors' env membership). -/
theorem lowerCore_exhaustive {ctors : CtorEnv} {s : Surface.Expr} {c : Expr}
    (hcov : SurfaceCovers ctors s) (hlow : lowerCore ctors s = some c) :
    AllMatchesExhaustive ctors c := by
  simp only [lowerCore] at hlow
  exact lowerCoreExpr_exhaustive hcov hlow

/-- `openTyVars` preserves exhaustiveness (via `instTy`). -/
private theorem AllMatchesExhaustive.openTyVars {ctors : CtorEnv} (Xs : List Nat)
    {e : Expr} (h : AllMatchesExhaustive ctors e) :
    AllMatchesExhaustive ctors (e.openTyVars Xs) := by
  rw [← Expr.instTy_fvar_eq_openTyVars]
  exact AllMatchesExhaustive.instTy _ h

/-! ## 9b. Whole-program pipeline

`Surface.Program` = user `DataDecl`s + binding `groups` + body.
Acyclic singleton groups desugar to `letIn`; recursive SCCs desugar to
`letRecIn` (`Program.term`). The prelude is merged in; then reuse expression
`lowerCore`/`surface_type_safe`. Flat bindings
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
inductive CoreLowersProgram : Surface.Program → CtorEnv → Expr → Prop
  | mk {p : Surface.Program} {ctors : CtorEnv} {c : Expr} {userCore : List DataDecl} :
      LowersDataDeclsIn preludeKindEnv p.decls userCore →
      DataDecls.WF (preludeDecls ++ userCore) →
      elabDecls (preludeDecls ++ userCore) = some ctors →
      CoreLowers ctors p.term c →
      CoreLowersProgram p ctors c

/-- Elaborate a program's decl group + lowerCore its desugared term to Core. -/
def lowerCoreProgram (p : Surface.Program) : Option (CtorEnv × Expr) := do
  let userCore ← lowerDataDeclsIn preludeKindEnv p.decls
  let ctors ← elabDecls (preludeDecls ++ userCore)
  let c ← lowerCore ctors p.term
  pure (ctors, c)

private theorem option_bind_eq_some {α β : Type} {o : Option α} {f : α → Option β} {b : β}
    (h : o >>= f = some b) : ∃ a, o = some a ∧ f a = some b :=
  Option.bind_eq_some_iff.mp h

/-- Soundness: executable program lowering implies the declarative relation. -/
theorem lowerCoreProgram_sound {p : Surface.Program} {ctors : CtorEnv} {c : Expr} :
    lowerCoreProgram p = some (ctors, c) → CoreLowersProgram p ctors c := by
  intro h
  unfold lowerCoreProgram at h
  obtain ⟨userCore, hUser, hb⟩ := option_bind_eq_some h
  obtain ⟨ctors', hElab, hb'⟩ := option_bind_eq_some hb
  obtain ⟨c', hBody, hPure⟩ := option_bind_eq_some hb'
  simp at hPure
  obtain ⟨rfl, rfl⟩ := hPure
  refine CoreLowersProgram.mk (lowerDataDeclsIn_sound hUser) (elabDecls_sound hElab) hElab
    (lowerCore_sound hBody)

/-- Completeness: declarative `CoreLowersProgram` ⇒ executable `lowerCoreProgram` returns
    the same `CtorEnv` and the same Core body (now that `CoreLowers` is fully
    deterministic, including at `match_`). -/
theorem lowerCoreProgram_complete {p : Surface.Program} {ctors : CtorEnv} {c : Expr} :
    CoreLowersProgram p ctors c → lowerCoreProgram p = some (ctors, c) := by
  intro h
  cases h with
  | mk hUser _hWF hElab hBody =>
    simp [lowerCoreProgram, lowerDataDeclsIn_complete hUser, hElab, lowerCore_complete hBody]

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

-- Simple acyclic top-level binding group: `let x = 1 in x`
private def pLetOne : Surface.Program :=
  ⟨[], [[{ name := .mk "x", ann := none, rhs := .primLit (.int 1) }]],
   .var (.mk "x")⟩

-- Two nested acyclic singleton groups: `let x = 1 in let y = x in y`
private def pLetTwo : Surface.Program :=
  ⟨[],
   [[{ name := .mk "x", ann := none, rhs := .primLit (.int 1) }],
    [{ name := .mk "y", ann := none, rhs := .var (.mk "x") }]],
   .var (.mk "y")⟩

/-- A top-level signature scopes its type variable through RHS annotations,
    including annotations nested under an inner `let`. -/
private def pScopedSingleton : Surface.Program :=
  let a : ValName := .mk "a"
  let x : ValName := .mk "x"
  let y : ValName := .mk "y"
  let id : ValName := .mk "id"
  ⟨[],
   [[{ name := id
       ann := some ⟨[a], .arrow (.tvar a) (.tvar a)⟩
       rhs := .lambda (.name x) (some (.tvar a))
         (.letIn y [] [] (some ⟨[], .tvar a⟩) (.var x) (.var y)) }]],
   .app (.var id) (.primLit (.int 1))⟩

/-- Scoped variables are rigid: the annotation cannot be specialized to make
    integer addition fit a claimed `∀ a. a → a`. -/
private def pScopedRigidReject : Surface.Program :=
  let a : ValName := .mk "a"
  let x : ValName := .mk "x"
  let bad : ValName := .mk "bad"
  ⟨[],
   [[{ name := bad
       ann := some ⟨[a], .arrow (.tvar a) (.tvar a)⟩
       rhs := .lambda (.name x) (some (.tvar a))
         (.app (.app (.primBinOp .intAdd) (.var x)) (.primLit (.int 1))) }]],
   .app (.var bad) (.primLit (.int 1))⟩

-- redeclaring Bool clashes with prelude
#guard (lowerCoreProgram pClashBool).isNone
-- user field references prelude type; combined decl group elaborates
#guard match lowerDataDeclsIn preludeKindEnv
    [⟨.mk "Box", [], [(.mk "Mk", [.customTy (.mk "List") [.prim .bool]])]⟩] with
  | some userCore => (elabDecls (preludeDecls ++ userCore)).isSome
  | none => false
-- wrong-arity prelude ref in a user field → rejected
#guard (lowerDataDeclsIn preludeKindEnv
  [⟨.mk "Bad", [], [(.mk "Mk", [.customTy (.mk "List") [.prim .int, .prim .int]])]⟩]).isNone
-- user ctor name clashes with prelude ctor True → rejected
#guard (lowerCoreProgram ⟨[⟨.mk "Box", [], [(.mk "True", [])]⟩], [], .primLit (.int 0)⟩).isNone
-- empty group is a no-op (`term` equals body)
#guard match Surface.desugarGroups [[]] (.primLit (.int 0)) with
  | .primLit (.int 0) => true
  | _ => false
#guard match pLetOne.term with
  | .letIn (.mk "x") [] [] none (.primLit (.int 1)) (.var (.mk "x")) => true
  | _ => false
#guard match Surface.desugarGroups
    [[{ name := .mk "loop", ann := none, rhs := .var (.mk "loop") }]]
    (.var (.mk "loop")) with
  | .letRecIn [_] (.var (.mk "loop")) => true
  | _ => false
#guard match lowerCoreProgram pScopedSingleton with
  | some (ctors, core) => (coreTypecheck ctors core).isSome
  | none => false
#guard match lowerCoreProgram pScopedRigidReject with
  | some (ctors, core) => (coreTypecheck ctors core).isNone
  | none => false
#guard (Program.ofFlat [] [bA, { name := .mk "a", ann := none, rhs := .primLit (.int 0) }]
  (.primLit (.int 0))).isNone
-- SurfaceCovers is inhabited for the Maybe term (no matches → trivial coverage)
example : ∀ ctors, SurfaceCovers ctors pMaybeId.term := fun _ =>
  .app (.ctor) (.primLit)


/-! ## 10. Surface-program type safety

A well-typed, exhaustive surface program elaborates to a Core term that is
type-safe and never gets stuck. Stated over the executable pipeline (`lowerCore`
succeeds, `coreTypecheck` succeeds, patterns cover) — the object that actually runs.

The declarative `SurfaceWT` corollary closes the specification/implementation
loop: structural surface typing plus coverage implies that the concrete `lowerCore`
output typechecks, after which `surface_type_safe` applies. -/

/-- Well-typed surface programs lowerCore to Core whose erased runtime term is
    HM-typed, match-exhaustive, and non-stuck. Source annotations are static and
    do not enter `SmallStep.Step`. -/
theorem surface_type_safe {ctors : CtorEnv} {s : Surface.Expr} {c : Expr}
    (hlow : lowerCore ctors s = some c)
    (htc : (coreTypecheck ctors c).isSome)
    (hcov : SurfaceCovers ctors s) :
    ∃ τ, RuntimeTyping.RunWT ⟨[], ctors⟩ (c.erase) τ ∧
      AllMatchesExhaustive ctors (c.erase) ∧
      ∀ e', Relation.ReflTransGen Step (c.erase) e' →
        (IsValue e' ∨ ∃ e'', Step e' e'') := by
  obtain ⟨result, hresult⟩ := infer_of_typecheck (lowerCore_tyClosed hlow) htc
  have hsource : TypeOfHM ⟨[], ctors⟩ c result.ty := inferOfCore_source_sound hresult
  have hty : RuntimeTyping.RunWT ⟨[], ctors⟩ c.erase result.ty := hsource.erase_preserves_typing
  have hexh : AllMatchesExhaustive ctors c.erase :=
    SmallStep.AllMatchesExhaustive.erase (lowerCore_exhaustive hcov hlow)
  have hexhSource : AllMatchesExhaustive ctors c := lowerCore_exhaustive hcov hlow
  -- Check first, erase second: the source derivation launches the erased
  -- runtime safety chain under `RunWT`.
  have hsafe : ∀ e', Relation.ReflTransGen Step (c.erase) e' →
      IsValue e' ∨ ∃ e'', Step e' e'' := by
    intro e' hrtc
    exact (TypeOfHM.erased_type_safety_star hsource hexhSource e' hrtc).2
  exact ⟨result.ty, hty, hexh, hsafe⟩

/-- **Well-typed surface programs don't go wrong** (program-level).
    Composes decl elaboration with `surface_type_safe` on the desugared term. -/
theorem program_type_safe {p : Surface.Program} {ctors : CtorEnv} {c : Expr}
    (hlow : lowerCoreProgram p = some (ctors, c))
    (htc : (coreTypecheck ctors c).isSome)
    (hcov : SurfaceCovers ctors p.term) :
    ∃ τ, RuntimeTyping.RunWT ⟨[], ctors⟩ (c.erase) τ ∧
      AllMatchesExhaustive ctors (c.erase) ∧
      ∀ e', Relation.ReflTransGen Step (c.erase) e' →
        (IsValue e' ∨ ∃ e'', Step e' e'') := by
  obtain ⟨userCore, hUser, hb⟩ := option_bind_eq_some hlow
  obtain ⟨ctors', hElab, hb'⟩ := option_bind_eq_some hb
  obtain ⟨c', hBody, hPure⟩ := option_bind_eq_some hb'
  simp at hPure
  obtain ⟨rfl, rfl⟩ := hPure
  obtain ⟨τ, hty, hexh, hsafe⟩ := surface_type_safe hBody htc hcov
  exact ⟨τ, hty, hexh, hsafe⟩


end SurfaceBridge

@[simp] theorem finalizeInputAnn_noHead (ann : Option Surface.PolyTy) :
    finalizeInputAnn [] [] ann = SurfaceBridge.finalizeAnn [] [] ann := rfl
