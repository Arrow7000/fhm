import FHM.SurfaceLang
import FHM.Bounds.Erase
import FHM.Bounds.Ann

/-!
# P4c — pipeline contract (mode gate + ofLower)

Wired from Live/`--bl`. Gate and erase are **separate**: `hmRequireNoBl` is D16
only; `eraseProgram` always runs. Under `--bl`, Live runs `ofLower` + origin
HasBounds synth / ascription check (slice 4; D22).

**Deprecated packaging path (2026-08-04):** `eraseProgram` / `ofLower` are **not**
the live product contract going forward. See
`briefs/design-memo-bounds-preserving-elaboration.md`. Replacement: keep BL on
Core through Infer; bounds second elab. Do not extend this erase/`ofLower` API;
may remain until Phase 5.

## Architecture (legacy dual-walk packaging; still wired today)

```text
surface Program
    │
    ├─ .hm: hmRequireNoBl          ← D16 gate only (no erase)
    │
    └─ both modes ─► eraseProgram  ← Erase.lean (total; always)
                          ▼
              ErasedSurface { mode, erased }
                          │
         lower erased.toProgram
                          │
              .bl: ofLower → origin synth + MeetsAscription
```

## Design locks

* **M1** `.hm` — `hmRequireNoBl` fail-fast on BL (D16). Does not erase.
* **M2** Both modes then `eraseProgram`; lower `erased.toProgram`.
* **M3** Bounds on `ErasedBinding` (from erase); `ofLower` after lower.
* **M4** `binderEnvFromGroups` = `groups.reverse.flatMap` (0 = innermost; within-group order preserved).
-/

namespace FHM.Bounds.Pipeline

open Surface (Program Binding DataDecl Pattern)
open FHM.Bounds (BoundsAnnTy ProgramBoundsAnns)
open FHM.Bounds.Erase

/-! ## Types & props (shapes) -/

/-- Frontend / pipeline mode (CLI `--bl` selects `.bl`). -/
inductive BoundsMode where
  | hm
  | bl
  deriving DecidableEq, Repr

/-- Default frontend mode: plain HM (no BL). -/
def BoundsMode.default : BoundsMode := .hm

/-- HM-accepted surface: no `BL` (D16). Produced by the gate, not by erase. -/
structure HmProgram where
  program : Surface.Program
  noBl : Program.DoesntContainBounds program

/-- Erased surface tagged with the mode that accepted it.

Built by Live as `{ mode, erased := eraseProgram … }` after any HM gate. -/
structure ErasedSurface where
  mode : BoundsMode
  erased : ErasedProgram

/-! ## BL detectors (Bool; Prop linkage below) -/

/-- Any `BL` in a type (re-export Erase helper). -/
abbrev tyContainsBl : Surface.Ty → Bool := FHM.Bounds.Erase.tyContainsBl

def polyContainsBl (σ : Surface.PolyTy) : Bool :=
  tyContainsBl σ.body

def optPolyContainsBl : Option Surface.PolyTy → Bool
  | none => false
  | some σ => polyContainsBl σ

def optTyContainsBl : Option Surface.Ty → Bool
  | none => false
  | some t => tyContainsBl t

def paramsContainBl (ps : List (ValName × Option Surface.Ty)) : Bool :=
  ps.any fun (_, t?) => optTyContainsBl t?

/-- Walk surface expressions for BL in type positions. -/
def exprContainsBl : Surface.Expr → Bool :=
  Surface.Expr.rec_strong
    (fun _ => false)
    (fun _ => false)
    (fun _ _ ca cb => ca || cb)
    (fun _ _ ch ct => ch || ct)
    (fun items ih => (items.attach.map fun ⟨e, he⟩ => ih e he).any id)
    (fun _param paramAnn _body eb => optTyContainsBl paramAnn || eb)
    (fun _f _a ef ea => ef || ea)
    (fun _name _tvs params ann _rhs _body erhs ebody =>
      paramsContainBl params || optPolyContainsBl ann || erhs || ebody)
    (fun bindings _body ihbs ebody =>
      (bindings.attach.map fun ⟨b, hb⟩ =>
        paramsContainBl b.params || optPolyContainsBl b.ann || ihbs b hb).any id
      || ebody)
    (fun _ => false)
    (fun _ => false)
    (fun _ _ _ ec et ef => ec || et || ef)
    (fun _s brs es ihb =>
      es || (brs.attach.map fun ⟨⟨_p, e⟩, h⟩ => ihb _p e h).any id)

def dataDeclContainsBl (d : DataDecl) : Bool :=
  d.ctors.any fun (_, fs) => fs.any tyContainsBl

/-- `true` if any surface type in the program mentions `BL`. -/
def programContainsBl (p : Surface.Program) : Bool :=
  exprContainsBl p.body
  || p.decls.any dataDeclContainsBl
  || p.groups.any fun g =>
      g.any fun b =>
        paramsContainBl b.params || optPolyContainsBl b.ann || exprContainsBl b.rhs

private theorem tyNoBl_of_containsBl_false (ty : Surface.Ty)
    (h : tyContainsBl ty = false) : Surface.Ty.DoesntContainBounds ty := by
  induction ty using Surface.Ty.rec_strong with
  | prim => exact .prim
  | tvar => exact .tvar
  | pair left right ihLeft ihRight | arrow left right ihLeft ihRight =>
      have both : tyContainsBl left = false ∧ tyContainsBl right = false := by
        simpa only [tyContainsBl, FHM.Bounds.Erase.tyContainsBl,
          Surface.Ty.rec_strong.eq_2, Surface.Ty.rec_strong.eq_3,
          Bool.or_eq_false_iff] using h
      first
      | exact .pair (ihLeft both.1) (ihRight both.2)
      | exact .arrow (ihLeft both.1) (ihRight both.2)
  | customTy name args ih =>
      apply Surface.Ty.DoesntContainBounds.customTy
      intro arg member
      apply ih arg member
      apply Bool.eq_false_iff.mpr
      intro argTrue
      have anyTrue :
          (args.attach.map (fun ⟨source, sourceMember⟩ => tyContainsBl source)).any id = true :=
        List.any_eq_true.mpr ⟨tyContainsBl arg, by
          apply List.mem_map.mpr
          exact ⟨⟨arg, member⟩, by simp, rfl⟩, by simpa using argTrue⟩
      have none :
          (args.attach.map (fun ⟨source, sourceMember⟩ => tyContainsBl source)).any id = false := by
        simpa only [tyContainsBl, FHM.Bounds.Erase.tyContainsBl,
          Surface.Ty.rec_strong.eq_5] using h
      rw [none] at anyTrue
      cases anyTrue
  | bl => simp [tyContainsBl, FHM.Bounds.Erase.tyContainsBl,
      Surface.Ty.rec_strong.eq_6] at h

private theorem containsBl_false_of_tyNoBl {ty : Surface.Ty}
    (h : Surface.Ty.DoesntContainBounds ty) : tyContainsBl ty = false := by
  induction h with
  | prim => simp [tyContainsBl, FHM.Bounds.Erase.tyContainsBl,
      Surface.Ty.rec_strong.eq_1]
  | tvar => simp [tyContainsBl, FHM.Bounds.Erase.tyContainsBl,
      Surface.Ty.rec_strong.eq_4]
  | pair _ _ ihLeft ihRight | arrow _ _ ihLeft ihRight =>
      simp only [tyContainsBl, FHM.Bounds.Erase.tyContainsBl,
        Surface.Ty.rec_strong.eq_2, Surface.Ty.rec_strong.eq_3]
      have rawLeft := ihLeft
      have rawRight := ihRight
      simp only [tyContainsBl, FHM.Bounds.Erase.tyContainsBl] at rawLeft rawRight
      rw [rawLeft, rawRight]
      rfl
  | customTy fields ih =>
      simp only [tyContainsBl, FHM.Bounds.Erase.tyContainsBl,
        Surface.Ty.rec_strong.eq_5]
      apply List.any_eq_false.mpr
      intro value member valueTrue
      obtain ⟨attached, _, rfl⟩ := List.mem_map.mp member
      rcases attached with ⟨source, sourceMember⟩
      exact Bool.eq_false_iff.mp (ih source sourceMember) valueTrue

private theorem polyNoBl_of_containsBl_false (scheme : Surface.PolyTy)
    (h : polyContainsBl scheme = false) : Surface.PolyTy.DoesntContainBounds scheme :=
  .mk (tyNoBl_of_containsBl_false scheme.body h)

private theorem containsBl_false_of_polyNoBl {scheme : Surface.PolyTy}
    (h : Surface.PolyTy.DoesntContainBounds scheme) : polyContainsBl scheme = false := by
  cases h with
  | mk body => exact containsBl_false_of_tyNoBl body

private theorem containsBl_false_of_optTyNoBl {annotation : Option Surface.Ty}
    (h : ∀ ty, annotation = some ty → Surface.Ty.DoesntContainBounds ty) :
    optTyContainsBl annotation = false := by
  cases annotation with
  | none => rfl
  | some ty => exact containsBl_false_of_tyNoBl (h ty rfl)

private theorem containsBl_false_of_optPolyNoBl {annotation : Option Surface.PolyTy}
    (h : ∀ scheme, annotation = some scheme → Surface.PolyTy.DoesntContainBounds scheme) :
    optPolyContainsBl annotation = false := by
  cases annotation with
  | none => rfl
  | some scheme => exact containsBl_false_of_polyNoBl (h scheme rfl)

private theorem optTyNoBl_of_containsBl_false {annotation : Option Surface.Ty}
    (h : optTyContainsBl annotation = false) :
    ∀ ty, annotation = some ty → Surface.Ty.DoesntContainBounds ty := by
  intro ty equality
  subst annotation
  exact tyNoBl_of_containsBl_false ty h

private theorem optPolyNoBl_of_containsBl_false {annotation : Option Surface.PolyTy}
    (h : optPolyContainsBl annotation = false) :
    ∀ scheme, annotation = some scheme → Surface.PolyTy.DoesntContainBounds scheme := by
  intro scheme equality
  subst annotation
  exact polyNoBl_of_containsBl_false scheme h

private theorem paramsNoBl_of_containsBl_false
    (params : List (ValName × Option Surface.Ty))
    (h : paramsContainBl params = false) :
    ∀ name ty, (name, some ty) ∈ params → Surface.Ty.DoesntContainBounds ty := by
  intro name ty member
  apply tyNoBl_of_containsBl_false ty
  apply Bool.eq_false_iff.mpr
  intro tyTrue
  have anyTrue : params.any (fun (_, annotation) => optTyContainsBl annotation) = true :=
    List.any_eq_true.mpr ⟨(name, some ty), member, by simpa [optTyContainsBl] using tyTrue⟩
  have none : params.any (fun (_, annotation) => optTyContainsBl annotation) = false := by
    simpa only [paramsContainBl] using h
  rw [none] at anyTrue
  cases anyTrue

private theorem containsBl_false_of_paramsNoBl
    (params : List (ValName × Option Surface.Ty))
    (h : ∀ name ty, (name, some ty) ∈ params → Surface.Ty.DoesntContainBounds ty) :
    paramsContainBl params = false := by
  apply List.any_eq_false.mpr
  intro entry member entryTrue
  rcases entry with ⟨name, annotation⟩
  cases annotation with
  | none => cases entryTrue
  | some ty =>
      exact Bool.eq_false_iff.mp (containsBl_false_of_tyNoBl (h name ty member)) entryTrue

private theorem exprNoBl_of_containsBl_false (e : Surface.Expr)
    (h : exprContainsBl e = false) : Surface.Expr.DoesntContainBounds e := by
  induction e using Surface.Expr.rec_strong with
  | primLit => exact .primLit
  | primBinOp => exact .primBinOp
  | pair left right ihLeft ihRight | cons left right ihLeft ihRight =>
      have both : exprContainsBl left = false ∧ exprContainsBl right = false := by
        simpa only [exprContainsBl, Surface.Expr.rec_strong.eq_3,
          Surface.Expr.rec_strong.eq_4, Bool.or_eq_false_iff] using h
      first
      | exact .pair (ihLeft both.1) (ihRight both.2)
      | exact .cons (ihLeft both.1) (ihRight both.2)
  | list items ih =>
      apply Surface.Expr.DoesntContainBounds.list
      intro item member
      apply ih item member
      have allFalse := List.any_eq_false.mp (by
        simpa only [exprContainsBl, Surface.Expr.rec_strong.eq_5] using h)
      apply Bool.eq_false_iff.mpr
      exact allFalse (exprContainsBl item) (by
          apply List.mem_map.mpr
          exact ⟨⟨item, member⟩, by simp, rfl⟩)
  | lambda param annotation body ihBody =>
      have both : optTyContainsBl annotation = false ∧ exprContainsBl body = false := by
        simpa only [exprContainsBl, Surface.Expr.rec_strong.eq_6,
          Bool.or_eq_false_iff] using h
      exact .lambda (optTyNoBl_of_containsBl_false both.1) (ihBody both.2)
  | app fn arg ihFn ihArg =>
      have both : exprContainsBl fn = false ∧ exprContainsBl arg = false := by
        simpa only [exprContainsBl, Surface.Expr.rec_strong.eq_7,
          Bool.or_eq_false_iff] using h
      exact .app (ihFn both.1) (ihArg both.2)
  | letIn name tyParams params annotation rhs body ihRhs ihBody =>
      have all : paramsContainBl params = false ∧ optPolyContainsBl annotation = false ∧
          exprContainsBl rhs = false ∧ exprContainsBl body = false := by
        simpa only [exprContainsBl, Surface.Expr.rec_strong.eq_8,
          Bool.or_eq_false_iff, and_assoc] using h
      exact .letIn
        (paramsNoBl_of_containsBl_false params all.1)
        (optPolyNoBl_of_containsBl_false all.2.1)
        (ihRhs all.2.2.1) (ihBody all.2.2.2)
  | letRecIn bindings body ihBindings ihBody =>
      have both :
          (bindings.attach.map fun ⟨binding, _⟩ =>
            paramsContainBl binding.params || optPolyContainsBl binding.ann ||
              exprContainsBl binding.rhs).any id = false ∧
          exprContainsBl body = false := by
        simpa only [exprContainsBl, Surface.Expr.rec_strong.eq_9,
          Bool.or_eq_false_iff] using h
      have bindingFalse (binding : Binding) (member : binding ∈ bindings) :
          paramsContainBl binding.params = false ∧
          optPolyContainsBl binding.ann = false ∧
          exprContainsBl binding.rhs = false := by
        have allFalse := List.any_eq_false.mp both.1
        have entryFalse :
            (paramsContainBl binding.params || optPolyContainsBl binding.ann ||
              exprContainsBl binding.rhs) = false := Bool.eq_false_iff.mpr <| allFalse
                (paramsContainBl binding.params || optPolyContainsBl binding.ann ||
                  exprContainsBl binding.rhs) (by
                    apply List.mem_map.mpr
                    exact ⟨⟨binding, member⟩, by simp, rfl⟩)
        simpa only [Bool.or_eq_false_iff, and_assoc] using entryFalse
      apply Surface.Expr.DoesntContainBounds.letRecIn
      · intro binding member
        exact paramsNoBl_of_containsBl_false binding.params (bindingFalse binding member).1
      · intro binding member
        exact optPolyNoBl_of_containsBl_false (bindingFalse binding member).2.1
      · intro binding member
        exact ihBindings binding member (bindingFalse binding member).2.2
      · exact ihBody both.2
  | var => exact .var
  | ctor => exact .ctor
  | ife cond yes no ihCond ihYes ihNo =>
      have all : exprContainsBl cond = false ∧ exprContainsBl yes = false ∧
          exprContainsBl no = false := by
        simpa only [exprContainsBl, Surface.Expr.rec_strong.eq_12,
          Bool.or_eq_false_iff, and_assoc] using h
      exact .ife (ihCond all.1) (ihYes all.2.1) (ihNo all.2.2)
  | match_ scrutinee branches ihScrutinee ihBranches =>
      have both : exprContainsBl scrutinee = false ∧
          (branches.attach.map fun ⟨⟨_, branch⟩, _⟩ => exprContainsBl branch).any id = false := by
        simpa only [exprContainsBl, Surface.Expr.rec_strong.eq_13,
          Bool.or_eq_false_iff] using h
      apply Surface.Expr.DoesntContainBounds.match_ (ihScrutinee both.1)
      intro pattern branch member
      apply ihBranches pattern branch member
      have allFalse := List.any_eq_false.mp both.2
      apply Bool.eq_false_iff.mpr
      exact allFalse (exprContainsBl branch) (by
          apply List.mem_map.mpr
          exact ⟨⟨(pattern, branch), member⟩, by simp, rfl⟩)

private theorem value_false_of_any_false {α : Type} {values : List α} {predicate : α → Bool}
    (h : values.any predicate = false) {value : α} (member : value ∈ values) :
    predicate value = false :=
  Bool.eq_false_iff.mpr (List.any_eq_false.mp h value member)

private theorem any_false_of_values_false {α : Type} {values : List α} {predicate : α → Bool}
    (h : ∀ value ∈ values, predicate value = false) : values.any predicate = false := by
  apply List.any_eq_false.mpr
  intro value member
  exact Bool.eq_false_iff.mp (h value member)

private theorem dataNoBl_of_containsBl_false (declaration : DataDecl)
    (h : dataDeclContainsBl declaration = false) :
    DataDecl.DoesntContainBounds declaration := by
  constructor
  intro ctor fields fieldGroupMember ty tyMember
  have fieldsFalse : fields.any tyContainsBl = false :=
    value_false_of_any_false h fieldGroupMember
  exact tyNoBl_of_containsBl_false ty
    (value_false_of_any_false fieldsFalse tyMember)

private theorem bindingNoBl_of_containsBl_false (binding : Binding)
    (hParams : paramsContainBl binding.params = false)
    (hAnn : optPolyContainsBl binding.ann = false)
    (hRhs : exprContainsBl binding.rhs = false) :
    Binding.DoesntContainBounds binding where
  params := paramsNoBl_of_containsBl_false binding.params hParams
  ann := optPolyNoBl_of_containsBl_false hAnn
  rhs := exprNoBl_of_containsBl_false binding.rhs hRhs

/-- Bool detector → inductive Prop (HM gate uses this). -/
theorem DoesntContainBounds_of_not_containsBl {p : Program}
    (h : programContainsBl p = false) :
    Program.DoesntContainBounds p := by
  have all : exprContainsBl p.body = false ∧
      p.decls.any dataDeclContainsBl = false ∧
      p.groups.any (fun group => group.any fun binding =>
        paramsContainBl binding.params || optPolyContainsBl binding.ann ||
          exprContainsBl binding.rhs) = false := by
    simpa only [programContainsBl, Bool.or_eq_false_iff, and_assoc] using h
  apply Program.DoesntContainBounds.mk
  · intro declaration member
    exact dataNoBl_of_containsBl_false declaration
      (value_false_of_any_false all.2.1 member)
  · intro group groupMember binding bindingMember
    have groupFalse :
        group.any (fun candidate => paramsContainBl candidate.params ||
          optPolyContainsBl candidate.ann || exprContainsBl candidate.rhs) = false :=
      value_false_of_any_false all.2.2 groupMember
    have bindingFalse :
        (paramsContainBl binding.params || optPolyContainsBl binding.ann ||
          exprContainsBl binding.rhs) = false :=
      value_false_of_any_false groupFalse bindingMember
    have parts : paramsContainBl binding.params = false ∧
        optPolyContainsBl binding.ann = false ∧
        exprContainsBl binding.rhs = false := by
      simpa only [Bool.or_eq_false_iff, and_assoc] using bindingFalse
    exact bindingNoBl_of_containsBl_false binding parts.1 parts.2.1 parts.2.2
  · exact exprNoBl_of_containsBl_false p.body all.1

/-! ## HM gate (D16) — not erase -/

/-- Reject BL syntax in HM mode. Returns a proof-carrying program; does **not**
erase. Caller still runs `eraseProgram` (shared with `.bl`). -/
def hmRequireNoBl (p : Program) : Except String HmProgram :=
  if h : programContainsBl p = false then
    .ok ⟨p, DoesntContainBounds_of_not_containsBl h⟩
  else
    .error "bounded-list syntax (BL) requires --bl"

/-! ## Name → de Bruijn (post-lower) -/

/-- Map erase binder anns onto a de Bruijn spine.

`binderEnv[i]` is the name of Core env slot `i` (**0 = innermost**).
Names with no `ErasedBinding` ann/scheme get `none`. Call **after** lower.

**Deprecated for product path (2026-08-04).** See
`briefs/design-memo-bounds-preserving-elaboration.md`. Keep BL on Core through
Infer; bounds second elab. Do not extend this API; may remain until Phase 5. -/
def ProgramBoundsAnns.ofLower
    (binderEnv : List ValName) (ep : ErasedProgram) : ProgramBoundsAnns :=
  let surf := ep.toSurfaceAnns
  { binderAnns := binderEnv.map fun n =>
      (surf.byName.find? fun ⟨n', _⟩ => n' = n).map (·.2)
    bodyAnn := surf.bodyAnn }

/-- Core env names for the program body: index **0 = innermost**.

`letRecElab` puts member 0 of the innermost SCC group at de Bruijn 0, then the
rest of that group, then outer groups. So: reverse the group list, preserve
within-group binding order (do **not** reverse the flattened name list). -/
def binderEnvFromGroups (groups : List (List Binding)) : List ValName :=
  groups.reverse.flatMap (·.map (·.name))

def binderEnvFromErased (ep : ErasedProgram) : List ValName :=
  binderEnvFromGroups ep.toProgram.groups

/-! ## Theorems (prove after shape ✅) -/

theorem exprContainsBl_eq_false_of_noBl {e : Surface.Expr}
    (h : Surface.Expr.DoesntContainBounds e) : exprContainsBl e = false := by
  induction h with
  | primLit => simp [exprContainsBl, Surface.Expr.rec_strong.eq_1]
  | primBinOp => simp [exprContainsBl, Surface.Expr.rec_strong.eq_2]
  | pair _ _ ihLeft ihRight | cons _ _ ihLeft ihRight =>
      simp only [exprContainsBl, Surface.Expr.rec_strong.eq_3,
        Surface.Expr.rec_strong.eq_4]
      have rawLeft := ihLeft
      have rawRight := ihRight
      simp only [exprContainsBl] at rawLeft rawRight
      rw [rawLeft, rawRight]
      rfl
  | list noBl ih =>
      simp only [exprContainsBl, Surface.Expr.rec_strong.eq_5]
      apply any_false_of_values_false
      intro value member
      obtain ⟨attached, _, rfl⟩ := List.mem_map.mp member
      rcases attached with ⟨source, sourceMember⟩
      exact ih source sourceMember
  | lambda annotationNoBl _ ihBody =>
      simp only [exprContainsBl, Surface.Expr.rec_strong.eq_6]
      simp only [exprContainsBl] at ihBody
      rw [containsBl_false_of_optTyNoBl annotationNoBl, ihBody]
      rfl
  | app _ _ ihFn ihArg =>
      simp only [exprContainsBl, Surface.Expr.rec_strong.eq_7]
      simp only [exprContainsBl] at ihFn ihArg
      rw [ihFn, ihArg]
      rfl
  | letIn paramsNoBl annotationNoBl _ _ ihRhs ihBody =>
      simp only [exprContainsBl, Surface.Expr.rec_strong.eq_8]
      simp only [exprContainsBl] at ihRhs ihBody
      rw [containsBl_false_of_paramsNoBl _ paramsNoBl,
        containsBl_false_of_optPolyNoBl annotationNoBl, ihRhs, ihBody]
      rfl
  | letRecIn paramsNoBl annotationNoBl rhsNoBl bodyNoBl ihRhs ihBody =>
      rename_i bindings body
      simp only [exprContainsBl, Surface.Expr.rec_strong.eq_9]
      have bindingsFalse :
          (bindings.attach.map fun ⟨binding, _⟩ =>
            paramsContainBl binding.params || optPolyContainsBl binding.ann ||
              exprContainsBl binding.rhs).any id = false := by
        apply any_false_of_values_false
        intro value member
        obtain ⟨attached, _, rfl⟩ := List.mem_map.mp member
        rcases attached with ⟨binding, bindingMember⟩
        have rhsFalse := ihRhs binding bindingMember
        simp only [id_eq]
        rw [containsBl_false_of_paramsNoBl binding.params (paramsNoBl binding bindingMember),
          containsBl_false_of_optPolyNoBl (annotationNoBl binding bindingMember),
          rhsFalse]
        rfl
      simp only [exprContainsBl] at bindingsFalse
      simp only [exprContainsBl] at ihBody
      rw [bindingsFalse, ihBody]
      rfl
  | var => simp [exprContainsBl, Surface.Expr.rec_strong.eq_10]
  | ctor => simp [exprContainsBl, Surface.Expr.rec_strong.eq_11]
  | ife _ _ _ ihCond ihYes ihNo =>
      simp only [exprContainsBl, Surface.Expr.rec_strong.eq_12]
      simp only [exprContainsBl] at ihCond ihYes ihNo
      rw [ihCond, ihYes, ihNo]
      rfl
  | match_ scrutineeNoBl branchesNoBl ihScrutinee ihBranches =>
      rename_i scrutinee branches
      simp only [exprContainsBl, Surface.Expr.rec_strong.eq_13]
      have branchesFalse :
          (branches.attach.map fun ⟨⟨_, branch⟩, _⟩ =>
            exprContainsBl branch).any id = false := by
        apply any_false_of_values_false
        intro value member
        obtain ⟨attached, _, rfl⟩ := List.mem_map.mp member
        rcases attached with ⟨⟨pattern, branch⟩, branchMember⟩
        have branchFalse := ihBranches pattern branch branchMember
        simpa only [exprContainsBl] using branchFalse
      simp only [exprContainsBl] at branchesFalse
      simp only [exprContainsBl] at ihScrutinee
      rw [ihScrutinee, branchesFalse]
      rfl

private theorem dataContainsBl_eq_false_of_noBl {declaration : DataDecl}
    (h : DataDecl.DoesntContainBounds declaration) :
    dataDeclContainsBl declaration = false := by
  cases h with
  | mk fieldsNoBl =>
      apply any_false_of_values_false
      intro entry member
      rcases entry with ⟨ctor, fields⟩
      apply any_false_of_values_false
      intro ty tyMember
      exact containsBl_false_of_tyNoBl (fieldsNoBl ctor fields member ty tyMember)

private theorem bindingContainsBl_eq_false_of_noBl {binding : Binding}
    (h : Binding.DoesntContainBounds binding) :
    (paramsContainBl binding.params || optPolyContainsBl binding.ann ||
      exprContainsBl binding.rhs) = false := by
  rw [containsBl_false_of_paramsNoBl binding.params h.params,
    containsBl_false_of_optPolyNoBl h.ann,
    exprContainsBl_eq_false_of_noBl h.rhs]
  rfl

theorem programContainsBl_eq_false_of_noBl {p : Program}
    (h : Program.DoesntContainBounds p) : programContainsBl p = false := by
  cases h with
  | mk declarationsNoBl groupsNoBl bodyNoBl =>
      have declarationsFalse : p.decls.any dataDeclContainsBl = false :=
        any_false_of_values_false fun declaration member =>
          dataContainsBl_eq_false_of_noBl (declarationsNoBl declaration member)
      have groupsFalse :
          p.groups.any (fun group => group.any fun binding =>
            paramsContainBl binding.params || optPolyContainsBl binding.ann ||
              exprContainsBl binding.rhs) = false := by
        apply any_false_of_values_false
        intro group groupMember
        apply any_false_of_values_false
        intro binding bindingMember
        exact bindingContainsBl_eq_false_of_noBl
          (groupsNoBl group groupMember binding bindingMember)
      rw [programContainsBl, exprContainsBl_eq_false_of_noBl bodyNoBl,
        declarationsFalse, groupsFalse]
      rfl

theorem hmRequireNoBl_isOk_of_noBl {p : Program}
    (h : programContainsBl p = false) :
    (hmRequireNoBl p).isOk := by
  simp [hmRequireNoBl, h]
  rfl

theorem hmRequireNoBl_not_isOk_of_bl {p : Program}
    (h : programContainsBl p = true) :
    ¬ (hmRequireNoBl p).isOk := by
  simp [hmRequireNoBl, h]
  rfl

theorem ofLower_bodyAnn (env : List ValName) (ep : ErasedProgram) :
    (ProgramBoundsAnns.ofLower env ep).bodyAnn = ep.bodyAnn := by
  rfl

theorem ofLower_get_of_find (env : List ValName) (ep : ErasedProgram)
    {n : ValName} {ann : BinderAnn} {i : Nat}
    (hi : env[i]? = some n)
    (hf : ep.toSurfaceAnns.byName.find? (fun ⟨n', _⟩ => n' = n) = some (n, ann)) :
    ProgramBoundsAnns.get? (ProgramBoundsAnns.ofLower env ep) i = some ann := by
  simp [ProgramBoundsAnns.get?, ProgramBoundsAnns.ofLower, List.getElem?_map, hi, hf]

/-! ## Guards -/

private def tyBl : Surface.Ty := .bl (.solid (.lit 0)) (.solid (.lit 5)) (.prim .int)
private def tyList : Surface.Ty := .customTy ⟨"List"⟩ [.prim .int]

-- `BL 0 5 Int` is detected as containing BL.
#guard tyContainsBl tyBl
-- `some (BL …)` is detected.
#guard optTyContainsBl (some tyBl)
-- Lambda param ascription `BL …` is detected in an expression.
#guard exprContainsBl (.lambda .wildcard (some tyBl) (.primLit (.int 0)))

-- Bare int program has no BL.
#guard !programContainsBl ⟨[], [], .primLit (.int 0)⟩
-- Lambda with BL param ascription is a BL program.
#guard programContainsBl ⟨[], [], .lambda .wildcard (some tyBl) (.primLit (.int 0))⟩
-- Bare `List Int` (no BL) is not a BL program.
#guard !programContainsBl ⟨[], [], .lambda .wildcard (some tyList) (.primLit (.int 0))⟩
-- BL on a top-level binder ascription is detected (groups path).
#guard programContainsBl
  ⟨[], [[{ name := ⟨"xs"⟩, ann := some ⟨[], tyBl⟩, rhs := .list [] }]], .primLit (.int 0)⟩

-- Default mode is HM.
#guard BoundsMode.default == .hm

-- HM gate rejects BL syntax.
#guard !(hmRequireNoBl ⟨[], [], .lambda .wildcard (some tyBl) (.primLit (.unit))⟩).isOk
-- HM gate accepts a program with no BL.
#guard (hmRequireNoBl ⟨[], [], .primLit (.int 0)⟩).isOk

private def annsEq (a b : List (Option BinderAnn)) : Bool :=
  reprStr a == reprStr b

private def progXsBl : Program :=
  ⟨[], [[{ name := ⟨"xs"⟩, ann := some ⟨[], tyBl⟩, rhs := .list [] }]], .var ⟨"xs"⟩⟩

-- Erase ties the BL ascription to binder `xs` (not a free-floating map).
#guard
  match (eraseProgram progXsBl).groups with
  | [[eb]] =>
      eb.binding.name == ⟨"xs"⟩ &&
      reprStr eb.ann ==
        reprStr (some (BoundsAnnTy.list (.solid (.lit 0)) (.solid (.lit 5)) (.prim .int)))
  | _ => false

-- `ofLower` maps that binder ann onto de Bruijn slot 0.
#guard annsEq (ProgramBoundsAnns.ofLower [⟨"xs"⟩] (eraseProgram progXsBl)).binderAnns
  [some (BinderAnn.mono (BoundsAnnTy.list (.solid (.lit 0)) (.solid (.lit 5)) (.prim .int)))]
-- Missing names become `none`; `xs` lands at index 1 when env is `[ys, xs]`.
#guard annsEq (ProgramBoundsAnns.ofLower [⟨"ys"⟩, ⟨"xs"⟩] (eraseProgram progXsBl)).binderAnns
  [none, some (BinderAnn.mono (BoundsAnnTy.list (.solid (.lit 0)) (.solid (.lit 5)) (.prim .int)))]

-- Slice 2: within-group order preserved; groups reversed for innermost-first.
private def progAB : Program :=
  ⟨[], [[{ name := ⟨"a"⟩, ann := none, rhs := .primLit (.int 0) },
         { name := ⟨"b"⟩, ann := none, rhs := .primLit (.int 1) }]], .var ⟨"a"⟩⟩
#guard binderEnvFromGroups progAB.groups == [⟨"a"⟩, ⟨"b"⟩]
private def progNested : Program :=
  ⟨[], [[{ name := ⟨"outer"⟩, ann := none, rhs := .primLit (.int 0) }],
        [{ name := ⟨"inner"⟩, ann := none, rhs := .primLit (.int 1) }]], .var ⟨"inner"⟩⟩
#guard binderEnvFromGroups progNested.groups == [⟨"inner"⟩, ⟨"outer"⟩]

end FHM.Bounds.Pipeline
