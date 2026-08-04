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

/-- Bool detector → inductive Prop (HM gate uses this). -/
theorem DoesntContainBounds_of_not_containsBl {p : Program}
    (h : programContainsBl p = false) :
    Program.DoesntContainBounds p := by
  sorry

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
  sorry

theorem programContainsBl_eq_false_of_noBl {p : Program}
    (h : Program.DoesntContainBounds p) : programContainsBl p = false := by
  sorry

theorem hmRequireNoBl_isOk_of_noBl {p : Program}
    (h : programContainsBl p = false) :
    (hmRequireNoBl p).isOk := by
  sorry

theorem hmRequireNoBl_not_isOk_of_bl {p : Program}
    (h : programContainsBl p = true) :
    ¬ (hmRequireNoBl p).isOk := by
  sorry

theorem ofLower_bodyAnn (env : List ValName) (ep : ErasedProgram) :
    (ProgramBoundsAnns.ofLower env ep).bodyAnn = ep.bodyAnn := by
  rfl

theorem ofLower_get_of_find (env : List ValName) (ep : ErasedProgram)
    {n : ValName} {ann : BinderAnn} {i : Nat}
    (hi : env[i]? = some n)
    (hf : ep.toSurfaceAnns.byName.find? (fun ⟨n', _⟩ => n' = n) = some (n, ann)) :
    ProgramBoundsAnns.get? (ProgramBoundsAnns.ofLower env ep) i = some ann := by
  sorry

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
