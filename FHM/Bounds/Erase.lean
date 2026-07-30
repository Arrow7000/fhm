import FHM.SurfaceLang
import FHM.Bounds.Ann

/-!
# P4b — eraseBounds

Strip surface `BL lo hi t` → `List t`, producing a mirrored `BoundsAnnTy`
(always — same spine as the erased type; list nodes carry user counts or
default `[0,0]` for bare `List`). Name-keyed sidecar for binder ascriptions;
de Bruijn `ProgramBoundsAnns` is **P4c**.

`Surface.Count` is solid arithmetic + named vars; `CountSlot` is hole | solid.
Named vars resolve against a Nat-binder telescope at erase (slice 7). Erase is
total on ground counts; open vars need `nats`.
-/

namespace FHM.Bounds.Erase

open Surface (Pattern Binding DataDecl Program Binding')
open FHM.Bounds (AnnoCount BoundsAnnTy listTyName boolTyName pairTyName)

/-! ## Counts -/

/-- Erase solid surface count into Kernel `Count`.

`nats` is the enclosing scheme’s Nat-binder telescope (index 0 = first / outermost).
Unbound names become rigid 0 as a temporary scaffold — pack/erase wiring will
reject them via `Except`. -/
def eraseCountSolid (c : Surface.Count) (nats : List ValName := []) : FHM.Bounds.Count :=
  match c with
  | .lit n => .lit n
  | .inf => .inf
  | .var n =>
      match nats.findIdx? (· == n) with
      | some i => .var ⟨.rigid, i⟩
      | none => .var ⟨.rigid, 0⟩
  | .add a b => .add (eraseCountSolid a nats) (eraseCountSolid b nats)
  | .mul a b => .mul (eraseCountSolid a nats) (eraseCountSolid b nats)
  | .pred a => .pred (eraseCountSolid a nats)
  | .min a b => .min (eraseCountSolid a nats) (eraseCountSolid b nats)
  | .max a b => .max (eraseCountSolid a nats) (eraseCountSolid b nats)

def eraseCount (c : Surface.CountSlot) (nats : List ValName := []) : AnnoCount :=
  match c with
  | .hole => .hole
  | .solid c => .solid (eraseCountSolid c nats)

/-! ## Prim / List helpers -/

def erasePrimTy : Surface.PrimTy → BoundsAnnTy
  | .unit => .prim .unit
  | .int  => .prim .int
  | .nat  => .prim .nat
  | .char => .prim .char
  | .bool => .custom boolTyName []

def surfaceListTy (elem : Surface.Ty) : Surface.Ty :=
  .customTy listTyName [elem]

/-- Default list interval when the surface wrote bare `List`, not `BL`. -/
def defaultListAnn (elem : BoundsAnnTy) : BoundsAnnTy :=
  .list (.solid (.lit 0)) (.solid (.lit 0)) elem

/-! ## Erased type package -/

structure ErasedTy where
  ty : Surface.Ty
  noBl : Surface.Ty.DoesntContainBounds ty
  ann : BoundsAnnTy

def eraseTyList (tys : List Surface.Ty)
    (ih : ∀ t ∈ tys, ErasedTy) : List ErasedTy :=
  tys.attach.map fun ⟨t, ht⟩ => ih t ht

theorem eraseTyList_noBl (tys : List Surface.Ty)
    (ih : ∀ t ∈ tys, ErasedTy) :
    ∀ t ∈ (eraseTyList tys ih).map (·.ty), Surface.Ty.DoesntContainBounds t := by
  intro t ht
  unfold eraseTyList at ht
  rw [List.mem_map] at ht
  obtain ⟨e, he, rfl⟩ := ht
  rw [List.mem_map] at he
  obtain ⟨⟨u, hu⟩, _, rfl⟩ := he
  exact (ih u hu).noBl

/-- Pre-erase: does this type mention `BL`? (for `byName` recording.) -/
def tyContainsBl : Surface.Ty → Bool :=
  Surface.Ty.rec_strong
    (fun _ => false)
    (fun _ _ ca cb => ca || cb)
    (fun _ _ ca cb => ca || cb)
    (fun _ => false)
    (fun _nm tys ih =>
      (tys.attach.map fun ⟨t, ht⟩ => ih t ht).any id)
    (fun _lo _hi _e _ee => true)

/-! ## Types (total via `Ty.rec_strong`) -/

/-- Erase a surface type. `nats` resolves `Count.var` under an enclosing scheme.
`tvars` maps scheme type foralls to `.fvar i` (0 = first forall / `a`). -/
def eraseTy (t : Surface.Ty) (nats : List ValName := []) (tvars : List ValName := []) :
    ErasedTy :=
  Surface.Ty.rec_strong
    (fun p => ⟨.prim p, .prim, erasePrimTy p⟩)
    (fun _a _b ea eb =>
      ⟨.pair ea.ty eb.ty, .pair ea.noBl eb.noBl,
        .custom pairTyName [ea.ann, eb.ann]⟩)
    (fun _a _b ea eb =>
      ⟨.arrow ea.ty eb.ty, .arrow ea.noBl eb.noBl, .arrow ea.ann eb.ann⟩)
    (fun n =>
      let i := (tvars.findIdx? (· == n)).getD 0
      ⟨.tvar n, .tvar, .fvar i⟩)
    (fun nm tys ih =>
      let erased := eraseTyList tys ih
      let args' := erased.map (·.ty)
      let anns := erased.map (·.ann)
      let noBlArgs := eraseTyList_noBl tys ih
      if nm = listTyName then
        match erased with
        | [eα] =>
            ⟨surfaceListTy eα.ty,
              .customTy (fun t ht => by
                have : t = eα.ty := List.mem_singleton.mp ht
                subst this
                exact eα.noBl),
              defaultListAnn eα.ann⟩
        | _ =>
            ⟨.customTy nm args', .customTy noBlArgs, .custom nm anns⟩
      else
        ⟨.customTy nm args', .customTy noBlArgs, .custom nm anns⟩)
    (fun lo hi _e ee =>
      ⟨surfaceListTy ee.ty,
        .customTy (fun t ht => by
          have : t = ee.ty := List.mem_singleton.mp ht
          subst this
          exact ee.noBl),
        .list (eraseCount lo nats) (eraseCount hi nats) ee.ann⟩)
    t

/-- Erase scheme body under optional Nat-binder telescope (sidecar, not on PolyTy).
Type foralls become `.fvar i` aligned with HM `bvar i`. -/
def erasePolyTy (σ : Surface.PolyTy) (nats : List ValName := []) :
    Surface.PolyTy × BoundsAnnTy :=
  let e := eraseTy σ.body nats σ.foralls
  ({ foralls := σ.foralls, body := e.ty }, e.ann)

/-- True if any head-param monotype mentions `BL`. -/
def paramsContainBl (ps : List (ValName × Option Surface.Ty)) : Bool :=
  ps.any fun
    | (_, some t) => tyContainsBl t
    | _ => false

/-- Fold head-param domain anns as arrows onto a result ann (R2).

Surface `params` are outermost-first; `BoundsAnnTy.arrow` is right-nested, so
`foldr`. Unannotated params are skipped (no domain slot).

Example: `(xs : BL 2 2 Int) : Int` → `BL 2 2 Int → Int`. -/
def foldHeadParamAnns (nats : List ValName) (tvars : List ValName)
    (params : List (ValName × Option Surface.Ty)) (ret : BoundsAnnTy) : BoundsAnnTy :=
  params.foldr (fun (_, t?) acc =>
    match t? with
    | none => acc
    | some t => .arrow (eraseTy t nats tvars).ann acc) ret

/-- Package Nat-binder sidecar + type foralls + erased body ann → `BoundsSchemeAnn`.
Pure mono (no Nat binders, no type foralls) → `none` (uses `ErasedBinding.ann`).

`params`: optional head-binder domains folded as arrows onto `σ.body` (R2). -/
def eraseSchemeAnn (nats : List ValName) (σ : Surface.PolyTy)
    (params : List (ValName × Option Surface.Ty) := []) :
    Option FHM.Bounds.BoundsSchemeAnn :=
  if nats.isEmpty && σ.foralls.isEmpty then none
  else
    let ret := (eraseTy σ.body nats σ.foralls).ann
    some {
      natBinders := nats
      tyBinders := σ.foralls
      body := foldHeadParamAnns nats σ.foralls params ret
    }

/-! ## Erased packages (bounds produced alongside erase) -/

/-- Flattened name→ann view for `ofLower` (derived from `ErasedProgram`, not a
second store). Prefer reading anns from `ErasedBinding` when you have the
package. -/
structure SurfaceBoundsAnns where
  byName : List (ValName × FHM.Bounds.BinderAnn) := []
  bodyAnn : Option BoundsAnnTy := none
  deriving Repr

def SurfaceBoundsAnns.empty : SurfaceBoundsAnns := {}

/-- One binder after erase — parallel to `ErasedTy`: erased binding **plus**
bounds ascription from the same erase step.

* `ann = some _` — mono surface ascription contained `BL` (no Nat binders)
* `schemeAnn = some _` — surface had `{n : Nat,…}` and/or type foralls `{a,…}`
* bare `List` / no ann → both `none`

Prefer `BinderAnn` (Ann.lean) once `ProgramBoundsAnns` migrates off bare
`Option BoundsAnnTy`. -/
structure ErasedBinding where
  binding : Binding
  ann : Option BoundsAnnTy
  schemeAnn : Option FHM.Bounds.BoundsSchemeAnn := none

/-- Combined view for migration / ofLower (mono or scheme). -/
def ErasedBinding.binderAnn (eb : ErasedBinding) : Option FHM.Bounds.BinderAnn :=
  match eb.schemeAnn, eb.ann with
  | some s, _ => some (.scheme s)
  | none, some a => some (.mono a)
  | none, none => none

/-- Erase package for a whole program (parallel to `ErasedTy`).

Bounds anns live **on the binders** (`ErasedBinding.ann`), not as a free-floating
map beside an unrelated `Program`. `toProgram` forgets anns for HM lower;
`toSurfaceAnns` / `ofLower` re-key for Core env after lower. -/
structure ErasedProgram where
  decls : List DataDecl
  groups : List (List ErasedBinding)
  body : Surface.Expr
  bodyAnn : Option BoundsAnnTy := none
  noBl : Program.DoesntContainBounds
    { decls := decls, groups := groups.map (·.map (·.binding)), body := body }

/-- HM / lower spine: drop per-binder anns. -/
def ErasedProgram.toProgram (ep : ErasedProgram) : Program where
  decls := ep.decls
  groups := ep.groups.map (·.map (·.binding))
  body := ep.body

/-- Name-keyed view of binder anns (for `ofLower`). -/
def ErasedProgram.toSurfaceAnns (ep : ErasedProgram) : SurfaceBoundsAnns where
  byName := ep.groups.flatMap fun g =>
    g.filterMap fun eb => eb.binderAnn.map (eb.binding.name, ·)
  bodyAnn := ep.bodyAnn

/-! ## Expressions / programs -/

def eraseOptTy : Option Surface.Ty → Option Surface.Ty × Option BoundsAnnTy
  | none => (none, none)
  | some t =>
      let e := eraseTy t
      (some e.ty, some e.ann)

def eraseOptPolyTy : Option Surface.PolyTy → Option Surface.PolyTy × Option BoundsAnnTy
  | none => (none, none)
  | some σ =>
      let (σ', ann) := erasePolyTy σ
      (some σ', some ann)

def eraseParams (ps : List (ValName × Option Surface.Ty)) :
    List (ValName × Option Surface.Ty) :=
  ps.map fun (n, t?) => (n, (eraseOptTy t?).1)

def eraseExpr : Surface.Expr → Surface.Expr :=
  Surface.Expr.rec_strong
    (fun p => .primLit p)
    (fun op => .primBinOp op)
    (fun _a _b ea eb => .pair ea eb)
    (fun _h _t eh et => .cons eh et)
    (fun items ih => .list (items.attach.map fun ⟨e, he⟩ => ih e he))
    (fun param paramAnn _body eb =>
      .lambda param (eraseOptTy paramAnn).1 eb)
    (fun _f _a ef ea => .app ef ea)
    (fun name tyParams params ann _rhs _body erhs ebody =>
      .letIn name tyParams (eraseParams params) (eraseOptPolyTy ann).1 erhs ebody)
    (fun bindings _body ihbs ebody =>
      .letRecIn
        (bindings.attach.map fun ⟨b, hb⟩ =>
          let ann' :=
            match b.ann with
            | some σ => some (erasePolyTy σ b.natBinders).1
            | none => none
          { b with
            params := eraseParams b.params
            ann := ann'
            natBinders := []
            rhs := ihbs b hb })
        ebody)
    (fun n => .var n)
    (fun n => .ctor n)
    (fun _c _t _f ec et ef => .ife ec et ef)
    (fun _s brs es ihb =>
      .match_ es
        (brs.attach.map fun ⟨⟨p, e⟩, h⟩ => (p, ihb p e h)))

/-- Erase one binding, producing its bounds ann in the same package.

When `eraseSchemeAnn` returns `some` (Nat and/or type foralls), leave mono `ann`
empty — scheme body carries the intervals and `∀` pretty-printing.

**R2:** head-param types `(xs : BL …)` are folded as arrow domains onto the
return ascription so `ofLower` / `checkAgainst` see the same demand spine as
`let f : BL … → … = \xs → …`. -/
def eraseBinding (b : Binding) : ErasedBinding :=
  let nats := b.natBinders
  let hadBlRet := match b.ann with | some σ => tyContainsBl σ.body | none => false
  let hadBlParams := paramsContainBl b.params
  let hadBl := hadBlRet || hadBlParams
  let (ann', annOut, schemeOut) :=
    match b.ann with
    | some σ =>
        let (σ', bodyAnn) := erasePolyTy σ nats
        let fullAnn := foldHeadParamAnns nats σ.foralls b.params bodyAnn
        (some σ', some fullAnn, eraseSchemeAnn nats σ b.params)
    | none =>
        -- Head params with BL but no return ascription: cannot build a full
        -- arrow interface without a codomain; leave bounds ann empty.
        (none, none, none)
  let b' : Binding :=
    { b with
      params := eraseParams b.params
      ann := ann'
      natBinders := []
      rhs := eraseExpr b.rhs }
  { binding := b'
    ann :=
      if schemeOut.isSome then none
      else if hadBl then annOut else none
    schemeAnn := schemeOut }

def eraseDataDecl (d : DataDecl) : DataDecl :=
  { d with
    ctors := d.ctors.map fun (cn, fs) =>
      (cn, fs.map fun t => (eraseTy t).ty) }

def eraseProgram (p : Program) : ErasedProgram :=
  let decls' := p.decls.map eraseDataDecl
  let groups' : List (List ErasedBinding) :=
    p.groups.map fun g => g.map eraseBinding
  { decls := decls'
    groups := groups'
    body := eraseExpr p.body
    bodyAnn := none
    -- prove after shape ✅ (`eraseProgram_noBl`)
    noBl := by sorry }

/-! ## Theorems -/

theorem eraseTy_doesntContainBounds (t : Surface.Ty) :
    Surface.Ty.DoesntContainBounds (eraseTy t).ty :=
  (eraseTy t).noBl

theorem eraseTy_bl (lo hi : Surface.CountSlot) (elem : Surface.Ty) (e : ErasedTy)
    (he : e = eraseTy (.bl lo hi elem)) :
    e.ty = surfaceListTy (eraseTy elem).ty ∧
    e.ann = .list (eraseCount lo) (eraseCount hi) (eraseTy elem).ann := by
  subst he
  simp only [eraseTy]; simp only [Surface.Ty.rec_strong, surfaceListTy]; trivial

#guard decide
  (eraseCountSolid (.var (.mk "n")) [.mk "n"] = .var ⟨.rigid, 0⟩)
#guard decide
  (eraseCountSolid (.var (.mk "m")) [.mk "n", .mk "m"] = .var ⟨.rigid, 1⟩)

/-! ## Guards -/

def eraseTyEq (t expectedTy : Surface.Ty) (expectedAnn : BoundsAnnTy) : Bool :=
  let e := eraseTy t
  reprStr e.ty == reprStr expectedTy && reprStr e.ann == reprStr expectedAnn

#guard decide (eraseCount (.solid (.lit 3)) = .solid (.lit 3))
#guard decide (eraseCount .hole = .hole)
#guard decide (eraseCount (.solid .inf) = .solid .inf)
#guard decide (eraseCount (.solid (.add (.lit 1) (.lit 2))) = .solid (.add (.lit 1) (.lit 2)))
#guard decide (eraseCount (.solid (.min (.lit 3) (.lit 5))) = .solid (.min (.lit 3) (.lit 5)))

#guard eraseTyEq
  (.bl (.solid (.lit 0)) (.solid (.lit 5)) (.prim .int))
  (surfaceListTy (.prim .int))
  (.list (.solid (.lit 0)) (.solid (.lit 5)) (.prim .int))

#guard eraseTyEq
  (.bl .hole (.solid (.lit 5)) (.tvar (.mk "a")))
  (surfaceListTy (.tvar (.mk "a")))
  (.list .hole (.solid (.lit 5)) (.fvar 0))

/-- Two type foralls → distinct fvar indices (map/filter schemes). -/
def eraseTy_ab_guard : Bool :=
  let e := eraseTy (.arrow (.tvar (.mk "a")) (.tvar (.mk "b")))
    (nats := []) (tvars := [.mk "a", .mk "b"])
  reprStr e.ann == reprStr (BoundsAnnTy.arrow (.fvar 0) (.fvar 1))
#guard eraseTy_ab_guard

/-- R2: `(xs : BL 2 2 Int) : Int` folds to mono `BL 2 2 Int → Int`. -/
private def eraseHeadBinderGuard : Bool :=
  let ret : Surface.PolyTy := ⟨[], .prim .int⟩
  let eb := eraseBinding {
    name := ⟨"head2"⟩
    params := [(⟨"xs"⟩, some (.bl (.solid (.lit 2)) (.solid (.lit 2)) (.prim .int)))]
    ann := some ret
    rhs := .list []
    natBinders := []
  }
  match eb.ann, eb.schemeAnn with
  | some (.arrow (.list (.solid (.lit 2)) (.solid (.lit 2)) (.prim .int)) (.prim .int)), none =>
      true
  | _, _ => false
#guard eraseHeadBinderGuard

/-- `{a} a → BL 1 1 a` → scheme sidecar (not mono fvar ann). -/
private def eraseSingletonSchemeGuard : Bool :=
  let σ : Surface.PolyTy :=
    ⟨[⟨"a"⟩],
      .arrow (.tvar (.mk "a"))
        (.bl (.solid (.lit 1)) (.solid (.lit 1)) (.tvar (.mk "a")))⟩
  let eb := eraseBinding
    { name := ⟨"singleton"⟩, ann := some σ, rhs := .list [], natBinders := [] }
  match eb.schemeAnn, eb.ann, eb.binderAnn with
  | some s, none, some (.scheme s') =>
      s.natBinders.isEmpty &&
      s.tyBinders == [⟨"a"⟩] &&
      reprStr s == reprStr s' &&
      BinderAnn.pretty (.scheme s) == "∀ a. a → BL 1 1 a"
  | _, _, _ => false
#guard eraseSingletonSchemeGuard

#guard eraseTyEq (.prim .int) (.prim .int) (.prim .int)

#guard eraseTyEq
  (.arrow (.bl (.solid (.lit 0)) (.solid (.lit 1)) (.prim .int)) (.prim .bool))
  (.arrow (surfaceListTy (.prim .int)) (.prim .bool))
  (.arrow
    (.list (.solid (.lit 0)) (.solid (.lit 1)) (.prim .int))
    (.custom boolTyName []))

#guard eraseTyEq
  (.pair (.bl (.solid (.lit 0)) (.solid (.lit 2)) (.prim .int)) (.prim .bool))
  (.pair (surfaceListTy (.prim .int)) (.prim .bool))
  (.custom pairTyName [
    .list (.solid (.lit 0)) (.solid (.lit 2)) (.prim .int),
    .custom boolTyName []])

end FHM.Bounds.Erase
