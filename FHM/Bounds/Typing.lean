import FHM.Core
import FHM.Bounds.Kernel
import FHM.Bounds.Oracle
import FHM.Bounds.Commit

/-!
# Bounds typing on Core — BoundInfo + parasitic HasBounds (P2 API)

**Status:** shapes for sign-off (BoundInfo mirrors Core `Ty` exactly).

## Design

`HasBounds Δ bctx e τ β` assigns bound info `β` to Core `e` at HM type `τ`.
Does **not** re-derive HM; compose with `TypeOfElabHM` at theorem boundaries.

### BoundInfo ≅ Core Ty + intervals on List

| Core `Ty` | `BoundInfo` |
|-----------|--------------|
| `prim p` | `prim p` |
| `arrow a b` | `arrow βa βb` |
| `bvar i` / `fvar i` | `bvar i` / `fvar i` |
| `customTy "List" [α]` | `list lo hi βα` (**only** place intervals live) |
| `customTy n args` (`n ≠ List`) | `custom n βargs` |

Example:
```
τ = Pair (List t) (List r)
β = custom ⟨"Pair"⟩ [list a b βt, list c d βr]
```

`Agrees β τ` is the shape invariant. List is never `custom "List" […]`.

Uniqueness ∉ declarative typing. Match join: min/max on every `list`.
-/

namespace FHM.Bounds

/-! ## Prelude names (align with SurfaceBridge) -/

def listTyName : TyName := ⟨"List"⟩
def nilCtorName : CtorName := ⟨"Nil"⟩
def consCtorName : CtorName := ⟨"Cons"⟩

def listTy (α : Ty) : Ty := .customTy listTyName [α]

def isListTy : Ty → Option Ty
  | .customTy n [α] => if n = listTyName then some α else none
  | _ => none

/-! ## BoundInfo -/

/-- Bound-layer view of a Core monotype — same spine as `Ty`, intervals only on List. -/
inductive BoundInfo where
  | prim (p : PrimTy)
  | arrow (dom cod : BoundInfo)
  | bvar (i : Nat)
  | fvar (i : Nat)
  | list (lo hi : Count) (elem : BoundInfo)
  | custom (name : TyName) (args : List BoundInfo)
  deriving Repr

/-- `β` matches HM type `τ` (constructors / arities; List uses `list`, not `custom`). -/
inductive Agrees : BoundInfo → Ty → Prop where
  | prim {p} :
      Agrees (.prim p) (.prim p)
  | arrow {βd βc τd τc} :
      Agrees βd τd →
      Agrees βc τc →
      Agrees (.arrow βd βc) (.arrow τd τc)
  | bvar {i} :
      Agrees (.bvar i) (.bvar i)
  | fvar {i} :
      Agrees (.fvar i) (.fvar i)
  | list {lo hi βe α} :
      Agrees βe α →
      Agrees (.list lo hi βe) (listTy α)
  | custom {name args tys} :
      name ≠ listTyName →
      List.Forall₂ Agrees args tys →
      Agrees (.custom name args) (.customTy name tys)

/-- Default bound view of a monotype.
Used when inventing β without annotations (e.g. `nil` elem). Not principal.

TODO(bounds-inf): lists currently default to interval `[0,0]`. Once `Count.inf`
exists (see Kernel `Count`), default should be `[0, inf]` (unbounded length). -/
def defaultBounds : Ty → BoundInfo
  | .prim p => .prim p
  | .arrow a b => .arrow (defaultBounds a) (defaultBounds b)
  | .bvar i => .bvar i
  | .fvar i => .fvar i
  | .customTy n [α] =>
      if n = listTyName then
        -- TODO(bounds-inf): hi should be `.inf`, not `.lit 0`
        .list (.lit 0) (.lit 0) (defaultBounds α)
      else .custom n [defaultBounds α]
  | .customTy n tys => .custom n (tys.map defaultBounds)

theorem defaultBounds_agrees (τ : Ty) : Agrees (defaultBounds τ) τ := by
  sorry

abbrev BoundEnv := List BoundInfo

def consBoundEnv (bctx : BoundEnv) (lo hi : Count) (βe : BoundInfo) : BoundEnv :=
  βe :: .list (.pred lo) (.pred hi) βe :: bctx

/-- Pointwise join; lists use min lo / max hi; fail on shape mismatch.
`partial` for API review; replace with well-founded mutual rec after sign-off. -/
partial def joinBoundInfo : BoundInfo → BoundInfo → Option BoundInfo
  | .prim p, .prim q => if p = q then some (.prim p) else none
  | .bvar i, .bvar j => if i = j then some (.bvar i) else none
  | .fvar i, .fvar j => if i = j then some (.fvar i) else none
  | .arrow a b, .arrow a' b' =>
      match joinBoundInfo a a', joinBoundInfo b b' with
      | some d, some c => some (.arrow d c)
      | _, _ => none
  | .list lo₁ hi₁ e₁, .list lo₂ hi₂ e₂ =>
      match joinBoundInfo e₁ e₂ with
      | some e => some (.list (.min lo₁ lo₂) (.max hi₁ hi₂) e)
      | none => none
  | .custom n₁ as₁, .custom n₂ as₂ =>
      if n₁ = n₂ && as₁.length = as₂.length then
        let rec go : List BoundInfo → List BoundInfo → Option (List BoundInfo)
          | [], [] => some []
          | x :: xs, y :: ys =>
              match joinBoundInfo x y, go xs ys with
              | some z, some zs => some (z :: zs)
              | _, _ => none
          | _, _ => none
        match go as₁ as₂ with
        | some args => some (.custom n₁ args)
        | none => none
      else none
  | _, _ => none

/-! ## Sub -/

/-- `Sub Δ β β'`: β usable where β' demanded. Structural; List via `checkValid` intervals. -/
inductive Sub (Δ : List Constraint) : BoundInfo → BoundInfo → Prop where
  | prim {p} :
      Sub Δ (.prim p) (.prim p)
  | bvar {i} :
      Sub Δ (.bvar i) (.bvar i)
  | fvar {i} :
      Sub Δ (.fvar i) (.fvar i)
  | arrow {a a' b b'} :
      Sub Δ a' a →
      Sub Δ b b' →
      Sub Δ (.arrow a b) (.arrow a' b')
  | list {lo hi lo' hi' e e'} :
      Count.DemandOK lo' →
      Count.DemandOK hi' →
      checkValid (Interval.subGoals Δ ⟨lo, hi⟩ ⟨lo', hi'⟩) = .valid →
      Sub Δ e e' →
      Sub Δ (.list lo hi e) (.list lo' hi' e')
  | list_refl {lo hi e} :
      Count.DemandOK lo →
      Count.DemandOK hi →
      Sub Δ e e →
      Sub Δ (.list lo hi e) (.list lo hi e)
  | custom {name as bs} :
      name ≠ listTyName →
      List.Forall₂ (Sub Δ) as bs →
      Sub Δ (.custom name as) (.custom name bs)

/-! ## HasBounds -/

def boundInfoOfPrimLit : PrimLitExpr → BoundInfo
  | .unit => .prim .unit
  | .int _ => .prim .int
  | .nat _ => .prim .nat
  | .char _ => .prim .char

/-- Parasitic bound assignment. Every conclusion should satisfy `Agrees β τ`
(lemma `HasBounds.agrees` after sign-off). -/
inductive HasBounds :
    List Constraint → BoundEnv → Expr → Ty → BoundInfo → Prop where

  | primLit {Δ bctx p} :
      HasBounds Δ bctx (.primLit p) (PrimLitExpr.ty p) (boundInfoOfPrimLit p)

  /-- Prim ops: β must agree with the HM type Infer already assigned. -/
  | primBinOp {Δ bctx op τ β} :
      Agrees β τ →
      HasBounds Δ bctx (.primBinOp op) τ β

  /-- `Nil` @ `List α` with interval `[0,0]`; `βe` bounds the element type. -/
  | nil {Δ bctx α βe} :
      Agrees βe α →
      HasBounds Δ bctx (.ctor nilCtorName) (listTy α) (.list (.lit 0) (.lit 0) βe)

  /-- `Cons h t` @ `List α`. -/
  | cons {Δ bctx h t α lo hi βh βe} :
      HasBounds Δ bctx h α βh →
      HasBounds Δ bctx t (listTy α) (.list lo hi βe) →
      Sub Δ βh βe →
      HasBounds Δ bctx
        (.app (.app (.ctor consCtorName) h) t)
        (listTy α)
        (.list (.add lo (.lit 1)) (.add hi (.lit 1)) βe)

  | var {Δ bctx i tyArgs τ β} :
      bctx[i]? = some β →
      Agrees β τ →
      HasBounds Δ bctx (.var i tyArgs) τ β

  | app {Δ bctx f arg τa τr βa βr βa'} :
      HasBounds Δ bctx f (.arrow τa τr) (.arrow βa βr) →
      HasBounds Δ bctx arg τa βa' →
      Sub Δ βa' βa →
      HasBounds Δ bctx (.app f arg) τr βr

  | lambda {Δ bctx ann body τp τb βp βb} :
      Agrees βp τp →
      HasBounds Δ (βp :: bctx) body τb βb →
      HasBounds Δ bctx (.lambda ann body) (.arrow τp τb) (.arrow βp βb)

  | letMono {Δ bctx ann e1 e2 τ1 τ2 β1 β2} :
      HasBounds Δ bctx e1 τ1 β1 →
      HasBounds Δ (β1 :: bctx) e2 τ2 β2 →
      HasBounds Δ bctx (.letIn ann e1 e2) τ2 β2

  /-- Exhaustive List match; join branch β (min/max on lists). -/
  | matchList {Δ bctx scrut eNil eCons α lo hi βe τ βnil βcons β} :
      HasBounds Δ bctx scrut (listTy α) (.list lo hi βe) →
      HasBounds (Δ ++ nilRefine lo hi) bctx eNil τ βnil →
      HasBounds (Δ ++ consRefine hi) (consBoundEnv bctx lo hi βe) eCons τ βcons →
      joinBoundInfo βnil βcons = some β →
      HasBounds Δ bctx
        (.match_ scrut [
          (.named nilCtorName 0, eNil),
          (.named consCtorName 2, eCons)])
        τ β

  | matchNil {Δ bctx scrut eNil α lo hi βe τ β} :
      HasBounds Δ bctx scrut (listTy α) (.list lo hi βe) →
      checkValid (mustBeEmpty Δ hi) = .valid →
      HasBounds (Δ ++ nilRefine lo hi) bctx eNil τ β →
      HasBounds Δ bctx
        (.match_ scrut [(.named nilCtorName 0, eNil)])
        τ β

  | matchCons {Δ bctx scrut eCons α lo hi βe τ β} :
      HasBounds Δ bctx scrut (listTy α) (.list lo hi βe) →
      checkValid (mustBeNonempty Δ lo) = .valid →
      HasBounds (Δ ++ consRefine hi) (consBoundEnv bctx lo hi βe) eCons τ β →
      HasBounds Δ bctx
        (.match_ scrut [(.named consCtorName 2, eCons)])
        τ β

  /-- Other nullary/custom ctors (Pair.Mk not fully applied, Bool, …): β agrees with τ.
  Fully applied Pair introduction can be a later rule building `custom "Pair" […]`. -/
  | ctor {Δ bctx name τ β} :
      name ≠ nilCtorName →
      Agrees β τ →
      HasBounds Δ bctx (.ctor name) τ β

/-! ## CheckBounds -/

inductive CheckBounds :
    List Constraint → BoundEnv → Expr → Ty → BoundInfo → Prop where
  | ofSub {Δ bctx e τ β β'} :
      HasBounds Δ bctx e τ β' →
      Sub Δ β' β →
      CheckBounds Δ bctx e τ β

/-! ## Theorem statements (prove after sign-off) -/

theorem joinBoundInfo_comm (β₁ β₂ : BoundInfo) :
    joinBoundInfo β₁ β₂ = joinBoundInfo β₂ β₁ := by
  sorry

theorem Sub.refl (Δ : List Constraint) (β : BoundInfo) : Sub Δ β β := by
  sorry

theorem HasBounds.agrees {Δ bctx e τ β}
    (h : HasBounds Δ bctx e τ β) : Agrees β τ := by
  sorry

theorem HasBounds.weaken_Δ {Δ Δ' bctx e τ β}
    (h : HasBounds Δ bctx e τ β)
    (hpre : ∀ c ∈ Δ, c ∈ Δ') :
    HasBounds Δ' bctx e τ β := by
  sorry

def WellBound (ctors : CtorEnv) (e : Expr) (τ : Ty) (β : BoundInfo) : Prop :=
  TypeOfElabHM ⟨[], ctors⟩ e τ ∧ HasBounds [] [] e τ β

end FHM.Bounds
