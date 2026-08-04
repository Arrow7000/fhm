import FHM.Core
import FHM.Bounds.Kernel

/-!
# Phase 1 draft — Core types that carry BL

**Status:** Design under review (2026-08-04). Not wired into Core/Infer/Live yet.

**Home (temporary):** lives under `FHM.Bounds` so we can `import` kernel `Count`
without putting Z3 on the default FHM target. After approval, intended homes:

| Symbol | Eventual home |
|--------|----------------|
| `Count` (already exists) | thin `FHM.Bounds.Count` (split from Kernel) or stay in Kernel |
| `CountSlot` | next to `Count` (replace/`abbrev` today’s `AnnoCount`) |
| `Ty` / `PolyTy` below | merge into `FHM.Core` (replace current five-ctor `Ty`) |

**Settled (from design thread — not open questions):**

* Intervals live **in** the type: `Ty.list`, not a sidecar payload on `customTy "List"`.
* Bare `List t` stays `customTy "List" [t]` (no length demand).
* User `BL …` (including `_` holes) is `Ty.list` with `CountSlot`s.
* Solid counts are kernel `Count` (rigid/inferable indices), not surface names.
* Core `PolyTy` stays **type-foralls only** in Phase 1; Nat telescopes remain on
  surface binders / bounds schemes until a later phase.
* Infer will be bounds-blind later; this file only freezes the **syntax** of types.

Build: `lake build FHM.Bounds.Phase1CoreTy` (on the FHMBounds root list).
-/

namespace FHM.Phase1

open FHM.Bounds (Count)

/-! ## Count slots (lo / hi of a BL)

Same shape as `FHM.Bounds.AnnoCount` and `Surface.CountSlot`.
Duplicated here so the draft does not depend on `Ann.lean` (which already imports
full Core). After approval: one definition next to `Count`, everyone aliases it.
-/

/-- One endpoint of a bounded list: `_` or a solid count expression. -/
inductive CountSlot where
  | hole
  | solid (c : Count)
  deriving DecidableEq, Repr

instance : Coe Count CountSlot where
  coe := .solid

/-! ## Proposed Core monotype

Mirrors current `Core.Ty` plus **`list`** for surface `BL lo hi elem`.

Runtime / List ADT values still use `customTy ⟨"List"⟩ […]` (Nil/Cons).
`list` is the *refined* type form that carries length intervals.
-/

/-- Name of the List ADT (Nil/Cons). Same string as today’s prelude. -/
def listTyName : TyName := ⟨"List"⟩

inductive Ty where
  | prim : PrimTy → Ty
  | arrow : (dom cod : Ty) → Ty
  /-- Bound var — only under a polytype’s type telescope. -/
  | bvar : Nat → Ty
  /-- Free / unification variable (HM). -/
  | fvar : Nat → Ty
  /-- Nominal type application (`List`, `Pair`, user ADTs, …). -/
  | customTy : TyName → List Ty → Ty
  /-- Bounded list `BL lo hi elem`. Intervals are part of the type.
  Not the List ADT itself — see `bareListTy`. -/
  | list : (lo hi : CountSlot) → (elem : Ty) → Ty
  deriving Repr

/-! ### List helpers -/

/-- Bare HM list type: user wrote `List t`, or Infer filled a list shape with no
length demand. **Not** `list hole hole t` — that would fake a BL ascription. -/
def bareListTy (α : Ty) : Ty :=
  .customTy listTyName [α]

/-- Bounded list (sugar for the ctor). -/
def blTy (lo hi : CountSlot) (α : Ty) : Ty :=
  .list lo hi α

def isBareListTy : Ty → Option Ty
  | .customTy n [α] => if n == listTyName then some α else none
  | _ => none

def isBlTy : Ty → Option (CountSlot × CountSlot × Ty)
  | .list lo hi α => some (lo, hi, α)
  | _ => none

/-- Drop intervals for an HM view: every `list _ _ α` becomes bare `List α`.
Function only — does **not** mutate programs. Used later by bounds-blind unify. -/
def eraseBounds : Ty → Ty
  | .prim p => .prim p
  | .arrow a b => .arrow (eraseBounds a) (eraseBounds b)
  | .bvar i => .bvar i
  | .fvar i => .fvar i
  | .customTy n as => .customTy n (as.map eraseBounds)
  | .list _ _ α => bareListTy (eraseBounds α)

/-! ## PolyTy (Phase 1: unchanged idea)

Type foralls only. Nat/length binders stay off this structure until we extend
schemes deliberately; surface already keeps `natBinders` on bindings.
-/

structure PolyTy where
  paramCount : Nat
  /-- Body may use `.bvar i` for `i < paramCount` (type params only). -/
  body : Ty
  deriving Repr

def PolyTy.mkTrivial (body : Ty) : PolyTy :=
  { paramCount := 0, body }

/-! ## Lowering sketch (not wired)

Surface → this `Ty` (for review of the mapping only).

```
Surface.bl lo hi e  ↦  Ty.list (slot lo) (slot hi) (lower e)
Surface.List e      ↦  bareListTy (lower e)
Surface hole        ↦  CountSlot.hole
Surface solid c     ↦  CountSlot.solid (resolve names → Count.var rigid i | lit | …)
```

Named surface count vars need the enclosing Nat telescope at the binder;
that resolution already exists on the erase path and will move to lower.
-/

/-! ## Relationship to existing types

| Existing | Relation to this draft |
|----------|----------------------|
| `Core.Ty` | Same spine **minus** `list`; Phase 1 merge adds `list` |
| `BoundsTy` | Parallel bounds spine; long-term can collapse toward `Ty` |
| `BoundsAnnTy` / `AnnoCount` | Ascription form with holes; `CountSlot` ≡ `AnnoCount` |
| `Surface.Ty.bl` | Source syntax for `Ty.list` |

No genuine open product choices left for these ctors; remaining work is
migration mechanics (file split, walker fallout, lower wiring).
-/

end FHM.Phase1
