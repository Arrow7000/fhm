import FHM.Core
import FHM.Bounds.Kernel

/-!
# Phase 1 draft — merged into Core

**Status:** Approved and merged (2026-08-04).

Authoritative definitions now live in:

| Symbol | Home |
|--------|------|
| `CountSlot` | `FHM.Bounds.Kernel` |
| `Ty.bl`, `listTyName`, `bareListTy`, `Ty.eraseBounds` | `FHM.Core` |
| `PolyTy` Nat telescope | **TODO** on `Core.PolyTy` (type-only for now) |

This module only re-exports for open buffers that still import `Phase1CoreTy`.
Prefer `import FHM.Core` for new code.
-/

namespace FHM.Phase1

export FHM.Bounds (Count CountSlot)
export _root_ (listTyName bareListTy)

abbrev Ty := _root_.Ty
abbrev PolyTy := _root_.PolyTy

def eraseBounds := Ty.eraseBounds
def isBareListTy : Ty → Option Ty
  | .customTy n [α] => if n == listTyName then some α else none
  | _ => none
def isBlTy : Ty → Option (CountSlot × CountSlot × Ty)
  | .bl lo hi α => some (lo, hi, α)
  | _ => none

end FHM.Phase1
