import FHM.Bounds.Typing

/-!
# Bounds layer — Core demos (P3.5c)

Hand-built Core terms illustrating:

1. **`HasBounds`** — Nil / Cons spines get list intervals
2. **`BoundCovers`** — full Nil+Cons, wildcard (oracle-free)
3. **Nil-only / Cons-only** — under an explicit `checkValid = .valid` hypothesis
   (Z3 is not a pure Lean decision procedure)
4. **`MatchSafe`** — pipeline coverage contract

No Surface yet. Build: `lake build FHM.Bounds.Examples`
-/

namespace FHM.Bounds.Examples

open FHM.Bounds

/-! ## Term builders -/

def nilE : Expr := .ctor nilCtorName

def consE (h t : Expr) : Expr :=
  .app (.app (.ctor consCtorName) h) t

def unitE : Expr := .primLit .unit

/-- `[()]` as Core: `Cons unit Nil`. -/
def singletonUnit : Expr := consE unitE nilE

/-- `[(), ()]`. -/
def twoUnits : Expr := consE unitE singletonUnit

def tyUnit : Ty := .prim .unit
def tyListUnit : Ty := listTy tyUnit

def βUnit : BoundsTy := .prim .unit

/-- Interval produced by one `cons` step from `[n,n]`. -/
def βAfterCons (lo hi : Count) : BoundsTy :=
  .list (.add lo (.lit 1)) (.add hi (.lit 1)) βUnit

def βList00 : BoundsTy := .list (.lit 0) (.lit 0) βUnit
/-- After one cons from empty: lo/hi are `0+1` (as in the typing rule). -/
def βList11 : BoundsTy := βAfterCons (.lit 0) (.lit 0)
/-- After two cons: `(0+1)+1`. -/
def βList22 : BoundsTy := βAfterCons (.add (.lit 0) (.lit 1)) (.add (.lit 0) (.lit 1))

/-! ## 1. HasBounds on Nil / Cons -/

/-- Empty list: `Nil` @ `List Unit` with bounds `[0,0]`. -/
theorem hasBounds_nil_unit :
    HasBounds [] [] nilE tyListUnit βList00 :=
  .nil (Agrees.prim (p := .unit))

/-- `Cons unit Nil` — length becomes `0+1`. -/
theorem hasBounds_singleton_unit :
    HasBounds [] [] singletonUnit tyListUnit βList11 :=
  .cons (.primLit) hasBounds_nil_unit (Sub.refl [] βUnit)

/-- `Cons unit (Cons unit Nil)` — length `(0+1)+1`. -/
theorem hasBounds_two_units :
    HasBounds [] [] twoUnits tyListUnit βList22 :=
  .cons (.primLit) hasBounds_singleton_unit (Sub.refl [] βUnit)

theorem hasBounds_two_units_agrees :
    Agrees βList22 tyListUnit :=
  HasBounds.agrees hasBounds_two_units

/-! ## 2. BoundCovers — no oracle needed -/

def matchNilCons (eNil eCons : Expr) : List (MatchPattern × Expr) :=
  [(.named nilCtorName 0, eNil), (.named consCtorName 2, eCons)]

def matchWild (body : Expr) : List (MatchPattern × Expr) :=
  [(.wildcard, body)]

def matchNilOnly (eNil : Expr) : List (MatchPattern × Expr) :=
  [(.named nilCtorName 0, eNil)]

def matchConsOnly (eCons : Expr) : List (MatchPattern × Expr) :=
  [(.named consCtorName 2, eCons)]

theorem covers_full_any (lo hi : Count) (βe : BoundsTy) :
    BoundCovers [] (.list lo hi βe) (matchNilCons unitE unitE) := by
  refine BoundCovers.listFull_of_both ?N ?C
  · exact ⟨unitE, by simp [matchNilCons]⟩
  · exact ⟨unitE, by simp [matchNilCons]⟩

theorem covers_wild_any (lo hi : Count) (βe : BoundsTy) :
    BoundCovers [] (.list lo hi βe) (matchWild unitE) :=
  BoundCovers.listWild_of ⟨unitE, by simp [matchWild]⟩

theorem covers_full_for_two :
    BoundCovers [] βList22 (matchNilCons unitE unitE) :=
  covers_full_any _ _ _

/-! ## 3. Nil-only / Cons-only (oracle side condition)

Packaged under `checkValid … = .valid`. Trivial goals `0 ≤ 0` / `1 ≤ 1` succeed
at runtime when `z3` is on PATH (`#eval` section below). -/

theorem covers_nilOnly_of_valid {Δ lo hi βe : _} {eNil : Expr}
    (hv : checkValid (mustBeEmpty Δ hi) = .valid)
    (hN : hasNilBranch (matchNilOnly eNil)) :
    BoundCovers Δ (.list lo hi βe) (matchNilOnly eNil) :=
  .listNilOnly hv hN

theorem covers_consOnly_of_valid {Δ lo hi βe : _} {eCons : Expr}
    (hv : checkValid (mustBeNonempty Δ lo) = .valid)
    (hC : hasConsBranch (matchConsOnly eCons)) :
    BoundCovers Δ (.list lo hi βe) (matchConsOnly eCons) :=
  .listConsOnly hv hC

theorem covers_nilOnly_exact0
    (hv : checkValid (mustBeEmpty [] (.lit 0)) = .valid) :
    BoundCovers [] βList00 (matchNilOnly unitE) :=
  covers_nilOnly_of_valid hv ⟨unitE, by simp [matchNilOnly]⟩

/-- Cons-only when lo is the solid literal `1` (hypothesis matches that goal). -/
theorem covers_consOnly_lit1
    (hv : checkValid (mustBeNonempty [] (.lit 1)) = .valid) :
    BoundCovers [] (.list (.lit 1) (.lit 1) βUnit) (matchConsOnly unitE) :=
  covers_consOnly_of_valid hv ⟨unitE, by simp [matchConsOnly]⟩

/-! ## 4. MatchSafe pipeline contract -/

theorem matchSafe_full_list :
    MatchSafe [] (fun _ => False) βList22 (matchNilCons unitE unitE) :=
  MatchSafe.list_of_covers covers_full_for_two

theorem matchSafe_prim_unit :
    MatchSafe [] (fun _ => True) βUnit (matchNilCons unitE unitE) :=
  .nonList (β := βUnit) rfl trivial

/-! ## 5. Optional Z3 smoke (requires `z3` on PATH)

```
lake env lean FHM/Bounds/Examples.lean
```
then uncomment the `#eval`s.
-/

def emptyIsEmpty : ValidVerdict :=
  checkValid (mustBeEmpty [] (.lit 0))

def oneIsNonempty : ValidVerdict :=
  checkValid (mustBeNonempty [] (.lit 1))

-- #eval emptyIsEmpty
-- #eval oneIsNonempty

/-! ## 6. Scope notes

* No Surface `BL` syntax (P4)
* No full `WellBound` (needs List in `CtorEnv` + `TypeOfElabHM`)
* Cons lengths are `add n 1` in the derivation, not folded `lit (n+1)`
* Nil-only/cons-only stay honest about the Z3 TCB

Next: Surface erase (P4) or `Count.inf` (P3.5a).
-/

end FHM.Bounds.Examples
