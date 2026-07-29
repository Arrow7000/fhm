import FHM.Core
import FHM.Bounds.Kernel

/-!
# Bounds annotations (Z3-free)

Shared surface/Core annotation AST used by erase and by Typing elaboration.
Kept out of `Typing.lean` so `Erase` / Live / diagnose do not pull Oracle→Z3.
-/

namespace FHM.Bounds

/-! ## Prelude names (align with SurfaceBridge) -/

def listTyName : TyName := ⟨"List"⟩
def boolTyName : TyName := ⟨"Bool"⟩
def pairTyName : TyName := ⟨"Pair"⟩

/-! ## Annotation AST -/

/-- A single count slot from surface: concrete or hole (to be solved / defaulted). -/
inductive AnnoCount where
  | hole
  | solid (c : Count)
  deriving DecidableEq, Repr

/-- Bound ascription with holes, same spine as `BoundsTy`.
List is the only place `AnnoCount` appears; everything else mirrors `BoundsTy`.
Renamed from `BoundAnn` so the name reads as an annotated `Ty`. -/
inductive BoundsAnnTy where
  | prim (p : PrimTy)
  | arrow (dom cod : BoundsAnnTy)
  | bvar (i : Nat)
  | fvar (i : Nat)
  | list (lo hi : AnnoCount) (elem : BoundsAnnTy)
  | custom (name : TyName) (args : List BoundsAnnTy)
  deriving Repr

/-! ## De Bruijn ascriptions (post-lower) -/

/-- Program-level bound ascriptions after lower (de Bruijn parallel to value env).

`binderAnns[i] = some ann` means binding `i` was surface-ascribed; the body of
the program may carry `bodyAnn`. Missing entries = no ascription (pure synth). -/
structure ProgramBoundsAnns where
  /-- Parallel to Core `env` after lower: index 0 = innermost binder. -/
  binderAnns : List (Option BoundsAnnTy) := []
  /-- Optional expected bounds on the whole expression / program body. -/
  bodyAnn : Option BoundsAnnTy := none
  deriving Repr

/-- Lookup ascription for de Bruijn index `i`. -/
def ProgramBoundsAnns.get? (a : ProgramBoundsAnns) (i : Nat) : Option BoundsAnnTy :=
  a.binderAnns[i]? |>.join

/-- Empty ascriptions (HM-only or no surface bounds). -/
def ProgramBoundsAnns.empty : ProgramBoundsAnns := {}

/-! ## Pretty (Live / diagnose; no Typing import) -/

def Count.pretty : Count → String
  | .lit n => toString n
  | .inf => "∞"
  | .add a b =>
      let sa := Count.pretty a
      let sb := Count.pretty b
      s!"({sa} + {sb})"
  | .mul a b =>
      let sa := Count.pretty a
      let sb := Count.pretty b
      s!"({sa} * {sb})"
  | .pred a => s!"(pred {Count.pretty a})"
  | .min a b =>
      let sa := Count.pretty a
      let sb := Count.pretty b
      s!"(min {sa} {sb})"
  | .max a b =>
      let sa := Count.pretty a
      let sb := Count.pretty b
      s!"(max {sa} {sb})"
  | .var v => reprStr (Count.var v)

def AnnoCount.pretty : AnnoCount → String
  | .hole => "_"
  | .solid c => Count.pretty c

def BoundsAnnTy.pretty : BoundsAnnTy → String
  | .prim p =>
      match p with
      | .unit => "Unit"
      | .int => "Int"
      | .nat => "Nat"
      | .char => "Char"
  | .arrow d c =>
      let sd := BoundsAnnTy.pretty d
      let sc := BoundsAnnTy.pretty c
      s!"{sd} → {sc}"
  | .bvar i => s!"β{i}"
  | .fvar i => s!"?β{i}"
  | .list lo hi e =>
      let slo := AnnoCount.pretty lo
      let shi := AnnoCount.pretty hi
      let se := BoundsAnnTy.pretty e
      s!"BL {slo} {shi} {se}"
  | .custom n args =>
      let nm := match n with | .mk s => s
      if args.isEmpty then nm
      else nm ++ " " ++ String.intercalate " " (args.map BoundsAnnTy.pretty)

/-- Human lines for present binder ascriptions (`name : ann`). -/
def ProgramBoundsAnns.prettyLines
    (anns : ProgramBoundsAnns) (binderEnv : List ValName) : List String :=
  binderEnv.zip anns.binderAnns |>.filterMap fun ⟨n, a?⟩ =>
    a?.map fun a =>
      let nm := match n with | .mk s => s
      s!"{nm} : {a.pretty}"

end FHM.Bounds
