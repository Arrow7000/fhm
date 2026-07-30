import FHM.Core
import FHM.Bounds.Kernel
import FHM.Pretty

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

/-! ## Bound schemes — erase-side sidecar (slice 7 shapes)

Dual-stack packaging (same strategy as mono `BoundsAnnTy`):

* HM `PolyTy` / Core schemes stay **type-only** (`{a} body`) — do not extend them
* Surface `{n : Nat, a} body` → type foralls in `PolyTy` + Nat names in a
  **sidecar** (Binding-level telescope at parse; erase → `BoundsSchemeAnn`)
* Type polymorphism = InferW; length polymorphism = Bounds-only
* Packed `BScheme` + InstantiatesTo live in `Typing.lean` (need `BoundsTy`)
-/

/-- Erase-side scheme ascription: named Nat binders + type foralls + annotated body.
Names are ordered (0 = first / outermost); erase maps name → rigid `Count.var`
and type forall → `.fvar i`. Parallel to mono `BoundsAnnTy` on `ErasedBinding.ann`. -/
structure BoundsSchemeAnn where
  natBinders : List ValName
  tyBinders : List ValName := []
  body : BoundsAnnTy
  deriving Repr

/-- Binder ascription after erase: mono `BL` or a Nat-quantified scheme.
Intended upgrade path for `ErasedBinding` / `ProgramBoundsAnns` (mono today;
`scheme` when Nat and/or type foralls present). -/
inductive BinderAnn where
  | mono (a : BoundsAnnTy)
  | scheme (s : BoundsSchemeAnn)
  deriving Repr

/-! ## De Bruijn ascriptions (post-lower) -/

/-- Program-level bound ascriptions after lower (de Bruijn parallel to value env).

`binderAnns[i] = some ann` means binding `i` was surface-ascribed (mono `BL` or
`{n : Nat,…}` scheme); the body of the program may carry `bodyAnn`.
Missing entries = no ascription (pure synth / D24). -/
structure ProgramBoundsAnns where
  /-- Parallel to Core `env` after lower: index 0 = innermost binder. -/
  binderAnns : List (Option BinderAnn) := []
  /-- Optional expected bounds on the whole expression / program body. -/
  bodyAnn : Option BoundsAnnTy := none
  deriving Repr

/-- Lookup mono ascription for de Bruijn index `i` (schemes → `none` here). -/
def ProgramBoundsAnns.getMono? (a : ProgramBoundsAnns) (i : Nat) : Option BoundsAnnTy :=
  match a.binderAnns[i]? |>.join with
  | some (.mono ann) => some ann
  | _ => none

/-- Lookup any binder ascription. -/
def ProgramBoundsAnns.get? (a : ProgramBoundsAnns) (i : Nat) : Option BinderAnn :=
  a.binderAnns[i]? |>.join

/-- Empty ascriptions (HM-only or no surface bounds). -/
def ProgramBoundsAnns.empty : ProgramBoundsAnns := {}

/-! ## Pretty (Live / diagnose; no Typing import) -/

/-- Default letters when no Nat-binder name is in scope. -/
private def prettyRigidIdx (i : Nat) : String :=
  let letters := ["n", "m", "k", "p", "q", "r", "s", "t"]
  letters.getD i ("n" ++ toString i)

private def prettyInferableIdx (i : Nat) : String :=
  "?" ++ prettyRigidIdx i

private def prettyTyVarIdx (i : Nat) : String :=
  -- Same letters as `prettyTyVarName` in `FHM/Pretty.lean` (a, b, c, …).
  prettyTyVarName i

/-- Pretty a count; `nats[i]` names rigid binder `i` when present (scheme bodies).
Constant-folds ground arithmetic first (display-layer only). -/
def Count.prettyWith (nats : List ValName) (c : Count) : String :=
  let rec go : Count → String
    | .lit n => toString n
    | .inf => "∞"
    | .add a b =>
        let sa := go a
        let sb := go b
        s!"({sa} + {sb})"
    | .mul a b =>
        let sa := go a
        let sb := go b
        s!"({sa} * {sb})"
    | .pred a => s!"(pred {go a})"
    | .min a b =>
        let sa := go a
        let sb := go b
        s!"(min {sa} {sb})"
    | .max a b =>
        let sa := go a
        let sb := go b
        s!"(max {sa} {sb})"
    | .var ⟨.rigid, i⟩ =>
        match nats[i]? with
        | some ⟨name⟩ => name
        | none => prettyRigidIdx i
    | .var ⟨.inferable, i⟩ => prettyInferableIdx i
  go (Count.simplify c)

def Count.pretty (c : Count) : String := Count.prettyWith [] c

def AnnoCount.prettyWith (nats : List ValName) : AnnoCount → String
  | .hole => "_"
  | .solid c => Count.prettyWith nats c

def AnnoCount.pretty (a : AnnoCount) : String := AnnoCount.prettyWith [] a

mutual
/-- `prec`: `0` = top, `1` = left of `→`, `2` = BL/custom argument position. -/
def BoundsAnnTy.prettyAux (nats : List ValName) (tvars : List ValName) (prec : Nat) :
    BoundsAnnTy → String
  | .prim p =>
      match p with
      | .unit => "Unit"
      | .int => "Int"
      | .nat => "Nat"
      | .char => "Char"
  | .arrow d c =>
      prettyParenIf (prec ≥ 1)
        (BoundsAnnTy.prettyAux nats tvars 1 d ++ " → " ++ BoundsAnnTy.prettyAux nats tvars 0 c)
  | .bvar i =>
      match tvars[i]? with
      | some ⟨name⟩ => name
      | none => prettyTyVarIdx i
  | .fvar i =>
      match tvars[i]? with
      | some ⟨name⟩ => name
      | none => prettyTyVarIdx i
  | .list lo hi e =>
      prettyParenIf (prec ≥ 2)
        ("BL " ++ AnnoCount.prettyWith nats lo ++ " " ++ AnnoCount.prettyWith nats hi ++ " " ++
          BoundsAnnTy.prettyAux nats tvars 2 e)
  | .custom (.mk "Pair") [a, b] =>
      "(" ++ BoundsAnnTy.prettyAux nats tvars 0 a ++ ", " ++ BoundsAnnTy.prettyAux nats tvars 0 b ++ ")"
  | .custom n args =>
      let nm := match n with | .mk s => s
      if args.isEmpty then nm
      else
        prettyParenIf (prec ≥ 2)
          (nm ++ " " ++ String.intercalate " " (BoundsAnnTy.prettyArgs nats tvars args))

def BoundsAnnTy.prettyArgs (nats : List ValName) (tvars : List ValName) :
    List BoundsAnnTy → List String
  | [] => []
  | t :: ts => BoundsAnnTy.prettyAux nats tvars 2 t :: BoundsAnnTy.prettyArgs nats tvars ts

end

def BoundsAnnTy.prettyWith (nats : List ValName) (tvars : List ValName := [])
    (a : BoundsAnnTy) : String :=
  BoundsAnnTy.prettyAux nats tvars 0 a

def BoundsAnnTy.pretty (a : BoundsAnnTy) : String := BoundsAnnTy.prettyWith [] [] a

/-- `∀ (lo hi : Nat) a b. body` — Nat binders combined Lean-style; type foralls bare. -/
def BoundsSchemeAnn.pretty (s : BoundsSchemeAnn) : String :=
  let natPart : Option String :=
    if s.natBinders.isEmpty then none
    else
      some ("(" ++ String.intercalate " " (s.natBinders.map prettyValName) ++ " : Nat)")
  let tyParts := s.tyBinders.map prettyValName
  let binders := natPart.toList ++ tyParts
  let quant :=
    if binders.isEmpty then ""
    else "∀ " ++ String.intercalate " " binders ++ ". "
  quant ++ BoundsAnnTy.prettyWith s.natBinders s.tyBinders s.body

def BinderAnn.pretty : BinderAnn → String
  | .mono a => a.pretty
  | .scheme s => s.pretty

/-- Count slot is a surface hole `_`. -/
def AnnoCount.isHole : AnnoCount → Bool
  | .hole => true
  | .solid _ => false

/-- Ascription still contains unfilled `_` (display should prefer synth when present). -/
partial def BoundsAnnTy.hasHoles : BoundsAnnTy → Bool
  | .prim _ | .bvar _ | .fvar _ => false
  | .arrow d c => d.hasHoles || c.hasHoles
  | .list lo hi e => lo.isHole || hi.isHole || e.hasHoles
  | .custom _ as => as.any BoundsAnnTy.hasHoles

def BinderAnn.hasHoles : BinderAnn → Bool
  | .mono a => a.hasHoles
  | .scheme s => s.body.hasHoles

/-- Human lines for present binder ascriptions (`name : ann`). -/
def ProgramBoundsAnns.prettyLines
    (anns : ProgramBoundsAnns) (binderEnv : List ValName) : List String :=
  binderEnv.zip anns.binderAnns |>.filterMap fun ⟨n, a?⟩ =>
    a?.map fun a =>
      let nm := match n with | .mk s => s
      s!"{nm} : {BinderAnn.pretty a}"

#guard
  BoundsSchemeAnn.pretty {
    natBinders := []
    tyBinders := [⟨"a"⟩]
    body := .arrow
      (.fvar 0)
      (.list (.solid (.lit 1)) (.solid (.lit 1)) (.fvar 0))
  } == "∀ a. a → BL 1 1 a"

#guard Count.pretty (.var ⟨.rigid, 0⟩) == "n"
#guard Count.pretty (.var ⟨.inferable, 1⟩) == "?m"
#guard
  BoundsSchemeAnn.pretty {
    natBinders := [⟨"n"⟩]
    tyBinders := [⟨"a"⟩]
    body := .arrow
      (.list (.solid (.var ⟨.rigid, 0⟩)) (.solid (.var ⟨.rigid, 0⟩)) (.fvar 0))
      (.list (.solid (.var ⟨.rigid, 0⟩)) (.solid (.var ⟨.rigid, 0⟩)) (.fvar 0))
  } == "∀ (n : Nat) a. BL n n a → BL n n a"
#guard
  BoundsSchemeAnn.pretty {
    natBinders := [⟨"lo"⟩, ⟨"hi"⟩]
    tyBinders := [⟨"a"⟩, ⟨"b"⟩]
    body := .arrow
      (.arrow (.fvar 0) (.fvar 1))
      (.arrow
        (.list (.solid (.var ⟨.rigid, 0⟩)) (.solid (.var ⟨.rigid, 1⟩)) (.fvar 0))
        (.list (.solid (.var ⟨.rigid, 0⟩)) (.solid (.var ⟨.rigid, 1⟩)) (.fvar 1)))
  } == "∀ (lo hi : Nat) a b. (a → b) → BL lo hi a → BL lo hi b"
#guard
  BoundsSchemeAnn.pretty {
    natBinders := [⟨"a"⟩, ⟨"b"⟩, ⟨"c"⟩, ⟨"d"⟩]
    tyBinders := [⟨"e"⟩]
    body := .arrow
      (.list (.solid (.var ⟨.rigid, 0⟩)) (.solid (.var ⟨.rigid, 1⟩)) (.fvar 0))
      (.arrow
        (.list (.solid (.var ⟨.rigid, 2⟩)) (.solid (.var ⟨.rigid, 3⟩)) (.fvar 0))
        (.list (.solid (.add (.var ⟨.rigid, 0⟩) (.var ⟨.rigid, 2⟩)))
          (.solid (.add (.var ⟨.rigid, 1⟩) (.var ⟨.rigid, 3⟩))) (.fvar 0)))
  } == "∀ (a b c d : Nat) e. BL a b e → BL c d e → BL (a + c) (b + d) e"

#guard BoundsAnnTy.pretty (.custom pairTyName [.fvar 0, .fvar 1]) == "(a, b)"
#guard
  BoundsAnnTy.pretty (.list (.solid (.lit 1)) (.solid (.lit 1)) (.arrow (.fvar 0) (.fvar 1))) ==
    "BL 1 1 (a → b)"
#guard
  BoundsSchemeAnn.pretty {
    natBinders := [⟨"n"⟩]
    tyBinders := [⟨"a"⟩, ⟨"b"⟩]
    body := .arrow
      (.list (.solid (.var ⟨.rigid, 0⟩)) (.solid (.var ⟨.rigid, 0⟩)) (.fvar 0))
      (.arrow
        (.list (.solid (.var ⟨.rigid, 0⟩)) (.solid (.var ⟨.rigid, 0⟩)) (.fvar 1))
        (.list (.solid (.var ⟨.rigid, 0⟩)) (.solid (.var ⟨.rigid, 0⟩))
          (.custom pairTyName [.fvar 0, .fvar 1])))
  } == "∀ (n : Nat) a b. BL n n a → BL n n b → BL n n (a, b)"

end FHM.Bounds
