import FHM.CorePath
import Mathlib.Data.Nat.Pairing

/-! # Static count identities and lexical scope

Count identities are artifact-local and source-derived, not inference variables
or local de Bruijn positions. Keeping the telescope outside HM schemes avoids
changing the proved HM rules. Paths locate binders; identities survive rebasing
and compiler cloning.
-/

namespace FHM.Bounds.Scope

structure BinderId where
  source : Nat
  member : Nat
  parameter : Nat
  deriving Repr, DecidableEq, BEq

def BinderId.index (id : BinderId) : Nat :=
  Nat.pair id.source (Nat.pair id.member id.parameter)

theorem BinderId.index_injective : Function.Injective BinderId.index := by
  intro a b h
  cases a; cases b
  simp only [BinderId.index, Nat.pair_eq_pair] at h
  rcases h with ⟨rfl, rfl, rfl⟩
  rfl

abbrev Lexical := List (ValName × Nat)

def telescope (source member : Nat) (names : List ValName) : Lexical :=
  names.mapIdx fun parameter name => (name, (BinderId.mk source member parameter).index)

structure Telescope where
  site : CoreBinderSite
  binders : Lexical
  deriving Repr

structure Problem where
  site : CoreBinderSite
  unresolved : List ValName := []
  duplicateBinders : List ValName := []
  deriving Repr

structure Metadata where
  telescopes : List Telescope := []
  problems : List Problem := []
  deriving Repr

def Metadata.below (pre : CorePath) (m : Metadata) : Metadata :=
  { telescopes := m.telescopes.map fun t =>
      { t with site := pre.foldr CoreBinderSite.below t.site }
    problems := m.problems.map fun p =>
      { p with site := pre.foldr CoreBinderSite.below p.site } }

def Metadata.combine (parts : List Metadata) : Metadata :=
  ⟨parts.flatMap (·.telescopes), parts.flatMap (·.problems)⟩

/-- Lexical membership is separate from scheme-local `BinderRigid`: source
    scopes may contain noncontiguous stable identities and captured binders. -/
def CountScoped (ids : List Nat) : Count → Prop
  | .lit _ | .inf => True
  | .var ⟨.rigid, i⟩ => i ∈ ids
  | .var ⟨.inferable, _⟩ => False
  | .add a b | .mul a b | .min a b | .max a b => CountScoped ids a ∧ CountScoped ids b
  | .pred a => CountScoped ids a

def renameCount (f : Var → Var) : Count → Count
  | .lit n => .lit n
  | .inf => .inf
  | .var v => .var (f v)
  | .add a b => .add (renameCount f a) (renameCount f b)
  | .mul a b => .mul (renameCount f a) (renameCount f b)
  | .pred a => .pred (renameCount f a)
  | .min a b => .min (renameCount f a) (renameCount f b)
  | .max a b => .max (renameCount f a) (renameCount f b)

theorem renameCount_eval (f : Var → Var) (c : Count) (σ : Assign) :
    (renameCount f c).eval σ = c.eval (σ ∘ f) := by
  induction c <;> simp only [renameCount, Count.eval, Function.comp_apply, *]

theorem CountScoped.rename {ids ids' : List Nat} {c : Count}
    (h : CountScoped ids c) (f : Nat → Nat)
    (hmap : ∀ i ∈ ids, f i ∈ ids') :
    CountScoped ids' (renameCount (fun v => { v with idx := f v.idx }) c) := by
  induction c with
  | lit | inf => trivial
  | var v =>
      cases v with | mk kind i =>
        cases kind with
        | rigid => exact hmap i h
        | inferable => cases h
  | add a b ha hb | mul a b ha hb | min a b ha hb | max a b ha hb =>
      exact ⟨ha h.1, hb h.2⟩
  | pred a ha => exact ha h

def renameSlot (f : Var → Var) : CountSlot → CountSlot
  | .hole => .hole
  | .solid c => .solid (renameCount f c)

mutual
def renameTy (f : Var → Var) : Ty → Ty
  | .prim p => .prim p
  | .fvar i => .fvar i
  | .bvar i => .bvar i
  | .arrow a b => .arrow (renameTy f a) (renameTy f b)
  | .customTy name args => .customTy name (renameTys f args)
  | .bl lo hi elem => .bl (renameSlot f lo) (renameSlot f hi) (renameTy f elem)

def renameTys (f : Var → Var) : List Ty → List Ty
  | [] => []
  | a :: as => renameTy f a :: renameTys f as
end

mutual
/-- Resolving count identities cannot affect HM's bounds-erased type. -/
theorem renameTy_erase (f : Var → Var) (τ : Ty) :
    (renameTy f τ).eraseBounds = τ.eraseBounds := by
  cases τ with
  | prim | fvar | bvar => rfl
  | arrow a b => simp only [renameTy, Ty.eraseBounds, renameTy_erase f a, renameTy_erase f b]
  | customTy n as => simp only [renameTy, Ty.eraseBounds, renameTys_erase f as]
  | bl lo hi e => simp only [renameTy, Ty.eraseBounds, renameTy_erase f e]
termination_by sizeOf τ

theorem renameTys_erase (f : Var → Var) (as : List Ty) :
    TyList.eraseBounds (renameTys f as) = TyList.eraseBounds as := by
  cases as with
  | nil => rfl
  | cons a as => simp only [renameTys, TyList.eraseBounds, renameTy_erase f a, renameTys_erase f as]
termination_by sizeOf as
end

#print axioms BinderId.index_injective
#print axioms renameTy_erase

end FHM.Bounds.Scope
