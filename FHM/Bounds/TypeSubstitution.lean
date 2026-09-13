import FHM.Bounds.ScopedScheme

/-! # Bounds specialization at HM bound slots

Only `.bvar` slots are replaced. Free HM identities are captures, not indices in
the argument vector. Replacement bounds are supplied explicitly; no shape-only
template is asserted to describe a caller's value.

Combined instantiation substitutes a scheme's counts before inserting caller
type arguments. Counts inside those arguments belong to the caller and must
not be mistaken for count binders in the scheme being instantiated.
-/

namespace FHM.Bounds.TypeSubstitution

open ScopedScheme

mutual
def substitute (args : Nat → BoundsTy) : BoundsTy → BoundsTy
  | .prim p => .prim p
  | .fvar i => .fvar i
  | .bvar i => args i
  | .arrow a b => .arrow (substitute args a) (substitute args b)
  | .list lo hi elem => .list lo hi (substitute args elem)
  | .custom n as => .custom n (substituteList args as)

def substituteList (args : Nat → BoundsTy) : List BoundsTy → List BoundsTy
  | [] => []
  | a :: as => substitute args a :: substituteList args as
end

mutual
/-- Bounds specialization mirrors HM's actual bound-variable operation. -/
theorem shape (args : Nat → BoundsTy) (β : BoundsTy) :
    Synth.BoundsTy.toTy (substitute args β) =
      (Synth.BoundsTy.toTy β).instantiate (fun i => Synth.BoundsTy.toTy (args i)) := by
  cases β with
  | prim | fvar | bvar => simp only [substitute, Synth.BoundsTy.toTy, Ty.instantiate]
  | arrow a b => simp only [substitute, Synth.BoundsTy.toTy, Ty.instantiate, shape args a, shape args b]
  | list lo hi elem =>
      simp only [substitute, Synth.BoundsTy.toTy, listTy, Ty.instantiate, TyList.instantiate,
        shape args elem]
  | custom n as =>
      simp only [substitute, Synth.BoundsTy.toTy, Ty.instantiate, list_shape args as]
termination_by sizeOf β

private theorem list_shape (args : Nat → BoundsTy) (as : List BoundsTy) :
    (substituteList args as).map Synth.BoundsTy.toTy =
      TyList.instantiate (fun i => Synth.BoundsTy.toTy (args i)) (as.map Synth.BoundsTy.toTy) := by
  cases as with
  | nil => simp only [substituteList, List.map_nil, TyList.instantiate]
  | cons a as =>
      simp only [substituteList, List.map_cons, TyList.instantiate, shape args a, list_shape args as]
termination_by sizeOf as
end

mutual
theorem subtype (args : Nat → BoundsTy) {Δ a b} (h : SemanticSub Δ a b) :
    SemanticSub Δ (substitute args a) (substitute args b) := by
  cases h with
  | prim => exact .prim
  | fvar => exact .fvar
  | bvar => exact SemanticSub.refl Δ _
  | arrow ha hb => exact .arrow (subtype args ha) (subtype args hb)
  | list hv he => exact .list hv (subtype args he)
  | custom hs => exact .custom (list_subtype args hs)
termination_by sizeOf a + sizeOf b

private theorem list_subtype (args : Nat → BoundsTy) {Δ as bs}
    (h : List.Forall₂ (SemanticSub Δ) as bs) :
    List.Forall₂ (SemanticSub Δ) (substituteList args as) (substituteList args bs) := by
  cases h with
  | nil => exact .nil
  | cons hh ht => exact .cons (subtype args hh) (list_subtype args ht)
termination_by sizeOf as + sizeOf bs
end

mutual
theorem inScope {ids β} (args : Nat → BoundsTy) (h : BoundsScoped ids β)
    (ha : ∀ i, BoundsScoped ids (args i)) : BoundsScoped ids (substitute args β) := by
  cases β with
  | prim | fvar => trivial
  | bvar i => exact ha i
  | arrow a b => exact ⟨inScope args h.1 ha, inScope args h.2 ha⟩
  | list lo hi elem => exact ⟨h.1, h.2.1, inScope args h.2.2 ha⟩
  | custom n as => exact list_inScope args h ha
termination_by sizeOf β

private theorem list_inScope {ids as} (args : Nat → BoundsTy) (h : BoundsListScoped ids as)
    (ha : ∀ i, BoundsScoped ids (args i)) : BoundsListScoped ids (substituteList args as) := by
  cases as with
  | nil => trivial
  | cons a as => exact ⟨inScope args h.1 ha, list_inScope args h.2 ha⟩
termination_by sizeOf as
end

/-- Counts supplied inside caller type arguments are not part of the scheme's
    count telescope. The order here is intentional, including recursive uses
    whose caller count scope can contain the same source identities. -/
def combined (rows : CountSubstitution.Bindings) (args : Nat → BoundsTy) (β : BoundsTy) :
    BoundsTy := substitute args (CountSubstitution.bounds rows β)

theorem combined_shape (rows : CountSubstitution.Bindings) (args : Nat → BoundsTy) (β : BoundsTy) :
    Synth.BoundsTy.toTy (combined rows args β) =
      (Synth.BoundsTy.toTy β).instantiate (fun i => Synth.BoundsTy.toTy (args i)) := by
  rw [combined, shape, CountSubstitution.bounds_shape]

theorem combined_subtype (rows : CountSubstitution.Bindings) (hf : CountSubstitution.Finite rows)
    (args : Nat → BoundsTy) {Δ a b} (h : SemanticSub Δ a b) :
    SemanticSub (Δ.map (CountSubstitution.constraint rows))
      (combined rows args a) (combined rows args b) :=
  subtype args (CountSubstitution.subtype rows hf h)

/-- A scoped count instance can be specialized at HM bound slots while retaining
    caller count scope and HM shape. Establishing the actual binder-slot map and
    argument instantiation evidence from the HM artifact remains separate work. -/
theorem instance_inScope {s counts caller} (inst : Instance s counts caller)
    (args : Nat → BoundsTy) (ha : ∀ i, BoundsScoped caller (args i)) :
    BoundsScoped caller (combined (s.quantified.zip counts) args s.body) :=
  inScope args inst.bodyScoped ha

theorem instance_useSubtype {s counts caller Δ} (inst : Instance s counts caller)
    (hu : inst.Usable Δ) (args : Nat → BoundsTy) {a b} (h : SemanticSub s.premises a b) :
    SemanticSub Δ (combined (s.quantified.zip counts) args a)
      (combined (s.quantified.zip counts) args b) := subtype args (inst.useSubtype hu h)

mutual
/-- Relational HM instantiation determines specialization at every used slot;
    unused slots need no invented type argument or default-shape witness. -/
theorem hm_instance {tyArgs τ found} (h : InstantiatesBy tyArgs τ found)
    (f : Nat → Ty) (ha : ∀ i t, tyArgs[i]? = some t → f i = t) :
    τ.instantiate f = found := by
  cases h with
  | prim | fvar => simp only [Ty.instantiate]
  | bvar hi => exact ha _ _ hi
  | arrow hd hc =>
      simp only [Ty.instantiate, hm_instance hd f ha, hm_instance hc f ha]
  | bl he => simp only [Ty.instantiate, hm_instance he f ha]
  | customTy hs => simp only [Ty.instantiate, hm_list_instance hs f ha]
termination_by sizeOf τ + sizeOf found

private theorem hm_list_instance {tyArgs as bs} (h : List.Forall₂ (InstantiatesBy tyArgs) as bs)
    (f : Nat → Ty) (ha : ∀ i t, tyArgs[i]? = some t → f i = t) :
    TyList.instantiate f as = bs := by
  cases h with
  | nil => simp only [TyList.instantiate]
  | cons hh ht => simp only [TyList.instantiate, hm_instance hh f ha, hm_list_instance ht f ha]
termination_by sizeOf as + sizeOf bs
end

/-- The final HM `.found` monotype remains authoritative. Given the actual
    inferred scheme and an HM instantiation witness, combined bounds
    specialization has precisely that monotype, preserving free HM captures.
    Extracting the binder-slot map and witnesses from artifacts is not done here. -/
theorem found_shape (rows : CountSubstitution.Bindings) (args : Nat → BoundsTy)
    {β : BoundsTy} {σ : PolyTy} {tyArgs : List Ty} {found : Ty}
    (hb : Synth.BoundsTy.toTy β = σ.body)
    (hi : σ.InstantiatesTo tyArgs found)
    (ha : ∀ i t, tyArgs[i]? = some t → Synth.BoundsTy.toTy (args i) = t) :
    Synth.BoundsTy.toTy (combined rows args β) = found := by
  rw [combined_shape, hb]
  exact hm_instance hi _ ha

#print axioms shape
#print axioms subtype
#print axioms combined_shape
#print axioms combined_subtype
#print axioms instance_useSubtype
#print axioms found_shape

end FHM.Bounds.TypeSubstitution
