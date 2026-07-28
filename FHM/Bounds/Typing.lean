import FHM.Core
import FHM.Bounds.Kernel
import FHM.Bounds.Oracle
import FHM.Bounds.Commit

/-!
# Bounds typing on Core — BoundInfo + parasitic HasBounds (P2 API)

**Status:** P2 theorems filled (see end for `HasBounds.weaken_Δ` report).

`HasBounds Δ bctx e τ β` assigns bound info `β` to Core `e` at HM type `τ`.
Does **not** re-derive HM; compose with `TypeOfElabHM` at theorem boundaries.

`Agrees β τ` is the shape invariant. List is never `custom "List" […]`.
Uniqueness ∉ declarative typing. Match join: min/max on every `list`.
-/

namespace FHM.Bounds

open Std

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

/-- Well-formed List arities for `Agrees` / `defaultBounds`.
Unrestricted `∀ τ, Agrees (defaultBounds τ) τ` is **false**:
`customTy "List" []` has no `Agrees` witness. -/
inductive ListShapeOK : Ty → Prop where
  | prim {p} : ListShapeOK (.prim p)
  | arrow {a b} : ListShapeOK a → ListShapeOK b → ListShapeOK (.arrow a b)
  | bvar {i} : ListShapeOK (.bvar i)
  | fvar {i} : ListShapeOK (.fvar i)
  | list {α} : ListShapeOK α → ListShapeOK (listTy α)
  | custom {n tys} :
      n ≠ listTyName →
      (∀ t ∈ tys, ListShapeOK t) →
      ListShapeOK (.customTy n tys)

private theorem forall₂_defaultBounds
    {tys : List Ty} (h : ∀ t ∈ tys, Agrees (defaultBounds t) t) :
    List.Forall₂ Agrees (tys.map defaultBounds) tys := by
  induction tys with
  | nil => exact .nil
  | cons t ts ih =>
      exact .cons (h t (by simp)) (ih (fun u hu => h u (List.mem_cons_of_mem _ hu)))

theorem defaultBounds_agrees {τ : Ty} (h : ListShapeOK τ) :
    Agrees (defaultBounds τ) τ := by
  induction h with
  | prim => simp only [defaultBounds]; exact .prim
  | arrow _ _ iha ihb => simp only [defaultBounds]; exact .arrow iha ihb
  | bvar => simp only [defaultBounds]; exact .bvar
  | fvar => simp only [defaultBounds]; exact .fvar
  | list _ ih =>
      simp only [listTy, defaultBounds, ↓reduceIte]
      exact .list ih
  | @custom n tys hne htys ih =>
      have hmap := forall₂_defaultBounds ih
      match tys with
      | [] => simpa [defaultBounds] using Agrees.custom hne .nil
      | [α] =>
          simp only [defaultBounds, hne, ↓reduceIte]
          cases hmap with | cons ha _ => exact .custom hne (.cons ha .nil)
      | _ :: _ :: _ =>
          simpa [defaultBounds] using Agrees.custom hne hmap

abbrev BoundEnv := List BoundInfo

def consBoundEnv (bctx : BoundEnv) (lo hi : Count) (βe : BoundInfo) : BoundEnv :=
  βe :: .list (.pred lo) (.pred hi) βe :: bctx

/-! ## Canonical min/max + joinBoundInfo (WF) -/

private def kindNat : VarKind → Nat
  | .rigid => 0 | .inferable => 1

def Count.encode : Count → List Nat
  | .lit n => [0, n]
  | .var v => [1, kindNat v.kind, v.idx]
  | .add a b => [2, (encode a).length] ++ encode a ++ encode b
  | .mul a b => [3, (encode a).length] ++ encode a ++ encode b
  | .pred a => [4, (encode a).length] ++ encode a
  | .min a b => [5, (encode a).length] ++ encode a ++ encode b
  | .max a b => [6, (encode a).length] ++ encode a ++ encode b

@[simp] private theorem enc_lit (n : Nat) : Count.encode (.lit n) = [0, n] := rfl
@[simp] private theorem enc_var (v : Var) : Count.encode (.var v) = [1, kindNat v.kind, v.idx] := rfl
@[simp] private theorem enc_add (a b : Count) :
  Count.encode (.add a b) = [2, (Count.encode a).length] ++ Count.encode a ++ Count.encode b := rfl
@[simp] private theorem enc_mul (a b : Count) :
  Count.encode (.mul a b) = [3, (Count.encode a).length] ++ Count.encode a ++ Count.encode b := rfl
@[simp] private theorem enc_pred (a : Count) :
  Count.encode (.pred a) = [4, (Count.encode a).length] ++ Count.encode a := rfl
@[simp] private theorem enc_min (a b : Count) :
  Count.encode (.min a b) = [5, (Count.encode a).length] ++ Count.encode a ++ Count.encode b := rfl
@[simp] private theorem enc_max (a b : Count) :
  Count.encode (.max a b) = [6, (Count.encode a).length] ++ Count.encode a ++ Count.encode b := rfl

private theorem enc_bin (tag : Nat) (a1 a2 b1 b2 : Count)
    (ih1 : Count.encode a1 = Count.encode b1 → a1 = b1)
    (ih2 : Count.encode a2 = Count.encode b2 → a2 = b2)
    (h : [tag, (Count.encode a1).length] ++ Count.encode a1 ++ Count.encode a2 =
         [tag, (Count.encode b1).length] ++ Count.encode b1 ++ Count.encode b2) :
    a1 = b1 ∧ a2 = b2 := by
  have hlen : (Count.encode a1).length = (Count.encode b1).length := by
    have := congrArg (fun l : List Nat => l[1]?) h; simp at this; exact this
  have hrest : Count.encode a1 ++ Count.encode a2 = Count.encode b1 ++ Count.encode b2 := by
    have := congrArg (fun l : List Nat => l.drop 2) h; simpa using this
  have he1 : Count.encode a1 = Count.encode b1 := by
    have t := congrArg (fun l : List Nat => l.take (Count.encode a1).length) hrest
    simp only [List.take_left] at t
    have t' : (Count.encode b1 ++ Count.encode b2).take (Count.encode a1).length = Count.encode b1 := by
      rw [hlen]; exact List.take_left
    rw [t'] at t; exact t
  have he2 : Count.encode a2 = Count.encode b2 := by
    have t := congrArg (fun l : List Nat => l.drop (Count.encode a1).length) hrest
    simp only [List.drop_left] at t
    have t' : (Count.encode b1 ++ Count.encode b2).drop (Count.encode a1).length = Count.encode b2 := by
      rw [hlen]; exact List.drop_left
    rw [t'] at t; exact t
  exact ⟨ih1 he1, ih2 he2⟩

private theorem kn_inj {k k' : VarKind} (h : kindNat k = kindNat k') : k = k' := by
  cases k <;> cases k' <;> simp [kindNat] at h ⊢

theorem Count.encode_inj {a b : Count} (h : Count.encode a = Count.encode b) : a = b := by
  induction a generalizing b with
  | lit n => cases b <;> (simp at h; try exact congrArg Count.lit h)
  | var v =>
    cases b with
    | var w =>
      simp at h; obtain ⟨hk, hi⟩ := h
      have hk' := kn_inj hk; cases v; cases w; simp_all
    | _ => simp at h
  | add a1 a2 ih1 ih2 =>
    cases b with
    | add b1 b2 => have ⟨e1, e2⟩ := enc_bin 2 a1 a2 b1 b2 ih1 ih2 (by simpa using h); simp [e1, e2]
    | _ => simp at h
  | mul a1 a2 ih1 ih2 =>
    cases b with
    | mul b1 b2 => have ⟨e1, e2⟩ := enc_bin 3 a1 a2 b1 b2 ih1 ih2 (by simpa using h); simp [e1, e2]
    | _ => simp at h
  | pred a ih =>
    cases b with
    | pred b => simp at h; exact congrArg _ (ih h.2)
    | _ => simp at h
  | min a1 a2 ih1 ih2 =>
    cases b with
    | min b1 b2 => have ⟨e1, e2⟩ := enc_bin 5 a1 a2 b1 b2 ih1 ih2 (by simpa using h); simp [e1, e2]
    | _ => simp at h
  | max a1 a2 ih1 ih2 =>
    cases b with
    | max b1 b2 => have ⟨e1, e2⟩ := enc_bin 6 a1 a2 b1 b2 ih1 ih2 (by simpa using h); simp [e1, e2]
    | _ => simp at h

def joinMin (a b : Count) : Count :=
  if Count.encode a ≤ Count.encode b then .min a b else .min b a
def joinMax (a b : Count) : Count :=
  if Count.encode a ≤ Count.encode b then .max a b else .max b a

theorem joinMin_comm (a b : Count) : joinMin a b = joinMin b a := by
  simp only [joinMin]
  have t : Count.encode a ≤ Count.encode b ∨ Count.encode b ≤ Count.encode a := le_total
  rcases t with hab | hba
  · simp only [hab, ↓reduceIte]
    by_cases hba' : Count.encode b ≤ Count.encode a
    · have : a = b := Count.encode_inj (le_antisymm hab hba'); subst this; simp
    · simp [hba']
  · by_cases hab' : Count.encode a ≤ Count.encode b
    · have : a = b := Count.encode_inj (le_antisymm hab' hba); subst this; simp
    · simp [hab', hba]

theorem joinMax_comm (a b : Count) : joinMax a b = joinMax b a := by
  simp only [joinMax]
  have t : Count.encode a ≤ Count.encode b ∨ Count.encode b ≤ Count.encode a := le_total
  rcases t with hab | hba
  · simp only [hab, ↓reduceIte]
    by_cases hba' : Count.encode b ≤ Count.encode a
    · have : a = b := Count.encode_inj (le_antisymm hab hba'); subst this; simp
    · simp [hba']
  · by_cases hab' : Count.encode a ≤ Count.encode b
    · have : a = b := Count.encode_inj (le_antisymm hab' hba); subst this; simp
    · simp [hab', hba]

mutual
  def joinBoundInfo (β₁ β₂ : BoundInfo) : Option BoundInfo :=
    match β₁, β₂ with
    | .prim p, .prim q => if p = q then some (.prim p) else none
    | .bvar i, .bvar j => if i = j then some (.bvar i) else none
    | .fvar i, .fvar j => if i = j then some (.fvar i) else none
    | .arrow a b, .arrow a' b' =>
        match joinBoundInfo a a', joinBoundInfo b b' with
        | some d, some c => some (.arrow d c)
        | _, _ => none
    | .list lo₁ hi₁ e₁, .list lo₂ hi₂ e₂ =>
        match joinBoundInfo e₁ e₂ with
        | some e => some (.list (joinMin lo₁ lo₂) (joinMax hi₁ hi₂) e)
        | none => none
    | .custom n₁ as₁, .custom n₂ as₂ =>
        if n₁ = n₂ && as₁.length = as₂.length then
          match joinBoundInfoArgs as₁ as₂ with
          | some args => some (.custom n₁ args)
          | none => none
        else none
    | _, _ => none
  termination_by sizeOf β₁ + sizeOf β₂

  def joinBoundInfoArgs (as₁ as₂ : List BoundInfo) : Option (List BoundInfo) :=
    match as₁, as₂ with
    | [], [] => some []
    | x :: xs, y :: ys =>
        match joinBoundInfo x y, joinBoundInfoArgs xs ys with
        | some z, some zs => some (z :: zs)
        | _, _ => none
    | _, _ => none
  termination_by sizeOf as₁ + sizeOf as₂
end

theorem joinBoundInfo_comm (β₁ β₂ : BoundInfo) :
    joinBoundInfo β₁ β₂ = joinBoundInfo β₂ β₁ := by
  refine joinBoundInfo.induct
    (motive1 := fun a b => joinBoundInfo a b = joinBoundInfo b a)
    (motive2 := fun as bs => joinBoundInfoArgs as bs = joinBoundInfoArgs bs as)
    ?c1 ?c2 ?c3 ?c4 ?c5 ?c6 ?c7 ?c8 ?c9 ?c10 ?c11 ?c12 ?c13 ?c14
    ?c15 ?c16 ?c17 ?c18 β₁ β₂
  case c1 => intro q; rw [joinBoundInfo.eq_def (β₁ := .prim q) (β₂ := .prim q)]
  case c2 =>
    intro p q hne
    have hne' : q ≠ p := (hne ·.symm)
    rw [joinBoundInfo.eq_def (β₁ := .prim p) (β₂ := .prim q),
        joinBoundInfo.eq_def (β₁ := .prim q) (β₂ := .prim p)]
    simp [hne, hne']
  case c3 => intro j; rw [joinBoundInfo.eq_def (β₁ := .bvar j) (β₂ := .bvar j)]
  case c4 =>
    intro i j hne
    have hne' : j ≠ i := (hne ·.symm)
    rw [joinBoundInfo.eq_def (β₁ := .bvar i) (β₂ := .bvar j),
        joinBoundInfo.eq_def (β₁ := .bvar j) (β₂ := .bvar i)]
    simp [hne, hne']
  case c5 => intro j; rw [joinBoundInfo.eq_def (β₁ := .fvar j) (β₂ := .fvar j)]
  case c6 =>
    intro i j hne
    have hne' : j ≠ i := (hne ·.symm)
    rw [joinBoundInfo.eq_def (β₁ := .fvar i) (β₂ := .fvar j),
        joinBoundInfo.eq_def (β₁ := .fvar j) (β₂ := .fvar i)]
    simp [hne, hne']
  case c7 =>
    intro a b a' b' d c hc hd iha ihb
    rw [joinBoundInfo.eq_def (β₁ := a.arrow b) (β₂ := a'.arrow b'),
        joinBoundInfo.eq_def (β₁ := a'.arrow b') (β₂ := a.arrow b)]
    have hd' : joinBoundInfo a' a = some d := iha.symm ▸ hd
    have hc' : joinBoundInfo b' b = some c := ihb.symm ▸ hc
    simp [iha, ihb, hd', hc']
  case c8 =>
    intro a b a' b' hfail iha ihb
    rw [joinBoundInfo.eq_def (β₁ := a.arrow b) (β₂ := a'.arrow b'),
        joinBoundInfo.eq_def (β₁ := a'.arrow b') (β₂ := a.arrow b)]
    simp only []
    cases h1 : joinBoundInfo a a' with
    | none =>
      have h1' : joinBoundInfo a' a = none := iha.symm ▸ h1
      cases h2 : joinBoundInfo b b' with
      | none =>
        have h2' : joinBoundInfo b' b = none := ihb.symm ▸ h2
        simp [h1', h2']
      | some c =>
        have h2' : joinBoundInfo b' b = some c := ihb.symm ▸ h2
        simp [h1', h2']
    | some d =>
      cases h2 : joinBoundInfo b b' with
      | none =>
        have h1' : joinBoundInfo a' a = some d := iha.symm ▸ h1
        have h2' : joinBoundInfo b' b = none := ihb.symm ▸ h2
        simp [h1', h2']
      | some c =>
          exact False.elim (hfail d c h1 h2)
  case c9 =>
    intro lo1 hi1 e1 lo2 hi2 e2 e he ihe
    rw [joinBoundInfo.eq_def (β₁ := .list lo1 hi1 e1) (β₂ := .list lo2 hi2 e2),
        joinBoundInfo.eq_def (β₁ := .list lo2 hi2 e2) (β₂ := .list lo1 hi1 e1)]
    simp only []
    have he' : joinBoundInfo e2 e1 = some e := ihe.symm ▸ he
    simp [he, he', joinMin_comm lo1 lo2, joinMax_comm hi1 hi2]
  case c10 =>
    intro lo1 hi1 e1 lo2 hi2 e2 he ihe
    rw [joinBoundInfo.eq_def (β₁ := .list lo1 hi1 e1) (β₂ := .list lo2 hi2 e2),
        joinBoundInfo.eq_def (β₁ := .list lo2 hi2 e2) (β₂ := .list lo1 hi1 e1)]
    simp only []
    have he' : joinBoundInfo e2 e1 = none := ihe.symm ▸ he
    simp [he, he']
  case c11 =>
    intro n1 as1 n2 as2 hcond args hargs ihas
    rw [joinBoundInfo.eq_def (β₁ := .custom n1 as1) (β₂ := .custom n2 as2),
        joinBoundInfo.eq_def (β₁ := .custom n2 as2) (β₂ := .custom n1 as1)]
    simp only []
    have hn : n1 = n2 ∧ as1.length = as2.length := by
      simpa [Bool.and_eq_true, decide_eq_true_eq] using hcond
    have hcond' : (decide (n2 = n1) && decide (as2.length = as1.length)) = true := by
      simp [hn.1.symm, hn.2.symm]
    have hargs' : joinBoundInfoArgs as2 as1 = some args := ihas.symm ▸ hargs
    simp [hargs, hargs', hn.1, hn.2]
  case c12 =>
    intro n1 as1 n2 as2 hcond hargs ihas
    rw [joinBoundInfo.eq_def (β₁ := .custom n1 as1) (β₂ := .custom n2 as2),
        joinBoundInfo.eq_def (β₁ := .custom n2 as2) (β₂ := .custom n1 as1)]
    simp only []
    have hn : n1 = n2 ∧ as1.length = as2.length := by
      simpa [Bool.and_eq_true, decide_eq_true_eq] using hcond
    have hcond' : (decide (n2 = n1) && decide (as2.length = as1.length)) = true := by
      simp [hn.1.symm, hn.2.symm]
    have hargs' : joinBoundInfoArgs as2 as1 = none := ihas.symm ▸ hargs
    simp [hcond, hcond', hargs, hargs']
  case c13 =>
    intro n1 as1 n2 as2 hcond
    have hcond' : ¬(decide (n2 = n1) && decide (as2.length = as1.length)) = true := by
      intro h
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h hcond
      exact hcond ⟨h.1.symm, h.2.symm⟩
    rw [joinBoundInfo.eq_def (β₁ := .custom n1 as1) (β₂ := .custom n2 as2),
        joinBoundInfo.eq_def (β₁ := .custom n2 as2) (β₂ := .custom n1 as1)]
    simp [hcond, hcond']
  case c14 =>
    intro a b hp hbv hfv har hli hcu
    rw [joinBoundInfo.eq_def (β₁ := a) (β₂ := b),
        joinBoundInfo.eq_def (β₁ := b) (β₂ := a)]
    cases a <;> cases b <;> first
      | rfl
      | exact False.elim (hp _ _ rfl rfl)
      | exact False.elim (hbv _ _ rfl rfl)
      | exact False.elim (hfv _ _ rfl rfl)
      | exact False.elim (har _ _ _ _ rfl rfl)
      | exact False.elim (hli _ _ _ _ _ _ rfl rfl)
      | exact False.elim (hcu _ _ _ _ rfl rfl)
  case c15 => rfl
  case c16 =>
    intro x xs y ys z zs hys hx ihx ihys
    rw [joinBoundInfoArgs.eq_def (as₁ := x::xs) (as₂ := y::ys),
        joinBoundInfoArgs.eq_def (as₁ := y::ys) (as₂ := x::xs)]
    simp only []
    have hx' : joinBoundInfo y x = some z := ihx.symm ▸ hx
    have hys' : joinBoundInfoArgs ys xs = some zs := ihys.symm ▸ hys
    simp [hx, hx', hys, hys']
  case c17 =>
    intro x xs y ys hfail ihx ihys
    rw [joinBoundInfoArgs.eq_def (as₁ := x::xs) (as₂ := y::ys),
        joinBoundInfoArgs.eq_def (as₁ := y::ys) (as₂ := x::xs)]
    simp only []
    cases h1 : joinBoundInfo x y with
    | none =>
      have h1' : joinBoundInfo y x = none := ihx.symm ▸ h1
      cases h2 : joinBoundInfoArgs xs ys with
      | none =>
        have h2' : joinBoundInfoArgs ys xs = none := ihys.symm ▸ h2
        simp [h1', h2']
      | some zs =>
        have h2' : joinBoundInfoArgs ys xs = some zs := ihys.symm ▸ h2
        simp [h1', h2']
    | some z =>
      cases h2 : joinBoundInfoArgs xs ys with
      | none =>
        have h1' : joinBoundInfo y x = some z := ihx.symm ▸ h1
        have h2' : joinBoundInfoArgs ys xs = none := ihys.symm ▸ h2
        simp [h1', h2']
      | some zs =>
          exact False.elim (hfail z zs h1 h2)
  case c18 =>
    intro as bs hnil hcons
    rw [joinBoundInfoArgs.eq_def (as₁ := as) (as₂ := bs),
        joinBoundInfoArgs.eq_def (as₁ := bs) (as₂ := as)]
    cases as <;> cases bs <;> first
      | rfl
      | exact False.elim (hnil rfl rfl)
      | exact False.elim (hcons _ _ _ _ rfl rfl)

/-! ## Sub -/

/-- `Sub Δ β β'`: β usable where β' demanded. Structural; List via `checkValid` intervals.

`list_refl` omits `DemandOK` so unrestricted `Sub.refl` holds; `DemandOK` stays on
the proper-subtype `list` rule. `custom` allows any name so `Sub.refl` covers all
`BoundInfo`s. -/
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
      Sub Δ e e →
      Sub Δ (.list lo hi e) (.list lo hi e)
  | custom {name as bs} :
      List.Forall₂ (Sub Δ) as bs →
      Sub Δ (.custom name as) (.custom name bs)

/-! ## HasBounds -/

def boundInfoOfPrimLit : PrimLitExpr → BoundInfo
  | .unit => .prim .unit
  | .int _ => .prim .int
  | .nat _ => .prim .nat
  | .char _ => .prim .char

private theorem boundInfoOfPrimLit_agrees (p : PrimLitExpr) :
    Agrees (boundInfoOfPrimLit p) (PrimLitExpr.ty p) := by
  cases p <;> exact .prim

/-- Parasitic bound assignment. Every conclusion should satisfy `Agrees β τ`. -/
inductive HasBounds :
    List Constraint → BoundEnv → Expr → Ty → BoundInfo → Prop where
  | primLit {Δ bctx p} :
      HasBounds Δ bctx (.primLit p) (PrimLitExpr.ty p) (boundInfoOfPrimLit p)
  | primBinOp {Δ bctx op τ β} :
      Agrees β τ →
      HasBounds Δ bctx (.primBinOp op) τ β
  | nil {Δ bctx α βe} :
      Agrees βe α →
      HasBounds Δ bctx (.ctor nilCtorName) (listTy α) (.list (.lit 0) (.lit 0) βe)
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

/-! ## Theorems -/

theorem Sub.refl (Δ : List Constraint) (β : BoundInfo) : Sub Δ β β := by
  refine BoundInfo.rec
    (motive_1 := fun β => Sub Δ β β)
    (motive_2 := fun as => List.Forall₂ (Sub Δ) as as)
    (fun _ => .prim)
    (fun _ _ ha hb => .arrow ha hb)
    (fun _ => .bvar)
    (fun _ => .fvar)
    (fun _ _ _ he => .list_refl he)
    (fun _ _ hargs => .custom hargs)
    List.Forall₂.nil
    (fun _ _ hh ht => List.Forall₂.cons hh ht)
    β

mutual
/-- Join of two bounds that both agree with `τ` still agrees with `τ`. -/
  theorem joinBoundInfo_agrees {β₁ : BoundInfo} {τ : Ty} (h1 : Agrees β₁ τ) :
      ∀ {β₂ β}, joinBoundInfo β₁ β₂ = some β → Agrees β₂ τ → Agrees β τ := by
    intro β₂ β hj h2
    cases h1 with
    | @prim p =>
        cases h2; simp [joinBoundInfo.eq_def] at hj; cases hj; exact .prim
    | @arrow βd βc τd τc hd hc =>
        cases h2 with
        | @arrow βd' βc' _ _ hd' hc' =>
            rw [joinBoundInfo.eq_def] at hj
            cases hdj : joinBoundInfo βd βd' with
            | none =>
                cases hcj : joinBoundInfo βc βc' <;> simp [hdj, hcj] at hj
            | some d =>
                cases hcj : joinBoundInfo βc βc' with
                | none => simp [hdj, hcj] at hj
                | some c =>
                    simp [hdj, hcj] at hj; cases hj
                    exact .arrow (joinBoundInfo_agrees hd hdj hd')
                      (joinBoundInfo_agrees hc hcj hc')
    | @bvar i =>
        cases h2; simp [joinBoundInfo.eq_def] at hj; cases hj; exact .bvar
    | @fvar i =>
        cases h2; simp [joinBoundInfo.eq_def] at hj; cases hj; exact .fvar
    | @list lo hi βe α he =>
        cases h2 with
        | @list lo' hi' βe' _ he' =>
            rw [joinBoundInfo.eq_def] at hj
            cases hej : joinBoundInfo βe βe' with
            | none => simp [hej] at hj
            | some e =>
                simp [hej] at hj; cases hj
                exact .list (joinBoundInfo_agrees he hej he')
        | @custom n _ _ hne _ =>
            -- τ = listTy α = customTy listTyName [_], so n = listTyName, contradicts hne
            exact absurd rfl hne
    | @custom name args tys hne hargs =>
        cases h2 with
        | @list _ _ _ _ _ =>
            -- τ = customTy name _ with name ≠ listTyName, can't be listTy
            exact absurd rfl hne
        | @custom _ args' _ _ hargs' =>
            rw [joinBoundInfo.eq_def] at hj
            have hl : args.length = args'.length := by
              have := List.Forall₂.length_eq hargs
              have := List.Forall₂.length_eq hargs'
              omega
            simp only [↓reduceIte, hl, decide_true, Bool.and_self] at hj
            cases hjs : joinBoundInfoArgs args args' with
            | none => simp [hjs] at hj
            | some zs =>
                simp [hjs] at hj; cases hj
                exact .custom hne (joinBoundInfoArgs_agrees hargs hjs hargs')
  termination_by sizeOf β₁

  theorem joinBoundInfoArgs_agrees
      {as : List BoundInfo} {tys : List Ty}
      (hargs : List.Forall₂ Agrees as tys) :
      ∀ {bs zs}, joinBoundInfoArgs as bs = some zs →
        List.Forall₂ Agrees bs tys → List.Forall₂ Agrees zs tys := by
    cases hargs with
    | nil =>
        intro bs zs hj hb
        cases hb
        simp [joinBoundInfoArgs.eq_def] at hj; cases hj; exact .nil
    | @cons a τ as tys ha has =>
        intro bs zs hj hb
        cases hb with
        | @cons b _ bs' _ hb hbs =>
            rw [joinBoundInfoArgs.eq_def] at hj
            cases hx : joinBoundInfo a b with
            | none =>
                cases hxs : joinBoundInfoArgs as bs' <;> simp [hx, hxs] at hj
            | some z =>
                cases hxs : joinBoundInfoArgs as bs' with
                | none => simp [hx, hxs] at hj
                | some zs' =>
                    simp [hx, hxs] at hj; cases hj
                    exact .cons (joinBoundInfo_agrees ha hx hb)
                      (joinBoundInfoArgs_agrees has hxs hbs)
  termination_by sizeOf as
end

theorem HasBounds.agrees {Δ bctx e τ β}
    (h : HasBounds Δ bctx e τ β) : Agrees β τ := by
  induction h with
  | primLit => exact boundInfoOfPrimLit_agrees _
  | primBinOp hA => exact hA
  | nil hA => exact .list hA
  | cons _ _ _ _ iht =>
      cases iht with
      | list he => exact .list he
  | var _ hA => exact hA
  | app _ _ _ ihf _ =>
      cases ihf with
      | arrow _ hr => exact hr
  | lambda hA _ ihb => exact .arrow hA ihb
  | letMono _ _ _ ih2 => exact ih2
  | matchList _ _ _ hj _ih_s ihnil ihcons =>
      exact joinBoundInfo_agrees ihnil hj ihcons
  | matchNil _ _ _ _ ih => exact ih
  | matchCons _ _ _ _ ih => exact ih
  | ctor _ hA => exact hA

/-!
### `HasBounds.weaken_Δ` — **not proved; stated form is false operationally**

Original statement:
```
theorem HasBounds.weaken_Δ {Δ Δ' bctx e τ β}
    (h : HasBounds Δ bctx e τ β)
    (hpre : ∀ c ∈ Δ, c ∈ Δ') :
    HasBounds Δ' bctx e τ β
```

**Why it fails.** Rules store computational `checkValid φ = .valid` with
`φ.prem = Δ` (`Sub.list`, `matchNil`, `matchCons`). Semantically
`ForallProblem.Valid` is monotone in premises, but `checkValid` is a Z3 bridge
that may return `.valid` under a small premise set and `.unknown` under a larger
one. There is no proved `checkValid_mono`, and it is false for the executable
oracle. Set-inclusion of path conditions is also the wrong API for match
refinements (interesting direction is branch strengthening, not thinning).

**Proposed restatements:**
1. Add an oracle-monotonicity hypothesis on all `checkValid` side conditions.
2. Store semantic `ForallProblem.Valid` in `Sub` / match rules; prove Valid-mono.
3. Drop until a path-condition algebra is designed.
-/

def WellBound (ctors : CtorEnv) (e : Expr) (τ : Ty) (β : BoundInfo) : Prop :=
  TypeOfElabHM ⟨[], ctors⟩ e τ ∧ HasBounds [] [] e τ β

/-! ## P3: BoundCovers — List match coverage under path conditions

**Status:** P3 theorems proved (branch detectors + `BoundCovers.only_list`).

Independent of Core `AllMatchesExhaustive`. Pipeline (BL mode):
* List scrutinee with refined `β` → require `BoundCovers Δ β branches`
* Other scrutinees → existing ctor exhaustiveness

`β` is an **input** (from `HasBounds`); Covers does not re-synthesize bounds.
Oracle side conditions use `checkValid … = .valid` (same as `HasBounds` match rules).
-/

/-- Branch list contains a `Nil` pattern with arity 0. -/
def hasNilBranch (brs : List (MatchPattern × Expr)) : Prop :=
  ∃ body, (MatchPattern.named nilCtorName 0, body) ∈ brs

/-- Branch list contains a `Cons` pattern with arity 2. -/
def hasConsBranch (brs : List (MatchPattern × Expr)) : Prop :=
  ∃ body, (MatchPattern.named consCtorName 2, body) ∈ brs

/-- Branch list contains a wildcard (covers every remaining case). -/
def hasWildcardBranch (brs : List (MatchPattern × Expr)) : Prop :=
  ∃ body, (MatchPattern.wildcard, body) ∈ brs

/-- Under path conditions `Δ`, match `branches` cover every case allowed by
scrutinee bound info `β`.

**Only List `β` has introduction rules.** For non-List `β`, `BoundCovers` is
simply not derivable — the pipeline should use `AllMatchesExhaustive` instead.
Wildcards cover List scrutinees without arithmetic side conditions. -/
inductive BoundCovers (Δ : List Constraint) :
    BoundInfo → List (MatchPattern × Expr) → Prop where
  /-- Both Nil and Cons present (order irrelevant). No arithmetic side condition. -/
  | listFull {lo hi βe brs} :
      hasNilBranch brs →
      hasConsBranch brs →
      BoundCovers Δ (.list lo hi βe) brs

  /-- Nil-only: upper bound forces empty under `Δ`. -/
  | listNilOnly {lo hi βe brs} :
      checkValid (mustBeEmpty Δ hi) = .valid →
      hasNilBranch brs →
      BoundCovers Δ (.list lo hi βe) brs

  /-- Cons-only: lower bound forces non-empty under `Δ`. -/
  | listConsOnly {lo hi βe brs} :
      checkValid (mustBeNonempty Δ lo) = .valid →
      hasConsBranch brs →
      BoundCovers Δ (.list lo hi βe) brs

  /-- Wildcard covers all List lengths/cases. -/
  | listWild {lo hi βe brs} :
      hasWildcardBranch brs →
      BoundCovers Δ (.list lo hi βe) brs

/-- Match expression covered given scrutinee bounds (expression shape not required). -/
def BoundCoversMatch (Δ : List Constraint) (β : BoundInfo)
    (m : Expr) : Prop :=
  match m with
  | .match_ _ brs => BoundCovers Δ β brs
  | _ => False

/-- Pipeline-facing: empty path, list bounds from `HasBounds`. -/
def BoundCoversClosed (β : BoundInfo) (brs : List (MatchPattern × Expr)) : Prop :=
  BoundCovers [] β brs

/-! ### P3 theorems -/

/-- Executable detectors for branch presence (mirrors of the Props). -/
def hasNilBranchB (brs : List (MatchPattern × Expr)) : Bool :=
  brs.any fun
    | (.named c n, _) => c == nilCtorName && n == 0
    | _ => false

def hasConsBranchB (brs : List (MatchPattern × Expr)) : Bool :=
  brs.any fun
    | (.named c n, _) => c == consCtorName && n == 2
    | _ => false

def hasWildcardBranchB (brs : List (MatchPattern × Expr)) : Bool :=
  brs.any fun
    | (.wildcard, _) => true
    | _ => false

theorem hasNilBranch_iff (brs : List (MatchPattern × Expr)) :
    hasNilBranchB brs = true ↔ hasNilBranch brs := by
  constructor
  · intro h
    obtain ⟨x, hx, hp⟩ := List.any_eq_true.mp h
    match x with
    | (.named c n, body) =>
        simp only [Bool.and_eq_true, beq_iff_eq] at hp
        obtain ⟨rfl, rfl⟩ := hp
        exact ⟨body, hx⟩
    | (.wildcard, _) => simp at hp
  · intro ⟨body, hmem⟩
    exact List.any_eq_true.mpr ⟨(.named nilCtorName 0, body), hmem, by simp⟩

theorem hasConsBranch_iff (brs : List (MatchPattern × Expr)) :
    hasConsBranchB brs = true ↔ hasConsBranch brs := by
  constructor
  · intro h
    obtain ⟨x, hx, hp⟩ := List.any_eq_true.mp h
    match x with
    | (.named c n, body) =>
        simp only [Bool.and_eq_true, beq_iff_eq] at hp
        obtain ⟨rfl, rfl⟩ := hp
        exact ⟨body, hx⟩
    | (.wildcard, _) => simp at hp
  · intro ⟨body, hmem⟩
    exact List.any_eq_true.mpr ⟨(.named consCtorName 2, body), hmem, by simp⟩

theorem hasWildcardBranch_iff (brs : List (MatchPattern × Expr)) :
    hasWildcardBranchB brs = true ↔ hasWildcardBranch brs := by
  constructor
  · intro h
    obtain ⟨x, hx, hp⟩ := List.any_eq_true.mp h
    match x with
    | (.named _ _, _) => simp at hp
    | (.wildcard, body) => exact ⟨body, hx⟩
  · intro ⟨body, hmem⟩
    exact List.any_eq_true.mpr ⟨(.wildcard, body), hmem, rfl⟩

/-- Full List match is always covered (no Z3). -/
theorem BoundCovers.listFull_of_both {Δ lo hi βe brs}
    (hN : hasNilBranch brs) (hC : hasConsBranch brs) :
    BoundCovers Δ (.list lo hi βe) brs :=
  .listFull hN hC

/-- Wildcard List match is always covered (no Z3). -/
theorem BoundCovers.listWild_of {Δ lo hi βe brs}
    (h : hasWildcardBranch brs) :
    BoundCovers Δ (.list lo hi βe) brs :=
  .listWild h

/-- Non-List bound info never satisfies `BoundCovers` (by constructors). -/
theorem BoundCovers.only_list {Δ β brs}
    (h : BoundCovers Δ β brs) :
    ∃ lo hi βe, β = .list lo hi βe := by
  cases h with
  | listFull => exact ⟨_, _, _, rfl⟩
  | listNilOnly => exact ⟨_, _, _, rfl⟩
  | listConsOnly => exact ⟨_, _, _, rfl⟩
  | listWild => exact ⟨_, _, _, rfl⟩

/-! ## P3.5b — BoundAnn + pipeline contract (shapes for sign-off)

**Status:** API review — not yet used by Surface/Live.

After Infer we have Core `e`, HM type `τ`, and synthesized `β` from `HasBounds`.
Surface erase will also produce **ascriptions** (user-written `BL lo hi t` on
bindings). Those ascriptions are checked with `Sub`, not re-inferred.

### Design locks (memo)

* Key ascriptions by **binding de Bruijn index** after lower (parallel to env),
  plus optional body ascription — avoid expression-path maps through PatComp.
* Holes in bound slots: `Option Count` (`none` = hole) until `Count.inf` / solve.
* Pipeline coverage: List `β` → `BoundCovers`; non-List → HM exhaustiveness (external).
-/

/-- A single count slot from surface: concrete or hole (to be solved / defaulted). -/
inductive AnnoCount where
  | hole
  | solid (c : Count)
  deriving Repr

/-- Bound ascription with holes, same spine as `BoundInfo`.
List is the only place `AnnoCount` appears; everything else mirrors `BoundInfo`. -/
inductive BoundAnn where
  | prim (p : PrimTy)
  | arrow (dom cod : BoundAnn)
  | bvar (i : Nat)
  | fvar (i : Nat)
  | list (lo hi : AnnoCount) (elem : BoundAnn)
  | custom (name : TyName) (args : List BoundAnn)
  deriving Repr

/-- Solid ascription (no holes) is already a `BoundInfo`; `none` if any hole remains. -/
def BoundAnn.toBoundInfo? : BoundAnn → Option BoundInfo
  | .prim p => some (.prim p)
  | .bvar i => some (.bvar i)
  | .fvar i => some (.fvar i)
  | .arrow d c =>
      match BoundAnn.toBoundInfo? d, BoundAnn.toBoundInfo? c with
      | some βd, some βc => some (.arrow βd βc)
      | _, _ => none
  | .list (.solid lo) (.solid hi) e =>
      match BoundAnn.toBoundInfo? e with
      | some βe => some (.list lo hi βe)
      | none => none
  | .list _ _ _ => none
  | .custom n as =>
      if n = listTyName then none
      else
        let rec go : (as : List BoundAnn) → Option (List BoundInfo)
          | [] => some []
          | a :: rest =>
              match BoundAnn.toBoundInfo? a, go rest with
              | some β, some bs => some (β :: bs)
              | _, _ => none
            termination_by as => sizeOf as
        (go as).map (fun bs => .custom n bs)
termination_by a => sizeOf a

/-- Pointwise solid conversion of annotation argument lists. -/
def BoundAnnList.toBoundInfo? : List BoundAnn → Option (List BoundInfo)
  | [] => some []
  | a :: rest =>
      match BoundAnn.toBoundInfo? a, BoundAnnList.toBoundInfo? rest with
      | some β, some bs => some (β :: bs)
      | _, _ => none
termination_by as => sizeOf as

/-- `ElabCount Φ a c Φ'` — elaborate annotation count; holes allocate inferables from frontier `Φ`. -/
inductive ElabCount : Nat → AnnoCount → Count → Nat → Prop where
  | hole {Φ} :
      ElabCount Φ .hole (.var ⟨.inferable, Φ⟩) (Φ + 1)
  | solid {Φ c} :
      ElabCount Φ (.solid c) c Φ

/-- `ElabAnn Φ ann β Φ'` — fill holes in a bound ascription to a concrete `BoundInfo`.

v1: holes only in **list** `lo`/`hi` (and nested lists via `elem`).
`custom` args must already be solid (`toBoundInfo?`). -/
inductive ElabAnn : Nat → BoundAnn → BoundInfo → Nat → Prop where
  | prim {Φ p} :
      ElabAnn Φ (.prim p) (.prim p) Φ
  | bvar {Φ i} :
      ElabAnn Φ (.bvar i) (.bvar i) Φ
  | fvar {Φ i} :
      ElabAnn Φ (.fvar i) (.fvar i) Φ
  | arrow {Φ a b βa βb Φ₁ Φ₂} :
      ElabAnn Φ a βa Φ₁ →
      ElabAnn Φ₁ b βb Φ₂ →
      ElabAnn Φ (.arrow a b) (.arrow βa βb) Φ₂
  | list {Φ lo hi e clo chi βe Φ₁ Φ₂ Φ₃} :
      ElabCount Φ lo clo Φ₁ →
      ElabCount Φ₁ hi chi Φ₂ →
      ElabAnn Φ₂ e βe Φ₃ →
      ElabAnn Φ (.list lo hi e) (.list clo chi βe) Φ₃
  | custom {Φ name as bs} :
      name ≠ listTyName →
      BoundAnnList.toBoundInfo? as = some bs →
      ElabAnn Φ (.custom name as) (.custom name bs) Φ

/-- Program-level bound ascriptions after lower (de Bruijn parallel to value env).

`binderAnns[i] = some ann` means binding `i` was surface-ascribed; the body of
the program may carry `bodyAnn`. Missing entries = no ascription (pure synth). -/
structure ProgramBoundAnns where
  /-- Parallel to Core `env` after lower: index 0 = innermost binder. -/
  binderAnns : List (Option BoundAnn) := []
  /-- Optional expected bounds on the whole expression / program body. -/
  bodyAnn : Option BoundAnn := none
  deriving Repr

/-- Lookup ascription for de Bruijn index `i`. -/
def ProgramBoundAnns.get? (a : ProgramBoundAnns) (i : Nat) : Option BoundAnn :=
  a.binderAnns[i]? |>.join

/-- Empty ascriptions (HM-only or no surface bounds). -/
def ProgramBoundAnns.empty : ProgramBoundAnns := {}

/-! ### Checking ascriptions against synthesized bounds -/

/-- Synthesized `β` satisfies surface ascription `ann` under `Δ` (after elab of holes). -/
inductive MeetsAscription (Δ : List Constraint) : BoundInfo → BoundAnn → Prop where
  | solid {β ann β'} :
      BoundAnn.toBoundInfo? ann = some β' →
      Sub Δ β β' →
      MeetsAscription Δ β ann
  | elab {β ann β' Φ Φ'} :
      ElabAnn Φ ann β' Φ' →
      Sub Δ β β' →
      MeetsAscription Δ β ann

/-- Env of synthesized bound infos (from walking HasBounds under binders).
Same length/discipline as `BoundEnv`. -/
abbrev SynthBoundEnv := BoundEnv

/-- Every present binder ascription is met by the synthesized binder bounds. -/
def MeetsBinderAnns (Δ : List Constraint)
    (syn : SynthBoundEnv) (anns : ProgramBoundAnns) : Prop :=
  ∀ (i : Nat) (ann : BoundAnn),
    anns.binderAnns[i]? = some (some ann) →
      ∃ β : BoundInfo, syn[i]? = some β ∧ MeetsAscription Δ β ann

/-! ### Pipeline coverage contract -/

/-- Does this bound view require `BoundCovers` (List) vs HM exhaustiveness? -/
def BoundInfo.needsBoundCovers : BoundInfo → Bool
  | .list _ _ _ => true
  | _ => false

/-- BL-mode match safety side condition, parameterized by external HM exhaustiveness.

`hmExh brs` is intended to be `AllMatchesExhaustive` (or surface check) on the
match when bounds do not refine List coverage. Kept abstract so Bounds does not
import SurfaceBridge. -/
inductive MatchSafe
    (Δ : List Constraint)
    (hmExh : List (MatchPattern × Expr) → Prop) :
    BoundInfo → List (MatchPattern × Expr) → Prop where
  /-- List scrutinee bounds: use BoundCovers. -/
  | list {lo hi βe brs} :
      BoundCovers Δ (.list lo hi βe) brs →
      MatchSafe Δ hmExh (.list lo hi βe) brs
  /-- Non-List: fall back to ordinary exhaustiveness. -/
  | nonList {β brs} :
      BoundInfo.needsBoundCovers β = false →
      hmExh brs →
      MatchSafe Δ hmExh β brs

/-- Top-level BL-mode judgment sketch (empty path, closed program).

`hmExh` plugs in Core/Surface exhaustiveness for non-List matches.
Full progress composition remains a later theorem. -/
structure BoundProgramOK
    (ctors : CtorEnv)
    (hmExh : List (MatchPattern × Expr) → Prop)
    (e : Expr) (τ : Ty) (β : BoundInfo)
    (anns : ProgramBoundAnns) : Prop where
  hm : TypeOfElabHM ⟨[], ctors⟩ e τ
  bounds : HasBounds [] [] e τ β
  agrees : Agrees β τ
  /-- Body ascription, if any. -/
  body_ann :
      match anns.bodyAnn with
      | none => True
      | some ann => MeetsAscription [] β ann
  /-- If `e` is a match, coverage per `MatchSafe`; otherwise True.
  Nested matches: require a separate walk (algo/pipeline), not this top-level Prop.
  v1 demos may only check the outer match. -/
  match_ok :
      match e with
      | .match_ _ brs => MatchSafe [] hmExh β brs
      | _ => True

/-! ### P3.5b theorem statements (after sign-off) -/

theorem ElabCount.frontier_le {Φ a c Φ'} (h : ElabCount Φ a c Φ') : Φ ≤ Φ' := by
  cases h with
  | hole => omega
  | solid => omega

theorem ElabAnn.frontier_le {Φ ann β Φ'} (h : ElabAnn Φ ann β Φ') : Φ ≤ Φ' := by
  induction h with
  | prim => omega
  | bvar => omega
  | fvar => omega
  | arrow _ _ iha ihb => omega
  | list hlo hhi _ ihe =>
      have := ElabCount.frontier_le hlo
      have := ElabCount.frontier_le hhi
      omega
  | custom => omega

/-- After elaboration, β is a solid BoundInfo; agreement with τ is a pipeline
duty (erase produces ann aligned with τ). Stated for the solid-ascription path. -/
theorem MeetsAscription.sub {Δ β ann β'}
    (h : BoundAnn.toBoundInfo? ann = some β')
    (hs : Sub Δ β β') :
    MeetsAscription Δ β ann :=
  .solid h hs

theorem BoundInfo.needsBoundCovers_iff (β : BoundInfo) :
    BoundInfo.needsBoundCovers β = true ↔ ∃ lo hi e, β = .list lo hi e := by
  constructor
  · intro h
    cases β <;> simp [BoundInfo.needsBoundCovers] at h
    exact ⟨_, _, _, rfl⟩
  · intro ⟨lo, hi, e, he⟩
    subst he
    rfl


theorem MatchSafe.list_of_covers {Δ hmExh lo hi βe brs}
    (h : BoundCovers Δ (.list lo hi βe) brs) :
    MatchSafe Δ hmExh (.list lo hi βe) brs :=
  .list h

end FHM.Bounds
