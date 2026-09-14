import FHM.Bounds.Semantic
import FHM.Bounds.ScopedScheme

/-! # Solver-independent, variance-correct branch bounds merging

Upper candidates use interval union; lower candidates use interval intersection.
Arrow domains reverse that choice. Successful construction proves both required
semantic inclusions at every premise context. This is branch-join groundwork,
not a match checker or a claim of unrestricted BL principality.
-/

namespace FHM.Bounds.BranchMerge

inductive Mode where
  | upper
  | lower
  deriving DecidableEq, Repr

def Mode.flip : Mode → Mode
  | .upper => .lower
  | .lower => .upper

def lowerCount : Mode → Count → Count → Count
  | .upper => .min
  | .lower => .max

def upperCount : Mode → Count → Count → Count
  | .upper => .max
  | .lower => .min

mutual
inductive Combines : Mode → BoundsTy → BoundsTy → BoundsTy → Prop where
  | prim : Combines mode (.prim p) (.prim p) (.prim p)
  | fvar : Combines mode (.fvar i) (.fvar i) (.fvar i)
  | bvar : Combines mode (.bvar i) (.bvar i) (.bvar i)
  | arrow : Combines mode.flip a a' domain → Combines mode b b' result →
      Combines mode (.arrow a b) (.arrow a' b') (.arrow domain result)
  | list : Combines mode e e' elem →
      Combines mode (.list lo hi e) (.list lo' hi' e')
        (.list (lowerCount mode lo lo') (upperCount mode hi hi') elem)
  | custom : CombinesArgs mode as bs cs →
      Combines mode (.custom name as) (.custom name bs) (.custom name cs)

inductive CombinesArgs : Mode → List BoundsTy → List BoundsTy → List BoundsTy → Prop where
  | nil : CombinesArgs mode [] [] []
  | cons : Combines mode a b c → CombinesArgs mode as bs cs →
      CombinesArgs mode (a :: as) (b :: bs) (c :: cs)
end

def Inclusions (mode : Mode) (Δ : List Constraint) (a b c : BoundsTy) : Prop :=
  match mode with
  | .upper => SemanticSub Δ a c ∧ SemanticSub Δ b c
  | .lower => SemanticSub Δ c a ∧ SemanticSub Δ c b

def ArgInclusions (mode : Mode) (Δ : List Constraint) (as bs cs : List BoundsTy) : Prop :=
  match mode with
  | .upper => List.Forall₂ (SemanticSub Δ) as cs ∧ List.Forall₂ (SemanticSub Δ) bs cs
  | .lower => List.Forall₂ (SemanticSub Δ) cs as ∧ List.Forall₂ (SemanticSub Δ) cs bs

private theorem min_left (a b : ExtNat) : ExtNat.le (ExtNat.min a b) a := by
  cases a <;> cases b <;> simp [ExtNat.le, ExtNat.min]

private theorem min_right (a b : ExtNat) : ExtNat.le (ExtNat.min a b) b := by
  cases a <;> cases b <;> simp [ExtNat.le, ExtNat.min]

private theorem max_left (a b : ExtNat) : ExtNat.le a (ExtNat.max a b) := by
  cases a <;> cases b <;> simp [ExtNat.le, ExtNat.max]

private theorem max_right (a b : ExtNat) : ExtNat.le b (ExtNat.max a b) := by
  cases a <;> cases b <;> simp [ExtNat.le, ExtNat.max]

private theorem interval (Δ : List Constraint) (lo hi lo' hi' : Count)
    (hl : ∀ σ, ExtNat.le (lo'.eval σ) (lo.eval σ))
    (hh : ∀ σ, ExtNat.le (hi.eval σ) (hi'.eval σ)) :
    (Interval.subGoals Δ ⟨lo, hi⟩ ⟨lo', hi'⟩).Valid := by
  intro σ _ g hg
  simp [Interval.subGoals] at hg
  rcases hg with rfl | rfl
  · exact hl σ
  · exact hh σ

mutual
theorem Combines.sound {mode a b c} (h : Combines mode a b c) (Δ : List Constraint) :
    Inclusions mode Δ a b c := by
  cases h with
  | prim => cases mode <;> exact ⟨.prim, .prim⟩
  | fvar => cases mode <;> exact ⟨.fvar, .fvar⟩
  | bvar => cases mode <;> exact ⟨.bvar, .bvar⟩
  | arrow hd hr =>
      have hd := hd.sound Δ
      have hr := hr.sound Δ
      cases mode <;> exact ⟨.arrow hd.1 hr.1, .arrow hd.2 hr.2⟩
  | @list mode e e' elem lo hi lo' hi' he =>
      have hs := he.sound Δ
      cases mode with
      | upper =>
          exact ⟨.list (interval Δ lo hi (.min lo lo') (.max hi hi')
              (fun σ => min_left _ _) (fun σ => max_left _ _)) hs.1,
            .list (interval Δ lo' hi' (.min lo lo') (.max hi hi')
              (fun σ => min_right _ _) (fun σ => max_right _ _)) hs.2⟩
      | lower =>
          exact ⟨.list (interval Δ (.max lo lo') (.min hi hi') lo hi
              (fun σ => max_left _ _) (fun σ => min_left _ _)) hs.1,
            .list (interval Δ (.max lo lo') (.min hi hi') lo' hi'
              (fun σ => max_right _ _) (fun σ => min_right _ _)) hs.2⟩
  | custom hs =>
      have hs := hs.sound Δ
      cases mode <;> exact ⟨.custom hs.1, .custom hs.2⟩
termination_by sizeOf a + sizeOf b
decreasing_by all_goals simp_wf; omega

theorem CombinesArgs.sound {mode as bs cs} (h : CombinesArgs mode as bs cs) (Δ : List Constraint) :
    ArgInclusions mode Δ as bs cs := by
  cases h with
  | nil => cases mode <;> exact ⟨.nil, .nil⟩
  | cons hh ht =>
      have hh := hh.sound Δ
      have ht := ht.sound Δ
      cases mode <;> exact ⟨.cons hh.1 ht.1, .cons hh.2 ht.2⟩
termination_by sizeOf as + sizeOf bs
decreasing_by all_goals simp_wf; omega
end

mutual
theorem Combines.shape {mode a b c} (h : Combines mode a b c) :
    Synth.BoundsTy.toTy c = Synth.BoundsTy.toTy a ∧
    Synth.BoundsTy.toTy c = Synth.BoundsTy.toTy b := by
  cases h with
  | prim => exact ⟨rfl, rfl⟩
  | fvar => exact ⟨rfl, rfl⟩
  | bvar => exact ⟨rfl, rfl⟩
  | arrow hd hr =>
      have hd := hd.shape
      have hr := hr.shape
      exact ⟨by simp only [Synth.BoundsTy.toTy, hd.1, hr.1],
        by simp only [Synth.BoundsTy.toTy, hd.2, hr.2]⟩
  | list he =>
      have he := he.shape
      exact ⟨by simp only [Synth.BoundsTy.toTy, he.1],
        by simp only [Synth.BoundsTy.toTy, he.2]⟩
  | custom hs =>
      have hs := hs.shape
      exact ⟨by simp only [Synth.BoundsTy.toTy, hs.1],
        by simp only [Synth.BoundsTy.toTy, hs.2]⟩
termination_by sizeOf a + sizeOf b
decreasing_by all_goals simp_wf; omega

theorem CombinesArgs.shape {mode as bs cs} (h : CombinesArgs mode as bs cs) :
    cs.map Synth.BoundsTy.toTy = as.map Synth.BoundsTy.toTy ∧
    cs.map Synth.BoundsTy.toTy = bs.map Synth.BoundsTy.toTy := by
  cases h with
  | nil => exact ⟨rfl, rfl⟩
  | cons hh ht =>
      have hh := hh.shape
      have ht := ht.shape
      exact ⟨by simp only [List.map_cons, hh.1, ht.1],
        by simp only [List.map_cons, hh.2, ht.2]⟩
termination_by sizeOf as + sizeOf bs
decreasing_by all_goals simp_wf; omega
end

mutual
theorem Combines.scoped {mode a b c} (h : Combines mode a b c) :
    ∀ ids, ScopedScheme.BoundsScoped ids a → ScopedScheme.BoundsScoped ids b →
      ScopedScheme.BoundsScoped ids c := by
  cases h with
  | prim | fvar | bvar => intros; trivial
  | arrow hd hr =>
      intro ids ha hb
      exact ⟨hd.scoped ids ha.1 hb.1, hr.scoped ids ha.2 hb.2⟩
  | list he =>
      intro ids ha hb
      have hElem := he.scoped ids ha.2.2 hb.2.2
      cases mode <;> exact ⟨⟨ha.1, hb.1⟩, ⟨⟨ha.2.1, hb.2.1⟩, hElem⟩⟩
  | custom hs => exact hs.scoped
termination_by sizeOf a + sizeOf b
decreasing_by all_goals simp_wf; omega

theorem CombinesArgs.scoped {mode as bs cs} (h : CombinesArgs mode as bs cs) :
    ∀ ids, ScopedScheme.BoundsListScoped ids as → ScopedScheme.BoundsListScoped ids bs →
      ScopedScheme.BoundsListScoped ids cs := by
  cases h with
  | nil => intros; trivial
  | cons hh ht =>
      intro ids ha hb
      exact ⟨hh.scoped ids ha.1 hb.1, ht.scoped ids ha.2 hb.2⟩
termination_by sizeOf as + sizeOf bs
decreasing_by all_goals simp_wf; omega
end

mutual
def combine (mode : Mode) (a b : BoundsTy) : Except String (Σ c, PLift (Combines mode a b c)) := do
  match a, b with
  | .prim p, .prim q =>
      if h : p = q then pure ⟨.prim p, ⟨by subst q; exact .prim⟩⟩
      else throw "bounds: branch primitive shapes disagree"
  | .fvar i, .fvar j =>
      if h : i = j then pure ⟨.fvar i, ⟨by subst j; exact .fvar⟩⟩
      else throw "bounds: branch free HM identities disagree"
  | .bvar i, .bvar j =>
      if h : i = j then pure ⟨.bvar i, ⟨by subst j; exact .bvar⟩⟩
      else throw "bounds: branch bound HM identities disagree"
  | .arrow a b, .arrow a' b' =>
      let ⟨domain, hd⟩ ← combine mode.flip a a'
      let ⟨result, hr⟩ ← combine mode b b'
      pure ⟨.arrow domain result, ⟨.arrow hd.down hr.down⟩⟩
  | .list lo hi e, .list lo' hi' e' =>
      let ⟨elem, he⟩ ← combine mode e e'
      pure ⟨.list (lowerCount mode lo lo') (upperCount mode hi hi') elem, ⟨.list he.down⟩⟩
  | .custom name as, .custom other bs =>
      if h : name = other then
        let ⟨cs, hs⟩ ← combineArgs mode as bs
        pure ⟨.custom name cs, ⟨by subst other; exact .custom hs.down⟩⟩
      else throw "bounds: branch constructor shapes disagree"
  | _, _ => throw "bounds: branch shapes disagree"
termination_by sizeOf a + sizeOf b

def combineArgs (mode : Mode) (as bs : List BoundsTy) :
    Except String (Σ cs, PLift (CombinesArgs mode as bs cs)) := do
  match as, bs with
  | [], [] => pure ⟨[], ⟨.nil⟩⟩
  | a :: as, b :: bs =>
      let ⟨c, hc⟩ ← combine mode a b
      let ⟨cs, hs⟩ ← combineArgs mode as bs
      pure ⟨c :: cs, ⟨.cons hc.down hs.down⟩⟩
  | _, _ => throw "bounds: branch constructor arities disagree"
termination_by sizeOf as + sizeOf bs
end

#print axioms Combines.sound
#print axioms Combines.shape
#print axioms Combines.scoped
#print axioms combine

end FHM.Bounds.BranchMerge
