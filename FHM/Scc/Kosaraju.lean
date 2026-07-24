import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Sort
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Nodup

/-! # Kosaraju SCC (abstract digraph)

Executable Kosaraju on a finite digraph `Digraph α`, with declarative
`Reach` / `Mutual` / `ValidSccPartition`. Adequacy: `kosaraju_sound` /
`ValidSccPartition.eqv_mutual` (axiom-clean aside from standard classical axioms).

Wired into `SurfaceBridge.sccGroups` via `bindDigraph` / `sccIndexSets`
(`α := Fin binds.length`, components mapped through `Fin.val`, Kahn on the
condensation).

Design notes:
- Vertices are `α` with `[Fintype α] [DecidableEq α]` (no explicit `verts` list).
- Edges are `succ : α → Finset α` (AbstractWalk-style).
- Executable DFS needs `[LinearOrder α]` so we can `Finset.sort` (computable);
  `Finset.toList` is noncomputable. Spec theorems do **not** need `LinearOrder`.
- No topo here — condensation ordering stays with Kahn in SurfaceBridge.
-/

namespace Scc

variable {α : Type} [Fintype α] [DecidableEq α]

/-- Finite directed graph: every `α` is a vertex; successors are a `Finset`. -/
structure Digraph (α : Type) [Fintype α] [DecidableEq α] where
  succ : α → Finset α

/-- Transpose: reverse every edge. -/
def Digraph.transpose (g : Digraph α) : Digraph α where
  succ := fun v => Finset.univ.filter (fun u => v ∈ g.succ u)

/-- Spec-level reachability (mirrors `SurfaceBridge.DepReach`). -/
inductive Reach (g : Digraph α) : α → α → Prop
  | refl {a} : Reach g a a
  | tail {a b c} : b ∈ g.succ a → Reach g b c → Reach g a c

/-- Mutual reachability = same SCC class. -/
def Mutual (g : Digraph α) (a b : α) : Prop :=
  Reach g a b ∧ Reach g b a

/-- Non-deterministic SCC partition of `g` (no topo).

`flatten_nodup` + `cover` ⇒ the components partition `α` up to intra-component
order and order among incomparable SCCs. -/
structure ValidSccPartition (g : Digraph α) (comps : List (List α)) : Prop where
  nonempty : ∀ c ∈ comps, c ≠ []
  flatten_nodup : comps.flatten.Nodup
  cover : ∀ v : α, ∃ c ∈ comps, v ∈ c
  sameScc : ∀ c ∈ comps, ∀ a ∈ c, ∀ b ∈ c, Mutual g a b
  maxScc : ∀ a b : α, Mutual g a b → ∃ c ∈ comps, a ∈ c ∧ b ∈ c

theorem Reach_trans {g : Digraph α} {a b c : α}
    (hab : Reach g a b) (hbc : Reach g b c) : Reach g a c := by
  induction hab with
  | refl => exact hbc
  | tail hab rbc ih => exact Reach.tail hab (ih hbc)

private theorem Reach_transpose_forward {g : Digraph α} {a b : α} :
    Reach g.transpose a b → Reach g b a := by
  intro h
  induction h with
  | refl => exact Reach.refl
  | tail hab rbc ih =>
    rw [Digraph.transpose] at hab
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hab
    exact Reach_trans ih (Reach.tail hab Reach.refl)

private theorem Reach_transpose_backward {g : Digraph α} {a b : α} :
    Reach g b a → Reach g.transpose a b := by
  intro h
  induction h with
  | refl => exact Reach.refl
  | tail hab rbc ih =>
    refine Reach_trans ih (Reach.tail ?_ Reach.refl)
    simp [Digraph.transpose, Finset.mem_filter, Finset.mem_univ, hab]

theorem Reach_transpose {g : Digraph α} {a b : α} :
    Reach g.transpose a b ↔ Reach g b a := by
  constructor
  · exact Reach_transpose_forward
  · exact Reach_transpose_backward

/-- Any two valid partitions induce the same mutual-reachability relation. -/
theorem ValidSccPartition.eqv_mutual
    {g : Digraph α} {comps₁ comps₂ : List (List α)}
    (h₁ : ValidSccPartition g comps₁) (h₂ : ValidSccPartition g comps₂)
    {a b : α} :
    (∃ c ∈ comps₁, a ∈ c ∧ b ∈ c) ↔
      (∃ c ∈ comps₂, a ∈ c ∧ b ∈ c) := by
  constructor
  · intro ⟨c, hc, ha, hb⟩
    exact h₂.maxScc a b (h₁.sameScc c hc a ha b hb)
  · intro ⟨c, hc, ha, hb⟩
    exact h₁.maxScc a b (h₂.sameScc c hc a ha b hb)

/-! ## Executable Kosaraju (fuelled, total)

`LinearOrder` is required only so successor / universe enumeration is computable
via `Finset.sort` (needed for `#guard` / runtime). Proofs about `Reach` do not
use the order.

Pass 1: DFS, push on finish → `finish` stack (last finished at head).
Pass 2: DFS on transpose, seeds = `finish` head-first → components. -/

section executable
variable [LinearOrder α]

/-- Computable listing of a finset (sorted). -/
def finsetList (s : Finset α) : List α :=
  s.sort (· ≤ ·)

/-- DFS for finish order: mark on entry, push `v` on exit. -/
def dfsFinish (g : Digraph α) : Nat → Finset α → List α → α → Finset α × List α
  | 0, visited, finish, _ => (visited, finish)
  | fuel + 1, visited, finish, v =>
    if v ∈ visited then (visited, finish)
    else
      let visited := insert v visited
      let (visited, finish) :=
        (finsetList (g.succ v)).foldl
          (fun ⟨vis, fin⟩ u => dfsFinish g fuel vis fin u)
          (visited, finish)
      (visited, v :: finish)

/-- First-pass outer loop (named for induction). -/
private def finishOrderGo (g : Digraph α) : Nat → Finset α → List α → List α
  | 0, _, finish => finish
  | fuel + 1, visited, finish =>
    match (finsetList (Finset.univ.filter (fun v => v ∉ visited))).head? with
    | none => finish
    | some v =>
      let (visited, finish) := dfsFinish g (Fintype.card α) visited finish v
      finishOrderGo g fuel visited finish

/-- First pass: finish stack over all vertices. -/
def finishOrder (g : Digraph α) : List α :=
  finishOrderGo g (Fintype.card α + 1) ∅ []

/-- Second-pass DFS: collect one component (mark + accumulate on entry). -/
def dfsCollect (g : Digraph α) : Nat → Finset α → List α → α → Finset α × List α
  | 0, visited, comp, _ => (visited, comp)
  | fuel + 1, visited, comp, v =>
    if v ∈ visited then (visited, comp)
    else
      let visited := insert v visited
      let comp := v :: comp
      (finsetList (g.succ v)).foldl
        (fun ⟨vis, c⟩ u => dfsCollect g fuel vis c u)
        (visited, comp)

/-- Second-pass outer loop (named for induction). -/
private def kosarajuGo (g : Digraph α) : Nat → Finset α → List α → List (List α) → List (List α)
  | 0, _, _, comps => comps
  | _fuel + 1, _visited, [], comps => comps
  | fuel + 1, visited, v :: vs, comps =>
    if v ∈ visited then kosarajuGo g fuel visited vs comps
    else
      let (visited, comp) := dfsCollect g.transpose (Fintype.card α) visited [] v
      kosarajuGo g fuel visited vs (comps ++ [comp])

/-- Kosaraju SCC partition. Component order is discovery order of pass 2 —
    **not** a condensation topo (Kahn handles that downstream). -/
def kosaraju (g : Digraph α) : List (List α) :=
  kosarajuGo g (Fintype.card α + 1) ∅ (finishOrder g) []

/-! ### Proof helpers -/

omit [Fintype α] [DecidableEq α] in
private theorem finsetList_mem {s : Finset α} {x : α} :
    x ∈ finsetList s ↔ x ∈ s := by
  simp [finsetList, Finset.mem_sort]

private theorem dfsFinish_visited_mono {g : Digraph α} :
    ∀ fuel visited finish v,
      visited ⊆ (dfsFinish g fuel visited finish v).1 := by
  intro fuel
  induction fuel with
  | zero => intro visited finish v; simp [dfsFinish]
  | succ fuel ih =>
    intro visited finish v
    simp only [dfsFinish]
    split_ifs with hv
    · exact Finset.Subset.refl _
    · -- After foldl, visited' ⊇ insert v visited ⊇ visited
      have fold_mono :
          ∀ (l : List α) (acc : Finset α × List α),
            acc.1 ⊆ (l.foldl (fun ⟨vis, fin⟩ u => dfsFinish g fuel vis fin u) acc).1 := by
        intro l acc
        induction l generalizing acc with
        | nil => exact Finset.Subset.refl _
        | cons u us ihl =>
          simp only [List.foldl]
          exact Finset.Subset.trans (ih acc.1 acc.2 u) (ihl _)
      exact Finset.Subset.trans (Finset.subset_insert v visited)
        (fold_mono (finsetList (g.succ v)) (insert v visited, finish))

private theorem dfsFinish_marks_root {g : Digraph α} :
    ∀ fuel visited finish v, 0 < fuel → v ∉ visited →
      v ∈ (dfsFinish g fuel visited finish v).1 := by
  intro fuel visited finish v hf hnv
  cases fuel with
  | zero => exact (Nat.not_lt_zero 0 hf).elim
  | succ fuel =>
    simp only [dfsFinish, hnv, ite_false]
    have fold_mono :
        ∀ (l : List α) (acc : Finset α × List α),
          acc.1 ⊆ (l.foldl (fun ⟨vis, fin⟩ u => dfsFinish g fuel vis fin u) acc).1 := by
      intro l acc
      induction l generalizing acc with
      | nil => exact Finset.Subset.refl _
      | cons u us ihl =>
        simp only [List.foldl]
        exact Finset.Subset.trans (dfsFinish_visited_mono fuel acc.1 acc.2 u) (ihl _)
    exact fold_mono (finsetList (g.succ v)) (insert v visited, finish)
      (Finset.mem_insert_self v visited)

private theorem dfsCollect_visited_mono {g : Digraph α} :
    ∀ fuel visited comp v,
      visited ⊆ (dfsCollect g fuel visited comp v).1 := by
  intro fuel
  induction fuel with
  | zero => intro visited comp v; simp [dfsCollect]
  | succ fuel ih =>
    intro visited comp v
    simp only [dfsCollect]
    split_ifs with hv
    · exact Finset.Subset.refl _
    · have fold_mono :
          ∀ (l : List α) (acc : Finset α × List α),
            acc.1 ⊆ (l.foldl (fun ⟨vis, c⟩ u => dfsCollect g fuel vis c u) acc).1 := by
        intro l acc
        induction l generalizing acc with
        | nil => exact Finset.Subset.refl _
        | cons u us ihl =>
          simp only [List.foldl]
          exact Finset.Subset.trans (ih acc.1 acc.2 u) (ihl _)
      exact Finset.Subset.trans (Finset.subset_insert v visited)
        (fold_mono (finsetList (g.succ v)) (insert v visited, v :: comp))

/-- Existing finish entries survive `dfsFinish`. -/
private theorem dfsFinish_preserves_finish_mem {g : Digraph α} :
    ∀ fuel visited finish v x,
      x ∈ finish → x ∈ (dfsFinish g fuel visited finish v).2 := by
  intro fuel
  induction fuel with
  | zero => intro visited finish v x hx; simp [dfsFinish]; exact hx
  | succ fuel ih =>
    intro visited finish v x hx
    simp only [dfsFinish]
    split_ifs with hv
    · exact hx
    · have fold_pres :
          ∀ (l : List α) (acc : Finset α × List α),
            x ∈ acc.2 →
              x ∈ (l.foldl (fun ⟨vis, fin⟩ u => dfsFinish g fuel vis fin u) acc).2 := by
        intro l acc hx'
        induction l generalizing acc with
        | nil => simpa using hx'
        | cons u us ihl =>
          simp only [List.foldl]
          exact ihl _ (ih acc.1 acc.2 u x hx')
      exact List.mem_cons_of_mem v
        (fold_pres (finsetList (g.succ v)) (insert v visited, finish) hx)

/-- Unvisited root with positive fuel is pushed onto the finish stack. -/
private theorem dfsFinish_root_mem_finish {g : Digraph α} :
    ∀ fuel visited finish root, 0 < fuel → root ∉ visited →
      root ∈ (dfsFinish g fuel visited finish root).2 := by
  intro fuel visited finish root hf hroot
  cases fuel with
  | zero => exact (Nat.not_lt_zero 0 hf).elim
  | succ fuel =>
    simp only [dfsFinish, hroot, ite_false]
    exact List.mem_cons_self

/-- Vertices newly added to finish are among those newly marked visited. -/
private theorem dfsFinish_finish_mem_visited {g : Digraph α} :
    ∀ fuel visited finish v x,
      x ∈ (dfsFinish g fuel visited finish v).2 →
        x ∈ finish ∨ x ∈ (dfsFinish g fuel visited finish v).1 := by
  intro fuel
  induction fuel with
  | zero =>
    intro visited finish v x hx
    simp only [dfsFinish] at hx
    exact Or.inl hx
  | succ fuel ih =>
    intro visited finish v x hx
    by_cases hv : v ∈ visited
    · simp only [dfsFinish, hv, ite_true] at hx ⊢
      exact Or.inl hx
    · simp only [dfsFinish, hv, ite_false] at hx ⊢
      have fold_vis_mono :
          ∀ (l : List α) (acc : Finset α × List α),
            acc.1 ⊆ (l.foldl (fun ⟨vis, fin⟩ u => dfsFinish g fuel vis fin u) acc).1 := by
        intro l acc
        induction l generalizing acc with
        | nil => exact Finset.Subset.refl _
        | cons u us ihl =>
          simp only [List.foldl]
          exact Finset.Subset.trans (dfsFinish_visited_mono fuel acc.1 acc.2 u) (ihl _)
      have fold_mem :
          ∀ (l : List α) (acc : Finset α × List α),
            x ∈ (l.foldl (fun ⟨vis, fin⟩ u => dfsFinish g fuel vis fin u) acc).2 →
              x ∈ acc.2 ∨
                x ∈ (l.foldl (fun ⟨vis, fin⟩ u => dfsFinish g fuel vis fin u) acc).1 := by
        intro l acc hx'
        induction l generalizing acc with
        | nil => exact Or.inl hx'
        | cons u us ihl =>
          simp only [List.foldl] at hx' ⊢
          rcases ihl (dfsFinish g fuel acc.1 acc.2 u) hx' with hInStepFin | hInRestVis
          · rcases ih acc.1 acc.2 u x hInStepFin with hInAcc | hInStepVis
            · exact Or.inl hInAcc
            · exact Or.inr
                (fold_vis_mono us (dfsFinish g fuel acc.1 acc.2 u) hInStepVis)
          · exact Or.inr hInRestVis
      simp only [List.mem_cons] at hx
      rcases hx with hxv | hx
      · subst hxv
        exact Or.inr (fold_vis_mono (finsetList (g.succ x)) (insert x visited, finish)
          (Finset.mem_insert_self x visited))
      · exact fold_mem (finsetList (g.succ v)) (insert v visited, finish) hx

private theorem dfsCollect_foldl_preserves_mem {g : Digraph α} {fuel : Nat}
    (pres : ∀ (visited : Finset α) (comp : List α) (u x : α),
      x ∈ comp → x ∈ (dfsCollect g fuel visited comp u).2)
    (x : α) :
    ∀ (l : List α) (acc : Finset α × List α),
      x ∈ acc.2 → x ∈ (l.foldl (fun ⟨vis, c⟩ u => dfsCollect g fuel vis c u) acc).2 := by
  intro l acc hx
  induction l generalizing acc with
  | nil => simpa using hx
  | cons u us ih =>
    simp only [List.foldl]
    exact ih (dfsCollect g fuel acc.1 acc.2 u) (pres acc.1 acc.2 u x hx)

private theorem dfsCollect_preserves_mem {g : Digraph α} :
    ∀ fuel visited comp u x,
      x ∈ comp → x ∈ (dfsCollect g fuel visited comp u).2 := by
  intro fuel
  induction fuel with
  | zero => intro visited comp u x hx; simp [dfsCollect]; exact hx
  | succ fuel ih =>
    intro visited comp u x hx
    simp only [dfsCollect]
    split_ifs with hv
    · exact hx
    · exact dfsCollect_foldl_preserves_mem ih x (finsetList (g.succ u))
        (insert u visited, u :: comp) (List.mem_cons_of_mem u hx)

private theorem dfsCollect_unvisited_mem_comp {g : Digraph α} :
    ∀ fuel visited comp root, root ∉ visited →
      root ∈ (dfsCollect g (fuel + 1) visited comp root).2 := by
  intro fuel visited comp root hroot
  have pres (visited comp u x : _) (hx : x ∈ comp) :
      x ∈ (dfsCollect g fuel visited comp u).2 :=
    dfsCollect_preserves_mem (g := g) fuel visited comp u x hx
  simp only [dfsCollect, hroot, ite_false]
  exact dfsCollect_foldl_preserves_mem pres root (finsetList (g.succ root))
    (insert root visited, root :: comp) List.mem_cons_self

private theorem dfsCollect_root_mem_pos {g : Digraph α} :
    ∀ (fuel : Nat) visited comp root, 0 < fuel → root ∉ visited →
      root ∈ (dfsCollect g fuel visited comp root).2 := by
  intro fuel visited comp root hf hroot
  cases fuel with
  | zero => exact (Nat.not_lt_zero 0 hf).elim
  | succ fuel => exact dfsCollect_unvisited_mem_comp fuel visited comp root hroot

/-- New component members produced by `dfsCollect` are reachable from the root. -/
private theorem dfsCollect_mem_reach {g : Digraph α} :
    ∀ fuel visited comp root w,
      w ∈ (dfsCollect g fuel visited comp root).2 →
        w ∈ comp ∨ Reach g root w := by
  intro fuel
  induction fuel with
  | zero =>
    intro visited comp root w hw
    simp only [dfsCollect] at hw
    exact Or.inl hw
  | succ fuel ih =>
    intro visited comp root w hw
    by_cases hroot : root ∈ visited
    · simp only [dfsCollect, hroot, ite_true] at hw
      exact Or.inl hw
    · simp only [dfsCollect, hroot, ite_false] at hw
      -- Acc starts as `root :: comp`; fold over successors of root.
      have fold_mem :
          ∀ (l : List α) (acc : Finset α × List α),
            (∀ x ∈ acc.2, x ∈ comp ∨ Reach g root x) →
            (∀ u ∈ l, Reach g root u) →
            w ∈ (l.foldl (fun ⟨vis, c⟩ u => dfsCollect g fuel vis c u) acc).2 →
              w ∈ comp ∨ Reach g root w := by
        intro l acc hacc hl hw'
        induction l generalizing acc with
        | nil =>
          exact hacc w hw'
        | cons u us ihl =>
          simp only [List.foldl] at hw'
          have hu : Reach g root u := hl u List.mem_cons_self
          refine ihl (dfsCollect g fuel acc.1 acc.2 u) ?_ ?_ hw'
          · intro x hx
            rcases ih acc.1 acc.2 u x hx with hxAcc | hxReach
            · exact hacc x hxAcc
            · exact Or.inr (Reach_trans hu hxReach)
          · intro v hv
            exact hl v (List.mem_cons_of_mem u hv)
      refine fold_mem (finsetList (g.succ root)) (insert root visited, root :: comp) ?_ ?_ hw
      · intro x hx
        simp only [List.mem_cons] at hx
        rcases hx with rfl | hx
        · exact Or.inr Reach.refl
        · exact Or.inl hx
      · intro u hu
        have : u ∈ g.succ root := finsetList_mem.mp hu
        exact Reach.tail this Reach.refl

/-- Every member of the output comp is in the output visited set. -/
private theorem dfsCollect_comp_subset_visited {g : Digraph α} :
    ∀ fuel visited comp root,
      (∀ x ∈ comp, x ∈ visited) →
      ∀ w ∈ (dfsCollect g fuel visited comp root).2,
        w ∈ (dfsCollect g fuel visited comp root).1 := by
  intro fuel
  induction fuel with
  | zero =>
    intro visited comp root hcomp w hw
    simp only [dfsCollect] at hw ⊢
    exact hcomp w hw
  | succ fuel ih =>
    intro visited comp root hcomp w hw
    by_cases hroot : root ∈ visited
    · simp only [dfsCollect, hroot, ite_true] at hw ⊢
      exact hcomp w hw
    · simp only [dfsCollect, hroot, ite_false] at hw ⊢
      have fold_prop :
          ∀ (l : List α) (acc : Finset α × List α),
            (∀ x ∈ acc.2, x ∈ acc.1) →
            ∀ w, w ∈ (l.foldl (fun ⟨vis, c⟩ u => dfsCollect g fuel vis c u) acc).2 →
              w ∈ (l.foldl (fun ⟨vis, c⟩ u => dfsCollect g fuel vis c u) acc).1 := by
        intro l acc
        induction l generalizing acc with
        | nil =>
          intro hacc w hw'
          exact hacc w hw'
        | cons u us ihl =>
          intro hacc w hw'
          simp only [List.foldl] at hw' ⊢
          exact ihl (dfsCollect g fuel acc.1 acc.2 u) (ih acc.1 acc.2 u hacc) w hw'
      refine fold_prop (finsetList (g.succ root)) (insert root visited, root :: comp) ?_ w hw
      intro x hx
      simp only [List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact Finset.mem_insert_self x visited
      · exact Finset.mem_insert_of_mem (hcomp x hx)

/-- New members of the component were not in the prior visited set. -/
private theorem dfsCollect_new_not_visited {g : Digraph α} :
    ∀ fuel visited comp root,
      (∀ x ∈ comp, x ∈ visited) →
      ∀ w ∈ (dfsCollect g fuel visited comp root).2,
        w ∈ visited → w ∈ comp := by
  intro fuel
  induction fuel with
  | zero =>
    intro visited comp root _hcomp w hw _hvis
    simpa [dfsCollect] using hw
  | succ fuel ih =>
    intro visited comp root hcomp w hw hvis
    by_cases hroot : root ∈ visited
    · simpa [dfsCollect, hroot] using hw
    · simp only [dfsCollect, hroot, ite_false] at hw
      have fold_prop :
          ∀ (l : List α) (acc : Finset α × List α),
            (∀ x ∈ acc.2, x ∈ acc.1) →
            (∀ x ∈ acc.2, x ∈ visited → x ∈ comp) →
            visited ⊆ acc.1 →
            w ∈ (l.foldl (fun ⟨vis, c⟩ u => dfsCollect g fuel vis c u) acc).2 →
            w ∈ visited → w ∈ comp := by
        intro l acc
        induction l generalizing acc with
        | nil =>
          intro _hacc haccOld _hsub hw' hvis'
          exact haccOld w hw' hvis'
        | cons u us ihl =>
          intro hacc haccOld hsub hw' hvis'
          simp only [List.foldl] at hw'
          refine ihl (dfsCollect g fuel acc.1 acc.2 u) ?_ ?_ ?_ hw' hvis'
          · exact fun x hx =>
              dfsCollect_comp_subset_visited fuel acc.1 acc.2 u hacc x hx
          · intro x hx hxOld
            have hxAcc : x ∈ acc.2 :=
              ih acc.1 acc.2 u hacc x hx (hsub hxOld)
            exact haccOld x hxAcc hxOld
          · exact Finset.Subset.trans hsub (dfsCollect_visited_mono fuel acc.1 acc.2 u)
      refine fold_prop (finsetList (g.succ root)) (insert root visited, root :: comp) ?_ ?_
        (Finset.subset_insert root visited) hw hvis
      · intro x hx
        simp only [List.mem_cons] at hx
        rcases hx with rfl | hx
        · exact Finset.mem_insert_self x visited
        · exact Finset.mem_insert_of_mem (hcomp x hx)
      · intro x hx hxOld
        simp only [List.mem_cons] at hx
        rcases hx with hxv | hx
        · subst hxv; exact (hroot hxOld).elim
        · exact hx

/-- `dfsCollect` preserves Nodup under the visited⊇comp invariant. -/
private theorem dfsCollect_nodup {g : Digraph α} :
    ∀ fuel visited comp root,
      (∀ x ∈ comp, x ∈ visited) →
      comp.Nodup →
      (dfsCollect g fuel visited comp root).2.Nodup := by
  intro fuel
  induction fuel with
  | zero =>
    intro visited comp root _hcomp hnd
    simpa [dfsCollect] using hnd
  | succ fuel ih =>
    intro visited comp root hcomp hnd
    by_cases hroot : root ∈ visited
    · simpa [dfsCollect, hroot] using hnd
    · simp only [dfsCollect, hroot, ite_false]
      have hroot_not_comp : root ∉ comp := fun hc => hroot (hcomp root hc)
      have fold_nd :
          ∀ (l : List α) (acc : Finset α × List α),
            (∀ x ∈ acc.2, x ∈ acc.1) →
            acc.2.Nodup →
            (l.foldl (fun ⟨vis, c⟩ u => dfsCollect g fuel vis c u) acc).2.Nodup := by
        intro l acc
        induction l generalizing acc with
        | nil =>
          intro _hacc hnd'; exact hnd'
        | cons u us ihl =>
          intro hacc hnd'
          simp only [List.foldl]
          exact ihl (dfsCollect g fuel acc.1 acc.2 u)
            (fun x hx => dfsCollect_comp_subset_visited fuel acc.1 acc.2 u hacc x hx)
            (ih acc.1 acc.2 u hacc hnd')
      exact fold_nd (finsetList (g.succ root)) (insert root visited, root :: comp)
        (fun x hx => by
          simp only [List.mem_cons] at hx
          rcases hx with rfl | hx
          · exact Finset.mem_insert_self x visited
          · exact Finset.mem_insert_of_mem (hcomp x hx))
        (List.Nodup.cons hroot_not_comp hnd)

/-- Fresh collect from `[]`: Nodup, disjoint from prior visited, subset of result visited. -/
private theorem dfsCollect_fresh_props {g : Digraph α}
    (fuel : Nat) (visited : Finset α) (root : α) :
    (dfsCollect g fuel visited [] root).2.Nodup ∧
      (∀ w ∈ (dfsCollect g fuel visited [] root).2, w ∉ visited) ∧
      (∀ w ∈ (dfsCollect g fuel visited [] root).2,
        w ∈ (dfsCollect g fuel visited [] root).1) := by
  refine ⟨?_, ?_, ?_⟩
  · exact dfsCollect_nodup fuel visited [] root (by intro x hx; cases hx) List.nodup_nil
  · intro w hw hvis
    have : w ∈ ([] : List α) :=
      dfsCollect_new_not_visited fuel visited [] root (by intro x hx; cases hx) w hw hvis
    cases this
  · exact dfsCollect_comp_subset_visited fuel visited [] root (by intro x hx; cases hx)

/-- Output visited is covered by prior visited union the output component. -/
private theorem dfsCollect_visited_subset_union {g : Digraph α} :
    ∀ fuel visited comp root,
      (∀ x ∈ comp, x ∈ visited) →
      ∀ x ∈ (dfsCollect g fuel visited comp root).1,
        x ∈ visited ∨ x ∈ (dfsCollect g fuel visited comp root).2 := by
  intro fuel
  induction fuel with
  | zero =>
    intro visited comp root hcomp x hx
    simp only [dfsCollect] at hx ⊢
    exact Or.inl hx
  | succ fuel ih =>
    intro visited comp root hcomp x hx
    by_cases hroot : root ∈ visited
    · simp only [dfsCollect, hroot, ite_true] at hx ⊢
      exact Or.inl hx
    · simp only [dfsCollect, hroot, ite_false] at hx ⊢
      have fold_prop :
          ∀ (l : List α) (acc : Finset α × List α),
            (∀ y ∈ acc.2, y ∈ acc.1) →
            (∀ y ∈ acc.1, y ∈ visited ∨ y ∈ acc.2) →
            ∀ y ∈ (l.foldl (fun ⟨vis, c⟩ u => dfsCollect g fuel vis c u) acc).1,
              y ∈ visited ∨
                y ∈ (l.foldl (fun ⟨vis, c⟩ u => dfsCollect g fuel vis c u) acc).2 := by
        intro l acc
        induction l generalizing acc with
        | nil =>
          intro _hacc haccUnion y hy
          exact haccUnion y hy
        | cons u us ihl =>
          intro hacc haccUnion y hy
          simp only [List.foldl] at hy ⊢
          refine ihl (dfsCollect g fuel acc.1 acc.2 u)
            (fun z hz => dfsCollect_comp_subset_visited fuel acc.1 acc.2 u hacc z hz)
            ?_ y hy
          intro z hz
          rcases ih acc.1 acc.2 u hacc z hz with hzAcc | hzComp
          · rcases haccUnion z hzAcc with hzVis | hzInAcc
            · exact Or.inl hzVis
            · exact Or.inr
                (dfsCollect_preserves_mem fuel acc.1 acc.2 u z hzInAcc)
          · exact Or.inr hzComp
      refine fold_prop (finsetList (g.succ root)) (insert root visited, root :: comp) ?_ ?_ x hx
      · intro y hy
        simp only [List.mem_cons] at hy
        rcases hy with rfl | hy
        · exact Finset.mem_insert_self y visited
        · exact Finset.mem_insert_of_mem (hcomp y hy)
      · intro y hy
        simp only [Finset.mem_insert] at hy
        rcases hy with rfl | hy
        · exact Or.inr List.mem_cons_self
        · exact Or.inl hy

private theorem dfsCollect_fresh_visited_union {g : Digraph α}
    (fuel : Nat) (visited : Finset α) (root : α) :
    ∀ x ∈ (dfsCollect g fuel visited [] root).1,
      x ∈ visited ∨ x ∈ (dfsCollect g fuel visited [] root).2 :=
  dfsCollect_visited_subset_union fuel visited [] root (by intro x hx; cases hx)

/-- `kosarajuGo` preserves flatten-Nodup when visited covers prior flatten and new comps are fresh. -/
private theorem kosarajuGo_flatten_nodup {g : Digraph α} :
    ∀ fuel visited finish comps,
      comps.flatten.Nodup →
      (∀ x ∈ comps.flatten, x ∈ visited) →
      (kosarajuGo g fuel visited finish comps).flatten.Nodup := by
  intro fuel
  induction fuel with
  | zero =>
    intro visited finish comps hnd _hsub
    simpa [kosarajuGo] using hnd
  | succ fuel ih =>
    intro visited finish comps hnd hsub
    cases finish with
    | nil => simpa [kosarajuGo] using hnd
    | cons seed vs =>
      by_cases hseed : seed ∈ visited
      · simpa [kosarajuGo, hseed] using ih visited vs comps hnd hsub
      · let step := dfsCollect g.transpose (Fintype.card α) visited [] seed
        let visited' := step.1
        let comp := step.2
        have hfresh := dfsCollect_fresh_props (g := g.transpose) (Fintype.card α) visited seed
        have hnd' : (comps ++ [comp]).flatten.Nodup := by
          simp only [List.flatten_append, List.flatten_cons, List.flatten_nil, List.append_nil]
          refine List.Nodup.append hnd hfresh.1 ?_
          intro x hx hxcomp
          exact (hfresh.2.1 x hxcomp) (hsub x hx)
        have hsub' : ∀ x ∈ (comps ++ [comp]).flatten, x ∈ visited' := by
          intro x hx
          simp only [List.flatten_append, List.flatten_cons, List.flatten_nil,
            List.append_nil, List.mem_append] at hx
          rcases hx with hx | hx
          · exact dfsCollect_visited_mono (Fintype.card α) visited [] seed (hsub x hx)
          · exact hfresh.2.2 x hx
        simpa [kosarajuGo, hseed] using
          ih visited' vs (comps ++ [comp]) hnd' hsub'

theorem kosaraju_flatten_nodup (g : Digraph α) :
    (kosaraju g).flatten.Nodup := by
  simpa [kosaraju] using
    kosarajuGo_flatten_nodup (Fintype.card α + 1) ∅ (finishOrder g) []
      (by simp) (by intro x hx; cases hx)

/-- Newly marked vertices appear on the finish stack. -/
private theorem dfsFinish_new_visited_mem_finish {g : Digraph α} :
    ∀ fuel visited finish v x,
      x ∉ visited →
      x ∈ (dfsFinish g fuel visited finish v).1 →
      x ∈ (dfsFinish g fuel visited finish v).2 := by
  intro fuel
  induction fuel with
  | zero =>
    intro visited finish v x hnv hx
    simp only [dfsFinish] at hx
    exact (hnv hx).elim
  | succ fuel ih =>
    intro visited finish v x hnv hx
    by_cases hv : v ∈ visited
    · simp only [dfsFinish, hv, ite_true] at hx
      exact (hnv hx).elim
    · simp only [dfsFinish, hv, ite_false] at hx ⊢
      have fold_pres_fin :
          ∀ (l : List α) (acc : Finset α × List α),
            x ∈ acc.2 →
            x ∈ (l.foldl (fun ⟨vis, fin⟩ u => dfsFinish g fuel vis fin u) acc).2 := by
        intro l acc hx'
        induction l generalizing acc with
        | nil => exact hx'
        | cons u us ihl =>
          simp only [List.foldl]
          exact ihl _ (dfsFinish_preserves_finish_mem fuel acc.1 acc.2 u x hx')
      have fold_prop :
          ∀ (l : List α) (acc : Finset α × List α),
            x ∉ acc.1 →
            x ∈ (l.foldl (fun ⟨vis, fin⟩ u => dfsFinish g fuel vis fin u) acc).1 →
            x ∈ (l.foldl (fun ⟨vis, fin⟩ u => dfsFinish g fuel vis fin u) acc).2 := by
        intro l acc
        induction l generalizing acc with
        | nil =>
          intro hnv' hx'; exact (hnv' hx').elim
        | cons u us ihl =>
          intro hnv' hx'
          simp only [List.foldl] at hx' ⊢
          by_cases hxStep : x ∈ (dfsFinish g fuel acc.1 acc.2 u).1
          · exact fold_pres_fin us (dfsFinish g fuel acc.1 acc.2 u)
              (ih acc.1 acc.2 u x hnv' hxStep)
          · exact ihl (dfsFinish g fuel acc.1 acc.2 u) (fun h => hxStep h) hx'
      by_cases hxv : x = v
      · subst hxv; exact List.mem_cons_self
      · have hnvInsert : x ∉ insert v visited := by
          simp [Finset.mem_insert, hnv, hxv]
        exact List.mem_cons_of_mem v
          (fold_prop (finsetList (g.succ v)) (insert v visited, finish) hnvInsert hx)

/-- After `dfsFinish`, visited and finish stay membership-synced. -/
private theorem dfsFinish_sync {g : Digraph α} :
    ∀ fuel visited finish v,
      (∀ x, x ∈ visited ↔ x ∈ finish) →
      ∀ x, x ∈ (dfsFinish g fuel visited finish v).1 ↔
        x ∈ (dfsFinish g fuel visited finish v).2 := by
  intro fuel visited finish v hsync x
  constructor
  · intro hx
    by_cases hxv : x ∈ visited
    · exact dfsFinish_preserves_finish_mem fuel visited finish v x ((hsync x).mp hxv)
    · exact dfsFinish_new_visited_mem_finish fuel visited finish v x hxv hx
  · intro hx
    rcases dfsFinish_finish_mem_visited fuel visited finish v x hx with hOld | hNew
    · exact dfsFinish_visited_mono fuel visited finish v ((hsync x).mpr hOld)
    · exact hNew

/-- Newly finished vertices were not already visited. -/
private theorem dfsFinish_new_finish_not_visited {g : Digraph α} :
    ∀ fuel visited finish v x,
      x ∈ (dfsFinish g fuel visited finish v).2 →
        x ∈ finish ∨ x ∉ visited := by
  intro fuel
  induction fuel with
  | zero =>
    intro visited finish v x hx
    simp only [dfsFinish] at hx
    exact Or.inl hx
  | succ fuel ih =>
    intro visited finish v x hx
    by_cases hv : v ∈ visited
    · simp only [dfsFinish, hv, ite_true] at hx
      exact Or.inl hx
    · simp only [dfsFinish, hv, ite_false] at hx
      have fold_prop :
          ∀ (l : List α) (acc : Finset α × List α),
            visited ⊆ acc.1 →
            x ∈ (l.foldl (fun ⟨vis, fin⟩ u => dfsFinish g fuel vis fin u) acc).2 →
              x ∈ acc.2 ∨ x ∉ visited := by
        intro l acc
        induction l generalizing acc with
        | nil =>
          intro _hsub hx'; exact Or.inl hx'
        | cons u us ihl =>
          intro hsub hx'
          simp only [List.foldl] at hx'
          rcases ihl (dfsFinish g fuel acc.1 acc.2 u)
            (Finset.Subset.trans hsub (dfsFinish_visited_mono fuel acc.1 acc.2 u)) hx'
            with hInStep | hNew
          · rcases ih acc.1 acc.2 u x hInStep with hOld | hNotAcc
            · exact Or.inl hOld
            · exact Or.inr (fun hvis => hNotAcc (hsub hvis))
          · exact Or.inr hNew
      simp only [List.mem_cons] at hx
      rcases hx with hxv | hx
      · subst hxv; exact Or.inr hv
      · exact fold_prop (finsetList (g.succ v)) (insert v visited, finish)
          (Finset.subset_insert v visited) hx

/-- Already-visited vertices absent from finish stay absent. -/
private theorem dfsFinish_stays_out {g : Digraph α}
    (fuel : Nat) (visited : Finset α) (finish : List α) (v x : α)
    (hvis : x ∈ visited) (hfin : x ∉ finish) :
    x ∉ (dfsFinish g fuel visited finish v).2 := by
  intro hx
  rcases dfsFinish_new_finish_not_visited fuel visited finish v x hx with hOld | hNew
  · exact hfin hOld
  · exact hNew hvis

/-- Fold version of `dfsFinish_stays_out`. -/
private theorem dfsFinish_foldl_stays_out {g : Digraph α} {fuel : Nat}
    (l : List α) (acc : Finset α × List α) (x : α)
    (hvis : x ∈ acc.1) (hfin : x ∉ acc.2) :
    x ∉ (l.foldl (fun ⟨vis, fin⟩ u => dfsFinish g fuel vis fin u) acc).2 := by
  induction l generalizing acc with
  | nil => exact hfin
  | cons u us ih =>
    simp only [List.foldl]
    exact ih (dfsFinish g fuel acc.1 acc.2 u)
      (dfsFinish_visited_mono fuel acc.1 acc.2 u hvis)
      (dfsFinish_stays_out fuel acc.1 acc.2 u x hvis hfin)

/-- `dfsFinish` preserves Nodup when finish ⊆ visited. -/
private theorem dfsFinish_nodup {g : Digraph α} :
    ∀ fuel visited finish v,
      (∀ x ∈ finish, x ∈ visited) →
      finish.Nodup →
      (dfsFinish g fuel visited finish v).2.Nodup := by
  intro fuel
  induction fuel with
  | zero =>
    intro visited finish v _hsub hnd
    simpa [dfsFinish] using hnd
  | succ fuel ih =>
    intro visited finish v hsub hnd
    by_cases hv : v ∈ visited
    · simpa [dfsFinish, hv] using hnd
    · simp only [dfsFinish, hv, ite_false]
      have fold_nd :
          ∀ (l : List α) (acc : Finset α × List α),
            (∀ x ∈ acc.2, x ∈ acc.1) →
            acc.2.Nodup →
            (l.foldl (fun ⟨vis, fin⟩ u => dfsFinish g fuel vis fin u) acc).2.Nodup := by
        intro l acc
        induction l generalizing acc with
        | nil =>
          intro _hacc hnd'; exact hnd'
        | cons u us ihl =>
          intro hacc hnd'
          simp only [List.foldl]
          refine ihl (dfsFinish g fuel acc.1 acc.2 u) ?_ (ih acc.1 acc.2 u hacc hnd')
          intro x hx
          rcases dfsFinish_finish_mem_visited fuel acc.1 acc.2 u x hx with hOld | hNew
          · exact dfsFinish_visited_mono fuel acc.1 acc.2 u (hacc x hOld)
          · exact hNew
      have hv_out : v ∉
          ((finsetList (g.succ v)).foldl (fun ⟨vis, fin⟩ u => dfsFinish g fuel vis fin u)
            (insert v visited, finish)).2 :=
        dfsFinish_foldl_stays_out (finsetList (g.succ v)) (insert v visited, finish) v
          (Finset.mem_insert_self v visited)
          (fun h => hv (hsub v h))
      exact List.Nodup.cons hv_out
        (fold_nd (finsetList (g.succ v)) (insert v visited, finish)
          (fun x hx => Finset.mem_insert_of_mem (hsub x hx)) hnd)

omit [Fintype α] [DecidableEq α] [LinearOrder α] in
/-- Helper: `head? = some v` implies membership. -/
private theorem list_mem_of_head?_eq_some {l : List α} {v : α}
    (h : l.head? = some v) : v ∈ l := by
  cases l with
  | nil => simp at h
  | cons a t =>
    simp only [List.head?, Option.some.injEq] at h
    subst h
    exact List.mem_cons_self

/-- `finishOrderGo` covers every vertex when fuel exceeds the unvisited count. -/
private theorem finishOrderGo_covers {g : Digraph α} :
    ∀ fuel visited finish,
      (∀ x, x ∈ visited ↔ x ∈ finish) →
      Fintype.card α - visited.card < fuel →
      ∀ x : α, x ∈ finishOrderGo g fuel visited finish := by
  intro fuel
  induction fuel with
  | zero =>
    intro visited finish _hsync hlt _x
    exact (Nat.not_lt_zero _ hlt).elim
  | succ fuel ih =>
    intro visited finish hsync hlt x
    cases hhead : (finsetList (Finset.univ.filter (fun v => v ∉ visited))).head? with
    | none =>
      have hall : ∀ v : α, v ∈ visited := by
        intro v
        by_contra hnv
        have hvRem : v ∈ finsetList (Finset.univ.filter (fun w => w ∉ visited)) :=
          finsetList_mem.mpr (by simp [hnv])
        have hnone : finsetList (Finset.univ.filter (fun w => w ∉ visited)) = [] :=
          List.head?_eq_none_iff.mp hhead
        simp [hnone] at hvRem
      have : finishOrderGo g (fuel + 1) visited finish = finish := by
        simp only [finishOrderGo, hhead]
      rw [this]
      exact (hsync x).mp (hall x)
    | some v =>
      have hv_mem : v ∈ finsetList (Finset.univ.filter (fun w => w ∉ visited)) :=
        list_mem_of_head?_eq_some hhead
      have hv_unvis : v ∉ visited := by
        have := finsetList_mem.mp hv_mem
        simpa using this
      let step := dfsFinish g (Fintype.card α) visited finish v
      have hsync' : ∀ y, y ∈ step.1 ↔ y ∈ step.2 :=
        dfsFinish_sync (Fintype.card α) visited finish v hsync
      have hv_marked : v ∈ step.1 := by
        by_cases hcard : Fintype.card α = 0
        · exact (Fintype.card_eq_zero_iff.mp hcard).elim v
        · exact dfsFinish_marks_root (Fintype.card α) visited finish v
            (Nat.pos_of_ne_zero hcard) hv_unvis
      have hcard_lt : visited.card < step.1.card :=
        Finset.card_lt_card
          ((Finset.ssubset_iff_of_subset
            (dfsFinish_visited_mono (Fintype.card α) visited finish v)).mpr
            ⟨v, hv_marked, hv_unvis⟩)
      have hfuel' : Fintype.card α - step.1.card < fuel := by
        have hle : step.1.card ≤ Fintype.card α := Finset.card_le_univ _
        have hlt' : Fintype.card α - step.1.card < Fintype.card α - visited.card := by
          omega
        omega
      have hgo : finishOrderGo g (fuel + 1) visited finish =
          finishOrderGo g fuel step.1 step.2 := by
        dsimp [step]
        simp only [finishOrderGo, hhead]
      rw [hgo]
      exact ih step.1 step.2 hsync' hfuel' x

private theorem finishOrder_mem (g : Digraph α) (x : α) : x ∈ finishOrder g := by
  simpa [finishOrder] using
    finishOrderGo_covers (Fintype.card α + 1) ∅ []
      (by intro y; simp) (by omega) x

/-- `finishOrderGo` preserves Nodup under sync. -/
private theorem finishOrderGo_nodup {g : Digraph α} :
    ∀ fuel visited finish,
      (∀ x, x ∈ visited ↔ x ∈ finish) →
      finish.Nodup →
      (finishOrderGo g fuel visited finish).Nodup := by
  intro fuel
  induction fuel with
  | zero =>
    intro visited finish _hsync hnd
    simpa [finishOrderGo] using hnd
  | succ fuel ih =>
    intro visited finish hsync hnd
    cases hhead : (finsetList (Finset.univ.filter (fun v => v ∉ visited))).head? with
    | none =>
      have : finishOrderGo g (fuel + 1) visited finish = finish := by
        simp only [finishOrderGo, hhead]
      rwa [this]
    | some v =>
      have hv_unvis : v ∉ visited := by
        have := finsetList_mem.mp (list_mem_of_head?_eq_some hhead)
        simpa using this
      let step := dfsFinish g (Fintype.card α) visited finish v
      have hsync' : ∀ y, y ∈ step.1 ↔ y ∈ step.2 :=
        dfsFinish_sync (Fintype.card α) visited finish v hsync
      have hsub : ∀ x ∈ finish, x ∈ visited := fun x hx => (hsync x).mpr hx
      have hnd' : step.2.Nodup :=
        dfsFinish_nodup (Fintype.card α) visited finish v hsub hnd
      have hgo : finishOrderGo g (fuel + 1) visited finish =
          finishOrderGo g fuel step.1 step.2 := by
        dsimp [step]; simp only [finishOrderGo, hhead]
      rw [hgo]
      exact ih step.1 step.2 hsync' hnd'

private theorem finishOrder_nodup (g : Digraph α) : (finishOrder g).Nodup := by
  simpa [finishOrder] using
    finishOrderGo_nodup (Fintype.card α + 1) ∅ []
      (by intro y; simp) List.nodup_nil

private theorem finishOrder_length_le_card (g : Digraph α) :
    (finishOrder g).length ≤ Fintype.card α :=
  List.Nodup.length_le_card (finishOrder_nodup g)

/-- `kosarajuGo` places every finish/visited vertex into some component. -/
private theorem kosarajuGo_covers {g : Digraph α} :
    ∀ fuel visited finish comps,
      (∀ x ∈ visited, x ∈ comps.flatten) →
      (∀ x ∈ comps.flatten, x ∈ visited) →
      finish.length ≤ fuel →
      ∀ x, (x ∈ visited ∨ x ∈ finish) →
        x ∈ (kosarajuGo g fuel visited finish comps).flatten := by
  intro fuel
  induction fuel with
  | zero =>
    intro visited finish comps hvis hflat hlen x hx
    have hfinish : finish = [] := by
      cases finish with
      | nil => rfl
      | cons _ _ => simp at hlen
    simp only [hfinish, List.mem_nil_iff, or_false] at hx
    simpa [kosarajuGo] using hvis x hx
  | succ fuel ih =>
    intro visited finish comps hvis hflat hlen x hx
    cases finish with
    | nil =>
      simp only [List.mem_nil_iff, or_false] at hx
      simpa [kosarajuGo] using hvis x hx
    | cons seed vs =>
      simp only [List.length_cons] at hlen
      have hlen' : vs.length ≤ fuel := by omega
      by_cases hseed : seed ∈ visited
      · have : kosarajuGo g (fuel + 1) visited (seed :: vs) comps =
            kosarajuGo g fuel visited vs comps := by
          simp [kosarajuGo, hseed]
        rw [this]
        refine ih visited vs comps hvis hflat hlen' x ?_
        rcases hx with hx | hx
        · exact Or.inl hx
        · simp only [List.mem_cons] at hx
          rcases hx with rfl | hx
          · exact Or.inl hseed
          · exact Or.inr hx
      · let step := dfsCollect g.transpose (Fintype.card α) visited [] seed
        let visited' := step.1
        let comp := step.2
        have hfresh := dfsCollect_fresh_props (g := g.transpose) (Fintype.card α) visited seed
        have hmem_seed : seed ∈ comp := by
          dsimp [comp, step]
          by_cases hcard : Fintype.card α = 0
          · exact (Fintype.card_eq_zero_iff.mp hcard).elim seed
          · exact dfsCollect_root_mem_pos (g := g.transpose) (Fintype.card α) visited [] seed
              (Nat.pos_of_ne_zero hcard) hseed
        have hvis' : ∀ y ∈ visited', y ∈ (comps ++ [comp]).flatten := by
          intro y hy
          simp only [List.flatten_append, List.flatten_cons, List.flatten_nil,
            List.append_nil, List.mem_append]
          rcases dfsCollect_fresh_visited_union (g := g.transpose)
              (Fintype.card α) visited seed y hy with hyOld | hyNew
          · exact Or.inl (hvis y hyOld)
          · exact Or.inr hyNew
        have hflat' : ∀ y ∈ (comps ++ [comp]).flatten, y ∈ visited' := by
          intro y hy
          simp only [List.flatten_append, List.flatten_cons, List.flatten_nil,
            List.append_nil, List.mem_append] at hy
          rcases hy with hy | hy
          · exact dfsCollect_visited_mono (Fintype.card α) visited [] seed (hflat y hy)
          · exact hfresh.2.2 y hy
        have hgo : kosarajuGo g (fuel + 1) visited (seed :: vs) comps =
            kosarajuGo g fuel visited' vs (comps ++ [comp]) := by
          dsimp [visited', comp, step]
          simp [kosarajuGo, hseed]
        rw [hgo]
        refine ih visited' vs (comps ++ [comp]) hvis' hflat' hlen' x ?_
        rcases hx with hx | hx
        · exact Or.inl (dfsCollect_visited_mono (Fintype.card α) visited [] seed hx)
        · simp only [List.mem_cons] at hx
          rcases hx with hxs | hx
          · subst hxs
            exact Or.inl (hfresh.2.2 x hmem_seed)
          · exact Or.inr hx

theorem kosaraju_cover (g : Digraph α) :
    ∀ v : α, ∃ c ∈ kosaraju g, v ∈ c := by
  intro v
  have hvFin : v ∈ finishOrder g := finishOrder_mem g v
  have hlen : (finishOrder g).length ≤ Fintype.card α + 1 :=
    Nat.le_trans (finishOrder_length_le_card g) (Nat.le_succ _)
  have hmem : v ∈ (kosarajuGo g (Fintype.card α + 1) ∅ (finishOrder g) []).flatten :=
    kosarajuGo_covers (Fintype.card α + 1) ∅ (finishOrder g) []
      (by intro x hx; simp at hx)
      (by intro x hx; cases hx)
      hlen v (Or.inr hvFin)
  simpa [kosaraju] using List.mem_flatten.mp hmem

private theorem kosarajuGo_nonempty {g : Digraph α} :
    ∀ fuel visited finish comps c,
      (∀ c' ∈ comps, c' ≠ []) →
      c ∈ kosarajuGo g fuel visited finish comps → c ≠ [] := by
  intro fuel
  induction fuel with
  | zero => intro visited finish comps c hcomps hc; exact hcomps c hc
  | succ fuel ih =>
    intro visited finish comps c hcomps hc
    cases finish with
    | nil =>
      simpa [kosarajuGo] using hcomps c hc
    | cons seed vs =>
      by_cases hseed : seed ∈ visited
      · exact ih visited vs comps c hcomps (by simpa [kosarajuGo, hseed] using hc)
      · let step := dfsCollect g.transpose (Fintype.card α) visited [] seed
        let visited' := step.1
        let comp := step.2
        have hmem : seed ∈ comp := by
          dsimp [comp, step]
          by_cases hcard : Fintype.card α = 0
          · exact (Fintype.card_eq_zero_iff.mp hcard).elim seed
          · have hfuel : 0 < Fintype.card α := Nat.pos_of_ne_zero hcard
            exact dfsCollect_root_mem_pos (g := g.transpose) (Fintype.card α) visited [] seed hfuel hseed
        have hc' : c ∈ kosarajuGo g fuel visited' vs (comps ++ [comp]) := by
          simpa [kosarajuGo, hseed] using hc
        refine ih visited' vs (comps ++ [comp]) c ?_ hc'
        intro c' hc'
        rcases List.mem_append.mp hc' with hc' | hc'
        · exact hcomps c' hc'
        · rw [List.mem_singleton] at hc'
          subst hc'
          intro h
          rw [h] at hmem
          simp at hmem

theorem kosaraju_nonempty (g : Digraph α) :
    ∀ c ∈ kosaraju g, c ≠ [] := by
  intro c hc
  simpa [kosaraju] using
    kosarajuGo_nonempty (Fintype.card α + 1) ∅ (finishOrder g) [] c
      (by intro c' hc'; simp at hc') hc

/-! ### Finish-order positions and Kosaraju key lemma -/

/-- `x` finishes no earlier than `y` in decreasing finish order (head = last finished). -/
private def finishBefore (fin : List α) (x y : α) : Prop :=
  List.idxOf x fin ≤ List.idxOf y fin

omit [Fintype α] [LinearOrder α] in
private theorem finishBefore_refl (fin : List α) (x : α) : finishBefore fin x x :=
  Nat.le_refl _

omit [Fintype α] [LinearOrder α] in
private theorem finishBefore_trans {fin : List α} {x y z : α}
    (hxy : finishBefore fin x y) (hyz : finishBefore fin y z) :
    finishBefore fin x z :=
  Nat.le_trans hxy hyz

omit [Fintype α] [LinearOrder α] in
private theorem idxOf_lt_of_ne_of_nodup {fin : List α} {x y : α}
    (_hnd : fin.Nodup) (hx : x ∈ fin) (hy : y ∈ fin) (hne : x ≠ y) :
    List.idxOf x fin ≠ List.idxOf y fin := by
  intro heq
  have hx' : fin[List.idxOf x fin]? = some x := List.getElem?_idxOf hx
  have hy' : fin[List.idxOf y fin]? = some y := List.getElem?_idxOf hy
  rw [heq] at hx'
  have : some x = some y := by
    rw [← hx', hy']
  exact hne (Option.some.inj this)

omit [Fintype α] [LinearOrder α] in
private theorem finishBefore_antisymm {fin : List α} {x y : α}
    (hnd : fin.Nodup) (hx : x ∈ fin) (hy : y ∈ fin)
    (hxy : finishBefore fin x y) (hyx : finishBefore fin y x) : x = y := by
  have : List.idxOf x fin = List.idxOf y fin := Nat.le_antisymm hxy hyx
  by_contra hne
  exact (idxOf_lt_of_ne_of_nodup hnd hx hy hne) this

/-- `dfsFinish` only prepends to the finish stack (old finish is a suffix). -/
private theorem dfsFinish_finish_suffix {g : Digraph α} :
    ∀ fuel visited finish v,
      ∃ mid, (dfsFinish g fuel visited finish v).2 = mid ++ finish := by
  intro fuel
  induction fuel with
  | zero =>
    intro visited finish v
    exact ⟨[], by simp [dfsFinish]⟩
  | succ fuel ih =>
    intro visited finish v
    simp only [dfsFinish]
    split_ifs with hv
    · exact ⟨[], rfl⟩
    · have fold_suf :
          ∀ (l : List α) (accFin : List α),
            (∃ mid, accFin = mid ++ finish) →
            ∀ accVis,
              ∃ mid,
                (l.foldl (fun ⟨vis, fin⟩ u => dfsFinish g fuel vis fin u)
                  (accVis, accFin)).2 = mid ++ finish := by
        intro l accFin hacc accVis
        induction l generalizing accVis accFin with
        | nil => exact hacc
        | cons u us ihl =>
          simp only [List.foldl]
          rcases hacc with ⟨mid₀, h₀⟩
          rcases ih accVis accFin u with ⟨mid₁, h₁⟩
          -- After processing `u`, finish is `mid₁ ++ accFin = mid₁ ++ mid₀ ++ finish`.
          have hacc' : ∃ mid, (dfsFinish g fuel accVis accFin u).2 = mid ++ finish :=
            ⟨mid₁ ++ mid₀, by rw [h₁, h₀, List.append_assoc]⟩
          exact ihl (dfsFinish g fuel accVis accFin u).2 hacc'
            (dfsFinish g fuel accVis accFin u).1
      rcases fold_suf (finsetList (g.succ v)) finish ⟨[], rfl⟩ (insert v visited)
        with ⟨mid, hmid⟩
      refine ⟨v :: mid, ?_⟩
      -- Result finish is `v :: foldl....2`
      change (v :: (List.foldl (fun ⟨vis, fin⟩ u => dfsFinish g fuel vis fin u)
          (insert v visited, finish) (finsetList (g.succ v))).2) = v :: mid ++ finish
      rw [hmid, List.cons_append]

omit [Fintype α] [LinearOrder α] in
/-- If `x` lies in the right half of an append and not in the left, `idxOf` shifts by `mid.length`. -/
private theorem idxOf_append_right {mid finish : List α} {x : α}
    (_hx : x ∈ finish) (hdisj : x ∉ mid) :
    List.idxOf x (mid ++ finish) = mid.length + List.idxOf x finish := by
  induction mid with
  | nil => simp
  | cons z zs ih =>
    have hne : z ≠ x := fun h => hdisj (by simp [h])
    have hdisj' : x ∉ zs := fun h => hdisj (List.mem_cons_of_mem z h)
    simp [List.idxOf_cons, show (z == x) = false from beq_eq_false_iff_ne.mpr hne,
      ih hdisj', Nat.succ_add]

omit [Fintype α] [LinearOrder α] in
private theorem idxOf_lt_append_right {mid finish : List α} {x y : α}
    (hx : x ∈ finish) (hy : y ∈ finish)
    (hx_mid : x ∉ mid) (hy_mid : y ∉ mid)
    (hlt : List.idxOf x finish < List.idxOf y finish) :
    List.idxOf x (mid ++ finish) < List.idxOf y (mid ++ finish) := by
  rw [idxOf_append_right hx hx_mid, idxOf_append_right hy hy_mid]
  omega

omit [Fintype α] [LinearOrder α] in
private theorem idxOf_cons_self_zero (x : α) (xs : List α) :
    List.idxOf x (x :: xs) = 0 :=
  List.idxOf_cons_self

omit [Fintype α] [LinearOrder α] in
private theorem idxOf_cons_ne {x y : α} {xs : List α} (hne : x ≠ y) :
    List.idxOf y (x :: xs) = List.idxOf y xs + 1 := by
  simp [List.idxOf_cons, show (x == y) = false from beq_eq_false_iff_ne.mpr hne]

/-- New finish prefix from `dfsFinish` is disjoint from the prior finish stack. -/
private theorem dfsFinish_mid_disjoint {g : Digraph α} :
    ∀ fuel visited finish v,
      (∀ x ∈ finish, x ∈ visited) →
      finish.Nodup →
      ∃ mid, (dfsFinish g fuel visited finish v).2 = mid ++ finish ∧
        (∀ x ∈ mid, x ∉ finish) ∧
        (dfsFinish g fuel visited finish v).2.Nodup := by
  intro fuel visited finish v hsub hnd
  rcases dfsFinish_finish_suffix (g := g) fuel visited finish v with ⟨mid, hmid⟩
  have hnd' : (dfsFinish g fuel visited finish v).2.Nodup :=
    dfsFinish_nodup fuel visited finish v hsub hnd
  refine ⟨mid, hmid, ?_, hnd'⟩
  intro x hxMid hxFin
  have hnd'' : (mid ++ finish).Nodup := by rwa [← hmid]
  have hge : 2 ≤ (mid ++ finish).count x := by
    have hcnt : (mid ++ finish).count x = mid.count x + finish.count x := by
      simp [List.count_append]
    have h1 : 0 < mid.count x := List.count_pos_iff.mpr hxMid
    have h2 : 0 < finish.count x := List.count_pos_iff.mpr hxFin
    omega
  have hle : (mid ++ finish).count x ≤ 1 :=
    (List.nodup_iff_count_le_one.mp hnd'') x
  omega

/-- Foldl of `dfsFinish` only prepends to the finish stack. -/
private theorem dfsFinish_foldl_suffix {g : Digraph α} (fuel : Nat) :
    ∀ (l : List α) (accVis : Finset α) (accFin : List α),
      ∃ mid,
        (l.foldl (fun ⟨vis, fin⟩ u => dfsFinish g fuel vis fin u) (accVis, accFin)).2 =
          mid ++ accFin := by
  intro l accVis accFin
  induction l generalizing accVis accFin with
  | nil => exact ⟨[], rfl⟩
  | cons u us ih =>
    rcases dfsFinish_finish_suffix (g := g) fuel accVis accFin u with ⟨mid₁, h₁⟩
    rcases ih (dfsFinish g fuel accVis accFin u).1 (dfsFinish g fuel accVis accFin u).2
      with ⟨mid₂, h₂⟩
    refine ⟨mid₂ ++ mid₁, ?_⟩
    simp only [List.foldl]
    rw [h₂, h₁, List.append_assoc]

/-- With positive fuel, every vertex in the fold list ends up visited. -/
private theorem dfsFinish_foldl_marks_members {g : Digraph α} (fuel : Nat) (hfuel : 0 < fuel) :
    ∀ (l : List α) (accVis : Finset α) (accFin : List α) (y : α),
      y ∈ l →
        y ∈ (l.foldl (fun ⟨vis, fin⟩ u => dfsFinish g fuel vis fin u)
          (accVis, accFin)).1 := by
  intro l accVis accFin y hy
  induction l generalizing accVis accFin with
  | nil => cases hy
  | cons u us ih =>
    simp only [List.mem_cons] at hy
    simp only [List.foldl]
    have mono_rest :
        (dfsFinish g fuel accVis accFin u).1 ⊆
          (us.foldl (fun ⟨vis, fin⟩ w => dfsFinish g fuel vis fin w)
            (dfsFinish g fuel accVis accFin u)).1 := by
      -- foldl visited mono
      revert u
      intro u
      have fold_mono :
          ∀ (l : List α) (acc : Finset α × List α),
            acc.1 ⊆ (l.foldl (fun ⟨vis, fin⟩ w => dfsFinish g fuel vis fin w) acc).1 := by
        intro l acc
        induction l generalizing acc with
        | nil => exact Finset.Subset.refl _
        | cons w ws ihl =>
          exact Finset.Subset.trans (dfsFinish_visited_mono fuel acc.1 acc.2 w) (ihl _)
      intro
      exact fold_mono us (dfsFinish g fuel accVis accFin u)
    rcases hy with rfl | hy
    · -- y = head: marked by this step, then preserved by the rest of the fold
      have hy_step : y ∈ (dfsFinish g fuel accVis accFin y).1 := by
        by_cases hvis : y ∈ accVis
        · exact dfsFinish_visited_mono fuel accVis accFin y hvis
        · exact dfsFinish_marks_root fuel accVis accFin y hfuel hvis
      exact mono_rest hy_step
    · exact ih (dfsFinish g fuel accVis accFin u).1
        (dfsFinish g fuel accVis accFin u).2 hy

/-- During exploration of a fixed `root`, the fold maintains: finish ⊆ visited,
Nodup finish, and every open vertex reaches `root`. -/
private theorem dfsFinish_foldl_open_reach {g : Digraph α} (fuel : Nat) (root : α) :
    ∀ (l : List α) (accVis : Finset α) (accFin : List α),
      (∀ x ∈ accFin, x ∈ accVis) →
      accFin.Nodup →
      (∀ o ∈ accVis, o ∉ accFin → Reach g o root) →
      root ∈ accVis →
      root ∉ accFin →
      let res := l.foldl (fun ⟨vis, fin⟩ u => dfsFinish g fuel vis fin u) (accVis, accFin)
      (∀ x ∈ res.2, x ∈ res.1) ∧
        res.2.Nodup ∧
        (∀ o ∈ res.1, o ∉ res.2 → Reach g o root) ∧
        root ∈ res.1 ∧
        root ∉ res.2 := by
  intro l accVis accFin hsub hnd hopen hrootVis hrootFin
  induction l generalizing accVis accFin with
  | nil =>
    exact ⟨hsub, hnd, hopen, hrootVis, hrootFin⟩
  | cons u us ih =>
    simp only [List.foldl]
    -- One dfsFinish step, then IH. Need sync-ish properties after one step.
    have hsub' : ∀ x ∈ (dfsFinish g fuel accVis accFin u).2,
        x ∈ (dfsFinish g fuel accVis accFin u).1 := by
      intro x hx
      rcases dfsFinish_finish_mem_visited fuel accVis accFin u x hx with hxOld | hxVis
      · exact dfsFinish_visited_mono fuel accVis accFin u (hsub x hxOld)
      · exact hxVis
    have hnd' : (dfsFinish g fuel accVis accFin u).2.Nodup :=
      dfsFinish_nodup fuel accVis accFin u hsub hnd
    -- Open-reach after one step: open verts still reach root.
    -- Key: new visited verts are finished (under sync from sync lemma when starting synced)...
    -- We may not have full sync. Use: if o ∈ res.1, o ∉ res.2, then o was open before
    -- or is a bug. From dfsFinish_visited_subset style...
    have hopen' : ∀ o ∈ (dfsFinish g fuel accVis accFin u).1,
        o ∉ (dfsFinish g fuel accVis accFin u).2 → Reach g o root := by
      intro o hoVis hoFin
      -- If o was already visited before the step:
      by_cases hoOld : o ∈ accVis
      · -- If o was finished before, it stays finished (preserves finish mem)
        by_cases hoOldFin : o ∈ accFin
        · exact absurd (dfsFinish_preserves_finish_mem fuel accVis accFin u o hoOldFin) hoFin
        · exact hopen o hoOld hoOldFin
      · -- o newly visited ⇒ must be on finish (dfsFinish_new_visited_mem_finish)
        exact absurd (dfsFinish_new_visited_mem_finish fuel accVis accFin u o hoOld hoVis) hoFin
    have hrootVis' : root ∈ (dfsFinish g fuel accVis accFin u).1 :=
      dfsFinish_visited_mono fuel accVis accFin u hrootVis
    have hrootFin' : root ∉ (dfsFinish g fuel accVis accFin u).2 :=
      dfsFinish_stays_out fuel accVis accFin u root hrootVis hrootFin
    exact ih (dfsFinish g fuel accVis accFin u).1 (dfsFinish g fuel accVis accFin u).2
      hsub' hnd' hopen' hrootVis' hrootFin'

/-- Outgoing edges of a freshly explored vertex are classified in that call's finish stack.
Fuel must cover remaining vertices (`card ≤ fuel + visited.card`), as in `finishOrder`. -/
private theorem dfsFinish_root_succ_class {g : Digraph α} :
    ∀ fuel visited finish root,
      0 < fuel →
      Fintype.card α ≤ fuel + visited.card →
      root ∉ visited →
      (∀ x ∈ finish, x ∈ visited) →
      (∀ o ∈ visited, o ∉ finish → Reach g o root) →
      finish.Nodup →
      ∀ y ∈ g.succ root,
        Reach g y root ∨
          (y ∈ (dfsFinish g fuel visited finish root).2 ∧
            List.idxOf root (dfsFinish g fuel visited finish root).2 <
              List.idxOf y (dfsFinish g fuel visited finish root).2) := by
  intro fuel visited finish root hfuel hcard hroot hsub hopen hnd y hy
  cases fuel with
  | zero => exact (Nat.not_lt_zero 0 hfuel).elim
  | succ fuel =>
    have hres :
        (dfsFinish g (fuel + 1) visited finish root).2 =
          root ::
            ((finsetList (g.succ root)).foldl
              (fun ⟨vis, fin⟩ u => dfsFinish g fuel vis fin u)
              (insert root visited, finish)).2 := by
      simp [dfsFinish, hroot]
    have hfold := dfsFinish_foldl_open_reach (g := g) fuel root
      (finsetList (g.succ root)) (insert root visited) finish
      (fun x hx => Finset.mem_insert_of_mem (hsub x hx)) hnd
      (fun o ho hof => by
        simp only [Finset.mem_insert] at ho
        rcases ho with rfl | ho
        · exact Reach.refl
        · exact hopen o ho hof)
      (Finset.mem_insert_self root visited)
      (fun h => hroot (hsub root h))
    set foldRes :=
      (finsetList (g.succ root)).foldl
        (fun ⟨vis, fin⟩ u => dfsFinish g fuel vis fin u)
        (insert root visited, finish)
    have hrootFinFold : root ∉ foldRes.2 := hfold.2.2.2.2
    have hy_cases : Reach g y root ∨ y ∈ foldRes.2 := by
      by_cases hyFin : y ∈ foldRes.2
      · exact Or.inr hyFin
      · have hyVis : y ∈ foldRes.1 := by
          by_cases hfuel' : 0 < fuel
          · exact dfsFinish_foldl_marks_members (g := g) fuel hfuel'
              (finsetList (g.succ root)) (insert root visited) finish y
              (finsetList_mem.mpr hy)
          · -- fuel = 0: fold is a no-op on visited; card bound ⇒ all verts visited
            have hfuel0 : fuel = 0 := Nat.eq_zero_of_not_pos hfuel'
            subst hfuel0
            have foldl_zero :
                ∀ (l : List α) (accVis : Finset α) (accFin : List α),
                  l.foldl (fun ⟨vis, fin⟩ u => dfsFinish g 0 vis fin u)
                    (accVis, accFin) = (accVis, accFin) := by
              intro l accVis accFin
              induction l generalizing accVis accFin with
              | nil => rfl
              | cons u us ihl =>
                simp only [List.foldl]
                have h0 : dfsFinish g 0 accVis accFin u = (accVis, accFin) := rfl
                rw [h0]
                exact ihl accVis accFin
            have hfold0 : foldRes = (insert root visited, finish) := by
              simpa [foldRes] using foldl_zero (finsetList (g.succ root))
                (insert root visited) finish
            have hcard' : Fintype.card α ≤ (insert root visited).card := by
              rw [Finset.card_insert_of_notMem hroot]
              omega
            have huniv : insert root visited = Finset.univ :=
              Finset.eq_univ_of_card _ (Nat.le_antisymm (Finset.card_le_univ _) hcard')
            have : y ∈ insert root visited := by
              rw [huniv]; exact Finset.mem_univ y
            simpa [hfold0] using this
        exact Or.inl (hfold.2.2.1 y hyVis hyFin)
    rw [hres]
    rcases hy_cases with hReach | hyIn
    · exact Or.inl hReach
    · refine Or.inr ⟨List.mem_cons_of_mem root hyIn, ?_⟩
      have hne : root ≠ y := fun h => hrootFinFold (by simpa [h] using hyIn)
      rw [idxOf_cons_self_zero, idxOf_cons_ne hne]
      omega

/-- Every newly finished vertex's outgoing edges are classified in the call result. -/
private theorem dfsFinish_succ_class {g : Digraph α} :
    ∀ fuel visited finish root,
      Fintype.card α ≤ fuel + visited.card →
      (∀ x ∈ finish, x ∈ visited) →
      (∀ o ∈ visited, o ∉ finish → Reach g o root) →
      finish.Nodup →
      ∀ x, x ∉ finish → x ∈ (dfsFinish g fuel visited finish root).2 →
        ∀ y ∈ g.succ x,
          Reach g y x ∨
            (y ∈ (dfsFinish g fuel visited finish root).2 ∧
              List.idxOf x (dfsFinish g fuel visited finish root).2 <
                List.idxOf y (dfsFinish g fuel visited finish root).2) := by
  intro fuel
  induction fuel with
  | zero =>
    intro visited finish root _hcard _hsub _hopen _hnd x hxFin hxRes
    change x ∈ finish at hxRes
    exact (hxFin hxRes).elim
  | succ fuel ih =>
    intro visited finish root hcard hsub hopen hnd x hxFin hxRes y hy
    by_cases hrootMem : root ∈ visited
    · have : dfsFinish g (fuel + 1) visited finish root = (visited, finish) := by
        simp [dfsFinish, hrootMem]
      rw [this] at hxRes
      exact (hxFin hxRes).elim
    · have hres2 :
          (dfsFinish g (fuel + 1) visited finish root).2 =
            root ::
              ((finsetList (g.succ root)).foldl
                (fun ⟨vis, fin⟩ u => dfsFinish g fuel vis fin u)
                (insert root visited, finish)).2 := by
        simp [dfsFinish, hrootMem]
      rw [hres2] at hxRes ⊢
      set foldRes :=
        (finsetList (g.succ root)).foldl
          (fun ⟨vis, fin⟩ u => dfsFinish g fuel vis fin u)
          (insert root visited, finish)
      -- Classify edges of `root` itself.
      have hroot_class :=
        dfsFinish_root_succ_class (g := g) (fuel + 1) visited finish root
          (Nat.succ_pos _) hcard hrootMem hsub hopen hnd
      simp only [dfsFinish, hrootMem, ite_false] at hroot_class
      -- Now either x = root or x finished in the fold.
      simp only [List.mem_cons] at hxRes
      rcases hxRes with rfl | hxFold
      · -- x = root
        rcases hroot_class y hy with hR | ⟨hyMem, hlt⟩
        · exact Or.inl hR
        · refine Or.inr ⟨hyMem, ?_⟩
          simpa using hlt
      · -- x finished during the successor fold
        have hfold_open := dfsFinish_foldl_open_reach (g := g) fuel root
          (finsetList (g.succ root)) (insert root visited) finish
          (fun z hz => Finset.mem_insert_of_mem (hsub z hz)) hnd
          (fun o ho hof => by
            simp only [Finset.mem_insert] at ho
            rcases ho with rfl | ho
            · exact Reach.refl
            · exact hopen o ho hof)
          (Finset.mem_insert_self root visited)
          (fun h => hrootMem (hsub root h))
        -- Fold classification under open-reach to `root` and edge to each head.
        have fold_class :
            ∀ (l : List α) (accVis : Finset α) (accFin : List α),
              (∀ z ∈ accFin, z ∈ accVis) →
              accFin.Nodup →
              (∀ o ∈ accVis, o ∉ accFin → Reach g o root) →
              root ∈ accVis →
              root ∉ accFin →
              (∀ u ∈ l, u ∈ g.succ root) →
              Fintype.card α ≤ fuel + accVis.card →
              ∀ x, x ∉ accFin →
                x ∈ (l.foldl (fun ⟨vis, fin⟩ u => dfsFinish g fuel vis fin u)
                  (accVis, accFin)).2 →
                ∀ y ∈ g.succ x,
                  Reach g y x ∨
                    (y ∈ (l.foldl (fun ⟨vis, fin⟩ u => dfsFinish g fuel vis fin u)
                        (accVis, accFin)).2 ∧
                      List.idxOf x (l.foldl (fun ⟨vis, fin⟩ u => dfsFinish g fuel vis fin u)
                          (accVis, accFin)).2 <
                        List.idxOf y (l.foldl (fun ⟨vis, fin⟩ u => dfsFinish g fuel vis fin u)
                          (accVis, accFin)).2) := by
          intro l accVis accFin hsubA hndA hopenA hrootV hrootF hsuccA hcardA
          induction l generalizing accVis accFin with
          | nil =>
            intro x hxFin hxRes
            simp only [List.foldl] at hxRes
            exact (hxFin hxRes).elim
          | cons u us ihl =>
            intro x hxFin hxRes y hy
            simp only [List.foldl] at hxRes ⊢
            set step := dfsFinish g fuel accVis accFin u
            have huSucc : u ∈ g.succ root := hsuccA u List.mem_cons_self
            have hopenU : ∀ o ∈ accVis, o ∉ accFin → Reach g o u :=
              fun o ho hof =>
                Reach_trans (hopenA o ho hof) (Reach.tail huSucc Reach.refl)
            by_cases hxInStep : x ∈ step.2 ∧ x ∉ accFin
            · -- classified in `step`; lift across `us` prefix-append
              have hclass :=
                ih accVis accFin u hcardA hsubA hopenU hndA x hxInStep.2 hxInStep.1 y hy
              rcases dfsFinish_foldl_suffix (g := g) fuel us step.1 step.2 with ⟨mid, hmid⟩
              have hndStep : step.2.Nodup :=
                dfsFinish_nodup fuel accVis accFin u hsubA hndA
              rcases dfsFinish_mid_disjoint (g := g) fuel accVis accFin u hsubA hndA
                with ⟨midU, hmidU, hdisjU, _⟩
              rcases hclass with hR | ⟨hyMem, hlt⟩
              · exact Or.inl hR
              · -- y ∈ step.2, idx x < idx y in step.2; after us: mid ++ step.2
                have hxStep : x ∈ step.2 := hxInStep.1
                have hy_not_mid : y ∉ mid := by
                  -- y ∈ step.2 and final nodup of mid++step.2
                  intro hym
                  have hndFinal :
                      (us.foldl (fun ⟨vis, fin⟩ u => dfsFinish g fuel vis fin u)
                        step).2.Nodup := by
                    -- use open_reach-style nodup threading; from foldl_open_reach on us
                    have h := dfsFinish_foldl_open_reach (g := g) fuel root us step.1 step.2
                      (fun z hz => by
                        rcases dfsFinish_finish_mem_visited fuel accVis accFin u z hz with h1 | h2
                        · exact dfsFinish_visited_mono fuel accVis accFin u (hsubA z h1)
                        · exact h2)
                      hndStep
                      (fun o ho hof => by
                        -- open reach to root after step
                        have hop := dfsFinish_foldl_open_reach (g := g) fuel root [u] accVis accFin
                          hsubA hndA hopenA hrootV hrootF
                        -- specialize: after one-element fold
                        simp only [List.foldl] at hop
                        exact hop.2.2.1 o ho hof)
                      (dfsFinish_visited_mono fuel accVis accFin u hrootV)
                      (dfsFinish_stays_out fuel accVis accFin u root hrootV hrootF)
                    exact h.2.1
                  rw [hmid] at hndFinal
                  have hge : 2 ≤ (mid ++ step.2).count y := by
                    have h1 : 0 < mid.count y := List.count_pos_iff.mpr hym
                    have h2 : 0 < step.2.count y := List.count_pos_iff.mpr hyMem
                    simp [List.count_append]; omega
                  have hle := (List.nodup_iff_count_le_one.mp hndFinal) y
                  omega
                have hx_not_mid : x ∉ mid := by
                  intro hxm
                  have hndFinal :
                      (us.foldl (fun ⟨vis, fin⟩ u => dfsFinish g fuel vis fin u)
                        step).2.Nodup := by
                    have h := dfsFinish_foldl_open_reach (g := g) fuel root us step.1 step.2
                      (fun z hz => by
                        rcases dfsFinish_finish_mem_visited fuel accVis accFin u z hz with h1 | h2
                        · exact dfsFinish_visited_mono fuel accVis accFin u (hsubA z h1)
                        · exact h2)
                      hndStep
                      (fun o ho hof => by
                        have hop := dfsFinish_foldl_open_reach (g := g) fuel root [u] accVis accFin
                          hsubA hndA hopenA hrootV hrootF
                        simp only [List.foldl] at hop
                        exact hop.2.2.1 o ho hof)
                      (dfsFinish_visited_mono fuel accVis accFin u hrootV)
                      (dfsFinish_stays_out fuel accVis accFin u root hrootV hrootF)
                    exact h.2.1
                  rw [hmid] at hndFinal
                  have hge : 2 ≤ (mid ++ step.2).count x := by
                    have h1 : 0 < mid.count x := List.count_pos_iff.mpr hxm
                    have h2 : 0 < step.2.count x := List.count_pos_iff.mpr hxStep
                    simp [List.count_append]; omega
                  have hle := (List.nodup_iff_count_le_one.mp hndFinal) x
                  omega
                refine Or.inr ⟨?_, ?_⟩
                · rw [hmid]; exact List.mem_append_right mid hyMem
                · rw [hmid]
                  exact idxOf_lt_append_right hxStep hyMem hx_not_mid hy_not_mid hlt
            · -- x not newly in this step: continue into us
              have hxRes' : x ∈ (us.foldl (fun ⟨vis, fin⟩ u => dfsFinish g fuel vis fin u)
                  step).2 := hxRes
              -- x ∉ step.2 ∨ x ∈ accFin; but x ∉ accFin, so x ∉ step.2?
              have hxFreshStep : x ∉ step.2 := by
                intro hxS
                exact hxInStep ⟨hxS, hxFin⟩
              -- But then for ihl we need x ∉ step.2 as the "not in accFin" for the next acc...
              have hsubS : ∀ z ∈ step.2, z ∈ step.1 := fun z hz => by
                rcases dfsFinish_finish_mem_visited fuel accVis accFin u z hz with h1 | h2
                · exact dfsFinish_visited_mono fuel accVis accFin u (hsubA z h1)
                · exact h2
              have hndS : step.2.Nodup :=
                dfsFinish_nodup fuel accVis accFin u hsubA hndA
              have hopenS : ∀ o ∈ step.1, o ∉ step.2 → Reach g o root := by
                intro o ho hof
                by_cases hoOld : o ∈ accVis
                · by_cases hoFin : o ∈ accFin
                  · exact absurd (dfsFinish_preserves_finish_mem fuel accVis accFin u o hoFin) hof
                  · exact hopenA o hoOld hoFin
                · exact absurd (dfsFinish_new_visited_mem_finish fuel accVis accFin u o hoOld ho) hof
              have hrootVS : root ∈ step.1 :=
                dfsFinish_visited_mono fuel accVis accFin u hrootV
              have hrootFS : root ∉ step.2 :=
                dfsFinish_stays_out fuel accVis accFin u root hrootV hrootF
              have hcardS : Fintype.card α ≤ fuel + step.1.card := by
                have : accVis.card ≤ step.1.card := Finset.card_le_card
                  (dfsFinish_visited_mono fuel accVis accFin u)
                omega
              have hxNotStepFin : x ∉ step.2 := hxFreshStep
              exact ihl step.1 step.2 hsubS hndS hopenS hrootVS hrootFS
                (fun v hv => hsuccA v (List.mem_cons_of_mem u hv)) hcardS
                x hxNotStepFin hxRes' y hy
        have hcardFold : Fintype.card α ≤ fuel + (insert root visited).card := by
          rw [Finset.card_insert_of_notMem hrootMem]
          omega
        have hclassFold :=
          fold_class (finsetList (g.succ root)) (insert root visited) finish
            (fun z hz => Finset.mem_insert_of_mem (hsub z hz)) hnd
            (fun o ho hof => by
              simp only [Finset.mem_insert] at ho
              rcases ho with rfl | ho
              · exact Reach.refl
              · exact hopen o ho hof)
            (Finset.mem_insert_self root visited)
            (fun h => hrootMem (hsub root h))
            (fun u hu => finsetList_mem.mp hu)
            hcardFold
            x hxFin hxFold y hy
        -- Lift from foldRes.2 to root :: foldRes.2
        rcases hclassFold with hR | ⟨hyMem, hlt⟩
        · exact Or.inl hR
        · refine Or.inr ⟨List.mem_cons_of_mem root hyMem, ?_⟩
          have hne_x : root ≠ x := fun h => by
            subst h
            exact hfold_open.2.2.2.2 hxFold
          have hne_y : root ≠ y := fun h => by
            subst h
            -- y ∈ foldRes and root ∉ foldRes; if y=root contradiction
            exact hfold_open.2.2.2.2 hyMem
          have hlt' : List.idxOf x foldRes.2 < List.idxOf y foldRes.2 := by
            simpa [foldRes] using hlt
          rw [idxOf_cons_ne hne_x, idxOf_cons_ne hne_y]
          exact Nat.add_lt_add_right hlt' 1

/-- Edge classification lifts through `finishOrderGo` under sync. -/
private theorem finishOrderGo_succ_class {g : Digraph α} :
    ∀ fuel visited finish,
      (∀ x, x ∈ visited ↔ x ∈ finish) →
      finish.Nodup →
      Fintype.card α ≤ Fintype.card α + visited.card → -- trivial; real bound uses dfsFinish fuel = card
      (∀ x y, y ∈ g.succ x → x ∈ finish →
        Reach g y x ∨
          (y ∈ finish ∧ List.idxOf x finish < List.idxOf y finish)) →
      ∀ x y, y ∈ g.succ x →
        x ∈ finishOrderGo g fuel visited finish →
        Reach g y x ∨
          (y ∈ finishOrderGo g fuel visited finish ∧
            List.idxOf x (finishOrderGo g fuel visited finish) <
              List.idxOf y (finishOrderGo g fuel visited finish)) := by
  intro fuel
  induction fuel with
  | zero =>
    intro visited finish hsync hnd _htriv hold x y hy hx
    simp only [finishOrderGo] at hx ⊢
    exact hold x y hy hx
  | succ fuel ih =>
    intro visited finish hsync hnd _htriv hold x y hy hx
    cases hhead : (finsetList (Finset.univ.filter (fun v => v ∉ visited))).head? with
    | none =>
      simp only [finishOrderGo, hhead] at hx ⊢
      exact hold x y hy hx
    | some v =>
      have hv_unvis : v ∉ visited := by
        have := finsetList_mem.mp (list_mem_of_head?_eq_some hhead)
        simpa using this
      let step := dfsFinish g (Fintype.card α) visited finish v
      have hsub : ∀ z ∈ finish, z ∈ visited := fun z hz => (hsync z).mpr hz
      have hopen : ∀ o ∈ visited, o ∉ finish → Reach g o v := by
        intro o ho hof
        exact absurd ((hsync o).mp ho) hof
      have hcard : Fintype.card α ≤ Fintype.card α + visited.card := Nat.le_add_right _ _
      have hgo : finishOrderGo g (fuel + 1) visited finish =
          finishOrderGo g fuel step.1 step.2 := by
        dsimp [step]; simp only [finishOrderGo, hhead]
      rw [hgo] at hx ⊢
      have hsync' : ∀ z, z ∈ step.1 ↔ z ∈ step.2 :=
        dfsFinish_sync (Fintype.card α) visited finish v hsync
      have hnd' : step.2.Nodup :=
        dfsFinish_nodup (Fintype.card α) visited finish v hsub hnd
      -- Extend `hold` with newly classified edges from this dfsFinish
      have hold' : ∀ x y, y ∈ g.succ x → x ∈ step.2 →
          Reach g y x ∨
            (y ∈ step.2 ∧ List.idxOf x step.2 < List.idxOf y step.2) := by
        intro x y hy hxStep
        by_cases hxOld : x ∈ finish
        · -- old vertex: use hold, lift indices via suffix
          rcases hold x y hy hxOld with hR | ⟨hyFin, hlt⟩
          · exact Or.inl hR
          · rcases dfsFinish_mid_disjoint (g := g) (Fintype.card α) visited finish v hsub hnd
              with ⟨mid, hmid, hdisj, _⟩
            have hx_mid : x ∉ mid := fun h => hdisj x h hxOld
            have hy_mid : y ∉ mid := fun h => hdisj y h hyFin
            refine Or.inr ⟨?_, ?_⟩
            · rw [hmid]; exact List.mem_append_right mid hyFin
            · have hlt' := idxOf_lt_append_right hxOld hyFin hx_mid hy_mid hlt
              simpa [step, hmid] using hlt'
        · -- newly finished: dfsFinish_succ_class
          have hclass :=
            dfsFinish_succ_class (g := g) (Fintype.card α) visited finish v
              hcard hsub hopen hnd x hxOld hxStep y hy
          exact hclass
      exact ih step.1 step.2 hsync' hnd' (Nat.le_add_right _ _) hold' x y hy hx

private theorem finishOrder_succ_class (g : Digraph α) {x y : α}
    (hy : y ∈ g.succ x) :
    Reach g y x ∨
      List.idxOf x (finishOrder g) < List.idxOf y (finishOrder g) := by
  have hx : x ∈ finishOrder g := finishOrder_mem g x
  have h :=
    finishOrderGo_succ_class (Fintype.card α + 1) ∅ []
      (by intro z; simp) List.nodup_nil (Nat.le_add_right _ _)
      (by intro x y hy hx; simp at hx)
      x y hy (by simpa [finishOrder] using hx)
  rcases h with hR | ⟨_, hlt⟩
  · exact Or.inl hR
  · exact Or.inr hlt

/-- Index in decreasing finish order (`finishOrder`); smaller = finished later. -/
private def finishIdx (g : Digraph α) (x : α) : Nat :=
  List.idxOf x (finishOrder g)

/-! ### MathComp-style `tsorted` approach (not CLRS discovery)

Literature pass (rocq-community/tarjan `kosaraju.v`, lengyijun Lean Kosaraju,
Pottier DFS axioms): successful Kosaraju proofs do **not** finish CLRS 22.13 via
white-path/discovery. They strengthen the finish list to a topological invariant
(`tsorted` / `reachable_before`) and peel Mutual classes from its head.

**False lemma (deleted):** `Reach u v ∧ finishBefore v u → Reach v u`.
**Demoted:** free-standing `scc_edge_maxFinish_lt` (CLRS hard case) — not needed
once `finishOrder_tsorted` + head characterization are proved. -/

omit [LinearOrder α] in
private theorem Mutual_refl (g : Digraph α) (a : α) : Mutual g a a :=
  ⟨Reach.refl, Reach.refl⟩

omit [LinearOrder α] in
private theorem Mutual_symm {g : Digraph α} {a b : α} (h : Mutual g a b) : Mutual g b a :=
  ⟨h.2, h.1⟩

omit [LinearOrder α] in
private theorem Mutual_trans {g : Digraph α} {a b c : α}
    (hab : Mutual g a b) (hbc : Mutual g b c) : Mutual g a c :=
  ⟨Reach_trans hab.1 hbc.1, Reach_trans hbc.2 hab.2⟩

/-! #### Restricted reachability (MathComp `relto` / `connect_to`) -/

/-- Reachability using only edges whose **target** lies in `s` (MathComp `relto s`).
    Endpoints: `refl` always; after the first step every vertex is in `s`. -/
private inductive ReachIn (g : Digraph α) (s : Finset α) : α → α → Prop
  | refl {a} : ReachIn g s a a
  | tail {a b c} : b ∈ g.succ a → b ∈ s → ReachIn g s b c → ReachIn g s a c

private def MutualIn (g : Digraph α) (s : Finset α) (a b : α) : Prop :=
  ReachIn g s a b ∧ ReachIn g s b a

omit [LinearOrder α] in
private theorem ReachIn_trans {g : Digraph α} {s : Finset α} {a b c : α}
    (hab : ReachIn g s a b) (hbc : ReachIn g s b c) : ReachIn g s a c := by
  induction hab with
  | refl => exact hbc
  | tail hsuc hin r ih => exact ReachIn.tail hsuc hin (ih hbc)

omit [LinearOrder α] in
private theorem ReachIn_univ {g : Digraph α} {a b : α} :
    ReachIn g Finset.univ a b ↔ Reach g a b := by
  constructor
  · intro h
    induction h with
    | refl => exact Reach.refl
    | tail hsuc _hin r ih => exact Reach.tail hsuc ih
  · intro h
    induction h with
    | refl => exact ReachIn.refl
    | tail hsuc r ih => exact ReachIn.tail hsuc (Finset.mem_univ _) ih

omit [LinearOrder α] in
private theorem MutualIn_univ {g : Digraph α} {a b : α} :
    MutualIn g Finset.univ a b ↔ Mutual g a b := by
  simp only [MutualIn, Mutual, ReachIn_univ]

omit [LinearOrder α] in
private theorem MutualIn_refl (g : Digraph α) (s : Finset α) (a : α) :
    MutualIn g s a a :=
  ⟨ReachIn.refl, ReachIn.refl⟩

omit [LinearOrder α] in
private theorem MutualIn_symm {g : Digraph α} {s : Finset α} {a b : α}
    (h : MutualIn g s a b) : MutualIn g s b a :=
  ⟨h.2, h.1⟩

omit [LinearOrder α] in
private theorem MutualIn_trans {g : Digraph α} {s : Finset α} {a b c : α}
    (hab : MutualIn g s a b) (hbc : MutualIn g s b c) : MutualIn g s a c :=
  ⟨ReachIn_trans hab.1 hbc.1, ReachIn_trans hbc.2 hab.2⟩

omit [LinearOrder α] in
private theorem ReachIn_to_Reach {g : Digraph α} {s : Finset α} {a b : α}
    (h : ReachIn g s a b) : Reach g a b := by
  induction h with
  | refl => exact Reach.refl
  | tail hsuc _hin r ih => exact Reach.tail hsuc ih

omit [LinearOrder α] in
private theorem ReachIn_mono {g : Digraph α} {s t : Finset α} {a b : α}
    (hsub : s ⊆ t) (h : ReachIn g s a b) : ReachIn g t a b := by
  induction h with
  | refl => exact ReachIn.refl
  | tail hsuc hin r ih => exact ReachIn.tail hsuc (hsub hin) ih

/-- Max-finish representative of `a` in `fin` w.r.t. `MutualIn` on `aSet`
    (MathComp `can_to`). -/
private def IsCanTo (g : Digraph α) (fin : List α) (aSet : Finset α)
    (a c : α) : Prop :=
  c ∈ fin ∧ MutualIn g aSet a c ∧
    ∀ z ∈ fin, MutualIn g aSet a z → finishBefore fin c z

/-- MathComp `tsorted`: `fin` is topologically sorted w.r.t. reachability in `aSet`.

Tweaked from exact `mem ↔ remaining` to MathComp’s `subset` + `closed` form so
DFS prefixes can be tsorted w.r.t. a larger allowed set than the prefix itself. -/
private structure TSorted (g : Digraph α) (aSet : Finset α) (fin : List α) : Prop where
  subset : ∀ x ∈ fin, x ∈ aSet
  nodup : fin.Nodup
  closed : ∀ x y, x ∈ fin → ReachIn g aSet x y → y ∈ fin
  can_before :
    ∀ x y, x ∈ fin → ReachIn g aSet x y →
      ∃ c, IsCanTo g fin aSet x c ∧ finishBefore fin c y

omit [LinearOrder α] in
private theorem TSorted.nil (g : Digraph α) (aSet : Finset α) :
    TSorted g aSet ([] : List α) where
  subset := by intro x hx; cases hx
  nodup := List.nodup_nil
  closed := by intro x y hx; cases hx
  can_before := by intro x y hx; cases hx

omit [LinearOrder α] in
/-- Existence of a max-finish `MutualIn` representative in `fin`. -/
private theorem exists_IsCanTo {g : Digraph α} {fin : List α} {aSet : Finset α}
    {a : α} (ha : a ∈ fin) :
    ∃ c, IsCanTo g fin aSet a c := by
  classical
  let s : Finset α := fin.toFinset.filter (fun z => MutualIn g aSet a z)
  have hs : s.Nonempty := ⟨a, by
    simp only [Finset.mem_filter, List.mem_toFinset, s]
    exact ⟨ha, MutualIn_refl g aSet a⟩⟩
  obtain ⟨c, hc, hmin⟩ := Finset.exists_min_image s (fun z => List.idxOf z fin) hs
  have hc' : c ∈ fin ∧ MutualIn g aSet a c := by
    simpa [s, List.mem_toFinset] using hc
  refine ⟨c, hc'.1, hc'.2, fun z hz hm => ?_⟩
  exact hmin z (by simp [s, List.mem_toFinset, hz, hm])

omit [Fintype α] [LinearOrder α] in
private theorem eq_of_idxOf_eq {fin : List α} {x y : α}
    (hx : x ∈ fin) (hy : y ∈ fin) (h : List.idxOf x fin = List.idxOf y fin) :
    x = y := by
  have hx' : fin[List.idxOf x fin]? = some x := List.getElem?_idxOf hx
  have hy' : fin[List.idxOf y fin]? = some y := List.getElem?_idxOf hy
  rw [h] at hx'
  exact Option.some.inj (hx'.symm.trans hy')

/-! #### Build `TSorted` during DFS (MathComp `pdfs_correct` path)

Prove `tsorted_cons_r`-style lemmas about `dfsFinish` prefixes, then assemble
`finishOrder_tsorted`. -/

omit [Fintype α] [LinearOrder α] in
private theorem finishBefore_cons_head (x : α) (fin : List α) (y : α) :
    finishBefore (x :: fin) x y := by
  change List.idxOf x (x :: fin) ≤ List.idxOf y (x :: fin)
  rw [idxOf_cons_self_zero]
  exact Nat.zero_le _

/-- Allowed set with list `l` removed (MathComp `[predD a & [pred x in l]]`). -/
private def aSetMinus (aSet : Finset α) (l : List α) : Finset α :=
  aSet.filter (fun z => z ∉ l)

omit [Fintype α] [LinearOrder α] in
private theorem mem_aSetMinus {aSet : Finset α} {l : List α} {z : α} :
    z ∈ aSetMinus aSet l ↔ z ∈ aSet ∧ z ∉ l := by
  simp [aSetMinus]

omit [Fintype α] [LinearOrder α] in
private theorem aSetMinus_subset (aSet : Finset α) (l : List α) :
    aSetMinus aSet l ⊆ aSet :=
  fun _z hz => (mem_aSetMinus.mp hz).1

omit [LinearOrder α] in
/-- If a path in `aSet` is not a path in `aSet.erase x`, it goes through `x`. -/
private theorem ReachIn_split_through {g : Digraph α} {aSet : Finset α} {x y z : α}
    (h : ReachIn g aSet y z) (hnot : ¬ReachIn g (aSet.erase x) y z) :
    ReachIn g aSet y x ∧ ReachIn g aSet x z := by
  induction h with
  | refl =>
    exact (hnot ReachIn.refl).elim
  | @tail a b c hsuc hin r ih =>
    by_cases hb : b = x
    · subst hb
      exact ⟨ReachIn.tail hsuc hin ReachIn.refl, r⟩
    · have hin' : b ∈ aSet.erase x := Finset.mem_erase.mpr ⟨hb, hin⟩
      have hnot' : ¬ReachIn g (aSet.erase x) b c := fun hbC =>
        hnot (ReachIn.tail hsuc hin' hbC)
      rcases ih hnot' with ⟨hbX, hxC⟩
      exact ⟨ReachIn.tail hsuc hin hbX, hxC⟩

omit [LinearOrder α] in
/-- A non-trivial `ReachIn` from `x` in `erase x` lands in `fin` when successors of
    `x` that remain in `aSet` are already in `fin` and `fin` is closed. -/
private theorem reachIn_from_root_mem {g : Digraph α} {aSet : Finset α}
    {x t : α} {fin : List α}
    (hne : t ≠ x)
    (hsucc : ∀ y, y ∈ g.succ x → y ∈ aSet → y ≠ x → y ∈ fin)
    (hclosed : ∀ u v, u ∈ fin → ReachIn g (aSet.erase x) u v → v ∈ fin)
    (hreach : ReachIn g (aSet.erase x) x t) :
    t ∈ fin := by
  cases hreach with
  | refl => exact (hne rfl).elim
  | @tail _ b _ hsuc hin r =>
    have hb_ne : b ≠ x := Finset.ne_of_mem_erase hin
    have hb_in : b ∈ aSet := Finset.mem_of_mem_erase hin
    have hb_fin : b ∈ fin := hsucc b hsuc hb_in hb_ne
    exact hclosed b t hb_fin r

omit [LinearOrder α] in
private theorem MutualIn_mono {g : Digraph α} {s t : Finset α} {a b : α}
    (hsub : s ⊆ t) (h : MutualIn g s a b) : MutualIn g t a b :=
  ⟨ReachIn_mono hsub h.1, ReachIn_mono hsub h.2⟩

omit [LinearOrder α] in
/-- Targets reachable from `x` or from `fin` under the cons hyps stay in `{x} ∪ fin`. -/
private theorem reachIn_mem_cons {g : Digraph α} {aSet : Finset α} {x : α} {fin : List α}
    (hsucc : ∀ y, y ∈ g.succ x → y ∈ aSet → y ≠ x → y ∈ fin)
    (hclosed : ∀ u v, u ∈ fin → ReachIn g (aSet.erase x) u v → v ∈ fin)
    {a z : α} (hreach : ReachIn g aSet a z) (ha : a = x ∨ a ∈ fin) :
    z = x ∨ z ∈ fin := by
  induction hreach with
  | refl => exact ha
  | @tail a b c hsuc hin r ih =>
    apply ih
    cases ha with
    | inl hax =>
      by_cases hbX : b = x
      · exact Or.inl hbX
      · exact Or.inr (hsucc b (by simpa [hax] using hsuc) (by simpa [hax] using hin) hbX)
    | inr haFin =>
      by_cases hbX : b = x
      · exact Or.inl hbX
      · have hin' : b ∈ aSet.erase x := Finset.mem_erase.mpr ⟨hbX, hin⟩
        exact Or.inr (hclosed a b haFin (ReachIn.tail hsuc hin' ReachIn.refl))

omit [LinearOrder α] in
/-- `TSorted` is preserved under extensional equality of allowed sets. -/
private theorem TSorted.congr {g : Digraph α} {aSet bSet : Finset α} {fin : List α}
    (heq : ∀ z, z ∈ aSet ↔ z ∈ bSet) (h : TSorted g aSet fin) :
    TSorted g bSet fin := by
  have hab : aSet ⊆ bSet := fun z hz => (heq z).mp hz
  have hba : bSet ⊆ aSet := fun z hz => (heq z).mpr hz
  refine ⟨fun x hx => hab (h.subset x hx), h.nodup, ?_, ?_⟩
  · intro x y hx hr
    exact h.closed x y hx (ReachIn_mono hba hr)
  · intro x y hx hr
    obtain ⟨c, hcan, hbefore⟩ := h.can_before x y hx (ReachIn_mono hba hr)
    refine ⟨c, ⟨hcan.1, MutualIn_mono hab hcan.2.1, ?_⟩, hbefore⟩
    intro z hz hm
    exact hcan.2.2 z hz (MutualIn_mono hba hm)

omit [LinearOrder α] in
/-- Prepending a freshly finished root `x` to a tsorted child-finish list
    (MathComp `tsorted_cons_r`). -/
private theorem tsorted_cons_r {g : Digraph α} {aSet : Finset α}
    {x : α} {fin : List α}
    (hx : x ∈ aSet) (hx_notin : x ∉ fin)
    (hreaches : ∀ y, y ∈ fin → ReachIn g aSet x y)
    (hsucc : ∀ y, y ∈ g.succ x → y ∈ aSet → y ≠ x → y ∈ fin)
    (hts : TSorted g (aSet.erase x) fin) :
    TSorted g aSet (x :: fin) where
  subset := by
    intro y hy
    simp only [List.mem_cons] at hy
    rcases hy with rfl | hy
    · exact hx
    · exact Finset.mem_of_mem_erase (hts.subset y hy)
  nodup := List.nodup_cons.mpr ⟨hx_notin, hts.nodup⟩
  closed := by
    intro y z hy hz
    simpa [List.mem_cons] using
      reachIn_mem_cons hsucc hts.closed hz (by simpa [List.mem_cons] using hy)
  can_before := by
    intro y z hy hz
    have erase_sub : aSet.erase x ⊆ aSet := Finset.erase_subset x aSet
    have hx_mem : x ∈ x :: fin := @List.Mem.head α x fin
    simp only [List.mem_cons] at hy
    cases hy with
    | inl hyx =>
      refine ⟨x, ⟨⟨hx_mem, ?_, fun w _ _ => finishBefore_cons_head x fin w⟩, finishBefore_cons_head x fin z⟩⟩
      simpa [hyx] using MutualIn_refl g aSet x
    | inr hyFin =>
      by_cases hMutX : MutualIn g aSet y x
      · refine ⟨x, ⟨⟨hx_mem, hMutX, ?_⟩, finishBefore_cons_head x fin z⟩⟩
        intro w _hw _hm
        exact finishBefore_cons_head x fin w
      · by_cases hzErase : ReachIn g (aSet.erase x) y z
        · obtain ⟨c, hcan, hbefore⟩ := hts.can_before y z hyFin hzErase
          have hcFin := hcan.1
          have hcMut := hcan.2.1
          have hcBefore := hcan.2.2
          have hc_ne : c ≠ x := fun h => hx_notin (by simpa [h] using hcFin)
          have hzFin : z ∈ fin := hts.closed y z hyFin hzErase
          have hz_ne : z ≠ x := fun h => hx_notin (by simpa [h] using hzFin)
          have mut_iff :
              ∀ w ∈ fin, MutualIn g aSet y w ↔ MutualIn g (aSet.erase x) y w := by
            intro w hw
            constructor
            · intro ⟨hyw, hwy⟩
              refine ⟨?_, ?_⟩
              · by_cases hE : ReachIn g (aSet.erase x) y w
                · exact hE
                · rcases ReachIn_split_through hyw hE with ⟨hyX, _⟩
                  exact (hMutX ⟨hyX, hreaches y hyFin⟩).elim
              · by_cases hE : ReachIn g (aSet.erase x) w y
                · exact hE
                · rcases ReachIn_split_through hwy hE with ⟨hwX, _⟩
                  by_cases hEw : ReachIn g (aSet.erase x) y w
                  · exact
                      (hMutX ⟨ReachIn_trans (ReachIn_mono erase_sub hEw) hwX,
                        hreaches y hyFin⟩).elim
                  · rcases ReachIn_split_through hyw hEw with ⟨hyX, _⟩
                    exact (hMutX ⟨hyX, hreaches y hyFin⟩).elim
            · intro hm
              exact MutualIn_mono erase_sub hm
          have hc_mem : c ∈ x :: fin := List.mem_cons_of_mem x hcFin
          refine ⟨c, ⟨⟨hc_mem, MutualIn_mono erase_sub hcMut, ?_⟩, ?_⟩⟩
          · intro w hw hm
            simp only [List.mem_cons] at hw
            cases hw with
            | inl hwx =>
              have : w = x := hwx
              exact (hMutX (by simpa [this] using hm)).elim
            | inr hwFin =>
              have hmE : MutualIn g (aSet.erase x) y w := (mut_iff w hwFin).mp hm
              have hBF := hcBefore w hwFin hmE
              have hw_ne : w ≠ x := fun h => hx_notin (by simpa [h] using hwFin)
              have hx_ne_c : x ≠ c := hc_ne.symm
              have hx_ne_w : x ≠ w := hw_ne.symm
              simp only [finishBefore, idxOf_cons_ne hx_ne_c, idxOf_cons_ne hx_ne_w]
              exact Nat.succ_le_succ hBF
          · have hx_ne_c : x ≠ c := hc_ne.symm
            have hx_ne_z : x ≠ z := hz_ne.symm
            simp only [finishBefore, idxOf_cons_ne hx_ne_c, idxOf_cons_ne hx_ne_z]
            exact Nat.succ_le_succ hbefore
        · rcases ReachIn_split_through hz hzErase with ⟨hyX, _⟩
          exact (hMutX ⟨hyX, hreaches y hyFin⟩).elim

omit [LinearOrder α] in
/-- A path from outside `l₁` either stays in `aSet \ l₁` or first hits `l₁`. -/
private theorem ReachIn_avoid_or_hit {g : Digraph α} {aSet : Finset α} {l₁ : List α}
    {x y : α} (hx : x ∉ l₁) (h : ReachIn g aSet x y) :
    ReachIn g (aSetMinus aSet l₁) x y ∨
      ∃ z ∈ l₁, ReachIn g aSet x z ∧ ReachIn g aSet z y := by
  revert hx
  induction h with
  | refl => intro _; exact Or.inl ReachIn.refl
  | @tail a b c hsuc hin r ih =>
    intro ha
    by_cases hb : b ∈ l₁
    · exact Or.inr ⟨b, hb, ReachIn.tail hsuc hin ReachIn.refl, r⟩
    · have hin' : b ∈ aSetMinus aSet l₁ := mem_aSetMinus.mpr ⟨hin, hb⟩
      rcases ih hb with hE | ⟨z, hz, hbz, hzy⟩
      · exact Or.inl (ReachIn.tail hsuc hin' hE)
      · exact Or.inr ⟨z, hz, ReachIn.tail hsuc hin hbz, hzy⟩

omit [Fintype α] [LinearOrder α] in
private theorem idxOf_append_left {l₂ l₁ : List α} {x : α} (hx : x ∈ l₂) :
    List.idxOf x (l₂ ++ l₁) = List.idxOf x l₂ :=
  List.idxOf_append_of_mem hx

omit [Fintype α] [LinearOrder α] in
private theorem idxOf_append_right_notin {l₂ l₁ : List α} {x : α} (hx : x ∉ l₂) :
    List.idxOf x (l₂ ++ l₁) = l₂.length + List.idxOf x l₁ :=
  List.idxOf_append_of_notMem hx

omit [Fintype α] [LinearOrder α] in
private theorem idxOf_lt_length_of_mem {l : List α} {x : α} (hx : x ∈ l) :
    List.idxOf x l < l.length :=
  lt_of_le_of_ne List.idxOf_le_length fun h => (List.idxOf_eq_length_iff.mp h) hx

omit [LinearOrder α] in
/-- Concatenation of tsorted segments (MathComp `tsorted_cat`):
    `l₂` is tsorted on `aSet \ l₁`, result is `l₂ ++ l₁`. -/
private theorem tsorted_cat {g : Digraph α} {aSet : Finset α}
    {l₁ l₂ : List α}
    (h₁ : TSorted g aSet l₁)
    (h₂ : TSorted g (aSetMinus aSet l₁) l₂) :
    TSorted g aSet (l₂ ++ l₁) where
  subset := by
    intro x hx
    simp only [List.mem_append] at hx
    rcases hx with hx | hx
    · exact aSetMinus_subset _ _ (h₂.subset x hx)
    · exact h₁.subset x hx
  nodup := by
    refine List.Nodup.append h₂.nodup h₁.nodup ?_
    intro x hx₂ hx₁
    exact (mem_aSetMinus.mp (h₂.subset x hx₂)).2 hx₁
  closed := by
    intro x y hx hy
    simp only [List.mem_append] at hx ⊢
    have minus_sub : aSetMinus aSet l₁ ⊆ aSet := aSetMinus_subset aSet l₁
    rcases hx with hx₂ | hx₁
    · have hx_notin : x ∉ l₁ := (mem_aSetMinus.mp (h₂.subset x hx₂)).2
      rcases ReachIn_avoid_or_hit hx_notin hy with hE | ⟨z, hz₁, -, hzy⟩
      · exact Or.inl (h₂.closed x y hx₂ hE)
      · exact Or.inr (h₁.closed z y hz₁ hzy)
    · exact Or.inr (h₁.closed x y hx₁ hy)
  can_before := by
    intro x y hx hy
    simp only [List.mem_append] at hx
    have minus_sub : aSetMinus aSet l₁ ⊆ aSet := aSetMinus_subset aSet l₁
    rcases hx with hx₂ | hx₁
    · -- seed in l₂ (newer / front)
      have hx_notin : x ∉ l₁ := (mem_aSetMinus.mp (h₂.subset x hx₂)).2
      rcases ReachIn_avoid_or_hit hx_notin hy with hE | ⟨z, hz₁, hxz, hzy⟩
      · -- path stays in aSetMinus: lift child can
        obtain ⟨c, hcan, hbefore⟩ := h₂.can_before x y hx₂ hE
        have hc₂ : c ∈ l₂ := hcan.1
        have hc_notin : c ∉ l₁ := (mem_aSetMinus.mp (h₂.subset c hc₂)).2
        -- MutualIn on minus lifts; partners in l₁ cannot be mutual with x in aSet
        -- without hitting l₁ from x... use exists_IsCanTo style on full list
        refine ⟨c, ⟨List.mem_append_left l₁ hc₂, MutualIn_mono minus_sub hcan.2.1, ?_⟩, ?_⟩
        · intro w hw hm
          simp only [List.mem_append] at hw
          rcases hw with hw₂ | hw₁
          · have hmE : MutualIn g (aSetMinus aSet l₁) x w := by
              -- same mut_iff argument as cons
              constructor
              · by_cases hR : ReachIn g (aSetMinus aSet l₁) x w
                · exact hR
                · rcases ReachIn_avoid_or_hit hx_notin hm.1 with hE' | ⟨u, hu, hxu, huw⟩
                  · exact (hR hE').elim
                  · -- x reaches u ∈ l₁ and u reaches w ∈ l₂; but w ∈ l₂ ⊆ aSetMinus so w ∉ l₁
                    -- closed of h₁: u reaches w ⇒ w ∈ l₁, contradiction
                    exact ((mem_aSetMinus.mp (h₂.subset w hw₂)).2 (h₁.closed u w hu huw)).elim
              · by_cases hR : ReachIn g (aSetMinus aSet l₁) w x
                · exact hR
                · have hw_notin : w ∉ l₁ := (mem_aSetMinus.mp (h₂.subset w hw₂)).2
                  rcases ReachIn_avoid_or_hit hw_notin hm.2 with hE' | ⟨u, hu, hwu, hux⟩
                  · exact (hR hE').elim
                  · exact ((mem_aSetMinus.mp (h₂.subset x hx₂)).2 (h₁.closed u x hu hux)).elim
            have hBF := hcan.2.2 w hw₂ hmE
            simpa [finishBefore, idxOf_append_left hc₂, idxOf_append_left hw₂] using hBF
          · -- w ∈ l₁: idx c in front half is before anything in l₁
            have hw_notin₂ : w ∉ l₂ := fun h =>
              (mem_aSetMinus.mp (h₂.subset w h)).2 hw₁
            rw [finishBefore, idxOf_append_left hc₂, idxOf_append_right_notin hw_notin₂]
            have hlt : List.idxOf c l₂ < l₂.length := idxOf_lt_length_of_mem hc₂
            omega
        · -- finishBefore c y
          have hy₂' : y ∈ l₂ := h₂.closed x y hx₂ hE
          rw [finishBefore, idxOf_append_left hc₂, idxOf_append_left hy₂']
          exact hbefore
      · -- path hits `l₁` at `z`: `y ∈ l₁`, and can of `x` stays in `l₂`
        have hy₁ : y ∈ l₁ := h₁.closed z y hz₁ hzy
        obtain ⟨c, hcan⟩ := exists_IsCanTo (aSet := aSet) (List.mem_append_left l₁ hx₂)
        have hc_mem : c ∈ l₂ ++ l₁ := hcan.1
        have hc₂ : c ∈ l₂ := by
          simp only [List.mem_append] at hc_mem
          rcases hc_mem with hc₂ | hc₁
          · exact hc₂
          · exact (hx_notin (h₁.closed c x hc₁ hcan.2.1.2)).elim
        have hy_notin₂ : y ∉ l₂ := fun h =>
          (mem_aSetMinus.mp (h₂.subset y h)).2 hy₁
        refine ⟨c, hcan, ?_⟩
        rw [finishBefore, idxOf_append_left hc₂, idxOf_append_right_notin hy_notin₂]
        have hlt : List.idxOf c l₂ < l₂.length := idxOf_lt_length_of_mem hc₂
        omega
    · -- seed in l₁ (older / back)
      obtain ⟨c, hcan, hbefore⟩ := h₁.can_before x y hx₁ hy
      have hc₁ : c ∈ l₁ := hcan.1
      have hc_notin₂ : c ∉ l₂ := fun h =>
        (mem_aSetMinus.mp (h₂.subset c h)).2 hc₁
      refine ⟨c, ⟨List.mem_append_right l₂ hc₁, hcan.2.1, ?_⟩, ?_⟩
      · intro w hw hm
        simp only [List.mem_append] at hw
        rcases hw with hw₂ | hw₁
        · have hx_notin₂ : x ∉ l₂ := fun h =>
            (mem_aSetMinus.mp (h₂.subset x h)).2 hx₁
          have hw_notin : w ∉ l₁ := (mem_aSetMinus.mp (h₂.subset w hw₂)).2
          rcases ReachIn_avoid_or_hit hw_notin hm.2 with hE | ⟨u, hu, -, hux⟩
          · exact (hx_notin₂ (h₂.closed w x hw₂ hE)).elim
          · exact (hw_notin (h₁.closed x w hx₁ hm.1)).elim
        · have hBF := hcan.2.2 w hw₁ hm
          have hw_notin₂ : w ∉ l₂ := fun h =>
            (mem_aSetMinus.mp (h₂.subset w h)).2 hw₁
          rw [finishBefore, idxOf_append_right_notin hc_notin₂,
            idxOf_append_right_notin hw_notin₂]
          exact Nat.add_le_add_left hBF _
      · have hy₁ : y ∈ l₁ := h₁.closed x y hx₁ hy
        have hy_notin₂ : y ∉ l₂ := fun h =>
          (mem_aSetMinus.mp (h₂.subset y h)).2 hy₁
        rw [finishBefore, idxOf_append_right_notin hc_notin₂,
          idxOf_append_right_notin hy_notin₂]
        exact Nat.add_le_add_left hbefore _

/-- Remaining vertices relative to `visited`. -/
private def remaining (visited : Finset α) : Finset α :=
  Finset.univ.filter (fun z => z ∉ visited)

omit [LinearOrder α] in
private theorem mem_remaining {visited : Finset α} {z : α} :
    z ∈ remaining visited ↔ z ∉ visited := by
  simp [remaining]

omit [LinearOrder α] in
private theorem remaining_erase (visited : Finset α) (v : α) :
    remaining (insert v visited) = (remaining visited).erase v := by
  ext z
  simp [remaining, Finset.mem_erase, Finset.mem_insert, not_or]

omit [Fintype α] [LinearOrder α] in
private theorem aSetMinus_nil (aSet : Finset α) :
    aSetMinus aSet ([] : List α) = aSet := by
  simp [aSetMinus]

omit [Fintype α] [LinearOrder α] in
private theorem aSetMinus_append (aSet : Finset α) (l₂ l₁ : List α) :
    aSetMinus aSet (l₂ ++ l₁) = aSetMinus (aSetMinus aSet l₁) l₂ := by
  ext z
  simp [mem_aSetMinus, List.mem_append]
  tauto

omit [Fintype α] [LinearOrder α] in
private theorem aSetMinus_cons (aSet : Finset α) (x : α) (l : List α) :
    aSetMinus aSet (x :: l) = aSetMinus (aSet.erase x) l := by
  ext z
  simp [mem_aSetMinus, Finset.mem_erase]
  tauto

private theorem dfsFinish_already_visited {g : Digraph α} :
    ∀ (fuel : Nat) (visited : Finset α) (finish : List α) (v : α),
      v ∈ visited → dfsFinish g fuel visited finish v = (visited, finish) := by
  intro fuel visited finish v hv
  cases fuel with
  | zero => rfl
  | succ _ => simp [dfsFinish, hv]

/-- MathComp `pdfs_correct`: one `dfsFinish` step yields a tsorted prefix of newly
    finished vertices, synced with the visited set. -/
private theorem dfsFinish_tsorted {g : Digraph α} :
    ∀ (fuel : Nat) (visited : Finset α) (finish : List α) (v : α),
      Fintype.card α ≤ fuel + visited.card →
      (∀ x ∈ finish, x ∈ visited) →
      finish.Nodup →
      v ∉ visited →
        ∃ mid,
          (dfsFinish g fuel visited finish v).2 = mid ++ finish ∧
            remaining (dfsFinish g fuel visited finish v).1 =
              aSetMinus (remaining visited) mid ∧
            v ∈ mid ∧
            (∀ x ∈ mid, x ∉ visited) ∧
            TSorted g (remaining visited) mid ∧
            (∀ y, y ∈ mid → ReachIn g (remaining visited) v y) := by
  intro fuel
  induction fuel with
  | zero =>
    intro visited finish v hcard _hsub _hnd hnotin
    have : visited = Finset.univ :=
      Finset.eq_univ_of_card _
        (Nat.le_antisymm (Finset.card_le_univ _) (by simpa using hcard))
    exact (hnotin (by simp [this])).elim
  | succ fuel ih =>
    intro visited finish v hcard hsub hnd hnotin
    simp only [dfsFinish, hnotin, ↓reduceIte]
    set rem0 : Finset α := (remaining visited).erase v
    have hrem0 : remaining (insert v visited) = rem0 := remaining_erase visited v
    have hcard0 : Fintype.card α ≤ fuel + (insert v visited).card := by
      rw [Finset.card_insert_of_notMem hnotin]
      omega
    have hsub0 : ∀ x ∈ finish, x ∈ insert v visited := fun x hx =>
      Finset.mem_insert_of_mem (hsub x hx)
    -- Fold over successors: mid syncs remaining with rem0.
    have fold_inv :
        ∀ (l : List α) (accVis : Finset α) (accFin : List α),
          (∀ y ∈ l, y ∈ g.succ v) →
          (∀ x ∈ accFin, x ∈ accVis) →
          accFin.Nodup →
          Fintype.card α ≤ fuel + accVis.card →
          insert v visited ⊆ accVis →
          (∃ mid,
            accFin = mid ++ finish ∧
              remaining accVis = aSetMinus rem0 mid ∧
              TSorted g rem0 mid ∧
              (∀ y ∈ mid, ReachIn g rem0 v y) ∧
              (∀ y ∈ mid, y ∉ visited) ∧
              v ∉ mid) →
          ∃ mid,
            (l.foldl (fun ⟨vis, fin⟩ u => dfsFinish g fuel vis fin u)
                (accVis, accFin)).2 =
              mid ++ finish ∧
              remaining
                  (l.foldl (fun ⟨vis, fin⟩ u => dfsFinish g fuel vis fin u)
                    (accVis, accFin)).1 =
                aSetMinus rem0 mid ∧
              TSorted g rem0 mid ∧
              (∀ y ∈ mid, ReachIn g rem0 v y) ∧
              (∀ y ∈ mid, y ∉ visited) ∧
              v ∉ mid := by
      intro l accVis accFin hsuccA hsubA hndA hcardA haccVis ⟨mid, hfinA, hsyncA, htsA,
        hreachA, hfreshA, hvmidA⟩
      induction l generalizing accVis accFin mid with
      | nil =>
        exact ⟨mid, hfinA, hsyncA, htsA, hreachA, hfreshA, hvmidA⟩
      | cons u us ihl =>
        simp only [List.foldl]
        have hu_succ : u ∈ g.succ v := hsuccA u List.mem_cons_self
        have hsucc' : ∀ y ∈ us, y ∈ g.succ v := fun y hy =>
          hsuccA y (List.mem_cons_of_mem u hy)
        by_cases hu : u ∈ accVis
        · have hdfs : dfsFinish g fuel accVis accFin u = (accVis, accFin) :=
            dfsFinish_already_visited fuel accVis accFin u hu
          rw [hdfs]
          exact ihl accVis accFin hsucc' hsubA hndA hcardA haccVis mid
            hfinA hsyncA htsA hreachA hfreshA hvmidA
        · rcases ih accVis accFin u hcardA hsubA hndA hu with
            ⟨mid_u, hfin_u, hsync_u, hu_mid, hfresh_u, hts_u, hreach_u⟩
          have hsub' : ∀ x ∈ (dfsFinish g fuel accVis accFin u).2,
              x ∈ (dfsFinish g fuel accVis accFin u).1 := by
            intro x hx
            rcases dfsFinish_finish_mem_visited fuel accVis accFin u x hx with hOld | hNew
            · exact dfsFinish_visited_mono fuel accVis accFin u (hsubA x hOld)
            · exact hNew
          have hnd' : (dfsFinish g fuel accVis accFin u).2.Nodup :=
            dfsFinish_nodup fuel accVis accFin u hsubA hndA
          have hcard' : Fintype.card α ≤ fuel + (dfsFinish g fuel accVis accFin u).1.card := by
            have : accVis.card ≤ (dfsFinish g fuel accVis accFin u).1.card :=
              Finset.card_le_card (dfsFinish_visited_mono fuel accVis accFin u)
            omega
          have hacc' : insert v visited ⊆ (dfsFinish g fuel accVis accFin u).1 :=
            Finset.Subset.trans haccVis (dfsFinish_visited_mono fuel accVis accFin u)
          have hu_ne_v : u ≠ v := fun h => hu (haccVis (by simp [h]))
          have hu_unvis : u ∉ visited := fun h =>
            hu (haccVis (Finset.mem_insert_of_mem h))
          have hu_rem0 : u ∈ rem0 :=
            Finset.mem_erase.mpr ⟨hu_ne_v, mem_remaining.mpr hu_unvis⟩
          have hedge : ReachIn g rem0 v u :=
            ReachIn.tail hu_succ hu_rem0 ReachIn.refl
          have rem_sub : remaining accVis ⊆ rem0 := by
            intro z hz
            have : z ∈ aSetMinus rem0 mid := by rwa [← hsyncA]
            exact (mem_aSetMinus.mp this).1
          have hts_u' : TSorted g (aSetMinus rem0 mid) mid_u :=
            TSorted.congr (fun z => by rw [hsyncA]) hts_u
          have hts_new : TSorted g rem0 (mid_u ++ mid) := tsorted_cat htsA hts_u'
          have hfin_new : (dfsFinish g fuel accVis accFin u).2 = (mid_u ++ mid) ++ finish := by
            rw [hfin_u, hfinA, List.append_assoc]
          have hsync_new :
              remaining (dfsFinish g fuel accVis accFin u).1 =
                aSetMinus rem0 (mid_u ++ mid) := by
            rw [hsync_u, hsyncA, aSetMinus_append]
          have hreach_new : ∀ y ∈ mid_u ++ mid, ReachIn g rem0 v y := by
            intro y hy
            simp only [List.mem_append] at hy
            rcases hy with hyu | hy0
            · exact ReachIn_trans hedge (ReachIn_mono rem_sub (hreach_u y hyu))
            · exact hreachA y hy0
          have hfresh_new : ∀ y ∈ mid_u ++ mid, y ∉ visited := by
            intro y hy
            simp only [List.mem_append] at hy
            rcases hy with hyu | hy0
            · exact fun h => hfresh_u y hyu (haccVis (Finset.mem_insert_of_mem h))
            · exact hfreshA y hy0
          have hvmid_new : v ∉ mid_u ++ mid := by
            intro hv
            simp only [List.mem_append] at hv
            rcases hv with hv | hv
            · exact hfresh_u v hv (haccVis (Finset.mem_insert_self v visited))
            · exact hvmidA hv
          exact ihl (dfsFinish g fuel accVis accFin u).1
            (dfsFinish g fuel accVis accFin u).2 hsucc' hsub' hnd' hcard' hacc'
            (mid_u ++ mid) hfin_new hsync_new hts_new hreach_new hfresh_new hvmid_new
    have hinit :
        ∃ mid,
          finish = mid ++ finish ∧
            remaining (insert v visited) = aSetMinus rem0 mid ∧
            TSorted g rem0 mid ∧
            (∀ y ∈ mid, ReachIn g rem0 v y) ∧
            (∀ y ∈ mid, y ∉ visited) ∧
            v ∉ mid :=
      ⟨[], by
        refine ⟨(List.nil_append finish).symm, ?_, TSorted.nil g rem0, ?_, ?_, ?_⟩
        · rw [hrem0, aSetMinus_nil]
        · intro y hy; cases hy
        · intro y hy; cases hy
        · intro h; cases h⟩
    rcases fold_inv (finsetList (g.succ v)) (insert v visited) finish
        (fun y hy => (finsetList_mem.mp hy)) hsub0 hnd hcard0 (Finset.Subset.refl _)
        hinit with ⟨mid, hfin, hsync, hts, hreach, hfresh, hvmid⟩
    refine ⟨v :: mid, ?_, ?_, List.mem_cons_self, ?_, ?_, ?_⟩
    · -- finish stack
      change v ::
          ((finsetList (g.succ v)).foldl (fun ⟨vis, fin⟩ u => dfsFinish g fuel vis fin u)
            (insert v visited, finish)).2 =
        v :: mid ++ finish
      rw [hfin, List.cons_append]
    · -- remaining sync after prepending v
      change remaining
          ((finsetList (g.succ v)).foldl (fun ⟨vis, fin⟩ u => dfsFinish g fuel vis fin u)
            (insert v visited, finish)).1 =
        aSetMinus (remaining visited) (v :: mid)
      rw [hsync, aSetMinus_cons]
    · intro x hx
      simp only [List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact hnotin
      · exact hfresh x hx
    · -- TSorted via tsorted_cons_r
      have hv_rem : v ∈ remaining visited := mem_remaining.mpr hnotin
      refine tsorted_cons_r hv_rem hvmid ?_ ?_ hts
      · intro y hy
        exact ReachIn_mono (Finset.erase_subset v (remaining visited)) (hreach y hy)
      · intro y hyS hyR hyne
        have hy_rem0 : y ∈ rem0 := Finset.mem_erase.mpr ⟨hyne, hyR⟩
        have hyVis :
            y ∈
              ((finsetList (g.succ v)).foldl (fun ⟨vis, fin⟩ u => dfsFinish g fuel vis fin u)
                (insert v visited, finish)).1 := by
          by_cases hfuel : 0 < fuel
          · exact dfsFinish_foldl_marks_members (g := g) fuel hfuel
              (finsetList (g.succ v)) (insert v visited) finish y (finsetList_mem.mpr hyS)
          · have hfuel0 : fuel = 0 := Nat.eq_zero_of_not_pos hfuel
            subst hfuel0
            have hcard' : Fintype.card α ≤ (insert v visited).card := by
              rw [Finset.card_insert_of_notMem hnotin]
              omega
            have huniv : insert v visited = Finset.univ :=
              Finset.eq_univ_of_card _
                (Nat.le_antisymm (Finset.card_le_univ _) hcard')
            have : rem0 = ∅ := by
              rw [← hrem0, huniv]
              simp [remaining]
            exact (Finset.notMem_empty y (this ▸ hy_rem0)).elim
        have hy_not_minus : y ∉ aSetMinus rem0 mid := by
          intro hyM
          have : y ∈ remaining
              ((finsetList (g.succ v)).foldl (fun ⟨vis, fin⟩ u => dfsFinish g fuel vis fin u)
                (insert v visited, finish)).1 := by rwa [hsync]
          exact (mem_remaining.mp this) hyVis
        by_contra hy_notin
        exact hy_not_minus (mem_aSetMinus.mpr ⟨hy_rem0, hy_notin⟩)
    · intro y hy
      simp only [List.mem_cons] at hy
      rcases hy with rfl | hy
      · exact ReachIn.refl
      · exact ReachIn_mono (Finset.erase_subset v (remaining visited)) (hreach y hy)

/-- Full `finishOrder` is tsorted on `univ` — via `finishOrderGo` + `dfsFinish_tsorted`. -/
private theorem finishOrderGo_tsorted {g : Digraph α} :
    ∀ (fuel : Nat) (visited : Finset α) (finish : List α),
      (∀ x, x ∈ visited ↔ x ∈ finish) →
      finish.Nodup →
      TSorted g Finset.univ finish →
      TSorted g Finset.univ (finishOrderGo g fuel visited finish) := by
  intro fuel
  induction fuel with
  | zero =>
    intro visited finish _hsync _hnd hts
    simpa [finishOrderGo] using hts
  | succ fuel ih =>
    intro visited finish hsync hnd hts
    cases hhead : (finsetList (Finset.univ.filter (fun v => v ∉ visited))).head? with
    | none =>
      have : finishOrderGo g (fuel + 1) visited finish = finish := by
        simp only [finishOrderGo, hhead]
      rwa [this]
    | some v =>
      have hv_unvis : v ∉ visited := by
        have := finsetList_mem.mp (list_mem_of_head?_eq_some hhead)
        simpa using this
      have hsub : ∀ x ∈ finish, x ∈ visited := fun x hx => (hsync x).mpr hx
      have hcard : Fintype.card α ≤ Fintype.card α + visited.card :=
        Nat.le_add_right _ _
      rcases dfsFinish_tsorted (g := g) (Fintype.card α) visited finish v
          hcard hsub hnd hv_unvis with
        ⟨mid, hfin, hsync_rem, hv_mid, hfresh, hts_mid, _hreach⟩
      let step := dfsFinish g (Fintype.card α) visited finish v
      have hstep2 : step.2 = mid ++ finish := by simpa [step] using hfin
      have hrem_eq : remaining visited = aSetMinus Finset.univ finish := by
        ext z
        simp only [mem_remaining, mem_aSetMinus, Finset.mem_univ, true_and]
        exact (not_iff_not.mpr (hsync z))
      have hts_mid' : TSorted g (aSetMinus Finset.univ finish) mid :=
        TSorted.congr (fun z => by rw [hrem_eq]) hts_mid
      have hts' : TSorted g Finset.univ step.2 := by
        rw [hstep2]
        exact tsorted_cat hts hts_mid'
      have hnd' : step.2.Nodup := dfsFinish_nodup (Fintype.card α) visited finish v hsub hnd
      have hsync' : ∀ y, y ∈ step.1 ↔ y ∈ step.2 :=
        dfsFinish_sync (Fintype.card α) visited finish v hsync
      have hgo : finishOrderGo g (fuel + 1) visited finish =
          finishOrderGo g fuel step.1 step.2 := by
        dsimp [step]; simp only [finishOrderGo, hhead]
      rw [hgo]
      exact ih step.1 step.2 hsync' hnd' hts'

private theorem finishOrder_tsorted (g : Digraph α) :
    TSorted g Finset.univ (finishOrder g) := by
  simpa [finishOrder] using
    finishOrderGo_tsorted (Fintype.card α + 1) ∅ []
      (by intro y; simp) List.nodup_nil (TSorted.nil g Finset.univ)

omit [LinearOrder α] in
/-- Head characterization (MathComp `tsorted_symconnect`): among vertices in a
    covering tsorted list, MutualIn with seed `s` (min-finish among `fin`) iff
    `ReachIn` to `s`. When `aSet = univ` and `fin` covers, this is Mutual ↔ Reach. -/
private theorem tsorted_head_mutual {g : Digraph α} {aSet : Finset α}
    {fin : List α} {s : α}
    (hts : TSorted g aSet fin)
    (hs : s ∈ fin)
    (hhead : ∀ z ∈ fin, finishBefore fin s z) :
    ∀ w ∈ fin, MutualIn g aSet s w ↔ ReachIn g aSet w s := by
  intro w hw
  constructor
  · intro hm
    exact hm.2
  · intro hreach
    obtain ⟨c, hcan, hbefore⟩ := hts.can_before w s hw hreach
    have hs_le : finishBefore fin s c := hhead c hcan.1
    have heq : List.idxOf c fin = List.idxOf s fin :=
      Nat.le_antisymm hbefore hs_le
    have hc_eq : c = s := eq_of_idxOf_eq hcan.1 hs heq
    subst hc_eq
    exact MutualIn_symm hcan.2.1

/-- Fresh transpose-collect from a head seed among remaining yields Mutual partners.

Requires the head characterization on remaining vertices (`univ \ visited` as list
`fin`), not merely Mutual-closure of `visited` (false without finish-order hyps). -/
private theorem collect_transpose_mutual {g : Digraph α}
    {fuel : Nat} {visited : Finset α} {fin : List α} {s w : α}
    (hts : TSorted g Finset.univ fin)
    (hrem : ∀ z, z ∈ fin ↔ z ∉ visited)
    (hs : s ∈ fin)
    (hhead : ∀ z ∈ fin, finishBefore fin s z)
    (_hs_unvis : s ∉ visited)
    (hw : w ∈ (dfsCollect g.transpose fuel visited [] s).2) :
    Mutual g s w := by
  have hw_fresh : w ∉ visited :=
    (dfsCollect_fresh_props (g := g.transpose) fuel visited s).2.1 w hw
  have hw_fin : w ∈ fin := (hrem w).mpr hw_fresh
  have hreach_t : Reach g.transpose s w := by
    have := dfsCollect_mem_reach (g := g.transpose) fuel visited [] s w hw
    simpa using this
  have hreach : Reach g w s := (Reach_transpose (g := g)).mp hreach_t
  have hreachIn : ReachIn g Finset.univ w s := (ReachIn_univ (g := g)).mpr hreach
  have hmutIn : MutualIn g Finset.univ s w :=
    (tsorted_head_mutual hts hs hhead w hw_fin).mpr hreachIn
  exact (MutualIn_univ (g := g)).mp hmutIn

omit [LinearOrder α] in
/-- Unrestricted head characterization when `fin` is tsorted on `univ` and covers. -/
private theorem tsorted_head_mutual_univ {g : Digraph α} {fin : List α} {s : α}
    (hts : TSorted g Finset.univ fin)
    (hcover : ∀ z, z ∈ fin)
    (hs : s ∈ fin)
    (hhead : ∀ z ∈ fin, finishBefore fin s z) :
    ∀ w, Mutual g s w ↔ Reach g w s := by
  intro w
  have hw : w ∈ fin := hcover w
  constructor
  · intro hm
    exact hm.2
  · intro hr
    have hmutIn : MutualIn g Finset.univ s w :=
      (tsorted_head_mutual hts hs hhead w hw).mpr ((ReachIn_univ (g := g)).mpr hr)
    exact (MutualIn_univ (g := g)).mp hmutIn

omit [LinearOrder α] in
/-- Reachability into `visited` is impossible from outside under `hno`, so unrestricted
    `Reach` between outsiders is `ReachIn` on `remaining`. -/
private theorem ReachIn_remaining_of_Reach {g : Digraph α} {visited : Finset α} {a b : α}
    (hno : ∀ x y, x ∉ visited → y ∈ visited → ¬Reach g x y)
    (ha : a ∉ visited) (hreach : Reach g a b) :
    b ∉ visited ∧ ReachIn g (remaining visited) a b := by
  induction hreach with
  | refl => exact ⟨ha, ReachIn.refl⟩
  | @tail a c b hsuc r ih =>
    have hc : c ∉ visited := fun hc =>
      hno a c ha hc (Reach.tail hsuc Reach.refl)
    have ⟨hb, hr⟩ := ih hc
    exact ⟨hb, ReachIn.tail hsuc (mem_remaining.mpr hc) hr⟩

/-! #### Completeness of `dfsCollect` (MathComp `dfs_pathP` / `pdfs_connect`) -/

/-- Explicit path witness for `ReachIn`: vertices after the start, each in `s`. -/
private inductive IsReachPath (g : Digraph α) (s : Finset α) : α → List α → Prop
  | nil {a} : IsReachPath g s a []
  | cons {a b p} : b ∈ g.succ a → b ∈ s → IsReachPath g s b p →
      IsReachPath g s a (b :: p)

private def pathEnd (a : α) (p : List α) : α :=
  p.getLastD a

omit [Fintype α] [DecidableEq α] [LinearOrder α] in
private theorem pathEnd_cons (a b : α) (p : List α) :
    pathEnd a (b :: p) = pathEnd b p := by
  cases p with
  | nil => rfl
  | cons _ _ => rfl

omit [Fintype α] [DecidableEq α] [LinearOrder α] in
private theorem pathEnd_append_cons (a z : α) (p₁ p₂ : List α) :
    pathEnd a (p₁ ++ z :: p₂) = pathEnd z p₂ := by
  induction p₁ generalizing a with
  | nil =>
    cases p₂ with
    | nil => rfl
    | cons _ _ => rfl
  | cons b bs ih =>
    rw [List.cons_append, pathEnd_cons, ih]

omit [LinearOrder α] in
private theorem ReachIn_of_IsReachPath {g : Digraph α} {s : Finset α} {a : α} {p : List α}
    (hp : IsReachPath g s a p) : ReachIn g s a (pathEnd a p) := by
  induction hp with
  | nil => exact ReachIn.refl
  | cons hsuc hin _hp ih =>
    rw [pathEnd_cons]
    exact ReachIn.tail hsuc hin ih

omit [LinearOrder α] in
private theorem exists_IsReachPath_of_ReachIn {g : Digraph α} {s : Finset α} {a b : α}
    (h : ReachIn g s a b) :
    ∃ p, IsReachPath g s a p ∧ pathEnd a p = b := by
  induction h with
  | refl => exact ⟨[], IsReachPath.nil, rfl⟩
  | tail hsuc hin _r ih =>
    obtain ⟨p, hp, he⟩ := ih
    refine ⟨_ :: p, IsReachPath.cons hsuc hin hp, ?_⟩
    rw [pathEnd_cons, he]

omit [LinearOrder α] in
private theorem IsReachPath_middle {g : Digraph α} {s : Finset α} {a z : α}
    {p₁ p₂ : List α} (hp : IsReachPath g s a (p₁ ++ z :: p₂)) :
    IsReachPath g s z p₂ := by
  induction p₁ generalizing a with
  | nil =>
    cases hp with
    | cons _ _ hp' => exact hp'
  | cons _b _bs ih =>
    cases hp with
    | cons _ _ hp' => exact ih hp'

omit [LinearOrder α] in
private theorem IsReachPath_erase {g : Digraph α} {s : Finset α} {x a : α} {p : List α}
    (hp : IsReachPath g s a p) (ha : a ≠ x) (hp_ne : ∀ z ∈ p, z ≠ x) :
    IsReachPath g (s.erase x) a p := by
  induction hp with
  | nil => exact IsReachPath.nil
  | @cons a b p hsuc hin hp ih =>
    have hb : b ≠ x := hp_ne b List.mem_cons_self
    have hp_ne' : ∀ z ∈ p, z ≠ x := fun z hz => hp_ne z (List.mem_cons_of_mem b hz)
    exact IsReachPath.cons hsuc (Finset.mem_erase.mpr ⟨hb, hin⟩) (ih hb hp_ne')

omit [LinearOrder α] in
/-- Non-trivial `ReachIn` from `x` has a first edge into `s.erase x` (simple-path). -/
private theorem ReachIn_exists_first_edge {g : Digraph α} {s : Finset α} {x w : α}
    (h : ReachIn g s x w) (hne : w ≠ x) :
    ∃ u, u ∈ g.succ x ∧ u ∈ s ∧ u ≠ x ∧ ReachIn g (s.erase x) u w := by
  obtain ⟨p, hp, hpe⟩ := exists_IsReachPath_of_ReachIn h
  have aux :
      ∀ (n : Nat) (q : List α),
        q.length = n → IsReachPath g s x q → pathEnd x q = w →
          ∃ u, u ∈ g.succ x ∧ u ∈ s ∧ u ≠ x ∧ ReachIn g (s.erase x) u w := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro q hlen hq hpw
      match q, hq with
      | [], IsReachPath.nil =>
        exact (hne (by simpa [pathEnd] using hpw.symm)).elim
      | u :: rest, IsReachPath.cons hsuc hin hp' =>
        have hlen_rest : rest.length < n := by
          simp only [List.length_cons] at hlen
          omega
        by_cases hu : u = x
        · subst hu
          exact ih rest.length hlen_rest rest rfl hp' (by simpa [pathEnd_cons] using hpw)
        · by_cases hx_rest : x ∈ rest
          · obtain ⟨pre, post, hsplit⟩ := List.append_of_mem hx_rest
            have hp_mid : IsReachPath g s x post := by
              have : IsReachPath g s u (pre ++ x :: post) := by simpa [hsplit] using hp'
              exact IsReachPath_middle this
            have hlen_post : post.length < n := by
              simp only [hsplit, List.length_append, List.length_cons] at hlen_rest
              omega
            have hpw_post : pathEnd x post = w := by
              have : pathEnd u rest = w := by simpa [pathEnd_cons] using hpw
              simpa [hsplit, pathEnd_append_cons] using this
            exact ih post.length hlen_post post rfl hp_mid hpw_post
          · refine ⟨u, hsuc, hin, hu, ?_⟩
            have hp_ne : ∀ z ∈ rest, z ≠ x := fun z hz hzx =>
              hx_rest (by simpa [hzx] using hz)
            have herase : IsReachPath g (s.erase x) u rest :=
              IsReachPath_erase hp' hu hp_ne
            have : pathEnd u rest = w := by simpa [pathEnd_cons] using hpw
            simpa [this] using ReachIn_of_IsReachPath herase
  exact aux p.length p rfl hp hpe

private theorem dfsCollect_already_visited {g : Digraph α} :
    ∀ (fuel : Nat) (visited : Finset α) (comp : List α) (v : α),
      v ∈ visited → dfsCollect g fuel visited comp v = (visited, comp) := by
  intro fuel visited comp v hv
  cases fuel with
  | zero => rfl
  | succ _ => simp [dfsCollect, hv]

omit [LinearOrder α] in
private theorem ReachIn_endpoint {g : Digraph α} {s : Finset α} {a b : α}
    (h : ReachIn g s a b) : b = a ∨ b ∈ s := by
  induction h with
  | refl => exact Or.inl rfl
  | tail _ hin _r ih =>
    rcases ih with rfl | hb
    · exact Or.inr hin
    · exact Or.inr hb

omit [LinearOrder α] in
private theorem remaining_mono {visited visited' : Finset α} (h : visited ⊆ visited') :
    remaining visited' ⊆ remaining visited := by
  intro z hz
  exact mem_remaining.mpr fun hzV => (mem_remaining.mp hz) (h hzV)

omit [LinearOrder α] in
/-- A `ReachIn` in `s` either stays in `t ⊆ s`, or first hits `s \ t`. -/
private theorem ReachIn_of_subset_or_hit {g : Digraph α} {s t : Finset α} {a b : α}
    (_hsub : t ⊆ s) (h : ReachIn g s a b) :
    ReachIn g t a b ∨
      ∃ z, z ∈ s ∧ z ∉ t ∧ ReachIn g s a z ∧ ReachIn g s z b := by
  induction h with
  | refl => exact Or.inl ReachIn.refl
  | @tail a c d hsuc hin r ih =>
    by_cases hc : c ∈ t
    · rcases ih with hE | ⟨z, zs, zt, hz1, hz2⟩
      · exact Or.inl (ReachIn.tail hsuc hc hE)
      · exact Or.inr ⟨z, zs, zt, ReachIn.tail hsuc hin hz1, hz2⟩
    · exact Or.inr ⟨c, hin, hc, ReachIn.tail hsuc hin ReachIn.refl, r⟩

/-- Like `dfsCollect_mem_reach`, restricted to the start `remaining` set. -/
private theorem dfsCollect_mem_reachIn {g : Digraph α} :
    ∀ fuel visited comp root w,
      (∀ x ∈ comp, x ∈ visited) →
      w ∈ (dfsCollect g fuel visited comp root).2 →
        w ∈ comp ∨ ReachIn g (remaining visited) root w := by
  intro fuel
  induction fuel with
  | zero =>
    intro visited comp root w _hsub hw
    simp only [dfsCollect] at hw
    exact Or.inl hw
  | succ fuel ih =>
    intro visited comp root w hsub hw
    by_cases hroot : root ∈ visited
    · simp only [dfsCollect, hroot, ite_true] at hw
      exact Or.inl hw
    · simp only [dfsCollect, hroot, ite_false] at hw
      have fold_mem :
          ∀ (l : List α) (accVis : Finset α) (accComp : List α),
            visited ⊆ accVis →
            (∀ x ∈ accComp, x ∈ accVis) →
            (∀ u ∈ l, u ∈ g.succ root) →
            (∀ x ∈ accComp, x ∈ comp ∨ ReachIn g (remaining visited) root x) →
            w ∈ (l.foldl (fun ⟨vis, c⟩ u => dfsCollect g fuel vis c u)
                  (accVis, accComp)).2 →
              w ∈ comp ∨ ReachIn g (remaining visited) root w := by
        intro l accVis accComp haccVis hsubA hsuccA hacc hw'
        induction l generalizing accVis accComp with
        | nil =>
          exact hacc w hw'
        | cons u us ihl =>
          simp only [List.foldl] at hw'
          have hu_succ : u ∈ g.succ root := hsuccA u List.mem_cons_self
          refine ihl (dfsCollect g fuel accVis accComp u).1
            (dfsCollect g fuel accVis accComp u).2 ?_ ?_ ?_ ?_ hw'
          · exact Finset.Subset.trans haccVis
              (dfsCollect_visited_mono fuel accVis accComp u)
          · exact fun x hx =>
              dfsCollect_comp_subset_visited fuel accVis accComp u hsubA x hx
          · exact fun v hv => hsuccA v (List.mem_cons_of_mem u hv)
          · intro x hx
            by_cases hu : u ∈ accVis
            · have heq : dfsCollect g fuel accVis accComp u = (accVis, accComp) :=
                dfsCollect_already_visited fuel accVis accComp u hu
              rw [heq] at hx
              exact hacc x hx
            · rcases ih accVis accComp u x hsubA hx with hxAcc | hxReach
              · exact hacc x hxAcc
              · have hu_rem : u ∈ remaining visited :=
                  mem_remaining.mpr fun h => hu (haccVis h)
                exact Or.inr (ReachIn.tail hu_succ hu_rem
                  (ReachIn_mono (remaining_mono haccVis) hxReach))
      refine fold_mem (finsetList (g.succ root)) (insert root visited) (root :: comp)
          (Finset.subset_insert _ _) ?_
          (fun y hy => finsetList_mem.mp hy) ?_ hw
      · intro x hx
        simp only [List.mem_cons] at hx
        rcases hx with rfl | hx
        · exact Finset.mem_insert_self _ _
        · exact Finset.mem_insert_of_mem (hsub x hx)
      · intro x hx
        simp only [List.mem_cons] at hx
        rcases hx with rfl | hx
        · exact Or.inr ReachIn.refl
        · exact Or.inl hx

/-- `dfsCollect` finds every vertex reachable in the remaining set (enough fuel).
    Generalized to a nonempty initial `comp` covered by `visited`. -/
private theorem dfsCollect_reachIn_mem_comp {g : Digraph α} :
    ∀ (fuel : Nat) (visited : Finset α) (comp : List α) (root w : α),
      Fintype.card α ≤ fuel + visited.card →
      (∀ x ∈ comp, x ∈ visited) →
      root ∉ visited →
      ReachIn g (remaining visited) root w →
      w ∈ (dfsCollect g fuel visited comp root).2 := by
  intro fuel
  induction fuel with
  | zero =>
    intro visited comp root w hcard _hsub hroot _
    have : visited = Finset.univ :=
      Finset.eq_univ_of_card _
        (Nat.le_antisymm (Finset.card_le_univ _) (by simpa using hcard))
    exact (hroot (by simp [this])).elim
  | succ fuel ih =>
    intro visited comp root w hcard hsub hroot hreach
    simp only [dfsCollect, hroot, ↓reduceIte]
    have hcard0 : Fintype.card α ≤ fuel + (insert root visited).card := by
      rw [Finset.card_insert_of_notMem hroot]
      omega
    have hsub0 : ∀ x ∈ root :: comp, x ∈ insert root visited := by
      intro x hx
      simp only [List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact Finset.mem_insert_self _ _
      · exact Finset.mem_insert_of_mem (hsub x hx)
    have fold_mem :
        ∀ (l : List α) (accVis : Finset α) (accComp : List α),
          Fintype.card α ≤ fuel + accVis.card →
          (∀ x ∈ accComp, x ∈ accVis) →
          (∀ x ∈ accVis, x ∈ visited ∨ x ∈ accComp) →
          insert root visited ⊆ accVis →
          (w ∈ accComp ∨
            ∃ u ∈ l, u ∉ accVis ∧ ReachIn g (remaining accVis) u w) →
          w ∈ (l.foldl (fun ⟨vis, c⟩ u => dfsCollect g fuel vis c u)
                (accVis, accComp)).2 := by
      intro l accVis accComp hcardA hsubA hsyncA haccA hwit
      induction l generalizing accVis accComp with
      | nil =>
        rcases hwit with hw | ⟨_, hu, _⟩
        · exact hw
        · cases hu
      | cons u us ihl =>
        simp only [List.foldl]
        set step := dfsCollect g fuel accVis accComp u
        have hsub' : ∀ x ∈ step.2, x ∈ step.1 :=
          fun x hx => dfsCollect_comp_subset_visited fuel accVis accComp u hsubA x hx
        have hcard' : Fintype.card α ≤ fuel + step.1.card := by
          have : accVis.card ≤ step.1.card :=
            Finset.card_le_card (dfsCollect_visited_mono fuel accVis accComp u)
          omega
        have hsync' : ∀ x ∈ step.1, x ∈ visited ∨ x ∈ step.2 := by
          intro x hx
          rcases dfsCollect_visited_subset_union fuel accVis accComp u hsubA x hx with
            hOld | hNew
          · rcases hsyncA x hOld with hV | hC
            · exact Or.inl hV
            · exact Or.inr (dfsCollect_preserves_mem fuel accVis accComp u x hC)
          · exact Or.inr hNew
        have hmono_vis : accVis ⊆ step.1 :=
          dfsCollect_visited_mono fuel accVis accComp u
        have hacc' : insert root visited ⊆ step.1 :=
          Finset.Subset.trans haccA hmono_vis
        refine ihl step.1 step.2 hcard' hsub' hsync' hacc' ?_
        rcases hwit with hw | ⟨u0, hu0l, hu0unvis, hu0reach⟩
        · exact Or.inl (dfsCollect_preserves_mem fuel accVis accComp u w hw)
        · simp only [List.mem_cons] at hu0l
          rcases hu0l with hu0u | hu0us
          · -- Witness is the head (hence unvisited by the witness).
            subst hu0u
            exact Or.inl (ih accVis accComp u0 w hcardA hsubA hu0unvis hu0reach)
          · -- Witness in the tail.
            have hrem_sub : remaining step.1 ⊆ remaining accVis := remaining_mono hmono_vis
            rcases ReachIn_of_subset_or_hit hrem_sub hu0reach with hE | ⟨z, hz_s, hz_t, _hz_to, hz_from⟩
            · by_cases hu0_vis' : u0 ∈ step.1
              · -- `u0` collected while exploring the head; finish `w` via the head.
                have hu0_comp : u0 ∈ step.2 := by
                  rcases hsync' u0 hu0_vis' with hV | hC
                  · exact (hu0unvis (haccA (Finset.mem_insert_of_mem hV))).elim
                  · exact hC
                by_cases hu_vis : u ∈ accVis
                · have heq : dfsCollect g fuel accVis accComp u = (accVis, accComp) :=
                    dfsCollect_already_visited fuel accVis accComp u hu_vis
                  have : u0 ∈ accVis := by
                    change u0 ∈ (dfsCollect g fuel accVis accComp u).1 at hu0_vis'
                    simpa [heq] using hu0_vis'
                  exact (hu0unvis this).elim
                · have hu0_from_u : ReachIn g (remaining accVis) u u0 := by
                    rcases dfsCollect_mem_reachIn fuel accVis accComp u u0 hsubA hu0_comp with
                      hIn | hR
                    · exact (hu0unvis (hsubA u0 hIn)).elim
                    · exact hR
                  exact Or.inl (ih accVis accComp u w hcardA hsubA hu_vis
                    (ReachIn_trans hu0_from_u hu0reach))
              · exact Or.inr ⟨u0, hu0us, hu0_vis', hE⟩
            · -- Path from `u0` to `w` hits the newly visited set at `z`.
              have hz_step : z ∈ step.1 := by
                simpa [mem_remaining] using hz_t
              have hz_comp : z ∈ step.2 := by
                rcases hsync' z hz_step with hV | hC
                · exact ((mem_remaining.mp hz_s) (haccA (Finset.mem_insert_of_mem hV))).elim
                · exact hC
              by_cases hu_vis : u ∈ accVis
              · have heq : dfsCollect g fuel accVis accComp u = (accVis, accComp) :=
                  dfsCollect_already_visited fuel accVis accComp u hu_vis
                have : z ∈ accVis := by
                  change z ∈ (dfsCollect g fuel accVis accComp u).1 at hz_step
                  simpa [heq] using hz_step
                exact ((mem_remaining.mp hz_s) this).elim
              · have hz_from_u : ReachIn g (remaining accVis) u z := by
                  rcases dfsCollect_mem_reachIn fuel accVis accComp u z hsubA hz_comp with
                    hIn | hR
                  · exact ((mem_remaining.mp hz_s) (hsubA z hIn)).elim
                  · exact hR
                exact Or.inl (ih accVis accComp u w hcardA hsubA hu_vis
                  (ReachIn_trans hz_from_u hz_from))
    refine fold_mem (finsetList (g.succ root)) (insert root visited) (root :: comp)
      hcard0 hsub0 ?_ (Finset.Subset.refl _) ?_
    · intro x hx
      simp only [Finset.mem_insert] at hx
      rcases hx with rfl | hx
      · exact Or.inr List.mem_cons_self
      · exact Or.inl hx
    · by_cases hweq : w = root
      · subst hweq
        exact Or.inl List.mem_cons_self
      · obtain ⟨u, hsuc, hu_rem, hu_ne, hu_reach⟩ :=
          ReachIn_exists_first_edge (s := remaining visited) hreach hweq
        have hu_unvis : u ∉ insert root visited := by
          simp only [Finset.mem_insert, not_or]
          exact ⟨hu_ne, mem_remaining.mp hu_rem⟩
        refine Or.inr ⟨u, finsetList_mem.mpr hsuc, hu_unvis, ?_⟩
        rwa [← remaining_erase] at hu_reach

/-- Specialization: fresh collect from `root`. -/
private theorem dfsCollect_reachIn_mem {g : Digraph α} :
    ∀ (fuel : Nat) (visited : Finset α) (root w : α),
      Fintype.card α ≤ fuel + visited.card →
      root ∉ visited →
      ReachIn g (remaining visited) root w →
      w ∈ (dfsCollect g fuel visited [] root).2 := by
  intro fuel visited root w hcard hroot hreach
  exact dfsCollect_reachIn_mem_comp fuel visited [] root w hcard
    (by intro x hx; cases hx) hroot hreach

/-- If `s` is earliest in `finishOrder` among unvisited and `visited` admits no
    external reach-in, transpose-collect from `s` yields Mutual partners. -/
private theorem mutual_of_finishOrder_collect {g : Digraph α}
    {fuel : Nat} {visited : Finset α} {s w : α}
    (hts : TSorted g Finset.univ (finishOrder g))
    (hno : ∀ x y, x ∉ visited → y ∈ visited → ¬Reach g x y)
    (hs_min : ∀ z, z ∉ visited → finishBefore (finishOrder g) s z)
    (_hs_unvis : s ∉ visited)
    (hw : w ∈ (dfsCollect g.transpose fuel visited [] s).2) :
    Mutual g s w := by
  have hw_fresh : w ∉ visited :=
    (dfsCollect_fresh_props (g := g.transpose) fuel visited s).2.1 w hw
  have hreach_t : Reach g.transpose s w := by
    have := dfsCollect_mem_reach (g := g.transpose) fuel visited [] s w hw
    simpa using this
  have hreach : Reach g w s := (Reach_transpose (g := g)).mp hreach_t
  have hreachIn : ReachIn g Finset.univ w s := (ReachIn_univ (g := g)).mpr hreach
  obtain ⟨c, hcan, hbefore⟩ :=
    hts.can_before w s (finishOrder_mem g w) hreachIn
  have hc_unvis : c ∉ visited := by
    intro hc
    have hm : Mutual g c w :=
      Mutual_symm ((MutualIn_univ (g := g)).mp hcan.2.1)
    exact hw_fresh (by
      have : Reach g w c := hm.2
      exact (hno w c hw_fresh hc this).elim)
  have hs_le : finishBefore (finishOrder g) s c := hs_min c hc_unvis
  have heq : List.idxOf c (finishOrder g) = List.idxOf s (finishOrder g) :=
    Nat.le_antisymm hbefore hs_le
  have hc_eq : c = s :=
    eq_of_idxOf_eq hcan.1 (finishOrder_mem g s) heq
  subst hc_eq
  exact Mutual_symm ((MutualIn_univ (g := g)).mp hcan.2.1)

omit [LinearOrder α] in
/-- Reverse a `ReachIn` path (targets stay in `s`; start must lie in `s`). -/
private theorem ReachIn_reverse {g : Digraph α} {s : Finset α} {a b : α}
    (h : ReachIn g s a b) (ha : a ∈ s) :
    ReachIn g.transpose s b a := by
  induction h with
  | refl => exact ReachIn.refl
  | @tail a c b hsuc hin r ih =>
    have ih' : ReachIn g.transpose s b c := ih hin
    have hedge : a ∈ g.transpose.succ c := by
      simpa [Digraph.transpose, Finset.mem_filter] using hsuc
    exact ReachIn_trans ih' (ReachIn.tail hedge ha ReachIn.refl)

/-- Reach into a finish-order head among remaining implies Mutual. -/
private theorem mutual_of_reach_to_head {g : Digraph α} {visited : Finset α} {s x : α}
    (hts : TSorted g Finset.univ (finishOrder g))
    (hno : ∀ u v, u ∉ visited → v ∈ visited → ¬Reach g u v)
    (hs_min : ∀ z, z ∉ visited → finishBefore (finishOrder g) s z)
    (hs : s ∉ visited) (hx : x ∉ visited)
    (hr : Reach g x s) : Mutual g x s := by
  have hreachIn : ReachIn g Finset.univ x s := (ReachIn_univ (g := g)).mpr hr
  obtain ⟨c, hcan, hbefore⟩ :=
    hts.can_before x s (finishOrder_mem g x) hreachIn
  have hc_unvis : c ∉ visited := by
    intro hc
    have hm : Mutual g c x :=
      Mutual_symm ((MutualIn_univ (g := g)).mp hcan.2.1)
    exact hx (by
      have : Reach g x c := hm.2
      exact (hno x c hx hc this).elim)
  have hs_le : finishBefore (finishOrder g) s c := hs_min c hc_unvis
  have heq : List.idxOf c (finishOrder g) = List.idxOf s (finishOrder g) :=
    Nat.le_antisymm hbefore hs_le
  have hc_eq : c = s :=
    eq_of_idxOf_eq hcan.1 (finishOrder_mem g s) heq
  subst hc_eq
  exact (MutualIn_univ (g := g)).mp hcan.2.1

omit [Fintype α] [LinearOrder α] in
private theorem finishBefore_of_suffix {fin pre : List α} {s z : α} {vs : List α}
    (hnd : fin.Nodup) (hsplit : fin = pre ++ s :: vs) (hz : z ∈ s :: vs) :
    finishBefore fin s z := by
  have hs_notin_pre : s ∉ pre := by
    intro hsp
    have hnd' : (pre ++ s :: vs).Nodup := by rwa [← hsplit]
    have : (pre ++ s :: vs).count s ≥ 2 := by
      have h1 : 0 < pre.count s := List.count_pos_iff.mpr hsp
      have h2 : 0 < (s :: vs).count s := by simp [List.count_cons_self]
      simp only [List.count_append]
      omega
    have : (pre ++ s :: vs).count s ≤ 1 := List.nodup_iff_count_le_one.mp hnd' s
    omega
  change List.idxOf s fin ≤ List.idxOf z fin
  have hz_notin_pre : z ∉ pre := by
    intro hzp
    have hnd' : (pre ++ s :: vs).Nodup := by rwa [← hsplit]
    exact (List.nodup_append.mp hnd').2.2 z hzp z hz rfl
  rw [hsplit, List.idxOf_append_of_notMem hs_notin_pre,
    List.idxOf_append_of_notMem hz_notin_pre]
  have : List.idxOf s (s :: vs) ≤ List.idxOf z (s :: vs) := by
    rw [idxOf_cons_self_zero]
    exact Nat.zero_le _
  exact Nat.add_le_add_left this _

/-- `kosarajuGo` emits Mutual cliques; `visited` stays unreachable from outside. -/
private theorem kosarajuGo_sameScc_aux {g : Digraph α} :
    ∀ (fuel : Nat) (visited : Finset α) (finish : List α) (comps : List (List α)),
      (∀ c ∈ comps, ∀ a ∈ c, ∀ b ∈ c, Mutual g a b) →
      (∀ x y, x ∉ visited → y ∈ visited → ¬Reach g x y) →
      (∀ z, z ∉ visited → z ∈ finish) →
      (∃ pre, finishOrder g = pre ++ finish) →
      ∀ c ∈ kosarajuGo g fuel visited finish comps,
        ∀ a ∈ c, ∀ b ∈ c, Mutual g a b := by
  intro fuel
  induction fuel with
  | zero =>
    intro visited finish comps hcomps _hno _hcover _hsuf c hc a ha b hb
    simpa [kosarajuGo] using hcomps c hc a ha b hb
  | succ fuel ih =>
    intro visited finish comps hcomps hno hcover hsuf c hc a ha b hb
    cases finish with
    | nil =>
      simpa [kosarajuGo] using hcomps c hc a ha b hb
    | cons seed vs =>
      by_cases hseed : seed ∈ visited
      · have hc' : c ∈ kosarajuGo g fuel visited vs comps := by
          simpa [kosarajuGo, hseed] using hc
        refine ih visited vs comps hcomps hno ?_ ?_ c hc' a ha b hb
        · intro z hz
          have hz' := hcover z hz
          simp only [List.mem_cons] at hz'
          rcases hz' with rfl | hz'
          · exact (hz hseed).elim
          · exact hz'
        · obtain ⟨pre, hpre⟩ := hsuf
          exact ⟨pre ++ [seed], by simp [hpre]⟩
      · set step := dfsCollect g.transpose (Fintype.card α) visited [] seed
        set visited' := step.1
        set comp := step.2
        have hts := finishOrder_tsorted g
        obtain ⟨pre, hpre⟩ := hsuf
        have hs_min : ∀ z, z ∉ visited → finishBefore (finishOrder g) seed z := by
          intro z hz
          exact finishBefore_of_suffix (finishOrder_nodup g) hpre (hcover z hz)
        have hmut_comp : ∀ w ∈ comp, Mutual g seed w := fun w hw =>
          mutual_of_finishOrder_collect (g := g) (fuel := Fintype.card α) hts hno hs_min
            hseed hw
        have hcomps' : ∀ c ∈ comps ++ [comp], ∀ a ∈ c, ∀ b ∈ c, Mutual g a b := by
          intro c' hc' a' ha' b' hb'
          simp only [List.mem_append, List.mem_singleton] at hc'
          rcases hc' with hc' | rfl
          · exact hcomps c' hc' a' ha' b' hb'
          · exact Mutual_trans (Mutual_symm (hmut_comp a' ha')) (hmut_comp b' hb')
        have hcard : Fintype.card α ≤ Fintype.card α + visited.card := by omega
        have hno' : ∀ x y, x ∉ visited' → y ∈ visited' → ¬Reach g x y := by
          intro x y hx hy hreach
          rcases dfsCollect_fresh_visited_union (g := g.transpose) (Fintype.card α)
              visited seed y hy with hyOld | hyNew
          · exact hno x y (fun h => hx (dfsCollect_visited_mono (Fintype.card α)
              visited [] seed h)) hyOld hreach
          · have hmy : Mutual g seed y := hmut_comp y hyNew
            have hxs : Reach g x seed := Reach_trans hreach hmy.2
            have hx_old : x ∉ visited := fun h =>
              hx (dfsCollect_visited_mono (Fintype.card α) visited [] seed h)
            have hmut_xs : Mutual g x seed :=
              mutual_of_reach_to_head hts hno hs_min hseed hx_old hxs
            have ⟨_, hreachIn_xs⟩ :=
              ReachIn_remaining_of_Reach hno hx_old hmut_xs.1
            have hx_rem : x ∈ remaining visited := mem_remaining.mpr hx_old
            have hreachIn_t : ReachIn g.transpose (remaining visited) seed x :=
              ReachIn_reverse hreachIn_xs hx_rem
            have hx_comp : x ∈ comp :=
              dfsCollect_reachIn_mem (g := g.transpose) (Fintype.card α) visited seed x
                hcard hseed hreachIn_t
            exact hx ((dfsCollect_fresh_props (g := g.transpose) (Fintype.card α)
              visited seed).2.2 x hx_comp)
        have hcover' : ∀ z, z ∉ visited' → z ∈ vs := by
          intro z hz
          have hz_old : z ∉ visited := fun h =>
            hz (dfsCollect_visited_mono (Fintype.card α) visited [] seed h)
          have hz_fin := hcover z hz_old
          simp only [List.mem_cons] at hz_fin
          rcases hz_fin with hz_eq | hz_vs
          · -- z was the seed
            subst hz_eq
            exact (hz ((dfsCollect_fresh_props (g := g.transpose) (Fintype.card α)
              visited z).2.2 z
              (by
                by_cases hcard0 : Fintype.card α = 0
                · exact (Fintype.card_eq_zero_iff.mp hcard0).elim z
                · exact dfsCollect_root_mem_pos (g := g.transpose) (Fintype.card α)
                    visited [] z (Nat.pos_of_ne_zero hcard0) hseed))).elim
          · exact hz_vs
        have hsuf' : ∃ pre, finishOrder g = pre ++ vs :=
          ⟨pre ++ [seed], by simp [hpre]⟩
        have hc' : c ∈ kosarajuGo g fuel visited' vs (comps ++ [comp]) := by
          simpa [kosarajuGo, hseed, step, visited', comp] using hc
        exact ih visited' vs (comps ++ [comp]) hcomps' hno' hcover' hsuf' c hc' a ha b hb

theorem kosaraju_sameScc (g : Digraph α) :
    ∀ c ∈ kosaraju g, ∀ a ∈ c, ∀ b ∈ c, Mutual g a b := by
  intro c hc a ha b hb
  exact kosarajuGo_sameScc_aux (Fintype.card α + 1) ∅ (finishOrder g) []
    (by intro c' hc'; cases hc')
    (by intro x y _ hy; exact (Finset.notMem_empty y hy).elim)
    (by intro z _; exact finishOrder_mem g z)
    ⟨[], rfl⟩
    c (by simpa [kosaraju] using hc) a ha b hb

/-- Mutual partner of an unvisited seed is collected by the transpose DFS. -/
private theorem mem_comp_of_mutual_seed {g : Digraph α}
    {fuel : Nat} {visited : Finset α} {seed w : α}
    (hno : ∀ x y, x ∉ visited → y ∈ visited → ¬Reach g x y)
    (hcard : Fintype.card α ≤ fuel + visited.card)
    (hseed : seed ∉ visited) (hw : w ∉ visited)
    (hm : Mutual g seed w) :
    w ∈ (dfsCollect g.transpose fuel visited [] seed).2 := by
  have ⟨_, hreachIn⟩ := ReachIn_remaining_of_Reach hno hw hm.2
  have hw_rem : w ∈ remaining visited := mem_remaining.mpr hw
  have hreachIn_t : ReachIn g.transpose (remaining visited) seed w :=
    ReachIn_reverse hreachIn hw_rem
  exact dfsCollect_reachIn_mem (g := g.transpose) fuel visited seed w
    hcard hseed hreachIn_t

/-- `kosarajuGo` covers Mutual classes of visited vertices; fuel drains the finish list. -/
private theorem kosarajuGo_maxScc_aux {g : Digraph α} :
    ∀ (fuel : Nat) (visited : Finset α) (finish : List α) (comps : List (List α)),
      (∀ x y, x ∉ visited → y ∈ visited → ¬Reach g x y) →
      (∀ z, z ∉ visited → z ∈ finish) →
      (∃ pre, finishOrder g = pre ++ finish) →
      (∀ a b, Mutual g a b → a ∈ visited → ∃ c ∈ comps, a ∈ c ∧ b ∈ c) →
      finish.length ≤ fuel →
      ∀ a b, Mutual g a b → (a ∈ visited ∨ a ∈ finish) →
        ∃ c ∈ kosarajuGo g fuel visited finish comps, a ∈ c ∧ b ∈ c := by
  intro fuel
  induction fuel with
  | zero =>
    intro visited finish comps _hno hcover _hsuf hinv hlen a b hm ha
    have hfinish : finish = [] := by
      cases finish with
      | nil => rfl
      | cons _ _ => simp at hlen
    simp only [hfinish, List.mem_nil_iff, or_false] at ha
    obtain ⟨c, hc, hab⟩ := hinv a b hm ha
    exact ⟨c, by simpa [kosarajuGo, hfinish] using hc, hab⟩
  | succ fuel ih =>
    intro visited finish comps hno hcover hsuf hinv hlen a b hm ha
    cases finish with
    | nil =>
      simp only [List.mem_nil_iff, or_false] at ha
      obtain ⟨c, hc, hab⟩ := hinv a b hm ha
      exact ⟨c, by simpa [kosarajuGo] using hc, hab⟩
    | cons seed vs =>
      simp only [List.length_cons] at hlen
      have hlen' : vs.length ≤ fuel := by omega
      by_cases hseed : seed ∈ visited
      · have hgo : kosarajuGo g (fuel + 1) visited (seed :: vs) comps =
            kosarajuGo g fuel visited vs comps := by
          simp [kosarajuGo, hseed]
        rw [hgo]
        refine ih visited vs comps hno ?_ ?_ hinv hlen' a b hm ?_
        · intro z hz
          have hz' := hcover z hz
          simp only [List.mem_cons] at hz'
          rcases hz' with rfl | hz'
          · exact (hz hseed).elim
          · exact hz'
        · obtain ⟨pre, hpre⟩ := hsuf
          exact ⟨pre ++ [seed], by simp [hpre]⟩
        · rcases ha with ha | ha
          · exact Or.inl ha
          · simp only [List.mem_cons] at ha
            rcases ha with rfl | ha
            · exact Or.inl hseed
            · exact Or.inr ha
      · set step := dfsCollect g.transpose (Fintype.card α) visited [] seed
        set visited' := step.1
        set comp := step.2
        have hts := finishOrder_tsorted g
        obtain ⟨pre, hpre⟩ := hsuf
        have hs_min : ∀ z, z ∉ visited → finishBefore (finishOrder g) seed z := by
          intro z hz
          exact finishBefore_of_suffix (finishOrder_nodup g) hpre (hcover z hz)
        have hmut_comp : ∀ w ∈ comp, Mutual g seed w := fun w hw =>
          mutual_of_finishOrder_collect (g := g) (fuel := Fintype.card α) hts hno hs_min
            hseed hw
        have hcard : Fintype.card α ≤ Fintype.card α + visited.card := by omega
        have hno' : ∀ x y, x ∉ visited' → y ∈ visited' → ¬Reach g x y := by
          intro x y hx hy hreach
          rcases dfsCollect_fresh_visited_union (g := g.transpose) (Fintype.card α)
              visited seed y hy with hyOld | hyNew
          · exact hno x y (fun h => hx (dfsCollect_visited_mono (Fintype.card α)
              visited [] seed h)) hyOld hreach
          · have hmy : Mutual g seed y := hmut_comp y hyNew
            have hxs : Reach g x seed := Reach_trans hreach hmy.2
            have hx_old : x ∉ visited := fun h =>
              hx (dfsCollect_visited_mono (Fintype.card α) visited [] seed h)
            have hmut_xs : Mutual g x seed :=
              mutual_of_reach_to_head hts hno hs_min hseed hx_old hxs
            have ⟨_, hreachIn_xs⟩ :=
              ReachIn_remaining_of_Reach hno hx_old hmut_xs.1
            have hx_rem : x ∈ remaining visited := mem_remaining.mpr hx_old
            have hreachIn_t : ReachIn g.transpose (remaining visited) seed x :=
              ReachIn_reverse hreachIn_xs hx_rem
            have hx_comp : x ∈ comp :=
              dfsCollect_reachIn_mem (g := g.transpose) (Fintype.card α) visited seed x
                hcard hseed hreachIn_t
            exact hx ((dfsCollect_fresh_props (g := g.transpose) (Fintype.card α)
              visited seed).2.2 x hx_comp)
        have hcover' : ∀ z, z ∉ visited' → z ∈ vs := by
          intro z hz
          have hz_old : z ∉ visited := fun h =>
            hz (dfsCollect_visited_mono (Fintype.card α) visited [] seed h)
          have hz_fin := hcover z hz_old
          simp only [List.mem_cons] at hz_fin
          rcases hz_fin with hz_eq | hz_vs
          · subst hz_eq
            exact (hz ((dfsCollect_fresh_props (g := g.transpose) (Fintype.card α)
              visited z).2.2 z
              (by
                by_cases hcard0 : Fintype.card α = 0
                · exact (Fintype.card_eq_zero_iff.mp hcard0).elim z
                · exact dfsCollect_root_mem_pos (g := g.transpose) (Fintype.card α)
                    visited [] z (Nat.pos_of_ne_zero hcard0) hseed))).elim
          · exact hz_vs
        have hsuf' : ∃ pre, finishOrder g = pre ++ vs :=
          ⟨pre ++ [seed], by simp [hpre]⟩
        have hinv' : ∀ a' b', Mutual g a' b' → a' ∈ visited' →
            ∃ c ∈ comps ++ [comp], a' ∈ c ∧ b' ∈ c := by
          intro a' b' hm' ha'
          rcases dfsCollect_fresh_visited_union (g := g.transpose) (Fintype.card α)
              visited seed a' ha' with haOld | haNew
          · obtain ⟨c, hc, hab⟩ := hinv a' b' hm' haOld
            exact ⟨c, by simp [hc], hab⟩
          · have hma : Mutual g seed a' := hmut_comp a' haNew
            have hmb : Mutual g seed b' := Mutual_trans hma hm'
            have hb_unvis : b' ∉ visited := fun hb =>
              hno seed b' hseed hb hmb.1
            have hb_comp : b' ∈ comp :=
              mem_comp_of_mutual_seed (g := g) (fuel := Fintype.card α) hno hcard
                hseed hb_unvis hmb
            exact ⟨comp, by simp, haNew, hb_comp⟩
        have hgo : kosarajuGo g (fuel + 1) visited (seed :: vs) comps =
            kosarajuGo g fuel visited' vs (comps ++ [comp]) := by
          dsimp [visited', comp, step]
          simp [kosarajuGo, hseed]
        rw [hgo]
        refine ih visited' vs (comps ++ [comp]) hno' hcover' hsuf' hinv' hlen' a b hm ?_
        · rcases ha with ha | ha
          · exact Or.inl (dfsCollect_visited_mono (Fintype.card α) visited [] seed ha)
          · simp only [List.mem_cons] at ha
            rcases ha with ha_eq | ha
            · refine Or.inl ?_
              rw [ha_eq]
              exact (dfsCollect_fresh_props (g := g.transpose) (Fintype.card α)
                  visited seed).2.2 seed
                  (by
                    by_cases hcard0 : Fintype.card α = 0
                    · exact (Fintype.card_eq_zero_iff.mp hcard0).elim seed
                    · exact dfsCollect_root_mem_pos (g := g.transpose) (Fintype.card α)
                        visited [] seed (Nat.pos_of_ne_zero hcard0) hseed)
            · exact Or.inr ha

theorem kosaraju_maxScc (g : Digraph α) :
    ∀ a b : α, Mutual g a b → ∃ c ∈ kosaraju g, a ∈ c ∧ b ∈ c := by
  intro a b hm
  have hlen : (finishOrder g).length ≤ Fintype.card α + 1 :=
    Nat.le_trans (finishOrder_length_le_card g) (Nat.le_succ _)
  obtain ⟨c, hc, hab⟩ :=
    kosarajuGo_maxScc_aux (Fintype.card α + 1) ∅ (finishOrder g) []
      (by intro x y _ hy; exact (Finset.notMem_empty y hy).elim)
      (by intro z _; exact finishOrder_mem g z)
      ⟨[], rfl⟩
      (by intro a' b' _ ha'; exact (Finset.notMem_empty a' ha').elim)
      hlen a b hm (Or.inr (finishOrder_mem g a))
  exact ⟨c, by simpa [kosaraju] using hc, hab⟩

theorem kosaraju_sound (g : Digraph α) :
    ValidSccPartition g (kosaraju g) := by
  refine {
    nonempty := kosaraju_nonempty g
    flatten_nodup := kosaraju_flatten_nodup g
    cover := kosaraju_cover g
    sameScc := kosaraju_sameScc g
    maxScc := kosaraju_maxScc g }

/-! ### Smoke tests (`α := Fin n`) -/

private def gEmpty : Digraph (Fin 0) where
  succ := fun _ => ∅

private def gOne : Digraph (Fin 1) where
  succ := fun _ => ∅

/-- Two-cycle: one SCC. -/
private def gCycle2 : Digraph (Fin 2) where
  succ := fun
    | ⟨0, _⟩ => {⟨1, by omega⟩}
    | ⟨1, _⟩ => {⟨0, by omega⟩}

/-- Chain `0 → 1 → 2`: three singleton SCCs. -/
private def gChain3 : Digraph (Fin 3) where
  succ := fun
    | ⟨0, _⟩ => {⟨1, by omega⟩}
    | ⟨1, _⟩ => {⟨2, by omega⟩}
    | ⟨2, _⟩ => ∅

#guard (kosaraju gEmpty).isEmpty
#guard kosaraju gOne = [[(0 : Fin 1)]]
#guard (kosaraju gCycle2).length = 1
#guard (kosaraju gCycle2).flatten.length = 2
#guard (kosaraju gChain3).length = 3
#guard (kosaraju gChain3).flatten.length = 3

end executable

end Scc
