import FHM.Scc.Kosaraju
import FHM.SurfaceBridge

/-! # Binding SCC glue (staging)

Bridge `SurfaceBridge.bindSucc` / `DepReach` to abstract `Scc.Digraph (Fin n)`
Kosaraju. **Staging only** — do not fold into `SurfaceBridge` until explicitly
asked. When merged, this module’s contents replace `sccIndexSets`; Kahn /
`ValidBindingGroups` / `DepReach` stay Nat-side.

Plan:
1. `bindDigraph` — one-shot `List Nat` successors → `Finset (Fin n)`.
2. `sccIndexSetsKosaraju` — `kosaraju` then `.map (·.map Fin.val)` (Nat comps).
3. Prove `Reach (bindDigraph) ↔` `DepReach` on indexed names.
4. Lift `ValidSccPartition` to the Nat index-set facts Kahn already consumes.
5. (Later, on say-so) swap `sccIndexSets` in SurfaceBridge; delete this staging role.
-/

namespace Scc.BindingGlue

open Scc
open SurfaceBridge

/-- Binding dependency digraph on indices `Fin binds.length`. -/
def bindDigraph (binds : List Surface.Binding) : Digraph (Fin binds.length) where
  succ := fun i =>
    ((bindSucc binds i.val).filterMap fun j =>
      if h : j < binds.length then some ⟨j, h⟩ else none).toFinset

/-- Kosaraju partition of binding indices, projected to `Nat` for Kahn. -/
def sccIndexSetsKosaraju (binds : List Surface.Binding) : List (List Nat) :=
  (kosaraju (bindDigraph binds)).map fun c => c.map Fin.val

/-- `j` is a successor of `i` in `bindDigraph` iff it is in `bindSucc`. -/
theorem mem_bindDigraph_succ {binds : List Surface.Binding}
    {i j : Fin binds.length} :
    j ∈ (bindDigraph binds).succ i ↔ j.val ∈ bindSucc binds i.val := by
  constructor
  · intro h
    simp only [bindDigraph, List.mem_toFinset, List.mem_filterMap] at h
    obtain ⟨j', hj', hj⟩ := h
    by_cases hlt : j' < binds.length
    · simp only [hlt, ↓reduceDIte, Option.some.injEq] at hj
      subst hj
      exact hj'
    · simp only [hlt, ↓reduceDIte] at hj
      cases hj
  · intro hj
    simp only [bindDigraph, List.mem_toFinset, List.mem_filterMap]
    exact ⟨j.val, hj, by simp [j.isLt]⟩

theorem bindDigraph_succ_of_bindSucc {binds : List Surface.Binding}
    {i : Fin binds.length} {j : Nat} (hj : j < binds.length)
    (h : j ∈ bindSucc binds i.val) :
    (⟨j, hj⟩ : Fin binds.length) ∈ (bindDigraph binds).succ i :=
  (mem_bindDigraph_succ (i := i) (j := ⟨j, hj⟩)).mpr h

theorem bindSucc_lt_of_mem {binds : List Surface.Binding} {i j : Nat}
    (h : j ∈ bindSucc binds i) : j < binds.length := by
  obtain ⟨_, _, _, hj, _⟩ := (bindSucc_mem (binds := binds) (i := i) (j := j)).mp h
  exact (List.getElem?_eq_some_iff.mp hj).1

/-- Direct edge on the Fin digraph ⇒ `DepEdge` on binding names. -/
theorem DepEdge_of_bindDigraph_succ {binds : List Surface.Binding}
    {i j : Fin binds.length} (h : j ∈ (bindDigraph binds).succ i) :
    ∃ b b', binds[i.val]? = some b ∧ binds[j.val]? = some b' ∧
      DepEdge binds b.name b'.name :=
  DepEdge_of_bindSucc ((mem_bindDigraph_succ (i := i) (j := j)).mp h)

/-- `Reach` on `bindDigraph` ⇒ `DepReach` on the corresponding names. -/
theorem DepReach_of_Reach {binds : List Surface.Binding}
    {i j : Fin binds.length}
    (h : Reach (bindDigraph binds) i j) :
    DepReach binds (binds[i.val]).name (binds[j.val]).name := by
  induction h with
  | refl => exact DepReach.refl
  | @tail a b c hab _rbc ih =>
    obtain ⟨ba, bb, hai, hbj, hedge⟩ := DepEdge_of_bindDigraph_succ hab
    have hai' : binds[a.val] = ba := (List.getElem?_eq_some_iff.mp hai).2
    have hbj' : binds[b.val] = bb := (List.getElem?_eq_some_iff.mp hbj).2
    rw [hai']
    refine DepReach.tail (by simpa [hai', hbj'] using hedge) ?_
    simpa [hbj'] using ih

/-- `canReach` on `bindSucc` ⇒ `Reach` on `bindDigraph` (seen stays in-range). -/
private theorem Reach_of_canReach_go (binds : List Surface.Binding) :
    ∀ (fuel : Nat) (seen : List Nat) (src dst : Fin binds.length),
      (∀ s ∈ seen, s < binds.length) →
      canReach (bindSucc binds) fuel seen src.val dst.val = true →
        Reach (bindDigraph binds) src dst := by
  intro fuel
  induction fuel with
  | zero =>
    intro seen src dst _hseen h
    unfold canReach at h
    by_cases heq : src.val = dst.val
    · have : src = dst := Fin.ext heq
      subst this
      exact Reach.refl
    · simp [heq] at h
  | succ fuel ih =>
    intro seen src dst hseen h
    unfold canReach at h
    by_cases heq : src.val = dst.val
    · have : src = dst := Fin.ext heq
      subst this
      exact Reach.refl
    · by_cases hmem : src.val ∈ seen
      · simp [heq, hmem] at h
      · simp [heq, hmem, List.any_eq_true] at h
        obtain ⟨n, hnmem, hn⟩ := h
        have hnlt : n < binds.length := bindSucc_lt_of_mem hnmem
        have hsucc :
            (⟨n, hnlt⟩ : Fin binds.length) ∈ (bindDigraph binds).succ src :=
          bindDigraph_succ_of_bindSucc hnlt hnmem
        refine Reach.tail hsucc (ih (src.val :: seen) ⟨n, hnlt⟩ dst ?_ hn)
        intro s hs
        cases List.mem_cons.mp hs with
        | inl hseq => cases hseq; exact src.isLt
        | inr hs' => exact hseen s hs'

theorem Reach_of_canReach {binds : List Surface.Binding} {fuel : Nat}
    {i j : Fin binds.length}
    (h : canReach (bindSucc binds) fuel [] i.val j.val = true) :
    Reach (bindDigraph binds) i j :=
  Reach_of_canReach_go binds fuel [] i j (by simp) h

/-- `DepReach` between in-range indexed names ⇒ `Reach` on `bindDigraph`. -/
theorem Reach_of_DepReach {binds : List Surface.Binding}
    (hn : (binds.map (·.name)).Nodup)
    {i j : Fin binds.length}
    (h : DepReach binds (binds[i.val]).name (binds[j.val]).name) :
    Reach (bindDigraph binds) i j :=
  Reach_of_canReach (canReach_complete hn i.isLt j.isLt h)

theorem Reach_iff_DepReach {binds : List Surface.Binding}
    (hn : (binds.map (·.name)).Nodup)
    {i j : Fin binds.length} :
    Reach (bindDigraph binds) i j ↔
      DepReach binds (binds[i.val]).name (binds[j.val]).name :=
  ⟨DepReach_of_Reach, Reach_of_DepReach hn⟩

theorem Mutual_iff_DepMutual {binds : List Surface.Binding}
    (hn : (binds.map (·.name)).Nodup)
    {i j : Fin binds.length} :
    Mutual (bindDigraph binds) i j ↔
      DepMutual binds (binds[i.val]).name (binds[j.val]).name := by
  simp only [Mutual, DepMutual, Reach_iff_DepReach hn]

/-- Kosaraju on the binding digraph is a valid abstract SCC partition. -/
theorem bindDigraph_kosaraju_sound (binds : List Surface.Binding) :
    ValidSccPartition (bindDigraph binds) (kosaraju (bindDigraph binds)) :=
  kosaraju_sound _

/-! ## Nat projection (for Kahn)

Next: lift `ValidSccPartition` through `Fin.val` to the facts
`sccOrderedIndexSets_*` style lemmas need (nonempty / flatten nodup / cover /
sameScc / maxScc on `List (List Nat)`), then wire Kahn on
`sccIndexSetsKosaraju`. -/

theorem sccIndexSetsKosaraju_nonempty (binds : List Surface.Binding) :
    ∀ c ∈ sccIndexSetsKosaraju binds, c ≠ [] := by
  intro c hc
  simp only [sccIndexSetsKosaraju, List.mem_map] at hc
  obtain ⟨cFin, hcFin, rfl⟩ := hc
  have hne := kosaraju_nonempty (bindDigraph binds) cFin hcFin
  intro hempty
  have : cFin = [] := by
    cases cFin with
    | nil => rfl
    | cons _ _ => simp [List.map] at hempty
  exact hne this

theorem sccIndexSetsKosaraju_flatten_nodup (binds : List Surface.Binding) :
    (sccIndexSetsKosaraju binds).flatten.Nodup := by
  -- `(L.map (List.map f)).flatten = L.flatten.map f`
  simpa [sccIndexSetsKosaraju, ← List.map_flatten] using
    (kosaraju_flatten_nodup (bindDigraph binds)).map Fin.val_injective

/-- Every in-range index appears in some Kosaraju component. -/
theorem sccIndexSetsKosaraju_cover (binds : List Surface.Binding) :
    ∀ i, i < binds.length → ∃ c ∈ sccIndexSetsKosaraju binds, i ∈ c := by
  intro i hi
  obtain ⟨cFin, hcFin, hmem⟩ :=
    (bindDigraph_kosaraju_sound binds).cover ⟨i, hi⟩
  refine ⟨cFin.map Fin.val, ?_, ?_⟩
  · simp only [sccIndexSetsKosaraju, List.mem_map]
    exact ⟨cFin, hcFin, rfl⟩
  · exact List.mem_map.mpr ⟨⟨i, hi⟩, hmem, rfl⟩

theorem sccIndexSetsKosaraju_mem_lt (binds : List Surface.Binding) :
    ∀ c ∈ sccIndexSetsKosaraju binds, ∀ i ∈ c, i < binds.length := by
  intro c hc i hi
  simp only [sccIndexSetsKosaraju, List.mem_map] at hc
  obtain ⟨cFin, _, rfl⟩ := hc
  obtain ⟨⟨j, hj⟩, _, rfl⟩ := List.mem_map.mp hi
  exact hj

/-- Flatten of Kosaraju index sets is a permutation of `0 .. n-1`. -/
theorem sccIndexSetsKosaraju_flatten_perm (binds : List Surface.Binding) :
    (sccIndexSetsKosaraju binds).flatten.Perm (List.range binds.length) := by
  have hnodup := sccIndexSetsKosaraju_flatten_nodup binds
  have hbound : ∀ x ∈ (sccIndexSetsKosaraju binds).flatten, x < binds.length := by
    intro x hx
    obtain ⟨c, hc, hx'⟩ := List.mem_flatten.mp hx
    exact sccIndexSetsKosaraju_mem_lt binds c hc x hx'
  have hlen : (sccIndexSetsKosaraju binds).flatten.length = binds.length := by
    have hsub : ((sccIndexSetsKosaraju binds).flatten).toFinset ⊆ Finset.range binds.length := by
      intro x hx
      exact Finset.mem_range.mpr (hbound x (List.mem_toFinset.mp hx))
    have hsup : Finset.range binds.length ⊆ ((sccIndexSetsKosaraju binds).flatten).toFinset := by
      intro x hx
      have hx' : x < binds.length := Finset.mem_range.mp hx
      obtain ⟨c, hc, hxmem⟩ := sccIndexSetsKosaraju_cover binds x hx'
      exact List.mem_toFinset.mpr (List.mem_flatten.mpr ⟨c, hc, hxmem⟩)
    have hEq : ((sccIndexSetsKosaraju binds).flatten).toFinset = Finset.range binds.length :=
      Finset.Subset.antisymm hsub hsup
    have hcard := congrArg Finset.card hEq
    rwa [List.toFinset_card_of_nodup hnodup, Finset.card_range] at hcard
  exact perm_range_of_nodup_length hnodup hbound hlen

/-- Length hyps are explicit so `binds[a]` elaborates without `binds[a]'…`. -/
theorem sccIndexSetsKosaraju_sameScc (binds : List Surface.Binding)
    (hn : (binds.map (·.name)).Nodup)
    {c : List Nat} (hc : c ∈ sccIndexSetsKosaraju binds)
    {a b : Nat} (ha : a ∈ c) (hb : b ∈ c)
    (ha_lt : a < binds.length) (hb_lt : b < binds.length) :
    DepMutual binds (binds[a]).name (binds[b]).name := by
  simp only [sccIndexSetsKosaraju, List.mem_map] at hc
  obtain ⟨cFin, hcFin, rfl⟩ := hc
  obtain ⟨ia, hia, rfl⟩ := List.mem_map.mp ha
  obtain ⟨ib, hib, rfl⟩ := List.mem_map.mp hb
  have hmut := (bindDigraph_kosaraju_sound binds).sameScc cFin hcFin ia hia ib hib
  exact (Mutual_iff_DepMutual hn (i := ia) (j := ib)).mp hmut

theorem sccIndexSetsKosaraju_maxScc (binds : List Surface.Binding)
    (hn : (binds.map (·.name)).Nodup)
    {a b : Nat} (ha : a < binds.length) (hb : b < binds.length)
    (hmut : DepMutual binds (binds[a]).name (binds[b]).name) :
    ∃ c ∈ sccIndexSetsKosaraju binds, a ∈ c ∧ b ∈ c := by
  have hR : Mutual (bindDigraph binds) ⟨a, ha⟩ ⟨b, hb⟩ :=
    (Mutual_iff_DepMutual hn).mpr hmut
  obtain ⟨cFin, hcFin, ha', hb'⟩ :=
    (bindDigraph_kosaraju_sound binds).maxScc _ _ hR
  refine ⟨cFin.map Fin.val, ?_, ?_, ?_⟩
  · simp only [sccIndexSetsKosaraju, List.mem_map]
    exact ⟨cFin, hcFin, rfl⟩
  · exact List.mem_map.mpr ⟨⟨a, ha⟩, ha', rfl⟩
  · exact List.mem_map.mpr ⟨⟨b, hb⟩, hb', rfl⟩

private theorem eq_of_mem_of_mem_of_pairwise_disjoint {α} {L : List (List α)}
    (hdisj : List.Pairwise List.Disjoint L)
    {g g' : List α} (hg : g ∈ L) (hg' : g' ∈ L) {x : α}
    (hx : x ∈ g) (hx' : x ∈ g') : g = g' := by
  induction L with
  | nil => cases hg
  | cons hd tl ih =>
    have hdisj' := List.pairwise_cons.mp hdisj
    cases List.mem_cons.mp hg with
    | inl h =>
      subst h
      cases List.mem_cons.mp hg' with
      | inl h' => exact h'.symm
      | inr h' => exact (hdisj'.1 g' h' hx hx').elim
    | inr h =>
      cases List.mem_cons.mp hg' with
      | inl h' =>
        subst h'
        exact (hdisj'.1 g h hx' hx).elim
      | inr h' => exact ih hdisj'.2 h h'

/-- Each index appears in exactly one Kosaraju component. -/
theorem sccIndexSetsKosaraju_unique_comp (binds : List Surface.Binding) {i : Nat}
    (hi : i < binds.length) :
    ∃ g ∈ sccIndexSetsKosaraju binds, i ∈ g ∧
      ∀ g' ∈ sccIndexSetsKosaraju binds, i ∈ g' → g' = g := by
  have hperm := sccIndexSetsKosaraju_flatten_perm binds
  have himem : i ∈ (sccIndexSetsKosaraju binds).flatten :=
    (List.Perm.mem_iff hperm).2 (List.mem_range.mpr hi)
  obtain ⟨g, hg, hi'⟩ := List.mem_flatten.mp himem
  refine ⟨g, hg, hi', ?_⟩
  intro g' hg' hi''
  have hnodup : (sccIndexSetsKosaraju binds).flatten.Nodup :=
    (List.Perm.nodup_iff hperm).2 List.nodup_range
  have hdisj : List.Pairwise List.Disjoint (sccIndexSetsKosaraju binds) :=
    (List.nodup_flatten.mp hnodup).2
  exact (eq_of_mem_of_mem_of_pairwise_disjoint hdisj hg hg' hi' hi'').symm

/-- Distinct components are mutual-reachability separated. -/
theorem sccIndexSetsKosaraju_separated (binds : List Surface.Binding)
    (hn : (binds.map (·.name)).Nodup)
    {c₁ c₂ : List Nat} (hc₁ : c₁ ∈ sccIndexSetsKosaraju binds)
    (hc₂ : c₂ ∈ sccIndexSetsKosaraju binds) (hne : c₁ ≠ c₂)
    {a b : Nat} (ha : a ∈ c₁) (hb : b ∈ c₂)
    (ha_lt : a < binds.length) (hb_lt : b < binds.length) :
    ¬DepMutual binds (binds[a]).name (binds[b]).name := by
  intro hmut
  obtain ⟨c, hc, ha', hb'⟩ := sccIndexSetsKosaraju_maxScc binds hn ha_lt hb_lt hmut
  have hnodup := sccIndexSetsKosaraju_flatten_nodup binds
  have hdisj : List.Pairwise List.Disjoint (sccIndexSetsKosaraju binds) :=
    (List.nodup_flatten.mp hnodup).2
  have hc₁c : c₁ = c :=
    eq_of_mem_of_mem_of_pairwise_disjoint hdisj hc₁ hc ha ha'
  have hc₂c : c₂ = c :=
    eq_of_mem_of_mem_of_pairwise_disjoint hdisj hc₂ hc hb hb'
  exact hne (hc₁c.trans hc₂c.symm)

/-! ## Ordered groups (Kahn on Kosaraju condensation) -/

/-- Kosaraju comps in Kahn topo order. -/
def sccOrderedIndexSetsKosaraju (binds : List Surface.Binding) : List (List Nat) :=
  let comps := sccIndexSetsKosaraju binds
  (kahnTopo comps.length (sccBeforeEdges (bindSucc binds) comps)).filterMap
    fun k => comps[k]?

/-- Executable Kosaraju → Kahn grouping (`none` if names not unique). -/
def sccGroupsKosaraju (binds : List Surface.Binding) :
    Option (List (List Surface.Binding)) := do
  guard (binds.map (·.name)).Nodup
  let comps := sccIndexSetsKosaraju binds
  let order := kahnTopo comps.length (sccBeforeEdges (bindSucc binds) comps)
  let ordered := order.filterMap fun k => comps[k]?
  pure (indexSetsToBindings binds ordered)

theorem sccGroupsKosaraju_eq_some_iff {binds : List Surface.Binding}
    {groups : List (List Surface.Binding)} :
    sccGroupsKosaraju binds = some groups ↔
      (binds.map (·.name)).Nodup ∧
        groups = indexSetsToBindings binds (sccOrderedIndexSetsKosaraju binds) := by
  constructor
  · intro h
    have hn : (binds.map (·.name)).Nodup := by
      by_contra hdup
      simp [sccGroupsKosaraju, guard, hdup] at h
    refine ⟨hn, ?_⟩
    simp [sccGroupsKosaraju, guard, hn] at h
    exact h.symm
  · intro ⟨hn, hg⟩
    simp [sccGroupsKosaraju, guard, hn, sccOrderedIndexSetsKosaraju, hg]

private theorem filterMap_ne_nil_of_isSome {α β}
    (f : α → Option β) {l : List α} (hne : l ≠ [])
    (h : ∀ x ∈ l, (f x).isSome) : l.filterMap f ≠ [] := by
  cases l with
  | nil => cases hne rfl
  | cons a as =>
    have ha := h a (by simp)
    cases hf : f a with
    | none => simp [hf] at ha
    | some b => simp [hf]

private theorem filterMap_getElem?_of_perm {α} {l : List α} {order : List Nat}
    (h : order.Perm (List.range l.length)) :
    (order.filterMap (fun i => l[i]?)).Perm l := by
  have h' := h.filterMap (fun i => l[i]?)
  rwa [range_filterMap_getElem?] at h'

private theorem sccOrderedIndexSetsKosaraju_mem_of_getElem
    (binds : List Surface.Binding) {idxs : List Nat}
    (h : idxs ∈ sccOrderedIndexSetsKosaraju binds) :
    idxs ∈ sccIndexSetsKosaraju binds := by
  simp only [sccOrderedIndexSetsKosaraju] at h
  obtain ⟨k, _hk, hget⟩ := List.mem_filterMap.mp h
  exact List.mem_of_getElem? hget

/-- One condensation before-edge ⇒ `DepReach` from dependent into dependency. -/
private theorem DepReach_of_sccBeforeEdge_kosaraju (binds : List Surface.Binding)
    (hn : (binds.map (·.name)).Nodup)
    {u v x y : Nat}
    (he : (u, v) ∈ sccBeforeEdges (bindSucc binds) (sccIndexSetsKosaraju binds))
    {ca cb : List Nat}
    (hca : (sccIndexSetsKosaraju binds)[v]? = some ca)
    (hcb : (sccIndexSetsKosaraju binds)[u]? = some cb)
    (hx : x ∈ ca) (hy : y ∈ cb)
    (hx_lt : x < binds.length) (hy_lt : y < binds.length) :
    DepReach binds (binds[x]).name (binds[y]).name := by
  set comps := sccIndexSetsKosaraju binds
  obtain ⟨_hne, _hu_lt, _hv_lt, ca', cb', hca', hcb', p, hp, q, hq, hsucc⟩ :=
    exists_succ_of_mem_sccBeforeEdges (bindSucc binds) comps he
  have hca_eq : ca' = ca := by
    rw [hca'] at hca; exact Option.some.inj hca
  have hcb_eq : cb' = cb := by
    rw [hcb'] at hcb; exact Option.some.inj hcb
  rw [hca_eq] at hp; rw [hcb_eq] at hq
  have hv_mem : ca ∈ comps := List.mem_of_getElem? hca
  have hu_mem : cb ∈ comps := List.mem_of_getElem? hcb
  have hp_lt := sccIndexSetsKosaraju_mem_lt binds ca hv_mem p hp
  have hq_lt := sccIndexSetsKosaraju_mem_lt binds cb hu_mem q hq
  obtain ⟨b, b', hb, hb', hedge⟩ := DepEdge_of_bindSucc hsucc
  have hb1 : b = binds[p] := by
    rw [List.getElem?_eq_getElem hp_lt] at hb; exact Option.some.inj hb.symm
  have hb2 : b' = binds[q] := by
    rw [List.getElem?_eq_getElem hq_lt] at hb'; exact Option.some.inj hb'.symm
  rw [hb1, hb2] at hedge
  have hxp : DepMutual binds (binds[x]).name (binds[p]).name :=
    sccIndexSetsKosaraju_sameScc binds hn hv_mem hx hp hx_lt hp_lt
  have hqy : DepMutual binds (binds[q]).name (binds[y]).name :=
    sccIndexSetsKosaraju_sameScc binds hn hu_mem hq hy hq_lt hy_lt
  exact DepReach_trans hxp.1 (DepReach.tail hedge hqy.1)

private theorem sccBeforeReach_lt_kosaraju (binds : List Surface.Binding)
    {u v : Nat}
    (h : Relation.TransGen
      (fun a b => (a, b) ∈ sccBeforeEdges (bindSucc binds) (sccIndexSetsKosaraju binds)) u v) :
    u < (sccIndexSetsKosaraju binds).length ∧ v < (sccIndexSetsKosaraju binds).length := by
  induction h with
  | single he =>
    exact ⟨(exists_succ_of_mem_sccBeforeEdges (bindSucc binds) _ he).2.1,
      (exists_succ_of_mem_sccBeforeEdges (bindSucc binds) _ he).2.2.1⟩
  | tail _hab hbc ih =>
    exact ⟨ih.1, (exists_succ_of_mem_sccBeforeEdges (bindSucc binds) _ hbc).2.2.1⟩

/-- Condensation path ⇒ `DepReach` from path-end component back to start. -/
private theorem DepReach_of_sccBeforeReach_kosaraju (binds : List Surface.Binding)
    (hn : (binds.map (·.name)).Nodup)
    {u v : Nat}
    (h : Relation.TransGen
      (fun a b => (a, b) ∈ sccBeforeEdges (bindSucc binds) (sccIndexSetsKosaraju binds)) u v)
    {ca cb : List Nat}
    (hca : (sccIndexSetsKosaraju binds)[v]? = some ca)
    (hcb : (sccIndexSetsKosaraju binds)[u]? = some cb)
    {x y : Nat} (hx : x ∈ ca) (hy : y ∈ cb)
    (hx_lt : x < binds.length) (hy_lt : y < binds.length) :
    DepReach binds (binds[x]).name (binds[y]).name := by
  induction h generalizing ca cb x y with
  | single he =>
    exact DepReach_of_sccBeforeEdge_kosaraju binds hn he hca hcb hx hy hx_lt hy_lt
  | tail hab hbc ih =>
    obtain ⟨_hne, _hw_lt, _hv_lt, cv, cw, hcv, hcw, p, hp, q, hq, hsucc⟩ :=
      exists_succ_of_mem_sccBeforeEdges (bindSucc binds) (sccIndexSetsKosaraju binds) hbc
    have hcv_eq : cv = ca := by
      rw [hcv] at hca; exact Option.some.inj hca
    rw [hcv_eq] at hp
    have hq_lt := sccIndexSetsKosaraju_mem_lt binds cw (List.mem_of_getElem? hcw) q hq
    have hp_lt := sccIndexSetsKosaraju_mem_lt binds ca (List.mem_of_getElem? hca) p hp
    have h_to_q : DepReach binds (binds[x]).name (binds[q]).name := by
      obtain ⟨b, b', hb, hb', hedge⟩ := DepEdge_of_bindSucc hsucc
      have hb1 : b = binds[p] := by
        rw [List.getElem?_eq_getElem hp_lt] at hb; exact Option.some.inj hb.symm
      have hb2 : b' = binds[q] := by
        rw [List.getElem?_eq_getElem hq_lt] at hb'; exact Option.some.inj hb'.symm
      rw [hb1, hb2] at hedge
      have hxp : DepMutual binds (binds[x]).name (binds[p]).name :=
        sccIndexSetsKosaraju_sameScc binds hn (List.mem_of_getElem? hca) hx hp hx_lt hp_lt
      exact DepReach_trans hxp.1 (DepReach.tail hedge DepReach.refl)
    have h_from_q : DepReach binds (binds[q]).name (binds[y]).name :=
      ih hcw hcb hq hy hq_lt hy_lt
    exact DepReach_trans h_to_q h_from_q

/-- A before-edge cycle among distinct SCC indices contradicts separation. -/
private theorem sccBeforeEdges_acyclic_kosaraju (binds : List Surface.Binding)
    (hn : (binds.map (·.name)).Nodup)
    {u v : Nat} (hne : u ≠ v)
    (huv : Relation.TransGen
      (fun a b => (a, b) ∈ sccBeforeEdges (bindSucc binds) (sccIndexSetsKosaraju binds)) u v)
    (hvu : Relation.TransGen
      (fun a b => (a, b) ∈ sccBeforeEdges (bindSucc binds) (sccIndexSetsKosaraju binds)) v u) :
    False := by
  set comps := sccIndexSetsKosaraju binds
  have ⟨hu_lt, hv_lt⟩ := sccBeforeReach_lt_kosaraju binds huv
  have hcu : comps[u]? = some comps[u] := List.getElem?_eq_getElem hu_lt
  have hcv : comps[v]? = some comps[v] := List.getElem?_eq_getElem hv_lt
  have hu_mem : comps[u] ∈ comps := List.getElem_mem hu_lt
  have hv_mem : comps[v] ∈ comps := List.getElem_mem hv_lt
  have hu_ne : comps[u] ≠ [] := sccIndexSetsKosaraju_nonempty binds _ hu_mem
  have hv_ne : comps[v] ≠ [] := sccIndexSetsKosaraju_nonempty binds _ hv_mem
  have hx := List.head_mem hu_ne
  have hy := List.head_mem hv_ne
  set x := comps[u].head hu_ne
  set y := comps[v].head hv_ne
  have hx_lt := sccIndexSetsKosaraju_mem_lt binds _ hu_mem x hx
  have hy_lt := sccIndexSetsKosaraju_mem_lt binds _ hv_mem y hy
  have hne_g : comps[u] ≠ comps[v] := by
    intro heq
    have hnodup : comps.flatten.Nodup :=
      (List.Perm.nodup_iff (sccIndexSetsKosaraju_flatten_perm binds)).2 List.nodup_range
    have hdisj : List.Pairwise List.Disjoint comps :=
      (List.nodup_flatten.mp hnodup).2
    have hlt : (⟨u, hu_lt⟩ : Fin comps.length) < ⟨v, hv_lt⟩ ∨
        (⟨v, hv_lt⟩ : Fin comps.length) < ⟨u, hu_lt⟩ := by
      rcases Nat.lt_or_gt_of_ne hne with h | h
      · exact Or.inl h
      · exact Or.inr h
    cases hlt with
    | inl h =>
      have hd := List.Pairwise.rel_get_of_lt hdisj h
      exact hd hx (by simpa [heq] using hx)
    | inr h =>
      have hd := List.Pairwise.rel_get_of_lt hdisj h
      exact hd (by simpa [heq] using hx) hx
  have dxy : DepReach binds (binds[y]).name (binds[x]).name :=
    DepReach_of_sccBeforeReach_kosaraju binds hn huv hcv hcu hy hx hy_lt hx_lt
  have dyx : DepReach binds (binds[x]).name (binds[y]).name :=
    DepReach_of_sccBeforeReach_kosaraju binds hn hvu hcu hcv hx hy hx_lt hy_lt
  have hmut : DepMutual binds (binds[x]).name (binds[y]).name := ⟨dyx, dxy⟩
  exact sccIndexSetsKosaraju_separated binds hn hu_mem hv_mem hne_g hx hy hx_lt hy_lt hmut

/-- Critical Kahn gap: condensation of Kosaraju comps is a DAG. -/
private theorem kahnTopo_scc_perm_kosaraju (binds : List Surface.Binding)
    (hn : (binds.map (·.name)).Nodup) :
    let comps := sccIndexSetsKosaraju binds
    let edges := sccBeforeEdges (bindSucc binds) comps
    (kahnTopo comps.length edges).Perm (List.range comps.length) := by
  set comps := sccIndexSetsKosaraju binds
  set edges := sccBeforeEdges (bindSucc binds) comps
  have hb := sccBeforeEdges_bounded (bindSucc binds) comps
  have hnodup_e := sccBeforeEdges_nodup (bindSucc binds) comps
  simp only [kahnTopo]
  set indeg0 := (List.range comps.length).map fun w =>
    (edges.filter (fun e => e.2 = w)).length
  set ready0 := (List.range comps.length).filter fun w => indegGet indeg0 w = 0
  set out := kahnGo edges (comps.length + 1) indeg0 ready0 []
  have hres := kahnGo_zero_closed edges comps.length hb hnodup_e
    (comps.length + 1) indeg0 ready0 []
    (by simp [indeg0, List.length_map, List.length_range])
    (fun w hw => by simpa [indeg0] using kahnTopo_indeg0_eq comps.length edges hw)
    (fun b hb' => by
      have hbmem := List.mem_filter.mp hb'
      refine ⟨List.mem_range.mp hbmem.1, ?_, by simp⟩
      have heq : indegGet indeg0 b = 0 := of_decide_eq_true hbmem.2
      rwa [show indeg0 = (List.range comps.length).map fun w =>
        (edges.filter (fun e => e.2 = w)).length from rfl,
        kahnTopo_indeg0_eq comps.length edges (List.mem_range.mp hbmem.1)] at heq)
    (List.Nodup.filter _ List.nodup_range)
    (fun y hy => by cases hy)
    (by simp)
    (fun v hv hz => by
      right
      refine List.mem_filter.mpr ⟨List.mem_range.mpr hv, ?_⟩
      have : indegGet indeg0 v = 0 := by
        rwa [show indeg0 = (List.range comps.length).map fun w =>
          (edges.filter (fun e => e.2 = w)).length from rfl,
          kahnTopo_indeg0_eq comps.length edges hv]
      exact decide_eq_true this)
    (by omega)
  change out.Perm (List.range comps.length)
  obtain ⟨hnodup_out, hlt_out, hlen_or⟩ := hres
  refine perm_range_of_nodup_length hnodup_out hlt_out ?_
  cases hlen_or with
  | inl hlen => exact hlen
  | inr hstuck =>
    obtain ⟨v0, hv0, hv0n, hpred⟩ := hstuck
    have hlen_lt : out.length < comps.length := by
      have hle := length_le_of_nodup_lt hnodup_out hlt_out
      by_contra hnge
      have heq : out.length = comps.length := Nat.le_antisymm hle (by omega)
      have hperm := perm_range_of_nodup_length hnodup_out hlt_out heq
      exact hv0n ((List.Perm.mem_iff hperm).2 (List.mem_range.mpr hv0))
    obtain ⟨u, v, hne, huv, hvu⟩ :=
      exists_edge_cycle_of_pred_closed edges hnodup_out hlen_lt
        (sccBeforeEdges_no_loop (bindSucc binds) comps) hpred
    exact (sccBeforeEdges_acyclic_kosaraju binds hn hne huv hvu).elim

private theorem sccOrderedIndexSetsKosaraju_flatten_perm (binds : List Surface.Binding)
    (hn : (binds.map (·.name)).Nodup) :
    (sccOrderedIndexSetsKosaraju binds).flatten.Perm (List.range binds.length) := by
  simp only [sccOrderedIndexSetsKosaraju]
  set comps := sccIndexSetsKosaraju binds
  set edges := sccBeforeEdges (bindSucc binds) comps
  set order := kahnTopo comps.length edges
  have hord := kahnTopo_scc_perm_kosaraju binds hn
  have hcomps : (order.filterMap (fun k => comps[k]?)).Perm comps :=
    filterMap_getElem?_of_perm hord
  have hflat := hcomps.flatten
  exact hflat.trans (sccIndexSetsKosaraju_flatten_perm binds)

private theorem sccIndexSetsKosaraju_mem_of_DepMutual (binds : List Surface.Binding)
    (hn : (binds.map (·.name)).Nodup)
    {g : List Nat} (hg : g ∈ sccIndexSetsKosaraju binds)
    {i j : Nat} (hi : i ∈ g)
    (hi_lt : i < binds.length) (hj : j < binds.length)
    (hmut : DepMutual binds (binds[i]).name (binds[j]).name) :
    j ∈ g := by
  obtain ⟨g', hg', hj', _⟩ := sccIndexSetsKosaraju_unique_comp binds hj
  suffices g' = g by rwa [← this]
  by_contra hne
  exact sccIndexSetsKosaraju_separated binds hn hg hg' (Ne.symm hne) hi hj' hi_lt hj hmut

theorem sccOrderedIndexSetsKosaraju_flatPerm (binds : List Surface.Binding)
    (hn : (binds.map (·.name)).Nodup) :
    (indexSetsToBindings binds (sccOrderedIndexSetsKosaraju binds)).flatten.Perm binds :=
  indexSetsToBindings_flatten_of_perm (sccOrderedIndexSetsKosaraju_flatten_perm binds hn)

theorem sccOrderedIndexSetsKosaraju_nonempty (binds : List Surface.Binding) :
    ∀ g ∈ indexSetsToBindings binds (sccOrderedIndexSetsKosaraju binds), g ≠ [] := by
  intro g hg
  simp only [indexSetsToBindings, List.mem_map] at hg
  obtain ⟨idxs, hidxs, rfl⟩ := hg
  have hcomp := sccOrderedIndexSetsKosaraju_mem_of_getElem binds hidxs
  have hne := sccIndexSetsKosaraju_nonempty binds idxs hcomp
  refine filterMap_ne_nil_of_isSome (fun i => binds[i]?) hne ?_
  intro i hi
  have hlt := sccIndexSetsKosaraju_mem_lt binds idxs hcomp i hi
  simp [List.getElem?_eq_getElem hlt]

theorem sccOrderedIndexSetsKosaraju_sameScc (binds : List Surface.Binding)
    (hn : (binds.map (·.name)).Nodup) :
    ∀ g ∈ indexSetsToBindings binds (sccOrderedIndexSetsKosaraju binds),
      ∀ b1 ∈ g, ∀ b2 ∈ g, DepMutual binds b1.name b2.name := by
  intro g hg b1 hb1 b2 hb2
  simp only [indexSetsToBindings, List.mem_map] at hg
  obtain ⟨idxs, hidxs, rfl⟩ := hg
  have hcomp := sccOrderedIndexSetsKosaraju_mem_of_getElem binds hidxs
  obtain ⟨i, hi, hbi⟩ := List.mem_filterMap.mp hb1
  obtain ⟨j, hj, hbj⟩ := List.mem_filterMap.mp hb2
  have hi_lt := sccIndexSetsKosaraju_mem_lt binds idxs hcomp i hi
  have hj_lt := sccIndexSetsKosaraju_mem_lt binds idxs hcomp j hj
  have hbi' : binds[i] = b1 := by
    rw [List.getElem?_eq_getElem hi_lt] at hbi; exact Option.some.inj hbi
  have hbj' : binds[j] = b2 := by
    rw [List.getElem?_eq_getElem hj_lt] at hbj; exact Option.some.inj hbj
  have hmut := sccIndexSetsKosaraju_sameScc binds hn hcomp hi hj hi_lt hj_lt
  simpa [hbi', hbj'] using hmut

theorem sccOrderedIndexSetsKosaraju_maxScc (binds : List Surface.Binding)
    (hn : (binds.map (·.name)).Nodup) :
    ∀ b1 ∈ binds, ∀ b2 ∈ binds,
      DepMutual binds b1.name b2.name →
        ∃ g ∈ indexSetsToBindings binds (sccOrderedIndexSetsKosaraju binds),
          b1 ∈ g ∧ b2 ∈ g := by
  intro b1 hb1 b2 hb2 hmut
  obtain ⟨i, hi, hib⟩ := List.mem_iff_getElem.mp hb1
  obtain ⟨j, hj, hjb⟩ := List.mem_iff_getElem.mp hb2
  subst hib; subst hjb
  obtain ⟨gIdxs, hgIdxs, hi_mem, _huniq⟩ := sccIndexSetsKosaraju_unique_comp binds hi
  have hj_mem : j ∈ gIdxs :=
    sccIndexSetsKosaraju_mem_of_DepMutual binds hn hgIdxs hi_mem hi hj hmut
  have hord := kahnTopo_scc_perm_kosaraju binds hn
  obtain ⟨k, hklt, rfl⟩ := List.mem_iff_getElem.mp hgIdxs
  have hk_ord : k ∈
      kahnTopo (sccIndexSetsKosaraju binds).length
        (sccBeforeEdges (bindSucc binds) (sccIndexSetsKosaraju binds)) :=
    (List.Perm.mem_iff hord).2 (List.mem_range.mpr hklt)
  have hidxs : (sccIndexSetsKosaraju binds)[k] ∈ sccOrderedIndexSetsKosaraju binds := by
    simp only [sccOrderedIndexSetsKosaraju, List.mem_filterMap]
    exact ⟨k, hk_ord, List.getElem?_eq_getElem hklt⟩
  refine ⟨(sccIndexSetsKosaraju binds)[k].filterMap (fun t => binds[t]?), ?_, ?_, ?_⟩
  · simp only [indexSetsToBindings, List.mem_map]
    exact ⟨(sccIndexSetsKosaraju binds)[k], hidxs, rfl⟩
  · exact List.mem_filterMap.mpr ⟨i, hi_mem, by simp [List.getElem?_eq_getElem hi]⟩
  · exact List.mem_filterMap.mpr ⟨j, hj_mem, by simp [List.getElem?_eq_getElem hj]⟩

theorem sccOrderedIndexSetsKosaraju_topo (binds : List Surface.Binding) :
    let groups := indexSetsToBindings binds (sccOrderedIndexSetsKosaraju binds)
    ∀ (i j : Nat) (gi gj : List Surface.Binding),
      groups[i]? = some gi → groups[j]? = some gj → i ≠ j →
      ∀ b1 ∈ gi, ∀ b2 ∈ gj,
        Binding.refersTo b1 b2.name = true → j < i := by
  intro groups i j gi gj hgi hgj _hne b1 hb1 b2 hb2 href
  set comps := sccIndexSetsKosaraju binds
  set edges := sccBeforeEdges (bindSucc binds) comps
  set order := kahnTopo comps.length edges
  have hb := sccBeforeEdges_bounded (bindSucc binds) comps
  have hnodup := sccBeforeEdges_nodup (bindSucc binds) comps
  simp only [groups, indexSetsToBindings, sccOrderedIndexSetsKosaraju] at hgi hgj
  rw [List.getElem?_map] at hgi hgj
  have hord_lt : ∀ x ∈ order, x < comps.length := kahnTopo_lt _ _ hb
  have hgi_fm :
      ((order.filterMap fun k => comps[k]?)[i]?).map
        (fun idxs => idxs.filterMap fun t => binds[t]?) = some gi := hgi
  have hgj_fm :
      ((order.filterMap fun k => comps[k]?)[j]?).map
        (fun idxs => idxs.filterMap fun t => binds[t]?) = some gj := hgj
  cases hi_ord : (order.filterMap fun k => comps[k]?)[i]? with
  | none => simp [hi_ord] at hgi_fm
  | some idxsi =>
    cases hj_ord : (order.filterMap fun k => comps[k]?)[j]? with
    | none => simp [hj_ord] at hgj_fm
    | some idxsj =>
      simp only [hi_ord, hj_ord, Option.map_some, Option.some.injEq] at hgi_fm hgj_fm
      have hfm_i := filterMap_getElem?_eq_map (fun k => comps[k]?) order
        (fun x hx => by
          have := hord_lt x hx
          simp [List.getElem?_eq_getElem this]) i
      have hfm_j := filterMap_getElem?_eq_map (fun k => comps[k]?) order
        (fun x hx => by
          have := hord_lt x hx
          simp [List.getElem?_eq_getElem this]) j
      rw [hfm_i] at hi_ord
      rw [hfm_j] at hj_ord
      cases hi_o : order[i]? with
      | none => simp [hi_o] at hi_ord
      | some ki =>
        cases hj_o : order[j]? with
        | none => simp [hj_o] at hj_ord
        | some kj =>
          simp only [hi_o, hj_o, Option.bind_eq_bind] at hi_ord hj_ord
          have hki_lt : ki < comps.length := hord_lt ki (List.mem_of_getElem? hi_o)
          have hkj_lt : kj < comps.length := hord_lt kj (List.mem_of_getElem? hj_o)
          have hidxsi : idxsi = comps[ki] := by
            simpa [List.getElem?_eq_getElem hki_lt] using hi_ord.symm
          have hidxsj : idxsj = comps[kj] := by
            simpa [List.getElem?_eq_getElem hkj_lt] using hj_ord.symm
          have hb1' := List.mem_filterMap.mp (by simpa [← hgi_fm] using hb1)
          have hb2' := List.mem_filterMap.mp (by simpa [← hgj_fm] using hb2)
          obtain ⟨p, hp, hbp⟩ := hb1'
          obtain ⟨q, hq, hbq⟩ := hb2'
          have hp' : p ∈ comps[ki] := by simpa [hidxsi] using hp
          have hq' : q ∈ comps[kj] := by simpa [hidxsj] using hq
          have hsucc : q ∈ bindSucc binds p :=
            (bindSucc_mem (binds := binds) (i := p) (j := q)).mpr
              ⟨b1, b2, hbp, hbq, href⟩
          have hne_kj : ki ≠ kj := by
            intro heq
            subst heq
            have hnodup_ord := kahnTopo_nodup comps.length edges hnodup
            have hi_lt : i < order.length := (List.getElem?_eq_some_iff.mp hi_o).1
            have hj_lt : j < order.length := (List.getElem?_eq_some_iff.mp hj_o).1
            have hei : order[i] = ki := (List.getElem?_eq_some_iff.mp hi_o).2
            have hej : order[j] = ki := (List.getElem?_eq_some_iff.mp hj_o).2
            exact _hne ((List.Nodup.getElem_inj_iff hnodup_ord).1 (hei.trans hej.symm))
          have hdep := compDependsOn_of_succ_mem (bindSucc binds) hp' hq' hsucc
          have hedge := mem_sccBeforeEdges_of_compDependsOn (bindSucc binds) comps
            hki_lt hkj_lt hne_kj hdep
          exact kahnTopo_edge_before comps.length edges hb hnodup hedge hj_o hi_o

theorem sccGroupsKosaraju_sound {binds : List Surface.Binding}
    {groups : List (List Surface.Binding)} :
    sccGroupsKosaraju binds = some groups → ValidBindingGroups binds groups := by
  intro h
  obtain ⟨hn, rfl⟩ := (sccGroupsKosaraju_eq_some_iff).1 h
  exact ⟨hn,
    sccOrderedIndexSetsKosaraju_flatPerm binds hn,
    sccOrderedIndexSetsKosaraju_nonempty binds,
    sccOrderedIndexSetsKosaraju_sameScc binds hn,
    sccOrderedIndexSetsKosaraju_maxScc binds hn,
    sccOrderedIndexSetsKosaraju_topo binds⟩

-- SCC `#guard`s (mirror SurfaceBridge `sccGroups` shape)
private def bF : Surface.Binding :=
  { name := .mk "f", ann := none,
    rhs := .lambda (.name (.mk "x")) none (.app (.var (.mk "f")) (.var (.mk "x"))) }
private def bG : Surface.Binding :=
  { name := .mk "g", ann := none, rhs := .var (.mk "f") }
private def bA : Surface.Binding :=
  { name := .mk "a", ann := none, rhs := .primLit (.int 1) }
private def bB : Surface.Binding :=
  { name := .mk "b", ann := none, rhs := .primLit (.int 2) }
private def bH : Surface.Binding :=
  { name := .mk "h", ann := none, rhs := .var (.mk "k") }
private def bK : Surface.Binding :=
  { name := .mk "k", ann := none, rhs := .var (.mk "h") }

-- g depends on f ⇒ [f]-group outer, then [g]
#guard match sccGroupsKosaraju [bF, bG] with
  | some [[{ name := .mk "f", .. }], [{ name := .mk "g", .. }]] => true
  | _ => false
-- mutual h ↔ k ⇒ one group containing both
#guard match sccGroupsKosaraju [bH, bK] with
  | some [g] =>
      g.length = 2 && (g.map (·.name)).contains (.mk "h") &&
        (g.map (·.name)).contains (.mk "k")
  | _ => false
-- independent a, b ⇒ two singleton groups (intra-order free under Kosaraju)
#guard match sccGroupsKosaraju [bA, bB] with
  | some [[{ name := .mk "a", .. }], [{ name := .mk "b", .. }]] => true
  | some [[{ name := .mk "b", .. }], [{ name := .mk "a", .. }]] => true
  | _ => false
-- duplicate names rejected
#guard (sccGroupsKosaraju [bA, { name := .mk "a", ann := none, rhs := .primLit (.int 0) }]).isNone
-- empty
#guard match sccGroupsKosaraju [] with | some [] => true | _ => false

end Scc.BindingGlue
