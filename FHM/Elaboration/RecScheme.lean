import FHM.Elaboration.Input
import FHM.CoreBackend.Infer

/-! Ordered completion schemes for recursive members. Written slots retain
all authored positions; remaining occurring pool variables follow them. -/

namespace Elaboration

/-- Preserve the written prefix, including vacuous slots, then quantify the
remaining pool variables that occur in this member's monotype. -/
def recNames (written pool : List Nat) (ty : Ty) : List Nat :=
  written ++ pool.filter (fun v => decide (v ∈ ty.freeVars) && decide (v ∉ written))

def recScheme (written pool : List Nat) (ty : Ty) : PolyTy :=
  ⟨(recNames written pool ty).length, Ty.closeOver (recNames written pool ty) ty⟩

/-- Complete signatures retain their exact scheme; monotypes use the member's
own ordered written prefix and the shared pool. -/
def _root_.RecSpec.completedScheme (written pool : List Nat) : RecSpec → PolyTy
  | .mono ty => recScheme written pool ty
  | .poly scheme => scheme

@[simp] theorem recNames_take_prefix (written pool : List Nat) (ty : Ty) :
    (recNames written pool ty).take written.length = written := by
  simp [recNames]

theorem recNames_prefix (written pool : List Nat) (ty : Ty) :
    List.IsPrefix written (recNames written pool ty) :=
  ⟨_, rfl⟩

theorem recNames_prefix_length_le (written pool : List Nat) (ty : Ty) :
    written.length ≤ (recNames written pool ty).length := by
  simp only [recNames, List.length_append]
  omega

@[simp] theorem mem_recNames {written pool : List Nat} {ty : Ty} {v : Nat} :
    v ∈ recNames written pool ty ↔
      v ∈ written ∨ (v ∈ pool ∧ v ∈ ty.freeVars ∧ v ∉ written) := by
  simp [recNames, List.mem_filter]

theorem recNames_nodup {written pool : List Nat} {ty : Ty}
    (hprefix : written.Nodup) (hpool : pool.Nodup) :
    (recNames written pool ty).Nodup := by
  refine List.nodup_append.mpr ⟨hprefix, hpool.filter _, ?_⟩
  intro v hv w hw heq
  have hparts : w ∈ ty.freeVars ∧ w ∉ written := by
    simpa only [Bool.and_eq_true, decide_eq_true_eq] using (List.mem_filter.mp hw).2
  exact hparts.2 (heq ▸ hv)

/-- Every pool variable occurring in this member is quantified. -/
theorem mem_recNames_of_mem_pool {written pool : List Nat} {ty : Ty} {v : Nat}
    (hpool : v ∈ pool) (hfree : v ∈ ty.freeVars) :
    v ∈ recNames written pool ty := by
  by_cases hp : v ∈ written
  · exact mem_recNames.mpr (Or.inl hp)
  · exact mem_recNames.mpr (Or.inr ⟨hpool, hfree, hp⟩)

theorem not_mem_pool_of_not_mem_recNames {written pool : List Nat} {ty : Ty} {v : Nat}
    (hfree : v ∈ ty.freeVars) (hnames : v ∉ recNames written pool ty) : v ∉ pool :=
  fun hpool => hnames (mem_recNames_of_mem_pool hpool hfree)

theorem recScheme_wf {written pool : List Nat} {ty : Ty} (hlc : ty.IsLC) :
    (recScheme written pool ty).WF :=
  Ty.closeOver_preserves_bvars hlc

/-- Closing names generalizes the original monotype; uniqueness is needed for
other opening arguments, but not for this direction of scheme generality. -/
theorem recScheme_generalizes_mono {written pool : List Nat} {ty : Ty} (hlc : ty.IsLC) :
    (recScheme written pool ty).Generalizes (PolyTy.mkTrivial ty) := by
  intro args target _ hinst
  have htarget : target = ty := InstantiatesBy.eq_of_closed hlc hinst
  subst target
  refine ⟨(recNames written pool ty).map Ty.fvar, ?_, ?_⟩
  · intro t ht
    obtain ⟨_, _, heq⟩ := List.mem_map.mp ht
    rw [← heq]
    exact .fvar
  · have hopen := InstantiatesBy.openVars (Xs := recNames written pool ty)
      (Ty.closeOver_preserves_bvars hlc) (Nat.le_refl _)
    rwa [Ty.openVars_closeOver_self hlc] at hopen

/-- Closing the occurring pool variables leaves only outer variables free. -/
theorem recScheme_freeVars_outer {written pool outer : List Nat} {ty : Ty}
    (hcover : ∀ v ∈ ty.freeVars, v ∈ pool ++ outer) :
    ∀ v ∈ (recScheme written pool ty).body.freeVars, v ∈ outer := by
  intro v hv
  have hty := Ty.freeVars_closeOver_subset hv
  rcases List.mem_append.mp (hcover v hty) with hpool | houter
  · exact False.elim (Ty.not_mem_closeOver_freeVars
      (mem_recNames_of_mem_pool hpool hty) hv)
  · exact houter

@[simp] theorem _root_.RecSpec.completedScheme_mono (written pool : List Nat) (ty : Ty) :
    RecSpec.completedScheme written pool (.mono ty) = recScheme written pool ty := rfl

@[simp] theorem _root_.RecSpec.completedScheme_poly (written pool : List Nat) (scheme : PolyTy) :
    RecSpec.completedScheme written pool (.poly scheme) = scheme := rfl

theorem _root_.RecSpec.completedScheme_wf {written pool : List Nat} {spec : RecSpec}
    (h : spec.LC) : (spec.completedScheme written pool).WF := by
  cases spec with
  | mono ty => exact recScheme_wf h
  | poly scheme => exact h

/-- Generic source transformation also updates free outer variables of complete
contracts. Their quantified binder count and bound variables stay unchanged. -/
def _root_.RecSpec.onSubstSource (S : Subst) : RecSpec → RecSpec
  | .mono ty => .mono (S.onTy ty)
  | .poly scheme => .poly (S.onPolyTy scheme)

/-- Only a complete written contract cuts recursive dependencies. Partial
annotations retain monomorphic recursive use until their component is solved. -/
def LetAnn.recModeAnn : LetAnn → Option PolyTy
  | .complete scheme => some scheme
  | _ => none

def LetAnn.recPrefixCount : LetAnn → Nat
  | .partialForall count _ => count
  | _ => 0

def recRenameNames (pool fresh names : List Nat) : List Nat :=
  names.map (fun name => (fresh[pool.idxOf name]?).getD name)

def recCompletedSchemes (specs : List RecSpec) (prefixes : List (List Nat))
    (pool : List Nat) : List PolyTy :=
  specs.mapIdx (fun i spec => spec.completedScheme (prefixes[i]?.getD []) pool)

def recBodyCtx (ctx : Ctx) (specs : List RecSpec) (prefixes : List (List Nat))
    (pool : List Nat) : Ctx :=
  { ctx with env := recCompletedSchemes specs prefixes pool ++ ctx.env }

def recStageEntry (prefixes : List (List Nat)) (done pool fresh : List Nat)
    (member : Nat) (spec : RecSpec) : PolyTy :=
  match spec with
  | .poly scheme => scheme
  | .mono ty =>
      if member ∈ done then recScheme (prefixes[member]?.getD []) pool ty
      else PolyTy.mkTrivial (Ty.renameG pool fresh ty)

def recStageCtx (ctx : Ctx) (specs : List RecSpec) (prefixes : List (List Nat))
    (done pool fresh : List Nat) : Ctx :=
  { ctx with env := specs.mapIdx (recStageEntry prefixes done pool fresh) ++ ctx.env }

structure RecPrefixesWF (anns : List LetAnn) (specs : List RecSpec)
    (prefixes : List (List Nat)) (pool : List Nat) : Prop where
  length : prefixes.length = specs.length
  member : ∀ (i : Nat) (ann : LetAnn) (names : List Nat), anns[i]? = some ann → prefixes[i]? = some names →
    names.length = ann.recPrefixCount ∧ names.Nodup ∧ ∀ name ∈ names, name ∈ pool




/-- Reordering quantified names and retaining unused names changes no instances
when the same occurring free variables are closed. -/
theorem closeScheme_generalizes_of_same_bound_vars {ty : Ty} {source target : List Nat}
    (hlc : ty.IsLC) (hnd : target.Nodup)
    (hcover : ∀ v ∈ ty.freeVars, v ∈ source ↔ v ∈ target) :
    PolyTy.Generalizes ⟨source.length, Ty.closeOver source ty⟩
      ⟨target.length, Ty.closeOver target ty⟩ := by
  obtain ⟨Xs, hlen, hXs, hav⟩ := exists_fresh_names (target ++ ty.freeVars) target.length
  let R : Subst := target.zip (Xs.map Ty.fvar)
  have hR : ∀ p ∈ R, p.2.IsLC := by
    intro p hp
    obtain ⟨_, _, heq⟩ := List.mem_map.mp (List.of_mem_zip hp).2
    rw [← heq]; exact .fvar
  have htargetXs : ∀ v ∈ target, v ∉ Xs := by
    intro v hv hx
    exact hav v hx (List.mem_append_left _ hv)
  have hXsTy : ∀ x ∈ Xs, x ∉ ty.freeVars := by
    intro x hx ht
    exact hav x hx (List.mem_append_right _ ht)
  have hfixed : R.onPolyTy ⟨source.length, Ty.closeOver source ty⟩ =
      ⟨source.length, Ty.closeOver source ty⟩ := by
    unfold Subst.onPolyTy
    congr 1
    apply Ty.substFvars_eq_self_of_no_key
    intro p hp hv
    have hty := Ty.freeVars_closeOver_subset hv
    exact Ty.not_mem_closeOver_freeVars ((hcover p.1 hty).mpr (List.of_mem_zip hp).1) hv
  have hh := closeOver_generalizes (g := source) (M := ⟨target.length, Ty.closeOver target ty⟩) hlc hR
    (Ty.closeOver_preserves_bvars (vars := target) hlc) hXs hlen
    (fun x hx hv => hXsTy x hx (Ty.freeVars_closeOver_subset hv))
    (Ty.openVars_closeOver_rename hlc hnd hlen htargetXs)
    (by rw [hfixed]; exact fun x hx hv => hXsTy x hx (Ty.freeVars_closeOver_subset hv))
  rwa [hfixed] at hh

theorem recScheme_generalizes_genGroup {written pool : List Nat} {ty : Ty}
    (hlc : ty.IsLC) (hpool : pool.Nodup) (hprefix : ∀ v ∈ written, v ∈ pool) :
    (recScheme written pool ty).Generalizes (PolyTy.genGroup pool ty) := by
  apply closeScheme_generalizes_of_same_bound_vars hlc (hpool.filter _)
  intro v hv
  simp only [mem_recNames, List.mem_filter, decide_eq_true_eq]
  constructor
  · rintro (hw | ⟨hp, _, _⟩)
    · exact ⟨hprefix v hw, hv⟩
    · exact ⟨hp, hv⟩
  · rintro ⟨hp, _⟩
    by_cases hw : v ∈ written
    · exact .inl hw
    · exact .inr ⟨hp, hv, hw⟩

theorem genGroup_generalizes_recScheme {written pool : List Nat} {ty : Ty}
    (hlc : ty.IsLC) (hpool : pool.Nodup) (hnd : written.Nodup)
    (hprefix : ∀ v ∈ written, v ∈ pool) :
    (PolyTy.genGroup pool ty).Generalizes (recScheme written pool ty) := by
  apply closeScheme_generalizes_of_same_bound_vars hlc (recNames_nodup hnd hpool)
  intro v hv
  simp only [mem_recNames, Ty.genFilter, List.mem_filter, decide_eq_true_eq]
  constructor
  · rintro ⟨hp, _⟩
    by_cases hw : v ∈ written
    · exact .inl hw
    · exact .inr ⟨hp, hv, hw⟩
  · rintro (hw | ⟨hp, _, _⟩)
    · exact ⟨hprefix v hw, hv⟩
    · exact ⟨hp, hv⟩




/-- The filtered pool scheme permits every simultaneous pool renaming. -/
theorem genGroup_generalizes_rename_mono {G Xs : List Nat} {ty : Ty} (hlc : ty.IsLC) :
    (PolyTy.genGroup G ty).Generalizes (PolyTy.mkTrivial (Ty.renameG G Xs ty)) := by
  let R : Subst := G.zip (Xs.map Ty.fvar)
  have hR : ∀ p ∈ R, p.2.IsLC := by
    intro p hp
    obtain ⟨_, _, heq⟩ := List.mem_map.mp (List.of_mem_zip hp).2
    rw [← heq]; exact .fvar
  have hbase : (PolyTy.genGroup G ty).Generalizes (PolyTy.mkTrivial ty) := by
    simpa [recScheme, recNames, PolyTy.genGroup, Ty.genFilter] using
      (recScheme_generalizes_mono (written := []) (pool := G) hlc)
  have hfixed : R.onPolyTy (PolyTy.genGroup G ty) = PolyTy.genGroup G ty := by
    unfold Subst.onPolyTy
    congr 1
    apply Ty.substFvars_eq_self_of_no_key
    intro p hp hv
    apply Ty.not_mem_closeOver_freeVars (gs := Ty.genFilter G ty) _ hv
    exact List.mem_filter.mpr ⟨(List.of_mem_zip hp).1, by
      simpa using Ty.freeVars_closeOver_subset hv⟩
  have hh := hbase.onSubst (S := R) hlc hR
  rw [hfixed] at hh
  exact hh

/-- Read the member's prefix invariant in the total indexing convention used
by completed environments. -/
theorem RecPrefixesWF.get {anns : List LetAnn} {specs : List RecSpec}
    (h : RecPrefixesWF anns specs prefixes G) (hlen : anns.length = specs.length)
    (hi : i < specs.length) :
    (prefixes[i]?.getD []).Nodup ∧ ∀ v ∈ prefixes[i]?.getD [], v ∈ G := by
  cases hp : prefixes[i]? with
  | none => simp
  | some names =>
      have hia : i < anns.length := by omega
      exact (h.member i anns[i] names (List.getElem?_eq_getElem hia) hp).2

/-- Erased Core's filtered pool exports generalize each ordered completion. -/
theorem bodySchemes_generalize_recCompleted {anns : List LetAnn} {specs : List RecSpec}
    (hwf : RecSpecs.WF (anns.map LetAnn.recModeAnn) bindings specs G)
    (hp : RecPrefixesWF anns specs prefixes G) :
    List.Forall₂ PolyTy.Generalizes (specs.map (RecSpec.bodyScheme G))
      (recCompletedSchemes specs prefixes G) := by
  apply List.forall₂_of_length_eq_of_get (by simp [recCompletedSchemes])
  intro i hb hc
  have hi : i < specs.length := by simpa using hb
  have hannsLen : anns.length = specs.length := by
    have := congrArg List.length hwf.anns_eq
    simpa using this.symm
  obtain ⟨hnd, hsub⟩ := hp.get hannsLen hi
  simp only [recCompletedSchemes, List.get_eq_getElem, List.getElem_map, List.getElem_mapIdx]
  cases hs : specs[i]'hi with
  | mono ty =>
      exact genGroup_generalizes_recScheme
        (hwf.mono_lc ty (hs ▸ List.getElem_mem hi)) hwf.nodup hnd hsub
  | poly scheme => exact PolyTy.Generalizes.refl _

/-- Ordered completed schemes and Core's filtered pool exports have precisely
identical instances, including unused authored quantifiers. -/
theorem recCompleted_generalize_bodySchemes {anns : List LetAnn} {specs : List RecSpec}
    (hwf : RecSpecs.WF (anns.map LetAnn.recModeAnn) bindings specs G)
    (hp : RecPrefixesWF anns specs prefixes G) :
    List.Forall₂ PolyTy.Generalizes (recCompletedSchemes specs prefixes G)
      (specs.map (RecSpec.bodyScheme G)) := by
  apply List.forall₂_of_length_eq_of_get (by simp [recCompletedSchemes])
  intro i hc hb
  have hi : i < specs.length := by simpa [recCompletedSchemes] using hc
  have hannsLen : anns.length = specs.length := by
    have := congrArg List.length hwf.anns_eq
    simpa using this.symm
  obtain ⟨_, hsub⟩ := hp.get hannsLen hi
  simp only [recCompletedSchemes, List.get_eq_getElem, List.getElem_map, List.getElem_mapIdx]
  cases hs : specs[i]'hi with
  | mono ty =>
      exact recScheme_generalizes_genGroup
        (hwf.mono_lc ty (hs ▸ List.getElem_mem hi)) hwf.nodup hsub
  | poly scheme => exact PolyTy.Generalizes.refl _

/-- The final filtered pool environment generalizes the new stage environment;
current/pending members remain monomorphic at the same shared opening. -/
theorem bodySchemes_generalize_recStage {anns : List LetAnn} {specs : List RecSpec}
    (hwf : RecSpecs.WF (anns.map LetAnn.recModeAnn) bindings specs G)
    (hp : RecPrefixesWF anns specs prefixes G) :
    List.Forall₂ PolyTy.Generalizes (specs.map (RecSpec.bodyScheme G))
      (specs.mapIdx (recStageEntry prefixes done G Xs)) := by
  apply List.forall₂_of_length_eq_of_get (by simp)
  intro i hb hs
  have hi : i < specs.length := by simpa using hb
  have hannsLen : anns.length = specs.length := by
    have := congrArg List.length hwf.anns_eq
    simpa using this.symm
  obtain ⟨hnd, hsub⟩ := hp.get hannsLen hi
  simp only [List.get_eq_getElem, List.getElem_map, List.getElem_mapIdx]
  cases he : specs[i]'hi with
  | mono ty =>
      simp only [RecSpec.bodyScheme, recStageEntry]
      split
      · exact genGroup_generalizes_recScheme
          (hwf.mono_lc ty (he ▸ List.getElem_mem hi)) hwf.nodup hnd hsub
      · exact genGroup_generalizes_rename_mono (hwf.mono_lc ty (he ▸ List.getElem_mem hi))
  | poly scheme => exact PolyTy.Generalizes.refl _




private def poolMap (G W : List Nat) (v : Nat) : Nat := (W[G.idxOf v]?).getD v

private theorem poolMap_eq {G W : List Nat} (hlen : W.length = G.length) {v : Nat} (hv : v ∈ G) :
    poolMap G W v = W[G.idxOf v]'(by have := List.idxOf_lt_length_iff.mpr hv; omega) := by
  have hi : G.idxOf v < W.length := by have := List.idxOf_lt_length_iff.mpr hv; omega
  unfold poolMap
  rw [List.getElem?_eq_getElem hi]
  rfl

private theorem poolMap_mem {G W : List Nat} (hlen : W.length = G.length) {v : Nat} (hv : v ∈ G) :
    poolMap G W v ∈ W := by
  rw [poolMap_eq hlen hv]
  exact List.getElem_mem _

private theorem poolMap_inj {G W : List Nat} (hlen : W.length = G.length) (hW : W.Nodup)
    {a b : Nat} (ha : a ∈ G) (hb : b ∈ G) (heq : poolMap G W a = poolMap G W b) : a = b := by
  rw [poolMap_eq hlen ha, poolMap_eq hlen hb] at heq
  have hi := (List.Nodup.getElem_inj_iff hW).mp heq
  have hh := congrArg (fun i => G[i]?) hi
  simpa only [List.getElem?_idxOf ha, List.getElem?_idxOf hb, Option.some.injEq] using hh

private theorem poolMap_pool {G W : List Nat} (hlen : W.length = G.length) (hG : G.Nodup) :
    G.map (poolMap G W) = W := by
  apply List.ext_get (by simp [hlen])
  intro i hi hj
  simp only [List.get_eq_getElem, List.getElem_map]
  simp only [poolMap, hG.idxOf_getElem i (by simpa using hi), List.getElem?_eq_getElem hj, Option.getD_some]

private theorem poolMap_sublist_mem {G W names : List Nat}
    (hlen : W.length = G.length) (hW : W.Nodup) (hnames : ∀ v ∈ names, v ∈ G)
    {v : Nat} (hv : v ∈ G) :
    poolMap G W v ∈ names.map (poolMap G W) ↔ v ∈ names := by
  constructor
  · intro hm
    obtain ⟨a, ha, heq⟩ := List.mem_map.mp hm
    exact poolMap_inj hlen hW (hnames a ha) hv heq ▸ ha
  · intro hm
    exact List.mem_map.mpr ⟨v, hm, rfl⟩

private theorem poolMap_occurs {G W : List Nat} {ty : Ty}
    (hlen : W.length = G.length) (hG : G.Nodup) (hW : W.Nodup)
    (hGW : ∀ g ∈ G, g ∉ W) (hWty : ∀ w ∈ W, w ∉ ty.freeVars)
    {v : Nat} (hv : v ∈ G) :
    poolMap G W v ∈ (Ty.renameG G W ty).freeVars ↔ v ∈ ty.freeVars := by
  exact Ty.mem_freeVars_renameG_iff hlen hG hW hGW hWty (List.getElem?_idxOf hv)
    (by rw [poolMap_eq hlen hv]; exact List.getElem?_eq_getElem _)

private theorem poolMap_nodup {G W names : List Nat}
    (hlen : W.length = G.length) (hW : W.Nodup) (hnd : names.Nodup)
    (hnames : ∀ v ∈ names, v ∈ G) : (names.map (poolMap G W)).Nodup := by
  induction names with
  | nil => exact .nil
  | cons head rest ih =>
    obtain ⟨hn, ht⟩ := List.nodup_cons.mp hnd
    apply List.nodup_cons.mpr
    refine ⟨?_, ih ht (fun v hv => hnames v (List.mem_cons_of_mem _ hv))⟩
    intro hm
    obtain ⟨v, hv, heq⟩ := List.mem_map.mp hm
    exact hn (poolMap_inj hlen hW (hnames v (List.mem_cons_of_mem _ hv))
      (hnames head List.mem_cons_self) heq ▸ hv)

theorem recNames_rename_pool {G W names : List Nat} {ty : Ty}
    (hlen : W.length = G.length) (hG : G.Nodup) (hW : W.Nodup)
    (hGW : ∀ g ∈ G, g ∉ W) (hWty : ∀ w ∈ W, w ∉ ty.freeVars)
    (hnames : ∀ v ∈ names, v ∈ G) :
    recNames (recRenameNames G W names) W (Ty.renameG G W ty) =
      recRenameNames G W (recNames names G ty) := by
  change names.map (poolMap G W) ++ W.filter _ = (names ++ G.filter _).map (poolMap G W)
  rw [List.map_append]
  congr 1
  calc
    W.filter (fun v => decide (v ∈ (Ty.renameG G W ty).freeVars) && decide (v ∉ names.map (poolMap G W))) =
        (G.map (poolMap G W)).filter (fun v => decide (v ∈ (Ty.renameG G W ty).freeVars) && decide (v ∉ names.map (poolMap G W))) :=
      congrArg (fun l => l.filter (fun v => decide (v ∈ (Ty.renameG G W ty).freeVars) && decide (v ∉ names.map (poolMap G W)))) (poolMap_pool hlen hG).symm
    _ = (G.filter (fun v => decide (poolMap G W v ∈ (Ty.renameG G W ty).freeVars) && decide (poolMap G W v ∉ names.map (poolMap G W)))).map (poolMap G W) := by
      rw [List.filter_map]; rfl
    _ = (G.filter (fun v => decide (v ∈ ty.freeVars) && decide (v ∉ names))).map (poolMap G W) := by
      congr 1
      apply List.filter_congr
      intro v hv
      simp only [poolMap_occurs hlen hG hW hGW hWty hv, poolMap_sublist_mem hlen hW hnames hv]

@[simp] theorem recRenameNames_length (G W names : List Nat) :
    (recRenameNames G W names).length = names.length := List.length_map _

theorem recRenameNames_nodup {G W names : List Nat}
    (hlen : W.length = G.length) (hW : W.Nodup) (hnd : names.Nodup)
    (hnames : ∀ v ∈ names, v ∈ G) : (recRenameNames G W names).Nodup :=
  poolMap_nodup hlen hW hnd hnames

theorem recRenameNames_mem {G W names : List Nat}
    (hlen : W.length = G.length) (hnames : ∀ v ∈ names, v ∈ G) :
    ∀ v ∈ recRenameNames G W names, v ∈ W := by
  intro v hv
  obtain ⟨original, ho, rfl⟩ := List.mem_map.mp hv
  exact poolMap_mem hlen (hnames original ho)

theorem recRenameNames_composition {G W Xs names : List Nat}
    (hlen : W.length = G.length) (hXs : Xs.length = G.length) (hW : W.Nodup)
    (hnames : ∀ v ∈ names, v ∈ G) :
    recRenameNames W Xs (recRenameNames G W names) = recRenameNames G Xs names := by
  simp only [recRenameNames, List.map_map]
  apply List.map_congr_left
  intro v hv
  have hi : G.idxOf v < W.length := by have := List.idxOf_lt_length_iff.mpr (hnames v hv); omega
  simp only [Function.comp_def]
  change poolMap W Xs (poolMap G W v) = poolMap G Xs v
  rw [poolMap_eq hlen (hnames v hv)]
  have hiXs : G.idxOf v < Xs.length := by omega
  simp only [poolMap, hW.idxOf_getElem _ hi, List.getElem?_eq_getElem hiXs, Option.getD_some]

theorem Ty.mem_freeVars_onTy_of_pool_avoid {S : Subst} {W : List Nat} {ty : Ty} {v : Nat}
    (hdom : ∀ p ∈ S, p.1 ∉ W)
    (hran : ∀ p ∈ S, ∀ x ∈ p.2.freeVars, x ∉ W) (hv : v ∈ W) :
    v ∈ (S.onTy ty).freeVars ↔ v ∈ ty.freeVars := by
  constructor
  · intro himage
    by_contra hnot
    exact Subst.notMemOnTy (fun p hp hc => hran p hp v hc hv) hnot himage
  · intro hty
    apply Ty.mem_freeVars_substFvars_image.mpr
    refine ⟨v, hty, ?_⟩
    have hfix : S.onTy (.fvar v) = .fvar v := by
      apply Ty.substFvars_eq_self_of_no_key
      intro p hp hc
      have heq := List.mem_singleton.mp hc
      exact hdom p hp (heq ▸ hv)
    change v ∈ (S.onTy (.fvar v)).freeVars
    rw [hfix]
    exact List.mem_cons_self

theorem recNames_subst_pool_avoid {S : Subst} {W names : List Nat} {ty : Ty}
    (hdom : ∀ p ∈ S, p.1 ∉ W)
    (hran : ∀ p ∈ S, ∀ x ∈ p.2.freeVars, x ∉ W) :
    recNames names W (S.onTy ty) = recNames names W ty := by
  unfold recNames
  congr 1
  apply List.filter_congr
  intro v hv
  simp only [Ty.mem_freeVars_onTy_of_pool_avoid hdom hran hv]

private theorem ty_substFvars_congr {subst other : List (Nat × Ty)} {ty : Ty}
    (h : ∀ v ∈ ty.freeVars, (Ty.fvar v).substFvars subst = (Ty.fvar v).substFvars other) : ty.substFvars subst = ty.substFvars other := by
  induction ty using Ty.rec_strong with
  | prim p => simp only [Ty.substFvars_prim]
  | bvar i => simp only [Ty.substFvars_bvar]
  | fvar n => exact h n (by simp only [Ty.freeVars, List.mem_singleton])
  | arrow a b iha ihb =>
      rw [Ty.substFvars_arrow, Ty.substFvars_arrow,
        iha (fun v hv => h v (by simp only [Ty.freeVars, List.mem_dedup, List.mem_append]; exact .inl hv)),
        ihb (fun v hv => h v (by simp only [Ty.freeVars, List.mem_dedup, List.mem_append]; exact .inr hv))]
  | customTy name args ih =>
      rw [Ty.substFvars_customTy, Ty.substFvars_customTy]
      congr 1
      apply List.map_congr_left
      intro ty hty
      exact ih ty hty (fun v hv => h v (TyList.mem_freeVars_of_mem hty hv))

private theorem renameG_restrict_pool {G W names : List Nat} {ty : Ty}
    (hlen : W.length = G.length) (hG : G.Nodup) (hnd : names.Nodup)
    (hGW : ∀ g ∈ G, g ∉ W) (hnames : ∀ v ∈ names, v ∈ G)
    (hcover : ∀ v ∈ ty.freeVars, v ∈ G → v ∈ names) :
    Ty.renameG G W ty = Ty.renameG names (recRenameNames G W names) ty := by
  apply ty_substFvars_congr
  intro v hv
  by_cases hg : v ∈ G
  · have hn := hcover v hv hg
    have hfull : Ty.substFvars (G.zip (W.map Ty.fvar)) (.fvar v) = .fvar (poolMap G W v) :=
      Ty.substFvars_zip_fvar_renameG hlen hG hGW (List.getElem?_idxOf hg)
        (by rw [poolMap_eq hlen hg]; exact List.getElem?_eq_getElem _)
    rw [hfull]
    symm
    apply Ty.substFvars_zip_fvar_renameG (by simp [recRenameNames]) hnd
      (fun n hm hc => hGW n (hnames n hm) (recRenameNames_mem hlen hnames n hc))
      (List.getElem?_idxOf hn)
    simp only [recRenameNames, List.getElem?_map, List.getElem?_idxOf hn, Option.map_some]
    rfl
  · have hn : v ∉ names := fun hv => hg (hnames v hv)
    have fix : ∀ (keys : List Nat) (values : List Ty), v ∉ keys →
        Ty.substFvars (keys.zip values) (.fvar v) = .fvar v := by
      intro keys values hn
      apply Ty.substFvars_eq_self_of_no_key
      intro p hp hc
      exact hn ((List.mem_singleton.mp hc) ▸ (List.of_mem_zip hp).1)
    rw [fix _ _ hg, fix _ _ hn]

theorem recScheme_rename_pool {G W names : List Nat} {ty : Ty}
    (hlc : ty.IsLC) (hlen : W.length = G.length) (hG : G.Nodup) (hW : W.Nodup)
    (hGW : ∀ g ∈ G, g ∉ W) (hWty : ∀ w ∈ W, w ∉ ty.freeVars)
    (hnd : names.Nodup) (hnames : ∀ v ∈ names, v ∈ G) :
    recScheme (recRenameNames G W names) W (Ty.renameG G W ty) = recScheme names G ty := by
  unfold recScheme
  rw [recNames_rename_pool hlen hG hW hGW hWty hnames]
  have hsub : ∀ v ∈ recNames names G ty, v ∈ G := by
    intro v hv
    rcases mem_recNames.mp hv with hv | ⟨hv, _, _⟩
    · exact hnames v hv
    · exact hv
  have hclose := Ty.closeOver_rename (gs := recNames names G ty)
    (gs' := recRenameNames G W (recNames names G ty)) hlc
    (recRenameNames_length ..) (recNames_nodup hnd hG)
    (recRenameNames_nodup hlen hW (recNames_nodup hnd hG) hsub)
    (fun g hg hw => hGW g (hsub g hg) (recRenameNames_mem hlen hsub g hw))
    (fun w hw => hWty w (recRenameNames_mem hlen hsub w hw))
  change Ty.closeOver (recRenameNames G W (recNames names G ty))
    (Ty.renameG (recNames names G ty) (recRenameNames G W (recNames names G ty)) ty) = _ at hclose
  rw [← renameG_restrict_pool hlen hG (recNames_nodup hnd hG) hGW hsub
    (fun v hv hg => mem_recNames_of_mem_pool hg hv)] at hclose
  simp only [recRenameNames_length]
  exact congrArg (PolyTy.mk (recNames names G ty).length) hclose

 theorem recScheme_subst_pool_avoid {S : Subst} {W names : List Nat} {ty : Ty}
    (hdom : ∀ p ∈ S, p.1 ∉ W)
    (hran : ∀ p ∈ S, ∀ x ∈ p.2.freeVars, x ∉ W)
    (hnames : ∀ v ∈ names, v ∈ W) :
    recScheme names W (S.onTy ty) = S.onPolyTy (recScheme names W ty) := by
  unfold recScheme Subst.onPolyTy
  rw [recNames_subst_pool_avoid hdom hran]
  congr 1
  symm
  apply Ty.substFvars_closeOver
  · intro p hp hv
    rcases mem_recNames.mp hv with hv | ⟨hv, _, _⟩
    · exact hdom p hp (hnames p.1 hv)
    · exact hdom p hp hv
  · intro p hp v hv hn
    rcases mem_recNames.mp hn with hn | ⟨hn, _, _⟩
    · exact hran p hp v hv (hnames v hn)
    · exact hran p hp v hv hn

/-- Freshen the bound pool before applying an arbitrary LC source substitution.
The freshness assumptions concern the newly chosen pool and cofinite opening. -/
theorem Ty.renameG_subst_fresh_pool {S : Subst} {G W Xs : List Nat} {ty : Ty}
    (hlc : ty.IsLC) (hS : ∀ p ∈ S, p.2.IsLC)
    (hlen : W.length = G.length) (hG : G.Nodup) (hW : W.Nodup)
    (hGW : ∀ g ∈ G, g ∉ W) (hWty : ∀ w ∈ W, w ∉ ty.freeVars)
    (hdomW : ∀ p ∈ S, p.1 ∉ W)
    (hranW : ∀ p ∈ S, ∀ v ∈ p.2.freeVars, v ∉ W)
    (hXs : Xs.length = G.length)
    (hGXs : ∀ g ∈ G, g ∉ Xs) (hWXs : ∀ w ∈ W, w ∉ Xs)
    (hdomXs : ∀ p ∈ S, p.1 ∉ Xs) :
    Ty.renameG W Xs (S.onTy (Ty.renameG G W ty)) = S.onTy (Ty.renameG G Xs ty) := by
  have hGWeq : Ty.renameG G W ty = Ty.openVars W (Ty.closeOver G ty) :=
    (Ty.openVars_closeOver_rename hlc hG hlen hGW).symm
  have hGXeq : Ty.renameG G Xs ty = Ty.openVars Xs (Ty.closeOver G ty) :=
    (Ty.openVars_closeOver_rename hlc hG hXs hGXs).symm
  have hnew : S.onTy (Ty.renameG G W ty) = Ty.openVars W (S.onTy (Ty.closeOver G ty)) := by
    rw [hGWeq, Subst.onTy_openVars hS hdomW]
  have hnewLC : (S.onTy (Ty.renameG G W ty)).IsLC := by
    apply Subst.onTy_lc hS
    apply Subst.onTy_lc (S := G.zip (W.map Ty.fvar)) _ hlc
    intro p hp
    obtain ⟨_, _, heq⟩ := List.mem_map.mp (List.of_mem_zip hp).2
    rw [← heq]; exact .fvar
  have hclose : Ty.closeOver W (S.onTy (Ty.renameG G W ty)) = S.onTy (Ty.closeOver G ty) := by
    rw [hnew]
    apply Ty.closeOver_openVars_self hW
    · rw [hlen]
      exact Subst.onTy_containsBvars hS (Ty.closeOver_preserves_bvars hlc)
    · intro w hw
      exact Subst.notMemOnTy (fun p hp hv => hranW p hp w hv hw)
        (fun hv => hWty w hw (Ty.freeVars_closeOver_subset hv))
  have hh := (Ty.openVars_closeOver_rename hnewLC hW (hXs.trans hlen.symm) hWXs).symm
  change Ty.renameG W Xs (S.onTy (Ty.renameG G W ty)) = _ at hh
  rw [hclose] at hh
  rw [hh, hGXeq, Subst.onTy_openVars hS hdomXs]

private theorem recRenameNames_getD (G W : List Nat) (prefixes : List (List Nat)) (i : Nat) :
    (prefixes.map (recRenameNames G W))[i]?.getD [] = recRenameNames G W (prefixes[i]?.getD []) := by
  rw [List.getElem?_map]
  cases prefixes[i]? <;> rfl

/-- Reparameterizing the bound pool and then substituting free outer leaves
commutes with the literal ordered/vacuous export list. -/
theorem recCompletedSchemes_subst_fresh_pool {S : Subst} {G W : List Nat}
    {specs : List RecSpec} {prefixes : List (List Nat)}
    (hS : ∀ p ∈ S, p.2.IsLC) (hlen : W.length = G.length) (hG : G.Nodup) (hW : W.Nodup)
    (hGW : ∀ g ∈ G, g ∉ W)
    (hWmono : ∀ ty, .mono ty ∈ specs → ∀ w ∈ W, w ∉ ty.freeVars)
    (hdomW : ∀ p ∈ S, p.1 ∉ W)
    (hranW : ∀ p ∈ S, ∀ v ∈ p.2.freeVars, v ∉ W)
    (hlc : ∀ ty, .mono ty ∈ specs → ty.IsLC)
    (hprefix : ∀ i, i < specs.length →
      (prefixes[i]?.getD []).Nodup ∧ ∀ v ∈ prefixes[i]?.getD [], v ∈ G) :
    recCompletedSchemes
      (specs.map (fun spec => RecSpec.onSubstSource S (RecSpec.onSubst (G.zip (W.map Ty.fvar)) spec)))
      (prefixes.map (recRenameNames G W)) W =
      (recCompletedSchemes specs prefixes G).map S.onPolyTy := by
  apply List.ext_get (by simp [recCompletedSchemes])
  intro i hi hj
  have hit : i < specs.length := by simpa [recCompletedSchemes] using hj
  simp only [recCompletedSchemes, List.get_eq_getElem, List.getElem_map, List.getElem_mapIdx,
    recRenameNames_getD]
  cases hs : specs[i]'hit with
  | poly scheme => rfl
  | mono ty =>
    obtain ⟨hnd, hsub⟩ := hprefix i hit
    have hty : .mono ty ∈ specs := hs ▸ List.getElem_mem hit
    change recScheme (recRenameNames G W (prefixes[i]?.getD [])) W
      (S.onTy (Ty.renameG G W ty)) = S.onPolyTy (recScheme (prefixes[i]?.getD []) G ty)
    rw [recScheme_subst_pool_avoid hdomW hranW (recRenameNames_mem hlen hsub),
      recScheme_rename_pool (hlc ty hty) hlen hG hW hGW (hWmono ty hty) hnd hsub]

 theorem recStageSchemes_subst_fresh_pool {S : Subst} {G W Xs : List Nat}
    {specs : List RecSpec} {prefixes : List (List Nat)}
    (hS : ∀ p ∈ S, p.2.IsLC) (hlen : W.length = G.length) (hG : G.Nodup) (hW : W.Nodup)
    (hGW : ∀ g ∈ G, g ∉ W)
    (hWmono : ∀ ty, .mono ty ∈ specs → ∀ w ∈ W, w ∉ ty.freeVars)
    (hdomW : ∀ p ∈ S, p.1 ∉ W)
    (hranW : ∀ p ∈ S, ∀ v ∈ p.2.freeVars, v ∉ W)
    (hlc : ∀ ty, .mono ty ∈ specs → ty.IsLC)
    (hprefix : ∀ i, i < specs.length →
      (prefixes[i]?.getD []).Nodup ∧ ∀ v ∈ prefixes[i]?.getD [], v ∈ G)
    (hXs : Xs.length = G.length) (hGXs : ∀ g ∈ G, g ∉ Xs)
    (hWXs : ∀ w ∈ W, w ∉ Xs) (hdomXs : ∀ p ∈ S, p.1 ∉ Xs) :
    (specs.map (fun spec => RecSpec.onSubstSource S (RecSpec.onSubst (G.zip (W.map Ty.fvar)) spec))).mapIdx
      (recStageEntry (prefixes.map (recRenameNames G W)) done W Xs) =
      (specs.mapIdx (recStageEntry prefixes done G Xs)).map S.onPolyTy := by
  apply List.ext_get (by simp)
  intro i hi hj
  have hit : i < specs.length := by simpa using hj
  simp only [List.get_eq_getElem, List.getElem_map, List.getElem_mapIdx]
  cases hs : specs[i]'hit with
  | poly scheme => rfl
  | mono ty =>
    have hty : .mono ty ∈ specs := hs ▸ List.getElem_mem hit
    simp only [RecSpec.onSubstSource, RecSpec.onSubst, recStageEntry, recRenameNames_getD]
    split
    · obtain ⟨hnd, hsub⟩ := hprefix i hit
      change recScheme (recRenameNames G W (prefixes[i]?.getD [])) W
        (S.onTy (Ty.renameG G W ty)) = S.onPolyTy (recScheme (prefixes[i]?.getD []) G ty)
      rw [recScheme_subst_pool_avoid hdomW hranW (recRenameNames_mem hlen hsub),
        recScheme_rename_pool (hlc ty hty) hlen hG hW hGW (hWmono ty hty) hnd hsub]
    · change PolyTy.mkTrivial (Ty.renameG W Xs (S.onTy (Ty.renameG G W ty))) =
        PolyTy.mkTrivial (S.onTy (Ty.renameG G Xs ty))
      rw [Ty.renameG_subst_fresh_pool (hlc ty hty) hS hlen hG hW hGW (hWmono ty hty)
        hdomW hranW hXs hGXs hWXs hdomXs]



@[simp] theorem LetAnn.recModeAnn_subst_source (ann : LetAnn) (S : Subst) :
    (ann.substTyFvars S).recModeAnn = ann.recModeAnn.map S.onPolyTy := by
  cases ann <;> rfl

@[simp] theorem LetAnn.recPrefixCount_subst_source (ann : LetAnn) (S : Subst) :
    (ann.substTyFvars S).recPrefixCount = ann.recPrefixCount := by
  cases ann <;> rfl

theorem RecPrefixesWF.subst_fresh_pool {S : Subst} {G W : List Nat}
    (h : RecPrefixesWF anns specs prefixes G) (hlen : W.length = G.length) (hW : W.Nodup) :
    RecPrefixesWF (anns.map (LetAnn.substTyFvars S))
      (specs.map (fun spec => RecSpec.onSubstSource S (RecSpec.onSubst (G.zip (W.map Ty.fvar)) spec)))
      (prefixes.map (recRenameNames G W)) W := by
  refine ⟨by simpa only [List.length_map] using h.length, ?_⟩
  intro i ann names ha hn
  rw [List.getElem?_map] at ha hn
  obtain ⟨ann0, ha0, rfl⟩ := Option.map_eq_some_iff.mp ha
  obtain ⟨names0, hn0, rfl⟩ := Option.map_eq_some_iff.mp hn
  obtain ⟨hcount, hnd, hsub⟩ := h.member i ann0 names0 ha0 hn0
  exact ⟨by simpa using hcount, recRenameNames_nodup hlen hW hnd hsub,
    recRenameNames_mem hlen hsub⟩

theorem RecSpecs.WF.subst_fresh_pool {S : Subst} {G W : List Nat}
    {anns : List LetAnn} {bindings : List Expr} {specs : List RecSpec}
    (h : RecSpecs.WF (anns.map LetAnn.recModeAnn) bindings specs G)
    (hS : ∀ p ∈ S, p.2.IsLC) (hW : W.Nodup) :
    RecSpecs.WF ((anns.map (LetAnn.substTyFvars S)).map LetAnn.recModeAnn) bindings
      (specs.map (fun spec => RecSpec.onSubstSource S (RecSpec.onSubst (G.zip (W.map Ty.fvar)) spec))) W := by
  have hR : ∀ p ∈ G.zip (W.map Ty.fvar), p.2.IsLC := by
    intro p hp
    obtain ⟨_, _, heq⟩ := List.mem_map.mp (List.of_mem_zip hp).2
    rw [← heq]; exact .fvar
  refine ⟨?_, by simpa only [List.length_map] using h.length, hW, ?_, ?_⟩
  · have hmap : (specs.map (fun spec => RecSpec.onSubstSource S
        (RecSpec.onSubst (G.zip (W.map Ty.fvar)) spec))).map RecSpec.ann =
        (specs.map RecSpec.ann).map (Option.map S.onPolyTy) := by
      simp only [List.map_map]
      apply List.map_congr_left
      intro spec _
      cases spec <;> rfl
    rw [hmap, h.anns_eq]
    simp only [List.map_map, Function.comp_def, LetAnn.recModeAnn_subst_source]
  · intro ty ht
    obtain ⟨spec, hs, heq⟩ := List.mem_map.mp ht
    cases spec with
    | poly scheme => cases heq
    | mono original =>
      cases heq
      exact Subst.onTy_lc hS (Subst.onTy_lc hR (h.mono_lc original hs))
  · intro scheme hs
    obtain ⟨spec, ho, heq⟩ := List.mem_map.mp hs
    cases spec with
    | mono ty => cases heq
    | poly original =>
      cases heq
      exact Subst.onPolyTy_wf hS (h.poly_wf original ho)


theorem _root_.RecSpec.lc_onSubstSource {S : Subst} (hS : ∀ p ∈ S, p.2.IsLC)
    {spec : RecSpec} (hs : spec.LC) : (spec.onSubstSource S).LC := by
  cases spec with
  | mono ty => exact Subst.onTy_lc hS hs
  | poly scheme => exact Subst.onPolyTy_wf hS hs

end Elaboration
