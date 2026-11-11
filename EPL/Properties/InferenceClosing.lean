import EPL.Properties.InferenceModelAgreement

namespace EPL

/-- Closing the fresh rigid block used to check a written scheme is inverse to
opening the resulting scheme at that same outer boundary. -/
theorem PolyTy.openRigids_closeRigids
    {openTy : Ty} {rigidCount count : Nat}
    (openScoped : openTy.Scoped (rigidCount + count) 0) :
    PolyTy.openRigids
      (⟨count, openTy.closeRigids rigidCount count⟩ : PolyTy)
      rigidCount = openTy := by
  change (openTy.closeRigids rigidCount count).openWith
    (rigidBlock rigidCount count) = openTy
  induction openScoped with
  | prim => rfl
  | arrow _ _ ihDomain ihCodomain =>
      simp only [Ty.closeRigids, Ty.openWith, ihDomain, ihCodomain]
  | bvar hlt => omega
  | rigid hlt =>
      rename_i level
      simp only [Ty.closeRigids]
      by_cases hOuter : level < rigidCount
      · rw [if_pos hOuter]
        rfl
      · rw [if_neg hOuter]
        have hLocal : level - rigidCount < count := by omega
        rw [if_pos hLocal]
        simp only [Ty.openWith, rigidBlock, List.getElem?_map]
        have hIndex : level - rigidCount < (List.range count).length := by
          simpa using hLocal
        rw [List.getElem?_eq_getElem hIndex, Option.map_some,
          Option.getD_some, List.getElem_range]
        congr
        omega
  | mvar id => rfl

/-- A match against an opened written template closes back to a match against
the original template, preserving local named-hole coherence. -/
theorem Template.matches_closeRigids
    {template : Template} {openTy : Ty} {rigidCount count : Nat}
    (templateScoped : template.Scoped rigidCount count)
    (openScoped : openTy.Scoped (rigidCount + count) 0)
    (openedMatches :
      (template.openRigidsFrom 0 rigidCount count).Matches openTy) :
    template.Matches (openTy.closeRigids rigidCount count) := by
  let closeHoles : HoleAssignment → HoleAssignment :=
    List.map fun entry =>
      (entry.1, entry.2.closeRigids rigidCount count)
  have closeHoles_unique : ∀ {holes : HoleAssignment},
      holes.Unique → (closeHoles holes).Unique := by
    intro holes unique
    simpa [HoleAssignment.Unique, closeHoles, List.map_map,
      Function.comp_def] using unique
  have closeHoles_lookup : ∀ (holes : HoleAssignment) (name : String),
      (closeHoles holes).lookup name =
        (holes.lookup name).map (Ty.closeRigids rigidCount count) := by
    intro holes name
    induction holes with
    | nil => rfl
    | cons entry rest ih =>
        rcases entry with ⟨key, ty⟩
        simp only [closeHoles, List.map_cons, List.lookup]
        split
        · rfl
        · simpa [closeHoles] using ih
  have close_open : ∀ {ty : Ty}, ty.Scoped rigidCount count →
      (ty.openRigidsFrom 0 rigidCount count).closeRigids
        rigidCount count = ty := by
    intro ty typeScoped
    induction typeScoped with
    | prim => rfl
    | arrow _ _ ihDomain ihCodomain =>
        simp only [Ty.openRigidsFrom, Ty.closeRigids, ihDomain, ihCodomain]
    | bvar hlt =>
        simp [Ty.openRigidsFrom, Ty.closeRigids, hlt]
    | rigid hlt =>
        simp [Ty.openRigidsFrom, Ty.closeRigids, hlt]
    | mvar id => rfl
  rcases openedMatches with ⟨holes, holesUnique, fits⟩
  refine ⟨closeHoles holes, closeHoles_unique holesUnique, ?_⟩
  induction templateScoped generalizing openTy holes with
  | fixed typeWF =>
      cases fits
      rw [close_open typeWF.1]
      exact .fixed
  | hole =>
      cases fits
      exact .hole
  | named =>
      cases fits with
      | named lookup =>
          apply Template.Fits.named
          rw [closeHoles_lookup, lookup]
          rfl
  | arrow _ _ ihDomain ihCodomain =>
      cases fits with
      | arrow domainFits codomainFits =>
          cases openScoped with
          | arrow domainOpenScoped codomainOpenScoped =>
              exact .arrow
                (ihDomain domainOpenScoped holes holesUnique domainFits)
                (ihCodomain codomainOpenScoped holes holesUnique codomainFits)

end EPL
