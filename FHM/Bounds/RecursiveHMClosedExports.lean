import FHM.Bounds.RecursiveHMClosedExitRuntime

/-! # Structural facts for generalized-group closed exports

`GeneralizedGroup.closedExports` is the environment boundary used by the body
rules for generalized recursive groups.  This module records the source-order
and closure-normality facts needed to consume that boundary without unfolding
its implementation at every static or runtime lookup.
-/

namespace FHM.Bounds.RecursiveHMUniform

open RecursiveHMJudgement CountSubstitution

theorem GeneralizedGroup.closedExports_length
    {output metadata path captures premises bodyTypes outerEnv}
    (group : GeneralizedGroup output metadata path captures premises bodyTypes outerEnv)
    (outer : Bindings) (types : Nat → BoundsTy) :
    (group.closedExports outer types).length = group.exports.length := by
  simp only [GeneralizedGroup.closedExports, List.length_map]

theorem GeneralizedGroup.closedExportCount
    {output metadata path captures premises bodyTypes outerEnv}
    (group : GeneralizedGroup output metadata path captures premises bodyTypes outerEnv)
    (outer : Bindings) (types : Nat → BoundsTy) :
    (group.closedExports outer types).length = group.rhss.length := by
  rw [group.closedExports_length, group.exportCount]

/-- Selection from the closed environment retains the exact source scheme and
    stores precisely its enclosing count and HM interpretations. -/
theorem GeneralizedGroup.closedExports_getElem?
    {output metadata path captures premises bodyTypes outerEnv}
    (group : GeneralizedGroup output metadata path captures premises bodyTypes outerEnv)
    (outer : Bindings) (types : Nat → BoundsTy)
    (offset : Nat) (inside : offset < group.exports.length) :
    (group.closedExports outer types)[offset]? = some
      (.closure (group.selected offset inside).rhs.certificate.interface.scheme
        (HMCountSchemeClosure.interpretedCountCaptures outer
          (group.selected offset inside).rhs.certificate.interface.scheme)
        (HMCountSchemeClosure.interpretedTypeCaptures types
          (group.selected offset inside).rhs.certificate.interface.scheme)) := by
  have selected := congrArg
    (Option.map fun s =>
      Binding.closure s (HMCountSchemeClosure.interpretedCountCaptures outer s)
        (HMCountSchemeClosure.interpretedTypeCaptures types s))
    (group.selected offset inside).selection
  simpa only [GeneralizedGroup.closedExports, GeneralizedGroup.exports,
    List.getElem?_map, Option.map_some] using selected

/-- The same selected lookup after the closed group has been prefixed to an
    arbitrary enclosing body environment. -/
theorem GeneralizedGroup.closedExports_append_getElem?
    {output metadata path captures premises bodyTypes outerEnv}
    (group : GeneralizedGroup output metadata path captures premises bodyTypes outerEnv)
    (outer : Bindings) (types : Nat → BoundsTy) (tail : List Binding)
    (offset : Nat) (inside : offset < group.exports.length) :
    (group.closedExports outer types ++ tail)[offset]? = some
      (.closure (group.selected offset inside).rhs.certificate.interface.scheme
        (HMCountSchemeClosure.interpretedCountCaptures outer
          (group.selected offset inside).rhs.certificate.interface.scheme)
        (HMCountSchemeClosure.interpretedTypeCaptures types
          (group.selected offset inside).rhs.certificate.interface.scheme)) := by
  rw [List.getElem?_append_left]
  · exact group.closedExports_getElem? outer types offset inside
  · simpa only [group.closedExports_length] using inside

theorem GeneralizedGroup.closedExport_mem
    {output metadata path captures premises bodyTypes outerEnv}
    (group : GeneralizedGroup output metadata path captures premises bodyTypes outerEnv)
    (outer : Bindings) (types : Nat → BoundsTy)
    (offset : Nat) (inside : offset < group.exports.length) :
    .closure (group.selected offset inside).rhs.certificate.interface.scheme
        (HMCountSchemeClosure.interpretedCountCaptures outer
          (group.selected offset inside).rhs.certificate.interface.scheme)
        (HMCountSchemeClosure.interpretedTypeCaptures types
          (group.selected offset inside).rhs.certificate.interface.scheme) ∈
      group.closedExports outer types := by
  exact List.mem_of_getElem? (group.closedExports_getElem? outer types offset inside)

/-- Every entry introduced by `closedExports` is a lexical closure; in
    particular the boundary never reintroduces a legacy raw `exported` entry. -/
theorem GeneralizedGroup.mem_closedExports
    {output metadata path captures premises bodyTypes outerEnv}
    (group : GeneralizedGroup output metadata path captures premises bodyTypes outerEnv)
    (outer : Bindings) (types : Nat → BoundsTy) {binding : Binding}
    (member : binding ∈ group.closedExports outer types) :
    ∃ s, binding = .closure s
      (HMCountSchemeClosure.interpretedCountCaptures outer s)
      (HMCountSchemeClosure.interpretedTypeCaptures types s) := by
  rcases List.mem_map.mp member with ⟨s, _, rfl⟩
  exact ⟨s, rfl⟩

theorem GeneralizedGroup.closedExports_closureNormal
    {output metadata path captures premises bodyTypes outerEnv}
    (group : GeneralizedGroup output metadata path captures premises bodyTypes outerEnv)
    (outer : Bindings) (types : Nat → BoundsTy) :
    ClosureNormal (group.closedExports outer types) := by
  intro s member
  obtain ⟨source, impossible⟩ := group.mem_closedExports outer types member
  cases impossible

theorem GeneralizedGroup.closedExports_append_closureNormal
    {output metadata path captures premises bodyTypes outerEnv}
    (group : GeneralizedGroup output metadata path captures premises bodyTypes outerEnv)
    (outer : Bindings) (types : Nat → BoundsTy) (tail : List Binding)
    (normal : ClosureNormal tail) :
    ClosureNormal (group.closedExports outer types ++ tail) := by
  intro s member
  rcases List.mem_append.mp member with groupMember | tailMember
  · exact group.closedExports_closureNormal outer types s groupMember
  · exact normal s tailMember

/-- A closed use's capture agreement is exactly agreement with the vectors
    stored in the selected body binding. -/
theorem GeneralizedGroup.closedExports_captureArguments
    {output metadata path captures premises bodyTypes outerEnv calleeΔ found caller}
    (group : GeneralizedGroup output metadata path captures premises bodyTypes outerEnv)
    (outer : Bindings) (types : Nat → BoundsTy)
    (offset : Nat) (inside : offset < group.exports.length)
    (used : HMCountScheme.Use
      (HMCountSchemeClosure.close
        (group.selected offset inside).rhs.certificate.interface.scheme)
      calleeΔ found caller)
    (captures : HMCountSchemeClosure.CapturesAgree
      (group.selected offset inside).rhs.certificate.interface.scheme outer types used) :
    HMCountSchemeClosure.HasCaptureArguments
      (group.selected offset inside).rhs.certificate.interface.scheme
      (HMCountSchemeClosure.interpretedCountCaptures outer
        (group.selected offset inside).rhs.certificate.interface.scheme)
      (HMCountSchemeClosure.interpretedTypeCaptures types
        (group.selected offset inside).rhs.certificate.interface.scheme)
      used :=
  captures

end FHM.Bounds.RecursiveHMUniform
