import FHM.Bounds.RecursiveHMClosedRuntimeReady

/-! # Canonical closed recursive-program entry point

This downstream wrapper assembles the checked root group, constructs its
closed-export runtime witness, and supplies that witness to the executable
closed-body checker.  The source artifact and resulting report remain exactly
those of the upstream checker.
-/

namespace FHM.Bounds.RecursiveHMClosedExit

open RecursiveHMJudgement CountSubstitution ScopedScheme
open RecursiveHMUniform

/-- Canonical source-linked checker for a root recursive group through the
    lexical-closure semantics.  In contrast to the legacy root wrapper, the
    body environment contains `closedExports` and its optional runtime theorem
    is discharged by the proved use-indexed recursive fixed point. -/
def checkClosedProgram (output : Expr) (metadata : Scope.Metadata)
    (schemes : BinderSchemeMap := []) (expected : Option BoundsTy := none)
    (ctors : CtorEnv := []) :
    Except String (ProgramResult output metadata) := do
  let assembled ← HMDeclaredCoordinates.check output metadata [] (schemes := schemes)
    (ctors := ctors)
  let members ← match assembled.checked.members.runtimeReady with
    | none => throw "bounds: closed recursive group is outside the supported runtime fragment"
    | some ready => pure ready
  let group := GeneralizedGroup.ofChecked assembled.checked
    (fun _ f lc scope fixed => allMembers assembled.checked.members f lc scope fixed)
  let closedReady : group.ClosedRuntimeReady [] BoundsTy.fvar :=
    FHM.Bounds.RecursiveHMClosedExit.GeneralizedGroup.closedRuntimeReadyTop
      group [] (by intro row member; simp at member) []
      (by intro row member; simp at member) BoundsTy.fvar
      (by
        intro i
        simpa [Synth.BoundsTy.toTy] using
          (ContainsBvarsUpTo.fvar : (Ty.fvar i).IsLC))
      (by intro i; trivial)
      (fun offset inside => (members.down offset inside).1)
      (fun offset inside => (members.down offset inside).2)
      (fun _ => Runtime.Supported.fvar)
  let body ← RecursiveHMUniform.checkBodyClosed assembled.checked [] [] [] [] schemes
    closedReady expected ctors
  have sourceEq : output = .found assembled.checked.originalHM
      (.letRec assembled.checked.annotations assembled.checked.rhss assembled.checked.body) := by
    simpa only [Expr.atCorePath, Option.some.injEq] using assembled.checked.source
  pure ⟨assembled, by simpa only [sourceEq] using body⟩

#print axioms checkClosedProgram

end FHM.Bounds.RecursiveHMClosedExit
