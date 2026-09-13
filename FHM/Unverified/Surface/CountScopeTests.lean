import FHM.Bounds.Found

/-! Construction-time count scope regressions. Not part of the HM proof roots. -/

namespace SurfaceBridge.CountScopeTests

open Surface.Span SurfaceBridge.Provenance FHM.Bounds.Scope

private def s : Span := ⟨1, 1, 1, 80⟩
private def leaf : SpannedExpr := .leaf s
private def xs : ValName := ⟨"xs"⟩
private def n : ValName := ⟨"n"⟩
private def m : ValName := ⟨"m"⟩
private def unknown : ValName := ⟨"unknown"⟩
private def ctors : CtorEnv := (elabDecls preludeDecls).getD []

private def interval (lo hi : ValName) : Surface.Ty :=
  .bl (.solid (.var lo)) (.solid (.var hi)) (.prim .int)

private def binding (name : ValName) (names : List ValName) (lo hi : ValName) : Surface.Binding :=
  { name, natBinders := names
    ann := some ⟨[], .arrow (interval lo hi) (interval lo hi)⟩
    rhs := .lambda (.name xs) (some (interval lo hi)) (.var xs) }

private def bindingSpan : SpannedExpr := .lambda s leaf

private def lower (bindings : List Surface.Binding) : Option Lowered :=
  lowerWithProvenance ctors (.letRecIn bindings (.primLit (.int 1)))
    (.letRecIn s (bindings.map fun _ => bindingSpan) leaf)

private def countPair? : Ty → Option (Nat × Nat)
  | .bl (.solid (.var ⟨.rigid, lo⟩)) (.solid (.var ⟨.rigid, hi⟩)) _ => some (lo, hi)
  | _ => none

private def memberParam? (e : Expr) (member : Nat) : Option (Nat × Nat) := do
  let rhs ← e.atCorePath [.letRecRhs member]
  match rhs with
  | .lambda (some ann) _ => countPair? ann
  | _ => none

private def twoMembers : Bool :=
  match lower [binding ⟨"f"⟩ [n, m] n m, binding ⟨"g"⟩ [n, m] n m] with
  | none => false
  | some r =>
      let fids := (BinderId.mk 0 0 0).index
      let fm := (BinderId.mk 0 0 1).index
      let gids := (BinderId.mk 0 1 0).index
      let gm := (BinderId.mk 0 1 1).index
      r.provenanceTotal && r.counts.problems.isEmpty && r.counts.telescopes.length == 2 &&
      memberParam? r.expr 0 == some (fids, fm) &&
      memberParam? r.expr 1 == some (gids, gm) && fids != gids && fm != gm &&
      (inferWithProvenance ctors r).isSome

private def shadowAndCapture : Bool := Id.run do
  let inner := binding ⟨"inner"⟩ [n] n m
  let outer := { binding ⟨"outer"⟩ [n, m] n m with
    rhs := Surface.Expr.lambda (.name xs) (some (interval n m))
      (.letRecIn [inner] (.var xs)) }
  let spans : SpannedExpr := .letRecIn s
    [.lambda s (.letRecIn s [bindingSpan] leaf)] leaf
  match lowerWithProvenance ctors (.letRecIn [outer] (.primLit (.int 1))) spans with
  | none => return false
  | some r =>
      let outerN := (BinderId.mk 0 0 0).index
      let outerM := (BinderId.mk 0 0 1).index
      let innerN := (BinderId.mk 2 0 0).index
      let innerPath : CorePath := [.letRecRhs 0, .lambdaBody, .letRecRhs 0]
      let innerPair := do
        let rhs ← r.expr.atCorePath innerPath
        match rhs with
        | .lambda (some ann) _ => countPair? ann
        | _ => none
      return r.provenanceTotal && r.counts.problems.isEmpty && outerN != innerN &&
        innerPair == some (innerN, outerM) &&
        r.counts.telescopes.any (fun t => t.site == .letRec [.letRecRhs 0, .lambdaBody] 0) &&
        (inferWithProvenance ctors r).isSome

private def unknownKeepsHM : Bool :=
  match lower [binding ⟨"f"⟩ [n] n unknown] with
  | none => false
  | some r =>
      r.counts.problems.any (fun p => unknown ∈ p.unresolved) &&
      match inferWithProvenance ctors r with
      | none => false
      | some typed =>
          match FHM.Bounds.Found.synthNodes typed with
          | .error msg => msg == "bounds: unresolved or duplicate count binder scope"
          | _ => false

private def duplicateKeepsHM : Bool :=
  match lower [binding ⟨"f"⟩ [n, n] n n] with
  | none => false
  | some r =>
      r.counts.problems.any (fun p => n ∈ p.duplicateBinders) &&
      (inferWithProvenance ctors r).isSome

private def rebasingKeepsIds : Bool :=
  match lower [binding ⟨"f"⟩ [n, m] n m] with
  | none => false
  | some r =>
      let moved := r.belowPath [.appArg]
      (moved.counts.telescopes.map (·.binders)) == (r.counts.telescopes.map (·.binders)) &&
      moved.counts.telescopes.all (fun t => t.site == .letRec [.appArg] 0)

private def cloningKeepsSites : Bool :=
  match lower [binding ⟨"f"⟩ [n, m] n m] with
  | none => false
  | some r =>
      let cloned := Lowered.metadata (.app r.expr r.expr)
        [r.belowPath [.appFun], r.belowPath [.appArg]]
      cloned.counts.telescopes.length == 2 &&
      cloned.counts.telescopes.all (fun t => t.binders == telescope 0 0 [n, m]) &&
      cloned.counts.telescopes.any (fun t => t.site == .letRec [.appFun] 0) &&
      cloned.counts.telescopes.any (fun t => t.site == .letRec [.appArg] 0)

def main : IO Unit := do
  for (name, ok) in [
      ("same-named member telescopes have distinct identities", twoMembers),
      ("nested shadowing preserves captured outer counts", shadowAndCapture),
      ("unknown counts remain HM-blind but fail BL", unknownKeepsHM),
      ("duplicate count binders remain HM-blind but recorded invalid", duplicateKeepsHM),
      ("rebasing changes sites, not count identities", rebasingKeepsIds),
      ("cloning retains both Core sites without changing identities", cloningKeepsSites)] do
    IO.println s!"{if ok then "PASS" else "FAIL"}: {name}"
    unless ok do throw (IO.userError s!"count scope regression: {name}")

#eval main

end SurfaceBridge.CountScopeTests
