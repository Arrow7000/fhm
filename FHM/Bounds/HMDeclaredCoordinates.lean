import FHM.Bounds.HMDeclaredGroup

/-! Deterministic opaque-coordinate proposals for annotated recursive groups.
Only fresh opaque coordinates may be identified, and only by full erased shape
constraints on shared solved identities. No HM inference is rerun. Renaming is
finite/total and carries no acceptance authority: the final proposal goes back
through exact source reconciliation and actual universally signed RHS checking.
Full-type equations requiring more than coordinate renaming reject explicitly. -/

namespace FHM.Bounds.HMDeclaredCoordinates

open HMDeclaredGroup RecursiveHMJudgement

private def freshVectors (annotations : List (Option PolyTy)) (frontier : Nat) : List (List Nat) :=
  match annotations with
  | [] => []
  | a :: rest =>
      let arity := (a.map PolyTy.paramCount).getD 0
      (List.range arity).map (frontier + ·) :: freshVectors rest (frontier + arity)

private def bindingIds : Binding → List Nat
  | .mono β => (Synth.BoundsTy.toTy β).freeVars
  | .recursive c => c.hm.freeVars ++ c.template.hm.body.freeVars ++
      c.fixed.types.flatMap (fun β => (Synth.BoundsTy.toTy β).freeVars)
  | .exported s => s.hm.body.freeVars

mutual
private def alignTypes (opaqueIds : List Nat) (a b : Ty) : Except String (List (Nat × Nat)) := do
  match a, b with
  | .fvar i, .fvar j =>
      if i = j then pure []
      else if opaqueIds.contains i && opaqueIds.contains j then pure [(i, j)]
      else throw "bounds: coordinate alignment cannot change a rigid captured HM identity"
  | .prim p, .prim q =>
      if p = q then pure [] else throw "bounds: shared solved HM identity has incompatible primitive shapes"
  | .bvar i, .bvar j =>
      if i = j then pure [] else throw "bounds: shared solved HM identity has incompatible lexical slots"
  | .arrow a b, .arrow c d =>
      pure ((← alignTypes opaqueIds a c) ++ (← alignTypes opaqueIds b d))
  | .customTy n as, .customTy m bs =>
      if n = m then alignTypeLists opaqueIds as bs
      else throw "bounds: shared solved HM identity has incompatible data shapes"
  | _, _ => throw "bounds: shared HM coordinate alignment requires more than opaque slot renaming"
termination_by sizeOf a + sizeOf b

private def alignTypeLists (opaqueIds : List Nat) (as bs : List Ty) : Except String (List (Nat × Nat)) := do
  match as, bs with
  | [], [] => pure []
  | a :: as, b :: bs => pure ((← alignTypes opaqueIds a b) ++ (← alignTypeLists opaqueIds as bs))
  | _, _ => throw "bounds: shared solved HM identity has incompatible data arities"
termination_by sizeOf as + sizeOf bs
end

private def alignRow (opaqueIds : List Nat) (a : Nat × Ty) (rows : List (Nat × Ty)) :
    Except String (List (Nat × Nat)) := do
  match rows with
  | [] => pure []
  | b :: rest =>
      let head ← if a.1 = b.1 then alignTypes opaqueIds a.2 b.2 else pure []
      pure (head ++ (← alignRow opaqueIds a rest))

private def alignRows (opaqueIds : List Nat) (rows : List (Nat × Ty)) : Except String (List (Nat × Nat)) := do
  match rows with
  | [] => pure []
  | a :: rest => pure ((← alignRow opaqueIds a rest) ++ (← alignRows opaqueIds rest))

private def lookup (coordinates : List (Nat × Nat)) (i : Nat) : Nat :=
  ((coordinates.find? (fun row => row.1 == i)).map Prod.snd).getD i

/-- Eager finite equivalence classes avoid recursive representative lookup,
    fuel, cycles and partial functions. The least fresh identity is canonical. -/
private def coordinateClasses (opaqueIds : List Nat) (edges : List (Nat × Nat)) : List (Nat × Nat) :=
  edges.foldl (fun current edge =>
    let a := lookup current edge.1
    let b := lookup current edge.2
    current.map fun row => (row.1, if row.2 == a || row.2 == b then min a b else row.2))
    (opaqueIds.map fun i => (i, i))

/-- Return proposals only. Final group checking independently rejects duplicate
    slots, changed captures, conflicting shapes and actual invalid contracts. -/
def propose (output : Expr) (metadata : Scope.Metadata) (path : CorePath)
    (captures : List Nat := []) (premises : List Constraint := []) (outerTypes : List Ty := [])
    (outerEnv : List Binding := []) (schemes : BinderSchemeMap := []) : Except String (List (List Nat)) := do
  unless metadata.problems.isEmpty do throw "bounds: unresolved count scope in recursive coordinate proposal"
  match output.atCorePath path with
  | some (.found _ (.letRec annotations rhss _)) =>
      unless annotations.length = rhss.length do throw "bounds: coordinate proposal annotation/RHS arity mismatch"
      let used := output.tyFreeVars ++ outerTypes.flatMap Ty.freeVars ++ outerEnv.flatMap bindingIds ++
        schemes.flatMap (fun fact => fact.2.body.freeVars)
      let frontier := used.foldl max 0 + 1
      let vectors := freshVectors annotations frontier
      let opaqueIds := vectors.flatten
      let guarded := annotations.filterMap (fun a => a.map (fun s => s.body.eraseBounds)) ++ outerTypes
      let ps ← prepareInterfaces output metadata path captures premises guarded 0 vectors
      let edges ← alignRows opaqueIds ps.proposals
      let classes := coordinateClasses opaqueIds edges
      pure (vectors.map fun vector => vector.map (lookup classes))
  | _ => throw "bounds: coordinate proposal requires an original found recursive group"

structure Result (output : Expr) (metadata : Scope.Metadata) (path : CorePath)
    (captures : List Nat) (premises : List Constraint) (outerTypes : List Ty) (outerEnv : List Binding) where
  vectors : List (List Nat)
  checked : HMDeclaredGroup.Checked output metadata path vectors captures premises outerTypes outerEnv

/-- Automatic proposals followed by group assembly with a caller-supplied exact
    RHS checker. Coordinate inference has no authority over the callback's
    typing proof; the result still passes through `HMDeclaredGroup.checkWith`. -/
def checkWith (output : Expr) (metadata : Scope.Metadata) (path : CorePath)
    (captures : List Nat := []) (premises : List Constraint := []) (outerTypes : List Ty := [])
    (outerEnv : List Binding := []) (schemes : BinderSchemeMap := [])
    (checkRHS : ∀ {memberIndex : Nat} {typeCaptures : List Ty},
      (p : HMDeclaredGroup.Member output metadata path memberIndex captures premises typeCaptures) →
      (env : List Binding) → Except String (HMDeclaredRHS.Checked p.reconciled env)) :
    Except String (Result output metadata path captures premises outerTypes outerEnv) := do
  let vectors ← propose output metadata path captures premises outerTypes outerEnv schemes
  let checked ← HMDeclaredGroup.checkWith output metadata path vectors captures premises
    outerTypes outerEnv checkRHS
  pure ⟨vectors, checked⟩

/-- Automatic proposals are accepted ONLY through the same proof-carrying
    original-member checker as explicitly supplied vectors. No legacy fallback. -/
def check (output : Expr) (metadata : Scope.Metadata) (path : CorePath)
    (captures : List Nat := []) (premises : List Constraint := []) (outerTypes : List Ty := [])
    (outerEnv : List Binding := []) (schemes : BinderSchemeMap := []) (ctors : CtorEnv := []) :
    Except String (Result output metadata path captures premises outerTypes outerEnv) :=
  checkWith output metadata path captures premises outerTypes outerEnv schemes
    (fun p env => HMDeclaredRHS.check p.reconciled env schemes ctors)

#print axioms propose
#print axioms checkWith
#print axioms check

end FHM.Bounds.HMDeclaredCoordinates
