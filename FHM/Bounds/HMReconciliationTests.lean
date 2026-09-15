import FHM.Bounds.HMReconciliation
import FHM.Bounds.RecursiveHMReconciled

namespace FHM.Bounds.HMReconciliationTests

open HMReconciliation

private def n : Count := .var ⟨.rigid, 7⟩
private def sourceList (a : Ty := .bvar 0) : Ty := .bl (.solid n) (.solid n) a
private def signature : PolyTy := ⟨1, .arrow sourceList sourceList⟩
private def discovered : Ty := .arrow (.fvar 90) (.fvar 90)
private def inferred : PolyTy := ⟨1, .arrow (.bvar 0) (.bvar 0)⟩
private def identity : Expr := .found discovered
  (.lambda none (.found (.fvar 90) (.var 0)))
private def output : Expr := .found (.prim .int)
  (.letIn none identity (.found (.prim .int) (.primLit (.int 0))))
private def original : BoundsTy := .arrow (.fvar 90) (.fvar 90)
private def facts : BinderSchemeMap := [(.letIn [], inferred)]
private def originalNode : HMFoundView.AtNode output [.letRhs] :=
  ⟨discovered, .lambda none (.found (.fvar 90) (.var 0)),
    by simp [output, identity, Expr.atCorePath]⟩

private def run (annotation : PolyTy := signature) (ids : List Nat := [91])
    (schemes : BinderSchemeMap := facts) (captures : List Ty := [])
    (skeleton : BoundsTy := original) (site : CoreBinderSite := .letIn []) : Except String Unit := do
  let node ← HMFoundView.locate output [.letRhs]
  let s ← HMCountScheme.decode annotation [7] []
  let _ ← check node schemes site s skeleton ids captures
  pure ()

private def exactViews : Except String Bool := do
  let root ← HMFoundView.locate output [.letRhs]
  let child ← HMFoundView.locate output [.letRhs, .lambdaBody]
  let s ← HMCountScheme.decode signature [7] []
  let c ← check root facts (.letIn []) s original [91] []
  let _ := c.machineInstance
  pure (match c.interpretation 90, child.view c.interpretation with
    | .list lo hi (.fvar i), .customTy name [.fvar j] =>
        lo == n && hi == n && i == 91 && j == 91 && name == FHM.Bounds.listTyName
    | _, _ => false)

private def unusedSlot : Except String Bool := do
  let hm : Ty := .arrow (.prim .int) (.prim .int)
  let rhs : Expr := .found hm (.lambda none (.found (.prim .int) (.var 0)))
  let out : Expr := .found (.prim .int) (.letIn none rhs (.found (.prim .int) (.primLit (.int 0))))
  let node ← HMFoundView.locate out [.letRhs]
  let s ← HMCountScheme.decode ⟨1, hm⟩ [] []
  let c ← check node [(.letIn [], ⟨0, hm⟩)] (.letIn []) s
    (.arrow (.prim .int) (.prim .int)) [91] []
  pure (c.signatureIds == [91] && c.opening.ids == [91] && c.arguments.isEmpty)

private def unsoundForall : Except String Unit := do
  let rhs : Expr := .found (.prim .int) (.primLit (.int 1))
  let out : Expr := .found (.prim .int) (.letIn none rhs (.found (.prim .int) (.primLit (.int 0))))
  let node ← HMFoundView.locate out [.letRhs]
  let s ← HMCountScheme.decode ⟨1, .bvar 0⟩ [] []
  let _ ← check node [(.letIn [], ⟨0, .prim .int⟩)] (.letIn []) s (.prim .int) [91] []
  pure ()

private def typedIdentity (annotation : PolyTy := signature) : Except String Bool := do
  let s ← HMCountScheme.decode annotation [7] []
  let c ← check originalNode facts (.letIn []) s original [91] []
  have typing : RecursiveHMJudgement.Derives BoundsTy.fvar
      (s.counts.quantified ++ s.counts.captures) [] s.counts.premises []
      originalNode.inner.stripFound original := by
    simp only [originalNode, original, Expr.stripFound]
    exact .lambda True.intro (.varMono rfl)
  let result ← checkRHS c original typing (by intro d hd; cases hd)
    (by intro d hd; cases hd)
  pure (match result.typed.actual with
    | .arrow (.list lo hi (.fvar i)) (.list lo' hi' (.fvar j)) =>
        lo == n && hi == n && lo' == n && hi' == n && i == 91 && j == 91
    | _ => false)

private def mismatchingDerivation : Except String Unit := do
  let s ← HMCountScheme.decode signature [7] []
  let c ← check originalNode facts (.letIn []) s original [91] []
  let actual : BoundsTy := .arrow (.prim .int) (.prim .int)
  have typing : RecursiveHMJudgement.Derives BoundsTy.fvar
      (s.counts.quantified ++ s.counts.captures) [] s.counts.premises []
      originalNode.inner.stripFound actual := by
    simp only [originalNode, actual, Expr.stripFound]
    exact .lambda True.intro (.varMono rfl)
  let _ ← checkRHS c actual typing (by intro d hd; cases hd)
    (by intro d hd; cases hd)
  pure ()

/-- End-to-end symbolic certificate construction and external specialization:
    original gamma maps first to List n alpha, then n to 3, and finally alpha
    to caller List n Int. The caller's n must stay untouched in the final type. -/
private def universalSpecialization (annotation : PolyTy := signature)
    (scopedAnnotation : Bool := false) : Except String Bool := do
  let body := Expr.lambda (if scopedAnnotation then some (.fvar 90) else none)
    (.found (.fvar 90) (.var 0))
  let node : HMFoundView.AtNode
      (.found (.prim .int) (.letIn none (.found discovered body)
        (.found (.prim .int) (.primLit (.int 0))))) [.letRhs] :=
    ⟨discovered, body, by simp [Expr.atCorePath]⟩
  let interface ← HMCountScheme.decodeAnnotated annotation [7] []
  let c ← check node facts (.letIn []) interface.scheme original [91] []
  let located ← RecursiveHMReconciled.checkLocated c []
  let cert := RecursiveHMReconciled.fromAnnotated interface c located.rhs
    (by intro d hd; cases hd) (by intro s hs; cases hs)
    (by intro d hd; cases hd) (by intro s hs; cases hs)
  let inst ← interface.scheme.counts.instantiate [.lit 3] [7]
  let arg : BoundsTy := .list n n (.prim .int)
  if ha : [arg].length = annotation.paramCount then
    let used := RecursiveHMSigned.atInterpretedNode node cert inst [arg] ha
      (by
        intro a hin
        have he : a = arg := by simpa using hin
        subst a
        apply (Ty.bvarsBelow_iff _).mp
        simp [arg, Synth.BoundsTy.toTy, listTy, Ty.bvarsBelow, TyList.bvarsBelow])
      (by decide)
    pure (match used.typed.actual with
      | .arrow (.list lo hi (.list callerLo callerHi (.prim .int)))
          (.list resultLo resultHi (.list nestedLo nestedHi (.prim .int))) =>
        lo == .lit 3 && hi == .lit 3 && resultLo == .lit 3 && resultHi == .lit 3 &&
          callerLo == n && callerHi == n && nestedLo == n && nestedHi == n
      | _ => false)
  else throw "test: expected one source HM slot"

private def succeeds (r : Except String α) : Bool := match r with | .ok _ => true | _ => false
private def passes (r : Except String Bool) : Bool := match r with | .ok b => b | _ => false
private def fails (r : Except String α) (needle : String) : Bool :=
  match r with | .error m => (m.splitOn needle).length > 1 | _ => false

private def cases : List (String × Bool) := [
  ("more-general machine identity reconciles with a forall/List source signature", succeeds run),
  ("full source count payloads interpret original root and inner found nodes", passes exactViews),
  ("unused source forall keeps its explicit fresh identity without a Unit opening", passes unusedSlot),
  ("source forall cannot assert an arbitrary type for an Int RHS", !succeeds unsoundForall),
  ("missing machine binder evidence rejects reconciliation", fails (run signature [91] []) "missing inferred"),
  ("duplicate machine binder evidence rejects reconciliation", fails (run signature [91] (facts ++ facts)) "duplicate inferred"),
  ("machine fact cannot be taken from a different RHS Core site", fails
    (run signature [91] facts [] original (.letRec [] 0)) "exact RHS Core path"),
  ("source HM identities cannot alias the original machine identities", fails (run signature [90]) "fresh from machine"),
  ("source HM identities cannot escape through captured type interfaces", fails
    (run signature [91] facts [listTy (.fvar 91)]) "captured type interface"),
  ("machine generalized identities cannot already escape into captures", fails
    (run signature [91] facts [listTy (.fvar 90)]) "escapes into captured"),
  ("reconciliation cannot use a skeleton for another discovered type", fails
    (run signature [91] facts [] (.arrow (.prim .int) (.prim .int))) "original found node"),
  ("a repeated machine slot cannot satisfy incompatible source forall slots", fails
    (run ⟨2, .arrow (sourceList (.bvar 0)) (sourceList (.bvar 1))⟩ [91, 92]) "disagrees"),
  ("fresh source forall slots must be distinct", fails
    (run ⟨2, .arrow (sourceList (.bvar 0)) (sourceList (.bvar 1))⟩ [91, 91]) "alias"),
  ("source opening retains exact declared HM arity", fails (run signature []) "wrong HM arity"),
  ("interpretation cannot make the identity return a different primitive element", fails
    (run ⟨1, .arrow sourceList (sourceList (.prim .char))⟩) "disagrees"),
  ("more-general RHS is accepted only with real original-node typing and inclusion", passes typedIdentity),
  ("loose result signature preserves the actual exact interval instead of overwriting it", passes
    (typedIdentity ⟨1, .arrow sourceList (.bl (.solid (.lit 0)) (.solid .inf) (.bvar 0))⟩)),
  ("HM-compatible signature cannot assert an unjustifiably tight result interval", fails
    (typedIdentity ⟨1, .arrow sourceList (.bl (.solid (.lit 0)) (.solid (.lit 0)) (.bvar 0))⟩)
    "interval inclusion"),
  ("a real derivation still rejects when its interpreted actual disagrees with the node", fails
    mismatchingDerivation "interpreted found payload"),
  ("a reconciled actual RHS yields universal written-signature and exact original-node instances", passes
    universalSpecialization),
  ("counts inside source replacements specialize before nested caller counts are inserted", passes
    (universalSpecialization ⟨1, .arrow sourceList (.bl (.solid (.lit 0)) (.solid .inf) (.bvar 0))⟩)),
  ("carried lambda type annotations use the same reconciled universal source interpretation", passes
    (universalSpecialization signature true))]

def main : IO Unit := do
  for (name, ok) in cases do
    IO.println s!"{if ok then "PASS" else "FAIL"}: {name}"
    unless ok do throw (IO.userError s!"HM reconciliation regression failed: {name}")

#eval main

end FHM.Bounds.HMReconciliationTests
