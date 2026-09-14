import FHM.Bounds.RecursiveContract

namespace FHM.Bounds.HMCountSchemeTests

open HMCountScheme

private def n : Count := .var ⟨.rigid, 7⟩
private def exact (c : Count) (elem : BoundsTy := .prim .int) : BoundsTy := .list c c elem
private def annList (elem : Ty := .bvar 0) : Ty := .bl (.solid n) (.solid n) elem
private def identity : PolyTy := ⟨1, .arrow annList annList⟩
private def identityHM (elem : Ty := .fvar 90) : Ty := .arrow (listTy elem) (listTy elem)
private def template (ann : PolyTy := identity) (premises : List Constraint := []) : Except String Scheme :=
  decode ann [7] [] premises
private def succeeds (r : Except String α) : Bool := match r with | .ok _ => true | _ => false
private def fails (r : Except String α) (needle : String) : Bool :=
  match r with | .error m => (m.splitOn needle).length > 1 | _ => false

private def opens (ids : List Nat := [90]) (captures : List Ty := [])
    (found : Ty := identityHM) : Except String BoundsTy := do
  let s ← template
  let o ← openFixed s found ids captures
  pure o.bounds

private def use (counts : List Count := [.lit 2]) (types : List BoundsTy := [.prim .int])
    (caller : List Nat := []) (found : Ty := identityHM (.prim .int))
    (premises : List Constraint := []) : Except String BoundsTy := do
  let s ← template identity premises
  let u ← check s [] found counts types caller
  pure u.bounds

private def opaqueUse (found : Ty := identityHM) : Except String BoundsTy := do
  let o ← RecursiveContract.decodeOpaque identity identityHM [90] [7] [] []
  let u ← RecursiveContract.check o.declared [] found [.lit 2] []
  pure u.bounds

private def vacuous (external : Bool) : Except String BoundsTy := do
  let s ← decode ⟨1, .arrow (.prim .int) (.prim .int)⟩ [] []
  if external then
    let u ← check s [] (.arrow (.prim .int) (.prim .int)) [] [.fvar 123] []
    pure u.bounds
  else
    let o ← openFixed s (.arrow (.prim .int) (.prim .int)) [123] []
    pure o.bounds

private def nestedCollision : Bool :=
  let callerCount := Count.var ⟨.rigid, 7⟩
  let arg := exact callerCount
  let found := identityHM (listTy (.prim .int))
  match use [.lit 3] [arg] [7] found with
  | .ok (.arrow (.list lo hi (.list a b (.prim .int)))
      (.list lo' hi' (.list a' b' (.prim .int)))) =>
      lo == .lit 3 && hi == .lit 3 && lo' == .lit 3 && hi' == .lit 3 &&
      a == callerCount && b == callerCount && a' == callerCount && b' == callerCount
  | _ => false

private def cases : List (String × Bool) := [
  ("closed forall/count identity decodes without inventing an RHS", succeeds template),
  ("opaque opening agrees with the actual free HM identity", succeeds opens),
  ("opaque opening has exact HM arity", fails (opens []) "wrong HM arity"),
  ("opaque opening cannot specialize its universal slot to Int", fails
    (opens [90] [] (identityHM (.prim .int))) "needs specialization"),
  ("opaque opening cannot rename the actual fixed HM identity", fails
    (opens [91]) "disagrees"),
  ("opaque identity cannot escape through a nested captured type", fails
    (opens [90] [listTy (.fvar 90)]) "captured type interface"),
  ("unrelated captured HM identities remain allowed", succeeds
    (opens [90] [listTy (.fvar 91)])),
  ("type and count numeric identities occupy separate namespaces", succeeds
    (opens [7] [] (identityHM (.fvar 7)))),
  ("independent forall slots cannot alias", fails (do
    let s ← template ⟨2, .arrow (annList (.bvar 0)) (annList (.bvar 1))⟩
    let _ ← openFixed s identityHM [90, 90] []
    pure ()) "alias"),
  ("independent forall slots can use distinct fixed identities", succeeds (do
    let s ← template ⟨2, .arrow (annList (.bvar 0)) (annList (.bvar 1))⟩
    let _ ← openFixed s (.arrow (listTy (.fvar 90)) (listTy (.fvar 91))) [90, 91] []
    pure ())),
  ("declared free captures cannot alias even an otherwise unused slot", fails (do
    let s ← decode ⟨1, .arrow (.fvar 90) (.fvar 90)⟩ [] []
    let _ ← openFixed s (.arrow (.fvar 90) (.fvar 90)) [90] []
    pure ()) "captured type interface"),
  ("vacuous forall can open at an explicit fresh opaque identity", succeeds (vacuous false)),
  ("vacuous forall accepts a non-Unit external type witness", succeeds (vacuous true)),
  ("an out-of-scope HM slot is not defaulted", fails
    (template ⟨1, .arrow (annList (.bvar 1)) annList⟩) "out-of-scope HM slot"),
  ("count scope is independently checked in the closed template", fails
    (decode identity [] []) "lexical scope"),
  ("external specialization accepts actual Int bounds", succeeds use),
  ("external specialization can choose Char independently", succeeds
    (use [.lit 2] [.prim .char] [] (identityHM (.prim .char)))),
  ("external specialization checks every repeated HM slot", fails
    (use [.lit 2] [.prim .int] [] (.arrow (listTy (.prim .int)) (listTy (.prim .char)))) "found monotype"),
  ("external specialization has exact HM arity", fails (use [.lit 2] []) "wrong HM arity"),
  ("external specialization rejects caller bound slots", fails
    (use [.lit 2] [.bvar 0]) "enclosing bound slot"),
  ("caller type argument counts cannot escape even through a used slot", fails
    (use [.lit 2] [exact n] [] (identityHM (listTy (.prim .int)))) "outside caller scope"),
  ("caller counts inside HM arguments are inserted after telescope substitution", nestedCollision),
  ("external count witnesses must remain finite Nat values", fails
    (use [.inf]) "finite"),
  ("external count witnesses discharge declared premises", fails
    (use [.lit 2] [.prim .int] [] (identityHM (.prim .int)) [⟨n, .lit 0⟩]) "premises"),
  ("opaque recursive assumption accepts count-only specialization", succeeds opaqueUse),
  ("opaque recursive assumption does not reopen HM quantifiers at calls", fails
    (opaqueUse (identityHM (.prim .int))) "fixed HM monotype")]

example {s Δ found caller} (u : Use s Δ found caller) :
    ScopedScheme.BoundsScoped caller u.bounds := u.inScope

example {s Δ found caller} (u : Use s Δ found caller) :
    s.hm.InstantiatesTo (u.types.map Synth.BoundsTy.toTy) found.eraseBounds := u.hm_instance

example {s found captures} (o : Opening s found captures) : o.counts.WF := o.wf

def main : IO Unit := do
  let mut failures := 0
  for (name, ok) in cases do
    IO.println s!"{if ok then "PASS" else "FAIL"}: {name}"
    unless ok do failures := failures + 1
  unless failures = 0 do throw (IO.userError s!"{failures} HM/count contract regressions failed")

#eval main

end FHM.Bounds.HMCountSchemeTests
