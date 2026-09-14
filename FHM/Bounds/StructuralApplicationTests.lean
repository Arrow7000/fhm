import FHM.Bounds.StructuralApplication

namespace FHM.Bounds.StructuralApplicationTests

private def list (n : Nat) (a : BoundsTy) : BoundsTy := .list (.lit n) (.lit n) a
private def a : BoundsTy := .fvar 7
private def b : BoundsTy := .fvar 8
private def char : BoundsTy := .prim .char
private def int : BoundsTy := .prim .int
private def top (a : BoundsTy) : BoundsTy := .list (.lit 0) .inf a

private def run (σ : PolyTy) (schema actual : BoundsTy) (resultHM : Ty)
    (scope : List Nat := []) : Except String (BoundsTy × BoundsTy) := do
  let checked ← BinderBridge.abstract σ schema []
  let s := SchemeTyping.fromBinder checked
  let r ← StructuralApplication.check [] [.mono actual, .poly s] 1 (.var 0) actual
    (.varMono rfl) (.arrow (Synth.BoundsTy.toTy actual) resultHM) resultHM scope
  pure (r.domain, r.bounds)

private def succeeds (r : Except String α) : Bool := match r with | .ok _ => true | _ => false
private def fails (r : Except String α) (needle : String) : Bool :=
  match r with | .error m => (m.splitOn needle).length > 1 | _ => false

private def listScheme : PolyTy := ⟨1, .arrow (listTy (.bvar 0)) (listTy (.bvar 0))⟩
private def listBody : BoundsTy := .arrow (top a) (top a)
private def arrowScheme : PolyTy := ⟨2,
  .arrow (.arrow (.bvar 0) (.bvar 1)) (.arrow (.bvar 0) (.bvar 1))⟩
private def arrowBody : BoundsTy := .arrow (.arrow a b) (.arrow a b)
private def repeatedScheme : PolyTy := ⟨1,
  .arrow (.arrow (.bvar 0) (.bvar 0)) (.bvar 0)⟩
private def repeatedBody : BoundsTy := .arrow (.arrow a a) a
private def n : Count := .var ⟨.rigid, 19⟩

-- Successful results certify the callee's actual specialized domain, not an
-- invented arrow using the narrower argument bounds as its domain.
example {Δ env i arg functionHM resultHM scope}
    (r : StructuralApplication.Result Δ env i arg functionHM resultHM scope) :
    SchemeTyping.Derives Δ env (.app (.var i) arg) r.bounds ∧
    Synth.BoundsTy.toTy (.arrow r.domain r.bounds) = functionHM.eraseBounds :=
  ⟨r.derivation, r.functionShape⟩

private def cases : List (String × Bool) := [
  ("List element slot specialized from actual origin", match
    run listScheme listBody (list 1 char) (listTy (.prim .char)) with
    | .ok (.list (.lit 0) .inf (.prim .char), .list (.lit 0) .inf (.prim .char)) => true
    | _ => false),
  ("nested List slot retains inner exact origin", match
    run listScheme listBody (list 1 (list 2 char)) (listTy (listTy (.prim .char))) with
    | .ok (_, .list (.lit 0) .inf (.list (.lit 2) (.lit 2) (.prim .char))) => true
    | _ => false),
  ("two slots from higher-order argument", match
    run arrowScheme arrowBody (.arrow (list 1 char) int)
      (.arrow (listTy (.prim .char)) (.prim .int)) with
    | .ok (_, result) => result.pretty == "BL 1 1 Char → Int"
    | _ => false),
  ("structural domain interval obligation rejects wrong length", fails
    (run listScheme (.arrow (list 2 a) (top a)) (list 1 char) (listTy (.prim .char)))
    "interval inclusion"),
  ("repeated slot incompatible HM instances rejected", fails
    (run repeatedScheme repeatedBody (.arrow int char) (.prim .int)) "repeated"),
  ("repeated slot bounds checked with arrow variance", fails
    (run repeatedScheme repeatedBody (.arrow (list 1 char) (list 2 char))
      (listTy (.prim .char))) "interval inclusion"),
  ("unused slot Unit witness supported", succeeds
    (run ⟨2, .arrow (.bvar 0) (.arrow (.bvar 1) (.bvar 0))⟩
      (.arrow a (.arrow b a)) char (.arrow (.prim .unit) (.prim .char)))),
  ("unused slot Int is not fabricated from HM payload", fails
    (run ⟨2, .arrow (.bvar 0) (.arrow (.bvar 1) (.bvar 0))⟩
      (.arrow a (.arrow b a)) char (.arrow (.prim .int) (.prim .char))) "disagree"),
  ("slot counts retain caller scope", succeeds
    (run ⟨1, .arrow (.bvar 0) (.bvar 0)⟩ (.arrow a a)
      (.list n n char) (listTy (.prim .char)) [19])),
  ("slot counts outside caller scope rejected", fails
    (run ⟨1, .arrow (.bvar 0) (.bvar 0)⟩ (.arrow a a)
      (.list n n char) (listTy (.prim .char))) "counts"),
  ("enclosing bound slot is not a locally closed argument", fails
    (run ⟨1, .arrow (.bvar 0) (.bvar 0)⟩ (.arrow a a) (.bvar 0) (.bvar 0)) "enclosing")]

def main : IO Unit := do
  for (name, ok) in cases do
    IO.println s!"{if ok then "PASS" else "FAIL"}: {name}"
    unless ok do throw (IO.userError s!"structural bounds application regression: {name}")

#eval main

end FHM.Bounds.StructuralApplicationTests
