import FHM.Bounds.CountApplication
import FHM.Bounds.ScopedDeclaration
import FHM.Bounds.Found

namespace FHM.Bounds.CountApplicationTests

open SchemeTyping SurfaceBridge.Provenance

private def ctors : CtorEnv := (elabDecls preludeDecls).getD []
private def span : Surface.Span.Span := ⟨1, 1, 1, 80⟩
private def leaf : Surface.Span.SpannedExpr := .leaf span
private def n : ValName := ⟨"n"⟩
private def xs : ValName := ⟨"xs"⟩
private def exact (c : Surface.Count) : Surface.Ty := .bl (.solid c) (.solid c) (.prim .int)
private def identity : Surface.Binding :=
  { name := ⟨"f"⟩, natBinders := [n]
    ann := some ⟨[], .arrow (exact (.var n)) (exact (.var n))⟩
    rhs := .lambda (.name xs) (some (exact (.var n))) (.var xs) }
private def increment : Surface.Binding :=
  { identity with
    ann := some ⟨[], .arrow (exact (.var n)) (exact (.add (.var n) (.lit 1)))⟩
    rhs := .lambda (.name xs) (some (exact (.var n)))
      (.app (.app (.ctor consCtorName) (.primLit (.int 1))) (.var xs)) }
private def singleton : Surface.Binding :=
  { identity with
    ann := none
    rhs := .lambda (.name xs) none (.list [.var xs]) }
private def emptyResult : Surface.Binding :=
  { identity with
    ann := none
    rhs := .lambda (.name xs) (some (exact (.var n))) (.list []) }
private def scalar : Surface.Binding :=
  { identity with
    ann := none
    rhs := .primLit (.int 1) }

private def artifact (b : Surface.Binding) : Option TypedLowered := do
  let bodySpan := match b.rhs with
    | .lambda _ _ (.list es) => Surface.Span.SpannedExpr.list span (es.map fun _ => leaf)
    | .lambda _ _ (.app _ _) => .app span (.app span leaf leaf) leaf
    | _ => leaf
  let rhsSpan := match b.rhs with
    | .lambda _ _ _ => Surface.Span.SpannedExpr.lambda span bodySpan
    | _ => leaf
  let lowered ← lowerWithProvenance ctors (.letRecIn [b] (.primLit (.int 1)))
    (.letRecIn span [rhsSpan] leaf)
  inferWithProvenance ctors lowered

private def zero (elem : BoundsTy) : BoundsTy := .list (.lit 0) (.lit 0) elem
private def nil : Expr := .ctor nilCtorName
private def one : Expr := .app (.app (.ctor consCtorName) (.primLit (.int 1))) nil
private def oneBounds : BoundsTy := .list (.add (.lit 0) (.lit 1)) (.add (.lit 0) (.lit 1)) (.prim .int)
private def oneTyping (Δ : List Constraint) : Derives Δ [] one oneBounds :=
  .cons .literal .nil (SemanticSub.refl Δ (.prim .int))
private def function : Expr := .lambda none (.var 0)
private def functionBounds : BoundsTy := .arrow oneBounds oneBounds
private def functionTyping : Derives [] [] function functionBounds := .lambda True.intro (.varMono rfl)
private def arrowHM : Ty := .arrow (listTy (.prim .int)) (listTy (.prim .int))
private def top : BoundsTy := .list (.lit 0) .inf (.prim .int)
private def cm : Count := .var ⟨.rigid, 99⟩

-- Every contract here comes from a genuinely inferred, lowered declaration
-- RHS. Inspecting that member does not accept the recursive group itself.
private def run (b : Surface.Binding) (arg : Expr) (actual : BoundsTy)
    (typing : Derives Δ [] arg actual) (resultHM : Ty) (counts : List Count)
    (caller : List Nat := []) (guarded : Bool := false)
    (functionHM : Option Ty := none) (explicit : Option (List BoundsTy) := none) :
    Except String (BoundsTy × BoundsTy) := do
  let a ← match artifact b with
    | none => throw "test: HM artifact construction failed"
    | some a => pure a
  let q ← ScopedDeclaration.telescope a.lowering.counts (.letRec [] 0)
  let premises := if guarded then q.map (fun id => (⟨.var ⟨.rigid, id⟩, .lit 0⟩ : Constraint)) else []
  let c ← ScopedDeclaration.checkRHS a.inference.output a.inference.binderSchemes
    a.lowering.counts (.letRec [] 0) [] [] premises
  let hm := functionHM.getD (.arrow (Synth.BoundsTy.toTy actual) resultHM)
  let r ← match explicit with
    | none => CountApplication.fromOrigin c.certificate Δ arg actual typing hm resultHM counts caller
    | some args => CountApplication.check c.certificate Δ arg actual typing hm resultHM counts args caller
  pure (r.domain, r.bounds)

private def succeeds (r : Except String α) : Bool := match r with | .ok _ => true | _ => false
private def fails (r : Except String α) (needle : String) : Bool :=
  match r with | .error m => (m.splitOn needle).length > 1 | _ => false
private def intList : Ty := listTy (.prim .int)
private def identityNil (counts : List Count) :=
  run identity nil (zero (.prim .int)) (Δ := []) .nil intList counts
private def identityOne (counts : List Count) :=
  run identity one oneBounds (oneTyping []) intList counts

private def callerCollision : Bool :=
  match artifact singleton with
  | none => false
  | some a => match ScopedDeclaration.checkRHS a.inference.output a.inference.binderSchemes
      a.lowering.counts (.letRec [] 0) with
    | .error _ => false
    | .ok c => match c.quantified with
      | [id] =>
          let k : Count := .var ⟨.rigid, id⟩
          let actual := zero (.list k k (.prim .int))
          let resultHM := listTy (Synth.BoundsTy.toTy actual)
          match CountApplication.fromOrigin c.certificate [] nil actual .nil
              (.arrow (Synth.BoundsTy.toTy actual) resultHM) resultHM [.lit 3] [id] with
          | .ok r => match r.bounds with
            | .list _ _ (.list _ _ (.list lo hi (.prim .int))) => lo == k && hi == k
            | _ => false
          | .error _ => false
      | _ => false

example {Δ env rhs arg actual functionHM resultHM caller}
    (r : CountApplication.Result Δ env rhs arg actual functionHM resultHM caller) :
    Derives Δ env (.app rhs arg) r.bounds ∧ SemanticSub Δ actual r.domain ∧
      Synth.BoundsTy.toTy r.bounds = resultHM.eraseBounds ∧
      ScopedScheme.BoundsScoped caller r.bounds :=
  ⟨r.derivation, r.inclusion, r.shape, r.countScope⟩

private def cases : List (String × Bool) := [
  ("certified identity accepts actual Nil at count zero", succeeds (identityNil [.lit 0])),
  ("HM-compatible identity rejects Nil at count one", fails (identityNil [.lit 1]) "interval inclusion"),
  ("certified identity accepts actual Cons at count one", succeeds (identityOne [.lit 1])),
  ("HM-compatible identity rejects Cons at count zero", fails (identityOne [.lit 0]) "interval inclusion"),
  ("certified Cons implementation increments actual count", match
    run increment one oneBounds (oneTyping []) intList [.lit 1] with
    | .ok (_, .list lo hi (.prim .int)) => lo.eval (fun _ => 0) == .ofNat 2 && hi.eval (fun _ => 0) == .ofNat 2
    | _ => false),
  ("generic contract slots come from primitive argument origin", match
    run singleton (.primLit (.char 'x')) (.prim .char) (Δ := []) .literal
      (listTy (.prim .char)) [.lit 7] with
    | .ok (_, .list lo hi (.prim .char)) => lo.eval (fun _ => 0) == .ofNat 1 && hi.eval (fun _ => 0) == .ofNat 1
    | _ => false),
  ("generic contract preserves full nested List origin", match
    run singleton nil (zero (zero (.prim .char))) (Δ := []) .nil
      (listTy (listTy (listTy (.prim .char)))) [.lit 7] with
    | .ok (_, .list _ _ (.list (.lit 0) (.lit 0) (.list (.lit 0) (.lit 0) (.prim .char)))) => true
    | _ => false),
  ("combined contract application preserves colliding caller count", callerCollision),
  ("argument scope checked even outside HM-slot proposals", fails
    (run singleton nil (zero (.list cm cm (.prim .int))) (Δ := []) .nil
      (listTy (listTy intList)) [.lit 3]) "argument counts"),
  ("missing explicit count argument rejected", fails (identityNil []) "arity"),
  ("infinite explicit Nat argument rejected", fails (identityNil [.inf]) "finite"),
  ("unscoped explicit count argument rejected", fails (identityNil [cm]) "outside caller scope"),
  ("false declaration premise is not asserted for an application", fails
    (run identity one oneBounds (oneTyping []) intList [.lit 1] [] true) "not established"),
  ("true declaration premise is independently discharged", succeeds
    (run identity nil (zero (.prim .int)) (Δ := []) .nil intList [.lit 0] [] true)),
  ("caller premise permits scoped symbolic application", succeeds
    (run identity nil (zero (.prim .int)) (Δ := [⟨cm, .lit 0⟩]) .nil intList [cm] [99] true)),
  ("scoped symbolic premise requires independent caller evidence", fails
    (run identity nil (zero (.prim .int)) (Δ := []) .nil intList [cm] [99] true) "not established"),
  ("complete supplied slot cannot bypass argument HM mismatch", fails
    (run singleton (.primLit (.int 1)) (.prim .int) (Δ := []) .literal
      (listTy (.prim .char)) [.lit 3] [] false
      (some (.arrow (.prim .char) (listTy (.prim .char)))) (some [.prim .char])) "primitive mismatch"),
  ("application result payload checked separately", fails
    (run identity nil (zero (.prim .int)) (Δ := []) .nil (listTy (.prim .char)) [.lit 0] [] false
      (some (.arrow intList intList))) "result disagrees"),
  ("result-only HM slot is not fabricated from found payload", fails
    (run emptyResult nil (zero (.prim .int)) (Δ := []) .nil (listTy (.prim .char)) [.lit 0]) "disagree"),
  ("explicit result-only primitive slot checked against contract", succeeds
    (run emptyResult nil (zero (.prim .int)) (Δ := []) .nil (listTy (.prim .char)) [.lit 0] [] false
      none (some [.prim .char]))),
  ("higher-order slot proposals retain exact argument bounds", succeeds
    (run singleton function functionBounds functionTyping (listTy arrowHM) [.lit 3])),
  ("supplied higher-order slot checks contravariant domain", fails
    (run singleton function functionBounds functionTyping (listTy arrowHM) [.lit 3] [] false
      none (some [.arrow top top])) "interval inclusion"),
  ("supplied higher-order slot permits covariant result widening", succeeds
    (run singleton function functionBounds functionTyping (listTy arrowHM) [.lit 3] [] false
      none (some [.arrow oneBounds top]))),
  ("origin-backed call rejects scalar contract before proposals", fails
    (run scalar nil (zero (.prim .int)) (Δ := []) .nil (.prim .int) [.lit 3]) "non-arrow body"),
  ("explicit call cannot treat scalar certificate as a function", fails
    (run scalar nil (zero (.prim .int)) (Δ := []) .nil (.prim .int) [.lit 3] [] false
      (some (.prim .int)) (some [])) "not a function")]

def main : IO Unit := do
  for (name, ok) in cases do
    IO.println s!"{if ok then "PASS" else "FAIL"}: {name}"
    unless ok do throw (IO.userError s!"count application regression: {name}")

#eval main

end FHM.Bounds.CountApplicationTests
