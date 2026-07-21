import FHM.SurfaceBridge

/-!
Shared pipeline helpers used by `Live` and `EditorSupport`.
-/

open SurfaceBridge

/-- Collect schemes from the outer `letIn (some σ)` spine produced by
    `letRecElab` (stops at the program body). -/
partial def collectTopSchemes : Expr → List PolyTy
  | .letIn (some σ) _ body => σ :: collectTopSchemes body
  | _ => []

/-- `letRecElab` wraps group members outermost-last, so each group's chunk of
    schemes from `collectTopSchemes` is reversed relative to binding order.
    Undo that per SCC group and zip with surface names. -/
def zipBindingTypes (groups : List (List Surface.Binding)) (schemes : List PolyTy) :
    List (ValName × PolyTy) :=
  let rec go (gs : List (List Surface.Binding)) (ss : List PolyTy)
      (acc : List (ValName × PolyTy)) : List (ValName × PolyTy) :=
    match gs with
    | [] => acc
    | g :: gs' =>
      let n := g.length
      let chunk := (ss.take n).reverse
      let pairs := g.map (·.name) |>.zip chunk
      go gs' (ss.drop n) (acc ++ pairs)
  go groups schemes []
