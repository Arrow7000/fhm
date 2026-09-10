import FHM.Bounds.Found

open Surface Surface.Span SurfaceBridge SurfaceBridge.Provenance
open FHM.Bounds FHM.Bounds.Found

private def demoCtors : CtorEnv := (elabDecls preludeDecls).getD []

private def listSurface : Surface.Expr :=
  .list [.primLit (.int 1), .primLit (.int 2)]

private def listSpanned : SpannedExpr :=
  .list ⟨1, 1, 1, 7⟩ [.leaf ⟨1, 2, 1, 3⟩, .leaf ⟨1, 5, 1, 6⟩]

private def foundHoverBoundsVertical : Bool :=
  match checkRoot demoCtors listSurface listSpanned with
  | .error _ => false
  | .ok (typed, report) =>
      let hoverOk := match typed.hoverAt? 1 2 with
        | some ⟨⟨1, _⟩, [([.appFun, .appArg], .prim .int)]⟩ => true
        | _ => false
      let hmOk := match report.hm with
        | .customTy ⟨"List"⟩ [.prim .int] => true
        | _ => false
      let boundsOk := report.bounds.pretty == "BL 2 2 Int"
      report.source.id == 0 && hoverOk && hmOk && boundsOk

def main : IO Unit := do
  let ok := foundHoverBoundsVertical
  IO.println s!"{if ok then "PASS" else "FAIL"}: found → hover → root bounds"
  unless ok do throw (IO.userError "found/bounds vertical check failed")
