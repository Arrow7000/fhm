import FHM.SurfaceLang

/-! Reserved leaves in editor partial trees. Source cannot spell these names.
They have no type and must never reach native lowering or inference. -/
namespace Surface.PartialSyntax

def isHole (name : ValName) : Bool :=
  match name with | .mk text => text.startsWith "$syntax/"

mutual
def hasHole : Surface.Expr → Bool
  | .var name => isHole name
  | .primLit _ | .primBinOp _ | .ctor _ => false
  | .pair a b | .cons a b | .app a b => hasHole a || hasHole b
  | .list xs => hasHoles xs
  | .lambda _ _ body => hasHole body
  | .letIn _ _ _ _ rhs body => hasHole rhs || hasHole body
  | .letRecIn bs body => bindingsHaveHole bs || hasHole body
  | .ife a b c => hasHole a || hasHole b || hasHole c
  | .match_ scrut arms => hasHole scrut || branchesHaveHole arms
private def hasHoles : List Surface.Expr → Bool
  | [] => false
  | e :: rest => hasHole e || hasHoles rest
private def bindingsHaveHole : List Surface.Binding → Bool
  | [] => false
  | b :: rest => hasHole b.rhs || bindingsHaveHole rest
private def branchesHaveHole : List (Surface.Pattern × Surface.Expr) → Bool
  | [] => false
  | (_, e) :: rest => hasHole e || branchesHaveHole rest
end
end Surface.PartialSyntax
