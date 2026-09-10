import FHM.Core

/-! # Logical paths through Core expressions

Paths describe the ordinary Core skeleton. Inference metadata (`Expr.found`) is
transparent: adding or removing found wrappers never changes a path.
-/

/-- One edge from a Core expression to an immediate logical child. -/
inductive CoreStep where
  | lambdaBody
  | appFun
  | appArg
  | letRhs
  | letBody
  | matchScrut
  | matchBranch (index : Nat)
  | letRecRhs (member : Nat)
  | letRecBody
  deriving Repr, DecidableEq, BEq

/-- A root-relative path in the `.found`-transparent Core skeleton. -/
abbrev CorePath := List CoreStep

namespace CorePath

/-- Put every path below the same immediate Core edge. -/
def below (step : CoreStep) (paths : List CorePath) : List CorePath :=
  paths.map (step :: ·)

end CorePath

/-- Look up a logical Core node. A nonempty path passes transparently through
    any `.found` wrapper; an empty path returns the node including its wrapper,
    when present, so callers can inspect the discovered type. -/
def Expr.atCorePath : Expr → CorePath → Option Expr
  | e, [] => some e
  | .found _ inner, path => inner.atCorePath path
  | .lambda _ body, .lambdaBody :: rest => body.atCorePath rest
  | .app f _, .appFun :: rest => f.atCorePath rest
  | .app _ input, .appArg :: rest => input.atCorePath rest
  | .letIn _ rhs _, .letRhs :: rest => rhs.atCorePath rest
  | .letIn _ _ body, .letBody :: rest => body.atCorePath rest
  | .match_ scrut _, .matchScrut :: rest => scrut.atCorePath rest
  | .match_ _ branches, .matchBranch index :: rest =>
      match _h : branches[index]? with
      | some (_, body) => body.atCorePath rest
      | none => none
  | .letRec _ bindings _, .letRecRhs member :: rest =>
      match _h : bindings[member]? with
      | some rhs => rhs.atCorePath rest
      | none => none
  | .letRec _ _ body, .letRecBody :: rest => body.atCorePath rest
  | _, _ => none
termination_by e path => sizeOf e + sizeOf path
decreasing_by
  all_goals simp_wf
  all_goals first
    | omega
    | (have hsz := List.sizeOf_lt_of_mem (List.mem_of_getElem? _h); omega)
    | (have hsz := List.sizeOf_lt_of_mem (List.mem_of_getElem? _h)
       simp only [Prod.mk.sizeOf_spec] at hsz
       omega)

/-- A binder-producing position in Core. Several source binders can point into
    one node (a recursive group), and pattern compilation can duplicate a
    capture site. -/
inductive CoreBinderSite where
  | lambda (path : CorePath)
  | letIn (path : CorePath)
  | letRec (path : CorePath) (member : Nat)
  | patCapture (paths : List CorePath) (capture : Nat)
  deriving Repr, DecidableEq, BEq

private def foundPathDemo : Expr :=
  .found (.prim .int)
    (.app
      (.found (.arrow (.prim .int) (.prim .int)) (.var 0))
      (.found (.prim .int) (.primLit (.int 1))))

#guard match foundPathDemo.atCorePath [] with
  | some (.found (.prim .int) (.app _ _)) => true
  | _ => false

#guard match foundPathDemo.atCorePath [.appFun] with
  | some (.found (.arrow (.prim .int) (.prim .int)) (.var 0)) => true
  | _ => false

#guard match foundPathDemo.atCorePath [.appArg] with
  | some (.found (.prim .int) (.primLit (.int 1))) => true
  | _ => false
