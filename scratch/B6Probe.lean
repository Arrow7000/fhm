import FHM.Surface.Parse
import FHM.SurfaceBridge
import FHM.InferW
import FHM.Pretty
import FHM.Bounds.Erase

open Surface.Parse
open SurfaceBridge
open FHM.Bounds.Erase

private def keD : KindEnv := [(.mk "Bool", 0), (.mk "Pair", 2), (.mk "List", 1), (.mk "Maybe", 1)]

/-- B6 probe v3: lower succeeds, so run Infer directly on the result. -/
def probe : IO Unit := do
  match parseProgram "let id1 {a} (x : a) : a = x\nid1 5" with
  | .error e => IO.println s!"parse err: {e.msg}"
  | .ok p =>
    let ep := eraseProgram p
    let p2 := ep.toProgram
    match lowerProgram p2 with
    | none => IO.println "lower failed"
    | some (ctors, c) =>
      IO.println s!"lowered term: {c.pretty}"
      match infer c.freshFloor ⟨[], ctors⟩ c with
      | none => IO.println "INFER FAILED"
      | some (_, _, τ) => IO.println s!"inferred: {τ.pretty}"

#eval! probe
