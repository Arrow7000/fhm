import FHM.Surface.Parse
import FHM.SurfaceBridge
import FHM.InferW
import FHM.Pretty
import FHM.Bounds.Erase

open Surface.Parse
open SurfaceBridge
open FHM.Bounds.Erase

/-- Lower a source program and print the lowered core term (what Infer sees). -/
def probeLower (src : String) : IO Unit := do
  match parseProgram src with
  | .error e => IO.println s!"parse err: {e.msg}"
  | .ok p =>
    let ep := eraseProgram p
    let p2 := ep.toProgram
    match lowerProgram p2 with
    | none => IO.println "lower failed"
    | some (ctors, c) =>
      IO.println s!"lowered term:\n{c.pretty}"
      match infer c.freshFloor ⟨[], ctors⟩ c with
      | none => IO.println "INFER FAILED"
      | some r => IO.println s!"inferred: {r.2.2.pretty}"

/-- Mycroft's nested: annotated self-recursion at a different instantiation. -/
def nestedSrc : String :=
"let size : {a} Nested a -> Int = \\n -> match n with | Elem e -> 1 | Group h -> 1 + size h\nsize (Group (Elem [5]))"

/-- inner-poly calls: annotated f used at two instantiations inside the group. -/
def innerPolySrc : String :=
"let f : {a} Int -> a -> Int = \\n x -> if n < 1 then 1 else g (n - 1)\nlet g = \\n -> f n n + f n [n]\nf 2 5"

/-- skolem leak: annotated f passes its rigid scoped arg to unannotated g. -/
def leakSrc : String :=
"let f : {a} Int -> a -> List a = \\n x -> if n < 1 then Cons x Nil else g (n - 1) x\nlet g = \\n x -> Cons x (f n x)\nf 2 5"

#eval! probeLower nestedSrc
#eval! probeLower innerPolySrc
#eval! probeLower leakSrc
