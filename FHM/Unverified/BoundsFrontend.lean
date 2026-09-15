import FHM.SurfaceBridge

/-! Operational Bounds-mode selection for CLI/editor frontends.

This is deliberately unverified policy: it detects surface `BL` syntax and
chooses which checker the product should invoke. It proves no typing fact and
does not participate in either HM or Bounds acceptance. -/

namespace FHM.Unverified.BoundsFrontend

inductive Mode where
  | hm
  | bl
  deriving DecidableEq, Repr

def Mode.default : Mode := .hm

def tyContainsBl : Surface.Ty → Bool :=
  Surface.Ty.rec_strong
    (fun _ => false)
    (fun _ _ left right => left || right)
    (fun _ _ left right => left || right)
    (fun _ => false)
    (fun _ args ih => (args.attach.map fun ⟨arg, proof⟩ => ih arg proof).any id)
    (fun _ _ _ _ => true)

def polyContainsBl (sig : Surface.PolyTy) : Bool :=
  tyContainsBl sig.body

def optPolyContainsBl : Option Surface.PolyTy → Bool
  | none => false
  | some sig => polyContainsBl sig

def optTyContainsBl : Option Surface.Ty → Bool
  | none => false
  | some ty => tyContainsBl ty

def paramsContainBl (params : List (ValName × Option Surface.Ty)) : Bool :=
  params.any fun (_, ty) => optTyContainsBl ty

def exprContainsBl : Surface.Expr → Bool :=
  Surface.Expr.rec_strong
    (fun _ => false)
    (fun _ => false)
    (fun _ _ left right => left || right)
    (fun _ _ head tail => head || tail)
    (fun items ih => (items.attach.map fun ⟨e, he⟩ => ih e he).any id)
    (fun _ ann _ body => optTyContainsBl ann || body)
    (fun _ _ fn arg => fn || arg)
    (fun _ _ params ann _ _ rhs body =>
      paramsContainBl params || optPolyContainsBl ann || rhs || body)
    (fun bindings _ ihbs body =>
      (bindings.attach.map fun ⟨binding, proof⟩ =>
        paramsContainBl binding.params || optPolyContainsBl binding.ann ||
          ihbs binding proof).any id || body)
    (fun _ => false)
    (fun _ => false)
    (fun _ _ _ cond yes no => cond || yes || no)
    (fun _ branches scrutinee ihb =>
      scrutinee || (branches.attach.map fun ⟨⟨pattern, branch⟩, proof⟩ =>
        ihb pattern branch proof).any id)

def dataDeclContainsBl (decl : Surface.DataDecl) : Bool :=
  decl.ctors.any fun (_, fields) => fields.any tyContainsBl

def programContainsBl (program : Surface.Program) : Bool :=
  exprContainsBl program.body ||
  program.decls.any dataDeclContainsBl ||
  program.groups.any fun group => group.any fun binding =>
    paramsContainBl binding.params || optPolyContainsBl binding.ann ||
      exprContainsBl binding.rhs

end FHM.Unverified.BoundsFrontend
