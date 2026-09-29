import FHM.SurfaceLang

/-!
# Plain-HM surface boundary

Temporary source-shape guard used while the parser still contains the retired
bounded-list grammar.  Once that grammar is removed, this module can disappear:
the parser itself will enforce the same boundary.
-/

namespace FHM.Unverified.HMFrontend

def tyContainsBounds : Surface.Ty → Bool :=
  Surface.Ty.rec_strong
    (fun _ => false)
    (fun _ _ left right => left || right)
    (fun _ _ left right => left || right)
    (fun _ => false)
    (fun _ args ih => (args.attach.map fun ⟨arg, proof⟩ => ih arg proof).any id)
    (fun _ _ _ _ => true)

def polyContainsBounds (scheme : Surface.PolyTy) : Bool :=
  tyContainsBounds scheme.body

def optTyContainsBounds : Option Surface.Ty → Bool
  | none => false
  | some ty => tyContainsBounds ty

def optPolyContainsBounds : Option Surface.PolyTy → Bool
  | none => false
  | some scheme => polyContainsBounds scheme

def paramsContainBounds (params : List (ValName × Option Surface.Ty)) : Bool :=
  params.any fun (_, ty) => optTyContainsBounds ty

def bindingContainsBounds (binding : Surface.Binding) (rhsContainsBounds : Bool) : Bool :=
  !binding.natBinders.isEmpty || paramsContainBounds binding.params ||
    optPolyContainsBounds binding.ann || rhsContainsBounds

def exprContainsBounds : Surface.Expr → Bool :=
  Surface.Expr.rec_strong
    (fun _ => false)
    (fun _ => false)
    (fun _ _ left right => left || right)
    (fun _ _ head tail => head || tail)
    (fun items ih => (items.attach.map fun ⟨item, proof⟩ => ih item proof).any id)
    (fun _ ann _ body => optTyContainsBounds ann || body)
    (fun _ _ fn arg => fn || arg)
    (fun _ _ params ann _ _ rhs body =>
      paramsContainBounds params || optPolyContainsBounds ann || rhs || body)
    (fun bindings _ ihBindings body =>
      (bindings.attach.map fun ⟨binding, proof⟩ =>
        bindingContainsBounds binding (ihBindings binding proof)).any id || body)
    (fun _ => false)
    (fun _ => false)
    (fun _ _ _ cond yes no => cond || yes || no)
    (fun _ branches scrutinee ihBranches =>
      scrutinee || (branches.attach.map fun ⟨⟨pattern, branch⟩, proof⟩ =>
        ihBranches pattern branch proof).any id)

def dataDeclContainsBounds (decl : Surface.DataDecl) : Bool :=
  decl.ctors.any fun (_, fields) => fields.any tyContainsBounds

def programContainsBounds (program : Surface.Program) : Bool :=
  exprContainsBounds program.body ||
    program.decls.any dataDeclContainsBounds ||
    program.groups.any fun group => group.any fun binding =>
      bindingContainsBounds binding (exprContainsBounds binding.rhs)

def unsupportedMessage : String :=
  "bounded-list and count syntax is not supported by the Hindley--Milner language"

end FHM.Unverified.HMFrontend
