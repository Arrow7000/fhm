import FHM.AnonymousInfer
import FHM.Decls

/-! Semantic canaries for the proved anonymous lambda/ordinary-let slice.
These run the elaborator itself; output typing follows from `Infer.sourceSound`.
-/

namespace Anonymous.Examples

private def ctors : CtorEnv := (elabDecls preludeDecls).getD []
private def ctx : Ctx := ⟨[], ctors⟩

private def pair (left right : Input) : Input :=
  .app (.app (.ctor ⟨"Pair"⟩) left) right

/-- `let id = \(x : _) -> x in (id 1, id True)`. -/
def polymorphicId : Input :=
  .letIn .absent (.lambda (some .hole) (.var 0))
    (pair (.app (.var 0) (.primLit (.int 1))) (.app (.var 0) (.ctor ⟨"True"⟩)))

/-- Both occurrences of `_` are independently flexible. -/
def independentHoles : Input :=
  .letIn (.template (.arrow .hole .hole))
    (.lambda none (.primLit (.int 1)))
    (pair (.app (.var 0) (.ctor ⟨"True"⟩)) (.app (.var 0) (.primLit (.int 1))))

def structuredId : Input :=
  .letIn (.template (.arrow .hole .hole)) (.lambda none (.var 0))
    (pair (.app (.var 0) (.primLit (.int 1))) (.app (.var 0) (.ctor ⟨"True"⟩)))

/-- Variables reachable through the outer context cannot be generalized. -/
def outerMonomorphic : Input :=
  .lambda none
    (.letIn (.template .hole) (.var 0)
      (pair (.app (.var 0) (.primLit (.int 1))) (.app (.var 0) (.ctor ⟨"True"⟩))))

def occursCheck : Input :=
  .lambda (some .hole) (.app (.var 0) (.var 0))

def fixedDomainAccepted : Input :=
  .letIn (.template (.arrow (.fixed (.prim .int)) .hole)) (.lambda none (.var 0))
    (.app (.var 0) (.primLit (.int 1)))

def fixedDomainRejected : Input :=
  .letIn (.template (.arrow (.fixed (.prim .int)) .hole)) (.lambda none (.var 0))
    (.app (.var 0) (.ctor ⟨"True"⟩))

def rejectsPartialForall : Input :=
  .letIn (.partialForall 1 (.arrow (.fixed (.bvar 0)) .hole))
    (.lambda none (.var 0)) (.var 0)

def rejectsPartialRecursion : Input :=
  .letRec [.template (.arrow .hole (.fixed (.prim .int)))]
    [.lambda none (.primLit (.int 0))] (.var 0)

#guard (inferCore [] 0 ctx polymorphicId).isSome
#guard (inferCore [] 0 ctx independentHoles).isSome
#guard (inferCore [] 0 ctx structuredId).isSome
#guard !(inferCore [] 0 ctx outerMonomorphic).isSome
#guard !(inferCore [] 0 ctx occursCheck).isSome
#guard (inferCore [] 0 ctx fixedDomainAccepted).isSome
#guard !(inferCore [] 0 ctx fixedDomainRejected).isSome
#guard !(inferCore [] 0 ctx rejectsPartialForall).isSome
#guard !(inferCore [] 0 ctx rejectsPartialRecursion).isSome

/- The id canary really introduces a scheme binder and closes the lambda
annotation underneath that same binder. -/
#guard match inferCore [] 0 ctx polymorphicId with
  | some ⟨(_, _, .letIn (some scheme) (.lambda (some (.bvar 0)) _) _, _), _⟩ =>
      scheme.paramCount == 1
  | _ => false

end Anonymous.Examples
