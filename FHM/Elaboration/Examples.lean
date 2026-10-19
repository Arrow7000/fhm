import FHM.Elaboration.Complete
import FHM.Decls

/-! Semantic canaries for the proved anonymous lambda/ordinary-let slice.
These run the elaborator itself; output typing follows from `Infer.sourceSound`.
-/

namespace Elaboration.Examples

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

private def idHole : Input := .lambda (some .hole) (.var 0)

-- Independent local allocation: two syntactic visits, unrelated types.
def distinctCopies : Input := pair idHole idHole
#guard match inferCore [] 0 ctx distinctCopies with
  | some ⟨(_, _, _, .customTy ⟨"Pair"⟩
      [.arrow (.fvar a) (.fvar a'), .arrow (.fvar b) (.fvar b')]), _⟩ =>
      a == a' && b == b' && a != b
  | _ => false

-- Independent local uses: same Input value copied, each used at a different type.
def differentlyUsedCopies : Input :=
  pair (.app idHole (.primLit (.int 1))) (.app idHole (.ctor ⟨"True"⟩))
#guard (inferCore [] 0 ctx differentlyUsedCopies).isSome

-- Reallocating the holes must not reallocate the shared outer monomorphic f.
def sharedOuterRejected : Input :=
  .lambda none
    (pair
      (.app (.lambda (some .hole) (.app (.var 1) (.var 0))) (.primLit (.int 1)))
      (.app (.lambda (some .hole) (.app (.var 1) (.var 0))) (.ctor ⟨"True"⟩)))
#guard !(inferCore [] 0 ctx sharedOuterRejected).isSome

private def branches (yes no : Input) : List (MatchPattern × Input) :=
  [(.named ⟨"True"⟩ 0, yes), (.named ⟨"False"⟩ 0, no)]

-- Direct partial match currently unsupported, even if only the scrutinee has a hole.
def directPartialScrutinee : Input :=
  .match_ (.app idHole (.ctor ⟨"True"⟩))
    (branches (.primLit (.int 1)) (.primLit (.int 0)))
#guard !(inferCore [] 0 ctx directPartialScrutinee).isSome

-- Equivalent normal lowering shape: the match scrutinee is bound once first.
def loweredPartialScrutinee : Input :=
  .letIn .absent (.app idHole (.ctor ⟨"True"⟩))
    (.match_ (.var 0) (branches (.primLit (.int 1)) (.primLit (.int 0))))
#guard (inferCore [] 0 ctx loweredPartialScrutinee).isSome

-- Nested complete match is an argument to the partial scrutinee expression.
def nestedScrutinee : Input :=
  .letIn .absent
    (.app idHole
      (.letIn .absent (.ctor ⟨"False"⟩)
        (.match_ (.var 0) (branches (.ctor ⟨"False"⟩) (.ctor ⟨"True"⟩)))))
    (.match_ (.var 0) (branches (.primLit (.int 1)) (.primLit (.int 0))))
#guard (inferCore [] 0 ctx nestedScrutinee).isSome

-- Lowering an irrefutable named pattern makes another ordinary let. This
-- checks the existing lowering/generalization policy, independently of copying.
def irrefutableCapture : Input :=
  .letIn .absent idHole
    (.letIn .absent (.var 0)
      (pair (.app (.var 0) (.primLit (.int 1)))
        (.app (.var 0) (.ctor ⟨"True"⟩))))
#guard (inferCore [] 0 ctx irrefutableCapture).isSome


private def rigidArrow : Template := .arrow (.fixed (.fvar 7)) .hole
private def rigidIdentity : Input := .lambda (some rigidArrow) (.var 0)
private def violatesRigid : Input :=
  .lambda (some rigidArrow) (.app (.var 0) (.primLit (.int 1)))
private def rigidLet : Input :=
  .letIn (.template rigidArrow) (.lambda none (.var 0)) (.var 0)
private def violatesRigidLet : Input :=
  .letIn (.template rigidArrow) (.lambda none (.var 0))
    (.app (.var 0) (.primLit (.int 1)))

#guard (inferCore [7] 8 ctx rigidIdentity).isSome
#guard !(inferCore [7] 8 ctx violatesRigid).isSome
#guard !(inferCore [] 8 ctx rigidIdentity).isSome
#guard (inferCore [7] 8 ctx rigidLet).isSome
#guard !(inferCore [7] 8 ctx violatesRigidLet).isSome
#guard match inferCore [7] 8 ctx rigidLet with
  | some ⟨(_, _, .letIn (some scheme) _ _, .arrow (.fvar 7) (.fvar 7)), _⟩ =>
      scheme.paramCount == 0
  | _ => false

private def polyrec : Input :=
  .letRec [.complete ⟨1, .arrow (.bvar 0) (.prim .int)⟩]
    [.lambda none
      (.app (.var 1) (.app (.app (.ctor ⟨"Pair"⟩) (.var 0)) (.var 0)))]
    (.app (.var 0) (.ctor ⟨"True"⟩))
#guard (inferCore [] 0 ctx polyrec).isSome
#guard (inferCore [] 0 ctx
  (.letIn .absent (.lambda (some .hole) (.var 0)) polyrec)).isSome
#guard !(CoreBackend.principalType ctx.ctors polyrec.erase).isSome

-- Complete signatures with holes in their RHS are outside the first dispatch
-- fragment, including cases whose holes would be compatible with its skolems.
def completeForallWithPartialRhs : Input :=
  .letIn (.complete ⟨1, .arrow (.bvar 0) (.bvar 0)⟩)
    (.lambda (some .hole) (.var 0)) (.var 0)
#guard !(inferCore [] 0 ctx completeForallWithPartialRhs).isSome

-- An unused hole still generalizes at its own binding even when it is absent
-- from the whole-program result type.
def unusedHole : Input :=
  .letIn (.template .hole) (.ctor ⟨"Nil"⟩) (.primLit (.int 1))
#guard match inferCore [] 0 ctx unusedHole with
  | some ⟨(_, _, .letIn (some ⟨1, .customTy ⟨"List"⟩ [.bvar 0]⟩) _ _, .prim .int), _⟩ => true
  | _ => false

-- Public artifacts and completed output come from the same run. Synthetic
-- scheme binders do not turn source hover monotypes into dangling bvars.
#guard match inferWithTypes ctors polymorphicId with
  | some result => result.binderSchemes.any (fun fact => fact.2.paramCount == 1)
  | none => false
#guard match (inferWithTypes ctors polymorphicId).bind (fun result =>
    result.nodeTypes.find? (fun fact => fact.1 == [.letRhs])) with
  | some (_, .arrow (.fvar 0) (.fvar 0)) => true
  | _ => false

#print axioms Infer.sourceSound
#print axioms Infer.inputSound
#print axioms Infer.completes
#print axioms Infer.erase

end Elaboration.Examples
