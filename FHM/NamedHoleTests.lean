import FHM.Completeness

/-! Canonical source typing and production inference for annotation-local holes. -/

namespace NamedHoleTests

def pair (a b : Ty) : Ty := .customTy ⟨"Pair"⟩ [a, b]
def repeated : TyTemplate := .custom ⟨"Pair"⟩ [.named "a", .named "a"]
def independent : TyTemplate := .custom ⟨"Pair"⟩ [.named "a", .named "b"]
def anonymous : TyTemplate := .custom ⟨"Pair"⟩ [.hole, .hole]
def mixed : TyTemplate := .custom ⟨"Pair"⟩
  [.named "a", .custom ⟨"Pair"⟩ [.hole, .named "a"]]
def identity (annotation : TyTemplate) : InferInput := .lambda (some annotation) (.var 0)

#guard match inferWithTypes [] (identity .hole) with
  | some r => match r.ty with | .arrow (.fvar x) (.fvar y) => x == y | _ => false
  | none => false
#guard match inferWithTypes [] (identity repeated) with
  | some r => match r.ty with | .arrow (.customTy _ [.fvar x, .fvar y]) _ => x == y | _ => false
  | none => false
#guard match inferWithTypes [] (identity independent) with
  | some r => match r.ty with | .arrow (.customTy _ [.fvar x, .fvar y]) _ => x != y | _ => false
  | none => false
#guard match inferWithTypes [] (identity anonymous) with
  | some r => match r.ty with | .arrow (.customTy _ [.fvar x, .fvar y]) _ => x != y | _ => false
  | none => false
#guard match inferWithTypes [] (identity mixed) with
  | some r => match r.ty with
    | .arrow (.customTy _ [.fvar x, .customTy _ [.fvar y, .fvar z]]) _ => x == z && x != y
    | _ => false
  | none => false

def conflictCtx : Ctx := ⟨[PolyTy.mkTrivial (pair (.prim .int) (.prim .char))], []⟩
#guard (inferWithTypesCore [] 10 conflictCtx (.app (identity repeated) (.var 0))).isNone
#guard (inferWithTypesCore [] 10 conflictCtx (.app (identity independent) (.var 0))).isSome

def separate : InferInput := .letIn .absent
  (.app (identity (.named "a")) (.primLit (.int 1)))
  (.app (identity (.named "a")) (.primLit (.char 'x')))
#guard match inferWithTypes [] separate with
  | some r => match r.ty with | .prim .char => true | _ => false
  | none => false
#guard match SmallStep.evaluate 16 separate.erase with
  | some (.primLit (.char 'x')) => true
  | _ => false

def scopedTemplate : TyTemplate := .arrow (.fixed (.bvar 0)) (.named "item")
def scopedProgram : InferInput := .letIn (.partialForall 1 scopedTemplate)
  (.lambda (some (.fixed (.bvar 0))) (.var 0))
  (.app (.var 0) (.primLit (.int 42)))
#guard match inferWithTypes [] scopedProgram with
  | some r => match r.ty with | .prim .int => true | _ => false
  | none => false
#guard match SmallStep.evaluate 16 scopedProgram.erase with
  | some (.primLit (.int 42)) => true
  | _ => false

def recBindings : List InputRecBinding :=
  [{ ann := .partialForall 1 scopedTemplate,
     rhs := .lambda (some (.fixed (.bvar 0))) (.var 0) }]
def recursive : InferInput := .letRec recBindings
  (.letIn .absent (.app (.var 0) (.primLit (.int 1)))
    (.app (.var 1) (.primLit (.char 'x'))))
#guard match inferWithTypes [] recursive with
  | some r => match r.ty with | .prim .char => true | _ => false
  | none => false
#guard match SmallStep.evaluate 24 recursive.erase with
  | some (.primLit (.char 'x')) => true
  | _ => false

/-- The main source matcher enforces equality of repeated local names. -/
theorem repeated_shape (h : repeated.Matches param) : ∃ ty, param = pair ty ty := by
  obtain ⟨_, _, hf⟩ := h
  cases hf with
  | custom hs =>
    cases hs with
    | cons ha hs => cases hs with
      | cons hb hs =>
        cases hs
        have heq := ha.named_equality hb
        cases heq
        exact ⟨_, rfl⟩

theorem conflicting_named_rejected : ¬ repeated.Matches (pair (.prim .int) (.prim .char)) := by
  intro h
  obtain ⟨_, _, hf⟩ := h
  cases hf with
  | custom hs =>
    cases hs with
    | cons ha hs => cases hs with
      | cons hb hs => cases ha.named_equality hb

/-- Actual production inference proves the named source judgment directly. -/
theorem inferred_repeated_fidelity (h : inferWithTypes [] (identity repeated) = some result) :
    ∃ ty output, result.ty = .arrow (pair ty ty) output := by
  obtain ⟨param, output, heq, _, hfit, _, _⟩ := (inferWithTypes_input_sound h).lambda_inv
  obtain ⟨ty, hparam⟩ := repeated_shape (hfit repeated rfl)
  exact ⟨ty, output, heq.trans (congrArg (fun p => Ty.arrow p output) hparam)⟩

/-- One bound-variable completion is selected before every fresh opening. -/
theorem inferred_scoped_once (h : inferWithTypes [] scopedProgram = some result) :
    ∃ (scheme : PolyTy) (avoid : List Nat)
      (completion : PartialCore.Completion scheme.paramCount scopedTemplate scheme.body),
      ∀ Xs, FreshNames avoid scheme.paramCount Xs →
        PartialCore.Template.Fits (PartialCore.HoleAssignment.map (Ty.openVars Xs) completion.holes)
          (scopedTemplate.map (Ty.openVars (Xs.take 1))) (scheme.openVars Xs) := by
  obtain ⟨scheme, avoid, completion, _, _, hopen, _, _⟩ :=
    (inferWithTypes_input_sound h).partialSignature_completion
  exact ⟨scheme, avoid, completion, hopen⟩

theorem inferred_recursive_once (h : inferWithTypes [] recursive = some result) :
    ∃ (specs : List RecSpec) (prefixes : List (List Nat)) (pool : List Nat),
      RecAnnotationsMatch recBindings specs prefixes pool := by
  obtain ⟨specs, _, prefixes, pool, _, _, _, _, _, _, hm, _, _, _⟩ :=
    (inferWithTypes_input_sound h).rec_inv
  exact ⟨specs, prefixes, pool, hm⟩

#print axioms repeated_shape
#print axioms inferred_repeated_fidelity
#print axioms inferred_scoped_once
#print axioms inferred_recursive_once
#print axioms Infer.sound
#print axioms inferWithTypes_principal

end NamedHoleTests
