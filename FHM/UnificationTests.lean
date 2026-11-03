import FHM.InferenceFoundations

/-! Native typed-unification failures, propagation through solved constraints,
and the success contract used by existing inference clients. -/

namespace UnificationTests

-- Rigid variables can be equal or receive a flexible variable, but cannot
-- acquire a concrete type or be equated with another rigid variable.
#guard (unifyResultK [0] (.fvar 0) (.fvar 0)).isOk
#guard match unifyResultK [0] (.fvar 0) (.fvar 1) with
  | .ok ⟨[(1, .fvar 0)], _⟩ => true
  | _ => false
#guard match unifyResultK [0] (.fvar 1) (.fvar 0) with
  | .ok ⟨[(1, .fvar 0)], _⟩ => true
  | _ => false
#guard match unifyResultK [0, 1] (.fvar 0) (.fvar 1) with
  | .error (.rigidVariable 0 (.fvar 1)) => true
  | _ => false
#guard match unifyResultK [0] (.fvar 0) (.prim .int) with
  | .error (.rigidVariable 0 (.prim .int)) => true
  | _ => false
#guard match unifyResultK [0] (.prim .int) (.fvar 0) with
  | .error (.rigidVariable 0 (.prim .int)) => true
  | _ => false

-- Rigidity takes precedence over an occurs check on the same variable.
#guard match unifyResultK [0] (.fvar 0) (.arrow (.fvar 0) (.prim .int)) with
  | .error (.rigidVariable 0 (.arrow (.fvar 0) (.prim .int))) => true
  | _ => false
#guard match unifyResult (.fvar 0) (.arrow (.fvar 0) (.prim .int)) with
  | .error (.occursCheck 0 (.arrow (.fvar 0) (.prim .int))) => true
  | _ => false
#guard match unifyResult (.arrow (.fvar 0) (.prim .int)) (.fvar 0) with
  | .error (.occursCheck 0 (.arrow (.fvar 0) (.prim .int))) => true
  | _ => false

-- A later failure contains substituted operands, not the original variables.
#guard match unifyResult (.arrow (.fvar 0) (.fvar 0))
    (.arrow (.prim .int) (.prim .char)) with
  | .error (.mismatch (.prim .int) (.prim .char)) => true
  | _ => false
#guard match unifyResult (.arrow (.fvar 0) (.fvar 1))
    (.arrow (.fvar 1) (.arrow (.fvar 0) (.prim .int))) with
  | .error (.occursCheck 1 (.arrow (.fvar 1) (.prim .int))) => true
  | _ => false
#guard match unifyResult (.customTy ⟨"Pair"⟩ [.fvar 0, .fvar 0])
    (.customTy ⟨"Pair"⟩ [.prim .int, .prim .char]) with
  | .error (.mismatch (.prim .int) (.prim .char)) => true
  | _ => false

-- Different constructor names are distinct from unmatched argument lists.
#guard match unifyResult (.customTy ⟨"Left"⟩ []) (.customTy ⟨"Right"⟩ []) with
  | .error (.mismatch (.customTy ⟨"Left"⟩ []) (.customTy ⟨"Right"⟩ [])) => true
  | _ => false
#guard match unifyResult (.customTy ⟨"List"⟩ [.prim .int]) (.customTy ⟨"List"⟩ []) with
  | .error (.arityMismatch [.prim .int] []) => true
  | _ => false
#guard match unifyListResultK [] [] [.prim .char] with
  | .error (.arityMismatch [] [.prim .char]) => true
  | _ => false
#guard match unifyListResultK [] [.fvar 0, .fvar 0] [.prim .int] with
  | .error (.arityMismatch [.prim .int] []) => true
  | _ => false

-- Unopened bound variables remain outside the unifier's accepted inputs.
#guard match unifyResult (.bvar 0) (.bvar 0) with
  | .error (.mismatch (.bvar 0) (.bvar 0)) => true
  | _ => false

-- Composition and orientation are observable through the old API as well.
#guard match unifyResult (.arrow (.fvar 0) (.fvar 1))
    (.arrow (.prim .int) (.prim .char)) with
  | .ok [(0, .prim .int), (1, .prim .char)] => true
  | _ => false

example (a b : Ty) : (unifyResult a b).toOption = unify a b :=
  unifyResult_toOption a b

-- An error is a verified rejection, under the existing LC/rigidity contract.
example {K : List Nat} {a b : Ty} {error : UnifyError} {subst : Subst}
    (herror : unifyResultK K a b = .error error)
    (ha : a.IsLC) (hb : b.IsLC) (hlc : ∀ pair ∈ subst, pair.2.IsLC)
    (hrigid : ∀ k ∈ K, subst.onTy (.fvar k) = .fvar k) :
    ¬ Unifies subst a b :=
  unifyResultK_error_not_unifies herror ha hb hlc hrigid

end UnificationTests
