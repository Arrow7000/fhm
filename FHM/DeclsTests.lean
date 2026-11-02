import FHM.Decls

/-! Result fidelity: declaration validation alone cannot justify these facts. -/

namespace DeclsTests

def box : DataDecl :=
  { name := ⟨"Box"⟩, paramCount := 1,
    ctors := [(⟨"Box"⟩, [.bvar 0]), (⟨"Empty"⟩, [])] }

theorem actual_signatures (h : elabDecls [box] = some env) :
    env.signatures =
      [(⟨"Box"⟩, (1, ⟨"Box"⟩, [.bvar 0])), (⟨"Empty"⟩, (1, ⟨"Box"⟩, []))] :=
  (elabDecls_sound h).constructors

theorem cannot_discard : ¬ DataDecls.ElaboratesTo [box] [] := by
  intro h
  cases h.constructors

-- The contract rejects every way of corrupting a constructor's semantic data.
theorem cannot_change_fields (h : DataDecls.ElaboratesTo [box] env)
    (bad : env.signatures =
      [(⟨"Box"⟩, (1, ⟨"Box"⟩, [.prim .int])), (⟨"Empty"⟩, (1, ⟨"Box"⟩, []))]) : False := by
  have heq := bad.symm.trans h.constructors
  cases heq

theorem cannot_change_parent (h : DataDecls.ElaboratesTo [box] env)
    (bad : env.signatures =
      [(⟨"Box"⟩, (1, ⟨"Other"⟩, [.bvar 0])), (⟨"Empty"⟩, (1, ⟨"Box"⟩, []))]) : False := by
  have heq := bad.symm.trans h.constructors
  simp [DataDecls.constructorSignatures, box] at heq

theorem cannot_change_arity (h : DataDecls.ElaboratesTo [box] env)
    (bad : env.signatures =
      [(⟨"Box"⟩, (2, ⟨"Box"⟩, [.bvar 0])), (⟨"Empty"⟩, (1, ⟨"Box"⟩, []))]) : False := by
  have heq := bad.symm.trans h.constructors
  cases heq

theorem cannot_change_name (h : DataDecls.ElaboratesTo [box] env)
    (bad : env.signatures =
      [(⟨"Other"⟩, (1, ⟨"Box"⟩, [.bvar 0])), (⟨"Empty"⟩, (1, ⟨"Box"⟩, []))]) : False := by
  have heq := bad.symm.trans h.constructors
  simp [DataDecls.constructorSignatures, box] at heq

theorem cannot_drop_one (h : DataDecls.ElaboratesTo [box] env)
    (bad : env.signatures = [(⟨"Box"⟩, (1, ⟨"Box"⟩, [.bvar 0]))]) : False := by
  have heq := bad.symm.trans h.constructors
  cases heq

theorem cannot_add_entry (h : DataDecls.ElaboratesTo [box] env)
    (bad : env.signatures =
      [(⟨"Box"⟩, (1, ⟨"Box"⟩, [.bvar 0])), (⟨"Empty"⟩, (1, ⟨"Box"⟩, [])),
       (⟨"Extra"⟩, (0, ⟨"Extra"⟩, []))]) : False := by
  have heq := bad.symm.trans h.constructors
  cases heq

#guard match elabDecls [box] with
  | some [(_, first), (_, second)] => first.paramCount == 1 && second.paramCount == 1
  | _ => false

#print axioms elabDecls_sound
#print axioms elabDecls_eq_some_iff
#print axioms cannot_discard

end DeclsTests
