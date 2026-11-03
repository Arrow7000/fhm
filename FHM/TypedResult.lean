import FHM.Core

/-! Projection laws used while callers and proofs migrate to native error
results. These erase failure data without introducing another worker. -/

register_simp_attr typed_result_projection

namespace TypedResult

theorem toOption_ok {ε α : Type} (value : α) :
    (Except.ok value : Except ε α).toOption = some value := rfl

theorem toOption_pure {ε α : Type} (value : α) :
    (pure value : Except ε α).toOption = some value := rfl

theorem toOption_error {ε α : Type} (error : ε) :
    (Except.error error : Except ε α).toOption = none := rfl

theorem toOption_bind {ε α β : Type} (result : Except ε α) (next : α → Except ε β) :
    (result >>= next).toOption = result.toOption.bind (fun value => (next value).toOption) := by
  cases result <;> rfl

theorem toOption_mapError {ε δ α : Type} (result : Except ε α) (map : ε → δ) :
    (result.mapError map).toOption = result.toOption := by
  cases result <;> rfl

theorem toOption_map {ε α β : Type} (result : Except ε α) (map : α → β) :
    (result.map map).toOption = result.toOption.map map := by
  cases result <;> rfl

theorem toOption_ite {ε α : Type} (condition : Prop) [Decidable condition]
    (yes no : Except ε α) :
    (if condition then yes else no).toOption =
      if condition then yes.toOption else no.toOption := by
  split <;> rfl

theorem toOption_dite {ε α : Type} (condition : Prop) [Decidable condition]
    (yes : condition → Except ε α) (no : ¬ condition → Except ε α) :
    (if h : condition then yes h else no h).toOption =
      if h : condition then (yes h).toOption else (no h).toOption := by
  split <;> rfl

theorem toOption_eq_some {ε α : Type} {result : Except ε α} {value : α} :
    result.toOption = some value ↔ result = .ok value := by
  cases result <;> simp [Except.toOption]

end TypedResult
