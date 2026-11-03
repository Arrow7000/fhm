import FHM.Core

/-! Projection laws used while callers and proofs migrate to native error
results. These erase failure data without introducing another worker. -/

register_simp_attr typed_result_projection

namespace TypedResult

/-- A checked condition with caller-supplied failure data. -/
def ensure {ε : Type} (error : ε) (condition : Prop) [Decidable condition] : Except ε Unit :=
  if condition then .ok () else .error error

theorem toOption_ensure {ε : Type} (error : ε) (condition : Prop) [Decidable condition] :
    (ensure error condition).toOption = (guard condition : Option Unit) := by
  by_cases h : condition <;> simp [ensure, guard, h, Except.toOption]

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

theorem toOption_mapM {ε α β : Type} (map : α → Except ε β) (values : List α) :
    (values.mapM map).toOption = values.mapM (fun value => (map value).toOption) := by
  induction values with
  | nil => rfl
  | cons value rest ih =>
      simp only [List.mapM_cons, toOption_bind, toOption_pure, ih]

end TypedResult
