import EPL.Examples
import EPL.Tests
import EPL.Properties.InferenceState
import EPL.Properties.Declarative
import EPL.Properties.Runtime
import EPL.Properties.InferenceSound
import EPL.Properties.EndToEnd
import EPL.Properties.Unification

namespace EPL.Headlines

#check @Typing.regular
#check @Typing.sourceScoped
#check @Typing.weakenRigids
#check @Typing.erase
#check @RuntimeTyping.regular
#check @RuntimeTyping.weakenRigids
#check @RuntimeTyping.genericHasScheme
#check @RuntimeTyping.substScheme
#check @RuntimeTyping.progress
#check @RuntimeTyping.preservation
#check @MStore.unify_sound
#check @MStore.unify_complete
#check @MStore.unify_leveled
#check @inferFuel_safe
#check @InferState.has_model
#check @inferFuel_sound_model
#check @Elaborates.typing
#check @infer_sound
#check @infer_typing
#check @infer_result_wf
#check @inferFuel_principal
#check @inferFuel_principal_elab
#check @inferFuel_complete
#check @infer_type_unique
#check @infer_eq_some_iff
#check @infer_eq_none_iff
#check @infer_erases
#check @infer_progress
#check @infer_step_preserves
#check @infer_steps_preserve
#check @infer_type_safety
#check @Eval.step?_sound
#check @Eval.step?_complete
#check @Eval.Step.deterministic
#check @Eval.run_steps
#check @Eval.run_complete
#check @infer_run_typed
#check @infer_run_stops_at_value
#check @evaluate

#print axioms Typing.regular
#print axioms Typing.sourceScoped
#print axioms Typing.weakenRigids
#print axioms Typing.erase
#print axioms RuntimeTyping.genericHasScheme
#print axioms RuntimeTyping.substScheme
#print axioms RuntimeTyping.progress
#print axioms RuntimeTyping.preservation
#print axioms MStore.unify_sound
#print axioms MStore.unify_complete
#print axioms MStore.unify_leveled
#print axioms inferFuel_safe
#print axioms InferState.has_model
#print axioms inferFuel_sound_model
#print axioms Elaborates.typing
#print axioms infer_sound
#print axioms infer_typing
#print axioms infer_result_wf
#print axioms inferFuel_principal
#print axioms inferFuel_principal_elab
#print axioms inferFuel_complete
#print axioms infer_type_unique
#print axioms infer_eq_some_iff
#print axioms infer_eq_none_iff
#print axioms infer_erases
#print axioms infer_progress
#print axioms infer_step_preserves
#print axioms infer_steps_preserve
#print axioms infer_type_safety
#print axioms Eval.step?_sound
#print axioms Eval.step?_complete
#print axioms Eval.Step.deterministic
#print axioms Eval.run_steps
#print axioms Eval.run_complete
#print axioms infer_run_typed
#print axioms infer_run_stops_at_value
#print axioms evaluate

end EPL.Headlines
