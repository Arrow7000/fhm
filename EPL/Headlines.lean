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
#check @unify_sound
#check @unify_scoped
#check @Template.allocate_fits
#check @Template.allocate_scoped
#check @inferFuel_safe
#check @InferState.has_model
#check @MStore.Models.realize_apply
#check @Template.allocate_matches_realize
#check @InferState.constrain_refines
#check @MStore.Models.extend_checkedPrefix
#check @inferFuel_sound_model
#check @infer_sound
#check @infer_result_wf
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
#print axioms unify_sound
#print axioms unify_scoped
#print axioms Template.allocate_fits
#print axioms Template.allocate_scoped
#print axioms inferFuel_safe
#print axioms InferState.has_model
#print axioms MStore.Models.realize_apply
#print axioms Template.allocate_matches_realize
#print axioms InferState.constrain_refines
#print axioms MStore.Models.extend_checkedPrefix
#print axioms inferFuel_sound_model
#print axioms infer_sound
#print axioms infer_result_wf
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
