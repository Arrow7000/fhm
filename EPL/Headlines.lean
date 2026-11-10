import EPL.Examples
import EPL.AnnotationAllocationTests
import EPL.Properties.AnnotationAllocation
import EPL.Properties.Annotations
import EPL.Properties.Erasure
import EPL.Properties.InferenceSafety
import EPL.Properties.InferenceModelAnnotations
import EPL.Properties.InferenceModelProjection
import EPL.Properties.Regular
import EPL.Properties.RigidWeakening
import EPL.Properties.RuntimeRegular
import EPL.Properties.RuntimeSafety
import EPL.Properties.SourceScope
import EPL.Properties.UnificationScope
import EPL.Properties.UnificationSound
import EPL.UnificationTests

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

end EPL.Headlines
