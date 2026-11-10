import EPL.Examples
import EPL.Properties.Annotations
import EPL.Properties.Erasure
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

end EPL.Headlines
