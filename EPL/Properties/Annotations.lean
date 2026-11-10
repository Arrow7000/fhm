import EPL.Core

namespace EPL
namespace Template.Fits

/-- Two occurrences of the same local named hole in one assignment have the
same type. -/
theorem named_eq
    (first : Template.Fits holes (.named name) firstTy)
    (second : Template.Fits holes (.named name) secondTy) :
    firstTy = secondTy := by
  cases first with
  | named firstLookup =>
      cases second with
      | named secondLookup =>
          exact Option.some.inj (firstLookup.symm.trans secondLookup)

end Template.Fits
end EPL
