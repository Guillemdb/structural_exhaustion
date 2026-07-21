import Hypostructure.Core.Prelude

/-!
# CT14 aggregate-mass specification

The specification contains only primitive member semantics.  The finite
member family is deliberately absent: it belongs to the incoming residual
and is retrieved by the executable capability.
-/

namespace Hypostructure.CT14

universe uPrevious uMember uLabel

/-- Domain-neutral mass, optional-capacity, and optional-label semantics. -/
structure Spec (Previous : Type uPrevious) where
  Member : Previous -> Type uMember
  Label : Previous -> Type uLabel
  memberLowerMass : (previous : Previous) -> Member previous -> Nat
  memberCapacity : (previous : Previous) -> Member previous -> Option Nat
  memberLabel : (previous : Previous) -> Member previous -> Option (Label previous)

end Hypostructure.CT14
