import Hypostructure.Core.Prelude

/-!
# CT4 deterministic-charging specification

CT4 assigns every demand in an inherited finite schedule to the first
eligible payer in another inherited finite schedule.  The specification owns
only the domain-neutral charging semantics; schedules, routes, and generated
states belong to the executable capability.
-/

namespace Hypostructure.CT4

universe uPrevious uDemand uPayer

/-- Domain-neutral demand, payer, weight, and capacity semantics. -/
structure Spec (Previous : Type uPrevious) where
  Demand : Previous -> Type uDemand
  Payer : Previous -> Type uPayer
  Eligible : (previous : Previous) -> Demand previous -> Payer previous -> Prop
  demandWeight : (previous : Previous) -> Demand previous -> Nat
  capacity : (previous : Previous) -> Payer previous -> Nat
  required : Previous -> Nat

end Hypostructure.CT4
