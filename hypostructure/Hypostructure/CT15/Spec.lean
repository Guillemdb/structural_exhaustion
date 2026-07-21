import Hypostructure.Core.Prelude

/-!
# CT15 target-relative rank specification

The specification contains only primitive semantics.  Coordinate schedules,
rank computations, charge ledgers, comparisons, and branches are owned by the
executor and never supplied as completed application outputs.
-/

namespace Hypostructure.CT15

universe uPrevious uCoordinate

/-- Domain-neutral target-relative rank semantics over one literal
predecessor ledger.  The coordinate carrier may depend on that predecessor,
so CT15 never needs an ambient finite universe. -/
structure Spec (Previous : Type uPrevious) where
  Coordinate : Previous -> Type uCoordinate
  TargetDependent : (previous : Previous) -> Coordinate previous -> Prop
  charge : (previous : Previous) -> Coordinate previous -> Nat
  capacity : Previous -> Nat

end Hypostructure.CT15
