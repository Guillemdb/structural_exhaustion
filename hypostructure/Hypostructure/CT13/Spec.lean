import Hypostructure.Core.Prelude

/-!
# CT13 tiered-resource specification

The specification contains only primitive semantics.  Candidate orders and
all fallback schedules belong to the incoming residual and are supplied by
the executable capability as typed ledger queries.
-/

namespace Hypostructure.CT13

universe uPrevious uPayer uObstruction uResource

/-- Domain-neutral semantics for primary eligibility, fallback cost, resource
identity, charge, and demand. -/
structure Spec (Previous : Type uPrevious) where
  Payer : Previous -> Type uPayer
  Obstruction : Previous -> Type uObstruction
  Resource : Previous -> Type uResource
  Eligible : (previous : Previous) -> Payer previous -> Prop
  obstructionCost : (previous : Previous) -> Obstruction previous -> Nat
  payerResource : (previous : Previous) -> Payer previous -> Resource previous
  charge : (previous : Previous) -> Payer previous -> Nat
  demand : Previous -> Nat

end Hypostructure.CT13
