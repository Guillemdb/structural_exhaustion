import Hypostructure.Core.Prelude

/-!
# CT6 ordered-activity specification

CT6 inspects a predecessor-owned ordered family and selects its first failed
local condition.  This specification contains only local semantics; the
ordered family, branch choice, ledger, and routing are framework-owned.
-/

namespace Hypostructure.CT6

universe uPrevious uIndex uData

/-- Domain-neutral local failure and contribution semantics. -/
structure Spec (Previous : Type uPrevious) where
  Index : Previous -> Type uIndex
  FailureData : (previous : Previous) -> Index previous -> Type uData
  Failure : (previous : Previous) -> Index previous -> Prop
  failureData : (previous : Previous) -> (index : Index previous) ->
    Failure previous index -> FailureData previous index
  contribution : (previous : Previous) -> Index previous -> Nat

end Hypostructure.CT6
