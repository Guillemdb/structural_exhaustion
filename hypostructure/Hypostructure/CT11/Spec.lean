import Hypostructure.Core.Prelude

/-!
# CT11 finite-sum localization specification

CT11 localizes a strict negative sum on an exact predecessor-owned finite
family.  This specification contains only the local admissibility and additive
budget semantics.  The family, negative-total certificate, scans, routing,
ledger update, and generated residuals belong to the framework.
-/

namespace Hypostructure.CT11

universe uPrevious uCell

/-- Domain-neutral local semantics for additive-deficit localization. -/
structure Spec (Previous : Type uPrevious) where
  Cell : Previous -> Type uCell
  Admissible : (previous : Previous) -> Cell previous -> Prop
  localBudget : (previous : Previous) -> Cell previous -> Int

end Hypostructure.CT11
