import Hypostructure.Core.Prelude

/-!
# CT9 exact label-fibre specification

CT9 partitions the exact item schedule owned by its literal predecessor into
an authored finite label family.  This specification contains only primitive
label and capacity semantics.  It contains no finite item carrier, partition,
route, or terminal data.
-/

namespace Hypostructure.CT9

universe uPrevious uItem uLabel

/-- Domain-neutral label and fibre-capacity semantics. -/
structure Spec (Previous : Type uPrevious) where
  Item : Previous -> Type uItem
  Label : Previous -> Type uLabel
  label : (previous : Previous) -> Item previous -> Label previous
  capacity : (previous : Previous) -> Label previous -> Nat

end Hypostructure.CT9
