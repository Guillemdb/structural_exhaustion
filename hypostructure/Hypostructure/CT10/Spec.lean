import Hypostructure.Core.Finite.Enumeration

/-!
# CT10 finite-refinement specification

CT10 classifies only local data already carried by its literal predecessor.
The specification gives those data and classes their semantic meaning; it
does not own either finite schedule and it cannot select an execution branch.
-/

namespace Hypostructure.CT10

universe uPrevious uDatum uClass uPromotion

/-- Domain-neutral semantics for one finite refinement classification. -/
structure Spec (Previous : Type uPrevious) where
  Datum : Previous -> Type uDatum
  Class : Previous -> Type uClass
  Promotion : Previous -> Type uPromotion
  classOf : (previous : Previous) -> Datum previous -> Class previous
  Direct : (previous : Previous) -> Class previous -> Prop
  promote : (previous : Previous) -> Class previous -> Promotion previous

end Hypostructure.CT10
