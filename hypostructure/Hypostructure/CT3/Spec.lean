import Hypostructure.Core.Response.FiniteTable
import Hypostructure.Core.Finite.Accounting

/-!
# CT3 exact response-compression specification

CT3 compares representatives only through an exact finite coordinate schedule
owned by its literal predecessor.  This file declares semantic operations; it
does not contain schedules, branch choices, or execution outputs.
-/

namespace Hypostructure.CT3

universe uPrevious uRepresentative uContext uCoordinate uValue uCandidate uRow

/-- Domain-neutral semantics for exact response compression. -/
structure Spec (Previous : Type uPrevious) where
  Representative : Type uRepresentative
  Candidate : Type uCandidate
  Row : Type uRow
  system : Core.Response.System.{uRepresentative, uContext, uCoordinate, uValue}
    Representative
  semantics : Core.Response.TargetSemantics system
  candidatePiece : Candidate -> Representative
  rowPiece : Row -> Representative
  rowResponse : Row -> system.Coordinate -> system.Value
  Admissible : Previous -> Representative -> Candidate -> Prop
  StrictlySmaller : Previous -> Representative -> Candidate -> Prop

namespace Spec

/-- The ordered pair used by Core when comparing a source with a replacement. -/
def representatives {Previous : Type uPrevious}
    (spec : Spec.{uPrevious, uRepresentative, uContext, uCoordinate, uValue,
      uCandidate, uRow} Previous)
    (source replacement : spec.Representative) :
    Core.Response.Representatives spec.Representative where
  source := source
  replacement := replacement

end Spec

end Hypostructure.CT3
