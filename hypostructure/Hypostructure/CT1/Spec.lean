import Hypostructure.Core.Finite.Enumeration

/-!
# CT1 target-realization specification

CT1 reasons about candidates already listed by an incoming residual.  The
specification gives those candidates their mathematical meaning; it neither
owns a schedule nor chooses an execution outcome.
-/

namespace Hypostructure.CT1

universe uPrevious uCandidate

/-- Domain-neutral realization semantics over one literal predecessor stage. -/
structure Spec (Previous : Type uPrevious) where
  Candidate : Previous -> Type uCandidate
  Realizes : (previous : Previous) -> Candidate previous -> Prop

/-- The exact target represented by one residual-owned candidate schedule. -/
def Target {Previous : Type uPrevious} (spec : Spec.{uPrevious, uCandidate} Previous)
    (previous : Previous)
    (schedule : Core.Finite.Enumeration (spec.Candidate previous)) : Prop :=
  Exists fun candidate =>
    candidate ∈ schedule.values ∧ spec.Realizes previous candidate

end Hypostructure.CT1
