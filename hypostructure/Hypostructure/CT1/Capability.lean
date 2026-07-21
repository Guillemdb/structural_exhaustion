import Hypostructure.CT1.Spec
import Hypostructure.Core.Budget.Work
import Hypostructure.Core.Residual.Query

/-!
# CT1 executable capability

The candidate schedule is read through a typed query from the exact incoming
ledger.  Applications provide only primitive realization decisions and a
polynomial bound for that residual-owned scan.
-/

namespace Hypostructure.CT1

universe uPrevious uCandidate

/-- Number of primitive realization checks in the complete CT1 schedule. -/
def searchCheckBound {Previous : Type uPrevious}
    (spec : Spec.{uPrevious, uCandidate} Previous)
    (schedule : Core.Residual.Query Previous fun previous =>
      Core.Finite.Enumeration (spec.Candidate previous))
    (previous : Previous) : Nat :=
  (schedule.read previous).card

/-- Minimal executable surface for exhaustive CT1 validation. -/
structure Capability {Previous : Type uPrevious}
    (spec : Spec.{uPrevious, uCandidate} Previous) where
  schedule : Core.Residual.Query Previous fun previous =>
    Core.Finite.Enumeration (spec.Candidate previous)
  realizesDecidable : (previous : Previous) ->
    (candidate : spec.Candidate previous) ->
      Decidable (spec.Realizes previous candidate)
  inputSize : Previous -> Nat
  workCoefficient : Nat
  workDegree : Nat
  workBound : forall previous,
    searchCheckBound spec schedule previous <=
      workCoefficient * (inputSize previous + 1) ^ workDegree

/-- Optional semantic bridge to an independently named public target.

Indexing the bridge by the executable capability forces both directions to
use the same typed ledger query and exact schedule as the CT1 runner.
-/
structure TargetBridge {Previous : Type uPrevious}
    (spec : Spec.{uPrevious, uCandidate} Previous)
    (capability : Capability spec) (PublicTarget : Previous -> Prop) : Prop where
  equivalent : forall previous,
    PublicTarget previous <->
      Target spec previous (capability.schedule.read previous)

namespace Capability

/-- The exact schedule retrieved from one literal predecessor. -/
def scheduleAt {Previous : Type uPrevious}
    {spec : Spec.{uPrevious, uCandidate} Previous}
    (capability : Capability spec) (previous : Previous) :
    Core.Finite.Enumeration (spec.Candidate previous) :=
  capability.schedule.read previous

/-- Framework-visible worst-case polynomial work budget. -/
def polynomialBudget {Previous : Type uPrevious}
    {spec : Spec.{uPrevious, uCandidate} Previous}
    (capability : Capability spec) :
    Core.PolynomialCheckBudget Previous where
  size := capability.inputSize
  checks := searchCheckBound spec capability.schedule
  coefficient := capability.workCoefficient
  degree := capability.workDegree
  bounded := capability.workBound

end Capability

end Hypostructure.CT1
