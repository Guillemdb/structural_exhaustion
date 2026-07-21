import Hypostructure.CT12.Spec
import Hypostructure.Core.Budget.Work
import Hypostructure.Core.Residual.Query

/-!
# CT12 executable capability

The initial indexed state is read from the literal predecessor.  A capability
also proves one polynomial envelope for the complete well-founded run.
-/

namespace Hypostructure.CT12

universe uPrevious uState uPeeled uDemand uTier

/-- Exact predecessor-owned state at which CT12 starts. -/
structure InitialState {Previous : Type uPrevious}
    (spec : Spec.{uPrevious, uState, uPeeled, uDemand, uTier} Previous)
    (previous : Previous) where
  load : Nat
  state : spec.State previous load

/-- Framework worst-case primitive checks for a run starting at `load`.

Every positive iteration pays four checks (saturation, peel, restoration
selection, and routing/decrease verification); exhaustion pays one final
saturation check. -/
def maximumChecks (load : Nat) : Nat :=
  4 * load + 1

/-- Minimum executable CT12 contract. -/
structure Capability {Previous : Type uPrevious}
    (spec : Spec.{uPrevious, uState, uPeeled, uDemand, uTier} Previous) where
  initial : Core.Residual.Query Previous (InitialState spec)
  inputSize : Previous -> Nat
  workCoefficient : Nat
  workDegree : Nat
  workBound : forall previous,
    maximumChecks (initial.read previous).load <=
      workCoefficient * (inputSize previous + 1) ^ workDegree

namespace Capability

variable {Previous : Type uPrevious}
  {spec : Spec.{uPrevious, uState, uPeeled, uDemand, uTier} Previous}

/-- Exact indexed state queried from one predecessor. -/
def initialAt (capability : Capability spec) (previous : Previous) :
    InitialState spec previous :=
  capability.initial.read previous

/-- Polynomial budget for the complete CT12 execution. -/
def polynomialBudget (capability : Capability spec) :
    Core.PolynomialCheckBudget Previous where
  size := capability.inputSize
  checks := fun previous => maximumChecks (capability.initialAt previous).load
  coefficient := capability.workCoefficient
  degree := capability.workDegree
  bounded := capability.workBound

end Capability

end Hypostructure.CT12
