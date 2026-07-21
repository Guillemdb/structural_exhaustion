import Hypostructure.CT4.Spec
import Hypostructure.Core.Budget.Work
import Hypostructure.Core.Finite.Enumeration
import Hypostructure.Core.Residual.Query

/-!
# CT4 executable capability

Both finite schedules are typed queries into the literal predecessor.  CT4
does not enumerate an ambient demand or payer type and does not accept an
assignment, route, terminal, or completed charging ledger from its caller.
-/

namespace Hypostructure.CT4

universe uPrevious uDemand uPayer

/-- Worst-case primitive decisions for the prescribed CT4 machine.

The two product terms respectively charge canonical payer searches and fibre
construction.  The remaining terms charge availability, overload, and the
final capacity comparison. -/
def localCheckBound {Demand : Type uDemand} {Payer : Type uPayer}
    (demands : Core.Finite.Enumeration Demand)
    (payers : Core.Finite.Enumeration Payer) : Nat :=
  2 * demands.card * payers.card + demands.card + payers.card + 1

/-- Minimal author-facing CT4 capability. -/
structure Capability {Previous : Type uPrevious}
    (spec : Spec.{uPrevious, uDemand, uPayer} Previous) where
  demands : Core.Residual.Query Previous fun previous =>
    Core.Finite.Enumeration (spec.Demand previous)
  payers : Core.Residual.Query Previous fun previous =>
    Core.Finite.Enumeration (spec.Payer previous)
  eligibleDecidable : (previous : Previous) ->
    (demand : spec.Demand previous) -> (payer : spec.Payer previous) ->
      Decidable (spec.Eligible previous demand payer)
  inputSize : Previous -> Nat
  workCoefficient : Nat
  workDegree : Nat
  workBound : forall previous,
    localCheckBound (demands.read previous) (payers.read previous) <=
      workCoefficient * (inputSize previous + 1) ^ workDegree

namespace Capability

variable {Previous : Type uPrevious}
  {spec : Spec.{uPrevious, uDemand, uPayer} Previous}

/-- Exact residual-owned demand schedule. -/
def demandsAt (capability : Capability spec) (previous : Previous) :
    Core.Finite.Enumeration (spec.Demand previous) :=
  capability.demands.read previous

/-- Exact residual-owned payer schedule. -/
def payersAt (capability : Capability spec) (previous : Previous) :
    Core.Finite.Enumeration (spec.Payer previous) :=
  capability.payers.read previous

/-- Framework-visible polynomial envelope for the complete CT4 schedule. -/
def polynomialBudget (capability : Capability spec) :
    Core.PolynomialCheckBudget Previous where
  size := capability.inputSize
  checks := fun previous =>
    localCheckBound (capability.demandsAt previous)
      (capability.payersAt previous)
  coefficient := capability.workCoefficient
  degree := capability.workDegree
  bounded := capability.workBound

end Capability

end Hypostructure.CT4
