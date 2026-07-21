import Hypostructure.CT13.Spec
import Hypostructure.Core.Budget.Work
import Hypostructure.Core.Finite.Enumeration
import Hypostructure.Core.Residual.Query

/-!
# CT13 executable capability

The payer order, nonempty obstruction order, and every obstruction-indexed
tier-two order are read from the literal predecessor.  Applications cannot
provide a selected fallback, reconciliation ledger, outcome, or route.
-/

namespace Hypostructure.CT13

universe uPrevious uPayer uObstruction uResource

/-- A nonempty obstruction schedule with an observable first/default member.
Tie-breaking retains the earliest member of this exact order. -/
structure ObstructionSchedule (Obstruction : Type uObstruction) where
  fallbackDefault : Obstruction
  remaining : List Obstruction
  nodup : (fallbackDefault :: remaining).Nodup
  decEq : DecidableEq Obstruction

namespace ObstructionSchedule

/-- The exact nonempty obstruction enumeration. -/
def enumeration (schedule : ObstructionSchedule Obstruction) :
    Core.Finite.Enumeration Obstruction where
  values := schedule.fallbackDefault :: schedule.remaining
  nodup := schedule.nodup
  decEq := schedule.decEq

/-- Number of cost comparisons made by canonical fallback selection. -/
def comparisonCount (schedule : ObstructionSchedule Obstruction) : Nat :=
  schedule.remaining.length

@[simp] theorem default_mem (schedule : ObstructionSchedule Obstruction) :
    schedule.fallbackDefault ∈ schedule.enumeration.values := by
  simp [enumeration]

end ObstructionSchedule

/-- Sum of all inherited tier-two schedule cardinalities.  It supplies a
framework-computed envelope for whichever obstruction is selected. -/
def tierTwoCardSum {Payer : Type uPayer} {Obstruction : Type uObstruction}
    (obstructions : ObstructionSchedule Obstruction)
    (tierTwo : Obstruction -> Core.Finite.Enumeration Payer) : Nat :=
  (obstructions.enumeration.values.map fun obstruction =>
    (tierTwo obstruction).card).sum

/-- Worst-case CT13 primitive work over only predecessor-owned schedules.

The terms charge the complete primary search, fallback comparisons, pairwise
resource reconciliation, charge-ledger construction, and final comparison.
-/
def localCheckBound {Payer : Type uPayer} {Obstruction : Type uObstruction}
    (payers : Core.Finite.Enumeration Payer)
    (obstructions : ObstructionSchedule Obstruction)
    (tierTwo : Obstruction -> Core.Finite.Enumeration Payer) : Nat :=
  let total := tierTwoCardSum obstructions tierTwo
  payers.card + obstructions.comparisonCount + total * total + total + 1

/-- Minimal author-facing CT13 capability. -/
structure Capability {Previous : Type uPrevious}
    (spec : Spec.{uPrevious, uPayer, uObstruction, uResource} Previous) where
  payers : Core.Residual.Query Previous fun previous =>
    Core.Finite.Enumeration (spec.Payer previous)
  obstructions : Core.Residual.Query Previous fun previous =>
    ObstructionSchedule (spec.Obstruction previous)
  tierTwo : Core.Residual.Query Previous fun previous =>
    (obstruction : spec.Obstruction previous) ->
      Core.Finite.Enumeration (spec.Payer previous)
  eligibleDecidable : (previous : Previous) ->
    (payer : spec.Payer previous) -> Decidable (spec.Eligible previous payer)
  resourceDecidableEq : (previous : Previous) ->
    DecidableEq (spec.Resource previous)
  inputSize : Previous -> Nat
  workCoefficient : Nat
  workDegree : Nat
  workBound : forall previous,
    localCheckBound (payers.read previous) (obstructions.read previous)
      (tierTwo.read previous) <=
        workCoefficient * (inputSize previous + 1) ^ workDegree

namespace Capability

variable {Previous : Type uPrevious}
  {spec : Spec.{uPrevious, uPayer, uObstruction, uResource} Previous}

/-- Exact residual-owned tier-one payer order. -/
def payersAt (capability : Capability spec) (previous : Previous) :
    Core.Finite.Enumeration (spec.Payer previous) :=
  capability.payers.read previous

/-- Exact residual-owned nonempty obstruction order. -/
def obstructionsAt (capability : Capability spec) (previous : Previous) :
    ObstructionSchedule (spec.Obstruction previous) :=
  capability.obstructions.read previous

/-- Exact residual-owned tier-two order for one inherited obstruction. -/
def tierTwoAt (capability : Capability spec) (previous : Previous)
    (obstruction : spec.Obstruction previous) :
    Core.Finite.Enumeration (spec.Payer previous) :=
  (capability.tierTwo.read previous) obstruction

/-- Total inherited tier-two cardinality envelope. -/
def tierTwoCardSumAt (capability : Capability spec) (previous : Previous) : Nat :=
  tierTwoCardSum (capability.obstructionsAt previous)
    (capability.tierTwo.read previous)

/-- Framework-visible polynomial envelope for the prescribed CT13 machine. -/
def polynomialBudget (capability : Capability spec) :
    Core.PolynomialCheckBudget Previous where
  size := capability.inputSize
  checks := fun previous =>
    localCheckBound (capability.payersAt previous)
      (capability.obstructionsAt previous)
      (capability.tierTwo.read previous)
  coefficient := capability.workCoefficient
  degree := capability.workDegree
  bounded := capability.workBound

end Capability

end Hypostructure.CT13
