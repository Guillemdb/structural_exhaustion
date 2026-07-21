import Hypostructure.CT14.Spec
import Hypostructure.Core.Budget.Work
import Hypostructure.Core.Finite.Enumeration
import Hypostructure.Core.Residual.Query

/-!
# CT14 executable capability

The exact member schedule is a typed read from the literal predecessor.  No
ambient member universe, label assignment, subset family, or completed
ledger is accepted from an application.
-/

namespace Hypostructure.CT14

universe uPrevious uMember uLabel

/-- Worst-case primitive work: one lower-mass pass, two complete optional-data
scans, and one aggregate comparison. -/
def localCheckBound {Member : Type uMember}
    (members : Core.Finite.Enumeration Member) : Nat :=
  3 * members.card + 1

/-- Minimal executable CT14 surface. -/
structure Capability {Previous : Type uPrevious}
    (spec : Spec.{uPrevious, uMember, uLabel} Previous) where
  members : Core.Residual.Query Previous fun previous =>
    Core.Finite.Enumeration (spec.Member previous)
  labelDecidableEq : (previous : Previous) -> DecidableEq (spec.Label previous)
  inputSize : Previous -> Nat
  workCoefficient : Nat
  workDegree : Nat
  workBound : forall previous,
    localCheckBound (members.read previous) <=
      workCoefficient * (inputSize previous + 1) ^ workDegree

namespace Capability

/-- Exact residual-owned member schedule at one predecessor. -/
def membersAt {Previous : Type uPrevious}
    {spec : Spec.{uPrevious, uMember, uLabel} Previous}
    (capability : Capability spec) (previous : Previous) :
    Core.Finite.Enumeration (spec.Member previous) :=
  capability.members.read previous

/-- Framework-visible polynomial work envelope. -/
def polynomialBudget {Previous : Type uPrevious}
    {spec : Spec.{uPrevious, uMember, uLabel} Previous}
    (capability : Capability spec) :
    Core.PolynomialCheckBudget Previous where
  size := capability.inputSize
  checks := fun previous => localCheckBound (capability.membersAt previous)
  coefficient := capability.workCoefficient
  degree := capability.workDegree
  bounded := capability.workBound

end Capability

end Hypostructure.CT14
