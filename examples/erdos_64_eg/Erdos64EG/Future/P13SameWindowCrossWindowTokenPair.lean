import Erdos64EG.Future.P13SameWindowPackedOwnerChange
import StructuralExhaustion.Routes.InducedPathCrossWindowTokenPair

namespace Erdos64EG.Internal

open StructuralExhaustion

universe u

/-!
# Node [171]: exact cross-window token-pair residual

This thin adapter consumes the exact computed node-`[169]` result and applies
the reusable zero-check route.  Its output is the terminal residual of the
computed all-inside branch.  It asserts no repeated owner, second connector,
cycle, cold-family, demand, capacity, successor, target, or density conclusion.
-/

variable {ctx : Core.MinimalCounterexampleContext
  PackedProblem.{u} PackedTarget.{u}}
variable {previous : VerifiedP13MultiScaleCurvaturePrefix ctx}
variable {window : P13ActualSelectedWindow ctx}
variable {fork : P13ActualAttachmentColdFork ctx previous window}
variable {quiet : P13SameWindowQuietOutput fork}
variable {short : P13SameWindowComputedShort fork quiet}
variable {boundaryInput : P13SameWindowNormalizedBoundaryInput (short := short)}
variable {computed : P13SameWindowComputedNormalizedReturnBoundary boundaryInput}

/-- Exact terminal node-`[171]` residual, indexed by the complete node-`[169]` run. -/
abbrev P13SameWindowCrossWindowTokenPair
    {inside : P13SameWindowComputedAllInside computed}
    (cross : P13SameWindowFirstCrossWindow inside) :=
  Routes.InducedPathCrossWindowTokenPair.CrossWindowTokenPair cross.crossing

/-- Execute only the reusable bookkeeping route. -/
noncomputable def runP13SameWindowCrossWindowTokenPair
    {inside : P13SameWindowComputedAllInside computed}
    (cross : P13SameWindowFirstCrossWindow inside) :
    P13SameWindowCrossWindowTokenPair cross :=
  Routes.InducedPathCrossWindowTokenPair.route cross.crossing

theorem runP13SameWindowCrossWindowTokenPair_source_exact
    {inside : P13SameWindowComputedAllInside computed}
    (cross : P13SameWindowFirstCrossWindow inside) :
    (runP13SameWindowCrossWindowTokenPair cross).leftToken =
        cross.crossing.leftToken ∧
      (runP13SameWindowCrossWindowTokenPair cross).rightToken =
        cross.crossing.rightToken :=
  ⟨(runP13SameWindowCrossWindowTokenPair cross).leftTokenExact,
    (runP13SameWindowCrossWindowTokenPair cross).rightTokenExact⟩

theorem p13SameWindowCrossWindowTokenPair_additionalChecks_eq_zero :
    Routes.InducedPathCrossWindowTokenPair.additionalChecks = 0 :=
  Routes.InducedPathCrossWindowTokenPair.additionalChecks_eq_zero

end Erdos64EG.Internal
