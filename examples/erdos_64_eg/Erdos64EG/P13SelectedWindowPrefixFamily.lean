import Erdos64EG.CT10P13MultiScaleCurvature
import StructuralExhaustion.Core.FinitePrefixExtensionFamily

namespace Erdos64EG.Internal

open StructuralExhaustion

universe u uState uFailure

/-!
# Exact selected-window lift of the symbolic prefix runner

This is the first finite producer needed at the node-[160] repair boundary.
It runs one graph/application-owned prefix machine for every member of the
exact CT12-selected `P₁₃` packing, in that packing's deterministic order, and
returns the first local obstruction or complete symbolic ledgers for every
selected window.

The family is indexed by the exact node-[21]
`VerifiedP13MultiScaleCurvaturePrefix`.  It does not construct the still-
missing pointwise graph completion machine and makes no claim about Boolean
realization, an omitted assignment, entropy, or commuting gluing.
-/

/-- One member of the exact CT12-selected packing, with membership retained
in its type.  This definition is local to the symbolic-prefix producer and
does not use the older Boolean-realization classifier. -/
abbrev P13PrefixSelectedWindow
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :=
  {window : InducedP13Window ctx // window ∈ p13Windows ctx}

/-- The CT12 packing order lifted to the exact membership subtype. -/
noncomputable def p13PrefixSelectedWindows
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    List (P13PrefixSelectedWindow ctx) :=
  (p13Windows ctx).attach

theorem p13PrefixSelectedWindows_length
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    (p13PrefixSelectedWindows ctx).length = p13 ctx := by
  rw [p13PrefixSelectedWindows, List.length_attach]
  simp [p13Windows, p13,
    Graph.InducedPathPacking.packingNumber,
    Graph.InducedPathPacking.windows]

/-- The exact 91-coordinate node-[21] barrier order. -/
def p13PrefixCoordinateSchedule : List P13BarrierIndex :=
  p13BarrierClassification.classes.orderedValues

theorem p13PrefixCoordinateSchedule_length :
    p13PrefixCoordinateSchedule.length = 91 := by
  rw [p13PrefixCoordinateSchedule, FinEnum.orderedValues_length]
  change p13BarrierClassification.classCount = 91
  exact p13Barrier_class_count

/-- Pointwise graph/application producer interface.  A later node-[160]
module must construct this family from actual completion semantics; callers
cannot select a hot/cold Boolean or a family outcome. -/
structure P13PointwisePrefixMachineFamily
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (_previous : VerifiedP13MultiScaleCurvaturePrefix ctx) where
  machine : P13PrefixSelectedWindow ctx →
    Core.FinitePrefixExtension.Machine.{0, uState, uFailure} P13BarrierIndex

namespace P13PointwisePrefixMachineFamily

variable {ctx : Core.MinimalCounterexampleContext
  PackedProblem.{u} PackedTarget.{u}}
variable {previous : VerifiedP13MultiScaleCurvaturePrefix ctx}

/-- Exact exhaustive output over the CT12-selected family. -/
abbrev Outcome
    (family : P13PointwisePrefixMachineFamily.{u, uState, uFailure}
      ctx previous) :=
  Core.FinitePrefixExtensionFamily.Outcome family.machine
    (fun _ => p13PrefixCoordinateSchedule) (p13PrefixSelectedWindows ctx)

/-- Run the pointwise prefix machine on every selected window until the first
obstruction, or retain complete ledgers for the whole selected family. -/
noncomputable def run
    (family : P13PointwisePrefixMachineFamily.{u, uState, uFailure}
      ctx previous) :
    family.Outcome :=
  Core.FinitePrefixExtensionFamily.run family.machine
    (fun _ => p13PrefixCoordinateSchedule) (p13PrefixSelectedWindows ctx)

/-- The exact first-obstruction/all-complete split.  Both alternatives are
produced by the runner; neither is supplied by a caller. -/
theorem run_exhaustive
    (family : P13PointwisePrefixMachineFamily.{u, uState, uFailure}
      ctx previous) :
    (∃ failure, family.run =
        Core.FinitePrefixExtensionFamily.Outcome.firstObstruction failure) ∨
      (∃ ledgers, family.run =
        Core.FinitePrefixExtensionFamily.Outcome.allComplete ledgers) :=
  Core.FinitePrefixExtensionFamily.run_exhaustive family.machine
    (fun _ => p13PrefixCoordinateSchedule) (p13PrefixSelectedWindows ctx)

/-- Full visible-work envelope: 91 pointwise extension calls per selected
window.  A first obstruction may terminate before this envelope is reached. -/
noncomputable def visibleCheckEnvelope
    (family : P13PointwisePrefixMachineFamily.{u, uState, uFailure}
      ctx previous) : Nat :=
  Core.FinitePrefixExtensionFamily.visibleCheckEnvelope
    (fun _ : P13PrefixSelectedWindow ctx => p13PrefixCoordinateSchedule)
    (p13PrefixSelectedWindows ctx)

theorem visibleCheckEnvelope_exact
    (family : P13PointwisePrefixMachineFamily.{u, uState, uFailure}
      ctx previous) :
    family.visibleCheckEnvelope = 91 * p13 ctx := by
  simp [visibleCheckEnvelope,
    Core.FinitePrefixExtensionFamily.visibleCheckEnvelope,
    p13PrefixCoordinateSchedule_length,
    p13PrefixSelectedWindows_length, Nat.mul_comm]

end P13PointwisePrefixMachineFamily

end Erdos64EG.Internal
