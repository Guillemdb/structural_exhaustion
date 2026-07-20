import Erdos64EG.Future.P13SameWindowComponentBoundarySchedule
import StructuralExhaustion.Graph.InducedPathComponentD1D3Observation

namespace Erdos64EG.Internal

open StructuralExhaustion
open StructuralExhaustion.Graph

universe u

/-!
# Node [173]: one short-branch component D1--D3 observation

This adapter consumes the exact node-`[170]` first-transition input and
projects its two literal boundary stubs and computed BFS connector to one
normalized D1--D3 state.  The local-coordinate type is empty, so the result
explicitly stops at `MissingD4D7Reconstruction`.

It does not join the mutually exclusive node-`[163]` long branch and proves no
repetition, CT3 compression, cold-family membership, Boolean realization,
target closure, or density statement.
-/

variable {ctx : Core.MinimalCounterexampleContext
  PackedProblem.{u} PackedTarget.{u}}
variable {previous : VerifiedP13MultiScaleCurvaturePrefix ctx}
variable {window : P13ActualSelectedWindow ctx}
variable {fork : P13ActualAttachmentColdFork ctx previous window}
variable {quiet : P13SameWindowQuietOutput fork}
variable {short : P13SameWindowComputedShort fork quiet}
variable {input : P13SameWindowNormalizedBoundaryInput (short := short)}
variable {computed : P13SameWindowComputedNormalizedReturnBoundary input}

abbrev P13SameWindowComponentD1D3Residual
    (transition : P13SameWindowFirstTransitionBoundaryInput computed) :=
  InducedPathComponentD1D3Observation.OneStateResidual transition.graphInput
    PowerOfTwoLength powerOfTwoLengthDecidable

/-- Execute the generic one-state projection on the exact node-`[170]` data. -/
noncomputable def runP13SameWindowComponentD1D3Observation
    (transition : P13SameWindowFirstTransitionBoundaryInput computed) :
    P13SameWindowComponentD1D3Residual transition :=
  InducedPathComponentD1D3Observation.run transition.graphInput
    PowerOfTwoLength powerOfTwoLengthDecidable

theorem p13SameWindowComponentD1D3_exact_state
    (transition : P13SameWindowFirstTransitionBoundaryInput computed) :
    (runP13SameWindowComponentD1D3Observation transition).value =
      InducedPathComponentD1D3Observation.state transition.graphInput
        PowerOfTwoLength powerOfTwoLengthDecidable :=
  (runP13SameWindowComponentD1D3Observation transition).valueExact

theorem p13SameWindowComponentD1D3_exact_node170_data
    (transition : P13SameWindowFirstTransitionBoundaryInput computed) :
    InducedPathComponentD1D3Observation.data transition.graphInput =
      transition.result := rfl

theorem p13SameWindowComponentD1D3_missing_d4_d7
    (transition : P13SameWindowFirstTransitionBoundaryInput computed) :
    Nonempty (InducedPathColdSkeleton.TwoStubComponent.MissingD4D7Reconstruction
      transition.result
      (InducedPathComponentD1D3Observation.canonicalPath
        transition.graphInput)) :=
  ⟨(runP13SameWindowComponentD1D3Observation transition).missing⟩

theorem p13SameWindowComponentD1D3_targetResponse
    (transition : P13SameWindowFirstTransitionBoundaryInput computed)
    (offset : Core.FixedTwoBoundaryCutState.TargetOffset) :
    (runP13SameWindowComponentD1D3Observation transition).value.targetResponse
        offset =
      decide (PowerOfTwoLength
        (transition.componentPath.length + offset.val)) :=
  InducedPathComponentD1D3Observation.targetResponse_eq
    transition.graphInput PowerOfTwoLength powerOfTwoLengthDecidable offset

theorem p13SameWindowComponentD1D3_visibleChecks_eq
    (transition : P13SameWindowFirstTransitionBoundaryInput computed) :
    InducedPathComponentD1D3Observation.visibleChecks transition.graphInput =
      2 * ctx.G.object.input.vertices.card + 13 :=
  InducedPathComponentD1D3Observation.visibleChecks_eq transition.graphInput

theorem p13SameWindowComponentD1D3_visibleChecks_linear
    (transition : P13SameWindowFirstTransitionBoundaryInput computed) :
    InducedPathComponentD1D3Observation.visibleChecks transition.graphInput ≤
      15 * (ctx.G.object.input.vertices.card + 1) :=
  InducedPathComponentD1D3Observation.visibleChecks_linear
    transition.graphInput

end Erdos64EG.Internal
