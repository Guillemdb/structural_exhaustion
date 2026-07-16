import Erdos64EG.P13SameWindowNormalizedReturnBoundary
import StructuralExhaustion.Graph.InducedPathColdSkeletonBoundaryTransition

namespace Erdos64EG.Internal

open StructuralExhaustion
open StructuralExhaustion.Graph
open StructuralExhaustion.Graph.InducedPathWindowLedger

universe u

/-!
# Node [168]: normalized-return packed-support transition

This thin adapter consumes one exact computed node-`[167]` normalized return.
It views that proof-carrying return in the ambient graph and invokes the
generic first-transition scan against the union of *all* ambient-cubic
selected-window supports.

The output is exactly either full containment of this one return support in
that union, or the first oriented crossing together with its literal boundary
stub, outside endpoint, and induced-remainder component.  It constructs no
successor and makes no claim that the extracted window lies in a manuscript
cold subfamily.
-/

variable {ctx : Core.MinimalCounterexampleContext
  PackedProblem.{u} PackedTarget.{u}}
variable {previous : VerifiedP13MultiScaleCurvaturePrefix ctx}
variable {window : P13ActualSelectedWindow ctx}
variable {fork : P13ActualAttachmentColdFork ctx previous window}
variable {quiet : P13SameWindowQuietOutput fork}
variable {short : P13SameWindowComputedShort fork quiet}

/-- Exact proof-carrying output of node `[167]`. -/
structure P13SameWindowComputedNormalizedReturnBoundary
    (input : P13SameWindowNormalizedBoundaryInput (short := short)) where
  result : P13SameWindowNormalizedReturnBoundary input
  runExact : runP13SameWindowNormalizedReturnBoundary input = result

namespace P13SameWindowComputedNormalizedReturnBoundary

variable {input : P13SameWindowNormalizedBoundaryInput (short := short)}

theorem support_bounded
    (computed : P13SameWindowComputedNormalizedReturnBoundary input) :
    computed.result.selectedReturn.path.support.length ≤
      p13ColdD1D3BaseThreshold := by
  rw [← computed.runExact]
  exact runP13SameWindowNormalizedReturnBoundary_support_bounded input

/-- Ambient view of the one selected deleted-edge return. -/
noncomputable def ambientPath
    (computed : P13SameWindowComputedNormalizedReturnBoundary input) :
    ctx.G.object.graph.Walk quiet.stub.neighbor
      (selectedWindow ctx.G.object quiet.stub.window quiet.stub.position) :=
  computed.result.selectedReturn.path.mapLe
    (ctx.G.object.graph.deleteEdges_le {quiet.stub.dart.edge})

theorem ambientPath_isPath
    (computed : P13SameWindowComputedNormalizedReturnBoundary input) :
    computed.ambientPath.IsPath :=
  computed.result.selectedReturn.isPath.mapLe _

/-- The return endpoint is in the ambient-cubic deleted union because the
predecessor's selected stub carries both its exact window and cubicity proof. -/
theorem endpoint_mem_deletedWindowVertices
    (_computed : P13SameWindowComputedNormalizedReturnBoundary input) :
    selectedWindow ctx.G.object quiet.stub.window quiet.stub.position ∈
      InducedPathColdSkeleton.deletedWindowVertices ctx.G.object := by
  classical
  simp only [InducedPathColdSkeleton.deletedWindowVertices,
    Finset.mem_biUnion]
  refine ⟨quiet.stub.window, Finset.mem_univ _, ?_⟩
  simp only [quiet.stub.cubic, if_pos,
    InducedPathPacking.mem_support_iff]
  exact ⟨quiet.stub.position, rfl⟩

/-- Exact generic node-`[168]` input, assembled only from node `[167]`. -/
noncomputable def graphInput
    (computed : P13SameWindowComputedNormalizedReturnBoundary input) :
    InducedPathColdSkeletonBoundaryTransition.Input ctx.G.object where
  start := quiet.stub.neighbor
  finish := selectedWindow ctx.G.object quiet.stub.window quiet.stub.position
  path := computed.ambientPath
  isPath := computed.ambientPath_isPath
  finalInside := computed.endpoint_mem_deletedWindowVertices

theorem graphInput_path_length
    (computed : P13SameWindowComputedNormalizedReturnBoundary input) :
    computed.graphInput.path.length =
      computed.result.selectedReturn.path.length := by
  change (computed.result.selectedReturn.path.map _).length = _
  rw [SimpleGraph.Walk.length_map]

theorem graphInput_length_le_Qbase
    (computed : P13SameWindowComputedNormalizedReturnBoundary input) :
    computed.graphInput.path.length ≤ p13ColdD1D3BaseThreshold := by
  have bounded := computed.support_bounded
  rw [SimpleGraph.Walk.length_support] at bounded
  rw [computed.graphInput_path_length]
  omega

end P13SameWindowComputedNormalizedReturnBoundary

/-- Exact dependent result of node `[168]`. -/
abbrev P13SameWindowNormalizedReturnPackedSupportTransition
    {input : P13SameWindowNormalizedBoundaryInput (short := short)}
    (computed : P13SameWindowComputedNormalizedReturnBoundary input) :=
  InducedPathColdSkeletonBoundaryTransition.Result computed.graphInput

/-- Execute only the graph-owned one-path transition scan. -/
noncomputable def runP13SameWindowNormalizedReturnPackedSupportTransition
    {input : P13SameWindowNormalizedBoundaryInput (short := short)}
    (computed : P13SameWindowComputedNormalizedReturnBoundary input) :
    P13SameWindowNormalizedReturnPackedSupportTransition computed :=
  InducedPathColdSkeletonBoundaryTransition.run computed.graphInput

/-- The two results are exhaustive, with the first-transition branch retaining
the exact first-hit, oriented consecutive vertices, boundary stub, outside
endpoint, and component produced by the generic runner. -/
theorem runP13SameWindowNormalizedReturnPackedSupportTransition_exhaustive
    {input : P13SameWindowNormalizedBoundaryInput (short := short)}
    (computed : P13SameWindowComputedNormalizedReturnBoundary input) :
    (∃ supportSubset,
      runP13SameWindowNormalizedReturnPackedSupportTransition computed =
        .allInside supportSubset) ∨
    (∃ hit crossing stub stubExact endpoint endpointExact component componentExact,
      runP13SameWindowNormalizedReturnPackedSupportTransition computed =
        .firstTransition hit crossing stub stubExact endpoint endpointExact
          component componentExact) :=
  InducedPathColdSkeletonBoundaryTransition.run_exhaustive computed.graphInput

/-- Exact node-local work identity. -/
theorem p13SameWindowNormalizedReturnPackedSupportTransition_visibleChecks_eq
    {input : P13SameWindowNormalizedBoundaryInput (short := short)}
    (computed : P13SameWindowComputedNormalizedReturnBoundary input) :
    InducedPathColdSkeletonBoundaryTransition.visibleChecks computed.graphInput =
      13 * packingNumber ctx.G.object * ctx.G.object.input.vertices.card +
        13 * packingNumber ctx.G.object +
        26 * packingNumber ctx.G.object * computed.graphInput.path.length :=
  InducedPathColdSkeletonBoundaryTransition.visibleChecks_eq computed.graphInput

/-- Conservative locally polynomial bound using the inherited `Qbase` length
bound and no ambient graph/path/coloring/context universe. -/
theorem p13SameWindowNormalizedReturnPackedSupportTransition_visibleChecks_le
    {input : P13SameWindowNormalizedBoundaryInput (short := short)}
    (computed : P13SameWindowComputedNormalizedReturnBoundary input) :
    InducedPathColdSkeletonBoundaryTransition.visibleChecks computed.graphInput ≤
      ctx.G.object.input.vertices.card ^ 2 +
        (2 * p13ColdD1D3BaseThreshold + 1) *
          ctx.G.object.input.vertices.card :=
  InducedPathColdSkeletonBoundaryTransition.visibleChecks_le_square_add_linear
    computed.graphInput p13ColdD1D3BaseThreshold
      computed.graphInput_length_le_Qbase

end Erdos64EG.Internal
