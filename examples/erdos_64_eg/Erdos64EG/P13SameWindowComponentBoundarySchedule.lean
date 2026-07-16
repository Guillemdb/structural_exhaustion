import Erdos64EG.P13SameWindowNormalizedReturnPackedSupportTransition
import Erdos64EG.CT2BridgeContraction
import StructuralExhaustion.Graph.InducedPathComponentBoundarySchedule

namespace Erdos64EG.Internal

open StructuralExhaustion
open StructuralExhaustion.Graph

universe u

/-!
# Node [170]: component boundary schedule

This adapter consumes the exact first-transition constructor of node `[168]`.
It retains every dependent equality from that constructor and supplies only
the already verified all-darts non-bridge theorem.  The graph layer constructs
the second boundary stub, the stored incident-stub schedule and successor,
and a shortest simple path in the returned component.

The boundary universe is still the union of all ambient-cubic selected
windows.  No cold-family membership or lexicographically first path is
claimed.
-/

variable {ctx : Core.MinimalCounterexampleContext
  PackedProblem.{u} PackedTarget.{u}}
variable {previous : VerifiedP13MultiScaleCurvaturePrefix ctx}
variable {window : P13ActualSelectedWindow ctx}
variable {fork : P13ActualAttachmentColdFork ctx previous window}
variable {quiet : P13SameWindowQuietOutput fork}
variable {short : P13SameWindowComputedShort fork quiet}
variable {input : P13SameWindowNormalizedBoundaryInput (short := short)}

/-- The exact dependent node-`[168]` first-transition branch. -/
structure P13SameWindowFirstTransitionBoundaryInput
    (computed : P13SameWindowComputedNormalizedReturnBoundary input) where
  hit : Core.FiniteSearch.FirstHit computed.graphInput.edgeOrder
    computed.graphInput.TransitionAt
  crossing : InducedPathColdSkeletonBoundaryTransition.OrientedCrossing
    computed.graphInput hit
  stub : InducedPathColdSkeleton.BoundaryStub ctx.G.object
  stubExact : stub = crossing.boundaryStub
  endpoint : InducedPathColdSkeleton.OutsideVertex ctx.G.object
  endpointExact : endpoint = stub.endpoint
  component : (InducedPathColdSkeleton.outsideObject ctx.G.object).graph.ConnectedComponent
  componentExact : component = InducedPathColdSkeleton.component stub
  runExact : runP13SameWindowNormalizedReturnPackedSupportTransition computed =
    .firstTransition hit crossing stub stubExact endpoint endpointExact
      component componentExact

namespace P13SameWindowFirstTransitionBoundaryInput

variable {computed : P13SameWindowComputedNormalizedReturnBoundary input}

noncomputable def graphInput
    (transition : P13SameWindowFirstTransitionBoundaryInput computed) :
    InducedPathComponentBoundarySchedule.Input ctx.G.object where
  anchor := transition.stub
  notBridge := dart_not_bridge ctx _

noncomputable def result
    (transition : P13SameWindowFirstTransitionBoundaryInput computed) :=
  InducedPathComponentBoundarySchedule.twoStubComponent transition.graphInput

noncomputable def componentPath
    (transition : P13SameWindowFirstTransitionBoundaryInput computed) :=
  InducedPathComponentBoundarySchedule.componentPath
    transition.graphInput

theorem anchor_is_exact_node168_stub
    (transition : P13SameWindowFirstTransitionBoundaryInput computed) :
    transition.result.anchor = transition.stub := rfl

theorem successor_distinct_and_same_returned_component
    (transition : P13SameWindowFirstTransitionBoundaryInput computed) :
    transition.result.successor ≠ transition.stub ∧
      InducedPathColdSkeleton.component transition.result.successor =
        transition.component := by
  constructor
  · exact transition.result.distinct
  · rw [transition.componentExact]
    exact transition.result.sameComponent

theorem computed_exit_and_schedule
    (transition : P13SameWindowFirstTransitionBoundaryInput computed) :
    transition.graphInput.exitCertificate =
        InducedPathComponentBoundarySchedule.scanExit
          transition.graphInput.ambientReturn
          transition.graphInput.InAnchorComponent
          transition.graphInput.anchor_in_component
          transition.graphInput.window_vertex_not_in_component ∧
      (∀ stub, stub ∈ InducedPathComponentBoundarySchedule.incidentStubs
          transition.graphInput ↔
        InducedPathColdSkeleton.component stub =
          InducedPathColdSkeleton.component transition.stub) ∧
      2 ≤ (InducedPathComponentBoundarySchedule.incidentStubs
        transition.graphInput).length := by
  exact ⟨rfl,
    InducedPathComponentBoundarySchedule.mem_incidentStubs_iff
      transition.graphInput,
    InducedPathComponentBoundarySchedule.two_le_incidentStubs_length
      transition.graphInput⟩

theorem successor_is_stored_cyclic_next
    (transition : P13SameWindowFirstTransitionBoundaryInput computed) :
    transition.result.successor =
      @List.next _
        (InducedPathComponentBoundarySchedule.boundaryStubs
          ctx.G.object).decEq
        (InducedPathComponentBoundarySchedule.incidentStubs
          transition.graphInput) transition.stub
          (InducedPathComponentBoundarySchedule.anchor_mem_incidentStubs
            transition.graphInput) := rfl

theorem slot_first_hit_provenance
    (transition : P13SameWindowFirstTransitionBoundaryInput computed) :
    ∃ hit, transition.graphInput.slotScan = .found hit ∧
      transition.graphInput.windowPosition.1 = hit.value ∧
      ∀ candidate ∈ hit.before,
        ¬transition.graphInput.SlotPredicate candidate :=
  transition.graphInput.windowPosition_firstHit

theorem componentPath_shortest
    (transition : P13SameWindowFirstTransitionBoundaryInput computed) :
    transition.componentPath.IsPath ∧
      transition.componentPath.length =
        (InducedPathColdSkeleton.component transition.stub).toSimpleGraph.dist
          transition.result.componentRoot transition.result.componentTarget :=
  ⟨InducedPathComponentBoundarySchedule.componentPath_isPath
      transition.graphInput,
    InducedPathComponentBoundarySchedule.componentPath_shortest
      transition.graphInput⟩

theorem visibleChecks_eq
    (transition : P13SameWindowFirstTransitionBoundaryInput computed) :
    InducedPathComponentBoundarySchedule.visibleChecks transition.graphInput =
      InducedPathWindowLedger.checks ctx.G.object +
        13 * InducedPathWindowLedger.packingNumber ctx.G.object +
        transition.graphInput.ambientReturn.length *
          (InducedPathColdSkeleton.outsideObject
            ctx.G.object).input.vertices.card +
        (InducedPathComponentBoundarySchedule.outsideBfsProfile
          transition.graphInput).budget
          (InducedPathColdSkeleton.outsideObject
            ctx.G.object).input.vertices.card +
        (InducedPathColdSkeleton.outsideObject
          ctx.G.object).input.vertices.card ^ 2 +
        (InducedPathWindowLedger.tokens ctx.G.object).card *
          (2 + 13 * InducedPathWindowLedger.packingNumber ctx.G.object +
            (InducedPathColdSkeleton.outsideObject
              ctx.G.object).input.vertices.card) +
        (InducedPathComponentBoundarySchedule.bfsProfile
          transition.graphInput).budget
          (InducedPathComponentBoundarySchedule.componentObject
            transition.graphInput).input.vertices.card :=
  InducedPathComponentBoundarySchedule.visibleChecks_eq transition.graphInput

theorem visibleChecks_polynomial
    (transition : P13SameWindowFirstTransitionBoundaryInput computed) :
    InducedPathComponentBoundarySchedule.visibleChecks transition.graphInput ≤
      50 * InducedPathComponentBoundarySchedule.localScale
        transition.graphInput ^ 3 :=
  InducedPathComponentBoundarySchedule.visibleChecks_polynomial
    transition.graphInput

end P13SameWindowFirstTransitionBoundaryInput

end Erdos64EG.Internal
