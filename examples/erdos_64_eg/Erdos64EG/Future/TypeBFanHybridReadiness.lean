import Erdos64EG.Future.TypeBFanIncidenceCoordinateLedger
import StructuralExhaustion.Graph.FanClosedPort

namespace Erdos64EG.Internal.TypeBFanHybridReadiness

open StructuralExhaustion

universe u

variable {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}

open TypeBEntryRouting
open TypeBFanIncidenceSupportClassification
open TypeBFanIncidenceCoordinateLedger

/-- The literal carrier for one node-`[64]` shoulder coordinate.  This is the
same ordered endpoint--shoulder pair required by `FanClosedPort.Assigned`.
It is data derived from the graph, not an assignment predicate. -/
def carrier
    (residual : VerifiedNode64Residual ctx)
    (coordinate : TypeBFanShoulderIncidenceCoordinates.Coordinate residual) :
    Graph.FanClosedPort.LocalCarrier ctx.G.Vertex :=
  (Endpoint residual coordinate, Shoulder residual coordinate)

theorem carrier_adjacent
    (residual : VerifiedNode64Residual ctx)
    (coordinate : TypeBFanShoulderIncidenceCoordinates.Coordinate residual) :
    ctx.G.object.graph.Adj (carrier residual coordinate).1
      (carrier residual coordinate).2 :=
  Graph.TypeBFanShoulderIncidenceCoordinate.Coordinate.shoulder_incident
    ctx.G.object (TypeBFanShoulderIncidenceCoordinates.profile residual) coordinate

/-- Exact assignment input still required after a shoulder lands in a selected
window.  The request retains all proved geometry and support provenance; it
does not assert or negate the absent `Assigned` judgment. -/
structure WindowAssignmentRequest
    (residual : VerifiedNode64Residual ctx)
    (coordinate : TypeBFanShoulderIncidenceCoordinates.Coordinate residual) where
  carrier : Graph.FanClosedPort.LocalCarrier ctx.G.Vertex
  carrierExact : carrier = TypeBFanHybridReadiness.carrier residual coordinate
  adjacent : ctx.G.object.graph.Adj carrier.1 carrier.2
  endpointAssigned : Endpoint residual coordinate ∈ residual.support.core
  endpointRemainder : Endpoint residual coordinate ∈ p13RemainderVertices ctx
  shoulderOwner : Graph.SelectedWindowIncidenceCoordinate.SelectedSlot
    ctx.G.object (Shoulder residual coordinate)
  incidence : Graph.SelectedWindowIncidenceCoordinate.WindowRemainderIncidence
    ctx.G.object

/-- Exact assignment input still required when the whole literal incidence
stays in the remainder. -/
structure InternalAssignmentRequest
    (residual : VerifiedNode64Residual ctx)
    (coordinate : TypeBFanShoulderIncidenceCoordinates.Coordinate residual) where
  carrier : Graph.FanClosedPort.LocalCarrier ctx.G.Vertex
  carrierExact : carrier = TypeBFanHybridReadiness.carrier residual coordinate
  adjacent : ctx.G.object.graph.Adj carrier.1 carrier.2
  endpointAssigned : Endpoint residual coordinate ∈ residual.support.core
  incidence : Graph.SelectedWindowIncidenceCoordinate.InternalRemainderIncidence
    ctx.G.object

/-- Earliest dependency-ready adapter toward the hybrid-fan modules.  The
three constructors are exactly the exhaustive incidence ledger branches.
The endpoint-window branch is already routed geometrically.  In the other two
branches the next semantic input is precisely an assignment judgment for the
displayed actual carrier. -/
inductive Readiness
    (residual : VerifiedNode64Residual ctx)
    (coordinate : TypeBFanShoulderIncidenceCoordinates.Coordinate residual) where
  | endpointWindow
      (outside : EndpointOutsideResidual residual coordinate)
      (landing : TypeBFanWindowLandingCoordinate.MissingSourceOwnerResidual
        residual coordinate outside)
  | windowAssignmentRequired
      (request : WindowAssignmentRequest residual coordinate)
  | internalAssignmentRequired
      (request : InternalAssignmentRequest residual coordinate)

/-- Classify one actual shoulder coordinate without inspecting any ambient
vertex family. -/
noncomputable def classify
    (residual : VerifiedNode64Residual ctx)
    (coordinate : TypeBFanShoulderIncidenceCoordinates.Coordinate residual) :
    Readiness residual coordinate := by
  cases TypeBFanIncidenceCoordinateLedger.ledger residual coordinate with
  | endpointWindow outside landing =>
      exact .endpointWindow outside landing
  | shoulderWindow entry =>
      exact .windowAssignmentRequired {
        carrier := carrier residual coordinate
        carrierExact := rfl
        adjacent := carrier_adjacent residual coordinate
        endpointAssigned := entry.endpointAssigned
        endpointRemainder := entry.endpointRemainder
        shoulderOwner := entry.shoulderOwner
        incidence := entry.incidence }
  | internalRemainder entry =>
      exact .internalAssignmentRequired {
        carrier := carrier residual coordinate
        carrierExact := rfl
        adjacent := carrier_adjacent residual coordinate
        endpointAssigned := entry.endpointAssigned
        incidence := entry.incidence }

/-- A canonical first readiness result exists because node `[64]` already
proves degree at least four.  Selecting it performs no scan. -/
noncomputable def first
    (residual : VerifiedNode64Residual ctx) :
    Readiness residual
      (Graph.TypeBFanShoulderIncidenceCoordinate.firstCoordinate ctx.G.object
        (TypeBFanShoulderIncidenceCoordinates.profile residual)) :=
  classify residual
    (Graph.TypeBFanShoulderIncidenceCoordinate.firstCoordinate ctx.G.object
      (TypeBFanShoulderIncidenceCoordinates.profile residual))

/-- The adapter reuses the exact two-membership-read incidence schedule and
therefore keeps its linear local bound. -/
def visibleChecks (residual : VerifiedNode64Residual ctx) : Nat :=
  TypeBFanIncidenceCoordinateLedger.visibleChecks residual

theorem visibleChecks_linear (residual : VerifiedNode64Residual ctx) :
    visibleChecks residual ≤ 4 * ctx.G.object.input.vertices.card :=
  TypeBFanIncidenceCoordinateLedger.visibleChecks_linear residual

end Erdos64EG.Internal.TypeBFanHybridReadiness
