import Erdos64EG.Future.TypeBFanHybridReadiness
import StructuralExhaustion.Graph.InducedCoreFanAssignment

namespace Erdos64EG.Internal.TypeBFanWholePortAssignment

open StructuralExhaustion

universe u

variable {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}

open TypeBEntryRouting
open TypeBFanIncidenceSupportClassification

abbrev Port (residual : VerifiedNode64Residual ctx) :=
  Graph.InducedCoreFanAssignment.Port ctx.G.object
    (TypeBFanShoulderIncidenceCoordinates.profile residual)

def coordinate (residual : VerifiedNode64Residual ctx)
    (port : Port residual) (side : Fin 2) :
    TypeBFanShoulderIncidenceCoordinates.Coordinate residual :=
  Graph.InducedCoreFanAssignment.coordinate ctx.G.object
    (TypeBFanShoulderIncidenceCoordinates.profile residual) port side

abbrev Assigned (residual : VerifiedNode64Residual ctx)
    (carrier : Graph.FanClosedPort.LocalCarrier ctx.G.Vertex) :=
  Graph.InducedCoreFanAssignment.Assigned ctx.G.object residual.support.core carrier

/-- The application-level fan profile is derived entirely from node `[64]`:
window and remainder sides are the fixed packing split, while assignment is
literal induced-core adjacency. -/
noncomputable def fanWindowProfile (residual : VerifiedNode64Residual ctx) :
    Graph.FanClosedPort.FanWindowProfile ctx.G.Vertex := by
  letI : FinEnum ctx.G.Vertex := ctx.G.object.input.vertices
  letI : DecidableEq ctx.G.Vertex := ctx.G.object.input.vertices.decEq
  exact {
    WindowSide := fun vertex => vertex ∈ p13CoveredVertices ctx
    RemainderSide := fun vertex => vertex ∈ p13RemainderVertices ctx
    Assigned := Assigned residual
    windowDecidable := fun _vertex => inferInstance
    remainderDecidable := fun _vertex => inferInstance
    assignedDecidable :=
      Graph.InducedCoreFanAssignment.assignedDecidable ctx.G.object
        residual.support.core
    remainder_not_window := by
      intro vertex remainder window
      unfold p13RemainderVertices Graph.InducedPathPacking.remainderVertices at remainder
      simp only [Finset.mem_sdiff, Finset.mem_univ, true_and] at remainder
      exact remainder window }

/-- Proof-carrying obligation for the first carrier that fails induced-core
assignment.  Its exact incidence-ledger and readiness provenance are retained. -/
structure MissingAssignmentRequest
    (residual : VerifiedNode64Residual ctx) (port : Port residual) where
  side : Fin 2
  missing : ¬Assigned residual
    (Graph.InducedCoreFanAssignment.carrier ctx.G.object
      (TypeBFanShoulderIncidenceCoordinates.profile residual) port side)
  ledger : TypeBFanIncidenceCoordinateLedger.IncidenceLedger residual
    (coordinate residual port side)
  readiness : TypeBFanHybridReadiness.Readiness residual
    (coordinate residual port side)

/-- Exact two-coordinate whole-port decision. -/
inductive Availability (residual : VerifiedNode64Residual ctx)
    (port : Port residual) where
  | both
      (first : Assigned residual
        (Graph.InducedCoreFanAssignment.carrier ctx.G.object
          (TypeBFanShoulderIncidenceCoordinates.profile residual) port
          Graph.InducedCoreFanAssignment.firstSide))
      (second : Assigned residual
        (Graph.InducedCoreFanAssignment.carrier ctx.G.object
          (TypeBFanShoulderIncidenceCoordinates.profile residual) port
          Graph.InducedCoreFanAssignment.secondSide))
      (firstLedger : TypeBFanIncidenceCoordinateLedger.IncidenceLedger residual
        (coordinate residual port Graph.InducedCoreFanAssignment.firstSide))
      (secondLedger : TypeBFanIncidenceCoordinateLedger.IncidenceLedger residual
        (coordinate residual port Graph.InducedCoreFanAssignment.secondSide))
  | firstMissing (request : MissingAssignmentRequest residual port)
      (firstSide : request.side = Graph.InducedCoreFanAssignment.firstSide)
  | secondMissing
      (first : Assigned residual
        (Graph.InducedCoreFanAssignment.carrier ctx.G.object
          (TypeBFanShoulderIncidenceCoordinates.profile residual) port
          Graph.InducedCoreFanAssignment.firstSide))
      (firstLedger : TypeBFanIncidenceCoordinateLedger.IncidenceLedger residual
        (coordinate residual port Graph.InducedCoreFanAssignment.firstSide))
      (request : MissingAssignmentRequest residual port)
      (secondSide : request.side = Graph.InducedCoreFanAssignment.secondSide)

/-- Run the graph-owned fixed two-side classifier and attach the exact node-64
incidence provenance to its result. -/
noncomputable def classify (residual : VerifiedNode64Residual ctx)
    (port : Port residual) : Availability residual port := by
  let profile := TypeBFanShoulderIncidenceCoordinates.profile residual
  cases Graph.InducedCoreFanAssignment.classify ctx.G.object profile
      residual.support.core port with
  | both first second =>
      exact .both first second
        (TypeBFanIncidenceCoordinateLedger.ledger residual
          (coordinate residual port Graph.InducedCoreFanAssignment.firstSide))
        (TypeBFanIncidenceCoordinateLedger.ledger residual
          (coordinate residual port Graph.InducedCoreFanAssignment.secondSide))
  | firstMissing missing =>
      exact .firstMissing {
        side := Graph.InducedCoreFanAssignment.firstSide
        missing := missing
        ledger := TypeBFanIncidenceCoordinateLedger.ledger residual _
        readiness := TypeBFanHybridReadiness.classify residual _ } rfl
  | secondMissing first missing =>
      exact .secondMissing first
        (TypeBFanIncidenceCoordinateLedger.ledger residual _)
        {
          side := Graph.InducedCoreFanAssignment.secondSide
          missing := missing
          ledger := TypeBFanIncidenceCoordinateLedger.ledger residual _
          readiness := TypeBFanHybridReadiness.classify residual _ } rfl

/-- A proof-carrying `both` result is exactly enough to establish fan closure
for an actual open port under the derived profile. -/
theorem fanClosed_of_both (residual : VerifiedNode64Residual ctx)
    (port : Graph.FanClosedPort.OpenPort
      (TypeBFanShoulderIncidenceCoordinates.profile residual).centerHigh
      (TypeBFanShoulderIncidenceCoordinates.profile residual).deletionCritical)
    (first : Assigned residual
      (Graph.InducedCoreFanAssignment.carrier ctx.G.object
        (TypeBFanShoulderIncidenceCoordinates.profile residual) port.1
        Graph.InducedCoreFanAssignment.firstSide))
    (second : Assigned residual
      (Graph.InducedCoreFanAssignment.carrier ctx.G.object
        (TypeBFanShoulderIncidenceCoordinates.profile residual) port.1
        Graph.InducedCoreFanAssignment.secondSide)) :
    Graph.FanClosedPort.FanClosed
      (TypeBFanShoulderIncidenceCoordinates.profile residual).centerHigh
      (TypeBFanShoulderIncidenceCoordinates.profile residual).deletionCritical
      (fanWindowProfile residual) port := by
  constructor
  · exact residual.core_subset_remainder ctx first.2.1
  · intro side
    cases side
    · rw [← Graph.InducedCoreFanAssignment.firstCarrier_eq_fanClosedCarrier
        ctx.G.object (TypeBFanShoulderIncidenceCoordinates.profile residual) port]
      exact first
    · rw [← Graph.InducedCoreFanAssignment.secondCarrier_eq_fanClosedCarrier
        ctx.G.object (TypeBFanShoulderIncidenceCoordinates.profile residual) port]
      exact second

/-- Consumer-facing result on an actual open port.  The successful constructor
contains the exact `FanClosed` proof required by the hybrid-fan modules; the
two failure constructors retain the first-missing order and all ledger data. -/
inductive OpenPortAvailability (residual : VerifiedNode64Residual ctx)
    (port : Graph.FanClosedPort.OpenPort
      (TypeBFanShoulderIncidenceCoordinates.profile residual).centerHigh
      (TypeBFanShoulderIncidenceCoordinates.profile residual).deletionCritical) where
  | fanClosed
      (first : Assigned residual
        (Graph.InducedCoreFanAssignment.carrier ctx.G.object
          (TypeBFanShoulderIncidenceCoordinates.profile residual) port.1
          Graph.InducedCoreFanAssignment.firstSide))
      (second : Assigned residual
        (Graph.InducedCoreFanAssignment.carrier ctx.G.object
          (TypeBFanShoulderIncidenceCoordinates.profile residual) port.1
          Graph.InducedCoreFanAssignment.secondSide))
      (firstLedger : TypeBFanIncidenceCoordinateLedger.IncidenceLedger residual
        (coordinate residual port.1 Graph.InducedCoreFanAssignment.firstSide))
      (secondLedger : TypeBFanIncidenceCoordinateLedger.IncidenceLedger residual
        (coordinate residual port.1 Graph.InducedCoreFanAssignment.secondSide))
      (closed : Graph.FanClosedPort.FanClosed
        (TypeBFanShoulderIncidenceCoordinates.profile residual).centerHigh
        (TypeBFanShoulderIncidenceCoordinates.profile residual).deletionCritical
        (fanWindowProfile residual) port)
  | firstMissing (request : MissingAssignmentRequest residual port.1)
      (firstSide : request.side = Graph.InducedCoreFanAssignment.firstSide)
  | secondMissing
      (first : Assigned residual
        (Graph.InducedCoreFanAssignment.carrier ctx.G.object
          (TypeBFanShoulderIncidenceCoordinates.profile residual) port.1
          Graph.InducedCoreFanAssignment.firstSide))
      (firstLedger : TypeBFanIncidenceCoordinateLedger.IncidenceLedger residual
        (coordinate residual port.1 Graph.InducedCoreFanAssignment.firstSide))
      (request : MissingAssignmentRequest residual port.1)
      (secondSide : request.side = Graph.InducedCoreFanAssignment.secondSide)

noncomputable def classifyOpen (residual : VerifiedNode64Residual ctx)
    (port : Graph.FanClosedPort.OpenPort
      (TypeBFanShoulderIncidenceCoordinates.profile residual).centerHigh
      (TypeBFanShoulderIncidenceCoordinates.profile residual).deletionCritical) :
    OpenPortAvailability residual port := by
  cases classify residual port.1 with
  | both first second firstLedger secondLedger =>
      exact .fanClosed first second firstLedger secondLedger
        (fanClosed_of_both residual port first second)
  | firstMissing request firstSide =>
      exact .firstMissing request firstSide
  | secondMissing first firstLedger request secondSide =>
      exact .secondMissing first firstLedger request secondSide

def visibleChecks : Nat := Graph.InducedCoreFanAssignment.visibleChecks

theorem visibleChecks_eq_two : visibleChecks = 2 := rfl

end Erdos64EG.Internal.TypeBFanWholePortAssignment
