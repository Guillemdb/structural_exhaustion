import Erdos64EG.Future.TypeBFanWindowLandingCoordinate

namespace Erdos64EG.Internal.TypeBFanIncidenceCoordinateLedger

open StructuralExhaustion

universe u

variable {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}

open TypeBEntryRouting
open TypeBFanIncidenceSupportClassification

/-- Assigned endpoint with a literal shoulder landing in one uniquely owned
selected-window slot. -/
structure ShoulderWindowEntry
    (residual : VerifiedNode64Residual ctx)
    (coordinate : TypeBFanShoulderIncidenceCoordinates.Coordinate residual) where
  endpointAssigned : Endpoint residual coordinate ∈ residual.support.core
  endpointRemainder : Endpoint residual coordinate ∈ p13RemainderVertices ctx
  shoulderOwner : Graph.SelectedWindowIncidenceCoordinate.SelectedSlot
    ctx.G.object (Shoulder residual coordinate)
  incidence : Graph.SelectedWindowIncidenceCoordinate.WindowRemainderIncidence
    ctx.G.object

/-- Assigned endpoint whose second literal incidence also stays in the exact
remainder. -/
structure InternalRemainderEntry
    (residual : VerifiedNode64Residual ctx)
    (coordinate : TypeBFanShoulderIncidenceCoordinates.Coordinate residual) where
  endpointAssigned : Endpoint residual coordinate ∈ residual.support.core
  incidence : Graph.SelectedWindowIncidenceCoordinate.InternalRemainderIncidence
    ctx.G.object

/-- Exhaustive D6 incidence-coordinate ledger for one ordinary node-`[64]`
shoulder coordinate.  The source coordinate is retained as an index in every
constructor. -/
inductive IncidenceLedger
    (residual : VerifiedNode64Residual ctx)
    (coordinate : TypeBFanShoulderIncidenceCoordinates.Coordinate residual) where
  | endpointWindow
      (outside : EndpointOutsideResidual residual coordinate)
      (landing : TypeBFanWindowLandingCoordinate.MissingSourceOwnerResidual
        residual coordinate outside)
  | shoulderWindow (entry : ShoulderWindowEntry residual coordinate)
  | internalRemainder (entry : InternalRemainderEntry residual coordinate)

/-- Execute the branch-specific ledger.  Selected-window owners are recovered
directly from covered-membership proofs; no selected-window family is scanned. -/
noncomputable def ledger
    (residual : VerifiedNode64Residual ctx)
    (coordinate : TypeBFanShoulderIncidenceCoordinates.Coordinate residual) :
    IncidenceLedger residual coordinate := by
  cases TypeBFanIncidenceSupportClassification.route residual coordinate with
  | endpointOutside outside =>
      exact .endpointWindow outside
        (TypeBFanWindowLandingCoordinate.windowLanding residual coordinate outside)
  | window endpointAssigned endpointRemainder shoulderWindow =>
      let owner :=
        Graph.SelectedWindowIncidenceCoordinate.SelectedSlot.of_mem_covered
          ctx.G.object shoulderWindow
      exact .shoulderWindow {
        endpointAssigned := endpointAssigned
        endpointRemainder := endpointRemainder
        shoulderOwner := owner
        incidence := {
          windowVertex := Shoulder residual coordinate
          slot := owner
          remainderVertex := Endpoint residual coordinate
          remainder := endpointRemainder
          adjacent :=
            Graph.TypeBFanShoulderIncidenceCoordinate.Coordinate.shoulder_incident
              ctx.G.object
                (TypeBFanShoulderIncidenceCoordinates.profile residual) coordinate } }
  | nonWindow endpointAssigned endpointRemainder shoulderRemainder =>
      exact .internalRemainder {
        endpointAssigned := endpointAssigned
        incidence := {
          leftVertex := Endpoint residual coordinate
          leftRemainder := endpointRemainder
          rightVertex := Shoulder residual coordinate
          rightRemainder := shoulderRemainder
          adjacent :=
            Graph.TypeBFanShoulderIncidenceCoordinate.Coordinate.shoulder_incident
              ctx.G.object
                (TypeBFanShoulderIncidenceCoordinates.profile residual) coordinate } }

/-- Ledger execution inherits the two-membership-read schedule of the exact
support classifier.  Owner recovery is proof-selected from covered membership
and adds no window scan. -/
def visibleChecks (residual : VerifiedNode64Residual ctx) : Nat :=
  Graph.TypeBFanIncidenceSupportClassification.visibleChecks ctx.G.object
    (TypeBFanShoulderIncidenceCoordinates.profile residual)

theorem visibleChecks_linear (residual : VerifiedNode64Residual ctx) :
    visibleChecks residual ≤ 4 * ctx.G.object.input.vertices.card :=
  Graph.TypeBFanIncidenceSupportClassification.visibleChecks_linear ctx.G.object
    (TypeBFanShoulderIncidenceCoordinates.profile residual)

end Erdos64EG.Internal.TypeBFanIncidenceCoordinateLedger
