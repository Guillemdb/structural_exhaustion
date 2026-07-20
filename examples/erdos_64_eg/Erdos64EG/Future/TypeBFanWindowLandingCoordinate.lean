import Erdos64EG.Future.TypeBFanIncidenceSupportClassification
import StructuralExhaustion.Graph.SelectedWindowIncidenceCoordinate

namespace Erdos64EG.Internal.TypeBFanWindowLandingCoordinate

open StructuralExhaustion

universe u

variable {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}

open TypeBEntryRouting
open TypeBFanIncidenceSupportClassification

/-- The exact selected-window owner of the endpoint in an endpoint-outside D6
residual.  The lookup consumes covered membership and does not scan windows. -/
noncomputable def endpointSlot
    (residual : VerifiedNode64Residual ctx)
    (coordinate : TypeBFanShoulderIncidenceCoordinates.Coordinate residual)
    (outside : EndpointOutsideResidual residual coordinate) :
    Graph.SelectedWindowIncidenceCoordinate.SelectedSlot ctx.G.object
      (Endpoint residual coordinate) :=
  Graph.SelectedWindowIncidenceCoordinate.SelectedSlot.of_mem_covered
    ctx.G.object outside.endpointWindow

private theorem center_not_covered
    (residual : VerifiedNode64Residual ctx) :
    residual.highSurplus.center ∉ p13CoveredVertices ctx := by
  letI : FinEnum ctx.G.Vertex := ctx.G.object.input.vertices
  letI : DecidableEq ctx.G.Vertex := ctx.G.object.input.vertices.decEq
  have centerRemainder : residual.highSurplus.center ∈ p13RemainderVertices ctx :=
    residual.core_subset_remainder ctx residual.highSurplus.center_mem
  unfold p13RemainderVertices Graph.InducedPathPacking.remainderVertices at centerRemainder
  simp only [Finset.mem_sdiff, Finset.mem_univ, true_and] at centerRemainder
  unfold p13CoveredVertices
  exact centerRemainder

/-- No source-window owner is retained because the literal source center is a
remainder vertex and therefore has no selected-window owner.  The corresponding
coordinate is exactly a window--remainder incidence, not a same/cross-window
pair. -/
structure MissingSourceOwnerResidual
    (residual : VerifiedNode64Residual ctx)
    (coordinate : TypeBFanShoulderIncidenceCoordinates.Coordinate residual)
    (outside : EndpointOutsideResidual residual coordinate) where
  endpointOwner : Graph.SelectedWindowIncidenceCoordinate.SelectedSlot
    ctx.G.object (Endpoint residual coordinate)
  sourceRemainder : residual.highSurplus.center ∈ p13RemainderVertices ctx
  sourceNotCovered : residual.highSurplus.center ∉ p13CoveredVertices ctx
  incidence : Graph.SelectedWindowIncidenceCoordinate.WindowRemainderIncidence
    ctx.G.object

noncomputable def windowLanding
    (residual : VerifiedNode64Residual ctx)
    (coordinate : TypeBFanShoulderIncidenceCoordinates.Coordinate residual)
    (outside : EndpointOutsideResidual residual coordinate) :
    MissingSourceOwnerResidual residual coordinate outside := by
  let owner := endpointSlot residual coordinate outside
  let sourceRemainder : residual.highSurplus.center ∈ p13RemainderVertices ctx :=
    residual.core_subset_remainder ctx residual.highSurplus.center_mem
  exact {
    endpointOwner := owner
    sourceRemainder := sourceRemainder
    sourceNotCovered := center_not_covered residual
    incidence := {
      windowVertex := Endpoint residual coordinate
      slot := owner
      remainderVertex := residual.highSurplus.center
      remainder := sourceRemainder
      adjacent := outside.centerEndpoint } }

theorem endpoint_owner_unique
    (residual : VerifiedNode64Residual ctx)
    (coordinate : TypeBFanShoulderIncidenceCoordinates.Coordinate residual)
    (outside : EndpointOutsideResidual residual coordinate)
    (other : Graph.SelectedWindowIncidenceCoordinate.SelectedSlot ctx.G.object
      (Endpoint residual coordinate)) :
    (endpointSlot residual coordinate outside).window = other.window :=
  Graph.SelectedWindowIncidenceCoordinate.SelectedSlot.window_unique ctx.G.object
    (endpointSlot residual coordinate outside) other

end Erdos64EG.Internal.TypeBFanWindowLandingCoordinate
