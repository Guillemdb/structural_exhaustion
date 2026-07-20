import Erdos64EG.Future.TypeBFanCenterCoordinates
import StructuralExhaustion.Graph.TypeBFanShoulderIncidenceCoordinate

namespace Erdos64EG.Internal.TypeBFanShoulderIncidenceCoordinates

open StructuralExhaustion

universe u

variable
  {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}

open TypeBEntryRouting

/-- The next D6 input is deliberately restricted to the ordinary node-`[64]`
branch, whose assigned high center is the center of the full ambient fan.  The
decorated node-`[66]` branch only supplies its retained `firstNeighbors`, so it
must not be widened to all ambient ports here.  Deletion criticality is the
already proved theorem on the same minimal graph. -/
def profile
    (residual : VerifiedNode64Residual ctx) :
    Graph.TypeBFanShoulderIncidenceCoordinate.Profile ctx.G.object where
  center := residual.highSurplus.center
  centerHigh := residual.highSurplus.high
  deletionCritical :=
    (fixedPackedInput ctx).dart_has_tight_endpoint
      (packedStaticInput.fixedContext ctx)

abbrev Coordinate
    (residual : VerifiedNode64Residual ctx) :=
  Graph.TypeBFanShoulderIncidenceCoordinate.Coordinate ctx.G.object
    (profile residual)

@[implicit_reducible]
def coordinates
    (residual : VerifiedNode64Residual ctx) : FinEnum (Coordinate residual) :=
  Graph.TypeBFanShoulderIncidenceCoordinate.coordinates ctx.G.object
    (profile residual)

@[simp]
theorem profile_center
    (residual : VerifiedNode64Residual ctx) :
    (profile residual).center = residual.highSurplus.center :=
  rfl

theorem coordinate_incidences
    (residual : VerifiedNode64Residual ctx)
    (coordinate : Coordinate residual) :
    ctx.G.object.graph.Adj (profile residual).center
        (Graph.TypeBFanShoulderIncidenceCoordinate.Coordinate.endpoint
          ctx.G.object (profile residual) coordinate) ∧
      ctx.G.object.graph.Adj
        (Graph.TypeBFanShoulderIncidenceCoordinate.Coordinate.endpoint
          ctx.G.object (profile residual) coordinate)
        (Graph.TypeBFanShoulderIncidenceCoordinate.Coordinate.shoulder
          ctx.G.object (profile residual) coordinate) :=
  ⟨Graph.TypeBFanShoulderIncidenceCoordinate.Coordinate.center_incident
      ctx.G.object (profile residual) coordinate,
    Graph.TypeBFanShoulderIncidenceCoordinate.Coordinate.shoulder_incident
      ctx.G.object (profile residual) coordinate⟩

theorem coordinate_endpoint_cubic
    (residual : VerifiedNode64Residual ctx)
    (coordinate : Coordinate residual) :
    ctx.G.object.degree
      (Graph.TypeBFanShoulderIncidenceCoordinate.Coordinate.endpoint
        ctx.G.object (profile residual) coordinate) = 3 :=
  Graph.TypeBFanShoulderIncidenceCoordinate.Coordinate.endpoint_cubic
    ctx.G.object (profile residual) coordinate

theorem coordinates_card_eq_two_mul_center_degree
    (residual : VerifiedNode64Residual ctx) :
    (coordinates residual).card =
      2 * ctx.G.object.degree residual.highSurplus.center :=
  Graph.TypeBFanShoulderIncidenceCoordinate.coordinates_card_eq_two_mul_degree
    ctx.G.object (profile residual)

theorem coordinates_linear
    (residual : VerifiedNode64Residual ctx) :
    (coordinates residual).card ≤ 2 * ctx.G.object.input.vertices.card := by
  change Graph.TypeBFanShoulderIncidenceCoordinate.visibleChecks ctx.G.object
    (profile residual) ≤ 2 * ctx.G.object.input.vertices.card
  exact Graph.TypeBFanShoulderIncidenceCoordinate.visibleChecks_linear
    ctx.G.object (profile residual)

end Erdos64EG.Internal.TypeBFanShoulderIncidenceCoordinates
