import Erdos64EG.TypeBEntryRouting
import StructuralExhaustion.Graph.TypeBFanCenterCoordinate

namespace Erdos64EG.Internal.TypeBFanCenterCoordinates

open StructuralExhaustion

universe u

variable
  {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}
  {ContextSafe ForbiddenFree CoreFree Uncompressible :
    Finset ctx.G.Vertex → Prop}
  {FanSafe : ctx.G.Vertex → ctx.G.Vertex → ctx.G.Vertex → Prop}

open TypeBEntryRouting

/-- The exact first D6 input at node `[65]`.  The ordinary branch uses the
node-`[64]` high-center witness; the decorated branch uses the center stored by
the node-`[108] -> [66]` handoff.  No branch-specific property is transferred
across the join. -/
def profile
    (residual : VerifiedNode65Residual ctx ContextSafe ForbiddenFree CoreFree
      Uncompressible FanSafe) :
    Graph.TypeBFanCenterCoordinate.Profile ctx.G.object := by
  cases residual with
  | ordinary residual =>
      exact {
        center := residual.highSurplus.center
        centerHigh := residual.highSurplus.high }
  | decorated residual =>
      exact {
        center := residual.decorated.center
        centerHigh := residual.decorated.center_high }

abbrev Coordinate
    (residual : VerifiedNode65Residual ctx ContextSafe ForbiddenFree CoreFree
      Uncompressible FanSafe) :=
  Graph.TypeBFanCenterCoordinate.Coordinate ctx.G.object (profile residual)

/-- Exact finite fan-center incidence schedule attached to node `[65]`. -/
@[implicit_reducible]
def coordinates
    (residual : VerifiedNode65Residual ctx ContextSafe ForbiddenFree CoreFree
      Uncompressible FanSafe) : FinEnum (Coordinate residual) :=
  Graph.TypeBFanCenterCoordinate.coordinates ctx.G.object (profile residual)

@[simp]
theorem profile_center_ordinary (residual : VerifiedNode64Residual ctx) :
    (profile (VerifiedNode65Residual.ordinary residual :
      VerifiedNode65Residual ctx ContextSafe ForbiddenFree CoreFree
        Uncompressible FanSafe)).center = residual.highSurplus.center :=
  rfl

@[simp]
theorem profile_center_decorated
    (residual : Node66Residual ctx ContextSafe ForbiddenFree CoreFree
      Uncompressible FanSafe) :
    (profile (VerifiedNode65Residual.decorated residual :
      VerifiedNode65Residual ctx ContextSafe ForbiddenFree CoreFree
        Uncompressible FanSafe)).center = residual.decorated.center :=
  rfl

theorem coordinate_incident
    (residual : VerifiedNode65Residual ctx ContextSafe ForbiddenFree CoreFree
      Uncompressible FanSafe)
    (coordinate : Coordinate residual) :
    ctx.G.object.graph.Adj (profile residual).center
      (Graph.TypeBFanCenterCoordinate.Coordinate.endpoint ctx.G.object
        (profile residual) coordinate) :=
  Graph.TypeBFanCenterCoordinate.Coordinate.incident ctx.G.object
    (profile residual) coordinate

theorem coordinates_card_eq_center_degree
    (residual : VerifiedNode65Residual ctx ContextSafe ForbiddenFree CoreFree
      Uncompressible FanSafe) :
    (coordinates residual).card = ctx.G.object.degree (profile residual).center :=
  Graph.TypeBFanCenterCoordinate.coordinates_card_eq_degree ctx.G.object
    (profile residual)

theorem coordinates_linear
    (residual : VerifiedNode65Residual ctx ContextSafe ForbiddenFree CoreFree
      Uncompressible FanSafe) :
    (coordinates residual).card ≤ ctx.G.object.input.vertices.card := by
  change Graph.TypeBFanCenterCoordinate.visibleChecks ctx.G.object
    (profile residual) ≤ ctx.G.object.input.vertices.card
  exact Graph.TypeBFanCenterCoordinate.visibleChecks_linear ctx.G.object
    (profile residual)

end Erdos64EG.Internal.TypeBFanCenterCoordinates
