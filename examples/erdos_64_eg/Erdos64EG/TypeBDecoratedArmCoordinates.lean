import Erdos64EG.TypeBEntryRouting
import StructuralExhaustion.Graph.TypeBDecoratedArmCoordinate

namespace Erdos64EG.Internal.TypeBDecoratedArmCoordinates

open StructuralExhaustion

universe u

variable
  {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}
  {ContextSafe ForbiddenFree CoreFree Uncompressible :
    Finset ctx.G.Vertex → Prop}
  {FanSafe : ctx.G.Vertex → ctx.G.Vertex → ctx.G.Vertex → Prop}

open TypeBEntryRouting

abbrev Coordinate
    (residual : Node66Residual ctx ContextSafe ForbiddenFree CoreFree
      Uncompressible FanSafe) :=
  Graph.TypeBDecoratedArmCoordinate.Coordinate residual.decorated

/-- Exact D6 decorated-arm coordinate family, without widening the retained
`firstNeighbors` supplied by node `[66]`. -/
@[implicit_reducible]
noncomputable def coordinates
    (residual : Node66Residual ctx ContextSafe ForbiddenFree CoreFree
      Uncompressible FanSafe) : FinEnum (Coordinate residual) :=
  Graph.TypeBDecoratedArmCoordinate.coordinates residual.decorated

theorem coordinate_first_adjacent_center
    (residual : Node66Residual ctx ContextSafe ForbiddenFree CoreFree
      Uncompressible FanSafe)
    (coordinate : Coordinate residual) :
    ctx.G.object.graph.Adj residual.decorated.center coordinate.first.1 :=
  coordinate.first_adjacent_center residual.decorated

theorem coordinate_first_entry
    (residual : Node66Residual ctx ContextSafe ForbiddenFree CoreFree
      Uncompressible FanSafe)
    (coordinate : Coordinate residual)
    (coreMember : coordinate.vertex residual.decorated ∈ residual.source.core) :
    coordinate.vertex residual.decorated =
      (residual.decorated.arm coordinate.first).terminal :=
  coordinate.core_vertex_is_terminal residual.decorated coreMember

theorem coordinate_center_avoided
    (residual : Node66Residual ctx ContextSafe ForbiddenFree CoreFree
      Uncompressible FanSafe)
    (coordinate : Coordinate residual) :
    residual.decorated.center ∉
      (residual.decorated.arm coordinate.first).path.support :=
  coordinate.center_not_mem_arm residual.decorated

theorem retained_pair_fanSafe
    (residual : Node66Residual ctx ContextSafe ForbiddenFree CoreFree
      Uncompressible FanSafe)
    (left right : Graph.TypeBDecoratedArmCoordinate.FirstNeighbor
      residual.decorated)
    (distinct : left ≠ right) :
    FanSafe residual.decorated.center left.1 right.1 :=
  Graph.TypeBDecoratedArmCoordinate.retained_pair_fanSafe residual.decorated
    left right distinct

theorem coordinates_quadratic
    (residual : Node66Residual ctx ContextSafe ForbiddenFree CoreFree
      Uncompressible FanSafe) :
    (coordinates residual).card ≤
      residual.decorated.firstNeighbors.card *
        (ctx.G.object.input.vertices.card + 1) :=
  Graph.TypeBDecoratedArmCoordinate.coordinates_card_le_visibleChecks
    residual.decorated

end Erdos64EG.Internal.TypeBDecoratedArmCoordinates
