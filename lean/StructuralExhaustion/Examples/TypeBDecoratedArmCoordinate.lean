import StructuralExhaustion.Graph.TypeBDecoratedArmCoordinate

namespace StructuralExhaustion.Examples.TypeBDecoratedArmCoordinate

open StructuralExhaustion
open StructuralExhaustion.Graph

universe u

variable
  {V : Type u}
  {object : FiniteObject V}
  {ContextSafe ForbiddenFree CoreFree Uncompressible : Finset V → Prop}
  {FanSafe : V → V → V → Prop}
  {source : NegativeSupportHandoff.ConnectedNegativeSupport object}
  (handoff : NegativeSupportHandoff.DecoratedHandoff object ContextSafe
    ForbiddenFree CoreFree Uncompressible FanSafe source)

open Graph.TypeBDecoratedArmCoordinate

example (coordinate : Coordinate handoff) :
    object.graph.Adj handoff.center coordinate.first.1 :=
  coordinate.first_adjacent_center handoff

example (coordinate : Coordinate handoff) :
    coordinate.vertex handoff ∈ (handoff.arm coordinate.first).path.support ∧
      handoff.center ∉ (handoff.arm coordinate.first).path.support :=
  ⟨coordinate.vertex_mem_arm handoff, coordinate.center_not_mem_arm handoff⟩

example (coordinate : Coordinate handoff)
    (coreMember : coordinate.vertex handoff ∈ source.core) :
    coordinate.vertex handoff = (handoff.arm coordinate.first).terminal :=
  coordinate.core_vertex_is_terminal handoff coreMember

example (left right : FirstNeighbor handoff) (distinct : left ≠ right) :
    FanSafe handoff.center left.1 right.1 :=
  retained_pair_fanSafe handoff left right distinct

example :
    (coordinates handoff).card ≤ visibleChecks handoff :=
  coordinates_card_le_visibleChecks handoff

example :
    visibleChecks handoff ≤
      object.input.vertices.card * (object.input.vertices.card + 1) :=
  visibleChecks_quadratic handoff

example :
    (budget handoff).checks () ≤ (budget handoff).coefficient *
      ((budget handoff).size () + 1) ^ (budget handoff).degree :=
  (budget handoff).bounded ()

end StructuralExhaustion.Examples.TypeBDecoratedArmCoordinate
