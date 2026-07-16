import Erdos64EG.TypeANode63Support
import StructuralExhaustion.Graph.TypeACompletionPortCoordinate

namespace Erdos64EG.Internal.TypeACompletionPortCoordinates

open StructuralExhaustion

universe u

variable
  {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}

abbrev Node61
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :=
  TypeBEntryRouting.VerifiedNode61Residual ctx

/-- Exact completion-port coordinate attached to the proof-carrying node
`[63]` Type A residual, rather than to a freshly assumed support profile. -/
abbrev Coordinate (node61 : Node61 ctx)
    (node63 : TypeANode63Support.VerifiedNode63Residual (ctx := ctx) node61) :=
  Graph.TypeACompletionPortCoordinate.Coordinate ctx.G.object
    node63.typeAProfile

@[implicit_reducible]
noncomputable def coordinates (node61 : Node61 ctx)
    (node63 : TypeANode63Support.VerifiedNode63Residual (ctx := ctx) node61) :
    FinEnum (Coordinate (ctx := ctx) node61 node63) :=
  Graph.TypeACompletionPortCoordinate.coordinates ctx.G.object
    node63.typeAProfile

theorem receiver_mem_node61_support (node61 : Node61 ctx)
    (node63 : TypeANode63Support.VerifiedNode63Residual (ctx := ctx) node61)
    (port : Coordinate (ctx := ctx) node61 node63) :
    (port.receiver ctx.G.object node63.typeAProfile).1 ∈
      node61.support.core := by
  rw [← node63.profile_support]
  exact (port.receiver ctx.G.object node63.typeAProfile).2

theorem outside_not_mem_node61_support (node61 : Node61 ctx)
    (node63 : TypeANode63Support.VerifiedNode63Residual (ctx := ctx) node61)
    (port : Coordinate (ctx := ctx) node61 node63) :
    port.outside ctx.G.object node63.typeAProfile ∉
      node61.support.core := by
  rw [← node63.profile_support]
  exact port.outside_not_mem_support ctx.G.object node63.typeAProfile

theorem receiver_internal_degree_le_two (node61 : Node61 ctx)
    (node63 : TypeANode63Support.VerifiedNode63Residual (ctx := ctx) node61)
    (port : Coordinate (ctx := ctx) node61 node63) :
    (node63.typeAProfile.supportObject ctx.G.object).degree
      (port.receiver ctx.G.object node63.typeAProfile) ≤ 2 :=
  port.receiver_internal_degree_le_two ctx.G.object node63.typeAProfile

theorem receiver_ambient_degree_eq_three (node61 : Node61 ctx)
    (node63 : TypeANode63Support.VerifiedNode63Residual (ctx := ctx) node61)
    (port : Coordinate (ctx := ctx) node61 node63) :
    ctx.G.object.degree
      (port.receiver ctx.G.object node63.typeAProfile).1 = 3 :=
  port.receiver_ambient_degree_eq_three ctx.G.object node63.typeAProfile

theorem port_is_actual_ambient_edge (node61 : Node61 ctx)
    (node63 : TypeANode63Support.VerifiedNode63Residual (ctx := ctx) node61)
    (port : Coordinate (ctx := ctx) node61 node63) :
    ctx.G.object.graph.Adj
      (port.receiver ctx.G.object node63.typeAProfile).1
      (port.outside ctx.G.object node63.typeAProfile) :=
  port.adjacent ctx.G.object node63.typeAProfile

theorem visibleChecks_polynomial (node61 : Node61 ctx)
    (node63 : TypeANode63Support.VerifiedNode63Residual (ctx := ctx) node61) :
    Graph.TypeACompletionPortCoordinate.visibleChecks ctx.G.object
        node63.typeAProfile ≤ 4 * ctx.G.object.input.vertices.card :=
  Graph.TypeACompletionPortCoordinate.visibleChecks_polynomial ctx.G.object
    node63.typeAProfile

end Erdos64EG.Internal.TypeACompletionPortCoordinates
