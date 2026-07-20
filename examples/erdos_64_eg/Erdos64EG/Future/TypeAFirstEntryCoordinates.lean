import Erdos64EG.Future.TypeAAnchoredReturnCoordinates
import StructuralExhaustion.Graph.TypeAFirstEntryCoordinate

namespace Erdos64EG.Internal.TypeAFirstEntryCoordinates

open StructuralExhaustion

universe u

variable
  {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}

abbrev Node61 := TypeBEntryRouting.VerifiedNode61Residual ctx
abbrev Node63 (node61 : Node61 (ctx := ctx)) :=
  TypeANode63Support.VerifiedNode63Residual (ctx := ctx) node61
abbrev Port (node61 : Node61 (ctx := ctx)) (node63 : Node63 node61) :=
  TypeACompletionPortCoordinates.Coordinate (ctx := ctx) node61 node63

noncomputable def firstEntry (node61 : Node61 (ctx := ctx))
    (node63 : Node63 node61) (port : Port node61 node63) :=
  Graph.TypeAFirstEntryCoordinate.select ctx.G.object node63.typeAProfile port
    (TypeAAnchoredReturnCoordinates.anchoredReturn node61 node63 port)

theorem firstEntry_is_receiver (node61 : Node61 (ctx := ctx))
    (node63 : Node63 node61) (port : Port node61 node63) :
    (node63.typeAProfile.supportObject ctx.G.object).degree
      (⟨(firstEntry node61 node63 port).entry ctx.G.object node63.typeAProfile port
          (TypeAAnchoredReturnCoordinates.anchoredReturn node61 node63 port),
        (firstEntry node61 node63 port).entry_mem_support ctx.G.object
          node63.typeAProfile port
          (TypeAAnchoredReturnCoordinates.anchoredReturn node61 node63 port)⟩ :
        node63.typeAProfile.Vertex) ≤ 2 :=
  (firstEntry node61 node63 port).entry_internal_degree_le_two ctx.G.object
    node63.typeAProfile port
    (TypeAAnchoredReturnCoordinates.anchoredReturn node61 node63 port)

theorem firstEntry_predecessor_outside (node61 : Node61 (ctx := ctx))
    (node63 : Node63 node61) (port : Port node61 node63) :
    (firstEntry node61 node63 port).predecessor ctx.G.object
        node63.typeAProfile port
        (TypeAAnchoredReturnCoordinates.anchoredReturn node61 node63 port) ∉
      node61.support.core := by
  rw [← node63.profile_support]
  exact (firstEntry node61 node63 port).predecessor_outside ctx.G.object
    node63.typeAProfile port
    (TypeAAnchoredReturnCoordinates.anchoredReturn node61 node63 port)

end Erdos64EG.Internal.TypeAFirstEntryCoordinates
