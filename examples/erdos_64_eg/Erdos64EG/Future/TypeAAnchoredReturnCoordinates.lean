import Erdos64EG.Future.TypeACompletionPortCoordinates
import Erdos64EG.Future.CT2BridgeContraction
import StructuralExhaustion.Graph.TypeAAnchoredReturnCoordinate

namespace Erdos64EG.Internal.TypeAAnchoredReturnCoordinates

open StructuralExhaustion

universe u

variable
  {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}

abbrev Node61 := TypeBEntryRouting.VerifiedNode61Residual ctx

abbrev Node63 (node61 : Node61 (ctx := ctx)) :=
  TypeANode63Support.VerifiedNode63Residual (ctx := ctx) node61

abbrev Port (node61 : Node61 (ctx := ctx)) (node63 : Node63 node61) :=
  TypeACompletionPortCoordinates.Coordinate (ctx := ctx) node61 node63

/-- The graph-level minimality theorem supplies exactly the local non-bridge
premise for every node-`[63]` completion port, without inventing a dependency
on the separate node-`[69]` CT2 route. -/
noncomputable def producer (node61 : Node61 (ctx := ctx))
    (node63 : Node63 node61) :
    Graph.TypeAAnchoredReturnCoordinate.Producer ctx.G.object
      node63.typeAProfile where
  notBridge := fun port => minimality_dart_not_bridge ctx
    (Graph.TypeAAnchoredReturnCoordinate.dart ctx.G.object
      node63.typeAProfile port)

/-- One proof-selected simple return through each exact completion port. -/
noncomputable def anchoredReturn (node61 : Node61 (ctx := ctx))
    (node63 : Node63 node61) (port : Port node61 node63) :
    Graph.TypeAAnchoredReturnCoordinate.AnchoredReturn ctx.G.object
      node63.typeAProfile port :=
  (producer node61 node63).produce ctx.G.object node63.typeAProfile port

theorem anchoredReturn_isPath (node61 : Node61 (ctx := ctx))
    (node63 : Node63 node61) (port : Port node61 node63) :
    (anchoredReturn node61 node63 port).path ctx.G.object
      node63.typeAProfile |>.IsPath :=
  (anchoredReturn node61 node63 port).isPath ctx.G.object node63.typeAProfile

theorem anchoredReturn_avoids_port (node61 : Node61 (ctx := ctx))
    (node63 : Node63 node61) (port : Port node61 node63) :
    s((port.receiver ctx.G.object node63.typeAProfile).1,
        port.outside ctx.G.object node63.typeAProfile) ∉
      (Graph.EdgeRootedReturn.ambientPath
        (anchoredReturn node61 node63 port).returnPath.toEdgeRootedReturn).edges :=
  (anchoredReturn node61 node63 port).avoids_port_edge ctx.G.object
    node63.typeAProfile

end Erdos64EG.Internal.TypeAAnchoredReturnCoordinates
