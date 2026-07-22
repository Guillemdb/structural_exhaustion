import HypostructureErdos64EG.Node42
import Hypostructure.Graph.SupportComponents

namespace HypostructureErdos64EG

open Hypostructure

universe u v

structure Node43ComponentContract (Previous : Type u) (Vertex : Previous -> Type v) where
  object : Core.Residual.Query Previous (fun previous =>
    Graph.FiniteObject.{v})
  support : Core.Residual.Query Previous (fun previous =>
    Finset (object.read previous).Vertex)

abbrev Node43Components
    (contract : Node43ComponentContract Previous Vertex)
    (previous : Previous) :=
  List (Graph.SupportComponents.Connected.Component
    (contract.object.read previous) (contract.support.read previous))

noncomputable def node43Components
    (contract : Node43ComponentContract Previous Vertex) (previous : Previous) :
    Core.Residual.Ledger.Extension Previous (Node43Components contract) :=
  Core.Residual.Ledger.extend previous
    (Graph.SupportComponents.Connected.order
      (contract.object.read previous) (contract.support.read previous))

abbrev Node43Stage (contract : Node41Contract Previous)
    (Fact : Node41Stage contract -> Type v) :=
  Core.Residual.Ledger.Extension (Node41Stage contract) Fact

noncomputable def node43 (contract : Node41Contract Previous)
    (Fact : Node41Stage contract -> Type v)
    (previous : Node41Stage contract) (fact : Fact previous) :
    Node43Stage contract Fact :=
  Core.Residual.Ledger.extend previous fact

end HypostructureErdos64EG
