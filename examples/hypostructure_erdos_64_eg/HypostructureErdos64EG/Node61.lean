import HypostructureErdos64EG.Node60
import Hypostructure.Graph.SupportComponents

namespace HypostructureErdos64EG

open Hypostructure

universe u v w

/-! The connected-support decomposition is a Graph adapter over the generic
finite partition and CT11 machines.  All inputs are predecessor queries. -/
structure Node61ComponentContract (Previous : Type u) (Vertex : Previous -> Type v) where
  object : Core.Residual.Query Previous (fun _ => Graph.FiniteObject.{v})
  support : Core.Residual.Query Previous (fun previous =>
    Finset (object.read previous).Vertex)

abbrev Node61Components
    (contract : Node61ComponentContract Previous Vertex) (previous : Previous) :=
  List (Graph.SupportComponents.Connected.Component
    (contract.object.read previous) (contract.support.read previous))

noncomputable def node61Components
    (contract : Node61ComponentContract Previous Vertex) (previous : Previous) :
    Core.Residual.Ledger.Extension Previous (Node61Components contract) :=
  Core.Residual.Ledger.extend previous
    (Graph.SupportComponents.Connected.order
      (contract.object.read previous) (contract.support.read previous))

abbrev Node61Stage (contract : Node59Contract Previous)
    (Closed : Node59Stage contract -> Type v)
    (Components : Node60Stage contract Closed -> Type w) :=
  Core.Residual.Ledger.Extension (Node60Stage contract Closed) Components

noncomputable def node61 (contract : Node59Contract Previous)
    (Closed : Node59Stage contract -> Type v)
    (Components : Node60Stage contract Closed -> Type w)
    (previous : Node60Stage contract Closed) (components : Components previous) :
    Node61Stage contract Closed Components :=
  Core.Residual.Ledger.extend previous components

end HypostructureErdos64EG
