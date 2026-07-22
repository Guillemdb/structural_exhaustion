import HypostructureErdos64EG.Node146

namespace HypostructureErdos64EG

open Hypostructure

universe u v

abbrev Node147Stage (contract : Node146Contract Previous)
    (Route : Node146Stage contract -> Type v) :=
  Core.Residual.Ledger.Extension (Node146Stage contract) Route

noncomputable def node147 (contract : Node146Contract Previous)
    (Route : Node146Stage contract -> Type v)
    (previous : Node146Stage contract) (route : Route previous) :
    Node147Stage contract Route :=
  Core.Residual.Ledger.extend previous route

end HypostructureErdos64EG
