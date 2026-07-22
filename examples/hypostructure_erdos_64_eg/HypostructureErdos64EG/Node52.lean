import HypostructureErdos64EG.Node51

namespace HypostructureErdos64EG

open Hypostructure

universe u v

abbrev Node52Stage (contract : Node50Contract Previous)
    (Budget : Node50Stage contract -> Type v) :=
  Core.Residual.Ledger.Extension (Node50Stage contract) Budget

noncomputable def node52 (contract : Node50Contract Previous)
    (Budget : Node50Stage contract -> Type v)
    (previous : Node50Stage contract) (budget : Budget previous) :
    Node52Stage contract Budget :=
  Core.Residual.Ledger.extend previous budget

end HypostructureErdos64EG
