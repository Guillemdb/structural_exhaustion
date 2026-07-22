import HypostructureErdos64EG.Node62

namespace HypostructureErdos64EG

open Hypostructure

universe u v

structure Node63HandoffContract (Previous : Type u) (Handoff : Previous -> Type v) where
  produce : (previous : Previous) -> Handoff previous

abbrev Node63Stage (contract : Node62Contract Previous)
    (Handoff : Node62Stage contract -> Type v) :=
  Core.Residual.Ledger.Extension (Node62Stage contract) Handoff

noncomputable def node63 (contract : Node62Contract Previous)
    (Handoff : Node62Stage contract -> Type v)
    (previous : Node62Stage contract) (handoff : Handoff previous) :
    Node63Stage contract Handoff :=
  Core.Residual.Ledger.extend previous handoff

noncomputable def node63FromContract
    (contract : Node63HandoffContract (Node62Stage node62Contract) Handoff)
    (previous : Node62Stage node62Contract) :
    Node63Stage node62Contract Handoff :=
  node63 node62Contract Handoff previous (contract.produce previous)

end HypostructureErdos64EG
