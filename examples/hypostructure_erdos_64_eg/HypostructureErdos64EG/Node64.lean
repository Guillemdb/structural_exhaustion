import HypostructureErdos64EG.Node63

namespace HypostructureErdos64EG

open Hypostructure

universe u v w

structure Node64ResidualContract (Previous : Type u) (Residual : Previous -> Type w) where
  produce : (previous : Previous) -> Residual previous

abbrev Node64Stage (contract : Node62Contract Previous)
    (Handoff : Node62Stage contract -> Type v)
    (Residual : Node63Stage contract Handoff -> Type w) :=
  Core.Residual.Ledger.Extension (Node63Stage contract Handoff) Residual

noncomputable def node64 (contract : Node62Contract Previous)
    (Handoff : Node62Stage contract -> Type v)
    (Residual : Node63Stage contract Handoff -> Type w)
    (previous : Node63Stage contract Handoff) (residual : Residual previous) :
    Node64Stage contract Handoff Residual :=
  Core.Residual.Ledger.extend previous residual

noncomputable def node64FromContract
    (contract : Node64ResidualContract (Node63Stage node62Contract Handoff) Residual)
    (previous : Node63Stage node62Contract Handoff) :
    Node64Stage node62Contract Handoff Residual :=
  node64 node62Contract Handoff Residual previous (contract.produce previous)

end HypostructureErdos64EG
