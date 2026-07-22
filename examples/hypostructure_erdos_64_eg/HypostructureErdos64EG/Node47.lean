import HypostructureErdos64EG.Node46

namespace HypostructureErdos64EG

open Hypostructure

universe u v w x

structure Node47FullRankContract (Previous : Type u) (Ledger : Previous -> Type v) where
  ledger : ∀ previous, Ledger previous

noncomputable def node47FullRank
    (contract : Node41Contract Previous)
    (Fact : Node41Stage contract -> Type v)
    (Repair : Node43Stage contract Fact -> Type w)
    (Barrier : Node44Stage contract Fact Repair -> Type x)
    (FullRank : Node45Stage contract Fact Repair Barrier -> Type u)
    (ledger : Node47FullRankContract
      (Node45Stage contract Fact Repair Barrier) FullRank)
    (previous : Node45Stage contract Fact Repair Barrier) :
    Core.Residual.Ledger.Extension
      (Node45Stage contract Fact Repair Barrier) FullRank :=
  Core.Residual.Ledger.extend previous (ledger.ledger previous)

abbrev Node47Stage (contract : Node41Contract Previous)
    (Fact : Node41Stage contract -> Type v)
    (Repair : Node43Stage contract Fact -> Type w)
    (Barrier : Node44Stage contract Fact Repair -> Type x)
    (FullRank : Node45Stage contract Fact Repair Barrier -> Type u) :=
  Core.Residual.Ledger.Extension
    (Node45Stage contract Fact Repair Barrier) FullRank

noncomputable def node47 (contract : Node41Contract Previous)
    (Fact : Node41Stage contract -> Type v)
    (Repair : Node43Stage contract Fact -> Type w)
    (Barrier : Node44Stage contract Fact Repair -> Type x)
    (FullRank : Node45Stage contract Fact Repair Barrier -> Type u)
    (previous : Node45Stage contract Fact Repair Barrier)
    (fullRank : FullRank previous) :
    Node47Stage contract Fact Repair Barrier FullRank :=
  Core.Residual.Ledger.extend previous fullRank

end HypostructureErdos64EG
