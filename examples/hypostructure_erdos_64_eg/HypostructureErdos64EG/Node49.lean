import HypostructureErdos64EG.Node48

namespace HypostructureErdos64EG

open Hypostructure

universe u v w x y z

structure Node49EntropyContract (Previous : Type u) (Quantity : Type v)
    [Preorder Quantity] where
  profile : Core.Budget.Dynamic.Profile Previous Quantity

theorem node49_entropy_within [Preorder Quantity]
    (contract : Node49EntropyContract Previous Quantity) (previous : Previous) :
    contract.profile.current previous <= contract.profile.limit previous :=
  contract.profile.current_le_limit previous

abbrev Node49Stage (contract : Node41Contract Previous)
    (Fact : Node41Stage contract -> Type v)
    (Repair : Node43Stage contract Fact -> Type w)
    (Barrier : Node44Stage contract Fact Repair -> Type x)
    (FullRank : Node45Stage contract Fact Repair Barrier -> Type u)
    (Cost : Node47Stage contract Fact Repair Barrier FullRank -> Type y)
    (Entropy : Node48Stage contract Fact Repair Barrier FullRank Cost -> Type z) :=
  Core.Residual.Ledger.Extension
    (Node48Stage contract Fact Repair Barrier FullRank Cost) Entropy

noncomputable def node49 (contract : Node41Contract Previous)
    (Fact : Node41Stage contract -> Type v)
    (Repair : Node43Stage contract Fact -> Type w)
    (Barrier : Node44Stage contract Fact Repair -> Type x)
    (FullRank : Node45Stage contract Fact Repair Barrier -> Type u)
    (Cost : Node47Stage contract Fact Repair Barrier FullRank -> Type y)
    (Entropy : Node48Stage contract Fact Repair Barrier FullRank Cost -> Type z)
    (previous : Node48Stage contract Fact Repair Barrier FullRank Cost)
    (entropy : Entropy previous) :
    Node49Stage contract Fact Repair Barrier FullRank Cost Entropy :=
  Core.Residual.Ledger.extend previous entropy

end HypostructureErdos64EG
