import HypostructureErdos64EG.Node47
import Hypostructure.Core.Budget.Dynamic

namespace HypostructureErdos64EG

open Hypostructure

universe u v w x y

structure Node48CostContract (Previous : Type u) (Quantity : Type v)
    [Preorder Quantity] where
  profile : Core.Budget.Dynamic.Profile Previous Quantity

abbrev Node48Stage (contract : Node41Contract Previous)
    (Fact : Node41Stage contract -> Type v)
    (Repair : Node43Stage contract Fact -> Type w)
    (Barrier : Node44Stage contract Fact Repair -> Type x)
    (FullRank : Node45Stage contract Fact Repair Barrier -> Type u)
    (Cost : Node47Stage contract Fact Repair Barrier FullRank -> Type y) :=
  Core.Residual.Ledger.Extension
    (Node47Stage contract Fact Repair Barrier FullRank) Cost

noncomputable def node48 (contract : Node41Contract Previous)
    (Fact : Node41Stage contract -> Type v)
    (Repair : Node43Stage contract Fact -> Type w)
    (Barrier : Node44Stage contract Fact Repair -> Type x)
    (FullRank : Node45Stage contract Fact Repair Barrier -> Type u)
    (Cost : Node47Stage contract Fact Repair Barrier FullRank -> Type y)
    (previous : Node47Stage contract Fact Repair Barrier FullRank)
    (cost : Cost previous) :
    Node48Stage contract Fact Repair Barrier FullRank Cost :=
  Core.Residual.Ledger.extend previous cost

end HypostructureErdos64EG
