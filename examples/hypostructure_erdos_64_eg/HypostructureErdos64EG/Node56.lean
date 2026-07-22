import HypostructureErdos64EG.Node55
import Hypostructure.Core.Budget.Dynamic

namespace HypostructureErdos64EG

open Hypostructure

universe u v w x

structure Node56CapContract (Previous : Type u) (Quantity : Type v)
    [Preorder Quantity] where
  profile : Core.Budget.Dynamic.Profile Previous Quantity

theorem node56_cap_within [Preorder Quantity]
    (contract : Node56CapContract Previous Quantity) (previous : Previous) :
    contract.profile.current previous <= contract.profile.limit previous :=
  contract.profile.current_le_limit previous

abbrev Node56Stage (contract : Node53Contract Previous)
    (Terminal : Node53Stage contract -> Type v)
    (ResidualC : Node54Stage contract Terminal -> Type w)
    (Cap : Node55Stage contract Terminal ResidualC -> Type x) :=
  Core.Residual.Ledger.Extension
    (Node55Stage contract Terminal ResidualC) Cap

noncomputable def node56 (contract : Node53Contract Previous)
    (Terminal : Node53Stage contract -> Type v)
    (ResidualC : Node54Stage contract Terminal -> Type w)
    (Cap : Node55Stage contract Terminal ResidualC -> Type x)
    (previous : Node55Stage contract Terminal ResidualC) (cap : Cap previous) :
    Node56Stage contract Terminal ResidualC Cap :=
  Core.Residual.Ledger.extend previous cap

end HypostructureErdos64EG
