import HypostructureErdos64EG.Node57
import Hypostructure.Core.Budget.Dynamic

namespace HypostructureErdos64EG

open Hypostructure

universe u v w x y

structure Node58ChargeContract (Previous : Type u) (Quantity : Type v)
    [Preorder Quantity] where
  profile : Core.Budget.Dynamic.Profile Previous Quantity

theorem node58_charge_within [Preorder Quantity]
    (contract : Node58ChargeContract Previous Quantity) (previous : Previous) :
    contract.profile.current previous <= contract.profile.limit previous :=
  contract.profile.current_le_limit previous

abbrev Node58Stage (contract : Node53Contract Previous)
    (Terminal : Node53Stage contract -> Type v)
    (ResidualC : Node54Stage contract Terminal -> Type w)
    (Cap : Node55Stage contract Terminal ResidualC -> Type x)
    (Net : Node56Stage contract Terminal ResidualC Cap -> Type u)
    (Charge : Node57Stage contract Terminal ResidualC Cap Net -> Type y) :=
  Core.Residual.Ledger.Extension (Node57Stage contract Terminal ResidualC Cap Net) Charge

noncomputable def node58 (contract : Node53Contract Previous)
    (Terminal : Node53Stage contract -> Type v)
    (ResidualC : Node54Stage contract Terminal -> Type w)
    (Cap : Node55Stage contract Terminal ResidualC -> Type x)
    (Net : Node56Stage contract Terminal ResidualC Cap -> Type u)
    (Charge : Node57Stage contract Terminal ResidualC Cap Net -> Type y)
    (previous : Node57Stage contract Terminal ResidualC Cap Net)
    (charge : Charge previous) : Node58Stage contract Terminal ResidualC Cap Net Charge :=
  Core.Residual.Ledger.extend previous charge

end HypostructureErdos64EG
