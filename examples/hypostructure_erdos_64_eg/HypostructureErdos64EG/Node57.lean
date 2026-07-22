import HypostructureErdos64EG.Node56

namespace HypostructureErdos64EG

open Hypostructure

universe u v w x

abbrev Node57Stage (contract : Node53Contract Previous)
    (Terminal : Node53Stage contract -> Type v)
    (ResidualC : Node54Stage contract Terminal -> Type w)
    (Cap : Node55Stage contract Terminal ResidualC -> Type x)
    (Net : Node56Stage contract Terminal ResidualC Cap -> Type u) :=
  Core.Residual.Ledger.Extension (Node56Stage contract Terminal ResidualC Cap) Net

noncomputable def node57 (contract : Node53Contract Previous)
    (Terminal : Node53Stage contract -> Type v)
    (ResidualC : Node54Stage contract Terminal -> Type w)
    (Cap : Node55Stage contract Terminal ResidualC -> Type x)
    (Net : Node56Stage contract Terminal ResidualC Cap -> Type u)
    (previous : Node56Stage contract Terminal ResidualC Cap)
    (net : Net previous) : Node57Stage contract Terminal ResidualC Cap Net :=
  Core.Residual.Ledger.extend previous net

end HypostructureErdos64EG
