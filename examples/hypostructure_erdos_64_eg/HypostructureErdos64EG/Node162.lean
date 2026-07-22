import HypostructureErdos64EG.Node161

namespace HypostructureErdos64EG
open Hypostructure
universe u v

abbrev Node162Stage (Previous : Type u) (Residual : Previous -> Type v) :=
  Core.Residual.Ledger.Extension Previous Residual

noncomputable def node162 (Previous : Type u) (Residual : Previous -> Type v)
    (previous : Previous) (residual : Residual previous) : Node162Stage Previous Residual :=
  Core.Residual.Ledger.extend previous residual

end HypostructureErdos64EG
