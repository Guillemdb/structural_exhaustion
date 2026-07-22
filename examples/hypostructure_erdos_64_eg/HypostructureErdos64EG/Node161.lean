import HypostructureErdos64EG.Node160

namespace HypostructureErdos64EG
open Hypostructure
universe u v

abbrev Node161Stage (Previous : Type u) (Evidence : Previous -> Type v) :=
  Core.Residual.Ledger.Extension Previous Evidence

noncomputable def node161 (Previous : Type u) (Evidence : Previous -> Type v)
    (previous : Previous) (evidence : Evidence previous) : Node161Stage Previous Evidence :=
  Core.Residual.Ledger.extend previous evidence

end HypostructureErdos64EG
