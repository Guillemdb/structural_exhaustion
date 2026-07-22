import HypostructureErdos64EG.Node156

namespace HypostructureErdos64EG
open Hypostructure
universe u v

abbrev Node157Stage (Previous : Type u) (Germ : Previous -> Type v) :=
  Core.Residual.Ledger.Extension Previous Germ

noncomputable def node157 (Previous : Type u) (Germ : Previous -> Type v)
    (previous : Previous) (germ : Germ previous) : Node157Stage Previous Germ :=
  Core.Residual.Ledger.extend previous germ

end HypostructureErdos64EG
