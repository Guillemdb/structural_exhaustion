import HypostructureErdos64EG.Node64

namespace HypostructureErdos64EG

open Hypostructure

universe u v

abbrev Node145Stage (Previous : Type u) (Interface : Previous -> Type v) :=
  Core.Residual.Ledger.Extension Previous Interface

noncomputable def node145 (previous : Previous)
    (Interface : Previous -> Type v) (interface : Interface previous) :
    Node145Stage Previous Interface :=
  Core.Residual.Ledger.extend previous interface

end HypostructureErdos64EG
