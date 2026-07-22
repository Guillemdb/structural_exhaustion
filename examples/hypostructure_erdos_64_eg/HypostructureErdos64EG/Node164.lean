import HypostructureErdos64EG.Node163

namespace HypostructureErdos64EG
open Hypostructure
universe u v

abbrev Node164Stage (Previous : Type u) (Package : Previous -> Type v) :=
  Core.Residual.Ledger.Extension Previous Package

noncomputable def node164 (Previous : Type u) (Package : Previous -> Type v)
    (previous : Previous) (package : Package previous) : Node164Stage Previous Package :=
  Core.Residual.Ledger.extend previous package

end HypostructureErdos64EG
