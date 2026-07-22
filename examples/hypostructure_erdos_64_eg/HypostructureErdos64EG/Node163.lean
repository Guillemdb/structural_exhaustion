import HypostructureErdos64EG.Node162

namespace HypostructureErdos64EG
open Hypostructure
universe u v

structure Node163Contract (Previous : Type u) where
  package : Previous -> Type v
  package_of_good : ∀ previous, Nonempty (package previous)

abbrev Node163Stage (contract : Node163Contract Previous) :=
  Core.Residual.Ledger.Extension Previous contract.package

noncomputable def node163 (contract : Node163Contract Previous) (previous : Previous) :
    Node163Stage contract :=
  Core.Residual.Ledger.extend previous
    (Classical.choice (contract.package_of_good previous))

end HypostructureErdos64EG
