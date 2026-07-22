import HypostructureErdos64EG.Node39

namespace HypostructureErdos64EG

open Hypostructure

universe u v

structure Node40SupportContract (Previous : Type u) (Support : Previous -> Type v) where
  support : ∀ previous, Support previous

noncomputable def node40Support
    (contract : Node40SupportContract Previous Support)
    (previous : Previous) :
    Core.Residual.Ledger.Extension Previous Support :=
  Core.Residual.Ledger.extend previous (contract.support previous)

abbrev Node40Stage (contract : Node38Contract Previous) := Node38Stage contract
abbrev Node40Output (contract : Node38Contract Previous) : Type v := PUnit

end HypostructureErdos64EG
