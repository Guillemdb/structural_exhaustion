import HypostructureErdos64EG.Node157

namespace HypostructureErdos64EG
open Hypostructure
universe u v

structure Node158Contract (Previous : Type u) where
  scale : Previous -> Nat
  bounded : Previous -> Prop
  bounded_of_scale : ∀ previous, bounded previous

abbrev Node158Stage (contract : Node158Contract Previous) :=
  Core.Residual.Ledger.Extension Previous (fun previous => contract.bounded previous)

noncomputable def node158 (contract : Node158Contract Previous) (previous : Previous) :
    Node158Stage contract :=
  Core.Residual.Ledger.extend previous (contract.bounded_of_scale previous)

end HypostructureErdos64EG
