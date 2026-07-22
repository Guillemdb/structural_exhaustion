import HypostructureErdos64EG.Node159

namespace HypostructureErdos64EG
open Hypostructure
universe u

structure Node160Contract (Previous : Type u) where
  good : Previous -> Prop
  good_decidable : DecidablePred good

abbrev Node160Stage (contract : Node160Contract Previous) :=
  Core.Residual.Decision.Stage contract.good (fun previous => ¬ contract.good previous)

noncomputable def node160 (contract : Node160Contract Previous) (previous : Previous) :
    Node160Stage contract :=
  Core.Residual.Decision.Node.create contract.good_decidable
    (fun _ absent => absent) |>.run previous

end HypostructureErdos64EG
