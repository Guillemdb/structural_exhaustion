import HypostructureErdos64EG.Node155

namespace HypostructureErdos64EG
open Hypostructure
universe u v w x y z a

structure Node156Contract (Previous : Type u) where
  event : Previous -> Prop
  event_decidable : DecidablePred event

abbrev Node156Stage (contract : Node156Contract Previous) :=
  Core.Residual.Decision.Stage (contract.event) (fun previous => ¬ contract.event previous)

noncomputable def node156 (contract : Node156Contract Previous) (previous : Previous) :
    Node156Stage contract :=
  Core.Residual.Decision.Node.create contract.event_decidable
    (fun _ absent => absent) |>.run previous

end HypostructureErdos64EG
