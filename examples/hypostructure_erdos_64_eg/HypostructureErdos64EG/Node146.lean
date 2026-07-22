import HypostructureErdos64EG.Node145

namespace HypostructureErdos64EG

open Hypostructure

universe u

structure Node146Contract (Previous : Type u) where
  profile : Previous -> Core.OrderThresholdSplit.Profile Nat

abbrev Node146BelowThreshold (contract : Node146Contract Previous)
    (stage : Previous) : Prop :=
  (contract.profile stage).threshold < (contract.profile stage).value

abbrev Node146AtMostThreshold (contract : Node146Contract Previous)
    (stage : Previous) : Prop :=
  (contract.profile stage).value ≤ (contract.profile stage).threshold

abbrev Node146Stage (contract : Node146Contract Previous) :=
  Core.Residual.Decision.Stage (Node146BelowThreshold contract)
    (Node146AtMostThreshold contract)

noncomputable def node146 (contract : Node146Contract Previous)
    (previous : Previous) : Node146Stage contract :=
  let decision : Core.Residual.Decision.Node _
      (Node146BelowThreshold contract) (Node146AtMostThreshold contract) :=
    Core.Residual.Decision.Node.create
      (fun _ => by classical exact inferInstance)
      (fun _ absent => le_of_not_gt absent)
  decision.run previous

end HypostructureErdos64EG
