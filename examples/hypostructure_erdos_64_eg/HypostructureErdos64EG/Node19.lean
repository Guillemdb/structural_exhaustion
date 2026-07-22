import Hypostructure.Core.OrderThresholdSplit
import HypostructureErdos64EG.Node18

namespace HypostructureErdos64EG

open Hypostructure

universe u

structure Node19Contract (Previous : Type u) where
  profile : Previous -> Core.OrderThresholdSplit.Profile Nat

abbrev Node19High (contract : Node19Contract Previous) (stage : Previous) : Prop :=
  (contract.profile stage).threshold < (contract.profile stage).value

abbrev Node19Low (contract : Node19Contract Previous) (stage : Previous) : Prop :=
  (contract.profile stage).value ≤ (contract.profile stage).threshold

abbrev Node19Stage (contract : Node19Contract Table) :=
  Core.Residual.Decision.Stage (Node19High contract) (Node19Low contract)

noncomputable def node19 (contract : Node19Contract Previous)
    (previous : Previous) : Node19Stage contract :=
  let profile := contract.profile previous
  let decision : Core.Residual.Decision.Node _
      (Node19High contract) (Node19Low contract) :=
    Core.Residual.Decision.Node.create
      (fun _ => by classical exact inferInstance)
      (fun _ absent => le_of_not_gt absent)
  decision.run previous

end HypostructureErdos64EG
