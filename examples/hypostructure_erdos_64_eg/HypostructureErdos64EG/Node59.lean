import HypostructureErdos64EG.Node58

namespace HypostructureErdos64EG

open Hypostructure

universe u

structure Node59Contract (Previous : Type u) where
  profile : Previous -> Core.OrderThresholdSplit.Profile Nat

abbrev Node59Nonnegative (contract : Node59Contract Previous) (stage : Previous) : Prop :=
  (contract.profile stage).threshold < (contract.profile stage).value

abbrev Node59Negative (contract : Node59Contract Previous) (stage : Previous) : Prop :=
  (contract.profile stage).value ≤ (contract.profile stage).threshold

abbrev Node59Stage (contract : Node59Contract Previous) :=
  Core.Residual.Decision.Stage (Node59Nonnegative contract) (Node59Negative contract)

noncomputable def node59 (contract : Node59Contract Previous)
    (previous : Previous) : Node59Stage contract :=
  let decision : Core.Residual.Decision.Node _
      (Node59Nonnegative contract) (Node59Negative contract) :=
    Core.Residual.Decision.Node.create
      (fun _ => by classical exact inferInstance)
      (fun _ absent => le_of_not_gt absent)
  decision.run previous

end HypostructureErdos64EG
