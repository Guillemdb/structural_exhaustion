import HypostructureErdos64EG.Node153

namespace HypostructureErdos64EG

open Hypostructure

universe u

structure Node154Contract (Previous : Type u) where
  profile : Previous -> Core.OrderThresholdSplit.Profile Nat

abbrev Node154Hit (contract : Node154Contract Previous) (stage : Previous) : Prop :=
  (contract.profile stage).threshold < (contract.profile stage).value

abbrev Node154NoHit (contract : Node154Contract Previous) (stage : Previous) : Prop :=
  (contract.profile stage).value ≤ (contract.profile stage).threshold

abbrev Node154Stage (contract : Node154Contract Previous) :=
  Core.Residual.Decision.Stage (Node154Hit contract) (Node154NoHit contract)

noncomputable def node154 (contract : Node154Contract Previous)
    (previous : Previous) : Node154Stage contract :=
  let decision : Core.Residual.Decision.Node _
      (Node154Hit contract) (Node154NoHit contract) :=
    Core.Residual.Decision.Node.create
      (fun _ => by classical exact inferInstance)
      (fun _ absent => le_of_not_gt absent)
  decision.run previous

end HypostructureErdos64EG
