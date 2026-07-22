import HypostructureErdos64EG.Node40

namespace HypostructureErdos64EG

open Hypostructure

universe u

structure Node41Contract (Previous : Type u) where
  profile : Previous -> Core.OrderThresholdSplit.Profile Nat

abbrev Node41Proper (contract : Node41Contract Previous) (stage : Previous) : Prop :=
  (contract.profile stage).threshold < (contract.profile stage).value

abbrev Node41Whole (contract : Node41Contract Previous) (stage : Previous) : Prop :=
  (contract.profile stage).value ≤ (contract.profile stage).threshold

abbrev Node41Stage (contract : Node41Contract Previous) :=
  Core.Residual.Decision.Stage (Node41Proper contract) (Node41Whole contract)

noncomputable def node41 (contract : Node41Contract Previous)
    (previous : Previous) : Node41Stage contract :=
  let decision : Core.Residual.Decision.Node _
      (Node41Proper contract) (Node41Whole contract) :=
    Core.Residual.Decision.Node.create
      (fun _ => by classical exact inferInstance)
      (fun _ absent => le_of_not_gt absent)
  decision.run previous

end HypostructureErdos64EG
