import HypostructureErdos64EG.Node37

namespace HypostructureErdos64EG

open Hypostructure

universe u v

structure Node38Contract (Previous : Type u) where
  profile : Previous -> Core.OrderThresholdSplit.Profile Nat

abbrev Node38AtOriginal (contract : Node38Contract Previous) (stage : Previous) : Prop :=
  (contract.profile stage).threshold < (contract.profile stage).value

abbrev Node38Enlarged (contract : Node38Contract Previous) (stage : Previous) : Prop :=
  (contract.profile stage).value ≤ (contract.profile stage).threshold

abbrev Node38Stage (contract : Node38Contract Previous) :=
  Core.Residual.Decision.Stage (Node38AtOriginal contract) (Node38Enlarged contract)

noncomputable def node38 (contract : Node38Contract Previous)
    (previous : Previous) : Node38Stage contract :=
  let decision : Core.Residual.Decision.Node _
      (Node38AtOriginal contract) (Node38Enlarged contract) :=
    Core.Residual.Decision.Node.create
      (fun _ => by classical exact inferInstance)
      (fun _ absent => le_of_not_gt absent)
  decision.run previous

end HypostructureErdos64EG
