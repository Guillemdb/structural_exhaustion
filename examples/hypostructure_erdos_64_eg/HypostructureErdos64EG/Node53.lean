import HypostructureErdos64EG.Node52

namespace HypostructureErdos64EG

open Hypostructure

universe u

structure Node53Contract (Previous : Type u) where
  profile : Previous -> Core.OrderThresholdSplit.Profile Nat

abbrev Node53Large (contract : Node53Contract Previous) (stage : Previous) : Prop :=
  (contract.profile stage).threshold < (contract.profile stage).value

abbrev Node53Small (contract : Node53Contract Previous) (stage : Previous) : Prop :=
  (contract.profile stage).value ≤ (contract.profile stage).threshold

abbrev Node53Stage (contract : Node53Contract Previous) :=
  Core.Residual.Decision.Stage (Node53Large contract) (Node53Small contract)

noncomputable def node53 (contract : Node53Contract Previous)
    (previous : Previous) : Node53Stage contract :=
  let decision : Core.Residual.Decision.Node _
      (Node53Large contract) (Node53Small contract) :=
    Core.Residual.Decision.Node.create
      (fun _ => by classical exact inferInstance)
      (fun _ absent => le_of_not_gt absent)
  decision.run previous

end HypostructureErdos64EG
