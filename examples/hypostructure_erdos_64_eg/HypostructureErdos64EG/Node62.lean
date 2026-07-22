import HypostructureErdos64EG.Node61

namespace HypostructureErdos64EG

open Hypostructure

universe u

structure Node62Contract (Previous : Type u) where
  profile : Previous -> Core.OrderThresholdSplit.Profile Nat

abbrev Node62HighSurplus (contract : Node62Contract Previous) (stage : Previous) : Prop :=
  (contract.profile stage).threshold < (contract.profile stage).value

abbrev Node62NoHighSurplus (contract : Node62Contract Previous) (stage : Previous) : Prop :=
  (contract.profile stage).value ≤ (contract.profile stage).threshold

abbrev Node62Stage (contract : Node62Contract Previous) :=
  Core.Residual.Decision.Stage (Node62HighSurplus contract) (Node62NoHighSurplus contract)

noncomputable def node62 (contract : Node62Contract Previous)
    (previous : Previous) : Node62Stage contract :=
  let decision : Core.Residual.Decision.Node _
      (Node62HighSurplus contract) (Node62NoHighSurplus contract) :=
    Core.Residual.Decision.Node.create
      (fun _ => by classical exact inferInstance)
      (fun _ absent => le_of_not_gt absent)
  decision.run previous

end HypostructureErdos64EG
