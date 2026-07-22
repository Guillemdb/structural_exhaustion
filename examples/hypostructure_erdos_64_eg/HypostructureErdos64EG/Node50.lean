import HypostructureErdos64EG.Node49

namespace HypostructureErdos64EG

open Hypostructure

universe u

structure Node50Contract (Previous : Type u) where
  profile : Previous -> Core.OrderThresholdSplit.Profile Nat

abbrev Node50High (contract : Node50Contract Previous) (stage : Previous) : Prop :=
  (contract.profile stage).threshold < (contract.profile stage).value

abbrev Node50Low (contract : Node50Contract Previous) (stage : Previous) : Prop :=
  (contract.profile stage).value ≤ (contract.profile stage).threshold

abbrev Node50Stage (contract : Node50Contract Previous) :=
  Core.Residual.Decision.Stage (Node50High contract) (Node50Low contract)

noncomputable def node50 (contract : Node50Contract Previous)
    (previous : Previous) : Node50Stage contract :=
  let decision : Core.Residual.Decision.Node _
      (Node50High contract) (Node50Low contract) :=
    Core.Residual.Decision.Node.create
      (fun _ => by classical exact inferInstance)
      (fun _ absent => le_of_not_gt absent)
  decision.run previous

end HypostructureErdos64EG
