import Hypostructure.Core.OrderThresholdSplit
import HypostructureErdos64EG.Node21

namespace HypostructureErdos64EG

open Hypostructure

universe u w x

structure Node22Contract (Previous : Type u) (Table : Type w) (Index : Type x) where
  base : Node19Contract Previous
  profile : Node21Stage base Table Index ->
    Core.OrderThresholdSplit.Profile Nat

abbrev Node22High (contract : Node22Contract Previous Table Index)
    (stage : Node21Stage contract.base Table Index) : Prop :=
  (contract.profile stage).threshold < (contract.profile stage).value

abbrev Node22Low (contract : Node22Contract Previous Table Index)
    (stage : Node21Stage contract.base Table Index) : Prop :=
  (contract.profile stage).value ≤ (contract.profile stage).threshold

abbrev Node22Stage (contract : Node22Contract Previous Table Index) :=
  Core.Residual.Decision.Stage (Node22High contract) (Node22Low contract)

noncomputable def node22 (contract : Node22Contract Previous Table Index)
    (previous : Node21Stage contract.base Table Index) : Node22Stage contract :=
  let decision : Core.Residual.Decision.Node _
      (Node22High contract) (Node22Low contract) :=
    Core.Residual.Decision.Node.create
      (fun _ => by classical exact inferInstance)
      (fun _ absent => le_of_not_gt absent)
  decision.run previous

end HypostructureErdos64EG
