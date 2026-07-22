import Hypostructure.Core.OrderThresholdSplit
import Hypostructure.CT15.Automation
import HypostructureErdos64EG.Node31

namespace HypostructureErdos64EG

open Hypostructure

universe u v

structure Node32CT15Contract (Previous : Type u)
    (Coordinate : Previous -> Type v) where
  spec : CT15.Spec.{u, v} Previous
  capability : CT15.Capability.{u, v} spec

abbrev Node32CT15Stage
    (contract : Node32CT15Contract Previous Coordinate) :=
  Core.Residual.Ledger.Extension Previous
    (fun previous => CT15.ExecutionResult contract.spec contract.capability)

noncomputable def node32CT15
    (contract : Node32CT15Contract Previous Coordinate) (previous : Previous) :
    Node32CT15Stage contract :=
  Core.Residual.Ledger.extend previous
    (CT15.execute contract.spec contract.capability previous)

structure Node32Contract (Previous : Type u) where
  profile : Previous -> Core.OrderThresholdSplit.Profile Nat

abbrev Node32RankDrop (contract : Node32Contract Previous) (stage : Previous) : Prop :=
  (contract.profile stage).threshold < (contract.profile stage).value

abbrev Node32FullRank (contract : Node32Contract Previous) (stage : Previous) : Prop :=
  (contract.profile stage).value ≤ (contract.profile stage).threshold

abbrev Node32Stage (contract : Node32Contract Previous) :=
  Core.Residual.Decision.Stage (Node32RankDrop contract) (Node32FullRank contract)

noncomputable def node32 (contract : Node32Contract Previous)
    (previous : Previous) : Node32Stage contract :=
  let decision : Core.Residual.Decision.Node _
      (Node32RankDrop contract) (Node32FullRank contract) :=
    Core.Residual.Decision.Node.create
      (fun _ => by classical exact inferInstance)
      (fun _ absent => le_of_not_gt absent)
  decision.run previous

end HypostructureErdos64EG
