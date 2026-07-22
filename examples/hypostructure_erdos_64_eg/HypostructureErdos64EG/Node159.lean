import HypostructureErdos64EG.Node158

namespace HypostructureErdos64EG
open Hypostructure
universe u v w

structure Node159Contract (Previous : Type u) where
  candidate : Previous -> Type v
  admissible : (previous : Previous) -> candidate previous -> Prop
  witness : ∀ previous, Nonempty (candidate previous)
  witness_admissible : ∀ previous, ∃ candidate, admissible previous candidate

abbrev Node159Stage (contract : Node159Contract Previous) :=
  Core.Residual.Ledger.Extension Previous
    (fun previous => ∃ candidate, contract.admissible previous candidate)

noncomputable def node159 (contract : Node159Contract Previous) (previous : Previous) :
    Node159Stage contract :=
  Core.Residual.Ledger.extend previous (contract.witness_admissible previous)

end HypostructureErdos64EG
