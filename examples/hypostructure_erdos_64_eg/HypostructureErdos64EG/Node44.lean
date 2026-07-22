import HypostructureErdos64EG.Node43

namespace HypostructureErdos64EG

open Hypostructure

universe u v w

structure Node44RepairContract (Previous : Type u) (Repair : Previous -> Prop) where
  identity : ∀ previous, Repair previous

theorem node44_repair_identity
    (contract : Node44RepairContract Previous Repair) (previous : Previous) :
    Repair previous :=
  contract.identity previous

abbrev Node44Stage (contract : Node41Contract Previous)
    (Fact : Node41Stage contract -> Type v)
    (Repair : Node43Stage contract Fact -> Type w) :=
  Core.Residual.Ledger.Extension (Node43Stage contract Fact) Repair

noncomputable def node44 (contract : Node41Contract Previous)
    (Fact : Node41Stage contract -> Type v)
    (Repair : Node43Stage contract Fact -> Type w)
    (previous : Node43Stage contract Fact) (repair : Repair previous) :
    Node44Stage contract Fact Repair :=
  Core.Residual.Ledger.extend previous repair

end HypostructureErdos64EG
