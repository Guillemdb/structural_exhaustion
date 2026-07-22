import HypostructureErdos64EG.Node44

namespace HypostructureErdos64EG

open Hypostructure

universe u v w x

structure Node45BarrierContract (Previous : Type u) (Barrier : Previous -> Prop) where
  barrier : ∀ previous, Barrier previous

theorem node45_barrier
    (contract : Node45BarrierContract Previous Barrier) (previous : Previous) :
    Barrier previous :=
  contract.barrier previous

abbrev Node45Stage (contract : Node41Contract Previous)
    (Fact : Node41Stage contract -> Type v)
    (Repair : Node43Stage contract Fact -> Type w)
    (Barrier : Node44Stage contract Fact Repair -> Type x) :=
  Core.Residual.Ledger.Extension (Node44Stage contract Fact Repair) Barrier

noncomputable def node45 (contract : Node41Contract Previous)
    (Fact : Node41Stage contract -> Type v)
    (Repair : Node43Stage contract Fact -> Type w)
    (Barrier : Node44Stage contract Fact Repair -> Type x)
    (previous : Node44Stage contract Fact Repair) (barrier : Barrier previous) :
    Node45Stage contract Fact Repair Barrier :=
  Core.Residual.Ledger.extend previous barrier

end HypostructureErdos64EG
