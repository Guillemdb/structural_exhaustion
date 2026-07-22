import HypostructureErdos64EG.Node29

namespace HypostructureErdos64EG

open Hypostructure

universe u w x y z a b c

structure Node30TransportContract (Previous : Type u) (Quantity : Type w)
    [Preorder Quantity] where
  budget : Node29BudgetContract Previous Quantity
  transported : Previous -> Quantity
  transport_within : ∀ previous,
    transported previous <= budget.profile.budget.read previous

abbrev Node30Stage (contract : Node22Contract Previous Table Index)
    (Remainder : Type y) (Fact : Node26Stage contract Remainder -> Type z)
    (Next : Node27Stage contract Remainder Fact -> Type a)
    (Final : Node28Stage contract Remainder Fact Next -> Type b)
    (Transport : Node29Stage contract Remainder Fact Next Final -> Type c) :=
  Core.Residual.Ledger.Extension
    (Node29Stage contract Remainder Fact Next Final) Transport

noncomputable def node30 (contract : Node22Contract Previous Table Index)
    (remainder : Type y) (Fact : Node26Stage contract remainder -> Type z)
    (Next : Node27Stage contract remainder Fact -> Type a)
    (Final : Node28Stage contract remainder Fact Next -> Type b)
    (Transport : Node29Stage contract remainder Fact Next Final -> Type c)
    (previous : Node29Stage contract remainder Fact Next Final)
    (fact : Transport previous) :
    Node30Stage contract remainder Fact Next Final Transport :=
  Core.Residual.Ledger.extend previous fact

end HypostructureErdos64EG
