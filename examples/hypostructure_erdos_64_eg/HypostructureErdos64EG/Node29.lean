import HypostructureErdos64EG.Node28
import Hypostructure.Core.Budget.Dynamic

namespace HypostructureErdos64EG

open Hypostructure

universe u w x y z a b

/-! Generic residual-owned net-budget certificate used by the panel branch.
The quantity is intentionally abstract: graph surplus and PDE energy use the
same Core profile. -/
structure Node29BudgetContract (Previous : Type u) (Quantity : Type w)
    [Preorder Quantity] where
  profile : Core.Budget.Dynamic.Profile Previous Quantity

theorem node29_budget_within {Previous : Type u} {Quantity : Type w}
    [Preorder Quantity] (contract : Node29BudgetContract Previous Quantity)
    (previous : Previous) :
    contract.profile.value.read previous <= contract.profile.budget.read previous :=
  contract.profile.within previous

abbrev Node29Stage (contract : Node22Contract Previous Table Index)
    (Remainder : Type y) (Fact : Node26Stage contract Remainder -> Type z)
    (Next : Node27Stage contract Remainder Fact -> Type a)
    (Final : Node28Stage contract Remainder Fact Next -> Type b) :=
  Core.Residual.Ledger.Extension (Node28Stage contract Remainder Fact Next) Final

noncomputable def node29 (contract : Node22Contract Previous Table Index)
    (remainder : Type y) (Fact : Node26Stage contract remainder -> Type z)
    (Next : Node27Stage contract remainder Fact -> Type a)
    (Final : Node28Stage contract remainder Fact Next -> Type b)
    (previous : Node28Stage contract remainder Fact Next) (fact : Final previous) :
    Node29Stage contract remainder Fact Next Final :=
  Core.Residual.Ledger.extend previous fact

end HypostructureErdos64EG
