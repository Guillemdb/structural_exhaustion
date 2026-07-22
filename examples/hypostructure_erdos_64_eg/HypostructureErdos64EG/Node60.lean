import HypostructureErdos64EG.Node59

namespace HypostructureErdos64EG

open Hypostructure

universe u v

structure Node60ClosureContract (Previous : Type u) (Nonnegative : Previous -> Prop) where
  nonnegative : ∀ previous, Nonnegative previous
  contradiction : ∀ previous, Nonnegative previous -> False

theorem node60_close
    (contract : Node60ClosureContract Previous Nonnegative) (previous : Previous) : False :=
  contract.contradiction previous (contract.nonnegative previous)

abbrev Node60Stage (contract : Node59Contract Previous)
    (Closed : Node59Stage contract -> Type v) :=
  Core.Residual.Ledger.Extension (Node59Stage contract) Closed

noncomputable def node60 (contract : Node59Contract Previous)
    (Closed : Node59Stage contract -> Type v)
    (previous : Node59Stage contract) (closed : Closed previous) :
    Node60Stage contract Closed :=
  Core.Residual.Ledger.extend previous closed

end HypostructureErdos64EG
