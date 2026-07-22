import HypostructureErdos64EG.Node24

namespace HypostructureErdos64EG

open Hypostructure

universe u w x y

structure Node25Output (Remainder : Type y) where
  remainder : Remainder

structure Node25Contract (Remainder : Type y) where
  certificate : Remainder

abbrev Node25Stage (contract : Node22Contract Previous Table Index)
    (Remainder : Type y) :=
  Core.Residual.Ledger.Extension (Node24Stage contract Remainder)
    (fun _stage => Node25Output Remainder)

noncomputable def node25 (contract : Node22Contract Previous Table Index)
    (remainder : Type y) (value : remainder)
    (previous : Node24Stage contract remainder) : Node25Stage contract remainder :=
  Core.Residual.Ledger.extend previous { remainder := value }

noncomputable def node25Certified
    (contract : Node22Contract Previous Table Index)
    (remainder : Type y) (certificate : Node25Contract remainder)
    (previous : Node24Stage contract remainder) : Node25Stage contract remainder :=
  Core.Residual.Ledger.extend previous { remainder := certificate.certificate }

end HypostructureErdos64EG
