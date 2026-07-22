import HypostructureErdos64EG.Node26

namespace HypostructureErdos64EG

open Hypostructure

universe u w x y z

abbrev Node27Stage (contract : Node22Contract Previous Table Index)
    (Remainder : Type y) (Fact : Node26Stage contract Remainder -> Type z) :=
  Core.Residual.Ledger.Extension (Node26Stage contract Remainder) Fact

noncomputable def node27 (contract : Node22Contract Previous Table Index)
    (remainder : Type y) (Fact : Node26Stage contract remainder -> Type z)
    (previous : Node26Stage contract remainder) (fact : Fact previous) :
    Node27Stage contract remainder Fact :=
  Core.Residual.Ledger.extend previous fact

end HypostructureErdos64EG
