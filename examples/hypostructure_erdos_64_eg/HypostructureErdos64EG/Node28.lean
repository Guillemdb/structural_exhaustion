import HypostructureErdos64EG.Node27

namespace HypostructureErdos64EG

open Hypostructure

universe u w x y z a

abbrev Node28Stage (contract : Node22Contract Previous Table Index)
    (Remainder : Type y) (Fact : Node26Stage contract Remainder -> Type z)
    (Next : Node27Stage contract Remainder Fact -> Type a) :=
  Core.Residual.Ledger.Extension (Node27Stage contract Remainder Fact) Next

noncomputable def node28 (contract : Node22Contract Previous Table Index)
    (remainder : Type y) (Fact : Node26Stage contract remainder -> Type z)
    (Next : Node27Stage contract remainder Fact -> Type a)
    (previous : Node27Stage contract remainder Fact) (fact : Next previous) :
    Node28Stage contract remainder Fact Next :=
  Core.Residual.Ledger.extend previous fact

end HypostructureErdos64EG
