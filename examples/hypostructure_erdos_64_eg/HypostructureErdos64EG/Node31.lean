import HypostructureErdos64EG.Node30

namespace HypostructureErdos64EG

open Hypostructure

universe u w x y z a b c d

abbrev Node31Stage (contract : Node22Contract Previous Table Index)
    (Remainder : Type y) (Fact : Node26Stage contract Remainder -> Type z)
    (Next : Node27Stage contract Remainder Fact -> Type a)
    (Final : Node28Stage contract Remainder Fact Next -> Type b)
    (Transport : Node29Stage contract Remainder Fact Next Final -> Type c)
    (Rank : Node30Stage contract Remainder Fact Next Final Transport -> Type d) :=
  Core.Residual.Ledger.Extension
    (Node30Stage contract Remainder Fact Next Final Transport) Rank

noncomputable def node31 (contract : Node22Contract Previous Table Index)
    (remainder : Type y) (Fact : Node26Stage contract remainder -> Type z)
    (Next : Node27Stage contract remainder Fact -> Type a)
    (Final : Node28Stage contract remainder Fact Next -> Type b)
    (Transport : Node29Stage contract remainder Fact Next Final -> Type c)
    (Rank : Node30Stage contract remainder Fact Next Final Transport -> Type d)
    (previous : Node30Stage contract remainder Fact Next Final Transport)
    (fact : Rank previous) :
    Node31Stage contract remainder Fact Next Final Transport Rank :=
  Core.Residual.Ledger.extend previous fact

end HypostructureErdos64EG
