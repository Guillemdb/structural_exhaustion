import HypostructureErdos64EG.Node23

namespace HypostructureErdos64EG

open Hypostructure

universe u w x y

structure Node24Contract (Table : Type w) (Index : Type x) where
  remainder : Type y
  certificate : remainder

abbrev Node24Stage (contract : Node22Contract Previous Table Index)
    (Remainder : Type y) :=
  Core.Residual.Ledger.Extension (Node22Stage contract)
    (fun _stage => Remainder)

noncomputable def node24 (contract : Node22Contract Previous Table Index)
    (remainder : Type y) (value : remainder)
    (previous : Node22Stage contract) : Node24Stage contract remainder :=
  Core.Residual.Ledger.extend previous value

noncomputable def node24Certified
    (contract : Node22Contract Previous Table Index)
    (certificate : Node24Contract Table Index)
    (previous : Node22Stage contract) : Node24Stage contract certificate.remainder :=
  Core.Residual.Ledger.extend previous certificate.certificate

end HypostructureErdos64EG
