import HypostructureErdos64EG.Node34

namespace HypostructureErdos64EG

open Hypostructure

universe u v

structure Node35CircuitContract (Previous : Type u) (Circuit : Previous -> Type v) where
  certificate : ∀ previous, Circuit previous

noncomputable def node35Certified
    (contract : Node32Contract Previous)
    (Circuit : Node32Stage contract -> Type v)
    (certificate : Node35CircuitContract (Node32Stage contract) Circuit)
    (previous : Node32Stage contract) :
    Core.Residual.Ledger.Extension (Node32Stage contract) Circuit :=
  Core.Residual.Ledger.extend previous (certificate.certificate previous)

abbrev Node35Stage (contract : Node32Contract Previous)
    (Circuit : Node32Stage contract -> Type v) :=
  Core.Residual.Ledger.Extension (Node32Stage contract) Circuit

noncomputable def node35 (contract : Node32Contract Previous)
    (Circuit : Node32Stage contract -> Type v)
    (previous : Node32Stage contract) (circuit : Circuit previous) :
    Node35Stage contract Circuit :=
  Core.Residual.Ledger.extend previous circuit

end HypostructureErdos64EG
