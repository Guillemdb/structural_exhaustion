import HypostructureErdos64EG.Node152

namespace HypostructureErdos64EG

open Hypostructure

universe u v w x y z a b

abbrev Node153Stage (contract : Node146Contract Previous)
    (Route : Node146Stage contract -> Type v)
    (Private : Node147Stage contract Route -> Type w)
    (Audit : Node148Stage contract Route Private -> Type x)
    (Cold : Node149Stage contract Route Private Audit -> Type y)
    (Filter : Node150Stage contract Route Private Audit Cold -> Type z)
    (Stubs : Node151Stage contract Route Private Audit Cold Filter -> Type a)
    (Scan : Node152Stage contract Route Private Audit Cold Filter Stubs -> Type b) :=
  Core.Residual.Ledger.Extension (Node152Stage contract Route Private Audit Cold Filter Stubs) Scan

noncomputable def node153 (contract : Node146Contract Previous)
    (Route : Node146Stage contract -> Type v)
    (Private : Node147Stage contract Route -> Type w)
    (Audit : Node148Stage contract Route Private -> Type x)
    (Cold : Node149Stage contract Route Private Audit -> Type y)
    (Filter : Node150Stage contract Route Private Audit Cold -> Type z)
    (Stubs : Node151Stage contract Route Private Audit Cold Filter -> Type a)
    (Scan : Node152Stage contract Route Private Audit Cold Filter Stubs -> Type b)
    (previous : Node152Stage contract Route Private Audit Cold Filter Stubs) (scan : Scan previous) :
    Node153Stage contract Route Private Audit Cold Filter Stubs Scan :=
  Core.Residual.Ledger.extend previous scan

end HypostructureErdos64EG
