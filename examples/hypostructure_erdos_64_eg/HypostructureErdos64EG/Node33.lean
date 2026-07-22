import HypostructureErdos64EG.Node32

namespace HypostructureErdos64EG

open Hypostructure

universe u v

abbrev Node33Stage (contract : Node32Contract Previous) := Node32Stage contract

abbrev Node33Output (contract : Node32Contract Previous)
    (stage : Node32Stage contract) : Type v := PUnit

noncomputable def node33 (contract : Node32Contract Previous)
    (previous : Node32Stage contract) : Node33Stage contract := previous

end HypostructureErdos64EG
