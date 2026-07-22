import HypostructureErdos64EG.Node25

namespace HypostructureErdos64EG

open Hypostructure

universe u w x y

abbrev Node26Stage (contract : Node22Contract Previous Table Index)
    (Remainder : Type y) := Node25Stage contract Remainder

abbrev Node26Entry (contract : Node22Contract Previous Table Index)
    (Remainder : Type y) := Node26Stage contract Remainder

end HypostructureErdos64EG
