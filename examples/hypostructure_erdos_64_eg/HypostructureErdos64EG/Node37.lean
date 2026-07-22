import HypostructureErdos64EG.Node36

namespace HypostructureErdos64EG

universe u v

abbrev Node37Stage (contract : Node32Contract Previous)
    (Circuit : Node32Stage contract -> Type u)
    (Audit : Node35Stage contract Circuit -> Type v) :=
  Node36Stage contract Circuit Audit

end HypostructureErdos64EG
