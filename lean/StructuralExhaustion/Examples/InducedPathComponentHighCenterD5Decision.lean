import StructuralExhaustion.Graph.InducedPathComponentHighCenterD5Decision

namespace StructuralExhaustion.Examples.InducedPathComponentHighCenterD5Decision

open StructuralExhaustion.Graph

example :
    InducedPathComponentHighCenterD5Decision.missingTypeAFacts =
      [.p13FreeOnSupport, .internalCoreFree] := rfl

example :
    InducedPathComponentHighCenterD5Decision.missingTypeAFacts.Nodup :=
  InducedPathComponentHighCenterD5Decision.missingTypeAFacts_nodup

end StructuralExhaustion.Examples.InducedPathComponentHighCenterD5Decision
