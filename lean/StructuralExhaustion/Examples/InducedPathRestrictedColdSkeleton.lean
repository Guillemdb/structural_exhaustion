import StructuralExhaustion.Graph.InducedPathRestrictedColdSkeleton

namespace StructuralExhaustion.Examples.InducedPathRestrictedColdSkeleton

open StructuralExhaustion.Graph

universe u

variable {V : Type u} {object : FiniteObject V}
variable (family :
  InducedPathRestrictedColdSkeleton.CubicWindowFamily object)
variable (stub : InducedPathColdCorridor.CubicStub object)
variable (windowMem : stub.window ∈ family.windows)

example :
    (∃ boundary tokenExact,
      InducedPathRestrictedColdSkeleton.route family stub windowMem =
        .componentBoundary boundary tokenExact) ∨
    (∃ residual,
      InducedPathRestrictedColdSkeleton.route family stub windowMem =
        .crossWindow residual) :=
  InducedPathRestrictedColdSkeleton.route_exhaustive family stub windowMem

end StructuralExhaustion.Examples.InducedPathRestrictedColdSkeleton

