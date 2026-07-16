import StructuralExhaustion.Graph.InducedPathColdBranchExcess

namespace StructuralExhaustion.Examples.InducedPathColdBranchExcess

open StructuralExhaustion.Graph
open StructuralExhaustion.Graph.InducedPathWindowLedger
open StructuralExhaustion.Graph.InducedPathColdLedger
open StructuralExhaustion.Graph.InducedPathColdBranchExcess

universe u

variable {V : Type u}
variable (object : FiniteObject V) (window : WindowIndex object)

/-- Graph-generic transfer check for the exact thirteen-stub producer. -/
example (cubic : AmbientCubic object window) :
    (branchExcessStubs object window cubic).length = 13 ∧
      (branchExcessStubs object window cubic).Nodup ∧
      ∀ stub ∈ branchExcessStubs object window cubic,
        stub.window = window :=
  ⟨branchExcessStubs_length_eq_thirteen object window cubic,
    branchExcessStubs_nodup object window cubic,
    branchExcessStubs_same_window object window cubic⟩

end StructuralExhaustion.Examples.InducedPathColdBranchExcess
