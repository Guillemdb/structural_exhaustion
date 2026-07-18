import StructuralExhaustion.Graph.InducedPathRestrictedPrefixCompletion

namespace StructuralExhaustion.Examples.InducedPathRestrictedPrefixCompletion

open StructuralExhaustion
open StructuralExhaustion.Graph
open StructuralExhaustion.Graph.InducedPathRestrictedColdSkeleton
open StructuralExhaustion.Graph.InducedPathRestrictedComponentBoundarySchedule

universe u

variable {V : Type u} {object : FiniteObject V}
variable {family : CubicWindowFamily object}

/-- Non-Erdős transfer surface: the reusable restricted-prefix predicate
always transfers to the public cycle-existence contract. -/
theorem completion_transfers
    (input : Input family) (LengthOK : Nat → Prop)
    (stage : InducedPathRestrictedPrefixCompletion.Stage input)
    (offset : Fin 13)
    (hit : InducedPathRestrictedPrefixCompletion.CompletionAt input LengthOK
      stage offset) :
    HasCycleWithLength object.graph LengthOK :=
  ⟨InducedPathRestrictedPrefixCompletion.cycleOfCompletion input LengthOK
    stage offset hit⟩

end StructuralExhaustion.Examples.InducedPathRestrictedPrefixCompletion
