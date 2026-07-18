import StructuralExhaustion.Graph.InducedPathRestrictedComponentBoundarySchedule

namespace StructuralExhaustion.Examples.InducedPathRestrictedComponentBoundarySchedule

open StructuralExhaustion.Graph

universe u

variable {V : Type u} {object : FiniteObject V}
variable {family : InducedPathRestrictedColdSkeleton.CubicWindowFamily object}
variable (input : InducedPathRestrictedComponentBoundarySchedule.Input family)

example :
    (InducedPathRestrictedComponentBoundarySchedule.successor input ≠ input.anchor) ∧
      InducedPathRestrictedColdSkeleton.component
          (InducedPathRestrictedComponentBoundarySchedule.successor input) =
        InducedPathRestrictedColdSkeleton.component input.anchor :=
  ⟨InducedPathRestrictedComponentBoundarySchedule.successor_distinct input,
    InducedPathRestrictedComponentBoundarySchedule.successor_same_component input⟩

example :
    (InducedPathRestrictedComponentBoundarySchedule.componentPath input).IsPath ∧
      (InducedPathRestrictedComponentBoundarySchedule.componentPath input).length =
        (InducedPathRestrictedColdSkeleton.component input.anchor).toSimpleGraph.dist
          (InducedPathRestrictedComponentBoundarySchedule.twoStubComponent input).componentRoot
          (InducedPathRestrictedComponentBoundarySchedule.twoStubComponent input).componentTarget :=
  ⟨InducedPathRestrictedComponentBoundarySchedule.componentPath_isPath input,
    InducedPathRestrictedComponentBoundarySchedule.componentPath_shortest input⟩

example :
    (InducedPathRestrictedComponentBoundarySchedule.componentPathDeclaredOrderCertificate
      input).path =
      InducedPathRestrictedComponentBoundarySchedule.componentPath input :=
  InducedPathRestrictedComponentBoundarySchedule.componentPathDeclaredOrderCertificate_path
    input

end StructuralExhaustion.Examples.InducedPathRestrictedComponentBoundarySchedule
