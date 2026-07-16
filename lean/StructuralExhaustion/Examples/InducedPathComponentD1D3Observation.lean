import StructuralExhaustion.Graph.InducedPathComponentD1D3Observation

namespace StructuralExhaustion.Examples.ComponentD1D3Observation

open StructuralExhaustion
open StructuralExhaustion.Graph
open StructuralExhaustion.Graph.InducedPathColdSkeleton
open StructuralExhaustion.Graph.InducedPathComponentBoundarySchedule
open StructuralExhaustion.Graph.InducedPathComponentD1D3Observation

universe u

variable {V : Type u} {object : FiniteObject V}

/-! Theorem-independent transfer of the one-state component observation. -/

structure Source (object : FiniteObject V) where
  input : InducedPathComponentBoundarySchedule.Input object

namespace Source

noncomputable def result (source : Source object)
    (LengthOK : Nat → Prop) (lengthOKDecidable : DecidablePred LengthOK) :=
  InducedPathComponentD1D3Observation.run source.input LengthOK
    lengthOKDecidable

theorem exact_two_boundary_observation (source : Source object)
    (LengthOK : Nat → Prop) (lengthOKDecidable : DecidablePred LengthOK) :
    (source.result LengthOK lengthOKDecidable).value.boundaryDegree 0 =
        Core.FixedTwoBoundaryCutState.capDegree
          (object.degree source.input.anchor.neighbor) ∧
      (source.result LengthOK lengthOKDecidable).value.windowOffset 1 =
        (twoStubComponent source.input).successor.offset :=
  ⟨boundaryDegree_zero source.input LengthOK lengthOKDecidable,
    windowOffset_one source.input LengthOK lengthOKDecidable⟩

theorem stops_at_missing_d4_d7 (source : Source object)
    (LengthOK : Nat → Prop) (lengthOKDecidable : DecidablePred LengthOK) :
    Nonempty (TwoStubComponent.MissingD4D7Reconstruction (data source.input)
      (canonicalPath source.input)) :=
  ⟨(source.result LengthOK lengthOKDecidable).missing⟩

theorem exact_local_work (source : Source object) :
    InducedPathComponentD1D3Observation.visibleChecks source.input =
      2 * object.input.vertices.card + 13 :=
  InducedPathComponentD1D3Observation.visibleChecks_eq source.input

theorem local_work_linear (source : Source object) :
    InducedPathComponentD1D3Observation.visibleChecks source.input ≤
      15 * (object.input.vertices.card + 1) :=
  InducedPathComponentD1D3Observation.visibleChecks_linear source.input

end Source

end StructuralExhaustion.Examples.ComponentD1D3Observation
