import StructuralExhaustion.Examples.InducedPathComponentD4D7OrCoarseRepeat
import StructuralExhaustion.Graph.InducedPathComponentD4D7SemanticReadiness

namespace StructuralExhaustion.Examples.ComponentD4D7SemanticReadiness

open StructuralExhaustion
open StructuralExhaustion.Graph
open StructuralExhaustion.Graph.InducedPathColdSkeleton

universe u

variable {V : Type u} {object : FiniteObject V}
variable (source : ComponentD1D3Ledger.Source object)
variable (LengthOK : Nat → Prop)
variable (lengthOKDecidable : DecidablePred LengthOK)

noncomputable def input :=
  InducedPathComponentD4D7SemanticReadiness.computedSource source.input
    (source.anchorState LengthOK lengthOKDecidable) LengthOK lengthOKDecidable

noncomputable def result :=
  InducedPathComponentD4D7SemanticReadiness.run source.input
    (source.anchorState LengthOK lengthOKDecidable) LengthOK lengthOKDecidable
    (input source LengthOK lengthOKDecidable)

set_option maxHeartbeats 800000 in
theorem exact_predecessor :
    (input source LengthOK lengthOKDecidable).node175 =
      InducedPathComponentD4D7OrCoarseRepeat.run source.input
        (source.anchorState LengthOK lengthOKDecidable) LengthOK
        lengthOKDecidable
        (InducedPathComponentD4D7OrCoarseRepeat.computedSource source.input
          (source.anchorState LengthOK lengthOKDecidable) LengthOK
          lengthOKDecidable) := rfl

example : InducedPathComponentD1D3Ledger.anchorStub source.input ∈
    InducedPathComponentD1D3Ledger.stubs source.input :=
  InducedPathComponentD4D7SemanticReadiness.anchor_mem_stubs source.input

example
    (family : InducedPathComponentD4D7OrCoarseRepeat.ReconstructedFamily
      source.input) : False :=
  InducedPathComponentD4D7SemanticReadiness.reconstructed_impossible
    source.input family

example
    (blocked : InducedPathComponentD4D7SemanticReadiness.CoarseBlocked
      source.input (source.anchorState LengthOK lengthOKDecidable) LengthOK
      lengthOKDecidable) :
    Nonempty (TwoStubComponent.MissingD4D7Reconstruction
      (InducedPathComponentD1D3Observation.data
        blocked.residual.repetition.firstInput)
      blocked.residual.repetition.firstPath) :=
  blocked.firstMissing

example
    (blocked : InducedPathComponentD4D7SemanticReadiness.CoarseBlocked
      source.input (source.anchorState LengthOK lengthOKDecidable) LengthOK
      lengthOKDecidable) :
    Nonempty (TwoStubComponent.MissingD4D7Reconstruction
      (InducedPathComponentD1D3Observation.data
        blocked.residual.repetition.secondInput)
      blocked.residual.repetition.secondPath) :=
  blocked.secondMissing

example
    (blocked : InducedPathComponentD4D7SemanticReadiness.BoundedBlocked
      source.input (source.anchorState LengthOK lengthOKDecidable) LengthOK
      lengthOKDecidable) :
    Nonempty (TwoStubComponent.MissingD4D7Reconstruction
      (InducedPathComponentD1D3Observation.data
        (InducedPathComponentD1D3Ledger.connectorInput source.input
          blocked.residual.scan.row))
      (InducedPathComponentD1D3Observation.canonicalPath
        (InducedPathComponentD1D3Ledger.connectorInput source.input
          blocked.residual.scan.row))) :=
  blocked.missing

set_option maxHeartbeats 800000 in
theorem result_exhaustive :
    (∃ blocked, result source LengthOK lengthOKDecidable =
      .coarseBlocked blocked) ∨
    (∃ blocked, result source LengthOK lengthOKDecidable =
      .boundedBlocked blocked) :=
  InducedPathComponentD4D7SemanticReadiness.run_exhaustive source.input
    (source.anchorState LengthOK lengthOKDecidable) LengthOK lengthOKDecidable _

theorem local_work :
    InducedPathComponentD4D7SemanticReadiness.visibleChecks ≤
      InducedPathComponentD1D3Ledger.localScale source.input + 1 :=
  InducedPathComponentD4D7SemanticReadiness.visibleChecks_linear source.input

end StructuralExhaustion.Examples.ComponentD4D7SemanticReadiness
