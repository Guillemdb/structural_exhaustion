import StructuralExhaustion.Graph.InducedPathComponentD4D7OrCoarseRepeat

namespace StructuralExhaustion.Graph.InducedPathComponentD4D7SemanticReadiness

open StructuralExhaustion
open InducedPathColdSkeleton

universe u

variable {V : Type u} {object : FiniteObject V}
variable
  (input : InducedPathComponentD1D3Ledger.Input object)
  (anchorState : InducedPathComponentD1D3Ledger.State)
  (LengthOK : Nat → Prop)
  (lengthOKDecidable : DecidablePred LengthOK)

/-!
# Exact semantic-readiness fork after the component D4--D7 classifier

The preceding classifier has three syntactic constructors, but its purported
complete-reconstruction constructor is uninhabited for the current graph
profile: every actual schedule contains its anchor row, while the graph layer
has derived no D4--D7 clause for that row.  This module removes that impossible
constructor and retains the exact obstruction already carried by either
remaining predecessor residual.

This is deliberately not CT8.  Equality of coarse D1--D3 states supplies
neither a compatible-response family nor a smaller-object operation.
-/

abbrev PriorResult :=
  InducedPathComponentD4D7OrCoarseRepeat.Result input anchorState LengthOK
    lengthOKDecidable

structure Source where
  node175 : PriorResult input anchorState LengthOK lengthOKDecidable
  node175Exact : node175 =
    InducedPathComponentD4D7OrCoarseRepeat.run input anchorState LengthOK
      lengthOKDecidable
      (InducedPathComponentD4D7OrCoarseRepeat.computedSource input anchorState
        LengthOK lengthOKDecidable)

noncomputable def computedSource :
    Source input anchorState LengthOK lengthOKDecidable where
  node175 := InducedPathComponentD4D7OrCoarseRepeat.run input anchorState
    LengthOK lengthOKDecidable
    (InducedPathComponentD4D7OrCoarseRepeat.computedSource input anchorState
      LengthOK lengthOKDecidable)
  node175Exact := rfl

theorem anchor_mem_stubs :
    InducedPathComponentD1D3Ledger.anchorStub input ∈
      InducedPathComponentD1D3Ledger.stubs input := by
  simp [InducedPathComponentD1D3Ledger.stubs,
    InducedPathComponentD1D3Ledger.anchorStub]

/-- A complete family is impossible because its anchor-row clause would
inhabit the intentionally constructor-free graph derivation status. -/
theorem reconstructed_impossible
    (family : InducedPathComponentD4D7OrCoarseRepeat.ReconstructedFamily input) :
    False := by
  have derived := family.value
    (InducedPathComponentD1D3Ledger.anchorStub input) (anchor_mem_stubs input)
  exact nomatch derived

structure CoarseBlocked where
  residual :
    InducedPathComponentD4D7OrCoarseRepeat.CoarseRepeatResidual input
      anchorState LengthOK lengthOKDecidable
  firstMissing : Nonempty (TwoStubComponent.MissingD4D7Reconstruction
    (InducedPathComponentD1D3Observation.data residual.repetition.firstInput)
    residual.repetition.firstPath)
  secondMissing : Nonempty (TwoStubComponent.MissingD4D7Reconstruction
    (InducedPathComponentD1D3Observation.data residual.repetition.secondInput)
    residual.repetition.secondPath)

structure BoundedBlocked where
  bounded : InducedPathComponentD4D7OrCoarseRepeat.BoundedResidual input
    anchorState LengthOK lengthOKDecidable
  residual :
    InducedPathComponentD4D7OrCoarseRepeat.FirstMissingReconstruction input
  missing : Nonempty (TwoStubComponent.MissingD4D7Reconstruction
    (InducedPathComponentD1D3Observation.data
      (InducedPathComponentD1D3Ledger.connectorInput input residual.scan.row))
    (InducedPathComponentD1D3Observation.canonicalPath
      (InducedPathComponentD1D3Ledger.connectorInput input residual.scan.row)))

inductive Result where
  | coarseBlocked
      (blocked : CoarseBlocked input anchorState LengthOK lengthOKDecidable)
  | boundedBlocked
      (blocked : BoundedBlocked input anchorState LengthOK lengthOKDecidable)

/-- Inspect only the already computed predecessor constructor and retain its
local missing-clause witnesses. -/
noncomputable def run
    (source : Source input anchorState LengthOK lengthOKDecidable) :
    Result input anchorState LengthOK lengthOKDecidable := by
  cases source.node175 with
  | coarseRepeat residual =>
      exact .coarseBlocked {
        residual := residual
        firstMissing := residual.firstMissingD4D7
        secondMissing := residual.secondMissingD4D7
      }
  | boundedReconstructed _bounded family =>
      exact (reconstructed_impossible input family).elim
  | boundedFirstMissing bounded residual =>
      exact .boundedBlocked {
        bounded := bounded
        residual := residual
        missing := residual.marker
      }

theorem source_exact
    (source : Source input anchorState LengthOK lengthOKDecidable) :
    source.node175 =
      InducedPathComponentD4D7OrCoarseRepeat.run input anchorState LengthOK
        lengthOKDecidable
        (InducedPathComponentD4D7OrCoarseRepeat.computedSource input anchorState
          LengthOK lengthOKDecidable) := source.node175Exact

theorem run_exhaustive
    (source : Source input anchorState LengthOK lengthOKDecidable) :
    (∃ blocked, run input anchorState LengthOK lengthOKDecidable source =
      .coarseBlocked blocked) ∨
    (∃ blocked, run input anchorState LengthOK lengthOKDecidable source =
      .boundedBlocked blocked) := by
  cases equation : run input anchorState LengthOK lengthOKDecidable source with
  | coarseBlocked blocked => exact Or.inl ⟨blocked, rfl⟩
  | boundedBlocked blocked => exact Or.inr ⟨blocked, rfl⟩

/-- One constructor inspection; all graph work belongs to the predecessor. -/
def visibleChecks : Nat := 1

theorem visibleChecks_linear :
    visibleChecks ≤ InducedPathComponentD1D3Ledger.localScale input + 1 := by
  unfold visibleChecks
  omega

end StructuralExhaustion.Graph.InducedPathComponentD4D7SemanticReadiness
