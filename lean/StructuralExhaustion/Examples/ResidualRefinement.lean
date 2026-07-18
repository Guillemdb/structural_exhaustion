import StructuralExhaustion.Core.ResidualRefinement

namespace StructuralExhaustion.Examples.ResidualRefinement

open StructuralExhaustion

structure Residual where
  value : Nat
  positive : 0 < value

def IsPositive (residual : Residual) : Prop :=
  0 < residual.value

def SquarePositive (residual : Residual) : Prop :=
  0 < residual.value * residual.value

def Nonzero (residual : Residual) : Prop :=
  residual.value ≠ 0

noncomputable def positiveNode :
    Core.ResidualRefinement.State.Node (facts := []) IsPositive where
  prove := fun state => state.residual.positive

noncomputable def squareNode :
    Core.ResidualRefinement.State.Node
      (facts := [IsPositive]) SquarePositive where
  prove := fun state => Nat.mul_pos state.latest state.latest

noncomputable def nonzeroNode :
    Core.ResidualRefinement.State.Node
      (facts := [SquarePositive, IsPositive]) Nonzero where
  prove := fun state => Nat.ne_of_gt (state.get (.there .here))

noncomputable def seed : Residual := ⟨2, by omega⟩

noncomputable def initialState :=
  Core.ResidualRefinement.State.initial seed

noncomputable def afterPositive := positiveNode.run initialState
noncomputable def afterSquare := squareNode.run afterPositive
noncomputable def afterNonzero := nonzeroNode.run afterSquare

theorem all_properties_accumulated :
    IsPositive afterNonzero.residual ∧
      SquarePositive afterNonzero.residual ∧
      Nonzero afterNonzero.residual := by
  exact ⟨afterNonzero.get (.there (.there .here)),
    afterNonzero.get (.there .here), afterNonzero.latest⟩

noncomputable def firstOccurrence :
    Core.FiniteResidualLedger.Ledger Residual :=
  .singleton seed

noncomputable def secondOccurrence :
    Core.FiniteResidualLedger.Ledger Residual :=
  .singleton seed

noncomputable def occurrences :
    Core.FiniteResidualLedger.Ledger Residual :=
  firstOccurrence.append secondOccurrence

noncomputable def positiveProducer :
    Core.ResidualRefinement.Ledger.Producer Residual IsPositive where
  emit := id
  prove := fun residual => residual.positive

/-- The producer route starts with its theorem already installed, so the next
node consumes a current state rather than reconstructing provenance. -/
noncomputable def producedLedger :=
  Core.ResidualRefinement.Ledger.produce occurrences positiveProducer

noncomputable def producedThenSquared :=
  producedLedger.refine squareNode

theorem produced_chain_retains_origin
    (occurrence : producedThenSquared.residuals.Occurrence) :
    IsPositive (producedThenSquared.residuals.event occurrence) ∧
      SquarePositive (producedThenSquared.residuals.event occurrence) := by
  let state := producedThenSquared.state occurrence
  exact ⟨state.get (.there .here), state.latest⟩

noncomputable def initialLedger :=
  Core.ResidualRefinement.Ledger.initial occurrences

noncomputable def refinedLedger :=
  ((initialLedger.refine positiveNode).refine squareNode).refine nonzeroNode

theorem occurrence_identity_preserved :
    refinedLedger.residuals.Occurrence = occurrences.Occurrence :=
  rfl

theorem every_occurrence_has_all_properties
    (occurrence : refinedLedger.residuals.Occurrence) :
    IsPositive (refinedLedger.residuals.event occurrence) ∧
      SquarePositive (refinedLedger.residuals.event occurrence) ∧
      Nonzero (refinedLedger.residuals.event occurrence) := by
  let state := refinedLedger.state occurrence
  exact ⟨state.get (.there (.there .here)), state.get (.there .here),
    state.latest⟩

#print axioms all_properties_accumulated
#print axioms occurrence_identity_preserved
#print axioms every_occurrence_has_all_properties
#print axioms produced_chain_retains_origin

end StructuralExhaustion.Examples.ResidualRefinement
