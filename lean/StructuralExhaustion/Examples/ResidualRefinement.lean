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

structure PositiveCertificate (residual : Residual) : Type where
  proof : IsPositive residual

instance : Core.ResidualRefinement.State.StageEntails
    PositiveCertificate IsPositive where
  prove certificate := certificate.proof

def canonicalPositiveCertificate (residual : Residual) :
    PositiveCertificate residual :=
  ⟨residual.positive⟩

abbrev ExactPositiveCertificate (residual : Residual) :=
  Core.ExactHandoff (canonicalPositiveCertificate residual)

structure PositiveSquareCertificate (residual : Residual) : Type where
  proof : SquarePositive residual

instance : Core.ResidualRefinement.State.StageEntails
    PositiveSquareCertificate SquarePositive where
  prove certificate := certificate.proof

structure NonzeroCertificate (residual : Residual) : Type where
  proof : Nonzero residual

instance : Core.ResidualRefinement.State.StageEntails
    NonzeroCertificate Nonzero where
  prove certificate := certificate.proof

structure CombinedCertificate (residual : Residual) : Type where
  positive : IsPositive residual
  nonzero : Nonzero residual

structure TripleCertificate (residual : Residual) : Type where
  positive : IsPositive residual
  nonzero : Nonzero residual
  squarePositive : SquarePositive residual

/-- A temporary named view assembled from the ledger.  It is consumed by a
node producer and is not part of that node's output. -/
structure CombinedInputs (residual : Residual) : Type where
  positive : PositiveCertificate residual
  nonzero : NonzeroCertificate residual

structure PositiveSuccessor (residual : Residual)
    (previous : PositiveCertificate residual) : Type where
  proof : IsPositive residual

abbrev PositiveDependentSuccessor (residual : Residual) :=
  Core.ResidualRefinement.State.DependentSuccessor
    PositiveCertificate PositiveSuccessor residual

abbrev PositiveYes (residual : Residual)
    (_certificate : PositiveCertificate residual) : Prop :=
  IsPositive residual

abbrev PositiveNo (residual : Residual)
    (_certificate : PositiveCertificate residual) : Prop :=
  ¬IsPositive residual

abbrev PositiveFirstContinuation (residual : Residual) :=
  Core.ResidualRefinement.State.DependentDecisionYesContinuation
    PositiveCertificate PositiveYes PositiveNo
    (fun residual certificate _proof => PositiveSuccessor residual certificate) residual

abbrev PositiveSecondContinuation (residual : Residual) :=
  Core.ResidualRefinement.State.DependentDecisionYesSuccessor
    PositiveCertificate PositiveYes PositiveNo
    (fun residual certificate _proof => PositiveSuccessor residual certificate)
    (fun residual _certificate _proof _current =>
      PositiveSquareCertificate residual) residual

noncomputable def positiveCertificateNode {facts} :
    Core.ResidualRefinement.State.StageNode
      (facts := facts) PositiveCertificate where
  produce := fun state => ⟨state.residual.positive⟩

noncomputable def exactPositiveCertificateNode {facts} :
    Core.ResidualRefinement.State.StageNode
      (facts := facts) ExactPositiveCertificate :=
  Core.ResidualRefinement.State.StageNode.exact
    canonicalPositiveCertificate

noncomputable def exactPositiveCertificateEcho {facts}
    [Core.ResidualRefinement.Proofs.Contains
      (Core.ResidualRefinement.State.Available ExactPositiveCertificate) facts] :
    Core.ResidualRefinement.State.StageNode
      (facts := facts) ExactPositiveCertificate :=
  Core.ResidualRefinement.State.StageNode.mapExactStage
    (expected := canonicalPositiveCertificate)
    (fun _residual previous => previous)

noncomputable def positiveSquareCertificateNode {facts}
    [Core.ResidualRefinement.Proofs.Contains IsPositive facts]
    [Core.ResidualRefinement.Proofs.Contains
      (Core.ResidualRefinement.State.Available PositiveCertificate) facts] :
  Core.ResidualRefinement.State.StageNode
      (facts := facts) PositiveSquareCertificate :=
  Core.ResidualRefinement.State.StageNode.usingFactAndStage
    (required := IsPositive) (Required := PositiveCertificate)
      fun _state positive certificate =>
      ⟨Nat.mul_pos positive certificate.proof⟩

noncomputable def nonzeroCertificateNode {facts} :
    Core.ResidualRefinement.State.StageNode
      (facts := facts) NonzeroCertificate where
  produce := fun state => ⟨Nat.ne_of_gt state.residual.positive⟩

noncomputable def combinedCertificateNode {facts}
    [Core.ResidualRefinement.Proofs.Contains
      (Core.ResidualRefinement.State.Available PositiveCertificate) facts]
    [Core.ResidualRefinement.Proofs.Contains
      (Core.ResidualRefinement.State.Available NonzeroCertificate) facts] :
    Core.ResidualRefinement.State.StageNode
      (facts := facts) CombinedCertificate :=
  Core.ResidualRefinement.State.StageNode.derive
    (((Core.ResidualRefinement.State.LedgerQuery.stage
        (facts := facts) (Stage := PositiveCertificate)).andStage
      (Stage := NonzeroCertificate)).map fun _residual inputs =>
        CombinedInputs.mk inputs.fst inputs.snd)
    fun _state inputs => ⟨inputs.positive.proof, inputs.nonzero.proof⟩

/-- The same combination through registered theorem projections. The
consumer never opens the earlier certificate structures. -/
noncomputable def combinedEntailedCertificateNode {facts}
    [Core.ResidualRefinement.Proofs.Contains
      (Core.ResidualRefinement.State.Available PositiveCertificate) facts]
    [Core.ResidualRefinement.Proofs.Contains
      (Core.ResidualRefinement.State.Available NonzeroCertificate) facts] :
    Core.ResidualRefinement.State.StageNode
      (facts := facts) CombinedCertificate :=
  Core.ResidualRefinement.State.StageNode.derive
    ((Core.ResidualRefinement.State.LedgerQuery.entailedStage
      (facts := facts) (Stage := PositiveCertificate)
      (property := IsPositive)).andEntailedStage
        (Stage := NonzeroCertificate) (property := Nonzero))
    fun _state inputs => ⟨inputs.fst, inputs.snd⟩

noncomputable def tripleCertificateNode {facts}
    [Core.ResidualRefinement.Proofs.Contains
      (Core.ResidualRefinement.State.Available PositiveCertificate) facts]
    [Core.ResidualRefinement.Proofs.Contains
      (Core.ResidualRefinement.State.Available NonzeroCertificate) facts]
    [Core.ResidualRefinement.Proofs.Contains
      (Core.ResidualRefinement.State.Available PositiveSquareCertificate) facts] :
    Core.ResidualRefinement.State.StageNode
      (facts := facts) TripleCertificate :=
  Core.ResidualRefinement.State.StageNode.derive
    (((Core.ResidualRefinement.State.LedgerQuery.stage
        (facts := facts) (Stage := PositiveCertificate)).andStage
      (Stage := NonzeroCertificate)).andStage
      (Stage := PositiveSquareCertificate))
    fun _state inputs =>
      ⟨inputs.fst.fst.proof, inputs.fst.snd.proof, inputs.snd.proof⟩

noncomputable def positiveDependentSuccessorNode {facts}
    [Core.ResidualRefinement.Proofs.Contains
      (Core.ResidualRefinement.State.Available PositiveCertificate) facts] :
    Core.ResidualRefinement.State.StageNode
      (facts := facts) PositiveDependentSuccessor :=
  Core.ResidualRefinement.State.StageNode.mapStage
    fun _residual previous => ⟨previous.proof⟩

noncomputable def positiveDecisionNode {facts}
    [Core.ResidualRefinement.Proofs.Contains
      (Core.ResidualRefinement.State.Available PositiveCertificate) facts] :
    Core.ResidualRefinement.State.StageNode (facts := facts)
      (Core.ResidualRefinement.State.DependentDecision
        PositiveCertificate PositiveYes PositiveNo) :=
  Core.ResidualRefinement.State.StageNode.decideUsingStage
    (fun residual _certificate => Classical.propDecidable (IsPositive residual))
    (fun _residual _certificate absent => absent)

noncomputable def positiveFirstContinuationNode {facts}
    [Core.ResidualRefinement.Proofs.Contains
    (Core.ResidualRefinement.State.Available
        (Core.ResidualRefinement.State.DependentDecision
          PositiveCertificate PositiveYes PositiveNo)) facts] :
    Core.ResidualRefinement.State.StageNode (facts := facts)
      PositiveFirstContinuation :=
  Core.ResidualRefinement.State.StageNode.continueDependentDecisionYes
    fun _residual certificate _positive => ⟨certificate.proof⟩

noncomputable def positiveSecondContinuationNode {facts}
    [Core.ResidualRefinement.Proofs.Contains
      (Core.ResidualRefinement.State.Available PositiveFirstContinuation) facts] :
    Core.ResidualRefinement.State.StageNode (facts := facts)
      PositiveSecondContinuation :=
  Core.ResidualRefinement.State.StageNode.continueDependentDecisionYesAgain
    fun _residual _certificate positive current =>
      ⟨Nat.mul_pos positive current.proof⟩

/-- The same branch continuation while retrieving an older mathematical fact
through its registered stage entailment. -/
noncomputable def positiveSecondContinuationFromEntailedNode {facts}
    [Core.ResidualRefinement.Proofs.Contains
      (Core.ResidualRefinement.State.Available PositiveFirstContinuation) facts]
    [Core.ResidualRefinement.Proofs.Contains
      (Core.ResidualRefinement.State.Available PositiveCertificate) facts] :
    Core.ResidualRefinement.State.StageNode (facts := facts)
      PositiveSecondContinuation :=
  Core.ResidualRefinement.State.StageNode.continueDependentDecisionYesAgainDerived
      (Core.ResidualRefinement.State.LedgerQuery.entailedStage
        (facts := facts) (Stage := PositiveCertificate)
        (property := IsPositive))
      fun _residual inherited _certificate _positive _current =>
        ⟨Nat.mul_pos inherited inherited⟩

/-- A genuinely predecessor-indexed output used to exercise simultaneous
fact retrieval and exact dependent transport. -/
structure PositiveCertificateEcho (residual : Residual)
    (certificate : PositiveCertificate residual) where
  positive : IsPositive residual

abbrev CanonicalPositiveCertificateEcho (residual : Residual) :=
  PositiveCertificateEcho residual (canonicalPositiveCertificate residual)

noncomputable def positiveCertificateEchoNode {facts}
    [Core.ResidualRefinement.Proofs.Contains IsPositive facts]
    [Core.ResidualRefinement.Proofs.Contains
      (Core.ResidualRefinement.State.Available ExactPositiveCertificate) facts] :
    Core.ResidualRefinement.State.StageNode
      (facts := facts) CanonicalPositiveCertificateEcho :=
  Core.ResidualRefinement.State.StageNode.usingFactAndExactStage
    (required := IsPositive)
    (expected := canonicalPositiveCertificate)
    (Next := fun residual _positive certificate =>
      PositiveCertificateEcho residual certificate)
    (fun _residual positive _certificate => ⟨positive⟩)
    (fun _residual _positive output => output)

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

/-- The same consumer using type-directed accumulated-fact lookup. -/
noncomputable def nonzeroNodeByType :
    Core.ResidualRefinement.State.Node
      (facts := [SquarePositive, IsPositive]) Nonzero where
  prove := fun state =>
    Nat.ne_of_gt (state.require (property := IsPositive))

noncomputable def seed : Residual := ⟨2, by omega⟩

noncomputable def initialState :=
  Core.ResidualRefinement.State.initial seed

noncomputable def afterCertificate :=
  positiveCertificateNode.run initialState

noncomputable def afterExactCertificate :=
  exactPositiveCertificateNode.run initialState

noncomputable def afterExactCertificateEcho :=
  exactPositiveCertificateEcho.run afterExactCertificate

noncomputable def afterPositiveAndExactCertificate :=
  exactPositiveCertificateNode.run (positiveNode.run initialState)

noncomputable def afterPositiveCertificateEcho :=
  positiveCertificateEchoNode.run afterPositiveAndExactCertificate

noncomputable def afterPositiveAndCertificate :=
  positiveCertificateNode.run (positiveNode.run initialState)

noncomputable def afterTwoCertificates :=
  nonzeroCertificateNode.run afterCertificate

noncomputable def afterCombinedCertificate :=
  combinedCertificateNode.run afterTwoCertificates

noncomputable def afterCombinedEntailedCertificate :=
  combinedEntailedCertificateNode.run afterTwoCertificates

noncomputable def afterPositiveDependentSuccessor :=
  positiveDependentSuccessorNode.run afterPositiveAndCertificate

noncomputable def afterPositiveDecision :=
  positiveDecisionNode.run afterCertificate

noncomputable def afterPositiveFirstContinuation :=
  positiveFirstContinuationNode.run afterPositiveDecision

noncomputable def afterPositiveSecondContinuation :=
  positiveSecondContinuationNode.run afterPositiveFirstContinuation

noncomputable def afterPositiveSquareCertificate :=
  positiveSquareCertificateNode.run afterPositiveAndCertificate

theorem certificate_available :
    IsPositive afterCertificate.residual :=
  (afterCertificate.requireStage
    (Stage := PositiveCertificate)).proof

theorem exact_certificate_echo_retains_output :
    (afterExactCertificateEcho.requireStage
      (Stage := ExactPositiveCertificate)).output =
        canonicalPositiveCertificate afterExactCertificateEcho.residual :=
  (afterExactCertificateEcho.requireStage
    (Stage := ExactPositiveCertificate)).outputExact

theorem fact_and_exact_stage_retains_fact :
    IsPositive afterPositiveCertificateEcho.residual :=
  (afterPositiveCertificateEcho.requireStage
    (Stage := CanonicalPositiveCertificateEcho)).positive

theorem fact_and_stage_produce_square :
    SquarePositive afterPositiveSquareCertificate.residual :=
  (afterPositiveSquareCertificate.requireStage
    (Stage := PositiveSquareCertificate)).proof

theorem two_stages_are_retrieved_without_rederivation :
    IsPositive afterCombinedCertificate.residual ∧
      Nonzero afterCombinedCertificate.residual := by
  let combined := afterCombinedCertificate.requireStage
    (Stage := CombinedCertificate)
  exact ⟨combined.positive, combined.nonzero⟩

theorem entailed_facts_are_retrieved_without_opening_stages :
    IsPositive afterCombinedEntailedCertificate.residual ∧
      Nonzero afterCombinedEntailedCertificate.residual := by
  let combined := afterCombinedEntailedCertificate.requireStage
    (Stage := CombinedCertificate)
  exact ⟨combined.positive, combined.nonzero⟩

theorem dependent_successor_retains_literal_predecessor :
    IsPositive afterPositiveDependentSuccessor.residual := by
  let successor := afterPositiveDependentSuccessor.requireStage
    (Stage := PositiveDependentSuccessor)
  exact successor.output.proof

theorem repeated_yes_continuation_retains_current_output :
    SquarePositive afterPositiveSecondContinuation.residual := by
  let result := afterPositiveSecondContinuation.requireStage
    (Stage := PositiveSecondContinuation)
  cases result with
  | yesBranch _ _ current output =>
      exact output.proof
  | noBranch certificate absent =>
      exact False.elim (absent certificate.proof)

noncomputable def afterPositive := positiveNode.run initialState
noncomputable def afterSquare := squareNode.run afterPositive
noncomputable def afterNonzero := nonzeroNode.run afterSquare

theorem all_properties_accumulated :
    IsPositive afterNonzero.residual ∧
      SquarePositive afterNonzero.residual ∧
      Nonzero afterNonzero.residual := by
  exact ⟨afterNonzero.get (.there (.there .here)),
    afterNonzero.get (.there .here), afterNonzero.latest⟩

theorem all_properties_by_type :
    IsPositive afterNonzero.residual ∧
      SquarePositive afterNonzero.residual ∧
      Nonzero afterNonzero.residual := by
  exact ⟨afterNonzero.require, afterNonzero.require,
    afterNonzero.require⟩

def IsTwo (residual : Residual) : Prop := residual.value = 2
def IsNotTwo (residual : Residual) : Prop := residual.value ≠ 2
abbrev OneBelow (residual : Residual) : Prop := 1 < residual.value
abbrev OneExact (residual : Residual) : Prop := 1 = residual.value

noncomputable def twoDecision :
    Core.ResidualRefinement.State.DecisionNode
      (facts := [SquarePositive, IsPositive]) IsTwo IsNotTwo :=
  Core.ResidualRefinement.State.DecisionNode.complement IsTwo
    (fun state =>
      show Decidable (state.residual.value = 2) from inferInstance)

noncomputable def twoDecisionResult := twoDecision.run afterSquare

noncomputable def oneLtOrEqDecision :
    Core.ResidualRefinement.State.DecisionNode
      (facts := [Core.ResidualRefinement.State.Available PositiveCertificate])
      OneBelow OneExact := by
  simpa [OneBelow, OneExact] using
    (Core.ResidualRefinement.State.DecisionNode.ltOrEqUsingStage
      (Required := PositiveCertificate)
      (facts := [Core.ResidualRefinement.State.Available PositiveCertificate])
      (fun _residual : Residual => 1)
      (fun residual => residual.value)
      (fun _state certificate => certificate.proof))

noncomputable def oneLtOrEqResult :=
  oneLtOrEqDecision.run afterCertificate

theorem one_lt_or_eq_decision_is_exhaustive :
    match oneLtOrEqResult with
    | .yesBranch branch => OneBelow branch.state.residual
    | .noBranch branch => OneExact branch.state.residual := by
  cases oneLtOrEqResult with
  | yesBranch branch => exact branch.state.latest
  | noBranch branch => exact branch.state.latest

noncomputable def refinedYesBranch :=
  twoDecisionResult.mapYes (property := Nonzero) fun branch =>
    Nat.ne_of_gt (branch.require (property := IsPositive))

noncomputable def yesCertificateNode :
    Core.ResidualRefinement.State.StageNode
      (facts := [IsTwo, SquarePositive, IsPositive]) PositiveCertificate where
  produce := fun state => ⟨state.require⟩

noncomputable def refinedYesStage :=
  twoDecisionResult.mapYesStage yesCertificateNode

noncomputable def noCertificateNode :
    Core.ResidualRefinement.State.StageNode
      (facts := [IsNotTwo, SquarePositive, IsPositive]) PositiveCertificate where
  produce := fun state => ⟨state.require⟩

noncomputable def refinedBothStages :=
  twoDecisionResult.mapStages yesCertificateNode noCertificateNode

theorem refinedBothStages_retain_edge_certificates :
    match refinedBothStages with
    | .yesBranch branch =>
        Nonempty (PositiveCertificate branch.state.residual)
    | .noBranch branch =>
        Nonempty (PositiveCertificate branch.state.residual) := by
  cases refinedBothStages with
  | yesBranch branch =>
      exact ⟨branch.requireStage (Stage := PositiveCertificate)⟩
  | noBranch branch =>
      exact ⟨branch.requireStage (Stage := PositiveCertificate)⟩

theorem refinedYesStage_retains_certificate :
    match refinedYesStage with
    | .yesBranch branch =>
        IsPositive branch.state.residual ∧
          Nonempty (PositiveCertificate branch.state.residual)
    | .noBranch branch => IsPositive branch.state.residual := by
  cases refinedYesStage with
  | yesBranch branch =>
      exact ⟨branch.require (property := IsPositive),
        ⟨branch.requireStage (Stage := PositiveCertificate)⟩⟩
  | noBranch branch => exact branch.require (property := IsPositive)

/-- Branch-local refinement retains both the literal decision fact and every
incoming fact without reconstructing a predecessor structure. -/
theorem refinedYesBranch_retains_facts :
    match refinedYesBranch with
    | .yesBranch branch =>
        Nonzero branch.state.residual ∧ IsTwo branch.state.residual ∧
          IsPositive branch.state.residual ∧
          branch.state.residual = afterSquare.residual
    | .noBranch branch =>
        IsNotTwo branch.state.residual ∧ IsPositive branch.state.residual ∧
          branch.state.residual = afterSquare.residual := by
  cases refinedYesBranch with
  | yesBranch branch =>
      exact ⟨branch.require, branch.require, branch.require,
        branch.residualExact⟩
  | noBranch branch =>
      exact ⟨branch.require, branch.require, branch.residualExact⟩

noncomputable def firstOccurrence :
    Core.FiniteResidualLedger.Ledger Residual :=
  .singleton seed

noncomputable def secondOccurrence :
    Core.FiniteResidualLedger.Ledger Residual :=
  .singleton seed

noncomputable def occurrences :
    Core.FiniteResidualLedger.Ledger Residual :=
  firstOccurrence.append secondOccurrence

noncomputable def enumeratedOccurrences :
    Core.FiniteResidualLedger.Ledger Bool :=
  Core.FiniteResidualLedger.Ledger.ofEnumeration Core.Enumeration.bool

example (occurrence : enumeratedOccurrences.Occurrence) :
    enumeratedOccurrences.event occurrence = occurrence :=
  rfl

noncomputable def positiveProducer :
    Core.ResidualRefinement.Ledger.Producer Residual IsPositive where
  emit := id
  prove := fun residual => residual.positive

/-- The producer route starts with its theorem already installed, so the next
node consumes a current state rather than reconstructing provenance. -/
noncomputable def producedLedger :=
  Core.ResidualRefinement.Ledger.produce occurrences positiveProducer

/-- Occurrence-aware provenance can be installed directly on an existing
schedule, without an application-level `initial.add`. -/
noncomputable def certifiedLedger :=
  Core.ResidualRefinement.Ledger.certify (property := IsPositive)
    occurrences fun occurrence =>
    (occurrences.event occurrence).positive

theorem every_certified_occurrence_is_positive
    (occurrence : certifiedLedger.residuals.Occurrence) :
    IsPositive (certifiedLedger.residuals.event occurrence) :=
  certifiedLedger.require occurrence

noncomputable def producedThenSquared :=
  producedLedger.refine squareNode

noncomputable def producedCertificateNode :
    Core.ResidualRefinement.State.StageNode
      (facts := [IsPositive]) PositiveCertificate where
  produce := fun state => ⟨state.require⟩

noncomputable def producedThenCertified :=
  producedLedger.refineStage producedCertificateNode

theorem every_produced_occurrence_has_certificate
    (occurrence : producedThenCertified.residuals.Occurrence) :
    IsPositive (producedThenCertified.residuals.event occurrence) :=
  (producedThenCertified.requireStage
    (Stage := PositiveCertificate) occurrence).proof

theorem produced_chain_retains_origin
    (occurrence : producedThenSquared.residuals.Occurrence) :
    IsPositive (producedThenSquared.residuals.event occurrence) ∧
      SquarePositive (producedThenSquared.residuals.event occurrence) := by
  let state := producedThenSquared.state occurrence
  exact ⟨state.require, state.require⟩

noncomputable def initialLedger :=
  Core.ResidualRefinement.Ledger.initial occurrences

noncomputable def refinedLedger :=
  ((initialLedger.refine positiveNode).refine squareNode).refine nonzeroNode

noncomputable def three : Residual := ⟨3, by omega⟩

noncomputable def mixedOccurrences :
    Core.FiniteResidualLedger.Ledger Residual :=
  (Core.FiniteResidualLedger.Ledger.singleton seed).append
    (Core.FiniteResidualLedger.Ledger.singleton three)

noncomputable def mixedLedger :=
  ((Core.ResidualRefinement.Ledger.initial mixedOccurrences).refine
    positiveNode).refine squareNode

noncomputable def mixedSplit := mixedLedger.decide twoDecision

theorem mixed_split_covers
    (occurrence : mixedLedger.residuals.Occurrence) :
    (∃ branchOccurrence,
      mixedSplit.yesOriginal branchOccurrence = occurrence) ∨
    (∃ branchOccurrence,
      mixedSplit.noOriginal branchOccurrence = occurrence) :=
  mixedSplit.coverage occurrence

theorem mixed_split_covers_uniquely
    (occurrence : mixedLedger.residuals.Occurrence) :
    (∃! branchOccurrence,
      mixedSplit.yesOriginal branchOccurrence = occurrence) ∨
    (∃! branchOccurrence,
      mixedSplit.noOriginal branchOccurrence = occurrence) :=
  mixedSplit.uniqueCoverage occurrence

theorem mixed_split_has_one_tagged_preimage
    (occurrence : mixedLedger.residuals.Occurrence) :
    ∃! branchOccurrence : mixedSplit.BranchOccurrence,
      mixedSplit.original branchOccurrence = occurrence :=
  mixedSplit.globallyUniqueCoverage occurrence

noncomputable example : mixedSplit.BranchOccurrence ≃
    mixedLedger.residuals.Occurrence :=
  mixedSplit.occurrenceEquiv

theorem mixed_split_branches_are_disjoint
    (yesOccurrence : mixedSplit.yesBranch.residuals.Occurrence)
    (noOccurrence : mixedSplit.noBranch.residuals.Occurrence) :
    mixedSplit.yesOriginal yesOccurrence ≠
      mixedSplit.noOriginal noOccurrence :=
  mixedSplit.not_both yesOccurrence noOccurrence

theorem mixed_yes_branch_has_exact_fact
    (occurrence : mixedSplit.yesBranch.residuals.Occurrence) :
    IsTwo (mixedSplit.yesBranch.residuals.event occurrence) :=
  mixedSplit.yesBranch.require (property := IsTwo) occurrence

theorem mixed_no_branch_has_exact_fact
    (occurrence : mixedSplit.noBranch.residuals.Occurrence) :
    IsNotTwo (mixedSplit.noBranch.residuals.event occurrence) :=
  mixedSplit.noBranch.require (property := IsNotTwo) occurrence

theorem mixed_split_polynomial :
    mixedLedger.decideBudget.checks () ≤
      mixedLedger.decideBudget.coefficient *
        (mixedLedger.decideBudget.size () + 1) ^
          mixedLedger.decideBudget.degree :=
  mixedLedger.decideBudget.bounded ()

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
#print axioms all_properties_by_type
#print axioms refinedYesBranch_retains_facts
#print axioms refinedYesStage_retains_certificate
#print axioms refinedBothStages_retain_edge_certificates
#print axioms occurrence_identity_preserved
#print axioms every_occurrence_has_all_properties
#print axioms mixed_split_covers
#print axioms mixed_split_covers_uniquely
#print axioms mixed_split_has_one_tagged_preimage
#print axioms mixed_split_branches_are_disjoint
#print axioms mixed_yes_branch_has_exact_fact
#print axioms mixed_no_branch_has_exact_fact
#print axioms mixed_split_polynomial
#print axioms produced_chain_retains_origin
#print axioms every_produced_occurrence_has_certificate
#print axioms every_certified_occurrence_is_positive
#print axioms exact_certificate_echo_retains_output
#print axioms fact_and_stage_produce_square
#print axioms one_lt_or_eq_decision_is_exhaustive

end StructuralExhaustion.Examples.ResidualRefinement
