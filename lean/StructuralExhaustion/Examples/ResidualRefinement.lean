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

/-- Mirror fixture: a paper node may live only on the no edge, while the
framework transports the untouched yes edge without an application handoff. -/
abbrev PositiveNoContinuation (residual : Residual) :=
  Core.ResidualRefinement.State.DependentDecisionNoContinuation
    PositiveCertificate PositiveYes PositiveNo
    (fun residual _certificate proof => NonzeroCertificate residual) residual

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

noncomputable def positiveNoContinuationNode {facts}
    [Core.ResidualRefinement.Proofs.Contains
      (Core.ResidualRefinement.State.Available
        (Core.ResidualRefinement.State.DependentDecision
          PositiveCertificate PositiveYes PositiveNo)) facts] :
    Core.ResidualRefinement.State.StageNode (facts := facts)
      PositiveNoContinuation :=
  Core.ResidualRefinement.State.StageNode.continueDependentDecisionNo
    fun _residual certificate _absent =>
      ⟨Nat.ne_of_gt certificate.proof⟩

/-! A nested decision fixture: the outer no leaf already carries a payload,
then its inner yes and no successors are populated independently. -/

abbrev NestedPositiveDecision (residual : Residual) :=
  Core.ResidualRefinement.State.DependentDecisionOnNoContinuation
    PositiveCertificate
    (fun _ _ => False) (fun _ _ => True)
    (fun _ _ _ => PUnit)
    (fun residual _ _ _ => IsPositive residual)
    (fun residual _ _ _ => ¬IsPositive residual) residual

abbrev NestedPositiveYesContinuation (residual : Residual) :=
  Core.ResidualRefinement.State.DependentDecisionOnNoYesContinuation
    PositiveCertificate
    (fun _ _ => False) (fun _ _ => True)
    (fun _ _ _ => PUnit)
    (fun residual _ _ _ => IsPositive residual)
    (fun residual _ _ _ => ¬IsPositive residual)
    (fun residual _ _ _ _ => PositiveSquareCertificate residual) residual

abbrev NestedPositiveBothContinuations (residual : Residual) :=
  Core.ResidualRefinement.State.DependentDecisionOnNoNoAfterYes
    PositiveCertificate
    (fun _ _ => False) (fun _ _ => True)
    (fun _ _ _ => PUnit)
    (fun residual _ _ _ => IsPositive residual)
    (fun residual _ _ _ => ¬IsPositive residual)
    (fun residual _ _ _ _ => PositiveSquareCertificate residual)
    (fun residual _ _ _ _ => NonzeroCertificate residual) residual

noncomputable def nestedPositiveYesContinuationNode {facts}
    [Core.ResidualRefinement.Proofs.Contains
      (Core.ResidualRefinement.State.Available NestedPositiveDecision) facts] :
    Core.ResidualRefinement.State.StageNode (facts := facts)
      NestedPositiveYesContinuation :=
  Core.ResidualRefinement.State.StageNode.continueDependentDecisionOnNoYes
    fun residual certificate _outer _output positive =>
      ⟨Nat.mul_pos positive certificate.proof⟩

noncomputable def nestedPositiveBothContinuationsNode {facts}
    [Core.ResidualRefinement.Proofs.Contains
      (Core.ResidualRefinement.State.Available
        NestedPositiveYesContinuation) facts] :
    Core.ResidualRefinement.State.StageNode (facts := facts)
      NestedPositiveBothContinuations :=
  Core.ResidualRefinement.State.StageNode.continueDependentDecisionOnNoNoAfterYes
    fun _residual certificate _outer _output _absent =>
      ⟨Nat.ne_of_gt certificate.proof⟩

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

noncomputable def afterPositiveNoContinuation :=
  positiveNoContinuationNode.run afterPositiveDecision

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

theorem no_continuation_transports_the_untouched_yes_edge :
    match afterPositiveNoContinuation.requireStage
      (Stage := PositiveNoContinuation) with
    | .yesBranch certificate proof => IsPositive seed
    | .noBranch _certificate _proof output => Nonzero seed := by
  generalize resultEq : afterPositiveNoContinuation.requireStage
    (Stage := PositiveNoContinuation) = result
  cases result with
  | yesBranch certificate proof => exact proof
  | noBranch _certificate _proof output => exact output.proof

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

/-! ## Reusable active cursor after a nested yes-leaf closure -/

abbrev NestedFixturePrevious (_residual : Residual) : Type := PUnit

abbrev NestedFixtureOuterYes (_residual : Residual)
    (_previous : PUnit) : Prop := False

abbrev NestedFixtureOuterNo (_residual : Residual)
    (_previous : PUnit) : Prop := True

abbrev NestedFixtureOuterOutput (_residual : Residual)
    (_previous : PUnit) (_proof : True) : Type := PUnit

abbrev NestedFixtureInnerYes (_residual : Residual)
    (_previous : PUnit) (_outerProof : True)
    (_outerOutput : PUnit) : Prop := False

abbrev NestedFixtureInnerNo (_residual : Residual)
    (_previous : PUnit) (_outerProof : True)
    (_outerOutput : PUnit) : Prop := True

abbrev NestedFixtureCurrent (_residual : Residual) (_previous : PUnit)
    (_outerProof : True) (_outerOutput : PUnit) (_innerProof : True) : Type := PUnit

abbrev NestedFixtureNext (_residual : Residual) (_previous : PUnit)
    (_outerProof : True) (_outerOutput : PUnit) (_innerProof : True) : Type := Bool

abbrev NestedFixtureClosed (residual : Residual) :=
  Core.ResidualRefinement.State.DependentDecisionOnNoYesClosed
    NestedFixturePrevious NestedFixtureOuterYes NestedFixtureOuterNo
    NestedFixtureOuterOutput NestedFixtureInnerYes NestedFixtureInnerNo residual

abbrev NestedFixtureActiveUnit (residual : Residual) :=
  Core.ResidualRefinement.State.DependentDecisionOnNoYesClosedActive
    NestedFixturePrevious NestedFixtureOuterYes NestedFixtureOuterNo
    NestedFixtureOuterOutput NestedFixtureInnerYes NestedFixtureInnerNo
    NestedFixtureCurrent
    residual

abbrev NestedFixtureActiveBool (residual : Residual) :=
  Core.ResidualRefinement.State.DependentDecisionOnNoYesClosedActive
    NestedFixturePrevious NestedFixtureOuterYes NestedFixtureOuterNo
    NestedFixtureOuterOutput NestedFixtureInnerYes NestedFixtureInnerNo
    NestedFixtureNext
    residual

noncomputable def nestedFixtureClosedNode {facts} :
    Core.ResidualRefinement.State.StageNode (facts := facts)
      NestedFixtureClosed where
  produce := fun _state =>
    .innerNoBranch PUnit.unit trivial PUnit.unit trivial

noncomputable def nestedFixtureStartNode {facts}
    [Core.ResidualRefinement.Proofs.Contains
      (Core.ResidualRefinement.State.Available NestedFixtureClosed) facts] :
    Core.ResidualRefinement.State.StageNode (facts := facts)
      NestedFixtureActiveUnit :=
  Core.ResidualRefinement.State.StageNode.continueDependentDecisionOnNoYesClosed
    (fun _residual _previous _outerProof _outerOutput _innerProof => PUnit.unit)

noncomputable def nestedFixtureMapNode {facts}
    [Core.ResidualRefinement.Proofs.Contains
      (Core.ResidualRefinement.State.Available NestedFixtureActiveUnit) facts] :
    Core.ResidualRefinement.State.StageNode (facts := facts)
      NestedFixtureActiveBool :=
  Core.ResidualRefinement.State.StageNode.mapDependentDecisionOnNoYesClosedActive
    (Current := NestedFixtureCurrent) (Next := NestedFixtureNext)
    (fun _residual _previous _outerProof _outerOutput _innerProof _current => true)

noncomputable def nestedFixtureAfterClosed :=
  nestedFixtureClosedNode.run (Core.ResidualRefinement.State.initial seed)

noncomputable def nestedFixtureAfterStart :=
  nestedFixtureStartNode.run nestedFixtureAfterClosed

noncomputable def nestedFixtureAfterMap :=
  nestedFixtureMapNode.run nestedFixtureAfterStart

/-- Mapping the active leaf adds only its new output and leaves the earlier
active certificate retrievable from the same accumulated ledger. -/
theorem nested_active_cursor_accumulates :
    Nonempty (NestedFixtureActiveUnit nestedFixtureAfterMap.residual) ∧
      Nonempty (NestedFixtureActiveBool nestedFixtureAfterMap.residual) := by
  exact ⟨nestedFixtureAfterMap.require
      (property := Core.ResidualRefinement.State.Available
        NestedFixtureActiveUnit),
    nestedFixtureAfterMap.require
      (property := Core.ResidualRefinement.State.Available
        NestedFixtureActiveBool)⟩

abbrev NestedFixtureDecisionYes (_residual : Residual) (_previous : PUnit)
    (_outerProof : True) (_outerOutput : PUnit) (_innerProof : True)
    (current : Bool) : Prop := current = true

abbrev NestedFixtureDecisionNo (_residual : Residual) (_previous : PUnit)
    (_outerProof : True) (_outerOutput : PUnit) (_innerProof : True)
    (current : Bool) : Prop := current = false

abbrev NestedFixtureDecision (residual : Residual) :=
  Core.ResidualRefinement.State.ActiveCursorDecision
    NestedFixturePrevious NestedFixtureOuterYes NestedFixtureOuterNo
    NestedFixtureOuterOutput NestedFixtureInnerYes NestedFixtureInnerNo
    NestedFixtureNext NestedFixtureDecisionYes NestedFixtureDecisionNo residual

noncomputable def nestedFixtureDecideNode {facts}
    [Core.ResidualRefinement.Proofs.Contains
      (Core.ResidualRefinement.State.Available NestedFixtureActiveBool) facts] :
    Core.ResidualRefinement.State.StageNode (facts := facts)
      NestedFixtureDecision :=
  Core.ResidualRefinement.State.StageNode.decideDependentDecisionOnNoYesClosedActive
    (yes := NestedFixtureDecisionYes) (no := NestedFixtureDecisionNo)
    (fun _ _ _ _ _ current => inferInstanceAs (Decidable (current = true)))
    (fun _ _ _ _ _ current absent => by
      cases current <;> simp_all)

noncomputable def nestedFixtureMapFalseNode {facts}
    [Core.ResidualRefinement.Proofs.Contains
      (Core.ResidualRefinement.State.Available NestedFixtureActiveUnit) facts] :
    Core.ResidualRefinement.State.StageNode (facts := facts)
      NestedFixtureActiveBool :=
  Core.ResidualRefinement.State.StageNode.mapDependentDecisionOnNoYesClosedActive
    (Current := NestedFixtureCurrent) (Next := NestedFixtureNext)
    (fun _ _ _ _ _ _ => false)

noncomputable def nestedFixtureYesDecision :=
  nestedFixtureDecideNode.run nestedFixtureAfterMap

noncomputable def nestedFixtureFalseActive :=
  nestedFixtureMapFalseNode.run nestedFixtureAfterStart

noncomputable def nestedFixtureNoDecision :=
  nestedFixtureDecideNode.run nestedFixtureFalseActive

/-- Both local outcomes preserve the active predecessor and append the
decision to the same accumulated ledger. -/
theorem nested_active_decision_preserves_ledger :
    (Nonempty (NestedFixtureActiveBool nestedFixtureYesDecision.residual) ∧
      Nonempty (NestedFixtureDecision nestedFixtureYesDecision.residual)) ∧
    (Nonempty (NestedFixtureActiveBool nestedFixtureNoDecision.residual) ∧
      Nonempty (NestedFixtureDecision nestedFixtureNoDecision.residual)) := by
  exact ⟨⟨nestedFixtureYesDecision.require
      (property := Core.ResidualRefinement.State.Available
        NestedFixtureActiveBool),
      nestedFixtureYesDecision.latest⟩,
    ⟨nestedFixtureNoDecision.require
      (property := Core.ResidualRefinement.State.Available
        NestedFixtureActiveBool),
      nestedFixtureNoDecision.latest⟩⟩

/-! ## Independent continuations of one active-cursor decision -/

abbrev NestedFixtureYesPayload (_residual : Residual) (_previous : PUnit)
    (_outerProof : True) (_outerOutput : PUnit) (_innerProof : True)
    (_current : Bool) (_proof : _current = true) : Type := PUnit

abbrev NestedFixtureNoPayload (_residual : Residual) (_previous : PUnit)
    (_outerProof : True) (_outerOutput : PUnit) (_innerProof : True)
    (_current : Bool) (_proof : _current = false) : Type := PUnit

abbrev NestedFixtureYesNext (_residual : Residual) (_previous : PUnit)
    (_outerProof : True) (_outerOutput : PUnit) (_innerProof : True)
    (_current : Bool) (_proof : _current = true) : Type := Bool

abbrev NestedFixtureNoNext (_residual : Residual) (_previous : PUnit)
    (_outerProof : True) (_outerOutput : PUnit) (_innerProof : True)
    (_current : Bool) (_proof : _current = false) : Type := Bool

abbrev NestedFixtureYesContinuation (residual : Residual) :=
  Core.ResidualRefinement.State.ActiveCursorDecisionYesContinuation
    NestedFixturePrevious NestedFixtureOuterYes NestedFixtureOuterNo
    NestedFixtureOuterOutput NestedFixtureInnerYes NestedFixtureInnerNo
    NestedFixtureNext NestedFixtureDecisionYes NestedFixtureDecisionNo
    NestedFixtureYesPayload residual

abbrev NestedFixtureNoContinuation (residual : Residual) :=
  Core.ResidualRefinement.State.ActiveCursorDecisionNoContinuation
    NestedFixturePrevious NestedFixtureOuterYes NestedFixtureOuterNo
    NestedFixtureOuterOutput NestedFixtureInnerYes NestedFixtureInnerNo
    NestedFixtureNext NestedFixtureDecisionYes NestedFixtureDecisionNo
    NestedFixtureNoPayload residual

abbrev NestedFixtureYesMapped (residual : Residual) :=
  Core.ResidualRefinement.State.ActiveCursorDecisionYesContinuation
    NestedFixturePrevious NestedFixtureOuterYes NestedFixtureOuterNo
    NestedFixtureOuterOutput NestedFixtureInnerYes NestedFixtureInnerNo
    NestedFixtureNext NestedFixtureDecisionYes NestedFixtureDecisionNo
    NestedFixtureYesNext residual

abbrev NestedFixtureNoMapped (residual : Residual) :=
  Core.ResidualRefinement.State.ActiveCursorDecisionNoContinuation
    NestedFixturePrevious NestedFixtureOuterYes NestedFixtureOuterNo
    NestedFixtureOuterOutput NestedFixtureInnerYes NestedFixtureInnerNo
    NestedFixtureNext NestedFixtureDecisionYes NestedFixtureDecisionNo
    NestedFixtureNoNext residual

abbrev NestedFixtureNoFocusedBypass :=
  Core.ResidualRefinement.State.ActiveCursorDecisionNoContinuationBypass
    NestedFixturePrevious NestedFixtureOuterYes NestedFixtureOuterNo
    NestedFixtureOuterOutput NestedFixtureInnerYes NestedFixtureInnerNo
    NestedFixtureNext NestedFixtureDecisionYes NestedFixtureDecisionNo

abbrev NestedFixtureNoFocusedActive :=
  Core.ResidualRefinement.State.ActiveCursorDecisionNoContinuationActive
    NestedFixturePrevious NestedFixtureOuterNo NestedFixtureOuterOutput
    NestedFixtureInnerNo NestedFixtureNext NestedFixtureDecisionNo
    NestedFixtureNoNext

abbrev NestedFixtureNoFocusedYes (_residual : Residual)
    (active : NestedFixtureNoFocusedActive _residual) : Prop :=
  active.output = true

abbrev NestedFixtureNoFocusedNo (_residual : Residual)
    (active : NestedFixtureNoFocusedActive _residual) : Prop :=
  active.output = false

abbrev NestedFixtureNoFocusedDecision :=
  Core.ResidualRefinement.State.FocusedBranchDecision
    NestedFixtureNoFocusedBypass NestedFixtureNoFocusedActive
    NestedFixtureNoFocusedYes NestedFixtureNoFocusedNo

noncomputable def nestedFixtureYesContinuationNode {facts}
    [Core.ResidualRefinement.Proofs.Contains
      (Core.ResidualRefinement.State.Available NestedFixtureDecision) facts] :
    Core.ResidualRefinement.State.StageNode (facts := facts)
      NestedFixtureYesContinuation :=
  Core.ResidualRefinement.State.StageNode.continueActiveCursorDecisionYes
    (YesOutput := NestedFixtureYesPayload)
    (fun _ _ _ _ _ _ _ => PUnit.unit)

noncomputable def nestedFixtureNoContinuationNode {facts}
    [Core.ResidualRefinement.Proofs.Contains
      (Core.ResidualRefinement.State.Available NestedFixtureDecision) facts] :
    Core.ResidualRefinement.State.StageNode (facts := facts)
      NestedFixtureNoContinuation :=
  Core.ResidualRefinement.State.StageNode.continueActiveCursorDecisionNo
    (NoOutput := NestedFixtureNoPayload)
    (fun _ _ _ _ _ _ _ => PUnit.unit)

noncomputable def nestedFixtureMapYesContinuationNode {facts}
    [Core.ResidualRefinement.Proofs.Contains
      (Core.ResidualRefinement.State.Available NestedFixtureYesContinuation)
        facts] :
    Core.ResidualRefinement.State.StageNode (facts := facts)
      NestedFixtureYesMapped :=
  Core.ResidualRefinement.State.StageNode.mapActiveCursorDecisionYesContinuation
    (YesOutput := NestedFixtureYesPayload) (NextOutput := NestedFixtureYesNext)
    (fun _ _ _ _ _ _ _ _ => true)

noncomputable def nestedFixtureMapNoContinuationNode {facts}
    [Core.ResidualRefinement.Proofs.Contains
      (Core.ResidualRefinement.State.Available NestedFixtureNoContinuation)
        facts] :
    Core.ResidualRefinement.State.StageNode (facts := facts)
      NestedFixtureNoMapped :=
  Core.ResidualRefinement.State.StageNode.mapActiveCursorDecisionNoContinuation
    (Output := NestedFixtureNoPayload) (Next := NestedFixtureNoNext)
    (fun _ _ _ _ _ _ _ _ => true)

/-- The same no-leaf mapping while querying an earlier exact decision from
the one accumulated ledger. -/
noncomputable def nestedFixtureMapNoContinuationDerivedNode {facts}
    [Core.ResidualRefinement.Proofs.Contains
      (Core.ResidualRefinement.State.Available NestedFixtureNoContinuation)
        facts]
    [Core.ResidualRefinement.Proofs.Contains
      (Core.ResidualRefinement.State.Available NestedFixtureDecision) facts] :
    Core.ResidualRefinement.State.StageNode (facts := facts)
      NestedFixtureNoMapped :=
  Core.ResidualRefinement.State.StageNode.mapActiveCursorDecisionNoContinuationDerived
    (Output := NestedFixtureNoPayload)
    (Next := NestedFixtureNoNext)
    (Core.ResidualRefinement.State.LedgerQuery.stage
      (facts := facts) (Stage := NestedFixtureDecision))
    (fun _ _inherited _ _ _ _ _ _ _ => true)

noncomputable def nestedFixtureDecideNoContinuationNode {facts}
    [Core.ResidualRefinement.Proofs.Contains
      (Core.ResidualRefinement.State.Available NestedFixtureNoMapped) facts] :
    Core.ResidualRefinement.State.StageNode (facts := facts)
      NestedFixtureNoFocusedDecision :=
  Core.ResidualRefinement.State.StageNode.decideActiveCursorDecisionNoContinuation
    (nextYes := NestedFixtureNoFocusedYes)
    (nextNo := NestedFixtureNoFocusedNo)
    (fun _ active => inferInstanceAs (Decidable (active.output = true)))
    (fun _ _active absent => Bool.eq_false_of_not_eq_true absent)

noncomputable def nestedFixtureAfterYesContinuation :=
  nestedFixtureYesContinuationNode.run nestedFixtureYesDecision

/-- The no continuation is deliberately run after the yes continuation from
the same accumulated state.  It retrieves the original decision and leaves
the already appended yes stage untouched. -/
noncomputable def nestedFixtureAfterBothContinuations :=
  nestedFixtureNoContinuationNode.run nestedFixtureAfterYesContinuation

noncomputable def nestedFixtureAfterMappedYes :=
  nestedFixtureMapYesContinuationNode.run nestedFixtureAfterBothContinuations

noncomputable def nestedFixtureAfterNoContinuationActive :=
  nestedFixtureNoContinuationNode.run nestedFixtureNoDecision

noncomputable def nestedFixtureAfterMappedNo :=
  nestedFixtureMapNoContinuationNode.run nestedFixtureAfterNoContinuationActive

noncomputable def nestedFixtureAfterMappedNoDerived :=
  nestedFixtureMapNoContinuationDerivedNode.run
    nestedFixtureAfterNoContinuationActive

noncomputable def nestedFixtureAfterNoContinuationDecision :=
  nestedFixtureDecideNoContinuationNode.run nestedFixtureAfterMappedNo

/-- The decision, both independent branch continuations, and the next mapped
yes payload are all retrievable from one accumulated ledger. -/
theorem active_cursor_branch_continuations_accumulate :
    Nonempty (NestedFixtureDecision nestedFixtureAfterMappedYes.residual) ∧
      Nonempty
        (NestedFixtureYesContinuation nestedFixtureAfterMappedYes.residual) ∧
      Nonempty
        (NestedFixtureNoContinuation nestedFixtureAfterMappedYes.residual) ∧
      Nonempty (NestedFixtureYesMapped nestedFixtureAfterMappedYes.residual) := by
  exact ⟨nestedFixtureAfterMappedYes.require
      (property := Core.ResidualRefinement.State.Available
        NestedFixtureDecision),
    nestedFixtureAfterMappedYes.require
      (property := Core.ResidualRefinement.State.Available
        NestedFixtureYesContinuation),
    nestedFixtureAfterMappedYes.require
      (property := Core.ResidualRefinement.State.Available
        NestedFixtureNoContinuation),
      nestedFixtureAfterMappedYes.latest⟩

theorem active_cursor_derived_query_accumulates :
    Nonempty (NestedFixtureDecision
        nestedFixtureAfterMappedNoDerived.residual) ∧
      Nonempty (NestedFixtureNoContinuation
        nestedFixtureAfterMappedNoDerived.residual) ∧
      Nonempty (NestedFixtureNoMapped
        nestedFixtureAfterMappedNoDerived.residual) := by
  exact ⟨nestedFixtureAfterMappedNoDerived.require
      (property := Core.ResidualRefinement.State.Available NestedFixtureDecision),
    nestedFixtureAfterMappedNoDerived.require
      (property := Core.ResidualRefinement.State.Available
        NestedFixtureNoContinuation),
    nestedFixtureAfterMappedNoDerived.latest⟩

theorem active_cursor_no_continuation_focus_accumulates :
    Nonempty
        (NestedFixtureNoContinuation
          nestedFixtureAfterNoContinuationDecision.residual) ∧
      Nonempty
        (NestedFixtureNoMapped
          nestedFixtureAfterNoContinuationDecision.residual) ∧
      Nonempty
        (NestedFixtureNoFocusedDecision
          nestedFixtureAfterNoContinuationDecision.residual) := by
  exact ⟨nestedFixtureAfterNoContinuationDecision.require
      (property := Core.ResidualRefinement.State.Available
        NestedFixtureNoContinuation),
    nestedFixtureAfterNoContinuationDecision.require
      (property := Core.ResidualRefinement.State.Available
        NestedFixtureNoMapped),
    nestedFixtureAfterNoContinuationDecision.latest⟩

/-! ## Focused decisions below an active yes continuation -/

abbrev NestedFixtureFamily :=
  Core.ResidualRefinement.State.ActiveCursorYesContinuationFamily.mk
    NestedFixturePrevious NestedFixtureOuterYes NestedFixtureOuterNo
    NestedFixtureOuterOutput NestedFixtureInnerYes NestedFixtureInnerNo
    NestedFixtureNext NestedFixtureDecisionYes NestedFixtureDecisionNo
    NestedFixtureYesPayload

abbrev NestedFixtureAuditYes (_residual : Residual)
    (_data : NestedFixtureFamily.ActiveData _residual) : Prop := True

abbrev NestedFixtureAuditNo (_residual : Residual)
    (_data : NestedFixtureFamily.ActiveData _residual) : Prop := False

abbrev NestedFixtureFinalYes (_residual : Residual)
    (_data : NestedFixtureFamily.ActiveData _residual)
    (_audit : NestedFixtureAuditYes _residual _data) : Prop := False

abbrev NestedFixtureFinalNo (_residual : Residual)
    (_data : NestedFixtureFamily.ActiveData _residual)
    (_audit : NestedFixtureAuditYes _residual _data) : Prop := True

abbrev NestedFixtureAuditDecision :=
  NestedFixtureFamily.Decision NestedFixtureAuditYes NestedFixtureAuditNo

abbrev NestedFixtureAuditNoTerminal :=
  NestedFixtureFamily.NoTerminal NestedFixtureAuditYes NestedFixtureAuditNo

abbrev NestedFixtureFinalDecision :=
  NestedFixtureFamily.YesDecision NestedFixtureAuditYes NestedFixtureAuditNo
    NestedFixtureFinalYes NestedFixtureFinalNo

abbrev NestedFixtureFinalYesClosed :=
  NestedFixtureFamily.FinalYesClosed NestedFixtureAuditYes NestedFixtureAuditNo
    NestedFixtureFinalYes NestedFixtureFinalNo

abbrev NestedFixtureFinalNoActive :=
  NestedFixtureFamily.FinalNoActive NestedFixtureAuditYes NestedFixtureAuditNo
    NestedFixtureFinalYes NestedFixtureFinalNo

noncomputable def nestedFixtureAuditDecisionNode {facts}
    [Core.ResidualRefinement.Proofs.Contains
      (Core.ResidualRefinement.State.Available NestedFixtureYesContinuation)
        facts] :
    Core.ResidualRefinement.State.StageNode (facts := facts)
      NestedFixtureAuditDecision :=
  Core.ResidualRefinement.State.StageNode.decideActiveCursorYesContinuation
    NestedFixtureFamily
    (fun _ _ => isTrue trivial)
    (fun _ _ absent => (absent trivial).elim)

noncomputable def nestedFixtureAuditNoTerminalNode {facts}
    [Core.ResidualRefinement.Proofs.Contains
      (Core.ResidualRefinement.State.Available NestedFixtureAuditDecision)
        facts] :
    Core.ResidualRefinement.State.StageNode (facts := facts)
      NestedFixtureAuditNoTerminal :=
  Core.ResidualRefinement.State.StageNode.markActiveCursorYesContinuationNoTerminal
    NestedFixtureFamily

noncomputable def nestedFixtureFinalDecisionNode {facts}
    [Core.ResidualRefinement.Proofs.Contains
      (Core.ResidualRefinement.State.Available NestedFixtureAuditDecision)
        facts] :
    Core.ResidualRefinement.State.StageNode (facts := facts)
      NestedFixtureFinalDecision :=
  Core.ResidualRefinement.State.StageNode.decideActiveCursorYesContinuationYes
    NestedFixtureFamily
    (fun _ _ _ => isFalse id)
    (fun _ _ _ _ => trivial)

noncomputable def nestedFixtureFinalYesClosedNode {facts}
    [Core.ResidualRefinement.Proofs.Contains
      (Core.ResidualRefinement.State.Available NestedFixtureFinalDecision)
        facts] :
    Core.ResidualRefinement.State.StageNode (facts := facts)
      NestedFixtureFinalYesClosed :=
  Core.ResidualRefinement.State.StageNode.closeActiveCursorYesContinuationFinalYes
    NestedFixtureFamily (fun _ _ _ impossible => impossible)

noncomputable def nestedFixtureFinalNoActiveNode {facts}
    [Core.ResidualRefinement.Proofs.Contains
      (Core.ResidualRefinement.State.Available NestedFixtureFinalDecision)
        facts] :
    Core.ResidualRefinement.State.StageNode (facts := facts)
      NestedFixtureFinalNoActive :=
  Core.ResidualRefinement.State.StageNode.focusActiveCursorYesContinuationFinalNo
    NestedFixtureFamily

abbrev NestedFixtureFocusedBypass (residual : Residual) : Type :=
  NestedFixtureFamily.FinalNoBypass NestedFixtureAuditYes NestedFixtureAuditNo
    NestedFixtureFinalYes NestedFixtureFinalNo residual

abbrev NestedFixtureFocusedActive (residual : Residual) : Type :=
  NestedFixtureFamily.FinalNoData NestedFixtureAuditYes NestedFixtureFinalNo residual

abbrev NestedFixtureFocusedYes (_residual : Residual)
    (_data : NestedFixtureFocusedActive _residual) : Prop := False

abbrev NestedFixtureFocusedNo (_residual : Residual)
    (_data : NestedFixtureFocusedActive _residual) : Prop := True

abbrev NestedFixtureFocusedDecision (residual : Residual) : Type :=
  Core.ResidualRefinement.State.FocusedBranchDecision
    NestedFixtureFocusedBypass NestedFixtureFocusedActive
    NestedFixtureFocusedYes NestedFixtureFocusedNo residual

abbrev NestedFixtureFocusedYesClosed (residual : Residual) : Type :=
  Core.ResidualRefinement.State.FocusedBranchDecisionYesClosed
    NestedFixtureFocusedBypass NestedFixtureFocusedActive
    NestedFixtureFocusedYes NestedFixtureFocusedNo residual

abbrev NestedFixtureFocusedNoContinuation (residual : Residual) : Type :=
  Core.ResidualRefinement.State.FocusedBranchDecisionNoContinuation
    NestedFixtureFocusedBypass NestedFixtureFocusedActive
    NestedFixtureFocusedYes NestedFixtureFocusedNo
    (fun _ _ _ => PUnit) residual

abbrev NestedFixtureFocusedYesContinuation (residual : Residual) : Type :=
  Core.ResidualRefinement.State.FocusedBranchDecisionYesContinuation
    NestedFixtureFocusedBypass NestedFixtureFocusedActive
    NestedFixtureFocusedYes NestedFixtureFocusedNo
    (fun _ _ _ => PUnit) residual

abbrev NestedFixtureFocusedYesMapped (residual : Residual) : Type :=
  Core.ResidualRefinement.State.FocusedBranchDecisionYesContinuation
    NestedFixtureFocusedBypass NestedFixtureFocusedActive
    NestedFixtureFocusedYes NestedFixtureFocusedNo
    (fun _ _ _ => True) residual

abbrev NestedFixtureFocusedInnerYes (_residual : Residual)
    (data : NestedFixtureFocusedActive _residual)
    (_outer : NestedFixtureFocusedNo _residual data) : Prop := False

abbrev NestedFixtureFocusedInnerNo (_residual : Residual)
    (data : NestedFixtureFocusedActive _residual)
    (_outer : NestedFixtureFocusedNo _residual data) : Prop := True

abbrev NestedFixtureFocusedNestedDecision (residual : Residual) : Type :=
  Core.ResidualRefinement.State.FocusedBranchYesContinuationNoDecision
    NestedFixtureFocusedBypass NestedFixtureFocusedActive
    NestedFixtureFocusedYes NestedFixtureFocusedNo
    (fun _ _ _ => PUnit)
    NestedFixtureFocusedInnerYes NestedFixtureFocusedInnerNo residual

abbrev NestedFixtureFocusedNestedTerminalBypass
    (residual : Residual) : Type :=
  Core.ResidualRefinement.State.FocusedBranchYesTerminalBypass
    NestedFixtureFocusedBypass NestedFixtureFocusedActive
    NestedFixtureFocusedYes (fun _ _ _ => PUnit)
    (fun _ _ _ _ => PUnit) residual

abbrev NestedFixtureFocusedNestedNoActive (residual : Residual) : Type :=
  Core.ResidualRefinement.State.FocusedBranchNestedNoActive
    NestedFixtureFocusedActive NestedFixtureFocusedNo
    NestedFixtureFocusedInnerNo residual

abbrev NestedFixtureFocusedNestedClosed (residual : Residual) : Type :=
  Core.ResidualRefinement.State.FocusedBranch
    NestedFixtureFocusedNestedTerminalBypass
    NestedFixtureFocusedNestedNoActive residual

abbrev NestedFixtureFocusedActiveContinuation (residual : Residual) : Type :=
  Core.ResidualRefinement.State.FocusedBranchActiveContinuation
    NestedFixtureFocusedNestedTerminalBypass
    NestedFixtureFocusedNestedNoActive
    (fun _ _ => Bool) residual

abbrev NestedFixtureFocusedNoMapped :=
  Core.ResidualRefinement.State.FocusedBranchDecisionNoContinuation
    NestedFixtureFocusedBypass NestedFixtureFocusedActive
    NestedFixtureFocusedYes NestedFixtureFocusedNo
    (fun _ _ _ => Bool)

abbrev NestedFixtureFocusedTerminalYes (_residual : Residual)
    (_data : NestedFixtureFocusedActive _residual) : Prop := True

abbrev NestedFixtureFocusedTerminalNo (_residual : Residual)
    (_data : NestedFixtureFocusedActive _residual) : Prop := False

abbrev NestedFixtureFocusedTerminalDecision :=
  Core.ResidualRefinement.State.FocusedBranchDecision
    NestedFixtureFocusedBypass NestedFixtureFocusedActive
    NestedFixtureFocusedTerminalYes NestedFixtureFocusedTerminalNo

abbrev NestedFixtureFocusedTerminalNoContinuation :=
  Core.ResidualRefinement.State.FocusedBranchDecisionNoContinuation
    NestedFixtureFocusedBypass NestedFixtureFocusedActive
    NestedFixtureFocusedTerminalYes NestedFixtureFocusedTerminalNo
    (fun _ _ _ => Unit)

abbrev NestedFixtureFocusedTerminalNoClosed :=
  Core.ResidualRefinement.State.FocusedBranchDecisionNoClosed
    NestedFixtureFocusedBypass NestedFixtureFocusedActive
    NestedFixtureFocusedTerminalYes NestedFixtureFocusedTerminalNo

noncomputable def nestedFixtureFocusedDecisionNode {facts}
    [Core.ResidualRefinement.Proofs.Contains
      (Core.ResidualRefinement.State.Available NestedFixtureFinalNoActive) facts] :
    Core.ResidualRefinement.State.StageNode (facts := facts)
      NestedFixtureFocusedDecision :=
  Core.ResidualRefinement.State.StageNode.decideFocusedBranch
    (fun _ _ => isFalse id) (fun _ _ _ => trivial)

noncomputable def nestedFixtureFocusedYesClosedNode {facts}
    [Core.ResidualRefinement.Proofs.Contains
      (Core.ResidualRefinement.State.Available NestedFixtureFocusedDecision)
        facts] :
    Core.ResidualRefinement.State.StageNode (facts := facts)
      NestedFixtureFocusedYesClosed :=
  Core.ResidualRefinement.State.StageNode.closeFocusedBranchYes
    (fun _ _ impossible => impossible)

noncomputable def nestedFixtureFocusedNoContinuationNode {facts}
    [Core.ResidualRefinement.Proofs.Contains
      (Core.ResidualRefinement.State.Available NestedFixtureFocusedDecision)
        facts] :
    Core.ResidualRefinement.State.StageNode (facts := facts)
      NestedFixtureFocusedNoContinuation :=
  Core.ResidualRefinement.State.StageNode.continueFocusedBranchNo
    (fun _ _ _ => PUnit.unit)

noncomputable def nestedFixtureFocusedYesContinuationNode {facts}
    [Core.ResidualRefinement.Proofs.Contains
      (Core.ResidualRefinement.State.Available NestedFixtureFocusedDecision)
        facts] :
    Core.ResidualRefinement.State.StageNode (facts := facts)
      NestedFixtureFocusedYesContinuation :=
  Core.ResidualRefinement.State.StageNode.continueFocusedBranchYes
    (fun _ _ _ => PUnit.unit)

noncomputable def nestedFixtureFocusedYesMappedNode {facts}
    [Core.ResidualRefinement.Proofs.Contains
      (Core.ResidualRefinement.State.Available
        NestedFixtureFocusedYesContinuation) facts] :
    Core.ResidualRefinement.State.StageNode (facts := facts)
      NestedFixtureFocusedYesMapped :=
  Core.ResidualRefinement.State.StageNode.mapFocusedBranchYesContinuation
    (Output := fun _ _ _ => PUnit)
    (Next := fun _ _ _ => True)
    (fun _ _ _ _ => trivial)

noncomputable def nestedFixtureFocusedNestedDecisionNode {facts}
    [Core.ResidualRefinement.Proofs.Contains
      (Core.ResidualRefinement.State.Available
        NestedFixtureFocusedYesContinuation) facts] :
    Core.ResidualRefinement.State.StageNode (facts := facts)
      NestedFixtureFocusedNestedDecision :=
  Core.ResidualRefinement.State.StageNode.decideFocusedBranchYesContinuationNo
      (fun _ _ _ => isFalse id)
      (fun _ _ _ _ => trivial)

noncomputable def nestedFixtureFocusedNestedClosedNode {facts}
    [Core.ResidualRefinement.Proofs.Contains
      (Core.ResidualRefinement.State.Available
        NestedFixtureFocusedNestedDecision) facts] :
    Core.ResidualRefinement.State.StageNode (facts := facts)
      NestedFixtureFocusedNestedClosed :=
  Core.ResidualRefinement.State.StageNode.terminalizeFocusedBranchYesCloseNestedYes
      (fun _ _ _ _ => PUnit.unit)
      (fun _ _ _ impossible => impossible)

noncomputable def nestedFixtureFocusedActiveContinuationNode {facts}
    [Core.ResidualRefinement.Proofs.Contains
      (Core.ResidualRefinement.State.Available
        NestedFixtureFocusedNestedClosed) facts] :
    Core.ResidualRefinement.State.StageNode (facts := facts)
      NestedFixtureFocusedActiveContinuation :=
  Core.ResidualRefinement.State.StageNode.continueFocusedBranchActive
    (fun _ _ => true)

/-- The same focused mapping while retrieving an independent earlier stage
from the one accumulated ledger. -/
noncomputable def nestedFixtureFocusedYesMappedDerivedNode {facts}
    [Core.ResidualRefinement.Proofs.Contains
      (Core.ResidualRefinement.State.Available
        NestedFixtureFocusedYesContinuation) facts]
    [Core.ResidualRefinement.Proofs.Contains
      (Core.ResidualRefinement.State.Available NestedFixtureFinalNoActive) facts] :
    Core.ResidualRefinement.State.StageNode (facts := facts)
      NestedFixtureFocusedYesMapped :=
  Core.ResidualRefinement.State.StageNode.mapFocusedBranchYesContinuationDerived
    (Output := fun _ _ _ => PUnit)
    (Next := fun _ _ _ => True)
    (Core.ResidualRefinement.State.LedgerQuery.stage
      (facts := facts) (Stage := NestedFixtureFinalNoActive))
    (fun _ _inherited _ _ _ => trivial)

noncomputable def nestedFixtureFocusedNoMappedNode {facts}
    [Core.ResidualRefinement.Proofs.Contains
      (Core.ResidualRefinement.State.Available
        NestedFixtureFocusedNoContinuation) facts] :
    Core.ResidualRefinement.State.StageNode (facts := facts)
      NestedFixtureFocusedNoMapped :=
  Core.ResidualRefinement.State.StageNode.mapFocusedBranchNoContinuation
    (Output := fun _ _ _ => PUnit)
    (Next := fun _ _ _ => Bool)
    (fun _ _ _ _ => true)

noncomputable def nestedFixtureFocusedTerminalDecisionNode {facts}
    [Core.ResidualRefinement.Proofs.Contains
      (Core.ResidualRefinement.State.Available NestedFixtureFinalNoActive) facts] :
    Core.ResidualRefinement.State.StageNode (facts := facts)
      NestedFixtureFocusedTerminalDecision :=
  Core.ResidualRefinement.State.StageNode.decideFocusedBranch
    (fun _ _ => isTrue trivial) (fun _ _ absent => (absent trivial).elim)

noncomputable def nestedFixtureFocusedTerminalNoContinuationNode {facts}
    [Core.ResidualRefinement.Proofs.Contains
      (Core.ResidualRefinement.State.Available
        NestedFixtureFocusedTerminalDecision) facts] :
    Core.ResidualRefinement.State.StageNode (facts := facts)
      NestedFixtureFocusedTerminalNoContinuation :=
  Core.ResidualRefinement.State.StageNode.continueFocusedBranchNo
    (fun _ _ impossible => impossible.elim)

noncomputable def nestedFixtureFocusedTerminalNoClosedNode {facts}
    [Core.ResidualRefinement.Proofs.Contains
      (Core.ResidualRefinement.State.Available
        NestedFixtureFocusedTerminalNoContinuation) facts] :
    Core.ResidualRefinement.State.StageNode (facts := facts)
      NestedFixtureFocusedTerminalNoClosed :=
  Core.ResidualRefinement.State.StageNode.closeFocusedBranchNoContinuation
    (Output := fun _ _ _ => Unit)
    (fun _ _ impossible _ => impossible.elim)

noncomputable def nestedFixtureAfterAuditDecision :=
  nestedFixtureAuditDecisionNode.run nestedFixtureAfterYesContinuation

noncomputable def nestedFixtureAfterAuditTerminal :=
  nestedFixtureAuditNoTerminalNode.run nestedFixtureAfterAuditDecision

noncomputable def nestedFixtureAfterFinalDecision :=
  nestedFixtureFinalDecisionNode.run nestedFixtureAfterAuditTerminal

noncomputable def nestedFixtureAfterFinalYesClosed :=
  nestedFixtureFinalYesClosedNode.run nestedFixtureAfterFinalDecision

noncomputable def nestedFixtureAfterFinalNoActive :=
  nestedFixtureFinalNoActiveNode.run nestedFixtureAfterFinalYesClosed

noncomputable def nestedFixtureAfterFocusedDecision :=
  nestedFixtureFocusedDecisionNode.run nestedFixtureAfterFinalNoActive

noncomputable def nestedFixtureAfterFocusedYesClosed :=
  nestedFixtureFocusedYesClosedNode.run nestedFixtureAfterFocusedDecision

noncomputable def nestedFixtureAfterFocusedNoContinuation :=
  nestedFixtureFocusedNoContinuationNode.run nestedFixtureAfterFocusedYesClosed

noncomputable def nestedFixtureAfterFocusedYesContinuation :=
  nestedFixtureFocusedYesContinuationNode.run nestedFixtureAfterFocusedDecision

noncomputable def nestedFixtureAfterFocusedYesMapped :=
  nestedFixtureFocusedYesMappedNode.run nestedFixtureAfterFocusedYesContinuation

noncomputable def nestedFixtureAfterFocusedNestedDecision :=
  nestedFixtureFocusedNestedDecisionNode.run
    nestedFixtureAfterFocusedYesContinuation

noncomputable def nestedFixtureAfterFocusedNestedClosed :=
  nestedFixtureFocusedNestedClosedNode.run
    nestedFixtureAfterFocusedNestedDecision

noncomputable def nestedFixtureAfterFocusedActiveContinuation :=
  nestedFixtureFocusedActiveContinuationNode.run
    nestedFixtureAfterFocusedNestedClosed

noncomputable def nestedFixtureAfterFocusedYesMappedDerived :=
  nestedFixtureFocusedYesMappedDerivedNode.run
    nestedFixtureAfterFocusedYesContinuation

noncomputable def nestedFixtureAfterFocusedNoMapped :=
  nestedFixtureFocusedNoMappedNode.run nestedFixtureAfterFocusedNoContinuation

noncomputable def nestedFixtureAfterFocusedTerminalDecision :=
  nestedFixtureFocusedTerminalDecisionNode.run nestedFixtureAfterFinalNoActive

noncomputable def nestedFixtureAfterFocusedTerminalNoContinuation :=
  nestedFixtureFocusedTerminalNoContinuationNode.run
    nestedFixtureAfterFocusedTerminalDecision

noncomputable def nestedFixtureAfterFocusedTerminalNoClosed :=
  nestedFixtureFocusedTerminalNoClosedNode.run
    nestedFixtureAfterFocusedTerminalNoContinuation

theorem focused_active_cursor_accumulates :
    Nonempty
        (NestedFixtureFinalYesClosed
          nestedFixtureAfterFocusedNoMapped.residual) ∧
      Nonempty
        (NestedFixtureFocusedNoContinuation
          nestedFixtureAfterFocusedNoMapped.residual) ∧
      Nonempty
        (NestedFixtureFocusedNoMapped
          nestedFixtureAfterFocusedNoMapped.residual) := by
  exact ⟨nestedFixtureAfterFocusedNoMapped.require
      (property := Core.ResidualRefinement.State.Available
        NestedFixtureFinalYesClosed),
    nestedFixtureAfterFocusedNoMapped.require
      (property := Core.ResidualRefinement.State.Available
        NestedFixtureFocusedNoContinuation),
    nestedFixtureAfterFocusedNoMapped.latest⟩

theorem focused_no_closure_accumulates :
    Nonempty
        (NestedFixtureFocusedTerminalDecision
          nestedFixtureAfterFocusedTerminalNoClosed.residual) ∧
      Nonempty
        (NestedFixtureFocusedTerminalNoContinuation
          nestedFixtureAfterFocusedTerminalNoClosed.residual) ∧
      Nonempty
        (NestedFixtureFocusedTerminalNoClosed
          nestedFixtureAfterFocusedTerminalNoClosed.residual) := by
  let continuation :
      NestedFixtureFocusedTerminalNoContinuation
        nestedFixtureAfterFocusedTerminalNoClosed.residual :=
    nestedFixtureAfterFocusedTerminalNoClosed.requireStage
      (Stage := NestedFixtureFocusedTerminalNoContinuation)
  exact ⟨nestedFixtureAfterFocusedTerminalNoClosed.require
      (property := Core.ResidualRefinement.State.Available
        NestedFixtureFocusedTerminalDecision),
    ⟨continuation⟩,
    nestedFixtureAfterFocusedTerminalNoClosed.latest⟩

theorem focused_yes_continuation_accumulates :
    Nonempty
        (NestedFixtureFocusedDecision
          nestedFixtureAfterFocusedYesMapped.residual) ∧
      Nonempty
        (NestedFixtureFocusedYesContinuation
          nestedFixtureAfterFocusedYesMapped.residual) ∧
      Nonempty
        (NestedFixtureFocusedYesMapped
          nestedFixtureAfterFocusedYesMapped.residual) := by
  exact ⟨nestedFixtureAfterFocusedYesMapped.require
      (property := Core.ResidualRefinement.State.Available
        NestedFixtureFocusedDecision),
    nestedFixtureAfterFocusedYesMapped.require
      (property := Core.ResidualRefinement.State.Available
        NestedFixtureFocusedYesContinuation),
    nestedFixtureAfterFocusedYesMapped.latest⟩

theorem focused_yes_then_no_decision_accumulates :
    Nonempty
        (NestedFixtureFocusedYesContinuation
          nestedFixtureAfterFocusedActiveContinuation.residual) ∧
      Nonempty
        (NestedFixtureFocusedNestedDecision
          nestedFixtureAfterFocusedActiveContinuation.residual) ∧
      Nonempty
        (NestedFixtureFocusedNestedClosed
          nestedFixtureAfterFocusedActiveContinuation.residual) ∧
      Nonempty
        (NestedFixtureFocusedActiveContinuation
          nestedFixtureAfterFocusedActiveContinuation.residual) := by
  exact ⟨nestedFixtureAfterFocusedActiveContinuation.require
      (property := Core.ResidualRefinement.State.Available
        NestedFixtureFocusedYesContinuation),
    nestedFixtureAfterFocusedActiveContinuation.require
      (property := Core.ResidualRefinement.State.Available
        NestedFixtureFocusedNestedDecision),
    nestedFixtureAfterFocusedActiveContinuation.require
      (property := Core.ResidualRefinement.State.Available
        NestedFixtureFocusedNestedClosed),
    nestedFixtureAfterFocusedActiveContinuation.latest⟩

theorem focused_yes_continuation_derived_query_accumulates :
    Nonempty
        (NestedFixtureFinalNoActive
          nestedFixtureAfterFocusedYesMappedDerived.residual) ∧
      Nonempty
        (NestedFixtureFocusedYesContinuation
          nestedFixtureAfterFocusedYesMappedDerived.residual) ∧
      Nonempty
        (NestedFixtureFocusedYesMapped
          nestedFixtureAfterFocusedYesMappedDerived.residual) := by
  exact ⟨nestedFixtureAfterFocusedYesMappedDerived.require
      (property := Core.ResidualRefinement.State.Available
        NestedFixtureFinalNoActive),
    nestedFixtureAfterFocusedYesMappedDerived.require
      (property := Core.ResidualRefinement.State.Available
        NestedFixtureFocusedYesContinuation),
    nestedFixtureAfterFocusedYesMappedDerived.latest⟩

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
#print axioms no_continuation_transports_the_untouched_yes_edge
#print axioms every_certified_occurrence_is_positive
#print axioms exact_certificate_echo_retains_output
#print axioms fact_and_stage_produce_square
#print axioms one_lt_or_eq_decision_is_exhaustive
#print axioms nested_active_cursor_accumulates
#print axioms nested_active_decision_preserves_ledger
#print axioms active_cursor_derived_query_accumulates
#print axioms focused_yes_continuation_derived_query_accumulates
#print axioms active_cursor_branch_continuations_accumulate
#print axioms active_cursor_no_continuation_focus_accumulates
#print axioms focused_active_cursor_accumulates
#print axioms focused_no_closure_accumulates
#print axioms focused_yes_continuation_accumulates
#print axioms focused_yes_then_no_decision_accumulates

end StructuralExhaustion.Examples.ResidualRefinement
