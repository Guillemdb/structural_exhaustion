import Erdos64EG.P13WeightedColdRestrictedExactContinuation
import StructuralExhaustion.Graph.WalkOrderedSpan
import StructuralExhaustion.Graph.FiniteTwoBoundaryIncidenceOwnership

namespace Erdos64EG.Internal

open StructuralExhaustion
open StructuralExhaustion.Graph

universe u

variable {ctx : Core.MinimalCounterexampleContext
  PackedProblem.{u} PackedTarget.{u}}
variable {node21 : VerifiedP13MultiScaleCurvaturePrefix ctx}

namespace P13WeightedColdRestrictedPrefixPackage

variable (package : P13WeightedColdRestrictedPrefixPackage ctx node21)

/-- In the repeated F5 constructor the normalized structural state repeats,
but the actual moving boundary vertex does not.  This distinction is exactly
what a later graph-owned same-interface reconstruction must bridge. -/
noncomputable def repeated_actual_endpoint_ne
    {ledger : package.PriorD6Ledger}
    (survivor : package.LocalCorridorSurvivor ledger)
    (repetition : (package.coldStructuralCorridorProfile survivor).Repeated) :=
  package.currentAmbientEndpoint_ne_of_val_lt repetition.first repetition.second
    (package.repeated_stage_val_lt survivor repetition)

theorem repeated_first_val_eq_index_add_one
    {ledger : package.PriorD6Ledger}
    (survivor : package.LocalCorridorSurvivor ledger)
    (repetition : (package.coldStructuralCorridorProfile survivor).Repeated) :
    repetition.first.val = repetition.firstIndex + 1 := by
  have firstBound : repetition.firstIndex < package.positiveStages.values.length :=
    repetition.firstInBounds.trans_le
      (package.coldStructuralCorridorProfile survivor).inspectedStages_sublist.length_le
  rw [repetition.firstExact]
  simpa [Core.FiniteExactStateCorridor.Profile.inspectedStages,
    coldStructuralCorridorProfile] using
      package.positiveStages_getElem_val repetition.firstIndex firstBound

theorem repeated_second_val_eq_index_add_one
    {ledger : package.PriorD6Ledger}
    (survivor : package.LocalCorridorSurvivor ledger)
    (repetition : (package.coldStructuralCorridorProfile survivor).Repeated) :
    repetition.second.val = repetition.secondIndex + 1 := by
  have secondBound : repetition.secondIndex < package.positiveStages.values.length :=
    repetition.secondInBounds.trans_le
      (package.coldStructuralCorridorProfile survivor).inspectedStages_sublist.length_le
  rw [repetition.secondExact]
  simpa [Core.FiniteExactStateCorridor.Profile.inspectedStages,
    coldStructuralCorridorProfile] using
      package.positiveStages_getElem_val repetition.secondIndex secondBound

theorem repeated_stage_span_le_QCold
    {ledger : package.PriorD6Ledger}
    (survivor : package.LocalCorridorSurvivor ledger)
    (repetition : (package.coldStructuralCorridorProfile survivor).Repeated) :
    repetition.second.val - repetition.first.val ≤ QCold := by
  rw [package.repeated_first_val_eq_index_add_one survivor repetition,
    package.repeated_second_val_eq_index_add_one survivor repetition]
  have := repetition.span_le_bound
  have ordered := repetition.ordered
  simp only [coldStructuralCorridorProfile] at this
  omega

/-- The literal induced two-boundary piece on exactly the bounded path span
between the repeated positions.  This is the graph-owned cut promised by the
first half of the original F5 sentence; it does not yet claim ownership of
side incidences or an alternative representative. -/
noncomputable def repeatedSpanInput
    {ledger : package.PriorD6Ledger}
    (survivor : package.LocalCorridorSurvivor ledger)
    (repetition : (package.coldStructuralCorridorProfile survivor).Repeated) :
    FiniteTwoBoundaryPiece.Input
      (InducedPathRestrictedComponentBoundarySchedule.componentObject
        package.input) := by
  let path := InducedPathRestrictedComponentBoundarySchedule.componentPath
    package.input
  have ordered := package.repeated_stage_val_lt survivor repetition
  have secondLe : repetition.second.val ≤ path.length := by
    have secondBound := repetition.second.isLt
    have supportLength := path.length_support
    dsimp [path] at secondBound supportLength ⊢
    omega
  exact WalkOrderedSpan.twoBoundaryInput path
    (InducedPathRestrictedComponentBoundarySchedule.componentPath_isPath
      package.input)
    repetition.first.val repetition.second.val ordered secondLe

theorem repeatedSpanInput_card_le_QCold_add_one
    {ledger : package.PriorD6Ledger}
    (survivor : package.LocalCorridorSurvivor ledger)
    (repetition : (package.coldStructuralCorridorProfile survivor).Repeated) :
    (package.repeatedSpanInput survivor repetition).support.card ≤ QCold + 1 := by
  let path := InducedPathRestrictedComponentBoundarySchedule.componentPath
    package.input
  have ordered := package.repeated_stage_val_lt survivor repetition
  have secondLe : repetition.second.val ≤ path.length := by
    have secondBound := repetition.second.isLt
    have supportLength := path.length_support
    dsimp [path] at secondBound supportLength ⊢
    omega
  have localBound := WalkOrderedSpan.twoBoundaryInput_card_le_span_add_one
    path
    (InducedPathRestrictedComponentBoundarySchedule.componentPath_isPath
      package.input)
    repetition.first.val repetition.second.val ordered secondLe
  exact localBound.trans (Nat.add_le_add_right
    (package.repeated_stage_span_le_QCold survivor repetition) 1)

/-- Exact local side-incidence ledger of the bounded repeated span.  Its outer
schedule is the span support and each inner schedule is one declared neighbor
row; no ambient vertex scan is used. -/
noncomputable def repeatedSpanEscapingIncidences
    {ledger : package.PriorD6Ledger}
    (survivor : package.LocalCorridorSurvivor ledger)
    (repetition : (package.coldStructuralCorridorProfile survivor).Repeated) :=
  FiniteTwoBoundaryIncidenceOwnership.escapingInternalIncidences
    (package.repeatedSpanInput survivor repetition)

abbrev RepeatedSpanIncidencesOwned
    {ledger : package.PriorD6Ledger}
    (survivor : package.LocalCorridorSurvivor ledger)
    (repetition : (package.coldStructuralCorridorProfile survivor).Repeated) : Prop :=
  FiniteTwoBoundaryIncidenceOwnership.InternalIncidencesOwned
    (package.repeatedSpanInput survivor repetition)

theorem repeatedSpanEscapingIncidences_eq_nil_iff
    {ledger : package.PriorD6Ledger}
    (survivor : package.LocalCorridorSurvivor ledger)
    (repetition : (package.coldStructuralCorridorProfile survivor).Repeated) :
    package.repeatedSpanEscapingIncidences survivor repetition = [] ↔
      package.RepeatedSpanIncidencesOwned survivor repetition :=
  FiniteTwoBoundaryIncidenceOwnership.escapingInternalIncidences_eq_nil_iff _

noncomputable def repeatedSpanOwnershipDecidable
    {ledger : package.PriorD6Ledger}
    (survivor : package.LocalCorridorSurvivor ledger)
    (repetition : (package.coldStructuralCorridorProfile survivor).Repeated) :
    Decidable (package.RepeatedSpanIncidencesOwned survivor repetition) :=
  FiniteTwoBoundaryIncidenceOwnership.ownershipDecidable _

noncomputable def repeatedSpanOwnershipChecks
    {ledger : package.PriorD6Ledger}
    (survivor : package.LocalCorridorSurvivor ledger)
    (repetition : (package.coldStructuralCorridorProfile survivor).Repeated) : Nat :=
  FiniteTwoBoundaryIncidenceOwnership.visibleChecks
    (package.repeatedSpanInput survivor repetition)

/-- Every field genuinely derivable from the repeated F5 output before a
same-interface atom/replacement is constructed.  In particular this keeps
normalized-state equality separate from equality of actual boundary vertices. -/
structure RepeatedColdGermFrontier {ledger : package.PriorD6Ledger}
    (survivor : package.LocalCorridorSurvivor ledger)
    (f1Clear : package.F1Clear)
    (repetition : (package.coldStructuralCorridorProfile survivor).Repeated)
    (universal :
      (package.repeatedMatchedPriorPiecePair survivor repetition).UniversalTargetEquality)
    (negative :
      (package.repeatedMatchedPriorPiecePair survivor repetition).F3Negative) where
  support : package.RepeatedF5Support survivor f1Clear repetition
    universal negative
  pair : package.MatchedPriorPiecePair survivor
    repetition.second repetition.first
  pairExact : pair = package.repeatedMatchedPriorPiecePair survivor repetition
  structuralEqual : package.coldStructuralStateCode survivor repetition.first =
    package.coldStructuralStateCode survivor repetition.second
  cappedBoundaryDegreeEqual :
    package.activeBoundaryDegree repetition.first =
      package.activeBoundaryDegree repetition.second
  activeHalfEdgeRoleEqual :
    package.activeHalfEdgeEndpointRole repetition.first =
      package.activeHalfEdgeEndpointRole repetition.second
  actualMovingBoundaryDistinct :
    package.currentAmbientEndpoint repetition.first ≠
      package.currentAmbientEndpoint repetition.second
  spanBound : repetition.secondIndex - repetition.firstIndex ≤ QCold
  targetUniversal : pair.UniversalTargetEquality
  noProperPrefixRepresentative : pair.F3Negative

/-- Thin exact constructor from the original repeated F5 payload. -/
noncomputable def repeatedColdGermFrontier
    {ledger : package.PriorD6Ledger}
    (survivor : package.LocalCorridorSurvivor ledger)
    (f1Clear : package.F1Clear)
    (repetition : (package.coldStructuralCorridorProfile survivor).Repeated)
    (universal :
      (package.repeatedMatchedPriorPiecePair survivor repetition).UniversalTargetEquality)
    (negative :
      (package.repeatedMatchedPriorPiecePair survivor repetition).F3Negative)
    (support : package.RepeatedF5Support survivor f1Clear repetition
      universal negative) :
    package.RepeatedColdGermFrontier survivor f1Clear repetition
      universal negative := by
  exact {
    support := support
    pair := support.pair
    pairExact := support.pairExact
    structuralEqual := package.repeated_equal_structural_code survivor repetition
    cappedBoundaryDegreeEqual := support.pair.boundaryDegree_eq
    activeHalfEdgeRoleEqual := support.pair.activeHalfEdge_eq
    actualMovingBoundaryDistinct :=
      package.repeated_actual_endpoint_ne survivor repetition
    spanBound := support.spanBound
    targetUniversal := support.f2Universal
    noProperPrefixRepresentative := support.f3Negative
  }

/-- Every field genuinely derivable from the terminal F5 output.  The terminal
predecessor supplies one bounded actual corridor, but no second representative
or atom decomposition. -/
structure TerminalColdGermFrontier {ledger : package.PriorD6Ledger}
    (survivor : package.LocalCorridorSurvivor ledger)
    (f1Clear : package.F1Clear)
    (short : (package.coldStructuralCorridorProfile survivor).stages.values.length ≤
      (package.coldStructuralCorridorProfile survivor).stateBound) where
  support : package.TerminalF5Support survivor f1Clear short
  wholeCorridorIsPath :
    (InducedPathRestrictedComponentBoundarySchedule.componentPath
      package.input).IsPath
  supportBound :
    (InducedPathRestrictedComponentBoundarySchedule.componentPath
      package.input).support.length ≤ QCold + 1
  f1Negative : package.F1Clear
  f4Negative : ∀ stage : package.Stage,
    ∃ complete : package.D6Complete ledger stage,
      package.runD6 ledger stage = .complete complete

noncomputable def terminalColdGermFrontier
    {ledger : package.PriorD6Ledger}
    (survivor : package.LocalCorridorSurvivor ledger)
    (f1Clear : package.F1Clear)
    (short : (package.coldStructuralCorridorProfile survivor).stages.values.length ≤
      (package.coldStructuralCorridorProfile survivor).stateBound)
    (support : package.TerminalF5Support survivor f1Clear short) :
    package.TerminalColdGermFrontier survivor f1Clear short :=
  ⟨support, support.wholeCorridorIsPath, support.wholeCorridorSupportBound,
    support.f1Negative, support.f4Negative⟩

end P13WeightedColdRestrictedPrefixPackage

end Erdos64EG.Internal
