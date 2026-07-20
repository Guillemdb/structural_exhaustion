import Erdos64EG.Future.P13ProducedPriorSupportLedgerCoverage

namespace Erdos64EG.Internal.P13ProducedPriorSupportLedgerCoverage.Tests

open StructuralExhaustion

universe u

variable {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}
variable {node84 : VerifiedTypeBLocalFanMassPrefix ctx}
variable {node21 : VerifiedP13MultiScaleCurvaturePrefix ctx}

example
    (entry : P13ProducedPriorSupportLedger.Node64To65Ordinary (ctx := ctx))
    (occurrence : (Ordinary.singleton entry).Occurrence) :
    (Ordinary.singleton entry).event occurrence = entry :=
  Ordinary.singleton_event entry occurrence

example
    (left right : Ordinary.Schedule (ctx := ctx))
    (occurrence : left.Occurrence) :
    (Ordinary.append left right).event (.inl occurrence) =
      left.event occurrence :=
  Ordinary.append_event_left left right occurrence

example
    (left right : Ordinary.Schedule (ctx := ctx))
    (occurrence : right.Occurrence) :
    (Ordinary.append left right).event (.inr occurrence) =
      right.event occurrence :=
  Ordinary.append_event_right left right occurrence

example (state : CompleteState (ctx := ctx) (node84 := node84))
    (occurrence : state.ordinarySchedule.Occurrence) :
    (.inl occurrence : (CompleteState.baseState state).residuals.Occurrence) ∈
      (CompleteState.baseState state).residuals.entries :=
  ordinaryOccurrence_mem state occurrence

example (state : CompleteState (ctx := ctx) (node84 := node84))
    (grouped : state.realization.GroupedFamily) :
    (.inr (.inl grouped) :
      (CompleteState.baseState state).residuals.Occurrence) ∈
      (CompleteState.baseState state).residuals.entries :=
  decoratedOccurrence_mem state grouped

example (state : CompleteState (ctx := ctx) (node84 := node84))
    (extracted : Global.ExtractedSupport state.realization) :
    (.inr (.inr extracted) :
      (CompleteState.baseState state).residuals.Occurrence) ∈
      (CompleteState.baseState state).residuals.entries :=
  routeEightOccurrence_mem state extracted

example (_package : P13WeightedColdRestrictedPrefixPackage ctx node21)
    (state : CompleteState (ctx := ctx) (node84 := node84)) :
    (P13WeightedColdRestrictedPrefixPackage.completePriorD6State state).baseState =
      CompleteState.baseState state :=
  P13WeightedColdRestrictedPrefixPackage.completePriorD6State_baseState_eq
    state

#print axioms outside_all_produced_occurrences
#print axioms persistentBase_event_origin
#print axioms P13ProducedPriorSupportLedger.PersistentLedger.recognize_exact
#print axioms Erdos64EG.Internal.P13WeightedColdRestrictedPrefixPackage.ProducedPriorD6State.recognizeF4_exact
#print axioms P13WeightedColdRestrictedPrefixPackage.exists_localCorridorSurvivor_of_completeProducedLedger

end Erdos64EG.Internal.P13ProducedPriorSupportLedgerCoverage.Tests
