import Erdos64EG.P13WeightedColdRestrictedSurvivorFilter

namespace Erdos64EG.Internal.P13ProducedPriorSupportLedgerCoverage

open StructuralExhaustion
open StructuralExhaustion.Graph

universe u

variable {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}

namespace Ordinary

/-- The finite occurrence schedule emitted by the existing ordinary
`[64] -> [65]` producer.  This is the reusable occurrence-preserving core
schedule specialized to the exact node-[64] residual type. -/
abbrev Schedule :=
  Core.FiniteResidualLedger.Ledger.{u, u + 3}
    (P13ProducedPriorSupportLedger.Node64To65Ordinary (ctx := ctx))

/-- The exact one-step schedule created when the existing node-[64] producer
emits one ordinary node-[65] input. -/
noncomputable def singleton
    (entry : P13ProducedPriorSupportLedger.Node64To65Ordinary (ctx := ctx)) :
    Schedule (ctx := ctx) :=
  Core.FiniteResidualLedger.Ledger.singletonAt entry

@[simp] theorem singleton_event
    (entry : P13ProducedPriorSupportLedger.Node64To65Ordinary (ctx := ctx))
    (occurrence : (singleton entry).Occurrence) :
    (singleton entry).event occurrence = entry :=
  rfl

/-- Append two already produced ordinary schedules.  Sum-tagged occurrences
preserve production identity even if both steps emitted the same residual. -/
noncomputable def append
    (left right : Schedule (ctx := ctx)) : Schedule (ctx := ctx) :=
  left.append right

@[simp] theorem append_event_left
    (left right : Schedule (ctx := ctx))
    (occurrence : left.Occurrence) :
    (append left right).event (.inl occurrence) = left.event occurrence :=
  rfl

@[simp] theorem append_event_right
    (left right : Schedule (ctx := ctx))
    (occurrence : right.Occurrence) :
    (append left right).event (.inr occurrence) = right.event occurrence :=
  rfl

end Ordinary

namespace Global

variable {node84 : VerifiedTypeBLocalFanMassPrefix ctx}

/-- Convert one grouped exit-(7) source without changing its core, center,
first-neighbour family, arms, or semantic predicates. -/
noncomputable def recordedDecorated
    (source : Node84GlobalFanMass.GroupedExitSevenEnvelopeSource (ctx := ctx)) :
    TypeBProducedSupportLedgerConnector.RecordedDecoratedHandoff (ctx := ctx) where
  ContextSafe := source.ContextSafe
  ForbiddenFree := source.ForbiddenFree
  CoreFree := source.CoreFree
  Uncompressible := source.Uncompressible
  FanSafe := source.FanSafe
  source := source.source
  handoff := source.handoff

@[simp] theorem recordedDecorated_source
    (source : Node84GlobalFanMass.GroupedExitSevenEnvelopeSource (ctx := ctx)) :
    (recordedDecorated source).source = source.source :=
  rfl

@[simp] theorem recordedDecorated_handoff
    (source : Node84GlobalFanMass.GroupedExitSevenEnvelopeSource (ctx := ctx)) :
    (recordedDecorated source).handoff = source.handoff :=
  rfl

/-- Literal extracted support occurrences of the node-[84] realization. -/
abbrev ExtractedSupport
    (realization : Node84GlobalFanMass.Realization node84) :=
  {support : realization.Support //
    realization.producer.profile.extracted support}

@[implicit_reducible] noncomputable def extractedSupports
    (realization : Node84GlobalFanMass.Realization node84) :
    FinEnum (ExtractedSupport realization) :=
  Core.Enumeration.subtype realization.producer.profile.supports
    realization.producer.profile.extracted
    realization.producer.profile.extractedDecidable

/-- Convert exactly the route-8 extraction already stored for one extracted
node-[84] support. -/
noncomputable def recordedRouteEight
    (realization : Node84GlobalFanMass.Realization node84)
    (extracted : ExtractedSupport realization) :
    P13ProducedPriorSupportLedger.RecordedRouteEightExtraction (ctx := ctx) where
  previous := node84
  source := realization.ordinarySource extracted.1
    (realization.extractedRoleOrdinary extracted.1 extracted.2)
  extraction := realization.extractedByRouteEight extracted.1 extracted.2

@[simp] theorem recordedRouteEight_core
    (realization : Node84GlobalFanMass.Realization node84)
    (extracted : ExtractedSupport realization) :
    (recordedRouteEight realization extracted).declaredSupport =
      (recordedRouteEight realization extracted).source.scope.coreVertices :=
  (recordedRouteEight realization extracted).declaredSupport_eq_source_core

end Global

/-! ## Exact three-producer aggregation -/

variable {node84 : VerifiedTypeBLocalFanMassPrefix ctx}

noncomputable def ordinaryPersistent
    (schedule : Ordinary.Schedule (ctx := ctx)) :
    P13ProducedPriorSupportLedger.PersistentLedger (ctx := ctx) :=
  schedule.map fun entry => .first entry

noncomputable def decoratedPersistent
    (realization : Node84GlobalFanMass.Realization node84) :
    P13ProducedPriorSupportLedger.PersistentLedger (ctx := ctx) :=
  (Core.FiniteResidualLedger.Ledger.ofEnumeration
    realization.groupedFamilySchedule).map fun grouped => .second
      (Global.recordedDecorated (realization.canonicalGroupedSource grouped))

noncomputable def routeEightPersistent
    (realization : Node84GlobalFanMass.Realization node84) :
    P13ProducedPriorSupportLedger.PersistentLedger (ctx := ctx) :=
  (Core.FiniteResidualLedger.Ledger.ofEnumeration
    (Global.extractedSupports realization)).map fun extracted => .third
      (Global.recordedRouteEight realization extracted)

/-- The single persistent F4 base ledger.  Its occurrence type is the tagged
sum of the three existing producer schedules. -/
noncomputable def persistentBase
    (ordinarySchedule : Ordinary.Schedule (ctx := ctx))
    (realization : Node84GlobalFanMass.Realization node84) :
    P13ProducedPriorSupportLedger.PersistentLedger (ctx := ctx) :=
  (ordinaryPersistent ordinarySchedule).append
    ((decoratedPersistent realization).append
      (routeEightPersistent realization))

theorem persistentBase_event_origin
    (ordinarySchedule : Ordinary.Schedule (ctx := ctx))
    (realization : Node84GlobalFanMass.Realization node84)
    (occurrence : (persistentBase ordinarySchedule realization).Occurrence) :
    P13WeightedColdRestrictedPrefixPackage.PriorD6Origin
      ((persistentBase ordinarySchedule realization).event occurrence) := by
  rcases occurrence with occurrence | occurrence
  · simpa [persistentBase, ordinaryPersistent] using
      (P13WeightedColdRestrictedPrefixPackage.PriorD6Origin.ordinary
        (ordinarySchedule.event occurrence))
  · rcases occurrence with grouped | extracted
    · exact .decorated (Global.recordedDecorated
        (realization.canonicalGroupedSource grouped))
    · exact .routeEight (Global.recordedRouteEight realization extracted)

/-- Branch-total state built from the ordinary occurrence schedule and the
two complete schedules already owned by the node-[84] realization.  The three
fields are exactly the three existing F4 families. -/
structure CompleteState where
  ordinarySchedule : Ordinary.Schedule (ctx := ctx)
  realization : Node84GlobalFanMass.Realization node84

/-- The canonical persistent base is computed once from the two predecessor
states.  It is not a caller-overridable field. -/
noncomputable def CompleteState.base
    (state : CompleteState (ctx := ctx) (node84 := node84)) :=
  persistentBase state.ordinarySchedule state.realization

/- The producer proofs below are occurrence-sensitive, so they are installed
directly by `Ledger.add` after the framework maps the exact schedules. -/
noncomputable def CompleteState.ordinaryState
    (state : CompleteState (ctx := ctx) (node84 := node84)) :
    Core.ResidualRefinement.Ledger
      (P13ProducedPriorSupportLedger.Event (ctx := ctx))
      [P13WeightedColdRestrictedPrefixPackage.PriorD6Origin] :=
  Core.ResidualRefinement.Ledger.certify
    (ordinaryPersistent state.ordinarySchedule) fun occurrence => by
      simpa [ordinaryPersistent] using
        (P13WeightedColdRestrictedPrefixPackage.PriorD6Origin.ordinary
          (state.ordinarySchedule.event occurrence))

noncomputable def CompleteState.decoratedState
    (state : CompleteState (ctx := ctx) (node84 := node84)) :
    Core.ResidualRefinement.Ledger
      (P13ProducedPriorSupportLedger.Event (ctx := ctx))
      [P13WeightedColdRestrictedPrefixPackage.PriorD6Origin] :=
  Core.ResidualRefinement.Ledger.certify
    (decoratedPersistent state.realization) fun grouped =>
      .decorated (Global.recordedDecorated
        (state.realization.canonicalGroupedSource grouped))

noncomputable def CompleteState.routeEightState
    (state : CompleteState (ctx := ctx) (node84 := node84)) :
    Core.ResidualRefinement.Ledger
      (P13ProducedPriorSupportLedger.Event (ctx := ctx))
      [P13WeightedColdRestrictedPrefixPackage.PriorD6Origin] :=
  Core.ResidualRefinement.Ledger.certify
    (routeEightPersistent state.realization) fun extracted =>
      .routeEight (Global.recordedRouteEight state.realization extracted)

/-- The framework accumulator adds producer origin once and retains it for all
later nodes.  No downstream state repeats this provenance field. -/
noncomputable def CompleteState.baseState
    (state : CompleteState (ctx := ctx) (node84 := node84)) :
    P13WeightedColdRestrictedPrefixPackage.AccumulatedPriorD6Ledger
      (ctx := ctx) :=
  state.ordinaryState.append
    (state.decoratedState.append state.routeEightState)

noncomputable def completeState
    (ordinarySchedule : Ordinary.Schedule (ctx := ctx))
    (realization : Node84GlobalFanMass.Realization node84) :
    CompleteState (ctx := ctx) (node84 := node84) where
  ordinarySchedule := ordinarySchedule
  realization := realization

theorem ordinaryOccurrence_mem (state : CompleteState (ctx := ctx)
    (node84 := node84)) (occurrence : state.ordinarySchedule.Occurrence) :
    (.inl occurrence : state.baseState.residuals.Occurrence) ∈
      state.baseState.residuals.entries :=
  state.baseState.residuals.occurrence_mem (.inl occurrence)

theorem decoratedOccurrence_mem (state : CompleteState (ctx := ctx)
    (node84 := node84)) (grouped : state.realization.GroupedFamily) :
    (.inr (.inl grouped) : state.baseState.residuals.Occurrence) ∈
      state.baseState.residuals.entries :=
  state.baseState.residuals.occurrence_mem (.inr (.inl grouped))

theorem routeEightOccurrence_mem (state : CompleteState (ctx := ctx)
    (node84 := node84))
    (extracted : Global.ExtractedSupport state.realization) :
    (.inr (.inr extracted) : state.baseState.residuals.Occurrence) ∈
      state.baseState.residuals.entries :=
  state.baseState.residuals.occurrence_mem (.inr (.inr extracted))

/-- Absence from the complete combined ledger implies absence from every
literal producer occurrence, with no deduplication of equal supports. -/
theorem outside_all_produced_occurrences
    (state : CompleteState (ctx := ctx) (node84 := node84))
    (vertex : ctx.G.Vertex)
    (outside : ∀ occurrence : state.base.Occurrence,
      vertex ∉ P13ProducedPriorSupportLedger.eventSupport
        (state.base.event occurrence)) :
    (∀ occurrence : state.ordinarySchedule.Occurrence,
      vertex ∉ (state.ordinarySchedule.event occurrence).declaredSupport) ∧
    (∀ grouped : state.realization.GroupedFamily,
      vertex ∉ (Global.recordedDecorated
        (state.realization.canonicalGroupedSource grouped)).declaredSupport) ∧
    (∀ extracted : Global.ExtractedSupport state.realization,
      vertex ∉ (Global.recordedRouteEight state.realization extracted).declaredSupport) := by
  refine ⟨?_, ?_, ?_⟩
  · intro occurrence
    simpa [CompleteState.base, persistentBase, ordinaryPersistent,
      P13ProducedPriorSupportLedger.eventSupport] using
        outside (.inl occurrence)
  · intro grouped
    exact outside (.inr (.inl grouped))
  · intro extracted
    exact outside (.inr (.inr extracted))

/-! ## Exact entry into the existing node-[153] continuation -/

variable {node21 : VerifiedP13MultiScaleCurvaturePrefix ctx}

namespace P13WeightedColdRestrictedPrefixPackage

variable (package : P13WeightedColdRestrictedPrefixPackage ctx node21)

/-- Repackage the complete three-producer aggregation as the D6 predecessor
type without changing or materializing its occurrence ledger. -/
noncomputable def completePriorD6State
    (state : CompleteState (ctx := ctx) (node84 := node84)) :
    Erdos64EG.Internal.P13WeightedColdRestrictedPrefixPackage.ProducedPriorD6State
      (ctx := ctx) :=
  Erdos64EG.Internal.P13WeightedColdRestrictedPrefixPackage.producedPriorD6State
    state.baseState

theorem completePriorD6State_baseState_eq
    (state : CompleteState (ctx := ctx) (node84 := node84)) :
    (completePriorD6State state).baseState = state.baseState := by
  rfl

/-- Exact connector into `LocalCorridorSurvivor`: the D6-negative premise is
now checked against the occurrence-complete three-producer ledger. -/
theorem exists_localCorridorSurvivor_of_completeProducedLedger
    (state : CompleteState (ctx := ctx) (node84 := node84))
    (subcubic : ∀ stage : package.Stage,
      WalkTypeAD5Projection.NoHigh (package.ambientPrefix stage)
        (Erdos64EG.Internal.P13WeightedColdRestrictedPrefixPackage.minimumDegreeThree
          (ctx := ctx)))
    (outsideProduced : ∀ stage : package.Stage,
      ∀ occurrence : state.base.Occurrence,
        package.currentAmbientEndpoint stage ∉
          P13ProducedPriorSupportLedger.eventSupport
            (state.base.event occurrence)) :
    Nonempty (Erdos64EG.Internal.P13WeightedColdRestrictedPrefixPackage.LocalCorridorSurvivor
      package (completePriorD6State state)) := by
  apply Erdos64EG.Internal.P13WeightedColdRestrictedPrefixPackage.exists_localCorridorSurvivor_of_branchExclusions
    package (completePriorD6State state) subcubic
  intro stage occurrence
  exact outsideProduced stage occurrence

end P13WeightedColdRestrictedPrefixPackage

end Erdos64EG.Internal.P13ProducedPriorSupportLedgerCoverage
