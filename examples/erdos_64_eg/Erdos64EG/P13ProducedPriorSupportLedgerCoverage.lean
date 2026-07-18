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
  Core.FiniteResidualLedger.Ledger
    (P13ProducedPriorSupportLedger.Node64To65Ordinary (ctx := ctx))

noncomputable def ledger (schedule : Schedule (ctx := ctx)) :
    P13ProducedPriorSupportLedger.OrdinaryTypeBLedger (ctx := ctx) where
  entries := schedule.entries.map schedule.event
  vertexDecEq := ctx.G.object.input.vertices.decEq
  support := P13ProducedPriorSupportLedger.Node64To65Ordinary.declaredSupport

theorem occurrence_mem (schedule : Schedule (ctx := ctx))
    (occurrence : schedule.Occurrence) :
    schedule.event occurrence ∈ (ledger schedule).entries := by
  exact List.mem_map_of_mem (schedule.occurrence_mem occurrence)

theorem entries_exact (schedule : Schedule (ctx := ctx)) :
    (ledger schedule).entries =
      schedule.entries.map schedule.event :=
  rfl

/-- The exact one-step schedule created when the existing node-[64] producer
emits one ordinary node-[65] input. -/
noncomputable def singleton
    (entry : P13ProducedPriorSupportLedger.Node64To65Ordinary (ctx := ctx)) :
    Schedule (ctx := ctx) :=
  Core.FiniteResidualLedger.Ledger.singleton entry

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

/-- Every grouped-family occurrence in the exact node-[84] realization,
in the realization's inherited order. -/
noncomputable def decoratedLedger
    (realization : Node84GlobalFanMass.Realization node84) :
    TypeBProducedSupportLedgerConnector.Ledger (ctx := ctx) where
  entries := realization.groupedFamilySchedule.orderedValues.map fun grouped =>
    recordedDecorated (realization.canonicalGroupedSource grouped)
  vertexDecEq := ctx.G.object.input.vertices.decEq
  support :=
    TypeBProducedSupportLedgerConnector.RecordedDecoratedHandoff.declaredSupport

theorem groupedOccurrence_mem
    (realization : Node84GlobalFanMass.Realization node84)
    (grouped : realization.GroupedFamily) :
    recordedDecorated (realization.canonicalGroupedSource grouped) ∈
      (decoratedLedger realization).entries := by
  exact List.mem_map_of_mem
    (realization.groupedFamilySchedule.mem_orderedValues grouped)

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
  previous := realization.previous
  source := realization.ordinarySource extracted.1
    (realization.extractedRoleOrdinary extracted.1 extracted.2)
  extraction := realization.extractedByRouteEight extracted.1 extracted.2

@[simp] theorem recordedRouteEight_core
    (realization : Node84GlobalFanMass.Realization node84)
    (extracted : ExtractedSupport realization) :
    (recordedRouteEight realization extracted).declaredSupport =
      (recordedRouteEight realization extracted).source.scope.coreVertices :=
  (recordedRouteEight realization extracted).declaredSupport_eq_source_core

/-- The complete route-8 ledger is the filtered support schedule already
carried by the node-[84] realization. -/
noncomputable def routeEightLedger
    (realization : Node84GlobalFanMass.Realization node84) :
    P13ProducedPriorSupportLedger.RouteEightLedger (ctx := ctx) where
  entries := (extractedSupports realization).orderedValues.map
    (recordedRouteEight realization)
  vertexDecEq := ctx.G.object.input.vertices.decEq
  support := P13ProducedPriorSupportLedger.RecordedRouteEightExtraction.declaredSupport

theorem extractedOccurrence_mem
    (realization : Node84GlobalFanMass.Realization node84)
    (extracted : ExtractedSupport realization) :
    recordedRouteEight realization extracted ∈
      (routeEightLedger realization).entries := by
  exact List.mem_map_of_mem
    ((extractedSupports realization).mem_orderedValues extracted)

end Global

/-! ## Exact three-producer aggregation -/

variable {node84 : VerifiedTypeBLocalFanMassPrefix ctx}

noncomputable def ordinaryPersistent
    (schedule : Ordinary.Schedule (ctx := ctx)) :
    P13ProducedPriorSupportLedger.PersistentLedger (ctx := ctx) :=
  schedule.map P13ProducedPriorSupportLedger.PriorSupportEvent.ordinary

noncomputable def decoratedPersistent
    (realization : Node84GlobalFanMass.Realization node84) :
    P13ProducedPriorSupportLedger.PersistentLedger (ctx := ctx) where
  Occurrence := realization.GroupedFamily
  occurrences := realization.groupedFamilySchedule
  event := fun grouped => .decorated
    (Global.recordedDecorated (realization.canonicalGroupedSource grouped))

noncomputable def routeEightPersistent
    (realization : Node84GlobalFanMass.Realization node84) :
    P13ProducedPriorSupportLedger.PersistentLedger (ctx := ctx) where
  Occurrence := Global.ExtractedSupport realization
  occurrences := Global.extractedSupports realization
  event := fun extracted => .routeEight
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
    (∃ entry ∈ (Ordinary.ledger ordinarySchedule).entries,
      (persistentBase ordinarySchedule realization).event occurrence =
        .ordinary entry) ∨
    (∃ entry ∈ (Global.decoratedLedger realization).entries,
      (persistentBase ordinarySchedule realization).event occurrence =
        .decorated entry) ∨
    (∃ entry ∈ (Global.routeEightLedger realization).entries,
      (persistentBase ordinarySchedule realization).event occurrence =
        .routeEight entry) := by
  rcases occurrence with occurrence | occurrence
  · exact .inl ⟨ordinarySchedule.event occurrence,
      Ordinary.occurrence_mem ordinarySchedule occurrence, rfl⟩
  · rcases occurrence with grouped | extracted
    · exact .inr (.inl ⟨Global.recordedDecorated
        (realization.canonicalGroupedSource grouped),
        Global.groupedOccurrence_mem realization grouped, rfl⟩)
    · exact .inr (.inr ⟨Global.recordedRouteEight realization extracted,
        Global.extractedOccurrence_mem realization extracted, rfl⟩)

/-- Branch-total state built from the ordinary occurrence schedule and the
two complete schedules already owned by the node-[84] realization.  The three
fields are exactly the three existing F4 families. -/
structure CompleteState where
  ordinarySchedule : Ordinary.Schedule (ctx := ctx)
  realization : Node84GlobalFanMass.Realization node84

noncomputable def CompleteState.ordinary
    (state : CompleteState (ctx := ctx) (node84 := node84)) :=
  Ordinary.ledger state.ordinarySchedule

noncomputable def CompleteState.decorated
    (state : CompleteState (ctx := ctx) (node84 := node84)) :=
  Global.decoratedLedger state.realization

noncomputable def CompleteState.routeEight
    (state : CompleteState (ctx := ctx) (node84 := node84)) :=
  Global.routeEightLedger state.realization

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
      [P13WeightedColdRestrictedPrefixPackage.PriorD6Origin
        state.ordinary state.decorated state.routeEight] :=
  (Core.ResidualRefinement.Ledger.initial
    (ordinaryPersistent state.ordinarySchedule)).add fun occurrence =>
      .inl ⟨state.ordinarySchedule.event occurrence,
        Ordinary.occurrence_mem state.ordinarySchedule occurrence, rfl⟩

noncomputable def CompleteState.decoratedState
    (state : CompleteState (ctx := ctx) (node84 := node84)) :
    Core.ResidualRefinement.Ledger
      (P13ProducedPriorSupportLedger.Event (ctx := ctx))
      [P13WeightedColdRestrictedPrefixPackage.PriorD6Origin
        state.ordinary state.decorated state.routeEight] :=
  (Core.ResidualRefinement.Ledger.initial
    (decoratedPersistent state.realization)).add fun grouped =>
      .inr (.inl ⟨Global.recordedDecorated
        (state.realization.canonicalGroupedSource grouped),
        Global.groupedOccurrence_mem state.realization grouped, rfl⟩)

noncomputable def CompleteState.routeEightState
    (state : CompleteState (ctx := ctx) (node84 := node84)) :
    Core.ResidualRefinement.Ledger
      (P13ProducedPriorSupportLedger.Event (ctx := ctx))
      [P13WeightedColdRestrictedPrefixPackage.PriorD6Origin
        state.ordinary state.decorated state.routeEight] :=
  (Core.ResidualRefinement.Ledger.initial
    (routeEightPersistent state.realization)).add fun extracted =>
      .inr (.inr ⟨Global.recordedRouteEight state.realization extracted,
        Global.extractedOccurrence_mem state.realization extracted, rfl⟩)

/-- The framework accumulator adds producer origin once and retains it for all
later nodes.  No downstream state repeats this provenance field. -/
noncomputable def CompleteState.baseState
    (state : CompleteState (ctx := ctx) (node84 := node84)) :
    P13WeightedColdRestrictedPrefixPackage.AccumulatedPriorD6Ledger
      state.ordinary state.decorated state.routeEight :=
  state.ordinaryState.append
    (state.decoratedState.append state.routeEightState)

/-- Compatibility projection for the existing list-indexed D6 runner. -/
noncomputable def CompleteState.ledger
    (state : CompleteState (ctx := ctx) (node84 := node84)) :=
  (P13WeightedColdRestrictedPrefixPackage.priorD6SupportProfile
    (ctx := ctx)).materialize state.baseState

noncomputable def completeState
    (ordinarySchedule : Ordinary.Schedule (ctx := ctx))
    (realization : Node84GlobalFanMass.Realization node84) :
    CompleteState (ctx := ctx) (node84 := node84) where
  ordinarySchedule := ordinarySchedule
  realization := realization

theorem ordinaryOccurrence_mem (state : CompleteState (ctx := ctx)
    (node84 := node84)) (occurrence : state.ordinarySchedule.Occurrence) :
    .ordinary (state.ordinarySchedule.event occurrence) ∈ state.ledger.entries := by
  exact P13ProducedPriorSupportLedger.PersistentLedger.event_mem_materialize
    (persistentBase state.ordinarySchedule state.realization) (.inl occurrence)

theorem decoratedOccurrence_mem (state : CompleteState (ctx := ctx)
    (node84 := node84)) (grouped : state.realization.GroupedFamily) :
    .decorated (Global.recordedDecorated
      (state.realization.canonicalGroupedSource grouped)) ∈
      state.ledger.entries := by
  exact P13ProducedPriorSupportLedger.PersistentLedger.event_mem_materialize
    (persistentBase state.ordinarySchedule state.realization) (.inr (.inl grouped))

theorem routeEightOccurrence_mem (state : CompleteState (ctx := ctx)
    (node84 := node84))
    (extracted : Global.ExtractedSupport state.realization) :
    .routeEight (Global.recordedRouteEight state.realization extracted) ∈
      state.ledger.entries := by
  exact P13ProducedPriorSupportLedger.PersistentLedger.event_mem_materialize
    (persistentBase state.ordinarySchedule state.realization) (.inr (.inr extracted))

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
    exact outside (.inl occurrence)
  · intro grouped
    exact outside (.inr (.inl grouped))
  · intro extracted
    exact outside (.inr (.inr extracted))

/-! ## Exact entry into the existing node-[153] continuation -/

variable {node21 : VerifiedP13MultiScaleCurvaturePrefix ctx}

namespace P13WeightedColdRestrictedPrefixPackage

variable (package : P13WeightedColdRestrictedPrefixPackage ctx node21)

/-- Repackage the complete three-producer aggregation as the already existing
D6 predecessor type.  Its list is the compatibility materialization of the
persistent base; no independent event list or support function is accepted. -/
noncomputable def completePriorD6State
    (state : CompleteState (ctx := ctx) (node84 := node84)) :
    Erdos64EG.Internal.P13WeightedColdRestrictedPrefixPackage.ProducedPriorD6State
      (ctx := ctx) :=
  Erdos64EG.Internal.P13WeightedColdRestrictedPrefixPackage.producedPriorD6State
    state.ordinary state.decorated state.routeEight
    state.baseState

theorem completePriorD6State_ledger_eq
    (state : CompleteState (ctx := ctx) (node84 := node84)) :
    ((completePriorD6State state).ledger (package := package)) = state.ledger := by
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
      package ((completePriorD6State state).ledger (package := package))) := by
  apply Erdos64EG.Internal.P13WeightedColdRestrictedPrefixPackage.exists_localCorridorSurvivor_of_branchExclusions
    package (completePriorD6State state) subcubic
  intro stage event member
  rw [completePriorD6State_ledger_eq package state] at member
  rcases List.mem_map.mp member with ⟨occurrence, _occurrenceMem, rfl⟩
  exact outsideProduced stage occurrence

end P13WeightedColdRestrictedPrefixPackage

end Erdos64EG.Internal.P13ProducedPriorSupportLedgerCoverage
