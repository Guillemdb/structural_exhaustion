import Erdos64EG.Future.CT14TypeBLocalFanMass
import StructuralExhaustion.Graph.NegativeSupportHandoff
import StructuralExhaustion.Routes.Accumulated

namespace Erdos64EG.Internal

open StructuralExhaustion

universe u

/-!
# Original node [84]: global Type B fan-mass payload

Node `[84]` consumes a canonical finite family containing the ordinary Type B
supports and the grouped decorated Type A exit-`(7)` envelopes.  This module
defines the exact semantic producer and executes the support-indexed CT14
payload used on the existing `[84] -> [85]` edge.

No ambient vertex subset, graph, or context universe is enumerated: the only
scans are over the producer's three finite schedules.
-/

namespace Node84GlobalFanMass

variable
  {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}

/-- An ordinary support is literal node-`[84]` input data together with the
exact route selected by that predecessor. -/
structure OrdinarySupportSource
    (previous : VerifiedTypeBLocalFanMassPrefix ctx) where
  scope : TypeBSupportScope ctx
  noHigher : scope.NoHigherCenter
  route : scope.LocalFanMassRoute noHigher
  routeExact : (typeBLocalFanMassFacts previous).route scope noHigher = route

namespace OrdinarySupportSource

/-- The manuscript quantity `No_-(X)`, in the exact quarter-charge units used
by the existing assigned-support ledger. -/
noncomputable def noMinus
    {previous : VerifiedTypeBLocalFanMassPrefix ctx}
    (source : OrdinarySupportSource previous) : Nat :=
  Int.toNat (-source.scope.highCenterChargeProfile.netQuarterCharge)

end OrdinarySupportSource

/-- A grouped support retains an actual proof-carrying decorated handoff.  Its
four local predicates and fan-safety relation are data inherited from the
corresponding exit-`(7)` branch, not conclusions manufactured here. -/
structure GroupedExitSevenEnvelopeSource where
  ContextSafe : Finset ctx.G.Vertex → Prop
  ForbiddenFree : Finset ctx.G.Vertex → Prop
  CoreFree : Finset ctx.G.Vertex → Prop
  Uncompressible : Finset ctx.G.Vertex → Prop
  FanSafe : ctx.G.Vertex → ctx.G.Vertex → ctx.G.Vertex → Prop
  source : Graph.NegativeSupportHandoff.ConnectedNegativeSupport ctx.G.object
  handoff : Graph.NegativeSupportHandoff.DecoratedHandoff ctx.G.object
    ContextSafe ForbiddenFree CoreFree Uncompressible FanSafe source
  exitNumber : Nat
  exitNumberExact : exitNumber = 7

namespace GroupedExitSevenEnvelopeSource

/-- Exact negative part of the existing graph-defined charge on the grouped
decorated core. -/
noncomputable def noMinus
    (source : GroupedExitSevenEnvelopeSource (ctx := ctx)) : Nat :=
  Int.toNat (-(Graph.NegativeSupportHandoff.chargeProfile ctx.G.object
    source.source.core).netQuarterCharge)

end GroupedExitSevenEnvelopeSource

/-- Exact non-window core extraction data for a support discarded by route
`(8)`.  The extracted core is the literal node-`[84]` core, and the selected
route is propositionally the predecessor's route. -/
structure RouteEightExtraction
    {previous : VerifiedTypeBLocalFanMassPrefix ctx}
    (source : OrdinarySupportSource previous) where
  result : source.scope.B2RemainingNegative source.noHigher
  routeExact : source.route = .route8 result
  nonWindowCore : Finset ctx.G.Vertex
  coreExact : nonWindowCore = source.scope.coreVertices

/-- Concrete semantic producer for the global accounting inside node `[84]`.

`Support`, `Center`, and `Occurrence` are the actual finite types scanned by
the graph-owned profile.  The provenance fields identify each support with
the relevant manuscript family, identify each center with an actual high
vertex of `G`, and identify every extracted support with the exact route-`(8)`
core supplied after node `[84]`. -/
structure Realization
    (node84 : VerifiedTypeBLocalFanMassPrefix ctx) : Type (u + 1) where
  Support : Type u
  Center : Type u
  Occurrence : Type u
  producer : TypeBGlobalFanMassProducer Support Center Occurrence
  OrdinaryFamily : Type u
  GroupedFamily : Type u
  ordinaryFamilySchedule : FinEnum OrdinaryFamily
  groupedFamilySchedule : FinEnum GroupedFamily
  canonicalOrdinarySource : OrdinaryFamily → OrdinarySupportSource node84
  canonicalGroupedSource : GroupedFamily → GroupedExitSevenEnvelopeSource
  ordinaryFamilySupport : OrdinaryFamily → Support
  groupedFamilySupport : GroupedFamily → Support
  ordinaryFamilySupportInjective : Function.Injective ordinaryFamilySupport
  groupedFamilySupportInjective : Function.Injective groupedFamilySupport
  familySupportsDisjoint : ∀ ordinary grouped,
    ordinaryFamilySupport ordinary ≠ groupedFamilySupport grouped
  ordinarySource : ∀ support,
    producer.profile.role support = .ordinary → OrdinarySupportSource node84
  groupedSource : ∀ support,
    producer.profile.role support = .grouped → GroupedExitSevenEnvelopeSource
  ordinaryFamilyRole : ∀ ordinary,
    producer.profile.role (ordinaryFamilySupport ordinary) = .ordinary
  groupedFamilyRole : ∀ grouped,
    producer.profile.role (groupedFamilySupport grouped) = .grouped
  ordinaryFamilySourceExact : ∀ ordinary,
    ordinarySource (ordinaryFamilySupport ordinary)
      (ordinaryFamilyRole ordinary) = canonicalOrdinarySource ordinary
  groupedFamilySourceExact : ∀ grouped,
    groupedSource (groupedFamilySupport grouped)
      (groupedFamilyRole grouped) = canonicalGroupedSource grouped
  supportScheduleComplete : ∀ support : Support,
    (∃ ordinary : OrdinaryFamily,
      ordinaryFamilySupport ordinary = support) ∨
    (∃ grouped : GroupedFamily,
      groupedFamilySupport grouped = support)
  centerVertex : Center → ctx.G.Vertex
  centerVertexInjective : Function.Injective centerVertex
  centerHigh : ∀ center, 4 ≤ ctx.G.object.degree (centerVertex center)
  centerSurplusExact : ∀ center,
    producer.profile.centerSurplus center =
      ctx.G.object.degree (centerVertex center) - 3
  ordinaryOccurrenceInSupport : ∀ occurrence
    (roleExact : producer.profile.role
      (producer.profile.occurrenceSupport occurrence) = .ordinary),
      centerVertex (producer.profile.occurrenceCenter occurrence) ∈
        (ordinarySource (producer.profile.occurrenceSupport occurrence)
          roleExact).scope.vertices
  groupedOccurrenceIsDecorationCenter : ∀ occurrence
    (roleExact : producer.profile.role
      (producer.profile.occurrenceSupport occurrence) = .grouped),
      centerVertex (producer.profile.occurrenceCenter occurrence) =
        (groupedSource (producer.profile.occurrenceSupport occurrence)
          roleExact).handoff.center
  ordinaryCenterOccurrenceComplete : ∀ (support : Support)
    (roleExact : producer.profile.role support = .ordinary)
    (center : (ordinarySource support roleExact).scope.Center),
      ∃ occurrence : Occurrence,
        producer.profile.occurrenceSupport occurrence = support ∧
          centerVertex (producer.profile.occurrenceCenter occurrence) = center.1
  groupedDecorationOccurrenceComplete : ∀ (support : Support)
    (roleExact : producer.profile.role support = .grouped),
      ∃ occurrence : Occurrence,
        producer.profile.occurrenceSupport occurrence = support ∧
          centerVertex (producer.profile.occurrenceCenter occurrence) =
            (groupedSource support roleExact).handoff.center
  ordinaryOccurrenceExact : ∀ (support : Support)
    (roleExact : producer.profile.role support = .ordinary)
    (vertex : ctx.G.Vertex),
      vertex ∈ (ordinarySource support roleExact).scope.highCenters ↔
        ∃ occurrence : Occurrence,
          producer.profile.occurrenceSupport occurrence = support ∧
            centerVertex (producer.profile.occurrenceCenter occurrence) = vertex
  groupedOccurrenceExact : ∀ (support : Support)
    (roleExact : producer.profile.role support = .grouped)
    (vertex : ctx.G.Vertex),
      vertex = (groupedSource support roleExact).handoff.center ↔
        ∃ occurrence : Occurrence,
          producer.profile.occurrenceSupport occurrence = support ∧
            centerVertex (producer.profile.occurrenceCenter occurrence) = vertex
  ordinaryDeficitExact : ∀ (support : Support)
    (roleExact : producer.profile.role support = .ordinary),
      producer.profile.deficit support =
        (ordinarySource support roleExact).noMinus
  groupedDeficitExact : ∀ (support : Support)
    (roleExact : producer.profile.role support = .grouped),
      producer.profile.deficit support =
        (groupedSource support roleExact).noMinus
  ordinaryCoefficient208IncidenceBound : ∀ support,
    producer.profile.role support = .ordinary →
      ¬ producer.profile.extracted support →
      producer.profile.deficit support ≤
        208 * producer.profile.supportTokenMass support
  groupedCoefficient208IncidenceBound : ∀ support,
    producer.profile.role support = .grouped →
      ¬ producer.profile.extracted support →
      producer.profile.deficit support ≤
        208 * producer.profile.supportTokenMass support
  withinRoleCenterDisjointness : Function.Injective (fun occurrence ↦
    (producer.profile.role (producer.profile.occurrenceSupport occurrence),
      producer.profile.occurrenceCenter occurrence))
  extractedRoleOrdinary : ∀ support, producer.profile.extracted support →
    producer.profile.role support = .ordinary
  extractedByRouteEight : ∀ support
    (extracted : producer.profile.extracted support),
      RouteEightExtraction
        (ordinarySource support (extractedRoleOrdinary support extracted))

noncomputable def target
    {node84 : VerifiedTypeBLocalFanMassPrefix ctx}
    (realization : Realization node84) :=
  (realization.producer.profile.capability PackedProblem.{u}).executableInterface

noncomputable def adapter
    {node84 : VerifiedTypeBLocalFanMassPrefix ctx}
    (realization : Realization node84) :
    Routes.Accumulated.Adapter (VerifiedTypeBLocalFanMassPrefix ctx)
      (target realization) where
  targetContext := fun _source => ctx.toBranchContext
  trigger := fun _source => ⟨⟩

noncomputable def transitionStage
    {node84 : VerifiedTypeBLocalFanMassPrefix ctx}
    (realization : Realization node84) :=
  Routes.Accumulated.advanceCurrent (target realization) (adapter realization)
    (Core.Routing.ResidualStage.exact (tactic := .ct14) node84)

abbrev TransitionLedger
    {node84 : VerifiedTypeBLocalFanMassPrefix ctx}
    (realization : Realization node84) :=
  Routes.Accumulated.OutputLedger (sourceTactic := .ct14)
    (target realization) (adapter realization)
    (Core.Routing.ResidualStage.exact (tactic := .ct14) node84)

structure Facts
    {node84 : VerifiedTypeBLocalFanMassPrefix ctx}
    (realization : Realization node84)
    (execution : TransitionLedger realization) : Prop where
  verified : realization.producer.profile.VerifiedExecutionStage
    ctx.toBranchContext execution.targetResult
  residualMassBound : realization.producer.profile.residualMass ≤
    416 * realization.producer.profile.globalSurplus

abbrev Ledger
    {node84 : VerifiedTypeBLocalFanMassPrefix ctx}
    (realization : Realization node84) :=
  Core.Routing.LedgerExtension (TransitionLedger realization)
    (Facts realization)

noncomputable def ledgerStage
    {node84 : VerifiedTypeBLocalFanMassPrefix ctx}
    (realization : Realization node84) :
    Core.Routing.ResidualStage .ct14 (Ledger realization) := by
  let execution := transitionStage realization
  exact execution.extend {
    verified := Graph.SupportIndexedFanMass.Profile.verifiedExecutionStage
      realization.producer.profile ctx.toBranchContext
        execution.output.targetResult rfl
    residualMassBound := globalFanMass_bound_of_producer realization.producer
  }

/-- Verified global output of node `[84]`, consisting only of the semantic
producer and its framework-owned accumulated CT14 ledger. -/
structure Verified
    (node84 : VerifiedTypeBLocalFanMassPrefix ctx) : Type (u + 3) where
  realization : Realization node84
  ledgerStage : Core.Routing.ResidualStage .ct14 (Ledger realization)

def Verified.facts
    {node84 : VerifiedTypeBLocalFanMassPrefix ctx}
    (global : Verified node84) :=
  global.ledgerStage.output.added

theorem Verified.residualMassBound
    {node84 : VerifiedTypeBLocalFanMassPrefix ctx}
    (global : Verified node84) :
    global.realization.producer.profile.residualMass ≤
      416 * global.realization.producer.profile.globalSurplus :=
  global.ledgerStage.output.added.residualMassBound

noncomputable def verify
    {node84 : VerifiedTypeBLocalFanMassPrefix ctx}
    (realization : Realization node84) : Verified node84 :=
  ⟨realization, ledgerStage realization⟩

end Node84GlobalFanMass

end Erdos64EG.Internal
