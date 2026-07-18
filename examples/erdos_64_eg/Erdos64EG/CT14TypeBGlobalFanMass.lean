import Erdos64EG.CT14TypeBLocalFanMass
import StructuralExhaustion.Core.ExactHandoff
import StructuralExhaustion.Graph.NegativeSupportHandoff

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
  routeExact : previous.route scope noHigher = route

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
    (node84 : VerifiedTypeBLocalFanMassPrefix ctx) : Type (u + 1)
    extends Core.ExactHandoff node84 where
  Support : Type u
  Center : Type u
  Occurrence : Type u
  producer : TypeBGlobalFanMassProducer Support Center Occurrence
  OrdinaryFamily : Type u
  GroupedFamily : Type u
  ordinaryFamilySchedule : FinEnum OrdinaryFamily
  groupedFamilySchedule : FinEnum GroupedFamily
  canonicalOrdinarySource : OrdinaryFamily → OrdinarySupportSource previous
  canonicalGroupedSource : GroupedFamily → GroupedExitSevenEnvelopeSource
  ordinaryFamilySupport : OrdinaryFamily → Support
  groupedFamilySupport : GroupedFamily → Support
  ordinaryFamilySupportInjective : Function.Injective ordinaryFamilySupport
  groupedFamilySupportInjective : Function.Injective groupedFamilySupport
  familySupportsDisjoint : ∀ ordinary grouped,
    ordinaryFamilySupport ordinary ≠ groupedFamilySupport grouped
  ordinarySource : ∀ support,
    producer.profile.role support = .ordinary → OrdinarySupportSource previous
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

namespace Realization

noncomputable def stage
    {node84 : VerifiedTypeBLocalFanMassPrefix ctx}
    (realization : Realization node84) :
    realization.producer.profile.VerifiedStage ctx.toBranchContext :=
  realization.producer.profile.verifiedStage ctx.toBranchContext

end Realization

/-- Verified global output of node `[84]`.  The CT14 terminal, exact trace,
validity, totality, manuscript mass bound, and local quadratic check ledger
are all exposed rather than hidden behind the runner. -/
structure Verified
    (node84 : VerifiedTypeBLocalFanMassPrefix ctx) : Type (u + 1) where
  realization : Realization node84
  stage : realization.producer.profile.VerifiedStage ctx.toBranchContext
  terminal :
    (realization.producer.profile.run ctx.toBranchContext).terminal = .capacity
  trace :
    (realization.producer.profile.run ctx.toBranchContext).trace =
      [.entry, .lowerMass, .memberScan, .upperCapacity, .comparison,
        .capacityTerminal]
  valid :
    (realization.producer.profile.run ctx.toBranchContext).outcome.Valid
  traceValid : @CT14.Graph.ValidTrace PackedProblem
    (realization.producer.profile.capability PackedProblem)
    ctx.toBranchContext
    (realization.producer.profile.run ctx.toBranchContext).trace
  total : ∃ result : CT14.ExecutionResult
      (realization.producer.profile.capability PackedProblem)
      ctx.toBranchContext,
    result.outcome.Valid ∧ @CT14.Graph.ValidTrace PackedProblem
      (realization.producer.profile.capability PackedProblem)
      ctx.toBranchContext result.trace
  residualMassBound : realization.producer.profile.residualMass ≤
    416 * realization.producer.profile.globalSurplus
  workExact : realization.producer.profile.checks =
    2 * realization.producer.profile.supports.card *
        realization.producer.profile.occurrences.card +
      2 * realization.producer.profile.supports.card + 1
  quadraticWork : realization.producer.profile.checks ≤
    3 * (realization.producer.profile.supports.card + 1) *
      (realization.producer.profile.occurrences.card + 1)

noncomputable def verify
    {node84 : VerifiedTypeBLocalFanMassPrefix ctx}
    (realization : Realization node84) : Verified node84 := by
  let stage := realization.stage
  exact {
    realization := realization
    stage := stage
    terminal := stage.terminal
    trace := stage.trace
    valid := stage.verified
    traceValid := stage.traceValid
    total := stage.total
    residualMassBound := globalFanMass_bound_of_producer realization.producer
    workExact := stage.workExact
    quadraticWork := stage.quadraticWorkBound
  }

/-- A conditional handoff toward node `[85]`.  It records only the exact
verified global node-`[84]` output; it does not assert the sublinearity and global
deficit hypotheses still required to prove node `[85]`. -/
structure ConditionalNode85Handoff
    {node84 : VerifiedTypeBLocalFanMassPrefix ctx}
    (global : Verified node84) extends Core.ExactHandoff global where
  massBound : previous.realization.producer.profile.residualMass ≤
    416 * previous.realization.producer.profile.globalSurplus

def Verified.toConditionalNode85Handoff
    {node84 : VerifiedTypeBLocalFanMassPrefix ctx}
    (global : Verified node84) : ConditionalNode85Handoff global where
  previous := global
  previousExact := rfl
  massBound := global.residualMassBound

end Node84GlobalFanMass

end Erdos64EG.Internal
