import Erdos64EG.P13ProducedPriorSupportLedger

namespace Erdos64EG.Internal.P13ProducedPriorSupportLedger.Tests

open StructuralExhaustion

universe u

variable {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}

example (entry : CanonicalOrdinaryEvent (ctx := ctx)) :
    entry ∈ (canonicalOrdinaryLedger (ctx := ctx)).entries :=
  canonicalOrdinaryLedger_complete entry

example (node84 : VerifiedTypeBLocalFanMassPrefix ctx)
    (entry : CanonicalOrdinaryEvent (ctx := ctx)) :
    (canonicalOrdinarySources node84).event entry =
        Node84GlobalFanMass.CanonicalOrdinary.source node84 entry ∧
      entry ∈ (canonicalOrdinarySources node84).entries :=
  canonicalOrdinarySource_mem node84 entry

example
    (entry : Node64To65Ordinary (ctx := ctx))
    (occurrence : (Core.FiniteResidualLedger.Ledger.singleton
      (.first entry : Event (ctx := ctx))).Occurrence) :
    (Core.FiniteResidualLedger.Ledger.singleton
      (.first entry : Event (ctx := ctx))).event occurrence =
        .first entry :=
  Core.FiniteResidualLedger.Ledger.singleton_event _ occurrence

example
    (left right : PersistentLedger (ctx := ctx))
    (occurrence : right.Occurrence) :
    (left.append right).event (.inr occurrence) = right.event occurrence :=
  Core.FiniteResidualLedger.Ledger.append_event_right left right occurrence

example
    (entry : RecordedRouteEightExtraction (ctx := ctx)) :
    eventSupport (.third entry) = entry.source.scope.coreVertices :=
  routeEight_event_has_exact_source_core entry

example (entry : Node64To65Ordinary (ctx := ctx)) :
    entry.highSurplus.center ∈ eventSupport (.first entry) :=
  Node64To65Ordinary.center_mem_declaredSupport entry

example (entry : Node64To65Ordinary (ctx := ctx)) :
    4 ≤ ctx.G.object.degree entry.highSurplus.center :=
  Node64To65Ordinary.center_high entry

example (ledger : PersistentLedger (ctx := ctx)) (vertex : ctx.G.Vertex) :
    match ledger.supportView.recognize vertex with
    | .found hit =>
        hit.event = ledger.event hit.occurrence ∧
          hit.occurrence ∈ ledger.entries ∧
          vertex ∈ eventSupport (ledger.event hit.occurrence) ∧
          ∀ earlier ∈ hit.before,
            vertex ∉ eventSupport (ledger.event earlier)
    | .absent _ =>
        ∀ occurrence : ledger.Occurrence,
          vertex ∉ eventSupport (ledger.event occurrence) :=
  PersistentLedger.recognize_exact ledger vertex

end Erdos64EG.Internal.P13ProducedPriorSupportLedger.Tests
