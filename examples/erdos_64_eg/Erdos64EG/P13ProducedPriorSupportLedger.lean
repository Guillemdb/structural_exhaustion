import Erdos64EG.CT14TypeBCanonicalOrdinaryFamily
import Erdos64EG.TypeANode63Support
import Erdos64EG.TypeBProducedSupportLedgerConnector
import StructuralExhaustion.Core.FiniteResidualLedger
import StructuralExhaustion.Graph.ResidualSupportRefinement

namespace Erdos64EG.Internal.P13ProducedPriorSupportLedger

open StructuralExhaustion

universe u v

variable {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}

/-!
# Exact prior Type-B and route-8 support events for cold F4

Only events emitted by an existing proof-carrying producer enter this ledger.
In particular, a node-[63] Type-A support is not relabelled as route 8: the
current Lean dependency chain has not yet implemented nodes [86]--[111].
-/

/-! ## Canonical ordinary node-[84] producer schedule -/

abbrev CanonicalOrdinaryEvent :=
  Node84GlobalFanMass.CanonicalOrdinary.Family (ctx := ctx)

namespace CanonicalOrdinaryEvent

noncomputable def declaredSupport
    (entry : CanonicalOrdinaryEvent (ctx := ctx)) : Finset ctx.G.Vertex :=
  (P13NegativeSupportLocalization.Canonical.cell ctx entry.index).core

theorem declaredSupport_subset_remainder
    (entry : CanonicalOrdinaryEvent (ctx := ctx)) :
    entry.declaredSupport ⊆ p13RemainderVertices ctx :=
  (P13NegativeSupportLocalization.Canonical.cell ctx entry.index).core_subset_remainder

end CanonicalOrdinaryEvent

abbrev CanonicalOrdinaryLedger := Core.FiniteResidualLedger.Ledger
  (CanonicalOrdinaryEvent (ctx := ctx))

noncomputable def canonicalOrdinarySupportProfile :
    Graph.ResidualSupportRefinement.Profile
      (Event := CanonicalOrdinaryEvent (ctx := ctx)) ctx.G.Vertex where
  vertexDecEq := ctx.G.object.input.vertices.decEq
  support := CanonicalOrdinaryEvent.declaredSupport

/-- The exact graph-owned ordinary ledger: its entry order is the filtered
canonical component order, not a caller-supplied list. -/
noncomputable def canonicalOrdinaryLedger :
    CanonicalOrdinaryLedger (ctx := ctx) :=
  Core.FiniteResidualLedger.Ledger.ofEnumeration
    Node84GlobalFanMass.CanonicalOrdinary.family

@[simp] theorem canonicalOrdinaryLedger_entries :
    (canonicalOrdinaryLedger (ctx := ctx)).entries =
      Node84GlobalFanMass.CanonicalOrdinary.family.orderedValues :=
  rfl

theorem canonicalOrdinaryLedger_complete
    (entry : CanonicalOrdinaryEvent (ctx := ctx)) :
    entry ∈ (canonicalOrdinaryLedger (ctx := ctx)).entries := by
  exact (canonicalOrdinaryLedger (ctx := ctx)).occurrence_mem entry

/-- Every canonical ordinary occurrence is converted to its exact node-[84]
source without changing occurrence identity or order. -/
noncomputable def canonicalOrdinarySources
    (node84 : VerifiedTypeBLocalFanMassPrefix ctx) :
    Core.FiniteResidualLedger.Ledger
      (Node84GlobalFanMass.OrdinarySupportSource node84) :=
  (canonicalOrdinaryLedger (ctx := ctx)).map
    (Node84GlobalFanMass.CanonicalOrdinary.source node84)

theorem canonicalOrdinarySource_mem
    (node84 : VerifiedTypeBLocalFanMassPrefix ctx)
    (entry : CanonicalOrdinaryEvent (ctx := ctx)) :
    (canonicalOrdinarySources node84).event entry =
        Node84GlobalFanMass.CanonicalOrdinary.source node84 entry ∧
      entry ∈ (canonicalOrdinarySources node84).entries := by
  exact ⟨rfl, (canonicalOrdinarySources node84).occurrence_mem entry⟩

/-- Exact ordinary Type-B input on the existing `[64] -> [65]` edge.  The
node-[61] negative support and node-[62] high-center witness remain fields of
this value; F4 therefore receives neither a reconstructed support nor a fresh
high-degree branch. -/
abbrev Node64To65Ordinary :=
  TypeBEntryRouting.VerifiedNode64Residual ctx

namespace Node64To65Ordinary

noncomputable def declaredSupport
    (entry : Node64To65Ordinary (ctx := ctx)) : Finset ctx.G.Vertex :=
  entry.support.core

theorem center_mem_declaredSupport
    (entry : Node64To65Ordinary (ctx := ctx)) :
    entry.highSurplus.center ∈ entry.declaredSupport :=
  entry.highSurplus.center_mem

theorem center_high (entry : Node64To65Ordinary (ctx := ctx)) :
    4 ≤ ctx.G.object.degree entry.highSurplus.center :=
  entry.highSurplus.high

end Node64To65Ordinary

/-- One actual route-8 output already produced by the Type-B local router.
The `routeExact` field in `extraction` proves that the predecessor selected
the route-8 constructor; `nonWindowCore` is therefore safe to expose to F4. -/
structure RecordedRouteEightExtraction where
  previous : VerifiedTypeBLocalFanMassPrefix ctx
  source : Node84GlobalFanMass.OrdinarySupportSource previous
  extraction : Node84GlobalFanMass.RouteEightExtraction source

namespace RecordedRouteEightExtraction

noncomputable def declaredSupport
    (entry : RecordedRouteEightExtraction (ctx := ctx)) : Finset ctx.G.Vertex :=
  entry.extraction.nonWindowCore

theorem declaredSupport_eq_source_core
    (entry : RecordedRouteEightExtraction (ctx := ctx)) :
    entry.declaredSupport = entry.source.scope.coreVertices :=
  entry.extraction.coreExact

theorem source_selected_route_eight
    (entry : RecordedRouteEightExtraction (ctx := ctx)) :
    ∃ result : entry.source.scope.B2RemainingNegative entry.source.noHigher,
      entry.source.route = .route8 result :=
  ⟨entry.extraction.result, entry.extraction.routeExact⟩

end RecordedRouteEightExtraction

abbrev DecoratedTypeBEvent :=
  TypeBProducedSupportLedgerConnector.RecordedDecoratedHandoff (ctx := ctx)

/-! One fixed event language for the existing F4 Type-B or route-8 handoff.
The three constructors are the three already-authored producer routes; they
are not new proof-diagram cases. -/
inductive PriorSupportEvent
  | ordinary (entry : Node64To65Ordinary (ctx := ctx))
  | decorated (entry : DecoratedTypeBEvent (ctx := ctx))
  | routeEight (entry : RecordedRouteEightExtraction (ctx := ctx))

abbrev Event := PriorSupportEvent (ctx := ctx)

noncomputable def eventSupport : Event (ctx := ctx) → Finset ctx.G.Vertex
  | .ordinary entry => entry.declaredSupport
  | .decorated entry => entry.declaredSupport
  | .routeEight entry => entry.declaredSupport

/-- Occurrence-primary persistent ledger.  Equal event values emitted at two
different proof steps remain distinct occurrences. -/
abbrev PersistentLedger := Core.FiniteResidualLedger.Ledger.{v, u + 3}
  (Event (ctx := ctx))

noncomputable def supportProfile :
    Graph.ResidualSupportRefinement.Profile
      (Event := Event (ctx := ctx)) ctx.G.Vertex where
  vertexDecEq := ctx.G.object.input.vertices.decEq
  support := eventSupport

/-- Exact occurrence-indexed support interpretation used by F4. -/
noncomputable def PersistentLedger.supportView
    (ledger : PersistentLedger (ctx := ctx)) :
    Graph.FiniteResidualSupportLedger.View ledger ctx.G.Vertex :=
  (supportProfile (ctx := ctx)).viewSchedule ledger

/-- F4 scans occurrences, not deduplicated event values. -/
theorem PersistentLedger.recognize_exact
    (ledger : PersistentLedger (ctx := ctx)) (vertex : ctx.G.Vertex) :
    match ledger.supportView.recognize vertex with
    | .found hit =>
        hit.event = ledger.event hit.occurrence ∧
          hit.occurrence ∈ ledger.entries ∧
          vertex ∈ eventSupport (ledger.event hit.occurrence) ∧
          ∀ earlier ∈ hit.before,
            vertex ∉ eventSupport (ledger.event earlier)
    | .absent _ =>
        ∀ occurrence : ledger.Occurrence,
          vertex ∉ eventSupport (ledger.event occurrence) := by
  cases result : ledger.supportView.recognize vertex with
  | found hit =>
      exact ⟨hit.eventExact, hit.occurrence_mem ledger.supportView vertex,
        hit.vertexMember, hit.beforeAbsent⟩
  | absent none =>
      exact none

theorem routeEight_event_has_exact_source_core
    (entry : RecordedRouteEightExtraction (ctx := ctx)) :
    eventSupport (.routeEight entry) = entry.source.scope.coreVertices :=
  entry.declaredSupport_eq_source_core

end Erdos64EG.Internal.P13ProducedPriorSupportLedger
