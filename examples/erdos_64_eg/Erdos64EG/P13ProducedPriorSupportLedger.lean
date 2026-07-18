import Erdos64EG.CT14TypeBCanonicalOrdinaryFamily
import Erdos64EG.TypeANode63Support
import Erdos64EG.TypeBProducedSupportLedgerConnector
import StructuralExhaustion.Core.FiniteResidualLedger
import StructuralExhaustion.Graph.ResidualSupportRefinement

namespace Erdos64EG.Internal.P13ProducedPriorSupportLedger

open StructuralExhaustion

universe u

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

abbrev CanonicalOrdinaryLedger := Core.FiniteProducedSupportLedger.Ledger
  (CanonicalOrdinaryEvent (ctx := ctx)) ctx.G.Vertex

/-- The exact graph-owned ordinary ledger: its entry order is the filtered
canonical component order, not a caller-supplied list. -/
noncomputable def canonicalOrdinaryLedger :
    CanonicalOrdinaryLedger (ctx := ctx) where
  entries := Node84GlobalFanMass.CanonicalOrdinary.family.orderedValues
  vertexDecEq := ctx.G.object.input.vertices.decEq
  support := CanonicalOrdinaryEvent.declaredSupport

@[simp] theorem canonicalOrdinaryLedger_entries :
    (canonicalOrdinaryLedger (ctx := ctx)).entries =
      Node84GlobalFanMass.CanonicalOrdinary.family.orderedValues :=
  rfl

theorem canonicalOrdinaryLedger_complete
    (entry : CanonicalOrdinaryEvent (ctx := ctx)) :
    entry ∈ (canonicalOrdinaryLedger (ctx := ctx)).entries := by
  exact Node84GlobalFanMass.CanonicalOrdinary.family.mem_orderedValues entry

/-- Every canonical ordinary entry is converted to its exact node-[84]
source; this is the source list consumed by the global fan-mass accounting. -/
noncomputable def canonicalOrdinarySources
    (node84 : VerifiedTypeBLocalFanMassPrefix ctx) :
    List (Node84GlobalFanMass.OrdinarySupportSource node84) :=
  (canonicalOrdinaryLedger (ctx := ctx)).entries.map
    (Node84GlobalFanMass.CanonicalOrdinary.source node84)

theorem canonicalOrdinarySource_mem
    (node84 : VerifiedTypeBLocalFanMassPrefix ctx)
    (entry : CanonicalOrdinaryEvent (ctx := ctx)) :
    Node84GlobalFanMass.CanonicalOrdinary.source node84 entry ∈
      canonicalOrdinarySources node84 := by
  exact List.mem_map_of_mem (canonicalOrdinaryLedger_complete entry)

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
abbrev PersistentLedger := Core.FiniteResidualLedger.Ledger.{u, u}
  (Event (ctx := ctx))

abbrev Ledger := Core.FiniteProducedSupportLedger.Ledger
  (Event (ctx := ctx)) ctx.G.Vertex

noncomputable def supportProfile :
    Graph.ResidualSupportRefinement.Profile
      (Event := Event (ctx := ctx)) ctx.G.Vertex where
  vertexDecEq := ctx.G.object.input.vertices.decEq
  support := eventSupport

noncomputable def PersistentLedger.initialState
    (ledger : PersistentLedger (ctx := ctx)) :=
  Core.ResidualRefinement.Ledger.initial ledger

/-- Compatibility projection for list-indexed consumers.  The list is the
exact persistent occurrence order mapped through `event`; equal event values
remain at distinct list positions. -/
noncomputable def PersistentLedger.materialize
    (ledger : PersistentLedger (ctx := ctx)) : Ledger (ctx := ctx) :=
  (supportProfile (ctx := ctx)).materialize ledger.initialState

theorem PersistentLedger.event_mem_materialize
    (ledger : PersistentLedger (ctx := ctx))
    (occurrence : ledger.Occurrence) :
    ledger.event occurrence ∈ ledger.materialize.entries := by
  exact List.mem_map_of_mem (ledger.occurrence_mem occurrence)

/-- Exact occurrence-indexed support interpretation used by F4. -/
noncomputable def PersistentLedger.supportView
    (ledger : PersistentLedger (ctx := ctx)) :
    Graph.FiniteResidualSupportLedger.View ledger ctx.G.Vertex :=
  (supportProfile (ctx := ctx)).view ledger.initialState

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

abbrev RouteEightLedger := Core.FiniteProducedSupportLedger.Ledger
  (RecordedRouteEightExtraction (ctx := ctx)) ctx.G.Vertex

abbrev OrdinaryTypeBLedger := Core.FiniteProducedSupportLedger.Ledger
  (Node64To65Ordinary (ctx := ctx)) ctx.G.Vertex

noncomputable def empty : Ledger (ctx := ctx) :=
  .empty ctx.G.object.input.vertices.decEq eventSupport

/-- Combine the exact events already emitted by the two producer call sites.
The left (Type-B) order is retained, followed by the right (route-8) order. -/
noncomputable def combine
    (ordinary : OrdinaryTypeBLedger (ctx := ctx))
    (typeB : TypeBProducedSupportLedgerConnector.Ledger (ctx := ctx))
    (routeEight : RouteEightLedger (ctx := ctx)) :
    Ledger (ctx := ctx) where
  entries := ordinary.entries.map PriorSupportEvent.ordinary ++
    typeB.entries.map PriorSupportEvent.decorated ++
    routeEight.entries.map PriorSupportEvent.routeEight
  vertexDecEq := ctx.G.object.input.vertices.decEq
  support := eventSupport

theorem combine_entries
    (ordinary : OrdinaryTypeBLedger (ctx := ctx))
    (typeB : TypeBProducedSupportLedgerConnector.Ledger (ctx := ctx))
    (routeEight : RouteEightLedger (ctx := ctx)) :
    (combine ordinary typeB routeEight).entries =
      ordinary.entries.map PriorSupportEvent.ordinary ++
        (typeB.entries.map PriorSupportEvent.decorated ++
          routeEight.entries.map PriorSupportEvent.routeEight) := by
  simp [combine, List.append_assoc]

/-- Every event in the combined branch ledger comes from one of the two
proof-carrying manuscript producers.  This is the provenance theorem used by
the cold F4 scan; an arbitrary unified event list is never needed. -/
theorem mem_combine_iff
    (ordinary : OrdinaryTypeBLedger (ctx := ctx))
    (typeB : TypeBProducedSupportLedgerConnector.Ledger (ctx := ctx))
    (routeEight : RouteEightLedger (ctx := ctx))
    (event : Event (ctx := ctx)) :
    event ∈ (combine ordinary typeB routeEight).entries ↔
      (∃ entry ∈ ordinary.entries, event = .ordinary entry) ∨
      (∃ entry ∈ typeB.entries, event = .decorated entry) ∨
      (∃ entry ∈ routeEight.entries, event = .routeEight entry) := by
  rw [combine_entries, List.mem_append, List.mem_append,
    List.mem_map, List.mem_map, List.mem_map]
  constructor
  · intro member
    rcases member with ⟨entry, entryMem, rfl⟩ |
      (⟨entry, entryMem, rfl⟩ | ⟨entry, entryMem, rfl⟩)
    · exact .inl ⟨entry, entryMem, rfl⟩
    · exact .inr (.inl ⟨entry, entryMem, rfl⟩)
    · exact .inr (.inr ⟨entry, entryMem, rfl⟩)
  · rintro (⟨entry, entryMem, rfl⟩ |
      ⟨entry, entryMem, rfl⟩ | ⟨entry, entryMem, rfl⟩)
    · exact .inl ⟨entry, entryMem, rfl⟩
    · exact .inr (.inl ⟨entry, entryMem, rfl⟩)
    · exact .inr (.inr ⟨entry, entryMem, rfl⟩)

/-- Record the exact existing `[64] -> [65]` ordinary edge.  The public F4
outcome remains the manuscript's Type-B handoff. -/
noncomputable def node64To65Ordinary
    (ledger : OrdinaryTypeBLedger (ctx := ctx))
    (entry : TypeBEntryRouting.VerifiedNode64Residual ctx) :
    OrdinaryTypeBLedger (ctx := ctx) :=
  ledger.record entry

theorem node64To65Ordinary_exact
    (ledger : OrdinaryTypeBLedger (ctx := ctx))
    (entry : TypeBEntryRouting.VerifiedNode64Residual ctx) :
    (node64To65Ordinary ledger entry).entries = ledger.entries ++ [entry] :=
  rfl

/-- Execute node [66] on an actual exit-(7) payload and append that identical
payload to the unified prior-support ledger. -/
noncomputable def node66AndRecord
    {ContextSafe ForbiddenFree CoreFree Uncompressible :
      Finset ctx.G.Vertex → Prop}
    {FanSafe : ctx.G.Vertex → ctx.G.Vertex → ctx.G.Vertex → Prop}
    (ledger : Ledger (ctx := ctx))
    (handoff : TypeBEntryRouting.Exit7Handoff ctx ContextSafe ForbiddenFree
      CoreFree Uncompressible FanSafe) :
    TypeBEntryRouting.Node66Residual ctx ContextSafe ForbiddenFree CoreFree
      Uncompressible FanSafe × Ledger (ctx := ctx) :=
  (TypeBEntryRouting.node66 ctx handoff,
    ledger.record (.decorated
      (TypeBProducedSupportLedgerConnector.recordedOfExit7 handoff)))

theorem node66AndRecord_exact
    {ContextSafe ForbiddenFree CoreFree Uncompressible :
      Finset ctx.G.Vertex → Prop}
    {FanSafe : ctx.G.Vertex → ctx.G.Vertex → ctx.G.Vertex → Prop}
    (ledger : Ledger (ctx := ctx))
    (handoff : TypeBEntryRouting.Exit7Handoff ctx ContextSafe ForbiddenFree
      CoreFree Uncompressible FanSafe) :
    (node66AndRecord ledger handoff).2.entries = ledger.entries ++
      [.decorated
        (TypeBProducedSupportLedgerConnector.recordedOfExit7 handoff)] :=
  rfl

/-- Append one literal route-8 extraction.  The only public constructor takes
the proof-carrying predecessor output, so an arbitrary Type-A support cannot
be inserted by this operation. -/
noncomputable def recordRouteEight
    (ledger : Ledger (ctx := ctx))
    (entry : RecordedRouteEightExtraction (ctx := ctx)) :
    Ledger (ctx := ctx) :=
  ledger.record (.routeEight entry)

theorem recordRouteEight_exact
    (ledger : Ledger (ctx := ctx))
    (entry : RecordedRouteEightExtraction (ctx := ctx)) :
    (recordRouteEight ledger entry).entries =
      ledger.entries ++ [.routeEight entry] :=
  rfl

theorem routeEight_event_has_exact_source_core
    (entry : RecordedRouteEightExtraction (ctx := ctx)) :
    eventSupport (.routeEight entry) = entry.source.scope.coreVertices :=
  entry.declaredSupport_eq_source_core

/-- Exact branch-total F4 scan over the already produced event list.  The
negative branch proves absence from every recorded support; it does not make
a claim about a support whose producer has not run. -/
theorem recognize_exact
    (ledger : Ledger (ctx := ctx)) (vertex : ctx.G.Vertex) :
    match ledger.recognize vertex with
    | .found event member holds =>
        event ∈ ledger.entries ∧ vertex ∈ ledger.support event
    | .absent _noneProof =>
        ∀ event ∈ ledger.entries, vertex ∉ ledger.support event := by
  unfold Core.FiniteProducedSupportLedger.Ledger.recognize
  cases result : Core.FiniteSearch.onList ledger.entries
      (ledger.Meets vertex) (ledger.meetsDecidable vertex) with
  | found event member holds =>
      exact ⟨member, holds⟩
  | absent noneProof =>
      exact noneProof

end Erdos64EG.Internal.P13ProducedPriorSupportLedger
