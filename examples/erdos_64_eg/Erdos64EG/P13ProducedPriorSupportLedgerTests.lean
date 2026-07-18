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
    Node84GlobalFanMass.CanonicalOrdinary.source node84 entry ∈
      canonicalOrdinarySources node84 :=
  canonicalOrdinarySource_mem node84 entry

example
    {ContextSafe ForbiddenFree CoreFree Uncompressible :
      Finset ctx.G.Vertex → Prop}
    {FanSafe : ctx.G.Vertex → ctx.G.Vertex → ctx.G.Vertex → Prop}
    (ledger : Ledger (ctx := ctx))
    (handoff : TypeBEntryRouting.Exit7Handoff ctx ContextSafe ForbiddenFree
      CoreFree Uncompressible FanSafe) :
    (node66AndRecord ledger handoff).1 = TypeBEntryRouting.node66 ctx handoff :=
  rfl

example
    (ledger : Ledger (ctx := ctx))
    (entry : RecordedRouteEightExtraction (ctx := ctx)) :
    (recordRouteEight ledger entry).entries =
      ledger.entries ++ [.routeEight entry] :=
  recordRouteEight_exact ledger entry

example
    (entry : RecordedRouteEightExtraction (ctx := ctx)) :
    eventSupport (.routeEight entry) = entry.source.scope.coreVertices :=
  routeEight_event_has_exact_source_core entry

example
    (ledger : OrdinaryTypeBLedger (ctx := ctx))
    (entry : Node64To65Ordinary (ctx := ctx)) :
    (node64To65Ordinary ledger entry).entries = ledger.entries ++ [entry] :=
  node64To65Ordinary_exact ledger entry

example (entry : Node64To65Ordinary (ctx := ctx)) :
    entry.highSurplus.center ∈ eventSupport (.ordinary entry) :=
  Node64To65Ordinary.center_mem_declaredSupport entry

example (entry : Node64To65Ordinary (ctx := ctx)) :
    4 ≤ ctx.G.object.degree entry.highSurplus.center :=
  Node64To65Ordinary.center_high entry

example (ledger : Ledger (ctx := ctx)) (vertex : ctx.G.Vertex) :
    match ledger.recognize vertex with
    | .found event member holds =>
        event ∈ ledger.entries ∧ vertex ∈ ledger.support event
    | .absent _noneProof =>
        ∀ event ∈ ledger.entries, vertex ∉ ledger.support event :=
  recognize_exact ledger vertex

end Erdos64EG.Internal.P13ProducedPriorSupportLedger.Tests
