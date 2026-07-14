import Erdos64EG.CT12TypeBDemandSystem

namespace Erdos64EG.Internal

open StructuralExhaustion

universe u

/-!
# Cached graph reachability for Type B demand carriers

This module isolates the dependent universe-lift elaboration connecting the
heterogeneous Type B item type to literal graph paths. It contains no runner,
candidate-product enumeration, or graph search.
-/

namespace TypeBLocalEntry

set_option maxHeartbeats 800000 in
set_option linter.constructorNameAsVariable false in
/-- Every declared local carrier is connected to the literal fan center by
actual ambient graph edges. Certificate carriers lie one edge from the
center; positive-fan incidence endpoints lie at distance at most two. -/
theorem declaredCarrierSupport_reachable
    {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}
    (entry : TypeBLocalEntry ctx)
    (reserve : Graph.RefinedFanLedger.Reserve ctx.G.Vertex)
    {carrier : ctx.G.Vertex}
    (member : carrier ∈ (entry.selectionProfile reserve).declaredCarrierSupport) :
    ctx.G.object.graph.Reachable entry.center carrier := by
  cases entry with
  | certificate marked =>
      rw [selectionProfile_certificate] at member
      apply (marked.candidateProfile reserve.vertexReserve
        ).uliftItems_declaredCarrierSupport_of
          (fun carrier => ctx.G.object.graph.Reachable marked.fan.center carrier)
      · exact fun carrier member =>
          marked.declaredCarrierSupport_reachable reserve.vertexReserve member
      · exact member
  | positive entry =>
      rw [selectionProfile_positive] at member
      change ctx.G.object.graph.Reachable entry.fan.center carrier
      exact entry.declaredCarrierSupport_reachable
        reserve.incidenceReserve member

end TypeBLocalEntry

namespace TypeBAssignedSupport

variable
  {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}
  (support : TypeBAssignedSupport ctx)

/-- The whole declared carrier universe of one scheduled demand lies in the
ambient connected component of its scheduled center. -/
theorem demandSupport_reachable (demand : support.Demand)
    {carrier : ctx.G.Vertex}
    (member : carrier ∈ support.ledgerProfile.demandSupport demand) :
    ctx.G.object.graph.Reachable demand.1 carrier := by
  change carrier ∈
    (support.selectionProfile demand).declaredCarrierSupport at member
  rw [← support.entry_center demand]
  exact (support.entry demand).declaredCarrierSupport_reachable
    support.reserve member

end TypeBAssignedSupport

end Erdos64EG.Internal
