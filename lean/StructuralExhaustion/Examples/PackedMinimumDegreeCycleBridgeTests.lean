import StructuralExhaustion.Graph.PackedMinimumDegreeCycle

namespace StructuralExhaustion.Examples

open StructuralExhaustion Graph

universe u

/-! A problem-independent fixture for the packed-to-fixed minimal-context
bridge.  No Erdős constants or graph data are used: the theorem is
polymorphic in the minimum-degree threshold and target predicate. -/

def bridgeFixture : Graph.PackedMinimumDegreeCycle.StaticInput where
  minimumDegree := 2
  LengthOK := fun length => length ≥ 3

theorem bridgeFixture_graph
    (ctx : Core.MinimalCounterexampleContext
      bridgeFixture.problem bridgeFixture.Target) :
    (bridgeFixture.fixedContext ctx).G = ctx.G.object := by
  exact Graph.PackedMinimumDegreeCycle.StaticInput.fixedContext_graph
    bridgeFixture ctx

theorem bridgeFixture_preserves_facts
    (ctx : Core.MinimalCounterexampleContext
      bridgeFixture.problem bridgeFixture.Target) :
    (bridgeFixture.fixedContext ctx).baseline = ctx.baseline ∧
      (bridgeFixture.fixedContext ctx).avoids = ctx.avoids := by
  exact ⟨
    Graph.PackedMinimumDegreeCycle.StaticInput.fixedContext_baseline
      bridgeFixture ctx,
    Graph.PackedMinimumDegreeCycle.StaticInput.fixedContext_avoids
      bridgeFixture ctx⟩

#print axioms bridgeFixture_graph
#print axioms bridgeFixture_preserves_facts

end StructuralExhaustion.Examples
