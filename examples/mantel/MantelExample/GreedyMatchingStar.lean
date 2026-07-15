import StructuralExhaustion.Core.GreedyMatchingStar

namespace MantelExample.GreedyMatchingStar

open StructuralExhaustion

/-!
# Matching--star transfer on the complete graph `K₄`

The six edges of the standard complete graph `K₄` form the concrete pair
schedule.  This external theorem package executes the same framework-owned
greedy matching--star stage used by the Erdős homogeneous-overload consumer.
-/

@[implicit_reducible]
def vertices : FinEnum (Fin 4) := inferInstance

def edges : Core.OrderedCollection
    (Core.Enumeration.OrderedDistinctPair vertices) :=
  (Core.Enumeration.orderedDistinctPairs vertices).toOrderedCollection

theorem edge_count : edges.values.length = 6 := by
  native_decide

noncomputable def stage :
    Core.GreedyMatchingStar.VerifiedStage vertices edges 2 :=
  Core.GreedyMatchingStar.verifiedStage vertices edges 2 (by native_decide)

/-- The reusable scan returns a literal two-edge matching or two-edge star in
the standard `K₄` edge schedule. -/
theorem matching_or_star :
    Nonempty (Core.GreedyMatchingStar.Pattern vertices edges 2) :=
  ⟨stage.pattern⟩

theorem work_exact :
    Core.GreedyMatchingStar.checks vertices edges = 108 := by
  native_decide

theorem work_quadratic :
    Core.GreedyMatchingStar.checks vertices edges ≤
      3 * (edges.values.length + 1) ^ 2 :=
  stage.polynomial

end MantelExample.GreedyMatchingStar
