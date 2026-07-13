import Mathlib.Combinatorics.SimpleGraph.Finite
import StructuralExhaustion.Core.Enumeration

namespace StructuralExhaustion.Graph

open StructuralExhaustion

universe u

/-!
# Finite graph execution inputs

The mathematical graph is Mathlib's `SimpleGraph`.  The only additional datum
needed by the exact reference machines is a Mathlib `FinEnum` value fixing the
order in which finite vertices are inspected.  Unlike a bare `Fintype`, a
`FinEnum` carries an explicit rank and therefore determines reproducible
first-hit machine semantics.
-/

/-- Static finite/executable data associated with a Mathlib simple graph.

Consumers install `input.vertices` as a local `FinEnum` and
`input.decideAdj` as a local adjacency decision procedure when invoking
Mathlib's finite graph API.  The standard Mathlib `Fintype` and
`DecidableEq` instances are then derived from that `FinEnum`; no parallel
finite-graph representation is introduced.
-/
structure FiniteInput {V : Type u} (G : SimpleGraph V) where
  vertices : FinEnum V
  decideAdj : DecidableRel G.Adj

namespace FiniteInput

/-- The number of vertices, computed in the declared machine order. -/
def card {V : Type u} {G : SimpleGraph V} (input : FiniteInput G) : Nat :=
  input.vertices.card

/-- The deterministic vertex list has exactly the declared `FinEnum` size. -/
theorem card_eq_orderedValues_length {V : Type u} {G : SimpleGraph V}
    (input : FiniteInput G) :
    input.card = input.vertices.orderedValues.length := by
  simp [card, FinEnum.orderedValues, FinEnum.toList]

end FiniteInput

end StructuralExhaustion.Graph
