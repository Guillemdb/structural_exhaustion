import Mathlib.Combinatorics.SimpleGraph.Dart
import Mathlib.Data.FinEnum
import Hypostructure.Core.Problem

/-!
# Finite graph objects

The graph layer uses Mathlib's `SimpleGraph` directly.  `FiniteObject` adds
only an explicit vertex schedule and decidable adjacency, the data needed by
deterministic finite executors.  Packing the vertex type allows graph
coordinates to change it without introducing a second ambient graph model.
-/

namespace Hypostructure.Graph

universe u v

/-- A finite Mathlib simple graph with a fixed deterministic vertex schedule. -/
structure FiniteObject where
  Vertex : Type u
  graph : SimpleGraph Vertex
  vertices : FinEnum Vertex
  decideAdj : DecidableRel graph.Adj

namespace FiniteObject

/-- Pack a graph and its finite execution data without changing either. -/
def of {V : Type u} (graph : SimpleGraph V) (vertices : FinEnum V)
    (decideAdj : DecidableRel graph.Adj) : FiniteObject.{u} where
  Vertex := V
  graph := graph
  vertices := vertices
  decideAdj := decideAdj

end FiniteObject

/-- Register a graph problem without coupling its target to the ambient data. -/
def problem (Baseline : FiniteObject.{u} → Prop)
    (BranchState : FiniteObject.{u} → Type v) : Core.Problem where
  Ambient := FiniteObject.{u}
  Baseline := Baseline
  BranchState := BranchState

end Hypostructure.Graph
