import Mathlib.Combinatorics.SimpleGraph.Bipartite
import StructuralExhaustion.Graph.OpenPortSuppression

namespace MantelExample.K34OpenPortSuppression

open StructuralExhaustion

/-!
`K₃,₄` is the standard complete-bipartite extremal example behind Mantel's
theorem.  A vertex on its three-vertex side has degree four, while every
vertex on the four-vertex side is cubic.  Suppressing one such cubic port is
therefore a concrete non-Erdős instantiation of the reusable local graph
operation.
-/

abbrev Vertex := Fin 3 ⊕ Fin 4

def graph : SimpleGraph Vertex :=
  completeBipartiteGraph (Fin 3) (Fin 4)

def input : Graph.FiniteInput graph where
  vertices := inferInstance
  decideAdj := by
    intro left right
    cases left <;> cases right
    · exact .isFalse (by simp [graph, completeBipartiteGraph])
    · exact .isTrue (by simp [graph, completeBipartiteGraph])
    · exact .isTrue (by simp [graph, completeBipartiteGraph])
    · exact .isFalse (by simp [graph, completeBipartiteGraph])

def object : Graph.FiniteObject Vertex := ⟨graph, input⟩

def center : Vertex := Sum.inl 0
def endpoint : Vertex := Sum.inr 0
def firstShoulder : Vertex := Sum.inl 1
def secondShoulder : Vertex := Sum.inl 2

def setup : Graph.OpenPortSuppression.Setup object where
  center := center
  endpoint := endpoint
  first := firstShoulder
  second := secondShoulder
  endpoint_ne_center := by decide
  endpoint_ne_first := by decide
  endpoint_ne_second := by decide
  first_ne_second := by decide
  center_ne_first := by decide
  center_ne_second := by decide
  endpoint_neighbors := by
    intro vertex
    rcases vertex with left | right
    · fin_cases left <;>
        simp [object, graph, endpoint, center, firstShoulder, secondShoulder,
          completeBipartiteGraph]
    · simp [object, graph, endpoint, center, firstShoulder, secondShoulder,
        completeBipartiteGraph]
  open_shoulders := by
    simp [object, graph, firstShoulder, secondShoulder, completeBipartiteGraph]
  center_high := by decide

theorem source_minDegree : 3 ≤ object.minDegree := by
  decide

/-- The shared graph theorem proves the suppressed `K₃,₄` object still has
minimum degree three; the external example performs no path or graph search. -/
theorem suppressed_minDegree : 3 ≤ setup.suppressedObject.minDegree :=
  setup.minDegree_three source_minDegree

/-- The same operation has the strict packed-rank decrease consumed by the
minimal-counterexample activation layer. -/
theorem suppressed_rank_decreases :
    (Graph.PackedFiniteObject.pack setup.suppressedObject).lexRank <
      (Graph.PackedFiniteObject.pack object).lexRank :=
  setup.packedRank_lt

end MantelExample.K34OpenPortSuppression
