import StructuralExhaustion.Graph.FiniteTwoBoundaryIncidenceOwnership

namespace StructuralExhaustion.Examples.FiniteTwoBoundaryIncidenceOwnership

open StructuralExhaustion
open StructuralExhaustion.Graph

/-!
The span `0-3-1` in `K_{3,3}` is induced and every ambient vertex is cubic,
but its internal vertex `3` has the escaping neighbor `2`.  Thus induced-path
geometry plus the cubic degree condition does not imply two-boundary incidence
ownership.
-/

abbrev Vertex := Fin 6

def graph : SimpleGraph Vertex :=
  SimpleGraph.fromRel fun left right =>
    (left.val < 3 ∧ 3 ≤ right.val) ∨
      (right.val < 3 ∧ 3 ≤ left.val)

def object : FiniteObject Vertex where
  graph := graph
  input := {
    vertices := inferInstance
    decideAdj := by dsimp [graph]; infer_instance
  }

def support : Finset Vertex := {0, 3, 1}

def input : FiniteTwoBoundaryPiece.Input object where
  support := support
  left := 0
  right := 1
  left_mem := by simp [support]
  right_mem := by simp [support]
  left_ne_right := by decide

theorem ambient_cubic (vertex : Vertex) : object.degree vertex = 3 := by
  letI : DecidableRel object.graph.Adj := object.input.decideAdj
  fin_cases vertex <;> native_decide +revert

theorem span_is_induced_path :
    object.graph.Adj 0 3 ∧ object.graph.Adj 3 1 ∧ ¬object.graph.Adj 0 1 := by
  simp [object, graph]

theorem escaping_internal_incidence :
    (3, 2) ∈
      FiniteTwoBoundaryIncidenceOwnership.escapingInternalIncidences input := by
  rw [FiniteTwoBoundaryIncidenceOwnership.mem_escapingInternalIncidences_iff]
  simp [input, support, object, graph]

theorem not_owned :
    ¬FiniteTwoBoundaryIncidenceOwnership.InternalIncidencesOwned input := by
  intro owned
  have inside := owned 3 (by simp [input, support]) (by decide) (by decide) 2
    (by simp [object, graph])
  exact (by native_decide : (2 : Vertex) ∉ support) inside

example :
    FiniteTwoBoundaryIncidenceOwnership.escapingInternalIncidences input ≠ [] := by
  intro empty
  exact not_owned
    ((FiniteTwoBoundaryIncidenceOwnership.escapingInternalIncidences_eq_nil_iff
      input).mp empty)

end StructuralExhaustion.Examples.FiniteTwoBoundaryIncidenceOwnership
