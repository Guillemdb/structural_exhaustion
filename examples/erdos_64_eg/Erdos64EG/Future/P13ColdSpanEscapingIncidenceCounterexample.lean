import Erdos64EG.TargetAlgebra
import StructuralExhaustion.Graph.FiniteTwoBoundaryIncidenceOwnership

namespace Erdos64EG.Internal.P13ColdSpanEscapingIncidenceCounterexample

open StructuralExhaustion
open StructuralExhaustion.Graph

/-!
This is a target-aware local countermodel to the unsupported local implication

  `cubic induced corridor span + this escaping return is not target-realizing`
    `=> every internal incidence is owned by the two-boundary span`.

The displayed corridor is the induced path `0-1-2`.  Its internal vertex `1`
is cubic and has the escaping neighbour `3`.  The escaping edge returns to
the left boundary and closes a triangle, whose length `3` is not a power of
two.  Thus the literal escaping incidence is neither ruled out by the local
degree data nor, merely by its existence, an F1 target certificate.

This example does not model a global minimal counterexample.  It isolates the
local implication needed by the original F5 sentence: global minimality or
one of the declared D4--D7 clauses must supply an additional theorem routing
this exact incidence to F2, F3, F4, or contradiction.
-/

abbrev Vertex := Fin 4

def graph : SimpleGraph Vertex :=
  SimpleGraph.fromRel fun left right =>
    (left = 0 ∧ right = 1) ∨ (left = 1 ∧ right = 0) ∨
    (left = 1 ∧ right = 2) ∨ (left = 2 ∧ right = 1) ∨
    (left = 1 ∧ right = 3) ∨ (left = 3 ∧ right = 1) ∨
    (left = 0 ∧ right = 3) ∨ (left = 3 ∧ right = 0)

def object : FiniteObject Vertex where
  graph := graph
  input := {
    vertices := inferInstance
    decideAdj := by dsimp [graph]; infer_instance
  }

def support : Finset Vertex := {0, 1, 2}

def input : FiniteTwoBoundaryPiece.Input object where
  support := support
  left := 0
  right := 2
  left_mem := by simp [support]
  right_mem := by simp [support]
  left_ne_right := by decide

theorem span_is_induced_path :
    object.graph.Adj 0 1 ∧ object.graph.Adj 1 2 ∧ ¬object.graph.Adj 0 2 := by
  simp [object, graph]

theorem internal_vertex_cubic : object.degree 1 = 3 := by
  letI : DecidableRel object.graph.Adj := object.input.decideAdj
  native_decide

theorem escaping_internal_incidence :
    (1, 3) ∈
      FiniteTwoBoundaryIncidenceOwnership.escapingInternalIncidences input := by
  rw [FiniteTwoBoundaryIncidenceOwnership.mem_escapingInternalIncidences_iff]
  simp [input, support, object, graph]

theorem escaping_return_is_triangle :
    object.graph.Adj 0 1 ∧ object.graph.Adj 1 3 ∧ object.graph.Adj 3 0 := by
  simp [object, graph]

theorem triangle_length_not_target : ¬PowerOfTwoLength 3 := by
  rw [powerOfTwoLength_iff]
  rintro ⟨exponent, lower, equality⟩
  have powerLower : 2 ^ 2 ≤ 2 ^ exponent :=
    Nat.pow_le_pow_right (by decide) lower
  omega

theorem not_owned :
    ¬FiniteTwoBoundaryIncidenceOwnership.InternalIncidencesOwned input := by
  intro owned
  have inside := owned 1 (by simp [input, support]) (by decide) (by decide) 3
    (by simp [object, graph])
  exact (by native_decide : (3 : Vertex) ∉ support) inside

end Erdos64EG.Internal.P13ColdSpanEscapingIncidenceCounterexample
