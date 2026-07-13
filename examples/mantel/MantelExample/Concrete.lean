import Mathlib.Combinatorics.SimpleGraph.Circulant
import MantelExample.Run

namespace MantelExample

open StructuralExhaustion

namespace ConcreteK4

/-! `K₄` violates the numerical Mantel bound.  It is intentionally not
triangle-free: this fixture executes and pins the CT11 localization machine
independently of the final graph-theoretic contradiction. -/

abbrev Vertex := Fin 4

def graph : SimpleGraph Vertex := ⊤

def input : Graph.FiniteInput graph where
  vertices := inferInstance
  decideAdj := by
    change DecidableRel fun left right : Vertex => left ≠ right
    infer_instance

def object : Graph.FiniteObject Vertex := ⟨graph, input⟩

theorem violation : object.input.vertices.card ^ 2 < 4 * object.edgeCount := by
  native_decide

def execution := ct11Run object violation

theorem terminal_localized : execution.terminal = .localized :=
  Graph.Mantel.run_terminal_localized object violation

theorem trace_exact : execution.trace =
    [.entry, .decomposition, .admissibility, .localization,
      .localizedTerminal] := by
  native_decide

theorem selected_dart_exact :
    (Graph.Mantel.offendingResidual object violation).cell.toProd = (0, 1) := by
  native_decide

end ConcreteK4

namespace ConcreteC5

/-! `C₅` is a non-bipartite triangle-free graph.  The external package only
checks its concrete input properties and invokes the framework theorem. -/

abbrev Vertex := Fin 5

def graph : SimpleGraph Vertex := SimpleGraph.cycleGraph 5

def input : Graph.FiniteInput graph where
  vertices := inferInstance
  decideAdj := by
    change DecidableRel (SimpleGraph.cycleGraph 5).Adj
    infer_instance

def object : Graph.FiniteObject Vertex := ⟨graph, input⟩

theorem triangleFree : object.graph.CliqueFree 3 := by
  letI : FinEnum Vertex := object.input.vertices
  letI : DecidableRel object.graph.Adj := object.input.decideAdj
  rw [← SimpleGraph.cliqueFinset_eq_empty_iff]
  native_decide

theorem edgeCount_exact : object.edgeCount = 5 := by
  native_decide

theorem mantel_bound : Target object := mantel object triangleFree

end ConcreteC5

end MantelExample
