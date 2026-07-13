import EvenCycleExample.Concrete
import StructuralExhaustion.Graph.InducedPath

namespace EvenCycleExample.InducedEdge

open StructuralExhaustion

/-!
# External induced-edge CT1 fixture

The reusable graph layer owns the complete induced-`P₂` CT1 profile.  This
external package supplies only a concrete graph edge and pins the resulting
terminal, trace, and work count.
-/

namespace ConcreteK4

open EvenCycleExample.ConcreteK4

def dart : graph.Dart :=
  ⟨(.v0, .v1), by simp [graph]⟩

def execution := Graph.InducedPath.runEdge object dart

theorem terminal_c1 : execution.result.terminal = .c1 :=
  Graph.InducedPath.runEdge_terminal object dart

theorem trace_exact : execution.result.trace =
    [.entry, .equivalenceCertification, .realizationDecision,
      .c1Terminal] :=
  Graph.InducedPath.runEdge_trace object dart

theorem one_check : execution.checks = 1 :=
  Graph.InducedPath.runEdge_checks object dart

end ConcreteK4

end EvenCycleExample.InducedEdge
