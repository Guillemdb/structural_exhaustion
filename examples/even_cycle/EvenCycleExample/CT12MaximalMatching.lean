import EvenCycleExample.Concrete
import StructuralExhaustion.Graph.MaximumMatching

namespace EvenCycleExample.MaximalMatching

open StructuralExhaustion

/-!
# External maximum-matching CT12 fixture

The reusable graph layer owns maximum matching selection, the selected-list
CT12 audit, the unmatched partition, and remainder edgelessness.  This file
only pins the execution on `K₄`.
-/

namespace ConcreteK4

open EvenCycleExample.ConcreteK4

noncomputable def execution :=
  Graph.MaximumMatching.run object (Graph.FiniteObject.context object)

theorem exhausted : execution.terminal = .exhausted :=
  Graph.MaximumMatching.run_terminal_exhausted object
    (Graph.FiniteObject.context object)

theorem bounded : execution.iterations ≤ object.input.vertices.card :=
  Graph.MaximumMatching.run_iterations_le_vertices object
    (Graph.FiniteObject.context object)

end ConcreteK4

end EvenCycleExample.MaximalMatching
