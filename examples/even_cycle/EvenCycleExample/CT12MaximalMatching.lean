import EvenCycleExample.Concrete
import EvenCycleExample.CT1InducedEdge
import StructuralExhaustion.Graph.MaximumMatching
import StructuralExhaustion.Routes.CT1ToCT12

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

def ct1Source : Routes.CT1ToCT12.PackedC1
    (Graph.InducedPath.edgeProfile Vertex).encoding.spec
    (Graph.InducedPath.edgeInput object) :=
  ⟨(), Graph.InducedPath.edgeCertificate object InducedEdge.ConcreteK4.dart,
    trivial⟩

noncomputable def routeAdapter : Routes.CT1ToCT12.SemanticAdapter
    (S := (Graph.InducedPath.edgeProfile Vertex).encoding.spec)
    (input := Graph.InducedPath.edgeInput object)
    (CT12.ListPeeling.capability (Graph.FiniteObject.problem Vertex)
      (Graph.MaximumMatching.Edge object)) where
  trigger := fun _source => {
    load := (Graph.MaximumMatching.profile object).values.length
    state := CT12.ListPeeling.initialState
      (Graph.MaximumMatching.profile object).values
  }
  Evidence := fun _source _trigger => Graph.MaximumMatching.edges object ≠ []
  evidence := by
    intro source
    rcases source with ⟨_unit, certificate, _accepts⟩
    exact Graph.InducedPathPacking.windows_nonempty_of_realization object 2
      (by decide) ⟨certificate⟩

noncomputable def routedInput := Routes.CT1ToCT12.buildInput
  (CT12.ListPeeling.capability (Graph.FiniteObject.problem Vertex)
    (Graph.MaximumMatching.Edge object)) routeAdapter ct1Source

theorem routedInput_exact : routedInput =
    (Graph.MaximumMatching.profile object).input
      (Graph.FiniteObject.context object) := rfl

theorem route_id :
    ((Routes.CT1ToCT12.rule
      (CT12.ListPeeling.capability (Graph.FiniteObject.problem Vertex)
        (Graph.MaximumMatching.Edge object)) routeAdapter).generate
        ct1Source ()).routeId = "CT1.terminal.c1->CT12" :=
  Routes.CT1ToCT12.generated_route_id _ _ _

theorem routed_matching_nonempty : Graph.MaximumMatching.edges object ≠ [] :=
  Routes.CT1ToCT12.evidence_preserved _ routeAdapter ct1Source

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
