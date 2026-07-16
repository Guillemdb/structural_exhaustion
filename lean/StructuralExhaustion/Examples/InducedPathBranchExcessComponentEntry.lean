import StructuralExhaustion.Graph.InducedPathBranchExcessComponentEntry

namespace StructuralExhaustion.Examples.InducedPathBranchExcessComponentEntry

open StructuralExhaustion
open StructuralExhaustion.Graph

universe u

variable {V : Type u} {object : FiniteObject V}

/-! A non-Erdos transfer of the one-stub component-entry dichotomy. -/

theorem local_component_entry_is_total
    (producer : InducedPathColdCorridor.Producer object)
    (stub : InducedPathColdCorridor.CubicStub object) :
    (∃ boundary boundaryExact input inputExact,
      InducedPathBranchExcessComponentEntry.route producer stub =
        .component boundary boundaryExact input inputExact) ∨
    (∃ residual,
      InducedPathBranchExcessComponentEntry.route producer stub =
        .crossWindow residual) :=
  InducedPathBranchExcessComponentEntry.route_exhaustive producer stub

theorem local_component_entry_work
    (producer : InducedPathColdCorridor.Producer object)
    (stub : InducedPathColdCorridor.CubicStub object) :
    InducedPathBranchExcessComponentEntry.visibleChecks producer stub ≤
      object.input.vertices.card + 1 :=
  InducedPathBranchExcessComponentEntry.visibleChecks_le_linear producer stub

end StructuralExhaustion.Examples.InducedPathBranchExcessComponentEntry
