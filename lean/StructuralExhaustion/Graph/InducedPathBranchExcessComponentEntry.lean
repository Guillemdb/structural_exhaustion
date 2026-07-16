import StructuralExhaustion.Graph.InducedPathComponentBoundarySchedule

namespace StructuralExhaustion.Graph.InducedPathBranchExcessComponentEntry

open StructuralExhaustion
open InducedPathColdCorridor
open InducedPathColdSkeleton

universe u

variable {V : Type u} {object : FiniteObject V}

/-!
# Component entry for one literal branch-excess stub

The cold-corridor construction starts only after deciding whether the outside
endpoint of a selected window stub survives deletion of all ambient-cubic
windows.  A surviving endpoint gives the exact boundary stub and component
schedule input used by `InducedPathComponentBoundarySchedule`.  Otherwise the
same literal incidence is retained as a cross-window residual.

Only membership of the one supplied endpoint is tested.  No component, path,
graph, or context family is enumerated here.
-/

/-- A selected incidence whose other endpoint belongs to the deleted
ambient-cubic window union. -/
structure CrossWindowResidual (stub : CubicStub object) where
  stubExact : CubicStub object
  exact : stubExact = stub
  endpointDeleted : stub.neighbor ∈ deletedWindowVertices object

/-- Exact component-entry dichotomy for one graph-owned stub. -/
inductive Result (producer : Producer object) (stub : CubicStub object) where
  | component
      (boundary : BoundaryStub object)
      (boundaryTokenExact : boundary.token = stub.token)
      (input : InducedPathComponentBoundarySchedule.Input object)
      (inputAnchorExact : input.anchor = boundary)
  | crossWindow (residual : CrossWindowResidual stub)

/-- Inspect the endpoint of one literal incidence.  On the component branch,
the all-darts non-bridge theorem supplies the exact input required by the
existing component-boundary producer. -/
noncomputable def route (producer : Producer object) (stub : CubicStub object) :
    Result producer stub := by
  letI : DecidableEq V := object.input.vertices.decEq
  by_cases survives : stub.neighbor ∈ outsideVertices object
  · let boundary : BoundaryStub object := {
      token := stub.token
      cubic := stub.cubic
      outside := survives
    }
    let input : InducedPathComponentBoundarySchedule.Input object := {
      anchor := boundary
      notBridge := producer.notBridge stub.dart
    }
    exact .component boundary rfl input rfl
  · have endpointDeleted :
        stub.neighbor ∈ deletedWindowVertices object := by
      by_contra notDeleted
      apply survives
      rw [outsideVertices, Finset.mem_sdiff]
      exact ⟨object.mem_vertexFinset stub.neighbor, notDeleted⟩
    exact .crossWindow {
      stubExact := stub
      exact := rfl
      endpointDeleted := endpointDeleted
    }

theorem route_exhaustive (producer : Producer object) (stub : CubicStub object) :
    (∃ boundary boundaryExact input inputExact,
      route producer stub = .component boundary boundaryExact input inputExact) ∨
    (∃ residual, route producer stub = .crossWindow residual) := by
  cases equation : route producer stub with
  | component boundary boundaryExact input inputExact =>
      exact Or.inl ⟨boundary, boundaryExact, input, inputExact, rfl⟩
  | crossWindow residual => exact Or.inr ⟨residual, rfl⟩

/-- A supplied deleted-endpoint proof forces the cross-window constructor.
This is a one-token local decision; no owner or graph family is scanned. -/
theorem route_crossWindow_of_endpointDeleted
    (producer : Producer object) (stub : CubicStub object)
    (endpointDeleted : stub.neighbor ∈ deletedWindowVertices object) :
    ∃ residual, route producer stub = .crossWindow residual := by
  letI : DecidableEq V := object.input.vertices.decEq
  unfold route
  split
  next survives =>
    exact False.elim ((Finset.mem_sdiff.mp survives).2 endpointDeleted)
  next notSurvives =>
    exact ⟨_, rfl⟩

/-- The entry decision performs one membership test in the explicitly stored
deleted-window support. -/
def visibleChecks (_producer : Producer object) (_stub : CubicStub object) : Nat := 1

theorem visibleChecks_le_linear (producer : Producer object)
    (stub : CubicStub object) :
    visibleChecks producer stub ≤ object.input.vertices.card + 1 := by
  simp [visibleChecks]

end StructuralExhaustion.Graph.InducedPathBranchExcessComponentEntry
