import Erdos64EG.TypeBFanShoulderIncidenceCoordinates
import StructuralExhaustion.Graph.TypeBFanIncidenceSupportClassification

namespace Erdos64EG.Internal.TypeBFanIncidenceSupportClassification

open StructuralExhaustion

universe u

variable {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}

open TypeBEntryRouting

/-- Exact local readiness decision on the ordinary node-`[64]` branch.  The
assigned set is the actual localized support core and the window set is the
literal maximum-packing covered set.  An ambient port endpoint outside the
core remains an explicit residual rather than being assigned by fiat. -/
noncomputable def classify
    (residual : VerifiedNode64Residual ctx)
    (coordinate : TypeBFanShoulderIncidenceCoordinates.Coordinate residual) :=
  Graph.TypeBFanIncidenceSupportClassification.Coordinate.classify ctx.G.object
    (TypeBFanShoulderIncidenceCoordinates.profile residual)
    residual.support.core (p13CoveredVertices ctx) coordinate

abbrev Endpoint
    (residual : VerifiedNode64Residual ctx)
    (coordinate : TypeBFanShoulderIncidenceCoordinates.Coordinate residual) :=
  Graph.TypeBFanIncidenceSupportClassification.Coordinate.endpoint ctx.G.object
    (TypeBFanShoulderIncidenceCoordinates.profile residual) coordinate

abbrev Shoulder
    (residual : VerifiedNode64Residual ctx)
    (coordinate : TypeBFanShoulderIncidenceCoordinates.Coordinate residual) :=
  Graph.TypeBFanIncidenceSupportClassification.Coordinate.shoulder ctx.G.object
    (TypeBFanShoulderIncidenceCoordinates.profile residual) coordinate

/-- Exact unassigned-incidence residual.  The two literal graph incidences are
retained with the proof that the cubic port endpoint is outside the localized
assigned core.  Existing predecessor facts do not make this case impossible. -/
structure EndpointOutsideResidual
    (residual : VerifiedNode64Residual ctx)
    (coordinate : TypeBFanShoulderIncidenceCoordinates.Coordinate residual) : Prop where
  endpointOutside : Endpoint residual coordinate ∉ residual.support.core
  centerEndpoint : ctx.G.object.graph.Adj residual.highSurplus.center
    (Endpoint residual coordinate)
  endpointShoulder : ctx.G.object.graph.Adj (Endpoint residual coordinate)
    (Shoulder residual coordinate)
  endpointNotRemainder : Endpoint residual coordinate ∉ p13RemainderVertices ctx
  endpointWindow : Endpoint residual coordinate ∈ p13CoveredVertices ctx

/-- Branch-specific D6 readiness route.  Only assigned endpoints proceed to
the window/non-window cases, and both retain node-`[61]` remainder provenance.
The endpoint-outside case remains a typed residual. -/
inductive Route
    (residual : VerifiedNode64Residual ctx)
    (coordinate : TypeBFanShoulderIncidenceCoordinates.Coordinate residual) : Type u where
  | endpointOutside (outside : EndpointOutsideResidual residual coordinate)
  | window
      (endpointAssigned : Endpoint residual coordinate ∈ residual.support.core)
      (endpointRemainder : Endpoint residual coordinate ∈ p13RemainderVertices ctx)
      (shoulderWindow : Shoulder residual coordinate ∈ p13CoveredVertices ctx)
  | nonWindow
      (endpointAssigned : Endpoint residual coordinate ∈ residual.support.core)
      (endpointRemainder : Endpoint residual coordinate ∈ p13RemainderVertices ctx)
      (shoulderRemainder : Shoulder residual coordinate ∈ p13RemainderVertices ctx)

private theorem shoulder_mem_remainder_of_not_covered
    (residual : VerifiedNode64Residual ctx)
    (coordinate : TypeBFanShoulderIncidenceCoordinates.Coordinate residual)
    (notCovered : Shoulder residual coordinate ∉ p13CoveredVertices ctx) :
    Shoulder residual coordinate ∈ p13RemainderVertices ctx := by
  letI : FinEnum ctx.G.Vertex := ctx.G.object.input.vertices
  letI : DecidableEq ctx.G.Vertex := ctx.G.object.input.vertices.decEq
  unfold p13RemainderVertices Graph.InducedPathPacking.remainderVertices
  simp only [Finset.mem_sdiff, Finset.mem_univ, true_and]
  exact notCovered

private theorem mem_covered_of_not_remainder (vertex : ctx.G.Vertex)
    (notRemainder : vertex ∉ p13RemainderVertices ctx) :
    vertex ∈ p13CoveredVertices ctx := by
  letI : FinEnum ctx.G.Vertex := ctx.G.object.input.vertices
  letI : DecidableEq ctx.G.Vertex := ctx.G.object.input.vertices.decEq
  by_contra notCovered
  apply notRemainder
  unfold p13CoveredVertices at notCovered
  unfold p13RemainderVertices Graph.InducedPathPacking.remainderVertices
  simp only [Finset.mem_sdiff, Finset.mem_univ, true_and]
  exact notCovered

/-- Execute the readiness route using only the literal core/window membership
tests. -/
noncomputable def route
    (residual : VerifiedNode64Residual ctx)
    (coordinate : TypeBFanShoulderIncidenceCoordinates.Coordinate residual) :
    Route residual coordinate := by
  cases classify residual coordinate with
  | endpointOutside outside =>
      have endpointNotRemainder :
          Endpoint residual coordinate ∉ p13RemainderVertices ctx := by
        intro endpointRemainder
        apply outside
        exact residual.remainder_neighbor_closed ctx
          residual.highSurplus.center_mem endpointRemainder
          (Graph.TypeBFanShoulderIncidenceCoordinate.Coordinate.center_incident
            ctx.G.object (TypeBFanShoulderIncidenceCoordinates.profile residual)
              coordinate)
      exact .endpointOutside {
        endpointOutside := outside
        centerEndpoint :=
          Graph.TypeBFanShoulderIncidenceCoordinate.Coordinate.center_incident
            ctx.G.object (TypeBFanShoulderIncidenceCoordinates.profile residual)
              coordinate
        endpointShoulder :=
          Graph.TypeBFanShoulderIncidenceCoordinate.Coordinate.shoulder_incident
            ctx.G.object (TypeBFanShoulderIncidenceCoordinates.profile residual)
              coordinate
        endpointNotRemainder := endpointNotRemainder
        endpointWindow := mem_covered_of_not_remainder _ endpointNotRemainder }
  | window endpointAssigned shoulderWindow =>
      exact .window endpointAssigned
        (residual.core_subset_remainder ctx endpointAssigned) shoulderWindow
  | nonWindow endpointAssigned shoulderNonWindow =>
      exact .nonWindow endpointAssigned
        (residual.core_subset_remainder ctx endpointAssigned)
        (shoulder_mem_remainder_of_not_covered residual coordinate
          shoulderNonWindow)

theorem route_preserves_node61
    (residual : VerifiedNode64Residual ctx) :
    residual.support = residual.node61.support ∧
      residual.previous = residual.node61.previous ∧
      residual.support.core ⊆ p13RemainderVertices ctx :=
  ⟨rfl, rfl, residual.core_subset_remainder ctx⟩

theorem exhaustive
    (residual : VerifiedNode64Residual ctx)
    (coordinate : TypeBFanShoulderIncidenceCoordinates.Coordinate residual) :
    (Graph.TypeBFanIncidenceSupportClassification.Coordinate.endpoint ctx.G.object
        (TypeBFanShoulderIncidenceCoordinates.profile residual) coordinate ∉
      residual.support.core) ∨
    (Graph.TypeBFanIncidenceSupportClassification.Coordinate.endpoint ctx.G.object
          (TypeBFanShoulderIncidenceCoordinates.profile residual) coordinate ∈
        residual.support.core ∧
      Graph.TypeBFanIncidenceSupportClassification.Coordinate.shoulder ctx.G.object
          (TypeBFanShoulderIncidenceCoordinates.profile residual) coordinate ∈
        p13CoveredVertices ctx) ∨
    (Graph.TypeBFanIncidenceSupportClassification.Coordinate.endpoint ctx.G.object
          (TypeBFanShoulderIncidenceCoordinates.profile residual) coordinate ∈
        residual.support.core ∧
      Graph.TypeBFanIncidenceSupportClassification.Coordinate.shoulder ctx.G.object
          (TypeBFanShoulderIncidenceCoordinates.profile residual) coordinate ∉
        p13CoveredVertices ctx) :=
  Graph.TypeBFanIncidenceSupportClassification.Coordinate.exhaustive ctx.G.object
    (TypeBFanShoulderIncidenceCoordinates.profile residual)
    residual.support.core (p13CoveredVertices ctx) coordinate

theorem checks_linear (residual : VerifiedNode64Residual ctx) :
    Graph.TypeBFanIncidenceSupportClassification.visibleChecks ctx.G.object
      (TypeBFanShoulderIncidenceCoordinates.profile residual) ≤
        4 * ctx.G.object.input.vertices.card :=
  Graph.TypeBFanIncidenceSupportClassification.visibleChecks_linear ctx.G.object
    (TypeBFanShoulderIncidenceCoordinates.profile residual)

end Erdos64EG.Internal.TypeBFanIncidenceSupportClassification
