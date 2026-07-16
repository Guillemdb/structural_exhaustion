import StructuralExhaustion.Core.WorkBudget
import StructuralExhaustion.Graph.TypeBFanShoulderIncidenceCoordinate

namespace StructuralExhaustion.Graph.TypeBFanIncidenceSupportClassification

open StructuralExhaustion

universe u

variable {V : Type u} (object : FiniteObject V)
variable (profile : TypeBFanShoulderIncidenceCoordinate.Profile object)
variable (assignedVertices windowVertices : Finset V)

/-!
# Readiness classification for D6 fan-window incidences

A shoulder incidence can enter the manuscript's assigned fan-window profile
only after its port endpoint is proved to belong to the assigned local
support.  This classifier makes that missing input explicit.  For every
already declared shoulder incidence it returns either an endpoint-outside
residual, or (only after endpoint membership is proved) the literal
window/non-window classification of the shoulder.

The classifier performs two finite-set membership reads at most.  It does not
add an assignment hypothesis, enumerate vertex subsets, or claim fan-closed or
hybrid-ledger semantics.
-/

abbrev Coordinate :=
  TypeBFanShoulderIncidenceCoordinate.Coordinate object profile

namespace Coordinate

abbrev endpoint (coordinate : Coordinate object profile) : V :=
  TypeBFanShoulderIncidenceCoordinate.Coordinate.endpoint object profile coordinate

abbrev shoulder (coordinate : Coordinate object profile) : V :=
  TypeBFanShoulderIncidenceCoordinate.Coordinate.shoulder object profile coordinate

inductive Result (coordinate : Coordinate object profile) where
  | endpointOutside
      (outside : coordinate.endpoint object profile ∉ assignedVertices)
  | window
      (endpointAssigned : coordinate.endpoint object profile ∈ assignedVertices)
      (shoulderWindow : coordinate.shoulder object profile ∈ windowVertices)
  | nonWindow
      (endpointAssigned : coordinate.endpoint object profile ∈ assignedVertices)
      (shoulderNonWindow : coordinate.shoulder object profile ∉ windowVertices)

noncomputable def classify (coordinate : Coordinate object profile) :
    coordinate.Result object profile assignedVertices windowVertices := by
  letI : DecidableEq V := object.input.vertices.decEq
  by_cases endpointAssigned : coordinate.endpoint object profile ∈ assignedVertices
  · by_cases shoulderWindow : coordinate.shoulder object profile ∈ windowVertices
    · exact .window endpointAssigned shoulderWindow
    · exact .nonWindow endpointAssigned shoulderWindow
  · exact .endpointOutside endpointAssigned

theorem exhaustive (coordinate : Coordinate object profile) :
    (coordinate.endpoint object profile ∉ assignedVertices) ∨
      (coordinate.endpoint object profile ∈ assignedVertices ∧
        coordinate.shoulder object profile ∈ windowVertices) ∨
      (coordinate.endpoint object profile ∈ assignedVertices ∧
        coordinate.shoulder object profile ∉ windowVertices) := by
  cases coordinate.classify object profile assignedVertices windowVertices with
  | endpointOutside outside => exact Or.inl outside
  | window endpointAssigned shoulderWindow =>
      exact Or.inr (Or.inl ⟨endpointAssigned, shoulderWindow⟩)
  | nonWindow endpointAssigned shoulderNonWindow =>
      exact Or.inr (Or.inr ⟨endpointAssigned, shoulderNonWindow⟩)

theorem classified_incidence (coordinate : Coordinate object profile) :
    object.graph.Adj (coordinate.endpoint object profile)
      (coordinate.shoulder object profile) :=
  TypeBFanShoulderIncidenceCoordinate.Coordinate.shoulder_incident object
    profile coordinate

end Coordinate

/-- Two membership reads for every already declared shoulder incidence. -/
def visibleChecks : Nat :=
  2 * (TypeBFanShoulderIncidenceCoordinate.coordinates object profile).card

theorem visibleChecks_linear :
    visibleChecks object profile ≤ 4 * object.input.vertices.card := by
  unfold visibleChecks
  have coordinateBound :=
    TypeBFanShoulderIncidenceCoordinate.visibleChecks_linear object profile
  change (TypeBFanShoulderIncidenceCoordinate.coordinates object profile).card ≤
    2 * object.input.vertices.card at coordinateBound
  omega

def budget : Core.PolynomialCheckBudget Unit where
  size := fun _ => object.input.vertices.card
  checks := fun _ => visibleChecks object profile
  coefficient := 4
  degree := 1
  bounded := by
    intro _unit
    calc
      visibleChecks object profile ≤ 4 * object.input.vertices.card :=
        visibleChecks_linear object profile
      _ ≤ 4 * (object.input.vertices.card + 1) ^ 1 := by simp

end StructuralExhaustion.Graph.TypeBFanIncidenceSupportClassification
