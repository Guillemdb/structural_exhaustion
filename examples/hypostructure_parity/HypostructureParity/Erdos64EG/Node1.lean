import Erdos64EG.Node1
import HypostructureErdos64EG.Node1

namespace HypostructureParity.Erdos64EG.Node1

open Hypostructure

universe u

/-!
# Diagram node 1 parity

The immutable proof diagram assigns node `[1]` only the finite simple theorem-
root graph and sends it directly to node `[2]`.  The minimum-degree-three
proposition is the root theorem baseline consumed by node `[2]`; target
avoidance is not asserted here.

This module compares the two implementations through that paper-visible
surface.  It neither equates their residual records nor imports legacy code
into the Hypostructure application.
-/

/-- Test-only legacy packaging of the exact graph and finite schedule carried
by a Hypostructure graph object.  No proof or downstream output is copied. -/
def legacyView (object : Graph.FiniteObject.{u}) :
    StructuralExhaustion.Graph.FiniteObject object.Vertex where
  graph := object.graph
  input := {
    vertices := object.vertices
    decideAdj := object.decideAdj
  }

/-- Both node-1 representations expose literally the same Mathlib graph. -/
@[simp]
theorem legacyView_graph (object : Graph.FiniteObject.{u}) :
    (legacyView object).graph = object.graph :=
  rfl

/-- The normalized finite vertex count agrees at the theorem root. -/
@[simp]
theorem legacyView_vertexCount (object : Graph.FiniteObject.{u}) :
    (legacyView object).input.vertices.card = object.vertexCount :=
  rfl

/-- The normalized finite edge count agrees at the theorem root. -/
theorem legacyView_edgeCount (object : Graph.FiniteObject.{u}) :
    (legacyView object).edgeCount = object.edgeCount :=
  rfl

/-- The normalized Mathlib minimum degree agrees at the theorem root. -/
theorem legacyView_minDegree (object : Graph.FiniteObject.{u}) :
    (legacyView object).minDegree = object.minDegree :=
  rfl

/-- Paper-visible baseline parity: both implementations interpret the root
minimum-degree hypothesis as the same proposition `delta(G) >= 3`. -/
theorem baseline_iff (object : Graph.FiniteObject.{u}) :
    _root_.Erdos64EG.Internal.Baseline (legacyView object) ↔
      HypostructureErdos64EG.problem.Baseline object := by
  change 3 ≤ (legacyView object).minDegree ↔ 3 ≤ object.minDegree
  rw [legacyView_minDegree]

/-- Normalized node-1 parity, including the graph identity and the complete
minimum-degree baseline.  This deliberately says nothing about the
counterexample branch decided at node `[2]`. -/
theorem normalizedRootParity (object : Graph.FiniteObject.{u}) :
    (legacyView object).graph = object.graph ∧
      (legacyView object).input.vertices.card = object.vertexCount ∧
      (legacyView object).edgeCount = object.edgeCount ∧
      (legacyView object).minDegree = object.minDegree ∧
      (_root_.Erdos64EG.Internal.Baseline (legacyView object) ↔
        HypostructureErdos64EG.problem.Baseline object) := by
  exact ⟨rfl, rfl, rfl, rfl, baseline_iff object⟩

/-- The exact Hypostructure stage on the edge `[1] -> [2]` retains the same
normalized theorem-root graph and baseline; node `[1]` adds no premise. -/
theorem node1Edge_normalizedRootParity
    (root : HypostructureErdos64EG.InitialResidual.{u}) :
    let current := Core.Residual.residualOf
      (HypostructureErdos64EG.node1 root)
    (legacyView current.object).graph = root.object.graph ∧
      (legacyView current.object).input.vertices.card =
        root.object.vertexCount ∧
      (legacyView current.object).edgeCount = root.object.edgeCount ∧
      (legacyView current.object).minDegree = root.object.minDegree ∧
      (_root_.Erdos64EG.Internal.Baseline
          (legacyView current.object) ↔
        HypostructureErdos64EG.problem.Baseline root.object) := by
  change
    (legacyView root.object).graph = root.object.graph ∧
      (legacyView root.object).input.vertices.card =
        root.object.vertexCount ∧
      (legacyView root.object).edgeCount = root.object.edgeCount ∧
      (legacyView root.object).minDegree = root.object.minDegree ∧
      (_root_.Erdos64EG.Internal.Baseline
          (legacyView root.object) ↔
        HypostructureErdos64EG.problem.Baseline root.object)
  exact normalizedRootParity root.object

#print axioms baseline_iff
#print axioms normalizedRootParity
#print axioms node1Edge_normalizedRootParity

end HypostructureParity.Erdos64EG.Node1
