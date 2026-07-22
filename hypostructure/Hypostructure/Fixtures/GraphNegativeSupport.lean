import Hypostructure.Fixtures.GraphBasics
import Hypostructure.Graph.NegativeSupport
import Hypostructure.Graph.SupportComponents

/-!
# Negative-support Graph fixture

This fixture exercises the parameterized support contract on a concrete finite
graph without supplying a branch result or a route.
-/

namespace Hypostructure.Fixtures.GraphNegativeSupport

open Hypostructure.Graph
open Hypostructure.Fixtures.GraphBasics
open Hypostructure.Core.Finite

open Hypostructure.Graph.SupportComponents.Connected

def singleton : NegativeSupport.Support GraphBasics.k4 where
  source := {
    core := {0}
    cells := Enumeration.singleton 0
    cells_toFinset := by
      ext value
      simp [Enumeration.singleton, Enumeration.ofNodupList, Enumeration.toFinset]
    charge := fun _ => -1
    negative := by
      norm_num [Enumeration.singleton, Enumeration.ofNodupList] }
  connected := by
    change ConnectedOn GraphBasics.k4 ({0} : Finset GraphBasics.k4.Vertex)
    refine ⟨⟨0, by simp⟩, ?_⟩
    intro left right leftMem rightMem
    have leftEq : left = 0 := by simpa using leftMem
    have rightEq : right = 0 := by simpa using rightMem
    subst left
    subst right
    exact ⟨SimpleGraph.Walk.nil, by simp, by
      intro vertex vertexMem
      rw [SimpleGraph.Walk.mem_support_nil_iff] at vertexMem
      simpa using vertexMem⟩

theorem singleton_noHigh : singleton.HasNoHigh 4 := by
  unfold NegativeSupport.Support.HasNoHigh NegativeSupport.Support.highCenters
  change ({0} : Finset GraphBasics.k4.Vertex).filter
      (fun vertex => 4 ≤ GraphBasics.k4.degree vertex) = ∅
  ext vertex
  simp [GraphBasics.k4_degree]

theorem singleton_high : singleton.HasHigh 3 := by
  unfold NegativeSupport.Support.HasHigh NegativeSupport.Support.highCenters
  change (({0} : Finset GraphBasics.k4.Vertex).filter
      (fun vertex => 3 ≤ GraphBasics.k4.degree vertex)).Nonempty
  refine ⟨0, ?_⟩
  simp [GraphBasics.k4_degree]

theorem singleton_noHigh_degree :
    ∀ vertex ∈ singleton.core, GraphBasics.k4.degree vertex = 3 := by
  intro vertex member
  have minimum : 3 ≤ GraphBasics.k4.minDegree :=
    GraphBasics.k4.le_minDegree_of_forall_le_degree 3 (by
      intro value
      rw [GraphBasics.k4_degree value]
      )
  exact singleton.ambientDegree_eq_of_noHigh 3 4 rfl minimum
    singleton_noHigh vertex member

def singletonComponent : Component GraphBasics.k4 ({0} : Finset GraphBasics.k4.Vertex) :=
  componentOf GraphBasics.k4 {0} ⟨0, by simp⟩

theorem singletonComponent_mem_order :
    singletonComponent ∈ order GraphBasics.k4 ({0} : Finset GraphBasics.k4.Vertex) := by
  rw [order, Hypostructure.Core.Finite.OrderedPartition.labels_complete]
  exact ⟨⟨0, by simp⟩,
    FiniteObject.mem_orderedVertices (GraphBasics.k4.induce {0}) _, rfl⟩

theorem singletonComponent_connected :
    ConnectedOn GraphBasics.k4
      (members GraphBasics.k4 ({0} : Finset GraphBasics.k4.Vertex)
        singletonComponent) :=
  connectedOn_of_mem_order GraphBasics.k4 {0} singletonComponent_mem_order

#print axioms singleton_noHigh
#print axioms singleton_high
#print axioms singleton_noHigh_degree

end Hypostructure.Fixtures.GraphNegativeSupport
