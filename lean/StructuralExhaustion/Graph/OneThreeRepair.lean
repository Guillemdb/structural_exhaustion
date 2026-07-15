import StructuralExhaustion.Graph.FiniteObject
import StructuralExhaustion.Core.OneThreeRepair
import Mathlib.Combinatorics.SimpleGraph.Acyclic

namespace StructuralExhaustion.Graph.OneThreeRepair

open StructuralExhaustion
open scoped BigOperators

universe u

/-! # Finite one--three repair components -/

noncomputable def edgeCount {V : Type u} (object : FiniteObject V) : Nat := by
  letI : FinEnum V := object.input.vertices
  letI : Fintype V := @FinEnum.instFintype V object.input.vertices
  letI : DecidableEq V := object.input.vertices.decEq
  letI : DecidableRel object.graph.Adj := object.input.decideAdj
  exact object.graph.edgeFinset.card

/-- A literal connected finite graph whose declared boundary vertices are
leaves and whose remaining vertices have degree at least three. -/
structure Component (V : Type u) where
  object : FiniteObject V
  boundary : Finset V
  boundaryDegree : ∀ v ∈ boundary, object.degree v = 1
  internalDegreeThree : ∀ v, v ∉ boundary → 3 ≤ object.degree v
  boundaryCard_le_edgeCount : boundary.card ≤ edgeCount object
  connected : object.graph.Connected

namespace Component

variable {V : Type u} (component : Component V)

noncomputable def internal : Finset V :=
  by
    classical
    exact component.object.vertexFinset \ component.boundary

noncomputable def surplus : Nat :=
  ∑ v ∈ component.internal, (component.object.degree v - 3)

noncomputable def edgeCount : Nat := by
  exact OneThreeRepair.edgeCount component.object

noncomputable def cycleRank : Nat :=
  component.edgeCount + 1 -
    component.object.input.vertices.card

noncomputable def internalEdgeCount : Nat :=
  component.edgeCount - component.boundary.card

theorem boundary_subset :
    component.boundary ⊆ component.object.vertexFinset := by
  intro vertex _member
  simp [FiniteObject.vertexFinset]

theorem internal_disjoint_boundary :
    Disjoint component.internal component.boundary := by
  classical
  exact Finset.sdiff_disjoint

theorem sum_internal_degrees :
    ∑ v ∈ component.internal, component.object.degree v =
      3 * component.internal.card + component.surplus := by
  classical
  unfold surplus
  have degreeThree : ∀ v ∈ component.internal,
      3 ≤ component.object.degree v := by
    intro vertex member
    exact component.internalDegreeThree vertex (Finset.mem_sdiff.mp member).2
  calc
    ∑ v ∈ component.internal, component.object.degree v =
        ∑ v ∈ component.internal, (3 + (component.object.degree v - 3)) := by
      apply Finset.sum_congr rfl
      intro vertex member
      exact (Nat.add_sub_of_le (degreeThree vertex member)).symm
    _ = 3 * component.internal.card + component.surplus := by
      rw [Finset.sum_add_distrib]
      simp [Nat.mul_comm, surplus]

theorem sum_boundary_degrees :
    ∑ v ∈ component.boundary, component.object.degree v =
      component.boundary.card := by
  classical
  calc
    ∑ v ∈ component.boundary, component.object.degree v =
        ∑ _v ∈ component.boundary, 1 := by
      apply Finset.sum_congr rfl
      intro vertex member
      exact component.boundaryDegree vertex member
    _ = component.boundary.card := by simp

theorem handshake :
    3 * component.internal.card + component.surplus +
        component.boundary.card =
      2 * component.edgeCount := by
  classical
  letI : FinEnum V := component.object.input.vertices
  letI : Fintype V := @FinEnum.instFintype V component.object.input.vertices
  letI : DecidableEq V := component.object.input.vertices.decEq
  letI : DecidableRel component.object.graph.Adj :=
    component.object.input.decideAdj
  have split :
      (∑ v ∈ component.object.vertexFinset, component.object.degree v) =
        (∑ v ∈ component.internal, component.object.degree v) +
          ∑ v ∈ component.boundary, component.object.degree v := by
    have reunited : component.internal ∪ component.boundary =
        component.object.vertexFinset :=
      by
        ext vertex
        by_cases member : vertex ∈ component.boundary
        · simp [internal, member]
        · simp [internal, member]
    rw [← Finset.sum_union component.internal_disjoint_boundary, reunited]
  have degreeSum :
      (∑ v ∈ component.object.vertexFinset, component.object.degree v) =
        2 * component.edgeCount := by
    change (∑ v ∈ component.object.vertexFinset,
      component.object.degree v) =
        2 * component.object.graph.edgeFinset.card
    simpa [FiniteObject.vertexFinset, FiniteObject.degree] using
      component.object.graph.sum_degrees_eq_twice_card_edges
  rw [split, component.sum_internal_degrees,
    component.sum_boundary_degrees] at degreeSum
  exact degreeSum

theorem vertexCard_eq :
    component.object.input.vertices.card =
      component.internal.card + component.boundary.card := by
  classical
  have reunited : component.internal ∪ component.boundary =
      component.object.vertexFinset :=
    Finset.sdiff_union_of_subset component.boundary_subset
  calc
    component.object.input.vertices.card =
        component.object.vertexFinset.card := component.object.card_vertexFinset.symm
    _ = (component.internal ∪ component.boundary).card := by rw [reunited]
    _ = component.internal.card + component.boundary.card :=
      Finset.card_union_of_disjoint component.internal_disjoint_boundary

theorem boundary_card_le_edgeCount :
    component.boundary.card ≤ component.edgeCount := by
  unfold Component.edgeCount
  exact component.boundaryCard_le_edgeCount

theorem internalEdgeCount_add_boundary :
    component.internalEdgeCount + component.boundary.card =
      component.edgeCount := by
  unfold internalEdgeCount
  have bound := component.boundary_card_le_edgeCount
  omega

theorem cycleRank_cast :
    (component.cycleRank : Int) =
      component.edgeCount -
        component.object.input.vertices.card + 1 := by
  letI : FinEnum V := component.object.input.vertices
  letI : Fintype V := @FinEnum.instFintype V component.object.input.vertices
  letI : DecidableEq V := component.object.input.vertices.decEq
  letI : DecidableRel component.object.graph.Adj :=
    component.object.input.decideAdj
  have connectedBound : component.object.input.vertices.card ≤
      component.edgeCount + 1 := by
    have bound := component.connected.card_vert_le_card_edgeSet_add_one
    simpa [Nat.card_eq_fintype_card, FinEnum.card_eq_fintypeCard,
      SimpleGraph.edgeFinset_card, Component.edgeCount,
      OneThreeRepair.edgeCount] using bound
  unfold cycleRank
  rw [Nat.cast_sub connectedBound]
  push_cast
  ring

/-- Graph-level node-[44] theorem with all counts computed from the supplied
finite component. -/
theorem identity :
    (component.internal.card : Int) =
      component.boundary.card - 2 + 2 * component.cycleRank -
        component.surplus := by
  apply Core.OneThreeRepair.identity
      component.internal.card component.boundary.card
      component.internalEdgeCount component.cycleRank
      component.surplus
  · have handshake := component.handshake
    rw [← component.internalEdgeCount_add_boundary] at handshake
    exact_mod_cast handshake
  · rw [component.cycleRank_cast, component.vertexCard_eq]
    have edgeSplit := component.internalEdgeCount_add_boundary
    rw [← edgeSplit]
    push_cast
    ring

end Component

end StructuralExhaustion.Graph.OneThreeRepair
