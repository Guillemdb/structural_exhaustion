import Hypostructure.Core.AffineBalance
import Hypostructure.Graph.Finite

/-!
# Finite graph one-three repair

This is the Graph-owned adapter for the standard one-three handshake.  The
boundary, degree hypotheses, and connectivity are contract inputs; vertex,
edge, and degree sums are derived from the literal finite graph.
-/

namespace Hypostructure.Graph.OneThreeRepair

open Hypostructure.Graph

universe u

structure Component where
  object : FiniteObject.{u}
  boundary : Finset object.Vertex
  boundaryDegree : ∀ vertex ∈ boundary, object.degree vertex = 1
  internalDegreeThree : ∀ vertex, vertex ∉ boundary → 3 ≤ object.degree vertex
  boundaryCard_le_edgeCount : boundary.card ≤ object.edgeCount
  connected : object.graph.Connected

namespace Component

variable (component : Component.{u})

noncomputable def internal : Finset component.object.Vertex :=
  by
    classical
    exact component.object.vertexFinset \ component.boundary

noncomputable def surplus : Nat :=
  ∑ vertex ∈ component.internal,
    (component.object.degree vertex - 3)

noncomputable def cycleRank : Nat :=
  component.object.edgeCount + 1 - component.object.vertexCount

noncomputable def internalEdgeCount : Nat :=
  component.object.edgeCount - component.boundary.card

theorem internal_disjoint_boundary :
    Disjoint component.internal component.boundary := by
  classical
  exact Finset.sdiff_disjoint

theorem sum_internal_degrees :
    ∑ vertex ∈ component.internal, component.object.degree vertex =
      3 * component.internal.card + component.surplus := by
  classical
  unfold surplus
  have degreeThree : ∀ vertex ∈ component.internal,
      3 ≤ component.object.degree vertex := by
    intro vertex member
    exact component.internalDegreeThree vertex
      (Finset.mem_sdiff.mp (show vertex ∈
        component.object.vertexFinset \ component.boundary by
          simpa [internal] using member)).2
  calc
    (∑ vertex ∈ component.internal, component.object.degree vertex) =
        ∑ vertex ∈ component.internal,
          (3 + (component.object.degree vertex - 3)) := by
      apply Finset.sum_congr rfl
      intro vertex member
      exact (Nat.add_sub_of_le (degreeThree vertex member)).symm
    _ = 3 * component.internal.card +
          ∑ vertex ∈ component.internal,
            (component.object.degree vertex - 3) := by
      rw [Finset.sum_add_distrib]
      simp [Nat.mul_comm]

theorem sum_boundary_degrees :
    ∑ vertex ∈ component.boundary, component.object.degree vertex =
      component.boundary.card := by
  classical
  calc
    (∑ vertex ∈ component.boundary, component.object.degree vertex) =
        ∑ _vertex ∈ component.boundary, 1 := by
      apply Finset.sum_congr rfl
      intro vertex member
      exact component.boundaryDegree vertex member
    _ = component.boundary.card := by simp

theorem handshake :
    3 * component.internal.card + component.surplus +
        component.boundary.card = 2 * component.object.edgeCount := by
  classical
  letI : FinEnum component.object.Vertex := component.object.vertices
  letI : DecidableRel component.object.graph.Adj := component.object.decideAdj
  have split :
      (∑ vertex ∈ component.object.vertexFinset,
        component.object.degree vertex) =
        (∑ vertex ∈ component.internal,
          component.object.degree vertex) +
          ∑ vertex ∈ component.boundary,
            component.object.degree vertex := by
    have reunited : component.internal ∪ component.boundary =
        component.object.vertexFinset := by
      ext vertex
      by_cases member : vertex ∈ component.boundary
      · simp [internal, member]
      · simp [internal, member]
    rw [← Finset.sum_union component.internal_disjoint_boundary, reunited]
  have degreeSum :
      (∑ vertex ∈ component.object.vertexFinset,
        component.object.degree vertex) =
        2 * component.object.edgeCount := by
    change (∑ vertex ∈ component.object.vertexFinset,
      component.object.degree vertex) =
      2 * component.object.graph.edgeFinset.card
    simpa [FiniteObject.vertexFinset, FiniteObject.degree,
      FiniteObject.edgeCount] using
      component.object.graph.sum_degrees_eq_twice_card_edges
  rw [split, component.sum_internal_degrees,
    component.sum_boundary_degrees] at degreeSum
  exact degreeSum

theorem vertexCard_eq :
    component.object.vertexCount =
      component.internal.card + component.boundary.card := by
  classical
  have reunited : component.internal ∪ component.boundary =
      component.object.vertexFinset :=
    by
      simpa [internal] using
        (Finset.sdiff_union_of_subset (s₁ := component.boundary)
          (s₂ := component.object.vertexFinset)
          (by
            intro vertex member
            exact component.object.mem_vertexFinset vertex))
  calc
    component.object.vertexCount = component.object.vertexFinset.card := by
      exact component.object.card_vertexFinset.symm
    _ = (component.internal ∪ component.boundary).card := by rw [reunited]
    _ = component.internal.card + component.boundary.card :=
      Finset.card_union_of_disjoint component.internal_disjoint_boundary

theorem internalEdgeCount_add_boundary :
    component.internalEdgeCount + component.boundary.card =
      component.object.edgeCount := by
  unfold internalEdgeCount
  have bound := component.boundaryCard_le_edgeCount
  omega

theorem cycleRank_cast :
    (component.cycleRank : Int) =
      component.object.edgeCount - component.object.vertexCount + 1 := by
  have connectedBound : component.object.vertexCount ≤
      component.object.edgeCount + 1 := by
    have raw := component.connected.card_vert_le_card_edgeSet_add_one
    calc
      component.object.vertexCount = Nat.card component.object.Vertex := by
        letI : Fintype component.object.Vertex :=
          @FinEnum.instFintype _ component.object.vertices
        rw [FiniteObject.vertexCount,
          @FinEnum.card_eq_fintypeCard _ component.object.vertices]
        exact Fintype.card_eq_nat_card
      _ ≤ component.object.graph.edgeSet.ncard + 1 := raw
      _ = component.object.edgeCount + 1 := by
        rw [component.object.edgeCount_eq_ncard_edgeSet]
  unfold cycleRank
  rw [Nat.cast_sub connectedBound]
  push_cast
  ring

theorem identity :
    (component.internal.card : Int) =
      component.boundary.card - 2 + 2 * component.cycleRank -
        component.surplus := by
  apply Hypostructure.Core.AffineBalance.solve_one_three
      (internal := component.internal.card)
      (boundary := component.boundary.card)
      (total := component.object.edgeCount)
      (rank := component.cycleRank)
      (surplus := component.surplus)
  · have handshake := component.handshake
    exact_mod_cast handshake
  · rw [component.cycleRank_cast, component.vertexCard_eq]
    push_cast
    ring

end Component

end Hypostructure.Graph.OneThreeRepair
