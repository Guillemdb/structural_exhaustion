import EvenCycleExample.Concrete
import StructuralExhaustion.Graph.HighCenterDeletionCharge

namespace EvenCycleExample.ConcreteK34

open StructuralExhaustion

/-!
# Independent high-center deletion charge

The textbook complete bipartite graph `K₃,₄` gives a closed non-Erdős
instance of the graph-owned high-center deletion theorem.  Its three left
vertices have degree four, its four right vertices have degree three, and
deleting all left vertices leaves an edgeless graph.  Thus the receiver
continuation is proved directly, without the Hegde--Sandeep--Shashank theorem.
-/

def leftCenters : Finset Vertex :=
  (Finset.univ : Finset (Fin 3)).image fun vertex =>
    (Sum.inl vertex : Vertex)

def highCenterChargeProfile :
    Graph.AssignedSupportCharge.Profile object where
  core := Finset.univ
  assignedCenters := leftCenters

theorem leftDegree_exact (vertex : Fin 3) :
    object.degree (Sum.inl vertex) = 4 := by
  rw [object.degree_eq_ncard_neighborSet]
  have neighborSetEq :
      object.graph.neighborSet (Sum.inl vertex) =
        Set.range (fun right : Fin 4 => (Sum.inr right : Vertex)) := by
    ext other
    rcases other with left | right
    · simp [object, graph, completeBipartiteGraph]
    · simp [object, graph, completeBipartiteGraph]
  rw [neighborSetEq]
  calc
    (Set.range (fun right : Fin 4 => (Sum.inr right : Vertex))).ncard =
        Nat.card (Fin 4) :=
      Set.ncard_range_of_injective (by
        intro left right equal
        exact Sum.inr_injective equal)
    _ = 4 := by simp

theorem rightDegree_exact (vertex : Fin 4) :
    object.degree (Sum.inr vertex) = 3 := by
  rw [object.degree_eq_ncard_neighborSet]
  have neighborSetEq :
      object.graph.neighborSet (Sum.inr vertex) =
        Set.range (fun left : Fin 3 => (Sum.inl left : Vertex)) := by
    ext other
    rcases other with left | right
    · simp [object, graph, completeBipartiteGraph]
    · simp [object, graph, completeBipartiteGraph]
  rw [neighborSetEq]
  calc
    (Set.range (fun left : Fin 3 => (Sum.inl left : Vertex))).ncard =
        Nat.card (Fin 3) :=
      Set.ncard_range_of_injective (by
        intro left right equal
        exact Sum.inl_injective equal)
    _ = 3 := by simp

theorem leftCenters_subset_core :
    highCenterChargeProfile.assignedCenters ⊆
      highCenterChargeProfile.core := by
  intro vertex _member
  simp [highCenterChargeProfile]

theorem leftCenter_degree_at_least_four
    (center : Vertex) (member : center ∈ leftCenters) :
    4 ≤ object.degree center := by
  rcases Finset.mem_image.mp member with ⟨left, _leftMem, rfl⟩
  rw [leftDegree_exact]

theorem nonleft_core_vertex_degree_eq_three
    (vertex : Vertex) (_core : vertex ∈ highCenterChargeProfile.core)
    (notCenter : vertex ∉ highCenterChargeProfile.assignedCenters) :
    object.degree vertex = 3 := by
  rcases vertex with left | right
  · exact False.elim (notCenter (by simp [highCenterChargeProfile, leftCenters]))
  · exact rightDegree_exact right

def highCenterDeletionProfile :
    Graph.HighCenterDeletionCharge.Profile object where
  charge := highCenterChargeProfile
  centers_subset_core := leftCenters_subset_core
  center_high := leftCenter_degree_at_least_four
  noncenter_degree_eq_three := nonleft_core_vertex_degree_eq_three

theorem remainingCore_eq_rightVertices :
    highCenterDeletionProfile.remainingCore =
      (Finset.univ : Finset (Fin 4)).image fun vertex =>
        (Sum.inr vertex : Vertex) := by
  classical
  ext vertex
  rcases vertex with left | right
  · simp [Graph.HighCenterDeletionCharge.Profile.remainingCore,
      highCenterDeletionProfile, highCenterChargeProfile, leftCenters]
  · simp [Graph.HighCenterDeletionCharge.Profile.remainingCore,
      highCenterDeletionProfile, highCenterChargeProfile, leftCenters]

theorem remainingObject_graph_eq_bot :
    highCenterDeletionProfile.remainingObject.graph = ⊥ := by
  ext left right
  rcases left with ⟨left, leftMem⟩
  rcases right with ⟨right, rightMem⟩
  rw [remainingCore_eq_rightVertices] at leftMem rightMem
  rcases Finset.mem_image.mp leftMem with ⟨leftIndex, _leftIndexMem, rfl⟩
  rcases Finset.mem_image.mp rightMem with ⟨rightIndex, _rightIndexMem, rfl⟩
  change graph.Adj (Sum.inr leftIndex) (Sum.inr rightIndex) ↔ False
  simp [graph, completeBipartiteGraph]

theorem remainingObject_internalThreeCore_free :
    highCenterDeletionProfile.remainingObject.InternalMinDegreeFree 3 := by
  rintro ⟨support, minimumDegree⟩
  have inducedGraphBot :
      (highCenterDeletionProfile.remainingObject.induceFinset support).graph =
        ⊥ := by
    ext left right
    change highCenterDeletionProfile.remainingObject.graph.Adj
      left.1 right.1 ↔ False
    rw [remainingObject_graph_eq_bot]
    simp
  let induced := highCenterDeletionProfile.remainingObject.induceFinset support
  have positive : 0 < induced.minDegree := by
    change 0 <
      (highCenterDeletionProfile.remainingObject.induceFinset support).minDegree
    omega
  let vertex := Classical.choice (induced.nonempty_of_minDegree_pos positive)
  have minimumLeDegree := induced.minDegree_le_degree vertex
  have neighborSetEmpty : induced.graph.neighborSet vertex = ∅ := by
    change
      (highCenterDeletionProfile.remainingObject.induceFinset support).graph.neighborSet
          vertex = ∅
    rw [inducedGraphBot]
    simp
  have degreeZero : induced.degree vertex = 0 := by
    rw [induced.degree_eq_ncard_neighborSet, neighborSetEmpty]
    simp
  omega

/-- The exact reusable theorem, instantiated independently of every Erdős
definition and of the sole external theorem. -/
theorem highCenterDeletion_deficit_bound :
    -highCenterDeletionProfile.charge.netQuarterCharge ≤
      21 * (highCenterDeletionProfile.charge.assignedSurplus : Int) +
        (highCenterDeletionProfile.receiverOverload
          remainingObject_internalThreeCore_free : Int) :=
  highCenterDeletionProfile.neg_netQuarterCharge_le_twentyOne_mul_surplus_add_overload
    remainingObject_internalThreeCore_free

end EvenCycleExample.ConcreteK34
