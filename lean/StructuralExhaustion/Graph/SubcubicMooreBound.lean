import Mathlib.Tactic
import StructuralExhaustion.Graph.OrderedBFSTree

namespace StructuralExhaustion.Graph.OrderedBFSTree.Profile

open StructuralExhaustion
open scoped BigOperators

universe u

variable {V : Type u} {object : FiniteObject V}

variable (profile : OrderedBFSTree.Profile object)

noncomputable section

noncomputable def neighbors (parent : V) : Finset V := by
  letI : DecidableRel object.graph.Adj := object.input.decideAdj
  exact object.vertexFinset.filter fun vertex => object.graph.Adj parent vertex

noncomputable def nextNeighbors (steps : Nat) (parent : V) : Finset V := by
  letI : DecidableEq V := object.input.vertices.decEq
  exact neighbors (object := object) parent ∩ profile.layer (steps + 1)

noncomputable def nextCover (steps : Nat) : Finset V := by
  letI : DecidableEq V := object.input.vertices.decEq
  exact (profile.layer steps).biUnion (profile.nextNeighbors steps)

theorem layer_succ_subset_biUnion_nextNeighbors (steps : Nat) :
    profile.layer (steps + 1) ⊆ profile.nextCover steps := by
  letI : DecidableEq V := object.input.vertices.decEq
  letI : DecidableRel object.graph.Adj := object.input.decideAdj
  intro vertex member
  obtain ⟨_unseen, parent, parentMem, adjacent⟩ :=
    (profile.mem_layer_succ_iff steps vertex).mp member
  apply Finset.mem_biUnion.mpr
  refine ⟨parent, parentMem, ?_⟩
  simp [nextCover, nextNeighbors, neighbors, adjacent, member,
    object.mem_vertexFinset]

theorem card_nextNeighbors_zero_le_three
    (parent : V) (parentMem : parent ∈ profile.layer 0)
    (degreeLe : ∀ vertex, object.degree vertex ≤ 3) :
    (profile.nextNeighbors 0 parent).card ≤ 3 := by
  letI : DecidableEq V := object.input.vertices.decEq
  letI : DecidableRel object.graph.Adj := object.input.decideAdj
  exact (object.card_le_degree_of_adjacent_finset parent
    (profile.nextNeighbors 0 parent) (by
      intro vertex member
      have neighbor := (Finset.mem_inter.mp member).1
      simpa [neighbors] using (Finset.mem_filter.mp neighbor).2)).trans
        (degreeLe parent)

theorem card_layer_one_le_three
    (degreeLe : ∀ vertex, object.degree vertex ≤ 3) :
    (profile.layer 1).card ≤ 3 := by
  letI : DecidableEq V := object.input.vertices.decEq
  calc
    (profile.layer 1).card ≤
        (profile.nextCover 0).card :=
      Finset.card_le_card (profile.layer_succ_subset_biUnion_nextNeighbors 0)
    _ ≤ ∑ parent ∈ profile.layer 0,
        (profile.nextNeighbors 0 parent).card := by
      unfold nextCover
      exact Finset.card_biUnion_le
    _ ≤ ∑ _parent ∈ profile.layer 0, 3 := by
      exact Finset.sum_le_sum fun parent member =>
        profile.card_nextNeighbors_zero_le_three parent member degreeLe
    _ = 3 := by simp

theorem card_nextNeighbors_succ_le_two
    (degreeLe : ∀ vertex, object.degree vertex ≤ 3)
    (steps : Nat) (parent : V) (parentMem : parent ∈ profile.layer (steps + 1)) :
    (profile.nextNeighbors (steps + 1) parent).card ≤ 2 := by
  letI : DecidableEq V := object.input.vertices.decEq
  letI : DecidableRel object.graph.Adj := object.input.decideAdj
  obtain ⟨_unseen, back, backMem, backAdjacent⟩ :=
    (profile.mem_layer_succ_iff steps parent).mp parentMem
  have backDiscovered : back ∈ profile.discovered (steps + 1) :=
    profile.layer_subset_discovered steps backMem |>
      Finset.mem_of_subset (profile.discovered_mono_step steps)
  have backNotNext : back ∉ profile.layer (steps + 2) := by
    intro member
    exact ((profile.mem_layer_succ_iff (steps + 1) back).mp member).1 backDiscovered
  have subset : profile.nextNeighbors (steps + 1) parent ⊆
      (neighbors (object := object) parent).erase back := by
    intro vertex member
    have neighbor := (Finset.mem_inter.mp member).1
    have nextMem := (Finset.mem_inter.mp member).2
    apply Finset.mem_erase.mpr
    refine ⟨?_, neighbor⟩
    intro equal
    subst vertex
    exact backNotNext nextMem
  have backNeighbor' : back ∈ neighbors (object := object) parent := by
    simp [neighbors, object.mem_vertexFinset, backAdjacent.symm]
  have neighborCardLe : (neighbors (object := object) parent).card ≤
      object.degree parent :=
    object.card_le_degree_of_adjacent_finset parent
      (neighbors (object := object) parent) (by
        intro vertex member
        simpa [neighbors] using (Finset.mem_filter.mp member).2)
  have eraseEq : ((neighbors (object := object) parent).erase back).card + 1 =
      (neighbors (object := object) parent).card := by
    rw [Finset.card_erase_of_mem backNeighbor']
    have positive : 0 < (neighbors (object := object) parent).card :=
      Finset.card_pos.mpr ⟨back, backNeighbor'⟩
    omega
  have erasedLe : ((neighbors (object := object) parent).erase back).card ≤ 2 := by
    have degree := degreeLe parent
    omega
  exact (Finset.card_le_card subset).trans erasedLe

theorem card_layer_succ_succ_le_twice
    (degreeLe : ∀ vertex, object.degree vertex ≤ 3) (steps : Nat) :
    (profile.layer (steps + 2)).card ≤ 2 * (profile.layer (steps + 1)).card := by
  letI : DecidableEq V := object.input.vertices.decEq
  calc
    (profile.layer (steps + 2)).card ≤
        (profile.nextCover (steps + 1)).card :=
      Finset.card_le_card
        (profile.layer_succ_subset_biUnion_nextNeighbors (steps + 1))
    _ ≤ ∑ parent ∈ profile.layer (steps + 1),
        (profile.nextNeighbors (steps + 1) parent).card := by
      unfold nextCover
      exact Finset.card_biUnion_le
    _ ≤ ∑ _parent ∈ profile.layer (steps + 1), 2 := by
      exact Finset.sum_le_sum fun parent member =>
        profile.card_nextNeighbors_succ_le_two degreeLe steps parent member
    _ = 2 * (profile.layer (steps + 1)).card := by simp [Nat.mul_comm]

theorem card_discovered_succ_le (steps : Nat) :
    (profile.discovered (steps + 1)).card ≤
      (profile.discovered steps).card + (profile.layer (steps + 1)).card := by
  classical
  rw [show profile.discovered (steps + 1) =
      profile.discovered steps ∪ profile.layer (steps + 1) by
    ext vertex
    simp only [Finset.mem_union]
    exact profile.mem_discovered_succ_iff steps vertex]
  exact Finset.card_union_le _ _

/-- The paper's exact subcubic radius-eleven Moore count. -/
theorem card_vertices_le_6142_of_radius_eleven
    (preconnected : object.graph.Preconnected)
    (degreeLe : ∀ vertex, object.degree vertex ≤ 3)
    (radius : ∀ vertex : V,
      ∃ path : object.graph.Walk profile.root vertex,
        path.IsPath ∧ path.length ≤ 11) :
    object.input.vertices.card ≤ 6142 := by
  have allDiscovered : object.vertexFinset ⊆ profile.discovered 11 := by
    intro vertex _member
    obtain ⟨path, _isPath, lengthLe⟩ := radius vertex
    exact (profile.discovered_iff_bounded_walk 11 vertex).mpr ⟨path, lengthLe⟩
  have vertexCardLe : object.input.vertices.card ≤
      (profile.discovered 11).card := by
    rw [← object.card_vertexFinset]
    exact Finset.card_le_card allDiscovered
  have l1 := profile.card_layer_one_le_three degreeLe
  have l2 := profile.card_layer_succ_succ_le_twice degreeLe 0
  have l3 := profile.card_layer_succ_succ_le_twice degreeLe 1
  have l4 := profile.card_layer_succ_succ_le_twice degreeLe 2
  have l5 := profile.card_layer_succ_succ_le_twice degreeLe 3
  have l6 := profile.card_layer_succ_succ_le_twice degreeLe 4
  have l7 := profile.card_layer_succ_succ_le_twice degreeLe 5
  have l8 := profile.card_layer_succ_succ_le_twice degreeLe 6
  have l9 := profile.card_layer_succ_succ_le_twice degreeLe 7
  have l10 := profile.card_layer_succ_succ_le_twice degreeLe 8
  have l11 := profile.card_layer_succ_succ_le_twice degreeLe 9
  have d0 : (profile.discovered 0).card = 1 := by simp
  have d1 := profile.card_discovered_succ_le 0
  have d2 := profile.card_discovered_succ_le 1
  have d3 := profile.card_discovered_succ_le 2
  have d4 := profile.card_discovered_succ_le 3
  have d5 := profile.card_discovered_succ_le 4
  have d6 := profile.card_discovered_succ_le 5
  have d7 := profile.card_discovered_succ_le 6
  have d8 := profile.card_discovered_succ_le 7
  have d9 := profile.card_discovered_succ_le 8
  have d10 := profile.card_discovered_succ_le 9
  have d11 := profile.card_discovered_succ_le 10
  norm_num at l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11
  omega

end

end StructuralExhaustion.Graph.OrderedBFSTree.Profile
