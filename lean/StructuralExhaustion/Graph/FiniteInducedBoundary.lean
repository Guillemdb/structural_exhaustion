import Mathlib.Tactic
import StructuralExhaustion.Graph.FiniteObject

namespace StructuralExhaustion.Graph.FiniteInducedBoundary

universe u

/-!
# Literal boundary of a finite induced deletion

This module turns a positive loss of induced degree into an actual graph edge
crossing from the retained set to the processed set.  All sets are supplied as
finite graph data.  The proof compares two neighbour finsets; it does not
enumerate subsets or paths.
-/

variable {V : Type u}

structure Profile (object : Graph.FiniteObject V) where
  whole : Finset V
  processed : Finset V
  processed_subset_whole : processed ⊆ whole

namespace Profile

variable {object : Graph.FiniteObject V} (profile : Profile object)

noncomputable def remaining : Finset V := by
  letI : DecidableEq V := object.input.vertices.decEq
  exact profile.whole \ profile.processed

noncomputable def wholeNeighborCount (vertex : V) : Nat := by
  letI : FinEnum V := object.input.vertices
  letI : DecidableEq V := object.input.vertices.decEq
  letI : DecidableRel object.graph.Adj := object.input.decideAdj
  exact (object.graph.neighborFinset vertex ∩ profile.whole).card

noncomputable def remainingNeighborCount (vertex : V) : Nat := by
  letI : FinEnum V := object.input.vertices
  letI : DecidableEq V := object.input.vertices.decEq
  letI : DecidableRel object.graph.Adj := object.input.decideAdj
  exact (object.graph.neighborFinset vertex ∩ profile.remaining).card

noncomputable def loss (vertex : V) : Nat :=
  profile.wholeNeighborCount vertex - profile.remainingNeighborCount vertex

noncomputable def processedNeighborCount (vertex : V) : Nat := by
  letI : FinEnum V := object.input.vertices
  letI : DecidableEq V := object.input.vertices.decEq
  letI : DecidableRel object.graph.Adj := object.input.decideAdj
  exact (object.graph.neighborFinset vertex ∩ profile.processed).card

noncomputable def totalLoss : Nat := by
  letI : DecidableEq V := object.input.vertices.decEq
  exact ∑ vertex ∈ profile.remaining, profile.loss vertex

/-- An actual adjacency crossing the induced deletion boundary. -/
structure Incidence : Type u where
  retained : V
  retained_mem : retained ∈ profile.remaining
  deleted : V
  deleted_mem : deleted ∈ profile.processed
  adjacent : object.graph.Adj retained deleted

theorem remainingNeighborCount_le_wholeNeighborCount (vertex : V) :
    profile.remainingNeighborCount vertex ≤
      profile.wholeNeighborCount vertex := by
  letI : FinEnum V := object.input.vertices
  letI : DecidableEq V := object.input.vertices.decEq
  letI : DecidableRel object.graph.Adj := object.input.decideAdj
  unfold remainingNeighborCount wholeNeighborCount
  apply Finset.card_le_card
  intro neighbor member
  rw [Finset.mem_inter] at member ⊢
  exact ⟨member.1, (Finset.mem_sdiff.mp member.2).1⟩

theorem loss_eq_processedNeighborCount
    (vertex : V) (_retained : vertex ∈ profile.remaining) :
    profile.loss vertex = profile.processedNeighborCount vertex := by
  letI : FinEnum V := object.input.vertices
  letI : DecidableEq V := object.input.vertices.decEq
  letI : DecidableRel object.graph.Adj := object.input.decideAdj
  let remainingNeighbors := object.graph.neighborFinset vertex ∩ profile.remaining
  let processedNeighbors := object.graph.neighborFinset vertex ∩ profile.processed
  have disjoint : Disjoint remainingNeighbors processedNeighbors := by
    rw [Finset.disjoint_left]
    intro neighbor remainingMember processedMember
    have remainingPart := Finset.mem_inter.mp remainingMember |>.2
    exact (Finset.mem_sdiff.mp remainingPart).2
      (Finset.mem_inter.mp processedMember).2
  have partition :
      object.graph.neighborFinset vertex ∩ profile.whole =
        remainingNeighbors ∪ processedNeighbors := by
    ext neighbor
    constructor
    · intro member
      have parts := Finset.mem_inter.mp member
      by_cases deleted : neighbor ∈ profile.processed
      · exact Finset.mem_union_right _
          (Finset.mem_inter.mpr ⟨parts.1, deleted⟩)
      · exact Finset.mem_union_left _
          (Finset.mem_inter.mpr
            ⟨parts.1, Finset.mem_sdiff.mpr ⟨parts.2, deleted⟩⟩)
    · intro member
      rcases Finset.mem_union.mp member with remainingMember | processedMember
      · have parts := Finset.mem_inter.mp remainingMember
        exact Finset.mem_inter.mpr
          ⟨parts.1, (Finset.mem_sdiff.mp parts.2).1⟩
      · have parts := Finset.mem_inter.mp processedMember
        exact Finset.mem_inter.mpr
          ⟨parts.1, profile.processed_subset_whole parts.2⟩
  unfold loss wholeNeighborCount remainingNeighborCount processedNeighborCount
  rw [partition]
  change (remainingNeighbors ∪ processedNeighbors).card -
      remainingNeighbors.card = processedNeighbors.card
  rw [Finset.card_union_of_disjoint disjoint]
  exact Nat.add_sub_cancel_left _ _

/-- The total lost induced degree is at most the ambient degree sum of the
processed side.  This is the finite handshake bound for the cut. -/
theorem totalLoss_le_processedDegreeSum :
    profile.totalLoss ≤
      ∑ vertex ∈ profile.processed, object.degree vertex := by
  letI : FinEnum V := object.input.vertices
  letI : DecidableEq V := object.input.vertices.decEq
  letI : DecidableRel object.graph.Adj := object.input.decideAdj
  unfold totalLoss
  rw [show (∑ vertex ∈ profile.remaining, profile.loss vertex) =
      ∑ vertex ∈ profile.remaining,
        profile.processedNeighborCount vertex by
    apply Finset.sum_congr rfl
    intro vertex member
    exact profile.loss_eq_processedNeighborCount vertex member]
  unfold processedNeighborCount
  have countEq : ∀ retained,
      (object.graph.neighborFinset retained ∩ profile.processed).card =
        ∑ processed ∈ profile.processed,
          if object.graph.Adj retained processed then 1 else 0 := by
    intro retained
    rw [Finset.sum_boole]
    apply congrArg Finset.card
    ext processed
    simp [SimpleGraph.mem_neighborFinset, and_comm]
  simp_rw [countEq]
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro processed processedMem
  have neighborBound :
      (object.graph.neighborFinset processed ∩ profile.remaining).card ≤
        object.degree processed := by
    exact (Finset.card_le_card Finset.inter_subset_left).trans_eq rfl
  have countEq' :
      (∑ retained ∈ profile.remaining,
        if object.graph.Adj retained processed then 1 else 0) =
          (object.graph.neighborFinset processed ∩ profile.remaining).card := by
    rw [Finset.sum_boole]
    apply congrArg Finset.card
    ext retained
    simp [SimpleGraph.mem_neighborFinset, SimpleGraph.adj_comm, and_comm]
  rw [countEq']
  exact neighborBound

/-- Positive degree loss at a retained vertex yields a literal adjacent
processed vertex. -/
theorem exists_incidence_of_loss_pos
    (vertex : V) (retained : vertex ∈ profile.remaining)
    (positive : 0 < profile.loss vertex) :
    Nonempty profile.Incidence := by
  letI : FinEnum V := object.input.vertices
  letI : DecidableEq V := object.input.vertices.decEq
  letI : DecidableRel object.graph.Adj := object.input.decideAdj
  let wholeNeighbors := object.graph.neighborFinset vertex ∩ profile.whole
  let remainingNeighbors :=
    object.graph.neighborFinset vertex ∩ profile.remaining
  have subset : remainingNeighbors ⊆ wholeNeighbors := by
    intro neighbor member
    rw [Finset.mem_inter] at member ⊢
    exact ⟨member.1, (Finset.mem_sdiff.mp member.2).1⟩
  have cardLt : remainingNeighbors.card < wholeNeighbors.card := by
    unfold loss wholeNeighborCount remainingNeighborCount at positive
    change 0 < wholeNeighbors.card - remainingNeighbors.card at positive
    have le := Finset.card_le_card subset
    omega
  have notSubset : ¬wholeNeighbors ⊆ remainingNeighbors := by
    intro reverse
    have reverseCard := Finset.card_le_card reverse
    omega
  have setNotSubset :
      ¬(↑wholeNeighbors : Set V) ⊆ (↑remainingNeighbors : Set V) := by
    simpa using notSubset
  rcases Set.not_subset.mp setNotSubset with
    ⟨deleted, wholeMember, notRemainingMember⟩
  have wholeParts := Finset.mem_inter.mp wholeMember
  have deletedMem : deleted ∈ profile.processed := by
    by_contra notDeleted
    apply notRemainingMember
    exact Finset.mem_inter.mpr
      ⟨wholeParts.1, Finset.mem_sdiff.mpr ⟨wholeParts.2, notDeleted⟩⟩
  have adjacent : object.graph.Adj vertex deleted := by
    simpa using wholeParts.1
  exact ⟨⟨vertex, retained, deleted, deletedMem, adjacent⟩⟩

end Profile

end StructuralExhaustion.Graph.FiniteInducedBoundary
