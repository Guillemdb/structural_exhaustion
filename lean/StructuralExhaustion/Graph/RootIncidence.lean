import StructuralExhaustion.Core.FiniteSearch
import StructuralExhaustion.Graph.FiniteObject

namespace StructuralExhaustion.Graph.RootIncidence

open StructuralExhaustion

universe u

variable {V : Type u} (object : FiniteObject V) (root : V)

/-- Two distinct incident edges at one root. -/
structure Divergence where
  leftNext : V
  rightNext : V
  leftAdjacent : object.graph.Adj root leftNext
  rightAdjacent : object.graph.Adj root rightNext
  distinct : leftNext ≠ rightNext

/-- Declared-order first root incidence avoiding both divergent edges. -/
structure Third (divergence : Divergence object root) where
  hit : Core.FiniteSearch.FirstHit
    (object.input.orderedNeighbors root).values
    (fun candidate => candidate ≠ divergence.leftNext ∧
      candidate ≠ divergence.rightNext)

namespace Third

theorem adjacent {divergence : Divergence object root}
    (incidence : Third object root divergence) :
    object.graph.Adj root incidence.hit.value :=
  (object.input.mem_orderedNeighbors_iff _ _).1 incidence.hit.member

theorem ne_left {divergence : Divergence object root}
    (incidence : Third object root divergence) :
    incidence.hit.value ≠ divergence.leftNext := incidence.hit.holds.1

theorem ne_right {divergence : Divergence object root}
    (incidence : Third object root divergence) :
    incidence.hit.value ≠ divergence.rightNext := incidence.hit.holds.2

end Third

/-- Exact cubic/high split retained with the third incidence. -/
inductive Branch (divergence : Divergence object root) : Type u where
  | cubic (degree_eq : object.degree root = 3)
      (incidence : Third object root divergence)
  | high (degree_ge : 4 ≤ object.degree root)
      (incidence : Third object root divergence)

/-- Total scan of the actual declared neighbour list. -/
def classify (degree_ge_three : 3 ≤ object.degree root)
    (divergence : Divergence object root) : Branch object root divergence := by
  letI : DecidableEq V := object.input.vertices.decEq
  let neighbors := (object.input.orderedNeighbors root).values
  let result := Core.FiniteSearch.firstOnList neighbors
    (fun candidate => candidate ≠ divergence.leftNext ∧
      candidate ≠ divergence.rightNext)
    (fun _ => inferInstance)
  have incidence : Third object root divergence := by
    cases resultEq : result with
    | found hit => exact ⟨hit⟩
    | absent absent =>
        have impossible : False := by
          have everyExcluded : ∀ candidate ∈ neighbors,
              candidate = divergence.leftNext ∨
                candidate = divergence.rightNext := by
            intro candidate member
            by_contra neither
            push Not at neither
            exact absent candidate member neither
          have subset : neighbors.toFinset ⊆
              {divergence.leftNext, divergence.rightNext} := by
            intro candidate member
            rw [List.mem_toFinset] at member
            rcases everyExcluded candidate member with equal | equal
            · simp [equal]
            · simp [equal]
          have atMostTwo : neighbors.length ≤ 2 := by
            rw [← List.toFinset_card_of_nodup
              (object.input.orderedNeighbors root).nodup]
            have pairCard :
                ({divergence.leftNext, divergence.rightNext} : Finset V).card ≤ 2 := by
              rcases Finset.card_pair_eq_one_or_two
                  (a := divergence.leftNext) (b := divergence.rightNext) with
                one | two <;> omega
            exact (Finset.card_le_card subset).trans pairCard
          have exactDegree := object.input.orderedNeighbors_length root
          have exactDegree' : neighbors.length = object.degree root := by
            simpa [FiniteObject.degree] using exactDegree
          omega
        exact impossible.elim
  by_cases cubic : object.degree root = 3
  · exact .cubic cubic incidence
  · exact .high (by omega) incidence

def checks : Nat := (object.input.orderedNeighbors root).values.length

theorem checks_le_order : checks object root ≤ object.input.vertices.card := by
  rw [checks, FiniteInput.orderedNeighbors,
    ← FinEnum.orderedValues_length object.input.vertices]
  exact List.length_filter_le _ _

/-- Three pairwise-distinct actual incidences retained at one center. -/
structure AfterEdge (separator : V) where
  predecessor : V
  leftNext : V
  rightNext : V
  predecessorAdjacent : object.graph.Adj separator predecessor
  leftAdjacent : object.graph.Adj separator leftNext
  rightAdjacent : object.graph.Adj separator rightNext
  predecessor_ne_left : predecessor ≠ leftNext
  predecessor_ne_right : predecessor ≠ rightNext
  left_ne_right : leftNext ≠ rightNext

/-- Exact degree split for a center already carrying three certified
incidences. -/
inductive AfterEdgeBranch (separator : V)
    (incidence : AfterEdge object separator) : Type u where
  | cubic (degree_eq : object.degree separator = 3)
  | high (degree_ge : 4 ≤ object.degree separator)

def classifyAfterEdge (separator : V) (degree_ge_three : 3 ≤ object.degree separator)
    (incidence : AfterEdge object separator) :
    AfterEdgeBranch object separator incidence := by
  by_cases cubic : object.degree separator = 3
  · exact .cubic cubic
  · exact .high (by omega)

/-- The after-edge degree split performs only one degree comparison. -/
def afterEdgeChecks : Nat := 1

end StructuralExhaustion.Graph.RootIncidence
