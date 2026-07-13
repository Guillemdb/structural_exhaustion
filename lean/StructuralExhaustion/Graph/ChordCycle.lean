import StructuralExhaustion.Graph.Cycle
import StructuralExhaustion.Graph.Path

namespace StructuralExhaustion.Graph

universe u

variable {V : Type u} {G : SimpleGraph V} {root : V}

/-!
# Cycles cut out by two endpoint chords

Two neighbours of the active endpoint of a simple path cut out a simple
cycle.  The construction below is entirely in terms of Mathlib subwalks and
`Walk.cons_isCycle_iff`; no list-level cycle model is introduced.
-/

namespace RootedPath

/-- Return from the left chord endpoint along the selected path segment and
then across the right chord to the active endpoint. -/
def chordReturn (path : RootedPath G root) (left right : Nat)
    (left_le_right : left ≤ right)
    (rightAdjacent : G.Adj path.endpoint (path.path.val.getVert right)) :
    G.Walk (path.path.val.getVert left) path.endpoint :=
  (path.segment left right left_le_right).concat rightAdjacent.symm

/-- Close the chord return with the left endpoint chord. -/
def chordCycle (path : RootedPath G root) (left right : Nat)
    (left_le_right : left ≤ right)
    (leftAdjacent : G.Adj path.endpoint (path.path.val.getVert left))
    (rightAdjacent : G.Adj path.endpoint (path.path.val.getVert right)) :
    G.Walk path.endpoint path.endpoint :=
  SimpleGraph.Walk.cons leftAdjacent
    (path.chordReturn left right left_le_right rightAdjacent)

private theorem endpoint_not_mem_segment (path : RootedPath G root)
    {left right : Nat} (left_lt_right : left < right)
    (left_pos : 0 < left)
    (right_le_length : right ≤ path.length) :
    path.endpoint ∉ (path.segment left right left_lt_right.le).support := by
  change right ≤ path.path.val.length at right_le_length
  intro endpointMem
  rw [SimpleGraph.Walk.mem_support_iff_exists_getVert] at endpointMem
  obtain ⟨index, indexValue, indexLe⟩ := endpointMem
  have index_le_diff : index ≤ right - left := by
    rw [path.segment_length left right left_lt_right.le right_le_length] at indexLe
    exact indexLe
  have mapped :=
    path.segment_getVert left right index left_lt_right.le index_le_diff
  have equalAtZero :
      path.path.val.getVert (left + index) = path.path.val.getVert 0 := by
    calc
      path.path.val.getVert (left + index) =
          (path.segment left right left_lt_right.le).getVert index := mapped.symm
      _ = path.endpoint := indexValue
      _ = path.path.val.getVert 0 := path.path.val.getVert_zero.symm
  have indexEqual : left + index = 0 :=
    path.path.property.getVert_injOn
      (by simp only [Set.mem_setOf_eq]; omega)
      (by simp)
      equalAtZero
  omega

theorem chordReturn_isPath (path : RootedPath G root)
    {left right : Nat} (left_lt_right : left < right)
    (right_le_length : right ≤ path.length)
    (leftAdjacent : G.Adj path.endpoint (path.path.val.getVert left))
    (rightAdjacent : G.Adj path.endpoint (path.path.val.getVert right)) :
    (path.chordReturn left right left_lt_right.le rightAdjacent).IsPath := by
  have left_pos : 0 < left := by
    by_contra notPositive
    have equalZero : left = 0 := Nat.eq_zero_of_not_pos notPositive
    subst left
    have loop : G.Adj path.endpoint path.endpoint := by
      simpa only [SimpleGraph.Walk.getVert_zero] using leftAdjacent
    exact G.irrefl loop
  apply (path.segment_isPath left right left_lt_right.le).concat
  exact path.endpoint_not_mem_segment left_lt_right left_pos right_le_length

theorem chordReturn_length (path : RootedPath G root)
    {left right : Nat} (left_lt_right : left < right)
    (right_le_length : right ≤ path.length)
    (rightAdjacent : G.Adj path.endpoint (path.path.val.getVert right)) :
    (path.chordReturn left right left_lt_right.le rightAdjacent).length =
      right - left + 1 := by
  simp [chordReturn,
    path.segment_length left right left_lt_right.le right_le_length]

private theorem closingEdge_not_mem_chordReturn
    (path : RootedPath G root) {left right : Nat}
    (left_lt_right : left < right)
    (right_le_length : right ≤ path.length)
    (leftAdjacent : G.Adj path.endpoint (path.path.val.getVert left))
    (rightAdjacent : G.Adj path.endpoint (path.path.val.getVert right)) :
    s(path.endpoint, path.path.val.getVert left) ∉
      (path.chordReturn left right left_lt_right.le rightAdjacent).edges := by
  intro edgeMem
  have swapped :
      s(path.path.val.getVert left, path.endpoint) ∈
        (path.chordReturn left right left_lt_right.le rightAdjacent).edges := by
    rwa [Sym2.eq_swap]
  have lengthOne :=
    (path.chordReturn_isPath left_lt_right right_le_length
      leftAdjacent rightAdjacent)
      |>.length_eq_one_of_mem_edges swapped
  have exactLength :=
    path.chordReturn_length left_lt_right right_le_length rightAdjacent
  omega

theorem chordCycle_isCycle (path : RootedPath G root)
    {left right : Nat} (left_lt_right : left < right)
    (right_le_length : right ≤ path.length)
    (leftAdjacent : G.Adj path.endpoint (path.path.val.getVert left))
    (rightAdjacent : G.Adj path.endpoint (path.path.val.getVert right)) :
    (path.chordCycle left right left_lt_right.le
      leftAdjacent rightAdjacent).IsCycle := by
  rw [chordCycle, SimpleGraph.Walk.cons_isCycle_iff]
  exact
    ⟨path.chordReturn_isPath left_lt_right right_le_length
        leftAdjacent rightAdjacent,
      path.closingEdge_not_mem_chordReturn
        left_lt_right right_le_length leftAdjacent rightAdjacent⟩

theorem chordCycle_length (path : RootedPath G root)
    {left right : Nat} (left_lt_right : left < right)
    (right_le_length : right ≤ path.length)
    (leftAdjacent : G.Adj path.endpoint (path.path.val.getVert left))
    (rightAdjacent : G.Adj path.endpoint (path.path.val.getVert right)) :
    (path.chordCycle left right left_lt_right.le
      leftAdjacent rightAdjacent).length = right - left + 2 := by
  simp [chordCycle,
    path.chordReturn_length left_lt_right right_le_length rightAdjacent]

/-- Same-parity chord positions give an even Mathlib simple cycle. -/
def evenCycleOfEndpointChords (path : RootedPath G root)
    {left right : Nat} (left_lt_right : left < right)
    (right_le_length : right ≤ path.length)
    (leftAdjacent : G.Adj path.endpoint (path.path.val.getVert left))
    (rightAdjacent : G.Adj path.endpoint (path.path.val.getVert right))
    (sameParity : left % 2 = right % 2) :
    CycleWithLength G (fun length => length % 2 = 0) where
  vertex := path.endpoint
  walk := path.chordCycle left right left_lt_right.le
    leftAdjacent rightAdjacent
  isCycle := path.chordCycle_isCycle left_lt_right right_le_length
    leftAdjacent rightAdjacent
  length_ok := by
    rw [path.chordCycle_length left_lt_right right_le_length
      leftAdjacent rightAdjacent]
    omega

/-- Position-list form used directly after endpoint-neighbour collection and a
parity pigeonhole step. -/
def evenCycleOfEndpointNeighborPositions [DecidableRel G.Adj]
    (path : RootedPath G root) {left right : Nat}
    (leftMember : left ∈ path.endpointNeighborPositions)
    (rightMember : right ∈ path.endpointNeighborPositions)
    (left_lt_right : left < right)
    (sameParity : left % 2 = right % 2) :
    CycleWithLength G (fun length => length % 2 = 0) := by
  have leftLe : left ≤ path.length := by
    have bound := path.endpointNeighborPosition_lt leftMember
    change left < path.path.val.support.length at bound
    rw [SimpleGraph.Walk.length_support] at bound
    change left ≤ path.path.val.length
    omega
  have rightLe : right ≤ path.length := by
    have bound := path.endpointNeighborPosition_lt rightMember
    change right < path.path.val.support.length at bound
    rw [SimpleGraph.Walk.length_support] at bound
    change right ≤ path.path.val.length
    omega
  have leftAdjacent :
      G.Adj path.endpoint (path.path.val.getVert left) := by
    rw [path.path.val.getVert_eq_support_getElem leftLe]
    exact path.endpointNeighborPosition_adjacent leftMember
  have rightAdjacent :
      G.Adj path.endpoint (path.path.val.getVert right) := by
    rw [path.path.val.getVert_eq_support_getElem rightLe]
    exact path.endpointNeighborPosition_adjacent rightMember
  exact path.evenCycleOfEndpointChords left_lt_right rightLe
    leftAdjacent rightAdjacent sameParity

end RootedPath

end StructuralExhaustion.Graph
