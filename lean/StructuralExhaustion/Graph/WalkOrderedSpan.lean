import StructuralExhaustion.Graph.FiniteTwoBoundaryPiece

namespace StructuralExhaustion.Graph.WalkOrderedSpan

open StructuralExhaustion

universe u

variable {V : Type u} {object : FiniteObject V}

/-!
# A literal bounded span of one supplied simple walk

This module cuts between two supplied walk positions.  It performs no path,
support, graph, or context search.
-/

def spanWalk {start finish : V} (path : object.graph.Walk start finish)
    (left right : Nat) (left_le_right : left ≤ right) :
    object.graph.Walk (path.getVert left) (path.getVert right) :=
  (((path.drop left).take (right - left)).copy rfl (by
    rw [SimpleGraph.Walk.drop_getVert, Nat.add_sub_of_le left_le_right]))

theorem spanWalk_isPath {start finish : V}
    (path : object.graph.Walk start finish) (isPath : path.IsPath)
    (left right : Nat) (left_le_right : left ≤ right) :
    (spanWalk path left right left_le_right).IsPath := by
  unfold spanWalk
  rw [SimpleGraph.Walk.isPath_copy]
  exact (isPath.drop left).take (right - left)

theorem spanWalk_length {start finish : V}
    (path : object.graph.Walk start finish)
    (left right : Nat) (left_le_right : left ≤ right)
    (right_le_length : right ≤ path.length) :
    (spanWalk path left right left_le_right).length = right - left := by
  unfold spanWalk
  rw [SimpleGraph.Walk.length_copy, SimpleGraph.Walk.take_length,
    SimpleGraph.Walk.drop_length,
    Nat.min_eq_left (Nat.sub_le_sub_right right_le_length left)]

/-- The exact induced two-boundary piece on the span support. -/
noncomputable def twoBoundaryInput {start finish : V}
    (path : object.graph.Walk start finish) (isPath : path.IsPath)
    (left right : Nat) (left_lt_right : left < right)
    (right_le_length : right ≤ path.length) :
    FiniteTwoBoundaryPiece.Input object := by
  let walk := spanWalk path left right (Nat.le_of_lt left_lt_right)
  letI : DecidableEq V := object.input.vertices.decEq
  exact {
    support := walk.support.toFinset
    left := path.getVert left
    right := path.getVert right
    left_mem := List.mem_toFinset.mpr walk.start_mem_support
    right_mem := List.mem_toFinset.mpr walk.end_mem_support
    left_ne_right := by
      intro equal
      exact (Nat.ne_of_lt left_lt_right)
        (isPath.getVert_injOn (left_lt_right.le.trans right_le_length)
          right_le_length equal)
  }

theorem twoBoundaryInput_card_le_span_add_one {start finish : V}
    (path : object.graph.Walk start finish) (isPath : path.IsPath)
    (left right : Nat) (left_lt_right : left < right)
    (right_le_length : right ≤ path.length) :
    (twoBoundaryInput path isPath left right left_lt_right
      right_le_length).support.card ≤ right - left + 1 := by
  letI : DecidableEq V := object.input.vertices.decEq
  change (spanWalk path left right left_lt_right.le).support.toFinset.card ≤ _
  calc
    (spanWalk path left right left_lt_right.le).support.toFinset.card
        ≤ (spanWalk path left right left_lt_right.le).support.length :=
          List.toFinset_card_le _
    _ = (spanWalk path left right left_lt_right.le).length + 1 :=
      (spanWalk path left right left_lt_right.le).length_support
    _ = right - left + 1 := by
      rw [spanWalk_length path left right left_lt_right.le right_le_length]

end StructuralExhaustion.Graph.WalkOrderedSpan
