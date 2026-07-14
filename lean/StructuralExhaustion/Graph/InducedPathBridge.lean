import Mathlib.Tactic
import StructuralExhaustion.Graph.InducedPathAttachment

namespace StructuralExhaustion.Graph.InducedPathBridge

open StructuralExhaustion

universe u

/-!
# Paths and cycles through an induced-path segment

This module is the graph-theoretic core of fan-window cycle arguments.  It
constructs literal Mathlib walks from two external attachment vertices and
one segment of an embedded path.  The construction is symbolic in the four
vertices and two path positions; it never enumerates walks, paths, or graphs.
-/

/-- The path from `leftOutside` to `rightOutside` obtained by entering the
embedded path at `left`, following it to `right`, and leaving at `right`. -/
def bridge {V : Type u} {G : SimpleGraph V} {order : Nat}
    (path : SimpleGraph.pathGraph order ↪g G)
    (leftOutside rightOutside : V) (left right : Fin order)
    (left_le_right : left ≤ right)
    (leftAdjacent : G.Adj leftOutside (path left))
    (rightAdjacent : G.Adj rightOutside (path right)) :
    G.Walk leftOutside rightOutside :=
  .cons leftAdjacent
    ((InducedPathAttachment.ambientSegment path left right left_le_right).concat
      rightAdjacent.symm)

theorem bridge_length {V : Type u} {G : SimpleGraph V} {order : Nat}
    (path : SimpleGraph.pathGraph order ↪g G)
    (leftOutside rightOutside : V) (left right : Fin order)
    (left_le_right : left ≤ right)
    (leftAdjacent : G.Adj leftOutside (path left))
    (rightAdjacent : G.Adj rightOutside (path right)) :
    (bridge path leftOutside rightOutside left right left_le_right
      leftAdjacent rightAdjacent).length = right.1 - left.1 + 2 := by
  simp [bridge, InducedPathAttachment.ambientSegment_length]

/-- The bridge is simple when its two endpoints are distinct and both lie
outside the embedded path. -/
theorem bridge_isPath {V : Type u} {G : SimpleGraph V} {order : Nat}
    (path : SimpleGraph.pathGraph order ↪g G)
    (leftOutside rightOutside : V)
    (leftOutsidePath : ∀ position : Fin order,
      leftOutside ≠ path position)
    (rightOutsidePath : ∀ position : Fin order,
      rightOutside ≠ path position)
    (outsideDistinct : leftOutside ≠ rightOutside)
    (left right : Fin order) (left_le_right : left ≤ right)
    (leftAdjacent : G.Adj leftOutside (path left))
    (rightAdjacent : G.Adj rightOutside (path right)) :
    (bridge path leftOutside rightOutside left right left_le_right
      leftAdjacent rightAdjacent).IsPath := by
  let segment := InducedPathAttachment.ambientSegment path left right
    left_le_right
  have segmentPath : segment.IsPath :=
    InducedPathAttachment.ambientSegment_isPath path left right left_le_right
  have leftAbsent : leftOutside ∉ segment.support :=
    InducedPathAttachment.outside_not_mem_ambientSegment path leftOutside
      leftOutsidePath left right left_le_right
  have entered : (SimpleGraph.Walk.cons leftAdjacent segment).IsPath :=
    (SimpleGraph.Walk.cons_isPath_iff leftAdjacent segment).2
      ⟨segmentPath, leftAbsent⟩
  apply entered.concat
  simp only [SimpleGraph.Walk.support_cons, List.mem_cons]
  rintro (equal | member)
  · exact outsideDistinct equal.symm
  · exact InducedPathAttachment.outside_not_mem_ambientSegment path
      rightOutside rightOutsidePath left right left_le_right member

/-- Orientation-independent bridge between two external attachments. -/
def unorderedBridge {V : Type u} {G : SimpleGraph V} {order : Nat}
    (path : SimpleGraph.pathGraph order ↪g G)
    (leftOutside rightOutside : V) (left right : Fin order)
    (leftAdjacent : G.Adj leftOutside (path left))
    (rightAdjacent : G.Adj rightOutside (path right)) :
    G.Walk leftOutside rightOutside := by
  by_cases orderPositions : left ≤ right
  · exact bridge path leftOutside rightOutside left right orderPositions
      leftAdjacent rightAdjacent
  · exact (bridge path rightOutside leftOutside right left (by omega)
      rightAdjacent leftAdjacent).reverse

theorem unorderedBridge_isPath
    {V : Type u} {G : SimpleGraph V} {order : Nat}
    (path : SimpleGraph.pathGraph order ↪g G)
    (leftOutside rightOutside : V)
    (leftOutsidePath : ∀ position : Fin order,
      leftOutside ≠ path position)
    (rightOutsidePath : ∀ position : Fin order,
      rightOutside ≠ path position)
    (outsideDistinct : leftOutside ≠ rightOutside)
    (left right : Fin order)
    (leftAdjacent : G.Adj leftOutside (path left))
    (rightAdjacent : G.Adj rightOutside (path right)) :
    (unorderedBridge path leftOutside rightOutside left right leftAdjacent
      rightAdjacent).IsPath := by
  unfold unorderedBridge
  split
  · exact bridge_isPath path leftOutside rightOutside leftOutsidePath
      rightOutsidePath outsideDistinct left right ‹left ≤ right› leftAdjacent
      rightAdjacent
  · exact (bridge_isPath path rightOutside leftOutside rightOutsidePath
      leftOutsidePath outsideDistinct.symm right left (by omega) rightAdjacent
      leftAdjacent).reverse

theorem unorderedBridge_length
    {V : Type u} {G : SimpleGraph V} {order : Nat}
    (path : SimpleGraph.pathGraph order ↪g G)
    (leftOutside rightOutside : V) (left right : Fin order)
    (leftAdjacent : G.Adj leftOutside (path left))
    (rightAdjacent : G.Adj rightOutside (path right)) :
    (unorderedBridge path leftOutside rightOutside left right leftAdjacent
      rightAdjacent).length =
      InducedPathAttachment.positionDistance left right + 2 := by
  unfold unorderedBridge
  split
  · have valueOrder : left.1 ≤ right.1 := ‹left ≤ right›
    rw [bridge_length]
    simp [InducedPathAttachment.positionDistance, max_eq_right valueOrder,
      min_eq_left valueOrder]
  · have reverse : right ≤ left := by omega
    have valueOrder : right.1 ≤ left.1 := reverse
    rw [SimpleGraph.Walk.length_reverse, bridge_length]
    simp [InducedPathAttachment.positionDistance, max_eq_left valueOrder,
      min_eq_right valueOrder]

/-- Every tail vertex of an orientation-independent bridge is either on the
embedded path or is its right external endpoint. -/
theorem unorderedBridge_tail_member
    {V : Type u} {G : SimpleGraph V} {order : Nat}
    (path : SimpleGraph.pathGraph order ↪g G)
    (leftOutside rightOutside : V)
    (leftOutsidePath : ∀ position : Fin order,
      leftOutside ≠ path position)
    (rightOutsidePath : ∀ position : Fin order,
      rightOutside ≠ path position)
    (outsideDistinct : leftOutside ≠ rightOutside)
    (left right : Fin order)
    (leftAdjacent : G.Adj leftOutside (path left))
    (rightAdjacent : G.Adj rightOutside (path right))
    {vertex : V}
    (member : vertex ∈ (unorderedBridge path leftOutside rightOutside left
      right leftAdjacent rightAdjacent).support.tail) :
    (∃ position : Fin order, path position = vertex) ∨
      vertex = rightOutside := by
  by_cases positions : left ≤ right
  · have reduced : vertex ∈
        (bridge path leftOutside rightOutside left right positions
          leftAdjacent rightAdjacent).support.tail := by
      simpa [unorderedBridge, positions] using member
    simp only [bridge, SimpleGraph.Walk.support_cons, List.tail_cons,
      SimpleGraph.Walk.support_concat, List.mem_append, List.mem_singleton]
      at reduced
    rcases reduced with segmentMember | equal
    · left
      obtain ⟨position, equal, _bounds⟩ :=
        InducedPathAttachment.mem_ambientSegment_support_bounds path left
          right positions vertex segmentMember
      exact ⟨position, equal⟩
    · exact Or.inr equal
  · have reverse : right ≤ left := by omega
    let forward := bridge path rightOutside leftOutside right left reverse
      rightAdjacent leftAdjacent
    let route := forward.reverse
    have routePath : route.IsPath :=
      (bridge_isPath path rightOutside leftOutside rightOutsidePath
        leftOutsidePath outsideDistinct.symm right left reverse rightAdjacent
        leftAdjacent).reverse
    have routeMember : vertex ∈ route.support.tail := by
      simpa [route, forward, unorderedBridge, positions] using member
    have supportMember : vertex ∈ route.support :=
      List.mem_of_mem_tail routeMember
    have forwardSupport : vertex ∈
        forward.support := by
      change vertex ∈ forward.reverse.support at supportMember
      rw [SimpleGraph.Walk.support_reverse] at supportMember
      simpa using supportMember
    simp only [forward, bridge, SimpleGraph.Walk.support_cons,
      SimpleGraph.Walk.support_concat, List.mem_cons, List.mem_append,
      List.not_mem_nil, or_false] at forwardSupport
    rcases forwardSupport with equal | segmentMember | equal
    · exact Or.inr equal
    · left
      obtain ⟨position, equal, _bounds⟩ :=
        InducedPathAttachment.mem_ambientSegment_support_bounds path right
          left reverse vertex segmentMember
      exact ⟨position, equal⟩
    · subst vertex
      have nodup := routePath.support_nodup
      have startAbsent : leftOutside ∉ route.support.tail := by
        rw [show
          route.support = leftOutside :: route.support.tail from
          route.cons_tail_support.symm] at nodup
        exact (List.nodup_cons.mp nodup).1
      exact (startAbsent routeMember).elim

/-- A bridge contains no third external vertex that is distinct from both
bridge endpoints and lies outside the embedded path. -/
theorem external_not_mem_bridge_support
    {V : Type u} {G : SimpleGraph V} {order : Nat}
    (path : SimpleGraph.pathGraph order ↪g G)
    (leftOutside rightOutside external : V)
    (externalPath : ∀ position : Fin order, external ≠ path position)
    (externalNeLeft : external ≠ leftOutside)
    (externalNeRight : external ≠ rightOutside)
    (left right : Fin order) (left_le_right : left ≤ right)
    (leftAdjacent : G.Adj leftOutside (path left))
    (rightAdjacent : G.Adj rightOutside (path right)) :
    external ∉ (bridge path leftOutside rightOutside left right left_le_right
      leftAdjacent rightAdjacent).support := by
  simp only [bridge, SimpleGraph.Walk.support_cons,
    SimpleGraph.Walk.support_concat, List.mem_cons, List.mem_append,
    List.not_mem_nil, or_false]
  intro member
  rcases member with equal | member | equal
  · exact externalNeLeft equal
  · exact InducedPathAttachment.outside_not_mem_ambientSegment path external
      externalPath left right left_le_right member
  · exact externalNeRight equal

/-- The literal two-edge path `left-middle-right`. -/
def twoEdgePath {V : Type u} {G : SimpleGraph V}
    {left middle right : V} (leftMiddle : G.Adj left middle)
    (middleRight : G.Adj middle right) : G.Walk left right :=
  .cons leftMiddle (.cons middleRight .nil)

theorem twoEdgePath_isPath {V : Type u} {G : SimpleGraph V}
    {left middle right : V} (leftMiddle : G.Adj left middle)
    (middleRight : G.Adj middle right) (leftNeRight : left ≠ right) :
    (twoEdgePath leftMiddle middleRight).IsPath := by
  rw [SimpleGraph.Walk.isPath_def]
  simp [twoEdgePath, leftMiddle.ne, middleRight.ne, leftNeRight]

theorem twoEdgePath_length {V : Type u} {G : SimpleGraph V}
    {left middle right : V} (leftMiddle : G.Adj left middle)
    (middleRight : G.Adj middle right) :
    (twoEdgePath leftMiddle middleRight).length = 2 := rfl

/-- A two-edge route through an external connector and an induced-path
bridge form a literal simple cycle. -/
def connectorCycle
    {V : Type u} {G : SimpleGraph V} {order : Nat}
    (LengthOK : Nat → Prop)
    (path : SimpleGraph.pathGraph order ↪g G)
    (leftOutside connector rightOutside : V)
    (leftOutsidePath : ∀ position : Fin order,
      leftOutside ≠ path position)
    (connectorPath : ∀ position : Fin order,
      connector ≠ path position)
    (rightOutsidePath : ∀ position : Fin order,
      rightOutside ≠ path position)
    (leftNeRight : leftOutside ≠ rightOutside)
    (leftConnector : G.Adj leftOutside connector)
    (connectorRight : G.Adj connector rightOutside)
    (left right : Fin order) (left_le_right : left ≤ right)
    (rightAdjacent : G.Adj rightOutside (path left))
    (leftAdjacent : G.Adj leftOutside (path right))
    (lengthOK : LengthOK (4 + (right.1 - left.1))) :
    CycleWithLength G LengthOK := by
  let upper := twoEdgePath leftConnector connectorRight
  let lower := bridge path rightOutside leftOutside left right left_le_right
    rightAdjacent leftAdjacent
  have upperPath : upper.IsPath :=
    twoEdgePath_isPath leftConnector connectorRight leftNeRight
  have lowerPath : lower.IsPath :=
    bridge_isPath path rightOutside leftOutside rightOutsidePath
      leftOutsidePath leftNeRight.symm left right left_le_right rightAdjacent
      leftAdjacent
  have disjoint : upper.support.tail.Disjoint lower.support.tail := by
    rw [List.disjoint_left]
    intro vertex upperMember lowerMember
    simp [upper, twoEdgePath] at upperMember
    rcases upperMember with equal | equal
    · subst vertex
      have connectorAbsent : connector ∉ lower.support :=
        external_not_mem_bridge_support path rightOutside leftOutside connector
          connectorPath connectorRight.ne leftConnector.ne.symm left right
          left_le_right rightAdjacent leftAdjacent
      exact connectorAbsent (List.mem_of_mem_tail lowerMember)
    · subst vertex
      have lowerNodup := lowerPath.support_nodup
      rw [show lower.support = rightOutside :: lower.support.tail from
        lower.cons_tail_support.symm] at lowerNodup
      exact (List.nodup_cons.mp lowerNodup).1 lowerMember
  refine {
    vertex := leftOutside
    walk := upper.append lower
    isCycle := upperPath.isCycle_append lowerPath disjoint (Or.inl ?_)
    length_ok := ?_
  }
  · simp [upper, twoEdgePath]
  · rw [SimpleGraph.Walk.length_append,
      twoEdgePath_length leftConnector connectorRight,
      bridge_length path rightOutside leftOutside left right left_le_right
        rightAdjacent leftAdjacent]
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using lengthOK

/-- Two disjoint ordered segments of one induced path, closed by the same two
external attachment vertices, form a literal simple cycle.  This is the
generic interlacing-endpoint constructor used by fan-window arguments. -/
def interlacingCycle
    {V : Type u} {G : SimpleGraph V} {order : Nat}
    (LengthOK : Nat → Prop)
    (path : SimpleGraph.pathGraph order ↪g G)
    (leftOutside rightOutside : V)
    (leftOutsidePath : ∀ position : Fin order,
      leftOutside ≠ path position)
    (rightOutsidePath : ∀ position : Fin order,
      rightOutside ≠ path position)
    (outsideDistinct : leftOutside ≠ rightOutside)
    (first second third fourth : Fin order)
    (first_lt_second : first < second)
    (second_lt_third : second < third)
    (third_lt_fourth : third < fourth)
    (leftFirst : G.Adj leftOutside (path first))
    (rightSecond : G.Adj rightOutside (path second))
    (leftThird : G.Adj leftOutside (path third))
    (rightFourth : G.Adj rightOutside (path fourth))
    (lengthOK : LengthOK
      (4 + (second.1 - first.1) + (fourth.1 - third.1))) :
    CycleWithLength G LengthOK := by
  let early := bridge path leftOutside rightOutside first second
    first_lt_second.le leftFirst rightSecond
  let lateForward := bridge path leftOutside rightOutside third fourth
    third_lt_fourth.le leftThird rightFourth
  let late := lateForward.reverse
  have earlyPath : early.IsPath :=
    bridge_isPath path leftOutside rightOutside leftOutsidePath
      rightOutsidePath outsideDistinct first second first_lt_second.le
      leftFirst rightSecond
  have lateForwardPath : lateForward.IsPath :=
    bridge_isPath path leftOutside rightOutside leftOutsidePath
      rightOutsidePath outsideDistinct third fourth third_lt_fourth.le
      leftThird rightFourth
  have latePath : late.IsPath := lateForwardPath.reverse
  have lateStartAbsent : rightOutside ∉ late.support.tail := by
    have nodup := latePath.support_nodup
    rw [show late.support = rightOutside :: late.support.tail from
      late.cons_tail_support.symm] at nodup
    exact (List.nodup_cons.mp nodup).1
  have disjoint : early.support.tail.Disjoint late.support.tail := by
    rw [List.disjoint_left]
    intro vertex earlyMember lateMember
    simp only [early, bridge, SimpleGraph.Walk.support_cons, List.tail_cons,
      SimpleGraph.Walk.support_concat, List.mem_append,
      List.mem_singleton] at earlyMember
    have lateSupport : vertex ∈ lateForward.support := by
      have supportMember : vertex ∈ late.support :=
        List.mem_of_mem_tail lateMember
      change vertex ∈ lateForward.reverse.support at supportMember
      rw [SimpleGraph.Walk.support_reverse] at supportMember
      simpa using supportMember
    simp only [lateForward, bridge, SimpleGraph.Walk.support_cons,
      SimpleGraph.Walk.support_concat, List.mem_cons, List.mem_append,
      List.not_mem_nil, or_false] at lateSupport
    rcases earlyMember with earlySegment | earlyRight
    · rcases lateSupport with lateLeft | lateSegment | lateRight
      · subst vertex
        obtain ⟨position, equal, _firstLe, _leSecond⟩ :=
          InducedPathAttachment.mem_ambientSegment_support_bounds path first
            second first_lt_second.le leftOutside earlySegment
        exact leftOutsidePath position equal.symm
      · obtain ⟨earlyPosition, earlyEqual, _firstLe, earlyLeSecond⟩ :=
          InducedPathAttachment.mem_ambientSegment_support_bounds path first
            second first_lt_second.le vertex earlySegment
        obtain ⟨latePosition, lateEqual, thirdLeLate, _lateLeFourth⟩ :=
          InducedPathAttachment.mem_ambientSegment_support_bounds path third
            fourth third_lt_fourth.le vertex lateSegment
        have positionsEqual : earlyPosition = latePosition :=
          path.injective (earlyEqual.trans lateEqual.symm)
        subst latePosition
        omega
      · subst vertex
        obtain ⟨position, equal, _firstLe, _leSecond⟩ :=
          InducedPathAttachment.mem_ambientSegment_support_bounds path first
            second first_lt_second.le rightOutside earlySegment
        exact rightOutsidePath position equal.symm
    · subst vertex
      rcases lateSupport with lateLeft | lateSegment | lateRight
      · exact outsideDistinct lateLeft.symm
      · obtain ⟨position, equal, _thirdLe, _leFourth⟩ :=
          InducedPathAttachment.mem_ambientSegment_support_bounds path third
            fourth third_lt_fourth.le rightOutside lateSegment
        exact rightOutsidePath position equal.symm
      · exact lateStartAbsent lateMember
  refine {
    vertex := leftOutside
    walk := early.append late
    isCycle := earlyPath.isCycle_append latePath disjoint (Or.inl ?_)
    length_ok := ?_
  }
  · rw [bridge_length path leftOutside rightOutside first second
      first_lt_second.le leftFirst rightSecond]
    omega
  · rw [SimpleGraph.Walk.length_append,
      bridge_length path leftOutside rightOutside first second
        first_lt_second.le leftFirst rightSecond,
      SimpleGraph.Walk.length_reverse,
      bridge_length path leftOutside rightOutside third fourth
        third_lt_fourth.le leftThird rightFourth]
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using lengthOK

end StructuralExhaustion.Graph.InducedPathBridge
