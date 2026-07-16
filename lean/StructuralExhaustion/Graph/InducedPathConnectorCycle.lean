import StructuralExhaustion.Graph.InducedPathBridge

namespace StructuralExhaustion.Graph.InducedPathConnectorCycle

open StructuralExhaustion

universe u

/-!
# A cycle closed by an arbitrary outside connector path

This extends the two-edge connector constructor with a literal simple outside
walk of any declared length.  It is symbolic in one retained walk and does not
enumerate walks or graphs.
-/

/-- A simple path outside an embedded path, together with one attachment at
each endpoint, closes the expected cycle through the embedded segment. -/
def connectorCycle
    {V : Type u} {G : SimpleGraph V} {order : Nat}
    (LengthOK : Nat → Prop)
    (path : SimpleGraph.pathGraph order ↪g G)
    {leftOutside rightOutside : V}
    (connector : G.Walk leftOutside rightOutside)
    (connectorPath : connector.IsPath)
    (connectorOutside : ∀ vertex ∈ connector.support,
      ∀ position : Fin order, vertex ≠ path position)
    (outsideDistinct : leftOutside ≠ rightOutside)
    (leftPosition rightPosition : Fin order)
    (leftAdjacent : G.Adj leftOutside (path leftPosition))
    (rightAdjacent : G.Adj rightOutside (path rightPosition))
    (lengthOK : LengthOK
      (connector.length + 2 +
        InducedPathAttachment.positionDistance leftPosition rightPosition)) :
    CycleWithLength G LengthOK := by
  let lower := InducedPathBridge.unorderedBridge path rightOutside leftOutside
    rightPosition leftPosition rightAdjacent leftAdjacent
  have leftOutsidePath : ∀ position : Fin order,
      leftOutside ≠ path position := by
    intro position equal
    exact connectorOutside leftOutside (by simp) position equal
  have rightOutsidePath : ∀ position : Fin order,
      rightOutside ≠ path position := by
    intro position equal
    exact connectorOutside rightOutside
      connector.end_mem_support position equal
  have lowerPath : lower.IsPath :=
    InducedPathBridge.unorderedBridge_isPath path rightOutside leftOutside
      rightOutsidePath leftOutsidePath outsideDistinct.symm
      rightPosition leftPosition rightAdjacent leftAdjacent
  have disjoint : connector.support.tail.Disjoint lower.support.tail := by
    rw [List.disjoint_left]
    intro vertex connectorMember lowerMember
    rcases InducedPathBridge.unorderedBridge_tail_member path
        rightOutside leftOutside rightOutsidePath leftOutsidePath
        outsideDistinct.symm rightPosition leftPosition rightAdjacent
        leftAdjacent lowerMember with ⟨position, equal⟩ | equal
    · exact connectorOutside vertex (List.mem_of_mem_tail connectorMember)
        position equal.symm
    · subst vertex
      have nodup := connectorPath.support_nodup
      rw [show connector.support =
          leftOutside :: connector.support.tail from
        connector.cons_tail_support.symm] at nodup
      exact (List.nodup_cons.mp nodup).1 connectorMember
  refine {
    vertex := leftOutside
    walk := connector.append lower
    isCycle := connectorPath.isCycle_append lowerPath disjoint (Or.inr ?_)
    length_ok := ?_
  }
  · rw [InducedPathBridge.unorderedBridge_length path rightOutside
      leftOutside rightPosition leftPosition rightAdjacent leftAdjacent]
    omega
  · rw [SimpleGraph.Walk.length_append,
      InducedPathBridge.unorderedBridge_length path rightOutside leftOutside
        rightPosition leftPosition rightAdjacent leftAdjacent]
    simpa [InducedPathAttachment.positionDistance, Nat.max_comm, Nat.min_comm,
      Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using lengthOK

end StructuralExhaustion.Graph.InducedPathConnectorCycle
