import Erdos64EG.Future.TypeANode93VisibleFamily

namespace Erdos64EG.Internal.TypeAExit2CommonPort

open StructuralExhaustion

universe u v w x y

variable
  {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}

abbrev Node61 := TypeBEntryRouting.VerifiedNode61Residual ctx
abbrev Node63 (node61 : Node61 (ctx := ctx)) :=
  TypeANode63Support.VerifiedNode63Residual (ctx := ctx) node61
abbrev Port (node61 : Node61 (ctx := ctx)) (node63 : Node63 node61) :=
  TypeACompletionPortCoordinates.Coordinate (ctx := ctx) node61 node63

abbrev Coordinate {node61 : Node61 (ctx := ctx)} (node63 : Node63 node61)
    (port : Port node61 node63)
    (Label : Type v) (SupportDatum : Type w) (Value : Type x) (Fibre : Type y) :=
  Graph.TypeADeclaredContinuationCoordinate.Coordinate ctx.G.object
    node63.typeAProfile port Label SupportDatum Value Fibre

/-- Original exit (2), with the disjointness written in the exact orientation
consumed by Mathlib's two-path cycle constructor.  Reversing the right path
removes its receiver endpoint from the tail, while the left tail removes the
common outside endpoint. -/
structure Exit2
    {node61 : Node61 (ctx := ctx)} (node63 : Node63 node61)
    (port : Port node61 node63)
    (Label : Type v) (SupportDatum : Type w) (Value : Type x) (Fibre : Type y) where
  left : Coordinate node63 port Label SupportDatum Value Fibre
  right : Coordinate node63 port Label SupportDatum Value Fibre
  distinct : left ≠ right
  internallyDisjoint : left.anchored.path ctx.G.object node63.typeAProfile |>.support.tail.Disjoint
    (right.anchored.path ctx.G.object node63.typeAProfile).reverse.support.tail
  nontrivial :
    1 < (left.anchored.path ctx.G.object node63.typeAProfile).length ∨
      1 < (right.anchored.path ctx.G.object node63.typeAProfile).length
  totalPowerOfTwo : PowerOfTwoLength
    ((left.anchored.path ctx.G.object node63.typeAProfile).length +
      (right.anchored.path ctx.G.object node63.typeAProfile).length)

namespace Exit2

variable {node61 : Node61 (ctx := ctx)} {node63 : Node63 node61}
variable {port : Port node61 node63}
variable {Label : Type v} {SupportDatum : Type w} {Value : Type x} {Fibre : Type y}

noncomputable def cycle
    (exit2 : Exit2 node63 port Label SupportDatum Value Fibre) :
    Graph.CycleWithLength ctx.G.object.graph PowerOfTwoLength := by
  let deleted := Graph.TypeAReceiverEntryChannel.DeletedGraph ctx.G.object
    node63.typeAProfile port
  let leftPath := exit2.left.anchored.path ctx.G.object node63.typeAProfile
  let rightPath := exit2.right.anchored.path ctx.G.object node63.typeAProfile
  let closed : deleted.Walk (port.outside ctx.G.object node63.typeAProfile)
      (port.outside ctx.G.object node63.typeAProfile) :=
    leftPath.append rightPath.reverse
  let localCycle : Graph.CycleWithLength deleted PowerOfTwoLength := {
    vertex := port.outside ctx.G.object node63.typeAProfile
    walk := closed
    isCycle := (exit2.left.anchored.isPath ctx.G.object node63.typeAProfile).isCycle_append
      ((exit2.right.anchored.isPath ctx.G.object node63.typeAProfile).reverse)
      exit2.internallyDisjoint (by
        simpa only [SimpleGraph.Walk.length_reverse] using exit2.nontrivial)
    length_ok := by
      change PowerOfTwoLength (closed.length)
      rw [SimpleGraph.Walk.length_append, SimpleGraph.Walk.length_reverse]
      exact exit2.totalPowerOfTwo }
  exact localCycle.mapLe (ctx.G.object.graph.deleteEdges_le _)

/-- Node `[98]`: exit (2) is a literal forbidden cycle in the identical
selected graph. -/
theorem closes
    (exit2 : Exit2 node63 port Label SupportDatum Value Fibre) : False :=
  ctx.avoids ⟨exit2.cycle⟩

end Exit2

end Erdos64EG.Internal.TypeAExit2CommonPort
