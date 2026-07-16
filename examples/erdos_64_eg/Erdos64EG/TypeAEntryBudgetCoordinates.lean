import Erdos64EG.TypeAFirstEntryCoordinates
import StructuralExhaustion.Graph.TypeAEntryBudgetCoordinate

namespace Erdos64EG.Internal.TypeAEntryBudgetCoordinates

open StructuralExhaustion

universe u

variable
  {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}

abbrev Node61 := TypeBEntryRouting.VerifiedNode61Residual ctx
abbrev Node63 (node61 : Node61 (ctx := ctx)) :=
  TypeANode63Support.VerifiedNode63Residual (ctx := ctx) node61
abbrev Port (node61 : Node61 (ctx := ctx)) (node63 : Node63 node61) :=
  TypeACompletionPortCoordinates.Coordinate (ctx := ctx) node61 node63

abbrev AnchoredReturn (node61 : Node61 (ctx := ctx))
    (node63 : Node63 node61) (port : Port node61 node63) :=
  Graph.TypeAAnchoredReturnCoordinate.AnchoredReturn ctx.G.object
    node63.typeAProfile port

/-- First entry of any proof-supplied anchored return.  The scan is restricted
to that return's stored support list. -/
noncomputable def firstEntryOf (node61 : Node61 (ctx := ctx))
    (node63 : Node63 node61) (port : Port node61 node63)
    (anchored : AnchoredReturn node61 node63 port) :=
  Graph.TypeAFirstEntryCoordinate.select ctx.G.object node63.typeAProfile
    port anchored

/-- Exact uniqueness clause of `lem:typeA-entry-budget`. -/
theorem completion_port_unique_of_degree_two
    (node61 : Node61 (ctx := ctx)) (node63 : Node63 node61)
    (terminal candidate : Port node61 node63)
    (degreeTwo : (node63.typeAProfile.supportObject ctx.G.object).degree
      (terminal.receiver ctx.G.object node63.typeAProfile) = 2)
    (sameReceiver : candidate.receiver ctx.G.object node63.typeAProfile =
      terminal.receiver ctx.G.object node63.typeAProfile) :
    candidate = terminal :=
  Graph.TypeAEntryBudgetCoordinate.port_eq_of_same_degree_two_receiver
    ctx.G.object node63.typeAProfile terminal candidate degreeTwo sameReceiver

/-- Every anchored return through a degree-two terminal port first enters at a
different receiver. -/
theorem firstEntry_receiver_ne_terminal
    (node61 : Node61 (ctx := ctx)) (node63 : Node63 node61)
    (terminal : Port node61 node63)
    (degreeTwo : (node63.typeAProfile.supportObject ctx.G.object).degree
      (terminal.receiver ctx.G.object node63.typeAProfile) = 2)
    (anchored : AnchoredReturn node61 node63 terminal) :
    let first := firstEntryOf node61 node63 terminal anchored
    (Graph.TypeAEntryBudgetCoordinate.firstEntryPort ctx.G.object
      node63.typeAProfile terminal anchored first).receiver ctx.G.object
        node63.typeAProfile ≠
      terminal.receiver ctx.G.object node63.typeAProfile := by
  let first := firstEntryOf node61 node63 terminal anchored
  exact Graph.TypeAEntryBudgetCoordinate.firstEntry_receiver_ne_terminal
    ctx.G.object node63.typeAProfile terminal degreeTwo anchored first

/-- All distinct outside-to-receiver first-entry edges across every anchored
return through the fixed terminal port are charged to the exact `q(r)` port
coordinates of receivers `r ≠ w`. -/
theorem external_first_entry_edge_budget
    (node61 : Node61 (ctx := ctx)) (node63 : Node63 node61)
    (terminal : Port node61 node63)
    (degreeTwo : (node63.typeAProfile.supportObject ctx.G.object).degree
      (terminal.receiver ctx.G.object node63.typeAProfile) = 2) :
    (Graph.TypeAEntryBudgetCoordinate.possibleFirstEntryEdges ctx.G.object
      node63.typeAProfile terminal).ncard ≤
      Graph.TypeAEntryBudgetCoordinate.otherReceiverDeficiencySum ctx.G.object
        node63.typeAProfile terminal := by
  rw [← Graph.TypeAEntryBudgetCoordinate.otherReceiverCapacity_eq_deficiencySum]
  exact Graph.TypeAEntryBudgetCoordinate.possibleFirstEntryEdges_ncard_le_otherReceiverCapacity
      ctx.G.object
      node63.typeAProfile terminal degreeTwo

/-- The earlier proof-selected anchored return and first-entry producer land in
the all-returns edge family used by the budget. -/
theorem selected_firstEntry_mem_possible
    (node61 : Node61 (ctx := ctx)) (node63 : Node63 node61)
    (terminal : Port node61 node63) :
    let anchored := TypeAAnchoredReturnCoordinates.anchoredReturn
      node61 node63 terminal
    let first := TypeAFirstEntryCoordinates.firstEntry node61 node63 terminal
    Graph.TypeAEntryBudgetCoordinate.firstEntryPort ctx.G.object
        node63.typeAProfile terminal anchored first ∈
      Graph.TypeAEntryBudgetCoordinate.possibleFirstEntryEdges ctx.G.object
        node63.typeAProfile terminal := by
  dsimp only [TypeAFirstEntryCoordinates.firstEntry]
  exact ⟨TypeAAnchoredReturnCoordinates.anchoredReturn node61 node63 terminal,
    Graph.TypeAFirstEntryCoordinate.select ctx.G.object node63.typeAProfile
      terminal (TypeAAnchoredReturnCoordinates.anchoredReturn node61 node63 terminal),
    rfl⟩

theorem visibleChecks_polynomial
    (node61 : Node61 (ctx := ctx)) (node63 : Node63 node61) :
    Graph.TypeACompletionPortCoordinate.visibleChecks ctx.G.object
        node63.typeAProfile +
        Graph.TypeAEntryBudgetCoordinate.additionalChecks ≤
      4 * ctx.G.object.input.vertices.card :=
  Graph.TypeAEntryBudgetCoordinate.totalVisibleChecks_polynomial ctx.G.object
    node63.typeAProfile

end Erdos64EG.Internal.TypeAEntryBudgetCoordinates
