import Erdos64EG.Future.TypeANodes107To108Handoff
import StructuralExhaustion.Graph.TypeAFourVisibleContinuation

namespace Erdos64EG.Internal.TypeANode93VisibleFamily

open StructuralExhaustion

universe u v w x y

variable
  {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}

abbrev Node61 := TypeBEntryRouting.VerifiedNode61Residual ctx
abbrev Node63 (node61 : Node61 (ctx := ctx)) :=
  TypeANode63Support.VerifiedNode63Residual (ctx := ctx) node61
abbrev Port (node61 : Node61 (ctx := ctx)) (node63 : Node63 node61) :=
  TypeACompletionPortCoordinates.Coordinate (ctx := ctx) node61 node63
abbrev Load {node61 : Node61 (ctx := ctx)} (node63 : Node63 node61) :=
  node63.typeAProfile.Cubic ctx.G.object

abbrev Schedule {node61 : Node61 (ctx := ctx)} (node63 : Node63 node61)
    (port : Port node61 node63)
    (Label : Type v) (SupportDatum : Type w) (Value : Type x) (Fibre : Type y) :=
  Graph.TypeAFourVisibleContinuation.Schedule ctx.G.object node63.typeAProfile
    port (Load node63) Label SupportDatum Value Fibre

/-- Exact yes-payload of original node `[93]`: one actual port and its actual
visible unpeeled return schedule contain at least four entries.  The schedule
entries themselves contain the anchored return, first entry, connector, and
receiver-entry channel. -/
structure VerifiedNode93Residual
    (node61 : Node61 (ctx := ctx)) (node63 : Node63 node61)
    (Label : Type v) (SupportDatum : Type w) (Value : Type x) (Fibre : Type y) where
  port : Port node61 node63
  schedule : Schedule node63 port Label SupportDatum Value Fibre
  atLeastFour : 4 ≤ schedule.entries.length

namespace VerifiedNode93Residual

variable {node61 : Node61 (ctx := ctx)} {node63 : Node63 node61}
variable {Label : Type v} {SupportDatum : Type w} {Value : Type x} {Fibre : Type y}

/-- Original node `[95]` input: deterministically retain the first four actual
visible unpeeled returns in the node-[93] schedule. -/
noncomputable def node95Input
    (node93 : VerifiedNode93Residual node61 node63 Label SupportDatum Value Fibre) :
    node93.schedule.Four :=
  Graph.TypeAFourVisibleContinuation.Schedule.firstFour ctx.G.object
    node63.typeAProfile node93.port node93.schedule node93.atLeastFour

/-- Same four entries, projected to the existing exact continuation-family
classifier. -/
noncomputable def node95Family
    (node93 : VerifiedNode93Residual node61 node63 Label SupportDatum Value Fibre) :
    Graph.TypeADeclaredContinuationCoordinate.Family ctx.G.object
      node63.typeAProfile node93.port Label SupportDatum Value Fibre :=
  Graph.TypeAFourVisibleContinuation.Schedule.family ctx.G.object
    node63.typeAProfile node93.port node93.schedule node93.node95Input

theorem node95Family_has_four
    (node93 : VerifiedNode93Residual node61 node63 Label SupportDatum Value Fibre) :
    node93.node95Family.coordinates.length = 4 :=
  Graph.TypeAFourVisibleContinuation.Schedule.family_has_four ctx.G.object
    node63.typeAProfile node93.port node93.schedule node93.node95Input

theorem node95_loads_distinct
    (node93 : VerifiedNode93Residual node61 node63 Label SupportDatum Value Fibre) :
    Function.Injective (fun i => node93.schedule.load (node93.node95Input.entry i)) :=
  node93.node95Input.load_injective

theorem node95_loads_unpeeled
    (node93 : VerifiedNode93Residual node61 node63 Label SupportDatum Value Fibre)
    (i : Fin 4) :
    node93.schedule.Unpeeled (node93.schedule.load (node93.node95Input.entry i)) :=
  node93.node95Input.unpeeled i

theorem node95_returns_visible
    (node93 : VerifiedNode93Residual node61 node63 Label SupportDatum Value Fibre)
    (i : Fin 4) : node93.schedule.Visible (node93.node95Input.entry i) :=
  node93.node95Input.visible i

/-- Execute the already verified local prefix classifier on exactly the four
node-[93] returns. -/
noncomputable def classifyContinuations
    (node93 : VerifiedNode93Residual node61 node63 Label SupportDatum Value Fibre) :
    Graph.TypeADeclaredContinuationCoordinate.Family.Outcome ctx.G.object
      node63.typeAProfile node93.port node93.node95Family :=
  node93.node95Family.classify ctx.G.object node63.typeAProfile node93.port

end VerifiedNode93Residual

end Erdos64EG.Internal.TypeANode93VisibleFamily
