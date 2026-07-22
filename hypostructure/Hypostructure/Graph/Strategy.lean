import Hypostructure.Core.Strategy
import Hypostructure.Graph.Object
import Hypostructure.Graph.SupportComponents

/-!
# Graph adapters for reusable strategies

Graph supplies finite schedules and graph semantics.  Strategy ownership,
ledger composition, and terminal routing remain in Core.
-/

namespace Hypostructure.Graph.Strategy

universe u

open Hypostructure

/-- The canonical vertex scan for any finite graph strategy. -/
noncomputable def vertexScan (object : Graph.FiniteObject.{u}) :
    Core.Finite.Enumeration object.Vertex :=
  { values := object.orderedVertices
    nodup := object.orderedVertices_nodup
    decEq := object.vertices.decEq }

/-- The canonical schedule of a supplied induced support. -/
noncomputable def supportScan (object : Graph.FiniteObject.{u})
    (support : Finset object.Vertex) :
    Core.Finite.Enumeration {vertex : object.Vertex // vertex ∈ support} :=
  Graph.SupportComponents.Connected.schedule object support

/-- Generic graph witness-scan interface.  The graph-specific predicate is the
only application input; order and finite scheduling are framework-owned. -/
structure WitnessScan (Previous : Type u) where
  object : Core.Residual.Query Previous (fun _ => Graph.FiniteObject.{u})
  witness : (previous : Previous) -> (object.read previous).Vertex -> Prop
  witnessDecidable : (previous : Previous) ->
    (vertex : (object.read previous).Vertex) ->
      Decidable (witness previous vertex)

/-- Generic graph response interface for local finite coordinates. -/
structure ResponseProfile (Previous : Type u) where
  Coordinate : Previous -> Type u
  schedule : Core.Residual.Query Previous
    (fun previous => Core.Finite.Enumeration (Coordinate previous))
  observe : (previous : Previous) -> Coordinate previous -> Bool

/-- Generic graph charge interface.  `charge` may be an integer graph charge,
while the Core capacity strategy can be instantiated with another quantity in
other domains. -/
structure ChargeProfile (Previous : Type u) where
  Item : Previous -> Type u
  schedule : Core.Residual.Query Previous
    (fun previous => Core.Finite.Enumeration (Item previous))
  charge : (previous : Previous) -> Item previous -> Int

/-- Connected-support specialization used by the Type A/Type B split. -/
structure ConnectedSupportProfile (Previous : Type u) where
  object : Core.Residual.Query Previous (fun _ => Graph.FiniteObject.{u})
  support : Core.Residual.Query Previous (fun previous =>
    Finset (object.read previous).Vertex)

noncomputable def connectedComponents
    (profile : ConnectedSupportProfile Previous) (previous : Previous) :
    List (Graph.SupportComponents.Connected.Component
      (profile.object.read previous) (profile.support.read previous)) :=
  Graph.SupportComponents.Connected.order
    (profile.object.read previous) (profile.support.read previous)

end Hypostructure.Graph.Strategy
