import StructuralExhaustion.Graph.OrderedSupportComponents

namespace StructuralExhaustion.Examples.OrderedSupportComponents

open StructuralExhaustion
open StructuralExhaustion.Graph

universe u

/-!
Problem-independent transfer check for the ordered support decomposition.
The fixture deliberately quantifies over an arbitrary finite graph and one
explicit support: no Erdős predicate or ambient graph-family search appears.
-/

variable {V : Type u} (object : FiniteObject V) (support : Finset V)

example {component : Graph.OrderedSupportComponents.Component object support}
    (member : component ∈ Graph.OrderedSupportComponents.order object support) :
    Graph.NegativeSupportHandoff.ConnectedOn object
      (Graph.OrderedSupportComponents.vertices object support component) :=
  Graph.OrderedSupportComponents.connectedOn_of_mem_order
    object support member

example (vertex : V) :
    vertex ∈ support ↔
      ∃ component ∈ Graph.OrderedSupportComponents.order object support,
        vertex ∈ Graph.OrderedSupportComponents.vertices
          object support component :=
  Graph.OrderedSupportComponents.mem_support_iff_mem_component
    object support vertex

example :
    (Graph.OrderedSupportComponents.order object support).length ≤
      support.card :=
  Graph.OrderedSupportComponents.order_length_le_support_card object support

end StructuralExhaustion.Examples.OrderedSupportComponents
