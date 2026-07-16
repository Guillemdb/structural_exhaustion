import StructuralExhaustion.Graph.SelectedWindowIncidenceCoordinate

namespace StructuralExhaustion.Examples.SelectedWindowIncidenceCoordinate

open StructuralExhaustion
open StructuralExhaustion.Graph

universe u

variable {V : Type u} (object : FiniteObject V)

open Graph.SelectedWindowIncidenceCoordinate

example {vertex : V}
    (covered : vertex ∈
      InducedPathPacking.coveredVertices object 13 (by decide)) :
    Nonempty (SelectedSlot object vertex) :=
  SelectedSlot.exists_of_mem_covered object covered

example {vertex : V} (left right : SelectedSlot object vertex) :
    left.window = right.window :=
  SelectedSlot.window_unique object left right

example (incidence : WindowRemainderIncidence object) :
    object.graph.Adj incidence.remainderVertex incidence.windowVertex :=
  incidence.adjacent

example (incidence : CrossWindowIncidence object) :
    incidence.leftSlot.window ≠ incidence.rightSlot.window :=
  incidence.differentOwner

example (incidence : InternalRemainderIncidence object) :
    incidence.leftVertex ∈
        InducedPathPacking.remainderVertices object 13 (by decide) ∧
      incidence.rightVertex ∈
        InducedPathPacking.remainderVertices object 13 (by decide) ∧
      object.graph.Adj incidence.leftVertex incidence.rightVertex :=
  ⟨incidence.leftRemainder, incidence.rightRemainder, incidence.adjacent⟩

end StructuralExhaustion.Examples.SelectedWindowIncidenceCoordinate
