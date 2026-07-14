import StructuralExhaustion.Graph.FiniteObject

namespace StructuralExhaustion.Graph.EliminationOrder

open StructuralExhaustion

universe u

/-- Unordered view of a scheduled vertex list using the object's declared
decidable equality. -/
def verticesFinset (object : FiniteObject V) (values : List V) : Finset V :=
  @List.toFinset V object.input.vertices.decEq values

@[simp]
theorem mem_verticesFinset_iff (object : FiniteObject V) (vertex : V)
    (values : List V) :
    vertex ∈ verticesFinset object values ↔ vertex ∈ values := by
  letI : DecidableEq V := object.input.vertices.decEq
  simp [verticesFinset]

/-- Later neighbours of a vertex in a declared elimination order. -/
def laterNeighbors (object : FiniteObject V) (vertex : V)
    (tail : List V) : List V :=
  tail.filter fun neighbor =>
    @decide (object.graph.Adj vertex neighbor)
      (object.input.decideAdj vertex neighbor)

@[simp]
theorem mem_laterNeighbors_iff (object : FiniteObject V) (vertex neighbor : V)
    (tail : List V) :
    neighbor ∈ laterNeighbors object vertex tail ↔
      neighbor ∈ tail ∧ object.graph.Adj vertex neighbor := by
  letI : DecidableRel object.graph.Adj := object.input.decideAdj
  simp [laterNeighbors]

/-- Machine-checkable elimination-order contract: each vertex has at most
`bound` neighbours later in the order. -/
inductive BoundedOrder (object : FiniteObject V) (bound : Nat) :
    List V → Type u where
  | nil : BoundedOrder object bound []
  | cons {vertex : V} {tail : List V}
      (headBound : (laterNeighbors object vertex tail).length ≤ bound)
      (tailBound : BoundedOrder object bound tail) :
      BoundedOrder object bound (vertex :: tail)

namespace BoundedOrder

/-- A global degree bound generates a bounded elimination certificate for
every duplicate-free vertex schedule. -/
def of_degree_bound (object : FiniteObject V) (bound : Nat)
    (degreeBound : ∀ vertex, object.degree vertex ≤ bound) :
    ∀ values : List V, values.Nodup → BoundedOrder object bound values
  | [], _nodup => .nil
  | vertex :: tail, nodup => by
      have laterNodup : (laterNeighbors object vertex tail).Nodup :=
        nodup.tail.filter _
      have laterSubset : laterNeighbors object vertex tail ⊆
          (object.input.orderedNeighbors vertex).values := by
        intro neighbor member
        exact (object.input.mem_orderedNeighbors_iff vertex neighbor).2
          ((mem_laterNeighbors_iff object vertex neighbor tail).1 member).2
      letI : DecidableEq V := object.input.vertices.decEq
      have finsetSubset :
          (laterNeighbors object vertex tail).toFinset ⊆
            (object.input.orderedNeighbors vertex).values.toFinset := by
        intro neighbor member
        simpa using laterSubset (by simpa using member)
      have countLeOrdered : (laterNeighbors object vertex tail).length ≤
          (object.input.orderedNeighbors vertex).values.length := by
        rw [← List.toFinset_card_of_nodup laterNodup,
          ← List.toFinset_card_of_nodup
            (object.input.orderedNeighbors vertex).nodup]
        exact Finset.card_le_card finsetSubset
      have countLeDegree : (laterNeighbors object vertex tail).length ≤
          object.degree vertex :=
        countLeOrdered.trans_eq
          (object.input.orderedNeighbors_length vertex)
      exact .cons (countLeDegree.trans (degreeBound vertex))
        (of_degree_bound object bound degreeBound tail nodup.tail)

end BoundedOrder

end StructuralExhaustion.Graph.EliminationOrder
