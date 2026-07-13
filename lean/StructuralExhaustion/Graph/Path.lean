import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Hasse
import Mathlib.Combinatorics.SimpleGraph.Paths

namespace StructuralExhaustion.Graph

universe u

/-! ## Canonical path graphs -/

/-- Computable adjacency for Mathlib's canonical finite path graph. -/
@[reducible]
def pathGraphAdjDecidable (order : Nat) :
    DecidableRel (SimpleGraph.pathGraph order).Adj := fun left right =>
  decidable_of_iff
    (left.val + 1 = right.val ∨ right.val + 1 = left.val)
    SimpleGraph.pathGraph_adj.symm

/-- The canonical path graphs used by the finite parity-series fixture are
acyclic graph facts, independent of that application. -/
theorem pathGraph_two_isAcyclic :
    (SimpleGraph.pathGraph 2).IsAcyclic := by
  letI : DecidableRel (SimpleGraph.pathGraph 2).Adj :=
    pathGraphAdjDecidable 2
  letI : Fintype (SimpleGraph.pathGraph 2).edgeSet := inferInstance
  exact (SimpleGraph.isTree_iff_connected_and_card.mpr
    ⟨SimpleGraph.pathGraph_connected 1, by
      have edgeCard : Nat.card (SimpleGraph.pathGraph 2).edgeSet =
          (SimpleGraph.pathGraph 2).edgeFinset.card := by
        rw [Nat.card_eq_fintype_card, SimpleGraph.edgeFinset_card]
      rw [edgeCard, Nat.card_eq_fintype_card]
      native_decide⟩).isAcyclic

theorem pathGraph_three_isAcyclic :
    (SimpleGraph.pathGraph 3).IsAcyclic := by
  letI : DecidableRel (SimpleGraph.pathGraph 3).Adj :=
    pathGraphAdjDecidable 3
  letI : Fintype (SimpleGraph.pathGraph 3).edgeSet := inferInstance
  exact (SimpleGraph.isTree_iff_connected_and_card.mpr
    ⟨SimpleGraph.pathGraph_connected 2, by
      have edgeCard : Nat.card (SimpleGraph.pathGraph 3).edgeSet =
          (SimpleGraph.pathGraph 3).edgeFinset.card := by
        rw [Nat.card_eq_fintype_card, SimpleGraph.edgeFinset_card]
      rw [edgeCard, Nat.card_eq_fintype_card]
      native_decide⟩).isAcyclic

theorem pathGraph_four_isAcyclic :
    (SimpleGraph.pathGraph 4).IsAcyclic := by
  letI : DecidableRel (SimpleGraph.pathGraph 4).Adj :=
    pathGraphAdjDecidable 4
  letI : Fintype (SimpleGraph.pathGraph 4).edgeSet := inferInstance
  exact (SimpleGraph.isTree_iff_connected_and_card.mpr
    ⟨SimpleGraph.pathGraph_connected 3, by
      have edgeCard : Nat.card (SimpleGraph.pathGraph 4).edgeSet =
          (SimpleGraph.pathGraph 4).edgeFinset.card := by
        rw [Nat.card_eq_fintype_card, SimpleGraph.edgeFinset_card]
      rw [edgeCard, Nat.card_eq_fintype_card]
      native_decide⟩).isAcyclic

theorem pathGraph_five_isAcyclic :
    (SimpleGraph.pathGraph 5).IsAcyclic := by
  letI : DecidableRel (SimpleGraph.pathGraph 5).Adj :=
    pathGraphAdjDecidable 5
  letI : Fintype (SimpleGraph.pathGraph 5).edgeSet := inferInstance
  exact (SimpleGraph.isTree_iff_connected_and_card.mpr
    ⟨SimpleGraph.pathGraph_connected 4, by
      have edgeCard : Nat.card (SimpleGraph.pathGraph 5).edgeSet =
          (SimpleGraph.pathGraph 5).edgeFinset.card := by
        rw [Nat.card_eq_fintype_card, SimpleGraph.edgeFinset_card]
      rw [edgeCard, Nat.card_eq_fintype_card]
      native_decide⟩).isAcyclic

/-!
# Rooted paths for sequential machines

`SimpleGraph.Path` is indexed by both endpoints.  A path-extension machine
changes its active endpoint while retaining its initial root, so its state is
the small dependent wrapper `RootedPath`.  All walk and simplicity facts remain
Mathlib facts about the contained `SimpleGraph.Path`.
-/

/-- A Mathlib path whose fixed root is the final vertex and whose active
endpoint is explicit machine state. -/
structure RootedPath {V : Type u} (G : SimpleGraph V) (root : V) where
  endpoint : V
  path : G.Path endpoint root

namespace RootedPath

variable {V : Type u} {G : SimpleGraph V} {root : V}

/-- Vertices in path order, beginning at the active endpoint. -/
def vertices (path : RootedPath G root) : List V :=
  path.path.val.support

def length (path : RootedPath G root) : Nat :=
  path.path.val.length

@[simp]
theorem vertices_nodup (path : RootedPath G root) : path.vertices.Nodup :=
  path.path.property.support_nodup

@[simp]
theorem head_vertices (path : RootedPath G root) :
    path.vertices.head path.path.val.support_ne_nil = path.endpoint :=
  path.path.val.head_support

@[simp]
theorem root_mem_vertices (path : RootedPath G root) : root ∈ path.vertices :=
  path.path.val.end_mem_support

/-- The length-zero path rooted at a selected vertex. -/
def singleton (G : SimpleGraph V) (root : V) : RootedPath G root where
  endpoint := root
  path := SimpleGraph.Path.nil

@[simp]
theorem vertices_singleton (G : SimpleGraph V) (root : V) :
    (singleton G root).vertices = [root] :=
  rfl

/-- Extend a rooted path at its active endpoint using Mathlib's path
constructor. -/
def prepend (path : RootedPath G root) (next : V)
    (edge : G.Adj next path.endpoint) (fresh : next ∉ path.vertices) :
    RootedPath G root where
  endpoint := next
  path :=
    ⟨SimpleGraph.Walk.cons edge path.path.val,
      path.path.property.cons fresh⟩

@[simp]
theorem vertices_prepend (path : RootedPath G root) (next : V)
    (edge : G.Adj next path.endpoint) (fresh : next ∉ path.vertices) :
    (path.prepend next edge fresh).vertices = next :: path.vertices :=
  rfl

@[simp]
theorem length_prepend (path : RootedPath G root) (next : V)
    (edge : G.Adj next path.endpoint) (fresh : next ∉ path.vertices) :
    (path.prepend next edge fresh).length = path.length + 1 :=
  rfl

/-! ## Mathlib subpaths selected by support positions -/

/-- The Mathlib subwalk between two ordered positions of a rooted path. -/
def segment (path : RootedPath G root) (left right : Nat)
    (left_le_right : left ≤ right) :
    G.Walk (path.path.val.getVert left) (path.path.val.getVert right) :=
  (((path.path.val.drop left).take (right - left)).copy rfl (by
    rw [SimpleGraph.Walk.drop_getVert, Nat.add_sub_of_le left_le_right]))

theorem segment_isPath (path : RootedPath G root) (left right : Nat)
    (left_le_right : left ≤ right) :
    (path.segment left right left_le_right).IsPath := by
  unfold segment
  rw [SimpleGraph.Walk.isPath_copy]
  exact (path.path.property.drop left).take (right - left)

theorem segment_length (path : RootedPath G root) (left right : Nat)
    (left_le_right : left ≤ right)
    (right_le_length : right ≤ path.length) :
    (path.segment left right left_le_right).length = right - left := by
  change right ≤ path.path.val.length at right_le_length
  unfold segment
  rw [SimpleGraph.Walk.length_copy, SimpleGraph.Walk.take_length,
    SimpleGraph.Walk.drop_length,
    Nat.min_eq_left (Nat.sub_le_sub_right right_le_length left)]

theorem segment_getVert (path : RootedPath G root) (left right index : Nat)
    (left_le_right : left ≤ right) (index_le : index ≤ right - left) :
    (path.segment left right left_le_right).getVert index =
      path.path.val.getVert (left + index) := by
  simp [segment, SimpleGraph.Walk.take_getVert,
    Nat.min_eq_right index_le, SimpleGraph.Walk.drop_getVert]

/-! ## Ordered endpoint-neighbour positions -/

/-- Executable recognition of an endpoint-neighbour position. -/
def isEndpointNeighborPosition [DecidableRel G.Adj]
    (path : RootedPath G root) (position : Nat) : Bool :=
  match path.vertices[position]? with
  | none => false
  | some vertex => decide (G.Adj path.endpoint vertex)

/-- All positions occupied by neighbours of the active endpoint, in ascending
list order. -/
def endpointNeighborPositions [DecidableRel G.Adj]
    (path : RootedPath G root) : List Nat :=
  (List.range path.vertices.length).filter path.isEndpointNeighborPosition

theorem mem_endpointNeighborPositions_iff [DecidableRel G.Adj]
    (path : RootedPath G root) (position : Nat) :
    position ∈ path.endpointNeighborPositions ↔
      ∃ inBounds : position < path.vertices.length,
        G.Adj path.endpoint path.vertices[position] := by
  simp only [endpointNeighborPositions, List.mem_filter, List.mem_range]
  constructor
  · rintro ⟨inBounds, adjacent⟩
    refine ⟨inBounds, ?_⟩
    simpa [isEndpointNeighborPosition,
      List.getElem?_eq_getElem inBounds] using adjacent
  · rintro ⟨inBounds, adjacent⟩
    refine ⟨inBounds, ?_⟩
    simpa [isEndpointNeighborPosition,
      List.getElem?_eq_getElem inBounds] using adjacent

theorem endpointNeighborPosition_lt [DecidableRel G.Adj]
    (path : RootedPath G root) {position : Nat}
    (member : position ∈ path.endpointNeighborPositions) :
    position < path.vertices.length :=
  (List.mem_filter.mp member).1 |> List.mem_range.mp

theorem endpointNeighborPosition_adjacent [DecidableRel G.Adj]
    (path : RootedPath G root) {position : Nat}
    (member : position ∈ path.endpointNeighborPositions) :
    G.Adj path.endpoint
      (path.vertices.get
        ⟨position, path.endpointNeighborPosition_lt member⟩) := by
  exact (path.mem_endpointNeighborPositions_iff position).mp member |>.2

end RootedPath

end StructuralExhaustion.Graph
