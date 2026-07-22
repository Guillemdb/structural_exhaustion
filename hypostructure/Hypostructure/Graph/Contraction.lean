import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Tactic
import Hypostructure.Graph.Finite

/-!
# Graph contraction

The graph layer contracts one chosen vertex by deleting its name from the
vertex schedule and rerouting adjacency through the surviving endpoint.
This is a reusable finite-graph coordinate, not an application-specific
bridge proof.
-/

namespace Hypostructure.Graph

universe u

/-- The surviving vertex type after contracting away the distinguished
vertex `v`. -/
abbrev ContractedVertex (V : Type u) (v : V) := {x : V // x ≠ v}

/-- The surviving name of the contracted vertex. -/
def contractionCenter {V : Type u} (u v : V) (huv : u ≠ v) :
    ContractedVertex V v :=
  ⟨u, huv⟩

/-- Adjacency in the contracted graph. -/
def contractionGraph {V : Type u} (G : SimpleGraph V) (u v : V) :
    SimpleGraph (ContractedVertex V v) where
  Adj x y := x ≠ y ∧
    (G.Adj x.1 y.1 ∨
      (x.1 = u ∧ G.Adj v y.1) ∨
      (y.1 = u ∧ G.Adj x.1 v))
  symm.symm := by
    intro x y h
    rcases h with ⟨hxy, direct | fromV | toV⟩
    · exact ⟨hxy.symm, Or.inl direct.symm⟩
    · exact ⟨hxy.symm, Or.inr (Or.inr ⟨fromV.1, fromV.2.symm⟩)⟩
    · exact ⟨hxy.symm, Or.inr (Or.inl ⟨toV.1, toV.2.symm⟩)⟩
  loopless.irrefl := by
    intro x h
    exact h.1 rfl

@[simp]
theorem contractionGraph_adj {V : Type u} {G : SimpleGraph V} {u v : V}
    {x y : ContractedVertex V v} :
    (contractionGraph G u v).Adj x y ↔ x ≠ y ∧
      (G.Adj x.1 y.1 ∨
        (x.1 = u ∧ G.Adj v y.1) ∨
        (y.1 = u ∧ G.Adj x.1 v)) :=
  Iff.rfl

/-- The contracted finite graph with the source schedule filtered at the
deleted vertex. -/
def contractionFiniteObject (object : FiniteObject) (u v : object.Vertex) :
    FiniteObject where
  Vertex := ContractedVertex object.Vertex v
  graph := contractionGraph object.graph u v
  vertices := by
    letI : FinEnum object.Vertex := object.vertices
    letI : DecidableEq object.Vertex := object.vertices.decEq
    letI : DecidablePred (fun vertex : object.Vertex => vertex ≠ v) := by
      intro vertex
      infer_instance
    exact FinEnum.Subtype.finEnum (fun vertex : object.Vertex => vertex ≠ v)
  decideAdj := by
    letI : FinEnum object.Vertex := object.vertices
    letI : DecidableEq object.Vertex := object.vertices.decEq
    letI : DecidableRel object.graph.Adj := object.decideAdj
    intro x y
    change Decidable
      (x ≠ y ∧
        (object.graph.Adj x.1 y.1 ∨
          (x.1 = u ∧ object.graph.Adj v y.1) ∨
          (y.1 = u ∧ object.graph.Adj x.1 v)))
    infer_instance

/-- The contracted graph has one fewer vertex than the source. -/
theorem vertexCount_lt (object : FiniteObject) (u v : object.Vertex) :
    (contractionFiniteObject object u v).vertexCount < object.vertexCount := by
  letI : FinEnum object.Vertex := object.vertices
  letI : Fintype object.Vertex := by infer_instance
  letI : FinEnum (ContractedVertex object.Vertex v) :=
    (contractionFiniteObject object u v).vertices
  letI : Fintype (ContractedVertex object.Vertex v) := by infer_instance
  letI : FinEnum (contractionFiniteObject object u v).Vertex :=
    (contractionFiniteObject object u v).vertices
  letI : Fintype (contractionFiniteObject object u v).Vertex := by infer_instance
  simpa [contractionFiniteObject, ContractedVertex, FiniteObject.vertexCount,
    FinEnum.card_eq_fintypeCard] using
    (Fintype.card_subtype_lt (p := fun x : object.Vertex => x ≠ v)
      (x := v) (by simp))

end Hypostructure.Graph
