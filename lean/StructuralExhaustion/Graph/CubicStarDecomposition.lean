import StructuralExhaustion.Graph.CubicStar
import StructuralExhaustion.Graph.PackedBoundariedGluing

namespace StructuralExhaustion.Graph.CubicStarDecomposition

open StructuralExhaustion

universe u

variable {V : Type u} (object : FiniteObject V) {center : V}
variable (data : CubicStar.Data object center)

abbrev Boundary := ULift.{u} (Fin 3)
abbrev CenterVertex := ULift.{u} Unit
abbrev Outside := {vertex : V // vertex ∉ CubicStar.Data.support object data}

def boundaryVertex (index : Boundary) : V :=
  match index.down with
  | 0 => data.first
  | 1 => data.second
  | 2 => data.third

theorem boundaryVertex_injective : Function.Injective (boundaryVertex object data) := by
  rintro ⟨left⟩ ⟨right⟩ equal
  congr
  fin_cases left <;> fin_cases right <;>
    simp_all [boundaryVertex, data.first_ne_second, data.first_ne_third,
      data.second_ne_third, Ne.symm data.first_ne_second,
      Ne.symm data.first_ne_third, Ne.symm data.second_ne_third]

theorem boundaryVertex_mem_support (index : Boundary) :
    boundaryVertex object data index ∈ CubicStar.Data.support object data := by
  letI : DecidableEq V := object.input.vertices.decEq
  rcases index with ⟨index⟩
  fin_cases index <;> simp [boundaryVertex, CubicStar.Data.support,
    CubicStar.Data.boundary]

theorem center_mem_support :
    center ∈ CubicStar.Data.support object data := by
  letI : DecidableEq V := object.input.vertices.decEq
  simp [CubicStar.Data.support]

theorem boundaryVertex_adjacent (index : Boundary) :
    object.graph.Adj center (boundaryVertex object data index) := by
  rcases index with ⟨index⟩
  fin_cases index
  · exact data.firstAdjacent
  · exact data.secondAdjacent
  · exact data.thirdAdjacent

@[implicit_reducible]
noncomputable def outsideVertices : FinEnum (Outside object data) := by
  letI : DecidableEq V := object.input.vertices.decEq
  exact Core.Enumeration.subtype object.input.vertices
    (fun vertex => vertex ∉ CubicStar.Data.support object data)
    (fun _vertex => inferInstance)

def pieceVertex : Boundary ⊕ CenterVertex → V
  | .inl index => boundaryVertex object data index
  | .inr _ => center

def contextVertex : Boundary ⊕ Outside object data → V
  | .inl index => boundaryVertex object data index
  | .inr vertex => vertex.1

def piece : PackedBoundariedGluing.Piece Boundary where
  Internal := CenterVertex
  internalVertices := inferInstance
  graph := object.graph.comap (pieceVertex object data)
  decideAdj := fun _left _right => object.input.decideAdj _ _

def contextGraph : SimpleGraph (Boundary ⊕ Outside object data) where
  Adj left right := object.graph.Adj
      (contextVertex object data left) (contextVertex object data right) ∧
    ((∃ outside, left = .inr outside) ∨ ∃ outside, right = .inr outside)
  symm.symm := by
    intro left right adjacent
    refine ⟨adjacent.1.symm, ?_⟩
    rcases adjacent.2 with ⟨outside, equal⟩ | ⟨outside, equal⟩
    · exact Or.inr ⟨outside, equal⟩
    · exact Or.inl ⟨outside, equal⟩
  loopless.irrefl := by
    intro vertex adjacent
    exact object.graph.irrefl adjacent.1

noncomputable def outside : PackedBoundariedGluing.Context Boundary where
  Internal := Outside object data
  internalVertices := outsideVertices object data
  graph := contextGraph object data
  decideAdj := by
    classical
    infer_instance
  noBoundaryEdge := by
    intro left right adjacent
    exact adjacent.2.elim
      (by rintro ⟨outside, impossible⟩; cases impossible)
      (by rintro ⟨outside, impossible⟩; cases impossible)

abbrev Combined := Boundary ⊕ (CenterVertex ⊕ Outside object data)

def combinedVertex : Combined object data → V
  | .inl index => boundaryVertex object data index
  | .inr (.inl _) => center
  | .inr (.inr outside) => outside.1

theorem combinedVertex_injective : Function.Injective (combinedVertex object data) := by
  letI : DecidableEq V := object.input.vertices.decEq
  have centerNe (index : Boundary) : center ≠ boundaryVertex object data index := by
    exact (boundaryVertex_adjacent object data index).ne
  have outsideNeBoundary (outside : Outside object data) (index : Boundary) :
      outside.1 ≠ boundaryVertex object data index := by
    intro equal
    apply outside.property
    rw [equal]
    exact boundaryVertex_mem_support object data index
  have outsideNeCenter (outside : Outside object data) : outside.1 ≠ center := by
    intro equal
    apply outside.property
    rw [equal]
    exact center_mem_support object data
  intro left right equal
  cases left with
  | inl leftBoundary =>
      cases right with
      | inl rightBoundary =>
          exact congrArg Sum.inl (boundaryVertex_injective object data equal)
      | inr rightInternal =>
          cases rightInternal with
          | inl rightCenter =>
              exact (centerNe leftBoundary equal.symm).elim
          | inr rightOutside =>
              exact (outsideNeBoundary rightOutside leftBoundary equal.symm).elim
  | inr leftInternal =>
      cases leftInternal with
      | inl leftCenter =>
          cases right with
          | inl rightBoundary =>
              exact (centerNe rightBoundary equal).elim
          | inr rightInternal =>
              cases rightInternal with
              | inl rightCenter =>
                  rcases leftCenter with ⟨⟨⟩⟩
                  rcases rightCenter with ⟨⟨⟩⟩
                  rfl
              | inr rightOutside =>
                  exact (outsideNeCenter rightOutside equal.symm).elim
      | inr leftOutside =>
          cases right with
          | inl rightBoundary =>
              exact (outsideNeBoundary leftOutside rightBoundary equal).elim
          | inr rightInternal =>
              cases rightInternal with
              | inl rightCenter =>
                  exact (outsideNeCenter leftOutside equal).elim
              | inr rightOutside =>
                  congr
                  exact Subtype.ext equal

theorem combinedVertex_surjective : Function.Surjective (combinedVertex object data) := by
  intro vertex
  letI : DecidableEq V := object.input.vertices.decEq
  by_cases member : vertex ∈ CubicStar.Data.support object data
  · rw [CubicStar.Data.support, Finset.mem_insert] at member
    rcases member with rfl | boundaryMember
    · exact ⟨.inr (.inl ⟨()⟩), rfl⟩
    · simp only [CubicStar.Data.boundary, Finset.mem_insert,
        Finset.mem_singleton] at boundaryMember
      rcases boundaryMember with rfl | rfl | rfl
      · exact ⟨.inl ⟨0⟩, rfl⟩
      · exact ⟨.inl ⟨1⟩, rfl⟩
      · exact ⟨.inl ⟨2⟩, rfl⟩
  · exact ⟨.inr (.inr ⟨vertex, member⟩), rfl⟩

noncomputable def vertexEquiv : Combined object data ≃ V :=
  Equiv.ofBijective (combinedVertex object data)
    ⟨combinedVertex_injective object data, combinedVertex_surjective object data⟩

@[simp] theorem vertexEquiv_apply (vertex : Combined object data) :
    vertexEquiv object data vertex = combinedVertex object data vertex := rfl

theorem pieceSound (left right : Boundary ⊕ CenterVertex)
    (adjacent : (piece object data).graph.Adj left right) :
    object.graph.Adj
      (vertexEquiv object data
        (PackedBoundariedGluing.pieceEmbedding (piece object data)
          (outside object data) left))
      (vertexEquiv object data
        (PackedBoundariedGluing.pieceEmbedding (piece object data)
          (outside object data) right)) := by
  cases left <;> cases right <;> exact adjacent

theorem contextSound (left right : Boundary ⊕ Outside object data)
    (adjacent : (outside object data).graph.Adj left right) :
    object.graph.Adj
      (vertexEquiv object data
        (PackedBoundariedGluing.contextEmbedding (piece object data)
          (outside object data) left))
      (vertexEquiv object data
        (PackedBoundariedGluing.contextEmbedding (piece object data)
          (outside object data) right)) := by
  cases left <;> cases right <;> exact adjacent.1

theorem center_not_adjacent_outside (outsideVertex : Outside object data) :
    ¬object.graph.Adj center outsideVertex.1 := by
  letI : DecidableEq V := object.input.vertices.decEq
  intro adjacent
  have boundaryMember :=
    (CubicStar.Data.adjacent_iff_mem_boundary object data outsideVertex.1).1 adjacent
  exact outsideVertex.property (Finset.mem_insert_of_mem boundaryMember)

theorem ambientOwned (left right : Combined object data)
    (adjacent : object.graph.Adj
      (vertexEquiv object data left) (vertexEquiv object data right)) :
    (∃ pieceLeft pieceRight,
      (piece object data).graph.Adj pieceLeft pieceRight ∧
        PackedBoundariedGluing.pieceEmbedding (piece object data)
          (outside object data) pieceLeft = left ∧
        PackedBoundariedGluing.pieceEmbedding (piece object data)
          (outside object data) pieceRight = right) ∨
    (∃ contextLeft contextRight,
      (outside object data).graph.Adj contextLeft contextRight ∧
        PackedBoundariedGluing.contextEmbedding (piece object data)
          (outside object data) contextLeft = left ∧
        PackedBoundariedGluing.contextEmbedding (piece object data)
          (outside object data) contextRight = right) := by
  cases left with
  | inl leftBoundary =>
      cases right with
      | inl rightBoundary =>
          exact Or.inl ⟨.inl leftBoundary, .inl rightBoundary, adjacent, rfl, rfl⟩
      | inr rightInternal =>
          cases rightInternal with
          | inl rightCenter =>
              exact Or.inl ⟨.inl leftBoundary, .inr ⟨()⟩, adjacent, rfl, rfl⟩
          | inr rightOutside =>
              exact Or.inr ⟨.inl leftBoundary, .inr rightOutside,
                ⟨adjacent, Or.inr ⟨rightOutside, rfl⟩⟩, rfl, rfl⟩
  | inr leftInternal =>
      cases leftInternal with
      | inl leftCenter =>
          cases right with
          | inl rightBoundary =>
              exact Or.inl ⟨.inr ⟨()⟩, .inl rightBoundary, adjacent, rfl, rfl⟩
          | inr rightInternal =>
              cases rightInternal with
              | inl rightCenter => exact (object.graph.irrefl adjacent).elim
              | inr rightOutside =>
                  exact (center_not_adjacent_outside object data rightOutside adjacent).elim
      | inr leftOutside =>
          cases right with
          | inl rightBoundary =>
              exact Or.inr ⟨.inr leftOutside, .inl rightBoundary,
                ⟨adjacent, Or.inl ⟨leftOutside, rfl⟩⟩, rfl, rfl⟩
          | inr rightInternal =>
              cases rightInternal with
              | inl rightCenter =>
                  exact (center_not_adjacent_outside object data leftOutside
                    adjacent.symm).elim
              | inr rightOutside =>
                  exact Or.inr ⟨.inr leftOutside, .inr rightOutside,
                    ⟨adjacent, Or.inl ⟨leftOutside, rfl⟩⟩, rfl, rfl⟩

noncomputable def reconstruction :
    PackedBoundariedGluing.glueGraph (piece object data) (outside object data)
      ≃g object.graph :=
  PackedBoundariedGluing.glueGraphIsoOfOwnedPartition
    (piece object data) (outside object data) object.graph
    (vertexEquiv object data) (pieceSound object data) (contextSound object data)
    (ambientOwned object data)

theorem piece_internalBaseline :
    (piece object data).InternalBaseline (inferInstance : FinEnum Boundary) 3 := by
  intro internal
  cases internal
  let boundaries : FinEnum Boundary := inferInstance
  let packed := PackedBoundariedGluing.Piece.pack boundaries (piece object data)
  change 3 ≤ packed.object.degree (.inr ⟨()⟩)
  let neighbors : Finset (Boundary ⊕ CenterVertex) :=
    {Sum.inl (⟨(0 : Fin 3)⟩ : Boundary),
      Sum.inl (⟨(1 : Fin 3)⟩ : Boundary),
      Sum.inl (⟨(2 : Fin 3)⟩ : Boundary)}
  have neighborsCard : neighbors.card = 3 := by simp [neighbors]
  rw [← neighborsCard]
  apply FiniteObject.card_le_degree_of_adjacent_finset
  intro vertex member
  simp only [neighbors, Finset.mem_insert, Finset.mem_singleton] at member
  rcases member with rfl | rfl | rfl
  · exact data.firstAdjacent
  · exact data.secondAdjacent
  · exact data.thirdAdjacent

theorem piece_preconnected : (piece object data).graph.Preconnected := by
  intro left right
  have toCenter : ∀ vertex : Boundary ⊕ CenterVertex,
      (piece object data).graph.Reachable vertex (.inr ⟨()⟩) := by
    intro vertex
    cases vertex with
    | inl index =>
        have adjacent : (piece object data).graph.Adj (.inl index) (.inr ⟨()⟩) :=
          (boundaryVertex_adjacent object data index).symm
        exact adjacent.reachable
    | inr internal => cases internal; exact .rfl
  exact (toCenter left).trans (toCenter right).symm

theorem boundary_owned_by_piece (left right : Boundary) :
    (piece object data).graph.Adj (.inl left) (.inl right) ↔
      object.graph.Adj (boundaryVertex object data left)
        (boundaryVertex object data right) := Iff.rfl

theorem boundary_center_owned_by_piece (index : Boundary) :
    (piece object data).graph.Adj (.inl index) (.inr ⟨()⟩) :=
  (boundaryVertex_adjacent object data index).symm

theorem piece_adj_iff_ambient (left right : Boundary ⊕ CenterVertex) :
    (piece object data).graph.Adj left right ↔
      object.graph.Adj (pieceVertex object data left)
        (pieceVertex object data right) := Iff.rfl

theorem boundary_not_owned_by_context (left right : Boundary) :
    ¬(outside object data).graph.Adj (.inl left) (.inl right) :=
  (outside object data).noBoundaryEdge left right

/-- The outside-complement scan tests at most four fixed support vertices for
each declared ambient vertex; all remaining ownership operations are proofs
on the fixed four-vertex piece. -/
def constructionChecks : Nat := 4 * object.input.vertices.card

theorem constructionChecks_linear :
    constructionChecks object ≤ 4 * object.input.vertices.card := le_rfl

end StructuralExhaustion.Graph.CubicStarDecomposition
