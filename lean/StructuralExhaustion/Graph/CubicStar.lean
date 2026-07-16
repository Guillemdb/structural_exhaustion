import StructuralExhaustion.Graph.RootIncidence

namespace StructuralExhaustion.Graph.CubicStar

open StructuralExhaustion

universe u

variable {V : Type u} (object : FiniteObject V)

/-- Exact three-neighbour geometry at a cubic center. -/
structure Data (center : V) where
  first : V
  second : V
  third : V
  firstAdjacent : object.graph.Adj center first
  secondAdjacent : object.graph.Adj center second
  thirdAdjacent : object.graph.Adj center third
  first_ne_second : first ≠ second
  first_ne_third : first ≠ third
  second_ne_third : second ≠ third
  degree_eq : object.degree center = 3

def ofAfterEdge {center : V} (incidence : RootIncidence.AfterEdge object center)
    (degree_eq : object.degree center = 3) : Data object center where
  first := incidence.predecessor
  second := incidence.leftNext
  third := incidence.rightNext
  firstAdjacent := incidence.predecessorAdjacent
  secondAdjacent := incidence.leftAdjacent
  thirdAdjacent := incidence.rightAdjacent
  first_ne_second := incidence.predecessor_ne_left
  first_ne_third := incidence.predecessor_ne_right
  second_ne_third := incidence.left_ne_right
  degree_eq := degree_eq

def ofRootDivergence {center : V}
    (divergence : RootIncidence.Divergence object center)
    (third : RootIncidence.Third object center divergence)
    (degree_eq : object.degree center = 3) : Data object center where
  first := divergence.leftNext
  second := divergence.rightNext
  third := third.hit.value
  firstAdjacent := divergence.leftAdjacent
  secondAdjacent := divergence.rightAdjacent
  thirdAdjacent := third.adjacent
  first_ne_second := divergence.distinct
  first_ne_third := third.ne_left.symm
  second_ne_third := third.ne_right.symm
  degree_eq := degree_eq

/-- Cubic geometry or the retained high-degree alternative. -/
inductive Result (center : V) : Type u where
  | cubic (data : Data object center)
  | high (degree_ge : 4 ≤ object.degree center)

/-- Consume the exact cubic/high result without erasing the high-degree
alternative. -/
def fromAfterEdgeBranch {center : V}
    (incidence : RootIncidence.AfterEdge object center) :
    RootIncidence.AfterEdgeBranch object center incidence →
      Result object center
  | .cubic degree_eq => .cubic (ofAfterEdge object incidence degree_eq)
  | .high degree_ge => .high degree_ge

/-- Root-divergence analogue of `fromAfterEdgeBranch`. -/
def fromRootBranch {center : V}
    (divergence : RootIncidence.Divergence object center) :
    RootIncidence.Branch object center divergence →
      Result object center
  | .cubic degree_eq third =>
      .cubic (ofRootDivergence object divergence third degree_eq)
  | .high degree_ge _third => .high degree_ge

namespace Data

variable {center : V} (data : Data object center)

noncomputable def boundary : Finset V := by
  letI : DecidableEq V := object.input.vertices.decEq
  exact {data.first, data.second, data.third}

noncomputable def support : Finset V := by
  letI : DecidableEq V := object.input.vertices.decEq
  exact insert center (boundary object data)

theorem boundary_card : (boundary object data).card = 3 := by
  letI : DecidableEq V := object.input.vertices.decEq
  simp [boundary, data.first_ne_second, data.first_ne_third,
    data.second_ne_third]

theorem center_not_mem_boundary : center ∉ boundary object data := by
  letI : DecidableEq V := object.input.vertices.decEq
  simp [boundary, data.firstAdjacent.ne, data.secondAdjacent.ne,
    data.thirdAdjacent.ne]

theorem support_card : (support object data).card = 4 := by
  letI : DecidableEq V := object.input.vertices.decEq
  rw [support, Finset.card_insert_of_notMem (center_not_mem_boundary object data),
    boundary_card object data]

noncomputable def fullNeighborFinset (center : V) : Finset V := by
  letI : Fintype V := @FinEnum.instFintype V object.input.vertices
  letI : DecidableRel object.graph.Adj := object.input.decideAdj
  exact object.graph.neighborFinset center

theorem mem_fullNeighborFinset_iff (center vertex : V) :
    vertex ∈ fullNeighborFinset object center ↔ object.graph.Adj center vertex := by
  letI : Fintype V := @FinEnum.instFintype V object.input.vertices
  letI : DecidableRel object.graph.Adj := object.input.decideAdj
  simp [fullNeighborFinset, SimpleGraph.mem_neighborFinset]

theorem boundary_subset_fullNeighborFinset :
    boundary object data ⊆ fullNeighborFinset object center := by
  letI : FinEnum V := object.input.vertices
  letI : DecidableEq V := object.input.vertices.decEq
  intro vertex member
  simp only [boundary, Finset.mem_insert, Finset.mem_singleton] at member
  rw [mem_fullNeighborFinset_iff object center]
  rcases member with rfl | rfl | rfl
  · exact data.firstAdjacent
  · exact data.secondAdjacent
  · exact data.thirdAdjacent

/-- Cubicity and the three distinct certified incidences exhaust the full
ambient neighbourhood. -/
theorem neighborFinset_eq_boundary :
    fullNeighborFinset object center = boundary object data := by
  letI : DecidableEq V := object.input.vertices.decEq
  symm
  apply Finset.eq_of_subset_of_card_le
    (boundary_subset_fullNeighborFinset object data)
  change object.degree center ≤ (boundary object data).card
  rw [data.degree_eq, boundary_card object data]

theorem adjacent_iff_mem_boundary (vertex : V) :
    object.graph.Adj center vertex ↔ vertex ∈ boundary object data := by
  letI : DecidableEq V := object.input.vertices.decEq
  rw [← mem_fullNeighborFinset_iff object center,
    neighborFinset_eq_boundary object data]

/-- Every support vertex has a one-edge-or-shorter center walk staying inside
the four-vertex support. -/
theorem support_root_walk {vertex : V} (member : vertex ∈ support object data) :
    ∃ walk : object.graph.Walk center vertex,
      ∀ point ∈ walk.support, point ∈ support object data := by
  letI : DecidableEq V := object.input.vertices.decEq
  rw [support, Finset.mem_insert] at member
  rcases member with rfl | boundaryMem
  · exact ⟨.nil, by simp [support]⟩
  · have adjacent := (adjacent_iff_mem_boundary object data vertex).2 boundaryMem
    refine ⟨.cons adjacent .nil, ?_⟩
    intro point pointMem
    simp only [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil,
      List.mem_cons] at pointMem
    rcases pointMem with rfl | (rfl | pointMem)
    · simp [support]
    · exact Finset.mem_insert_of_mem boundaryMem
    · simp at pointMem

/-- The four-vertex support is connected by walks that never leave it. -/
theorem support_connected {left right : V}
    (leftMem : left ∈ support object data)
    (rightMem : right ∈ support object data) :
    ∃ walk : object.graph.Walk left right,
      ∀ point ∈ walk.support, point ∈ support object data := by
  obtain ⟨leftWalk, leftSupport⟩ := support_root_walk object data leftMem
  obtain ⟨rightWalk, rightSupport⟩ := support_root_walk object data rightMem
  refine ⟨leftWalk.reverse.append rightWalk, ?_⟩
  intro point pointMem
  rw [SimpleGraph.Walk.support_append,
    SimpleGraph.Walk.support_reverse] at pointMem
  simp only [List.mem_append, List.mem_reverse] at pointMem
  rcases pointMem with pointMem | pointMem
  · exact leftSupport point pointMem
  · exact rightSupport point (List.mem_of_mem_tail pointMem)

/-- A finite ownership shape for later boundaried-piece construction.  The
three leaves are labelled boundary vertices and the center is the sole local
internal owner.  No context equivalence or replacement claim is included. -/
structure SwitchBoundaryShape where
  boundaryVertex : Fin 3 → V
  boundaryInjective : Function.Injective boundaryVertex
  internalVertex : V
  internal_eq : internalVertex = center
  boundaryAdjacent : ∀ index, object.graph.Adj internalVertex (boundaryVertex index)
  boundary_zero : boundaryVertex 0 = data.first
  boundary_one : boundaryVertex 1 = data.second
  boundary_two : boundaryVertex 2 = data.third
  ownsAllInternalIncidences :
    ∀ vertex, object.graph.Adj internalVertex vertex →
      ∃ index, boundaryVertex index = vertex

def switchBoundaryShape : data.SwitchBoundaryShape where
  boundaryVertex
    | 0 => data.first
    | 1 => data.second
    | 2 => data.third
  boundaryInjective := by
    intro left right equal
    fin_cases left <;> fin_cases right <;>
      simp_all [data.first_ne_second, data.first_ne_third,
        data.second_ne_third, Ne.symm data.first_ne_second,
        Ne.symm data.first_ne_third, Ne.symm data.second_ne_third]
  internalVertex := center
  internal_eq := rfl
  boundaryAdjacent := by
    intro index
    fin_cases index
    · exact data.firstAdjacent
    · exact data.secondAdjacent
    · exact data.thirdAdjacent
  boundary_zero := rfl
  boundary_one := rfl
  boundary_two := rfl
  ownsAllInternalIncidences := by
    letI : DecidableEq V := object.input.vertices.decEq
    intro vertex adjacent
    have boundaryMem := (adjacent_iff_mem_boundary object data vertex).1 adjacent
    simp only [boundary, Finset.mem_insert, Finset.mem_singleton] at boundaryMem
    rcases boundaryMem with rfl | rfl | rfl
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
    · exact ⟨2, rfl⟩

theorem switchBoundary_support_eq :
    let shape := switchBoundaryShape object data
    ({shape.internalVertex} ∪ Set.range shape.boundaryVertex) =
      (support object data : Set V) := by
  letI : DecidableEq V := object.input.vertices.decEq
  ext vertex
  simp only [Set.mem_union, Set.mem_singleton_iff, Set.mem_range,
    Finset.mem_coe, support, Finset.mem_insert, boundary,
    Finset.mem_singleton]
  constructor
  · rintro (rfl | ⟨index, rfl⟩)
    · exact Or.inl rfl
    · fin_cases index <;> simp [switchBoundaryShape]
  · rintro (rfl | rfl | rfl | rfl)
    · exact Or.inl rfl
    · exact Or.inr ⟨0, rfl⟩
    · exact Or.inr ⟨1, rfl⟩
    · exact Or.inr ⟨2, rfl⟩

/-- Constructing the star from already certified incidences only projects
proof data and performs no primitive finite scan. -/
def constructionChecks : Nat := 0

/-- Materializing `fullNeighborFinset` uses Mathlib's ambient finite filter;
charge one adjacency decision per vertex in the declared ambient order. -/
def ambientNeighborChecks : Nat := object.input.vertices.card

theorem ambientNeighborChecks_eq_order :
    ambientNeighborChecks object = object.input.vertices.card := rfl

end Data

end StructuralExhaustion.Graph.CubicStar
