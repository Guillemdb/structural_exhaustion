import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import StructuralExhaustion.CT12.DisjointPacking
import StructuralExhaustion.Graph.InducedPath
import StructuralExhaustion.Graph.InducedSubgraph

namespace StructuralExhaustion.Graph.InducedPathPacking

open StructuralExhaustion

universe u uAmbient uBranch

variable {V : Type u}

/-!
# Maximum vertex-disjoint induced-path packings

An item is a literal Mathlib induced embedding of `pathGraph order`.  The
generic finite-disjoint-packing theorem selects a maximum support-disjoint
family; CT12 then peels only that selected family.  No definition here scans
the embedding type or a powerset of packings.
-/

/-- One labelled induced path window in a finite host graph. -/
abbrev Window (object : FiniteObject V) (order : Nat) :=
  SimpleGraph.pathGraph order ↪g object.graph

/-- Vertex support of one induced path embedding. -/
noncomputable def support (object : FiniteObject V) (order : Nat)
    (window : Window object order) : Finset V := by
  letI : FinEnum V := object.input.vertices
  letI : DecidableEq V := object.input.vertices.decEq
  exact Finset.univ.image window

theorem mem_support_iff (object : FiniteObject V) (order : Nat)
    (window : Window object order) (vertex : V) :
    vertex ∈ support object order window ↔
      ∃ index : Fin order, window index = vertex := by
  letI : FinEnum V := object.input.vertices
  letI : DecidableEq V := object.input.vertices.decEq
  simp [support]

theorem support_card (object : FiniteObject V) (order : Nat)
    (window : Window object order) :
    (support object order window).card = order := by
  letI : FinEnum V := object.input.vertices
  letI : DecidableEq V := object.input.vertices.decEq
  rw [support, Finset.card_image_of_injective Finset.univ window.injective]
  simp

/-- Static CT12 packing profile.  Positivity supplies a representative vertex
for every nonempty path support. -/
noncomputable def profile (object : FiniteObject V) (order : Nat)
    (positive : 0 < order) :
    CT12.DisjointPacking.Profile V (Window object order) where
  vertices := object.input.vertices
  finiteItems := by
    letI : FinEnum V := object.input.vertices
    letI : Fintype V := inferInstance
    infer_instance
  support := support object order
  representative := fun window => window ⟨0, positive⟩
  representative_mem := by
    intro window
    exact (mem_support_iff object order window _).2
      ⟨⟨0, positive⟩, rfl⟩

/-- The maximum packing selected by the reusable core theorem. -/
abbrev Packing (object : FiniteObject V) (order : Nat)
    (positive : 0 < order) :=
  (profile object order positive).Packing

/-- Selected labelled windows in the exact CT12 peeling order. -/
noncomputable def windows (object : FiniteObject V) (order : Nat)
    (positive : 0 < order) : List (Window object order) :=
  (profile object order positive).values

/-- The packed-window count. -/
noncomputable def packingNumber (object : FiniteObject V) (order : Nat)
    (positive : 0 < order) : Nat :=
  (windows object order positive).length

/-- Vertices covered by the selected maximum packing. -/
noncomputable def coveredVertices (object : FiniteObject V) (order : Nat)
    (positive : 0 < order) : Finset V := by
  classical
  exact (profile object order positive).maximum.1.biUnion
    (support object order)

/-- The vertex complement of the selected packing. -/
noncomputable def remainderVertices (object : FiniteObject V) (order : Nat)
    (positive : 0 < order) : Finset V := by
  letI : FinEnum V := object.input.vertices
  letI : DecidableEq V := object.input.vertices.decEq
  exact Finset.univ \ coveredVertices object order positive

/-- The actual finite induced graph left after deleting every packed support. -/
noncomputable def remainder (object : FiniteObject V) (order : Nat)
    (positive : 0 < order) :
    FiniteObject {vertex : V // vertex ∈
      remainderVertices object order positive} :=
  object.induceFinset (remainderVertices object order positive)

/-- Canonical graph embedding of the remainder into the host. -/
noncomputable def remainderEmbedding (object : FiniteObject V)
    (order : Nat) (positive : 0 < order) :
    (remainder object order positive).graph ↪g object.graph :=
  object.induceFinsetEmbedding (remainderVertices object order positive)

theorem mem_coveredVertices_iff (object : FiniteObject V) (order : Nat)
    (positive : 0 < order) (vertex : V) :
    vertex ∈ coveredVertices object order positive ↔
      ∃ window ∈ windows object order positive,
        vertex ∈ support object order window := by
  classical
  simp only [coveredVertices, Finset.mem_biUnion, windows]
  constructor
  · rintro ⟨window, windowMem, vertexMem⟩
    exact ⟨window,
      ((profile object order positive).mem_values_iff window).2 windowMem,
      vertexMem⟩
  · rintro ⟨window, windowMem, vertexMem⟩
    exact ⟨window,
      ((profile object order positive).mem_values_iff window).1 windowMem,
      vertexMem⟩

/-- Exact cardinality of the packed vertex set. -/
theorem coveredVertices_card (object : FiniteObject V) (order : Nat)
    (positive : 0 < order) :
    (coveredVertices object order positive).card =
      order * packingNumber object order positive := by
  classical
  change (((profile object order positive).maximum.1.biUnion
    (profile object order positive).support).card) = _
  rw [Finset.card_biUnion
    (profile object order positive).maximum.2]
  change (∑ window ∈ (profile object order positive).maximum.1,
    (support object order window).card) = _
  simp_rw [support_card object order]
  simp [packingNumber, windows,
    (profile object order positive).values_length, Nat.mul_comm]

/-- Exact packed/remainder partition identity. -/
theorem remainder_partition (object : FiniteObject V) (order : Nat)
    (positive : 0 < order) :
    (remainderVertices object order positive).card +
      order * packingNumber object order positive =
        object.input.vertices.card := by
  letI : FinEnum V := object.input.vertices
  letI : DecidableEq V := object.input.vertices.decEq
  have partition := Finset.card_sdiff_add_card_eq_card
    (show coveredVertices object order positive ⊆ (Finset.univ : Finset V)
      from Finset.subset_univ _)
  rw [← coveredVertices_card object order positive]
  simpa [remainderVertices, FinEnum.card_eq_fintypeCard] using partition

/-- Subtraction form of the exact packed/remainder partition. -/
theorem remainder_card_eq_sub (object : FiniteObject V) (order : Nat)
    (positive : 0 < order) :
    (remainderVertices object order positive).card =
      object.input.vertices.card -
        order * packingNumber object order positive := by
  have partition := remainder_partition object order positive
  omega

/-- A coverage bound from the preceding packing-density branch transfers
exactly to a lower bound on the complementary remainder.  This is local
arithmetic on the already selected packing; it performs no search. -/
theorem remainder_card_ge_of_coverage_add_floor_le
    (object : FiniteObject V) (order : Nat) (positive : 0 < order)
    (floor : Nat)
    (coverage : order * packingNumber object order positive + floor ≤
      object.input.vertices.card) :
    floor ≤ (remainderVertices object order positive).card := by
  have partition := remainder_partition object order positive
  omega

/-- An upper bound on the number of selected packed items gives the exact
complementary remainder floor.  This is the direct local handoff used after a
packing-density branch. -/
theorem remainder_card_ge_of_packingNumber_le
    (object : FiniteObject V) (order : Nat) (positive : 0 < order)
    (windowCeiling : Nat)
    (packingBound : packingNumber object order positive ≤ windowCeiling) :
    object.input.vertices.card - order * windowCeiling ≤
      (remainderVertices object order positive).card := by
  rw [remainder_card_eq_sub object order positive]
  exact Nat.sub_le_sub_left
    (Nat.mul_le_mul_left order packingBound)
    object.input.vertices.card

/-- In particular, `order * p ≤ |V|`. -/
theorem packing_vertices_bound (object : FiniteObject V) (order : Nat)
    (positive : 0 < order) :
    order * packingNumber object order positive ≤
      object.input.vertices.card := by
  have partition := remainder_partition object order positive
  omega

/-- Maximum cardinality among every other family of pairwise support-disjoint
induced path embeddings. -/
theorem maximum (object : FiniteObject V) (order : Nat)
    (positive : 0 < order) (other : Packing object order positive) :
    other.1.card ≤ packingNumber object order positive := by
  change other.1.card ≤ (profile object order positive).values.length
  rw [(profile object order positive).values_length]
  exact (profile object order positive).maximum_spec other

/-- Maximality in the form used by remainder arguments: every induced path
window meets a packed window. -/
theorem saturated (object : FiniteObject V) (order : Nat)
    (positive : 0 < order) (window : Window object order) :
    ∃ selected ∈ windows object order positive,
      ¬Disjoint (support object order window)
        (support object order selected) :=
  (profile object order positive).values_saturated window

/-- The complement of a maximum induced-path packing is induced-path-free. -/
theorem remainder_free (object : FiniteObject V) (order : Nat)
    (positive : 0 < order) :
    InducedPathFree (remainder object order positive).graph order := by
  classical
  letI : FinEnum V := object.input.vertices
  intro realization
  rcases realization with ⟨remainderWindow⟩
  let lifted : Window object order :=
    (remainderEmbedding object order positive).comp remainderWindow
  rcases saturated object order positive lifted with
    ⟨selected, selectedMem, intersects⟩
  apply intersects
  rw [Finset.disjoint_left]
  intro vertex vertexLifted vertexSelected
  rcases (mem_support_iff object order lifted vertex).1 vertexLifted with
    ⟨index, imageEq⟩
  have remainderMem := (remainderWindow index).property
  have notCovered : vertex ∉ coveredVertices object order positive := by
    have imageValue : lifted index = (remainderWindow index).1 := rfl
    rw [imageValue] at imageEq
    have remainderParts :
        (remainderWindow index).1 ∈
          (Finset.univ : Finset V) \
            coveredVertices object order positive := by
      exact remainderMem
    have sourceNotCovered := (Finset.mem_sdiff.mp remainderParts).2
    rw [imageEq] at sourceNotCovered
    exact sourceNotCovered
  have covered : vertex ∈ coveredVertices object order positive :=
    (mem_coveredVertices_iff object order positive vertex).2
      ⟨selected, selectedMem, vertexSelected⟩
  exact notCovered covered

/-- Induced-path-freeness is inherited by every induced subgraph of the
remainder, hence in particular by every connected component. -/
theorem remainder_induce_free (object : FiniteObject V) (order : Nat)
    (positive : 0 < order)
    (vertices : Set {vertex : V // vertex ∈
      remainderVertices object order positive}) :
    InducedPathFree
      ((remainder object order positive).graph.induce vertices) order := by
  intro realization
  rcases realization with ⟨window⟩
  exact remainder_free object order positive
    ⟨(SimpleGraph.Embedding.induce vertices).comp window⟩

/-- Complete graph-level CT12 packing stage. -/
structure VerifiedStage {P : Core.Problem.{uAmbient, uBranch}}
    (object : FiniteObject V) (order : Nat) (positive : 0 < order)
    (context : Core.BranchContext P) : Prop where
  audit : (profile object order positive).VerifiedStage context
  coveredCard : (coveredVertices object order positive).card =
    order * packingNumber object order positive
  partition : (remainderVertices object order positive).card +
    order * packingNumber object order positive = object.input.vertices.card
  remainderFree :
    InducedPathFree (remainder object order positive).graph order
  hereditaryFree : ∀ vertices : Set {vertex : V // vertex ∈
      remainderVertices object order positive},
    InducedPathFree
      ((remainder object order positive).graph.induce vertices) order

/-- Construct all packing, execution, and remainder conclusions from the
finite host object. -/
noncomputable def verifiedStage {P : Core.Problem.{uAmbient, uBranch}}
    (object : FiniteObject V) (order : Nat) (positive : 0 < order)
    (context : Core.BranchContext P) :
    VerifiedStage object order positive context where
  audit := (profile object order positive).verifiedStage context
  coveredCard := coveredVertices_card object order positive
  partition := remainder_partition object order positive
  remainderFree := remainder_free object order positive
  hereditaryFree := remainder_induce_free object order positive

/-- A previously verified induced path forces the selected maximum packing to
contain at least one window. -/
theorem windows_nonempty_of_realization (object : FiniteObject V)
    (order : Nat) (positive : 0 < order)
    (realization : HasInducedPath object.graph order) :
    windows object order positive ≠ [] := by
  rcases realization with ⟨window⟩
  exact (profile object order positive).values_nonempty_of_item window

end StructuralExhaustion.Graph.InducedPathPacking
