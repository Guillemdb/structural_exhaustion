import StructuralExhaustion.Graph.FiniteObject

namespace StructuralExhaustion.Graph.FiniteObject

open StructuralExhaustion

universe u

variable {V : Type u}

/-!
# Explicit finite induced subgraphs

The mathematical graph is Mathlib's `SimpleGraph.induce`.  This wrapper only
restricts an existing finite vertex schedule to a declared finset and keeps
the canonical embedding back into the original graph.
-/

/-- Restrict a finite graph object to a finite set of vertices. -/
def induceFinset (object : FiniteObject V) (vertices : Finset V) :
    FiniteObject {vertex : V // vertex ∈ vertices} where
  graph := object.graph.induce {vertex | vertex ∈ vertices}
  input := {
    vertices := Core.Enumeration.subtype object.input.vertices
      (fun vertex => vertex ∈ vertices) (by
        letI : DecidableEq V := object.input.vertices.decEq
        infer_instance)
    decideAdj := by
      letI : DecidableRel object.graph.Adj := object.input.decideAdj
      infer_instance
  }

/-- Canonical induced embedding from a restricted finite object into its
source graph. -/
def induceFinsetEmbedding (object : FiniteObject V) (vertices : Finset V) :
    (object.induceFinset vertices).graph ↪g object.graph :=
  SimpleGraph.Embedding.induce {vertex | vertex ∈ vertices}

@[simp]
theorem induceFinsetEmbedding_apply (object : FiniteObject V)
    (vertices : Finset V) (vertex : {vertex : V // vertex ∈ vertices}) :
    object.induceFinsetEmbedding vertices vertex = vertex.1 :=
  rfl

@[simp]
theorem induceFinset_vertexCount (object : FiniteObject V)
    (vertices : Finset V) :
    (object.induceFinset vertices).input.vertices.card = vertices.card := by
  letI : FinEnum {vertex : V // vertex ∈ vertices} :=
    (object.induceFinset vertices).input.vertices
  rw [FinEnum.card_eq_fintypeCard]
  exact Fintype.card_coe vertices

/-- Inducing on a support does not change the degree of a supported vertex
when every ambient neighbour of that vertex remains in the support.  The
wrapper fixes the finite instances on both sides, so consumers need not
reconcile two extensionally equal `Fintype` enumerations. -/
theorem induceFinset_degree_of_neighborSet_subset
    (object : FiniteObject V) (vertices : Finset V)
    (vertex : {value : V // value ∈ vertices})
    (closed : object.graph.neighborSet vertex.1 ⊆ (vertices : Set V)) :
    (object.induceFinset vertices).degree vertex = object.degree vertex.1 := by
  rw [(object.induceFinset vertices).degree_eq_ncard_neighborSet,
    object.degree_eq_ncard_neighborSet]
  apply Set.ncard_congr (fun neighbor _ ↦ neighbor.1)
  · intro neighbor adjacent
    exact adjacent
  · intro left right _ _ equal
    exact Subtype.ext equal
  · intro neighbor adjacent
    let supported : {value : V // value ∈ vertices} :=
      ⟨neighbor, closed adjacent⟩
    exact ⟨supported, adjacent, rfl⟩

/-- Deleting one supported vertex after inducing is canonically the same as
inducing once on the erased support. -/
noncomputable def induceFinsetEraseEquiv (object : FiniteObject V)
    (support : Finset V) (vertex : V) (member : vertex ∈ support) :
    {inner : {value : V // value ∈ support} //
        inner ∈ ({(⟨vertex, member⟩ : {value : V // value ∈ support})}ᶜ :
          Set {value : V // value ∈ support})} ≃
      {value : V // value ∈
        @Finset.erase V object.input.vertices.decEq support vertex} where
  toFun inner := by
    letI : DecidableEq V := object.input.vertices.decEq
    have neSubtype : inner.1 ≠ ⟨vertex, member⟩ := by
      intro equal
      exact inner.2 (by simp [equal])
    have neVertex : inner.1.1 ≠ vertex := by
      intro equal
      exact neSubtype (Subtype.ext equal)
    exact ⟨inner.1.1, Finset.mem_erase.mpr ⟨neVertex, inner.1.2⟩⟩
  invFun value := by
    letI : DecidableEq V := object.input.vertices.decEq
    have erased := Finset.mem_erase.mp value.2
    refine ⟨⟨value.1, erased.2⟩, ?_⟩
    simpa using (fun equal : (⟨value.1, erased.2⟩ :
      {value : V // value ∈ support}) = ⟨vertex, member⟩ =>
        erased.1 (congrArg Subtype.val equal))
  left_inv inner := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  right_inv value := by
    apply Subtype.ext
    rfl

/-- Graph isomorphism implementing the erase-after-induce identity. -/
noncomputable def induceFinsetEraseIso (object : FiniteObject V)
    (support : Finset V) (vertex : V) (member : vertex ∈ support) :
    (object.induceFinset support).graph.induce
        ({(⟨vertex, member⟩ : {value : V // value ∈ support})}ᶜ :
          Set {value : V // value ∈ support}) ≃g
      (object.induceFinset
        (@Finset.erase V object.input.vertices.decEq support vertex)).graph where
  __ := object.induceFinsetEraseEquiv support vertex member
  map_rel_iff' := by
    intro left right
    rfl

/-- Exact edge recurrence for one local induced-support peeling step. -/
theorem edgeCount_induceFinset_erase_add_degree
    (object : FiniteObject V) (support : Finset V) (vertex : V)
    (member : vertex ∈ support) :
    (object.induceFinset
        (@Finset.erase V object.input.vertices.decEq support vertex)).edgeCount +
        (object.induceFinset support).degree ⟨vertex, member⟩ =
      (object.induceFinset support).edgeCount := by
  let current := object.induceFinset support
  let selected : {value : V // value ∈ support} := ⟨vertex, member⟩
  let remaining := object.induceFinset
    (@Finset.erase V object.input.vertices.decEq support vertex)
  letI : FinEnum {value : V // value ∈ support} := current.input.vertices
  letI : Fintype {value : V // value ∈ support} :=
    @FinEnum.instFintype _ current.input.vertices
  letI : DecidableEq {value : V // value ∈ support} :=
    current.input.vertices.decEq
  letI : DecidableRel current.graph.Adj := current.input.decideAdj
  letI : FinEnum {value : V // value ∈
      @Finset.erase V object.input.vertices.decEq support vertex} :=
    remaining.input.vertices
  letI : Fintype {value : V // value ∈
      @Finset.erase V object.input.vertices.decEq support vertex} :=
    @FinEnum.instFintype _ remaining.input.vertices
  letI : DecidableRel remaining.graph.Adj := remaining.input.decideAdj
  have isoCard :
      (current.graph.induce
        ({selected}ᶜ : Set {value : V // value ∈ support})).edgeFinset.card =
        remaining.graph.edgeFinset.card := by
    exact (object.induceFinsetEraseIso support vertex member).card_edgeFinset_eq
  have deletedCard :
      (current.graph.induce
        ({selected}ᶜ : Set {value : V // value ∈ support})).edgeFinset.card =
        (current.graph.deleteIncidenceSet selected).edgeFinset.card :=
    current.graph.card_edgeFinset_induce_compl_singleton selected
  have deleteEq :
      (current.graph.deleteIncidenceSet selected).edgeFinset.card =
        current.graph.edgeFinset.card - current.graph.degree selected :=
    current.graph.card_edgeFinset_deleteIncidenceSet selected
  have degreeLe : current.graph.degree selected ≤ current.graph.edgeFinset.card :=
    current.graph.degree_le_card_edgeFinset selected
  have recurrence : remaining.graph.edgeFinset.card +
      current.graph.degree selected = current.graph.edgeFinset.card := by
    rw [← isoCard, deletedCard, deleteEq]
    exact Nat.sub_add_cancel degreeLe
  simpa [FiniteObject.edgeCount, FiniteObject.degree, current, remaining,
    selected] using recurrence

/-- Edge-count form of the full-support induced-graph identity. -/
@[simp]
theorem induceFinset_univ_edgeCount (object : FiniteObject V) :
    (object.induceFinset object.vertexFinset).edgeCount =
      object.edgeCount := by
  letI : FinEnum V := object.input.vertices
  letI : Fintype V := @FinEnum.instFintype _ object.input.vertices
  letI : DecidableRel object.graph.Adj := object.input.decideAdj
  let induced := object.induceFinset object.vertexFinset
  letI : FinEnum {vertex : V // vertex ∈ object.vertexFinset} :=
    induced.input.vertices
  letI : Fintype {vertex : V // vertex ∈ object.vertexFinset} :=
    @FinEnum.instFintype _ induced.input.vertices
  letI : DecidableRel induced.graph.Adj := induced.input.decideAdj
  let iso : induced.graph ≃g object.graph := {
    toFun vertex := vertex.1
    invFun vertex := ⟨vertex, object.mem_vertexFinset vertex⟩
    left_inv vertex := Subtype.ext rfl
    right_inv _vertex := rfl
    map_rel_iff' := by
      intro left right
      rfl
  }
  simpa [FiniteObject.edgeCount, induced] using iso.card_edgeFinset_eq

/-- Vertex degrees are unchanged by the full-support induced restriction. -/
@[simp]
theorem induceFinset_univ_degree (object : FiniteObject V) (vertex : V) :
    (object.induceFinset object.vertexFinset).degree
        ⟨vertex, object.mem_vertexFinset vertex⟩ =
      object.degree vertex := by
  let induced := object.induceFinset object.vertexFinset
  let selected : {value : V // value ∈ object.vertexFinset} :=
    ⟨vertex, object.mem_vertexFinset vertex⟩
  let iso : induced.graph ≃g object.graph := {
    toFun value := value.1
    invFun value := ⟨value, object.mem_vertexFinset value⟩
    left_inv value := Subtype.ext rfl
    right_inv _value := rfl
    map_rel_iff' := by
      intro left right
      rfl
  }
  rw [induced.degree_eq_ncard_neighborSet,
    object.degree_eq_ncard_neighborSet]
  exact Set.ncard_congr' (iso.mapNeighborSet selected)

/-- The graph contains an induced vertex support whose internal minimum
degree reaches `bound`. -/
def HasInternalMinDegreeAtLeast (object : FiniteObject V) (bound : Nat) :
    Prop :=
  ∃ vertices : Finset V, bound ≤ (object.induceFinset vertices).minDegree

/-- Absence of an internal induced core at the declared degree threshold. -/
def InternalMinDegreeFree (object : FiniteObject V) (bound : Nat) : Prop :=
  ¬object.HasInternalMinDegreeAtLeast bound

/-- The vertex-count bound alone excludes an induced core whose minimum
degree reaches that count.  This is the finite simple-graph base case used by
small transfer examples; it performs no graph-universe search. -/
theorem internalMinDegreeFree_of_vertexCount_le (object : FiniteObject V)
    {bound : Nat} (positive : 0 < bound)
    (countLe : object.input.vertices.card ≤ bound) :
    object.InternalMinDegreeFree bound := by
  rintro ⟨support, minimum⟩
  let induced := object.induceFinset support
  by_cases supportEmpty : support = ∅
  · subst support
    simp [FiniteObject.minDegree, FiniteObject.induceFinset] at minimum
    exact (Nat.ne_of_gt positive) minimum
  · have supportNonempty : support.Nonempty :=
      Finset.nonempty_iff_ne_empty.mpr supportEmpty
    letI : Nonempty {vertex : V // vertex ∈ support} :=
      Finset.nonempty_coe_sort.mpr supportNonempty
    letI : FinEnum {vertex : V // vertex ∈ support} :=
      induced.input.vertices
    letI : Fintype {vertex : V // vertex ∈ support} :=
      @FinEnum.instFintype _ induced.input.vertices
    letI : DecidableRel induced.graph.Adj := induced.input.decideAdj
    let vertex : {vertex : V // vertex ∈ support} := Classical.choice inferInstance
    have minimumLe : bound ≤ induced.degree vertex :=
      minimum.trans (induced.minDegree_le_degree vertex)
    have degreeLt : induced.degree vertex < support.card := by
      simpa [FiniteObject.degree, FiniteObject.induceFinset,
        FinEnum.card_eq_fintypeCard] using
        induced.graph.degree_lt_card_verts vertex
    letI : FinEnum V := object.input.vertices
    letI : Fintype V := @FinEnum.instFintype _ object.input.vertices
    have supportLe : support.card ≤ object.input.vertices.card := by
      simpa [FinEnum.card_eq_fintypeCard] using Finset.card_le_univ support
    omega

/-! ## Arbitrary finite internal subgraphs -/

/-- An ordinary finite subgraph supported on an explicit vertex subset.

Unlike `induceFinset`, `graph` may omit ambient edges.  The inclusion field is
the complete condition relating it to the host.  Keeping the finite support
explicit lets graph applications state manuscript clauses about arbitrary
subgraphs without introducing a global subgraph enumeration. -/
structure InternalSubgraph (object : FiniteObject V) where
  vertices : Finset V
  graph : SimpleGraph {vertex : V // vertex ∈ vertices}
  decideAdj : DecidableRel graph.Adj
  graph_le : graph ≤ (object.induceFinset vertices).graph

namespace InternalSubgraph

/-- Minimum degree of an ordinary internal subgraph, evaluated with the
host-induced support enumeration. -/
def minDegree {object : FiniteObject V}
    (subgraph : InternalSubgraph object) : Nat :=
  @SimpleGraph.minDegree _ subgraph.graph
    (@FinEnum.instFintype _
      (object.induceFinset subgraph.vertices).input.vertices)
    subgraph.decideAdj

/-- Adding every ambient edge on the same support cannot lower minimum
degree. -/
theorem minDegree_le_induced {object : FiniteObject V}
    (subgraph : InternalSubgraph object) :
    subgraph.minDegree ≤
      (object.induceFinset subgraph.vertices).minDegree := by
  let induced := object.induceFinset subgraph.vertices
  let enumeration : FinEnum {vertex : V // vertex ∈ subgraph.vertices} :=
    induced.input.vertices
  have monotone :
      @SimpleGraph.minDegree _ subgraph.graph
          (@FinEnum.instFintype _ enumeration) subgraph.decideAdj ≤
        @SimpleGraph.minDegree _ induced.graph
          (@FinEnum.instFintype _ enumeration) induced.input.decideAdj :=
    @SimpleGraph.minDegree_le_minDegree _ subgraph.graph
      (@FinEnum.instFintype _ enumeration) induced.graph
      subgraph.decideAdj induced.input.decideAdj subgraph.graph_le
  simpa only [InternalSubgraph.minDegree, FiniteObject.minDegree,
    induced, enumeration] using monotone

end InternalSubgraph

/-- The host contains an arbitrary finite internal subgraph whose minimum
degree reaches `bound`. -/
def HasInternalSubgraphMinDegreeAtLeast (object : FiniteObject V)
    (bound : Nat) : Prop :=
  ∃ subgraph : InternalSubgraph object, bound ≤ subgraph.minDegree

/-- An ordinary internal core yields the induced core on the same support. -/
theorem hasInternalMinDegreeAtLeast_of_internalSubgraph
    (object : FiniteObject V) (bound : Nat) :
    object.HasInternalSubgraphMinDegreeAtLeast bound →
      object.HasInternalMinDegreeAtLeast bound := by
  rintro ⟨subgraph, minimumDegree⟩
  exact ⟨subgraph.vertices,
    minimumDegree.trans subgraph.minDegree_le_induced⟩

/-- Excluding induced cores excludes every ordinary finite subgraph at the
same minimum-degree threshold. -/
theorem internalSubgraphMinDegreeFree_of_internalMinDegreeFree
    (object : FiniteObject V) (bound : Nat)
    (free : object.InternalMinDegreeFree bound) :
    ¬object.HasInternalSubgraphMinDegreeAtLeast bound :=
  fun internalSubgraph =>
    free (object.hasInternalMinDegreeAtLeast_of_internalSubgraph bound
      internalSubgraph)

/-! ## Heredity under a second induced restriction -/

/-- Flatten a finite set of vertices of an induced object back to the host
vertex type. -/
noncomputable def flattenInducedVertices (_object : FiniteObject V)
    (support : Finset V)
    (vertices : Finset {vertex : V // vertex ∈ support}) : Finset V :=
  vertices.map (Function.Embedding.subtype fun vertex => vertex ∈ support)

/-- The natural equivalence between a twice-restricted vertex type and its
flattened once-restricted form. -/
noncomputable def flattenInducedEquiv (object : FiniteObject V)
    (support : Finset V)
    (vertices : Finset {vertex : V // vertex ∈ support}) :
    {vertex : {vertex : V // vertex ∈ support} // vertex ∈ vertices} ≃
      {vertex : V // vertex ∈
        object.flattenInducedVertices support vertices} :=
  Equiv.ofBijective
    (fun vertex => ⟨vertex.1.1, by
      unfold flattenInducedVertices
      exact Finset.mem_map.mpr ⟨vertex.1, vertex.2, rfl⟩⟩)
    (by
      constructor
      · intro left right equal
        apply Subtype.ext
        apply Subtype.ext
        exact congrArg (fun vertex => vertex.1) equal
      · intro vertex
        unfold flattenInducedVertices at vertex
        obtain ⟨source, member, value⟩ := Finset.mem_map.mp vertex.2
        refine ⟨⟨source, member⟩, ?_⟩
        apply Subtype.ext
        exact value)

/-- Restricting an induced graph a second time is isomorphic to inducing the
host graph on the flattened support. -/
noncomputable def flattenInducedIso (object : FiniteObject V)
    (support : Finset V)
    (vertices : Finset {vertex : V // vertex ∈ support}) :
    ((object.induceFinset support).induceFinset vertices).graph ≃g
      (object.induceFinset
        (object.flattenInducedVertices support vertices)).graph where
  __ := object.flattenInducedEquiv support vertices
  map_rel_iff' := by
    intro left right
    rfl

/-- Internal-core freeness is hereditary under restriction to any explicit
finite induced support. -/
theorem internalMinDegreeFree_induceFinset (object : FiniteObject V)
    (support : Finset V) (bound : Nat)
    (free : object.InternalMinDegreeFree bound) :
    (object.induceFinset support).InternalMinDegreeFree bound := by
  intro restrictedCore
  rcases restrictedCore with ⟨vertices, minimum⟩
  let inner := (object.induceFinset support).induceFinset vertices
  let outerVertices := object.flattenInducedVertices support vertices
  let outer := object.induceFinset outerVertices
  let iso := object.flattenInducedIso support vertices
  apply free
  refine ⟨outerVertices, ?_⟩
  letI : FinEnum {vertex : {vertex : V // vertex ∈ support} //
      vertex ∈ vertices} := inner.input.vertices
  letI : DecidableRel inner.graph.Adj := inner.input.decideAdj
  letI : FinEnum {vertex : V // vertex ∈ outerVertices} :=
    outer.input.vertices
  letI : DecidableRel outer.graph.Adj := outer.input.decideAdj
  by_cases verticesNonempty : vertices.Nonempty
  · let sourceVertex := verticesNonempty.choose
    let source : {vertex : {vertex : V // vertex ∈ support} //
        vertex ∈ vertices} := ⟨sourceVertex, verticesNonempty.choose_spec⟩
    letI : Nonempty {vertex : V // vertex ∈ outerVertices} :=
      ⟨iso source⟩
    apply outer.le_minDegree_of_forall_le_degree bound
    intro vertex
    let source := iso.symm vertex
    have sourceLower : bound ≤ inner.degree source :=
      minimum.trans (inner.minDegree_le_degree source)
    have degreeEq : outer.degree (iso source) = inner.degree source := by
      rw [outer.degree_eq_ncard_neighborSet,
        inner.degree_eq_ncard_neighborSet]
      exact (Set.ncard_congr' (iso.mapNeighborSet source)).symm
    have mapped : iso source = vertex := iso.apply_symm_apply vertex
    rw [mapped] at degreeEq
    rw [degreeEq]
    exact sourceLower
  · have verticesEmpty : vertices = ∅ := Finset.not_nonempty_iff_eq_empty.mp
      verticesNonempty
    subst vertices
    simpa [inner, outer, outerVertices, flattenInducedVertices,
      FiniteObject.minDegree] using minimum

end StructuralExhaustion.Graph.FiniteObject
