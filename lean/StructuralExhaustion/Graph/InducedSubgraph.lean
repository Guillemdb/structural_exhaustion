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

/-- The graph contains an induced vertex support whose internal minimum
degree reaches `bound`. -/
def HasInternalMinDegreeAtLeast (object : FiniteObject V) (bound : Nat) :
    Prop :=
  ∃ vertices : Finset V, bound ≤ (object.induceFinset vertices).minDegree

/-- Absence of an internal induced core at the declared degree threshold. -/
def InternalMinDegreeFree (object : FiniteObject V) (bound : Nat) : Prop :=
  ¬object.HasInternalMinDegreeAtLeast bound

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
