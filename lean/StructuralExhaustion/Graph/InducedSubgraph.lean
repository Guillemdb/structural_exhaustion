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

end StructuralExhaustion.Graph.FiniteObject
