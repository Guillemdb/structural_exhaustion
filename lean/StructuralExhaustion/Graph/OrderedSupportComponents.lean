import StructuralExhaustion.Graph.InducedSubgraph
import StructuralExhaustion.Graph.NegativeSupportHandoff

namespace StructuralExhaustion.Graph.OrderedSupportComponents

open StructuralExhaustion

universe u

/-!
# Ordered connected components of one declared support

This file decomposes one explicit finite vertex support by scanning its
vertices in the order inherited from `FiniteObject.input.vertices`.  It does
not enumerate ambient graphs, subsets, paths, or Boolean assignments.  A
component is inserted at its first supported vertex and later repetitions are
removed by `List.eraseDups`.
-/

variable {V : Type u}

/-- The induced graph on the supplied literal support. -/
abbrev inducedObject (object : FiniteObject V) (support : Finset V) :=
  object.induceFinset support

/-- The finite connected-component type of the induced support graph. -/
abbrev Component (object : FiniteObject V) (support : Finset V) :=
  (inducedObject object support).graph.ConnectedComponent

/-- The component containing a supported vertex. -/
def vertexComponent (object : FiniteObject V) (support : Finset V)
    (vertex : {value : V // value ∈ support}) : Component object support :=
  (inducedObject object support).graph.connectedComponentMk vertex

/-- Components in first-occurrence order along the declared support scan. -/
noncomputable def order (object : FiniteObject V) (support : Finset V) :
    List (Component object support) := by
  classical
  exact ((inducedObject object support).input.vertices.orderedValues.map
    (vertexComponent object support)).dedup

/-- Literal ambient vertices belonging to one induced component. -/
noncomputable def vertices (object : FiniteObject V) (support : Finset V)
    (component : Component object support) : Finset V := by
  classical
  exact ((inducedObject object support).vertexFinset.filter fun vertex =>
    vertexComponent object support vertex = component).image Subtype.val

@[simp]
theorem mem_vertices_iff (object : FiniteObject V) (support : Finset V)
    (component : Component object support) (vertex : V) :
    vertex ∈ vertices object support component ↔
      ∃ member : vertex ∈ support,
        vertexComponent object support ⟨vertex, member⟩ = component := by
  classical
  unfold vertices
  constructor
  · intro member
    rcases Finset.mem_image.mp member with ⟨supported, supportedMem, rfl⟩
    exact ⟨supported.2, (Finset.mem_filter.mp supportedMem).2⟩
  · rintro ⟨member, equal⟩
    apply Finset.mem_image.mpr
    refine ⟨⟨vertex, member⟩, ?_, rfl⟩
    apply Finset.mem_filter.mpr
    exact ⟨(inducedObject object support).mem_vertexFinset _, equal⟩

/-- Every listed component has at least one literal supported vertex. -/
theorem vertices_nonempty_of_mem_order (object : FiniteObject V)
    (support : Finset V) {component : Component object support}
    (member : component ∈ order object support) :
    (vertices object support component).Nonempty := by
  classical
  rw [order, List.mem_dedup] at member
  rcases List.mem_map.mp member with ⟨vertex, _vertexMem, rfl⟩
  refine ⟨vertex.1, ?_⟩
  exact (mem_vertices_iff object support _ _).mpr ⟨vertex.2, rfl⟩

/-- Every component produced by the scan is connected inside its literal
ambient support. -/
theorem connectedOn_of_mem_order (object : FiniteObject V)
    (support : Finset V) {component : Component object support}
    (member : component ∈ order object support) :
    NegativeSupportHandoff.ConnectedOn object
      (vertices object support component) := by
  refine ⟨vertices_nonempty_of_mem_order object support member, ?_⟩
  intro left right leftMem rightMem
  classical
  rcases (mem_vertices_iff object support component left).mp leftMem with
    ⟨leftSupport, leftComponent⟩
  rcases (mem_vertices_iff object support component right).mp rightMem with
    ⟨rightSupport, rightComponent⟩
  let left' : {value : V // value ∈ support} := ⟨left, leftSupport⟩
  let right' : {value : V // value ∈ support} := ⟨right, rightSupport⟩
  have sameComponent :
      (inducedObject object support).graph.connectedComponentMk left' =
        (inducedObject object support).graph.connectedComponentMk right' := by
    simpa [left', right', vertexComponent] using
      leftComponent.trans rightComponent.symm
  have reachable :
      (inducedObject object support).graph.Reachable left' right' :=
    SimpleGraph.ConnectedComponent.exact sameComponent
  exact reachable.elim_path fun path => by
    let embedding := object.induceFinsetEmbedding support
    let mappedPath := path.map embedding.toHom embedding.injective
    have contained : ∀ vertex ∈ mappedPath.val.support,
        vertex ∈ vertices object support component := by
      intro vertex vertexMem
      change vertex ∈ (path.val.map embedding.toHom).support at vertexMem
      rw [SimpleGraph.Walk.support_map] at vertexMem
      rcases List.mem_map.mp vertexMem with ⟨supported, supportedMem, rfl⟩
      apply (mem_vertices_iff object support component supported.1).mpr
      refine ⟨supported.2, ?_⟩
      have connected :
          (inducedObject object support).graph.Reachable left' supported :=
        ⟨path.val.takeUntil supported supportedMem⟩
      have equal := SimpleGraph.ConnectedComponent.sound connected
      exact equal.symm.trans leftComponent
    have result : ∃ ambientPath : object.graph.Walk
        (embedding.toHom left') (embedding.toHom right'),
        ambientPath.IsPath ∧
          ∀ vertex ∈ ambientPath.support,
            vertex ∈ vertices object support component :=
      ⟨mappedPath, mappedPath.property, contained⟩
    simpa [embedding, left', right'] using result

/-- Distinct produced component carriers are disjoint. -/
theorem disjoint_vertices (object : FiniteObject V) (support : Finset V)
    {left right : Component object support} (different : left ≠ right) :
    Disjoint (vertices object support left) (vertices object support right) := by
  classical
  apply Finset.disjoint_left.mpr
  intro vertex leftMem rightMem
  rcases (mem_vertices_iff object support left vertex).mp leftMem with
    ⟨leftSupport, leftComponent⟩
  rcases (mem_vertices_iff object support right vertex).mp rightMem with
    ⟨rightSupport, rightComponent⟩
  apply different
  rw [← leftComponent, ← rightComponent]

/-- A supported neighbour of a vertex in one produced component remains in
that same literal component. -/
theorem neighbor_mem_vertices (object : FiniteObject V) (support : Finset V)
    (component : Component object support) {vertex neighbor : V}
    (vertexMember : vertex ∈ vertices object support component)
    (neighborSupport : neighbor ∈ support)
    (adjacent : object.graph.Adj vertex neighbor) :
    neighbor ∈ vertices object support component := by
  classical
  rcases (mem_vertices_iff object support component vertex).mp vertexMember with
    ⟨vertexSupport, vertexComponentEqual⟩
  let vertex' : {value : V // value ∈ support} := ⟨vertex, vertexSupport⟩
  let neighbor' : {value : V // value ∈ support} := ⟨neighbor, neighborSupport⟩
  have inducedAdjacent : (inducedObject object support).graph.Adj
      vertex' neighbor' := adjacent
  have sameMembership := SimpleGraph.ConnectedComponent.mem_supp_congr_adj
    component inducedAdjacent
  have vertexInComponent : vertex' ∈ component.supp := by
    rw [SimpleGraph.ConnectedComponent.mem_supp_iff]
    exact vertexComponentEqual
  have neighborInComponent : neighbor' ∈ component.supp :=
    sameMembership.mp vertexInComponent
  apply (mem_vertices_iff object support component neighbor).mpr
  exact ⟨neighborSupport,
    (SimpleGraph.ConnectedComponent.mem_supp_iff _ _).mp neighborInComponent⟩

/-- Exact pointwise coverage of the supplied support. -/
theorem mem_support_iff_mem_component (object : FiniteObject V)
    (support : Finset V) (vertex : V) :
    vertex ∈ support ↔
      ∃ component ∈ order object support,
        vertex ∈ vertices object support component := by
  classical
  constructor
  · intro vertexMem
    let supported : {value : V // value ∈ support} := ⟨vertex, vertexMem⟩
    refine ⟨vertexComponent object support supported, ?_, ?_⟩
    · rw [order, List.mem_dedup]
      exact List.mem_map.mpr
        ⟨supported,
          (inducedObject object support).input.vertices.mem_orderedValues _, rfl⟩
    · exact (mem_vertices_iff object support _ vertex).mpr ⟨vertexMem, rfl⟩
  · rintro ⟨component, _componentMem, vertexMem⟩
    exact ((mem_vertices_iff object support component vertex).mp vertexMem).1

/-- The component order contains no duplicate component. -/
theorem order_nodup (object : FiniteObject V) (support : Finset V) :
    (order object support).Nodup := by
  classical
  exact List.nodup_dedup _

/-- At most one component is introduced per scanned support vertex. -/
theorem order_length_le_support_card (object : FiniteObject V)
    (support : Finset V) :
    (order object support).length ≤ support.card := by
  classical
  calc
    (order object support).length ≤
        ((inducedObject object support).input.vertices.orderedValues.map
          (vertexComponent object support)).length := by
      exact (List.dedup_sublist
        ((inducedObject object support).input.vertices.orderedValues.map
          (vertexComponent object support))).length_le
    _ = support.card := by simp

/-- Primitive work charged to the decomposition: one component lookup per
actual supported vertex. -/
def checks (_object : FiniteObject V) (support : Finset V) : Nat :=
  support.card

theorem checks_linear (object : FiniteObject V) (support : Finset V) :
    checks object support ≤ support.card := le_rfl

end StructuralExhaustion.Graph.OrderedSupportComponents
