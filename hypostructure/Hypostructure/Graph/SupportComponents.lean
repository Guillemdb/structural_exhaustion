import Hypostructure.Graph.Finite
import Hypostructure.Graph.Induced
import Hypostructure.Core.Finite.ConnectedPartition
import Hypostructure.Core.Finite.Partition

namespace Hypostructure.Graph.SupportComponents

/-! ## Graph-derived connected-component adapter

Core owns the ordered label partition machinery; Graph specializes it for
connected components of an induced support and proves the ambient connectivity
and disjoint coverage laws needed by the legacy support-localization nodes. -/

namespace Connected

universe u

abbrev InducedObject (object : FiniteObject.{u})
    (support : Finset object.Vertex) := object.induce support

abbrev Component (object : FiniteObject.{u})
    (support : Finset object.Vertex) :=
  (InducedObject object support).graph.ConnectedComponent

noncomputable def schedule (object : FiniteObject.{u})
    (support : Finset object.Vertex) :
    Core.Finite.Enumeration {value : object.Vertex // value ∈ support} := by
  let induced := InducedObject object support
  exact {
    values := induced.orderedVertices
    nodup := induced.orderedVertices_nodup
    decEq := induced.vertices.decEq }

def componentOf (object : FiniteObject.{u})
    (support : Finset object.Vertex)
    (vertex : {value : object.Vertex // value ∈ support}) :
    Component object support :=
  (InducedObject object support).graph.connectedComponentMk vertex

noncomputable def order (object : FiniteObject.{u})
    (support : Finset object.Vertex) : List (Component object support) := by
  exact Core.Finite.ConnectedPartition.order
    (schedule object support) (componentOf object support)

noncomputable def members (object : FiniteObject.{u})
    (support : Finset object.Vertex)
    (component : Component object support) : Finset object.Vertex := by
  classical
  exact (Core.Finite.ConnectedPartition.members
    (schedule object support) (componentOf object support) component).image
      Subtype.val

/- Compatibility with earlier component APIs. -/
noncomputable def vertices (object : FiniteObject.{u})
    (support : Finset object.Vertex)
    (component : Component object support) : Finset object.Vertex :=
  members object support component

def ConnectedOn (object : FiniteObject.{u})
    (core : Finset object.Vertex) : Prop :=
  core.Nonempty ∧
    ∀ ⦃left right : object.Vertex⦄, left ∈ core → right ∈ core →
      ∃ path : object.graph.Walk left right,
        path.IsPath ∧ ∀ vertex ∈ path.support, vertex ∈ core

@[simp] theorem mem_members_iff (object : FiniteObject.{u})
    (support : Finset object.Vertex) (component : Component object support)
    (vertex : object.Vertex) :
    vertex ∈ members object support component ↔
      ∃ member : vertex ∈ support,
        componentOf object support ⟨vertex, member⟩ = component := by
  classical
  unfold members
  constructor
  · intro member
    rcases Finset.mem_image.mp member with ⟨supported, supportedMem, rfl⟩
    have exactMember :=
      (Core.Finite.ConnectedPartition.mem_members_iff
        (schedule object support) (componentOf object support) component
        supported).mp supportedMem
    exact ⟨supported.2, exactMember.2⟩
  · rintro ⟨member, componentEq⟩
    refine Finset.mem_image.mpr ⟨⟨vertex, member⟩, ?_, rfl⟩
    have scheduleMember :
        (⟨vertex, member⟩ : {value : object.Vertex // value ∈ support}) ∈
          (schedule object support).values := by
      change (⟨vertex, member⟩ : (InducedObject object support).Vertex) ∈
        (InducedObject object support).orderedVertices
      exact (InducedObject object support).mem_orderedVertices _
    exact (Core.Finite.ConnectedPartition.mem_members_iff
      (schedule object support) (componentOf object support) component
      ⟨vertex, member⟩).mpr
      ⟨scheduleMember, componentEq⟩

@[simp] theorem mem_vertices_iff (object : FiniteObject.{u})
    (support : Finset object.Vertex) (component : Component object support)
    (vertex : object.Vertex) :
    vertex ∈ vertices object support component ↔
      ∃ member : vertex ∈ support,
        componentOf object support ⟨vertex, member⟩ = component := by
  simp [vertices, mem_members_iff]

theorem member_nonempty (object : FiniteObject.{u})
    (support : Finset object.Vertex) {component : Component object support}
    (componentMem : component ∈ order object support) :
    (members object support component).Nonempty := by
  classical
  rw [order, Core.Finite.ConnectedPartition.order, Core.Finite.OrderedPartition.labels_complete] at componentMem
  rcases componentMem with ⟨vertex, _vertexMem, rfl⟩
  refine ⟨vertex.1, ?_⟩
  exact (mem_members_iff object support _ _).mpr ⟨vertex.2, rfl⟩

theorem vertices_nonempty_of_mem_order (object : FiniteObject.{u})
    (support : Finset object.Vertex) {component : Component object support}
    (componentMem : component ∈ order object support) :
    (vertices object support component).Nonempty := by
  simpa [vertices] using member_nonempty object support componentMem

theorem connectedOn_of_mem_order (object : FiniteObject.{u})
    (support : Finset object.Vertex)
    {component : Component object support}
    (componentMem : component ∈ order object support) :
    ConnectedOn object (members object support component) := by
  refine ⟨member_nonempty object support componentMem, ?_⟩
  intro left right leftMem rightMem
  classical
  rcases (mem_members_iff object support component left).mp leftMem with
    ⟨leftSupport, leftComponent⟩
  rcases (mem_members_iff object support component right).mp rightMem with
    ⟨rightSupport, rightComponent⟩
  let left' : {value : object.Vertex // value ∈ support} :=
    ⟨left, leftSupport⟩
  let right' : {value : object.Vertex // value ∈ support} :=
    ⟨right, rightSupport⟩
  have sameComponent :
      (InducedObject object support).graph.connectedComponentMk left' =
        (InducedObject object support).graph.connectedComponentMk right' := by
    simpa [left', right', componentOf] using
      leftComponent.trans rightComponent.symm
  have reachable :
      (InducedObject object support).graph.Reachable left' right' :=
    SimpleGraph.ConnectedComponent.exact sameComponent
  exact reachable.elim_path (fun path => by
    let embedding := object.induceEmbedding support
    let mappedPath := path.map embedding.toHom embedding.injective
    have contained : ∀ vertex ∈ mappedPath.val.support,
        vertex ∈ members object support component := by
      intro vertex vertexMem
      change vertex ∈ (path.val.map embedding.toHom).support at vertexMem
      rw [SimpleGraph.Walk.support_map] at vertexMem
      rcases List.mem_map.mp vertexMem with ⟨supported, supportedMem, rfl⟩
      apply (mem_members_iff object support component supported.1).mpr
      refine ⟨supported.2, ?_⟩
      have connected :
          (InducedObject object support).graph.Reachable left' supported :=
        ⟨path.val.takeUntil supported supportedMem⟩
      have equal := SimpleGraph.ConnectedComponent.sound connected
      exact equal.symm.trans leftComponent
    have result : ∃ ambientPath : object.graph.Walk
        (embedding.toHom left') (embedding.toHom right'),
        ambientPath.IsPath ∧
          ∀ vertex ∈ ambientPath.support,
            vertex ∈ members object support component :=
      ⟨mappedPath, mappedPath.property, contained⟩
    simpa [embedding, left', right'] using result)

theorem disjoint_members (object : FiniteObject.{u})
    (support : Finset object.Vertex)
    {left right : Component object support} (different : left ≠ right) :
    Disjoint (members object support left) (members object support right) := by
  classical
  apply Finset.disjoint_left.mpr
  intro vertex leftMem rightMem
  rcases (mem_members_iff object support left vertex).mp leftMem with
    ⟨leftSupport, leftComponent⟩
  rcases (mem_members_iff object support right vertex).mp rightMem with
    ⟨rightSupport, rightComponent⟩
  apply different
  rw [← leftComponent, ← rightComponent]

theorem disjoint_vertices (object : FiniteObject.{u})
    (support : Finset object.Vertex)
    {left right : Component object support} (different : left ≠ right) :
    Disjoint (vertices object support left) (vertices object support right) := by
  simpa [vertices] using
    disjoint_members object support (left := left) (right := right) different

theorem mem_support_iff_mem_component (object : FiniteObject.{u})
    (support : Finset object.Vertex) (vertex : object.Vertex) :
    vertex ∈ support ↔
      ∃ component ∈ order object support,
        vertex ∈ members object support component := by
  classical
  constructor
  · intro vertexMem
    let supported : {value : object.Vertex // value ∈ support} :=
      ⟨vertex, vertexMem⟩
    refine ⟨componentOf object support supported, ?_, ?_⟩
    · rw [order, Core.Finite.ConnectedPartition.order,
        Core.Finite.OrderedPartition.labels_complete]
      exact ⟨supported,
        (InducedObject object support).mem_orderedVertices _, rfl⟩
    · exact (mem_members_iff object support _ vertex).mpr ⟨vertexMem, rfl⟩
  · rintro ⟨component, _componentMem, vertexMem⟩
    exact ((mem_members_iff object support component vertex).mp vertexMem).1

theorem mem_support_iff_mem_component_with_vertices
    (object : FiniteObject.{u})
    (support : Finset object.Vertex) (vertex : object.Vertex) :
    vertex ∈ support ↔
      ∃ component ∈ order object support,
        vertex ∈ vertices object support component := by
  simpa [vertices] using mem_support_iff_mem_component object support vertex

theorem order_nodup (object : FiniteObject.{u})
  (support : Finset object.Vertex) :
  (order object support).Nodup := by
  classical
  exact Core.Finite.ConnectedPartition.order_nodup
    (schedule object support) (componentOf object support)

theorem order_length_le_support_card (object : FiniteObject.{u})
    (support : Finset object.Vertex) :
    (order object support).length ≤ support.card := by
  classical
  calc
    (order object support).length ≤
        (schedule object support).card :=
      Core.Finite.ConnectedPartition.order_length_le
        (schedule object support) (componentOf object support)
    _ = support.card := by
      change (InducedObject object support).orderedVertices.length = support.card
      rw [(InducedObject object support).orderedVertices_length]
      exact object.vertexCount_induce support

/-- A neighbor in the same support and adjacency preserves connected-component
membership. -/
theorem neighbor_mem_vertices (object : FiniteObject.{u}) (support : Finset object.Vertex)
    (component : Component object support) {vertex neighbor : object.Vertex}
    (vertexMember : vertex ∈ vertices object support component)
    (neighborSupport : neighbor ∈ support)
    (adjacent : object.graph.Adj vertex neighbor) :
    neighbor ∈ vertices object support component := by
  rcases (mem_vertices_iff object support component vertex).mp vertexMember with
    ⟨vertexSupport, vertexComponentEqual⟩
  let vertex' : {value : object.Vertex // value ∈ support} := ⟨vertex, vertexSupport⟩
  let neighbor' : {value : object.Vertex // value ∈ support} := ⟨neighbor, neighborSupport⟩
  have inducedAdjacent : (InducedObject object support).graph.Adj
      vertex' neighbor' := adjacent
  have sameMembership :=
    SimpleGraph.ConnectedComponent.mem_supp_congr_adj
      (componentOf object support vertex') inducedAdjacent
  have vertexInComponent : vertex' ∈ (componentOf object support vertex').supp := by
    have h : vertex' ∈ (componentOf object support vertex').supp := by
      exact (SimpleGraph.ConnectedComponent.mem_supp_iff
        (C := componentOf object support vertex') vertex').2 rfl
    exact h
  have neighborInComponent : neighbor' ∈ (componentOf object support vertex').supp :=
    sameMembership.mp vertexInComponent
  have neighborComponent' : componentOf object support neighbor' =
      componentOf object support vertex' :=
    (SimpleGraph.ConnectedComponent.mem_supp_iff
      (C := componentOf object support vertex') neighbor').1
      neighborInComponent
  have neighborComponent : componentOf object support neighbor' = component := by
    rw [neighborComponent', vertexComponentEqual]
  exact (mem_vertices_iff object support component neighbor).mpr
    ⟨neighborSupport, neighborComponent⟩

def checks (object : FiniteObject.{u})
    (support : Finset object.Vertex) : Nat := support.card

theorem checks_linear (object : FiniteObject.{u})
    (support : Finset object.Vertex) :
    checks object support ≤ support.card := le_rfl

end Connected
end Hypostructure.Graph.SupportComponents
