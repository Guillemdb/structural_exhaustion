import StructuralExhaustion.Graph.InducedSubgraph
import StructuralExhaustion.Graph.WalkPrefixFiltration

namespace StructuralExhaustion.Graph.FiniteTwoBoundaryPiece

open StructuralExhaustion

universe u

variable {V : Type u} {object : FiniteObject V}

/-!
# A finite induced piece with two labelled boundary vertices

This module reconstructs a literal `Fin 2`-boundaried piece from one declared
finite support.  Its internal type contains exactly the supported vertices
other than the two endpoints.  The piece graph is the ambient graph comapped
along the resulting vertex equivalence, so no ambient graph or context family
is enumerated.
-/

/-- The complete local data needed to cut out a two-boundary piece. -/
structure Input (object : FiniteObject V) where
  support : Finset V
  left : V
  right : V
  left_mem : left ∈ support
  right_mem : right ∈ support
  left_ne_right : left ≠ right

namespace Input

/-- Supported vertices not used as labelled boundary vertices. -/
def Internal (input : Input object) :=
  {vertex : V // vertex ∈ input.support ∧
    vertex ≠ input.left ∧ vertex ≠ input.right}

/-- The two endpoints in their declared boundary order. -/
def boundary (input : Input object) : Fin 2 → V :=
  Fin.cases input.left (fun _ : Fin 1 => input.right)

@[simp]
theorem boundary_zero (input : Input object) : input.boundary 0 = input.left := rfl

@[simp]
theorem boundary_one (input : Input object) : input.boundary 1 = input.right := rfl

theorem boundary_mem (input : Input object) (index : Fin 2) :
    input.boundary index ∈ input.support := by
  fin_cases index <;> simp [input.left_mem, input.right_mem]

theorem boundary_injective (input : Input object) :
    Function.Injective input.boundary := by
  intro first second equal
  fin_cases first <;> fin_cases second
  · rfl
  · exact False.elim (input.left_ne_right equal)
  · exact False.elim (input.left_ne_right equal.symm)
  · rfl

/-- Exact vertex identification between a two-boundary piece and the support
subtype. -/
def vertexEquiv (input : Input object) :
    Fin 2 ⊕ input.Internal ≃ {vertex : V // vertex ∈ input.support} := by
  letI : DecidableEq V := object.input.vertices.decEq
  exact {
    toFun := fun
      | .inl index => ⟨input.boundary index, input.boundary_mem index⟩
      | .inr internal => ⟨internal.1, internal.2.1⟩
    invFun := fun vertex =>
      if left : vertex.1 = input.left then .inl 0
      else if right : vertex.1 = input.right then .inl 1
      else .inr ⟨vertex.1, vertex.2, left, right⟩
    left_inv := by
      intro vertex
      cases vertex with
      | inl index =>
          fin_cases index
          · simp
          · simp [input.left_ne_right.symm]
      | inr internal =>
          simp [internal.2.2.1, internal.2.2.2]
    right_inv := by
      intro vertex
      by_cases left : vertex.1 = input.left
      · apply Subtype.ext
        simp [left]
      · by_cases right : vertex.1 = input.right
        · apply Subtype.ext
          simp [right, input.left_ne_right.symm]
        · apply Subtype.ext
          simp [left, right]
  }

@[simp]
theorem vertexEquiv_inl_val (input : Input object) (index : Fin 2) :
    (input.vertexEquiv (.inl index)).1 = input.boundary index := rfl

@[simp]
theorem vertexEquiv_inr_val (input : Input object)
    (internal : input.Internal) :
    (input.vertexEquiv (.inr internal)).1 = internal.1 := rfl

@[simp]
theorem vertexEquiv_symm_left (input : Input object) :
    input.vertexEquiv.symm ⟨input.left, input.left_mem⟩ = .inl 0 := by
  simp [vertexEquiv]

@[simp]
theorem vertexEquiv_symm_right (input : Input object) :
    input.vertexEquiv.symm ⟨input.right, input.right_mem⟩ = .inl 1 := by
  simp [vertexEquiv, input.left_ne_right.symm]

/-- The finite schedule on internal vertices is the source schedule filtered
by support and endpoint exclusion. -/
@[implicit_reducible]
def internalVertices (input : Input object) : FinEnum input.Internal :=
  Core.Enumeration.subtype object.input.vertices
    (fun vertex => vertex ∈ input.support ∧
      vertex ≠ input.left ∧ vertex ≠ input.right)
    (by
      letI : DecidableEq V := object.input.vertices.decEq
      infer_instance)

/-- A literal finite graph with two labelled boundary vertices.  This local
structure permits the boundary and internal types to live in different
universes; its packed view is an ordinary `FiniteObject`. -/
structure Piece (input : Input object) where
  graph : SimpleGraph (Fin 2 ⊕ input.Internal)
  decideAdj : DecidableRel graph.Adj

/-- The literal boundaried graph whose vertices are exactly `support`. -/
def piece (input : Input object) : Piece input where
  graph := SimpleGraph.comap
    (fun vertex => (input.vertexEquiv vertex).1) object.graph
  decideAdj := by
    letI : DecidableRel object.graph.Adj := object.input.decideAdj
    infer_instance

/-- Pack the two-boundary piece as an ordinary explicitly finite graph. -/
def Piece.pack (piece : Piece input) : FiniteObject (Fin 2 ⊕ input.Internal) where
  graph := piece.graph
  input := {
    vertices := by
      letI : FinEnum input.Internal := input.internalVertices
      infer_instance
    decideAdj := piece.decideAdj
  }

/-- Exact degree at a labelled boundary vertex. -/
def Piece.boundaryDegree (piece : Piece input) (index : Fin 2) : Nat :=
  by
    letI : FinEnum input.Internal := input.internalVertices
    letI : DecidableRel piece.graph.Adj := piece.decideAdj
    exact piece.graph.degree (.inl index)

/-- Ambient neighbours of one boundary vertex that remain in the declared
support. -/
def supportedNeighbors (input : Input object) (index : Fin 2) : Finset V := by
  letI : DecidableEq V := object.input.vertices.decEq
  letI : FinEnum input.Internal := input.internalVertices
  letI : DecidableRel input.piece.graph.Adj := input.piece.decideAdj
  exact (input.piece.graph.neighborFinset (.inl index)).image
    fun vertex => (input.vertexEquiv vertex).1

@[simp]
theorem mem_supportedNeighbors_iff (input : Input object) (index : Fin 2)
    (vertex : V) :
    vertex ∈ input.supportedNeighbors index ↔
      vertex ∈ input.support ∧
        object.graph.Adj (input.boundary index) vertex := by
  letI : DecidableEq V := object.input.vertices.decEq
  letI : DecidableRel object.graph.Adj := object.input.decideAdj
  letI : FinEnum input.Internal := input.internalVertices
  letI : DecidableRel input.piece.graph.Adj := input.piece.decideAdj
  constructor
  · intro member
    rw [supportedNeighbors, Finset.mem_image] at member
    rcases member with ⟨pieceVertex, adjacent, rfl⟩
    refine ⟨(input.vertexEquiv pieceVertex).2, ?_⟩
    rw [SimpleGraph.mem_neighborFinset] at adjacent
    exact adjacent
  · rintro ⟨supported, adjacent⟩
    let vertex : {value : V // value ∈ input.support} := ⟨vertex, supported⟩
    rw [supportedNeighbors, Finset.mem_image]
    refine ⟨input.vertexEquiv.symm vertex, ?_, ?_⟩
    · rw [SimpleGraph.mem_neighborFinset]
      change object.graph.Adj (input.boundary index)
        (input.vertexEquiv (input.vertexEquiv.symm vertex)).1
      simpa [vertex] using adjacent
    · simp [vertex]

@[simp]
theorem piece_adj_iff (input : Input object)
    (first second : Fin 2 ⊕ input.Internal) :
    input.piece.graph.Adj first second ↔
      object.graph.Adj (input.vertexEquiv first).1
        (input.vertexEquiv second).1 :=
  Iff.rfl

@[simp]
theorem boundary_adj_iff (input : Input object) (index : Fin 2)
    (vertex : Fin 2 ⊕ input.Internal) :
    input.piece.graph.Adj (.inl index) vertex ↔
      object.graph.Adj (input.boundary index)
        (input.vertexEquiv vertex).1 :=
  Iff.rfl

@[simp]
theorem internal_adj_iff (input : Input object)
    (first second : input.Internal) :
    input.piece.graph.Adj (.inr first) (.inr second) ↔
      object.graph.Adj first.1 second.1 :=
  Iff.rfl

/-- The piece is graph-isomorphic to the ambient graph induced on exactly the
declared support. -/
def supportIso (input : Input object) :
    input.piece.graph ≃g (object.induceFinset input.support).graph :=
  SimpleGraph.Iso.comap input.vertexEquiv
    (object.induceFinset input.support).graph

@[simp]
theorem supportIso_apply (input : Input object)
    (vertex : Fin 2 ⊕ input.Internal) :
    input.supportIso vertex = input.vertexEquiv vertex := rfl

/-- The image of the piece's vertex equivalence is the whole declared
support, not an enlarged ambient carrier. -/
theorem vertex_image_eq_support (input : Input object) :
    Set.range (fun vertex : Fin 2 ⊕ input.Internal =>
      (input.vertexEquiv vertex).1) = (input.support : Set V) := by
  ext vertex
  constructor
  · rintro ⟨pieceVertex, rfl⟩
    exact (input.vertexEquiv pieceVertex).2
  · intro member
    let supported : {value : V // value ∈ input.support} := ⟨vertex, member⟩
    exact ⟨input.vertexEquiv.symm supported, by simp [supported]⟩

/-- Packing the piece retains the exact induced-support graph, modulo the
canonical vertex equivalence. -/
def packIso (input : Input object) :
    input.piece.pack.graph ≃g
      (object.induceFinset input.support).graph :=
  input.supportIso

@[simp]
theorem packIso_apply (input : Input object)
    (vertex : Fin 2 ⊕ input.Internal) :
    input.packIso vertex = input.vertexEquiv vertex := rfl

/-- Exact degree at either boundary: it counts precisely the ambient
neighbours that lie in the declared support. -/
theorem boundaryDegree_eq_supportedNeighbors (input : Input object)
    (index : Fin 2) :
    input.piece.boundaryDegree index =
      (input.supportedNeighbors index).card := by
  letI : FinEnum V := object.input.vertices
  letI : DecidableEq V := object.input.vertices.decEq
  letI : DecidableRel object.graph.Adj := object.input.decideAdj
  letI : FinEnum input.Internal := input.internalVertices
  letI : DecidableRel input.piece.graph.Adj := input.piece.decideAdj
  unfold Piece.boundaryDegree
  change input.piece.graph.degree (.inl index) = _
  change (input.piece.graph.neighborFinset (.inl index)).card = _
  rw [supportedNeighbors, Finset.card_image_of_injective]
  exact fun _ _ equal => input.vertexEquiv.injective (Subtype.ext equal)

/-- Transfer a selected piece walk to the identical induced support. -/
def walkToSupport (input : Input object) {first second}
    (walk : input.piece.graph.Walk first second) :
    (object.induceFinset input.support).graph.Walk
      (input.vertexEquiv first) (input.vertexEquiv second) :=
  walk.map input.supportIso.toHom

/-- Transfer a selected induced-support walk back to the literal piece. -/
def walkFromSupport (input : Input object) {first second}
    (walk : (object.induceFinset input.support).graph.Walk first second) :
    input.piece.graph.Walk
      (input.vertexEquiv.symm first) (input.vertexEquiv.symm second) :=
  walk.map input.supportIso.symm.toHom

@[simp]
theorem walkToSupport_length (input : Input object) {first second}
    (walk : input.piece.graph.Walk first second) :
    (input.walkToSupport walk).length = walk.length := by
  exact walk.length_map input.supportIso.toHom

@[simp]
theorem walkFromSupport_length (input : Input object) {first second}
    (walk : (object.induceFinset input.support).graph.Walk first second) :
    (input.walkFromSupport walk).length = walk.length := by
  exact walk.length_map input.supportIso.symm.toHom

theorem walkToSupport_isPath (input : Input object) {first second}
    {walk : input.piece.graph.Walk first second} (isPath : walk.IsPath) :
    (input.walkToSupport walk).IsPath :=
  SimpleGraph.Walk.map_isPath_of_injective input.supportIso.injective isPath

theorem walkFromSupport_isPath (input : Input object) {first second}
    {walk : (object.induceFinset input.support).graph.Walk first second}
    (isPath : walk.IsPath) :
    (input.walkFromSupport walk).IsPath :=
  SimpleGraph.Walk.map_isPath_of_injective input.supportIso.symm.injective isPath

end Input

section WalkPrefix

variable {start finish : V}
variable {path : object.graph.Walk start finish}

/-- The exact support finset of a proof-selected initial path prefix. -/
noncomputable def prefixFinset
    (profile : WalkPrefixFiltration.Profile path)
    (stage : profile.Stage) : Finset V := by
  letI : DecidableEq V := object.input.vertices.decEq
  exact (profile.prefixSupport stage).toFinset

/-- A positive path-prefix stage supplies a literal two-boundary piece: its
boundaries are the path start and the current prefix endpoint. -/
noncomputable def ofWalkPrefix
    (profile : WalkPrefixFiltration.Profile path)
    (stage : profile.Stage) (positive : 0 < stage.val) : Input object := by
  letI : DecidableEq V := object.input.vertices.decEq
  exact {
    support := prefixFinset profile stage
    left := start
    right := path.getVert stage.val
    left_mem := by
      rw [prefixFinset, List.mem_toFinset, ← profile.prefixWalk_support stage]
      exact (profile.prefixWalk stage).start_mem_support
    right_mem := by
      rw [prefixFinset, List.mem_toFinset, ← profile.prefixWalk_support stage]
      exact (profile.prefixWalk stage).end_mem_support
    left_ne_right := by
      intro equal
      have atStart : path.getVert stage.val = start := equal.symm
      have bounded : stage.val ≤ path.length := by
        have lt := stage.isLt
        have supportLength : path.support.length = path.length + 1 :=
          path.length_support
        omega
      exact (Nat.ne_of_gt positive)
        ((profile.isPath.getVert_eq_start_iff bounded).mp atStart)
  }

@[simp]
theorem ofWalkPrefix_support
    (profile : WalkPrefixFiltration.Profile path)
    (stage : profile.Stage) (positive : 0 < stage.val) :
    (ofWalkPrefix profile stage positive).support =
      prefixFinset profile stage := rfl

@[simp]
theorem ofWalkPrefix_left
    (profile : WalkPrefixFiltration.Profile path)
    (stage : profile.Stage) (positive : 0 < stage.val) :
    (ofWalkPrefix profile stage positive).left = start := rfl

@[simp]
theorem ofWalkPrefix_right
    (profile : WalkPrefixFiltration.Profile path)
    (stage : profile.Stage) (positive : 0 < stage.val) :
    (ofWalkPrefix profile stage positive).right =
      path.getVert stage.val := rfl

end WalkPrefix

end StructuralExhaustion.Graph.FiniteTwoBoundaryPiece
