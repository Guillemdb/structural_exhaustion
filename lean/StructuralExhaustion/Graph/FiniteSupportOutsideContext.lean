import StructuralExhaustion.Graph.FiniteSupportResponse

namespace StructuralExhaustion.Graph.FiniteSupportOutsideContext

open StructuralExhaustion
open PackedBoundariedGluing

universe u

variable {V : Type u}

/-- The literal complement of a declared finite support. -/
abbrev Complement (support : Finset V) := {vertex : V // vertex ∉ support}

/-- Decode a normalized outside-context vertex back to its ambient label. -/
def decode (support : Finset V) : V ⊕ Complement support → V
  | .inl vertex => vertex
  | .inr vertex => vertex.1

/-- Only declared support labels are active on the boundary side.  This keeps
the ambient boundary type required by `FiniteSupportResponse` without adding
duplicate copies of complement vertices to the represented graph. -/
def Active (support : Finset V) : V ⊕ Complement support → Prop
  | .inl vertex => vertex ∈ support
  | .inr _ => True

/-- The normalized outside graph owns precisely support--complement and
complement--complement ambient edges; support--support edges remain owned by
the finite-support piece. -/
noncomputable def graph (ambient : SimpleGraph V) (support : Finset V) :
    SimpleGraph (V ⊕ Complement support) where
  Adj left right :=
    ambient.Adj (decode support left) (decode support right) ∧
      Active support left ∧ Active support right ∧
      ¬(left.isLeft ∧ right.isLeft)
  symm := ⟨by
      rintro left right ⟨adjacent, activeLeft, activeRight, notBoth⟩
      exact ⟨(ambient.adj_comm _ _).mp adjacent, activeRight, activeLeft, by
        simpa [and_comm] using notBoth⟩⟩
  loopless := ⟨by
      intro vertex adjacent
      exact (SimpleGraph.loopless ambient).irrefl _ adjacent.1⟩

/-- Framework-owned outside context on the literal complement.  Its boundary
type remains the ambient vertex type, exactly as required by finite-support
response coordinates. -/
noncomputable def context (object : FiniteObject V) (support : Finset V) :
    Context V := by
  letI : FinEnum V := object.input.vertices
  exact {
    Internal := Complement support
    internalVertices := inferInstance
    graph := graph object.graph support
    decideAdj := Classical.decRel _
    noBoundaryEdge := by
      intro left right adjacent
      exact adjacent.2.2.2 ⟨rfl, rfl⟩
  }

@[simp]
theorem context_adj_boundary_internal_iff (object : FiniteObject V)
    (support : Finset V) (boundary : V) (internal : Complement support) :
    (context object support).graph.Adj (.inl boundary) (.inr internal) ↔
      boundary ∈ support ∧ object.graph.Adj boundary internal.1 := by
  classical
  simp [context, graph, decode, Active, and_comm]

@[simp]
theorem context_adj_internal_internal_iff (object : FiniteObject V)
    (support : Finset V) (left right : Complement support) :
    (context object support).graph.Adj (.inr left) (.inr right) ↔
      object.graph.Adj left.1 right.1 := by
  classical
  simp [context, graph, decode, Active]

/-- Canonical representative of each ambient vertex in the normalized glued
carrier: support vertices use their ambient boundary label and all other
vertices use the unique complement copy. -/
noncomputable def ambientEmbedding (support : Finset V) :
    V ↪ (V ⊕ Complement support) := by
  classical
  exact {
    toFun := fun vertex =>
      if member : vertex ∈ support then .inl vertex else .inr ⟨vertex, member⟩
    inj' := by
      intro left right equal
      by_cases leftMem : left ∈ support <;>
        by_cases rightMem : right ∈ support <;>
          simp [leftMem, rightMem] at equal <;> simp_all
  }

@[simp]
theorem decode_ambientEmbedding (support : Finset V) (vertex : V) :
    decode support (ambientEmbedding support vertex) = vertex := by
  classical
  by_cases member : vertex ∈ support <;>
    simp [ambientEmbedding, member, decode]

/-- The normalized context represents every ambient edge not internal to the
declared support, on the canonical ambient representatives. -/
theorem context_adj_ambientEmbedding_iff (object : FiniteObject V)
    (support : Finset V) (left right : V)
    (outsideOwned : ¬(left ∈ support ∧ right ∈ support)) :
    (context object support).graph.Adj
        (ambientEmbedding support left) (ambientEmbedding support right) ↔
      object.graph.Adj left right := by
  classical
  simp only [context, graph]
  rw [decode_ambientEmbedding, decode_ambientEmbedding]
  simp only [ambientEmbedding]
  by_cases leftMem : left ∈ support <;>
    by_cases rightMem : right ∈ support <;>
      simp [leftMem, rightMem, Active] at outsideOwned ⊢

/-- Canonical copy of the ambient vertices in the literal gluing of the
finite-support piece with its normalized complement context. -/
noncomputable def gluedEmbedding (support : Finset V) :
    V ↪ (V ⊕ (PEmpty.{u + 1} ⊕ Complement support)) := by
  classical
  exact {
    toFun := fun vertex =>
      if member : vertex ∈ support then .inl vertex
      else .inr (.inr ⟨vertex, member⟩)
    inj' := by
      intro left right equal
      by_cases leftMem : left ∈ support <;>
        by_cases rightMem : right ∈ support <;>
          simp [leftMem, rightMem] at equal <;> simp_all
  }

end StructuralExhaustion.Graph.FiniteSupportOutsideContext
