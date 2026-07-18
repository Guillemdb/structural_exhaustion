import StructuralExhaustion.Graph.FiniteTwoBoundaryPiece

namespace StructuralExhaustion.Graph.FiniteTwoBoundaryIncidenceOwnership

open StructuralExhaustion

universe u

variable {V : Type u} {object : FiniteObject V}

/-!
# Local ownership ledger for a two-boundary support

The ledger scans only vertices of the declared support and their already
declared neighbor rows.  It never enumerates an ambient graph or a family of
outside contexts.
-/

noncomputable def escapingInternalIncidences
    (input : FiniteTwoBoundaryPiece.Input object) : List (V × V) := by
  letI : DecidableEq V := object.input.vertices.decEq
  exact input.support.toList.flatMap fun vertex =>
    if vertex = input.left ∨ vertex = input.right then []
    else ((object.input.orderedNeighbors vertex).values.filter
      fun neighbor => decide (neighbor ∉ input.support)).map
        fun neighbor => (vertex, neighbor)

theorem mem_escapingInternalIncidences_iff
    (input : FiniteTwoBoundaryPiece.Input object) (vertex neighbor : V) :
    (vertex, neighbor) ∈ escapingInternalIncidences input ↔
      vertex ∈ input.support ∧ vertex ≠ input.left ∧
        vertex ≠ input.right ∧ object.graph.Adj vertex neighbor ∧
        neighbor ∉ input.support := by
  letI : DecidableEq V := object.input.vertices.decEq
  rw [escapingInternalIncidences, List.mem_flatMap]
  constructor
  · rintro ⟨source, sourceMem, pairMem⟩
    rw [Finset.mem_toList] at sourceMem
    by_cases boundary : source = input.left ∨ source = input.right
    · simp [boundary] at pairMem
    · simp only [if_neg boundary, List.mem_map, List.mem_filter] at pairMem
      rcases pairMem with ⟨target, ⟨targetMem, targetOutside⟩, equal⟩
      push Not at boundary
      rcases boundary with ⟨sourceLeft, sourceRight⟩
      have pairEqual : source = vertex ∧ target = neighbor := by
        simpa only [Prod.mk.injEq] using equal
      rcases pairEqual with ⟨rfl, rfl⟩
      exact ⟨sourceMem, sourceLeft, sourceRight,
        (object.input.mem_orderedNeighbors_iff _ _).1 targetMem,
        of_decide_eq_true targetOutside⟩
  · rintro ⟨sourceMem, sourceLeft, sourceRight, adjacent, targetOutside⟩
    refine ⟨vertex, Finset.mem_toList.mpr sourceMem, ?_⟩
    have notBoundary : ¬(vertex = input.left ∨ vertex = input.right) := by
      simp [sourceLeft, sourceRight]
    rw [if_neg notBoundary, List.mem_map]
    exact ⟨neighbor, List.mem_filter.mpr
      ⟨(object.input.mem_orderedNeighbors_iff _ _).2 adjacent,
        decide_eq_true targetOutside⟩, rfl⟩

/-- Exact graph-theoretic ownership condition: every incidence at an internal
support vertex remains inside the declared support. -/
def InternalIncidencesOwned
    (input : FiniteTwoBoundaryPiece.Input object) : Prop :=
  ∀ vertex ∈ input.support,
    vertex ≠ input.left → vertex ≠ input.right →
      ∀ neighbor, object.graph.Adj vertex neighbor → neighbor ∈ input.support

theorem escapingInternalIncidences_eq_nil_iff
    (input : FiniteTwoBoundaryPiece.Input object) :
    escapingInternalIncidences input = [] ↔ InternalIncidencesOwned input := by
  rw [List.eq_nil_iff_forall_not_mem]
  constructor
  · intro absent vertex vertexMem notLeft notRight neighbor adjacent
    by_contra outside
    exact absent (vertex, neighbor)
      ((mem_escapingInternalIncidences_iff input vertex neighbor).2
        ⟨vertexMem, notLeft, notRight, adjacent, outside⟩)
  · intro owned pair member
    rcases pair with ⟨vertex, neighbor⟩
    rcases (mem_escapingInternalIncidences_iff input vertex neighbor).1 member with
      ⟨vertexMem, notLeft, notRight, adjacent, outside⟩
    exact outside (owned vertex vertexMem notLeft notRight neighbor adjacent)

noncomputable def ownershipDecidable
    (input : FiniteTwoBoundaryPiece.Input object) :
    Decidable (InternalIncidencesOwned input) := by
  rw [← escapingInternalIncidences_eq_nil_iff]
  infer_instance

/-- Visible local work: one support row plus the declared neighbor rows of its
internal vertices. -/
noncomputable def visibleChecks
    (input : FiniteTwoBoundaryPiece.Input object) : Nat := by
  letI : DecidableEq V := object.input.vertices.decEq
  exact input.support.card + input.support.toList.foldl
    (fun total vertex => total +
      if vertex = input.left ∨ vertex = input.right then 0
      else (object.input.orderedNeighbors vertex).values.length) 0

end StructuralExhaustion.Graph.FiniteTwoBoundaryIncidenceOwnership
