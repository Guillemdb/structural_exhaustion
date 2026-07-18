import StructuralExhaustion.Graph.InducedPathConnectorCycle
import StructuralExhaustion.Graph.InducedPathRestrictedComponentBoundarySchedule
import StructuralExhaustion.Graph.WalkPrefixFiltration

namespace StructuralExhaustion.Graph.InducedPathRestrictedPrefixCompletion

open StructuralExhaustion
open InducedPathWindowLedger
open InducedPathRestrictedColdSkeleton
open InducedPathRestrictedComponentBoundarySchedule

universe u

variable {V : Type u} {object : FiniteObject V}
variable {family : CubicWindowFamily object}

/-!
# Literal completions from restricted component-path prefixes

For one stored restricted component path, a completion at a window offset is
recognized only when the current prefix endpoint has the corresponding
ambient edge back to the anchor window.  The predicate therefore records an
actual graph edge, not merely acceptance of an arithmetically smeared length.
-/

noncomputable def componentEmbedding (input : Input family) :
    (component input.anchor).toSimpleGraph ↪g object.graph :=
  (object.induceFinsetEmbedding (outsideVertices family)).comp
    (SimpleGraph.Embedding.induce (component input.anchor).supp)

noncomputable def profile (input : Input family) :
    WalkPrefixFiltration.Profile (componentPath input) :=
  ⟨componentPath_isPath input⟩

abbrev Stage (input : Input family) := (profile input).Stage

/-- The actual prefix, mapped through both induced-subgraph inclusions to the
original graph. -/
noncomputable def ambientPrefix (input : Input family) (stage : Stage input) :
    object.graph.Walk input.anchor.neighbor
      ((componentPath input).getVert stage.val).1.1 :=
  ((profile input).prefixWalk stage).map (componentEmbedding input).toHom

theorem ambientPrefix_isPath (input : Input family) (stage : Stage input) :
    (ambientPrefix input stage).IsPath :=
  SimpleGraph.Walk.map_isPath_of_injective
    (componentEmbedding input).injective
    ((profile input).prefixWalk_isPath stage)

theorem anchor_window_vertex_deleted (input : Input family)
    (offset : Fin 13) :
    selectedWindow object input.anchor.window offset ∈
      deletedWindowVertices family := by
  classical
  simp only [deletedWindowVertices, Finset.mem_biUnion]
  refine ⟨input.anchor.window, input.anchor.window_mem, ?_⟩
  rw [InducedPathPacking.mem_support_iff]
  exact ⟨offset, rfl⟩

theorem ambientPrefix_outside_anchor_window (input : Input family)
    (stage : Stage input) :
    ∀ vertex ∈ (ambientPrefix input stage).support,
      ∀ position : Fin 13,
        vertex ≠ selectedWindow object input.anchor.window position := by
  classical
  letI : DecidableEq V := object.input.vertices.decEq
  intro vertex member position equal
  have supportEq := SimpleGraph.Walk.support_map
    (componentEmbedding input).toHom ((profile input).prefixWalk stage)
  change vertex ∈ (((profile input).prefixWalk stage).map
    (componentEmbedding input).toHom).support at member
  rw [supportEq] at member
  obtain ⟨internal, _internalMember, internalEq⟩ := List.mem_map.mp member
  have outside : internal.1.1 ∈ outsideVertices family := internal.1.2
  have notDeleted := (Finset.mem_sdiff.mp outside).2
  have internalValueEq : internal.1.1 = vertex := internalEq
  apply notDeleted
  rw [internalValueEq, equal]
  exact anchor_window_vertex_deleted input position

theorem anchor_adjacent (input : Input family) :
    object.graph.Adj input.anchor.neighbor
      (selectedWindow object input.anchor.window input.anchor.offset) := by
  classical
  letI : FinEnum V := object.input.vertices
  letI : DecidableEq V := object.input.vertices.decEq
  letI : DecidableRel object.graph.Adj := object.input.decideAdj
  have adjacent : object.graph.Adj
      (selectedWindow object input.anchor.window input.anchor.offset)
      input.anchor.neighbor := by
    have ambient := (Finset.mem_sdiff.mp input.anchor.token.2.2.2).1
    simpa [ambientNeighbors, SimpleGraph.mem_neighborFinset] using ambient
  exact adjacent.symm

/-- Exact local F1 predicate.  The positive-stage guard excludes a degenerate
zero-length connector; the adjacency field is the literal missing return edge
which an arithmetic target-response bit by itself does not supply. -/
def CompletionAt (input : Input family) (LengthOK : Nat → Prop)
    (stage : Stage input) (offset : Fin 13) : Prop :=
  0 < (ambientPrefix input stage).length ∧
    object.graph.Adj ((componentPath input).getVert stage.val).1.1
      (selectedWindow object input.anchor.window offset) ∧
    LengthOK ((ambientPrefix input stage).length + 2 +
      InducedPathAttachment.positionDistance input.anchor.offset offset)

/-- A reported restricted-prefix completion constructs a literal simple
cycle in the original graph with the accepted exact length. -/
noncomputable def cycleOfCompletion (input : Input family)
    (LengthOK : Nat → Prop) (stage : Stage input) (offset : Fin 13)
    (hit : CompletionAt input LengthOK stage offset) :
    CycleWithLength object.graph LengthOK := by
  have endpointDistinct :
      input.anchor.neighbor ≠
        ((componentPath input).getVert stage.val).1.1 := by
    intro equal
    have endAtStart :
        (ambientPrefix input stage).getVert
            (ambientPrefix input stage).length = input.anchor.neighbor := by
      simpa using equal.symm
    have zero := ((ambientPrefix_isPath input stage).getVert_eq_start_iff
      (i := (ambientPrefix input stage).length) (by omega)).mp endAtStart
    exact (Nat.ne_of_gt hit.1) zero
  exact InducedPathConnectorCycle.connectorCycle LengthOK
    (selectedWindow object input.anchor.window)
    (ambientPrefix input stage) (ambientPrefix_isPath input stage)
    (ambientPrefix_outside_anchor_window input stage) endpointDistinct
    input.anchor.offset offset (anchor_adjacent input) hit.2.1 (by
      exact hit.2.2)

end StructuralExhaustion.Graph.InducedPathRestrictedPrefixCompletion
