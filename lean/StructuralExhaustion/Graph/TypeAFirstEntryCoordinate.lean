import StructuralExhaustion.Graph.TypeAAnchoredReturnCoordinate
import StructuralExhaustion.Core.FiniteSearch

namespace StructuralExhaustion.Graph.TypeAFirstEntryCoordinate

open StructuralExhaustion
open TypeACanonicalReceiverTrace

universe u

variable {V : Type u} (object : FiniteObject V)
variable (profile : SupportProfile object)
variable (port : TypeAAnchoredReturnCoordinate.Port object profile)
variable (anchored : TypeAAnchoredReturnCoordinate.AnchoredReturn object profile port)

abbrev Path := anchored.path object profile

noncomputable def inSupportDecidable (vertex : V) :
    Decidable (vertex ∈ profile.support) := by
  letI : DecidableEq V := object.input.vertices.decEq
  exact inferInstance

/-- First support hit along the one stored anchored-return path. -/
structure FirstEntry where
  hit : Core.FiniteSearch.FirstHit (Path object profile port anchored).support
    (fun vertex => vertex ∈ profile.support)

namespace FirstEntry

def entry (first : FirstEntry object profile port anchored) : V :=
  first.hit.value

theorem entry_mem_support (first : FirstEntry object profile port anchored) :
    first.entry object profile port anchored ∈ profile.support :=
  first.hit.holds

theorem before_outside (first : FirstEntry object profile port anchored) :
    ∀ vertex ∈ first.hit.before, vertex ∉ profile.support :=
  first.hit.beforeAbsent

theorem before_nonempty (first : FirstEntry object profile port anchored) :
    first.hit.before ≠ [] := by
  intro empty
  have split := first.hit.split
  rw [empty, List.nil_append] at split
  have headExact := congrArg List.head? split
  have pathHead : (Path object profile port anchored).support.head? =
      some (port.outside object profile) := by
    calc
      (Path object profile port anchored).support.head? =
          ((port.outside object profile) ::
            (Path object profile port anchored).support.tail).head? :=
        congrArg List.head?
          (Path object profile port anchored).cons_tail_support.symm
      _ = some (port.outside object profile) := rfl
  rw [pathHead] at headExact
  simp at headExact
  have outside := port.outside_not_mem_support object profile
  exact outside (headExact ▸ first.entry_mem_support object profile port anchored)

def predecessor (first : FirstEntry object profile port anchored) : V :=
  first.hit.before.getLast (first.before_nonempty object profile port anchored)

theorem predecessor_mem_before (first : FirstEntry object profile port anchored) :
    first.predecessor object profile port anchored ∈ first.hit.before :=
  List.getLast_mem _

theorem predecessor_outside (first : FirstEntry object profile port anchored) :
    first.predecessor object profile port anchored ∉ profile.support :=
  first.before_outside object profile port anchored _
    (first.predecessor_mem_before object profile port anchored)

theorem predecessor_adjacent_entry
    (first : FirstEntry object profile port anchored) :
    object.graph.Adj
      (first.predecessor object profile port anchored)
      (first.entry object profile port anchored) := by
  have chain := (Path object profile port anchored).isChain_adj_support
  rw [first.hit.split] at chain
  have boundary := (List.isChain_append.mp chain).2.2
    (first.predecessor object profile port anchored)
      (List.getLast?_eq_some_getLast
        (first.before_nonempty object profile port anchored))
    (first.entry object profile port anchored) (by simp [entry])
  exact (object.graph.deleteEdges_le _ ) boundary

/-- The first-entry incidence is retained in the literal port-edge-deleted
graph.  Keeping this stronger form is what lets the degree-two entry argument
exclude the terminal receiver without forgetting which edge was deleted. -/
theorem predecessor_adjacent_entry_deleted
    (first : FirstEntry object profile port anchored) :
    (object.graph.deleteEdges
      {s((port.receiver object profile).1,
        port.outside object profile)}).Adj
      (first.predecessor object profile port anchored)
      (first.entry object profile port anchored) := by
  have chain := (Path object profile port anchored).isChain_adj_support
  rw [first.hit.split] at chain
  exact (List.isChain_append.mp chain).2.2
    (first.predecessor object profile port anchored)
      (List.getLast?_eq_some_getLast
        (first.before_nonempty object profile port anchored))
    (first.entry object profile port anchored) (by simp [entry])

/-- The outside predecessor occupies one ambient incidence absent from the
induced support, so ambient cubicity forces internal degree at most two. -/
theorem entry_internal_degree_le_two
    (first : FirstEntry object profile port anchored) :
    (profile.supportObject object).degree
      (⟨first.entry object profile port anchored,
        first.entry_mem_support object profile port anchored⟩ : profile.Vertex) ≤ 2 := by
  let entryVertex : profile.Vertex :=
    ⟨first.entry object profile port anchored,
      first.entry_mem_support object profile port anchored⟩
  change (profile.supportObject object).degree entryVertex ≤ 2
  letI : FinEnum V := object.input.vertices
  letI : DecidableRel object.graph.Adj := object.input.decideAdj
  have subset : Subtype.val ''
      (profile.supportObject object).graph.neighborSet entryVertex ⊆
      object.graph.neighborSet entryVertex.1 := by
    rintro neighbor ⟨internal, adjacent, rfl⟩
    exact adjacent
  have strict : Subtype.val ''
      (profile.supportObject object).graph.neighborSet entryVertex ⊂
      object.graph.neighborSet entryVertex.1 := by
    refine ⟨subset, ?_⟩
    intro reverse
    have predecessorAmbient : first.predecessor object profile port anchored ∈
        object.graph.neighborSet entryVertex.1 :=
      (first.predecessor_adjacent_entry object profile port anchored).symm
    obtain ⟨internal, _adjacent, exact⟩ := reverse predecessorAmbient
    apply first.predecessor_outside object profile port anchored
    rw [← exact]
    exact internal.2
  have cardinalStrict := Set.ncard_lt_ncard strict
  have imageCard :
      (Subtype.val ''
        (profile.supportObject object).graph.neighborSet entryVertex).ncard =
        ((profile.supportObject object).graph.neighborSet entryVertex).ncard :=
    Set.ncard_image_of_injective _ Subtype.val_injective
  rw [imageCard, ← (profile.supportObject object).degree_eq_ncard_neighborSet,
    ← object.degree_eq_ncard_neighborSet] at cardinalStrict
  rw [profile.ambient_cubic entryVertex.1 entryVertex.2] at cardinalStrict
  omega

end FirstEntry

/-- Execute one first-entry scan on the literal stored path support. The final
receiver guarantees a hit, so the absence branch is impossible. -/
noncomputable def select : FirstEntry object profile port anchored := by
  let result := Core.FiniteSearch.firstOnList
    (Path object profile port anchored).support
    (fun vertex => vertex ∈ profile.support)
    (inSupportDecidable object profile)
  cases result with
  | found hit => exact ⟨hit⟩
  | absent none =>
      have terminalMem : (port.receiver object profile).1 ∈
          (Path object profile port anchored).support := by
        simpa only [SimpleGraph.Walk.getVert_length] using
          (Path object profile port anchored).getVert_mem_support
            (Path object profile port anchored).length
      exact (none _ terminalMem (port.receiver object profile).2).elim

def visibleChecks : Nat := (Path object profile port anchored).support.length

theorem visibleChecks_eq_length_add_one :
    visibleChecks object profile port anchored =
      (Path object profile port anchored).length + 1 := by
  exact (Path object profile port anchored).length_support

end StructuralExhaustion.Graph.TypeAFirstEntryCoordinate
