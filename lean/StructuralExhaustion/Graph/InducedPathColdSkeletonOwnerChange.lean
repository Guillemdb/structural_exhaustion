import StructuralExhaustion.Graph.InducedPathColdSkeletonBoundaryTransition
import Mathlib.Data.Vector.Basic
import Mathlib.Tactic

namespace StructuralExhaustion.Graph.InducedPathColdSkeletonOwnerChange

open StructuralExhaustion
open InducedPathWindowLedger
open InducedPathColdLedger
open InducedPathColdSkeleton

universe u

variable {V : Type u}

/-!
# First selected-window owner change on one packed return

The input is exactly the all-inside output of the preceding boundary scan.
Every path vertex is assigned its unique ambient-cubic selected-window owner.
The runner then scans only consecutive owner values.  It returns either one
owner for the whole path or the first literal cross-window edge.

This module does not define a cold subfamily and does not construct an outside
component or successor.
-/

/-- A selected ambient-cubic window and exact position owning one vertex. -/
structure OwnedSlot (object : FiniteObject V) (vertex : V) where
  window : WindowIndex object
  cubic : AmbientCubic object window
  position : Fin 13
  exact : selectedWindow object window position = vertex

namespace OwnedSlot

variable {object : FiniteObject V} {vertex : V}

theorem exists_of_mem_deleted
    (member : vertex ∈ deletedWindowVertices object) :
    Nonempty (OwnedSlot object vertex) := by
  classical
  simp only [deletedWindowVertices, Finset.mem_biUnion] at member
  rcases member with ⟨window, _windowUniv, member⟩
  by_cases cubic : AmbientCubic object window
  · simp only [cubic, if_pos, InducedPathPacking.mem_support_iff] at member
    rcases member with ⟨position, exact⟩
    exact ⟨⟨window, cubic, position, exact⟩⟩
  · simp [cubic] at member

theorem window_unique (left right : OwnedSlot object vertex) :
    left.window = right.window := by
  classical
  by_contra different
  let profile := InducedPathPacking.profile object 13 (by decide)
  have selectedEq : selectedWindows object = profile.maximum.1 :=
    selectedWindows_eq_maximum object
  have leftMember : left.window.1 ∈ profile.maximum.1 := by
    rw [← selectedEq]
    exact left.window.2
  have rightMember : right.window.1 ∈ profile.maximum.1 := by
    rw [← selectedEq]
    exact right.window.2
  have windowDifferent : left.window.1 ≠ right.window.1 := by
    intro equal
    apply different
    exact Subtype.ext equal
  have disjoint := profile.maximum.2 leftMember rightMember windowDifferent
  have leftSupport : vertex ∈ InducedPathPacking.support object 13 left.window.1 :=
    (InducedPathPacking.mem_support_iff object 13 left.window.1 vertex).2
      ⟨left.position, left.exact⟩
  have rightSupport : vertex ∈ InducedPathPacking.support object 13 right.window.1 :=
    (InducedPathPacking.mem_support_iff object 13 right.window.1 vertex).2
      ⟨right.position, right.exact⟩
  exact Finset.disjoint_left.mp disjoint leftSupport rightSupport

theorem position_unique (left right : OwnedSlot object vertex)
    (same : left.window = right.window) : left.position = right.position := by
  have rightExact : selectedWindow object left.window right.position = vertex := by
    simpa [same] using right.exact
  exact (selectedWindow object left.window).injective
    (left.exact.trans rightExact.symm)

end OwnedSlot

/-- One path together with the exact all-inside predecessor residual. -/
structure Input (object : FiniteObject V) where
  boundaryInput : InducedPathColdSkeletonBoundaryTransition.Input object
  supportSubset : ∀ vertex ∈ boundaryInput.path.support,
    vertex ∈ deletedWindowVertices object
  /-- The ambient-cubic filter is stored once, rather than recomputed by each
  vertex lookup. -/
  preparedCubicWindows : List (WindowIndex object)
  preparedCubicWindows_eq : preparedCubicWindows =
    (windowIndices object).orderedValues.filter
      (fun window ↦ @decide (AmbientCubic object window)
        (ambientCubicDecidable object window))
  /-- The corresponding finite slot inventory is likewise stored once. -/
  preparedSlots : List (WindowIndex object × Fin 13)
  preparedSlots_eq : preparedSlots = preparedCubicWindows.flatMap fun window ↦
    (inferInstance : FinEnum (Fin 13)).orderedValues.map fun position ↦
      (window, position)

namespace Input

variable {object : FiniteObject V}

abbrev path (input : Input object) := input.boundaryInput.path
abbrev VertexIndex (input : Input object) := Fin (input.path.length + 1)
abbrev EdgeIndex (input : Input object) := Fin input.path.length

theorem vertex_mem_support (input : Input object) (index : input.VertexIndex) :
    input.path.getVert index.1 ∈ input.path.support := by
  rw [SimpleGraph.Walk.mem_support_iff_exists_getVert]
  exact ⟨index.1, rfl, by omega⟩

/-- Selected windows in their declared finite order. -/
noncomputable def windowOrder (input : Input object) : List (WindowIndex object) :=
  (windowIndices object).orderedValues

/-- The executable ambient-cubic filter, evaluated once by the reference
owner inventory. -/
noncomputable def cubicWindowOrder (input : Input object) :
    List (WindowIndex object) := input.preparedCubicWindows

/-- Exact finite `window × Fin 13` owner inventory. -/
noncomputable def slotOrder (input : Input object) :
    List (WindowIndex object × Fin 13) := input.preparedSlots

/-- Construct the once-prepared local inventory. -/
noncomputable def prepare
    (boundaryInput : InducedPathColdSkeletonBoundaryTransition.Input object)
    (supportSubset : ∀ vertex ∈ boundaryInput.path.support,
      vertex ∈ deletedWindowVertices object) : Input object := by
  classical
  let cubicWindows := (windowIndices object).orderedValues.filter
    (fun window ↦ @decide (AmbientCubic object window)
      (ambientCubicDecidable object window))
  let slots := cubicWindows.flatMap fun window ↦
    (inferInstance : FinEnum (Fin 13)).orderedValues.map fun position ↦
      (window, position)
  exact {
    boundaryInput := boundaryInput
    supportSubset := supportSubset
    preparedCubicWindows := cubicWindows
    preparedCubicWindows_eq := rfl
    preparedSlots := slots
    preparedSlots_eq := rfl
  }

theorem cubic_of_mem_slotOrder (input : Input object)
    {entry : WindowIndex object × Fin 13} (member : entry ∈ input.slotOrder) :
    AmbientCubic object entry.1 := by
  classical
  rw [slotOrder, input.preparedSlots_eq, List.mem_flatMap] at member
  rcases member with ⟨window, windowMember, positionMember⟩
  rw [List.mem_map] at positionMember
  rcases positionMember with ⟨position, _positionMember, equal⟩
  cases equal
  rw [input.preparedCubicWindows_eq] at windowMember
  exact @of_decide_eq_true (AmbientCubic object window)
    (ambientCubicDecidable object window)
    (List.mem_filter.mp windowMember).2

theorem pair_mem_slotOrder (input : Input object)
    (window : WindowIndex object) (cubic : AmbientCubic object window)
    (position : Fin 13) : (window, position) ∈ input.slotOrder := by
  classical
  rw [slotOrder, input.preparedSlots_eq, List.mem_flatMap]
  refine ⟨window, ?_, ?_⟩
  · rw [input.preparedCubicWindows_eq, List.mem_filter]
    exact ⟨FinEnum.mem_orderedValues (windowIndices object) window,
      @decide_eq_true (AmbientCubic object window)
        (ambientCubicDecidable object window) cubic⟩
  · rw [List.mem_map]
    exact ⟨position,
      FinEnum.mem_orderedValues (inferInstance : FinEnum (Fin 13)) position,
      rfl⟩

def SlotMatches (input : Input object) (vertex : V)
    (entry : WindowIndex object × Fin 13) : Prop :=
  selectedWindow object entry.1 entry.2 = vertex

noncomputable def slotMatchesDecidable (input : Input object) (vertex : V)
    (entry : WindowIndex object × Fin 13) :
    Decidable (input.SlotMatches vertex entry) := by
  exact object.input.vertices.decEq _ _

/-- Actual finite lookup used by `ownedSlot`. -/
noncomputable def lookup (input : Input object) (vertex : V) :
    Core.FiniteSearch.FirstResult input.slotOrder (input.SlotMatches vertex) :=
  Core.FiniteSearch.firstOnList input.slotOrder (input.SlotMatches vertex)
    (input.slotMatchesDecidable vertex)

noncomputable def ownedSlot (input : Input object) (index : input.VertexIndex) :
    OwnedSlot object (input.path.getVert index.1) := by
  generalize equation : input.lookup (input.path.getVert index.1) = result
  cases result with
  | found hit =>
      exact {
        window := hit.value.1
        cubic := input.cubic_of_mem_slotOrder hit.member
        position := hit.value.2
        exact := hit.holds
      }
  | absent none =>
      apply False.elim
      have member := input.supportSubset _ (input.vertex_mem_support index)
      simp only [deletedWindowVertices, Finset.mem_biUnion] at member
      rcases member with ⟨window, _windowUniv, member⟩
      by_cases cubic : AmbientCubic object window
      · simp only [cubic, if_pos, InducedPathPacking.mem_support_iff] at member
        rcases member with ⟨position, exact⟩
        exact none (window, position)
          (input.pair_mem_slotOrder window cubic position) exact
      · simp [cubic] at member

/-- Once-materialized owner table, aligned with `Fin (path.length + 1)`.
Construction performs the charged slot lookup once per path vertex. -/
structure OwnerTable (input : Input object) where
  values : List.Vector (WindowIndex object × Fin 13) (input.path.length + 1)
  cubic : ∀ index : input.VertexIndex,
    AmbientCubic object (values.get index).1
  exact : ∀ index : input.VertexIndex,
    selectedWindow object (values.get index).1 (values.get index).2 =
        input.path.getVert index.1

noncomputable def prepareOwnerTable (input : Input object) : OwnerTable input := by
  let values := List.Vector.ofFn fun index : input.VertexIndex ↦
    let slot := input.ownedSlot index
    (slot.window, slot.position)
  refine {
    values := values
    cubic := ?_
    exact := ?_
  }
  · intro index
    simpa only [values, List.Vector.get_ofFn] using
      (input.ownedSlot index).cubic
  · intro index
    simpa only [values, List.Vector.get_ofFn] using
      (input.ownedSlot index).exact

namespace OwnerTable

noncomputable def slot {input : Input object} (table : OwnerTable input)
    (index : input.VertexIndex) :
    OwnedSlot object (input.path.getVert index.1) where
  window := (table.values.get
    index).1
  cubic := table.cubic index
  position := (table.values.get
    index).2
  exact := table.exact index

noncomputable def owner {input : Input object} (table : OwnerTable input)
    (index : input.VertexIndex) : WindowIndex object :=
  (table.slot index).window

end OwnerTable

noncomputable def edgeOrder (input : Input object) : List input.EdgeIndex :=
  (inferInstance : FinEnum input.EdgeIndex).orderedValues

def OwnerChangeAt (input : Input object) (table : OwnerTable input)
    (index : input.EdgeIndex) : Prop :=
  table.owner ⟨index.1, by omega⟩ ≠
    table.owner ⟨index.1 + 1, by omega⟩

noncomputable def ownerChangeDecidable (input : Input object)
    (table : OwnerTable input) (index : input.EdgeIndex) :
    Decidable (input.OwnerChangeAt table index) := by
  classical
  exact inferInstance

noncomputable def scan (input : Input object) (table : OwnerTable input) :
    Core.FiniteSearch.FirstResult input.edgeOrder (input.OwnerChangeAt table) :=
  Core.FiniteSearch.first (inferInstance : FinEnum input.EdgeIndex)
    (input.OwnerChangeAt table) (input.ownerChangeDecidable table)

end Input

/-- Exact data at the first edge joining two distinct selected windows. -/
structure FirstCrossWindow {object : FiniteObject V} (input : Input object)
    (table : Input.OwnerTable input)
    (hit : Core.FiniteSearch.FirstHit input.edgeOrder
      (input.OwnerChangeAt table)) where
  leftSlot : OwnedSlot object (input.path.getVert hit.value.1)
  rightSlot : OwnedSlot object (input.path.getVert (hit.value.1 + 1))
  leftOwnerExact : leftSlot.window = table.owner ⟨hit.value.1, by omega⟩
  rightOwnerExact : rightSlot.window = table.owner ⟨hit.value.1 + 1, by omega⟩
  ownersDistinct : leftSlot.window ≠ rightSlot.window
  adjacent : object.graph.Adj (input.path.getVert hit.value.1)
    (input.path.getVert (hit.value.1 + 1))
  leftToken : Token object
  leftTokenWindow : leftToken.1 = leftSlot.window
  leftTokenPosition : leftToken.2.1 = leftSlot.position
  leftTokenNeighbor : leftToken.2.2.1 = input.path.getVert (hit.value.1 + 1)
  leftTokenSubtype : tokenSubtype object leftToken = .crossWindow
  rightToken : Token object
  rightTokenWindow : rightToken.1 = rightSlot.window
  rightTokenPosition : rightToken.2.1 = rightSlot.position
  rightTokenNeighbor : rightToken.2.2.1 = input.path.getVert hit.value.1
  rightTokenSubtype : tokenSubtype object rightToken = .crossWindow

namespace FirstCrossWindow

variable {object : FiniteObject V} {input : Input object}
variable {table : Input.OwnerTable input}
variable {hit : Core.FiniteSearch.FirstHit input.edgeOrder
  (input.OwnerChangeAt table)}

noncomputable def ofFirstHit : FirstCrossWindow input table hit := by
  classical
  letI : FinEnum V := object.input.vertices
  letI : DecidableEq V := object.input.vertices.decEq
  letI : DecidableRel object.graph.Adj := object.input.decideAdj
  let left := table.slot ⟨hit.value.1, by omega⟩
  let right := table.slot ⟨hit.value.1 + 1, by omega⟩
  have adjacent := input.path.adj_getVert_succ hit.value.2
  have distinct : left.window ≠ right.window := hit.holds
  have rightNotLeftSupport : input.path.getVert (hit.value.1 + 1) ∉
      InducedPathPacking.support object 13 (selectedWindow object left.window) := by
    intro member
    let candidate : OwnedSlot object (input.path.getVert (hit.value.1 + 1)) := {
      window := left.window
      cubic := left.cubic
      position := Classical.choose
        ((InducedPathPacking.mem_support_iff object 13
          (selectedWindow object left.window) _).1 member)
      exact := Classical.choose_spec
        ((InducedPathPacking.mem_support_iff object 13
          (selectedWindow object left.window) _).1 member)
    }
    exact distinct (OwnedSlot.window_unique candidate right)
  have leftNotRightSupport : input.path.getVert hit.value.1 ∉
      InducedPathPacking.support object 13 (selectedWindow object right.window) := by
    intro member
    let candidate : OwnedSlot object (input.path.getVert hit.value.1) := {
      window := right.window
      cubic := right.cubic
      position := Classical.choose
        ((InducedPathPacking.mem_support_iff object 13
          (selectedWindow object right.window) _).1 member)
      exact := Classical.choose_spec
        ((InducedPathPacking.mem_support_iff object 13
          (selectedWindow object right.window) _).1 member)
    }
    exact distinct ((OwnedSlot.window_unique left candidate).trans rfl)
  have rightExternal : input.path.getVert (hit.value.1 + 1) ∈
      externalNeighbors object left.window left.position := by
    rw [externalNeighbors, Finset.mem_sdiff]
    constructor
    · rw [ambientNeighbors, SimpleGraph.mem_neighborFinset, left.exact]
      exact adjacent
    · intro internal
      apply rightNotLeftSupport
      rw [InducedPathPacking.mem_support_iff]
      unfold internalNeighbors at internal
      rw [Finset.mem_image] at internal
      rcases internal with ⟨position, _member, exact⟩
      exact ⟨position, exact⟩
  have leftExternal : input.path.getVert hit.value.1 ∈
      externalNeighbors object right.window right.position := by
    rw [externalNeighbors, Finset.mem_sdiff]
    constructor
    · rw [ambientNeighbors, SimpleGraph.mem_neighborFinset, right.exact]
      exact adjacent.symm
    · intro internal
      apply leftNotRightSupport
      rw [InducedPathPacking.mem_support_iff]
      unfold internalNeighbors at internal
      rw [Finset.mem_image] at internal
      rcases internal with ⟨position, _member, exact⟩
      exact ⟨position, exact⟩
  exact {
    leftSlot := left
    rightSlot := right
    leftOwnerExact := rfl
    rightOwnerExact := rfl
    ownersDistinct := distinct
    adjacent := adjacent
    leftToken := ⟨left.window, left.position,
      ⟨input.path.getVert (hit.value.1 + 1), rightExternal⟩⟩
    leftTokenWindow := rfl
    leftTokenPosition := rfl
    leftTokenNeighbor := rfl
    leftTokenSubtype := by
      rw [tokenSubtype, if_pos]
      change input.path.getVert (hit.value.1 + 1) ∈
        InducedPathPacking.coveredVertices object 13 (by decide)
      exact right.exact ▸
        selectedWindow_mem_covered object right.window right.position
    rightToken := ⟨right.window, right.position,
      ⟨input.path.getVert hit.value.1, leftExternal⟩⟩
    rightTokenWindow := rfl
    rightTokenPosition := rfl
    rightTokenNeighbor := rfl
    rightTokenSubtype := by
      rw [tokenSubtype, if_pos]
      change input.path.getVert hit.value.1 ∈
        InducedPathPacking.coveredVertices object 13 (by decide)
      exact left.exact ▸
        selectedWindow_mem_covered object left.window left.position
  }

end FirstCrossWindow

/-- Exact exhaustive result of the owner-change scan. -/
inductive Result {object : FiniteObject V} (input : Input object) where
  | singleWindow (table : Input.OwnerTable input)
      (owner : WindowIndex object)
      (cubic : AmbientCubic object owner)
      (supportSubset : ∀ vertex ∈ input.path.support,
        vertex ∈ InducedPathPacking.support object 13
          (selectedWindow object owner))
  | firstCrossWindow
      (table : Input.OwnerTable input)
      (hit : Core.FiniteSearch.FirstHit input.edgeOrder
        (input.OwnerChangeAt table))
      (crossing : FirstCrossWindow input table hit)

noncomputable def run {object : FiniteObject V} (input : Input object) :
    Result input := by
  let table := input.prepareOwnerTable
  cases equation : input.scan table with
  | found hit => exact .firstCrossWindow table hit FirstCrossWindow.ofFirstHit
  | absent none =>
      let first : input.VertexIndex := ⟨0, by omega⟩
      let owner := table.owner first
      refine .singleWindow table owner (table.slot first).cubic ?_
      intro vertex member
      rw [SimpleGraph.Walk.mem_support_iff_exists_getVert] at member
      rcases member with ⟨index, rfl, indexLe⟩
      let atIndex : input.VertexIndex := ⟨index, by omega⟩
      have sameOwner : table.owner atIndex = owner := by
        induction index with
        | zero => rfl
        | succ index induction =>
            have indexLt : index < input.path.length := by omega
            let edge : input.EdgeIndex := ⟨index, indexLt⟩
            have noChange := none edge
              (FinEnum.mem_orderedValues
                (inferInstance : FinEnum input.EdgeIndex) edge)
            have equalOwners :
                table.owner ⟨index, by omega⟩ =
                  table.owner ⟨index + 1, by omega⟩ :=
              Classical.not_not.mp (by
                simpa [Input.OwnerChangeAt] using noChange)
            exact equalOwners.symm.trans (induction (by omega))
      let slot := table.slot atIndex
      have slotOwner : slot.window = owner := sameOwner
      rw [InducedPathPacking.mem_support_iff]
      exact ⟨slot.position, by simpa [slotOwner] using slot.exact⟩

theorem run_exhaustive {object : FiniteObject V} (input : Input object) :
    (∃ table owner cubic supportSubset,
      run input = .singleWindow table owner cubic supportSubset) ∨
    (∃ table hit crossing,
      run input = .firstCrossWindow table hit crossing) := by
  cases equation : run input with
  | singleWindow table owner cubic supportSubset =>
      exact Or.inl ⟨table, owner, cubic, supportSubset, rfl⟩
  | firstCrossWindow table hit crossing =>
      exact Or.inr ⟨table, hit, crossing, rfl⟩

/-- The first term prepares the ambient-cubic window inventory.  The second
materializes the aligned owner table by one finite slot scan per path vertex.
The final term compares consecutive stored owners once.  Subsequent
`OwnerTable.slot` projections, including the two projections retained in a
`FirstCrossWindow`, are constant-time reads from that already materialized
vector and add no predicate evaluations to this ledger. -/
noncomputable def visibleChecks {object : FiniteObject V}
    (input : Input object) : Nat :=
  13 * packingNumber object * object.input.vertices.card +
    input.path.support.length * (13 * packingNumber object) + input.path.length

theorem visibleChecks_le {object : FiniteObject V} (input : Input object)
    (scale : Nat) (supportBound : input.path.support.length ≤ scale) :
    visibleChecks input ≤ object.input.vertices.card ^ 2 +
      scale * (object.input.vertices.card + 1) := by
  have packed := InducedPathPacking.packing_vertices_bound object 13 (by decide)
  change 13 * packingNumber object ≤ object.input.vertices.card at packed
  have pathLength : input.path.length ≤ scale := by
    rw [SimpleGraph.Walk.length_support] at supportBound
    omega
  unfold visibleChecks
  nlinarith

end StructuralExhaustion.Graph.InducedPathColdSkeletonOwnerChange
