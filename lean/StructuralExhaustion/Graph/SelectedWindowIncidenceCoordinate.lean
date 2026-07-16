import StructuralExhaustion.Graph.InducedPathWindowLedger

namespace StructuralExhaustion.Graph.SelectedWindowIncidenceCoordinate

open StructuralExhaustion
open InducedPathWindowLedger

universe u

variable {V : Type u} (object : FiniteObject V)

/-!
# Direct ownership of covered vertices and literal window incidences

Covered membership already contains one selected window and one path position.
This module exposes that proof-selected slot directly and proves uniqueness
from packing disjointness.  It performs no scan of the selected-window family.
-/

/-- A selected-window owner and exact position for one literal covered vertex. -/
structure SelectedSlot (vertex : V) where
  window : WindowIndex object
  position : Fin 13
  exact : selectedWindow object window position = vertex

namespace SelectedSlot

theorem exists_of_mem_covered {vertex : V}
    (covered : vertex ∈
      InducedPathPacking.coveredVertices object 13 (by decide)) :
    Nonempty (SelectedSlot object vertex) := by
  classical
  rw [InducedPathPacking.mem_coveredVertices_iff] at covered
  rcases covered with ⟨window, windowMember, supportMember⟩
  let index : WindowIndex object := ⟨window, by
    unfold selectedWindows
    exact List.mem_toFinset.mpr windowMember⟩
  rcases (InducedPathPacking.mem_support_iff object 13 window vertex).mp
      supportMember with ⟨position, exact⟩
  exact ⟨⟨index, position, exact⟩⟩

/-- Proof-selected owner lookup from exact covered membership. -/
noncomputable def of_mem_covered {vertex : V}
    (covered : vertex ∈
      InducedPathPacking.coveredVertices object 13 (by decide)) :
    SelectedSlot object vertex :=
  Classical.choice (exists_of_mem_covered object covered)

theorem window_unique {vertex : V} (left right : SelectedSlot object vertex) :
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

theorem position_unique {vertex : V} (left right : SelectedSlot object vertex)
    (sameWindow : left.window = right.window) :
    left.position = right.position := by
  have rightExact :
      selectedWindow object left.window right.position = vertex := by
    simpa [sameWindow] using right.exact
  exact (selectedWindow object left.window).injective
    (left.exact.trans rightExact.symm)

end SelectedSlot

/-- Literal edge from a remainder-side vertex to its uniquely owned selected
window landing. -/
structure WindowRemainderIncidence where
  windowVertex : V
  slot : SelectedSlot object windowVertex
  remainderVertex : V
  remainder : remainderVertex ∈
    InducedPathPacking.remainderVertices object 13 (by decide)
  adjacent : object.graph.Adj remainderVertex windowVertex

/-- Literal edge whose two endpoints have different selected-window owners. -/
structure CrossWindowIncidence where
  leftVertex : V
  leftSlot : SelectedSlot object leftVertex
  rightVertex : V
  rightSlot : SelectedSlot object rightVertex
  differentOwner : leftSlot.window ≠ rightSlot.window
  adjacent : object.graph.Adj leftVertex rightVertex

/-- Literal edge whose two endpoints both lie in the exact remainder. -/
structure InternalRemainderIncidence where
  leftVertex : V
  leftRemainder : leftVertex ∈
    InducedPathPacking.remainderVertices object 13 (by decide)
  rightVertex : V
  rightRemainder : rightVertex ∈
    InducedPathPacking.remainderVertices object 13 (by decide)
  adjacent : object.graph.Adj leftVertex rightVertex

end StructuralExhaustion.Graph.SelectedWindowIncidenceCoordinate
