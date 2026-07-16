import StructuralExhaustion.Core.WorkBudget
import StructuralExhaustion.Graph.NegativeSupportHandoff

namespace StructuralExhaustion.Graph.TypeBDecoratedArmCoordinate

open StructuralExhaustion

universe u

variable
  {V : Type u}
  {object : FiniteObject V}
  {ContextSafe ForbiddenFree CoreFree Uncompressible : Finset V → Prop}
  {FanSafe : V → V → V → Prop}
  {source : NegativeSupportHandoff.ConnectedNegativeSupport object}
  (handoff : NegativeSupportHandoff.DecoratedHandoff object ContextSafe
    ForbiddenFree CoreFree Uncompressible FanSafe source)

/-!
# D6 decorated handoff-arm coordinates

The decorated Type A-to-Type B predecessor already stores a finite set of
first neighbours and one proof-carrying first-entry arm for each of them.  The
coordinate family here is exactly the dependent sum of those retained arms
and their literal walk positions.  It does not inspect any unretained neighbor
of the decoration center and does not search for paths.
-/

abbrev FirstNeighbor :=
  {vertex : V // vertex ∈ handoff.firstNeighbors}

/-- Enumerate the retained finite set directly; there is no ambient-vertex
filtering pass. -/
@[implicit_reducible]
noncomputable def firstNeighbors : FinEnum (FirstNeighbor handoff) := by
  letI : DecidableEq V := object.input.vertices.decEq
  exact @FinEnum.ofNodupList (FirstNeighbor handoff) inferInstance
    handoff.firstNeighbors.attach.toList
    (by
      intro first
      rw [Finset.mem_toList]
      exact Finset.mem_attach _ first)
    handoff.firstNeighbors.attach.nodup_toList

abbrev ArmPosition (first : FirstNeighbor handoff) :=
  Fin ((handoff.arm first).path.length + 1)

abbrev Coordinate :=
  Sigma fun first : FirstNeighbor handoff => ArmPosition handoff first

@[implicit_reducible]
noncomputable def coordinates : FinEnum (Coordinate handoff) := by
  letI : FinEnum (FirstNeighbor handoff) := firstNeighbors handoff
  letI : (first : FirstNeighbor handoff) →
      FinEnum (ArmPosition handoff first) := fun _ => inferInstance
  infer_instance

namespace Coordinate

noncomputable def first (coordinate : Coordinate handoff) :
    FirstNeighbor handoff :=
  coordinate.1

def position (coordinate : Coordinate handoff) : Nat :=
  coordinate.2.1

theorem position_le_length (coordinate : Coordinate handoff) :
    coordinate.position handoff ≤ (handoff.arm coordinate.first).path.length :=
  Nat.le_of_lt_succ coordinate.2.2

noncomputable def vertex (coordinate : Coordinate handoff) : V :=
  (handoff.arm coordinate.first).path.getVert coordinate.position

noncomputable def support (coordinate : Coordinate handoff) : Finset V := by
  letI : DecidableEq V := object.input.vertices.decEq
  exact insert handoff.center (handoff.arm coordinate.first).path.support.toFinset

/-- Literal stored value at one decorated-arm position. -/
structure Value (coordinate : Coordinate handoff) where
  firstNeighbor : V
  firstNeighborExact : firstNeighbor = coordinate.first.1
  position : Nat
  positionExact : position = coordinate.position handoff
  vertex : V
  vertexExact : vertex = coordinate.vertex handoff

noncomputable def value (coordinate : Coordinate handoff) : coordinate.Value handoff where
  firstNeighbor := coordinate.first.1
  firstNeighborExact := rfl
  position := coordinate.position handoff
  positionExact := rfl
  vertex := coordinate.vertex handoff
  vertexExact := rfl

theorem first_adjacent_center (coordinate : Coordinate handoff) :
    object.graph.Adj handoff.center coordinate.first.1 := by
  rw [← handoff.arm_first coordinate.first]
  exact (handoff.arm coordinate.first).center_adjacent

theorem arm_isPath (coordinate : Coordinate handoff) :
    (handoff.arm coordinate.first).path.IsPath :=
  (handoff.arm coordinate.first).isPath

theorem vertex_mem_arm (coordinate : Coordinate handoff) :
    coordinate.vertex handoff ∈
      (handoff.arm coordinate.first).path.support := by
  exact (handoff.arm coordinate.first).path.getVert_mem_support
    coordinate.position

theorem vertex_mem_support (coordinate : Coordinate handoff) :
    coordinate.vertex handoff ∈ coordinate.support handoff := by
  simp [support, coordinate.vertex_mem_arm handoff]

theorem center_not_mem_arm (coordinate : Coordinate handoff) :
    handoff.center ∉ (handoff.arm coordinate.first).path.support :=
  (handoff.arm coordinate.first).center_avoided

theorem core_vertex_is_terminal (coordinate : Coordinate handoff)
    (coreMember : coordinate.vertex handoff ∈ source.core) :
    coordinate.vertex handoff = (handoff.arm coordinate.first).terminal :=
  (handoff.arm coordinate.first).firstEntry _
    (coordinate.vertex_mem_arm handoff) coreMember

theorem terminal_mem_core (coordinate : Coordinate handoff) :
    (handoff.arm coordinate.first).terminal ∈ source.core :=
  (handoff.arm coordinate.first).terminal_mem

end Coordinate

theorem arm_length_lt_vertex_card (first : FirstNeighbor handoff) :
    (handoff.arm first).path.length < object.input.vertices.card := by
  letI : FinEnum V := object.input.vertices
  have bound := (handoff.arm first).isPath.length_lt
  simpa [FinEnum.card_eq_fintypeCard] using bound

/-- The predecessor's fan-safe semantics are exposed only on the retained
first-neighbor family.  No statement is made about any other center port. -/
theorem retained_pair_fanSafe
    (left right : FirstNeighbor handoff) (distinct : left ≠ right) :
    FanSafe handoff.center left.1 right.1 :=
  handoff.pairwiseFanSafe left.2 right.2 (by
    intro equal
    apply distinct
    exact Subtype.ext equal)

noncomputable def coordinateEmbedding :
    Coordinate handoff → FirstNeighbor handoff ×
      Fin (object.input.vertices.card + 1) :=
  fun coordinate =>
    ⟨coordinate.1, ⟨coordinate.2.1, by
      have positionLe := coordinate.position_le_length handoff
      have armLt := arm_length_lt_vertex_card handoff coordinate.1
      omega⟩⟩

theorem coordinateEmbedding_injective :
    Function.Injective (coordinateEmbedding handoff) := by
  intro left right equal
  obtain ⟨leftFirst, leftPosition⟩ := left
  obtain ⟨rightFirst, rightPosition⟩ := right
  have firstEqual : leftFirst = rightFirst := congrArg Prod.fst equal
  subst rightFirst
  have positionEqual : leftPosition = rightPosition := by
    apply Fin.ext
    exact congrArg (fun output => output.2.1) equal
  subst rightPosition
  rfl

theorem firstNeighbors_card_eq :
    (firstNeighbors handoff).card = handoff.firstNeighbors.card := by
  letI : DecidableEq V := object.input.vertices.decEq
  letI : FinEnum (FirstNeighbor handoff) := firstNeighbors handoff
  rw [FinEnum.card_eq_fintypeCard]
  simp

def visibleChecks : Nat :=
  handoff.firstNeighbors.card * (object.input.vertices.card + 1)

theorem coordinates_card_le_visibleChecks :
    (coordinates handoff).card ≤ visibleChecks handoff := by
  letI : FinEnum (FirstNeighbor handoff) := firstNeighbors handoff
  letI : (first : FirstNeighbor handoff) →
      FinEnum (ArmPosition handoff first) := fun _ => inferInstance
  rw [FinEnum.card_eq_fintypeCard]
  calc
    Fintype.card (Coordinate handoff) ≤
        Fintype.card (FirstNeighbor handoff ×
          Fin (object.input.vertices.card + 1)) :=
      Fintype.card_le_of_injective (coordinateEmbedding handoff)
        (coordinateEmbedding_injective handoff)
    _ = visibleChecks handoff := by
      rw [Fintype.card_prod, Fintype.card_fin]
      have firstCard := firstNeighbors_card_eq handoff
      rw [FinEnum.card_eq_fintypeCard] at firstCard
      rw [firstCard]
      rfl

theorem firstNeighbors_card_le_vertex_card :
    handoff.firstNeighbors.card ≤ object.input.vertices.card := by
  rw [← object.card_vertexFinset]
  apply Finset.card_le_card
  intro vertex _member
  exact object.mem_vertexFinset vertex

theorem visibleChecks_quadratic :
    visibleChecks handoff ≤
      object.input.vertices.card * (object.input.vertices.card + 1) :=
  Nat.mul_le_mul_right (object.input.vertices.card + 1)
    (firstNeighbors_card_le_vertex_card handoff)

noncomputable def budget : Core.PolynomialCheckBudget Unit where
  size := fun _ => object.input.vertices.card
  checks := fun _ => (coordinates handoff).card
  coefficient := 1
  degree := 2
  bounded := by
    intro _unit
    calc
      (coordinates handoff).card ≤ visibleChecks handoff :=
        coordinates_card_le_visibleChecks handoff
      _ ≤ object.input.vertices.card *
          (object.input.vertices.card + 1) := visibleChecks_quadratic handoff
      _ ≤ 1 * (object.input.vertices.card + 1) ^ 2 := by nlinarith

end StructuralExhaustion.Graph.TypeBDecoratedArmCoordinate
