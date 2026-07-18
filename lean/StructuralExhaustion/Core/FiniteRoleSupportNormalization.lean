import Mathlib.Data.Fintype.BigOperators
import StructuralExhaustion.Core.EnumerationCombinators

namespace StructuralExhaustion.Core.FiniteRoleSupportNormalization

universe uRole uVertex uKind uLabel uValue uCoordinate

/-!
# Finite normalization through a fixed carrier-role interface

This is the reusable normalization used when a proof has already produced a
finite coordinate schedule and every retained coordinate is supported on a
fixed finite interface.  The implementation maps only those produced
coordinates.  The full code alphabet is used solely in a symbolic cardinality
theorem and is never enumerated.
-/

variable {Role : Type uRole} {Vertex : Type uVertex}
variable {Kind : Type uKind} {Label : Type uLabel} {Value : Type uValue}
variable {Coordinate : Type uCoordinate}

structure Profile (Role : Type uRole) (Vertex : Type uVertex)
    (Kind : Type uKind) (Label : Type uLabel) (Value : Type uValue)
    (Coordinate : Type uCoordinate) where
  roles : FinEnum Role
  vertexDecEq : DecidableEq Vertex
  roleVertex : Role → Vertex
  carrier : Finset Vertex
  memCarrier_iff_role : ∀ vertex,
    vertex ∈ carrier ↔ ∃ role, roleVertex role = vertex
  coordinates : FinEnum Coordinate
  kind : Coordinate → Kind
  label : Coordinate → Label
  support : Coordinate → Finset Vertex
  supportContained : ∀ coordinate, support coordinate ⊆ carrier
  value : Coordinate → Value

namespace Profile

variable (profile : Profile Role Vertex Kind Label Value Coordinate)
variable [Fintype Role] [Fintype Kind] [Fintype Label] [Fintype Value]
variable [DecidableEq Role] [DecidableEq Kind] [DecidableEq Label]
variable [DecidableEq Value]

abbrev Code (Role : Type uRole) (Kind : Type uKind) (Label : Type uLabel)
    (Value : Type uValue) := Kind × Label × (Role → Bool) × Value

noncomputable def supportMask (coordinate : Coordinate) : Role → Bool := by
  letI : DecidableEq Vertex := profile.vertexDecEq
  exact fun role => decide (profile.roleVertex role ∈ profile.support coordinate)

noncomputable def code (coordinate : Coordinate) : Code Role Kind Label Value :=
  (profile.kind coordinate, profile.label coordinate,
    profile.supportMask coordinate, profile.value coordinate)

theorem code_card :
    Fintype.card (Code Role Kind Label Value) =
      Fintype.card Kind * Fintype.card Label *
        2 ^ Fintype.card Role * Fintype.card Value := by
  simp only [Fintype.card_prod, Fintype.card_fun, Fintype.card_bool]
  simp [Nat.mul_assoc]

theorem support_eq_of_mask_eq {left right : Coordinate}
    (equal : profile.supportMask left = profile.supportMask right) :
    profile.support left = profile.support right := by
  letI : DecidableEq Vertex := profile.vertexDecEq
  apply Finset.ext
  intro vertex
  constructor
  · intro leftMember
    have carrierMember := profile.supportContained left leftMember
    obtain ⟨role, roleExact⟩ := (profile.memCarrier_iff_role vertex).mp carrierMember
    have bitEqual := congrFun equal role
    have leftTrue : profile.supportMask left role = true := by
      simp [supportMask, roleExact, leftMember]
    have rightTrue : profile.supportMask right role = true := by
      rw [← bitEqual]
      exact leftTrue
    simpa [supportMask, roleExact] using of_decide_eq_true rightTrue
  · intro rightMember
    have carrierMember := profile.supportContained right rightMember
    obtain ⟨role, roleExact⟩ := (profile.memCarrier_iff_role vertex).mp carrierMember
    have bitEqual := congrFun equal role
    have rightTrue : profile.supportMask right role = true := by
      simp [supportMask, roleExact, rightMember]
    have leftTrue : profile.supportMask left role = true := by
      rw [bitEqual]
      exact rightTrue
    simpa [supportMask, roleExact] using of_decide_eq_true leftTrue

structure StructuralValue (Vertex : Type uVertex) (Kind : Type uKind)
    (Label : Type uLabel) (Value : Type uValue) where
  kind : Kind
  label : Label
  support : Finset Vertex
  value : Value

theorem StructuralValue.eq_of_fields
    {left right : StructuralValue Vertex Kind Label Value}
    (kindEqual : left.kind = right.kind)
    (labelEqual : left.label = right.label)
    (supportEqual : left.support = right.support)
    (valueEqual : left.value = right.value) : left = right := by
  cases left
  cases right
  simp only [StructuralValue.mk.injEq] at kindEqual labelEqual supportEqual valueEqual ⊢
  exact ⟨kindEqual, labelEqual, supportEqual, valueEqual⟩

noncomputable def structuralValue (coordinate : Coordinate) :
    StructuralValue Vertex Kind Label Value where
  kind := profile.kind coordinate
  label := profile.label coordinate
  support := profile.support coordinate
  value := profile.value coordinate

theorem code_eq_implies_structuralValue_eq {left right : Coordinate}
    (equal : profile.code left = profile.code right) :
    profile.structuralValue left = profile.structuralValue right := by
  have kindEqual := congrArg
    (fun code : Code Role Kind Label Value => code.1) equal
  have labelEqual := congrArg
    (fun code : Code Role Kind Label Value => code.2.1) equal
  have maskEqual := congrArg
    (fun code : Code Role Kind Label Value => code.2.2.1) equal
  have valueEqual := congrArg
    (fun code : Code Role Kind Label Value => code.2.2.2) equal
  apply StructuralValue.eq_of_fields
  · simpa [structuralValue, code] using kindEqual
  · simpa [structuralValue, code] using labelEqual
  · exact profile.support_eq_of_mask_eq maskEqual
  · simpa [structuralValue, code] using valueEqual

noncomputable def normalizedCodes : List (Code Role Kind Label Value) := by
  classical
  exact (profile.coordinates.orderedValues.map profile.code).dedup

theorem normalizedCodes_nodup : profile.normalizedCodes.Nodup := by
  classical
  exact List.nodup_dedup _

theorem every_coordinate_has_normalizedCode (coordinate : Coordinate) :
    profile.code coordinate ∈ profile.normalizedCodes := by
  classical
  simp [normalizedCodes]

theorem normalizedCodes_length_le_card :
    profile.normalizedCodes.length ≤
      Fintype.card (Code Role Kind Label Value) :=
  profile.normalizedCodes_nodup.length_le_card

theorem normalizedCodes_length_le_symbolic :
    profile.normalizedCodes.length ≤
      Fintype.card Kind * Fintype.card Label *
        2 ^ Fintype.card Role * Fintype.card Value := by
  rw [← code_card (Role := Role) (Kind := Kind) (Label := Label)
    (Value := Value)]
  exact profile.normalizedCodes_length_le_card

end Profile

end StructuralExhaustion.Core.FiniteRoleSupportNormalization
