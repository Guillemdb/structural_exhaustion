import StructuralExhaustion.Core.FiniteSearch

namespace StructuralExhaustion.Core.FinitePredicateAlignment

universe u

/-! An exact first-disagreement scan for two predicates on one declared finite
universe.  The runner never chooses an ambient universe: every inspected
coordinate comes from `coordinates`. -/

structure Profile where
  Coordinate : Type u
  coordinates : FinEnum Coordinate
  left : Coordinate → Prop
  right : Coordinate → Prop
  leftDecidable : ∀ coordinate, Decidable (left coordinate)
  rightDecidable : ∀ coordinate, Decidable (right coordinate)

namespace Profile

variable (profile : Profile)

def Mismatch (coordinate : profile.Coordinate) : Prop :=
  ¬(profile.left coordinate ↔ profile.right coordinate)

def mismatchDecidable (coordinate : profile.Coordinate) :
    Decidable (profile.Mismatch coordinate) := by
  unfold Mismatch
  exact @instDecidableNot _
    (@instDecidableIff _ _ (profile.leftDecidable coordinate)
      (profile.rightDecidable coordinate))

inductive Decision where
  | mismatch
      (hit : FiniteSearch.FirstHit profile.coordinates.orderedValues
        profile.Mismatch)
  | aligned (exact : ∀ coordinate,
      profile.left coordinate ↔ profile.right coordinate)

def decide : profile.Decision :=
  match FiniteSearch.first profile.coordinates profile.Mismatch
      profile.mismatchDecidable with
  | .found hit => .mismatch hit
  | .absent absent => .aligned fun coordinate => by
      by_contra mismatch
      exact absent coordinate
        (profile.coordinates.mem_orderedValues coordinate) mismatch

theorem decide_total :
    (∃ hit, profile.decide = .mismatch hit) ∨
      (∃ exact, profile.decide = .aligned exact) := by
  cases equation : profile.decide with
  | mismatch hit => exact Or.inl ⟨hit, rfl⟩
  | aligned exact => exact Or.inr ⟨exact, rfl⟩

theorem mismatch_sound
    (hit : FiniteSearch.FirstHit profile.coordinates.orderedValues
      profile.Mismatch) :
    profile.Mismatch hit.value :=
  hit.holds

theorem mismatch_prefix_exact
    (hit : FiniteSearch.FirstHit profile.coordinates.orderedValues
      profile.Mismatch) :
    ∀ coordinate, coordinate ∈ hit.before →
      (profile.left coordinate ↔ profile.right coordinate) := by
  intro coordinate member
  exact not_not.mp (hit.beforeAbsent coordinate member)

def checks : Nat := profile.coordinates.card

end Profile

end StructuralExhaustion.Core.FinitePredicateAlignment
