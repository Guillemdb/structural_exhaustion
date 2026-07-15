import StructuralExhaustion.Core.Enumeration
import Mathlib.Data.Fintype.BigOperators

namespace StructuralExhaustion.Core.BooleanStateEntropy

universe uCoordinate uState

/-!
# Exact Boolean-state realization

This is the finite contract needed before a coordinate ledger can be charged
as independent Boolean entropy.  Pairwise distinguishability, injectivity of a
quotient code, and the absence of a rank drop do not by themselves provide
this contract: the application must supply a state realizing every Boolean
assignment.

The theorem is proof-level.  It does not enumerate assignments or states.
-/

/-- A finite coordinate family realizes every Boolean assignment inside a
finite state family. -/
structure Profile where
  Coordinate : Type uCoordinate
  State : Type uState
  coordinates : FinEnum Coordinate
  states : FinEnum State
  value : State → Coordinate → Bool
  realizes : ∀ assignment : Coordinate → Bool,
    ∃ state, value state = assignment

namespace Profile

variable (profile : Profile)

noncomputable def realizingState (assignment : profile.Coordinate → Bool) :
    profile.State :=
  Classical.choose (profile.realizes assignment)

theorem realizingState_spec (assignment : profile.Coordinate → Bool) :
    profile.value (profile.realizingState assignment) = assignment :=
  Classical.choose_spec (profile.realizes assignment)

/-- Distinct Boolean assignments require distinct realized states. -/
theorem realizingState_injective :
    Function.Injective profile.realizingState := by
  intro left right equal
  rw [← profile.realizingState_spec left,
    ← profile.realizingState_spec right, equal]

/-- Exact finite entropy consequence of realizing the complete Boolean cube. -/
theorem two_pow_coordinateCard_le_stateCard :
    2 ^ profile.coordinates.card ≤ profile.states.card := by
  letI : FinEnum profile.Coordinate := profile.coordinates
  letI : FinEnum profile.State := profile.states
  letI : DecidableEq profile.Coordinate := profile.coordinates.decEq
  letI : Fintype profile.Coordinate :=
    @FinEnum.instFintype _ profile.coordinates
  letI : Fintype profile.State := @FinEnum.instFintype _ profile.states
  have bound := Fintype.card_le_of_injective
    profile.realizingState profile.realizingState_injective
  simpa [FinEnum.card_eq_fintypeCard] using bound

end Profile

end StructuralExhaustion.Core.BooleanStateEntropy
