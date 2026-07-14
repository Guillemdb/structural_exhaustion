import Mathlib.Tactic
import StructuralExhaustion.Core.Enumeration

namespace StructuralExhaustion.Core.FiniteBoundaryTransfer

open scoped BigOperators

universe u

/-!
# Finite boundary transfer

This module packages a finite family of literal boundary demands.  An item
may contribute several incidences, every incidence requires a fixed number of
integer charge units, and the receiving ledger has an exact number of
available units.  A transfer is an injection between the corresponding `Fin`
types.  Thus it is proof data, not a search over assignments.

The basic theorem is the exact arithmetic alternative: either the injection
exists, or the required number of units is strictly larger than the available
number.  Its proof constructs the monotone `Fin` embedding from a cardinal
inequality.  It never enumerates functions, subsets, or matchings.
-/

structure Profile (Item : Type u) where
  items : FinEnum Item
  multiplicity : Item → Nat
  unitsPerIncidence : Nat
  availableUnits : Nat

namespace Profile

variable {Item : Type u} (profile : Profile Item)

noncomputable def totalIncidences : Nat := by
  letI : DecidableEq Item := profile.items.decEq
  exact ∑ item ∈ profile.items.orderedValues.toFinset,
    profile.multiplicity item

noncomputable def requiredUnits : Nat :=
  profile.unitsPerIncidence * profile.totalIncidences

/-- A literal one-to-one payment of every required boundary unit by one
available ledger unit. -/
abbrev Transfer := Fin profile.requiredUnits ↪ Fin profile.availableUnits

/-- The exact failure state: there are fewer available units than required
boundary units. -/
def Overloaded : Prop :=
  profile.availableUnits < profile.requiredUnits

theorem transfer_or_overloaded :
    Nonempty profile.Transfer ∨ profile.Overloaded := by
  by_cases enough : profile.requiredUnits ≤ profile.availableUnits
  · exact Or.inl ⟨Fin.castLEEmb enough⟩
  · exact Or.inr (by
      unfold Overloaded
      omega)

theorem requiredUnits_le_availableUnits
    (transfer : profile.Transfer) :
    profile.requiredUnits ≤ profile.availableUnits := by
  simpa using Fintype.card_le_of_injective transfer transfer.injective

theorem overloaded_iff_not_nonempty_transfer :
    profile.Overloaded ↔ ¬Nonempty profile.Transfer := by
  constructor
  · intro overloaded transfer
    have enough := profile.requiredUnits_le_availableUnits transfer.some
    exact (Nat.not_le_of_lt overloaded) enough
  · intro noTransfer
    rcases profile.transfer_or_overloaded with transfer | overloaded
    · exact False.elim (noTransfer transfer)
    · exact overloaded

end Profile

end StructuralExhaustion.Core.FiniteBoundaryTransfer
