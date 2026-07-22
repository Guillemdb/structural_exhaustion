import Hypostructure.Core.Finite.Enumeration
import Hypostructure.Core.Budget.Work
import Mathlib.Order.CompleteLattice.Finset

/-!
# Domain-neutral finite maximal selection

This contract is shared by finite graph packings and represented PDE packet
selections.  The producer of the selected family belongs to the domain
contract; Core owns the exact schedule, maximality shape, and work interface.
-/

namespace Hypostructure.Core.Finite.MaximalSelection

open Hypostructure.Core.Finite

universe u

/-! ## Finite maximal-element selection -/

variable {α : Type u}

noncomputable def chooseMaximal [DecidableEq α] [LE α] [IsTrans α (· ≤ ·)]
    (candidates : Finset α) (nonempty : candidates.Nonempty) : α :=
  Classical.choose (candidates.exists_maximal nonempty)

theorem chooseMaximal_mem [DecidableEq α] [LE α] [IsTrans α (· ≤ ·)]
    (candidates : Finset α) (nonempty : candidates.Nonempty) :
    chooseMaximal candidates nonempty ∈ candidates :=
  (Classical.choose_spec (candidates.exists_maximal nonempty)).prop

theorem chooseMaximal_maximal [DecidableEq α] [LE α] [IsTrans α (· ≤ ·)]
    (candidates : Finset α) (nonempty : candidates.Nonempty) :
    Maximal (fun value => value ∈ candidates)
      (chooseMaximal candidates nonempty) :=
  Classical.choose_spec (candidates.exists_maximal nonempty)

structure Choice [DecidableEq α] [LE α] [IsTrans α (· ≤ ·)]
    (candidates : Finset α) (nonempty : candidates.Nonempty) where
  value : α
  mem : value ∈ candidates
  maximal : Maximal (fun candidate => candidate ∈ candidates) value

noncomputable def chooseSelection [DecidableEq α] [LE α] [IsTrans α (· ≤ ·)]
    (candidates : Finset α) (nonempty : candidates.Nonempty) :
    Choice candidates nonempty :=
  { value := chooseMaximal candidates nonempty
    mem := chooseMaximal_mem candidates nonempty
    maximal := chooseMaximal_maximal candidates nonempty }

structure Profile (schedule : Enumeration α) (conflict : α → α → Prop)
    [DecidableRel conflict] where
  selected : List α
  selected_nodup : selected.Nodup
  pairwiseCompatible : ∀ ⦃left right⦄,
    left ∈ selected → right ∈ selected → left ≠ right → ¬ conflict left right
  maximal : ∀ item, item ∈ schedule.values →
    ∃ selectedItem ∈ selected, conflict item selectedItem ∨ item = selectedItem

namespace Profile

variable {α : Type u} {schedule : Enumeration α}
  {conflict : α → α → Prop} [DecidableRel conflict]

def selectedEnumeration (profile : Profile schedule conflict) :
    Enumeration α :=
  letI : DecidableEq α := schedule.decEq
  Enumeration.ofNodupList profile.selected profile.selected_nodup

def packingNumber (profile : Profile schedule conflict) : Nat :=
  profile.selected.length

def workBudget (profile : Profile schedule conflict) :
    Core.PolynomialCheckBudget Unit :=
  Core.PolynomialCheckBudget.constant
    (fun _ => schedule.card * (schedule.card + 1)) schedule.card

theorem selectedEnumeration_card (profile : Profile schedule conflict) :
    profile.selectedEnumeration.card = profile.packingNumber := by
  change profile.selected.length = profile.selected.length
  rfl

theorem checks_within (profile : Profile schedule conflict) :
    profile.workBudget.checks () ≤
      schedule.card * (schedule.card + 1) := by
  simp [workBudget, PolynomialCheckBudget.constant]
  calc
    schedule.card = schedule.card * 1 := by simp
    _ ≤ schedule.card * (schedule.card + 1) := by
      exact Nat.mul_le_mul_left _ (Nat.le_add_left 1 schedule.card)

end Profile

end Hypostructure.Core.Finite.MaximalSelection
