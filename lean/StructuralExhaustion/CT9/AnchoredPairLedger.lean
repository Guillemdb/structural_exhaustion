import StructuralExhaustion.CT9.ExactLedger
import StructuralExhaustion.Core.EnumerationCombinators

namespace StructuralExhaustion.CT9.AnchoredPairLedger

open StructuralExhaustion

universe uAmbient uBranch uItem

/-!
# Canonical endpoint ledgers for finite pair schedules

Every canonically ordered pair is assigned to its first endpoint.  The
resulting CT9 fibres are exact stars: two members of one fibre have the same
first endpoint.  This module contains only finite bookkeeping.  In
particular, it makes no graph-theoretic claim about how an overloaded star is
consumed.
-/

abbrev Pair {Item : Type uItem} (items : FinEnum Item) :=
  Core.Enumeration.OrderedDistinctPair items

@[implicit_reducible]
def pairs {Item : Type uItem} (items : FinEnum Item) : FinEnum (Pair items) :=
  Core.Enumeration.orderedDistinctPairs items

def anchor {Item : Type uItem} {items : FinEnum Item} (pair : Pair items) : Item :=
  Core.Enumeration.OrderedDistinctPair.first pair

def capability (P : Core.Problem.{uAmbient, uBranch})
    {Item : Type uItem} (items : FinEnum Item)
    (capacity : Item → Nat := fun _ ↦ 0) : CT9.Capability P :=
  CT9.ExactLedger.capability P (Pair items) Item items anchor capacity

def input {P : Core.Problem.{uAmbient, uBranch}}
    {Item : Type uItem} {items : FinEnum Item} {capacity : Item → Nat}
    (context : Core.BranchContext P) : CT9.Input (capability P items capacity) :=
  CT9.ExactLedger.input context (pairs items).toOrderedCollection

/-- Every scheduled pair is counted in exactly one anchor fibre. -/
theorem noOvercounting {P : Core.Problem.{uAmbient, uBranch}}
    {Item : Type uItem} (items : FinEnum Item)
    (context : Core.BranchContext P) :
    (pairs items).orderedValues.length =
      (items.orderedValues.map fun item ↦
        CT9.fibreCount
          (capability P items)
          (input (capacity := fun _ ↦ 0) context) item).sum := by
  exact CT9.ExactLedger.noOvercounting items anchor context
    (pairs items).toOrderedCollection

/-- Membership in an anchor fibre exposes the common first endpoint. -/
theorem anchor_eq_of_mem_fibre {P : Core.Problem.{uAmbient, uBranch}}
    {Item : Type uItem} {items : FinEnum Item}
    (context : Core.BranchContext P) {item : Item} {pair : Pair items}
    (member : pair ∈ CT9.fibre
      (capability P items)
      (input (capacity := fun _ ↦ 0) context) item) :
    anchor pair = item := by
  letI : DecidableEq Item := items.decEq
  change pair ∈ (pairs items).orderedValues.filter
    (fun current ↦ anchor current = item) at member
  exact of_decide_eq_true (List.mem_filter.mp member).2

/-- Any two members of one fibre form a literal star at the supplied anchor. -/
theorem same_anchor_of_mem_fibre {P : Core.Problem.{uAmbient, uBranch}}
    {Item : Type uItem} {items : FinEnum Item}
    (context : Core.BranchContext P) {item : Item}
    {left right : Pair items}
    (leftMember : left ∈ CT9.fibre
      (capability P items)
      (input (capacity := fun _ ↦ 0) context) item)
    (rightMember : right ∈ CT9.fibre
      (capability P items)
      (input (capacity := fun _ ↦ 0) context) item) :
    anchor left = anchor right := by
  exact (anchor_eq_of_mem_fibre context leftMember).trans
    (anchor_eq_of_mem_fibre context rightMember).symm

/-- A uniform bound on the exact star fibres bounds the whole pair schedule. -/
theorem bounded_total {P : Core.Problem.{uAmbient, uBranch}}
    {Item : Type uItem} (items : FinEnum Item)
    (context : Core.BranchContext P) (bound : Nat)
    (bounded : ∀ item,
      CT9.fibreCount
        (capability P items)
        (input (capacity := fun _ ↦ 0) context) item ≤ bound) :
    (pairs items).orderedValues.length ≤ bound * items.card := by
  exact CT9.ExactLedger.bounded_total items anchor context
    (pairs items).toOrderedCollection bound bounded

/-- Constructing the pair schedule is quadratic in the authored item count. -/
theorem pairCount_le_square {Item : Type uItem} (items : FinEnum Item) :
    (pairs items).card ≤ items.card ^ 2 :=
  Core.Enumeration.orderedDistinctPairs_card_le_square items

end StructuralExhaustion.CT9.AnchoredPairLedger
