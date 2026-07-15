import StructuralExhaustion.CT9.Theorems

namespace StructuralExhaustion.CT9.ExactLedger

open StructuralExhaustion

universe uAmbient uBranch uItem uLabel

/-!
# Exact finite function ledgers

This is the reusable CT9 profile for manuscript ledgers in which every
authored item is assigned exactly one finite label.  The runner may still be
used for overload search; the theorem below exposes the exact no-overcounting
identity independently of any capacity choice.
-/

def capability (P : Core.Problem.{uAmbient, uBranch})
    (Item : Type uItem) (Label : Type uLabel) (labels : FinEnum Label)
    (assign : Item → Label) (capacity : Label → Nat := fun _ => 0) :
    CT9.Capability P where
  Item := Item
  Label := Label
  labels := labels
  label := assign
  capacity := capacity

def input {P : Core.Problem.{uAmbient, uBranch}}
    {Item : Type uItem} {Label : Type uLabel} {labels : FinEnum Label}
    {assign : Item → Label} {capacity : Label → Nat}
    (context : Core.BranchContext P) (items : Core.OrderedCollection Item) :
    CT9.Input (capability P Item Label labels assign capacity) :=
  ⟨context, items⟩

theorem noOvercounting {P : Core.Problem.{uAmbient, uBranch}}
    {Item : Type uItem} {Label : Type uLabel} (labels : FinEnum Label)
    (assign : Item → Label) (context : Core.BranchContext P)
    (items : Core.OrderedCollection Item) :
    items.values.length =
      (labels.orderedValues.map fun label =>
        CT9.fibreCount
          (capability P Item Label labels assign)
          (input (capacity := fun _ => 0) context items) label).sum :=
  by
    simpa [capability, input] using
      (CT9.cardinality_eq_sum_fibreCount
        (capability P Item Label labels assign (fun _ => 0))
        (input (capacity := fun _ => 0) context items))

theorem bounded_total {P : Core.Problem.{uAmbient, uBranch}}
    {Item : Type uItem} {Label : Type uLabel} (labels : FinEnum Label)
    (assign : Item → Label) (context : Core.BranchContext P)
    (items : Core.OrderedCollection Item) (bound : Nat)
    (bounded : ∀ label,
      CT9.fibreCount
        (capability P Item Label labels assign)
        (input (capacity := fun _ => 0) context items) label ≤ bound) :
    items.values.length ≤ bound * labels.card := by
  rw [noOvercounting labels assign context items]
  have pointwise : ∀ values : List Label,
      (values.map fun label =>
        CT9.fibreCount
          (capability P Item Label labels assign)
          (input (capacity := fun _ => 0) context items) label).sum ≤
        (values.map fun _ => bound).sum := by
    intro values
    induction values with
    | nil => rfl
    | cons label tail ih =>
        simp only [List.map_cons, List.sum_cons]
        exact Nat.add_le_add (bounded label) ih
  calc
    (labels.orderedValues.map fun label =>
      CT9.fibreCount
        (capability P Item Label labels assign)
        (input (capacity := fun _ => 0) context items) label).sum ≤
        (labels.orderedValues.map fun _ => bound).sum := by
      exact pointwise labels.orderedValues
    _ = bound * labels.card := by
      simp [Nat.mul_comm]

end StructuralExhaustion.CT9.ExactLedger
