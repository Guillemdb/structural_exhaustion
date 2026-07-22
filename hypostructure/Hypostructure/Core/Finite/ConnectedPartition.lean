import Hypostructure.Core.Finite.Partition

/-!
# Ordered component partitions

Domain-neutral ordered component-style partitions are the generic carrier-side part of
node-local support decompositions. The core owns the deduplicated component order,
component member sets, coverage, disjointness, and linear work bounds. Graph and
PDE adapters add the semantic meaning of each abstract component.
-/

namespace Hypostructure.Core.Finite.ConnectedPartition

open Hypostructure.Core.Finite

universe uCarrier uLabel

variable {Carrier : Type uCarrier} {Label : Type uLabel}

/-- Ordered component labels induced from an exact finite schedule. -/
noncomputable def order (schedule : Enumeration Carrier) (labelOf : Carrier -> Label) :
    List Label :=
  OrderedPartition.labels schedule labelOf

/-- Carrier entries assigned to one ordered label. -/
noncomputable def members (schedule : Enumeration Carrier) (labelOf : Carrier -> Label)
    (label : Label) : Finset Carrier :=
  OrderedPartition.members schedule labelOf label

@[simp] theorem mem_members_iff (schedule : Enumeration Carrier)
    (labelOf : Carrier -> Label) (label : Label) (carrier : Carrier) :
    carrier ∈ members schedule labelOf label ↔
      carrier ∈ schedule.values ∧ labelOf carrier = label := by
  unfold members
  exact OrderedPartition.mem_members_iff schedule labelOf label carrier

/-- Labels are disjoint by construction. -/
theorem members_disjoint (schedule : Enumeration Carrier)
    (labelOf : Carrier -> Label) {left right : Label}
    (different : left ≠ right) :
    Disjoint (members schedule labelOf left) (members schedule labelOf right) := by
  exact OrderedPartition.members_disjoint schedule labelOf different

/-- Every scheduled entry belongs to the component of its own label. -/
theorem mem_label_iff_mem_component (schedule : Enumeration Carrier)
    (labelOf : Carrier -> Label) (carrier : Carrier) :
    carrier ∈ schedule.values ↔
      ∃ component ∈ order schedule labelOf, carrier ∈ members schedule labelOf component := by
  constructor
  · intro carrierMem
    refine ⟨labelOf carrier, ?_, by
      exact (mem_members_iff schedule labelOf (labelOf carrier) carrier).2
        ⟨carrierMem, rfl⟩⟩
    exact (OrderedPartition.labels_complete schedule labelOf (labelOf carrier)).2
      ⟨carrier, carrierMem, rfl⟩
  · rintro ⟨component, _componentMem, carrierMem⟩
    exact (mem_members_iff schedule labelOf component carrier).mp carrierMem |>.1

/-- Component labels are nodup in the exact induced order. -/
theorem order_nodup (schedule : Enumeration Carrier) (labelOf : Carrier -> Label) :
    (order schedule labelOf).Nodup := by
  exact OrderedPartition.labels_nodup schedule labelOf

/-- At most one component introduction per scheduled entry. -/
theorem order_length_le (schedule : Enumeration Carrier)
    (labelOf : Carrier -> Label) :
    (order schedule labelOf).length ≤ schedule.card := by
  exact OrderedPartition.labels_length_le schedule labelOf

/-- Scan budget for this decomposition. -/
def checks (schedule : Enumeration Carrier) : Nat := schedule.card

theorem checks_linear (schedule : Enumeration Carrier) :
    checks schedule ≤ schedule.card := le_rfl

end Hypostructure.Core.Finite.ConnectedPartition
