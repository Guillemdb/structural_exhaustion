import Hypostructure.Core.Budget.Dynamic
import Hypostructure.Graph.AssignedSupportCharge
import Hypostructure.Graph.SurplusClasswiseOverload

/-!
# Graph budget umbrella

The graph layer exposes one public budget namespace that collects the reusable
support-charge and classwise-overload surfaces.  Core still owns the generic
numeric budgets; Graph only supplies graph-facing packaging for later nodes
and PDE reuse.
-/

namespace Hypostructure.Graph.Budget

universe u uPrevious uPrevious' uQuantity uNewQuantity

abbrev SupportProfile (object : FiniteObject.{u}) :=
  AssignedSupportCharge.Profile object

abbrev DynamicProfile (Previous : Sort uPrevious) (Quantity : Type uQuantity)
    [Preorder Quantity] :=
  Core.Budget.Dynamic.Profile Previous Quantity

namespace Profile

variable {Previous : Sort uPrevious} {Quantity : Type uQuantity}
variable {Previous' : Sort uPrevious'}
variable {NewQuantity : Type uNewQuantity}
variable [Preorder Quantity] [Preorder NewQuantity]

def reindex
    {Previous' : Sort uPrevious'}
    (project : Previous' -> Previous)
    (profile : DynamicProfile Previous Quantity) :
    DynamicProfile Previous' Quantity :=
  Core.Budget.Dynamic.Profile.reindex (Previous := Previous)
    (Quantity := Quantity) project profile

def map
    (f : Quantity -> NewQuantity)
    (monotone : Monotone f)
    (profile : DynamicProfile Previous Quantity) :
    DynamicProfile Previous NewQuantity :=
  Core.Budget.Dynamic.Profile.map (Previous := Previous)
    (Quantity := Quantity) (NewQuantity := NewQuantity) f monotone profile

end Profile

abbrev CapacityProfile (Class : Type u) :=
  SurplusClasswiseOverload.CapacityProfile Class

abbrev OverloadProfile (Class : Type u) :=
  SurplusClasswiseOverload.OverloadProfile Class

abbrev supportNetQuarterCharge {object : FiniteObject.{u}}
    (profile : SupportProfile object) : Int :=
  profile.netQuarterCharge

theorem supportNetQuarterCharge_eq_augmented_add_centers
    {object : FiniteObject.{u}} (profile : SupportProfile object) :
    profile.netQuarterCharge =
      profile.augmentedQuarterCharge +
        (profile.assignedCenters.card : Int) := by
  exact profile.netQuarterCharge_eq_augmented_add_centers

theorem supportNetQuarterCharge_nonnegative_of_augmented
    {object : FiniteObject.{u}} (profile : SupportProfile object)
    (nonnegative : 0 ≤ profile.augmentedQuarterCharge) :
    0 ≤ profile.netQuarterCharge :=
  profile.netQuarterCharge_nonnegative_of_augmented nonnegative

abbrev totalCapacity {Class : Type u} (profile : CapacityProfile Class) : Nat :=
  profile.totalCapacity

abbrev excess {Class : Type u} (profile : OverloadProfile Class) : Nat :=
  profile.excess

theorem totalCapacity_le {Class : Type u} (profile : CapacityProfile Class) :
    profile.totalCapacity ≤ profile.maxCap * profile.classes.length :=
  profile.totalCapacity_le

theorem excess_pos_iff {Class : Type u} (profile : OverloadProfile Class) :
    0 < profile.excess ↔ profile.totalCapacity < profile.itemCount :=
  profile.excess_pos_iff

abbrev workBudget {Class : Type u} (profile : OverloadProfile Class) :=
  profile.workBudget

abbrev verifiedStage {Class : Type u} (profile : OverloadProfile Class) :=
  profile.verifiedStage

end Hypostructure.Graph.Budget
