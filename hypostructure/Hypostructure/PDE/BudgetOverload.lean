import Mathlib.Tactic
import Hypostructure.Core.Budget.Work

/-!
# PDE classwise capacity overload

PDE packet classes, profile labels, and channels use the same generic capacity
comparison as the Graph specialization.  This module keeps the PDE-facing
namespace and derives no analytic estimate.
-/

namespace Hypostructure.PDE.Budget.Overload

universe u

structure CapacityProfile (Class : Type u) where
  classes : List Class
  capacity : Class -> Nat
  maxCapacity : Nat
  capacity_le_max : forall classValue, classValue ∈ classes ->
    capacity classValue ≤ maxCapacity

def totalCapacity {Class : Type u} (profile : CapacityProfile Class) : Nat :=
  (profile.classes.map profile.capacity).sum

private theorem sumCapacity_le_mul_length {Class : Type u}
    (classes : List Class) (capacity : Class -> Nat) (cap : Nat)
    (bound : ∀ classValue, classValue ∈ classes ->
      capacity classValue ≤ cap) :
    (classes.map capacity).sum ≤ cap * classes.length := by
  induction classes with
  | nil => simp
  | cons head tail ih =>
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      have headBound : capacity head ≤ cap := bound head (by simp)
      have tailBound : (tail.map capacity).sum ≤ cap * tail.length := by
        apply ih
        intro classValue member
        exact bound classValue (by simp [member])
      calc
        capacity head + (tail.map capacity).sum ≤
            cap + cap * tail.length :=
          Nat.add_le_add headBound tailBound
        _ = cap * (tail.length + 1) := by
          rw [Nat.mul_succ]
          exact Nat.add_comm _ _

theorem totalCapacity_le {Class : Type u}
    (profile : CapacityProfile Class) :
    totalCapacity profile ≤ profile.maxCapacity * profile.classes.length := by
  exact sumCapacity_le_mul_length profile.classes profile.capacity
    profile.maxCapacity profile.capacity_le_max

structure OverloadProfile (Class : Type u) where
  capacity : CapacityProfile Class
  itemCount : Nat

def excess {Class : Type u} (profile : OverloadProfile Class) : Nat :=
  profile.itemCount - totalCapacity profile.capacity

theorem excess_pos_iff {Class : Type u}
    (profile : OverloadProfile Class) :
  0 < excess profile ↔ totalCapacity profile.capacity < profile.itemCount :=
  Nat.sub_pos_iff_lt

def workBudget {Class : Type u} (profile : OverloadProfile Class) :
    _root_.Hypostructure.Core.PolynomialCheckBudget Unit :=
  _root_.Hypostructure.Core.PolynomialCheckBudget.constant
    (fun _ => profile.capacity.classes.length)
    (profile.itemCount * profile.capacity.classes.length)

structure VerifiedStage {Class : Type u}
    (profile : OverloadProfile Class) : Type u where
  totalCapacity_eq : totalCapacity profile.capacity =
    (profile.capacity.classes.map profile.capacity.capacity).sum
  excess_eq : excess profile = profile.itemCount - totalCapacity profile.capacity
  capacityBound : totalCapacity profile.capacity ≤
    profile.capacity.maxCapacity * profile.capacity.classes.length
  work : (workBudget profile).checks () =
    profile.itemCount * profile.capacity.classes.length

def verifiedStage {Class : Type u} (profile : OverloadProfile Class) :
    VerifiedStage profile where
  totalCapacity_eq := rfl
  excess_eq := rfl
  capacityBound := totalCapacity_le profile.capacity
  work := rfl

end Hypostructure.PDE.Budget.Overload
