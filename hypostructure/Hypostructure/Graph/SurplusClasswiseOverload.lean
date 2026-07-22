import Mathlib.Tactic
import Hypostructure.Core.Budget.Work

/-!
# Generic classwise capacity overload helpers

The graph layer owns only the generic capacity comparison: class capacities,
their maximum, total capacity over a finite label family, and excess.  Concrete
classes, labels, and capacity functions are application or CT output data.
-/

namespace Hypostructure.Graph.SurplusClasswiseOverload

universe u

/-- Capacity data for a finite family of labelled classes. -/
structure CapacityProfile (Class : Type u) where
  classes : List Class
  capacity : Class -> Nat
  maxCap : Nat
  capacity_le_maxCap : forall classValue,
    classValue ∈ classes -> capacity classValue <= maxCap

namespace CapacityProfile

variable {Class : Type u}
variable (profile : CapacityProfile Class)

theorem capacity_bound {classValue : Class}
    (member : classValue ∈ profile.classes) :
    profile.capacity classValue <= profile.maxCap := by
  exact profile.capacity_le_maxCap classValue member

def totalCapacity : Nat :=
  (profile.classes.map profile.capacity).sum

private theorem sum_map_le_mul_length (classes : List Class)
    (capacity : Class -> Nat) (cap : Nat)
    (bound : forall classValue, classValue ∈ classes ->
      capacity classValue <= cap) :
    (classes.map capacity).sum <= cap * classes.length := by
  induction classes with
  | nil => simp
  | cons head tail ih =>
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      have headBound : capacity head <= cap := bound head (by simp)
      have tailBound : (tail.map capacity).sum <= cap * tail.length := by
        apply ih
        intro classValue member
        exact bound classValue (by simp [member])
      calc
        capacity head + (tail.map capacity).sum <=
            cap + cap * tail.length :=
          Nat.add_le_add headBound tailBound
        _ = cap * (tail.length + 1) := by
          rw [Nat.mul_succ]
          exact Nat.add_comm _ _

theorem totalCapacity_le :
    profile.totalCapacity <= profile.maxCap * profile.classes.length := by
  unfold totalCapacity
  exact sum_map_le_mul_length profile.classes profile.capacity profile.maxCap
    profile.capacity_le_maxCap

end CapacityProfile

/-- Exact overload comparison over an abstract item count and class capacity. -/
structure OverloadProfile (Class : Type u) where
  capacityProfile : CapacityProfile Class
  itemCount : Nat

namespace OverloadProfile

variable {Class : Type u}
variable (profile : OverloadProfile Class)

def totalCapacity : Nat :=
  profile.capacityProfile.totalCapacity

def excess : Nat :=
  profile.itemCount - profile.totalCapacity

theorem excess_pos_iff :
    0 < profile.excess ↔ profile.totalCapacity < profile.itemCount :=
  Nat.sub_pos_iff_lt

def workBudget : _root_.Hypostructure.Core.PolynomialCheckBudget Unit :=
  _root_.Hypostructure.Core.PolynomialCheckBudget.constant
    (fun _ => profile.capacityProfile.classes.length)
    (profile.itemCount * profile.capacityProfile.classes.length)

structure VerifiedStage : Type u where
  totalCapacity_eq : profile.totalCapacity =
    profile.capacityProfile.totalCapacity
  excess_eq : profile.excess =
    profile.itemCount - profile.totalCapacity
  capacityBound : profile.totalCapacity <=
    profile.capacityProfile.maxCap * profile.capacityProfile.classes.length
  work : profile.workBudget.checks () =
    profile.itemCount * profile.capacityProfile.classes.length

def verifiedStage : profile.VerifiedStage where
  totalCapacity_eq := rfl
  excess_eq := rfl
  capacityBound := profile.capacityProfile.totalCapacity_le
  work := rfl

end OverloadProfile

end Hypostructure.Graph.SurplusClasswiseOverload
