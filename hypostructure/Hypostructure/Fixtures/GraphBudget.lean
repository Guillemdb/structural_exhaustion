import Hypostructure.Fixtures.GraphBasics
import Hypostructure.Graph.Budget

/-!
# Graph budget fixture

This fixture exercises the public graph budget umbrella on a concrete finite
graph object and on a finite classwise overload profile.
-/

namespace Hypostructure.Fixtures.GraphBudget

open Hypostructure.Graph.Budget
open Hypostructure.Fixtures.GraphBasics

def supportProfile : SupportProfile GraphBasics.k4 where
  augmentedQuarterCharge := 0
  assignedCenters := {1}

theorem supportProfile_netQuarterCharge_eq :
    supportProfile.netQuarterCharge =
      supportProfile.augmentedQuarterCharge +
        (supportProfile.assignedCenters.card : Int) := by
  simpa using
    supportNetQuarterCharge_eq_augmented_add_centers supportProfile

noncomputable def energyProfile : DynamicProfile Unit ℝ where
  value := Hypostructure.Core.Residual.Query.ofFunction fun _ => (3 : ℝ) / 2
  budget := Hypostructure.Core.Residual.Query.ofFunction fun _ => (2 : ℝ)
  within := by
    intro _
    change (3 : ℝ) / 2 ≤ 2
    norm_num

def capacityProfile : CapacityProfile (Fin 2) where
  classes := [0, 1]
  capacity := fun _ => 1
  maxCap := 1
  capacity_le_maxCap := by
    intro classValue member
    simp

theorem capacityProfile_totalCapacity_le :
    capacityProfile.totalCapacity ≤
      capacityProfile.maxCap * capacityProfile.classes.length := by
  simpa using totalCapacity_le capacityProfile

def overloadProfile : OverloadProfile (Fin 2) where
  capacityProfile := capacityProfile
  itemCount := 3

theorem overloadProfile_excess_pos_iff :
    0 < overloadProfile.excess ↔
      overloadProfile.totalCapacity < overloadProfile.itemCount := by
  simpa using excess_pos_iff overloadProfile

theorem energyProfile_current_le_limit :
    energyProfile.current () <= energyProfile.limit () := by
  change (3 : ℝ) / 2 ≤ 2
  norm_num

#print axioms supportProfile_netQuarterCharge_eq
#print axioms energyProfile_current_le_limit
#print axioms capacityProfile_totalCapacity_le
#print axioms overloadProfile_excess_pos_iff

end Hypostructure.Fixtures.GraphBudget
