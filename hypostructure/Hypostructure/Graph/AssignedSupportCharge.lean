import Hypostructure.Graph.Finite

/-!
# Assigned support charge

This graph adapter packages the common support-accounting view where a signed
support contribution is augmented by a finite set of assigned centers.  The
arithmetic is domain-neutral integer bookkeeping; the graph layer only fixes
the center carrier to the selected graph's vertex type.
-/

namespace Hypostructure.Graph.AssignedSupportCharge

universe u

/-- Graph-facing support-charge profile.  Problem contracts supply the exact
augmented charge and the assigned center set; Graph derives the net charge and
its basic accounting laws. -/
structure Profile (object : FiniteObject.{u}) where
  augmentedQuarterCharge : Int
  assignedCenters : Finset object.Vertex

namespace Profile

variable {object : FiniteObject.{u}} (profile : Profile object)

/-- Net quarter-charge after each assigned center contributes one unit. -/
def netQuarterCharge : Int :=
  profile.augmentedQuarterCharge + (profile.assignedCenters.card : Int)

@[simp] theorem netQuarterCharge_eq_augmented_add_centers :
    profile.netQuarterCharge =
      profile.augmentedQuarterCharge +
        (profile.assignedCenters.card : Int) :=
  rfl

theorem netQuarterCharge_nonnegative_of_augmented
    (nonnegative : 0 ≤ profile.augmentedQuarterCharge) :
    0 ≤ profile.netQuarterCharge := by
  unfold netQuarterCharge
  exact add_nonneg nonnegative (Int.natCast_nonneg _)

end Profile

end Hypostructure.Graph.AssignedSupportCharge
