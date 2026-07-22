import Hypostructure.PDE.Budget

/-!
# PDE budget fixture

This fixture exercises the Core dynamic-budget contract through the PDE
namespace on a simple residual-indexed energy profile.
-/

namespace Hypostructure.Fixtures.PDEBudget

open Hypostructure.PDE.Budget

noncomputable def energyProfile : Profile Unit ℝ where
  value := Hypostructure.Core.Residual.Query.ofFunction fun _ => (3 : ℝ) / 2
  budget := Hypostructure.Core.Residual.Query.ofFunction fun _ => (2 : ℝ)
  within := by
    intro _
    change (3 : ℝ) / 2 ≤ 2
    norm_num

theorem energyProfile_current_le_limit :
    energyProfile.current () <= energyProfile.limit () := by
  exact Hypostructure.Core.Budget.Dynamic.Profile.current_le_limit energyProfile ()

#print axioms energyProfile_current_le_limit

end Hypostructure.Fixtures.PDEBudget
