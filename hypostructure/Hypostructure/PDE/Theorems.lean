import Hypostructure.PDE.Obstruction
import Hypostructure.PDE.OneThreeRepair
import Hypostructure.PDE.Progress
import Hypostructure.PDE.TargetClosure

/-!
# Reusable PDE theorem profiles

This barrel mirrors Graph's theorem-profile namespace.  It only re-exports
generic PDE capabilities; a concrete regularity proof supplies the analytic
predicates and certificates.
-/

namespace Hypostructure.PDE.Theorems

universe u uPattern uMeasure

abbrev obstructionHas (M : LocalModel.{u})
    (profile : Obstruction.Profile M) (object : M.problem.Ambient) :=
  Obstruction.Has profile object
abbrev obstructionFree (M : LocalModel.{u})
    (profile : Obstruction.Profile M) (object : M.problem.Ambient) :=
  Obstruction.Free profile object
abbrev progressProfile (M : LocalModel.{u}) :=
  Progress.Profile M
abbrev targetAvoidance (M : LocalModel.{u})
    (Target : M.problem.Ambient -> Prop) :=
  TargetClosure.AvoidsTarget M Target

def repairedInternal {P : Core.Problem.{u, u}}
    (component : OneThreeRepair.Component P) :=
  OneThreeRepair.repairedInternal component
theorem repairedInternal_eq {P : Core.Problem.{u, u}}
    (component : OneThreeRepair.Component P) :
    component.internal = repairedInternal component :=
  OneThreeRepair.repairedInternal_eq component

end Hypostructure.PDE.Theorems
