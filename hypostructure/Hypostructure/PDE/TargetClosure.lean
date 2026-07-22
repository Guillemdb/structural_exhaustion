import Hypostructure.Core.Closure
import Hypostructure.PDE.Model

/-!
PDE target-hit closure.

The core framework owns the closure mechanism; this module only supplies a
minimal PDE-side compatibility alias used by PDE branches when a local witness
realizes an external PDE target.
-/

namespace Hypostructure.PDE.TargetClosure

open Hypostructure.Core

universe u v

/-- A residual-owned PDE target-avoidance fact. -/
abbrev AvoidsTarget (M : LocalModel.{u})
    (Target : M.problem.Ambient -> Prop) :=
  Closure.TargetAvoidance Target

/-- A local certificate-to-target bridge. -/
abbrev HitBridge
    (M : LocalModel.{u}) (Target : M.problem.Ambient -> Prop)
    (object : M.problem.Ambient) (Hit : Type v) :=
  Closure.TargetWitnessBridge Target object Hit

/-- Close a PDE branch when a locally witnessed target contradicts inherited
avoidance. -/
def closeHit
    {M : LocalModel.{u}} {Target : M.problem.Ambient -> Prop}
    {object : M.problem.Ambient} {Hit : Type v}
    (avoidance : AvoidsTarget M Target object)
    (bridge : HitBridge M Target object Hit) (hit : Hit) :
    Closure.Result False :=
  Closure.closeTargetHit avoidance bridge hit

end Hypostructure.PDE.TargetClosure
