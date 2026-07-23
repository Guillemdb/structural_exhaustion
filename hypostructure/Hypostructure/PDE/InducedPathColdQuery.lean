import Hypostructure.PDE.InducedPathCold

/-!# Residual-query projections for PDE cold windows -/

namespace Hypostructure.PDE.InducedPathCold.QuerySurface

universe uPrevious uWindow

open Hypostructure

def coldValuesQuery {Previous : Type uPrevious}
    (profile : InducedPathCold.Profile Previous) :
    Core.Residual.Query Previous
      (fun previous => List (profile.Window previous)) :=
  profile.schedule.map fun previous _schedule =>
    InducedPathCold.coldValues profile previous

noncomputable def coldWindowScheduleQuery {Previous : Type uPrevious}
    (profile : InducedPathCold.Profile Previous) :
    Core.Residual.Query Previous
      (fun previous => Core.Finite.Enumeration (profile.Window previous)) :=
  profile.schedule.dependentMap fun previous _schedule => by
    letI : DecidableEq (profile.Window previous) := Classical.decEq _
    exact Core.Finite.Enumeration.ofNodupList
      (InducedPathCold.coldValues profile previous)
      (InducedPathCold.coldValues_nodup profile previous)

end Hypostructure.PDE.InducedPathCold.QuerySurface
