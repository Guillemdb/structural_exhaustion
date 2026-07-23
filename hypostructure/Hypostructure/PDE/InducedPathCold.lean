import Hypostructure.Core.Finite.Enumeration
import Hypostructure.Core.Residual.Query

/-!# PDE cold-window contracts

Cold branches are represented by finite window schedules and a caller-owned
coldness predicate.  The PDE layer supplies analytic meaning (small flux,
regular profile, or inactive defect); Core/CT layers consume only the ordered
schedule and decision.
-/

namespace Hypostructure.PDE.InducedPathCold

universe uPrevious uWindow

open Hypostructure

structure Profile (Previous : Type uPrevious) where
  Window : Previous -> Type uWindow
  schedule : Core.Residual.Query Previous
    (fun previous => Core.Finite.Enumeration (Window previous))
  cold : (previous : Previous) -> Window previous -> Prop
  coldDecidable : (previous : Previous) ->
    (window : Window previous) -> Decidable (cold previous window)

def coldValues (profile : Profile Previous) (previous : Previous) :
    List (profile.Window previous) := by
  letI : ∀ window, Decidable (profile.cold previous window) :=
    profile.coldDecidable previous
  exact (profile.schedule.read previous).values.filter
    (fun window => decide (profile.cold previous window))

theorem coldValues_mem
    (profile : Profile Previous) (previous : Previous)
    {window : profile.Window previous}
    (membership : window ∈ coldValues profile previous) :
    window ∈ (profile.schedule.read previous).values := by
  classical
  simp [coldValues] at membership ⊢
  exact membership.1

theorem coldValues_nodup
    (profile : Profile Previous) (previous : Previous) :
    (coldValues profile previous).Nodup := by
  classical
  exact (profile.schedule.read previous).nodup.filter _

end Hypostructure.PDE.InducedPathCold
