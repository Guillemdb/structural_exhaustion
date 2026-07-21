import Hypostructure.CT12.Automation
import Hypostructure.PDE.Observable

/-!
# PDE adapter for CT12

PDE rows may peel only an explicit finite observable schedule owned by the
incoming residual.  The adapter gives that schedule to the shared list
profile; it does not enumerate a continuum, choose a scale, or implement a
parallel recursive runner.
-/

namespace Hypostructure.PDE.CT12

universe uPrevious uModel

/-- Canonical list-peeling profile for one residual-owned finite subfamily of
a represented model's observables. -/
def observablePeelingProfile
    {Previous : Type uPrevious} {M : LocalModel.{uModel}}
    (observables : ObservableInterface M)
    (schedule : Core.Residual.Query Previous fun _previous =>
      Core.Finite.Enumeration observables.Index) :
    _root_.Hypostructure.CT12.ListPeeling.Profile Previous where
  Value := fun _previous => observables.Index
  schedule := schedule

/-- Framework-owned peeling of the exact supplied observable schedule. -/
def peelObservables
    {Previous : Type uPrevious} {M : LocalModel.{uModel}}
    (observables : ObservableInterface M)
    (schedule : Core.Residual.Query Previous fun _previous =>
      Core.Finite.Enumeration observables.Index)
    (previous : Previous) :=
  _root_.Hypostructure.CT12.ListPeeling.run
    (observablePeelingProfile observables schedule) previous

end Hypostructure.PDE.CT12
