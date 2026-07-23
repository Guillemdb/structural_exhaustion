import Hypostructure.Core.Progress
import Hypostructure.PDE.Model

/-!
# PDE progress and induced reduction

Graph exposes a concrete lexicographic size.  PDE cannot impose one universal
analytic size, so it exposes the same capability boundary with a caller-owned
well-founded measure (scale, energy, defect rank, or a lexicographic product).
Core remains the sole owner of well-founded recursion and minimality execution.
-/

namespace Hypostructure.PDE.Progress

universe u uMeasure

structure Profile (M : PDE.LocalModel.{u}) where
  Measure : Type uMeasure
  lt : Measure -> Measure -> Prop
  wellFounded : WellFounded lt
  measure : M.problem.Ambient -> Measure

def toCore {M : PDE.LocalModel.{u}} (profile : Profile M) :
    Core.Progress M.problem where
  Measure := profile.Measure
  lt := profile.lt
  wellFounded := profile.wellFounded
  measure := profile.measure

abbrev Smaller {M : PDE.LocalModel.{u}}
    (profile : Profile M) (left right : M.problem.Ambient) : Prop :=
  profile.lt (profile.measure left) (profile.measure right)

theorem notSmallerSelf {M : PDE.LocalModel.{u}}
    (profile : Profile M) (object : M.problem.Ambient) :
    Not (Smaller profile object object) :=
  (toCore profile).not_smaller_self object

end Hypostructure.PDE.Progress
