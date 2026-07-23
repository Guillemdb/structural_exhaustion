import Hypostructure.Core.Strategy
import Hypostructure.Core.Residual.Query
import Hypostructure.Core.Finite.Enumeration
import Hypostructure.PDE.Model

/-!
# PDE saturation-support strategy

This is the PDE specialization of the generic success-or-residual strategy.
The application supplies only a finite represented support schedule and the
analytic saturation predicate.  Core performs the branch construction and
retains the exact predecessor.
-/

namespace Hypostructure.PDE.FastTrack.Saturation

universe uPrevious uModel uItem

open Hypostructure

structure Profile {Previous : Type uPrevious}
    (M : PDE.LocalModel.{uModel}) where
  Item : Previous -> Type uItem
  support : Core.Residual.Query Previous
    (fun previous => Core.Finite.Enumeration (Item previous))
  state : Core.Residual.Query Previous (fun _ => M.problem.Ambient)
  saturated : (previous : Previous) -> M.problem.Ambient -> Prop
  saturatedDecidable : (previous : Previous) ->
    (object : M.problem.Ambient) -> Decidable (saturated previous object)
  residual : (previous : Previous) -> Core.Finite.Enumeration (Item previous)
  saturationSound : (previous : Previous) -> saturated previous
      (state.read previous) ->
      residual previous = support.read previous

def strategy {Previous : Type uPrevious} {M : PDE.LocalModel.{uModel}}
    (profile : Profile (M := M) (Previous := Previous)) :
    Core.Strategy.Contract Previous :=
  Core.Strategy.binaryContract
    (fun previous => profile.saturated previous (profile.state.read previous))
    (fun previous => profile.saturatedDecidable previous
      (profile.state.read previous))
    profile.residual

end Hypostructure.PDE.FastTrack.Saturation
