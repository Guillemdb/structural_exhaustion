import Hypostructure.Core.Strategy
import Hypostructure.Core.Finite.Enumeration
import Hypostructure.Core.Residual.Query
import Hypostructure.PDE.Model

/-!
# PDE adapters for reusable strategies

The PDE specialization supplies only represented states, observable schedules,
and analytic predicates.  Core owns dichotomy composition, ledger extension,
and terminal routing.  In particular, these interfaces never enumerate the
continuum: finite schedules are queries on the active residual.
-/

namespace Hypostructure.PDE.Strategy

universe uPrevious uModel uItem uCoordinate uValue

open Hypostructure

structure ObservableScan (Previous : Type uPrevious) (M : PDE.LocalModel.{uModel}) where
  state : Core.Residual.Query Previous
    (fun _previous => M.problem.Ambient)
  Item : Previous -> Type uItem
  schedule : Core.Residual.Query Previous
    (fun previous => Core.Finite.Enumeration (Item previous))
  observe : (previous : Previous) -> M.problem.Ambient ->
    Item previous -> Bool

structure ResponseProfile (Previous : Type uPrevious) where
  Coordinate : Previous -> Type uCoordinate
  schedule : Core.Residual.Query Previous
    (fun previous => Core.Finite.Enumeration (Coordinate previous))
  observe : (previous : Previous) -> Coordinate previous -> Bool

structure ChargeProfile (Previous : Type uPrevious) where
  Item : Previous -> Type uItem
  schedule : Core.Residual.Query Previous
    (fun previous => Core.Finite.Enumeration (Item previous))
  charge : (previous : Previous) -> Item previous -> Int

/-! A residual-owned scale/window schedule for concentration and regularity
strategies.  The type is abstract: an application may use dyadic windows,
profiles, channels, or any other finite represented index. -/
structure ScaleWindowProfile (Previous : Type uPrevious) where
  Scale : Previous -> Type uValue
  schedule : Core.Residual.Query Previous
    (fun previous => Core.Finite.Enumeration (Scale previous))
  active : (previous : Previous) -> Scale previous -> Prop
  activeDecidable : (previous : Previous) -> (scale : Scale previous) ->
    Decidable (active previous scale)

abbrev Dichotomy (Previous : Type uPrevious) :=
  Core.Strategy.Dichotomy Previous

abbrev ClosedDichotomy (Previous : Type uPrevious) :=
  Core.Strategy.ClosedDichotomy Previous

end Hypostructure.PDE.Strategy
