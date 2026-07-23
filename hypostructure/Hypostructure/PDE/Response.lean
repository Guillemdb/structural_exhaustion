import Hypostructure.Core.Response.System
import Hypostructure.PDE.Model
import Hypostructure.PDE.Representation
import Hypostructure.Core.Residual.Query
import Hypostructure.Core.Finite.Enumeration
import Hypostructure.PDE.Strategy

/-!
# PDE response and context equivalence

This is the continuum analogue of the Graph response layer.  Contexts are
symbolic analytic objects (windows, tails, gauges, or exterior data); the
framework does not enumerate them.  A finite coordinate schedule is supplied
only when a CT execution needs one.
-/

namespace Hypostructure.PDE.Response

universe uPrevious uModel uContext uCoordinate uValue

open Hypostructure

structure Interface (M : PDE.LocalModel.{uModel}) where
  Context : Type uContext
  Coordinate : Type uCoordinate
  Value : Type uValue
  observe : M.problem.Ambient -> Context -> Coordinate -> Value
  targetResponse : M.problem.Ambient -> Context -> Prop

def ContextEquivalent {M : PDE.LocalModel.{uModel}}
    (interface : Interface M) (left right : M.problem.Ambient) : Prop :=
  forall context : interface.Context,
    interface.targetResponse left context ↔
      interface.targetResponse right context

structure TargetComplete {M : PDE.LocalModel.{uModel}}
    (interface : Interface M) (left right : M.problem.Ambient) : Prop where
  contextUniversal : ContextEquivalent interface left right
  coordinateComplete : forall context coordinate,
    interface.observe left context coordinate =
      interface.observe right context coordinate

def TargetDefect {M : PDE.LocalModel.{uModel}}
    (interface : Interface M) (left right : M.problem.Ambient) : Prop :=
  Not (TargetComplete interface left right)

theorem targetDefect_of_not_contextEquivalent
    {M : PDE.LocalModel.{uModel}}
    (interface : Interface M) {left right : M.problem.Ambient}
    (h : Not (ContextEquivalent interface left right)) :
    TargetDefect interface left right := by
  intro complete
  exact h complete.contextUniversal

structure FiniteCoordinateCoverage {Previous : Type uPrevious}
    {M : PDE.LocalModel.{uModel}} (interface : Interface M) where
  schedule : Core.Residual.Query Previous
    (fun _ => Core.Finite.Enumeration interface.Coordinate)
  covered : forall (previous : Previous) (context : interface.Context)
    (coordinate : interface.Coordinate), Prop
  covered_decidable : forall (previous : Previous)
    (context : interface.Context) (coordinate : interface.Coordinate),
    Decidable (covered previous context coordinate)

def toStrategyResponseProfile
    {Previous : Type uPrevious}
    {M : PDE.LocalModel.{uModel}}
    (interface : Interface M)
    (coverage : FiniteCoordinateCoverage (Previous := Previous) interface)
    (context : Core.Residual.Query Previous
      (fun _previous => interface.Context))
    (observe : (previous : Previous) -> interface.Context ->
      interface.Coordinate -> Bool) :
    PDE.Strategy.ResponseProfile Previous where
  Coordinate := fun _ => interface.Coordinate
  schedule := coverage.schedule
  observe := fun previous coordinate =>
    observe previous (context.read previous) coordinate

end Hypostructure.PDE.Response
