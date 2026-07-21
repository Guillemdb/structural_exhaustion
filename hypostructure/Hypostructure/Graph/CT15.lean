import Hypostructure.CT15.Automation
import Hypostructure.Graph.Object

/-!
# Graph adapter for CT15

This adapter only evaluates caller-supplied rank semantics against the packed
graph retrieved from the predecessor.  It creates no graph coordinate family,
rank notion, route, or result of its own.
-/

namespace Hypostructure.Graph.CT15

universe uPrevious uCoordinate uVertex

/-- Translate graph-indexed target dependence and natural-number resource
data into the domain-neutral CT15 contract. -/
def targetRelativeSpec {Previous : Type uPrevious}
    (object : Core.Residual.Query Previous fun _previous =>
      FiniteObject.{uVertex})
    (Coordinate : Previous -> Type uCoordinate)
    (TargetDependent : (previous : Previous) -> FiniteObject.{uVertex} ->
      Coordinate previous -> Prop)
    (charge : (previous : Previous) -> FiniteObject.{uVertex} ->
      Coordinate previous -> Nat)
    (capacity : (previous : Previous) -> FiniteObject.{uVertex} -> Nat) :
    _root_.Hypostructure.CT15.Spec Previous where
  Coordinate := Coordinate
  TargetDependent := fun previous coordinate =>
    TargetDependent previous (object.read previous) coordinate
  charge := fun previous coordinate =>
    charge previous (object.read previous) coordinate
  capacity := fun previous => capacity previous (object.read previous)

/-- Supply only the residual-owned schedule, primitive graph semantic decider,
and work bound to the shared CT15 executor. -/
def targetRelativeCapability {Previous : Type uPrevious}
    (object : Core.Residual.Query Previous fun _previous =>
      FiniteObject.{uVertex})
    (Coordinate : Previous -> Type uCoordinate)
    (TargetDependent : (previous : Previous) -> FiniteObject.{uVertex} ->
      Coordinate previous -> Prop)
    (charge : (previous : Previous) -> FiniteObject.{uVertex} ->
      Coordinate previous -> Nat)
    (capacity : (previous : Previous) -> FiniteObject.{uVertex} -> Nat)
    (coordinates : Core.Residual.Query Previous fun previous =>
      Core.Finite.Enumeration (Coordinate previous))
    (targetDependentDecidable : (previous : Previous) ->
      (object : FiniteObject.{uVertex}) ->
      (coordinate : Coordinate previous) ->
        Decidable (TargetDependent previous object coordinate))
    (inputSize : Previous -> Nat) (workCoefficient workDegree : Nat)
    (workBound : forall previous,
      _root_.Hypostructure.CT15.localCheckBound
          (coordinates.read previous) <=
        workCoefficient * (inputSize previous + 1) ^ workDegree) :
    _root_.Hypostructure.CT15.Capability
      (targetRelativeSpec object Coordinate TargetDependent charge capacity) where
  coordinates := coordinates
  targetDependentDecidable := fun previous coordinate =>
    targetDependentDecidable previous (object.read previous) coordinate
  inputSize := inputSize
  workCoefficient := workCoefficient
  workDegree := workDegree
  workBound := workBound

end Hypostructure.Graph.CT15
