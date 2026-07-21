import Hypostructure.CT15.Automation
import Hypostructure.PDE.Model

/-!
# PDE adapter for CT15

The PDE layer only evaluates target-dependence, charge, and capacity against a
represented ambient state read from the incoming ledger.  Gauge, quotient,
closed-range, and active-rank interpretations remain semantic parameters of
the caller and use the unchanged Core CT15 machine.
-/

namespace Hypostructure.PDE.CT15

universe uPrevious uCoordinate uModel

/-- Translate represented PDE rank semantics into the shared CT15 contract. -/
def targetRelativeSpec {Previous : Type uPrevious}
    (M : LocalModel.{uModel})
    (state : Core.Residual.Query Previous fun _previous => M.problem.Ambient)
    (Coordinate : Previous -> Type uCoordinate)
    (TargetDependent : (previous : Previous) -> M.problem.Ambient ->
      Coordinate previous -> Prop)
    (charge : (previous : Previous) -> M.problem.Ambient ->
      Coordinate previous -> Nat)
    (capacity : (previous : Previous) -> M.problem.Ambient -> Nat) :
    _root_.Hypostructure.CT15.Spec Previous where
  Coordinate := Coordinate
  TargetDependent := fun previous coordinate =>
    TargetDependent previous (state.read previous) coordinate
  charge := fun previous coordinate =>
    charge previous (state.read previous) coordinate
  capacity := fun previous => capacity previous (state.read previous)

/-- Supply only the residual-owned finite directions, primitive represented
dependence decision, and work envelope to the common CT15 executor. -/
def targetRelativeCapability {Previous : Type uPrevious}
    (M : LocalModel.{uModel})
    (state : Core.Residual.Query Previous fun _previous => M.problem.Ambient)
    (Coordinate : Previous -> Type uCoordinate)
    (TargetDependent : (previous : Previous) -> M.problem.Ambient ->
      Coordinate previous -> Prop)
    (charge : (previous : Previous) -> M.problem.Ambient ->
      Coordinate previous -> Nat)
    (capacity : (previous : Previous) -> M.problem.Ambient -> Nat)
    (coordinates : Core.Residual.Query Previous fun previous =>
      Core.Finite.Enumeration (Coordinate previous))
    (targetDependentDecidable : (previous : Previous) ->
      (state : M.problem.Ambient) ->
      (coordinate : Coordinate previous) ->
        Decidable (TargetDependent previous state coordinate))
    (inputSize : Previous -> Nat) (workCoefficient workDegree : Nat)
    (workBound : forall previous,
      _root_.Hypostructure.CT15.localCheckBound
          (coordinates.read previous) <=
        workCoefficient * (inputSize previous + 1) ^ workDegree) :
    _root_.Hypostructure.CT15.Capability
      (targetRelativeSpec M state Coordinate TargetDependent charge capacity) where
  coordinates := coordinates
  targetDependentDecidable := fun previous coordinate =>
    targetDependentDecidable previous (state.read previous) coordinate
  inputSize := inputSize
  workCoefficient := workCoefficient
  workDegree := workDegree
  workBound := workBound

end Hypostructure.PDE.CT15
