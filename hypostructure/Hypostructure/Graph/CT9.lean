import Hypostructure.CT9.Automation
import Hypostructure.Graph.Object

/-!
# Graph adapter for CT9

The adapter evaluates generic role labels, capacities, and optional parity
ranks against a finite graph object read from the incoming ledger.  It never
constructs an item family, fibre, partition, result, or route.
-/

namespace Hypostructure.Graph.CT9

universe uPrevious uItem uLabel uVertex

/-- Translate graph-indexed role semantics into the shared CT9 spec. -/
def roleSpec {Previous : Type uPrevious}
    (object : Core.Residual.Query Previous fun _previous =>
      FiniteObject.{uVertex})
    (Item : Previous -> Type uItem)
    (Label : Previous -> Type uLabel)
    (label : (previous : Previous) -> FiniteObject.{uVertex} ->
      Item previous -> Label previous)
    (capacity : (previous : Previous) -> FiniteObject.{uVertex} ->
      Label previous -> Nat) :
    _root_.Hypostructure.CT9.Spec Previous where
  Item := Item
  Label := Label
  label := fun previous item => label previous (object.read previous) item
  capacity := fun previous role =>
    capacity previous (object.read previous) role

/-- Supply only residual-owned items, the complete role schedule, graph
semantics, and a work envelope to the shared CT9 executor. -/
def roleCapability {Previous : Type uPrevious}
    (object : Core.Residual.Query Previous fun _previous =>
      FiniteObject.{uVertex})
    (Item : Previous -> Type uItem)
    (Label : Previous -> Type uLabel)
    (label : (previous : Previous) -> FiniteObject.{uVertex} ->
      Item previous -> Label previous)
    (capacity : (previous : Previous) -> FiniteObject.{uVertex} ->
      Label previous -> Nat)
    (items : Core.Residual.Query Previous fun previous =>
      Core.Finite.Enumeration (Item previous))
    (labels : (previous : Previous) ->
      Core.Finite.CompleteEnumeration (Label previous))
    (inputSize : Previous -> Nat) (workCoefficient workDegree : Nat)
    (workBound : forall previous,
      _root_.Hypostructure.CT9.localCheckBound (items.read previous)
          (labels previous).toEnumeration <=
        workCoefficient * (inputSize previous + 1) ^ workDegree) :
    _root_.Hypostructure.CT9.Capability
      (roleSpec object Item Label label capacity) where
  items := items
  labels := labels
  inputSize := inputSize
  workCoefficient := workCoefficient
  workDegree := workDegree
  workBound := workBound

/-- Derive the common two-parity capacity-one profile from a graph-indexed
rank while retaining the predecessor-owned item schedule. -/
def parityProfile {Previous : Type uPrevious}
    (object : Core.Residual.Query Previous fun _previous =>
      FiniteObject.{uVertex})
    (Item : Previous -> Type uItem)
    (rank : (previous : Previous) -> FiniteObject.{uVertex} ->
      Item previous -> Nat)
    (items : Core.Residual.Query Previous fun previous =>
      Core.Finite.Enumeration (Item previous))
    (inputSize : Previous -> Nat) (workCoefficient workDegree : Nat)
    (workBound : forall previous,
      _root_.Hypostructure.CT9.localCheckBound (items.read previous)
          _root_.Hypostructure.CT9.parityLabels.toEnumeration <=
        workCoefficient * (inputSize previous + 1) ^ workDegree) :
    _root_.Hypostructure.CT9.ParityCapacityOneProfile Previous where
  Item := Item
  rank := fun previous item => rank previous (object.read previous) item
  items := items
  inputSize := inputSize
  workCoefficient := workCoefficient
  workDegree := workDegree
  workBound := workBound

end Hypostructure.Graph.CT9
