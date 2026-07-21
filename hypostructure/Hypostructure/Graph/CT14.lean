import Hypostructure.CT14.Automation
import Hypostructure.Graph.Object

/-!
# Graph adapter for CT14

The adapter only evaluates generic mass, capacity, and label semantics against
a finite graph object read from the incoming ledger.  It creates no member
family, ledger, outcome, route, or graph-specific aggregate notion.
-/

namespace Hypostructure.Graph.CT14

universe uPrevious uMember uLabel uVertex

/-- Translate graph-indexed primitive semantics into the shared CT14 spec. -/
def aggregateSpec {Previous : Type uPrevious}
    (object : Core.Residual.Query Previous fun _previous =>
      FiniteObject.{uVertex})
    (Member : Previous -> Type uMember)
    (Label : Previous -> Type uLabel)
    (lowerMass : (previous : Previous) -> FiniteObject.{uVertex} ->
      Member previous -> Nat)
    (capacity : (previous : Previous) -> FiniteObject.{uVertex} ->
      Member previous -> Option Nat)
    (label : (previous : Previous) -> FiniteObject.{uVertex} ->
      Member previous -> Option (Label previous)) :
    _root_.Hypostructure.CT14.Spec Previous where
  Member := Member
  Label := Label
  memberLowerMass := fun previous member =>
    lowerMass previous (object.read previous) member
  memberCapacity := fun previous member =>
    capacity previous (object.read previous) member
  memberLabel := fun previous member =>
    label previous (object.read previous) member

/-- Supply only the residual-owned members, primitive graph semantics, label
equality, and work envelope to the common CT14 executor. -/
def aggregateCapability {Previous : Type uPrevious}
    (object : Core.Residual.Query Previous fun _previous =>
      FiniteObject.{uVertex})
    (Member : Previous -> Type uMember)
    (Label : Previous -> Type uLabel)
    (lowerMass : (previous : Previous) -> FiniteObject.{uVertex} ->
      Member previous -> Nat)
    (capacity : (previous : Previous) -> FiniteObject.{uVertex} ->
      Member previous -> Option Nat)
    (label : (previous : Previous) -> FiniteObject.{uVertex} ->
      Member previous -> Option (Label previous))
    (members : Core.Residual.Query Previous fun previous =>
      Core.Finite.Enumeration (Member previous))
    (labelDecidableEq : (previous : Previous) -> DecidableEq (Label previous))
    (inputSize : Previous -> Nat) (workCoefficient workDegree : Nat)
    (workBound : forall previous,
      _root_.Hypostructure.CT14.localCheckBound (members.read previous) <=
        workCoefficient * (inputSize previous + 1) ^ workDegree) :
    _root_.Hypostructure.CT14.Capability
      (aggregateSpec object Member Label lowerMass capacity label) where
  members := members
  labelDecidableEq := labelDecidableEq
  inputSize := inputSize
  workCoefficient := workCoefficient
  workDegree := workDegree
  workBound := workBound

end Hypostructure.Graph.CT14
