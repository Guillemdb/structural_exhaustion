import Hypostructure.CT14.Automation
import Hypostructure.PDE.Model

/-!
# PDE adapter for CT14

The PDE layer evaluates generic profile mass, capacity, and label semantics
against a represented state retrieved from the predecessor.  The shared CT14
machine owns every finite scan, ledger, comparison, and route.
-/

namespace Hypostructure.PDE.CT14

universe uPrevious uMember uLabel uModel

/-- Translate represented PDE aggregate semantics into the shared CT14 spec. -/
def aggregateSpec {Previous : Type uPrevious}
    (M : LocalModel.{uModel})
    (state : Core.Residual.Query Previous fun _previous => M.problem.Ambient)
    (Member : Previous -> Type uMember)
    (Label : Previous -> Type uLabel)
    (lowerMass : (previous : Previous) -> M.problem.Ambient ->
      Member previous -> Nat)
    (capacity : (previous : Previous) -> M.problem.Ambient ->
      Member previous -> Option Nat)
    (label : (previous : Previous) -> M.problem.Ambient ->
      Member previous -> Option (Label previous)) :
    _root_.Hypostructure.CT14.Spec Previous where
  Member := Member
  Label := Label
  memberLowerMass := fun previous member =>
    lowerMass previous (state.read previous) member
  memberCapacity := fun previous member =>
    capacity previous (state.read previous) member
  memberLabel := fun previous member =>
    label previous (state.read previous) member

/-- Supply only the residual-owned profiles, primitive represented semantics,
label equality, and work envelope to the common CT14 executor. -/
def aggregateCapability {Previous : Type uPrevious}
    (M : LocalModel.{uModel})
    (state : Core.Residual.Query Previous fun _previous => M.problem.Ambient)
    (Member : Previous -> Type uMember)
    (Label : Previous -> Type uLabel)
    (lowerMass : (previous : Previous) -> M.problem.Ambient ->
      Member previous -> Nat)
    (capacity : (previous : Previous) -> M.problem.Ambient ->
      Member previous -> Option Nat)
    (label : (previous : Previous) -> M.problem.Ambient ->
      Member previous -> Option (Label previous))
    (members : Core.Residual.Query Previous fun previous =>
      Core.Finite.Enumeration (Member previous))
    (labelDecidableEq : (previous : Previous) -> DecidableEq (Label previous))
    (inputSize : Previous -> Nat) (workCoefficient workDegree : Nat)
    (workBound : forall previous,
      _root_.Hypostructure.CT14.localCheckBound (members.read previous) <=
        workCoefficient * (inputSize previous + 1) ^ workDegree) :
    _root_.Hypostructure.CT14.Capability
      (aggregateSpec M state Member Label lowerMass capacity label) where
  members := members
  labelDecidableEq := labelDecidableEq
  inputSize := inputSize
  workCoefficient := workCoefficient
  workDegree := workDegree
  workBound := workBound

end Hypostructure.PDE.CT14
