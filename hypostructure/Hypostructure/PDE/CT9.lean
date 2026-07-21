import Hypostructure.CT9.Automation
import Hypostructure.PDE.Model

/-!
# PDE adapter for CT9

The PDE layer evaluates packet/profile labels, finite capacities, and optional
parity ranks against a represented state queried from the predecessor.  The
shared CT9 machine owns all finite partitioning, scans, accounting, and
routing.
-/

namespace Hypostructure.PDE.CT9

universe uPrevious uItem uLabel uModel

/-- Translate represented PDE fibre semantics into the shared CT9 spec. -/
def packetSpec {Previous : Type uPrevious}
    (M : LocalModel.{uModel})
    (state : Core.Residual.Query Previous fun _previous => M.problem.Ambient)
    (Item : Previous -> Type uItem)
    (Label : Previous -> Type uLabel)
    (label : (previous : Previous) -> M.problem.Ambient ->
      Item previous -> Label previous)
    (capacity : (previous : Previous) -> M.problem.Ambient ->
      Label previous -> Nat) :
    _root_.Hypostructure.CT9.Spec Previous where
  Item := Item
  Label := Label
  label := fun previous item => label previous (state.read previous) item
  capacity := fun previous packetLabel =>
    capacity previous (state.read previous) packetLabel

/-- Supply only residual-owned packets/profiles, the complete label schedule,
represented semantics, and a work envelope to the shared CT9 executor. -/
def packetCapability {Previous : Type uPrevious}
    (M : LocalModel.{uModel})
    (state : Core.Residual.Query Previous fun _previous => M.problem.Ambient)
    (Item : Previous -> Type uItem)
    (Label : Previous -> Type uLabel)
    (label : (previous : Previous) -> M.problem.Ambient ->
      Item previous -> Label previous)
    (capacity : (previous : Previous) -> M.problem.Ambient ->
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
      (packetSpec M state Item Label label capacity) where
  items := items
  labels := labels
  inputSize := inputSize
  workCoefficient := workCoefficient
  workDegree := workDegree
  workBound := workBound

/-- Derive the common two-parity capacity-one profile from a represented
PDE rank while retaining the predecessor-owned packet schedule. -/
def parityProfile {Previous : Type uPrevious}
    (M : LocalModel.{uModel})
    (state : Core.Residual.Query Previous fun _previous => M.problem.Ambient)
    (Item : Previous -> Type uItem)
    (rank : (previous : Previous) -> M.problem.Ambient ->
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
  rank := fun previous item => rank previous (state.read previous) item
  items := items
  inputSize := inputSize
  workCoefficient := workCoefficient
  workDegree := workDegree
  workBound := workBound

end Hypostructure.PDE.CT9
