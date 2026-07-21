import Hypostructure.CT4.Automation
import Hypostructure.PDE.Model

/-!
# PDE adapter for CT4 window charging

The PDE layer interprets payers as an exact predecessor-owned window/account
schedule and evaluates charging semantics against the represented state read
from the same ledger.  It performs no window enumeration and no routing.
-/

namespace Hypostructure.PDE.CT4

universe uModel uPrevious uDemand

/-- Shared CT4 semantics for assigning finite error demands to local windows. -/
def windowChargingSpec {Previous : Type uPrevious}
    (M : LocalModel.{uModel})
    (state : Core.Residual.Query Previous fun _previous => M.problem.Ambient)
    (Demand : Previous -> Type uDemand)
    (Eligible : (previous : Previous) -> M.problem.Ambient ->
      Demand previous -> M.atlas.Window -> Prop)
    (demandWeight : (previous : Previous) -> M.problem.Ambient ->
      Demand previous -> Nat)
    (capacity : (previous : Previous) -> M.problem.Ambient ->
      M.atlas.Window -> Nat)
    (required : (previous : Previous) -> M.problem.Ambient -> Nat) :
    _root_.Hypostructure.CT4.Spec Previous where
  Demand := Demand
  Payer := fun _previous => M.atlas.Window
  Eligible := fun previous demand window =>
    Eligible previous (state.read previous) demand window
  demandWeight := fun previous demand =>
    demandWeight previous (state.read previous) demand
  capacity := fun previous window =>
    capacity previous (state.read previous) window
  required := fun previous => required previous (state.read previous)

/-- Build the PDE window-charging capability from two exact ledger queries,
one primitive semantic decider, and a verifier-work envelope. -/
def windowChargingCapability {Previous : Type uPrevious}
    (M : LocalModel.{uModel})
    (state : Core.Residual.Query Previous fun _previous => M.problem.Ambient)
    (Demand : Previous -> Type uDemand)
    (Eligible : (previous : Previous) -> M.problem.Ambient ->
      Demand previous -> M.atlas.Window -> Prop)
    (demandWeight : (previous : Previous) -> M.problem.Ambient ->
      Demand previous -> Nat)
    (capacity : (previous : Previous) -> M.problem.Ambient ->
      M.atlas.Window -> Nat)
    (required : (previous : Previous) -> M.problem.Ambient -> Nat)
    (demands : Core.Residual.Query Previous fun previous =>
      Core.Finite.Enumeration (Demand previous))
    (windows : Core.Residual.Query Previous fun _previous =>
      Core.Finite.Enumeration M.atlas.Window)
    (eligibleDecidable : (previous : Previous) ->
      (selected : M.problem.Ambient) -> (demand : Demand previous) ->
        (window : M.atlas.Window) ->
          Decidable (Eligible previous selected demand window))
    (inputSize : Previous -> Nat) (workCoefficient workDegree : Nat)
    (workBound : forall previous,
      _root_.Hypostructure.CT4.localCheckBound
          (demands.read previous) (windows.read previous) <=
        workCoefficient * (inputSize previous + 1) ^ workDegree) :
    _root_.Hypostructure.CT4.Capability
      (windowChargingSpec M state Demand Eligible demandWeight capacity
        required) where
  demands := demands
  payers := windows
  eligibleDecidable := fun previous demand window =>
    eligibleDecidable previous (state.read previous) demand window
  inputSize := inputSize
  workCoefficient := workCoefficient
  workDegree := workDegree
  workBound := workBound

end Hypostructure.PDE.CT4
