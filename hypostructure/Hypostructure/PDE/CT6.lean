import Hypostructure.CT6.Automation
import Hypostructure.Core.Finite.ScheduleEvents
import Hypostructure.PDE.Model

/-!
# PDE adapter for CT6

This adapter evaluates an ordered row, scale, or window condition against a
represented PDE state queried from the predecessor.  It performs no search,
ledger construction, coordinate change, or routing of its own.
-/

namespace Hypostructure.PDE.CT6

universe uPrevious uIndex uData uModel uItem uOutput

/-- Translate represented PDE activity into the domain-neutral CT6 spec. -/
def orderedActivitySpec {Previous : Type uPrevious}
    (M : LocalModel.{uModel})
    (state : Core.Residual.Query Previous fun _previous => M.problem.Ambient)
    (Index : Previous -> Type uIndex)
    (FailureData : (previous : Previous) -> Index previous -> Type uData)
    (failure : (previous : Previous) -> M.problem.Ambient ->
      Index previous -> Prop)
    (failureData : (previous : Previous) ->
      (state : M.problem.Ambient) -> (index : Index previous) ->
      failure previous state index -> FailureData previous index)
    (contribution : (previous : Previous) -> M.problem.Ambient ->
      Index previous -> Nat) :
    _root_.Hypostructure.CT6.Spec Previous where
  Index := Index
  FailureData := FailureData
  Failure := fun previous index =>
    failure previous (state.read previous) index
  failureData := fun previous index failed =>
    failureData previous (state.read previous) index failed
  contribution := fun previous index =>
    contribution previous (state.read previous) index

/-- Construct the common CT6 capability from a predecessor-owned PDE order
and its primitive represented failure decider. -/
def orderedActivityCapability {Previous : Type uPrevious}
    (M : LocalModel.{uModel})
    (state : Core.Residual.Query Previous fun _previous => M.problem.Ambient)
    (Index : Previous -> Type uIndex)
    (FailureData : (previous : Previous) -> Index previous -> Type uData)
    (failure : (previous : Previous) -> M.problem.Ambient ->
      Index previous -> Prop)
    (failureData : (previous : Previous) ->
      (state : M.problem.Ambient) -> (index : Index previous) ->
      failure previous state index -> FailureData previous index)
    (contribution : (previous : Previous) -> M.problem.Ambient ->
      Index previous -> Nat)
    (failureOrder : Core.Residual.Query Previous fun previous =>
      Core.Finite.Enumeration (Index previous))
    (failureDecidable : (previous : Previous) ->
      (state : M.problem.Ambient) -> (index : Index previous) ->
      Decidable (failure previous state index))
    (inputSize : Previous -> Nat) (workCoefficient workDegree : Nat)
    (workBound : forall previous,
      _root_.Hypostructure.CT6.localCheckBound
          (failureOrder.read previous) <=
        workCoefficient * (inputSize previous + 1) ^ workDegree) :
    _root_.Hypostructure.CT6.Capability
      (orderedActivitySpec M state Index FailureData failure failureData
        contribution) where
  failureOrder := failureOrder
  failureDecidable := fun previous index =>
    failureDecidable previous (state.read previous) index
  inputSize := inputSize
  workCoefficient := workCoefficient
  workDegree := workDegree
  workBound := workBound

/-! ## Focused schedule-event specialization -/

/-- Build a Core schedule-event executor for a represented PDE state read from
the active residual.  PDE supplies only state-dependent local packets and their
event predicate; Core owns the scan, split, residual registration, and routing
surface. -/
def focusedScheduleEvents {Previous : Type uPrevious}
    {focus : Core.Residual.Focus.Profile Previous}
    (M : LocalModel.{uModel})
    (state :
      Core.Residual.Focus.ActiveQuery focus
        fun _previous _active => M.problem.Ambient)
    (Item : Type uItem)
    (items :
      Core.Residual.Focus.ActiveQuery focus
        fun _previous _active => Core.Finite.Enumeration Item)
    (Output : M.problem.Ambient -> Item -> Type uOutput)
    (runner :
      Core.Residual.Focus.ActiveQuery focus
        fun previous active =>
          (item : Item) -> Output (state.read previous active) item)
    (event : (previous : Previous) -> (active : focus.Active previous) ->
      (item : Item) -> Output (state.read previous active) item -> Prop)
    (eventDecidable :
      (previous : Previous) -> (active : focus.Active previous) ->
        (item : Item) ->
          Decidable (event previous active item
            ((runner.read previous active) item))) :
    Core.Finite.ScheduleEvents.FocusedContract focus :=
  Core.Finite.ScheduleEvents.focusedFromQueries Item items
    (fun previous active item => Output (state.read previous active) item)
    runner event eventDecidable

end Hypostructure.PDE.CT6
