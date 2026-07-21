import Hypostructure.CT8.Automation
import Hypostructure.Core.Progress
import Hypostructure.PDE.Model

/-!
# PDE adapter for CT8

The adapter interprets recurrence states as local profiles, scale states, or
other PDE proof objects and the removal as a represented ambient state below
the queried source.  It introduces no recurrence carrier or routing layer.
-/

namespace Hypostructure.PDE.CT8

universe uPrevious uState uType uContext uValue uModel uMeasure

/-- Translate represented PDE recurrence semantics into the shared CT8 spec. -/
def profileRecurrenceSpec {Previous : Type uPrevious}
    (M : LocalModel.{uModel})
    (progress : Core.Progress.{uModel, uModel, uMeasure} M.problem)
    (source : Core.Residual.Query Previous fun _previous =>
      M.problem.Ambient)
    (State : Previous -> Type uState)
    (ExactType : Previous -> Type uType)
    (ResponseContext : Previous -> Type uContext)
    (ResponseValue : Previous -> Type uValue)
    (exactType : (previous : Previous) -> State previous ->
      ExactType previous)
    (response : (previous : Previous) -> State previous ->
      ResponseContext previous -> ResponseValue previous) :
    _root_.Hypostructure.CT8.Spec Previous where
  State := State
  ExactType := ExactType
  ResponseContext := ResponseContext
  ResponseValue := ResponseValue
  Removal := fun _previous => M.problem.Ambient
  exactType := exactType
  response := response
  StrictlySmaller := fun previous candidate =>
    progress.Smaller candidate (source.read previous)

/-- Supply only predecessor-owned recurrence schedules, primitive represented
semantics, a certified removal, and the work envelope. -/
def profileRecurrenceCapability {Previous : Type uPrevious}
    (M : LocalModel.{uModel})
    (progress : Core.Progress.{uModel, uModel, uMeasure} M.problem)
    (source : Core.Residual.Query Previous fun _previous =>
      M.problem.Ambient)
    (State : Previous -> Type uState)
    (ExactType : Previous -> Type uType)
    (ResponseContext : Previous -> Type uContext)
    (ResponseValue : Previous -> Type uValue)
    (exactType : (previous : Previous) -> State previous ->
      ExactType previous)
    (response : (previous : Previous) -> State previous ->
      ResponseContext previous -> ResponseValue previous)
    (sequence : Core.Residual.Query Previous fun previous =>
      List (State previous))
    (exactTypes : Core.Residual.Query Previous fun previous =>
      Core.Finite.CompleteEnumeration (ExactType previous))
    (responseContexts : Core.Residual.Query Previous fun previous =>
      Core.Finite.CompleteEnumeration (ResponseContext previous))
    (responseValueDecEq : (previous : Previous) ->
      DecidableEq (ResponseValue previous))
    (remove : (previous : Previous) ->
      (first second : State previous) ->
      (sameType : exactType previous first = exactType previous second) ->
      (equalResponses : forall context,
        response previous first context = response previous second context) ->
        M.problem.Ambient)
    (removeStrict : (previous : Previous) ->
      (first second : State previous) ->
      (sameType : exactType previous first = exactType previous second) ->
      (equalResponses : forall context,
        response previous first context = response previous second context) ->
      progress.Smaller
        (remove previous first second sameType equalResponses)
        (source.read previous))
    (inputSize : Previous -> Nat) (workCoefficient workDegree : Nat)
    (workBound : forall previous,
      _root_.Hypostructure.CT8.localCheckBound
          (sequence.read previous)
          (responseContexts.read previous).toEnumeration <=
        workCoefficient * (inputSize previous + 1) ^ workDegree) :
    _root_.Hypostructure.CT8.Capability
      (profileRecurrenceSpec M progress source State ExactType ResponseContext
        ResponseValue exactType response) where
  sequence := sequence
  exactTypes := exactTypes
  responseContexts := responseContexts
  responseValueDecEq := responseValueDecEq
  remove := remove
  removeStrict := removeStrict
  inputSize := inputSize
  workCoefficient := workCoefficient
  workDegree := workDegree
  workBound := workBound

end Hypostructure.PDE.CT8
