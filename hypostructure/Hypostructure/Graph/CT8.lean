import Hypostructure.CT8.Automation
import Hypostructure.Graph.Progress

/-!
# Graph adapter for CT8

The adapter interprets the generic removal as a finite graph strictly below
the source graph read from the predecessor.  Occurrence types, exact graph or
interface codes, and responses remain caller-supplied semantics.  The shared
CT8 machine owns every schedule, scan, route, output, and ledger update.
-/

namespace Hypostructure.Graph.CT8

universe uPrevious uState uType uContext uValue uVertex uBranch uMeasure

/-- Translate graph-indexed recurrence semantics into the domain-neutral CT8
contract. -/
def orderedRecurrenceSpec {Previous : Type uPrevious}
    (Baseline : FiniteObject.{uVertex} -> Prop)
    (BranchState : FiniteObject.{uVertex} -> Type uBranch)
    (progress : Core.Progress.{uVertex + 1, uBranch, uMeasure}
      (problem Baseline BranchState))
    (object : Core.Residual.Query Previous fun _previous =>
      FiniteObject.{uVertex})
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
  Removal := fun _previous => FiniteObject.{uVertex}
  exactType := exactType
  response := response
  StrictlySmaller := fun previous candidate =>
    progress.Smaller candidate (object.read previous)

/-- Supply only predecessor-owned schedules, primitive graph recurrence
semantics, a certified graph removal, and the work envelope. -/
def orderedRecurrenceCapability {Previous : Type uPrevious}
    (Baseline : FiniteObject.{uVertex} -> Prop)
    (BranchState : FiniteObject.{uVertex} -> Type uBranch)
    (progress : Core.Progress.{uVertex + 1, uBranch, uMeasure}
      (problem Baseline BranchState))
    (object : Core.Residual.Query Previous fun _previous =>
      FiniteObject.{uVertex})
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
        FiniteObject.{uVertex})
    (removeStrict : (previous : Previous) ->
      (first second : State previous) ->
      (sameType : exactType previous first = exactType previous second) ->
      (equalResponses : forall context,
        response previous first context = response previous second context) ->
      progress.Smaller
        (remove previous first second sameType equalResponses)
        (object.read previous))
    (inputSize : Previous -> Nat) (workCoefficient workDegree : Nat)
    (workBound : forall previous,
      _root_.Hypostructure.CT8.localCheckBound
          (sequence.read previous)
          (responseContexts.read previous).toEnumeration <=
        workCoefficient * (inputSize previous + 1) ^ workDegree) :
    _root_.Hypostructure.CT8.Capability
      (orderedRecurrenceSpec Baseline BranchState progress object State
        ExactType ResponseContext ResponseValue exactType response) where
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

end Hypostructure.Graph.CT8
