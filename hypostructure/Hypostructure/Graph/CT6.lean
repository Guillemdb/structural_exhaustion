import Hypostructure.CT6.Automation
import Hypostructure.Graph.Object

/-!
# Graph adapter for CT6

This adapter only evaluates ordered local activity against a finite graph
object retrieved from the predecessor.  The shared CT6 machine owns the
order scan, branch, diagnostic residual, active ledger, trace, and routing.
-/

namespace Hypostructure.Graph.CT6

universe uPrevious uIndex uData uVertex

/-- Translate graph-indexed local activity into the domain-neutral CT6 spec. -/
def orderedActivitySpec {Previous : Type uPrevious}
    (object : Core.Residual.Query Previous fun _previous =>
      FiniteObject.{uVertex})
    (Index : Previous -> Type uIndex)
    (FailureData : (previous : Previous) -> Index previous -> Type uData)
    (failure : (previous : Previous) -> FiniteObject.{uVertex} ->
      Index previous -> Prop)
    (failureData : (previous : Previous) ->
      (object : FiniteObject.{uVertex}) -> (index : Index previous) ->
      failure previous object index -> FailureData previous index)
    (contribution : (previous : Previous) -> FiniteObject.{uVertex} ->
      Index previous -> Nat) :
    _root_.Hypostructure.CT6.Spec Previous where
  Index := Index
  FailureData := FailureData
  Failure := fun previous index =>
    failure previous (object.read previous) index
  failureData := fun previous index failed =>
    failureData previous (object.read previous) index failed
  contribution := fun previous index =>
    contribution previous (object.read previous) index

/-- Construct the common CT6 capability from residual-owned graph sites and
their primitive activity decider. -/
def orderedActivityCapability {Previous : Type uPrevious}
    (object : Core.Residual.Query Previous fun _previous =>
      FiniteObject.{uVertex})
    (Index : Previous -> Type uIndex)
    (FailureData : (previous : Previous) -> Index previous -> Type uData)
    (failure : (previous : Previous) -> FiniteObject.{uVertex} ->
      Index previous -> Prop)
    (failureData : (previous : Previous) ->
      (object : FiniteObject.{uVertex}) -> (index : Index previous) ->
      failure previous object index -> FailureData previous index)
    (contribution : (previous : Previous) -> FiniteObject.{uVertex} ->
      Index previous -> Nat)
    (failureOrder : Core.Residual.Query Previous fun previous =>
      Core.Finite.Enumeration (Index previous))
    (failureDecidable : (previous : Previous) ->
      (object : FiniteObject.{uVertex}) -> (index : Index previous) ->
      Decidable (failure previous object index))
    (inputSize : Previous -> Nat) (workCoefficient workDegree : Nat)
    (workBound : forall previous,
      _root_.Hypostructure.CT6.localCheckBound
          (failureOrder.read previous) <=
        workCoefficient * (inputSize previous + 1) ^ workDegree) :
    _root_.Hypostructure.CT6.Capability
      (orderedActivitySpec object Index FailureData failure failureData
        contribution) where
  failureOrder := failureOrder
  failureDecidable := fun previous index =>
    failureDecidable previous (object.read previous) index
  inputSize := inputSize
  workCoefficient := workCoefficient
  workDegree := workDegree
  workBound := workBound

end Hypostructure.Graph.CT6
