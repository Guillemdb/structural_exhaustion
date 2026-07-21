import Hypostructure.CT10.Automation
import Hypostructure.PDE.Observable

/-!
# PDE specialization of CT10

The adapter classifies a residual-owned finite family of public observable
indices.  It reads the current represented object through a ledger query and
computes each class from the registered observable value.  It never enumerates
points, windows, scales, functions, or measurable sets.
-/

namespace Hypostructure.PDE.CT10

universe u uPrevious uClass uPromotion

/-- Residual-signature semantics for finite public observable indices. -/
@[implicit_reducible]
def observableSpec {Previous : Type uPrevious}
    (M : LocalModel.{u}) (observables : ObservableInterface M)
    (object : Core.Residual.Query Previous fun _previous =>
      M.problem.Ambient)
    (Class : Previous -> Type uClass)
    (Promotion : Previous -> Type uPromotion)
    (classify : (previous : Previous) -> (index : observables.Index) ->
      observables.Value index -> Class previous)
    (Direct : (previous : Previous) -> Class previous -> Prop)
    (promote : (previous : Previous) ->
      Class previous -> Promotion previous) :
    _root_.Hypostructure.CT10.Spec Previous where
  Datum := fun _previous => observables.Index
  Class := Class
  Promotion := Promotion
  classOf := fun previous index =>
    classify previous index (observables.observe (object.read previous) index)
  Direct := Direct
  promote := promote

/-- Build CT10 from an exact residual-owned observable-index schedule and
complete residual-owned signature alphabet. -/
def observableCapability {Previous : Type uPrevious}
    (M : LocalModel.{u}) (observables : ObservableInterface M)
    (object : Core.Residual.Query Previous fun _previous =>
      M.problem.Ambient)
    (Class : Previous -> Type uClass)
    (Promotion : Previous -> Type uPromotion)
    (classify : (previous : Previous) -> (index : observables.Index) ->
      observables.Value index -> Class previous)
    (Direct : (previous : Previous) -> Class previous -> Prop)
    (promote : (previous : Previous) ->
      Class previous -> Promotion previous)
    (data : Core.Residual.Query Previous fun _previous =>
      Core.Finite.Enumeration observables.Index)
    (classes : Core.Residual.Query Previous fun previous =>
      Core.Finite.CompleteEnumeration (Class previous))
    (directDecidable : (previous : Previous) ->
      (cls : Class previous) -> Decidable (Direct previous cls))
    (inputSize : Previous -> Nat) (workCoefficient workDegree : Nat)
    (workBound : forall previous,
      _root_.Hypostructure.CT10.localCheckBound
          (observableSpec M observables object Class Promotion classify Direct
            promote)
          data classes previous <=
        workCoefficient * (inputSize previous + 1) ^ workDegree) :
    _root_.Hypostructure.CT10.Capability
      (observableSpec M observables object Class Promotion classify Direct
        promote) where
  data := data
  classes := classes
  directDecidable := directDecidable
  inputSize := inputSize
  workCoefficient := workCoefficient
  workDegree := workDegree
  workBound := workBound

end Hypostructure.PDE.CT10
