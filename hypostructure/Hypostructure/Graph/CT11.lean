import Hypostructure.CT11.Automation
import Hypostructure.Graph.Object

/-!
# Graph adapter for CT11

The adapter evaluates generic admissibility and additive-budget semantics
against a finite graph object retrieved from the predecessor.  The shared CT11
machine owns the ordered family, scans, routing, result, and ledger extension.
-/

namespace Hypostructure.Graph.CT11

universe uPrevious uCell uVertex

/-- Translate graph-indexed local semantics into the shared CT11 spec. -/
def additiveSpec {Previous : Type uPrevious}
    (object : Core.Residual.Query Previous fun _previous =>
      FiniteObject.{uVertex})
    (Cell : Previous -> Type uCell)
    (admissible : (previous : Previous) -> FiniteObject.{uVertex} ->
      Cell previous -> Prop)
    (localBudget : (previous : Previous) -> FiniteObject.{uVertex} ->
      Cell previous -> Int) :
    _root_.Hypostructure.CT11.Spec Previous where
  Cell := Cell
  Admissible := fun previous cell =>
    admissible previous (object.read previous) cell
  localBudget := fun previous cell =>
    localBudget previous (object.read previous) cell

/-- Supply only residual-owned cells, primitive graph semantics, the registered
negative total, and a work envelope to the common CT11 executor. -/
def additiveCapability {Previous : Type uPrevious}
    (object : Core.Residual.Query Previous fun _previous =>
      FiniteObject.{uVertex})
    (Cell : Previous -> Type uCell)
    (admissible : (previous : Previous) -> FiniteObject.{uVertex} ->
      Cell previous -> Prop)
    (localBudget : (previous : Previous) -> FiniteObject.{uVertex} ->
      Cell previous -> Int)
    (cells : Core.Residual.Query Previous fun previous =>
      Core.Finite.Enumeration (Cell previous))
    (admissibleDecidable : (previous : Previous) ->
      (cell : Cell previous) ->
        Decidable (admissible previous (object.read previous) cell))
    (negativeTotal : Core.Residual.Query Previous fun previous =>
      ((cells.read previous).values.map
        (fun cell => localBudget previous (object.read previous) cell)).sum < 0)
    (inputSize : Previous -> Nat) (workCoefficient workDegree : Nat)
    (workBound : forall previous,
      _root_.Hypostructure.CT11.localCheckBound (cells.read previous) <=
        workCoefficient * (inputSize previous + 1) ^ workDegree) :
    _root_.Hypostructure.CT11.Capability
      (additiveSpec object Cell admissible localBudget) where
  cells := cells
  admissibleDecidable := admissibleDecidable
  negativeTotal := negativeTotal
  inputSize := inputSize
  workCoefficient := workCoefficient
  workDegree := workDegree
  workBound := workBound

/-- Everywhere-admissible graph budgets use the shared ordered profile. -/
def negativeBudgetProfile {Previous : Type uPrevious}
    (object : Core.Residual.Query Previous fun _previous =>
      FiniteObject.{uVertex})
    (Cell : Previous -> Type uCell)
    (localBudget : (previous : Previous) -> FiniteObject.{uVertex} ->
      Cell previous -> Int)
    (cells : Core.Residual.Query Previous fun previous =>
      Core.Finite.Enumeration (Cell previous))
    (negativeTotal : Core.Residual.Query Previous fun previous =>
      ((cells.read previous).values.map
        (fun cell => localBudget previous (object.read previous) cell)).sum < 0)
    (inputSize : Previous -> Nat) (workCoefficient workDegree : Nat)
    (workBound : forall previous,
      _root_.Hypostructure.CT11.localCheckBound (cells.read previous) <=
        workCoefficient * (inputSize previous + 1) ^ workDegree) :
    _root_.Hypostructure.CT11.OrderedNegativeBudgetProfile Previous where
  Cell := Cell
  localBudget := fun previous cell =>
    localBudget previous (object.read previous) cell
  cells := cells
  negativeTotal := negativeTotal
  inputSize := inputSize
  workCoefficient := workCoefficient
  workDegree := workDegree
  workBound := workBound

end Hypostructure.Graph.CT11
