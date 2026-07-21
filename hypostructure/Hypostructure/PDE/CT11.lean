import Hypostructure.CT11.Automation
import Hypostructure.PDE.Model

/-!
# PDE adapter for CT11

The PDE layer evaluates local admissibility and additive error semantics
against a represented state retrieved from the predecessor.  The shared CT11
executor owns every finite action and route.
-/

namespace Hypostructure.PDE.CT11

universe uPrevious uCell uModel

/-- Translate represented PDE localization semantics into the shared spec. -/
def additiveSpec {Previous : Type uPrevious}
    (M : LocalModel.{uModel})
    (state : Core.Residual.Query Previous fun _previous => M.problem.Ambient)
    (Cell : Previous -> Type uCell)
    (admissible : (previous : Previous) -> M.problem.Ambient ->
      Cell previous -> Prop)
    (localBudget : (previous : Previous) -> M.problem.Ambient ->
      Cell previous -> Int) :
    _root_.Hypostructure.CT11.Spec Previous where
  Cell := Cell
  Admissible := fun previous cell =>
    admissible previous (state.read previous) cell
  localBudget := fun previous cell =>
    localBudget previous (state.read previous) cell

/-- Supply residual-owned windows or channels and their local semantics to the
common CT11 executor. -/
def additiveCapability {Previous : Type uPrevious}
    (M : LocalModel.{uModel})
    (state : Core.Residual.Query Previous fun _previous => M.problem.Ambient)
    (Cell : Previous -> Type uCell)
    (admissible : (previous : Previous) -> M.problem.Ambient ->
      Cell previous -> Prop)
    (localBudget : (previous : Previous) -> M.problem.Ambient ->
      Cell previous -> Int)
    (cells : Core.Residual.Query Previous fun previous =>
      Core.Finite.Enumeration (Cell previous))
    (admissibleDecidable : (previous : Previous) ->
      (cell : Cell previous) ->
        Decidable (admissible previous (state.read previous) cell))
    (negativeTotal : Core.Residual.Query Previous fun previous =>
      ((cells.read previous).values.map
        (fun cell => localBudget previous (state.read previous) cell)).sum < 0)
    (inputSize : Previous -> Nat) (workCoefficient workDegree : Nat)
    (workBound : forall previous,
      _root_.Hypostructure.CT11.localCheckBound (cells.read previous) <=
        workCoefficient * (inputSize previous + 1) ^ workDegree) :
    _root_.Hypostructure.CT11.Capability
      (additiveSpec M state Cell admissible localBudget) where
  cells := cells
  admissibleDecidable := admissibleDecidable
  negativeTotal := negativeTotal
  inputSize := inputSize
  workCoefficient := workCoefficient
  workDegree := workDegree
  workBound := workBound

/-- Everywhere-admissible PDE budgets use the shared ordered profile. -/
def negativeBudgetProfile {Previous : Type uPrevious}
    (M : LocalModel.{uModel})
    (state : Core.Residual.Query Previous fun _previous => M.problem.Ambient)
    (Cell : Previous -> Type uCell)
    (localBudget : (previous : Previous) -> M.problem.Ambient ->
      Cell previous -> Int)
    (cells : Core.Residual.Query Previous fun previous =>
      Core.Finite.Enumeration (Cell previous))
    (negativeTotal : Core.Residual.Query Previous fun previous =>
      ((cells.read previous).values.map
        (fun cell => localBudget previous (state.read previous) cell)).sum < 0)
    (inputSize : Previous -> Nat) (workCoefficient workDegree : Nat)
    (workBound : forall previous,
      _root_.Hypostructure.CT11.localCheckBound (cells.read previous) <=
        workCoefficient * (inputSize previous + 1) ^ workDegree) :
    _root_.Hypostructure.CT11.OrderedNegativeBudgetProfile Previous where
  Cell := Cell
  localBudget := fun previous cell =>
    localBudget previous (state.read previous) cell
  cells := cells
  negativeTotal := negativeTotal
  inputSize := inputSize
  workCoefficient := workCoefficient
  workDegree := workDegree
  workBound := workBound

end Hypostructure.PDE.CT11
