import Hypostructure.CT13.Automation
import Hypostructure.PDE.Model

/-!
# PDE adapter for CT13

This adapter evaluates primitive local/harmonic or gauge/fallback semantics
against a represented PDE state read from the incoming ledger.  The shared
CT13 machine owns all finite search, minimization, reconciliation, and routing.
-/

namespace Hypostructure.PDE.CT13

universe uPrevious uPayer uObstruction uResource uModel

/-- Translate represented PDE tiered-resource semantics into shared CT13. -/
def tieredSpec {Previous : Type uPrevious}
    (M : LocalModel.{uModel})
    (state : Core.Residual.Query Previous fun _previous => M.problem.Ambient)
    (Payer : Previous -> Type uPayer)
    (Obstruction : Previous -> Type uObstruction)
    (Resource : Previous -> Type uResource)
    (eligible : (previous : Previous) -> M.problem.Ambient ->
      Payer previous -> Prop)
    (obstructionCost : (previous : Previous) -> M.problem.Ambient ->
      Obstruction previous -> Nat)
    (payerResource : (previous : Previous) -> M.problem.Ambient ->
      Payer previous -> Resource previous)
    (charge : (previous : Previous) -> M.problem.Ambient ->
      Payer previous -> Nat)
    (demand : (previous : Previous) -> M.problem.Ambient -> Nat) :
    _root_.Hypostructure.CT13.Spec Previous where
  Payer := Payer
  Obstruction := Obstruction
  Resource := Resource
  Eligible := fun previous payer =>
    eligible previous (state.read previous) payer
  obstructionCost := fun previous obstruction =>
    obstructionCost previous (state.read previous) obstruction
  payerResource := fun previous payer =>
    payerResource previous (state.read previous) payer
  charge := fun previous payer =>
    charge previous (state.read previous) payer
  demand := fun previous => demand previous (state.read previous)

/-- Supply only inherited schedules, primitive represented-state decisions,
and a work envelope to the common CT13 executor. -/
def tieredCapability {Previous : Type uPrevious}
    (M : LocalModel.{uModel})
    (state : Core.Residual.Query Previous fun _previous => M.problem.Ambient)
    (Payer : Previous -> Type uPayer)
    (Obstruction : Previous -> Type uObstruction)
    (Resource : Previous -> Type uResource)
    (eligible : (previous : Previous) -> M.problem.Ambient ->
      Payer previous -> Prop)
    (obstructionCost : (previous : Previous) -> M.problem.Ambient ->
      Obstruction previous -> Nat)
    (payerResource : (previous : Previous) -> M.problem.Ambient ->
      Payer previous -> Resource previous)
    (charge : (previous : Previous) -> M.problem.Ambient ->
      Payer previous -> Nat)
    (demand : (previous : Previous) -> M.problem.Ambient -> Nat)
    (payers : Core.Residual.Query Previous fun previous =>
      Core.Finite.Enumeration (Payer previous))
    (obstructions : Core.Residual.Query Previous fun previous =>
      _root_.Hypostructure.CT13.ObstructionSchedule
        (Obstruction previous))
    (tierTwo : Core.Residual.Query Previous fun previous =>
      (obstruction : Obstruction previous) ->
        Core.Finite.Enumeration (Payer previous))
    (eligibleDecidable : (previous : Previous) ->
      (represented : M.problem.Ambient) -> (payer : Payer previous) ->
        Decidable (eligible previous represented payer))
    (resourceDecidableEq : (previous : Previous) ->
      DecidableEq (Resource previous))
    (inputSize : Previous -> Nat) (workCoefficient workDegree : Nat)
    (workBound : forall previous,
      _root_.Hypostructure.CT13.localCheckBound
        (payers.read previous) (obstructions.read previous)
        (tierTwo.read previous) <=
          workCoefficient * (inputSize previous + 1) ^ workDegree) :
    _root_.Hypostructure.CT13.Capability
      (tieredSpec M state Payer Obstruction Resource eligible obstructionCost
        payerResource charge demand) where
  payers := payers
  obstructions := obstructions
  tierTwo := tierTwo
  eligibleDecidable := fun previous payer =>
    eligibleDecidable previous (state.read previous) payer
  resourceDecidableEq := resourceDecidableEq
  inputSize := inputSize
  workCoefficient := workCoefficient
  workDegree := workDegree
  workBound := workBound

end Hypostructure.PDE.CT13
