import Hypostructure.PDE.Contract
import HypostructurePDEExamples.RepresentedNS2DProfileFamilyPacket

/-!
# Represented 2D Navier--Stokes row-10 boundary-repair packet

The represented row-9 packet is inactive because the row-8 successor is
inactive.  Row 10 is still instantiated over the literal row-9 successor.
Core skips the CT10-to-CT11-to-CT14-to-CT1 payload on the inactive successor
and retains the predecessor ledger.
-/

namespace HypostructurePDEExamples.RepresentedNS2DBoundaryRepairPacket

open Hypostructure
open Hypostructure.Core
open Hypostructure.Core.Residual
open Hypostructure.PDE.FastTrack
open HypostructurePDEExamples.RepresentedNS2DProfileFamilyPacket

noncomputable section

abbrev RowNineProfile := rowNineProfile
abbrev RowNineStage := BoundaryRepair.RowNineStage RowNineProfile
abbrev RowTenView := BoundaryRepair.ActiveView RowNineProfile

def rowNineStage : RowNineStage :=
  rowNineRun.value

theorem rowNineSuccessorInactive :
    Not ((ProfileFamily.SuccessorFocus RowNineProfile).Active
      rowNineStage) := by
  intro active
  change
    (ExactResponseCoverage.SuccessorFocus RowEightProfile).Active
      rowNineRun.value.previous at active
  rw [rowNine_retains_literal_row_eight] at active
  exact rowEightSuccessorInactive active

abbrev classificationSpec : CT10.Spec RowTenView where
  Datum := fun _previous => Unit
  Class := fun _previous => Unit
  Promotion := fun _previous => Unit
  classOf := fun _previous _datum => ()
  Direct := fun _previous _class => False
  promote := fun _previous _class => ()

def datumQuery :
    Residual.Query RowTenView fun _previous =>
      Core.Finite.Enumeration Unit :=
  Residual.Query.residual.map fun _previous _root =>
    Core.Finite.Enumeration.singleton ()

def classQuery :
    Residual.Query RowTenView fun _previous =>
      Core.Finite.CompleteEnumeration Unit :=
  Residual.Query.residual.map fun _previous _root => {
    toEnumeration := Core.Finite.Enumeration.singleton ()
    complete := by
      intro value
      cases value
      simp [Core.Finite.Enumeration.singleton,
        Core.Finite.Enumeration.ofNodupList]
  }

def classificationCapability :
    CT10.Capability classificationSpec where
  data := datumQuery
  classes := classQuery
  directDecidable := fun _previous _class => isFalse (by intro h; cases h)
  inputSize := fun _previous => 0
  workCoefficient := 2
  workDegree := 0
  workBound := by
    intro previous
    norm_num [CT10.localCheckBound, datumQuery, classQuery,
      Core.Finite.Enumeration.card, Core.Finite.Enumeration.singleton,
      Core.Finite.Enumeration.ofNodupList]

abbrev ClassificationStage :=
  CT10.Stage classificationSpec classificationCapability

def budgetCellQuery :
    Residual.Query ClassificationStage fun _previous =>
      Core.Finite.Enumeration Unit :=
  Residual.Query.residual.map fun _previous _root =>
    Core.Finite.Enumeration.singleton ()

def negativeTotalQuery :
    Residual.Query ClassificationStage fun previous =>
      ((budgetCellQuery.read previous).values.map
        (fun _cell : Unit => (-1 : Int))).sum < 0 :=
  Residual.Query.residual.map fun (_previous : ClassificationStage) _root => by
    change (([()].map (fun _cell : Unit => (-1 : Int))).sum < 0)
    decide

def budgetProfile : CT11.OrderedNegativeBudgetProfile ClassificationStage where
  Cell := fun _previous => Unit
  localBudget := fun _previous _cell => -1
  cells := budgetCellQuery
  negativeTotal := negativeTotalQuery
  inputSize := fun _previous => 0
  workCoefficient := 2
  workDegree := 0
  workBound := by
    intro previous
    change CT11.localCheckBound (Core.Finite.Enumeration.singleton ()) <= 2
    decide

abbrev budgetSpec : CT11.Spec ClassificationStage :=
  budgetProfile.spec

def budgetCapability : CT11.Capability budgetSpec :=
  budgetProfile.capability

abbrev BudgetStage :=
  CT11.Stage budgetSpec budgetCapability

abbrev capacitySpec : CT14.Spec BudgetStage where
  Member := fun _previous => Unit
  Label := fun _previous => Unit
  memberLowerMass := fun _previous _member => 1
  memberCapacity := fun _previous _member => some 0
  memberLabel := fun _previous _member => some ()

def memberQuery :
    Residual.Query BudgetStage fun _previous =>
      Core.Finite.Enumeration Unit :=
  Residual.Query.residual.map fun _previous _root =>
    Core.Finite.Enumeration.singleton ()

def capacityCapability : CT14.Capability capacitySpec where
  members := memberQuery
  labelDecidableEq := fun _previous => by
    change DecidableEq Unit
    infer_instance
  inputSize := fun _previous => 0
  workCoefficient := 4
  workDegree := 0
  workBound := by
    intro previous
    change CT14.localCheckBound (Core.Finite.Enumeration.singleton ()) <=
      4 * (0 + 1) ^ 0
    decide

abbrev CapacityStage :=
  CT14.Stage capacitySpec capacityCapability

abbrev targetSpec : CT1.Spec CapacityStage where
  Candidate := fun _previous => Empty
  Realizes := fun _previous candidate => nomatch candidate

def targetScheduleQuery :
    Residual.Query CapacityStage fun _previous =>
      Core.Finite.Enumeration Empty :=
  Residual.Query.residual.map fun _previous _root =>
    Core.Finite.Enumeration.empty Empty

def targetCapability : CT1.Capability targetSpec where
  schedule := targetScheduleQuery
  realizesDecidable := fun _previous candidate => nomatch candidate
  inputSize := fun _previous => 0
  workCoefficient := 1
  workDegree := 0
  workBound := by
    intro previous
    simp [CT1.searchCheckBound, targetScheduleQuery,
      Core.Finite.Enumeration.empty, Core.Finite.Enumeration.card,
      Core.Finite.Enumeration.ofNodupList]

def rowTenContract :
    PDE.Contract.BoundaryRepairContract RowNineProfile :=
  PDE.Contract.BoundaryRepairContract.ofCapabilityCanonicalEnvelope
    classificationSpec classificationCapability budgetSpec budgetCapability
    capacitySpec capacityCapability targetSpec targetCapability

abbrev rowTenProfile : BoundaryRepair.Profile RowNineProfile :=
  rowTenContract.toProfile

def rowTenRun :=
  rowTenContract.run rowNineStage

theorem rowTen_retains_literal_row_nine :
    rowTenRun.value.previous = rowNineStage :=
  rowTenContract.run_previous rowNineStage

theorem rowTen_skips_inactive_payload :
    rowTenRun.checks =
      (ProfileFamily.SuccessorFocus
        RowNineProfile).selectionBudget.checks rowNineStage :=
  rowTenContract.run_checks_of_inactive rowNineStage
    rowNineSuccessorInactive

theorem rowTen_work_is_bounded :
    rowTenRun.checks <=
      ((ProfileFamily.SuccessorFocus RowNineProfile).selectionBudget.add
        (BoundaryRepair.payloadBudget rowTenProfile)).coefficient *
      (((ProfileFamily.SuccessorFocus RowNineProfile).selectionBudget.add
        (BoundaryRepair.payloadBudget rowTenProfile)).size rowNineStage + 1) ^
      ((ProfileFamily.SuccessorFocus RowNineProfile).selectionBudget.add
        (BoundaryRepair.payloadBudget rowTenProfile)).degree :=
  rowTenContract.run_checks_bounded rowNineStage

theorem rowTen_retains_root_residual :
    Core.Residual.residualOf rowTenRun.value =
      HypostructurePDEExamples.RepresentedNS2DLocalTailPacket.zeroRootResidual :=
  by
    change Core.Residual.residualOf rowTenRun.value.previous =
      HypostructurePDEExamples.RepresentedNS2DLocalTailPacket.zeroRootResidual
    rw [rowTen_retains_literal_row_nine]
    exact rowNine_retains_root_residual

#print axioms rowTen_skips_inactive_payload
#print axioms rowTen_work_is_bounded

end

end HypostructurePDEExamples.RepresentedNS2DBoundaryRepairPacket
