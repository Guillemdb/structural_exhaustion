import Hypostructure.Fixtures.PDERow8ExactResponseCoverage
import Hypostructure.PDE.Contract

/-!
# PDE row-9 profile-family fixture

This finite fixture exercises the row-9 CT17-to-CT12-to-CT11 executor on the
active row-8 successor residual.  The fixture supplies only residual-owned
finite schedules and component work envelopes; the framework owns all
sequencing, routing, ledgers, and payload accounting.
-/

namespace Hypostructure.Fixtures.PDERow9ProfileFamily

open Hypostructure
open Hypostructure.Core
open Hypostructure.Core.Residual
open Hypostructure.PDE.FastTrack

noncomputable section

abbrev RowSevenProfile :=
  PDERow8ExactResponseCoverage.PositiveRowSevenProfile

abbrev RowEightProfile :=
  PDERow8ExactResponseCoverage.rowEightProfile

abbrev RowEightStage :=
  ProfileFamily.RowEightStage RowEightProfile

abbrev RowNineView :=
  ProfileFamily.ActiveView RowEightProfile

def rowEightStage : RowEightStage :=
  PDERow8ExactResponseCoverage.rowEightRun.value

theorem rowEightSuccessorActive :
    (ExactResponseCoverage.SuccessorFocus RowEightProfile).Active
      rowEightStage := by
  change
    (CapacityProfile.PositiveCapacityFocus RowSevenProfile).Active
      PDERow8ExactResponseCoverage.rowEightRun.value.previous
  rw [PDERow8ExactResponseCoverage.rowEight_retains_literal_row_seven]
  exact PDERow8ExactResponseCoverage.rowSevenPositiveActive

def rowNineView : RowNineView :=
  Focus.ActiveView.of rowEightStage rowEightSuccessorActive

abbrev thickeningSpec : CT17.Spec RowNineView where
  Target := fun _previous => Unit
  Offset := fun _previous => Unit
  Position := fun _previous _scale => Empty
  Value := fun _previous => Nat
  targetValue := fun _previous _target => 1
  blockValue := fun _previous _scale position _offset => nomatch position
  orbitValue := fun _previous _scale _offset => 0
  Compatible := fun _previous _target _offset => True

def targetQuery :
    Residual.Query RowNineView fun _previous =>
      Core.Finite.Enumeration Unit :=
  Residual.Query.residual.map fun _previous _root =>
    Core.Finite.Enumeration.singleton ()

def offsetQuery :
    Residual.Query RowNineView fun _previous =>
      Core.Finite.Enumeration Unit :=
  Residual.Query.residual.map fun _previous _root =>
    Core.Finite.Enumeration.singleton ()

def scaleQuery :
    Residual.Query RowNineView fun _previous =>
      Core.Finite.Enumeration Nat :=
  Residual.Query.residual.map fun _previous _root =>
    Core.Finite.Enumeration.singleton 0

def selectedScaleQuery :
    Residual.Query RowNineView fun _previous => Nat :=
  Residual.Query.residual.map fun _previous _root => 0

theorem selectedScale_mem_query (previous : RowNineView) :
    selectedScaleQuery.read previous ∈ (scaleQuery.read previous).values := by
  simp [selectedScaleQuery, scaleQuery, Core.Finite.Enumeration.singleton,
    Core.Finite.Enumeration.ofNodupList]

def emptyPositionQuery (_scale : Nat) :
    Residual.Query RowNineView fun _previous =>
      Core.Finite.Enumeration Empty :=
  Residual.Query.residual.map fun _previous _root =>
    Core.Finite.Enumeration.empty Empty

def finiteScaleLimitQuery :
    Residual.Query RowNineView fun _previous => Nat :=
  Residual.Query.residual.map fun _previous _root => 1

def thickeningCapability : CT17.Capability thickeningSpec where
  targets := targetQuery
  offsets := offsetQuery
  scales := scaleQuery
  selectedScale := selectedScaleQuery
  selectedScale_mem := selectedScale_mem_query
  positions := emptyPositionQuery
  finiteScaleLimit := finiteScaleLimitQuery
  compatibleDecidable := fun _previous _target _offset => isTrue trivial
  valueDecidableEq := by
    intro _previous
    change DecidableEq Nat
    infer_instance
  inputSize := fun _previous => 0
  workCoefficient := 5
  workDegree := 0
  workBound := by
    intro previous
    change
      CT17.localCheckBound (targetQuery.read previous)
          (offsetQuery.read previous)
          ((emptyPositionQuery (selectedScaleQuery.read previous)).read previous) <=
        5 * (0 + 1) ^ 0
    norm_num [CT17.localCheckBound, targetQuery, offsetQuery,
      selectedScaleQuery, emptyPositionQuery,
      Core.Finite.Enumeration.singleton, Core.Finite.Enumeration.empty,
      Core.Finite.Enumeration.ofNodupList]

abbrev ThickeningStage :=
  CT17.Stage thickeningSpec thickeningCapability

def profileScheduleQuery :
    Residual.Query ThickeningStage fun _previous =>
      Core.Finite.Enumeration Unit :=
  Residual.Query.residual.map fun _previous _root =>
    Core.Finite.Enumeration.singleton ()

def peelingProfile : CT12.ListPeeling.Profile ThickeningStage where
  Value := fun _previous => Unit
  schedule := profileScheduleQuery

abbrev peelingSpec : CT12.Spec ThickeningStage :=
  CT12.ListPeeling.spec peelingProfile

def peelingCapability : CT12.Capability peelingSpec :=
  CT12.ListPeeling.capability peelingProfile

abbrev PeelingStage :=
  CT12.Stage peelingSpec peelingCapability

def cellQuery :
    Residual.Query PeelingStage fun _previous =>
      Core.Finite.Enumeration Unit :=
  Residual.Query.residual.map fun _previous _root =>
    Core.Finite.Enumeration.singleton ()

def negativeTotalQuery :
    Residual.Query PeelingStage fun previous =>
      ((cellQuery.read previous).values.map (fun _cell : Unit => (-1 : Int))).sum <
        0 :=
  Residual.Query.residual.map fun (_previous : PeelingStage) _root => by
    change (([()].map (fun _cell : Unit => (-1 : Int))).sum < 0)
    decide

def budgetProfile : CT11.OrderedNegativeBudgetProfile PeelingStage where
  Cell := fun _previous => Unit
  localBudget := fun _previous _cell => -1
  cells := cellQuery
  negativeTotal := negativeTotalQuery
  inputSize := fun _previous => 0
  workCoefficient := 2
  workDegree := 0
  workBound := by
    intro previous
    change CT11.localCheckBound (Core.Finite.Enumeration.singleton ()) <= 2
    decide

abbrev budgetSpec : CT11.Spec PeelingStage :=
  budgetProfile.spec

def budgetCapability : CT11.Capability budgetSpec :=
  budgetProfile.capability

def rowNineContract :
    PDE.Contract.ProfileFamilyContract RowEightProfile :=
  PDE.Contract.ProfileFamilyContract.ofCapabilityCanonicalEnvelope
    thickeningSpec thickeningCapability peelingSpec peelingCapability
    budgetSpec budgetCapability

abbrev rowNineProfile :
    ProfileFamily.Profile RowEightProfile :=
  rowNineContract.toProfile

def rowNineRun :=
  rowNineContract.run rowEightStage

theorem rowNine_retains_literal_row_eight :
    rowNineRun.value.previous = rowEightStage :=
  rowNineContract.run_previous rowEightStage

theorem rowNine_active_work :
    rowNineRun.checks =
      (ExactResponseCoverage.SuccessorFocus
        RowEightProfile).selectionBudget.checks rowEightStage +
        (ProfileFamily.generateActiveCounted
          rowNineProfile rowNineView).checks :=
  rowNineContract.run_checks_of_active rowEightStage rowEightSuccessorActive

theorem rowNine_work_is_bounded :
    rowNineRun.checks <=
      ((ExactResponseCoverage.SuccessorFocus RowEightProfile).selectionBudget.add
        (ProfileFamily.payloadBudget rowNineProfile)).coefficient *
      (((ExactResponseCoverage.SuccessorFocus RowEightProfile).selectionBudget.add
        (ProfileFamily.payloadBudget rowNineProfile)).size rowEightStage + 1) ^
      ((ExactResponseCoverage.SuccessorFocus RowEightProfile).selectionBudget.add
        (ProfileFamily.payloadBudget rowNineProfile)).degree :=
  rowNineContract.run_checks_bounded rowEightStage

#print axioms rowNine_work_is_bounded

end

end Hypostructure.Fixtures.PDERow9ProfileFamily
