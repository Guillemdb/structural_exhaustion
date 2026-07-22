import Hypostructure.Fixtures.PDERow7CapacityTargetCompactification
import Hypostructure.PDE.Contract

/-!
# PDE row-8 exact response coverage fixture

This finite fixture exercises the row-8 CT3-to-CT7 executor on the active
positive-capacity row-7 residual.  The fixture supplies only tiny residual-owned
finite schedules; CT3 and CT7 own all branch routing and accounting.
-/

namespace Hypostructure.Fixtures.PDERow8ExactResponseCoverage

open Hypostructure
open Hypostructure.Core
open Hypostructure.Core.Residual
open Hypostructure.PDE.FastTrack

noncomputable section

abbrev RowSevenProfile :=
  PDERow7CapacityTargetCompactification.profile

abbrev PositiveRowSevenProfile := RowSevenProfile .positive

abbrev RowSevenStage :=
  ExactResponseCoverage.RowSevenStage PositiveRowSevenProfile

abbrev ResponseView :=
  ExactResponseCoverage.ActiveView PositiveRowSevenProfile

def rowSevenStage : RowSevenStage :=
  PDERow7CapacityTargetCompactification.positiveRun.value

def rowSevenPositiveActive :
    (CapacityProfile.PositiveCapacityFocus PositiveRowSevenProfile).Active
      rowSevenStage := by
  refine ⟨PDERow7CapacityTargetCompactification.positiveStageActive, ?_⟩
  change
    (CapacityProfile.terminalQuery PositiveRowSevenProfile).read rowSevenStage
      PDERow7CapacityTargetCompactification.positiveStageActive = .c1
  exact PDERow7CapacityTargetCompactification.positiveOutput_terminal

def responseView : ResponseView :=
  Focus.ActiveView.of rowSevenStage rowSevenPositiveActive

def responseSystem : Core.Response.System Unit :=
  Core.Response.System.ofDecodedContexts Unit Unit Bool
    (fun _representative _context => true) id

instance responseSystemContextSubsingleton :
    Subsingleton responseSystem.Context := by
  change Subsingleton Unit
  infer_instance

def responseSemantics : Core.Response.TargetSemantics responseSystem where
  TargetResponse := fun _representative _context => True
  Accepts := fun value => value = true
  target_iff_accepts := by
    intro representative context
    constructor
    · intro _target
      cases representative
      cases context
      rfl
    · intro _accepts
      trivial

abbrev responseSpec : CT3.Spec ResponseView where
  Representative := Unit
  Candidate := Unit
  Row := Unit
  system := responseSystem
  semantics := responseSemantics
  candidatePiece := id
  rowPiece := id
  rowResponse := fun _row _coordinate => true
  Admissible := fun _previous _source _candidate => True
  StrictlySmaller := fun _previous _source _candidate => True

def responseSourceQuery :
    Residual.Query ResponseView fun _view => Unit :=
  Residual.Query.residual.map fun _view _root => ()

def responseCoordinatesQuery :
    Residual.Query ResponseView fun _view =>
      Core.Finite.Enumeration Unit :=
  Residual.Query.residual.map fun _view _root =>
    Core.Finite.Enumeration.singleton ()

def responseCandidatesQuery :
    Residual.Query ResponseView fun _view =>
      Core.Finite.Enumeration Unit :=
  Residual.Query.residual.map fun _view _root =>
    Core.Finite.Enumeration.singleton ()

def responseRowsQuery :
    Residual.Query ResponseView fun _view =>
      Core.Finite.Enumeration Unit :=
  Residual.Query.residual.map fun _view _root =>
    Core.Finite.Enumeration.empty Unit

def responseCoverage
    (previous : ResponseView) (replacement : Unit) :
    Core.Response.FiniteTable.SymbolicCoverage responseSystem
      (responseSpec.representatives
        (responseSourceQuery.read previous) replacement)
      (Core.Response.FiniteTable.ExactSchedule.ofList
        (responseCoordinatesQuery.read previous).values) := by
  change
    Core.Response.FiniteTable.SymbolicCoverage responseSystem
      (responseSpec.representatives
        (responseSourceQuery.read previous) replacement)
      (Core.Response.FiniteTable.ExactSchedule.ofList [()])
  exact Core.Response.FiniteTable.SymbolicCoverage.ofSubsingletonSingleton
    responseSystem
    (responseSpec.representatives
      (responseSourceQuery.read previous) replacement) ()

def responseCapability : CT3.Capability responseSpec where
  source := responseSourceQuery
  coordinates := responseCoordinatesQuery
  candidates := responseCandidatesQuery
  rows := responseRowsQuery
  valueDecEq := by
    change DecidableEq Bool
    infer_instance
  admissibleDecidable := fun _previous _source _candidate => isTrue trivial
  smallerDecidable := fun _previous _source _candidate => isTrue trivial
  candidateCoverage := fun previous candidate _member =>
    responseCoverage previous candidate
  rowCoverage := fun previous row _member =>
    responseCoverage previous row
  inputSize := fun _previous => 0
  workCoefficient := 3
  workDegree := 0
  workBound := by
    intro _previous
    change CT3.localCheckBound (Core.Finite.Enumeration.singleton ())
      (Core.Finite.Enumeration.singleton ())
      (Core.Finite.Enumeration.empty Unit) <= 3
    decide

abbrev ContextPrevious :=
  CT3.Stage responseSpec responseCapability

def contextSystem : Core.Response.System Unit :=
  Core.Response.System.ofDecodedContexts Unit Unit Bool
    (fun _representative _context => true) id

instance contextSystemContextSubsingleton :
    Subsingleton contextSystem.Context := by
  change Subsingleton Unit
  infer_instance

instance contextSystemCoordinateDecidableEq :
    DecidableEq contextSystem.Coordinate := by
  change DecidableEq Unit
  infer_instance

abbrev contextSpec : CT7.Spec ContextPrevious where
  Representative := Unit
  system := contextSystem
  Realizes := fun _previous _representative _context => True

def contextRepresentativesQuery :
    Residual.Query ContextPrevious fun _previous =>
      Core.Response.Representatives Unit :=
  Residual.Query.residual.map fun _previous _root =>
    { source := (), replacement := () }

def contextCoordinatesQuery :
    Residual.Query ContextPrevious fun _previous =>
      Core.Finite.Enumeration Unit :=
  Residual.Query.residual.map fun _previous _root =>
    Core.Finite.Enumeration.singleton ()

def contextCoordinateQuery :
    Residual.Query ContextPrevious fun _previous => Unit :=
  Residual.Query.residual.map fun _previous _root => ()

def contextCapability : CT7.Capability contextSpec :=
  CT7.Capability.ofSubsingletonSingletonContexts contextRepresentativesQuery
    contextCoordinateQuery
    (by
      change DecidableEq Bool
      infer_instance)
    (fun _previous => isTrue trivial)

def rowEightContract :
    PDE.Contract.ExactResponse PositiveRowSevenProfile :=
  PDE.Contract.ExactResponse.ofCapabilityCanonicalEnvelope
    responseSpec responseCapability contextSpec contextCapability

abbrev rowEightProfile :
    ExactResponseCoverage.Profile PositiveRowSevenProfile :=
  rowEightContract.toProfile

def rowEightRun :=
  rowEightContract.run rowSevenStage

theorem rowEight_retains_literal_row_seven :
    rowEightRun.value.previous = rowSevenStage :=
  rowEightContract.run_previous rowSevenStage

theorem rowEight_active_work :
    rowEightRun.checks =
      (CapacityProfile.PositiveCapacityFocus
        PositiveRowSevenProfile).selectionBudget.checks rowSevenStage +
        (ExactResponseCoverage.generateActiveCounted
          rowEightProfile responseView).checks :=
  rowEightContract.run_checks_of_active rowSevenStage rowSevenPositiveActive

theorem rowEight_work_is_bounded :
    rowEightRun.checks <=
      ((CapacityProfile.PositiveCapacityFocus
        PositiveRowSevenProfile).selectionBudget.add
        (ExactResponseCoverage.payloadBudget rowEightProfile)).coefficient *
      (((CapacityProfile.PositiveCapacityFocus
        PositiveRowSevenProfile).selectionBudget.add
        (ExactResponseCoverage.payloadBudget rowEightProfile)).size
          rowSevenStage + 1) ^
      ((CapacityProfile.PositiveCapacityFocus
        PositiveRowSevenProfile).selectionBudget.add
        (ExactResponseCoverage.payloadBudget rowEightProfile)).degree :=
  rowEightContract.run_checks_bounded rowSevenStage

#print axioms rowEight_work_is_bounded

end

end Hypostructure.Fixtures.PDERow8ExactResponseCoverage
