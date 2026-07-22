import Hypostructure.PDE.Contract
import HypostructurePDEExamples.RepresentedNS2DDefectRoutingPacket
import HypostructurePDEExamples.RepresentedNS2DCapacityTargetCompactificationPacket

/-!
# Represented 2D Navier--Stokes row-8 exact-response packet

The represented row-7 packet is inactive because the row-6 capacity-ready
focus is already inactive.  Row 8 is still instantiated over the literal row-7
successor.  The PDE contract owns the exact CT3-to-CT7 payload composition and
Core skips that payload on the inactive positive-capacity sibling.
-/

namespace HypostructurePDEExamples.RepresentedNS2DExactResponseCoveragePacket

open Hypostructure
open Hypostructure.Core
open Hypostructure.Core.Residual
open Hypostructure.PDE.FastTrack
open HypostructurePDEExamples.RepresentedNS2DDefectRoutingPacket
open HypostructurePDEExamples.RepresentedNS2DCapacityTargetCompactificationPacket

noncomputable section

abbrev RowSevenProfile := rowSevenProfile
abbrev RowSevenStage := ExactResponseCoverage.RowSevenStage RowSevenProfile
abbrev ResponseView := ExactResponseCoverage.ActiveView RowSevenProfile

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
    PDE.Contract.ExactResponse RowSevenProfile :=
    PDE.Contract.ExactResponse.ofCapabilityCanonicalEnvelope
    responseSpec responseCapability contextSpec contextCapability

abbrev rowEightProfile : ExactResponseCoverage.Profile RowSevenProfile :=
  rowEightContract.toProfile

def rowEightRun : Core.Counted (ExactResponseCoverage.Stage rowEightProfile) :=
  rowEightContract.run rowSevenRun.value

theorem rowEight_retains_literal_row_seven :
    rowEightRun.value.previous = rowSevenRun.value :=
  rowEightContract.run_previous rowSevenRun.value

theorem rowEight_positive_capacity_inactive :
    Not ((CapacityProfile.PositiveCapacityFocus rowSevenProfile).Active
      rowSevenRun.value) := by
  intro active
  have successorActive :
      (CapacityProfile.SuccessorFocus rowSevenProfile).Active
        rowSevenRun.value :=
    active.parent
  have capacityActive :
      RowSixProfile.CapacityReadyFocus.Active rowSevenRun.value.previous := by
    change RowSixProfile.CapacityReadyFocus.Active rowSevenRun.value.previous
      at successorActive
    exact successorActive
  rw [rowSeven_retains_literal_row_six] at capacityActive
  exact rowSeven_capacity_ready_inactive capacityActive

theorem rowEight_skips_inactive_payload :
    rowEightRun.checks =
      (CapacityProfile.PositiveCapacityFocus
        rowSevenProfile).selectionBudget.checks rowSevenRun.value :=
  rowEightContract.run_checks_of_inactive rowSevenRun.value
    rowEight_positive_capacity_inactive

theorem rowEight_work_is_bounded :
    rowEightRun.checks <=
      ((CapacityProfile.PositiveCapacityFocus rowSevenProfile).selectionBudget.add
        (ExactResponseCoverage.payloadBudget rowEightProfile)).coefficient *
      (((CapacityProfile.PositiveCapacityFocus rowSevenProfile).selectionBudget.add
        (ExactResponseCoverage.payloadBudget rowEightProfile)).size
          rowSevenRun.value + 1) ^
      ((CapacityProfile.PositiveCapacityFocus rowSevenProfile).selectionBudget.add
        (ExactResponseCoverage.payloadBudget rowEightProfile)).degree :=
  rowEightContract.run_checks_bounded rowSevenRun.value

theorem rowEight_retains_root_residual :
    Core.Residual.residualOf rowEightRun.value =
      HypostructurePDEExamples.RepresentedNS2DLocalTailPacket.zeroRootResidual :=
  by
    change Core.Residual.residualOf rowEightRun.value.previous =
      HypostructurePDEExamples.RepresentedNS2DLocalTailPacket.zeroRootResidual
    rw [rowEight_retains_literal_row_seven]
    change Core.Residual.residualOf rowSevenRun.value.previous =
      HypostructurePDEExamples.RepresentedNS2DLocalTailPacket.zeroRootResidual
    rw [rowSeven_retains_literal_row_six]
    exact rowSix_retains_root_residual

#print axioms rowEight_skips_inactive_payload
#print axioms rowEight_work_is_bounded

end

end HypostructurePDEExamples.RepresentedNS2DExactResponseCoveragePacket
