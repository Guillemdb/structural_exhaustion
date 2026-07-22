import Hypostructure.PDE.Contract
import HypostructurePDEExamples.RepresentedNS2DDirectedExhaustivenessPacket

/-!
# Represented 2D Navier--Stokes row-6 routing packet

The represented row-5 packet reaches its positive structural-gap terminal.
Consequently row 6 is an inactive sibling: Core evaluates the framework-owned
target-visible selector, skips both CT generators, appends no routing payload,
and retains the literal row-5 ledger.

The total CT13 and CT7 registrations below are finite primitive schedules
needed to instantiate the generic executor on every possible predecessor.
No analytic alignment is registered, and this packet proves no effective-
resistance, harmonic-projection, pressure-gauge, continuum, or regularity
theorem.
-/

namespace HypostructurePDEExamples.RepresentedNS2DDefectRoutingPacket

open Hypostructure
open Hypostructure.Core
open Hypostructure.Core.Residual
open Hypostructure.PDE.FastTrack
open HypostructurePDEExamples.RepresentedNS2DDirectedExhaustivenessPacket
open HypostructurePDEExamples.RepresentedNS2DQuotientDefectPacket

noncomputable section

abbrev RoutingView := DefectRouting.ActiveView rowFiveProfile

def routingViewQuery :
    Residual.Query RoutingView fun _view => RoutingView :=
  Residual.Query.residual

/-! ## Total finite CT registrations -/

def payerSchedule : Core.Finite.Enumeration Unit :=
  Core.Finite.Enumeration.singleton ()

def obstructionSchedule : CT13.ObstructionSchedule Unit where
  fallbackDefault := ()
  remaining := []
  nodup := by simp
  decEq := inferInstance

def tierTwoSchedule (_obstruction : Unit) :
    Core.Finite.Enumeration Unit :=
  Core.Finite.Enumeration.singleton ()

def payerQuery :
    Residual.Query RoutingView fun _view =>
      Core.Finite.Enumeration Unit :=
  routingViewQuery.map fun _view _root => payerSchedule

def obstructionQuery :
    Residual.Query RoutingView fun _view => CT13.ObstructionSchedule Unit :=
  routingViewQuery.map fun _view _root => obstructionSchedule

def tierTwoQuery :
    Residual.Query RoutingView fun _view =>
      Unit -> Core.Finite.Enumeration Unit :=
  routingViewQuery.map fun _view _root => tierTwoSchedule

def tieredSpec : CT13.Spec RoutingView where
  Payer := fun _view => Unit
  Obstruction := fun _view => Unit
  Resource := fun _view => Unit
  Eligible := fun _view _payer => False
  obstructionCost := fun _view _obstruction => 0
  payerResource := fun _view _payer => ()
  charge := fun _view _payer => 0
  demand := fun _view => 0

def tieredCapability : CT13.Capability tieredSpec where
  payers := payerQuery
  obstructions := obstructionQuery
  tierTwo := tierTwoQuery
  eligibleDecidable := fun _view _payer => isFalse id
  resourceDecidableEq := fun _view => by
    change DecidableEq Unit
    infer_instance
  inputSize := fun _view => 0
  workCoefficient := 8
  workDegree := 0
  workBound := by
    intro _view
    change CT13.localCheckBound payerSchedule obstructionSchedule
      tierTwoSchedule <= 8
    decide

def contextSchedule : Core.Finite.Enumeration Unit :=
  Core.Finite.Enumeration.singleton ()

theorem contextSchedule_complete (context : Unit) :
    Exists fun index : Fin contextSchedule.card =>
      context = contextSchedule.get index := by
  cases context
  exact ⟨⟨0, by decide⟩, rfl⟩

def representatives : Core.Response.Representatives Unit :=
  ⟨(), ()⟩

def responseSystem : Core.Response.System Unit :=
  Core.Response.System.ofDecodedContexts Unit Unit Unit
    (fun _representative _context => ()) id

def representativesQuery :
    Residual.Query RoutingView fun _view =>
      Core.Response.Representatives Unit :=
  routingViewQuery.map fun _view _root => representatives

def contextsQuery :
    Residual.Query RoutingView fun _view =>
      Core.Finite.Enumeration Unit :=
  routingViewQuery.map fun _view _root => contextSchedule

def contextSpec : CT7.Spec RoutingView where
  Representative := Unit
  system := responseSystem
  Realizes := fun _view _representative _context => False

def contextCapability : CT7.Capability contextSpec :=
  CT7.Capability.ofExactContexts
    representativesQuery contextsQuery
    (by
      change DecidableEq Unit
      infer_instance)
    (fun _view _coordinate => isFalse id)
    (fun _view context => contextSchedule_complete context)

/-! ## Row-6 registration and inactive execution -/

def rowSixContract : PDE.Contract.DefectRouting rowFiveProfile where
  profile := {
    tieredSpec := tieredSpec
    tieredCapability := tieredCapability
    contextSpec := contextSpec
    contextCapability := contextCapability
    FiniteResistance := fun _view _boundary _raw => False
    HarmonicZero := fun _view _boundary _raw => False
    HarmonicLedgerMember := fun _view _boundary _raw => False
    NonroutableTargetVisible := fun _view _boundary _raw => False
    alignmentRegistration :=
      rowFiveProfile.targetVisibleBoundaryQuery.map
        fun _stage _active _boundary =>
          .unavailable .notRegistered
  }

abbrev rowSixProfile : DefectRouting.Profile rowFiveProfile :=
  rowSixContract.toProfile

theorem rowFiveLedgerTerminal :
    rowFiveOutputFromLedger.terminal = .positiveStructuralGap := by
  unfold rowFiveOutputFromLedger rowFiveStage rowFiveRun
  rw [rowFiveContract.outputQuery_run_of_active containedDecision rowFourActive]
  exact activePayload_is_positiveGap

theorem rowFiveTargetVisibleInactive :
    Not (rowFiveProfile.TargetVisibleFocus.Active rowFiveStage) := by
  intro selected
  have terminal := selected.accepted
  have parentEqual : selected.parent = rowFiveStageActive :=
    Subsingleton.elim _ _
  cases parentEqual
  change rowFiveOutputFromLedger.terminal = .targetVisibleBoundary at terminal
  rw [rowFiveLedgerTerminal] at terminal
  cases terminal

def rowSixRun :=
  rowSixContract.run rowFiveStage

theorem rowSix_retains_literal_rowFive :
  rowSixRun.value.previous = rowFiveStage :=
  rowSixContract.run_previous rowFiveStage

theorem rowSix_retains_root_residual :
    Core.Residual.residualOf rowSixRun.value =
      HypostructurePDEExamples.RepresentedNS2DLocalTailPacket.zeroRootResidual :=
  by
    change Core.Residual.residualOf rowSixRun.value.previous =
      HypostructurePDEExamples.RepresentedNS2DLocalTailPacket.zeroRootResidual
    rw [rowSix_retains_literal_rowFive]
    exact rowFiveStage_retains_root_residual

theorem rowSix_skips_inactive_payload :
    Exists fun absent => rowSixRun.value.added =
      Core.Residual.Focus.Outcome.inactive absent :=
  rowSixContract.run_added_of_inactive rowFiveStage
    rowFiveTargetVisibleInactive

theorem rowSix_exact_work :
    rowSixRun.checks =
      rowFiveProfile.TargetVisibleFocus.selectionBudget.checks rowFiveStage :=
  rowSixContract.run_checks_of_inactive rowFiveStage
    rowFiveTargetVisibleInactive

theorem rowSix_target_selector_checks_exact :
    rowFiveProfile.TargetVisibleFocus.selectionBudget.checks rowFiveStage = 2 :=
  by
    rw [← rowFiveProfile.TargetVisibleFocus.select_checks rowFiveStage]
    change (Core.Residual.Focus.selectRefined rowFiveProfile.SuccessorFocus
      rowFiveProfile.targetVisibleRefinement rowFiveStage).checks = 2
    rw [Core.Residual.Focus.selectRefined_checks_of_parent_active
      rowFiveProfile.SuccessorFocus rowFiveProfile.targetVisibleRefinement
      rowFiveStage rowFiveStageActive]
    rfl

theorem rowSix_selector_checks_exact : rowSixRun.checks = 2 := by
  rw [rowSix_exact_work]
  exact rowSix_target_selector_checks_exact

theorem rowSix_work_is_bounded :
    rowSixRun.checks <=
      (rowFiveProfile.TargetVisibleFocus.selectionBudget.add
        rowSixContract.workBudget).coefficient *
      ((rowFiveProfile.TargetVisibleFocus.selectionBudget.add
        rowSixContract.workBudget).size rowFiveStage + 1) ^
      (rowFiveProfile.TargetVisibleFocus.selectionBudget.add
        rowSixContract.workBudget).degree :=
  rowSixContract.run_checks_bounded rowFiveStage

def importedAnalyticContracts : List Core.AuthorPrimitiveRef := []

theorem imported_analytic_boundary_is_empty :
    importedAnalyticContracts = [] :=
  rfl

#print axioms rowSix_retains_literal_rowFive
#print axioms rowSix_retains_root_residual
#print axioms rowSix_skips_inactive_payload
#print axioms rowSix_exact_work
#print axioms rowSix_target_selector_checks_exact
#print axioms rowSix_selector_checks_exact
#print axioms rowSix_work_is_bounded
#print axioms imported_analytic_boundary_is_empty

end

end HypostructurePDEExamples.RepresentedNS2DDefectRoutingPacket
