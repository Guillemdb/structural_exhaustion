import Hypostructure.PDE.Contract
import HypostructurePDEExamples.RepresentedNS2DConservativeCarrierPacket

/-!
# Represented 2D Navier--Stokes row-12 elliptic-constraint-tail packet

The represented row-11 packet is inactive because the row-10 successor is
inactive. Row 12 is still instantiated over the literal row-11 successor. Core
skips the CT3-to-CT14-to-CT15-to-CT13 payload on the inactive successor and
retains the predecessor ledger.
-/

namespace HypostructurePDEExamples.RepresentedNS2DEllipticConstraintTailPacket

open Hypostructure
open Hypostructure.Core
open Hypostructure.Core.Residual
open Hypostructure.PDE.FastTrack
open HypostructurePDEExamples.RepresentedNS2DConservativeCarrierPacket

noncomputable section

abbrev RowElevenProfile := rowElevenProfile
abbrev RowElevenStage :=
  EllipticConstraintTail.RowElevenStage RowElevenProfile
abbrev RowTwelveView :=
  EllipticConstraintTail.ActiveView RowElevenProfile

structure EllipticConstraintTailProblemContract where
  dyadicLowerMass : Nat
  dyadicCapacity : Nat
  gaugeCharge : Nat
  gaugeCapacity : Nat
  fallbackObstructionCost : Nat
  fallbackCharge : Nat
  fallbackDemand : Nat

def ellipticConstraintTailProblemContract :
    EllipticConstraintTailProblemContract where
  dyadicLowerMass := 1
  dyadicCapacity := 0
  gaugeCharge := 0
  gaugeCapacity := 0
  fallbackObstructionCost := 0
  fallbackCharge := 0
  fallbackDemand := 0

def rowElevenStage : RowElevenStage :=
  rowElevenRun.value

theorem rowElevenSuccessorInactive :
    Not ((ConservativeCarrier.SuccessorFocus RowElevenProfile).Active
      rowElevenStage) := by
  intro active
  change
    (BoundaryRepair.SuccessorFocus RowTenProfile).Active
      rowElevenRun.value.previous at active
  rw [rowEleven_retains_literal_row_ten] at active
  exact rowTenSuccessorInactive active

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

abbrev responseSpec : CT3.Spec RowTwelveView where
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
    Residual.Query RowTwelveView fun _view => Unit :=
  Residual.Query.residual.map fun _view _root => ()

def responseCoordinatesQuery :
    Residual.Query RowTwelveView fun _view =>
      Core.Finite.Enumeration Unit :=
  Residual.Query.residual.map fun _view _root =>
    Core.Finite.Enumeration.singleton ()

def responseCandidatesQuery :
    Residual.Query RowTwelveView fun _view =>
      Core.Finite.Enumeration Unit :=
  Residual.Query.residual.map fun _view _root =>
    Core.Finite.Enumeration.singleton ()

def responseRowsQuery :
    Residual.Query RowTwelveView fun _view =>
      Core.Finite.Enumeration Unit :=
  Residual.Query.residual.map fun _view _root =>
    Core.Finite.Enumeration.empty Unit

def responseCoverage
    (previous : RowTwelveView) (replacement : Unit) :
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

def responseCapability : CT3.Capability responseSpec :=
  EllipticConstraintTail.CanonicalCapability.response
    responseSourceQuery responseCoordinatesQuery responseCandidatesQuery
    responseRowsQuery
    (by
      change DecidableEq Bool
      infer_instance)
    (fun _previous _source _candidate => isTrue trivial)
    (fun _previous _source _candidate => isTrue trivial)
    (fun previous candidate _member => responseCoverage previous candidate)
    (fun previous row _member => responseCoverage previous row)

abbrev DyadicPrevious :=
  CT3.Stage responseSpec responseCapability

abbrev dyadicSpec : CT14.Spec DyadicPrevious where
  Member := fun _previous => Unit
  Label := fun _previous => Unit
  memberLowerMass := fun _previous _member =>
    ellipticConstraintTailProblemContract.dyadicLowerMass
  memberCapacity := fun _previous _member =>
    some ellipticConstraintTailProblemContract.dyadicCapacity
  memberLabel := fun _previous _member => some ()

def dyadicMemberQuery :
    Residual.Query DyadicPrevious fun _previous =>
      Core.Finite.Enumeration Unit :=
  Residual.Query.residual.map fun _previous _root =>
    Core.Finite.Enumeration.singleton ()

def dyadicCapability : CT14.Capability dyadicSpec :=
  EllipticConstraintTail.CanonicalCapability.dyadic dyadicMemberQuery
    (fun _previous => by
      change DecidableEq Unit
      infer_instance)

abbrev GaugeRankPrevious :=
  CT14.Stage dyadicSpec dyadicCapability

abbrev gaugeRankSpec : CT15.Spec GaugeRankPrevious where
  Coordinate := fun _previous => Unit
  TargetDependent := fun _previous _coordinate => False
  charge := fun _previous _coordinate =>
    ellipticConstraintTailProblemContract.gaugeCharge
  capacity := fun _previous =>
    ellipticConstraintTailProblemContract.gaugeCapacity

def gaugeCoordinateQuery :
    Residual.Query GaugeRankPrevious fun _previous =>
      Core.Finite.Enumeration Unit :=
  Residual.Query.residual.map fun _previous _root =>
    Core.Finite.Enumeration.singleton ()

def gaugeRankCapability : CT15.Capability gaugeRankSpec :=
  EllipticConstraintTail.CanonicalCapability.gaugeRank gaugeCoordinateQuery
    (fun _previous _coordinate => isFalse id)

abbrev FallbackPrevious :=
  CT15.Stage gaugeRankSpec gaugeRankCapability

abbrev fallbackSpec : CT13.Spec FallbackPrevious where
  Payer := fun _previous => Unit
  Obstruction := fun _previous => Unit
  Resource := fun _previous => Unit
  Eligible := fun _previous _payer => False
  obstructionCost := fun _previous _obstruction =>
    ellipticConstraintTailProblemContract.fallbackObstructionCost
  payerResource := fun _previous _payer => ()
  charge := fun _previous _payer =>
    ellipticConstraintTailProblemContract.fallbackCharge
  demand := fun _previous =>
    ellipticConstraintTailProblemContract.fallbackDemand

def payerQuery :
    Residual.Query FallbackPrevious fun _previous =>
      Core.Finite.Enumeration Unit :=
  Residual.Query.residual.map fun _previous _root =>
    Core.Finite.Enumeration.singleton ()

def obstructionSchedule : CT13.ObstructionSchedule Unit where
  fallbackDefault := ()
  remaining := []
  nodup := by decide
  decEq := inferInstance

def obstructionQuery :
    Residual.Query FallbackPrevious fun _previous =>
      CT13.ObstructionSchedule Unit :=
  Residual.Query.residual.map fun _previous _root =>
    obstructionSchedule

def tierTwoQuery :
    Residual.Query FallbackPrevious fun _previous =>
      Unit -> Core.Finite.Enumeration Unit :=
  Residual.Query.residual.map fun _previous _root _obstruction =>
    Core.Finite.Enumeration.singleton ()

def fallbackCapability : CT13.Capability fallbackSpec :=
  EllipticConstraintTail.CanonicalCapability.fallback payerQuery obstructionQuery
    tierTwoQuery
    (fun _previous _payer => isFalse id)
    (fun _previous => by
      change DecidableEq Unit
      infer_instance)

def rowTwelveContract :
    PDE.Contract.EllipticConstraintTailContract RowElevenProfile :=
  PDE.Contract.EllipticConstraintTailContract.ofCapabilityCanonicalEnvelope
    responseSpec responseCapability dyadicSpec dyadicCapability
    gaugeRankSpec gaugeRankCapability fallbackSpec fallbackCapability

abbrev rowTwelveProfile :
    EllipticConstraintTail.Profile RowElevenProfile :=
  rowTwelveContract.toProfile

def rowTwelveRun :=
  rowTwelveContract.run rowElevenStage

theorem rowTwelve_retains_literal_row_eleven :
    rowTwelveRun.value.previous = rowElevenStage :=
  rowTwelveContract.run_previous rowElevenStage

theorem rowTwelve_skips_inactive_payload :
    rowTwelveRun.checks =
      (ConservativeCarrier.SuccessorFocus RowElevenProfile).selectionBudget.checks
        rowElevenStage :=
  rowTwelveContract.run_checks_of_inactive rowElevenStage
    rowElevenSuccessorInactive

theorem rowTwelve_work_is_bounded :
    rowTwelveRun.checks <=
      ((ConservativeCarrier.SuccessorFocus RowElevenProfile).selectionBudget.add
        (EllipticConstraintTail.payloadBudget rowTwelveProfile)).coefficient *
      (((ConservativeCarrier.SuccessorFocus RowElevenProfile).selectionBudget.add
        (EllipticConstraintTail.payloadBudget rowTwelveProfile)).size
          rowElevenStage + 1) ^
      ((ConservativeCarrier.SuccessorFocus RowElevenProfile).selectionBudget.add
        (EllipticConstraintTail.payloadBudget rowTwelveProfile)).degree :=
  rowTwelveContract.run_checks_bounded rowElevenStage

theorem rowTwelve_retains_root_residual :
    Core.Residual.residualOf rowTwelveRun.value =
      HypostructurePDEExamples.RepresentedNS2DLocalTailPacket.zeroRootResidual :=
  by
    change Core.Residual.residualOf rowTwelveRun.value.previous =
      HypostructurePDEExamples.RepresentedNS2DLocalTailPacket.zeroRootResidual
    rw [rowTwelve_retains_literal_row_eleven]
    exact rowEleven_retains_root_residual

#print axioms rowTwelve_skips_inactive_payload
#print axioms rowTwelve_work_is_bounded

end

end HypostructurePDEExamples.RepresentedNS2DEllipticConstraintTailPacket
