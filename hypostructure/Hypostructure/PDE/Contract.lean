import Hypostructure.Core.Contract
import Hypostructure.PDE.FastTrack.CapacityProfile
import Hypostructure.PDE.FastTrack.ExactResponseCoverage
import Hypostructure.PDE.FastTrack.ProfileFamily
import Hypostructure.PDE.FastTrack.BoundaryRepair
import Hypostructure.PDE.FastTrack.ConservativeCarrier
import Hypostructure.PDE.FastTrack.EllipticConstraintTail

/-!
# PDE proof contracts

The PDE contract layer is the only PDE-facing place where an application should
register irreducible analytic or finite-profile parameters.  Executors below
this layer derive payload checks, active routing proofs, ledgers, and terminals
from the registered CT capabilities.
-/

namespace Hypostructure.PDE.Contract

open Hypostructure.Core
open Hypostructure.PDE.FastTrack

universe uPrevious uPotential uCurrent uMember uLabel uCandidate
universe uRepresentative uContext uCoordinate uValue uRow
universe uRepresentative7 uContext7 uCoordinate7 uValue7
universe uRankCoordinate uSupportCoordinate uCode uCarrier uQuotient
  uNextQuotient uPayer uObstruction uResource
universe uTarget uOffset uPosition uThickValue uState uPeeled uDemand uTier
  uCell
universe uDatum uClass uPromotion uCell10 uMember10 uLabel10 uCandidate10
universe uSite uWitness uMember11 uLabel11 uCell11
universe uRepresentative12 uContext12 uCoordinate12 uValue12 uCandidate12 uRow12
universe uMember12 uLabel12 uRankCoordinate12 uPayer12 uObstruction12 uResource12

variable {Previous : Type uPrevious}
variable {Potential : Type uPotential} {Current : Type uCurrent}
variable [NormedAddCommGroup Potential] [InnerProductSpace Real Potential]
variable [CompleteSpace Potential]
variable [NormedAddCommGroup Current] [InnerProductSpace Real Current]
variable [CompleteSpace Current]
variable {focus : Residual.Focus.Profile Previous}
variable {rowFive : DirectedExhaustiveness.Profile Previous focus Potential Current}
variable {rowSix : DefectRouting.Profile rowFive}

/-- PDE contract for row 5 directed exhaustiveness.

The application registers the row-5 profile as the contract payload.  Public
execution, work accounting, ledger reads, and focus routing are exposed through
this contract namespace so downstream examples do not call fast-track plumbing
directly. -/
structure DirectedExhaustiveness
    (Previous : Type uPrevious) (focus : Residual.Focus.Profile Previous)
    (Potential : Type uPotential) (Current : Type uCurrent)
    [NormedAddCommGroup Potential] [InnerProductSpace Real Potential]
    [CompleteSpace Potential]
    [NormedAddCommGroup Current] [InnerProductSpace Real Current]
    [CompleteSpace Current] where
  profile :
    _root_.Hypostructure.PDE.FastTrack.DirectedExhaustiveness.Profile.{
      uPrevious, uPotential, uCurrent, uRankCoordinate, uSupportCoordinate,
      uCode, uCarrier, uQuotient, uNextQuotient}
      Previous focus Potential Current

namespace DirectedExhaustiveness

variable {focus : Residual.Focus.Profile Previous}

abbrev toProfile
    (contract : DirectedExhaustiveness Previous focus Potential Current) :
    _root_.Hypostructure.PDE.FastTrack.DirectedExhaustiveness.Profile.{
      uPrevious, uPotential, uCurrent, uRankCoordinate, uSupportCoordinate,
      uCode, uCarrier, uQuotient, uNextQuotient}
      Previous focus Potential Current :=
  contract.profile

def workBudget
    (contract : DirectedExhaustiveness Previous focus Potential Current) :
    PolynomialCheckBudget Previous :=
  _root_.Hypostructure.PDE.FastTrack.DirectedExhaustiveness.payloadBudget
    contract.toProfile

def run (contract : DirectedExhaustiveness Previous focus Potential Current)
    (previous : Previous) :
    Counted
      (_root_.Hypostructure.PDE.FastTrack.DirectedExhaustiveness.Stage
        contract.toProfile) :=
  _root_.Hypostructure.PDE.FastTrack.DirectedExhaustiveness.run
    contract.toProfile previous

@[simp] theorem run_previous
    (contract : DirectedExhaustiveness Previous focus Potential Current)
    (previous : Previous) :
    (contract.run previous).value.previous = previous :=
  _root_.Hypostructure.PDE.FastTrack.DirectedExhaustiveness.run_previous
    contract.toProfile previous

def runActiveProof
    (contract : DirectedExhaustiveness Previous focus Potential Current)
    (previous : Previous) (active : focus.Active previous) :
    contract.toProfile.SuccessorFocus.Active
      (contract.run previous).value :=
  _root_.Hypostructure.PDE.FastTrack.DirectedExhaustiveness.runActiveProof
    contract.toProfile previous active

theorem outputQuery_run_of_active
    (contract : DirectedExhaustiveness Previous focus Potential Current)
    (previous : Previous) (active : focus.Active previous) :
    contract.toProfile.outputQuery.read (contract.run previous).value
        (contract.runActiveProof previous active) =
      _root_.Hypostructure.PDE.FastTrack.DirectedExhaustiveness.generateActive
        contract.toProfile (Residual.Focus.ActiveView.of previous active) :=
  _root_.Hypostructure.PDE.FastTrack.DirectedExhaustiveness.outputQuery_run_of_active
    contract.toProfile previous active

theorem run_checks_of_active
    (contract : DirectedExhaustiveness Previous focus Potential Current)
    (previous : Previous) (active : focus.Active previous) :
    (contract.run previous).checks =
      focus.selectionBudget.checks previous +
        contract.workBudget.checks previous :=
  _root_.Hypostructure.PDE.FastTrack.DirectedExhaustiveness.run_checks_of_active
    contract.toProfile previous active

theorem run_checks_of_inactive
    (contract : DirectedExhaustiveness Previous focus Potential Current)
    (previous : Previous) (inactive : Not (focus.Active previous)) :
    (contract.run previous).checks =
      focus.selectionBudget.checks previous :=
  _root_.Hypostructure.PDE.FastTrack.DirectedExhaustiveness.run_checks_of_inactive
    contract.toProfile previous inactive

theorem run_checks_bounded
    (contract : DirectedExhaustiveness Previous focus Potential Current)
    (previous : Previous) :
    (contract.run previous).checks <=
      (focus.selectionBudget.add contract.workBudget).coefficient *
        ((focus.selectionBudget.add contract.workBudget).size previous + 1) ^
          (focus.selectionBudget.add contract.workBudget).degree :=
  _root_.Hypostructure.PDE.FastTrack.DirectedExhaustiveness.run_checks_bounded
    contract.toProfile previous

end DirectedExhaustiveness

/-- PDE contract for row 6 defect routing. -/
structure DefectRouting
    (rowFive :
      _root_.Hypostructure.PDE.FastTrack.DirectedExhaustiveness.Profile.{
        uPrevious, uPotential, uCurrent, uObstruction, uResource,
        uRepresentative, uContext, uCoordinate, uValue}
        Previous focus Potential Current) where
  profile :
    _root_.Hypostructure.PDE.FastTrack.DefectRouting.Profile.{
      uPrevious, uPotential, uCurrent, uPayer, uObstruction, uResource,
      uRepresentative, uContext, uCoordinate, uValue} rowFive

namespace DefectRouting

variable {focus : Residual.Focus.Profile Previous}
variable {rowFive :
  _root_.Hypostructure.PDE.FastTrack.DirectedExhaustiveness.Profile.{
    uPrevious, uPotential, uCurrent, uObstruction, uResource,
    uRepresentative, uContext, uCoordinate, uValue}
    Previous focus Potential Current}

abbrev toProfile (contract : DefectRouting rowFive) :
    _root_.Hypostructure.PDE.FastTrack.DefectRouting.Profile.{
      uPrevious, uPotential, uCurrent, uPayer, uObstruction, uResource,
      uRepresentative, uContext, uCoordinate, uValue} rowFive :=
  contract.profile

def workBudget (contract : DefectRouting rowFive) :
    PolynomialCheckBudget
      (_root_.Hypostructure.PDE.FastTrack.DefectRouting.RowFiveStage rowFive) :=
  _root_.Hypostructure.PDE.FastTrack.DefectRouting.payloadBudget
    contract.toProfile

def run (contract : DefectRouting rowFive)
    (previous :
      _root_.Hypostructure.PDE.FastTrack.DefectRouting.RowFiveStage rowFive) :
    Counted
      (_root_.Hypostructure.PDE.FastTrack.DefectRouting.Stage
        contract.toProfile) :=
  _root_.Hypostructure.PDE.FastTrack.DefectRouting.run
    contract.toProfile previous

@[simp] theorem run_previous (contract : DefectRouting rowFive)
    (previous :
      _root_.Hypostructure.PDE.FastTrack.DefectRouting.RowFiveStage rowFive) :
    (contract.run previous).value.previous = previous :=
  _root_.Hypostructure.PDE.FastTrack.DefectRouting.run_previous
    contract.toProfile previous

theorem run_checks_of_inactive (contract : DefectRouting rowFive)
    (previous :
      _root_.Hypostructure.PDE.FastTrack.DefectRouting.RowFiveStage rowFive)
    (inactive : Not (rowFive.TargetVisibleFocus.Active previous)) :
    (contract.run previous).checks =
      rowFive.TargetVisibleFocus.selectionBudget.checks previous :=
  _root_.Hypostructure.PDE.FastTrack.DefectRouting.run_checks_of_inactive
    contract.toProfile previous inactive

theorem run_added_of_inactive (contract : DefectRouting rowFive)
    (previous :
      _root_.Hypostructure.PDE.FastTrack.DefectRouting.RowFiveStage rowFive)
    (inactive : Not (rowFive.TargetVisibleFocus.Active previous)) :
    Exists fun absent =>
      (contract.run previous).value.added =
        Residual.Focus.Outcome.inactive absent :=
  _root_.Hypostructure.PDE.FastTrack.DefectRouting.run_added_of_inactive
    contract.toProfile previous inactive

theorem run_checks_bounded (contract : DefectRouting rowFive)
    (previous :
      _root_.Hypostructure.PDE.FastTrack.DefectRouting.RowFiveStage rowFive) :
    (contract.run previous).checks <=
      (rowFive.TargetVisibleFocus.selectionBudget.add
        contract.workBudget).coefficient *
      ((rowFive.TargetVisibleFocus.selectionBudget.add
        contract.workBudget).size previous + 1) ^
      (rowFive.TargetVisibleFocus.selectionBudget.add
        contract.workBudget).degree :=
  _root_.Hypostructure.PDE.FastTrack.DefectRouting.run_checks_bounded
    contract.toProfile previous

end DefectRouting

/-- Minimal PDE contract for the row-7 capacity-target fast track.

The application registers the CT14 and CT1 primitive capabilities.  Public
constructors derive the payload function, active payload equality, focused
routing, downstream ledger output, and canonical work envelope from those
capabilities. -/
structure CapacityTarget
    (rowSix : DefectRouting.Profile rowFive) where
  capacitySpec :
    _root_.Hypostructure.CT14.Spec.{_, uMember, uLabel}
      (CapacityProfile.ActiveView rowSix)
  capacityCapability :
    _root_.Hypostructure.CT14.Capability capacitySpec
  targetSpec :
    _root_.Hypostructure.CT1.Spec.{_, uCandidate}
      (_root_.Hypostructure.CT14.Stage capacitySpec capacityCapability)
  targetCapability :
    _root_.Hypostructure.CT1.Capability targetSpec
  inputSize : CapacityProfile.RowSixStage rowSix -> Nat
  workCoefficient : Nat
  workDegree : Nat
  workBound : forall previous,
    CapacityProfile.canonicalPayloadChecksFor capacitySpec capacityCapability
      targetSpec targetCapability previous <=
        workCoefficient * (inputSize previous + 1) ^ workDegree

namespace CapacityTarget

/-- Core work envelope derived from a PDE capacity-target contract. -/
noncomputable def workEnvelope (contract : CapacityTarget rowSix) :
    Core.Contract.WorkEnvelope (CapacityProfile.RowSixStage rowSix) where
  size := contract.inputSize
  checks := CapacityProfile.canonicalPayloadChecksFor contract.capacitySpec
    contract.capacityCapability contract.targetSpec contract.targetCapability
  coefficient := contract.workCoefficient
  degree := contract.workDegree
  bounded := contract.workBound

/-- Build the executable row-7 fast-track profile from the PDE contract. -/
noncomputable def toCapacityProfile (contract : CapacityTarget rowSix) :
    CapacityProfile.Profile rowSix where
  capacitySpec := contract.capacitySpec
  capacityCapability := contract.capacityCapability
  targetSpec := contract.targetSpec
  targetCapability := contract.targetCapability
  inputSize := contract.inputSize
  payloadChecks := contract.workEnvelope.checks
  payloadChecks_active := by
    intro previous active
    exact CapacityProfile.canonicalPayloadChecksFor_active
      contract.capacitySpec contract.capacityCapability contract.targetSpec
      contract.targetCapability previous active
  workCoefficient := contract.workEnvelope.coefficient
  workDegree := contract.workEnvelope.degree
  workBound := contract.workEnvelope.bounded

/-- Execute row 7 directly from the PDE contract. -/
noncomputable def run (contract : CapacityTarget rowSix)
    (previous : CapacityProfile.RowSixStage rowSix) :
    Counted (CapacityProfile.Stage contract.toCapacityProfile) :=
  CapacityProfile.run contract.toCapacityProfile previous

@[simp] theorem run_previous (contract : CapacityTarget rowSix)
    (previous : CapacityProfile.RowSixStage rowSix) :
    (contract.run previous).value.previous = previous :=
  CapacityProfile.run_previous contract.toCapacityProfile previous

theorem run_checks_of_inactive (contract : CapacityTarget rowSix)
    (previous : CapacityProfile.RowSixStage rowSix)
    (inactive : Not (rowSix.CapacityReadyFocus.Active previous)) :
    (contract.run previous).checks =
      rowSix.CapacityReadyFocus.selectionBudget.checks previous :=
  CapacityProfile.run_checks_of_inactive contract.toCapacityProfile previous
    inactive

def runActiveProof (contract : CapacityTarget rowSix)
    (previous : CapacityProfile.RowSixStage rowSix)
    (active : rowSix.CapacityReadyFocus.Active previous) :
    (CapacityProfile.SuccessorFocus contract.toCapacityProfile).Active
      (contract.run previous).value :=
  CapacityProfile.runActiveProof contract.toCapacityProfile previous active

theorem outputQuery_run_of_active (contract : CapacityTarget rowSix)
    (previous : CapacityProfile.RowSixStage rowSix)
    (active : rowSix.CapacityReadyFocus.Active previous) :
    (CapacityProfile.outputQuery contract.toCapacityProfile).read
        (contract.run previous).value
        (contract.runActiveProof previous active) =
      (CapacityProfile.generateActiveCounted contract.toCapacityProfile
        (Residual.Focus.ActiveView.of previous active)).value :=
  CapacityProfile.outputQuery_run_of_active contract.toCapacityProfile previous
    active

theorem run_checks_of_active (contract : CapacityTarget rowSix)
    (previous : CapacityProfile.RowSixStage rowSix)
    (active : rowSix.CapacityReadyFocus.Active previous) :
    (contract.run previous).checks =
      rowSix.CapacityReadyFocus.selectionBudget.checks previous +
        (CapacityProfile.generateActiveCounted contract.toCapacityProfile
          (Residual.Focus.ActiveView.of previous active)).checks :=
  CapacityProfile.run_checks_of_active contract.toCapacityProfile previous
    active

theorem run_checks_bounded (contract : CapacityTarget rowSix)
    (previous : CapacityProfile.RowSixStage rowSix) :
    (contract.run previous).checks <=
      (rowSix.CapacityReadyFocus.selectionBudget.add
        (CapacityProfile.payloadBudget contract.toCapacityProfile)).coefficient *
      ((rowSix.CapacityReadyFocus.selectionBudget.add
        (CapacityProfile.payloadBudget contract.toCapacityProfile)).size previous + 1) ^
      (rowSix.CapacityReadyFocus.selectionBudget.add
        (CapacityProfile.payloadBudget contract.toCapacityProfile)).degree :=
  CapacityProfile.run_checks_bounded contract.toCapacityProfile previous

noncomputable def ofCapabilityCanonicalEnvelope
    (capacitySpec :
      _root_.Hypostructure.CT14.Spec.{_, uMember, uLabel}
        (CapacityProfile.ActiveView rowSix))
    (capacityCapability :
      _root_.Hypostructure.CT14.Capability capacitySpec)
    (targetSpec :
      _root_.Hypostructure.CT1.Spec.{_, uCandidate}
        (_root_.Hypostructure.CT14.Stage capacitySpec capacityCapability))
    (targetCapability :
      _root_.Hypostructure.CT1.Capability targetSpec) :
    CapacityTarget rowSix where
  capacitySpec := capacitySpec
  capacityCapability := capacityCapability
  targetSpec := targetSpec
  targetCapability := targetCapability
  inputSize :=
    CapacityProfile.canonicalPayloadCapabilityBound capacitySpec
      capacityCapability targetSpec targetCapability
  workCoefficient := 1
  workDegree := 1
  workBound := by
    intro previous
    exact Nat.le_trans
      (CapacityProfile.canonicalPayloadChecksFor_le_capability_bound
        capacitySpec capacityCapability targetSpec targetCapability previous)
      (by simp)

end CapacityTarget

/-- Minimal PDE contract for row-8 exact response coverage.

The application registers the CT3 and CT7 capabilities and one outer work
envelope.  The CT3-to-CT7 payload composition, active payload equality, focused
routing, and ledger output are derived by the framework. -/
structure ExactResponse
    (rowSeven : CapacityProfile.Profile rowSix) where
  responseSpec :
    _root_.Hypostructure.CT3.Spec.{_, uRepresentative, uContext,
      uCoordinate, uValue, uCandidate, uRow}
      (ExactResponseCoverage.ActiveView rowSeven)
  responseCapability :
    _root_.Hypostructure.CT3.Capability responseSpec
  contextSpec :
    _root_.Hypostructure.CT7.Spec.{_, uRepresentative7, uContext7,
      uCoordinate7, uValue7}
      (_root_.Hypostructure.CT3.Stage responseSpec responseCapability)
  contextCapability :
    _root_.Hypostructure.CT7.Capability contextSpec
  inputSize : ExactResponseCoverage.RowSevenStage rowSeven -> Nat
  workCoefficient : Nat
  workDegree : Nat
  workBound : forall previous,
    ExactResponseCoverage.canonicalPayloadChecksFor responseSpec
      responseCapability contextSpec contextCapability previous <=
        workCoefficient * (inputSize previous + 1) ^ workDegree

namespace ExactResponse

variable {rowSeven :
  CapacityProfile.Profile (Previous := Previous) (Potential := Potential)
    (Current := Current) rowSix}

theorem canonicalPayloadChecksFor_le_capability_envelope
    (responseSpec :
      _root_.Hypostructure.CT3.Spec.{_, uRepresentative, uContext,
        uCoordinate, uValue, uCandidate, uRow}
        (ExactResponseCoverage.ActiveView rowSeven))
    (responseCapability :
      _root_.Hypostructure.CT3.Capability responseSpec)
    (contextSpec :
      _root_.Hypostructure.CT7.Spec.{_, uRepresentative7, uContext7,
        uCoordinate7, uValue7}
        (_root_.Hypostructure.CT3.Stage responseSpec responseCapability))
    (contextCapability :
      _root_.Hypostructure.CT7.Capability contextSpec)
    (responseBound contextBound : Nat)
    (responseEnvelope : forall view,
      responseCapability.workCoefficient *
          (responseCapability.inputSize view + 1) ^
          responseCapability.workDegree <= responseBound)
    (contextEnvelope : forall stage,
      (contextCapability.linearWorkBudget).coefficient *
          ((contextCapability.linearWorkBudget).size stage + 1) ^
          (contextCapability.linearWorkBudget).degree <= contextBound)
    (previous : ExactResponseCoverage.RowSevenStage rowSeven) :
    ExactResponseCoverage.canonicalPayloadChecksFor responseSpec
        responseCapability contextSpec contextCapability previous <=
      responseBound + contextBound :=
  by
    let responseChecksLe : forall view,
        (_root_.Hypostructure.CT3.run responseSpec responseCapability
          view).checks <= responseBound := fun view =>
      Nat.le_trans
        ((_root_.Hypostructure.CT3.run responseSpec responseCapability
          view).checks_le_polynomial)
        (responseEnvelope view)
    let contextChecksLe : forall stage,
        (_root_.Hypostructure.CT7.run contextSpec contextCapability
          stage).checks <= contextBound := fun stage =>
      Nat.le_trans
        ((_root_.Hypostructure.CT7.run contextSpec contextCapability
          stage).checks_le_polynomial)
        (contextEnvelope stage)
    exact ExactResponseCoverage.canonicalPayloadChecksFor_le_of_component_bounds
      responseSpec responseCapability contextSpec contextCapability
      responseBound contextBound responseChecksLe contextChecksLe previous

/-- Build a row-8 contract from primitive CT3/CT7 capabilities and coarse
component envelopes.  The application registers only those envelopes; the
canonical payload, active split, CT sequencing, and work proof are derived
inside the PDE contract layer. -/
noncomputable def ofCapabilityEnvelope
    (responseSpec :
      _root_.Hypostructure.CT3.Spec.{_, uRepresentative, uContext,
        uCoordinate, uValue, uCandidate, uRow}
        (ExactResponseCoverage.ActiveView rowSeven))
    (responseCapability :
      _root_.Hypostructure.CT3.Capability responseSpec)
    (contextSpec :
      _root_.Hypostructure.CT7.Spec.{_, uRepresentative7, uContext7,
        uCoordinate7, uValue7}
        (_root_.Hypostructure.CT3.Stage responseSpec responseCapability))
    (contextCapability :
      _root_.Hypostructure.CT7.Capability contextSpec)
    (inputSize : ExactResponseCoverage.RowSevenStage rowSeven -> Nat)
    (workCoefficient workDegree responseBound contextBound : Nat)
    (responseEnvelope : forall view,
      responseCapability.workCoefficient *
          (responseCapability.inputSize view + 1) ^
          responseCapability.workDegree <= responseBound)
    (contextEnvelope : forall stage,
      (contextCapability.linearWorkBudget).coefficient *
          ((contextCapability.linearWorkBudget).size stage + 1) ^
          (contextCapability.linearWorkBudget).degree <= contextBound)
    (envelope : forall previous,
      responseBound + contextBound <=
        workCoefficient * (inputSize previous + 1) ^ workDegree) :
    ExactResponse rowSeven where
  responseSpec := responseSpec
  responseCapability := responseCapability
  contextSpec := contextSpec
  contextCapability := contextCapability
  inputSize := inputSize
  workCoefficient := workCoefficient
  workDegree := workDegree
  workBound := fun previous =>
    Nat.le_trans
      (canonicalPayloadChecksFor_le_capability_envelope
        responseSpec responseCapability contextSpec contextCapability
        responseBound contextBound responseEnvelope contextEnvelope previous)
      (envelope previous)

/-- Build a zero-size row-8 contract from component envelopes.

This is the common finite-fixture and compact-profile case: the application
registers the primitive CT capabilities and the two component envelope bounds,
while the contract derives the outer degree-zero payload envelope. -/
noncomputable def ofZeroSizeCapabilityEnvelope
    (responseSpec :
      _root_.Hypostructure.CT3.Spec.{_, uRepresentative, uContext,
        uCoordinate, uValue, uCandidate, uRow}
        (ExactResponseCoverage.ActiveView rowSeven))
    (responseCapability :
      _root_.Hypostructure.CT3.Capability responseSpec)
    (contextSpec :
      _root_.Hypostructure.CT7.Spec.{_, uRepresentative7, uContext7,
        uCoordinate7, uValue7}
        (_root_.Hypostructure.CT3.Stage responseSpec responseCapability))
    (contextCapability :
      _root_.Hypostructure.CT7.Capability contextSpec)
    (responseBound contextBound : Nat)
    (responseEnvelope : forall view,
      responseCapability.workCoefficient *
          (responseCapability.inputSize view + 1) ^
          responseCapability.workDegree <= responseBound)
    (contextEnvelope : forall stage,
      (contextCapability.linearWorkBudget).coefficient *
          ((contextCapability.linearWorkBudget).size stage + 1) ^
          (contextCapability.linearWorkBudget).degree <= contextBound) :
    ExactResponse rowSeven :=
  ofCapabilityEnvelope responseSpec responseCapability contextSpec
    contextCapability (fun _previous => 0) (responseBound + contextBound) 0
    responseBound contextBound responseEnvelope contextEnvelope
    (by intro _previous; simp)

noncomputable def ofCapabilityCanonicalEnvelope
    (responseSpec :
      _root_.Hypostructure.CT3.Spec.{_, uRepresentative, uContext,
        uCoordinate, uValue, uCandidate, uRow}
        (ExactResponseCoverage.ActiveView rowSeven))
    (responseCapability :
      _root_.Hypostructure.CT3.Capability responseSpec)
    (contextSpec :
      _root_.Hypostructure.CT7.Spec.{_, uRepresentative7, uContext7,
        uCoordinate7, uValue7}
        (_root_.Hypostructure.CT3.Stage responseSpec responseCapability))
    (contextCapability :
      _root_.Hypostructure.CT7.Capability contextSpec) :
    ExactResponse rowSeven where
  responseSpec := responseSpec
  responseCapability := responseCapability
  contextSpec := contextSpec
  contextCapability := contextCapability
  inputSize := ExactResponseCoverage.canonicalPayloadChecksFor responseSpec
    responseCapability contextSpec contextCapability
  workCoefficient := 1
  workDegree := 1
  workBound := by
    intro previous
    simp

noncomputable def workEnvelope (contract : ExactResponse rowSeven) :
    Core.Contract.WorkEnvelope
      (ExactResponseCoverage.RowSevenStage rowSeven) where
  size := contract.inputSize
  checks := ExactResponseCoverage.canonicalPayloadChecksFor
    contract.responseSpec contract.responseCapability contract.contextSpec
    contract.contextCapability
  coefficient := contract.workCoefficient
  degree := contract.workDegree
  bounded := contract.workBound

noncomputable def toProfile (contract : ExactResponse rowSeven) :
    ExactResponseCoverage.Profile rowSeven where
  responseSpec := contract.responseSpec
  responseCapability := contract.responseCapability
  contextSpec := contract.contextSpec
  contextCapability := contract.contextCapability
  inputSize := contract.inputSize
  payloadChecks := contract.workEnvelope.checks
  payloadChecks_active := by
    intro previous active
    exact ExactResponseCoverage.canonicalPayloadChecksFor_active
      contract.responseSpec contract.responseCapability contract.contextSpec
      contract.contextCapability previous active
  workCoefficient := contract.workEnvelope.coefficient
  workDegree := contract.workEnvelope.degree
  workBound := contract.workEnvelope.bounded

noncomputable def run (contract : ExactResponse rowSeven)
    (previous : ExactResponseCoverage.RowSevenStage rowSeven) :
    Counted (ExactResponseCoverage.Stage contract.toProfile) :=
  ExactResponseCoverage.run contract.toProfile previous

@[simp] theorem run_previous (contract : ExactResponse rowSeven)
    (previous : ExactResponseCoverage.RowSevenStage rowSeven) :
    (contract.run previous).value.previous = previous :=
  ExactResponseCoverage.run_previous contract.toProfile previous

theorem run_checks_of_active (contract : ExactResponse rowSeven)
    (previous : ExactResponseCoverage.RowSevenStage rowSeven)
    (active : (CapacityProfile.PositiveCapacityFocus rowSeven).Active
      previous) :
    (contract.run previous).checks =
      (CapacityProfile.PositiveCapacityFocus rowSeven).selectionBudget.checks
        previous +
        (ExactResponseCoverage.generateActiveCounted contract.toProfile
          (Residual.Focus.ActiveView.of previous active)).checks :=
  ExactResponseCoverage.run_checks_of_active contract.toProfile previous active

theorem run_checks_of_inactive (contract : ExactResponse rowSeven)
    (previous : ExactResponseCoverage.RowSevenStage rowSeven)
    (inactive : Not ((CapacityProfile.PositiveCapacityFocus rowSeven).Active
      previous)) :
    (contract.run previous).checks =
      (CapacityProfile.PositiveCapacityFocus rowSeven).selectionBudget.checks
        previous :=
  ExactResponseCoverage.run_checks_of_inactive contract.toProfile previous
    inactive

theorem run_checks_bounded (contract : ExactResponse rowSeven)
    (previous : ExactResponseCoverage.RowSevenStage rowSeven) :
    (contract.run previous).checks <=
      ((CapacityProfile.PositiveCapacityFocus rowSeven).selectionBudget.add
        (ExactResponseCoverage.payloadBudget contract.toProfile)).coefficient *
      (((CapacityProfile.PositiveCapacityFocus rowSeven).selectionBudget.add
        (ExactResponseCoverage.payloadBudget contract.toProfile)).size
          previous + 1) ^
      ((CapacityProfile.PositiveCapacityFocus rowSeven).selectionBudget.add
        (ExactResponseCoverage.payloadBudget contract.toProfile)).degree :=
  ExactResponseCoverage.run_checks_bounded contract.toProfile previous

end ExactResponse

variable {rowSeven :
  CapacityProfile.Profile (Previous := Previous) (Potential := Potential)
    (Current := Current) rowSix}

/-- Minimal PDE contract for row-9 profile-family localization.

The application registers CT17, CT12, and CT11 capabilities plus component
work envelopes.  The CT17-to-CT12-to-CT11 payload composition, focused
routing, successor ledger, and public work theorems are derived by the
framework. -/
structure ProfileFamilyContract
    (rowEight : ExactResponseCoverage.Profile rowSeven) where
  thickeningSpec :
    _root_.Hypostructure.CT17.Spec.{_, uTarget, uOffset, uPosition,
      uThickValue} (_root_.Hypostructure.PDE.FastTrack.ProfileFamily.ActiveView
        rowEight)
  thickeningCapability :
    _root_.Hypostructure.CT17.Capability thickeningSpec
  peelingSpec :
    _root_.Hypostructure.CT12.Spec.{_, uState, uPeeled, uDemand, uTier}
      (_root_.Hypostructure.CT17.Stage thickeningSpec thickeningCapability)
  peelingCapability :
    _root_.Hypostructure.CT12.Capability peelingSpec
  budgetSpec :
    _root_.Hypostructure.CT11.Spec.{_, uCell}
      (_root_.Hypostructure.CT12.Stage peelingSpec peelingCapability)
  budgetCapability :
    _root_.Hypostructure.CT11.Capability budgetSpec
  inputSize :
    _root_.Hypostructure.PDE.FastTrack.ProfileFamily.RowEightStage rowEight ->
      Nat
  workCoefficient : Nat
  workDegree : Nat
  workBound : forall previous,
    _root_.Hypostructure.PDE.FastTrack.ProfileFamily.canonicalPayloadChecksFor
      thickeningSpec thickeningCapability peelingSpec peelingCapability
      budgetSpec budgetCapability previous <=
        workCoefficient * (inputSize previous + 1) ^ workDegree

namespace ProfileFamilyContract

variable {rowEight : ExactResponseCoverage.Profile rowSeven}

theorem canonicalPayloadChecksFor_le_capability_envelope
    (thickeningSpec :
      _root_.Hypostructure.CT17.Spec.{_, uTarget, uOffset, uPosition,
        uThickValue}
        (_root_.Hypostructure.PDE.FastTrack.ProfileFamily.ActiveView
          rowEight))
    (thickeningCapability :
      _root_.Hypostructure.CT17.Capability thickeningSpec)
    (peelingSpec :
      _root_.Hypostructure.CT12.Spec.{_, uState, uPeeled, uDemand, uTier}
        (_root_.Hypostructure.CT17.Stage thickeningSpec
          thickeningCapability))
    (peelingCapability :
      _root_.Hypostructure.CT12.Capability peelingSpec)
    (budgetSpec :
      _root_.Hypostructure.CT11.Spec.{_, uCell}
        (_root_.Hypostructure.CT12.Stage peelingSpec peelingCapability))
    (budgetCapability :
      _root_.Hypostructure.CT11.Capability budgetSpec)
    (thickeningBound peelingBound budgetBound : Nat)
    (thickeningEnvelope : forall view,
      thickeningCapability.workCoefficient *
          (thickeningCapability.inputSize view + 1) ^
          thickeningCapability.workDegree <= thickeningBound)
    (peelingEnvelope : forall stage,
      peelingCapability.workCoefficient *
          (peelingCapability.inputSize stage + 1) ^
          peelingCapability.workDegree <= peelingBound)
    (budgetEnvelope : forall stage,
      budgetCapability.workCoefficient *
          (budgetCapability.inputSize stage + 1) ^
          budgetCapability.workDegree <= budgetBound)
    (previous :
      _root_.Hypostructure.PDE.FastTrack.ProfileFamily.RowEightStage
        rowEight) :
    _root_.Hypostructure.PDE.FastTrack.ProfileFamily.canonicalPayloadChecksFor
        thickeningSpec thickeningCapability peelingSpec peelingCapability
        budgetSpec budgetCapability previous <=
      thickeningBound + peelingBound + budgetBound :=
  by
    let thickeningChecksLe : forall view,
        (_root_.Hypostructure.CT17.run thickeningSpec thickeningCapability
          view).checks <= thickeningBound := fun view =>
      Nat.le_trans
        ((_root_.Hypostructure.CT17.run thickeningSpec thickeningCapability
          view).checks_le_polynomial)
        (thickeningEnvelope view)
    let peelingChecksLe : forall stage,
        (_root_.Hypostructure.CT12.run peelingSpec peelingCapability
          stage).checks <= peelingBound := fun stage =>
      Nat.le_trans
        ((_root_.Hypostructure.CT12.run peelingSpec peelingCapability
          stage).checks_le_polynomial)
        (peelingEnvelope stage)
    let budgetChecksLe : forall stage,
        (_root_.Hypostructure.CT11.run budgetSpec budgetCapability
          stage).checks <= budgetBound := fun stage =>
      Nat.le_trans
        ((_root_.Hypostructure.CT11.run budgetSpec budgetCapability
          stage).checks_le_polynomial)
        (budgetEnvelope stage)
    exact
      _root_.Hypostructure.PDE.FastTrack.ProfileFamily.canonicalPayloadChecksFor_le_of_component_bounds
        thickeningSpec thickeningCapability peelingSpec peelingCapability
        budgetSpec budgetCapability thickeningBound peelingBound budgetBound
        thickeningChecksLe peelingChecksLe budgetChecksLe previous

/-- Build a row-9 contract from primitive CT capabilities and coarse component
envelopes. -/
noncomputable def ofCapabilityEnvelope
    (thickeningSpec :
      _root_.Hypostructure.CT17.Spec.{_, uTarget, uOffset, uPosition,
        uThickValue}
        (_root_.Hypostructure.PDE.FastTrack.ProfileFamily.ActiveView
          rowEight))
    (thickeningCapability :
      _root_.Hypostructure.CT17.Capability thickeningSpec)
    (peelingSpec :
      _root_.Hypostructure.CT12.Spec.{_, uState, uPeeled, uDemand, uTier}
        (_root_.Hypostructure.CT17.Stage thickeningSpec
          thickeningCapability))
    (peelingCapability :
      _root_.Hypostructure.CT12.Capability peelingSpec)
    (budgetSpec :
      _root_.Hypostructure.CT11.Spec.{_, uCell}
        (_root_.Hypostructure.CT12.Stage peelingSpec peelingCapability))
    (budgetCapability :
      _root_.Hypostructure.CT11.Capability budgetSpec)
    (inputSize :
      _root_.Hypostructure.PDE.FastTrack.ProfileFamily.RowEightStage
          rowEight ->
        Nat)
    (workCoefficient workDegree thickeningBound peelingBound budgetBound : Nat)
    (thickeningEnvelope : forall view,
      thickeningCapability.workCoefficient *
          (thickeningCapability.inputSize view + 1) ^
          thickeningCapability.workDegree <= thickeningBound)
    (peelingEnvelope : forall stage,
      peelingCapability.workCoefficient *
          (peelingCapability.inputSize stage + 1) ^
          peelingCapability.workDegree <= peelingBound)
    (budgetEnvelope : forall stage,
      budgetCapability.workCoefficient *
          (budgetCapability.inputSize stage + 1) ^
          budgetCapability.workDegree <= budgetBound)
    (envelope : forall previous,
      thickeningBound + peelingBound + budgetBound <=
        workCoefficient * (inputSize previous + 1) ^ workDegree) :
    ProfileFamilyContract rowEight where
  thickeningSpec := thickeningSpec
  thickeningCapability := thickeningCapability
  peelingSpec := peelingSpec
  peelingCapability := peelingCapability
  budgetSpec := budgetSpec
  budgetCapability := budgetCapability
  inputSize := inputSize
  workCoefficient := workCoefficient
  workDegree := workDegree
  workBound := fun previous =>
    Nat.le_trans
      (canonicalPayloadChecksFor_le_capability_envelope
        thickeningSpec thickeningCapability peelingSpec peelingCapability
        budgetSpec budgetCapability thickeningBound peelingBound budgetBound
        thickeningEnvelope peelingEnvelope budgetEnvelope previous)
      (envelope previous)

noncomputable def ofCapabilityCanonicalEnvelope
    (thickeningSpec :
      _root_.Hypostructure.CT17.Spec.{_, uTarget, uOffset, uPosition,
        uThickValue}
        (_root_.Hypostructure.PDE.FastTrack.ProfileFamily.ActiveView
          rowEight))
    (thickeningCapability :
      _root_.Hypostructure.CT17.Capability thickeningSpec)
    (peelingSpec :
      _root_.Hypostructure.CT12.Spec.{_, uState, uPeeled, uDemand, uTier}
        (_root_.Hypostructure.CT17.Stage thickeningSpec
          thickeningCapability))
    (peelingCapability :
      _root_.Hypostructure.CT12.Capability peelingSpec)
    (budgetSpec :
      _root_.Hypostructure.CT11.Spec.{_, uCell}
        (_root_.Hypostructure.CT12.Stage peelingSpec peelingCapability))
    (budgetCapability :
      _root_.Hypostructure.CT11.Capability budgetSpec) :
    ProfileFamilyContract rowEight where
  thickeningSpec := thickeningSpec
  thickeningCapability := thickeningCapability
  peelingSpec := peelingSpec
  peelingCapability := peelingCapability
  budgetSpec := budgetSpec
  budgetCapability := budgetCapability
  inputSize :=
    _root_.Hypostructure.PDE.FastTrack.ProfileFamily.canonicalPayloadChecksFor
      thickeningSpec thickeningCapability peelingSpec peelingCapability
      budgetSpec budgetCapability
  workCoefficient := 1
  workDegree := 1
  workBound := by
    intro previous
    simp

noncomputable def workEnvelope (contract : ProfileFamilyContract rowEight) :
    Core.Contract.WorkEnvelope
      (_root_.Hypostructure.PDE.FastTrack.ProfileFamily.RowEightStage
        rowEight) where
  size := contract.inputSize
  checks :=
    _root_.Hypostructure.PDE.FastTrack.ProfileFamily.canonicalPayloadChecksFor
      contract.thickeningSpec contract.thickeningCapability
      contract.peelingSpec contract.peelingCapability
      contract.budgetSpec contract.budgetCapability
  coefficient := contract.workCoefficient
  degree := contract.workDegree
  bounded := contract.workBound

noncomputable def toProfile (contract : ProfileFamilyContract rowEight) :
    _root_.Hypostructure.PDE.FastTrack.ProfileFamily.Profile rowEight where
  thickeningSpec := contract.thickeningSpec
  thickeningCapability := contract.thickeningCapability
  peelingSpec := contract.peelingSpec
  peelingCapability := contract.peelingCapability
  budgetSpec := contract.budgetSpec
  budgetCapability := contract.budgetCapability
  inputSize := contract.inputSize
  payloadChecks := contract.workEnvelope.checks
  payloadChecks_active := by
    intro previous active
    exact _root_.Hypostructure.PDE.FastTrack.ProfileFamily.canonicalPayloadChecksFor_active
      contract.thickeningSpec contract.thickeningCapability
      contract.peelingSpec contract.peelingCapability
      contract.budgetSpec contract.budgetCapability previous active
  workCoefficient := contract.workEnvelope.coefficient
  workDegree := contract.workEnvelope.degree
  workBound := contract.workEnvelope.bounded

noncomputable def run (contract : ProfileFamilyContract rowEight)
    (previous :
      _root_.Hypostructure.PDE.FastTrack.ProfileFamily.RowEightStage
        rowEight) :
    Counted
      (_root_.Hypostructure.PDE.FastTrack.ProfileFamily.Stage
        contract.toProfile) :=
  _root_.Hypostructure.PDE.FastTrack.ProfileFamily.run contract.toProfile
    previous

@[simp] theorem run_previous (contract : ProfileFamilyContract rowEight)
    (previous :
      _root_.Hypostructure.PDE.FastTrack.ProfileFamily.RowEightStage
        rowEight) :
    (contract.run previous).value.previous = previous :=
  _root_.Hypostructure.PDE.FastTrack.ProfileFamily.run_previous
    contract.toProfile previous

theorem run_checks_of_active (contract : ProfileFamilyContract rowEight)
    (previous :
      _root_.Hypostructure.PDE.FastTrack.ProfileFamily.RowEightStage
        rowEight)
    (active :
      (_root_.Hypostructure.PDE.FastTrack.ExactResponseCoverage.SuccessorFocus
        rowEight).Active previous) :
    (contract.run previous).checks =
      (_root_.Hypostructure.PDE.FastTrack.ExactResponseCoverage.SuccessorFocus
        rowEight).selectionBudget.checks previous +
        (_root_.Hypostructure.PDE.FastTrack.ProfileFamily.generateActiveCounted
          contract.toProfile
          (Residual.Focus.ActiveView.of previous active)).checks :=
  _root_.Hypostructure.PDE.FastTrack.ProfileFamily.run_checks_of_active
    contract.toProfile previous active

theorem run_checks_of_inactive (contract : ProfileFamilyContract rowEight)
    (previous :
      _root_.Hypostructure.PDE.FastTrack.ProfileFamily.RowEightStage
        rowEight)
    (inactive : Not
      ((_root_.Hypostructure.PDE.FastTrack.ExactResponseCoverage.SuccessorFocus
        rowEight).Active previous)) :
    (contract.run previous).checks =
      (_root_.Hypostructure.PDE.FastTrack.ExactResponseCoverage.SuccessorFocus
        rowEight).selectionBudget.checks previous :=
  _root_.Hypostructure.PDE.FastTrack.ProfileFamily.run_checks_of_inactive
    contract.toProfile previous inactive

theorem run_checks_bounded (contract : ProfileFamilyContract rowEight)
    (previous :
      _root_.Hypostructure.PDE.FastTrack.ProfileFamily.RowEightStage
        rowEight) :
    (contract.run previous).checks <=
      ((_root_.Hypostructure.PDE.FastTrack.ExactResponseCoverage.SuccessorFocus
        rowEight).selectionBudget.add
        (_root_.Hypostructure.PDE.FastTrack.ProfileFamily.payloadBudget
          contract.toProfile)).coefficient *
      (((_root_.Hypostructure.PDE.FastTrack.ExactResponseCoverage.SuccessorFocus
        rowEight).selectionBudget.add
        (_root_.Hypostructure.PDE.FastTrack.ProfileFamily.payloadBudget
          contract.toProfile)).size previous + 1) ^
      ((_root_.Hypostructure.PDE.FastTrack.ExactResponseCoverage.SuccessorFocus
        rowEight).selectionBudget.add
        (_root_.Hypostructure.PDE.FastTrack.ProfileFamily.payloadBudget
          contract.toProfile)).degree :=
  _root_.Hypostructure.PDE.FastTrack.ProfileFamily.run_checks_bounded
    contract.toProfile previous

end ProfileFamilyContract

variable {rowEight : ExactResponseCoverage.Profile rowSeven}

/-- Minimal PDE contract for row-10 SCRC/boundary repair.

The application registers CT10, CT11, CT14, and CT1 capabilities plus
component work envelopes.  The rigid/cost classification, deficit
localization, capacity aggregation, target split, focused routing, successor
ledger, and work composition are derived by the framework. -/
structure BoundaryRepairContract
    (rowNine :
      _root_.Hypostructure.PDE.FastTrack.ProfileFamily.Profile rowEight) where
  classificationSpec :
    _root_.Hypostructure.CT10.Spec.{_, uDatum, uClass, uPromotion}
      (_root_.Hypostructure.PDE.FastTrack.BoundaryRepair.ActiveView rowNine)
  classificationCapability :
    _root_.Hypostructure.CT10.Capability classificationSpec
  budgetSpec :
    _root_.Hypostructure.CT11.Spec.{_, uCell10}
      (_root_.Hypostructure.CT10.Stage classificationSpec
        classificationCapability)
  budgetCapability :
    _root_.Hypostructure.CT11.Capability budgetSpec
  capacitySpec :
    _root_.Hypostructure.CT14.Spec.{_, uMember10, uLabel10}
      (_root_.Hypostructure.CT11.Stage budgetSpec budgetCapability)
  capacityCapability :
    _root_.Hypostructure.CT14.Capability capacitySpec
  targetSpec :
    _root_.Hypostructure.CT1.Spec.{_, uCandidate10}
      (_root_.Hypostructure.CT14.Stage capacitySpec capacityCapability)
  targetCapability :
    _root_.Hypostructure.CT1.Capability targetSpec
  inputSize :
    _root_.Hypostructure.PDE.FastTrack.BoundaryRepair.RowNineStage rowNine ->
      Nat
  workCoefficient : Nat
  workDegree : Nat
  workBound : forall previous,
    _root_.Hypostructure.PDE.FastTrack.BoundaryRepair.canonicalPayloadChecksFor
      classificationSpec classificationCapability budgetSpec budgetCapability
      capacitySpec capacityCapability targetSpec targetCapability previous <=
        workCoefficient * (inputSize previous + 1) ^ workDegree

namespace BoundaryRepairContract

variable {rowEight : ExactResponseCoverage.Profile rowSeven}
variable {rowNine :
  _root_.Hypostructure.PDE.FastTrack.ProfileFamily.Profile rowEight}

theorem canonicalPayloadChecksFor_le_capability_envelope
    (classificationSpec :
      _root_.Hypostructure.CT10.Spec.{_, uDatum, uClass, uPromotion}
        (_root_.Hypostructure.PDE.FastTrack.BoundaryRepair.ActiveView
          rowNine))
    (classificationCapability :
      _root_.Hypostructure.CT10.Capability classificationSpec)
    (budgetSpec :
      _root_.Hypostructure.CT11.Spec.{_, uCell10}
        (_root_.Hypostructure.CT10.Stage classificationSpec
          classificationCapability))
    (budgetCapability :
      _root_.Hypostructure.CT11.Capability budgetSpec)
    (capacitySpec :
      _root_.Hypostructure.CT14.Spec.{_, uMember10, uLabel10}
        (_root_.Hypostructure.CT11.Stage budgetSpec budgetCapability))
    (capacityCapability :
      _root_.Hypostructure.CT14.Capability capacitySpec)
    (targetSpec :
      _root_.Hypostructure.CT1.Spec.{_, uCandidate10}
        (_root_.Hypostructure.CT14.Stage capacitySpec capacityCapability))
    (targetCapability :
      _root_.Hypostructure.CT1.Capability targetSpec)
    (classificationBound budgetBound capacityBound targetBound : Nat)
    (classificationEnvelope : forall view,
      classificationCapability.workCoefficient *
          (classificationCapability.inputSize view + 1) ^
          classificationCapability.workDegree <= classificationBound)
    (budgetEnvelope : forall stage,
      budgetCapability.workCoefficient *
          (budgetCapability.inputSize stage + 1) ^
          budgetCapability.workDegree <= budgetBound)
    (capacityEnvelope : forall stage,
      capacityCapability.workCoefficient *
          (capacityCapability.inputSize stage + 1) ^
          capacityCapability.workDegree <= capacityBound)
    (targetEnvelope : forall stage,
      targetCapability.workCoefficient *
          (targetCapability.inputSize stage + 1) ^
          targetCapability.workDegree <= targetBound)
    (previous :
      _root_.Hypostructure.PDE.FastTrack.BoundaryRepair.RowNineStage
        rowNine) :
    _root_.Hypostructure.PDE.FastTrack.BoundaryRepair.canonicalPayloadChecksFor
        classificationSpec classificationCapability budgetSpec
        budgetCapability capacitySpec capacityCapability targetSpec
        targetCapability previous <=
      classificationBound + budgetBound + capacityBound + targetBound :=
  by
    let classificationChecksLe : forall view,
        (_root_.Hypostructure.CT10.run classificationCapability
          view).checks <= classificationBound := fun view =>
      Nat.le_trans
        ((_root_.Hypostructure.CT10.run classificationCapability
          view).checks_le_polynomial)
        (classificationEnvelope view)
    let budgetChecksLe : forall stage,
        (_root_.Hypostructure.CT11.run budgetSpec budgetCapability
          stage).checks <= budgetBound := fun stage =>
      Nat.le_trans
        ((_root_.Hypostructure.CT11.run budgetSpec budgetCapability
          stage).checks_le_polynomial)
        (budgetEnvelope stage)
    let capacityChecksLe : forall stage,
        (_root_.Hypostructure.CT14.run capacitySpec capacityCapability
          stage).checks <= capacityBound := fun stage =>
      Nat.le_trans
        ((_root_.Hypostructure.CT14.run capacitySpec capacityCapability
          stage).checks_le_polynomial)
        (capacityEnvelope stage)
    let targetChecksLe : forall stage,
        (_root_.Hypostructure.CT1.run targetSpec targetCapability
          stage).checks <= targetBound := fun stage =>
      Nat.le_trans
        ((_root_.Hypostructure.CT1.run targetSpec targetCapability
          stage).checks_le_polynomial)
        (targetEnvelope stage)
    exact
      _root_.Hypostructure.PDE.FastTrack.BoundaryRepair.canonicalPayloadChecksFor_le_of_component_bounds
        classificationSpec classificationCapability budgetSpec
        budgetCapability capacitySpec capacityCapability targetSpec
        targetCapability classificationBound budgetBound capacityBound
        targetBound classificationChecksLe budgetChecksLe capacityChecksLe
        targetChecksLe previous

noncomputable def ofCapabilityEnvelope
    (classificationSpec :
      _root_.Hypostructure.CT10.Spec.{_, uDatum, uClass, uPromotion}
        (_root_.Hypostructure.PDE.FastTrack.BoundaryRepair.ActiveView
          rowNine))
    (classificationCapability :
      _root_.Hypostructure.CT10.Capability classificationSpec)
    (budgetSpec :
      _root_.Hypostructure.CT11.Spec.{_, uCell10}
        (_root_.Hypostructure.CT10.Stage classificationSpec
          classificationCapability))
    (budgetCapability :
      _root_.Hypostructure.CT11.Capability budgetSpec)
    (capacitySpec :
      _root_.Hypostructure.CT14.Spec.{_, uMember10, uLabel10}
        (_root_.Hypostructure.CT11.Stage budgetSpec budgetCapability))
    (capacityCapability :
      _root_.Hypostructure.CT14.Capability capacitySpec)
    (targetSpec :
      _root_.Hypostructure.CT1.Spec.{_, uCandidate10}
        (_root_.Hypostructure.CT14.Stage capacitySpec capacityCapability))
    (targetCapability :
      _root_.Hypostructure.CT1.Capability targetSpec)
    (inputSize :
      _root_.Hypostructure.PDE.FastTrack.BoundaryRepair.RowNineStage
          rowNine ->
        Nat)
    (workCoefficient workDegree classificationBound budgetBound capacityBound
      targetBound : Nat)
    (classificationEnvelope : forall view,
      classificationCapability.workCoefficient *
          (classificationCapability.inputSize view + 1) ^
          classificationCapability.workDegree <= classificationBound)
    (budgetEnvelope : forall stage,
      budgetCapability.workCoefficient *
          (budgetCapability.inputSize stage + 1) ^
          budgetCapability.workDegree <= budgetBound)
    (capacityEnvelope : forall stage,
      capacityCapability.workCoefficient *
          (capacityCapability.inputSize stage + 1) ^
          capacityCapability.workDegree <= capacityBound)
    (targetEnvelope : forall stage,
      targetCapability.workCoefficient *
          (targetCapability.inputSize stage + 1) ^
          targetCapability.workDegree <= targetBound)
    (envelope : forall previous,
      classificationBound + budgetBound + capacityBound + targetBound <=
        workCoefficient * (inputSize previous + 1) ^ workDegree) :
    BoundaryRepairContract rowNine where
  classificationSpec := classificationSpec
  classificationCapability := classificationCapability
  budgetSpec := budgetSpec
  budgetCapability := budgetCapability
  capacitySpec := capacitySpec
  capacityCapability := capacityCapability
  targetSpec := targetSpec
  targetCapability := targetCapability
  inputSize := inputSize
  workCoefficient := workCoefficient
  workDegree := workDegree
  workBound := fun previous =>
    Nat.le_trans
      (canonicalPayloadChecksFor_le_capability_envelope
        classificationSpec classificationCapability budgetSpec
        budgetCapability capacitySpec capacityCapability targetSpec
        targetCapability classificationBound budgetBound capacityBound
        targetBound classificationEnvelope budgetEnvelope capacityEnvelope
        targetEnvelope previous)
      (envelope previous)

noncomputable def ofCapabilityCanonicalEnvelope
    (classificationSpec :
      _root_.Hypostructure.CT10.Spec.{_, uDatum, uClass, uPromotion}
        (_root_.Hypostructure.PDE.FastTrack.BoundaryRepair.ActiveView
          rowNine))
    (classificationCapability :
      _root_.Hypostructure.CT10.Capability classificationSpec)
    (budgetSpec :
      _root_.Hypostructure.CT11.Spec.{_, uCell10}
        (_root_.Hypostructure.CT10.Stage classificationSpec
          classificationCapability))
    (budgetCapability :
      _root_.Hypostructure.CT11.Capability budgetSpec)
    (capacitySpec :
      _root_.Hypostructure.CT14.Spec.{_, uMember10, uLabel10}
        (_root_.Hypostructure.CT11.Stage budgetSpec budgetCapability))
    (capacityCapability :
      _root_.Hypostructure.CT14.Capability capacitySpec)
    (targetSpec :
      _root_.Hypostructure.CT1.Spec.{_, uCandidate10}
        (_root_.Hypostructure.CT14.Stage capacitySpec capacityCapability))
    (targetCapability :
      _root_.Hypostructure.CT1.Capability targetSpec) :
    BoundaryRepairContract rowNine where
  classificationSpec := classificationSpec
  classificationCapability := classificationCapability
  budgetSpec := budgetSpec
  budgetCapability := budgetCapability
  capacitySpec := capacitySpec
  capacityCapability := capacityCapability
  targetSpec := targetSpec
  targetCapability := targetCapability
  inputSize :=
    _root_.Hypostructure.PDE.FastTrack.BoundaryRepair.canonicalPayloadChecksFor
      classificationSpec classificationCapability budgetSpec budgetCapability
      capacitySpec capacityCapability targetSpec targetCapability
  workCoefficient := 1
  workDegree := 1
  workBound := by
    intro previous
    simp

noncomputable def workEnvelope (contract : BoundaryRepairContract rowNine) :
    Core.Contract.WorkEnvelope
      (_root_.Hypostructure.PDE.FastTrack.BoundaryRepair.RowNineStage
        rowNine) where
  size := contract.inputSize
  checks :=
    _root_.Hypostructure.PDE.FastTrack.BoundaryRepair.canonicalPayloadChecksFor
      contract.classificationSpec contract.classificationCapability
      contract.budgetSpec contract.budgetCapability contract.capacitySpec
      contract.capacityCapability contract.targetSpec contract.targetCapability
  coefficient := contract.workCoefficient
  degree := contract.workDegree
  bounded := contract.workBound

noncomputable def toProfile (contract : BoundaryRepairContract rowNine) :
    _root_.Hypostructure.PDE.FastTrack.BoundaryRepair.Profile rowNine where
  classificationSpec := contract.classificationSpec
  classificationCapability := contract.classificationCapability
  budgetSpec := contract.budgetSpec
  budgetCapability := contract.budgetCapability
  capacitySpec := contract.capacitySpec
  capacityCapability := contract.capacityCapability
  targetSpec := contract.targetSpec
  targetCapability := contract.targetCapability
  inputSize := contract.inputSize
  payloadChecks := contract.workEnvelope.checks
  payloadChecks_active := by
    intro previous active
    exact _root_.Hypostructure.PDE.FastTrack.BoundaryRepair.canonicalPayloadChecksFor_active
      contract.classificationSpec contract.classificationCapability
      contract.budgetSpec contract.budgetCapability contract.capacitySpec
      contract.capacityCapability contract.targetSpec contract.targetCapability
      previous active
  workCoefficient := contract.workEnvelope.coefficient
  workDegree := contract.workEnvelope.degree
  workBound := contract.workEnvelope.bounded

noncomputable def run (contract : BoundaryRepairContract rowNine)
    (previous :
      _root_.Hypostructure.PDE.FastTrack.BoundaryRepair.RowNineStage
        rowNine) :
    Counted
      (_root_.Hypostructure.PDE.FastTrack.BoundaryRepair.Stage
        contract.toProfile) :=
  _root_.Hypostructure.PDE.FastTrack.BoundaryRepair.run contract.toProfile
    previous

@[simp] theorem run_previous (contract : BoundaryRepairContract rowNine)
    (previous :
      _root_.Hypostructure.PDE.FastTrack.BoundaryRepair.RowNineStage
        rowNine) :
    (contract.run previous).value.previous = previous :=
  _root_.Hypostructure.PDE.FastTrack.BoundaryRepair.run_previous
    contract.toProfile previous

theorem run_checks_of_active (contract : BoundaryRepairContract rowNine)
    (previous :
      _root_.Hypostructure.PDE.FastTrack.BoundaryRepair.RowNineStage
        rowNine)
    (active :
      (_root_.Hypostructure.PDE.FastTrack.ProfileFamily.SuccessorFocus
        rowNine).Active previous) :
    (contract.run previous).checks =
      (_root_.Hypostructure.PDE.FastTrack.ProfileFamily.SuccessorFocus
        rowNine).selectionBudget.checks previous +
        (_root_.Hypostructure.PDE.FastTrack.BoundaryRepair.generateActiveCounted
          contract.toProfile
          (Residual.Focus.ActiveView.of previous active)).checks :=
  _root_.Hypostructure.PDE.FastTrack.BoundaryRepair.run_checks_of_active
    contract.toProfile previous active

theorem run_checks_of_inactive (contract : BoundaryRepairContract rowNine)
    (previous :
      _root_.Hypostructure.PDE.FastTrack.BoundaryRepair.RowNineStage
        rowNine)
    (inactive : Not
      ((_root_.Hypostructure.PDE.FastTrack.ProfileFamily.SuccessorFocus
        rowNine).Active previous)) :
    (contract.run previous).checks =
      (_root_.Hypostructure.PDE.FastTrack.ProfileFamily.SuccessorFocus
        rowNine).selectionBudget.checks previous :=
  _root_.Hypostructure.PDE.FastTrack.BoundaryRepair.run_checks_of_inactive
    contract.toProfile previous inactive

theorem run_checks_bounded (contract : BoundaryRepairContract rowNine)
    (previous :
      _root_.Hypostructure.PDE.FastTrack.BoundaryRepair.RowNineStage
        rowNine) :
    (contract.run previous).checks <=
      ((_root_.Hypostructure.PDE.FastTrack.ProfileFamily.SuccessorFocus
        rowNine).selectionBudget.add
        (_root_.Hypostructure.PDE.FastTrack.BoundaryRepair.payloadBudget
          contract.toProfile)).coefficient *
      (((_root_.Hypostructure.PDE.FastTrack.ProfileFamily.SuccessorFocus
        rowNine).selectionBudget.add
        (_root_.Hypostructure.PDE.FastTrack.BoundaryRepair.payloadBudget
          contract.toProfile)).size previous + 1) ^
      ((_root_.Hypostructure.PDE.FastTrack.ProfileFamily.SuccessorFocus
        rowNine).selectionBudget.add
        (_root_.Hypostructure.PDE.FastTrack.BoundaryRepair.payloadBudget
          contract.toProfile)).degree :=
  _root_.Hypostructure.PDE.FastTrack.BoundaryRepair.run_checks_bounded
    contract.toProfile previous

end BoundaryRepairContract

variable {rowNine :
  _root_.Hypostructure.PDE.FastTrack.ProfileFamily.Profile rowEight}
variable {rowTen :
  _root_.Hypostructure.PDE.FastTrack.BoundaryRepair.Profile rowNine}
variable {rowEleven :
  _root_.Hypostructure.PDE.FastTrack.ConservativeCarrier.Profile rowTen}

/-- Minimal PDE contract for row-11 conservative carrier.

The application registers CT5, CT14, and CT11 capabilities plus component work
envelopes for the latter two CTs.  CT5 contributes its framework-owned linear
work budget, while carrier aggregation, capacity accounting, reduced sign
localization, focused routing, successor ledger, and work composition are
derived by the framework. -/
structure ConservativeCarrierContract
    (rowTen :
      _root_.Hypostructure.PDE.FastTrack.BoundaryRepair.Profile rowNine) where
  carrierSpec :
    _root_.Hypostructure.CT5.Spec.{_, uSite, uWitness, uResource}
      (_root_.Hypostructure.PDE.FastTrack.ConservativeCarrier.ActiveView
        rowTen)
  carrierCapability :
    _root_.Hypostructure.CT5.Capability carrierSpec
  capacitySpec :
    _root_.Hypostructure.CT14.Spec.{_, uMember11, uLabel11}
      (_root_.Hypostructure.CT5.Stage carrierSpec carrierCapability)
  capacityCapability :
    _root_.Hypostructure.CT14.Capability capacitySpec
  budgetSpec :
    _root_.Hypostructure.CT11.Spec.{_, uCell11}
      (_root_.Hypostructure.CT14.Stage capacitySpec capacityCapability)
  budgetCapability :
    _root_.Hypostructure.CT11.Capability budgetSpec
  inputSize :
    _root_.Hypostructure.PDE.FastTrack.ConservativeCarrier.RowTenStage
        rowTen ->
      Nat
  workCoefficient : Nat
  workDegree : Nat
  workBound : forall previous,
    _root_.Hypostructure.PDE.FastTrack.ConservativeCarrier.canonicalPayloadChecksFor
      carrierSpec carrierCapability capacitySpec capacityCapability
      budgetSpec budgetCapability previous <=
        workCoefficient * (inputSize previous + 1) ^ workDegree

namespace ConservativeCarrierContract

variable {rowEight : ExactResponseCoverage.Profile rowSeven}
variable {rowNine :
  _root_.Hypostructure.PDE.FastTrack.ProfileFamily.Profile rowEight}
variable {rowTen :
  _root_.Hypostructure.PDE.FastTrack.BoundaryRepair.Profile rowNine}

theorem canonicalPayloadChecksFor_le_capability_envelope
    (carrierSpec :
      _root_.Hypostructure.CT5.Spec.{_, uSite, uWitness, uResource}
        (_root_.Hypostructure.PDE.FastTrack.ConservativeCarrier.ActiveView
          rowTen))
    (carrierCapability :
      _root_.Hypostructure.CT5.Capability carrierSpec)
    (capacitySpec :
      _root_.Hypostructure.CT14.Spec.{_, uMember11, uLabel11}
        (_root_.Hypostructure.CT5.Stage carrierSpec carrierCapability))
    (capacityCapability :
      _root_.Hypostructure.CT14.Capability capacitySpec)
    (budgetSpec :
      _root_.Hypostructure.CT11.Spec.{_, uCell11}
        (_root_.Hypostructure.CT14.Stage capacitySpec capacityCapability))
    (budgetCapability :
      _root_.Hypostructure.CT11.Capability budgetSpec)
    (carrierBound capacityBound budgetBound : Nat)
    (carrierEnvelope : forall view,
      (carrierCapability.linearWorkBudget).coefficient *
          ((carrierCapability.linearWorkBudget).size view + 1) ^
          (carrierCapability.linearWorkBudget).degree <= carrierBound)
    (capacityEnvelope : forall stage,
      capacityCapability.workCoefficient *
          (capacityCapability.inputSize stage + 1) ^
          capacityCapability.workDegree <= capacityBound)
    (budgetEnvelope : forall stage,
      budgetCapability.workCoefficient *
          (budgetCapability.inputSize stage + 1) ^
          budgetCapability.workDegree <= budgetBound)
    (previous :
      _root_.Hypostructure.PDE.FastTrack.ConservativeCarrier.RowTenStage
        rowTen) :
    _root_.Hypostructure.PDE.FastTrack.ConservativeCarrier.canonicalPayloadChecksFor
        carrierSpec carrierCapability capacitySpec capacityCapability
        budgetSpec budgetCapability previous <=
      carrierBound + capacityBound + budgetBound :=
  by
    let carrierChecksLe : forall view,
        (_root_.Hypostructure.CT5.run carrierSpec carrierCapability
          view).checks <= carrierBound := fun view =>
      Nat.le_trans
        ((_root_.Hypostructure.CT5.run carrierSpec carrierCapability
          view).checks_le_polynomial)
        (carrierEnvelope view)
    let capacityChecksLe : forall stage,
        (_root_.Hypostructure.CT14.run capacitySpec capacityCapability
          stage).checks <= capacityBound := fun stage =>
      Nat.le_trans
        ((_root_.Hypostructure.CT14.run capacitySpec capacityCapability
          stage).checks_le_polynomial)
        (capacityEnvelope stage)
    let budgetChecksLe : forall stage,
        (_root_.Hypostructure.CT11.run budgetSpec budgetCapability
          stage).checks <= budgetBound := fun stage =>
      Nat.le_trans
        ((_root_.Hypostructure.CT11.run budgetSpec budgetCapability
          stage).checks_le_polynomial)
        (budgetEnvelope stage)
    exact
      _root_.Hypostructure.PDE.FastTrack.ConservativeCarrier.canonicalPayloadChecksFor_le_of_component_bounds
        carrierSpec carrierCapability capacitySpec capacityCapability
        budgetSpec budgetCapability carrierBound capacityBound budgetBound
        carrierChecksLe capacityChecksLe budgetChecksLe previous

noncomputable def ofCapabilityEnvelope
    (carrierSpec :
      _root_.Hypostructure.CT5.Spec.{_, uSite, uWitness, uResource}
        (_root_.Hypostructure.PDE.FastTrack.ConservativeCarrier.ActiveView
          rowTen))
    (carrierCapability :
      _root_.Hypostructure.CT5.Capability carrierSpec)
    (capacitySpec :
      _root_.Hypostructure.CT14.Spec.{_, uMember11, uLabel11}
        (_root_.Hypostructure.CT5.Stage carrierSpec carrierCapability))
    (capacityCapability :
      _root_.Hypostructure.CT14.Capability capacitySpec)
    (budgetSpec :
      _root_.Hypostructure.CT11.Spec.{_, uCell11}
        (_root_.Hypostructure.CT14.Stage capacitySpec capacityCapability))
    (budgetCapability :
      _root_.Hypostructure.CT11.Capability budgetSpec)
    (inputSize :
      _root_.Hypostructure.PDE.FastTrack.ConservativeCarrier.RowTenStage
          rowTen ->
        Nat)
    (workCoefficient workDegree carrierBound capacityBound budgetBound : Nat)
    (carrierEnvelope : forall view,
      (carrierCapability.linearWorkBudget).coefficient *
          ((carrierCapability.linearWorkBudget).size view + 1) ^
          (carrierCapability.linearWorkBudget).degree <= carrierBound)
    (capacityEnvelope : forall stage,
      capacityCapability.workCoefficient *
          (capacityCapability.inputSize stage + 1) ^
          capacityCapability.workDegree <= capacityBound)
    (budgetEnvelope : forall stage,
      budgetCapability.workCoefficient *
          (budgetCapability.inputSize stage + 1) ^
          budgetCapability.workDegree <= budgetBound)
    (envelope : forall previous,
      carrierBound + capacityBound + budgetBound <=
        workCoefficient * (inputSize previous + 1) ^ workDegree) :
    ConservativeCarrierContract rowTen where
  carrierSpec := carrierSpec
  carrierCapability := carrierCapability
  capacitySpec := capacitySpec
  capacityCapability := capacityCapability
  budgetSpec := budgetSpec
  budgetCapability := budgetCapability
  inputSize := inputSize
  workCoefficient := workCoefficient
  workDegree := workDegree
  workBound := fun previous =>
    Nat.le_trans
      (canonicalPayloadChecksFor_le_capability_envelope
        carrierSpec carrierCapability capacitySpec capacityCapability
        budgetSpec budgetCapability carrierBound capacityBound budgetBound
        carrierEnvelope capacityEnvelope budgetEnvelope previous)
      (envelope previous)

noncomputable def exactCarrierBudget
    (carrierSpec :
      _root_.Hypostructure.CT5.Spec.{_, uSite, uWitness, uResource}
        (_root_.Hypostructure.PDE.FastTrack.ConservativeCarrier.ActiveView
          rowTen))
    (carrierCapability :
      _root_.Hypostructure.CT5.Capability carrierSpec) :
    PolynomialCheckBudget
      (_root_.Hypostructure.PDE.FastTrack.ConservativeCarrier.ActiveView
        rowTen) where
  size := (carrierCapability.linearWorkBudget).size
  checks := fun view =>
    (_root_.Hypostructure.CT5.run carrierSpec carrierCapability view).checks
  coefficient := (carrierCapability.linearWorkBudget).coefficient
  degree := (carrierCapability.linearWorkBudget).degree
  bounded := fun view =>
    (_root_.Hypostructure.CT5.run carrierSpec carrierCapability
      view).checks_le_polynomial

noncomputable def exactCapacityBudget
    (carrierSpec :
      _root_.Hypostructure.CT5.Spec.{_, uSite, uWitness, uResource}
        (_root_.Hypostructure.PDE.FastTrack.ConservativeCarrier.ActiveView
          rowTen))
    (carrierCapability :
      _root_.Hypostructure.CT5.Capability carrierSpec)
    (capacitySpec :
      _root_.Hypostructure.CT14.Spec.{_, uMember11, uLabel11}
        (_root_.Hypostructure.CT5.Stage carrierSpec carrierCapability))
    (capacityCapability :
      _root_.Hypostructure.CT14.Capability capacitySpec) :
    PolynomialCheckBudget
      (_root_.Hypostructure.PDE.FastTrack.ConservativeCarrier.ActiveView
        rowTen) where
  size := fun view =>
    capacityCapability.inputSize
      (_root_.Hypostructure.CT5.run carrierSpec carrierCapability view).stage
  checks := fun view =>
    (_root_.Hypostructure.CT14.run capacitySpec capacityCapability
      (_root_.Hypostructure.CT5.run carrierSpec carrierCapability
        view).stage).checks
  coefficient := capacityCapability.workCoefficient
  degree := capacityCapability.workDegree
  bounded := fun view =>
    (_root_.Hypostructure.CT14.run capacitySpec capacityCapability
      (_root_.Hypostructure.CT5.run carrierSpec carrierCapability
        view).stage).checks_le_polynomial

noncomputable def exactBudgetBudget
    (carrierSpec :
      _root_.Hypostructure.CT5.Spec.{_, uSite, uWitness, uResource}
        (_root_.Hypostructure.PDE.FastTrack.ConservativeCarrier.ActiveView
          rowTen))
    (carrierCapability :
      _root_.Hypostructure.CT5.Capability carrierSpec)
    (capacitySpec :
      _root_.Hypostructure.CT14.Spec.{_, uMember11, uLabel11}
        (_root_.Hypostructure.CT5.Stage carrierSpec carrierCapability))
    (capacityCapability :
      _root_.Hypostructure.CT14.Capability capacitySpec)
    (budgetSpec :
      _root_.Hypostructure.CT11.Spec.{_, uCell11}
        (_root_.Hypostructure.CT14.Stage capacitySpec capacityCapability))
    (budgetCapability :
      _root_.Hypostructure.CT11.Capability budgetSpec) :
    PolynomialCheckBudget
      (_root_.Hypostructure.PDE.FastTrack.ConservativeCarrier.ActiveView
        rowTen) where
  size := fun view =>
    budgetCapability.inputSize
      (_root_.Hypostructure.CT14.run capacitySpec capacityCapability
        (_root_.Hypostructure.CT5.run carrierSpec carrierCapability
          view).stage).stage
  checks := fun view =>
    (_root_.Hypostructure.CT11.run budgetSpec budgetCapability
      (_root_.Hypostructure.CT14.run capacitySpec capacityCapability
        (_root_.Hypostructure.CT5.run carrierSpec carrierCapability
          view).stage).stage).checks
  coefficient := budgetCapability.workCoefficient
  degree := budgetCapability.workDegree
  bounded := fun view =>
    (_root_.Hypostructure.CT11.run budgetSpec budgetCapability
      (_root_.Hypostructure.CT14.run capacitySpec capacityCapability
        (_root_.Hypostructure.CT5.run carrierSpec carrierCapability
          view).stage).stage).checks_le_polynomial

noncomputable def activePayloadBudget
    (carrierSpec :
      _root_.Hypostructure.CT5.Spec.{_, uSite, uWitness, uResource}
        (_root_.Hypostructure.PDE.FastTrack.ConservativeCarrier.ActiveView
          rowTen))
    (carrierCapability :
      _root_.Hypostructure.CT5.Capability carrierSpec)
    (capacitySpec :
      _root_.Hypostructure.CT14.Spec.{_, uMember11, uLabel11}
        (_root_.Hypostructure.CT5.Stage carrierSpec carrierCapability))
    (capacityCapability :
      _root_.Hypostructure.CT14.Capability capacitySpec)
    (budgetSpec :
      _root_.Hypostructure.CT11.Spec.{_, uCell11}
        (_root_.Hypostructure.CT14.Stage capacitySpec capacityCapability))
    (budgetCapability :
      _root_.Hypostructure.CT11.Capability budgetSpec) :
    PolynomialCheckBudget
      (_root_.Hypostructure.PDE.FastTrack.ConservativeCarrier.ActiveView
        rowTen) :=
  (exactCarrierBudget carrierSpec carrierCapability).add
    ((exactCapacityBudget carrierSpec carrierCapability capacitySpec
      capacityCapability).add
      (exactBudgetBudget carrierSpec carrierCapability capacitySpec
        capacityCapability budgetSpec budgetCapability))

noncomputable def payloadBudgetFromCapabilities
    (carrierSpec :
      _root_.Hypostructure.CT5.Spec.{_, uSite, uWitness, uResource}
        (_root_.Hypostructure.PDE.FastTrack.ConservativeCarrier.ActiveView
          rowTen))
    (carrierCapability :
      _root_.Hypostructure.CT5.Capability carrierSpec)
    (capacitySpec :
      _root_.Hypostructure.CT14.Spec.{_, uMember11, uLabel11}
        (_root_.Hypostructure.CT5.Stage carrierSpec carrierCapability))
    (capacityCapability :
      _root_.Hypostructure.CT14.Capability capacitySpec)
    (budgetSpec :
      _root_.Hypostructure.CT11.Spec.{_, uCell11}
        (_root_.Hypostructure.CT14.Stage capacitySpec capacityCapability))
    (budgetCapability :
      _root_.Hypostructure.CT11.Capability budgetSpec) :
    PolynomialCheckBudget
      (_root_.Hypostructure.PDE.FastTrack.ConservativeCarrier.RowTenStage
        rowTen) :=
  by
    classical
    let activeBudget :=
      activePayloadBudget carrierSpec carrierCapability capacitySpec
        capacityCapability budgetSpec budgetCapability
    exact {
      size := fun previous =>
        if active :
            (_root_.Hypostructure.PDE.FastTrack.BoundaryRepair.SuccessorFocus
              rowTen).Active previous then
          activeBudget.size (Residual.Focus.ActiveView.of previous active)
        else
          0
      checks := fun previous =>
        if active :
            (_root_.Hypostructure.PDE.FastTrack.BoundaryRepair.SuccessorFocus
              rowTen).Active previous then
          activeBudget.checks (Residual.Focus.ActiveView.of previous active)
        else
          0
      coefficient := activeBudget.coefficient
      degree := activeBudget.degree
      bounded := by
        intro previous
        by_cases active :
            (_root_.Hypostructure.PDE.FastTrack.BoundaryRepair.SuccessorFocus
              rowTen).Active previous
        · simpa [active]
            using activeBudget.bounded
              (Residual.Focus.ActiveView.of previous active)
        · simp [active]
    }

theorem canonicalPayloadChecksFor_le_payloadBudgetFromCapabilities
    (carrierSpec :
      _root_.Hypostructure.CT5.Spec.{_, uSite, uWitness, uResource}
        (_root_.Hypostructure.PDE.FastTrack.ConservativeCarrier.ActiveView
          rowTen))
    (carrierCapability :
      _root_.Hypostructure.CT5.Capability carrierSpec)
    (capacitySpec :
      _root_.Hypostructure.CT14.Spec.{_, uMember11, uLabel11}
        (_root_.Hypostructure.CT5.Stage carrierSpec carrierCapability))
    (capacityCapability :
      _root_.Hypostructure.CT14.Capability capacitySpec)
    (budgetSpec :
      _root_.Hypostructure.CT11.Spec.{_, uCell11}
        (_root_.Hypostructure.CT14.Stage capacitySpec capacityCapability))
    (budgetCapability :
      _root_.Hypostructure.CT11.Capability budgetSpec)
    (previous :
      _root_.Hypostructure.PDE.FastTrack.ConservativeCarrier.RowTenStage
        rowTen) :
    _root_.Hypostructure.PDE.FastTrack.ConservativeCarrier.canonicalPayloadChecksFor
        carrierSpec carrierCapability capacitySpec capacityCapability
        budgetSpec budgetCapability previous <=
      (payloadBudgetFromCapabilities carrierSpec carrierCapability
        capacitySpec capacityCapability budgetSpec budgetCapability).checks
        previous :=
  by
    classical
    by_cases active :
        (_root_.Hypostructure.PDE.FastTrack.BoundaryRepair.SuccessorFocus
      rowTen).Active previous
    · rw [_root_.Hypostructure.PDE.FastTrack.ConservativeCarrier.canonicalPayloadChecksFor_active
        carrierSpec carrierCapability capacitySpec capacityCapability
        budgetSpec budgetCapability previous active]
      unfold payloadBudgetFromCapabilities activePayloadBudget
      simp [PolynomialCheckBudget.add, exactCarrierBudget,
        exactCapacityBudget, exactBudgetBudget, active, Nat.add_assoc]
    · simp [_root_.Hypostructure.PDE.FastTrack.ConservativeCarrier.canonicalPayloadChecksFor,
        active]

noncomputable def ofCapabilityCanonicalEnvelope
    (carrierSpec :
      _root_.Hypostructure.CT5.Spec.{_, uSite, uWitness, uResource}
        (_root_.Hypostructure.PDE.FastTrack.ConservativeCarrier.ActiveView
          rowTen))
    (carrierCapability :
      _root_.Hypostructure.CT5.Capability carrierSpec)
    (capacitySpec :
      _root_.Hypostructure.CT14.Spec.{_, uMember11, uLabel11}
        (_root_.Hypostructure.CT5.Stage carrierSpec carrierCapability))
    (capacityCapability :
      _root_.Hypostructure.CT14.Capability capacitySpec)
    (budgetSpec :
      _root_.Hypostructure.CT11.Spec.{_, uCell11}
        (_root_.Hypostructure.CT14.Stage capacitySpec capacityCapability))
    (budgetCapability :
      _root_.Hypostructure.CT11.Capability budgetSpec) :
    ConservativeCarrierContract rowTen :=
  let payload :=
    payloadBudgetFromCapabilities carrierSpec carrierCapability capacitySpec
      capacityCapability budgetSpec budgetCapability
  {
    carrierSpec := carrierSpec
    carrierCapability := carrierCapability
    capacitySpec := capacitySpec
    capacityCapability := capacityCapability
    budgetSpec := budgetSpec
    budgetCapability := budgetCapability
    inputSize := payload.size
    workCoefficient := payload.coefficient
    workDegree := payload.degree
    workBound := fun previous =>
      Nat.le_trans
        (canonicalPayloadChecksFor_le_payloadBudgetFromCapabilities
          carrierSpec carrierCapability capacitySpec capacityCapability
          budgetSpec budgetCapability previous)
        (payload.bounded previous)
  }

noncomputable def workEnvelope
    (contract : ConservativeCarrierContract rowTen) :
    Core.Contract.WorkEnvelope
      (_root_.Hypostructure.PDE.FastTrack.ConservativeCarrier.RowTenStage
        rowTen) where
  size := contract.inputSize
  checks :=
    _root_.Hypostructure.PDE.FastTrack.ConservativeCarrier.canonicalPayloadChecksFor
      contract.carrierSpec contract.carrierCapability contract.capacitySpec
      contract.capacityCapability contract.budgetSpec contract.budgetCapability
  coefficient := contract.workCoefficient
  degree := contract.workDegree
  bounded := contract.workBound

noncomputable def toProfile
    (contract : ConservativeCarrierContract rowTen) :
    _root_.Hypostructure.PDE.FastTrack.ConservativeCarrier.Profile
      rowTen where
  carrierSpec := contract.carrierSpec
  carrierCapability := contract.carrierCapability
  capacitySpec := contract.capacitySpec
  capacityCapability := contract.capacityCapability
  budgetSpec := contract.budgetSpec
  budgetCapability := contract.budgetCapability
  inputSize := contract.inputSize
  payloadChecks := contract.workEnvelope.checks
  payloadChecks_active := by
    intro previous active
    exact _root_.Hypostructure.PDE.FastTrack.ConservativeCarrier.canonicalPayloadChecksFor_active
      contract.carrierSpec contract.carrierCapability contract.capacitySpec
      contract.capacityCapability contract.budgetSpec contract.budgetCapability
      previous active
  workCoefficient := contract.workEnvelope.coefficient
  workDegree := contract.workEnvelope.degree
  workBound := contract.workEnvelope.bounded

noncomputable def run (contract : ConservativeCarrierContract rowTen)
    (previous :
      _root_.Hypostructure.PDE.FastTrack.ConservativeCarrier.RowTenStage
        rowTen) :
    Counted
      (_root_.Hypostructure.PDE.FastTrack.ConservativeCarrier.Stage
        contract.toProfile) :=
  _root_.Hypostructure.PDE.FastTrack.ConservativeCarrier.run
    contract.toProfile previous

@[simp] theorem run_previous (contract : ConservativeCarrierContract rowTen)
    (previous :
      _root_.Hypostructure.PDE.FastTrack.ConservativeCarrier.RowTenStage
        rowTen) :
    (contract.run previous).value.previous = previous :=
  _root_.Hypostructure.PDE.FastTrack.ConservativeCarrier.run_previous
    contract.toProfile previous

theorem run_checks_of_active
    (contract : ConservativeCarrierContract rowTen)
    (previous :
      _root_.Hypostructure.PDE.FastTrack.ConservativeCarrier.RowTenStage
        rowTen)
    (active :
      (_root_.Hypostructure.PDE.FastTrack.BoundaryRepair.SuccessorFocus
        rowTen).Active previous) :
    (contract.run previous).checks =
      (_root_.Hypostructure.PDE.FastTrack.BoundaryRepair.SuccessorFocus
        rowTen).selectionBudget.checks previous +
        (_root_.Hypostructure.PDE.FastTrack.ConservativeCarrier.generateActiveCounted
          contract.toProfile
          (Residual.Focus.ActiveView.of previous active)).checks :=
  _root_.Hypostructure.PDE.FastTrack.ConservativeCarrier.run_checks_of_active
    contract.toProfile previous active

theorem run_checks_of_inactive
    (contract : ConservativeCarrierContract rowTen)
    (previous :
      _root_.Hypostructure.PDE.FastTrack.ConservativeCarrier.RowTenStage
        rowTen)
    (inactive : Not
      ((_root_.Hypostructure.PDE.FastTrack.BoundaryRepair.SuccessorFocus
        rowTen).Active previous)) :
    (contract.run previous).checks =
      (_root_.Hypostructure.PDE.FastTrack.BoundaryRepair.SuccessorFocus
        rowTen).selectionBudget.checks previous :=
  _root_.Hypostructure.PDE.FastTrack.ConservativeCarrier.run_checks_of_inactive
    contract.toProfile previous inactive

theorem run_checks_bounded
    (contract : ConservativeCarrierContract rowTen)
    (previous :
      _root_.Hypostructure.PDE.FastTrack.ConservativeCarrier.RowTenStage
        rowTen) :
    (contract.run previous).checks <=
      ((_root_.Hypostructure.PDE.FastTrack.BoundaryRepair.SuccessorFocus
        rowTen).selectionBudget.add
        (_root_.Hypostructure.PDE.FastTrack.ConservativeCarrier.payloadBudget
          contract.toProfile)).coefficient *
      (((_root_.Hypostructure.PDE.FastTrack.BoundaryRepair.SuccessorFocus
        rowTen).selectionBudget.add
        (_root_.Hypostructure.PDE.FastTrack.ConservativeCarrier.payloadBudget
          contract.toProfile)).size previous + 1) ^
      ((_root_.Hypostructure.PDE.FastTrack.BoundaryRepair.SuccessorFocus
        rowTen).selectionBudget.add
        (_root_.Hypostructure.PDE.FastTrack.ConservativeCarrier.payloadBudget
          contract.toProfile)).degree :=
  _root_.Hypostructure.PDE.FastTrack.ConservativeCarrier.run_checks_bounded
    contract.toProfile previous

end ConservativeCarrierContract

/-- Minimal PDE contract for row-12 elliptic constraint tail. -/
structure EllipticConstraintTailContract
    (rowEleven :
      _root_.Hypostructure.PDE.FastTrack.ConservativeCarrier.Profile
        rowTen) where
  responseSpec :
    _root_.Hypostructure.CT3.Spec.{_, uRepresentative12, uContext12,
      uCoordinate12, uValue12, uCandidate12, uRow12}
      (_root_.Hypostructure.PDE.FastTrack.EllipticConstraintTail.ActiveView
        rowEleven)
  responseCapability :
    _root_.Hypostructure.CT3.Capability responseSpec
  dyadicSpec :
    _root_.Hypostructure.CT14.Spec.{_, uMember12, uLabel12}
      (_root_.Hypostructure.CT3.Stage responseSpec responseCapability)
  dyadicCapability :
    _root_.Hypostructure.CT14.Capability dyadicSpec
  gaugeRankSpec :
    _root_.Hypostructure.CT15.Spec.{_, uRankCoordinate12}
      (_root_.Hypostructure.CT14.Stage dyadicSpec dyadicCapability)
  gaugeRankCapability :
    _root_.Hypostructure.CT15.Capability gaugeRankSpec
  fallbackSpec :
    _root_.Hypostructure.CT13.Spec.{_, uPayer12, uObstruction12,
      uResource12}
      (_root_.Hypostructure.CT15.Stage gaugeRankSpec gaugeRankCapability)
  fallbackCapability :
    _root_.Hypostructure.CT13.Capability fallbackSpec
  inputSize :
    _root_.Hypostructure.PDE.FastTrack.EllipticConstraintTail.RowElevenStage
        rowEleven ->
      Nat
  workCoefficient : Nat
  workDegree : Nat
  workBound : forall previous,
    _root_.Hypostructure.PDE.FastTrack.EllipticConstraintTail.canonicalPayloadChecksFor
      responseSpec responseCapability dyadicSpec dyadicCapability
      gaugeRankSpec gaugeRankCapability fallbackSpec fallbackCapability
      previous <=
        workCoefficient * (inputSize previous + 1) ^ workDegree

namespace EllipticConstraintTailContract

variable {rowEight : ExactResponseCoverage.Profile rowSeven}
variable {rowNine :
  _root_.Hypostructure.PDE.FastTrack.ProfileFamily.Profile rowEight}
variable {rowTen :
  _root_.Hypostructure.PDE.FastTrack.BoundaryRepair.Profile rowNine}
variable {rowEleven :
  _root_.Hypostructure.PDE.FastTrack.ConservativeCarrier.Profile rowTen}

noncomputable def ofCapabilityCanonicalEnvelope
    (responseSpec :
      _root_.Hypostructure.CT3.Spec.{_, uRepresentative12, uContext12,
        uCoordinate12, uValue12, uCandidate12, uRow12}
        (_root_.Hypostructure.PDE.FastTrack.EllipticConstraintTail.ActiveView
          rowEleven))
    (responseCapability :
      _root_.Hypostructure.CT3.Capability responseSpec)
    (dyadicSpec :
      _root_.Hypostructure.CT14.Spec.{_, uMember12, uLabel12}
        (_root_.Hypostructure.CT3.Stage responseSpec responseCapability))
    (dyadicCapability :
      _root_.Hypostructure.CT14.Capability dyadicSpec)
    (gaugeRankSpec :
      _root_.Hypostructure.CT15.Spec.{_, uRankCoordinate12}
        (_root_.Hypostructure.CT14.Stage dyadicSpec dyadicCapability))
    (gaugeRankCapability :
      _root_.Hypostructure.CT15.Capability gaugeRankSpec)
    (fallbackSpec :
      _root_.Hypostructure.CT13.Spec.{_, uPayer12, uObstruction12,
        uResource12}
        (_root_.Hypostructure.CT15.Stage gaugeRankSpec gaugeRankCapability))
    (fallbackCapability :
      _root_.Hypostructure.CT13.Capability fallbackSpec) :
    EllipticConstraintTailContract rowEleven where
  responseSpec := responseSpec
  responseCapability := responseCapability
  dyadicSpec := dyadicSpec
  dyadicCapability := dyadicCapability
  gaugeRankSpec := gaugeRankSpec
  gaugeRankCapability := gaugeRankCapability
  fallbackSpec := fallbackSpec
  fallbackCapability := fallbackCapability
  inputSize :=
    _root_.Hypostructure.PDE.FastTrack.EllipticConstraintTail.canonicalPayloadChecksFor
      responseSpec responseCapability dyadicSpec dyadicCapability
      gaugeRankSpec gaugeRankCapability fallbackSpec fallbackCapability
  workCoefficient := 1
  workDegree := 1
  workBound := by
    intro previous
    simp

noncomputable def workEnvelope
    (contract : EllipticConstraintTailContract rowEleven) :
    Core.Contract.WorkEnvelope
      (_root_.Hypostructure.PDE.FastTrack.EllipticConstraintTail.RowElevenStage
        rowEleven) where
  size := contract.inputSize
  checks :=
    _root_.Hypostructure.PDE.FastTrack.EllipticConstraintTail.canonicalPayloadChecksFor
      contract.responseSpec contract.responseCapability contract.dyadicSpec
      contract.dyadicCapability contract.gaugeRankSpec
      contract.gaugeRankCapability contract.fallbackSpec
      contract.fallbackCapability
  coefficient := contract.workCoefficient
  degree := contract.workDegree
  bounded := contract.workBound

noncomputable def toProfile
    (contract : EllipticConstraintTailContract rowEleven) :
    _root_.Hypostructure.PDE.FastTrack.EllipticConstraintTail.Profile
      rowEleven where
  responseSpec := contract.responseSpec
  responseCapability := contract.responseCapability
  dyadicSpec := contract.dyadicSpec
  dyadicCapability := contract.dyadicCapability
  gaugeRankSpec := contract.gaugeRankSpec
  gaugeRankCapability := contract.gaugeRankCapability
  fallbackSpec := contract.fallbackSpec
  fallbackCapability := contract.fallbackCapability
  inputSize := contract.inputSize
  payloadChecks := contract.workEnvelope.checks
  payloadChecks_active := by
    intro previous active
    exact _root_.Hypostructure.PDE.FastTrack.EllipticConstraintTail.canonicalPayloadChecksFor_active
      contract.responseSpec contract.responseCapability contract.dyadicSpec
      contract.dyadicCapability contract.gaugeRankSpec
      contract.gaugeRankCapability contract.fallbackSpec
      contract.fallbackCapability previous active
  workCoefficient := contract.workEnvelope.coefficient
  workDegree := contract.workEnvelope.degree
  workBound := contract.workEnvelope.bounded

noncomputable def run (contract : EllipticConstraintTailContract rowEleven)
    (previous :
      _root_.Hypostructure.PDE.FastTrack.EllipticConstraintTail.RowElevenStage
        rowEleven) :
    Counted
      (_root_.Hypostructure.PDE.FastTrack.EllipticConstraintTail.Stage
        contract.toProfile) :=
  _root_.Hypostructure.PDE.FastTrack.EllipticConstraintTail.run
    contract.toProfile previous

@[simp] theorem run_previous (contract : EllipticConstraintTailContract rowEleven)
    (previous :
      _root_.Hypostructure.PDE.FastTrack.EllipticConstraintTail.RowElevenStage
        rowEleven) :
    (contract.run previous).value.previous = previous :=
  _root_.Hypostructure.PDE.FastTrack.EllipticConstraintTail.run_previous
    contract.toProfile previous

theorem run_checks_of_active
    (contract : EllipticConstraintTailContract rowEleven)
    (previous :
      _root_.Hypostructure.PDE.FastTrack.EllipticConstraintTail.RowElevenStage
        rowEleven)
    (active :
      (_root_.Hypostructure.PDE.FastTrack.ConservativeCarrier.SuccessorFocus
        rowEleven).Active previous) :
    (contract.run previous).checks =
      (_root_.Hypostructure.PDE.FastTrack.ConservativeCarrier.SuccessorFocus
        rowEleven).selectionBudget.checks previous +
        (_root_.Hypostructure.PDE.FastTrack.EllipticConstraintTail.generateActiveCounted
          contract.toProfile
          (Residual.Focus.ActiveView.of previous active)).checks :=
  _root_.Hypostructure.PDE.FastTrack.EllipticConstraintTail.run_checks_of_active
    contract.toProfile previous active

theorem run_checks_of_inactive
    (contract : EllipticConstraintTailContract rowEleven)
    (previous :
      _root_.Hypostructure.PDE.FastTrack.EllipticConstraintTail.RowElevenStage
        rowEleven)
    (inactive : Not
      ((_root_.Hypostructure.PDE.FastTrack.ConservativeCarrier.SuccessorFocus
        rowEleven).Active previous)) :
    (contract.run previous).checks =
      (_root_.Hypostructure.PDE.FastTrack.ConservativeCarrier.SuccessorFocus
        rowEleven).selectionBudget.checks previous :=
  _root_.Hypostructure.PDE.FastTrack.EllipticConstraintTail.run_checks_of_inactive
    contract.toProfile previous inactive

theorem run_checks_bounded
    (contract : EllipticConstraintTailContract rowEleven)
    (previous :
      _root_.Hypostructure.PDE.FastTrack.EllipticConstraintTail.RowElevenStage
        rowEleven) :
    (contract.run previous).checks <=
      ((_root_.Hypostructure.PDE.FastTrack.ConservativeCarrier.SuccessorFocus
        rowEleven).selectionBudget.add
        (_root_.Hypostructure.PDE.FastTrack.EllipticConstraintTail.payloadBudget
          contract.toProfile)).coefficient *
      (((_root_.Hypostructure.PDE.FastTrack.ConservativeCarrier.SuccessorFocus
        rowEleven).selectionBudget.add
        (_root_.Hypostructure.PDE.FastTrack.EllipticConstraintTail.payloadBudget
          contract.toProfile)).size previous + 1) ^
      ((_root_.Hypostructure.PDE.FastTrack.ConservativeCarrier.SuccessorFocus
        rowEleven).selectionBudget.add
        (_root_.Hypostructure.PDE.FastTrack.EllipticConstraintTail.payloadBudget
          contract.toProfile)).degree :=
  _root_.Hypostructure.PDE.FastTrack.EllipticConstraintTail.run_checks_bounded
    contract.toProfile previous

end EllipticConstraintTailContract

end Hypostructure.PDE.Contract
