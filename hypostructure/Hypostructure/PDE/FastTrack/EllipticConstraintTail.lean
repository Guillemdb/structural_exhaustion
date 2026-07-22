import Hypostructure.CT3.Automation
import Hypostructure.CT13.Automation
import Hypostructure.CT14.Automation
import Hypostructure.CT15.Automation
import Hypostructure.PDE.FastTrack.ConservativeCarrier

/-!
# PDE fast-track row 12: elliptic constraint tail

Row 12 consumes the row-11 successor residual.  On that focused predecessor the
framework runs CT3 for exact response compression, CT14 for the descended
dyadic/tail mass profile, CT15 for the target-relative gauge rank, and CT13 for
the fallback resource split.  Applications register only the shared CT
capabilities; CT sequencing, focused routing, ledger extension, and payload
composition are framework-owned.
-/

namespace Hypostructure.PDE.FastTrack.EllipticConstraintTail

open Hypostructure.Core

universe uPrevious uPotential uCurrent
universe uRepresentative uContext uCoordinate uValue uCandidate8 uRow
universe uRepresentative7 uContext7 uCoordinate7 uValue7
universe uTarget uOffset uPosition uThickValue
universe uState uPeeled uDemand uTier uCell9
universe uDatum uClass uPromotion uCell10 uMember10 uLabel10 uCandidate10
universe uSite uWitness uResource11 uMember11 uLabel11 uCell11
universe uRepresentative12 uContext12 uCoordinate12 uValue12 uCandidate12 uRow12
universe uMember12 uLabel12 uRankCoordinate12 uPayer12 uObstruction12 uResource12

variable {Previous : Type uPrevious}
variable {Potential : Type uPotential} {Current : Type uCurrent}
variable [NormedAddCommGroup Potential] [InnerProductSpace Real Potential]
variable [CompleteSpace Potential]
variable [NormedAddCommGroup Current] [InnerProductSpace Real Current]
variable [CompleteSpace Current]

namespace CanonicalCapability

/-- CT3 capability with its work envelope derived from the prescribed local
check bound. -/
def response
    {Previous : Type uPrevious}
    {spec :
      _root_.Hypostructure.CT3.Spec.{uPrevious, uRepresentative12, uContext12,
        uCoordinate12, uValue12, uCandidate12, uRow12} Previous}
    (source : Core.Residual.Query Previous fun _previous => spec.Representative)
    (coordinates : Core.Residual.Query Previous fun _previous =>
      Core.Finite.Enumeration spec.system.Coordinate)
    (candidates : Core.Residual.Query Previous fun _previous =>
      Core.Finite.Enumeration spec.Candidate)
    (rows : Core.Residual.Query Previous fun _previous =>
      Core.Finite.Enumeration spec.Row)
    (valueDecEq : DecidableEq spec.system.Value)
    (admissibleDecidable : (previous : Previous) ->
      (source : spec.Representative) -> (candidate : spec.Candidate) ->
        Decidable (spec.Admissible previous source candidate))
    (smallerDecidable : (previous : Previous) ->
      (source : spec.Representative) -> (candidate : spec.Candidate) ->
        Decidable (spec.StrictlySmaller previous source candidate))
    (candidateCoverage : (previous : Previous) -> (candidate : spec.Candidate) ->
      candidate ∈ (candidates.read previous).values ->
        Core.Response.FiniteTable.SymbolicCoverage spec.system
          (spec.representatives (source.read previous)
            (spec.candidatePiece candidate))
          (Core.Response.FiniteTable.ExactSchedule.ofList
            (coordinates.read previous).values))
    (rowCoverage : (previous : Previous) -> (row : spec.Row) ->
      row ∈ (rows.read previous).values ->
        Core.Response.FiniteTable.SymbolicCoverage spec.system
          (spec.representatives (source.read previous) (spec.rowPiece row))
          (Core.Response.FiniteTable.ExactSchedule.ofList
            (coordinates.read previous).values)) :
    _root_.Hypostructure.CT3.Capability spec where
  source := source
  coordinates := coordinates
  candidates := candidates
  rows := rows
  valueDecEq := valueDecEq
  admissibleDecidable := admissibleDecidable
  smallerDecidable := smallerDecidable
  candidateCoverage := candidateCoverage
  rowCoverage := rowCoverage
  inputSize := fun previous =>
    _root_.Hypostructure.CT3.localCheckBound (coordinates.read previous)
      (candidates.read previous) (rows.read previous)
  workCoefficient := 1
  workDegree := 1
  workBound := by
    intro previous
    simp

/-- CT14 capability with its work envelope derived from the prescribed local
check bound. -/
def dyadic
    {Previous : Type uPrevious}
    {spec :
      _root_.Hypostructure.CT14.Spec.{uPrevious, uMember12, uLabel12} Previous}
    (members : Core.Residual.Query Previous fun previous =>
      Core.Finite.Enumeration (spec.Member previous))
    (labelDecidableEq : (previous : Previous) ->
      DecidableEq (spec.Label previous)) :
    _root_.Hypostructure.CT14.Capability spec where
  members := members
  labelDecidableEq := labelDecidableEq
  inputSize := fun previous =>
    _root_.Hypostructure.CT14.localCheckBound (members.read previous)
  workCoefficient := 1
  workDegree := 1
  workBound := by
    intro previous
    simp

/-- CT15 capability with its work envelope derived from the prescribed local
check bound. -/
def gaugeRank
    {Previous : Type uPrevious}
    {spec :
      _root_.Hypostructure.CT15.Spec.{uPrevious, uRankCoordinate12} Previous}
    (coordinates : Core.Residual.Query Previous fun previous =>
      Core.Finite.Enumeration (spec.Coordinate previous))
    (targetDependentDecidable : (previous : Previous) ->
      (coordinate : spec.Coordinate previous) ->
        Decidable (spec.TargetDependent previous coordinate)) :
    _root_.Hypostructure.CT15.Capability spec where
  coordinates := coordinates
  targetDependentDecidable := targetDependentDecidable
  inputSize := fun previous =>
    _root_.Hypostructure.CT15.localCheckBound (coordinates.read previous)
  workCoefficient := 1
  workDegree := 1
  workBound := by
    intro previous
    simp

/-- CT13 capability with its work envelope derived from the prescribed local
check bound. -/
def fallback
    {Previous : Type uPrevious}
    {spec :
      _root_.Hypostructure.CT13.Spec.{uPrevious, uPayer12, uObstruction12,
        uResource12} Previous}
    (payers : Core.Residual.Query Previous fun previous =>
      Core.Finite.Enumeration (spec.Payer previous))
    (obstructions : Core.Residual.Query Previous fun previous =>
      _root_.Hypostructure.CT13.ObstructionSchedule
        (spec.Obstruction previous))
    (tierTwo : Core.Residual.Query Previous fun previous =>
      (obstruction : spec.Obstruction previous) ->
        Core.Finite.Enumeration (spec.Payer previous))
    (eligibleDecidable : (previous : Previous) ->
      (payer : spec.Payer previous) -> Decidable (spec.Eligible previous payer))
    (resourceDecidableEq : (previous : Previous) ->
      DecidableEq (spec.Resource previous)) :
    _root_.Hypostructure.CT13.Capability spec where
  payers := payers
  obstructions := obstructions
  tierTwo := tierTwo
  eligibleDecidable := eligibleDecidable
  resourceDecidableEq := resourceDecidableEq
  inputSize := fun previous =>
    _root_.Hypostructure.CT13.localCheckBound (payers.read previous)
      (obstructions.read previous) (tierTwo.read previous)
  workCoefficient := 1
  workDegree := 1
  workBound := by
    intro previous
    simp

end CanonicalCapability

variable {focus : Residual.Focus.Profile Previous}
variable {rowFive : DirectedExhaustiveness.Profile Previous focus Potential Current}
variable {rowSix : DefectRouting.Profile rowFive}
variable {rowSeven : CapacityProfile.Profile rowSix}
variable {rowEight : ExactResponseCoverage.Profile rowSeven}
variable {rowNine : ProfileFamily.Profile rowEight}
variable {rowTen : BoundaryRepair.Profile rowNine}

/-- Literal row-11 stage consumed by row 12. -/
abbrev RowElevenStage (rowEleven : ConservativeCarrier.Profile rowTen) :=
  ConservativeCarrier.Stage rowEleven

/-- Exact row-11 successor view selected by the framework. -/
abbrev ActiveView (rowEleven : ConservativeCarrier.Profile rowTen) :=
  Residual.Focus.ActiveView (ConservativeCarrier.SuccessorFocus rowEleven)

/-- Minimal row-12 registration. -/
structure Profile (rowEleven : ConservativeCarrier.Profile rowTen) where
  responseSpec :
    _root_.Hypostructure.CT3.Spec.{_, uRepresentative12, uContext12,
      uCoordinate12, uValue12, uCandidate12, uRow12} (ActiveView rowEleven)
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
    _root_.Hypostructure.CT13.Spec.{_, uPayer12, uObstruction12, uResource12}
      (_root_.Hypostructure.CT15.Stage gaugeRankSpec gaugeRankCapability)
  fallbackCapability :
    _root_.Hypostructure.CT13.Capability fallbackSpec
  inputSize : RowElevenStage rowEleven -> Nat
  payloadChecks : RowElevenStage rowEleven -> Nat
  payloadChecks_active : forall (previous : RowElevenStage rowEleven)
    (active : (ConservativeCarrier.SuccessorFocus rowEleven).Active previous),
    payloadChecks previous =
      let view := Residual.Focus.ActiveView.of previous active
      let response :=
        _root_.Hypostructure.CT3.run responseSpec responseCapability view
      let dyadic :=
        _root_.Hypostructure.CT14.run dyadicSpec dyadicCapability
          response.stage
      let gaugeRank :=
        _root_.Hypostructure.CT15.run gaugeRankSpec gaugeRankCapability
          dyadic.stage
      response.checks + dyadic.checks + gaugeRank.checks +
        (_root_.Hypostructure.CT13.run fallbackSpec fallbackCapability
          gaugeRank.stage).checks
  workCoefficient : Nat
  workDegree : Nat
  workBound : forall previous,
    payloadChecks previous <=
      workCoefficient * (inputSize previous + 1) ^ workDegree

variable {rowEleven : ConservativeCarrier.Profile rowTen}

/-- Canonical row-12 payload accounting. -/
noncomputable def canonicalPayloadChecksFor
    (responseSpec :
      _root_.Hypostructure.CT3.Spec.{_, uRepresentative12, uContext12,
        uCoordinate12, uValue12, uCandidate12, uRow12} (ActiveView rowEleven))
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
      _root_.Hypostructure.CT13.Spec.{_, uPayer12, uObstruction12, uResource12}
        (_root_.Hypostructure.CT15.Stage gaugeRankSpec gaugeRankCapability))
    (fallbackCapability :
      _root_.Hypostructure.CT13.Capability fallbackSpec)
    (previous : RowElevenStage rowEleven) : Nat := by
  classical
  exact
    if active : (ConservativeCarrier.SuccessorFocus rowEleven).Active previous then
      let view := Residual.Focus.ActiveView.of previous active
      let response :=
        _root_.Hypostructure.CT3.run responseSpec responseCapability view
      let dyadic :=
        _root_.Hypostructure.CT14.run dyadicSpec dyadicCapability
          response.stage
      let gaugeRank :=
        _root_.Hypostructure.CT15.run gaugeRankSpec gaugeRankCapability
          dyadic.stage
      response.checks + dyadic.checks + gaugeRank.checks +
        (_root_.Hypostructure.CT13.run fallbackSpec fallbackCapability
          gaugeRank.stage).checks
    else
      0

theorem canonicalPayloadChecksFor_active
    (responseSpec :
      _root_.Hypostructure.CT3.Spec.{_, uRepresentative12, uContext12,
        uCoordinate12, uValue12, uCandidate12, uRow12} (ActiveView rowEleven))
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
      _root_.Hypostructure.CT13.Spec.{_, uPayer12, uObstruction12, uResource12}
        (_root_.Hypostructure.CT15.Stage gaugeRankSpec gaugeRankCapability))
    (fallbackCapability :
      _root_.Hypostructure.CT13.Capability fallbackSpec)
    (previous : RowElevenStage rowEleven)
    (active : (ConservativeCarrier.SuccessorFocus rowEleven).Active previous) :
    canonicalPayloadChecksFor responseSpec responseCapability dyadicSpec
        dyadicCapability gaugeRankSpec gaugeRankCapability fallbackSpec
        fallbackCapability previous =
      let view := Residual.Focus.ActiveView.of previous active
      let response :=
        _root_.Hypostructure.CT3.run responseSpec responseCapability view
      let dyadic :=
        _root_.Hypostructure.CT14.run dyadicSpec dyadicCapability
          response.stage
      let gaugeRank :=
        _root_.Hypostructure.CT15.run gaugeRankSpec gaugeRankCapability
          dyadic.stage
      response.checks + dyadic.checks + gaugeRank.checks +
        (_root_.Hypostructure.CT13.run fallbackSpec fallbackCapability
          gaugeRank.stage).checks := by
  unfold canonicalPayloadChecksFor
  rw [dif_pos active]

theorem canonicalPayloadChecksFor_le_of_component_bounds
    (responseSpec :
      _root_.Hypostructure.CT3.Spec.{_, uRepresentative12, uContext12,
        uCoordinate12, uValue12, uCandidate12, uRow12} (ActiveView rowEleven))
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
      _root_.Hypostructure.CT13.Spec.{_, uPayer12, uObstruction12, uResource12}
        (_root_.Hypostructure.CT15.Stage gaugeRankSpec gaugeRankCapability))
    (fallbackCapability :
      _root_.Hypostructure.CT13.Capability fallbackSpec)
    (responseBound dyadicBound gaugeRankBound fallbackBound : Nat)
    (responseChecks :
      forall view,
        (_root_.Hypostructure.CT3.run responseSpec responseCapability
          view).checks <= responseBound)
    (dyadicChecks :
      forall stage,
        (_root_.Hypostructure.CT14.run dyadicSpec dyadicCapability
          stage).checks <= dyadicBound)
    (gaugeRankChecks :
      forall stage,
        (_root_.Hypostructure.CT15.run gaugeRankSpec gaugeRankCapability
          stage).checks <= gaugeRankBound)
    (fallbackChecks :
      forall stage,
        (_root_.Hypostructure.CT13.run fallbackSpec fallbackCapability
          stage).checks <= fallbackBound)
    (previous : RowElevenStage rowEleven) :
    canonicalPayloadChecksFor responseSpec responseCapability dyadicSpec
        dyadicCapability gaugeRankSpec gaugeRankCapability fallbackSpec
        fallbackCapability previous <=
      responseBound + dyadicBound + gaugeRankBound + fallbackBound := by
  classical
  by_cases active : (ConservativeCarrier.SuccessorFocus rowEleven).Active previous
  · rw [canonicalPayloadChecksFor_active responseSpec responseCapability
      dyadicSpec dyadicCapability gaugeRankSpec gaugeRankCapability fallbackSpec
      fallbackCapability previous active]
    let view := Residual.Focus.ActiveView.of previous active
    let response :=
      _root_.Hypostructure.CT3.run responseSpec responseCapability view
    let dyadic :=
      _root_.Hypostructure.CT14.run dyadicSpec dyadicCapability response.stage
    let gaugeRank :=
      _root_.Hypostructure.CT15.run gaugeRankSpec gaugeRankCapability
        dyadic.stage
    exact Nat.add_le_add
      (Nat.add_le_add
        (Nat.add_le_add (responseChecks view) (dyadicChecks response.stage))
        (gaugeRankChecks dyadic.stage))
      (fallbackChecks gaugeRank.stage)
  · simp [canonicalPayloadChecksFor, active]

/-- Constructor-sealed row-12 output for one active row-11 successor. -/
structure Generated (profile : Profile rowEleven) (view : ActiveView rowEleven)
    where
  private mk ::
  response :
    _root_.Hypostructure.CT3.ExecutionResult profile.responseSpec
      profile.responseCapability
  dyadic :
    _root_.Hypostructure.CT14.ExecutionResult profile.dyadicSpec
      profile.dyadicCapability
  gaugeRank :
    _root_.Hypostructure.CT15.ExecutionResult profile.gaugeRankSpec
      profile.gaugeRankCapability
  fallback :
    _root_.Hypostructure.CT13.ExecutionResult profile.fallbackSpec
      profile.fallbackCapability

set_option maxHeartbeats 800000

/-- Execute CT3, CT14, CT15, then CT13 on one row-11 successor view. -/
def generateActiveCounted
    (profile : Profile rowEleven) (view : ActiveView rowEleven) :
    Counted (Generated profile view) :=
  let response :
      _root_.Hypostructure.CT3.ExecutionResult profile.responseSpec
        profile.responseCapability :=
    _root_.Hypostructure.CT3.run profile.responseSpec
      profile.responseCapability view
  let dyadic :
      _root_.Hypostructure.CT14.ExecutionResult profile.dyadicSpec
        profile.dyadicCapability :=
    _root_.Hypostructure.CT14.run profile.dyadicSpec
      profile.dyadicCapability response.stage
  let gaugeRank :
      _root_.Hypostructure.CT15.ExecutionResult profile.gaugeRankSpec
        profile.gaugeRankCapability :=
    _root_.Hypostructure.CT15.run profile.gaugeRankSpec
      profile.gaugeRankCapability dyadic.stage
  let fallback :
      _root_.Hypostructure.CT13.ExecutionResult profile.fallbackSpec
        profile.fallbackCapability :=
    _root_.Hypostructure.CT13.run profile.fallbackSpec
      profile.fallbackCapability gaugeRank.stage
  {
    value := {
      response := response
      dyadic := dyadic
      gaugeRank := gaugeRank
      fallback := fallback
    }
    checks := response.checks + dyadic.checks + gaugeRank.checks +
      fallback.checks
  }

@[simp] theorem generateActiveCounted_checks
    (profile : Profile rowEleven) (view : ActiveView rowEleven) :
    (generateActiveCounted profile view).checks =
      (generateActiveCounted profile view).value.response.checks +
        (generateActiveCounted profile view).value.dyadic.checks +
        (generateActiveCounted profile view).value.gaugeRank.checks +
        (generateActiveCounted profile view).value.fallback.checks :=
  rfl

abbrev Output (profile : Profile rowEleven)
    (previous : RowElevenStage rowEleven)
    (proof : (ConservativeCarrier.SuccessorFocus rowEleven).Active previous) :=
  Generated profile (Residual.Focus.ActiveView.of previous proof)

abbrev Stage (profile : Profile rowEleven) :=
  Residual.Focus.Stage (ConservativeCarrier.SuccessorFocus rowEleven)
    (Output profile)

abbrev SuccessorFocus (profile : Profile rowEleven) :=
  Residual.Focus.successor (ConservativeCarrier.SuccessorFocus rowEleven)
    (Output profile)

def payloadBudget (profile : Profile rowEleven) :
    PolynomialCheckBudget (RowElevenStage rowEleven) where
  size := profile.inputSize
  checks := profile.payloadChecks
  coefficient := profile.workCoefficient
  degree := profile.workDegree
  bounded := profile.workBound

private theorem generateActiveCounted_checks_eq_payloadBudget
    (profile : Profile rowEleven) (previous : RowElevenStage rowEleven)
    (active : (ConservativeCarrier.SuccessorFocus rowEleven).Active previous) :
    (generateActiveCounted profile
      (Residual.Focus.ActiveView.of previous active)).checks =
      (payloadBudget profile).checks previous := by
  unfold payloadBudget
  change
    (generateActiveCounted profile
      (Residual.Focus.ActiveView.of previous active)).checks =
      profile.payloadChecks previous
  rw [profile.payloadChecks_active previous active]
  rfl

def outputQuery (profile : Profile rowEleven) :
    Residual.Focus.ActiveQuery (SuccessorFocus profile)
      fun stage active => Output profile stage.previous active :=
  Residual.Focus.ActiveQuery.latest

noncomputable def run
    (profile : Profile rowEleven) (previous : RowElevenStage rowEleven) :
    Counted (Stage profile) :=
  Residual.Focus.runCountedPayload
    (Output := Output profile)
    (ConservativeCarrier.SuccessorFocus rowEleven) (payloadBudget profile)
    previous
    (fun proof _selectionChecks _selectionExact =>
      generateActiveCounted profile
        (Residual.Focus.ActiveView.of previous proof))
    (fun proof _selectionChecks _selectionExact =>
      generateActiveCounted_checks_eq_payloadBudget profile previous proof)

@[simp] theorem run_previous
    (profile : Profile rowEleven) (previous : RowElevenStage rowEleven) :
    (run profile previous).value.previous = previous := by
  unfold run
  exact Residual.Focus.runCountedPayload_previous
    (Output := Output profile)
    (ConservativeCarrier.SuccessorFocus rowEleven) (payloadBudget profile)
    previous
    (fun proof _selectionChecks _selectionExact =>
      generateActiveCounted profile
        (Residual.Focus.ActiveView.of previous proof))
    (fun proof _selectionChecks _selectionExact =>
      generateActiveCounted_checks_eq_payloadBudget profile previous proof)

theorem run_checks_of_active
    (profile : Profile rowEleven) (previous : RowElevenStage rowEleven)
    (active : (ConservativeCarrier.SuccessorFocus rowEleven).Active previous) :
    (run profile previous).checks =
      (ConservativeCarrier.SuccessorFocus rowEleven).selectionBudget.checks
        previous +
        (generateActiveCounted profile
          (Residual.Focus.ActiveView.of previous active)).checks := by
  have exactCore :=
    Residual.Focus.runCountedPayload_checks_of_active
      (Output := Output profile)
      (ConservativeCarrier.SuccessorFocus rowEleven) (payloadBudget profile)
      previous
      (fun proof _selectionChecks _selectionExact =>
        generateActiveCounted profile
          (Residual.Focus.ActiveView.of previous proof))
      (fun proof _selectionChecks _selectionExact =>
        generateActiveCounted_checks_eq_payloadBudget profile previous proof)
      active
  unfold run
  rw [exactCore]
  unfold PolynomialCheckBudget.add
  rw [generateActiveCounted_checks_eq_payloadBudget profile previous active]

theorem run_checks_of_inactive
    (profile : Profile rowEleven) (previous : RowElevenStage rowEleven)
    (inactive :
      Not ((ConservativeCarrier.SuccessorFocus rowEleven).Active previous)) :
    (run profile previous).checks =
      (ConservativeCarrier.SuccessorFocus rowEleven).selectionBudget.checks
        previous := by
  unfold run
  exact Residual.Focus.runCountedPayload_checks_of_inactive
    (Output := Output profile)
    (ConservativeCarrier.SuccessorFocus rowEleven) (payloadBudget profile)
    previous
    (fun proof _selectionChecks _selectionExact =>
      generateActiveCounted profile
        (Residual.Focus.ActiveView.of previous proof))
    (fun proof _selectionChecks _selectionExact =>
      generateActiveCounted_checks_eq_payloadBudget profile previous proof)
    inactive

theorem run_checks_bounded
    (profile : Profile rowEleven) (previous : RowElevenStage rowEleven) :
    (run profile previous).checks <=
      ((ConservativeCarrier.SuccessorFocus rowEleven).selectionBudget.add
        (payloadBudget profile)).coefficient *
      (((ConservativeCarrier.SuccessorFocus rowEleven).selectionBudget.add
        (payloadBudget profile)).size previous + 1) ^
      ((ConservativeCarrier.SuccessorFocus rowEleven).selectionBudget.add
        (payloadBudget profile)).degree := by
  unfold run
  exact Residual.Focus.runCountedPayload_checks_bounded
    (Output := Output profile)
    (ConservativeCarrier.SuccessorFocus rowEleven) (payloadBudget profile)
    previous
    (fun proof _selectionChecks _selectionExact =>
      generateActiveCounted profile
        (Residual.Focus.ActiveView.of previous proof))
    (fun proof _selectionChecks _selectionExact =>
      generateActiveCounted_checks_eq_payloadBudget profile previous proof)

end Hypostructure.PDE.FastTrack.EllipticConstraintTail
