import Hypostructure.CT3.Execution
import Hypostructure.CT7.Automation
import Hypostructure.PDE.CT3
import Hypostructure.PDE.FastTrack.CapacityProfile

/-!
# PDE fast-track row 8: exact response coverage

Row 8 consumes exactly the positive-capacity row-7 residual.  On that focused
predecessor it runs CT3 to classify the finite response table, then runs CT7 on
the exact CT3 stage.  The PDE layer supplies only the two CT capabilities and a
polynomial payload envelope; CT3, CT7, and Core own all routing, ledgers, traces,
and work accounting.
-/

namespace Hypostructure.PDE.FastTrack.ExactResponseCoverage

open Hypostructure.Core

universe uPrevious uPotential uCurrent
universe uRepresentative uContext uCoordinate uValue uCandidate uRow
universe uRepresentative7 uContext7 uCoordinate7 uValue7

variable {Previous : Type uPrevious}
variable {Potential : Type uPotential} {Current : Type uCurrent}
variable [NormedAddCommGroup Potential] [InnerProductSpace Real Potential]
variable [CompleteSpace Potential]
variable [NormedAddCommGroup Current] [InnerProductSpace Real Current]
variable [CompleteSpace Current]

variable {focus : Residual.Focus.Profile Previous}
variable {rowFive : DirectedExhaustiveness.Profile Previous focus Potential Current}
variable {rowSix : DefectRouting.Profile rowFive}

/-- Literal row-7 stage consumed by row 8. -/
abbrev RowSevenStage (rowSeven : CapacityProfile.Profile rowSix) :=
  CapacityProfile.Stage rowSeven

/-- Exact positive-capacity row-7 active view. -/
abbrev ActiveView (rowSeven : CapacityProfile.Profile rowSix) :=
  Residual.Focus.ActiveView (CapacityProfile.PositiveCapacityFocus rowSeven)

/-- Minimal row-8 registration.  CT3 is run over the row-7 positive-capacity
view, and CT7 is run over the exact CT3 stage. -/
structure Profile (rowSeven : CapacityProfile.Profile rowSix) where
  responseSpec :
    _root_.Hypostructure.CT3.Spec.{_, uRepresentative, uContext,
      uCoordinate, uValue, uCandidate, uRow} (ActiveView rowSeven)
  responseCapability :
    _root_.Hypostructure.CT3.Capability responseSpec
  contextSpec :
    _root_.Hypostructure.CT7.Spec.{_, uRepresentative7, uContext7,
      uCoordinate7, uValue7}
      (_root_.Hypostructure.CT3.Stage responseSpec responseCapability)
  contextCapability :
    _root_.Hypostructure.CT7.Capability contextSpec
  inputSize : RowSevenStage rowSeven -> Nat
  payloadChecks : RowSevenStage rowSeven -> Nat
  payloadChecks_active : forall (previous : RowSevenStage rowSeven)
    (active : (CapacityProfile.PositiveCapacityFocus rowSeven).Active previous),
    payloadChecks previous =
      let view := Residual.Focus.ActiveView.of previous active
      let ct3 :=
        _root_.Hypostructure.CT3.run responseSpec responseCapability view
      ct3.checks +
        (_root_.Hypostructure.CT7.run contextSpec contextCapability
          ct3.stage).checks
  workCoefficient : Nat
  workDegree : Nat
  workBound : forall previous,
    payloadChecks previous <=
      workCoefficient * (inputSize previous + 1) ^ workDegree

variable {rowSeven : CapacityProfile.Profile rowSix}

/-- Canonical row-8 payload accounting: if the row-7 positive-capacity focus
is active, run CT3 and then CT7 on the resulting stage; otherwise the focused
executor installs only the inactive marker. -/
noncomputable def canonicalPayloadChecksFor
    (responseSpec :
      _root_.Hypostructure.CT3.Spec.{_, uRepresentative, uContext,
        uCoordinate, uValue, uCandidate, uRow} (ActiveView rowSeven))
    (responseCapability :
      _root_.Hypostructure.CT3.Capability responseSpec)
    (contextSpec :
      _root_.Hypostructure.CT7.Spec.{_, uRepresentative7, uContext7,
        uCoordinate7, uValue7}
        (_root_.Hypostructure.CT3.Stage responseSpec responseCapability))
    (contextCapability :
      _root_.Hypostructure.CT7.Capability contextSpec)
    (previous : RowSevenStage rowSeven) : Nat := by
  classical
  exact
    if active : (CapacityProfile.PositiveCapacityFocus rowSeven).Active
        previous then
      let view := Residual.Focus.ActiveView.of previous active
      let response :=
        _root_.Hypostructure.CT3.run responseSpec responseCapability view
      response.checks +
        (_root_.Hypostructure.CT7.run contextSpec contextCapability
          response.stage).checks
    else
      0

theorem canonicalPayloadChecksFor_active
    (responseSpec :
      _root_.Hypostructure.CT3.Spec.{_, uRepresentative, uContext,
        uCoordinate, uValue, uCandidate, uRow} (ActiveView rowSeven))
    (responseCapability :
      _root_.Hypostructure.CT3.Capability responseSpec)
    (contextSpec :
      _root_.Hypostructure.CT7.Spec.{_, uRepresentative7, uContext7,
        uCoordinate7, uValue7}
        (_root_.Hypostructure.CT3.Stage responseSpec responseCapability))
    (contextCapability :
      _root_.Hypostructure.CT7.Capability contextSpec)
    (previous : RowSevenStage rowSeven)
    (active :
      (CapacityProfile.PositiveCapacityFocus rowSeven).Active previous) :
    canonicalPayloadChecksFor responseSpec responseCapability contextSpec
        contextCapability previous =
      let view := Residual.Focus.ActiveView.of previous active
      let response :=
        _root_.Hypostructure.CT3.run responseSpec responseCapability view
      response.checks +
        (_root_.Hypostructure.CT7.run contextSpec contextCapability
          response.stage).checks := by
  unfold canonicalPayloadChecksFor
  rw [dif_pos active]

theorem canonicalPayloadChecksFor_le_of_component_bounds
    (responseSpec :
      _root_.Hypostructure.CT3.Spec.{_, uRepresentative, uContext,
        uCoordinate, uValue, uCandidate, uRow} (ActiveView rowSeven))
    (responseCapability :
      _root_.Hypostructure.CT3.Capability responseSpec)
    (contextSpec :
      _root_.Hypostructure.CT7.Spec.{_, uRepresentative7, uContext7,
        uCoordinate7, uValue7}
        (_root_.Hypostructure.CT3.Stage responseSpec responseCapability))
    (contextCapability :
      _root_.Hypostructure.CT7.Capability contextSpec)
    (responseBound contextBound : Nat)
    (responseChecks :
      forall view,
        (_root_.Hypostructure.CT3.run responseSpec responseCapability
          view).checks <= responseBound)
    (contextChecks :
      forall stage,
        (_root_.Hypostructure.CT7.run contextSpec contextCapability
          stage).checks <= contextBound)
    (previous : RowSevenStage rowSeven) :
    canonicalPayloadChecksFor responseSpec responseCapability contextSpec
        contextCapability previous <= responseBound + contextBound := by
  classical
  by_cases active :
      (CapacityProfile.PositiveCapacityFocus rowSeven).Active previous
  · rw [canonicalPayloadChecksFor_active responseSpec responseCapability
      contextSpec contextCapability previous active]
    exact Nat.add_le_add
      (responseChecks (Residual.Focus.ActiveView.of previous active))
      (contextChecks
        (_root_.Hypostructure.CT3.run responseSpec responseCapability
          (Residual.Focus.ActiveView.of previous active)).stage)
  · simp [canonicalPayloadChecksFor, active]

/-- Constructor-sealed row-8 output for one active row-7 residual. -/
structure Generated (profile : Profile rowSeven) (view : ActiveView rowSeven)
    where
  private mk ::
  response :
    _root_.Hypostructure.CT3.ExecutionResult profile.responseSpec
      profile.responseCapability
  context :
    _root_.Hypostructure.CT7.ExecutionResult
      profile.contextSpec profile.contextCapability
  context_previous : context.stage.previous = response.stage

namespace Generated

/-- CT3 terminal selected by the exact response-coverage stage. -/
def responseTerminal {profile : Profile rowSeven} {view : ActiveView rowSeven}
    (generated : Generated profile view) :
    _root_.Hypostructure.CT3.Terminal :=
  generated.response.terminal

/-- CT7 terminal selected after the CT3 stage. -/
def contextTerminal {profile : Profile rowSeven} {view : ActiveView rowSeven}
    (generated : Generated profile view) :
    _root_.Hypostructure.CT7.Terminal :=
  generated.context.terminal

/-- Exact row-8 payload work. -/
def checks {profile : Profile rowSeven} {view : ActiveView rowSeven}
    (generated : Generated profile view) : Nat :=
  generated.response.checks + generated.context.checks

/-- Recover CT3 soundness for the exact row-8 response stage. -/
theorem response_verified {profile : Profile rowSeven}
    {view : ActiveView rowSeven}
    (generated : Generated profile view) :
    _root_.Hypostructure.CT3.OutcomeClaim generated.response.outcome :=
  generated.response.verified

/-- Recover CT7 soundness for the exact CT3 successor stage. -/
theorem context_verified {profile : Profile rowSeven}
    {view : ActiveView rowSeven}
    (generated : Generated profile view) :
    _root_.Hypostructure.CT7.OutcomeClaim generated.context.outcome :=
  generated.context.verified

end Generated

/-- Execute CT3 and then CT7 on one row-7 positive-capacity view. -/
def generateActiveCounted
    (profile : Profile rowSeven) (view : ActiveView rowSeven) :
    Counted (Generated profile view) :=
  let response :=
    _root_.Hypostructure.CT3.run profile.responseSpec
      profile.responseCapability view
  let context :=
    _root_.Hypostructure.CT7.run profile.contextSpec
      profile.contextCapability response.stage
  {
    value := {
      response := response
      context := context
      context_previous := rfl
    }
    checks := response.checks + context.checks
  }

@[simp] theorem generateActiveCounted_checks
    (profile : Profile rowSeven) (view : ActiveView rowSeven) :
    (generateActiveCounted profile view).checks =
      (generateActiveCounted profile view).value.checks :=
  rfl

/-- Exact conditional payload appended by the row-8 executor. -/
abbrev Output (profile : Profile rowSeven)
    (previous : RowSevenStage rowSeven)
    (proof : (CapacityProfile.PositiveCapacityFocus rowSeven).Active previous) :=
  Generated profile (Residual.Focus.ActiveView.of previous proof)

/-- Literal accumulated stage emitted by row 8. -/
abbrev Stage (profile : Profile rowSeven) :=
  Residual.Focus.Stage (CapacityProfile.PositiveCapacityFocus rowSeven)
    (Output profile)

/-- Framework-owned successor focus for row-8 descendants. -/
abbrev SuccessorFocus (profile : Profile rowSeven) :=
  Residual.Focus.successor (CapacityProfile.PositiveCapacityFocus rowSeven)
    (Output profile)

/-- Worst-case active payload budget declared by the row-8 registration. -/
def payloadBudget (profile : Profile rowSeven) :
    PolynomialCheckBudget (RowSevenStage rowSeven) where
  size := profile.inputSize
  checks := profile.payloadChecks
  coefficient := profile.workCoefficient
  degree := profile.workDegree
  bounded := profile.workBound

private theorem generateActiveCounted_checks_eq_payloadBudget
    (profile : Profile rowSeven) (previous : RowSevenStage rowSeven)
    (active : (CapacityProfile.PositiveCapacityFocus rowSeven).Active previous) :
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

/-- Retrieve the exact row-8 output from the accumulated successor ledger. -/
def outputQuery (profile : Profile rowSeven) :
    Residual.Focus.ActiveQuery (SuccessorFocus profile)
      fun stage active => Output profile stage.previous active :=
  Residual.Focus.ActiveQuery.latest

/-- Execute row 8 through the existing focused counted machine. -/
noncomputable def run
    (profile : Profile rowSeven) (previous : RowSevenStage rowSeven) :
    Counted (Stage profile) :=
  Residual.Focus.runCountedPayload
    (Output := Output profile)
    (CapacityProfile.PositiveCapacityFocus rowSeven) (payloadBudget profile)
    previous
    (fun proof _selectionChecks _selectionExact =>
      generateActiveCounted profile
        (Residual.Focus.ActiveView.of previous proof))
    (fun proof _selectionChecks _selectionExact =>
      generateActiveCounted_checks_eq_payloadBudget profile previous proof)

@[simp] theorem run_previous
    (profile : Profile rowSeven) (previous : RowSevenStage rowSeven) :
    (run profile previous).value.previous = previous := by
  unfold run
  exact Residual.Focus.runCountedPayload_previous
    (Output := Output profile)
    (CapacityProfile.PositiveCapacityFocus rowSeven) (payloadBudget profile)
    previous
    (fun proof _selectionChecks _selectionExact =>
      generateActiveCounted profile
        (Residual.Focus.ActiveView.of previous proof))
    (fun proof _selectionChecks _selectionExact =>
      generateActiveCounted_checks_eq_payloadBudget profile previous proof)

theorem run_checks_of_active
    (profile : Profile rowSeven) (previous : RowSevenStage rowSeven)
    (active : (CapacityProfile.PositiveCapacityFocus rowSeven).Active previous) :
    (run profile previous).checks =
      (CapacityProfile.PositiveCapacityFocus rowSeven).selectionBudget.checks
        previous +
        (generateActiveCounted profile
          (Residual.Focus.ActiveView.of previous active)).checks := by
  have exactCore :=
    Residual.Focus.runCountedPayload_checks_of_active
      (Output := Output profile)
      (CapacityProfile.PositiveCapacityFocus rowSeven) (payloadBudget profile)
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
    (profile : Profile rowSeven) (previous : RowSevenStage rowSeven)
    (inactive :
      Not ((CapacityProfile.PositiveCapacityFocus rowSeven).Active previous)) :
    (run profile previous).checks =
      (CapacityProfile.PositiveCapacityFocus rowSeven).selectionBudget.checks
        previous := by
  unfold run
  exact Residual.Focus.runCountedPayload_checks_of_inactive
    (Output := Output profile)
    (CapacityProfile.PositiveCapacityFocus rowSeven) (payloadBudget profile)
    previous
    (fun proof _selectionChecks _selectionExact =>
      generateActiveCounted profile
        (Residual.Focus.ActiveView.of previous proof))
    (fun proof _selectionChecks _selectionExact =>
      generateActiveCounted_checks_eq_payloadBudget profile previous proof)
    inactive

theorem run_checks_bounded
    (profile : Profile rowSeven) (previous : RowSevenStage rowSeven) :
    (run profile previous).checks <=
      ((CapacityProfile.PositiveCapacityFocus rowSeven).selectionBudget.add
        (payloadBudget profile)).coefficient *
      (((CapacityProfile.PositiveCapacityFocus rowSeven).selectionBudget.add
        (payloadBudget profile)).size previous + 1) ^
      ((CapacityProfile.PositiveCapacityFocus rowSeven).selectionBudget.add
        (payloadBudget profile)).degree := by
  unfold run
  exact Residual.Focus.runCountedPayload_checks_bounded
    (Output := Output profile)
    (CapacityProfile.PositiveCapacityFocus rowSeven) (payloadBudget profile)
    previous
    (fun proof _selectionChecks _selectionExact =>
      generateActiveCounted profile
        (Residual.Focus.ActiveView.of previous proof))
    (fun proof _selectionChecks _selectionExact =>
      generateActiveCounted_checks_eq_payloadBudget profile previous proof)

end Hypostructure.PDE.FastTrack.ExactResponseCoverage
