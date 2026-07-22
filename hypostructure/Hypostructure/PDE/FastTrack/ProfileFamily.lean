import Hypostructure.CT11.Automation
import Hypostructure.CT12.Automation
import Hypostructure.CT17.Automation
import Hypostructure.PDE.FastTrack.ExactResponseCoverage

/-!
# PDE fast-track row 9: profile-family resource localization

Row 9 consumes the row-8 successor residual.  On that focused predecessor the
framework runs CT17 for bounded target thickening, CT12 for the residual-owned
finite profile schedule, and CT11 for the resulting additive budget
localization.  The application registers only the three shared CT capabilities
and a payload work envelope; CT sequencing, focused routing, ledger extension,
and work composition remain framework-owned.
-/

namespace Hypostructure.PDE.FastTrack.ProfileFamily

open Hypostructure.Core

universe uPrevious uPotential uCurrent
universe uRepresentative uContext uCoordinate uValue uCandidate uRow
universe uRepresentative7 uContext7 uCoordinate7 uValue7
universe uTarget uOffset uPosition uThickValue
universe uState uPeeled uDemand uTier uCell

variable {Previous : Type uPrevious}
variable {Potential : Type uPotential} {Current : Type uCurrent}
variable [NormedAddCommGroup Potential] [InnerProductSpace Real Potential]
variable [CompleteSpace Potential]
variable [NormedAddCommGroup Current] [InnerProductSpace Real Current]
variable [CompleteSpace Current]

variable {focus : Residual.Focus.Profile Previous}
variable {rowFive : DirectedExhaustiveness.Profile Previous focus Potential Current}
variable {rowSix : DefectRouting.Profile rowFive}
variable {rowSeven : CapacityProfile.Profile rowSix}

/-- Literal row-8 stage consumed by row 9. -/
abbrev RowEightStage (rowEight : ExactResponseCoverage.Profile rowSeven) :=
  ExactResponseCoverage.Stage rowEight

/-- Exact row-8 successor view selected by the framework. -/
abbrev ActiveView (rowEight : ExactResponseCoverage.Profile rowSeven) :=
  Residual.Focus.ActiveView (ExactResponseCoverage.SuccessorFocus rowEight)

/-- Minimal row-9 registration.  CT17 is run over the active row-8 view, CT12
over the exact CT17 stage, and CT11 over the exact CT12 stage. -/
structure Profile (rowEight : ExactResponseCoverage.Profile rowSeven) where
  thickeningSpec :
    _root_.Hypostructure.CT17.Spec.{_, uTarget, uOffset, uPosition,
      uThickValue} (ActiveView rowEight)
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
  inputSize : RowEightStage rowEight -> Nat
  payloadChecks : RowEightStage rowEight -> Nat
  payloadChecks_active : forall (previous : RowEightStage rowEight)
    (active : (ExactResponseCoverage.SuccessorFocus rowEight).Active previous),
    payloadChecks previous =
      let view := Residual.Focus.ActiveView.of previous active
      let thickening :=
        _root_.Hypostructure.CT17.run thickeningSpec thickeningCapability view
      let peeling :=
        _root_.Hypostructure.CT12.run peelingSpec peelingCapability
          thickening.stage
      thickening.checks + peeling.checks +
        (_root_.Hypostructure.CT11.run budgetSpec budgetCapability
          peeling.stage).checks
  workCoefficient : Nat
  workDegree : Nat
  workBound : forall previous,
    payloadChecks previous <=
      workCoefficient * (inputSize previous + 1) ^ workDegree

variable {rowEight : ExactResponseCoverage.Profile rowSeven}

/-- Canonical row-9 payload accounting: if the row-8 successor focus is
active, run CT17, then CT12 on the exact CT17 stage, then CT11 on the exact
CT12 stage.  Inactive siblings receive no active payload. -/
noncomputable def canonicalPayloadChecksFor
    (thickeningSpec :
      _root_.Hypostructure.CT17.Spec.{_, uTarget, uOffset, uPosition,
        uThickValue} (ActiveView rowEight))
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
    (previous : RowEightStage rowEight) : Nat := by
  classical
  exact
    if active : (ExactResponseCoverage.SuccessorFocus rowEight).Active
        previous then
      let view := Residual.Focus.ActiveView.of previous active
      let thickening :=
        _root_.Hypostructure.CT17.run thickeningSpec thickeningCapability view
      let peeling :=
        _root_.Hypostructure.CT12.run peelingSpec peelingCapability
          thickening.stage
      thickening.checks + peeling.checks +
        (_root_.Hypostructure.CT11.run budgetSpec budgetCapability
          peeling.stage).checks
    else
      0

theorem canonicalPayloadChecksFor_active
    (thickeningSpec :
      _root_.Hypostructure.CT17.Spec.{_, uTarget, uOffset, uPosition,
        uThickValue} (ActiveView rowEight))
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
    (previous : RowEightStage rowEight)
    (active :
      (ExactResponseCoverage.SuccessorFocus rowEight).Active previous) :
    canonicalPayloadChecksFor thickeningSpec thickeningCapability
        peelingSpec peelingCapability budgetSpec budgetCapability previous =
      let view := Residual.Focus.ActiveView.of previous active
      let thickening :=
        _root_.Hypostructure.CT17.run thickeningSpec thickeningCapability view
      let peeling :=
        _root_.Hypostructure.CT12.run peelingSpec peelingCapability
          thickening.stage
      thickening.checks + peeling.checks +
        (_root_.Hypostructure.CT11.run budgetSpec budgetCapability
          peeling.stage).checks := by
  unfold canonicalPayloadChecksFor
  rw [dif_pos active]

theorem canonicalPayloadChecksFor_le_of_component_bounds
    (thickeningSpec :
      _root_.Hypostructure.CT17.Spec.{_, uTarget, uOffset, uPosition,
        uThickValue} (ActiveView rowEight))
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
    (thickeningChecks :
      forall view,
        (_root_.Hypostructure.CT17.run thickeningSpec thickeningCapability
          view).checks <= thickeningBound)
    (peelingChecks :
      forall stage,
        (_root_.Hypostructure.CT12.run peelingSpec peelingCapability
          stage).checks <= peelingBound)
    (budgetChecks :
      forall stage,
        (_root_.Hypostructure.CT11.run budgetSpec budgetCapability
          stage).checks <= budgetBound)
    (previous : RowEightStage rowEight) :
    canonicalPayloadChecksFor thickeningSpec thickeningCapability
        peelingSpec peelingCapability budgetSpec budgetCapability previous <=
      thickeningBound + peelingBound + budgetBound := by
  classical
  by_cases active :
      (ExactResponseCoverage.SuccessorFocus rowEight).Active previous
  · rw [canonicalPayloadChecksFor_active thickeningSpec thickeningCapability
      peelingSpec peelingCapability budgetSpec budgetCapability previous
      active]
    exact Nat.add_le_add
      (Nat.add_le_add
        (thickeningChecks (Residual.Focus.ActiveView.of previous active))
        (peelingChecks
          (_root_.Hypostructure.CT17.run thickeningSpec thickeningCapability
            (Residual.Focus.ActiveView.of previous active)).stage))
      (budgetChecks
        (_root_.Hypostructure.CT12.run peelingSpec peelingCapability
          (_root_.Hypostructure.CT17.run thickeningSpec thickeningCapability
            (Residual.Focus.ActiveView.of previous active)).stage).stage)
  · simp [canonicalPayloadChecksFor, active]

/-- Constructor-sealed row-9 output for one active row-8 successor. -/
structure Generated (profile : Profile rowEight) (view : ActiveView rowEight)
    where
  private mk ::
  thickening :
    _root_.Hypostructure.CT17.ExecutionResult profile.thickeningSpec
      profile.thickeningCapability
  peeling :
    _root_.Hypostructure.CT12.ExecutionResult profile.peelingSpec
      profile.peelingCapability
  budget :
    _root_.Hypostructure.CT11.ExecutionResult profile.budgetSpec
      profile.budgetCapability
  peeling_previous : peeling.stage.previous = thickening.stage
  budget_previous : budget.stage.previous = peeling.stage

namespace Generated

/-- CT17 terminal selected by the profile-family stage. -/
def thickeningTerminal {profile : Profile rowEight}
    {view : ActiveView rowEight} (generated : Generated profile view) :
    _root_.Hypostructure.CT17.Terminal :=
  generated.thickening.terminal

/-- CT12 terminal selected after bounded thickening. -/
def peelingTerminal {profile : Profile rowEight}
    {view : ActiveView rowEight} (generated : Generated profile view) :
    _root_.Hypostructure.CT12.Terminal :=
  generated.peeling.terminal

/-- CT11 terminal selected after profile peeling. -/
def budgetTerminal {profile : Profile rowEight}
    {view : ActiveView rowEight} (generated : Generated profile view) :
    _root_.Hypostructure.CT11.Terminal :=
  generated.budget.terminal

/-- Exact row-9 active payload work. -/
def checks {profile : Profile rowEight} {view : ActiveView rowEight}
    (generated : Generated profile view) : Nat :=
  generated.thickening.checks + generated.peeling.checks +
    generated.budget.checks

/-- Recover CT17 soundness for the exact row-9 thickening stage. -/
theorem thickening_verified {profile : Profile rowEight}
    {view : ActiveView rowEight} (generated : Generated profile view) :
    _root_.Hypostructure.CT17.OutcomeClaim generated.thickening.outcome :=
  generated.thickening.verified

/-- Recover CT12 soundness for the exact CT17 successor stage. -/
theorem peeling_verified {profile : Profile rowEight}
    {view : ActiveView rowEight} (generated : Generated profile view) :
    _root_.Hypostructure.CT12.OutcomeClaim generated.peeling.outcome :=
  generated.peeling.verified

/-- Recover CT11 soundness for the exact CT12 successor stage. -/
theorem budget_verified {profile : Profile rowEight}
    {view : ActiveView rowEight} (generated : Generated profile view) :
    _root_.Hypostructure.CT11.OutcomeClaim generated.budget.outcome :=
  generated.budget.verified

end Generated

/-- Execute CT17, CT12, then CT11 on one row-8 successor view. -/
def generateActiveCounted
    (profile : Profile rowEight) (view : ActiveView rowEight) :
    Counted (Generated profile view) :=
  let thickening :=
    _root_.Hypostructure.CT17.run profile.thickeningSpec
      profile.thickeningCapability view
  let peeling :=
    _root_.Hypostructure.CT12.run profile.peelingSpec
      profile.peelingCapability thickening.stage
  let budget :=
    _root_.Hypostructure.CT11.run profile.budgetSpec
      profile.budgetCapability peeling.stage
  {
    value := {
      thickening := thickening
      peeling := peeling
      budget := budget
      peeling_previous := rfl
      budget_previous := rfl
    }
    checks := thickening.checks + peeling.checks + budget.checks
  }

@[simp] theorem generateActiveCounted_checks
    (profile : Profile rowEight) (view : ActiveView rowEight) :
    (generateActiveCounted profile view).checks =
      (generateActiveCounted profile view).value.checks :=
  rfl

/-- Exact conditional payload appended by the row-9 executor. -/
abbrev Output (profile : Profile rowEight)
    (previous : RowEightStage rowEight)
    (proof : (ExactResponseCoverage.SuccessorFocus rowEight).Active previous) :=
  Generated profile (Residual.Focus.ActiveView.of previous proof)

/-- Literal accumulated stage emitted by row 9. -/
abbrev Stage (profile : Profile rowEight) :=
  Residual.Focus.Stage (ExactResponseCoverage.SuccessorFocus rowEight)
    (Output profile)

/-- Framework-owned successor focus for row-9 descendants. -/
abbrev SuccessorFocus (profile : Profile rowEight) :=
  Residual.Focus.successor (ExactResponseCoverage.SuccessorFocus rowEight)
    (Output profile)

/-- Worst-case active payload budget declared by the row-9 registration. -/
def payloadBudget (profile : Profile rowEight) :
    PolynomialCheckBudget (RowEightStage rowEight) where
  size := profile.inputSize
  checks := profile.payloadChecks
  coefficient := profile.workCoefficient
  degree := profile.workDegree
  bounded := profile.workBound

private theorem generateActiveCounted_checks_eq_payloadBudget
    (profile : Profile rowEight) (previous : RowEightStage rowEight)
    (active : (ExactResponseCoverage.SuccessorFocus rowEight).Active previous) :
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

/-- Retrieve the exact row-9 output from the accumulated successor ledger. -/
def outputQuery (profile : Profile rowEight) :
    Residual.Focus.ActiveQuery (SuccessorFocus profile)
      fun stage active => Output profile stage.previous active :=
  Residual.Focus.ActiveQuery.latest

/-- Execute row 9 through the existing focused counted machine. -/
noncomputable def run
    (profile : Profile rowEight) (previous : RowEightStage rowEight) :
    Counted (Stage profile) :=
  Residual.Focus.runCountedPayload
    (Output := Output profile)
    (ExactResponseCoverage.SuccessorFocus rowEight) (payloadBudget profile)
    previous
    (fun proof _selectionChecks _selectionExact =>
      generateActiveCounted profile
        (Residual.Focus.ActiveView.of previous proof))
    (fun proof _selectionChecks _selectionExact =>
      generateActiveCounted_checks_eq_payloadBudget profile previous proof)

@[simp] theorem run_previous
    (profile : Profile rowEight) (previous : RowEightStage rowEight) :
    (run profile previous).value.previous = previous := by
  unfold run
  exact Residual.Focus.runCountedPayload_previous
    (Output := Output profile)
    (ExactResponseCoverage.SuccessorFocus rowEight) (payloadBudget profile)
    previous
    (fun proof _selectionChecks _selectionExact =>
      generateActiveCounted profile
        (Residual.Focus.ActiveView.of previous proof))
    (fun proof _selectionChecks _selectionExact =>
      generateActiveCounted_checks_eq_payloadBudget profile previous proof)

theorem run_checks_of_active
    (profile : Profile rowEight) (previous : RowEightStage rowEight)
    (active : (ExactResponseCoverage.SuccessorFocus rowEight).Active previous) :
    (run profile previous).checks =
      (ExactResponseCoverage.SuccessorFocus rowEight).selectionBudget.checks
        previous +
        (generateActiveCounted profile
          (Residual.Focus.ActiveView.of previous active)).checks := by
  have exactCore :=
    Residual.Focus.runCountedPayload_checks_of_active
      (Output := Output profile)
      (ExactResponseCoverage.SuccessorFocus rowEight) (payloadBudget profile)
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
    (profile : Profile rowEight) (previous : RowEightStage rowEight)
    (inactive :
      Not ((ExactResponseCoverage.SuccessorFocus rowEight).Active previous)) :
    (run profile previous).checks =
      (ExactResponseCoverage.SuccessorFocus rowEight).selectionBudget.checks
        previous := by
  unfold run
  exact Residual.Focus.runCountedPayload_checks_of_inactive
    (Output := Output profile)
    (ExactResponseCoverage.SuccessorFocus rowEight) (payloadBudget profile)
    previous
    (fun proof _selectionChecks _selectionExact =>
      generateActiveCounted profile
        (Residual.Focus.ActiveView.of previous proof))
    (fun proof _selectionChecks _selectionExact =>
      generateActiveCounted_checks_eq_payloadBudget profile previous proof)
    inactive

theorem run_checks_bounded
    (profile : Profile rowEight) (previous : RowEightStage rowEight) :
    (run profile previous).checks <=
      ((ExactResponseCoverage.SuccessorFocus rowEight).selectionBudget.add
        (payloadBudget profile)).coefficient *
      (((ExactResponseCoverage.SuccessorFocus rowEight).selectionBudget.add
        (payloadBudget profile)).size previous + 1) ^
      ((ExactResponseCoverage.SuccessorFocus rowEight).selectionBudget.add
        (payloadBudget profile)).degree := by
  unfold run
  exact Residual.Focus.runCountedPayload_checks_bounded
    (Output := Output profile)
    (ExactResponseCoverage.SuccessorFocus rowEight) (payloadBudget profile)
    previous
    (fun proof _selectionChecks _selectionExact =>
      generateActiveCounted profile
        (Residual.Focus.ActiveView.of previous proof))
    (fun proof _selectionChecks _selectionExact =>
      generateActiveCounted_checks_eq_payloadBudget profile previous proof)

end Hypostructure.PDE.FastTrack.ProfileFamily
