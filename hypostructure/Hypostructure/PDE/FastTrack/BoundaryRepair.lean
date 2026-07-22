import Hypostructure.CT1.Automation
import Hypostructure.CT10.Automation
import Hypostructure.CT11.Automation
import Hypostructure.CT14.Automation
import Hypostructure.PDE.FastTrack.ProfileFamily

/-!
# PDE fast-track row 10: SCRC boundary repair

Row 10 consumes the row-9 successor residual.  On that focused predecessor the
framework runs CT10 for finite rigid/cost class stratification, CT11 for the
resulting signed budget localization, CT14 for the capacity/mass profile, and
CT1 for the target-visible in-window alternative.  The application registers
only the four shared CT capabilities and a payload work envelope; sequencing,
focused routing, ledger extension, and work composition are framework-owned.
-/

namespace Hypostructure.PDE.FastTrack.BoundaryRepair

open Hypostructure.Core

universe uPrevious uPotential uCurrent
universe uRepresentative uContext uCoordinate uValue uCandidate8 uRow
universe uRepresentative7 uContext7 uCoordinate7 uValue7
universe uTarget uOffset uPosition uThickValue
universe uState uPeeled uDemand uTier uCell9
universe uDatum uClass uPromotion uCell10 uMember uLabel uCandidate10

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
variable {rowEight : ExactResponseCoverage.Profile rowSeven}

/-- Literal row-9 stage consumed by row 10. -/
abbrev RowNineStage (rowNine : ProfileFamily.Profile rowEight) :=
  ProfileFamily.Stage rowNine

/-- Exact row-9 successor view selected by the framework. -/
abbrev ActiveView (rowNine : ProfileFamily.Profile rowEight) :=
  Residual.Focus.ActiveView (ProfileFamily.SuccessorFocus rowNine)

/-- Minimal row-10 registration. -/
structure Profile (rowNine : ProfileFamily.Profile rowEight) where
  classificationSpec :
    _root_.Hypostructure.CT10.Spec.{_, uDatum, uClass, uPromotion}
      (ActiveView rowNine)
  classificationCapability :
    _root_.Hypostructure.CT10.Capability classificationSpec
  budgetSpec :
    _root_.Hypostructure.CT11.Spec.{_, uCell10}
      (_root_.Hypostructure.CT10.Stage classificationSpec
        classificationCapability)
  budgetCapability :
    _root_.Hypostructure.CT11.Capability budgetSpec
  capacitySpec :
    _root_.Hypostructure.CT14.Spec.{_, uMember, uLabel}
      (_root_.Hypostructure.CT11.Stage budgetSpec budgetCapability)
  capacityCapability :
    _root_.Hypostructure.CT14.Capability capacitySpec
  targetSpec :
    _root_.Hypostructure.CT1.Spec.{_, uCandidate10}
      (_root_.Hypostructure.CT14.Stage capacitySpec capacityCapability)
  targetCapability :
    _root_.Hypostructure.CT1.Capability targetSpec
  inputSize : RowNineStage rowNine -> Nat
  payloadChecks : RowNineStage rowNine -> Nat
  payloadChecks_active : forall (previous : RowNineStage rowNine)
    (active : (ProfileFamily.SuccessorFocus rowNine).Active previous),
    payloadChecks previous =
      let view := Residual.Focus.ActiveView.of previous active
      let classification :=
        _root_.Hypostructure.CT10.run classificationCapability view
      let budget :=
        _root_.Hypostructure.CT11.run budgetSpec budgetCapability
          classification.stage
      let capacity :=
        _root_.Hypostructure.CT14.run capacitySpec capacityCapability
          budget.stage
      classification.checks + budget.checks + capacity.checks +
        (_root_.Hypostructure.CT1.run targetSpec targetCapability
          capacity.stage).checks
  workCoefficient : Nat
  workDegree : Nat
  workBound : forall previous,
    payloadChecks previous <=
      workCoefficient * (inputSize previous + 1) ^ workDegree

variable {rowNine : ProfileFamily.Profile rowEight}

/-- Canonical row-10 payload accounting. -/
noncomputable def canonicalPayloadChecksFor
    (classificationSpec :
      _root_.Hypostructure.CT10.Spec.{_, uDatum, uClass, uPromotion}
        (ActiveView rowNine))
    (classificationCapability :
      _root_.Hypostructure.CT10.Capability classificationSpec)
    (budgetSpec :
      _root_.Hypostructure.CT11.Spec.{_, uCell10}
        (_root_.Hypostructure.CT10.Stage classificationSpec
          classificationCapability))
    (budgetCapability :
      _root_.Hypostructure.CT11.Capability budgetSpec)
    (capacitySpec :
      _root_.Hypostructure.CT14.Spec.{_, uMember, uLabel}
        (_root_.Hypostructure.CT11.Stage budgetSpec budgetCapability))
    (capacityCapability :
      _root_.Hypostructure.CT14.Capability capacitySpec)
    (targetSpec :
      _root_.Hypostructure.CT1.Spec.{_, uCandidate10}
        (_root_.Hypostructure.CT14.Stage capacitySpec capacityCapability))
    (targetCapability :
      _root_.Hypostructure.CT1.Capability targetSpec)
    (previous : RowNineStage rowNine) : Nat := by
  classical
  exact
    if active : (ProfileFamily.SuccessorFocus rowNine).Active previous then
      let view := Residual.Focus.ActiveView.of previous active
      let classification :=
        _root_.Hypostructure.CT10.run classificationCapability view
      let budget :=
        _root_.Hypostructure.CT11.run budgetSpec budgetCapability
          classification.stage
      let capacity :=
        _root_.Hypostructure.CT14.run capacitySpec capacityCapability
          budget.stage
      classification.checks + budget.checks + capacity.checks +
        (_root_.Hypostructure.CT1.run targetSpec targetCapability
          capacity.stage).checks
    else
      0

theorem canonicalPayloadChecksFor_active
    (classificationSpec :
      _root_.Hypostructure.CT10.Spec.{_, uDatum, uClass, uPromotion}
        (ActiveView rowNine))
    (classificationCapability :
      _root_.Hypostructure.CT10.Capability classificationSpec)
    (budgetSpec :
      _root_.Hypostructure.CT11.Spec.{_, uCell10}
        (_root_.Hypostructure.CT10.Stage classificationSpec
          classificationCapability))
    (budgetCapability :
      _root_.Hypostructure.CT11.Capability budgetSpec)
    (capacitySpec :
      _root_.Hypostructure.CT14.Spec.{_, uMember, uLabel}
        (_root_.Hypostructure.CT11.Stage budgetSpec budgetCapability))
    (capacityCapability :
      _root_.Hypostructure.CT14.Capability capacitySpec)
    (targetSpec :
      _root_.Hypostructure.CT1.Spec.{_, uCandidate10}
        (_root_.Hypostructure.CT14.Stage capacitySpec capacityCapability))
    (targetCapability :
      _root_.Hypostructure.CT1.Capability targetSpec)
    (previous : RowNineStage rowNine)
    (active : (ProfileFamily.SuccessorFocus rowNine).Active previous) :
    canonicalPayloadChecksFor classificationSpec classificationCapability
        budgetSpec budgetCapability capacitySpec capacityCapability targetSpec
        targetCapability previous =
      let view := Residual.Focus.ActiveView.of previous active
      let classification :=
        _root_.Hypostructure.CT10.run classificationCapability view
      let budget :=
        _root_.Hypostructure.CT11.run budgetSpec budgetCapability
          classification.stage
      let capacity :=
        _root_.Hypostructure.CT14.run capacitySpec capacityCapability
          budget.stage
      classification.checks + budget.checks + capacity.checks +
        (_root_.Hypostructure.CT1.run targetSpec targetCapability
          capacity.stage).checks := by
  unfold canonicalPayloadChecksFor
  rw [dif_pos active]

theorem canonicalPayloadChecksFor_le_of_component_bounds
    (classificationSpec :
      _root_.Hypostructure.CT10.Spec.{_, uDatum, uClass, uPromotion}
        (ActiveView rowNine))
    (classificationCapability :
      _root_.Hypostructure.CT10.Capability classificationSpec)
    (budgetSpec :
      _root_.Hypostructure.CT11.Spec.{_, uCell10}
        (_root_.Hypostructure.CT10.Stage classificationSpec
          classificationCapability))
    (budgetCapability :
      _root_.Hypostructure.CT11.Capability budgetSpec)
    (capacitySpec :
      _root_.Hypostructure.CT14.Spec.{_, uMember, uLabel}
        (_root_.Hypostructure.CT11.Stage budgetSpec budgetCapability))
    (capacityCapability :
      _root_.Hypostructure.CT14.Capability capacitySpec)
    (targetSpec :
      _root_.Hypostructure.CT1.Spec.{_, uCandidate10}
        (_root_.Hypostructure.CT14.Stage capacitySpec capacityCapability))
    (targetCapability :
      _root_.Hypostructure.CT1.Capability targetSpec)
    (classificationBound budgetBound capacityBound targetBound : Nat)
    (classificationChecks :
      forall view,
        (_root_.Hypostructure.CT10.run classificationCapability
          view).checks <= classificationBound)
    (budgetChecks :
      forall stage,
        (_root_.Hypostructure.CT11.run budgetSpec budgetCapability
          stage).checks <= budgetBound)
    (capacityChecks :
      forall stage,
        (_root_.Hypostructure.CT14.run capacitySpec capacityCapability
          stage).checks <= capacityBound)
    (targetChecks :
      forall stage,
        (_root_.Hypostructure.CT1.run targetSpec targetCapability
          stage).checks <= targetBound)
    (previous : RowNineStage rowNine) :
    canonicalPayloadChecksFor classificationSpec classificationCapability
        budgetSpec budgetCapability capacitySpec capacityCapability targetSpec
        targetCapability previous <=
      classificationBound + budgetBound + capacityBound + targetBound := by
  classical
  by_cases active : (ProfileFamily.SuccessorFocus rowNine).Active previous
  · rw [canonicalPayloadChecksFor_active classificationSpec
      classificationCapability budgetSpec budgetCapability capacitySpec
      capacityCapability targetSpec targetCapability previous active]
    exact Nat.add_le_add
      (Nat.add_le_add
        (Nat.add_le_add
          (classificationChecks
            (Residual.Focus.ActiveView.of previous active))
          (budgetChecks
            (_root_.Hypostructure.CT10.run classificationCapability
              (Residual.Focus.ActiveView.of previous active)).stage))
        (capacityChecks
          (_root_.Hypostructure.CT11.run budgetSpec budgetCapability
            (_root_.Hypostructure.CT10.run classificationCapability
              (Residual.Focus.ActiveView.of previous active)).stage).stage))
      (targetChecks
        (_root_.Hypostructure.CT14.run capacitySpec capacityCapability
          (_root_.Hypostructure.CT11.run budgetSpec budgetCapability
            (_root_.Hypostructure.CT10.run classificationCapability
              (Residual.Focus.ActiveView.of previous active)).stage).stage).stage)
  · simp [canonicalPayloadChecksFor, active]

/-- Constructor-sealed row-10 output for one active row-9 successor. -/
structure Generated (profile : Profile rowNine) (view : ActiveView rowNine)
    where
  private mk ::
  classification :
    _root_.Hypostructure.CT10.ExecutionResult profile.classificationSpec
      profile.classificationCapability
  budget :
    _root_.Hypostructure.CT11.ExecutionResult profile.budgetSpec
      profile.budgetCapability
  capacity :
    _root_.Hypostructure.CT14.ExecutionResult profile.capacitySpec
      profile.capacityCapability
  target :
    _root_.Hypostructure.CT1.ExecutionResult profile.targetSpec
      profile.targetCapability
  budget_previous : budget.stage.previous = classification.stage
  capacity_previous : capacity.stage.previous = budget.stage
  target_previous : target.stage.previous = capacity.stage

namespace Generated

def classificationTerminal {profile : Profile rowNine}
    {view : ActiveView rowNine} (generated : Generated profile view) :
    _root_.Hypostructure.CT10.Terminal :=
  generated.classification.terminal

def budgetTerminal {profile : Profile rowNine}
    {view : ActiveView rowNine} (generated : Generated profile view) :
    _root_.Hypostructure.CT11.Terminal :=
  generated.budget.terminal

def capacityTerminal {profile : Profile rowNine}
    {view : ActiveView rowNine} (generated : Generated profile view) :
    _root_.Hypostructure.CT14.Terminal :=
  generated.capacity.terminal

def targetTerminal {profile : Profile rowNine}
    {view : ActiveView rowNine} (generated : Generated profile view) :
    _root_.Hypostructure.CT1.Terminal :=
  generated.target.terminal

def checks {profile : Profile rowNine} {view : ActiveView rowNine}
    (generated : Generated profile view) : Nat :=
  generated.classification.checks + generated.budget.checks +
    generated.capacity.checks + generated.target.checks

theorem classification_verified {profile : Profile rowNine}
    {view : ActiveView rowNine} (generated : Generated profile view) :
    _root_.Hypostructure.CT10.OutcomeClaim
      profile.classificationCapability
      generated.classification.stage.previous
      generated.classification.terminal :=
  generated.classification.verified

theorem budget_verified {profile : Profile rowNine}
    {view : ActiveView rowNine} (generated : Generated profile view) :
    _root_.Hypostructure.CT11.OutcomeClaim generated.budget.outcome :=
  generated.budget.verified

theorem capacity_verified {profile : Profile rowNine}
    {view : ActiveView rowNine} (generated : Generated profile view) :
    _root_.Hypostructure.CT14.OutcomeClaim generated.capacity.outcome :=
  generated.capacity.verified

theorem target_verified {profile : Profile rowNine}
    {view : ActiveView rowNine} (generated : Generated profile view) :
    _root_.Hypostructure.CT1.OutcomeClaim profile.targetSpec
      profile.targetCapability generated.target.stage.previous
      generated.target.terminal :=
  generated.target.verified

end Generated

/-- Execute CT10, CT11, CT14, then CT1 on one row-9 successor view. -/
def generateActiveCounted
    (profile : Profile rowNine) (view : ActiveView rowNine) :
    Counted (Generated profile view) :=
  let classification :=
    _root_.Hypostructure.CT10.run profile.classificationCapability view
  let budget :=
    _root_.Hypostructure.CT11.run profile.budgetSpec
      profile.budgetCapability classification.stage
  let capacity :=
    _root_.Hypostructure.CT14.run profile.capacitySpec
      profile.capacityCapability budget.stage
  let target :=
    _root_.Hypostructure.CT1.run profile.targetSpec
      profile.targetCapability capacity.stage
  {
    value := {
      classification := classification
      budget := budget
      capacity := capacity
      target := target
      budget_previous := rfl
      capacity_previous := rfl
      target_previous := rfl
    }
    checks := classification.checks + budget.checks + capacity.checks +
      target.checks
  }

@[simp] theorem generateActiveCounted_checks
    (profile : Profile rowNine) (view : ActiveView rowNine) :
    (generateActiveCounted profile view).checks =
      (generateActiveCounted profile view).value.checks :=
  rfl

abbrev Output (profile : Profile rowNine)
    (previous : RowNineStage rowNine)
    (proof : (ProfileFamily.SuccessorFocus rowNine).Active previous) :=
  Generated profile (Residual.Focus.ActiveView.of previous proof)

abbrev Stage (profile : Profile rowNine) :=
  Residual.Focus.Stage (ProfileFamily.SuccessorFocus rowNine)
    (Output profile)

abbrev SuccessorFocus (profile : Profile rowNine) :=
  Residual.Focus.successor (ProfileFamily.SuccessorFocus rowNine)
    (Output profile)

def payloadBudget (profile : Profile rowNine) :
    PolynomialCheckBudget (RowNineStage rowNine) where
  size := profile.inputSize
  checks := profile.payloadChecks
  coefficient := profile.workCoefficient
  degree := profile.workDegree
  bounded := profile.workBound

private theorem generateActiveCounted_checks_eq_payloadBudget
    (profile : Profile rowNine) (previous : RowNineStage rowNine)
    (active : (ProfileFamily.SuccessorFocus rowNine).Active previous) :
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

def outputQuery (profile : Profile rowNine) :
    Residual.Focus.ActiveQuery (SuccessorFocus profile)
      fun stage active => Output profile stage.previous active :=
  Residual.Focus.ActiveQuery.latest

noncomputable def run
    (profile : Profile rowNine) (previous : RowNineStage rowNine) :
    Counted (Stage profile) :=
  Residual.Focus.runCountedPayload
    (Output := Output profile)
    (ProfileFamily.SuccessorFocus rowNine) (payloadBudget profile)
    previous
    (fun proof _selectionChecks _selectionExact =>
      generateActiveCounted profile
        (Residual.Focus.ActiveView.of previous proof))
    (fun proof _selectionChecks _selectionExact =>
      generateActiveCounted_checks_eq_payloadBudget profile previous proof)

@[simp] theorem run_previous
    (profile : Profile rowNine) (previous : RowNineStage rowNine) :
    (run profile previous).value.previous = previous := by
  unfold run
  exact Residual.Focus.runCountedPayload_previous
    (Output := Output profile)
    (ProfileFamily.SuccessorFocus rowNine) (payloadBudget profile)
    previous
    (fun proof _selectionChecks _selectionExact =>
      generateActiveCounted profile
        (Residual.Focus.ActiveView.of previous proof))
    (fun proof _selectionChecks _selectionExact =>
      generateActiveCounted_checks_eq_payloadBudget profile previous proof)

theorem run_checks_of_active
    (profile : Profile rowNine) (previous : RowNineStage rowNine)
    (active : (ProfileFamily.SuccessorFocus rowNine).Active previous) :
    (run profile previous).checks =
      (ProfileFamily.SuccessorFocus rowNine).selectionBudget.checks
        previous +
        (generateActiveCounted profile
          (Residual.Focus.ActiveView.of previous active)).checks := by
  have exactCore :=
    Residual.Focus.runCountedPayload_checks_of_active
      (Output := Output profile)
      (ProfileFamily.SuccessorFocus rowNine) (payloadBudget profile)
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
    (profile : Profile rowNine) (previous : RowNineStage rowNine)
    (inactive :
      Not ((ProfileFamily.SuccessorFocus rowNine).Active previous)) :
    (run profile previous).checks =
      (ProfileFamily.SuccessorFocus rowNine).selectionBudget.checks
        previous := by
  unfold run
  exact Residual.Focus.runCountedPayload_checks_of_inactive
    (Output := Output profile)
    (ProfileFamily.SuccessorFocus rowNine) (payloadBudget profile)
    previous
    (fun proof _selectionChecks _selectionExact =>
      generateActiveCounted profile
        (Residual.Focus.ActiveView.of previous proof))
    (fun proof _selectionChecks _selectionExact =>
      generateActiveCounted_checks_eq_payloadBudget profile previous proof)
    inactive

theorem run_checks_bounded
    (profile : Profile rowNine) (previous : RowNineStage rowNine) :
    (run profile previous).checks <=
      ((ProfileFamily.SuccessorFocus rowNine).selectionBudget.add
        (payloadBudget profile)).coefficient *
      (((ProfileFamily.SuccessorFocus rowNine).selectionBudget.add
        (payloadBudget profile)).size previous + 1) ^
      ((ProfileFamily.SuccessorFocus rowNine).selectionBudget.add
        (payloadBudget profile)).degree := by
  unfold run
  exact Residual.Focus.runCountedPayload_checks_bounded
    (Output := Output profile)
    (ProfileFamily.SuccessorFocus rowNine) (payloadBudget profile)
    previous
    (fun proof _selectionChecks _selectionExact =>
      generateActiveCounted profile
        (Residual.Focus.ActiveView.of previous proof))
    (fun proof _selectionChecks _selectionExact =>
      generateActiveCounted_checks_eq_payloadBudget profile previous proof)

end Hypostructure.PDE.FastTrack.BoundaryRepair
