import Hypostructure.CT5.Automation
import Hypostructure.CT11.Automation
import Hypostructure.CT14.Automation
import Hypostructure.PDE.FastTrack.BoundaryRepair

/-!
# PDE fast-track row 11: conservative carrier

Row 11 consumes the row-10 successor residual.  On that focused predecessor the
framework runs CT5 for conservative local-witness carrier aggregation, CT14
for the descended capacity/mass profile, and CT11 for the reduced signed budget
localization.  Applications register only the shared CT capabilities and work
envelopes; CT sequencing, focused routing, ledger extension, and payload
composition are framework-owned.
-/

namespace Hypostructure.PDE.FastTrack.ConservativeCarrier

open Hypostructure.Core

universe uPrevious uPotential uCurrent
universe uRepresentative uContext uCoordinate uValue uCandidate8 uRow
universe uRepresentative7 uContext7 uCoordinate7 uValue7
universe uTarget uOffset uPosition uThickValue
universe uState uPeeled uDemand uTier uCell9
universe uDatum uClass uPromotion uCell10 uMember10 uLabel10 uCandidate10
universe uSite uWitness uResource uMember11 uLabel11 uCell11

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
variable {rowNine : ProfileFamily.Profile rowEight}

/-- Literal row-10 stage consumed by row 11. -/
abbrev RowTenStage (rowTen : BoundaryRepair.Profile rowNine) :=
  BoundaryRepair.Stage rowTen

/-- Exact row-10 successor view selected by the framework. -/
abbrev ActiveView (rowTen : BoundaryRepair.Profile rowNine) :=
  Residual.Focus.ActiveView (BoundaryRepair.SuccessorFocus rowTen)

/-- Minimal row-11 registration. -/
structure Profile (rowTen : BoundaryRepair.Profile rowNine) where
  carrierSpec :
    _root_.Hypostructure.CT5.Spec.{_, uSite, uWitness, uResource}
      (ActiveView rowTen)
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
  inputSize : RowTenStage rowTen -> Nat
  payloadChecks : RowTenStage rowTen -> Nat
  payloadChecks_active : forall (previous : RowTenStage rowTen)
    (active : (BoundaryRepair.SuccessorFocus rowTen).Active previous),
    payloadChecks previous =
      let view := Residual.Focus.ActiveView.of previous active
      let carrier :=
        _root_.Hypostructure.CT5.run carrierSpec carrierCapability view
      let capacity :=
        _root_.Hypostructure.CT14.run capacitySpec capacityCapability
          carrier.stage
      carrier.checks + capacity.checks +
        (_root_.Hypostructure.CT11.run budgetSpec budgetCapability
          capacity.stage).checks
  workCoefficient : Nat
  workDegree : Nat
  workBound : forall previous,
    payloadChecks previous <=
      workCoefficient * (inputSize previous + 1) ^ workDegree

variable {rowTen : BoundaryRepair.Profile rowNine}

/-- Canonical row-11 payload accounting. -/
noncomputable def canonicalPayloadChecksFor
    (carrierSpec :
      _root_.Hypostructure.CT5.Spec.{_, uSite, uWitness, uResource}
        (ActiveView rowTen))
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
    (previous : RowTenStage rowTen) : Nat := by
  classical
  exact
    if active : (BoundaryRepair.SuccessorFocus rowTen).Active previous then
      let view := Residual.Focus.ActiveView.of previous active
      let carrier :=
        _root_.Hypostructure.CT5.run carrierSpec carrierCapability view
      let capacity :=
        _root_.Hypostructure.CT14.run capacitySpec capacityCapability
          carrier.stage
      carrier.checks + capacity.checks +
        (_root_.Hypostructure.CT11.run budgetSpec budgetCapability
          capacity.stage).checks
    else
      0

theorem canonicalPayloadChecksFor_active
    (carrierSpec :
      _root_.Hypostructure.CT5.Spec.{_, uSite, uWitness, uResource}
        (ActiveView rowTen))
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
    (previous : RowTenStage rowTen)
    (active : (BoundaryRepair.SuccessorFocus rowTen).Active previous) :
    canonicalPayloadChecksFor carrierSpec carrierCapability capacitySpec
        capacityCapability budgetSpec budgetCapability previous =
      let view := Residual.Focus.ActiveView.of previous active
      let carrier :=
        _root_.Hypostructure.CT5.run carrierSpec carrierCapability view
      let capacity :=
        _root_.Hypostructure.CT14.run capacitySpec capacityCapability
          carrier.stage
      carrier.checks + capacity.checks +
        (_root_.Hypostructure.CT11.run budgetSpec budgetCapability
          capacity.stage).checks := by
  unfold canonicalPayloadChecksFor
  rw [dif_pos active]

theorem canonicalPayloadChecksFor_le_of_component_bounds
    (carrierSpec :
      _root_.Hypostructure.CT5.Spec.{_, uSite, uWitness, uResource}
        (ActiveView rowTen))
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
    (carrierChecks :
      forall view,
        (_root_.Hypostructure.CT5.run carrierSpec carrierCapability
          view).checks <= carrierBound)
    (capacityChecks :
      forall stage,
        (_root_.Hypostructure.CT14.run capacitySpec capacityCapability
          stage).checks <= capacityBound)
    (budgetChecks :
      forall stage,
        (_root_.Hypostructure.CT11.run budgetSpec budgetCapability
          stage).checks <= budgetBound)
    (previous : RowTenStage rowTen) :
    canonicalPayloadChecksFor carrierSpec carrierCapability capacitySpec
        capacityCapability budgetSpec budgetCapability previous <=
      carrierBound + capacityBound + budgetBound := by
  classical
  by_cases active : (BoundaryRepair.SuccessorFocus rowTen).Active previous
  · rw [canonicalPayloadChecksFor_active carrierSpec carrierCapability
      capacitySpec capacityCapability budgetSpec budgetCapability previous
      active]
    exact Nat.add_le_add
      (Nat.add_le_add
        (carrierChecks (Residual.Focus.ActiveView.of previous active))
        (capacityChecks
          (_root_.Hypostructure.CT5.run carrierSpec carrierCapability
            (Residual.Focus.ActiveView.of previous active)).stage))
      (budgetChecks
        (_root_.Hypostructure.CT14.run capacitySpec capacityCapability
          (_root_.Hypostructure.CT5.run carrierSpec carrierCapability
            (Residual.Focus.ActiveView.of previous active)).stage).stage)
  · simp [canonicalPayloadChecksFor, active]

/-- Constructor-sealed row-11 output for one active row-10 successor. -/
structure Generated (profile : Profile rowTen) (view : ActiveView rowTen)
    where
  private mk ::
  carrier :
    _root_.Hypostructure.CT5.ExecutionResult profile.carrierSpec
      profile.carrierCapability
  capacity :
    _root_.Hypostructure.CT14.ExecutionResult profile.capacitySpec
      profile.capacityCapability
  budget :
    _root_.Hypostructure.CT11.ExecutionResult profile.budgetSpec
      profile.budgetCapability
  capacity_previous : capacity.stage.previous = carrier.stage
  budget_previous : budget.stage.previous = capacity.stage

namespace Generated

def carrierTerminal {profile : Profile rowTen}
    {view : ActiveView rowTen} (generated : Generated profile view) :
    _root_.Hypostructure.CT5.Terminal :=
  generated.carrier.terminal

def capacityTerminal {profile : Profile rowTen}
    {view : ActiveView rowTen} (generated : Generated profile view) :
    _root_.Hypostructure.CT14.Terminal :=
  generated.capacity.terminal

def budgetTerminal {profile : Profile rowTen}
    {view : ActiveView rowTen} (generated : Generated profile view) :
    _root_.Hypostructure.CT11.Terminal :=
  generated.budget.terminal

def checks {profile : Profile rowTen} {view : ActiveView rowTen}
    (generated : Generated profile view) : Nat :=
  generated.carrier.checks + generated.capacity.checks +
    generated.budget.checks

theorem carrier_verified {profile : Profile rowTen}
    {view : ActiveView rowTen} (generated : Generated profile view) :
    _root_.Hypostructure.CT5.OutcomeClaim profile.carrierSpec
      profile.carrierCapability generated.carrier.stage.previous
      generated.carrier.terminal :=
  generated.carrier.verified

theorem capacity_verified {profile : Profile rowTen}
    {view : ActiveView rowTen} (generated : Generated profile view) :
    _root_.Hypostructure.CT14.OutcomeClaim generated.capacity.outcome :=
  generated.capacity.verified

theorem budget_verified {profile : Profile rowTen}
    {view : ActiveView rowTen} (generated : Generated profile view) :
    _root_.Hypostructure.CT11.OutcomeClaim generated.budget.outcome :=
  generated.budget.verified

end Generated

/-- Execute CT5, CT14, then CT11 on one row-10 successor view. -/
def generateActiveCounted
    (profile : Profile rowTen) (view : ActiveView rowTen) :
    Counted (Generated profile view) :=
  let carrier :=
    _root_.Hypostructure.CT5.run profile.carrierSpec
      profile.carrierCapability view
  let capacity :=
    _root_.Hypostructure.CT14.run profile.capacitySpec
      profile.capacityCapability carrier.stage
  let budget :=
    _root_.Hypostructure.CT11.run profile.budgetSpec
      profile.budgetCapability capacity.stage
  {
    value := {
      carrier := carrier
      capacity := capacity
      budget := budget
      capacity_previous := rfl
      budget_previous := rfl
    }
    checks := carrier.checks + capacity.checks + budget.checks
  }

@[simp] theorem generateActiveCounted_checks
    (profile : Profile rowTen) (view : ActiveView rowTen) :
    (generateActiveCounted profile view).checks =
      (generateActiveCounted profile view).value.checks :=
  rfl

abbrev Output (profile : Profile rowTen)
    (previous : RowTenStage rowTen)
    (proof : (BoundaryRepair.SuccessorFocus rowTen).Active previous) :=
  Generated profile (Residual.Focus.ActiveView.of previous proof)

abbrev Stage (profile : Profile rowTen) :=
  Residual.Focus.Stage (BoundaryRepair.SuccessorFocus rowTen)
    (Output profile)

abbrev SuccessorFocus (profile : Profile rowTen) :=
  Residual.Focus.successor (BoundaryRepair.SuccessorFocus rowTen)
    (Output profile)

def payloadBudget (profile : Profile rowTen) :
    PolynomialCheckBudget (RowTenStage rowTen) where
  size := profile.inputSize
  checks := profile.payloadChecks
  coefficient := profile.workCoefficient
  degree := profile.workDegree
  bounded := profile.workBound

private theorem generateActiveCounted_checks_eq_payloadBudget
    (profile : Profile rowTen) (previous : RowTenStage rowTen)
    (active : (BoundaryRepair.SuccessorFocus rowTen).Active previous) :
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

def outputQuery (profile : Profile rowTen) :
    Residual.Focus.ActiveQuery (SuccessorFocus profile)
      fun stage active => Output profile stage.previous active :=
  Residual.Focus.ActiveQuery.latest

noncomputable def run
    (profile : Profile rowTen) (previous : RowTenStage rowTen) :
    Counted (Stage profile) :=
  Residual.Focus.runCountedPayload
    (Output := Output profile)
    (BoundaryRepair.SuccessorFocus rowTen) (payloadBudget profile)
    previous
    (fun proof _selectionChecks _selectionExact =>
      generateActiveCounted profile
        (Residual.Focus.ActiveView.of previous proof))
    (fun proof _selectionChecks _selectionExact =>
      generateActiveCounted_checks_eq_payloadBudget profile previous proof)

@[simp] theorem run_previous
    (profile : Profile rowTen) (previous : RowTenStage rowTen) :
    (run profile previous).value.previous = previous := by
  unfold run
  exact Residual.Focus.runCountedPayload_previous
    (Output := Output profile)
    (BoundaryRepair.SuccessorFocus rowTen) (payloadBudget profile)
    previous
    (fun proof _selectionChecks _selectionExact =>
      generateActiveCounted profile
        (Residual.Focus.ActiveView.of previous proof))
    (fun proof _selectionChecks _selectionExact =>
      generateActiveCounted_checks_eq_payloadBudget profile previous proof)

theorem run_checks_of_active
    (profile : Profile rowTen) (previous : RowTenStage rowTen)
    (active : (BoundaryRepair.SuccessorFocus rowTen).Active previous) :
    (run profile previous).checks =
      (BoundaryRepair.SuccessorFocus rowTen).selectionBudget.checks previous +
        (generateActiveCounted profile
          (Residual.Focus.ActiveView.of previous active)).checks := by
  have exactCore :=
    Residual.Focus.runCountedPayload_checks_of_active
      (Output := Output profile)
      (BoundaryRepair.SuccessorFocus rowTen) (payloadBudget profile)
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
    (profile : Profile rowTen) (previous : RowTenStage rowTen)
    (inactive : Not ((BoundaryRepair.SuccessorFocus rowTen).Active previous)) :
    (run profile previous).checks =
      (BoundaryRepair.SuccessorFocus rowTen).selectionBudget.checks previous := by
  unfold run
  exact Residual.Focus.runCountedPayload_checks_of_inactive
    (Output := Output profile)
    (BoundaryRepair.SuccessorFocus rowTen) (payloadBudget profile)
    previous
    (fun proof _selectionChecks _selectionExact =>
      generateActiveCounted profile
        (Residual.Focus.ActiveView.of previous proof))
    (fun proof _selectionChecks _selectionExact =>
      generateActiveCounted_checks_eq_payloadBudget profile previous proof)
    inactive

theorem run_checks_bounded
    (profile : Profile rowTen) (previous : RowTenStage rowTen) :
    (run profile previous).checks <=
      ((BoundaryRepair.SuccessorFocus rowTen).selectionBudget.add
        (payloadBudget profile)).coefficient *
      (((BoundaryRepair.SuccessorFocus rowTen).selectionBudget.add
        (payloadBudget profile)).size previous + 1) ^
      ((BoundaryRepair.SuccessorFocus rowTen).selectionBudget.add
        (payloadBudget profile)).degree := by
  unfold run
  exact Residual.Focus.runCountedPayload_checks_bounded
    (Output := Output profile)
    (BoundaryRepair.SuccessorFocus rowTen) (payloadBudget profile)
    previous
    (fun proof _selectionChecks _selectionExact =>
      generateActiveCounted profile
        (Residual.Focus.ActiveView.of previous proof))
    (fun proof _selectionChecks _selectionExact =>
      generateActiveCounted_checks_eq_payloadBudget profile previous proof)

end Hypostructure.PDE.FastTrack.ConservativeCarrier
