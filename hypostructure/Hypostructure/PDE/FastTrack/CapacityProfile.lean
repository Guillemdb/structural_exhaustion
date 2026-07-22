import Hypostructure.CT14.Execution
import Hypostructure.PDE.FastTrack.DefectRouting
import Hypostructure.PDE.FastTrack.TargetCompactification

/-!
# PDE fast-track row 7: capacity profile

Row 7 consumes the row-6 capacity-ready focus.  On that exact active residual
the framework first builds the CT14 capacity ledger and then runs CT1 on the
resulting CT14 stage through the target-compactification adapter.  The wrapper
adds no branch selector of its own: the public terminal is just CT1's
framework-selected terminal interpreted as either a zero-capacity exclusion or
a positive-capacity target witness.
-/

namespace Hypostructure.PDE.FastTrack.CapacityProfile

open Hypostructure.Core

universe uPrevious uPotential uCurrent uMember uLabel uCandidate

variable {Previous : Type uPrevious}
variable {Potential : Type uPotential} {Current : Type uCurrent}
variable [NormedAddCommGroup Potential] [InnerProductSpace Real Potential]
variable [CompleteSpace Potential]
variable [NormedAddCommGroup Current] [InnerProductSpace Real Current]
variable [CompleteSpace Current]

/-- Literal row-6 successor stage accepted by row 7. -/
abbrev RowSixStage
    {focus : Residual.Focus.Profile Previous}
    {rowFive : DirectedExhaustiveness.Profile Previous focus Potential Current}
    (rowSix : DefectRouting.Profile rowFive) :=
  DefectRouting.Stage rowSix

/-- Exact row-6 successful-capacity view selected by the framework. -/
abbrev ActiveView
    {focus : Residual.Focus.Profile Previous}
    {rowFive : DirectedExhaustiveness.Profile Previous focus Potential Current}
    (rowSix : DefectRouting.Profile rowFive) :=
  Residual.Focus.ActiveView rowSix.CapacityReadyFocus

/-- Minimal row-7 registration.  The capacity profile is CT14 data over the
row-6 capacity-ready view.  The compactified target profile is CT1 data over
the exact CT14 stage. -/
structure Profile
    {focus : Residual.Focus.Profile Previous}
    {rowFive : DirectedExhaustiveness.Profile Previous focus Potential Current}
    (rowSix : DefectRouting.Profile rowFive) where
  capacitySpec :
    _root_.Hypostructure.CT14.Spec.{_, uMember, uLabel} (ActiveView rowSix)
  capacityCapability :
    _root_.Hypostructure.CT14.Capability capacitySpec
  targetSpec :
    _root_.Hypostructure.CT1.Spec.{_, uCandidate}
      (_root_.Hypostructure.CT14.Stage capacitySpec capacityCapability)
  targetCapability :
    _root_.Hypostructure.CT1.Capability targetSpec
  inputSize : RowSixStage rowSix -> Nat
  payloadChecks : RowSixStage rowSix -> Nat
  payloadChecks_active : forall (previous : RowSixStage rowSix)
    (active : rowSix.CapacityReadyFocus.Active previous),
    payloadChecks previous =
      let view := Residual.Focus.ActiveView.of previous active
      let ct14 :=
        _root_.Hypostructure.CT14.run capacitySpec capacityCapability view
      ct14.checks +
        (_root_.Hypostructure.CT1.run targetSpec targetCapability
          ct14.stage).checks
  workCoefficient : Nat
  workDegree : Nat
  workBound : forall previous,
    payloadChecks previous <=
      workCoefficient * (inputSize previous + 1) ^ workDegree

variable {focus : Residual.Focus.Profile Previous}
variable {rowFive : DirectedExhaustiveness.Profile Previous focus Potential Current}
variable {rowSix : DefectRouting.Profile rowFive}

/-- Canonical row-7 payload accounting: if the row-6 capacity focus is active,
run CT14 and then CT1 on the resulting stage; otherwise the payload cost is
zero because the focused executor will append only an inactive marker. -/
noncomputable def canonicalPayloadChecksFor
    (capacitySpec :
      _root_.Hypostructure.CT14.Spec.{_, uMember, uLabel} (ActiveView rowSix))
    (capacityCapability :
      _root_.Hypostructure.CT14.Capability capacitySpec)
    (targetSpec :
      _root_.Hypostructure.CT1.Spec.{_, uCandidate}
        (_root_.Hypostructure.CT14.Stage capacitySpec capacityCapability))
    (targetCapability :
      _root_.Hypostructure.CT1.Capability targetSpec)
    (previous : RowSixStage rowSix) : Nat := by
  classical
  exact
    if active : rowSix.CapacityReadyFocus.Active previous then
      let view := Residual.Focus.ActiveView.of previous active
      let capacity :=
        _root_.Hypostructure.CT14.run capacitySpec capacityCapability view
      capacity.checks +
        (_root_.Hypostructure.CT1.run targetSpec targetCapability
          capacity.stage).checks
    else
      0

theorem canonicalPayloadChecksFor_active
    (capacitySpec :
      _root_.Hypostructure.CT14.Spec.{_, uMember, uLabel} (ActiveView rowSix))
    (capacityCapability :
      _root_.Hypostructure.CT14.Capability capacitySpec)
    (targetSpec :
      _root_.Hypostructure.CT1.Spec.{_, uCandidate}
        (_root_.Hypostructure.CT14.Stage capacitySpec capacityCapability))
    (targetCapability :
      _root_.Hypostructure.CT1.Capability targetSpec)
    (previous : RowSixStage rowSix)
    (active : rowSix.CapacityReadyFocus.Active previous) :
    canonicalPayloadChecksFor capacitySpec capacityCapability targetSpec
        targetCapability previous =
      let view := Residual.Focus.ActiveView.of previous active
      let capacity :=
        _root_.Hypostructure.CT14.run capacitySpec capacityCapability view
      capacity.checks +
        (_root_.Hypostructure.CT1.run targetSpec targetCapability
          capacity.stage).checks := by
  unfold canonicalPayloadChecksFor
  rw [dif_pos active]

theorem canonicalPayloadChecksFor_le_of_component_bounds
    (capacitySpec :
      _root_.Hypostructure.CT14.Spec.{_, uMember, uLabel} (ActiveView rowSix))
    (capacityCapability :
      _root_.Hypostructure.CT14.Capability capacitySpec)
    (targetSpec :
      _root_.Hypostructure.CT1.Spec.{_, uCandidate}
        (_root_.Hypostructure.CT14.Stage capacitySpec capacityCapability))
    (targetCapability :
      _root_.Hypostructure.CT1.Capability targetSpec)
    (capacityBound targetBound : Nat)
    (capacityChecks :
      forall view,
        (_root_.Hypostructure.CT14.run capacitySpec capacityCapability
          view).checks <= capacityBound)
    (targetChecks :
      forall stage,
        (_root_.Hypostructure.CT1.run targetSpec targetCapability
          stage).checks <= targetBound)
    (previous : RowSixStage rowSix) :
    canonicalPayloadChecksFor capacitySpec capacityCapability targetSpec
        targetCapability previous <= capacityBound + targetBound := by
  classical
  by_cases active : rowSix.CapacityReadyFocus.Active previous
  · rw [canonicalPayloadChecksFor_active capacitySpec capacityCapability
      targetSpec targetCapability previous active]
    exact Nat.add_le_add
      (capacityChecks (Residual.Focus.ActiveView.of previous active))
      (targetChecks
        (_root_.Hypostructure.CT14.run capacitySpec capacityCapability
          (Residual.Focus.ActiveView.of previous active)).stage)
  · simp [canonicalPayloadChecksFor, active]

/-- Framework-derived component polynomial envelope for the canonical row-7
payload, read directly from the registered CT14 and CT1 capabilities. -/
noncomputable def canonicalPayloadCapabilityBound
    (capacitySpec :
      _root_.Hypostructure.CT14.Spec.{_, uMember, uLabel} (ActiveView rowSix))
    (capacityCapability :
      _root_.Hypostructure.CT14.Capability capacitySpec)
    (targetSpec :
      _root_.Hypostructure.CT1.Spec.{_, uCandidate}
        (_root_.Hypostructure.CT14.Stage capacitySpec capacityCapability))
    (targetCapability :
      _root_.Hypostructure.CT1.Capability targetSpec)
    (previous : RowSixStage rowSix) : Nat := by
  classical
  exact
    if active : rowSix.CapacityReadyFocus.Active previous then
      let view := Residual.Focus.ActiveView.of previous active
      let capacity :=
        _root_.Hypostructure.CT14.run capacitySpec capacityCapability view
      capacityCapability.workCoefficient *
          (capacityCapability.inputSize view + 1) ^
            capacityCapability.workDegree +
        targetCapability.workCoefficient *
          (targetCapability.inputSize capacity.stage + 1) ^
            targetCapability.workDegree
    else
      0

theorem canonicalPayloadChecksFor_le_capability_bound
    (capacitySpec :
      _root_.Hypostructure.CT14.Spec.{_, uMember, uLabel} (ActiveView rowSix))
    (capacityCapability :
      _root_.Hypostructure.CT14.Capability capacitySpec)
    (targetSpec :
      _root_.Hypostructure.CT1.Spec.{_, uCandidate}
        (_root_.Hypostructure.CT14.Stage capacitySpec capacityCapability))
    (targetCapability :
      _root_.Hypostructure.CT1.Capability targetSpec)
    (previous : RowSixStage rowSix) :
    canonicalPayloadChecksFor capacitySpec capacityCapability targetSpec
        targetCapability previous <=
      canonicalPayloadCapabilityBound capacitySpec capacityCapability
        targetSpec targetCapability previous := by
  classical
  by_cases active : rowSix.CapacityReadyFocus.Active previous
  · rw [canonicalPayloadChecksFor_active capacitySpec capacityCapability
      targetSpec targetCapability previous active]
    unfold canonicalPayloadCapabilityBound
    rw [dif_pos active]
    exact Nat.add_le_add
      (_root_.Hypostructure.CT14.ExecutionResult.checks_le_polynomial
        (_root_.Hypostructure.CT14.run capacitySpec capacityCapability
          (Residual.Focus.ActiveView.of previous active)))
      (_root_.Hypostructure.CT1.ExecutionResult.checks_le_polynomial
        (_root_.Hypostructure.CT1.run targetSpec targetCapability
          (_root_.Hypostructure.CT14.run capacitySpec capacityCapability
            (Residual.Focus.ActiveView.of previous active)).stage))
  · simp [canonicalPayloadChecksFor, canonicalPayloadCapabilityBound, active]

/-- Problem-provided local work envelope for the canonical row-7 CT14-then-CT1
payload.  The constants live in the PDE contract; the framework owns how they
are consumed by the row executor. -/
structure CanonicalPayloadEnvelope
    (capacitySpec :
      _root_.Hypostructure.CT14.Spec.{_, uMember, uLabel} (ActiveView rowSix))
    (capacityCapability :
      _root_.Hypostructure.CT14.Capability capacitySpec)
    (targetSpec :
      _root_.Hypostructure.CT1.Spec.{_, uCandidate}
        (_root_.Hypostructure.CT14.Stage capacitySpec capacityCapability))
    (targetCapability :
      _root_.Hypostructure.CT1.Capability targetSpec) where
  capacityBound : Nat
  targetBound : Nat
  totalBound : Nat
  capacityChecks :
    forall view,
      (_root_.Hypostructure.CT14.run capacitySpec capacityCapability
        view).checks <= capacityBound
  targetChecks :
    forall stage,
      (_root_.Hypostructure.CT1.run targetSpec targetCapability
        stage).checks <= targetBound
  totalCovers : capacityBound + targetBound <= totalBound

theorem canonicalPayloadChecksFor_le_envelope
    (capacitySpec :
      _root_.Hypostructure.CT14.Spec.{_, uMember, uLabel} (ActiveView rowSix))
    (capacityCapability :
      _root_.Hypostructure.CT14.Capability capacitySpec)
    (targetSpec :
      _root_.Hypostructure.CT1.Spec.{_, uCandidate}
        (_root_.Hypostructure.CT14.Stage capacitySpec capacityCapability))
    (targetCapability :
      _root_.Hypostructure.CT1.Capability targetSpec)
    (envelope :
      CanonicalPayloadEnvelope capacitySpec capacityCapability targetSpec
        targetCapability)
    (previous : RowSixStage rowSix) :
    canonicalPayloadChecksFor capacitySpec capacityCapability targetSpec
        targetCapability previous <= envelope.totalBound :=
  Nat.le_trans
    (canonicalPayloadChecksFor_le_of_component_bounds capacitySpec
      capacityCapability targetSpec targetCapability envelope.capacityBound
      envelope.targetBound envelope.capacityChecks envelope.targetChecks
      previous)
    envelope.totalCovers

/-- Constructor-sealed row-7 output on one active capacity-ready view. -/
structure Generated (profile : Profile rowSix) (view : ActiveView rowSix) where
  private mk ::
  capacity :
    _root_.Hypostructure.CT14.ExecutionResult profile.capacitySpec
      profile.capacityCapability
  target :
    _root_.Hypostructure.CT1.ExecutionResult
      profile.targetSpec profile.targetCapability
  target_previous : target.stage.previous = capacity.stage

namespace Generated

/-- Public row-7 terminal, inherited exactly from CT1. -/
def terminal {profile : Profile rowSix} {view : ActiveView rowSix}
    (generated : Generated profile view) :
    _root_.Hypostructure.CT1.Terminal :=
  generated.target.terminal

/-- Exact row-7 payload work. -/
def checks {profile : Profile rowSix} {view : ActiveView rowSix}
    (generated : Generated profile view) : Nat :=
  generated.capacity.checks + generated.target.checks

/-- Zero-capacity exclusion is the CT1 avoiding claim on the exact CT14
ledger. -/
def ZeroCapacityExclusion {profile : Profile rowSix} {view : ActiveView rowSix}
    (generated : Generated profile view) : Prop :=
  generated.terminal = .avoiding

/-- Positive-capacity target witness is the CT1 C1 claim on the exact CT14
ledger. -/
def PositiveCapacityWitness {profile : Profile rowSix} {view : ActiveView rowSix}
    (generated : Generated profile view) : Prop :=
  generated.terminal = .c1

/-- Recover CT1 soundness for the exact compactified target stage. -/
theorem target_verified {profile : Profile rowSix} {view : ActiveView rowSix}
    (generated : Generated profile view) :
    _root_.Hypostructure.CT1.OutcomeClaim
      profile.targetSpec profile.targetCapability
      generated.target.stage.previous generated.terminal :=
  generated.target.verified

end Generated

/-- Execute CT14 and then CT1 on one exact row-6 capacity-ready view. -/
def generateActiveCounted
    (profile : Profile rowSix) (view : ActiveView rowSix) :
    Counted (Generated profile view) :=
  let capacity :=
      _root_.Hypostructure.CT14.run profile.capacitySpec
      profile.capacityCapability view
  let target :=
    _root_.Hypostructure.CT1.run profile.targetSpec
      profile.targetCapability capacity.stage
  {
    value := {
      capacity := capacity
      target := target
      target_previous := rfl
    }
    checks := capacity.checks + target.checks
  }

@[simp] theorem generateActiveCounted_checks
    (profile : Profile rowSix) (view : ActiveView rowSix) :
    (generateActiveCounted profile view).checks =
      (generateActiveCounted profile view).value.checks :=
  rfl

/-- Exact conditional payload appended by the row-7 executor. -/
abbrev Output (profile : Profile rowSix)
    (previous : RowSixStage rowSix)
    (proof : rowSix.CapacityReadyFocus.Active previous) :=
  Generated profile (Residual.Focus.ActiveView.of previous proof)

/-- Literal accumulated stage emitted by row 7. -/
abbrev Stage (profile : Profile rowSix) :=
  Residual.Focus.Stage rowSix.CapacityReadyFocus (Output profile)

/-- Framework-owned successor focus for row-7 descendants. -/
abbrev SuccessorFocus (profile : Profile rowSix) :=
  Residual.Focus.successor rowSix.CapacityReadyFocus (Output profile)

/-- Worst-case active payload budget declared by the row-7 registration. -/
def payloadBudget (profile : Profile rowSix) :
    PolynomialCheckBudget (RowSixStage rowSix) where
  size := profile.inputSize
  checks := profile.payloadChecks
  coefficient := profile.workCoefficient
  degree := profile.workDegree
  bounded := profile.workBound

private theorem generateActiveCounted_checks_eq_payloadBudget
    (profile : Profile rowSix) (previous : RowSixStage rowSix)
    (active : rowSix.CapacityReadyFocus.Active previous) :
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

/-- Retrieve the exact row-7 output from the accumulated successor ledger. -/
def outputQuery (profile : Profile rowSix) :
    Residual.Focus.ActiveQuery (SuccessorFocus profile)
      fun stage active => Output profile stage.previous active :=
  Residual.Focus.ActiveQuery.latest

/-- Read the CT1 terminal selected by the row-7 payload. -/
def terminalQuery (profile : Profile rowSix) :
    Residual.Focus.ActiveQuery (SuccessorFocus profile)
      fun _stage _active => _root_.Hypostructure.CT1.Terminal :=
  (outputQuery profile).map fun _stage _active generated =>
    generated.terminal

/-- Refine to the zero-capacity exclusion row-7 residual. -/
def zeroCapacityRefinement (profile : Profile rowSix) :
    Residual.Focus.Refinement (SuccessorFocus profile) :=
  (terminalQuery profile).equalTo .avoiding

/-- Refine to the positive-capacity target-witness row-7 residual. -/
def positiveCapacityRefinement (profile : Profile rowSix) :
    Residual.Focus.Refinement (SuccessorFocus profile) :=
  (terminalQuery profile).equalTo .c1

/-- Focus selected exactly by the row-7 zero-capacity terminal. -/
abbrev ZeroCapacityFocus (profile : Profile rowSix) :=
  Residual.Focus.refine (SuccessorFocus profile)
    (zeroCapacityRefinement profile)

/-- Focus selected exactly by the row-7 positive-capacity target terminal. -/
abbrev PositiveCapacityFocus (profile : Profile rowSix) :=
  Residual.Focus.refine (SuccessorFocus profile)
    (positiveCapacityRefinement profile)

/-- Read the exact zero-capacity payload and terminal equality. -/
def zeroCapacityOutputQuery (profile : Profile rowSix) :
    Residual.Focus.ActiveQuery (ZeroCapacityFocus profile)
      fun stage active =>
        { generated : Output profile stage.previous active.parent //
          generated.terminal = .avoiding } :=
  (outputQuery profile).selectedTag
    (fun _stage _active generated => generated.terminal) .avoiding

/-- Read the exact positive-capacity payload and terminal equality. -/
def positiveCapacityOutputQuery (profile : Profile rowSix) :
    Residual.Focus.ActiveQuery (PositiveCapacityFocus profile)
      fun stage active =>
        { generated : Output profile stage.previous active.parent //
          generated.terminal = .c1 } :=
  (outputQuery profile).selectedTag
    (fun _stage _active generated => generated.terminal) .c1

/-- Execute row 7 through the existing focused counted machine. -/
noncomputable def run
    (profile : Profile rowSix) (previous : RowSixStage rowSix) :
    Counted (Stage profile) :=
  Residual.Focus.runCountedPayload
    (Output := Output profile)
    rowSix.CapacityReadyFocus (payloadBudget profile) previous
    (fun proof _selectionChecks _selectionExact =>
      generateActiveCounted profile
        (Residual.Focus.ActiveView.of previous proof))
    (fun proof _selectionChecks _selectionExact =>
      generateActiveCounted_checks_eq_payloadBudget profile previous proof)

@[simp] theorem run_previous
    (profile : Profile rowSix) (previous : RowSixStage rowSix) :
    (run profile previous).value.previous = previous := by
  unfold run
  exact Residual.Focus.runCountedPayload_previous
    (Output := Output profile)
    rowSix.CapacityReadyFocus (payloadBudget profile) previous
    (fun proof _selectionChecks _selectionExact =>
      generateActiveCounted profile
        (Residual.Focus.ActiveView.of previous proof))
    (fun proof _selectionChecks _selectionExact =>
      generateActiveCounted_checks_eq_payloadBudget profile previous proof)

/-- The successor focus remains active after an active row-7 execution. -/
def runActiveProof
    (profile : Profile rowSix) (previous : RowSixStage rowSix)
    (active : rowSix.CapacityReadyFocus.Active previous) :
    (SuccessorFocus profile).Active (run profile previous).value := by
  change rowSix.CapacityReadyFocus.Active (run profile previous).value.previous
  rw [run_previous]
  exact active

/-- Reading row 7's latest payload after an active run returns exactly the
framework-generated active payload.  Downstream rows use this theorem instead
of unfolding the focused executor. -/
theorem outputQuery_run_of_active
    (profile : Profile rowSix) (previous : RowSixStage rowSix)
    (active : rowSix.CapacityReadyFocus.Active previous) :
    (outputQuery profile).read (run profile previous).value
        (runActiveProof profile previous active) =
      (generateActiveCounted profile
        (Residual.Focus.ActiveView.of previous active)).value := by
  unfold outputQuery runActiveProof run
  cases selected : (rowSix.CapacityReadyFocus.select previous).value with
  | isTrue proof =>
      have equal : proof = active := Subsingleton.elim _ _
      cases equal
      simp only [Residual.Focus.runCountedPayload]
      rw [selected]
      rfl
  | isFalse absent => exact (absent active).elim

theorem run_checks_of_active
    (profile : Profile rowSix) (previous : RowSixStage rowSix)
    (active : rowSix.CapacityReadyFocus.Active previous) :
    (run profile previous).checks =
      rowSix.CapacityReadyFocus.selectionBudget.checks previous +
        (generateActiveCounted profile
          (Residual.Focus.ActiveView.of previous active)).checks := by
  have exactCore :=
    Residual.Focus.runCountedPayload_checks_of_active
      (Output := Output profile)
      rowSix.CapacityReadyFocus (payloadBudget profile) previous
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
    (profile : Profile rowSix) (previous : RowSixStage rowSix)
    (inactive : Not (rowSix.CapacityReadyFocus.Active previous)) :
    (run profile previous).checks =
      rowSix.CapacityReadyFocus.selectionBudget.checks previous := by
  unfold run
  exact Residual.Focus.runCountedPayload_checks_of_inactive
    (Output := Output profile)
    rowSix.CapacityReadyFocus (payloadBudget profile) previous
    (fun proof _selectionChecks _selectionExact =>
      generateActiveCounted profile
        (Residual.Focus.ActiveView.of previous proof))
    (fun proof _selectionChecks _selectionExact =>
      generateActiveCounted_checks_eq_payloadBudget profile previous proof)
    inactive

theorem run_checks_bounded
    (profile : Profile rowSix) (previous : RowSixStage rowSix) :
    (run profile previous).checks <=
      (rowSix.CapacityReadyFocus.selectionBudget.add
        (payloadBudget profile)).coefficient *
      ((rowSix.CapacityReadyFocus.selectionBudget.add
        (payloadBudget profile)).size previous + 1) ^
      (rowSix.CapacityReadyFocus.selectionBudget.add
        (payloadBudget profile)).degree := by
  unfold run
  exact Residual.Focus.runCountedPayload_checks_bounded
    (Output := Output profile)
    rowSix.CapacityReadyFocus (payloadBudget profile) previous
    (fun proof _selectionChecks _selectionExact =>
      generateActiveCounted profile
        (Residual.Focus.ActiveView.of previous proof))
    (fun proof _selectionChecks _selectionExact =>
      generateActiveCounted_checks_eq_payloadBudget profile previous proof)

end Hypostructure.PDE.FastTrack.CapacityProfile
