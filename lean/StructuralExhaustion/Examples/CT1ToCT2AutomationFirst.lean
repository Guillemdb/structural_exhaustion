import StructuralExhaustion.Routes.CT1ToCT2
import StructuralExhaustion.Examples.CT2AutomationFirst

namespace StructuralExhaustion.Examples.CT1ToCT2AutomationFirst

open StructuralExhaustion
open StructuralExhaustion.Examples.CT2AutomationFirst
open StructuralExhaustion.Routes.CT1ToCT2

/-! ## Enabled CT1 avoiding → CT2 execution -/

/-- CT1's target is realized exactly by the smaller toy object. -/
def targetSpec : CT1.Spec problem where
  TestIndex := Unit
  Witness := fun _ _ => Unit
  Realizes := fun G _ _ => G = .small

def targetCapability : CT1.Capability targetSpec where
  tests := units
  witnesses := fun _ _ => units
  realizesDecidable := by
    intro G _ _
    change Decidable (G = Object.small)
    exact inferInstance
  inputSize := fun _ => 0
  workCoefficient := 1
  workDegree := 0
  workBound := by intro G; cases G <;> native_decide

def ct1Input : CT1.Input problem where
  context := context.toBranchContext

def ct1Result : CT1.ExecutionResult targetSpec ct1Input :=
  CT1.run targetSpec targetCapability ct1Input

theorem ct1_reaches_avoiding : ct1Result.terminal = .avoiding := rfl

/-- Complete CT1 execution ledger restricted to its verified avoiding leaf. -/
abbrev AvoidingLedger :=
  {result : CT1.ExecutionResult targetSpec ct1Input //
    result.terminal = .avoiding}

def ct1Ledger : AvoidingLedger := ⟨ct1Result, ct1_reaches_avoiding⟩

def currentAvoiding (ledger : AvoidingLedger) : PackedAvoiding targetSpec ct1Input :=
  PackedAvoiding.ofResult ledger.1 ledger.2

def avoidingSource : PackedAvoiding targetSpec ct1Input :=
  currentAvoiding ct1Ledger

/-- This is the one shared induction theorem closed over by the route. -/
def minimality :
    Core.MinimalityKernel problem (CT1.Target targetSpec)
      ct1Input.context := by
  intro value smaller _baseline
  cases value with
  | small => exact ⟨(), (), rfl⟩
  | large => simp [ct1Input, context, problem, rank] at smaller

/-- Reuse CT2's mathematical operators with CT1's canonical target decider. -/
abbrev observable : CT2.Observable problem (CT1.Target targetSpec) where
  baselineDecidable := fun _ => .isTrue trivial
  targetDecidable := CT1.targetDecidable targetSpec targetCapability

abbrev capability :
    CT2.Capability problem (CT1.Target targetSpec) where
  pieces := pieces
  interfaces := interfaces
  contexts := contexts
  observable := observable
  reductions := reductions
  replacements := emptyReplacements

abbrev routedContext := targetContext minimality avoidingSource

abbrev sourceStage : Core.Routing.ResidualStage .ct1 AvoidingLedger :=
  Core.Routing.ResidualStage.exact ct1Ledger

abbrev routedTransition := transition capability minimality

abbrev routedLedgerTransition := routedTransition.onLedger currentAvoiding

/-- This value is not authored route plumbing: it is the expected result of
the generic capability discovery, named only so the executable test can state
the reduction exactly. -/
def discoveredTrigger : CT2.Input capability routedContext where
  seed := {
    piece := .large
    proper := trivial
    admissible := trivial
  }

theorem route_is_enabled :
    routedLedgerTransition.discover sourceStage = .enabled discoveredTrigger :=
  rfl

def routedTrigger : CT2.Input capability routedContext :=
  routedLedgerTransition.trigger sourceStage discoveredTrigger

def routedStage : routedLedgerTransition.EnabledStage sourceStage :=
  routedLedgerTransition.runEnabled sourceStage discoveredTrigger route_is_enabled

def routedLedger := routedStage.ledgerStage

def routedOutcome := advance capability minimality currentAvoiding sourceStage

theorem route_provenance :
    routedTransition.profileId = transitionId :=
  rfl

theorem route_executes : routedOutcome = .enabled routedStage := rfl

theorem route_seed_sound :
    capability.pieces.Proper routedTrigger.seed.piece ∧
      capability.pieces.Admissible routedContext.state routedTrigger.seed.piece :=
  enabled_sound capability minimality currentAvoiding sourceStage routedStage

theorem preserves_branch : routedContext.toBranchContext = ct1Input.context :=
  branchContext_preserved minimality avoidingSource

theorem preserves_ambient : routedContext.G = ct1Input.context.G :=
  ambient_preserved minimality avoidingSource

theorem preserves_state : routedContext.state = ct1Input.context.state :=
  state_preserved minimality avoidingSource

theorem preserves_baseline : routedContext.baseline = ct1Input.context.baseline :=
  baseline_preserved minimality avoidingSource

theorem preserves_avoidance :
    routedContext.avoids = avoidingSource.state.targetAvoiding :=
  avoidance_preserved minimality avoidingSource

/-- End-to-end CT2 execution is retained by the typed transition stage. -/
def ct2Result := routedStage.targetResult

theorem ct2_reaches_criticality : ct2Result.terminal = .criticality := rfl

theorem ct2_trace :
    ct2Result.trace =
      [.entry, .deletionDecision, .replacementAnalysis,
        .criticalityTerminal] :=
  rfl

theorem ct2_result_sound : ct2Result.outcome.Valid :=
  CT2.run_verified capability routedContext routedTrigger

/-! ## Target-decision-free local-deletion route -/

abbrev localCapability : CT2.LocalDeletionCapability problem where
  pieces := pieces
  reductions := reductions

def localDiscoveredTrigger :
    CT2.LocalDeletionInput localCapability routedContext where
  seed := {
    piece := .large
    proper := trivial
    admissible := trivial
  }

theorem local_route_is_enabled :
    localCapability.discover routedContext = .enabled localDiscoveredTrigger :=
  rfl

theorem local_route_preserves_branch :
    routedContext.toBranchContext = ct1Input.context :=
  LocalDeletion.branchContext_preserved minimality avoidingSource

/- Any semantic closure rule for an enabled local trigger is accepted by the
local CT2 runner and follows its exact deletion-C2 trace. -/
section LocalConsumer

variable (closure : CT2.LocalDeletionClosureRule
  (Target := CT1.Target targetSpec) localCapability)

abbrev localTransition :=
  LocalDeletion.transition localCapability minimality closure

abbrev localLedgerTransition :=
  (localTransition closure).onLedger currentAvoiding

theorem local_transition_is_enabled :
    (localLedgerTransition closure).discover sourceStage =
      .enabled localDiscoveredTrigger :=
  rfl

def localStage : (localLedgerTransition closure).EnabledStage sourceStage :=
  (localLedgerTransition closure).runEnabled sourceStage localDiscoveredTrigger
    (local_transition_is_enabled closure)

def localLedger := (localStage closure).ledgerStage

def localOutcome :=
  LocalDeletion.advance localCapability minimality closure currentAvoiding
    sourceStage

theorem local_route_provenance :
    (localTransition closure).profileId = LocalDeletion.transitionId := rfl

theorem local_transition_executes :
    localOutcome closure = .enabled (localStage closure) := rfl

def localCT2Run := (localStage closure).targetResult

theorem local_ct2_terminal :
    (localCT2Run closure).terminal = .deletionC2 :=
  rfl

theorem local_ct2_trace :
    (localCT2Run closure).trace =
      [.entry, .deletionDecision, .deletionC2Terminal] :=
  rfl

include closure in
theorem local_ct2_closes : False :=
  (localCT2Run closure).verified

end LocalConsumer

/-! ## Disabled CT2 discovery -/

def disabledSpec : CT1.Spec problem where
  TestIndex := Unit
  Witness := fun _ _ => Unit
  Realizes := fun _ _ _ => False

def disabledCT1Capability : CT1.Capability disabledSpec where
  tests := units
  witnesses := fun _ _ => units
  realizesDecidable := fun _ _ _ => .isFalse id
  inputSize := fun _ => 0
  workCoefficient := 1
  workDegree := 0
  workBound := by intro G; cases G <;> native_decide

def smallInput : CT1.Input problem where
  context := {
    G := .small
    baseline := trivial
    state := ()
  }

def disabledCT1Result : CT1.ExecutionResult disabledSpec smallInput :=
  CT1.run disabledSpec disabledCT1Capability smallInput

theorem disabled_ct1_avoids : disabledCT1Result.terminal = .avoiding := rfl

def disabledSource : PackedAvoiding disabledSpec smallInput :=
  PackedAvoiding.ofResult disabledCT1Result disabled_ct1_avoids

abbrev DisabledAvoidingLedger :=
  {result : CT1.ExecutionResult disabledSpec smallInput //
    result.terminal = .avoiding}

def disabledCT1Ledger : DisabledAvoidingLedger :=
  ⟨disabledCT1Result, disabled_ct1_avoids⟩

def currentDisabledAvoiding (ledger : DisabledAvoidingLedger) :
    PackedAvoiding disabledSpec smallInput :=
  PackedAvoiding.ofResult ledger.1 ledger.2

def disabledMinimality :
    Core.MinimalityKernel problem (CT1.Target disabledSpec)
      smallInput.context := by
  intro value smaller _baseline
  cases value <;> simp [smallInput, problem, rank] at smaller

abbrev disabledObservable :
    CT2.Observable problem (CT1.Target disabledSpec) where
  baselineDecidable := fun _ => .isTrue trivial
  targetDecidable := CT1.targetDecidable disabledSpec disabledCT1Capability

abbrev disabledCapability :
    CT2.Capability problem (CT1.Target disabledSpec) where
  pieces := pieces
  interfaces := interfaces
  contexts := contexts
  observable := disabledObservable
  reductions := reductions
  replacements := emptyReplacements

abbrev disabledContext := targetContext disabledMinimality disabledSource

abbrev disabledSourceStage :
    Core.Routing.ResidualStage .ct1 DisabledAvoidingLedger :=
  Core.Routing.ResidualStage.exact disabledCT1Ledger

abbrev disabledTransition :=
  transition disabledCapability disabledMinimality

abbrev disabledLedgerTransition :=
  disabledTransition.onLedger currentDisabledAvoiding

def disabledReject : disabledLedgerTransition.Seed disabledSourceStage → False :=
  fun trigger => nomatch trigger.seed.piece

theorem route_is_disabled :
    disabledLedgerTransition.discover disabledSourceStage =
      .disabled disabledReject := by
  cases discovery : disabledLedgerTransition.discover disabledSourceStage with
  | enabled trigger => exact nomatch trigger.seed.piece
  | disabled reject =>
      exact congrArg Core.Routing.Discovery.disabled
        (Subsingleton.elim reject disabledReject)

def disabledOutcome :=
  advance disabledCapability disabledMinimality currentDisabledAvoiding
    disabledSourceStage

theorem disabled_transition_result :
    disabledOutcome = .disabled disabledReject route_is_disabled := rfl

theorem disabled_not_enabled :
    ∀ stage : disabledLedgerTransition.EnabledStage disabledSourceStage,
      disabledOutcome ≠ .enabled stage := by
  intro stage enabled
  rw [disabled_transition_result] at enabled
  contradiction

theorem disabled_has_no_eligible_piece :
    ∀ piece : disabledCapability.pieces.Piece disabledContext.G,
      ¬ disabledCapability.pieces.Proper piece ∨
        ¬ disabledCapability.pieces.Admissible disabledContext.state piece :=
  disabled_sound disabledCapability disabledMinimality currentDisabledAvoiding
    disabledSourceStage disabled_not_enabled

def disabledLocalClosure : CT2.LocalDeletionClosureRule
    (Target := CT1.Target disabledSpec) localCapability where
  preservesBaseline := by
    intro object state piece proper admissible baseline
    trivial
  targetMonotone := by
    intro object state piece proper admissible baseline reducedTarget
    rcases reducedTarget with ⟨index, witness, realizes⟩
    exact realizes.elim

abbrev disabledLocalTransition :=
  LocalDeletion.transition localCapability disabledMinimality
    disabledLocalClosure

abbrev disabledLocalLedgerTransition :=
  disabledLocalTransition.onLedger currentDisabledAvoiding

def disabledLocalReject :
    disabledLocalLedgerTransition.Seed disabledSourceStage → False :=
  fun trigger => nomatch trigger.seed.piece

theorem local_route_is_disabled :
    disabledLocalLedgerTransition.discover disabledSourceStage =
      .disabled disabledLocalReject := by
  cases discovery : disabledLocalLedgerTransition.discover disabledSourceStage with
  | enabled trigger => exact nomatch trigger.seed.piece
  | disabled reject =>
      exact congrArg Core.Routing.Discovery.disabled
        (Subsingleton.elim reject disabledLocalReject)

def disabledLocalOutcome := LocalDeletion.advance localCapability
  disabledMinimality disabledLocalClosure currentDisabledAvoiding
    disabledSourceStage

theorem disabled_local_transition_result :
    disabledLocalOutcome =
      .disabled disabledLocalReject local_route_is_disabled :=
  rfl

/-! ## Certificate-target composition profile -/

/-- A public target with no realizations, used to exercise the reusable
certificate-CT1-to-local-deletion-CT2 composition independently of graphs. -/
def neverTarget (_value : Object) : Prop := False

def neverTargetEncoding : CT1.TargetCertificateEncoding
    (P := problem) neverTarget where
  Code := fun _value => Unit
  Accepts := fun _value _code => False
  encode := by
    intro value target
    exact target.elim
  decode := by
    intro value code accepts
    exact accepts.elim

def neverTargetContext :
    Core.MinimalCounterexampleContext problem neverTarget where
  toAvoidingContext := {
    toBranchContext := {
      G := .small
      baseline := trivial
      state := ()
    }
    avoids := by simp [neverTarget]
  }
  minimal := by
    intro value smaller _baseline
    cases value <;> simp [rank] at smaller

def neverTargetClosure : CT2.LocalDeletionClosureRule
    (Target := neverTarget) localCapability where
  preservesBaseline := by
    intro object state piece proper admissible baseline
    trivial
  targetMonotone := by
    intro object state piece proper admissible baseline reducedTarget
    exact reducedTarget.elim

def certificateRouteProfile :
    LocalDeletion.CertificateProfile (P := problem) neverTarget where
  encoding := neverTargetEncoding
  capability := localCapability
  closure := neverTargetClosure

abbrev certificateProfileInput :=
  certificateRouteProfile.input neverTargetContext

abbrev certificateProfileRun :=
  certificateRouteProfile.runAvoiding neverTargetContext

theorem certificate_profile_reaches_avoiding :
    certificateProfileRun.result.terminal = .avoiding :=
  certificateProfileRun.terminal_eq

theorem certificate_profile_transition_not_enabled :
    ∀ stage :
      ((certificateRouteProfile.transition neverTargetContext).onLedger
        (certificateRouteProfile.currentAvoiding neverTargetContext)).EnabledStage
          (certificateRouteProfile.sourceLedger neverTargetContext),
      certificateRouteProfile.outcome neverTargetContext ≠ .enabled stage :=
  certificateRouteProfile.transition_not_enabled neverTargetContext

theorem certificate_profile_transition_id :
    (certificateRouteProfile.transition neverTargetContext).profileId =
      LocalDeletion.transitionId :=
  rfl

end StructuralExhaustion.Examples.CT1ToCT2AutomationFirst
