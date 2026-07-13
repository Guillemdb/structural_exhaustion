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

def avoidingSource : PackedAvoiding targetSpec ct1Input :=
  PackedAvoiding.ofResult ct1Result ct1_reaches_avoiding

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

abbrev routeRule := rule capability minimality
abbrev routedContext := targetContext minimality avoidingSource

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
    routeRule.discover avoidingSource = .enabled discoveredTrigger :=
  rfl

def routedTrigger : CT2.Input capability routedContext :=
  buildTrigger capability minimality avoidingSource discoveredTrigger

def generatedRoute := routeRule.generate avoidingSource discoveredTrigger

theorem route_provenance :
    generatedRoute.routeId = "CT1.residual.avoiding->CT2" :=
  generated_route_id capability minimality avoidingSource discoveredTrigger

theorem route_seed_sound :
    capability.pieces.Proper routedTrigger.seed.piece ∧
      capability.pieces.Admissible routedContext.state routedTrigger.seed.piece :=
  enabled_sound route_is_enabled

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

/-- End-to-end execution consumes the trigger built by the typed route. -/
def ct2Result : CT2.ExecutionResult capability routedContext routedTrigger :=
  CT2.run capability routedContext routedTrigger

theorem ct2_reaches_criticality : ct2Result.terminal = .criticality := rfl

theorem ct2_trace :
    ct2Result.trace =
      [.entry, .deletionDecision, .replacementAnalysis,
        .criticalityTerminal] :=
  rfl

theorem ct2_result_sound : ct2Result.outcome.Valid :=
  CT2.run_verified capability routedContext routedTrigger

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

abbrev disabledRule := rule disabledCapability disabledMinimality
abbrev disabledContext := targetContext disabledMinimality disabledSource

def disabledReject : disabledRule.Seed disabledSource → False :=
  fun trigger => nomatch trigger.seed.piece

theorem route_is_disabled :
    disabledRule.discover disabledSource = .disabled disabledReject := by
  cases discovery : disabledRule.discover disabledSource with
  | enabled trigger => exact nomatch trigger.seed.piece
  | disabled reject =>
      exact congrArg Core.Routing.Discovery.disabled
        (Subsingleton.elim reject disabledReject)

theorem disabled_has_no_eligible_piece :
    ∀ piece : disabledCapability.pieces.Piece disabledContext.G,
      ¬ disabledCapability.pieces.Proper piece ∨
        ¬ disabledCapability.pieces.Admissible disabledContext.state piece :=
  disabled_sound route_is_disabled

def disabledAttempt := disabledRule.attempt disabledSource

theorem disabled_generates_no_route : disabledAttempt.generated? = none :=
  rfl

end StructuralExhaustion.Examples.CT1ToCT2AutomationFirst
