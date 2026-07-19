import StructuralExhaustion.Routes.CT2ToCT3
import StructuralExhaustion.CT3.Automation
import StructuralExhaustion.Examples.CT2AutomationFirst

namespace StructuralExhaustion.Examples.CT2ToCT3AutomationFirst

open StructuralExhaustion
open StructuralExhaustion.Examples.CT2AutomationFirst
open StructuralExhaustion.Routes.CT2ToCT3

/-- Complete CT2 execution ledger restricted to its separating terminal. -/
abbrev SeparatingLedger :=
  {result : CT2.ExecutionResult separatingCapability context separatingInput //
    result.terminal = .separating}

def separatingLedger : SeparatingLedger := ⟨separatingResult, rfl⟩

/-- Read the separating residual from the verified CT2 terminal. -/
def currentSeparating (ledger : SeparatingLedger) :
    CT2.SeparatingContextResidual
      separatingCapability context separatingInput := by
  rcases ledger with ⟨result, terminal⟩
  cases result with
  | mk terminalId path outcome =>
      cases outcome with
      | deletionC2 witness => cases terminal
      | replacementC2 witness => cases terminal
      | separating residual => exact residual
      | criticality residual => cases terminal

def source : CT2.SeparatingContextResidual
    separatingCapability context separatingInput :=
  currentSeparating separatingLedger

inductive RoutedPiece where
  | source
  deriving DecidableEq

inductive NoCandidate

def noCandidateEq : DecidableEq NoCandidate := fun candidate => nomatch candidate

@[implicit_reducible]
def noCandidates : FinEnum NoCandidate :=
  @FinEnum.ofNodupList NoCandidate noCandidateEq []
    (by intro candidate; nomatch candidate) (by simp)

def targetSpec : CT3.Spec problem where
  Piece := RoutedPiece
  Context := Unit
  Candidate := NoCandidate
  Row := Unit
  response := fun _ _ => true
  candidatePiece := fun candidate => nomatch candidate
  Admissible := fun _ _ candidate => nomatch candidate
  Smaller := fun _ _ candidate => nomatch candidate
  rowPiece := fun _ => .source
  rowResponse := fun _ _ => true

def targetCapability : CT3.Capability targetSpec where
  contexts := units
  candidates := noCandidates
  rows := units
  admissibleDecidable := fun _ _ candidate => nomatch candidate
  smallerDecidable := fun _ _ candidate => nomatch candidate
  inputSize := fun _ => 0
  workCoefficient := 2
  workDegree := 0
  workBound := by intro G; cases G <;> native_decide

def enabledDiscovery : PieceDiscovery
    (CT2.SeparatingContextResidual
      separatingCapability context separatingInput) RoutedPiece where
  Seed := fun _ => Unit
  discover := fun _ => .enabled ()
  piece := fun _ _ => .source

abbrev enabledTransition := transition targetCapability enabledDiscovery

abbrev enabledLedgerTransition :=
  enabledTransition.onLedger currentSeparating

abbrev sourceStage : Core.Routing.ResidualStage .ct2 SeparatingLedger :=
  Core.Routing.ResidualStage.exact separatingLedger

theorem enabled_discovery :
    enabledLedgerTransition.discover sourceStage = .enabled () :=
  rfl

def enabledStage : enabledLedgerTransition.EnabledStage sourceStage :=
  enabledLedgerTransition.runEnabled sourceStage () enabled_discovery

def enabledLedger := enabledStage.ledgerStage

def enabledOutcome :=
  advance targetCapability enabledDiscovery currentSeparating sourceStage

theorem enabled_attempt_materializes :
    enabledOutcome = .enabled enabledStage :=
  rfl

theorem preserves_branch :
    targetContext source = context.toBranchContext :=
  branchContext_preserved source

theorem preserves_ambient : (targetContext source).G = context.G :=
  ambient_preserved source

theorem preserves_baseline :
    (targetContext source).baseline = context.baseline :=
  baseline_preserved source

theorem preserves_state : (targetContext source).state = context.state :=
  state_preserved source

theorem generated_provenance :
    enabledTransition.profileId = transitionId :=
  rfl

theorem trigger_is_source :
    (enabledLedgerTransition.trigger sourceStage enabledStage.execution.seed).piece =
      .source :=
  rfl

/-- Target execution is retained in the full transition stage. -/
def targetResult := enabledStage.targetResult

theorem target_executes : targetResult.terminal = .knownRow :=
  rfl

inductive NoSeed

def disabledDiscovery : PieceDiscovery
    (CT2.SeparatingContextResidual
      separatingCapability context separatingInput) RoutedPiece where
  Seed := fun _ => NoSeed
  discover := fun _ => .disabled fun seed => nomatch seed
  piece := fun _ seed => nomatch seed

abbrev disabledTransition := transition targetCapability disabledDiscovery

abbrev disabledLedgerTransition :=
  disabledTransition.onLedger currentSeparating

abbrev disabledSourceStage : Core.Routing.ResidualStage .ct2 SeparatingLedger :=
  Core.Routing.ResidualStage.exact separatingLedger

def rejectNoSeed : disabledLedgerTransition.Seed disabledSourceStage → False :=
  fun seed => nomatch seed

theorem disabled_discovery :
    disabledLedgerTransition.discover disabledSourceStage =
      .disabled rejectNoSeed := by
  congr

def disabledOutcome :=
  advance targetCapability disabledDiscovery currentSeparating
    disabledSourceStage

theorem disabled_attempt_generates_nothing :
    disabledOutcome = .disabled rejectNoSeed disabled_discovery :=
  rfl

theorem disabled_has_no_seed :
    IsEmpty (disabledDiscovery.Seed
      (currentSeparating disabledSourceStage.output)) :=
  disabled_sound targetCapability disabledDiscovery currentSeparating
    disabledSourceStage <| by
    intro stage _enabled
    exact nomatch stage.execution.seed

end StructuralExhaustion.Examples.CT2ToCT3AutomationFirst
