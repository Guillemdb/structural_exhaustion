import StructuralExhaustion.Routes.CT2ToCT3
import StructuralExhaustion.CT3.Automation
import StructuralExhaustion.Examples.CT2AutomationFirst

namespace StructuralExhaustion.Examples.CT2ToCT3AutomationFirst

open StructuralExhaustion
open StructuralExhaustion.Examples.CT2AutomationFirst
open StructuralExhaustion.Routes.CT2ToCT3

/-- The semantic residual is extracted from the real executable CT2 fixture;
it contains no CT3 data. -/
def source : CT2.SeparatingContextResidual
    separatingCapability context separatingInput :=
  match separatingResult.outcome with
  | .separating residual => residual

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

abbrev enabledRule := rule targetCapability enabledDiscovery

theorem enabled_discovery :
    enabledRule.discover source = .enabled () :=
  rfl

def enabledTrigger : CT3.Trigger targetSpec (targetContext source) :=
  buildTrigger targetCapability enabledDiscovery source ()

def enabledInput : CT3.Input targetSpec :=
  CT3.Input.ofTrigger (targetContext source) enabledTrigger

def generatedRoute := enabledRule.generate source ()

theorem enabled_attempt_materializes :
    (enabledRule.attempt source).generated? = some generatedRoute :=
  enabled_generates targetCapability enabledDiscovery source () enabled_discovery

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
    generatedRoute.routeId = "CT2.residual.separatingContext->CT3" :=
  generated_route_id targetCapability enabledDiscovery source ()

theorem trigger_is_source : enabledTrigger.piece = .source :=
  rfl

/-- The generated trigger is directly consumable by CT3. -/
def targetResult := CT3.run targetSpec targetCapability enabledInput

theorem target_executes : targetResult.terminal = .knownRow :=
  rfl

inductive NoSeed

def disabledDiscovery : PieceDiscovery
    (CT2.SeparatingContextResidual
      separatingCapability context separatingInput) RoutedPiece where
  Seed := fun _ => NoSeed
  discover := fun _ => .disabled fun seed => nomatch seed
  piece := fun _ seed => nomatch seed

abbrev disabledRule := rule targetCapability disabledDiscovery

def rejectNoSeed : disabledRule.Seed source → False :=
  fun seed => nomatch seed

theorem disabled_discovery :
    disabledRule.discover source = .disabled rejectNoSeed := by
  congr

theorem disabled_attempt_generates_nothing :
    (disabledRule.attempt source).generated? = none :=
  disabled_generates_none targetCapability disabledDiscovery source
    rejectNoSeed disabled_discovery

end StructuralExhaustion.Examples.CT2ToCT3AutomationFirst
