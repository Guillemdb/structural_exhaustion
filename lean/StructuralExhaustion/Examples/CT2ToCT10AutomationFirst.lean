import StructuralExhaustion.Routes.CT2ToCT10
import StructuralExhaustion.CT10.Automation
import StructuralExhaustion.Examples.CT2AutomationFirst

namespace StructuralExhaustion.Examples.CT2ToCT10AutomationFirst

open StructuralExhaustion
open StructuralExhaustion.Examples.CT2AutomationFirst
open StructuralExhaustion.Routes.CT2ToCT10

/-- Complete CT2 execution ledger restricted to its criticality terminal. -/
abbrev CriticalityLedger :=
  {result : CT2.ExecutionResult criticalityCapability context criticalityInput //
    result.terminal = .criticality}

def criticalityLedger : CriticalityLedger := ⟨criticalityResult, rfl⟩

def currentCriticality (ledger : CriticalityLedger) :
    CT2.CriticalityResidual criticalityCapability context criticalityInput := by
  rcases ledger with ⟨result, terminal⟩
  cases result with
  | mk terminalId path outcome =>
      cases outcome with
      | deletionC2 witness => cases terminal
      | replacementC2 witness => cases terminal
      | separating residual => cases terminal
      | criticality residual => exact residual

def source : CT2.CriticalityResidual
    criticalityCapability context criticalityInput :=
  currentCriticality criticalityLedger

inductive Datum where
  | critical
  deriving DecidableEq

def datumCollection : Core.OrderedCollection Datum where
  values := [.critical]
  nodup := by simp
  decEq := inferInstance

def targetCapability : CT10.Capability problem where
  Datum := Datum
  Class := Unit
  Promotion := Unit
  classes := units
  classOf := fun _ => ()
  Direct := fun _ => False
  directDecidable := fun _ => .isFalse id
  promote := fun _ => ()

def enabledDiscovery : DataDiscovery
    (CT2.CriticalityResidual criticalityCapability context criticalityInput)
    Datum where
  Seed := fun _ => Unit
  discover := fun _ => .enabled ()
  data := fun _ _ => datumCollection

abbrev enabledTransition := transition targetCapability enabledDiscovery

abbrev enabledLedgerTransition :=
  enabledTransition.onLedger currentCriticality

abbrev sourceStage : Core.Routing.ResidualStage .ct2 CriticalityLedger :=
  Core.Routing.ResidualStage.exact criticalityLedger

theorem enabled_discovery :
    enabledLedgerTransition.discover sourceStage = .enabled () :=
  rfl

def enabledStage : enabledLedgerTransition.EnabledStage sourceStage :=
  enabledLedgerTransition.runEnabled sourceStage () enabled_discovery

def enabledLedger : Core.Routing.ResidualStage .ct10
    (enabledLedgerTransition.EnabledStage sourceStage) :=
  Core.Routing.ResidualStage.exact enabledStage

def enabledOutcome :=
  advance targetCapability enabledDiscovery currentCriticality sourceStage

theorem enabled_attempt_materializes :
    enabledOutcome = .enabled enabledLedger :=
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

theorem materialized_context_is_preserved :
    enabledLedgerTransition.targetContext sourceStage = context.toBranchContext :=
  rfl

theorem materialized_data_is_discovered :
    (enabledLedgerTransition.trigger sourceStage enabledStage.execution.seed).data =
      datumCollection :=
  rfl

theorem generated_provenance :
    enabledTransition.profileId = transitionId :=
  rfl

/-- The CT10 execution is retained in the complete enabled ledger. -/
def targetResult := enabledStage.targetResult

theorem target_executes : targetResult.terminal = .exhaustive :=
  rfl

inductive NoSeed

def disabledDiscovery : DataDiscovery
    (CT2.CriticalityResidual criticalityCapability context criticalityInput)
    Datum where
  Seed := fun _ => NoSeed
  discover := fun _ => .disabled fun seed => nomatch seed
  data := fun _ seed => nomatch seed

abbrev disabledTransition := transition targetCapability disabledDiscovery

abbrev disabledLedgerTransition :=
  disabledTransition.onLedger currentCriticality

abbrev disabledSourceStage : Core.Routing.ResidualStage .ct2 CriticalityLedger :=
  Core.Routing.ResidualStage.exact criticalityLedger

def rejectNoSeed : disabledLedgerTransition.Seed disabledSourceStage → False :=
  fun seed => nomatch seed

theorem disabled_discovery :
    disabledLedgerTransition.discover disabledSourceStage =
      .disabled rejectNoSeed := by
  congr

def disabledOutcome :=
  advance targetCapability disabledDiscovery currentCriticality
    disabledSourceStage

theorem disabled_attempt_generates_nothing :
    disabledOutcome = .disabled (Core.Routing.ResidualStage.exact {
      previous := disabledSourceStage
      previousExact := rfl
      reject := rejectNoSeed
      discovered := disabled_discovery
    }) :=
  rfl

theorem disabled_has_no_seed :
    IsEmpty (disabledDiscovery.Seed
      (currentCriticality disabledSourceStage.output)) :=
  disabled_sound targetCapability disabledDiscovery currentCriticality
    disabledSourceStage <| by
    intro stage _enabled
    exact nomatch stage.output.execution.seed

end StructuralExhaustion.Examples.CT2ToCT10AutomationFirst
