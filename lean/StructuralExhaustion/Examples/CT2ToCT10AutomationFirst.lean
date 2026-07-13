import StructuralExhaustion.Routes.CT2ToCT10
import StructuralExhaustion.CT10.Automation
import StructuralExhaustion.Examples.CT2AutomationFirst

namespace StructuralExhaustion.Examples.CT2ToCT10AutomationFirst

open StructuralExhaustion
open StructuralExhaustion.Examples.CT2AutomationFirst
open StructuralExhaustion.Routes.CT2ToCT10

def source : CT2.CriticalityResidual
    criticalityCapability context criticalityInput :=
  match criticalityResult.outcome with
  | .criticality residual => residual

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

abbrev enabledRule := rule targetCapability enabledDiscovery

theorem enabled_discovery : enabledRule.discover source = .enabled () :=
  rfl

def enabledTrigger : CT10.Trigger targetCapability (targetContext source) :=
  buildTrigger targetCapability enabledDiscovery source ()

def enabledInput : CT10.Input targetCapability :=
  buildInput targetCapability enabledDiscovery source ()

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

theorem materialized_context_is_preserved :
    enabledInput.context = context.toBranchContext :=
  input_context_preserved targetCapability enabledDiscovery source ()

theorem materialized_data_is_discovered :
    enabledInput.data = datumCollection :=
  input_data_preserved targetCapability enabledDiscovery source ()

theorem generated_provenance :
    generatedRoute.routeId = "CT2.residual.criticality->CT10" :=
  generated_route_id targetCapability enabledDiscovery source ()

/-- The generated trigger is directly consumable by CT10. -/
def targetResult := CT10.run targetCapability enabledInput

theorem target_executes : targetResult.terminal = .exhaustive :=
  rfl

inductive NoSeed

def disabledDiscovery : DataDiscovery
    (CT2.CriticalityResidual criticalityCapability context criticalityInput)
    Datum where
  Seed := fun _ => NoSeed
  discover := fun _ => .disabled fun seed => nomatch seed
  data := fun _ seed => nomatch seed

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

end StructuralExhaustion.Examples.CT2ToCT10AutomationFirst
