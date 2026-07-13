import StructuralExhaustion.Routes.CT6ToCT9
import StructuralExhaustion.CT9.Automation
import StructuralExhaustion.Examples.CT6AutomationFirst
import StructuralExhaustion.Core.EnumerationCombinators

namespace StructuralExhaustion.Examples.CT6ToCT9AutomationFirst

open StructuralExhaustion
open StructuralExhaustion.Examples.CT6AutomationFirst
open StructuralExhaustion.Routes.CT6ToCT9

/-- A semantic source produced by the executable CT6 fixture. -/
def source : CT6.ActiveLedgerResidual spec capability (input false) :=
  match activeResult.outcome with
  | .activeLedger residual => residual

/-- CT9's own reusable label/capacity capability remains explicit. -/
def targetCapability : CT9.Capability problem where
  Item := Bool
  Label := Unit
  labels := Core.Enumeration.unit
  label := fun _item => ()
  capacity := fun _label => 1

/-- The sole problem-semantic adapter: reinterpret CT6's exact monitored
index collection as CT9's active item collection. -/
def itemAdapter : ItemCollectionAdapter
    (CT6.ActiveLedgerResidual spec capability (input false)) Bool :=
  ItemCollectionAdapter.constant capability.failureOrder.toOrderedCollection

abbrev routedRule := rule targetCapability itemAdapter

def routedTrigger : CT9.Trigger targetCapability (targetContext source) :=
  buildTrigger targetCapability itemAdapter source

def routedInput : CT9.Input targetCapability :=
  buildInput targetCapability itemAdapter source

def generatedRoute := routedRule.generate source ()

theorem route_is_enabled :
    (routedRule.attempt source).generated? = some generatedRoute :=
  enabled_generates targetCapability itemAdapter source

theorem preserves_branch : targetContext source = input false :=
  branchContext_preserved source

theorem materialized_context_is_preserved :
    routedInput.context = input false :=
  input_context_preserved targetCapability itemAdapter source

theorem materialized_items_are_adapted :
    routedInput.items = itemAdapter.items source :=
  input_items_are_adapted targetCapability itemAdapter source

theorem source_activity_is_preserved :
    ∀ index, ¬spec.Failure (input false) index :=
  active_evidence_preserved source

theorem generated_provenance :
    generatedRoute.routeId = "CT6.residual.activeLedger->CT9" :=
  generated_route_id targetCapability itemAdapter source

/-- The generated input is consumed directly by the ordinary CT9 runner. -/
def targetResult := CT9.run targetCapability routedInput

theorem target_executes : targetResult.terminal = .overloaded :=
  rfl

theorem target_trace : targetResult.trace =
    [.entry, .partition, .overload, .overloadedTerminal] :=
  rfl

end StructuralExhaustion.Examples.CT6ToCT9AutomationFirst
