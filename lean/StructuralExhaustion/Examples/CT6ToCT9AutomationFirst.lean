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

abbrev routedTransition := transition targetCapability itemAdapter

abbrev sourceStage : Core.Routing.ResidualStage .ct6
    (CT6.ActiveLedgerResidual spec capability (input false)) :=
  Core.Routing.ResidualStage.exact source

abbrev routedExecution := routedTransition.onLedger id

def routedStage : Core.Routing.ResidualStage .ct9
    (routedExecution.EnabledStage sourceStage) :=
  advance targetCapability itemAdapter id sourceStage

def routedLedger := routedStage

theorem preserves_source : routedStage.output.previous = sourceStage :=
  routedStage.output.previous_eq

theorem preserves_branch :
    routedTransition.targetContext sourceStage = input false :=
  rfl

theorem transition_items_are_adapted :
    (routedTransition.trigger sourceStage ()).items =
      itemAdapter.items source :=
  rfl

theorem source_activity_is_preserved :
    ∀ index, ¬spec.Failure (input false) index :=
  source.noFailure

theorem transition_provenance :
    routedTransition.profileId = "CT6.residual.activeLedger->CT9" :=
  transition_profile_id targetCapability itemAdapter

/-- CT9 is executed by the transition and retained in the accumulated ledger. -/
def targetResult := routedStage.output.targetResult

theorem target_executes : targetResult.terminal = .overloaded :=
  rfl

theorem target_trace : targetResult.trace =
    [.entry, .partition, .overload, .overloadedTerminal] :=
  rfl

end StructuralExhaustion.Examples.CT6ToCT9AutomationFirst
