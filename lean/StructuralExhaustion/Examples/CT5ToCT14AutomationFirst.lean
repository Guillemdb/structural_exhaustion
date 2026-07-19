import StructuralExhaustion.Routes.CT5ToCT14
import StructuralExhaustion.Examples.CT5AutomationFirst

namespace StructuralExhaustion.Examples.CT5ToCT14AutomationFirst

open StructuralExhaustion
open StructuralExhaustion.Examples.CT5AutomationFirst

def source : CT5.ChargeLedgerResidual spec (capability 1 2)
    (input true 1) :=
  CT5.ExecutionResult.chargeResidual spec (capability 1 2) (input true 1)
    chargeResult charge_terminal

def targetCapability : CT14.Capability problem where
  Member := Unit
  members := Core.Enumeration.unit
  Label := Unit
  labelDecidableEq := inferInstance
  memberLowerMass := fun _ctx _member => 1
  memberCapacity := fun _ctx _member => some 1
  memberLabel := fun _ctx _member => some ()

abbrev routedTransition := Routes.CT5ToCT14.transition
  (S := spec) (sourceCapability := capability 1 2) (input := input true 1)
  targetCapability

abbrev sourceStage : Core.Routing.ResidualStage .ct5
    (CT5.ChargeLedgerResidual spec (capability 1 2) (input true 1)) :=
  Core.Routing.ResidualStage.exact source

abbrev routedExecution := routedTransition.onLedger id

def routedStage : Core.Routing.ResidualStage .ct14
    (routedExecution.EnabledStage sourceStage) :=
  Routes.CT5ToCT14.advance targetCapability id sourceStage

def routedLedger := routedStage

theorem preserves_source : routedStage.output.previous = sourceStage :=
  routedStage.output.previous_eq

theorem preserves_branch :
    routedTransition.targetContext sourceStage = input true 1 :=
  rfl

theorem transition_provenance :
    routedTransition.profileId = "CT5.residual.chargeLedger->CT14" :=
  Routes.CT5ToCT14.transition_profile_id targetCapability

def targetResult := routedStage.output.targetResult

theorem target_executes : targetResult.terminal = .capacity := rfl

theorem target_trace : targetResult.trace =
    [.entry, .lowerMass, .memberScan, .upperCapacity, .comparison,
      .capacityTerminal] := rfl

end StructuralExhaustion.Examples.CT5ToCT14AutomationFirst
