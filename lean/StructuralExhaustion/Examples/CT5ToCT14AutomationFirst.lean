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

abbrev routedRule := Routes.CT5ToCT14.rule
  (S := spec) (sourceCapability := capability 1 2) (input := input true 1)
  targetCapability

def routedInput : CT14.Input targetCapability
    (Routes.CT5ToCT14.targetContext source) :=
  Routes.CT5ToCT14.buildInput targetCapability source

def generatedRoute := routedRule.generate source ()

theorem route_is_enabled :
    (routedRule.attempt source).generated? = some generatedRoute :=
  Routes.CT5ToCT14.enabled_generates targetCapability source

theorem preserves_branch :
    Routes.CT5ToCT14.targetContext source = input true 1 :=
  Routes.CT5ToCT14.branchContext_preserved source

theorem generated_provenance :
    generatedRoute.routeId = "CT5.residual.chargeLedger->CT14" :=
  Routes.CT5ToCT14.generated_route_id targetCapability source

def targetResult := CT14.run targetCapability
  (Routes.CT5ToCT14.targetContext source) routedInput

theorem target_executes : targetResult.terminal = .capacity := rfl

theorem target_trace : targetResult.trace =
    [.entry, .lowerMass, .memberScan, .upperCapacity, .comparison,
      .capacityTerminal] := rfl

end StructuralExhaustion.Examples.CT5ToCT14AutomationFirst
