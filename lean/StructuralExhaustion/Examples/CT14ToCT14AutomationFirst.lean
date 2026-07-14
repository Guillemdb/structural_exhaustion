import StructuralExhaustion.Routes.CT14ToCT14
import StructuralExhaustion.Examples.CT14AutomationFirst

namespace StructuralExhaustion.Examples.CT14ToCT14AutomationFirst

open StructuralExhaustion
open StructuralExhaustion.Examples.CT14AutomationFirst

def source : CT14.CapacityResidual C (ctx .capacity) :=
  CT14.ExecutionResult.capacityResidual capacityResult rfl

def targetCapability : CT14.Capability P where
  Member := Bool
  members := Core.Enumeration.bool
  Label := Bool
  labelDecidableEq := inferInstance
  memberLowerMass := fun _ctx _member => 1
  memberCapacity := fun _ctx _member => some 1
  memberLabel := fun _ctx member => some member

abbrev routedRule := Routes.CT14ToCT14.rule
  (sourceCapability := C) (ctx := ctx .capacity) targetCapability

def routedInput : CT14.Input targetCapability
    (Routes.CT14ToCT14.targetContext source) :=
  Routes.CT14ToCT14.buildInput targetCapability source

def generatedRoute := routedRule.generate source ()

theorem route_is_enabled :
    (routedRule.attempt source).generated? = some generatedRoute :=
  Routes.CT14ToCT14.enabled_generates targetCapability source

theorem preserves_branch :
    Routes.CT14ToCT14.targetContext source = ctx .capacity :=
  Routes.CT14ToCT14.branchContext_preserved source

theorem generated_provenance :
    generatedRoute.routeId = "CT14.residual.capacity->CT14" :=
  Routes.CT14ToCT14.generated_route_id targetCapability source

def targetResult := CT14.run targetCapability
  (Routes.CT14ToCT14.targetContext source) routedInput

theorem target_executes : targetResult.terminal = .capacity := rfl

theorem target_trace : targetResult.trace =
    [.entry, .lowerMass, .memberScan, .upperCapacity, .comparison,
      .capacityTerminal] := rfl

end StructuralExhaustion.Examples.CT14ToCT14AutomationFirst
