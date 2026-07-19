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

abbrev routedTransition := Routes.CT14ToCT14.transition
  (sourceCapability := C) (ctx := ctx .capacity) targetCapability

abbrev sourceStage : Core.Routing.ResidualStage .ct14
    (CT14.CapacityResidual C (ctx .capacity)) :=
  Core.Routing.ResidualStage.exact source

abbrev routedExecution := routedTransition.onLedger id

def routedStage : routedExecution.EnabledStage sourceStage :=
  Routes.CT14ToCT14.advance targetCapability id sourceStage

def routedLedger := routedStage.ledgerStage

theorem preserves_source : routedStage.previous = sourceStage :=
  routedStage.previous_eq

theorem preserves_branch :
    routedTransition.targetContext sourceStage = ctx .capacity :=
  rfl

theorem transition_provenance :
    routedTransition.profileId = "CT14.residual.capacity->CT14" :=
  Routes.CT14ToCT14.transition_profile_id targetCapability

def targetResult := routedStage.targetResult

theorem target_executes : targetResult.terminal = .capacity := rfl

theorem target_trace : targetResult.trace =
    [.entry, .lowerMass, .memberScan, .upperCapacity, .comparison,
      .capacityTerminal] := rfl

end StructuralExhaustion.Examples.CT14ToCT14AutomationFirst
