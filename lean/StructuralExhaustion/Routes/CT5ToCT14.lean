import StructuralExhaustion.CT5.State
import StructuralExhaustion.CT14.Automation

namespace StructuralExhaustion.Routes.CT5ToCT14

open StructuralExhaustion

universe uSite uWitness uMember uLabel
universe uAmbient uBranch

/-!
# CT5 charge-ledger to CT14 aggregate-mass route

A CT5 charge residual has completed its local witness ledger on one branch
context.  CT14's member universe is already fixed by its target capability and
its trigger carries no additional author datum.  The framework therefore owns
the unique context-preserving transition; no semantic adapter or application
choice is required.
-/

def targetContext
    {P : Core.Problem.{uAmbient, uBranch}}
    {S : CT5.Spec.{uSite, uWitness} P}
    {sourceCapability : CT5.Capability S}
    {input : CT5.Input P}
    (_source : CT5.ChargeLedgerResidual S sourceCapability input) :
    Core.BranchContext P :=
  input

def rule
    {P : Core.Problem.{uAmbient, uBranch}}
    {S : CT5.Spec.{uSite, uWitness} P}
    {sourceCapability : CT5.Capability S}
    {input : CT5.Input P}
    (targetCapability : CT14.Capability.{uMember, uLabel} P) :
    Core.Routing.RouteRule
      (CT5.ChargeLedgerResidual S sourceCapability input)
      targetCapability.tacticInterface where
  routeId := "CT5.residual.chargeLedger->CT14"
  targetContext := targetContext
  Seed := fun _source => Unit
  discover := targetCapability.discover
  buildTrigger := fun _source _seed => ⟨⟩

def buildInput
    {P : Core.Problem.{uAmbient, uBranch}}
    {S : CT5.Spec.{uSite, uWitness} P}
    {sourceCapability : CT5.Capability S}
    {input : CT5.Input P}
    (targetCapability : CT14.Capability.{uMember, uLabel} P)
    (source : CT5.ChargeLedgerResidual S sourceCapability input) :
    CT14.Input targetCapability (targetContext source) :=
  (rule targetCapability).buildTrigger source ()

theorem branchContext_preserved
    {P : Core.Problem.{uAmbient, uBranch}}
    {S : CT5.Spec.{uSite, uWitness} P}
    {sourceCapability : CT5.Capability S}
    {input : CT5.Input P}
    (source : CT5.ChargeLedgerResidual S sourceCapability input) :
    targetContext source = input :=
  rfl

theorem ambient_preserved
    {P : Core.Problem.{uAmbient, uBranch}}
    {S : CT5.Spec.{uSite, uWitness} P}
    {sourceCapability : CT5.Capability S}
    {input : CT5.Input P}
    (source : CT5.ChargeLedgerResidual S sourceCapability input) :
    (targetContext source).G = input.G :=
  rfl

theorem baseline_preserved
    {P : Core.Problem.{uAmbient, uBranch}}
    {S : CT5.Spec.{uSite, uWitness} P}
    {sourceCapability : CT5.Capability S}
    {input : CT5.Input P}
    (source : CT5.ChargeLedgerResidual S sourceCapability input) :
    (targetContext source).baseline = input.baseline :=
  rfl

theorem state_preserved
    {P : Core.Problem.{uAmbient, uBranch}}
    {S : CT5.Spec.{uSite, uWitness} P}
    {sourceCapability : CT5.Capability S}
    {input : CT5.Input P}
    (source : CT5.ChargeLedgerResidual S sourceCapability input) :
    (targetContext source).state = input.state :=
  rfl

theorem enabled_generates
    {P : Core.Problem.{uAmbient, uBranch}}
    {S : CT5.Spec.{uSite, uWitness} P}
    {sourceCapability : CT5.Capability S}
    {input : CT5.Input P}
    (targetCapability : CT14.Capability.{uMember, uLabel} P)
    (source : CT5.ChargeLedgerResidual S sourceCapability input) :
    ((rule targetCapability).attempt source).generated? =
      some ((rule targetCapability).generate source ()) :=
  rfl

theorem generated_route_id
    {P : Core.Problem.{uAmbient, uBranch}}
    {S : CT5.Spec.{uSite, uWitness} P}
    {sourceCapability : CT5.Capability S}
    {input : CT5.Input P}
    (targetCapability : CT14.Capability.{uMember, uLabel} P)
    (source : CT5.ChargeLedgerResidual S sourceCapability input) :
    ((rule targetCapability).generate source ()).routeId =
      "CT5.residual.chargeLedger->CT14" :=
  rfl

def routeContract : Core.RouteContract where
  routeId := "CT5.residual.chargeLedger->CT14"
  sourceResidualKind := "CT5.residual.chargeLedger"
  targetTacticId := "CT14"
  discovery := "StructuralExhaustion.CT14.Capability.discover"
  triggerConstructor := "StructuralExhaustion.Routes.CT5ToCT14.buildInput"
  soundnessTheorem := "StructuralExhaustion.Routes.CT5ToCT14.enabled_generates"
  contextPreservationTheorem :=
    "StructuralExhaustion.Routes.CT5ToCT14.branchContext_preserved"
  provenanceTheorem :=
    "StructuralExhaustion.Routes.CT5ToCT14.generated_route_id"
  selectionClass := .forced
  semanticDiscovery := .capabilityDiscovery
  problemSpecificInputs := [.targetCapability]

end StructuralExhaustion.Routes.CT5ToCT14
