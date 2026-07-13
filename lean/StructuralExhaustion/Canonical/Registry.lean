import Lean
import StructuralExhaustion.CT1.Automation
import StructuralExhaustion.CT2.Automation
import StructuralExhaustion.CT3.Automation
import StructuralExhaustion.CT4.Automation
import StructuralExhaustion.CT5.Automation
import StructuralExhaustion.CT6.Automation
import StructuralExhaustion.CT7.Automation
import StructuralExhaustion.CT8.Automation
import StructuralExhaustion.CT9.Automation
import StructuralExhaustion.CT10.Automation
import StructuralExhaustion.CT11.Automation
import StructuralExhaustion.CT12.Automation
import StructuralExhaustion.CT13.Automation
import StructuralExhaustion.CT14.Automation
import StructuralExhaustion.CT15.Automation
import StructuralExhaustion.CT16.Automation
import StructuralExhaustion.CT17.Automation
import StructuralExhaustion.Routes.CT1ToCT2
import StructuralExhaustion.Routes.CT2ToCT3
import StructuralExhaustion.Routes.CT2ToCT10
import StructuralExhaustion.Routes.CT6ToCT9

namespace StructuralExhaustion.Canonical

/-- The Lean-owned registry row for one automation-first closure tactic. -/
structure TacticDescriptor where
  tacticId : String
  title : String
  apiVersion : String
  namespaceName : Lean.Name
  capabilityContract : Core.CapabilityContract
  capabilityProfiles : List Core.CapabilityProfile
  nodeAutomationContracts : List Core.NodeAutomationContract
  residualKindContracts : List Core.ResidualKindContract
  deriving Repr, DecidableEq

private def descriptor
    (tacticId title apiVersion : String) (namespaceName : Lean.Name)
    (capabilityContract : Core.CapabilityContract)
    (nodeAutomationContracts : List Core.NodeAutomationContract)
    (residualKindContracts : List Core.ResidualKindContract)
    (capabilityProfiles : List Core.CapabilityProfile := []) :
    TacticDescriptor := {
  tacticId := tacticId
  title := title
  apiVersion := apiVersion
  namespaceName := namespaceName
  capabilityContract := capabilityContract
  capabilityProfiles := capabilityProfiles
  nodeAutomationContracts := nodeAutomationContracts
  residualKindContracts := residualKindContracts
}

/-- Ordered stable registry.  The remaining CT rows are added only after their
automation-first implementations satisfy the same compiled contract. -/
def tactics : Array TacticDescriptor := #[
  descriptor "CT1" "Finite target realization" "CT1-v5"
    `StructuralExhaustion.CT1 CT1.capabilityContract
    CT1.nodeAutomationContracts CT1.residualKindContracts
    [CT1.targetEncodingCapabilityProfile],
  descriptor "CT2" "Minimal deletion and exhaustive replacement" "CT2-v6"
    `StructuralExhaustion.CT2 CT2.capabilityContract
    CT2.nodeAutomationContracts CT2.residualKindContracts
    [CT2.deletionOnlyCapabilityProfile],
  descriptor "CT3" "Exact external-response compression" "CT3-v3"
    `StructuralExhaustion.CT3 CT3.capabilityContract
    CT3.nodeAutomationContracts CT3.residualKindContracts,
  descriptor "CT4" "Deterministic charging and capacity" "CT4-v4"
    `StructuralExhaustion.CT4 CT4.capabilityContract
    CT4.nodeAutomationContracts CT4.residualKindContracts
    [CT4.functionalCardinalityCapabilityProfile],
  descriptor "CT5" "Local witness aggregation" "CT5-v3"
    `StructuralExhaustion.CT5 CT5.capabilityContract
    CT5.nodeAutomationContracts CT5.residualKindContracts,
  descriptor "CT6" "Ordered activity failure" "CT6-v5"
    `StructuralExhaustion.CT6 CT6.capabilityContract
    CT6.nodeAutomationContracts CT6.residualKindContracts,
  descriptor "CT7" "Exact context classification" "CT7-v3"
    `StructuralExhaustion.CT7 CT7.capabilityContract
    CT7.nodeAutomationContracts CT7.residualKindContracts,
  descriptor "CT8" "Finite repetition and response" "CT8-v3"
    `StructuralExhaustion.CT8 CT8.capabilityContract
    CT8.nodeAutomationContracts CT8.residualKindContracts,
  descriptor "CT9" "Exact label-fibre overload" "CT9-v5"
    `StructuralExhaustion.CT9 CT9.capabilityContract
    CT9.nodeAutomationContracts CT9.residualKindContracts
    [CT9.parityCapacityOneCapabilityProfile],
  descriptor "CT10" "Finite refinement classification" "CT10-v3"
    `StructuralExhaustion.CT10 CT10.capabilityContract
    CT10.nodeAutomationContracts CT10.residualKindContracts,
  descriptor "CT11" "Finite-sum localization" "CT11-v4"
    `StructuralExhaustion.CT11 CT11.capabilityContract
    CT11.nodeAutomationContracts CT11.residualKindContracts
    [CT11.negativeBudgetCapabilityProfile],
  descriptor "CT12" "Well-founded structural peeling" "CT12-v4"
    `StructuralExhaustion.CT12 CT12.capabilityContract
    CT12.nodeAutomationContracts CT12.residualKindContracts
    [CT12.listPeelingCapabilityProfile],
  descriptor "CT13" "Tier availability and canonical fallback" "CT13-v3"
    `StructuralExhaustion.CT13 CT13.capabilityContract
    CT13.nodeAutomationContracts CT13.residualKindContracts,
  descriptor "CT14" "Aggregate mass and multiplicity" "CT14-v3"
    `StructuralExhaustion.CT14 CT14.capabilityContract
    CT14.nodeAutomationContracts CT14.residualKindContracts,
  descriptor "CT15" "Target-relative rank and full-rank ledger" "CT15-v3"
    `StructuralExhaustion.CT15 CT15.capabilityContract
    CT15.nodeAutomationContracts CT15.residualKindContracts,
  descriptor "CT16" "Exact whole-support closed type" "CT16-v3"
    `StructuralExhaustion.CT16 CT16.capabilityContract
    CT16.nodeAutomationContracts CT16.residualKindContracts,
  descriptor "CT17" "Finite target thickening and survivor arithmetic" "CT17-v3"
    `StructuralExhaustion.CT17 CT17.capabilityContract
    CT17.nodeAutomationContracts CT17.residualKindContracts
]

/-- Framework-generated routes currently proved in Lean. -/
def routes : List Core.RouteContract := [
  Routes.CT1ToCT2.contract,
  Routes.CT2ToCT3.routeContract,
  Routes.CT2ToCT10.routeContract,
  Routes.CT6ToCT9.routeContract
]

end StructuralExhaustion.Canonical
