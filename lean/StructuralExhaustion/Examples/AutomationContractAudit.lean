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

namespace StructuralExhaustion.Examples.AutomationContractAudit

open StructuralExhaustion

def nodeIds (contracts : List Core.NodeAutomationContract) : List String :=
  contracts.map (·.nodeId)

/-- Duplicate-free string list check used by the compiled audit. -/
def nodupStrings : List String → Bool
  | [] => true
  | head :: tail => !tail.contains head && nodupStrings tail

def refs (items : List Core.ProvisionedRef) : List String :=
  items.map (·.ref)

def explicitInstanceRefs (capability : Core.CapabilityContract) : List String :=
  refs (capability.requiredDefinitions.filter fun required =>
    required.provision == .instanceBridge)

def profileValid (profile : Core.CapabilityProfile) : Bool :=
  nodupStrings (refs profile.requiredDefinitions) &&
  profile.requiredInstances == explicitInstanceRefs profile &&
  !profile.derivedOperations.isEmpty &&
  profile.requiredDefinitions.all fun required =>
    required.provision.isAuthorProvided

example : profileValid CT1.targetEncodingCapabilityProfile = true := by
  native_decide

example : profileValid CT2.deletionOnlyCapabilityProfile = true := by
  native_decide

example : profileValid CT3.literalPackedReplacementCapabilityProfile = true := by
  native_decide

example : profileValid CT9.parityCapacityOneCapabilityProfile = true := by
  native_decide

/-- Strong static invariant for one tactic's public automation inventory. -/
def contractsValid (capability : Core.CapabilityContract)
    (expectedNodeIds : List String)
    (contracts : List Core.NodeAutomationContract) : Bool :=
  nodeIds contracts == expectedNodeIds &&
  nodupStrings expectedNodeIds &&
  nodupStrings (refs capability.requiredDefinitions) &&
  capability.requiredInstances == explicitInstanceRefs capability &&
  (capability.requiredDefinitions.all fun required =>
    required.provision.isAuthorProvided) &&
  (contracts.all fun contract =>
    !contract.generatedOutputs.isEmpty &&
    contract.manualObligations.isEmpty &&
    nodupStrings (refs contract.authorInputs) &&
    nodupStrings (refs contract.derivedInputs) &&
    nodupStrings (refs contract.generatedOutputs) &&
    (contract.derivedInputs.all fun input =>
      !contract.generatedOutputs.any fun output => output.ref == input.ref) &&
    contract.authorInputs.all (·.provision.isAuthorProvided) &&
    contract.derivedInputs.all (·.provision.isFrameworkDerived) &&
    contract.generatedOutputs.all (·.provision.isFrameworkDerived) &&
    contract.authorInputs.all fun authorInput =>
      capability.requiredDefinitions.any fun required =>
        required.ref == authorInput.ref &&
          required.provision == authorInput.provision)

def ct1Nodes := [
  CT1.Graph.NodeId.code .entry,
  CT1.Graph.NodeId.code .equivalenceCertification,
  CT1.Graph.NodeId.code .realizationDecision]

def ct2Nodes := [
  CT2.Graph.NodeId.code .entry,
  CT2.Graph.NodeId.code .deletionDecision,
  CT2.Graph.NodeId.code .replacementAnalysis]

def ct3Nodes := [
  CT3.Graph.NodeId.code .entry,
  CT3.Graph.NodeId.code .vectorComputation,
  CT3.Graph.NodeId.code .compressionSearch,
  CT3.Graph.NodeId.code .tableValidation,
  CT3.Graph.NodeId.code .rowLookup]

def ct4Nodes := [
  CT4.Graph.NodeId.code .entry,
  CT4.Graph.NodeId.code .assignment,
  CT4.Graph.NodeId.code .availability,
  CT4.Graph.NodeId.code .fibres,
  CT4.Graph.NodeId.code .comparison]

def ct5Nodes := [
  CT5.Graph.NodeId.code .entry,
  CT5.Graph.NodeId.code .deficitSearch,
  CT5.Graph.NodeId.code .summation,
  CT5.Graph.NodeId.code .comparison]

def ct6Nodes := [
  CT6.Graph.NodeId.code .entry,
  CT6.Graph.NodeId.code .firstFailureSearch]

def ct7Nodes := [
  CT7.Graph.NodeId.code .entry,
  CT7.Graph.NodeId.code .realizationSearch,
  CT7.Graph.NodeId.code .distinctionSearch]

def ct8Nodes := [
  CT8.Graph.NodeId.code .entry,
  CT8.Graph.NodeId.code .repetition,
  CT8.Graph.NodeId.code .response]

def ct9Nodes := [
  CT9.Graph.NodeId.code .entry,
  CT9.Graph.NodeId.code .partition,
  CT9.Graph.NodeId.code .overload]

def ct10Nodes := [
  CT10.Graph.NodeId.code .entry,
  CT10.Graph.NodeId.code .table,
  CT10.Graph.NodeId.code .direct,
  CT10.Graph.NodeId.code .missing,
  CT10.Graph.NodeId.code .promotion]

def ct11Nodes := [
  CT11.Graph.NodeId.code .entry,
  CT11.Graph.NodeId.code .decomposition,
  CT11.Graph.NodeId.code .admissibility,
  CT11.Graph.NodeId.code .localization]

def ct12Nodes := [
  CT12.Graph.NodeId.code .entry,
  CT12.Graph.NodeId.code .saturation,
  CT12.Graph.NodeId.code .peel,
  CT12.Graph.NodeId.code .restoration,
  CT12.Graph.NodeId.code .decrease]

def ct13Nodes := [
  CT13.Graph.NodeId.code .entry,
  CT13.Graph.NodeId.code .tierOne,
  CT13.Graph.NodeId.code .fallback,
  CT13.Graph.NodeId.code .reconciliation,
  CT13.Graph.NodeId.code .comparison]

def ct14Nodes := [
  CT14.Graph.NodeId.code .entry,
  CT14.Graph.NodeId.code .lowerMass,
  CT14.Graph.NodeId.code .memberScan,
  CT14.Graph.NodeId.code .upperCapacity,
  CT14.Graph.NodeId.code .comparison]

def ct15Nodes := [
  CT15.Graph.NodeId.code .entry,
  CT15.Graph.NodeId.code .rankComputation,
  CT15.Graph.NodeId.code .rankSplit,
  CT15.Graph.NodeId.code .ledgerComputation,
  CT15.Graph.NodeId.code .ledgerComparison]

def ct16Nodes := [
  CT16.Graph.NodeId.code .entry,
  CT16.Graph.NodeId.code .supportScan,
  CT16.Graph.NodeId.code .codeComputation,
  CT16.Graph.NodeId.code .codeComparison]

def ct17Nodes := [
  CT17.Graph.NodeId.code .entry,
  CT17.Graph.NodeId.code .compatibility,
  CT17.Graph.NodeId.code .scale,
  CT17.Graph.NodeId.code .survivors,
  CT17.Graph.NodeId.code .arithmetic]

example : contractsValid CT1.capabilityContract ct1Nodes
    CT1.nodeAutomationContracts = true := by decide
example : contractsValid CT2.capabilityContract ct2Nodes
    CT2.nodeAutomationContracts = true := by decide
example : contractsValid CT3.capabilityContract ct3Nodes
    CT3.nodeAutomationContracts = true := by decide
example : contractsValid CT4.capabilityContract ct4Nodes
    CT4.nodeAutomationContracts = true := by decide
example : contractsValid CT5.capabilityContract ct5Nodes
    CT5.nodeAutomationContracts = true := by decide
example : contractsValid CT6.capabilityContract ct6Nodes
    CT6.nodeAutomationContracts = true := by decide
example : contractsValid CT7.capabilityContract ct7Nodes
    CT7.nodeAutomationContracts = true := by decide
example : contractsValid CT8.capabilityContract ct8Nodes
    CT8.nodeAutomationContracts = true := by decide
example : contractsValid CT9.capabilityContract ct9Nodes
    CT9.nodeAutomationContracts = true := by decide
example : contractsValid CT10.capabilityContract ct10Nodes
    CT10.nodeAutomationContracts = true := by decide
example : contractsValid CT11.capabilityContract ct11Nodes
    CT11.nodeAutomationContracts = true := by decide
example : contractsValid CT12.capabilityContract ct12Nodes
    CT12.nodeAutomationContracts = true := by decide
example : contractsValid CT13.capabilityContract ct13Nodes
    CT13.nodeAutomationContracts = true := by decide
example : contractsValid CT14.capabilityContract ct14Nodes
    CT14.nodeAutomationContracts = true := by decide
example : contractsValid CT15.capabilityContract ct15Nodes
    CT15.nodeAutomationContracts = true := by decide
example : contractsValid CT16.capabilityContract ct16Nodes
    CT16.nodeAutomationContracts = true := by decide
example : contractsValid CT17.capabilityContract ct17Nodes
    CT17.nodeAutomationContracts = true := by decide

end StructuralExhaustion.Examples.AutomationContractAudit
