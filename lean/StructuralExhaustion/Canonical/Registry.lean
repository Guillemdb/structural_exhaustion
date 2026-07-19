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
import StructuralExhaustion.Canonical.CapabilityConcepts
import StructuralExhaustion.Canonical.ExampleRegistry
import StructuralExhaustion.Canonical.NodeInternalMetadata
import StructuralExhaustion.Routes.CT1ToCT2
import StructuralExhaustion.Routes.CT1ToCT12
import StructuralExhaustion.Routes.CT2ToCT3
import StructuralExhaustion.Routes.CT2ToCT10
import StructuralExhaustion.Routes.CT5ToCT14
import StructuralExhaustion.Routes.CT6ToCT9
import StructuralExhaustion.Routes.CT9ToCT7
import StructuralExhaustion.Routes.CT14ToCT14
import StructuralExhaustion.Routes.Accumulated

namespace StructuralExhaustion.Canonical

/-- The Lean-owned registry row for one automation-first closure tactic. -/
structure TacticDescriptor where
  tacticId : String
  title : String
  apiVersion : String
  namespaceName : Lean.Name
  capabilityContract : Core.CapabilityContract
  capabilityProfiles : List Core.CapabilityProfile
  capabilityConcepts : List CapabilityConcept
  nodeAutomationContracts : List Core.NodeAutomationContract
  nodeInternalFlows : List NodeInternalFlowDescriptor
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
  capabilityConcepts := CapabilityConcepts.forTactic tacticId
  nodeAutomationContracts := nodeAutomationContracts
  nodeInternalFlows := nodeAutomationContracts.map
    NodeInternalFlowDescriptor.ofContract
  residualKindContracts := residualKindContracts ++ [{
    residualKindId := tacticId ++ ".residual.accumulatedLedger"
    leanType := "StructuralExhaustion.Core.Routing.ResidualStage"
    semanticFields := [
      ⟨"previous", "complete exact predecessor ledger",
        .derivedFromPredecessor⟩,
      ⟨"execution", "public CT execution indexed by the predecessor",
        .derivedByGenericTheorem⟩]
    inheritedContext := .branch
  }]
}

/-- Ordered stable registry.  The remaining CT rows are added only after their
automation-first implementations satisfy the same compiled contract. -/
def tactics : Array TacticDescriptor := #[
  descriptor "CT1" "Finite target realization" "CT1-v6"
    `StructuralExhaustion.CT1 CT1.capabilityContract
    CT1.nodeAutomationContracts CT1.residualKindContracts
    [CT1.targetEncodingCapabilityProfile,
      CT1.targetCertificateCapabilityProfile],
  descriptor "CT2" "Minimal deletion and exhaustive replacement" "CT2-v8"
    `StructuralExhaustion.CT2 CT2.capabilityContract
    CT2.nodeAutomationContracts CT2.residualKindContracts
    [CT2.deletionOnlyCapabilityProfile, CT2.localDeletionCapabilityProfile,
      CT2.certifiedReductionCapabilityProfile],
  descriptor "CT3" "Exact external-response compression" "CT3-v4"
    `StructuralExhaustion.CT3 CT3.capabilityContract
    CT3.nodeAutomationContracts CT3.residualKindContracts
    [CT3.literalPackedReplacementCapabilityProfile],
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
  descriptor "CT12" "Well-founded structural peeling" "CT12-v6"
    `StructuralExhaustion.CT12 CT12.capabilityContract
    CT12.nodeAutomationContracts CT12.residualKindContracts
    [CT12.listPeelingCapabilityProfile,
      CT12.disjointPackingCapabilityProfile,
      CT12.refinedLedgerCompletionCapabilityProfile],
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

/-- One executable profile of a typed CT-to-CT transition family.  The
constructor and executor are recorded separately so catalog consumers cannot
mistake static metadata for the operation that advances the full ledger. -/
structure RegisteredTransitionProfileDescriptor where
  contract : Core.CTTransitionProfileContract
  transitionDeclaration : Lean.Name
  advanceDeclaration : Lean.Name
  deriving Repr, DecidableEq

/-- All executable profiles currently proved in Lean.  CT1→CT2 deliberately
has two profiles inside one family; their trigger/result types remain distinct
while transport and ledger semantics are identical. -/
def transitionProfiles : List RegisteredTransitionProfileDescriptor := [
  ⟨Routes.CT1ToCT2.transitionContract,
    `StructuralExhaustion.Routes.CT1ToCT2.transition,
    `StructuralExhaustion.Routes.CT1ToCT2.advance⟩,
  ⟨Routes.CT1ToCT2.LocalDeletion.transitionContract,
    `StructuralExhaustion.Routes.CT1ToCT2.LocalDeletion.transition,
    `StructuralExhaustion.Routes.CT1ToCT2.LocalDeletion.advance⟩,
  ⟨Routes.CT1ToCT12.transitionContract,
    `StructuralExhaustion.Routes.CT1ToCT12.transition,
    `StructuralExhaustion.Routes.CT1ToCT12.advance⟩,
  ⟨Routes.CT2ToCT3.transitionContract,
    `StructuralExhaustion.Routes.CT2ToCT3.transition,
    `StructuralExhaustion.Routes.CT2ToCT3.advance⟩,
  ⟨Routes.CT2ToCT10.transitionContract,
    `StructuralExhaustion.Routes.CT2ToCT10.transition,
    `StructuralExhaustion.Routes.CT2ToCT10.advance⟩,
  ⟨Routes.CT5ToCT14.transitionContract,
    `StructuralExhaustion.Routes.CT5ToCT14.transition,
    `StructuralExhaustion.Routes.CT5ToCT14.advance⟩,
  ⟨Routes.CT6ToCT9.transitionContract,
    `StructuralExhaustion.Routes.CT6ToCT9.transition,
    `StructuralExhaustion.Routes.CT6ToCT9.advance⟩,
  ⟨Routes.CT9ToCT7.transitionContract,
    `StructuralExhaustion.Routes.CT9ToCT7.transition,
    `StructuralExhaustion.Routes.CT9ToCT7.advance⟩,
  ⟨Routes.CT14ToCT14.transitionContract,
    `StructuralExhaustion.Routes.CT14ToCT14.transition,
    `StructuralExhaustion.Routes.CT14ToCT14.advance⟩,
  ⟨Routes.Accumulated.transitionContract .ct1 .ct9
      "StructuralExhaustion.CT9.Capability.executableInterface",
    `StructuralExhaustion.Routes.Accumulated.transition,
    `StructuralExhaustion.Routes.Accumulated.advance⟩,
  ⟨Routes.Accumulated.transitionContract .ct1 .ct10
      "StructuralExhaustion.CT10.Capability.executableInterface",
    `StructuralExhaustion.Routes.Accumulated.transition,
    `StructuralExhaustion.Routes.Accumulated.advance⟩,
  ⟨Routes.Accumulated.transitionContract .ct2 .ct1
      "StructuralExhaustion.CT1.Capability.executableInterface",
    `StructuralExhaustion.Routes.Accumulated.transition,
    `StructuralExhaustion.Routes.Accumulated.advance⟩,
  ⟨Routes.Accumulated.transitionContract .ct3 .ct1
      "StructuralExhaustion.CT1.Capability.executableInterface",
    `StructuralExhaustion.Routes.Accumulated.transition,
    `StructuralExhaustion.Routes.Accumulated.advance⟩,
  ⟨Routes.Accumulated.transitionContract .ct5 .ct2
      "StructuralExhaustion.CT2.Capability.executableInterface",
    `StructuralExhaustion.Routes.Accumulated.transition,
    `StructuralExhaustion.Routes.Accumulated.advance⟩,
  ⟨Routes.Accumulated.transitionContract .ct7 .ct5
      "StructuralExhaustion.CT5.Capability.executableInterface",
    `StructuralExhaustion.Routes.Accumulated.transition,
    `StructuralExhaustion.Routes.Accumulated.advance⟩,
  ⟨Routes.Accumulated.transitionContract .ct5 .ct10
      "StructuralExhaustion.CT10.Capability.executableInterface",
    `StructuralExhaustion.Routes.Accumulated.transition,
    `StructuralExhaustion.Routes.Accumulated.advance⟩,
  ⟨Routes.Accumulated.transitionContract .ct9 .ct1
      "StructuralExhaustion.CT1.Capability.executableInterface",
    `StructuralExhaustion.Routes.Accumulated.transition,
    `StructuralExhaustion.Routes.Accumulated.advance⟩,
  ⟨Routes.Accumulated.transitionContract .ct9 .ct5
      "StructuralExhaustion.CT5.Capability.executableInterface",
    `StructuralExhaustion.Routes.Accumulated.transition,
    `StructuralExhaustion.Routes.Accumulated.advance⟩,
  ⟨Routes.Accumulated.transitionContract .ct9 .ct10
      "StructuralExhaustion.CT10.Capability.executableInterface",
    `StructuralExhaustion.Routes.Accumulated.transition,
    `StructuralExhaustion.Routes.Accumulated.advance⟩,
  ⟨Routes.Accumulated.transitionContract .ct9 .ct14
      "StructuralExhaustion.CT14.Capability.executableInterface",
    `StructuralExhaustion.Routes.Accumulated.transition,
    `StructuralExhaustion.Routes.Accumulated.advance⟩,
  ⟨Routes.Accumulated.transitionContract .ct10 .ct5
      "StructuralExhaustion.CT5.Capability.executableInterface",
    `StructuralExhaustion.Routes.Accumulated.transition,
    `StructuralExhaustion.Routes.Accumulated.advance⟩,
  ⟨Routes.Accumulated.transitionContract .ct10 .ct6
      "StructuralExhaustion.CT6.Capability.executableInterface",
    `StructuralExhaustion.Routes.Accumulated.transition,
    `StructuralExhaustion.Routes.Accumulated.advance⟩,
  ⟨Routes.Accumulated.transitionContract .ct10 .ct9
      "StructuralExhaustion.CT9.Capability.executableInterface",
    `StructuralExhaustion.Routes.Accumulated.transition,
    `StructuralExhaustion.Routes.Accumulated.advance⟩,
  ⟨Routes.Accumulated.transitionContract .ct10 .ct14
      "StructuralExhaustion.CT14.Capability.executableInterface",
    `StructuralExhaustion.Routes.Accumulated.transition,
    `StructuralExhaustion.Routes.Accumulated.advance⟩,
  ⟨Routes.Accumulated.transitionContract .ct12 .ct10
      "StructuralExhaustion.CT10.Capability.executableInterface",
    `StructuralExhaustion.Routes.Accumulated.transition,
    `StructuralExhaustion.Routes.Accumulated.advance⟩,
  ⟨Routes.Accumulated.transitionContract .ct12 .ct15
      "StructuralExhaustion.CT15.Capability.executableInterface",
    `StructuralExhaustion.Routes.Accumulated.transition,
    `StructuralExhaustion.Routes.Accumulated.advance⟩,
  ⟨Routes.Accumulated.transitionContract .ct14 .ct1
      "StructuralExhaustion.CT1.Capability.executableInterface",
    `StructuralExhaustion.Routes.Accumulated.transition,
    `StructuralExhaustion.Routes.Accumulated.advance⟩,
  ⟨Routes.Accumulated.transitionContract .ct14 .ct12
      "StructuralExhaustion.CT12.Capability.executableInterface",
    `StructuralExhaustion.Routes.Accumulated.transition,
    `StructuralExhaustion.Routes.Accumulated.advance⟩,
  ⟨Routes.Accumulated.transitionContract .ct15 .ct9
      "StructuralExhaustion.CT9.Capability.executableInterface",
    `StructuralExhaustion.Routes.Accumulated.transition,
    `StructuralExhaustion.Routes.Accumulated.advance⟩
]

/-- One source/target CT family and all of its executable profiles. -/
structure RegisteredTransitionFamilyDescriptor where
  sourceTacticId : String
  targetTacticId : String
  profiles : List RegisteredTransitionProfileDescriptor
  deriving Repr, DecidableEq

namespace RegisteredTransitionFamilyDescriptor

def familyId (family : RegisteredTransitionFamilyDescriptor) : String :=
  family.sourceTacticId ++ "->" ++ family.targetTacticId

end RegisteredTransitionFamilyDescriptor

private def transitionPairs : List (String × String) :=
  (transitionProfiles.map fun profile =>
    (profile.contract.sourceTacticId, profile.contract.targetTacticId)).eraseDups

/-- Families are derived from the profile registry, so adding a subtype never
creates a second meaning for the same CT pair. -/
def transitionFamilies : List RegisteredTransitionFamilyDescriptor :=
  transitionPairs.map fun pair => {
    sourceTacticId := pair.1
    targetTacticId := pair.2
    profiles := transitionProfiles.filter fun profile =>
      profile.contract.sourceTacticId == pair.1 &&
        profile.contract.targetTacticId == pair.2
  }

/-- Resolve the mandatory full-ledger executor of a registered profile. -/
def registeredTransitionAutomation? (profileId : String) : Option Lean.Name :=
  (transitionProfiles.find? fun profile =>
    profile.contract.profileId == profileId).map (·.advanceDeclaration)

namespace ExampleLinkDescriptor

/-- Resolve the automation declarations of one example edge. Registered
transitions obtain their full-ledger executor from the canonical registry;
ordinary framework compositions retain their declared framework executor. -/
def resolvedAutomationDeclarations
    (link : ExampleLinkDescriptor) : List Lean.Name :=
  match link.kind, link.transitionProfileId? with
  | .registeredTransition, some profileId =>
      match registeredTransitionAutomation? profileId with
      | some owner => [owner]
      | none => []
  | _, _ => link.automationDeclarations

end ExampleLinkDescriptor

end StructuralExhaustion.Canonical
