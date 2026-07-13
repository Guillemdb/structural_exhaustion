import StructuralExhaustion.CT14.Theorems

namespace StructuralExhaustion.CT14

def residualKindContracts : List Core.ResidualKindContract := [
  {
    residualKindId := "CT14.residual.unboundedMember"
    leanType := "StructuralExhaustion.CT14.UnboundedMemberResidual"
    semanticFields := [
      ⟨"member", "Capability.Member", .derivedByGenericSearch⟩,
      ⟨"missing", "Capability.memberCapacity ctx member = none",
        .derivedByGenericTheorem⟩]
    inheritedContext := .branch
  },
  {
    residualKindId := "CT14.residual.missingLabel"
    leanType := "StructuralExhaustion.CT14.MissingLabelResidual"
    semanticFields := [
      ⟨"member", "Capability.Member", .derivedByGenericSearch⟩,
      ⟨"missing", "Capability.memberLabel ctx member = none",
        .derivedByGenericTheorem⟩]
    inheritedContext := .branch
  },
  {
    residualKindId := "CT14.residual.capacity"
    leanType := "StructuralExhaustion.CT14.CapacityResidual"
    semanticFields := [
      ⟨"lower", "Nat", .derivedByComputation⟩,
      ⟨"upper", "Nat", .derivedByComputation⟩,
      ⟨"lowerExact", "lower = StructuralExhaustion.CT14.lowerMass C ctx",
        .derivedByGenericTheorem⟩,
      ⟨"upperExact", "upper = StructuralExhaustion.CT14.upperCapacity C ctx",
        .derivedByGenericTheorem⟩,
      ⟨"within", "lower ≤ upper", .derivedByComputation⟩]
    inheritedContext := .branch
  }
]

def residualKindIds := residualKindContracts.map (·.residualKindId)

def capabilityContract : Core.CapabilityContract where
  capabilityId := "StructuralExhaustion.CT14.reference"
  tacticId := "CT14"
  requiredDefinitions := [
    ⟨"StructuralExhaustion.CT14.Capability.Member", .userDefinition⟩,
    ⟨"StructuralExhaustion.CT14.Capability.members", .userFiniteEnumeration⟩,
    ⟨"StructuralExhaustion.CT14.Capability.Label", .userDefinition⟩,
    ⟨"StructuralExhaustion.CT14.Capability.labelDecidableEq", .instanceBridge⟩,
    ⟨"StructuralExhaustion.CT14.Capability.memberLowerMass", .userOperator⟩,
    ⟨"StructuralExhaustion.CT14.Capability.memberCapacity", .userOperator⟩,
    ⟨"StructuralExhaustion.CT14.Capability.memberLabel", .userOperator⟩
  ]
  requiredInstances := [
    "StructuralExhaustion.CT14.Capability.labelDecidableEq"]
  derivedOperations := [
    "StructuralExhaustion.CT14.lowerMass",
    "StructuralExhaustion.CT14.scanMembers",
    "StructuralExhaustion.CT14.computeLedger",
    "StructuralExhaustion.CT14.compare",
    "StructuralExhaustion.CT14.runReference"
  ]

def nodeAutomationContracts : List Core.NodeAutomationContract := [
  {
    nodeId := "CT14.entry"
    executionClass := .definitional
    authorInputs := []
    derivedInputs := [⟨"context", .derivedFromPredecessor⟩]
    frameworkTheorems := []
    generatedOutputs := [
      ⟨"StructuralExhaustion.CT14.Input", .derivedFromPredecessor⟩]
    manualObligations := []
  },
  {
    nodeId := "CT14.compute.lower-mass"
    executionClass := .verifiedComputation
    authorInputs := [
      ⟨"StructuralExhaustion.CT14.Capability.members", .userFiniteEnumeration⟩,
      ⟨"StructuralExhaustion.CT14.Capability.memberLowerMass", .userOperator⟩]
    derivedInputs := [⟨"context", .derivedFromPredecessor⟩]
    frameworkTheorems := []
    generatedOutputs := [
      ⟨"StructuralExhaustion.CT14.LowerMassState", .derivedByComputation⟩]
    manualObligations := []
  },
  {
    nodeId := "CT14.search.members"
    executionClass := .finiteSearch
    authorInputs := [
      ⟨"StructuralExhaustion.CT14.Capability.members", .userFiniteEnumeration⟩,
      ⟨"StructuralExhaustion.CT14.Capability.memberCapacity", .userOperator⟩,
      ⟨"StructuralExhaustion.CT14.Capability.memberLabel", .userOperator⟩]
    derivedInputs := [
      ⟨"StructuralExhaustion.CT14.LowerMassState", .derivedFromPredecessor⟩]
    frameworkTheorems := [
      "StructuralExhaustion.Core.FiniteSearch.first"]
    generatedOutputs := [
      ⟨"StructuralExhaustion.CT14.ScanDecision", .derivedByGenericSearch⟩,
      ⟨"StructuralExhaustion.CT14.UnboundedMemberResidual",
        .derivedByGenericSearch⟩,
      ⟨"StructuralExhaustion.CT14.MissingLabelResidual",
        .derivedByGenericSearch⟩,
      ⟨"StructuralExhaustion.CT14.MemberScanState",
        .derivedByGenericTheorem⟩]
    manualObligations := []
  },
  {
    nodeId := "CT14.compute.upper-capacity"
    executionClass := .verifiedComputation
    authorInputs := [
      ⟨"StructuralExhaustion.CT14.Capability.members", .userFiniteEnumeration⟩,
      ⟨"StructuralExhaustion.CT14.Capability.memberCapacity", .userOperator⟩,
      ⟨"StructuralExhaustion.CT14.Capability.memberLabel", .userOperator⟩,
      ⟨"StructuralExhaustion.CT14.Capability.labelDecidableEq", .instanceBridge⟩]
    derivedInputs := [
      ⟨"StructuralExhaustion.CT14.MemberScanState", .derivedFromPredecessor⟩]
    frameworkTheorems := []
    generatedOutputs := [
      ⟨"StructuralExhaustion.CT14.LedgerState", .derivedByComputation⟩]
    manualObligations := []
  },
  {
    nodeId := "CT14.decide.comparison"
    executionClass := .verifiedComputation
    authorInputs := []
    derivedInputs := [
      ⟨"StructuralExhaustion.CT14.LedgerState", .derivedFromPredecessor⟩]
    frameworkTheorems := []
    generatedOutputs := [
      ⟨"StructuralExhaustion.CT14.ComparisonDecision", .derivedByComputation⟩,
      ⟨"StructuralExhaustion.CT14.AggregateCertificate",
        .derivedByGenericTheorem⟩,
      ⟨"StructuralExhaustion.CT14.CapacityResidual", .derivedByGenericTheorem⟩]
    manualObligations := []
  }
]

syntax "ct14_execute " term " at " term " on " term : term
macro_rules
  | `(ct14_execute $capability at $context on $input) =>
      `(StructuralExhaustion.CT14.run $capability $context $input)

syntax "ct14 " term " at " term " on " term : tactic
macro_rules
  | `(tactic| ct14 $capability at $context on $input) =>
      `(tactic| exact StructuralExhaustion.CT14.run_verified
        $capability $context $input)

syntax "ct14_total " term " at " term " on " term : tactic
macro_rules
  | `(tactic| ct14_total $capability at $context on $input) =>
      `(tactic| exact StructuralExhaustion.CT14.run_total
        $capability $context $input)

end StructuralExhaustion.CT14
