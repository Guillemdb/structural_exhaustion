import StructuralExhaustion.CT13.Theorems
import StructuralExhaustion.Core.CTTransition

namespace StructuralExhaustion.CT13

namespace Capability

/-- Canonical executable CT13 entry.  A transition supplies the inherited
branch context and the unique empty invocation; CT13 owns the complete
tier-one/fallback/reconciliation execution. -/
def executableInterface {P : Core.Problem} (C : Capability P) :
    Core.Routing.ExecutableInterface .ct13 where
  Context := Core.BranchContext P
  Trigger := Input C
  Result := fun ctx _input => ExecutionResult C ctx
  execute := fun ctx input => run C ctx input

end Capability

def residualKindContracts : List Core.ResidualKindContract := [
  {
    residualKindId := "CT13.residual.tierOne"
    leanType := "StructuralExhaustion.CT13.TierOneResidual"
    semanticFields := [
      ⟨"payer", "Capability.Payer", .derivedByGenericSearch⟩,
      ⟨"eligible", "Capability.Eligible ctx payer", .derivedByGenericTheorem⟩]
    inheritedContext := .branch
  },
  {
    residualKindId := "CT13.residual.overlap"
    leanType := "StructuralExhaustion.CT13.OverlapResidual"
    semanticFields := [
      ⟨"fallback", "StructuralExhaustion.CT13.FallbackState",
        .derivedFromPredecessor⟩,
      ⟨"left", "Capability.Payer", .derivedByGenericSearch⟩,
      ⟨"right", "Capability.Payer", .derivedByGenericSearch⟩,
      ⟨"different", "left ≠ right", .derivedByGenericTheorem⟩,
      ⟨"sameResource", "resource ctx left = resource ctx right",
        .derivedByGenericTheorem⟩]
    inheritedContext := .branch
  },
  {
    residualKindId := "CT13.residual.deficit"
    leanType := "StructuralExhaustion.CT13.DeficitResidual"
    semanticFields := [
      ⟨"state", "StructuralExhaustion.CT13.ReconciledState",
        .derivedFromPredecessor⟩,
      ⟨"deficit", "state.capacity < Capability.demand ctx",
        .derivedByComputation⟩]
    inheritedContext := .branch
  }
]

def residualKindIds := residualKindContracts.map (·.residualKindId)

def capabilityContract : Core.CapabilityContract where
  capabilityId := "StructuralExhaustion.CT13.reference"
  tacticId := "CT13"
  requiredDefinitions := [
    ⟨"StructuralExhaustion.CT13.Capability.Payer", .userDefinition⟩,
    ⟨"StructuralExhaustion.CT13.Capability.payers", .userFiniteEnumeration⟩,
    ⟨"StructuralExhaustion.CT13.Capability.Eligible", .userDefinition⟩,
    ⟨"StructuralExhaustion.CT13.Capability.eligibleDecidable", .instanceBridge⟩,
    ⟨"StructuralExhaustion.CT13.Capability.Obstruction", .userDefinition⟩,
    ⟨"StructuralExhaustion.CT13.Capability.obstructions", .userFiniteEnumeration⟩,
    ⟨"StructuralExhaustion.CT13.Capability.fallbackDefault", .userDefinition⟩,
    ⟨"StructuralExhaustion.CT13.Capability.obstructionCost", .userOperator⟩,
    ⟨"StructuralExhaustion.CT13.Capability.Resource", .userDefinition⟩,
    ⟨"StructuralExhaustion.CT13.Capability.resourceDecidableEq", .instanceBridge⟩,
    ⟨"StructuralExhaustion.CT13.Capability.resource", .userOperator⟩,
    ⟨"StructuralExhaustion.CT13.Capability.tierTwo", .userOperator⟩,
    ⟨"StructuralExhaustion.CT13.Capability.charge", .userOperator⟩,
    ⟨"StructuralExhaustion.CT13.Capability.demand", .userOperator⟩
  ]
  requiredInstances := [
    "StructuralExhaustion.CT13.Capability.eligibleDecidable",
    "StructuralExhaustion.CT13.Capability.resourceDecidableEq"
  ]
  derivedOperations := [
    "StructuralExhaustion.CT13.selectTierOne",
    "StructuralExhaustion.CT13.computeFallback",
    "StructuralExhaustion.CT13.reconcile",
    "StructuralExhaustion.CT13.compare",
    "StructuralExhaustion.CT13.runReference",
    "StructuralExhaustion.CT13.Capability.executableInterface"
  ]

def nodeAutomationContracts : List Core.NodeAutomationContract := [
  {
    nodeId := "CT13.entry"
    executionClass := .definitional
    authorInputs := []
    derivedInputs := [⟨"context", .derivedFromPredecessor⟩]
    frameworkTheorems := []
    generatedOutputs := [
      ⟨"StructuralExhaustion.CT13.Input", .derivedFromPredecessor⟩]
    manualObligations := []
  },
  {
    nodeId := "CT13.search.tier-one"
    executionClass := .finiteSearch
    authorInputs := [
      ⟨"StructuralExhaustion.CT13.Capability.payers", .userFiniteEnumeration⟩,
      ⟨"StructuralExhaustion.CT13.Capability.Eligible", .userDefinition⟩,
      ⟨"StructuralExhaustion.CT13.Capability.eligibleDecidable", .instanceBridge⟩]
    derivedInputs := [⟨"context", .derivedFromPredecessor⟩]
    frameworkTheorems := [
      "StructuralExhaustion.Core.FiniteSearch.first"]
    generatedOutputs := [
      ⟨"StructuralExhaustion.CT13.TierOneDecision", .derivedByGenericSearch⟩,
      ⟨"StructuralExhaustion.CT13.TierOneResidual", .derivedByGenericSearch⟩,
      ⟨"StructuralExhaustion.CT13.TierOneAbsenceState",
        .derivedByGenericTheorem⟩]
    manualObligations := []
  },
  {
    nodeId := "CT13.compute.fallback"
    executionClass := .verifiedComputation
    authorInputs := [
      ⟨"StructuralExhaustion.CT13.Capability.obstructions",
        .userFiniteEnumeration⟩,
      ⟨"StructuralExhaustion.CT13.Capability.fallbackDefault", .userDefinition⟩,
      ⟨"StructuralExhaustion.CT13.Capability.obstructionCost", .userOperator⟩]
    derivedInputs := [
      ⟨"StructuralExhaustion.CT13.TierOneAbsenceState",
        .derivedFromPredecessor⟩]
    frameworkTheorems := [
      "StructuralExhaustion.CT13.selectMin",
      "StructuralExhaustion.CT13.selectMin_le_of_mem"]
    generatedOutputs := [
      ⟨"StructuralExhaustion.CT13.FallbackState", .derivedByComputation⟩]
    manualObligations := []
  },
  {
    nodeId := "CT13.compute.reconciliation"
    executionClass := .finiteSearch
    authorInputs := [
      ⟨"StructuralExhaustion.CT13.Capability.tierTwo", .userOperator⟩,
      ⟨"StructuralExhaustion.CT13.Capability.resource", .userOperator⟩,
      ⟨"StructuralExhaustion.CT13.Capability.resourceDecidableEq",
        .instanceBridge⟩,
      ⟨"StructuralExhaustion.CT13.Capability.charge", .userOperator⟩]
    derivedInputs := [
      ⟨"StructuralExhaustion.CT13.FallbackState", .derivedFromPredecessor⟩]
    frameworkTheorems := [
      "StructuralExhaustion.Core.FiniteSearch.onList"]
    generatedOutputs := [
      ⟨"StructuralExhaustion.CT13.ReconciliationDecision",
        .derivedByGenericSearch⟩,
      ⟨"StructuralExhaustion.CT13.OverlapResidual", .derivedByGenericSearch⟩,
      ⟨"StructuralExhaustion.CT13.ReconciledState", .derivedByComputation⟩]
    manualObligations := []
  },
  {
    nodeId := "CT13.decide.comparison"
    executionClass := .verifiedComputation
    authorInputs := [
      ⟨"StructuralExhaustion.CT13.Capability.demand", .userOperator⟩]
    derivedInputs := [
      ⟨"StructuralExhaustion.CT13.ReconciledState", .derivedFromPredecessor⟩]
    frameworkTheorems := []
    generatedOutputs := [
      ⟨"StructuralExhaustion.CT13.ComparisonDecision", .derivedByComputation⟩,
      ⟨"StructuralExhaustion.CT13.DeficitResidual", .derivedByGenericTheorem⟩,
      ⟨"StructuralExhaustion.CT13.ReconciliationCertificate",
        .derivedByGenericTheorem⟩]
    manualObligations := []
  }
]

syntax "ct13_execute " term " at " term " on " term : term
macro_rules
  | `(ct13_execute $capability at $context on $input) =>
      `(StructuralExhaustion.CT13.run $capability $context $input)

syntax "ct13 " term " at " term " on " term : tactic
macro_rules
  | `(tactic| ct13 $capability at $context on $input) =>
      `(tactic| exact StructuralExhaustion.CT13.run_verified
        $capability $context $input)

syntax "ct13_total " term " at " term " on " term : tactic
macro_rules
  | `(tactic| ct13_total $capability at $context on $input) =>
      `(tactic| exact StructuralExhaustion.CT13.run_total
        $capability $context $input)

end StructuralExhaustion.CT13
