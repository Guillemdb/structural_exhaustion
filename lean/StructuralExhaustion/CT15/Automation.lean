import StructuralExhaustion.CT15.Theorems

namespace StructuralExhaustion.CT15

def capabilityContract : Core.CapabilityContract where
  capabilityId := "StructuralExhaustion.CT15.reference"
  tacticId := "CT15"
  requiredDefinitions := [
    ⟨"Spec.Coordinate", .userDefinition⟩,
    ⟨"Spec.TargetDependent", .userDefinition⟩,
    ⟨"Spec.charge", .userOperator⟩,
    ⟨"Spec.capacity", .userOperator⟩,
    ⟨"Capability.coordinates", .userFiniteEnumeration⟩,
    ⟨"Capability.targetDependentDecidable", .instanceBridge⟩
  ]
  requiredInstances := ["Capability.targetDependentDecidable"]
  derivedOperations := [
    "CT15.rankContribution",
    "CT15.computedRank",
    "CT15.splitRank",
    "CT15.ledgerEntries",
    "CT15.ledgerTotal",
    "CT15.buildLedger",
    "CT15.compareLedger",
    "CT15.runReference"
  ]

def residualKindContracts : List Core.ResidualKindContract := [
  {
    residualKindId := "CT15.residual.rankDrop"
    leanType :=
      "StructuralExhaustion.CT15.RankDropResidual S capability input rank"
    semanticFields := [
      ⟨"rank", "CT15.RankState S capability input", .derivedFromPredecessor⟩,
      ⟨"hit",
        "Core.FiniteSearch.FirstHit capability.coordinates.orderedValues (S.TargetDependent input)",
        .derivedByGenericSearch⟩
    ]
    inheritedContext := .branch
  },
  {
    residualKindId := "CT15.residual.fullRankLedger"
    leanType :=
      "StructuralExhaustion.CT15.FullRankLedgerResidual S capability input ledger"
    semanticFields := [
      ⟨"ledger", "CT15.LedgerState S capability input full",
        .derivedFromPredecessor⟩,
      ⟨"total_le_capacity", "ledger.total ≤ S.capacity input",
        .derivedByComputation⟩
    ]
    inheritedContext := .branch
  }
]

def residualKindIds : List String :=
  residualKindContracts.map fun contract => contract.residualKindId

def nodeAutomationContracts : List Core.NodeAutomationContract := [
  {
    nodeId := "CT15.entry"
    executionClass := .definitional
    authorInputs := []
    derivedInputs := [⟨"input", .derivedFromPredecessor⟩]
    frameworkTheorems := []
    generatedOutputs := [⟨"CT15.Input", .derivedDefinitionally⟩]
    manualObligations := []
  },
  {
    nodeId := "CT15.compute.targetRelativeRank"
    executionClass := .verifiedComputation
    authorInputs := [
      ⟨"Spec.TargetDependent", .userDefinition⟩,
      ⟨"Capability.coordinates", .userFiniteEnumeration⟩,
      ⟨"Capability.targetDependentDecidable", .instanceBridge⟩
    ]
    derivedInputs := [⟨"input", .derivedFromPredecessor⟩]
    frameworkTheorems := ["CT15.computeRank"]
    generatedOutputs := [⟨"CT15.RankState", .derivedByComputation⟩]
    manualObligations := []
  },
  {
    nodeId := "CT15.search.firstRankDrop"
    executionClass := .finiteSearch
    authorInputs := [
      ⟨"Spec.TargetDependent", .userDefinition⟩,
      ⟨"Capability.coordinates", .userFiniteEnumeration⟩,
      ⟨"Capability.targetDependentDecidable", .instanceBridge⟩
    ]
    derivedInputs := [⟨"CT15.RankState", .derivedFromPredecessor⟩]
    frameworkTheorems := [
      "Core.FiniteSearch.first",
      "CT15.computedRank_eq_targetRank",
      "CT15.splitRank_sound"
    ]
    generatedOutputs := [
      ⟨"CT15.RankSplitDecision", .derivedByGenericSearch⟩,
      ⟨"CT15.RankDropResidual", .derivedByGenericSearch⟩,
      ⟨"CT15.FullRankState", .derivedByGenericTheorem⟩
    ]
    manualObligations := []
  },
  {
    nodeId := "CT15.compute.fullRankLedger"
    executionClass := .verifiedComputation
    authorInputs := [⟨"Spec.charge", .userOperator⟩]
    derivedInputs := [⟨"CT15.FullRankState", .derivedFromPredecessor⟩]
    frameworkTheorems := ["CT15.buildLedger", "CT15.ledger_exact"]
    generatedOutputs := [⟨"CT15.LedgerState", .derivedByComputation⟩]
    manualObligations := []
  },
  {
    nodeId := "CT15.decide.ledgerCapacity"
    executionClass := .verifiedComputation
    authorInputs := [⟨"Spec.capacity", .userOperator⟩]
    derivedInputs := [⟨"CT15.LedgerState", .derivedFromPredecessor⟩]
    frameworkTheorems := ["Nat.decLt", "CT15.compareLedger"]
    generatedOutputs := [
      ⟨"CT15.LedgerComparison", .derivedByComputation⟩,
      ⟨"CT15.C4Certificate", .derivedByGenericTheorem⟩,
      ⟨"CT15.FullRankLedgerResidual", .derivedByGenericTheorem⟩
    ]
    manualObligations := []
  }
]

syntax (name := ct15Execute)
  "ct15_execute " term " using " term " at " term : term
macro_rules
  | `(ct15_execute $S:term using $capability:term at $input:term) =>
      `(StructuralExhaustion.CT15.run $S $capability $input)

syntax (name := ct15Tactic)
  "ct15 " term " using " term " at " term : tactic
macro_rules
  | `(tactic| ct15 $S:term using $capability:term at $input:term) =>
      `(tactic| exact StructuralExhaustion.CT15.run_verified
        $S $capability $input)

syntax (name := ct15TotalTactic)
  "ct15_total " term " using " term " at " term : tactic
macro_rules
  | `(tactic| ct15_total $S:term using $capability:term at $input:term) =>
      `(tactic| exact StructuralExhaustion.CT15.run_total
        $S $capability $input)

end StructuralExhaustion.CT15
