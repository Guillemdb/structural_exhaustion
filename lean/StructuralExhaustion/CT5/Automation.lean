import StructuralExhaustion.CT5.Theorems

namespace StructuralExhaustion.CT5

def residualKindContracts : List Core.ResidualKindContract := [
  {
    residualKindId := "CT5.residual.localDeficit"
    leanType := "StructuralExhaustion.CT5.LocalDeficitResidual S input"
    semanticFields := [
      ⟨"site", "S.Site", .derivedByGenericSearch⟩,
      ⟨"active", "S.Active input site", .derivedByGenericSearch⟩,
      ⟨"noWitness", "CT5.NoSupportingWitness S input site",
        .derivedByGenericTheorem⟩
    ]
    inheritedContext := .branch
  },
  {
    residualKindId := "CT5.residual.chargeLedger"
    leanType := "StructuralExhaustion.CT5.ChargeLedgerResidual S capability input"
    semanticFields := [
      ⟨"ledger", "CT5.LocalLedgerState S capability input",
        .derivedFromPredecessor⟩,
      ⟨"total_le_capacity", "ledger.total ≤ capability.capacity input",
        .derivedByComputation⟩
    ]
    inheritedContext := .branch
  },
  {
    residualKindId := "CT5.residual.aggregate"
    leanType := "StructuralExhaustion.CT5.AggregateResidual S capability input"
    semanticFields := [
      ⟨"ledger", "CT5.LocalLedgerState S capability input",
        .derivedFromPredecessor⟩,
      ⟨"required_le_capacity", "capability.required input ≤ capability.capacity input",
        .derivedByComputation⟩,
      ⟨"capacity_lt_total", "capability.capacity input < ledger.total",
        .derivedByComputation⟩
    ]
    inheritedContext := .branch
  }
]

def residualKindIds : List String :=
  residualKindContracts.map fun contract => contract.residualKindId

def capabilityContract : Core.CapabilityContract where
  capabilityId := "StructuralExhaustion.CT5.reference"
  tacticId := "CT5"
  requiredDefinitions := [
    ⟨"Spec.Site", .userDefinition⟩,
    ⟨"Spec.Witness", .userDefinition⟩,
    ⟨"Spec.Active", .userDefinition⟩,
    ⟨"Spec.Supports", .userDefinition⟩,
    ⟨"Spec.contribution", .userOperator⟩,
    ⟨"Capability.sites", .userFiniteEnumeration⟩,
    ⟨"Capability.witnesses", .userFiniteEnumeration⟩,
    ⟨"Capability.activeDecidable", .instanceBridge⟩,
    ⟨"Capability.supportsDecidable", .instanceBridge⟩,
    ⟨"Capability.required", .userOperator⟩,
    ⟨"Capability.capacity", .userOperator⟩]
  requiredInstances := [
    "Capability.activeDecidable",
    "Capability.supportsDecidable"]
  derivedOperations := ["CT5.analyzeDeficit", "CT5.computeLedger",
    "CT5.ledgerTotal", "CT5.compare",
    "CT5.runReference", "CT5.residual.localDeficit",
    "CT5.residual.chargeLedger", "CT5.residual.aggregate"]

def nodeAutomationContracts : List Core.NodeAutomationContract := [
  { nodeId := "CT5.entry", executionClass := .definitional,
    authorInputs := [], derivedInputs := [], frameworkTheorems := [],
    generatedOutputs := [⟨"CT5.Input", .derivedDefinitionally⟩],
    manualObligations := [] },
  { nodeId := "CT5.search.deficit", executionClass := .finiteSearch,
    authorInputs := [⟨"Capability.sites", .userFiniteEnumeration⟩,
      ⟨"Capability.witnesses", .userFiniteEnumeration⟩,
      ⟨"Spec.Active", .userDefinition⟩,
      ⟨"Spec.Supports", .userDefinition⟩,
      ⟨"Capability.activeDecidable", .instanceBridge⟩,
      ⟨"Capability.supportsDecidable", .instanceBridge⟩],
    derivedInputs := [⟨"FiniteSearch.search", .derivedByGenericSearch⟩],
    frameworkTheorems := ["Core.FiniteSearch.search_none_iff"],
    generatedOutputs := [
      ⟨"CT5.DeficitDecision", .derivedByGenericSearch⟩,
      ⟨"CT5.LocalDeficitResidual", .derivedByGenericSearch⟩,
      ⟨"CT5.DeficitFreeState", .derivedByGenericTheorem⟩],
    manualObligations := [] },
  { nodeId := "CT5.compute.summation", executionClass := .verifiedComputation,
    authorInputs := [⟨"Spec.contribution", .userOperator⟩,
      ⟨"Capability.sites", .userFiniteEnumeration⟩,
      ⟨"Capability.witnesses", .userFiniteEnumeration⟩,
      ⟨"Spec.Active", .userDefinition⟩,
      ⟨"Spec.Supports", .userDefinition⟩,
      ⟨"Capability.activeDecidable", .instanceBridge⟩,
      ⟨"Capability.supportsDecidable", .instanceBridge⟩],
    derivedInputs := [⟨"CT5.DeficitFreeState", .derivedFromPredecessor⟩,
      ⟨"ledgerTotal", .derivedByComputation⟩],
    frameworkTheorems := [],
    generatedOutputs := [⟨"CT5.LocalLedgerState", .derivedByComputation⟩],
    manualObligations := [] },
  { nodeId := "CT5.decide.comparison", executionClass := .verifiedComputation,
    authorInputs := [⟨"Capability.required", .userOperator⟩,
      ⟨"Capability.capacity", .userOperator⟩],
    derivedInputs := [⟨"CT5.LocalLedgerState", .derivedFromPredecessor⟩],
    frameworkTheorems := [],
    generatedOutputs := [
      ⟨"CT5.ComparisonDecision", .derivedByComputation⟩,
      ⟨"CT5.C4Certificate", .derivedByGenericTheorem⟩,
      ⟨"CT5.ChargeLedgerResidual", .derivedByGenericTheorem⟩,
      ⟨"CT5.AggregateResidual", .derivedByGenericTheorem⟩],
    manualObligations := [] }
]

syntax "ct5_execute " term " using " term " at " term : term
macro_rules
  | `(ct5_execute $S using $cap at $input) =>
      `(StructuralExhaustion.CT5.run $S $cap $input)
syntax "ct5 " term " using " term " at " term : tactic
macro_rules
  | `(tactic| ct5 $S using $cap at $input) =>
      `(tactic| exact StructuralExhaustion.CT5.run_verified $S $cap $input)
syntax "ct5_total " term " using " term " at " term : tactic
macro_rules
  | `(tactic| ct5_total $S using $cap at $input) =>
      `(tactic| exact StructuralExhaustion.CT5.run_total $S $cap $input)

end StructuralExhaustion.CT5
