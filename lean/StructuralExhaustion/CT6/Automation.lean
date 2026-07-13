import StructuralExhaustion.CT6.Theorems

namespace StructuralExhaustion.CT6

def residualKindContracts : List Core.ResidualKindContract := [
  {
    residualKindId := "CT6.residual.firstFailure"
    leanType := "StructuralExhaustion.CT6.FirstFailureResidual S capability input"
    semanticFields := [
      ⟨"hit", "Core.FiniteSearch.FirstHit capability.failureOrder.orderedValues (S.Failure input)",
        .derivedByGenericSearch⟩,
      ⟨"data", "S.FailureData", .derivedByComputation⟩,
      ⟨"data_eq", "data = S.failureData input hit.value hit.holds",
        .derivedDefinitionally⟩
    ]
    inheritedContext := .branch
  },
  {
    residualKindId := "CT6.residual.activeLedger"
    leanType := "StructuralExhaustion.CT6.ActiveLedgerResidual S capability input"
    semanticFields := [
      ⟨"noFailure", "∀ index, ¬ S.Failure input index",
        .derivedByGenericTheorem⟩,
      ⟨"total", "Nat", .derivedByComputation⟩,
      ⟨"computed", "total = CT6.activeTotal S capability input",
        .derivedDefinitionally⟩
    ]
    inheritedContext := .branch
  }
]

def residualKindIds : List String :=
  residualKindContracts.map fun contract => contract.residualKindId

def capabilityContract : Core.CapabilityContract where
  capabilityId := "StructuralExhaustion.CT6.reference"
  tacticId := "CT6"
  requiredDefinitions := [
    ⟨"Spec.Index", .userDefinition⟩,
    ⟨"Spec.FailureData", .userDefinition⟩,
    ⟨"Spec.Failure", .userDefinition⟩,
    ⟨"Spec.failureData", .userOperator⟩,
    ⟨"Spec.contribution", .userOperator⟩,
    ⟨"Capability.failureOrder", .userFiniteEnumeration⟩,
    ⟨"Capability.failureDecidable", .instanceBridge⟩]
  requiredInstances := ["Capability.failureDecidable"]
  derivedOperations := ["Core.FiniteSearch.first", "CT6.analyzeActivity",
    "CT6.activeTotal", "CT6.activeLedgerResidual_of_noFailure",
    "CT6.ExecutionResult.activeLedgerResidual_of_terminal_eq",
    "CT6.runActiveLedgerResidual_of_noFailure",
    "CT6.ActiveLedgerRun", "CT6.ActiveLedgerRun.residual",
    "CT6.runActiveLedgerOfNoFailure",
    "CT6.run_terminal_activeLedger_of_noFailure",
    "CT6.run_trace_activeLedger_of_noFailure",
    "CT6.runReference", "CT6.residual.firstFailure",
    "CT6.residual.activeLedger"]

def nodeAutomationContracts : List Core.NodeAutomationContract := [
  { nodeId := "CT6.entry", executionClass := .definitional,
    authorInputs := [], derivedInputs := [], frameworkTheorems := [],
    generatedOutputs := [⟨"CT6.Input", .derivedDefinitionally⟩],
    manualObligations := [] },
  { nodeId := "CT6.search.firstFailure", executionClass := .finiteSearch,
    authorInputs := [⟨"Capability.failureOrder", .userFiniteEnumeration⟩,
      ⟨"Spec.Failure", .userDefinition⟩,
      ⟨"Spec.failureData", .userOperator⟩,
      ⟨"Spec.contribution", .userOperator⟩,
      ⟨"Capability.failureDecidable", .instanceBridge⟩],
    derivedInputs := [⟨"FirstHit.beforeAbsent", .derivedByGenericSearch⟩],
    frameworkTheorems := ["Core.FiniteSearch.first_hit_no_earlier"],
    generatedOutputs := [
      ⟨"CT6.ActivityDecision", .derivedByGenericSearch⟩,
      ⟨"CT6.FirstFailureResidual", .derivedByGenericSearch⟩,
      ⟨"CT6.ActiveLedgerResidual", .derivedByGenericTheorem⟩],
    manualObligations := [] }
]

syntax "ct6_execute " term " using " term " at " term : term
macro_rules
  | `(ct6_execute $S using $cap at $input) =>
      `(StructuralExhaustion.CT6.run $S $cap $input)
syntax "ct6 " term " using " term " at " term : tactic
macro_rules
  | `(tactic| ct6 $S using $cap at $input) =>
      `(tactic| exact StructuralExhaustion.CT6.run_verified $S $cap $input)
syntax "ct6_total " term " using " term " at " term : tactic
macro_rules
  | `(tactic| ct6_total $S using $cap at $input) =>
      `(tactic| exact StructuralExhaustion.CT6.run_total $S $cap $input)

end StructuralExhaustion.CT6
